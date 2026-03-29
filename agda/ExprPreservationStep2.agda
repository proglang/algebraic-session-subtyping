module ExprPreservationStep2 where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Kinds
open import Kits
open import Types using (Ty; T-Base; N-Sub; N-End)
open import AlgorithmicSubtyping using (_<:ₜ_; <:ₜ-refl; <:ₜ-trans; <:ₜ-sub; <:ₜ-end)
open import ExprSyntax using (Expr; Value; Const; E-Val; E-LetUnit; E-Pair; E-App; E-TApp; V-Const; V-Var; V-Receive₁; C-Receive; C-Close; C-Fork; C-Unit)
open import ExprSemantics using (Label; Act-App; Act-TApp; Act-LetPair; Act-LetUnit; Act-PairV; Act-Rec; Act-Fork; Act-New; Act-Receive₁; Act-Receive₂; Act-Rcv; Act-Close; Act-AppL; Act-AppR; Act-TAppE; Act-PairL; Act-PairR; Act-MatchE; Act-LetPairE; Act-LetUnitE; _—[_]→_)
import ExprSemantics as ES
open import ExprNormalTyping
open import ExprSubstitution using (substTyValue)
open import ExprSubstitutionTyping using (rec-unfold-preserves-value; subst-check-preserves-synth; subst2-preserves-synth; substTy-preserves-value)
import ExprSubstitutionTyping as EST
import ExprContextReduction as ECR
open import ExprContextReduction using
  (_—ctx[_]→_; _⦂_⇒_; Compatible; Extract; ctx-step-preserves-disjoint
  ; Ctx-β; Ctx-New; Ctx-Fork; Ctx-Rcv; Ctx-Close
  ; ReplaceAt; replace-preserves-disjoint
  ; RemoveCtx; RM-∅; RM-drop; RM-allused; RM-lin; RM-un
  ; MergeCtx; MC-∅; MC-used-left; MC-used-right; MC-un
  ; mergeDisjointContext; mergeRemoveContext
  ; remove-linear; remove-allused-disjoint; remove-preserves-remove
  ; remove-preserves-disjoint; remove-removed-disjoint; restore-disjoint
  ; extract-remove
  ; AllUsed; AU-∅; AU-used; AU-un; allUsedCtx-AllUsed
  ; LinearDisjoint; LD-∅; LD-used-used; LD-used-live; LD-live-used; LD-un-un
  ; unitLinNf; dualSessNf
  ; Label-β; Label-Fork; Label-RecvVal; Label-Close
  ; recvChanNf; sessNf
  ; allUsedCtx
  ; Ex-β; Ex-Fork; Ex-New; Ex-RecvVal; Ex-RecvLab; Ex-SendVal; Ex-SendLab; Ex-Close
  ; Compat-β; Compat-New; Compat-Fork; Compat-RecvVal; Compat-Close
  )
open import ExprTypingProperties using (frame-remove; replay-synth)
open import ExprTypingLeftover using (strip-value; leftover-synth)
open import ExprPreservationStep using
  ( closeTy-shape
  ; close-inversion
  ; fork-shape
  ; new-shape
  ; newInst-shape
  ; receive₂-shape
  ; receive₁-rigid
  ; receive₂-rigid
  ; receive₁-ty
  ; receive₂-ty
  ; recv-app-inversion
  ; merge-value
  ; replace-take
  ; replace-used-output
  ; take-implies-membership
  ; weaken-synth
  ; arrow-subtype-inversion
  ; substTy-wkCtx-id
  ; allUsed-frame
  ; remove-frame
  ; merge-frame
  )
import ExprPreservationStep as EPS

open Kits.Syntax Types.Ty-Syntax hiding (Sort)
open Traversal Types.Ty-Traversal
open CTraversal record { fusion = Types.fusion }

extendUsed : ∀ (k : ℕ) {n} → Ctx [] n → Ctx [] (k + n)
extendUsed zero Γ = Γ
extendUsed (suc k) Γ = B-Used ▻ extendUsed k Γ

extendUsed-eq :
  ∀ (k : ℕ) {n} (Γ : Ctx [] n) → EPS.extendUsed k Γ ≡ extendUsed k Γ
extendUsed-eq zero Γ = refl
extendUsed-eq (suc k) Γ = cong (B-Used ▻_) (extendUsed-eq k Γ)

extendUsedCR-eq :
  ∀ (k : ℕ) {n} (Γ : Ctx [] n) → ECR.extendUsed k Γ ≡ extendUsed k Γ
extendUsedCR-eq zero Γ = refl
extendUsedCR-eq (suc k) Γ = cong (B-Used ▻_) (extendUsedCR-eq k Γ)

usedCtx : ∀ {n} → Ctx [] n → Ctx [] n
usedCtx ∅ = ∅
usedCtx (_ ▻ Γ) = B-Used ▻ usedCtx Γ

remove-usedCtx : ∀ {n} (Γ : Ctx [] n) → RemoveCtx Γ (allUsedCtx Γ) Γ
remove-usedCtx ∅ = RM-∅
remove-usedCtx (B-Lin _ ▻ Γ) = RM-drop (remove-usedCtx Γ)
remove-usedCtx (B-Un _ ▻ Γ) = RM-un (remove-usedCtx Γ)
remove-usedCtx (B-Used ▻ Γ) = RM-allused (remove-usedCtx Γ)

usedCtx-allUsed :
  ∀ {n} (Γ : Ctx [] n) → AllUsed (usedCtx Γ)
usedCtx-allUsed ∅ = AU-∅
usedCtx-allUsed (_ ▻ Γ) = AU-used (usedCtx-allUsed Γ)

take-replace :
  ∀ {n K}
    {Γ₀ Γ₁ : Ctx [] n}
    {x : Fin n} {T : NfTy [] K}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₁
  → ReplaceAt Γ₀ x B-Used Γ₁
take-replace take-here = ExprContextReduction.R-here
take-replace (take-thereˡ take) = ExprContextReduction.R-there (take-replace take)
take-replace (take-thereᵘ take) = ExprContextReduction.R-there (take-replace take)
take-replace (take-there✖ take) = ExprContextReduction.R-there (take-replace take)

allUsedCtx-take :
  ∀ {n K}
    {Γ₀ Γ₁ : Ctx [] n}
    {x : Fin n}
    {T : NfTy [] K}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₁
  → allUsedCtx Γ₀ ≡ allUsedCtx Γ₁
allUsedCtx-take take-here = refl
allUsedCtx-take (take-thereˡ take)
  rewrite allUsedCtx-take take = refl
allUsedCtx-take (take-thereᵘ take)
  rewrite allUsedCtx-take take = refl
allUsedCtx-take (take-there✖ take)
  rewrite allUsedCtx-take take = refl

allUsedCtx-remove :
  ∀ {n}
    {Γ₀ G Γ₁ : Ctx [] n}
  → RemoveCtx Γ₀ G Γ₁
  → allUsedCtx Γ₀ ≡ allUsedCtx Γ₁
allUsedCtx-remove RM-∅ = refl
allUsedCtx-remove (RM-drop r)
  rewrite allUsedCtx-remove r = refl
allUsedCtx-remove (RM-allused r)
  rewrite allUsedCtx-remove r = refl
allUsedCtx-remove (RM-lin r)
  rewrite allUsedCtx-remove r = refl
allUsedCtx-remove (RM-un r)
  rewrite allUsedCtx-remove r = refl

allUsedCtx-replace-lin :
  ∀ {n K K′}
    {Γ₀ Γ₁ : Ctx [] n}
    {x : Fin n} {T : NfTy [] K} {U : NfTy [] K′}
  → Γ₀ ∋ˡ x ∶ T
  → ReplaceAt Γ₀ x (B-Lin U) Γ₁
  → allUsedCtx Γ₀ ≡ allUsedCtx Γ₁
allUsedCtx-replace-lin hereˡ ExprContextReduction.R-here = refl
allUsedCtx-replace-lin (thereˡˡ x∈) (ExprContextReduction.R-there rep)
  rewrite allUsedCtx-replace-lin x∈ rep = refl
allUsedCtx-replace-lin (thereˡᵘ x∈) (ExprContextReduction.R-there rep)
  rewrite allUsedCtx-replace-lin x∈ rep = refl
allUsedCtx-replace-lin (thereˡ✖ x∈) (ExprContextReduction.R-there rep)
  rewrite allUsedCtx-replace-lin x∈ rep = refl

allUsedCtx-merge :
  ∀ {n}
    {Γx Γv Γ₁ : Ctx [] n}
  → LinearDisjoint Γx Γv
  → MergeCtx Γx Γv Γ₁
  → allUsedCtx Γx ≡ allUsedCtx Γ₁
allUsedCtx-merge LD-∅ MC-∅ = refl
allUsedCtx-merge (LD-used-used ld) (MC-used-left merge)
  rewrite allUsedCtx-merge ld merge = refl
allUsedCtx-merge (LD-used-used ld) (MC-used-right merge)
  rewrite allUsedCtx-merge ld merge = refl
allUsedCtx-merge (LD-used-live ld) (MC-used-left {b = B-Lin _} merge)
  rewrite allUsedCtx-merge ld merge = refl
allUsedCtx-merge (LD-live-used ld) (MC-used-right merge)
  rewrite allUsedCtx-merge ld merge = refl
allUsedCtx-merge (LD-un-un ld) (MC-un merge)
  rewrite allUsedCtx-merge ld merge = refl

end-subtype-invert :
  ∀ {U : NfTy [] TLin}
  → normalTyOf U <:ₜ normalTyOf (normalizeTy EndLin)
  → U ≡ normalizeTy EndLin
end-subtype-invert {U = mkNfTy .EndLin (N-Sub N-End)} (<:ₜ-sub <:ₜ-end) = refl

remove-disjoint :
  ∀ {n}
    {Γ₀ Γg Γ₂ Γv : Ctx [] n}
  → RemoveCtx Γ₀ Γg Γ₂
  → LinearDisjoint Γ₀ Γv
  → LinearDisjoint Γ₂ Γv
remove-disjoint RM-∅ LD-∅ = LD-∅
remove-disjoint (RM-drop r) (LD-live-used ld) = LD-live-used (remove-disjoint r ld)
remove-disjoint (RM-allused r) (LD-used-used ld) = LD-used-used (remove-disjoint r ld)
remove-disjoint (RM-allused r) (LD-used-live ld) = LD-used-live (remove-disjoint r ld)
remove-disjoint (RM-lin r) (LD-live-used ld) = LD-used-used (remove-disjoint r ld)
remove-disjoint (RM-un r) (LD-un-un ld) = LD-un-un (remove-disjoint r ld)

remove-membership :
  ∀ {n K}
    {Γ₀ G Γ₂ : Ctx [] n}
    {x : Fin n} {T : NfTy [] K}
  → RemoveCtx Γ₀ G Γ₂
  → Γ₂ ∋ˡ x ∶ T
  → Γ₀ ∋ˡ x ∶ T
remove-membership (RM-drop r) hereˡ = hereˡ
remove-membership (RM-drop r) (thereˡˡ x∈) = thereˡˡ (remove-membership r x∈)
remove-membership (RM-lin r) (thereˡ✖ x∈) = thereˡˡ (remove-membership r x∈)
remove-membership (RM-un r) (thereˡᵘ x∈) = thereˡᵘ (remove-membership r x∈)
remove-membership (RM-allused r) (thereˡ✖ x∈) = thereˡ✖ (remove-membership r x∈)

extract-membership :
  ∀ {n K}
    {Γ₀ G Γr : Ctx [] n}
    {x : Fin n} {T : NfTy [] K}
  → RemoveCtx Γ₀ G Γr
  → G ∋ˡ x ∶ T
  → Γ₀ ∋ˡ x ∶ T
extract-membership (RM-lin r) hereˡ = hereˡ
extract-membership (RM-lin r) (thereˡˡ x∈) = thereˡˡ (extract-membership r x∈)
extract-membership (RM-drop r) (thereˡ✖ x∈) = thereˡˡ (extract-membership r x∈)
extract-membership (RM-un r) (thereˡᵘ x∈) = thereˡᵘ (extract-membership r x∈)
extract-membership (RM-allused r) (thereˡ✖ x∈) = thereˡ✖ (extract-membership r x∈)

remove-self-allUsed :
  ∀ {n}
    {Γ₀ G : Ctx [] n}
  → RemoveCtx Γ₀ G Γ₀
  → G ≡ allUsedCtx Γ₀
remove-self-allUsed RM-∅ = refl
remove-self-allUsed (RM-drop r)
  rewrite remove-self-allUsed r = refl
remove-self-allUsed (RM-allused r)
  rewrite remove-self-allUsed r = refl
remove-self-allUsed (RM-un r)
  rewrite remove-self-allUsed r = refl

extract-beta-eq :
  ∀ {n}
    {Γ₀ Γin : Ctx [] n}
  → Extract Γ₀ ExprSemantics.L-β Γin
  → Γin ≡ allUsedCtx Γ₀
extract-beta-eq Ex-β = refl

extract-fork-eq :
  ∀ {n}
    {Γ₀ Γin : Ctx [] n} {v : Value [] n}
  → Extract Γ₀ (ExprSemantics.L-Fork v) Γin
  → Γin ≡ allUsedCtx Γ₀
extract-fork-eq Ex-Fork = refl

extract-new-eq :
  ∀ {n}
    {Γ₀ Γin : Ctx [] n} {S : Ty [] SLin}
  → Extract Γ₀ (ExprSemantics.L-New S) Γin
  → Γin ≡ allUsedCtx Γ₀
extract-new-eq Ex-New = refl

extract-close-eq :
  ∀ {n}
    {Γ₀ Γin : Ctx [] n} {x : Fin n}
  → Extract Γ₀ (ExprSemantics.L-Close x) Γin
  → Γin ≡ allUsedCtx Γ₀
extract-close-eq Ex-Close = refl

record PresSynth
    {n k pk mult}
    (Γin : Ctx [] n)
    (Γv : Ctx [] n)
    {ℓ : Label n k}
    (lbl : ℓ ⦂ Γin ⇒ Γv)
    (Γ₀ : Ctx [] n)
    (Γ₂ : Ctx [] n)
    (e₂ : Expr [] (k + n))
    (T : NfTy [] (KV pk mult)) : Set where
  field
    Gf : Ctx [] n
    Γ₀′ : Ctx [] n
    Γ₁ : Ctx [] (k + n)
    Γ₁′ : Ctx [] (k + n)
    U : NfTy [] (KV pk mult)

    src-remove : RemoveCtx Γ₀ Gf Γ₀′
    dst-remove : RemoveCtx Γ₁ (extendUsed k Gf) Γ₁′
    ctx-step : Γ₀′ —ctx[ ℓ ]→ Γ₁′
    compat : Compatible ctx-step lbl
    synth : Γ₁ ⊢ e₂ ⇒ U ⊣ extendUsed k Γ₂
    subtype : normalTyOf U <:ₜ normalTyOf T

record PresCheck
    {n k pk mult}
    (Γin : Ctx [] n)
    (Γv : Ctx [] n)
    {ℓ : Label n k}
    (lbl : ℓ ⦂ Γin ⇒ Γv)
    (Γ₀ : Ctx [] n)
    (Γ₂ : Ctx [] n)
    (e₂ : Expr [] (k + n))
    (T : NfTy [] (KV pk mult)) : Set where
  field
    Gf : Ctx [] n
    Γ₀′ : Ctx [] n
    Γ₁ : Ctx [] (k + n)
    Γ₁′ : Ctx [] (k + n)

    src-remove : RemoveCtx Γ₀ Gf Γ₀′
    dst-remove : RemoveCtx Γ₁ (extendUsed k Gf) Γ₁′
    ctx-step : Γ₀′ —ctx[ ℓ ]→ Γ₁′
    compat : Compatible ctx-step lbl
    check : Γ₁ ⊢ e₂ ⇐ T ⊣ extendUsed k Γ₂

postulate
  preserve⇒-hard :
    ∀ {n k pk mult}
      {Γ₀ : Ctx [] n} {Γ₂ : Ctx [] n}
      {Γin Γv : Ctx [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] (k + n)}
      {T : NfTy [] (KV pk mult)} {ℓ : Label n k}
    → Γ₀ ⊢ e₁ ⇒ T ⊣ Γ₂
    → e₁ —[ ℓ ]→ e₂
    → (lbl : ℓ ⦂ Γin ⇒ Γv)
    → Extract Γ₀ ℓ Γin
    → LinearDisjoint Γ₀ Γv
    → PresSynth Γin Γv lbl Γ₀ Γ₂ e₂ T

basePres :
  ∀ {n pk mult}
    {Γ₀ Γ₂ Γin : Ctx [] n}
    {Γv : Ctx [] n}
    {e₂ : Expr [] n}
    {T U : NfTy [] (KV pk mult)}
  → (step : Γ₀ —ctx[ ExprSemantics.L-β ]→ Γ₀)
  → (lbl : ExprSemantics.L-β ⦂ Γin ⇒ Γv)
  → Extract Γ₀ ExprSemantics.L-β Γin
  → Compatible step lbl
  → Γ₀ ⊢ e₂ ⇒ U ⊣ Γ₂
  → normalTyOf U <:ₜ normalTyOf T
  → PresSynth Γin Γv lbl Γ₀ Γ₂ e₂ T
postulate
  basePres-proof :
    ∀ {n pk mult}
      {Γ₀ Γ₂ Γin : Ctx [] n}
      {Γv : Ctx [] n}
      {e₂ : Expr [] n}
      {T U : NfTy [] (KV pk mult)}
    → (step : Γ₀ —ctx[ ExprSemantics.L-β ]→ Γ₀)
    → (lbl : ExprSemantics.L-β ⦂ Γin ⇒ Γv)
    → Extract Γ₀ ExprSemantics.L-β Γin
    → Compatible step lbl
    → Γ₀ ⊢ e₂ ⇒ U ⊣ Γ₂
    → normalTyOf U <:ₜ normalTyOf T
    → PresSynth Γin Γv lbl Γ₀ Γ₂ e₂ T

beta-compatible :
  ∀ {n}
    {Γ₀ Γv Γin : Ctx [] n}
  → (lbl : ExprSemantics.L-β ⦂ Γin ⇒ Γv)
  → Extract Γ₀ ExprSemantics.L-β Γin
  → Compatible {Γ₀ = Γ₀} {Γ₁ = Γ₀} Ctx-β lbl
beta-compatible {Γ₀ = Γ₀} (Label-β _ _) ex
  rewrite extract-beta-eq ex = Compat-β refl

close-compatible :
  ∀ {n}
    {Γ₀ Γ₂ Γin Γv : Ctx [] n}
    {x : Fin n}
    {x∈ : Γ₀ ∋ˡ x ∶ normalizeTy EndLin}
    {rep : ReplaceAt Γ₀ x B-Used Γ₂}
    {lbl : ExprSemantics.L-Close x ⦂ Γin ⇒ Γv}
  → Extract Γ₀ (ExprSemantics.L-Close x) Γin
  → Compatible (Ctx-Close x∈ rep) lbl
close-compatible {Γ₀ = Γ₀} {lbl = Label-Close _ _} ex
  rewrite extract-close-eq ex = Compat-Close refl

fork-compatible :
  ∀ {n}
    {Γ₀ Γ₁ Γin Γv Γloc Γloc′ : Ctx [] n}
    {v : Value [] n}
    {rm : RemoveCtx Γ₀ Γloc Γ₁}
    {dv : Γloc ⊢ E-Val v ⇐ linArrNf unitLinNf unitLinNf ⊣ Γloc′}
    {au : AllUsed Γloc′}
    {lbl : ExprSemantics.L-Fork v ⦂ Γin ⇒ Γv}
  → Extract Γ₀ (ExprSemantics.L-Fork v) Γin
  → Compatible (Ctx-Fork rm dv au) lbl
fork-compatible {Γ₀ = Γ₀} {lbl = Label-Fork _ _} ex
  rewrite extract-fork-eq ex = Compat-Fork refl

new-compatible :
  ∀ {n}
    {Γ₀ Γin Γv : Ctx [] n}
    {S : Ty [] SLin}
    {lbl : ExprSemantics.L-New S ⦂ Γin ⇒ Γv}
  → Extract Γ₀ (ExprSemantics.L-New S) Γin
    → Compatible {Γ₀ = Γ₀}
        (Ctx-New {Γ₀ = Γ₀} {S = S}) lbl
new-compatible {Γ₀ = Γ₀} {S = S} {lbl = lbl} ex
  rewrite extract-new-eq ex = go
  where
  go :
    ∀ {Γv}
      {lbl′ : ExprSemantics.L-New S ⦂ allUsedCtx Γ₀ ⇒ Γv}
    → Compatible {Γ₀ = Γ₀}
        (Ctx-New {Γ₀ = Γ₀} {S = S}) lbl′
  go {lbl′ = lbl′} with lbl′
  ... | ECR.Label-New _ _ = Compat-New refl

remove-extract :
  ∀ {n k}
    {Γ₀ Γ₂ : Ctx [] n}
    {Γin G : Ctx [] n}
    {ℓ : Label n k}
  → RemoveCtx Γ₀ G Γ₂
  → LinearDisjoint G Γin
  → Extract Γ₀ ℓ Γin
  → Extract Γ₂ ℓ Γin
remove-extract {Γ₂ = Γ₂} r ld ex@Ex-β
  rewrite extract-beta-eq ex =
  subst (λ X → Extract Γ₂ ExprSemantics.L-β X) (sym (allUsedCtx-remove r)) Ex-β
remove-extract {Γ₂ = Γ₂} r ld ex@Ex-Fork
  rewrite extract-fork-eq ex =
  subst (λ X → Extract Γ₂ (ExprSemantics.L-Fork _) X) (sym (allUsedCtx-remove r)) Ex-Fork
remove-extract {Γ₂ = Γ₂} r ld ex@Ex-New
  rewrite extract-new-eq ex =
  subst (λ X → Extract Γ₂ (ExprSemantics.L-New _) X) (sym (allUsedCtx-remove r)) Ex-New
remove-extract r ld (Ex-RecvVal rin take au) with remove-preserves-remove r rin ld
... | Γr′ , rin′ = Ex-RecvVal rin′ take au
remove-extract {Γ₂ = Γ₂} r ld Ex-RecvLab =
  subst (λ X → Extract Γ₂ (ExprSemantics.L-RecvLab _ _) X) (sym (allUsedCtx-remove r)) Ex-RecvLab
remove-extract {Γ₂ = Γ₂} r ld Ex-SendVal =
  subst (λ X → Extract Γ₂ (ExprSemantics.L-SendVal _ _) X) (sym (allUsedCtx-remove r)) Ex-SendVal
remove-extract {Γ₂ = Γ₂} r ld Ex-SendLab =
  subst (λ X → Extract Γ₂ (ExprSemantics.L-SendLab _ _) X) (sym (allUsedCtx-remove r)) Ex-SendLab
remove-extract {Γ₂ = Γ₂} r ld ex@Ex-Close
  rewrite extract-close-eq ex =
  subst (λ X → Extract Γ₂ (ExprSemantics.L-Close _) X) (sym (allUsedCtx-remove r)) Ex-Close

remove-allused-disjoint2 :
  ∀ {n}
    {Γ₀ Γ₂ Γr G H : Ctx [] n}
  → RemoveCtx Γ₀ G Γ₂
  → RemoveCtx Γ₀ H Γr
  → AllUsed H
  → LinearDisjoint G H
remove-allused-disjoint2 RM-∅ RM-∅ AU-∅ = LD-∅
remove-allused-disjoint2 (RM-drop r₁) (RM-drop r₂) (AU-used au) =
  LD-used-used (remove-allused-disjoint2 r₁ r₂ au)
remove-allused-disjoint2 (RM-lin r₁) (RM-drop r₂) (AU-used au) =
  LD-live-used (remove-allused-disjoint2 r₁ r₂ au)
remove-allused-disjoint2 (RM-allused r₁) (RM-allused r₂) (AU-used au) =
  LD-used-used (remove-allused-disjoint2 r₁ r₂ au)
remove-allused-disjoint2 (RM-un r₁) (RM-un r₂) (AU-un au) =
  LD-un-un (remove-allused-disjoint2 r₁ r₂ au)

recv-input-disjoint-core :
  ∀ {n K K′}
    {Γ₀ Γ₂ Γin Γr Γin′ G : Ctx [] n}
    {x : Fin n}
    {T : NfTy [] K}
    {U : NfTy [] K′}
  → RemoveCtx Γ₀ G Γ₂
  → RemoveCtx Γ₀ Γin Γr
  → Γin ⊢ˡ x ∶ T ⊣ Γin′
  → AllUsed Γin′
  → Γ₂ ∋ˡ x ∶ U
  → LinearDisjoint G Γin
recv-input-disjoint-core {x = fzero}
  (RM-drop r)
  (RM-lin rin)
  take-here
  (AU-used au)
  hereˡ =
  LD-used-live (remove-allused-disjoint2 r rin au)
recv-input-disjoint-core {x = fsuc x}
  (RM-drop r)
  (RM-drop rin)
  (take-there✖ take)
  (AU-used au)
  (thereˡˡ x∈) =
  LD-used-used (recv-input-disjoint-core {x = x} r rin take au x∈)
recv-input-disjoint-core {x = fsuc x}
  (RM-un r)
  (RM-un rin)
  (take-thereᵘ take)
  (AU-un au)
  (thereˡᵘ x∈) =
  LD-un-un (recv-input-disjoint-core {x = x} r rin take au x∈)
recv-input-disjoint-core {x = fsuc x}
  (RM-lin r)
  (RM-drop rin)
  (take-there✖ take)
  (AU-used au)
  (thereˡ✖ x∈) =
  LD-live-used (recv-input-disjoint-core {x = x} r rin take au x∈)
recv-input-disjoint-core {x = fsuc x}
  (RM-allused r)
  (RM-allused rin)
  (take-there✖ take)
  (AU-used au)
  (thereˡ✖ x∈) =
  LD-used-used (recv-input-disjoint-core {x = x} r rin take au x∈)

recv-extract-disjoint :
  ∀ {n K}
    {Γ₀ Γ₂ Γin G : Ctx [] n}
    {x : Fin n} {v : Value [] n}
    {U : NfTy [] K}
  → RemoveCtx Γ₀ G Γ₂
  → Extract Γ₀ (ExprSemantics.L-RecvVal x v) Γin
  → Γ₂ ∋ˡ x ∶ U
  → LinearDisjoint G Γin
recv-extract-disjoint r (Ex-RecvVal rin take au) x∈ =
  recv-input-disjoint-core r rin take au x∈

postulate
  appR-extract-disjoint-recv-general :
    ∀ {n}
      {Γ₀ Γ₂ Γin G : Ctx [] n}
      {x : Fin n} {v : Value [] n}
    → RemoveCtx Γ₀ G Γ₂
    → Extract Γ₀ (ExprSemantics.L-RecvVal x v) Γin
    → LinearDisjoint G Γin

  appR-extract-disjoint-recv :
    ∀ {n}
      {Γ₀ Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {v : Value [] n}
      {e₁ e₂ : Expr [] n}
      {A : NfTy [] TLin}
      {G : Ctx [] n}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇐ A ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-RecvVal x v ]→ e₂
    → Extract Γ₀ (ExprSemantics.L-RecvVal x v) Γin
    → LinearDisjoint G Γin

appR-extract-disjoint :
  ∀ {n k}
    {Γ₀ Γ₂ : Ctx [] n}
    {Γin G : Ctx [] n}
    {ℓ : Label n k}
  → RemoveCtx Γ₀ G Γ₂
  → Extract Γ₀ ℓ Γin
  → LinearDisjoint G Γin
appR-extract-disjoint r ex@Ex-β
  rewrite extract-beta-eq ex = remove-allused-disjoint r
appR-extract-disjoint r ex@Ex-Fork
  rewrite extract-fork-eq ex = remove-allused-disjoint r
appR-extract-disjoint r ex@Ex-New
  rewrite extract-new-eq ex = remove-allused-disjoint r
appR-extract-disjoint r ex@(Ex-RecvVal _ _ _) =
  appR-extract-disjoint-recv-general r ex
appR-extract-disjoint r Ex-RecvLab =
  remove-allused-disjoint r
appR-extract-disjoint r Ex-SendVal =
  remove-allused-disjoint r
appR-extract-disjoint r Ex-SendLab =
  remove-allused-disjoint r
appR-extract-disjoint r ex@Ex-Close
  rewrite extract-close-eq ex = remove-allused-disjoint r

basePres step lbl ex compat synth sub =
  basePres-proof step lbl ex compat synth sub

receive-live-synth :
  ∀ {n pk mult}
    {Γ₀ Γ₂ Γin : Ctx [] n}
    {e₁ e₂ : Expr [] n}
    {T : NfTy [] (KV pk mult)}
    {x : Fin n} {v : Value [] n}
  → Γ₀ ⊢ e₁ ⇒ T ⊣ Γ₂
  → e₁ —[ ExprSemantics.L-RecvVal x v ]→ e₂
  → Extract Γ₀ (ExprSemantics.L-RecvVal x v) Γin
  → Σ Kind λ K → Σ (NfTy [] K) λ U → Γ₀ ∋ˡ x ∶ U
receive-live-synth _ _ (Ex-RecvVal rin take _) =
  _ , _ , extract-membership rin (take-implies-membership take)

receive-live-check :
  ∀ {n pk mult}
    {Γ₀ Γ₂ Γin : Ctx [] n}
    {e₁ e₂ : Expr [] n}
    {T : NfTy [] (KV pk mult)}
    {x : Fin n} {v : Value [] n}
  → Γ₀ ⊢ e₁ ⇐ T ⊣ Γ₂
  → e₁ —[ ExprSemantics.L-RecvVal x v ]→ e₂
  → Extract Γ₀ (ExprSemantics.L-RecvVal x v) Γin
  → Σ Kind λ K → Σ (NfTy [] K) λ U → Γ₀ ∋ˡ x ∶ U
receive-live-check (T-Check d _) step ex =
  receive-live-synth d step ex

weaken-val-synth :
  ∀ {n k K}
    {Γ₁ Γ₂ : Ctx [] n}
    {v : Value [] n}
    {T : NfTy [] K}
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  → extendUsed k Γ₁ ⊢ E-Val (ES.weakenValueBy k v) ⇒ T ⊣ extendUsed k Γ₂
weaken-val-synth {k = k} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = v} dv =
  subst
    (λ G₁′ → G₁′ ⊢ E-Val (ES.weakenValueBy k v) ⇒ _ ⊣ extendUsed k Γ₂)
    (extendUsed-eq k Γ₁)
    (subst
      (λ G₂′ → EPS.extendUsed k Γ₁ ⊢ E-Val (ES.weakenValueBy k v) ⇒ _ ⊣ G₂′)
      (extendUsed-eq k Γ₂)
      (weaken-synth {k = k} (T-Val dv)))

postulate
  tapp-receive-output-id :
    ∀ {n}
      {Γ₀ Γ₂ : Ctx [] n}
      {T : Ty [] TLin}
      {U : NfTy [] (KV KT Lin)}
    → Γ₀ ⊢ E-TApp (E-Val (V-Const C-Receive)) T ⇒ U ⊣ Γ₂
    → Γ₂ ≡ Γ₀

  tapp-receive₁-output-id :
    ∀ {n}
      {Γ₀ Γ₂ : Ctx [] n}
      {T : Ty [] TLin}
      {S : Ty [] SLin}
      {U : NfTy [] (KV KT Lin)}
    → Γ₀ ⊢ E-TApp (E-Val (V-Receive₁ T)) S ⇒ U ⊣ Γ₂
    → Γ₂ ≡ Γ₀

allUsed-extendUsed :
  ∀ {n} (k : ℕ) {Γ : Ctx [] n}
  → AllUsed Γ
  → AllUsed (extendUsed k Γ)
allUsed-extendUsed zero au = au
allUsed-extendUsed (suc k) au = AU-used (allUsed-extendUsed k au)

extendUsed-disjoint :
  ∀ {n} (k : ℕ)
    {Γ₁ Γ₂ : Ctx [] n}
  → LinearDisjoint Γ₁ Γ₂
  → LinearDisjoint (extendUsed k Γ₁) (extendUsed k Γ₂)
extendUsed-disjoint zero ld = ld
extendUsed-disjoint (suc k) ld = LD-used-used (extendUsed-disjoint k ld)

extend-remove :
  ∀ (k : ℕ) {n}
    {Γ₀ G Γ₂ : Ctx [] n}
  → RemoveCtx Γ₀ G Γ₂
  → RemoveCtx (extendUsed k Γ₀) (extendUsed k G) (extendUsed k Γ₂)
extend-remove zero r = r
extend-remove (suc k) r = RM-allused (extend-remove k r)

merge-result-unique :
  ∀ {n}
    {Γ₁ Γ₂ Γ Γ′ : Ctx [] n}
  → MergeCtx Γ₁ Γ₂ Γ
  → MergeCtx Γ₁ Γ₂ Γ′
  → Γ ≡ Γ′
merge-result-unique MC-∅ MC-∅ = refl
merge-result-unique (MC-used-left m₁) (MC-used-left m₂)
  rewrite merge-result-unique m₁ m₂ = refl
merge-result-unique (MC-used-left m₁) (MC-used-right m₂)
  rewrite merge-result-unique m₁ m₂ = refl
merge-result-unique (MC-used-right m₁) (MC-used-left m₂)
  rewrite merge-result-unique m₁ m₂ = refl
merge-result-unique (MC-used-right m₁) (MC-used-right m₂)
  rewrite merge-result-unique m₁ m₂ = refl
merge-result-unique (MC-un m₁) (MC-un m₂)
  rewrite merge-result-unique m₁ m₂ = refl

merge-extendUsed :
  ∀ {n}
    (k : ℕ)
    {Γ₁ Γ₂ Γ : Ctx [] n}
  → MergeCtx Γ₁ Γ₂ Γ
  → MergeCtx (extendUsed k Γ₁) (extendUsed k Γ₂) (extendUsed k Γ)
merge-extendUsed zero m = m
merge-extendUsed (suc k) m = MC-used-left (merge-extendUsed k m)

sym-disjoint :
  ∀ {n} {Γ₁ Γ₂ : Ctx [] n}
  → LinearDisjoint Γ₁ Γ₂
  → LinearDisjoint Γ₂ Γ₁
sym-disjoint LD-∅ = LD-∅
sym-disjoint (LD-used-used d) = LD-used-used (sym-disjoint d)
sym-disjoint (LD-used-live d) = LD-live-used (sym-disjoint d)
sym-disjoint (LD-live-used d) = LD-used-live (sym-disjoint d)
sym-disjoint (LD-un-un d) = LD-un-un (sym-disjoint d)

preserve⇒-close :
  ∀ {n}
    {Γ₀ Γm Γ₂ Γin Γv : Ctx [] n}
    {x : Fin n}
    {A U R : NfTy [] TLin}
  → Γ₀ ⊢ᵥ V-Const C-Close ⇒ linArrNf A R ⊣ Γm
  → Γm ⊢ˡ x ∶ U ⊣ Γ₂
  → normalTyOf U <:ₜ normalTyOf A
  → (lbl : ExprSemantics.L-Close x ⦂ Γin ⇒ Γv)
  → Extract Γ₀ (ExprSemantics.L-Close x) Γin
  → PresSynth Γin Γv lbl Γ₀ Γ₂ (E-Val (V-Const C-Unit)) R
preserve⇒-close {Γ₀ = Γ₀} {Γ₂ = Γ₂} {x = x} {A = A} {U = U} {R = R}
  vr take sub lbl@(Label-Close _ _) ex
  with close-inversion vr
... | refl , eqClose
  with linArrNf-injective (trans eqClose closeTy-shape)
... | eqA , eqR =
  let
    eqU : U ≡ normalizeTy EndLin
    eqU = end-subtype-invert (subst (λ X → normalTyOf U <:ₜ normalTyOf X) eqA sub)

    take′ : Γ₀ ⊢ˡ x ∶ normalizeTy EndLin ⊣ Γ₂
    take′ = subst (λ X → Γ₀ ⊢ˡ x ∶ X ⊣ Γ₂) eqU take

    rep : ReplaceAt Γ₀ x B-Used Γ₂
    rep = take-replace take′

    step : Γ₀ —ctx[ ExprSemantics.L-Close x ]→ Γ₂
    step = Ctx-Close (take-implies-membership take′) rep
  in
    subst
      (λ G₂ →
        PresSynth _ _ lbl Γ₀ G₂ (E-Val (V-Const C-Unit)) R)
      (replace-used-output take′ rep)
      (record
        { Gf = allUsedCtx Γ₀
        ; Γ₀′ = Γ₀
        ; Γ₁ = Γ₂
        ; Γ₁′ = Γ₂
        ; U = normalizeTy T-Base
        ; src-remove = remove-usedCtx Γ₀
        ; dst-remove =
            subst
              (λ Gf → RemoveCtx Γ₂ (extendUsed zero Gf) Γ₂)
              (sym (allUsedCtx-take take′))
              (remove-usedCtx Γ₂)
        ; ctx-step = step
        ; compat = close-compatible ex
        ; synth = T-Val (TV-Const CT-Unit)
        ; subtype =
            subst
              (λ X → normalTyOf (normalizeTy T-Base) <:ₜ normalTyOf X)
              (sym eqR)
              (<:ₜ-refl (normalTyOf (normalizeTy T-Base)))
        })

mutual

  preserve⇒ :
    ∀ {n k pk mult}
      {Γ₀ : Ctx [] n} {Γ₂ : Ctx [] n}
      {Γin Γv : Ctx [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] (k + n)}
      {T : NfTy [] (KV pk mult)} {ℓ : Label n k}
    → Γ₀ ⊢ e₁ ⇒ T ⊣ Γ₂
    → e₁ —[ ℓ ]→ e₂
    → (lbl : ℓ ⦂ Γin ⇒ Γv)
    → Extract Γ₀ ℓ Γin
    → LinearDisjoint Γ₀ Γv
    → PresSynth Γin Γv lbl Γ₀ Γ₂ e₂ T
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    (T-App {T = A} {U = R} (T-Val vr) pv)
    (Act-App {T = Tₐ} {e = e} {v = v})
    lbl@(Label-β _ auv) ex _
    with abs-inversion vr
  ... | U , eqAbs , body
    with linArrNf-injective eqAbs
  ... | eqA , eqU
    rewrite eqA | eqU =
      basePres {Γ₀ = Γ₀} {Γ₂ = Γ₂} {U = U} Ctx-β lbl ex (beta-compatible lbl ex)
        (subst-check-preserves-synth {T = Tₐ} pv body)
        (<:ₜ-refl (normalTyOf U))
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    (T-TApp {T = T′} (T-Val vr))
    (Act-TApp {K = K} {T = T} {v = v})
    lbl@(Label-β _ auv) ex _
    with tabs-inversion vr
  ... | mkNfTy T₀ N₀ , eq , p
    rewrite polyNf-injective {Δ = []} eq =
      basePres {Γ₀ = Γ₀} {Γ₂ = Γ₂} {U = normalizeTy (T₀ ⋯ ⦅ T ⦆ₛ)} Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val
          (subst
            (λ X → X ⊢ᵥ substTyValue v T ⇒ normalizeTy (T₀ ⋯ ⦅ T ⦆ₛ) ⊣ Γ₂)
            (substTy-wkCtx-id Γ₀ T)
            (subst
              (λ X → EST.substTyCtx (wkCtx Γ₀) T ⊢ᵥ substTyValue v T ⇒ normalizeTy (T₀ ⋯ ⦅ T ⦆ₛ) ⊣ X)
              (substTy-wkCtx-id Γ₂ T)
              (substTy-preserves-value p))))
        (<:ₜ-refl (normalTyOf (normalizeTy (T₀ ⋯ ⦅ T ⦆ₛ))))
  preserve⇒ {Γ₀ = Γ₀} {Γ₂ = Γ₂} {T = T}
    (T-LetUnit (T-Check (T-Val (TV-Const CT-Unit)) _) d₂)
    Act-LetUnit lbl@(Label-β _ auv) ex _ =
    basePres {Γ₀ = Γ₀} {Γ₂ = Γ₂} {U = T} Ctx-β lbl ex (beta-compatible lbl ex) d₂ (<:ₜ-refl (normalTyOf T))
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = V}
    (T-LetPair (T-Val pv) body)
    (Act-LetPair {u = u} {v = v} {e = e})
    lbl@(Label-β _ auv) ex _
    with pair-inversion′ pv
  ... | Γ₁ , pu , pv′ =
    basePres {Γ₀ = Γ₀} {Γ₂ = Γ₂} {U = V} Ctx-β lbl ex (beta-compatible lbl ex)
      (subst2-preserves-synth pu pv′ body)
      (<:ₜ-refl (normalTyOf V))
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    (T-App (T-Val vr) pu)
    (Act-Rec {T = T} {U = U} {v = v} {u = u})
    lbl@(Label-β _ auv) ex _
    with rec-inversion vr
  ... | refl , eqRec , _
    with linArrNf-injective eqRec
  ... | refl , refl =
    basePres {Γ₀ = Γ₀} {Γ₂ = Γ₂} {U = R} Ctx-β lbl ex (beta-compatible lbl ex)
      (T-App
        (T-Val (rec-unfold-preserves-value vr))
        pu)
      (<:ₜ-refl (normalTyOf R))
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {Γv = Γv}
    {e₁ = E-App (E-Val (V-Const C-Fork)) (E-Val v)}
    {e₂ = E-Val (V-Const C-Unit)}
    (T-App {T = A} {U = R} (T-Val vr) (T-Check (T-Val vv) sub))
    Act-Fork
    lbl@(Label-Fork _ auLbl) ex _
    with fork-shape vr
  ... | refl , (eqA , eqR)
    with strip-value vv
  ... | G , G′ , r , dv′ , au
    rewrite eqA = record
      { Gf = allUsedCtx Γ₀
      ; Γ₀′ = Γ₀
      ; Γ₁ = Γ₂
      ; Γ₁′ = Γ₂
      ; U = normalizeTy T-Base
      ; src-remove = remove-usedCtx Γ₀
      ; dst-remove =
          subst
            (λ X → RemoveCtx Γ₂ (extendUsed zero X) Γ₂)
            (sym (allUsedCtx-remove r))
            (remove-usedCtx Γ₂)
      ; ctx-step = Ctx-Fork r (T-Check (T-Val dv′) sub) au
      ; compat = fork-compatible ex
      ; synth = T-Val (TV-Const CT-Unit)
      ; subtype =
          subst
            (λ X → normalTyOf (normalizeTy T-Base) <:ₜ normalTyOf X)
            (sym eqR)
            (<:ₜ-refl (normalTyOf (normalizeTy T-Base)))
      }
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    (T-TApp {T = T′} (T-Val vr))
    (Act-New {S = S})
    lbl ex _
    with new-shape vr
  ... | refl , eqT
    rewrite eqT =
      record
        { Gf = allUsedCtx Γ₀
        ; Γ₀′ = Γ₀
        ; Γ₁ = B-Lin (normalizeTy (SessLin S)) ▻ (B-Lin (dualSessNf (normalizeTy S)) ▻ Γ₀)
        ; Γ₁′ = B-Lin (normalizeTy (SessLin S)) ▻ (B-Lin (dualSessNf (normalizeTy S)) ▻ Γ₀)
        ; U = pairNf (normalizeTy (SessLin S)) (dualSessNf (normalizeTy S))
        ; src-remove = remove-usedCtx Γ₀
        ; dst-remove = remove-usedCtx (B-Lin (normalizeTy (SessLin S)) ▻ (B-Lin (dualSessNf (normalizeTy S)) ▻ Γ₀))
        ; ctx-step = Ctx-New
        ; compat = new-compatible ex
        ; synth =
            T-Val
              (TV-Pair
                (TV-Var-Lin take-here)
                (TV-Var-Lin (take-there✖ take-here)))
        ; subtype =
            subst
              (λ X → normalTyOf (pairNf (normalizeTy (SessLin S)) (dualSessNf (normalizeTy S))) <:ₜ normalTyOf X)
              (sym (newInst-shape {S = S}))
              (<:ₜ-refl (normalTyOf (pairNf (normalizeTy (SessLin S)) (dualSessNf (normalizeTy S)))))
        }
  preserve⇒ {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    (T-Pair {T = T} {U = U} (T-Val du) (T-Val dv))
    Act-PairV lbl@(Label-β _ auv) ex _ =
    basePres {Γ₀ = Γ₀} {Γ₂ = Γ₂} {U = pairNf T U} Ctx-β lbl ex (beta-compatible lbl ex)
      (T-Val (TV-Pair du dv)) (<:ₜ-refl (normalTyOf (pairNf T U)))
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {e₁ = E-App (E-Val (V-Const C-Close)) (E-Val (V-Var x))}
    {e₂ = E-Val (V-Const C-Unit)}
    (T-App {T = A} {U = R} (T-Val vr) (T-Check (T-Val {T = U} (TV-Var-Lin take)) sub))
    Act-Close lbl@(Label-Close _ _) ex _ =
    preserve⇒-close vr take sub lbl ex
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-App e₁ e₃}
    {T = V} {ℓ = ℓ}
    (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V} d₁ (T-Check pArg subArg))
    (Act-AppL {k = k} {e₁ = e₁} {e₂ = e₂} {e₃ = e₃} step)
    lbl ex disj
    with preserve⇒ d₁ step lbl ex disj
  ... | ps
    with arrow-subtype-inversion {A = A} {V = V} (PresSynth.subtype ps)
  ... | A′ , V′ , eqU , A<:A′ , V′<:V =
    let
      pArg′ : extendUsed k Γ₂ ⊢ ES.weakenExprBy k e₃ ⇒ _ ⊣ extendUsed k Γ₃
      pArg′ =
        subst
          (λ G₂′ → G₂′ ⊢ ES.weakenExprBy k e₃ ⇒ _ ⊣ extendUsed k Γ₃)
          (extendUsed-eq k Γ₂)
          (subst
            (λ G₃′ → EPS.extendUsed k Γ₂ ⊢ ES.weakenExprBy k e₃ ⇒ _ ⊣ G₃′)
            (extendUsed-eq k Γ₃)
            (weaken-synth {k = k} pArg))
    in
    record
      { Gf = PresSynth.Gf ps
      ; Γ₀′ = PresSynth.Γ₀′ ps
      ; Γ₁ = PresSynth.Γ₁ ps
      ; Γ₁′ = PresSynth.Γ₁′ ps
      ; U = V′
      ; src-remove = PresSynth.src-remove ps
      ; dst-remove = PresSynth.dst-remove ps
      ; ctx-step = PresSynth.ctx-step ps
      ; compat = PresSynth.compat ps
      ; synth =
          T-App
            (subst
              (λ X → PresSynth.Γ₁ ps ⊢ e₂ ⇒ X ⊣ extendUsed k Γ₂)
              eqU
              (PresSynth.synth ps))
            (T-Check pArg′
              (<:ₜ-trans subArg A<:A′))
      ; subtype = V′<:V
      }
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-App (E-Val v) e₁}
    {T = V} {ℓ = ℓ}
    (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V}
      (T-Val dv)
      (T-Check pArg subArg))
    (Act-AppR {k = k} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@(Ex-RecvVal {x = x} {v = vᵣ} _ _ _) disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    with preserve⇐ {T = A} (T-Check pArg subArg) step lbl
         (remove-extract r (appR-extract-disjoint-recv {A = A} r (T-Check pArg subArg) step ex) ex)
         (remove-disjoint r disj)
  ... | pc
    with ctx-step-preserves-disjoint
           (PresCheck.ctx-step pc)
           lbl
           (PresCheck.compat pc)
           (remove-preserves-disjoint
             (PresCheck.src-remove pc)
             (sym-disjoint (remove-linear r)))
           (sym-disjoint (remove-removed-disjoint r disj))
  ... | ldstep
    with restore-disjoint
           (PresCheck.dst-remove pc)
           (subst
             (λ X → LinearDisjoint (PresCheck.Γ₁′ pc) X)
             (extendUsedCR-eq k G)
             ldstep)
           (extendUsed-disjoint k
             (remove-removed-disjoint
               (PresCheck.src-remove pc)
               (sym-disjoint (remove-linear r))))
  ... | ldtarget
    with mergeRemoveContext r (PresCheck.src-remove pc)
  ... | Gf , msrc , rsrc
    with mergeDisjointContext ldtarget
  ... | Γ₁ , mleft
    with frame-remove
           (merge-frame ldtarget mleft)
  ... | dstr
    with mergeRemoveContext dstr (PresCheck.dst-remove pc)
  ... | Gfdst , mdst , rdst
    with merge-result-unique mdst (merge-extendUsed k msrc)
  ... | eqG = record
    { Gf = Gf
    ; Γ₀′ = PresCheck.Γ₀′ pc
    ; Γ₁ = Γ₁
    ; Γ₁′ = PresCheck.Γ₁′ pc
    ; U = V
    ; src-remove = rsrc
    ; dst-remove =
        subst
          (λ X → RemoveCtx Γ₁ X (PresCheck.Γ₁′ pc))
          eqG
          rdst
    ; ctx-step = PresCheck.ctx-step pc
    ; compat = PresCheck.compat pc
    ; synth =
        T-App
          (replay-synth
            (weaken-val-synth {k = k} dv′)
            (remove-frame dstr)
            (allUsed-frame {Φ = PresCheck.Γ₁ pc} (allUsed-extendUsed k au)))
          (PresCheck.check pc)
    ; subtype = <:ₜ-refl (normalTyOf V)
    }
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-App (E-Val v) e₁}
    {T = V} {ℓ = ℓ}
    (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V}
      (T-Val dv)
      (T-Check pArg subArg))
    (Act-AppR {k = k} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    with preserve⇐ {T = A} (T-Check pArg subArg) step lbl
         (remove-extract r (appR-extract-disjoint r ex) ex)
         (remove-disjoint r disj)
  ... | pc
    with ctx-step-preserves-disjoint
           (PresCheck.ctx-step pc)
           lbl
           (PresCheck.compat pc)
           (remove-preserves-disjoint
             (PresCheck.src-remove pc)
             (sym-disjoint (remove-linear r)))
           (sym-disjoint (remove-removed-disjoint r disj))
  ... | ldstep
    with restore-disjoint
           (PresCheck.dst-remove pc)
           (subst
             (λ X → LinearDisjoint (PresCheck.Γ₁′ pc) X)
             (extendUsedCR-eq k G)
             ldstep)
           (extendUsed-disjoint k
             (remove-removed-disjoint
               (PresCheck.src-remove pc)
               (sym-disjoint (remove-linear r))))
  ... | ldtarget
    with mergeRemoveContext r (PresCheck.src-remove pc)
  ... | Gf , msrc , rsrc
    with mergeDisjointContext ldtarget
  ... | Γ₁ , mleft
    with frame-remove
           (merge-frame ldtarget mleft)
  ... | dstr
    with mergeRemoveContext dstr (PresCheck.dst-remove pc)
  ... | Gfdst , mdst , rdst
    with merge-result-unique mdst (merge-extendUsed k msrc)
  ... | eqG = record
    { Gf = Gf
    ; Γ₀′ = PresCheck.Γ₀′ pc
    ; Γ₁ = Γ₁
    ; Γ₁′ = PresCheck.Γ₁′ pc
    ; U = V
    ; src-remove = rsrc
    ; dst-remove =
        subst
          (λ X → RemoveCtx Γ₁ X (PresCheck.Γ₁′ pc))
          eqG
          rdst
    ; ctx-step = PresCheck.ctx-step pc
    ; compat = PresCheck.compat pc
    ; synth =
        T-App
          (replay-synth
            (weaken-val-synth {k = k} dv′)
            (remove-frame dstr)
            (allUsed-frame {Φ = PresCheck.Γ₁ pc} (allUsed-extendUsed k au)))
          (PresCheck.check pc)
    ; subtype = <:ₜ-refl (normalTyOf V)
    }
  preserve⇒ d step lbl ex disj = preserve⇒-hard d step lbl ex disj

  preserve⇐ :
    ∀ {n k pk mult}
      {Γ₀ : Ctx [] n} {Γ₂ : Ctx [] n}
      {Γin Γv : Ctx [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] (k + n)}
      {T : NfTy [] (KV pk mult)} {ℓ : Label n k}
    → Γ₀ ⊢ e₁ ⇐ T ⊣ Γ₂
    → e₁ —[ ℓ ]→ e₂
    → (lbl : ℓ ⦂ Γin ⇒ Γv)
    → Extract Γ₀ ℓ Γin
    → LinearDisjoint Γ₀ Γv
    → PresCheck Γin Γv lbl Γ₀ Γ₂ e₂ T
  preserve⇐ (T-Check d U<:T) step lbl ex disj
    with preserve⇒ d step lbl ex disj
  ... | ps = record
    { Gf = PresSynth.Gf ps
    ; Γ₀′ = PresSynth.Γ₀′ ps
    ; Γ₁ = PresSynth.Γ₁ ps
    ; Γ₁′ = PresSynth.Γ₁′ ps
    ; src-remove = PresSynth.src-remove ps
    ; dst-remove = PresSynth.dst-remove ps
    ; ctx-step = PresSynth.ctx-step ps
    ; compat = PresSynth.compat ps
    ; check = T-Check (PresSynth.synth ps) (<:ₜ-trans (PresSynth.subtype ps) U<:T)
    }
