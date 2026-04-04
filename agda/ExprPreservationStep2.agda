module ExprPreservationStep2 where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

import Duality
open import Kinds
open import Kits
import Types
open import Variance using
  ( Variance
  ; ⊕
  ; ⊝
  ; ⊘
  ; vswap
  ; vcompose
  ; vcompose-sym
  ; vcompose-⊕
  ; vcompose-⊝
  ; vcompose-⊘
  ; vcompose-assoc
  ; vcompose-swap
  ; VarianceCovers
  ; compose-covers
  )
open import Types using (Ty; T-Base; N-Sub; N-End)
open import AlgorithmicSubtyping using (_<:ₜ_; <:ₜ-refl; <:ₜ-trans; <:ₜ-sub; <:ₜ-msg; <:ₚ′-proto; <:ₜ-end)
open import Subtyping using
  ( _<:_
  ; _<<:[_]_
  ; injᵥ
  ; <:-refl
  ; <:-trans
  ; <:-sub
  ; <:-fun
  ; <:-pair
  ; <:-all
  ; <:-msg
  ; <:-proto
  ; <:-minus
  ; <:-dual-lr
  ; <:-up
  ; <:-protoD
  ; <<:-trans
  ; conv⇒subty
  ; norm-pres-sub
  )
open import TypesProtocolConstructors using
  ( ConstructorSignature
  ; ProtocolConstructors
  ; SelectTy1
  ; SelectTy2
  ; SelectConstTy
  ; instantiate
  ; materialize
  ; singletonSubst
  ; UsageVariance
  ; unused
  ; used
  ; usageVariance
  ; allUsageVariance
  ; swapUsage
  ; joinUsage
  ; composeUsage
  )
open import ExprSyntax using (Expr; Value; Const; E-Val; E-LetUnit; E-Pair; E-App; E-TApp; V-Const; V-Var; V-Receive₁; V-Send₁; V-Send₂; V-Send₃; V-Select₁; V-Select₂; C-Receive; C-Send; C-Select; C-Close; C-Fork; C-Unit)
open import ExprSemantics using (Label; Act-App; Act-TApp; Act-LetPair; Act-LetUnit; Act-PairV; Act-Rec; Act-Fork; Act-New; Act-Receive₁; Act-Receive₂; Act-Rcv; Act-Send₁; Act-Send₂; Act-Send₃; Act-Send; Act-Sel; Act-Select₁; Act-Select₂; Act-Close; Act-AppL; Act-AppR; Act-TAppE; Act-PairL; Act-PairR; Act-MatchE; Act-LetPairE; Act-LetUnitE; _—[_]→_)
import ExprSemantics as ES
open import ExprNormalTyping
open import ExprSubstitution using (substTyValue)
open import ExprSubstitutionTyping using
  ( rec-unfold-preserves-value
  ; subst-check-preserves-synth
  ; subst2-preserves-synth
  ; substTy-preserves-value
  ; substTy-normalizeTy
  ; substTy-SelectConstTy
  ; substTy-SelectTy1
  )
import ExprSubstitutionTyping as EST
open import SubstitutionSubtyping using (subst-preserves-≡c; subst-preserves; subst-preserves-<<:)
open import AlgorithmicSound using (sound-algₜ; sound-<<:ₚ)
open import AlgorithmicComplete using (complete-algₜ)
import ExprContextReduction as ECR
open import ExprContextReduction using
  (_—ctx[_]→_; _⦂_⇒_; Compatible; Extract; ctx-step-preserves-disjoint
  ; Ctx-β; Ctx-New; Ctx-Fork; Ctx-Rcv; Ctx-Send; Ctx-Select; Ctx-Close
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
  ; Label-β; Label-Fork; Label-RecvVal; Label-SendVal; Label-SendLab; Label-Close
  ; recvChanNf; sendChanNf; selectInNf; selectOutNf; sessNf
  ; allUsedCtx
  ; Ex-β; Ex-Fork; Ex-New; Ex-RecvVal; Ex-RecvLab; Ex-SendVal; Ex-SendLab; Ex-Close
  ; Compat-β; Compat-New; Compat-Fork; Compat-RecvVal; Compat-SendVal; Compat-Select; Compat-Close
  )
open import ExprTypingProperties using (frame-remove; replay-synth-allUsed; replay-check-allUsed)
open import ExprTypingLeftover using (strip-value; leftover-synth)
open import ExprPreservationStep using
  ( closeTy-shape
  ; close-inversion
  ; fork-shape
  ; new-shape
  ; newInst-shape
  ; sess-normalizeTy
  ; sendTy-shape
  ; receive₂-shape
  ; send₃-shape
  ; send₁-rigid
  ; send₂-rigid
  ; send₁-ty
  ; send₂-ty
  ; send₂-shape
  ; receive₁-rigid
  ; receive₂-rigid
  ; receive₁-ty
  ; receive₂-ty
  ; recv-app-inversion
  ; check-output-unique
  ; merge-value
   ; replace-take
   ; replace-used-output
  ; take-from-membership
  ; take-unique
  ; take-implies-membership
  ; sendChan-subtype
  ; sess-subtype
  ; weaken-synth
  ; arrow-subtype-inversion
  ; substTy-wkCtx-id
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

take-replace-lin :
  ∀ {n K K′}
    {Γ₀ Γ₂ : Ctx [] n}
    {x : Fin n} {T : NfTy [] K} {U : NfTy [] K′}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₂
  → Σ (Ctx [] n) λ Γ₁ → ReplaceAt Γ₀ x (B-Lin U) Γ₁
take-replace-lin {U = U} (take-here {Γ = Γ}) =
  U ∷ˡ Γ , ExprContextReduction.R-here
take-replace-lin {U = U} (take-thereˡ {U = V} take)
  with take-replace-lin {U = U} take
... | Γ₁ , rep = V ∷ˡ Γ₁ , ExprContextReduction.R-there rep
take-replace-lin {U = U} (take-thereᵘ {U = V} take)
  with take-replace-lin {U = U} take
... | Γ₁ , rep = V ∷ᵘ Γ₁ , ExprContextReduction.R-there rep
take-replace-lin {U = U} (take-there✖ take)
  with take-replace-lin {U = U} take
... | Γ₁ , rep = used∷ Γ₁ , ExprContextReduction.R-there rep

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
end-subtype-invert {U = mkNfTy .EndLin (N-Sub _ N-End)} (<:ₜ-sub <:ₜ-end) = refl

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

remove-membership-un :
  ∀ {n K}
    {Γ₀ G Γ₂ : Ctx [] n}
    {x : Fin n} {T : NfTy [] K}
  → RemoveCtx Γ₀ G Γ₂
  → Γ₂ ∋ᵘ x ∶ T
  → Γ₀ ∋ᵘ x ∶ T
remove-membership-un (RM-un r) hereᵘ = hereᵘ
remove-membership-un (RM-drop r) (thereᵘˡ x∈) = thereᵘˡ (remove-membership-un r x∈)
remove-membership-un (RM-lin r) (thereᵘ✖ x∈) = thereᵘˡ (remove-membership-un r x∈)
remove-membership-un (RM-un r) (thereᵘᵘ x∈) = thereᵘᵘ (remove-membership-un r x∈)
remove-membership-un (RM-allused r) (thereᵘ✖ x∈) = thereᵘ✖ (remove-membership-un r x∈)

lin-un-disjoint :
  ∀ {n K K′}
    {Γ : Ctx [] n}
    {x : Fin n} {T : NfTy [] K} {U : NfTy [] K′}
  → Γ ∋ˡ x ∶ T
  → Γ ∋ᵘ x ∶ U
  → ⊥
lin-un-disjoint hereˡ ()
lin-un-disjoint (thereˡˡ x∈) (thereᵘˡ x∈′) = lin-un-disjoint x∈ x∈′
lin-un-disjoint (thereˡᵘ x∈) (thereᵘᵘ x∈′) = lin-un-disjoint x∈ x∈′
lin-un-disjoint (thereˡ✖ x∈) (thereᵘ✖ x∈′) = lin-un-disjoint x∈ x∈′

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

  select₁-pres :
    ∀ {n k}
      {Γ Γ′ : Ctx [] n}
      {v : Variance} {i : Fin k} {P : Ty [] KP}
      {T : NfTy [] (KV KT Lin)}
    → Γ ⊢ E-TApp (E-Val (V-Const (C-Select v i))) P ⇒ T ⊣ Γ′
    → Γ ⊢ᵥ V-Select₁ v i P ⇒ T ⊣ Γ′

  select₂-pres :
    ∀ {n k}
      {Γ Γ′ : Ctx [] n}
      {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin}
      {T : NfTy [] (KV KT Lin)}
    → Γ ⊢ E-TApp (E-Val (V-Select₁ v i P)) S ⇒ T ⊣ Γ′
    → Γ ⊢ᵥ V-Select₂ v i P S ⇒ T ⊣ Γ′

  select-app-subtype :
    ∀ {n k}
      {Γ Γ′ : Ctx [] n}
      {v₁ v₂ : Variance} {i : Fin k}
      {P : Ty [] KP} {S : Ty [] SLin}
      {P′ : NfTy [] KP} {S′ : NfTy [] SLin}
      {A R : NfTy [] TLin}
    → Γ ⊢ᵥ V-Select₂ v₁ i P S ⇒ linArrNf A R ⊣ Γ′
    → normalTyOf (selectInNf v₂ i P′ S′) <:ₜ normalTyOf A
    → normalTyOf (selectOutNf v₂ i P′ S′) <:ₜ normalTyOf R

_≈ₛ_ : ∀ {Δ₁ Δ₂} → (Δ₁ →ₛ Δ₂) → (Δ₁ →ₛ Δ₂) → Set
_≈ₛ_ {Δ₁} ϕ ψ = ∀ K (x : K ∈ Δ₁) → (ϕ K x) Types.≡c (ψ K x)

SubstRelVar :
  ∀ {Δ K Δ′}
  → K ∈ Δ → KP ∈ Δ → Variance
  → Ty Δ′ K → Ty Δ′ K → Set
SubstRelVar (here refl) (here refl) v T U = T <<:[ v ] U
SubstRelVar (here refl) (there q) v T U = T Types.≡c U
SubstRelVar (there x) (here refl) v T U = T Types.≡c U
SubstRelVar (there x) (there p) v T U = SubstRelVar x p v T U

SubstRelates :
  ∀ {Δ₁ Δ₂}
  → (Δ₁ →ₛ Δ₂) → KP ∈ Δ₁ → Variance → (Δ₁ →ₛ Δ₂) → Set
SubstRelates {Δ₁} ϕ p v ψ =
  ∀ K (x : K ∈ Δ₁) → SubstRelVar x p v (ϕ K x) (ψ K x)

SubstRelUnused :
  ∀ {Δ K Δ′}
  → K ∈ Δ → KP ∈ Δ
  → Ty Δ′ K → Ty Δ′ K → Set
SubstRelUnused (here refl) (here refl) T U = ⊤
SubstRelUnused (here refl) (there q) T U = T Types.≡c U
SubstRelUnused (there x) (here refl) T U = T Types.≡c U
SubstRelUnused (there x) (there p) T U = SubstRelUnused x p T U

SubstIgnores :
  ∀ {Δ₁ Δ₂}
  → (Δ₁ →ₛ Δ₂) → KP ∈ Δ₁ → (Δ₁ →ₛ Δ₂) → Set
SubstIgnores {Δ₁} ϕ p ψ =
  ∀ K (x : K ∈ Δ₁) → SubstRelUnused x p (ϕ K x) (ψ K x)

≈ᵥ⇒≈ᵤ :
  ∀ {Δ₁ Δ₂}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
    {p : KP ∈ Δ₁}
    {v : Variance}
  → SubstRelates ϕ p v ψ
  → SubstIgnores ϕ p ψ
≈ᵥ⇒≈ᵤ {p = here refl} rel K (here refl) = tt
≈ᵥ⇒≈ᵤ {p = there q} rel K (here refl) = rel K (here refl)
≈ᵥ⇒≈ᵤ {p = here refl} rel K (there x) = rel K (there x)
≈ᵥ⇒≈ᵤ {p = there p} rel K (there x) = ≈ᵥ⇒≈ᵤ {p = p} (λ K′ y → rel K′ (there y)) K x

lift-≈ₛ :
  ∀ {Δ₁ Δ₂ K} {ϕ ψ : Δ₁ →ₛ Δ₂}
  → ϕ ≈ₛ ψ
  → (ϕ ↑ₛ K) ≈ₛ (ψ ↑ₛ K)
lift-≈ₛ rel K′ (here refl) = Types.≡c-refl
lift-≈ₛ rel K′ (there x) = subst-preserves-≡c (rel K′ x) (weakenᵣ _)

weaken-SubstRelUnused :
  ∀ {Δ K Δ′ K′}
    {x : K ∈ Δ} {p : KP ∈ Δ}
    {T U : Ty Δ′ K}
  → SubstRelUnused x p T U
  → SubstRelUnused x p (T ⋯ weakenᵣ K′) (U ⋯ weakenᵣ K′)
weaken-SubstRelUnused {x = here refl} {p = here refl} rel = tt
weaken-SubstRelUnused {x = here refl} {p = there q} rel =
  subst-preserves-≡c rel (weakenᵣ _)
weaken-SubstRelUnused {x = there x} {p = here refl} rel =
  subst-preserves-≡c rel (weakenᵣ _)
weaken-SubstRelUnused {x = there x} {p = there p} rel =
  weaken-SubstRelUnused {x = x} {p = p} rel

lift-≈ᵤ :
  ∀ {Δ₁ Δ₂ K}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
    {p : KP ∈ Δ₁}
  → SubstIgnores ϕ p ψ
  → SubstIgnores (ϕ ↑ₛ K) (there p) (ψ ↑ₛ K)
lift-≈ᵤ rel K′ (here refl) = Types.≡c-refl
lift-≈ᵤ {p = p} rel K′ (there x) =
  weaken-SubstRelUnused {x = x} {p = p} (rel K′ x)

t-dual-preserves-≡c :
  ∀ {Δ m} {T U : Ty Δ (KV KS m)}
  → T Types.≡c U
  → Types.t-dual Duality.D-S T Types.≡c Types.t-dual Duality.D-S U
t-dual-preserves-≡c Types.≡c-refl = Types.≡c-refl
t-dual-preserves-≡c (Types.≡c-symm eq) =
  Types.≡c-symm (t-dual-preserves-≡c eq)
t-dual-preserves-≡c (Types.≡c-trns eq₁ eq₂) =
  Types.≡c-trns (t-dual-preserves-≡c eq₁) (t-dual-preserves-≡c eq₂)
t-dual-preserves-≡c (Types.≡c-sub (≤k-step ≤p-refl x) eq) =
  Types.≡c-sub (≤k-step ≤p-refl x) (t-dual-preserves-≡c eq)
t-dual-preserves-≡c
  {T = Types.T-Dual Duality.D-S (Types.T-Sub (≤k-step ≤p-refl x) T)}
  Types.≡c-sub-dual = Types.≡c-refl
t-dual-preserves-≡c
  {T = Types.T-Dual Duality.D-S (Types.T-Dual Duality.D-S U)}
  (Types.≡c-dual-dual Duality.D-S) =
  Types.dual-tinv U
t-dual-preserves-≡c Types.≡c-dual-end = Types.≡c-refl
t-dual-preserves-≡c {T = Types.T-Dual Duality.D-S (Types.T-Msg p T S)} Types.≡c-dual-msg
  rewrite Duality.invert-involution {p} =
    Types.≡c-msg Types.≡c-refl Types.≡c-refl
t-dual-preserves-≡c {T = Types.T-Msg p T S} (Types.≡c-msg-minus {p = p}) =
  Types.≡c-msg-minus {p = Duality.invert p}
t-dual-preserves-≡c (Types.≡c-msg eqT eqS) =
  Types.≡c-msg eqT (t-dual-preserves-≡c eqS)
t-dual-preserves-≡c (Types.≡c-fun {≤pk = ≤p-step ()} _ _)

subst-preserves-≡c-pointwise :
  ∀ {Δ₁ Δ₂ K} {ϕ ψ : Δ₁ →ₛ Δ₂} (T : Ty Δ₁ K)
  → ϕ ≈ₛ ψ
  → (T ⋯ ϕ) Types.≡c (T ⋯ ψ)
subst-preserves-≡c-pointwise (Types.T-Var x) rel = rel _ x
subst-preserves-≡c-pointwise T-Base rel = Types.≡c-refl
subst-preserves-≡c-pointwise (Types.T-Arrow ≤pk T U) rel =
  Types.≡c-fun
    (subst-preserves-≡c-pointwise T rel)
    (subst-preserves-≡c-pointwise U rel)
subst-preserves-≡c-pointwise (Types.T-Pair T U) rel =
  Types.≡c-pair
    (subst-preserves-≡c-pointwise T rel)
    (subst-preserves-≡c-pointwise U rel)
subst-preserves-≡c-pointwise (Types.T-Poly K′ T) rel =
  Types.≡c-all (subst-preserves-≡c-pointwise T (lift-≈ₛ rel))
subst-preserves-≡c-pointwise (Types.T-Sub K≤K′ T) rel =
  Types.≡c-sub K≤K′ (subst-preserves-≡c-pointwise T rel)
subst-preserves-≡c-pointwise (Types.T-Dual Duality.D-S T) rel =
  Types.≡c-trns
    (Types.dual-tinv (T ⋯ _))
    (Types.≡c-trns
      (t-dual-preserves-≡c (subst-preserves-≡c-pointwise T rel))
      (Types.≡c-symm (Types.dual-tinv (T ⋯ _))))
subst-preserves-≡c-pointwise Types.T-End rel = Types.≡c-refl
subst-preserves-≡c-pointwise (Types.T-Msg p T S) rel =
  Types.≡c-msg
    (subst-preserves-≡c-pointwise T rel)
    (subst-preserves-≡c-pointwise S rel)
subst-preserves-≡c-pointwise (Types.T-Up T) rel =
  Types.≡c-up (subst-preserves-≡c-pointwise T rel)
subst-preserves-≡c-pointwise (Types.T-Minus T) rel =
  Types.≡c-minus (subst-preserves-≡c-pointwise T rel)
subst-preserves-≡c-pointwise (Types.T-ProtoD T) rel =
  Types.≡c-protoD (subst-preserves-≡c-pointwise T rel)
subst-preserves-≡c-pointwise (Types.T-ProtoP #c v T) rel =
  Types.≡c-protoP (subst-preserves-≡c-pointwise T rel)

singletonSubst-≈ₛ :
  ∀ {Δ} {U V : Ty Δ KP}
  → U Types.≡c V
  → singletonSubst U ≈ₛ singletonSubst V
singletonSubst-≈ₛ eq K (here refl) = eq
singletonSubst-≈ₛ eq K (there ()) 

singletonSubst-≈ᵤ :
  ∀ {Δ}
    {U V : Ty Δ KP}
  → SubstIgnores (singletonSubst U) (here refl) (singletonSubst V)
singletonSubst-≈ᵤ K (here refl) = tt
singletonSubst-≈ᵤ K (there ())

singletonSubst-≈ᵥ :
  ∀ {Δ}
    {U V : Ty Δ KP}
    {v : Variance}
  → U <<:[ v ] V
  → SubstRelates (singletonSubst U) (here refl) v (singletonSubst V)
singletonSubst-≈ᵥ rel K (here refl) = rel
singletonSubst-≈ᵥ rel K (there ())

conv⇒<<: :
  ∀ {Δ K} {T₁ T₂ : Ty Δ K} {v : Variance}
  → T₁ Types.≡c T₂
  → T₁ <<:[ v ] T₂
conv⇒<<: {v = ⊕} eq = proj₁ (conv⇒subty _ _ eq)
conv⇒<<: {v = ⊝} eq = proj₂ (conv⇒subty _ _ eq)
conv⇒<<: {v = ⊘} eq = eq

swap-<<: :
  ∀ {Δ K} {T₁ T₂ : Ty Δ K} {v : Variance}
  → T₁ <<:[ v ] T₂
  → T₂ <<:[ vswap v ] T₁
swap-<<: {v = ⊕} rel = rel
swap-<<: {v = ⊝} rel = rel
swap-<<: {v = ⊘} rel = Types.≡c-symm rel

swap-SubstRelVar :
  ∀ {Δ K Δ′}
    {x : K ∈ Δ} {p : KP ∈ Δ}
    {v : Variance}
    {T U : Ty Δ′ K}
  → SubstRelVar x p v T U
  → SubstRelVar x p (vswap v) U T
swap-SubstRelVar {x = here refl} {p = here refl} rel =
  swap-<<: rel
swap-SubstRelVar {x = here refl} {p = there q} rel =
  Types.≡c-symm rel
swap-SubstRelVar {x = there x} {p = here refl} rel =
  Types.≡c-symm rel
swap-SubstRelVar {x = there x} {p = there p} rel =
  swap-SubstRelVar {x = x} {p = p} rel

swap-≈ᵥ :
  ∀ {Δ₁ Δ₂}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
    {p : KP ∈ Δ₁}
    {v : Variance}
  → SubstRelates ϕ p v ψ
  → SubstRelates ψ p (vswap v) ϕ
swap-≈ᵥ {p = p} rel K x = swap-SubstRelVar {x = x} {p = p} (rel K x)

coerce-<<: :
  ∀ {Δ K}
    {T₁ T₂ : Ty Δ K}
    {v₁ v₂ : Variance}
  → T₁ <<:[ v₁ ] T₂
  → VarianceCovers v₁ v₂
  → T₁ <<:[ v₂ ] T₂
coerce-<<: {v₁ = ⊕} {⊕} rel cov = rel
coerce-<<: {v₁ = ⊝} {⊝} rel cov = rel
coerce-<<: {v₁ = ⊘} {⊕} rel cov = conv⇒<<: {v = ⊕} rel
coerce-<<: {v₁ = ⊘} {⊝} rel cov = conv⇒<<: {v = ⊝} rel
coerce-<<: {v₁ = ⊘} {⊘} rel cov = rel

coerce-SubstRelVar :
  ∀ {Δ K Δ′}
    {x : K ∈ Δ} {p : KP ∈ Δ}
    {v₁ v₂ : Variance}
    {T U : Ty Δ′ K}
  → SubstRelVar x p v₁ T U
  → VarianceCovers v₁ v₂
  → SubstRelVar x p v₂ T U
coerce-SubstRelVar {x = here refl} {p = here refl} rel cov =
  coerce-<<: rel cov
coerce-SubstRelVar {x = here refl} {p = there q} rel cov = rel
coerce-SubstRelVar {x = there x} {p = here refl} rel cov = rel
coerce-SubstRelVar {x = there x} {p = there p} rel cov =
  coerce-SubstRelVar {x = x} {p = p} rel cov

coerce-≈ᵥ :
  ∀ {Δ₁ Δ₂}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
    {p : KP ∈ Δ₁}
    {v₁ v₂ : Variance}
  → (∀ K (x : K ∈ Δ₁) → SubstRelVar x p v₁ (ϕ K x) (ψ K x))
  → VarianceCovers v₁ v₂
  → (∀ K (x : K ∈ Δ₁) → SubstRelVar x p v₂ (ϕ K x) (ψ K x))
coerce-≈ᵥ {p = p} rel cov K x = coerce-SubstRelVar {x = x} {p = p} (rel K x) cov

weaken-SubstRelVar :
  ∀ {Δ K Δ′ K′}
    {x : K ∈ Δ} {p : KP ∈ Δ}
    {v : Variance}
    {T U : Ty Δ′ K}
  → SubstRelVar x p v T U
  → SubstRelVar x p v (T ⋯ weakenᵣ K′) (U ⋯ weakenᵣ K′)
weaken-SubstRelVar {x = here refl} {p = here refl} rel =
  subst-preserves-<<: rel (weakenᵣ _)
weaken-SubstRelVar {x = here refl} {p = there q} rel =
  subst-preserves-≡c rel (weakenᵣ _)
weaken-SubstRelVar {x = there x} {p = here refl} rel =
  subst-preserves-≡c rel (weakenᵣ _)
weaken-SubstRelVar {x = there x} {p = there p} rel =
  weaken-SubstRelVar {x = x} {p = p} rel

lift-≈ᵥ :
  ∀ {Δ₁ Δ₂ K}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
    {p : KP ∈ Δ₁}
    {v : Variance}
  → (∀ K′ (x : K′ ∈ Δ₁) → SubstRelVar x p v (ϕ K′ x) (ψ K′ x))
  → (∀ K′ (x : K′ ∈ (K ∷ Δ₁)) →
        SubstRelVar x (there p) v ((ϕ ↑ₛ K) K′ x) ((ψ ↑ₛ K) K′ x))
lift-≈ᵥ rel K′ (here refl) = Types.≡c-refl
lift-≈ᵥ {p = p} rel K′ (there x) = weaken-SubstRelVar {x = x} {p = p} (rel K′ x)

sub-<<: :
  ∀ {Δ pk pk′ m m′}
    {K≤K′ : KV pk m ≤k KV pk′ m′}
    {T₁ T₂ : Ty Δ (KV pk m)}
    {v : Variance}
  → T₁ <<:[ v ] T₂
  → Types.T-Sub K≤K′ T₁ <<:[ v ] Types.T-Sub K≤K′ T₂
sub-<<: {K≤K′ = K≤K′} {v = ⊕} rel = <:-sub K≤K′ rel
sub-<<: {K≤K′ = K≤K′} {v = ⊝} rel = <:-sub K≤K′ rel
sub-<<: {v = ⊘} rel = Types.≡c-sub _ rel

fun-<<: :
  ∀ {Δ pk m}
    {≤pk : KM ≤p pk}
    {T₁ T₂ : Ty Δ _} {U₁ U₂ : Ty Δ _}
    {v : Variance}
  → T₁ <<:[ vswap v ] T₂
  → U₁ <<:[ v ] U₂
  → Types.T-Arrow {m = m} ≤pk T₁ U₁ <<:[ v ] Types.T-Arrow ≤pk T₂ U₂
fun-<<: {v = ⊕} dom cod = <:-fun dom cod
fun-<<: {v = ⊝} dom cod = <:-fun dom cod
fun-<<: {v = ⊘} dom cod = Types.≡c-fun dom cod

pair-<<: :
  ∀ {Δ pk₁ pk₂ m}
    {T₁ T₂ : Ty Δ (KV pk₁ m)}
    {U₁ U₂ : Ty Δ (KV pk₂ m)}
    {v : Variance}
  → T₁ <<:[ v ] T₂
  → U₁ <<:[ v ] U₂
  → Types.T-Pair T₁ U₁ <<:[ v ] Types.T-Pair T₂ U₂
pair-<<: {v = ⊕} relT relU = <:-pair relT relU
pair-<<: {v = ⊝} relT relU = <:-pair relT relU
pair-<<: {v = ⊘} relT relU = Types.≡c-pair relT relU

all-<<: :
  ∀ {Δ K′ m}
    {T₁ T₂ : Ty (K′ ∷ Δ) (KV KT m)}
    {v : Variance}
  → T₁ <<:[ v ] T₂
  → Types.T-Poly K′ T₁ <<:[ v ] Types.T-Poly K′ T₂
all-<<: {v = ⊕} rel = <:-all rel
all-<<: {v = ⊝} rel = <:-all rel
all-<<: {v = ⊘} rel = Types.≡c-all rel

dual-<<: :
  ∀ {Δ m}
    {T₁ T₂ : Ty Δ (KV KS m)}
    {v : Variance}
  → T₁ <<:[ vswap v ] T₂
  → Types.T-Dual Duality.D-S T₁ <<:[ v ] Types.T-Dual Duality.D-S T₂
dual-<<: {v = ⊕} rel = <:-dual-lr Duality.D-S rel
dual-<<: {v = ⊝} rel = <:-dual-lr Duality.D-S rel
dual-<<: {T₁ = T₁} {T₂ = T₂} {v = ⊘} rel =
  Types.≡c-trns
    (Types.dual-tinv T₁)
    (Types.≡c-trns
      (t-dual-preserves-≡c rel)
      (Types.≡c-symm (Types.dual-tinv T₂)))

up-<<: :
  ∀ {Δ pk m}
    {T₁ T₂ : Ty Δ (KV pk m)}
    {v : Variance}
  → T₁ <<:[ v ] T₂
  → Types.T-Up T₁ <<:[ v ] Types.T-Up T₂
up-<<: {v = ⊕} rel = <:-up rel
up-<<: {v = ⊝} rel = <:-up rel
up-<<: {v = ⊘} rel = Types.≡c-up rel

minus-<<: :
  ∀ {Δ}
    {T₁ T₂ : Ty Δ KP}
    {v : Variance}
  → T₁ <<:[ vswap v ] T₂
  → Types.T-Minus T₁ <<:[ v ] Types.T-Minus T₂
minus-<<: {v = ⊕} rel = <:-minus rel
minus-<<: {v = ⊝} rel = <:-minus rel
minus-<<: {v = ⊘} rel = Types.≡c-minus rel

protoD-<<: :
  ∀ {Δ}
    {T₁ T₂ : Ty Δ TLin}
    {v : Variance}
  → T₁ <<:[ v ] T₂
  → Types.T-ProtoD T₁ <<:[ v ] Types.T-ProtoD T₂
protoD-<<: {v = ⊕} rel = <:-protoD rel
protoD-<<: {v = ⊝} rel = <:-protoD rel
protoD-<<: {v = ⊘} rel = Types.≡c-protoD rel

protoP-<<: :
  ∀ {Δ k}
    {#c : Subset.Subset k}
    {v₁ v₂ : Variance}
    {T₁ T₂ : Ty Δ KP}
  → T₁ <<:[ vcompose v₁ v₂ ] T₂
  → Types.T-ProtoP #c v₁ T₁ <<:[ v₂ ] Types.T-ProtoP #c v₁ T₂
protoP-<<: {v₁ = ⊕} {v₂ = ⊕} rel = <:-proto (λ {x} z → z) rel
protoP-<<: {v₁ = ⊝} {v₂ = ⊕} rel = <:-proto (λ {x} z → z) rel
protoP-<<: {v₁ = ⊘} {v₂ = ⊕} rel = <:-proto (λ {x} z → z) (conv⇒<<: rel)
protoP-<<: {v₁ = ⊕} {v₂ = ⊝} rel = <:-proto (λ {x} z → z) rel
protoP-<<: {v₁ = ⊝} {v₂ = ⊝} rel = <:-proto (λ {x} z → z) (swap-<<: {v = ⊕} rel)
protoP-<<: {v₁ = ⊘} {v₂ = ⊝} rel = <:-proto (λ {x} z → z) (Types.≡c-symm rel)
protoP-<<: {v₁ = ⊕} {v₂ = ⊘} rel = Types.≡c-protoP rel
protoP-<<: {v₁ = ⊝} {v₂ = ⊘} rel = Types.≡c-protoP rel
protoP-<<: {v₁ = ⊘} {v₂ = ⊘} rel = Types.≡c-protoP rel

msg-<<: :
  ∀ {Δ}
    {p : Duality.Polarity}
    {T₁ T₂ : Ty Δ KP}
    {S₁ S₂ : Ty Δ SLin}
    {v : Variance}
  → T₁ <<:[ vcompose (injᵥ p) v ] T₂
  → S₁ <<:[ v ] S₂
  → Types.T-Msg p T₁ S₁ <<:[ v ] Types.T-Msg p T₂ S₂
msg-<<: {p = Duality.⊕} {v = ⊕} relT relS = <:-msg relT relS
msg-<<: {p = Duality.⊕} {v = ⊝} relT relS = <:-msg (swap-<<: {v = ⊕} relT) relS
msg-<<: {p = Duality.⊕} {v = ⊘} relT relS = Types.≡c-msg relT relS
msg-<<: {p = Duality.⊝} {v = ⊕} relT relS = <:-msg relT relS
msg-<<: {p = Duality.⊝} {v = ⊝} relT relS = <:-msg relT relS
msg-<<: {p = Duality.⊝} {v = ⊘} relT relS = Types.≡c-msg relT relS

join-left-covers :
  ∀ {u₁ u u₂}
  → joinUsage (used u₁) u₂ ≡ used u
  → VarianceCovers u u₁
join-left-covers {u₁ = ⊕} {u = ⊕} {u₂ = unused} refl = tt
join-left-covers {u₁ = ⊕} {u = ⊕} {u₂ = used ⊕} refl = tt
join-left-covers {u₁ = ⊕} {u = ⊘} {u₂ = used ⊝} refl = tt
join-left-covers {u₁ = ⊕} {u = ⊘} {u₂ = used ⊘} refl = tt
join-left-covers {u₁ = ⊝} {u = ⊝} {u₂ = unused} refl = tt
join-left-covers {u₁ = ⊝} {u = ⊘} {u₂ = used ⊕} refl = tt
join-left-covers {u₁ = ⊝} {u = ⊝} {u₂ = used ⊝} refl = tt
join-left-covers {u₁ = ⊝} {u = ⊘} {u₂ = used ⊘} refl = tt
join-left-covers {u₁ = ⊘} {u = ⊘} {u₂ = unused} refl = tt
join-left-covers {u₁ = ⊘} {u = ⊘} {u₂ = used ⊕} refl = tt
join-left-covers {u₁ = ⊘} {u = ⊘} {u₂ = used ⊝} refl = tt
join-left-covers {u₁ = ⊘} {u = ⊘} {u₂ = used ⊘} refl = tt

join-right-covers :
  ∀ {u₂ u u₁}
  → joinUsage u₁ (used u₂) ≡ used u
  → VarianceCovers u u₂
join-right-covers {u₂ = ⊕} {u = ⊕} {u₁ = unused} refl = tt
join-right-covers {u₂ = ⊕} {u = ⊕} {u₁ = used ⊕} refl = tt
join-right-covers {u₂ = ⊕} {u = ⊘} {u₁ = used ⊝} refl = tt
join-right-covers {u₂ = ⊕} {u = ⊘} {u₁ = used ⊘} refl = tt
join-right-covers {u₂ = ⊝} {u = ⊝} {u₁ = unused} refl = tt
join-right-covers {u₂ = ⊝} {u = ⊘} {u₁ = used ⊕} refl = tt
join-right-covers {u₂ = ⊝} {u = ⊝} {u₁ = used ⊝} refl = tt
join-right-covers {u₂ = ⊝} {u = ⊘} {u₁ = used ⊘} refl = tt
join-right-covers {u₂ = ⊘} {u = ⊘} {u₁ = unused} refl = tt
join-right-covers {u₂ = ⊘} {u = ⊘} {u₁ = used ⊕} refl = tt
join-right-covers {u₂ = ⊘} {u = ⊘} {u₁ = used ⊝} refl = tt
join-right-covers {u₂ = ⊘} {u = ⊘} {u₁ = used ⊘} refl = tt

unused≢used : ∀ {u} → unused ≡ used u → ⊥
unused≢used ()

used≢unused : ∀ {u} → used u ≡ unused → ⊥
used≢unused ()

instantiate-normalized-raw :
  ∀ {K} {p : Duality.Polarity}
    (T : Ty (KP ∷ []) K)
    {P : Ty [] KP}
  → instantiate ⦃ Kₛ ⦄ p T ⌞ normalizeTy P ⌟
      Types.≡c instantiate ⦃ Kₛ ⦄ p T P
instantiate-normalized-raw T {P} =
  subst-preserves-≡c-pointwise
    {ϕ = singletonSubst (Types.nf Duality.⊕ Duality.d?⊥ P)}
    {ψ = singletonSubst P}
    T
    (singletonSubst-≈ₛ (Types.nf-sound+ P))

materializeList-normalized-raw :
  (Ts : List (Ty (KP ∷ []) KP))
  {P : Ty [] KP} {S : Ty [] SLin}
  → TypesProtocolConstructors.materializeList Ts Duality.⊕ ⌞ normalizeTy P ⌟ ⌞ normalizeTy S ⌟
      Types.≡c TypesProtocolConstructors.materializeList Ts Duality.⊕ P S
materializeList-normalized-raw [] {S = S} = Types.nf-sound+ S
materializeList-normalized-raw (T ∷ Ts) {P} {S} =
  Types.≡c-msg
    (instantiate-normalized-raw {p = Duality.⊕} T {P = P})
    (materializeList-normalized-raw Ts {P} {S})

materialize-normalized-raw :
  ∀ {v}
    (sig : ConstructorSignature v)
    {P : Ty [] KP} {S : Ty [] SLin}
  → materialize sig Duality.⊕ ⌞ normalizeTy P ⌟ ⌞ normalizeTy S ⌟
      Types.≡c materialize sig Duality.⊕ P S
materialize-normalized-raw (Ts , uv) {P} {S} =
  materializeList-normalized-raw Ts {P} {S}

select₂-inversion :
  ∀ {n k}
    {Γ Γ′ : Ctx [] n}
    {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin}
    {W : NfTy [] TLin}
  → Γ ⊢ᵥ V-Select₂ v i P S ⇒ W ⊣ Γ′
  → (Γ ≡ Γ′) × (W ≡ normalizeTy (SelectTy2 v i P S))
select₂-inversion TV-Select₂ = refl , refl

selectTy2-shape :
  ∀ {k} {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin}
  → normalizeTy (SelectTy2 v i P S)
    ≡ linArrNf
        (selectInNf v i (normalizeTy P) (normalizeTy S))
        (selectOutNf v i (normalizeTy P) (normalizeTy S))
selectTy2-shape {k} {v} {i} {P} {S} =
  nfTyEq
    (cong₂ (Types.T-Arrow (≤p-step <p-mt))
      (cong ⌞_⌟ inputEq)
      (cong ⌞_⌟ outputEq))
    _
    _
  where
  inputRaw : Ty [] SLin
  inputRaw = Types.T-Msg Duality.⊕ (Types.T-ProtoP (Subset.⁅ i ⁆) v P) S

  inputNorm : Ty [] SLin
  inputNorm = Types.T-Msg Duality.⊕ (Types.T-ProtoP (Subset.⁅ i ⁆) v ⌞ normalizeTy P ⌟) ⌞ normalizeTy S ⌟

  inputInnerEq : normalizeTy inputRaw ≡ normalizeTy inputNorm
  inputInnerEq =
    sym
      (nfEq
        (Types.nf-complete
          Duality.d?⊥
          Duality.d?⊥
          (Types.≡c-msg
            (Types.≡c-protoP (Types.nf-sound+ P))
            (Types.nf-sound+ S)))
        _
        _)

  inputEq :
    normalizeTy (SessLin inputRaw)
      ≡ selectInNf v i (normalizeTy P) (normalizeTy S)
  inputEq =
    trans
      (sess-normalizeTy {S = inputRaw})
      (cong sessNf inputInnerEq)

  outputRaw : Ty [] SLin
  outputRaw = materialize ((ProtocolConstructors k v) i) Duality.⊕ P S

  outputNorm : Ty [] SLin
  outputNorm = materialize ((ProtocolConstructors k v) i) Duality.⊕ ⌞ normalizeTy P ⌟ ⌞ normalizeTy S ⌟

  outputInnerEq : normalizeTy outputRaw ≡ normalizeTy outputNorm
  outputInnerEq =
    sym
      (nfEq
        (Types.nf-complete
          Duality.d?⊥
          Duality.d?⊥
          (materialize-normalized-raw ((ProtocolConstructors k v) i) {P} {S}))
        _
        _)

  outputEq :
    normalizeTy (SessLin outputRaw)
      ≡ selectOutNf v i (normalizeTy P) (normalizeTy S)
  outputEq =
    trans
      (sess-normalizeTy {S = outputRaw})
      (cong sessNf outputInnerEq)

select₂-shape :
  ∀ {n k}
    {Γ Γ′ : Ctx [] n}
    {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin}
    {A R : NfTy [] TLin}
  → Γ ⊢ᵥ V-Select₂ v i P S ⇒ linArrNf A R ⊣ Γ′
  → Γ ≡ Γ′
    × (A ≡ selectInNf v i (normalizeTy P) (normalizeTy S))
    × (R ≡ selectOutNf v i (normalizeTy P) (normalizeTy S))
select₂-shape {v = v} {i = i} {P = P} {S = S} vr
  with select₂-inversion vr
... | refl , eqSelect
  with linArrNf-injective (trans eqSelect (selectTy2-shape {v = v} {i = i} {P = P} {S = S}))
... | eqA , eqR = refl , eqA , eqR

selectIn-subtype :
  ∀ {k}
    {v₁ v₂ : Variance} {i : Fin k}
    {P₁ P₂ : NfTy [] KP}
    {S₁ S₂ : NfTy [] SLin}
  → normalTyOf (selectInNf v₁ i P₁ S₁) <:ₜ normalTyOf (selectInNf v₂ i P₂ S₂)
  → (v₁ ≡ v₂)
    × (⌞ P₂ ⌟ <<:[ v₁ ] ⌞ P₁ ⌟)
    × (⌞ S₁ ⌟ <: ⌞ S₂ ⌟)
selectIn-subtype
  {v₁ = v₁}
  {P₁ = mkNfTy P₁ NP₁} {P₂ = mkNfTy P₂ NP₂}
  {S₁ = mkNfTy S₁ NS₁} {S₂ = mkNfTy S₂ NS₂}
  (<:ₜ-sub (<:ₜ-msg (<:ₚ′-proto ss paramRel) Ssub)) =
  refl , pRel , sRel
  where
  pRel₀ : Types.nf Duality.⊕ Duality.d?⊥ P₂ <<:[ v₁ ] Types.nf Duality.⊕ Duality.d?⊥ P₁
  pRel₀ = sound-<<:ₚ paramRel

  pRel₁ : P₂ <<:[ v₁ ] Types.nf Duality.⊕ Duality.d?⊥ P₁
  pRel₁ =
    subst
      (λ X → X <<:[ v₁ ] Types.nf Duality.⊕ Duality.d?⊥ P₁)
      (Types.nfp-idempotent NP₂)
      pRel₀

  pRel : P₂ <<:[ v₁ ] P₁
  pRel =
    subst
      (λ Y → P₂ <<:[ v₁ ] Y)
      (Types.nfp-idempotent NP₁)
      pRel₁

  sRel₀ : Types.nf Duality.⊕ Duality.d?⊥ S₁ <: Types.nf Duality.⊕ Duality.d?⊥ S₂
  sRel₀ = sound-algₜ Ssub

  sRel₁ : S₁ <: Types.nf Duality.⊕ Duality.d?⊥ S₂
  sRel₁ =
    subst
      (λ X → X <: Types.nf Duality.⊕ Duality.d?⊥ S₂)
      (Types.nf-idempotent NS₁)
      sRel₀

  sRel : S₁ <: S₂
  sRel =
    subst
      (λ Y → S₁ <: Y)
      (Types.nf-idempotent NS₂)
      sRel₁

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
basePres-proof {Γ₀ = Γ₀} step lbl ex compat synth sub = record
  { Gf = allUsedCtx Γ₀
  ; Γ₀′ = Γ₀
  ; Γ₁ = Γ₀
  ; Γ₁′ = Γ₀
  ; U = _
  ; src-remove = remove-usedCtx Γ₀
  ; dst-remove = remove-usedCtx Γ₀
  ; ctx-step = step
  ; compat = compat
  ; synth = synth
  ; subtype = sub
  }

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

send-compatible :
  ∀ {n}
    {Γ₀ Γin Γx Γ₁ Γv Γv′ : Ctx [] n}
    {x : Fin n} {T : NfTy [] TLin} {S : NfTy [] SLin} {v : Value [] n}
    {take : Γin ⊢ˡ x ∶ sendChanNf T S ⊣ Γv}
    {rm : RemoveCtx Γ₀ Γv Γx}
    {dv : Γv ⊢ᵥ v ⇒ T ⊣ Γv′}
    {au : AllUsed Γv′}
    {x∈ : Γx ∋ˡ x ∶ sendChanNf T S}
    {rep : ReplaceAt Γx x (B-Lin (sessNf S)) Γ₁}
  → Extract Γ₀ (ExprSemantics.L-SendVal x v) Γin
  → Compatible (Ctx-Send rm dv au x∈ rep) (Label-SendVal take dv au)
send-compatible _ = Compat-SendVal

send-remove-membership :
  ∀ {n}
    {Γ₀ Γin Γr Γv : Ctx [] n}
    {x : Fin n} {T : NfTy [] TLin} {S : NfTy [] SLin}
  → RemoveCtx Γ₀ Γin Γr
  → Γin ⊢ˡ x ∶ sendChanNf T S ⊣ Γv
  → Σ (Ctx [] n) λ Γx →
      RemoveCtx Γ₀ Γv Γx × (Γx ∋ˡ x ∶ sendChanNf T S)
send-remove-membership (RM-lin r) take-here =
  _ , RM-drop r , hereˡ
send-remove-membership (RM-lin r) (take-thereˡ take)
  with send-remove-membership r take
... | Γx , rm , x∈ =
  used∷ Γx , RM-lin rm , thereˡ✖ x∈
send-remove-membership (RM-un r) (take-thereᵘ take)
  with send-remove-membership r take
... | Γx , rm , x∈ =
  _ ∷ᵘ Γx , RM-un rm , thereˡᵘ x∈
send-remove-membership (RM-allused r) (take-there✖ take)
  with send-remove-membership r take
... | Γx , rm , x∈ =
  used∷ Γx , RM-allused rm , thereˡ✖ x∈
send-remove-membership (RM-drop r) (take-there✖ take)
  with send-remove-membership r take
... | Γx , rm , x∈ =
  _ ∷ˡ Γx , RM-drop rm , thereˡˡ x∈

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
remove-extract r ld (Ex-SendVal rin take dv au) with remove-preserves-remove r rin ld
... | Γr′ , rin′ = Ex-SendVal rin′ take dv au
remove-extract r ld (Ex-SendLab {v = v} {P = P} {S = S} rin take) with remove-preserves-remove r rin ld
... | Γr′ , rin′ = Ex-SendLab {v = v} {P = P} {S = S} rin′ take
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

send-input-disjoint-core :
  ∀ {n K}
    {Γ₀ Γ₂ Γin Γr Γv G : Ctx [] n}
    {x : Fin n}
    {T : NfTy [] TLin} {S : NfTy [] SLin}
    {U : NfTy [] K}
  → RemoveCtx Γ₀ G Γ₂
  → RemoveCtx Γ₀ Γin Γr
  → Γin ⊢ˡ x ∶ sendChanNf T S ⊣ Γv
  → Γ₂ ∋ˡ x ∶ U
  → LinearDisjoint G Γv
  → LinearDisjoint G Γin
send-input-disjoint-core {x = fzero}
  (RM-drop r)
  (RM-lin rin)
  take-here
  hereˡ
  (LD-used-used ldv) =
  LD-used-live ldv
send-input-disjoint-core {x = fsuc x}
  (RM-drop r)
  (RM-lin rin)
  (take-thereˡ take)
  (thereˡˡ x∈)
  (LD-used-live ldv) =
  LD-used-live (send-input-disjoint-core {x = x} r rin take x∈ ldv)
send-input-disjoint-core {x = fsuc x}
  (RM-un r)
  (RM-un rin)
  (take-thereᵘ take)
  (thereˡᵘ x∈)
  (LD-un-un ldv) =
  LD-un-un (send-input-disjoint-core {x = x} r rin take x∈ ldv)
send-input-disjoint-core {x = fsuc x}
  (RM-drop r)
  (RM-drop rin)
  (take-there✖ take)
  (thereˡˡ x∈)
  (LD-used-used ldv) =
  LD-used-used (send-input-disjoint-core {x = x} r rin take x∈ ldv)
send-input-disjoint-core {x = fsuc x}
  (RM-lin r)
  (RM-drop rin)
  (take-there✖ take)
  (thereˡ✖ x∈)
  (LD-live-used ldv) =
  LD-live-used (send-input-disjoint-core {x = x} r rin take x∈ ldv)
send-input-disjoint-core {x = fsuc x}
  (RM-allused r)
  (RM-allused rin)
  (take-there✖ take)
  (thereˡ✖ x∈)
  (LD-used-used ldv) =
  LD-used-used (send-input-disjoint-core {x = x} r rin take x∈ ldv)

send-extract-disjoint :
  ∀ {n K}
    {Γ₀ Γ₂ Γin Γv G : Ctx [] n}
    {x : Fin n} {w : Value [] n}
    {U : NfTy [] K}
  → RemoveCtx Γ₀ G Γ₂
  → LinearDisjoint Γ₀ Γv
  → ExprSemantics.L-SendVal x w ⦂ Γin ⇒ Γv
  → Extract Γ₀ (ExprSemantics.L-SendVal x w) Γin
  → Γ₂ ∋ˡ x ∶ U
  → LinearDisjoint G Γin
send-extract-disjoint
  r disj
  (Label-SendVal take dv au)
  (Ex-SendVal rin _ _ _)
  x∈ =
  send-input-disjoint-core r rin take x∈ (remove-removed-disjoint r disj)

basePres step lbl ex compat synth sub =
  basePres-proof step lbl ex compat synth sub

mutual

  recv-live-synth-removed :
    ∀ {n pk mult}
      {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {v : Value [] n}
      {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇒ T ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-RecvVal x v ]→ e₂
    → Extract Γ₀ (ExprSemantics.L-RecvVal x v) Γin
    → Σ Kind λ K → Σ (NfTy [] K) λ U → Γ₂ ∋ˡ x ∶ U

  recv-live-synth-removed r
    (T-App (T-Val vr) (T-Check (T-Val vv) sub))
    (Act-Rcv {x = x} {v = v})
    (Ex-RecvVal rin take au)
    with receive₂-shape vr
  ... | refl , _
    with extract-membership rin (take-implies-membership take)
  ... | x∈₀
    with vv
  ... | TV-Var-Lin {K = K} {T = U} take₂ =
      K , U , take-implies-membership take₂
  ... | TV-Var-Un x∈ᵘ = ⊥-elim (lin-un-disjoint x∈₀ (remove-membership-un r x∈ᵘ))

  recv-live-synth-removed r
    (T-App d₁ d₂)
    (Act-AppL step)
    ex =
    recv-live-synth-removed r d₁ step ex

  recv-live-synth-removed r
    (T-App (T-Val dv) d₂)
    (Act-AppR step)
    ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with recv-live-check-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈

  recv-live-synth-removed r
    (T-TApp d)
    (Act-TAppE step)
    ex =
    recv-live-synth-removed r d step ex

  recv-live-synth-removed r
    (T-Pair d₁ d₂)
    (Act-PairL step)
    ex =
    recv-live-synth-removed r d₁ step ex

  recv-live-synth-removed r
    (T-Pair (T-Val dv) d₂)
    (Act-PairR step)
    ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with recv-live-synth-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈

  recv-live-synth-removed r
    (T-Match d mb bs bj)
    (Act-MatchE step)
    ex =
    recv-live-synth-removed r d step ex

  recv-live-synth-removed r
    (T-LetPair d body)
    (Act-LetPairE step)
    ex =
    recv-live-synth-removed r d step ex

  recv-live-synth-removed r
    (T-LetUnit d₁ d₂)
    (Act-LetUnitE step)
    ex =
    recv-live-check-removed r d₁ step ex

  recv-live-check-removed :
    ∀ {n pk mult}
      {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {v : Value [] n}
      {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇐ T ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-RecvVal x v ]→ e₂
    → Extract Γ₀ (ExprSemantics.L-RecvVal x v) Γin
    → Σ Kind λ K → Σ (NfTy [] K) λ U → Γ₂ ∋ˡ x ∶ U

  recv-live-check-removed r (T-Check d sub) step ex =
    recv-live-synth-removed r d step ex

  send-live-synth-removed :
    ∀ {n pk mult}
      {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {w : Value [] n}
      {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇒ T ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-SendVal x w ]→ e₂
    → Extract Γ₀ (ExprSemantics.L-SendVal x w) Γin
    → Σ Kind λ K → Σ (NfTy [] K) λ U → Γ₂ ∋ˡ x ∶ U

  send-live-synth-removed r
    (T-App (T-Val vr) (T-Check (T-Val vv) sub))
    (Act-Send {T = Tᵣ} {S = Sᵣ})
    ex@(Ex-SendVal rin take dv au)
    with extract-membership rin (take-implies-membership take)
  ... | x∈₀
    with strip-value vr
  ... | Gv , Gv′ , rv , vr′ , auv
    with vv
  ... | TV-Var-Lin {K = K} {T = U} take₂ =
      K , U , remove-membership rv (take-implies-membership take₂)
  ... | TV-Var-Un x∈ᵘ =
      ⊥-elim
        (lin-un-disjoint x∈₀
          (remove-membership-un r (remove-membership-un rv x∈ᵘ)))

  send-live-synth-removed r
    (T-App d₁ d₂)
    (Act-AppL step)
    ex =
    send-live-synth-removed r d₁ step ex

  send-live-synth-removed r
    (T-App (T-Val dv) d₂)
    (Act-AppR step)
    ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with send-live-check-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈

  send-live-synth-removed r
    (T-TApp d)
    (Act-TAppE step)
    ex =
    send-live-synth-removed r d step ex

  send-live-synth-removed r
    (T-Pair d₁ d₂)
    (Act-PairL step)
    ex =
    send-live-synth-removed r d₁ step ex

  send-live-synth-removed r
    (T-Pair (T-Val dv) d₂)
    (Act-PairR step)
    ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with send-live-synth-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈

  send-live-synth-removed r
    (T-Match d mb bs bj)
    (Act-MatchE step)
    ex =
    send-live-synth-removed r d step ex

  send-live-synth-removed r
    (T-LetPair d body)
    (Act-LetPairE step)
    ex =
    send-live-synth-removed r d step ex

  send-live-synth-removed r
    (T-LetUnit d₁ d₂)
    (Act-LetUnitE step)
    ex =
    send-live-check-removed r d₁ step ex

  send-live-check-removed :
    ∀ {n pk mult}
      {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {w : Value [] n}
      {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇐ T ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-SendVal x w ]→ e₂
    → Extract Γ₀ (ExprSemantics.L-SendVal x w) Γin
    → Σ Kind λ K → Σ (NfTy [] K) λ U → Γ₂ ∋ˡ x ∶ U

  send-live-check-removed r (T-Check d sub) step ex =
    send-live-synth-removed r d step ex

  select-live-synth-removed :
    ∀ {n k pk mult}
      {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {i : Fin k}
      {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇒ T ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-SendLab {k = k} x i ]→ e₂
    → Extract Γ₀ (ExprSemantics.L-SendLab {k = k} x i) Γin
    → Σ Kind λ K → Σ (NfTy [] K) λ U → Γ₂ ∋ˡ x ∶ U

  select-live-synth-removed r
    (T-App (T-Val vr) (T-Check (T-Val vv) sub))
    (Act-Sel {x = x})
    (Ex-SendLab rin take)
    with extract-membership rin (take-implies-membership take)
  ... | x∈₀
    with strip-value vr
  ... | Gv , Gv′ , rv , vr′ , auv
    with vv
  ... | TV-Var-Lin {K = K} {T = U} take₂ =
      K , U , remove-membership rv (take-implies-membership take₂)
  ... | TV-Var-Un x∈ᵘ =
      ⊥-elim
        (lin-un-disjoint x∈₀
          (remove-membership-un r (remove-membership-un rv x∈ᵘ)))

  select-live-synth-removed r
    (T-App d₁ d₂)
    (Act-AppL step)
    ex =
    select-live-synth-removed r d₁ step ex

  select-live-synth-removed r
    (T-App (T-Val dv) d₂)
    (Act-AppR step)
    ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with select-live-check-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈

  select-live-synth-removed r
    (T-TApp d)
    (Act-TAppE step)
    ex =
    select-live-synth-removed r d step ex

  select-live-synth-removed r
    (T-Pair d₁ d₂)
    (Act-PairL step)
    ex =
    select-live-synth-removed r d₁ step ex

  select-live-synth-removed r
    (T-Pair (T-Val dv) d₂)
    (Act-PairR step)
    ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with select-live-synth-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈

  select-live-synth-removed r
    (T-Match d mb bs bj)
    (Act-MatchE step)
    ex =
    select-live-synth-removed r d step ex

  select-live-synth-removed r
    (T-LetPair d body)
    (Act-LetPairE step)
    ex =
    select-live-synth-removed r d step ex

  select-live-synth-removed r
    (T-LetUnit d₁ d₂)
    (Act-LetUnitE step)
    ex =
    select-live-check-removed r d₁ step ex

  select-live-check-removed :
    ∀ {n k pk mult}
      {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {i : Fin k}
      {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇐ T ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-SendLab {k = k} x i ]→ e₂
    → Extract Γ₀ (ExprSemantics.L-SendLab {k = k} x i) Γin
    → Σ Kind λ K → Σ (NfTy [] K) λ U → Γ₂ ∋ˡ x ∶ U

  select-live-check-removed r (T-Check d sub) step ex =
    select-live-synth-removed r d step ex

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
  appR-extract-disjoint-recv r d step ex
    with recv-live-check-removed r d step ex
  ... | K , U , x∈ = recv-extract-disjoint r ex x∈

  appR-extract-disjoint-send :
    ∀ {n}
      {Γ₀ Γ₂ Γ₃ Γin Γv : Ctx [] n}
      {x : Fin n} {w : Value [] n}
      {e₁ e₂ : Expr [] n}
      {A : NfTy [] TLin}
      {G : Ctx [] n}
    → RemoveCtx Γ₀ G Γ₂
    → LinearDisjoint Γ₀ Γv
    → Γ₂ ⊢ e₁ ⇐ A ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-SendVal x w ]→ e₂
    → ExprSemantics.L-SendVal x w ⦂ Γin ⇒ Γv
    → Extract Γ₀ (ExprSemantics.L-SendVal x w) Γin
    → LinearDisjoint G Γin
  appR-extract-disjoint-send r disj d step lbl ex
    with send-live-check-removed r d step ex
  ... | K , U , x∈ = send-extract-disjoint r disj lbl ex x∈

  appR-extract-disjoint-sendlab :
    ∀ {n k}
      {Γ₀ Γ₂ Γ₃ Γin Γin′ : Ctx [] n}
      {x : Fin n} {i : Fin k}
      {e₁ e₂ : Expr [] n}
      {A : NfTy [] TLin}
      {G : Ctx [] n}
      {v : Variance} {P : NfTy [] KP} {S : NfTy [] SLin}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇐ A ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-SendLab {k = k} x i ]→ e₂
    → ExprSemantics.L-SendLab {k = k} x i ⦂ Γin ⇒ Γin′
    → Extract Γ₀ (ExprSemantics.L-SendLab {k = k} x i) Γin
    → LinearDisjoint G Γin
  appR-extract-disjoint-sendlab r d step (Label-SendLab {v = v} {P = P} {S = S} take au) ex@(Ex-SendLab rin _)
    with select-live-check-removed r d step ex
  ... | K , U , x∈ = recv-input-disjoint-core r rin take au x∈

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

tapp-receive-output-id :
  ∀ {n}
    {Γ₀ Γ₂ : Ctx [] n}
    {T : Ty [] TLin}
    {U : NfTy [] (KV KT Lin)}
  → Γ₀ ⊢ E-TApp (E-Val (V-Const C-Receive)) T ⇒ U ⊣ Γ₂
  → Γ₂ ≡ Γ₀
tapp-receive-output-id d = sym (receive₁-rigid d)

tapp-receive₁-output-id :
  ∀ {n}
    {Γ₀ Γ₂ : Ctx [] n}
    {T : Ty [] TLin}
    {S : Ty [] SLin}
    {U : NfTy [] (KV KT Lin)}
  → Γ₀ ⊢ E-TApp (E-Val (V-Receive₁ T)) S ⇒ U ⊣ Γ₂
  → Γ₂ ≡ Γ₀
tapp-receive₁-output-id d = sym (receive₂-rigid d)

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

preserve⇒-send :
  ∀ {n}
    {Γ₀ Γm Γ₂ Γin Γv : Ctx [] n}
    {x : Fin n} {v : Value [] n}
    {Tᵣ : Ty [] TLin} {Sᵣ : Ty [] SLin}
    {A Uarg R : NfTy [] TLin}
  → Γ₀ ⊢ᵥ V-Send₃ Tᵣ Sᵣ v ⇒ linArrNf A R ⊣ Γm
  → Γm ⊢ᵥ V-Var x ⇒ Uarg ⊣ Γ₂
  → normalTyOf Uarg <:ₜ normalTyOf A
  → (lbl : ExprSemantics.L-SendVal x v ⦂ Γin ⇒ Γv)
  → Extract Γ₀ (ExprSemantics.L-SendVal x v) Γin
  → LinearDisjoint Γ₀ Γv
  → PresSynth Γin Γv lbl Γ₀ Γ₂ (E-Val (V-Var x)) R
preserve⇒-send
  {Γ₀ = Γ₀} {Γ₂ = Γ₂}
  {x = x} {v = v}
  {Tᵣ = Tᵣ} {Sᵣ = Sᵣ}
  {A = A} {Uarg = Uarg} {R = R}
  vr vv sub lbl@(Label-SendVal {T = T} {S = S} take dv au) ex disj
  with send-remove-membership (proj₂ (extract-remove ex)) take
... | Γx , rm , x∈
  with check-output-unique
         (replay-check-allUsed
           (T-Check
             {T = T} {U = T}
             (T-Val {T = T} dv)
             (<:ₜ-refl (normalTyOf T)))
           (remove-frame rm)
           au)
         (proj₁ (send₃-shape {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} vr))
... | eqΓm
  rewrite eqΓm
  with vv
... | TV-Var-Un x∈ᵘ = ⊥-elim (lin-un-disjoint x∈ x∈ᵘ)
... | TV-Var-Lin take′
  with take-from-membership x∈
... | Γx′ , take₀
  with take-unique take₀ take′
... | eqChan , eqΓ
  rewrite eqΓ
  with sendChan-subtype
         {T₁ = T} {T₂ = normalizeTy Tᵣ}
         {S₁ = S} {S₂ = normalizeTy Sᵣ}
         (subst
           (λ X → normalTyOf X <:ₜ normalTyOf (sendChanNf (normalizeTy Tᵣ) (normalizeTy Sᵣ)))
           (sym eqChan)
           (subst
             (λ X → normalTyOf Uarg <:ₜ normalTyOf X)
             (proj₁ (proj₂ (send₃-shape {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} vr)))
             sub))
... | _ , S<:Sᵣ
  with take-replace-lin {U = sessNf S} take₀
... | Γ₁ , rep =
  let
    eqAll : allUsedCtx Γ₀ ≡ allUsedCtx Γ₁
    eqAll = trans (allUsedCtx-remove rm) (allUsedCtx-replace-lin x∈ rep)
  in
  record
    { Gf = allUsedCtx Γ₀
    ; Γ₀′ = Γ₀
    ; Γ₁ = Γ₁
    ; Γ₁′ = Γ₁
    ; U = sessNf S
    ; src-remove = remove-usedCtx Γ₀
    ; dst-remove =
        subst
          (λ X → RemoveCtx Γ₁ X Γ₁)
          (sym eqAll)
          (remove-usedCtx Γ₁)
    ; ctx-step = Ctx-Send rm dv au x∈ rep
    ; compat = send-compatible ex
    ; synth = T-Val (TV-Var-Lin (replace-take take₀ rep))
    ; subtype =
        subst
          (λ X → normalTyOf (sessNf S) <:ₜ normalTyOf X)
          (sym (proj₂ (proj₂ (send₃-shape {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} vr))))
          (sess-subtype {S₁ = S} {S₂ = normalizeTy Sᵣ} S<:Sᵣ)
    }

mutual

  preserve⇒-appR-core :
    ∀ {n k}
      {Γ₀ Γ₂ Γ₃ : Ctx [] n}
      {Γin Γv G G′ : Ctx [] n}
      {v : Value [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] (k + n)}
      {A V : NfTy [] TLin}
      {ℓ : Label n k}
    → (r : RemoveCtx Γ₀ G Γ₂)
    → G ⊢ᵥ v ⇒ linArrNf A V ⊣ G′
    → AllUsed G′
    → Γ₂ ⊢ e₁ ⇐ A ⊣ Γ₃
    → e₁ —[ ℓ ]→ e₂
    → (lbl : ℓ ⦂ Γin ⇒ Γv)
    → (ex : Extract Γ₀ ℓ Γin)
    → LinearDisjoint Γ₀ Γv
    → LinearDisjoint G Γin
    → PresSynth Γin Γv lbl Γ₀ Γ₃ (E-App (E-Val (ES.weakenValueBy k v)) e₂) V
  preserve⇒-appR-core {k = k} {Γ₀ = Γ₀} {Γ₂ = Γ₂} {Γ₃ = Γ₃}
    {Γin = Γin} {Γv = Γv} {G = G} {v = v} {e₂ = e₂} {A = A} {V = V}
    r dv′ au darg step lbl ex disj ldex
    with preserve⇐ {T = A} darg step lbl
         (remove-extract r ldex ex)
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
          (replay-synth-allUsed
            (weaken-val-synth {k = k} dv′)
            (remove-frame dstr)
            (allUsed-extendUsed k au))
          (PresCheck.check pc)
    ; subtype = <:ₜ-refl (normalTyOf V)
    }

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
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    d@(T-TApp (T-Val vr))
    (Act-Send₁ {T = T})
    lbl@(Label-β _ _) ex _
    rewrite sym (send₁-rigid d) =
      basePres
        {Γ₀ = Γ₀} {Γ₂ = Γ₀}
        {U = normalizeTy (SendTy1 T)}
        Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val TV-Send₁)
        (subst
          (λ X → normalTyOf (normalizeTy (SendTy1 T)) <:ₜ normalTyOf X)
          (sym (send₁-ty d))
          (<:ₜ-refl (normalTyOf (normalizeTy (SendTy1 T)))))
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    d@(T-TApp (T-Val vr))
    (Act-Send₂ {T = T} {S = S})
    lbl@(Label-β _ _) ex _
    rewrite sym (send₂-rigid d) =
      basePres
        {Γ₀ = Γ₀} {Γ₂ = Γ₀}
        {U = normalizeTy (SendTy T S)}
        Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val TV-Send₂)
        (subst
          (λ X → normalTyOf (normalizeTy (SendTy T S)) <:ₜ normalTyOf X)
          (sym (send₂-ty d))
          (<:ₜ-refl (normalTyOf (normalizeTy (SendTy T S)))))
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    (T-App (T-Val vr) pv)
    (Act-Send₃ {T = T} {S = S} {v = v})
    lbl@(Label-β _ _) ex _
    with send₂-shape {Tᵣ = T} {Sᵣ = S} vr
  ... | refl , (eqA , eqR)
    rewrite eqA | eqR =
      basePres
        {Γ₀ = Γ₀} {Γ₂ = Γ₂}
        {U = linArrNf (sendChanNf (normalizeTy T) (normalizeTy S))
             (sessNf (normalizeTy S))}
        Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val
          (subst
            (λ X → Γ₀ ⊢ᵥ V-Send₃ T S v ⇒ X ⊣ Γ₂)
            (sendTy-shape {T = T} {S = S})
            (TV-Send₃ pv)))
        (<:ₜ-refl
          (normalTyOf
            (linArrNf (sendChanNf (normalizeTy T) (normalizeTy S))
              (sessNf (normalizeTy S)))))
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    (T-App {Γ₂ = Γ₁} {Γ₃ = Γ₂}
      {T = A} {U = R}
      (T-Val vr)
      (T-Check {U = Uarg} (T-Val vv) sub))
    (Act-Sel {v = vₛ} {i = i} {P = Pₛ} {S = Sₛ} {x = x})
    (Label-SendLab {v = v} {P = P′} {S = S′} take au)
    (Ex-SendLab rin _)
    disj
    with select₂-shape vr
  ... | eqΓ₁ , eqA , eqR
    rewrite sym eqΓ₁ | eqA | eqR
    with extract-membership rin (take-implies-membership take)
  ... | x∈
    with vv
  ... | TV-Var-Un x∈ᵘ = ⊥-elim (lin-un-disjoint x∈ x∈ᵘ)
  ... | TV-Var-Lin take′
    with take-from-membership x∈
  ... | Γx , take₀
    with take-unique take₀ take′
  ... | eqChan , eqΓ
    rewrite eqΓ
    with take-replace-lin
           {U = selectOutNf v i P′ S′}
           (subst
             (λ X → Γ₀ ⊢ˡ x ∶ X ⊣ Γ₂)
             (sym eqChan)
             take′)
  ... | Γ₁ , rep =
    let
      eqAll : allUsedCtx Γ₀ ≡ allUsedCtx Γ₁
      eqAll =
        allUsedCtx-replace-lin
          (take-implies-membership
            (subst
              (λ X → Γ₀ ⊢ˡ x ∶ X ⊣ Γ₂)
              (sym eqChan)
              take′))
          rep

      selSub :
        normalTyOf (selectInNf v i P′ S′)
          <:ₜ
        normalTyOf (selectInNf vₛ i (normalizeTy Pₛ) (normalizeTy Sₛ))
      selSub =
        subst
          (λ X →
             normalTyOf X
               <:ₜ
             normalTyOf (selectInNf vₛ i (normalizeTy Pₛ) (normalizeTy Sₛ)))
          (sym eqChan)
          sub
    in
    record
      { Gf = allUsedCtx Γ₀
      ; Γ₀′ = Γ₀
      ; Γ₁ = Γ₁
      ; Γ₁′ = Γ₁
      ; U = selectOutNf v i P′ S′
      ; src-remove = remove-usedCtx Γ₀
      ; dst-remove =
          subst
            (λ X → RemoveCtx Γ₁ X Γ₁)
            (sym eqAll)
            (remove-usedCtx Γ₁)
      ; ctx-step =
          Ctx-Select
            (take-implies-membership
              (subst
                (λ X → Γ₀ ⊢ˡ x ∶ X ⊣ Γ₂)
                (sym eqChan)
                take′))
            rep
      ; compat = Compat-Select
      ; synth =
          T-Val
            (TV-Var-Lin
              (replace-take
                (subst
                  (λ X → Γ₀ ⊢ˡ x ∶ X ⊣ Γ₂)
                  (sym eqChan)
                  take′)
                rep))
      ; subtype =
          select-app-subtype
            {v₂ = v}
            {P′ = P′}
            {S′ = S′}
            vr
            selSub
      }
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    d
    Act-Select₁
    lbl@(Label-β _ _) ex _ =
      basePres
        {Γ₀ = Γ₀} {Γ₂ = Γ₂}
        {U = R}
        Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val (select₁-pres d))
        (<:ₜ-refl (normalTyOf R))
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    d
    Act-Select₂
    lbl@(Label-β _ _) ex _ =
      basePres
        {Γ₀ = Γ₀} {Γ₂ = Γ₂}
        {U = R}
        Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val (select₂-pres d))
        (<:ₜ-refl (normalTyOf R))
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    d@(T-TApp (T-Val vr))
    (Act-Receive₁ {T = T})
    lbl@(Label-β _ _) ex _
    rewrite tapp-receive-output-id d =
      basePres
        {Γ₀ = Γ₀} {Γ₂ = Γ₀}
        {U = normalizeTy (ReceiveTy1 T)}
        Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val TV-Receive₁)
        (subst
          (λ X → normalTyOf (normalizeTy (ReceiveTy1 T)) <:ₜ normalTyOf X)
          (sym (receive₁-ty d))
          (<:ₜ-refl (normalTyOf (normalizeTy (ReceiveTy1 T)))))
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    d@(T-TApp (T-Val vr))
    (Act-Receive₂ {T = T} {S = S})
    lbl@(Label-β _ _) ex _
    rewrite tapp-receive₁-output-id d =
      basePres
        {Γ₀ = Γ₀} {Γ₂ = Γ₀}
        {U = normalizeTy (ReceiveTy T S)}
        Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val TV-Receive₂)
        (subst
          (λ X → normalTyOf (normalizeTy (ReceiveTy T S)) <:ₜ normalTyOf X)
          (sym (receive₂-ty d))
          (<:ₜ-refl (normalTyOf (normalizeTy (ReceiveTy T S)))))
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {Γv = Γv}
    {T = R}
    d
    (Act-Rcv {T = Tᵣ} {S = Sᵣ} {x = x} {v = v})
    (Label-RecvVal {T = T} {S = S} take auin dv au)
    (Ex-RecvVal rin _ _)
    disj
    with extract-membership rin (take-implies-membership take)
  ... | x∈
    with recv-app-inversion {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} {T = T} {S = S} d x∈
  ... | take₀ , _ , _ , sub
    with take-replace-lin {U = sessNf S} take₀
  ... | Γx , rep
    with mergeDisjointContext (replace-preserves-disjoint x∈ disj rep)
  ... | Γ₁ , merge =
    let
      ld : LinearDisjoint Γx Γv
      ld = replace-preserves-disjoint x∈ disj rep

      eqAll : allUsedCtx Γ₀ ≡ allUsedCtx Γ₁
      eqAll = trans (allUsedCtx-replace-lin x∈ rep) (allUsedCtx-merge ld merge)
    in
    record
      { Gf = allUsedCtx Γ₀
      ; Γ₀′ = Γ₀
      ; Γ₁ = Γ₁
      ; Γ₁′ = Γ₁
      ; U = pairNf T (sessNf S)
      ; src-remove = remove-usedCtx Γ₀
      ; dst-remove =
          subst
            (λ X → RemoveCtx Γ₁ X Γ₁)
            (sym eqAll)
            (remove-usedCtx Γ₁)
      ; ctx-step = Ctx-Rcv dv au disj x∈ rep merge
      ; compat = Compat-RecvVal
      ; synth =
          T-Val
            (TV-Pair
              (merge-value dv au ld merge)
              (TV-Var-Lin (replace-take take₀ rep)))
      ; subtype = sub
      }
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {e₁ = E-App (E-Val (V-Send₃ Tᵣ Sᵣ v)) (E-Val (V-Var x))}
    {e₂ = E-Val (V-Var x)}
    {T = R}
    (T-App {Γ₂ = Γm} {Γ₃ = Γ₂} {T = A} {U = R}
      (T-Val vr)
      (T-Check {U = U} (T-Val vv) sub))
    (Act-Send {T = Tᵣ} {S = Sᵣ} {x = x} {v = v})
    lbl ex disj =
    preserve⇒-send vr vv sub lbl ex disj
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
    = preserve⇒-appR-core
        r
        dv′
        au
        (T-Check pArg subArg)
        step
        lbl
        ex
        disj
        (appR-extract-disjoint-recv {A = A} r (T-Check pArg subArg) step ex)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-App (E-Val v) e₁}
    {T = V} {ℓ = ℓ}
    (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V}
      (T-Val dv)
      (T-Check pArg subArg))
    (Act-AppR {k = k} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@Ex-β disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-appR-core
        r
        dv′
        au
        (T-Check pArg subArg)
        step
        lbl
        ex
        disj
        (remove-allused-disjoint r)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-App (E-Val v) e₁}
    {T = V} {ℓ = ℓ}
    (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V}
      (T-Val dv)
      (T-Check pArg subArg))
    (Act-AppR {k = k} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@Ex-Fork disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-appR-core
        r
        dv′
        au
        (T-Check pArg subArg)
        step
        lbl
        ex
        disj
        (remove-allused-disjoint r)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-App (E-Val v) e₁}
    {T = V} {ℓ = ℓ}
    (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V}
      (T-Val dv)
      (T-Check pArg subArg))
    (Act-AppR {k = k} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@Ex-New disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-appR-core
        r
        dv′
        au
        (T-Check pArg subArg)
        step
        lbl
        ex
        disj
        (remove-allused-disjoint r)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-App (E-Val v) e₁}
    {T = V} {ℓ = ℓ}
    (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V}
      (T-Val dv)
      (T-Check pArg subArg))
    (Act-AppR {k = k} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@Ex-RecvLab disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-appR-core
        r
        dv′
        au
        (T-Check pArg subArg)
        step
        lbl
        ex
        disj
        (remove-allused-disjoint r)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-App (E-Val v) e₁}
    {T = V} {ℓ = ℓ}
    (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V}
      (T-Val dv)
      (T-Check pArg subArg))
    (Act-AppR {k = k} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@(Ex-SendVal _ _ _ _) disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-appR-core
        r
        dv′
        au
        (T-Check pArg subArg)
        step
        lbl
        ex
        disj
        (appR-extract-disjoint-send {A = A} r disj (T-Check pArg subArg) step lbl ex)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-App (E-Val v) e₁}
    {T = V} {ℓ = ℓ}
    (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V}
      (T-Val dv)
      (T-Check pArg subArg))
    (Act-AppR {k = k} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl@(Label-SendLab {v = vₗ} {P = Pₗ} {S = Sₗ} _ _)
    ex@(Ex-SendLab {i = i} _ _) disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-appR-core
        r
        dv′
        au
        (T-Check pArg subArg)
        step
        lbl
        ex
        disj
        (appR-extract-disjoint-sendlab
          {A = A}
          {v = vₗ}
          {P = Pₗ}
          {S = Sₗ}
          r
          (T-Check pArg subArg)
          step
          lbl
          ex)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-App (E-Val v) e₁}
    {T = V} {ℓ = ℓ}
    (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V}
      (T-Val dv)
      (T-Check pArg subArg))
    (Act-AppR {k = k} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@Ex-Close disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-appR-core
        r
        dv′
        au
        (T-Check pArg subArg)
        step
        lbl
        ex
        disj
        (remove-allused-disjoint r)
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
