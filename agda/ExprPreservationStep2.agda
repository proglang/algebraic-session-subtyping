module ExprPreservationStep2 where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Nat.Properties using (≤-refl; n≤1+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; inspect; Reveal_·_is_)

import Duality
open import Kinds
open import Kits
import Types
open import NormalTypes using
  ( N-Normal
  ; N-Var
  ; NV-Var
  ; N-Arrow
  ; N-Sub
  ; N-End
  ; toNormalProto
  ; toNormalTy
  ; nfProtoTy
  ; nfProtoTy-fromNormalProto
  ; nfTyTy-fromNormalTy
  ; sizeₚ
  )
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
open import Types using (Ty; T-Base)
open import AlgorithmicNFSubtyping using
  ( _<:ₜ_
  ; _<<:ₚ[_]_
  ; <<:ₚ-refl
  ; <:ₜ-refl
  ; <:ₜ-trans
  ; <:ₜ-pair
  ; <:ₜ-poly
  ; <:ₜ-sub
  ; <:ₜ-msg
  ; <:ₚ′-proto
  ; <:ₜ-end
  )
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
open import ExprSyntax using (Expr; Value; Const; E-Val; E-LetUnit; E-LetPair; E-Pair; E-App; E-TApp; V-Const; V-Var; V-Pair; V-Receive₁; V-Receive₂; V-Send₁; V-Send₂; V-Select₁; V-Select₂; C-New; C-Receive; C-Send; C-Select; C-Close; C-Fork; C-Unit)
open import ExprSemantics using (Label; Act-App; Act-TApp; Act-LetPair; Act-LetUnit; Act-PairV; Act-Rec; Act-Fork; Act-New; Act-Receive₁; Act-Receive₂; Act-Rcv; Act-Send₁; Act-Send₂; Act-Send; Act-Sel; Act-Select₁; Act-Select₂; Act-Close; Act-AppL; Act-AppR; Act-TAppE; Act-PairL; Act-PairR; Act-MatchE; Act-LetPairE; Act-LetUnitE; _—[_]→_)
import ExprSemantics as ES
open import ExprNormalTyping
open import NormalTypesSubstitution using
  ( NFSub
  ; nfSubTy
  ; wkNFSub
  ; singleNFSub
  ; singleNFSub-sound
  ; wkNFKind-sound
  ; substNFTy
  ; substNFProtoWith
  ; substNFTyWith
  ; substNFProto-sound
  ; substNFTy-sound
  ; msgNF-sound
  )
open import AlgorithmicNFSubstitution using
  ( msgNF-preserves-<:
  ; subst-preserves-<:ₜ
  )
open import AlgorithmicNFComplete using
  ( complete-<<:ₚ
  )
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
open import AlgorithmicNFSound using (sound-algₜ; sound-<<:ₚ)
import ExprContextReduction as ECR
open import ExprContextReduction using
  (_—ctx[_]→_; _⦂_⇒_; Compatible; Extract; ctx-step-preserves-disjoint
  ; Ctx-β; Ctx-New; Ctx-Fork; Ctx-Rcv; Ctx-Send; Ctx-Select; Ctx-Close
  ; ReplaceAt; replace-preserves-disjoint
  ; RemoveCtx; RM-∅; RM-drop; RM-allused; RM-lin; RM-un
  ; MergeCtx; MC-∅; MC-used-used; MC-used-left; MC-used-right; MC-un
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
  ; extendUsed
  ; used-head-eq
  ; Ex-β; Ex-Fork; Ex-New; Ex-RecvVal; Ex-RecvLab; Ex-SendVal; Ex-SendLab; Ex-Close
  ; Compat-β; Compat-New; Compat-Fork; Compat-RecvVal; Compat-SendVal; Compat-Select; Compat-Close
  )
open import ExprTypingProperties using (FrameCtx; FC-∅; FC-frame; FC-allused; FC-live; FC-un; frame-remove; replay-synth-allUsed; replay-check-allUsed)
open import ExprTypingLeftover using (strip-value; leftover-synth)
open import ExprTypingInversion
open import ExprPreservationStep2.ContextLemmas
open import ExprPreservationStep2.SubstitutionLemmas

open Kits.Syntax Types.Ty-Syntax hiding (Sort)
open Traversal Types.Ty-Traversal
open CTraversal record { fusion = Types.fusion }

extendUsed-eq :
  ∀ (Θ : List (Ty [] SLin)) {n} (Γ : Ctx [] n) → extendUsed Θ Γ ≡ extendUsed Θ Γ
extendUsed-eq Θ Γ = refl

extendUsedCR-eq :
  ∀ (Θ : List (Ty [] SLin)) {n} (Γ : Ctx [] n) → ECR.extendUsed Θ Γ ≡ extendUsed Θ Γ
extendUsedCR-eq Θ Γ = refl

postulate
  check-output-unique :
    ∀ {Δ n pk m pk′ m′} {Γ : Ctx Δ n} {e : Expr Δ n}
      {T : NfTy Δ (KV pk m)} {U : NfTy Δ (KV pk′ m′)} {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ e ⇐ T ⊣ Γ₁
    → Γ ⊢ e ⇐ U ⊣ Γ₂
    → Γ₁ ≡ Γ₂

  merge-value :
    ∀ {n K}
      {Γx Γv Γ₁ Γv′ : Ctx [] n}
      {v : Value [] n} {T : NfTy [] K}
    → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
    → AllUsed Γv′
    → LinearDisjoint Γx Γv
    → MergeCtx Γx Γv Γ₁
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γx

  replace-take :
    ∀ {n pk pk′}
      {Γ₀ Γx Γ₂ : Ctx [] n}
      {x : Fin n} {T : NfTy [] (KV pk Lin)} {U : NfTy [] (KV pk′ Lin)}
    → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₂
    → ReplaceAt Γ₀ x (B-Lin U) Γx
    → Γx ⊢ˡ x ∶ U ⊣ Γ₂

  replace-used-output :
    ∀ {n pk}
      {Γ₀ Γ₁ Γ₂ : Ctx [] n}
      {x : Fin n} {T : NfTy [] (KV pk Lin)}
    → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₂
    → ReplaceAt Γ₀ x (B-Used T) Γ₁
    → Γ₁ ≡ Γ₂

  take-from-membership :
    ∀ {n pk}
      {Γ : Ctx [] n}
      {x : Fin n} {T : NfTy [] (KV pk Lin)}
    → Γ ∋ˡ x ∶ T
    → Σ (Ctx [] n) λ Γ′ → Γ ⊢ˡ x ∶ T ⊣ Γ′

  take-unique :
    ∀ {n pk}
      {Γ : Ctx [] n}
      {x : Fin n} {T U : NfTy [] (KV pk Lin)}
      {Γ₁ Γ₂ : Ctx [] n}
    → Γ ⊢ˡ x ∶ T ⊣ Γ₁
    → Γ ⊢ˡ x ∶ U ⊣ Γ₂
    → (T ≡ U) × (Γ₁ ≡ Γ₂)

  take-implies-membership :
    ∀ {Δ n pk} {Γ Γ′ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Lin)}
    → Γ ⊢ˡ x ∶ T ⊣ Γ′
    → Γ ∋ˡ x ∶ T

  sendChan-subtype :
    ∀ {T₁ T₂ : NfTy [] TLin} {S₁ S₂ : NfTy [] SLin}
    → normalTyOf (sendChanNf T₁ S₁) <:ₜ normalTyOf (sendChanNf T₂ S₂)
    → (normalTyOf T₂ <:ₜ normalTyOf T₁) × (normalTyOf S₁ <:ₜ normalTyOf S₂)

  sess-subtype :
    ∀ {S₁ S₂ : NfTy [] SLin}
    → normalTyOf S₁ <:ₜ normalTyOf S₂
    → normalTyOf (sessNf S₁) <:ₜ normalTyOf (sessNf S₂)

  weaken-synth :
    ∀ {n Θ K}
      {Γ₁ Γ₂ : Ctx [] n}
      {e : Expr [] n} {T : NfTy [] K}
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
    → extendUsed Θ Γ₁ ⊢ ES.weakenExprBy (length Θ) e ⇒ T ⊣ extendUsed Θ Γ₂

  arrow-subtype-inversion :
    ∀ {m A V U}
    → normalTyOf U <:ₜ normalTyOf (N-Arrow {m = m} (≤p-step <p-mt) A V)
    → Σ (NfTy [] TLin) λ A′ →
        Σ (NfTy [] TLin) λ V′ →
          (U ≡ N-Arrow {m = m} (≤p-step <p-mt) A′ V′)
          × (normalTyOf A <:ₜ normalTyOf A′)
          × (normalTyOf V′ <:ₜ normalTyOf V)

  strengthen-letpair-body :
    ∀ {n pk₁ pk₂}
      {Γ₂ Γ₃ : Ctx [] n}
      {T : NfTy [] (KV pk₁ Lin)} {U : NfTy [] (KV pk₂ Lin)}
      {T′ : NfTy [] (KV pk₁ Lin)} {U′ : NfTy [] (KV pk₂ Lin)}
      {V : NfTy [] TLin}
      {e : Expr [] (suc (suc n))}
    → normalTyOf T′ <:ₜ normalTyOf T
    → normalTyOf U′ <:ₜ normalTyOf U
    → (T ∷ˡ (U ∷ˡ Γ₂)) ⊢ e ⇒ V ⊣ used∷ {T = T} (used∷ {T = U} Γ₃)
    → Σ (NfTy [] TLin) λ V′ →
        ((T′ ∷ˡ (U′ ∷ˡ Γ₂))
          ⊢ e ⇒ V′ ⊣ used∷ {T = T′} (used∷ {T = U′} Γ₃))
        × (normalTyOf V′ <:ₜ normalTyOf V)

  weaken-synth2 :
    ∀ {n Θ pk₁ pk₂}
      {Γ₂ Γ₃ : Ctx [] n}
      {T : NfTy [] (KV pk₁ Lin)} {U : NfTy [] (KV pk₂ Lin)}
      {V : NfTy [] TLin}
      {e : Expr [] (suc (suc n))}
    → (T ∷ˡ (U ∷ˡ Γ₂)) ⊢ e ⇒ V ⊣ used∷ {T = T} (used∷ {T = U} Γ₃)
    → (T ∷ˡ (U ∷ˡ extendUsed Θ Γ₂))
        ⊢ ES.weakenExprBy2 (length Θ) e ⇒ V ⊣ used∷ {T = T} (used∷ {T = U} (extendUsed Θ Γ₃))

  substTy-wkCtx-id :
    ∀ {K n} (Γ : Ctx [] n) (U : Ty [] K) → EST.substTyCtx (wkCtx Γ) U ≡ Γ

  remove-frame :
    ∀ {n}
      {Γ₀ Γv Γx : Ctx [] n}
    → RemoveCtx Γ₀ Γv Γx
    → FrameCtx Γx Γv Γ₀

  merge-frame :
    ∀ {n}
      {Γx Γv Γ₁ : Ctx [] n}
    → LinearDisjoint Γx Γv
    → MergeCtx Γx Γv Γ₁
    → FrameCtx Γx Γv Γ₁


record PresSynth
    {n Θ pk mult}
    (Γin : Ctx [] n)
    (Γv : Ctx [] n)
    {ℓ : Label n Θ}
    (lbl : ℓ ⦂ Γin ⇒ Γv)
    (Γ₀ : Ctx [] n)
    (Γ₂ : Ctx [] n)
    (e₂ : Expr [] (length Θ + n))
    (T : NfTy [] (KV pk mult)) : Set where
  field
    Gf : Ctx [] n
    Γ₀′ : Ctx [] n
    Γ₁ : Ctx [] (length Θ + n)
    Γ₁′ : Ctx [] (length Θ + n)
    U : NfTy [] (KV pk mult)

    src-remove : RemoveCtx Γ₀ Gf Γ₀′
    dst-remove : RemoveCtx Γ₁ (extendUsed Θ Gf) Γ₁′
    ctx-step : Γ₀′ —ctx[ ℓ ]→ Γ₁′
    compat : Compatible ctx-step lbl
    synth : Γ₁ ⊢ e₂ ⇒ U ⊣ extendUsed Θ Γ₂
    subtype : normalTyOf U <:ₜ normalTyOf T

record PresCheck
    {n Θ pk mult}
    (Γin : Ctx [] n)
    (Γv : Ctx [] n)
    {ℓ : Label n Θ}
    (lbl : ℓ ⦂ Γin ⇒ Γv)
    (Γ₀ : Ctx [] n)
    (Γ₂ : Ctx [] n)
    (e₂ : Expr [] (length Θ + n))
    (T : NfTy [] (KV pk mult)) : Set where
  field
    Gf : Ctx [] n
    Γ₀′ : Ctx [] n
    Γ₁ : Ctx [] (length Θ + n)
    Γ₁′ : Ctx [] (length Θ + n)

    src-remove : RemoveCtx Γ₀ Gf Γ₀′
    dst-remove : RemoveCtx Γ₁ (extendUsed Θ Gf) Γ₁′
    ctx-step : Γ₀′ —ctx[ ℓ ]→ Γ₁′
    compat : Compatible ctx-step lbl
    check : Γ₁ ⊢ e₂ ⇐ T ⊣ extendUsed Θ Γ₂

match-branch-subtype :
  ∀ {k}
    {ss : Subset.Subset k}
    {V : (i : Fin k) → i Subset.∈ ss → NfTy [] TLin}
    {U : NfTy [] TLin}
    {sub : (i : Fin k) → (i∈ : i Subset.∈ ss) → V i i∈ <:ₜ U}
    (i : Fin k)
    (i∈ : i Subset.∈ ss)
  → BranchJoin⁺ ss V ≡ just (U , sub)
  → normalTyOf (V i i∈) <:ₜ normalTyOf U
match-branch-subtype {sub = sub} i i∈ bj = sub i i∈


pair-subtype-inversion :
  ∀ {pk₁ pk₂}
    {X : NfTy [] TLin}
    {T : NfTy [] (KV pk₁ Lin)}
    {U : NfTy [] (KV pk₂ Lin)}
  → normalTyOf X <:ₜ normalTyOf (pairNf T U)
  → Σ (NfTy [] (KV pk₁ Lin)) λ T′ →
      Σ (NfTy [] (KV pk₂ Lin)) λ U′ →
        (X ≡ pairNf T′ U′)
        × (normalTyOf T′ <:ₜ normalTyOf T)
        × (normalTyOf U′ <:ₜ normalTyOf U)
pair-subtype-inversion (<:ₜ-pair T′<:T U′<:U) =
  _ , _ , refl , T′<:T , U′<:U

letpair-body-pres :
  ∀ {n Θ pk₁ pk₂}
    {Γ₂ Γ₃ : Ctx [] n}
    {T : NfTy [] (KV pk₁ Lin)} {U : NfTy [] (KV pk₂ Lin)}
    {T′ : NfTy [] (KV pk₁ Lin)} {U′ : NfTy [] (KV pk₂ Lin)}
    {V : NfTy [] TLin}
    {e : Expr [] (suc (suc n))}
  → normalTyOf T′ <:ₜ normalTyOf T
  → normalTyOf U′ <:ₜ normalTyOf U
  → (T ∷ˡ (U ∷ˡ Γ₂)) ⊢ e ⇒ V ⊣ used∷ {T = T} (used∷ {T = U} Γ₃)
  → Σ (NfTy [] TLin) λ V′ →
      ((T′ ∷ˡ (U′ ∷ˡ extendUsed Θ Γ₂))
        ⊢ ES.weakenExprBy2 (length Θ) e ⇒ V′ ⊣ used∷ {T = T′} (used∷ {T = U′} (extendUsed Θ Γ₃)))
      × (normalTyOf V′ <:ₜ normalTyOf V)
letpair-body-pres
  {Θ = Θ}
  {T = T} {U = U}
  {T′ = T′} {U′ = U′}
  T′<:T U′<:U d
  with strengthen-letpair-body {T = T} {U = U} {T′ = T′} {U′ = U′} T′<:T U′<:U d
... | V′ , d′ , V′<:V =
  V′ , weaken-synth2 {Θ = Θ} d′ , V′<:V

selectIn-subtype :
  ∀ {k}
    {v₁ v₂ : Variance} {i : Fin k}
    {P₁ P₂ : NfTy [] KP}
    {S₁ S₂ : NfTy [] SLin}
  → normalTyOf (selectInNf v₁ i P₁ S₁) <:ₜ normalTyOf (selectInNf v₂ i P₂ S₂)
  → (v₁ ≡ v₂)
    × (P₂ <<:ₚ[ v₁ ] P₁)
    × (S₁ <:ₜ S₂)
selectIn-subtype
  {v₁ = v₁}
  (<:ₜ-sub (<:ₜ-msg (<:ₚ′-proto ss paramRel) Ssub)) =
  refl , paramRel , Ssub

covers-refl : ∀ {v} → VarianceCovers v v
covers-refl {v = ⊕} = tt
covers-refl {v = ⊝} = tt
covers-refl {v = ⊘} = tt

materialize-head-used :
  ∀
    (T : Ty (KP ∷ []) KP)
    {u v : Variance}
    {P₁ P₂ : NfTy [] KP}
  → usageVariance T (here refl) ≡ used u
  → P₂ <<:ₚ[ v ] P₁
  → VarianceCovers v u
  → normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)
       <<:ₚ[ ⊝ ]
    normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)
materialize-head-used T {u = u} {v = v} {P₁} {P₂} uv pu cov =
  complete-<<:ₚ
    (suc (sizeₚ N₁ ⊔ sizeₚ N₂))
    {⊙ = ⊝}
    {T₁ = instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟}
    {T₂ = instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟}
    rawMinus
    {f₁ = Duality.d?⊥}
    {f₂ = Duality.d?⊥}
    {N₁ = N₁}
    {N₂ = N₂}
    eqN₁
    eqN₂
    (n≤1+n _)
  where
  N₁ : NfTy [] KP
  N₁ = normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)

  N₂ : NfTy [] KP
  N₂ = normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)

  eqN₁ :
    nfProtoTy N₁
      ≡
    Types.nf Duality.⊕ Duality.d?⊥ (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)
  eqN₁ =
    nfProtoTy-fromNormalProto
      (Types.nf-normal-proto (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟))

  eqN₂ :
    nfProtoTy N₂
      ≡
    Types.nf Duality.⊕ Duality.d?⊥ (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)
  eqN₂ =
    nfProtoTy-fromNormalProto
      (Types.nf-normal-proto (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟))

  rawPlus :
    instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟
      <<:[ ⊕ ]
    instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟
  rawPlus =
    subst-preserves-<<:-used⊕
      T
      {p = here refl}
      {u = u}
      {v = v}
      {ϕ = singletonSubst ⌞ P₂ ⌟}
      {ψ = singletonSubst ⌞ P₁ ⌟}
      uv
      (singletonSubst-≈ᵥ (sound-<<:ₚ pu))
      cov

  rawMinus :
    instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟
      <<:[ ⊝ ]
    instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟
  rawMinus = swap-<<: {v = ⊕} rawPlus

materialize-head-unused :
  ∀
    (T : Ty (KP ∷ []) KP)
    {P₁ P₂ : NfTy [] KP}
  → usageVariance T (here refl) ≡ unused
  → normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)
       <<:ₚ[ ⊝ ]
     normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)
materialize-head-unused T {P₁} {P₂} uv =
  subst
    (λ X →
      X <<:ₚ[ ⊝ ]
      normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟))
    (sym eqNf)
    (<<:ₚ-refl {⊙ = ⊝}
      (normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)))
  where
  eqNf :
    normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)
      ≡
    normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)
  eqNf = nfEq eqRaw
    where
    eqConv :
      instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟
        Types.≡c
      instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟
    eqConv =
      instantiate-unused-independent
        T
        {P = ⌞ P₁ ⌟}
        {Q = ⌞ P₂ ⌟}
        uv

    eqRaw :
      ⌞ normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟) ⌟
        ≡
      ⌞ normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟) ⌟
    eqRaw =
      trans
        (nfProtoTy-fromNormalProto
          (Types.nf-normal-proto (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)))
        (trans
          (Types.nf-complete Duality.d?⊥ Duality.d?⊥ eqConv)
          (sym
            (nfProtoTy-fromNormalProto
              (Types.nf-normal-proto (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)))))

mutual

  materializeListNf-sub-used :
    ∀
      (Ts : List (Ty (KP ∷ []) KP))
      {u v : Variance}
      {P₁ P₂ : NfTy [] KP}
      {S₁ S₂ : NfTy [] SLin}
    → allUsageVariance Ts (here refl) ≡ used u
    → P₂ <<:ₚ[ v ] P₁
    → VarianceCovers v u
    → S₁ <:ₜ S₂
    → materializeListNf Ts Duality.⊕ P₁ S₁
         <:ₜ
       materializeListNf Ts Duality.⊕ P₂ S₂

  materializeListNf-sub-unused :
    ∀
      (Ts : List (Ty (KP ∷ []) KP))
      {P₁ P₂ : NfTy [] KP}
      {S₁ S₂ : NfTy [] SLin}
    → allUsageVariance Ts (here refl) ≡ unused
    → S₁ <:ₜ S₂
    → materializeListNf Ts Duality.⊕ P₁ S₁
         <:ₜ
       materializeListNf Ts Duality.⊕ P₂ S₂

  materializeListNf-sub-used [] ()
  materializeListNf-sub-used (T ∷ Ts) {u = u} {v = v} {P₁} {P₂} {S₁} {S₂} eq pu cov ssub
    with usageVariance T (here refl) | inspect (usageVariance T) (here refl)
       | allUsageVariance Ts (here refl) | inspect (allUsageVariance Ts) (here refl)
       | eq
  ... | unused | Eq.[ eqT ] | used uTs | Eq.[ eqTs ] | refl =
    msgNF-preserves-<:
      (materialize-head-unused T {P₁ = P₁} {P₂ = P₂} eqT)
      (materializeListNf-sub-used Ts eqTs pu cov ssub)
  ... | used uT | Eq.[ eqT ] | unused | Eq.[ eqTs ] | refl =
    msgNF-preserves-<:
      (materialize-head-used T {u = uT} {v = v} {P₁ = P₁} {P₂ = P₂}
        eqT pu (covers-trans cov (join-left-covers {u₂ = unused} refl)))
      (materializeListNf-sub-unused Ts eqTs ssub)
  ... | used uT | Eq.[ eqT ] | used uTs | Eq.[ eqTs ] | eqJoin =
    msgNF-preserves-<:
      (materialize-head-used T {u = uT} {v = v} {P₁ = P₁} {P₂ = P₂}
        eqT pu (covers-trans cov (join-left-covers {u₂ = used uTs} eqJoin)))
      (materializeListNf-sub-used Ts eqTs pu
        (covers-trans cov (join-right-covers {u₂ = uTs} {u₁ = used uT} eqJoin))
        ssub)

  materializeListNf-sub-unused [] _ ssub = ssub
  materializeListNf-sub-unused (T ∷ Ts) {P₁} {P₂} {S₁} {S₂} eq ssub
    with usageVariance T (here refl) | inspect (usageVariance T) (here refl)
       | allUsageVariance Ts (here refl) | inspect (allUsageVariance Ts) (here refl)
       | eq
  ... | unused | Eq.[ eqT ] | unused | Eq.[ eqTs ] | refl =
    msgNF-preserves-<:
      (materialize-head-unused T {P₁ = P₁} {P₂ = P₂} eqT)
      (materializeListNf-sub-unused Ts eqTs ssub)
  ... | used uT | Eq.[ eqT ] | unused | Eq.[ eqTs ] | ()
  ... | used uT | Eq.[ eqT ] | used uTs | Eq.[ eqTs ] | eqJoin =
    ⊥-elim (joinUsage-used-used≢unused eqJoin)

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
select-app-subtype
  {v₁ = v₁} {i = i} {P = P} {S = S}
  {P′ = P′} {S′ = S′}
  vr selSub
  with select₂-shape vr
... | refl , refl , refl
  with selectIn-subtype selSub
... | refl , psub , ssub
  with ProtocolConstructors _ v₁ i
... | Ts , inj₁ usedTs =
  <:ₜ-sub
    (materializeListNf-sub-used
      Ts
      usedTs
      psub
      covers-refl
      ssub)
... | Ts , inj₂ unusedTs =
  <:ₜ-sub
    (materializeListNf-sub-unused
      Ts
      unusedTs
      ssub)

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
    {rep : ReplaceAt Γ₀ x (B-Used (normalizeTy EndLin)) Γ₂}
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
  ∀ {n Θ}
    {Γ₀ Γ₂ : Ctx [] n}
    {Γin G : Ctx [] n}
    {ℓ : Label n Θ}
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
  ∀ {n pk pk′}
    {Γ₀ Γ₂ Γin Γr Γin′ G : Ctx [] n}
    {x : Fin n}
    {T : NfTy [] (KV pk Lin)}
    {U : NfTy [] (KV pk′ Lin)}
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
  ∀ {n pk}
    {Γ₀ Γ₂ Γin G : Ctx [] n}
    {x : Fin n} {v : Value [] n}
    {U : NfTy [] (KV pk Lin)}
  → RemoveCtx Γ₀ G Γ₂
  → Extract Γ₀ (ExprSemantics.L-RecvVal x v) Γin
  → Γ₂ ∋ˡ x ∶ U
  → LinearDisjoint G Γin
recv-extract-disjoint r (Ex-RecvVal rin take au) x∈ =
  recv-input-disjoint-core r rin take au x∈

send-input-disjoint-core :
  ∀ {n pk}
    {Γ₀ Γ₂ Γin Γr Γv G : Ctx [] n}
    {x : Fin n}
    {T : NfTy [] TLin} {S : NfTy [] SLin}
    {U : NfTy [] (KV pk Lin)}
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
  ∀ {n pk}
    {Γ₀ Γ₂ Γin Γv G : Ctx [] n}
    {x : Fin n} {w : Value [] n}
    {U : NfTy [] (KV pk Lin)}
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

wkNfProto-normalizeTy :
  ∀ {K} {P : Ty [] KP}
  → wkNfTy {K′ = K} (normalizeTy P) ≡ normalizeTy (P ⋯ weakenᵣ K)
wkNfProto-normalizeTy {K} {P} =
  trans
    (sym (normalizeTy-id (wkNfTy {K′ = K} (normalizeTy P))))
    (nfEq eqRaw)
  where
  eqcNorm : ⌞ normalizeTy P ⌟ Types.≡c P
  eqcNorm =
    Types.≡c-trns
      (Types.≡c-refl-eq (nfProtoTy-fromNormalProto (Types.nf-normal-proto P)))
      (Types.nf-sound+ P)

  eqcWk : ⌞ wkNfTy {K′ = K} (normalizeTy P) ⌟ Types.≡c (P ⋯ weakenᵣ K)
  eqcWk =
    subst
      (λ X → X Types.≡c (P ⋯ weakenᵣ K))
      (sym (wkNFKind-sound {K = KP} {K′ = K} (normalizeTy P)))
      (subst-preserves-≡c eqcNorm (weakenᵣ K))

  eqRaw :
    ⌞ normalizeTy ⌞ wkNfTy {K′ = K} (normalizeTy P) ⌟ ⌟
      ≡
    ⌞ normalizeTy (P ⋯ weakenᵣ K) ⌟
  eqRaw =
    trans
      (nfProtoTy-fromNormalProto (Types.nf-normal-proto ⌞ wkNfTy {K′ = K} (normalizeTy P) ⌟))
      (trans
        (Types.nf-complete Duality.d?⊥ Duality.d?⊥ eqcWk)
        (sym (nfProtoTy-fromNormalProto (Types.nf-normal-proto (P ⋯ weakenᵣ K)))))

substNFProtoWith-normalizeTy :
  ∀ {Δ₁ Δ₂}
    (σ : NFSub Δ₁ Δ₂)
    (P : Ty Δ₁ KP)
  → substNFProtoWith σ (normalizeTy P)
      ≡ normalizeTy (P ⋯ nfSubTy σ)
substNFProtoWith-normalizeTy σ P = nfEq raw
  where
  eqcNorm : ⌞ normalizeTy P ⌟ Types.≡c P
  eqcNorm =
    Types.≡c-trns
      (Types.≡c-refl-eq (nfProtoTy-fromNormalProto (Types.nf-normal-proto P)))
      (Types.nf-sound+ P)

  eqcSubst : (⌞ normalizeTy P ⌟ ⋯ nfSubTy σ) Types.≡c (P ⋯ nfSubTy σ)
  eqcSubst =
    subst-preserves-≡c eqcNorm (nfSubTy σ)

  raw :
    ⌞ substNFProtoWith σ (normalizeTy P) ⌟
      ≡
    ⌞ normalizeTy (P ⋯ nfSubTy σ) ⌟
  raw =
    trans
      (substNFProto-sound σ (normalizeTy P))
      (trans
        (Types.nf-complete Duality.d?⊥ Duality.d?⊥ eqcSubst)
        (sym (nfProtoTy-fromNormalProto (Types.nf-normal-proto (P ⋯ nfSubTy σ)))))

select₁-materialize-head :
  ∀ (T : Ty (KP ∷ []) KP) {P : Ty [] KP}
  → substNFProtoWith
      (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))
      (normalizeTy
        (instantiate
          ⦃ Kₛ ⦄
          Duality.⊕
          T
          (Types.T-Var (there (here refl)))))
      ≡
    normalizeTy
      (instantiate
        ⦃ Kₛ ⦄
        Duality.⊕
        T
        ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟)
select₁-materialize-head T {P} =
  trans
    (substNFProtoWith-normalizeTy
      (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))
      (instantiate
        ⦃ Kₛ ⦄
        Duality.⊕
        T
        (Types.T-Var (there (here refl)))))
    (cong normalizeTy
      (instantiate-compose
        {Δ₁ = SLin ∷ KP ∷ []}
        {Δ₂ = SLin ∷ []}
        {K = KP}
        {p = Duality.⊕}
        T
        {P = Types.T-Var (there (here refl))}
        {ϕ = nfSubTy (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))}))

materializeList-select₁-compose :
  ∀ (Ts : List (Ty (KP ∷ []) KP)) {P : Ty [] KP}
  → TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      (Types.T-Var (there (here refl)))
      (Types.T-Var (here refl))
      ⋯ nfSubTy (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))
      ≡
    TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
      (Types.T-Var (here refl))
materializeList-select₁-compose [] = refl
materializeList-select₁-compose (T ∷ Ts) {P}
  rewrite instantiate-compose
            {Δ₁ = SLin ∷ KP ∷ []}
            {Δ₂ = SLin ∷ []}
            {K = KP}
            {p = Duality.⊕}
            T
            {P = Types.T-Var (there (here refl))}
            {ϕ = nfSubTy (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))}
        | materializeList-select₁-compose Ts {P} =
  refl

materializeListNf-select₁ :
  ∀ (Ts : List (Ty (KP ∷ []) KP)) {P : Ty [] KP}
  → substNFTyWith
      (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))
      (materializeListNf
        Ts
        Duality.⊕
        (normalizeTy (Types.T-Var (there (here refl))))
        (normalizeTy (Types.T-Var (here refl))))
      ≡
    materializeListNf
      Ts
      Duality.⊕
      (wkNfTy {K′ = SLin} (normalizeTy P))
      (normalizeTy (Types.T-Var (here refl)))
materializeListNf-select₁ Ts {P} = nfEq raw
  where
  σ : NFSub (SLin ∷ KP ∷ []) (SLin ∷ [])
  σ = wkNFSub {K = SLin} (singleNFSub (normalizeTy P))

  leftNF : NfTy (SLin ∷ KP ∷ []) SLin
  leftNF =
    materializeListNf
      Ts
      Duality.⊕
      (normalizeTy (Types.T-Var (there (here refl))))
      (normalizeTy (Types.T-Var (here refl)))

  rightNF : NfTy (SLin ∷ []) SLin
  rightNF =
    materializeListNf
      Ts
      Duality.⊕
      (wkNfTy {K′ = SLin} (normalizeTy P))
      (normalizeTy (Types.T-Var (here refl)))

  rightRaw :
    Ty (SLin ∷ []) SLin
  rightRaw =
    TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
      (Types.T-Var (here refl))

  raw :
    ⌞ substNFTyWith σ leftNF ⌟ ≡ ⌞ rightNF ⌟
  raw = trans eq₁ (trans eq₂ (trans eq₃ eq₄))
    where
    eq₁ :
      ⌞ substNFTyWith σ leftNF ⌟
        ≡
      Types.nf Duality.⊕ Duality.d?⊥ (⌞ leftNF ⌟ ⋯ nfSubTy σ)
    eq₁ = substNFTy-sound σ leftNF

    eq₂ :
      Types.nf Duality.⊕ Duality.d?⊥ (⌞ leftNF ⌟ ⋯ nfSubTy σ)
        ≡
      Types.nf Duality.⊕ Duality.d?⊥
        (TypesProtocolConstructors.materializeList
          Ts
          Duality.⊕
          (Types.T-Var (there (here refl)))
          (Types.T-Var (here refl))
          ⋯ nfSubTy σ)
    eq₂ =
      Types.nf-complete
        Duality.d?⊥
        Duality.d?⊥
        (subst-preserves-≡c
          (materializeListNf-raw
            Ts
            {P = normalizeTy (Types.T-Var (there (here refl)))}
            {S = normalizeTy (Types.T-Var (here refl))})
          (nfSubTy σ))

    eq₃ :
      Types.nf Duality.⊕ Duality.d?⊥
        (TypesProtocolConstructors.materializeList
          Ts
          Duality.⊕
          (Types.T-Var (there (here refl)))
          (Types.T-Var (here refl))
          ⋯ nfSubTy σ)
        ≡
      Types.nf Duality.⊕ Duality.d?⊥ rightRaw
    eq₃ =
      cong
        (Types.nf Duality.⊕ Duality.d?⊥)
        (materializeList-select₁-compose Ts {P})

    eq₄ :
      Types.nf Duality.⊕ Duality.d?⊥ rightRaw
        ≡
      ⌞ rightNF ⌟
    eq₄ = trans eq₄a eq₄b
      where
      eq₄a :
        Types.nf Duality.⊕ Duality.d?⊥ rightRaw
          ≡
        Types.nf Duality.⊕ Duality.d?⊥ ⌞ rightNF ⌟
      eq₄a =
        sym
          (Types.nf-complete
            Duality.d?⊥
            Duality.d?⊥
            (materializeListNf-raw
              Ts
              {P = wkNfTy {K′ = SLin} (normalizeTy P)}
              {S = normalizeTy (Types.T-Var (here refl))}))

      eq₄b :
        Types.nf Duality.⊕ Duality.d?⊥ ⌞ rightNF ⌟
          ≡
        ⌞ rightNF ⌟
      eq₄b = Types.nf-idempotent (toNormalTy rightNF)

wkNfTy-normalizeTy-subst-raw :
  ∀ {K Kₚ} {P : Ty [] Kₚ} {U : Ty [] K}
  → ⌞ wkNfTy {K′ = K} (normalizeTy P) ⌟ ⋯ ⦅ ⌞ normalizeTy U ⌟ ⦆ₛ
      ≡
    ⌞ normalizeTy P ⌟
wkNfTy-normalizeTy-subst-raw {K} {Kₚ} {P} {U} =
  trans
    (cong
      (λ X → X ⋯ ⦅ ⌞ normalizeTy U ⌟ ⦆ₛ)
      (wkNFKind-sound {K = Kₚ} {K′ = K} (normalizeTy P)))
    (wk-cancels-⦅⦆-⋯ ⌞ normalizeTy P ⌟ ⌞ normalizeTy U ⌟)

wkNfTy-normalizeTy-subst :
  ∀ {K} {P : Ty [] KP} {U : Ty [] K}
  → substNFProtoWith
      (singleNFSub (normalizeTy U))
      (wkNfTy {K′ = K} (normalizeTy P))
      ≡
    normalizeTy P
wkNfTy-normalizeTy-subst {K} {P} {U} = nfEq raw
  where
  σ : NFSub (K ∷ []) []
  σ = singleNFSub (normalizeTy U)

  raw :
    ⌞ substNFProtoWith σ (wkNfTy {K′ = K} (normalizeTy P)) ⌟
      ≡
    ⌞ normalizeTy P ⌟
  raw =
    trans
      (substNFProto-sound σ (wkNfTy {K′ = K} (normalizeTy P)))
      (trans
        (cong
          (Types.nf Duality.⊕ Duality.d?⊥)
          (trans
            (⋯-cong
              ⌞ wkNfTy {K′ = K} (normalizeTy P) ⌟
              (singleNFSub-sound (normalizeTy U)))
            (wkNfTy-normalizeTy-subst-raw {K = K} {P = P} {U = U})))
        (Types.nfp-idempotent (toNormalProto (normalizeTy P))))

wkNfTy-normalizeTy-substTy :
  ∀ {K pk m} {P : Ty [] (KV pk m)} {U : Ty [] K}
  → substNFTyWith
      (singleNFSub (normalizeTy U))
      (wkNfTy {K′ = K} (normalizeTy P))
      ≡
    normalizeTy P
wkNfTy-normalizeTy-substTy {K} {P = P} {U = U} = nfEq raw
  where
  σ : NFSub (K ∷ []) []
  σ = singleNFSub (normalizeTy U)

  raw :
    ⌞ substNFTyWith σ (wkNfTy {K′ = K} (normalizeTy P)) ⌟
      ≡
    ⌞ normalizeTy P ⌟
  raw =
    trans
      (substNFTy-sound σ (wkNfTy {K′ = K} (normalizeTy P)))
      (trans
        (cong
          (Types.nf Duality.⊕ Duality.d?⊥)
          (trans
            (⋯-cong
              ⌞ wkNfTy {K′ = K} (normalizeTy P) ⌟
              (singleNFSub-sound (normalizeTy U)))
            (wkNfTy-normalizeTy-subst-raw {K = K} {P = P} {U = U})))
        (Types.nf-idempotent (toNormalTy (normalizeTy P))))

materializeList-select₂-compose :
  ∀ (Ts : List (Ty (KP ∷ []) KP)) {P : Ty [] KP} {S : Ty [] SLin}
  → TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
      (Types.T-Var (here refl))
      ⋯ ⦅ ⌞ normalizeTy S ⌟ ⦆ₛ
      ≡
    TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      ⌞ normalizeTy P ⌟
      ⌞ normalizeTy S ⌟
materializeList-select₂-compose [] = refl
materializeList-select₂-compose (T ∷ Ts) {P} {S}
  rewrite instantiate-compose
            {Δ₁ = SLin ∷ []}
            {Δ₂ = []}
            {K = KP}
            {p = Duality.⊕}
            T
            {P = ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟}
            {ϕ = ⦅ ⌞ normalizeTy S ⌟ ⦆ₛ}
        | wkNfTy-normalizeTy-subst-raw {K = SLin} {P = P} {U = S}
        | materializeList-select₂-compose Ts {P} {S} =
  refl

materializeListNf-select₂ :
  ∀ (Ts : List (Ty (KP ∷ []) KP)) {P : Ty [] KP} {S : Ty [] SLin}
  → substNFTyWith
      (singleNFSub (normalizeTy S))
      (materializeListNf
        Ts
        Duality.⊕
        (wkNfTy {K′ = SLin} (normalizeTy P))
        (normalizeTy (Types.T-Var (here refl))))
      ≡
    materializeListNf
      Ts
      Duality.⊕
      (normalizeTy P)
      (normalizeTy S)
materializeListNf-select₂ Ts {P} {S} = nfEq raw
  where
  σ : NFSub (SLin ∷ []) []
  σ = singleNFSub (normalizeTy S)

  leftNF : NfTy (SLin ∷ []) SLin
  leftNF =
    materializeListNf
      Ts
      Duality.⊕
      (wkNfTy {K′ = SLin} (normalizeTy P))
      (normalizeTy (Types.T-Var (here refl)))

  rightNF : NfTy [] SLin
  rightNF =
    materializeListNf
      Ts
      Duality.⊕
      (normalizeTy P)
      (normalizeTy S)

  rightRaw : Ty [] SLin
  rightRaw =
    TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      ⌞ normalizeTy P ⌟
      ⌞ normalizeTy S ⌟

  raw :
    ⌞ substNFTyWith σ leftNF ⌟ ≡ ⌞ rightNF ⌟
  raw = trans eq₁ (trans eq₂ (trans eq₃ eq₄))
    where
    eq₁ :
      ⌞ substNFTyWith σ leftNF ⌟
        ≡
      Types.nf Duality.⊕ Duality.d?⊥ (⌞ leftNF ⌟ ⋯ nfSubTy σ)
    eq₁ = substNFTy-sound σ leftNF

    eq₂ :
      Types.nf Duality.⊕ Duality.d?⊥ (⌞ leftNF ⌟ ⋯ nfSubTy σ)
        ≡
      Types.nf Duality.⊕ Duality.d?⊥
        (TypesProtocolConstructors.materializeList
          Ts
          Duality.⊕
          ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
          (Types.T-Var (here refl))
          ⋯ nfSubTy σ)
    eq₂ =
      Types.nf-complete
        Duality.d?⊥
        Duality.d?⊥
        (subst-preserves-≡c
          (materializeListNf-raw
            Ts
            {P = wkNfTy {K′ = SLin} (normalizeTy P)}
            {S = normalizeTy (Types.T-Var (here refl))})
          (nfSubTy σ))

    eq₃ :
      Types.nf Duality.⊕ Duality.d?⊥
        (TypesProtocolConstructors.materializeList
          Ts
          Duality.⊕
          ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
          (Types.T-Var (here refl))
          ⋯ nfSubTy σ)
        ≡
      Types.nf Duality.⊕ Duality.d?⊥ rightRaw
    eq₃ = trans eq₃a eq₃b
      where
      eq₃a :
        Types.nf Duality.⊕ Duality.d?⊥
          (TypesProtocolConstructors.materializeList
            Ts
            Duality.⊕
            ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
            (Types.T-Var (here refl))
            ⋯ nfSubTy σ)
          ≡
        Types.nf Duality.⊕ Duality.d?⊥
          (TypesProtocolConstructors.materializeList
            Ts
            Duality.⊕
            ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
            (Types.T-Var (here refl))
            ⋯ ⦅ ⌞ normalizeTy S ⌟ ⦆ₛ)
      eq₃a =
        cong
          (Types.nf Duality.⊕ Duality.d?⊥)
          (⋯-cong
            (TypesProtocolConstructors.materializeList
              Ts
              Duality.⊕
              ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
              (Types.T-Var (here refl)))
            (singleNFSub-sound (normalizeTy S)))

      eq₃b :
        Types.nf Duality.⊕ Duality.d?⊥
          (TypesProtocolConstructors.materializeList
            Ts
            Duality.⊕
            ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
            (Types.T-Var (here refl))
            ⋯ ⦅ ⌞ normalizeTy S ⌟ ⦆ₛ)
          ≡
        Types.nf Duality.⊕ Duality.d?⊥ rightRaw
      eq₃b =
        cong
          (Types.nf Duality.⊕ Duality.d?⊥)
          (materializeList-select₂-compose Ts {P} {S})

    eq₄ :
      Types.nf Duality.⊕ Duality.d?⊥ rightRaw
        ≡
      ⌞ rightNF ⌟
    eq₄ = trans eq₄a eq₄b
      where
      eq₄a :
        Types.nf Duality.⊕ Duality.d?⊥ rightRaw
          ≡
        Types.nf Duality.⊕ Duality.d?⊥ ⌞ rightNF ⌟
      eq₄a =
        sym
          (Types.nf-complete
            Duality.d?⊥
            Duality.d?⊥
            (materializeListNf-raw
              Ts
              {P = normalizeTy P}
              {S = normalizeTy S}))

      eq₄b :
        Types.nf Duality.⊕ Duality.d?⊥ ⌞ rightNF ⌟
          ≡
        ⌞ rightNF ⌟
      eq₄b = Types.nf-idempotent (toNormalTy rightNF)

select₁-body :
  ∀ {k} {v : Variance} {i : Fin k} {P : Ty [] KP}
  → substNFTy
      (select1Nf v i (N-Normal (N-Var (here refl))))
      (normalizeTy P)
      ≡
    select1Nf v i (normalizeTy P)
select₁-body {v = v} {i = i} {P = P}
  rewrite materializeListNf-select₁ (proj₁ (ProtocolConstructors _ v i)) {P = P} =
  refl

select₂-body :
  ∀ {k} {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin}
  → substNFTy
      (selectNf v i (wkNfTy {K′ = SLin} (normalizeTy P)) (N-Var (NV-Var (here refl))))
      (normalizeTy S)
      ≡
    selectNf v i (normalizeTy P) (normalizeTy S)
select₂-body {v = v} {i = i} {P = P} {S = S}
  rewrite wkNfTy-normalizeTy-subst {K = SLin} {P = P} {U = S}
        | materializeListNf-select₂ (proj₁ (ProtocolConstructors _ v i)) {P = P} {S = S} =
  refl

select₁-pres :
  ∀ {n k}
    {Γ Γ′ : Ctx [] n}
    {v : Variance} {i : Fin k} {P : Ty [] KP}
    {T : NfTy [] (KV KT Lin)}
  → Γ ⊢ E-TApp (E-Val (V-Const (C-Select v i))) P ⇒ T ⊣ Γ′
  → Γ ⊢ᵥ V-Select₁ v i P ⇒ T ⊣ Γ′
select₁-pres
  {Γ = Γ}
  {Γ′ = Γ′}
  {v = v} {i = i} {P = P}
  (T-TApp (T-Val (TV-Const CT-Select)))
  rewrite select₁-body {v = v} {i = i} {P = P} =
  TV-Select₁

select₂-pres :
  ∀ {n k}
    {Γ Γ′ : Ctx [] n}
    {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin}
    {T : NfTy [] (KV KT Lin)}
  → Γ ⊢ E-TApp (E-Val (V-Select₁ v i P)) S ⇒ T ⊣ Γ′
  → Γ ⊢ᵥ V-Select₂ v i P S ⇒ T ⊣ Γ′
select₂-pres
  {Γ = Γ}
  {Γ′ = Γ′}
  {v = v} {i = i} {P = P} {S = S}
  (T-TApp (T-Val TV-Select₁))
  rewrite select₂-body {v = v} {i = i} {P = P} {S = S} =
  TV-Select₂

poly-subtype-inversion :
  ∀ {K m}
    {U : NfTy [] (KV KT m)}
    {T : NfTy (K ∷ []) (KV KT m)}
  → normalTyOf U <:ₜ normalTyOf (polyNf T)
  → Σ (NfTy (K ∷ []) (KV KT m)) λ T′ →
      (U ≡ polyNf T′) × (normalTyOf T′ <:ₜ normalTyOf T)
poly-subtype-inversion (<:ₜ-poly sub) = _ , refl , sub

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
    → Σ PreKind λ pk′ → Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U

  recv-live-synth-removed r
    (T-App {m = Un} (T-Val ()) (T-Check (T-Val vv) sub))
    (Act-Rcv {x = x} {v = v})
    (Ex-RecvVal rin take au)

  recv-live-synth-removed r
    (T-App {m = Lin} (T-Val vr) (T-Check (T-Val vv) sub))
    (Act-Rcv {x = x} {v = v})
    (Ex-RecvVal rin take au)
    with receive₂-shape vr
  ... | refl , _
    with extract-membership rin (take-implies-membership take)
  ... | x∈₀
    with vv
  ... | TV-Var-Lin {pk = pk′} {T = U} take₂ =
      pk′ , U , take-implies-membership take₂

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
    (T-Match d bs bj)
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
    → Σ PreKind λ pk′ → Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U

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
    → Σ PreKind λ pk′ → Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U

  send-live-synth-removed r
    (T-App (T-Val vr) (T-Check (T-Val vv) sub))
    (Act-Send {T = Tᵣ} {S = Sᵣ})
    ex@(Ex-SendVal rin take dv au)
    with extract-membership rin (take-implies-membership take)
  ... | x∈₀
    with strip-value vr
  ... | Gv , Gv′ , rv , vr′ , auv
    with vv
  ... | TV-Pair dvw (TV-Var-Lin {pk = pk′} {T = U} take₂)
    with strip-value dvw
  ... | Gw , Gw′ , rw , dw′ , auw =
      pk′ , U , remove-membership rv (remove-membership rw (take-implies-membership take₂))

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
    (T-Match d bs bj)
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
    → Σ PreKind λ pk′ → Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U

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
    → Σ PreKind λ pk′ → Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U

  select-live-synth-removed r
    (T-App (T-Val vr) (T-Check (T-Val vv) sub))
    (Act-Sel {x = x})
    (Ex-SendLab rin take)
    with extract-membership rin (take-implies-membership take)
  ... | x∈₀
    with strip-value vr
  ... | Gv , Gv′ , rv , vr′ , auv
    with vv
  ... | TV-Var-Lin {pk = pk′} {T = U} take₂ =
      pk′ , U , remove-membership rv (take-implies-membership take₂)

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
    (T-Match d bs bj)
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
    → Σ PreKind λ pk′ → Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U

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

  pairR-extract-disjoint-recv :
    ∀ {n}
      {Γ₀ Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {v : Value [] n}
      {e₁ e₂ : Expr [] n}
      {pk mult}
      {A : NfTy [] (KV pk mult)}
      {G : Ctx [] n}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇒ A ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-RecvVal x v ]→ e₂
    → Extract Γ₀ (ExprSemantics.L-RecvVal x v) Γin
    → LinearDisjoint G Γin
  pairR-extract-disjoint-recv r d step ex
    with recv-live-synth-removed r d step ex
  ... | K , U , x∈ = recv-extract-disjoint r ex x∈

  pairR-extract-disjoint-send :
    ∀ {n}
      {Γ₀ Γ₂ Γ₃ Γin Γv : Ctx [] n}
      {x : Fin n} {w : Value [] n}
      {e₁ e₂ : Expr [] n}
      {pk mult}
      {A : NfTy [] (KV pk mult)}
      {G : Ctx [] n}
    → RemoveCtx Γ₀ G Γ₂
    → LinearDisjoint Γ₀ Γv
    → Γ₂ ⊢ e₁ ⇒ A ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-SendVal x w ]→ e₂
    → ExprSemantics.L-SendVal x w ⦂ Γin ⇒ Γv
    → Extract Γ₀ (ExprSemantics.L-SendVal x w) Γin
    → LinearDisjoint G Γin
  pairR-extract-disjoint-send r disj d step lbl ex
    with send-live-synth-removed r d step ex
  ... | K , U , x∈ = send-extract-disjoint r disj lbl ex x∈

  pairR-extract-disjoint-sendlab :
    ∀ {n k}
      {Γ₀ Γ₂ Γ₃ Γin Γin′ : Ctx [] n}
      {x : Fin n} {i : Fin k}
      {e₁ e₂ : Expr [] n}
      {pk mult}
      {A : NfTy [] (KV pk mult)}
      {G : Ctx [] n}
      {v : Variance} {P : NfTy [] KP} {S : NfTy [] SLin}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇒ A ⊣ Γ₃
    → e₁ —[ ExprSemantics.L-SendLab {k = k} x i ]→ e₂
    → ExprSemantics.L-SendLab {k = k} x i ⦂ Γin ⇒ Γin′
    → Extract Γ₀ (ExprSemantics.L-SendLab {k = k} x i) Γin
    → LinearDisjoint G Γin
  pairR-extract-disjoint-sendlab r d step (Label-SendLab {v = v} {P = P} {S = S} take au) ex@(Ex-SendLab rin _)
    with select-live-synth-removed r d step ex
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
  → Σ PreKind λ pk′ → Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₀ ∋ˡ x ∶ U
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
  → Σ PreKind λ pk′ → Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₀ ∋ˡ x ∶ U
receive-live-check (T-Check d _) step ex =
  receive-live-synth d step ex

weaken-val-synth :
  ∀ {n Θ K}
    {Γ₁ Γ₂ : Ctx [] n}
    {v : Value [] n}
    {T : NfTy [] K}
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  → extendUsed Θ Γ₁ ⊢ E-Val (ES.weakenValueBy (length Θ) v) ⇒ T ⊣ extendUsed Θ Γ₂
weaken-val-synth {Θ = Θ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = v} dv =
  subst
    (λ G₁′ → G₁′ ⊢ E-Val (ES.weakenValueBy (length Θ) v) ⇒ _ ⊣ extendUsed Θ Γ₂)
    (extendUsed-eq Θ Γ₁)
    (subst
      (λ G₂′ → extendUsed Θ Γ₁ ⊢ E-Val (ES.weakenValueBy (length Θ) v) ⇒ _ ⊣ G₂′)
      (extendUsed-eq Θ Γ₂)
      (weaken-synth {Θ = Θ} (T-Val dv)))

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
  ∀ {n} (Θ : List (Ty [] SLin)) {Γ : Ctx [] n}
  → AllUsed Γ
  → AllUsed (extendUsed Θ Γ)
allUsed-extendUsed [] au = au
allUsed-extendUsed (S ∷ Θ) au = AU-used {T = normalizeTy (SessLin S)} (allUsed-extendUsed Θ au)

extendUsed-disjoint :
  ∀ {n} (Θ : List (Ty [] SLin))
    {Γ₁ Γ₂ : Ctx [] n}
  → LinearDisjoint Γ₁ Γ₂
  → LinearDisjoint (extendUsed Θ Γ₁) (extendUsed Θ Γ₂)
extendUsed-disjoint [] ld = ld
extendUsed-disjoint (S ∷ Θ) ld =
  LD-used-used {T = normalizeTy (SessLin S)} (extendUsed-disjoint Θ ld)

extend-remove :
  ∀ (Θ : List (Ty [] SLin)) {n}
    {Γ₀ G Γ₂ : Ctx [] n}
  → RemoveCtx Γ₀ G Γ₂
  → RemoveCtx (extendUsed Θ Γ₀) (extendUsed Θ G) (extendUsed Θ Γ₂)
extend-remove [] r = r
extend-remove (S ∷ Θ) r = RM-allused {T = normalizeTy (SessLin S)} (extend-remove Θ r)

merge-result-unique :
  ∀ {n}
    {Γ₁ Γ₂ Γ Γ′ : Ctx [] n}
  → MergeCtx Γ₁ Γ₂ Γ
  → MergeCtx Γ₁ Γ₂ Γ′
  → Γ ≡ Γ′
merge-result-unique MC-∅ MC-∅ = refl
merge-result-unique (MC-used-used m₁) (MC-used-used m₂)
  rewrite merge-result-unique m₁ m₂ = refl
merge-result-unique (MC-used-left m₁) (MC-used-left m₂)
  rewrite merge-result-unique m₁ m₂ = refl
merge-result-unique (MC-used-right m₁) (MC-used-right m₂)
  rewrite merge-result-unique m₁ m₂ = refl
merge-result-unique (MC-un m₁) (MC-un m₂)
  rewrite merge-result-unique m₁ m₂ = refl

merge-extendUsed :
  ∀ {n}
    (Θ : List (Ty [] SLin))
    {Γ₁ Γ₂ Γ : Ctx [] n}
  → MergeCtx Γ₁ Γ₂ Γ
  → MergeCtx (extendUsed Θ Γ₁) (extendUsed Θ Γ₂) (extendUsed Θ Γ)
merge-extendUsed [] m = m
merge-extendUsed (S ∷ Θ) m =
  MC-used-used {T = normalizeTy (SessLin S)} (merge-extendUsed Θ m)

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

    rep : ReplaceAt Γ₀ x (B-Used (normalizeTy EndLin)) Γ₂
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
              (λ Gf → RemoveCtx Γ₂ (extendUsed [] Gf) Γ₂)
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
  → Γ₀ ⊢ᵥ V-Send₂ Tᵣ Sᵣ ⇒ linArrNf A R ⊣ Γm
  → Γm ⊢ᵥ V-Pair v (V-Var x) ⇒ Uarg ⊣ Γ₂
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
  vr (TV-Pair {T = Tv} {U = Uv} dvv (TV-Var-Lin take′)) sub
  lbl@(Label-SendVal {T = T} {S = S} take dv au) ex disj
  with send₂-shape {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} vr
... | eqΓm , eqA , eqR
  rewrite sym eqΓm | eqA | eqR
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
         (T-Check (T-Val dvv) (<:ₜ-refl (normalTyOf Tv)))
... | eqΓmid
  rewrite eqΓmid
  with sub
... | <:ₜ-pair Tv<:Tᵣ Uv<:Chan
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
           Uv<:Chan)
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
    ; subtype = sess-subtype {S₁ = S} {S₂ = normalizeTy Sᵣ} S<:Sᵣ
    }

mutual

  preserve⇒-appR-core :
    ∀ {n Θ}
      {Γ₀ Γ₂ Γ₃ : Ctx [] n}
      {Γin Γv G G′ : Ctx [] n}
      {v : Value [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] (length Θ + n)}
      {m : Multiplicity}
      {A V : NfTy [] TLin}
      {ℓ : Label n Θ}
    → (r : RemoveCtx Γ₀ G Γ₂)
    → G ⊢ᵥ v ⇒ N-Arrow {m = m} (≤p-step <p-mt) A V ⊣ G′
    → AllUsed G′
    → Γ₂ ⊢ e₁ ⇐ A ⊣ Γ₃
    → e₁ —[ ℓ ]→ e₂
    → (lbl : ℓ ⦂ Γin ⇒ Γv)
    → (ex : Extract Γ₀ ℓ Γin)
    → LinearDisjoint Γ₀ Γv
    → LinearDisjoint G Γin
    → PresSynth Γin Γv lbl Γ₀ Γ₃ (E-App (E-Val (ES.weakenValueBy (length Θ) v)) e₂) V
  preserve⇒-appR-core {Θ = Θ} {Γ₀ = Γ₀} {Γ₂ = Γ₂} {Γ₃ = Γ₃}
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
             (extendUsedCR-eq Θ G)
             ldstep)
           (extendUsed-disjoint Θ
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
    with merge-result-unique mdst (merge-extendUsed Θ msrc)
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
            (weaken-val-synth {Θ = Θ} dv′)
            (remove-frame dstr)
            (allUsed-extendUsed Θ au))
          (PresCheck.check pc)
    ; subtype = <:ₜ-refl (normalTyOf V)
    }

  preserve⇒-pairR-core :
    ∀ {n Θ}
      {Γ₀ Γ₂ Γ₃ : Ctx [] n}
      {Γin Γv G G′ : Ctx [] n}
      {v : Value [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] (length Θ + n)}
      {pk₁ pk₂ m}
      {T : NfTy [] (KV pk₁ m)}
      {U : NfTy [] (KV pk₂ m)}
      {ℓ : Label n Θ}
    → (r : RemoveCtx Γ₀ G Γ₂)
    → G ⊢ᵥ v ⇒ T ⊣ G′
    → AllUsed G′
    → Γ₂ ⊢ e₁ ⇒ U ⊣ Γ₃
    → e₁ —[ ℓ ]→ e₂
    → (lbl : ℓ ⦂ Γin ⇒ Γv)
    → (ex : Extract Γ₀ ℓ Γin)
    → LinearDisjoint Γ₀ Γv
    → LinearDisjoint G Γin
    → PresSynth Γin Γv lbl Γ₀ Γ₃ (E-Pair (E-Val (ES.weakenValueBy (length Θ) v)) e₂) (pairNf T U)
  preserve⇒-pairR-core {Θ = Θ} {Γ₀ = Γ₀} {Γ₂ = Γ₂} {Γ₃ = Γ₃}
    {Γin = Γin} {Γv = Γv} {G = G} {v = v} {e₂ = e₂} {T = T} {U = U}
    r dv′ au darg step lbl ex disj ldex
    with preserve⇒ darg step lbl
         (remove-extract r ldex ex)
         (remove-disjoint r disj)
  ... | ps
    with ctx-step-preserves-disjoint
           (PresSynth.ctx-step ps)
           lbl
           (PresSynth.compat ps)
           (remove-preserves-disjoint
             (PresSynth.src-remove ps)
             (sym-disjoint (remove-linear r)))
           (sym-disjoint (remove-removed-disjoint r disj))
  ... | ldstep
    with restore-disjoint
           (PresSynth.dst-remove ps)
           (subst
             (λ X → LinearDisjoint (PresSynth.Γ₁′ ps) X)
             (extendUsedCR-eq Θ G)
             ldstep)
           (extendUsed-disjoint Θ
             (remove-removed-disjoint
               (PresSynth.src-remove ps)
               (sym-disjoint (remove-linear r))))
  ... | ldtarget
    with mergeRemoveContext r (PresSynth.src-remove ps)
  ... | Gf , msrc , rsrc
    with mergeDisjointContext ldtarget
  ... | Γ₁ , mleft
    with frame-remove
           (merge-frame ldtarget mleft)
  ... | dstr
    with mergeRemoveContext dstr (PresSynth.dst-remove ps)
  ... | Gfdst , mdst , rdst
    with merge-result-unique mdst (merge-extendUsed Θ msrc)
  ... | eqG = record
    { Gf = Gf
    ; Γ₀′ = PresSynth.Γ₀′ ps
    ; Γ₁ = Γ₁
    ; Γ₁′ = PresSynth.Γ₁′ ps
    ; U = pairNf T (PresSynth.U ps)
    ; src-remove = rsrc
    ; dst-remove =
        subst
          (λ X → RemoveCtx Γ₁ X (PresSynth.Γ₁′ ps))
          eqG
          rdst
    ; ctx-step = PresSynth.ctx-step ps
    ; compat = PresSynth.compat ps
    ; synth =
        T-Pair
          (replay-synth-allUsed
            (weaken-val-synth {Θ = Θ} dv′)
            (remove-frame dstr)
            (allUsed-extendUsed Θ au))
          (PresSynth.synth ps)
    ; subtype =
        <:ₜ-pair
          (<:ₜ-refl (normalTyOf T))
          (PresSynth.subtype ps)
    }

  preserve⇒ :
    ∀ {n Θ pk mult}
      {Γ₀ : Ctx [] n} {Γ₂ : Ctx [] n}
      {Γin Γv : Ctx [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] (length Θ + n)}
      {T : NfTy [] (KV pk mult)} {ℓ : Label n Θ}
    → Γ₀ ⊢ e₁ ⇒ T ⊣ Γ₂
    → e₁ —[ ℓ ]→ e₂
    → (lbl : ℓ ⦂ Γin ⇒ Γv)
    → Extract Γ₀ ℓ Γin
    → LinearDisjoint Γ₀ Γv
    → PresSynth Γin Γv lbl Γ₀ Γ₂ e₂ T
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    (T-App {m = Lin} {T = A} {U = R} (T-Val vr) pv)
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
  ... | T₀ , eq , p
    rewrite polyNf-injective {Δ = []} eq =
      basePres {Γ₀ = Γ₀} {Γ₂ = Γ₂} {U = EST.substTyNf T₀ T} Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val
          (subst
            (λ X → X ⊢ᵥ substTyValue v T ⇒ EST.substTyNf T₀ T ⊣ Γ₂)
            (substTy-wkCtx-id Γ₀ T)
            (subst
              (λ X → EST.substTyCtx (wkCtx Γ₀) T ⊢ᵥ substTyValue v T ⇒ EST.substTyNf T₀ T ⊣ X)
              (substTy-wkCtx-id Γ₂ T)
              (substTy-preserves-value p))))
        (subst
          (λ X → normalTyOf (EST.substTyNf T₀ T) <:ₜ normalTyOf X)
          (sym (EST.substTyNF-bridge T₀ T))
          (<:ₜ-refl (normalTyOf (EST.substTyNf T₀ T))))
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
    (T-App {m = Un} (T-Val vr) pu)
    (Act-Rec {T = T} {U = U} {v = v} {u = u})
    lbl@(Label-β _ auv) ex _
    with rec-inversion vr
  ... | refl , eqRec , _
    with unArrNf-injective eqRec
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
    (T-App {m = Lin} {T = A} {U = R} (T-Val vr) (T-Check (T-Val vv) sub))
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
            (λ X → RemoveCtx Γ₂ (extendUsed [] X) Γ₂)
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
    {e₁ = E-App (E-Val (V-Const C-Fork)) (E-Val v)}
    {e₂ = E-Val (V-Const C-Unit)}
    (T-App {m = Un} (T-Val (TV-Const ())) _)
    Act-Fork
    lbl ex disj
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = U}
    d@(T-Match {ss = ssin} {incl = incl} (T-Val vv) bs bj)
    (ES.Act-Match {ss = ss} {ne = ne} {x = x} {branches = branches} {i = i} i∈)
    lbl@(ECR.Label-RecvLab _ _)
    Ex-RecvLab
    disj
    with vv
  ... | TV-Var-Lin take
    with take-replace-lin take
  ... | Γ₁ , rep =
    let
      eqAll : allUsedCtx Γ₀ ≡ allUsedCtx Γ₁
      eqAll =
        allUsedCtx-replace-lin
          (take-implies-membership take)
          rep
    in
    record
      { Gf = allUsedCtx Γ₀
      ; Γ₀′ = Γ₀
      ; Γ₁ = Γ₁
      ; Γ₁′ = Γ₁
      ; U = _
      ; src-remove = remove-usedCtx Γ₀
      ; dst-remove =
          subst
            (λ X → RemoveCtx Γ₁ X Γ₁)
            (sym eqAll)
            (remove-usedCtx Γ₁)
      ; ctx-step =
          ECR.Ctx-Match {ssin = ssin} {ssout = ss} {incl = incl} i∈
            (take-implies-membership take)
            rep
      ; compat = ECR.Compat-Match refl
      ; synth =
          EST.subst-var-preserves-synth
            (replace-take take rep)
            (bs i i∈)
      ; subtype = match-branch-subtype i i∈ bj
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
      let
        sessT = normalizeTy (SessLin S)
        dualT = dualSessNf (normalizeTy S)

        allUsed-new-eq :
          allUsedCtx (B-Lin sessT ▻ (B-Lin dualT ▻ Γ₀))
            ≡
          extendUsed (S ∷ Types.T-Dual Duality.D-S S ∷ []) (allUsedCtx Γ₀)
        allUsed-new-eq =
          cong
            (B-Used sessT ▻_)
            (used-head-eq
              {T₁ = dualT}
              {T₂ = normalizeTy (SessLin (Types.T-Dual Duality.D-S S))}
              {Γ = allUsedCtx Γ₀})

        synth-new-eq :
          (B-Used sessT ▻ (B-Used dualT ▻ Γ₀))
            ≡
          extendUsed (S ∷ Types.T-Dual Duality.D-S S ∷ []) Γ₀
        synth-new-eq =
          cong
            (B-Used sessT ▻_)
            (used-head-eq
              {T₁ = dualT}
              {T₂ = normalizeTy (SessLin (Types.T-Dual Duality.D-S S))}
              {Γ = Γ₀})

        synth-new :
          (B-Lin sessT ▻ (B-Lin dualT ▻ Γ₀))
            ⊢ E-Val (V-Pair (V-Var fzero) (V-Var (fsuc fzero)))
            ⇒ pairNf sessT dualT
            ⊣ (B-Used sessT ▻ (B-Used dualT ▻ Γ₀))
        synth-new =
          T-Val
            (TV-Pair
              (TV-Var-Lin take-here)
              (TV-Var-Lin (take-there✖ take-here)))
      in
      record
        { Gf = allUsedCtx Γ₀
        ; Γ₀′ = Γ₀
        ; Γ₁ = B-Lin (normalizeTy (SessLin S)) ▻ (B-Lin (dualSessNf (normalizeTy S)) ▻ Γ₀)
        ; Γ₁′ = B-Lin (normalizeTy (SessLin S)) ▻ (B-Lin (dualSessNf (normalizeTy S)) ▻ Γ₀)
        ; U = pairNf (normalizeTy (SessLin S)) (dualSessNf (normalizeTy S))
        ; src-remove = remove-usedCtx Γ₀
        ; dst-remove =
            subst
              (λ X →
                RemoveCtx
                  (B-Lin (normalizeTy (SessLin S)) ▻ (B-Lin (dualSessNf (normalizeTy S)) ▻ Γ₀))
                  X
                  (B-Lin (normalizeTy (SessLin S)) ▻ (B-Lin (dualSessNf (normalizeTy S)) ▻ Γ₀)))
              allUsed-new-eq
              (remove-usedCtx (B-Lin (normalizeTy (SessLin S)) ▻ (B-Lin (dualSessNf (normalizeTy S)) ▻ Γ₀)))
        ; ctx-step = Ctx-New
        ; compat = new-compatible ex
        ; synth =
            subst
              (λ X →
                (B-Lin sessT ▻ (B-Lin dualT ▻ Γ₀))
                  ⊢ E-Val (V-Pair (V-Var fzero) (V-Var (fsuc fzero)))
                  ⇒ pairNf sessT dualT
                  ⊣ X)
              synth-new-eq
              synth-new
        ; subtype =
            let
              pairTy = Ty.T-Pair
                (SessLin (Ty.T-Var (here refl)))
                (SessLin (Types.T-Dual Duality.D-S (Ty.T-Var (here refl))))
            in
            subst
              (λ X → normalTyOf (pairNf (normalizeTy (SessLin S)) (dualSessNf (normalizeTy S))) <:ₜ normalTyOf X)
              (trans
                (trans
                  (sym (newInst-shape {S = S}))
                  (sym (EST.substTy-normalizeTy pairTy S)))
                (sym (EST.substTyNF-bridge (normalizeTy pairTy) S)))
              (<:ₜ-refl (normalTyOf (pairNf (normalizeTy (SessLin S)) (dualSessNf (normalizeTy S)))))
        }
  preserve⇒
    (T-TApp {m = Un} (T-Val (TV-Const ())))
    (Act-New {S = S})
    lbl ex disj
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
        {U = send1Nf (normalizeTy T)}
        Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val TV-Send₁)
        (subst
          (λ X → normalTyOf (send1Nf (normalizeTy T)) <:ₜ normalTyOf X)
          (trans (send₁-shapeNF {T = T}) (sym (send₁-ty d)))
          (<:ₜ-refl (normalTyOf (send1Nf (normalizeTy T)))))
  preserve⇒
    (T-TApp {m = Un} (T-Val (TV-Const ())))
    (Act-Send₁ {T = T})
    lbl ex disj
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
        {U = sendNf (normalizeTy T) (normalizeTy S)}
        Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val TV-Send₂)
        (subst
          (λ X → normalTyOf (sendNf (normalizeTy T) (normalizeTy S)) <:ₜ normalTyOf X)
          (trans (send₂-shapeNF {T = T} {S = S}) (sym (send₂-ty d)))
          (<:ₜ-refl (normalTyOf (sendNf (normalizeTy T) (normalizeTy S)))))
  preserve⇒
    {pk = KT} {mult = Lin}
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {T = R}
    (T-App {m = Lin}
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
    {e₁ = E-App (E-Val (V-Select₂ vₛ i Pₛ Sₛ)) (E-Val (V-Var x))}
    {e₂ = E-Val (V-Var x)}
    (T-App {m = Un} (T-Val ()) _)
    (Act-Sel {v = vₛ} {i = i} {P = Pₛ} {S = Sₛ} {x = x})
    lbl ex disj
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
    (T-TApp {m = Un} (T-Val (TV-Const ())))
    Act-Select₁
    lbl ex disj
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
    (T-TApp {m = Un} (T-Val ()))
    Act-Select₂
    lbl ex disj
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
        {U = receive1Nf (normalizeTy T)}
        Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val TV-Receive₁)
        (subst
          (λ X → normalTyOf (receive1Nf (normalizeTy T)) <:ₜ normalTyOf X)
          (trans (receive₁-shapeNF {T = T}) (sym (receive₁-ty d)))
          (<:ₜ-refl (normalTyOf (receive1Nf (normalizeTy T)))))
  preserve⇒
    (T-TApp {m = Un} (T-Val (TV-Const ())))
    (Act-Receive₁ {T = T})
    lbl ex disj
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
        {U = receiveNf (normalizeTy T) (normalizeTy S)}
        Ctx-β lbl ex (beta-compatible lbl ex)
        (T-Val TV-Receive₂)
        (subst
          (λ X → normalTyOf (receiveNf (normalizeTy T) (normalizeTy S)) <:ₜ normalTyOf X)
          (trans (receive₂-shapeNF {T = T} {S = S}) (sym (receive₂-ty d)))
          (<:ₜ-refl (normalTyOf (receiveNf (normalizeTy T) (normalizeTy S)))))
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
    {e₁ = E-App (E-Val (V-Send₂ Tᵣ Sᵣ)) (E-Val (V-Pair v (V-Var x)))}
    {e₂ = E-Val (V-Var x)}
    {T = R}
    (T-App {m = Lin} {T = A} {U = R}
      (T-Val vr)
      (T-Check {U = U} (T-Val vv) sub))
    (Act-Send {T = Tᵣ} {S = Sᵣ} {x = x} {v = v})
    lbl ex disj =
    preserve⇒-send vr vv sub lbl ex disj
  preserve⇒
    {e₁ = E-App (E-Val (V-Send₂ Tᵣ Sᵣ)) (E-Val (V-Pair v (V-Var x)))}
    {e₂ = E-Val (V-Var x)}
    (T-App {m = Un} (T-Val ()) _)
    (Act-Send {T = Tᵣ} {S = Sᵣ} {x = x} {v = v})
    lbl ex disj
  preserve⇒ {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    (T-Pair {T = T} {U = U} (T-Val du) (T-Val dv))
    Act-PairV lbl@(Label-β _ auv) ex _ =
    basePres {Γ₀ = Γ₀} {Γ₂ = Γ₂} {U = pairNf T U} Ctx-β lbl ex (beta-compatible lbl ex)
      (T-Val (TV-Pair du dv)) (<:ₜ-refl (normalTyOf (pairNf T U)))
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    {e₁ = E-App (E-Val (V-Const C-Close)) (E-Val (V-Var x))}
    {e₂ = E-Val (V-Const C-Unit)}
    (T-App {m = Lin} {T = A} {U = R} (T-Val vr) (T-Check (T-Val {T = U} (TV-Var-Lin take)) sub))
    Act-Close lbl@(Label-Close _ _) ex _ =
    preserve⇒-close vr take sub lbl ex
  preserve⇒
    {e₁ = E-App (E-Val (V-Const C-Close)) (E-Val (V-Var x))}
    {e₂ = E-Val (V-Const C-Unit)}
    (T-App {m = Un} (T-Val (TV-Const ())) _)
    Act-Close lbl ex disj
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-TApp e₁ Uty}
    {ℓ = ℓ}
    (T-TApp {Γ₁ = Γ₂} {Γ₂ = Γ₃} {K = K} {m = m} {T = Tₚ} {U = Uty} d₁)
    (Act-TAppE {Θ = Θ} {K = K} {e₁ = e₁} {e₂ = e₂} {T = Uty} step)
    lbl ex disj
    with preserve⇒ d₁ step lbl ex disj
  ... | ps
    with poly-subtype-inversion {K = K} {T = Tₚ} (PresSynth.subtype ps)
  ... | Tₚ′ , eqPoly , Tₚ′<:Tₚ =
    record
      { Gf = PresSynth.Gf ps
      ; Γ₀′ = PresSynth.Γ₀′ ps
      ; Γ₁ = PresSynth.Γ₁ ps
      ; Γ₁′ = PresSynth.Γ₁′ ps
      ; U = substNFTy Tₚ′ (normalizeTy Uty)
      ; src-remove = PresSynth.src-remove ps
      ; dst-remove = PresSynth.dst-remove ps
      ; ctx-step = PresSynth.ctx-step ps
      ; compat = PresSynth.compat ps
      ; synth =
          T-TApp {T = Tₚ′} {U = Uty}
            (subst
              (λ X → PresSynth.Γ₁ ps ⊢ e₂ ⇒ X ⊣ extendUsed Θ Γ₃)
              eqPoly
              (PresSynth.synth ps))
      ; subtype =
          subst-preserves-<:ₜ
            {U = normalizeTy Uty}
            Tₚ′<:Tₚ
      }
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-App e₁ e₃}
    {T = V} {ℓ = ℓ}
    (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V} d₁ (T-Check pArg subArg))
    (Act-AppL {Θ = Θ} {e₁ = e₁} {e₂ = e₂} {e₃ = e₃} step)
    lbl ex disj
    with preserve⇒ d₁ step lbl ex disj
  ... | ps
    with arrow-subtype-inversion {A = A} {V = V} (PresSynth.subtype ps)
  ... | A′ , V′ , eqU , A<:A′ , V′<:V =
    let
      pArg′ : extendUsed Θ Γ₂ ⊢ ES.weakenExprBy (length Θ) e₃ ⇒ _ ⊣ extendUsed Θ Γ₃
      pArg′ =
        subst
          (λ G₂′ → G₂′ ⊢ ES.weakenExprBy (length Θ) e₃ ⇒ _ ⊣ extendUsed Θ Γ₃)
          (extendUsed-eq Θ Γ₂)
          (subst
            (λ G₃′ → extendUsed Θ Γ₂ ⊢ ES.weakenExprBy (length Θ) e₃ ⇒ _ ⊣ G₃′)
            (extendUsed-eq Θ Γ₃)
            (weaken-synth {Θ = Θ} pArg))
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
              (λ X → PresSynth.Γ₁ ps ⊢ e₂ ⇒ X ⊣ extendUsed Θ Γ₂)
              eqU
              (PresSynth.synth ps))
            (T-Check pArg′
              (<:ₜ-trans subArg A<:A′))
      ; subtype = V′<:V
      }
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-Pair e₁ e₃}
    {ℓ = ℓ}
    (T-Pair {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = Tₚ} {U = Uₚ} d₁ d₂)
    (Act-PairL {Θ = Θ} {e₁ = e₁} {e₂ = e₂} {e₃ = e₃} step)
    lbl ex disj
    with preserve⇒ d₁ step lbl ex disj
  ... | ps =
    let
      d₂′ : extendUsed Θ Γ₂ ⊢ ES.weakenExprBy (length Θ) e₃ ⇒ Uₚ ⊣ extendUsed Θ Γ₃
      d₂′ =
        subst
          (λ G₂′ → G₂′ ⊢ ES.weakenExprBy (length Θ) e₃ ⇒ _ ⊣ extendUsed Θ Γ₃)
          (extendUsed-eq Θ Γ₂)
          (subst
            (λ G₃′ → extendUsed Θ Γ₂ ⊢ ES.weakenExprBy (length Θ) e₃ ⇒ _ ⊣ G₃′)
            (extendUsed-eq Θ Γ₃)
            (weaken-synth {Θ = Θ} d₂))
    in
    record
      { Gf = PresSynth.Gf ps
      ; Γ₀′ = PresSynth.Γ₀′ ps
      ; Γ₁ = PresSynth.Γ₁ ps
      ; Γ₁′ = PresSynth.Γ₁′ ps
      ; U = pairNf (PresSynth.U ps) Uₚ
      ; src-remove = PresSynth.src-remove ps
      ; dst-remove = PresSynth.dst-remove ps
      ; ctx-step = PresSynth.ctx-step ps
      ; compat = PresSynth.compat ps
      ; synth = T-Pair (PresSynth.synth ps) d₂′
      ; subtype =
          <:ₜ-pair
            (PresSynth.subtype ps)
            (<:ₜ-refl (normalTyOf Uₚ))
      }
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-LetPair e₁ e₃}
    {T = V} {ℓ = ℓ}
    (T-LetPair {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = Tₚ} {U = Uₚ} {V = V} d₁ d₂)
    (Act-LetPairE {Θ = Θ} {e₁ = e₁} {e₂ = e₂} {e₃ = e₃} step)
    lbl ex disj
    with preserve⇒ d₁ step lbl ex disj
  ... | ps
    with pair-subtype-inversion {T = Tₚ} {U = Uₚ} (PresSynth.subtype ps)
  ... | Tₚ′ , Uₚ′ , eqPair , Tₚ′<:Tₚ , Uₚ′<:Uₚ
    with letpair-body-pres
           {Θ = Θ}
           {T = Tₚ} {U = Uₚ}
           {T′ = Tₚ′} {U′ = Uₚ′}
           Tₚ′<:Tₚ Uₚ′<:Uₚ d₂
  ... | V′ , d₂′ , V′<:V =
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
          T-LetPair
            (subst
              (λ X → PresSynth.Γ₁ ps ⊢ e₂ ⇒ X ⊣ extendUsed Θ Γ₂)
              eqPair
              (PresSynth.synth ps))
            d₂′
      ; subtype = V′<:V
      }
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-LetUnit e₁ e₃}
    {T = T} {ℓ = ℓ}
    (T-LetUnit {Γ₂ = Γ₂} {Γ₃ = Γ₃} d₁ d₂)
    (Act-LetUnitE {Θ = Θ} {e₁ = e₁} {e₂ = e₂} {e₃ = e₃} step)
    lbl ex disj
    with preserve⇐ {T = unitConstNf} d₁ step lbl ex disj
  ... | pc =
    let
      d₂′ : extendUsed Θ Γ₂ ⊢ ES.weakenExprBy (length Θ) e₃ ⇒ T ⊣ extendUsed Θ Γ₃
      d₂′ =
        subst
          (λ G₂′ → G₂′ ⊢ ES.weakenExprBy (length Θ) e₃ ⇒ _ ⊣ extendUsed Θ Γ₃)
          (extendUsed-eq Θ Γ₂)
          (subst
            (λ G₃′ → extendUsed Θ Γ₂ ⊢ ES.weakenExprBy (length Θ) e₃ ⇒ _ ⊣ G₃′)
            (extendUsed-eq Θ Γ₃)
            (weaken-synth {Θ = Θ} d₂))
    in
    record
      { Gf = PresCheck.Gf pc
      ; Γ₀′ = PresCheck.Γ₀′ pc
      ; Γ₁ = PresCheck.Γ₁ pc
      ; Γ₁′ = PresCheck.Γ₁′ pc
      ; U = T
      ; src-remove = PresCheck.src-remove pc
      ; dst-remove = PresCheck.dst-remove pc
      ; ctx-step = PresCheck.ctx-step pc
      ; compat = PresCheck.compat pc
      ; synth = T-LetUnit (PresCheck.check pc) d₂′
      ; subtype = <:ₜ-refl (normalTyOf T)
      }
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-Pair (E-Val v) e₁}
    {ℓ = ℓ}
    (T-Pair {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = Tₚ} {U = Uₚ}
      (T-Val dv)
      d₂)
    (Act-PairR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@(Ex-RecvVal {x = x} {v = vᵣ} _ _ _) disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-pairR-core
        r
        dv′
        au
        d₂
        step
        lbl
        ex
        disj
        (pairR-extract-disjoint-recv
          r
          d₂
          step
          ex)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-Pair (E-Val v) e₁}
    {ℓ = ℓ}
    (T-Pair {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = Tₚ} {U = Uₚ}
      (T-Val dv)
      d₂)
    (Act-PairR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@Ex-β disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-pairR-core
        r
        dv′
        au
        d₂
        step
        lbl
        ex
        disj
        (remove-allused-disjoint r)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-Pair (E-Val v) e₁}
    {ℓ = ℓ}
    (T-Pair {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = Tₚ} {U = Uₚ}
      (T-Val dv)
      d₂)
    (Act-PairR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@Ex-Fork disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-pairR-core
        r
        dv′
        au
        d₂
        step
        lbl
        ex
        disj
        (remove-allused-disjoint r)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-Pair (E-Val v) e₁}
    {ℓ = ℓ}
    (T-Pair {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = Tₚ} {U = Uₚ}
      (T-Val dv)
      d₂)
    (Act-PairR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@Ex-New disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-pairR-core
        r
        dv′
        au
        d₂
        step
        lbl
        ex
        disj
        (remove-allused-disjoint r)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-Pair (E-Val v) e₁}
    {ℓ = ℓ}
    (T-Pair {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = Tₚ} {U = Uₚ}
      (T-Val dv)
      d₂)
    (Act-PairR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@Ex-RecvLab disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-pairR-core
        r
        dv′
        au
        d₂
        step
        lbl
        ex
        disj
        (remove-allused-disjoint r)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-Pair (E-Val v) e₁}
    {ℓ = ℓ}
    (T-Pair {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = Tₚ} {U = Uₚ}
      (T-Val dv)
      d₂)
    (Act-PairR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@(Ex-SendVal _ _ _ _) disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-pairR-core
        r
        dv′
        au
        d₂
        step
        lbl
        ex
        disj
        (pairR-extract-disjoint-send
          r
          disj
          d₂
          step
          lbl
          ex)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-Pair (E-Val v) e₁}
    {ℓ = ℓ}
    (T-Pair {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = Tₚ} {U = Uₚ}
      (T-Val dv)
      d₂)
    (Act-PairR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl@(Label-SendLab {v = vₗ} {P = Pₗ} {S = Sₗ} _ _)
    ex@(Ex-SendLab {i = i} _ _) disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-pairR-core
        r
        dv′
        au
        d₂
        step
        lbl
        ex
        disj
        (pairR-extract-disjoint-sendlab
          {v = vₗ}
          {P = Pₗ}
          {S = Sₗ}
          r
          d₂
          step
          lbl
          ex)
  preserve⇒
    {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    {e₁ = E-Pair (E-Val v) e₁}
    {ℓ = ℓ}
    (T-Pair {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = Tₚ} {U = Uₚ}
      (T-Val dv)
      d₂)
    (Act-PairR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
    lbl ex@Ex-Close disj
    with strip-value dv
  ... | G , G′ , r , dv′ , au
    = preserve⇒-pairR-core
        r
        dv′
        au
        d₂
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
    (Act-AppR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
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
    (Act-AppR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
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
    (Act-AppR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
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
    (Act-AppR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
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
    (Act-AppR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
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
    (Act-AppR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
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
    (Act-AppR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
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
    (Act-AppR {Θ = Θ} {v = v} {e₁ = e₁} {e₂ = e₂} step)
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
  preserve⇐ :
    ∀ {n Θ pk mult}
      {Γ₀ : Ctx [] n} {Γ₂ : Ctx [] n}
      {Γin Γv : Ctx [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] (length Θ + n)}
      {T : NfTy [] (KV pk mult)} {ℓ : Label n Θ}
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
