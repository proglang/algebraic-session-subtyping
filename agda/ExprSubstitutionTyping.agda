module ExprSubstitutionTyping where

open import Data.Fin using (Fin)
import Data.Fin.Subset as Subset
open import Data.List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

import Duality as D
open import Kinds
open import Kits
open import Variance using (Variance)
open import Types using
  ( Ty; Ty-Syntax; Ty-Traversal; T-Var; T-Base; T-Poly; T-Msg; T-Up
  ; nf
  ; nf-complete; nf-sound+; fusion
  )
open import TypesProtocolConstructors using (SelectConstTy; SelectTy1; SelectTy2)
open import AlgorithmicNFSubtyping using (_<:ₜ_; <:ₜ-trans)
open import AlgorithmicNFSubstitution using () renaming (subst-preserves-<:ₜ to substNF-preserves-<:ₜ)
open import NormalTypesSubstitution using (substNFTy; substNFTy-single-sound)
open import SubstitutionSubtyping using (subst-preserves-≡c)
open import ExprSyntax using
  ( Expr; Value; E-App; E-LetPair; E-TApp; E-Val
  ; V-Abs; V-Rec; V-TAbs; V-Var
  ; V-Receive₁; V-Receive₂
  ; V-Send₁; V-Send₂; V-Send₃
  ; V-Select₁; V-Select₂
  ; C-Select
  )
open import ExprSubstitution
open import ExprNormalTyping

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (⋯-id)
open CTraversal record { fusion = fusion }

substTyNfWith : ∀ {Δ Δ′ K} → NfTy Δ K → Δ →ₛ Δ′ → NfTy Δ′ K
substTyNfWith T ϕ = normalizeTy (⌞ T ⌟ ⋯ ϕ)

substTyBindingWith : ∀ {Δ Δ′} → Binding Δ → Δ →ₛ Δ′ → Binding Δ′
substTyBindingWith (B-Lin T) ϕ = B-Lin (substTyNfWith T ϕ)
substTyBindingWith (B-Un T) ϕ = B-Un (substTyNfWith T ϕ)
substTyBindingWith B-Used ϕ = B-Used

substTyCtxWith : ∀ {Δ Δ′ n} → Ctx Δ n → Δ →ₛ Δ′ → Ctx Δ′ n
substTyCtxWith ∅ ϕ = ∅
substTyCtxWith (b ▻ Γ) ϕ = substTyBindingWith b ϕ ▻ substTyCtxWith Γ ϕ

substTyNf : ∀ {Δ K K′} → NfTy (K ∷ Δ) K′ → Ty Δ K → NfTy Δ K′
substTyNf T U = substTyNfWith T ⦅ U ⦆ₛ

substTyBinding : ∀ {Δ K} → Binding (K ∷ Δ) → Ty Δ K → Binding Δ
substTyBinding b U = substTyBindingWith b ⦅ U ⦆ₛ

substTyCtx : ∀ {Δ n K} → Ctx (K ∷ Δ) n → Ty Δ K → Ctx Δ n
substTyCtx Γ U = substTyCtxWith Γ ⦅ U ⦆ₛ

substTy-preserves-∋ᵘ :
  ∀ {Δ n K K′} {Γ : Ctx (K ∷ Δ) n} {x : Fin n} {T : NfTy (K ∷ Δ) K′} {U : Ty Δ K}
  → Γ ∋ᵘ x ∶ T
  → substTyCtx Γ U ∋ᵘ x ∶ substTyNf T U
substTy-preserves-∋ᵘ hereᵘ = hereᵘ
substTy-preserves-∋ᵘ (thereᵘˡ p) = thereᵘˡ (substTy-preserves-∋ᵘ p)
substTy-preserves-∋ᵘ (thereᵘᵘ p) = thereᵘᵘ (substTy-preserves-∋ᵘ p)
substTy-preserves-∋ᵘ (thereᵘ✖ p) = thereᵘ✖ (substTy-preserves-∋ᵘ p)

substTy-preserves-⊢ˡ :
  ∀ {Δ n K K′} {Γ₁ Γ₂ : Ctx (K ∷ Δ) n} {x : Fin n} {T : NfTy (K ∷ Δ) K′} {U : Ty Δ K}
  → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂
  → substTyCtx Γ₁ U ⊢ˡ x ∶ substTyNf T U ⊣ substTyCtx Γ₂ U
substTy-preserves-⊢ˡ take-here = take-here
substTy-preserves-⊢ˡ (take-thereˡ p) = take-thereˡ (substTy-preserves-⊢ˡ p)
substTy-preserves-⊢ˡ (take-thereᵘ p) = take-thereᵘ (substTy-preserves-⊢ˡ p)
substTy-preserves-⊢ˡ (take-there✖ p) = take-there✖ (substTy-preserves-⊢ˡ p)

postulate
  BranchJoin-subst :
    ∀ {Δ K k} {ss : Subset.Subset k} {ne : Subset.Nonempty ss}
      {V : (i : Fin k) → i Subset.∈ ss → NfTy (K ∷ Δ) TLin}
      {U : NfTy (K ∷ Δ) TLin} {W : Ty Δ K}
    → BranchJoin {ss = ss} {ne = ne} V U
    → BranchJoin {ss = ss} {ne = ne} (λ i i∈ → substTyNf (V i i∈) W) (substTyNf U W)

  substTyWith-preserves-value :
    ∀ {Δ Δ′ n K} {Γ₁ Γ₂ : Ctx Δ n}
      {v : Value Δ n} {T : NfTy Δ K} {ϕ : Δ →ₛ Δ′}
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
    → substTyCtxWith Γ₁ ϕ ⊢ᵥ substTyValueWith ϕ v ⇒ substTyNfWith T ϕ ⊣ substTyCtxWith Γ₂ ϕ

  substTy-preserves-synth-tapp :
    ∀ {Δ n K K′ m} {Γ₁ Γ₂ : Ctx (K ∷ Δ) n}
      {e : Expr (K ∷ Δ) n} {T : NfTy (K′ ∷ K ∷ Δ) (KV KT m)} {U : Ty (K ∷ Δ) K′} {W : Ty Δ K}
    → Γ₁ ⊢ e ⇒ polyNf T ⊣ Γ₂
    → substTyCtx Γ₁ W ⊢ E-TApp (substTyExpr e W) (U ⋯ ⦅ W ⦆ₛ)
         ⇒ substTyNf (normalizeTy (⌞ T ⌟ ⋯ ⦅ U ⦆ₛ)) W
         ⊣ substTyCtx Γ₂ W

  substTy-preserves-synth-letpair :
    ∀ {Δ n K pk₁ pk₂} {Γ₁ Γ₂ Γ₃ : Ctx (K ∷ Δ) n}
      {T : NfTy (K ∷ Δ) (KV pk₁ Lin)} {U : NfTy (K ∷ Δ) (KV pk₂ Lin)}
      {V : NfTy (K ∷ Δ) TLin} {e₁ : Expr (K ∷ Δ) n} {e₂ : Expr (K ∷ Δ) (suc (suc n))}
      {W : Ty Δ K}
    → Γ₁ ⊢ e₁ ⇒ pairNf T U ⊣ Γ₂
    → (T ∷ˡ (U ∷ˡ Γ₂)) ⊢ e₂ ⇒ V ⊣ used∷ (used∷ Γ₃)
    → substTyCtx Γ₁ W ⊢ E-LetPair (substTyExpr e₁ W) (substTyExpr e₂ W)
         ⇒ substTyNf V W ⊣ substTyCtx Γ₃ W

substTy-linArrNf :
  ∀ {Δ K} (T U : NfTy (K ∷ Δ) TLin) (W : Ty Δ K)
  → substTyNf (linArrNf T U) W ≡ linArrNf (substTyNf T W) (substTyNf U W)
substTy-linArrNf T U W = refl

substTy-pairNf :
  ∀ {Δ K pk₁ pk₂ m}
    (T : NfTy (K ∷ Δ) (KV pk₁ m))
    (U : NfTy (K ∷ Δ) (KV pk₂ m))
    (W : Ty Δ K)
  → substTyNf (pairNf T U) W ≡ pairNf (substTyNf T W) (substTyNf U W)
substTy-pairNf T U W = refl

postulate
  substTyWith-normalizeTy :
    ∀ {Δ Δ′ K} (T : Ty Δ K) (ϕ : Δ →ₛ Δ′)
    → substTyNfWith (normalizeTy T) ϕ ≡ normalizeTy (T ⋯ ϕ)

substTy-normalizeTy :
  ∀ {Δ K K′} (T : Ty (K ∷ Δ) K′) (U : Ty Δ K)
  → substTyNf (normalizeTy T) U ≡ normalizeTy (T ⋯ ⦅ U ⦆ₛ)
substTy-normalizeTy T U = substTyWith-normalizeTy T ⦅ U ⦆ₛ

_≈ₛ_ : ∀ {Δ₁ Δ₂} → (Δ₁ →ₛ Δ₂) → (Δ₁ →ₛ Δ₂) → Set
ϕ ≈ₛ ψ = ∀ K → (x : K ∈ _) → ϕ K x Types.≡c ψ K x

lift-≈ₛ :
  ∀ {Δ₁ Δ₂ K} {ϕ ψ : Δ₁ →ₛ Δ₂}
  → ϕ ≈ₛ ψ
  → (ϕ ↑ₛ K) ≈ₛ (ψ ↑ₛ K)
lift-≈ₛ rel K′ (here refl) = Types.≡c-refl
lift-≈ₛ rel K′ (there x) = subst-preserves-≡c (rel K′ x) (weakenᵣ _)

t-dual-preserves-≡c :
  ∀ {Δ m} {T U : Ty Δ (KV KS m)}
  → T Types.≡c U
  → Types.t-dual D.D-S T Types.≡c Types.t-dual D.D-S U
t-dual-preserves-≡c Types.≡c-refl = Types.≡c-refl
t-dual-preserves-≡c (Types.≡c-symm eq) =
  Types.≡c-symm (t-dual-preserves-≡c eq)
t-dual-preserves-≡c (Types.≡c-trns eq₁ eq₂) =
  Types.≡c-trns (t-dual-preserves-≡c eq₁) (t-dual-preserves-≡c eq₂)
t-dual-preserves-≡c (Types.≡c-sub (≤k-step ≤p-refl x) eq) =
  Types.≡c-sub (≤k-step ≤p-refl x) (t-dual-preserves-≡c eq)
t-dual-preserves-≡c
  {T = Types.T-Dual D.D-S (Types.T-Sub (≤k-step ≤p-refl x) T)}
  Types.≡c-sub-dual = Types.≡c-refl
t-dual-preserves-≡c
  {T = Types.T-Dual D.D-S (Types.T-Dual D.D-S U)}
  (Types.≡c-dual-dual D.D-S) =
  Types.dual-tinv U
t-dual-preserves-≡c Types.≡c-dual-end = Types.≡c-refl
t-dual-preserves-≡c {T = Types.T-Dual D.D-S (Types.T-Msg p T S)} Types.≡c-dual-msg
  rewrite D.invert-involution {p} =
    Types.≡c-msg Types.≡c-refl Types.≡c-refl
t-dual-preserves-≡c {T = Types.T-Msg p T S} (Types.≡c-msg-minus {p = p}) =
  Types.≡c-msg-minus {p = D.invert p}
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
subst-preserves-≡c-pointwise (Types.T-Dual D.D-S T) rel =
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

singleSubst-≈ₛ :
  ∀ {Δ K} {U V : Ty Δ K}
  → U Types.≡c V
  → (⦅ U ⦆ₛ) ≈ₛ (⦅ V ⦆ₛ)
singleSubst-≈ₛ eq K (here refl) = eq
singleSubst-≈ₛ eq K (there x) = Types.≡c-refl

postulate
  substTyNF-bridge :
    ∀ {Δ K pk m} (T : NfTy (K ∷ Δ) (KV pk m)) (U : Ty Δ K)
    → substNFTy T (normalizeTy U) ≡ substTyNf T U

substTy-preserves-<:ₜ :
  ∀ {Δ K pk m} {T U : NfTy (K ∷ Δ) (KV pk m)} {V : Ty Δ K}
  → U <:ₜ T
  → substTyNf U V <:ₜ substTyNf T V
substTy-preserves-<:ₜ {T = T} {U = U} {V = V} q
  rewrite sym (substTyNF-bridge U V)
        | sym (substTyNF-bridge T V)
  = substNF-preserves-<:ₜ {U = normalizeTy V} q

postulate
  substTyWith-wkNfTy :
    ∀ {Δ Δ′ K K′} (T : NfTy Δ K) (ϕ : Δ →ₛ Δ′)
    → substTyNfWith (wkNfTy {K′ = K′} T) (ϕ ↑ₛ K′) ≡ wkNfTy {K′ = K′} (substTyNfWith T ϕ)

  substTyWith-wkBinding :
    ∀ {Δ Δ′ K} (b : Binding Δ) (ϕ : Δ →ₛ Δ′)
    → substTyBindingWith (wkBinding {K = K} b) (ϕ ↑ₛ K) ≡ wkBinding {K = K} (substTyBindingWith b ϕ)

  substTyWith-wkCtx :
    ∀ {Δ Δ′ n K} (Γ : Ctx Δ n) (ϕ : Δ →ₛ Δ′)
    → substTyCtxWith (wkCtx {K = K} Γ) (ϕ ↑ₛ K) ≡ wkCtx {K = K} (substTyCtxWith Γ ϕ)

  substTyWith-polyNf :
    ∀ {Δ Δ′ K m} (T : NfTy (K ∷ Δ) (KV KT m)) (ϕ : Δ →ₛ Δ′)
    → substTyNfWith (polyNf T) ϕ ≡ polyNf (substTyNfWith T (ϕ ↑ₛ K))

  substTy-SelectConstTy :
    ∀ {Δ K k} {v : Variance} {i : Fin k} (U : Ty Δ K)
    → (SelectConstTy {Δ = K ∷ Δ} v i) ⋯ ⦅ U ⦆ₛ ≡ SelectConstTy {Δ = Δ} v i

  substTy-SelectTy1 :
    ∀ {Δ K k} {v : Variance} {i : Fin k} (P : Ty (K ∷ Δ) KP) (U : Ty Δ K)
    → (SelectTy1 v i P) ⋯ ⦅ U ⦆ₛ ≡ SelectTy1 v i (P ⋯ ⦅ U ⦆ₛ)

  substTy-SelectTy2 :
    ∀ {Δ K k} {v : Variance} {i : Fin k} (P : Ty (K ∷ Δ) KP) (S : Ty (K ∷ Δ) SLin) (U : Ty Δ K)
    → (SelectTy2 v i P S) ⋯ ⦅ U ⦆ₛ ≡ SelectTy2 v i (P ⋯ ⦅ U ⦆ₛ) (S ⋯ ⦅ U ⦆ₛ)

  ConstTy-select-subst :
    ∀ {Δ K k} {v : Variance} {i : Fin k} {U : Ty Δ K}
    → ConstTy (C-Select v i) (substTyNf (normalizeTy (SelectConstTy {Δ = K ∷ Δ} v i)) U)

substTy-preserves-value-tabs :
  ∀ {Δ n K K′ m} {Γ₁ Γ₂ : Ctx (K ∷ Δ) n}
    {v : Value (K′ ∷ K ∷ Δ) n} {T : NfTy (K′ ∷ K ∷ Δ) (KV KT m)} {U : Ty Δ K}
  → wkCtx {K = K′} Γ₁ ⊢ᵥ v ⇒ T ⊣ wkCtx Γ₂
  → substTyCtx Γ₁ U ⊢ᵥ V-TAbs K′ (substTyValueWith (⦅ U ⦆ₛ ↑ₛ K′) v)
       ⇒ substTyNf (polyNf T) U ⊣ substTyCtx Γ₂ U
substTy-preserves-value-tabs {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = v} {T = T} {U = U} p =
  Eq.subst
    (λ X → substTyCtx Γ₁ U ⊢ᵥ V-TAbs _ (substTyValueWith (⦅ U ⦆ₛ ↑ₛ _) v) ⇒ X ⊣ substTyCtx Γ₂ U)
    (Eq.sym (substTyWith-polyNf T ⦅ U ⦆ₛ))
    (TV-TAbs premise₂)
  where
  premise₀ :
    substTyCtxWith (wkCtx Γ₁) (⦅ U ⦆ₛ ↑ₛ _) ⊢ᵥ
      substTyValueWith (⦅ U ⦆ₛ ↑ₛ _) v ⇒
      substTyNfWith T (⦅ U ⦆ₛ ↑ₛ _) ⊣
      substTyCtxWith (wkCtx Γ₂) (⦅ U ⦆ₛ ↑ₛ _)
  premise₀ = substTyWith-preserves-value p

  premise₁ :
    wkCtx (substTyCtx Γ₁ U) ⊢ᵥ
      substTyValueWith (⦅ U ⦆ₛ ↑ₛ _) v ⇒
      substTyNfWith T (⦅ U ⦆ₛ ↑ₛ _) ⊣
      substTyCtxWith (wkCtx Γ₂) (⦅ U ⦆ₛ ↑ₛ _)
  premise₁ =
    Eq.subst
      (λ X → X ⊢ᵥ
        substTyValueWith (⦅ U ⦆ₛ ↑ₛ _) v ⇒
        substTyNfWith T (⦅ U ⦆ₛ ↑ₛ _) ⊣
        substTyCtxWith (wkCtx Γ₂) (⦅ U ⦆ₛ ↑ₛ _))
      (substTyWith-wkCtx {K = _} Γ₁ ⦅ U ⦆ₛ)
      premise₀

  premise₂ :
    wkCtx (substTyCtx Γ₁ U) ⊢ᵥ
      substTyValueWith (⦅ U ⦆ₛ ↑ₛ _) v ⇒
      substTyNfWith T (⦅ U ⦆ₛ ↑ₛ _) ⊣
      wkCtx (substTyCtx Γ₂ U)
  premise₂ =
    Eq.subst
      (λ X → wkCtx (substTyCtx Γ₁ U) ⊢ᵥ
        substTyValueWith (⦅ U ⦆ₛ ↑ₛ _) v ⇒
        substTyNfWith T (⦅ U ⦆ₛ ↑ₛ _) ⊣ X)
      (substTyWith-wkCtx {K = _} Γ₂ ⦅ U ⦆ₛ)
      premise₁

substTy-ReceiveTy1 :
  ∀ {Δ K} (T : Ty (K ∷ Δ) TLin) (U : Ty Δ K)
  → (ReceiveTy1 T) ⋯ ⦅ U ⦆ₛ ≡ ReceiveTy1 (T ⋯ ⦅ U ⦆ₛ)
substTy-ReceiveTy1 T U =
  cong (T-Poly SLin)
    (cong (λ X → ReceiveTy X (T-Var (here refl)))
      (sym (⋯-↑-wk T ⦅ U ⦆ₛ SLin)))

substTy-SendTy1 :
  ∀ {Δ K} (T : Ty (K ∷ Δ) TLin) (U : Ty Δ K)
  → (SendTy1 T) ⋯ ⦅ U ⦆ₛ ≡ SendTy1 (T ⋯ ⦅ U ⦆ₛ)
substTy-SendTy1 T U =
  cong (T-Poly SLin)
    (cong (λ X → SendTy X (T-Var (here refl)))
      (sym (⋯-↑-wk T ⦅ U ⦆ₛ SLin)))

postulate
  substTy-preserves-value-receive₁ :
    ∀ {Δ n K} {Γ₁ : Ctx (K ∷ Δ) n} {T : Ty (K ∷ Δ) TLin} {U : Ty Δ K}
    → substTyCtx Γ₁ U ⊢ᵥ V-Receive₁ (T ⋯ ⦅ U ⦆ₛ)
         ⇒ substTyNf (normalizeTy (ReceiveTy1 T)) U ⊣ substTyCtx Γ₁ U

postulate
  substTy-preserves-value-send₁ :
    ∀ {Δ n K} {Γ₁ : Ctx (K ∷ Δ) n} {T : Ty (K ∷ Δ) TLin} {U : Ty Δ K}
    → substTyCtx Γ₁ U ⊢ᵥ V-Send₁ (T ⋯ ⦅ U ⦆ₛ)
         ⇒ substTyNf (normalizeTy (SendTy1 T)) U ⊣ substTyCtx Γ₁ U

postulate
  substTy-preserves-value-receive₂ :
    ∀ {Δ n K} {Γ₁ : Ctx (K ∷ Δ) n} {T : Ty (K ∷ Δ) TLin} {S : Ty (K ∷ Δ) SLin} {U : Ty Δ K}
    → substTyCtx Γ₁ U ⊢ᵥ V-Receive₂ (T ⋯ ⦅ U ⦆ₛ) (S ⋯ ⦅ U ⦆ₛ)
         ⇒ substTyNf (normalizeTy (ReceiveTy T S)) U ⊣ substTyCtx Γ₁ U

postulate
  substTy-preserves-value-send₂ :
    ∀ {Δ n K} {Γ₁ : Ctx (K ∷ Δ) n} {T : Ty (K ∷ Δ) TLin} {S : Ty (K ∷ Δ) SLin} {U : Ty Δ K}
    → substTyCtx Γ₁ U ⊢ᵥ V-Send₂ (T ⋯ ⦅ U ⦆ₛ) (S ⋯ ⦅ U ⦆ₛ)
         ⇒ substTyNf (normalizeTy (SendTy T S)) U ⊣ substTyCtx Γ₁ U

postulate
  substTy-preserves-value-select₁ :
    ∀ {Δ n K k} {Γ₁ : Ctx (K ∷ Δ) n} {v : Variance} {i : Fin k} {P : Ty (K ∷ Δ) KP} {U : Ty Δ K}
    → substTyCtx Γ₁ U ⊢ᵥ V-Select₁ v i (P ⋯ ⦅ U ⦆ₛ)
         ⇒ substTyNf (normalizeTy (SelectTy1 v i P)) U ⊣ substTyCtx Γ₁ U

postulate
  substTy-preserves-value-select₂ :
    ∀ {Δ n K k} {Γ₁ : Ctx (K ∷ Δ) n}
      {v : Variance} {i : Fin k} {P : Ty (K ∷ Δ) KP} {S : Ty (K ∷ Δ) SLin} {U : Ty Δ K}
    → substTyCtx Γ₁ U ⊢ᵥ V-Select₂ v i (P ⋯ ⦅ U ⦆ₛ) (S ⋯ ⦅ U ⦆ₛ)
         ⇒ substTyNf (normalizeTy (SelectTy2 v i P S)) U ⊣ substTyCtx Γ₁ U

postulate
  ConstTy-subst :
    ∀ {Δ K c K′} {T : NfTy (K ∷ Δ) K′} {U : Ty Δ K}
    → ConstTy c T
    → ConstTy c (substTyNf T U)

postulate

  subst2-preserves-synth :
    ∀ {Δ n K pk₁ pk₂} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx Δ n}
      {T : NfTy Δ (KV pk₁ Lin)} {U : NfTy Δ (KV pk₂ Lin)}
      {u v : Value Δ n} {e : Expr Δ (Data.Nat.suc (Data.Nat.suc n))}
      {V : NfTy Δ K}
    → Γ₁ ⊢ᵥ u ⇒ T ⊣ Γ₂
    → Γ₂ ⊢ᵥ v ⇒ U ⊣ Γ₃
    → (T ∷ˡ (U ∷ˡ Γ₃)) ⊢ e ⇒ V ⊣ used∷ (used∷ Γ₄)
    → Γ₁ ⊢ substExpr₂ e u v ⇒ V ⊣ Γ₄

  subst-var-preserves-synth :
    ∀ {Δ n K L} {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
      {x : Fin n} {T : NfTy Δ L} {e : Expr Δ (Data.Nat.suc n)} {U : NfTy Δ K}
    → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂
    → (T ∷ˡ Γ₂) ⊢ e ⇒ U ⊣ used∷ Γ₃
    → Γ₁ ⊢ substExpr e (V-Var x) ⇒ U ⊣ Γ₃

  subst-preserves-check :
    ∀ {Δ n pk m} {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
      {T : Ty Δ TLin} {v : Value Δ n} {e : Expr Δ (Data.Nat.suc n)}
      {U V : NfTy Δ (KV pk m)}
    → Γ₁ ⊢ᵥ v ⇒ normalizeTy T ⊣ Γ₂
    → (normalizeTy T ∷ˡ Γ₂) ⊢ e ⇐ U ⊣ used∷ Γ₃
    → normalTyOf U <:ₜ normalTyOf V
    → Γ₁ ⊢ substExpr e v ⇐ V ⊣ Γ₃

  subst-check-preserves-synth :
    ∀ {Δ n K} {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
      {T : Ty Δ TLin} {v : Value Δ n} {e : Expr Δ (Data.Nat.suc n)}
      {U : NfTy Δ K}
    → Γ₂ ⊢ E-Val v ⇐ normalizeTy T ⊣ Γ₃
    → (normalizeTy T ∷ˡ Γ₁) ⊢ e ⇒ U ⊣ used∷ Γ₂
    → Γ₁ ⊢ substExpr e v ⇒ U ⊣ Γ₃

  rec-unfold-preserves-value :
    ∀ {Δ n} {Γ : Ctx Δ n}
      {T U : Ty Δ TLin} {v : Value Δ (Data.Nat.suc n)}
    → Γ ⊢ᵥ V-Rec T U v ⇒ linArrNf (normalizeTy T) (normalizeTy U) ⊣ Γ
    → Γ ⊢ᵥ substValue v (V-Rec T U v) ⇒ linArrNf (normalizeTy T) (normalizeTy U) ⊣ Γ

postulate
  substTy-preserves-value :
    ∀ {Δ n K K′} {Γ₁ Γ₂ : Ctx (K ∷ Δ) n}
      {v : Value (K ∷ Δ) n} {T : NfTy (K ∷ Δ) K′} {U : Ty Δ K}
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
    → substTyCtx Γ₁ U ⊢ᵥ substTyValue v U ⇒ substTyNf T U ⊣ substTyCtx Γ₂ U

  substTy-preserves-synth :
    ∀ {Δ n K K′} {Γ₁ Γ₂ : Ctx (K ∷ Δ) n}
      {e : Expr (K ∷ Δ) n} {T : NfTy (K ∷ Δ) K′} {U : Ty Δ K}
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
    → substTyCtx Γ₁ U ⊢ substTyExpr e U ⇒ substTyNf T U ⊣ substTyCtx Γ₂ U

  substTy-preserves-check :
    ∀ {Δ n K pk m} {Γ₁ Γ₂ : Ctx (K ∷ Δ) n}
      {e : Expr (K ∷ Δ) n} {T : NfTy (K ∷ Δ) (KV pk m)} {V : Ty Δ K}
    → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
    → substTyCtx Γ₁ V ⊢ substTyExpr e V ⇐ substTyNf T V ⊣ substTyCtx Γ₂ V
