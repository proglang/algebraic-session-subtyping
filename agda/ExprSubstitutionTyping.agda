module ExprSubstitutionTyping where

open import Data.Fin using (Fin)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (suc)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

import Duality as D
open import Kinds
open import Kits
open import Variance using (Variance)
open import Types using
  ( Ty; Ty-Syntax; Ty-Traversal; T-Var; T-Base; T-Poly; T-Msg; T-Up
  ; NormalTy; NormalProto
  ; nf
  ; nf-complete; nf-sound+; fusion
  ; nt-unique; np-unique
  )
open import TypesProtocolConstructors using (SelectConstTy; SelectTy1; SelectTy2)
open import AlgorithmicSubtyping using (_<:ₜ_; <:ₜ-trans)
open import AlgorithmicSubstitution using () renaming (subst-preserves-<:ₜ to substTy-preserves-<:ₜ)
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
substTyNfWith (mkNfTy T _) ϕ = normalizeTy (T ⋯ ϕ)

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

nfTy-eq :
  ∀ {Δ pk m} {T₁ T₂ : Ty Δ (KV pk m)}
    (eq : T₁ ≡ T₂) (N₁ : NormalTy T₁) (N₂ : NormalTy T₂)
  → mkNfTy T₁ N₁ ≡ mkNfTy T₂ N₂
nfTy-eq refl N₁ N₂ = cong (mkNfTy _) (nt-unique N₁ N₂)

nfProto-eq :
  ∀ {Δ} {T₁ T₂ : Ty Δ KP}
    (eq : T₁ ≡ T₂) (N₁ : NormalProto T₁) (N₂ : NormalProto T₂)
  → mkNfTy T₁ N₁ ≡ mkNfTy T₂ N₂
nfProto-eq refl N₁ N₂ = cong (mkNfTy _) (np-unique N₁ N₂)

postulate
  BranchJoin-subst :
    ∀ {Δ K k} {V : Fin (suc k) → NfTy (K ∷ Δ) TLin} {U : NfTy (K ∷ Δ) TLin} {W : Ty Δ K}
    → BranchJoin V U
    → BranchJoin (λ i → substTyNf (V i) W) (substTyNf U W)

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
substTy-linArrNf (mkNfTy T NT) (mkNfTy U NU) W = refl

substTy-pairNf :
  ∀ {Δ K pk₁ pk₂ m}
    (T : NfTy (K ∷ Δ) (KV pk₁ m))
    (U : NfTy (K ∷ Δ) (KV pk₂ m))
    (W : Ty Δ K)
  → substTyNf (pairNf T U) W ≡ pairNf (substTyNf T W) (substTyNf U W)
substTy-pairNf (mkNfTy T NT) (mkNfTy U NU) W = refl

substTyWith-normalizeTy :
  ∀ {Δ Δ′ K} (T : Ty Δ K) (ϕ : Δ →ₛ Δ′)
  → substTyNfWith (normalizeTy T) ϕ ≡ normalizeTy (T ⋯ ϕ)
substTyWith-normalizeTy {K = KV pk m} T ϕ =
  nfTy-eq
    (nf-complete D.d?⊥ D.d?⊥ (subst-preserves-≡c (nf-sound+ T) ϕ))
    _
    _
substTyWith-normalizeTy {K = KP} T ϕ =
  nfProto-eq
    (nf-complete D.d?⊥ D.d?⊥ (subst-preserves-≡c (nf-sound+ T) ϕ))
    _
    _

substTy-normalizeTy :
  ∀ {Δ K K′} (T : Ty (K ∷ Δ) K′) (U : Ty Δ K)
  → substTyNf (normalizeTy T) U ≡ normalizeTy (T ⋯ ⦅ U ⦆ₛ)
substTy-normalizeTy T U = substTyWith-normalizeTy T ⦅ U ⦆ₛ

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

substTy-preserves-value-receive₁ :
  ∀ {Δ n K} {Γ₁ : Ctx (K ∷ Δ) n} {T : Ty (K ∷ Δ) TLin} {U : Ty Δ K}
  → substTyCtx Γ₁ U ⊢ᵥ V-Receive₁ (T ⋯ ⦅ U ⦆ₛ)
       ⇒ substTyNf (normalizeTy (ReceiveTy1 T)) U ⊣ substTyCtx Γ₁ U
substTy-preserves-value-receive₁ {Δ = Δ} {K = K} {Γ₁ = Γ₁} {T = T} {U = U} =
  Eq.subst
    (Receive₁Ty (substTyCtx Γ₁ U) (T ⋯ ⦅ U ⦆ₛ))
    (Eq.sym
      (Eq.trans
        (substTy-normalizeTy {Δ = Δ} {K = K} (ReceiveTy1 T) U)
        (cong normalizeTy (substTy-ReceiveTy1 T U))))
    (TV-Receive₁ {T = T ⋯ ⦅ U ⦆ₛ})
  where
  Receive₁Ty :
    ∀ {Δ n} (Γ₁ : Ctx Δ n) (T : Ty Δ TLin) →
    NfTy Δ TLin → Set
  Receive₁Ty Γ₁ T X =
    Γ₁ ⊢ᵥ V-Receive₁ T ⇒ X ⊣ Γ₁

substTy-preserves-value-send₁ :
  ∀ {Δ n K} {Γ₁ : Ctx (K ∷ Δ) n} {T : Ty (K ∷ Δ) TLin} {U : Ty Δ K}
  → substTyCtx Γ₁ U ⊢ᵥ V-Send₁ (T ⋯ ⦅ U ⦆ₛ)
       ⇒ substTyNf (normalizeTy (SendTy1 T)) U ⊣ substTyCtx Γ₁ U
substTy-preserves-value-send₁ {Δ = Δ} {K = K} {Γ₁ = Γ₁} {T = T} {U = U} =
  Eq.subst
    (Send₁Ty (substTyCtx Γ₁ U) (T ⋯ ⦅ U ⦆ₛ))
    (Eq.sym
      (Eq.trans
        (substTy-normalizeTy {Δ = Δ} {K = K} (SendTy1 T) U)
        (cong normalizeTy (substTy-SendTy1 T U))))
    (TV-Send₁ {T = T ⋯ ⦅ U ⦆ₛ})
  where
  Send₁Ty :
    ∀ {Δ n} (Γ₁ : Ctx Δ n) (T : Ty Δ TLin) →
    NfTy Δ TLin → Set
  Send₁Ty Γ₁ T X =
    Γ₁ ⊢ᵥ V-Send₁ T ⇒ X ⊣ Γ₁

substTy-preserves-value-receive₂ :
  ∀ {Δ n K} {Γ₁ : Ctx (K ∷ Δ) n} {T : Ty (K ∷ Δ) TLin} {S : Ty (K ∷ Δ) SLin} {U : Ty Δ K}
  → substTyCtx Γ₁ U ⊢ᵥ V-Receive₂ (T ⋯ ⦅ U ⦆ₛ) (S ⋯ ⦅ U ⦆ₛ)
       ⇒ substTyNf (normalizeTy (ReceiveTy T S)) U ⊣ substTyCtx Γ₁ U
substTy-preserves-value-receive₂ {Γ₁ = Γ₁} {T = T} {S = S} {U = U} =
  Eq.subst
    (Receive₂Ty Γ₁ T S U)
    (sym (substTy-normalizeTy (ReceiveTy T S) U))
    (TV-Receive₂ {T = T ⋯ ⦅ U ⦆ₛ} {S = S ⋯ ⦅ U ⦆ₛ})
  where
  Receive₂Ty :
    ∀ {Δ n K} (Γ₁ : Ctx (K ∷ Δ) n) (T : Ty (K ∷ Δ) TLin) (S : Ty (K ∷ Δ) SLin) (U : Ty Δ K) →
    NfTy Δ TLin → Set
  Receive₂Ty Γ₁ T S U X =
    substTyCtx Γ₁ U ⊢ᵥ V-Receive₂ (T ⋯ ⦅ U ⦆ₛ) (S ⋯ ⦅ U ⦆ₛ) ⇒ X ⊣ substTyCtx Γ₁ U

substTy-preserves-value-send₂ :
  ∀ {Δ n K} {Γ₁ : Ctx (K ∷ Δ) n} {T : Ty (K ∷ Δ) TLin} {S : Ty (K ∷ Δ) SLin} {U : Ty Δ K}
  → substTyCtx Γ₁ U ⊢ᵥ V-Send₂ (T ⋯ ⦅ U ⦆ₛ) (S ⋯ ⦅ U ⦆ₛ)
       ⇒ substTyNf (normalizeTy (SendTy T S)) U ⊣ substTyCtx Γ₁ U
substTy-preserves-value-send₂ {Γ₁ = Γ₁} {T = T} {S = S} {U = U} =
  Eq.subst
    (Send₂Ty Γ₁ T S U)
    (sym (substTy-normalizeTy (SendTy T S) U))
    (TV-Send₂ {T = T ⋯ ⦅ U ⦆ₛ} {S = S ⋯ ⦅ U ⦆ₛ})
  where
  Send₂Ty :
    ∀ {Δ n K} (Γ₁ : Ctx (K ∷ Δ) n) (T : Ty (K ∷ Δ) TLin) (S : Ty (K ∷ Δ) SLin) (U : Ty Δ K) →
    NfTy Δ TLin → Set
  Send₂Ty Γ₁ T S U X =
    substTyCtx Γ₁ U ⊢ᵥ V-Send₂ (T ⋯ ⦅ U ⦆ₛ) (S ⋯ ⦅ U ⦆ₛ) ⇒ X ⊣ substTyCtx Γ₁ U

substTy-preserves-value-select₁ :
  ∀ {Δ n K k} {Γ₁ : Ctx (K ∷ Δ) n} {v : Variance} {i : Fin k} {P : Ty (K ∷ Δ) KP} {U : Ty Δ K}
  → substTyCtx Γ₁ U ⊢ᵥ V-Select₁ v i (P ⋯ ⦅ U ⦆ₛ)
       ⇒ substTyNf (normalizeTy (SelectTy1 v i P)) U ⊣ substTyCtx Γ₁ U
substTy-preserves-value-select₁ {Γ₁ = Γ₁} {v = v} {i = i} {P = P} {U = U} =
  Eq.subst
    (Select₁Ty Γ₁ v i P U)
    (Eq.sym
      (Eq.trans
        (substTy-normalizeTy (SelectTy1 v i P) U)
        (cong normalizeTy (substTy-SelectTy1 {v = v} P U))))
    (TV-Select₁ {v = v} {i = i} {P = P ⋯ ⦅ U ⦆ₛ})
  where
  Select₁Ty :
    ∀ {Δ n K k} (Γ₁ : Ctx (K ∷ Δ) n) (v : Variance) (i : Fin k) (P : Ty (K ∷ Δ) KP) (U : Ty Δ K) →
    NfTy Δ TLin → Set
  Select₁Ty Γ₁ v i P U X =
    substTyCtx Γ₁ U ⊢ᵥ V-Select₁ v i (P ⋯ ⦅ U ⦆ₛ) ⇒ X ⊣ substTyCtx Γ₁ U

substTy-preserves-value-select₂ :
  ∀ {Δ n K k} {Γ₁ : Ctx (K ∷ Δ) n}
    {v : Variance} {i : Fin k} {P : Ty (K ∷ Δ) KP} {S : Ty (K ∷ Δ) SLin} {U : Ty Δ K}
  → substTyCtx Γ₁ U ⊢ᵥ V-Select₂ v i (P ⋯ ⦅ U ⦆ₛ) (S ⋯ ⦅ U ⦆ₛ)
       ⇒ substTyNf (normalizeTy (SelectTy2 v i P S)) U ⊣ substTyCtx Γ₁ U
substTy-preserves-value-select₂ {Γ₁ = Γ₁} {v = v} {i = i} {P = P} {S = S} {U = U} =
  Eq.subst
    (Select₂Ty Γ₁ v i P S U)
    (Eq.sym
      (Eq.trans
        (substTy-normalizeTy (SelectTy2 v i P S) U)
        (cong normalizeTy (substTy-SelectTy2 {v = v} P S U))))
    (TV-Select₂ {v = v} {i = i} {P = P ⋯ ⦅ U ⦆ₛ} {S = S ⋯ ⦅ U ⦆ₛ})
  where
  Select₂Ty :
    ∀ {Δ n K k}
      (Γ₁ : Ctx (K ∷ Δ) n) (v : Variance) (i : Fin k) (P : Ty (K ∷ Δ) KP) (S : Ty (K ∷ Δ) SLin) (U : Ty Δ K) →
      NfTy Δ TLin → Set
  Select₂Ty Γ₁ v i P S U X =
    substTyCtx Γ₁ U ⊢ᵥ V-Select₂ v i (P ⋯ ⦅ U ⦆ₛ) (S ⋯ ⦅ U ⦆ₛ) ⇒ X ⊣ substTyCtx Γ₁ U

ConstTy-subst :
  ∀ {Δ K c K′} {T : NfTy (K ∷ Δ) K′} {U : Ty Δ K}
  → ConstTy c T
  → ConstTy c (substTyNf T U)
ConstTy-subst {U = U} CT-Unit rewrite substTy-normalizeTy T-Base U = CT-Unit
ConstTy-subst {U = U} CT-Fork rewrite substTy-normalizeTy ForkTy U = CT-Fork
ConstTy-subst {U = U} CT-New rewrite substTy-normalizeTy NewTy U = CT-New
ConstTy-subst {U = U} CT-Receive
  rewrite substTy-normalizeTy (T-Poly TLin (ReceiveTy1 (T-Var (here refl)))) U
  = CT-Receive
ConstTy-subst {U = U} CT-Send
  rewrite substTy-normalizeTy (T-Poly TLin (SendTy1 (T-Var (here refl)))) U
  = CT-Send
ConstTy-subst {U = U} CT-Close rewrite substTy-normalizeTy (LinArr EndLin UnitLin) U = CT-Close
ConstTy-subst CT-Select = ConstTy-select-subst

postulate

  MatchBranches-subst :
    ∀ {Δ K k} {T : NfTy (K ∷ Δ) SLin} {B : Fin k → NfTy (K ∷ Δ) SLin} {U : Ty Δ K}
    → MatchBranches T B
    → MatchBranches (substTyNf T U) (λ i → substTyNf (B i) U)

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

mutual

  substTy-preserves-value :
    ∀ {Δ n K K′} {Γ₁ Γ₂ : Ctx (K ∷ Δ) n}
      {v : Value (K ∷ Δ) n} {T : NfTy (K ∷ Δ) K′} {U : Ty Δ K}
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
    → substTyCtx Γ₁ U ⊢ᵥ substTyValue v U ⇒ substTyNf T U ⊣ substTyCtx Γ₂ U
  substTy-preserves-value (TV-Const p) = TV-Const (ConstTy-subst p)
  substTy-preserves-value (TV-Var-Lin p) = TV-Var-Lin (substTy-preserves-⊢ˡ p)
  substTy-preserves-value (TV-Var-Un p) = TV-Var-Un (substTy-preserves-∋ᵘ p)
  substTy-preserves-value {Γ₁ = Γ₁} {Γ₂ = Γ₂} {U = W}
    (TV-Abs {T = T} {U = U} {e = e} p) =
    Eq.subst
      (λ X → substTyCtx Γ₁ W ⊢ᵥ V-Abs (T ⋯ ⦅ W ⦆ₛ) (substTyExpr e W) ⇒ X ⊣ substTyCtx Γ₂ W)
      (Eq.sym
        (Eq.trans
          (substTy-linArrNf (normalizeTy T) U W)
          (cong (λ X → linArrNf X (substTyNf U W))
            (substTy-normalizeTy T W))))
        (TV-Abs
          (Eq.subst
          (λ X → (X ∷ˡ substTyCtx Γ₁ W) ⊢ substTyExpr e W ⇒ substTyNf U W ⊣ used∷ (substTyCtx Γ₂ W))
          (substTy-normalizeTy T W)
          (substTy-preserves-synth p)))
  substTy-preserves-value {Γ₁ = Γ₁} {U = W}
    (TV-Rec {T = T} {U = U} {v = v} p) =
    Eq.subst
      (λ X → substTyCtx Γ₁ W ⊢ᵥ V-Rec (T ⋯ ⦅ W ⦆ₛ) (U ⋯ ⦅ W ⦆ₛ) (substTyValue v W) ⇒ X ⊣ substTyCtx Γ₁ W)
      (Eq.sym
        (Eq.trans
          (substTy-linArrNf (normalizeTy T) (normalizeTy U) W)
          (cong₂ linArrNf (substTy-normalizeTy T W) (substTy-normalizeTy U W))))
      (TV-Rec
        (Eq.subst
          (λ X → (X ∷ᵘ substTyCtx Γ₁ W) ⊢ E-Val (substTyValue v W) ⇐ X ⊣ (X ∷ᵘ (substTyCtx Γ₁ W)))
          (Eq.trans
            (substTy-linArrNf (normalizeTy T) (normalizeTy U) W)
            (cong₂ linArrNf (substTy-normalizeTy T W) (substTy-normalizeTy U W)))
          (substTy-preserves-check p)))
  substTy-preserves-value {Γ₁ = Γ₁} {Γ₂ = Γ₂} {U = U}
    (TV-TAbs {K = K′} {m = m} {v = v} {T = T} p) =
    substTy-preserves-value-tabs {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = v} {T = T} {U = U} p
  substTy-preserves-value {U = U} (TV-Pair {T = T} {U = U₁} p q)
    rewrite substTy-pairNf T U₁ U
    = TV-Pair (substTy-preserves-value p) (substTy-preserves-value q)
  substTy-preserves-value {Γ₁ = Γ₁} {U = U} (TV-Receive₁ {T = T}) =
    substTy-preserves-value-receive₁ {Γ₁ = Γ₁} {T = T} {U = U}
  substTy-preserves-value {Γ₁ = Γ₁} {U = U} (TV-Receive₂ {T = T} {S = S}) =
    substTy-preserves-value-receive₂ {Γ₁ = Γ₁} {T = T} {S = S} {U = U}
  substTy-preserves-value {Γ₁ = Γ₁} {U = U} (TV-Send₁ {T = T}) =
    substTy-preserves-value-send₁ {Γ₁ = Γ₁} {T = T} {U = U}
  substTy-preserves-value {Γ₁ = Γ₁} {U = U} (TV-Send₂ {T = T} {S = S}) =
    substTy-preserves-value-send₂ {Γ₁ = Γ₁} {T = T} {S = S} {U = U}
  substTy-preserves-value {Γ₁ = Γ₁} {Γ₂ = Γ₂} {U = U}
    (TV-Send₃ {T = T} {S = S} {v = v} p)
    rewrite substTy-normalizeTy (LinArr (SessLin (T-Msg D.⊕ (T-Up T) S)) (SessLin S)) U
    = TV-Send₃
        (Eq.subst
          (λ X → substTyCtx Γ₁ U ⊢ E-Val (substTyValue v U) ⇐ X ⊣ substTyCtx Γ₂ U)
          (substTy-normalizeTy T U)
          (substTy-preserves-check p))
  substTy-preserves-value {Γ₁ = Γ₁} {U = U} (TV-Select₁ {v = v} {i = i} {P = P}) =
    substTy-preserves-value-select₁ {Γ₁ = Γ₁} {v = v} {i = i} {P = P} {U = U}
  substTy-preserves-value {Γ₁ = Γ₁} {U = U} (TV-Select₂ {v = v} {i = i} {P = P} {S = S}) =
    substTy-preserves-value-select₂ {Γ₁ = Γ₁} {v = v} {i = i} {P = P} {S = S} {U = U}

  substTy-preserves-synth :
    ∀ {Δ n K K′} {Γ₁ Γ₂ : Ctx (K ∷ Δ) n}
      {e : Expr (K ∷ Δ) n} {T : NfTy (K ∷ Δ) K′} {U : Ty Δ K}
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
    → substTyCtx Γ₁ U ⊢ substTyExpr e U ⇒ substTyNf T U ⊣ substTyCtx Γ₂ U
  substTy-preserves-synth (T-Val p) = T-Val (substTy-preserves-value p)
  substTy-preserves-synth {U = U} (T-Pair {T = T} {U = U₁} p q)
    rewrite substTy-pairNf T U₁ U
    = T-Pair (substTy-preserves-synth p) (substTy-preserves-synth q)
  substTy-preserves-synth {Γ₁ = Γ₁} {Γ₂ = Γ₃} {U = W}
    (T-App {Γ₂ = Γ₂} {e₁ = e₁} {e₂ = e₂} {T = T} {U = U₁} p q)
    = T-App
        (Eq.subst
          (λ X → substTyCtx Γ₁ W ⊢ substTyExpr e₁ W ⇒ X ⊣ substTyCtx Γ₂ W)
          (substTy-linArrNf T U₁ W)
          (substTy-preserves-synth p))
        (substTy-preserves-check q)
  substTy-preserves-synth (T-LetUnit p q) = T-LetUnit (substTy-preserves-check p) (substTy-preserves-synth q)
  substTy-preserves-synth {U = U} (T-LetPair p q) = substTy-preserves-synth-letpair p q
  substTy-preserves-synth {U = U} (T-Match p mb br bj) =
    T-Match
      (substTy-preserves-synth p)
      (MatchBranches-subst mb)
      (λ i → substTy-preserves-synth (br i))
      (BranchJoin-subst bj)
  substTy-preserves-synth {U = U} (T-TApp p) = substTy-preserves-synth-tapp p

  substTy-preserves-check :
    ∀ {Δ n K pk m} {Γ₁ Γ₂ : Ctx (K ∷ Δ) n}
      {e : Expr (K ∷ Δ) n} {T : NfTy (K ∷ Δ) (KV pk m)} {V : Ty Δ K}
    → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
    → substTyCtx Γ₁ V ⊢ substTyExpr e V ⇐ substTyNf T V ⊣ substTyCtx Γ₂ V
  substTy-preserves-check {V = V}
    (T-Check {T = mkNfTy T NT} {U = mkNfTy U NU} p q) =
    T-Check
      (substTy-preserves-synth p)
      (substTy-preserves-<:ₜ {T₁ = U} {T₂ = T} {U = V}
        {N₁ = NU} {N₂ = NT} q)
