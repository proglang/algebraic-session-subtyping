module ExprTypingStrengthening where

open import Duality
open import Variance
open import Kinds
open import Kits
open import Types
open import Subtyping
open import TypesProtocolConstructors
import NormalTypes as NT
open import AlgorithmicNFMerge using (joinₜ)
open import AlgorithmicNFSubtyping using
  ( _<:ₜ_
  ; _<:ₚ′_
  ; _<:ₚ_
  ; _<<:ₚ′[_]_
  ; _<<:ₚ[_]_
  ; <:ₜ-var
  ; <:ₜ-base
  ; <:ₜ-trans
  ; <:ₜ-refl
  ; <:ₜ-arrow
  ; <:ₜ-pair
  ; <:ₜ-poly
  ; <:ₜ-sub
  ; <:ₜ-end
  ; <:ₜ-msg
  ; <:ₜ-data
  ; <:ₚ′-proto
  ; <:ₚ′-up
  ; <:ₚ′-var
  ; <:ₚ-plus
  ; <:ₚ-minus
  )
open import AlgorithmicNFSubstitution using (subst-preserves-<:ₜ)
open import NormalTypesSubstitution using (substNFTy)
open import NormalTypesRenamings using (renNFTy; renNFProto′; renNFProto; wkNFTy; renNFProto′-sound; renNFProto-sound)

open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_; here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin.Subset as Subset
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary using (¬_; Dec; yes; no; map′)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; inspect; Reveal_·_is_)

open import ExprNormalTyping
open import ExprSyntax
open import ExprContextReduction using (RM-lin)
open import ExprTypingLeftover using (leftover-synth)

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (_⋯_; ⋯-id)


data _<:Γ_ : ∀ {Δ n} (Γ₁ : Ctx Δ n) (Γ₂ : Ctx Δ n) → Set where

  <:-[] : ∀ {Δ} → ∅ {Δ} <:Γ ∅

  <:-used :
      ∀ {Δ n pk}
      {T : NfTy Δ (KV pk Lin)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ₁ <:Γ Γ₂
    → (B-Used T ▻ Γ₁) <:Γ (B-Used T ▻ Γ₂)

  <:-sub-used :
      ∀ {Δ n pk}
      {T₁ T₂ : NfTy Δ (KV pk Lin)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → T₁ <:ₜ T₂
    → Γ₁ <:Γ Γ₂
    → (B-Used T₁ ▻ Γ₁) <:Γ (B-Used T₂ ▻ Γ₂)

  <:-lin :
      ∀ {Δ n pk}
      {T : NfTy Δ (KV pk Lin)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ₁ <:Γ Γ₂
    → (B-Lin T ▻ Γ₁) <:Γ (B-Lin T ▻ Γ₂)

  <:-sub-lin :
      ∀ {Δ n pk}
      {T₁ T₂ : NfTy Δ (KV pk Lin)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → T₁ <:ₜ T₂
    → Γ₁ <:Γ Γ₂
    → (B-Lin T₁ ▻ Γ₁) <:Γ (B-Lin T₂ ▻ Γ₂)

  <:-sub-unr :
      ∀ {Δ n pk}
      {T₁ T₂ : NfTy Δ (KV pk Un)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → T₁ <:ₜ T₂
    → Γ₁ <:Γ Γ₂
    → (B-Un T₁ ▻ Γ₁) <:Γ (B-Un T₂ ▻ Γ₂)

  <:-un :
      ∀ {Δ n pk}
      {T : NfTy Δ (KV pk Un)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ₁ <:Γ Γ₂
    → (B-Un T ▻ Γ₁) <:Γ (B-Un T ▻ Γ₂)


<:Γ-refl : ∀ {Δ n} {Γ : Ctx Δ n} → Γ <:Γ Γ
<:Γ-refl {Γ = ∅} = <:-[]
<:Γ-refl {Γ = B-Used T ▻ Γ} = <:-used <:Γ-refl
<:Γ-refl {Γ = B-Lin T ▻ Γ} = <:-lin <:Γ-refl
<:Γ-refl {Γ = B-Un T ▻ Γ} = <:-un <:Γ-refl

mutual

  ren-preserves-<:ₜ :
    ∀ {Δ₁ Δ₂ pk m}
      (ρ : Δ₁ →ᵣ Δ₂) {T₁ T₂ : NfTy Δ₁ (KV pk m)}
    → T₁ <:ₜ T₂
    → renNFTy ρ T₁ <:ₜ renNFTy ρ T₂

  ren-preserves-<:ₚ′ :
    ∀ {Δ₁ Δ₂}
      (ρ : Δ₁ →ᵣ Δ₂) {P₁ P₂ : NT.NFProto′ Δ₁}
    → P₁ <:ₚ′ P₂
    → renNFProto′ ρ P₁ <:ₚ′ renNFProto′ ρ P₂

  ren-preserves-<:ₚ :
    ∀ {Δ₁ Δ₂}
      (ρ : Δ₁ →ᵣ Δ₂) {P₁ P₂ : NT.NFProto Δ₁}
    → P₁ <:ₚ P₂
    → renNFProto ρ P₁ <:ₚ renNFProto ρ P₂

  ren-preserves-<<:ₚ′ :
    ∀ {Δ₁ Δ₂}
      (ρ : Δ₁ →ᵣ Δ₂) {P₁ P₂ : NT.NFProto′ Δ₁} {v : Variance}
    → P₁ <<:ₚ′[ v ] P₂
    → renNFProto′ ρ P₁ <<:ₚ′[ v ] renNFProto′ ρ P₂

  ren-preserves-<<:ₚ :
    ∀ {Δ₁ Δ₂}
      (ρ : Δ₁ →ᵣ Δ₂) {P₁ P₂ : NT.NFProto Δ₁} {v : Variance}
    → P₁ <<:ₚ[ v ] P₂
    → renNFProto ρ P₁ <<:ₚ[ v ] renNFProto ρ P₂

  ren-preserves-<:ₜ ρ <:ₜ-var = <:ₜ-var
  ren-preserves-<:ₜ ρ <:ₜ-base = <:ₜ-base
  ren-preserves-<:ₜ ρ (<:ₜ-arrow dom cod) =
    <:ₜ-arrow (ren-preserves-<:ₜ ρ dom) (ren-preserves-<:ₜ ρ cod)
  ren-preserves-<:ₜ ρ (<:ₜ-pair l r) =
    <:ₜ-pair (ren-preserves-<:ₜ ρ l) (ren-preserves-<:ₜ ρ r)
  ren-preserves-<:ₜ ρ (<:ₜ-poly sub) =
    <:ₜ-poly (ren-preserves-<:ₜ (ρ ↑ᵣ _) sub)
  ren-preserves-<:ₜ ρ (<:ₜ-sub sub) =
    <:ₜ-sub (ren-preserves-<:ₜ ρ sub)
  ren-preserves-<:ₜ ρ <:ₜ-end = <:ₜ-end
  ren-preserves-<:ₜ ρ (<:ₜ-msg psub ssub) =
    <:ₜ-msg (ren-preserves-<<:ₚ′ ρ psub) (ren-preserves-<:ₜ ρ ssub)
  ren-preserves-<:ₜ ρ (<:ₜ-data sub) =
    <:ₜ-data (ren-preserves-<:ₜ ρ sub)

  ren-preserves-<:ₚ′ ρ (<:ₚ′-proto ss sub) =
    <:ₚ′-proto ss (ren-preserves-<<:ₚ ρ sub)
  ren-preserves-<:ₚ′ ρ (<:ₚ′-up sub) =
    <:ₚ′-up (ren-preserves-<:ₜ ρ sub)
  ren-preserves-<:ₚ′ ρ <:ₚ′-var = <:ₚ′-var

  ren-preserves-<:ₚ ρ (<:ₚ-plus sub) = <:ₚ-plus (ren-preserves-<:ₚ′ ρ sub)
  ren-preserves-<:ₚ ρ (<:ₚ-minus sub) = <:ₚ-minus (ren-preserves-<:ₚ′ ρ sub)

  ren-preserves-<<:ₚ′ ρ {v = ⊕} sub = ren-preserves-<:ₚ′ ρ sub
  ren-preserves-<<:ₚ′ ρ {v = ⊝} sub = ren-preserves-<:ₚ′ ρ sub
  ren-preserves-<<:ₚ′ ρ {P₁ = P₁} {P₂ = P₂} {v = ⊘} eq =
    trans
      (renNFProto′-sound ρ P₁)
      (trans
        (cong (λ T → T ⋯ ρ) eq)
        (sym (renNFProto′-sound ρ P₂)))

  ren-preserves-<<:ₚ ρ {v = ⊕} sub = ren-preserves-<:ₚ ρ sub
  ren-preserves-<<:ₚ ρ {v = ⊝} sub = ren-preserves-<:ₚ ρ sub
  ren-preserves-<<:ₚ ρ {P₁ = P₁} {P₂ = P₂} {v = ⊘} eq =
    trans
      (renNFProto-sound ρ P₁)
      (trans
        (cong (λ T → T ⋯ ρ) eq)
        (sym (renNFProto-sound ρ P₂)))

<:ₜ-wk :
  ∀ {Δ K pk m}
    {T₁ T₂ : NfTy Δ (KV pk m)}
  → T₁ <:ₜ T₂
  → wkNfTy {K′ = K} T₁ <:ₜ wkNfTy T₂
<:ₜ-wk {K = K} sub = ren-preserves-<:ₜ (weakenᵣ K) sub

<:Γ-wk : 
  ∀ {Δ n K} {Γ₁ Γ₂ : Ctx Δ n}
  → Γ₁ <:Γ Γ₂
  → wkCtx {K = K} Γ₁ <:Γ wkCtx Γ₂
<:Γ-wk <:-[] = <:-[]
<:Γ-wk (<:-used rel) = <:-used (<:Γ-wk rel)
<:Γ-wk (<:-sub-used sub rel) = <:-sub-used (<:ₜ-wk sub) (<:Γ-wk rel)
<:Γ-wk (<:-lin rel) = <:-lin (<:Γ-wk rel)
<:Γ-wk (<:-sub-lin sub rel) = <:-sub-lin (<:ₜ-wk sub) (<:Γ-wk rel)
<:Γ-wk (<:-sub-unr sub rel) = <:-sub-unr (<:ₜ-wk sub) (<:Γ-wk rel)
<:Γ-wk (<:-un rel) = <:-un (<:Γ-wk rel)

used-tail-<:Γ :
  ∀ {Δ n pk} {Γ₁ : Ctx Δ (suc n)} {Γ₂ : Ctx Δ n}
    {T : NfTy Δ (KV pk Lin)}
  → Γ₁ <:Γ (used∷ {T = T} Γ₂)
  → Σ (NfTy Δ (KV pk Lin)) λ T₁ →
      Σ (Ctx Δ n) λ Γ₁′ →
        Γ₁ ≡ used∷ {T = T₁} Γ₁′ × Γ₁′ <:Γ Γ₂
used-tail-<:Γ {Γ₁ = B-Used T ▻ Γ₁} (<:-used rel) = T , Γ₁ , refl , rel
used-tail-<:Γ {Γ₁ = B-Used T₁ ▻ Γ₁} (<:-sub-used _ rel) = T₁ , Γ₁ , refl , rel

lin-used-head-rigid :
  ∀ {Δ n K pk}
    {Γin Γout : Ctx Δ n}
    {T T′ : NfTy Δ (KV pk Lin)}
    {e : Expr Δ (suc n)}
    {U : NfTy Δ K}
  → (T ∷ˡ Γin) ⊢ e ⇒ U ⊣ (B-Used T′ ▻ Γout)
  → T ≡ T′
lin-used-head-rigid d with leftover-synth d
... | _ , RM-lin _ = refl

lin2-used2-head-rigid :
  ∀ {Δ n K pk₁ pk₂}
    {Γin Γout : Ctx Δ n}
    {T T′ : NfTy Δ (KV pk₁ Lin)}
    {U U′ : NfTy Δ (KV pk₂ Lin)}
    {e : Expr Δ (suc (suc n))}
    {V : NfTy Δ K}
  → (T ∷ˡ (U ∷ˡ Γin)) ⊢ e ⇒ V ⊣ (B-Used T′ ▻ (B-Used U′ ▻ Γout))
  → (T ≡ T′) × (U ≡ U′)
lin2-used2-head-rigid d with leftover-synth d
... | _ , RM-lin r with r
... | RM-lin _ = refl , refl

check-subsumption :
  ∀ {Δ n pk m}
    {Γ₁ Γ₂ : Ctx Δ n}
    {e : Expr Δ n}
    {T U : NfTy Δ (KV pk m)}
  → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
  → normalTyOf T <:ₜ normalTyOf U
  → Γ₁ ⊢ e ⇐ U ⊣ Γ₂
check-subsumption (T-Check d sub) sub′ = T-Check d (<:ₜ-trans sub sub′)

arrow-subtype-inversion :
  ∀ {Δ m}
    {A B : NfTy Δ TLin}
    {X : NfTy Δ (KV KT m)}
  → normalTyOf X <:ₜ normalTyOf (NT.N-Arrow {m = m} (≤p-step <p-mt) A B)
  → Σ (NfTy Δ TLin) λ A′ →
      Σ (NfTy Δ TLin) λ B′ →
        (X ≡ NT.N-Arrow {m = m} (≤p-step <p-mt) A′ B′)
        × (normalTyOf A <:ₜ normalTyOf A′)
        × (normalTyOf B′ <:ₜ normalTyOf B)
arrow-subtype-inversion (<:ₜ-arrow dom cod) = _ , _ , refl , dom , cod

pair-subtype-inversion :
  ∀ {Δ pk₁ pk₂ m}
    {T : NfTy Δ (KV pk₁ m)}
    {U : NfTy Δ (KV pk₂ m)}
    {X : NfTy Δ (KV KT m)}
  → normalTyOf X <:ₜ normalTyOf (pairNf T U)
  → Σ (NfTy Δ (KV pk₁ m)) λ T′ →
      Σ (NfTy Δ (KV pk₂ m)) λ U′ →
        (X ≡ pairNf T′ U′)
        × (normalTyOf T′ <:ₜ normalTyOf T)
        × (normalTyOf U′ <:ₜ normalTyOf U)
pair-subtype-inversion (<:ₜ-pair l r) = _ , _ , refl , l , r

poly-subtype-inversion :
  ∀ {Δ K m}
    {X : NfTy Δ (KV KT m)}
    {T : NfTy (K ∷ Δ) (KV KT m)}
  → normalTyOf X <:ₜ normalTyOf (polyNf {K = K} T)
  → Σ (NfTy (K ∷ Δ) (KV KT m)) λ T′ →
      (X ≡ polyNf T′) × (normalTyOf T′ <:ₜ normalTyOf T)
poly-subtype-inversion (<:ₜ-poly sub) = _ , refl , sub

strengthen-∋ᵘ :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ : Ctx Δ n}
    {x : Fin n} {T : NfTy Δ (KV pk Un)}
  → Γ₁ <:Γ Γ₂
  → Γ₂ ∋ᵘ x ∶ T
  → Σ (NfTy Δ (KV pk Un)) λ T′ →
      (Γ₁ ∋ᵘ x ∶ T′) × (normalTyOf T′ <:ₜ normalTyOf T)
strengthen-∋ᵘ (<:-sub-unr sub _) hereᵘ = _ , hereᵘ , sub
strengthen-∋ᵘ (<:-un _) hereᵘ = _ , hereᵘ , <:ₜ-refl _
strengthen-∋ᵘ (<:-lin rel) (thereᵘˡ x∈)
  with strengthen-∋ᵘ rel x∈
... | T′ , x∈′ , sub = T′ , thereᵘˡ x∈′ , sub
strengthen-∋ᵘ (<:-sub-lin _ rel) (thereᵘˡ x∈)
  with strengthen-∋ᵘ rel x∈
... | T′ , x∈′ , sub = T′ , thereᵘˡ x∈′ , sub
strengthen-∋ᵘ (<:-un rel) (thereᵘᵘ x∈)
  with strengthen-∋ᵘ rel x∈
... | T′ , x∈′ , sub = T′ , thereᵘᵘ x∈′ , sub
strengthen-∋ᵘ (<:-sub-unr _ rel) (thereᵘᵘ x∈)
  with strengthen-∋ᵘ rel x∈
... | T′ , x∈′ , sub = T′ , thereᵘᵘ x∈′ , sub
strengthen-∋ᵘ (<:-used rel) (thereᵘ✖ x∈)
  with strengthen-∋ᵘ rel x∈
... | T′ , x∈′ , sub = T′ , thereᵘ✖ x∈′ , sub
strengthen-∋ᵘ (<:-sub-used _ rel) (thereᵘ✖ x∈)
  with strengthen-∋ᵘ rel x∈
... | T′ , x∈′ , sub = T′ , thereᵘ✖ x∈′ , sub

strengthen-take :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
    {x : Fin n} {T : NfTy Δ (KV pk Lin)}
  → Γ₁ <:Γ Γ₂
  → Γ₂ ⊢ˡ x ∶ T ⊣ Γ₃
  → Σ (NfTy Δ (KV pk Lin)) λ T′ →
      Σ (Ctx Δ n) λ Γ₃′ →
        (Γ₁ ⊢ˡ x ∶ T′ ⊣ Γ₃′)
        × (normalTyOf T′ <:ₜ normalTyOf T
        × Γ₃′ <:Γ Γ₃)
strengthen-take (<:-sub-lin sub rel) take-here =
  _ , _ , take-here , sub , <:-sub-used sub rel
strengthen-take (<:-lin rel) take-here =
  _ , _ , take-here , <:ₜ-refl _ , <:-used rel
strengthen-take (<:-lin rel) (take-thereˡ take)
  with strengthen-take rel take
... | T′ , Γ₃′ , take′ , sub , rel′ =
  T′ , _ , take-thereˡ take′ , sub , <:-lin rel′
strengthen-take (<:-sub-lin subh rel) (take-thereˡ take)
  with strengthen-take rel take
... | T′ , Γ₃′ , take′ , sub , rel′ =
  T′ , _ , take-thereˡ take′ , sub , <:-sub-lin subh rel′
strengthen-take (<:-sub-unr subh rel) (take-thereᵘ take)
  with strengthen-take rel take
... | T′ , Γ₃′ , take′ , sub , rel′ =
  T′ , _ , take-thereᵘ take′ , sub , <:-sub-unr subh rel′
strengthen-take (<:-un rel) (take-thereᵘ take)
  with strengthen-take rel take
... | T′ , Γ₃′ , take′ , sub , rel′ =
  T′ , _ , take-thereᵘ take′ , sub , <:-un rel′
strengthen-take (<:-used rel) (take-there✖ take)
  with strengthen-take rel take
... | T′ , Γ₃′ , take′ , sub , rel′ =
  T′ , _ , take-there✖ take′ , sub , <:-used rel′
strengthen-take (<:-sub-used subh rel) (take-there✖ take)
  with strengthen-take rel take
... | T′ , Γ₃′ , take′ , sub , rel′ =
  T′ , _ , take-there✖ take′ , sub , <:-sub-used subh rel′

strengthen-var-lin :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
    {x : Fin n} {T : NfTy Δ (KV pk Lin)}
  → Γ₁ <:Γ Γ₂
  → Γ₂ ⊢ˡ x ∶ T ⊣ Γ₃
  → Σ (NfTy Δ (KV pk Lin)) λ T′ →
      Σ (Ctx Δ n) λ Γ₃′ →
        (Γ₁ ⊢ᵥ V-Var x ⇒ T′ ⊣ Γ₃′)
        × (normalTyOf T′ <:ₜ normalTyOf T
        × Γ₃′ <:Γ Γ₃)
strengthen-var-lin rel take
  with strengthen-take rel take
... | T′ , Γ₃′ , take′ , sub , rel′ =
  T′ , Γ₃′ , TV-Var-Lin take′ , sub , rel′

strengthen-var-un :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ : Ctx Δ n}
    {x : Fin n} {T : NfTy Δ (KV pk Un)}
  → Γ₁ <:Γ Γ₂
  → Γ₂ ∋ᵘ x ∶ T
  → Σ (NfTy Δ (KV pk Un)) λ T′ →
      Σ (Ctx Δ n) λ Γ₂′ →
        (Γ₁ ⊢ᵥ V-Var x ⇒ T′ ⊣ Γ₂′)
        × (normalTyOf T′ <:ₜ normalTyOf T
        × Γ₂′ <:Γ Γ₂)
strengthen-var-un {Γ₁ = Γ₁} rel x∈
  with strengthen-∋ᵘ rel x∈
... | T′ , x∈′ , sub =
  T′ , Γ₁ , TV-Var-Un x∈′ , sub , rel

take-not-refl :
  ∀ {Δ n pk} {Γ Γ′ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Lin)}
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
  → Γ ≡ Γ′
  → ⊥
take-not-refl take-here ()
take-not-refl (take-thereˡ take) eq =
  take-not-refl take (cong (λ where (_ ▻ Γ) → Γ) eq)
take-not-refl (take-thereᵘ take) eq =
  take-not-refl take (cong (λ where (_ ▻ Γ) → Γ) eq)
take-not-refl (take-there✖ take) eq =
  take-not-refl take (cong (λ where (_ ▻ Γ) → Γ) eq)

take-no-id :
  ∀ {Δ n pk} {Γ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Lin)}
  → Γ ⊢ˡ x ∶ T ⊣ Γ
  → ⊥
take-no-id take = take-not-refl take refl

strengthen-value-rec :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {T U : Ty Δ TLin}
    {v : Value Δ (suc n)}
  → Γ₁ <:Γ Γ₂
  → (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₂)
       ⊢ E-Val v ⇐ unArrNf (normalizeTy T) (normalizeTy U)
       ⊣ (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₂)
  → (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)
       ⊢ E-Val v ⇐ unArrNf (normalizeTy T) (normalizeTy U)
       ⊣ (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)
strengthen-value-rec rel (T-Check (T-Val (TV-Const ())) sub)
strengthen-value-rec rel (T-Check (T-Val (TV-Var-Un x∈)) sub)
  with strengthen-∋ᵘ (<:-un rel) x∈
... | T′ , x∈′ , sub′ =
  T-Check (T-Val (TV-Var-Un x∈′)) (<:ₜ-trans sub′ sub)
strengthen-value-rec rel (T-Check (T-Val (TV-Rec {T = T₀} {U = U₀} d)) sub) =
  T-Check
    (T-Val (TV-Rec (strengthen-value-rec {T = T₀} {U = U₀} (<:-un rel) d)))
    sub
strengthen-value-rec rel (T-Check (T-Val (TV-TAbs d)) ())
strengthen-value-rec rel (T-Check (T-Val (TV-Pair d₁ d₂)) ())

mutual

  split-renTy-from-sub :
    ∀ {Δ₁ Δ₂ pk m}
      (ρ : Δ₁ →ᵣ Δ₂)
      {T₁ : NfTy Δ₂ (KV pk m)}
      {T₂ : NfTy Δ₁ (KV pk m)}
    → T₁ <:ₜ renNFTy ρ T₂
    → Σ (NfTy Δ₁ (KV pk m)) λ T₁′ →
        (T₁ ≡ renNFTy ρ T₁′) × (T₁′ <:ₜ T₂)

  split-renTy-to-sub :
    ∀ {Δ₁ Δ₂ pk m}
      (ρ : Δ₁ →ᵣ Δ₂)
      {T₁ : NfTy Δ₂ (KV pk m)}
      {T₂ : NfTy Δ₁ (KV pk m)}
    → renNFTy ρ T₂ <:ₜ T₁
    → Σ (NfTy Δ₁ (KV pk m)) λ T₁′ →
        (T₁ ≡ renNFTy ρ T₁′) × (T₂ <:ₜ T₁′)

  split-renProto′-from-sub :
    ∀ {Δ₁ Δ₂}
      (v : Variance) (ρ : Δ₁ →ᵣ Δ₂)
      {P₁ : NT.NFProto′ Δ₂}
      {P₂ : NT.NFProto′ Δ₁}
    → P₁ <<:ₚ′[ v ] renNFProto′ ρ P₂
    → Σ (NT.NFProto′ Δ₁) λ P₁′ →
        (P₁ ≡ renNFProto′ ρ P₁′) × (P₁′ <<:ₚ′[ v ] P₂)

  split-renProto′-to-sub :
    ∀ {Δ₁ Δ₂}
      (v : Variance) (ρ : Δ₁ →ᵣ Δ₂)
      {P₁ : NT.NFProto′ Δ₂}
      {P₂ : NT.NFProto′ Δ₁}
    → renNFProto′ ρ P₂ <<:ₚ′[ v ] P₁
    → Σ (NT.NFProto′ Δ₁) λ P₁′ →
        (P₁ ≡ renNFProto′ ρ P₁′) × (P₂ <<:ₚ′[ v ] P₁′)

  split-renProto-from-sub :
    ∀ {Δ₁ Δ₂}
      (v : Variance) (ρ : Δ₁ →ᵣ Δ₂)
      {P₁ : NT.NFProto Δ₂}
      {P₂ : NT.NFProto Δ₁}
    → P₁ <<:ₚ[ v ] renNFProto ρ P₂
    → Σ (NT.NFProto Δ₁) λ P₁′ →
        (P₁ ≡ renNFProto ρ P₁′) × (P₁′ <<:ₚ[ v ] P₂)

  split-renProto-to-sub :
    ∀ {Δ₁ Δ₂}
      (v : Variance) (ρ : Δ₁ →ᵣ Δ₂)
      {P₁ : NT.NFProto Δ₂}
      {P₂ : NT.NFProto Δ₁}
    → renNFProto ρ P₂ <<:ₚ[ v ] P₁
    → Σ (NT.NFProto Δ₁) λ P₁′ →
        (P₁ ≡ renNFProto ρ P₁′) × (P₂ <<:ₚ[ v ] P₁′)

  split-renTy-from-sub ρ {T₂ = NT.N-Var x} <:ₜ-var =
    NT.N-Var x , refl , <:ₜ-var
  split-renTy-from-sub ρ {T₂ = NT.N-Base} <:ₜ-base =
    NT.N-Base , refl , <:ₜ-base
  split-renTy-from-sub ρ {T₂ = NT.N-Arrow km A₂ B₂} (<:ₜ-arrow dom cod)
    with split-renTy-to-sub ρ {T₂ = A₂} dom
       | split-renTy-from-sub ρ {T₂ = B₂} cod
  ... | A₁′ , eqA , A₂<:A₁′ | B₁′ , eqB , B₁′<:B₂
    rewrite eqA | eqB =
      NT.N-Arrow km A₁′ B₁′ , refl , <:ₜ-arrow A₂<:A₁′ B₁′<:B₂
  split-renTy-from-sub ρ {T₂ = NT.N-Pair A₂ B₂} (<:ₜ-pair l r)
    with split-renTy-from-sub ρ {T₂ = A₂} l
       | split-renTy-from-sub ρ {T₂ = B₂} r
  ... | A₁′ , eqA , A₁′<:A₂ | B₁′ , eqB , B₁′<:B₂
    rewrite eqA | eqB =
      NT.N-Pair A₁′ B₁′ , refl , <:ₜ-pair A₁′<:A₂ B₁′<:B₂
  split-renTy-from-sub ρ {T₂ = NT.N-Poly K′ T₂} (<:ₜ-poly sub)
    with split-renTy-from-sub (ρ ↑ᵣ K′) {T₂ = T₂} sub
  ... | T₁′ , eqT , sub′
    rewrite eqT =
      NT.N-Poly K′ T₁′ , refl , <:ₜ-poly sub′
  split-renTy-from-sub ρ {T₂ = NT.N-Sub km≤ T₂} (<:ₜ-sub sub)
    with split-renTy-from-sub ρ {T₂ = T₂} sub
  ... | T₁′ , eqT , sub′
    rewrite eqT =
      NT.N-Sub km≤ T₁′ , refl , <:ₜ-sub sub′
  split-renTy-from-sub ρ {T₂ = NT.N-End} <:ₜ-end =
    NT.N-End , refl , <:ₜ-end
  split-renTy-from-sub ρ {T₂ = NT.N-Msg p P₂ S₂} (<:ₜ-msg psub ssub)
    with split-renProto′-from-sub (injᵥ p) ρ {P₂ = P₂} psub
       | split-renTy-from-sub ρ {T₂ = S₂} ssub
  ... | P₁′ , eqP , psub′ | S₁′ , eqS , ssub′
    rewrite eqP | eqS =
      NT.N-Msg p P₁′ S₁′ , refl , <:ₜ-msg psub′ ssub′
  split-renTy-from-sub ρ {T₂ = NT.N-ProtoD T₂} (<:ₜ-data sub)
    with split-renTy-from-sub ρ {T₂ = T₂} sub
  ... | T₁′ , eqT , sub′
    rewrite eqT =
      NT.N-ProtoD T₁′ , refl , <:ₜ-data sub′

  split-renTy-to-sub ρ {T₂ = NT.N-Var x} <:ₜ-var =
    NT.N-Var x , refl , <:ₜ-var
  split-renTy-to-sub ρ {T₂ = NT.N-Base} <:ₜ-base =
    NT.N-Base , refl , <:ₜ-base
  split-renTy-to-sub ρ {T₂ = NT.N-Arrow km A₂ B₂} (<:ₜ-arrow dom cod)
    with split-renTy-from-sub ρ {T₂ = A₂} dom
       | split-renTy-to-sub ρ {T₂ = B₂} cod
  ... | A₁′ , eqA , A₁′<:A₂ | B₁′ , eqB , B₂<:B₁′
    rewrite eqA | eqB =
      NT.N-Arrow km A₁′ B₁′ , refl , <:ₜ-arrow A₁′<:A₂ B₂<:B₁′
  split-renTy-to-sub ρ {T₂ = NT.N-Pair A₂ B₂} (<:ₜ-pair l r)
    with split-renTy-to-sub ρ {T₂ = A₂} l
       | split-renTy-to-sub ρ {T₂ = B₂} r
  ... | A₁′ , eqA , A₂<:A₁′ | B₁′ , eqB , B₂<:B₁′
    rewrite eqA | eqB =
      NT.N-Pair A₁′ B₁′ , refl , <:ₜ-pair A₂<:A₁′ B₂<:B₁′
  split-renTy-to-sub ρ {T₂ = NT.N-Poly K′ T₂} (<:ₜ-poly sub)
    with split-renTy-to-sub (ρ ↑ᵣ K′) {T₂ = T₂} sub
  ... | T₁′ , eqT , sub′
    rewrite eqT =
      NT.N-Poly K′ T₁′ , refl , <:ₜ-poly sub′
  split-renTy-to-sub ρ {T₂ = NT.N-Sub km≤ T₂} (<:ₜ-sub sub)
    with split-renTy-to-sub ρ {T₂ = T₂} sub
  ... | T₁′ , eqT , sub′
    rewrite eqT =
      NT.N-Sub km≤ T₁′ , refl , <:ₜ-sub sub′
  split-renTy-to-sub ρ {T₂ = NT.N-End} <:ₜ-end =
    NT.N-End , refl , <:ₜ-end
  split-renTy-to-sub ρ {T₂ = NT.N-Msg p P₂ S₂} (<:ₜ-msg psub ssub)
    with split-renProto′-to-sub (injᵥ p) ρ {P₂ = P₂} psub
       | split-renTy-to-sub ρ {T₂ = S₂} ssub
  ... | P₁′ , eqP , psub′ | S₁′ , eqS , ssub′
    rewrite eqP | eqS =
      NT.N-Msg p P₁′ S₁′ , refl , <:ₜ-msg psub′ ssub′
  split-renTy-to-sub ρ {T₂ = NT.N-ProtoD T₂} (<:ₜ-data sub)
    with split-renTy-to-sub ρ {T₂ = T₂} sub
  ... | T₁′ , eqT , sub′
    rewrite eqT =
      NT.N-ProtoD T₁′ , refl , <:ₜ-data sub′

  split-renProto′-from-sub ⊕ ρ {P₂ = NT.N-ProtoP #c₂ ⊙ P₂} (<:ₚ′-proto {#c₁ = #c₁} #c⊆ sub)
    with split-renProto-from-sub ⊙ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-ProtoP #c₁ ⊙ P₁′ , refl , <:ₚ′-proto #c⊆ sub′
  split-renProto′-from-sub ⊕ ρ {P₂ = NT.N-Up T₂} (<:ₚ′-up sub)
    with split-renTy-from-sub ρ {T₂ = T₂} sub
  ... | T₁′ , eqT , sub′
    rewrite eqT =
      NT.N-Up T₁′ , refl , <:ₚ′-up sub′
  split-renProto′-from-sub ⊕ ρ {P₂ = NT.N-Var x} <:ₚ′-var =
    NT.N-Var x , refl , <:ₚ′-var

  split-renProto′-from-sub ⊝ ρ {P₂ = NT.N-ProtoP #c₂ ⊙ P₂} (<:ₚ′-proto {#c₂ = #c₁} #c⊆ sub)
    with split-renProto-to-sub ⊙ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-ProtoP #c₁ ⊙ P₁′ , refl , <:ₚ′-proto #c⊆ sub′
  split-renProto′-from-sub ⊝ ρ {P₂ = NT.N-Up T₂} (<:ₚ′-up sub)
    with split-renTy-to-sub ρ {T₂ = T₂} sub
  ... | T₁′ , eqT , sub′
    rewrite eqT =
      NT.N-Up T₁′ , refl , <:ₚ′-up sub′
  split-renProto′-from-sub ⊝ ρ {P₂ = NT.N-Var x} <:ₚ′-var =
    NT.N-Var x , refl , <:ₚ′-var

  split-renProto′-from-sub ⊘ ρ {P₂ = P₂} eq =
    P₂ , NT.nfProto′Ty-injective eq , refl

  split-renProto′-to-sub ⊕ ρ {P₂ = NT.N-ProtoP #c₂ ⊙ P₂} (<:ₚ′-proto {#c₂ = #c₁} #c⊆ sub)
    with split-renProto-to-sub ⊙ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-ProtoP #c₁ ⊙ P₁′ , refl , <:ₚ′-proto #c⊆ sub′
  split-renProto′-to-sub ⊕ ρ {P₂ = NT.N-Up T₂} (<:ₚ′-up sub)
    with split-renTy-to-sub ρ {T₂ = T₂} sub
  ... | T₁′ , eqT , sub′
    rewrite eqT =
      NT.N-Up T₁′ , refl , <:ₚ′-up sub′
  split-renProto′-to-sub ⊕ ρ {P₂ = NT.N-Var x} <:ₚ′-var =
    NT.N-Var x , refl , <:ₚ′-var

  split-renProto′-to-sub ⊝ ρ {P₂ = NT.N-ProtoP #c₂ ⊙ P₂} (<:ₚ′-proto {#c₁ = #c₁} #c⊆ sub)
    with split-renProto-from-sub ⊙ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-ProtoP #c₁ ⊙ P₁′ , refl , <:ₚ′-proto #c⊆ sub′
  split-renProto′-to-sub ⊝ ρ {P₂ = NT.N-Up T₂} (<:ₚ′-up sub)
    with split-renTy-from-sub ρ {T₂ = T₂} sub
  ... | T₁′ , eqT , sub′
    rewrite eqT =
      NT.N-Up T₁′ , refl , <:ₚ′-up sub′
  split-renProto′-to-sub ⊝ ρ {P₂ = NT.N-Var x} <:ₚ′-var =
    NT.N-Var x , refl , <:ₚ′-var

  split-renProto′-to-sub ⊘ ρ {P₂ = P₂} eq =
    P₂ , NT.nfProto′Ty-injective (sym eq) , refl

  split-renProto-from-sub ⊕ ρ {P₂ = NT.N-Normal P₂} (<:ₚ-plus sub)
    with split-renProto′-from-sub ⊕ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-Normal P₁′ , refl , <:ₚ-plus sub′
  split-renProto-from-sub ⊕ ρ {P₂ = NT.N-Minus P₂} (<:ₚ-minus sub)
    with split-renProto′-to-sub ⊕ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-Minus P₁′ , refl , <:ₚ-minus sub′

  split-renProto-from-sub ⊝ ρ {P₂ = NT.N-Normal P₂} (<:ₚ-plus sub)
    with split-renProto′-to-sub ⊕ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-Normal P₁′ , refl , <:ₚ-plus sub′
  split-renProto-from-sub ⊝ ρ {P₂ = NT.N-Minus P₂} (<:ₚ-minus sub)
    with split-renProto′-from-sub ⊕ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-Minus P₁′ , refl , <:ₚ-minus sub′

  split-renProto-from-sub ⊘ ρ {P₂ = P₂} eq =
    P₂ , NT.nfProtoTy-injective eq , refl

  split-renProto-to-sub ⊕ ρ {P₂ = NT.N-Normal P₂} (<:ₚ-plus sub)
    with split-renProto′-to-sub ⊕ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-Normal P₁′ , refl , <:ₚ-plus sub′
  split-renProto-to-sub ⊕ ρ {P₂ = NT.N-Minus P₂} (<:ₚ-minus sub)
    with split-renProto′-from-sub ⊕ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-Minus P₁′ , refl , <:ₚ-minus sub′

  split-renProto-to-sub ⊝ ρ {P₂ = NT.N-Normal P₂} (<:ₚ-plus sub)
    with split-renProto′-from-sub ⊕ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-Normal P₁′ , refl , <:ₚ-plus sub′
  split-renProto-to-sub ⊝ ρ {P₂ = NT.N-Minus P₂} (<:ₚ-minus sub)
    with split-renProto′-to-sub ⊕ ρ {P₂ = P₂} sub
  ... | P₁′ , eqP , sub′
    rewrite eqP =
      NT.N-Minus P₁′ , refl , <:ₚ-minus sub′

  split-renProto-to-sub ⊘ ρ {P₂ = P₂} eq =
    P₂ , NT.nfProtoTy-injective (sym eq) , refl

split-wkTy-from-sub :
  ∀ {Δ K pk m}
    {T₁ : NfTy (K ∷ Δ) (KV pk m)}
    {T₂ : NfTy Δ (KV pk m)}
  → T₁ <:ₜ wkNfTy {K′ = K} T₂
  → Σ (NfTy Δ (KV pk m)) λ T₁′ →
      (T₁ ≡ wkNfTy {K′ = K} T₁′) × (T₁′ <:ₜ T₂)
split-wkTy-from-sub {K = K} sub = split-renTy-from-sub (weakenᵣ K) sub

split-wkCtx-from-rel :
  ∀ {Δ n K} {Γw : Ctx (K ∷ Δ) n} {Γ : Ctx Δ n}
  → Γw <:Γ wkCtx {K = K} Γ
  → Σ (Ctx Δ n) λ Γ′ → (Γw ≡ wkCtx {K = K} Γ′) × (Γ′ <:Γ Γ)
split-wkCtx-from-rel {Γ = ∅} <:-[] =
  ∅ , refl , <:-[]
split-wkCtx-from-rel {K = K} {Γ = B-Used T ▻ Γ} (<:-used rel)
  with split-wkCtx-from-rel {K = K} {Γ = Γ} rel
... | Γ′ , eq , rel′ =
  (B-Used T ▻ Γ′) ,
  cong (λ X → B-Used (wkNfTy {K′ = K} T) ▻ X) eq ,
  <:-used rel′
split-wkCtx-from-rel
    {K = K}
    {Γ = B-Used {pk = pk} T ▻ Γ}
    (<:-sub-used sub rel)
  with split-wkTy-from-sub {K = K} sub
     | split-wkCtx-from-rel {K = K} {Γ = Γ} rel
... | T′ , eqT , sub′ | Γ′ , eqΓ , rel′
  rewrite eqT | eqΓ =
    (B-Used T′ ▻ Γ′) , refl , <:-sub-used sub′ rel′
split-wkCtx-from-rel {K = K} {Γ = B-Lin T ▻ Γ} (<:-lin rel)
  with split-wkCtx-from-rel {K = K} {Γ = Γ} rel
... | Γ′ , eq , rel′ =
  (B-Lin T ▻ Γ′) ,
  cong (λ X → B-Lin (wkNfTy {K′ = K} T) ▻ X) eq ,
  <:-lin rel′
split-wkCtx-from-rel
    {K = K}
    {Γ = B-Lin {pk = pk} T ▻ Γ}
    (<:-sub-lin sub rel)
  with split-wkTy-from-sub {K = K} sub
     | split-wkCtx-from-rel {K = K} {Γ = Γ} rel
... | T′ , eqT , sub′ | Γ′ , eqΓ , rel′
  rewrite eqT | eqΓ =
    (B-Lin T′ ▻ Γ′) , refl , <:-sub-lin sub′ rel′
split-wkCtx-from-rel
    {K = K}
    {Γ = B-Un {pk = pk} T ▻ Γ}
    (<:-sub-unr sub rel)
  with split-wkTy-from-sub {K = K} sub
     | split-wkCtx-from-rel {K = K} {Γ = Γ} rel
... | T′ , eqT , sub′ | Γ′ , eqΓ , rel′
  rewrite eqT | eqΓ =
    (B-Un T′ ▻ Γ′) , refl , <:-sub-unr sub′ rel′
split-wkCtx-from-rel {K = K} {Γ = B-Un T ▻ Γ} (<:-un rel)
  with split-wkCtx-from-rel {K = K} {Γ = Γ} rel
... | Γ′ , eq , rel′ =
  (B-Un T ▻ Γ′) ,
  cong (λ X → B-Un (wkNfTy {K′ = K} T) ▻ X) eq ,
  <:-un rel′

match-input-subtype-inversion :
  ∀ {Δ k}
    {ss : Subset.Subset k} {v : Variance}
    {P : NfTy Δ KP} {S : NfTy Δ SLin}
    {M : NfTy Δ SLin}
  → normalTyOf M <:ₜ normalTyOf (MatchBranchInput ss v P S)
  → Σ (Subset.Subset k) λ ss′ →
      Σ (NfTy Δ KP) λ P′ →
      Σ (NfTy Δ SLin) λ S′ →
        (M ≡ MatchBranchInput ss′ v P′ S′)
        × (ss′ Subset.⊆ ss)
        × (P′ <<:ₚ[ v ] P)
        × (S′ <:ₜ S)
match-input-subtype-inversion
    {M = NT.N-Msg ⊝ (NT.N-ProtoP ss′ v P′) S′}
    (<:ₜ-msg {p = ⊝} (<:ₚ′-proto ss′⊆ss P′<:P) S′<:S) =
  ss′ , P′ , S′ , refl , ss′⊆ss , P′<:P , S′<:S

postulate
  match-output-subtype :
    ∀ {Δ k}
      {ss : Subset.Subset (suc k)} {v : Variance}
      {P P′ : NfTy Δ KP} {S S′ : NfTy Δ SLin}
      (i : Fin (suc k)) (i∈ : i Subset.∈ ss)
    → P′ <<:ₚ[ v ] P
    → S′ <:ₜ S
    → MatchBranchOutput ss v P′ S′ i i∈ <:ₜ MatchBranchOutput ss v P S i i∈

postulate
  cohere-strengthened-branches :
    ∀ {Δ n k}
      {Γmid′ Γmid Γ₃ : Ctx Δ n}
      {ssbranches : Subset.Subset (suc k)} {v : Variance}
      {P P′ : NfTy Δ KP} {S S′ : NfTy Δ SLin}
      {branches : (i : Fin (suc k)) → i Subset.∈ ssbranches → Expr Δ (suc n)}
      {V : (i : Fin (suc k)) → i Subset.∈ ssbranches → NfTy Δ TLin}
    → ((i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) →
         Σ (NfTy Δ TLin) λ V′i →
           Σ (Ctx Δ n) λ Γ₃i →
             ((MatchBranchOutput ssbranches v P′ S′ i i∈ ∷ˡ Γmid′)
                ⊢ branches i i∈ ⇒ V′i ⊣ used∷ {T = MatchBranchOutput ssbranches v P′ S′ i i∈} Γ₃i)
             × (V′i <:ₜ V i i∈)
             × (Γ₃i <:Γ Γ₃))
    → Σ (Ctx Δ n) λ Γ₃′ →
        Σ ((i : Fin (suc k)) → i Subset.∈ ssbranches → NfTy Δ TLin) λ V′ →
          (((i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) →
              (MatchBranchOutput ssbranches v P′ S′ i i∈ ∷ˡ Γmid′)
                ⊢ branches i i∈ ⇒ V′ i i∈ ⊣ used∷ {T = MatchBranchOutput ssbranches v P′ S′ i i∈} Γ₃′))
          × ((i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) → V′ i i∈ <:ₜ V i i∈)
          × (Γ₃′ <:Γ Γ₃)

postulate
  branchjoin⁺-monotone :
    ∀ {Δ k}
      {ss : Subset.Subset k}
      {V V′ : (i : Fin k) → i Subset.∈ ss → NfTy Δ TLin}
      {U : NfTy Δ TLin}
      {sub : (i : Fin k) → (i∈ : i Subset.∈ ss) → V i i∈ <:ₜ U}
    → BranchJoin⁺ ss V ≡ just (U , sub)
    → ((i : Fin k) → (i∈ : i Subset.∈ ss) → V′ i i∈ <:ₜ V i i∈)
    → Σ (NfTy Δ TLin) λ U′ →
        Σ ((i : Fin k) → (i∈ : i Subset.∈ ss) → V′ i i∈ <:ₜ U′) λ sub′ →
          (BranchJoin⁺ ss V′ ≡ just (U′ , sub′))
          × (U′ <:ₜ U)

mutual

  strengthen-value-abs :
    ∀ {Δ n}
      {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
      {T : Ty Δ TLin} {U : NfTy Δ TLin} {e : Expr Δ (suc n)}
    → Γ₁ <:Γ Γ₂
    → Γ₂ ⊢ᵥ V-Abs T e ⇒ linArrNf (normalizeTy T) U ⊣ Γ₃
    → Σ (NfTy Δ TLin) λ W′ →
      Σ (Ctx Δ n) λ Γ₃′ →
        (Γ₁ ⊢ᵥ V-Abs T e ⇒ W′ ⊣ Γ₃′)
        × (normalTyOf W′ <:ₜ normalTyOf (linArrNf (normalizeTy T) U)
        × Γ₃′ <:Γ Γ₃)

  strengthen-value-abs {Γ₁ = Γ₁} rel (TV-Abs {T = T} {U = U} {e = e} d) =
    let U′ , Γbody′ , d′ , U′<:U , relBody =
          strengthen-synth (<:-sub-lin (<:ₜ-refl (normalizeTy T)) rel) d in
    let Tused , Γ₂′ , eqBody , rel₂ = used-tail-<:Γ relBody in
    let eqHead : normalizeTy T ≡ Tused
        eqHead =
          lin-used-head-rigid
            (subst
              (λ Γ → (normalizeTy T ∷ˡ Γ₁) ⊢ e ⇒ U′ ⊣ Γ)
              eqBody
              d′) in
    let eqBody′ :
          Γbody′ ≡ used∷ {T = normalizeTy T} Γ₂′
        eqBody′ =
          trans
            eqBody
            (cong (λ X → used∷ {T = X} Γ₂′) (sym eqHead)) in
    linArrNf (normalizeTy T) U′ , Γ₂′ ,
    TV-Abs (subst (λ Γ → (normalizeTy T ∷ˡ Γ₁) ⊢ e ⇒ U′ ⊣ Γ) eqBody′ d′) ,
    <:ₜ-arrow (<:ₜ-refl (normalizeTy T)) U′<:U ,
    rel₂

  strengthen-value-tabs :
    ∀ {Δ n K m}
      {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
      {v : Value (K ∷ Δ) n}
      {T : NfTy (K ∷ Δ) (KV KT m)}
    → Γ₁ <:Γ Γ₂
    → wkCtx {K = K} Γ₂ ⊢ᵥ v ⇒ T ⊣ wkCtx Γ₃
    → Σ (NfTy (K ∷ Δ) (KV KT m)) λ T′ →
      Σ (Ctx Δ n) λ Γ₃′ →
        (wkCtx {K = K} Γ₁ ⊢ᵥ v ⇒ T′ ⊣ wkCtx Γ₃′)
        × (normalTyOf T′ <:ₜ normalTyOf T
        × Γ₃′ <:Γ Γ₃)

  strengthen-value-tabs {K = K} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} {v = v} {T = T} rel d =
    let T′ , Γw′ , d′ , T′<:T , rel′ = strengthen-value (<:Γ-wk {K = K} rel) d in
    let Γ₃′ , eqw , rel₃ = split-wkCtx-from-rel {K = K} rel′ in
    T′ , Γ₃′ ,
    subst (λ X → wkCtx {K = K} Γ₁ ⊢ᵥ v ⇒ T′ ⊣ X) eqw d′ ,
    T′<:T ,
    rel₃

  strengthen-value :
    ∀ {Δ n pk m}
      {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
      {T : NfTy Δ (KV pk m)}
      {v : Value Δ n}
    → Γ₁ <:Γ Γ₂
    → Γ₂ ⊢ᵥ v ⇒ T ⊣ Γ₃
    → Σ (NfTy Δ (KV pk m)) λ T′ →
      Σ (Ctx Δ n) λ Γ₃′ →
        (Γ₁ ⊢ᵥ v ⇒ T′ ⊣ Γ₃′)
        × (normalTyOf T′ <:ₜ normalTyOf T
        × Γ₃′ <:Γ Γ₃)

  strengthen-value {Γ₁ = Γ₁} rel (TV-Const cT) =
    _ , Γ₁ , TV-Const cT , <:ₜ-refl _ , rel
  strengthen-value rel (TV-Var-Lin take) = strengthen-var-lin rel take
  strengthen-value rel (TV-Var-Un x∈) = strengthen-var-un rel x∈
  strengthen-value rel d@(TV-Abs _) = strengthen-value-abs rel d
  strengthen-value {Γ₁ = Γ₁} rel (TV-Rec {T = T} {U = U} d) =
    unArrNf (normalizeTy T) (normalizeTy U) , Γ₁ ,
    TV-Rec (strengthen-value-rec {T = T} {U = U} rel d) ,
    <:ₜ-refl (unArrNf (normalizeTy T) (normalizeTy U)) ,
    rel
  strengthen-value rel (TV-TAbs {K = K} {T = T} d) =
    let T′ , Γ₃′ , d′ , T′<:T , rel′ = strengthen-value-tabs rel d in
    polyNf T′ , Γ₃′ , TV-TAbs d′ , <:ₜ-poly T′<:T , rel′
  strengthen-value rel (TV-Pair {T = T} {U = U} d₁ d₂) =
    let T′ , Γ₂′ , d₁′ , T′<:T , rel₂ = strengthen-value rel d₁ in
    let U′ , Γ₃′ , d₂′ , U′<:U , rel₃ = strengthen-value rel₂ d₂ in
    pairNf T′ U′ , Γ₃′ ,
    TV-Pair d₁′ d₂′ ,
    <:ₜ-pair T′<:T U′<:U ,
    rel₃
  strengthen-value {Γ₁ = Γ₁} rel TV-Receive₁ = _ , Γ₁ , TV-Receive₁ , <:ₜ-refl _ , rel
  strengthen-value {Γ₁ = Γ₁} rel TV-Receive₂ = _ , Γ₁ , TV-Receive₂ , <:ₜ-refl _ , rel
  strengthen-value {Γ₁ = Γ₁} rel TV-Send₁ = _ , Γ₁ , TV-Send₁ , <:ₜ-refl _ , rel
  strengthen-value {Γ₁ = Γ₁} rel TV-Send₂ = _ , Γ₁ , TV-Send₂ , <:ₜ-refl _ , rel
  strengthen-value {Γ₁ = Γ₁} rel TV-Select₁ = _ , Γ₁ , TV-Select₁ , <:ₜ-refl _ , rel
  strengthen-value {Γ₁ = Γ₁} rel TV-Select₂ = _ , Γ₁ , TV-Select₂ , <:ₜ-refl _ , rel

  strengthen-synth :
    ∀ {Δ n pk m}
      {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
      {V : NfTy Δ (KV pk m)}
      {e : Expr Δ n}
    → Γ₁ <:Γ Γ₂
    → Γ₂ ⊢ e ⇒ V ⊣ Γ₃
    → Σ (NfTy Δ (KV pk m)) λ V′ →
      Σ (Ctx Δ n) λ Γ₃′ →
        (Γ₁ ⊢ e ⇒ V′ ⊣ Γ₃′)
        × (normalTyOf V′ <:ₜ normalTyOf V
        × Γ₃′ <:Γ Γ₃)

  strengthen-synth-match :
    ∀ {Δ n k}
      {Γ₁ Γ₂ Γmid Γ₃ : Ctx Δ n}
      {ss : Subset.Subset (suc k)}
      {ssbranches : Subset.Subset (suc k)} {incl : ss Subset.⊆ ssbranches}
      {ne : Subset.Nonempty ssbranches} {v : Variance}
      {P : NfTy Δ KP} {S : NfTy Δ SLin} {U : NfTy Δ TLin}
      {e : Expr Δ n}
      {branches : (i : Fin (suc k)) → i Subset.∈ ssbranches → Expr Δ (suc n)}
      {V : (i : Fin (suc k)) → i Subset.∈ ssbranches → NfTy Δ TLin}
      {sub : (i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) → V i i∈ <:ₜ U}
    → Γ₁ <:Γ Γ₂
    → Γ₂ ⊢ e ⇒ MatchBranchInput ss v P S ⊣ Γmid
    → ((i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) → (MatchBranchOutput ssbranches v P S i i∈ ∷ˡ Γmid) ⊢ branches i i∈ ⇒ V i i∈ ⊣ used∷ Γ₃)
    → BranchJoin⁺ ssbranches V ≡ just (U , sub)
    → Σ (NfTy Δ TLin) λ U′ →
      Σ (Ctx Δ n) λ Γ₃′ →
        (Γ₁ ⊢ E-Match {ss = ssbranches} e ne branches ⇒ U′ ⊣ Γ₃′)
        × (normalTyOf U′ <:ₜ normalTyOf U
        × Γ₃′ <:Γ Γ₃)
  strengthen-synth-match
      {Γmid = Γmid} {Γ₃ = Γ₃}
      {ss = ss} {ssbranches = ssbranches} {incl = incl}
      {v = v} {P = P} {S = S} {U = U}
      {branches = branches} {V = V} {sub = sub}
      rel d bs j
    with strengthen-synth rel d
  ... | M′ , Γmid′ , d′ , subIn , relmid
    with match-input-subtype-inversion {ss = ss} {v = v} {P = P} {S = S} {M = M′} subIn
  ... | ss′ , P′ , S′ , eqIn , ss′⊆ss , P′<:P , S′<:S
    rewrite eqIn
    with cohere-strengthened-branches
           {Γmid′ = Γmid′} {Γmid = Γmid} {Γ₃ = Γ₃}
           {ssbranches = ssbranches} {v = v}
           {P = P} {P′ = P′} {S = S} {S′ = S′}
           {branches = branches} {V = V}
           (λ i i∈ →
             let V′i , Γout′ , d′ , V′i<:V , relout =
                   strengthen-synth
                     (<:-sub-lin (match-output-subtype i i∈ P′<:P S′<:S) relmid)
                     (bs i i∈)
             in
             let Tout , Γ₃′ , eqUsed , rel₃ = used-tail-<:Γ relout
             in
             let eqHead : MatchBranchOutput ssbranches v P′ S′ i i∈ ≡ Tout
                 eqHead =
                   lin-used-head-rigid
                     (subst
                       (λ Γ →
                         (MatchBranchOutput ssbranches v P′ S′ i i∈ ∷ˡ Γmid′)
                           ⊢ branches i i∈ ⇒ V′i ⊣ Γ)
                       eqUsed
                       d′)
             in
             let eqUsed′ :
                   Γout′ ≡ used∷ {T = MatchBranchOutput ssbranches v P′ S′ i i∈} Γ₃′
                 eqUsed′ =
                   trans
                     eqUsed
                     (cong (λ X → used∷ {T = X} Γ₃′) (sym eqHead))
             in
             V′i , Γ₃′ ,
             subst
               (λ Γ → (MatchBranchOutput ssbranches v P′ S′ i i∈ ∷ˡ Γmid′) ⊢ branches i i∈ ⇒ V′i ⊣ Γ)
               eqUsed′
               d′ ,
             V′i<:V ,
             rel₃)
  ... | Γ₃′ , V′ , bs′ , V′<:V , rel₃
    with branchjoin⁺-monotone
           {ss = ssbranches}
           {V = V}
           {V′ = V′}
           {U = U}
           {sub = sub}
           j
           V′<:V
  ... | U′ , sub′ , bj′ , U′<:U =
    U′ , Γ₃′ ,
    T-Match
      {ss = ss′}
      {incl = λ {i} i∈ → incl (ss′⊆ss i∈)}
      {V = V′}
      {sub = sub′}
      d′
      bs′
      bj′ ,
    U′<:U ,
    rel₃

  strengthen-synth rel (T-Val d) =
    let T′ , Γ₃′ , d′ , sub , rel′ = strengthen-value rel d in
    T′ , Γ₃′ , T-Val d′ , sub , rel′
  strengthen-synth rel (T-Pair {T = T} {U = U} d₁ d₂) =
    let T′ , Γ₂′ , d₁′ , T′<:T , rel₂ = strengthen-synth rel d₁ in
    let U′ , Γ₃′ , d₂′ , U′<:U , rel₃ = strengthen-synth rel₂ d₂ in
    pairNf T′ U′ , Γ₃′ ,
    T-Pair d₁′ d₂′ ,
    <:ₜ-pair T′<:T U′<:U ,
    rel₃
  strengthen-synth {Γ₁ = Γ₁} rel (T-App {e₁ = e₁} {m = m} {T = T} {U = U} d₁ d₂) =
    let F′ , Γ₂′ , d₁′ , subF , rel₂ = strengthen-synth rel d₁ in
    let A′ , V′ , eqF , T<:A′ , V′<:U = arrow-subtype-inversion {m = m} {A = T} {B = U} {X = F′} subF in
    let Γ₃′ , d₂′ , rel₃ = strengthen-check rel₂ d₂ in
    V′ , Γ₃′ ,
    T-App
      (subst (λ X → Γ₁ ⊢ e₁ ⇒ X ⊣ Γ₂′) eqF d₁′)
      (check-subsumption d₂′ T<:A′) ,
    V′<:U ,
    rel₃
  strengthen-synth rel (T-LetUnit d₁ d₂) =
    let Γ₂′ , d₁′ , rel₂ = strengthen-check rel d₁ in
    let V′ , Γ₃′ , d₂′ , sub , rel₃ = strengthen-synth rel₂ d₂ in
    V′ , Γ₃′ , T-LetUnit d₁′ d₂′ , sub , rel₃
  strengthen-synth {Γ₁ = Γ₁} rel (T-LetPair {T = T} {U = U} {e₁ = e₁} {e₂ = e₂} d₁ d₂) =
    let X′ , Γ₂′ , d₁′ , subPair , rel₂ = strengthen-synth rel d₁ in
    let T′ , U′ , eqPair , T′<:T , U′<:U = pair-subtype-inversion {T = T} {U = U} {X = X′} subPair in
    let V′ , Γbody′ , d₂′ , subV , relBody = strengthen-synth (<:-sub-lin T′<:T (<:-sub-lin U′<:U rel₂)) d₂ in
    let Tused₁ , Γused₁ , eqUsed₁ , relUsed₁ = used-tail-<:Γ relBody in
    let Tused₂ , Γ₃′ , eqUsed₂ , rel₃ = used-tail-<:Γ relUsed₁ in
    let eqBodyRaw : Γbody′ ≡ used∷ {T = Tused₁} (used∷ {T = Tused₂} Γ₃′)
        eqBodyRaw = trans eqUsed₁ (cong (used∷ {T = Tused₁}) eqUsed₂) in
    let eqHeads :
          (T′ ≡ Tused₁) × (U′ ≡ Tused₂)
        eqHeads =
          lin2-used2-head-rigid
            (subst
              (λ Γ → (T′ ∷ˡ (U′ ∷ˡ Γ₂′)) ⊢ e₂ ⇒ V′ ⊣ Γ)
              eqBodyRaw
              d₂′) in
    let eqBody : Γbody′ ≡ used∷ {T = T′} (used∷ {T = U′} Γ₃′)
        eqBody =
          trans
            eqBodyRaw
            (cong₂
              (λ A B → used∷ {T = A} (used∷ {T = B} Γ₃′))
              (sym (proj₁ eqHeads))
              (sym (proj₂ eqHeads))) in
    V′ , Γ₃′ ,
    T-LetPair
      (subst (λ X → Γ₁ ⊢ e₁ ⇒ X ⊣ Γ₂′) eqPair d₁′)
      (subst (λ Γ → (T′ ∷ˡ (U′ ∷ˡ Γ₂′)) ⊢ e₂ ⇒ V′ ⊣ Γ) eqBody d₂′) ,
    subV ,
    rel₃
  strengthen-synth rel (T-Match {ss = ss} {incl = incl} d bs j) =
    strengthen-synth-match {ss = ss} {incl = incl} rel d bs j
  strengthen-synth {Γ₁ = Γ₁} rel (T-TApp {K = K} {T = T} {U = U} d) =
    let P′ , Γ₂′ , d′ , subP , rel₂ = strengthen-synth rel d in
    let T′ , eqPoly , T′<:T = poly-subtype-inversion {K = K} {X = P′} {T = T} subP in
    substNFTy T′ (normalizeTy U) , Γ₂′ ,
    T-TApp (subst (λ X → Γ₁ ⊢ _ ⇒ X ⊣ Γ₂′) eqPoly d′) ,
    subst-preserves-<:ₜ T′<:T ,
    rel₂

  strengthen-check :
    ∀ {Δ n pk m}
      {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
      {T : NfTy Δ (KV pk m)}
      {e : Expr Δ n}
    → Γ₁ <:Γ Γ₂
    → Γ₂ ⊢ e ⇐ T ⊣ Γ₃
    → Σ (Ctx Δ n) λ Γ₃′ →
        (Γ₁ ⊢ e ⇐ T ⊣ Γ₃′)
        × Γ₃′ <:Γ Γ₃

  strengthen-check rel (T-Check d sub) =
    let U′ , Γ₃′ , d′ , sub′ , rel′ = strengthen-synth rel d in
    Γ₃′ , T-Check d′ (<:ₜ-trans sub′ sub) , rel′

strengthen-match-branch :
  ∀ {Δ n k}
    {Γmid′ Γmid Γ₃ : Ctx Δ n}
    {ssbranches : Subset.Subset (suc k)} {v : Variance}
    {P P′ : NfTy Δ KP} {S S′ : NfTy Δ SLin}
    {branches : (i : Fin (suc k)) → i Subset.∈ ssbranches → Expr Δ (suc n)}
    {V : (i : Fin (suc k)) → i Subset.∈ ssbranches → NfTy Δ TLin}
    (i : Fin (suc k)) (i∈ : i Subset.∈ ssbranches)
  → P′ <<:ₚ[ v ] P
  → S′ <:ₜ S
  → Γmid′ <:Γ Γmid
  → (MatchBranchOutput ssbranches v P S i i∈ ∷ˡ Γmid)
      ⊢ branches i i∈ ⇒ V i i∈
      ⊣ used∷ {T = MatchBranchOutput ssbranches v P S i i∈} Γ₃
  → Σ (NfTy Δ TLin) λ V′i →
      Σ (Ctx Δ n) λ Γ₃′ →
        ((MatchBranchOutput ssbranches v P′ S′ i i∈ ∷ˡ Γmid′)
          ⊢ branches i i∈ ⇒ V′i ⊣ used∷ {T = MatchBranchOutput ssbranches v P′ S′ i i∈} Γ₃′)
        × (V′i <:ₜ V i i∈)
        × (Γ₃′ <:Γ Γ₃)
strengthen-match-branch
  {Γmid′ = Γmid′}
  {ssbranches = ssbranches}
  {v = v}
  {P′ = P′} {S′ = S′}
  {branches = branches}
  i i∈ P′<:P S′<:S relmid d =
  let V′i , Γout′ , d′ , V′i<:V , relout =
        strengthen-synth
          (<:-sub-lin (match-output-subtype i i∈ P′<:P S′<:S) relmid)
          d
  in
  let Tout , Γ₃′ , eqUsed , rel₃ = used-tail-<:Γ relout
  in
  let eqHead : MatchBranchOutput ssbranches v P′ S′ i i∈ ≡ Tout
      eqHead =
        lin-used-head-rigid
          (subst
            (λ Γ → (MatchBranchOutput ssbranches v P′ S′ i i∈ ∷ˡ Γmid′) ⊢ branches i i∈ ⇒ V′i ⊣ Γ)
            eqUsed
            d′)
  in
  let eqUsed′ :
        Γout′ ≡ used∷ {T = MatchBranchOutput ssbranches v P′ S′ i i∈} Γ₃′
      eqUsed′ =
        trans
          eqUsed
          (cong (λ X → used∷ {T = X} Γ₃′) (sym eqHead))
  in
  V′i , Γ₃′ ,
  subst
    (λ Γ → (MatchBranchOutput ssbranches v P′ S′ i i∈ ∷ˡ Γmid′) ⊢ branches i i∈ ⇒ V′i ⊣ Γ)
    eqUsed′
    d′ ,
  V′i<:V ,
  rel₃

strengthen-match-branches :
  ∀ {Δ n k}
    {Γmid′ Γmid Γ₃ : Ctx Δ n}
    {ssbranches : Subset.Subset (suc k)} {v : Variance}
    {P P′ : NfTy Δ KP} {S S′ : NfTy Δ SLin}
    {branches : (i : Fin (suc k)) → i Subset.∈ ssbranches → Expr Δ (suc n)}
    {V : (i : Fin (suc k)) → i Subset.∈ ssbranches → NfTy Δ TLin}
  → P′ <<:ₚ[ v ] P
  → S′ <:ₜ S
  → Γmid′ <:Γ Γmid
  → ((i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) → (MatchBranchOutput ssbranches v P S i i∈ ∷ˡ Γmid) ⊢ branches i i∈ ⇒ V i i∈ ⊣ used∷ Γ₃)
  → Σ (Ctx Δ n) λ Γ₃′ →
      Σ ((i : Fin (suc k)) → i Subset.∈ ssbranches → NfTy Δ TLin) λ V′ →
        (((i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) → (MatchBranchOutput ssbranches v P′ S′ i i∈ ∷ˡ Γmid′) ⊢ branches i i∈ ⇒ V′ i i∈ ⊣ used∷ Γ₃′))
        × ((i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) → V′ i i∈ <:ₜ V i i∈)
        × (Γ₃′ <:Γ Γ₃)
strengthen-match-branches
  {Γmid′ = Γmid′} {Γmid = Γmid} {Γ₃ = Γ₃}
  {ssbranches = ssbranches} {v = v}
  {P = P} {P′ = P′} {S = S} {S′ = S′}
  {branches = branches} {V = V}
  P′<:P S′<:S relmid bs =
  cohere-strengthened-branches
    {Γmid′ = Γmid′} {Γmid = Γmid} {Γ₃ = Γ₃}
    {ssbranches = ssbranches} {v = v}
    {P = P} {P′ = P′} {S = S} {S′ = S′}
    {branches = branches} {V = V}
    (λ i i∈ →
      strengthen-match-branch
        {Γmid′ = Γmid′} {Γmid = Γmid} {Γ₃ = Γ₃}
        {ssbranches = ssbranches} {v = v}
        {P = P} {P′ = P′} {S = S} {S′ = S′}
        {branches = branches} {V = V}
        i i∈ P′<:P S′<:S relmid (bs i i∈))
