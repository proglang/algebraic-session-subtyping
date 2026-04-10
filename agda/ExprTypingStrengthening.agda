module ExprTypingStrengthening where

open import Duality
open import Variance
open import Kinds
open import Types
open import Subtyping
open import TypesProtocolConstructors
import NormalTypes as NT
open import AlgorithmicNFMerge using (joinₜ)
open import AlgorithmicNFSubtyping using
  ( _<:ₜ_
  ; <:ₜ-trans
  ; <:ₜ-refl
  ; <:ₜ-arrow
  ; <:ₜ-pair
  ; <:ₜ-poly
  )
open import AlgorithmicNFSubstitution using (subst-preserves-<:ₜ)
open import NormalTypesSubstitution using (substNFTy)

open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_; here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary using (¬_; Dec; yes; no; map′)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; inspect; Reveal_·_is_)

open import ExprNormalTyping
open import ExprSyntax hiding (Ctx)


data _<:Γ_ : ∀ {Δ n} (Γ₁ : Ctx Δ n) (Γ₂ : Ctx Δ n) → Set where

  <:-[] : ∀ {Δ} → ∅ {Δ} <:Γ ∅

  <:-used :
      ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
    → Γ₁ <:Γ Γ₂
    → (B-Used ▻ Γ₁) <:Γ (B-Used ▻ Γ₂)

  <:-lin :
      ∀ {Δ n K}
      {T : NfTy Δ K}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ₁ <:Γ Γ₂
    → (B-Lin T ▻ Γ₁) <:Γ (B-Lin T ▻ Γ₂)

  <:-sub-lin :
      ∀ {Δ n pk m}
      {T₁ T₂ : NfTy Δ (KV pk m)}
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
      ∀ {Δ n K}
      {T : NfTy Δ K}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ₁ <:Γ Γ₂
    → (B-Un T ▻ Γ₁) <:Γ (B-Un T ▻ Γ₂)


<:Γ-refl : ∀ {Δ n} {Γ : Ctx Δ n} → Γ <:Γ Γ
<:Γ-refl {Γ = ∅} = <:-[]
<:Γ-refl {Γ = B-Used ▻ Γ} = <:-used <:Γ-refl
<:Γ-refl {Γ = B-Lin T ▻ Γ} = <:-lin <:Γ-refl
<:Γ-refl {Γ = B-Un T ▻ Γ} = <:-un <:Γ-refl

used-tail-<:Γ :
  ∀ {Δ n} {Γ₁ : Ctx Δ (suc n)} {Γ₂ : Ctx Δ n}
  → Γ₁ <:Γ (used∷ Γ₂)
  → Σ (Ctx Δ n) λ Γ₁′ → Γ₁ ≡ used∷ Γ₁′ × Γ₁′ <:Γ Γ₂
used-tail-<:Γ (<:-used rel) = _ , refl , rel

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

strengthen-take :
  ∀ {Δ n pk m}
    {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
    {x : Fin n} {T : NfTy Δ (KV pk m)}
  → Γ₁ <:Γ Γ₂
  → Γ₂ ⊢ˡ x ∶ T ⊣ Γ₃
  → Σ (NfTy Δ (KV pk m)) λ T′ →
      Σ (Ctx Δ n) λ Γ₃′ →
        (Γ₁ ⊢ˡ x ∶ T′ ⊣ Γ₃′)
        × (normalTyOf T′ <:ₜ normalTyOf T
        × Γ₃′ <:Γ Γ₃)
strengthen-take (<:-sub-lin sub rel) take-here =
  _ , _ , take-here , sub , <:-used rel
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

strengthen-var-lin :
  ∀ {Δ n pk m}
    {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
    {x : Fin n} {T : NfTy Δ (KV pk m)}
  → Γ₁ <:Γ Γ₂
  → Γ₂ ⊢ˡ x ∶ T ⊣ Γ₃
  → Σ (NfTy Δ (KV pk m)) λ T′ →
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

postulate
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

  strengthen-synth-match :
    ∀ {Δ n k}
      {Γ₁ Γ₂ Γmid Γ₃ : Ctx Δ n}
      {ss : Subset.Subset (suc k)} {ne : Subset.Nonempty ss} {v : Variance}
      {P : NfTy Δ KP} {S : NfTy Δ SLin} {U : NfTy Δ TLin}
      {e : Expr Δ n}
      {branches : (i : Fin (suc k)) → i Subset.∈ ss → Expr Δ (suc n)}
      {V : (i : Fin (suc k)) → i Subset.∈ ss → NfTy Δ TLin}
      {sub : (i : Fin (suc k)) → (i∈ : i Subset.∈ ss) → V i i∈ <:ₜ U}
    → Γ₁ <:Γ Γ₂
    → Γ₂ ⊢ e ⇒ MatchBranchInput ss v P S ⊣ Γmid
    → ((i : Fin (suc k)) → (i∈ : i Subset.∈ ss) → (MatchBranchOutput ss v P S i i∈ ∷ˡ Γmid) ⊢ branches i i∈ ⇒ V i i∈ ⊣ used∷ Γ₃)
    → BranchJoin⁺ ss V ≡ just (U , sub)
    → Σ (NfTy Δ TLin) λ U′ →
      Σ (Ctx Δ n) λ Γ₃′ →
        (Γ₁ ⊢ E-Match e ne branches ⇒ U′ ⊣ Γ₃′)
        × (normalTyOf U′ <:ₜ normalTyOf U
        × Γ₃′ <:Γ Γ₃)


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
    let Γ₂′ , eqBody , rel₂ = used-tail-<:Γ relBody in
    linArrNf (normalizeTy T) U′ , Γ₂′ ,
    TV-Abs (subst (λ Γ → (normalizeTy T ∷ˡ Γ₁) ⊢ e ⇒ U′ ⊣ Γ) eqBody d′) ,
    <:ₜ-arrow (<:ₜ-refl (normalizeTy T)) U′<:U ,
    rel₂

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
  strengthen-value rel (TV-Send₃ {T = T} {S = S} d) =
    let Γ₂′ , d′ , rel′ = strengthen-check rel d in
    sendResultNf (normalizeTy T) (normalizeTy S) , Γ₂′ ,
    TV-Send₃ d′ ,
    <:ₜ-refl _ ,
    rel′
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
    let Γused₁ , eqUsed₁ , relUsed₁ = used-tail-<:Γ relBody in
    let Γ₃′ , eqUsed₂ , rel₃ = used-tail-<:Γ relUsed₁ in
    let eqBody : Γbody′ ≡ used∷ (used∷ Γ₃′)
        eqBody = trans eqUsed₁ (cong used∷ eqUsed₂) in
    V′ , Γ₃′ ,
    T-LetPair
      (subst (λ X → Γ₁ ⊢ e₁ ⇒ X ⊣ Γ₂′) eqPair d₁′)
      (subst (λ Γ → (T′ ∷ˡ (U′ ∷ˡ Γ₂′)) ⊢ e₂ ⇒ V′ ⊣ Γ) eqBody d₂′) ,
    subV ,
    rel₃
  strengthen-synth rel (T-Match {ss = ss} {ne = ne} {v = v} {P = P} {S = S} {U = U} d bs j) =
    strengthen-synth-match rel d bs j
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
