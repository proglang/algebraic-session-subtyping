module ExprContextShape where

open import Data.Fin using (Fin)
import Data.Fin.Subset as Subset
open import Data.List using (List)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (Σ; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Kinds
open import ExprSyntax using (NfTy; Expr; Value)
open import ExprNormalTyping
open import ExprContextProperties using (allUsedCtx)

infix 4 _~Ctx_

data _~Ctx_ {Δ : List Kind} : {n : ℕ} → Ctx Δ n → Ctx Δ n → Set where
  ∅~∅ : ∅ ~Ctx ∅
  Lin~Lin : ∀ {n pk} {Γ₁ Γ₂ : Ctx Δ n} {T : NfTy Δ (KV pk Lin)}
    → Γ₁ ~Ctx Γ₂
    → (B-Lin T ▻ Γ₁) ~Ctx (B-Lin T ▻ Γ₂)
  Un~Un : ∀ {n pk} {Γ₁ Γ₂ : Ctx Δ n} {T : NfTy Δ (KV pk Un)}
    → Γ₁ ~Ctx Γ₂
    → (B-Un T ▻ Γ₁) ~Ctx (B-Un T ▻ Γ₂)
  Lin~Used : ∀ {n pk} {Γ₁ Γ₂ : Ctx Δ n} {T : NfTy Δ (KV pk Lin)}
    → Γ₁ ~Ctx Γ₂
    → (B-Lin T ▻ Γ₁) ~Ctx (B-Used T ▻ Γ₂)
  Used~Used : ∀ {n pk} {Γ₁ Γ₂ : Ctx Δ n} {T : NfTy Δ (KV pk Lin)}
    → Γ₁ ~Ctx Γ₂
    → (B-Used T ▻ Γ₁) ~Ctx (B-Used T ▻ Γ₂)

~Ctx-refl : ∀ {Δ n} (Γ : Ctx Δ n) → Γ ~Ctx Γ
~Ctx-refl {n = zero} ∅ = ∅~∅
~Ctx-refl (B-Lin T ▻ Γ) = Lin~Lin (~Ctx-refl Γ)
~Ctx-refl (B-Un T ▻ Γ) = Un~Un (~Ctx-refl Γ)
~Ctx-refl (B-Used T ▻ Γ) = Used~Used (~Ctx-refl Γ)

~Ctx-trans :
  ∀ {Δ n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
  → Γ₁ ~Ctx Γ₂
  → Γ₂ ~Ctx Γ₃
  → Γ₁ ~Ctx Γ₃
~Ctx-trans ∅~∅ ∅~∅ = ∅~∅
~Ctx-trans (Lin~Lin s₁) (Lin~Lin s₂) = Lin~Lin (~Ctx-trans s₁ s₂)
~Ctx-trans (Lin~Lin s₁) (Lin~Used s₂) = Lin~Used (~Ctx-trans s₁ s₂)
~Ctx-trans (Un~Un s₁) (Un~Un s₂) = Un~Un (~Ctx-trans s₁ s₂)
~Ctx-trans (Lin~Used s₁) (Used~Used s₂) = Lin~Used (~Ctx-trans s₁ s₂)
~Ctx-trans (Used~Used s₁) (Used~Used s₂) = Used~Used (~Ctx-trans s₁ s₂)

~Ctx-allUsedCtx :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
  → Γ₁ ~Ctx Γ₂
  → allUsedCtx Γ₁ ≡ allUsedCtx Γ₂
~Ctx-allUsedCtx ∅~∅ = refl
~Ctx-allUsedCtx (Lin~Lin s) = cong (B-Used _ ▻_) (~Ctx-allUsedCtx s)
~Ctx-allUsedCtx (Un~Un s) = cong (B-Un _ ▻_) (~Ctx-allUsedCtx s)
~Ctx-allUsedCtx (Lin~Used s) = cong (B-Used _ ▻_) (~Ctx-allUsedCtx s)
~Ctx-allUsedCtx (Used~Used s) = cong (B-Used _ ▻_) (~Ctx-allUsedCtx s)

take-preserves-~Ctx :
  ∀ {Δ n pk} {Γ₁ Γ₂ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Lin)}
  → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂
  → Γ₁ ~Ctx Γ₂
take-preserves-~Ctx {Γ₁ = _} take-here = Lin~Used (~Ctx-refl _)
take-preserves-~Ctx (take-thereˡ take) = Lin~Lin (take-preserves-~Ctx take)
take-preserves-~Ctx (take-thereᵘ take) = Un~Un (take-preserves-~Ctx take)
take-preserves-~Ctx (take-there✖ take) = Used~Used (take-preserves-~Ctx take)

lin-lin-invert :
  ∀ {Δ n pk₁ pk₂} {Γ₁ Γ₂ : Ctx Δ n}
    {T₁ : NfTy Δ (KV pk₁ Lin)} {T₂ : NfTy Δ (KV pk₂ Lin)}
  → (B-Lin T₁ ▻ Γ₁) ~Ctx (B-Lin T₂ ▻ Γ₂)
  → Σ (pk₁ ≡ pk₂) λ where
      refl → Σ (T₁ ≡ T₂) λ _ → Γ₁ ~Ctx Γ₂
lin-lin-invert (Lin~Lin s) = refl , refl , s

un-un-invert :
  ∀ {Δ n pk₁ pk₂} {Γ₁ Γ₂ : Ctx Δ n}
    {T₁ : NfTy Δ (KV pk₁ Un)} {T₂ : NfTy Δ (KV pk₂ Un)}
  → (B-Un T₁ ▻ Γ₁) ~Ctx (B-Un T₂ ▻ Γ₂)
  → Σ (pk₁ ≡ pk₂) λ where
      refl → Σ (T₁ ≡ T₂) λ _ → Γ₁ ~Ctx Γ₂
un-un-invert (Un~Un s) = refl , refl , s

drop-lin-used :
  ∀ {Δ n pk} {Γ₁ Γ₂ : Ctx Δ n} {T : NfTy Δ (KV pk Lin)}
  → (B-Lin T ▻ Γ₁) ~Ctx (B-Used T ▻ Γ₂)
  → Γ₁ ~Ctx Γ₂
drop-lin-used (Lin~Used s) = s

lin-used-invert :
  ∀ {Δ n pk₁ pk₂} {Γ₁ Γ₂ : Ctx Δ n}
    {T₁ : NfTy Δ (KV pk₁ Lin)} {T₂ : NfTy Δ (KV pk₂ Lin)}
  → (B-Lin T₁ ▻ Γ₁) ~Ctx (B-Used T₂ ▻ Γ₂)
  → Σ (pk₁ ≡ pk₂) λ where
      refl → Σ (T₁ ≡ T₂) λ _ → Γ₁ ~Ctx Γ₂
lin-used-invert (Lin~Used s) = refl , refl , s

used-used-invert :
  ∀ {Δ n pk₁ pk₂} {Γ₁ Γ₂ : Ctx Δ n}
    {T₁ : NfTy Δ (KV pk₁ Lin)} {T₂ : NfTy Δ (KV pk₂ Lin)}
  → (B-Used T₁ ▻ Γ₁) ~Ctx (B-Used T₂ ▻ Γ₂)
  → Σ (pk₁ ≡ pk₂) λ where
      refl → Σ (T₁ ≡ T₂) λ _ → Γ₁ ~Ctx Γ₂
used-used-invert (Used~Used s) = refl , refl , s

wkCtx-cons :
  ∀ {Δ n K} (b : Binding Δ) (Γ : Ctx Δ n)
  → wkCtx {K = K} (b ▻ Γ) ≡ (wkBinding {K = K} b ▻ wkCtx {K = K} Γ)
wkCtx-cons b Γ = refl

unwk-~Ctx :
  ∀ {Δ n K} {Γ₁ Γ₂ : Ctx Δ n}
  → wkCtx {K = K} Γ₁ ~Ctx wkCtx {K = K} Γ₂
  → Γ₁ ~Ctx Γ₂
unwk-~Ctx {Γ₁ = ∅} {Γ₂ = ∅} ∅~∅ = ∅~∅
unwk-~Ctx
  {K = K}
  {Γ₁ = B-Lin T₁ ▻ Γ₁}
  {Γ₂ = B-Lin T₂ ▻ Γ₂}
  rel
  rewrite wkCtx-cons {K = K} (B-Lin T₁) Γ₁
        | wkCtx-cons {K = K} (B-Lin T₂) Γ₂
  with lin-lin-invert rel
... | refl , eqWk , rel′
  with wkNfTy-injective {K′ = K} eqWk
... | refl = Lin~Lin (unwk-~Ctx rel′)
unwk-~Ctx
  {K = K}
  {Γ₁ = B-Un T₁ ▻ Γ₁}
  {Γ₂ = B-Un T₂ ▻ Γ₂}
  rel
  rewrite wkCtx-cons {K = K} (B-Un T₁) Γ₁
        | wkCtx-cons {K = K} (B-Un T₂) Γ₂
  with un-un-invert rel
... | refl , eqWk , rel′
  with wkNfTy-injective {K′ = K} eqWk
... | refl = Un~Un (unwk-~Ctx rel′)
unwk-~Ctx
  {K = K}
  {Γ₁ = B-Lin T₁ ▻ Γ₁}
  {Γ₂ = B-Used T₂ ▻ Γ₂}
  rel
  rewrite wkCtx-cons {K = K} (B-Lin T₁) Γ₁
        | wkCtx-cons {K = K} (B-Used T₂) Γ₂
  with lin-used-invert rel
... | refl , eqWk , rel′
  with wkNfTy-injective {K′ = K} eqWk
... | refl = Lin~Used (unwk-~Ctx rel′)
unwk-~Ctx
  {K = K}
  {Γ₁ = B-Used T₁ ▻ Γ₁}
  {Γ₂ = B-Used T₂ ▻ Γ₂}
  rel
  rewrite wkCtx-cons {K = K} (B-Used T₁) Γ₁
        | wkCtx-cons {K = K} (B-Used T₂) Γ₂
  with used-used-invert rel
... | refl , eqWk , rel′
  with wkNfTy-injective {K′ = K} eqWk
... | refl = Used~Used (unwk-~Ctx rel′)

mutual

  value-preserves-~Ctx :
    ∀ {Δ n pk m}
      {Γ₁ Γ₂ : Ctx Δ n}
      {v : Value Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
    → Γ₁ ~Ctx Γ₂
  value-preserves-~Ctx {Γ₁ = Γ} (TV-Const _) = ~Ctx-refl Γ
  value-preserves-~Ctx (TV-Var-Lin take) = take-preserves-~Ctx take
  value-preserves-~Ctx {Γ₁ = Γ} (TV-Var-Un _) = ~Ctx-refl Γ
  value-preserves-~Ctx (TV-Abs d) = drop-lin-used (synth-preserves-~Ctx d)
  value-preserves-~Ctx {Γ₁ = Γ} (TV-Rec _) = ~Ctx-refl Γ
  value-preserves-~Ctx (TV-TAbs d) = unwk-~Ctx (value-preserves-~Ctx d)
  value-preserves-~Ctx (TV-Pair d₁ d₂) =
    ~Ctx-trans (value-preserves-~Ctx d₁) (value-preserves-~Ctx d₂)
  value-preserves-~Ctx {Γ₁ = Γ} TV-Receive₁ = ~Ctx-refl Γ
  value-preserves-~Ctx {Γ₁ = Γ} TV-Receive₂ = ~Ctx-refl Γ
  value-preserves-~Ctx {Γ₁ = Γ} TV-Send₁ = ~Ctx-refl Γ
  value-preserves-~Ctx {Γ₁ = Γ} TV-Send₂ = ~Ctx-refl Γ
  value-preserves-~Ctx {Γ₁ = Γ} TV-Select₁ = ~Ctx-refl Γ
  value-preserves-~Ctx {Γ₁ = Γ} TV-Select₂ = ~Ctx-refl Γ

  synth-preserves-~Ctx :
    ∀ {Δ n pk m}
      {Γ₁ Γ₂ : Ctx Δ n}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
    → Γ₁ ~Ctx Γ₂
  synth-preserves-~Ctx (T-Val d) = value-preserves-~Ctx d
  synth-preserves-~Ctx (T-Pair d₁ d₂) =
    ~Ctx-trans (synth-preserves-~Ctx d₁) (synth-preserves-~Ctx d₂)
  synth-preserves-~Ctx (T-App d₁ d₂) =
    ~Ctx-trans (synth-preserves-~Ctx d₁) (check-preserves-~Ctx d₂)
  synth-preserves-~Ctx (T-LetUnit d₁ d₂) =
    ~Ctx-trans (check-preserves-~Ctx d₁) (synth-preserves-~Ctx d₂)
  synth-preserves-~Ctx (T-LetPair d₁ d₂) =
    ~Ctx-trans
      (synth-preserves-~Ctx d₁)
      (drop-lin-used (drop-lin-used (synth-preserves-~Ctx d₂)))
  synth-preserves-~Ctx (T-Match {ne = ne} d bs _) =
    ~Ctx-trans
      (synth-preserves-~Ctx d)
      (drop-lin-used (synth-preserves-~Ctx (bs (proj₁ ne) (proj₂ ne))))
  synth-preserves-~Ctx (T-TApp d) = synth-preserves-~Ctx d

  check-preserves-~Ctx :
    ∀ {Δ n pk m}
      {Γ₁ Γ₂ : Ctx Δ n}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
    → Γ₁ ~Ctx Γ₂
  check-preserves-~Ctx (T-Check d _) = synth-preserves-~Ctx d
