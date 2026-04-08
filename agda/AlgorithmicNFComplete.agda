module AlgorithmicNFComplete where

open import Data.List using (List)
open import Data.Nat using (ℕ; _⊔_; _≤_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong₂; subst; subst₂)

open import Util
open import Kinds
open import Duality
open import Variance
open import Types using (Ty; _≡c_; nf; t-minus)
open import Subtyping using (_<:_; _<<:[_]_; injᵥ)
open import NormalTypes using
  ( NFProto
  ; NFProto′
  ; NFTy
  ; nfProtoTy
  ; nfProto′Ty
  ; nfTyTy
  ; nfProtoTy-injective
  ; nfProto′Ty-injective
  ; nfTyTy-injective
  ; toNormalProto
  ; toNormalProto′
  ; toNormalTy
  ; fromNormalProto
  ; fromNormalProto′
  ; fromNormalTy
  ; nfProtoTy-fromNormalProto
  ; nfProto′Ty-fromNormalProto′
  ; nfTyTy-fromNormalTy
  ; sizeₚ
  ; sizeₚ′
  ; sizeₜ
  ; sizeₚ-toNormal
  ; sizeₚ′-toNormal
  ; sizeₜ-toNormal
  )
open import AlgorithmicNFSubtyping

import Types
import NormalTypes as NF
import AlgorithmicSubtyping as A
import AlgorithmicComplete as C

private
  variable
    Δ : List Kind

fromNormalProto∘toNormalProto :
  (N : NFProto Δ) → fromNormalProto (toNormalProto N) ≡ N
fromNormalProto∘toNormalProto N =
  nfProtoTy-injective (nfProtoTy-fromNormalProto (toNormalProto N))

fromNormalProto′∘toNormalProto′ :
  (N : NFProto′ Δ) → fromNormalProto′ (toNormalProto′ N) ≡ N
fromNormalProto′∘toNormalProto′ N =
  nfProto′Ty-injective (nfProto′Ty-fromNormalProto′ (toNormalProto′ N))

fromNormalTy∘toNormalTy :
  (N : NFTy Δ (KV pk m)) → fromNormalTy (toNormalTy N) ≡ N
fromNormalTy∘toNormalTy N =
  nfTyTy-injective (nfTyTy-fromNormalTy (toNormalTy N))

fromNormalProto-subst-toNormal :
  ∀ {T : Ty Δ KP} {N : NFProto Δ}
  → (eq : nfProtoTy N ≡ T)
  → fromNormalProto (subst Types.NormalProto eq (toNormalProto N)) ≡ N
fromNormalProto-subst-toNormal {N = N} refl =
  fromNormalProto∘toNormalProto N

fromNormalProto′-subst-toNormal :
  ∀ {T : Ty Δ KP} {N : NFProto′ Δ}
  → (eq : nfProto′Ty N ≡ T)
  → fromNormalProto′ (subst Types.NormalProto′ eq (toNormalProto′ N)) ≡ N
fromNormalProto′-subst-toNormal {N = N} refl =
  fromNormalProto′∘toNormalProto′ N

fromNormalTy-subst-toNormal :
  ∀ {T : Ty Δ (KV pk m)} {N : NFTy Δ (KV pk m)}
  → (eq : nfTyTy N ≡ T)
  → fromNormalTy (subst Types.NormalTy eq (toNormalTy N)) ≡ N
fromNormalTy-subst-toNormal {N = N} refl =
  fromNormalTy∘toNormalTy N

mutual

  old→nf-core-<:ₜ :
    ∀ {T₁ T₂ : Ty Δ (KV pk m)}
      {M₁ : Types.NormalTy T₁} {M₂ : Types.NormalTy T₂}
    → A._<:ₜ_ M₁ M₂
    → fromNormalTy M₁ <:ₜ fromNormalTy M₂
  old→nf-core-<:ₜ A.<:ₜ-var = <:ₜ-var
  old→nf-core-<:ₜ A.<:ₜ-base = <:ₜ-base
  old→nf-core-<:ₜ (A.<:ₜ-arrow N₂<:N₁ N₁<:N₂) =
    <:ₜ-arrow (old→nf-core-<:ₜ N₂<:N₁) (old→nf-core-<:ₜ N₁<:N₂)
  old→nf-core-<:ₜ (A.<:ₜ-pair N₁<:N₂ M₁<:M₂) =
    <:ₜ-pair (old→nf-core-<:ₜ N₁<:N₂) (old→nf-core-<:ₜ M₁<:M₂)
  old→nf-core-<:ₜ (A.<:ₜ-poly N₁<:N₂) =
    <:ₜ-poly (old→nf-core-<:ₜ N₁<:N₂)
  old→nf-core-<:ₜ (A.<:ₜ-sub N₁<:N₂) =
    <:ₜ-sub (old→nf-core-<:ₜ N₁<:N₂)
  old→nf-core-<:ₜ A.<:ₜ-end = <:ₜ-end
  old→nf-core-<:ₜ (A.<:ₜ-msg NP₁<<:NP₂ S₁<:S₂) =
    <:ₜ-msg (old→nf-core-<<:ₚ′ NP₁<<:NP₂) (old→nf-core-<:ₜ S₁<:S₂)
  old→nf-core-<:ₜ (A.<:ₜ-data N₁<:N₂) =
    <:ₜ-data (old→nf-core-<:ₜ N₁<:N₂)

  old→nf-core-<:ₚ′ :
    ∀ {T₁ T₂ : Ty Δ KP}
      {M₁ : Types.NormalProto′ T₁} {M₂ : Types.NormalProto′ T₂}
    → A._<:ₚ′_ M₁ M₂
    → fromNormalProto′ M₁ <:ₚ′ fromNormalProto′ M₂
  old→nf-core-<:ₚ′ (A.<:ₚ′-proto #c₁⊆#c₂ N₁<<:N₂) =
    <:ₚ′-proto #c₁⊆#c₂ (old→nf-core-<<:ₚ N₁<<:N₂)
  old→nf-core-<:ₚ′ (A.<:ₚ′-up N₁<:N₂) =
    <:ₚ′-up (old→nf-core-<:ₜ N₁<:N₂)
  old→nf-core-<:ₚ′ A.<:ₚ′-var = <:ₚ′-var

  old→nf-core-<:ₚ :
    ∀ {T₁ T₂ : Ty Δ KP}
      {M₁ : Types.NormalProto T₁} {M₂ : Types.NormalProto T₂}
    → A._<:ₚ_ M₁ M₂
    → fromNormalProto M₁ <:ₚ fromNormalProto M₂
  old→nf-core-<:ₚ (A.<:ₚ-plus N₁<:N₂) =
    <:ₚ-plus (old→nf-core-<:ₚ′ N₁<:N₂)
  old→nf-core-<:ₚ (A.<:ₚ-minus N₂<:N₁) =
    <:ₚ-minus (old→nf-core-<:ₚ′ N₂<:N₁)

  old→nf-core-<<:ₚ′ :
    ∀ {⊙} {T₁ T₂ : Ty Δ KP}
      {M₁ : Types.NormalProto′ T₁} {M₂ : Types.NormalProto′ T₂}
    → A._<<:ₚ′[_]_ M₁ ⊙ M₂
    → fromNormalProto′ M₁ <<:ₚ′[ ⊙ ] fromNormalProto′ M₂
  old→nf-core-<<:ₚ′ {⊙ = Variance.⊕} N₁<<:N₂ = old→nf-core-<:ₚ′ N₁<<:N₂
  old→nf-core-<<:ₚ′ {⊙ = Variance.⊘} {M₁ = M₁} {M₂ = M₂} N₁≡N₂
    rewrite nfProto′Ty-fromNormalProto′ M₁
          | nfProto′Ty-fromNormalProto′ M₂
    = N₁≡N₂
  old→nf-core-<<:ₚ′ {⊙ = Variance.⊝} N₂<<:N₁ = old→nf-core-<:ₚ′ N₂<<:N₁

  old→nf-core-<<:ₚ :
    ∀ {⊙} {T₁ T₂ : Ty Δ KP}
      {M₁ : Types.NormalProto T₁} {M₂ : Types.NormalProto T₂}
    → A._<<:ₚ[_]_ M₁ ⊙ M₂
    → fromNormalProto M₁ <<:ₚ[ ⊙ ] fromNormalProto M₂
  old→nf-core-<<:ₚ {⊙ = Variance.⊕} N₁<<:N₂ = old→nf-core-<:ₚ N₁<<:N₂
  old→nf-core-<<:ₚ {⊙ = Variance.⊘} {M₁ = M₁} {M₂ = M₂} N₁≡N₂
    rewrite nfProtoTy-fromNormalProto M₁
          | nfProtoTy-fromNormalProto M₂
    = N₁≡N₂
  old→nf-core-<<:ₚ {⊙ = Variance.⊝} N₂<<:N₁ = old→nf-core-<:ₚ N₂<<:N₁

  old→nf-core-<<:ₜ :
    ∀ {p} {T₁ T₂ : Ty Δ (KV pk m)}
      {M₁ : Types.NormalTy T₁} {M₂ : Types.NormalTy T₂}
    → A._<<:ₜ[_]_ M₁ p M₂
    → fromNormalTy M₁ <<:ₜ[ p ] fromNormalTy M₂
  old→nf-core-<<:ₜ {p = Duality.⊕} N₁<<:N₂ = old→nf-core-<:ₜ N₁<<:N₂
  old→nf-core-<<:ₜ {p = Duality.⊝} N₂<<:N₁ = old→nf-core-<:ₜ N₂<<:N₁

old→nf-<:ₜ :
  ∀ {N₁ N₂ : NFTy Δ (KV pk m)}
  → A._<:ₜ_ (toNormalTy N₁) (toNormalTy N₂)
  → N₁ <:ₜ N₂
old→nf-<:ₜ {N₁ = N₁} {N₂ = N₂} rel =
  subst₂
    (λ X Y → X <:ₜ Y)
    (fromNormalTy∘toNormalTy N₁)
    (fromNormalTy∘toNormalTy N₂)
    (old→nf-core-<:ₜ rel)

old→nf-<:ₚ′ :
  ∀ {N₁ N₂ : NFProto′ Δ}
  → A._<:ₚ′_ (toNormalProto′ N₁) (toNormalProto′ N₂)
  → N₁ <:ₚ′ N₂
old→nf-<:ₚ′ {N₁ = N₁} {N₂ = N₂} rel =
  subst₂
    (λ X Y → X <:ₚ′ Y)
    (fromNormalProto′∘toNormalProto′ N₁)
    (fromNormalProto′∘toNormalProto′ N₂)
    (old→nf-core-<:ₚ′ rel)

old→nf-<:ₚ :
  ∀ {N₁ N₂ : NFProto Δ}
  → A._<:ₚ_ (toNormalProto N₁) (toNormalProto N₂)
  → N₁ <:ₚ N₂
old→nf-<:ₚ {N₁ = N₁} {N₂ = N₂} rel =
  subst₂
    (λ X Y → X <:ₚ Y)
    (fromNormalProto∘toNormalProto N₁)
    (fromNormalProto∘toNormalProto N₂)
    (old→nf-core-<:ₚ rel)

old→nf-<<:ₚ′ :
  ∀ {⊙} {N₁ N₂ : NFProto′ Δ}
  → A._<<:ₚ′[_]_ (toNormalProto′ N₁) ⊙ (toNormalProto′ N₂)
  → N₁ <<:ₚ′[ ⊙ ] N₂
old→nf-<<:ₚ′ {⊙ = Variance.⊕} N₁<<:N₂ = old→nf-<:ₚ′ N₁<<:N₂
old→nf-<<:ₚ′ {⊙ = Variance.⊘} N₁≡N₂ = N₁≡N₂
old→nf-<<:ₚ′ {⊙ = Variance.⊝} N₂<<:N₁ = old→nf-<:ₚ′ N₂<<:N₁

old→nf-<<:ₚ :
  ∀ {⊙} {N₁ N₂ : NFProto Δ}
  → A._<<:ₚ[_]_ (toNormalProto N₁) ⊙ (toNormalProto N₂)
  → N₁ <<:ₚ[ ⊙ ] N₂
old→nf-<<:ₚ {⊙ = Variance.⊕} N₁<<:N₂ = old→nf-<:ₚ N₁<<:N₂
old→nf-<<:ₚ {⊙ = Variance.⊘} N₁≡N₂ = N₁≡N₂
old→nf-<<:ₚ {⊙ = Variance.⊝} N₂<<:N₁ = old→nf-<:ₚ N₂<<:N₁

old→nf-<<:ₜ :
  ∀ {p} {N₁ N₂ : NFTy Δ (KV pk m)}
  → A._<<:ₜ[_]_ (toNormalTy N₁) p (toNormalTy N₂)
  → N₁ <<:ₜ[ p ] N₂
old→nf-<<:ₜ {p = Duality.⊕} N₁<<:N₂ = old→nf-<:ₜ N₁<<:N₂
old→nf-<<:ₜ {p = Duality.⊝} N₂<<:N₁ = old→nf-<:ₜ N₂<<:N₁

sizeₚ≤-toOld :
  ∀ {n : ℕ} {N₁ N₂ : NFProto Δ}
  → sizeₚ N₁ ⊔ sizeₚ N₂ ≤ n
  → Types.sizeₚ (toNormalProto N₁) ⊔ Types.sizeₚ (toNormalProto N₂) ≤ n
sizeₚ≤-toOld {n = n} {N₁} {N₂} sz≤ =
  subst
    (λ x → x ≤ n)
    (sym (cong₂ _⊔_ (sizeₚ-toNormal N₁) (sizeₚ-toNormal N₂)))
    sz≤

sizeₚ′≤-toOld :
  ∀ {n : ℕ} {N₁ N₂ : NFProto′ Δ}
  → sizeₚ′ N₁ ⊔ sizeₚ′ N₂ ≤ n
  → Types.sizeₚ′ (toNormalProto′ N₁) ⊔ Types.sizeₚ′ (toNormalProto′ N₂) ≤ n
sizeₚ′≤-toOld {n = n} {N₁} {N₂} sz≤ =
  subst
    (λ x → x ≤ n)
    (sym (cong₂ _⊔_ (sizeₚ′-toNormal N₁) (sizeₚ′-toNormal N₂)))
    sz≤

sizeₜ≤-toOld :
  ∀ {n : ℕ} {N₁ N₂ : NFTy Δ (KV pk m)}
  → sizeₜ N₁ ⊔ sizeₜ N₂ ≤ n
  → Types.sizeₜ (toNormalTy N₁) ⊔ Types.sizeₜ (toNormalTy N₂) ≤ n
sizeₜ≤-toOld {n = n} {N₁} {N₂} sz≤ =
  subst
    (λ x → x ≤ n)
    (sym (cong₂ _⊔_ (sizeₜ-toNormal N₁) (sizeₜ-toNormal N₂)))
    sz≤

sizeₚ≤-cast :
  ∀ {n : ℕ} {N₁ N₂ : NFProto Δ}
    {T₁ T₂ : Ty Δ KP}
  → (eq₁ : nfProtoTy N₁ ≡ T₁)
  → (eq₂ : nfProtoTy N₂ ≡ T₂)
  → sizeₚ N₁ ⊔ sizeₚ N₂ ≤ n
  → Types.sizeₚ (subst Types.NormalProto eq₁ (toNormalProto N₁))
      ⊔ Types.sizeₚ (subst Types.NormalProto eq₂ (toNormalProto N₂))
      ≤ n
sizeₚ≤-cast {n = n} {N₁} {N₂} eq₁ eq₂ sz≤ =
  subst
    (λ x → x ≤ n)
    (cong₂ _⊔_
      (Types.sizeₚ-subst (toNormalProto N₁) eq₁)
      (Types.sizeₚ-subst (toNormalProto N₂) eq₂))
    (sizeₚ≤-toOld {N₁ = N₁} {N₂ = N₂} sz≤)

sizeₚ′≤-cast :
  ∀ {n : ℕ} {N₁ N₂ : NFProto′ Δ}
    {T₁ T₂ : Ty Δ KP}
  → (eq₁ : nfProto′Ty N₁ ≡ T₁)
  → (eq₂ : nfProto′Ty N₂ ≡ T₂)
  → sizeₚ′ N₁ ⊔ sizeₚ′ N₂ ≤ n
  → Types.sizeₚ′ (subst Types.NormalProto′ eq₁ (toNormalProto′ N₁))
      ⊔ Types.sizeₚ′ (subst Types.NormalProto′ eq₂ (toNormalProto′ N₂))
      ≤ n
sizeₚ′≤-cast {n = n} {N₁} {N₂} eq₁ eq₂ sz≤ =
  subst
    (λ x → x ≤ n)
    (cong₂ _⊔_
      (Types.sizeₚ′-subst (toNormalProto′ N₁) eq₁)
      (Types.sizeₚ′-subst (toNormalProto′ N₂) eq₂))
    (sizeₚ′≤-toOld {N₁ = N₁} {N₂ = N₂} sz≤)

sizeₜ≤-cast :
  ∀ {n : ℕ} {N₁ N₂ : NFTy Δ (KV pk m)}
    {T₁ T₂ : Ty Δ (KV pk m)}
  → (eq₁ : nfTyTy N₁ ≡ T₁)
  → (eq₂ : nfTyTy N₂ ≡ T₂)
  → sizeₜ N₁ ⊔ sizeₜ N₂ ≤ n
  → Types.sizeₜ (subst Types.NormalTy eq₁ (toNormalTy N₁))
      ⊔ Types.sizeₜ (subst Types.NormalTy eq₂ (toNormalTy N₂))
      ≤ n
sizeₜ≤-cast {n = n} {N₁} {N₂} eq₁ eq₂ sz≤ =
  subst
    (λ x → x ≤ n)
    (cong₂ _⊔_
      (Types.sizeₜ-subst (toNormalTy N₁) eq₁)
      (Types.sizeₜ-subst (toNormalTy N₂) eq₂))
    (sizeₜ≤-toOld {N₁ = N₁} {N₂ = N₂} sz≤)

complete-algₚ :
  ∀ n {T₁ T₂ : Ty Δ KP}
  → T₁ <: T₂
  → ∀ {f₁ f₂} {N₁ : NFProto Δ}{N₂ : NFProto Δ}
  → nfProtoTy N₁ ≡ nf Duality.⊕ f₁ T₁
  → nfProtoTy N₂ ≡ nf Duality.⊕ f₂ T₂
  → sizeₚ N₁ ⊔ sizeₚ N₂ ≤ n
  → N₁ <:ₚ N₂
complete-algₚ n {T₁ = T₁} {T₂ = T₂} T₁<:T₂ {f₁ = f₁} {f₂ = f₂} {N₁ = N₁} {N₂ = N₂} eq₁ eq₂ sz≤ =
  subst₂
    (λ X Y → X <:ₚ Y)
    (fromNormalProto-subst-toNormal eq₁)
    (fromNormalProto-subst-toNormal eq₂)
    (old→nf-core-<:ₚ
      (C.complete-algₚ n T₁<:T₂ {f₁ = f₁} {f₂ = f₂}
        {N₁ = subst Types.NormalProto eq₁ (toNormalProto N₁)}
        {N₂ = subst Types.NormalProto eq₂ (toNormalProto N₂)}
        (sizeₚ≤-cast
          {N₁ = N₁} {N₂ = N₂}
          {T₁ = nf Duality.⊕ f₁ T₁}
          {T₂ = nf Duality.⊕ f₂ T₂}
          eq₁ eq₂ sz≤)))

complete-algₚ-inverted :
  ∀ n {T₁ T₂ : Ty Δ KP}
  → T₁ <: T₂
  → ∀ {f₁ f₂} {N₁ : NFProto Δ}{N₂ : NFProto Δ}
  → nfProtoTy N₁ ≡ t-minus (nf Duality.⊕ f₁ T₁)
  → nfProtoTy N₂ ≡ t-minus (nf Duality.⊕ f₂ T₂)
  → sizeₚ N₁ ⊔ sizeₚ N₂ ≤ n
  → N₂ <:ₚ N₁
complete-algₚ-inverted n {T₁ = T₁} {T₂ = T₂} T₁<:T₂ {f₁ = f₁} {f₂ = f₂} {N₁ = N₁} {N₂ = N₂} eq₁ eq₂ sz≤ =
  subst₂
    (λ X Y → X <:ₚ Y)
    (fromNormalProto-subst-toNormal eq₂)
    (fromNormalProto-subst-toNormal eq₁)
    (old→nf-core-<:ₚ
      (C.complete-algₚ-inverted n T₁<:T₂ {f₁ = f₁} {f₂ = f₂}
        {N₁ = subst Types.NormalProto eq₁ (toNormalProto N₁)}
        {N₂ = subst Types.NormalProto eq₂ (toNormalProto N₂)}
        (sizeₚ≤-cast
          {N₁ = N₁} {N₂ = N₂}
          {T₁ = t-minus (nf Duality.⊕ f₁ T₁)}
          {T₂ = t-minus (nf Duality.⊕ f₂ T₂)}
          eq₁ eq₂ sz≤)))

complete-<<:ₚ :
  ∀ n {⊙} {T₁ T₂ : Ty Δ KP}
  → T₁ <<:[ ⊙ ] T₂
  → ∀ {f₁ f₂} {N₁ : NFProto Δ}{N₂ : NFProto Δ}
  → nfProtoTy N₁ ≡ nf Duality.⊕ f₁ T₁
  → nfProtoTy N₂ ≡ nf Duality.⊕ f₂ T₂
  → sizeₚ N₁ ⊔ sizeₚ N₂ ≤ n
  → N₁ <<:ₚ[ ⊙ ] N₂
complete-<<:ₚ n {⊙ = ⊙} {T₁ = T₁} {T₂ = T₂} T₁<<:T₂ {f₁ = f₁} {f₂ = f₂} {N₁ = N₁} {N₂ = N₂} eq₁ eq₂ sz≤ =
  subst₂
    (λ X Y → X <<:ₚ[ ⊙ ] Y)
    (fromNormalProto-subst-toNormal eq₁)
    (fromNormalProto-subst-toNormal eq₂)
    (old→nf-core-<<:ₚ
      (C.complete-<<:ₚ n T₁<<:T₂ {f₁ = f₁} {f₂ = f₂}
        {N₁ = subst Types.NormalProto eq₁ (toNormalProto N₁)}
        {N₂ = subst Types.NormalProto eq₂ (toNormalProto N₂)}
        (sizeₚ≤-cast
          {N₁ = N₁} {N₂ = N₂}
          {T₁ = nf Duality.⊕ f₁ T₁}
          {T₂ = nf Duality.⊕ f₂ T₂}
          eq₁ eq₂ sz≤)))

complete-<<:ₚ′ :
  ∀ n {⊙} {T₁ T₂ : Ty Δ KP}
  → T₁ <<:[ injᵥ ⊙ ] T₂
  → ∀ {f₁ f₂} {N₁ : NFProto′ Δ}{N₂ : NFProto′ Δ}
  → nfProto′Ty N₁ ≡ nf Duality.⊕ f₁ T₁
  → nfProto′Ty N₂ ≡ nf Duality.⊕ f₂ T₂
  → sizeₚ′ N₁ ⊔ sizeₚ′ N₂ ≤ n
  → N₁ <<:ₚ′[ injᵥ ⊙ ] N₂
complete-<<:ₚ′ n {⊙ = ⊙} {T₁ = T₁} {T₂ = T₂} T₁<<:T₂ {f₁ = f₁} {f₂ = f₂} {N₁ = N₁} {N₂ = N₂} eq₁ eq₂ sz≤ =
  subst₂
    (λ X Y → X <<:ₚ′[ injᵥ ⊙ ] Y)
    (fromNormalProto′-subst-toNormal eq₁)
    (fromNormalProto′-subst-toNormal eq₂)
    (old→nf-core-<<:ₚ′
      (C.complete-<<:ₚ′ n T₁<<:T₂ {f₁ = f₁} {f₂ = f₂}
        {N₁ = subst Types.NormalProto′ eq₁ (toNormalProto′ N₁)}
        {N₂ = subst Types.NormalProto′ eq₂ (toNormalProto′ N₂)}
        (sizeₚ′≤-cast
          {N₁ = N₁} {N₂ = N₂}
          {T₁ = nf Duality.⊕ f₁ T₁}
          {T₂ = nf Duality.⊕ f₂ T₂}
          eq₁ eq₂ sz≤)))

complete-<<:ₚ′-inverted :
  ∀ n {⊙} {T₁ T₂ : Ty Δ KP}
  → T₁ <<:[ injᵥ ⊙ ] T₂
  → ∀ {f₁ f₂} {N₁ : NFProto′ Δ}{N₂ : NFProto′ Δ}
  → nfProto′Ty N₁ ≡ t-minus (nf Duality.⊕ f₁ T₁)
  → nfProto′Ty N₂ ≡ t-minus (nf Duality.⊕ f₂ T₂)
  → sizeₚ′ N₁ ⊔ sizeₚ′ N₂ ≤ n
  → N₂ <<:ₚ′[ injᵥ ⊙ ] N₁
complete-<<:ₚ′-inverted n {⊙ = ⊙} {T₁ = T₁} {T₂ = T₂} T₁<<:T₂ {f₁ = f₁} {f₂ = f₂} {N₁ = N₁} {N₂ = N₂} eq₁ eq₂ sz≤ =
  subst₂
    (λ X Y → X <<:ₚ′[ injᵥ ⊙ ] Y)
    (fromNormalProto′-subst-toNormal eq₂)
    (fromNormalProto′-subst-toNormal eq₁)
    (old→nf-core-<<:ₚ′
      (C.complete-<<:ₚ′-inverted n T₁<<:T₂ {f₁ = f₁} {f₂ = f₂}
        {N₁ = subst Types.NormalProto′ eq₁ (toNormalProto′ N₁)}
        {N₂ = subst Types.NormalProto′ eq₂ (toNormalProto′ N₂)}
        (sizeₚ′≤-cast
          {N₁ = N₁} {N₂ = N₂}
          {T₁ = t-minus (nf Duality.⊕ f₁ T₁)}
          {T₂ = t-minus (nf Duality.⊕ f₂ T₂)}
          eq₁ eq₂ sz≤)))

complete-algₜ :
  ∀ n {p : Polarity} {T₁ T₂ : Ty Δ (KV pk m)}
  → T₁ <: T₂
  → ∀ {f₁ f₂} {N₁ : NFTy Δ (KV pk m)}{N₂ : NFTy Δ (KV pk m)}
  → nfTyTy N₁ ≡ nf p f₁ T₁
  → nfTyTy N₂ ≡ nf p f₂ T₂
  → sizeₜ N₁ ⊔ sizeₜ N₂ ≤ n
  → N₁ <<:ₜ[ p ] N₂
complete-algₜ n {p = p} {T₁ = T₁} {T₂ = T₂} T₁<:T₂ {f₁ = f₁} {f₂ = f₂} {N₁ = N₁} {N₂ = N₂} eq₁ eq₂ sz≤ =
  subst₂
    (λ X Y → X <<:ₜ[ p ] Y)
    (fromNormalTy-subst-toNormal eq₁)
    (fromNormalTy-subst-toNormal eq₂)
    (old→nf-core-<<:ₜ
      (C.complete-algₜ n {p = p} T₁<:T₂ {f₁ = f₁} {f₂ = f₂}
        {N₁ = subst Types.NormalTy eq₁ (toNormalTy N₁)}
        {N₂ = subst Types.NormalTy eq₂ (toNormalTy N₂)}
        (sizeₜ≤-cast
          {N₁ = N₁} {N₂ = N₂}
          {T₁ = nf p f₁ T₁}
          {T₂ = nf p f₂ T₂}
          eq₁ eq₂ sz≤)))

subty⇒conv : {T₁ T₂ : Ty Δ K} → T₁ <: T₂ → T₂ <: T₁ → T₁ ≡c T₂
subty⇒conv = C.subty⇒conv
