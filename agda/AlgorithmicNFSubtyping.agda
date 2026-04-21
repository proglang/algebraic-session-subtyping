open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Nat
open import Data.Fin.Subset as Subset using (_⊆_)
open import Data.Fin.Subset.Properties using (⊆-refl; ⊆-antisym)
open import Data.List
open import Data.Product
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Function using (const)

module AlgorithmicNFSubtyping where

open import Util
open import Kinds
open import Duality
open import Types hiding
  ( NormalTy
  ; NormalProto
  ; NormalProto′
  ; NormalVar
  ; N-Var
  ; N-Base
  ; N-Arrow
  ; N-Pair
  ; N-Poly
  ; N-Sub
  ; N-End
  ; N-Msg
  ; N-ProtoD
  ; N-ProtoP
  ; N-Up
  ; N-Normal
  ; N-Minus
  ; NV-Var
  ; NV-Dual
  ; nt-unique
  ; nt-unique-eq
  ; np-unique
  ; np-unique-eq
  ; np′-unique
  )
open import NormalTypes using
  ( NFProto
  ; NFProto′
  ; NFVar
  ; NFTy
  ; nfProtoTy
  ; nfProto′Ty
  ; nfTyTy
  ; nfTyTy-injective
  ; N-Var
  ; N-Base
  ; N-Arrow
  ; N-Pair
  ; N-Poly
  ; N-Sub
  ; N-End
  ; N-Msg
  ; N-ProtoD
  ; N-ProtoP
  ; N-Up
  ; N-Normal
  ; N-Minus
  )
open import Subtyping

-- algorithmic version of subtyping that only works on normal forms

data _<:ₚ_ : NFProto Δ → NFProto Δ → Set
data _<:ₚ′_ : NFProto′ Δ → NFProto′ Δ → Set

_<<:ₚ′[_]_ : NFProto′ Δ → Variance → NFProto′ Δ → Set
N₁ <<:ₚ′[ ⊕ ] N₂ = N₁ <:ₚ′ N₂
N₁ <<:ₚ′[ ⊘ ] N₂ = nfProto′Ty N₁ ≡ nfProto′Ty N₂
N₁ <<:ₚ′[ ⊝ ] N₂ = N₂ <:ₚ′ N₁

_<<:ₚ[_]_ : NFProto Δ → Variance → NFProto Δ → Set
N₁ <<:ₚ[ ⊕ ] N₂ = N₁ <:ₚ N₂
N₁ <<:ₚ[ ⊘ ] N₂ = nfProtoTy N₁ ≡ nfProtoTy N₂
N₁ <<:ₚ[ ⊝ ] N₂ = N₂ <:ₚ N₁

data _<:ₜ_ : NFTy Δ (KV pk m) → NFTy Δ (KV pk m) → Set where

  <:ₜ-var : ∀ {nv : NFVar Δ (KV pk m)} → N-Var nv <:ₜ N-Var nv
  <:ₜ-base : N-Base {Δ = Δ} <:ₜ N-Base
  <:ₜ-arrow : ∀
        {pk₁ pk₂ : PreKind} {m₁ m₂ : Multiplicity}
        {M₁ : NFTy Δ (KV pk₁ m₁)} {N₁ : NFTy Δ (KV pk₂ m₂)}
        {M₂ : NFTy Δ (KV pk₁ m₁)} {N₂ : NFTy Δ (KV pk₂ m₂)}
        → M₂ <:ₜ M₁ → N₁ <:ₜ N₂ → (N-Arrow {m = m} M₁ N₁) <:ₜ (N-Arrow {m = m} M₂ N₂)
  <:ₜ-pair : ∀ {m}
        {M₁ M₂ : NFTy Δ (KV pk₁ m)} {N₁ N₂ : NFTy Δ (KV pk₂ m)}
        → M₁ <:ₜ M₂ → N₁ <:ₜ N₂ → N-Pair M₁ N₁ <:ₜ N-Pair M₂ N₂
  <:ₜ-poly : ∀ {m} {K′} {N₁ N₂ : NFTy (K′ ∷ Δ) (KV KT m)}
        → N₁ <:ₜ N₂ → N-Poly K′ N₁ <:ₜ N-Poly K′ N₂
  <:ₜ-sub : ∀ {km≤ : KV pk m ≤k KV pk′ m′} {N₁ N₂ : NFTy Δ (KV pk m)}
          → N₁ <:ₜ N₂ → N-Sub km≤ N₁ <:ₜ N-Sub km≤ N₂
  <:ₜ-end : N-End {Δ = Δ} <:ₜ N-End
  <:ₜ-msg : ∀ {p} {NP₁ NP₂ : NFProto′ Δ} {NS₁ NS₂ : NFTy Δ SLin}
          → NP₁ <<:ₚ′[ injᵥ p ] NP₂ → NS₁ <:ₜ NS₂ → N-Msg p NP₁ NS₁ <:ₜ N-Msg p NP₂ NS₂
  <:ₜ-data : ∀ {N₁ N₂ : NFTy Δ TLin}
    → N₁ <:ₜ N₂ → N-ProtoD N₁ <:ₜ N-ProtoD N₂

data _<:ₚ′_ where

  <:ₚ′-proto : ∀ {N₁ N₂ : NFProto Δ}
    → #c₁ ⊆ #c₂
    → N₁ <<:ₚ[ ⊙ ] N₂
    → N-ProtoP #c₁ ⊙ N₁ <:ₚ′ N-ProtoP #c₂ ⊙ N₂
  <:ₚ′-up : ∀ {N₁ N₂ : NFTy Δ (KV pk m)}
    → N₁ <:ₜ N₂
    → N-Up N₁ <:ₚ′ N-Up N₂
  <:ₚ′-var : ∀ {x : KP ∈ Δ} → N-Var {Δ = Δ} x <:ₚ′ N-Var x

data _<:ₚ_ where

  <:ₚ-plus : {N₁ N₂ : NFProto′ Δ}
    → N₁ <:ₚ′ N₂ → N-Normal N₁ <:ₚ N-Normal N₂
  <:ₚ-minus : {N₁ N₂ : NFProto′ Δ}
    → N₂ <:ₚ′ N₁ → N-Minus N₁ <:ₚ N-Minus N₂

-- algorithmic subtyping is reflexive

<:ₜ-refl : ∀ (N : NFTy Δ (KV pk m)) → N <:ₜ N
<:ₚ′-refl : ∀ (NP : NFProto′ Δ) → NP <:ₚ′ NP
<<:ₚ-refl : ∀ (NP : NFProto Δ) → NP <<:ₚ[ ⊙ ] NP
<<:ₚ′-refl : ∀ (NP : NFProto′ Δ) → NP <<:ₚ′[ ⊙ ] NP

<:ₚ′-refl (N-ProtoP #c ⊙ NP) = <:ₚ′-proto {#c₁ = #c} {#c₂ = #c} {⊙ = ⊙} (λ {x} z → z) (<<:ₚ-refl NP)
<:ₚ′-refl (N-Up N) = <:ₚ′-up (<:ₜ-refl N)
<:ₚ′-refl (N-Var x) = <:ₚ′-var

<:ₚ-refl : ∀ (NP : NFProto Δ) → NP <:ₚ NP
<:ₚ-refl (N-Normal NP) = <:ₚ-plus (<:ₚ′-refl NP)
<:ₚ-refl (N-Minus NP) = <:ₚ-minus (<:ₚ′-refl NP)

<<:ₚ-refl {⊙ = ⊕} NP = <:ₚ-refl NP
<<:ₚ-refl {⊙ = ⊝} NP = <:ₚ-refl NP
<<:ₚ-refl {⊙ = ⊘} NP = refl

<<:ₚ′-refl {⊙ = ⊕} NP = <:ₚ′-refl NP
<<:ₚ′-refl {⊙ = ⊝} NP = <:ₚ′-refl NP
<<:ₚ′-refl {⊙ = ⊘} NP = refl

<:ₜ-refl (N-Var x) = <:ₜ-var
<:ₜ-refl N-Base = <:ₜ-base
<:ₜ-refl (N-Arrow {m = m} N N₁) = <:ₜ-arrow {m = m} (<:ₜ-refl N) (<:ₜ-refl N₁)
<:ₜ-refl (N-Pair N N₁) = <:ₜ-pair (<:ₜ-refl N) (<:ₜ-refl N₁)
<:ₜ-refl (N-Poly _ N) = <:ₜ-poly (<:ₜ-refl N)
<:ₜ-refl (N-Sub _ N) = <:ₜ-sub (<:ₜ-refl N)
<:ₜ-refl N-End = <:ₜ-end
<:ₜ-refl (N-Msg p NP N) = <:ₜ-msg (<<:ₚ′-refl NP) (<:ₜ-refl N)
<:ₜ-refl (N-ProtoD N) = <:ₜ-data (<:ₜ-refl N)

<:ₜ-refl-eq : ∀ {N₁ N₂ : NFTy Δ (KV pk m)} → N₁ ≡ N₂ → N₁ <:ₜ N₂
<:ₜ-refl-eq refl = <:ₜ-refl _


-- algorithmic subtyping is transitive

<:ₜ-trans : ∀ {N₁ N₂ N₃ : NFTy Δ (KV pk m)} → N₁ <:ₜ N₂ → N₂ <:ₜ N₃ → N₁ <:ₜ N₃
<:ₚ′-trans : ∀ {N₁ N₂ N₃ : NFProto′ Δ} → N₁ <:ₚ′ N₂ → N₂ <:ₚ′ N₃ → N₁ <:ₚ′ N₃
<<:ₚ-trans : ∀ {N₁ N₂ N₃ : NFProto Δ} → N₁ <<:ₚ[ ⊙ ] N₂ → N₂ <<:ₚ[ ⊙ ] N₃ → N₁ <<:ₚ[ ⊙ ] N₃
<<:ₚ′-trans : ∀ {N₁ N₂ N₃ : NFProto′ Δ} → N₁ <<:ₚ′[ ⊙ ] N₂ → N₂ <<:ₚ′[ ⊙ ] N₃ → N₁ <<:ₚ′[ ⊙ ] N₃

<:ₚ′-trans (<:ₚ′-proto #c₁⊆#c₂ N₁<<:N₂) (<:ₚ′-proto #c₂⊆#c₃ N₂<<:N₃) = <:ₚ′-proto (λ {x} z → #c₂⊆#c₃ (#c₁⊆#c₂ z)) (<<:ₚ-trans N₁<<:N₂ N₂<<:N₃)
<:ₚ′-trans (<:ₚ′-up N₁<:N₂) (<:ₚ′-up N₂<:N₃) = <:ₚ′-up (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₚ′-trans <:ₚ′-var <:ₚ′-var = <:ₚ′-var

<:ₚ-trans : ∀ {N₁ N₂ N₃ : NFProto Δ} → N₁ <:ₚ N₂ → N₂ <:ₚ N₃ → N₁ <:ₚ N₃
<:ₚ-trans (<:ₚ-plus N₁<:N₂) (<:ₚ-plus N₂<:N₃) = <:ₚ-plus (<:ₚ′-trans N₁<:N₂ N₂<:N₃)
<:ₚ-trans (<:ₚ-minus N₁<:N₂) (<:ₚ-minus N₂<:N₃) = <:ₚ-minus (<:ₚ′-trans N₂<:N₃ N₁<:N₂)

<<:ₚ-trans {⊙ = ⊕} N₁<<:N₂ N₂<<:N₃ = <:ₚ-trans N₁<<:N₂ N₂<<:N₃
<<:ₚ-trans {⊙ = ⊝} N₁<<:N₂ N₂<<:N₃ = <:ₚ-trans N₂<<:N₃ N₁<<:N₂
<<:ₚ-trans {⊙ = ⊘} N₁<<:N₂ N₂<<:N₃ = trans N₁<<:N₂ N₂<<:N₃

<<:ₚ′-trans {⊙ = ⊕} N₁<<:N₂ N₂<<:N₃ = <:ₚ′-trans N₁<<:N₂ N₂<<:N₃
<<:ₚ′-trans {⊙ = ⊝} N₁<<:N₂ N₂<<:N₃ = <:ₚ′-trans N₂<<:N₃ N₁<<:N₂
<<:ₚ′-trans {⊙ = ⊘} N₁<<:N₂ N₂<<:N₃ = trans N₁<<:N₂ N₂<<:N₃

<:ₜ-trans <:ₜ-var <:ₜ-var = <:ₜ-var
<:ₜ-trans <:ₜ-base <:ₜ-base = <:ₜ-base
<:ₜ-trans (<:ₜ-arrow {m = m} N₁<:N₂ N₁<:N₃) (<:ₜ-arrow {m = .m} N₂<:N₃ N₂<:N₄) = <:ₜ-arrow {m = m} (<:ₜ-trans N₂<:N₃ N₁<:N₂) (<:ₜ-trans N₁<:N₃ N₂<:N₄)
<:ₜ-trans (<:ₜ-pair N₁<:N₂ N₁<:N₃) (<:ₜ-pair N₂<:N₃ N₂<:N₄) = <:ₜ-pair (<:ₜ-trans N₁<:N₂ N₂<:N₃) (<:ₜ-trans N₁<:N₃ N₂<:N₄)
<:ₜ-trans (<:ₜ-poly N₁<:N₂) (<:ₜ-poly N₂<:N₃) = <:ₜ-poly (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans (<:ₜ-sub N₁<:N₂) (<:ₜ-sub N₂<:N₃) = <:ₜ-sub (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans <:ₜ-end <:ₜ-end = <:ₜ-end
<:ₜ-trans (<:ₜ-msg P₁<<:P₂ N₁<:N₂) (<:ₜ-msg P₂<<:P₃ N₂<:N₃) = <:ₜ-msg (<<:ₚ′-trans P₁<<:P₂ P₂<<:P₃) (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans (<:ₜ-data N₁<:N₂) (<:ₜ-data N₂<:N₃) = <:ₜ-data (<:ₜ-trans N₁<:N₂ N₂<:N₃)

-- utility

<:ₜ-eq-ty : (N₁ N₂ : NFTy Δ (KV pk m)) → nfTyTy N₁ ≡ nfTyTy N₂ → N₁ <:ₜ N₂
<:ₜ-eq-ty N₁ N₂ eq =
  Eq.subst (λ N → N <:ₜ N₂) (sym (nfTyTy-injective eq)) (<:ₜ-refl N₂)

_<<:ₜ[_]_ : NFTy Δ (KV pk m) → Polarity → NFTy Δ (KV pk m) → Set
N₁ <<:ₜ[ ⊕ ] N₂ = N₁ <:ₜ N₂
N₁ <<:ₜ[ ⊝ ] N₂ = N₂ <:ₜ N₁

<<:ₜ-refl : ∀ {p} (N : NFTy Δ (KV pk m)) → N <<:ₜ[ p ] N
<<:ₜ-refl {p = ⊕} N = <:ₜ-refl N
<<:ₜ-refl {p = ⊝} N = <:ₜ-refl N

<<:ₜ-refl-eq : ∀ {p} (N₁ N₂ : NFTy Δ (KV pk m)) (eq : nfTyTy N₁ ≡ nfTyTy N₂) → N₁ <<:ₜ[ p ] N₂
<<:ₜ-refl-eq {p = p} N₁ N₂ eq =
  Eq.subst (λ N → N <<:ₜ[ p ] N₂) (sym (nfTyTy-injective eq)) (<<:ₜ-refl N₂)

<<:ₜ-trans : ∀ {p} {N₁ N₂ N₃ : NFTy Δ (KV pk m)} → N₁ <<:ₜ[ p ] N₂ → N₂ <<:ₜ[ p ] N₃ → N₁ <<:ₜ[ p ] N₃
<<:ₜ-trans {p = ⊕} N₁<<:N₂ N₂<<:N₃ = <:ₜ-trans N₁<<:N₂ N₂<<:N₃
<<:ₜ-trans {p = ⊝} N₁<<:N₂ N₂<<:N₃ = <:ₜ-trans N₂<<:N₃ N₁<<:N₂

<<:ₜ-var : ∀ {p} {nv : NFVar Δ (KV pk m)} → N-Var nv <<:ₜ[ p ] N-Var nv
<<:ₜ-var {p = ⊕} = <:ₜ-var
<<:ₜ-var {p = ⊝} = <:ₜ-var

<<:ₜ-base : N-Base {Δ = Δ} <<:ₜ[ p ] N-Base
<<:ₜ-base {p = ⊕} = <:ₜ-base
<<:ₜ-base {p = ⊝} = <:ₜ-base

<<:ₜ-end : N-End {Δ = Δ} <<:ₜ[ p ] N-End
<<:ₜ-end {p = ⊕} = <:ₜ-end
<<:ₜ-end {p = ⊝} = <:ₜ-end

<<:ₜ-sub : ∀ {N₁ N₂ : NFTy Δ (KV pk m)}
  → {km≤ : KV pk m ≤k KV pk′ m′} → N₁ <<:ₜ[ p ] N₂ → N-Sub km≤ N₁ <<:ₜ[ p ] N-Sub km≤ N₂
<<:ₜ-sub {p = ⊕} N₁<:N₂ = <:ₜ-sub N₁<:N₂
<<:ₜ-sub {p = ⊝} N₁<:N₂ = <:ₜ-sub N₁<:N₂

<<:ₜ-sub-invert : ∀ {N₁ N₂ : NFTy Δ (KV pk m)}
  → {km≤ : KV pk m ≤k KV pk′ m′} → N₁ <<:ₜ[ p ] N₂ → N-Sub km≤ N₁ <<:ₜ[ p ] N-Sub km≤ N₂
<<:ₜ-sub-invert {p = ⊕} N₁<:N₂ = <:ₜ-sub N₁<:N₂
<<:ₜ-sub-invert {p = ⊝} N₁<:N₂ = <:ₜ-sub N₁<:N₂

subst-<<: : {⊙ : Variance} {N₁ N₂ : NFProto′ Δ} {T₁′ T₂′ : Ty Δ KP}
  → (eq₁ : nfProto′Ty N₁ ≡ T₁′) (eq₂ : nfProto′Ty N₂ ≡ T₂′)
  → N₁ <<:ₚ′[ ⊙ ] N₂
  → N₁ <<:ₚ′[ ⊙ ] N₂
subst-<<: eq₁ eq₂ N₁<<:N₂ = N₁<<:N₂

subst-<:ₚ : ∀ {N₁ N₂ : NFProto Δ} {T₂′ : Ty Δ KP}
  → (eq : nfProtoTy N₂ ≡ T₂′) → N₁ <:ₚ N₂ → N₁ <:ₚ N₂
subst-<:ₚ eq N₁<:N₂ = N₁<:N₂
