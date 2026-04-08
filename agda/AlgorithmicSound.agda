open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Nat
open import Data.Fin.Subset as Subset using (_⊆_)
open import Data.Fin.Subset.Properties using (⊆-refl; ⊆-antisym)
open import Data.List
open import Data.Product
-- open import Data.Sum
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Function using (const)

module AlgorithmicSound  where

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
  ; np′-unique-eq
  )
open import TypesProperties using
  ( minus-injective
  ; protoP-injective
  ; up-injective
  )
open import NormalTypes using
  ( NFProto
  ; NFProto′
  ; NFTy
  ; nfProtoTy
  ; nfProto′Ty
  ; nfTyTy
  ; N-ProtoP
  ; N-Up
  ; N-Var
  ; N-Normal
  ; N-Minus
  )
open import Subtyping
open import AlgorithmicSubtyping

-- algorithmic typing is sound

sound-algₜ : ∀ {N₁ N₂ : NFTy Δ (KV pk m)}
  → N₁ <:ₜ N₂ → nfTyTy N₁ <: nfTyTy N₂

sound-<<:ₚ : ∀ {N₁ N₂ : NFProto Δ}
  → N₁ <<:ₚ[ ⊙ ] N₂ → nfProtoTy N₁ <<:[ ⊙ ] nfProtoTy N₂

sound-<<:ₚ′ : ∀ {N₁ N₂ : NFProto′ Δ}
  → N₁ <<:ₚ′[ ⊙ ] N₂ → nfProto′Ty N₁ <<:[ ⊙ ] nfProto′Ty N₂

sound-algₚ′ : ∀ {N₁ N₂ : NFProto′ Δ}
  → N₁ <:ₚ′ N₂ → nfProto′Ty N₁ <: nfProto′Ty N₂
sound-algₚ′ (<:ₚ′-proto #c₁⊆#c₂ N₁<:N₂) = <:-proto #c₁⊆#c₂ (sound-<<:ₚ N₁<:N₂)
sound-algₚ′ (<:ₚ′-up N₁<:ₜN₂) = <:-up (sound-algₜ N₁<:ₜN₂)
sound-algₚ′ <:ₚ′-var = <:-refl

sound-algₚ : ∀ {N₁ N₂ : NFProto Δ}
  → N₁ <:ₚ N₂ → nfProtoTy N₁ <: nfProtoTy N₂
sound-algₚ (<:ₚ-plus N₁<:N₂) = sound-algₚ′ N₁<:N₂
sound-algₚ (<:ₚ-minus N₂<:N₁) = <:-minus (sound-algₚ′ N₂<:N₁)

sound-<<:ₚ {⊙ = ⊕} N₁<<:N₂ = sound-algₚ N₁<<:N₂
sound-<<:ₚ {⊙ = ⊝} N₁<<:N₂ = sound-algₚ N₁<<:N₂
sound-<<:ₚ {⊙ = ⊘} eq = ≡c-refl-eq eq

sound-<<:ₚ′ {⊙ = ⊕} N₁<<:N₂ = sound-algₚ′ N₁<<:N₂
sound-<<:ₚ′ {⊙ = ⊝} N₁<<:N₂ = sound-algₚ′ N₁<<:N₂
sound-<<:ₚ′ {⊙ = ⊘} eq = ≡c-refl-eq eq

sound-algₜ <:ₜ-var = <:-refl
sound-algₜ <:ₜ-base = <:-refl
sound-algₜ (<:ₜ-arrow M₂<:ₜM₁ N₁<:ₜN₂) = <:-fun (sound-algₜ M₂<:ₜM₁) (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-pair N₁<:ₜN₂ N₃<:ₜN₄) = <:-pair (sound-algₜ N₁<:ₜN₂) (sound-algₜ N₃<:ₜN₄)
sound-algₜ (<:ₜ-poly N₁<:ₜN₂) = <:-all (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-sub {km≤ = km≤} N₁<:ₜN₂) = <:-sub km≤ (sound-algₜ N₁<:ₜN₂)
sound-algₜ <:ₜ-end = <:-refl
sound-algₜ (<:ₜ-msg {p = p} P₁<<P₂ N₁<:ₜN₂) = <:-msg (sound-<<:ₚ′ P₁<<P₂) (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-data N₁<:ₜN₂) = <:-protoD (sound-algₜ N₁<:ₜN₂)


-- algorithmic subtyping is antisymmetric

≡⇒<:ₚ : ∀ {N₁ N₂ : NFProto Δ} → nfProtoTy N₁ ≡ nfProtoTy N₂ → N₁ <:ₚ N₂
≡⇒<:ₚ′ : ∀ {N₁ N₂ : NFProto′ Δ} → nfProto′Ty N₁ ≡ nfProto′Ty N₂ → N₁ <:ₚ′ N₂
≡⇒<<:ₚ : ∀ {N₁ N₂ : NFProto Δ} → nfProtoTy N₁ ≡ nfProtoTy N₂ → N₁ <<:ₚ[ ⊙ ] N₂

≡⇒<:ₚ {N₁ = N-Normal N₁} {N₂ = N-Normal N₂} eq = <:ₚ-plus (≡⇒<:ₚ′ eq)
≡⇒<:ₚ {N₁ = N-Normal (N-ProtoP #c ⊙ N₁)} {N₂ = N-Minus N₂} ()
≡⇒<:ₚ {N₁ = N-Normal (N-Up N₁)} {N₂ = N-Minus N₂} ()
≡⇒<:ₚ {N₁ = N-Normal (N-Var x)} {N₂ = N-Minus N₂} ()
≡⇒<:ₚ {N₁ = N-Minus N₁} {N₂ = N-Normal (N-ProtoP #c ⊙ N₂)} ()
≡⇒<:ₚ {N₁ = N-Minus N₁} {N₂ = N-Normal (N-Up N₂)} ()
≡⇒<:ₚ {N₁ = N-Minus N₁} {N₂ = N-Normal (N-Var x)} ()
≡⇒<:ₚ {N₁ = N-Minus N₁} {N₂ = N-Minus N₂} eq
  with minus-injective eq
... | eq′ = <:ₚ-minus (≡⇒<:ₚ′ {N₁ = N₂} {N₂ = N₁} (sym eq′))

≡⇒<:ₚ′ {N₁ = N-ProtoP #c₁ ⊙₁ N₁} {N₂ = N-ProtoP #c₂ ⊙₂ N₂} eq
  with protoP-injective eq
... | refl , refl , refl , eq′ = <:ₚ′-proto ⊆-refl (≡⇒<<:ₚ {⊙ = ⊙₁} eq′)
≡⇒<:ₚ′ {N₁ = N-ProtoP #c ⊙ N₁} {N₂ = N-Up N₂} ()
≡⇒<:ₚ′ {N₁ = N-ProtoP #c ⊙ N₁} {N₂ = N-Var x} ()
≡⇒<:ₚ′ {N₁ = N-Up N₁} {N₂ = N-ProtoP #c ⊙ N₂} ()
≡⇒<:ₚ′ {N₁ = N-Up N₁} {N₂ = N-Up N₂} eq
  with up-injective eq
... | refl , refl , eq′ = <:ₚ′-up (<:ₜ-eq-ty N₁ N₂ eq′)
≡⇒<:ₚ′ {N₁ = N-Up N₁} {N₂ = N-Var x} ()
≡⇒<:ₚ′ {N₁ = N-Var x} {N₂ = N-ProtoP #c ⊙ N₂} ()
≡⇒<:ₚ′ {N₁ = N-Var x} {N₂ = N-Up N₂} ()
≡⇒<:ₚ′ {N₁ = N-Var x} {N₂ = N-Var y} eq
  with t-var-injective eq
... | refl = <:ₚ′-var

≡⇒<<:ₚ {⊙ = ⊕} eq = ≡⇒<:ₚ eq
≡⇒<<:ₚ {⊙ = ⊘} eq = eq
≡⇒<<:ₚ {⊙ = ⊝} eq = ≡⇒<:ₚ (sym eq)

<:ₜ-antisym : ∀ {N₁ N₂ : NFTy Δ (KV pk m)} → (N₁<:N₂ : N₁ <:ₜ N₂) → (N₂<:N₁ : N₂ <:ₜ N₁) → N₁ ≡ N₂
<:ₚ-antisym : ∀ {N₁ N₂ : NFProto Δ} → (N₁<:N₂ : N₁ <:ₚ N₂) → (N₂<:N₁ : N₂ <:ₚ N₁) → N₁ ≡ N₂
<:ₚ′-antisym : ∀ {N₁ N₂ : NFProto′ Δ} → (N₁<:N₂ : N₁ <:ₚ′ N₂) → (N₂<:N₁ : N₂ <:ₚ′ N₁) → N₁ ≡ N₂

<:ₜ-antisym <:ₜ-var <:ₜ-var = refl
<:ₜ-antisym <:ₜ-base <:ₜ-base = refl
<:ₜ-antisym (<:ₜ-arrow N₁<:N₂ N₁<:N₃) (<:ₜ-arrow N₂<:N₁ N₂<:N₂) rewrite <:ₜ-antisym N₁<:N₂ N₂<:N₁ | <:ₜ-antisym N₁<:N₃ N₂<:N₂ = refl
<:ₜ-antisym (<:ₜ-pair N₁<:N₂ N₁<:N₃) (<:ₜ-pair N₂<:N₁ N₂<:N₂) rewrite <:ₜ-antisym N₁<:N₂ N₂<:N₁ | <:ₜ-antisym N₁<:N₃ N₂<:N₂ = refl
<:ₜ-antisym (<:ₜ-poly N₁<:N₂) (<:ₜ-poly N₂<:N₁) rewrite <:ₜ-antisym N₁<:N₂ N₂<:N₁ = refl
<:ₜ-antisym (<:ₜ-sub N₁<:N₂) (<:ₜ-sub N₂<:N₁) rewrite <:ₜ-antisym N₁<:N₂ N₂<:N₁ = refl
<:ₜ-antisym <:ₜ-end <:ₜ-end = refl
<:ₜ-antisym (<:ₜ-msg {p = ⊕} T₁<<:T₂ N₁<:N₂) (<:ₜ-msg T₂<<:T₁ N₂<:N₁) rewrite <:ₜ-antisym N₁<:N₂ N₂<:N₁ | <:ₚ′-antisym T₁<<:T₂ T₂<<:T₁ = refl
<:ₜ-antisym (<:ₜ-msg {p = ⊝} T₁<<:T₂ N₁<:N₂) (<:ₜ-msg T₂<<:T₁ N₂<:N₁) rewrite <:ₜ-antisym N₁<:N₂ N₂<:N₁ | <:ₚ′-antisym T₂<<:T₁ T₁<<:T₂ = refl
<:ₜ-antisym (<:ₜ-data N₁<:N₂) (<:ₜ-data N₂<:N₁) rewrite <:ₜ-antisym N₁<:N₂ N₂<:N₁ = refl

<:ₚ-antisym (<:ₚ-plus N₁<:N₂) (<:ₚ-plus N₂<:N₁) rewrite <:ₚ′-antisym N₁<:N₂ N₂<:N₁ = refl
<:ₚ-antisym (<:ₚ-minus N₁<:N₂) (<:ₚ-minus N₂<:N₁) rewrite <:ₚ′-antisym N₂<:N₁ N₁<:N₂ = refl

<:ₚ′-antisym (<:ₚ′-proto {⊙ = ⊕} #c₁⊆#c₂ N₁<<:N₂) (<:ₚ′-proto #c₂⊆#c₁ N₂<<:N₁) rewrite ⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁ | <:ₚ-antisym N₁<<:N₂ N₂<<:N₁ = refl
<:ₚ′-antisym (<:ₚ′-proto {⊙ = ⊝} #c₁⊆#c₂ N₁<<:N₂) (<:ₚ′-proto #c₂⊆#c₁ N₂<<:N₁) rewrite ⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁ | <:ₚ-antisym N₂<<:N₁ N₁<<:N₂ = refl
<:ₚ′-antisym (<:ₚ′-proto {⊙ = ⊘} #c₁⊆#c₂ eq₁) (<:ₚ′-proto #c₂⊆#c₁ eq₂)
  rewrite ⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁
  = cong (N-ProtoP _ ⊘) (<:ₚ-antisym (≡⇒<:ₚ eq₁) (≡⇒<:ₚ eq₂))
<:ₚ′-antisym (<:ₚ′-up N₁<:N₂) (<:ₚ′-up N₂<:N₁) rewrite <:ₜ-antisym N₁<:N₂ N₂<:N₁ = refl
<:ₚ′-antisym <:ₚ′-var <:ₚ′-var = refl
