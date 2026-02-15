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
open import Types
open import Subtyping
open import AlgorithmicSubtyping

-- algorithmic typing is sound

sound-algₜ : ∀ {T₁ T₂ : Ty Δ (KV pk m)} {N₁ : NormalTy T₁}{N₂ : NormalTy T₂}
  → N₁ <:ₜ N₂ → T₁ <: T₂

sound-<<:ₚ : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto T₁}{N₂ : NormalProto T₂}
  → N₁ <<:ₚ[ ⊙ ] N₂ → T₁ <<:[ ⊙ ] T₂

sound-<<:ₚ′ : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto′ T₁}{N₂ : NormalProto′ T₂}
  → N₁ <<:ₚ′[ ⊙ ] N₂ → T₁ <<:[ ⊙ ] T₂

sound-algₚ′ : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto′ T₁}{N₂ : NormalProto′ T₂}
  → N₁ <:ₚ′ N₂ → T₁ <: T₂
sound-algₚ′ (<:ₚ′-proto #c₁⊆#c₂ N₁<:N₂) = <:-proto #c₁⊆#c₂ (sound-<<:ₚ N₁<:N₂)
sound-algₚ′ (<:ₚ′-up N₁<:ₜN₂) = <:-up (sound-algₜ N₁<:ₜN₂)
sound-algₚ′ <:ₚ′-var = <:-refl

sound-algₚ : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto T₁}{N₂ : NormalProto T₂}
  → N₁ <:ₚ N₂ → T₁ <: T₂
sound-algₚ (<:ₚ-plus N₁<:N₂) = sound-algₚ′ N₁<:N₂
sound-algₚ (<:ₚ-minus N₂<:N₁) = <:-minus (sound-algₚ′ N₂<:N₁)

sound-<<:ₚ {⊙ = ⊕} N₁<<:N₂ = sound-algₚ N₁<<:N₂
sound-<<:ₚ {⊙ = ⊝} N₁<<:N₂ = sound-algₚ N₁<<:N₂
sound-<<:ₚ {⊙ = ⊘} refl = ≡c-refl

sound-<<:ₚ′ {⊙ = ⊕} N₁<<:N₂ = sound-algₚ′ N₁<<:N₂
sound-<<:ₚ′ {⊙ = ⊝} N₁<<:N₂ = sound-algₚ′ N₁<<:N₂
sound-<<:ₚ′ {⊙ = ⊘} refl = ≡c-refl

sound-algₜ <:ₜ-var = <:-refl
sound-algₜ <:ₜ-base = <:-refl
sound-algₜ (<:ₜ-arrow M₂<:ₜM₁ N₁<:ₜN₂) = <:-fun (sound-algₜ M₂<:ₜM₁) (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-poly N₁<:ₜN₂) = <:-all (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-sub {km≤ = km≤} N₁<:ₜN₂) = <:-sub km≤ (sound-algₜ N₁<:ₜN₂)
sound-algₜ <:ₜ-end = <:-refl
sound-algₜ (<:ₜ-msg {p = p} P₁<<P₂ N₁<:ₜN₂) = <:-msg (sound-<<:ₚ′ P₁<<P₂) (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-data N₁<:ₜN₂) = <:-protoD (sound-algₜ N₁<:ₜN₂)


-- algorithmic subtyping is antisymmetric

<:ₜ-pre-antisym : ∀ {T₁ T₂ : Ty Δ (KV pk m)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂} → N₁ <:ₜ N₂ → N₂ <:ₜ N₁ → T₁ ≡ T₂
<:ₚ′-pre-antisym : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto′ T₁} {N₂ : NormalProto′ T₂} → N₁ <:ₚ′ N₂ → N₂ <:ₚ′ N₁ → T₁ ≡ T₂
<:ₚ-pre-antisym : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto T₁} {N₂ : NormalProto T₂} → N₁ <:ₚ N₂ → N₂ <:ₚ N₁ → T₁ ≡ T₂

<:ₜ-pre-antisym <:ₜ-var <:ₜ-var = refl
<:ₜ-pre-antisym <:ₜ-base <:ₜ-base = refl
<:ₜ-pre-antisym (<:ₜ-arrow N₁<:N₂ N₁<:N₃) (<:ₜ-arrow N₂<:N₁ N₂<:N₂) rewrite <:ₜ-pre-antisym N₁<:N₂ N₂<:N₁ | <:ₜ-pre-antisym N₁<:N₃ N₂<:N₂ = refl
<:ₜ-pre-antisym (<:ₜ-poly N₁<:N₂) (<:ₜ-poly N₂<:N₁) rewrite <:ₜ-pre-antisym N₁<:N₂ N₂<:N₁ = refl
<:ₜ-pre-antisym (<:ₜ-sub N₁<:N₂) (<:ₜ-sub N₂<:N₁) rewrite <:ₜ-pre-antisym N₁<:N₂ N₂<:N₁ = refl
<:ₜ-pre-antisym <:ₜ-end <:ₜ-end = refl
<:ₜ-pre-antisym (<:ₜ-msg {p = ⊕} T₁<<:T₂ N₁<:N₂) (<:ₜ-msg T₂<<:T₁ N₂<:N₁) rewrite <:ₜ-pre-antisym N₁<:N₂ N₂<:N₁ | <:ₚ′-pre-antisym T₁<<:T₂ T₂<<:T₁ = refl
<:ₜ-pre-antisym (<:ₜ-msg {p = ⊝} T₁<<:T₂ N₁<:N₂) (<:ₜ-msg T₂<<:T₁ N₂<:N₁) rewrite <:ₜ-pre-antisym N₁<:N₂ N₂<:N₁ | <:ₚ′-pre-antisym T₁<<:T₂ T₂<<:T₁ = refl
<:ₜ-pre-antisym (<:ₜ-data N₁<:N₂) (<:ₜ-data N₂<:N₁) rewrite <:ₜ-pre-antisym N₁<:N₂ N₂<:N₁ = refl

<:ₚ′-pre-antisym (<:ₚ′-proto {⊙ = ⊕} #c₁⊆#c₂ N₁<<:N₂) (<:ₚ′-proto #c₂⊆#c₁ N₂<<:N₁) rewrite ⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁ | <:ₚ-pre-antisym N₁<<:N₂ N₂<<:N₁ = refl
<:ₚ′-pre-antisym (<:ₚ′-proto {⊙ = ⊝} #c₁⊆#c₂ N₁<<:N₂) (<:ₚ′-proto #c₂⊆#c₁ N₂<<:N₁) rewrite ⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁ | <:ₚ-pre-antisym N₁<<:N₂ N₂<<:N₁ = refl
<:ₚ′-pre-antisym (<:ₚ′-proto {⊙ = ⊘} #c₁⊆#c₂ refl) (<:ₚ′-proto #c₂⊆#c₁ refl) rewrite ⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁ = refl
<:ₚ′-pre-antisym (<:ₚ′-up N₁<:N₂) (<:ₚ′-up N₂<:N₁) rewrite <:ₜ-pre-antisym N₁<:N₂ N₂<:N₁ = refl
<:ₚ′-pre-antisym <:ₚ′-var <:ₚ′-var = refl

<:ₚ-pre-antisym (<:ₚ-plus N₁<:N₂) (<:ₚ-plus N₂<:N₁) rewrite <:ₚ′-pre-antisym N₁<:N₂ N₂<:N₁ = refl
<:ₚ-pre-antisym (<:ₚ-minus N₁<:N₂) (<:ₚ-minus N₂<:N₁) rewrite <:ₚ′-pre-antisym N₁<:N₂ N₂<:N₁ = refl

<:ₜ-antisym : ∀ {T₁ T₂ : Ty Δ (KV pk m)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂} → (N₁<:N₂ : N₁ <:ₜ N₂) → (N₂<:N₁ : N₂ <:ₜ N₁) → subst NormalTy (<:ₜ-pre-antisym N₁<:N₂ N₂<:N₁) N₁ ≡ N₂
<:ₜ-antisym {N₁ = N₁}{N₂ = N₂} N₁<:N₂ N₂<:N₁ = sym (nt-unique-eq (<:ₜ-pre-antisym N₁<:N₂ N₂<:N₁) N₂ N₁)

<:ₚ-antisym : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto T₁} {N₂ : NormalProto T₂} → (N₁<:N₂ : N₁ <:ₚ N₂) → (N₂<:N₁ : N₂ <:ₚ N₁) → subst NormalProto (<:ₚ-pre-antisym N₁<:N₂ N₂<:N₁) N₁ ≡ N₂
<:ₚ-antisym {N₁ = N₁} {N₂} N₁<:N₂ N₂<:N₁ = sym (np-unique-eq (<:ₚ-pre-antisym N₁<:N₂ N₂<:N₁) N₂ N₁)

<:ₚ′-antisym : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto′ T₁} {N₂ : NormalProto′ T₂} → (N₁<:N₂ : N₁ <:ₚ′ N₂) → (N₂<:N₁ : N₂ <:ₚ′ N₁) → subst NormalProto′ (<:ₚ′-pre-antisym N₁<:N₂ N₂<:N₁) N₁ ≡ N₂
<:ₚ′-antisym {N₁ = N₁} {N₂} N₁<:N₂ N₂<:N₁ = sym (np′-unique-eq (<:ₚ′-pre-antisym N₁<:N₂ N₂<:N₁) N₂ N₁)
