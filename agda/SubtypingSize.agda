open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Product

open import Kinds
open import Duality
open import Types
open import Subtyping
open import SubtypingProperties

module SubtypingSize where

-- A size measure for algorithmic subtyping derivations.
-- Always returns a Nat > 0, and exposes the top-level `suc` before inspecting the derivation.

size-<:   : ∀ {Δ K} {T₁ T₂ : Ty Δ K} → T₁ <: T₂ → ℕ
size-<<:  : ∀ {Δ K} {T₁ T₂ : Ty Δ K} {⊙ : Variance} → T₁ <<:[ ⊙ ] T₂ → ℕ

private
    -- This auxiliary may return zero; the outer `suc` ensures positivity
    -- and makes the constructor of the result visible without pattern matching.
    size-<:-aux : ∀ {Δ K} {T₁ T₂ : Ty Δ K} → T₁ <: T₂ → ℕ

    -- Size for the variance-directed relation `T₁ <<:[ ⊙ ] T₂`.
    -- For ⊕/⊝ it is just a (possibly flipped) subtyping derivation.
    -- For ⊘ it's a kinded equality proof; we assign it size 0 here.


    size-<:-aux (<:-trans d₁ d₂) = size-<: d₁ + size-<: d₂

    size-<:-aux (<:-sub _ d) = size-<: d
    size-<:-aux <:-sub-dual-l = zero
    size-<:-aux <:-sub-dual-r = zero

    size-<:-aux <:-var = zero
    size-<:-aux <:-dual-var = zero
    size-<:-aux <:-base = zero

    size-<:-aux (<:-fun ddom dcod) = size-<: ddom + size-<: dcod
    size-<:-aux (<:-protoD d) = size-<: d
    size-<:-aux (<:-all d) = size-<: d

    size-<:-aux (<:-msg-minus _ ) = zero
    size-<:-aux (<:-minus-msg _ ) = zero

    size-<:-aux (<:-dual-dual-l-new _ ) = zero
    size-<:-aux (<:-dual-dual-r-new _ ) = zero

    size-<:-aux (<:-dual-msg-l-new _ ) = zero
    size-<:-aux (<:-dual-msg-r-new _ ) = zero

    size-<:-aux <:-dual-end-l = zero
    size-<:-aux <:-dual-end-r = zero

    size-<:-aux (<:-msg d<< dS) = size-<<: d<< + size-<: dS
    size-<:-aux <:-end = zero
    size-<:-aux (<:-up d) = size-<: d

    size-<:-aux (<:-proto _ d<<) = size-<<: d<<
    size-<:-aux (<:-minus d) = size-<: d
    size-<:-aux (<:-minus-minus-l d) = size-<: d
    size-<:-aux (<:-minus-minus-r d) = size-<: d


size-<<: {⊙ = ⊕} d = size-<: d
size-<<: {⊙ = ⊝} d = size-<: d
size-<<: {⊙ = ⊘} T₁≡cT₂ = zero

size-<: d = suc (size-<:-aux d)

{-
lemma-sub-loop : ∀ {p₃} {T₁ T₂ : Ty Δ KP} (T₁<<:T₂ : T₁ <<:[ injᵥ p₃ ] T₂)
  → t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₂ <<:[ injᵥ (t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₁) ] t-loop p₃ (nf ⊕ d?⊥ T₂) .proj₂
-}
{- may not be true
lemma-sub-loop-preserves-size : {T₁ T₂ : Ty Δ KP} → ∀ p → (T₁<<:T₂ : T₁ <<:[ injᵥ p ] T₂) →
  size-<<: (lemma-sub-loop T₁<<:T₂) ≤ size-<<: T₁<<:T₂
lemma-sub-loop-preserves-size {T₁ = T₁} {T₂ = T₃} ⊕ (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃) = {!!}
lemma-sub-loop-preserves-size ⊕ <:-var = s≤s z≤n
lemma-sub-loop-preserves-size ⊕ (<:-up T₁<<:T₂) = {!!}
lemma-sub-loop-preserves-size ⊕ (<:-proto x x₁) = {!!}
lemma-sub-loop-preserves-size ⊕ (<:-minus T₁<<:T₂) = {!!}
lemma-sub-loop-preserves-size ⊕ (<:-minus-minus-l T₁<<:T₂) = {!!}
lemma-sub-loop-preserves-size ⊕ (<:-minus-minus-r T₁<<:T₂) = {!!}
lemma-sub-loop-preserves-size ⊝ T₁<<:T₂ = {!!}
-}
