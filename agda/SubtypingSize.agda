open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Subtyping
open import Types

module SubtypingSize where

-- A size measure for algorithmic subtyping derivations.
-- Always returns a Nat > 0, and exposes the top-level `suc` before inspecting the derivation.

size-<: : ∀ {Δ K} {T₁ T₂ : Ty Δ K} → T₁ <: T₂ → ℕ
size-<: d = suc (size-<:-aux d)
  where
    -- This auxiliary may return zero; the outer `suc` ensures positivity
    -- and makes the constructor of the result visible without pattern matching.
    size-<:-aux : ∀ {Δ K} {T₁ T₂ : Ty Δ K} → T₁ <: T₂ → ℕ

    -- Size for the variance-directed relation `T₁ <<:[ ⊙ ] T₂`.
    -- For ⊕/⊝ it is just a (possibly flipped) subtyping derivation.
    -- For ⊘ it's a kinded equality proof; we assign it size 0 here.
    size-<<: : ∀ {Δ K} {T₁ T₂ : Ty Δ K} {⊙ : Variance} → T₁ <<:[ ⊙ ] T₂ → ℕ


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
