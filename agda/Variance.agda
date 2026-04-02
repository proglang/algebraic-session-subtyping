module Variance where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)

-- variance of parameter of protocol type constructor
-- ⊕ : covariant - parameter appears under even number of polarity flips
-- ⊝ : contravariant - parameter appears under odd number of polarity flips
-- ⊘ : invariant - parameter appears in both positive and negative positions

data Variance : Set where
  ⊕ ⊝ ⊘ : Variance

variable
  ⊙ ⊙₁ ⊙₂ : Variance

vswap : Variance → Variance
vswap ⊕ = ⊝
vswap ⊝ = ⊕
vswap ⊘ = ⊘

vcompose : Variance → Variance → Variance
vcompose ⊕ v = v
vcompose ⊝ v = vswap v
vcompose ⊘ v = ⊘

vcompose-⊕ : ∀ v → vcompose v ⊕ ≡ v
vcompose-⊕ ⊕ = refl
vcompose-⊕ ⊝ = refl
vcompose-⊕ ⊘ = refl

vcompose-⊝ : ∀ v → vcompose v ⊝ ≡ vswap v
vcompose-⊝ ⊕ = refl
vcompose-⊝ ⊝ = refl
vcompose-⊝ ⊘ = refl

vcompose-⊘ : ∀ v → vcompose v ⊘ ≡ ⊘
vcompose-⊘ ⊕ = refl
vcompose-⊘ ⊝ = refl
vcompose-⊘ ⊘ = refl

vcompose-sym : ∀ v₁ v₂ → vcompose v₁ v₂ ≡ vcompose v₂ v₁
vcompose-sym ⊕ v = sym (vcompose-⊕ v)
vcompose-sym ⊝ v = sym (vcompose-⊝ v)
vcompose-sym ⊘ v = sym (vcompose-⊘ v)

vpos : Variance → Set
vpos ⊕ = ⊤
vpos ⊝ = ⊥
vpos ⊘ = ⊤
