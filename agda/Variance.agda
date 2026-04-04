module Variance where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
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

vcompose-assoc :
  ∀ v₁ v₂ v₃ → vcompose (vcompose v₁ v₂) v₃ ≡ vcompose v₁ (vcompose v₂ v₃)
vcompose-assoc ⊕ v₂ v₃ = refl
vcompose-assoc ⊝ ⊕ v₃ = refl
vcompose-assoc ⊝ ⊝ ⊕ = refl
vcompose-assoc ⊝ ⊝ ⊝ = refl
vcompose-assoc ⊝ ⊝ ⊘ = refl
vcompose-assoc ⊝ ⊘ v₃ = refl
vcompose-assoc ⊘ v₂ v₃ = refl

vcompose-swap :
  ∀ v₁ v₂ → vcompose (vswap v₁) v₂ ≡ vcompose v₁ (vswap v₂)
vcompose-swap ⊕ v₂ = refl
vcompose-swap ⊝ ⊕ = refl
vcompose-swap ⊝ ⊝ = refl
vcompose-swap ⊝ ⊘ = refl
vcompose-swap ⊘ v₂ = refl

VarianceCovers : Variance → Variance → Set
VarianceCovers ⊕ ⊕ = ⊤
VarianceCovers ⊝ ⊝ = ⊤
VarianceCovers ⊘ v = ⊤
VarianceCovers _ _ = ⊥

compose-covers :
  ∀ {v v₁ v₂}
  → VarianceCovers v₁ v₂
  → VarianceCovers (vcompose v₁ v) (vcompose v₂ v)
compose-covers {v = ⊕} {v₁ = ⊕} {⊕} cov = tt
compose-covers {v = ⊝} {v₁ = ⊕} {⊕} cov = tt
compose-covers {v = ⊘} {v₁ = ⊕} {⊕} cov = tt
compose-covers {v = ⊕} {v₁ = ⊝} {⊝} cov = tt
compose-covers {v = ⊝} {v₁ = ⊝} {⊝} cov = tt
compose-covers {v = ⊘} {v₁ = ⊝} {⊝} cov = tt
compose-covers {v = ⊕} {v₁ = ⊘} cov = tt
compose-covers {v = ⊝} {v₁ = ⊘} cov = tt
compose-covers {v = ⊘} {v₁ = ⊘} cov = tt

⊙-equal : (v₁ v₂ : Variance) → Dec (v₁ ≡ v₂)
⊙-equal ⊕ ⊕ = yes refl
⊙-equal ⊕ ⊝ = no λ()
⊙-equal ⊕ ⊘ = no λ()
⊙-equal ⊝ ⊕ = no λ()
⊙-equal ⊝ ⊝ = yes refl
⊙-equal ⊝ ⊘ = no λ()
⊙-equal ⊘ ⊕ = no λ()
⊙-equal ⊘ ⊝ = no λ()
⊙-equal ⊘ ⊘ = yes refl

vpos : Variance → Set
vpos ⊕ = ⊤
vpos ⊝ = ⊥
vpos ⊘ = ⊤
