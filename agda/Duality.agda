module Duality where

open import Data.Sum
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)

open import Ext
open import Kinds

data Polarity : Set where
  ⊕ ⊝ : Polarity

variable
  p p₁ p₂ : Polarity

-- inversion and properties

invert : Polarity → Polarity
invert ⊕ = ⊝
invert ⊝ = ⊕

invert-involution : invert (invert p) ≡ p
invert-involution {⊕} = refl
invert-involution {⊝} = refl

invert-injective : invert p₁ ≡ invert p₂ → p₁ ≡ p₂
invert-injective {⊕} {⊕} ip≡ = refl
invert-injective {⊝} {⊝} ip≡ = refl

-- multiplication and properties

mult : Polarity → Polarity → Polarity
mult ⊕ p = p
mult ⊝ p = invert p

-- definitional
mult-identityˡ : ∀ p → mult ⊕ p ≡ p
mult-identityˡ p = refl

mult-identityʳ : ∀ p → mult p ⊕ ≡ p
mult-identityʳ ⊕ = refl
mult-identityʳ ⊝ = refl

-- definitional
mult-invertˡ : ∀ p → mult ⊝ p ≡ invert p
mult-invertˡ p = refl

mult-invertʳ : ∀ p → mult p ⊝ ≡ invert p
mult-invertʳ ⊕ = refl
mult-invertʳ ⊝ = refl

mult-comm : ∀ p₁ p₂ → mult p₁ p₂ ≡ mult p₂ p₁
mult-comm ⊕ ⊕ = refl
mult-comm ⊕ ⊝ = refl
mult-comm ⊝ ⊕ = refl
mult-comm ⊝ ⊝ = refl

mult-assoc : ∀ p₁ p₂ p₃ → mult p₁ (mult p₂ p₃) ≡ mult (mult p₁ p₂) p₃
mult-assoc ⊕ p₂ p₃ = refl
mult-assoc ⊝ ⊕ p₃ = refl
mult-assoc ⊝ ⊝ p₃ = invert-involution

mult-square : ∀ p → mult p p ≡ ⊕
mult-square ⊕ = refl
mult-square ⊝ = refl

mult-inv-square : ∀ p → mult p (invert p) ≡ ⊝
mult-inv-square ⊕ = refl
mult-inv-square ⊝ = refl

mult-invert-invert : ∀ p₁ p₂ → mult (invert p₁) p₂ ≡ mult p₁ (invert p₂)
mult-invert-invert ⊕ p₂ = refl
mult-invert-invert ⊝ p₂ = sym invert-involution

-- definitional
mult-invert : mult ⊝ p ≡ mult ⊕ (invert p)
mult-invert = refl

mult-invert-⊕ : mult ⊕ p ≡ mult ⊝ (invert p)
mult-invert-⊕ = sym invert-involution

mult-invert-⊕-invert : invert (mult ⊕ (invert p)) ≡ mult ⊕ p
mult-invert-⊕-invert = invert-involution

invert-mult-⊙ : ∀ p {⊙} → invert (mult ⊙ p) ≡ mult ⊙ (invert p)
invert-mult-⊙ p {⊕} = refl
invert-mult-⊙ p {⊝} = refl


data Dualizable : Kind → Set where
  D-S : Dualizable (KV KS m)

dualizable-sub : Dualizable K → K₁ ≤k K → Dualizable K₁
dualizable-sub D-S (≤k-step ≤p-refl x₁) = D-S

p-dual : ∀ p → (p ≡ ⊝ → Dualizable K) → p ≡ ⊕ ⊎ Dualizable K
p-dual ⊕ f = inj₁ refl
p-dual ⊝ f = inj₂ (f refl)

¬-dual-mun : ¬ Dualizable MUn
¬-dual-mun ()

¬-dual-m≤ : (M≤ : KM ≤p pk) → ¬ Dualizable (KV pk m)
¬-dual-m≤ ≤p-refl ()
¬-dual-m≤ (≤p-step <p-mt) ()

¬-dual-p : ¬ Dualizable KP
¬-dual-p ()


dual-s-irrelevant : (a b : Dualizable (KV KS m)) → a ≡ b
dual-s-irrelevant D-S D-S = refl

ext-dual-s-irrelevant : (f g : ⊝ ≡ ⊝ → Dualizable (KV KS m)) → f ≡ g
ext-dual-s-irrelevant f g = ext f g (λ x → dual-s-irrelevant (f x) (g x))


dual-irrelevant : ∀ {K} → (f g : ⊝ ≡ ⊝ → Dualizable K) → f ≡ g
dual-irrelevant {KV KM x₁} f g with () ← f refl
dual-irrelevant {KV KS x₁} f g = ext-dual-s-irrelevant f g
dual-irrelevant {KV KT x₁} f g with () ← f refl
dual-irrelevant {KP} f g with () ← f refl

dual-all-irrelevant : ∀ {p} {K} → (f g : p ≡ ⊝ → Dualizable K) → f ≡ g
dual-all-irrelevant {⊕} f g = ext f g (λ())
dual-all-irrelevant {⊝} f g = dual-irrelevant f g

-- use this definition instead of (λ()) to enable rewriting

d?⊥ : (⊕ ≡ ⊝ → Dualizable K)
d?⊥ ()

d?S : ∀ {p} → p ≡ ⊝ → Dualizable (KV KS m)
d?S _ = D-S
