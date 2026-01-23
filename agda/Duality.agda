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
  p p₁ : Polarity

invert : Polarity → Polarity
invert ⊕ = ⊝
invert ⊝ = ⊕

invert-involution : invert (invert p) ≡ p
invert-involution {⊕} = refl
invert-involution {⊝} = refl

mult : Polarity → Polarity → Polarity
mult ⊕ p = p
mult ⊝ p = invert p

mult-identityˡ : ∀ p → mult ⊕ p ≡ p
mult-identityˡ p = refl

mult-identityʳ : ∀ p → mult p ⊕ ≡ p
mult-identityʳ ⊕ = refl
mult-identityʳ ⊝ = refl

mult-⊖-invert : ∀ p → mult ⊝ p ≡ invert p
mult-⊖-invert p = refl

mult-comm : ∀ p₁ p₂ → mult p₁ p₂ ≡ mult p₂ p₁
mult-comm ⊕ ⊕ = refl
mult-comm ⊕ ⊝ = refl
mult-comm ⊝ ⊕ = refl
mult-comm ⊝ ⊝ = refl

mult-invert-invert : ∀ p₁ p₂ → mult (invert p₁) p₂ ≡ mult p₁ (invert p₂)
mult-invert-invert ⊕ p₂ = refl
mult-invert-invert ⊝ p₂ = sym invert-involution

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
