module Util where

open import Data.List using  (List; _∷_)
open import Data.List.Relation.Unary.Any using (here; there) public 
open import Data.List.Membership.Propositional using (_∈_; _∉_) public
open import Data.Maybe using (just)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Ext using (ext)

Rel : Set → Set₁
Rel A = A → A → Set

dependent-ext₂ :
  ∀ {A : Set} {B : A → Set} {C : Set}
    {f g : (x : A) → B x → C}
  → (∀ x y → f x y ≡ g x y)
  → f ≡ g
dependent-ext₂ {A = A} {B = B} {C = C} {f = f} {g = g} eq =
  cong recurry
    (ext uncurry-f uncurry-g (λ where (x , y) → eq x y))
  where
  uncurry-f : Σ A B → C
  uncurry-f (x , y) = f x y

  uncurry-g : Σ A B → C
  uncurry-g (x , y) = g x y

  recurry : (Σ A B → C) → (x : A) → B x → C
  recurry h x y = h (x , y)

just-injective :
  ∀ {a} {A : Set a} {x y : A}
  → just x ≡ just y
  → x ≡ y
just-injective refl = refl

variable
  A B : Set
  a a₁ a₂ : A
  as : List A
