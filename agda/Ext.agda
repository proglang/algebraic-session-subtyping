module Ext where

open import Relation.Binary.PropositionalEquality using (_≡_)

-- extensionality

postulate
  ext : {A B : Set} (f g : A → B) → (∀ x → f x ≡ g x) → f ≡ g

