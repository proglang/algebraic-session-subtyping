module Util where

open import Data.List using  (List; _∷_)
open import Data.List.Relation.Unary.Any using (here; there) public 
open import Data.List.Membership.Propositional using (_∈_; _∉_) public

Rel : Set → Set₁
Rel A = A → A → Set

variable
  A B : Set
  a a₁ a₂ : A
  as : List A

