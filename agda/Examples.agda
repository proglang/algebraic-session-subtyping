
open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Nat
open import Data.Fin.Subset as Subset using (_⊆_; ⁅_⁆; ⊤)
open import Data.Fin.Subset.Properties using (⊆-refl; ⊆⊤)
open import Data.List
open import Data.Product
-- open import Data.Sum
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; inspect; Reveal_·_is_)

module Examples where

open import Util
open import Kinds
open import Duality
open import Types
open import Subtyping

-- Q: should we change the definition to address non-parametric protocols explicitly?

---- protocol defintions

-- proto Alt X = A0 | A1

T-Alt : Subset.Subset 2 → Ty [] KP
T-Alt ctrs = T-ProtoP ctrs ⊘ (T-Up T-Base)

-- proto Inv X = Inv -X

T-Inv : Subset.Subset 2 → Ty [] KP
T-Inv ctrs = T-ProtoP{k = 1} ⁅ zero ⁆ ⊝ (T-Alt ctrs)

T-Inv-Minus : Subset.Subset 2 → Ty [] KP
T-Inv-Minus ctrs = T-ProtoP{k = 1} ⁅ zero ⁆ ⊝ (T-Minus (T-Alt ctrs))


-- proto Id X = Id X

T-Id : Subset.Subset 2 → Ty [] KP
T-Id ctrs = T-ProtoP{k = 1}  ⁅ zero ⁆ ⊕ (T-Alt ctrs)

T-Id-Minus : Subset.Subset 2 → Ty [] KP
T-Id-Minus ctrs = T-ProtoP{k = 1}  ⁅ zero ⁆ ⊕ (T-Minus (T-Alt ctrs))

---- subtyping judgments

-- given that c⊆d ...

-- Alt[c] <: Alt[d]

st-alt : ∀ {c d} (c⊆d : c ⊆ d) → T-Alt c <: T-Alt d
st-alt c⊆d = <:-proto c⊆d ≡c-refl

-- Id (Alt[c]) <: Id (Alt[d])

st-id : ∀ {c d} (c⊆d : c ⊆ d) → T-Id c <: T-Id d
st-id c⊆d = <:-proto ⊆-refl (st-alt c⊆d)

-- Inv (Alt[d]) <: Inv (Alt[c])

st-inv : ∀ {c d} (c⊆d : c ⊆ d) → T-Inv d <: T-Inv c
st-inv c⊆d = <:-proto ⊆-refl (st-alt c⊆d)

-- Id (-Alt[d]) <: Id (-Alt[c])

st-id-minus : ∀ {c d} (c⊆d : c ⊆ d) → T-Id-Minus d <: T-Id-Minus c
st-id-minus c⊆d = <:-proto ⊆-refl (<:-minus (st-alt c⊆d))

-- Inv (-Alt[c]) <: Inv (-Alt[d])

st-inv-minus : ∀ {c d} (c⊆d : c ⊆ d) → T-Inv-Minus c <: T-Inv-Minus d
st-inv-minus c⊆d = <:-proto ⊆-refl (<:-minus (st-alt c⊆d))
