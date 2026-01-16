
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

---- protocol definitions

-- proto Alt X = A0 | A1

E-Alt : Subset.Subset 2 → Ty [] KP
E-Alt ctrs = T-ProtoP ctrs ⊘ (T-Up T-Base)

-- proto Inv X = Inv -X

E-Inv : Subset.Subset 2 → Ty [] KP
E-Inv ctrs = T-ProtoP{k = 1} ⁅ zero ⁆ ⊝ (E-Alt ctrs)

E-Inv-Minus : Subset.Subset 2 → Ty [] KP
E-Inv-Minus ctrs = T-ProtoP{k = 1} ⁅ zero ⁆ ⊝ (T-Minus (E-Alt ctrs))


-- proto Id X = Id X

E-Id : Subset.Subset 2 → Ty [] KP
E-Id ctrs = T-ProtoP{k = 1}  ⁅ zero ⁆ ⊕ (E-Alt ctrs)

E-Id-Minus : Subset.Subset 2 → Ty [] KP
E-Id-Minus ctrs = T-ProtoP{k = 1} ⁅ zero ⁆ ⊕ (T-Minus (E-Alt ctrs))

E-Id′ : ∀ {Δ} → Ty Δ KP → Ty Δ KP
E-Id′ P = T-ProtoP{k = 1} ⁅ zero ⁆ ⊕ P

-- a parameterized protocol with two alternatives
-- (so that we can have nontrivial subtyping)

-- proto SX X = S1 X | S2 X

E-SX : ∀ {Δ} → Subset.Subset 2 → Ty Δ KP → Ty Δ KP
E-SX ctrs X = T-ProtoP ctrs ⊕ X


---- subtyping judgments

-- given that c⊆d ...

-- Alt[c] <: Alt[d]

st-alt : ∀ {c d} (c⊆d : c ⊆ d) → E-Alt c <: E-Alt d
st-alt c⊆d = <:-proto c⊆d ≡c-refl

-- Id (Alt[c]) <: Id (Alt[d])

st-id : ∀ {c d} (c⊆d : c ⊆ d) → E-Id c <: E-Id d
st-id c⊆d = <:-proto ⊆-refl (st-alt c⊆d)

-- Inv (Alt[d]) <: Inv (Alt[c])

st-inv : ∀ {c d} (c⊆d : c ⊆ d) → E-Inv d <: E-Inv c
st-inv c⊆d = <:-proto ⊆-refl (st-alt c⊆d)

-- Id (-Alt[d]) <: Id (-Alt[c])

st-id-minus : ∀ {c d} (c⊆d : c ⊆ d) → E-Id-Minus d <: E-Id-Minus c
st-id-minus c⊆d = <:-proto ⊆-refl (<:-minus (st-alt c⊆d))

-- Inv (-Alt[c]) <: Inv (-Alt[d])

st-inv-minus : ∀ {c d} (c⊆d : c ⊆ d) → E-Inv-Minus c <: E-Inv-Minus d
st-inv-minus c⊆d = <:-proto ⊆-refl (<:-minus (st-alt c⊆d))

-- question: is subtyping closed under substitution?
-- the suspicion was that substituting negative types might lead to problems
-- but the example shows that it does not

-- SX[c] X <: SX[d] X

st-sx : ∀ {c d}  (c⊆d : c ⊆ d) → E-SX{Δ = KP ∷ []} c (T-Var (here refl)) <: E-SX d (T-Var (here refl))
st-sx c⊆d = <:-proto c⊆d <:-refl

st-sx-alt : ∀ {c d}  (c⊆d : c ⊆ d) → E-SX c (E-Alt c) <: E-SX d (E-Alt c)
st-sx-alt c⊆d = <:-proto c⊆d (<:-proto ⊆-refl ≡c-refl)

st-sx-alt-minus : ∀ {c d}  (c⊆d : c ⊆ d) → E-SX c (T-Minus (E-Alt c)) <: E-SX d (T-Minus (E-Alt c))
st-sx-alt-minus c⊆d = <:-proto c⊆d (<:-minus (<:-proto ⊆-refl ≡c-refl))

