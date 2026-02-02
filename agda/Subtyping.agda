open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Nat
open import Data.Fin.Subset as Subset using (_⊆_)
open import Data.Fin.Subset.Properties using (⊆-refl)
open import Data.List
open import Data.Product
-- open import Data.Sum
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; inspect; Reveal_·_is_)

open import Function using (id)

module Subtyping  where

-- 2025

open import Util
open import Kinds
open import Duality
open import Types

injᵥ : Polarity → Variance
injᵥ ⊕ = ⊝
injᵥ ⊝ = ⊕

-- subtyping

data _<:_ {Δ} : {K : Kind} → Rel (Ty Δ K)

_<<:[_]_ : Ty Δ K → Variance → Ty Δ K → Set
T₁ <<:[ ⊕ ] T₂ = T₁ <: T₂
T₁ <<:[ ⊝ ] T₂ = T₂ <: T₁
T₁ <<:[ ⊘ ] T₂ = T₁ ≡c T₂

invert-<<: : ∀ p → T₁ <<:[ injᵥ p ] T₂ ≡ T₂ <<:[ injᵥ (invert p) ] T₁
invert-<<: ⊕ = refl
invert-<<: ⊝ = refl

data _<:_ {Δ} where
  -- <:-refl  : T <: T
  <:-trans : T₁ <: T₂ → T₂ <: T₃ → T₁ <: T₃

  <:-sub  : (K≤K′ : KV pk m ≤k KV pk′ m′) → T₁ <: T₂ → T-Sub K≤K′ T₁ <: T-Sub K≤K′ T₂
  <:-sub-dual-l : {T : Ty Δ (KV KS m)} {K≤K′ : KV KS m ≤k KV KS m′}
    → T-Dual D-S (T-Sub K≤K′ T) <: T-Sub K≤K′ (T-Dual D-S T)
  <:-sub-dual-r : {T : Ty Δ (KV KS m)} {K≤K′ : KV KS m ≤k KV KS m′}
    → T-Sub K≤K′ (T-Dual D-S T) <: T-Dual D-S (T-Sub K≤K′ T)

  <:-var : ∀ {x : K ∈ Δ} → T-Var x <: T-Var x
  <:-dual-var : ∀ {x : (KV KS m) ∈ Δ} → T-Dual D-S (T-Var x) <: T-Dual D-S (T-Var x)
  <:-base : T-Base <: T-Base
  <:-fun : ∀ {pk : PreKind} {≤pk : KM ≤p pk} {m}
    → T₃ <: T₁ → T₂ <: T₄
    → T-Arrow {m = m} ≤pk T₁ T₂ <: T-Arrow ≤pk T₃ T₄
  <:-protoD : T₁ <: T₂ → T-ProtoD T₁ <: T-ProtoD T₂
  <:-all : {T₁ T₂ : Ty (K′ ∷ Δ) (KV KT m)} → T₁ <: T₂ → T-Poly T₁ <: T-Poly T₂

  -- obsolete
  -- <:-neg-l : T-Msg (invert p) T S <: S′ → T-Msg p (T-Minus T) S <: S′
  -- <:-neg-r : S′ <: T-Msg (invert p) T S → S′ <: T-Msg p (T-Minus T) S
  -- replace by
  <:-msg-minus : p₂ ≡ invert p₁ → T-Msg p₁ (T-Minus T) S <: T-Msg p₂ T S
  <:-minus-msg : p₁ ≡ invert p₂ → T-Msg p₂ T S <: T-Msg p₁ (T-Minus T) S

  -- this rule is derivable
  -- <:-dual-lr : {T₁ T₂ : Ty Δ K} (d : Dualizable K) → T₂ <: T₁ → T-Dual d T₁ <: T-Dual d T₂
  -- <:-dual-dual-l : (d : Dualizable K) → T₁ <: T₂ → T-Dual d (T-Dual d T₁) <: T₂
  -- <:-dual-dual-r : (d : Dualizable K) → T₁ <: T₂ → T₁ <: T-Dual d (T-Dual d T₂)
  <:-dual-dual-l-new : (d : Dualizable K) → T-Dual d (T-Dual d T) <: T
  <:-dual-dual-r-new : (d : Dualizable K) → T <: T-Dual d (T-Dual d T)

  -- <:-dual-msg-l : T-Msg (invert p) T (T-Dual D-S S) <: T₂ → T-Dual D-S (T-Msg p T S) <: T₂
  -- <:-dual-msg-r : T₁ <: T-Msg (invert p) T (T-Dual D-S S) → T₁ <: T-Dual D-S (T-Msg p T S)
  <:-dual-msg-l-new : p₂ ≡ invert p₁ → T-Msg p₁ T (T-Dual D-S S) <: T-Dual D-S (T-Msg p₂ T S)
  <:-dual-msg-r-new : p₁ ≡ invert p₂ → T-Dual D-S (T-Msg p₁ T S) <: T-Msg p₂ T (T-Dual D-S S)

  <:-dual-end-l  : T-Dual D-S T-End <: T-End
  <:-dual-end-r  : T-End <: T-Dual D-S T-End

  <:-msg : T₁ <<:[ injᵥ p ] T₂ → S₁ <: S₂ → T-Msg p T₁ S₁ <: T-Msg p T₂ S₂
  <:-end : T-End <: T-End
  <:-up : T₁ <: T₂ → T-Up T₁ <: T-Up T₂

  -- protocol kinds
  
  <:-proto : #c₁ ⊆ #c₂ → T₁ <<:[ ⊙ ] T₂
    → T-ProtoP #c₁ ⊙ T₁ <: T-ProtoP #c₂ ⊙ T₂
  <:-minus : T₂ <: T₁ → T-Minus T₁ <: T-Minus T₂
  <:-minus-minus-l : T₁ <: T₂ → T-Minus (T-Minus T₁) <: T₂
  <:-minus-minus-r : T₁ <: T₂ → T₁ <: T-Minus (T-Minus T₂)

-- reflexivity is derivable

<:-refl : ∀ {T : Ty Δ K} → T <: T
<:-refl-dual : ∀ {T : Ty Δ (KV KS m)} → T-Dual D-S T <: T-Dual D-S T
<<:-refl : ∀ {T : Ty Δ K} {⊙} → T <<:[ ⊙ ] T

<:-refl {T = T-Var x} = <:-var
<:-refl {T = T-Base} = <:-base
<:-refl {T = T-Arrow x T T₁} = <:-fun <:-refl <:-refl
<:-refl {T = T-Poly T} = <:-all <:-refl
<:-refl {T = T-Sub x T} = <:-sub x <:-refl
<:-refl {T = T-Dual D-S T} = <:-refl-dual
<:-refl {T = T-End} = <:-end
<:-refl {T = T-Msg ⊙ T T₁} = <:-msg <<:-refl <:-refl
<:-refl {T = T-Up T} = <:-up <:-refl
<:-refl {T = T-Minus T} = <:-minus <:-refl
<:-refl {T = T-ProtoD T} = <:-protoD <:-refl
<:-refl {T = T-ProtoP #c v T} = <:-proto ⊆-refl <<:-refl

<:-refl-dual {T = T-Var x} = <:-dual-var
<:-refl-dual {T = T-Arrow (≤p-step ()) T T₁}
<:-refl-dual {T = T-Sub (≤k-step ≤p-refl x₁) T} = <:-trans <:-sub-dual-l (<:-trans (<:-sub (≤k-step ≤p-refl x₁) <:-refl-dual) <:-sub-dual-r)
<:-refl-dual {T = T-Dual D-S T} = <:-trans (<:-dual-dual-l-new D-S) (<:-trans <:-refl (<:-dual-dual-r-new D-S))
<:-refl-dual {T = T-End} = <:-trans <:-dual-end-l <:-dual-end-r
<:-refl-dual {T = T-Msg p T S} = <:-trans (<:-dual-msg-r-new {p₂ = invert p} (sym invert-involution)) (<:-trans (<:-msg <<:-refl <:-refl-dual) (<:-dual-msg-l-new (sym invert-involution)))

<<:-refl {⊙ = ⊕} = <:-refl
<<:-refl {⊙ = ⊝} = <:-refl
<<:-refl {⊙ = ⊘} = ≡c-refl

<:-refl-subst : T₁ ≡ T₂ → T₁ <: T₂
<:-refl-subst refl = <:-refl

<<:-trans : ∀ {T₁ T₂ T₃ : Ty Δ K} {⊙} → T₁ <<:[ ⊙ ] T₂ → T₂ <<:[ ⊙ ] T₃ → T₁ <<:[ ⊙ ] T₃
<<:-trans {⊙ = ⊕} T₁<<:T₂ T₂<<:T₃ = <:-trans T₁<<:T₂ T₂<<:T₃
<<:-trans {⊙ = ⊝} T₁<<:T₂ T₂<<:T₃ = <:-trans T₂<<:T₃ T₁<<:T₂
<<:-trans {⊙ = ⊘} T₁<<:T₂ T₂<<:T₃ = ≡c-trns T₁<<:T₂ T₂<<:T₃

invert-minus-<<: : T₁ <<:[ injᵥ (invert p) ] T₂ → T-Minus T₁ <<:[ injᵥ p ] T-Minus T₂
invert-minus-<<: {p = ⊕} T₁<<:T₂ = <:-minus T₁<<:T₂
invert-minus-<<: {p = ⊝} T₁<<:T₂ = <:-minus T₁<<:T₂

minus-minus-<<: : T <<:[ injᵥ p ] T-Minus (T-Minus T)
minus-minus-<<: {p = ⊕} = <:-minus-minus-l <:-refl
minus-minus-<<: {p = ⊝} = <:-minus-minus-r <:-refl

-- former rules, now derivable

<:-dual-msg-l-derivable :
  T-Msg (invert p) T (T-Dual D-S S) <: T₂ →
  ----------------------------------------
  T-Dual D-S (T-Msg p T S) <: T₂

<:-dual-msg-l-derivable (<:-trans T₁<:T₂ T₂<:T₃) = <:-trans (<:-dual-msg-l-derivable T₁<:T₂) T₂<:T₃
<:-dual-msg-l-derivable {p} (<:-msg-minus refl)
  rewrite invert-involution {p}
  = <:-trans (<:-dual-msg-r-new (sym invert-involution)) (<:-trans (<:-msg-minus {p₂ = invert (invert p)} refl) (<:-refl-subst (cong (λ p → T-Msg p _ _) invert-involution)))
<:-dual-msg-l-derivable (<:-minus-msg refl) = <:-trans (<:-dual-msg-r-new (sym invert-involution)) (<:-trans (<:-msg <<:-refl <:-refl) (<:-minus-msg refl))
<:-dual-msg-l-derivable (<:-dual-dual-r-new D-S) = <:-trans (<:-dual-msg-r-new (sym invert-involution)) (<:-trans <:-refl (<:-dual-dual-r-new D-S))
-- <:-dual-msg-l-derivable (<:-dual-msg-r T₁<:T₂) = <:-trans (<:-dual-msg-r-new (sym invert-involution)) (<:-trans T₁<:T₂ (<:-dual-msg-l-new (sym invert-involution)))
<:-dual-msg-l-derivable {p} (<:-dual-msg-l-new refl) = <:-trans (<:-dual-msg-r-new {p₂ = invert p} (sym invert-involution)) (<:-trans <:-refl (<:-dual-msg-l-new refl))
<:-dual-msg-l-derivable {p} (<:-msg T₁<<:T₂ S₁<:S₂) = <:-trans (<:-dual-msg-r-new {p₁ = p} (sym invert-involution)) (<:-msg T₁<<:T₂ S₁<:S₂)

<:-dual-msg-r-derivable :
  T₁ <: T-Msg (invert p) T (T-Dual D-S S) →
  ----------------------------------------
  T₁ <: T-Dual D-S (T-Msg p T S)

<:-dual-msg-r-derivable {p = p} (<:-trans T₁<:T₂ T₂<:T₃) = <:-trans T₁<:T₂ (<:-dual-msg-r-derivable T₂<:T₃)
<:-dual-msg-r-derivable {p = p} (<:-msg-minus eq) = <:-trans (<:-msg-minus {p₂ = invert p} eq) (<:-dual-msg-l-new (sym invert-involution))
<:-dual-msg-r-derivable {p = p} (<:-minus-msg eq) = <:-trans (<:-minus-msg eq) (<:-dual-msg-l-new{p₁ = invert p} (sym invert-involution))
<:-dual-msg-r-derivable {p = p} (<:-dual-dual-l-new D-S) = <:-trans (<:-dual-dual-l-new D-S) (<:-dual-msg-l-new (sym invert-involution))
-- <:-dual-msg-r-derivable {p = p} (<:-dual-msg-l T₁<:T₂) = <:-trans (<:-dual-msg-r-new (sym invert-involution)) (<:-trans T₁<:T₂ (<:-dual-msg-l-new (sym invert-involution)))
<:-dual-msg-r-derivable {p = p} (<:-dual-msg-r-new refl) = <:-trans (<:-dual-msg-r-new {p₂ = invert p} refl) (<:-trans <:-refl (<:-dual-msg-l-new (sym invert-involution)))
<:-dual-msg-r-derivable {p = p} (<:-msg T₁<<:T₂ S₁<:S₂) = <:-trans (<:-msg T₁<<:T₂ S₁<:S₂) (<:-dual-msg-l-new (sym invert-involution))


<:-neg-l :
  T-Msg (invert p) T S <: S′ →
  ------------------------------
  T-Msg p (T-Minus T) S <: S′

<:-neg-l (<:-trans S₁<:S₂ S₂<:S₃) = <:-trans (<:-neg-l S₁<:S₂) S₂<:S₃
-- <:-neg-l (<:-neg-l S₁<:S₂) = <:-trans (<:-msg-minus refl) (<:-trans (<:-msg-minus refl) S₁<:S₂)
-- <:-neg-l (<:-neg-r S₁<:S₂) = <:-trans (<:-msg-minus refl) (<:-trans S₁<:S₂ (<:-minus-msg (sym invert-involution)))
<:-neg-l (<:-msg-minus refl) = <:-trans (<:-msg-minus refl) (<:-msg-minus refl)
<:-neg-l {p} (<:-minus-msg refl) rewrite invert-involution {p} = <:-refl
-- <:-neg-l (<:-dual-dual-r D-S S₁<:S₂) = <:-dual-dual-r D-S (<:-neg-l S₁<:S₂)
-- <:-neg-l (<:-dual-msg-r S₁<:S₂) = <:-dual-msg-r (<:-neg-l S₁<:S₂)
<:-neg-l (<:-msg T₁<<:T₂ S₁<:S₂) = <:-trans (<:-msg-minus refl) (<:-msg T₁<<:T₂ S₁<:S₂)
<:-neg-l (<:-dual-dual-r-new D-S) = <:-trans (<:-msg-minus refl) (<:-dual-dual-r-new D-S)
<:-neg-l (<:-dual-msg-l-new refl) = <:-trans (<:-msg-minus refl) (<:-dual-msg-l-new refl)

<:-neg-r :
  S′ <: T-Msg (invert p) T S →
  ------------------------------
  S′ <: T-Msg p (T-Minus T) S

<:-neg-r (<:-trans S₁<:S₂ S₁<:S₃) = <:-trans S₁<:S₂ (<:-neg-r S₁<:S₃)
-- <:-neg-r (<:-neg-l S₁<:S₂) = <:-neg-l (<:-neg-r S₁<:S₂)
-- <:-neg-r (<:-neg-r S₁<:S₂) = <:-neg-r (<:-neg-r S₁<:S₂)
<:-neg-r {p = p} (<:-msg-minus {p₁ = p₁} x) rewrite invert-injective x = <:-refl
<:-neg-r {p = p} (<:-minus-msg {p₂ = p₂} x) rewrite invert-injective x = <:-msg minus-minus-<<: <:-refl
-- <:-neg-r (<:-dual-dual-l d S₁<:S₂) = <:-dual-dual-l d (<:-neg-r S₁<:S₂)
-- <:-neg-r (<:-dual-msg-l S₁<:S₂) = <:-dual-msg-l (<:-neg-r S₁<:S₂)
<:-neg-r {p = p} {T = T} {S = S} (<:-msg {T₁} {S₁ = S₁} T₁<<:T₂ S₁<:S₂) = <:-trans (<:-minus-msg refl) (S₁<:S₂′ p T₁<<:T₂)
  where S₁<:S₂′ : ∀ p → (T₁<<:T₂ : T₁ <<:[ injᵥ (invert p) ] T) → T-Msg (invert (invert p)) (T-Minus T₁) S₁ <: T-Msg p (T-Minus T) S
        S₁<:S₂′ p T₁<<:T₂ rewrite invert-involution {p} = <:-msg (invert-minus-<<: T₁<<:T₂) S₁<:S₂
<:-neg-r (<:-dual-dual-l-new D-S) = <:-trans (<:-dual-dual-l-new D-S) (<:-minus-msg (sym invert-involution))
<:-neg-r (<:-dual-msg-r-new refl) = <:-trans (<:-dual-msg-r-new refl) (<:-minus-msg (sym invert-involution))

<:-dual-dual-l-derivable :
  (d : Dualizable K) →
  T₁ <: T₂ →
  ------------------------------
  T-Dual d (T-Dual d T₁) <: T₂

<:-dual-dual-l-derivable D-S (<:-trans T₁<:T₂ T₁<:T₃) = <:-trans (<:-dual-dual-l-derivable D-S T₁<:T₂) T₁<:T₃
<:-dual-dual-l-derivable D-S (<:-sub K≤K′ T₁<:T₂) = <:-trans (<:-dual-dual-l-new D-S) (<:-sub K≤K′ T₁<:T₂)
<:-dual-dual-l-derivable D-S <:-sub-dual-l = <:-trans (<:-dual-dual-l-new D-S) <:-sub-dual-l
<:-dual-dual-l-derivable D-S <:-sub-dual-r = <:-trans (<:-dual-dual-l-new D-S) <:-sub-dual-r
<:-dual-dual-l-derivable D-S <:-var = <:-dual-dual-l-new D-S
<:-dual-dual-l-derivable D-S <:-dual-var = <:-dual-dual-l-new D-S
<:-dual-dual-l-derivable D-S (<:-fun T₁<:T₂ T₁<:T₃) = <:-trans (<:-dual-dual-l-new D-S) (<:-fun T₁<:T₂ T₁<:T₃)
<:-dual-dual-l-derivable D-S (<:-msg-minus x) = <:-trans (<:-dual-dual-l-new D-S) (<:-msg-minus x)
<:-dual-dual-l-derivable D-S (<:-minus-msg x) = <:-trans (<:-dual-dual-l-new D-S) (<:-minus-msg x)
<:-dual-dual-l-derivable D-S (<:-dual-dual-l-new d) = <:-trans (<:-dual-dual-l-new D-S) (<:-dual-dual-l-new d)
<:-dual-dual-l-derivable D-S (<:-dual-dual-r-new d) = <:-trans (<:-dual-dual-l-new D-S) (<:-dual-dual-r-new d)
-- <:-dual-dual-l-derivable D-S (<:-dual-msg-l T₁<:T₂) = <:-trans (<:-dual-dual-l-new D-S) (<:-dual-msg-l T₁<:T₂)
-- <:-dual-dual-l-derivable D-S (<:-dual-msg-r T₁<:T₂) = <:-dual-msg-r (<:-dual-dual-l-derivable D-S T₁<:T₂)
<:-dual-dual-l-derivable D-S <:-dual-end-l = <:-trans (<:-dual-dual-l-new D-S) <:-dual-end-l
<:-dual-dual-l-derivable D-S <:-dual-end-r = <:-trans (<:-dual-dual-l-new D-S) <:-dual-end-r
<:-dual-dual-l-derivable D-S (<:-msg x T₁<:T₂) = <:-trans (<:-dual-dual-l-new D-S) (<:-msg x T₁<:T₂)
<:-dual-dual-l-derivable D-S <:-end = <:-dual-dual-l-new D-S
<:-dual-dual-l-derivable D-S (<:-dual-msg-l-new refl) = <:-trans (<:-dual-dual-l-new D-S) (<:-dual-msg-l-new refl)
<:-dual-dual-l-derivable D-S (<:-dual-msg-r-new refl) = <:-trans (<:-dual-dual-l-new D-S) (<:-dual-msg-r-new refl)

<:-dual-dual-r-derivable :
  (d : Dualizable K) →
  T₁ <: T₂ →
  ------------------------------
  T₁ <: T-Dual d (T-Dual d T₂)

<:-dual-dual-r-derivable D-S (<:-trans T₁<:T₂ T₁<:T₃) = <:-trans T₁<:T₂ (<:-dual-dual-r-derivable D-S T₁<:T₃)
<:-dual-dual-r-derivable D-S (<:-sub K≤K′ T₁<:T₂) = <:-trans (<:-sub K≤K′ T₁<:T₂) (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S <:-sub-dual-l = <:-trans <:-sub-dual-l (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S <:-sub-dual-r = <:-trans <:-sub-dual-r (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S <:-var = <:-dual-dual-r-new D-S
<:-dual-dual-r-derivable D-S <:-dual-var = <:-dual-dual-r-new D-S
<:-dual-dual-r-derivable D-S (<:-fun T₁<:T₂ T₁<:T₃) = <:-trans (<:-fun T₁<:T₂ T₁<:T₃) (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S (<:-msg-minus x) = <:-trans (<:-msg-minus x) (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S (<:-minus-msg x) = <:-trans (<:-minus-msg x) (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S (<:-dual-dual-l-new d) = <:-trans (<:-dual-dual-l-new d) (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S (<:-dual-dual-r-new d) = <:-trans (<:-dual-dual-r-new d) (<:-dual-dual-r-new D-S)
-- <:-dual-dual-r-derivable D-S (<:-dual-msg-l T₁<:T₂) = <:-dual-msg-l (<:-dual-dual-r-derivable D-S T₁<:T₂)
-- <:-dual-dual-r-derivable D-S (<:-dual-msg-r T₁<:T₂) = <:-trans (<:-dual-msg-r T₁<:T₂) (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S <:-dual-end-l = <:-trans <:-dual-end-l (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S <:-dual-end-r = <:-trans <:-dual-end-r (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S (<:-msg x T₁<:T₂) = <:-trans (<:-msg x T₁<:T₂) (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S <:-end = <:-dual-dual-r-new D-S
<:-dual-dual-r-derivable D-S (<:-dual-msg-l-new refl) = <:-trans (<:-dual-msg-l-new refl) (<:-dual-dual-r-new D-S)
<:-dual-dual-r-derivable D-S (<:-dual-msg-r-new refl) = <:-trans (<:-dual-msg-r-new refl) (<:-dual-dual-r-new D-S)

-- auxiliary lemmas / properties

t-dual-<: : {T₁ : Ty Δ K} → (dk : Dualizable K) → t-dual dk T₁ <: T-Dual dk T₁
t-dual-<: {T₁ = T-Var x} D-S = <:-refl
t-dual-<: {T₁ = T-Arrow (≤p-step ()) T₁ T₂} D-S
t-dual-<: {T₁ = T-Sub K≤K′@(≤k-step ≤p-refl x₁) T₁} D-S = <:-trans (<:-sub K≤K′ (t-dual-<: D-S)) (<:-sub-dual-r {T = T₁}{K≤K′ = K≤K′})
t-dual-<: {T₁ = T-Dual D-S T₁} D-S = <:-dual-dual-r-new D-S
t-dual-<: {T₁ = T-End} D-S = <:-dual-end-r
t-dual-<: {T₁ = T-Msg p T₁ T₂} D-S = <:-dual-msg-r-derivable (<:-msg <<:-refl (t-dual-<: {T₁ = T₂} D-S))

t-dual-:> : {T₁ : Ty Δ K} → (dk : Dualizable K) → T-Dual dk T₁ <: t-dual dk T₁
t-dual-:> {T₁ = T-Var x} D-S = <:-refl
t-dual-:> {T₁ = T-Arrow (≤p-step ()) T₁ T₂} D-S
t-dual-:> {T₁ = T-Sub K≤K′@(≤k-step ≤p-refl x₁) T₁} D-S = <:-trans <:-sub-dual-l (<:-sub K≤K′ (t-dual-:> D-S))
t-dual-:> {T₁ = T-Dual D-S T₁} D-S = <:-dual-dual-l-new D-S
t-dual-:> {T₁ = T-End} D-S = <:-dual-end-l
t-dual-:> {T₁ = T-Msg p T₁ T₂} D-S = <:-dual-msg-l-derivable (<:-msg <<:-refl (t-dual-:> D-S))


dual-<: : {T₁ T₂ : Ty Δ K} → (dk : Dualizable K) → T₁ <: T₂ → t-dual dk T₂ <: t-dual dk T₁
-- dual-<: df <:-refl = <:-refl
dual-<: df (<:-trans T₁<:T₂ T₂<:T₃) = <:-trans (dual-<: df T₂<:T₃) (dual-<: df T₁<:T₂)
dual-<: D-S (<:-sub (≤k-step ≤p-refl x₁) T₁<:T₂) = <:-sub (≤k-step ≤p-refl x₁) (dual-<: D-S T₁<:T₂)
dual-<: D-S (<:-sub-dual-l {K≤K′ = ≤k-step ≤p-refl x₁}) = <:-sub (≤k-step ≤p-refl x₁) <:-refl
dual-<: D-S (<:-sub-dual-r {K≤K′ = ≤k-step ≤p-refl x₁}) = <:-refl
dual-<: D-S (<:-var) = <:-dual-var
dual-<: D-S (<:-dual-var) = <:-var
dual-<: D-S (<:-end) = <:-end
dual-<: D-S (<:-fun {≤pk = ≤p-step ()} T₁<:T₂ T₁<:T₃)
-- dual-<: D-S (<:-neg-l T₁<:T₂) = <:-trans (dual-<: D-S T₁<:T₂) (<:-neg-r <:-refl)
-- dual-<: D-S (<:-neg-r T₁<:T₂) = <:-trans (<:-neg-l <:-refl) (dual-<: D-S T₁<:T₂)
dual-<: D-S (<:-msg-minus refl) = <:-minus-msg (cong invert (sym invert-involution))
dual-<: D-S (<:-minus-msg refl) = <:-msg-minus (cong invert (sym invert-involution))
-- dual-<: D-S (<:-dual-lr d T₁<:T₂) = T₁<:T₂
-- dual-<: D-S (<:-dual-dual-l D-S T₁<:T₂) = <:-trans (dual-<: D-S T₁<:T₂) (t-dual-<: D-S)
-- dual-<: D-S (<:-dual-dual-r D-S T₁<:T₂) = <:-trans (t-dual-:> D-S) (dual-<: D-S T₁<:T₂)
-- dual-<: D-S (<:-dual-msg-l {p} T₁<:T₂) with dual-<: D-S T₁<:T₂
-- ... | ih rewrite invert-involution{p} = ih
-- dual-<: D-S (<:-dual-msg-r {p = p} T₁<:T₂) with dual-<: D-S T₁<:T₂
-- ... | ih rewrite invert-involution{p} = ih
dual-<: D-S <:-dual-end-l = <:-refl
dual-<: D-S <:-dual-end-r = <:-refl
dual-<: D-S (<:-msg {p = ⊕} T₁<<:[p]T₂ S₁<:S₂) = <:-msg T₁<<:[p]T₂ (dual-<: D-S S₁<:S₂)
dual-<: D-S (<:-msg {p = ⊝} T₁<<:[p]T₂ S₁<:S₂) = <:-msg T₁<<:[p]T₂ (dual-<: D-S S₁<:S₂)
dual-<: D-S (<:-dual-dual-l-new D-S) = t-dual-<: D-S
dual-<: D-S (<:-dual-dual-r-new D-S) = t-dual-:> D-S
dual-<: D-S (<:-dual-msg-l-new refl) = <:-refl
dual-<: D-S (<:-dual-msg-r-new refl) = <:-refl


-- convertibility implies subtyping


conv⇒subty : (T₁ T₂ : Ty Δ K) → T₁ ≡c T₂ → T₁ <: T₂ × T₂ <: T₁
conv⇒subty T₁ T₂ ≡c-refl = <:-refl , <:-refl
conv⇒subty T₁ T₂ (≡c-symm T₂≡T₁) = swap (conv⇒subty T₂ T₁ T₂≡T₁)
conv⇒subty T₁ T₃ (≡c-trns {T₂ = T₂} T₁≡T₂ T₂≡T₃)
  with conv⇒subty _ _ T₁≡T₂ | conv⇒subty _ _ T₂≡T₃
... | T₁<:T₂ , T₂<:T₁ | T₂<:T₃ , T₃<:T₂ = (<:-trans T₁<:T₂ T₂<:T₃) , (<:-trans T₃<:T₂ T₂<:T₁)
conv⇒subty T₁ T₂ (≡c-sub K≤K′ T₁≡T₂)
  using T₁<:T₂ , T₂<:T₁ ← conv⇒subty _ _ T₁≡T₂ = <:-sub K≤K′ T₁<:T₂ , <:-sub K≤K′ T₂<:T₁
conv⇒subty T₁ T₂ ≡c-sub-dual = <:-sub-dual-l , <:-sub-dual-r
conv⇒subty T₁ T₂ (≡c-dual-dual d) = (<:-dual-dual-l-new d) , (<:-dual-dual-r-new d)
conv⇒subty T₁ T₂ ≡c-dual-end = <:-dual-end-l , <:-dual-end-r
conv⇒subty T₁ T₂ ≡c-dual-msg = <:-dual-msg-l-derivable <:-refl , <:-dual-msg-r-derivable <:-refl
conv⇒subty T₁ T₂ ≡c-msg-minus = <:-neg-l <:-refl , <:-neg-r <:-refl
conv⇒subty T₁ T₂ ≡c-minus-p = <:-minus-minus-l <:-refl , <:-minus-minus-r <:-refl
conv⇒subty _ _ (≡c-fun T₁≡T₂ T₃≡T₄)
  using T₁<:T₂ , T₂<:T₁ ← conv⇒subty _ _ T₁≡T₂
  using T₃<:T₄ , T₄<:T₃ ← conv⇒subty _ _ T₃≡T₄
  = (<:-fun T₂<:T₁ T₃<:T₄) , <:-fun T₁<:T₂ T₄<:T₃
conv⇒subty T₁ T₂ (≡c-all T₁≡T₂)
  using T₁<:T₂ , T₂<:T₁ ← conv⇒subty _ _ T₁≡T₂
  = <:-all T₁<:T₂ , <:-all T₂<:T₁
conv⇒subty _ _ (≡c-msg {p = ⊕} T₁≡T₂ T₃≡T₄)
  using T₁<:T₂ , T₂<:T₁ <- conv⇒subty _ _ T₁≡T₂
  using T₃<:T₄ , T₄<:T₃ <- conv⇒subty _ _ T₃≡T₄ = <:-msg T₂<:T₁ T₃<:T₄ , <:-msg T₁<:T₂ T₄<:T₃
conv⇒subty _ _ (≡c-msg {p = ⊝} T₁≡T₂ T₃≡T₄)
  using T₁<:T₂ , T₂<:T₁ <- conv⇒subty _ _ T₁≡T₂
  using T₃<:T₄ , T₄<:T₃ <- conv⇒subty _ _ T₃≡T₄ = <:-msg T₁<:T₂ T₃<:T₄ , <:-msg T₂<:T₁ T₄<:T₃
conv⇒subty T₁ T₂ (≡c-protoD T₁≡T₂)
  using T₁<:T₂ , T₂<:T₁ ← conv⇒subty _ _ T₁≡T₂
  = <:-protoD T₁<:T₂ , <:-protoD T₂<:T₁
conv⇒subty T₁ T₂ (≡c-protoP {⊙ = ⊕} T₁≡T₂)
  using T₁<:T₂ , T₂<:T₁ <- conv⇒subty _ _ T₁≡T₂ = <:-proto ⊆-refl T₁<:T₂ , <:-proto ⊆-refl T₂<:T₁
conv⇒subty T₁ T₂ (≡c-protoP {⊙ = ⊝} T₁≡T₂)
  using T₁<:T₂ , T₂<:T₁ <- conv⇒subty _ _ T₁≡T₂ = <:-proto ⊆-refl T₂<:T₁ , <:-proto ⊆-refl T₁<:T₂
conv⇒subty T₁ T₂ (≡c-protoP {⊙ = ⊘} T₁≡T₂)
  using T₁<:T₂ , T₂<:T₁ <- conv⇒subty _ _ T₁≡T₂ = <:-proto ⊆-refl T₁≡T₂ , <:-proto ⊆-refl (≡c-symm T₁≡T₂)
conv⇒subty T₁ T₂ (≡c-up T₁≡T₂)
  using T₁<:T₂ , T₂<:T₁ ← conv⇒subty _ _ T₁≡T₂
  = <:-up T₁<:T₂ , <:-up T₂<:T₁
conv⇒subty T₁ T₂ (≡c-minus T₁≡T₂)
  using T₁<:T₂ , T₂<:T₁ ← conv⇒subty _ _ T₁≡T₂
  = <:-minus T₂<:T₁ , <:-minus T₁<:T₂

-- subtyping is compatible with normalization
-- i.e., normalization preserves subtyping

norm-pres-sub : ∀ {p} {d? : (p ≡ ⊝ → Dualizable K)} → T₁ <: T₂ → nf p d? T₂ <<:[ injᵥ p ] nf p d? T₁
norm-pres-sub {T₁ = T₁} {T₂} {p = ⊕} {d? = d?} T₁<:T₂
  with conv⇒subty _ _ (nf-sound+ {f = d?} T₁) | conv⇒subty _ _ (nf-sound+ {f = d?} T₂)
... | nT₁<:T₁ , T₁<:nT₁ | nT₂<:T₂ , T₂<:nT₂ = <:-trans (<:-trans nT₁<:T₁ T₁<:T₂) T₂<:nT₂
norm-pres-sub {T₁ = T₁} {T₂} {p = ⊝} {d?} T₁<:T₂
  with D-S ← d? refl
  with conv⇒subty _ _ (nf-sound- {f = d?} T₁) | conv⇒subty _ _ (nf-sound- {f = d?} T₂)
... | nT₁<:T₁ , T₁<:nT₁ | nT₂<:T₂ , T₂<:nT₁ = <:-trans nT₂<:T₂ (<:-trans (dual-<: D-S T₁<:T₂) T₁<:nT₁)

-- further derivable rules for _<:_

<:-dual-lr :  {T₁ T₂ : Ty Δ K} (d : Dualizable K) → T₂ <: T₁ → T-Dual d T₁ <: T-Dual d T₂
-- <:-dual-lr d <:-refl = <:-refl
<:-dual-lr D-S <:-var = <:-dual-var
<:-dual-lr D-S <:-dual-var = <:-trans (<:-dual-dual-l-new D-S) (<:-dual-dual-r-new D-S)
<:-dual-lr D-S <:-end = <:-trans <:-dual-end-l <:-dual-end-r
<:-dual-lr D-S (<:-trans T₃<:T₂ T₂<:T₁) = <:-trans (<:-dual-lr D-S T₂<:T₁) (<:-dual-lr D-S T₃<:T₂)
<:-dual-lr {K = KV KS m} D-S (<:-sub (≤k-step ≤p-refl x₁) T₂<:T₁) = <:-trans <:-sub-dual-l (<:-trans (<:-sub (≤k-step ≤p-refl x₁) (<:-dual-lr D-S T₂<:T₁)) <:-sub-dual-r)
<:-dual-lr D-S (<:-sub-dual-l { K≤K′ = K≤K′ }) = <:-trans (<:-trans <:-sub-dual-l (<:-sub K≤K′ (<:-dual-dual-l-new D-S))) (<:-dual-dual-r-new D-S)
<:-dual-lr D-S (<:-sub-dual-r {K≤K′ = K≤K′}) = <:-trans
                                                 (<:-trans (<:-dual-dual-l-new D-S)
                                                  (<:-sub K≤K′ (<:-dual-dual-r-new D-S)))
                                                 <:-sub-dual-r
<:-dual-lr {K = KV KS m} D-S (<:-fun {≤pk = ≤p-step ()} T₂<:T₁ T₂<:T₂)
-- <:-dual-lr D-S (<:-neg-l T₂<:T₁) = <:-trans (<:-neg-r (<:-trans (<:-dual-lr D-S T₂<:T₁) (<:-dual-msg-l <:-refl))) (<:-dual-msg-r <:-refl)
-- <:-dual-lr D-S (<:-neg-r T₂<:T₁) = <:-trans (<:-dual-msg-l <:-refl) (<:-neg-l (<:-trans (<:-dual-msg-r <:-refl) (<:-dual-lr D-S T₂<:T₁)))
<:-dual-lr D-S (<:-msg-minus refl) = <:-dual-msg-l-derivable (<:-dual-msg-r-derivable (<:-minus-msg (cong invert (sym invert-involution))))
<:-dual-lr D-S (<:-minus-msg refl) = <:-dual-msg-l-derivable (<:-dual-msg-r-derivable (<:-msg-minus (cong invert (sym invert-involution))))
-- <:-dual-lr D-S (<:-dual-dual-l D-S T₂<:T₁) = <:-dual-dual-r D-S (<:-dual-lr D-S T₂<:T₁)
-- <:-dual-lr D-S (<:-dual-dual-r D-S T₂<:T₁) = <:-dual-dual-l D-S (<:-dual-lr D-S T₂<:T₁)
-- <:-dual-lr D-S (<:-dual-msg-l T₂<:T₁) = <:-trans (<:-dual-lr D-S T₂<:T₁) (<:-dual-msg-l (<:-trans (<:-trans (<:-refl-subst (cong (λ p → T-Msg p _ _) invert-involution)) (<:-msg <<:-refl (<:-dual-dual-l-new D-S))) (<:-dual-dual-r-new D-S)))
-- <:-dual-lr D-S (<:-dual-msg-r T₂<:T₁) = <:-trans (<:-trans (<:-dual-dual-l-new D-S) (<:-dual-msg-r (<:-trans (<:-msg <<:-refl (<:-dual-dual-r-new D-S)) (<:-refl-subst (cong (λ p → T-Msg p _ _) (sym invert-involution)))))) (<:-dual-lr D-S T₂<:T₁)
<:-dual-lr D-S <:-dual-end-l = <:-trans <:-dual-end-l (<:-dual-dual-r-new D-S)
<:-dual-lr D-S <:-dual-end-r = <:-trans (<:-dual-dual-l-new D-S) <:-dual-end-r
<:-dual-lr D-S (<:-msg {p = p} P₁<<:P₂ T₂<:T₁) = <:-trans (<:-dual-msg-l-derivable (<:-msg (subst id (invert-<<: p) P₁<<:P₂) (<:-dual-lr D-S T₂<:T₁))) (<:-dual-msg-r-derivable <:-refl)
<:-dual-lr D-S (<:-dual-dual-l-new D-S) = <:-dual-dual-r-new D-S
<:-dual-lr D-S (<:-dual-dual-r-new D-S) = <:-dual-dual-l-new D-S
<:-dual-lr {T₁ = T-Dual _ (T-Msg p T₁ T₂)} D-S (<:-dual-msg-l-new refl) = <:-trans (<:-dual-dual-l-new D-S) (<:-trans (<:-msg <<:-refl (<:-dual-dual-r-new D-S)) (<:-dual-msg-l-new (sym invert-involution)))
<:-dual-lr {T₁ = T-Msg p T₁ (T-Dual .D-S _)} D-S (<:-dual-msg-r-new refl) = <:-trans (<:-dual-msg-r-new (sym invert-involution)) (<:-trans (<:-msg <<:-refl (<:-dual-dual-l-new D-S)) (<:-dual-dual-r-new D-S))


-- properties


t-loop-sub : ∀ p → T₁ <: T₂ → t-loop p (nf ⊕ d?⊥ T₁) .proj₁ ≡ t-loop p (nf ⊕ d?⊥ T₂) .proj₁
t-loop-sub-minus : ∀ p → T₂ <: T₁ → t-loop p (t-minus (nf ⊕ d?⊥ T₁)) .proj₁ ≡ t-loop p (t-minus (nf ⊕ d?⊥ T₂)) .proj₁

-- t-loop-sub p <:-refl = refl
t-loop-sub p <:-var = refl
t-loop-sub p (<:-trans T₁<:T₂ T₂<:T₃) = trans (t-loop-sub p T₁<:T₂) (t-loop-sub p T₂<:T₃)
t-loop-sub p (<:-up T₁<:T₂) = refl
t-loop-sub p (<:-proto x x₁) = refl
t-loop-sub p (<:-minus T₂<:T₁) = t-loop-sub-minus p T₂<:T₁
t-loop-sub p (<:-minus-minus-l {T₁} T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = t-loop-sub p T₁<:T₂
t-loop-sub p (<:-minus-minus-r {T₂ = T₂} T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = t-loop-sub p T₁<:T₂

-- t-loop-sub-minus p <:-refl = refl
t-loop-sub-minus p <:-var = refl
t-loop-sub-minus p (<:-trans T₃<:T₂ T₂<:T₁) = trans (t-loop-sub-minus p T₂<:T₁) (t-loop-sub-minus p T₃<:T₂)
t-loop-sub-minus p (<:-up T₂<:T₁) = refl
t-loop-sub-minus p (<:-proto x x₁) = refl
t-loop-sub-minus p (<:-minus {T₂} {T₁} T₂<:T₁)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁) | t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = t-loop-sub p T₂<:T₁
t-loop-sub-minus p (<:-minus-minus-l {T₁} T₂<:T₁)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = t-loop-sub-minus p T₂<:T₁
t-loop-sub-minus p (<:-minus-minus-r {T₂ = T₂} T₂<:T₁)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = t-loop-sub-minus p T₂<:T₁

t-loop-sub-<<: : ∀ v p →  T₁ <<:[ injᵥ v ] T₂
  → t-loop p (nf ⊕ d?⊥ T₁) .proj₁ ≡ t-loop p (nf ⊕ d?⊥ T₂) .proj₁
t-loop-sub-<<: ⊕ p T₁<<:T₂ = sym (t-loop-sub p T₁<<:T₂)
t-loop-sub-<<: ⊝ p T₁<<:T₂ = t-loop-sub p T₁<<:T₂
