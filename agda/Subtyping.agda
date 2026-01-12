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

data _<:_ {Δ} where
  <:-refl  : T <: T
  <:-trans : T₁ <: T₂ → T₂ <: T₃ → T₁ <: T₃

  <:-sub  : (K≤K′ : KV pk m ≤k KV pk′ m′) → T₁ <: T₂ → T-Sub K≤K′ T₁ <: T-Sub K≤K′ T₂
  <:-sub-dual-l : {T : Ty Δ (KV KS m)} {K≤K′ : KV KS m ≤k KV KS m′}
    → T-Dual D-S (T-Sub K≤K′ T) <: T-Sub K≤K′ (T-Dual D-S T)
  <:-sub-dual-r : {T : Ty Δ (KV KS m)} {K≤K′ : KV KS m ≤k KV KS m′}
    → T-Sub K≤K′ (T-Dual D-S T) <: T-Dual D-S (T-Sub K≤K′ T)

  <:-fun : ∀ {pk : PreKind} {≤pk : KM ≤p pk} {m}
    → T₃ <: T₁ → T₂ <: T₄
    → T-Arrow {m = m} ≤pk T₁ T₂ <: T-Arrow ≤pk T₃ T₄
  <:-protoD : T₁ <: T₂ → T-ProtoD T₁ <: T-ProtoD T₂
  <:-all : {T₁ T₂ : Ty (K′ ∷ Δ) (KV KT m)} → T₁ <: T₂ → T-Poly T₁ <: T-Poly T₂

  <:-neg-l : T-Msg (invert p) T S <: S′ → T-Msg p (T-Minus T) S <: S′
  <:-neg-r : S′ <: T-Msg (invert p) T S → S′ <: T-Msg p (T-Minus T) S

  <:-dual-lr : {T₁ T₂ : Ty Δ K} (d : Dualizable K) → T₂ <: T₁ → T-Dual d T₁ <: T-Dual d T₂
  <:-dual-dual-l : (d : Dualizable K) → T₁ <: T₂ → T-Dual d (T-Dual d T₁) <: T₂
  <:-dual-dual-r : (d : Dualizable K) → T₁ <: T₂ → T₁ <: T-Dual d (T-Dual d T₂)
  <:-dual-msg-l : T-Msg (invert p) T (T-Dual D-S S) <: T₂ → T-Dual D-S (T-Msg p T S) <: T₂
  <:-dual-msg-r : T₁ <: T-Msg (invert p) T (T-Dual D-S S) → T₁ <: T-Dual D-S (T-Msg p T S)
  <:-dual-end-l  : T-Dual D-S T-End <: T-End
  <:-dual-end-r  : T-End <: T-Dual D-S T-End

  <:-msg : T₁ <<:[ injᵥ p ] T₂ → S₁ <: S₂ → T-Msg p T₁ S₁ <: T-Msg p T₂ S₂
  <:-up : T₁ <: T₂ → T-Up T₁ <: T-Up T₂

  -- protocol kinds
  
  <:-proto : ∀ {#c₁ #c₂ : Subset.Subset k}
    → #c₁ ⊆ #c₂ → T₁ <<:[ ⊙ ] T₂
    → T-ProtoP #c₁ ⊙ T₁ <: T-ProtoP #c₂ ⊙ T₂
  <:-minus : T₂ <: T₁ → T-Minus T₁ <: T-Minus T₂
  <:-minus-minus-l : T₁ <: T₂ → T-Minus (T-Minus T₁) <: T₂
  <:-minus-minus-r : T₁ <: T₂ → T₁ <: T-Minus (T-Minus T₂)

<<:-refl : ∀ {T : Ty Δ K} {⊙} → T <<:[ ⊙ ] T
<<:-refl {⊙ = ⊕} = <:-refl
<<:-refl {⊙ = ⊝} = <:-refl
<<:-refl {⊙ = ⊘} = ≡c-refl

t-dual-<: : {T₁ : Ty Δ K} → (dk : Dualizable K) → t-dual dk T₁ <: T-Dual dk T₁
t-dual-<: {T₁ = T-Var x} D-S = <:-refl
t-dual-<: {T₁ = T-Arrow (≤p-step ()) T₁ T₂} D-S
t-dual-<: {T₁ = T-Sub K≤K′@(≤k-step ≤p-refl x₁) T₁} D-S = <:-trans (<:-sub K≤K′ (t-dual-<: D-S)) (<:-sub-dual-r {T = T₁}{K≤K′ = K≤K′})
t-dual-<: {T₁ = T-Dual D-S T₁} D-S = <:-dual-dual-r D-S <:-refl
t-dual-<: {T₁ = T-End} D-S = <:-dual-end-r
t-dual-<: {T₁ = T-Msg p T₁ T₂} D-S = <:-dual-msg-r (<:-msg <<:-refl (t-dual-<: {T₁ = T₂} D-S))

t-dual-:> : {T₁ : Ty Δ K} → (dk : Dualizable K) → T-Dual dk T₁ <: t-dual dk T₁
t-dual-:> {T₁ = T-Var x} D-S = <:-refl
t-dual-:> {T₁ = T-Arrow (≤p-step ()) T₁ T₂} D-S
t-dual-:> {T₁ = T-Sub K≤K′@(≤k-step ≤p-refl x₁) T₁} D-S = <:-trans <:-sub-dual-l (<:-sub K≤K′ (t-dual-:> D-S))
t-dual-:> {T₁ = T-Dual D-S T₁} D-S = <:-dual-dual-l D-S <:-refl
t-dual-:> {T₁ = T-End} D-S = <:-dual-end-l
t-dual-:> {T₁ = T-Msg p T₁ T₂} D-S = <:-dual-msg-l (<:-msg <<:-refl (t-dual-:> D-S))


dual-<: : {T₁ T₂ : Ty Δ K} → (dk : Dualizable K) → T₁ <: T₂ → t-dual dk T₂ <: t-dual dk T₁
dual-<: df <:-refl = <:-refl
dual-<: df (<:-trans T₁<:T₂ T₂<:T₃) = <:-trans (dual-<: df T₂<:T₃) (dual-<: df T₁<:T₂)
dual-<: D-S (<:-sub (≤k-step ≤p-refl x₁) T₁<:T₂) = <:-sub (≤k-step ≤p-refl x₁) (dual-<: D-S T₁<:T₂)
dual-<: D-S (<:-sub-dual-l {K≤K′ = ≤k-step ≤p-refl x₁}) = <:-sub (≤k-step ≤p-refl x₁) <:-refl
dual-<: D-S (<:-sub-dual-r {K≤K′ = ≤k-step ≤p-refl x₁}) = <:-refl
dual-<: D-S (<:-fun {≤pk = ≤p-step ()} T₁<:T₂ T₁<:T₃)
dual-<: D-S (<:-neg-l T₁<:T₂) = <:-trans (dual-<: D-S T₁<:T₂) (<:-neg-r <:-refl)
dual-<: D-S (<:-neg-r T₁<:T₂) = <:-trans (<:-neg-l <:-refl) (dual-<: D-S T₁<:T₂)
dual-<: D-S (<:-dual-lr d T₁<:T₂) = T₁<:T₂
dual-<: D-S (<:-dual-dual-l D-S T₁<:T₂) = <:-trans (dual-<: D-S T₁<:T₂) (t-dual-<: D-S)
dual-<: D-S (<:-dual-dual-r D-S T₁<:T₂) = <:-trans (t-dual-:> D-S) (dual-<: D-S T₁<:T₂)
dual-<: D-S (<:-dual-msg-l {p} T₁<:T₂) with dual-<: D-S T₁<:T₂
... | ih rewrite invert-involution{p} = ih
dual-<: D-S (<:-dual-msg-r {p = p} T₁<:T₂) with dual-<: D-S T₁<:T₂
... | ih rewrite invert-involution{p} = ih
dual-<: D-S <:-dual-end-l = <:-refl
dual-<: D-S <:-dual-end-r = <:-refl
dual-<: D-S (<:-msg {p = ⊕} T₁<<:[p]T₂ S₁<:S₂) = <:-msg T₁<<:[p]T₂ (dual-<: D-S S₁<:S₂)
dual-<: D-S (<:-msg {p = ⊝} T₁<<:[p]T₂ S₁<:S₂) = <:-msg T₁<<:[p]T₂ (dual-<: D-S S₁<:S₂)

-- convertible implies subtyping


conv⇒subty : (T₁ T₂ : Ty Δ K) → T₁ ≡c T₂ → T₁ <: T₂ × T₂ <: T₁
conv⇒subty T₁ T₂ ≡c-refl = <:-refl , <:-refl
conv⇒subty T₁ T₂ (≡c-symm T₂≡T₁) = swap (conv⇒subty T₂ T₁ T₂≡T₁)
conv⇒subty T₁ T₃ (≡c-trns {T₂ = T₂} T₁≡T₂ T₂≡T₃)
  with conv⇒subty _ _ T₁≡T₂ | conv⇒subty _ _ T₂≡T₃
... | T₁<:T₂ , T₂<:T₁ | T₂<:T₃ , T₃<:T₂ = (<:-trans T₁<:T₂ T₂<:T₃) , (<:-trans T₃<:T₂ T₂<:T₁)
conv⇒subty T₁ T₂ (≡c-sub K≤K′ T₁≡T₂)
  using T₁<:T₂ , T₂<:T₁ ← conv⇒subty _ _ T₁≡T₂ = <:-sub K≤K′ T₁<:T₂ , <:-sub K≤K′ T₂<:T₁
conv⇒subty T₁ T₂ ≡c-sub-dual = <:-sub-dual-l , <:-sub-dual-r
conv⇒subty T₁ T₂ (≡c-dual-dual d) = <:-dual-dual-l d <:-refl , <:-dual-dual-r d <:-refl
conv⇒subty T₁ T₂ ≡c-dual-end = <:-dual-end-l , <:-dual-end-r
conv⇒subty T₁ T₂ ≡c-dual-msg = <:-dual-msg-l <:-refl , <:-dual-msg-r <:-refl
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

