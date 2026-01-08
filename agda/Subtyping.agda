
open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Nat
open import Data.Fin.Subset using (_⊆_)
open import Data.Fin.Subset.Properties using (⊆-refl)
open import Data.List
open import Data.Product
-- open import Data.Sum
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; inspect; Reveal_·_is_)


module Subtyping {k : ℕ}  where

-- 2025

open import Util
open import Kinds
open import Duality
open import Types

injᵥ : Polarity → Variance
injᵥ ⊕ = ⊝
injᵥ ⊝ = ⊕

-- subtyping

data _<:_ {Δ} : {K : Kind} → Rel (Ty {k} Δ K)

_<<:[_]_ : Ty {k} Δ K → Variance → Ty {k} Δ K → Set
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

  <:-fun : ∀ {pk : PreKind} {≤pk : KM ≤p pk} {m} →
           T₃ <: T₁ → T₂ <: T₄ → T-Arrow {m = m} ≤pk T₁ T₂ <: T-Arrow ≤pk T₃ T₄
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
  
  <:-proto : ∀ {#c₁ #c₂} → #c₁ ⊆ #c₂ → T₁ <<:[ ⊙ ] T₂ → T-ProtoP #c₁ ⊙ T₁ <: T-ProtoP #c₂ ⊙ T₂
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


conv⇒subty : (T₁ T₂ : Ty {k} Δ K) → T₁ ≡c T₂ → T₁ <: T₂ × T₂ <: T₁
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

-- algorithmic version of subtyping that only works on normal forms

module _ {k : ℕ} where

  data _<:ₚ_ : {P₁ P₂ : Ty{k} Δ KP} → NormalProto P₁ → NormalProto P₂ → Set

  _<<:ₚ[_]_ : {P₁ P₂ : Ty {k} Δ KP} → NormalProto P₁ → Variance → NormalProto P₂ → Set
  N₁ <<:ₚ[ ⊕ ] N₂ = N₁ <:ₚ N₂
  _<<:ₚ[_]_ {P₁ = P₁}{P₂} N₁ ⊘ N₂ = P₁ ≡ P₂
  N₁ <<:ₚ[ ⊝ ] N₂ = N₂ <:ₚ N₁

  data _<:ₜ_ : {T₁ T₂ : Ty{k} Δ (KV pk m)} → NormalTy T₁ → NormalTy T₂ → Set where

    <:ₜ-var : ∀ {T : Ty{k} Δ (KV pk m)} {nv : NormalVar T} → N-Var nv <:ₜ N-Var nv
    <:ₜ-base : N-Base{Δ = Δ} <:ₜ N-Base
    <:ₜ-arrow : ∀ {≤pk : KM ≤p pk} {m} {T₁ : Ty{k} Δ _}{U₁}{T₂}{U₂}
                 {M₁ : NormalTy T₁}{N₁ : NormalTy U₁}{M₂ : NormalTy T₂}{N₂ : NormalTy U₂}
          → M₂ <:ₜ M₁ → N₁ <:ₜ N₂ → _<:ₜ_ (N-Arrow{km = ≤pk}{m} M₁ N₁) (N-Arrow{km = ≤pk}{m} M₂ N₂)
    <:ₜ-poly : ∀ {m}{K′}{T₁ T₂ : Ty{k} (K′ ∷ Δ) (KV KT m)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂}
          → N₁ <:ₜ N₂ → N-Poly N₁ <:ₜ N-Poly N₂
    <:ₜ-sub : ∀ {km≤ : KV pk m ≤k KV pk′ m′}{T₁ T₂ : Ty{k} Δ (KV pk m)}{N₁ : NormalTy T₁}{N₂ : NormalTy T₂} → N₁ <:ₜ N₂ → N-Sub{km≤ = km≤} N₁ <:ₜ N-Sub{km≤ = km≤} N₂
    <:ₜ-end : N-End{Δ = Δ} <:ₜ N-End
    <:ₜ-msg : ∀ {p} {P₁ P₂ : Ty{k} Δ KP}{S₁ S₂ : Ty{k} Δ (KV KS Lin)}
            {NP₁ : NormalProto P₁}{NP₂ : NormalProto P₂}{NS₁ : NormalTy S₁} {NS₂ : NormalTy S₂}
            → NP₁ <<:ₚ[ injᵥ p ] NP₂ → NS₁ <:ₜ NS₂ → N-Msg p NP₁ NS₁ <:ₜ N-Msg p NP₂ NS₂
    <:ₜ-data : ∀ {T₁ T₂ : Ty{k} Δ (KV KT Lin)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂}
      → N₁ <:ₜ N₂ → N-ProtoD N₁ <:ₜ N-ProtoD N₂

  data _<:ₚ′_ : {P₁ P₂ : Ty{k} Δ KP} → NormalProto′ P₁ → NormalProto′ P₂ → Set where

    <:ₚ′-proto : ∀ {#c₁ #c₂}{P₁ P₂ : Ty{k} Δ KP} {N₁ : NormalProto P₁}{N₂ : NormalProto P₂}
      → #c₁ ⊆ #c₂
      → N₁ <<:ₚ[ ⊙ ] N₂
      → N-ProtoP{#c = #c₁}{⊙ = ⊙} N₁ <:ₚ′ N-ProtoP{#c = #c₂}{⊙ = ⊙} N₂
    <:ₚ′-up : ∀ {T₁ T₂ : Ty{k} Δ (KV pk m)}{N₁ : NormalTy T₁}{N₂ : NormalTy T₂}
      → N₁ <:ₜ N₂
      → N-Up N₁ <:ₚ′ N-Up N₂
    <:ₚ′-var : ∀ {x : KP ∈ Δ} → N-Var{x = x} <:ₚ′ N-Var{x = x}

  data _<:ₚ_ where

    <:ₚ-plus : {P₁ P₂ : Ty{k} Δ KP} → {N₁ : NormalProto′ P₁}{N₂ : NormalProto′ P₂}
      → N₁ <:ₚ′ N₂ → N-Normal N₁ <:ₚ N-Normal N₂
    <:ₚ-minus : {P₁ P₂ : Ty{k} Δ KP} → {N₁ : NormalProto′ P₁}{N₂ : NormalProto′ P₂}
      → N₂ <:ₚ′ N₁ → N-Minus N₁ <:ₚ N-Minus N₂

-- algorithmic typing is sound

sound-algₜ : ∀ {T₁ T₂ : Ty{k} Δ (KV pk m)} {N₁ : NormalTy T₁}{N₂ : NormalTy T₂}
  → N₁ <:ₜ N₂ → T₁ <: T₂

sound-<<:ₚ : ∀ {T₁ T₂ : Ty{k} Δ KP} {N₁ : NormalProto T₁}{N₂ : NormalProto T₂}
  → N₁ <<:ₚ[ ⊙ ] N₂ → T₁ <<:[ ⊙ ] T₂

sound-algₚ′ : ∀ {T₁ T₂ : Ty{k} Δ KP} {N₁ : NormalProto′ T₁}{N₂ : NormalProto′ T₂}
  → N₁ <:ₚ′ N₂ → T₁ <: T₂
sound-algₚ′ (<:ₚ′-proto #c₁⊆#c₂ N₁<:N₂) = <:-proto #c₁⊆#c₂ (sound-<<:ₚ N₁<:N₂)
sound-algₚ′ (<:ₚ′-up N₁<:ₜN₂) = <:-up (sound-algₜ N₁<:ₜN₂)
sound-algₚ′ <:ₚ′-var = <:-refl

sound-algₚ : ∀ {T₁ T₂ : Ty{k} Δ KP} {N₁ : NormalProto T₁}{N₂ : NormalProto T₂}
  → N₁ <:ₚ N₂ → T₁ <: T₂
sound-algₚ (<:ₚ-plus N₁<:N₂) = sound-algₚ′ N₁<:N₂
sound-algₚ (<:ₚ-minus N₂<:N₁) = <:-minus (sound-algₚ′ N₂<:N₁)

sound-<<:ₚ {⊙ = ⊕} N₁<<:N₂ = sound-algₚ N₁<<:N₂
sound-<<:ₚ {⊙ = ⊝} N₁<<:N₂ = sound-algₚ N₁<<:N₂
sound-<<:ₚ {⊙ = ⊘} refl = ≡c-refl

sound-algₜ <:ₜ-var = <:-refl
sound-algₜ <:ₜ-base = <:-refl
sound-algₜ (<:ₜ-arrow M₂<:ₜM₁ N₁<:ₜN₂) = <:-fun (sound-algₜ M₂<:ₜM₁) (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-poly N₁<:ₜN₂) = <:-all (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-sub {km≤ = km≤} N₁<:ₜN₂) = <:-sub km≤ (sound-algₜ N₁<:ₜN₂)
sound-algₜ <:ₜ-end = <:-refl
sound-algₜ (<:ₜ-msg {p = p} P₁<<P₂ N₁<:ₜN₂) = <:-msg (sound-<<:ₚ P₁<<P₂) (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-data N₁<:ₜN₂) = <:-protoD (sound-algₜ N₁<:ₜN₂)

-- urk

nv-unique : ∀ {T : Ty{k} Δ (KV pk m)} (NV₁ NV₂ : NormalVar T) → NV₁ ≡ NV₂
nv-unique NV-Var NV-Var = refl
nv-unique (NV-Dual d x) (NV-Dual d₁ x₁) = refl

nt-unique : ∀ {T : Ty{k} Δ (KV pk m)}(N₁ N₂ : NormalTy T) → N₁ ≡ N₂
np′-unique : ∀ {P : Ty{k} Δ KP} (NP₁ NP₂ : NormalProto′ P) → NP₁ ≡ NP₂
np-unique : ∀ {P : Ty{k} Δ KP} (NP₁ NP₂ : NormalProto P) → NP₁ ≡ NP₂

np-unique (N-Normal NP₁) (N-Normal NP₂) = cong N-Normal (np′-unique NP₁ NP₂)
np-unique (N-Minus NP₁) (N-Minus NP₂) = cong N-Minus (np′-unique NP₁ NP₂)

np′-unique (N-ProtoP NP₁) (N-ProtoP NP₂) = cong N-ProtoP (np-unique NP₁ NP₂)
np′-unique (N-Up N₁) (N-Up N₂) = cong N-Up (nt-unique N₁ N₂)
np′-unique N-Var N-Var = refl

nt-unique (N-Var NV₁) (N-Var NV₂) = cong N-Var (nv-unique NV₁ NV₂)
nt-unique N-Base N-Base = refl
nt-unique (N-Arrow N₁ N₃) (N-Arrow N₂ N₄) = cong₂ N-Arrow (nt-unique N₁ N₂) (nt-unique N₃ N₄)
nt-unique (N-Poly N₁) (N-Poly N₂) = cong N-Poly (nt-unique N₁ N₂)
nt-unique (N-Sub N₁) (N-Sub N₂) = cong N-Sub (nt-unique N₁ N₂)
nt-unique N-End N-End = refl
nt-unique (N-Msg {T = T} p NP₁ N₁) (N-Msg p₁ NP₂ N₂) = cong₂ (N-Msg p) (np-unique {P = T} NP₁ NP₂) (nt-unique N₁ N₂)
nt-unique (N-ProtoD N₁) (N-ProtoD N₂) = cong N-ProtoD (nt-unique N₁ N₂)

-- algorithmic subtyping is reflexive

<:ₜ-refl : ∀ {T : Ty{k} Δ (KV pk m)}(N : NormalTy T) → N <:ₜ N
<:ₚ′-refl :  ∀ {T : Ty{k} Δ KP}(NP : NormalProto′ T) → NP <:ₚ′ NP
<<:ₚ-refl : ∀ {T : Ty{k} Δ KP}(NP : NormalProto T) → NP <<:ₚ[ ⊙ ] NP

<:ₚ′-refl (N-ProtoP NP) = <:ₚ′-proto (λ {x} z → z) (<<:ₚ-refl NP)
<:ₚ′-refl (N-Up N) = <:ₚ′-up (<:ₜ-refl N)
<:ₚ′-refl N-Var = <:ₚ′-var


<:ₚ-refl :  ∀ {T : Ty{k} Δ KP}(NP : NormalProto T) → NP <:ₚ NP
<:ₚ-refl (N-Normal NP) = <:ₚ-plus (<:ₚ′-refl NP)
<:ₚ-refl (N-Minus NP) = <:ₚ-minus (<:ₚ′-refl NP)

<<:ₚ-refl {⊙ = ⊕} NP = <:ₚ-refl NP
<<:ₚ-refl {⊙ = ⊝} NP = <:ₚ-refl NP
<<:ₚ-refl {⊙ = ⊘} NP = refl

<:ₜ-refl (N-Var x) = <:ₜ-var
<:ₜ-refl N-Base = <:ₜ-base
<:ₜ-refl (N-Arrow N N₁) = <:ₜ-arrow (<:ₜ-refl N) (<:ₜ-refl N₁)
<:ₜ-refl (N-Poly N) = <:ₜ-poly (<:ₜ-refl N)
<:ₜ-refl (N-Sub N) = <:ₜ-sub (<:ₜ-refl N)
<:ₜ-refl N-End = <:ₜ-end
<:ₜ-refl (N-Msg p NP N) = <:ₜ-msg (<<:ₚ-refl NP) (<:ₜ-refl N)
<:ₜ-refl (N-ProtoD N) = <:ₜ-data (<:ₜ-refl N)

-- algorithmic subtyping is transitive

<:ₜ-trans : ∀ {T₁ T₂ T₃ : Ty{k} Δ (KV pk m)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂} {N₃ : NormalTy T₃} → N₁ <:ₜ N₂ → N₂ <:ₜ N₃ → N₁ <:ₜ N₃
<:ₚ′-trans : ∀ {T₁ T₂ T₃ : Ty{k} Δ KP} {N₁ : NormalProto′ T₁} {N₂ : NormalProto′ T₂} {N₃ : NormalProto′ T₃} → N₁ <:ₚ′ N₂ → N₂ <:ₚ′ N₃ → N₁ <:ₚ′ N₃
<<:ₚ-trans : ∀ {T₁ T₂ T₃ : Ty{k} Δ KP} {N₁ : NormalProto T₁} {N₂ : NormalProto T₂} {N₃ : NormalProto T₃} → N₁ <<:ₚ[ ⊙ ] N₂ → N₂ <<:ₚ[ ⊙ ] N₃ → N₁ <<:ₚ[ ⊙ ] N₃

<:ₚ′-trans (<:ₚ′-proto #c₁⊆#c₂ N₁<<:N₂) (<:ₚ′-proto #c₂⊆#c₃ N₂<<:N₃) = <:ₚ′-proto (λ {x} z → #c₂⊆#c₃ (#c₁⊆#c₂ z)) (<<:ₚ-trans N₁<<:N₂ N₂<<:N₃)
<:ₚ′-trans (<:ₚ′-up N₁<:N₂) (<:ₚ′-up N₂<:N₃) = <:ₚ′-up (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₚ′-trans <:ₚ′-var <:ₚ′-var = <:ₚ′-var

<:ₚ-trans : ∀ {T₁ T₂ T₃ : Ty{k} Δ KP} {N₁ : NormalProto T₁} {N₂ : NormalProto T₂} {N₃ : NormalProto T₃} → N₁ <:ₚ N₂ → N₂ <:ₚ N₃ → N₁ <:ₚ N₃
<:ₚ-trans (<:ₚ-plus N₁<:N₂) (<:ₚ-plus N₂<:N₃) = <:ₚ-plus (<:ₚ′-trans N₁<:N₂ N₂<:N₃)
<:ₚ-trans (<:ₚ-minus N₁<:N₂) (<:ₚ-minus N₂<:N₃) = <:ₚ-minus (<:ₚ′-trans N₂<:N₃ N₁<:N₂)


<<:ₚ-trans {⊙ = ⊕} N₁<<:N₂ N₂<<:N₃ = <:ₚ-trans N₁<<:N₂ N₂<<:N₃
<<:ₚ-trans {⊙ = ⊝} N₁<<:N₂ N₂<<:N₃ = <:ₚ-trans N₂<<:N₃ N₁<<:N₂
<<:ₚ-trans {⊙ = ⊘} N₁<<:N₂ N₂<<:N₃ = trans N₁<<:N₂ N₂<<:N₃

<:ₜ-trans <:ₜ-var <:ₜ-var = <:ₜ-var
<:ₜ-trans <:ₜ-base <:ₜ-base = <:ₜ-base
<:ₜ-trans (<:ₜ-arrow N₁<:N₂ N₁<:N₃) (<:ₜ-arrow N₂<:N₃ N₂<:N₄) = <:ₜ-arrow (<:ₜ-trans N₂<:N₃ N₁<:N₂) (<:ₜ-trans N₁<:N₃ N₂<:N₄)
<:ₜ-trans (<:ₜ-poly N₁<:N₂) (<:ₜ-poly N₂<:N₃) = <:ₜ-poly (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans (<:ₜ-sub N₁<:N₂) (<:ₜ-sub N₂<:N₃) = <:ₜ-sub (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans <:ₜ-end <:ₜ-end = <:ₜ-end
<:ₜ-trans (<:ₜ-msg P₁<<:P₂ N₁<:N₂) (<:ₜ-msg P₂<<:P₃ N₂<:N₃) = <:ₜ-msg (<<:ₚ-trans P₁<<:P₂ P₂<<:P₃) (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans (<:ₜ-data N₁<:N₂) (<:ₜ-data N₂<:N₃) = <:ₜ-data (<:ₜ-trans N₁<:N₂ N₂<:N₃)


-- algorithmic subtyping is complete

complete-algₜ : ∀ {T₁ T₂ : Ty{k} Δ (KV pk m)} {N₁ : NormalTy T₁}{N₂ : NormalTy T₂}
  → T₁ <: T₂ → N₁ <:ₜ N₂
complete-algₜ {N₁ = N₁} {N₂} <:-refl rewrite nt-unique N₁ N₂ = <:ₜ-refl N₂
complete-algₜ (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) = <:ₜ-trans (complete-algₜ T₁<:T₂) (complete-algₜ T₂<:T₃)
-- this is more complex: T₂ is not necessarily normalized!
-- hence: normalize T₂ → T₂′, we have T₁ <: T₂ and T₂ ≡ T₂′ ⇒ T₁ <: T₂′ and in the same manner T₂′ <: T₃
-- now we have suitable arguments for complete-algₜ!
complete-algₜ {N₁ = N-Sub N₁} {N-Sub N₂} (<:-sub K≤K′ T₁<:T₂) = <:ₜ-sub (complete-algₜ T₁<:T₂)
complete-algₜ {N₁ = N-Var ()} {N-Var x₁} <:-sub-dual-l
complete-algₜ {N₁ = N-Var ()} {N-Sub N₂} <:-sub-dual-l
complete-algₜ {N₁ = N-Var ()} {N-Var x₁} <:-sub-dual-r
complete-algₜ {N₁ = N-Sub N₁} {N-Var ()} <:-sub-dual-r
complete-algₜ {N₁ = N-Arrow N₁ N₂} {N-Arrow N₃ N₄} (<:-fun T₁<:T₂ T₁<:T₃) = <:ₜ-arrow (complete-algₜ T₁<:T₂) (complete-algₜ T₁<:T₃)
complete-algₜ {N₁ = N-ProtoD N₁} {N-ProtoD N₂} (<:-protoD T₁<:T₂) = <:ₜ-data (complete-algₜ T₁<:T₂)
complete-algₜ {N₁ = N-Poly N₁} {N-Poly N₂} (<:-all T₁<:T₂) = <:ₜ-poly (complete-algₜ T₁<:T₂)
complete-algₜ {N₁ = N₁} {N₂} (<:-neg-l T₁<:T₂) = {!!}
complete-algₜ (<:-neg-r T₁<:T₂) = {!!}
complete-algₜ {N₁ = N-Var (NV-Dual d₁ x)} {N-Var (NV-Dual d₂ x₁)} (<:-dual-lr d T₁<:T₂) = {!<:ₜ-var!}
complete-algₜ {N₁ = N₁} {N₂} (<:-dual-dual-l d T₁<:T₂) = {!N₁ N₂!}
complete-algₜ {N₁ = N₁} {N₂} (<:-dual-dual-r d T₁<:T₂) = {!!}
complete-algₜ (<:-dual-msg-l T₁<:T₂) = {!!}
complete-algₜ (<:-dual-msg-r T₁<:T₂) = {!!}
complete-algₜ {N₁ = N-Var x} {N-Var ()} <:-dual-end-l
complete-algₜ {N₁ = N-Var ()} {N-End} <:-dual-end-l
complete-algₜ {N₁ = N-End} {N-Var ()} <:-dual-end-r
complete-algₜ {N₁ = N-Msg p₁ P₁ N₁} {N-Msg p₂ P₂ N₂} (<:-msg P₁<<:P₂ T₁<:T₂) = <:ₜ-msg {!!} (complete-algₜ T₁<:T₂)

-- subtyping implies conversion
-- not possible to prove with a transitivity rule...

subty⇒conv : {T₁ T₂ : Ty {k} Δ K} → T₁ <: T₂ → T₂ <: T₁ → T₁ ≡c T₂
subty⇒conv = {!!}

-- -- type conversion

-- data _≡c_ {Δ} : {K : Kind} → Rel (Ty Δ K) where
--   ≡c-refl : T ≡c T
--   ≡c-symm : T₁ ≡c T₂ → T₂ ≡c T₁
--   ≡c-trns : T₁ ≡c T₂ → T₂ ≡c T₃ → T₁ ≡c T₃
--   ≡c-sub  : (K≤K′ : KV pk m ≤k KV pk′ m′) → T₁ ≡c T₂ → T-Sub K≤K′ T₁ ≡c T-Sub K≤K′ T₂

--   ≡c-sub-dual : {T : Ty Δ (KV KS m)} {K≤K′ : KV KS m ≤k KV KS m′} → T-Dual D-S (T-Sub K≤K′ T) ≡c T-Sub K≤K′ (T-Dual D-S T)

--   ≡c-dual-dual : (d : Dualizable K) → T-Dual d (T-Dual d T) ≡c T
--   ≡c-dual-end  : T-Dual D-S T-End ≡c T-End
--   ≡c-dual-msg  : T-Dual D-S (T-Msg p T S) ≡c T-Msg (invert p) T (T-Dual D-S S)

--   ≡c-msg-minus : T-Msg p (T-Minus T) S ≡c T-Msg (invert p) T S

--   ≡c-plus-p    : T ≡c T-Plus T
--   ≡c-minus-p   : T-Minus (T-Minus T) ≡c T

-- -- congruence rules as needed
  
--   ≡c-fun : ∀ {pk : PreKind} {≤pk : KM ≤p pk} {m} →
--            T ≡c T₂ → T₁ ≡c T₃ → T-Arrow {m = m} ≤pk T T₁ ≡c T-Arrow ≤pk T₂ T₃
--   ≡c-all : ∀ {m} → T₁ ≡c T₂ → T-Poly {m = m} T₁ ≡c T-Poly T₂
--   ≡c-msg : T₁ ≡c T₂ → S₁ ≡c S₂ → T-Msg p T₁ S₁ ≡c T-Msg p T₂ S₂
--   ≡c-protoD : T₁ ≡c T₂ → T-ProtoD T₁ ≡c T-ProtoD T₂
--   ≡c-protoP : T₁ ≡c T₂ → T-ProtoP ⊙ T₁ ≡c T-ProtoP ⊙ T₂
--   ≡c-up : T₁ ≡c T₂ → T-Up T₁ ≡c T-Up T₂
--   ≡c-minus : T₁ ≡c T₂ → T-Minus T₁ ≡c T-Minus T₂

-- -- smart constructors

-- t-msg : Polarity → Ty Δ KP → Ty Δ SLin → Ty Δ SLin
-- t-msg p T@(T-Var x) = T-Msg p T
-- t-msg p T@(T-Up _)  = T-Msg p T
-- t-msg p (T-Plus T)  = t-msg p T
-- t-msg p (T-Minus T) = t-msg (invert p) T
-- t-msg p T@(T-ProtoP _ _) = T-Msg p T

-- t-plus  : Ty Δ KP → Ty Δ KP
-- t-minus : Ty Δ KP → Ty Δ KP

-- t-plus (T-Var x) = T-Var x
-- t-plus (T-Up T) = T-Up T
-- t-plus (T-Plus T) = t-plus T
-- t-plus (T-Minus T) = t-minus T
-- t-plus (T-ProtoP ⊙ T) = T-ProtoP ⊙ T

-- t-minus T@(T-Var x) = T-Minus T
-- t-minus T@(T-Up _) = T-Minus T
-- t-minus (T-Plus T) = t-minus T
-- t-minus (T-Minus T) = t-plus T
-- t-minus T@(T-ProtoP _ _) = T-Minus T

-- -- properties of smart constructors

-- -- t-plus and t-minus are sound for conversion

-- t-plus-≡c : ∀ (T : Ty Δ KP) → t-plus T ≡c T
-- t-minus-≡c : ∀ (T : Ty Δ KP) → t-minus T ≡c T-Minus T

-- t-plus-≡c (T-Var x) = ≡c-refl
-- t-plus-≡c (T-Up T) = ≡c-refl
-- t-plus-≡c (T-Plus T) = ≡c-trns (t-plus-≡c T) ≡c-plus-p
-- t-plus-≡c (T-Minus T) = t-minus-≡c T
-- t-plus-≡c (T-ProtoP _ T) = ≡c-refl

-- t-minus-≡c (T-Var x) = ≡c-refl
-- t-minus-≡c (T-Up T) = ≡c-refl
-- t-minus-≡c (T-Plus T) = ≡c-trns (t-minus-≡c T) (≡c-minus ≡c-plus-p)
-- t-minus-≡c (T-Minus T) = ≡c-trns (t-plus-≡c T) (≡c-symm ≡c-minus-p)
-- t-minus-≡c (T-ProtoP _ T) = ≡c-refl

-- -- t-msg is sound for conversion

-- t-msg-≡c : ∀ T → t-msg p T S ≡c T-Msg p T S
-- t-msg-≡c (T-Var x) = ≡c-refl
-- t-msg-≡c (T-Up T) = ≡c-refl
-- t-msg-≡c (T-Plus T) = ≡c-trns (t-msg-≡c T) (≡c-msg ≡c-plus-p ≡c-refl)
-- t-msg-≡c (T-Minus T) = ≡c-trns (t-msg-≡c T) (≡c-symm ≡c-msg-minus)
-- t-msg-≡c (T-ProtoP _ T) = ≡c-refl

-- -- t-dual is sound for conversion

-- dual-tinv : ∀ (T : Ty Δ (KV KS m)) → T-Dual D-S T ≡c t-dual D-S T
-- dual-tinv (T-Var x) = ≡c-refl
-- dual-tinv (T-Arrow (≤p-step ()) T T₁)
-- dual-tinv (T-Sub (≤k-step ≤p-refl x₁) T) = ≡c-trns ≡c-sub-dual (≡c-sub (≤k-step ≤p-refl x₁) (dual-tinv T))
-- dual-tinv (T-Dual D-S T) = ≡c-dual-dual D-S
-- dual-tinv T-End = ≡c-dual-end
-- dual-tinv (T-Msg x T T₁) = ≡c-trns (≡c-dual-msg {p = x} {T = T} {S = T₁}) (≡c-msg (≡c-refl{T = T}) (dual-tinv T₁))

-- tinv-dual : ∀ (T : Ty Δ (KV KS m)) → T ≡c t-dual D-S (T-Dual D-S T)
-- tinv-dual (T-Var x) = ≡c-refl
-- tinv-dual (T-Arrow (≤p-step ()) T T₁)
-- tinv-dual (T-Sub x T) = ≡c-refl
-- tinv-dual (T-Dual x T) = ≡c-refl
-- tinv-dual T-End = ≡c-refl
-- tinv-dual (T-Msg x T T₁) = ≡c-refl

-- t-msg-plus : (T : Ty Δ KP) → t-msg p (t-plus T) S ≡ t-msg p T S
-- t-msg-minus : (T : Ty Δ KP) → t-msg p (t-minus T) S ≡ t-msg (invert p) T S

-- t-msg-plus (T-Var x) = refl
-- t-msg-plus (T-Up T) = refl
-- t-msg-plus (T-Plus T) = t-msg-plus T
-- t-msg-plus (T-Minus T) = t-msg-minus T
-- t-msg-plus (T-ProtoP _ T) = refl

-- t-msg-minus (T-Var x) = refl
-- t-msg-minus (T-Up T) = refl
-- t-msg-minus (T-Plus T) = t-msg-minus T
-- t-msg-minus {p = p} (T-Minus T) rewrite invert-involution{p} = t-msg-plus T
-- t-msg-minus (T-ProtoP _ T) = refl

-- t-minus-reify : (T : Ty Δ KP) → NormalTy′ T → t-minus T ≡ T-Minus T
-- t-minus-reify (T-Var x) N-Var = refl
-- t-minus-reify (T-Dual x T) ()
-- t-minus-reify (T-Up T) N-Up = refl
-- t-minus-reify (T-Plus T) ()
-- t-minus-reify (T-Minus T) ()
-- t-minus-reify (T-ProtoP _ T) N-ProtoP = refl

-- t-plus-constant : (T : Ty Δ KP) → NormalTy T → t-plus T ≡ T
-- t-plus-constant (T-Var x) (N-Normal x₁) = refl
-- t-plus-constant (T-Up T) (N-Normal x) = refl
-- t-plus-constant (T-Minus T) (N-Minus x) = t-minus-reify T x
-- t-plus-constant (T-ProtoP _ T) (N-Normal x) = refl

-- t-minus-normal : (T : Ty Δ KP) → NormalTy T → NormalTy (t-minus T)
-- t-minus-normal (T-Var x) (N-Normal N-Var) = N-Minus N-Var
-- t-minus-normal (T-Up T) (N-Normal x) = N-Minus N-Up
-- t-minus-normal (T-Minus (T-ProtoP _ _)) (N-Minus N-ProtoP) = N-Normal N-ProtoP
-- t-minus-normal (T-Minus (T-Up _)) (N-Minus N-Up) = N-Normal N-Up
-- t-minus-normal (T-Minus (T-Var _)) (N-Minus N-Var) = N-Normal N-Var
-- t-minus-normal (T-ProtoP _ T) (N-Normal x) = N-Minus N-ProtoP

-- t-minus-involution : (T : Ty Δ KP) → NormalTy T → t-minus (t-minus T) ≡ T
-- t-minus-involution (T-Var x) (N-Normal x₁) = refl
-- t-minus-involution (T-Up T) (N-Normal x) = refl
-- t-minus-involution (T-Minus (T-ProtoP _ _)) (N-Minus N-ProtoP) = refl
-- t-minus-involution (T-Minus (T-Up _)) (N-Minus N-Up) = refl
-- t-minus-involution (T-Minus (T-Var _)) (N-Minus N-Var) = refl
-- t-minus-involution (T-ProtoP _ T) (N-Normal x) = refl

-- -- normal form

-- nf-var : (p : Polarity) → (p ≡ ⊝ → Dualizable K) → K ∈ Δ → Ty Δ K
-- nf-var ⊕ d? x = T-Var x
-- nf-var ⊝ d? x = T-Dual (d? refl) (T-Var x)

-- nf : (p : Polarity) → (p ≡ ⊝ → Dualizable K) → Ty Δ K → Ty Δ K
-- nf p d? (T-Var x) = nf-var p d? x
-- nf p d? T-Base = T-Base
-- nf p d? (T-Arrow x T U) = T-Arrow x (nf ⊕ (λ()) T) (nf ⊕ (λ()) U)
-- nf p d? (T-Poly T) = T-Poly (nf ⊕ (λ()) T)
-- nf p d? (T-Sub x T) = T-Sub x (nf p (λ x₁ → dualizable-sub (d? x₁) x) T)
-- nf p d? (T-Dual dK T) = nf (invert p) (λ x₁ → dK) T
-- nf p d? T-End = T-End
-- nf p d? (T-Msg q T S) = t-msg (mult p q) (nf ⊕ (λ()) T) (nf p d? S)
-- nf p d? (T-Up T) = T-Up (nf ⊕ (λ()) T)
-- nf p d? (T-Plus T) = t-plus (nf ⊕ (λ()) T)
-- nf p d? (T-Minus T) = t-minus (nf ⊕ (λ()) T)
-- nf p d? (T-ProtoD T) = T-ProtoD (nf ⊕ (λ()) T)
-- nf p d? (T-ProtoP ⊙ T) = T-ProtoP ⊙ (nf ⊕ (λ()) T)

-- -- the nf algorithm returns a normal form

-- nf-normal : (T : Ty Δ KP) → NormalTy (nf ⊕ (λ ()) T)
-- nf-normal (T-Var x) = N-Normal N-Var
-- nf-normal (T-Up T) = N-Normal N-Up
-- nf-normal (T-Plus T) with nf-normal T
-- ... | nf-T = subst NormalTy (sym (t-plus-constant ((nf ⊕ (λ()) T)) nf-T)) nf-T
-- nf-normal (T-Minus T) with inspect (nf ⊕ (λ ())) T | nf-normal T
-- ... | Eq.[ eq ] | nf-t-normal = t-minus-normal ((nf ⊕ (λ ())) T) nf-t-normal
-- nf-normal (T-ProtoP ⊙ T) = N-Normal N-ProtoP

-- -- nf ⊕ ignores dualizability

-- nf-⊕-ignores : ∀ f g → nf ⊕ f T ≡ nf ⊕ g T
-- nf-⊕-ignores {T = T-Var x} f g = refl
-- nf-⊕-ignores {T = T-Base} f g = refl
-- nf-⊕-ignores {T = T-Arrow x T T₁} f g = refl
-- nf-⊕-ignores {T = T-Poly T} f g = refl
-- nf-⊕-ignores {T = T-Sub x T} f g = cong (T-Sub x) (nf-⊕-ignores {T = T} (λ x₁ → dualizable-sub (f x₁) x) (λ x₁ → dualizable-sub (g x₁) x))
-- nf-⊕-ignores {T = T-Dual x T} f g = refl
-- nf-⊕-ignores {T = T-End} f g = refl
-- nf-⊕-ignores {T = T-Msg x T T₁} f g = cong (t-msg (mult ⊕ x) (nf ⊕ (λ ()) T)) (nf-⊕-ignores {T = T₁} f g)
-- nf-⊕-ignores {T = T-Up T} f g = refl
-- nf-⊕-ignores {T = T-Plus T} f g = refl
-- nf-⊕-ignores {T = T-Minus T} f g = refl
-- nf-⊕-ignores {T = T-ProtoD T} f g = refl
-- nf-⊕-ignores {T = T-ProtoP _ T} f g = refl

-- -- completeness

-- nf-complete : ∀ f g → T₁ ≡c T₂ → nf ⊕ f T₁ ≡ nf ⊕ g T₂
-- nf-complete {T₁ = T₁} f g ≡c-refl = nf-⊕-ignores {T = T₁} f g
-- nf-complete f g (≡c-symm T1=T2) = sym (nf-complete g f T1=T2)
-- nf-complete f g (≡c-trns T1=T2 T1=T3) = trans (nf-complete f (λ ()) T1=T2) (nf-complete (λ ()) g T1=T3)
-- nf-complete f g (≡c-sub K≤K′ T1=T2) = cong (T-Sub K≤K′) (nf-complete (λ x₁ → dualizable-sub (f x₁) K≤K′) (λ x₁ → dualizable-sub (g x₁) K≤K′) T1=T2)
-- nf-complete {T₂ = T₂} f g (≡c-dual-dual d) = nf-⊕-ignores {T = T₂} (λ x₁ → d) g
-- nf-complete f g ≡c-dual-end = refl
-- nf-complete f g (≡c-dual-msg {p = p}) rewrite mult-invert{p = p} = refl
-- nf-complete f g (≡c-msg-minus {p = p} {T = T} {S = S}) rewrite nf-⊕-ignores{T = S} f g | mult-⊕-unit p | mult-⊕-unit (invert p) = t-msg-minus {p = p} (nf ⊕ (λ()) T)
-- nf-complete {T₁ = T₁} {T₂ = T₂} f g ≡c-plus-p
--   rewrite nf-⊕-ignores{T = T₁} f (λ()) = sym (t-plus-constant (nf ⊕ (λ()) T₁) (nf-normal T₁))
-- nf-complete {T₂ = T₂} f g ≡c-minus-p rewrite nf-⊕-ignores {T = T₂} g (λ()) = t-minus-involution (nf ⊕ (λ()) T₂) (nf-normal T₂)
-- nf-complete f g (≡c-fun {≤pk = ≤pk} T1=T2 T1=T3) = cong₂ (T-Arrow ≤pk) (nf-complete (λ()) (λ()) T1=T2) (nf-complete (λ()) (λ()) T1=T3)
-- nf-complete f g (≡c-all T1=T2) = cong T-Poly (nf-complete (λ()) (λ()) T1=T2)
-- nf-complete f g (≡c-msg {p = p} T1=T2 T1=T3) = cong₂ (t-msg (mult ⊕ p)) (nf-complete (λ()) (λ()) T1=T2) (nf-complete f g T1=T3)
-- nf-complete f g (≡c-protoD T1=T2) = cong T-ProtoD (nf-complete (λ()) (λ()) T1=T2)
-- nf-complete f g (≡c-protoP T1=T2) = cong (T-ProtoP _) (nf-complete (λ()) (λ()) T1=T2)
-- nf-complete f g (≡c-sub-dual {K≤K′ = ≤k-step ≤p-refl x₁}) = refl
-- nf-complete f g (≡c-up T1=T2) = cong T-Up (nf-complete (λ ()) (λ ()) T1=T2)
-- nf-complete f g (≡c-minus T1=T2) = cong t-minus (nf-complete _ _ T1=T2)

-- nf-complete- : ∀ f → T₁ ≡c T₂ → nf ⊝ f T₁ ≡ nf ⊝ f T₂
-- nf-complete- f ≡c-refl = refl
-- nf-complete- f (≡c-symm t1≡t2) = sym (nf-complete- f t1≡t2)
-- nf-complete- f (≡c-trns t1≡t2 t1≡t3) = trans (nf-complete- f t1≡t2) (nf-complete- f t1≡t3)
-- nf-complete- f (≡c-sub K≤K′ t1≡t2) rewrite nf-complete- (λ x → dualizable-sub (f x) K≤K′) t1≡t2 = refl
-- nf-complete- f (≡c-sub-dual {K≤K′ = ≤k-step ≤p-refl _}) = refl
-- nf-complete- f (≡c-dual-dual d) rewrite dual-irrelevant f (λ x → d) = refl
-- nf-complete- f ≡c-dual-end = refl
-- nf-complete- f (≡c-dual-msg {p = p}) rewrite mult-invert-⊕ {p} = refl
-- nf-complete- f (≡c-msg-minus {p = p}{T = T}{S = S}) = subst (λ x → x ≡ t-msg (mult ⊝ (invert p)) (nf ⊕ (λ ()) T) (nf ⊝ f S)) (sym (t-msg-minus {p = (mult ⊝ p)}{nf ⊝ f S} (nf ⊕ (λ()) T))) (cong (λ q → t-msg q (nf ⊕ (λ ()) T) (nf ⊝ f S)) (invert-mult-⊝ p))
-- nf-complete- f ≡c-plus-p with () ← f refl
-- nf-complete- f ≡c-minus-p with () ← f refl
-- nf-complete- f (≡c-fun {≤pk = ≤p-refl} t1≡t2 t1≡t3) with () ← f refl
-- nf-complete- f (≡c-fun {≤pk = ≤p-step <p-mt} t1≡t2 t1≡t3) with () ← f refl
-- nf-complete- f (≡c-all t1≡t2) with () ← f refl
-- nf-complete- f (≡c-msg {S₂ = S₂} {p = p} t1≡t2 t1≡t3) rewrite nf-complete- f t1≡t3 = cong (λ nft → t-msg (mult ⊝ p) nft (nf ⊝ f S₂)) ( nf-complete (λ()) (λ()) t1≡t2)
-- nf-complete- f (≡c-protoD t1≡t2) with () ← f refl
-- nf-complete- f (≡c-protoP t1≡t2) with () ← f refl
-- nf-complete- f (≡c-up t1≡t2) with () ← f refl
-- nf-complete- f (≡c-minus t1≡t2) with () ← f refl

-- -- soundness

-- nf-sound+ : ∀ {f} → (T : Ty Δ K)         → nf ⊕ f T ≡c T
-- nf-sound- : ∀ {f} → (T : Ty Δ (KV KS m)) → nf ⊝ f T ≡c t-dual D-S T

-- nf-sound+ (T-Var x) = ≡c-refl
-- nf-sound+ T-Base = ≡c-refl
-- nf-sound+ (T-Arrow x T T₁) = ≡c-fun (nf-sound+ T) (nf-sound+ T₁)
-- nf-sound+ (T-Poly T) = ≡c-all (nf-sound+ T)
-- nf-sound+ (T-Sub x T) = ≡c-sub x (nf-sound+ T)
-- nf-sound+ (T-Dual D-S T) = ≡c-trns (nf-sound- T) (≡c-symm (dual-tinv T))
-- nf-sound+ T-End = ≡c-refl
-- nf-sound+ (T-Msg ⊕ T S) = ≡c-trns (t-msg-≡c (nf ⊕ (λ ()) T)) (≡c-msg (nf-sound+ T) (nf-sound+ S))
-- nf-sound+ (T-Msg ⊝ T S) = ≡c-trns (t-msg-≡c (nf ⊕ (λ ()) T)) (≡c-msg (nf-sound+ T) (nf-sound+ S))
-- nf-sound+ (T-Up T) = ≡c-up (nf-sound+ T)
-- nf-sound+ (T-Plus T) = ≡c-trns (t-plus-≡c (nf ⊕ (λ ()) T)) (≡c-trns (nf-sound+ T) ≡c-plus-p)
-- nf-sound+ (T-Minus T) = ≡c-trns (t-minus-≡c (nf ⊕ (λ ()) T)) (≡c-minus (nf-sound+ T))
-- nf-sound+ (T-ProtoD T) = ≡c-protoD (nf-sound+ T)
-- nf-sound+ (T-ProtoP _ T) = ≡c-protoP (nf-sound+ T)

-- nf-sound- {f = f} (T-Var x) rewrite ext-dual-s-irrelevant f (λ x → D-S) = ≡c-refl
-- nf-sound- (T-Arrow (≤p-step ()) T T₁)
-- nf-sound- (T-Sub (≤k-step ≤p-refl x₁) T) = ≡c-sub (≤k-step ≤p-refl x₁) (nf-sound- T)
-- nf-sound- (T-Dual D-S T) = nf-sound+ T
-- nf-sound- T-End = ≡c-refl
-- nf-sound- (T-Msg ⊕ T S) = ≡c-trns (t-msg-≡c (nf ⊕ (λ ()) T)) (≡c-msg (nf-sound+ T) (nf-sound- S))
-- nf-sound- (T-Msg ⊝ T S) = ≡c-trns (t-msg-≡c (nf ⊕ (λ ()) T)) (≡c-msg (nf-sound+ T) (nf-sound- S))

