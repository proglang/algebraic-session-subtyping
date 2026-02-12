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

module SubtypingProperties  where

open import Util
open import Kinds
open import Duality
open import Types
open import Subtyping

normal-proto′-<: : (T₁ T₂ : Ty Δ KP) → T₁ <: T₂ → NormalProto′ (nf ⊕ d?⊥ T₁) → NormalProto′ (nf ⊕ d?⊥ T₂)
normal-proto′-<:-minus : (T₁ T₂ : Ty Δ KP) → T₂ <: T₁ → NormalProto′ (t-minus (nf ⊕ d?⊥ T₁)) → NormalProto′ (t-minus (nf ⊕ d?⊥ T₂))

normal-proto′-<: T₁ T₃ (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) N₁ = normal-proto′-<: T₂ T₃ T₂<:T₃ (normal-proto′-<: T₁ T₂ T₁<:T₂ N₁)
normal-proto′-<: T₁ T₂ <:-var N₁ = N₁
normal-proto′-<: (T-Up T₁) (T-Up T₂) (<:-up T₁<:T₂) N₁ = N-Up (nf-normal-type ⊕ d?⊥ T₂)
normal-proto′-<: (T-ProtoP #c ⊙ T₁) (T-ProtoP #d .⊙ T₂) (<:-proto #c⊆#d T₁<<:T₂) N₁ = N-ProtoP (nf-normal-proto T₂)
normal-proto′-<: T₁ T₂ (<:-minus T₁<:T₂) N₁ = normal-proto′-<:-minus _ _ T₁<:T₂ N₁
normal-proto′-<: T₁ T₂ (<:-minus-minus-l {T₃} T₁<:T₂) N₁
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-<: _ _ T₁<:T₂ N₁ 
normal-proto′-<: T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₁<:T₂) N₁
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-<: _ _ T₁<:T₂ N₁

normal-proto′-<:-minus T₁ T₃ (<:-trans T₃<:T₂ T₂<:T₁) N₁ = normal-proto′-<:-minus _ _ T₃<:T₂ (normal-proto′-<:-minus _ _ T₂<:T₁ N₁)
normal-proto′-<:-minus T₁ T₂ (<:-minus {T₄} {T₁ = T₃} T₂<:T₁) N₁
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  | t-minus-involution (nf ⊕ d?⊥ T₄) (nf-normal-proto T₄)
  = normal-proto′-<: _ _ T₂<:T₁ N₁
normal-proto′-<:-minus T₁ T₂ (<:-minus-minus-l {T₃} T₂<:T₁) N₁
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-<:-minus _ _ T₂<:T₁ N₁
normal-proto′-<:-minus T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₂<:T₁) N₁
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-<:-minus _ _ T₂<:T₁ N₁

<<:-invert : ∀ {p} {T₁ T₂ : Ty Δ KP} → T₁ <<:[ injᵥ p ] T₂ → T₂ <<:[ injᵥ (invert p) ] T₁
<<:-invert {p = ⊕} T₁<<:T₂ = T₁<<:T₂
<<:-invert {p = ⊝} T₁<<:T₂ = T₁<<:T₂


lemma-sub-<<: : {T₁ T₂ : Ty Δ KP} (T₁<<:T₂ : T₁ <<:[ ⊙ ] T₂) → nf ⊕ d?⊥ T₁ <<:[ ⊙ ] nf ⊕ d?⊥ T₂
lemma-sub-<<: {⊙ = ⊕} T₁<<:T₂ = norm-pres-sub {p = ⊕} T₁<<:T₂
lemma-sub-<<: {⊙ = ⊝} T₂<<:T₁ = norm-pres-sub {p = ⊕} T₂<<:T₁
lemma-sub-<<: {⊙ = ⊘} T₁≡cT₂ rewrite nf-complete d?⊥ d?⊥ T₁≡cT₂ = ≡c-refl

lemma-sub-loop : ∀ {p₃} {T₁ T₂ : Ty Δ KP} (T₁<<:T₂ : T₁ <<:[ injᵥ p₃ ] T₂)
  → t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₂ <<:[ injᵥ (t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₁) ] t-loop p₃ (nf ⊕ d?⊥ T₂) .proj₂
lemma-sub-loop {p₃ = ⊕} {T₁} {T₃} (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃)
  = <<:-trans (lemma-sub-loop {p₃ = ⊕} T₂<<:T₃) (subst (λ p → _ <<:[ injᵥ p ] _) (t-loop-sub-<<: ⊝ ⊕ T₂<<:T₃) (lemma-sub-loop {p₃ = ⊕} T₁<<:T₂))
lemma-sub-loop {p₃ = ⊕} <:-var = <:-var
lemma-sub-loop {p₃ = ⊕} (<:-up T₁<<:T₂) = <:-up (norm-pres-sub {p = ⊕} T₁<<:T₂)
lemma-sub-loop {p₃ = ⊕} (<:-proto #c⊆#d T₁<<:T₂) = <:-proto #c⊆#d (lemma-sub-<<: T₁<<:T₂)
lemma-sub-loop {p₃ = ⊕} (<:-minus {T₂} {T₁ = T₁} T₁<<:T₂)
  rewrite t-loop-minus {p = ⊕} (nf ⊕ d?⊥ T₁) | t-loop-minus {p = ⊕} (nf ⊕ d?⊥ T₂)
  = lemma-sub-loop {p₃ = ⊝} T₁<<:T₂
lemma-sub-loop {p₃ = ⊕} (<:-minus-minus-l {T₁} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = lemma-sub-loop {p₃ = ⊕} T₁<<:T₂
lemma-sub-loop {p₃ = ⊕} (<:-minus-minus-r {T₂ = T₂} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = lemma-sub-loop {p₃ = ⊕} T₁<<:T₂
lemma-sub-loop {p₃ = ⊝} {T₁} {T₃} (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃)
  = <<:-trans (lemma-sub-loop {p₃ = ⊝} T₁<<:T₂)
              (subst (λ p → _ <<:[ injᵥ p ] _) (sym (t-loop-sub-<<: ⊝ ⊝ T₁<<:T₂)) (lemma-sub-loop {p₃ = ⊝} T₂<<:T₃))
lemma-sub-loop {p₃ = ⊝} <:-var = <:-var
lemma-sub-loop {p₃ = ⊝} (<:-up T₁<<:T₂) = <:-up (norm-pres-sub {p = ⊕} T₁<<:T₂)
lemma-sub-loop {p₃ = ⊝} (<:-proto #c⊆#d T₁<<:T₂) = <:-proto #c⊆#d (lemma-sub-<<: T₁<<:T₂)
lemma-sub-loop {p₃ = ⊝} (<:-minus {T₂} {T₁ = T₁} T₁<<:T₂)
  rewrite t-loop-minus {p = ⊝} (nf ⊕ d?⊥ T₁) |  t-loop-minus {p = ⊝} (nf ⊕ d?⊥ T₂)
  = lemma-sub-loop {p₃ = ⊕} T₁<<:T₂
lemma-sub-loop {p₃ = ⊝} (<:-minus-minus-l {T₁} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = lemma-sub-loop {p₃ = ⊝} T₁<<:T₂
lemma-sub-loop {p₃ = ⊝} (<:-minus-minus-r {T₂ = T₂} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = lemma-sub-loop {p₃ = ⊝} T₁<<:T₂

lemma-sub-loop-right : ∀ {p₃} {T₁ T₂ : Ty Δ KP} (T₁<<:T₂ : T₁ <<:[ injᵥ p₃ ] T₂)
  → t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₂ <<:[ injᵥ (t-loop p₃ (nf ⊕ d?⊥ T₂) .proj₁) ] t-loop p₃ (nf ⊕ d?⊥ T₂) .proj₂
lemma-sub-loop-right {p₃ = p₃} T₁<<:T₂
  with lemma-sub-loop T₁<<:T₂
... | r
  rewrite t-loop-sub-<<: p₃ p₃ T₁<<:T₂ = r

