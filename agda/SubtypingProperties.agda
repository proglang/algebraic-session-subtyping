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
