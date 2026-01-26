open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Nat
open import Data.Fin.Subset as Subset using (_⊆_)
open import Data.Fin.Subset.Properties using (⊆-refl; ⊆-antisym)
open import Data.List
open import Data.Product
-- open import Data.Sum
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; inspect; Reveal_·_is_; module ≡-Reasoning)
open ≡-Reasoning

open import Function using (const)

module SubstitutionSubtyping  where

open import Util
open import Kinds
open import Duality
open import Types
open import Subtyping

open import Kits

open Syntax Ty-Syntax hiding (Sort)

subst-preserves-≡c : ⦃ KT : Kit _∋/⊢_ ⦄ → {T₁ T₂ : Ty Δ₁ K} → T₁ ≡c T₂ → (ϕ : Δ₁ –[ KT ]→ Δ₂) → (T₁ ⋯ ϕ) ≡c (T₂ ⋯ ϕ)
subst-preserves-≡c ≡c-refl ϕ = ≡c-refl
subst-preserves-≡c (≡c-symm T₁≡T₂) ϕ = ≡c-symm (subst-preserves-≡c T₁≡T₂ ϕ)
subst-preserves-≡c (≡c-trns T₁≡T₂ T₁≡T₃) ϕ = ≡c-trns (subst-preserves-≡c T₁≡T₂ ϕ) (subst-preserves-≡c T₁≡T₃ ϕ)
subst-preserves-≡c (≡c-sub K≤K′ T₁≡T₂) ϕ = ≡c-sub K≤K′ (subst-preserves-≡c T₁≡T₂ ϕ)
subst-preserves-≡c ≡c-sub-dual ϕ = ≡c-sub-dual
subst-preserves-≡c (≡c-dual-dual d) ϕ = ≡c-dual-dual d
subst-preserves-≡c ≡c-dual-end ϕ = ≡c-dual-end
subst-preserves-≡c ≡c-dual-msg ϕ = ≡c-dual-msg
subst-preserves-≡c ≡c-msg-minus ϕ = ≡c-msg-minus
subst-preserves-≡c ≡c-minus-p ϕ = ≡c-minus-p
subst-preserves-≡c (≡c-fun T₁≡T₂ T₁≡T₃) ϕ = ≡c-fun (subst-preserves-≡c T₁≡T₂ ϕ) (subst-preserves-≡c T₁≡T₃ ϕ)
subst-preserves-≡c (≡c-all T₁≡T₂) ϕ = ≡c-all (subst-preserves-≡c T₁≡T₂ (ϕ ↑ _))
subst-preserves-≡c (≡c-msg T₁≡T₂ T₁≡T₃) ϕ = ≡c-msg (subst-preserves-≡c T₁≡T₂ ϕ) (subst-preserves-≡c T₁≡T₃ ϕ)
subst-preserves-≡c (≡c-protoD T₁≡T₂) ϕ = ≡c-protoD (subst-preserves-≡c T₁≡T₂ ϕ)
subst-preserves-≡c (≡c-protoP T₁≡T₂) ϕ = ≡c-protoP (subst-preserves-≡c T₁≡T₂ ϕ)
subst-preserves-≡c (≡c-up T₁≡T₂) ϕ = ≡c-up (subst-preserves-≡c T₁≡T₂ ϕ)
subst-preserves-≡c (≡c-minus T₁≡T₂) ϕ = ≡c-minus (subst-preserves-≡c T₁≡T₂ ϕ)

subst-preserves : ⦃ KT : Kit _∋/⊢_ ⦄ → {T₁ T₂ : Ty Δ₁ K} → T₁ <: T₂ → (ϕ : Δ₁ –[ KT ]→ Δ₂) → (T₁ ⋯ ϕ) <: (T₂ ⋯ ϕ)
subst-preserves-<<: : ⦃ KT : Kit _∋/⊢_ ⦄ → {T₁ T₂ : Ty Δ₁ K} → T₁ <<:[ ⊙ ] T₂ → (ϕ : Δ₁ –[ KT ]→ Δ₂) → (T₁ ⋯ ϕ) <<:[ ⊙ ] (T₂ ⋯ ϕ)

subst-preserves <:-var ϕ = <:-refl
subst-preserves <:-dual-var ϕ = <:-refl
subst-preserves <:-base ϕ = <:-refl
subst-preserves <:-end ϕ = <:-refl
subst-preserves (<:-trans T₁<:T₂ T₁<:T₃) ϕ = <:-trans (subst-preserves T₁<:T₂ ϕ) (subst-preserves T₁<:T₃ ϕ)
subst-preserves (<:-sub K≤K′ T₁<:T₂) ϕ = <:-sub K≤K′ (subst-preserves T₁<:T₂ ϕ)
subst-preserves <:-sub-dual-l ϕ = <:-sub-dual-l
subst-preserves <:-sub-dual-r ϕ = <:-sub-dual-r
subst-preserves (<:-fun T₁<:T₂ T₁<:T₃) ϕ = <:-fun (subst-preserves T₁<:T₂ ϕ) (subst-preserves T₁<:T₃ ϕ)
subst-preserves (<:-protoD T₁<:T₂) ϕ = <:-protoD (subst-preserves T₁<:T₂ ϕ)
subst-preserves (<:-all T₁<:T₂) ϕ = <:-all (subst-preserves T₁<:T₂ (ϕ ↑ _))
subst-preserves (<:-neg-l T₁<:T₂) ϕ = <:-neg-l (subst-preserves T₁<:T₂ ϕ)
subst-preserves (<:-neg-r T₁<:T₂) ϕ = <:-neg-r (subst-preserves T₁<:T₂ ϕ)
subst-preserves (<:-dual-dual-l d T₁<:T₂) ϕ = <:-dual-dual-l d (subst-preserves T₁<:T₂ ϕ)
subst-preserves (<:-dual-dual-r d T₁<:T₂) ϕ = <:-dual-dual-r d (subst-preserves T₁<:T₂ ϕ)
subst-preserves (<:-dual-msg-l T₁<:T₂) ϕ = <:-dual-msg-l (subst-preserves T₁<:T₂ ϕ)
subst-preserves (<:-dual-msg-r T₁<:T₂) ϕ = <:-dual-msg-r (subst-preserves T₁<:T₂ ϕ)
subst-preserves <:-dual-end-l ϕ = <:-dual-end-l
subst-preserves <:-dual-end-r ϕ = <:-dual-end-r
subst-preserves (<:-msg T₁<<:T₂ S₁<:S₂) ϕ = <:-msg (subst-preserves-<<: T₁<<:T₂ ϕ) (subst-preserves S₁<:S₂ ϕ)
subst-preserves (<:-up T₁<:T₂) ϕ = <:-up (subst-preserves T₁<:T₂ ϕ)
subst-preserves (<:-proto #c⊆#d T₁<<:T₂) ϕ = <:-proto #c⊆#d (subst-preserves-<<: T₁<<:T₂ ϕ)
subst-preserves (<:-minus T₁<:T₂) ϕ = <:-minus (subst-preserves T₁<:T₂ ϕ)
subst-preserves (<:-minus-minus-l T₁<:T₂) ϕ = <:-minus-minus-l (subst-preserves T₁<:T₂ ϕ)
subst-preserves (<:-minus-minus-r T₁<:T₂) ϕ = <:-minus-minus-r (subst-preserves T₁<:T₂ ϕ)

subst-preserves-<<: {⊙ = ⊕} T₁<<:T₂ ϕ = subst-preserves T₁<<:T₂ ϕ
subst-preserves-<<: {⊙ = ⊝} T₁<<:T₂ ϕ = subst-preserves T₁<<:T₂ ϕ
subst-preserves-<<: {⊙ = ⊘} T₁<<:T₂ ϕ = subst-preserves-≡c T₁<<:T₂ ϕ
