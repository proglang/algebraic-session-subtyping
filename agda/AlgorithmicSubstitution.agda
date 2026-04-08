module AlgorithmicSubstitution where

open import Data.Nat using (_⊔_)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (_∷_)

open import Kinds
open import Kits
import Duality as D
open import Types using (Ty; Ty-Syntax; Ty-Traversal; NormalTy; nf-normal-type; sizeₜ)
open import Subtyping
open import SubstitutionSubtyping
open import AlgorithmicSubtyping
open import AlgorithmicSound
open import AlgorithmicComplete

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (⋯-id)

subst-preserves-<:ₜ :
  ∀ {Δ K pk m} {T₁ T₂ : Ty (K ∷ Δ) (KV pk m)} {U : Ty Δ K}
    {N₁ : NormalTy T₁} {N₂ : NormalTy T₂}
  → N₁ <:ₜ N₂
  → nf-normal-type D.⊕ D.d?⊥ (T₁ ⋯ ⦅ U ⦆ₛ) <:ₜ nf-normal-type D.⊕ D.d?⊥ (T₂ ⋯ ⦅ U ⦆ₛ)
subst-preserves-<:ₜ {T₁ = T₁} {T₂ = T₂} {U = U} {N₁ = N₁} {N₂ = N₂} N₁<:N₂
  using T₁<:T₂ ← sound-algₜ N₁<:N₂
  using N₁′ ← nf-normal-type D.⊕ D.d?⊥ (T₁ ⋯ ⦅ U ⦆ₛ)
  using N₂′ ← nf-normal-type D.⊕ D.d?⊥ (T₂ ⋯ ⦅ U ⦆ₛ)
  = complete-algₜ (sizeₜ N₁′ ⊔ sizeₜ N₂′)
      (subst-preserves T₁<:T₂ ⦅ U ⦆ₛ)
      {N₁ = N₁′} {N₂ = N₂′}
      ≤-refl
