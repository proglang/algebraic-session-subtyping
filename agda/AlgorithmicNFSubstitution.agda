module AlgorithmicNFSubstitution where

open import Data.List using (_∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

open import Kinds
open import Kits
open import Duality
open import Variance using (Variance; ⊕; ⊝; ⊘)
open import Types using (Ty; Ty-Syntax; Ty-Traversal; nf)
open import Subtyping using (injᵥ)
open import AlgorithmicNFSubtyping
open import NormalTypes using (NFProto; NFProto′; NFTy; N-Var; nfProtoTy; nfProto′Ty)
open import NormalTypesSubstitution

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (⋯-id)

substNFProtoWith-≡ :
  ∀ {Δ₁ Δ₂} (σ : NFSub Δ₁ Δ₂) {N₁ N₂ : NFProto Δ₁}
  → nfProtoTy N₁ ≡ nfProtoTy N₂
  → nfProtoTy (substNFProtoWith σ N₁) ≡ nfProtoTy (substNFProtoWith σ N₂)
substNFProtoWith-≡ σ {N₁ = N₁} {N₂ = N₂} eq =
  trans
    (substNFProto-sound σ N₁)
    (trans
      (cong (λ T → nf ⊕ d?⊥ (T ⋯ nfSubTy σ)) eq)
      (sym (substNFProto-sound σ N₂)))

substNFProto′With-≡ :
  ∀ {Δ₁ Δ₂} (σ : NFSub Δ₁ Δ₂) {N₁ N₂ : NFProto′ Δ₁}
  → nfProto′Ty N₁ ≡ nfProto′Ty N₂
  → nfProtoTy (substNFProto′With σ N₁) ≡ nfProtoTy (substNFProto′With σ N₂)
substNFProto′With-≡ σ {N₁ = N₁} {N₂ = N₂} eq =
  trans
    (substNFProto′-sound σ N₁)
    (trans
      (cong (λ T → nf ⊕ d?⊥ (T ⋯ nfSubTy σ)) eq)
      (sym (substNFProto′-sound σ N₂)))

msgNF-preserves-<: :
  ∀ {Δ} {p : Polarity} {P₁ P₂ : NFProto Δ} {S₁ S₂ : NFTy Δ SLin}
  → P₁ <<:ₚ[ injᵥ p ] P₂
  → S₁ <:ₜ S₂
  → msgNF p P₁ S₁ <:ₜ msgNF p P₂ S₂
msgNF-preserves-<: {p = ⊕} (<:ₚ-plus P₁<<:P₂) S₁<:S₂ = <:ₜ-msg P₁<<:P₂ S₁<:S₂
msgNF-preserves-<: {p = ⊕} (<:ₚ-minus P₂<<:P₁) S₁<:S₂ = <:ₜ-msg P₂<<:P₁ S₁<:S₂
msgNF-preserves-<: {p = ⊝} (<:ₚ-plus P₂<<:P₁) S₁<:S₂ = <:ₜ-msg P₂<<:P₁ S₁<:S₂
msgNF-preserves-<: {p = ⊝} (<:ₚ-minus P₁<<:P₂) S₁<:S₂ = <:ₜ-msg P₁<<:P₂ S₁<:S₂

minusNF-preserves-<: :
  ∀ {Δ} {P₁ P₂ : NFProto Δ}
  → P₂ <:ₚ P₁
  → minusNF P₁ <:ₚ minusNF P₂
minusNF-preserves-<: (<:ₚ-plus P₂<:P₁) = <:ₚ-minus P₂<:P₁
minusNF-preserves-<: (<:ₚ-minus P₁<:P₂) = <:ₚ-plus P₁<:P₂

mutual

  subst-preserves-<:ₜWith :
    ∀ {Δ₁ Δ₂ pk m}
      (σ : NFSub Δ₁ Δ₂) {N₁ N₂ : NFTy Δ₁ (KV pk m)}
    → N₁ <:ₜ N₂
    → substNFTyWith σ N₁ <:ₜ substNFTyWith σ N₂

  subst-preserves-<:ₚ′With :
    ∀ {Δ₁ Δ₂}
      (σ : NFSub Δ₁ Δ₂) {N₁ N₂ : NFProto′ Δ₁}
    → N₁ <:ₚ′ N₂
    → substNFProto′With σ N₁ <:ₚ substNFProto′With σ N₂

  subst-preserves-<:ₚWith :
    ∀ {Δ₁ Δ₂}
      (σ : NFSub Δ₁ Δ₂) {N₁ N₂ : NFProto Δ₁}
    → N₁ <:ₚ N₂
    → substNFProtoWith σ N₁ <:ₚ substNFProtoWith σ N₂

  subst-preserves-<<:ₚ′With :
    ∀ {Δ₁ Δ₂}
      (σ : NFSub Δ₁ Δ₂) {N₁ N₂ : NFProto′ Δ₁}
      {⊙ : Variance}
    → N₁ <<:ₚ′[ ⊙ ] N₂
    → substNFProto′With σ N₁ <<:ₚ[ ⊙ ] substNFProto′With σ N₂

  subst-preserves-<<:ₚWith :
    ∀ {Δ₁ Δ₂}
      (σ : NFSub Δ₁ Δ₂) {N₁ N₂ : NFProto Δ₁}
      {⊙ : Variance}
    → N₁ <<:ₚ[ ⊙ ] N₂
    → substNFProtoWith σ N₁ <<:ₚ[ ⊙ ] substNFProtoWith σ N₂

  subst-preserves-<:ₜWith σ (<:ₜ-var {nv = nv}) = <:ₜ-refl (substNFTyWith σ (N-Var nv))
  subst-preserves-<:ₜWith σ <:ₜ-base = <:ₜ-base
  subst-preserves-<:ₜWith σ (<:ₜ-arrow N₂<:N₁ N₁<:N₂) =
    <:ₜ-arrow (subst-preserves-<:ₜWith σ N₂<:N₁) (subst-preserves-<:ₜWith σ N₁<:N₂)
  subst-preserves-<:ₜWith σ (<:ₜ-pair N₁<:N₂ N₃<:N₄) =
    <:ₜ-pair (subst-preserves-<:ₜWith σ N₁<:N₂) (subst-preserves-<:ₜWith σ N₃<:N₄)
  subst-preserves-<:ₜWith σ (<:ₜ-poly N₁<:N₂) =
    <:ₜ-poly (subst-preserves-<:ₜWith (wkNFSub σ) N₁<:N₂)
  subst-preserves-<:ₜWith σ (<:ₜ-sub N₁<:N₂) =
    <:ₜ-sub (subst-preserves-<:ₜWith σ N₁<:N₂)
  subst-preserves-<:ₜWith σ <:ₜ-end = <:ₜ-end
  subst-preserves-<:ₜWith σ (<:ₜ-msg P₁<<:P₂ S₁<:S₂) =
    msgNF-preserves-<:
      (subst-preserves-<<:ₚ′With σ P₁<<:P₂)
      (subst-preserves-<:ₜWith σ S₁<:S₂)
  subst-preserves-<:ₜWith σ (<:ₜ-data N₁<:N₂) =
    <:ₜ-data (subst-preserves-<:ₜWith σ N₁<:N₂)

  subst-preserves-<:ₚ′With σ (<:ₚ′-proto #c₁⊆#c₂ N₁<<:N₂) =
    <:ₚ-plus (<:ₚ′-proto #c₁⊆#c₂ (subst-preserves-<<:ₚWith σ N₁<<:N₂))
  subst-preserves-<:ₚ′With σ (<:ₚ′-up N₁<:N₂) =
    <:ₚ-plus (<:ₚ′-up (subst-preserves-<:ₜWith σ N₁<:N₂))
  subst-preserves-<:ₚ′With σ (<:ₚ′-var {x = x}) =
    <:ₚ-refl (σ KP x)

  subst-preserves-<:ₚWith σ (<:ₚ-plus N₁<:N₂) =
    subst-preserves-<:ₚ′With σ N₁<:N₂
  subst-preserves-<:ₚWith σ (<:ₚ-minus N₂<:N₁) =
    minusNF-preserves-<: (subst-preserves-<:ₚ′With σ N₂<:N₁)

  subst-preserves-<<:ₚ′With σ {⊙ = ⊕} N₁<<:N₂ =
    subst-preserves-<:ₚ′With σ N₁<<:N₂
  subst-preserves-<<:ₚ′With σ {N₁ = N₁} {N₂ = N₂} {⊙ = ⊘} N₁≡N₂ =
    substNFProto′With-≡ σ {N₁ = N₁} {N₂ = N₂} N₁≡N₂
  subst-preserves-<<:ₚ′With σ {⊙ = ⊝} N₂<<:N₁ =
    subst-preserves-<:ₚ′With σ N₂<<:N₁

  subst-preserves-<<:ₚWith σ {⊙ = ⊕} N₁<<:N₂ =
    subst-preserves-<:ₚWith σ N₁<<:N₂
  subst-preserves-<<:ₚWith σ {N₁ = N₁} {N₂ = N₂} {⊙ = ⊘} N₁≡N₂ =
    substNFProtoWith-≡ σ {N₁ = N₁} {N₂ = N₂} N₁≡N₂
  subst-preserves-<<:ₚWith σ {⊙ = ⊝} N₂<<:N₁ =
    subst-preserves-<:ₚWith σ N₂<<:N₁

subst-preserves-<:ₜ :
  ∀ {Δ K pk m} {N₁ N₂ : NFTy (K ∷ Δ) (KV pk m)} {U : NFKind Δ K}
  → N₁ <:ₜ N₂
  → substNFTy N₁ U <:ₜ substNFTy N₂ U
subst-preserves-<:ₜ {U = U} =
  subst-preserves-<:ₜWith (singleNFSub U)
