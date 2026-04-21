module NormalTypesRenamings where

open import Data.List using (List; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)

open import Kinds
open import Kits
open import Duality
open import Types using (Ty; Ty-Syntax; Ty-Traversal)
open import NormalTypes

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (⋯-id)

variable
  Δ₁ Δ₂ : List Kind

mutual

  renNFProto′ : (ρ : Δ₁ →ᵣ Δ₂) → NFProto′ Δ₁ → NFProto′ Δ₂
  renNFProto : (ρ : Δ₁ →ᵣ Δ₂) → NFProto Δ₁ → NFProto Δ₂
  renNFVar : ∀ {K} → (ρ : Δ₁ →ᵣ Δ₂) → NFVar Δ₁ K → NFVar Δ₂ K
  renNFTy : ∀ {K} → (ρ : Δ₁ →ᵣ Δ₂) → NFTy Δ₁ K → NFTy Δ₂ K

  renNFProto′ ρ (N-ProtoP #c ⊙ N) = N-ProtoP #c ⊙ (renNFProto ρ N)
  renNFProto′ ρ (N-Up N) = N-Up (renNFTy ρ N)
  renNFProto′ ρ (N-Var x) = N-Var (ρ _ x)

  renNFProto ρ (N-Normal N) = N-Normal (renNFProto′ ρ N)
  renNFProto ρ (N-Minus N) = N-Minus (renNFProto′ ρ N)

  renNFVar ρ (NV-Var x) = NV-Var (ρ _ x)
  renNFVar ρ (NV-Dual d x) = NV-Dual d (ρ _ x)

  renNFTy ρ (N-Var N) = N-Var (renNFVar ρ N)
  renNFTy ρ N-Base = N-Base
  renNFTy ρ (N-Arrow N₁ N₂) = N-Arrow (renNFTy ρ N₁) (renNFTy ρ N₂)
  renNFTy ρ (N-Pair N₁ N₂) = N-Pair (renNFTy ρ N₁) (renNFTy ρ N₂)
  renNFTy ρ (N-Poly K′ N) = N-Poly K′ (renNFTy (ρ ↑ᵣ K′) N)
  renNFTy ρ (N-Sub km≤ N) = N-Sub km≤ (renNFTy ρ N)
  renNFTy ρ N-End = N-End
  renNFTy ρ (N-Msg p NP NS) = N-Msg p (renNFProto′ ρ NP) (renNFTy ρ NS)
  renNFTy ρ (N-ProtoD N) = N-ProtoD (renNFTy ρ N)

wkNFProto′ : ∀ {K} → NFProto′ Δ → NFProto′ (K ∷ Δ)
wkNFProto′ {K = K} = renNFProto′ (weakenᵣ K)

wkNFProto : ∀ {K} → NFProto Δ → NFProto (K ∷ Δ)
wkNFProto {K = K} = renNFProto (weakenᵣ K)

wkNFVar : ∀ {K K′} → NFVar Δ K → NFVar (K′ ∷ Δ) K
wkNFVar {K′ = K′} = renNFVar (weakenᵣ K′)

wkNFTy : ∀ {K K′} → NFTy Δ K → NFTy (K′ ∷ Δ) K
wkNFTy {K′ = K′} = renNFTy (weakenᵣ K′)

mutual

  renNFProto′-sound :
    (ρ : Δ₁ →ᵣ Δ₂) (N : NFProto′ Δ₁)
    → nfProto′Ty (renNFProto′ ρ N) ≡ nfProto′Ty N ⋯ ρ

  renNFProto-sound :
    (ρ : Δ₁ →ᵣ Δ₂) (N : NFProto Δ₁)
    → nfProtoTy (renNFProto ρ N) ≡ nfProtoTy N ⋯ ρ

  renNFVar-sound :
    ∀ {K} (ρ : Δ₁ →ᵣ Δ₂) (N : NFVar Δ₁ K)
    → nfVarTy (renNFVar ρ N) ≡ nfVarTy N ⋯ ρ

  renNFTy-sound :
    ∀ {K} (ρ : Δ₁ →ᵣ Δ₂) (N : NFTy Δ₁ K)
    → nfTyTy (renNFTy ρ N) ≡ nfTyTy N ⋯ ρ

  renNFProto′-sound ρ (N-ProtoP #c ⊙ N) =
    cong (λ T → Types.T-ProtoP #c ⊙ T) (renNFProto-sound ρ N)
  renNFProto′-sound ρ (N-Up N) =
    cong Types.T-Up (renNFTy-sound ρ N)
  renNFProto′-sound ρ (N-Var x) = refl

  renNFProto-sound ρ (N-Normal N) = renNFProto′-sound ρ N
  renNFProto-sound ρ (N-Minus N) =
    cong Types.T-Minus (renNFProto′-sound ρ N)

  renNFVar-sound ρ (NV-Var x) = refl
  renNFVar-sound ρ (NV-Dual d x) = refl

  renNFTy-sound ρ (N-Var N) = renNFVar-sound ρ N
  renNFTy-sound ρ N-Base = refl
  renNFTy-sound ρ (N-Arrow N₁ N₂) =
    cong₂ Types.T-Arrow (renNFTy-sound ρ N₁) (renNFTy-sound ρ N₂)
  renNFTy-sound ρ (N-Pair N₁ N₂) =
    cong₂ Types.T-Pair (renNFTy-sound ρ N₁) (renNFTy-sound ρ N₂)
  renNFTy-sound ρ (N-Poly K′ N) =
    cong (Types.T-Poly K′) (renNFTy-sound (ρ ↑ᵣ K′) N)
  renNFTy-sound ρ (N-Sub km≤ N) =
    cong (Types.T-Sub km≤) (renNFTy-sound ρ N)
  renNFTy-sound ρ N-End = refl
  renNFTy-sound ρ (N-Msg p NP NS) =
    cong₂ (Types.T-Msg p) (renNFProto′-sound ρ NP) (renNFTy-sound ρ NS)
  renNFTy-sound ρ (N-ProtoD N) =
    cong Types.T-ProtoD (renNFTy-sound ρ N)
