open import Data.Empty using (⊥-elim)
-- open import Data.Fin
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; s≤s; z≤n; s≤s⁻¹; _≟_)
open import Data.Nat.Properties using (≤-reflexive; ≤-refl; ≤-trans; n≤1+n; ⊔-comm; ⊔-assoc)
open import Data.Fin.Subset as Subset using (_⊆_)
open import Data.Fin.Subset.Properties using (⊆-refl; ⊆-antisym; _⊆?_)
-- open import Data.List
open import Data.Product
-- open import Data.Sum
open import Relation.Nullary using (¬_; Dec; yes; no; map′)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; cong-app; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

-- open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to ≅-refl)

open import Function using (const; _$_; case_of_)

module AlgorithmicInference where

open import Util
open import Kinds
open import Duality
open import Types
open import TypesDecidable
open import Subtyping
open import SubtypingProperties
open import AlgorithmicSubtyping
open import AlgorithmicSound



subtype-inference-var : ∀  {T : Ty Δ K} (NV₁ NV₂ : NormalVar T)
  → Dec (NV₁ ≡ NV₂)
subtype-inference-var NV-Var NV-Var = yes refl
subtype-inference-var (NV-Dual D-S x) (NV-Dual d x₁) = yes refl

subtype-inference : ∀ {T₁ T₂ : Ty Δ (KV pk m)}
  (N₁ : NormalTy T₁)(N₂ : NormalTy T₂)
  → Dec (N₁ <:ₜ N₂)
subtype-inference-<<:ₚ′ : ∀ {T₁ T₂ : Ty Δ KP}
  (N₁ : NormalProto′ T₁) (N₂ : NormalProto′ T₂)
  → Dec (N₁ <<:ₚ′[ injᵥ p ] N₂)
subtype-inference-<:ₚ′ : ∀ {T₁ T₂ : Ty Δ KP}
  (N₁ : NormalProto′ T₁) (N₂ : NormalProto′ T₂)
  → Dec (N₁ <:ₚ′ N₂)
subtype-inference-<<:ₚ :  ∀ {⊙} {T₁ T₂ : Ty Δ KP}
  (N₁ : NormalProto T₁) (N₂ : NormalProto T₂)
  → Dec (N₁ <<:ₚ[ ⊙ ] N₂)
subtype-inference-<:ₚ :  ∀ {T₁ T₂ : Ty Δ KP}
  (N₁ : NormalProto T₁) (N₂ : NormalProto T₂)
  → Dec (N₁ <:ₚ N₂)

subtype-inference {T₁ = T₁} {T₂} (N-Var NV) (N-Var NV₁)
  with ty-equal T₁ T₂
... | yes refl = map′ (λ{ refl → <:ₜ-var}) (λ{ <:ₜ-var → refl}) (subtype-inference-var NV NV₁)
... | no T₁≢T₂ = no (λ{ <:ₜ-var → T₁≢T₂ refl})
subtype-inference (N-Var NV) N-Base = no (λ())
subtype-inference (N-Var NV) (N-Arrow N₂ N₃) = no (λ ())
subtype-inference (N-Var NV) (N-Poly N₂) = no λ()
subtype-inference (N-Var NV) (N-Sub N₂) = no λ()
subtype-inference (N-Var NV) N-End = no λ()
subtype-inference (N-Var NV) (N-Msg p N N₂) = no λ()
subtype-inference (N-Var NV) (N-ProtoD N₂) = no λ()
subtype-inference N-Base (N-Var NV) = no λ()
subtype-inference N-Base N-Base = yes <:ₜ-base
subtype-inference N-Base (N-Arrow N₂ N₃) = no λ()
subtype-inference N-Base (N-Sub N₂) = no λ()
subtype-inference (N-Arrow N₁ N₂) (N-Var NV) = no λ()
subtype-inference (N-Arrow N₁ N₂) N-Base = no λ()
subtype-inference (N-Arrow {km = km₁} N₁ N₂) (N-Arrow {km = km₂} N₃ N₄)
  rewrite ≤p-irrelevant km₁ km₂
  with subtype-inference N₃ N₁
... | no ¬N₃<:N₁ = no (λ { (<:ₜ-arrow x x₁) → ¬N₃<:N₁ x})
... | yes N₃<:N₁ = map′ (<:ₜ-arrow N₃<:N₁) (λ{ (<:ₜ-arrow x x₁) → x₁}) (subtype-inference N₂ N₄)
subtype-inference (N-Arrow N₁ N₂) (N-Poly N₃) = no λ()
subtype-inference (N-Arrow N₁ N₂) (N-Sub N₃) = no λ()
subtype-inference (N-Arrow N₁ N₂) N-End = no λ()
subtype-inference (N-Arrow N₁ N₂) (N-Msg p N N₃) = no λ()
subtype-inference (N-Arrow N₁ N₂) (N-ProtoD N₃) = no λ()
subtype-inference (N-Poly N₁) (N-Var NV) = no λ()
subtype-inference (N-Poly N₁) (N-Arrow N₂ N₃) = no λ()
subtype-inference (N-Poly {K′₁} N₁) (N-Poly {K′₂} N₂)
  with eq-kind K′₁ K′₂
... | no K′₁≢K′₂ = no (λ{ (<:ₜ-poly x) → K′₁≢K′₂ refl})
... | yes refl = map′ <:ₜ-poly (λ{ (<:ₜ-poly x) → x}) (subtype-inference N₁ N₂)
subtype-inference (N-Poly N₁) (N-Sub N₂) = no λ()
subtype-inference (N-Poly N₁) (N-ProtoD N₂) = no λ()
subtype-inference (N-Sub N₁) (N-Var NV) = no λ()
subtype-inference (N-Sub N₁) N-Base = no λ()
subtype-inference (N-Sub N₁) (N-Arrow N₂ N₃) = no λ()
subtype-inference (N-Sub N₁) (N-Poly N₂) = no λ()
subtype-inference (N-Sub {pk₁}{m₁}{km≤ = km≤₁} N₁) (N-Sub {pk₂}{m₂}{km≤ = km≤₂} N₂)
  with eq-prekind pk₁ pk₂
... | no pk₁≢pk₂ = no (λ{ (<:ₜ-sub x) → pk₁≢pk₂ refl})
... | yes refl
  with eq-multiplicity m₁ m₂
... | no m₁≢m₂ = no (λ{ (<:ₜ-sub x) → m₁≢m₂ refl})
... | yes refl
  rewrite ≤k-irrelevant km≤₁ km≤₂
  with subtype-inference N₁ N₂
... | no ¬N₁<:N₂ = no (λ{ (<:ₜ-sub x) → ¬N₁<:N₂ x})
... | yes N₁<:N₂ = yes (<:ₜ-sub {km≤ = km≤₂} N₁<:N₂)
subtype-inference (N-Sub N₁) N-End = no λ()
subtype-inference (N-Sub N₁) (N-Msg p N N₂) = no λ()
subtype-inference (N-Sub N₁) (N-ProtoD N₂) = no λ()
subtype-inference N-End (N-Var NV) = no λ()
subtype-inference N-End (N-Arrow N₂ N₃) = no λ()
subtype-inference N-End (N-Sub N₂) = no λ()
subtype-inference N-End N-End = yes <:ₜ-end
subtype-inference (N-Msg p N N₁) (N-Var NV) = no λ()
subtype-inference (N-Msg p N N₁) (N-Arrow N₂ N₃) = no λ()
subtype-inference (N-Msg p N N₁) (N-Sub N₂) = no λ()
subtype-inference (N-Msg p₁ NP₁ NS₁) (N-Msg p₂ NP₂ NS₂)
  with polarity-equal p₁ p₂
... | no p₁≢p₂  = no (λ{ (<:ₜ-msg x x₁) → p₁≢p₂ refl})
... | yes refl
  with subtype-inference-<<:ₚ′ {p = p₂} NP₁ NP₂
... | no ¬NP₁<<:NP₂ = no (λ{ (<:ₜ-msg x x₁) → ¬NP₁<<:NP₂ x})
... | yes NP₁<<:NP₂ = map′ (<:ₜ-msg NP₁<<:NP₂) (λ{ (<:ₜ-msg x x₁) → x₁}) (subtype-inference NS₁ NS₂)
subtype-inference (N-ProtoD N₁) (N-Var NV) = no λ()
subtype-inference (N-ProtoD N₁) (N-Arrow N₂ N₃) = no λ()
subtype-inference (N-ProtoD N₁) (N-Poly N₂) = no λ()
subtype-inference (N-ProtoD N₁) (N-Sub N₂) = no λ()
subtype-inference (N-ProtoD N₁) (N-ProtoD N₂) = map′ <:ₜ-data (λ{ (<:ₜ-data x) → x}) (subtype-inference N₁ N₂)

subtype-inference-<<:ₚ′ {p = ⊕} N₁ N₂ = subtype-inference-<:ₚ′ N₂ N₁
subtype-inference-<<:ₚ′ {p = ⊝} N₁ N₂ = subtype-inference-<:ₚ′ N₁ N₂

subtype-inference-<:ₚ′ {T₁ = T-ProtoP {k = k₁} #c₁ ⊙₁ T₁} {T₂ = T-ProtoP {k = k₂} #c₂ ⊙₂ T₂} (N-ProtoP N) (N-ProtoP N₁)
  with k₁ ≟ k₂
... | no k₁≢k₂ = no (λ{ (<:ₚ′-proto x x₁) → k₁≢k₂ refl})
... | yes refl
  with ⊙-equal ⊙₁ ⊙₂
... | no ⊙₁≢⊙₂ = no (λ{ (<:ₚ′-proto x x₁) → ⊙₁≢⊙₂ refl})
... | yes refl
  with #c₁ ⊆? #c₂
... | no ¬c₁⊆c₂ = no (λ{ (<:ₚ′-proto x x₁) → ¬c₁⊆c₂ x})
... | yes c₁⊆c₂ = map′ (<:ₚ′-proto c₁⊆c₂) (λ{ (<:ₚ′-proto x x₁) → x₁}) (subtype-inference-<<:ₚ N N₁)
subtype-inference-<:ₚ′ (N-ProtoP N) (N-Up N₁) = no λ()
subtype-inference-<:ₚ′ (N-ProtoP N) N-Var = no λ()
subtype-inference-<:ₚ′ (N-Up N) (N-ProtoP N₁) = no λ()
subtype-inference-<:ₚ′ {T₁ = T-Up {pk₁} {m₁} T₁} {T-Up {pk₂} {m₂} T₂} (N-Up N) (N-Up N₁)
  with eq-prekind pk₁ pk₂
... | no pk₁≢pk₂ = no (λ{ (<:ₚ′-up x) → pk₁≢pk₂ refl})
... | yes refl
  with eq-multiplicity m₁ m₂
... | no m₁≢m₂ = no (λ { (<:ₚ′-up x) → m₁≢m₂ refl })
... | yes refl = map′ <:ₚ′-up (λ{ (<:ₚ′-up x) → x}) (subtype-inference N N₁)
subtype-inference-<:ₚ′ (N-Up N) N-Var = no λ()
subtype-inference-<:ₚ′ N-Var (N-ProtoP N) = no λ()
subtype-inference-<:ₚ′ N-Var (N-Up N) = no λ()
subtype-inference-<:ₚ′ {T₁ = T₁}{T₂ = T₂} N-Var N-Var
  with ty-equal T₁ T₂
... | no T₁≢T₂ = no (λ{ <:ₚ′-var → T₁≢T₂ refl})
... | yes refl = yes <:ₚ′-var

subtype-inference-<<:ₚ {⊙ = ⊕} N₁ N₂ = subtype-inference-<:ₚ N₁ N₂
subtype-inference-<<:ₚ {⊙ = ⊝} N₁ N₂ = subtype-inference-<:ₚ N₂ N₁
subtype-inference-<<:ₚ {⊙ = ⊘} {T₁} {T₂} N₁ N₂ = ty-equal T₁ T₂

subtype-inference-<:ₚ (N-Normal NP) (N-Normal NP₁) = map′ <:ₚ-plus (λ{ (<:ₚ-plus x) → x}) (subtype-inference-<:ₚ′ NP NP₁)
subtype-inference-<:ₚ (N-Normal NP) (N-Minus NP₁) = no λ()
subtype-inference-<:ₚ (N-Minus NP) (N-Normal NP₁) = no λ()
subtype-inference-<:ₚ (N-Minus NP) (N-Minus NP₁) = map′ <:ₚ-minus (λ{ (<:ₚ-minus x) → x}) (subtype-inference-<:ₚ′ NP₁ NP)
