open import Data.Empty using (⊥-elim)
-- open import Data.Fin
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; s≤s; z≤n; s≤s⁻¹; _≟_)
open import Data.Nat.Properties using (≤-reflexive; ≤-refl; ≤-trans; n≤1+n; ⊔-comm; ⊔-assoc)
open import Data.Fin.Subset as Subset using (_⊆_; _∪_; _∩_)
open import Data.Fin.Subset.Properties using (⊆-refl; ⊆-antisym; _⊆?_; p⊆p∪q; q⊆p∪q; p∩q⊆p; p∩q⊆q)
-- open import Data.List
open import Data.Product
-- open import Data.Sum
open import Relation.Nullary using (¬_; Dec; yes; no; map′)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; cong-app; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

-- open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to ≅-refl)

open import Function using (const; _$_; case_of_)

module AlgorithmicNFMerge where

open import Util
open import Kinds
open import Duality
open import Types hiding
  ( NormalTy
  ; NormalProto
  ; NormalProto′
  ; NormalVar
  ; N-Var
  ; N-Base
  ; N-Arrow
  ; N-Pair
  ; N-Poly
  ; N-Sub
  ; N-End
  ; N-Msg
  ; N-ProtoD
  ; N-ProtoP
  ; N-Up
  ; N-Normal
  ; N-Minus
  ; NV-Var
  ; NV-Dual
  ; nv-unique
  )
open import TypesDecidable
open import NormalTypes using
  ( NFProto
  ; NFProto′
  ; NFVar
  ; NFTy
  ; nfVarTy
  ; nfVarTy-injective
  ; nfProtoTy
  ; nfProto′Ty
  ; N-Var
  ; N-Base
  ; N-Arrow
  ; N-Pair
  ; N-Poly
  ; N-Sub
  ; N-End
  ; N-Msg
  ; N-ProtoD
  ; N-ProtoP
  ; N-Up
  ; N-Normal
  ; N-Minus
  ; NV-Var
  ; NV-Dual
  )
open import Subtyping
open import SubtypingProperties
open import AlgorithmicNFSubtyping
open import AlgorithmicNFSound

join-var : ∀ {K}
  (N₁ N₂ : NFVar Δ K)
  → Dec (N₁ ≡ N₂)
join-var N₁ N₂
  with ty-equal (nfVarTy N₁) (nfVarTy N₂)
... | no neq = no (λ eq → neq (cong nfVarTy eq))
... | yes eq = yes (nfVarTy-injective eq)

joinₜ : ∀ {pk m}
  (N₁ N₂ : NFTy Δ (KV pk m))
  → Dec (∃[ N ] (N₁ <:ₜ N × N₂ <:ₜ N))
mergeₚ′-join : ∀ (p : Polarity)
  (N₁ N₂ : NFProto′ Δ)
  → Dec (∃[ N ] (N₁ <<:ₚ′[ injᵥ p ] N × N₂ <<:ₚ′[ injᵥ p ] N))
mergeₚ′-meet : ∀ (p : Polarity)
  (N₁ N₂ : NFProto′ Δ)
  → Dec (∃[ N ] (N <<:ₚ′[ injᵥ p ] N₁ × N <<:ₚ′[ injᵥ p ] N₂))
mergeₚ-join : ∀ (v : Variance)
  (N₁ N₂ : NFProto Δ)
  → Dec (∃[ N ] (N₁ <<:ₚ[ v ] N × N₂ <<:ₚ[ v ] N))
mergeₚ-meet : ∀ (v : Variance)
  (N₁ N₂ : NFProto Δ)
  → Dec (∃[ N ] (N <<:ₚ[ v ] N₁ × N <<:ₚ[ v ] N₂))
joinₚ : ∀
  (N₁ N₂ : NFProto Δ)
  → Dec (∃[ N ] (N₁ <:ₚ N × N₂ <:ₚ N))
meetₚ : ∀
  (N₁ N₂ : NFProto Δ)
  → Dec (∃[ N ] (N <:ₚ N₁ × N <:ₚ N₂))
joinₚ′ : ∀
  (N₁ N₂ : NFProto′ Δ)
  → Dec (∃[ N ] (N₁ <:ₚ′ N × N₂ <:ₚ′ N))
meetₚ′ : ∀
  (N₁ N₂ : NFProto′ Δ)
  → Dec (∃[ N ] (N <:ₚ′ N₁ × N <:ₚ′ N₂))

meetₜ : ∀ {pk m}
  (N₁ N₂ : NFTy Δ (KV pk m))
  → Dec (∃[ N ] (N <:ₜ N₁ × N <:ₜ N₂))


joinₜ (N-Var NV) (N-Var NV₁)
  = map′ (λ{ refl → N-Var NV , <:ₜ-var , <:ₜ-var})
         (λ{ (_ , <:ₜ-var , <:ₜ-var) → refl})
         (join-var NV NV₁)
joinₜ (N-Var NV) N-Base = no (λ{ (_ , <:ₜ-var , ())})
joinₜ (N-Var NV) (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-var , ())})
joinₜ (N-Var NV) (N-Pair N₂ N₃) = no (λ{ (_ , <:ₜ-var , ())})
joinₜ (N-Var NV) (N-Poly _ N₂) = no (λ{ (_ , <:ₜ-var , ())})
joinₜ (N-Var NV) (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-var , ())})
joinₜ (N-Var NV) N-End = no (λ{ (_ , <:ₜ-var , ())})
joinₜ (N-Var NV) (N-Msg p N N₂) = no (λ{ (_ , <:ₜ-var , ())})
joinₜ (N-Var NV) (N-ProtoD N₂) = no (λ{ (_ , <:ₜ-var , ())})
joinₜ N-Base (N-Var NV) = no (λ{ (_ , <:ₜ-base , ())})
joinₜ N-Base N-Base = yes (N-Base , <:ₜ-base , <:ₜ-base)
joinₜ N-Base (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-base , ())})
joinₜ N-Base (N-Pair N₂ N₃) = no (λ{ (_ , <:ₜ-base , ())})
joinₜ N-Base (N-Poly _ N₂) = no (λ{ (_ , <:ₜ-base , ())})
joinₜ N-Base (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-base , ())})
joinₜ N-Base (N-ProtoD N₂) = no (λ{ (_ , <:ₜ-base , ())})
joinₜ (N-Arrow _ N₁ N₂) (N-Var NV) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow _ N₁ N₂) N-Base = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow _ N₁ N₂) (N-Pair N₃ N₄) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow km₁ N₁ N₂) (N-Arrow km₂ N₃ N₄)
  rewrite ≤p-irrelevant km₁ km₂
  with meetₜ N₃ N₁
... | no ¬meet = no λ{ (_ , <:ₜ-arrow <:₁ <:₂ , <:ₜ-arrow <:₃ <:₄) → ¬meet (_ , <:₃ , <:₁)}
... | yes (N₃⊓N₁ , <:₁ , <:₂)
    = map′ (λ{ (N₂⊔N₄ , <:₃ , <:₄) → N-Arrow km₂ N₃⊓N₁ N₂⊔N₄ , <:ₜ-arrow <:₂ <:₃ , <:ₜ-arrow <:₁ <:₄ })
           (λ{ (_ , <:ₜ-arrow <:₁ <:₃ , <:ₜ-arrow <:₂ <:₄) → _ , <:₃ , <:₄})
           (joinₜ N₂ N₄)
joinₜ (N-Arrow _ N₁ N₂) (N-Poly _ N₃) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow _ N₁ N₂) (N-Sub _ N₃) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow _ N₁ N₂) N-End = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow _ N₁ N₂) (N-Msg p N N₃) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow _ N₁ N₂) (N-ProtoD N₃) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
joinₜ (N-Pair N₁ N₂) (N-Var NV) = no (λ{ (_ , <:ₜ-pair _ _ , ())})
joinₜ (N-Pair N₁ N₂) N-Base = no (λ{ (_ , <:ₜ-pair _ _ , ())})
joinₜ (N-Pair N₁ N₂) (N-Arrow _ N₃ N₄) = no (λ{ (_ , <:ₜ-pair _ _ , ())})
joinₜ (N-Pair {pk₁ = pk₁} {pk₂ = pk₂} N₁ N₂) (N-Pair {pk₁ = pk₃} {pk₂ = pk₄} N₃ N₄)
  with eq-prekind pk₁ pk₃
... | no pk₁≢pk₃ = no (λ{ (_ , <:ₜ-pair _ _ , <:ₜ-pair _ _) → pk₁≢pk₃ refl})
... | yes refl
  with eq-prekind pk₂ pk₄
... | no pk₂≢pk₄ = no (λ{ (_ , <:ₜ-pair _ _ , <:ₜ-pair _ _) → pk₂≢pk₄ refl})
... | yes refl
  with joinₜ N₁ N₃
... | no ¬join = no λ{ (_ , <:ₜ-pair <:₁ <:₂ , <:ₜ-pair <:₃ <:₄) → ¬join (_ , <:₁ , <:₃) }
... | yes (N₁⊔N₃ , <:₁ , <:₂)
  = map′ (λ{ (N₂⊔N₄ , <:₃ , <:₄) → N-Pair N₁⊔N₃ N₂⊔N₄ , <:ₜ-pair <:₁ <:₃ , <:ₜ-pair <:₂ <:₄})
         (λ{ (_ , <:ₜ-pair <:₁ <:₃ , <:ₜ-pair <:₂ <:₄) → _ , <:₃ , <:₄ })
         (joinₜ N₂ N₄)
joinₜ (N-Pair N₁ N₂) (N-Poly _ N₃) = no (λ{ (_ , <:ₜ-pair _ _ , ())})
joinₜ (N-Pair N₁ N₂) (N-Sub _ N₃) = no (λ{ (_ , <:ₜ-pair _ _ , ())})
joinₜ (N-Pair N₁ N₂) (N-ProtoD N₃) = no (λ{ (_ , <:ₜ-pair _ _ , ())})
joinₜ (N-Poly _ N₁) (N-Var NV) = no (λ{ (_ , <:ₜ-poly _ , ())})
joinₜ (N-Poly _ N₁) N-Base = no (λ{ (_ , <:ₜ-poly _ , ())})
joinₜ (N-Poly _ N₁) (N-Pair N₂ N₃) = no (λ{ (_ , <:ₜ-poly _ , ())})
joinₜ (N-Poly _ N₁) (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-poly _ , ())})
joinₜ (N-Poly K₁′ N₁) (N-Poly K₂′ N₂)
  with eq-kind K₁′ K₂′
... | no K₁′≢K₂′ = no λ{ (_ , <:ₜ-poly <:₁ , <:ₜ-poly <:₂) → K₁′≢K₂′ refl}
... | yes refl = map′ (λ{ (N , <:₁ , <:₂) → N-Poly K₁′ N , <:ₜ-poly <:₁ , <:ₜ-poly <:₂})
                      (λ{ (_ , <:ₜ-poly <:₁ , <:ₜ-poly <:₂) → _ , <:₁ , <:₂})
                      (joinₜ N₁ N₂)
joinₜ (N-Poly _ N₁) (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-poly _ , ())})
joinₜ (N-Poly _ N₁) (N-ProtoD N₂) = no (λ{ (_ , <:ₜ-poly _ , ())})
joinₜ (N-Sub _ N₁) (N-Var NV) = no (λ{ (_ , <:ₜ-sub _ , ())})
joinₜ (N-Sub _ N₁) N-Base = no (λ{ (_ , <:ₜ-sub _ , ())})
joinₜ (N-Sub _ N₁) (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-sub _ , ())})
joinₜ (N-Sub _ N₁) (N-Poly _ N₂) = no (λ{ (_ , <:ₜ-sub _ , ())})
joinₜ (N-Sub {pk₁}{m₁} km≤₁ N₁) (N-Sub {pk₂}{m₂} km≤₂ N₂)
  with eq-prekind pk₁ pk₂
... | no pk₁≢pk₂ = no (λ{ (_ , <:ₜ-sub x₁ , <:ₜ-sub x₂) → pk₁≢pk₂ refl})
... | yes refl
  with eq-multiplicity m₁ m₂
... | no m₁≢m₂ = no (λ{ (_ , <:ₜ-sub x₁ , <:ₜ-sub x₂) → m₁≢m₂ refl})
... | yes refl
  rewrite ≤k-irrelevant km≤₁ km≤₂
  = map′ (λ{ (N , <:₁ , <:₂) → N-Sub km≤₂ N , <:ₜ-sub <:₁ , <:ₜ-sub <:₂})
         (λ{ (_ , <:ₜ-sub <:₁ , <:ₜ-sub <:₂) → _ , <:₁ , <:₂ })
         (joinₜ N₁ N₂)
joinₜ (N-Sub _ N₁) (N-Pair N₂ N₃) = no (λ{ (_ , <:ₜ-sub _ , ())})
joinₜ (N-Sub _ N₁) N-End = no (λ{ (_ , <:ₜ-sub _ , ())})
joinₜ (N-Sub _ N₁) (N-Msg p N N₂) = no (λ{ (_ , <:ₜ-sub _ , ())})
joinₜ (N-Sub _ N₁) (N-ProtoD N₂) = no (λ{ (_ , <:ₜ-sub _ , ())})
joinₜ N-End (N-Var NV) = no (λ{ (_ , <:ₜ-end , ())})
joinₜ N-End (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-end , ())})
joinₜ N-End (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-end , ())})
joinₜ N-End N-End = yes (N-End , <:ₜ-end , <:ₜ-end)
joinₜ (N-Msg p N N₁) (N-Var NV) = no (λ{ (_ , <:ₜ-msg _ _ , ())})
joinₜ (N-Msg p N N₁) (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-msg _ _ , ())})
joinₜ (N-Msg p N N₁) (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-msg _ _ , ())})
joinₜ (N-Msg p₁ NP₁ NS₁) (N-Msg p₂ NP₂ NS₂)
  with polarity-equal p₁ p₂
... | no p≢p₁ = no (λ{ (_ , <:ₜ-msg x <:₁ , <:ₜ-msg x₁ <:₂) → p≢p₁ refl})
... | yes refl
  with mergeₚ′-join p₁ NP₁ NP₂
... | no ¬merge = no λ{ (_ , <:ₜ-msg {NP₁ = NP₁} x <:₁ , <:ₜ-msg {NP₁ = NP₂} x₁ <:₂) → ¬merge (_ , x , x₁) }
... | yes (NP , <:₁ , <:₂)
  = map′ (λ{ (NS , <:ₜ₁ , <:ₜ₂) → N-Msg p₁ NP NS , <:ₜ-msg <:₁ <:ₜ₁ , <:ₜ-msg <:₂ <:ₜ₂})
         (λ{ (_ , <:ₜ-msg x <:ₜ₁ , <:ₜ-msg x₁ <:ₜ₂) → _ , <:ₜ₁ , <:ₜ₂})
         (joinₜ NS₁ NS₂)
joinₜ (N-ProtoD N₁) (N-Var NV) = no (λ{ (_ , <:ₜ-data _ , ())})
joinₜ (N-ProtoD N₁) N-Base = no (λ{ (_ , <:ₜ-data _ , ())})
joinₜ (N-ProtoD N₁) (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-data _ , ())})
joinₜ (N-ProtoD N₁) (N-Pair N₂ N₃) = no (λ{ (_ , <:ₜ-data _ , ())})
joinₜ (N-ProtoD N₁) (N-Poly _ N₂) = no (λ{ (_ , <:ₜ-data _ , ())})
joinₜ (N-ProtoD N₁) (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-data _ , ())})
joinₜ (N-ProtoD N₁) (N-ProtoD N₂)
  = map′ (λ{ (N , <:₁ , <:₂) → N-ProtoD N , <:ₜ-data <:₁ , <:ₜ-data <:₂ })
         (λ{ (_ , <:ₜ-data <:₁ , <:ₜ-data <:₂) → _ , <:₁ , <:₂})
         (joinₜ N₁ N₂)

mergeₚ′-join ⊕ N₁ N₂ = meetₚ′ N₁ N₂
mergeₚ′-join ⊝ N₁ N₂ = joinₚ′ N₁ N₂

mergeₚ′-meet ⊕ N₁ N₂ = joinₚ′ N₁ N₂
mergeₚ′-meet ⊝ N₁ N₂ = meetₚ′ N₁ N₂

joinₚ′ (N-ProtoP {k = k₁} #c₁ ⊙₁ N₁) (N-ProtoP {k = k₂} #c₂ ⊙₂ N₂)
  with k₁ ≟ k₂
... | no k₁≢k₂ = no (λ{ (_ , <:ₚ′-proto x x₁ , <:ₚ′-proto x₂ x₃) → k₁≢k₂ refl})
... | yes refl
  with ⊙-equal ⊙₁ ⊙₂
... | no ⊙₁≢⊙₂ = no (λ{ (_ , <:ₚ′-proto x x₁ , <:ₚ′-proto x₂ x₃) → ⊙₁≢⊙₂ refl})
... | yes refl
  = map′ (λ{ (N , <:₁ , <:₂) → N-ProtoP (#c₁ ∪ #c₂) ⊙₁ N , <:ₚ′-proto (p⊆p∪q #c₂) <:₁ , <:ₚ′-proto (q⊆p∪q #c₁ #c₂) <:₂ })
         (λ{ (_ , <:ₚ′-proto x x₁ , <:ₚ′-proto x₂ x₃) → _ , x₁ , x₃})
         (mergeₚ-join ⊙₁ N₁ N₂)
joinₚ′ (N-ProtoP _ _ N) (N-Up N₁) = no (λ{ (_ , <:ₚ′-proto _ _ , ()) })
joinₚ′ (N-ProtoP _ _ N) (N-Var x) = no (λ{ (_ , <:ₚ′-proto _ _ , ()) })
joinₚ′ (N-Up N) (N-ProtoP _ _ N₁) = no (λ{ (_ , <:ₚ′-up _ , ()) })
joinₚ′ (N-Up {pk = pk₁} {m = m₁} N) (N-Up {pk = pk₂} {m = m₂} N₁)
  with eq-prekind pk₁ pk₂
... | no pk₁≢pk₂ = no λ{ (_ , <:ₚ′-up x , <:ₚ′-up x₁) → pk₁≢pk₂ refl }
... | yes refl
  with eq-multiplicity m₁ m₂
... | no m₁≢m₂ = no λ{ (_ , <:ₚ′-up x , <:ₚ′-up x₁) → m₁≢m₂ refl }
... | yes refl = map′ (λ{ (N , <:₁ , <:₂) → N-Up N , <:ₚ′-up <:₁ , <:ₚ′-up <:₂})
                      (λ{ (_ , <:ₚ′-up x , <:ₚ′-up x₁) → _ , x , x₁})
                      (joinₜ N N₁)
joinₚ′ (N-Up N) (N-Var x) = no (λ{ (_ , <:ₚ′-up _ , ()) })
joinₚ′ (N-Var x) (N-ProtoP _ _ N) = no (λ{ (_ , <:ₚ′-var , ()) })
joinₚ′ (N-Var x) (N-Up N) = no (λ{ (_ , <:ₚ′-var , ()) })
joinₚ′ (N-Var x) (N-Var y)
  with ty-equal (nfProto′Ty (N-Var x)) (nfProto′Ty (N-Var y))
... | no neq = no (λ{ (_ , <:ₚ′-var , <:ₚ′-var) → neq refl})
... | yes refl = yes (_ , <:ₚ′-var , <:ₚ′-var)

meetₚ′ (N-ProtoP {k = k₁} #c₁ ⊙₁ N₁) (N-ProtoP {k = k₂} #c₂ ⊙₂ N₂)
  with k₁ ≟ k₂
... | no k₁≢k₂ = no (λ{ (_ , <:ₚ′-proto x x₁ , <:ₚ′-proto x₂ x₃) → k₁≢k₂ refl})
... | yes refl
  with ⊙-equal ⊙₁ ⊙₂
... | no ⊙₁≢⊙₂ = no (λ{ (_ , <:ₚ′-proto x x₁ , <:ₚ′-proto x₂ x₃) → ⊙₁≢⊙₂ refl})
... | yes refl
  = map′ (λ{ (N , <:₁ , <:₂) → N-ProtoP (#c₁ ∩ #c₂) ⊙₁ N , <:ₚ′-proto (p∩q⊆p #c₁ #c₂) <:₁ , <:ₚ′-proto (p∩q⊆q #c₁ #c₂) <:₂ })
         (λ{ (_ , <:ₚ′-proto x x₁ , <:ₚ′-proto x₂ x₃) → _ , x₁ , x₃})
         (mergeₚ-meet ⊙₁ N₁ N₂)
meetₚ′ (N-ProtoP _ _ N) (N-Up N₁) = no (λ{ (_ , <:ₚ′-proto _ _ , ()) })
meetₚ′ (N-ProtoP _ _ N) (N-Var x) = no (λ{ (_ , <:ₚ′-proto _ _ , ()) })
meetₚ′ (N-Up N) (N-ProtoP _ _ N₁) = no (λ{ (_ , <:ₚ′-up _ , ()) })
meetₚ′ (N-Up {pk = pk₁} {m = m₁} N) (N-Up {pk = pk₂} {m = m₂} N₁)
  with eq-prekind pk₁ pk₂
... | no pk₁≢pk₂ = no λ{ (_ , <:ₚ′-up x , <:ₚ′-up x₁) → pk₁≢pk₂ refl }
... | yes refl
  with eq-multiplicity m₁ m₂
... | no m₁≢m₂ = no λ{ (_ , <:ₚ′-up x , <:ₚ′-up x₁) → m₁≢m₂ refl }
... | yes refl = map′ (λ{ (N , <:₁ , <:₂) → N-Up N , <:ₚ′-up <:₁ , <:ₚ′-up <:₂})
                      (λ{ (_ , <:ₚ′-up x , <:ₚ′-up x₁) → _ , x , x₁})
                      (meetₜ N N₁)
meetₚ′ (N-Up N) (N-Var x) = no (λ{ (_ , <:ₚ′-up _ , ()) })
meetₚ′ (N-Var x) (N-ProtoP _ _ N) = no (λ{ (_ , <:ₚ′-var , ()) })
meetₚ′ (N-Var x) (N-Up N) = no (λ{ (_ , <:ₚ′-var , ()) })
meetₚ′ (N-Var x) (N-Var y)
  with ty-equal (nfProto′Ty (N-Var x)) (nfProto′Ty (N-Var y))
... | no neq = no (λ{ (_ , <:ₚ′-var , <:ₚ′-var) → neq refl})
... | yes refl = yes (_ , <:ₚ′-var , <:ₚ′-var)

mergeₚ-join ⊕ N₁ N₂ = joinₚ N₁ N₂
mergeₚ-join ⊝ N₁ N₂ = meetₚ N₁ N₂
mergeₚ-join ⊘ N₁ N₂ = map′ (λ eq → N₁ , refl , sym eq) (λ{ (_ , ≡₁ , ≡₂) → trans ≡₁ (sym ≡₂) }) (ty-equal (nfProtoTy N₁) (nfProtoTy N₂))

mergeₚ-meet ⊕ N₁ N₂ = meetₚ N₁ N₂
mergeₚ-meet ⊝ N₁ N₂ = joinₚ N₁ N₂
mergeₚ-meet ⊘ N₁ N₂ = map′ (λ eq → N₁ , refl , eq) (λ{(_ , ≡₁ , ≡₂) → trans (sym ≡₁) ≡₂ } ) (ty-equal (nfProtoTy N₁) (nfProtoTy N₂))

joinₚ (N-Normal NP) (N-Normal NP₁) = map′ (λ{ (N , <:₁ , <:₂) → N-Normal N , <:ₚ-plus <:₁ , <:ₚ-plus <:₂ })
                                          (λ{ (_ , <:ₚ-plus x , <:ₚ-plus x₁) → _ , x , x₁ })
                                          (joinₚ′ NP NP₁)
joinₚ (N-Normal NP) (N-Minus NP₁) = no λ{ (_ , <:ₚ-plus x , ()) }
joinₚ (N-Minus NP) (N-Normal NP₁) = no λ{ (_ , <:ₚ-minus x , ()) }
joinₚ (N-Minus NP) (N-Minus NP₁) = map′ (λ{ (N , <:₁ , <:₂) → N-Minus N , <:ₚ-minus <:₁ , <:ₚ-minus <:₂ })
                                        (λ{ (_ , <:ₚ-minus x , <:ₚ-minus x₁) → _ , x , x₁ })
                                        (meetₚ′ NP NP₁)

meetₚ (N-Normal NP) (N-Normal NP₁) = map′ (λ{ (N , <:₁ , <:₂) → N-Normal N , <:ₚ-plus <:₁ , <:ₚ-plus <:₂ })
                                          (λ{ (_ , <:ₚ-plus x , <:ₚ-plus x₁) → _ , x , x₁ })
                                          (meetₚ′ NP NP₁)
meetₚ (N-Normal NP) (N-Minus NP₁) = no λ{ (_ , <:ₚ-plus x , ()) }
meetₚ (N-Minus NP) (N-Normal NP₁) = no λ{ (_ , <:ₚ-minus x , ()) }
meetₚ (N-Minus NP) (N-Minus NP₁) = map′ (λ{ (N , <:₁ , <:₂) → N-Minus N , <:ₚ-minus <:₁ , <:ₚ-minus <:₂ })
                                        (λ{ (_ , <:ₚ-minus x , <:ₚ-minus x₁) → _ , x , x₁ })
                                        (joinₚ′ NP NP₁)

meetₜ (N-Var NV) (N-Var NV₁)
  = map′ (λ{ refl → N-Var NV , <:ₜ-var , <:ₜ-var})
         (λ{ (_ , <:ₜ-var , <:ₜ-var) → refl})
         (join-var NV NV₁)
meetₜ (N-Var NV) N-Base = no (λ{ (_ , <:ₜ-var , ())})
meetₜ (N-Var NV) (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-var , ())})
meetₜ (N-Var NV) (N-Pair N₂ N₃) = no (λ{ (_ , <:ₜ-var , ())})
meetₜ (N-Var NV) (N-Poly _ N₂) = no (λ{ (_ , <:ₜ-var , ())})
meetₜ (N-Var NV) (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-var , ())})
meetₜ (N-Var NV) N-End = no (λ{ (_ , <:ₜ-var , ())})
meetₜ (N-Var NV) (N-Msg p N N₂) = no (λ{ (_ , <:ₜ-var , ())})
meetₜ (N-Var NV) (N-ProtoD N₂) = no (λ{ (_ , <:ₜ-var , ())})
meetₜ N-Base (N-Var NV) = no (λ{ (_ , <:ₜ-base , ())})
meetₜ N-Base N-Base = yes (N-Base , <:ₜ-base , <:ₜ-base)
meetₜ N-Base (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-base , ())})
meetₜ N-Base (N-Pair N₂ N₃) = no (λ{ (_ , <:ₜ-base , ())})
meetₜ N-Base (N-Poly _ N₂) = no (λ{ (_ , <:ₜ-base , ())})
meetₜ N-Base (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-base , ())})
meetₜ N-Base (N-ProtoD N₂) = no (λ{ (_ , <:ₜ-base , ())})
meetₜ (N-Arrow _ N₁ N₂) (N-Var NV) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
meetₜ (N-Arrow _ N₁ N₂) N-Base = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
meetₜ (N-Arrow _ N₁ N₂) (N-Pair N₃ N₄) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
meetₜ (N-Arrow km₁ N₁ N₂) (N-Arrow km₂ N₃ N₄)
  rewrite ≤p-irrelevant km₁ km₂
  with joinₜ N₃ N₁
... | no ¬meet = no λ{ (_ , <:ₜ-arrow <:₁ <:₂ , <:ₜ-arrow <:₃ <:₄) → ¬meet (_ , <:₃ , <:₁)}
... | yes (N₃⊓N₁ , <:₁ , <:₂)
    = map′ (λ{ (N₂⊔N₄ , <:₃ , <:₄) → N-Arrow km₂ N₃⊓N₁ N₂⊔N₄ , <:ₜ-arrow <:₂ <:₃ , <:ₜ-arrow <:₁ <:₄ })
           (λ{ (_ , <:ₜ-arrow <:₁ <:₃ , <:ₜ-arrow <:₂ <:₄) → _ , <:₃ , <:₄})
           (meetₜ N₂ N₄)
meetₜ (N-Arrow _ N₁ N₂) (N-Poly _ N₃) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
meetₜ (N-Arrow _ N₁ N₂) (N-Sub _ N₃) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
meetₜ (N-Arrow _ N₁ N₂) N-End = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
meetₜ (N-Arrow _ N₁ N₂) (N-Msg p N N₃) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
meetₜ (N-Arrow _ N₁ N₂) (N-ProtoD N₃) = no (λ{ (_ , <:ₜ-arrow _ _ , ())})
meetₜ (N-Pair N₁ N₂) (N-Var NV) = no (λ{ (_ , <:ₜ-pair _ _ , ())})
meetₜ (N-Pair N₁ N₂) N-Base = no (λ{ (_ , <:ₜ-pair _ _ , ())})
meetₜ (N-Pair N₁ N₂) (N-Arrow _ N₃ N₄) = no (λ{ (_ , <:ₜ-pair _ _ , ())})
meetₜ (N-Pair {pk₁ = pk₁} {pk₂ = pk₂} N₁ N₂) (N-Pair {pk₁ = pk₃} {pk₂ = pk₄} N₃ N₄)
  with eq-prekind pk₁ pk₃
... | no pk₁≢pk₃ = no (λ{ (_ , <:ₜ-pair _ _ , <:ₜ-pair _ _) → pk₁≢pk₃ refl})
... | yes refl
  with eq-prekind pk₂ pk₄
... | no pk₂≢pk₄ = no (λ{ (_ , <:ₜ-pair _ _ , <:ₜ-pair _ _) → pk₂≢pk₄ refl})
... | yes refl
  with meetₜ N₁ N₃
... | no ¬meet = no λ{ (_ , <:ₜ-pair <:₁ <:₂ , <:ₜ-pair <:₃ <:₄) → ¬meet (_ , <:₁ , <:₃) }
... | yes (N₁⊓N₃ , <:₁ , <:₂)
  = map′ (λ{ (N₂⊓N₄ , <:₃ , <:₄) → N-Pair N₁⊓N₃ N₂⊓N₄ , <:ₜ-pair <:₁ <:₃ , <:ₜ-pair <:₂ <:₄})
         (λ{ (_ , <:ₜ-pair <:₁ <:₃ , <:ₜ-pair <:₂ <:₄) → _ , <:₃ , <:₄ })
         (meetₜ N₂ N₄)
meetₜ (N-Pair N₁ N₂) (N-Poly _ N₃) = no (λ{ (_ , <:ₜ-pair _ _ , ())})
meetₜ (N-Pair N₁ N₂) (N-Sub _ N₃) = no (λ{ (_ , <:ₜ-pair _ _ , ())})
meetₜ (N-Pair N₁ N₂) (N-ProtoD N₃) = no (λ{ (_ , <:ₜ-pair _ _ , ())})
meetₜ (N-Poly _ N₁) (N-Var NV) = no (λ{ (_ , <:ₜ-poly _ , ())})
meetₜ (N-Poly _ N₁) N-Base = no (λ{ (_ , <:ₜ-poly _ , ())})
meetₜ (N-Poly _ N₁) (N-Pair N₂ N₃) = no (λ{ (_ , <:ₜ-poly _ , ())})
meetₜ (N-Poly _ N₁) (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-poly _ , ())})
meetₜ (N-Poly K₁′ N₁) (N-Poly K₂′ N₂)
  with eq-kind K₁′ K₂′
... | no K₁′≢K₂′ = no λ{ (_ , <:ₜ-poly <:₁ , <:ₜ-poly <:₂) → K₁′≢K₂′ refl}
... | yes refl = map′ (λ{ (N , <:₁ , <:₂) → N-Poly K₁′ N , <:ₜ-poly <:₁ , <:ₜ-poly <:₂})
                      (λ{ (_ , <:ₜ-poly <:₁ , <:ₜ-poly <:₂) → _ , <:₁ , <:₂})
                      (meetₜ N₁ N₂)
meetₜ (N-Poly _ N₁) (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-poly _ , ())})
meetₜ (N-Poly _ N₁) (N-ProtoD N₂) = no (λ{ (_ , <:ₜ-poly _ , ())})
meetₜ (N-Sub _ N₁) (N-Var NV) = no (λ{ (_ , <:ₜ-sub _ , ())})
meetₜ (N-Sub _ N₁) N-Base = no (λ{ (_ , <:ₜ-sub _ , ())})
meetₜ (N-Sub _ N₁) (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-sub _ , ())})
meetₜ (N-Sub _ N₁) (N-Poly _ N₂) = no (λ{ (_ , <:ₜ-sub _ , ())})
meetₜ (N-Sub {pk₁}{m₁} km≤₁ N₁) (N-Sub {pk₂}{m₂} km≤₂ N₂)
  with eq-prekind pk₁ pk₂
... | no pk₁≢pk₂ = no (λ{ (_ , <:ₜ-sub x₁ , <:ₜ-sub x₂) → pk₁≢pk₂ refl})
... | yes refl
  with eq-multiplicity m₁ m₂
... | no m₁≢m₂ = no (λ{ (_ , <:ₜ-sub x₁ , <:ₜ-sub x₂) → m₁≢m₂ refl})
... | yes refl
  rewrite ≤k-irrelevant km≤₁ km≤₂
  = map′ (λ{ (N , <:₁ , <:₂) → N-Sub km≤₂ N , <:ₜ-sub <:₁ , <:ₜ-sub <:₂})
         (λ{ (_ , <:ₜ-sub <:₁ , <:ₜ-sub <:₂) → _ , <:₁ , <:₂ })
         (meetₜ N₁ N₂)
meetₜ (N-Sub _ N₁) (N-Pair N₂ N₃) = no (λ{ (_ , <:ₜ-sub _ , ())})
meetₜ (N-Sub _ N₁) N-End = no (λ{ (_ , <:ₜ-sub _ , ())})
meetₜ (N-Sub _ N₁) (N-Msg p N N₂) = no (λ{ (_ , <:ₜ-sub _ , ())})
meetₜ (N-Sub _ N₁) (N-ProtoD N₂) = no (λ{ (_ , <:ₜ-sub _ , ())})
meetₜ N-End (N-Var NV) = no (λ{ (_ , <:ₜ-end , ())})
meetₜ N-End (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-end , ())})
meetₜ N-End (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-end , ())})
meetₜ N-End N-End = yes (N-End , <:ₜ-end , <:ₜ-end)
meetₜ (N-Msg p N N₁) (N-Var NV) = no (λ{ (_ , <:ₜ-msg _ _ , ())})
meetₜ (N-Msg p N N₁) (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-msg _ _ , ())})
meetₜ (N-Msg p N N₁) (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-msg _ _ , ())})
meetₜ (N-Msg p₁ NP₁ NS₁) (N-Msg p₂ NP₂ NS₂)
  with polarity-equal p₁ p₂
... | no p≢p₁ = no (λ{ (_ , <:ₜ-msg x <:₁ , <:ₜ-msg x₁ <:₂) → p≢p₁ refl})
... | yes refl
  with mergeₚ′-meet p₁ NP₁ NP₂
... | no ¬merge = no λ{ (_ , <:ₜ-msg {NP₁ = NP₁} x <:₁ , <:ₜ-msg {NP₁ = NP₂} x₁ <:₂) → ¬merge (_ , x , x₁) }
... | yes (NP , <:₁ , <:₂)
  = map′ (λ{ (NS , <:ₜ₁ , <:ₜ₂) → N-Msg p₁ NP NS , <:ₜ-msg <:₁ <:ₜ₁ , <:ₜ-msg <:₂ <:ₜ₂})
         (λ{ (_ , <:ₜ-msg x <:ₜ₁ , <:ₜ-msg x₁ <:ₜ₂) → _ , <:ₜ₁ , <:ₜ₂})
         (meetₜ NS₁ NS₂)
meetₜ (N-ProtoD N₁) (N-Var NV) = no (λ{ (_ , <:ₜ-data _ , ())})
meetₜ (N-ProtoD N₁) N-Base = no (λ{ (_ , <:ₜ-data _ , ())})
meetₜ (N-ProtoD N₁) (N-Arrow _ N₂ N₃) = no (λ{ (_ , <:ₜ-data _ , ())})
meetₜ (N-ProtoD N₁) (N-Pair N₂ N₃) = no (λ{ (_ , <:ₜ-data _ , ())})
meetₜ (N-ProtoD N₁) (N-Poly _ N₂) = no (λ{ (_ , <:ₜ-data _ , ())})
meetₜ (N-ProtoD N₁) (N-Sub _ N₂) = no (λ{ (_ , <:ₜ-data _ , ())})
meetₜ (N-ProtoD N₁) (N-ProtoD N₂)
  = map′ (λ{ (N , <:₁ , <:₂) → N-ProtoD N , <:ₜ-data <:₁ , <:ₜ-data <:₂ })
         (λ{ (_ , <:ₜ-data <:₁ , <:ₜ-data <:₂) → _ , <:₁ , <:₂})
         (meetₜ N₁ N₂)
