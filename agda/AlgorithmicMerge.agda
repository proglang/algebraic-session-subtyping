open import Data.Empty using (⊥-elim)
-- open import Data.Fin
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; s≤s; z≤n; s≤s⁻¹; _≟_)
open import Data.Nat.Properties using (≤-reflexive; ≤-refl; ≤-trans; n≤1+n; ⊔-comm; ⊔-assoc)
open import Data.Fin.Subset as Subset using (_⊆_; _∪_; _∩_)
open import Data.Fin.Subset.Properties using (⊆-refl; ⊆-antisym; _⊆?_; p⊆p∪q; q⊆p∪q)
-- open import Data.List
open import Data.Product
-- open import Data.Sum
open import Relation.Nullary using (¬_; Dec; yes; no; map′)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; cong-app; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

-- open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to ≅-refl)

open import Function using (const; _$_; case_of_)

module AlgorithmicMerge where

open import Util
open import Kinds
open import Duality
open import Types
open import TypesDecidable
open import Subtyping
open import SubtypingProperties
open import AlgorithmicSubtyping
open import AlgorithmicSound

join-var : ∀ {T₁ T₂ : Ty Δ (KV pk m)}
  (N₁ : NormalVar T₁)(N₂ : NormalVar T₂)
  → Dec (∃[ T ] T₁ ≡ T × T₂ ≡ T)
join-var {T₁ = T₁}{T₂} N₁ N₂
  with ty-equal T₁ T₂
... | no T₁≢T₂ = no (λ{ (T , ≡₁ , ≡₂) → T₁≢T₂ (trans ≡₁ (sym ≡₂))})
... | yes refl = yes (T₁ , refl , refl)

joinₜ : ∀ {T₁ T₂ : Ty Δ (KV pk m)}
  (N₁ : NormalTy T₁)(N₂ : NormalTy T₂)
  → Dec (∃[ T ] Σ (NormalTy T) λ N → N₁ <:ₜ N × N₂ <:ₜ N)
mergeₚ′ : ∀ (p : Polarity) {T₁ T₂ : Ty Δ KP}
  (N₁ : NormalProto′ T₁)(N₂ : NormalProto′ T₂)
  → Dec (∃[ T ] Σ (NormalProto′ T) λ N → N₁ <<:ₚ′[ injᵥ p ] N × N₂ <<:ₚ′[ injᵥ p ] N)
mergeₚ : ∀ (v : Variance) {T₁ T₂ : Ty Δ KP}
  (N₁ : NormalProto T₁)(N₂ : NormalProto T₂)
  → Dec (∃[ T ] Σ (NormalProto T) λ N → N₁ <<:ₚ[ v ] N × N₂ <<:ₚ[ v ] N)
joinₚ : ∀ {T₁ T₂ : Ty Δ KP}
  (N₁ : NormalProto T₁)(N₂ : NormalProto T₂)
  → Dec (∃[ T ] Σ (NormalProto T) λ N → N₁ <:ₚ N × N₂ <:ₚ N)
meetₚ : ∀ {T₁ T₂ : Ty Δ KP}
  (N₁ : NormalProto T₁)(N₂ : NormalProto T₂)
  → Dec (∃[ T ] Σ (NormalProto T) λ N → N <:ₚ N₁ × N <:ₚ N₂)
joinₚ′ : ∀ {T₁ T₂ : Ty Δ KP}
  (N₁ : NormalProto′ T₁)(N₂ : NormalProto′ T₂)
  → Dec (∃[ T ] Σ (NormalProto′ T) λ N → N₁ <:ₚ′ N × N₂ <:ₚ′ N)
meetₚ′ : ∀ {T₁ T₂ : Ty Δ KP}
  (N₁ : NormalProto′ T₁)(N₂ : NormalProto′ T₂)
  → Dec (∃[ T ] Σ (NormalProto′ T) λ N → N <:ₚ′ N₁ × N <:ₚ′ N₂)

meetₜ : ∀ {T₁ T₂ : Ty Δ (KV pk m)}
  (N₁ : NormalTy T₁)(N₂ : NormalTy T₂)
  → Dec (∃[ T ] Σ (NormalTy T) λ N → N <:ₜ N₁ × N <:ₜ N₂)


joinₜ (N-Var NV) (N-Var NV₁)
  = map′ (λ{ (T , refl , refl) → case nv-unique NV NV₁ of λ{ refl → T , (N-Var NV , <:ₜ-var , <:ₜ-var)}})
         (λ{ (T₁ , N , <:ₜ-var , <:ₜ-var) → _ , refl , refl})
         (join-var NV NV₁)
joinₜ (N-Var NV) N-Base = no (λ{ (T₁ , N , <:ₜ-var , ())})
joinₜ (N-Var NV) (N-Arrow N₂ N₃) = no (λ{ (T₁ , N , <:ₜ-var , ())})
joinₜ (N-Var NV) (N-Poly N₂) = no (λ{ (T₁ , N , <:ₜ-var , ())})
joinₜ (N-Var NV) (N-Sub N₂) = no (λ{ (T₁ , N , <:ₜ-var , ())})
joinₜ (N-Var NV) N-End = no (λ{ (T₁ , N , <:ₜ-var , ())})
joinₜ (N-Var NV) (N-Msg p N N₂) = no (λ{ (T₁ , N , <:ₜ-var , ())})
joinₜ (N-Var NV) (N-ProtoD N₂) = no (λ{ (T₁ , N , <:ₜ-var , ())})
joinₜ N-Base (N-Var NV) = no (λ{ (T₁ , N , <:ₜ-base , ())})
joinₜ N-Base N-Base = yes (T-Base , N-Base , <:ₜ-base , <:ₜ-base)
joinₜ N-Base (N-Arrow N₂ N₃) = no (λ{ (T₁ , N , <:ₜ-base , ())})
joinₜ N-Base (N-Sub N₂) = no (λ{ (T₁ , N , <:ₜ-base , ())})
joinₜ (N-Arrow N₁ N₂) (N-Var NV) = no (λ{ (T₁ , N , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow N₁ N₂) N-Base = no (λ{ (T₁ , N , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow {km = km₁} N₁ N₂) (N-Arrow {km = km₂} N₃ N₄)
  rewrite ≤p-irrelevant km₁ km₂
  with meetₜ N₃ N₁
... | no ¬meet = no λ{ (T , N , <:ₜ-arrow <:₁ <:₂ , <:ₜ-arrow <:₃ <:₄) → ¬meet (_ , _ , <:₃ , <:₁)}
... | yes (T₅ , N₃⊓N₁ , <:₁ , <:₂)
    = map′ (λ{ (T₆ , N₂⊔N₄ , <:₃ , <:₄) → T-Arrow km₂ T₅ T₆ , ((N-Arrow N₃⊓N₁ N₂⊔N₄) , (<:ₜ-arrow <:₂ <:₃) , <:ₜ-arrow <:₁ <:₄)})
           (λ{ (T , N , <:ₜ-arrow <:₁ <:₃ , <:ₜ-arrow <:₂ <:₄) → _ , _ , <:₃ , <:₄})
           (joinₜ N₂ N₄)
joinₜ (N-Arrow N₁ N₂) (N-Poly N₃) = no (λ{ (T₁ , N , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow N₁ N₂) (N-Sub N₃) = no (λ{ (T₁ , N , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow N₁ N₂) N-End = no (λ{ (T₁ , N , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow N₁ N₂) (N-Msg p N N₃) = no (λ{ (T₁ , N , <:ₜ-arrow _ _ , ())})
joinₜ (N-Arrow N₁ N₂) (N-ProtoD N₃) = no (λ{ (T₁ , N , <:ₜ-arrow _ _ , ())})
joinₜ (N-Poly N₁) (N-Var NV) = no (λ{ (T₁ , N , <:ₜ-poly _ , ())})
joinₜ (N-Poly N₁) (N-Arrow N₂ N₃) = no (λ{ (T₁ , N , <:ₜ-poly _ , ())})
joinₜ (N-Poly {K₁′} N₁) (N-Poly {K₂′} N₂)
  with eq-kind K₁′ K₂′
... | no K₁′≢K₂′ = no λ{ (T , N , <:ₜ-poly <:₁ , <:ₜ-poly <:₂) → K₁′≢K₂′ refl}
... | yes refl = map′ (λ{ (T , N , <:₁ , <:₂) → T-Poly T , N-Poly N , <:ₜ-poly <:₁ , <:ₜ-poly <:₂})
                      (λ{ (T , N , <:ₜ-poly <:₁ , <:ₜ-poly <:₂) → _ , _ , <:₁ , <:₂})
                      (joinₜ N₁ N₂)
joinₜ (N-Poly N₁) (N-Sub N₂) = no (λ{ (T₁ , N , <:ₜ-poly _ , ())})
joinₜ (N-Poly N₁) (N-ProtoD N₂) = no (λ{ (T₁ , N , <:ₜ-poly _ , ())})
joinₜ (N-Sub N₁) (N-Var NV) = no (λ{ (T₁ , N , <:ₜ-sub _ , ())})
joinₜ (N-Sub N₁) N-Base = no (λ{ (T₁ , N , <:ₜ-sub _ , ())})
joinₜ (N-Sub N₁) (N-Arrow N₂ N₃) = no (λ{ (T₁ , N , <:ₜ-sub _ , ())})
joinₜ (N-Sub N₁) (N-Poly N₂) = no (λ{ (T₁ , N , <:ₜ-sub _ , ())})
joinₜ (N-Sub {pk₁}{m₁}{km≤ = km≤₁} N₁) (N-Sub {pk₂}{m₂}{km≤ = km≤₂} N₂)
  with eq-prekind pk₁ pk₂
... | no pk₁≢pk₂ = no (λ{ (_ , _ , <:ₜ-sub x₁ , <:ₜ-sub x₂) → pk₁≢pk₂ refl})
... | yes refl
  with eq-multiplicity m₁ m₂
... | no m₁≢m₂ = no (λ{ (_ , _ , <:ₜ-sub x₁ , <:ₜ-sub x₂) → m₁≢m₂ refl})
... | yes refl
  rewrite ≤k-irrelevant km≤₁ km≤₂
  = map′ (λ{ (_ , _ , <:₁ , <:₂) → T-Sub km≤₂ _ , N-Sub _ , <:ₜ-sub <:₁ , <:ₜ-sub <:₂})
         (λ{ (_ , _ , <:ₜ-sub <:₁ , <:ₜ-sub <:₂) → _ , _ , <:₁ , <:₂ })
         (joinₜ N₁ N₂)
joinₜ (N-Sub N₁) N-End = no (λ{ (T₁ , N , <:ₜ-sub _ , ())})
joinₜ (N-Sub N₁) (N-Msg p N N₂) = no (λ{ (T₁ , N , <:ₜ-sub _ , ())})
joinₜ (N-Sub N₁) (N-ProtoD N₂) = no (λ{ (T₁ , N , <:ₜ-sub _ , ())})
joinₜ N-End (N-Var NV) = no (λ{ (T₁ , N , <:ₜ-end , ())})
joinₜ N-End (N-Arrow N₂ N₃) = no (λ{ (T₁ , N , <:ₜ-end , ())})
joinₜ N-End (N-Sub N₂) = no (λ{ (T₁ , N , <:ₜ-end , ())})
joinₜ N-End N-End = yes (T-End , N-End , <:ₜ-end , <:ₜ-end)
joinₜ (N-Msg p N N₁) (N-Var NV) = no (λ{ (T₁ , N , <:ₜ-msg _ _ , ())})
joinₜ (N-Msg p N N₁) (N-Arrow N₂ N₃) = no (λ{ (T₁ , N , <:ₜ-msg _ _ , ())})
joinₜ (N-Msg p N N₁) (N-Sub N₂) = no (λ{ (T₁ , N , <:ₜ-msg _ _ , ())})
joinₜ (N-Msg p₁ NP₁ NS₁) (N-Msg p₂ NP₂ NS₂)
  with polarity-equal p₁ p₂
... | no p≢p₁ = no (λ{ (T , N , <:ₜ-msg x <:₁ , <:ₜ-msg x₁ <:₂) → p≢p₁ refl})
... | yes refl
  with mergeₚ′ p₁ NP₁ NP₂
... | no ¬merge = no λ{ (TS , NS , <:ₜ-msg {NP₁ = NP₁} x <:₁ , <:ₜ-msg {NP₁ = NP₂} x₁ <:₂) → ¬merge (_ , _ , x , x₁) }
... | yes (TP , NP , <:₁ , <:₂)
  = map′ (λ{ (TS , NS , <:ₜ₁ , <:ₜ₂) → T-Msg p₁ TP TS , N-Msg p₁ NP NS , <:ₜ-msg <:₁ <:ₜ₁ , <:ₜ-msg <:₂ <:ₜ₂})
         (λ{ (TS , NS , <:ₜ-msg x <:ₜ₁ , <:ₜ-msg x₁ <:ₜ₂) → _ , _ , <:ₜ₁ , <:ₜ₂})
         (joinₜ NS₁ NS₂)
joinₜ (N-ProtoD N₁) (N-Var NV) = no (λ{ (T₁ , N , <:ₜ-data _ , ())})
joinₜ (N-ProtoD N₁) (N-Arrow N₂ N₃) = no (λ{ (T₁ , N , <:ₜ-data _ , ())})
joinₜ (N-ProtoD N₁) (N-Poly N₂) = no (λ{ (T₁ , N , <:ₜ-data _ , ())})
joinₜ (N-ProtoD N₁) (N-Sub N₂) = no (λ{ (T₁ , N , <:ₜ-data _ , ())})
joinₜ (N-ProtoD N₁) (N-ProtoD N₂)
  = map′ (λ{ (T , N , <:₁ , <:₂) → (T-ProtoD T) , (N-ProtoD N) , (<:ₜ-data <:₁ , <:ₜ-data <:₂)})
         (λ{ (T , N , <:ₜ-data <:₁ , <:ₜ-data <:₂) → _ , _ , <:₁ , <:₂})
         (joinₜ N₁ N₂)

mergeₚ′ ⊕ N₁ N₂ = meetₚ′ N₁ N₂
mergeₚ′ ⊝ N₁ N₂ = joinₚ′ N₁ N₂

joinₚ′ {T₁ = T-ProtoP {k = k₁} #c₁ ⊙₁ T₁} {T₂ =  T-ProtoP {k = k₂} #c₂ ⊙₂ T₂}
       (N-ProtoP N₁) (N-ProtoP N₂)
  with k₁ ≟ k₂
... | no k₁≢k₂ = no (λ{ (T , N , <:ₚ′-proto x x₁ , <:ₚ′-proto x₂ x₃) → k₁≢k₂ refl})
... | yes refl
  with ⊙-equal ⊙₁ ⊙₂
... | no ⊙₁≢⊙₂ = no (λ{ (T , N , <:ₚ′-proto x x₁ , <:ₚ′-proto x₂ x₃) → ⊙₁≢⊙₂ refl})
... | yes refl
  = map′ (λ{ (T , N , <:₁ , <:₂) → _ , (N-ProtoP {#c = #c₁ ∪ #c₂} {⊙₁} N , (<:ₚ′-proto (p⊆p∪q #c₂) <:₁) , (<:ₚ′-proto (q⊆p∪q #c₁ #c₂) <:₂))})
         (λ{ (T , N , <:ₚ′-proto x x₁ , <:ₚ′-proto x₂ x₃) → _ , _ , x₁ , x₃})
         (mergeₚ ⊙₁ N₁ N₂)
joinₚ′ (N-ProtoP N) (N-Up N₁) = no (λ{ (_ , _ , <:ₚ′-proto _ _ , ()) })
joinₚ′ (N-ProtoP N) N-Var = no (λ{ (_ , _ , <:ₚ′-proto _ _ , ()) })
joinₚ′ (N-Up N) (N-ProtoP N₁) = no (λ{ (_ , _ , <:ₚ′-up _ , ()) })
joinₚ′ {T₁ = T-Up {pk₁} {m₁} T₁} {T-Up {pk₂} {m₂} T₂}
       (N-Up N) (N-Up N₁)
  with eq-prekind pk₁ pk₂
... | no pk₁≢pk₂ = no λ{ (T , N , <:ₚ′-up x , <:ₚ′-up x₁) → pk₁≢pk₂ refl }
... | yes refl
  with eq-multiplicity m₁ m₂
... | no m₁≢m₂ = no λ{ (T , N , <:ₚ′-up x , <:ₚ′-up x₁) → m₁≢m₂ refl }
... | yes refl = map′ (λ{ (T , N , <:₁ , <:₂) → T-Up T , N-Up N , <:ₚ′-up <:₁ , <:ₚ′-up <:₂})
                      (λ{ (T , N , <:ₚ′-up x , <:ₚ′-up x₁) → _ , _ , x , x₁})
                      (joinₜ N N₁)
joinₚ′ (N-Up N) N-Var = no (λ{ (_ , _ , <:ₚ′-up _ , ()) })
joinₚ′ N-Var (N-ProtoP N) = no (λ{ (_ , _ , <:ₚ′-var , ()) })
joinₚ′ N-Var (N-Up N) = no (λ{ (_ , _ , <:ₚ′-var , ()) })
joinₚ′ {T₁ = T₁} {T₂ = T₂} N-Var N-Var
  with ty-equal T₁ T₂
... | no T₁≢T₂ = no (λ{ (_ , _ , <:ₚ′-var , <:ₚ′-var) → T₁≢T₂ refl})
... | yes refl = yes (_ , _ , <:ₚ′-var , <:ₚ′-var)

mergeₚ ⊕ N₁ N₂ = joinₚ N₁ N₂
mergeₚ ⊝ N₁ N₂ = meetₚ N₁ N₂
mergeₚ ⊘ {T₁} {T₂} N₁ N₂ = map′ (λ{ refl → T₁ , N₁ , refl , refl }) (λ{ (_ , _ , ≡₁ , ≡₂) → trans ≡₁ (sym ≡₂) }) (ty-equal T₁ T₂)

joinₚ (N-Normal NP) (N-Normal NP₁) = map′ (λ{ (_ , _ , <:₁ , <:₂) → _ , N-Normal _ , <:ₚ-plus <:₁ , <:ₚ-plus <:₂ })
                                          (λ{ (_ , _ , <:ₚ-plus x , <:ₚ-plus x₁) → _ , _ , x , x₁ })
                                          (joinₚ′ NP NP₁)
joinₚ (N-Normal NP) (N-Minus NP₁) = no λ{ (_ , _ , <:ₚ-plus x , ()) }
joinₚ (N-Minus NP) (N-Normal NP₁) = no λ{ (_ , _ , <:ₚ-minus x , ()) }
joinₚ (N-Minus NP) (N-Minus NP₁) = map′ (λ{ (_ , _ , <:₁ , <:₂) → T-Minus _ , N-Minus _ , <:ₚ-minus <:₁ , <:ₚ-minus <:₂ })
                                        (λ{ (_ , _ , <:ₚ-minus x , <:ₚ-minus x₁) → _ , _ , x , x₁ })
                                        (meetₚ′ NP NP₁)
