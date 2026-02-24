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

module AlgorithmicLubGlb where

open import Util
open import Kinds
open import Duality
open import Types
open import TypesDecidable
open import Subtyping
open import SubtypingProperties
open import AlgorithmicSubtyping
open import AlgorithmicSound
open import AlgorithmicMerge

-- prove that join and meet computer least upper (greatest lower) bounds, respectively

lub-joinₜ : ∀ {T₁ T₂ T₃ : Ty Δ (KV pk m)}
  (N₁ : NormalTy T₁) (N₂ : NormalTy T₂) (N₃ : NormalTy T₃)
  → N₁ <:ₜ N₃ → N₂ <:ₜ N₃
  → ∃[ T ] ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] joinₜ N₁ N₂ ≡ yes (T , N , <:₁ , <:₂) × N <:ₜ N₃

lub-joinₚ′ : ∀ {T₁ T₂ T₃ : Ty Δ KP}
  (N₁ : NormalProto′ T₁) (N₂ : NormalProto′ T₂) (N₃ : NormalProto′ T₃)
  → N₁ <:ₚ′ N₃ → N₂ <:ₚ′ N₃
  → ∃[ T ] ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] joinₚ′ N₁ N₂ ≡ yes (T , N , <:₁ , <:₂) × N <:ₚ′ N₃

lub-joinₚ : ∀ {T₁ T₂ T₃ : Ty Δ KP}
  (N₁ : NormalProto T₁) (N₂ : NormalProto T₂) (N₃ : NormalProto T₃)
  → N₁ <:ₚ N₃ → N₂ <:ₚ N₃
  → ∃[ T ] ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] joinₚ N₁ N₂ ≡ yes (T , N , <:₁ , <:₂) × N <:ₚ N₃

glb-meetₜ : ∀ {T₁ T₂ T₃ : Ty Δ (KV pk m)}
  (N₁ : NormalTy T₁) (N₂ : NormalTy T₂) (N₃ : NormalTy T₃)
  → N₃ <:ₜ N₁ → N₃ <:ₜ N₂
  → ∃[ T ] ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] meetₜ N₁ N₂ ≡ yes (T , N , <:₁ , <:₂) × N₃ <:ₜ N

glb-meetₚ′ : ∀ {T₁ T₂ T₃ : Ty Δ KP}
  (N₁ : NormalProto′ T₁) (N₂ : NormalProto′ T₂) (N₃ : NormalProto′ T₃)
  → N₃ <:ₚ′ N₁ → N₃ <:ₚ′ N₂
  → ∃[ T ] ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] meetₚ′ N₁ N₂ ≡ yes (T , N , <:₁ , <:₂) × N₃ <:ₚ′ N

glb-meetₚ : ∀ {T₁ T₂ T₃ : Ty Δ KP}
  (N₁ : NormalProto T₁) (N₂ : NormalProto T₂) (N₃ : NormalProto T₃)
  → N₃ <:ₚ N₁ → N₃ <:ₚ N₂
  → ∃[ T ] ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] meetₚ N₁ N₂ ≡ yes (T , N , <:₁ , <:₂) × N₃ <:ₚ N

lub-joinₜ {T₁ = T-Var x} N₁ N₂ N₃ (<:ₜ-var {nv = NV-Var}) <:ₜ-var
  with join-var (NV-Var{x = x}) (NV-Var {x = x})
... | no ¬a = ⊥-elim (¬a (T-Var x , refl , refl))
... | yes (T , refl , refl) = (T-Var x) , ((N-Var NV-Var) , (<:ₜ-var , (<:ₜ-var , (refl , <:ₜ-var))))
lub-joinₜ {T₁ = T₁} N₁ N₂ N₃ (<:ₜ-var {nv = NV-Dual D-S x}) <:ₜ-var
  with join-var (NV-Var{x = x}) (NV-Var {x = x})
... | no ¬a = ⊥-elim (¬a (T-Var x , refl , refl))
... | yes (T , refl , refl)
  rewrite var-equal′ x = (T-Dual D-S (T-Var x)) , ((N-Var (NV-Dual D-S x)) , (<:ₜ-var , (<:ₜ-var , (refl , <:ₜ-var))))
lub-joinₜ N₁ N₂ N₃ <:ₜ-base <:ₜ-base = T-Base , N-Base , <:ₜ-base , <:ₜ-base , refl , <:ₜ-base
lub-joinₜ (N-Arrow N₁₁ N₁₂) (N-Arrow N₂₁ N₂₂) (N-Arrow N₃₁ N₃₂) (<:ₜ-arrow {≤pk = ≤pk} N₁<:N₃ N₁<:N₄) (<:ₜ-arrow N₂<:N₃ N₂<:N₄)
  rewrite ≤p-irrelevant ≤pk ≤pk
  with glb-meetₜ N₂₁ N₁₁ N₃₁ N₂<:N₃ N₁<:N₃
... | Tdom , Ndom , <:₁₁ , <:₁₂ , meet≡ , <:₁₃
  with lub-joinₜ N₁₂ N₂₂ N₃₂ N₁<:N₄ N₂<:N₄
... | Tcod , Ncod , <:₂₁ , <:₂₂ , join≡ , <:₂₃
  rewrite meet≡ | join≡
  = (T-Arrow ≤pk Tdom Tcod) , ((N-Arrow Ndom Ncod) , ((<:ₜ-arrow <:₁₂ <:₂₁) , ((<:ₜ-arrow <:₁₁ <:₂₂) , (refl , (<:ₜ-arrow <:₁₃ <:₂₃)))))
lub-joinₜ N₁ N₂ N₃ (<:ₜ-poly {K′ = K′} N₁<:N₃) (<:ₜ-poly N₂<:N₃)
  with lub-joinₜ _ _ _ N₁<:N₃ N₂<:N₃
... | ( T , N , <:₁ , <:₂ , join≡ , N<:N₃)
  rewrite eq-kind′ K′ | join≡ = (T-Poly T) , ((N-Poly N) , ((<:ₜ-poly <:₁) , ((<:ₜ-poly <:₂) , (refl , (<:ₜ-poly N<:N₃)))))
lub-joinₜ N₁ N₂ N₃ (<:ₜ-sub {pk = pk}{m = m}{km≤ = km≤} N₁<:N₃) (<:ₜ-sub N₂<:N₃)
  with lub-joinₜ _ _ _ N₁<:N₃ N₂<:N₃
... | ( T , N , <:₁ , <:₂ , join≡ , N<:N₃)
  rewrite eq-prekind′ pk | eq-multiplicity′ m | ≤k-irrelevant km≤ km≤ | join≡
  = T-Sub km≤ T , (N-Sub N) , ((<:ₜ-sub <:₁) , ((<:ₜ-sub <:₂) , (refl , (<:ₜ-sub N<:N₃))))
lub-joinₜ N₁ N₂ N₃ <:ₜ-end <:ₜ-end = T-End , N-End , <:ₜ-end , <:ₜ-end , refl , <:ₜ-end
lub-joinₜ (N-Msg ⊕ NP₁ NS₁) (N-Msg ⊕ NP₂ NS₂) (N-Msg ⊕ NP₃ NS₃) (<:ₜ-msg {p = ⊕} NP₁<<:NP₃ NS₁<:NS₃) (<:ₜ-msg NP₂<<:NP₃ NS₂<:NS₃)
  with glb-meetₚ′ NP₁ NP₂ NP₃ NP₁<<:NP₃ NP₂<<:NP₃
... | (Tm , Nm , <:₁₁ , <:₁₂ , meet≡ , <:₁₃)
  with lub-joinₜ NS₁ NS₂ NS₃ NS₁<:NS₃ NS₂<:NS₃
... | (Tc , Nc , <:₂₁ , <:₂₂ , join≡ , <:₂₃)
  rewrite meet≡ | join≡
  = T-Msg ⊕ Tm Tc , (N-Msg ⊕ Nm Nc) , ((<:ₜ-msg <:₁₁ <:₂₁) , ((<:ₜ-msg <:₁₂ <:₂₂) , (refl , (<:ₜ-msg <:₁₃ <:₂₃))))
lub-joinₜ (N-Msg ⊝ NP₁ NS₁) (N-Msg ⊝ NP₂ NS₂) (N-Msg ⊝ NP₃ NS₃) (<:ₜ-msg {p = ⊝} NP₁<<:NP₃ NS₁<:NS₃) (<:ₜ-msg NP₂<<:NP₃ NS₂<:NS₃)
  with lub-joinₚ′ NP₁ NP₂ NP₃ NP₁<<:NP₃ NP₂<<:NP₃
... | (Tm , Nm , <:₁₁ , <:₁₂ , join≡₁ , <:₁₃)
  with lub-joinₜ NS₁ NS₂ NS₃ NS₁<:NS₃ NS₂<:NS₃
... | (Tc , Nc , <:₂₁ , <:₂₂ , join≡₂ , <:₂₃)
  rewrite join≡₁ | join≡₂
  = (T-Msg ⊝ Tm Tc) , ((N-Msg ⊝ Nm Nc) , (<:ₜ-msg <:₁₁ <:₂₁ , (<:ₜ-msg <:₁₂ <:₂₂) , (refl , (<:ₜ-msg <:₁₃ <:₂₃))))
lub-joinₜ N₁ N₂ N₃ (<:ₜ-data N₁<:N₃) (<:ₜ-data N₂<:N₃)
  with lub-joinₜ _ _ _ N₁<:N₃ N₂<:N₃
... | ( T , N , <:₁ , <:₂ , join≡ , N<:N₃)
  rewrite join≡ = (T-ProtoD T) , (N-ProtoD N , (<:ₜ-data <:₁) , ((<:ₜ-data <:₂) , (refl , <:ₜ-data N<:N₃)))

lub-joinₚ′ (N-ProtoP {⊙ = ⊕} N₁) (N-ProtoP N₂) (N-ProtoP N₃) (<:ₚ′-proto #c₁⊆#c₃ N₁<<:N₃) (<:ₚ′-proto #c₂⊆#c₃ N₂<<:N₃)
  with lub-joinₚ N₁ N₂ N₃ N₁<<:N₃ N₂<<:N₃
... | ( T , N , <:₁ , <:₂ , join≡ , N<:N₃) = (T-ProtoP {!!} ⊕ T) , (N-ProtoP N) , ((<:ₚ′-proto (λ {x} z → z) <:₁) , ((<:ₚ′-proto {!!} <:₂) , ({!!} , (<:ₚ′-proto #c₁⊆#c₃ N<:N₃))))
lub-joinₚ′ (N-ProtoP {⊙ = ⊝} N₁) (N-ProtoP N₂) (N-ProtoP N₃) (<:ₚ′-proto #c₁⊆#c₃ N₁<<:N₃) (<:ₚ′-proto #c₂⊆#c₃ N₂<<:N₃) = {!!}
lub-joinₚ′ (N-ProtoP {⊙ = ⊘} N₁) (N-ProtoP N₂) (N-ProtoP N₃) (<:ₚ′-proto #c₁⊆#c₃ refl) (<:ₚ′-proto #c₂⊆#c₃ refl) = {!!}
lub-joinₚ′ (N-Up N₁) (N-Up N₂) (N-Up N₃) (<:ₚ′-up {pk = pk}{m = m} N₁<:N₃) (<:ₚ′-up N₂<:N₃)
  with lub-joinₜ N₁ N₂ N₃ N₁<:N₃ N₂<:N₃
... | ( T , N , <:₁ , <:₂ , join≡ , N<:N₃)
  rewrite eq-prekind′ pk | eq-multiplicity′ m | join≡
  = (T-Up T) , ((N-Up N) , ((<:ₚ′-up <:₁) , ((<:ₚ′-up <:₂) , (refl , (<:ₚ′-up N<:N₃)))))
lub-joinₚ′ N₁ N₂ N₃ (<:ₚ′-var {x = x}) <:ₚ′-var
  rewrite var-equal′ x
  = (T-Var x) , (N-Var , (<:ₚ′-var , (<:ₚ′-var , (refl , <:ₚ′-var))))
