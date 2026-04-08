open import Data.Empty using (⊥-elim)
-- open import Data.Fin
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; s≤s; z≤n; s≤s⁻¹; _≟_)
open import Data.Nat.Properties using (≤-reflexive; ≤-refl; ≤-trans; n≤1+n; ⊔-comm; ⊔-assoc)
open import Data.Fin.Subset as Subset using (_⊆_; _∪_; _∩_)
open import Data.Fin.Subset.Properties using (⊆-refl; ⊆-antisym; _⊆?_; p⊆p∪q; q⊆p∪q; p∩q⊆p; p∩q⊆q; x∈p∪q⁻; x∈p∩q⁺)
-- open import Data.List
open import Data.Product
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no; map′)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; cong-app; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

-- open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to ≅-refl)

open import Function using (const; _$_; case_of_)

module AlgorithmicNFLubGlb where

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
  )
open import TypesDecidable
open import NormalTypes using
  ( NFProto
  ; NFProto′
  ; NFVar
  ; NFTy
  ; nfProtoTy
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
open import AlgorithmicNFMerge

-- prove that join and meet computer least upper (greatest lower) bounds, respectively

∪-lub : ∀ {k} {c1 c2 c3 : Subset.Subset k} → c1 ⊆ c3 → c2 ⊆ c3 → c1 ∪ c2 ⊆ c3
∪-lub {c1 = c1} {c2} c1⊆c3 c2⊆c3 z with x∈p∪q⁻ c1 c2 z
... | inj₁ z₁ = c1⊆c3 z₁
... | inj₂ z₂ = c2⊆c3 z₂

⊆-∩ : ∀ {k} {c1 c2 c3 : Subset.Subset k} → c3 ⊆ c1 → c3 ⊆ c2 → c3 ⊆ c1 ∩ c2
⊆-∩ c3⊆c1 c3⊆c2 z = x∈p∩q⁺ (c3⊆c1 z , c3⊆c2 z)

lub-joinₜ : ∀ {pk m}
  (N₁ N₂ N₃ : NFTy Δ (KV pk m))
  → N₁ <:ₜ N₃ → N₂ <:ₜ N₃
  → ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] joinₜ N₁ N₂ ≡ yes (N , <:₁ , <:₂) × N <:ₜ N₃

lub-joinₚ′ : ∀
  (N₁ N₂ N₃ : NFProto′ Δ)
  → N₁ <:ₚ′ N₃ → N₂ <:ₚ′ N₃
  → ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] joinₚ′ N₁ N₂ ≡ yes (N , <:₁ , <:₂) × N <:ₚ′ N₃

lub-joinₚ : ∀
  (N₁ N₂ N₃ : NFProto Δ)
  → N₁ <:ₚ N₃ → N₂ <:ₚ N₃
  → ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] joinₚ N₁ N₂ ≡ yes (N , <:₁ , <:₂) × N <:ₚ N₃

glb-meetₜ : ∀ {pk m}
  (N₁ N₂ N₃ : NFTy Δ (KV pk m))
  → N₃ <:ₜ N₁ → N₃ <:ₜ N₂
  → ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] meetₜ N₁ N₂ ≡ yes (N , <:₁ , <:₂) × N₃ <:ₜ N

glb-meetₚ′ : ∀
  (N₁ N₂ N₃ : NFProto′ Δ)
  → N₃ <:ₚ′ N₁ → N₃ <:ₚ′ N₂
  → ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] meetₚ′ N₁ N₂ ≡ yes (N , <:₁ , <:₂) × N₃ <:ₚ′ N

glb-meetₚ : ∀
  (N₁ N₂ N₃ : NFProto Δ)
  → N₃ <:ₚ N₁ → N₃ <:ₚ N₂
  → ∃[ N ] ∃[ <:₁ ] ∃[ <:₂ ] meetₚ N₁ N₂ ≡ yes (N , <:₁ , <:₂) × N₃ <:ₚ N

lub-joinₜ (N-Var (NV-Var x)) (N-Var (NV-Var .x)) (N-Var (NV-Var .x)) <:ₜ-var <:ₜ-var
  with join-var (NV-Var x) (NV-Var x)
... | no ¬a = ⊥-elim (¬a refl)
... | yes refl = N-Var (NV-Var x) , <:ₜ-var , <:ₜ-var , refl , <:ₜ-var
lub-joinₜ (N-Var (NV-Dual D-S x)) (N-Var (NV-Dual D-S .x)) (N-Var (NV-Dual D-S .x)) <:ₜ-var <:ₜ-var
  with join-var (NV-Dual D-S x) (NV-Dual D-S x)
... | no ¬a = ⊥-elim (¬a refl)
... | yes refl = N-Var (NV-Dual D-S x) , <:ₜ-var , <:ₜ-var , refl , <:ₜ-var
lub-joinₜ N₁ N₂ N₃ <:ₜ-base <:ₜ-base = N-Base , <:ₜ-base , <:ₜ-base , refl , <:ₜ-base
lub-joinₜ (N-Arrow _ N₁₁ N₁₂) (N-Arrow _ N₂₁ N₂₂) (N-Arrow _ N₃₁ N₃₂) (<:ₜ-arrow {≤pk = ≤pk} N₁<:N₃ N₁<:N₄) (<:ₜ-arrow N₂<:N₃ N₂<:N₄)
  rewrite ≤p-irrelevant ≤pk ≤pk
  with glb-meetₜ N₂₁ N₁₁ N₃₁ N₂<:N₃ N₁<:N₃
... | Ndom , <:₁₁ , <:₁₂ , meet≡ , <:₁₃
  with lub-joinₜ N₁₂ N₂₂ N₃₂ N₁<:N₄ N₂<:N₄
... | Ncod , <:₂₁ , <:₂₂ , join≡ , <:₂₃
  rewrite meet≡ | join≡
  = N-Arrow ≤pk Ndom Ncod , <:ₜ-arrow <:₁₂ <:₂₁ , <:ₜ-arrow <:₁₁ <:₂₂ , refl , <:ₜ-arrow <:₁₃ <:₂₃
lub-joinₜ (N-Pair {pk₁ = pk₁} {pk₂ = pk₂} N₁₁ N₁₂) (N-Pair {pk₁ = .pk₁} {pk₂ = .pk₂} N₂₁ N₂₂) (N-Pair N₃₁ N₃₂) (<:ₜ-pair N₁<:N₃ N₁<:N₄) (<:ₜ-pair N₂<:N₃ N₂<:N₄)
  with lub-joinₜ N₁₁ N₂₁ N₃₁ N₁<:N₃ N₂<:N₃
... | Nfst , <:₁₁ , <:₁₂ , join≡₁ , <:₁₃
  with lub-joinₜ N₁₂ N₂₂ N₃₂ N₁<:N₄ N₂<:N₄
... | Nsnd , <:₂₁ , <:₂₂ , join≡₂ , <:₂₃
  rewrite eq-prekind′ pk₁ | eq-prekind′ pk₂ | join≡₁ | join≡₂
  = N-Pair Nfst Nsnd , <:ₜ-pair <:₁₁ <:₂₁ , <:ₜ-pair <:₁₂ <:₂₂ , refl , <:ₜ-pair <:₁₃ <:₂₃
lub-joinₜ N₁ N₂ N₃ (<:ₜ-poly {K′ = K′} N₁<:N₃) (<:ₜ-poly N₂<:N₃)
  with lub-joinₜ _ _ _ N₁<:N₃ N₂<:N₃
... | N , <:₁ , <:₂ , join≡ , N<:N₃
  rewrite eq-kind′ K′ | join≡ = N-Poly K′ N , <:ₜ-poly <:₁ , <:ₜ-poly <:₂ , refl , <:ₜ-poly N<:N₃
lub-joinₜ N₁ N₂ N₃ (<:ₜ-sub {pk = pk}{m = m}{km≤ = km≤} N₁<:N₃) (<:ₜ-sub N₂<:N₃)
  with lub-joinₜ _ _ _ N₁<:N₃ N₂<:N₃
... | N , <:₁ , <:₂ , join≡ , N<:N₃
  rewrite eq-prekind′ pk | eq-multiplicity′ m | ≤k-irrelevant km≤ km≤ | join≡
  = N-Sub km≤ N , <:ₜ-sub <:₁ , <:ₜ-sub <:₂ , refl , <:ₜ-sub N<:N₃
lub-joinₜ N₁ N₂ N₃ <:ₜ-end <:ₜ-end = N-End , <:ₜ-end , <:ₜ-end , refl , <:ₜ-end
lub-joinₜ (N-Msg ⊕ NP₁ NS₁) (N-Msg ⊕ NP₂ NS₂) (N-Msg ⊕ NP₃ NS₃) (<:ₜ-msg {p = ⊕} NP₁<<:NP₃ NS₁<:NS₃) (<:ₜ-msg NP₂<<:NP₃ NS₂<:NS₃)
  with glb-meetₚ′ NP₁ NP₂ NP₃ NP₁<<:NP₃ NP₂<<:NP₃
... | Nm , <:₁₁ , <:₁₂ , meet≡ , <:₁₃
  with lub-joinₜ NS₁ NS₂ NS₃ NS₁<:NS₃ NS₂<:NS₃
... | Nc , <:₂₁ , <:₂₂ , join≡ , <:₂₃
  rewrite meet≡ | join≡
  = N-Msg ⊕ Nm Nc , <:ₜ-msg <:₁₁ <:₂₁ , <:ₜ-msg <:₁₂ <:₂₂ , refl , <:ₜ-msg <:₁₃ <:₂₃
lub-joinₜ (N-Msg ⊝ NP₁ NS₁) (N-Msg ⊝ NP₂ NS₂) (N-Msg ⊝ NP₃ NS₃) (<:ₜ-msg {p = ⊝} NP₁<<:NP₃ NS₁<:NS₃) (<:ₜ-msg NP₂<<:NP₃ NS₂<:NS₃)
  with lub-joinₚ′ NP₁ NP₂ NP₃ NP₁<<:NP₃ NP₂<<:NP₃
... | Nm , <:₁₁ , <:₁₂ , join≡₁ , <:₁₃
  with lub-joinₜ NS₁ NS₂ NS₃ NS₁<:NS₃ NS₂<:NS₃
... | Nc , <:₂₁ , <:₂₂ , join≡₂ , <:₂₃
  rewrite join≡₁ | join≡₂
  = N-Msg ⊝ Nm Nc , <:ₜ-msg <:₁₁ <:₂₁ , <:ₜ-msg <:₁₂ <:₂₂ , refl , <:ₜ-msg <:₁₃ <:₂₃
lub-joinₜ N₁ N₂ N₃ (<:ₜ-data N₁<:N₃) (<:ₜ-data N₂<:N₃)
  with lub-joinₜ _ _ _ N₁<:N₃ N₂<:N₃
... | N , <:₁ , <:₂ , join≡ , N<:N₃
  rewrite join≡ = N-ProtoD N , <:ₜ-data <:₁ , <:ₜ-data <:₂ , refl , <:ₜ-data N<:N₃

lub-joinₚ′ (N-ProtoP {k = k} #c₁ ⊕ N₁) (N-ProtoP {k = .k} #c₂ ⊕ N₂) (N-ProtoP {k = .k} #c₃ ⊕ N₃) (<:ₚ′-proto #c₁⊆#c₃ N₁<<:N₃) (<:ₚ′-proto #c₂⊆#c₃ N₂<<:N₃)
  with k ≟ k
... | no k≢k = ⊥-elim (k≢k refl)
... | yes refl
  with ⊙-equal ⊕ ⊕
... | no ⊕≢⊕ = ⊥-elim (⊕≢⊕ refl)
... | yes refl
  with lub-joinₚ N₁ N₂ N₃ N₁<<:N₃ N₂<<:N₃
... | N , <:₁ , <:₂ , join≡ , N<:N₃
  rewrite join≡
  = N-ProtoP (#c₁ ∪ #c₂) ⊕ N , <:ₚ′-proto (p⊆p∪q #c₂) <:₁ , <:ₚ′-proto (q⊆p∪q #c₁ #c₂) <:₂ , refl , <:ₚ′-proto (∪-lub #c₁⊆#c₃ #c₂⊆#c₃) N<:N₃
lub-joinₚ′ (N-ProtoP {k = k} #c₁ ⊝ N₁) (N-ProtoP {k = .k} #c₂ ⊝ N₂) (N-ProtoP {k = .k} #c₃ ⊝ N₃) (<:ₚ′-proto #c₁⊆#c₃ N₁<<:N₃) (<:ₚ′-proto #c₂⊆#c₃ N₂<<:N₃)
  with k ≟ k
... | no k≢k = ⊥-elim (k≢k refl)
... | yes refl
  with ⊙-equal ⊝ ⊝
... | no ⊝≢⊝ = ⊥-elim (⊝≢⊝ refl)
... | yes refl
  with glb-meetₚ N₁ N₂ N₃ N₁<<:N₃ N₂<<:N₃
... | N , <:₁ , <:₂ , meet≡ , N₃<:N
  rewrite meet≡
  = N-ProtoP (#c₁ ∪ #c₂) ⊝ N , <:ₚ′-proto (p⊆p∪q #c₂) <:₁ , <:ₚ′-proto (q⊆p∪q #c₁ #c₂) <:₂ , refl , <:ₚ′-proto (∪-lub #c₁⊆#c₃ #c₂⊆#c₃) N₃<:N
lub-joinₚ′ (N-ProtoP {k = k} #c₁ ⊘ N₁) (N-ProtoP {k = .k} #c₂ ⊘ N₂) (N-ProtoP {k = .k} #c₃ ⊘ N₃) (<:ₚ′-proto #c₁⊆#c₃ eq₁) (<:ₚ′-proto #c₂⊆#c₃ eq₂)
  with k ≟ k
... | no k≢k = ⊥-elim (k≢k refl)
... | yes refl
  with ⊙-equal ⊘ ⊘
... | no ⊘≢⊘ = ⊥-elim (⊘≢⊘ refl)
... | yes refl
  with ty-equal (nfProtoTy N₁) (nfProtoTy N₂)
... | no neq = ⊥-elim (neq (trans eq₁ (sym eq₂)))
... | yes eq
  = N-ProtoP (#c₁ ∪ #c₂) ⊘ N₁
  , <:ₚ′-proto (p⊆p∪q #c₂) refl
  , <:ₚ′-proto (q⊆p∪q #c₁ #c₂) (sym eq)
  , refl
  , <:ₚ′-proto (∪-lub #c₁⊆#c₃ #c₂⊆#c₃) eq₁
lub-joinₚ′ (N-Up N₁) (N-Up N₂) (N-Up N₃) (<:ₚ′-up {pk = pk}{m = m} N₁<:N₃) (<:ₚ′-up N₂<:N₃)
  with lub-joinₜ N₁ N₂ N₃ N₁<:N₃ N₂<:N₃
... | N , <:₁ , <:₂ , join≡ , N<:N₃
  rewrite eq-prekind′ pk | eq-multiplicity′ m | join≡
  = N-Up N , <:ₚ′-up <:₁ , <:ₚ′-up <:₂ , refl , <:ₚ′-up N<:N₃
lub-joinₚ′ (N-Var x) (N-Var .x) (N-Var .x) <:ₚ′-var <:ₚ′-var
  with ty-equal (T-Var x) (T-Var x)
... | no neq = ⊥-elim (neq refl)
... | yes refl = N-Var x , <:ₚ′-var , <:ₚ′-var , refl , <:ₚ′-var

lub-joinₚ (N-Normal N₁) (N-Normal N₂) (N-Normal N₃) (<:ₚ-plus N₁<:N₃) (<:ₚ-plus N₂<:N₃)
  with lub-joinₚ′ N₁ N₂ N₃ N₁<:N₃ N₂<:N₃
... | N , <:₁ , <:₂ , join≡ , N<:N₃
  rewrite join≡
  = N-Normal N , <:ₚ-plus <:₁ , <:ₚ-plus <:₂ , refl , <:ₚ-plus N<:N₃
lub-joinₚ (N-Minus N₁) (N-Minus N₂) (N-Minus N₃) (<:ₚ-minus N₃<:N₁) (<:ₚ-minus N₃<:N₂)
  with glb-meetₚ′ N₁ N₂ N₃ N₃<:N₁ N₃<:N₂
... | N , <:₁ , <:₂ , meet≡ , N₃<:N
  rewrite meet≡
  = N-Minus N , <:ₚ-minus <:₁ , <:ₚ-minus <:₂ , refl , <:ₚ-minus N₃<:N

glb-meetₜ (N-Var (NV-Var x)) (N-Var (NV-Var .x)) (N-Var (NV-Var .x)) <:ₜ-var <:ₜ-var
  with join-var (NV-Var x) (NV-Var x)
... | no ¬a = ⊥-elim (¬a refl)
... | yes refl = N-Var (NV-Var x) , <:ₜ-var , <:ₜ-var , refl , <:ₜ-var
glb-meetₜ (N-Var (NV-Dual D-S x)) (N-Var (NV-Dual D-S .x)) (N-Var (NV-Dual D-S .x)) <:ₜ-var <:ₜ-var
  with join-var (NV-Dual D-S x) (NV-Dual D-S x)
... | no ¬a = ⊥-elim (¬a refl)
... | yes refl = N-Var (NV-Dual D-S x) , <:ₜ-var , <:ₜ-var , refl , <:ₜ-var
glb-meetₜ N₁ N₂ N₃ <:ₜ-base <:ₜ-base = N-Base , <:ₜ-base , <:ₜ-base , refl , <:ₜ-base
glb-meetₜ (N-Arrow _ N₁₁ N₁₂) (N-Arrow _ N₂₁ N₂₂) (N-Arrow _ N₃₁ N₃₂) (<:ₜ-arrow {≤pk = ≤pk} N₁<:N₃ N₃<:N₄) (<:ₜ-arrow N₂<:N₃ N₃<:N₅)
  rewrite ≤p-irrelevant ≤pk ≤pk
  with lub-joinₜ N₂₁ N₁₁ N₃₁ N₂<:N₃ N₁<:N₃
... | Ndom , <:₁₁ , <:₁₂ , join≡ , <:₁₃
  with glb-meetₜ N₁₂ N₂₂ N₃₂ N₃<:N₄ N₃<:N₅
... | Ncod , <:₂₁ , <:₂₂ , meet≡ , <:₂₃
  rewrite join≡ | meet≡
  = N-Arrow ≤pk Ndom Ncod , <:ₜ-arrow <:₁₂ <:₂₁ , <:ₜ-arrow <:₁₁ <:₂₂ , refl , <:ₜ-arrow <:₁₃ <:₂₃
glb-meetₜ (N-Pair {pk₁ = pk₁} {pk₂ = pk₂} N₁₁ N₁₂) (N-Pair {pk₁ = .pk₁} {pk₂ = .pk₂} N₂₁ N₂₂) (N-Pair N₃₁ N₃₂) (<:ₜ-pair N₃<:N₁ N₃<:N₂) (<:ₜ-pair N₃<:N₄ N₃<:N₅)
  with glb-meetₜ N₁₁ N₂₁ N₃₁ N₃<:N₁ N₃<:N₄
... | Nfst , <:₁₁ , <:₁₂ , meet≡₁ , <:₁₃
  with glb-meetₜ N₁₂ N₂₂ N₃₂ N₃<:N₂ N₃<:N₅
... | Nsnd , <:₂₁ , <:₂₂ , meet≡₂ , <:₂₃
  rewrite eq-prekind′ pk₁ | eq-prekind′ pk₂ | meet≡₁ | meet≡₂
  = N-Pair Nfst Nsnd , <:ₜ-pair <:₁₁ <:₂₁ , <:ₜ-pair <:₁₂ <:₂₂ , refl , <:ₜ-pair <:₁₃ <:₂₃
glb-meetₜ N₁ N₂ N₃ (<:ₜ-poly {K′ = K′} N₃<:N₁) (<:ₜ-poly N₃<:N₂)
  with glb-meetₜ _ _ _ N₃<:N₁ N₃<:N₂
... | N , <:₁ , <:₂ , meet≡ , N₃<:N
  rewrite eq-kind′ K′ | meet≡ = N-Poly K′ N , <:ₜ-poly <:₁ , <:ₜ-poly <:₂ , refl , <:ₜ-poly N₃<:N
glb-meetₜ N₁ N₂ N₃ (<:ₜ-sub {pk = pk}{m = m}{km≤ = km≤} N₃<:N₁) (<:ₜ-sub N₃<:N₂)
  with glb-meetₜ _ _ _ N₃<:N₁ N₃<:N₂
... | N , <:₁ , <:₂ , meet≡ , N₃<:N
  rewrite eq-prekind′ pk | eq-multiplicity′ m | ≤k-irrelevant km≤ km≤ | meet≡
  = N-Sub km≤ N , <:ₜ-sub <:₁ , <:ₜ-sub <:₂ , refl , <:ₜ-sub N₃<:N
glb-meetₜ N₁ N₂ N₃ <:ₜ-end <:ₜ-end = N-End , <:ₜ-end , <:ₜ-end , refl , <:ₜ-end
glb-meetₜ (N-Msg ⊕ NP₁ NS₁) (N-Msg ⊕ NP₂ NS₂) (N-Msg ⊕ NP₃ NS₃) (<:ₜ-msg {p = ⊕} NP₃<<:NP₁ NS₃<:NS₁) (<:ₜ-msg NP₃<<:NP₂ NS₃<:NS₂)
  with lub-joinₚ′ NP₁ NP₂ NP₃ NP₃<<:NP₁ NP₃<<:NP₂
... | Nm , <:₁₁ , <:₁₂ , join≡ , <:₁₃
  with glb-meetₜ NS₁ NS₂ NS₃ NS₃<:NS₁ NS₃<:NS₂
... | Nc , <:₂₁ , <:₂₂ , meet≡ , <:₂₃
  rewrite join≡ | meet≡
  = N-Msg ⊕ Nm Nc , <:ₜ-msg <:₁₁ <:₂₁ , <:ₜ-msg <:₁₂ <:₂₂ , refl , <:ₜ-msg <:₁₃ <:₂₃
glb-meetₜ (N-Msg ⊝ NP₁ NS₁) (N-Msg ⊝ NP₂ NS₂) (N-Msg ⊝ NP₃ NS₃) (<:ₜ-msg {p = ⊝} NP₃<<:NP₁ NS₃<:NS₁) (<:ₜ-msg NP₃<<:NP₂ NS₃<:NS₂)
  with glb-meetₚ′ NP₁ NP₂ NP₃ NP₃<<:NP₁ NP₃<<:NP₂
... | Nm , <:₁₁ , <:₁₂ , meet≡₁ , <:₁₃
  with glb-meetₜ NS₁ NS₂ NS₃ NS₃<:NS₁ NS₃<:NS₂
... | Nc , <:₂₁ , <:₂₂ , meet≡₂ , <:₂₃
  rewrite meet≡₁ | meet≡₂
  = N-Msg ⊝ Nm Nc , <:ₜ-msg <:₁₁ <:₂₁ , <:ₜ-msg <:₁₂ <:₂₂ , refl , <:ₜ-msg <:₁₃ <:₂₃
glb-meetₜ N₁ N₂ N₃ (<:ₜ-data N₃<:N₁) (<:ₜ-data N₃<:N₂)
  with glb-meetₜ _ _ _ N₃<:N₁ N₃<:N₂
... | N , <:₁ , <:₂ , meet≡ , N₃<:N
  rewrite meet≡ = N-ProtoD N , <:ₜ-data <:₁ , <:ₜ-data <:₂ , refl , <:ₜ-data N₃<:N

glb-meetₚ′ (N-ProtoP {k = k} #c₁ ⊕ N₁) (N-ProtoP {k = .k} #c₂ ⊕ N₂) (N-ProtoP {k = .k} #c₃ ⊕ N₃) (<:ₚ′-proto #c₃⊆#c₁ N₃<<:N₁) (<:ₚ′-proto #c₃⊆#c₂ N₃<<:N₂)
  with k ≟ k
... | no k≢k = ⊥-elim (k≢k refl)
... | yes refl
  with ⊙-equal ⊕ ⊕
... | no ⊕≢⊕ = ⊥-elim (⊕≢⊕ refl)
... | yes refl
  with glb-meetₚ N₁ N₂ N₃ N₃<<:N₁ N₃<<:N₂
... | N , <:₁ , <:₂ , meet≡ , N₃<:N
  rewrite meet≡
  = N-ProtoP (#c₁ ∩ #c₂) ⊕ N , <:ₚ′-proto (p∩q⊆p #c₁ #c₂) <:₁ , <:ₚ′-proto (p∩q⊆q #c₁ #c₂) <:₂ , refl , <:ₚ′-proto (⊆-∩ #c₃⊆#c₁ #c₃⊆#c₂) N₃<:N
glb-meetₚ′ (N-ProtoP {k = k} #c₁ ⊝ N₁) (N-ProtoP {k = .k} #c₂ ⊝ N₂) (N-ProtoP {k = .k} #c₃ ⊝ N₃) (<:ₚ′-proto #c₃⊆#c₁ N₁<:N₃) (<:ₚ′-proto #c₃⊆#c₂ N₂<:N₃)
  with k ≟ k
... | no k≢k = ⊥-elim (k≢k refl)
... | yes refl
  with ⊙-equal ⊝ ⊝
... | no ⊝≢⊝ = ⊥-elim (⊝≢⊝ refl)
... | yes refl
  with lub-joinₚ N₁ N₂ N₃ N₁<:N₃ N₂<:N₃
... | N , <:₁ , <:₂ , join≡ , N<:N₃
  rewrite join≡
  = N-ProtoP (#c₁ ∩ #c₂) ⊝ N , <:ₚ′-proto (p∩q⊆p #c₁ #c₂) <:₁ , <:ₚ′-proto (p∩q⊆q #c₁ #c₂) <:₂ , refl , <:ₚ′-proto (⊆-∩ #c₃⊆#c₁ #c₃⊆#c₂) N<:N₃
glb-meetₚ′ (N-ProtoP {k = k} #c₁ ⊘ N₁) (N-ProtoP {k = .k} #c₂ ⊘ N₂) (N-ProtoP {k = .k} #c₃ ⊘ N₃) (<:ₚ′-proto #c₃⊆#c₁ eq₁) (<:ₚ′-proto #c₃⊆#c₂ eq₂)
  with k ≟ k
... | no k≢k = ⊥-elim (k≢k refl)
... | yes refl
  with ⊙-equal ⊘ ⊘
... | no ⊘≢⊘ = ⊥-elim (⊘≢⊘ refl)
... | yes refl
  with ty-equal (nfProtoTy N₁) (nfProtoTy N₂)
... | no neq = ⊥-elim (neq (trans (sym eq₁) eq₂))
... | yes eq
  = N-ProtoP (#c₁ ∩ #c₂) ⊘ N₁
  , <:ₚ′-proto (p∩q⊆p #c₁ #c₂) refl
  , <:ₚ′-proto (p∩q⊆q #c₁ #c₂) eq
  , refl
  , <:ₚ′-proto (⊆-∩ #c₃⊆#c₁ #c₃⊆#c₂) eq₁
glb-meetₚ′ (N-Up N₁) (N-Up N₂) (N-Up N₃) (<:ₚ′-up {pk = pk}{m = m} N₃<:N₁) (<:ₚ′-up N₃<:N₂)
  with glb-meetₜ N₁ N₂ N₃ N₃<:N₁ N₃<:N₂
... | N , <:₁ , <:₂ , meet≡ , N₃<:N
  rewrite eq-prekind′ pk | eq-multiplicity′ m | meet≡
  = N-Up N , <:ₚ′-up <:₁ , <:ₚ′-up <:₂ , refl , <:ₚ′-up N₃<:N
glb-meetₚ′ (N-Var x) (N-Var .x) (N-Var .x) <:ₚ′-var <:ₚ′-var
  with ty-equal (T-Var x) (T-Var x)
... | no neq = ⊥-elim (neq refl)
... | yes refl = N-Var x , <:ₚ′-var , <:ₚ′-var , refl , <:ₚ′-var

glb-meetₚ (N-Normal N₁) (N-Normal N₂) (N-Normal N₃) (<:ₚ-plus N₃<:N₁) (<:ₚ-plus N₃<:N₂)
  with glb-meetₚ′ N₁ N₂ N₃ N₃<:N₁ N₃<:N₂
... | N , <:₁ , <:₂ , meet≡ , N₃<:N
  rewrite meet≡
  = N-Normal N , <:ₚ-plus <:₁ , <:ₚ-plus <:₂ , refl , <:ₚ-plus N₃<:N
glb-meetₚ (N-Minus N₁) (N-Minus N₂) (N-Minus N₃) (<:ₚ-minus N₁<:N₃) (<:ₚ-minus N₂<:N₃)
  with lub-joinₚ′ N₁ N₂ N₃ N₁<:N₃ N₂<:N₃
... | N , <:₁ , <:₂ , join≡ , N<:N₃
  rewrite join≡
  = N-Minus N , <:ₚ-minus <:₁ , <:ₚ-minus <:₂ , refl , <:ₚ-minus N<:N₃
