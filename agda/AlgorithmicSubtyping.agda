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
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Function using (const)

module AlgorithmicSubtyping  where

open import Util
open import Kinds
open import Duality
open import Types
open import Subtyping

-- algorithmic version of subtyping that only works on normal forms

data _<:ₚ_ : {P₁ P₂ : Ty Δ KP} → NormalProto P₁ → NormalProto P₂ → Set
data _<:ₚ′_ : {P₁ P₂ : Ty Δ KP} → NormalProto′ P₁ → NormalProto′ P₂ → Set

_<<:ₚ′[_]_ : {P₁ P₂ : Ty Δ KP} → NormalProto′ P₁ → Variance → NormalProto′ P₂ → Set
N₁ <<:ₚ′[ ⊕ ] N₂ = N₁ <:ₚ′ N₂
_<<:ₚ′[_]_ {P₁ = P₁}{P₂} N₁ ⊘ N₂ = P₁ ≡ P₂
N₁ <<:ₚ′[ ⊝ ] N₂ = N₂ <:ₚ′ N₁

_<<:ₚ[_]_ : {P₁ P₂ : Ty Δ KP} → NormalProto P₁ → Variance → NormalProto P₂ → Set
N₁ <<:ₚ[ ⊕ ] N₂ = N₁ <:ₚ N₂
_<<:ₚ[_]_ {P₁ = P₁}{P₂} N₁ ⊘ N₂ = P₁ ≡ P₂
N₁ <<:ₚ[ ⊝ ] N₂ = N₂ <:ₚ N₁


data _<:ₜ_ : {T₁ T₂ : Ty Δ (KV pk m)} → NormalTy T₁ → NormalTy T₂ → Set where

  <:ₜ-var : ∀ {T : Ty Δ (KV pk m)} {nv : NormalVar T} → N-Var nv <:ₜ N-Var nv
  <:ₜ-base : N-Base{Δ = Δ} <:ₜ N-Base
  <:ₜ-arrow : ∀ {≤pk : KM ≤p pk} {m} {T₁ : Ty Δ _}{U₁}{T₂}{U₂}
               {M₁ : NormalTy T₁}{N₁ : NormalTy U₁}{M₂ : NormalTy T₂}{N₂ : NormalTy U₂}
        → M₂ <:ₜ M₁ → N₁ <:ₜ N₂ → (N-Arrow{km = ≤pk}{m} M₁ N₁) <:ₜ (N-Arrow{km = ≤pk}{m} M₂ N₂)
  <:ₜ-poly : ∀ {m}{K′}{T₁ T₂ : Ty (K′ ∷ Δ) (KV KT m)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂}
        → N₁ <:ₜ N₂ → N-Poly N₁ <:ₜ N-Poly N₂
  <:ₜ-sub : ∀ {km≤ : KV pk m ≤k KV pk′ m′}{T₁ T₂ : Ty Δ (KV pk m)}{N₁ : NormalTy T₁}{N₂ : NormalTy T₂}
          → N₁ <:ₜ N₂ → N-Sub{km≤ = km≤} N₁ <:ₜ N-Sub{km≤ = km≤} N₂
  <:ₜ-end : N-End{Δ = Δ} <:ₜ N-End
  <:ₜ-msg : ∀ {p} {P₁ P₂ : Ty Δ KP}{S₁ S₂ : Ty Δ (KV KS Lin)}
          {NP₁ : NormalProto′ P₁}{NP₂ : NormalProto′ P₂}{NS₁ : NormalTy S₁} {NS₂ : NormalTy S₂}
          → NP₁ <<:ₚ′[ injᵥ p ] NP₂ → NS₁ <:ₜ NS₂ → N-Msg p NP₁ NS₁ <:ₜ N-Msg p NP₂ NS₂
  <:ₜ-data : ∀ {T₁ T₂ : Ty Δ (KV KT Lin)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂}
    → N₁ <:ₜ N₂ → N-ProtoD N₁ <:ₜ N-ProtoD N₂

data _<:ₚ′_ where

  <:ₚ′-proto : ∀{P₁ P₂ : Ty Δ KP} {N₁ : NormalProto P₁}{N₂ : NormalProto P₂}
    → #c₁ ⊆ #c₂
    → N₁ <<:ₚ[ ⊙ ] N₂
    → N-ProtoP{#c = #c₁}{⊙ = ⊙} N₁ <:ₚ′ N-ProtoP{#c = #c₂}{⊙ = ⊙} N₂
  <:ₚ′-up : ∀ {T₁ T₂ : Ty Δ (KV pk m)}{N₁ : NormalTy T₁}{N₂ : NormalTy T₂}
    → N₁ <:ₜ N₂
    → N-Up N₁ <:ₚ′ N-Up N₂
  <:ₚ′-var : ∀ {x : KP ∈ Δ} → N-Var{x = x} <:ₚ′ N-Var{x = x}

data _<:ₚ_ where

  <:ₚ-plus : {P₁ P₂ : Ty Δ KP} → {N₁ : NormalProto′ P₁}{N₂ : NormalProto′ P₂}
    → N₁ <:ₚ′ N₂ → N-Normal N₁ <:ₚ N-Normal N₂
  <:ₚ-minus : {P₁ P₂ : Ty Δ KP} → {N₁ : NormalProto′ P₁}{N₂ : NormalProto′ P₂}
    → N₂ <:ₚ′ N₁ → N-Minus N₁ <:ₚ N-Minus N₂


-- algorithmic subtyping is reflexive

<:ₜ-refl : ∀ {T : Ty Δ (KV pk m)}(N : NormalTy T) → N <:ₜ N
<:ₚ′-refl :  ∀ {T : Ty Δ KP}(NP : NormalProto′ T) → NP <:ₚ′ NP
<<:ₚ-refl : ∀ {T : Ty Δ KP}(NP : NormalProto T) → NP <<:ₚ[ ⊙ ] NP
<<:ₚ′-refl : ∀ {T : Ty Δ KP}(NP : NormalProto′ T) → NP <<:ₚ′[ ⊙ ] NP

<:ₚ′-refl (N-ProtoP NP) = <:ₚ′-proto (λ {x} z → z) (<<:ₚ-refl NP)
<:ₚ′-refl (N-Up N) = <:ₚ′-up (<:ₜ-refl N)
<:ₚ′-refl N-Var = <:ₚ′-var


<:ₚ-refl :  ∀ {T : Ty Δ KP}(NP : NormalProto T) → NP <:ₚ NP
<:ₚ-refl (N-Normal NP) = <:ₚ-plus (<:ₚ′-refl NP)
<:ₚ-refl (N-Minus NP) = <:ₚ-minus (<:ₚ′-refl NP)

<<:ₚ-refl {⊙ = ⊕} NP = <:ₚ-refl NP
<<:ₚ-refl {⊙ = ⊝} NP = <:ₚ-refl NP
<<:ₚ-refl {⊙ = ⊘} NP = refl

<<:ₚ′-refl {⊙ = ⊕} NP = <:ₚ′-refl NP
<<:ₚ′-refl {⊙ = ⊝} NP = <:ₚ′-refl NP
<<:ₚ′-refl {⊙ = ⊘} NP = refl

<:ₜ-refl (N-Var x) = <:ₜ-var
<:ₜ-refl N-Base = <:ₜ-base
<:ₜ-refl (N-Arrow N N₁) = <:ₜ-arrow (<:ₜ-refl N) (<:ₜ-refl N₁)
<:ₜ-refl (N-Poly N) = <:ₜ-poly (<:ₜ-refl N)
<:ₜ-refl (N-Sub N) = <:ₜ-sub (<:ₜ-refl N)
<:ₜ-refl N-End = <:ₜ-end
<:ₜ-refl (N-Msg p NP N) = <:ₜ-msg (<<:ₚ′-refl NP) (<:ₜ-refl N)
<:ₜ-refl (N-ProtoD N) = <:ₜ-data (<:ₜ-refl N)


-- algorithmic subtyping is transitive

<:ₜ-trans : ∀ {T₁ T₂ T₃ : Ty Δ (KV pk m)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂} {N₃ : NormalTy T₃} → N₁ <:ₜ N₂ → N₂ <:ₜ N₃ → N₁ <:ₜ N₃
<:ₚ′-trans : ∀ {T₁ T₂ T₃ : Ty Δ KP} {N₁ : NormalProto′ T₁} {N₂ : NormalProto′ T₂} {N₃ : NormalProto′ T₃} → N₁ <:ₚ′ N₂ → N₂ <:ₚ′ N₃ → N₁ <:ₚ′ N₃
<<:ₚ-trans : ∀ {T₁ T₂ T₃ : Ty Δ KP} {N₁ : NormalProto T₁} {N₂ : NormalProto T₂} {N₃ : NormalProto T₃} → N₁ <<:ₚ[ ⊙ ] N₂ → N₂ <<:ₚ[ ⊙ ] N₃ → N₁ <<:ₚ[ ⊙ ] N₃
<<:ₚ′-trans : ∀ {T₁ T₂ T₃ : Ty Δ KP} {N₁ : NormalProto′ T₁} {N₂ : NormalProto′ T₂} {N₃ : NormalProto′ T₃} → N₁ <<:ₚ′[ ⊙ ] N₂ → N₂ <<:ₚ′[ ⊙ ] N₃ → N₁ <<:ₚ′[ ⊙ ] N₃

<:ₚ′-trans (<:ₚ′-proto #c₁⊆#c₂ N₁<<:N₂) (<:ₚ′-proto #c₂⊆#c₃ N₂<<:N₃) = <:ₚ′-proto (λ {x} z → #c₂⊆#c₃ (#c₁⊆#c₂ z)) (<<:ₚ-trans N₁<<:N₂ N₂<<:N₃)
<:ₚ′-trans (<:ₚ′-up N₁<:N₂) (<:ₚ′-up N₂<:N₃) = <:ₚ′-up (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₚ′-trans <:ₚ′-var <:ₚ′-var = <:ₚ′-var

<:ₚ-trans : ∀ {T₁ T₂ T₃ : Ty Δ KP} {N₁ : NormalProto T₁} {N₂ : NormalProto T₂} {N₃ : NormalProto T₃} → N₁ <:ₚ N₂ → N₂ <:ₚ N₃ → N₁ <:ₚ N₃
<:ₚ-trans (<:ₚ-plus N₁<:N₂) (<:ₚ-plus N₂<:N₃) = <:ₚ-plus (<:ₚ′-trans N₁<:N₂ N₂<:N₃)
<:ₚ-trans (<:ₚ-minus N₁<:N₂) (<:ₚ-minus N₂<:N₃) = <:ₚ-minus (<:ₚ′-trans N₂<:N₃ N₁<:N₂)

<<:ₚ-trans {⊙ = ⊕} N₁<<:N₂ N₂<<:N₃ = <:ₚ-trans N₁<<:N₂ N₂<<:N₃
<<:ₚ-trans {⊙ = ⊝} N₁<<:N₂ N₂<<:N₃ = <:ₚ-trans N₂<<:N₃ N₁<<:N₂
<<:ₚ-trans {⊙ = ⊘} N₁<<:N₂ N₂<<:N₃ = trans N₁<<:N₂ N₂<<:N₃

<<:ₚ′-trans {⊙ = ⊕} N₁<<:N₂ N₂<<:N₃ = <:ₚ′-trans N₁<<:N₂ N₂<<:N₃
<<:ₚ′-trans {⊙ = ⊝} N₁<<:N₂ N₂<<:N₃ = <:ₚ′-trans N₂<<:N₃ N₁<<:N₂
<<:ₚ′-trans {⊙ = ⊘} N₁<<:N₂ N₂<<:N₃ = trans N₁<<:N₂ N₂<<:N₃

<:ₜ-trans <:ₜ-var <:ₜ-var = <:ₜ-var
<:ₜ-trans <:ₜ-base <:ₜ-base = <:ₜ-base
<:ₜ-trans (<:ₜ-arrow N₁<:N₂ N₁<:N₃) (<:ₜ-arrow N₂<:N₃ N₂<:N₄) = <:ₜ-arrow (<:ₜ-trans N₂<:N₃ N₁<:N₂) (<:ₜ-trans N₁<:N₃ N₂<:N₄)
<:ₜ-trans (<:ₜ-poly N₁<:N₂) (<:ₜ-poly N₂<:N₃) = <:ₜ-poly (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans (<:ₜ-sub N₁<:N₂) (<:ₜ-sub N₂<:N₃) = <:ₜ-sub (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans <:ₜ-end <:ₜ-end = <:ₜ-end
<:ₜ-trans (<:ₜ-msg P₁<<:P₂ N₁<:N₂) (<:ₜ-msg P₂<<:P₃ N₂<:N₃) = <:ₜ-msg (<<:ₚ′-trans P₁<<:P₂ P₂<<:P₃) (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans (<:ₜ-data N₁<:N₂) (<:ₜ-data N₂<:N₃) = <:ₜ-data (<:ₜ-trans N₁<:N₂ N₂<:N₃)


-- utility

<:ₜ-eq-ty : (N₁ : NormalTy T₁) (N₂ : NormalTy T₂) → T₁ ≡ T₂ → N₁ <:ₜ N₂
<:ₜ-eq-ty N₁ N₂ refl
  rewrite nt-unique N₁ N₂ = <:ₜ-refl N₂


_<<:ₜ[_]_ : {T₁ T₂ : Ty Δ (KV pk m)} → NormalTy T₁ → Polarity → NormalTy T₂ → Set
N₁ <<:ₜ[ ⊕ ] N₂ = N₁ <:ₜ N₂
N₁ <<:ₜ[ ⊝ ] N₂ = N₂ <:ₜ N₁

<<:ₜ-refl : ∀ {p} (N : NormalTy T) → N <<:ₜ[ p ] N
<<:ₜ-refl {p = ⊕} N = <:ₜ-refl N
<<:ₜ-refl {p = ⊝} N = <:ₜ-refl N

<<:ₜ-refl-eq : ∀ {p} (N₁ : NormalTy T₁) (N₂ : NormalTy T₂) (eq : T₁ ≡ T₂) → N₁ <<:ₜ[ p ] N₂
<<:ₜ-refl-eq N₁ N₂ refl
  rewrite nt-unique N₁ N₂ = <<:ₜ-refl N₂


<<:ₜ-trans : ∀ {p} {T₁ T₂ T₃ : Ty Δ (KV pk m)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂} {N₃ : NormalTy T₃} → N₁ <<:ₜ[ p ] N₂ → N₂ <<:ₜ[ p ] N₃ → N₁ <<:ₜ[ p ] N₃
<<:ₜ-trans {p = ⊕} N₁<<:N₂ N₂<<:N₃ = <:ₜ-trans N₁<<:N₂ N₂<<:N₃
<<:ₜ-trans {p = ⊝} N₁<<:N₂ N₂<<:N₃ = <:ₜ-trans N₂<<:N₃ N₁<<:N₂


<<:ₜ-var : ∀ {p} {T : Ty Δ (KV pk m)} {nv : NormalVar T} → N-Var nv <<:ₜ[ p ] N-Var nv
<<:ₜ-var {p = ⊕} = <:ₜ-var
<<:ₜ-var {p = ⊝} = <:ₜ-var

<<:ₜ-base : N-Base{Δ = Δ} <<:ₜ[ p ] N-Base
<<:ₜ-base {p = ⊕} = <:ₜ-base
<<:ₜ-base {p = ⊝} = <:ₜ-base

<<:ₜ-end : N-End{Δ = Δ} <<:ₜ[ p ] N-End
<<:ₜ-end {p = ⊕} = <:ₜ-end
<<:ₜ-end {p = ⊝} = <:ₜ-end

<<:ₜ-sub : ∀ {f₁ f₂} {N₁ : NormalTy (nf p f₁ T₁)}{N₂ : NormalTy (nf p f₂ T₂)}
  → {km≤ : KV pk m ≤k KV pk′ m′} → N₁ <<:ₜ[ p ] N₂ → N-Sub {pk = pk}{m = m}{km≤ = km≤} N₁ <<:ₜ[ p ] N-Sub{pk = pk}{m = m}{km≤ = km≤} N₂
<<:ₜ-sub {⊕} N₁<:N₂ = <:ₜ-sub N₁<:N₂
<<:ₜ-sub {⊝} N₁<:N₂ = <:ₜ-sub N₁<:N₂

-- <<:ₜ-msg : ∀ {p p₀} {P₁ P₂ : Ty Δ KP}{S₁ S₂ : Ty Δ (KV KS Lin)}
--           {NP₁ : NormalProto′ P₁}{NP₂ : NormalProto′ P₂}{NS₁ : NormalTy S₁} {NS₂ : NormalTy S₂}
--           → NP₁ <<:ₚ′[ injᵥ (mult p p₀) ] NP₂
--           → NS₁ <<:ₜ[ p ] NS₂
--           → N-Msg (mult p p₀) NP₁ NS₁ <<:ₜ[ p ] N-Msg (mult p p₀) NP₂ NS₂
-- <<:ₜ-msg {p = ⊕} NP<< NS<< = <:ₜ-msg NP<< NS<<
-- <<:ₜ-msg {p = ⊝} NP<< NS<< = {!<:ₜ-msg NP<<!}
