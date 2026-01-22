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

module AlgorithmicSubtyping  where

open import Util
open import Kinds
open import Duality
open import Types
open import Subtyping

-- algorithmic version of subtyping that only works on normal forms

data _<:ₚ_ : {P₁ P₂ : Ty Δ KP} → NormalProto P₁ → NormalProto P₂ → Set

_<<:ₚ[_]_ : {P₁ P₂ : Ty Δ KP} → NormalProto P₁ → Variance → NormalProto P₂ → Set
N₁ <<:ₚ[ ⊕ ] N₂ = N₁ <:ₚ N₂
_<<:ₚ[_]_ {P₁ = P₁}{P₂} N₁ ⊘ N₂ = P₁ ≡ P₂
N₁ <<:ₚ[ ⊝ ] N₂ = N₂ <:ₚ N₁

data _<:ₜ_ : {T₁ T₂ : Ty Δ (KV pk m)} → NormalTy T₁ → NormalTy T₂ → Set where

  <:ₜ-var : ∀ {T : Ty Δ (KV pk m)} {nv : NormalVar T} → N-Var nv <:ₜ N-Var nv
  <:ₜ-base : N-Base{Δ = Δ} <:ₜ N-Base
  <:ₜ-arrow : ∀ {≤pk : KM ≤p pk} {m} {T₁ : Ty Δ _}{U₁}{T₂}{U₂}
               {M₁ : NormalTy T₁}{N₁ : NormalTy U₁}{M₂ : NormalTy T₂}{N₂ : NormalTy U₂}
        → M₂ <:ₜ M₁ → N₁ <:ₜ N₂ → _<:ₜ_ (N-Arrow{km = ≤pk}{m} M₁ N₁) (N-Arrow{km = ≤pk}{m} M₂ N₂)
  <:ₜ-poly : ∀ {m}{K′}{T₁ T₂ : Ty (K′ ∷ Δ) (KV KT m)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂}
        → N₁ <:ₜ N₂ → N-Poly N₁ <:ₜ N-Poly N₂
  <:ₜ-sub : ∀ {km≤ : KV pk m ≤k KV pk′ m′}{T₁ T₂ : Ty Δ (KV pk m)}{N₁ : NormalTy T₁}{N₂ : NormalTy T₂} → N₁ <:ₜ N₂ → N-Sub{km≤ = km≤} N₁ <:ₜ N-Sub{km≤ = km≤} N₂
  <:ₜ-end : N-End{Δ = Δ} <:ₜ N-End
  <:ₜ-msg : ∀ {p} {P₁ P₂ : Ty Δ KP}{S₁ S₂ : Ty Δ (KV KS Lin)}
          {NP₁ : NormalProto P₁}{NP₂ : NormalProto P₂}{NS₁ : NormalTy S₁} {NS₂ : NormalTy S₂}
          → NP₁ <<:ₚ[ injᵥ p ] NP₂ → NS₁ <:ₜ NS₂ → N-Msg p NP₁ NS₁ <:ₜ N-Msg p NP₂ NS₂
  <:ₜ-data : ∀ {T₁ T₂ : Ty Δ (KV KT Lin)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂}
    → N₁ <:ₜ N₂ → N-ProtoD N₁ <:ₜ N-ProtoD N₂

data _<:ₚ′_ : {P₁ P₂ : Ty Δ KP} → NormalProto′ P₁ → NormalProto′ P₂ → Set where

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

-- algorithmic typing is sound

sound-algₜ : ∀ {T₁ T₂ : Ty Δ (KV pk m)} {N₁ : NormalTy T₁}{N₂ : NormalTy T₂}
  → N₁ <:ₜ N₂ → T₁ <: T₂

sound-<<:ₚ : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto T₁}{N₂ : NormalProto T₂}
  → N₁ <<:ₚ[ ⊙ ] N₂ → T₁ <<:[ ⊙ ] T₂

sound-algₚ′ : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto′ T₁}{N₂ : NormalProto′ T₂}
  → N₁ <:ₚ′ N₂ → T₁ <: T₂
sound-algₚ′ (<:ₚ′-proto #c₁⊆#c₂ N₁<:N₂) = <:-proto #c₁⊆#c₂ (sound-<<:ₚ N₁<:N₂)
sound-algₚ′ (<:ₚ′-up N₁<:ₜN₂) = <:-up (sound-algₜ N₁<:ₜN₂)
sound-algₚ′ <:ₚ′-var = <:-refl

sound-algₚ : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto T₁}{N₂ : NormalProto T₂}
  → N₁ <:ₚ N₂ → T₁ <: T₂
sound-algₚ (<:ₚ-plus N₁<:N₂) = sound-algₚ′ N₁<:N₂
sound-algₚ (<:ₚ-minus N₂<:N₁) = <:-minus (sound-algₚ′ N₂<:N₁)

sound-<<:ₚ {⊙ = ⊕} N₁<<:N₂ = sound-algₚ N₁<<:N₂
sound-<<:ₚ {⊙ = ⊝} N₁<<:N₂ = sound-algₚ N₁<<:N₂
sound-<<:ₚ {⊙ = ⊘} refl = ≡c-refl

sound-algₜ <:ₜ-var = <:-refl
sound-algₜ <:ₜ-base = <:-refl
sound-algₜ (<:ₜ-arrow M₂<:ₜM₁ N₁<:ₜN₂) = <:-fun (sound-algₜ M₂<:ₜM₁) (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-poly N₁<:ₜN₂) = <:-all (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-sub {km≤ = km≤} N₁<:ₜN₂) = <:-sub km≤ (sound-algₜ N₁<:ₜN₂)
sound-algₜ <:ₜ-end = <:-refl
sound-algₜ (<:ₜ-msg {p = p} P₁<<P₂ N₁<:ₜN₂) = <:-msg (sound-<<:ₚ P₁<<P₂) (sound-algₜ N₁<:ₜN₂)
sound-algₜ (<:ₜ-data N₁<:ₜN₂) = <:-protoD (sound-algₜ N₁<:ₜN₂)


-- algorithmic subtyping is reflexive

<:ₜ-refl : ∀ {T : Ty Δ (KV pk m)}(N : NormalTy T) → N <:ₜ N
<:ₚ′-refl :  ∀ {T : Ty Δ KP}(NP : NormalProto′ T) → NP <:ₚ′ NP
<<:ₚ-refl : ∀ {T : Ty Δ KP}(NP : NormalProto T) → NP <<:ₚ[ ⊙ ] NP

<:ₚ′-refl (N-ProtoP NP) = <:ₚ′-proto (λ {x} z → z) (<<:ₚ-refl NP)
<:ₚ′-refl (N-Up N) = <:ₚ′-up (<:ₜ-refl N)
<:ₚ′-refl N-Var = <:ₚ′-var


<:ₚ-refl :  ∀ {T : Ty Δ KP}(NP : NormalProto T) → NP <:ₚ NP
<:ₚ-refl (N-Normal NP) = <:ₚ-plus (<:ₚ′-refl NP)
<:ₚ-refl (N-Minus NP) = <:ₚ-minus (<:ₚ′-refl NP)

<<:ₚ-refl {⊙ = ⊕} NP = <:ₚ-refl NP
<<:ₚ-refl {⊙ = ⊝} NP = <:ₚ-refl NP
<<:ₚ-refl {⊙ = ⊘} NP = refl

<:ₜ-refl (N-Var x) = <:ₜ-var
<:ₜ-refl N-Base = <:ₜ-base
<:ₜ-refl (N-Arrow N N₁) = <:ₜ-arrow (<:ₜ-refl N) (<:ₜ-refl N₁)
<:ₜ-refl (N-Poly N) = <:ₜ-poly (<:ₜ-refl N)
<:ₜ-refl (N-Sub N) = <:ₜ-sub (<:ₜ-refl N)
<:ₜ-refl N-End = <:ₜ-end
<:ₜ-refl (N-Msg p NP N) = <:ₜ-msg (<<:ₚ-refl NP) (<:ₜ-refl N)
<:ₜ-refl (N-ProtoD N) = <:ₜ-data (<:ₜ-refl N)

-- algorithmic subtyping is transitive

<:ₜ-trans : ∀ {T₁ T₂ T₃ : Ty Δ (KV pk m)} {N₁ : NormalTy T₁} {N₂ : NormalTy T₂} {N₃ : NormalTy T₃} → N₁ <:ₜ N₂ → N₂ <:ₜ N₃ → N₁ <:ₜ N₃
<:ₚ′-trans : ∀ {T₁ T₂ T₃ : Ty Δ KP} {N₁ : NormalProto′ T₁} {N₂ : NormalProto′ T₂} {N₃ : NormalProto′ T₃} → N₁ <:ₚ′ N₂ → N₂ <:ₚ′ N₃ → N₁ <:ₚ′ N₃
<<:ₚ-trans : ∀ {T₁ T₂ T₃ : Ty Δ KP} {N₁ : NormalProto T₁} {N₂ : NormalProto T₂} {N₃ : NormalProto T₃} → N₁ <<:ₚ[ ⊙ ] N₂ → N₂ <<:ₚ[ ⊙ ] N₃ → N₁ <<:ₚ[ ⊙ ] N₃

<:ₚ′-trans (<:ₚ′-proto #c₁⊆#c₂ N₁<<:N₂) (<:ₚ′-proto #c₂⊆#c₃ N₂<<:N₃) = <:ₚ′-proto (λ {x} z → #c₂⊆#c₃ (#c₁⊆#c₂ z)) (<<:ₚ-trans N₁<<:N₂ N₂<<:N₃)
<:ₚ′-trans (<:ₚ′-up N₁<:N₂) (<:ₚ′-up N₂<:N₃) = <:ₚ′-up (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₚ′-trans <:ₚ′-var <:ₚ′-var = <:ₚ′-var

<:ₚ-trans : ∀ {T₁ T₂ T₃ : Ty Δ KP} {N₁ : NormalProto T₁} {N₂ : NormalProto T₂} {N₃ : NormalProto T₃} → N₁ <:ₚ N₂ → N₂ <:ₚ N₃ → N₁ <:ₚ N₃
<:ₚ-trans (<:ₚ-plus N₁<:N₂) (<:ₚ-plus N₂<:N₃) = <:ₚ-plus (<:ₚ′-trans N₁<:N₂ N₂<:N₃)
<:ₚ-trans (<:ₚ-minus N₁<:N₂) (<:ₚ-minus N₂<:N₃) = <:ₚ-minus (<:ₚ′-trans N₂<:N₃ N₁<:N₂)


<<:ₚ-trans {⊙ = ⊕} N₁<<:N₂ N₂<<:N₃ = <:ₚ-trans N₁<<:N₂ N₂<<:N₃
<<:ₚ-trans {⊙ = ⊝} N₁<<:N₂ N₂<<:N₃ = <:ₚ-trans N₂<<:N₃ N₁<<:N₂
<<:ₚ-trans {⊙ = ⊘} N₁<<:N₂ N₂<<:N₃ = trans N₁<<:N₂ N₂<<:N₃

<:ₜ-trans <:ₜ-var <:ₜ-var = <:ₜ-var
<:ₜ-trans <:ₜ-base <:ₜ-base = <:ₜ-base
<:ₜ-trans (<:ₜ-arrow N₁<:N₂ N₁<:N₃) (<:ₜ-arrow N₂<:N₃ N₂<:N₄) = <:ₜ-arrow (<:ₜ-trans N₂<:N₃ N₁<:N₂) (<:ₜ-trans N₁<:N₃ N₂<:N₄)
<:ₜ-trans (<:ₜ-poly N₁<:N₂) (<:ₜ-poly N₂<:N₃) = <:ₜ-poly (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans (<:ₜ-sub N₁<:N₂) (<:ₜ-sub N₂<:N₃) = <:ₜ-sub (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans <:ₜ-end <:ₜ-end = <:ₜ-end
<:ₜ-trans (<:ₜ-msg P₁<<:P₂ N₁<:N₂) (<:ₜ-msg P₂<<:P₃ N₂<:N₃) = <:ₜ-msg (<<:ₚ-trans P₁<<:P₂ P₂<<:P₃) (<:ₜ-trans N₁<:N₂ N₂<:N₃)
<:ₜ-trans (<:ₜ-data N₁<:N₂) (<:ₜ-data N₂<:N₃) = <:ₜ-data (<:ₜ-trans N₁<:N₂ N₂<:N₃)


-- algorithmic subtyping is complete

open import Ext using (ext)

<:ₜ-eq-ty : (N₁ : NormalTy T₁) (N₂ : NormalTy T₂) → T₁ ≡ T₂ → N₁ <:ₜ N₂
<:ₜ-eq-ty N₁ N₂ refl
  rewrite nt-unique N₁ N₂ = <:ₜ-refl N₂

complete-algₜ : ∀ {p : Polarity} {T₁ T₂ : Ty Δ (KV pk m)}
  {f₁ f₂} {N₁ : NormalTy (nf p f₁ T₁)}{N₂ : NormalTy (nf p f₂ T₂)}
  → T₁ <: T₂
  → N₁ <:ₜ N₂

-- complete-algₚ′ : ∀ {T₁ T₂ : Ty Δ KP}
--   {f₁ f₂} {N₁ : NormalProto′ (nf ⊕ f₁ T₁)}{N₂ : NormalProto′ (nf ⊕ f₂ T₂)}
--   → T₁ <: T₂
--   → N₁ <:ₚ′ N₂

complete-algₚ : ∀ {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto (nf ⊕ f₁ T₁)}{N₂ : NormalProto (nf ⊕ f₂ T₂)}
  → T₁ <: T₂
  → N₁ <:ₚ N₂

complete-algₚ-inverted : ∀ {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto (t-minus (nf ⊕ f₁ T₁))}{N₂ : NormalProto (t-minus (nf ⊕ f₂ T₂))}
  → T₁ <: T₂
  → N₂ <:ₚ N₁

complete-<<:ₚ : ∀ {⊙} {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto (nf ⊕ f₁ T₁)}{N₂ : NormalProto (nf ⊕ f₂ T₂)}
  → T₁ <<:[ ⊙ ] T₂
  → N₁ <<:ₚ[ ⊙ ] N₂

complete-<<:ₚ {⊙ = ⊕} T₁<<:T₂ = complete-algₚ T₁<<:T₂
complete-<<:ₚ {⊙ = ⊝} T₁<<:T₂ = complete-algₚ T₁<<:T₂
complete-<<:ₚ {⊙ = ⊘} T₁<<:T₂ = nf-complete _ _ T₁<<:T₂

complete-algₚ-inverted {f₁ = f₁} {f₂} {N₁} {N₂} <:-refl
  rewrite dual-all-irrelevant {⊕} f₁ f₂ | np-unique N₁ N₂ = <:ₚ-refl N₂
complete-algₚ-inverted {N₁ = N₁} {N₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃)
  using N₂ ← nf-normal-proto-inverted T₂
  using N₁<:N₂ ← complete-algₚ-inverted{N₁ = N₁}{N₂ = N₂} T₁<:T₂
  using N₂<:N₃ ← complete-algₚ-inverted {N₁ = N₂}{N₂ = N₃} T₂<:T₃ = <:ₚ-trans N₂<:N₃ N₁<:N₂
complete-algₚ-inverted {N₁ = N-Minus (N-Up N₁)} {N-Minus (N-Up N₂)} (<:-up T₁<:T₂) = <:ₚ-minus (<:ₚ′-up (complete-algₜ T₁<:T₂))
complete-algₚ-inverted {N₁ = N-Minus (N-ProtoP N₁)} {N-Minus (N-ProtoP N₂)} (<:-proto #c₁⊆#c₂ T₁<<:T₂) = <:ₚ-minus (<:ₚ′-proto #c₁⊆#c₂ (complete-<<:ₚ T₁<<:T₂))
complete-algₚ-inverted (<:-minus {T₂} {T₁} T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
        | t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-algₚ T₁<:T₂
complete-algₚ-inverted (<:-minus-minus-l {T₁} T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-algₚ-inverted T₁<:T₂
complete-algₚ-inverted (<:-minus-minus-r {T₂ = T₂} T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-algₚ-inverted T₁<:T₂

complete-algₚ{f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-refl 
  rewrite dual-all-irrelevant {⊕} f₁ f₂ | np-unique N₁ N₂ = <:ₚ-refl N₂
complete-algₚ {N₁ = N₁} {N₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃)
  using N₂ ← nf-normal-proto T₂
  using N₁<:N₂ ← complete-algₚ{N₁ = N₁}{N₂ = N₂} T₁<:T₂
  using N₂<:N₃ ← complete-algₚ{N₁ = N₂}{N₂ = N₃} T₂<:T₃    
  = <:ₚ-trans N₁<:N₂ N₂<:N₃
complete-algₚ {N₁ = N-Normal (N-Up N₁)} {N-Normal (N-Up N₂)} (<:-up T₁<:T₂)
  = <:ₚ-plus (<:ₚ′-up (complete-algₜ T₁<:T₂))
complete-algₚ {N₁ = N-Normal (N-ProtoP N₁)} {N-Normal (N-ProtoP N₂)} (<:-proto #c₁⊆#c₂ T₁<<:T₂)
  = <:ₚ-plus (<:ₚ′-proto #c₁⊆#c₂ (complete-<<:ₚ T₁<<:T₂))
complete-algₚ (<:-minus T₁<:T₂) = complete-algₚ-inverted T₁<:T₂
complete-algₚ (<:-minus-minus-l {T₁} T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-algₚ T₁<:T₂
complete-algₚ (<:-minus-minus-r {T₂ = T₂} T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-algₚ T₁<:T₂

complete-algₜ {p = p}{f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-refl
  rewrite dual-all-irrelevant {p} f₁ f₂ | nt-unique N₁ N₂ = <:ₜ-refl N₂
complete-algₜ {p = p}{f₂ = f₂} {N₁ = N₁} {N₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) 
  using N₂ ← nf-normal-type p f₂ T₂
  using N₁<:N₂ ← complete-algₜ{N₁ = N₁}{N₂ = N₂} T₁<:T₂
  using N₂<:N₃ ← complete-algₜ{N₁ = N₂}{N₂ = N₃} T₂<:T₃ = <:ₜ-trans N₁<:N₂ N₂<:N₃ 
complete-algₜ {N₁ = N-Sub N₁} {N-Sub N₂} (<:-sub K≤K′ T₁<:T₂) = <:ₜ-sub (complete-algₜ T₁<:T₂)
complete-algₜ {N₁ = N-Sub N₁} {N-Sub N₂} (<:-sub-dual-l {K≤K′ = ≤k-step ≤p-refl _})
  rewrite nt-unique N₁ N₂ = <:ₜ-sub (<:ₜ-refl N₂)
complete-algₜ {N₁ = N-Sub N₁} {N-Sub N₂} (<:-sub-dual-r {K≤K′ = ≤k-step ≤p-refl _})
  rewrite nt-unique N₁ N₂ = <:ₜ-sub (<:ₜ-refl N₂)
complete-algₜ {N₁ = N-Arrow N₁ N₂} {N-Arrow N₃ N₄} (<:-fun T₁<:T₂ T₁<:T₃) = <:ₜ-arrow (complete-algₜ T₁<:T₂) (complete-algₜ T₁<:T₃)
complete-algₜ {N₁ = N-ProtoD N₁} {N-ProtoD N₂} (<:-protoD T₁<:T₂) = <:ₜ-data (complete-algₜ T₁<:T₂)
complete-algₜ {N₁ = N-Poly N₁} {N-Poly N₂} (<:-all T₁<:T₂) = <:ₜ-poly (complete-algₜ T₁<:T₂)
complete-algₜ {p = p}{f₁ = f₁}{f₂ = f₂} {N₁ = N₁@(N-Msg p₁ NP NS)}{N₂ = N₂} (<:-neg-l {p₂} {T} {S} T₁<:T₂)
  with nf-normal-type p d?S (T-Msg (invert p₂) T S)
... |  N₁′
  with dual-all-irrelevant f₁ (const D-S)
... | refl
  using N₁′<:N₂ ← complete-algₜ {N₁ = N₁′}{N₂ = N₂} T₁<:T₂
  with begin
             t-msg (mult p p₂) (t-minus (nf ⊕ d?⊥ T)) (nf p (const D-S) S)
           ≡⟨ t-msg-minus {p = mult p p₂} (nf ⊕ d?⊥ T) ⟩
             t-msg (invert (mult p p₂)) (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)
           ≡⟨ cong (λ ⊙ → t-msg ⊙ (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)) (invert-mult-⊙ p₂ {p}) ⟩
             t-msg (mult p (invert p₂)) (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)
           ≡⟨ refl ⟩
             T-Msg (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₁)
               (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₂)
               (nf p (λ _ → D-S) S)
       ∎
... | t-eq
  = <:ₜ-trans (<:ₜ-eq-ty N₁ N₁′ t-eq) N₁′<:N₂
complete-algₜ {p = p}{f₁ = f₁}{f₂ = f₂} {N₁ = N₁} {N₂ = N₂@(N-Msg p₁ NP NS)} (<:-neg-r {p = p₂} {T} {S} T₁<:T₂)
  with nf-normal-type p d?S (T-Msg (invert p₂) T S)
... | N₂′
  with dual-all-irrelevant f₂ (const D-S)
... | refl
  using N₁<:N₂′ ← complete-algₜ {N₁ = N₁} {N₂ = N₂′} T₁<:T₂
  with begin
             t-msg (mult p p₂) (t-minus (nf ⊕ d?⊥ T)) (nf p (const D-S) S)
           ≡⟨ t-msg-minus {p = mult p p₂} (nf ⊕ d?⊥ T) ⟩
             t-msg (invert (mult p p₂)) (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)
           ≡⟨ cong (λ ⊙ → t-msg ⊙ (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)) (invert-mult-⊙ p₂ {p}) ⟩
             t-msg (mult p (invert p₂)) (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)
           ≡⟨ refl ⟩
             T-Msg (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₁)
               (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₂)
               (nf p (λ _ → D-S) S)
       ∎
... | t-eq
  = <:ₜ-trans N₁<:N₂′ (<:ₜ-eq-ty N₂′ N₂ (sym t-eq))
-- complete-algₜ {p = p} {T₁ = T-Dual _ T₁} {T₂ = T-Dual _ T₂} {N₁ = N₁} {N₂} (<:-dual-lr d T₁<:T₂) = {!complete-algₜ {p = invert p} {T₁ = T₂}{T₂ = T₁} {N₁ = N₂} {N₂ = N₁} T₁<:T₂ !}
complete-algₜ {p = p} (<:-dual-dual-l d T₁<:T₂)
  rewrite invert-involution {p} = complete-algₜ T₁<:T₂
complete-algₜ {p = p} (<:-dual-dual-r d T₁<:T₂)
  rewrite invert-involution {p} = complete-algₜ T₁<:T₂

complete-algₜ {p = p}{f₁ = f₁}{f₂ = f₂} {N₁ = N₁@(N-Msg p₁ NP NS)} {N₂} (<:-dual-msg-l {p = p₂}{T = T}{S = S} T₁<:T₂)
    with nf-normal-type p d?S (T-Msg (invert p₂) T (T-Dual D-S S))
... | N₁′
    using N₁′<:N₂ ← complete-algₜ {f₁ = const D-S} {N₁ = N₁′} {N₂ = N₂} T₁<:T₂
    with begin
           (t-msg (mult (invert p) p₂) (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S))
         ≡⟨ cong (λ ⊙ → t-msg ⊙ (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S)) (mult-invert-invert p p₂) ⟩
           t-msg (mult p (invert p₂)) (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S)  
         ≡⟨ refl ⟩
           (T-Msg (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₁) (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₂) (nf (invert p) (λ x₁ → D-S) S))
         ∎
... | t-eq
  = <:ₜ-trans (<:ₜ-eq-ty N₁ N₁′ t-eq) N₁′<:N₂

complete-algₜ {p = p}{f₁ = f₁}{f₂ = f₂}{N₁ = N₁} {N₂@(N-Msg p₁ NP NS)} (<:-dual-msg-r {p = p₂}{T = T}{S = S} T₁<:T₂)
    with nf-normal-type p d?S (T-Msg (invert p₂) T (T-Dual D-S S))
... | N₂′
    using N₁<:N₂′ ← complete-algₜ {f₂ = const D-S} {N₁ = N₁} {N₂ = N₂′} T₁<:T₂
    with begin
           (t-msg (mult (invert p) p₂) (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S))
         ≡⟨ cong (λ ⊙ → t-msg ⊙ (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S)) (mult-invert-invert p p₂) ⟩
           t-msg (mult p (invert p₂)) (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S)  
         ≡⟨ refl ⟩
           (T-Msg (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₁) (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₂) (nf (invert p) (λ x₁ → D-S) S))
         ∎
... | t-eq
  = <:ₜ-trans N₁<:N₂′ (<:ₜ-eq-ty N₂′ N₂ (sym t-eq))
complete-algₜ {N₁ = N-End} {N-End} <:-dual-end-l = <:ₜ-end
complete-algₜ {N₁ = N-End} {N-End} <:-dual-end-r = <:ₜ-end
complete-algₜ {p = p} {f₁ = f₁}{f₂ = f₂} {N₁ = N-Msg p₁ NT₁ NS₁} {N-Msg p₂ NT₂ NS₂} (<:-msg {T₁ = T₁}{p = p₃} {T₂ = T₂} T₁<<:T₂ S₁<:S₂)
  rewrite t-loop-sub-<<: p₃ (mult p p₃) T₁<<:T₂
  = <:ₜ-msg (complete-<<:ₚ {f₁ = d?⊥}{f₂ = d?⊥} {N₁ = NT₁} {N₂ = NT₂} {!!}) (complete-algₜ S₁<:S₂)


--------------------------------------------------------------------------------

-- complete-algₜ : ∀ {T₁ T₂ : Ty Δ (KV pk m)} {N₁ : NormalTy T₁}{N₂ : NormalTy T₂}
--   → T₁ <: T₂ → N₁ <:ₜ N₂
-- complete-algₜ {N₁ = N₁} {N₂} <:-refl rewrite nt-unique N₁ N₂ = <:ₜ-refl N₂
-- complete-algₜ (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃)
--   using T₂′ ← nf ⊕ d?⊥ T₂
--   with  nf-normal-type ⊕ d?⊥ T₂ | nf-sound+ {f = d?⊥}T₂
-- ... | N₂ | nf≡T₂
--   using T₂′<:T₂ , T₂<:T₂′ ← conv⇒subty T₂′ T₂ nf≡T₂ = {!!}
-- -- <:ₜ-trans (complete-algₜ T₁<:T₂) (complete-algₜ T₂<:T₃)
-- -- this is more complex: T₂ is not necessarily normalized!
-- -- hence: normalize T₂ → T₂′, we have T₁ <: T₂ and T₂ ≡ T₂′ ⇒ T₁ <: T₂′ and in the same manner T₂′ <: T₃
-- -- now we have suitable arguments for complete-algₜ!
-- complete-algₜ {N₁ = N-Sub N₁} {N-Sub N₂} (<:-sub K≤K′ T₁<:T₂) = <:ₜ-sub (complete-algₜ T₁<:T₂)
-- complete-algₜ {N₁ = N-Var ()} {N-Var x₁} <:-sub-dual-l
-- complete-algₜ {N₁ = N-Var ()} {N-Sub N₂} <:-sub-dual-l
-- complete-algₜ {N₁ = N-Var ()} {N-Var x₁} <:-sub-dual-r
-- complete-algₜ {N₁ = N-Sub N₁} {N-Var ()} <:-sub-dual-r
-- complete-algₜ {N₁ = N-Arrow N₁ N₂} {N-Arrow N₃ N₄} (<:-fun T₁<:T₂ T₁<:T₃) = <:ₜ-arrow (complete-algₜ T₁<:T₂) (complete-algₜ T₁<:T₃)
-- complete-algₜ {N₁ = N-ProtoD N₁} {N-ProtoD N₂} (<:-protoD T₁<:T₂) = <:ₜ-data (complete-algₜ T₁<:T₂)
-- complete-algₜ {N₁ = N-Poly N₁} {N-Poly N₂} (<:-all T₁<:T₂) = <:ₜ-poly (complete-algₜ T₁<:T₂)
-- complete-algₜ {N₁ = N₁} {N₂} (<:-neg-l T₁<:T₂) = {!!}
-- complete-algₜ (<:-neg-r T₁<:T₂) = {!!}
-- complete-algₜ {N₁ = N-Var (NV-Dual d₁ x)} {N-Var (NV-Dual d₂ x₁)} (<:-dual-lr d T₁<:T₂) = {!<:ₜ-var!}
-- complete-algₜ {N₁ = N₁} {N₂} (<:-dual-dual-l d T₁<:T₂) = {!N₁ N₂!}
-- complete-algₜ {N₁ = N₁} {N₂} (<:-dual-dual-r d T₁<:T₂) = {!!}
-- complete-algₜ (<:-dual-msg-l T₁<:T₂) = {!!}
-- complete-algₜ (<:-dual-msg-r T₁<:T₂) = {!!}
-- complete-algₜ {N₁ = N-Var x} {N-Var ()} <:-dual-end-l
-- complete-algₜ {N₁ = N-Var ()} {N-End} <:-dual-end-l
-- complete-algₜ {N₁ = N-End} {N-Var ()} <:-dual-end-r
-- complete-algₜ {N₁ = N-Msg p₁ P₁ N₁} {N-Msg p₂ P₂ N₂} (<:-msg P₁<<:P₂ T₁<:T₂) = <:ₜ-msg {!!} (complete-algₜ T₁<:T₂)

-- subtyping implies conversion
-- not possible to prove with a transitivity rule...

alg-subty⇒conv :  ∀ {T₁ T₂ : Ty Δ (KV pk m)} {N₁ : NormalTy T₁}{N₂ : NormalTy T₂}
    → N₁ <:ₜ N₂ → N₂ <:ₜ N₁ → T₁ ≡ T₂
alg-subproto⇒conv : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto T₁}{N₂ : NormalProto T₂}
    → N₁ <:ₚ N₂ → N₂ <:ₚ N₁ → T₁ ≡ T₂
alg-subproto′⇒conv : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto′ T₁}{N₂ : NormalProto′ T₂}
    → N₁ <:ₚ′ N₂ → N₂ <:ₚ′ N₁ → T₁ ≡ T₂

alg-subty⇒conv <:ₜ-var <:ₜ-var = refl
alg-subty⇒conv <:ₜ-base <:ₜ-base = refl
alg-subty⇒conv (<:ₜ-arrow N₁<:N₂ N₁<:N₃) (<:ₜ-arrow N₂<:N₁ N₂<:N₂) = cong₂ (T-Arrow _) (alg-subty⇒conv N₂<:N₁ N₁<:N₂) (alg-subty⇒conv N₁<:N₃ N₂<:N₂)
alg-subty⇒conv (<:ₜ-poly N₁<:N₂) (<:ₜ-poly N₂<:N₁) = cong T-Poly (alg-subty⇒conv N₁<:N₂ N₂<:N₁)
alg-subty⇒conv (<:ₜ-sub N₁<:N₂) (<:ₜ-sub N₂<:N₁) = cong (T-Sub _) (alg-subty⇒conv N₁<:N₂ N₂<:N₁)
alg-subty⇒conv <:ₜ-end <:ₜ-end = refl
alg-subty⇒conv (<:ₜ-msg {p = ⊕} NP₁<<:NP₂ N₁<:N₂) (<:ₜ-msg NP₂<<:NP₁ N₂<:N₁) = cong₂ (T-Msg _) (alg-subproto⇒conv NP₂<<:NP₁ NP₁<<:NP₂) (alg-subty⇒conv N₁<:N₂ N₂<:N₁)
alg-subty⇒conv (<:ₜ-msg {p = ⊝} NP₁<<:NP₂ N₁<:N₂) (<:ₜ-msg NP₂<<:NP₁ N₂<:N₁) = cong₂ (T-Msg _) (alg-subproto⇒conv NP₁<<:NP₂ NP₂<<:NP₁) (alg-subty⇒conv N₁<:N₂ N₂<:N₁)
alg-subty⇒conv (<:ₜ-data N₁<:N₂) (<:ₜ-data N₂<:N₁) = cong T-ProtoD (alg-subty⇒conv N₁<:N₂ N₂<:N₁)

alg-subproto⇒conv (<:ₚ-plus N₁<:N₂) (<:ₚ-plus N₂<:N₁) = alg-subproto′⇒conv N₁<:N₂ N₂<:N₁
alg-subproto⇒conv (<:ₚ-minus N₂<:N₁) (<:ₚ-minus N₁<:N₂) = cong T-Minus (alg-subproto′⇒conv N₁<:N₂ N₂<:N₁)

alg-subproto′⇒conv (<:ₚ′-proto {⊙ = ⊕} #c₁⊆#c₂ P₁<<:P₂) (<:ₚ′-proto #c₂⊆#c₁ P₂<<:P₁) = cong₂ (λ a b → T-ProtoP a ⊕ b) (⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁) (alg-subproto⇒conv P₁<<:P₂ P₂<<:P₁)
alg-subproto′⇒conv (<:ₚ′-proto {⊙ = ⊝} #c₁⊆#c₂ P₁<<:P₂) (<:ₚ′-proto #c₂⊆#c₁ P₂<<:P₁) = cong₂ (λ a b → T-ProtoP a ⊝ b) (⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁) (alg-subproto⇒conv P₂<<:P₁ P₁<<:P₂)
alg-subproto′⇒conv (<:ₚ′-proto {⊙ = ⊘} #c₁⊆#c₂ P₁<<:P₂) (<:ₚ′-proto #c₂⊆#c₁ P₂<<:P₁) = cong₂ (λ a b → T-ProtoP a ⊘ b) (⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁) P₁<<:P₂
alg-subproto′⇒conv (<:ₚ′-up N₁<:N₂) (<:ₚ′-up N₂<:N₁) = cong T-Up (alg-subty⇒conv N₁<:N₂ N₂<:N₁)
alg-subproto′⇒conv <:ₚ′-var <:ₚ′-var = refl

{- TODO:
subty⇒conv : {T₁ T₂ : Ty Δ K} → T₁ <: T₂ → T₂ <: T₁ → T₁ ≡c T₂
subty⇒conv {K = KV x x₁}{T₁ = T₁}{T₂ = T₂} T₁<:T₂ T₂<:T₁
  using N₁<:N₂ ← complete-algₜ {N₁ = {!nf-normal-type ⊕ d?⊥ T₁ !}}T₁<:T₂
  using N₂<:N₁ ← complete-algₜ T₂<:T₁ = {! !}
subty⇒conv {K = KP} T₁<:T₂ T₂<:T₁ = {!!}

-}
