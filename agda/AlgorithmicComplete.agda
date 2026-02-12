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
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; cong-app; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Function using (const)

module AlgorithmicComplete  where

open import Util
open import Kinds
open import Duality
open import Types
open import Subtyping
open import SubtypingProperties
open import AlgorithmicSubtyping

-- algorithmic subtyping is complete


complete-algₚ : ∀ {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto (nf ⊕ f₁ T₁)}{N₂ : NormalProto (nf ⊕ f₂ T₂)}
  → T₁ <: T₂
  → N₁ <:ₚ N₂

complete-algₚ-inverted : ∀ {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto (t-minus (nf ⊕ f₁ T₁))}{N₂ : NormalProto (t-minus (nf ⊕ f₂ T₂))}
  → T₁ <: T₂
  → N₂ <:ₚ N₁

-- complete-algₚ′ : ∀ {T₁ T₂ : Ty Δ KP}
--   {f₁ f₂} {N₁ : NormalProto′ (nf ⊕ f₁ T₁)}{N₂ : NormalProto′ (nf ⊕ f₂ T₂)}
--   → T₁ <: T₂
--   → N₁ <:ₚ′ N₂

complete-<<:ₚ : ∀ {⊙} {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto (nf ⊕ f₁ T₁)}{N₂ : NormalProto (nf ⊕ f₂ T₂)}
  → T₁ <<:[ ⊙ ] T₂
  → N₁ <<:ₚ[ ⊙ ] N₂

complete-<<:ₚ′ : ∀ {⊙} {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto′ (nf ⊕ f₁ T₁)}{N₂ : NormalProto′ (nf ⊕ f₂ T₂)}
  → T₁ <<:[ injᵥ ⊙ ] T₂
  → N₁ <<:ₚ′[ injᵥ ⊙ ] N₂

complete-<<:ₚ′-inverted : ∀ {⊙} {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto′ (t-minus (nf ⊕ f₁ T₁))}{N₂ : NormalProto′ (t-minus (nf ⊕ f₂ T₂))}
  → T₁ <<:[ injᵥ ⊙ ] T₂
  → N₂ <<:ₚ′[ injᵥ ⊙ ] N₁

complete-algₜ : ∀ {p : Polarity} {T₁ T₂ : Ty Δ (KV pk m)}
  {f₁ f₂} {N₁ : NormalTy (nf p f₁ T₁)}{N₂ : NormalTy (nf p f₂ T₂)}
  → T₁ <: T₂
  → N₁ <<:ₜ[ p ] N₂

----

complete-algₚ {T₁ = T₁} {T₃} {f₁} {f₂} {N₁} {N₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃)
  using N₂ ← nf-normal-proto T₂
  rewrite dual-all-irrelevant f₁ d?⊥ | dual-all-irrelevant f₂ d?⊥
  = <:ₚ-trans (complete-algₚ {N₁ = N₁} {N₂ = N₂} T₁<:T₂) (complete-algₚ {N₁ = N₂} {N₂ = N₃} T₂<:T₃)
complete-algₚ {T₁ = T₁} {T₂} {f₁} {f₂} {N-Normal N-Var} {N-Normal N-Var} <:-var = <:ₚ-plus <:ₚ′-var
complete-algₚ {T₁ = T₁} {T₂} {f₁} {f₂} {N-Normal (N-Up N₁)} {N-Normal (N-Up N₂)} (<:-up T₁<:T₂) = <:ₚ-plus (<:ₚ′-up (complete-algₜ {N₁ = N₁}{N₂ = N₂} T₁<:T₂))
complete-algₚ {T₁ = T₁} {T₂} {f₁} {f₂} {N-Normal (N-ProtoP N₁)} {N-Normal (N-ProtoP N₂)} (<:-proto #c⊆#d T₁<<:T₂) = <:ₚ-plus (<:ₚ′-proto #c⊆#d (complete-<<:ₚ {N₁ = N₁} {N₂ = N₂} T₁<<:T₂))
complete-algₚ {T₁ = T-Minus T₁} {T-Minus T₂} {f₁} {f₂} {N₁} {N₂} (<:-minus T₁<:T₂) = complete-algₚ-inverted {N₁ = N₂} {N₂ = N₁} T₁<:T₂
complete-algₚ {T₁ = T-Minus (T-Minus T₁)} {T₂} {f₁} {f₂} {N₁} {N₂} (<:-minus-minus-l T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-algₚ {N₁ = N₁} {N₂ = N₂} T₁<:T₂
complete-algₚ {T₁ = T₁} {T-Minus (T-Minus T₂)} {f₁} {f₂} {N₁} {N₂} (<:-minus-minus-r T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-algₚ {N₁ = N₁} {N₂ = N₂} T₁<:T₂

----

complete-algₚ-inverted {T₁ = T₁} {T₃} {f₁} {f₂} {N₁} {N₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃)
  using N₂ ← nf-normal-proto-inverted T₂
  rewrite dual-all-irrelevant f₁ d?⊥ | dual-all-irrelevant f₂ d?⊥
   = <:ₚ-trans (complete-algₚ-inverted {N₁ = N₂} {N₂ = N₃} T₂<:T₃) (complete-algₚ-inverted {N₁ = N₁} {N₂ = N₂} T₁<:T₂)
complete-algₚ-inverted {T₁ = T₁} {T₂} {f₁} {f₂} {N-Minus N-Var} {N-Minus N-Var} <:-var = <:ₚ-minus <:ₚ′-var
complete-algₚ-inverted {T₁ = T₁} {T₂} {f₁} {f₂} {N-Minus (N-Up N₁)} {N-Minus (N-Up N₂)} (<:-up T₁<:T₂) = <:ₚ-minus (<:ₚ′-up (complete-algₜ {N₁ = N₁} {N₂ = N₂} T₁<:T₂))
complete-algₚ-inverted {T₁ = T₁} {T₂} {f₁} {f₂} {N-Minus (N-ProtoP N₁)} {N-Minus (N-ProtoP N₂)} (<:-proto #c⊆#d T₁<<:T₂) = <:ₚ-minus (<:ₚ′-proto #c⊆#d (complete-<<:ₚ {N₁ = N₁} {N₂ = N₂} T₁<<:T₂))
complete-algₚ-inverted {T₁ = T-Minus T₁} {T-Minus T₂} {f₁} {f₂} {N₁} {N₂} (<:-minus T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁) |  t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-algₚ {N₁ = N₂} {N₂ = N₁} T₁<:T₂
complete-algₚ-inverted {T₁ = T-Minus (T-Minus T₁)} {T₂} {f₁} {f₂} {N₁} {N₂} (<:-minus-minus-l T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-algₚ-inverted {N₁ = N₁}{N₂ = N₂} T₁<:T₂
complete-algₚ-inverted {T₁ = T₁} {T-Minus (T-Minus T₂)} {f₁} {f₂} {N₁} {N₂} (<:-minus-minus-r T₁<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-algₚ-inverted {N₁ = N₁}{N₂ = N₂} T₁<:T₂

----

complete-<<:ₚ′-inverted {⊙ = ⊕} {T₁} {T₃} {N₁ = N₁} {N₃} (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃)
  using N₂ ← normal-proto′-<:-minus _ _ T₂<<:T₃ (subst (λ f → NormalProto′ (t-minus (nf ⊕ f T₁))) (dual-all-irrelevant _ _) N₁)
  using N₁<:N₂ ← complete-<<:ₚ′-inverted {⊙ = ⊝}{N₁ = N₂}{N₂ = N₁} T₂<<:T₃
  using N₂<:N₃ ← complete-<<:ₚ′-inverted {⊙ = ⊝}{N₁ = N₃}{N₂ = N₂} T₁<<:T₂
  = <:ₚ′-trans N₁<:N₂ N₂<:N₃ 
complete-<<:ₚ′-inverted {⊙ = ⊕} {T-Minus T₁} {T-Minus T₂} {N₁ = N₁} {N₂} (<:-minus T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  | t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′ {⊙ = ⊝}{N₁ = N₁} {N₂ = N₂} T₁<<:T₂
complete-<<:ₚ′-inverted {⊙ = ⊕} {T₁} {T-Minus (T-Minus T₂)} {N₁ = N₁} {N₂} (<:-minus-minus-l T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′-inverted {⊙ = ⊕} {N₁ = N₁} {N₂ = N₂} T₁<<:T₂
complete-<<:ₚ′-inverted {⊙ = ⊕} {T-Minus (T-Minus T₁)} {T₂} {N₁ = N₁} {N₂} (<:-minus-minus-r T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-<<:ₚ′-inverted {⊙ = ⊕} {N₁ = N₁} {N₂ = N₂} T₁<<:T₂

complete-<<:ₚ′-inverted {⊙ = ⊝} {T₁} {T₃} {N₁ = N₁} {N₃} (<:-trans T₁<<:T₂ T₂<<:T₃)
  using N₂ ← normal-proto′-<:-minus _ _ T₂<<:T₃ (subst (λ f → NormalProto′ (t-minus (nf ⊕ f T₃))) (dual-all-irrelevant _ _) N₃)
  using N₃<:N₂ ← complete-<<:ₚ′-inverted {⊙ = ⊕} {N₁ = N₃}{N₂ = N₂} T₂<<:T₃
  using N₂<:N₁ ← complete-<<:ₚ′-inverted {⊙ = ⊕} {N₁ = N₂}{N₂ = N₁} T₁<<:T₂
  = <:ₚ′-trans N₃<:N₂ N₂<:N₁
complete-<<:ₚ′-inverted {⊙ = ⊝} {T-Minus T₁} {T-Minus T₂} {N₁ = N₁} {N₂} (<:-minus T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  | t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′ {⊙ = ⊕} {N₁ = N₁} {N₂ = N₂} T₁<<:T₂
complete-<<:ₚ′-inverted {⊙ = ⊝} {T-Minus (T-Minus T₁)} {T₂} {N₁ = N₁} {N₂} (<:-minus-minus-l T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-<<:ₚ′-inverted {⊙ = ⊝} {N₁ = N₁}{N₂ = N₂} T₁<<:T₂
complete-<<:ₚ′-inverted {⊙ = ⊝} {T₁} {T-Minus (T-Minus T₂)} {N₁ = N₁} {N₂} (<:-minus-minus-r T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′-inverted {⊙ = ⊝} {N₁ = N₁}{N₂ = N₂} T₁<<:T₂

complete-<<:ₚ′ {⊙ = ⊕} {T₁} {T₃} {N₁ = N₁} {N₃} (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃)
  using N₂ ← normal-proto′-<: _ _ T₁<<:T₂ (subst (λ f → NormalProto′ (nf ⊕ f T₃)) (dual-all-irrelevant _ _) N₃)
  using N₃<:N₂ ← complete-<<:ₚ′ {⊙ = ⊝} {T₁ = T₃}{T₂ = T₂}{N₁ = N₃}{N₂ = N₂} T₁<<:T₂
  using N₁<:N₂ ← complete-<<:ₚ′ {⊙ = ⊝} {T₁ = T₂}{T₂ = T₁}{N₁ = N₂}{N₂ = N₁} T₂<<:T₃
  = <:ₚ′-trans N₃<:N₂ N₁<:N₂
complete-<<:ₚ′ {⊙ = ⊕} {N₁ = N-Var} {N-Var} <:-var = <:ₚ′-var
complete-<<:ₚ′ {⊙ = ⊕} {N₁ = N-Up N₁} {N-Up N₂} (<:-up T₁<<:T₂) = <:ₚ′-up (complete-algₜ {p = ⊕} {N₁ = N₂} {N₂ = N₁} T₁<<:T₂)
complete-<<:ₚ′ {⊙ = ⊕} {N₁ = N-ProtoP N₁} {N-ProtoP N₂} (<:-proto {⊙ = ⊙} #c⊆#d T₁<<:T₂) = <:ₚ′-proto #c⊆#d (complete-<<:ₚ {⊙ = ⊙} T₁<<:T₂)
complete-<<:ₚ′ {⊙ = ⊕} {N₁ = N₁} {N₂} (<:-minus T₁<<:T₂) = complete-<<:ₚ′-inverted {⊙ = ⊝} T₁<<:T₂
complete-<<:ₚ′ {⊙ = ⊕} {N₁ = N₁} {N₂} (<:-minus-minus-l {T₁} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-<<:ₚ′ {⊙ = ⊕} T₁<<:T₂
complete-<<:ₚ′ {⊙ = ⊕} {N₁ = N₁} {N₂} (<:-minus-minus-r {T₂ = T₂} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′ {⊙ = ⊕} T₁<<:T₂

complete-<<:ₚ′ {⊙ = ⊝} {T₁} {T₃} {N₁ = N₁} {N₃} (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃)
  using N₂ ← normal-proto′-<: _ _ T₁<<:T₂ (subst (λ f → NormalProto′ (nf ⊕ f T₁)) (dual-all-irrelevant _ _) N₁)
  using N₁<:N₂ ← complete-<<:ₚ′ {⊙ = ⊝} {T₁ = T₁}{T₂ = T₂}{N₁ = N₁}{N₂ = N₂} T₁<<:T₂
  using N₂<:N₃ ← complete-<<:ₚ′ {⊙ = ⊝} {T₁ = T₂}{T₂ = T₃}{N₁ = N₂}{N₂ = N₃} T₂<<:T₃
  = <:ₚ′-trans N₁<:N₂ N₂<:N₃
complete-<<:ₚ′ {⊙ = ⊝} {N₁ = N-Var} {N-Var} <:-var = <:ₚ′-var
complete-<<:ₚ′ {⊙ = ⊝} {N₁ = N-Up N₁} {N-Up N₂} (<:-up T₁<<:T₂) = <:ₚ′-up (complete-algₜ {p = ⊕} {N₁ = N₁} {N₂ = N₂} T₁<<:T₂)
complete-<<:ₚ′ {⊙ = ⊝} {N₁ = N-ProtoP N₁} {N-ProtoP N₂} (<:-proto {⊙ = ⊙} #c⊆#d T₁<<:T₂) = <:ₚ′-proto #c⊆#d (complete-<<:ₚ {⊙ = ⊙} T₁<<:T₂)
complete-<<:ₚ′ {⊙ = ⊝} {N₁ = N₁} {N₂} (<:-minus T₁<<:T₂) = complete-<<:ₚ′-inverted {⊙ = ⊕} T₁<<:T₂
complete-<<:ₚ′ {⊙ = ⊝} {N₁ = N₁} {N₂} (<:-minus-minus-l {T₁} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-<<:ₚ′ {⊙ = ⊝} T₁<<:T₂
complete-<<:ₚ′ {⊙ = ⊝} {N₁ = N₁} {N₂} (<:-minus-minus-r {T₂ = T₂} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′ {⊙ = ⊝} T₁<<:T₂

----

complete-<<:ₚ {⊙ = ⊕} T₁<<:T₂ = complete-algₚ T₁<<:T₂
complete-<<:ₚ {⊙ = ⊝} T₁<<:T₂ = complete-algₚ T₁<<:T₂
complete-<<:ₚ {⊙ = ⊘} T₁<<:T₂ = nf-complete _ _ T₁<<:T₂


complete-algₜ {p = ⊕} {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ N₁ NS₁} {N-Msg p₂ N₂ NS₂} (<:-msg {T₁ = T₁} {p = p₃} {T₂ = T₂} T₁<<:T₂ S₁<:S₂)
  rewrite t-loop-sub-<<: p₃ p₃ T₁<<:T₂
  using eq₁ ← (nfp′-idempotent N₁)
  using eq₂ ← (nfp′-idempotent N₂)
  with       complete-<<:ₚ′{⊙ = (t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₁)}
                           {T₁ = t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₂}{T₂ = t-loop p₃ (nf ⊕ d?⊥ T₂) .proj₂}
                           {N₁ = subst NormalProto′ (sym eq₁) N₁}{N₂ = subst NormalProto′ (sym eq₂) N₂}
                           (lemma-sub-loop {p₃ = p₃} T₁<<:T₂)
... | ih
  rewrite t-loop-sub-<<: p₃ p₃ T₁<<:T₂
  = <:ₜ-msg (subst-<<: (sym eq₁) (sym eq₂) ih) (complete-algₜ {N₁ = NS₁} {N₂ = NS₂} S₁<:S₂)

complete-algₜ {p = ⊝} {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ N₁ NS₁} {N-Msg p₂ N₂ NS₂} (<:-msg {T₁ = T₁} {p = p₃} {T₂ = T₂} T₁<<:T₂ S₁<:S₂)
  rewrite sym (t-loop-sub-<<: p₃ (invert p₃) T₁<<:T₂)
  using eq₁ ← nfp′-idempotent N₁
  using eq₂ ← nfp′-idempotent N₂
  with complete-<<:ₚ′ {⊙ = t-loop (invert p₃) (nf ⊕ d?⊥ T₁) .proj₁}{f₁ = d?⊥}{f₂ = d?⊥} {N₁ = subst NormalProto′ (sym eq₂) N₂} {N₂ = subst NormalProto′ (sym eq₁) N₁} (lemma-sub-loop-right {p₃ = invert p₃} (<<:-invert T₁<<:T₂))
... | ih
  = <:ₜ-msg (subst-<<: (sym eq₂) (sym eq₁) ih) (complete-algₜ {N₁ = NS₁} {N₂ = NS₂} S₁<:S₂)

complete-algₜ {p = p} {T₁ = T₁} {T₃} {f₁ = f₁} {f₂} {N₁ = N₁} {N₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃)
  using N₂ ← nf-normal-type p f₁ T₂
  using N₁<<:N₂ ← complete-algₜ {T₁ = T₁}{T₂}{N₁ = N₁}{N₂ = N₂} T₁<:T₂
  using N₂<<:N₁ ← complete-algₜ {T₁ = T₂}{T₃}{N₁ = N₂}{N₂ = N₃} T₂<:T₃
  = <<:ₜ-trans N₁<<:N₂ N₂<<:N₁
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N-Sub N₁} {N-Sub N₂} (<:-sub {T₁ = T₁}{T₂ = T₂} K≤K′ T₁<:T₂)
  = <<:ₜ-sub{T₁ = T₁}{T₂ = T₂}{f₁ = λ x → dualizable-sub (f₁ x) K≤K′}{f₂ = λ x → dualizable-sub (f₂ x) K≤K′}{km≤ = K≤K′} (complete-algₜ {p = p} {N₁ = N₁}{N₂ = N₂} T₁<:T₂)
complete-algₜ {p = p} {T₁ = T-Dual D-S (T-Sub (≤k-step ≤p-refl _) T)} {T₂ = T-Sub K≤K′ (T-Dual D-S T)} {f₁ = f₁} {f₂} {N₁ = N-Sub N₁} {N-Sub N₂} (<:-sub-dual-l {T = T} {K≤K′ = K≤K′})
  rewrite nt-unique N₁ N₂
  = <<:ₜ-sub-invert {p = p}{T₁ = T}{T₂ = T}{f₁ = const D-S}{f₂ = const D-S}{km≤ = K≤K′} (<<:ₜ-refl {T = (nf (invert p) (λ x₁ → D-S) T)} N₂)
complete-algₜ {p = p} {T₁ = T-Sub K≤K′ (T-Dual D-S T)} {T₂ = T-Dual D-S (T-Sub (≤k-step ≤p-refl _) T)} {f₁ = f₁} {f₂} {N₁ = N-Sub N₁} {N-Sub N₂} <:-sub-dual-r
  rewrite nt-unique N₁ N₂
  = <<:ₜ-sub-invert {p = p}{T₁ = T}{T₂ = T}{f₁ = const D-S}{f₂ = const D-S}{km≤ = K≤K′} (<<:ₜ-refl {T = (nf (invert p) (λ x₁ → D-S) T)} N₂)
complete-algₜ {p = ⊕}{T₁ = T-Var x} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-var
  rewrite nt-unique N₁ N₂
  = <<:ₜ-refl {T = T-Var x}{⊕} N₂
complete-algₜ {p = ⊝} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-var
  rewrite dual-all-irrelevant f₁ f₂ | nt-unique N₁ N₂
  = <<:ₜ-refl {T = T-Dual _ (T-Var _)} {p = ⊝} N₂
complete-algₜ {p = ⊕} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-dual-var
  rewrite nt-unique N₁ N₂
  = <<:ₜ-refl {T = T-Dual D-S (T-Var _)} {p = ⊕} N₂
complete-algₜ {p = ⊝} {T₁ = T-Dual D-S (T-Var x)} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-dual-var
  rewrite nt-unique N₁ N₂
  = <<:ₜ-refl {T = T-Var x}{⊝} N₂
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N-Base} {N-Base} <:-base = <<:ₜ-base
complete-algₜ {p = ⊕} {f₁ = f₁} {f₂} {N₁ = N-Arrow N₁ N₃} {N-Arrow N₂ N₄} (<:-fun T₁<:T₂ T₁<:T₃) = <:ₜ-arrow (complete-algₜ {N₁ = N₂}{N₂ = N₁} T₁<:T₂) (complete-algₜ {N₁ = N₃} {N₂ = N₄} T₁<:T₃)
complete-algₜ {p = ⊝} {f₁ = f₁} {f₂} {N₁ = N-Arrow N₁ N₃} {N-Arrow N₂ N₄} (<:-fun {≤pk = ≤p-refl} T₁<:T₂ T₁<:T₃)
  with () ←  f₁ refl
complete-algₜ {p = ⊝} {f₁ = f₁} {f₂} {N₁ = N-Arrow N₁ N₃} {N-Arrow N₂ N₄} (<:-fun {≤pk = ≤p-step <p-mt} T₁<:T₂ T₁<:T₃)
  with () ← f₁ refl
complete-algₜ {p = ⊕} {f₁ = f₁} {f₂} {N₁ = N-ProtoD N₁} {N-ProtoD N₂} (<:-protoD T₁<:T₂) = <:ₜ-data (complete-algₜ {N₁ = N₁} {N₂ = N₂} T₁<:T₂)
complete-algₜ {p = ⊝} {f₁ = f₁} {f₂} {N₁ = N-ProtoD N₁} {N-ProtoD N₂} (<:-protoD T₁<:T₂)
  with () ← f₁ refl
complete-algₜ {p = ⊕} {f₁ = f₁} {f₂} {N₁ = N-Poly N₁} {N-Poly N₂} (<:-all T₁<:T₂) = <:ₜ-poly (complete-algₜ {N₁ = N₁} {N₂ = N₂} T₁<:T₂)
complete-algₜ {p = ⊝} {f₁ = f₁} {f₂} {N₁ = N-Poly N₁} {N-Poly N₂} (<:-all T₁<:T₂)
  with () ← f₁ refl
complete-algₜ {p = ⊕} {T₁ = T-Msg p₁ T₁ (T-Dual D-S S₁)} {T₂ = T-Dual D-S (T-Msg .(invert p₁) T₁ S₁)} {f₁ = f₁} {f₂} {N₁ = N-Msg p₂ NT₁ NS₁} {N-Msg p₃ NT₂ NS₂} (<:-dual-msg-l-new refl)
  rewrite invert-involution {p₁} | nt-unique NS₁ NS₂ | np′-unique NT₁ NT₂
  = <:ₜ-msg (<<:ₚ′-refl NT₂) (<:ₜ-refl NS₂)
complete-algₜ {p = ⊝} {T₁ = T-Msg p₁ T₁ (T-Dual D-S S₁)} {T₂ = T-Dual D-S (T-Msg .(invert p₁) T₁ S₁)} {f₁ = f₁} {f₂} {N₁ = N-Msg p₂ NT₁ NS₁} {N-Msg p₃ NT₂ NS₂} (<:-dual-msg-l-new refl)
  rewrite nt-unique NS₁ NS₂ | np′-unique NT₁ NT₂
  = <:ₜ-msg (<<:ₚ′-refl NT₂) (<:ₜ-refl NS₂)
complete-algₜ {p = ⊕} {T₁ = T-Dual D-S (T-Msg p₁ T S)} {T₂ = T-Msg p₁′ T (T-Dual D-S S)} {f₁ = f₁} {f₂} {N₁ = N-Msg p₂ NT₁ NS₁} {N-Msg p₃ NT₂ NS₂} (<:-dual-msg-r-new refl)
  rewrite invert-involution {p₁′} | nt-unique NS₁ NS₂ | np′-unique NT₁ NT₂
  = <:ₜ-msg (<<:ₚ′-refl NT₂) (<:ₜ-refl NS₂)
complete-algₜ {p = ⊝} {T₁ = T-Dual D-S (T-Msg p₁ T S)} {T₂ = T-Msg p₁′ T (T-Dual D-S S)} {f₁ = f₁} {f₂} {N₁ = N-Msg p₂ NT₁ NS₁} {N-Msg p₃ NT₂ NS₂} (<:-dual-msg-r-new refl)
  rewrite nt-unique NS₁ NS₂ | np′-unique NT₁ NT₂
  = <:ₜ-msg (<<:ₚ′-refl NT₂) (<:ₜ-refl NS₂)
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N-End} {N-End} <:-dual-end-l = <<:ₜ-end
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N-End} {N-End} <:-dual-end-r = <<:ₜ-end
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N-End} {N-End} <:-end = <<:ₜ-end
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-dual-dual-l-new D-S)
  rewrite invert-involution {p} | dual-all-irrelevant (const D-S) f₂ | nt-unique N₁ N₂
  = <<:ₜ-refl N₂ 
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-dual-dual-r-new D-S)
  rewrite invert-involution {p} | dual-all-irrelevant (const D-S) f₁ | nt-unique N₁ N₂
  = <<:ₜ-refl N₂
complete-algₜ {p = ⊕} {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ NP₁ NS₁} {N-Msg p₂ NP₂ NS₂} (<:-msg-minus {p₁ = p₃} {T} refl)
  rewrite t-loop-minus {p = p₃} (nf ⊕ d?⊥ T) | dual-all-irrelevant f₁ f₂ | nt-unique NS₁ NS₂ | np′-unique NP₁ NP₂
  = <:ₜ-msg (<<:ₚ′-refl NP₂) (<:ₜ-refl NS₂)
complete-algₜ {p = ⊝} {T₁ = T-Msg p (T-Minus T) S}{T₂ = T-Msg .(invert p) T S} {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ NP₁ NS₁} {N-Msg p₂ NP₂ NS₂} (<:-msg-minus {p₁ = p₃} refl)
  rewrite invert-involution {p₃}
  rewrite t-loop-minus-invert {p = p} (nf ⊕ d?⊥ T) | dual-all-irrelevant f₁ f₂ | nt-unique NS₁ NS₂ | np′-unique NP₁ NP₂
  = <:ₜ-msg (<<:ₚ′-refl NP₂) (<:ₜ-refl NS₂)
complete-algₜ {p = ⊕} {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ NP₁ NS₁} {N-Msg p₂ NP₂ NS₂} (<:-minus-msg {p₂ = p₃} {T = T} refl)
  rewrite t-loop-minus-invert {p = p₃} (nf ⊕ d?⊥ T) | dual-all-irrelevant f₁ f₂ |  nt-unique NS₁ NS₂ | np′-unique NP₁ NP₂
  = <:ₜ-msg (<<:ₚ′-refl NP₂) (<:ₜ-refl NS₂)
complete-algₜ {p = ⊝} {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ NP₁ NS₁} {N-Msg p₂ NP₂ NS₂} (<:-minus-msg {p₂ = p₃} {T = T} refl)
  rewrite invert-involution {p₃} | t-loop-minus {p = p₃} (nf ⊕ d?⊥ T) | dual-all-irrelevant f₁ f₂ |  nt-unique NS₁ NS₂ | np′-unique NP₁ NP₂
  = <:ₜ-msg (<<:ₚ′-refl NP₂) (<:ₜ-refl NS₂)


-- {- TODO:
-- subty⇒conv : {T₁ T₂ : Ty Δ K} → T₁ <: T₂ → T₂ <: T₁ → T₁ ≡c T₂
-- subty⇒conv {K = KV x x₁}{T₁ = T₁}{T₂ = T₂} T₁<:T₂ T₂<:T₁
--   using N₁<:N₂ ← complete-algₜ {N₁ = {!nf-normal-type ⊕ d?⊥ T₁ !}}T₁<:T₂
--   using N₂<:N₁ ← complete-algₜ T₂<:T₁ = {! !}
-- subty⇒conv {K = KP} T₁<:T₂ T₂<:T₁ = {!!}

-- -}
