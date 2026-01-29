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

module AlgorithmicComplete-20260126  where

open import Util
open import Kinds
open import Duality
open import Types
open import Subtyping
open import AlgorithmicSubtyping

-- algorithmic subtyping is complete

lemma-sub-<<: : {T₁ T₂ : Ty Δ KP} (T₁<<:T₂ : T₁ <<:[ ⊙ ] T₂) → nf ⊕ d?⊥ T₁ <<:[ ⊙ ] nf ⊕ d?⊥ T₂
lemma-sub-<<: {⊙ = ⊕} T₁<<:T₂ = norm-pres-sub {p = ⊕} T₁<<:T₂
lemma-sub-<<: {⊙ = ⊝} T₂<<:T₁ = norm-pres-sub {p = ⊕} T₂<<:T₁
lemma-sub-<<: {⊙ = ⊘} T₁≡cT₂ rewrite nf-complete d?⊥ d?⊥ T₁≡cT₂ = ≡c-refl

lemma-sub-loop : ∀ {p₃} {T₁ T₂ : Ty Δ KP} (T₁<<:T₂ : T₁ <<:[ injᵥ p₃ ] T₂)
  → t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₂ <<:[ injᵥ (t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₁) ] t-loop p₃ (nf ⊕ d?⊥ T₂) .proj₂
lemma-sub-loop {p₃ = ⊕} {T₁} {T₃} (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃)
  = <<:-trans (lemma-sub-loop {p₃ = ⊕} T₂<<:T₃) (subst (λ p → _ <<:[ injᵥ p ] _) (t-loop-sub-<<: ⊝ ⊕ T₂<<:T₃) (lemma-sub-loop {p₃ = ⊕} T₁<<:T₂))
lemma-sub-loop {p₃ = ⊕} <:-var = <:-var
lemma-sub-loop {p₃ = ⊕} (<:-up T₁<<:T₂) = <:-up (norm-pres-sub {p = ⊕} T₁<<:T₂)
lemma-sub-loop {p₃ = ⊕} (<:-proto #c⊆#d T₁<<:T₂) = <:-proto #c⊆#d (lemma-sub-<<: T₁<<:T₂)
lemma-sub-loop {p₃ = ⊕} (<:-minus {T₂} {T₁ = T₁} T₁<<:T₂)
  rewrite t-loop-minus {p = ⊕} (nf ⊕ d?⊥ T₁) | t-loop-minus {p = ⊕} (nf ⊕ d?⊥ T₂)
  = lemma-sub-loop {p₃ = ⊝} T₁<<:T₂
lemma-sub-loop {p₃ = ⊕} (<:-minus-minus-l {T₁} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = lemma-sub-loop {p₃ = ⊕} T₁<<:T₂
lemma-sub-loop {p₃ = ⊕} (<:-minus-minus-r {T₂ = T₂} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = lemma-sub-loop {p₃ = ⊕} T₁<<:T₂
lemma-sub-loop {p₃ = ⊝} {T₁} {T₃} (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃)
  = <<:-trans (lemma-sub-loop {p₃ = ⊝} T₁<<:T₂)
              (subst (λ p → _ <<:[ injᵥ p ] _) (sym (t-loop-sub-<<: ⊝ ⊝ T₁<<:T₂)) (lemma-sub-loop {p₃ = ⊝} T₂<<:T₃))
lemma-sub-loop {p₃ = ⊝} <:-var = <:-var
lemma-sub-loop {p₃ = ⊝} (<:-up T₁<<:T₂) = <:-up (norm-pres-sub {p = ⊕} T₁<<:T₂)
lemma-sub-loop {p₃ = ⊝} (<:-proto #c⊆#d T₁<<:T₂) = <:-proto #c⊆#d (lemma-sub-<<: T₁<<:T₂)
lemma-sub-loop {p₃ = ⊝} (<:-minus {T₂} {T₁ = T₁} T₁<<:T₂)
  rewrite t-loop-minus {p = ⊝} (nf ⊕ d?⊥ T₁) |  t-loop-minus {p = ⊝} (nf ⊕ d?⊥ T₂)
  = lemma-sub-loop {p₃ = ⊕} T₁<<:T₂
lemma-sub-loop {p₃ = ⊝} (<:-minus-minus-l {T₁} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = lemma-sub-loop {p₃ = ⊝} T₁<<:T₂
lemma-sub-loop {p₃ = ⊝} (<:-minus-minus-r {T₂ = T₂} T₁<<:T₂)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = lemma-sub-loop {p₃ = ⊝} T₁<<:T₂


complete-algₚ : ∀ {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto (nf ⊕ f₁ T₁)}{N₂ : NormalProto (nf ⊕ f₂ T₂)}
  → T₁ <: T₂
  → N₁ <:ₚ N₂

complete-algₚ-inverted : ∀ {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto (t-minus (nf ⊕ f₁ T₁))}{N₂ : NormalProto (t-minus (nf ⊕ f₂ T₂))}
  → T₁ <: T₂
  → N₂ <:ₚ N₁

complete-algₚ′ : ∀ {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto′ (nf ⊕ f₁ T₁)}{N₂ : NormalProto′ (nf ⊕ f₂ T₂)}
  → T₁ <: T₂
  → N₁ <:ₚ′ N₂

complete-<<:ₚ : ∀ {⊙} {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto (nf ⊕ f₁ T₁)}{N₂ : NormalProto (nf ⊕ f₂ T₂)}
  → T₁ <<:[ ⊙ ] T₂
  → N₁ <<:ₚ[ ⊙ ] N₂

complete-<<:ₚ′ : ∀ {⊙} {T₁ T₂ : Ty Δ KP}
  {f₁ f₂} {N₁ : NormalProto′ (nf ⊕ f₁ T₁)}{N₂ : NormalProto′ (nf ⊕ f₂ T₂)}
  → T₁ <<:[ injᵥ ⊙ ] T₂
  → N₁ <<:ₚ′[ injᵥ ⊙ ] N₂

complete-algₜ : ∀ {p : Polarity} {T₁ T₂ : Ty Δ (KV pk m)}
  {f₁ f₂} {N₁ : NormalTy (nf p f₁ T₁)}{N₂ : NormalTy (nf p f₂ T₂)}
  → T₁ <: T₂
  → N₁ <<:ₜ[ p ] N₂

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
  = <:ₜ-msg {!ih!} (complete-algₜ {N₁ = NS₁} {N₂ = NS₂} S₁<:S₂)
complete-algₜ {p = ⊝} {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ N₁ NS₁} {N-Msg p₂ N₂ NS₂} (<:-msg {T₁ = T₁} {p = p₃} {T₂ = T₂} T₁<<:T₂ S₁<:S₂) = {!!}
--   with t-loop-sub-<<: p₃ (mult p p₃) T₁<<:T₂
-- ... | p₁≡p₂

complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-trans T₁<:T₂ T₁<:T₃) = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-sub K≤K′ T₁<:T₂) = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-sub-dual-l = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-sub-dual-r = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-var = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-dual-var = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-base = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-fun T₁<:T₂ T₁<:T₃) = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-protoD T₁<:T₂) = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-all T₁<:T₂) = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-neg-l T₁<:T₂) = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-neg-r T₁<:T₂) = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-dual-dual-l D-S T₁<:T₂) = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-dual-dual-r D-S T₁<:T₂) = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-dual-msg-l T₁<:T₂) = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} (<:-dual-msg-r T₁<:T₂) = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-dual-end-l = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-dual-end-r = {!!}
complete-algₜ {p = p} {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-end = {!!}

-- -- complete-algₚ-inverted {f₁ = f₁} {f₂} {N₁} {N₂} <:-refl
-- --   rewrite dual-all-irrelevant {⊕} f₁ f₂ | np-unique N₁ N₂ = <:ₚ-refl N₂
-- complete-algₚ-inverted {f₁ = f₁} {f₂} {N₁} {N₂} <:-var
--   rewrite np-unique N₁ N₂ = <:ₚ-refl N₂
-- complete-algₚ-inverted {N₁ = N₁} {N₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃)
--   using N₂ ← nf-normal-proto-inverted T₂
--   using N₁<:N₂ ← complete-algₚ-inverted{N₁ = N₁}{N₂ = N₂} T₁<:T₂
--   using N₂<:N₃ ← complete-algₚ-inverted {N₁ = N₂}{N₂ = N₃} T₂<:T₃ = <:ₚ-trans N₂<:N₃ N₁<:N₂
-- complete-algₚ-inverted {N₁ = N-Minus (N-Up N₁)} {N-Minus (N-Up N₂)} (<:-up T₁<:T₂) = <:ₚ-minus (<:ₚ′-up (complete-algₜ T₁<:T₂))
-- complete-algₚ-inverted {N₁ = N-Minus (N-ProtoP N₁)} {N-Minus (N-ProtoP N₂)} (<:-proto #c₁⊆#c₂ T₁<<:T₂) = <:ₚ-minus (<:ₚ′-proto #c₁⊆#c₂ (complete-<<:ₚ T₁<<:T₂))
-- complete-algₚ-inverted (<:-minus {T₂} {T₁} T₁<:T₂)
--   rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
--         | t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
--   = complete-algₚ T₁<:T₂
-- complete-algₚ-inverted (<:-minus-minus-l {T₁} T₁<:T₂)
--   rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
--   = complete-algₚ-inverted T₁<:T₂
-- complete-algₚ-inverted (<:-minus-minus-r {T₂ = T₂} T₁<:T₂)
--   rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
--   = complete-algₚ-inverted T₁<:T₂

-- -- complete-algₚ{f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-refl 
-- --   rewrite dual-all-irrelevant {⊕} f₁ f₂ | np-unique N₁ N₂ = <:ₚ-refl N₂
-- complete-algₚ{f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-var
--   rewrite np-unique N₁ N₂ = <:ₚ-refl N₂
-- complete-algₚ {N₁ = N₁} {N₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃)
--   using N₂ ← nf-normal-proto T₂
--   using N₁<:N₂ ← complete-algₚ{N₁ = N₁}{N₂ = N₂} T₁<:T₂
--   using N₂<:N₃ ← complete-algₚ{N₁ = N₂}{N₂ = N₃} T₂<:T₃    
--   = <:ₚ-trans N₁<:N₂ N₂<:N₃
-- complete-algₚ {N₁ = N-Normal (N-Up N₁)} {N-Normal (N-Up N₂)} (<:-up T₁<:T₂)
--   = <:ₚ-plus (<:ₚ′-up (complete-algₜ T₁<:T₂))
-- complete-algₚ {N₁ = N-Normal (N-ProtoP N₁)} {N-Normal (N-ProtoP N₂)} (<:-proto #c₁⊆#c₂ T₁<<:T₂)
--   = <:ₚ-plus (<:ₚ′-proto #c₁⊆#c₂ (complete-<<:ₚ T₁<<:T₂))
-- complete-algₚ (<:-minus T₁<:T₂) = complete-algₚ-inverted T₁<:T₂
-- complete-algₚ (<:-minus-minus-l {T₁} T₁<:T₂)
--   rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
--   = complete-algₚ T₁<:T₂
-- complete-algₚ (<:-minus-minus-r {T₂ = T₂} T₁<:T₂)
--   rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
--   = complete-algₚ T₁<:T₂

-- -- complete-algₜ {p = p}{f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-refl
-- --   rewrite dual-all-irrelevant {p} f₁ f₂ | nt-unique N₁ N₂ = <:ₜ-refl N₂
-- complete-algₜ {p = p}{f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-var
--   rewrite dual-all-irrelevant {p} f₁ f₂ | nt-unique N₁ N₂ = <:ₜ-refl N₂
-- complete-algₜ {p = p}{f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-dual-var
--   rewrite nt-unique N₁ N₂ = <:ₜ-refl N₂
-- complete-algₜ {p = p}{f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-base
--   rewrite nt-unique N₁ N₂ = <:ₜ-refl N₂
-- complete-algₜ {p = p}{f₁ = f₁} {f₂} {N₁ = N₁} {N₂} <:-end
--   rewrite nt-unique N₁ N₂ = <:ₜ-refl N₂
-- complete-algₜ {p = p}{f₂ = f₂} {N₁ = N₁} {N₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) 
--   using N₂ ← nf-normal-type p f₂ T₂
--   using N₁<:N₂ ← complete-algₜ{N₁ = N₁}{N₂ = N₂} T₁<:T₂
--   using N₂<:N₃ ← complete-algₜ{N₁ = N₂}{N₂ = N₃} T₂<:T₃ = <:ₜ-trans N₁<:N₂ N₂<:N₃ 
-- complete-algₜ {N₁ = N-Sub N₁} {N-Sub N₂} (<:-sub K≤K′ T₁<:T₂) = <:ₜ-sub (complete-algₜ T₁<:T₂)
-- complete-algₜ {N₁ = N-Sub N₁} {N-Sub N₂} (<:-sub-dual-l {K≤K′ = ≤k-step ≤p-refl _})
--   rewrite nt-unique N₁ N₂ = <:ₜ-sub (<:ₜ-refl N₂)
-- complete-algₜ {N₁ = N-Sub N₁} {N-Sub N₂} (<:-sub-dual-r {K≤K′ = ≤k-step ≤p-refl _})
--   rewrite nt-unique N₁ N₂ = <:ₜ-sub (<:ₜ-refl N₂)
-- complete-algₜ {N₁ = N-Arrow N₁ N₂} {N-Arrow N₃ N₄} (<:-fun T₁<:T₂ T₁<:T₃) = <:ₜ-arrow (complete-algₜ T₁<:T₂) (complete-algₜ T₁<:T₃)
-- complete-algₜ {N₁ = N-ProtoD N₁} {N-ProtoD N₂} (<:-protoD T₁<:T₂) = <:ₜ-data (complete-algₜ T₁<:T₂)
-- complete-algₜ {N₁ = N-Poly N₁} {N-Poly N₂} (<:-all T₁<:T₂) = <:ₜ-poly (complete-algₜ T₁<:T₂)
-- complete-algₜ {p = p}{f₁ = f₁}{f₂ = f₂} {N₁ = N₁@(N-Msg p₁ NP NS)}{N₂ = N₂} (<:-neg-l {p₂} {T} {S} T₁<:T₂)
--   with nf-normal-type p d?S (T-Msg (invert p₂) T S)
-- ... |  N₁′
--   with dual-all-irrelevant f₁ (const D-S)
-- ... | refl
--   using N₁′<:N₂ ← complete-algₜ {N₁ = N₁′}{N₂ = N₂} T₁<:T₂
--   with begin
--              t-msg (mult p p₂) (t-minus (nf ⊕ d?⊥ T)) (nf p (const D-S) S)
--            ≡⟨ t-msg-minus {p = mult p p₂} (nf ⊕ d?⊥ T) ⟩
--              t-msg (invert (mult p p₂)) (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)
--            ≡⟨ cong (λ ⊙ → t-msg ⊙ (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)) (invert-mult-⊙ p₂ {p}) ⟩
--              t-msg (mult p (invert p₂)) (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)
--            ≡⟨ refl ⟩
--              T-Msg (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₁)
--                (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₂)
--                (nf p (λ _ → D-S) S)
--        ∎
-- ... | t-eq
--   = <:ₜ-trans (<:ₜ-eq-ty N₁ N₁′ t-eq) N₁′<:N₂
-- complete-algₜ {p = p}{f₁ = f₁}{f₂ = f₂} {N₁ = N₁} {N₂ = N₂@(N-Msg p₁ NP NS)} (<:-neg-r {p = p₂} {T} {S} T₁<:T₂)
--   with nf-normal-type p d?S (T-Msg (invert p₂) T S)
-- ... | N₂′
--   with dual-all-irrelevant f₂ (const D-S)
-- ... | refl
--   using N₁<:N₂′ ← complete-algₜ {N₁ = N₁} {N₂ = N₂′} T₁<:T₂
--   with begin
--              t-msg (mult p p₂) (t-minus (nf ⊕ d?⊥ T)) (nf p (const D-S) S)
--            ≡⟨ t-msg-minus {p = mult p p₂} (nf ⊕ d?⊥ T) ⟩
--              t-msg (invert (mult p p₂)) (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)
--            ≡⟨ cong (λ ⊙ → t-msg ⊙ (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)) (invert-mult-⊙ p₂ {p}) ⟩
--              t-msg (mult p (invert p₂)) (nf ⊕ d?⊥ T) (nf p (λ _ → D-S) S)
--            ≡⟨ refl ⟩
--              T-Msg (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₁)
--                (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₂)
--                (nf p (λ _ → D-S) S)
--        ∎
-- ... | t-eq
--   = <:ₜ-trans N₁<:N₂′ (<:ₜ-eq-ty N₂′ N₂ (sym t-eq))
-- -- complete-algₜ {p = p} {T₁ = T-Dual _ T₁} {T₂ = T-Dual _ T₂} {N₁ = N₁} {N₂} (<:-dual-lr d T₁<:T₂) = {!complete-algₜ {p = invert p} {T₁ = T₂}{T₂ = T₁} {N₁ = N₂} {N₂ = N₁} T₁<:T₂ !}
-- complete-algₜ {p = p} (<:-dual-dual-l d T₁<:T₂)
--   rewrite invert-involution {p} = complete-algₜ T₁<:T₂
-- complete-algₜ {p = p} (<:-dual-dual-r d T₁<:T₂)
--   rewrite invert-involution {p} = complete-algₜ T₁<:T₂

-- complete-algₜ {p = p}{f₁ = f₁}{f₂ = f₂} {N₁ = N₁@(N-Msg p₁ NP NS)} {N₂} (<:-dual-msg-l {p = p₂}{T = T}{S = S} T₁<:T₂)
--     with nf-normal-type p d?S (T-Msg (invert p₂) T (T-Dual D-S S))
-- ... | N₁′
--     using N₁′<:N₂ ← complete-algₜ {f₁ = const D-S} {N₁ = N₁′} {N₂ = N₂} T₁<:T₂
--     with begin
--            (t-msg (mult (invert p) p₂) (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S))
--          ≡⟨ cong (λ ⊙ → t-msg ⊙ (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S)) (mult-invert-invert p p₂) ⟩
--            t-msg (mult p (invert p₂)) (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S)  
--          ≡⟨ refl ⟩
--            (T-Msg (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₁) (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₂) (nf (invert p) (λ x₁ → D-S) S))
--          ∎
-- ... | t-eq
--   = <:ₜ-trans (<:ₜ-eq-ty N₁ N₁′ t-eq) N₁′<:N₂

-- complete-algₜ {p = p}{f₁ = f₁}{f₂ = f₂}{N₁ = N₁} {N₂@(N-Msg p₁ NP NS)} (<:-dual-msg-r {p = p₂}{T = T}{S = S} T₁<:T₂)
--     with nf-normal-type p d?S (T-Msg (invert p₂) T (T-Dual D-S S))
-- ... | N₂′
--     using N₁<:N₂′ ← complete-algₜ {f₂ = const D-S} {N₁ = N₁} {N₂ = N₂′} T₁<:T₂
--     with begin
--            (t-msg (mult (invert p) p₂) (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S))
--          ≡⟨ cong (λ ⊙ → t-msg ⊙ (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S)) (mult-invert-invert p p₂) ⟩
--            t-msg (mult p (invert p₂)) (nf ⊕ d?⊥ T) (nf (invert p) (λ x₁ → D-S) S)  
--          ≡⟨ refl ⟩
--            (T-Msg (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₁) (t-loop (mult p (invert p₂)) (nf ⊕ d?⊥ T) .proj₂) (nf (invert p) (λ x₁ → D-S) S))
--          ∎
-- ... | t-eq
--   = <:ₜ-trans N₁<:N₂′ (<:ₜ-eq-ty N₂′ N₂ (sym t-eq))
-- complete-algₜ {N₁ = N-End} {N-End} <:-dual-end-l = <:ₜ-end
-- complete-algₜ {N₁ = N-End} {N-End} <:-dual-end-r = <:ₜ-end

-- complete-algₜ {p = p} {f₁ = f₁}{f₂ = f₂} {N₁ = N-Msg p₁ NT₁ NS₁} {N-Msg p₂ NT₂ NS₂} (<:-msg {T₁ = T₁}{p = p₃} {T₂ = T₂} T₁<<:T₂ S₁<:S₂)
--   with t-loop-sub-<<: p₃ (mult p p₃) T₁<<:T₂
-- ... | eq
--   rewrite eq
--   = <:ₜ-msg (aux p₃ T₁ T₂ T₁<<:T₂ NT₁ NT₂) (complete-algₜ S₁<:S₂)
--   where
--     aux : (p₃ : Polarity) (T₁ T₂ : Ty Δ KP) → (T₁<<:T₂ : T₁ <<:[ injᵥ p₃ ] T₂)
--       → (NT₁     : NormalProto′ (t-loop (mult p p₃) (nf ⊕ d?⊥ T₁) .proj₂))
--       → (NT₂     : NormalProto′ (t-loop (mult p p₃) (nf ⊕ d?⊥ T₂) .proj₂))
--       → NT₁ <<:ₚ′[ injᵥ (t-loop (mult p p₃) (nf ⊕ d?⊥ T₂) .proj₁) ] NT₂
--     aux ⊕ T₁ T₂ (<:-trans T₂<:T₁ T₂<:T₂) NT₁ NT₂ = {!!}
--     aux ⊕ T₁ T₂ <:-var N-Var N-Var = <<:ₚ′-refl N-Var
--     aux ⊕ T₁ T₂ (<:-up T₂<:T₁) (N-Up NT₁) (N-Up NT₂) = {!complete-algₜ {N₁ = NT₂}{N₂ = NT₁} T₂<:T₁!}
--     aux ⊕ T₁ T₂ (<:-proto #c₁⊆#c₂ T₁<<:T₂) (N-ProtoP NT₁) (N-ProtoP NT₂) = {!!}
--     aux ⊕ T₁ T₂ (<:-minus T₂<:T₁) NT₁ NT₂ = {!!}
--     aux ⊕ T₁ T₂ (<:-minus-minus-l T₂<:T₁) NT₁ NT₂ = {!!}
--     aux ⊕ T₁ T₂ (<:-minus-minus-r T₂<:T₁) NT₁ NT₂ = {!!}
--     aux ⊝ T₁ T₂ T₁<:T₂ NT₁ NT₂ = {!!}

-- -- p₁ ≡ p₂, but p₃ can be different


-- {-
-- complete-algₜ {p = p} {f₁ = f₁} {f₂ = f₂} {N₁ = N-Msg p₁ NT₁ NS₁} {N-Msg p₂ NT₂ NS₂} (<:-msg {T₁ = T₁} {p = ⊕} {T₂ = T₂} T₁<<:T₂ S₁<:S₂)
--   rewrite t-loop-sub-<<: ⊕ (mult p ⊕) T₁<<:T₂ | mult-identityʳ p
--   = <:ₜ-msg {!t-loop-nf-ident T₂ NT₂!} (complete-algₜ S₁<:S₂)
-- complete-algₜ {p = p} {f₁ = f₁} {f₂ = f₂} {N₁ = N-Msg p₁ NT₁ NS₁} {N-Msg p₂ NT₂ NS₂} (<:-msg {T₁ = T₁} {p = ⊝} {T₂ = T₂} T₁<<:T₂ S₁<:S₂) = {!t-loop-nf-ident T₂ NT₂!}
--   -- rewrite t-loop-sub-<<: p₃ (mult p p₃) T₁<<:T₂
--   -- = <:ₜ-msg {!!} (complete-algₜ S₁<:S₂)
-- -}

-- -- (complete-<<:ₚ {f₁ = d?⊥}{f₂ = d?⊥} {N₁ = NT₁} {N₂ = NT₂} {!t-loop-sub-<<:!})

-- --------------------------------------------------------------------------------

-- -- complete-algₜ : ∀ {T₁ T₂ : Ty Δ (KV pk m)} {N₁ : NormalTy T₁}{N₂ : NormalTy T₂}
-- --   → T₁ <: T₂ → N₁ <:ₜ N₂
-- -- complete-algₜ {N₁ = N₁} {N₂} <:-refl rewrite nt-unique N₁ N₂ = <:ₜ-refl N₂
-- -- complete-algₜ (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃)
-- --   using T₂′ ← nf ⊕ d?⊥ T₂
-- --   with  nf-normal-type ⊕ d?⊥ T₂ | nf-sound+ {f = d?⊥}T₂
-- -- ... | N₂ | nf≡T₂
-- --   using T₂′<:T₂ , T₂<:T₂′ ← conv⇒subty T₂′ T₂ nf≡T₂ = {!!}
-- -- -- <:ₜ-trans (complete-algₜ T₁<:T₂) (complete-algₜ T₂<:T₃)
-- -- -- this is more complex: T₂ is not necessarily normalized!
-- -- -- hence: normalize T₂ → T₂′, we have T₁ <: T₂ and T₂ ≡ T₂′ ⇒ T₁ <: T₂′ and in the same manner T₂′ <: T₃
-- -- -- now we have suitable arguments for complete-algₜ!
-- -- complete-algₜ {N₁ = N-Sub N₁} {N-Sub N₂} (<:-sub K≤K′ T₁<:T₂) = <:ₜ-sub (complete-algₜ T₁<:T₂)
-- -- complete-algₜ {N₁ = N-Var ()} {N-Var x₁} <:-sub-dual-l
-- -- complete-algₜ {N₁ = N-Var ()} {N-Sub N₂} <:-sub-dual-l
-- -- complete-algₜ {N₁ = N-Var ()} {N-Var x₁} <:-sub-dual-r
-- -- complete-algₜ {N₁ = N-Sub N₁} {N-Var ()} <:-sub-dual-r
-- -- complete-algₜ {N₁ = N-Arrow N₁ N₂} {N-Arrow N₃ N₄} (<:-fun T₁<:T₂ T₁<:T₃) = <:ₜ-arrow (complete-algₜ T₁<:T₂) (complete-algₜ T₁<:T₃)
-- -- complete-algₜ {N₁ = N-ProtoD N₁} {N-ProtoD N₂} (<:-protoD T₁<:T₂) = <:ₜ-data (complete-algₜ T₁<:T₂)
-- -- complete-algₜ {N₁ = N-Poly N₁} {N-Poly N₂} (<:-all T₁<:T₂) = <:ₜ-poly (complete-algₜ T₁<:T₂)
-- -- complete-algₜ {N₁ = N₁} {N₂} (<:-neg-l T₁<:T₂) = {!!}
-- -- complete-algₜ (<:-neg-r T₁<:T₂) = {!!}
-- -- complete-algₜ {N₁ = N-Var (NV-Dual d₁ x)} {N-Var (NV-Dual d₂ x₁)} (<:-dual-lr d T₁<:T₂) = {!<:ₜ-var!}
-- -- complete-algₜ {N₁ = N₁} {N₂} (<:-dual-dual-l d T₁<:T₂) = {!N₁ N₂!}
-- -- complete-algₜ {N₁ = N₁} {N₂} (<:-dual-dual-r d T₁<:T₂) = {!!}
-- -- complete-algₜ (<:-dual-msg-l T₁<:T₂) = {!!}
-- -- complete-algₜ (<:-dual-msg-r T₁<:T₂) = {!!}
-- -- complete-algₜ {N₁ = N-Var x} {N-Var ()} <:-dual-end-l
-- -- complete-algₜ {N₁ = N-Var ()} {N-End} <:-dual-end-l
-- -- complete-algₜ {N₁ = N-End} {N-Var ()} <:-dual-end-r
-- -- complete-algₜ {N₁ = N-Msg p₁ P₁ N₁} {N-Msg p₂ P₂ N₂} (<:-msg P₁<<:P₂ T₁<:T₂) = <:ₜ-msg {!!} (complete-algₜ T₁<:T₂)

-- -- subtyping implies conversion
-- -- not possible to prove with a transitivity rule...

-- alg-subty⇒conv :  ∀ {T₁ T₂ : Ty Δ (KV pk m)} {N₁ : NormalTy T₁}{N₂ : NormalTy T₂}
--     → N₁ <:ₜ N₂ → N₂ <:ₜ N₁ → T₁ ≡ T₂
-- alg-subproto⇒conv : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto T₁}{N₂ : NormalProto T₂}
--     → N₁ <:ₚ N₂ → N₂ <:ₚ N₁ → T₁ ≡ T₂
-- alg-subproto′⇒conv : ∀ {T₁ T₂ : Ty Δ KP} {N₁ : NormalProto′ T₁}{N₂ : NormalProto′ T₂}
--     → N₁ <:ₚ′ N₂ → N₂ <:ₚ′ N₁ → T₁ ≡ T₂

-- alg-subty⇒conv <:ₜ-var <:ₜ-var = refl
-- alg-subty⇒conv <:ₜ-base <:ₜ-base = refl
-- alg-subty⇒conv (<:ₜ-arrow N₁<:N₂ N₁<:N₃) (<:ₜ-arrow N₂<:N₁ N₂<:N₂) = cong₂ (T-Arrow _) (alg-subty⇒conv N₂<:N₁ N₁<:N₂) (alg-subty⇒conv N₁<:N₃ N₂<:N₂)
-- alg-subty⇒conv (<:ₜ-poly N₁<:N₂) (<:ₜ-poly N₂<:N₁) = cong T-Poly (alg-subty⇒conv N₁<:N₂ N₂<:N₁)
-- alg-subty⇒conv (<:ₜ-sub N₁<:N₂) (<:ₜ-sub N₂<:N₁) = cong (T-Sub _) (alg-subty⇒conv N₁<:N₂ N₂<:N₁)
-- alg-subty⇒conv <:ₜ-end <:ₜ-end = refl
-- alg-subty⇒conv (<:ₜ-msg {p = ⊕} NP₁<<:NP₂ N₁<:N₂) (<:ₜ-msg NP₂<<:NP₁ N₂<:N₁) = cong₂ (T-Msg _) (alg-subproto′⇒conv NP₂<<:NP₁ NP₁<<:NP₂) (alg-subty⇒conv N₁<:N₂ N₂<:N₁)
-- alg-subty⇒conv (<:ₜ-msg {p = ⊝} NP₁<<:NP₂ N₁<:N₂) (<:ₜ-msg NP₂<<:NP₁ N₂<:N₁) = cong₂ (T-Msg _) (alg-subproto′⇒conv NP₁<<:NP₂ NP₂<<:NP₁) (alg-subty⇒conv N₁<:N₂ N₂<:N₁)
-- alg-subty⇒conv (<:ₜ-data N₁<:N₂) (<:ₜ-data N₂<:N₁) = cong T-ProtoD (alg-subty⇒conv N₁<:N₂ N₂<:N₁)

-- alg-subproto⇒conv (<:ₚ-plus N₁<:N₂) (<:ₚ-plus N₂<:N₁) = alg-subproto′⇒conv N₁<:N₂ N₂<:N₁
-- alg-subproto⇒conv (<:ₚ-minus N₂<:N₁) (<:ₚ-minus N₁<:N₂) = cong T-Minus (alg-subproto′⇒conv N₁<:N₂ N₂<:N₁)

-- alg-subproto′⇒conv (<:ₚ′-proto {⊙ = ⊕} #c₁⊆#c₂ P₁<<:P₂) (<:ₚ′-proto #c₂⊆#c₁ P₂<<:P₁) = cong₂ (λ a b → T-ProtoP a ⊕ b) (⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁) (alg-subproto⇒conv P₁<<:P₂ P₂<<:P₁)
-- alg-subproto′⇒conv (<:ₚ′-proto {⊙ = ⊝} #c₁⊆#c₂ P₁<<:P₂) (<:ₚ′-proto #c₂⊆#c₁ P₂<<:P₁) = cong₂ (λ a b → T-ProtoP a ⊝ b) (⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁) (alg-subproto⇒conv P₂<<:P₁ P₁<<:P₂)
-- alg-subproto′⇒conv (<:ₚ′-proto {⊙ = ⊘} #c₁⊆#c₂ P₁<<:P₂) (<:ₚ′-proto #c₂⊆#c₁ P₂<<:P₁) = cong₂ (λ a b → T-ProtoP a ⊘ b) (⊆-antisym #c₁⊆#c₂ #c₂⊆#c₁) P₁<<:P₂
-- alg-subproto′⇒conv (<:ₚ′-up N₁<:N₂) (<:ₚ′-up N₂<:N₁) = cong T-Up (alg-subty⇒conv N₁<:N₂ N₂<:N₁)
-- alg-subproto′⇒conv <:ₚ′-var <:ₚ′-var = refl

-- {- TODO:
-- subty⇒conv : {T₁ T₂ : Ty Δ K} → T₁ <: T₂ → T₂ <: T₁ → T₁ ≡c T₂
-- subty⇒conv {K = KV x x₁}{T₁ = T₁}{T₂ = T₂} T₁<:T₂ T₂<:T₁
--   using N₁<:N₂ ← complete-algₜ {N₁ = {!nf-normal-type ⊕ d?⊥ T₁ !}}T₁<:T₂
--   using N₂<:N₁ ← complete-algₜ T₂<:T₁ = {! !}
-- subty⇒conv {K = KP} T₁<:T₂ T₂<:T₁ = {!!}

-- -}
