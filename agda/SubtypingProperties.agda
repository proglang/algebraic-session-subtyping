open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Nat
open import Data.Fin.Subset as Subset using (_⊆_)
open import Data.Fin.Subset.Properties using (⊆-refl)
open import Data.List
open import Data.Product
open import Data.Sum
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Function using (id; const; _$_; case_of_)

module SubtypingProperties  where

open import Util
open import Kinds
open import Duality
open import Types
open import Subtyping

normal-proto′-<: : (T₁ T₂ : Ty Δ KP) → T₁ <: T₂ → NormalProto′ (nf ⊕ d?⊥ T₁) → NormalProto′ (nf ⊕ d?⊥ T₂)
normal-proto′-<:-minus : (T₁ T₂ : Ty Δ KP) → T₂ <: T₁ → NormalProto′ (t-minus (nf ⊕ d?⊥ T₁)) → NormalProto′ (t-minus (nf ⊕ d?⊥ T₂))

normal-proto′-<: T₁ T₃ (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) N₁ = normal-proto′-<: T₂ T₃ T₂<:T₃ (normal-proto′-<: T₁ T₂ T₁<:T₂ N₁)
normal-proto′-<: T₁ T₂ <:-var N₁ = N₁
normal-proto′-<: (T-Up T₁) (T-Up T₂) (<:-up T₁<:T₂) N₁ = N-Up (nf-normal-type ⊕ d?⊥ T₂)
normal-proto′-<: (T-ProtoP #c ⊙ T₁) (T-ProtoP #d .⊙ T₂) (<:-proto #c⊆#d T₁<<:T₂) N₁ = N-ProtoP (nf-normal-proto T₂)
normal-proto′-<: T₁ T₂ (<:-minus T₁<:T₂) N₁ = normal-proto′-<:-minus _ _ T₁<:T₂ N₁
normal-proto′-<: T₁ T₂ (<:-minus-minus-l {T₃} T₁<:T₂) N₁
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-<: _ _ T₁<:T₂ N₁ 
normal-proto′-<: T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₁<:T₂) N₁
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-<: _ _ T₁<:T₂ N₁

normal-proto′-<:-minus T₁ T₃ (<:-trans T₃<:T₂ T₂<:T₁) N₁ = normal-proto′-<:-minus _ _ T₃<:T₂ (normal-proto′-<:-minus _ _ T₂<:T₁ N₁)
normal-proto′-<:-minus T₁ T₂ (<:-minus {T₄} {T₁ = T₃} T₂<:T₁) N₁
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  | t-minus-involution (nf ⊕ d?⊥ T₄) (nf-normal-proto T₄)
  = normal-proto′-<: _ _ T₂<:T₁ N₁
normal-proto′-<:-minus T₁ T₂ (<:-minus-minus-l {T₃} T₂<:T₁) N₁
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-<:-minus _ _ T₂<:T₁ N₁
normal-proto′-<:-minus T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₂<:T₁) N₁
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-<:-minus _ _ T₂<:T₁ N₁

normal-proto′-loop-<: : (T₁ T₂ : Ty Δ KP) → T₁ <: T₂ → NormalProto′ (t-loop p (nf ⊕ d?⊥ T₁) .proj₂) → NormalProto′ (t-loop p (nf ⊕ d?⊥ T₂) .proj₂)
normal-proto′-loop-<:-minus : (T₁ T₂ : Ty Δ KP) → T₂ <: T₁ → NormalProto′ (t-loop p (t-minus (nf ⊕ d?⊥ T₁)) .proj₂) → NormalProto′ (t-loop p (t-minus (nf ⊕ d?⊥ T₂)) .proj₂)

normal-proto′-loop-<: T₁ T₃ (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) N = normal-proto′-loop-<: T₂ T₃ T₂<:T₃ (normal-proto′-loop-<: T₁ T₂ T₁<:T₂ N)
normal-proto′-loop-<: T₁ T₂ <:-var N = N
normal-proto′-loop-<: T₁ T₂ (<:-up {T₂ = T₃} T₁<:T₂) N = N-Up (nf-normal-type ⊕ d?⊥ T₃)
normal-proto′-loop-<: T₁ T₂ (<:-proto {T₂ = T₃} x x₁) N = N-ProtoP (nf-normal-proto T₃)
normal-proto′-loop-<: T₁ T₂ (<:-minus {T₃} {T₄} T₁<:T₂) N = normal-proto′-loop-<:-minus _ _ T₁<:T₂ N 
normal-proto′-loop-<: T₁ T₂ (<:-minus-minus-l {T₃} T₁<:T₂) N
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-loop-<: _ _ T₁<:T₂ N
normal-proto′-loop-<: T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₁<:T₂) N
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-loop-<: _ _ T₁<:T₂ N

normal-proto′-loop-<:-minus T₁ T₃ (<:-trans {T₂ = T₂} T₃<:T₂ T₂<:T₁) N = normal-proto′-loop-<:-minus _ _ T₃<:T₂ (normal-proto′-loop-<:-minus _ _ T₂<:T₁ N)
normal-proto′-loop-<:-minus T₁ T₂ <:-var N = N
normal-proto′-loop-<:-minus T₁ T₂ (<:-up {T₁ = T₃} T₂<:T₁) N = N-Up (nf-normal-type ⊕ d?⊥ T₃)
normal-proto′-loop-<:-minus T₁ T₂ (<:-proto {T₁ = T₄} {T₂ = T₃} #c⊆#d T₁<<:T₂) N = N-ProtoP (nf-normal-proto T₄)
normal-proto′-loop-<:-minus T₁ T₂ (<:-minus {T₃} {T₄} T₂<:T₁) N
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₄) (nf-normal-proto T₄)
  = normal-proto′-loop-<: _ _ T₂<:T₁ N
normal-proto′-loop-<:-minus T₁ T₂ (<:-minus-minus-l {T₃} T₂<:T₁) N
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-loop-<:-minus _ _ T₂<:T₁ N
normal-proto′-loop-<:-minus T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₂<:T₁) N
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = normal-proto′-loop-<:-minus _ _ T₂<:T₁ N

<<:-invert : ∀ {p} {T₁ T₂ : Ty Δ KP} → T₁ <<:[ injᵥ p ] T₂ → T₂ <<:[ injᵥ (invert p) ] T₁
<<:-invert {p = ⊕} T₁<<:T₂ = T₁<<:T₂
<<:-invert {p = ⊝} T₁<<:T₂ = T₁<<:T₂


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

lemma-sub-loop-right : ∀ {p₃} {T₁ T₂ : Ty Δ KP} (T₁<<:T₂ : T₁ <<:[ injᵥ p₃ ] T₂)
  → t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₂ <<:[ injᵥ (t-loop p₃ (nf ⊕ d?⊥ T₂) .proj₁) ] t-loop p₃ (nf ⊕ d?⊥ T₂) .proj₂
lemma-sub-loop-right {p₃ = p₃} T₁<<:T₂
  with lemma-sub-loop T₁<<:T₂
... | r
  rewrite t-loop-sub-<<: p₃ p₃ T₁<<:T₂ = r

-- subtyping preserves the size of normal forms

nfp-size : (T₁ T₂ : Ty Δ KP) → T₁ <: T₂
  → ∀ {p} {f₁ f₂} → (N₁ : NormalProto (nf p f₁ T₁)) (N₂ : NormalProto (nf p f₂ T₂))
  → sizeₚ N₁ ≡ sizeₚ N₂
nfp-invert-size : (T₁ T₂ : Ty Δ KP) → T₂ <: T₁
  → ∀ {p}{f₁ f₂} → (N₁ : NormalProto (t-minus (nf p f₁ T₁))) (N₂ : NormalProto (t-minus (nf p f₂ T₂)))
  → sizeₚ N₁ ≡ sizeₚ N₂
nfp′-size : (T₁ T₂ : Ty Δ KP) → T₁ <: T₂
  → ∀ {p}{f₁ f₂} → (N₁ : NormalProto′ (nf p f₁ T₁)) (N₂ : NormalProto′ (nf p f₂ T₂))
  → sizeₚ′ N₁ ≡ sizeₚ′ N₂
nfp′-invert-size : (T₁ T₂ : Ty Δ KP) → T₂ <: T₁
  → ∀ {p}{f₁ f₂} → (N₁ : NormalProto′ (t-minus (nf p f₁ T₁))) (N₂ : NormalProto′ (t-minus (nf p f₂ T₂)))
  → sizeₚ′ N₁ ≡ sizeₚ′ N₂
nfp′-size-t-loop : ∀ p₃ → (T₁ T₂ : Ty Δ KP) → (T₁<<:T₂ : T₁ <<:[ injᵥ p₃ ] T₂)
  → (N₁ : NormalProto′ (t-loop p (nf ⊕ d?⊥ T₁) .proj₂)) (N₂ : NormalProto′ (t-loop p (nf ⊕ d?⊥ T₂) .proj₂))
  → sizeₚ′ N₁ ≡ sizeₚ′ N₂
nfp′-invert-size-t-loop : ∀ p₃ → (T₁ T₂ : Ty Δ KP) → (T₁<<:T₂ : T₁ <<:[ injᵥ p₃ ] T₂)
  → (N₁ : NormalProto′ (t-loop p (t-minus (nf ⊕ d?⊥ T₁)) .proj₂)) (N₂ : NormalProto′ (t-loop p (t-minus (nf ⊕ d?⊥ T₂)) .proj₂))
  → sizeₚ′ N₁ ≡ sizeₚ′ N₂
nft-size : (T₁ T₂ : Ty Δ (KV pk m)) → T₁ <: T₂
  → ∀ {p}{f₁ f₂} → (N₁ : NormalTy (nf p f₁ T₁)) (N₂ : NormalTy (nf p f₂ T₂))
  → sizeₜ N₁ ≡ sizeₜ N₂

nft-size T₁ T₃ (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) {p = p}{f₁ = f₁} N₁ N₃
  using N₂ ← nf-normal-type p f₁ T₂
  = trans (nft-size T₁ T₂ T₁<:T₂ N₁ N₂) (nft-size T₂ T₃ T₂<:T₃ N₂ N₃)
nft-size T₁ T₂ (<:-sub K≤K′ T₁<:T₂) (N-Sub N₁) (N-Sub N₂) = cong suc (nft-size _ _ T₁<:T₂ N₁ N₂)
nft-size T₁ T₂ (<:-sub-dual-l {T = T}{K≤K′}) {p} (N-Sub N₁) (N-Sub N₂)
  using eq ← (cong (λ f → nf (invert p) f T) (dual-all-irrelevant (λ x₁ → D-S) (λ x₁ → dualizable-sub D-S K≤K′)))
  rewrite nt-unique-eq eq N₁ N₂
  = sym (cong suc (sizeₜ-subst N₂ eq))
nft-size T₁ T₂ (<:-sub-dual-r {T = T}{K≤K′}) {p} (N-Sub N₁) (N-Sub N₂)
  using eq ← (cong (λ f → nf (invert p) f T) (dual-all-irrelevant (λ x₁ → dualizable-sub D-S K≤K′) (λ x₁ → D-S)))
  rewrite nt-unique-eq eq N₁ N₂
  = sym (cong suc (sizeₜ-subst N₂ eq))
nft-size T₁ T₂ <:-var {p = ⊕} (N-Var x) (N-Var x₁) = refl
nft-size T₁ T₂ <:-var {p = ⊝} (N-Var x) (N-Var x₁) = refl
nft-size T₁ T₂ <:-dual-var {p = ⊕} (N-Var x) (N-Var x₁) = refl
nft-size T₁ T₂ <:-dual-var {p = ⊝} (N-Var x) (N-Var x₁) = refl
nft-size T₁ T₂ <:-base N-Base N-Base = refl
nft-size (T-Arrow _ T₁ T₂) (T-Arrow _ T₃ T₄) (<:-fun T₃<:T₁ T₂<:T₄) (N-Arrow N₁ N₂) (N-Arrow N₃ N₄)
  = cong suc $ begin
      (sizeₜ N₁ ⊔ sizeₜ N₂)
    ≡⟨ cong₂ _⊔_ (sym $ nft-size T₃ T₁ T₃<:T₁ N₃ N₁) (nft-size T₂ T₄ T₂<:T₄ N₂ N₄) ⟩
      (sizeₜ N₃ ⊔ sizeₜ N₄)
    ∎
nft-size (T-ProtoD T₁) (T-ProtoD T₂) (<:-protoD T₁<:T₂) (N-ProtoD N₁) (N-ProtoD N₂) = cong suc (nft-size T₁ T₂ T₁<:T₂ N₁ N₂)
nft-size T₁ T₂ (<:-all T₁<:T₂) (N-Poly N₁) (N-Poly N₂) = cong suc (nft-size _ _ T₁<:T₂ N₁ N₂)
nft-size (T-Msg p₃ (T-Minus T) S) (T-Msg .(invert p₃) T S)  (<:-msg-minus refl) {p = p} {f₁}{f₂} (N-Msg p₁ N₁ NS₁) (N-Msg p₂ N₂ NS₂)
  rewrite dual-all-irrelevant f₁ f₂ | nt-unique NS₁ NS₂
  rewrite sym (invert-mult-⊙ p₃ {p})
  rewrite t-loop-minus {p = mult p p₃} (nf ⊕ d?⊥ T) | np′-unique N₁ N₂
  = refl
nft-size (T-Msg p₃ T S) (T-Msg .(invert p₃) (T-Minus T) S) (<:-minus-msg refl) {p = p} {f₁}{f₂} (N-Msg p₁ N₁ NS₁) (N-Msg p₂ N₂ NS₂)
  rewrite dual-all-irrelevant f₁ f₂ | nt-unique NS₁ NS₂
  rewrite sym (invert-mult-⊙ p₃ {p})
  rewrite sym (t-loop-minus {p = mult p p₃} (t-minus (nf ⊕ d?⊥ T))) | t-minus-involution (nf ⊕ d?⊥ T) (nf-normal-proto T) | np′-unique N₁ N₂
  = refl
nft-size (T-Dual D-S (T-Dual D-S T)) T (<:-dual-dual-l-new d) {p = p} {f₂ = f₂} N₁ N₂
  rewrite invert-involution {p} | dual-all-irrelevant (const D-S) f₂ | nt-unique N₁ N₂
  = refl
nft-size T₁ (T-Dual D-S (T-Dual D-S T₂)) (<:-dual-dual-r-new d) {p = p} {f₁} N₁ N₂
  rewrite invert-involution {p} | dual-all-irrelevant (const D-S) f₁ | nt-unique N₁ N₂
  = refl
nft-size (T-Msg p₃ T (T-Dual D-S S)) (T-Dual D-S (T-Msg .(invert p₃) T S)) (<:-dual-msg-l-new refl) {p = p} (N-Msg p₁ N₁ NS₁) (N-Msg p₂ N₂ NS₂)
  rewrite nt-unique NS₁ NS₂
  rewrite mult-invert-invert⇒mult p p₃ | np′-unique N₁ N₂
  = refl
nft-size (T-Dual D-S (T-Msg .(invert p₃) T S)) (T-Msg p₃ T (T-Dual D-S S)) (<:-dual-msg-r-new refl) {p = p} (N-Msg p₁ N₁ NS₁) (N-Msg p₂ N₂ NS₂)
  rewrite nt-unique NS₁ NS₂
  rewrite mult-invert-invert⇒mult p p₃ | np′-unique N₁ N₂
  = refl
nft-size T₁ T₂ <:-dual-end-l N-End N-End = refl
nft-size T₁ T₂ <:-dual-end-r N-End N-End = refl
nft-size T₁ T₂ <:-end N-End N-End = refl
nft-size (T-Msg p₃ T₁ S₁) (T-Msg p₃ T₂ S₂) (<:-msg T₁<<:T₂ S₁<:S₂) {p = p} {f₁}{f₂} (N-Msg p₁ N₁ NS₁) (N-Msg p₂ N₂ NS₂)
  rewrite dual-all-irrelevant f₁ f₂
  = cong suc $ begin
      sizeₚ′ N₁ ⊔ sizeₜ NS₁
    ≡⟨ cong (sizeₚ′ N₁ ⊔_) (nft-size S₁ S₂ S₁<:S₂ NS₁ NS₂)  ⟩
      sizeₚ′ N₁ ⊔ sizeₜ NS₂
    ≡⟨ cong (_⊔ sizeₜ NS₂) (nfp′-size-t-loop p₃ _ _ T₁<<:T₂ N₁ N₂)  ⟩
      sizeₚ′ N₂ ⊔ sizeₜ NS₂
    ∎

--     ≡⟨ cong₂ _⊔_ {!nfp′-size T₁ T₂!} ()  ⟩


nfp-size T₁ T₃ T₁<:T₂ {p = ⊝} {f₁ = f₁} N₁ N₃
  with f₁ refl
... | ()
nfp-size T₁ T₃ (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) {p = ⊕} N₁ N₃
  using N₂ ← nf-normal-proto T₂
  = trans (nfp-size T₁ T₂ T₁<:T₂ N₁ N₂) (nfp-size T₂ T₃ T₂<:T₃ N₂ N₃)
nfp-size T₁ T₂ <:-var {p = ⊕} (N-Normal N-Var) (N-Normal N-Var) = refl
nfp-size (T-Up T₁) (T-Up T₂) (<:-up T₁<:T₂) {p = ⊕} (N-Normal (N-Up N₁)) (N-Normal (N-Up N₂)) = cong suc (cong suc (nft-size T₁ T₂ T₁<:T₂ N₁ N₂))
nfp-size (T-ProtoP _ ⊕ T₁) (T-ProtoP _ _ T₂)(<:-proto #c⊆#d T₁<<:T₂) {p = ⊕} (N-Normal (N-ProtoP N₁)) (N-Normal (N-ProtoP N₂)) = cong suc (cong suc (nfp-size T₁ T₂ T₁<<:T₂ N₁ N₂))
nfp-size (T-ProtoP _ ⊝ T₁) (T-ProtoP _ _ T₂) (<:-proto #c⊆#d T₁<<:T₂) {p = ⊕} (N-Normal (N-ProtoP N₁)) (N-Normal (N-ProtoP N₂)) = cong suc (cong suc (sym (nfp-size T₂ T₁ T₁<<:T₂ N₂ N₁)))
nfp-size (T-ProtoP _ ⊘ T₁) (T-ProtoP _ _ T₂) (<:-proto #c⊆#d T₁≡cT₂) {p = ⊕} (N-Normal (N-ProtoP N₁)) (N-Normal (N-ProtoP N₂))
  rewrite nf-complete d?⊥ d?⊥ T₁≡cT₂ | np-unique N₁ N₂
  = refl
nfp-size (T-Minus T₁) (T-Minus T₂) (<:-minus T₂<:T₁) {p = ⊕} N₁ N₂ = nfp-invert-size T₁ T₂ T₂<:T₁ N₁ N₂
nfp-size (T-Minus (T-Minus T₁)) T₂ (<:-minus-minus-l T₁<:T₂) {p = ⊕} N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = nfp-size T₁ T₂ T₁<:T₂ N₁ N₂  
nfp-size T₁ (T-Minus (T-Minus T₂)) (<:-minus-minus-r T₁<:T₂) {p = ⊕} N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = nfp-size T₁ T₂ T₁<:T₂ N₁ N₂

nfp-invert-size T₁ T₂ T₂<:T₁ {⊝} {f₁} N₁ N₂ = case f₁ refl of λ()
nfp-invert-size T₁ T₃ (<:-trans {T₂ = T₂} T₂<:T₃ T₃<:T₁) {⊕} {f₁} N₁ N₃
  using N₂ ← nf-normal-proto-inverted T₂
  = trans (nfp-invert-size _ _ T₃<:T₁ N₁ N₂) (nfp-invert-size _ _ T₂<:T₃ N₂ N₃)
nfp-invert-size T₁ T₂ <:-var {⊕} {f₁} (N-Minus N-Var) (N-Minus N-Var) = refl
nfp-invert-size T₁ T₂ (<:-up T₂<:T₁) {⊕} {f₁} (N-Minus (N-Up N₁)) (N-Minus (N-Up N₂)) = cong suc $ cong suc (sym $ nft-size _ _ T₂<:T₁ N₂ N₁)
nfp-invert-size T₁ T₂ (<:-proto {⊙ = ⊕} #c⊆#d T₁<<:T₂) {⊕} {f₁} (N-Minus (N-ProtoP N₁)) (N-Minus (N-ProtoP N₂)) = cong suc $ cong suc (sym $ nfp-size _ _ T₁<<:T₂ N₂ N₁)
nfp-invert-size T₁ T₂ (<:-proto {⊙ = ⊝} #c⊆#d T₁<<:T₂) {⊕} {f₁} (N-Minus (N-ProtoP N₁)) (N-Minus (N-ProtoP N₂)) = cong suc $ cong suc (nfp-size _ _ T₁<<:T₂ N₁ N₂)
nfp-invert-size T₁ T₂ (<:-proto {⊙ = ⊘} #c⊆#d T₁≡cT₂) {⊕} {f₁} (N-Minus (N-ProtoP N₁)) (N-Minus (N-ProtoP N₂))
  rewrite nf-complete d?⊥ d?⊥ T₁≡cT₂ | np-unique N₁ N₂
  = refl
nfp-invert-size T₁ T₂ (<:-minus {T₃} {T₄} T₂<:T₁) {⊕} {f₁} N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₄) (nf-normal-proto T₄)
  = nfp-size _ _ T₂<:T₁ N₁ N₂
nfp-invert-size T₁ T₂ (<:-minus-minus-l {T₃} T₂<:T₁) {⊕} {f₁} N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp-invert-size _ _ T₂<:T₁ N₁ N₂
nfp-invert-size T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₂<:T₁) {⊕} {f₁} N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp-invert-size _ _ T₂<:T₁ N₁ N₂

nfp′-size T₁ T₂ T₁<:T₂ {⊝} {f₁} N₁ N₂ = case f₁ refl of λ ()
nfp′-size T₁ T₃ (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) {⊕} {f₁}{f₂} N₁ N₃
  rewrite dual-all-irrelevant f₁ d?⊥ | dual-all-irrelevant f₂ d?⊥
  using N₂ ← normal-proto′-<: T₁ T₂ T₁<:T₂ N₁
 = trans (nfp′-size T₁ T₂ T₁<:T₂ N₁ N₂) (nfp′-size T₂ T₃ T₂<:T₃ N₂ N₃)
nfp′-size T₁ T₂ <:-var {⊕} N-Var N-Var = refl
nfp′-size T₁ T₂ (<:-up T₁<:T₂) {⊕} (N-Up N₁) (N-Up N₂) = cong suc (nft-size _ _ T₁<:T₂ N₁ N₂)
nfp′-size T₁ T₂ (<:-proto {⊙ = ⊕} #c⊆#d T₁<<:T₂) {⊕} (N-ProtoP N₁) (N-ProtoP N₂) = cong suc (nfp-size _ _ T₁<<:T₂ N₁ N₂)
nfp′-size T₁ T₂ (<:-proto {⊙ = ⊝} #c⊆#d T₁<<:T₂) {⊕} (N-ProtoP N₁) (N-ProtoP N₂) = sym $ cong suc (nfp-size _ _ T₁<<:T₂ N₂ N₁)
nfp′-size T₁ T₂ (<:-proto {⊙ = ⊘} #c⊆#d T₁≡cT₂) {⊕} (N-ProtoP N₁) (N-ProtoP N₂)
  rewrite nf-complete d?⊥ d?⊥ T₁≡cT₂ | np-unique N₁ N₂
  = refl
nfp′-size T₁ T₂ (<:-minus T₁<:T₂) {⊕} N₁ N₂ = nfp′-invert-size _ _ T₁<:T₂ N₁ N₂
nfp′-size T₁ T₂ (<:-minus-minus-l {T₃} T₁<:T₂) {⊕} N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-size _ _ T₁<:T₂ {⊕} N₁ N₂
nfp′-size T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₁<:T₂) {⊕} N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-size _ _ T₁<:T₂ {⊕} N₁ N₂

nfp′-invert-size T₁ T₂ T₂<:T₁ {⊝} {f₁} N₁ N₂ = case f₁ refl of λ()
nfp′-invert-size T₁ T₃ (<:-trans T₃<:T₂ T₂<:T₁) {⊕} {f₁} N₁ N₃
  rewrite dual-all-irrelevant f₁ d?⊥
  using N₂ ← normal-proto′-<:-minus _ _ T₂<:T₁ N₁
  = trans (nfp′-invert-size _ _ T₂<:T₁ N₁ N₂) (nfp′-invert-size _ _ T₃<:T₂ N₂ N₃)
nfp′-invert-size T₁ T₂ (<:-minus {T₃} {T₄} T₂<:T₁) {⊕} N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃) | t-minus-involution (nf ⊕ d?⊥ T₄) (nf-normal-proto T₄)
  = nfp′-size _ _ T₂<:T₁ N₁ N₂ 
nfp′-invert-size T₁ T₂ (<:-minus-minus-l {T₃} T₂<:T₁) {⊕} N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-invert-size _ _ T₂<:T₁ N₁ N₂
nfp′-invert-size T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₂<:T₁) {⊕} N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-invert-size _ _ T₂<:T₁ N₁ N₂

nfp′-size-t-loop {p = p} ⊕ T₁ T₃ (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃) N₁ N₃
  using N₂ ← normal-proto′-loop-<: _ _ T₁<<:T₂ N₃
  = trans (nfp′-size-t-loop ⊕ _ _ T₂<<:T₃ N₁ N₂) (nfp′-size-t-loop ⊕ _ _ T₁<<:T₂ N₂ N₃)
nfp′-size-t-loop {p = p} ⊕ T₁ T₂ <:-var N-Var N-Var = refl
nfp′-size-t-loop {p = p} ⊕ T₁ T₂ (<:-up T₁<<:T₂) (N-Up N) (N-Up N₁) = sym $ cong suc $ nft-size _ _ T₁<<:T₂ N₁ N
nfp′-size-t-loop {p = p} ⊕ T₁ T₂ (<:-proto {⊙ = ⊕} #c⊆#d T₁<<:T₂) (N-ProtoP N) (N-ProtoP N₁) = sym $ cong suc $ nfp-size _ _ T₁<<:T₂ N₁ N
nfp′-size-t-loop {p = p} ⊕ T₁ T₂ (<:-proto {⊙ = ⊝} #c⊆#d T₁<<:T₂) (N-ProtoP N) (N-ProtoP N₁) = cong suc $ nfp-size _ _ T₁<<:T₂ N N₁
nfp′-size-t-loop {p = p} ⊕ T₁ T₂ (<:-proto {⊙ = ⊘} #c⊆#d T₁≡cT₂) (N-ProtoP N) (N-ProtoP N₁)
  rewrite nf-complete d?⊥ d?⊥ T₁≡cT₂ | np-unique N N₁
  = refl
nfp′-size-t-loop {p = p} ⊕ T₁ T₂ (<:-minus {T₃} {T₄} T₁<<:T₂) N₁ N₂ = nfp′-invert-size-t-loop ⊝ T₃ T₄ T₁<<:T₂ N₁ N₂
nfp′-size-t-loop {p = p} ⊕ T₁ T₂ (<:-minus-minus-l {T₃} T₁<<:T₂) N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-size-t-loop ⊕ _ _ T₁<<:T₂ N₁ N₂
nfp′-size-t-loop {p = p} ⊕ T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₁<<:T₂) N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-size-t-loop ⊕ _ _ T₁<<:T₂ N₁ N₂

nfp′-size-t-loop {p = p} ⊝ T₁ T₃ (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃) N₁ N₃
  using N₂ ← normal-proto′-loop-<: _ _ T₁<<:T₂ N₁
  = trans (nfp′-size-t-loop ⊝ _ _ T₁<<:T₂ N₁ N₂) (nfp′-size-t-loop ⊝ _ _ T₂<<:T₃ N₂ N₃)
nfp′-size-t-loop {p = p} ⊝ T₁ T₂ <:-var N-Var N-Var = refl
nfp′-size-t-loop {p = p} ⊝ T₁ T₂ (<:-up T₁<<:T₂) (N-Up N) (N-Up N₁) = cong suc (nft-size _ _ T₁<<:T₂ N N₁)
nfp′-size-t-loop {p = p} ⊝ T₁ T₂ (<:-proto {⊙ = ⊕} #c⊆#d T₁<<:T₂) (N-ProtoP N) (N-ProtoP N₁) = cong suc $ nfp-size _ _ T₁<<:T₂ N N₁
nfp′-size-t-loop {p = p} ⊝ T₁ T₂ (<:-proto {⊙ = ⊝} #c⊆#d T₁<<:T₂) (N-ProtoP N) (N-ProtoP N₁) = sym $ cong suc $ nfp-size _ _ T₁<<:T₂ N₁ N
nfp′-size-t-loop {p = p} ⊝ T₁ T₂ (<:-proto {⊙ = ⊘} #c⊆#d T₁≡cT₂) (N-ProtoP N) (N-ProtoP N₁)
  rewrite nf-complete d?⊥ d?⊥ T₁≡cT₂ | np-unique N N₁
  = refl
nfp′-size-t-loop {p = p} ⊝ T₁ T₂ (<:-minus {T₃} {T₄} T₁<<:T₂) N₁ N₂ = sym $ nfp′-invert-size-t-loop ⊝ T₃ T₄ T₁<<:T₂ N₂ N₁
nfp′-size-t-loop {p = p} ⊝ T₁ T₂ (<:-minus-minus-l {T₃} T₁<<:T₂) N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-size-t-loop ⊝ _ _ T₁<<:T₂ N₁ N₂
nfp′-size-t-loop {p = p} ⊝ T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₁<<:T₂) N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-size-t-loop ⊝ _ _ T₁<<:T₂ N₁ N₂

nfp′-invert-size-t-loop ⊕ T₁ T₃ (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃) N₁ N₃
  using N₂ ← normal-proto′-loop-<:-minus _ _ T₂<<:T₃ N₁
  = trans (nfp′-invert-size-t-loop ⊕ _ _ T₂<<:T₃ N₁ N₂) (nfp′-invert-size-t-loop ⊕ _ _ T₁<<:T₂ N₂ N₃)
nfp′-invert-size-t-loop ⊕ T₁ T₂ <:-var N-Var N-Var = refl
nfp′-invert-size-t-loop ⊕ T₁ T₂ (<:-up T₁<<:T₂) (N-Up N) (N-Up N₁) = cong suc (sym $ nft-size _ _ T₁<<:T₂ N₁ N)
nfp′-invert-size-t-loop ⊕ T₁ T₂ (<:-proto {⊙ = ⊕} #c⊆#d T₁<<:T₂) (N-ProtoP N) (N-ProtoP N₁) = cong suc (sym $ nfp-size _ _ T₁<<:T₂ N₁ N)
nfp′-invert-size-t-loop ⊕ T₁ T₂ (<:-proto {⊙ = ⊝} #c⊆#d T₁<<:T₂) (N-ProtoP N) (N-ProtoP N₁) = cong suc (nfp-size _ _ T₁<<:T₂ N N₁)
nfp′-invert-size-t-loop ⊕ T₁ T₂ (<:-proto {⊙ = ⊘} #c⊆#d T₁≡cT₂) (N-ProtoP N) (N-ProtoP N₁)
  rewrite nf-complete d?⊥ d?⊥ T₁≡cT₂ | np-unique N N₁
  = refl
nfp′-invert-size-t-loop ⊕ T₁ T₂ (<:-minus {T₃} {T₄} T₁<<:T₂) N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₄) (nf-normal-proto T₄)
  = nfp′-size-t-loop ⊝ _ _ T₁<<:T₂ N₁ N₂
nfp′-invert-size-t-loop ⊕ T₁ T₂ (<:-minus-minus-l {T₃} T₁<<:T₂) N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-invert-size-t-loop ⊕ _ _ T₁<<:T₂ N₁ N₂
nfp′-invert-size-t-loop ⊕ T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₁<<:T₂) N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-invert-size-t-loop ⊕ _ _ T₁<<:T₂ N₁ N₂

nfp′-invert-size-t-loop ⊝ T₁ T₃ (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃) N₁ N₃
  using N₂ ← normal-proto′-loop-<:-minus _ _ T₂<<:T₃ N₃
  = trans (nfp′-invert-size-t-loop ⊝ _ _ T₁<<:T₂ N₁ N₂) (nfp′-invert-size-t-loop ⊝ _ _ T₂<<:T₃ N₂ N₃)
nfp′-invert-size-t-loop ⊝ T₁ T₂ <:-var N-Var N-Var = refl
nfp′-invert-size-t-loop ⊝ T₁ T₂ (<:-up T₁<<:T₂) (N-Up N) (N-Up N₁) = cong suc (nft-size _ _ T₁<<:T₂ N N₁)
nfp′-invert-size-t-loop ⊝ T₁ T₂ (<:-proto {⊙ = ⊕} x T₁<<:T₂) (N-ProtoP N) (N-ProtoP N₁) = cong suc (nfp-size _ _ T₁<<:T₂ N N₁)
nfp′-invert-size-t-loop ⊝ T₁ T₂ (<:-proto {⊙ = ⊝} x T₁<<:T₂) (N-ProtoP N) (N-ProtoP N₁) = cong suc (sym $ nfp-size _ _ T₁<<:T₂ N₁ N)
nfp′-invert-size-t-loop ⊝ T₁ T₂ (<:-proto {⊙ = ⊘} x T₁≡cT₂) (N-ProtoP N) (N-ProtoP N₁)
  rewrite nf-complete d?⊥ d?⊥ T₁≡cT₂ | np-unique N N₁
  = refl
nfp′-invert-size-t-loop ⊝ T₁ T₂ (<:-minus {T₃} {T₄} T₁<<:T₂) N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  rewrite t-minus-involution (nf ⊕ d?⊥ T₄) (nf-normal-proto T₄)
  = sym $ nfp′-size-t-loop ⊝ _ _ T₁<<:T₂ N₂ N₁
nfp′-invert-size-t-loop ⊝ T₁ T₂ (<:-minus-minus-l {T₃} T₁<<:T₂) N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-invert-size-t-loop ⊝ _ _ T₁<<:T₂ N₁ N₂
nfp′-invert-size-t-loop ⊝ T₁ T₂ (<:-minus-minus-r {T₂ = T₃} T₁<<:T₂) N₁ N₂
  rewrite t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  = nfp′-invert-size-t-loop ⊝ _ _ T₁<<:T₂ N₁ N₂
