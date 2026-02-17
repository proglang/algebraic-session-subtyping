open import Data.Empty using (⊥-elim)
-- open import Data.Fin
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; s≤s; z≤n; s≤s⁻¹)
open import Data.Nat.Properties using (≤-reflexive; ≤-refl; ≤-trans; n≤1+n; ⊔-comm; ⊔-assoc)
open import Data.Fin.Subset as Subset using (_⊆_)
open import Data.Fin.Subset.Properties using (⊆-refl; ⊆-antisym)
-- open import Data.List
open import Data.Product
-- open import Data.Sum
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; cong-app; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import Function using (const; _$_; case_of_)

module AlgorithmicComplete  where

open import Util
open import Kinds
open import Duality
open import Types
open import Subtyping
open import SubtypingProperties
open import AlgorithmicSubtyping
open import AlgorithmicSound

⊔-≤ₗ : ∀ {m n o} → m ⊔ n ≤ o → m ≤ o
⊔-≤ₗ {zero} mn≤o = z≤n
⊔-≤ₗ {suc m} {zero} mn≤o = mn≤o
⊔-≤ₗ {suc m} {suc n} (s≤s mn≤o) = s≤s (⊔-≤ₗ mn≤o)

⊔-≤ᵣ : ∀ {m n o} → m ⊔ n ≤ o → n ≤ o
⊔-≤ᵣ {zero} mn≤o = mn≤o
⊔-≤ᵣ {suc m} {zero} mn≤o = z≤n
⊔-≤ᵣ {suc m} {suc n} (s≤s mn≤o) = s≤s (⊔-≤ᵣ mn≤o)


shuffle-⊔ : ∀ x₁ x₂ y₁ y₂ → (x₁ ⊔ x₂) ⊔ (y₁ ⊔ y₂) ≡ (x₁ ⊔ y₁) ⊔ (x₂ ⊔ y₂)
shuffle-⊔ x₁ x₂ y₁ y₂ =
  begin
    x₁ ⊔ x₂ ⊔ (y₁ ⊔ y₂)
  ≡⟨ ⊔-assoc x₁ x₂ (y₁ ⊔ y₂) ⟩
    x₁ ⊔ (x₂ ⊔ (y₁ ⊔ y₂))
  ≡⟨ cong (x₁ ⊔_) (sym (⊔-assoc x₂ y₁ y₂)) ⟩
    x₁ ⊔ ((x₂ ⊔ y₁) ⊔ y₂)
  ≡⟨ cong (x₁ ⊔_) (cong (_⊔ y₂) (⊔-comm x₂ y₁)) ⟩
    x₁ ⊔ ((y₁ ⊔ x₂) ⊔ y₂)
  ≡⟨ cong (x₁ ⊔_) (⊔-assoc y₁ x₂ y₂) ⟩
    x₁ ⊔ (y₁ ⊔ (x₂ ⊔ y₂))
  ≡⟨ sym (⊔-assoc x₁ y₁ (x₂ ⊔ y₂)) ⟩
    x₁ ⊔ y₁ ⊔ (x₂ ⊔ y₂)
  ∎

-- algorithmic subtyping is complete

complete-algₚ : ∀ {n} {T₁ T₂ : Ty Δ KP}
  → T₁ <: T₂
  → ∀ {f₁ f₂} {N₁ : NormalProto (nf ⊕ f₁ T₁)}{N₂ : NormalProto (nf ⊕ f₂ T₂)}
  → sizeₚ N₁ ⊔ sizeₚ N₂ ≤ n
  → N₁ <:ₚ N₂

complete-algₚ-inverted : ∀ {n} {T₁ T₂ : Ty Δ KP}
  → T₁ <: T₂
  → ∀ {f₁ f₂} {N₁ : NormalProto (t-minus (nf ⊕ f₁ T₁))}{N₂ : NormalProto (t-minus (nf ⊕ f₂ T₂))}
  → sizeₚ N₁ ⊔ sizeₚ N₂ ≤ n
  → N₂ <:ₚ N₁

complete-<<:ₚ : ∀ {n} {⊙} {T₁ T₂ : Ty Δ KP}
  → T₁ <<:[ ⊙ ] T₂
  → ∀ {f₁ f₂} {N₁ : NormalProto (nf ⊕ f₁ T₁)}{N₂ : NormalProto (nf ⊕ f₂ T₂)}
  → sizeₚ N₁ ⊔ sizeₚ N₂ ≤ n
  → N₁ <<:ₚ[ ⊙ ] N₂

complete-<<:ₚ′ : ∀ {n}{⊙} {T₁ T₂ : Ty Δ KP}
  → T₁ <<:[ injᵥ ⊙ ] T₂
  → ∀ {f₁ f₂} {N₁ : NormalProto′ (nf ⊕ f₁ T₁)}{N₂ : NormalProto′ (nf ⊕ f₂ T₂)}
  → sizeₚ′ N₁ ⊔ sizeₚ′ N₂ ≤ n
  → N₁ <<:ₚ′[ injᵥ ⊙ ] N₂

complete-<<:ₚ′-inverted : ∀ {n} {⊙} {T₁ T₂ : Ty Δ KP}
  → T₁ <<:[ injᵥ ⊙ ] T₂
  → ∀ {f₁ f₂} {N₁ : NormalProto′ (t-minus (nf ⊕ f₁ T₁))}{N₂ : NormalProto′ (t-minus (nf ⊕ f₂ T₂))}
  → sizeₚ′ N₁ ⊔ sizeₚ′ N₂ ≤ n
  → N₂ <<:ₚ′[ injᵥ ⊙ ] N₁

complete-algₜ : ∀ {n} {p : Polarity} {T₁ T₂ : Ty Δ (KV pk m)}
  → T₁ <: T₂
  → ∀ {f₁ f₂} {N₁ : NormalTy (nf p f₁ T₁)}{N₂ : NormalTy (nf p f₂ T₂)}
  → sizeₜ N₁ ⊔ sizeₜ N₂ ≤ n
  → N₁ <<:ₜ[ p ] N₂

----

complete-algₚ {n = suc n} {T₁ = T₁} {T₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) {f₁} {f₂} {N₁} {N₃} sz≤
  using N₂ ← nf-normal-proto T₂
  rewrite dual-all-irrelevant f₁ d?⊥ | dual-all-irrelevant f₂ d?⊥
  = <:ₚ-trans (complete-algₚ {n = suc n} T₁<:T₂ {N₁ = N₁} {N₂ = N₂} (≤-trans (≤-reflexive (cong (sizeₚ N₁ ⊔_) (nfp-size _ _ T₂<:T₃ N₂ N₃))) sz≤))
              (complete-algₚ {n = suc n} T₂<:T₃ {N₁ = N₂} {N₂ = N₃} (≤-trans (≤-reflexive (cong (_⊔ sizeₚ N₃) (sym (nfp-size _ _ T₁<:T₂ N₁ N₂)))) sz≤))
complete-algₚ {n = suc n} {T₁ = T₁} {T₂} <:-var {f₁} {f₂} {N-Normal N-Var} {N-Normal N-Var} sz≤ = <:ₚ-plus <:ₚ′-var
complete-algₚ {n = suc n} {T₁ = T₁} {T₂}  (<:-up T₁<:T₂) {f₁} {f₂} {N-Normal (N-Up N₁)} {N-Normal (N-Up N₂)} (s≤s sz≤)
  = <:ₚ-plus (<:ₚ′-up (complete-algₜ {n = n} T₁<:T₂ {N₁ = N₁}{N₂ = N₂} (≤-trans (n≤1+n _) sz≤)))
complete-algₚ {n = suc n} {T₁ = T₁} {T₂} (<:-proto #c⊆#d T₁<<:T₂) {f₁} {f₂} {N-Normal (N-ProtoP N₁)} {N-Normal (N-ProtoP N₂)} sz≤ = <:ₚ-plus (<:ₚ′-proto #c⊆#d (complete-<<:ₚ T₁<<:T₂ {N₁ = N₁} {N₂ = N₂} (≤-trans (n≤1+n _) (s≤s⁻¹ sz≤))))
complete-algₚ {n = suc n} {T₁ = T-Minus T₁} {T-Minus T₂} (<:-minus T₁<:T₂) {f₁} {f₂} {N₁} {N₂} sz≤
  rewrite ⊔-comm (sizeₚ N₁) (sizeₚ N₂)
  = complete-algₚ-inverted T₁<:T₂ {N₁ = N₂} {N₂ = N₁} sz≤
complete-algₚ {n = suc n} {T₁ = T-Minus (T-Minus T₁)} {T₂}  (<:-minus-minus-l T₁<:T₂) {f₁} {f₂} {N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-algₚ T₁<:T₂ {N₁ = N₁} {N₂ = N₂} sz≤
complete-algₚ {n = suc n} {T₁ = T₁} {_} (<:-minus-minus-r {T₂ = T₃} T₁<:T₂) {f₁} {f₂} {N₁} {N₂} sz≤
  using eq ← t-minus-involution (nf ⊕ d?⊥ T₃) (nf-normal-proto T₃)
  using r ← complete-algₚ {n = suc n} T₁<:T₂ {N₁ = N₁} {N₂ = subst NormalProto eq N₂} (≤-trans (≤-reflexive (cong (sizeₚ N₁ ⊔_) (sym $ sizeₚ-subst N₂ eq))) sz≤)
  = subst-<:ₚ eq r 

----

complete-algₚ-inverted {n = suc n} {T₁ = T₁} {T₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) {f₁} {f₂} {N₁} {N₃} sz≤
  using N₂ ← nf-normal-proto-inverted T₂
  rewrite dual-all-irrelevant f₁ d?⊥ | dual-all-irrelevant f₂ d?⊥
   = <:ₚ-trans (complete-algₚ-inverted {n = suc n} T₂<:T₃ {N₁ = N₂} {N₂ = N₃} (≤-trans (≤-reflexive (cong (_⊔ sizeₚ N₃) (nfp-invert-size _ _ T₁<:T₂ N₂ N₁))) sz≤))
               (complete-algₚ-inverted {n = suc n} T₁<:T₂ {N₁ = N₁} {N₂ = N₂} (≤-trans (≤-reflexive (cong (sizeₚ N₁ ⊔_) (sym $ nfp-invert-size _ _ T₂<:T₃ N₃ N₂))) sz≤)) -- N2=N3
complete-algₚ-inverted {n = suc n} {T₁ = T₁} {T₂} <:-var {f₁} {f₂} {N-Minus N-Var} {N-Minus N-Var} sz≤ = <:ₚ-minus <:ₚ′-var
complete-algₚ-inverted {n = suc n} {T₁ = T₁} {T₂} (<:-up T₁<:T₂) {f₁} {f₂} {N-Minus (N-Up N₁)} {N-Minus (N-Up N₂)} (s≤s sz≤)
  = <:ₚ-minus (<:ₚ′-up (complete-algₜ {n = n} T₁<:T₂ {N₁ = N₁} {N₂ = N₂} (≤-trans (n≤1+n _) sz≤)))
complete-algₚ-inverted {n = suc n} {T₁ = T₁} {T₂} (<:-proto #c⊆#d T₁<<:T₂) {f₁} {f₂} {N-Minus (N-ProtoP N₁)} {N-Minus (N-ProtoP N₂)} (s≤s (s≤s sz≤)) = <:ₚ-minus (<:ₚ′-proto #c⊆#d (complete-<<:ₚ T₁<<:T₂ {N₁ = N₁} {N₂ = N₂} sz≤))
complete-algₚ-inverted {n = suc n} {T₁ = T-Minus T₁} {T-Minus T₂} (<:-minus T₁<:T₂) {f₁} {f₂} {N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁) |  t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  | ⊔-comm (sizeₚ N₁) (sizeₚ N₂)
  = complete-algₚ T₁<:T₂ {N₁ = N₂} {N₂ = N₁} sz≤
complete-algₚ-inverted {n = suc n} {T₁ = T-Minus (T-Minus T₁)} {T₂} (<:-minus-minus-l T₁<:T₂) {f₁} {f₂} {N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-algₚ-inverted T₁<:T₂ {N₁ = N₁}{N₂ = N₂} sz≤
complete-algₚ-inverted {n = suc n} {T₁ = T₁} {T-Minus (T-Minus T₂)} (<:-minus-minus-r T₁<:T₂) {f₁} {f₂} {N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-algₚ-inverted T₁<:T₂ {N₁ = N₁}{N₂ = N₂} sz≤

----

complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊕} {T₁} {T₃} (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃) {f₁}{f₂} {N₁ = N₁} {N₃} sz≤
  rewrite dual-all-irrelevant f₁ d?⊥
  using N₂ ← normal-proto′-<:-minus _ _ T₂<<:T₃ N₁
  using N₁<:N₂ ← complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊝} T₂<<:T₃ {N₁ = N₂}{N₂ = N₁} (≤-trans (≤-trans (≤-reflexive (cong (_⊔ sizeₚ′ N₁) (nfp′-invert-size _ _ T₁<<:T₂ N₂ N₃))) (≤-reflexive (⊔-comm (sizeₚ′ N₃) (sizeₚ′ N₁)))) sz≤)
  using N₂<:N₃ ← complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊝}  T₁<<:T₂ {N₁ = N₃}{N₂ = N₂} (≤-trans (≤-trans (≤-reflexive (cong (sizeₚ′ N₃ ⊔_) $ sym $ nfp′-invert-size _ _ T₂<<:T₃ N₁ N₂)) (≤-reflexive (⊔-comm (sizeₚ′ N₃) (sizeₚ′ N₁)))) sz≤)
  = <:ₚ′-trans N₁<:N₂ N₂<:N₃ 
complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊕} {_} {_} (<:-minus {T₂ = T₁}{T₁ = T₂} T₁<<:T₂) {N₁ = N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  | t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} T₁<<:T₂ {N₁ = N₁} {N₂ = N₂} sz≤
complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊕} {T₁} {T-Minus (T-Minus T₂)} (<:-minus-minus-l T₁<<:T₂) {N₁ = N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′-inverted {⊙ = ⊕} T₁<<:T₂ {N₁ = N₁} {N₂ = N₂} sz≤
complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊕} {T-Minus (T-Minus T₁)} {T₂} (<:-minus-minus-r T₁<<:T₂) {N₁ = N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-<<:ₚ′-inverted {⊙ = ⊕} T₁<<:T₂ {N₁ = N₁} {N₂ = N₂} sz≤

complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊝} {T₁} {T₃} (<:-trans T₁<<:T₂ T₂<<:T₃) {f₁ = f₁}{f₂ = f₂} {N₁ = N₁} {N₃} sz≤
  rewrite dual-all-irrelevant f₂ d?⊥
  using N₂ ← normal-proto′-<:-minus _ _ T₂<<:T₃ N₃
  using N₃<:N₂ ← complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊕} T₂<<:T₃ {N₁ = N₃}{N₂ = N₂} (≤-trans (≤-reflexive (trans (cong (sizeₚ′ N₃ ⊔_) $ nfp′-invert-size _ _ T₁<<:T₂ N₂ N₁) (⊔-comm (sizeₚ′ N₃) (sizeₚ′ N₁)))) sz≤)
  using N₂<:N₁ ← complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊕} T₁<<:T₂ {N₁ = N₂}{N₂ = N₁} (≤-trans (≤-reflexive (trans (cong (_⊔ sizeₚ′ N₁) $ sym $ nfp′-invert-size _ _ T₂<<:T₃ N₃ N₂) (⊔-comm (sizeₚ′ N₃) (sizeₚ′ N₁)))) sz≤)
  = <:ₚ′-trans N₃<:N₂ N₂<:N₁
complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊝} {T-Minus T₁} {T-Minus T₂} (<:-minus T₁<<:T₂) {N₁ = N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  | t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′ {⊙ = ⊕} T₁<<:T₂ {N₁ = N₁} {N₂ = N₂} sz≤
complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊝} {T-Minus (T-Minus T₁)} {T₂} (<:-minus-minus-l T₁<<:T₂) {N₁ = N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-<<:ₚ′-inverted {⊙ = ⊝} T₁<<:T₂ {N₁ = N₁}{N₂ = N₂} sz≤
complete-<<:ₚ′-inverted {n = suc n} {⊙ = ⊝} {T₁} {T-Minus (T-Minus T₂)} (<:-minus-minus-r T₁<<:T₂) {N₁ = N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′-inverted {⊙ = ⊝} T₁<<:T₂ {N₁ = N₁}{N₂ = N₂} sz≤

complete-<<:ₚ′ {n = suc n} {⊙ = ⊕} {T₁} {T₃} (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃) {f₁}{f₂} {N₁ = N₁} {N₃} sz≤
  rewrite dual-all-irrelevant f₂ d?⊥
  using N₂ ← normal-proto′-<: _ _ T₁<<:T₂ N₃
  using N₃<:N₂ ← complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} {T₁ = T₃}{T₂ = T₂} T₁<<:T₂ {N₁ = N₃}{N₂ = N₂} (≤-trans (≤-reflexive (trans (cong (sizeₚ′ N₃ ⊔_) $ nfp′-size _ _ T₂<<:T₃ N₂ N₁) (⊔-comm (sizeₚ′ N₃) (sizeₚ′ N₁)))) sz≤)
  using N₁<:N₂ ← complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} {T₁ = T₂}{T₂ = T₁}  T₂<<:T₃ {N₁ = N₂}{N₂ = N₁} (≤-trans (≤-reflexive (trans (cong (_⊔ sizeₚ′ N₁) $ sym $ nfp′-size _ _ T₁<<:T₂ N₃ N₂) (⊔-comm (sizeₚ′ N₃) (sizeₚ′ N₁)))) sz≤)
  = <:ₚ′-trans N₃<:N₂ N₁<:N₂
complete-<<:ₚ′ {n = suc n} {⊙ = ⊕}  <:-var {N₁ = N-Var} {N-Var} sz≤ = <:ₚ′-var
complete-<<:ₚ′ {n = suc n} {⊙ = ⊕} (<:-up T₁<<:T₂) {N₁ = N-Up N₁} {N-Up N₂} (s≤s sz≤)
  rewrite ⊔-comm (sizeₜ N₁) (sizeₜ N₂)
  = <:ₚ′-up (complete-algₜ {p = ⊕} T₁<<:T₂ {N₁ = N₂} {N₂ = N₁} sz≤)
complete-<<:ₚ′ {n = suc n} {⊙ = ⊕} (<:-proto {⊙ = ⊙} #c⊆#d T₁<<:T₂) {N₁ = N-ProtoP N₁} {N-ProtoP N₂} (s≤s sz≤)
  rewrite ⊔-comm (sizeₚ N₁) (sizeₚ N₂)
  = <:ₚ′-proto #c⊆#d (complete-<<:ₚ {⊙ = ⊙} T₁<<:T₂ sz≤)
complete-<<:ₚ′ {n = suc n} {⊙ = ⊕} (<:-minus T₁<<:T₂) {N₁ = N₁} {N₂} sz≤ = complete-<<:ₚ′-inverted {⊙ = ⊝} T₁<<:T₂ sz≤
complete-<<:ₚ′ {n = suc n} {⊙ = ⊕} (<:-minus-minus-l {T₁} T₁<<:T₂) {N₁ = N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-<<:ₚ′ {⊙ = ⊕} T₁<<:T₂ sz≤
complete-<<:ₚ′ {n = suc n} {⊙ = ⊕} (<:-minus-minus-r {T₂ = T₂} T₁<<:T₂) {N₁ = N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′ {⊙ = ⊕} T₁<<:T₂ sz≤

complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} {T₁} {T₃} (<:-trans {T₂ = T₂} T₁<<:T₂ T₂<<:T₃) {f₁}{f₂} {N₁ = N₁} {N₃} sz≤
  rewrite dual-all-irrelevant f₁ d?⊥
  using N₂ ← normal-proto′-<: _ _ T₁<<:T₂ N₁
  using N₁<:N₂ ← complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} {T₁ = T₁}{T₂ = T₂} T₁<<:T₂ {N₁ = N₁}{N₂ = N₂} (≤-trans (≤-reflexive (cong (sizeₚ′ N₁ ⊔_) $ nfp′-size _ _ T₂<<:T₃ N₂ N₃)) sz≤)
  using N₂<:N₃ ← complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} {T₁ = T₂}{T₂ = T₃} T₂<<:T₃ {N₁ = N₂}{N₂ = N₃} (≤-trans (≤-reflexive (cong (_⊔ sizeₚ′ N₃) $ sym $ nfp′-size _ _ T₁<<:T₂ N₁ N₂)) sz≤)
  = <:ₚ′-trans N₁<:N₂ N₂<:N₃
complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} <:-var {N₁ = N-Var} {N-Var} sz≤ = <:ₚ′-var
complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} (<:-up T₁<<:T₂) {N₁ = N-Up N₁} {N-Up N₂} (s≤s sz≤) = <:ₚ′-up (complete-algₜ {p = ⊕} T₁<<:T₂ {N₁ = N₁} {N₂ = N₂} sz≤)
complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} (<:-proto {⊙ = ⊕} #c⊆#d T₁<<:T₂) {N₁ = N-ProtoP N₁} {N-ProtoP N₂} (s≤s sz≤) = <:ₚ′-proto #c⊆#d (complete-algₚ{n = n} T₁<<:T₂ {N₁ = N₁} {N₂ = N₂} sz≤)
complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} (<:-proto {⊙ = ⊝} #c⊆#d T₁<<:T₂) {N₁ = N-ProtoP N₁} {N-ProtoP N₂} (s≤s sz≤) = <:ₚ′-proto #c⊆#d (complete-algₚ {n = n} T₁<<:T₂ {N₁ = N₂} {N₂ = N₁} (≤-trans (≤-reflexive (⊔-comm (sizeₚ N₂) (sizeₚ N₁))) sz≤))
complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} (<:-proto {⊙ = ⊘} #c⊆#d T₁≡cT₂) {N₁ = N-ProtoP N₁} {N-ProtoP N₂} (s≤s sz≤) = <:ₚ′-proto #c⊆#d (nf-complete d?⊥ d?⊥ T₁≡cT₂)
complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} (<:-minus T₁<<:T₂) {N₁ = N₁} {N₂} sz≤ = complete-<<:ₚ′-inverted {⊙ = ⊕} T₁<<:T₂ sz≤
complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} (<:-minus-minus-l {T₁} T₁<<:T₂) {N₁ = N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₁) (nf-normal-proto T₁)
  = complete-<<:ₚ′ {⊙ = ⊝} T₁<<:T₂ sz≤
complete-<<:ₚ′ {n = suc n} {⊙ = ⊝} (<:-minus-minus-r {T₂ = T₂} T₁<<:T₂) {N₁ = N₁} {N₂} sz≤
  rewrite t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  = complete-<<:ₚ′ {⊙ = ⊝} T₁<<:T₂ sz≤

----

complete-<<:ₚ {⊙ = ⊕} T₁<<:T₂ sz≤ = complete-algₚ T₁<<:T₂ sz≤
complete-<<:ₚ {⊙ = ⊝} T₁<<:T₂ {N₁ = N₁} {N₂ = N₂} sz≤
  rewrite ⊔-comm (sizeₚ N₁) (sizeₚ N₂)
  = complete-algₚ T₁<<:T₂ sz≤
complete-<<:ₚ {⊙ = ⊘} T₁≡cT₂ sz≤ = nf-complete _ _ T₁≡cT₂


complete-algₜ {n = suc n} {p = ⊕} (<:-msg {T₁ = T₁} {p = p₃} {T₂ = T₂} T₁<<:T₂ S₁<:S₂) {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ N₁ NS₁} {N-Msg p₂ N₂ NS₂} (s≤s sz≤)
  rewrite shuffle-⊔ (sizeₚ′ N₁) (sizeₜ NS₁) (sizeₚ′ N₂) (sizeₜ NS₂)
  rewrite t-loop-sub-<<: p₃ p₃ T₁<<:T₂
  using eq₁ ← (nfp′-idempotent N₁)
  using eq₂ ← (nfp′-idempotent N₂)
  with       (complete-algₜ S₁<:S₂ {N₁ = NS₁} {N₂ = NS₂} (⊔-≤ᵣ {sizeₚ′ N₁ ⊔ sizeₚ′ N₂} {sizeₜ NS₁ ⊔ sizeₜ NS₂} sz≤))
  |          complete-<<:ₚ′{n = n}{⊙ = (t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₁)}
                           {T₁ = t-loop p₃ (nf ⊕ d?⊥ T₁) .proj₂}{T₂ = t-loop p₃ (nf ⊕ d?⊥ T₂) .proj₂}
                           (lemma-sub-loop {p₃ = p₃} T₁<<:T₂)
                           {N₁ = subst NormalProto′ (sym eq₁) N₁}{N₂ = subst NormalProto′ (sym eq₂) N₂}
                           (subst₂ (λ s₁ s₂ → s₁ ⊔ s₂ ≤ n)
                             (sizeₚ′-subst N₁ (sym eq₁))
                             (sizeₚ′-subst N₂ (sym eq₂))
                             (⊔-≤ₗ {sizeₚ′ N₁ ⊔ sizeₚ′ N₂} {sizeₜ NS₁ ⊔ sizeₜ NS₂} sz≤))
... | ihS | ihT
  rewrite t-loop-sub-<<: p₃ p₃ T₁<<:T₂
  = <:ₜ-msg (subst-<<: (sym eq₁) (sym eq₂) ihT) ihS


complete-algₜ {n = suc n} {p = ⊝} (<:-msg {T₁ = T₁} {p = p₃} {T₂ = T₂} T₁<<:T₂ S₁<:S₂) {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ N₁ NS₁} {N-Msg p₂ N₂ NS₂} (s≤s sz≤)
  rewrite shuffle-⊔ (sizeₚ′ N₁) (sizeₜ NS₁) (sizeₚ′ N₂) (sizeₜ NS₂)
  rewrite sym (t-loop-sub-<<: p₃ (invert p₃) T₁<<:T₂)
  using eq₁ ← nfp′-idempotent N₁
  using eq₂ ← nfp′-idempotent N₂
  with (complete-algₜ S₁<:S₂ {N₁ = NS₁} {N₂ = NS₂} (⊔-≤ᵣ {sizeₚ′ N₁ ⊔ sizeₚ′ N₂} {sizeₜ NS₁ ⊔ sizeₜ NS₂} sz≤))
  |    complete-<<:ₚ′ {n = n}{⊙ = t-loop (invert p₃) (nf ⊕ d?⊥ T₁) .proj₁}
                      (lemma-sub-loop-right {p₃ = invert p₃} (<<:-invert T₁<<:T₂))
                      {f₁ = d?⊥}{f₂ = d?⊥}
                      {N₁ = subst NormalProto′ (sym eq₂) N₂} {N₂ = subst NormalProto′ (sym eq₁) N₁}
                      (subst₂ (λ s₁ s₂ → s₁ ⊔ s₂ ≤ n)
                        (sizeₚ′-subst N₂ (sym eq₂))
                        (sizeₚ′-subst N₁ (sym eq₁))
                        (≤-trans (≤-reflexive (⊔-comm (sizeₚ′ N₂) (sizeₚ′ N₁))) ((⊔-≤ₗ {sizeₚ′ N₁ ⊔ sizeₚ′ N₂} {sizeₜ NS₁ ⊔ sizeₜ NS₂} sz≤))))
... | ihS | ihT
  = <:ₜ-msg (subst-<<: (sym eq₂) (sym eq₁) ihT) ihS

complete-algₜ {n = suc n} {p = p} {T₁ = T₁} {T₃} (<:-trans {T₂ = T₂} T₁<:T₂ T₂<:T₃) {f₁ = f₁} {f₂} {N₁ = N₁} {N₃} sz≤
  using N₂ ← nf-normal-type p f₁ T₂
  using N₁<<:N₂ ← complete-algₜ {n = suc n} {T₁ = T₁}{T₂} T₁<:T₂ {N₁ = N₁}{N₂ = N₂} (≤-trans (≤-reflexive (cong (sizeₜ N₁ ⊔_) (nft-size _ _ T₂<:T₃ N₂ N₃))) sz≤)
  using N₂<<:N₁ ← complete-algₜ {n = suc n} {T₁ = T₂}{T₃} T₂<:T₃ {N₁ = N₂}{N₂ = N₃} (≤-trans (≤-reflexive (cong (_⊔ sizeₜ N₃) (sym $ nft-size _ _ T₁<:T₂ N₁ N₂))) sz≤) -- N2=N1
  = <<:ₜ-trans N₁<<:N₂ N₂<<:N₁
complete-algₜ {n = suc n} {p = p} (<:-sub {T₁ = T₁}{T₂ = T₂} K≤K′ T₁<:T₂) {f₁ = f₁} {f₂} {N₁ = N-Sub N₁} {N-Sub N₂} (s≤s sz≤)
  = <<:ₜ-sub{T₁ = T₁}{T₂ = T₂}{f₁ = λ x → dualizable-sub (f₁ x) K≤K′}{f₂ = λ x → dualizable-sub (f₂ x) K≤K′}{km≤ = K≤K′} (complete-algₜ {p = p} T₁<:T₂ {N₁ = N₁}{N₂ = N₂} sz≤)
complete-algₜ {n = suc n} {p = p} {T₁ = T-Dual D-S (T-Sub (≤k-step ≤p-refl _) T)} {T₂ = T-Sub K≤K′ (T-Dual D-S T)} (<:-sub-dual-l {T = T} {K≤K′ = K≤K′}) {f₁ = f₁} {f₂} {N₁ = N-Sub N₁} {N-Sub N₂} sz≤
  rewrite nt-unique N₁ N₂
  = <<:ₜ-sub-invert {p = p}{T₁ = T}{T₂ = T}{f₁ = const D-S}{f₂ = const D-S}{km≤ = K≤K′} (<<:ₜ-refl {T = (nf (invert p) (λ x₁ → D-S) T)} N₂)
complete-algₜ {n = suc n} {p = p} {T₁ = T-Sub K≤K′ (T-Dual D-S T)} {T₂ = T-Dual D-S (T-Sub (≤k-step ≤p-refl _) T)} <:-sub-dual-r {f₁ = f₁} {f₂} {N₁ = N-Sub N₁} {N-Sub N₂} sz≤
  rewrite nt-unique N₁ N₂
  = <<:ₜ-sub-invert {p = p}{T₁ = T}{T₂ = T}{f₁ = const D-S}{f₂ = const D-S}{km≤ = K≤K′} (<<:ₜ-refl {T = (nf (invert p) (λ x₁ → D-S) T)} N₂)
complete-algₜ {n = suc n} {p = ⊕}{T₁ = T-Var x} <:-var {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} sz≤
  rewrite nt-unique N₁ N₂
  = <<:ₜ-refl {T = T-Var x}{⊕} N₂
complete-algₜ {n = suc n} {p = ⊝} <:-var {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} sz≤
  rewrite dual-all-irrelevant f₁ f₂ | nt-unique N₁ N₂
  = <<:ₜ-refl {T = T-Dual _ (T-Var _)} {p = ⊝} N₂
complete-algₜ {n = suc n} {p = ⊕} <:-dual-var {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} sz≤
  rewrite nt-unique N₁ N₂
  = <<:ₜ-refl {T = T-Dual D-S (T-Var _)} {p = ⊕} N₂
complete-algₜ {n = suc n} {p = ⊝} {T₁ = T-Dual D-S (T-Var x)} <:-dual-var {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} sz≤
  rewrite nt-unique N₁ N₂
  = <<:ₜ-refl {T = T-Var x}{⊝} N₂
complete-algₜ {n = suc n} {p = p} <:-base {f₁ = f₁} {f₂} {N₁ = N-Base} {N-Base} sz≤ = <<:ₜ-base
complete-algₜ {n = suc n} {p = ⊕} (<:-fun T₁<:T₂ T₁<:T₃) {f₁ = f₁} {f₂} {N₁ = N-Arrow N₁ N₃} {N-Arrow N₂ N₄} (s≤s sz≤)
  rewrite shuffle-⊔ (sizeₜ N₁) (sizeₜ N₃) (sizeₜ N₂) (sizeₜ N₄)
  = <:ₜ-arrow (complete-algₜ T₁<:T₂ {N₁ = N₂}{N₂ = N₁} (≤-trans (≤-reflexive (⊔-comm (sizeₜ N₂) (sizeₜ N₁))) (⊔-≤ₗ {sizeₜ N₁ ⊔ sizeₜ N₂} {sizeₜ N₃ ⊔ sizeₜ N₄} sz≤)))
              (complete-algₜ T₁<:T₃ {N₁ = N₃} {N₂ = N₄} (⊔-≤ᵣ {sizeₜ N₁ ⊔ sizeₜ N₂} {sizeₜ N₃ ⊔ sizeₜ N₄} sz≤))
complete-algₜ {n = suc n} {p = ⊝} (<:-fun {≤pk = ≤p-refl} T₁<:T₂ T₁<:T₃) {f₁ = f₁} {f₂} {N₁ = N-Arrow N₁ N₃} {N-Arrow N₂ N₄} sz≤
  with () ←  f₁ refl
complete-algₜ {n = suc n} {p = ⊝} (<:-fun {≤pk = ≤p-step <p-mt} T₁<:T₂ T₁<:T₃) {f₁ = f₁} {f₂} {N₁ = N-Arrow N₁ N₃} {N-Arrow N₂ N₄} sz≤
  with () ← f₁ refl
complete-algₜ {n = suc n} {p = ⊕} (<:-protoD T₁<:T₂) {f₁ = f₁} {f₂} {N₁ = N-ProtoD N₁} {N-ProtoD N₂} (s≤s sz≤) = <:ₜ-data (complete-algₜ T₁<:T₂ {N₁ = N₁} {N₂ = N₂} sz≤)
complete-algₜ {n = suc n} {p = ⊝} (<:-protoD T₁<:T₂) {f₁ = f₁} {f₂} {N₁ = N-ProtoD N₁} {N-ProtoD N₂} sz≤
  with () ← f₁ refl
complete-algₜ {n = suc n} {p = ⊕} (<:-all T₁<:T₂) {f₁ = f₁} {f₂} {N₁ = N-Poly N₁} {N-Poly N₂} (s≤s sz≤) = <:ₜ-poly (complete-algₜ {n = n} T₁<:T₂ {N₁ = N₁} {N₂ = N₂} sz≤)
complete-algₜ {n = suc n} {p = ⊝} (<:-all T₁<:T₂) {f₁ = f₁} {f₂} {N₁ = N-Poly N₁} {N-Poly N₂} sz≤
  with () ← f₁ refl
complete-algₜ {n = suc n} {p = ⊕} {T₁ = T-Msg p₁ T₁ (T-Dual D-S S₁)} {T₂ = T-Dual D-S (T-Msg .(invert p₁) T₁ S₁)} (<:-dual-msg-l-new refl) {f₁ = f₁} {f₂} {N₁ = N-Msg p₂ NT₁ NS₁} {N-Msg p₃ NT₂ NS₂} sz≤
  rewrite invert-involution {p₁} | nt-unique NS₁ NS₂ | np′-unique NT₁ NT₂
  = <:ₜ-msg (<<:ₚ′-refl NT₂) (<:ₜ-refl NS₂)
complete-algₜ {n = suc n} {p = ⊝} {T₁ = T-Msg p₁ T₁ (T-Dual D-S S₁)} {T₂ = T-Dual D-S (T-Msg .(invert p₁) T₁ S₁)} (<:-dual-msg-l-new refl) {f₁ = f₁} {f₂} {N₁ = N-Msg p₂ NT₁ NS₁} {N-Msg p₃ NT₂ NS₂} sz≤
  rewrite nt-unique NS₁ NS₂ | np′-unique NT₁ NT₂
  = <:ₜ-msg (<<:ₚ′-refl NT₂) (<:ₜ-refl NS₂)
complete-algₜ {n = suc n} {p = ⊕} {T₁ = T-Dual D-S (T-Msg p₁ T S)} {T₂ = T-Msg p₁′ T (T-Dual D-S S)} (<:-dual-msg-r-new refl) {f₁ = f₁} {f₂} {N₁ = N-Msg p₂ NT₁ NS₁} {N-Msg p₃ NT₂ NS₂} sz≤
  rewrite invert-involution {p₁′} | nt-unique NS₁ NS₂ | np′-unique NT₁ NT₂
  = <:ₜ-msg (<<:ₚ′-refl NT₂) (<:ₜ-refl NS₂)
complete-algₜ {n = suc n} {p = ⊝} {T₁ = T-Dual D-S (T-Msg p₁ T S)} {T₂ = T-Msg p₁′ T (T-Dual D-S S)} (<:-dual-msg-r-new refl) {f₁ = f₁} {f₂} {N₁ = N-Msg p₂ NT₁ NS₁} {N-Msg p₃ NT₂ NS₂} sz≤
  rewrite nt-unique NS₁ NS₂ | np′-unique NT₁ NT₂
  = <:ₜ-msg (<<:ₚ′-refl NT₂) (<:ₜ-refl NS₂)
complete-algₜ {n = suc n} {p = p} <:-dual-end-l {f₁ = f₁} {f₂} {N₁ = N-End} {N-End} sz≤ = <<:ₜ-end
complete-algₜ {n = suc n} {p = p} <:-dual-end-r {f₁ = f₁} {f₂} {N₁ = N-End} {N-End} sz≤ = <<:ₜ-end
complete-algₜ {n = suc n} {p = p} <:-end {f₁ = f₁} {f₂} {N₁ = N-End} {N-End} sz≤ = <<:ₜ-end
complete-algₜ {n = suc n} {p = p} (<:-dual-dual-l-new D-S) {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} sz≤
  rewrite invert-involution {p} | dual-all-irrelevant (const D-S) f₂ | nt-unique N₁ N₂
  = <<:ₜ-refl N₂ 
complete-algₜ {n = suc n} {p = p} (<:-dual-dual-r-new D-S) {f₁ = f₁} {f₂} {N₁ = N₁} {N₂} sz≤
  rewrite invert-involution {p} | dual-all-irrelevant (const D-S) f₁ | nt-unique N₁ N₂
  = <<:ₜ-refl N₂
complete-algₜ {n = suc n} {p = ⊕} (<:-msg-minus {p₁ = p₃} {T} refl) {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ NP₁ NS₁} {N-Msg p₂ NP₂ NS₂} sz≤
  rewrite t-loop-minus {p = p₃} (nf ⊕ d?⊥ T) | dual-all-irrelevant f₁ f₂ | nt-unique NS₁ NS₂ | np′-unique NP₁ NP₂
  = <:ₜ-msg (<<:ₚ′-refl NP₂) (<:ₜ-refl NS₂)
complete-algₜ {n = suc n} {p = ⊝} {T₁ = T-Msg p (T-Minus T) S}{T₂ = T-Msg .(invert p) T S} (<:-msg-minus {p₁ = p₃} refl) {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ NP₁ NS₁} {N-Msg p₂ NP₂ NS₂} sz≤
  rewrite invert-involution {p₃}
  rewrite t-loop-minus-invert {p = p} (nf ⊕ d?⊥ T) | dual-all-irrelevant f₁ f₂ | nt-unique NS₁ NS₂ | np′-unique NP₁ NP₂
  = <:ₜ-msg (<<:ₚ′-refl NP₂) (<:ₜ-refl NS₂)
complete-algₜ {n = suc n} {p = ⊕} (<:-minus-msg {p₂ = p₃} {T = T} refl) {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ NP₁ NS₁} {N-Msg p₂ NP₂ NS₂} sz≤
  rewrite t-loop-minus-invert {p = p₃} (nf ⊕ d?⊥ T) | dual-all-irrelevant f₁ f₂ |  nt-unique NS₁ NS₂ | np′-unique NP₁ NP₂
  = <:ₜ-msg (<<:ₚ′-refl NP₂) (<:ₜ-refl NS₂)
complete-algₜ {n = suc n} {p = ⊝} (<:-minus-msg {p₂ = p₃} {T = T} refl) {f₁ = f₁} {f₂} {N₁ = N-Msg p₁ NP₁ NS₁} {N-Msg p₂ NP₂ NS₂} sz≤
  rewrite invert-involution {p₃} | t-loop-minus {p = p₃} (nf ⊕ d?⊥ T) | dual-all-irrelevant f₁ f₂ |  nt-unique NS₁ NS₂ | np′-unique NP₁ NP₂
  = <:ₜ-msg (<<:ₚ′-refl NP₂) (<:ₜ-refl NS₂)



subty⇒conv : {T₁ T₂ : Ty Δ K} → T₁ <: T₂ → T₂ <: T₁ → T₁ ≡c T₂
subty⇒conv {K = KV x x₁}{T₁ = T₁}{T₂ = T₂} T₁<:T₂ T₂<:T₁
  using N₁ ← nf-normal-type ⊕ d?⊥ T₁
  using N₂ ← nf-normal-type ⊕ d?⊥ T₂
  using N₁<:N₂ ← complete-algₜ {n = sizeₜ N₁ ⊔ sizeₜ N₂} T₁<:T₂ {N₁ = N₁} {N₂ = N₂} ≤-refl
  using N₂<:N₁ ← complete-algₜ {n = sizeₜ N₂ ⊔ sizeₜ N₁} T₂<:T₁ {N₁ = N₂} {N₂ = N₁} ≤-refl
  using nfT₁≡nfT₂ ← <:ₜ-pre-antisym N₁<:N₂ N₂<:N₁
  = ≡c-trns (≡c-trns (≡c-symm (nf-sound+ T₁)) (≡c-refl-eq nfT₁≡nfT₂)) (nf-sound+ T₂)

subty⇒conv {K = KP} {T₁} {T₂} T₁<:T₂ T₂<:T₁
  using N₁ ← nf-normal-proto T₁
  using N₂ ← nf-normal-proto T₂
  using N₁<:N₂ ← complete-algₚ {n = sizeₚ N₁ ⊔ sizeₚ N₂} T₁<:T₂ {N₁ = N₁} {N₂ = N₂} ≤-refl
  using N₂<:N₁ ← complete-algₚ {n = sizeₚ N₂ ⊔ sizeₚ N₁} T₂<:T₁ {N₁ = N₂} {N₂ = N₁} ≤-refl
  using nfT₁≡nfT₂ ← <:ₚ-pre-antisym N₁<:N₂ N₂<:N₁
  = ≡c-trns (≡c-trns (≡c-symm (nf-sound+ T₁)) (≡c-refl-eq nfT₁≡nfT₂)) (nf-sound+ T₂)

