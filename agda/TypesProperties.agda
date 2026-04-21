module TypesProperties where

open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Fin.Subset as Subset using (Subset)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Kinds
open import Kits
open import Duality
open import Types

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (_⋯_; ⋯-id)

InjectiveRenaming : ∀ {Δ₁ Δ₂} → (Δ₁ →ᵣ Δ₂) → Set
InjectiveRenaming {Δ₁} ρ =
  ∀ {K} {a b : Δ₁ ∋ K} → ρ K a ≡ ρ K b → a ≡ b

there-injective :
  ∀ {A : Set} {P : A → Set} {x xs} {a b : Any P xs}
  → there {x = x} a ≡ there b
  → a ≡ b
there-injective refl = refl

arrow-injective :
  ∀ {Δ m} {t t′ u u′ : Ty Δ TLin}
  → T-Arrow {m = m} t u ≡ T-Arrow t′ u′
  → (t ≡ t′) × (u ≡ u′)
arrow-injective refl = refl , refl

pair-injective :
  ∀ {Δ m pk₁ pk₂ pk₁′ pk₂′}
    {t : Ty Δ (KV pk₁ m)} {u : Ty Δ (KV pk₂ m)}
    {t′ : Ty Δ (KV pk₁′ m)} {u′ : Ty Δ (KV pk₂′ m)}
  → T-Pair t u ≡ T-Pair t′ u′
  → Σ (pk₁ ≡ pk₁′) λ where
      refl → Σ (pk₂ ≡ pk₂′) λ where
        refl → (t ≡ t′) × (u ≡ u′)
pair-injective refl = refl , refl , refl , refl

poly-injective :
  ∀ {Δ K K′ m} {t : Ty (K ∷ Δ) (KV KT m)} {t′ : Ty (K′ ∷ Δ) (KV KT m)}
  → T-Poly K t ≡ T-Poly K′ t′
  → Σ (K ≡ K′) λ where
      refl → t ≡ t′
poly-injective refl = refl , refl

sub-injective :
  ∀ {Δ pk pk₁ pk′ m m₁ m′}
    {km≤ : KV pk m ≤k KV pk′ m′} {km≤′ : KV pk₁ m₁ ≤k KV pk′ m′}
    {t : Ty Δ (KV pk m)} {t′ : Ty Δ (KV pk₁ m₁)}
  → T-Sub km≤ t ≡ T-Sub km≤′ t′
  → Σ (pk ≡ pk₁) λ where
      refl → Σ (m ≡ m₁) λ where
        refl → Σ (km≤ ≡ km≤′) λ where
          refl → t ≡ t′
sub-injective refl = refl , refl , refl , refl

dual-injective :
  ∀ {Δ K} {d d′ : Dualizable K} {t t′ : Ty Δ K}
  → T-Dual d t ≡ T-Dual d′ t′
  → (d ≡ d′) × (t ≡ t′)
dual-injective refl = refl , refl

msg-injective :
  ∀ {Δ} {p p′ : Polarity} {t t′ : Ty Δ KP} {u u′ : Ty Δ SLin}
  → T-Msg p t u ≡ T-Msg p′ t′ u′
  → (p ≡ p′) × (t ≡ t′) × (u ≡ u′)
msg-injective refl = refl , refl , refl

up-injective :
  ∀ {Δ pk pk′ m m′} {t : Ty Δ (KV pk m)} {t′ : Ty Δ (KV pk′ m′)}
  → T-Up t ≡ T-Up t′
  → Σ (pk ≡ pk′) λ where
      refl → Σ (m ≡ m′) λ where
        refl → t ≡ t′
up-injective refl = refl , refl , refl

minus-injective :
  ∀ {Δ} {t t′ : Ty Δ KP}
  → T-Minus t ≡ T-Minus t′
  → t ≡ t′
minus-injective refl = refl

protoD-injective :
  ∀ {Δ} {t t′ : Ty Δ TLin}
  → T-ProtoD t ≡ T-ProtoD t′
  → t ≡ t′
protoD-injective refl = refl

protoP-injective :
  ∀ {Δ k k′} {c : Subset k} {c′ : Subset k′} {v v′ : Variance} {t t′ : Ty Δ KP}
  → T-ProtoP c v t ≡ T-ProtoP c′ v′ t′
  → Σ (k ≡ k′) λ where
      refl → Σ (c ≡ c′) λ where
        refl → Σ (v ≡ v′) λ where
          refl → t ≡ t′
protoP-injective refl = refl , refl , refl , refl

injective-↑ᵣ :
  ∀ {Δ₁ Δ₂ K′} {ρ : Δ₁ →ᵣ Δ₂}
  → InjectiveRenaming ρ
  → InjectiveRenaming (ρ ↑ᵣ K′)
injective-↑ᵣ inj {a = here refl} {b = here refl} refl = refl
injective-↑ᵣ inj {a = here refl} {b = there b} ()
injective-↑ᵣ inj {a = there a} {b = here refl} ()
injective-↑ᵣ inj {a = there a} {b = there b} eq =
  cong there (inj (there-injective eq))

renaming-injective :
  ∀ {Δ₁ Δ₂ K} {T₁ T₂ : Ty Δ₁ K} (ρ : Δ₁ →ᵣ Δ₂)
  → InjectiveRenaming ρ
  → T₁ ⋯ ρ ≡ T₂ ⋯ ρ
  → T₁ ≡ T₂
renaming-injective {T₁ = T-Var x} {T₂ = T-Var y} ρ inj eq =
  cong T-Var (inj (t-var-injective eq))
renaming-injective {T₁ = T-Base} {T₂ = T-Base} ρ inj eq = refl
renaming-injective {T₁ = T-Arrow t u} {T₂ = T-Arrow t₁ u₁} ρ inj eq
  with arrow-injective eq
... | eq₁ , eq₂
  = cong₂ T-Arrow
      (renaming-injective ρ inj eq₁)
      (renaming-injective ρ inj eq₂)
renaming-injective {T₁ = T-Pair t u} {T₂ = T-Pair t₁ u₁} ρ inj eq
  with pair-injective eq
... | refl , refl , eq₁ , eq₂
  = cong₂ T-Pair
      (renaming-injective ρ inj eq₁)
      (renaming-injective ρ inj eq₂)
renaming-injective {T₁ = T-Poly K t} {T₂ = T-Poly K₁ t₁} ρ inj eq
  with poly-injective eq
... | refl , eq′
  = cong (T-Poly K) (renaming-injective (ρ ↑ᵣ _) (injective-↑ᵣ inj) eq′)
renaming-injective {T₁ = T-Sub x t} {T₂ = T-Sub x₁ t₁} ρ inj eq
  with sub-injective eq
... | refl , refl , refl , eq′
  = cong (T-Sub x) (renaming-injective ρ inj eq′)
renaming-injective {T₁ = T-Dual x t} {T₂ = T-Dual x₁ t₁} ρ inj eq
  with dual-injective eq
... | refl , eq′
  = cong (T-Dual x) (renaming-injective ρ inj eq′)
renaming-injective {T₁ = T-End} {T₂ = T-End} ρ inj eq = refl
renaming-injective {T₁ = T-Msg x t u} {T₂ = T-Msg x₁ t₁ u₁} ρ inj eq
  with msg-injective eq
... | refl , eq₁ , eq₂
  = cong₂ (T-Msg x)
      (renaming-injective ρ inj eq₁)
      (renaming-injective ρ inj eq₂)
renaming-injective {T₁ = T-Up t} {T₂ = T-Up t₁} ρ inj eq
  with up-injective eq
... | refl , refl , eq′
  = cong T-Up (renaming-injective ρ inj eq′)
renaming-injective {T₁ = T-Minus t} {T₂ = T-Minus t₁} ρ inj eq
  with minus-injective eq
... | eq′
  = cong T-Minus (renaming-injective ρ inj eq′)
renaming-injective {T₁ = T-ProtoD t} {T₂ = T-ProtoD t₁} ρ inj eq
  with protoD-injective eq
... | eq′
  = cong T-ProtoD (renaming-injective ρ inj eq′)
renaming-injective {T₁ = T-ProtoP x v t} {T₂ = T-ProtoP x₁ v₁ t₁} ρ inj eq
  with protoP-injective eq
... | refl , refl , refl , eq′
  = cong (T-ProtoP x v) (renaming-injective ρ inj eq′)

weakenᵣ-injective :
  ∀ {Δ K′} → InjectiveRenaming (weakenᵣ {S = Δ} K′)
weakenᵣ-injective refl = refl
