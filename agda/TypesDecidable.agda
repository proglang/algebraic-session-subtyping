module TypesDecidable where

open import Data.Empty using (⊥-elim)
open import Data.Bool renaming (_≟_ to _≟b_)
open import Data.Fin using (Fin)
open import Data.Fin.Subset as Subset using ()
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≟_)
open import Data.Vec using (Vec)
open import Data.Vec.Properties using (≡-dec)
open import Data.List
open import Data.Product
open import Data.Sum
open import Relation.Nullary using (¬_; Dec; yes; no; map′)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; inspect; Reveal_·_is_)
open import Function using (const; case_of_; _$_)

open import Util
open import Kinds
open import Duality
open import Kits
open import Types

polarity-equal : (p₁ p₂ : Polarity) → Dec (p₁ ≡ p₂)
polarity-equal ⊕ ⊕ = yes refl
polarity-equal ⊕ ⊝ = no λ()
polarity-equal ⊝ ⊕ = no λ()
polarity-equal ⊝ ⊝ = yes refl

polarity-equal′ : (p : Polarity) → polarity-equal p p ≡ yes refl
polarity-equal′ ⊕ = refl
polarity-equal′ ⊝ = refl

⊙-equal : (v₁ v₂ : Variance) → Dec (v₁ ≡ v₂)
⊙-equal ⊕ ⊕ = yes refl
⊙-equal ⊕ ⊝ = no λ()
⊙-equal ⊕ ⊘ = no λ()
⊙-equal ⊝ ⊕ = no λ()
⊙-equal ⊝ ⊝ = yes refl
⊙-equal ⊝ ⊘ = no λ()
⊙-equal ⊘ ⊕ = no λ()
⊙-equal ⊘ ⊝ = no λ()
⊙-equal ⊘ ⊘ = yes refl

subset-equal : (M₁ M₂ : Subset.Subset k) → Dec (M₁ ≡ M₂)
subset-equal M₁ M₂ = ≡-dec _≟b_ M₁ M₂

var-equal : (x₁ x₂ : K ∈ Δ) → Dec (x₁ ≡ x₂)
var-equal (here refl) (here refl) = yes refl
var-equal (here refl) (there x₂) = no λ()
var-equal (there x₁) (here px) = no λ()
var-equal (there x₁) (there x₂) = map′ (cong there) (λ{ refl → refl}) (var-equal x₁ x₂)

var-equal′ : (x : K ∈ Δ) → var-equal x x ≡ yes refl
var-equal′ (here refl) = refl
var-equal′ (there x) rewrite var-equal′ x = refl

ty-equal : (T₁ T₂ : Ty Δ K) → Dec (T₁ ≡ T₂)
ty-equal (T-Var x) (T-Var x₁) = map′ (cong T-Var) (λ{refl → refl}) (var-equal x x₁)
ty-equal (T-Var x) T-Base = no λ()
ty-equal (T-Var x) (T-Arrow x₁ T₂ T₃) = no λ()
ty-equal (T-Var x) (T-Pair T₂ T₃) = no λ()
ty-equal (T-Var x) (T-Poly T₂) = no λ()
ty-equal (T-Var x) (T-Sub x₁ T₂) = no λ()
ty-equal (T-Var x) (T-Dual x₁ T₂) = no λ()
ty-equal (T-Var x) T-End = no λ()
ty-equal (T-Var x) (T-Msg x₁ T₂ T₃) = no λ()
ty-equal (T-Var x) (T-Up T₂) = no λ()
ty-equal (T-Var x) (T-Minus T₂) = no λ()
ty-equal (T-Var x) (T-ProtoD T₂) = no λ()
ty-equal (T-Var x) (T-ProtoP x₁ x₂ T₂) = no λ()
ty-equal T-Base (T-Var x) = no λ()
ty-equal T-Base T-Base = yes refl
ty-equal T-Base (T-Arrow x T₂ T₃) = no λ()
ty-equal T-Base (T-Sub x T₂) = no λ()
ty-equal (T-Arrow x T₁ T₂) (T-Var x₁) = no λ()
ty-equal (T-Arrow x T₁ T₂) T-Base = no λ()
ty-equal (T-Arrow {pk = pk} ≤pk₁ T₁ T₂) (T-Arrow ≤pk₂ T₃ T₄)
  rewrite ≤p-irrelevant ≤pk₁ ≤pk₂
  with ty-equal T₁ T₃
... | no T₁≢T₃ = no (λ{ refl → T₁≢T₃ refl})
... | yes refl
  with ty-equal T₂ T₄
... | no T₂≢T₄ = no (λ{ refl → T₂≢T₄ refl})
... | yes refl = yes refl
ty-equal (T-Arrow x T₁ T₂) (T-Pair T₃ T₄) = no λ()
ty-equal (T-Arrow x T₁ T₂) (T-Poly T₃) = no λ()
ty-equal (T-Arrow x T₁ T₂) (T-Sub x₁ T₃) = no λ()
ty-equal (T-Arrow x T₁ T₂) (T-Dual x₁ T₃) = no λ()
ty-equal (T-Arrow x T₁ T₂) T-End = no λ()
ty-equal (T-Arrow x T₁ T₂) (T-Msg x₁ T₃ T₄) = no λ()
ty-equal (T-Arrow x T₁ T₂) (T-ProtoD T₃) = no λ()
ty-equal (T-Pair T₁ T₂) (T-Var x) = no λ()
ty-equal (T-Pair T₁ T₂) (T-Arrow x T₃ T₄) = no λ()
ty-equal (T-Pair {pk₁ = pk₁} {pk₂ = pk₂} T₁ T₂) (T-Pair {pk₁ = pk₃} {pk₂ = pk₄} T₃ T₄)
  with eq-prekind pk₁ pk₃
... | no pk₁≢pk₃ = no (λ{ refl → pk₁≢pk₃ refl })
... | yes refl
  with eq-prekind pk₂ pk₄
... | no pk₂≢pk₄ = no (λ{ refl → pk₂≢pk₄ refl })
... | yes refl
  with ty-equal T₁ T₃
... | no T₁≢T₃ = no (λ{ refl → T₁≢T₃ refl})
... | yes refl
  with ty-equal T₂ T₄
... | no T₂≢T₄ = no (λ{ refl → T₂≢T₄ refl})
... | yes refl = yes refl
ty-equal (T-Pair T₁ T₂) (T-Poly T₃) = no λ()
ty-equal (T-Pair T₁ T₂) (T-Sub x T₃) = no λ()
ty-equal (T-Pair T₁ T₂) (T-Dual x T₃) = no λ()
ty-equal (T-Pair T₁ T₂) (T-ProtoD T₃) = no λ()
ty-equal (T-Poly T₁) (T-Var x) = no λ()
ty-equal (T-Poly T₁) (T-Pair T₂ T₃) = no λ()
ty-equal (T-Poly T₁) (T-Arrow x T₂ T₃) = no λ()
ty-equal (T-Poly {K′ = K₁} T₁) (T-Poly {K′ = K₂} T₂)
  with eq-kind K₁ K₂
... | no K₁≢K₂ = no (λ{refl → K₁≢K₂ refl})
... | yes refl = map′ (cong T-Poly) (λ{refl → refl}) (ty-equal T₁ T₂)
ty-equal (T-Poly T₁) (T-Sub x T₂) = no λ()
ty-equal (T-Poly T₁) (T-ProtoD T₂) = no λ()
ty-equal (T-Sub x T₁) (T-Var x₁) = no λ()
ty-equal (T-Sub x T₁) T-Base = no λ()
ty-equal (T-Sub x T₁) (T-Arrow x₁ T₂ T₃) = no λ()
ty-equal (T-Sub x T₁) (T-Pair T₂ T₃) = no λ()
ty-equal (T-Sub x T₁) (T-Poly T₂) = no λ()
ty-equal (T-Sub {pk = pk₁}{m = m₁} ≤k₁ T₁) (T-Sub {pk = pk₂}{m = m₂} ≤k₂ T₂)
  with eq-prekind pk₁ pk₂
... | no pk₁≢pk₂ = no (λ{ refl → pk₁≢pk₂ refl })
... | yes refl
  with eq-multiplicity m₁ m₂
... | no m₁≢m₂ = no (λ{ refl → m₁≢m₂ refl })
... | yes refl
  rewrite ≤k-irrelevant ≤k₁ ≤k₂ = map′ (cong (T-Sub ≤k₂)) (λ{ refl → refl}) (ty-equal T₁ T₂)
ty-equal (T-Sub x T₁) (T-Dual x₁ T₂) = no λ()
ty-equal (T-Sub x T₁) T-End = no λ()
ty-equal (T-Sub x T₁) (T-Msg x₁ T₂ T₃) = no λ()
ty-equal (T-Sub x T₁) (T-ProtoD T₂) = no λ()
ty-equal (T-Dual x T₁) (T-Var x₁) = no λ()
ty-equal (T-Dual x T₁) (T-Arrow x₁ T₂ T₃) = no λ()
ty-equal (T-Dual x T₁) (T-Sub x₁ T₂) = no λ()
ty-equal (T-Dual D-S T₁) (T-Dual D-S T₂) = map′ (cong (T-Dual D-S)) (λ{ refl → refl}) (ty-equal T₁ T₂)
ty-equal (T-Dual x T₁) T-End = no λ()
ty-equal (T-Dual x T₁) (T-Msg x₁ T₂ T₃) = no λ()
ty-equal T-End (T-Var x) = no λ()
ty-equal T-End (T-Arrow x T₂ T₃) = no λ()
ty-equal T-End (T-Sub x T₂) = no λ()
ty-equal T-End (T-Dual x T₂) = no λ()
ty-equal T-End T-End = yes refl
ty-equal (T-Msg x T₁ T₂) (T-Var x₁) = no λ()
ty-equal (T-Msg x T₁ T₂) (T-Arrow x₁ T₃ T₄) = no λ()
ty-equal (T-Msg x T₁ T₂) (T-Sub x₁ T₃) = no λ()
ty-equal (T-Msg x T₁ T₂) (T-Dual x₁ T₃) = no λ()
ty-equal (T-Msg p₁ T₁ S₁) (T-Msg p₂ T₂ S₂)
  with polarity-equal p₁ p₂
... | no p₁≢p₂ = no (λ{ refl → p₁≢p₂ refl })
... | yes refl
  with ty-equal T₁ T₂
... | no T₁≢T₂ = no (λ{ refl → T₁≢T₂ refl })
... | yes refl = map′ (cong (T-Msg p₁ T₁)) (λ{ refl → refl }) (ty-equal S₁ S₂)
ty-equal (T-Up T₁) (T-Var x) = no λ()
ty-equal (T-Up {pk₁}{m₁} T₁) (T-Up {pk₂}{m₂} T₂)
  with eq-prekind pk₁ pk₂
... | no pk₁≢pk₂ = no (λ{ refl → pk₁≢pk₂ refl })
... | yes refl
  with eq-multiplicity m₁ m₂
... | no m₁≢m₂ = no (λ{ refl → m₁≢m₂ refl })
... | yes refl = map′ (cong T-Up) (λ{ refl → refl }) (ty-equal T₁ T₂)
ty-equal (T-Up T₁) (T-Minus T₂) = no λ()
ty-equal (T-Up T₁) (T-ProtoP x x₁ T₂) = no λ()
ty-equal (T-Minus T₁) (T-Var x) = no λ()
ty-equal (T-Minus T₁) (T-Up T₂) = no λ()
ty-equal (T-Minus T₁) (T-Minus T₂) = map′ (cong T-Minus) (λ{refl → refl}) (ty-equal T₁ T₂)
ty-equal (T-Minus T₁) (T-ProtoP x x₁ T₂) = no λ()
ty-equal (T-ProtoD T₁) (T-Var x) = no λ()
ty-equal (T-ProtoD T₁) (T-Arrow x T₂ T₃) = no λ()
ty-equal (T-ProtoD T₁) (T-Pair T₂ T₃) = no λ()
ty-equal (T-ProtoD T₁) (T-Poly T₂) = no λ()
ty-equal (T-ProtoD T₁) (T-Sub x T₂) = no λ()
ty-equal (T-ProtoD T₁) (T-ProtoD T₂) = map′ (cong T-ProtoD) (λ{refl → refl}) (ty-equal T₁ T₂)
ty-equal (T-ProtoP x x₁ T₁) (T-Var x₂) = no λ()
ty-equal (T-ProtoP x x₁ T₁) (T-Up T₂) = no λ()
ty-equal (T-ProtoP x x₁ T₁) (T-Minus T₂) = no λ()
ty-equal (T-ProtoP {k = k₁} #c₁ ⊙₁ T₁) (T-ProtoP {k = k₂} #c₂ ⊙₂ T₂)
  with k₁ ≟ k₂
... | no k₁≢k₂ = no (λ{ refl → k₁≢k₂ refl})
... | yes refl
  with subset-equal #c₁ #c₂
... | no #c₁≢#c₂ = no (λ{ refl → #c₁≢#c₂ refl})
... | yes refl
  with ⊙-equal ⊙₁ ⊙₂
... | no ⊙₁≢⊙₂ = no (λ{ refl → ⊙₁≢⊙₂ refl })
... | yes refl = map′ (cong (T-ProtoP #c₁ ⊙₁)) (λ{refl → refl}) (ty-equal T₁ T₂)

infer-equiv : (T₁ T₂ : Ty Δ K) → Dec (T₁ ≡c T₂)
infer-equiv T₁ T₂
  using N₁ ← nf ⊕ d?⊥ T₁
  using N₂ ← nf ⊕ d?⊥ T₂
  with ty-equal N₁ N₂
... | yes N₁≡N₂ = yes (≡c-trns (≡c-trns (≡c-symm (nf-sound+ T₁)) (≡c-refl-eq N₁≡N₂)) (nf-sound+ T₂))
... | no N₁≢N₂ = no (λ T₁≡cT₂ → N₁≢N₂ (nf-complete d?⊥ d?⊥ T₁≡cT₂))
