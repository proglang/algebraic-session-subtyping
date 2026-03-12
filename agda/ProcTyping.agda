module ProcTyping where

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)

open import Kinds
open import Types
open import Duality
open import ExprSyntax using (Process; Expr; P-Exp; P-Par; P-New)
open import ExprNormalTyping

-- A process thread should consume every linear resource it receives.
-- Because expression typing uses leftover contexts with `B-Used` markers,
-- process typing checks that the leftover context is entirely used.

data AllUsed {Δ} : ∀ {n} → Ctx Δ n → Set where
  AU-∅ : AllUsed ∅
  AU-▻ : ∀ {n} {Γ : Ctx Δ n}
    → AllUsed Γ
    → AllUsed (B-Used ▻ Γ)

-- Context splitting for parallel composition.
-- Linear resources are assigned to exactly one side.
-- Unrestricted resources are copied to both sides.
-- Used entries stay used on both sides.

data Split {Δ} : ∀ {n} → Ctx Δ n → Ctx Δ n → Ctx Δ n → Set where
  S-∅ : Split ∅ ∅ ∅

  S-Linˡ : ∀ {n} {Γ Γ₁ Γ₂ : Ctx Δ n} {T : NfTy Δ K}
    → Split Γ Γ₁ Γ₂
    → Split (B-Lin T ▻ Γ) (B-Lin T ▻ Γ₁) (B-Used ▻ Γ₂)

  S-Linʳ : ∀ {n} {Γ Γ₁ Γ₂ : Ctx Δ n} {T : NfTy Δ K}
    → Split Γ Γ₁ Γ₂
    → Split (B-Lin T ▻ Γ) (B-Used ▻ Γ₁) (B-Lin T ▻ Γ₂)

  S-Un : ∀ {n} {Γ Γ₁ Γ₂ : Ctx Δ n} {T : NfTy Δ K}
    → Split Γ Γ₁ Γ₂
    → Split (B-Un T ▻ Γ) (B-Un T ▻ Γ₁) (B-Un T ▻ Γ₂)

  S-Used : ∀ {n} {Γ Γ₁ Γ₂ : Ctx Δ n}
    → Split Γ Γ₁ Γ₂
    → Split (B-Used ▻ Γ) (B-Used ▻ Γ₁) (B-Used ▻ Γ₂)

-- Suggested process typing judgment.
-- It is intentionally declarative/non-algorithmic at the process level:
-- `P-Par` relies on an explicit split witness and `P-New` guesses a session type.

data _⊢proc_ {Δ} : ∀ {n} → Ctx Δ n → Process Δ n → Set where
  P-Exp : ∀ {n} {Γ Γ′ : Ctx Δ n} {e : Expr Δ n}
    → Γ ⊢ e ⇐ normalizeTy T-Base ⊣ Γ′
    → AllUsed Γ′
    → Γ ⊢proc P-Exp e

  P-Par : ∀ {n} {Γ Γ₁ Γ₂ : Ctx Δ n} {p₁ p₂ : Process Δ n}
    → Split Γ Γ₁ Γ₂
    → Γ₁ ⊢proc p₁
    → Γ₂ ⊢proc p₂
    → Γ ⊢proc P-Par p₁ p₂

  P-New : ∀ {n} {Γ : Ctx Δ n} {p : Process Δ (suc (suc n))} {S : Ty Δ SLin}
    → (normalizeTy S ∷ˡ (normalizeTy (T-Dual D-S S) ∷ˡ Γ)) ⊢proc p
    → Γ ⊢proc P-New p

-- Small helper lemmas one would likely want next.

split-refl-used : ∀ {Δ n} {Γ : Ctx Δ n}
  → AllUsed Γ
  → Split Γ Γ Γ
split-refl-used AU-∅ = S-∅
split-refl-used (AU-▻ AUΓ) = S-Used (split-refl-used AUΓ)

split-allused : ∀ {Δ n} {Γ Γ₁ Γ₂ : Ctx Δ n}
  → Split Γ Γ₁ Γ₂
  → AllUsed Γ
  → AllUsed Γ₁ × AllUsed Γ₂
split-allused S-∅ AU-∅ = AU-∅ , AU-∅
split-allused (S-Used sp) (AU-▻ AUΓ) with split-allused sp AUΓ
... | AU₁ , AU₂ = AU-▻ AU₁ , AU-▻ AU₂

-- Suggested next steps, if this direction is adopted:
-- 1. A well-formedness predicate for process contexts, if desired.
-- 2. Structural lemmas for `Split` (commutativity, associativity up to proof).
-- 3. A compatibility lemma showing that `P-Exp` can be phrased using only
--    expression synthesis when the thread body is already known to synthesize `unit`.
