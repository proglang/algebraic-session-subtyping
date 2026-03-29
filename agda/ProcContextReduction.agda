module ProcContextReduction where

open import Data.Fin using (Fin)
open import Data.List using ([])
open import Data.Nat using (suc; _+_)

open import ExprSemantics using (Label)
open import ExprNormalTyping
open import ExprContextReduction using (_—ctx[_]→_)
open import ProcSemantics using (ProcLabel; Side; P-Expr; P-τ; P-ParAct; P-Open)

-- Process-context reduction extends expression-context reduction.
-- Expression labels are inherited explicitly through `P-Expr`.
-- The genuinely process-specific labels are exposed as separate interfaces.

infix 4 _—procctx[_]→_

data _—procctx[_]→_ : ∀ {n k} → Ctx [] n → ProcLabel n k → Ctx [] (k + n) → Set where
  PCtx-Expr : ∀ {n k} {Γ₀ : Ctx [] n} {Γ₁ : Ctx [] (k + n)} {ℓ : Label n k}
    → Γ₀ —ctx[ ℓ ]→ Γ₁
    → Γ₀ —procctx[ P-Expr ℓ ]→ Γ₁

  PCtx-τ : ∀ {n} {Γ : Ctx [] n}
    → Γ —procctx[ P-τ ]→ Γ

postulate
  PCtx-ParAct : ∀ {n k} {Γ₀ : Ctx [] n} {Γ₁ : Ctx [] (k + n)} {π₁ π₂ : ProcLabel n k}
    → Γ₀ —procctx[ π₁ ]→ Γ₁
    → Γ₀ —procctx[ π₂ ]→ Γ₁
    → Γ₀ —procctx[ P-ParAct π₁ π₂ ]→ Γ₁

  PCtx-Open : ∀ {n} {Γ₀ : Ctx [] n} {Γ₁ : Ctx [] (suc (suc n))} {sd : Side} {x : Fin n}
    → Γ₀ —procctx[ P-Open sd x ]→ Γ₁
