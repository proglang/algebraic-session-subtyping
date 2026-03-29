module ProcSemantics where

open import Data.Fin using (Fin) renaming (suc to fsuc)
open import Data.List using ([])
open import Data.Nat using (ℕ; _+_) renaming (zero to zeroℕ; suc to sucℕ)

open import ExprSyntax using
  ( Const
  ; C-Unit
  ; Expr
  ; Process
  ; Value
  ; E-App
  ; E-Val
  ; P-Exp
  ; P-Par
  ; P-New
  ; V-Const
  )
open import ExprSemantics using
  ( Label
  ; L-β
  ; L-Fork
  ; L-New
  ; L-RecvVal
  ; L-RecvLab
  ; L-SendVal
  ; L-SendLab
  ; L-Close
  ; _—[_]→_
  )
open import ExprSubstitution using (renameExpr; renameValue; extRen2)
open import Kinds using (SLin)
open import Types using (Ty)

-- The process LTS mirrors Fig. 7. We keep the externally visible session
-- actions explicit and use a few helper predicates for the restriction/open
-- rules, where the paper is name-based and the Agda syntax uses de Bruijn
-- indices.

data Side : Set where
  left right : Side

shiftRen : ∀ (k : ℕ) {n} → Fin n → Fin (k + n)
shiftRen zeroℕ x = x
shiftRen (sucℕ k) x = fsuc (shiftRen k x)

renameProcess : ∀ {n m} → (Fin n → Fin m) → Process [] n → Process [] m
renameProcess ρ (P-Exp e) = P-Exp (renameExpr ρ e)
renameProcess ρ (P-Par p q) = P-Par (renameProcess ρ p) (renameProcess ρ q)
renameProcess ρ (P-New p) = P-New (renameProcess (extRen2 ρ) p)

weakenValueBy : ∀ (k : ℕ) {n} → Value [] n → Value [] (k + n)
weakenValueBy k = renameValue (shiftRen k)

weakenExprBy : ∀ (k : ℕ) {n} → Expr [] n → Expr [] (k + n)
weakenExprBy k = renameExpr (shiftRen k)

weakenProcessBy : ∀ (k : ℕ) {n} → Process [] n → Process [] (k + n)
weakenProcessBy k = renameProcess (shiftRen k)

data ProcLabel : ℕ → ℕ → Set where
  P-Expr    : ∀ {n k} → Label n k → ProcLabel n k
  P-τ       : ∀ {n} → ProcLabel n 0
  P-ParAct  : ∀ {n k} → ProcLabel n k → ProcLabel n k → ProcLabel n k
  P-Open    : ∀ {n} → Side → Fin n → ProcLabel n 2

-- These helpers isolate the binder-sensitive parts of Fig. 7:
-- weakening a visible label under a fresh pair,
-- recognizing the internal communication patterns on the fresh pair, and
-- eliminating a closed restricted pair from the target process.

postulate
  wkProcLabel₂ : ∀ {n k} → ProcLabel n k → ProcLabel (sucℕ (sucℕ n)) k
  wkProcTarget₂ : ∀ {n k} → Process [] (k + sucℕ (sucℕ n)) → Process [] (sucℕ (sucℕ (k + n)))
  closeProcTarget₂ : ∀ {n} → Process [] (4 + sucℕ (sucℕ n)) → Process [] (sucℕ (sucℕ (sucℕ (sucℕ n))))

  MsgOnFreshPair : ∀ {n} → ProcLabel (sucℕ (sucℕ n)) 0 → Set
  BraOnFreshPair : ∀ {n} → ProcLabel (sucℕ (sucℕ n)) 0 → Set
  CloseOnFreshPair : ∀ {n} → ProcLabel (sucℕ (sucℕ n)) 0 → Set

  OpensLeft : ∀ {n k} → ProcLabel (sucℕ (sucℕ n)) k → Fin n → Set
  OpensRight : ∀ {n k} → ProcLabel (sucℕ (sucℕ n)) k → Fin n → Set
  ClosesLeft : ∀ {n} → ProcLabel (sucℕ (sucℕ n)) 4 → Set
  ClosesRight : ∀ {n} → ProcLabel (sucℕ (sucℕ n)) 4 → Set

  contractClosed : ∀ {n} → Process [] (sucℕ (sucℕ n)) → Process [] n

infix 4 _—proc[_]→_

data _—proc[_]→_ : ∀ {n k} → Process [] n → ProcLabel n k → Process [] (k + n) → Set where
  Act-SessionRecvVal : ∀ {n} {e₁ e₂ : Expr [] n} {x : Fin n} {v : Value [] n} →
      e₁ —[ L-RecvVal x v ]→ e₂
      → P-Exp e₁ —proc[ P-Expr (L-RecvVal x v) ]→ P-Exp e₂

  Act-SessionRecvLab : ∀ {n k} {e₁ e₂ : Expr [] n} {x : Fin n} {i : Fin k} →
      e₁ —[ L-RecvLab x i ]→ e₂
      → P-Exp e₁ —proc[ P-Expr (L-RecvLab x i) ]→ P-Exp e₂

  Act-SessionSendVal : ∀ {n} {e₁ e₂ : Expr [] n} {x : Fin n} {v : Value [] n} →
      e₁ —[ L-SendVal x v ]→ e₂
      → P-Exp e₁ —proc[ P-Expr (L-SendVal x v) ]→ P-Exp e₂

  Act-SessionSendLab : ∀ {n k} {e₁ e₂ : Expr [] n} {x : Fin n} {i : Fin k} →
      e₁ —[ L-SendLab x i ]→ e₂
      → P-Exp e₁ —proc[ P-Expr (L-SendLab x i) ]→ P-Exp e₂

  Act-SessionClose : ∀ {n} {e₁ e₂ : Expr [] n} {x : Fin n} →
      e₁ —[ L-Close x ]→ e₂
      → P-Exp e₁ —proc[ P-Expr (L-Close x) ]→ P-Exp e₂

  Act-Beta : ∀ {n} {e₁ e₂ : Expr [] n} →
      e₁ —[ L-β ]→ e₂
      → P-Exp e₁ —proc[ P-τ ]→ P-Exp e₂

  Act-Fork : ∀ {n} {e₁ e₂ : Expr [] n} {v : Value [] n} →
      e₁ —[ L-Fork v ]→ e₂
      → P-Exp e₁ —proc[ P-τ ]→ P-Par (P-Exp e₂) (P-Exp (E-App (E-Val v) (E-Val (V-Const C-Unit))))

  Act-New : ∀ {n} {e₁ : Expr [] n} {e₂ : Expr [] (sucℕ (sucℕ n))} {S : Ty [] SLin} →
      e₁ —[ L-New S ]→ e₂
      → P-Exp e₁ —proc[ P-τ ]→ P-New (P-Exp e₂)

  Act-JoinL : ∀ {n k} {p₁ p₂ : Process [] n} {q₁ q₂ : Process [] (k + n)} {π₁ π₂ : ProcLabel n k} →
      p₁ —proc[ π₁ ]→ q₁
      → p₂ —proc[ π₂ ]→ q₂
      → P-Par p₁ p₂ —proc[ P-ParAct π₁ π₂ ]→ P-Par q₁ q₂

  Act-JoinR : ∀ {n k} {p₁ p₂ : Process [] n} {q₁ q₂ : Process [] (k + n)} {π₁ π₂ : ProcLabel n k} →
      p₁ —proc[ π₁ ]→ q₁
      → p₂ —proc[ π₂ ]→ q₂
      → P-Par p₁ p₂ —proc[ P-ParAct π₂ π₁ ]→ P-Par q₁ q₂

  Act-Msg : ∀ {n} {p₁ p₂ : Process [] (sucℕ (sucℕ n))} {π : ProcLabel (sucℕ (sucℕ n)) 0} →
      p₁ —proc[ π ]→ p₂
      → MsgOnFreshPair π
      → P-New p₁ —proc[ P-τ ]→ P-New p₂

  Act-Bra : ∀ {n} {p₁ p₂ : Process [] (sucℕ (sucℕ n))} {π : ProcLabel (sucℕ (sucℕ n)) 0} →
      p₁ —proc[ π ]→ p₂
      → BraOnFreshPair π
      → P-New p₁ —proc[ P-τ ]→ P-New p₂

  Act-Wait : ∀ {n} {p₁ p₂ : Process [] (sucℕ (sucℕ n))} {π : ProcLabel (sucℕ (sucℕ n)) 0} →
      p₁ —proc[ π ]→ p₂
      → CloseOnFreshPair π
      → P-New p₁ —proc[ P-τ ]→ contractClosed p₂

  Act-ParL : ∀ {n k} {p₁ : Process [] n} {p₂ : Process [] (k + n)} {q : Process [] n} {π : ProcLabel n k} →
      p₁ —proc[ π ]→ p₂
      → P-Par p₁ q —proc[ π ]→ P-Par p₂ (weakenProcessBy k q)

  Act-ParR : ∀ {n k} {p : Process [] n} {q₁ : Process [] n} {q₂ : Process [] (k + n)} {π : ProcLabel n k} →
      q₁ —proc[ π ]→ q₂
      → P-Par p q₁ —proc[ π ]→ P-Par (weakenProcessBy k p) q₂

  Act-Res : ∀ {n k} {p₁ : Process [] (sucℕ (sucℕ n))} {p₂ : Process [] (k + sucℕ (sucℕ n))} {π : ProcLabel n k} →
      p₁ —proc[ wkProcLabel₂ π ]→ p₂
      → P-New p₁ —proc[ π ]→ P-New (wkProcTarget₂ p₂)

  Act-OpenL : ∀ {n} {p₁ : Process [] (sucℕ (sucℕ n))} {p₂ : Process [] (sucℕ (sucℕ n))} {π : ProcLabel (sucℕ (sucℕ n)) 0} {x : Fin n} →
      p₁ —proc[ π ]→ p₂
      → OpensLeft π x
      → P-New p₁ —proc[ P-Open left x ]→ p₂

  Act-OpenR : ∀ {n} {p₁ : Process [] (sucℕ (sucℕ n))} {p₂ : Process [] (sucℕ (sucℕ n))} {π : ProcLabel (sucℕ (sucℕ n)) 0} {x : Fin n} →
      p₁ —proc[ π ]→ p₂
      → OpensRight π x
      → P-New p₁ —proc[ P-Open right x ]→ p₂

  Act-CloseL : ∀ {n} {p₁ : Process [] (sucℕ (sucℕ n))} {p₂ : Process [] (4 + sucℕ (sucℕ n))}
      {π : ProcLabel (sucℕ (sucℕ n)) 4} →
      p₁ —proc[ π ]→ p₂
      → ClosesLeft π
      → P-New p₁ —proc[ P-τ ]→ P-New (P-New (closeProcTarget₂ p₂))

  Act-CloseR : ∀ {n} {p₁ : Process [] (sucℕ (sucℕ n))} {p₂ : Process [] (4 + sucℕ (sucℕ n))}
      {π : ProcLabel (sucℕ (sucℕ n)) 4} →
      p₁ —proc[ π ]→ p₂
      → ClosesRight π
      → P-New p₁ —proc[ P-τ ]→ P-New (P-New (closeProcTarget₂ p₂))

-- The concrete observable rules are direct encodings of Fig. 7.
-- The name-sensitive restriction rules are factored through helper predicates,
-- because the paper is phrased with named endpoints while the Agda syntax is
-- de Bruijn indexed.
