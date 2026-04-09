module ExprSemantics where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _+_) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Product using (_,_)

open import Kinds
open import Types
open import ExprSyntax
open import ExprSubstitution using (substExpr; substExpr₂; substValue; substTyValue; renameExpr; renameValue; extRen; extRen2)

-- The paper distinguishes several observable labels.
-- In the current syntax `wait` and `terminate` were merged into `C-Close`,
-- so we expose a single close-style label here.

data Label : ℕ → ℕ → Set where
  L-β       : Label n 0
  L-Fork    : Value [] n → Label n 0
  L-New     : Ty [] SLin → Label n 2
  L-RecvVal : Fin n → Value [] n → Label n 0
  L-RecvLab : ∀ {k} → Fin n → Fin k → Label n 0
  L-SendVal : Fin n → Value [] n → Label n 0
  L-SendLab : ∀ {k} → Fin n → Fin k → Label n 0
  L-Close   : Fin n → Label n 0

freshPair : Expr Δ (sucℕ (sucℕ n))
freshPair = E-Val (V-Pair (V-Var fzero) (V-Var (fsuc fzero)))

infix 4 _—[_]→_

shiftRen : ∀ (k : ℕ) {n} → Fin n → Fin (k + n)
shiftRen zeroℕ x = x
shiftRen (sucℕ k) x = fsuc (shiftRen k x)

weakenValueBy : ∀ (k : ℕ) {n} → Value [] n → Value [] (k + n)
weakenValueBy k = renameValue (shiftRen k)

weakenExprBy : ∀ (k : ℕ) {n} → Expr [] n → Expr [] (k + n)
weakenExprBy k = renameExpr (shiftRen k)

weakenExprBy1 : ∀ (k : ℕ) {n} → Expr [] (sucℕ n) → Expr [] (sucℕ (k + n))
weakenExprBy1 k = renameExpr (extRen (shiftRen k))

weakenExprBy2 : ∀ (k : ℕ) {n} → Expr [] (sucℕ (sucℕ n)) → Expr [] (sucℕ (sucℕ (k + n)))
weakenExprBy2 k = renameExpr (extRen2 (shiftRen k))

data _—[_]→_ : ∀ {n k} → Expr [] n → Label n k → Expr [] (k + n) → Set where
  Act-App : ∀ {n} {T : Ty [] TLin} {e : Expr [] (sucℕ n)} {v : Value [] n} →
      E-App (E-Val (V-Abs T e)) (E-Val v)
        —[ L-β ]→
      substExpr e v

  Act-TApp : ∀ {n K} {T : Ty [] K} {v : Value (K ∷ []) n} →
      E-TApp (E-Val (V-TAbs K v)) T
        —[ L-β ]→
      E-Val (substTyValue v T)

  Act-LetPair : ∀ {n} {u v : Value [] n} {e : Expr [] (sucℕ (sucℕ n))} →
      E-LetPair (E-Val (V-Pair u v)) e
        —[ L-β ]→
      substExpr₂ e u v

  Act-LetUnit : ∀ {n} {e : Expr [] n} →
      E-LetUnit (E-Val (V-Const C-Unit)) e
        —[ L-β ]→
      e

  Act-PairV : ∀ {n} {u v : Value [] n} →
      E-Pair (E-Val u) (E-Val v)
        —[ L-β ]→
      E-Val (V-Pair u v)

  Act-Rec : ∀ {n} {T U : Ty [] TLin} {v : Value [] (sucℕ n)} {u : Expr [] n} →
      E-App (E-Val (V-Rec T U v)) u
        —[ L-β ]→
      E-App (E-Val (substValue v (V-Rec T U v))) u

  Act-Fork : ∀ {n} {v : Value [] n} →
      E-App (E-Val (V-Const C-Fork)) (E-Val v)
        —[ L-Fork v ]→
      E-Val (V-Const C-Unit)

  Act-New : ∀ {n} {S : Ty [] SLin} →
      E-TApp (E-Val (V-Const C-New)) S
        —[ L-New S ]→
      (freshPair {n = n})

  Act-Receive₁ : ∀ {n} {T : Ty [] TLin} →
      E-TApp {K = TLin} (E-Val (V-Const {n = n} C-Receive)) T
        —[ L-β ]→
      E-Val (V-Receive₁ {n = n} T)

  Act-Receive₂ : ∀ {n} {T : Ty [] TLin} {S : Ty [] SLin} →
      E-TApp {K = SLin} (E-Val (V-Receive₁ {n = n} T)) S
        —[ L-β ]→
      E-Val (V-Receive₂ {n = n} T S)

  Act-Rcv : ∀ {n} {T : Ty [] TLin} {S : Ty [] SLin} {x : Fin n} {v : Value [] n} →
      E-App (E-Val (V-Receive₂ T S)) (E-Val (V-Var x))
        —[ L-RecvVal x v ]→
      E-Val (V-Pair v (V-Var x))

  Act-Send₁ : ∀ {n} {T : Ty [] TLin} →
      E-TApp {K = TLin} (E-Val (V-Const {n = n} C-Send)) T
        —[ L-β ]→
      E-Val (V-Send₁ {n = n} T)

  Act-Send₂ : ∀ {n} {T : Ty [] TLin} {S : Ty [] SLin} →
      E-TApp {K = SLin} (E-Val (V-Send₁ {n = n} T)) S
        —[ L-β ]→
      E-Val (V-Send₂ {n = n} T S)

  Act-Send₃ : ∀ {n} {T : Ty [] TLin} {S : Ty [] SLin} {v : Value [] n} →
      E-App (E-Val (V-Send₂ T S)) (E-Val v)
        —[ L-β ]→
      E-Val (V-Send₃ T S v)

  Act-Send : ∀ {n} {T : Ty [] TLin} {S : Ty [] SLin} {x : Fin n} {v : Value [] n} →
      E-App (E-Val (V-Send₃ T S v)) (E-Val (V-Var x))
        —[ L-SendVal x v ]→
      E-Val (V-Var x)

  Act-Match : ∀ {n k} {ss : Subset.Subset k} {ne : Subset.Nonempty ss}
      {x : Fin n} {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (sucℕ n)} {i : Fin k}
      (i∈ : i Subset.∈ ss) →
      E-Match (E-Val (V-Var x)) ne branches
        —[ L-RecvLab x i ]→
      substExpr (branches i i∈) (V-Var x)

  Act-Sel : ∀ {n k} {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin} {x : Fin n} →
      E-App (E-Val (V-Select₂ v i P S)) (E-Val (V-Var x))
        —[ L-SendLab x i ]→
      E-Val (V-Var x)

  Act-Select₁ : ∀ {n k} {v : Variance} {i : Fin k} {P : Ty [] KP} →
      E-TApp {K = KP} (E-Val (V-Const {n = n} (C-Select v i))) P
        —[ L-β ]→
      E-Val (V-Select₁ {n = n} v i P)

  Act-Select₂ : ∀ {n k} {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin} →
      E-TApp {K = SLin} (E-Val (V-Select₁ {n = n} v i P)) S
        —[ L-β ]→
      E-Val (V-Select₂ {n = n} v i P S)

  Act-Close : ∀ {n} {x : Fin n} →
      E-App (E-Val (V-Const C-Close)) (E-Val (V-Var x))
        —[ L-Close x ]→
      E-Val (V-Const C-Unit)

  Act-AppL : ∀ {n k} {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {e₃ : Expr [] n} {ℓ : Label n k} →
      e₁ —[ ℓ ]→ e₂
      → E-App e₁ e₃ —[ ℓ ]→ E-App e₂ (weakenExprBy k e₃)

  Act-AppR : ∀ {n k} {v : Value [] n} {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {ℓ : Label n k} →
      e₁ —[ ℓ ]→ e₂
      → E-App (E-Val v) e₁ —[ ℓ ]→ E-App (E-Val (weakenValueBy k v)) e₂

  Act-TAppE : ∀ {n k K} {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {T : Ty [] K} {ℓ : Label n k} →
      e₁ —[ ℓ ]→ e₂
      → E-TApp e₁ T —[ ℓ ]→ E-TApp e₂ T

  Act-PairL : ∀ {n k} {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {e₃ : Expr [] n} {ℓ : Label n k} →
      e₁ —[ ℓ ]→ e₂
      → E-Pair e₁ e₃ —[ ℓ ]→ E-Pair e₂ (weakenExprBy k e₃)

  Act-PairR : ∀ {n k} {v : Value [] n} {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {ℓ : Label n k} →
      e₁ —[ ℓ ]→ e₂
      → E-Pair (E-Val v) e₁ —[ ℓ ]→ E-Pair (E-Val (weakenValueBy k v)) e₂

  Act-MatchE : ∀ {n j k} {ss : Subset.Subset k} {ne : Subset.Nonempty ss}
      {e₁ : Expr [] n} {e₂ : Expr [] (j + n)}
      {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (sucℕ n)} {ℓ : Label n j} →
      e₁ —[ ℓ ]→ e₂
      → E-Match e₁ ne branches —[ ℓ ]→ E-Match e₂ ne (λ i i∈ → weakenExprBy1 j (branches i i∈))

  Act-LetPairE : ∀ {n k} {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {e₃ : Expr [] (sucℕ (sucℕ n))} {ℓ : Label n k} →
      e₁ —[ ℓ ]→ e₂
      → E-LetPair e₁ e₃ —[ ℓ ]→ E-LetPair e₂ (weakenExprBy2 k e₃)

  Act-LetUnitE : ∀ {n k} {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {e₃ : Expr [] n} {ℓ : Label n k} →
      e₁ —[ ℓ ]→ e₂
      → E-LetUnit e₁ e₃ —[ ℓ ]→ E-LetUnit e₂ (weakenExprBy k e₃)

-- `Act-TAppE` can propagate arbitrary labels because type application does not
-- mention term variables. The remaining structural rules are restricted to
-- size-preserving transitions: propagating fresh-name creation through those
-- contexts would require an explicit renaming/lifting development for
-- expressions under context extension.
