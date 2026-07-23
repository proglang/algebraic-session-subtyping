module ExprSemantics where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _+_) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Product using (_,_)

open import Kinds
open import Duality using (D-S)
open import Types
open import ExprSyntax
open import ExprSubstitution using (substExpr; substExpr₂; substValue; substTyValue; renameExpr; renameValue; extRen; extRen2)
open import ExprNormalTyping using (normalizeTy)

-- The paper distinguishes several observable labels.
-- In the current syntax `wait` and `terminate` were merged into `C-Close`,
-- so we expose a single close-style label here.

data Label (n : ℕ) : List (Ty [] SLin) → Set where
  L-β       : Label n []
  L-Fork    : Value [] n → Label n []
  L-New     : (S : Ty [] SLin) → Label n (S ∷ T-Dual D-S S ∷ [])
  L-RecvVal : Fin n → Value [] n → Label n []
  L-RecvLab : ∀ {k} → Fin n → Fin k → Label n []
  L-SendVal : Fin n → Value [] n → Label n []
  L-SendLab : ∀ {k} → Fin n → Fin k → Label n []
  L-Close   : Fin n → Label n []

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

data _—[_]→_ {n} : ∀ {Θ : List (Ty [] SLin)} → Expr [] n → Label n Θ → Expr [] (length Θ + n) → Set where
  Act-App : ∀ {pk} {T : NfTy [] (KV pk Lin)}
      {e : Expr [] (sucℕ n)} {v : Value [] n} →
      E-App (E-Val (V-Abs T e)) (E-Val v)
        —[ L-β ]→
      substExpr e v

  Act-TApp : ∀ {K} {T : Ty [] K} {v : Value (K ∷ []) n} →
      E-TApp (E-Val (V-TAbs K v)) (normalizeTy T)
        —[ L-β ]→
      E-Val (substTyValue v (normalizeTy T))

  Act-LetPair : ∀ {u v : Value [] n} {e : Expr [] (sucℕ (sucℕ n))} →
      E-LetPair (E-Val (V-Pair u v)) e
        —[ L-β ]→
      substExpr₂ e u v

  Act-LetUnit : ∀ {e : Expr [] n} →
      E-LetUnit (E-Val (V-Const C-Unit)) e
        —[ L-β ]→
      e

  Act-PairV : ∀ {u v : Value [] n} →
      E-Pair (E-Val u) (E-Val v)
        —[ L-β ]→
      E-Val (V-Pair u v)

  Act-Rec : ∀ {pk₁ pk₂ m₁ m₂}
      {T : NfTy [] (KV pk₁ m₁)} {U : NfTy [] (KV pk₂ m₂)}
      {v : Value [] (sucℕ n)} {u : Expr [] n} →
      E-App (E-Val (V-Rec T U v)) u
        —[ L-β ]→
      E-App (E-Val (substValue v (V-Rec T U v))) u

  Act-Fork : ∀ {v : Value [] n} →
      E-App (E-Val (V-Const C-Fork)) (E-Val v)
        —[ L-Fork v ]→
      E-Val (V-Const C-Unit)

  Act-New : ∀ {S : Ty [] SLin} →
      E-TApp (E-Val (V-Const C-New)) (normalizeTy S)
        —[ L-New S ]→
      (freshPair {n = n})

  Act-Receive₁ : ∀ {T : Ty [] TLin} →
      E-TApp {K = TLin} (E-Val (V-Const {n = n} C-Receive)) (normalizeTy T)
        —[ L-β ]→
      E-Val (V-Receive₁ {n = n} (normalizeTy T))

  Act-Receive₂ : ∀ {pk} {T : NfTy [] (KV pk Lin)} {S : NfTy [] SLin} →
      E-TApp {K = SLin} (E-Val (V-Receive₁ {n = n} T)) S
        —[ L-β ]→
      E-Val (V-Receive₂ {n = n} T S)

  Act-Rcv : ∀ {pk} {T : NfTy [] (KV pk Lin)} {S : NfTy [] SLin}
      {x : Fin n} {v : Value [] n} →
      E-App (E-Val (V-Receive₂ T S)) (E-Val (V-Var x))
        —[ L-RecvVal x v ]→
      E-Val (V-Pair v (V-Var x))

  Act-Send₁ : ∀ {T : Ty [] TLin} →
      E-TApp {K = TLin} (E-Val (V-Const {n = n} C-Send)) (normalizeTy T)
        —[ L-β ]→
      E-Val (V-Send₁ {n = n} (normalizeTy T))

  Act-Send₂ : ∀ {pk} {T : NfTy [] (KV pk Lin)} {S : NfTy [] SLin} →
      E-TApp {K = SLin} (E-Val (V-Send₁ {n = n} T)) S
        —[ L-β ]→
      E-Val (V-Send₂ {n = n} T S)

  Act-Send : ∀ {pk} {T : NfTy [] (KV pk Lin)} {S : NfTy [] SLin}
      {x : Fin n} {v : Value [] n} →
      E-App (E-Val (V-Send₂ T S)) (E-Val (V-Pair v (V-Var x)))
        —[ L-SendVal x v ]→
      E-Val (V-Var x)

  Act-Match : ∀ {k} {ss : Subset.Subset k} {ne : Subset.Nonempty ss}
      {x : Fin n} {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (sucℕ n)} {i : Fin k}
      (i∈ : i Subset.∈ ss) →
      E-Match (E-Val (V-Var x)) ne branches
        —[ L-RecvLab x i ]→
      substExpr (branches i i∈) (V-Var x)

  Act-Sel : ∀ {k} {v : Variance} {i : Fin k}
      {P : NfTy [] KP} {S : NfTy [] SLin} {x : Fin n} →
      E-App (E-Val (V-Select₂ v i P S)) (E-Val (V-Var x))
        —[ L-SendLab x i ]→
      E-Val (V-Var x)

  Act-Select₁ : ∀ {k} {v : Variance} {i : Fin k} {P : Ty [] KP} →
      E-TApp {K = KP} (E-Val (V-Const {n = n} (C-Select v i))) (normalizeTy P)
        —[ L-β ]→
      E-Val (V-Select₁ {n = n} v i (normalizeTy P))

  Act-Select₂ : ∀ {k} {v : Variance} {i : Fin k}
      {P : NfTy [] KP} {S : NfTy [] SLin} →
      E-TApp {K = SLin} (E-Val (V-Select₁ {n = n} v i P)) S
        —[ L-β ]→
      E-Val (V-Select₂ {n = n} v i P S)

  Act-Close : ∀ {x : Fin n} →
      E-App (E-Val (V-Const C-Close)) (E-Val (V-Var x))
        —[ L-Close x ]→
      E-Val (V-Const C-Unit)

  Act-AppL : ∀ {Θ} {ℓ : Label n Θ} {e₁ : Expr [] n} {e₂ : Expr [] (length Θ + n)} {e₃ : Expr [] n} →
      e₁ —[ ℓ ]→ e₂
      → E-App e₁ e₃ —[ ℓ ]→ E-App e₂ (weakenExprBy (length Θ) e₃)

  Act-AppR : ∀ {Θ} → let k = length Θ in {v : Value [] n} {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {ℓ : Label n Θ} →
      e₁ —[ ℓ ]→ e₂
      → E-App (E-Val v) e₁ —[ ℓ ]→ E-App (E-Val (weakenValueBy k v)) e₂

  Act-TAppE : ∀ {Θ K} → let k = length Θ in {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {T : NfTy [] K} {ℓ : Label n Θ} →
      e₁ —[ ℓ ]→ e₂
      → E-TApp e₁ T —[ ℓ ]→ E-TApp e₂ T

  Act-PairL : ∀ {Θ} → let k = length Θ in {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {e₃ : Expr [] n} {ℓ : Label n Θ} →
      e₁ —[ ℓ ]→ e₂
      → E-Pair e₁ e₃ —[ ℓ ]→ E-Pair e₂ (weakenExprBy k e₃)

  Act-PairR : ∀ {Θ} → let k = length Θ in {v : Value [] n} {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {ℓ : Label n Θ} →
      e₁ —[ ℓ ]→ e₂
      → E-Pair (E-Val v) e₁ —[ ℓ ]→ E-Pair (E-Val (weakenValueBy k v)) e₂

  Act-MatchE : ∀ {Θ k} → let j = length Θ in
      {ss : Subset.Subset k} {ne : Subset.Nonempty ss}
      {e₁ : Expr [] n} {e₂ : Expr [] (j + n)}
      {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (sucℕ n)} {ℓ : Label n Θ} →
      e₁ —[ ℓ ]→ e₂
      → E-Match e₁ ne branches —[ ℓ ]→ E-Match e₂ ne (λ i i∈ → weakenExprBy1 j (branches i i∈))

  Act-LetPairE : ∀ {Θ} → let k = length Θ in {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {e₃ : Expr [] (sucℕ (sucℕ n))} {ℓ : Label n Θ} →
      e₁ —[ ℓ ]→ e₂
      → E-LetPair e₁ e₃ —[ ℓ ]→ E-LetPair e₂ (weakenExprBy2 k e₃)

  Act-LetUnitE : ∀ {Θ} → let k = length Θ in {e₁ : Expr [] n} {e₂ : Expr [] (k + n)} {e₃ : Expr [] n} {ℓ : Label n Θ} →
      e₁ —[ ℓ ]→ e₂
      → E-LetUnit e₁ e₃ —[ ℓ ]→ E-LetUnit e₂ (weakenExprBy k e₃)

-- `Act-TAppE` can propagate arbitrary labels because type application does not
-- mention term variables. The remaining structural rules are restricted to
-- size-preserving transitions: propagating fresh-name creation through those
-- contexts would require an explicit renaming/lifting development for
-- expressions under context extension.
