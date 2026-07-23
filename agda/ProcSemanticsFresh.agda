module ProcSemanticsFresh where

open import Data.Fin using (Fin; _<_) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List as L using (List;[]; length;_∷_; map)
open import Data.List.Properties using (length-map)
open import Data.Nat using (ℕ; _+_) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Vec using () renaming (_∷_ to _∷ᵥ_)
open import Function using (_∘_; const)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; subst)

open import ExprSyntax using
  ( C-Unit
  ; Expr
  ; Value
  ; E-App
  ; E-Val
  ; V-Const
  ; V-Var
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
  ; shiftRen
  ; weakenValueBy
  ; weakenExprBy
  )
open import ExprSubstitution using (renameExpr)
open import Kinds using (SLin)
open import Types using (Ty)

length-updateAt : ∀ {A : Set} {f : A → A} (xs : List A) (i : Fin (length xs))
  → length (L.updateAt xs i f) ≡ length xs
length-updateAt (x ∷ xs) fzero = refl
length-updateAt (x ∷ xs) (fsuc i) = cong sucℕ (length-updateAt xs i)

-- We deviate from the process LTS in Fig. 7!
-- Instead of having structure composed of nested pars and binders,
-- we define a process configuration as a multiset of expressions.
-- the expressions are closed wrt type variables, but share the common
-- sessions in `n` free variables.

record Conf (n : ℕ) : Set where
  field
    exps : List (Expr [] n)
    live : Subset.Subset n

  ∣_∣ : ℕ
  ∣_∣ = length exps

  lookup : Fin (length exps) → Expr [] n
  lookup = L.lookup exps

  updateAt : Fin (length exps) → (Expr [] n → Expr [] n) → Conf n
  updateAt i f = record
    { exps = L.updateAt exps i f
    ; live = live
    }

  add : Expr [] n → Conf n
  add e = record
    { exps = e ∷ exps
    ; live = live
    }

  renameConf : ∀ {m} → (Fin n → Fin m)
    → (Subset.Subset n → Subset.Subset m)
    → Conf m
  renameConf ρ renameLive = record
    { exps = map (renameExpr ρ) exps
    ; live = renameLive live
    }

  closePair : Fin n → Fin n → Conf n
  closePair x y = record
    { exps = exps
    ; live = (live Subset.- x) Subset.- y
    }

open Conf

activateFreshPair : ∀ {n} → Conf n → Conf (2 + n)
activateFreshPair C =
  renameConf C (shiftRen 2)
    (λ live → Subset.inside ∷ᵥ Subset.inside ∷ᵥ live)

-- one channel end lives at even addresses 2n; the corresponding end at address 1+2n
data FinFreshPair : ∀ {n} → Fin (sucℕ (sucℕ n)) → Fin (sucℕ (sucℕ n)) → Set where
  here-fwd : ∀ {n} → FinFreshPair {n} fzero (fsuc fzero)
  here-bwd : ∀ {n} → FinFreshPair {n} (fsuc fzero) fzero
  there    : ∀ {n} {i j} → FinFreshPair {n} i j
    → FinFreshPair {sucℕ (sucℕ n)} (fsuc (fsuc i)) (fsuc (fsuc j))


data ConfLabel (n : ℕ) : ℕ → Set where
  C-τ       : ConfLabel n 0
  C-new     : ConfLabel n 2


-- Reduction of configurations is inspired by Fig. 7

data _—conf[_]→_ : ∀ {n} {k} → Conf n → ConfLabel n k → Conf (k + n) → Set where

  Act-Beta : ∀ {n} {e′ : Expr [] n} {C : Conf n} {i : Fin ∣ C ∣} →
      lookup C i —[ L-β ]→ e′
      → C —conf[ C-τ ]→ updateAt C i (const e′)

  Act-Fork : ∀ {n} {e′ : Expr [] n} {v : Value [] n} {C : Conf n} {i : Fin ∣ C ∣} →
      lookup C i —[ L-Fork v ]→ e′
      → C —conf[ C-τ ]→ add (updateAt C i (const e′)) ((E-App (E-Val v) (E-Val (V-Const C-Unit))))

  Act-New : ∀ {n} {e′ : Expr [] (2 + n)} {S : Ty [] SLin} {C : Conf n} {i : Fin ∣ C ∣} →
      lookup C i —[ L-New S ]→ e′
      → C —conf[ C-new ]→
        updateAt (activateFreshPair C)
          (subst Fin (sym (length-map _ (exps C))) i) (const e′)

  Act-Msg : ∀ {n} {e₁ e₂ : Expr [] (2 + n)} {v : Value [] (2 + n)} {C : Conf (2 + n)}
          {x y : Fin (2 + n)}
      → (i j : Fin ∣ C ∣)
      → i ≢ j
      → FinFreshPair{n} x y
      → x Subset.∈ live C
      → y Subset.∈ live C
      → lookup C i —[ L-RecvVal x v ]→ e₁
      → lookup C j —[ L-SendVal y v ]→ e₂
      → C —conf[ C-τ ]→ let C₁ = updateAt C i (const e₁) in
                        updateAt C₁ (subst Fin (sym (length-updateAt (exps C) i)) j) (const e₂)

  Act-Bra : ∀ {n k} {e₁ e₂ : Expr [] (2 + n)} {ℓ : Fin k}
          {C : Conf (2 + n)}
          {x y : Fin (2 + n)}
      → (i j : Fin ∣ C ∣)
      → i ≢ j
      → FinFreshPair {n} x y
      → x Subset.∈ live C
      → y Subset.∈ live C
      → lookup C i —[ L-RecvLab x ℓ ]→ e₁
      → lookup C j —[ L-SendLab y ℓ ]→ e₂
      → C —conf[ C-τ ]→ let C₁ = updateAt C i (const e₁) in
                        updateAt C₁ (subst Fin (sym (length-updateAt (exps C) i)) j) (const e₂)

  -- Configurations have no explicit restriction constructor.  Closing a
  -- fresh pair reduces both participating expressions in place and marks the
  -- two endpoint entries dead in the shared de Bruijn namespace.
  Act-Wait : ∀ {n} {e₁ e₂ : Expr [] (2 + n)}
          {C : Conf (2 + n)}
          {x y : Fin (2 + n)}
      → (i j : Fin ∣ C ∣)
      → i ≢ j
      → FinFreshPair {n} x y
      → x Subset.∈ live C
      → y Subset.∈ live C
      → lookup C i —[ L-Close x ]→ e₁
      → lookup C j —[ L-Close y ]→ e₂
      → C —conf[ C-τ ]→ let C₁ = updateAt C i (const e₁) in
        closePair
          (updateAt C₁
            (subst Fin (sym (length-updateAt (exps C) i)) j)
            (const e₂))
          x y
