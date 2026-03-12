module ExprSyntax where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_)

open import Kinds
open import Types

TyArg : List Kind → Set
TyArg Δ = Σ Kind (Ty Δ)

data Binding (Δ : List Kind) : Set where
  B-Lin : ∀ {K} → Ty Δ K → Binding Δ
  B-Un  : ∀ {K} → Ty Δ K → Binding Δ

Ctx : List Kind → Set
Ctx Δ = List (Binding Δ)

data Const : Set where
  C-Unit      : Const
  C-Fork      : Const
  C-New       : Const
  C-Receive   : Const
  C-Send      : Const
  C-Select    : ∀ {k} → Fin k → Const
  C-Close     : Const

mutual

  data Value (Δ : List Kind) (n : ℕ) : Set where
    V-Const    : Const → Value Δ n
    V-Var      : Fin n → Value Δ n
    V-Abs      : Ty Δ TLin → Expr Δ (suc n) → Value Δ n
    V-Rec      : Ty Δ TLin → Value Δ (suc n) → Value Δ n
    V-TAbs     : (K : Kind) → Value (K ∷ Δ) n → Value Δ n
    V-Pair     : Value Δ n → Value Δ n → Value Δ n
    V-Receive₁ : Ty Δ TLin → Value Δ n
    V-Receive₂ : Ty Δ TLin → Ty Δ SLin → Value Δ n
    V-Send₁    : Ty Δ TLin → Value Δ n
    V-Send₂    : Ty Δ TLin → Ty Δ SLin → Value Δ n
    V-Send₃    : Ty Δ TLin → Ty Δ SLin → Value Δ n → Value Δ n
    V-Selectᵀ  : ∀ {k} → Fin k → List (TyArg Δ) → Value Δ n

  data Expr (Δ : List Kind) (n : ℕ) : Set where
    E-Val     : Value Δ n → Expr Δ n
    E-App     : Expr Δ n → Expr Δ n → Expr Δ n
    E-TApp    : Expr Δ n → Ty Δ K → Expr Δ n
    E-LetUnit : Expr Δ n → Expr Δ n → Expr Δ n
    E-Pair    : Expr Δ n → Expr Δ n → Expr Δ n
    E-LetPair : Expr Δ n → Expr Δ (suc (suc n)) → Expr Δ n
    E-Match   : ∀ {k} → Expr Δ n → (Fin k → Expr Δ (suc n)) → Expr Δ n

data Process (Δ : List Kind) (n : ℕ) : Set where
  P-Exp : Expr Δ n → Process Δ n
  P-Par : Process Δ n → Process Δ n → Process Δ n
  P-New : Process Δ (suc (suc n)) → Process Δ n
