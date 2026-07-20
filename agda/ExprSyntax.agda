module ExprSyntax where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_)
import Data.Fin.Subset as Subset

open import Kinds
open import Types
open import NormalTypesSubstitution using (NFKind)

NfTy : List Kind → Kind → Set
NfTy = NFKind

TyArg : List Kind → Set
TyArg Δ = Σ Kind (Ty Δ)

data Const : Set where
  C-Unit      : Const
  C-Fork      : Const
  C-New       : Const
  C-Receive   : Const
  C-Send      : Const
  C-Select    : ∀ {k} → Variance → Fin k → Const
  C-Close     : Const

mutual

  data Value (Δ : List Kind) (n : ℕ) : Set where
    V-Const    : Const → Value Δ n
    V-Var      : Fin n → Value Δ n
    V-Abs      : NfTy Δ (KV pk m) → Expr Δ (suc n) → Value Δ n
    V-Rec      : NfTy Δ (KV pk₁ m₁) → NfTy Δ (KV pk₂ m₂) → Value Δ (suc n) → Value Δ n
    V-TAbs     : (K : Kind) → Value (K ∷ Δ) n → Value Δ n
    V-Pair     : Value Δ n → Value Δ n → Value Δ n
    V-Receive₁ : NfTy Δ (KV pk Lin) → Value Δ n
    V-Receive₂ : NfTy Δ (KV pk Lin) → NfTy Δ SLin → Value Δ n
    V-Send₁    : NfTy Δ (KV pk Lin) → Value Δ n
    V-Send₂    : NfTy Δ (KV pk Lin) → NfTy Δ SLin → Value Δ n
    V-Select₁  : ∀ {k} → Variance → Fin k → NfTy Δ KP → Value Δ n
    V-Select₂  : ∀ {k} → Variance → Fin k → NfTy Δ KP → NfTy Δ SLin → Value Δ n

  data Expr (Δ : List Kind) (n : ℕ) : Set where
    E-Val     : Value Δ n → Expr Δ n
    E-App     : Expr Δ n → Expr Δ n → Expr Δ n
    E-TApp    : Expr Δ n → NfTy Δ K → Expr Δ n
    E-LetUnit : Expr Δ n → Expr Δ n → Expr Δ n
    E-Pair    : Expr Δ n → Expr Δ n → Expr Δ n
    E-LetPair : Expr Δ n → Expr Δ (suc (suc n)) → Expr Δ n
    E-Match   : ∀ {k} {ss : Subset.Subset k} → Expr Δ n → Subset.Nonempty ss → ((i : Fin k) → i Subset.∈ ss → Expr Δ (suc n)) → Expr Δ n
