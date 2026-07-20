module ProcTypingFresh where

import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_)
open import Data.Vec using () renaming (_∷_ to _∷ᵥ_)

open import Kinds using (SLin; KV; Lin; Un)
open import Types using (T-Base)
open import ExprSyntax using (Expr; NfTy)
open import ExprNormalTyping
open import ExprContextProperties public
  using
  ( AllUsed
  ; AU-∅
  ; AU-used
  ; AU-un
  )
import ProcSemanticsFresh as PSF
open PSF using (Conf)
open PSF.Conf using (exps; live)

-- A split assigns each linear binding to exactly one side, copies
-- unrestricted bindings, and retains used bindings on both sides.

data Split {Δ} : ∀ {n} → Ctx Δ n → Ctx Δ n → Ctx Δ n → Set where
  S-∅ : Split ∅ ∅ ∅

  S-Linˡ : ∀ {n} {Γ Γ₁ Γ₂ : Ctx Δ n} {pk}
      {T : NfTy Δ (KV pk Lin)}
    → Split Γ Γ₁ Γ₂
    → Split (B-Lin T ▻ Γ) (B-Lin T ▻ Γ₁) (B-Used T ▻ Γ₂)

  S-Linʳ : ∀ {n} {Γ Γ₁ Γ₂ : Ctx Δ n} {pk}
      {T : NfTy Δ (KV pk Lin)}
    → Split Γ Γ₁ Γ₂
    → Split (B-Lin T ▻ Γ) (B-Used T ▻ Γ₁) (B-Lin T ▻ Γ₂)

  S-Un : ∀ {n} {Γ Γ₁ Γ₂ : Ctx Δ n} {pk}
      {T : NfTy Δ (KV pk Un)}
    → Split Γ Γ₁ Γ₂
    → Split (B-Un T ▻ Γ) (B-Un T ▻ Γ₁) (B-Un T ▻ Γ₂)

  S-Used : ∀ {n} {Γ Γ₁ Γ₂ : Ctx Δ n} {pk}
      {T : NfTy Δ (KV pk Lin)}
    → Split Γ Γ₁ Γ₂
    → Split (B-Used T ▻ Γ) (B-Used T ▻ Γ₁) (B-Used T ▻ Γ₂)

-- The liveness set and the configuration context describe the same channel
-- namespace.  A live slot contains an available linear session binding; a
-- dead slot retains its type but is marked used, so expression typing cannot
-- access it.

data LiveCtx : ∀ {n} → Subset.Subset n → Ctx [] n → Set where
  LC-∅ : LiveCtx Subset.⊥ ∅

  LC-live : ∀ {n} {ss : Subset.Subset n} {Γ : Ctx [] n}
      {S : NfTy [] SLin}
    → LiveCtx ss Γ
    → LiveCtx (Subset.inside ∷ᵥ ss) (B-Lin S ▻ Γ)

  LC-dead : ∀ {n} {ss : Subset.Subset n} {Γ : Ctx [] n}
      {S : NfTy [] SLin}
    → LiveCtx ss Γ
    → LiveCtx (Subset.outside ∷ᵥ ss) (B-Used S ▻ Γ)

-- Declarative typing of a configuration's expression multiset.  The split
-- assigns each available linear channel either to the head expression or to
-- the remaining expressions.  The head must consume everything assigned to
-- it, and the empty configuration may retain only already-used bindings.

data ThreadsTyped : ∀ {n} → Ctx [] n → List (Expr [] n) → Set where
  TT-[] : ∀ {n} {Γ : Ctx [] n}
    → AllUsed Γ
    → ThreadsTyped Γ []

  TT-∷ : ∀ {n} {Γ Γe Γrest Γe′ : Ctx [] n}
      {e : Expr [] n} {es : List (Expr [] n)}
    → Split Γ Γe Γrest
    → Γe ⊢ e ⇐ normalizeTy T-Base ⊣ Γe′
    → AllUsed Γe′
    → ThreadsTyped Γrest es
    → ThreadsTyped Γ (e ∷ es)

infix 4 _⊢conf_

-- Configuration typing exposes the complete typed channel namespace.  The
-- `LiveCtx` premise rules out use of dead channels; `ThreadsTyped` partitions
-- every live channel among the expressions and consumes it exactly once.

data _⊢conf_ : ∀ {n} → Ctx [] n → Conf n → Set where
  T-Conf : ∀ {n} {Γ : Ctx [] n} {C : Conf n}
    → LiveCtx (live C) Γ
    → ThreadsTyped Γ (exps C)
    → Γ ⊢conf C
