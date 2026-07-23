module ProcProgressFreshDefinitions where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
import Data.Fin.Subset as Subset
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)

open import Kinds using (SLin)
open import Types using (Ty; T-Base)
open import ExprSyntax using (Expr; Value; E-Val; NfTy)
open import ExprNormalTyping using
  ( Ctx
  ; B-Lin
  ; B-Used
  ; ∅
  ; _▻_
  ; normalizeTy
  ; _⊢_⇐_⊣_
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
import ProcSemanticsFresh as PS
open PS using
  ( Conf
  ; ConfLabel
  ; FinFreshPair
  ; _—conf[_]→_
  )
open PS.Conf using (exps; live; lookup; ∣_∣)
open import ProcTypingFresh

------------------------------------------------------------------------
-- Local states of an expression

data IsValue {n : ℕ} : Expr [] n → Set where
  is-value : (v : Value [] n) → IsValue (E-Val v)

data CommunicationLabel {n : ℕ} : Label n [] → Set where
  comm-recv-val : ∀ {x v} → CommunicationLabel (L-RecvVal x v)
  comm-recv-lab : ∀ {k} {x : Fin n} {ℓ : Fin k}
    → CommunicationLabel (L-RecvLab x ℓ)
  comm-send-val : ∀ {x v} → CommunicationLabel (L-SendVal x v)
  comm-send-lab : ∀ {k} {x : Fin n} {ℓ : Fin k}
    → CommunicationLabel (L-SendLab x ℓ)
  comm-close : ∀ {x} → CommunicationLabel (L-Close x)

record CommunicationBlocked {n : ℕ} (e : Expr [] n) : Set where
  constructor communication-blocked
  field
    label : Label n []
    target : Expr [] n
    communication : CommunicationLabel label
    transition : e —[ label ]→ target

data Runnable {n : ℕ} (e : Expr [] n) : Set where
  run-β : ∀ {e′ : Expr [] n}
    → e —[ L-β ]→ e′
    → Runnable e

  run-fork : ∀ {v : Value [] n} {e′ : Expr [] n}
    → e —[ L-Fork v ]→ e′
    → Runnable e

  run-new : ∀ {S : Ty [] SLin} {e′ : Expr [] (2 + n)}
    → e —[ L-New S ]→ e′
    → Runnable e

data LocalProgress {n : ℕ} (e : Expr [] n) : Set where
  local-value : IsValue e → LocalProgress e
  local-runnable : Runnable e → LocalProgress e
  local-communication : CommunicationBlocked e → LocalProgress e

------------------------------------------------------------------------
-- Terminal and globally deadlocked configurations

record Terminal {n : ℕ} (C : Conf n) : Set where
  constructor terminal
  field
    all-values : All IsValue (exps C)

data SynchronizationPossible : ∀ {n : ℕ} → Conf n → Set where
  sync-message : ∀ {n} {C : Conf (2 + n)}
      {x y : Fin (2 + n)} {v : Value [] (2 + n)}
      {e₁ e₂ : Expr [] (2 + n)}
    → (i j : Fin ∣ C ∣)
    → i ≢ j
    → FinFreshPair {n} x y
    → x Subset.∈ live C
    → y Subset.∈ live C
    → lookup C i —[ L-RecvVal x v ]→ e₁
    → lookup C j —[ L-SendVal y v ]→ e₂
    → SynchronizationPossible C

  sync-branch : ∀ {n k} {C : Conf (2 + n)}
      {x y : Fin (2 + n)} {ℓ : Fin k}
      {e₁ e₂ : Expr [] (2 + n)}
    → (i j : Fin ∣ C ∣)
    → i ≢ j
    → FinFreshPair {n} x y
    → x Subset.∈ live C
    → y Subset.∈ live C
    → lookup C i —[ L-RecvLab x ℓ ]→ e₁
    → lookup C j —[ L-SendLab y ℓ ]→ e₂
    → SynchronizationPossible C

  sync-close : ∀ {n} {C : Conf (2 + n)}
      {x y : Fin (2 + n)} {e₁ e₂ : Expr [] (2 + n)}
    → (i j : Fin ∣ C ∣)
    → i ≢ j
    → FinFreshPair {n} x y
    → x Subset.∈ live C
    → y Subset.∈ live C
    → lookup C i —[ L-Close x ]→ e₁
    → lookup C j —[ L-Close y ]→ e₂
    → SynchronizationPossible C

data RunnableAt {n : ℕ} (C : Conf n) : Set where
  runnable-at : (i : Fin ∣ C ∣) → Runnable (lookup C i) → RunnableAt C

record GlobalDeadlock {n : ℕ} (C : Conf n) : Set where
  constructor global-deadlock
  field
    all-quiescent :
      All (λ e → IsValue e ⊎ CommunicationBlocked e) (exps C)
    some-communication : Any CommunicationBlocked (exps C)
    no-independent-action : RunnableAt C → ⊥
    no-synchronization : SynchronizationPossible C → ⊥

------------------------------------------------------------------------
-- The progress trichotomy

data CanStep {n : ℕ} (C : Conf n) : Set where
  can-step : ∀ {k} {π : ConfLabel n k} {C′ : Conf (k + n)}
    → C —conf[ π ]→ C′
    → CanStep C

data Progress {n : ℕ} (C : Conf n) : Set where
  progress-terminal : Terminal C → Progress C
  progress-deadlock : GlobalDeadlock C → Progress C
  progress-step : CanStep C → Progress C

ConfigurationProgressTheorem : Set
ConfigurationProgressTheorem =
  ∀ {n} {Γ : Ctx [] n} {C : Conf n}
  → Γ ⊢conf C
  → Progress C

------------------------------------------------------------------------
-- Session-only expression contexts

data SessionCtx : ∀ {n : ℕ} → Ctx [] n → Set where
  session-∅ : SessionCtx ∅
  session-live : ∀ {n} {Γ : Ctx [] n} {S : NfTy [] SLin}
    → SessionCtx Γ
    → SessionCtx (B-Lin S ▻ Γ)
  session-used : ∀ {n} {Γ : Ctx [] n} {S : NfTy [] SLin}
    → SessionCtx Γ
    → SessionCtx (B-Used S ▻ Γ)

live-context-is-session : ∀ {n} {ss : Subset.Subset n} {Γ : Ctx [] n}
  → LiveCtx ss Γ
  → SessionCtx Γ
live-context-is-session LC-∅ = session-∅
live-context-is-session (LC-live live-ctx) =
  session-live (live-context-is-session live-ctx)
live-context-is-session (LC-dead live-ctx) =
  session-used (live-context-is-session live-ctx)

split-session-context : ∀ {n} {Γ Γ₁ Γ₂ : Ctx [] n}
  → SessionCtx Γ
  → Split Γ Γ₁ Γ₂
  → SessionCtx Γ₁ × SessionCtx Γ₂
split-session-context session-∅ S-∅ = session-∅ , session-∅
split-session-context (session-live session) (S-Linˡ split)
  with split-session-context session split
... | session₁ , session₂ =
  session-live session₁ , session-used session₂
split-session-context (session-live session) (S-Linʳ split)
  with split-session-context session split
... | session₁ , session₂ =
  session-used session₁ , session-live session₂
split-session-context (session-used session) (S-Used split)
  with split-session-context session split
... | session₁ , session₂ =
  session-used session₁ , session-used session₂

LocalProgressTheorem : Set
LocalProgressTheorem =
  ∀ {n} {Γ Γ′ : Ctx [] n} {e : Expr [] n}
  → SessionCtx Γ
  → Γ ⊢ e ⇐ normalizeTy T-Base ⊣ Γ′
  → LocalProgress e
