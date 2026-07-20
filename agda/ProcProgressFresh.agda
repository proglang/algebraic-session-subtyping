module ProcProgressFresh where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (const)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List.Relation.Unary.All using ()
  renaming ([] to all[]; _∷_ to _all∷_)
open import Data.List.Relation.Unary.Any using ()
  renaming (here to any-here; there to any-there)
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
  ; C-τ
  ; C-new
  ; FinFreshPair
  ; _—conf[_]→_
  )
open PS.Conf using (exps; live; lookup; ∣_∣)
open import ProcTypingFresh

------------------------------------------------------------------------
-- Local states of an expression

-- Values are terminal at expression level.  Keeping this as a predicate,
-- rather than testing the outer constructor elsewhere, makes the terminal
-- configuration predicate independent of typing derivations.

data IsValue {n : ℕ} : Expr [] n → Set where
  is-value : (v : Value [] n) → IsValue (E-Val v)

-- These are exactly the expression labels which need another thread before
-- they can become a configuration transition.  All of them preserve the
-- shared channel namespace.

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

-- A runnable expression has a configuration-level action which needs no
-- partner.  New is separate because its target has two more channel slots.

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

-- This is the local progress statement needed for a configuration thread.
-- Communication-blocked is not a stuck expression: it has an observable
-- expression transition, but that transition requires a matching thread.

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

-- SynchronizationPossible repeats only the premises of the three direct
-- synchronization rules.  In particular, it records distinct threads, live
-- peer endpoints, and agreement on the transmitted value or label.

data SynchronizationPossible : ∀ {n : ℕ} → Conf n → Set where
  sync-message : ∀ {n} {C : Conf (2 + n)}
      {i j : Fin ∣ C ∣} {i≠j : i ≢ j}
      {x y : Fin (2 + n)} {v : Value [] (2 + n)}
      {e₁ e₂ : Expr [] (2 + n)}
    → FinFreshPair {n} x y
    → x Subset.∈ live C
    → y Subset.∈ live C
    → lookup C i —[ L-RecvVal x v ]→ e₁
    → lookup C j —[ L-SendVal y v ]→ e₂
    → SynchronizationPossible C

  sync-branch : ∀ {n k} {C : Conf (2 + n)}
      {i j : Fin ∣ C ∣} {i≠j : i ≢ j}
      {x y : Fin (2 + n)} {ℓ : Fin k}
      {e₁ e₂ : Expr [] (2 + n)}
    → FinFreshPair {n} x y
    → x Subset.∈ live C
    → y Subset.∈ live C
    → lookup C i —[ L-RecvLab x ℓ ]→ e₁
    → lookup C j —[ L-SendLab y ℓ ]→ e₂
    → SynchronizationPossible C

  sync-close : ∀ {n} {C : Conf (2 + n)}
      {i j : Fin ∣ C ∣} {i≠j : i ≢ j}
      {x y : Fin (2 + n)} {e₁ e₂ : Expr [] (2 + n)}
    → FinFreshPair {n} x y
    → x Subset.∈ live C
    → y Subset.∈ live C
    → lookup C i —[ L-Close x ]→ e₁
    → lookup C j —[ L-Close y ]→ e₂
    → SynchronizationPossible C

data RunnableAt {n : ℕ} (C : Conf n) : Set where
  runnable-at : (i : Fin ∣ C ∣) → Runnable (lookup C i) → RunnableAt C

-- A global deadlock is positive information about every thread, not merely
-- the negation of a configuration step.  At least one thread is waiting for
-- communication, every other thread is a value or is also waiting, no thread
-- has an independent action, and no pair can synchronize on live peers.

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

-- This is the final progress theorem to be discharged.  Naming its type does
-- not assume it: the proved result at the end of this module exposes the
-- three remaining constructive obligations explicitly.

ConfigurationProgressTheorem : Set
ConfigurationProgressTheorem =
  ∀ {n} {Γ : Ctx [] n} {C : Conf n}
  → Γ ⊢conf C
  → Progress C

runnable-at-steps : ∀ {n} {C : Conf n} → RunnableAt C → CanStep C
runnable-at-steps (runnable-at i (run-β step)) =
  can-step (PS.Act-Beta {i = i} step)
runnable-at-steps (runnable-at i (run-fork step)) =
  can-step (PS.Act-Fork {i = i} step)
runnable-at-steps (runnable-at i (run-new step)) =
  can-step (PS.Act-New {i = i} step)

synchronization-steps :
  ∀ {n} {C : Conf n} → SynchronizationPossible C → CanStep C
synchronization-steps
    (sync-message {i≠j = i≠j} pair x-live y-live receive send) =
  can-step (PS.Act-Msg {i≠j = i≠j} pair x-live y-live receive send)
synchronization-steps
    (sync-branch {i≠j = i≠j} pair x-live y-live receive send) =
  can-step (PS.Act-Bra {i≠j = i≠j} pair x-live y-live receive send)
synchronization-steps
    (sync-close {i≠j = i≠j} pair x-live y-live close₁ close₂) =
  can-step (PS.Act-Wait {i≠j = i≠j} pair x-live y-live close₁ close₂)

step-source : ∀ {n} {C : Conf n}
  → CanStep C
  → RunnableAt C ⊎ SynchronizationPossible C
step-source (can-step (PS.Act-Beta {i = i} step)) =
  inj₁ (runnable-at i (run-β step))
step-source (can-step (PS.Act-Fork {i = i} step)) =
  inj₁ (runnable-at i (run-fork step))
step-source (can-step (PS.Act-New {i = i} step)) =
  inj₁ (runnable-at i (run-new step))
step-source
    (can-step
      (PS.Act-Msg {i≠j = i≠j} pair x-live y-live receive send)) =
  inj₂ (sync-message {i≠j = i≠j} pair x-live y-live receive send)
step-source
    (can-step
      (PS.Act-Bra {i≠j = i≠j} pair x-live y-live receive send)) =
  inj₂ (sync-branch {i≠j = i≠j} pair x-live y-live receive send)
step-source
    (can-step
      (PS.Act-Wait {i≠j = i≠j} pair x-live y-live close₁ close₂)) =
  inj₂ (sync-close {i≠j = i≠j} pair x-live y-live close₁ close₂)

deadlock-cannot-step : ∀ {n} {C : Conf n}
  → GlobalDeadlock C
  → CanStep C
  → ⊥
deadlock-cannot-step deadlock step with step-source step
... | inj₁ runnable =
  GlobalDeadlock.no-independent-action deadlock runnable
... | inj₂ synchronization =
  GlobalDeadlock.no-synchronization deadlock synchronization

------------------------------------------------------------------------
-- Lifting local progress to the thread pool

data ListProgress {n : ℕ} (es : List (Expr [] n)) : Set where
  list-terminal : All IsValue es → ListProgress es
  list-runnable :
    (i : Fin (length es)) → Runnable (Data.List.lookup es i) → ListProgress es
  list-quiescent :
    All (λ e → IsValue e ⊎ CommunicationBlocked e) es
    → Any CommunicationBlocked es
    → ListProgress es

all-values-quiescent : ∀ {n} {es : List (Expr [] n)}
  → All IsValue es
  → All (λ e → IsValue e ⊎ CommunicationBlocked e) es
all-values-quiescent all[] = all[]
all-values-quiescent (v all∷ vs) = inj₁ v all∷ all-values-quiescent vs

classify-list : ∀ {n} {es : List (Expr [] n)}
  → All LocalProgress es
  → ListProgress es
classify-list all[] = list-terminal all[]
classify-list (local-value v all∷ ps) with classify-list ps
... | list-terminal vs = list-terminal (v all∷ vs)
... | list-runnable i run = list-runnable (fsuc i) run
... | list-quiescent qs blocked =
  list-quiescent (inj₁ v all∷ qs) (any-there blocked)
classify-list (local-runnable run all∷ ps) =
  list-runnable fzero run
classify-list (local-communication blocked all∷ ps)
  with classify-list ps
... | list-terminal vs =
  list-quiescent
    (inj₂ blocked all∷ all-values-quiescent vs)
    (any-here blocked)
... | list-runnable i run = list-runnable (fsuc i) run
... | list-quiescent qs blocked′ =
  list-quiescent
    (inj₂ blocked all∷ qs)
    (any-here blocked)

list-progress-conf : ∀ {n} {C : Conf n}
  → ListProgress (exps C)
  → Dec (RunnableAt C)
  → Dec (SynchronizationPossible C)
  → Progress C
list-progress-conf (list-terminal values) runnable? sync? =
  progress-terminal (terminal values)
list-progress-conf (list-runnable i run) runnable? sync? =
  progress-step (runnable-at-steps (runnable-at i run))
list-progress-conf (list-quiescent qs blocked) (yes runnable) sync? =
  progress-step (runnable-at-steps runnable)
list-progress-conf (list-quiescent qs blocked) (no no-runnable) (yes sync) =
  progress-step (synchronization-steps sync)
list-progress-conf
    (list-quiescent qs blocked) (no no-runnable) (no no-sync) =
  progress-deadlock
    (global-deadlock qs blocked no-runnable no-sync)

------------------------------------------------------------------------
-- Typing connects the configuration to the local expression theorem

-- Contexts split from LiveCtx contain only linear session bindings and their
-- used markers.  This excludes free function and polymorphic variables, the
-- crucial hypothesis for canonical forms of configuration expressions.

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

-- The remaining expression-level theorem has this precise statement.  It is
-- deliberately a parameter of the configuration proof below rather than an
-- unproved postulate.  A proof proceeds by induction on the checking and
-- synthesis derivations, using SessionCtx in the variable canonical cases.

LocalProgressTheorem : Set
LocalProgressTheorem =
  ∀ {n} {Γ Γ′ : Ctx [] n} {e : Expr [] n}
  → SessionCtx Γ
  → Γ ⊢ e ⇐ normalizeTy T-Base ⊣ Γ′
  → LocalProgress e

threads-progress : ∀ {n} {Γ : Ctx [] n} {es : List (Expr [] n)}
  → LocalProgressTheorem
  → SessionCtx Γ
  → ThreadsTyped Γ es
  → All LocalProgress es
threads-progress local session (TT-[] all-used) = all[]
threads-progress local session (TT-∷ split check all-used threads)
  with split-session-context session split
... | session-e , session-rest =
  local session-e check all∷
    threads-progress local session-rest threads

-- This completes the global part of progress.  What remains for an
-- assumption-free theorem is to implement LocalProgressTheorem and the two
-- finite decision procedures below.

configuration-progress : ∀ {n} {Γ : Ctx [] n} {C : Conf n}
  → LocalProgressTheorem
  → Γ ⊢conf C
  → Dec (RunnableAt C)
  → Dec (SynchronizationPossible C)
  → Progress C
configuration-progress local (T-Conf live-ctx threads) runnable? sync? =
  list-progress-conf
    (classify-list
      (threads-progress local (live-context-is-session live-ctx) threads))
    runnable?
    sync?
