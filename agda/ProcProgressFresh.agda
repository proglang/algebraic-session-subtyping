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
open import ProcProgressFreshDefinitions public
open import ProcLocalProgressFresh using (local-progress)
open import ProcProgressFreshDecidable using
  ( runnable-at?
  ; synchronization-possible?
  )

------------------------------------------------------------------------
-- Operational bridges

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
    (sync-message i j i≠j pair x-live y-live receive send) =
  can-step (PS.Act-Msg i j i≠j pair x-live y-live receive send)
synchronization-steps
    (sync-branch i j i≠j pair x-live y-live receive send) =
  can-step (PS.Act-Bra i j i≠j pair x-live y-live receive send)
synchronization-steps
    (sync-close i j i≠j pair x-live y-live close₁ close₂) =
  can-step (PS.Act-Wait i j i≠j pair x-live y-live close₁ close₂)

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
      (PS.Act-Msg i j i≠j pair x-live y-live receive send)) =
  inj₂ (sync-message i j i≠j pair x-live y-live receive send)
step-source
    (can-step
      (PS.Act-Bra i j i≠j pair x-live y-live receive send)) =
  inj₂ (sync-branch i j i≠j pair x-live y-live receive send)
step-source
    (can-step
      (PS.Act-Wait i j i≠j pair x-live y-live close₁ close₂)) =
  inj₂ (sync-close i j i≠j pair x-live y-live close₁ close₂)

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

configuration-progress-from : ∀ {n} {Γ : Ctx [] n} {C : Conf n}
  → LocalProgressTheorem
  → Γ ⊢conf C
  → Dec (RunnableAt C)
  → Dec (SynchronizationPossible C)
  → Progress C
configuration-progress-from
    local (T-Conf live-ctx paired threads) runnable? sync? =
  list-progress-conf
    (classify-list
      (threads-progress local (live-context-is-session live-ctx) threads))
    runnable?
    sync?

configuration-progress : ConfigurationProgressTheorem
configuration-progress {C = C} typing =
  configuration-progress-from
    local-progress
    typing
    (runnable-at? C)
    (synchronization-possible? C)
