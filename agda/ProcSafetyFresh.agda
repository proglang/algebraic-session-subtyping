module ProcSafetyFresh where

open import Data.Fin.Subset as Subset using ()
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _+_)

open import ExprSyntax using (Expr)
open import ExprNormalTyping using
  ( Ctx
  ; ∅
  ; unitConstNf
  ; _⊢_⇐_⊣_
  )
open import ProcSemanticsFresh using
  ( Conf
  ; ConfLabel
  ; _—conf[_]→_
  )
open import ProcTypingFresh using
  ( AU-∅
  ; LC-∅
  ; PC-∅
  ; S-∅
  ; TT-[]
  ; TT-∷
  ; T-Conf
  ; _⊢conf_
  )
open import ProcProgressFreshDefinitions using (Progress)
open import ProcProgressFresh using (configuration-progress)
open import ProcReductionPreservationFresh using
  ( PreservationResult
  ; configuration-reduction-preserves-typing
  )

------------------------------------------------------------------------
-- Heterogeneous finite configuration reduction

-- The target namespace may be larger than the source namespace because an
-- Act-New step allocates two fresh channel endpoints.

infix 4 _—conf→*_

data _—conf→*_ : ∀ {n m} → Conf n → Conf m → Set where
  trace-refl : ∀ {n} {C : Conf n}
    → C —conf→* C

  trace-step : ∀ {n k m}
      {C : Conf n}
      {π : ConfLabel n k}
      {C₁ : Conf (k + n)}
      {C₂ : Conf m}
    → C —conf[ π ]→ C₁
    → C₁ —conf→* C₂
    → C —conf→* C₂

------------------------------------------------------------------------
-- Preservation and progress at every finitely reachable endpoint

finite-reduction-preserves-typing :
  ∀ {n m} {Γ : Ctx [] n} {C : Conf n} {C′ : Conf m}
  → Γ ⊢conf C
  → C —conf→* C′
  → PreservationResult C′
finite-reduction-preserves-typing typing trace-refl =
  record
    { Γ′ = _
    ; typing = typing
    }
finite-reduction-preserves-typing typing (trace-step step trace)
  with configuration-reduction-preserves-typing typing step
... | record { Γ′ = Γ′ ; typing = typing′ } =
  finite-reduction-preserves-typing typing′ trace

finite-reduction-progress :
  ∀ {n m} {Γ : Ctx [] n} {C : Conf n} {C′ : Conf m}
  → Γ ⊢conf C
  → C —conf→* C′
  → Progress C′
finite-reduction-progress typing trace
  with finite-reduction-preserves-typing typing trace
... | record { Γ′ = Γ′ ; typing = typing′ } =
  configuration-progress typing′

------------------------------------------------------------------------
-- End-to-end safety for one closed unit-typed expression

singleton : Expr [] 0 → Conf 0
singleton e = record
  { exps = e ∷ []
  ; live = Subset.⊥
  }

singleton-typed :
  ∀ {e : Expr [] 0}
  → ∅ ⊢ e ⇐ unitConstNf ⊣ ∅
  → ∅ ⊢conf singleton e
singleton-typed typing =
  T-Conf
    LC-∅
    PC-∅
    (TT-∷ S-∅ typing AU-∅ (TT-[] AU-∅))

-- `Progress C′` is precisely the terminal/deadlocked/can-step trichotomy
-- from ProcProgressFreshDefinitions.  The theorem applies after every
-- finite trace, including traces containing any number of allocations.

closed-unit-finite-progress :
  ∀ {m} {e : Expr [] 0} {C′ : Conf m}
  → ∅ ⊢ e ⇐ unitConstNf ⊣ ∅
  → singleton e —conf→* C′
  → Progress C′
closed-unit-finite-progress typing trace =
  finite-reduction-progress (singleton-typed typing) trace
