module ProcTypingFresh where

import Data.Fin.Subset as Subset
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_)
import Data.Vec.Base as Vec
open import Data.Vec using () renaming (_∷_ to _∷ᵥ_)

open import Kinds using (SLin; KV; Lin; Un)
open import Types using (T-Base)
open import ExprSyntax using (Expr; NfTy)
open import ExprNormalTyping
import Duality
open import NormalTypesSubstitution using (dualNFKind)
open import ExprContextProperties public
  using
  ( AllUsed
  ; AU-∅
  ; AU-used
  ; AU-un
  )
import ProcSemanticsFresh as PSF
open PSF using (Conf; FinFreshPair; here-fwd; here-bwd; there)
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

-- The de Bruijn namespace is allocated in adjacent endpoint pairs.  A
-- binding retains its session type after it becomes used, so compatibility
-- is independent of liveness.

data SessionBinding : Binding [] → NfTy [] SLin → Set where
  SB-live : ∀ {S} → SessionBinding (B-Lin S) S
  SB-dead : ∀ {S} → SessionBinding (B-Used S) S

-- Entry 0 of each allocated pair carries S and entry 1 carries dual S.
-- An odd final entry has no FinFreshPair partner and is therefore
-- unconstrained except for being a session binding.

data PairedCtx : ∀ {n} → Ctx [] n → Set where
  PC-∅ : PairedCtx ∅

  PC-single : ∀ {b : Binding []} {S : NfTy [] SLin}
    → SessionBinding b S
    → PairedCtx (b ▻ ∅)

  PC-pair : ∀ {n} {Γ : Ctx [] n}
      {b₀ b₁ : Binding []} {S : NfTy [] SLin}
    → SessionBinding b₀ S
    → SessionBinding b₁ (dualNFKind Duality.D-S S)
    → PairedCtx Γ
    → PairedCtx (b₀ ▻ b₁ ▻ Γ)

data DualLivePair
    {n : ℕ}
    (Γ : Ctx [] n)
    (x y : Fin n) : Set where

  DLP-forward : ∀ {S : NfTy [] SLin}
    → Γ ∋ˡ x ∶ S
    → Γ ∋ˡ y ∶ dualNFKind Duality.D-S S
    → DualLivePair Γ x y

  DLP-backward : ∀ {S : NfTy [] SLin}
    → Γ ∋ˡ x ∶ dualNFKind Duality.D-S S
    → Γ ∋ˡ y ∶ S
    → DualLivePair Γ x y

lift-session-membership :
  ∀ {n pk} {Γ : Ctx [] n} {b : Binding []}
    {S : NfTy [] SLin} {T : NfTy [] (KV pk Lin)} {x : Fin n}
  → SessionBinding b S
  → Γ ∋ˡ x ∶ T
  → (b ▻ Γ) ∋ˡ fsuc x ∶ T
lift-session-membership SB-live membership = thereˡˡ membership
lift-session-membership SB-dead membership = thereˡ✖ membership

lift-dual-live-pair :
  ∀ {n} {Γ : Ctx [] n} {x y : Fin n}
    {b₀ b₁ : Binding []} {S₀ S₁ : NfTy [] SLin}
  → SessionBinding b₀ S₀
  → SessionBinding b₁ S₁
  → DualLivePair Γ x y
  → DualLivePair
      (b₀ ▻ b₁ ▻ Γ)
      (fsuc (fsuc x))
      (fsuc (fsuc y))
lift-dual-live-pair sb₀ sb₁ (DLP-forward x∈ y∈) =
  DLP-forward
    (lift-session-membership sb₀ (lift-session-membership sb₁ x∈))
    (lift-session-membership sb₀ (lift-session-membership sb₁ y∈))
lift-dual-live-pair sb₀ sb₁ (DLP-backward x∈ y∈) =
  DLP-backward
    (lift-session-membership sb₀ (lift-session-membership sb₁ x∈))
    (lift-session-membership sb₀ (lift-session-membership sb₁ y∈))

-- Every live semantic pair is represented by two available, dual session
-- bindings in the global typing context.

paired-live-endpoints :
  ∀ {n} {ss : Subset.Subset (2 + n)} {Γ : Ctx [] (2 + n)}
    {x y : Fin (2 + n)}
  → LiveCtx ss Γ
  → PairedCtx Γ
  → FinFreshPair {n} x y
  → x Subset.∈ ss
  → y Subset.∈ ss
  → DualLivePair Γ x y
paired-live-endpoints
    (LC-live (LC-live live))
    (PC-pair SB-live SB-live paired)
    here-fwd Vec.here (Vec.there Vec.here) =
  DLP-forward hereˡ (thereˡˡ hereˡ)
paired-live-endpoints
    (LC-live (LC-live live))
    (PC-pair SB-live SB-live paired)
    here-bwd (Vec.there Vec.here) Vec.here =
  DLP-backward (thereˡˡ hereˡ) hereˡ
paired-live-endpoints
    (LC-live (LC-live live))
    (PC-pair SB-live SB-live paired)
    (there pair)
    (Vec.there (Vec.there x-live))
    (Vec.there (Vec.there y-live)) =
  lift-dual-live-pair SB-live SB-live
    (paired-live-endpoints live paired pair x-live y-live)
paired-live-endpoints
    (LC-live (LC-dead live))
    (PC-pair SB-live SB-dead paired)
    here-fwd Vec.here (Vec.there ())
paired-live-endpoints
    (LC-live (LC-dead live))
    (PC-pair SB-live SB-dead paired)
    here-bwd (Vec.there ()) Vec.here
paired-live-endpoints
    (LC-live (LC-dead live))
    (PC-pair SB-live SB-dead paired)
    (there pair)
    (Vec.there (Vec.there x-live))
    (Vec.there (Vec.there y-live)) =
  lift-dual-live-pair SB-live SB-dead
    (paired-live-endpoints live paired pair x-live y-live)
paired-live-endpoints
    (LC-dead (LC-live live))
    (PC-pair SB-dead SB-live paired)
    here-fwd () (Vec.there Vec.here)
paired-live-endpoints
    (LC-dead (LC-live live))
    (PC-pair SB-dead SB-live paired)
    here-bwd (Vec.there Vec.here) ()
paired-live-endpoints
    (LC-dead (LC-live live))
    (PC-pair SB-dead SB-live paired)
    (there pair)
    (Vec.there (Vec.there x-live))
    (Vec.there (Vec.there y-live)) =
  lift-dual-live-pair SB-dead SB-live
    (paired-live-endpoints live paired pair x-live y-live)
paired-live-endpoints
    (LC-dead (LC-dead live))
    (PC-pair SB-dead SB-dead paired)
    here-fwd () y-live
paired-live-endpoints
    (LC-dead (LC-dead live))
    (PC-pair SB-dead SB-dead paired)
    here-bwd x-live ()
paired-live-endpoints
    (LC-dead (LC-dead live))
    (PC-pair SB-dead SB-dead paired)
    (there pair)
    (Vec.there (Vec.there x-live))
    (Vec.there (Vec.there y-live)) =
  lift-dual-live-pair SB-dead SB-dead
    (paired-live-endpoints live paired pair x-live y-live)

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
-- `LiveCtx` premise rules out use of dead channels, `PairedCtx` relates each
-- allocated endpoint pair by duality, and `ThreadsTyped` partitions every
-- live channel among the expressions and consumes it exactly once.

data _⊢conf_ : ∀ {n} → Ctx [] n → Conf n → Set where
  T-Conf : ∀ {n} {Γ : Ctx [] n} {C : Conf n}
    → LiveCtx (live C) Γ
    → PairedCtx Γ
    → ThreadsTyped Γ (exps C)
    → Γ ⊢conf C
