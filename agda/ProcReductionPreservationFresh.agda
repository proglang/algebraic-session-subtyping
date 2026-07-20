module ProcReductionPreservationFresh where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset as Subset using (Subset)
open import Data.List as L using (List; []; _∷_; length; lookup; removeAt; map)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Binary.Permutation.Propositional as Perm using
  (_↭_; refl; prep; swap; trans; ↭-sym)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; _×_; _,_)
open import Function using (const)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)

open import Kinds using (SLin)
import Duality
open import Types using (Ty; T-Base; T-Dual)
open import ExprSyntax using (Expr; Value; C-Unit; E-App; E-Val; V-Const)
open import ExprNormalTyping
import ExprContextProperties as ECP
open import ExprContextProperties using
  ( FrameCtx
  ; FC-∅
  ; FC-allused
  ; FC-live
  ; FC-frame
  ; FC-un
  ; RemoveCtx
  ; RM-∅
  ; RM-drop
  ; RM-allused
  ; RM-lin
  ; RM-un
  ; allUsedCtx
  ; allUsedCtx-AllUsed
  )
open import ExprContextReduction using
  ( _⦂_⇒_
  ; Extract
  ; Label-Fork
  ; Ex-Fork
  ; Ctx-Fork
  ; Frm-Fork
  ; Label-New
  ; Ex-New
  ; Ctx-New
  ; Frm-New
  )
open import ExprSubstitutionPreservationFresh using
  ( _≈ᵘ_
  ; ≈ᵘ-∅
  ; ≈ᵘ-lin
  ; ≈ᵘ-un
  ; ≈ᵘ-used
  ; ≈ᵘ-sym
  ; CheckResult
  ; retag-check-input
  ; allUsed-resp-≈ᵘ
  )
open import ExprReductionPreservationFresh using
  ( beta-reduction-preserves-check
  ; reduction-preserves-check
  ; ReductionCheckResult
  ; remove-to-rest-frame
  ; new-weaken-check-at
  )
open import ExprSemantics using
  ( Label
  ; L-β
  ; L-Fork
  ; L-New
  ; _—[_]→_
  ; weakenExprBy
  )
open import AlgorithmicNFSubtyping using (<:ₜ-refl)
open import ExprTypingStrengthening using
  ( arrow-subtype-inversion
  ; check-subsumption
  )
import ProcSemanticsFresh as PSF
open PSF using
  ( Conf
  ; ConfLabel
  ; C-τ
  ; C-new
  ; _—conf[_]→_
  )
open PSF.Conf using (exps; live)
open import ProcTypingFresh

------------------------------------------------------------------------
-- Structural facts about declarative thread pools

split-to-frame :
  ∀ {Δ n} {Γ Γ₁ Γ₂ : Ctx Δ n}
  → Split Γ Γ₁ Γ₂
  → FrameCtx Γ₁ Γ₂ Γ
split-to-frame S-∅ = FC-∅
split-to-frame (S-Linˡ sp) = FC-frame (split-to-frame sp)
split-to-frame (S-Linʳ sp) = FC-live (split-to-frame sp)
split-to-frame (S-Un sp) = FC-un (split-to-frame sp)
split-to-frame (S-Used sp) = FC-allused (split-to-frame sp)

frame-to-split :
  ∀ {Δ n} {Γ Γ₁ Γ₂ : Ctx Δ n}
  → FrameCtx Γ₁ Γ₂ Γ
  → Split Γ Γ₁ Γ₂
frame-to-split FC-∅ = S-∅
frame-to-split (FC-allused f) = S-Used (frame-to-split f)
frame-to-split (FC-live f) = S-Linʳ (frame-to-split f)
frame-to-split (FC-frame f) = S-Linˡ (frame-to-split f)
frame-to-split (FC-un f) = S-Un (frame-to-split f)

ctx-allused-disjoint :
  ∀ {Δ n} (Γ : Ctx Δ n)
  → ECP.LinearDisjoint Γ (allUsedCtx Γ)
ctx-allused-disjoint ∅ = ECP.LD-∅
ctx-allused-disjoint (B-Lin _ ▻ Γ) =
  ECP.LD-live-used (ctx-allused-disjoint Γ)
ctx-allused-disjoint (B-Un _ ▻ Γ) =
  ECP.LD-un-un (ctx-allused-disjoint Γ)
ctx-allused-disjoint (B-Used _ ▻ Γ) =
  ECP.LD-used-used (ctx-allused-disjoint Γ)

-- Exchange two removals.  This is the pointwise resource fact used by fork:
-- the expression frame can be removed before the forked closure, or after it.

remove-exchange :
  ∀ {Δ n} {Γ₀ F A V B Γ₁ : Ctx Δ n}
  → RemoveCtx Γ₀ F A
  → RemoveCtx A V B
  → RemoveCtx Γ₁ F B
  → RemoveCtx Γ₀ V Γ₁
remove-exchange RM-∅ RM-∅ RM-∅ = RM-∅
remove-exchange (RM-drop rF) (RM-drop rV) (RM-drop rF′) =
  RM-drop (remove-exchange rF rV rF′)
remove-exchange (RM-drop rF) (RM-lin rV) (RM-allused rF′) =
  RM-lin (remove-exchange rF rV rF′)
remove-exchange (RM-lin rF) (RM-allused rV) (RM-lin rF′) =
  RM-drop (remove-exchange rF rV rF′)
remove-exchange (RM-allused rF) (RM-allused rV) (RM-allused rF′) =
  RM-allused (remove-exchange rF rV rF′)
remove-exchange (RM-un rF) (RM-un rV) (RM-un rF′) =
  RM-un (remove-exchange rF rV rF′)

remove-source-unique :
  ∀ {Δ n} {Γ₁ Γ₂ G R : Ctx Δ n}
  → RemoveCtx Γ₁ G R
  → RemoveCtx Γ₂ G R
  → Γ₁ ≡ Γ₂
remove-source-unique RM-∅ RM-∅ = refl
remove-source-unique (RM-drop r₁) (RM-drop r₂) =
  cong (_ ▻_) (remove-source-unique r₁ r₂)
remove-source-unique (RM-allused r₁) (RM-allused r₂) =
  cong (_ ▻_) (remove-source-unique r₁ r₂)
remove-source-unique (RM-lin r₁) (RM-lin r₂) =
  cong (_ ▻_) (remove-source-unique r₁ r₂)
remove-source-unique (RM-un r₁) (RM-un r₂) =
  cong (_ ▻_) (remove-source-unique r₁ r₂)

split-expand-left :
  ∀ {Δ n} {Γ AB C A B : Ctx Δ n}
  → Split Γ AB C
  → Split AB A B
  → Σ (Ctx Δ n) λ AC →
      Split Γ B AC × Split AC A C
split-expand-left S-∅ S-∅ = ∅ , S-∅ , S-∅
split-expand-left (S-Linˡ outer) (S-Linˡ inner)
  with split-expand-left outer inner
... | AC , first , second =
  _ , S-Linʳ first , S-Linˡ second
split-expand-left (S-Linˡ outer) (S-Linʳ inner)
  with split-expand-left outer inner
... | AC , first , second =
  _ , S-Linˡ first , S-Used second
split-expand-left (S-Linʳ outer) (S-Used inner)
  with split-expand-left outer inner
... | AC , first , second =
  _ , S-Linʳ first , S-Linʳ second
split-expand-left (S-Un outer) (S-Un inner)
  with split-expand-left outer inner
... | AC , first , second =
  _ , S-Un first , S-Un second
split-expand-left (S-Used outer) (S-Used inner)
  with split-expand-left outer inner
... | AC , first , second =
  _ , S-Used first , S-Used second

split-retag :
  ∀ {Δ n} {Γ Γ′ A B : Ctx Δ n}
  → Γ ≈ᵘ Γ′
  → Split Γ A B
  → Σ (Ctx Δ n) λ A′ →
      Σ (Ctx Δ n) λ B′ →
        Split Γ′ A′ B′ × (A ≈ᵘ A′) × (B ≈ᵘ B′)
split-retag ≈ᵘ-∅ S-∅ = ∅ , ∅ , S-∅ , ≈ᵘ-∅ , ≈ᵘ-∅
split-retag (≈ᵘ-lin eq) (S-Linˡ split)
  with split-retag eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Linˡ split′ , ≈ᵘ-lin eqA , ≈ᵘ-used eqB
split-retag (≈ᵘ-lin eq) (S-Linʳ split)
  with split-retag eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Linʳ split′ , ≈ᵘ-used eqA , ≈ᵘ-lin eqB
split-retag (≈ᵘ-un eq) (S-Un split)
  with split-retag eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Un split′ , ≈ᵘ-un eqA , ≈ᵘ-un eqB
split-retag (≈ᵘ-used eq) (S-Used split)
  with split-retag eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Used split′ , ≈ᵘ-used eqA , ≈ᵘ-used eqB

threads-retag :
  ∀ {n} {Γ Γ′ : Ctx [] n} {es : List (Expr [] n)}
  → Γ ≈ᵘ Γ′
  → ThreadsTyped Γ es
  → ThreadsTyped Γ′ es
threads-retag eq (TT-[] au) =
  TT-[] (allUsed-resp-≈ᵘ eq au)
threads-retag eq (TT-∷ split d au rest)
  with split-retag eq split
... | A′ , B′ , split′ , eqA , eqB
  with retag-check-input d eqA
... | Aout′ , d′ , out-eq =
  TT-∷
    split′
    d′
    (allUsed-resp-≈ᵘ (≈ᵘ-sym out-eq) au)
    (threads-retag eqB rest)

-- Reassociate two consecutive allocations so that the second thread is
-- allocated first.  This is the context-level content of swapping adjacent
-- threads.

split-swap-nested :
  ∀ {Δ n} {Γ Γ₁ Γ₂… Γ₂ Γ₃ : Ctx Δ n}
  → Split Γ Γ₁ Γ₂…
  → Split Γ₂… Γ₂ Γ₃
  → Σ (Ctx Δ n) λ Γ₁… →
      Split Γ Γ₂ Γ₁… × Split Γ₁… Γ₁ Γ₃
split-swap-nested S-∅ S-∅ = ∅ , S-∅ , S-∅
split-swap-nested (S-Linˡ sp₁) (S-Used sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , out , inner =
  _ , S-Linʳ out , S-Linˡ inner
split-swap-nested (S-Linʳ sp₁) (S-Linˡ sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , out , inner =
  _ , S-Linˡ out , S-Used inner
split-swap-nested (S-Linʳ sp₁) (S-Linʳ sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , out , inner =
  _ , S-Linʳ out , S-Linʳ inner
split-swap-nested (S-Un sp₁) (S-Un sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , out , inner =
  _ , S-Un out , S-Un inner
split-swap-nested (S-Used sp₁) (S-Used sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , out , inner =
  _ , S-Used out , S-Used inner

threads-swap :
  ∀ {n} {Γ : Ctx [] n} {e₁ e₂ : Expr [] n} {es : List (Expr [] n)}
  → ThreadsTyped Γ (e₁ ∷ e₂ ∷ es)
  → ThreadsTyped Γ (e₂ ∷ e₁ ∷ es)
threads-swap
    (TT-∷ split₁ d₁ au₁ (TT-∷ split₂ d₂ au₂ rest))
  with split-swap-nested split₁ split₂
... | Γ₁… , split₂′ , split₁′ =
  TT-∷ split₂′ d₂ au₂ (TT-∷ split₁′ d₁ au₁ rest)

threads-resp-↭ :
  ∀ {n} {Γ : Ctx [] n} {es es′ : List (Expr [] n)}
  → es ↭ es′
  → ThreadsTyped Γ es
  → ThreadsTyped Γ es′
threads-resp-↭ refl typed = typed
threads-resp-↭ (prep e permutation)
    (TT-∷ split d au rest) =
  TT-∷ split d au (threads-resp-↭ permutation rest)
threads-resp-↭ (swap e₁ e₂ permutation) typed
  with threads-swap typed
... | TT-∷ split₂ d₂ au₂ (TT-∷ split₁ d₁ au₁ rest) =
  TT-∷ split₂ d₂ au₂
    (TT-∷ split₁ d₁ au₁
      (threads-resp-↭ permutation rest))
threads-resp-↭ (trans p q) typed =
  threads-resp-↭ q (threads-resp-↭ p typed)

lookup-front :
  ∀ {A : Set} (xs : List A) (i : Fin (length xs))
  → xs ↭ lookup xs i ∷ removeAt xs i
lookup-front (x ∷ xs) fzero = refl
lookup-front (x ∷ xs) (fsuc i) =
  trans
    (prep x (lookup-front xs i))
    (swap x (lookup xs i) refl)

updateAt-front :
  ∀ {A : Set} (xs : List A) (i : Fin (length xs)) (x′ : A)
  → L.updateAt xs i (const x′) ↭ x′ ∷ removeAt xs i
updateAt-front (x ∷ xs) fzero x′ = refl
updateAt-front (x ∷ xs) (fsuc i) x′ =
  trans
    (prep x (updateAt-front xs i x′))
    (swap x x′ refl)

subst-Fin-zero-sym-cong :
  ∀ {m n} (p : m ≡ n)
  → subst Fin (sym (cong Data.Nat.suc p)) fzero ≡ fzero
subst-Fin-zero-sym-cong refl = refl

subst-Fin-suc-sym-cong :
  ∀ {m n} (p : m ≡ n) (i : Fin n)
  → subst Fin (sym (cong Data.Nat.suc p)) (fsuc i)
      ≡ fsuc (subst Fin (sym p) i)
subst-Fin-suc-sym-cong refl i = refl

map-updateAt-front :
  ∀ {A B : Set} (f : A → B) (xs : List A)
    (i : Fin (length xs)) (y : B)
  → L.updateAt (map f xs)
      (subst Fin (sym (length-map f xs)) i)
      (const y)
      ↭ y ∷ map f (removeAt xs i)
map-updateAt-front f (x ∷ xs) fzero y
  rewrite subst-Fin-zero-sym-cong (length-map f xs) = refl
map-updateAt-front f (x ∷ xs) (fsuc i) y
  rewrite subst-Fin-suc-sym-cong (length-map f xs) i =
  trans
    (prep (f x) (map-updateAt-front f xs i y))
    (swap (f x) y refl)

removeTwo :
  ∀ {A : Set} (xs : List A)
  → (i j : Fin (length xs))
  → i ≢ j
  → List A
removeTwo (x ∷ xs) fzero fzero i≠j = ⊥-elim (i≠j refl)
removeTwo (x ∷ xs) fzero (fsuc j) i≠j = removeAt xs j
removeTwo (x ∷ xs) (fsuc i) fzero i≠j = removeAt xs i
removeTwo (x ∷ xs) (fsuc i) (fsuc j) i≠j =
  x ∷ removeTwo xs i j (λ eq → i≠j (cong fsuc eq))

two-front :
  ∀ {A : Set} (xs : List A)
    (i j : Fin (length xs)) (i≠j : i ≢ j)
  → xs ↭
      lookup xs i ∷ lookup xs j ∷ removeTwo xs i j i≠j
two-front (x ∷ xs) fzero fzero i≠j = ⊥-elim (i≠j refl)
two-front (x ∷ xs) fzero (fsuc j) i≠j =
  prep x (lookup-front xs j)
two-front (x ∷ xs) (fsuc i) fzero i≠j =
  trans
    (prep x (lookup-front xs i))
    (swap x (lookup xs i) refl)
two-front (x ∷ xs) (fsuc i) (fsuc j) i≠j =
  let
    tail = two-front xs i j (λ eq → i≠j (cong fsuc eq))
  in
  trans
    (prep x tail)
    (trans
      (swap x (lookup xs i) refl)
      (prep (lookup xs i) (swap x (lookup xs j) refl)))

doubleUpdateAt :
  ∀ {A : Set} (xs : List A)
  → Fin (length xs)
  → Fin (length xs)
  → A → A → List A
doubleUpdateAt xs i j x′ y′ =
  let xs′ = L.updateAt xs i (const x′)
  in L.updateAt xs′
      (subst Fin (sym (PSF.length-updateAt xs i)) j)
      (const y′)

double-update-front :
  ∀ {A : Set} (xs : List A)
    (i j : Fin (length xs)) (i≠j : i ≢ j) (x′ y′ : A)
  → doubleUpdateAt xs i j x′ y′
      ↭ x′ ∷ y′ ∷ removeTwo xs i j i≠j
double-update-front (x ∷ xs) fzero fzero i≠j x′ y′ =
  ⊥-elim (i≠j refl)
double-update-front (x ∷ xs) fzero (fsuc j) i≠j x′ y′ =
  prep x′ (updateAt-front xs j y′)
double-update-front (x ∷ xs) (fsuc i) fzero i≠j x′ y′ =
  subst
    (λ index →
      L.updateAt (x ∷ L.updateAt xs i (const x′)) index (const y′)
        ↭ x′ ∷ y′ ∷ removeAt xs i)
    (sym (subst-Fin-zero-sym-cong (PSF.length-updateAt xs i)))
    (trans
      (prep y′ (updateAt-front xs i x′))
      (swap y′ x′ refl))
double-update-front (x ∷ xs) (fsuc i) (fsuc j) i≠j x′ y′ =
  subst
    (λ index →
      L.updateAt (x ∷ L.updateAt xs i (const x′)) index (const y′)
        ↭ x′ ∷ y′ ∷
          x ∷ removeTwo xs i j (λ eq → i≠j (cong fsuc eq)))
    (sym (subst-Fin-suc-sym-cong (PSF.length-updateAt xs i) j))
    (let
      tail = double-update-front xs i j
        (λ eq → i≠j (cong fsuc eq)) x′ y′
    in
    trans
      (prep x tail)
      (trans
        (swap x x′ refl)
        (prep x′ (swap x y′ refl))))

------------------------------------------------------------------------
-- Preservation statement and the internal beta case

record PreservationResult
    {n : ℕ}
    (C′ : Conf n) : Set where
  field
    Γ′ : Ctx [] n
    typing : Γ′ ⊢conf C′

beta-head-preserves :
  ∀ {n} {Γ : Ctx [] n} {e e′ : Expr [] n} {es : List (Expr [] n)}
  → e —[ L-β ]→ e′
  → ThreadsTyped Γ (e ∷ es)
  → ThreadsTyped Γ (e′ ∷ es)
beta-head-preserves step (TT-∷ split d au rest)
  with beta-reduction-preserves-check step d
... | result =
  TT-∷
    split
    (CheckResult.derivation result)
    (allUsed-resp-≈ᵘ (≈ᵘ-sym (CheckResult.leftover result)) au)
    rest

act-beta-preserves :
  ∀ {n} {Γ : Ctx [] n} {C : Conf n}
    {i : Fin (length (exps C))} {e′ : Expr [] n}
  → Γ ⊢conf C
  → PSF.Conf.lookup C i —[ L-β ]→ e′
  → Γ ⊢conf PSF.Conf.updateAt C i (const e′)
act-beta-preserves (T-Conf live-ok threads) step =
  T-Conf live-ok
    (threads-resp-↭
      (↭-sym (updateAt-front _ _ _))
      (beta-head-preserves step
        (threads-resp-↭ (lookup-front _ _) threads)))

fork-head-preserves :
  ∀ {n} {Γ : Ctx [] n} {e e′ : Expr [] n} {v : Value [] n}
    {es : List (Expr [] n)}
  → e —[ L-Fork v ]→ e′
  → ThreadsTyped Γ (e ∷ es)
  → ThreadsTyped Γ
      (E-App (E-Val v) (E-Val (V-Const C-Unit)) ∷ e′ ∷ es)
fork-head-preserves step (TT-∷ outer source source-au rest)
  with reduction-preserves-check
         step source
         (Label-Fork
           (allUsedCtx-AllUsed _)
           (allUsedCtx-AllUsed _))
         Ex-Fork
         (ctx-allused-disjoint _)
... | record
        { src-remove = src-remove
        ; frame-update = Frm-Fork
        ; dst-remove = dst-remove
        ; ctx-step = Ctx-Fork closure-remove closure-check closure-au
        ; check = reduct
        ; leftover = reduct-leftover
        }
  with remove-exchange src-remove closure-remove dst-remove
... | closure-remove-full
  with split-expand-left
         outer
         (frame-to-split (remove-to-rest-frame closure-remove-full))
... | after-closure , split-closure , split-reduct
  with closure-check
... | T-Check closure-synth closure-sub
  with arrow-subtype-inversion closure-sub
... | A , U , closure-type , unit<:A , U<:unit =
  TT-∷
    split-closure
    (T-Check
      (T-App
        (subst
          (λ X → _ ⊢ E-Val _ ⇒ X ⊣ _)
          closure-type
          closure-synth)
        (check-subsumption
          (T-Check
            (T-Val (TV-Const CT-Unit))
            (<:ₜ-refl (normalTyOf unitConstNf)))
          unit<:A))
      U<:unit)
    closure-au
    (TT-∷
      split-reduct
      reduct
      (allUsed-resp-≈ᵘ (≈ᵘ-sym reduct-leftover) source-au)
      rest)

act-fork-preserves :
  ∀ {n} {Γ : Ctx [] n} {C : Conf n}
    {i : Fin (length (exps C))} {e′ : Expr [] n} {v : Value [] n}
  → Γ ⊢conf C
  → PSF.Conf.lookup C i —[ L-Fork v ]→ e′
  → Γ ⊢conf
      PSF.Conf.add
        (PSF.Conf.updateAt C i (const e′))
        (E-App (E-Val v) (E-Val (V-Const C-Unit)))
act-fork-preserves (T-Conf live-ok threads) step =
  T-Conf live-ok
    (threads-resp-↭
      (prep _ (↭-sym (updateAt-front _ _ _)))
      (fork-head-preserves step
        (threads-resp-↭ (lookup-front _ _) threads)))

new-weaken-threads :
  ∀ {n} (S : Ty [] SLin) {Γ : Ctx [] n} {es : List (Expr [] n)}
  → ThreadsTyped Γ es
  → ThreadsTyped
      (B-Used (normalizeTy S) ▻
       B-Used (normalizeTy (T-Dual Duality.D-S S)) ▻ Γ)
      (map (weakenExprBy 2) es)
new-weaken-threads S (TT-[] au) =
  TT-[] (AU-used (AU-used au))
new-weaken-threads S (TT-∷ split d au rest) =
  TT-∷
    (S-Used (S-Used split))
    (new-weaken-check-at 0 S d)
    (AU-used (AU-used au))
    (new-weaken-threads S rest)

new-head-preserves :
  ∀ {n} {Γ : Ctx [] n} {e : Expr [] n}
    {e′ : Expr [] (2 + n)} {S : Ty [] SLin} {es : List (Expr [] n)}
  → e —[ L-New S ]→ e′
  → ThreadsTyped Γ (e ∷ es)
  → ThreadsTyped
      (B-Lin (normalizeTy S) ▻
       B-Lin (normalizeTy (T-Dual Duality.D-S S)) ▻ Γ)
      (e′ ∷ map (weakenExprBy 2) es)
new-head-preserves {S = S} step (TT-∷ outer source source-au rest)
  with reduction-preserves-check
         step source
         (Label-New
           (allUsedCtx-AllUsed _)
           (allUsedCtx-AllUsed _))
         Ex-New
         (ctx-allused-disjoint _)
... | record
        { Γ₁ = target-input
        ; src-remove = src-remove
        ; frame-update = Frm-New
        ; dst-remove = dst-remove
        ; ctx-step = Ctx-New
        ; check = reduct
        ; leftover = reduct-leftover
        } =
  let
    target-input-eq =
      remove-source-unique
        dst-remove
        (RM-drop (RM-drop src-remove))

    reduct′ =
      subst
        (λ X → X ⊢ _ ⇐ normalizeTy T-Base ⊣ _)
        target-input-eq
        reduct
  in
  TT-∷
    (S-Linˡ (S-Linˡ outer))
    reduct′
    (allUsed-resp-≈ᵘ
      (≈ᵘ-sym reduct-leftover)
      (AU-used (AU-used source-au)))
    (new-weaken-threads S rest)

act-new-preserves :
  ∀ {n} {Γ : Ctx [] n} {C : Conf n}
    {i : Fin (length (exps C))} {e′ : Expr [] (2 + n)}
    {S : Ty [] SLin}
  → Γ ⊢conf C
  → PSF.Conf.lookup C i —[ L-New S ]→ e′
  → (B-Lin (normalizeTy S) ▻
      B-Lin (normalizeTy (T-Dual Duality.D-S S)) ▻ Γ)
      ⊢conf
      PSF.Conf.updateAt
        (PSF.activateFreshPair C)
        (subst Fin (sym (length-map _ (exps C))) i)
        (const e′)
act-new-preserves (T-Conf live-ok threads) step =
  T-Conf
    (LC-live (LC-live live-ok))
    (threads-resp-↭
      (↭-sym (map-updateAt-front (weakenExprBy 2) _ _ _))
      (new-head-preserves step
        (threads-resp-↭ (lookup-front _ _) threads)))

------------------------------------------------------------------------
-- Typed synchronization

-- `LiveCtx` deliberately enforces liveness and linear ownership only; it
-- does not say that the two ends of a fresh pair carry compatible session
-- types.  That missing coherence is exactly what is needed to type a value
-- transferred from the sending thread in the receiving thread.  The
-- following witness isolates that assumption.  It contains label typing and
-- extraction evidence for both expression actions, plus only the
-- context-level fact that their two target contexts and the retagged passive
-- pool still form a live configuration.  It does not contain target
-- expression typing; that is derived below from expression preservation.

data BinaryCompatibility
    {n : ℕ}
    {Γ : Ctx [] n}
    {e₁ e₂ e₁′ e₂′ : Expr [] n}
    {es : List (Expr [] n)}
    {ℓ₁ ℓ₂ : Label n []}
    {live′ : Subset n}
    (step₁ : e₁ —[ ℓ₁ ]→ e₁′)
    (step₂ : e₂ —[ ℓ₂ ]→ e₂′)
  : ThreadsTyped Γ (e₁ ∷ e₂ ∷ es) → Set where

  binary-compatible :
    ∀ {Γ₁ Γ₂… Γ₂ Γrest Γ₁out Γ₂out : Ctx [] n}
      {split₁ : Split Γ Γ₁ Γ₂…}
      {check₁ : Γ₁ ⊢ e₁ ⇐ normalizeTy T-Base ⊣ Γ₁out}
      {used₁ : AllUsed Γ₁out}
      {split₂ : Split Γ₂… Γ₂ Γrest}
      {check₂ : Γ₂ ⊢ e₂ ⇐ normalizeTy T-Base ⊣ Γ₂out}
      {used₂ : AllUsed Γ₂out}
      {rest : ThreadsTyped Γrest es}
      {Γin₁ Γv₁ Γin₂ Γv₂ : Ctx [] n}
      (lbl₁ : ℓ₁ ⦂ Γin₁ ⇒ Γv₁)
      (extract₁ : Extract Γ₁ ℓ₁ Γin₁)
      (disjoint₁ : ECP.LinearDisjoint Γ₁ Γv₁)
      (lbl₂ : ℓ₂ ⦂ Γin₂ ⇒ Γv₂)
      (extract₂ : Extract Γ₂ ℓ₂ Γin₂)
      (disjoint₂ : ECP.LinearDisjoint Γ₂ Γv₂)
      (assemble :
        (result₁ :
          ReductionCheckResult
            Γin₁ Γv₁ lbl₁ Γ₁ Γ₁out e₁′ (normalizeTy T-Base))
        → (result₂ :
          ReductionCheckResult
            Γin₂ Γv₂ lbl₂ Γ₂ Γ₂out e₂′ (normalizeTy T-Base))
        → Σ (Ctx [] n) λ Γ′ →
            Σ (Ctx [] n) λ Γ₂…′ →
              Σ (Ctx [] n) λ Γrest′ →
                LiveCtx live′ Γ′
                × Split Γ′ (ReductionCheckResult.Γ₁ result₁) Γ₂…′
                × Split Γ₂…′
                    (ReductionCheckResult.Γ₁ result₂) Γrest′
                × (Γrest ≈ᵘ Γrest′))
    → BinaryCompatibility step₁ step₂
        (TT-∷ split₁ check₁ used₁
          (TT-∷ split₂ check₂ used₂ rest))

binary-head-preserves :
  ∀ {n} {Γ : Ctx [] n}
    {e₁ e₂ e₁′ e₂′ : Expr [] n} {es : List (Expr [] n)}
    {ℓ₁ ℓ₂ : Label n []} {live′ : Subset n}
    {step₁ : e₁ —[ ℓ₁ ]→ e₁′} {step₂ : e₂ —[ ℓ₂ ]→ e₂′}
    {typed : ThreadsTyped Γ (e₁ ∷ e₂ ∷ es)}
  → BinaryCompatibility {live′ = live′} step₁ step₂ typed
  → Σ (Ctx [] n) λ Γ′ →
      LiveCtx live′ Γ′ × ThreadsTyped Γ′ (e₁′ ∷ e₂′ ∷ es)
binary-head-preserves
    {step₁ = step₁} {step₂ = step₂}
    (binary-compatible
      {check₁ = check₁} {used₁ = used₁}
      {check₂ = check₂} {used₂ = used₂}
      {rest = rest}
      lbl₁ extract₁ disjoint₁
      lbl₂ extract₂ disjoint₂ assemble)
  with reduction-preserves-check
         step₁ check₁ lbl₁ extract₁ disjoint₁
... | result₁
  with reduction-preserves-check
         step₂ check₂ lbl₂ extract₂ disjoint₂
... | result₂
  with assemble result₁ result₂
... | Γ′ , Γ₂…′ , Γrest′ , live-ok , split₁′ , split₂′ , rest-eq =
  Γ′ , live-ok ,
  TT-∷
    split₁′
    (ReductionCheckResult.check result₁)
    (allUsed-resp-≈ᵘ
      (≈ᵘ-sym (ReductionCheckResult.leftover result₁)) used₁)
    (TT-∷
      split₂′
      (ReductionCheckResult.check result₂)
      (allUsed-resp-≈ᵘ
        (≈ᵘ-sym (ReductionCheckResult.leftover result₂)) used₂)
      (threads-retag rest-eq rest))

-- A typed reduction is an ordinary `ProcSemanticsFresh` reduction.  The
-- three internal rules need no extra evidence.  A synchronization rule also
-- carries `BinaryCompatibility`, because the current `LiveCtx` judgment does
-- not itself impose dual/compatible types on paired endpoints.

data ReductionTyping :
    ∀ {n k} {Γ : Ctx [] n} {C : Conf n}
      {π : ConfLabel n k} {C′ : Conf (k + n)}
    → Γ ⊢conf C
    → C —conf[ π ]→ C′
    → Set where

  RT-Beta :
    ∀ {n} {Γ : Ctx [] n} {C : Conf n}
      {typing : Γ ⊢conf C}
      {i : Fin (length (exps C))} {e′ : Expr [] n}
      {step : PSF.Conf.lookup C i —[ L-β ]→ e′}
    → ReductionTyping typing (PSF.Act-Beta step)

  RT-Fork :
    ∀ {n} {Γ : Ctx [] n} {C : Conf n}
      {typing : Γ ⊢conf C}
      {i : Fin (length (exps C))} {e′ : Expr [] n} {v : Value [] n}
      {step : PSF.Conf.lookup C i —[ L-Fork v ]→ e′}
    → ReductionTyping typing (PSF.Act-Fork step)

  RT-New :
    ∀ {n} {Γ : Ctx [] n} {C : Conf n}
      {typing : Γ ⊢conf C}
      {i : Fin (length (exps C))} {e′ : Expr [] (2 + n)}
      {S : Ty [] SLin}
      {step : PSF.Conf.lookup C i —[ L-New S ]→ e′}
    → ReductionTyping typing (PSF.Act-New step)

  RT-Msg :
    ∀ {n} {Γ : Ctx [] (2 + n)} {C : Conf (2 + n)}
      {i j : Fin (length (exps C))} {i≠j : i ≢ j}
      {x y : Fin (2 + n)} {e₁ e₂ : Expr [] (2 + n)}
      {v : Value [] (2 + n)}
      {pair : PSF.FinFreshPair {n} x y}
      {x-live : x Subset.∈ live C} {y-live : y Subset.∈ live C}
      {recv : PSF.Conf.lookup C i —[ ExprSemantics.L-RecvVal x v ]→ e₁}
      {send : PSF.Conf.lookup C j —[ ExprSemantics.L-SendVal y v ]→ e₂}
      {live-ok : LiveCtx (live C) Γ}
      {threads : ThreadsTyped Γ (exps C)}
    → BinaryCompatibility {live′ = live C} recv send
        (threads-resp-↭ (two-front (exps C) i j i≠j) threads)
    → ReductionTyping
        (T-Conf live-ok threads)
        (PSF.Act-Msg {i≠j = i≠j} pair x-live y-live recv send)

  RT-Bra :
    ∀ {n k} {Γ : Ctx [] (2 + n)} {C : Conf (2 + n)}
      {i j : Fin (length (exps C))} {i≠j : i ≢ j}
      {x y : Fin (2 + n)} {ℓ : Fin k}
      {e₁ e₂ : Expr [] (2 + n)}
      {pair : PSF.FinFreshPair {n} x y}
      {x-live : x Subset.∈ live C} {y-live : y Subset.∈ live C}
      {recv : PSF.Conf.lookup C i —[ ExprSemantics.L-RecvLab x ℓ ]→ e₁}
      {send : PSF.Conf.lookup C j —[ ExprSemantics.L-SendLab y ℓ ]→ e₂}
      {live-ok : LiveCtx (live C) Γ}
      {threads : ThreadsTyped Γ (exps C)}
    → BinaryCompatibility {live′ = live C} recv send
        (threads-resp-↭ (two-front (exps C) i j i≠j) threads)
    → ReductionTyping
        (T-Conf live-ok threads)
        (PSF.Act-Bra {i≠j = i≠j} pair x-live y-live recv send)

  RT-Wait :
    ∀ {n} {Γ : Ctx [] (2 + n)} {C : Conf (2 + n)}
      {i j : Fin (length (exps C))} {i≠j : i ≢ j}
      {x y : Fin (2 + n)} {e₁ e₂ : Expr [] (2 + n)}
      {pair : PSF.FinFreshPair {n} x y}
      {x-live : x Subset.∈ live C} {y-live : y Subset.∈ live C}
      {close₁ : PSF.Conf.lookup C i —[ ExprSemantics.L-Close x ]→ e₁}
      {close₂ : PSF.Conf.lookup C j —[ ExprSemantics.L-Close y ]→ e₂}
      {live-ok : LiveCtx (live C) Γ}
      {threads : ThreadsTyped Γ (exps C)}
    → BinaryCompatibility
        {live′ = (live C Subset.- x) Subset.- y}
        close₁ close₂
        (threads-resp-↭ (two-front (exps C) i j i≠j) threads)
    → ReductionTyping
        (T-Conf live-ok threads)
        (PSF.Act-Wait {i≠j = i≠j} pair x-live y-live close₁ close₂)

configuration-reduction-preserves-typing :
  ∀ {n k} {Γ : Ctx [] n} {C : Conf n}
    {π : ConfLabel n k} {C′ : Conf (k + n)}
    (typing : Γ ⊢conf C)
    (step : C —conf[ π ]→ C′)
  → ReductionTyping typing step
  → PreservationResult C′
configuration-reduction-preserves-typing {C = C}
    typing (PSF.Act-Beta step) RT-Beta =
  record
    { Γ′ = _
    ; typing = act-beta-preserves typing step
    }
configuration-reduction-preserves-typing {C = C}
    typing (PSF.Act-Fork step) RT-Fork =
  record
    { Γ′ = _
    ; typing = act-fork-preserves typing step
    }
configuration-reduction-preserves-typing {C = C}
    typing (PSF.Act-New step) RT-New =
  record
    { Γ′ = _
    ; typing = act-new-preserves typing step
    }
configuration-reduction-preserves-typing
    {C = C}
    (T-Conf live-ok threads)
    (PSF.Act-Msg pair x-live y-live recv send)
    (RT-Msg {i = i} {j = j} {i≠j = i≠j}
      {e₁ = e₁} {e₂ = e₂} compatibility)
  with binary-head-preserves compatibility
... | Γ′ , live-ok′ , target-front =
  record
    { Γ′ = Γ′
    ; typing = T-Conf live-ok′
        (threads-resp-↭
          (↭-sym (double-update-front (exps C) i j i≠j e₁ e₂))
          target-front)
    }
configuration-reduction-preserves-typing
    {C = C}
    (T-Conf live-ok threads)
    (PSF.Act-Bra pair x-live y-live recv send)
    (RT-Bra {i = i} {j = j} {i≠j = i≠j}
      {e₁ = e₁} {e₂ = e₂} compatibility)
  with binary-head-preserves compatibility
... | Γ′ , live-ok′ , target-front =
  record
    { Γ′ = Γ′
    ; typing = T-Conf live-ok′
        (threads-resp-↭
          (↭-sym (double-update-front (exps C) i j i≠j e₁ e₂))
          target-front)
    }
configuration-reduction-preserves-typing
    {C = C}
    (T-Conf live-ok threads)
    (PSF.Act-Wait pair x-live y-live close₁ close₂)
    (RT-Wait {i = i} {j = j} {i≠j = i≠j}
      {e₁ = e₁} {e₂ = e₂} compatibility)
  with binary-head-preserves compatibility
... | Γ′ , live-ok′ , target-front =
  record
    { Γ′ = Γ′
    ; typing = T-Conf live-ok′
        (threads-resp-↭
          (↭-sym (double-update-front (exps C) i j i≠j e₁ e₂))
          target-front)
    }
