module ProcSemanticsPermutationFresh where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List as L using
  (List; []; _∷_; length; lookup; removeAt; map)
open import Data.List.Properties using (length-map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProps
import Data.Nat as Nat
open Nat using (ℕ; _+_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Vec using () renaming (_∷_ to _∷ᵥ_)
open import Function using (const)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; subst)

open import ExprSyntax using (Expr)
open import ExprSemantics using (Label; _—[_]→_; shiftRen)
open import ExprSubstitution using (renameExpr)
open import ExprNormalTyping using (Ctx; ∅)

import ProcSemanticsFresh as PSF
open PSF using
  ( Conf
  ; ConfLabel
  ; C-τ
  ; C-new
  ; _—conf[_]→_
  ; Act-Beta
  ; Act-Fork
  ; Act-New
  ; Act-Msg
  ; Act-Bra
  ; Act-Wait
  )
open PSF.Conf using (exps; live)
open import ProcTypingFresh using
  ( Split
  ; S-∅
  ; S-Linˡ
  ; S-Linʳ
  ; S-Un
  ; S-Used
  ; LiveCtx
  ; ThreadsTyped
  ; TT-[]
  ; TT-∷
  ; _⊢conf_
  ; T-Conf
  )

------------------------------------------------------------------------
-- Positions transported by a list permutation

permuteIndex :
  ∀ {A : Set} {xs ys : List A}
  → xs ↭ ys
  → Fin (length xs)
  → Fin (length ys)
permuteIndex Perm.refl i = i
permuteIndex (Perm.prep x p) fzero = fzero
permuteIndex (Perm.prep x p) (fsuc i) = fsuc (permuteIndex p i)
permuteIndex (Perm.swap x y p) fzero = fsuc fzero
permuteIndex (Perm.swap x y p) (fsuc fzero) = fzero
permuteIndex (Perm.swap x y p) (fsuc (fsuc i)) =
  fsuc (fsuc (permuteIndex p i))
permuteIndex (Perm.trans p q) i =
  permuteIndex q (permuteIndex p i)

lookup-permute :
  ∀ {A : Set} {xs ys : List A}
  → (p : xs ↭ ys)
  → (i : Fin (length xs))
  → lookup xs i ≡ lookup ys (permuteIndex p i)
lookup-permute Perm.refl i = refl
lookup-permute (Perm.prep x p) fzero = refl
lookup-permute (Perm.prep x p) (fsuc i) = lookup-permute p i
lookup-permute (Perm.swap x y p) fzero = refl
lookup-permute (Perm.swap x y p) (fsuc fzero) = refl
lookup-permute (Perm.swap x y p) (fsuc (fsuc i)) = lookup-permute p i
lookup-permute (Perm.trans p q) i =
  Eq.trans (lookup-permute p i) (lookup-permute q (permuteIndex p i))

permuteIndex-inverse :
  ∀ {A : Set} {xs ys : List A}
  → (p : xs ↭ ys)
  → (i : Fin (length xs))
  → permuteIndex (Perm.↭-sym p) (permuteIndex p i) ≡ i
permuteIndex-inverse Perm.refl i = refl
permuteIndex-inverse (Perm.prep x p) fzero = refl
permuteIndex-inverse (Perm.prep x p) (fsuc i) =
  cong fsuc (permuteIndex-inverse p i)
permuteIndex-inverse (Perm.swap x y p) fzero = refl
permuteIndex-inverse (Perm.swap x y p) (fsuc fzero) = refl
permuteIndex-inverse (Perm.swap x y p) (fsuc (fsuc i)) =
  cong (λ j → fsuc (fsuc j)) (permuteIndex-inverse p i)
permuteIndex-inverse (Perm.trans p q) i
  rewrite permuteIndex-inverse q (permuteIndex p i)
        | permuteIndex-inverse p i = refl

permuteIndex-injective :
  ∀ {A : Set} {xs ys : List A}
  → (p : xs ↭ ys)
  → ∀ {i j : Fin (length xs)}
  → permuteIndex p i ≡ permuteIndex p j
  → i ≡ j
permuteIndex-injective p {i} {j} eq =
  Eq.trans
    (sym (permuteIndex-inverse p i))
    (Eq.trans
      (cong (permuteIndex (Perm.↭-sym p)) eq)
      (permuteIndex-inverse p j))

permuteIndex-≢ :
  ∀ {A : Set} {xs ys : List A}
  → (p : xs ↭ ys)
  → ∀ {i j : Fin (length xs)}
  → i ≢ j
  → permuteIndex p i ≢ permuteIndex p j
permuteIndex-≢ p i≢j eq = i≢j (permuteIndex-injective p eq)

------------------------------------------------------------------------
-- List operations respect permutation

lookup-front :
  ∀ {A : Set} (xs : List A) (i : Fin (length xs))
  → xs ↭ lookup xs i ∷ removeAt xs i
lookup-front (x ∷ xs) fzero = Perm.refl
lookup-front (x ∷ xs) (fsuc i) =
  Perm.trans
    (Perm.prep x (lookup-front xs i))
    (Perm.swap x (lookup xs i) Perm.refl)

removeAt-permute :
  ∀ {A : Set} {xs ys : List A}
  → (p : xs ↭ ys)
  → (i : Fin (length xs))
  → removeAt xs i ↭ removeAt ys (permuteIndex p i)
removeAt-permute Perm.refl i = Perm.refl
removeAt-permute (Perm.prep x p) fzero = p
removeAt-permute (Perm.prep x p) (fsuc i) =
  Perm.prep x (removeAt-permute p i)
removeAt-permute (Perm.swap x y p) fzero = Perm.prep y p
removeAt-permute (Perm.swap x y p) (fsuc fzero) = Perm.prep x p
removeAt-permute (Perm.swap x y p) (fsuc (fsuc i)) =
  Perm.swap x y (removeAt-permute p i)
removeAt-permute (Perm.trans p q) i =
  Perm.trans
    (removeAt-permute p i)
    (removeAt-permute q (permuteIndex p i))

updateAt-front :
  ∀ {A : Set} (xs : List A) (i : Fin (length xs)) (x′ : A)
  → L.updateAt xs i (const x′) ↭ x′ ∷ removeAt xs i
updateAt-front (x ∷ xs) fzero x′ = Perm.refl
updateAt-front (x ∷ xs) (fsuc i) x′ =
  Perm.trans
    (Perm.prep x (updateAt-front xs i x′))
    (Perm.swap x x′ Perm.refl)

updateAt-permute :
  ∀ {A : Set} {xs ys : List A}
  → (p : xs ↭ ys)
  → (i : Fin (length xs))
  → (x′ : A)
  → L.updateAt xs i (const x′)
      ↭ L.updateAt ys (permuteIndex p i) (const x′)
updateAt-permute {xs = xs} {ys = ys} p i x′ =
  Perm.trans
    (updateAt-front xs i x′)
    (Perm.trans
      (Perm.prep x′ (removeAt-permute p i))
      (Perm.↭-sym (updateAt-front ys (permuteIndex p i) x′)))

subst-Fin-zero-sym-cong :
  ∀ {m n} (p : m ≡ n)
  → subst Fin (sym (cong Nat.suc p)) fzero ≡ fzero
subst-Fin-zero-sym-cong refl = refl

subst-Fin-suc-sym-cong :
  ∀ {m n} (p : m ≡ n) (i : Fin n)
  → subst Fin (sym (cong Nat.suc p)) (fsuc i)
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
  rewrite subst-Fin-zero-sym-cong (length-map f xs) = Perm.refl
map-updateAt-front f (x ∷ xs) (fsuc i) y
  rewrite subst-Fin-suc-sym-cong (length-map f xs) i =
  Perm.trans
    (Perm.prep (f x) (map-updateAt-front f xs i y))
    (Perm.swap (f x) y Perm.refl)

map-updateAt-permute :
  ∀ {A B : Set} {xs ys : List A}
  → (f : A → B)
  → (p : xs ↭ ys)
  → (i : Fin (length xs))
  → (y : B)
  → L.updateAt (map f xs)
      (subst Fin (sym (length-map f xs)) i)
      (const y)
      ↭
      L.updateAt (map f ys)
        (subst Fin (sym (length-map f ys)) (permuteIndex p i))
        (const y)
map-updateAt-permute {xs = xs} {ys = ys} f p i y =
  Perm.trans
    (map-updateAt-front f xs i y)
    (Perm.trans
      (Perm.prep y (PermProps.map⁺ f (removeAt-permute p i)))
      (Perm.↭-sym
        (map-updateAt-front f ys (permuteIndex p i) y)))

removeTwo :
  ∀ {A : Set} (xs : List A)
  → (i j : Fin (length xs))
  → i ≢ j
  → List A
removeTwo (x ∷ xs) fzero fzero i≢j = ⊥-elim (i≢j refl)
removeTwo (x ∷ xs) fzero (fsuc j) i≢j = removeAt xs j
removeTwo (x ∷ xs) (fsuc i) fzero i≢j = removeAt xs i
removeTwo (x ∷ xs) (fsuc i) (fsuc j) i≢j =
  x ∷ removeTwo xs i j (λ eq → i≢j (cong fsuc eq))

two-front :
  ∀ {A : Set} (xs : List A)
    (i j : Fin (length xs)) (i≢j : i ≢ j)
  → xs ↭ lookup xs i ∷ lookup xs j ∷ removeTwo xs i j i≢j
two-front (x ∷ xs) fzero fzero i≢j = ⊥-elim (i≢j refl)
two-front (x ∷ xs) fzero (fsuc j) i≢j =
  Perm.prep x (lookup-front xs j)
two-front (x ∷ xs) (fsuc i) fzero i≢j =
  Perm.trans
    (Perm.prep x (lookup-front xs i))
    (Perm.swap x (lookup xs i) Perm.refl)
two-front (x ∷ xs) (fsuc i) (fsuc j) i≢j =
  let
    tail = two-front xs i j (λ eq → i≢j (cong fsuc eq))
  in
  Perm.trans
    (Perm.prep x tail)
    (Perm.trans
      (Perm.swap x (lookup xs i) Perm.refl)
      (Perm.prep (lookup xs i) (Perm.swap x (lookup xs j) Perm.refl)))

drop-∷-≡ :
  ∀ {A : Set} {x y : A} {xs ys : List A}
  → x ≡ y
  → x ∷ xs ↭ y ∷ ys
  → xs ↭ ys
drop-∷-≡ refl p = PermProps.drop-∷ p

removeTwo-permute :
  ∀ {A : Set} {xs ys : List A}
  → (p : xs ↭ ys)
  → (i j : Fin (length xs))
  → (i≢j : i ≢ j)
  → removeTwo xs i j i≢j
      ↭ removeTwo ys (permuteIndex p i) (permuteIndex p j)
          (permuteIndex-≢ p i≢j)
removeTwo-permute {xs = xs} {ys = ys} p i j i≢j =
  drop-∷-≡ (lookup-permute p j)
    (drop-∷-≡ (lookup-permute p i)
      (Perm.trans
        (Perm.↭-sym (two-front xs i j i≢j))
        (Perm.trans
          p
          (two-front ys (permuteIndex p i) (permuteIndex p j)
            (permuteIndex-≢ p i≢j)))))

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
    (i j : Fin (length xs)) (i≢j : i ≢ j) (x′ y′ : A)
  → doubleUpdateAt xs i j x′ y′
      ↭ x′ ∷ y′ ∷ removeTwo xs i j i≢j
double-update-front (x ∷ xs) fzero fzero i≢j x′ y′ =
  ⊥-elim (i≢j refl)
double-update-front (x ∷ xs) fzero (fsuc j) i≢j x′ y′ =
  Perm.prep x′ (updateAt-front xs j y′)
double-update-front (x ∷ xs) (fsuc i) fzero i≢j x′ y′ =
  subst
    (λ index →
      L.updateAt (x ∷ L.updateAt xs i (const x′)) index (const y′)
        ↭ x′ ∷ y′ ∷ removeAt xs i)
    (sym (subst-Fin-zero-sym-cong (PSF.length-updateAt xs i)))
    (Perm.trans
      (Perm.prep y′ (updateAt-front xs i x′))
      (Perm.swap y′ x′ Perm.refl))
double-update-front (x ∷ xs) (fsuc i) (fsuc j) i≢j x′ y′ =
  subst
    (λ index →
      L.updateAt (x ∷ L.updateAt xs i (const x′)) index (const y′)
        ↭ x′ ∷ y′ ∷
          x ∷ removeTwo xs i j (λ eq → i≢j (cong fsuc eq)))
    (sym (subst-Fin-suc-sym-cong (PSF.length-updateAt xs i) j))
    (let
      tail = double-update-front xs i j
        (λ eq → i≢j (cong fsuc eq)) x′ y′
    in
    Perm.trans
      (Perm.prep x tail)
      (Perm.trans
        (Perm.swap x x′ Perm.refl)
        (Perm.prep x′ (Perm.swap x y′ Perm.refl))))

doubleUpdateAt-permute :
  ∀ {A : Set} {xs ys : List A}
  → (p : xs ↭ ys)
  → (i j : Fin (length xs))
  → (i≢j : i ≢ j)
  → (x′ y′ : A)
  → doubleUpdateAt xs i j x′ y′
      ↭ doubleUpdateAt ys (permuteIndex p i) (permuteIndex p j) x′ y′
doubleUpdateAt-permute {xs = xs} {ys = ys} p i j i≢j x′ y′ =
  Perm.trans
    (double-update-front xs i j i≢j x′ y′)
    (Perm.trans
      (Perm.prep x′
        (Perm.prep y′ (removeTwo-permute p i j i≢j)))
      (Perm.↭-sym
        (double-update-front ys
          (permuteIndex p i) (permuteIndex p j)
          (permuteIndex-≢ p i≢j) x′ y′)))

------------------------------------------------------------------------
-- Configuration permutation and transition equivariance

infix 4 _≈ᶜ_

record _≈ᶜ_ {n : ℕ} (C D : Conf n) : Set where
  constructor conf-perm
  field
    exps↭ : exps C ↭ exps D
    live≡ : live C ≡ live D

≈ᶜ-refl : ∀ {n} {C : Conf n} → C ≈ᶜ C
≈ᶜ-refl = conf-perm Perm.refl refl

≈ᶜ-sym : ∀ {n} {C D : Conf n} → C ≈ᶜ D → D ≈ᶜ C
≈ᶜ-sym (conf-perm p eq) = conf-perm (Perm.↭-sym p) (sym eq)

≈ᶜ-trans : ∀ {n} {C D F : Conf n} → C ≈ᶜ D → D ≈ᶜ F → C ≈ᶜ F
≈ᶜ-trans (conf-perm p eq₁) (conf-perm q eq₂) =
  conf-perm (Perm.trans p q) (Eq.trans eq₁ eq₂)

------------------------------------------------------------------------
-- Configuration typing is invariant under permutation

split-swap-nested :
  ∀ {Δ n} {Γ Γ₁ Γ₂… Γ₂ Γ₃ : Ctx Δ n}
  → Split Γ Γ₁ Γ₂…
  → Split Γ₂… Γ₂ Γ₃
  → Σ (Ctx Δ n) λ Γ₁… →
      Split Γ Γ₂ Γ₁… × Split Γ₁… Γ₁ Γ₃
split-swap-nested S-∅ S-∅ = ∅ , S-∅ , S-∅
split-swap-nested (S-Linˡ sp₁) (S-Used sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , outer , inner =
  _ , S-Linʳ outer , S-Linˡ inner
split-swap-nested (S-Linʳ sp₁) (S-Linˡ sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , outer , inner =
  _ , S-Linˡ outer , S-Used inner
split-swap-nested (S-Linʳ sp₁) (S-Linʳ sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , outer , inner =
  _ , S-Linʳ outer , S-Linʳ inner
split-swap-nested (S-Un sp₁) (S-Un sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , outer , inner =
  _ , S-Un outer , S-Un inner
split-swap-nested (S-Used sp₁) (S-Used sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , outer , inner =
  _ , S-Used outer , S-Used inner

threads-swap :
  ∀ {n} {Γ : Ctx [] n} {e₁ e₂ : Expr [] n} {es : List (Expr [] n)}
  → ThreadsTyped Γ (e₁ ∷ e₂ ∷ es)
  → ThreadsTyped Γ (e₂ ∷ e₁ ∷ es)
threads-swap
    (TT-∷ split₁ d₁ used₁ (TT-∷ split₂ d₂ used₂ rest))
  with split-swap-nested split₁ split₂
... | Γ₁… , split₂′ , split₁′ =
  TT-∷ split₂′ d₂ used₂ (TT-∷ split₁′ d₁ used₁ rest)

threads-resp-↭ :
  ∀ {n} {Γ : Ctx [] n} {es es′ : List (Expr [] n)}
  → es ↭ es′
  → ThreadsTyped Γ es
  → ThreadsTyped Γ es′
threads-resp-↭ Perm.refl typed = typed
threads-resp-↭ (Perm.prep e p) (TT-∷ split d used rest) =
  TT-∷ split d used (threads-resp-↭ p rest)
threads-resp-↭ (Perm.swap e₁ e₂ p) typed
  with threads-swap typed
... | TT-∷ split₂ d₂ used₂ (TT-∷ split₁ d₁ used₁ rest) =
  TT-∷ split₂ d₂ used₂
    (TT-∷ split₁ d₁ used₁ (threads-resp-↭ p rest))
threads-resp-↭ (Perm.trans p q) typed =
  threads-resp-↭ q (threads-resp-↭ p typed)

typing-resp-≈ᶜ :
  ∀ {n} {Γ : Ctx [] n} {C D : Conf n}
  → C ≈ᶜ D
  → Γ ⊢conf C
  → Γ ⊢conf D
typing-resp-≈ᶜ (conf-perm p live-eq) (T-Conf live-ok threads) =
  T-Conf
    (subst (λ ss → LiveCtx ss _) live-eq live-ok)
    (threads-resp-↭ p threads)

step-source-subst :
  ∀ {n Θ} {e₁ e₂ : Expr [] n}
    {label : Label n Θ} {e′ : Expr [] (length Θ + n)}
  → e₁ ≡ e₂
  → e₁ —[ label ]→ e′
  → e₂ —[ label ]→ e′
step-source-subst refl step = step

step-resp-≈ᶜ :
  ∀ {n k} {C D : Conf n} {label : ConfLabel n k} {C′ : Conf (k + n)}
  → C ≈ᶜ D
  → C —conf[ label ]→ C′
  → Σ (Conf (k + n)) λ D′ →
      (D —conf[ label ]→ D′) × (C′ ≈ᶜ D′)
step-resp-≈ᶜ (conf-perm p live-eq)
    (Act-Beta {e′ = e′} {i = i} step) =
  let
    step′ = step-source-subst (lookup-permute p i) step
  in
  _ ,
  Act-Beta step′ ,
  conf-perm (updateAt-permute p i e′) live-eq
step-resp-≈ᶜ (conf-perm p live-eq)
    (Act-Fork {e′ = e′} {i = i} step) =
  let
    step′ = step-source-subst (lookup-permute p i) step
  in
  _ ,
  Act-Fork step′ ,
  conf-perm (Perm.prep _ (updateAt-permute p i e′)) live-eq
step-resp-≈ᶜ (conf-perm p live-eq)
    (Act-New {e′ = e′} {i = i} step) =
  let
    step′ = step-source-subst (lookup-permute p i) step
  in
  _ ,
  Act-New step′ ,
  conf-perm
    (map-updateAt-permute (renameExpr (shiftRen 2)) p i e′)
    (cong (λ ss → Subset.inside ∷ᵥ Subset.inside ∷ᵥ ss) live-eq)
step-resp-≈ᶜ (conf-perm p live-eq)
    (Act-Msg {e₁ = e₁} {e₂ = e₂} {i = i} {j = j} {i≠j = i≢j}
      {x = x} {y = y} fresh x-live y-live step₁ step₂) =
  let
    i≢j′ = permuteIndex-≢ p i≢j
    x-live′ = subst (λ ss → x Subset.∈ ss) live-eq x-live
    y-live′ = subst (λ ss → y Subset.∈ ss) live-eq y-live
    step₁′ = step-source-subst (lookup-permute p i) step₁
    step₂′ = step-source-subst (lookup-permute p j) step₂
  in
  _ ,
  Act-Msg {i≠j = i≢j′} fresh x-live′ y-live′ step₁′ step₂′ ,
  conf-perm (doubleUpdateAt-permute p i j i≢j e₁ e₂) live-eq
step-resp-≈ᶜ (conf-perm p live-eq)
    (Act-Bra {e₁ = e₁} {e₂ = e₂} {i = i} {j = j} {i≠j = i≢j}
      {x = x} {y = y} fresh x-live y-live step₁ step₂) =
  let
    i≢j′ = permuteIndex-≢ p i≢j
    x-live′ = subst (λ ss → x Subset.∈ ss) live-eq x-live
    y-live′ = subst (λ ss → y Subset.∈ ss) live-eq y-live
    step₁′ = step-source-subst (lookup-permute p i) step₁
    step₂′ = step-source-subst (lookup-permute p j) step₂
  in
  _ ,
  Act-Bra {i≠j = i≢j′} fresh x-live′ y-live′ step₁′ step₂′ ,
  conf-perm (doubleUpdateAt-permute p i j i≢j e₁ e₂) live-eq
step-resp-≈ᶜ (conf-perm p live-eq)
    (Act-Wait {e₁ = e₁} {e₂ = e₂} {i = i} {j = j} {i≠j = i≢j}
      {x = x} {y = y} fresh x-live y-live step₁ step₂) =
  let
    i≢j′ = permuteIndex-≢ p i≢j
    x-live′ = subst (λ ss → x Subset.∈ ss) live-eq x-live
    y-live′ = subst (λ ss → y Subset.∈ ss) live-eq y-live
    step₁′ = step-source-subst (lookup-permute p i) step₁
    step₂′ = step-source-subst (lookup-permute p j) step₂
  in
  _ ,
  Act-Wait {i≠j = i≢j′} fresh x-live′ y-live′ step₁′ step₂′ ,
  conf-perm
    (doubleUpdateAt-permute p i j i≢j e₁ e₂)
    (cong (λ ss → (ss Subset.- x) Subset.- y) live-eq)

step-resp-≈ᶜ-sym :
  ∀ {n k} {C D : Conf n} {label : ConfLabel n k} {D′ : Conf (k + n)}
  → C ≈ᶜ D
  → D —conf[ label ]→ D′
  → Σ (Conf (k + n)) λ C′ →
      (C —conf[ label ]→ C′) × (C′ ≈ᶜ D′)
step-resp-≈ᶜ-sym C≈D step
  with step-resp-≈ᶜ (≈ᶜ-sym C≈D) step
... | C′ , C-step , D′≈C′ = C′ , C-step , ≈ᶜ-sym D′≈C′
