module ProcProgressFreshDecidable where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using ()
  renaming (_≟_ to _≟Fin_)
import Data.Fin.Subset as Subset
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.All using ()
  renaming ([] to all[]; _∷_ to _all∷_)
open import Data.List.Relation.Unary.Any using ()
  renaming (here to any-here; there to any-there)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using ()
  renaming (_≟_ to _≟Nat_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (here; there) renaming (_∷_ to _∷ᵥ_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Kinds
open import ExprSyntax
open import ExprNormalTyping using (normalizeTy-id; ⌞_⌟)
open import ExprSemantics
import ProcSemanticsFresh as PS
open PS using (Conf; FinFreshPair; here-fwd; here-bwd; there)
open PS.Conf using (exps; live; lookup; ∣_∣)
open import ProcProgressFreshDefinitions

------------------------------------------------------------------------
-- Finite searches

any-fin? :
  ∀ {n} {P : Fin n → Set}
  → ((i : Fin n) → Dec (P i))
  → Dec (Σ (Fin n) P)
any-fin? {n = zero} decide = no λ where
  (() , _)
any-fin? {n = suc n} decide with decide fzero
... | yes proof = yes (fzero , proof)
... | no not-zero with any-fin? (λ i → decide (fsuc i))
... | yes (i , proof) = yes (fsuc i , proof)
... | no not-tail = no λ where
  (fzero , proof) → not-zero proof
  (fsuc i , proof) → not-tail (i , proof)

subset-member? :
  ∀ {n} (i : Fin n) (ss : Subset.Subset n)
  → Dec (i Subset.∈ ss)
subset-member? fzero (Subset.inside ∷ᵥ ss) = yes here
subset-member? fzero (Subset.outside ∷ᵥ ss) = no λ ()
subset-member? (fsuc i) (bit ∷ᵥ ss) with subset-member? i ss
... | yes member = yes (there member)
... | no not-member = no λ where
  (there member) → not-member member

fresh-pair? :
  ∀ {n} (x y : Fin (2 + n))
  → Dec (FinFreshPair {n} x y)
fresh-pair? fzero fzero = no λ ()
fresh-pair? fzero (fsuc fzero) = yes here-fwd
fresh-pair? fzero (fsuc (fsuc y)) = no λ ()
fresh-pair? (fsuc fzero) fzero = yes here-bwd
fresh-pair? (fsuc fzero) (fsuc fzero) = no λ ()
fresh-pair? (fsuc fzero) (fsuc (fsuc y)) = no λ ()
fresh-pair? (fsuc (fsuc x)) fzero = no λ ()
fresh-pair? (fsuc (fsuc x)) (fsuc fzero) = no λ ()
fresh-pair? {n = suc zero}
    (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) =
  no λ ()
fresh-pair? {n = suc (suc n)}
    (fsuc (fsuc x)) (fsuc (fsuc y))
  with fresh-pair? {n = n} x y
... | yes pair = yes (there pair)
... | no not-pair = no λ where
  (there pair) → not-pair pair

------------------------------------------------------------------------
-- Independent actions

is-value? : ∀ {n} (e : Expr [] n) → Dec (IsValue e)
is-value? (E-Val value) = yes (is-value value)
is-value? (E-App left right) = no λ ()
is-value? (E-TApp function argument) = no λ ()
is-value? (E-LetUnit first second) = no λ ()
is-value? (E-Pair first second) = no λ ()
is-value? (E-LetPair first body) = no λ ()
is-value? (E-Match scrutinee nonempty branches) = no λ ()

all-list? :
  ∀ {A : Set} {P : A → Set}
  → ((x : A) → Dec (P x))
  → (xs : Data.List.List A)
  → Dec (Data.List.Relation.Unary.All.All P xs)
all-list? decide [] = yes all[]
all-list? decide (x ∷ xs) with decide x | all-list? decide xs
... | yes proof | yes proofs = yes (proof all∷ proofs)
... | no not-proof | _ =
  no λ where
    (proof all∷ proofs) → not-proof proof
... | yes proof | no not-proofs =
  no λ where
    (proof′ all∷ proofs) → not-proofs proofs

any-list? :
  ∀ {A : Set} {P : A → Set}
  → ((x : A) → Dec (P x))
  → (xs : Data.List.List A)
  → Dec (Data.List.Relation.Unary.Any.Any P xs)
any-list? decide [] = no λ ()
any-list? decide (x ∷ xs) with decide x
... | yes proof = yes (any-here proof)
... | no not-proof with any-list? decide xs
... | yes proofs = yes (any-there proofs)
... | no not-proofs =
  no λ where
    (any-here proof) → not-proof proof
    (any-there proofs) → not-proofs proofs

terminal? : ∀ {n} (C : Conf n) → Dec (Terminal C)
terminal? C with all-list? is-value? (exps C)
... | yes values = yes (terminal values)
... | no not-values =
  no λ where
    (terminal values) → not-values values

data AppHeadRunnable {n : ℕ} :
    Value [] n → Expr [] n → Set where
  head-app : ∀ {pk} {T : NfTy [] (KV pk Lin)}
      {body : Expr [] (suc n)} {argument : Value [] n}
    → AppHeadRunnable (V-Abs T body) (E-Val argument)
  head-rec : ∀ {pk₁ pk₂ m₁ m₂}
      {T : NfTy [] (KV pk₁ m₁)} {U : NfTy [] (KV pk₂ m₂)}
      {body : Value [] (suc n)} {argument : Expr [] n}
    → AppHeadRunnable (V-Rec T U body) argument
  head-fork : ∀ {argument : Value [] n}
    → AppHeadRunnable (V-Const C-Fork) (E-Val argument)

app-head-runnable? :
  ∀ {n} (function : Value [] n) (argument : Expr [] n)
  → Dec (AppHeadRunnable function argument)
app-head-runnable? (V-Abs {m = m} T body) (E-Val argument)
  with eq-multiplicity m Lin
... | yes refl = yes head-app
... | no m≢ = no λ where
  head-app → m≢ refl
app-head-runnable? (V-Rec T U body) argument = yes head-rec
app-head-runnable? (V-Const C-Fork) (E-Val argument) = yes head-fork
app-head-runnable? (V-Const C-Unit) argument = no λ ()
app-head-runnable? (V-Const C-Fork) (E-App left right) = no λ ()
app-head-runnable? (V-Const C-Fork) (E-TApp function type) = no λ ()
app-head-runnable? (V-Const C-Fork) (E-LetUnit first second) = no λ ()
app-head-runnable? (V-Const C-Fork) (E-Pair first second) = no λ ()
app-head-runnable? (V-Const C-Fork) (E-LetPair first body) = no λ ()
app-head-runnable? (V-Const C-Fork) (E-Match scrutinee ne branches) =
  no λ ()
app-head-runnable? (V-Const C-New) argument = no λ ()
app-head-runnable? (V-Const C-Receive) argument = no λ ()
app-head-runnable? (V-Const C-Send) argument = no λ ()
app-head-runnable? (V-Const (C-Select variance i)) argument = no λ ()
app-head-runnable? (V-Const C-Close) argument = no λ ()
app-head-runnable? (V-Var x) argument = no λ ()
app-head-runnable? (V-Abs T body) (E-App left right) = no λ ()
app-head-runnable? (V-Abs T body) (E-TApp function type) = no λ ()
app-head-runnable? (V-Abs T body) (E-LetUnit first second) = no λ ()
app-head-runnable? (V-Abs T body) (E-Pair first second) = no λ ()
app-head-runnable? (V-Abs T body) (E-LetPair first pair-body) = no λ ()
app-head-runnable? (V-Abs T body) (E-Match scrutinee ne branches) =
  no λ ()
app-head-runnable? (V-TAbs K body) argument = no λ ()
app-head-runnable? (V-Pair first second) argument = no λ ()
app-head-runnable? (V-Receive₁ T) argument = no λ ()
app-head-runnable? (V-Receive₂ T S) argument = no λ ()
app-head-runnable? (V-Send₁ T) argument = no λ ()
app-head-runnable? (V-Send₂ T S) argument = no λ ()
app-head-runnable? (V-Select₁ variance i P) argument = no λ ()
app-head-runnable? (V-Select₂ variance i P S) argument = no λ ()

app-head-runs :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
  → AppHeadRunnable function argument
  → Runnable (E-App (E-Val function) argument)
app-head-runs head-app = run-β Act-App
app-head-runs head-rec = run-β Act-Rec
app-head-runs head-fork = run-fork Act-Fork

app-runnable-invert :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
  → Runnable (E-App (E-Val function) argument)
  → AppHeadRunnable function argument ⊎ Runnable argument
app-runnable-invert (run-β Act-App) = inj₁ head-app
app-runnable-invert (run-β Act-Rec) = inj₁ head-rec
app-runnable-invert (run-β (Act-AppR step)) = inj₂ (run-β step)
app-runnable-invert (run-fork Act-Fork) = inj₁ head-fork
app-runnable-invert (run-fork (Act-AppR step)) =
  inj₂ (run-fork step)
app-runnable-invert (run-new (Act-AppR step)) =
  inj₂ (run-new step)

data TAppHeadRunnable {n : ℕ} :
    ∀ {K} → Value [] n → NfTy [] K → Set where
  head-tapp : ∀ {K} {body : Value (K ∷ []) n} {U : NfTy [] K}
    → TAppHeadRunnable (V-TAbs K body) U
  head-new : ∀ {S : NfTy [] SLin}
    → TAppHeadRunnable (V-Const C-New) S
  head-receive₁ : ∀ {T : NfTy [] TLin}
    → TAppHeadRunnable (V-Const C-Receive) T
  head-receive₂ : ∀ {pk} {T : NfTy [] (KV pk Lin)}
      {S : NfTy [] SLin}
    → TAppHeadRunnable (V-Receive₁ T) S
  head-send₁ : ∀ {T : NfTy [] TLin}
    → TAppHeadRunnable (V-Const C-Send) T
  head-send₂ : ∀ {pk} {T : NfTy [] (KV pk Lin)}
      {S : NfTy [] SLin}
    → TAppHeadRunnable (V-Send₁ T) S
  head-select₁ : ∀ {k} {variance} {i : Fin k} {P : NfTy [] KP}
    → TAppHeadRunnable (V-Const (C-Select variance i)) P
  head-select₂ : ∀ {k} {variance} {i : Fin k}
      {P : NfTy [] KP} {S : NfTy [] SLin}
    → TAppHeadRunnable (V-Select₁ variance i P) S

tapp-head-runnable? :
  ∀ {n K} (function : Value [] n) (argument : NfTy [] K)
  → Dec (TAppHeadRunnable function argument)
tapp-head-runnable? {K = K} (V-Const C-New) argument
  with eq-kind K SLin
... | yes refl = yes head-new
... | no K≢ = no λ where
  head-new → K≢ refl
tapp-head-runnable? {K = K} (V-Const C-Receive) argument
  with eq-kind K TLin
... | yes refl = yes head-receive₁
... | no K≢ = no λ where
  head-receive₁ → K≢ refl
tapp-head-runnable? {K = K} (V-Const C-Send) argument
  with eq-kind K TLin
... | yes refl = yes head-send₁
... | no K≢ = no λ where
  head-send₁ → K≢ refl
tapp-head-runnable? {K = K}
    (V-Const (C-Select variance i)) argument
  with eq-kind K KP
... | yes refl = yes head-select₁
... | no K≢ = no λ where
  head-select₁ → K≢ refl
tapp-head-runnable? {K = K} (V-TAbs K′ body) argument
  with eq-kind K K′
... | yes refl = yes head-tapp
... | no K≢ = no λ where
  head-tapp → K≢ refl
tapp-head-runnable? {K = K} (V-Receive₁ T) argument
  with eq-kind K SLin
... | yes refl = yes head-receive₂
... | no K≢ = no λ where
  head-receive₂ → K≢ refl
tapp-head-runnable? {K = K} (V-Send₁ T) argument
  with eq-kind K SLin
... | yes refl = yes head-send₂
... | no K≢ = no λ where
  head-send₂ → K≢ refl
tapp-head-runnable? {K = K}
    (V-Select₁ variance i P) argument
  with eq-kind K SLin
... | yes refl = yes head-select₂
... | no K≢ = no λ where
  head-select₂ → K≢ refl
tapp-head-runnable? (V-Const C-Unit) argument = no λ ()
tapp-head-runnable? (V-Const C-Fork) argument = no λ ()
tapp-head-runnable? (V-Const C-Close) argument = no λ ()
tapp-head-runnable? (V-Var x) argument = no λ ()
tapp-head-runnable? (V-Abs T body) argument = no λ ()
tapp-head-runnable? (V-Rec T U body) argument = no λ ()
tapp-head-runnable? (V-Pair first second) argument = no λ ()
tapp-head-runnable? (V-Receive₂ T S) argument = no λ ()
tapp-head-runnable? (V-Send₂ T S) argument = no λ ()
tapp-head-runnable? (V-Select₂ variance i P S) argument = no λ ()

tapp-head-runs :
  ∀ {n K} {function : Value [] n} {argument : NfTy [] K}
  → TAppHeadRunnable function argument
  → Runnable (E-TApp (E-Val function) argument)
tapp-head-runs {argument = argument} head-tapp
  rewrite sym (normalizeTy-id argument) =
  run-β (Act-TApp {T = ⌞ argument ⌟})
tapp-head-runs {argument = argument} head-new
  rewrite sym (normalizeTy-id argument) =
  run-new (Act-New {S = ⌞ argument ⌟})
tapp-head-runs {argument = argument} head-receive₁
  rewrite sym (normalizeTy-id argument) =
  run-β (Act-Receive₁ {T = ⌞ argument ⌟})
tapp-head-runs head-receive₂ = run-β Act-Receive₂
tapp-head-runs {argument = argument} head-send₁
  rewrite sym (normalizeTy-id argument) =
  run-β (Act-Send₁ {T = ⌞ argument ⌟})
tapp-head-runs head-send₂ = run-β Act-Send₂
tapp-head-runs {argument = argument} head-select₁
  rewrite sym (normalizeTy-id argument) =
  run-β (Act-Select₁ {P = ⌞ argument ⌟})
tapp-head-runs head-select₂ = run-β Act-Select₂

tapp-runnable-invert :
  ∀ {n K} {function : Value [] n} {argument : NfTy [] K}
  → Runnable (E-TApp (E-Val function) argument)
  → TAppHeadRunnable function argument
tapp-runnable-invert (run-β Act-TApp) = head-tapp
tapp-runnable-invert (run-β Act-Receive₁) = head-receive₁
tapp-runnable-invert (run-β Act-Receive₂) = head-receive₂
tapp-runnable-invert (run-β Act-Send₁) = head-send₁
tapp-runnable-invert (run-β Act-Send₂) = head-send₂
tapp-runnable-invert (run-β Act-Select₁) = head-select₁
tapp-runnable-invert (run-β Act-Select₂) = head-select₂
tapp-runnable-invert (run-fork (Act-TAppE ()))
tapp-runnable-invert (run-new Act-New) = head-new

app-left-runnable-invert :
  ∀ {n} {left right : Expr [] n}
  → (IsValue left → ⊥)
  → Runnable (E-App left right)
  → Runnable left
app-left-runnable-invert not-value (run-β Act-App) =
  ⊥-elim (not-value (is-value _))
app-left-runnable-invert not-value (run-β Act-Rec) =
  ⊥-elim (not-value (is-value _))
app-left-runnable-invert not-value (run-β (Act-AppL step)) =
  run-β step
app-left-runnable-invert not-value (run-β (Act-AppR step)) =
  ⊥-elim (not-value (is-value _))
app-left-runnable-invert not-value (run-fork Act-Fork) =
  ⊥-elim (not-value (is-value _))
app-left-runnable-invert not-value (run-fork (Act-AppL step)) =
  run-fork step
app-left-runnable-invert not-value (run-fork (Act-AppR step)) =
  ⊥-elim (not-value (is-value _))
app-left-runnable-invert not-value (run-new (Act-AppL step)) =
  run-new step
app-left-runnable-invert not-value (run-new (Act-AppR step)) =
  ⊥-elim (not-value (is-value _))

pair-left-runnable-invert :
  ∀ {n} {left right : Expr [] n}
  → (IsValue left → ⊥)
  → Runnable (E-Pair left right)
  → Runnable left
pair-left-runnable-invert not-value (run-β Act-PairV) =
  ⊥-elim (not-value (is-value _))
pair-left-runnable-invert not-value (run-β (Act-PairL step)) =
  run-β step
pair-left-runnable-invert not-value (run-β (Act-PairR step)) =
  ⊥-elim (not-value (is-value _))
pair-left-runnable-invert not-value (run-fork (Act-PairL step)) =
  run-fork step
pair-left-runnable-invert not-value (run-fork (Act-PairR step)) =
  ⊥-elim (not-value (is-value _))
pair-left-runnable-invert not-value (run-new (Act-PairL step)) =
  run-new step
pair-left-runnable-invert not-value (run-new (Act-PairR step)) =
  ⊥-elim (not-value (is-value _))

pair-right-runnable-invert :
  ∀ {n} {left : Value [] n} {right : Expr [] n}
  → Runnable (E-Pair (E-Val left) right)
  → IsValue right ⊎ Runnable right
pair-right-runnable-invert (run-β Act-PairV) =
  inj₁ (is-value _)
pair-right-runnable-invert (run-β (Act-PairR step)) =
  inj₂ (run-β step)
pair-right-runnable-invert (run-fork (Act-PairR step)) =
  inj₂ (run-fork step)
pair-right-runnable-invert (run-new (Act-PairR step)) =
  inj₂ (run-new step)

tapp-function-runnable-invert :
  ∀ {n K} {function : Expr [] n} {argument : NfTy [] K}
  → (IsValue function → ⊥)
  → Runnable (E-TApp function argument)
  → Runnable function
tapp-function-runnable-invert not-value (run-β Act-TApp) =
  ⊥-elim (not-value (is-value _))
tapp-function-runnable-invert not-value (run-β Act-Receive₁) =
  ⊥-elim (not-value (is-value _))
tapp-function-runnable-invert not-value (run-β Act-Receive₂) =
  ⊥-elim (not-value (is-value _))
tapp-function-runnable-invert not-value (run-β Act-Send₁) =
  ⊥-elim (not-value (is-value _))
tapp-function-runnable-invert not-value (run-β Act-Send₂) =
  ⊥-elim (not-value (is-value _))
tapp-function-runnable-invert not-value (run-β Act-Select₁) =
  ⊥-elim (not-value (is-value _))
tapp-function-runnable-invert not-value (run-β Act-Select₂) =
  ⊥-elim (not-value (is-value _))
tapp-function-runnable-invert not-value (run-β (Act-TAppE step)) =
  run-β step
tapp-function-runnable-invert not-value (run-fork (Act-TAppE step)) =
  run-fork step
tapp-function-runnable-invert not-value (run-new Act-New) =
  ⊥-elim (not-value (is-value _))
tapp-function-runnable-invert not-value (run-new (Act-TAppE step)) =
  run-new step

match-runnable-invert :
  ∀ {n k} {ss : Subset.Subset k}
    {scrutinee : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
  → Runnable (E-Match scrutinee ne branches)
  → Runnable scrutinee
match-runnable-invert (run-β (Act-MatchE step)) = run-β step
match-runnable-invert (run-fork (Act-MatchE step)) = run-fork step
match-runnable-invert (run-new (Act-MatchE step)) = run-new step

data PairValue {n : ℕ} : Expr [] n → Set where
  pair-value : ∀ {first second}
    → PairValue (E-Val (V-Pair first second))

pair-value? : ∀ {n} (e : Expr [] n) → Dec (PairValue e)
pair-value? (E-Val (V-Pair first second)) = yes pair-value
pair-value? (E-Val (V-Const constant)) = no λ ()
pair-value? (E-Val (V-Var x)) = no λ ()
pair-value? (E-Val (V-Abs T body)) = no λ ()
pair-value? (E-Val (V-Rec T U body)) = no λ ()
pair-value? (E-Val (V-TAbs K body)) = no λ ()
pair-value? (E-Val (V-Receive₁ T)) = no λ ()
pair-value? (E-Val (V-Receive₂ T S)) = no λ ()
pair-value? (E-Val (V-Send₁ T)) = no λ ()
pair-value? (E-Val (V-Send₂ T S)) = no λ ()
pair-value? (E-Val (V-Select₁ variance i P)) = no λ ()
pair-value? (E-Val (V-Select₂ variance i P S)) = no λ ()
pair-value? (E-App left right) = no λ ()
pair-value? (E-TApp function argument) = no λ ()
pair-value? (E-LetUnit first second) = no λ ()
pair-value? (E-Pair first second) = no λ ()
pair-value? (E-LetPair first body) = no λ ()
pair-value? (E-Match scrutinee ne branches) = no λ ()

data UnitValue {n : ℕ} : Expr [] n → Set where
  unit-value : UnitValue (E-Val (V-Const C-Unit))

unit-value? : ∀ {n} (e : Expr [] n) → Dec (UnitValue e)
unit-value? (E-Val (V-Const C-Unit)) = yes unit-value
unit-value? (E-Val (V-Const C-Fork)) = no λ ()
unit-value? (E-Val (V-Const C-New)) = no λ ()
unit-value? (E-Val (V-Const C-Receive)) = no λ ()
unit-value? (E-Val (V-Const C-Send)) = no λ ()
unit-value? (E-Val (V-Const (C-Select variance i))) = no λ ()
unit-value? (E-Val (V-Const C-Close)) = no λ ()
unit-value? (E-Val (V-Var x)) = no λ ()
unit-value? (E-Val (V-Abs T body)) = no λ ()
unit-value? (E-Val (V-Rec T U body)) = no λ ()
unit-value? (E-Val (V-TAbs K body)) = no λ ()
unit-value? (E-Val (V-Pair first second)) = no λ ()
unit-value? (E-Val (V-Receive₁ T)) = no λ ()
unit-value? (E-Val (V-Receive₂ T S)) = no λ ()
unit-value? (E-Val (V-Send₁ T)) = no λ ()
unit-value? (E-Val (V-Send₂ T S)) = no λ ()
unit-value? (E-Val (V-Select₁ variance i P)) = no λ ()
unit-value? (E-Val (V-Select₂ variance i P S)) = no λ ()
unit-value? (E-App left right) = no λ ()
unit-value? (E-TApp function argument) = no λ ()
unit-value? (E-LetUnit first second) = no λ ()
unit-value? (E-Pair first second) = no λ ()
unit-value? (E-LetPair first body) = no λ ()
unit-value? (E-Match scrutinee ne branches) = no λ ()

let-pair-runnable-invert :
  ∀ {n} {first : Expr [] n} {body : Expr [] (suc (suc n))}
  → (PairValue first → ⊥)
  → Runnable (E-LetPair first body)
  → Runnable first
let-pair-runnable-invert not-pair (run-β Act-LetPair) =
  ⊥-elim (not-pair pair-value)
let-pair-runnable-invert not-pair (run-β (Act-LetPairE step)) =
  run-β step
let-pair-runnable-invert not-pair (run-fork (Act-LetPairE step)) =
  run-fork step
let-pair-runnable-invert not-pair (run-new (Act-LetPairE step)) =
  run-new step

let-unit-runnable-invert :
  ∀ {n} {first second : Expr [] n}
  → (UnitValue first → ⊥)
  → Runnable (E-LetUnit first second)
  → Runnable first
let-unit-runnable-invert not-unit (run-β Act-LetUnit) =
  ⊥-elim (not-unit unit-value)
let-unit-runnable-invert not-unit (run-β (Act-LetUnitE step)) =
  run-β step
let-unit-runnable-invert not-unit (run-fork (Act-LetUnitE step)) =
  run-fork step
let-unit-runnable-invert not-unit (run-new (Act-LetUnitE step)) =
  run-new step

runnable? : ∀ {n} (e : Expr [] n) → Dec (Runnable e)
value-not-runnable :
  ∀ {n} {value : Value [] n}
  → Runnable (E-Val value)
  → ⊥
value-not-runnable (run-β ())
value-not-runnable (run-fork ())
value-not-runnable (run-new ())

refute-sum :
  ∀ {P Q : Set}
  → (P → ⊥)
  → (Q → ⊥)
  → P ⊎ Q
  → ⊥
refute-sum not-P not-Q (inj₁ proof) = not-P proof
refute-sum not-P not-Q (inj₂ proof) = not-Q proof

app-left-runs-d :
  ∀ {n} {left right : Expr [] n}
  → Runnable left
  → Runnable (E-App left right)
app-left-runs-d (run-β step) = run-β (Act-AppL step)
app-left-runs-d (run-fork step) = run-fork (Act-AppL step)
app-left-runs-d (run-new step) = run-new (Act-AppL step)

app-right-runs-d :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
  → Runnable argument
  → Runnable (E-App (E-Val function) argument)
app-right-runs-d (run-β step) = run-β (Act-AppR step)
app-right-runs-d (run-fork step) = run-fork (Act-AppR step)
app-right-runs-d (run-new step) = run-new (Act-AppR step)

tapp-runs-d :
  ∀ {n K} {function : Expr [] n} {argument : NfTy [] K}
  → Runnable function
  → Runnable (E-TApp function argument)
tapp-runs-d (run-β step) =
  run-β (Act-TAppE step)
tapp-runs-d (run-fork step) =
  run-fork (Act-TAppE step)
tapp-runs-d (run-new step) =
  run-new (Act-TAppE step)

pair-left-runs-d :
  ∀ {n} {left right : Expr [] n}
  → Runnable left
  → Runnable (E-Pair left right)
pair-left-runs-d (run-β step) = run-β (Act-PairL step)
pair-left-runs-d (run-fork step) = run-fork (Act-PairL step)
pair-left-runs-d (run-new step) = run-new (Act-PairL step)

pair-right-runs-d :
  ∀ {n} {first : Value [] n} {second : Expr [] n}
  → Runnable second
  → Runnable (E-Pair (E-Val first) second)
pair-right-runs-d (run-β step) = run-β (Act-PairR step)
pair-right-runs-d (run-fork step) = run-fork (Act-PairR step)
pair-right-runs-d (run-new step) = run-new (Act-PairR step)

let-pair-runs-d :
  ∀ {n} {first : Expr [] n} {body : Expr [] (suc (suc n))}
  → Runnable first
  → Runnable (E-LetPair first body)
let-pair-runs-d (run-β step) = run-β (Act-LetPairE step)
let-pair-runs-d (run-fork step) = run-fork (Act-LetPairE step)
let-pair-runs-d (run-new step) = run-new (Act-LetPairE step)

let-unit-runs-d :
  ∀ {n} {first second : Expr [] n}
  → Runnable first
  → Runnable (E-LetUnit first second)
let-unit-runs-d (run-β step) = run-β (Act-LetUnitE step)
let-unit-runs-d (run-fork step) = run-fork (Act-LetUnitE step)
let-unit-runs-d (run-new step) = run-new (Act-LetUnitE step)

match-runs-d :
  ∀ {n k} {ss : Subset.Subset k}
    {scrutinee : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
  → Runnable scrutinee
  → Runnable (E-Match scrutinee ne branches)
match-runs-d (run-β step) = run-β (Act-MatchE step)
match-runs-d (run-fork step) = run-fork (Act-MatchE step)
match-runs-d (run-new step) = run-new (Act-MatchE step)

decide-app-left :
  ∀ {n} {left right : Expr [] n}
  → (IsValue left → ⊥)
  → Dec (Runnable left)
  → Dec (Runnable (E-App left right))
decide-app-left not-value (yes runnable) =
  yes (app-left-runs-d runnable)
decide-app-left not-value (no not-runnable) =
  no λ outer →
    not-runnable (app-left-runnable-invert not-value outer)

decide-app-value :
  ∀ {n} (function : Value [] n) (argument : Expr [] n)
  → Dec (AppHeadRunnable function argument)
  → Dec (Runnable argument)
  → Dec (Runnable (E-App (E-Val function) argument))
decide-app-value function argument (yes head) right? =
  yes (app-head-runs head)
decide-app-value function argument (no not-head) (yes runnable) =
  yes (app-right-runs-d runnable)
decide-app-value function argument
    (no not-head) (no not-runnable) =
  no λ outer →
    refute-sum not-head not-runnable
      (app-runnable-invert outer)

decide-tapp-function :
  ∀ {n K} {function : Expr [] n} {argument : NfTy [] K}
  → (IsValue function → ⊥)
  → Dec (Runnable function)
  → Dec (Runnable (E-TApp function argument))
decide-tapp-function not-value (yes runnable) =
  yes (tapp-runs-d runnable)
decide-tapp-function not-value (no not-runnable) =
  no λ outer →
    not-runnable
      (tapp-function-runnable-invert not-value outer)

decide-tapp-value :
  ∀ {n K} (function : Value [] n) (argument : NfTy [] K)
  → Dec (TAppHeadRunnable function argument)
  → Dec (Runnable (E-TApp (E-Val function) argument))
decide-tapp-value function argument (yes head) =
  yes (tapp-head-runs head)
decide-tapp-value function argument (no not-head) =
  no λ outer → not-head (tapp-runnable-invert outer)

decide-pair-left :
  ∀ {n} {left right : Expr [] n}
  → (IsValue left → ⊥)
  → Dec (Runnable left)
  → Dec (Runnable (E-Pair left right))
decide-pair-left not-value (yes runnable) =
  yes (pair-left-runs-d runnable)
decide-pair-left not-value (no not-runnable) =
  no λ outer →
    not-runnable (pair-left-runnable-invert not-value outer)

decide-pair-value :
  ∀ {n} (first : Value [] n) (second : Expr [] n)
  → Dec (IsValue second)
  → Dec (Runnable second)
  → Dec (Runnable (E-Pair (E-Val first) second))
decide-pair-value first .(E-Val second)
    (yes (is-value second)) decision =
  yes (run-β Act-PairV)
decide-pair-value first second
    (no not-value) (yes runnable) =
  yes (pair-right-runs-d runnable)
decide-pair-value first second
    (no not-value) (no not-runnable) =
  no λ outer →
    refute-sum not-value not-runnable
      (pair-right-runnable-invert outer)

decide-let-pair :
  ∀ {n} (first : Expr [] n) (body : Expr [] (suc (suc n)))
  → Dec (PairValue first)
  → Dec (Runnable first)
  → Dec (Runnable (E-LetPair first body))
decide-let-pair (E-Val (V-Pair first second)) body
    (yes pair-value) decision =
  yes (run-β Act-LetPair)
decide-let-pair first body
    (no not-pair) (yes runnable) =
  yes (let-pair-runs-d runnable)
decide-let-pair first body
    (no not-pair) (no not-runnable) =
  no λ outer →
    not-runnable
      (let-pair-runnable-invert not-pair outer)

decide-let-unit :
  ∀ {n} (first second : Expr [] n)
  → Dec (UnitValue first)
  → Dec (Runnable first)
  → Dec (Runnable (E-LetUnit first second))
decide-let-unit (E-Val (V-Const C-Unit)) second
    (yes unit-value) decision =
  yes (run-β Act-LetUnit)
decide-let-unit first second
    (no not-unit) (yes runnable) =
  yes (let-unit-runs-d runnable)
decide-let-unit first second
    (no not-unit) (no not-runnable) =
  no λ outer →
    not-runnable
      (let-unit-runnable-invert not-unit outer)

runnable? (E-Val value) = no value-not-runnable
runnable? (E-App left right)
  with is-value? left
... | no not-value =
  decide-app-left not-value (runnable? left)
... | yes (is-value function) =
  decide-app-value function right
    (app-head-runnable? function right)
    (runnable? right)
runnable? (E-TApp function argument)
  with is-value? function
... | no not-value =
  decide-tapp-function not-value (runnable? function)
... | yes (is-value value) =
  decide-tapp-value value argument
    (tapp-head-runnable? value argument)
runnable? (E-Pair left right)
  with is-value? left
... | no not-value =
  decide-pair-left not-value (runnable? left)
... | yes (is-value first) =
  decide-pair-value first right
    (is-value? right)
    (runnable? right)
runnable? (E-LetPair first body) =
  decide-let-pair first body
    (pair-value? first)
    (runnable? first)
runnable? (E-LetUnit first second) =
  decide-let-unit first second
    (unit-value? first)
    (runnable? first)
runnable? (E-Match scrutinee ne branches)
  with runnable? scrutinee
... | yes runnable = yes (match-runs-d runnable)
... | no not-runnable =
  no λ outer →
    not-runnable (match-runnable-invert outer)

runnable-at? : ∀ {n} (C : Conf n) → Dec (RunnableAt C)
runnable-at? C
  with any-fin? (λ i → runnable? (lookup C i))
... | yes (i , runnable) = yes (runnable-at i runnable)
... | no none = no λ where
  (runnable-at i runnable) → none (i , runnable)

------------------------------------------------------------------------
-- Fixed incoming actions

data InputLabel {n : ℕ} : Label n [] → Set where
  input-message : ∀ {x v} → InputLabel (L-RecvVal x v)
  input-branch : ∀ {k} {x : Fin n} {i : Fin k}
    → InputLabel (L-RecvLab x i)
  input-close : ∀ {x} → InputLabel (L-Close x)

record Accepts {n : ℕ}
    (e : Expr [] n) (label : Label n []) : Set where
  constructor accepts
  field
    target : Expr [] n
    transition : e —[ label ]→ target

data AppInputHead {n : ℕ} :
    (function : Value [] n)
    (argument : Expr [] n)
    (label : Label n [])
    → Set where
  input-head-message : ∀ {pk}
      {T : NfTy [] (KV pk Lin)} {S : NfTy [] SLin}
      {x : Fin n} {v : Value [] n}
    → AppInputHead
        (V-Receive₂ T S)
        (E-Val (V-Var x))
        (L-RecvVal x v)
  input-head-close : ∀ {x : Fin n}
    → AppInputHead
        (V-Const C-Close)
        (E-Val (V-Var x))
        (L-Close x)

app-input-head? :
  ∀ {n} (function : Value [] n) (argument : Expr [] n)
    {label : Label n []}
  → InputLabel label
  → Dec (AppInputHead function argument label)
app-input-head? (V-Receive₂ T S) (E-Val (V-Var y))
    {label = L-RecvVal x v} input-message
  with x ≟Fin y
... | yes refl = yes input-head-message
... | no x≢y = no λ where
  input-head-message → x≢y refl
app-input-head? (V-Const C-Close) (E-Val (V-Var y))
    {label = L-Close x} input-close
  with x ≟Fin y
... | yes refl = yes input-head-close
... | no x≢y = no λ where
  input-head-close → x≢y refl
app-input-head? (V-Receive₂ T S) (E-Val (V-Const constant))
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-Val (V-Abs U body))
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-Val (V-Rec U V body))
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-Val (V-TAbs K body))
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-Val (V-Pair first second))
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-Val (V-Receive₁ U))
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-Val (V-Receive₂ U V))
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-Val (V-Send₁ U))
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-Val (V-Send₂ U V))
    input-message = no λ ()
app-input-head? (V-Receive₂ T S)
    (E-Val (V-Select₁ variance i P)) input-message = no λ ()
app-input-head? (V-Receive₂ T S)
    (E-Val (V-Select₂ variance i P U)) input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-App left right)
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-TApp function argument)
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-LetUnit first second)
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-Pair first second)
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-LetPair first body)
    input-message = no λ ()
app-input-head? (V-Receive₂ T S) (E-Match e ne branches)
    input-message = no λ ()
app-input-head? (V-Const constant) argument input-message =
  no λ ()
app-input-head? (V-Var x) argument input-message = no λ ()
app-input-head? (V-Abs T body) argument input-message = no λ ()
app-input-head? (V-Rec T U body) argument input-message = no λ ()
app-input-head? (V-TAbs K body) argument input-message = no λ ()
app-input-head? (V-Pair first second) argument input-message = no λ ()
app-input-head? (V-Receive₁ T) argument input-message = no λ ()
app-input-head? (V-Send₁ T) argument input-message = no λ ()
app-input-head? (V-Send₂ T S) argument input-message = no λ ()
app-input-head? (V-Select₁ variance i P) argument input-message =
  no λ ()
app-input-head? (V-Select₂ variance i P S) argument input-message =
  no λ ()
app-input-head? function argument input-branch = no λ ()
app-input-head? (V-Const C-Close) (E-Val (V-Const constant))
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-Val (V-Abs T body))
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-Val (V-Rec T U body))
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-Val (V-TAbs K body))
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-Val (V-Pair first second))
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-Val (V-Receive₁ T))
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-Val (V-Receive₂ T S))
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-Val (V-Send₁ T))
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-Val (V-Send₂ T S))
    input-close = no λ ()
app-input-head? (V-Const C-Close)
    (E-Val (V-Select₁ variance i P)) input-close = no λ ()
app-input-head? (V-Const C-Close)
    (E-Val (V-Select₂ variance i P S)) input-close = no λ ()
app-input-head? (V-Const C-Close) (E-App left right)
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-TApp function argument)
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-LetUnit first second)
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-Pair first second)
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-LetPair first body)
    input-close = no λ ()
app-input-head? (V-Const C-Close) (E-Match e ne branches)
    input-close = no λ ()
app-input-head? (V-Const C-Unit) argument input-close = no λ ()
app-input-head? (V-Const C-Fork) argument input-close = no λ ()
app-input-head? (V-Const C-New) argument input-close = no λ ()
app-input-head? (V-Const C-Receive) argument input-close = no λ ()
app-input-head? (V-Const C-Send) argument input-close = no λ ()
app-input-head? (V-Const (C-Select variance i)) argument input-close =
  no λ ()
app-input-head? (V-Var x) argument input-close = no λ ()
app-input-head? (V-Abs T body) argument input-close = no λ ()
app-input-head? (V-Rec T U body) argument input-close = no λ ()
app-input-head? (V-TAbs K body) argument input-close = no λ ()
app-input-head? (V-Pair first second) argument input-close = no λ ()
app-input-head? (V-Receive₁ T) argument input-close = no λ ()
app-input-head? (V-Receive₂ T S) argument input-close = no λ ()
app-input-head? (V-Send₁ T) argument input-close = no λ ()
app-input-head? (V-Send₂ T S) argument input-close = no λ ()
app-input-head? (V-Select₁ variance i P) argument input-close =
  no λ ()
app-input-head? (V-Select₂ variance i P S) argument input-close =
  no λ ()

app-input-head-accepts :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
    {label : Label n []}
  → AppInputHead function argument label
  → Accepts (E-App (E-Val function) argument) label
app-input-head-accepts input-head-message =
  accepts _ Act-Rcv
app-input-head-accepts input-head-close =
  accepts _ Act-Close

app-value-accepts-invert :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
    {label : Label n []}
  → InputLabel label
  → Accepts (E-App (E-Val function) argument) label
  → AppInputHead function argument label ⊎ Accepts argument label
app-value-accepts-invert input-message (accepts _ Act-Rcv) =
  inj₁ input-head-message
app-value-accepts-invert input-message
    (accepts _ (Act-AppR step)) =
  inj₂ (accepts _ step)
app-value-accepts-invert input-branch
    (accepts _ (Act-AppR step)) =
  inj₂ (accepts _ step)
app-value-accepts-invert input-close (accepts _ Act-Close) =
  inj₁ input-head-close
app-value-accepts-invert input-close
    (accepts _ (Act-AppR step)) =
  inj₂ (accepts _ step)

app-left-accepts-invert :
  ∀ {n} {left right : Expr [] n} {label : Label n []}
  → InputLabel label
  → (IsValue left → ⊥)
  → Accepts (E-App left right) label
  → Accepts left label
app-left-accepts-invert input not-value
    (accepts _ (Act-AppL step)) =
  accepts _ step
app-left-accepts-invert input not-value
    (accepts _ (Act-AppR step)) =
  ⊥-elim (not-value (is-value _))
app-left-accepts-invert input-message not-value
    (accepts _ Act-Rcv) =
  ⊥-elim (not-value (is-value _))
app-left-accepts-invert input-close not-value
    (accepts _ Act-Close) =
  ⊥-elim (not-value (is-value _))

app-left-accepts :
  ∀ {n} {left right : Expr [] n} {label : Label n []}
  → Accepts left label
  → Accepts (E-App left right) label
app-left-accepts (accepts _ step) =
  accepts _ (Act-AppL step)

app-right-accepts :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
    {label : Label n []}
  → Accepts argument label
  → Accepts (E-App (E-Val function) argument) label
app-right-accepts (accepts _ step) =
  accepts _ (Act-AppR step)

decide-app-left-input :
  ∀ {n} {left right : Expr [] n} {label : Label n []}
  → InputLabel label
  → (IsValue left → ⊥)
  → Dec (Accepts left label)
  → Dec (Accepts (E-App left right) label)
decide-app-left-input input not-value (yes acceptance) =
  yes (app-left-accepts acceptance)
decide-app-left-input input not-value (no no-acceptance) =
  no λ outer →
    no-acceptance
      (app-left-accepts-invert input not-value outer)

decide-app-value-input :
  ∀ {n} (function : Value [] n) (argument : Expr [] n)
    {label : Label n []}
  → InputLabel label
  → Dec (AppInputHead function argument label)
  → Dec (Accepts argument label)
  → Dec (Accepts (E-App (E-Val function) argument) label)
decide-app-value-input function argument input
    (yes head) right? =
  yes (app-input-head-accepts head)
decide-app-value-input function argument input
    (no not-head) (yes acceptance) =
  yes (app-right-accepts acceptance)
decide-app-value-input function argument input
    (no not-head) (no no-acceptance) =
  no λ outer →
    refute-sum not-head no-acceptance
      (app-value-accepts-invert input outer)

tapp-accepts :
  ∀ {n K} {function : Expr [] n} {argument : NfTy [] K}
    {label : Label n []}
  → Accepts function label
  → Accepts (E-TApp function argument) label
tapp-accepts (accepts _ step) =
  accepts _ (Act-TAppE step)

tapp-accepts-invert :
  ∀ {n K} {function : Expr [] n} {argument : NfTy [] K}
    {label : Label n []}
  → InputLabel label
  → Accepts (E-TApp function argument) label
  → Accepts function label
tapp-accepts-invert input
    (accepts _ (Act-TAppE step)) =
  accepts _ step

pair-left-accepts :
  ∀ {n} {left right : Expr [] n} {label : Label n []}
  → Accepts left label
  → Accepts (E-Pair left right) label
pair-left-accepts (accepts _ step) =
  accepts _ (Act-PairL step)

pair-right-accepts :
  ∀ {n} {first : Value [] n} {second : Expr [] n}
    {label : Label n []}
  → Accepts second label
  → Accepts (E-Pair (E-Val first) second) label
pair-right-accepts (accepts _ step) =
  accepts _ (Act-PairR step)

pair-left-accepts-invert :
  ∀ {n} {left right : Expr [] n} {label : Label n []}
  → InputLabel label
  → (IsValue left → ⊥)
  → Accepts (E-Pair left right) label
  → Accepts left label
pair-left-accepts-invert input not-value
    (accepts _ (Act-PairL step)) =
  accepts _ step
pair-left-accepts-invert input not-value
    (accepts _ (Act-PairR step)) =
  ⊥-elim (not-value (is-value _))

pair-right-accepts-invert :
  ∀ {n} {first : Value [] n} {second : Expr [] n}
    {label : Label n []}
  → InputLabel label
  → Accepts (E-Pair (E-Val first) second) label
  → Accepts second label
pair-right-accepts-invert input
    (accepts _ (Act-PairR step)) =
  accepts _ step

decide-pair-left-input :
  ∀ {n} {left right : Expr [] n} {label : Label n []}
  → InputLabel label
  → (IsValue left → ⊥)
  → Dec (Accepts left label)
  → Dec (Accepts (E-Pair left right) label)
decide-pair-left-input input not-value (yes acceptance) =
  yes (pair-left-accepts acceptance)
decide-pair-left-input input not-value (no no-acceptance) =
  no λ outer →
    no-acceptance
      (pair-left-accepts-invert input not-value outer)

decide-pair-right-input :
  ∀ {n} {first : Value [] n} {second : Expr [] n}
    {label : Label n []}
  → InputLabel label
  → Dec (Accepts second label)
  → Dec (Accepts (E-Pair (E-Val first) second) label)
decide-pair-right-input input (yes acceptance) =
  yes (pair-right-accepts acceptance)
decide-pair-right-input input (no no-acceptance) =
  no λ outer →
    no-acceptance (pair-right-accepts-invert input outer)

match-accepts :
  ∀ {n k} {ss : Subset.Subset k}
    {scrutinee : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
    {label : Label n []}
  → Accepts scrutinee label
  → Accepts (E-Match scrutinee ne branches) label
match-accepts (accepts _ step) =
  accepts _ (Act-MatchE step)

data MatchInputHead {n : ℕ} :
    ∀ {k} {ss : Subset.Subset k}
    → (scrutinee : Expr [] n)
    → (ne : Subset.Nonempty ss)
    → ((i : Fin k) → i Subset.∈ ss → Expr [] (suc n))
    → Label n []
    → Set where
  input-head-branch :
    ∀ {k} {ss : Subset.Subset k} {ne : Subset.Nonempty ss}
      {x : Fin n} {i : Fin k}
      {branches : (j : Fin k) → j Subset.∈ ss → Expr [] (suc n)}
    → (i∈ : i Subset.∈ ss)
    → MatchInputHead
        (E-Val (V-Var x)) ne branches (L-RecvLab x i)

match-input-head? :
  ∀ {n k} {ss : Subset.Subset k}
    (scrutinee : Expr [] n)
    (ne : Subset.Nonempty ss)
    (branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n))
    {label : Label n []}
  → InputLabel label
  → Dec (MatchInputHead scrutinee ne branches label)
match-input-head? {k = k} (E-Val (V-Var y)) ne branches
    {label = L-RecvLab {k = k′} x i} input-branch
  with k ≟Nat k′
... | no k≢k′ = no λ where
  (input-head-branch i∈) → k≢k′ refl
... | yes refl with x ≟Fin y
... | no x≢y = no λ where
  (input-head-branch i∈) → x≢y refl
... | yes refl with subset-member? i _
... | yes i∈ = yes (input-head-branch i∈)
... | no i∉ = no λ where
  (input-head-branch i∈) → i∉ i∈
match-input-head? (E-Val (V-Const constant)) ne branches
    input-branch = no λ ()
match-input-head? (E-Val (V-Abs T body)) ne branches
    input-branch = no λ ()
match-input-head? (E-Val (V-Rec T U body)) ne branches
    input-branch = no λ ()
match-input-head? (E-Val (V-TAbs K body)) ne branches
    input-branch = no λ ()
match-input-head? (E-Val (V-Pair first second)) ne branches
    input-branch = no λ ()
match-input-head? (E-Val (V-Receive₁ T)) ne branches
    input-branch = no λ ()
match-input-head? (E-Val (V-Receive₂ T S)) ne branches
    input-branch = no λ ()
match-input-head? (E-Val (V-Send₁ T)) ne branches
    input-branch = no λ ()
match-input-head? (E-Val (V-Send₂ T S)) ne branches
    input-branch = no λ ()
match-input-head? (E-Val (V-Select₁ variance i P)) ne branches
    input-branch = no λ ()
match-input-head?
    (E-Val (V-Select₂ variance i P S)) ne branches
    input-branch = no λ ()
match-input-head? (E-App left right) ne branches
    input-branch = no λ ()
match-input-head? (E-TApp function argument) ne branches
    input-branch = no λ ()
match-input-head? (E-LetUnit first second) ne branches
    input-branch = no λ ()
match-input-head? (E-Pair first second) ne branches
    input-branch = no λ ()
match-input-head? (E-LetPair first body) ne branches
    input-branch = no λ ()
match-input-head? (E-Match scrutinee ne′ branches′) ne branches
    input-branch = no λ ()
match-input-head? scrutinee ne branches input-message =
  no λ ()
match-input-head? scrutinee ne branches input-close =
  no λ ()

match-input-head-accepts :
  ∀ {n k} {ss : Subset.Subset k}
    {scrutinee : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
    {label : Label n []}
  → MatchInputHead scrutinee ne branches label
  → Accepts (E-Match scrutinee ne branches) label
match-input-head-accepts (input-head-branch i∈) =
  accepts _ (Act-Match i∈)

match-accepts-invert :
  ∀ {n k} {ss : Subset.Subset k}
    {scrutinee : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
    {label : Label n []}
  → InputLabel label
  → Accepts (E-Match scrutinee ne branches) label
  → MatchInputHead scrutinee ne branches label
      ⊎ Accepts scrutinee label
match-accepts-invert input-branch
    (accepts _ (Act-Match i∈)) =
  inj₁ (input-head-branch i∈)
match-accepts-invert input
    (accepts _ (Act-MatchE step)) =
  inj₂ (accepts _ step)

decide-match-input :
  ∀ {n k} {ss : Subset.Subset k}
    (scrutinee : Expr [] n)
    (ne : Subset.Nonempty ss)
    (branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n))
    {label : Label n []}
  → InputLabel label
  → Dec (MatchInputHead scrutinee ne branches label)
  → Dec (Accepts scrutinee label)
  → Dec (Accepts (E-Match scrutinee ne branches) label)
decide-match-input scrutinee ne branches input
    (yes head) inner? =
  yes (match-input-head-accepts head)
decide-match-input scrutinee ne branches input
    (no not-head) (yes acceptance) =
  yes (match-accepts acceptance)
decide-match-input scrutinee ne branches input
    (no not-head) (no no-acceptance) =
  no λ outer →
    refute-sum not-head no-acceptance
      (match-accepts-invert input outer)

let-pair-accepts :
  ∀ {n} {first : Expr [] n} {body : Expr [] (suc (suc n))}
    {label : Label n []}
  → Accepts first label
  → Accepts (E-LetPair first body) label
let-pair-accepts (accepts _ step) =
  accepts _ (Act-LetPairE step)

let-pair-accepts-invert :
  ∀ {n} {first : Expr [] n} {body : Expr [] (suc (suc n))}
    {label : Label n []}
  → InputLabel label
  → Accepts (E-LetPair first body) label
  → Accepts first label
let-pair-accepts-invert input
    (accepts _ (Act-LetPairE step)) =
  accepts _ step

let-unit-accepts :
  ∀ {n} {first second : Expr [] n} {label : Label n []}
  → Accepts first label
  → Accepts (E-LetUnit first second) label
let-unit-accepts (accepts _ step) =
  accepts _ (Act-LetUnitE step)

let-unit-accepts-invert :
  ∀ {n} {first second : Expr [] n} {label : Label n []}
  → InputLabel label
  → Accepts (E-LetUnit first second) label
  → Accepts first label
let-unit-accepts-invert input
    (accepts _ (Act-LetUnitE step)) =
  accepts _ step

accepts? :
  ∀ {n} (e : Expr [] n) {label : Label n []}
  → InputLabel label
  → Dec (Accepts e label)
accepts? (E-Val value) input = no λ where
  (accepts _ ())
accepts? (E-App left right) input with is-value? left
... | no not-value =
  decide-app-left-input input not-value
    (accepts? left input)
... | yes (is-value function) =
  decide-app-value-input function right input
    (app-input-head? function right input)
    (accepts? right input)
accepts? (E-TApp function argument) input
  with accepts? function input
... | yes acceptance = yes (tapp-accepts acceptance)
... | no no-acceptance =
  no λ outer →
    no-acceptance (tapp-accepts-invert input outer)
accepts? (E-Pair left right) input with is-value? left
... | no not-value =
  decide-pair-left-input input not-value
    (accepts? left input)
... | yes (is-value first) =
  decide-pair-right-input input
    (accepts? right input)
accepts? (E-Match scrutinee ne branches) input =
  decide-match-input scrutinee ne branches input
    (match-input-head? scrutinee ne branches input)
    (accepts? scrutinee input)
accepts? (E-LetPair first body) input
  with accepts? first input
... | yes acceptance = yes (let-pair-accepts acceptance)
... | no no-acceptance =
  no λ outer →
    no-acceptance (let-pair-accepts-invert input outer)
accepts? (E-LetUnit first second) input
  with accepts? first input
... | yes acceptance = yes (let-unit-accepts acceptance)
... | no no-acceptance =
  no λ outer →
    no-acceptance (let-unit-accepts-invert input outer)

------------------------------------------------------------------------
-- The unique outgoing communication of an expression

data Output {n : ℕ} : Expr [] n → Set where
  output-message : ∀ {e e′ : Expr [] n}
      {y : Fin n} {v : Value [] n}
    → e —[ L-SendVal y v ]→ e′
    → Output e
  output-branch : ∀ {k} {e e′ : Expr [] n}
      {y : Fin n} {i : Fin k}
    → e —[ L-SendLab y i ]→ e′
    → Output e
  output-close : ∀ {e e′ : Expr [] n} {y : Fin n}
    → e —[ L-Close y ]→ e′
    → Output e

data SendArgument {n : ℕ} : Expr [] n → Set where
  send-argument : ∀ {payload : Value [] n} {channel : Fin n}
    → SendArgument
        (E-Val (V-Pair payload (V-Var channel)))

send-argument? :
  ∀ {n} (argument : Expr [] n)
  → Dec (SendArgument argument)
send-argument? (E-Val (V-Pair payload (V-Var channel))) =
  yes send-argument
send-argument? (E-Val (V-Pair payload (V-Const constant))) =
  no λ ()
send-argument? (E-Val (V-Pair payload (V-Abs T body))) =
  no λ ()
send-argument? (E-Val (V-Pair payload (V-Rec T U body))) =
  no λ ()
send-argument? (E-Val (V-Pair payload (V-TAbs K body))) =
  no λ ()
send-argument? (E-Val (V-Pair payload (V-Pair first second))) =
  no λ ()
send-argument? (E-Val (V-Pair payload (V-Receive₁ T))) =
  no λ ()
send-argument? (E-Val (V-Pair payload (V-Receive₂ T S))) =
  no λ ()
send-argument? (E-Val (V-Pair payload (V-Send₁ T))) =
  no λ ()
send-argument? (E-Val (V-Pair payload (V-Send₂ T S))) =
  no λ ()
send-argument?
    (E-Val (V-Pair payload (V-Select₁ variance i P))) =
  no λ ()
send-argument?
    (E-Val (V-Pair payload (V-Select₂ variance i P S))) =
  no λ ()
send-argument? (E-Val (V-Const constant)) = no λ ()
send-argument? (E-Val (V-Var x)) = no λ ()
send-argument? (E-Val (V-Abs T body)) = no λ ()
send-argument? (E-Val (V-Rec T U body)) = no λ ()
send-argument? (E-Val (V-TAbs K body)) = no λ ()
send-argument? (E-Val (V-Receive₁ T)) = no λ ()
send-argument? (E-Val (V-Receive₂ T S)) = no λ ()
send-argument? (E-Val (V-Send₁ T)) = no λ ()
send-argument? (E-Val (V-Send₂ T S)) = no λ ()
send-argument? (E-Val (V-Select₁ variance i P)) = no λ ()
send-argument? (E-Val (V-Select₂ variance i P S)) = no λ ()
send-argument? (E-App left right) = no λ ()
send-argument? (E-TApp function argument) = no λ ()
send-argument? (E-LetUnit first second) = no λ ()
send-argument? (E-Pair first second) = no λ ()
send-argument? (E-LetPair first body) = no λ ()
send-argument? (E-Match scrutinee ne branches) = no λ ()

data VariableArgument {n : ℕ} : Expr [] n → Set where
  variable-argument : ∀ {channel : Fin n}
    → VariableArgument (E-Val (V-Var channel))

variable-argument? :
  ∀ {n} (argument : Expr [] n)
  → Dec (VariableArgument argument)
variable-argument? (E-Val (V-Var channel)) =
  yes variable-argument
variable-argument? (E-Val (V-Const constant)) = no λ ()
variable-argument? (E-Val (V-Abs T body)) = no λ ()
variable-argument? (E-Val (V-Rec T U body)) = no λ ()
variable-argument? (E-Val (V-TAbs K body)) = no λ ()
variable-argument? (E-Val (V-Pair first second)) = no λ ()
variable-argument? (E-Val (V-Receive₁ T)) = no λ ()
variable-argument? (E-Val (V-Receive₂ T S)) = no λ ()
variable-argument? (E-Val (V-Send₁ T)) = no λ ()
variable-argument? (E-Val (V-Send₂ T S)) = no λ ()
variable-argument? (E-Val (V-Select₁ variance i P)) = no λ ()
variable-argument? (E-Val (V-Select₂ variance i P S)) = no λ ()
variable-argument? (E-App left right) = no λ ()
variable-argument? (E-TApp function argument) = no λ ()
variable-argument? (E-LetUnit first second) = no λ ()
variable-argument? (E-Pair first second) = no λ ()
variable-argument? (E-LetPair first body) = no λ ()
variable-argument? (E-Match scrutinee ne branches) = no λ ()

data AppOutputHead {n : ℕ} :
    Value [] n → Expr [] n → Set where
  output-head-message : ∀ {pk}
      {T : NfTy [] (KV pk Lin)} {S : NfTy [] SLin}
      {payload : Value [] n} {channel : Fin n}
    → AppOutputHead
        (V-Send₂ T S)
        (E-Val (V-Pair payload (V-Var channel)))
  output-head-branch : ∀ {k} {variance} {i : Fin k}
      {P : NfTy [] KP} {S : NfTy [] SLin}
      {channel : Fin n}
    → AppOutputHead
        (V-Select₂ variance i P S)
        (E-Val (V-Var channel))
  output-head-close : ∀ {channel : Fin n}
    → AppOutputHead
        (V-Const C-Close)
        (E-Val (V-Var channel))

app-output-head? :
  ∀ {n} (function : Value [] n) (argument : Expr [] n)
  → Dec (AppOutputHead function argument)
app-output-head? (V-Send₂ T S) argument
  with send-argument? argument
... | yes send-argument = yes output-head-message
... | no not-send = no λ where
  output-head-message → not-send send-argument
app-output-head? (V-Select₂ variance i P S) argument
  with variable-argument? argument
... | yes variable-argument = yes output-head-branch
... | no not-variable = no λ where
  output-head-branch → not-variable variable-argument
app-output-head? (V-Const C-Close) argument
  with variable-argument? argument
... | yes variable-argument = yes output-head-close
... | no not-variable = no λ where
  output-head-close → not-variable variable-argument
app-output-head? (V-Const C-Unit) argument = no λ ()
app-output-head? (V-Const C-Fork) argument = no λ ()
app-output-head? (V-Const C-New) argument = no λ ()
app-output-head? (V-Const C-Receive) argument = no λ ()
app-output-head? (V-Const C-Send) argument = no λ ()
app-output-head? (V-Const (C-Select variance i)) argument =
  no λ ()
app-output-head? (V-Var x) argument = no λ ()
app-output-head? (V-Abs T body) argument = no λ ()
app-output-head? (V-Rec T U body) argument = no λ ()
app-output-head? (V-TAbs K body) argument = no λ ()
app-output-head? (V-Pair first second) argument = no λ ()
app-output-head? (V-Receive₁ T) argument = no λ ()
app-output-head? (V-Receive₂ T S) argument = no λ ()
app-output-head? (V-Send₁ T) argument = no λ ()
app-output-head? (V-Select₁ variance i P) argument = no λ ()

app-output-head-output :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
  → AppOutputHead function argument
  → Output (E-App (E-Val function) argument)
app-output-head-output output-head-message =
  output-message Act-Send
app-output-head-output output-head-branch =
  output-branch Act-Sel
app-output-head-output output-head-close =
  output-close Act-Close

app-value-output-invert :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
  → Output (E-App (E-Val function) argument)
  → AppOutputHead function argument ⊎ Output argument
app-value-output-invert (output-message Act-Send) =
  inj₁ output-head-message
app-value-output-invert
    (output-message (Act-AppR step)) =
  inj₂ (output-message step)
app-value-output-invert (output-branch Act-Sel) =
  inj₁ output-head-branch
app-value-output-invert
    (output-branch (Act-AppR step)) =
  inj₂ (output-branch step)
app-value-output-invert (output-close Act-Close) =
  inj₁ output-head-close
app-value-output-invert
    (output-close (Act-AppR step)) =
  inj₂ (output-close step)

app-left-output-invert :
  ∀ {n} {left right : Expr [] n}
  → (IsValue left → ⊥)
  → Output (E-App left right)
  → Output left
app-left-output-invert not-value
    (output-message Act-Send) =
  ⊥-elim (not-value (is-value _))
app-left-output-invert not-value
    (output-message (Act-AppL step)) =
  output-message step
app-left-output-invert not-value
    (output-message (Act-AppR step)) =
  ⊥-elim (not-value (is-value _))
app-left-output-invert not-value
    (output-branch Act-Sel) =
  ⊥-elim (not-value (is-value _))
app-left-output-invert not-value
    (output-branch (Act-AppL step)) =
  output-branch step
app-left-output-invert not-value
    (output-branch (Act-AppR step)) =
  ⊥-elim (not-value (is-value _))
app-left-output-invert not-value
    (output-close Act-Close) =
  ⊥-elim (not-value (is-value _))
app-left-output-invert not-value
    (output-close (Act-AppL step)) =
  output-close step
app-left-output-invert not-value
    (output-close (Act-AppR step)) =
  ⊥-elim (not-value (is-value _))

app-left-output :
  ∀ {n} {left right : Expr [] n}
  → Output left
  → Output (E-App left right)
app-left-output (output-message step) =
  output-message (Act-AppL step)
app-left-output (output-branch step) =
  output-branch (Act-AppL step)
app-left-output (output-close step) =
  output-close (Act-AppL step)

app-right-output :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
  → Output argument
  → Output (E-App (E-Val function) argument)
app-right-output (output-message step) =
  output-message (Act-AppR step)
app-right-output (output-branch step) =
  output-branch (Act-AppR step)
app-right-output (output-close step) =
  output-close (Act-AppR step)

decide-app-left-output :
  ∀ {n} {left right : Expr [] n}
  → (IsValue left → ⊥)
  → Dec (Output left)
  → Dec (Output (E-App left right))
decide-app-left-output not-value (yes output) =
  yes (app-left-output output)
decide-app-left-output not-value (no no-output) =
  no λ outer →
    no-output (app-left-output-invert not-value outer)

decide-app-value-output :
  ∀ {n} (function : Value [] n) (argument : Expr [] n)
  → Dec (AppOutputHead function argument)
  → Dec (Output argument)
  → Dec (Output (E-App (E-Val function) argument))
decide-app-value-output function argument
    (yes head) right? =
  yes (app-output-head-output head)
decide-app-value-output function argument
    (no not-head) (yes output) =
  yes (app-right-output output)
decide-app-value-output function argument
    (no not-head) (no no-output) =
  no λ outer →
    refute-sum not-head no-output
      (app-value-output-invert outer)

tapp-output :
  ∀ {n K} {function : Expr [] n} {argument : NfTy [] K}
  → Output function
  → Output (E-TApp function argument)
tapp-output (output-message step) =
  output-message (Act-TAppE step)
tapp-output (output-branch step) =
  output-branch (Act-TAppE step)
tapp-output (output-close step) =
  output-close (Act-TAppE step)

tapp-output-invert :
  ∀ {n K} {function : Expr [] n} {argument : NfTy [] K}
  → Output (E-TApp function argument)
  → Output function
tapp-output-invert
    (output-message (Act-TAppE step)) =
  output-message step
tapp-output-invert
    (output-branch (Act-TAppE step)) =
  output-branch step
tapp-output-invert
    (output-close (Act-TAppE step)) =
  output-close step

pair-left-output :
  ∀ {n} {left right : Expr [] n}
  → Output left
  → Output (E-Pair left right)
pair-left-output (output-message step) =
  output-message (Act-PairL step)
pair-left-output (output-branch step) =
  output-branch (Act-PairL step)
pair-left-output (output-close step) =
  output-close (Act-PairL step)

pair-right-output :
  ∀ {n} {first : Value [] n} {second : Expr [] n}
  → Output second
  → Output (E-Pair (E-Val first) second)
pair-right-output (output-message step) =
  output-message (Act-PairR step)
pair-right-output (output-branch step) =
  output-branch (Act-PairR step)
pair-right-output (output-close step) =
  output-close (Act-PairR step)

pair-left-output-invert :
  ∀ {n} {left right : Expr [] n}
  → (IsValue left → ⊥)
  → Output (E-Pair left right)
  → Output left
pair-left-output-invert not-value
    (output-message (Act-PairL step)) =
  output-message step
pair-left-output-invert not-value
    (output-message (Act-PairR step)) =
  ⊥-elim (not-value (is-value _))
pair-left-output-invert not-value
    (output-branch (Act-PairL step)) =
  output-branch step
pair-left-output-invert not-value
    (output-branch (Act-PairR step)) =
  ⊥-elim (not-value (is-value _))
pair-left-output-invert not-value
    (output-close (Act-PairL step)) =
  output-close step
pair-left-output-invert not-value
    (output-close (Act-PairR step)) =
  ⊥-elim (not-value (is-value _))

pair-right-output-invert :
  ∀ {n} {first : Value [] n} {second : Expr [] n}
  → Output (E-Pair (E-Val first) second)
  → Output second
pair-right-output-invert
    (output-message (Act-PairR step)) =
  output-message step
pair-right-output-invert
    (output-branch (Act-PairR step)) =
  output-branch step
pair-right-output-invert
    (output-close (Act-PairR step)) =
  output-close step

decide-pair-left-output :
  ∀ {n} {left right : Expr [] n}
  → (IsValue left → ⊥)
  → Dec (Output left)
  → Dec (Output (E-Pair left right))
decide-pair-left-output not-value (yes output) =
  yes (pair-left-output output)
decide-pair-left-output not-value (no no-output) =
  no λ outer →
    no-output (pair-left-output-invert not-value outer)

decide-pair-right-output :
  ∀ {n} {first : Value [] n} {second : Expr [] n}
  → Dec (Output second)
  → Dec (Output (E-Pair (E-Val first) second))
decide-pair-right-output (yes output) =
  yes (pair-right-output output)
decide-pair-right-output (no no-output) =
  no λ outer →
    no-output (pair-right-output-invert outer)

match-output :
  ∀ {n k} {ss : Subset.Subset k}
    {scrutinee : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
  → Output scrutinee
  → Output (E-Match scrutinee ne branches)
match-output (output-message step) =
  output-message (Act-MatchE step)
match-output (output-branch step) =
  output-branch (Act-MatchE step)
match-output (output-close step) =
  output-close (Act-MatchE step)

match-output-invert :
  ∀ {n k} {ss : Subset.Subset k}
    {scrutinee : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
  → Output (E-Match scrutinee ne branches)
  → Output scrutinee
match-output-invert
    (output-message (Act-MatchE step)) =
  output-message step
match-output-invert
    (output-branch (Act-MatchE step)) =
  output-branch step
match-output-invert
    (output-close (Act-MatchE step)) =
  output-close step

let-pair-output :
  ∀ {n} {first : Expr [] n} {body : Expr [] (suc (suc n))}
  → Output first
  → Output (E-LetPair first body)
let-pair-output (output-message step) =
  output-message (Act-LetPairE step)
let-pair-output (output-branch step) =
  output-branch (Act-LetPairE step)
let-pair-output (output-close step) =
  output-close (Act-LetPairE step)

let-pair-output-invert :
  ∀ {n} {first : Expr [] n} {body : Expr [] (suc (suc n))}
  → Output (E-LetPair first body)
  → Output first
let-pair-output-invert
    (output-message (Act-LetPairE step)) =
  output-message step
let-pair-output-invert
    (output-branch (Act-LetPairE step)) =
  output-branch step
let-pair-output-invert
    (output-close (Act-LetPairE step)) =
  output-close step

let-unit-output :
  ∀ {n} {first second : Expr [] n}
  → Output first
  → Output (E-LetUnit first second)
let-unit-output (output-message step) =
  output-message (Act-LetUnitE step)
let-unit-output (output-branch step) =
  output-branch (Act-LetUnitE step)
let-unit-output (output-close step) =
  output-close (Act-LetUnitE step)

let-unit-output-invert :
  ∀ {n} {first second : Expr [] n}
  → Output (E-LetUnit first second)
  → Output first
let-unit-output-invert
    (output-message (Act-LetUnitE step)) =
  output-message step
let-unit-output-invert
    (output-branch (Act-LetUnitE step)) =
  output-branch step
let-unit-output-invert
    (output-close (Act-LetUnitE step)) =
  output-close step

output? : ∀ {n} (e : Expr [] n) → Dec (Output e)
output? (E-Val value) = no λ where
  (output-message ())
  (output-branch ())
  (output-close ())
output? (E-App left right) with is-value? left
... | no not-value =
  decide-app-left-output not-value (output? left)
... | yes (is-value function) =
  decide-app-value-output function right
    (app-output-head? function right)
    (output? right)
output? (E-TApp function argument)
  with output? function
... | yes output = yes (tapp-output output)
... | no no-output =
  no λ outer → no-output (tapp-output-invert outer)
output? (E-Pair left right) with is-value? left
... | no not-value =
  decide-pair-left-output not-value (output? left)
... | yes (is-value first) =
  decide-pair-right-output (output? right)
output? (E-Match scrutinee ne branches)
  with output? scrutinee
... | yes output = yes (match-output output)
... | no no-output =
  no λ outer → no-output (match-output-invert outer)
output? (E-LetPair first body)
  with output? first
... | yes output = yes (let-pair-output output)
... | no no-output =
  no λ outer → no-output (let-pair-output-invert outer)
output? (E-LetUnit first second)
  with output? first
... | yes output = yes (let-unit-output output)
... | no no-output =
  no λ outer → no-output (let-unit-output-invert outer)

------------------------------------------------------------------------
-- Existence of an incoming communication

data Input {n : ℕ} (e : Expr [] n) : Set where
  input-action :
    ∀ {label : Label n []}
    → InputLabel label
    → Accepts e label
    → Input e

data SomeAppInputHead {n : ℕ}
    (function : Value [] n) (argument : Expr [] n) : Set where
  some-app-input-head :
    ∀ {label : Label n []}
    → InputLabel label
    → AppInputHead function argument label
    → SomeAppInputHead function argument

some-app-input-head? :
  ∀ {n} (function : Value [] n) (argument : Expr [] n)
  → Dec (SomeAppInputHead function argument)
some-app-input-head? (V-Receive₂ T S) argument
  with variable-argument? argument
... | yes variable-argument =
  yes
    (some-app-input-head
      {label = L-RecvVal _ (V-Const C-Unit)}
      input-message
      input-head-message)
... | no not-variable =
  no λ where
    (some-app-input-head input-message input-head-message) →
      not-variable variable-argument
some-app-input-head? (V-Const C-Close) argument
  with variable-argument? argument
... | yes variable-argument =
  yes (some-app-input-head input-close input-head-close)
... | no not-variable =
  no λ where
    (some-app-input-head input-close input-head-close) →
      not-variable variable-argument
some-app-input-head? (V-Const C-Unit) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Const C-Fork) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Const C-New) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Const C-Receive) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Const C-Send) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Const (C-Select variance i)) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Var x) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Abs T body) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Rec T U body) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-TAbs K body) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Pair first second) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Receive₁ T) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Send₁ T) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Send₂ T S) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Select₁ variance i P) argument =
  no λ where (some-app-input-head input ())
some-app-input-head? (V-Select₂ variance i P S) argument =
  no λ where (some-app-input-head input ())

data SomeMatchInputHead {n : ℕ} :
    ∀ {k} {ss : Subset.Subset k}
    → (scrutinee : Expr [] n)
    → (ne : Subset.Nonempty ss)
    → ((i : Fin k) → i Subset.∈ ss → Expr [] (suc n))
    → Set where
  some-match-input-head :
    ∀ {k} {ss : Subset.Subset k} {ne : Subset.Nonempty ss}
      {scrutinee : Expr [] n}
      {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
      {label : Label n []}
    → InputLabel label
    → MatchInputHead scrutinee ne branches label
    → SomeMatchInputHead scrutinee ne branches

some-match-input-head? :
  ∀ {n k} {ss : Subset.Subset k}
    (scrutinee : Expr [] n)
    (ne : Subset.Nonempty ss)
    (branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n))
  → Dec (SomeMatchInputHead scrutinee ne branches)
some-match-input-head? scrutinee ne branches
  with variable-argument? scrutinee
... | no not-variable =
  no λ where
    (some-match-input-head
      input-branch
      (input-head-branch i∈)) →
        not-variable variable-argument
... | yes variable-argument with ne
... | i , i∈ =
  yes
    (some-match-input-head
      input-branch
      (input-head-branch i∈))

decide-from-sum :
  ∀ {P Q R : Set}
  → (P → R)
  → (Q → R)
  → (R → P ⊎ Q)
  → Dec P
  → Dec Q
  → Dec R
decide-from-sum left right invert (yes proof) other =
  yes (left proof)
decide-from-sum left right invert (no not-left) (yes proof) =
  yes (right proof)
decide-from-sum left right invert (no not-left) (no not-right) =
  no λ result →
    refute-sum not-left not-right (invert result)

map-dec :
  ∀ {P Q : Set}
  → (P → Q)
  → (Q → P)
  → Dec P
  → Dec Q
map-dec forward backward (yes proof) = yes (forward proof)
map-dec forward backward (no not-proof) =
  no λ result → not-proof (backward result)

app-head-input :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
  → SomeAppInputHead function argument
  → Input (E-App (E-Val function) argument)
app-head-input (some-app-input-head input head) =
  input-action input (app-input-head-accepts head)

app-value-input-invert :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
  → Input (E-App (E-Val function) argument)
  → SomeAppInputHead function argument ⊎ Input argument
app-value-input-invert (input-action input acceptance)
  with app-value-accepts-invert input acceptance
... | inj₁ head =
  inj₁ (some-app-input-head input head)
... | inj₂ inner =
  inj₂ (input-action input inner)

app-left-input :
  ∀ {n} {left right : Expr [] n}
  → Input left
  → Input (E-App left right)
app-left-input (input-action input acceptance) =
  input-action input (app-left-accepts acceptance)

app-left-input-invert :
  ∀ {n} {left right : Expr [] n}
  → (IsValue left → ⊥)
  → Input (E-App left right)
  → Input left
app-left-input-invert not-value
    (input-action input acceptance) =
  input-action input
    (app-left-accepts-invert input not-value acceptance)

app-right-input :
  ∀ {n} {function : Value [] n} {argument : Expr [] n}
  → Input argument
  → Input (E-App (E-Val function) argument)
app-right-input (input-action input acceptance) =
  input-action input (app-right-accepts acceptance)

tapp-input :
  ∀ {n K} {function : Expr [] n} {argument : NfTy [] K}
  → Input function
  → Input (E-TApp function argument)
tapp-input (input-action input acceptance) =
  input-action input (tapp-accepts acceptance)

tapp-input-invert :
  ∀ {n K} {function : Expr [] n} {argument : NfTy [] K}
  → Input (E-TApp function argument)
  → Input function
tapp-input-invert (input-action input acceptance) =
  input-action input (tapp-accepts-invert input acceptance)

pair-left-input :
  ∀ {n} {left right : Expr [] n}
  → Input left
  → Input (E-Pair left right)
pair-left-input (input-action input acceptance) =
  input-action input (pair-left-accepts acceptance)

pair-left-input-invert :
  ∀ {n} {left right : Expr [] n}
  → (IsValue left → ⊥)
  → Input (E-Pair left right)
  → Input left
pair-left-input-invert not-value
    (input-action input acceptance) =
  input-action input
    (pair-left-accepts-invert input not-value acceptance)

pair-right-input :
  ∀ {n} {first : Value [] n} {second : Expr [] n}
  → Input second
  → Input (E-Pair (E-Val first) second)
pair-right-input (input-action input acceptance) =
  input-action input (pair-right-accepts acceptance)

pair-right-input-invert :
  ∀ {n} {first : Value [] n} {second : Expr [] n}
  → Input (E-Pair (E-Val first) second)
  → Input second
pair-right-input-invert (input-action input acceptance) =
  input-action input (pair-right-accepts-invert input acceptance)

match-head-input :
  ∀ {n k} {ss : Subset.Subset k}
    {scrutinee : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
  → SomeMatchInputHead scrutinee ne branches
  → Input (E-Match scrutinee ne branches)
match-head-input (some-match-input-head input head) =
  input-action input (match-input-head-accepts head)

match-input-invert :
  ∀ {n k} {ss : Subset.Subset k}
    {scrutinee : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
  → Input (E-Match scrutinee ne branches)
  → SomeMatchInputHead scrutinee ne branches ⊎ Input scrutinee
match-input-invert (input-action input acceptance)
  with match-accepts-invert input acceptance
... | inj₁ head =
  inj₁ (some-match-input-head input head)
... | inj₂ inner =
  inj₂ (input-action input inner)

match-inner-input :
  ∀ {n k} {ss : Subset.Subset k}
    {scrutinee : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
  → Input scrutinee
  → Input (E-Match scrutinee ne branches)
match-inner-input (input-action input acceptance) =
  input-action input (match-accepts acceptance)

let-pair-input :
  ∀ {n} {first : Expr [] n} {body : Expr [] (suc (suc n))}
  → Input first
  → Input (E-LetPair first body)
let-pair-input (input-action input acceptance) =
  input-action input (let-pair-accepts acceptance)

let-pair-input-invert :
  ∀ {n} {first : Expr [] n} {body : Expr [] (suc (suc n))}
  → Input (E-LetPair first body)
  → Input first
let-pair-input-invert (input-action input acceptance) =
  input-action input (let-pair-accepts-invert input acceptance)

let-unit-input :
  ∀ {n} {first second : Expr [] n}
  → Input first
  → Input (E-LetUnit first second)
let-unit-input (input-action input acceptance) =
  input-action input (let-unit-accepts acceptance)

let-unit-input-invert :
  ∀ {n} {first second : Expr [] n}
  → Input (E-LetUnit first second)
  → Input first
let-unit-input-invert (input-action input acceptance) =
  input-action input (let-unit-accepts-invert input acceptance)

input? : ∀ {n} (e : Expr [] n) → Dec (Input e)
input? (E-Val value) =
  no λ where
    (input-action input (accepts _ ()))
input? (E-App left right) with is-value? left
... | no not-value =
  map-dec app-left-input
    (app-left-input-invert not-value)
    (input? left)
... | yes (is-value function) =
  decide-from-sum
    app-head-input
    app-right-input
    app-value-input-invert
    (some-app-input-head? function right)
    (input? right)
input? (E-TApp function argument) =
  map-dec tapp-input tapp-input-invert (input? function)
input? (E-Pair left right) with is-value? left
... | no not-value =
  map-dec pair-left-input
    (pair-left-input-invert not-value)
    (input? left)
... | yes (is-value first) =
  map-dec pair-right-input pair-right-input-invert (input? right)
input? (E-Match scrutinee ne branches) =
  decide-from-sum
    match-head-input
    match-inner-input
    match-input-invert
    (some-match-input-head? scrutinee ne branches)
    (input? scrutinee)
input? (E-LetPair first body) =
  map-dec let-pair-input let-pair-input-invert (input? first)
input? (E-LetUnit first second) =
  map-dec let-unit-input let-unit-input-invert (input? first)

input-label-communication :
  ∀ {n} {label : Label n []}
  → InputLabel label
  → CommunicationLabel label
input-label-communication input-message = comm-recv-val
input-label-communication input-branch = comm-recv-lab
input-label-communication input-close = comm-close

input-communication-blocked :
  ∀ {n} {e : Expr [] n}
  → Input e
  → CommunicationBlocked e
input-communication-blocked
    (input-action input (accepts target transition)) =
  communication-blocked
    _
    target
    (input-label-communication input)
    transition

output-communication-blocked :
  ∀ {n} {e : Expr [] n}
  → Output e
  → CommunicationBlocked e
output-communication-blocked (output-message transition) =
  communication-blocked
    _
    _
    comm-send-val
    transition
output-communication-blocked (output-branch transition) =
  communication-blocked
    _
    _
    comm-send-lab
    transition
output-communication-blocked (output-close transition) =
  communication-blocked
    _
    _
    comm-close
    transition

communication-blocked-invert :
  ∀ {n} {e : Expr [] n}
  → CommunicationBlocked e
  → Input e ⊎ Output e
communication-blocked-invert
    (communication-blocked _ target comm-recv-val transition) =
  inj₁
    (input-action
      input-message
      (accepts target transition))
communication-blocked-invert
    (communication-blocked _ target comm-recv-lab transition) =
  inj₁
    (input-action
      input-branch
      (accepts target transition))
communication-blocked-invert
    (communication-blocked _ target comm-send-val transition) =
  inj₂ (output-message transition)
communication-blocked-invert
    (communication-blocked _ target comm-send-lab transition) =
  inj₂ (output-branch transition)
communication-blocked-invert
    (communication-blocked _ target comm-close transition) =
  inj₁
    (input-action
      input-close
      (accepts target transition))

communication-blocked? :
  ∀ {n} (e : Expr [] n)
  → Dec (CommunicationBlocked e)
communication-blocked? e =
  decide-from-sum
    input-communication-blocked
    output-communication-blocked
    communication-blocked-invert
    (input? e)
    (output? e)

------------------------------------------------------------------------
-- Outgoing actions are deterministic

tapp-message-invert :
  ∀ {n K} {function : Expr [] n} {argument : NfTy [] K}
    {target : Expr [] n} {y : Fin n} {v : Value [] n}
  → E-TApp function argument —[ L-SendVal y v ]→ target
  → Σ (Expr [] n) λ target′ →
      function —[ L-SendVal y v ]→ target′
tapp-message-invert (Act-TAppE step) = _ , step

tapp-branch-invert :
  ∀ {n k K} {function : Expr [] n} {argument : NfTy [] K}
    {target : Expr [] n} {y : Fin n} {i : Fin k}
  → E-TApp function argument —[ L-SendLab y i ]→ target
  → Σ (Expr [] n) λ target′ →
      function —[ L-SendLab y i ]→ target′
tapp-branch-invert (Act-TAppE step) = _ , step

tapp-close-invert :
  ∀ {n K} {function : Expr [] n} {argument : NfTy [] K}
    {target : Expr [] n} {y : Fin n}
  → E-TApp function argument —[ L-Close y ]→ target
  → Σ (Expr [] n) λ target′ →
      function —[ L-Close y ]→ target′
tapp-close-invert (Act-TAppE step) = _ , step

send-message-unique :
  ∀ {n} {e e₁ e₂ : Expr [] n}
    {y₁ y₂ : Fin n} {v₁ v₂ : Value [] n}
  → e —[ L-SendVal y₁ v₁ ]→ e₁
  → e —[ L-SendVal y₂ v₂ ]→ e₂
  → y₁ ≡ y₂ × v₁ ≡ v₂
send-message-unique Act-Send Act-Send = refl , refl
send-message-unique (Act-AppL first) (Act-AppL second) =
  send-message-unique first second
send-message-unique (Act-AppR first) (Act-AppR second) =
  send-message-unique first second
send-message-unique
    (Act-TAppE first) second
  with tapp-message-invert second
... | _ , second′ =
  send-message-unique first second′
send-message-unique (Act-PairL first) (Act-PairL second) =
  send-message-unique first second
send-message-unique (Act-PairR first) (Act-PairR second) =
  send-message-unique first second
send-message-unique (Act-MatchE first) (Act-MatchE second) =
  send-message-unique first second
send-message-unique (Act-LetPairE first) (Act-LetPairE second) =
  send-message-unique first second
send-message-unique (Act-LetUnitE first) (Act-LetUnitE second) =
  send-message-unique first second

BranchAgreement :
  ∀ {n k₁ k₂}
  → Fin n → Fin k₁ → Fin n → Fin k₂ → Set
BranchAgreement {k₁ = k₁} {k₂ = k₂} y₁ i₁ y₂ i₂ =
  Σ (k₁ ≡ k₂) λ where
    refl → y₁ ≡ y₂ × i₁ ≡ i₂

send-branch-unique :
  ∀ {n k₁ k₂} {e e₁ e₂ : Expr [] n}
    {y₁ y₂ : Fin n} {i₁ : Fin k₁} {i₂ : Fin k₂}
  → e —[ L-SendLab y₁ i₁ ]→ e₁
  → e —[ L-SendLab y₂ i₂ ]→ e₂
  → BranchAgreement y₁ i₁ y₂ i₂
send-branch-unique Act-Sel Act-Sel =
  refl , (refl , refl)
send-branch-unique (Act-AppL first) (Act-AppL second) =
  send-branch-unique first second
send-branch-unique (Act-AppR first) (Act-AppR second) =
  send-branch-unique first second
send-branch-unique
    (Act-TAppE first) second
  with tapp-branch-invert second
... | _ , second′ =
  send-branch-unique first second′
send-branch-unique (Act-PairL first) (Act-PairL second) =
  send-branch-unique first second
send-branch-unique (Act-PairR first) (Act-PairR second) =
  send-branch-unique first second
send-branch-unique (Act-MatchE first) (Act-MatchE second) =
  send-branch-unique first second
send-branch-unique (Act-LetPairE first) (Act-LetPairE second) =
  send-branch-unique first second
send-branch-unique (Act-LetUnitE first) (Act-LetUnitE second) =
  send-branch-unique first second

send-close-unique :
  ∀ {n} {e e₁ e₂ : Expr [] n} {y₁ y₂ : Fin n}
  → e —[ L-Close y₁ ]→ e₁
  → e —[ L-Close y₂ ]→ e₂
  → y₁ ≡ y₂
send-close-unique Act-Close Act-Close = refl
send-close-unique (Act-AppL first) (Act-AppL second) =
  send-close-unique first second
send-close-unique (Act-AppR first) (Act-AppR second) =
  send-close-unique first second
send-close-unique
    (Act-TAppE first) second
  with tapp-close-invert second
... | _ , second′ =
  send-close-unique first second′
send-close-unique (Act-PairL first) (Act-PairL second) =
  send-close-unique first second
send-close-unique (Act-PairR first) (Act-PairR second) =
  send-close-unique first second
send-close-unique (Act-MatchE first) (Act-MatchE second) =
  send-close-unique first second
send-close-unique (Act-LetPairE first) (Act-LetPairE second) =
  send-close-unique first second
send-close-unique (Act-LetUnitE first) (Act-LetUnitE second) =
  send-close-unique first second

message-not-branch :
  ∀ {n k} {e e₁ e₂ : Expr [] n}
    {y₁ y₂ : Fin n} {v : Value [] n} {i : Fin k}
  → e —[ L-SendVal y₁ v ]→ e₁
  → e —[ L-SendLab y₂ i ]→ e₂
  → ⊥
message-not-branch (Act-AppL ()) Act-Sel
message-not-branch (Act-AppR ()) Act-Sel
message-not-branch (Act-AppL first) (Act-AppL second) =
  message-not-branch first second
message-not-branch (Act-AppR first) (Act-AppR second) =
  message-not-branch first second
message-not-branch (Act-TAppE first) second
  with tapp-branch-invert second
... | _ , second′ =
  message-not-branch first second′
message-not-branch (Act-PairL first) (Act-PairL second) =
  message-not-branch first second
message-not-branch (Act-PairR first) (Act-PairR second) =
  message-not-branch first second
message-not-branch (Act-MatchE first) (Act-MatchE second) =
  message-not-branch first second
message-not-branch (Act-LetPairE first) (Act-LetPairE second) =
  message-not-branch first second
message-not-branch (Act-LetUnitE first) (Act-LetUnitE second) =
  message-not-branch first second

message-not-close :
  ∀ {n} {e e₁ e₂ : Expr [] n}
    {y₁ y₂ : Fin n} {v : Value [] n}
  → e —[ L-SendVal y₁ v ]→ e₁
  → e —[ L-Close y₂ ]→ e₂
  → ⊥
message-not-close (Act-AppL ()) Act-Close
message-not-close (Act-AppR ()) Act-Close
message-not-close (Act-AppL first) (Act-AppL second) =
  message-not-close first second
message-not-close (Act-AppR first) (Act-AppR second) =
  message-not-close first second
message-not-close (Act-TAppE first) second
  with tapp-close-invert second
... | _ , second′ =
  message-not-close first second′
message-not-close (Act-PairL first) (Act-PairL second) =
  message-not-close first second
message-not-close (Act-PairR first) (Act-PairR second) =
  message-not-close first second
message-not-close (Act-MatchE first) (Act-MatchE second) =
  message-not-close first second
message-not-close (Act-LetPairE first) (Act-LetPairE second) =
  message-not-close first second
message-not-close (Act-LetUnitE first) (Act-LetUnitE second) =
  message-not-close first second

branch-not-close :
  ∀ {n k} {e e₁ e₂ : Expr [] n}
    {y₁ y₂ : Fin n} {i : Fin k}
  → e —[ L-SendLab y₁ i ]→ e₁
  → e —[ L-Close y₂ ]→ e₂
  → ⊥
branch-not-close (Act-AppL ()) Act-Close
branch-not-close (Act-AppR ()) Act-Close
branch-not-close (Act-AppL first) (Act-AppL second) =
  branch-not-close first second
branch-not-close (Act-AppR first) (Act-AppR second) =
  branch-not-close first second
branch-not-close (Act-TAppE first) second
  with tapp-close-invert second
... | _ , second′ =
  branch-not-close first second′
branch-not-close (Act-PairL first) (Act-PairL second) =
  branch-not-close first second
branch-not-close (Act-PairR first) (Act-PairR second) =
  branch-not-close first second
branch-not-close (Act-MatchE first) (Act-MatchE second) =
  branch-not-close first second
branch-not-close (Act-LetPairE first) (Act-LetPairE second) =
  branch-not-close first second
branch-not-close (Act-LetUnitE first) (Act-LetUnitE second) =
  branch-not-close first second

------------------------------------------------------------------------
-- Synchronization

record MessageEndpointMatch {n : ℕ}
    (C : Conf (2 + n)) (receiver : Fin ∣ C ∣)
    (y : Fin (2 + n)) (v : Value [] (2 + n))
    (x : Fin (2 + n)) : Set where
  constructor message-endpoint
  field
    pair : FinFreshPair {n} x y
    x-live : x Subset.∈ live C
    y-live : y Subset.∈ live C
    receive : Accepts (lookup C receiver) (L-RecvVal x v)

record BranchEndpointMatch {n k : ℕ}
    (C : Conf (2 + n)) (receiver : Fin ∣ C ∣)
    (y : Fin (2 + n)) (i : Fin k)
    (x : Fin (2 + n)) : Set where
  constructor branch-endpoint
  field
    pair : FinFreshPair {n} x y
    x-live : x Subset.∈ live C
    y-live : y Subset.∈ live C
    receive : Accepts (lookup C receiver) (L-RecvLab x i)

record CloseEndpointMatch {n : ℕ}
    (C : Conf (2 + n)) (receiver : Fin ∣ C ∣)
    (y x : Fin (2 + n)) : Set where
  constructor close-endpoint
  field
    pair : FinFreshPair {n} x y
    x-live : x Subset.∈ live C
    y-live : y Subset.∈ live C
    close : Accepts (lookup C receiver) (L-Close x)

decide-message-endpoint :
  ∀ {n} {C : Conf (2 + n)} {receiver : Fin ∣ C ∣}
    {y : Fin (2 + n)} {v : Value [] (2 + n)}
    {x : Fin (2 + n)}
  → Dec (FinFreshPair {n} x y)
  → Dec (x Subset.∈ live C)
  → Dec (y Subset.∈ live C)
  → Dec (Accepts (lookup C receiver) (L-RecvVal x v))
  → Dec (MessageEndpointMatch C receiver y v x)
decide-message-endpoint
    (yes pair) (yes x-live) (yes y-live) (yes receive) =
  yes (message-endpoint pair x-live y-live receive)
decide-message-endpoint
    (no not-pair) x-live? y-live? receive? =
  no λ where
    (message-endpoint pair _ _ _) → not-pair pair
decide-message-endpoint
    (yes pair) (no not-live) y-live? receive? =
  no λ where
    (message-endpoint _ x-live _ _) → not-live x-live
decide-message-endpoint
    (yes pair) (yes x-live) (no not-live) receive? =
  no λ where
    (message-endpoint _ _ y-live _) → not-live y-live
decide-message-endpoint
    (yes pair) (yes x-live) (yes y-live) (no not-receive) =
  no λ where
    (message-endpoint _ _ _ receive) → not-receive receive

message-endpoint-match? :
  ∀ {n} (C : Conf (2 + n)) (receiver : Fin ∣ C ∣)
    (y : Fin (2 + n)) (v : Value [] (2 + n))
    (x : Fin (2 + n))
  → Dec (MessageEndpointMatch C receiver y v x)
message-endpoint-match? C receiver y v x =
  decide-message-endpoint
    (fresh-pair? x y)
    (subset-member? x (live C))
    (subset-member? y (live C))
    (accepts? (lookup C receiver) input-message)

decide-branch-endpoint :
  ∀ {n k} {C : Conf (2 + n)} {receiver : Fin ∣ C ∣}
    {y : Fin (2 + n)} {i : Fin k} {x : Fin (2 + n)}
  → Dec (FinFreshPair {n} x y)
  → Dec (x Subset.∈ live C)
  → Dec (y Subset.∈ live C)
  → Dec (Accepts (lookup C receiver) (L-RecvLab x i))
  → Dec (BranchEndpointMatch C receiver y i x)
decide-branch-endpoint
    (yes pair) (yes x-live) (yes y-live) (yes receive) =
  yes (branch-endpoint pair x-live y-live receive)
decide-branch-endpoint
    (no not-pair) x-live? y-live? receive? =
  no λ where
    (branch-endpoint pair _ _ _) → not-pair pair
decide-branch-endpoint
    (yes pair) (no not-live) y-live? receive? =
  no λ where
    (branch-endpoint _ x-live _ _) → not-live x-live
decide-branch-endpoint
    (yes pair) (yes x-live) (no not-live) receive? =
  no λ where
    (branch-endpoint _ _ y-live _) → not-live y-live
decide-branch-endpoint
    (yes pair) (yes x-live) (yes y-live) (no not-receive) =
  no λ where
    (branch-endpoint _ _ _ receive) → not-receive receive

branch-endpoint-match? :
  ∀ {n k} (C : Conf (2 + n)) (receiver : Fin ∣ C ∣)
    (y : Fin (2 + n)) (i : Fin k) (x : Fin (2 + n))
  → Dec (BranchEndpointMatch C receiver y i x)
branch-endpoint-match? C receiver y i x =
  decide-branch-endpoint
    (fresh-pair? x y)
    (subset-member? x (live C))
    (subset-member? y (live C))
    (accepts? (lookup C receiver) input-branch)

decide-close-endpoint :
  ∀ {n} {C : Conf (2 + n)} {receiver : Fin ∣ C ∣}
    {y x : Fin (2 + n)}
  → Dec (FinFreshPair {n} x y)
  → Dec (x Subset.∈ live C)
  → Dec (y Subset.∈ live C)
  → Dec (Accepts (lookup C receiver) (L-Close x))
  → Dec (CloseEndpointMatch C receiver y x)
decide-close-endpoint
    (yes pair) (yes x-live) (yes y-live) (yes close) =
  yes (close-endpoint pair x-live y-live close)
decide-close-endpoint
    (no not-pair) x-live? y-live? close? =
  no λ where
    (close-endpoint pair _ _ _) → not-pair pair
decide-close-endpoint
    (yes pair) (no not-live) y-live? close? =
  no λ where
    (close-endpoint _ x-live _ _) → not-live x-live
decide-close-endpoint
    (yes pair) (yes x-live) (no not-live) close? =
  no λ where
    (close-endpoint _ _ y-live _) → not-live y-live
decide-close-endpoint
    (yes pair) (yes x-live) (yes y-live) (no not-close) =
  no λ where
    (close-endpoint _ _ _ close) → not-close close

close-endpoint-match? :
  ∀ {n} (C : Conf (2 + n)) (receiver : Fin ∣ C ∣)
    (y x : Fin (2 + n))
  → Dec (CloseEndpointMatch C receiver y x)
close-endpoint-match? C receiver y x =
  decide-close-endpoint
    (fresh-pair? x y)
    (subset-member? x (live C))
    (subset-member? y (live C))
    (accepts? (lookup C receiver) input-close)

data SynchronizationAt {n : ℕ} (C : Conf (2 + n))
    (receiver sender : Fin ∣ C ∣) : Set where
  sync-at-message :
      (receiver≠sender : receiver ≢ sender)
      (x : Fin (2 + n))
      {y : Fin (2 + n)} {v : Value [] (2 + n)}
      {target : Expr [] (2 + n)}
    → MessageEndpointMatch C receiver y v x
    → lookup C sender —[ L-SendVal y v ]→ target
    → SynchronizationAt C receiver sender
  sync-at-branch :
      ∀ {k}
      (receiver≠sender : receiver ≢ sender)
      (x : Fin (2 + n))
      {y : Fin (2 + n)} {i : Fin k}
      {target : Expr [] (2 + n)}
    → BranchEndpointMatch C receiver y i x
    → lookup C sender —[ L-SendLab y i ]→ target
    → SynchronizationAt C receiver sender
  sync-at-close :
      (receiver≠sender : receiver ≢ sender)
      (x : Fin (2 + n))
      {y : Fin (2 + n)} {target : Expr [] (2 + n)}
    → CloseEndpointMatch C receiver y x
    → lookup C sender —[ L-Close y ]→ target
    → SynchronizationAt C receiver sender

message-no-endpoint :
  ∀ {n} {C : Conf (2 + n)}
    {receiver sender : Fin ∣ C ∣}
    {y : Fin (2 + n)} {v : Value [] (2 + n)}
    {target : Expr [] (2 + n)}
  → lookup C sender —[ L-SendVal y v ]→ target
  → (Σ (Fin (2 + n))
        (MessageEndpointMatch C receiver y v) → ⊥)
  → SynchronizationAt C receiver sender
  → ⊥
message-no-endpoint send no-endpoint
    (sync-at-message _ x endpoint send′)
  with send-message-unique send send′
... | refl , refl = no-endpoint (x , endpoint)
message-no-endpoint send no-endpoint
    (sync-at-branch _ x endpoint send′) =
  message-not-branch send send′
message-no-endpoint send no-endpoint
    (sync-at-close _ x endpoint send′) =
  message-not-close send send′

message-sync-from-search :
  ∀ {n} {C : Conf (2 + n)}
    {receiver sender : Fin ∣ C ∣}
    (receiver≠sender : receiver ≢ sender)
    {y : Fin (2 + n)} {v : Value [] (2 + n)}
    {target : Expr [] (2 + n)}
  → lookup C sender —[ L-SendVal y v ]→ target
  → Dec
      (Σ (Fin (2 + n))
        (MessageEndpointMatch C receiver y v))
  → Dec (SynchronizationAt C receiver sender)
message-sync-from-search receiver≠sender send
    (yes (x , endpoint)) =
  yes (sync-at-message receiver≠sender x endpoint send)
message-sync-from-search receiver≠sender send
    (no no-endpoint) =
  no (message-no-endpoint send no-endpoint)

branch-no-endpoint :
  ∀ {n k} {C : Conf (2 + n)}
    {receiver sender : Fin ∣ C ∣}
    {y : Fin (2 + n)} {i : Fin k}
    {target : Expr [] (2 + n)}
  → lookup C sender —[ L-SendLab y i ]→ target
  → (Σ (Fin (2 + n))
        (BranchEndpointMatch C receiver y i) → ⊥)
  → SynchronizationAt C receiver sender
  → ⊥
branch-no-endpoint send no-endpoint
    (sync-at-message _ x endpoint send′) =
  message-not-branch send′ send
branch-no-endpoint send no-endpoint
    (sync-at-branch _ x endpoint send′)
  with send-branch-unique send send′
... | refl , (refl , refl) = no-endpoint (x , endpoint)
branch-no-endpoint send no-endpoint
    (sync-at-close _ x endpoint send′) =
  branch-not-close send send′

branch-sync-from-search :
  ∀ {n k} {C : Conf (2 + n)}
    {receiver sender : Fin ∣ C ∣}
    (receiver≠sender : receiver ≢ sender)
    {y : Fin (2 + n)} {i : Fin k}
    {target : Expr [] (2 + n)}
  → lookup C sender —[ L-SendLab y i ]→ target
  → Dec
      (Σ (Fin (2 + n))
        (BranchEndpointMatch C receiver y i))
  → Dec (SynchronizationAt C receiver sender)
branch-sync-from-search receiver≠sender send
    (yes (x , endpoint)) =
  yes (sync-at-branch receiver≠sender x endpoint send)
branch-sync-from-search receiver≠sender send
    (no no-endpoint) =
  no (branch-no-endpoint send no-endpoint)

close-no-endpoint :
  ∀ {n} {C : Conf (2 + n)}
    {receiver sender : Fin ∣ C ∣}
    {y : Fin (2 + n)} {target : Expr [] (2 + n)}
  → lookup C sender —[ L-Close y ]→ target
  → (Σ (Fin (2 + n))
        (CloseEndpointMatch C receiver y) → ⊥)
  → SynchronizationAt C receiver sender
  → ⊥
close-no-endpoint close no-endpoint
    (sync-at-message _ x endpoint send′) =
  message-not-close send′ close
close-no-endpoint close no-endpoint
    (sync-at-branch _ x endpoint send′) =
  branch-not-close send′ close
close-no-endpoint close no-endpoint
    (sync-at-close _ x endpoint close′)
  with send-close-unique close close′
... | refl = no-endpoint (x , endpoint)

close-sync-from-search :
  ∀ {n} {C : Conf (2 + n)}
    {receiver sender : Fin ∣ C ∣}
    (receiver≠sender : receiver ≢ sender)
    {y : Fin (2 + n)} {target : Expr [] (2 + n)}
  → lookup C sender —[ L-Close y ]→ target
  → Dec
      (Σ (Fin (2 + n))
        (CloseEndpointMatch C receiver y))
  → Dec (SynchronizationAt C receiver sender)
close-sync-from-search receiver≠sender close
    (yes (x , endpoint)) =
  yes (sync-at-close receiver≠sender x endpoint close)
close-sync-from-search receiver≠sender close
    (no no-endpoint) =
  no (close-no-endpoint close no-endpoint)

synchronization-at-from-output :
  ∀ {n} (C : Conf (2 + n))
    (receiver sender : Fin ∣ C ∣)
  → receiver ≢ sender
  → Dec (Output (lookup C sender))
  → Dec (SynchronizationAt C receiver sender)
synchronization-at-from-output C receiver sender
    receiver≠sender (no no-output) =
  no λ where
    (sync-at-message _ x endpoint send) →
      no-output (output-message send)
    (sync-at-branch _ x endpoint send) →
      no-output (output-branch send)
    (sync-at-close _ x endpoint close) →
      no-output (output-close close)
synchronization-at-from-output C receiver sender
    receiver≠sender (yes (output-message {y = y} {v = v} send)) =
  message-sync-from-search receiver≠sender send
    (any-fin?
      (message-endpoint-match? C receiver y v))
synchronization-at-from-output C receiver sender
    receiver≠sender (yes (output-branch {y = y} {i = i} send)) =
  branch-sync-from-search receiver≠sender send
    (any-fin?
      (branch-endpoint-match? C receiver y i))
synchronization-at-from-output C receiver sender
    receiver≠sender (yes (output-close {y = y} close)) =
  close-sync-from-search receiver≠sender close
    (any-fin?
      (close-endpoint-match? C receiver y))

synchronization-at? :
  ∀ {n} (C : Conf (2 + n))
    (receiver sender : Fin ∣ C ∣)
  → Dec (SynchronizationAt C receiver sender)
synchronization-at? C receiver sender
  with receiver ≟Fin sender
... | yes refl =
  no λ where
    (sync-at-message receiver≠sender _ _ _) →
      receiver≠sender refl
    (sync-at-branch receiver≠sender _ _ _) →
      receiver≠sender refl
    (sync-at-close receiver≠sender _ _ _) →
      receiver≠sender refl
... | no receiver≠sender =
  synchronization-at-from-output C receiver sender
    receiver≠sender
    (output? (lookup C sender))

synchronization-at-possible :
  ∀ {n} {C : Conf (2 + n)} {receiver sender : Fin ∣ C ∣}
  → SynchronizationAt C receiver sender
  → SynchronizationPossible C
synchronization-at-possible
    {receiver = receiver} {sender = sender}
    (sync-at-message receiver≠sender x
      (message-endpoint pair x-live y-live
        (accepts _ receive))
      send) =
  sync-message receiver sender receiver≠sender
    pair x-live y-live receive send
synchronization-at-possible
    {receiver = receiver} {sender = sender}
    (sync-at-branch receiver≠sender x
      (branch-endpoint pair x-live y-live
        (accepts _ receive))
      send) =
  sync-branch receiver sender receiver≠sender
    pair x-live y-live receive send
synchronization-at-possible
    {receiver = receiver} {sender = sender}
    (sync-at-close receiver≠sender x
      (close-endpoint pair x-live y-live
        (accepts _ close))
      close′) =
  sync-close receiver sender receiver≠sender
    pair x-live y-live close close′

possible-at-some-pair :
  ∀ {n} {C : Conf (2 + n)}
  → SynchronizationPossible C
  → Σ (Fin ∣ C ∣) λ receiver →
      Σ (Fin ∣ C ∣) λ sender →
        SynchronizationAt C receiver sender
possible-at-some-pair
    (sync-message {x = x} receiver sender receiver≠sender
      pair x-live y-live receive send) =
  receiver , sender ,
    sync-at-message receiver≠sender x
      (message-endpoint pair x-live y-live
        (accepts _ receive))
      send
possible-at-some-pair
    (sync-branch {x = x} receiver sender receiver≠sender
      pair x-live y-live receive send) =
  receiver , sender ,
    sync-at-branch receiver≠sender x
      (branch-endpoint pair x-live y-live
        (accepts _ receive))
      send
possible-at-some-pair
    (sync-close {x = x} receiver sender receiver≠sender
      pair x-live y-live close close′) =
  receiver , sender ,
    sync-at-close receiver≠sender x
      (close-endpoint pair x-live y-live
        (accepts _ close))
      close′

synchronization-possible₂? :
  ∀ {n} (C : Conf (2 + n))
  → Dec (SynchronizationPossible C)
synchronization-possible₂? C
  with any-fin?
    (λ receiver →
      any-fin?
        (λ sender →
          synchronization-at? C receiver sender))
... | yes (receiver , sender , synchronization) =
  yes (synchronization-at-possible synchronization)
... | no none =
  no λ synchronization →
    none (possible-at-some-pair synchronization)

synchronization-possible? :
  ∀ {n} (C : Conf n)
  → Dec (SynchronizationPossible C)
synchronization-possible? {n = zero} C = no λ ()
synchronization-possible? {n = suc zero} C = no λ ()
synchronization-possible? {n = suc (suc n)} C =
  synchronization-possible₂? C

------------------------------------------------------------------------
-- Terminal and global-deadlock decisions

quiescent? :
  ∀ {n} (e : Expr [] n)
  → Dec (IsValue e ⊎ CommunicationBlocked e)
quiescent? e with is-value? e
... | yes value = yes (inj₁ value)
... | no not-value with communication-blocked? e
... | yes blocked = yes (inj₂ blocked)
... | no not-blocked =
  no λ where
    (inj₁ value) → not-value value
    (inj₂ blocked) → not-blocked blocked

decide-global-deadlock :
  ∀ {n} {C : Conf n}
  → Dec
      (Data.List.Relation.Unary.All.All
        (λ e → IsValue e ⊎ CommunicationBlocked e)
        (exps C))
  → Dec
      (Data.List.Relation.Unary.Any.Any
        CommunicationBlocked
        (exps C))
  → Dec (RunnableAt C)
  → Dec (SynchronizationPossible C)
  → Dec (GlobalDeadlock C)
decide-global-deadlock (no not-quiescent) blocked? runnable? sync? =
  no λ where
    (global-deadlock quiescent _ _ _) →
      not-quiescent quiescent
decide-global-deadlock
    (yes quiescent) (no not-blocked) runnable? sync? =
  no λ where
    (global-deadlock _ blocked _ _) →
      not-blocked blocked
decide-global-deadlock
    (yes quiescent) (yes blocked) (yes runnable) sync? =
  no λ where
    (global-deadlock _ _ no-runnable _) →
      no-runnable runnable
decide-global-deadlock
    (yes quiescent) (yes blocked) (no no-runnable) (yes sync) =
  no λ where
    (global-deadlock _ _ _ no-sync) →
      no-sync sync
decide-global-deadlock
    (yes quiescent) (yes blocked) (no no-runnable) (no no-sync) =
  yes
    (global-deadlock
      quiescent
      blocked
      no-runnable
      no-sync)

global-deadlock? :
  ∀ {n} (C : Conf n)
  → Dec (GlobalDeadlock C)
global-deadlock? C =
  decide-global-deadlock
    (all-list? quiescent? (exps C))
    (any-list? communication-blocked? (exps C))
    (runnable-at? C)
    (synchronization-possible? C)
