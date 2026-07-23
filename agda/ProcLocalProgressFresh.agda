module ProcLocalProgressFresh where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
import Data.Fin.Subset as Subset
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Kinds
import Types
open import Types using (Ty; T-Base)
open import NormalTypes using (N-Arrow)
open import AlgorithmicNFSubtyping using
  ( _<:ₜ_
  ; <:ₜ-base
  ; <:ₜ-pair
  )
open import ExprSyntax
open import ExprSubstitution using (substExpr; substExpr₂; substValue)
open import ExprNormalTyping
open import ExprContextShape
open import ExprSemantics
open import ProcProgressFreshDefinitions

------------------------------------------------------------------------
-- Session contexts are stable under expression resource consumption

session-resp-~Ctx :
  ∀ {n} {Γ Γ′ : Ctx [] n}
  → SessionCtx Γ
  → Γ ~Ctx Γ′
  → SessionCtx Γ′
session-resp-~Ctx session-∅ ∅~∅ = session-∅
session-resp-~Ctx (session-live session) (Lin~Lin shape) =
  session-live (session-resp-~Ctx session shape)
session-resp-~Ctx (session-live session) (Lin~Used shape) =
  session-used (session-resp-~Ctx session shape)
session-resp-~Ctx (session-used session) (Used~Used shape) =
  session-used (session-resp-~Ctx session shape)

session-after-value :
  ∀ {n pk m} {Γ Γ′ : Ctx [] n}
    {v : Value [] n} {T : NfTy [] (KV pk m)}
  → SessionCtx Γ
  → Γ ⊢ᵥ v ⇒ T ⊣ Γ′
  → SessionCtx Γ′
session-after-value session typing =
  session-resp-~Ctx session (value-preserves-~Ctx typing)

session-after-synth :
  ∀ {n pk m} {Γ Γ′ : Ctx [] n}
    {e : Expr [] n} {T : NfTy [] (KV pk m)}
  → SessionCtx Γ
  → Γ ⊢ e ⇒ T ⊣ Γ′
  → SessionCtx Γ′
session-after-synth session typing =
  session-resp-~Ctx session (synth-preserves-~Ctx typing)

session-after-check :
  ∀ {n pk m} {Γ Γ′ : Ctx [] n}
    {e : Expr [] n} {T : NfTy [] (KV pk m)}
  → SessionCtx Γ
  → Γ ⊢ e ⇐ T ⊣ Γ′
  → SessionCtx Γ′
session-after-check session typing =
  session-resp-~Ctx session (check-preserves-~Ctx typing)

------------------------------------------------------------------------
-- Canonical variables in a session-only context

session-no-unrestricted :
  ∀ {n pk} {Γ : Ctx [] n} {x : Fin n}
    {T : NfTy [] (KV pk Un)}
  → SessionCtx Γ
  → Γ ∋ᵘ x ∶ T
  → ⊥
session-no-unrestricted (session-live session) (thereᵘˡ membership) =
  session-no-unrestricted session membership
session-no-unrestricted (session-used session) (thereᵘ✖ membership) =
  session-no-unrestricted session membership

session-no-linear-data :
  ∀ {n} {Γ Γ′ : Ctx [] n} {x : Fin n}
    {T : NfTy [] TLin}
  → SessionCtx Γ
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
  → ⊥
session-no-linear-data (session-live session) (take-thereˡ take) =
  session-no-linear-data session take
session-no-linear-data (session-used session) (take-there✖ take) =
  session-no-linear-data session take

session-value-is-variable :
  ∀ {n} {Γ Γ′ : Ctx [] n} {v : Value [] n}
    {S : NfTy [] SLin}
  → SessionCtx Γ
  → Γ ⊢ᵥ v ⇒ S ⊣ Γ′
  → Σ (Fin n) λ x → v ≡ V-Var x
session-value-is-variable session (TV-Var-Lin {x = x} take) =
  x , refl

checked-session-value-is-variable :
  ∀ {n} {Γ Γ′ : Ctx [] n} {v : Value [] n}
    {S : NfTy [] SLin}
  → SessionCtx Γ
  → Γ ⊢ E-Val v ⇐ S ⊣ Γ′
  → Σ (Fin n) λ x → v ≡ V-Var x
checked-session-value-is-variable session
    (T-Check (T-Val typing) subtype) =
  session-value-is-variable session typing

send-value-shape :
  ∀ {n pk} {Γ Γ′ : Ctx [] n} {v : Value [] n}
    {T : NfTy [] (KV pk Lin)} {S : NfTy [] SLin}
  → SessionCtx Γ
  → Γ ⊢ E-Val v ⇐ pairNf T S ⊣ Γ′
  → Σ (Value [] n) λ payload →
      Σ (Fin n) λ x → v ≡ V-Pair payload (V-Var x)
send-value-shape session
    (T-Check (T-Val (TV-Pair payload channel))
      (<:ₜ-pair payload-sub channel-sub))
  with session-value-is-variable
         (session-after-value session payload)
         channel
... | x , refl = _ , x , refl
send-value-shape session
    (T-Check (T-Val (TV-Var-Lin take)) (<:ₜ-pair _ _)) =
  ⊥-elim (session-no-linear-data session take)

pair-value-shape :
  ∀ {n pk₁ pk₂} {Γ Γ′ : Ctx [] n} {v : Value [] n}
    {T : NfTy [] (KV pk₁ Lin)} {U : NfTy [] (KV pk₂ Lin)}
  → SessionCtx Γ
  → Γ ⊢ᵥ v ⇒ pairNf T U ⊣ Γ′
  → Σ (Value [] n) λ v₁ → Σ (Value [] n) λ v₂ →
      v ≡ V-Pair v₁ v₂
pair-value-shape session (TV-Pair first second) = _ , _ , refl
pair-value-shape session (TV-Var-Lin take) =
  ⊥-elim (session-no-linear-data session take)

unit-value-shape :
  ∀ {n} {Γ Γ′ : Ctx [] n} {v : Value [] n}
  → SessionCtx Γ
  → Γ ⊢ E-Val v ⇐ unitConstNf ⊣ Γ′
  → v ≡ V-Const C-Unit
unit-value-shape session
    (T-Check (T-Val (TV-Const CT-Unit)) <:ₜ-base) = refl
unit-value-shape session
    (T-Check (T-Val (TV-Var-Lin take)) <:ₜ-base) =
  ⊥-elim (session-no-linear-data session take)

------------------------------------------------------------------------
-- Evaluation contexts preserve active local states

app-left-runnable :
  ∀ {n} {e₁ e₂ : Expr [] n}
  → Runnable e₁
  → Runnable (E-App e₁ e₂)
app-left-runnable (run-β step) = run-β (Act-AppL step)
app-left-runnable (run-fork step) = run-fork (Act-AppL step)
app-left-runnable (run-new step) = run-new (Act-AppL step)

app-left-communication :
  ∀ {n} {e₁ e₂ : Expr [] n}
  → CommunicationBlocked e₁
  → CommunicationBlocked (E-App e₁ e₂)
app-left-communication
    (communication-blocked label target communication step) =
  communication-blocked
    label _ communication (Act-AppL step)

app-right-runnable :
  ∀ {n} {v : Value [] n} {e : Expr [] n}
  → Runnable e
  → Runnable (E-App (E-Val v) e)
app-right-runnable (run-β step) = run-β (Act-AppR step)
app-right-runnable (run-fork step) = run-fork (Act-AppR step)
app-right-runnable (run-new step) = run-new (Act-AppR step)

app-right-communication :
  ∀ {n} {v : Value [] n} {e : Expr [] n}
  → CommunicationBlocked e
  → CommunicationBlocked (E-App (E-Val v) e)
app-right-communication
    (communication-blocked label target communication step) =
  communication-blocked
    label _ communication (Act-AppR step)

pair-left-runnable :
  ∀ {n} {e₁ e₂ : Expr [] n}
  → Runnable e₁
  → Runnable (E-Pair e₁ e₂)
pair-left-runnable (run-β step) = run-β (Act-PairL step)
pair-left-runnable (run-fork step) = run-fork (Act-PairL step)
pair-left-runnable (run-new step) = run-new (Act-PairL step)

pair-left-communication :
  ∀ {n} {e₁ e₂ : Expr [] n}
  → CommunicationBlocked e₁
  → CommunicationBlocked (E-Pair e₁ e₂)
pair-left-communication
    (communication-blocked label target communication step) =
  communication-blocked
    label _ communication (Act-PairL step)

pair-right-runnable :
  ∀ {n} {v : Value [] n} {e : Expr [] n}
  → Runnable e
  → Runnable (E-Pair (E-Val v) e)
pair-right-runnable (run-β step) = run-β (Act-PairR step)
pair-right-runnable (run-fork step) = run-fork (Act-PairR step)
pair-right-runnable (run-new step) = run-new (Act-PairR step)

pair-right-communication :
  ∀ {n} {v : Value [] n} {e : Expr [] n}
  → CommunicationBlocked e
  → CommunicationBlocked (E-Pair (E-Val v) e)
pair-right-communication
    (communication-blocked label target communication step) =
  communication-blocked
    label _ communication (Act-PairR step)

tapp-runnable :
  ∀ {n K} {e : Expr [] n} {T : NfTy [] K}
  → Runnable e
  → Runnable (E-TApp e T)
tapp-runnable (run-β step) =
  run-β (Act-TAppE step)
tapp-runnable (run-fork step) =
  run-fork (Act-TAppE step)
tapp-runnable (run-new step) =
  run-new (Act-TAppE step)

tapp-communication :
  ∀ {n K} {e : Expr [] n} {T : NfTy [] K}
  → CommunicationBlocked e
  → CommunicationBlocked (E-TApp e T)
tapp-communication
    (communication-blocked label target communication step) =
  communication-blocked
    label _ communication (Act-TAppE step)

match-runnable :
  ∀ {n k} {ss : Subset.Subset k}
    {e : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
  → Runnable e
  → Runnable (E-Match e ne branches)
match-runnable (run-β step) = run-β (Act-MatchE step)
match-runnable (run-fork step) = run-fork (Act-MatchE step)
match-runnable (run-new step) = run-new (Act-MatchE step)

match-communication :
  ∀ {n k} {ss : Subset.Subset k}
    {e : Expr [] n} {ne : Subset.Nonempty ss}
    {branches : (i : Fin k) → i Subset.∈ ss → Expr [] (suc n)}
  → CommunicationBlocked e
  → CommunicationBlocked (E-Match e ne branches)
match-communication
    (communication-blocked label target communication step) =
  communication-blocked
    label _ communication (Act-MatchE step)

let-pair-runnable :
  ∀ {n} {e₁ : Expr [] n} {e₂ : Expr [] (suc (suc n))}
  → Runnable e₁
  → Runnable (E-LetPair e₁ e₂)
let-pair-runnable (run-β step) = run-β (Act-LetPairE step)
let-pair-runnable (run-fork step) = run-fork (Act-LetPairE step)
let-pair-runnable (run-new step) = run-new (Act-LetPairE step)

let-pair-communication :
  ∀ {n} {e₁ : Expr [] n} {e₂ : Expr [] (suc (suc n))}
  → CommunicationBlocked e₁
  → CommunicationBlocked (E-LetPair e₁ e₂)
let-pair-communication
    (communication-blocked label target communication step) =
  communication-blocked
    label _ communication (Act-LetPairE step)

let-unit-runnable :
  ∀ {n} {e₁ e₂ : Expr [] n}
  → Runnable e₁
  → Runnable (E-LetUnit e₁ e₂)
let-unit-runnable (run-β step) = run-β (Act-LetUnitE step)
let-unit-runnable (run-fork step) = run-fork (Act-LetUnitE step)
let-unit-runnable (run-new step) = run-new (Act-LetUnitE step)

let-unit-communication :
  ∀ {n} {e₁ e₂ : Expr [] n}
  → CommunicationBlocked e₁
  → CommunicationBlocked (E-LetUnit e₁ e₂)
let-unit-communication
    (communication-blocked label target communication step) =
  communication-blocked
    label _ communication (Act-LetUnitE step)

------------------------------------------------------------------------
-- Canonical function values

value-application-progress :
  ∀ {n pk₁ pk₂ m m₁ m₂}
    {Γ Γf Γ′ : Ctx [] n}
    {function : Value [] n}
    {argument : Expr [] n}
    {T : NfTy [] (KV pk₁ m₁)}
    {U : NfTy [] (KV pk₂ m₂)}
  → SessionCtx Γ
  → SessionCtx Γf
  → Γ ⊢ᵥ function ⇒ N-Arrow {m = m} T U ⊣ Γf
  → Γf ⊢ argument ⇐ T ⊣ Γ′
  → LocalProgress argument
  → LocalProgress (E-App (E-Val function) argument)
value-application-progress session session-f function argument
    (local-runnable runnable) =
  local-runnable (app-right-runnable runnable)
value-application-progress session session-f function argument
    (local-communication communication) =
  local-communication (app-right-communication communication)
value-application-progress session session-f
    (TV-Var-Lin take) argument
    (local-value (is-value value)) =
  ⊥-elim (session-no-linear-data session take)
value-application-progress session session-f
    (TV-Var-Un membership) argument
    (local-value (is-value value)) =
  ⊥-elim (session-no-unrestricted session membership)
value-application-progress session session-f
    (TV-Abs body) argument
    (local-value (is-value value)) =
  local-runnable (run-β Act-App)
value-application-progress session session-f
    (TV-Rec body) argument progress =
  local-runnable (run-β Act-Rec)
value-application-progress session session-f
    (TV-Const CT-Fork) argument
    (local-value (is-value value)) =
  local-runnable (run-fork Act-Fork)
value-application-progress session session-f
    (TV-Const CT-Close) argument
    (local-value (is-value value))
  with checked-session-value-is-variable session-f argument
... | x , refl =
  local-communication
    (communication-blocked
      (L-Close x)
      _
      comm-close
      Act-Close)
value-application-progress session session-f
    (TV-Receive₂ {T = T} {S = S}) argument
    (local-value (is-value value))
  with checked-session-value-is-variable session-f argument
... | x , refl =
  local-communication
    (communication-blocked
      (L-RecvVal x (V-Const C-Unit))
      _
      comm-recv-val
      (Act-Rcv {T = T} {S = S}))
value-application-progress session session-f
    (TV-Send₂ {T = T} {S = S}) argument
    (local-value (is-value value))
  with send-value-shape session-f argument
... | payload , x , refl =
  local-communication
    (communication-blocked
      (L-SendVal x payload)
      _
      comm-send-val
      (Act-Send {T = T} {S = S}))
value-application-progress session session-f
    (TV-Select₂ {v = variance} {i = i} {P = P} {S = S}) argument
    (local-value (is-value value))
  with checked-session-value-is-variable session-f argument
... | x , refl =
  local-communication
    (communication-blocked
      (L-SendLab x i)
      _
      comm-send-lab
      (Act-Sel {v = variance} {i = i} {P = P} {S = S}))

value-type-application-progress :
  ∀ {n K m}
    {Γ Γ′ : Ctx [] n}
    {function : Value [] n}
    {T : NfTy (K ∷ []) (KV KT m)}
    {U : NfTy [] K}
  → SessionCtx Γ
  → Γ ⊢ᵥ function ⇒ polyNf T ⊣ Γ′
  → LocalProgress (E-TApp (E-Val function) U)
value-type-application-progress session
    (TV-Var-Lin take) =
  ⊥-elim (session-no-linear-data session take)
value-type-application-progress session
    (TV-Var-Un membership) =
  ⊥-elim (session-no-unrestricted session membership)
value-type-application-progress {U = U} session
    (TV-TAbs body)
  rewrite sym (normalizeTy-id U) =
  local-runnable
    (run-β (Act-TApp {T = ⌞ U ⌟}))
value-type-application-progress {U = U} session
    (TV-Const CT-New)
  rewrite sym (normalizeTy-id U) =
  local-runnable
    (run-new (Act-New {S = ⌞ U ⌟}))
value-type-application-progress {U = U} session
    (TV-Const CT-Receive)
  rewrite sym (normalizeTy-id U) =
  local-runnable
    (run-β (Act-Receive₁ {T = ⌞ U ⌟}))
value-type-application-progress {U = U} session
    (TV-Const CT-Send)
  rewrite sym (normalizeTy-id U) =
  local-runnable
    (run-β (Act-Send₁ {T = ⌞ U ⌟}))
value-type-application-progress {U = U} session
    (TV-Const CT-Select)
  rewrite sym (normalizeTy-id U) =
  local-runnable
    (run-β (Act-Select₁ {P = ⌞ U ⌟}))
value-type-application-progress session TV-Receive₁ =
  local-runnable (run-β Act-Receive₂)
value-type-application-progress session TV-Send₁ =
  local-runnable (run-β Act-Send₂)
value-type-application-progress session TV-Select₁ =
  local-runnable (run-β Act-Select₂)

synth-value-inversion :
  ∀ {n pk m} {Γ Γ′ : Ctx [] n}
    {v : Value [] n} {T : NfTy [] (KV pk m)}
  → Γ ⊢ E-Val v ⇒ T ⊣ Γ′
  → Γ ⊢ᵥ v ⇒ T ⊣ Γ′
synth-value-inversion (T-Val typing) = typing

------------------------------------------------------------------------
-- Local progress

mutual

  synth-progress :
    ∀ {n pk m} {Γ Γ′ : Ctx [] n}
      {e : Expr [] n} {T : NfTy [] (KV pk m)}
    → SessionCtx Γ
    → Γ ⊢ e ⇒ T ⊣ Γ′
    → LocalProgress e
  synth-progress session (T-Val value) =
    local-value (is-value _)
  synth-progress session (T-Pair first second)
    with synth-progress session first
  ... | local-runnable runnable =
    local-runnable (pair-left-runnable runnable)
  ... | local-communication communication =
    local-communication (pair-left-communication communication)
  ... | local-value (is-value first-value)
    with synth-progress (session-after-synth session first) second
  ... | local-runnable runnable =
    local-runnable (pair-right-runnable runnable)
  ... | local-communication communication =
    local-communication (pair-right-communication communication)
  ... | local-value (is-value second-value) =
    local-runnable (run-β Act-PairV)
  synth-progress session (T-App function argument)
    with synth-progress session function
  ... | local-runnable runnable =
    local-runnable (app-left-runnable runnable)
  ... | local-communication communication =
    local-communication (app-left-communication communication)
  ... | local-value (is-value function-value) =
    value-application-progress
      session
      (session-after-synth session function)
      (synth-value-inversion function)
      argument
      (check-progress (session-after-synth session function) argument)
  synth-progress session (T-LetUnit first second)
    with check-progress session first
  ... | local-runnable runnable =
    local-runnable (let-unit-runnable runnable)
  ... | local-communication communication =
    local-communication (let-unit-communication communication)
  ... | local-value (is-value value)
    with unit-value-shape session first
  ... | refl =
    local-runnable (run-β Act-LetUnit)
  synth-progress session (T-LetPair first body)
    with synth-progress session first
  ... | local-runnable runnable =
    local-runnable (let-pair-runnable runnable)
  ... | local-communication communication =
    local-communication (let-pair-communication communication)
  ... | local-value (is-value value)
    with pair-value-shape session (synth-value-inversion first)
  ... | first-value , second-value , refl =
    local-runnable (run-β Act-LetPair)
  synth-progress session (T-Match {ne = ne} scrutinee branches join)
    with synth-progress session scrutinee
  ... | local-runnable runnable =
    local-runnable (match-runnable runnable)
  ... | local-communication communication =
    local-communication (match-communication communication)
  ... | local-value (is-value value)
    with session-value-is-variable
           session
           (synth-value-inversion scrutinee)
  ... | x , refl
    with ne
  ... | i , i∈ =
    local-communication
      (communication-blocked
        (L-RecvLab x i)
        _
        comm-recv-lab
        (Act-Match i∈))
  synth-progress session (T-TApp function)
    with synth-progress session function
  ... | local-runnable runnable =
    local-runnable (tapp-runnable runnable)
  ... | local-communication communication =
    local-communication (tapp-communication communication)
  ... | local-value (is-value function-value) =
    value-type-application-progress
      session
      (synth-value-inversion function)

  check-progress :
    ∀ {n pk m} {Γ Γ′ : Ctx [] n}
      {e : Expr [] n} {T : NfTy [] (KV pk m)}
    → SessionCtx Γ
    → Γ ⊢ e ⇐ T ⊣ Γ′
    → LocalProgress e
  check-progress session (T-Check synthesis subtype) =
    synth-progress session synthesis

local-progress : LocalProgressTheorem
local-progress = check-progress
