module ExprActionResourcesFresh where

open import Data.Fin using (Fin)
import Data.Fin.Subset as Subset
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (subst)

open import Kinds using (KV; Lin; SLin; KP)
open import Variance using (Variance)
open import ExprSyntax using (NfTy; Expr; Value; V-Var; V-Pair; E-Val)
open import ExprNormalTyping
open import ExprContextProperties using
  ( AllUsed
  ; RemoveCtx
  ; RM-∅
  ; RM-drop
  ; RM-allused
  ; RM-lin
  ; RM-un
  )
open import ExprContextReduction using
  ( recvChanNf
  ; sendChanNf
  ; selectInNf
  ; selectSetInNf
  )
open import ExprSemantics using
  ( L-RecvVal
  ; L-SendVal
  ; L-SendLab
  ; _—[_]→_
  ; Act-Rcv
  ; Act-Send
  ; Act-Sel
  ; Act-AppL
  ; Act-AppR
  ; Act-TAppE
  ; Act-PairL
  ; Act-PairR
  ; Act-MatchE
  ; Act-LetPairE
  ; Act-LetUnitE
  )
open import AlgorithmicNFSubtyping using (_<:ₜ_; <:ₜ-trans)
open import ExprSubstitutionPreservationFresh using
  (exchange-value-after-value)
open import ExprTypingInversion using
  ( recvChan-subtype-shape
  ; sendChan-subtype-shape
  ; selectSetIn-subtype-shape
  )
open import ExprTypingStripFresh using (strip-value)

------------------------------------------------------------------------
-- Resources consumed by value communication

-- These predicates describe the complete action fragment, rather than
-- comparing the whole source context with the intermediate label context.
-- In particular, a linear payload is deliberately live between taking the
-- sending endpoint and typing the payload.

data RecvValueResources
    {n : ℕ}
    (Γ : Ctx [] n)
    (x : Fin n) : Set where

  recv-value-resources :
    ∀ {pk}
      {T : NfTy [] (KV pk Lin)}
      {S : NfTy [] SLin}
      {Γin Γused Γrest : Ctx [] n}
    → RemoveCtx Γ Γin Γrest
    → Γin ⊢ˡ x ∶ recvChanNf T S ⊣ Γused
    → AllUsed Γused
    → RecvValueResources Γ x

data SendValueResources
    {n : ℕ}
    (Γ : Ctx [] n)
    (x : Fin n)
    (v : Value [] n) : Set where

  send-value-resources :
    ∀ {pk}
      {T U : NfTy [] (KV pk Lin)}
      {S : NfTy [] SLin}
      {Γin Γv Γout Γrest : Ctx [] n}
    → RemoveCtx Γ Γin Γrest
    → Γin ⊢ˡ x ∶ sendChanNf T S ⊣ Γv
    → Γv ⊢ᵥ v ⇒ U ⊣ Γout
    → U <:ₜ T
    → AllUsed Γout
    → SendValueResources Γ x v

data SendLabelResources
    {n k : ℕ}
    (Γ : Ctx [] n)
    (x : Fin n)
    (i : Fin k) : Set where

  send-label-resources :
    ∀ {ss : Subset.Subset k}
      {v : Variance}
      {P : NfTy [] KP}
      {S : NfTy [] SLin}
      {Γin Γused Γrest : Ctx [] n}
    → i Subset.∈ ss
    → RemoveCtx Γ Γin Γrest
    → Γin ⊢ˡ x ∶ selectSetInNf ss v P S ⊣ Γused
    → AllUsed Γused
    → SendLabelResources Γ x i

remove-after :
  ∀ {Δ n} {Γ₀ G Γ₁ H Γ₂ : Ctx Δ n}
  → RemoveCtx Γ₀ G Γ₁
  → RemoveCtx Γ₁ H Γ₂
  → Σ (Ctx Δ n) λ ΓH → RemoveCtx Γ₀ H ΓH
remove-after RM-∅ RM-∅ = ∅ , RM-∅
remove-after (RM-drop first) (RM-drop second)
  with remove-after first second
... | ΓH , removed = _ , RM-drop removed
remove-after (RM-drop first) (RM-lin second)
  with remove-after first second
... | ΓH , removed = _ , RM-lin removed
remove-after (RM-lin first) (RM-allused second)
  with remove-after first second
... | ΓH , removed = _ , RM-drop removed
remove-after (RM-allused first) (RM-allused second)
  with remove-after first second
... | ΓH , removed = _ , RM-allused removed
remove-after (RM-un first) (RM-un second)
  with remove-after first second
... | ΓH , removed = _ , RM-un removed

recv-resources-before :
  ∀ {n} {Γ₀ G Γ₁ : Ctx [] n} {x : Fin n}
  → RemoveCtx Γ₀ G Γ₁
  → RecvValueResources Γ₁ x
  → RecvValueResources Γ₀ x
recv-resources-before first
    (recv-value-resources second take used)
  with remove-after first second
... | Γrest , removed =
  recv-value-resources removed take used

send-resources-before :
  ∀ {n} {Γ₀ G Γ₁ : Ctx [] n} {x : Fin n} {v : Value [] n}
  → RemoveCtx Γ₀ G Γ₁
  → SendValueResources Γ₁ x v
  → SendValueResources Γ₀ x v
send-resources-before first
    (send-value-resources second take payload sub used)
  with remove-after first second
... | Γrest , removed =
  send-value-resources removed take payload sub used

send-label-resources-before :
  ∀ {n k}
    {Γ₀ G Γ₁ : Ctx [] n}
    {x : Fin n}
    {i : Fin k}
  → RemoveCtx Γ₀ G Γ₁
  → SendLabelResources Γ₁ x i
  → SendLabelResources Γ₀ x i
send-label-resources-before first
    (send-label-resources i∈ second take used)
  with remove-after first second
... | Γrest , removed =
  send-label-resources i∈ removed take used

recv-direct-resources :
  ∀ {n pk} {Γ Γ′ : Ctx [] n} {x : Fin n}
    {T : NfTy [] (KV pk Lin)}
    {S : NfTy [] SLin}
  → Γ ⊢ E-Val (V-Var x) ⇐ recvChanNf T S ⊣ Γ′
  → RecvValueResources Γ x
recv-direct-resources
    (T-Check (T-Val (TV-Var-Lin take)) sub)
  with recvChan-subtype-shape sub
... | T₀ , S₀ , channel-eq , T₀<:T , S₀<:S
  with strip-value (TV-Var-Lin take)
... | Γin , Γused , removed , TV-Var-Lin take′ , used =
  recv-value-resources
    removed
    (subst
      (λ A → Γin ⊢ˡ _ ∶ A ⊣ Γused)
      channel-eq
      take′)
    used

send-direct-resources :
  ∀ {n pk} {Γ Γ′ : Ctx [] n} {x : Fin n} {v : Value [] n}
    {T : NfTy [] (KV pk Lin)}
    {S : NfTy [] SLin}
  → Γ ⊢ E-Val (V-Pair v (V-Var x))
      ⇐ pairNf T (sendChanNf T S) ⊣ Γ′
  → SendValueResources Γ x v
send-direct-resources
    (T-Check
      (T-Val (TV-Pair payload (TV-Var-Lin take)))
      (AlgorithmicNFSubtyping.<:ₜ-pair payload-sub channel-sub))
  with sendChan-subtype-shape channel-sub
... | T₀ , S₀ , channel-eq , T<:T₀ , S₀<:S
  with strip-value (TV-Pair payload (TV-Var-Lin take))
... | Γin , Γout , removed ,
      TV-Pair payload′ (TV-Var-Lin take′) , used
  with exchange-value-after-value payload′ (TV-Var-Lin take′)
... | Γv , TV-Var-Lin take-first , payload-after =
  send-value-resources
    removed
    (subst
      (λ A → Γin ⊢ˡ _ ∶ A ⊣ Γv)
      channel-eq
      take-first)
    payload-after
    (<:ₜ-trans payload-sub T<:T₀)
    used

send-label-direct-resources :
  ∀ {n k}
    {Γ Γ′ : Ctx [] n}
    {x : Fin n}
    {i : Fin k}
    {v : Variance}
    {P : NfTy [] KP}
    {S : NfTy [] SLin}
  → Γ ⊢ E-Val (V-Var x)
      ⇐ selectInNf v i P S ⊣ Γ′
  → SendLabelResources Γ x i
send-label-direct-resources
    (T-Check (T-Val (TV-Var-Lin take)) sub)
  with selectSetIn-subtype-shape sub
... | ss , P₀ , S₀ , i∈ , channel-eq , Psub , Ssub
  with strip-value (TV-Var-Lin take)
... | Γin , Γused , removed , TV-Var-Lin take′ , used =
  send-label-resources
    i∈
    removed
    (subst
      (λ A → Γin ⊢ˡ _ ∶ A ⊣ Γused)
      channel-eq
      take′)
    used

mutual

  recv-value-resources-synth :
    ∀ {n pk m} {Γ Γ′ : Ctx [] n}
      {e e′ : Expr [] n} {x : Fin n} {v : Value [] n}
      {T : NfTy [] (KV pk m)}
    → Γ ⊢ e ⇒ T ⊣ Γ′
    → e —[ L-RecvVal x v ]→ e′
    → RecvValueResources Γ x

  recv-value-resources-synth
      (T-App (T-Val TV-Receive₂) argument) Act-Rcv =
    recv-direct-resources argument
  recv-value-resources-synth (T-App left right) (Act-AppL step) =
    recv-value-resources-synth left step
  recv-value-resources-synth
      (T-App (T-Val value) right) (Act-AppR step)
    with strip-value value
  ... | G , G′ , removed , value′ , used =
    recv-resources-before removed
      (recv-value-resources-check right step)
  recv-value-resources-synth (T-TApp source) (Act-TAppE step) =
    recv-value-resources-synth source step
  recv-value-resources-synth (T-Pair left right) (Act-PairL step) =
    recv-value-resources-synth left step
  recv-value-resources-synth
      (T-Pair (T-Val value) right) (Act-PairR step)
    with strip-value value
  ... | G , G′ , removed , value′ , used =
    recv-resources-before removed
      (recv-value-resources-synth right step)
  recv-value-resources-synth (T-Match source branches join)
      (Act-MatchE step) =
    recv-value-resources-synth source step
  recv-value-resources-synth (T-LetPair source body)
      (Act-LetPairE step) =
    recv-value-resources-synth source step
  recv-value-resources-synth (T-LetUnit source body)
      (Act-LetUnitE step) =
    recv-value-resources-check source step

  recv-value-resources-check :
    ∀ {n pk m} {Γ Γ′ : Ctx [] n}
      {e e′ : Expr [] n} {x : Fin n} {v : Value [] n}
      {T : NfTy [] (KV pk m)}
    → Γ ⊢ e ⇐ T ⊣ Γ′
    → e —[ L-RecvVal x v ]→ e′
    → RecvValueResources Γ x
  recv-value-resources-check (T-Check source sub) step =
    recv-value-resources-synth source step

  send-value-resources-synth :
    ∀ {n pk m} {Γ Γ′ : Ctx [] n}
      {e e′ : Expr [] n} {x : Fin n} {v : Value [] n}
      {T : NfTy [] (KV pk m)}
    → Γ ⊢ e ⇒ T ⊣ Γ′
    → e —[ L-SendVal x v ]→ e′
    → SendValueResources Γ x v

  send-value-resources-synth
      (T-App (T-Val TV-Send₂) argument) Act-Send =
    send-direct-resources argument
  send-value-resources-synth (T-App left right) (Act-AppL step) =
    send-value-resources-synth left step
  send-value-resources-synth
      (T-App (T-Val value) right) (Act-AppR step)
    with strip-value value
  ... | G , G′ , removed , value′ , used =
    send-resources-before removed
      (send-value-resources-check right step)
  send-value-resources-synth (T-TApp source) (Act-TAppE step) =
    send-value-resources-synth source step
  send-value-resources-synth (T-Pair left right) (Act-PairL step) =
    send-value-resources-synth left step
  send-value-resources-synth
      (T-Pair (T-Val value) right) (Act-PairR step)
    with strip-value value
  ... | G , G′ , removed , value′ , used =
    send-resources-before removed
      (send-value-resources-synth right step)
  send-value-resources-synth (T-Match source branches join)
      (Act-MatchE step) =
    send-value-resources-synth source step
  send-value-resources-synth (T-LetPair source body)
      (Act-LetPairE step) =
    send-value-resources-synth source step
  send-value-resources-synth (T-LetUnit source body)
      (Act-LetUnitE step) =
    send-value-resources-check source step

  send-value-resources-check :
    ∀ {n pk m} {Γ Γ′ : Ctx [] n}
      {e e′ : Expr [] n} {x : Fin n} {v : Value [] n}
      {T : NfTy [] (KV pk m)}
    → Γ ⊢ e ⇐ T ⊣ Γ′
    → e —[ L-SendVal x v ]→ e′
    → SendValueResources Γ x v
  send-value-resources-check (T-Check source sub) step =
    send-value-resources-synth source step

mutual

  send-label-resources-synth :
    ∀ {n k pk m}
      {Γ Γ′ : Ctx [] n}
      {e e′ : Expr [] n}
      {x : Fin n}
      {i : Fin k}
      {T : NfTy [] (KV pk m)}
    → Γ ⊢ e ⇒ T ⊣ Γ′
    → e —[ L-SendLab x i ]→ e′
    → SendLabelResources Γ x i

  send-label-resources-synth
      (T-App (T-Val TV-Select₂) argument) Act-Sel =
    send-label-direct-resources argument
  send-label-resources-synth (T-App left right) (Act-AppL step) =
    send-label-resources-synth left step
  send-label-resources-synth
      (T-App (T-Val value) right) (Act-AppR step)
    with strip-value value
  ... | G , G′ , removed , value′ , used =
    send-label-resources-before removed
      (send-label-resources-check right step)
  send-label-resources-synth (T-TApp source) (Act-TAppE step) =
    send-label-resources-synth source step
  send-label-resources-synth (T-Pair left right) (Act-PairL step) =
    send-label-resources-synth left step
  send-label-resources-synth
      (T-Pair (T-Val value) right) (Act-PairR step)
    with strip-value value
  ... | G , G′ , removed , value′ , used =
    send-label-resources-before removed
      (send-label-resources-synth right step)
  send-label-resources-synth
      (T-Match source branches join) (Act-MatchE step) =
    send-label-resources-synth source step
  send-label-resources-synth
      (T-LetPair source body) (Act-LetPairE step) =
    send-label-resources-synth source step
  send-label-resources-synth
      (T-LetUnit source body) (Act-LetUnitE step) =
    send-label-resources-check source step

  send-label-resources-check :
    ∀ {n k pk m}
      {Γ Γ′ : Ctx [] n}
      {e e′ : Expr [] n}
      {x : Fin n}
      {i : Fin k}
      {T : NfTy [] (KV pk m)}
    → Γ ⊢ e ⇐ T ⊣ Γ′
    → e —[ L-SendLab x i ]→ e′
    → SendLabelResources Γ x i
  send-label-resources-check (T-Check source sub) step =
    send-label-resources-synth source step
