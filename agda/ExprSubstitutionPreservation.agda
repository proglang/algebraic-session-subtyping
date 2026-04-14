module ExprSubstitutionPreservation where

open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Subset as Subset
open import Data.List using (_∷_)
open import Data.Vec using (here; there) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Kinds
open import Kits
open import Ext using (ext)
open import Types using (Ty; Ty-Syntax; Ty-Traversal)
open import Variance using (Variance)
open import AlgorithmicNFSubtyping using (_<:ₜ_)
open import ExprSyntax using
  ( Expr
  ; Value
  ; E-Val
  ; E-LetPair
  ; E-Match
  ; V-Abs
  ; V-Rec
  ; V-TAbs
  )
open import ExprSubstitution using
  ( Sub
  ; extSub
  ; extSub2
  ; liftTySub
  ; wkTyValue
  ; substTyValueWith
  ; substValueWith
  ; substExprWith
  )
open import ExprNormalTyping
open import ExprSubstitutionTyping using
  ( substTyNfWith
  ; substTyCtxWith
  ; substTyWith-preserves-value
  )
open import ExprContextReduction
  using
    ( AllUsed
    ; AU-∅
    ; AU-used
    ; AU-un
    ; LinearDisjoint
    ; LD-∅
    ; LD-used-used
    ; LD-used-live
    ; LD-live-used
    ; LD-un-un
    ; allUsedCtx
    ; MergeCtx
    ; MC-∅
    ; MC-used-used
    ; MC-used-left
    ; MC-used-right
    ; MC-un
    ; RemoveCtx
    ; RM-∅
    ; RM-drop
    ; RM-allused
    ; RM-lin
    ; RM-un
    ; allUsed-merge
    ; rm-allUsed
    ; compose-merge-remove
    ; compose-merge-remove2
    ; merge-disjoint
    ; used-head-eq
    )
open import ExprTypingProperties
  using
    ( FrameCtx
    ; FC-∅
    ; FC-frame
    ; FC-allused
    ; FC-un
    ; replay-value
    )
open import ExprTypingLeftover
  using
    ( leftover-synth
    ; leftover-check
    ; leftover-value
    ; strip-lin-used
    )

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (⋯-id)


tailSub : ∀ {Δ n m} → Sub Δ (suc n) m → Sub Δ n m
tailSub σ x = σ (suc x)

used∷-injective :
  ∀ {Δ n pk}
    {T : NfTy Δ (KV pk Lin)}
    {Γ₁ Γ₂ : Ctx Δ n}
  → used∷ {T = T} Γ₁ ≡ used∷ {T = T} Γ₂
  → Γ₁ ≡ Γ₂
used∷-injective refl = refl

∷ᵘ-injective :
  ∀ {Δ n pk}
    {T : NfTy Δ (KV pk Un)}
    {Γ₁ Γ₂ : Ctx Δ n}
  → (T ∷ᵘ Γ₁) ≡ (T ∷ᵘ Γ₂)
  → Γ₁ ≡ Γ₂
∷ᵘ-injective refl = refl

∷ˡ-injective :
  ∀ {Δ n pk}
    {T : NfTy Δ (KV pk Lin)}
    {Γ₁ Γ₂ : Ctx Δ n}
  → (T ∷ˡ Γ₁) ≡ (T ∷ˡ Γ₂)
  → Γ₁ ≡ Γ₂
∷ˡ-injective refl = refl

take-input-unique′ :
  ∀ {Δ n pk₁ pk₂}
    {Γ₁ Γ₂ Γo : Ctx Δ n}
    {x : Fin n}
    {T₁ : NfTy Δ (KV pk₁ Lin)}
    {T₂ : NfTy Δ (KV pk₂ Lin)}
  → Γ₁ ⊢ˡ x ∶ T₁ ⊣ Γo
  → Γ₂ ⊢ˡ x ∶ T₂ ⊣ Γo
  → Γ₁ ≡ Γ₂
take-input-unique′ take-here take-here = refl
take-input-unique′ (take-thereˡ d₁) (take-thereˡ d₂) =
  cong (B-Lin _ ▻_) (take-input-unique′ d₁ d₂)
take-input-unique′ (take-thereᵘ d₁) (take-thereᵘ d₂) =
  cong (B-Un _ ▻_) (take-input-unique′ d₁ d₂)
take-input-unique′ (take-there✖ d₁) (take-there✖ d₂) =
  cong (B-Used _ ▻_) (take-input-unique′ d₁ d₂)

take-input-unique :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ Γo : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
  → Γ₁ ⊢ˡ x ∶ T ⊣ Γo
  → Γ₂ ⊢ˡ x ∶ T ⊣ Γo
  → Γ₁ ≡ Γ₂
take-input-unique = take-input-unique′

take-no-un :
  ∀ {Δ n pk pk′}
    {Γ Γ′ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
    {U : NfTy Δ (KV pk′ Un)}
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
  → Γ′ ∋ᵘ x ∶ U
  → ⊥
take-no-un take-here ()
take-no-un (take-thereˡ take) (thereᵘˡ x∈) = take-no-un take x∈
take-no-un (take-thereᵘ take) (thereᵘᵘ x∈) = take-no-un take x∈
take-no-un (take-there✖ take) (thereᵘ✖ x∈) = take-no-un take x∈

nothing≢just :
  ∀ {a} {A : Set a} {x : A}
  → nothing ≡ just x
  → ⊥
nothing≢just ()

cast-synth-out :
  ∀ {Δ n K}
    {Γin Γo₁ Γo₂ : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ K}
  → Γin ⊢ e ⇒ T ⊣ Γo₁
  → Γo₁ ≡ Γo₂
  → Γin ⊢ e ⇒ T ⊣ Γo₂
cast-synth-out d eq = subst (λ X → _ ⊢ _ ⇒ _ ⊣ X) eq d

branchjoin⁺-nonempty :
  ∀ {Δ k}
    {ss : Subset.Subset k}
    {V : (i : Fin k) → i Subset.∈ ss → NfTy Δ TLin}
    {U : NfTy Δ TLin}
    {sub : (i : Fin k) → (i∈ : i Subset.∈ ss) → V i i∈ <:ₜ U}
  → BranchJoin⁺ ss V ≡ just (U , sub)
  → Subset.Nonempty ss
branchjoin⁺-nonempty {ss = []ᵥ} ()
branchjoin⁺-nonempty {ss = Subset.inside ∷ᵥ _} _ = zero , here
branchjoin⁺-nonempty {ss = Subset.outside ∷ᵥ ss} {V = V} eq
  with BranchJoin⁺ ss (λ i i∈ → V (suc i) (there i∈)) in bj
... | nothing = ⊥-elim (nothing≢just eq)
... | just (N , sub′) =
  let i , i∈ =
        branchjoin⁺-nonempty
          {ss = ss}
          {V = λ i i∈ → V (suc i) (there i∈)}
          {U = N}
          {sub = sub′}
          bj
  in suc i , there i∈

mutual

  synth-input-unique′ :
    ∀ {Δ n K₁ K₂}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {e : Expr Δ n}
      {T₁ : NfTy Δ K₁}
      {T₂ : NfTy Δ K₂}
    → Γ₁ ⊢ e ⇒ T₁ ⊣ Γo
    → Γ₂ ⊢ e ⇒ T₂ ⊣ Γo
    → Γ₁ ≡ Γ₂
  synth-input-unique′ (T-Val d₁) (T-Val d₂) =
    value-input-unique′ d₁ d₂
  synth-input-unique′ (T-Pair d₁₁ d₁₂) (T-Pair d₂₁ d₂₂)
    with synth-input-unique′ d₁₂ d₂₂
  ... | eqmid rewrite eqmid =
    synth-input-unique′ d₁₁ d₂₁
  synth-input-unique′ (T-App d₁₁ d₁₂) (T-App d₂₁ d₂₂)
    with check-input-unique′ d₁₂ d₂₂
  ... | eqmid rewrite eqmid =
    synth-input-unique′ d₁₁ d₂₁
  synth-input-unique′ (T-LetUnit d₁₁ d₁₂) (T-LetUnit d₂₁ d₂₂)
    with synth-input-unique′ d₁₂ d₂₂
  ... | eqmid rewrite eqmid =
    check-input-unique′ d₁₁ d₂₁
  synth-input-unique′
    {Γo = Γo}
    (T-LetPair {Γ₂ = Γm₁} {T = A₁} {U = B₁} {e₂ = e₂} d₁₁ d₁₂)
    (T-LetPair {Γ₂ = Γm₂} {T = A₂} {U = B₂} d₂₁ d₂₂)
    with synth-input-unique′ d₁₂ d₂₂′
    where
    eqo :
      used∷ {T = A₂} (used∷ {T = B₂} Γo)
        ≡
      used∷ {T = A₁} (used∷ {T = B₁} Γo)
    eqo =
      trans
        (cong (B-Used A₂ ▻_)
          (used-head-eq {T₁ = B₂} {T₂ = B₁} {Γ = Γo}))
        (used-head-eq {T₁ = A₂} {T₂ = A₁} {Γ = B-Used B₁ ▻ Γo})

    d₂₂′ = cast-synth-out d₂₂ eqo
  ... | eqbody
    with cong (λ where (_ ▻ Γ) → Γ) (cong (λ where (_ ▻ Γ) → Γ) eqbody)
  ... | eqmid rewrite eqmid =
    synth-input-unique′ d₁₁ d₂₁
  synth-input-unique′
    {Γo = Γo}
    (T-Match {Γ₂ = Γm₁} d₁ bs₁ j₁)
    (T-Match {Γ₂ = Γm₂} d₂ bs₂ _)
    with synth-input-unique′ b₁ b₂′
    where
    i = proj₁ (branchjoin⁺-nonempty j₁)

    i∈ = proj₂ (branchjoin⁺-nonempty j₁)

    b₁ = bs₁ i i∈

    b₂′ = cast-synth-out (bs₂ i i∈) (used-head-eq {Γ = Γo})
  ... | eqbranch
    with cong (λ where (_ ▻ Γ) → Γ) eqbranch
  ... | eqmid rewrite eqmid =
    synth-input-unique′ d₁ d₂
  synth-input-unique′ (T-TApp d₁) (T-TApp d₂) =
    synth-input-unique′ d₁ d₂

  check-input-unique′ :
    ∀ {Δ n pk m}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {e : Expr Δ n}
      {T₁ T₂ : NfTy Δ (KV pk m)}
    → Γ₁ ⊢ e ⇐ T₁ ⊣ Γo
    → Γ₂ ⊢ e ⇐ T₂ ⊣ Γo
    → Γ₁ ≡ Γ₂
  check-input-unique′ (T-Check d₁ _) (T-Check d₂ _) =
    synth-input-unique′ d₁ d₂

  value-input-unique′ :
    ∀ {Δ n K₁ K₂}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {v : Value Δ n}
      {T₁ : NfTy Δ K₁}
      {T₂ : NfTy Δ K₂}
    → Γ₁ ⊢ᵥ v ⇒ T₁ ⊣ Γo
    → Γ₂ ⊢ᵥ v ⇒ T₂ ⊣ Γo
    → Γ₁ ≡ Γ₂
  value-input-unique′ (TV-Const _) (TV-Const _) = refl
  value-input-unique′ (TV-Var-Lin take₁) (TV-Var-Lin take₂) =
    take-input-unique′ take₁ take₂
  value-input-unique′ (TV-Var-Lin take) (TV-Var-Un x∈) =
    ⊥-elim (take-no-un take x∈)
  value-input-unique′ (TV-Var-Un x∈) (TV-Var-Lin take) =
    ⊥-elim (take-no-un take x∈)
  value-input-unique′ (TV-Var-Un _) (TV-Var-Un _) = refl
  value-input-unique′ (TV-Abs d₁) (TV-Abs d₂)
    with synth-input-unique′ d₁ d₂
  ... | eq = ∷ˡ-injective eq
  value-input-unique′ (TV-Rec d₁) (TV-Rec d₂)
    with check-input-unique′ d₁ d₂
  ... | eq = ∷ᵘ-injective eq
  value-input-unique′ (TV-TAbs d₁) (TV-TAbs d₂) =
    wkCtx-injective (value-input-unique′ d₁ d₂)
  value-input-unique′ (TV-Pair d₁₁ d₁₂) (TV-Pair d₂₁ d₂₂)
    with value-input-unique′ d₁₂ d₂₂
  ... | eqmid rewrite eqmid =
    value-input-unique′ d₁₁ d₂₁
  value-input-unique′ TV-Receive₁ TV-Receive₁ = refl
  value-input-unique′ TV-Receive₂ TV-Receive₂ = refl
  value-input-unique′ TV-Send₁ TV-Send₁ = refl
  value-input-unique′ TV-Send₂ TV-Send₂ = refl
  value-input-unique′ TV-Select₁ TV-Select₁ = refl
  value-input-unique′ TV-Select₂ TV-Select₂ = refl

synth-input-unique :
  ∀ {Δ n K}
    {Γ₁ Γ₂ Γo : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ K}
  → Γ₁ ⊢ e ⇒ T ⊣ Γo
  → Γ₂ ⊢ e ⇒ T ⊣ Γo
  → Γ₁ ≡ Γ₂
synth-input-unique = synth-input-unique′

check-input-unique :
  ∀ {Δ n pk m}
    {Γ₁ Γ₂ Γo : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk m)}
  → Γ₁ ⊢ e ⇐ T ⊣ Γo
  → Γ₂ ⊢ e ⇐ T ⊣ Γo
  → Γ₁ ≡ Γ₂
check-input-unique = check-input-unique′

value-input-unique :
  ∀ {Δ n K}
    {Γ₁ Γ₂ Γo : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ K}
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γo
  → Γ₂ ⊢ᵥ v ⇒ T ⊣ Γo
  → Γ₁ ≡ Γ₂
value-input-unique = value-input-unique′

infix 4 _⊢σ_∶_⊣_

data _⊢σ_∶_⊣_ {Δ m} (Γt : Ctx Δ m) : ∀ {n} → Sub Δ n m → Ctx Δ n → Ctx Δ m → Set where
  S-∅ :
    AllUsed Γt
    →
    Γt ⊢σ (λ ()) ∶ ∅ ⊣ Γt

  S-Lin :
    ∀ {n pk}
      {σ : Sub Δ (suc n) m}
      {Γ : Ctx Δ n}
      {T : NfTy Δ (KV pk Lin)}
      {Γrest Γv Γv′ Γo : Ctx Δ m}
    → MergeCtx Γrest Γv Γt
    → LinearDisjoint Γrest Γv
    → Γv ⊢ᵥ σ zero ⇒ T ⊣ Γv′
    → AllUsed Γv′
    → Γrest ⊢σ tailSub σ ∶ Γ ⊣ Γo
    → Γt ⊢σ σ ∶ (T ∷ˡ Γ) ⊣ Γo

  S-Un :
    ∀ {n pk}
      {σ : Sub Δ (suc n) m}
      {Γ : Ctx Δ n}
      {T : NfTy Δ (KV pk Un)}
      {Γo : Ctx Δ m}
    → allUsedCtx Γt ⊢ᵥ σ zero ⇒ T ⊣ allUsedCtx Γt
    → Γt ⊢σ tailSub σ ∶ Γ ⊣ Γo
    → Γt ⊢σ σ ∶ (T ∷ᵘ Γ) ⊣ Γo

  S-Used :
    ∀ {n pk}
      {σ : Sub Δ (suc n) m}
      {Γ : Ctx Δ n}
      {T : NfTy Δ (KV pk Lin)}
      {Γo : Ctx Δ m}
    → Γt ⊢σ tailSub σ ∶ Γ ⊣ Γo
    → Γt ⊢σ σ ∶ used∷ {T = T} Γ ⊣ Γo


frame-allUsedCtx :
  ∀ {Δ n} (Γ : Ctx Δ n) → FrameCtx Γ (allUsedCtx Γ) Γ
frame-allUsedCtx ∅ = FC-∅
frame-allUsedCtx (B-Lin T ▻ Γ) = FC-frame (frame-allUsedCtx Γ)
frame-allUsedCtx (B-Un T ▻ Γ) = FC-un (frame-allUsedCtx Γ)
frame-allUsedCtx (B-Used T ▻ Γ) = FC-allused (frame-allUsedCtx Γ)

replay-allUsed-value :
  ∀ {Δ n K}
    {Γ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ K}
  → allUsedCtx Γ ⊢ᵥ v ⇒ T ⊣ allUsedCtx Γ
  → Γ ⊢ᵥ v ⇒ T ⊣ Γ
replay-allUsed-value {Γ = Γ} d =
  replay-value d (frame-allUsedCtx Γ) (frame-allUsedCtx Γ)

postulate
  substTyNfWith-weaken :
    ∀ {Δ K K′}
      (T : NfTy Δ K)
    → substTyNfWith T (weakenₛ K′) ≡ wkNfTy {K′ = K′} T

  substTyCtxWith-weaken :
    ∀ {Δ n K}
      (Γ : Ctx Δ n)
    → substTyCtxWith Γ (weakenₛ K) ≡ wkCtx {K = K} Γ

  substTyValueWith-weaken :
    ∀ {Δ n K}
      (v : Value Δ n)
    → substTyValueWith (weakenₛ K) v ≡ wkTyValue {K = K} v

wkTy-preserves-value :
  ∀ {Δ n K K′}
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ K}
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  → wkCtx {K = K′} Γ₁ ⊢ᵥ wkTyValue {K = K′} v ⇒ wkNfTy {K′ = K′} T ⊣ wkCtx Γ₂
wkTy-preserves-value {K′ = K′} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = v} {T = T} d =
  let
    base :
      substTyCtxWith Γ₁ (weakenₛ K′)
        ⊢ᵥ substTyValueWith (weakenₛ K′) v
          ⇒ substTyNfWith T (weakenₛ K′)
          ⊣ substTyCtxWith Γ₂ (weakenₛ K′)
    base = substTyWith-preserves-value {ϕ = weakenₛ K′} d

    step₁ :
      substTyCtxWith Γ₁ (weakenₛ K′)
        ⊢ᵥ substTyValueWith (weakenₛ K′) v
          ⇒ substTyNfWith T (weakenₛ K′)
          ⊣ wkCtx Γ₂
    step₁ =
      subst
        (λ X →
          substTyCtxWith Γ₁ (weakenₛ K′)
            ⊢ᵥ substTyValueWith (weakenₛ K′) v
              ⇒ substTyNfWith T (weakenₛ K′)
              ⊣ X)
        (substTyCtxWith-weaken {K = K′} Γ₂)
        base

    step₂ :
      substTyCtxWith Γ₁ (weakenₛ K′)
        ⊢ᵥ substTyValueWith (weakenₛ K′) v
          ⇒ wkNfTy {K′ = K′} T
          ⊣ wkCtx Γ₂
    step₂ =
      subst
        (λ X →
          substTyCtxWith Γ₁ (weakenₛ K′)
            ⊢ᵥ substTyValueWith (weakenₛ K′) v
              ⇒ X
              ⊣ wkCtx Γ₂)
        (substTyNfWith-weaken {K′ = K′} T)
        step₁

    step₃ :
      substTyCtxWith Γ₁ (weakenₛ K′)
        ⊢ᵥ wkTyValue {K = K′} v
          ⇒ wkNfTy {K′ = K′} T
          ⊣ wkCtx Γ₂
    step₃ =
      subst
        (λ X →
          substTyCtxWith Γ₁ (weakenₛ K′)
            ⊢ᵥ X
              ⇒ wkNfTy {K′ = K′} T
              ⊣ wkCtx Γ₂)
        (substTyValueWith-weaken {K = K′} v)
        step₂
  in
  subst
    (λ X →
      X ⊢ᵥ wkTyValue {K = K′} v
        ⇒ wkNfTy {K′ = K′} T
        ⊣ wkCtx Γ₂)
    (substTyCtxWith-weaken {K = K′} Γ₁)
    step₃

wkAllUsed :
  ∀ {Δ n K}
    {Γ : Ctx Δ n}
  → AllUsed Γ
  → AllUsed (wkCtx {K = K} Γ)
wkAllUsed AU-∅ = AU-∅
wkAllUsed (AU-used au) = AU-used (wkAllUsed au)
wkAllUsed (AU-un au) = AU-un (wkAllUsed au)

wkMergeCtx :
  ∀ {Δ n}
    {Γx Γv Γt : Ctx Δ n}
    {K : Kind}
  → MergeCtx Γx Γv Γt
  → MergeCtx (wkCtx {K = K} Γx) (wkCtx {K = K} Γv) (wkCtx {K = K} Γt)
wkMergeCtx MC-∅ = MC-∅
wkMergeCtx (MC-used-used m) = MC-used-used (wkMergeCtx m)
wkMergeCtx (MC-used-left m) = MC-used-left (wkMergeCtx m)
wkMergeCtx (MC-used-right m) = MC-used-right (wkMergeCtx m)
wkMergeCtx (MC-un m) = MC-un (wkMergeCtx m)

wkCtx-allUsedCtx :
  ∀ {Δ n}
    {Γ : Ctx Δ n}
    {K : Kind}
  → wkCtx {K = K} (allUsedCtx Γ) ≡ allUsedCtx (wkCtx Γ)
wkCtx-allUsedCtx {Γ = ∅} = refl
wkCtx-allUsedCtx {Γ = B-Lin T ▻ Γ} = cong (B-Used (wkNfTy T) ▻_) wkCtx-allUsedCtx
wkCtx-allUsedCtx {Γ = B-Un T ▻ Γ} = cong (B-Un (wkNfTy T) ▻_) wkCtx-allUsedCtx
wkCtx-allUsedCtx {Γ = B-Used T ▻ Γ} = cong (B-Used (wkNfTy T) ▻_) wkCtx-allUsedCtx

wkLinearDisjoint :
  ∀ {Δ n K}
    {Γ₁ Γ₂ : Ctx Δ n}
  → LinearDisjoint Γ₁ Γ₂
  → LinearDisjoint (wkCtx {K = K} Γ₁) (wkCtx {K = K} Γ₂)
wkLinearDisjoint LD-∅ = LD-∅
wkLinearDisjoint (LD-used-used ld) =
  LD-used-used (wkLinearDisjoint ld)
wkLinearDisjoint (LD-used-live ld) =
  LD-used-live (wkLinearDisjoint ld)
wkLinearDisjoint (LD-live-used ld) =
  LD-live-used (wkLinearDisjoint ld)
wkLinearDisjoint (LD-un-un ld) =
  LD-un-un (wkLinearDisjoint ld)

liftTySub-empty :
  ∀ {Δ m K}
  → liftTySub {Δ = Δ} {n = 0} {m = m} {K = K} (λ ()) ≡ (λ ())
liftTySub-empty = ext _ _ λ ()

emptySub-η :
  ∀ {Δ m}
  → (σ : Sub Δ 0 m)
  → σ ≡ (λ ())
emptySub-η σ = ext σ (λ ()) λ ()

liftTySub-preserves-σ :
  ∀ {Δ n m K}
    {Γs : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
  → Γt ⊢σ σ ∶ Γs ⊣ Γo
  → wkCtx {K = K} Γt ⊢σ liftTySub σ ∶ wkCtx Γs ⊣ wkCtx Γo
liftTySub-preserves-σ {n = 0} {K = K} {Γt = Γt} {σ = σ} (S-∅ au)
  rewrite emptySub-η σ
  =
  subst
    (λ τ → wkCtx Γt ⊢σ τ ∶ ∅ ⊣ wkCtx Γt)
    (sym (liftTySub-empty {K = K}))
    (S-∅ (wkAllUsed au))
liftTySub-preserves-σ {K = K} (S-Lin {T = T} m ld dv au σtail) =
  S-Lin
    (wkMergeCtx {K = K} m)
    (wkLinearDisjoint {K = K} ld)
    (wkTy-preserves-value {K′ = K} dv)
    (wkAllUsed au)
    (liftTySub-preserves-σ {K = K} σtail)
liftTySub-preserves-σ {K = K} {σ = σ} (S-Un {T = T} d0 σtail) =
  S-Un
    (subst
      (λ X → X ⊢ᵥ liftTySub σ zero ⇒ wkNfTy {K′ = K} T ⊣ X)
      (wkCtx-allUsedCtx {K = K})
      (wkTy-preserves-value {K′ = K} d0))
    (liftTySub-preserves-σ {K = K} σtail)
liftTySub-preserves-σ {K = K} (S-Used σtail) =
  S-Used (liftTySub-preserves-σ {K = K} σtail)

postulate
  consume-lin-head-merge :
    ∀ {Δ n K}
      {Γrest Γv Γt Γv′ : Ctx Δ n}
      {v : Value Δ n}
      {T : NfTy Δ K}
    → MergeCtx Γrest Γv Γt
    → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
    → AllUsed Γv′
    → Γt ⊢ᵥ v ⇒ T ⊣ Γrest

  lift-lin-through-merge :
    ∀ {Δ n K}
      {Γrest Γmid Γv Γt : Ctx Δ n}
      {v : Value Δ n}
      {T : NfTy Δ K}
    → MergeCtx Γrest Γv Γt
    → Γrest ⊢ᵥ v ⇒ T ⊣ Γmid
    → Σ (Ctx Δ n) λ Γtout →
        Σ (LinearDisjoint Γmid Γv) λ ld →
          MergeCtx Γmid Γv Γtout
          × (Γt ⊢ᵥ v ⇒ T ⊣ Γtout)

  lift-un-through-merge :
    ∀ {Δ n pk}
      {Γrest Γv Γt : Ctx Δ n}
      {v : Value Δ n}
      {T : NfTy Δ (KV pk Un)}
    → MergeCtx Γrest Γv Γt
    → Γrest ⊢ᵥ v ⇒ T ⊣ Γrest
    → Γt ⊢ᵥ v ⇒ T ⊣ Γt

  lift-un-head-through-lookup :
    ∀ {Δ n m pk pk′}
      {Γ Γ′ : Ctx Δ n}
      {Γt Γt′ : Ctx Δ m}
      {σ : Sub Δ (suc n) m}
      {Γo : Ctx Δ m}
      {x : Fin n}
      {T : NfTy Δ (KV pk Un)}
      {U : NfTy Δ (KV pk′ Lin)}
    → Γ ⊢ˡ x ∶ U ⊣ Γ′
    → Γt ⊢σ tailSub σ ∶ Γ ⊣ Γo
    → Γt′ ⊢σ tailSub σ ∶ Γ′ ⊣ Γo
    → allUsedCtx Γt ⊢ᵥ σ zero ⇒ T ⊣ allUsedCtx Γt
    → allUsedCtx Γt′ ⊢ᵥ σ zero ⇒ T ⊣ allUsedCtx Γt′

  unliftTySub-preserves-σ :
    ∀ {Δ n m K}
      {Γs : Ctx Δ n}
      {Γtwk : Ctx (K ∷ Δ) m}
      {Γo : Ctx Δ m}
      {σ : Sub Δ n m}
    → Γtwk ⊢σ liftTySub σ ∶ wkCtx {K = K} Γs ⊣ wkCtx {K = K} Γo
    → Σ (Ctx Δ m) λ Γt →
        (Γtwk ≡ wkCtx {K = K} Γt)
        × (Γt ⊢σ σ ∶ Γs ⊣ Γo)

  extSub-preserves-σ-lin :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Lin)}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → (T ∷ˡ Γt) ⊢σ extSub σ ∶ (T ∷ˡ Γs) ⊣ used∷ {T = T} Γo

  extSub-preserves-σ-un :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Un)}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → (T ∷ᵘ Γt) ⊢σ extSub σ ∶ (T ∷ᵘ Γs) ⊣ (T ∷ᵘ Γo)

  unextSub-used :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γtwk Γowk : Ctx Δ (suc m)}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Lin)}
    → Γtwk ⊢σ extSub σ ∶ used∷ {T = T} Γs ⊣ Γowk
    → Σ (Ctx Δ m) λ Γt →
      Σ (Ctx Δ m) λ Γo →
        (Γtwk ≡ used∷ {T = T} Γt)
        × (Γowk ≡ used∷ {T = T} Γo)
        × (Γt ⊢σ σ ∶ Γs ⊣ Γo)

  unextSub-un-fixed :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {Γtwk Γowk : Ctx Δ (suc m)}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Un)}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Γtwk ⊢σ extSub σ ∶ (T ∷ᵘ Γs) ⊣ Γowk
    → Γtwk ≡ (T ∷ᵘ Γt)
    × Γowk ≡ (T ∷ᵘ Γo)


extSub2-preserves-σ-lin2 :
  ∀ {Δ n m pk pk′}
    {Γs : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {T : NfTy Δ (KV pk Lin)}
    {U : NfTy Δ (KV pk′ Lin)}
  → Γt ⊢σ σ ∶ Γs ⊣ Γo
  → (T ∷ˡ (U ∷ˡ Γt)) ⊢σ extSub2 σ ∶ (T ∷ˡ (U ∷ˡ Γs)) ⊣ used∷ {T = T} (used∷ {T = U} Γo)
extSub2-preserves-σ-lin2 σok =
  extSub-preserves-σ-lin (extSub-preserves-σ-lin σok)

unextSub2-used2 :
  ∀ {Δ n m pk pk′}
    {Γs : Ctx Δ n}
    {Γtwk Γowk : Ctx Δ (suc (suc m))}
    {σ : Sub Δ n m}
    {T : NfTy Δ (KV pk Lin)}
    {U : NfTy Δ (KV pk′ Lin)}
  → Γtwk ⊢σ extSub2 σ ∶ used∷ {T = T} (used∷ {T = U} Γs) ⊣ Γowk
  → Σ (Ctx Δ m) λ Γt →
    Σ (Ctx Δ m) λ Γo →
      (Γtwk ≡ used∷ {T = T} (used∷ {T = U} Γt))
      × (Γowk ≡ used∷ {T = T} (used∷ {T = U} Γo))
      × (Γt ⊢σ σ ∶ Γs ⊣ Γo)
unextSub2-used2 {Γs = Γs} {Γtwk = Γtwk} {σ = σ} {T = T} {U = U} σok
  with unextSub-used {Γtwk = Γtwk} {σ = extSub σ} {T = T} σok
... | Γu , Γou , eq₁ , eqo₁ , σu
  with unextSub-used {Γtwk = Γu} {σ = σ} {T = U} σu
... | Γt , Γo , eq₂ , eqo₂ , σt =
  Γt , Γo ,
  trans eq₁ (cong (used∷ {T = T}) eq₂) ,
  trans eqo₁ (cong (used∷ {T = T}) eqo₂) ,
  σt


mutual

  substσ-lookup-lin :
    ∀ {Δ n m pk}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {x : Fin n}
      {T : NfTy Δ (KV pk Lin)}
    → Γs ⊢ˡ x ∶ T ⊣ Γs′
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Σ (Ctx Δ m) λ Γt′ →
        (Γt ⊢ᵥ σ x ⇒ T ⊣ Γt′)
        × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-lookup-lin take-here (S-Lin m ld dv au σtail) =
    _ , consume-lin-head-merge m dv au , S-Used σtail
  substσ-lookup-lin (take-thereˡ take) (S-Lin m ld dv au σtail)
    with substσ-lookup-lin take σtail
  ... | Γmid , dmid , σtail′
    with lift-lin-through-merge m dmid
  ... | Γtout , ldout , mout , dout =
    Γtout , dout , S-Lin mout ldout dv au σtail′
  substσ-lookup-lin {σ = σ} (take-thereᵘ take) (S-Un d0 σtail)
    with substσ-lookup-lin take σtail
  ... | Γt′ , d′ , σtail′ =
    Γt′ , d′ , S-Un (lift-un-head-through-lookup {σ = σ} take σtail σtail′ d0) σtail′
  substσ-lookup-lin (take-there✖ take) (S-Used σtail)
    with substσ-lookup-lin take σtail
  ... | Γt′ , d′ , σtail′ =
    Γt′ , d′ , S-Used σtail′

  substσ-lookup-un :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {x : Fin n}
      {T : NfTy Δ (KV pk Un)}
    → Γs ∋ᵘ x ∶ T
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Γt ⊢ᵥ σ x ⇒ T ⊣ Γt

  substσ-lookup-un hereᵘ (S-Un d0 σtail) =
    replay-allUsed-value d0
  substσ-lookup-un (thereᵘˡ x∈) (S-Lin m ld dv au σtail) =
    lift-un-through-merge m (substσ-lookup-un x∈ σtail)
  substσ-lookup-un (thereᵘᵘ x∈) (S-Un d0 σtail) =
    substσ-lookup-un x∈ σtail
  substσ-lookup-un (thereᵘ✖ x∈) (S-Used σtail) =
    substσ-lookup-un x∈ σtail

subst-next-ctx :
  ∀ {Δ n m}
    (Γs G Γs′ : Ctx Δ n)
    (Γt Γo : Ctx Δ m)
  → (rm : RemoveCtx Γs G Γs′)
  → (σ : Sub Δ n m)
  → (⊢σ : Γt ⊢σ σ ∶ Γs ⊣ Γo)
  → Σ (Ctx Δ m) λ Γt′ →
    Σ (Ctx Δ m) λ G′ →
    Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo
      × allUsedCtx Γt ≡ allUsedCtx Γt′
      × RemoveCtx Γt G′ Γt′
subst-next-ctx ∅ ∅ ∅ Γt Γo RM-∅ σ (S-∅ x) = Γt , allUsedCtx Γt , (S-∅ x) , refl , rm-allUsed Γt
subst-next-ctx (B-Lin T ▻ Γs) (B-Used T ▻ G) (B-Lin T ▻ Γs′) Γt Γo (RM-drop rm) σ (S-Lin {Γrest = Γrest} {Γv} mcs lds dσ₀ auv ⊢σ)
  with subst-next-ctx Γs G Γs′ Γrest Γo rm (tailSub σ) ⊢σ
... | Γt′ , G′ , ⊢σ′ , au-transport , rmg
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm  = Γt″ , G′ , S-Lin mc (merge-disjoint mc) dσ₀ auv ⊢σ′ , trans (allUsed-merge mcs) (trans au-transport (sym (allUsed-merge mc))) , rm
subst-next-ctx (B-Lin T ▻ Γs) (B-Lin T ▻ G) (B-Used T ▻ Γs′) Γt Γo (RM-lin rm) σ (S-Lin {Γrest = Γrest} {Γv} mcs lds dσ₀ auv ⊢σ)
  with subst-next-ctx Γs G Γs′ Γrest Γo rm (tailSub σ) ⊢σ
... | Γt′ , G′ , ⊢σ′ , au-transport , rmg
  with compose-merge-remove mcs rmg
... | G″ , rm″ = Γt′ , G″ , S-Used ⊢σ′ , trans (allUsed-merge mcs) au-transport , rm″
subst-next-ctx (B-Un _ ▻ Γs) (B-Un _ ▻ G) (B-Un _ ▻ Γs′) Γt Γo (RM-un rm) σ (S-Un aux ⊢σ)
  with subst-next-ctx Γs G Γs′ Γt Γo rm (tailSub σ) ⊢σ
... | Γt′ , G′ , ⊢σ′ , au-transport , rmg rewrite au-transport = Γt′ , G′ , (S-Un aux ⊢σ′) , refl , rmg
subst-next-ctx (B-Used T ▻ Γs) (B-Used T ▻ G) (B-Used T ▻ Γs′) Γt Γo (RM-allused rm) σ (S-Used ⊢σ)
  with subst-next-ctx Γs G Γs′ Γt Γo rm (tailSub σ) ⊢σ
... | Γt′ , G′ , ⊢σ′ , au-transport , rmg = Γt′ , G′ , (S-Used ⊢σ′) , au-transport , rmg

subst-next-ctx-connect :
  ∀ {Δ n m}
    {Γs G Γs′ : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
  → (rm : RemoveCtx Γs G Γs′)
  → (σin : Γt ⊢σ σ ∶ Γs ⊣ Γo)
  → ∀ {Γt′}
  → Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo
  → ∀ {Γti}
  → Γti ⊢σ σ ∶ Γs′ ⊣ Γo
  → Γti ≡ Γt′
subst-next-ctx-connect rm σin σcalc σout = σ-target-unique σout σcalc
  where
  σ-target-unique :
    ∀ {Δ₀ n₀ m₀}
      {Γs₀ : Ctx Δ₀ n₀}
      {Γt₁ Γt₂ Γo₀ : Ctx Δ₀ m₀}
      {σ₀ : Sub Δ₀ n₀ m₀}
    → Γt₁ ⊢σ σ₀ ∶ Γs₀ ⊣ Γo₀
    → Γt₂ ⊢σ σ₀ ∶ Γs₀ ⊣ Γo₀
    → Γt₁ ≡ Γt₂
  σ-target-unique (S-∅ _) (S-∅ _) = refl
  σ-target-unique
    (S-Lin {Γrest = Γrest₁} m₁ _ dv₁ au₁ σtail₁)
    (S-Lin {Γrest = Γrest₂} m₂ _ dv₂ au₂ σtail₂)
    with σ-target-unique σtail₁ σtail₂
  ... | eqrest rewrite eqrest =
    value-input-unique
      (consume-lin-head-merge m₁ dv₁ au₁)
      (consume-lin-head-merge m₂ dv₂ au₂)
  σ-target-unique (S-Un _ σtail₁) (S-Un _ σtail₂) =
    σ-target-unique σtail₁ σtail₂
  σ-target-unique (S-Used σtail₁) (S-Used σtail₂) =
    σ-target-unique σtail₁ σtail₂

pack-synth-result :
  ∀ {Δ n m K}
    {Γs Γs′ : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {e : Expr Δ n}
    {T : NfTy Δ K}
  → Γs ⊢ e ⇒ T ⊣ Γs′
  → (Σ (Ctx Δ m) λ Γt′ →
      (Γt ⊢ substExprWith σ e ⇒ T ⊣ Γt′)
      × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo))
  → Σ (Ctx Δ n) λ G →
      RemoveCtx Γs G Γs′ ×
      Σ (Ctx Δ m) λ Γt′ →
        (Γt ⊢ substExprWith σ e ⇒ T ⊣ Γt′)
        × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)
pack-synth-result d (Γt′ , d′ , σok′) with leftover-synth d
... | G , rm = G , rm , Γt′ , d′ , σok′

pack-check-result :
  ∀ {Δ n m pk mult}
    {Γs Γs′ : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk mult)}
  → Γs ⊢ e ⇐ T ⊣ Γs′
  → (Σ (Ctx Δ m) λ Γt′ →
      (Γt ⊢ substExprWith σ e ⇐ T ⊣ Γt′)
      × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo))
  → Σ (Ctx Δ n) λ G →
      RemoveCtx Γs G Γs′ ×
      Σ (Ctx Δ m) λ Γt′ →
        (Γt ⊢ substExprWith σ e ⇐ T ⊣ Γt′)
        × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)
pack-check-result d (Γt′ , d′ , σok′) with leftover-check d
... | G , rm = G , rm , Γt′ , d′ , σok′

pack-value-result :
  ∀ {Δ n m K}
    {Γs Γs′ : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {v : Value Δ n}
    {T : NfTy Δ K}
  → Γs ⊢ᵥ v ⇒ T ⊣ Γs′
  → (Σ (Ctx Δ m) λ Γt′ →
      (Γt ⊢ᵥ substValueWith σ v ⇒ T ⊣ Γt′)
      × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo))
  → Σ (Ctx Δ n) λ G →
      RemoveCtx Γs G Γs′ ×
      Σ (Ctx Δ m) λ Γt′ →
        (Γt ⊢ᵥ substValueWith σ v ⇒ T ⊣ Γt′)
        × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)
pack-value-result d (Γt′ , d′ , σok′) with leftover-value d
... | G , rm = G , rm , Γt′ , d′ , σok′

pack-synth-eq :
  ∀ {Δ n m K}
    {Γs Γs′ : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {e : Expr Δ n}
    {T : NfTy Δ K}
  → (de : Γs ⊢ e ⇒ T ⊣ Γs′)
  → (⊢σ : Γt ⊢σ σ ∶ Γs ⊣ Γo)
  → (Σ (Ctx Δ m) λ Γt′ →
      (Γt ⊢ substExprWith σ e ⇒ T ⊣ Γt′)
      × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo))
  → let _ , rm = leftover-synth de in
    let Γt0 , _ = subst-next-ctx _ _ _ _ _ rm σ ⊢σ in
    Σ (Ctx Δ m) λ Γt′ →
      Γt0 ≡ Γt′
      × (Γt ⊢ substExprWith σ e ⇒ T ⊣ Γt′)
      × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)
pack-synth-eq {σ = σ} de ⊢σ (Γt′ , d′ , σok′)
  with leftover-synth de
... | G , rm
  with subst-next-ctx _ _ _ _ _ rm σ ⊢σ
... | Γt0 , _ , σ0 , _ , _ =
  Γt′ , sym (subst-next-ctx-connect rm ⊢σ σ0 σok′) , d′ , σok′


mutual

  substσ-preserves-value-abs-body :
    ∀ {Δ n m}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : Ty Δ TLin}
      {e : Expr Δ (suc n)}
      {U : NfTy Δ TLin}
    → (normalizeTy T ∷ˡ Γs) ⊢ e ⇒ U ⊣ used∷ {T = normalizeTy T} Γs′
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Σ (Ctx Δ n) λ G →
        RemoveCtx Γs G Γs′ ×
        Σ (Ctx Δ m) λ Γt′ →
          ((normalizeTy T ∷ˡ Γt) ⊢ substExprWith (extSub σ) e ⇒ U ⊣ used∷ {T = normalizeTy T} Γt′)
          × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-value-abs-body d σok
    with substσ-preserves-synth d (extSub-preserves-σ-lin σok)
  ... | Γtwk , _ , d′ , σwk
    with unextSub-used σwk
  ... | Γt′ , Γo′ , eq , eqo , σok′
    rewrite eq | used∷-injective eqo
    with leftover-synth d
  ... | G₀ , rm₀
    with strip-lin-used rm₀
  ... | G , rm =
      G , rm , Γt′ , d′ , σok′

  substσ-preserves-value-rec-body :
    ∀ {Δ n m}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T U : Ty Δ TLin}
      {v : Value Δ (suc n)}
    → (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γs)
        ⊢ E-Val v ⇐ unArrNf (normalizeTy T) (normalizeTy U)
        ⊣ (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γs)
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γt)
        ⊢ E-Val (substValueWith (extSub σ) v) ⇐ unArrNf (normalizeTy T) (normalizeTy U)
        ⊣ (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γt)

  substσ-preserves-value-rec-body {Γt = Γt} {σ = σ} {T = T} {U = U} d σok
    with substσ-preserves-check d (extSub-preserves-σ-un σok)
  ... | Γtwk , d′ , σwk
    with unextSub-un-fixed {Γt = Γt} {σ = σ} {T = unArrNf (normalizeTy T) (normalizeTy U)} σok σwk
  ... | eq , eqo
    rewrite eq =
      d′

  substσ-preserves-synth-letpair :
    ∀ {Δ n m}
      {Γs Γmid Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {pk₁ pk₂}
      {T : NfTy Δ (KV pk₁ Lin)}
      {U : NfTy Δ (KV pk₂ Lin)}
      {V : NfTy Δ TLin}
      {e₁ : Expr Δ n}
      {e₂ : Expr Δ (suc (suc n))}
    → Γs ⊢ e₁ ⇒ pairNf T U ⊣ Γmid
    → (T ∷ˡ (U ∷ˡ Γmid)) ⊢ e₂ ⇒ V ⊣ used∷ {T = T} (used∷ {T = U} Γs′)
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Σ (Ctx Δ n) λ G →
        RemoveCtx Γs G Γs′ ×
        Σ (Ctx Δ m) λ Γt′ →
          (Γt ⊢ substExprWith σ (E-LetPair e₁ e₂) ⇒ V ⊣ Γt′)
          × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-synth-letpair d₁ d₂ σok
    with substσ-preserves-synth d₁ σok
  ... | Γtmid , _ , d₁′ , σmid
    with substσ-preserves-synth d₂ (extSub2-preserves-σ-lin2 σmid)
  ... | Γtwk , _ , d₂′ , σwk
    with unextSub2-used2 σwk
  ... | Γt′ , Γo′ , eq , eqo , σok′
    rewrite eq | used∷-injective (used∷-injective eqo) =
      pack-synth-result
        (T-LetPair d₁ d₂)
        (Γt′ , T-LetPair d₁′ d₂′ , σok′)

  substσ-preserves-value-abs :
    ∀ {Δ n m}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : Ty Δ TLin}
      {e : Expr Δ (suc n)}
      {U : NfTy Δ TLin}
    → Γs ⊢ᵥ V-Abs T e ⇒ U ⊣ Γs′
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Σ (Ctx Δ n) λ G →
        RemoveCtx Γs G Γs′ ×
        Σ (Ctx Δ m) λ Γt′ →
          (Γt ⊢ᵥ substValueWith σ (V-Abs T e) ⇒ U ⊣ Γt′)
          × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-value-abs (TV-Abs {T = T} d) σok
    with substσ-preserves-value-abs-body {T = T} d σok
  ... | G , rm , Γt′ , d′ , σok′ =
    G , rm , Γt′ , TV-Abs d′ , σok′

  substσ-preserves-value-rec :
    ∀ {Δ n m}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T U : Ty Δ TLin}
      {v : Value Δ (suc n)}
      {W : NfTy Δ (KV KT Un)}
    → Γs ⊢ᵥ V-Rec T U v ⇒ W ⊣ Γs′
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Σ (Ctx Δ n) λ G →
        RemoveCtx Γs G Γs′ ×
        Σ (Ctx Δ m) λ Γt′ →
          (Γt ⊢ᵥ substValueWith σ (V-Rec T U v) ⇒ W ⊣ Γt′)
          × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-value-rec (TV-Rec {T = T} {U = U} d) σok =
    pack-value-result
      (TV-Rec d)
      (_ , TV-Rec (substσ-preserves-value-rec-body {T = T} {U = U} d σok) , σok)

  substσ-preserves-value-tabs :
    ∀ {Δ n m K m′}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {v : Value (K ∷ Δ) n}
      {T : NfTy (K ∷ Δ) (KV KT m′)}
    → Γs ⊢ᵥ V-TAbs K v ⇒ polyNf T ⊣ Γs′
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Σ (Ctx Δ n) λ G →
        RemoveCtx Γs G Γs′ ×
        Σ (Ctx Δ m) λ Γt′ →
          (Γt ⊢ᵥ substValueWith σ (V-TAbs K v) ⇒ polyNf T ⊣ Γt′)
          × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-value-tabs (TV-TAbs {K = K} d) σok
    with substσ-preserves-value d (liftTySub-preserves-σ {K = K} σok)
  ... | _ , _ , Γtwk′ , d′ , σwk′
    with unliftTySub-preserves-σ {K = K} σwk′
  ... | Γt′ , eqwk , σok′
    rewrite eqwk =
      pack-value-result
        (TV-TAbs d)
        (Γt′ , TV-TAbs d′ , σok′)

  substσ-preserves-value :
    ∀ {Δ n m K}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {v : Value Δ n}
      {T : NfTy Δ K}
    → Γs ⊢ᵥ v ⇒ T ⊣ Γs′
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Σ (Ctx Δ n) λ G →
        RemoveCtx Γs G Γs′ ×
        Σ (Ctx Δ m) λ Γt′ →
          (Γt ⊢ᵥ substValueWith σ v ⇒ T ⊣ Γt′)
          × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-value (TV-Const cT) σok =
    pack-value-result (TV-Const cT) (_ , TV-Const cT , σok)
  substσ-preserves-value (TV-Var-Lin take) σok =
    pack-value-result (TV-Var-Lin take) (substσ-lookup-lin take σok)
  substσ-preserves-value (TV-Var-Un x∈) σok =
    pack-value-result (TV-Var-Un x∈) (_ , substσ-lookup-un x∈ σok , σok)
  substσ-preserves-value d@(TV-Abs _) σok =
    substσ-preserves-value-abs d σok
  substσ-preserves-value d@(TV-Rec _) σok =
    substσ-preserves-value-rec d σok
  substσ-preserves-value d@(TV-TAbs _) σok =
    substσ-preserves-value-tabs d σok
  substσ-preserves-value (TV-Pair d₁ d₂) σok
    with substσ-preserves-value d₁ σok
  ... | _ , _ , Γt₂ , d₁′ , σok₂
    with substσ-preserves-value d₂ σok₂
  ... | _ , _ , Γt₃ , d₂′ , σok₃ =
    pack-value-result (TV-Pair d₁ d₂) (Γt₃ , TV-Pair d₁′ d₂′ , σok₃)
  substσ-preserves-value TV-Receive₁ σok =
    pack-value-result TV-Receive₁ (_ , TV-Receive₁ , σok)
  substσ-preserves-value TV-Receive₂ σok =
    pack-value-result TV-Receive₂ (_ , TV-Receive₂ , σok)
  substσ-preserves-value TV-Send₁ σok =
    pack-value-result TV-Send₁ (_ , TV-Send₁ , σok)
  substσ-preserves-value TV-Send₂ σok =
    pack-value-result TV-Send₂ (_ , TV-Send₂ , σok)
  substσ-preserves-value TV-Select₁ σok =
    pack-value-result TV-Select₁ (_ , TV-Select₁ , σok)
  substσ-preserves-value TV-Select₂ σok =
    pack-value-result TV-Select₂ (_ , TV-Select₂ , σok)

  substσ-preserves-synth-match :
    ∀ {Δ n m k}
      {Γs Γmid Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {ss : Subset.Subset (suc k)} {v : Variance}
      {ssbranches : Subset.Subset (suc k)} {incl : ss Subset.⊆ ssbranches}
      {ne : Subset.Nonempty ssbranches}
      {P : NfTy Δ KP} {S : NfTy Δ SLin} {U : NfTy Δ TLin}
      {e : Expr Δ n}
      {branches : (i : Fin (suc k)) → i Subset.∈ ssbranches → Expr Δ (suc n)}
      {V : (i : Fin (suc k)) → i Subset.∈ ssbranches → NfTy Δ TLin}
      {sub : (i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) → V i i∈ <:ₜ U}
    → Γs ⊢ e ⇒ MatchBranchInput ss v P S ⊣ Γmid
    → ((i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) →
        (MatchBranchOutput ssbranches v P S i i∈ ∷ˡ Γmid)
          ⊢ branches i i∈ ⇒ V i i∈ ⊣ used∷ {T = MatchBranchOutput ssbranches v P S i i∈} Γs′)
    → BranchJoin⁺ ssbranches V ≡ just (U , sub)
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Σ (Ctx Δ m) λ Γt′ →
        (Γt ⊢ substExprWith σ (E-Match {ss = ssbranches} e ne branches) ⇒ U ⊣ Γt′)
        × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-synth-match
    {σ = σ}
    {ss = ss} {v = v}
    {ssbranches = ssbranches} {incl = incl} {ne = ne}
    {P = P} {S = S} {U = U} {branches = branches} {V = V}
    d bs j σok
    with substσ-preserves-synth d σok
  ... | Γt₂ , _ , d′ , σmid
    with leftover-synth (bs (proj₁ ne) (proj₂ ne))
  ... | G₀ , rm₀
    with strip-lin-used rm₀
  ... | G₀′ , rm₀′
    with subst-next-ctx _ G₀′ _ Γt₂ _ rm₀′ σ σmid
  ... | Γt′ , _ , σok′ , _ , _ =
      Γt′ , T-Match {ss = ss} {ssbranches = ssbranches} {incl = incl} d′ bs′ j , σok′
    where
    branch :
      (i : Fin _)
      → (i∈ : i Subset.∈ ssbranches)
      → Σ (Ctx _ _) λ Γti →
          ((MatchBranchOutput ssbranches v P S i i∈ ∷ˡ Γt₂)
            ⊢ substExprWith (extSub σ) (branches i i∈) ⇒ V i i∈
            ⊣ used∷ {T = MatchBranchOutput ssbranches v P S i i∈} Γti)
          × (Γti ⊢σ σ ∶ _ ⊣ _)
    branch i i∈
      with substσ-preserves-synth (bs i i∈) (extSub-preserves-σ-lin σmid)
    ... | Γtwki , _ , di , σwki
      with unextSub-used σwki
    ... | Γti , Γoi , eqi , eqoi , σoki
      rewrite eqi | used∷-injective eqoi = Γti , di , σoki

    bs′ :
      (i : Fin _)
      → (i∈ : i Subset.∈ ssbranches)
      → (MatchBranchOutput ssbranches v P S i i∈ ∷ˡ Γt₂)
          ⊢ substExprWith (extSub σ) (branches i i∈) ⇒ V i i∈
          ⊣ used∷ {T = MatchBranchOutput ssbranches v P S i i∈} Γt′
    bs′ i i∈ with branch i i∈
    ... | Γti , di , σoki
      rewrite subst-next-ctx-connect rm₀′ σmid σok′ σoki = di

  substσ-preserves-synth :
    ∀ {Δ n m K}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {e : Expr Δ n}
      {T : NfTy Δ K}
    → (de : Γs ⊢ e ⇒ T ⊣ Γs′)
    → (⊢σ : Γt ⊢σ σ ∶ Γs ⊣ Γo)
    → let G , rm = leftover-synth de in
      let Γt0 , _ = subst-next-ctx _ _ _ _ _ rm σ ⊢σ in
      Σ (Ctx Δ m) λ Γt′ →
        Γt0 ≡ Γt′
        × (Γt ⊢ substExprWith σ e ⇒ T ⊣ Γt′)
        × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-synth (T-Val d) σok
    with substσ-preserves-value d σok
  ... | _ , _ , Γt′ , d′ , σok′ =
    pack-synth-eq (T-Val d) σok (Γt′ , T-Val d′ , σok′)
  substσ-preserves-synth (T-Pair d₁ d₂) σok
    with substσ-preserves-synth d₁ σok
  ... | Γt₂ , _ , d₁′ , σok₂
    with substσ-preserves-synth d₂ σok₂
  ... | Γt₃ , _ , d₂′ , σok₃ =
    pack-synth-eq (T-Pair d₁ d₂) σok (Γt₃ , T-Pair d₁′ d₂′ , σok₃)
  substσ-preserves-synth (T-App d₁ d₂) σok
    with substσ-preserves-synth d₁ σok
  ... | Γt₂ , _ , d₁′ , σok₂
    with substσ-preserves-check d₂ σok₂
  ... | Γt₃ , d₂′ , σok₃ =
    pack-synth-eq (T-App d₁ d₂) σok (Γt₃ , T-App d₁′ d₂′ , σok₃)
  substσ-preserves-synth (T-LetUnit d₁ d₂) σok
    with substσ-preserves-check d₁ σok
  ... | Γt₂ , d₁′ , σok₂
    with substσ-preserves-synth d₂ σok₂
  ... | Γt₃ , _ , d₂′ , σok₃ =
    pack-synth-eq (T-LetUnit d₁ d₂) σok (Γt₃ , T-LetUnit d₁′ d₂′ , σok₃)
  substσ-preserves-synth d@(T-LetPair d₁ d₂) σok
    with substσ-preserves-synth-letpair d₁ d₂ σok
  ... | _ , _ , Γt′ , d′ , σok′ =
    pack-synth-eq d σok (Γt′ , d′ , σok′)
  substσ-preserves-synth (T-Match {ss = ss} {incl = incl} d bs j) σok =
    pack-synth-eq
      (T-Match {ss = ss} {incl = incl} d bs j)
      σok
      (substσ-preserves-synth-match {ss = ss} {incl = incl} d bs j σok)
  substσ-preserves-synth (T-TApp d) σok
    with substσ-preserves-synth d σok
  ... | Γt′ , _ , d′ , σok′ =
    pack-synth-eq (T-TApp d) σok (Γt′ , T-TApp d′ , σok′)

  substσ-preserves-check :
    ∀ {Δ n m pk mult}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk mult)}
    → Γs ⊢ e ⇐ T ⊣ Γs′
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Σ (Ctx Δ m) λ Γt′ →
        (Γt ⊢ substExprWith σ e ⇐ T ⊣ Γt′)
        × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-check (T-Check d sub) σok
    with substσ-preserves-synth d σok
  ... | Γt′ , _ , d′ , σok′ =
    Γt′ , T-Check d′ sub , σok′
