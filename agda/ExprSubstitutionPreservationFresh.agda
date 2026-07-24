module ExprSubstitutionPreservationFresh where

open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Subset
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import Ext using (ext)
open import Util using (dependent-ext₂)
open import Kinds using
  ( Kind
  ; PreKind
  ; Multiplicity
  ; Lin
  ; Un
  ; KV
  )
open import Types using (Ty; Ty-Syntax; Ty-Traversal)
open import Kits
open import AlgorithmicNFSubtyping using (_<:ₜ_)
open import ExprSyntax using
  ( NfTy
  ; Expr
  ; Value
  ; E-Val
  ; V-Var
  ; V-Const
  ; V-Abs
  ; V-Rec
  ; V-TAbs
  ; V-Pair
  ; V-Receive₁
  ; V-Receive₂
  ; V-Send₁
  ; V-Send₂
  ; V-Select₁
  ; V-Select₂
  ; E-App
  ; E-TApp
  ; E-LetUnit
  ; E-Pair
  ; E-LetPair
  ; E-Match
  )
open import ExprSubstitution using
  ( Sub
  ; Ren
  ; extRen
  ; extRen2
  ; renameValue
  ; renameExpr
  ; renTyValue
  ; renTyExpr
  ; extSub
  ; extSub2
  ; liftTySub
  ; wkValue
  ; wkTyValue
  ; substValueWith
  ; substExprWith
  ; singleSub
  ; substExpr
  )
open import ExprNormalTyping using
  ( Binding
  ; B-Lin
  ; B-Un
  ; B-Used
  ; Ctx
  ; ∅
  ; _▻_
  ; _∷ˡ_
  ; _∷ᵘ_
  ; wkNfTy
  ; wkNfTy-injective
  ; wkBinding
  ; wkBinding-injective
  ; wkCtx
  ; wkCtx-injective
  ; _∋ˡ_∶_
  ; hereˡ
  ; thereˡˡ
  ; thereˡᵘ
  ; thereˡ✖
  ; _∋ᵘ_∶_
  ; hereᵘ
  ; thereᵘˡ
  ; thereᵘᵘ
  ; thereᵘ✖
  ; _⊢ˡ_∶_⊣_
  ; take-here
  ; take-thereˡ
  ; take-thereᵘ
  ; take-there✖
  ; _⊢ᵥ_⇒_⊣_
  ; TV-Const
  ; TV-Var-Lin
  ; TV-Var-Un
  ; TV-Abs
  ; TV-Rec
  ; TV-TAbs
  ; TV-Pair
  ; TV-Receive₁
  ; TV-Receive₂
  ; TV-Send₁
  ; TV-Send₂
  ; TV-Select₁
  ; TV-Select₂
  ; _⊢_⇒_⊣_
  ; T-Val
  ; T-Pair
  ; T-App
  ; T-LetUnit
  ; T-LetPair
  ; T-Match
  ; T-TApp
  ; _⊢_⇐_⊣_
  ; T-Check
  )
open import ExprContextShape using
  ( _~Ctx_
  ; ∅~∅
  ; Lin~Lin
  ; Un~Un
  ; Lin~Used
  ; Used~Used
  ; drop-lin-used
  ; value-preserves-~Ctx
  ; synth-preserves-~Ctx
  ; check-preserves-~Ctx
  )
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
  ; remove-allUsedCtx
  ; compose-merge-remove
  ; compose-merge-remove2
  )
open import ExprTypingProperties using
  ( frame-unique
  ; frame-value
  ; frame-synth
  ; frame-check
  ; wkFrameCtx
  ; replay-value
  ; replay-value-allUsed
  )
open import ExprTypingLeftover using
  ( leftover-value
  ; leftover-synth
  ; leftover-check
  ; strip-wk
  )
open import ExprTypingStrengthening using
  ( _<:Γ_
  ; <:-sub-lin
  ; <:Γ-refl
  ; used-tail-<:Γ
  ; lin-used-head-rigid
  ; coherent-strengthened-output
  ; strengthen-synth
  )
open import ExprRenamingPreservation using (wk-preserves-value)
open import ExprTypingStripFresh using
  ( strip-value
  ; strip-synth
  ; wk-allUsedCtx
  )
open import ExprTypeRenamingPreservationFresh using
  ( wkTy-preserves-value
  )
import ExprContextProperties as ECP using
  ( AllUsed
  ; AU-∅
  ; AU-used
  ; AU-un
  ; allUsedCtx
  ; allUsedCtx-AllUsed
  ; strip-rm-lin
  )
open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (_⋯_; ⋯-id)

-- Contexts are equivalent when their live linear and unrestricted entries
-- agree exactly, while the annotations stored in already-used entries may
-- differ.  This is option 1 from the preservation discussion.

infix 4 _≈ᵘ_

data _≈ᵘ_ {Δ : List Kind} : ∀ {n} → Ctx Δ n → Ctx Δ n → Set where
  ≈ᵘ-∅ :
    ∅ ≈ᵘ ∅

  ≈ᵘ-lin :
    ∀ {n pk}
      {T : NfTy Δ (KV pk Lin)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ₁ ≈ᵘ Γ₂
    → (B-Lin T ▻ Γ₁) ≈ᵘ (B-Lin T ▻ Γ₂)

  ≈ᵘ-un :
    ∀ {n pk}
      {T : NfTy Δ (KV pk Un)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ₁ ≈ᵘ Γ₂
    → (B-Un T ▻ Γ₁) ≈ᵘ (B-Un T ▻ Γ₂)

  ≈ᵘ-used :
    ∀ {n pk₁ pk₂}
      {T : NfTy Δ (KV pk₁ Lin)}
      {U : NfTy Δ (KV pk₂ Lin)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ₁ ≈ᵘ Γ₂
    → (B-Used T ▻ Γ₁) ≈ᵘ (B-Used U ▻ Γ₂)

≈ᵘ-refl : ∀ {Δ n} {Γ : Ctx Δ n} → Γ ≈ᵘ Γ
≈ᵘ-refl {Γ = ∅} = ≈ᵘ-∅
≈ᵘ-refl {Γ = B-Lin _ ▻ _} = ≈ᵘ-lin ≈ᵘ-refl
≈ᵘ-refl {Γ = B-Un _ ▻ _} = ≈ᵘ-un ≈ᵘ-refl
≈ᵘ-refl {Γ = B-Used _ ▻ _} = ≈ᵘ-used ≈ᵘ-refl

≈ᵘ-sym : ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n} → Γ₁ ≈ᵘ Γ₂ → Γ₂ ≈ᵘ Γ₁
≈ᵘ-sym ≈ᵘ-∅ = ≈ᵘ-∅
≈ᵘ-sym (≈ᵘ-lin eq) = ≈ᵘ-lin (≈ᵘ-sym eq)
≈ᵘ-sym (≈ᵘ-un eq) = ≈ᵘ-un (≈ᵘ-sym eq)
≈ᵘ-sym (≈ᵘ-used eq) = ≈ᵘ-used (≈ᵘ-sym eq)

≈ᵘ-trans :
  ∀ {Δ n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
  → Γ₁ ≈ᵘ Γ₂
  → Γ₂ ≈ᵘ Γ₃
  → Γ₁ ≈ᵘ Γ₃
≈ᵘ-trans ≈ᵘ-∅ ≈ᵘ-∅ = ≈ᵘ-∅
≈ᵘ-trans (≈ᵘ-lin eq₁) (≈ᵘ-lin eq₂) =
  ≈ᵘ-lin (≈ᵘ-trans eq₁ eq₂)
≈ᵘ-trans (≈ᵘ-un eq₁) (≈ᵘ-un eq₂) =
  ≈ᵘ-un (≈ᵘ-trans eq₁ eq₂)
≈ᵘ-trans (≈ᵘ-used eq₁) (≈ᵘ-used eq₂) =
  ≈ᵘ-used (≈ᵘ-trans eq₁ eq₂)

used-head-≈ᵘ :
  ∀ {Δ n pk₁ pk₂}
    {T : NfTy Δ (KV pk₁ Lin)}
    {U : NfTy Δ (KV pk₂ Lin)}
    {Γ : Ctx Δ n}
  → (B-Used T ▻ Γ) ≈ᵘ (B-Used U ▻ Γ)
used-head-≈ᵘ = ≈ᵘ-used ≈ᵘ-refl

-- The public result relation is intentionally coarse.  Replay of an
-- unchanged typing derivation needs the stronger fact that a used annotation
-- may change only when the entry was already used on input.  A live entry
-- consumed by the derivation keeps its original type on both sides.

data RetaggedTransition {Δ : List Kind} :
    ∀ {n}
    → Ctx Δ n
    → Ctx Δ n
    → Ctx Δ n
    → Ctx Δ n
    → Set where
  RT-∅ :
    RetaggedTransition ∅ ∅ ∅ ∅

  RT-lin-live :
    ∀ {n pk}
      {T : NfTy Δ (KV pk Lin)}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
    → RetaggedTransition Γin Γin′ Γout Γout′
    → RetaggedTransition
        (B-Lin T ▻ Γin)
        (B-Lin T ▻ Γin′)
        (B-Lin T ▻ Γout)
        (B-Lin T ▻ Γout′)

  RT-lin-used :
    ∀ {n pk}
      {T : NfTy Δ (KV pk Lin)}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
    → RetaggedTransition Γin Γin′ Γout Γout′
    → RetaggedTransition
        (B-Lin T ▻ Γin)
        (B-Lin T ▻ Γin′)
        (B-Used T ▻ Γout)
        (B-Used T ▻ Γout′)

  RT-un :
    ∀ {n pk}
      {T : NfTy Δ (KV pk Un)}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
    → RetaggedTransition Γin Γin′ Γout Γout′
    → RetaggedTransition
        (B-Un T ▻ Γin)
        (B-Un T ▻ Γin′)
        (B-Un T ▻ Γout)
        (B-Un T ▻ Γout′)

  RT-used :
    ∀ {n pk₁ pk₂}
      {T : NfTy Δ (KV pk₁ Lin)}
      {U : NfTy Δ (KV pk₂ Lin)}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
    → RetaggedTransition Γin Γin′ Γout Γout′
    → RetaggedTransition
        (B-Used T ▻ Γin)
        (B-Used U ▻ Γin′)
        (B-Used T ▻ Γout)
        (B-Used U ▻ Γout′)

retagged-id :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
  → Γ₁ ≈ᵘ Γ₂
  → RetaggedTransition Γ₁ Γ₂ Γ₁ Γ₂
retagged-id ≈ᵘ-∅ = RT-∅
retagged-id (≈ᵘ-lin eq) = RT-lin-live (retagged-id eq)
retagged-id (≈ᵘ-un eq) = RT-un (retagged-id eq)
retagged-id (≈ᵘ-used eq) = RT-used (retagged-id eq)

retagged-input :
  ∀ {Δ n} {Γin Γin′ Γout Γout′ : Ctx Δ n}
  → RetaggedTransition Γin Γin′ Γout Γout′
  → Γin ≈ᵘ Γin′
retagged-input RT-∅ = ≈ᵘ-∅
retagged-input (RT-lin-live tr) = ≈ᵘ-lin (retagged-input tr)
retagged-input (RT-lin-used tr) = ≈ᵘ-lin (retagged-input tr)
retagged-input (RT-un tr) = ≈ᵘ-un (retagged-input tr)
retagged-input (RT-used tr) = ≈ᵘ-used (retagged-input tr)

retagged-output :
  ∀ {Δ n} {Γin Γin′ Γout Γout′ : Ctx Δ n}
  → RetaggedTransition Γin Γin′ Γout Γout′
  → Γout ≈ᵘ Γout′
retagged-output RT-∅ = ≈ᵘ-∅
retagged-output (RT-lin-live tr) = ≈ᵘ-lin (retagged-output tr)
retagged-output (RT-lin-used tr) = ≈ᵘ-used (retagged-output tr)
retagged-output (RT-un tr) = ≈ᵘ-un (retagged-output tr)
retagged-output (RT-used tr) = ≈ᵘ-used (retagged-output tr)

retagged-target-unique :
  ∀ {Δ n}
    {Γin Γin′ Γout Γout₁′ Γout₂′ : Ctx Δ n}
  → RetaggedTransition Γin Γin′ Γout Γout₁′
  → RetaggedTransition Γin Γin′ Γout Γout₂′
  → Γout₁′ ≡ Γout₂′
retagged-target-unique RT-∅ RT-∅ = refl
retagged-target-unique (RT-lin-live tr₁) (RT-lin-live tr₂) =
  cong (B-Lin _ ▻_) (retagged-target-unique tr₁ tr₂)
retagged-target-unique (RT-lin-used tr₁) (RT-lin-used tr₂) =
  cong (B-Used _ ▻_) (retagged-target-unique tr₁ tr₂)
retagged-target-unique (RT-un tr₁) (RT-un tr₂) =
  cong (B-Un _ ▻_) (retagged-target-unique tr₁ tr₂)
retagged-target-unique (RT-used tr₁) (RT-used tr₂) =
  cong (B-Used _ ▻_) (retagged-target-unique tr₁ tr₂)

retagged-stable-output :
  ∀ {Δ n}
    {Γin Γin′ Γout′ : Ctx Δ n}
  → RetaggedTransition Γin Γin′ Γin Γout′
  → Γout′ ≡ Γin′
retagged-stable-output RT-∅ = refl
retagged-stable-output (RT-lin-live tr) =
  cong (B-Lin _ ▻_) (retagged-stable-output tr)
retagged-stable-output (RT-un tr) =
  cong (B-Un _ ▻_) (retagged-stable-output tr)
retagged-stable-output (RT-used tr) =
  cong (B-Used _ ▻_) (retagged-stable-output tr)

wk-retagged :
  ∀ {Δ n K}
    {Γin Γin′ Γout Γout′ : Ctx Δ n}
  → RetaggedTransition Γin Γin′ Γout Γout′
  → RetaggedTransition
      (wkCtx {K = K} Γin)
      (wkCtx Γin′)
      (wkCtx Γout)
      (wkCtx Γout′)
wk-retagged RT-∅ = RT-∅
wk-retagged (RT-lin-live tr) = RT-lin-live (wk-retagged tr)
wk-retagged (RT-lin-used tr) = RT-lin-used (wk-retagged tr)
wk-retagged (RT-un tr) = RT-un (wk-retagged tr)
wk-retagged (RT-used tr) = RT-used (wk-retagged tr)

split-retagged :
  ∀ {Δ n}
    {Γ₁ Γ₁′ Γ₂ Γ₃ Γ₃′ : Ctx Δ n}
  → RetaggedTransition Γ₁ Γ₁′ Γ₃ Γ₃′
  → Γ₁ ~Ctx Γ₂
  → Γ₂ ~Ctx Γ₃
  → Σ (Ctx Δ n) λ Γ₂′ →
      RetaggedTransition Γ₁ Γ₁′ Γ₂ Γ₂′
      × RetaggedTransition Γ₂ Γ₂′ Γ₃ Γ₃′
split-retagged RT-∅ ∅~∅ ∅~∅ =
  ∅ , RT-∅ , RT-∅
split-retagged (RT-lin-live tr) (Lin~Lin s₁) (Lin~Lin s₂)
  with split-retagged tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RT-lin-live tr₁ , RT-lin-live tr₂
split-retagged (RT-lin-used tr) (Lin~Lin s₁) (Lin~Used s₂)
  with split-retagged tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RT-lin-live tr₁ , RT-lin-used tr₂
split-retagged (RT-lin-used tr) (Lin~Used s₁) (Used~Used s₂)
  with split-retagged tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RT-lin-used tr₁ , RT-used tr₂
split-retagged (RT-un tr) (Un~Un s₁) (Un~Un s₂)
  with split-retagged tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RT-un tr₁ , RT-un tr₂
split-retagged (RT-used tr) (Used~Used s₁) (Used~Used s₂)
  with split-retagged tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RT-used tr₁ , RT-used tr₂

retagged-from-shape :
  ∀ {Δ n}
    {Γin Γin′ Γout : Ctx Δ n}
  → Γin ≈ᵘ Γin′
  → Γin ~Ctx Γout
  → Σ (Ctx Δ n) λ Γout′ →
      RetaggedTransition Γin Γin′ Γout Γout′
retagged-from-shape ≈ᵘ-∅ ∅~∅ =
  ∅ , RT-∅
retagged-from-shape (≈ᵘ-lin eq) (Lin~Lin shape)
  with retagged-from-shape eq shape
... | Γout′ , tr =
  _ , RT-lin-live tr
retagged-from-shape (≈ᵘ-lin eq) (Lin~Used shape)
  with retagged-from-shape eq shape
... | Γout′ , tr =
  _ , RT-lin-used tr
retagged-from-shape (≈ᵘ-un eq) (Un~Un shape)
  with retagged-from-shape eq shape
... | Γout′ , tr =
  _ , RT-un tr
retagged-from-shape (≈ᵘ-used eq) (Used~Used shape)
  with retagged-from-shape eq shape
... | Γout′ , tr =
  _ , RT-used tr

allUsed-resp-≈ᵘ :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
  → Γ₁ ≈ᵘ Γ₂
  → ECP.AllUsed Γ₁
  → ECP.AllUsed Γ₂
allUsed-resp-≈ᵘ ≈ᵘ-∅ ECP.AU-∅ = ECP.AU-∅
allUsed-resp-≈ᵘ (≈ᵘ-un eq) (ECP.AU-un au) =
  ECP.AU-un (allUsed-resp-≈ᵘ eq au)
allUsed-resp-≈ᵘ (≈ᵘ-used eq) (ECP.AU-used au) =
  ECP.AU-used (allUsed-resp-≈ᵘ eq au)

retag-∋ˡ :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
  → Γ₁ ≈ᵘ Γ₂
  → Γ₁ ∋ˡ x ∶ T
  → Γ₂ ∋ˡ x ∶ T
retag-∋ˡ (≈ᵘ-lin eq) hereˡ = hereˡ
retag-∋ˡ (≈ᵘ-lin eq) (thereˡˡ x∈) =
  thereˡˡ (retag-∋ˡ eq x∈)
retag-∋ˡ (≈ᵘ-un eq) (thereˡᵘ x∈) =
  thereˡᵘ (retag-∋ˡ eq x∈)
retag-∋ˡ (≈ᵘ-used eq) (thereˡ✖ x∈) =
  thereˡ✖ (retag-∋ˡ eq x∈)

retag-∋ᵘ :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Un)}
  → Γ₁ ≈ᵘ Γ₂
  → Γ₁ ∋ᵘ x ∶ T
  → Γ₂ ∋ᵘ x ∶ T
retag-∋ᵘ (≈ᵘ-lin eq) (thereᵘˡ x∈) =
  thereᵘˡ (retag-∋ᵘ eq x∈)
retag-∋ᵘ (≈ᵘ-un eq) hereᵘ = hereᵘ
retag-∋ᵘ (≈ᵘ-un eq) (thereᵘᵘ x∈) =
  thereᵘᵘ (retag-∋ᵘ eq x∈)
retag-∋ᵘ (≈ᵘ-used eq) (thereᵘ✖ x∈) =
  thereᵘ✖ (retag-∋ᵘ eq x∈)

retag-take-transition :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ Γ₁′ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
  → Γ₁ ≈ᵘ Γ₂
  → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₁′
  → Σ (Ctx Δ n) λ Γ₂′ →
      (Γ₂ ⊢ˡ x ∶ T ⊣ Γ₂′)
      × RetaggedTransition Γ₁ Γ₂ Γ₁′ Γ₂′
retag-take-transition (≈ᵘ-lin eq) take-here =
  _ , take-here , RT-lin-used (retagged-id eq)
retag-take-transition (≈ᵘ-lin eq) (take-thereˡ take)
  with retag-take-transition eq take
... | Γ₂′ , take′ , transition =
  _ , take-thereˡ take′ , RT-lin-live transition
retag-take-transition (≈ᵘ-un eq) (take-thereᵘ take)
  with retag-take-transition eq take
... | Γ₂′ , take′ , transition =
  _ , take-thereᵘ take′ , RT-un transition
retag-take-transition (≈ᵘ-used eq) (take-there✖ take)
  with retag-take-transition eq take
... | Γ₂′ , take′ , transition =
  _ , take-there✖ take′ , RT-used transition

retag-take :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ Γ₁′ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
  → Γ₁ ≈ᵘ Γ₂
  → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₁′
  → Σ (Ctx Δ n) λ Γ₂′ →
      (Γ₂ ⊢ˡ x ∶ T ⊣ Γ₂′) × (Γ₁′ ≈ᵘ Γ₂′)
retag-take eq take
  with retag-take-transition eq take
... | Γ₂′ , take′ , transition =
  Γ₂′ , take′ , retagged-output transition

retag-linear-variable :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ Γ₁′ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
  → Γ₁ ≈ᵘ Γ₂
  → Γ₁ ⊢ᵥ V-Var x ⇒ T ⊣ Γ₁′
  → Σ (Ctx Δ n) λ Γ₂′ →
      (Γ₂ ⊢ᵥ V-Var x ⇒ T ⊣ Γ₂′) × (Γ₁′ ≈ᵘ Γ₂′)
retag-linear-variable eq (TV-Var-Lin take)
  with retag-take eq take
... | Γ₂′ , take′ , out-eq =
  Γ₂′ , TV-Var-Lin take′ , out-eq

retag-unrestricted-variable :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Un)}
  → Γ₁ ≈ᵘ Γ₂
  → Γ₁ ⊢ᵥ V-Var x ⇒ T ⊣ Γ₁
  → Γ₂ ⊢ᵥ V-Var x ⇒ T ⊣ Γ₂
retag-unrestricted-variable eq (TV-Var-Un x∈) =
  TV-Var-Un (retag-∋ᵘ eq x∈)

mutual

  retag-value :
    ∀ {Δ n pk m}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
      {v : Value Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γin ⊢ᵥ v ⇒ T ⊣ Γout
    → RetaggedTransition Γin Γin′ Γout Γout′
    → Γin′ ⊢ᵥ v ⇒ T ⊣ Γout′
  retag-value (TV-Const cT) tr
    rewrite retagged-stable-output tr =
    TV-Const cT
  retag-value (TV-Var-Lin take) tr
    with retag-take-transition (retagged-input tr) take
  ... | Γout″ , take′ , tr′
    rewrite retagged-target-unique tr tr′ =
    TV-Var-Lin take′
  retag-value (TV-Var-Un x∈) tr
    rewrite retagged-stable-output tr =
    TV-Var-Un (retag-∋ᵘ (retagged-input tr) x∈)
  retag-value (TV-Abs d) tr =
    TV-Abs (retag-synth d (RT-lin-used tr))
  retag-value (TV-Rec d) tr
    rewrite retagged-stable-output tr =
    TV-Rec
      (retag-check d
        (RT-un (retagged-id (retagged-input tr))))
  retag-value (TV-TAbs d) tr =
    TV-TAbs (retag-value d (wk-retagged tr))
  retag-value (TV-Pair d₁ d₂) tr
    with split-retagged
      tr
      (value-preserves-~Ctx d₁)
      (value-preserves-~Ctx d₂)
  ... | Γmid′ , tr₁ , tr₂ =
    TV-Pair
      (retag-value d₁ tr₁)
      (retag-value d₂ tr₂)
  retag-value TV-Receive₁ tr
    rewrite retagged-stable-output tr =
    TV-Receive₁
  retag-value TV-Receive₂ tr
    rewrite retagged-stable-output tr =
    TV-Receive₂
  retag-value TV-Send₁ tr
    rewrite retagged-stable-output tr =
    TV-Send₁
  retag-value TV-Send₂ tr
    rewrite retagged-stable-output tr =
    TV-Send₂
  retag-value TV-Select₁ tr
    rewrite retagged-stable-output tr =
    TV-Select₁
  retag-value TV-Select₂ tr
    rewrite retagged-stable-output tr =
    TV-Select₂

  retag-synth :
    ∀ {Δ n pk m}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γin ⊢ e ⇒ T ⊣ Γout
    → RetaggedTransition Γin Γin′ Γout Γout′
    → Γin′ ⊢ e ⇒ T ⊣ Γout′
  retag-synth (T-Val d) tr =
    T-Val (retag-value d tr)
  retag-synth (T-Pair d₁ d₂) tr
    with split-retagged
      tr
      (synth-preserves-~Ctx d₁)
      (synth-preserves-~Ctx d₂)
  ... | Γmid′ , tr₁ , tr₂ =
    T-Pair
      (retag-synth d₁ tr₁)
      (retag-synth d₂ tr₂)
  retag-synth (T-App d₁ d₂) tr
    with split-retagged
      tr
      (synth-preserves-~Ctx d₁)
      (check-preserves-~Ctx d₂)
  ... | Γmid′ , tr₁ , tr₂ =
    T-App
      (retag-synth d₁ tr₁)
      (retag-check d₂ tr₂)
  retag-synth (T-LetUnit d₁ d₂) tr
    with split-retagged
      tr
      (check-preserves-~Ctx d₁)
      (synth-preserves-~Ctx d₂)
  ... | Γmid′ , tr₁ , tr₂ =
    T-LetUnit
      (retag-check d₁ tr₁)
      (retag-synth d₂ tr₂)
  retag-synth (T-LetPair d₁ d₂) tr
    with split-retagged
      tr
      (synth-preserves-~Ctx d₁)
      (drop-lin-used (drop-lin-used (synth-preserves-~Ctx d₂)))
  ... | Γmid′ , tr₁ , tr₂ =
    T-LetPair
      (retag-synth d₁ tr₁)
      (retag-synth d₂ (RT-lin-used (RT-lin-used tr₂)))
  retag-synth (T-Match {ss = ss} {incl = incl} {ne = ne} d bs j) tr
    with split-retagged
      tr
      (synth-preserves-~Ctx d)
      (drop-lin-used
        (synth-preserves-~Ctx (bs (proj₁ ne) (proj₂ ne))))
  ... | Γmid′ , tr₁ , tr₂ =
    T-Match {ss = ss} {incl = incl}
      (retag-synth d tr₁)
      (λ i i∈ → retag-synth (bs i i∈) (RT-lin-used tr₂))
      j
  retag-synth (T-TApp d) tr =
    T-TApp (retag-synth d tr)

  retag-check :
    ∀ {Δ n pk m}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γin ⊢ e ⇐ T ⊣ Γout
    → RetaggedTransition Γin Γin′ Γout Γout′
    → Γin′ ⊢ e ⇐ T ⊣ Γout′
  retag-check (T-Check d sub) tr =
    T-Check (retag-synth d tr) sub

retag-value-input :
  ∀ {Δ n pk m}
    {Γin Γin′ Γout : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
  → Γin ⊢ᵥ v ⇒ T ⊣ Γout
  → Γin ≈ᵘ Γin′
  → Σ (Ctx Δ n) λ Γout′ →
      (Γin′ ⊢ᵥ v ⇒ T ⊣ Γout′)
      × (Γout′ ≈ᵘ Γout)
retag-value-input d eq
  with retagged-from-shape eq (value-preserves-~Ctx d)
... | Γout′ , tr =
  Γout′ , retag-value d tr , ≈ᵘ-sym (retagged-output tr)

retag-synth-input :
  ∀ {Δ n pk m}
    {Γin Γin′ Γout : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk m)}
  → Γin ⊢ e ⇒ T ⊣ Γout
  → Γin ≈ᵘ Γin′
  → Σ (Ctx Δ n) λ Γout′ →
      (Γin′ ⊢ e ⇒ T ⊣ Γout′)
      × (Γout′ ≈ᵘ Γout)
retag-synth-input d eq
  with retagged-from-shape eq (synth-preserves-~Ctx d)
... | Γout′ , tr =
  Γout′ , retag-synth d tr , ≈ᵘ-sym (retagged-output tr)

retag-synth-input-lin-used :
  ∀ {Δ n pkᵀ pkᵁ mᵁ}
    {Γin Γin′ Γout : Ctx Δ n}
    {T : NfTy Δ (KV pkᵀ Lin)}
    {U : NfTy Δ (KV pkᵁ mᵁ)}
    {e : Expr Δ (Data.Nat.suc n)}
  → (T ∷ˡ Γin) ⊢ e ⇒ U ⊣ (B-Used T ▻ Γout)
  → Γin ≈ᵘ Γin′
  → Σ (Ctx Δ n) λ Γout′ →
      ((T ∷ˡ Γin′) ⊢ e ⇒ U ⊣ (B-Used T ▻ Γout′))
      × (Γout′ ≈ᵘ Γout)
retag-synth-input-lin-used d eq
  with retagged-from-shape
         (≈ᵘ-lin eq)
         (synth-preserves-~Ctx d)
... | B-Used _ ▻ Γout′ , RT-lin-used tr =
  Γout′
  , retag-synth d (RT-lin-used tr)
  , ≈ᵘ-sym (retagged-output tr)

retag-synth-input-two-lin-used :
  ∀ {Δ n pkT pkU pkV mV}
    {Γin Γin′ Γout : Ctx Δ n}
    {T : NfTy Δ (KV pkT Lin)}
    {U : NfTy Δ (KV pkU Lin)}
    {V : NfTy Δ (KV pkV mV)}
    {e : Expr Δ (Data.Nat.suc (Data.Nat.suc n))}
  → (T ∷ˡ (U ∷ˡ Γin)) ⊢ e ⇒ V
      ⊣ (B-Used T ▻ (B-Used U ▻ Γout))
  → Γin ≈ᵘ Γin′
  → Σ (Ctx Δ n) λ Γout′ →
      ((T ∷ˡ (U ∷ˡ Γin′)) ⊢ e ⇒ V
        ⊣ (B-Used T ▻ (B-Used U ▻ Γout′)))
      × (Γout′ ≈ᵘ Γout)
retag-synth-input-two-lin-used d eq
  with retagged-from-shape
         (≈ᵘ-lin (≈ᵘ-lin eq))
         (synth-preserves-~Ctx d)
... | B-Used _ ▻ (B-Used _ ▻ Γout′) ,
      RT-lin-used (RT-lin-used tr) =
  Γout′
  , retag-synth d (RT-lin-used (RT-lin-used tr))
  , ≈ᵘ-sym (retagged-output tr)

retag-check-input :
  ∀ {Δ n pk m}
    {Γin Γin′ Γout : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk m)}
  → Γin ⊢ e ⇐ T ⊣ Γout
  → Γin ≈ᵘ Γin′
  → Σ (Ctx Δ n) λ Γout′ →
      (Γin′ ⊢ e ⇐ T ⊣ Γout′)
      × (Γout′ ≈ᵘ Γout)
retag-check-input d eq
  with retagged-from-shape eq (check-preserves-~Ctx d)
... | Γout′ , tr =
  Γout′ , retag-check d tr , ≈ᵘ-sym (retagged-output tr)

-- A derivation may also be replayed after some resources that it did not use
-- have already been consumed.  `ReplayTransition` records exactly that
-- situation.  In particular, `RP-lin-masked` changes an unused live entry in
-- the old run into an already-used entry in the new run.

data ReplayTransition {Δ : List Kind} :
    ∀ {n}
    → Ctx Δ n
    → Ctx Δ n
    → Ctx Δ n
    → Ctx Δ n
    → Set where
  RP-∅ :
    ReplayTransition ∅ ∅ ∅ ∅

  RP-lin-live :
    ∀ {n pk}
      {T : NfTy Δ (KV pk Lin)}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
    → ReplayTransition Γin Γin′ Γout Γout′
    → ReplayTransition
        (B-Lin T ▻ Γin)
        (B-Lin T ▻ Γin′)
        (B-Lin T ▻ Γout)
        (B-Lin T ▻ Γout′)

  RP-lin-masked :
    ∀ {n pk₁ pk₂}
      {T : NfTy Δ (KV pk₁ Lin)}
      {U : NfTy Δ (KV pk₂ Lin)}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
    → ReplayTransition Γin Γin′ Γout Γout′
    → ReplayTransition
        (B-Lin T ▻ Γin)
        (B-Used U ▻ Γin′)
        (B-Lin T ▻ Γout)
        (B-Used U ▻ Γout′)

  RP-lin-used :
    ∀ {n pk}
      {T : NfTy Δ (KV pk Lin)}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
    → ReplayTransition Γin Γin′ Γout Γout′
    → ReplayTransition
        (B-Lin T ▻ Γin)
        (B-Lin T ▻ Γin′)
        (B-Used T ▻ Γout)
        (B-Used T ▻ Γout′)

  RP-un :
    ∀ {n pk}
      {T : NfTy Δ (KV pk Un)}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
    → ReplayTransition Γin Γin′ Γout Γout′
    → ReplayTransition
        (B-Un T ▻ Γin)
        (B-Un T ▻ Γin′)
        (B-Un T ▻ Γout)
        (B-Un T ▻ Γout′)

  RP-used :
    ∀ {n pk₁ pk₂}
      {T : NfTy Δ (KV pk₁ Lin)}
      {U : NfTy Δ (KV pk₂ Lin)}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
    → ReplayTransition Γin Γin′ Γout Γout′
    → ReplayTransition
        (B-Used T ▻ Γin)
        (B-Used U ▻ Γin′)
        (B-Used T ▻ Γout)
        (B-Used U ▻ Γout′)

  RP-used-live :
    ∀ {n pk₁ pk₂}
      {T : NfTy Δ (KV pk₁ Lin)}
      {U : NfTy Δ (KV pk₂ Lin)}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
    → ReplayTransition Γin Γin′ Γout Γout′
    → ReplayTransition
        (B-Used T ▻ Γin)
        (B-Lin U ▻ Γin′)
        (B-Used T ▻ Γout)
        (B-Lin U ▻ Γout′)

replay-input-id :
  ∀ {Δ n} {Γin Γin′ Γout Γout′ : Ctx Δ n}
  → ReplayTransition Γin Γin′ Γout Γout′
  → ReplayTransition Γin Γin′ Γin Γin′
replay-input-id RP-∅ = RP-∅
replay-input-id (RP-lin-live tr) =
  RP-lin-live (replay-input-id tr)
replay-input-id (RP-lin-masked tr) =
  RP-lin-masked (replay-input-id tr)
replay-input-id (RP-lin-used tr) =
  RP-lin-live (replay-input-id tr)
replay-input-id (RP-un tr) =
  RP-un (replay-input-id tr)
replay-input-id (RP-used tr) =
  RP-used (replay-input-id tr)
replay-input-id (RP-used-live tr) =
  RP-used-live (replay-input-id tr)

replay-stable-output :
  ∀ {Δ n} {Γin Γin′ Γout′ : Ctx Δ n}
  → ReplayTransition Γin Γin′ Γin Γout′
  → Γout′ ≡ Γin′
replay-stable-output RP-∅ = refl
replay-stable-output (RP-lin-live tr) =
  cong (B-Lin _ ▻_) (replay-stable-output tr)
replay-stable-output (RP-lin-masked tr) =
  cong (B-Used _ ▻_) (replay-stable-output tr)
replay-stable-output (RP-un tr) =
  cong (B-Un _ ▻_) (replay-stable-output tr)
replay-stable-output (RP-used tr) =
  cong (B-Used _ ▻_) (replay-stable-output tr)
replay-stable-output (RP-used-live tr) =
  cong (B-Lin _ ▻_) (replay-stable-output tr)

wk-replay :
  ∀ {Δ n K}
    {Γin Γin′ Γout Γout′ : Ctx Δ n}
  → ReplayTransition Γin Γin′ Γout Γout′
  → ReplayTransition
      (wkCtx {K = K} Γin)
      (wkCtx Γin′)
      (wkCtx Γout)
      (wkCtx Γout′)
wk-replay RP-∅ = RP-∅
wk-replay (RP-lin-live tr) = RP-lin-live (wk-replay tr)
wk-replay (RP-lin-masked tr) = RP-lin-masked (wk-replay tr)
wk-replay (RP-lin-used tr) = RP-lin-used (wk-replay tr)
wk-replay (RP-un tr) = RP-un (wk-replay tr)
wk-replay (RP-used tr) = RP-used (wk-replay tr)
wk-replay (RP-used-live tr) = RP-used-live (wk-replay tr)

split-replay :
  ∀ {Δ n}
    {Γ₁ Γ₁′ Γ₂ Γ₃ Γ₃′ : Ctx Δ n}
  → ReplayTransition Γ₁ Γ₁′ Γ₃ Γ₃′
  → Γ₁ ~Ctx Γ₂
  → Γ₂ ~Ctx Γ₃
  → Σ (Ctx Δ n) λ Γ₂′ →
      ReplayTransition Γ₁ Γ₁′ Γ₂ Γ₂′
      × ReplayTransition Γ₂ Γ₂′ Γ₃ Γ₃′
split-replay RP-∅ ∅~∅ ∅~∅ =
  ∅ , RP-∅ , RP-∅
split-replay (RP-lin-live tr) (Lin~Lin s₁) (Lin~Lin s₂)
  with split-replay tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RP-lin-live tr₁ , RP-lin-live tr₂
split-replay (RP-lin-masked tr) (Lin~Lin s₁) (Lin~Lin s₂)
  with split-replay tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RP-lin-masked tr₁ , RP-lin-masked tr₂
split-replay (RP-lin-used tr) (Lin~Lin s₁) (Lin~Used s₂)
  with split-replay tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RP-lin-live tr₁ , RP-lin-used tr₂
split-replay (RP-lin-used tr) (Lin~Used s₁) (Used~Used s₂)
  with split-replay tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RP-lin-used tr₁ , RP-used tr₂
split-replay (RP-un tr) (Un~Un s₁) (Un~Un s₂)
  with split-replay tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RP-un tr₁ , RP-un tr₂
split-replay (RP-used tr) (Used~Used s₁) (Used~Used s₂)
  with split-replay tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RP-used tr₁ , RP-used tr₂
split-replay (RP-used-live tr) (Used~Used s₁) (Used~Used s₂)
  with split-replay tr s₁ s₂
... | Γ₂′ , tr₁ , tr₂ =
  _ , RP-used-live tr₁ , RP-used-live tr₂

replay-take :
  ∀ {Δ n pk}
    {Γin Γin′ Γout Γout′ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
  → Γin ⊢ˡ x ∶ T ⊣ Γout
  → ReplayTransition Γin Γin′ Γout Γout′
  → Γin′ ⊢ˡ x ∶ T ⊣ Γout′
replay-take take-here (RP-lin-used tr)
  rewrite replay-stable-output tr =
  take-here
replay-take (take-thereˡ take) (RP-lin-live tr) =
  take-thereˡ (replay-take take tr)
replay-take (take-thereˡ take) (RP-lin-masked tr) =
  take-there✖ (replay-take take tr)
replay-take (take-thereᵘ take) (RP-un tr) =
  take-thereᵘ (replay-take take tr)
replay-take (take-there✖ take) (RP-used tr) =
  take-there✖ (replay-take take tr)
replay-take (take-there✖ take) (RP-used-live tr) =
  take-thereˡ (replay-take take tr)

replay-∋ᵘ :
  ∀ {Δ n pk}
    {Γin Γin′ Γout Γout′ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Un)}
  → Γin ∋ᵘ x ∶ T
  → ReplayTransition Γin Γin′ Γout Γout′
  → Γin′ ∋ᵘ x ∶ T
replay-∋ᵘ (thereᵘˡ x∈) (RP-lin-live tr) =
  thereᵘˡ (replay-∋ᵘ x∈ tr)
replay-∋ᵘ (thereᵘˡ x∈) (RP-lin-masked tr) =
  thereᵘ✖ (replay-∋ᵘ x∈ tr)
replay-∋ᵘ (thereᵘˡ x∈) (RP-lin-used tr) =
  thereᵘˡ (replay-∋ᵘ x∈ tr)
replay-∋ᵘ hereᵘ (RP-un tr) = hereᵘ
replay-∋ᵘ (thereᵘᵘ x∈) (RP-un tr) =
  thereᵘᵘ (replay-∋ᵘ x∈ tr)
replay-∋ᵘ (thereᵘ✖ x∈) (RP-used tr) =
  thereᵘ✖ (replay-∋ᵘ x∈ tr)
replay-∋ᵘ (thereᵘ✖ x∈) (RP-used-live tr) =
  thereᵘˡ (replay-∋ᵘ x∈ tr)

mutual

  replay-transition-value :
    ∀ {Δ n pk m}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
      {v : Value Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γin ⊢ᵥ v ⇒ T ⊣ Γout
    → ReplayTransition Γin Γin′ Γout Γout′
    → Γin′ ⊢ᵥ v ⇒ T ⊣ Γout′
  replay-transition-value (TV-Const cT) tr
    rewrite replay-stable-output tr =
    TV-Const cT
  replay-transition-value (TV-Var-Lin take) tr =
    TV-Var-Lin (replay-take take tr)
  replay-transition-value (TV-Var-Un x∈) tr
    rewrite replay-stable-output tr =
    TV-Var-Un (replay-∋ᵘ x∈ tr)
  replay-transition-value (TV-Abs d) tr =
    TV-Abs (replay-transition-synth d (RP-lin-used tr))
  replay-transition-value (TV-Rec d) tr
    rewrite replay-stable-output tr =
    TV-Rec
      (replay-transition-check d
        (RP-un (replay-input-id tr)))
  replay-transition-value (TV-TAbs d) tr =
    TV-TAbs (replay-transition-value d (wk-replay tr))
  replay-transition-value (TV-Pair d₁ d₂) tr
    with split-replay
      tr
      (value-preserves-~Ctx d₁)
      (value-preserves-~Ctx d₂)
  ... | Γmid′ , tr₁ , tr₂ =
    TV-Pair
      (replay-transition-value d₁ tr₁)
      (replay-transition-value d₂ tr₂)
  replay-transition-value TV-Receive₁ tr
    rewrite replay-stable-output tr =
    TV-Receive₁
  replay-transition-value TV-Receive₂ tr
    rewrite replay-stable-output tr =
    TV-Receive₂
  replay-transition-value TV-Send₁ tr
    rewrite replay-stable-output tr =
    TV-Send₁
  replay-transition-value TV-Send₂ tr
    rewrite replay-stable-output tr =
    TV-Send₂
  replay-transition-value TV-Select₁ tr
    rewrite replay-stable-output tr =
    TV-Select₁
  replay-transition-value TV-Select₂ tr
    rewrite replay-stable-output tr =
    TV-Select₂

  replay-transition-synth :
    ∀ {Δ n pk m}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γin ⊢ e ⇒ T ⊣ Γout
    → ReplayTransition Γin Γin′ Γout Γout′
    → Γin′ ⊢ e ⇒ T ⊣ Γout′
  replay-transition-synth (T-Val d) tr =
    T-Val (replay-transition-value d tr)
  replay-transition-synth (T-Pair d₁ d₂) tr
    with split-replay
      tr
      (synth-preserves-~Ctx d₁)
      (synth-preserves-~Ctx d₂)
  ... | Γmid′ , tr₁ , tr₂ =
    T-Pair
      (replay-transition-synth d₁ tr₁)
      (replay-transition-synth d₂ tr₂)
  replay-transition-synth (T-App d₁ d₂) tr
    with split-replay
      tr
      (synth-preserves-~Ctx d₁)
      (check-preserves-~Ctx d₂)
  ... | Γmid′ , tr₁ , tr₂ =
    T-App
      (replay-transition-synth d₁ tr₁)
      (replay-transition-check d₂ tr₂)
  replay-transition-synth (T-LetUnit d₁ d₂) tr
    with split-replay
      tr
      (check-preserves-~Ctx d₁)
      (synth-preserves-~Ctx d₂)
  ... | Γmid′ , tr₁ , tr₂ =
    T-LetUnit
      (replay-transition-check d₁ tr₁)
      (replay-transition-synth d₂ tr₂)
  replay-transition-synth (T-LetPair d₁ d₂) tr
    with split-replay
      tr
      (synth-preserves-~Ctx d₁)
      (drop-lin-used (drop-lin-used (synth-preserves-~Ctx d₂)))
  ... | Γmid′ , tr₁ , tr₂ =
    T-LetPair
      (replay-transition-synth d₁ tr₁)
      (replay-transition-synth d₂
        (RP-lin-used (RP-lin-used tr₂)))
  replay-transition-synth
      (T-Match {ss = ss} {incl = incl} {ne = ne} d bs j) tr
    with split-replay
      tr
      (synth-preserves-~Ctx d)
      (drop-lin-used
        (synth-preserves-~Ctx (bs (proj₁ ne) (proj₂ ne))))
  ... | Γmid′ , tr₁ , tr₂ =
    T-Match {ss = ss} {incl = incl}
      (replay-transition-synth d tr₁)
      (λ i i∈ →
        replay-transition-synth (bs i i∈) (RP-lin-used tr₂))
      j
  replay-transition-synth (T-TApp d) tr =
    T-TApp (replay-transition-synth d tr)

  replay-transition-check :
    ∀ {Δ n pk m}
      {Γin Γin′ Γout Γout′ : Ctx Δ n}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γin ⊢ e ⇐ T ⊣ Γout
    → ReplayTransition Γin Γin′ Γout Γout′
    → Γin′ ⊢ e ⇐ T ⊣ Γout′
  replay-transition-check (T-Check d sub) tr =
    T-Check (replay-transition-synth d tr) sub

remove-to-frame :
  ∀ {Δ n} {Γin G Γout : Ctx Δ n}
  → RemoveCtx Γin G Γout
  → FrameCtx G Γout Γin
remove-to-frame RM-∅ = FC-∅
remove-to-frame (RM-drop r) = FC-live (remove-to-frame r)
remove-to-frame (RM-allused r) = FC-allused (remove-to-frame r)
remove-to-frame (RM-lin r) = FC-frame (remove-to-frame r)
remove-to-frame (RM-un r) = FC-un (remove-to-frame r)

remove-frame-replay :
  ∀ {Δ n}
    {Γin G Γout Γfinal Γswap : Ctx Δ n}
  → RemoveCtx Γin G Γout
  → FrameCtx G Γfinal Γswap
  → ReplayTransition Γin Γswap Γout Γfinal
remove-frame-replay RM-∅ FC-∅ = RP-∅
remove-frame-replay (RM-drop r) (FC-live f) =
  RP-lin-live (remove-frame-replay r f)
remove-frame-replay (RM-drop r) (FC-allused f) =
  RP-lin-masked (remove-frame-replay r f)
remove-frame-replay (RM-allused r) (FC-allused f) =
  RP-used (remove-frame-replay r f)
remove-frame-replay (RM-allused r) (FC-live f) =
  RP-used-live (remove-frame-replay r f)
remove-frame-replay (RM-lin r) (FC-frame f) =
  RP-lin-used (remove-frame-replay r f)
remove-frame-replay (RM-un r) (FC-un f) =
  RP-un (remove-frame-replay r f)

exchange-value-after-value :
  ∀ {Δ n pk₁ pk₂ m₁ m₂}
    {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
    {v₁ v₂ : Value Δ n}
    {T : NfTy Δ (KV pk₁ m₁)}
    {U : NfTy Δ (KV pk₂ m₂)}
  → Γ₁ ⊢ᵥ v₁ ⇒ T ⊣ Γ₂
  → Γ₂ ⊢ᵥ v₂ ⇒ U ⊣ Γ₃
  → Σ (Ctx Δ n) λ Γ₂′ →
      (Γ₁ ⊢ᵥ v₂ ⇒ U ⊣ Γ₂′)
      × (Γ₂′ ⊢ᵥ v₁ ⇒ T ⊣ Γ₃)
exchange-value-after-value d₁ d₂
  with leftover-value d₁
... | G , r
  with frame-value d₂ (remove-to-frame r)
... | Γ₂′ , f , d₂′ =
  Γ₂′ , d₂′ ,
  replay-transition-value d₁ (remove-frame-replay r f)

exchange-value-after-synth :
  ∀ {Δ n pk₁ pk₂ m₁ m₂}
    {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
    {e : Expr Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk₁ m₁)}
    {U : NfTy Δ (KV pk₂ m₂)}
  → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
  → Γ₂ ⊢ᵥ v ⇒ U ⊣ Γ₃
  → Σ (Ctx Δ n) λ Γ₂′ →
      (Γ₁ ⊢ᵥ v ⇒ U ⊣ Γ₂′)
      × (Γ₂′ ⊢ e ⇒ T ⊣ Γ₃)
exchange-value-after-synth d₁ d₂
  with leftover-synth d₁
... | G , r
  with frame-value d₂ (remove-to-frame r)
... | Γ₂′ , f , d₂′ =
  Γ₂′ , d₂′ ,
  replay-transition-synth d₁ (remove-frame-replay r f)

exchange-check-after-synth :
  ∀ {Δ n pk₁ pk₂ m₁ m₂}
    {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
    {e₁ e₂ : Expr Δ n}
    {T : NfTy Δ (KV pk₁ m₁)}
    {U : NfTy Δ (KV pk₂ m₂)}
  → Γ₁ ⊢ e₁ ⇒ T ⊣ Γ₂
  → Γ₂ ⊢ e₂ ⇐ U ⊣ Γ₃
  → Σ (Ctx Δ n) λ Γ₂′ →
      (Γ₁ ⊢ e₂ ⇐ U ⊣ Γ₂′)
      × (Γ₂′ ⊢ e₁ ⇒ T ⊣ Γ₃)
exchange-check-after-synth d₁ d₂
  with leftover-synth d₁
... | G , r
  with frame-check d₂ (remove-to-frame r)
... | Γ₂′ , f , d₂′ =
  Γ₂′ , d₂′ ,
  replay-transition-synth d₁ (remove-frame-replay r f)

-- A well-typed simultaneous substitution whose images consume disjoint
-- fragments of the target context.  Unlike the legacy relation, the empty
-- substitution leaves an arbitrary target context untouched; this is needed
-- when the substituted expression leaves live resources for its continuation.

tailSub :
  ∀ {Δ n m}
  → Sub Δ (Data.Nat.suc n) m
  → Sub Δ n m
tailSub σ x = σ (suc x)

-- Type renaming and term renaming act on independent namespaces.  The
-- commuting proof is structural; the match case packages its dependent
-- branch function through a sigma domain so that the accepted ordinary
-- function extensionality principle is sufficient.

mutual

  renTy-rename-value :
    ∀ {Δ₁ Δ₂ n m}
      (ϕ : Δ₁ →ᵣ Δ₂)
      (ρ : Ren {n} {m})
      (v : Value Δ₁ n)
    → renTyValue ϕ (renameValue ρ v)
        ≡ renameValue ρ (renTyValue ϕ v)
  renTy-rename-value ϕ ρ (ExprSyntax.V-Const c) = refl
  renTy-rename-value ϕ ρ (V-Var x) = refl
  renTy-rename-value ϕ ρ (ExprSyntax.V-Abs T e)
    rewrite renTy-rename-expr ϕ (ExprSubstitution.extRen ρ) e = refl
  renTy-rename-value ϕ ρ (ExprSyntax.V-Rec T U v)
    rewrite renTy-rename-value ϕ (ExprSubstitution.extRen ρ) v = refl
  renTy-rename-value ϕ ρ (ExprSyntax.V-TAbs K v)
    rewrite renTy-rename-value (ϕ ↑ᵣ K) ρ v = refl
  renTy-rename-value ϕ ρ (ExprSyntax.V-Pair v₁ v₂)
    rewrite renTy-rename-value ϕ ρ v₁
          | renTy-rename-value ϕ ρ v₂ = refl
  renTy-rename-value ϕ ρ (ExprSyntax.V-Receive₁ T) = refl
  renTy-rename-value ϕ ρ (ExprSyntax.V-Receive₂ T S) = refl
  renTy-rename-value ϕ ρ (ExprSyntax.V-Send₁ T) = refl
  renTy-rename-value ϕ ρ (ExprSyntax.V-Send₂ T S) = refl
  renTy-rename-value ϕ ρ (ExprSyntax.V-Select₁ v i P) = refl
  renTy-rename-value ϕ ρ (ExprSyntax.V-Select₂ v i P S) = refl

  renTy-rename-expr :
    ∀ {Δ₁ Δ₂ n m}
      (ϕ : Δ₁ →ᵣ Δ₂)
      (ρ : Ren {n} {m})
      (e : Expr Δ₁ n)
    → renTyExpr ϕ (renameExpr ρ e)
        ≡ renameExpr ρ (renTyExpr ϕ e)
  renTy-rename-expr ϕ ρ (E-Val v)
    rewrite renTy-rename-value ϕ ρ v = refl
  renTy-rename-expr ϕ ρ (ExprSyntax.E-App e₁ e₂)
    rewrite renTy-rename-expr ϕ ρ e₁
          | renTy-rename-expr ϕ ρ e₂ = refl
  renTy-rename-expr ϕ ρ (ExprSyntax.E-TApp e T)
    rewrite renTy-rename-expr ϕ ρ e = refl
  renTy-rename-expr ϕ ρ (ExprSyntax.E-LetUnit e₁ e₂)
    rewrite renTy-rename-expr ϕ ρ e₁
          | renTy-rename-expr ϕ ρ e₂ = refl
  renTy-rename-expr ϕ ρ (ExprSyntax.E-Pair e₁ e₂)
    rewrite renTy-rename-expr ϕ ρ e₁
          | renTy-rename-expr ϕ ρ e₂ = refl
  renTy-rename-expr ϕ ρ (ExprSyntax.E-LetPair e₁ e₂)
    rewrite renTy-rename-expr ϕ ρ e₁
          | renTy-rename-expr ϕ (ExprSubstitution.extRen2 ρ) e₂ = refl
  renTy-rename-expr ϕ ρ
      (ExprSyntax.E-Match {ss = ss} e ne branches)
    rewrite renTy-rename-expr ϕ ρ e
          | dependent-ext₂
              (λ i i∈ →
                renTy-rename-expr
                  ϕ
                  (ExprSubstitution.extRen ρ)
                  (branches i i∈)) = refl

wkTy-wkValue :
  ∀ {Δ n K}
    (v : Value Δ n)
  → wkTyValue {K = K} (wkValue v)
      ≡ wkValue (wkTyValue {K = K} v)
wkTy-wkValue {K = K} v =
  renTy-rename-value (weakenᵣ K) suc v

infix 4 _⊢σ_∶_⊣_

data _⊢σ_∶_⊣_ :
    ∀ {Δ m}
    → (Γt : Ctx Δ m)
    → ∀ {n}
    → Sub Δ n m
    → Ctx Δ n
    → Ctx Δ m
    → Set where
  S-∅ :
    ∀ {Δ m}
      {Γt : Ctx Δ m}
      {σ : Sub Δ 0 m}
    → Γt ⊢σ σ ∶ ∅ ⊣ Γt

  S-Lin :
    ∀ {Δ n m pk}
      {Γt : Ctx Δ m}
      {σ : Sub Δ (Data.Nat.suc n) m}
      {Γs : Ctx Δ n}
      {T : NfTy Δ (KV pk Lin)}
      {Γrest Γv Γv′ Γo : Ctx Δ m}
    → FrameCtx Γrest Γv Γt
    → Γv ⊢ᵥ σ zero ⇒ T ⊣ Γv′
    → ECP.AllUsed Γv′
    → Γrest ⊢σ tailSub σ ∶ Γs ⊣ Γo
    → Γt ⊢σ σ ∶ (T ∷ˡ Γs) ⊣ Γo

  S-Un :
    ∀ {Δ n m pk}
      {Γt : Ctx Δ m}
      {σ : Sub Δ (Data.Nat.suc n) m}
      {Γs : Ctx Δ n}
      {T : NfTy Δ (KV pk Un)}
      {Γo : Ctx Δ m}
    → ECP.allUsedCtx Γt
        ⊢ᵥ σ zero ⇒ T
        ⊣ ECP.allUsedCtx Γt
    → Γt ⊢σ tailSub σ ∶ Γs ⊣ Γo
    → Γt ⊢σ σ ∶ (T ∷ᵘ Γs) ⊣ Γo

  S-Used :
    ∀ {Δ n m pk}
      {Γt : Ctx Δ m}
      {σ : Sub Δ (Data.Nat.suc n) m}
      {Γs : Ctx Δ n}
      {T : NfTy Δ (KV pk Lin)}
      {Γo : Ctx Δ m}
    → Γt ⊢σ tailSub σ ∶ Γs ⊣ Γo
    → Γt ⊢σ σ ∶ (B-Used T ▻ Γs) ⊣ Γo

  S-TargetLive :
    ∀ {Δ n m pk}
      {Γt Γo : Ctx Δ m}
      {Γs : Ctx Δ n}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Lin)}
    → (σok : Γt ⊢σ σ ∶ Γs ⊣ Γo)
    → (B-Lin T ▻ Γt)
        ⊢σ tailSub (extSub σ) ∶ Γs
        ⊣ (B-Lin T ▻ Γo)

  S-TargetUsed :
    ∀ {Δ n m pk}
      {Γt Γo : Ctx Δ m}
      {Γs : Ctx Δ n}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Lin)}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → (B-Used T ▻ Γt)
        ⊢σ tailSub (extSub σ) ∶ Γs
        ⊣ (B-Used T ▻ Γo)

  S-TargetUn :
    ∀ {Δ n m pk}
      {Γt Γo : Ctx Δ m}
      {Γs : Ctx Δ n}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Un)}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → (B-Un T ▻ Γt)
        ⊢σ tailSub (extSub σ) ∶ Γs
        ⊣ (B-Un T ▻ Γo)


data Residual :
    ∀ {Δ n m}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → ∀ {Γs′ Γt′}
    → Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo
    → Set where
  RS-∅ :
    ∀ {Δ m}
      {Γt : Ctx Δ m}
      {σ : Sub Δ 0 m}
    → Residual
        (S-∅ {Γt = Γt} {σ = σ})
        S-∅

  RS-LinLive :
    ∀ {Δ n m pk}
      {Γs Γs′ : Ctx Δ n}
      {Γrest Γrest′ Γv Γv′ Γt Γt′ Γo : Ctx Δ m}
      {σ : Sub Δ (Data.Nat.suc n) m}
      {T : NfTy Δ (KV pk Lin)}
      {frame : FrameCtx Γrest Γv Γt}
      {frame′ : FrameCtx Γrest′ Γv Γt′}
      {dv : Γv ⊢ᵥ σ zero ⇒ T ⊣ Γv′}
      {au : ECP.AllUsed Γv′}
      {σtail : Γrest ⊢σ tailSub σ ∶ Γs ⊣ Γo}
      {σtail′ : Γrest′ ⊢σ tailSub σ ∶ Γs′ ⊣ Γo}
    → Residual σtail σtail′
    → Residual
        (S-Lin {σ = σ} frame dv au σtail)
        (S-Lin {σ = σ} frame′ dv au σtail′)

  RS-LinUsed :
    ∀ {Δ n m pk}
      {Γs Γs′ : Ctx Δ n}
      {Γrest Γrest′ Γv Γv′ Γt Γo : Ctx Δ m}
      {σ : Sub Δ (Data.Nat.suc n) m}
      {T : NfTy Δ (KV pk Lin)}
      {frame : FrameCtx Γrest Γv Γt}
      {dv : Γv ⊢ᵥ σ zero ⇒ T ⊣ Γv′}
      {au : ECP.AllUsed Γv′}
      {σtail : Γrest ⊢σ tailSub σ ∶ Γs ⊣ Γo}
      {σtail′ : Γrest′ ⊢σ tailSub σ ∶ Γs′ ⊣ Γo}
    → Residual σtail σtail′
    → Residual
        (S-Lin {σ = σ} frame dv au σtail)
        (S-Used {σ = σ} {T = T} σtail′)

  RS-Un :
    ∀ {Δ n m pk}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γt′ Γo : Ctx Δ m}
      {σ : Sub Δ (Data.Nat.suc n) m}
      {T : NfTy Δ (KV pk Un)}
      {d0 :
        ECP.allUsedCtx Γt
          ⊢ᵥ σ zero ⇒ T
          ⊣ ECP.allUsedCtx Γt}
      {d0′ :
        ECP.allUsedCtx Γt′
          ⊢ᵥ σ zero ⇒ T
          ⊣ ECP.allUsedCtx Γt′}
      {σtail : Γt ⊢σ tailSub σ ∶ Γs ⊣ Γo}
      {σtail′ : Γt′ ⊢σ tailSub σ ∶ Γs′ ⊣ Γo}
    → Residual σtail σtail′
    → Residual
        (S-Un {σ = σ} d0 σtail)
        (S-Un {σ = σ} d0′ σtail′)

  RS-Used :
    ∀ {Δ n m pk}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γt′ Γo : Ctx Δ m}
      {σ : Sub Δ (Data.Nat.suc n) m}
      {T : NfTy Δ (KV pk Lin)}
      {σtail : Γt ⊢σ tailSub σ ∶ Γs ⊣ Γo}
      {σtail′ : Γt′ ⊢σ tailSub σ ∶ Γs′ ⊣ Γo}
    → Residual σtail σtail′
    → Residual
        (S-Used {σ = σ} {T = T} σtail)
        (S-Used {σ = σ} {T = T} σtail′)

  RS-TargetLive :
    ∀ {Δ n m pk}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γt′ Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Lin)}
      {σok : Γt ⊢σ σ ∶ Γs ⊣ Γo}
      {σok′ : Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo}
    → Residual σok σok′
    → Residual
        (S-TargetLive {T = T} σok)
        (S-TargetLive {T = T} σok′)

  RS-TargetUsed :
    ∀ {Δ n m pk}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γt′ Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Lin)}
      {σok : Γt ⊢σ σ ∶ Γs ⊣ Γo}
      {σok′ : Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo}
    → Residual σok σok′
    → Residual
        (S-TargetUsed {T = T} σok)
        (S-TargetUsed {T = T} σok′)

  RS-TargetUn :
    ∀ {Δ n m pk}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γt′ Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Un)}
      {σok : Γt ⊢σ σ ∶ Γs ⊣ Γo}
      {σok′ : Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo}
    → Residual σok σok′
    → Residual
        (S-TargetUn {T = T} σok)
        (S-TargetUn {T = T} σok′)


residual-refl :
  ∀ {Δ n m}
    {Γs : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    (σok : Γt ⊢σ σ ∶ Γs ⊣ Γo)
  → Residual σok σok
residual-refl S-∅ =
  RS-∅
residual-refl (S-Lin frame dv au σtail) =
  RS-LinLive (residual-refl σtail)
residual-refl (S-Un d0 σtail) =
  RS-Un (residual-refl σtail)
residual-refl (S-Used σtail) =
  RS-Used (residual-refl σtail)
residual-refl (S-TargetLive σok) =
  RS-TargetLive (residual-refl σok)
residual-refl (S-TargetUsed σok) =
  RS-TargetUsed (residual-refl σok)
residual-refl (S-TargetUn σok) =
  RS-TargetUn (residual-refl σok)

residual-target-unique :
  ∀ {Δ n m}
    {Γs Γs′ : Ctx Δ n}
    {Γt Γt₁ Γt₂ Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {σok : Γt ⊢σ σ ∶ Γs ⊣ Γo}
    {σok₁ : Γt₁ ⊢σ σ ∶ Γs′ ⊣ Γo}
    {σok₂ : Γt₂ ⊢σ σ ∶ Γs′ ⊣ Γo}
  → Residual σok σok₁
  → Residual σok σok₂
  → Γt₁ ≡ Γt₂
residual-target-unique RS-∅ RS-∅ =
  refl
residual-target-unique
    (RS-LinLive {frame′ = frame₁} r₁)
    (RS-LinLive {frame′ = frame₂} r₂)
  with residual-target-unique r₁ r₂
... | refl =
  frame-unique frame₁ frame₂
residual-target-unique
    (RS-LinUsed r₁)
    (RS-LinUsed r₂) =
  residual-target-unique r₁ r₂
residual-target-unique
    (RS-Un r₁)
    (RS-Un r₂) =
  residual-target-unique r₁ r₂
residual-target-unique
    (RS-Used r₁)
    (RS-Used r₂) =
  residual-target-unique r₁ r₂
residual-target-unique
    (RS-TargetLive r₁)
    (RS-TargetLive r₂) =
  cong (B-Lin _ ▻_) (residual-target-unique r₁ r₂)
residual-target-unique
    (RS-TargetUsed r₁)
    (RS-TargetUsed r₂) =
  cong (B-Used _ ▻_) (residual-target-unique r₁ r₂)
residual-target-unique
    (RS-TargetUn r₁)
    (RS-TargetUn r₂) =
  cong (B-Un _ ▻_) (residual-target-unique r₁ r₂)

residual-compose :
  ∀ {Δ n m}
    {Γs₁ Γs₂ Γs₃ : Ctx Δ n}
    {Γt₁ Γt₂ Γt₃ Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {σok₁ : Γt₁ ⊢σ σ ∶ Γs₁ ⊣ Γo}
    {σok₂ : Γt₂ ⊢σ σ ∶ Γs₂ ⊣ Γo}
    {σok₃ : Γt₃ ⊢σ σ ∶ Γs₃ ⊣ Γo}
  → Residual σok₁ σok₂
  → Residual σok₂ σok₃
  → Residual σok₁ σok₃
residual-compose RS-∅ RS-∅ =
  RS-∅
residual-compose
    (RS-LinLive r₁)
    (RS-LinLive r₂) =
  RS-LinLive (residual-compose r₁ r₂)
residual-compose
    (RS-LinLive r₁)
    (RS-LinUsed r₂) =
  RS-LinUsed (residual-compose r₁ r₂)
residual-compose
    (RS-LinUsed r₁)
    (RS-Used r₂) =
  RS-LinUsed (residual-compose r₁ r₂)
residual-compose
    (RS-Un r₁)
    (RS-Un r₂) =
  RS-Un (residual-compose r₁ r₂)
residual-compose
    (RS-Used r₁)
    (RS-Used r₂) =
  RS-Used (residual-compose r₁ r₂)
residual-compose
    (RS-TargetLive r₁)
    (RS-TargetLive r₂) =
  RS-TargetLive (residual-compose r₁ r₂)
residual-compose
    (RS-TargetUsed r₁)
    (RS-TargetUsed r₂) =
  RS-TargetUsed (residual-compose r₁ r₂)
residual-compose
    (RS-TargetUn r₁)
    (RS-TargetUn r₂) =
  RS-TargetUn (residual-compose r₁ r₂)

wk-AllUsed :
  ∀ {Δ n K} {Γ : Ctx Δ n}
  → ECP.AllUsed Γ
  → ECP.AllUsed (wkCtx {K = K} Γ)
wk-AllUsed ECP.AU-∅ = ECP.AU-∅
wk-AllUsed (ECP.AU-used au) = ECP.AU-used (wk-AllUsed au)
wk-AllUsed (ECP.AU-un au) = ECP.AU-un (wk-AllUsed au)

liftTySub-tail :
  ∀ {Δ n m K}
    (σ : Sub Δ (Data.Nat.suc n) m)
  → liftTySub {K = K} (tailSub σ)
      ≡ tailSub (liftTySub {K = K} σ)
liftTySub-tail σ = ext _ _ (λ _ → refl)

liftTySub-target-tail :
  ∀ {Δ n m K}
    (σ : Sub Δ n m)
  → liftTySub {K = K} (tailSub (extSub σ))
      ≡ tailSub (extSub (liftTySub {K = K} σ))
liftTySub-target-tail σ =
  ext _ _ (λ x → wkTy-wkValue (σ x))

cast-substitution-relation :
  ∀ {Δ n m}
    {Γs : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ τ : Sub Δ n m}
  → σ ≡ τ
  → Γt ⊢σ σ ∶ Γs ⊣ Γo
  → Γt ⊢σ τ ∶ Γs ⊣ Γo
cast-substitution-relation refl σok = σok

cast-residual-substitution :
  ∀ {Δ n m}
    {Γs Γs′ : Ctx Δ n}
    {Γt Γt′ Γo : Ctx Δ m}
    {σ τ : Sub Δ n m}
    {σok : Γt ⊢σ σ ∶ Γs ⊣ Γo}
    {σok′ : Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo}
    (eq : σ ≡ τ)
  → Residual σok σok′
  → Residual
      (cast-substitution-relation eq σok)
      (cast-substitution-relation eq σok′)
cast-residual-substitution refl r = r

lift-substitution-relation :
  ∀ {Δ n m K}
    {Γs : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
  → Γt ⊢σ σ ∶ Γs ⊣ Γo
  → wkCtx {K = K} Γt
      ⊢σ liftTySub σ ∶ wkCtx Γs
      ⊣ wkCtx Γo
lift-substitution-relation S-∅ =
  S-∅
lift-substitution-relation
    {K = K}
    {σ = σ}
    (S-Lin frame dv au σtail) =
  S-Lin
    (wkFrameCtx frame)
    (wkTy-preserves-value dv)
    (wk-AllUsed au)
    (cast-substitution-relation
      (liftTySub-tail {K = K} σ)
      (lift-substitution-relation σtail))
lift-substitution-relation
    {K = K}
    {Γt = Γt}
    {σ = σ}
    (S-Un d0 σtail) =
  S-Un
    (subst
      (λ X → X ⊢ᵥ liftTySub σ zero ⇒ _ ⊣ X)
      (sym (wk-allUsedCtx Γt))
      (wkTy-preserves-value d0))
    (cast-substitution-relation
      (liftTySub-tail {K = K} σ)
      (lift-substitution-relation σtail))
lift-substitution-relation
    {K = K}
    {σ = σ}
    (S-Used σtail) =
  S-Used
    (cast-substitution-relation
      (liftTySub-tail {K = K} σ)
      (lift-substitution-relation σtail))
lift-substitution-relation
    {K = K}
    (S-TargetLive {σ = σ} {T = T} σok) =
  cast-substitution-relation
    (sym (liftTySub-target-tail {K = K} σ))
    (S-TargetLive {T = wkNfTy T}
      (lift-substitution-relation σok))
lift-substitution-relation
    {K = K}
    (S-TargetUsed {σ = σ} {T = T} σok) =
  cast-substitution-relation
    (sym (liftTySub-target-tail {K = K} σ))
    (S-TargetUsed {T = wkNfTy T}
      (lift-substitution-relation σok))
lift-substitution-relation
    {K = K}
    (S-TargetUn {σ = σ} {T = T} σok) =
  cast-substitution-relation
    (sym (liftTySub-target-tail {K = K} σ))
    (S-TargetUn {T = wkNfTy T}
      (lift-substitution-relation σok))

lift-residual :
  ∀ {Δ n m K}
    {Γs Γs′ : Ctx Δ n}
    {Γt Γt′ Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {σok : Γt ⊢σ σ ∶ Γs ⊣ Γo}
    {σok′ : Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo}
  → Residual σok σok′
  → Residual
      (lift-substitution-relation {K = K} σok)
      (lift-substitution-relation {K = K} σok′)
lift-residual RS-∅ = RS-∅
lift-residual {K = K} (RS-LinLive {σ = σ} r) =
  RS-LinLive
    (cast-residual-substitution
      (liftTySub-tail {K = K} σ)
      (lift-residual r))
lift-residual {K = K} (RS-LinUsed {σ = σ} r) =
  RS-LinUsed
    (cast-residual-substitution
      (liftTySub-tail {K = K} σ)
      (lift-residual r))
lift-residual {K = K} (RS-Un {σ = σ} r) =
  RS-Un
    (cast-residual-substitution
      (liftTySub-tail {K = K} σ)
      (lift-residual r))
lift-residual {K = K} (RS-Used {σ = σ} r) =
  RS-Used
    (cast-residual-substitution
      (liftTySub-tail {K = K} σ)
      (lift-residual r))
lift-residual {K = K} (RS-TargetLive {σ = σ} r) =
  cast-residual-substitution
    (sym (liftTySub-target-tail {K = K} σ))
    (RS-TargetLive (lift-residual r))
lift-residual {K = K} (RS-TargetUsed {σ = σ} r) =
  cast-residual-substitution
    (sym (liftTySub-target-tail {K = K} σ))
    (RS-TargetUsed (lift-residual r))
lift-residual {K = K} (RS-TargetUn {σ = σ} r) =
  cast-residual-substitution
    (sym (liftTySub-target-tail {K = K} σ))
    (RS-TargetUn (lift-residual r))

merge-right-allUsed :
  ∀ {Δ n}
    (Γ : Ctx Δ n)
  → FrameCtx Γ (ECP.allUsedCtx Γ) Γ
merge-right-allUsed ∅ = FC-∅
merge-right-allUsed (B-Lin T ▻ Γ) =
  FC-frame (merge-right-allUsed Γ)
merge-right-allUsed (B-Un T ▻ Γ) =
  FC-un (merge-right-allUsed Γ)
merge-right-allUsed (B-Used T ▻ Γ) =
  FC-allused (merge-right-allUsed Γ)

lift-tail-live :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Lin)}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → (B-Lin T ▻ Γt)
        ⊢σ tailSub (extSub σ) ∶ Γs
        ⊣ (B-Lin T ▻ Γo)
lift-tail-live = S-TargetLive

lift-tail-used :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Lin)}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → (B-Used T ▻ Γt)
        ⊢σ tailSub (extSub σ) ∶ Γs
        ⊣ (B-Used T ▻ Γo)
lift-tail-used = S-TargetUsed

lift-tail-un :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Un)}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → (B-Un T ▻ Γt)
        ⊢σ tailSub (extSub σ) ∶ Γs
        ⊣ (B-Un T ▻ Γo)
lift-tail-un = S-TargetUn

frame-assoc-right :
  ∀ {Δ n}
    {Γbody Γmid Γin Γvalue Γout : Ctx Δ n}
  → FrameCtx Γbody Γmid Γin
  → FrameCtx Γvalue Γout Γmid
  → Σ (Ctx Δ n) λ Γrest →
      FrameCtx Γbody Γout Γrest
      × FrameCtx Γrest Γvalue Γin
frame-assoc-right FC-∅ FC-∅ =
  ∅ , FC-∅ , FC-∅
frame-assoc-right (FC-allused f₁) (FC-allused f₂)
  with frame-assoc-right f₁ f₂
... | Γrest , body-out , rest-value =
  _ , FC-allused body-out , FC-allused rest-value
frame-assoc-right (FC-live f₁) (FC-live f₂)
  with frame-assoc-right f₁ f₂
... | Γrest , body-out , rest-value =
  _ , FC-live body-out , FC-frame rest-value
frame-assoc-right (FC-live f₁) (FC-frame f₂)
  with frame-assoc-right f₁ f₂
... | Γrest , body-out , rest-value =
  _ , FC-allused body-out , FC-live rest-value
frame-assoc-right (FC-frame f₁) (FC-allused f₂)
  with frame-assoc-right f₁ f₂
... | Γrest , body-out , rest-value =
  _ , FC-frame body-out , FC-frame rest-value
frame-assoc-right (FC-un f₁) (FC-un f₂)
  with frame-assoc-right f₁ f₂
... | Γrest , body-out , rest-value =
  _ , FC-un body-out , FC-un rest-value

identitySub :
  ∀ {Δ n}
  → Sub Δ n n
identitySub x = V-Var x

tail-singleSub-identitySub :
  ∀ {Δ : List Kind} {n : ℕ}
    (v : Value Δ n)
  → tailSub (singleSub v) ≡ identitySub
tail-singleSub-identitySub v =
  ext _ _ (λ x → refl)

identity-substitution-canonical :
  ∀ {Δ n}
    {Γs Γo Γt : Ctx Δ n}
  → FrameCtx Γs Γo Γt
  → Γt ⊢σ identitySub ∶ Γs ⊣ Γo
identity-substitution-canonical FC-∅ =
  S-∅
identity-substitution-canonical
    (FC-allused frame) =
  S-Used
    (lift-tail-used
      (identity-substitution-canonical frame))
identity-substitution-canonical
    {Γt = B-Lin T ▻ Γt}
    (FC-live frame) =
  S-Used
    (lift-tail-live
      (identity-substitution-canonical frame))
identity-substitution-canonical
    {Γt = B-Lin T ▻ Γt}
    (FC-frame frame) =
  S-Lin
    (FC-live (merge-right-allUsed Γt))
    (TV-Var-Lin take-here)
    (ECP.AU-used (ECP.allUsedCtx-AllUsed Γt))
    (lift-tail-used
      (identity-substitution-canonical frame))
identity-substitution-canonical
    {Γt = B-Un T ▻ Γt}
    (FC-un frame) =
  S-Un
    (TV-Var-Un hereᵘ)
    (lift-tail-un
      (identity-substitution-canonical frame))

single-substitution-relation :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ Γ₃ G : Ctx Δ n}
    {T : NfTy Δ (KV pk Lin)}
    {v : Value Δ n}
  → Γ₂ ⊢ᵥ v ⇒ T ⊣ Γ₃
  → RemoveCtx Γ₁ G Γ₂
  → Γ₁ ⊢σ singleSub v ∶ (T ∷ˡ G) ⊣ Γ₃
single-substitution-relation {v = v} dv rbody
  with strip-value dv
... | Gv , Gv′ , rv , dv′ , au
  with frame-assoc-right
         (remove-to-frame rbody)
         (remove-to-frame rv)
... | Γrest , body-out , rest-value =
  S-Lin
    rest-value
    dv′
    au
    (identity-substitution-canonical body-out)

extend-substitution-linear :
  ∀ {Δ n m pk}
    {Γs : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {T : NfTy Δ (KV pk Lin)}
  → Γt ⊢σ σ ∶ Γs ⊣ Γo
  → (T ∷ˡ Γt) ⊢σ extSub σ ∶ (T ∷ˡ Γs)
      ⊣ (B-Used T ▻ Γo)
extend-substitution-linear {Γt = Γt} σok =
  S-Lin
    (FC-live (merge-right-allUsed Γt))
    (TV-Var-Lin take-here)
    (ECP.AU-used (ECP.allUsedCtx-AllUsed Γt))
    (S-TargetUsed σok)

extend-substitution-unrestricted :
  ∀ {Δ n m pk}
    {Γs : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {T : NfTy Δ (KV pk Un)}
  → Γt ⊢σ σ ∶ Γs ⊣ Γo
  → (T ∷ᵘ Γt) ⊢σ extSub σ ∶ (T ∷ᵘ Γs)
      ⊣ (T ∷ᵘ Γo)
extend-substitution-unrestricted σok =
  S-Un (TV-Var-Un hereᵘ) (S-TargetUn σok)

extend-substitution-linear2 :
  ∀ {Δ n m pk₁ pk₂}
    {Γs : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {T : NfTy Δ (KV pk₁ Lin)}
    {U : NfTy Δ (KV pk₂ Lin)}
  → Γt ⊢σ σ ∶ Γs ⊣ Γo
  → (T ∷ˡ (U ∷ˡ Γt)) ⊢σ extSub2 σ ∶ (T ∷ˡ (U ∷ˡ Γs))
      ⊣ (B-Used T ▻ B-Used U ▻ Γo)
extend-substitution-linear2 σok =
  extend-substitution-linear (extend-substitution-linear σok)

swapFrameCtx :
  ∀ {Δ n}
    {Γrest Γv Γt : Ctx Δ n}
  → FrameCtx Γrest Γv Γt
  → FrameCtx Γv Γrest Γt
swapFrameCtx FC-∅ = FC-∅
swapFrameCtx (FC-allused frame) =
  FC-allused (swapFrameCtx frame)
swapFrameCtx (FC-live frame) =
  FC-frame (swapFrameCtx frame)
swapFrameCtx (FC-frame frame) =
  FC-live (swapFrameCtx frame)
swapFrameCtx (FC-un frame) =
  FC-un (swapFrameCtx frame)

consume-image :
  ∀ {Δ n pk m}
    {Γrest Γv Γt Γv′ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
  → FrameCtx Γrest Γv Γt
  → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
  → ECP.AllUsed Γv′
  → Γt ⊢ᵥ v ⇒ T ⊣ Γrest
consume-image frame dv au =
  replay-value-allUsed dv frame au

lift-value-through-frame :
  ∀ {Δ n pk m}
    {Γrest Γmid Γv Γt : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
  → FrameCtx Γrest Γv Γt
  → Γrest ⊢ᵥ v ⇒ T ⊣ Γmid
  → Σ (Ctx Δ n) λ Γout →
      FrameCtx Γmid Γv Γout
      × (Γt ⊢ᵥ v ⇒ T ⊣ Γout)
lift-value-through-frame frame dv
  with frame-value dv (swapFrameCtx frame)
... | Γout , frame′ , dv′ =
  Γout , swapFrameCtx frame′ , dv′

replay-allUsed-value :
  ∀ {Δ n pk m}
    {Γ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
  → ECP.allUsedCtx Γ ⊢ᵥ v ⇒ T
      ⊣ ECP.allUsedCtx Γ
  → Γ ⊢ᵥ v ⇒ T ⊣ Γ
replay-allUsed-value {Γ = Γ} dv =
  replay-value-allUsed
    dv
    (merge-right-allUsed Γ)
    (ECP.allUsedCtx-AllUsed Γ)

allUsed-substitution-target :
  ∀ {Δ n m}
    {Γs : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
  → ECP.AllUsed Γs
  → Γt ⊢σ σ ∶ Γs ⊣ Γo
  → Γt ≡ Γo
allUsed-substitution-target ECP.AU-∅ S-∅ = refl
allUsed-substitution-target
    (ECP.AU-un au)
    (S-Un d0 σtail) =
  allUsed-substitution-target au σtail
allUsed-substitution-target
    (ECP.AU-used au)
    (S-Used σtail) =
  allUsed-substitution-target au σtail
allUsed-substitution-target au (S-TargetLive σok) =
  cong (B-Lin _ ▻_)
    (allUsed-substitution-target au σok)
allUsed-substitution-target au (S-TargetUsed σok) =
  cong (B-Used _ ▻_)
    (allUsed-substitution-target au σok)
allUsed-substitution-target au (S-TargetUn σok) =
  cong (B-Un _ ▻_)
    (allUsed-substitution-target au σok)

remove-allUsed-eq :
  ∀ {Δ n}
    {Γ G Γ′ : Ctx Δ n}
  → RemoveCtx Γ G Γ′
  → ECP.allUsedCtx Γ ≡ ECP.allUsedCtx Γ′
remove-allUsed-eq RM-∅ = refl
remove-allUsed-eq (RM-drop rm) =
  cong (B-Used _ ▻_) (remove-allUsed-eq rm)
remove-allUsed-eq (RM-allused rm) =
  cong (B-Used _ ▻_) (remove-allUsed-eq rm)
remove-allUsed-eq (RM-lin rm) =
  cong (B-Used _ ▻_) (remove-allUsed-eq rm)
remove-allUsed-eq (RM-un rm) =
  cong (B-Un _ ▻_) (remove-allUsed-eq rm)

advance-substitution :
  ∀ {Δ n m}
    {Γs Γs′ G : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    (rm : RemoveCtx Γs G Γs′)
    (σok : Γt ⊢σ σ ∶ Γs ⊣ Γo)
  → Σ (Ctx Δ m) λ Γt′ →
      Σ (Ctx Δ m) λ Gt →
        Σ (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo) λ σok′ →
          Residual σok σok′
          × RemoveCtx Γt Gt Γt′
advance-substitution RM-∅ S-∅ =
  _ , _ , S-∅ , RS-∅ , remove-allUsedCtx _
advance-substitution
    (RM-drop rm)
    (S-Lin frame dv au σtail)
  with advance-substitution rm σtail
... | Γrest′ , Gt , σtail′ , r , rmt
  with compose-merge-remove2 frame rmt
... | Γt′ , frame′ , rmt′ =
  Γt′ , Gt , S-Lin frame′ dv au σtail′ ,
  RS-LinLive r , rmt′
advance-substitution
    (RM-lin rm)
    (S-Lin frame dv au σtail)
  with advance-substitution rm σtail
... | Γrest′ , Gt , σtail′ , r , rmt
  with compose-merge-remove frame rmt
... | Gt′ , rmt′ =
  Γrest′ , Gt′ , S-Used σtail′ ,
  RS-LinUsed r , rmt′
advance-substitution
    (RM-un rm)
    (S-Un d0 σtail)
  with advance-substitution rm σtail
... | Γt′ , Gt , σtail′ , r , rmt =
  let d0′ = subst
              (λ X → X ⊢ᵥ _ ⇒ _ ⊣ X)
              (remove-allUsed-eq rmt)
              d0
  in Γt′ , Gt , S-Un d0′ σtail′ , RS-Un r , rmt
advance-substitution
    (RM-allused rm)
    (S-Used σtail)
  with advance-substitution rm σtail
... | Γt′ , Gt , σtail′ , r , rmt =
  Γt′ , Gt , S-Used σtail′ , RS-Used r , rmt
advance-substitution rm (S-TargetLive σok)
  with advance-substitution rm σok
... | Γt′ , Gt , σok′ , r , rmt =
  _ , _ , S-TargetLive σok′ ,
  RS-TargetLive r , RM-drop rmt
advance-substitution rm (S-TargetUsed σok)
  with advance-substitution rm σok
... | Γt′ , Gt , σok′ , r , rmt =
  _ , _ , S-TargetUsed σok′ ,
  RS-TargetUsed r , RM-allused rmt
advance-substitution rm (S-TargetUn σok)
  with advance-substitution rm σok
... | Γt′ , Gt , σok′ , r , rmt =
  _ , _ , S-TargetUn σok′ ,
  RS-TargetUn r , RM-un rmt

take-zero-invert :
  ∀ {Δ n pk₁ pk₂}
    {Γ : Ctx Δ n}
    {Γ′ : Ctx Δ (Data.Nat.suc n)}
    {T : NfTy Δ (KV pk₁ Lin)}
    {U : NfTy Δ (KV pk₂ Lin)}
  → (T ∷ˡ Γ) ⊢ˡ zero ∶ U ⊣ Γ′
  → Σ (pk₁ ≡ pk₂) λ where
      refl →
        (T ≡ U)
        × (Γ′ ≡ (B-Used T ▻ Γ))
take-zero-invert take-here =
  refl , refl , refl

take-there-lin-invert :
  ∀ {Δ n pk₁ pk₂}
    {Γ : Ctx Δ n}
    {Γ′ : Ctx Δ (Data.Nat.suc n)}
    {x : Fin n}
    {T : NfTy Δ (KV pk₁ Lin)}
    {U : NfTy Δ (KV pk₂ Lin)}
  → (T ∷ˡ Γ) ⊢ˡ suc x ∶ U ⊣ Γ′
  → Σ (Ctx Δ n) λ Γo →
      (Γ′ ≡ (T ∷ˡ Γo))
      × (Γ ⊢ˡ x ∶ U ⊣ Γo)
take-there-lin-invert (take-thereˡ take) =
  _ , refl , take

take-there-un-invert :
  ∀ {Δ n pk₁ pk₂}
    {Γ : Ctx Δ n}
    {Γ′ : Ctx Δ (Data.Nat.suc n)}
    {x : Fin n}
    {T : NfTy Δ (KV pk₁ Un)}
    {U : NfTy Δ (KV pk₂ Lin)}
  → (T ∷ᵘ Γ) ⊢ˡ suc x ∶ U ⊣ Γ′
  → Σ (Ctx Δ n) λ Γo →
      (Γ′ ≡ (T ∷ᵘ Γo))
      × (Γ ⊢ˡ x ∶ U ⊣ Γo)
take-there-un-invert (take-thereᵘ take) =
  _ , refl , take

take-there-used-invert :
  ∀ {Δ n pk₁ pk₂}
    {Γ : Ctx Δ n}
    {Γ′ : Ctx Δ (Data.Nat.suc n)}
    {x : Fin n}
    {T : NfTy Δ (KV pk₁ Lin)}
    {U : NfTy Δ (KV pk₂ Lin)}
  → (B-Used T ▻ Γ) ⊢ˡ suc x ∶ U ⊣ Γ′
  → Σ (Ctx Δ n) λ Γo →
      (Γ′ ≡ (B-Used T ▻ Γo))
      × (Γ ⊢ˡ x ∶ U ⊣ Γo)
take-there-used-invert (take-there✖ take) =
  _ , refl , take

unwk-cons :
  ∀ {Δ n K}
    {b : Binding Δ}
    {Γwk : Ctx (K ∷ Δ) n}
    {Γ : Ctx Δ (Data.Nat.suc n)}
  → (wkBinding {K = K} b ▻ Γwk) ≡ wkCtx {K = K} Γ
  → Σ (Ctx Δ n) λ Γtail →
      (Γ ≡ (b ▻ Γtail))
      × (Γwk ≡ wkCtx {K = K} Γtail)
unwk-cons {b = b} {Γ = b′ ▻ Γ} eq
  with wkBinding-injective
         (cong (λ where (b₀ ▻ _) → b₀) eq)
     | cong (λ where (_ ▻ Γ₀) → Γ₀) eq
... | refl | eqtail =
  Γ , refl , eqtail

unwk-take :
  ∀ {Δ n K pk}
    {Γ Γ′ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
  → wkCtx {K = K} Γ
      ⊢ˡ x ∶ wkNfTy {K′ = K} T
      ⊣ wkCtx {K = K} Γ′
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
unwk-take {Γ = ∅} {x = ()}
unwk-take {Γ = B-Lin U ▻ Γ} {x = zero} take
  with take-zero-invert take
... | refl , eqT , eqout
  with wkNfTy-injective eqT
... | refl
  with wkCtx-injective eqout
... | refl =
  take-here
unwk-take {Γ = B-Un U ▻ Γ} {x = zero} ()
unwk-take {Γ = B-Used U ▻ Γ} {x = zero} ()
unwk-take {Γ = B-Lin U ▻ Γ} {x = suc x} take
  with take-there-lin-invert take
... | Γwk , eqout , take′
  with unwk-cons (sym eqout)
... | Γo , eqΓ′ , eqwk
  rewrite eqΓ′ | eqwk =
    take-thereˡ (unwk-take take′)
unwk-take {Γ = B-Un U ▻ Γ} {x = suc x} take
  with take-there-un-invert take
... | Γwk , eqout , take′
  with unwk-cons (sym eqout)
... | Γo , eqΓ′ , eqwk
  rewrite eqΓ′ | eqwk =
    take-thereᵘ (unwk-take take′)
unwk-take {Γ = B-Used U ▻ Γ} {x = suc x} take
  with take-there-used-invert take
... | Γwk , eqout , take′
  with unwk-cons (sym eqout)
... | Γo , eqΓ′ , eqwk
  rewrite eqΓ′ | eqwk =
    take-there✖ (unwk-take take′)

unwk-take-exists :
  ∀ {Δ n K pk}
    {Γ : Ctx Δ n}
    {Γwk′ : Ctx (K ∷ Δ) n}
    {x : Fin n}
    {T : NfTy (K ∷ Δ) (KV pk Lin)}
  → wkCtx {K = K} Γ
      ⊢ˡ x ∶ T
      ⊣ Γwk′
  → Σ (NfTy Δ (KV pk Lin)) λ U →
      Σ (Ctx Δ n) λ Γ′ →
        (wkNfTy {K′ = K} U ≡ T)
        × (Γwk′ ≡ wkCtx {K = K} Γ′)
        × (Γ ⊢ˡ x ∶ U ⊣ Γ′)
unwk-take-exists {Γ = ∅} {x = ()}
unwk-take-exists
    {Γ = B-Lin U ▻ Γ}
    {x = zero}
    take
  with take-zero-invert take
... | refl , eqT , eqout
  =
  U ,
  (B-Used U ▻ Γ) ,
  eqT ,
  eqout ,
  take-here
unwk-take-exists {Γ = B-Un U ▻ Γ} {x = zero} ()
unwk-take-exists {Γ = B-Used U ▻ Γ} {x = zero} ()
unwk-take-exists
    {Γ = B-Lin U ▻ Γ}
    {x = suc x}
    take
  with take-there-lin-invert take
... | Γwk , eqout , take′
  with unwk-take-exists take′
... | V , Γo , eqT , eqwk , take₀ =
  V ,
  (B-Lin U ▻ Γo) ,
  eqT ,
  trans eqout (cong (B-Lin _ ▻_) eqwk) ,
  take-thereˡ take₀
unwk-take-exists
    {Γ = B-Un U ▻ Γ}
    {x = suc x}
    take
  with take-there-un-invert take
... | Γwk , eqout , take′
  with unwk-take-exists take′
... | V , Γo , eqT , eqwk , take₀ =
  V ,
  (B-Un U ▻ Γo) ,
  eqT ,
  trans eqout (cong (B-Un _ ▻_) eqwk) ,
  take-thereᵘ take₀
unwk-take-exists
    {Γ = B-Used U ▻ Γ}
    {x = suc x}
    take
  with take-there-used-invert take
... | Γwk , eqout , take′
  with unwk-take-exists take′
... | V , Γo , eqT , eqwk , take₀ =
  V ,
  (B-Used U ▻ Γo) ,
  eqT ,
  trans eqout (cong (B-Used _ ▻_) eqwk) ,
  take-there✖ take₀

unrestricted-zero-invert :
  ∀ {Δ n pk₁ pk₂}
    {Γ : Ctx Δ n}
    {T : NfTy Δ (KV pk₁ Un)}
    {U : NfTy Δ (KV pk₂ Un)}
  → (T ∷ᵘ Γ) ∋ᵘ zero ∶ U
  → Σ (pk₁ ≡ pk₂) λ where
      refl → T ≡ U
unrestricted-zero-invert hereᵘ =
  refl , refl

unwk-unrestricted :
  ∀ {Δ n K pk}
    {Γ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Un)}
  → wkCtx {K = K} Γ
      ∋ᵘ x ∶ wkNfTy {K′ = K} T
  → Γ ∋ᵘ x ∶ T
unwk-unrestricted {Γ = ∅} {x = ()}
unwk-unrestricted {Γ = B-Lin U ▻ Γ} {x = zero} ()
unwk-unrestricted {Γ = B-Un U ▻ Γ} {x = zero} x∈
  with unrestricted-zero-invert x∈
... | refl , eqT
  with wkNfTy-injective eqT
... | refl =
  hereᵘ
unwk-unrestricted {Γ = B-Used U ▻ Γ} {x = zero} ()
unwk-unrestricted {Γ = B-Lin U ▻ Γ} {x = suc x}
    (thereᵘˡ x∈) =
  thereᵘˡ (unwk-unrestricted x∈)
unwk-unrestricted {Γ = B-Un U ▻ Γ} {x = suc x}
    (thereᵘᵘ x∈) =
  thereᵘᵘ (unwk-unrestricted x∈)
unwk-unrestricted {Γ = B-Used U ▻ Γ} {x = suc x}
    (thereᵘ✖ x∈) =
  thereᵘ✖ (unwk-unrestricted x∈)

unwk-unrestricted-exists :
  ∀ {Δ n K pk}
    {Γ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy (K ∷ Δ) (KV pk Un)}
  → wkCtx {K = K} Γ ∋ᵘ x ∶ T
  → Σ (NfTy Δ (KV pk Un)) λ U →
      (wkNfTy {K′ = K} U ≡ T)
      × (Γ ∋ᵘ x ∶ U)
unwk-unrestricted-exists {Γ = ∅} {x = ()}
unwk-unrestricted-exists {Γ = B-Lin U ▻ Γ} {x = zero} ()
unwk-unrestricted-exists
    {Γ = B-Un U ▻ Γ}
    {x = zero}
    x∈
  with unrestricted-zero-invert x∈
... | refl , eqT =
  U , eqT , hereᵘ
unwk-unrestricted-exists {Γ = B-Used U ▻ Γ} {x = zero} ()
unwk-unrestricted-exists
    {Γ = B-Lin U ▻ Γ}
    {x = suc x}
    (thereᵘˡ x∈)
  with unwk-unrestricted-exists x∈
... | V , eqT , x∈₀ =
  V , eqT , thereᵘˡ x∈₀
unwk-unrestricted-exists
    {Γ = B-Un U ▻ Γ}
    {x = suc x}
    (thereᵘᵘ x∈)
  with unwk-unrestricted-exists x∈
... | V , eqT , x∈₀ =
  V , eqT , thereᵘᵘ x∈₀
unwk-unrestricted-exists
    {Γ = B-Used U ▻ Γ}
    {x = suc x}
    (thereᵘ✖ x∈)
  with unwk-unrestricted-exists x∈
... | V , eqT , x∈₀ =
  V , eqT , thereᵘ✖ x∈₀

mutual

  substitution-lookup-lin :
    ∀ {Δ n m pk}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {x : Fin n}
      {T : NfTy Δ (KV pk Lin)}
    → (σok : Γt ⊢σ σ ∶ Γs ⊣ Γo)
    → Γs ⊢ˡ x ∶ T ⊣ Γs′
    → Σ (Ctx Δ m) λ Γt′ →
        Σ (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo) λ σok′ →
          (Γt ⊢ᵥ σ x ⇒ T ⊣ Γt′)
          × Residual σok σok′
  substitution-lookup-lin
      (S-Lin frame dv au σtail)
      take-here =
    _ ,
    S-Used σtail ,
    consume-image frame dv au ,
    RS-LinUsed (residual-refl σtail)
  substitution-lookup-lin
      (S-Lin frame dv au σtail)
      (take-thereˡ take)
    with substitution-lookup-lin σtail take
  ... | Γmid , σtail′ , dmid , r
    with lift-value-through-frame frame dmid
  ... | Γout , frame′ , dout =
    Γout ,
    S-Lin frame′ dv au σtail′ ,
    dout ,
    RS-LinLive r
  substitution-lookup-lin
      (S-Un d0 σtail)
      (take-thereᵘ take)
    with substitution-lookup-lin σtail take
  ... | Γt′ , σtail′ , d′ , r =
    let eq = ExprContextShape.~Ctx-allUsedCtx
               (value-preserves-~Ctx d′)
        d0′ = subst
                (λ X → X ⊢ᵥ _ ⇒ _ ⊣ X)
                eq
                d0
    in Γt′ , S-Un d0′ σtail′ , d′ , RS-Un r
  substitution-lookup-lin
      (S-Used σtail)
      (take-there✖ take)
    with substitution-lookup-lin σtail take
  ... | Γt′ , σtail′ , d′ , r =
    Γt′ , S-Used σtail′ , d′ , RS-Used r
  substitution-lookup-lin
      (S-TargetLive {T = T} σok)
      take
    with substitution-lookup-lin σok take
  ... | Γt′ , σok′ , d′ , r =
    _ ,
    S-TargetLive σok′ ,
    wk-preserves-value (B-Lin T) d′ ,
    RS-TargetLive r
  substitution-lookup-lin
      (S-TargetUsed {T = T} σok)
      take
    with substitution-lookup-lin σok take
  ... | Γt′ , σok′ , d′ , r =
    _ ,
    S-TargetUsed σok′ ,
    wk-preserves-value (B-Used T) d′ ,
    RS-TargetUsed r
  substitution-lookup-lin
      (S-TargetUn {T = T} σok)
      take
    with substitution-lookup-lin σok take
  ... | Γt′ , σok′ , d′ , r =
    _ ,
    S-TargetUn σok′ ,
    wk-preserves-value (B-Un T) d′ ,
    RS-TargetUn r

  substitution-lookup-un :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {x : Fin n}
      {T : NfTy Δ (KV pk Un)}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Γs ∋ᵘ x ∶ T
    → Γt ⊢ᵥ σ x ⇒ T ⊣ Γt
  substitution-lookup-un
      (S-Un d0 σtail)
      hereᵘ =
    replay-allUsed-value d0
  substitution-lookup-un
      (S-Lin frame dv au σtail)
      (thereᵘˡ x∈) =
    replay-value
      (substitution-lookup-un σtail x∈)
      (swapFrameCtx frame)
      (swapFrameCtx frame)
  substitution-lookup-un
      (S-Un d0 σtail)
      (thereᵘᵘ x∈) =
    substitution-lookup-un σtail x∈
  substitution-lookup-un
      (S-Used σtail)
      (thereᵘ✖ x∈) =
    substitution-lookup-un σtail x∈
  substitution-lookup-un
      (S-TargetLive {T = T} σok)
      x∈ =
    wk-preserves-value
      (B-Lin T)
      (substitution-lookup-un σok x∈)
  substitution-lookup-un
      (S-TargetUsed {T = T} σok)
      x∈ =
    wk-preserves-value
      (B-Used T)
      (substitution-lookup-un σok x∈)
  substitution-lookup-un
      (S-TargetUn {T = T} σok)
      x∈ =
    wk-preserves-value
      (B-Un T)
      (substitution-lookup-un σok x∈)

mutual

  substitution-preserves-value :
    ∀ {Δ n m pk mult}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {v : Value Δ n}
      {T : NfTy Δ (KV pk mult)}
    → (σok : Γt ⊢σ σ ∶ Γs ⊣ Γo)
    → Γs ⊢ᵥ v ⇒ T ⊣ Γs′
    → Σ (Ctx Δ m) λ Γt′ →
        Σ (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo) λ σok′ →
          (Γt ⊢ᵥ substValueWith σ v ⇒ T ⊣ Γt′)
          × Residual σok σok′
  substitution-preserves-value σok (TV-Const cT) =
    _ , σok , TV-Const cT , residual-refl σok
  substitution-preserves-value σok (TV-Var-Lin take) =
    substitution-lookup-lin σok take
  substitution-preserves-value σok (TV-Var-Un x∈) =
    _ , σok , substitution-lookup-un σok x∈ , residual-refl σok
  substitution-preserves-value σok (TV-Abs body)
    with substitution-preserves-synth
           (extend-substitution-linear σok)
           body
  ... | _ , S-Used (S-TargetUsed σok′) , body′ ,
        RS-LinUsed (RS-TargetUsed r) =
    _ , σok′ , TV-Abs body′ , r
  substitution-preserves-value {Γt = Γt} σok (TV-Rec body)
    with substitution-preserves-check
           (extend-substitution-unrestricted σok)
           body
  ... | _ , S-Un d0 (S-TargetUn σok′) , body′ ,
        RS-Un (RS-TargetUn r)
    with residual-target-unique r (residual-refl σok)
  ... | refl =
    Γt , σok′ , TV-Rec body′ , r
  substitution-preserves-value σok (TV-TAbs {K = K} body)
    with leftover-value body
  ... | Gw , rmw
    with strip-wk rmw
  ... | G , rm
    with advance-substitution rm σok
  ... | Γbase′ , Gt , σbase′ , rbase , rmt
    with substitution-preserves-value
           (lift-substitution-relation {K = K} σok)
           body
  ... | Γlift′ , σlift′ , body′ , rlift
    with residual-target-unique rlift (lift-residual rbase)
  ... | refl =
    Γbase′ , σbase′ , TV-TAbs body′ , rbase
  substitution-preserves-value σok (TV-Pair d₁ d₂)
    with substitution-preserves-value σok d₁
  ... | Γt₂ , σok₂ , d₁′ , r₁
    with substitution-preserves-value σok₂ d₂
  ... | Γt₃ , σok₃ , d₂′ , r₂ =
    Γt₃ , σok₃ , TV-Pair d₁′ d₂′ , residual-compose r₁ r₂
  substitution-preserves-value σok TV-Receive₁ =
    _ , σok , TV-Receive₁ , residual-refl σok
  substitution-preserves-value σok TV-Receive₂ =
    _ , σok , TV-Receive₂ , residual-refl σok
  substitution-preserves-value σok TV-Send₁ =
    _ , σok , TV-Send₁ , residual-refl σok
  substitution-preserves-value σok TV-Send₂ =
    _ , σok , TV-Send₂ , residual-refl σok
  substitution-preserves-value σok TV-Select₁ =
    _ , σok , TV-Select₁ , residual-refl σok
  substitution-preserves-value σok TV-Select₂ =
    _ , σok , TV-Select₂ , residual-refl σok

  substitution-preserves-linear-body :
    ∀ {Δ n m pkT pkU mult}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pkT Lin)}
      {U : NfTy Δ (KV pkU mult)}
      {e : Expr Δ (Data.Nat.suc n)}
    → (σok : Γt ⊢σ σ ∶ Γs ⊣ Γo)
    → (T ∷ˡ Γs) ⊢ e ⇒ U ⊣ (B-Used T ▻ Γs′)
    → Σ (Ctx Δ m) λ Γt′ →
        Σ (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo) λ σok′ →
          ((T ∷ˡ Γt) ⊢ substExprWith (extSub σ) e ⇒ U
            ⊣ (B-Used T ▻ Γt′))
          × Residual σok σok′
  substitution-preserves-linear-body σok body
    with substitution-preserves-synth
           (extend-substitution-linear σok)
           body
  ... | _ , S-Used (S-TargetUsed σok′) , body′ ,
        RS-LinUsed (RS-TargetUsed r) =
    _ , σok′ , body′ , r

  substitution-preserves-linear-body-aligned :
    ∀ {Δ n m pkT pkU mult}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γt′ Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pkT Lin)}
      {U : NfTy Δ (KV pkU mult)}
      {e : Expr Δ (Data.Nat.suc n)}
      (σok : Γt ⊢σ σ ∶ Γs ⊣ Γo)
      (σok′ : Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)
    → Residual σok σok′
    → (T ∷ˡ Γs) ⊢ e ⇒ U ⊣ (B-Used T ▻ Γs′)
    → (T ∷ˡ Γt) ⊢ substExprWith (extSub σ) e ⇒ U
        ⊣ (B-Used T ▻ Γt′)
  substitution-preserves-linear-body-aligned
      σok σok′ rtarget body
    with substitution-preserves-linear-body σok body
  ... | Γti , σoki , body′ , ri
    with residual-target-unique ri rtarget
  ... | refl = body′

  substitution-preserves-synth :
    ∀ {Δ n m pk mult}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk mult)}
    → (σok : Γt ⊢σ σ ∶ Γs ⊣ Γo)
    → Γs ⊢ e ⇒ T ⊣ Γs′
    → Σ (Ctx Δ m) λ Γt′ →
        Σ (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo) λ σok′ →
          (Γt ⊢ substExprWith σ e ⇒ T ⊣ Γt′)
          × Residual σok σok′
  substitution-preserves-synth σok (T-Val d)
    with substitution-preserves-value σok d
  ... | Γt′ , σok′ , d′ , r =
    Γt′ , σok′ , T-Val d′ , r
  substitution-preserves-synth σok (T-Pair d₁ d₂)
    with substitution-preserves-synth σok d₁
  ... | Γt₂ , σok₂ , d₁′ , r₁
    with substitution-preserves-synth σok₂ d₂
  ... | Γt₃ , σok₃ , d₂′ , r₂ =
    Γt₃ , σok₃ , T-Pair d₁′ d₂′ , residual-compose r₁ r₂
  substitution-preserves-synth σok (T-App d₁ d₂)
    with substitution-preserves-synth σok d₁
  ... | Γt₂ , σok₂ , d₁′ , r₁
    with substitution-preserves-check σok₂ d₂
  ... | Γt₃ , σok₃ , d₂′ , r₂ =
    Γt₃ , σok₃ , T-App d₁′ d₂′ , residual-compose r₁ r₂
  substitution-preserves-synth σok (T-LetUnit d₁ d₂)
    with substitution-preserves-check σok d₁
  ... | Γt₂ , σok₂ , d₁′ , r₁
    with substitution-preserves-synth σok₂ d₂
  ... | Γt₃ , σok₃ , d₂′ , r₂ =
    Γt₃ , σok₃ , T-LetUnit d₁′ d₂′ , residual-compose r₁ r₂
  substitution-preserves-synth σok (T-LetPair d₁ d₂)
    with substitution-preserves-synth σok d₁
  ... | Γt₂ , σok₂ , d₁′ , r₁
    with substitution-preserves-synth
           (extend-substitution-linear2 σok₂)
           d₂
  ... | _ ,
        S-Used (S-TargetUsed (S-Used (S-TargetUsed σok₃))) ,
        d₂′ ,
        RS-LinUsed
          (RS-TargetUsed
            (RS-LinUsed
              (RS-TargetUsed r₂))) =
    _ , σok₃ , T-LetPair d₁′ d₂′ , residual-compose r₁ r₂
  substitution-preserves-synth
      {σ = σ}
      σok
      (T-Match
        {ss = ss}
        {ssbranches = ssbranches}
        {incl = incl}
        {ne = ne}
        d bs j)
    with substitution-preserves-synth σok d
  ... | Γt₂ , σok₂ , d′ , r₁
    with substitution-preserves-linear-body
           σok₂
           (bs (proj₁ ne) (proj₂ ne))
  ... | Γt₃ , σok₃ , anchor′ , r₂ =
    Γt₃ ,
    σok₃ ,
    T-Match
      {ss = ss}
      {ssbranches = ssbranches}
      {incl = incl}
      d′
      (λ i i∈ →
        substitution-preserves-linear-body-aligned
          σok₂ σok₃ r₂ (bs i i∈))
      j ,
    residual-compose r₁ r₂
  substitution-preserves-synth σok (T-TApp d)
    with substitution-preserves-synth σok d
  ... | Γt′ , σok′ , d′ , r =
    Γt′ , σok′ , T-TApp d′ , r

  substitution-preserves-check :
    ∀ {Δ n m pk mult}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk mult)}
    → (σok : Γt ⊢σ σ ∶ Γs ⊣ Γo)
    → Γs ⊢ e ⇐ T ⊣ Γs′
    → Σ (Ctx Δ m) λ Γt′ →
        Σ (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo) λ σok′ →
          (Γt ⊢ substExprWith σ e ⇐ T ⊣ Γt′)
          × Residual σok σok′
  substitution-preserves-check σok (T-Check d sub)
    with substitution-preserves-synth σok d
  ... | Γt′ , σok′ , d′ , r =
    Γt′ , σok′ , T-Check d′ sub , r

-- The corrected result shape for expression substitution.  The derivation
-- records its actual leftover; clients receive only the weaker guarantee
-- that it agrees with the expected leftover up to used annotations.

record SynthResult
    {Δ : List Kind}
    {n : ℕ}
    {pk : PreKind}
    {m : Multiplicity}
    (Γin : Ctx Δ n)
    (e : Expr Δ n)
    (T : NfTy Δ (KV pk m))
    (Γexpected : Ctx Δ n) : Set where
  field
    actualType : NfTy Δ (KV pk m)
    Γactual : Ctx Δ n
    derivation : Γin ⊢ e ⇒ actualType ⊣ Γactual
    type-preservation : actualType <:ₜ T
    leftover : Γactual ≈ᵘ Γexpected

record CheckResult
    {Δ : List Kind}
    {n : ℕ}
    {pk : PreKind}
    {m : Multiplicity}
    (Γin : Ctx Δ n)
    (e : Expr Δ n)
    (T : NfTy Δ (KV pk m))
    (Γexpected : Ctx Δ n) : Set where
  field
    Γactual : Ctx Δ n
    derivation : Γin ⊢ e ⇐ T ⊣ Γactual
    leftover : Γactual ≈ᵘ Γexpected

record BinderStrengtheningResult
    {Δ : List Kind}
    {n : ℕ}
    {pkT pkU : PreKind}
    {mU : Multiplicity}
    (Γin : Ctx Δ n)
    (e : Expr Δ (Data.Nat.suc n))
    (Tactual : NfTy Δ (KV pkT Lin))
    (Uexpected : NfTy Δ (KV pkU mU))
    (Γout : Ctx Δ n) : Set where
  field
    actualType : NfTy Δ (KV pkU mU)
    derivation :
      (Tactual ∷ˡ Γin) ⊢ e ⇒ actualType
        ⊣ (B-Used Tactual ▻ Γout)
    type-preservation :
      actualType <:ₜ Uexpected

ExpressionBinderStrengthening : Set
ExpressionBinderStrengthening =
  ∀ {Δ n pkT pkU mU}
    {Γ₁ Γ₂ : Ctx Δ n}
    {T V : NfTy Δ (KV pkT Lin)}
    {U : NfTy Δ (KV pkU mU)}
    {e : Expr Δ (Data.Nat.suc n)}
  → V <:ₜ T
  → (T ∷ˡ Γ₁) ⊢ e ⇒ U ⊣ (B-Used T ▻ Γ₂)
  → BinderStrengtheningResult Γ₁ e V U Γ₂

strengthen-substitution-binder : ExpressionBinderStrengthening
strengthen-substitution-binder {V = V} sub body
  with strengthen-synth (<:-sub-lin sub <:Γ-refl) body
... | U′ , Γout′ , body′ , U′<:U , relout
  with used-tail-<:Γ relout
... | W , Γ₂′ , eqout , reltail
  with subst
         (λ Γ → (V ∷ˡ _) ⊢ _ ⇒ U′ ⊣ Γ)
         eqout
         body′
... | body″
  with lin-used-head-rigid body″
... | refl
  with coherent-strengthened-output
         (drop-lin-used (synth-preserves-~Ctx body″))
         (drop-lin-used (synth-preserves-~Ctx body))
         reltail
         <:Γ-refl
... | refl =
  record
    { actualType = U′
    ; derivation = body″
    ; type-preservation = U′<:U
    }

substitution-variable-base :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ : Ctx Δ n}
    {T : NfTy Δ (KV pk Lin)}
    {v : Value Δ n}
  → Γ₁ ⊢ E-Val v ⇐ T ⊣ Γ₂
  → SynthResult
      Γ₁
      (substExpr (E-Val (V-Var zero)) v)
      T
      Γ₂
substitution-variable-base (T-Check (T-Val dv) sub) =
  record
    { actualType = _
    ; Γactual = _
    ; derivation = T-Val dv
    ; type-preservation = sub
    ; leftover = ≈ᵘ-refl
    }

-- The option-1 result records the actual leftover up to used annotations.
-- The former statement demanded Γactual ≡ Γ₃ directly.

ExpressionSubstitutionPreservesTyping : Set
ExpressionSubstitutionPreservesTyping =
  ∀ {Δ n pkT pkU mU}
    {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
    {T : NfTy Δ (KV pkT Lin)}
    {U : NfTy Δ (KV pkU mU)}
    {v : Value Δ n}
    {e : Expr Δ (Data.Nat.suc n)}
  → Γ₂ ⊢ E-Val v ⇐ T ⊣ Γ₃
  → (T ∷ˡ Γ₁) ⊢ e ⇒ U ⊣ (B-Used T ▻ Γ₂)
  → SynthResult Γ₁ (substExpr e v) U Γ₃

ExactExpressionSubstitutionPreservesTyping : Set
ExactExpressionSubstitutionPreservesTyping =
  ∀ {Δ n pkT pkU mU}
    {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
    {T : NfTy Δ (KV pkT Lin)}
    {U : NfTy Δ (KV pkU mU)}
    {v : Value Δ n}
    {e : Expr Δ (Data.Nat.suc n)}
  → Γ₂ ⊢ᵥ v ⇒ T ⊣ Γ₃
  → (T ∷ˡ Γ₁) ⊢ e ⇒ U ⊣ (B-Used T ▻ Γ₂)
  → Γ₁ ⊢ substExpr e v ⇒ U ⊣ Γ₃

exact-expression-substitution-preserves-typing :
  ExactExpressionSubstitutionPreservesTyping
exact-expression-substitution-preserves-typing dv body
  with strip-synth body
... | Gbody , Gout , rbody , body′ , au
  with ECP.strip-rm-lin rbody
... | G , refl , rm
  with substitution-preserves-synth
         (single-substitution-relation dv rm)
         body′
... | Γactual , σfinal , result , r
  with allUsed-substitution-target au σfinal
... | refl = result

expression-substitution-from-exact :
  ExpressionBinderStrengthening
  →
  ExactExpressionSubstitutionPreservesTyping
  → ExpressionSubstitutionPreservesTyping
expression-substitution-from-exact strengthen exact
    (T-Check (T-Val dv) sub) body
  with strengthen sub body
... | record
        { actualType = U′
        ; derivation = body′
        ; type-preservation = U′<:U
        } =
  record
    { actualType = U′
    ; Γactual = _
    ; derivation = exact dv body′
    ; type-preservation = U′<:U
    ; leftover = ≈ᵘ-refl
    }

expression-substitution-from-exact-trusted :
  ExactExpressionSubstitutionPreservesTyping
  → ExpressionSubstitutionPreservesTyping
expression-substitution-from-exact-trusted =
  expression-substitution-from-exact strengthen-substitution-binder

expression-substitution-preserves-typing :
  ExpressionSubstitutionPreservesTyping
expression-substitution-preserves-typing =
  expression-substitution-from-exact-trusted
    exact-expression-substitution-preserves-typing

shape-allUsed-frame :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
  → Γ₁ ~Ctx Γ₂
  → FrameCtx Γ₂ (ECP.allUsedCtx Γ₁) Γ₂
shape-allUsed-frame ∅~∅ = FC-∅
shape-allUsed-frame (Lin~Lin shape) =
  FC-frame (shape-allUsed-frame shape)
shape-allUsed-frame (Lin~Used shape) =
  FC-allused (shape-allUsed-frame shape)
shape-allUsed-frame (Un~Un shape) =
  FC-un (shape-allUsed-frame shape)
shape-allUsed-frame (Used~Used shape) =
  FC-allused (shape-allUsed-frame shape)

identity-shape-advance :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
    (shape : Γ₁ ~Ctx Γ₂)
  → Σ (Γ₂ ⊢σ identitySub ∶ Γ₂ ⊣ ECP.allUsedCtx Γ₁) λ final →
      Residual
        (identity-substitution-canonical (merge-right-allUsed Γ₁))
        final
identity-shape-advance ∅~∅ = S-∅ , RS-∅
identity-shape-advance
    {Γ₁ = B-Lin T ▻ Γ₁}
    (Lin~Lin shape)
  with identity-shape-advance shape
... | final , residual =
  S-Lin
    (FC-live (shape-allUsed-frame shape))
    (TV-Var-Lin take-here)
    (ECP.AU-used (ECP.allUsedCtx-AllUsed Γ₁))
    (S-TargetUsed final)
  , RS-LinLive (RS-TargetUsed residual)
identity-shape-advance (Lin~Used shape)
  with identity-shape-advance shape
... | final , residual =
  S-Used (S-TargetUsed final)
  , RS-LinUsed (RS-TargetUsed residual)
identity-shape-advance (Un~Un shape)
  with identity-shape-advance shape
... | final , residual =
  S-Un (TV-Var-Un hereᵘ) (S-TargetUn final)
  , RS-Un (RS-TargetUn residual)
identity-shape-advance (Used~Used shape)
  with identity-shape-advance shape
... | final , residual =
  S-Used (S-TargetUsed final)
  , RS-Used (RS-TargetUsed residual)

variable-substitution-preserves-synth :
  ∀ {Δ n pkᵀ pkᵁ mᵁ}
    {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pkᵀ Lin)}
    {U : NfTy Δ (KV pkᵁ mᵁ)}
    {e : Expr Δ (Data.Nat.suc n)}
  → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂
  → (T ∷ˡ Γ₂) ⊢ e ⇒ U ⊣ (B-Used T ▻ Γ₃)
  → Γ₁ ⊢ substExpr e (V-Var x) ⇒ U ⊣ Γ₃
variable-substitution-preserves-synth
    {Δ = Δ} {pkᵁ = pkᵁ} {mᵁ = mᵁ}
    {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} {x = x}
    {T = T} {U = U} {e = e}
    take body
  with strip-value (TV-Var-Lin take)
... | G , G′ , rm , dv , au
  with identity-shape-advance
         (drop-lin-used (synth-preserves-~Ctx body))
... | tailFinal , tailResidual
  with substitution-preserves-synth
         (S-Lin {σ = singleSub (V-Var x)}
           (swapFrameCtx (remove-to-frame rm))
           dv
           au
           (identity-substitution-canonical
             (merge-right-allUsed Γ₂)))
         body
... | Γactual , actual , result , residual
  rewrite residual-target-unique residual
            (RS-LinUsed tailResidual) = result
