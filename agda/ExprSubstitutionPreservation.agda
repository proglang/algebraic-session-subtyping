module ExprSubstitutionPreservation where

open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Subset as Subset
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using () renaming (here to hereₗ; there to thereₗ)
open import Data.Vec using (here; there) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Kinds
open import Kits
open import Ext using (ext)
open import Types using (Ty; Ty-Syntax; Ty-Traversal; T-Base; T-Arrow; T-Sub; T-End; T-Up) renaming (fusion to tyFusion)
open import Variance using (Variance)
open import AlgorithmicNFSubtyping using (_<:ₜ_)
open import ExprSyntax using
  ( Expr
  ; Value
  ; E-Val
  ; E-App
  ; E-TApp
  ; E-LetUnit
  ; E-Pair
  ; E-LetPair
  ; E-Match
  ; V-Const
  ; V-Var
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
  )
open import ExprSubstitution using
  ( Sub
  ; extSub
  ; extSub2
  ; liftTySub
  ; wkValue
  ; wkTyValue
  ; renTyValue
  ; renTyExpr
  ; substTyValueWith
  ; substTyExprWith
  ; substTyValue
  ; substTyExpr
  ; substValueWith
  ; substExprWith
  )
open import ExprNormalTyping
import NormalTypes as NT using (N-Arrow)
open import NormalTypesSubstitution using (wkNFKind-sound)
open import ExprSubstitutionTyping using
  ( substTyNfWith
  ; substTyCtxWith
  ; substTyNf
  ; substTyBinding
  ; substTyCtx
  ; substTyWith-preserves-value
  ; substTy-preserves-value
  )
open import ExprRenamingPreservation as Ren using (wk-preserves-value; unwk-preserves-value)
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
    ; allUsedCtx-AllUsed
    ; FrameCtx
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
    ; FC-live
    ; FC-un
    ; wkFrameCtx
    ; frame-value
    ; replay-value
    ; replay-value-allUsed
    )
open import ExprTypingLeftover
  using
    ( leftover-synth
    ; leftover-check
    ; leftover-value
    ; strip-lin-used
    )
open import ExprTypingInversion
  using
    ( rec-inversion
    ; tv-receive₁-inversion
    ; tv-receive₂-inversion
    ; tv-send₁-inversion
    ; tv-send₂-inversion
    ; tv-select₁-inversion
    ; tv-select₂-inversion
    )
open import ExprContextShape using (value-preserves-~Ctx; ~Ctx-allUsedCtx)

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal
open CTraversal record { fusion = tyFusion }


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
  ∀ {Δ n pk m}
    {Γin Γo₁ Γo₂ : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk m)}
  → Γin ⊢ e ⇒ T ⊣ Γo₁
  → Γo₁ ≡ Γo₂
  → Γin ⊢ e ⇒ T ⊣ Γo₂
cast-synth-out d eq = subst (λ X → _ ⊢ _ ⇒ _ ⊣ X) eq d

branchjoin⁺-nonempty :
  ∀ {Δ k pk m}
    {ss : Subset.Subset k}
    {V : (i : Fin k) → i Subset.∈ ss → NfTy Δ (KV pk m)}
    {U : NfTy Δ (KV pk m)}
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

postulate
  receive₁-input-unique :
    ∀ {Δ n pk₁ m₁ pk₂ m₂}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {T : Ty Δ TLin}
      {W₁ : NfTy Δ (KV pk₁ m₁)}
      {W₂ : NfTy Δ (KV pk₂ m₂)}
    → Γ₁ ⊢ᵥ V-Receive₁ T ⇒ W₁ ⊣ Γo
    → Γ₂ ⊢ᵥ V-Receive₁ T ⇒ W₂ ⊣ Γo
    → Γ₁ ≡ Γ₂

  receive₂-input-unique :
    ∀ {Δ n pk₁ m₁ pk₂ m₂}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {T : Ty Δ TLin}
      {S : Ty Δ SLin}
      {W₁ : NfTy Δ (KV pk₁ m₁)}
      {W₂ : NfTy Δ (KV pk₂ m₂)}
    → Γ₁ ⊢ᵥ V-Receive₂ T S ⇒ W₁ ⊣ Γo
    → Γ₂ ⊢ᵥ V-Receive₂ T S ⇒ W₂ ⊣ Γo
    → Γ₁ ≡ Γ₂

  send₁-input-unique :
    ∀ {Δ n pk₁ m₁ pk₂ m₂}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {T : Ty Δ TLin}
      {W₁ : NfTy Δ (KV pk₁ m₁)}
      {W₂ : NfTy Δ (KV pk₂ m₂)}
    → Γ₁ ⊢ᵥ V-Send₁ T ⇒ W₁ ⊣ Γo
    → Γ₂ ⊢ᵥ V-Send₁ T ⇒ W₂ ⊣ Γo
    → Γ₁ ≡ Γ₂

  send₂-input-unique :
    ∀ {Δ n pk₁ m₁ pk₂ m₂}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {T : Ty Δ TLin}
      {S : Ty Δ SLin}
      {W₁ : NfTy Δ (KV pk₁ m₁)}
      {W₂ : NfTy Δ (KV pk₂ m₂)}
    → Γ₁ ⊢ᵥ V-Send₂ T S ⇒ W₁ ⊣ Γo
    → Γ₂ ⊢ᵥ V-Send₂ T S ⇒ W₂ ⊣ Γo
    → Γ₁ ≡ Γ₂

  select₁-input-unique :
    ∀ {Δ n k pk₁ m₁ pk₂ m₂}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {v : Variance}
      {i : Fin k}
      {P : Ty Δ KP}
      {W₁ : NfTy Δ (KV pk₁ m₁)}
      {W₂ : NfTy Δ (KV pk₂ m₂)}
    → Γ₁ ⊢ᵥ V-Select₁ v i P ⇒ W₁ ⊣ Γo
    → Γ₂ ⊢ᵥ V-Select₁ v i P ⇒ W₂ ⊣ Γo
    → Γ₁ ≡ Γ₂

  select₂-input-unique :
    ∀ {Δ n k pk₁ m₁ pk₂ m₂}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {v : Variance}
      {i : Fin k}
      {P : Ty Δ KP}
      {S : Ty Δ SLin}
      {W₁ : NfTy Δ (KV pk₁ m₁)}
      {W₂ : NfTy Δ (KV pk₂ m₂)}
    → Γ₁ ⊢ᵥ V-Select₂ v i P S ⇒ W₁ ⊣ Γo
    → Γ₂ ⊢ᵥ V-Select₂ v i P S ⇒ W₂ ⊣ Γo
    → Γ₁ ≡ Γ₂

mutual

  synth-input-unique′ :
    ∀ {Δ n pk₁ m₁ pk₂ m₂}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {e : Expr Δ n}
      {T₁ : NfTy Δ (KV pk₁ m₁)}
      {T₂ : NfTy Δ (KV pk₂ m₂)}
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
    ∀ {Δ n pk₁ m₁ pk₂ m₂}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {e : Expr Δ n}
      {T₁ : NfTy Δ (KV pk₁ m₁)}
      {T₂ : NfTy Δ (KV pk₂ m₂)}
    → Γ₁ ⊢ e ⇐ T₁ ⊣ Γo
    → Γ₂ ⊢ e ⇐ T₂ ⊣ Γo
    → Γ₁ ≡ Γ₂
  check-input-unique′ (T-Check d₁ _) (T-Check d₂ _) =
    synth-input-unique′ d₁ d₂

  postulate
    value-input-unique′ :
      ∀ {Δ n pk₁ m₁ pk₂ m₂}
        {Γ₁ Γ₂ Γo : Ctx Δ n}
        {v : Value Δ n}
        {T₁ : NfTy Δ (KV pk₁ m₁)}
        {T₂ : NfTy Δ (KV pk₂ m₂)}
      → Γ₁ ⊢ᵥ v ⇒ T₁ ⊣ Γo
      → Γ₂ ⊢ᵥ v ⇒ T₂ ⊣ Γo
      → Γ₁ ≡ Γ₂

  value-input-unique″ :
    ∀ {Δ n pk m}
      {Γ₁ Γ₂ Γo : Ctx Δ n}
      {v : Value Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γo
    → Γ₂ ⊢ᵥ v ⇒ T ⊣ Γo
    → Γ₁ ≡ Γ₂
  value-input-unique″ (TV-Const _) (TV-Const _) = refl
  value-input-unique″ (TV-Var-Lin take₁) (TV-Var-Lin take₂) =
    take-input-unique′ take₁ take₂
  value-input-unique″ (TV-Var-Un _) (TV-Var-Un _) = refl
  value-input-unique″ {T = NT.N-Arrow T₁ T₂} (TV-Abs d₁) d₂ = {!!}
  --   with synth-input-unique′ d₁ d₂
  -- ... | eq = ∷ˡ-injective eq
  value-input-unique″ (TV-Rec d₁) (TV-Rec d₂)
    with check-input-unique′ d₁ d₂
  ... | eq = ∷ᵘ-injective eq
  value-input-unique″ (TV-TAbs d₁) (TV-TAbs d₂) =
    wkCtx-injective (value-input-unique′ d₁ d₂)
  value-input-unique″ (TV-Pair d₁₁ d₁₂) (TV-Pair d₂₁ d₂₂)
    with value-input-unique″ d₁₂ d₂₂
  ... | eqmid rewrite eqmid =
    value-input-unique″ d₁₁ d₂₁
  value-input-unique″ TV-Receive₁ TV-Receive₁ = refl
  value-input-unique″ TV-Receive₂ TV-Receive₂ = refl
  value-input-unique″ TV-Send₁ TV-Send₁ = refl
  value-input-unique″ TV-Send₂ TV-Send₂ = refl
  value-input-unique″ TV-Select₁ TV-Select₁ = refl
  value-input-unique″ TV-Select₂ TV-Select₂ = refl

synth-input-unique :
  ∀ {Δ n pk m}
    {Γ₁ Γ₂ Γo : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk m)}
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
  ∀ {Δ n pk m}
    {Γ₁ Γ₂ Γo : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
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
    → FrameCtx Γrest Γv Γt
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
  ∀ {Δ n pk m}
    {Γ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
  → allUsedCtx Γ ⊢ᵥ v ⇒ T ⊣ allUsedCtx Γ
  → Γ ⊢ᵥ v ⇒ T ⊣ Γ
replay-allUsed-value {Γ = Γ} d =
  replay-value d (frame-allUsedCtx Γ) (frame-allUsedCtx Γ)

unwk-used-head-value :
  ∀ {Δ n pk m pk′}
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
    {U : NfTy Δ (KV pk′ Lin)}
  → (B-Used U ▻ Γ₁) ⊢ᵥ wkValue v ⇒ T ⊣ (B-Used U ▻ Γ₂)
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
unwk-used-head-value {U = U} d =
  Ren.unwk-preserves-value (B-Used U) d

renToSub : ∀ {Δ Δ′} → (Δ →ᵣ Δ′) → (Δ →ₛ Δ′)
renToSub ρ = ρ ·ₖ idₛ

renTy-as-subst :
  ∀ {Δ Δ′ K} (ρ : Δ →ᵣ Δ′) (T : Ty Δ K)
  → T ⋯ ρ ≡ T ⋯ renToSub ρ
renTy-as-subst ρ T =
  trans
    (sym (⋯-id (T ⋯ ρ)))
    (fusion T ρ idₛ)

liftSub~ :
  ∀ {Δ Δ′ K} {ϕ ψ : Δ →ₛ Δ′}
  → ϕ ~ ψ
  → (ϕ ↑ₛ K) ~ (ψ ↑ₛ K)
liftSub~ {K = K} rel .K (hereₗ refl) = refl
liftSub~ {K = K} rel K′ (thereₗ x) =
  cong (λ t → t ⋯ weakenᵣ K) (rel K′ x)

renToSub-↑~ :
  ∀ {Δ Δ′ K} (ρ : Δ →ᵣ Δ′)
  → renToSub (ρ ↑ᵣ K) ~ (renToSub ρ ↑ₛ K)
renToSub-↑~ {K = K} ρ .K (hereₗ refl) = refl
renToSub-↑~ {K = K} ρ K′ (thereₗ x) =
  sym (⋯-var (ρ K′ x) (weakenᵣ K))

renToSub-weaken~ :
  ∀ {Δ K}
  → renToSub (weakenᵣ {S = Δ} K) ~ weakenₛ K
renToSub-weaken~ {K = K} K′ x =
  sym (⋯-var x (weakenᵣ K))

branch-ext :
  ∀ {Δ n k} {ss : Subset.Subset k}
    {f g : (i : Fin k) → i Subset.∈ ss → Expr Δ n}
  → (∀ i i∈ → f i i∈ ≡ g i i∈)
  → f ≡ g
branch-ext {Δ = Δ} {n = n} {k = k} {ss = ss} {f = f} {g = g} eq =
  cong curry
    (ext uncurry-f uncurry-g (λ where (i , i∈) → eq i i∈))
  where
  uncurry-f : Σ (Fin k) (λ i → i Subset.∈ ss) → Expr Δ n
  uncurry-f (i , i∈) = f i i∈

  uncurry-g : Σ (Fin k) (λ i → i Subset.∈ ss) → Expr Δ n
  uncurry-g (i , i∈) = g i i∈

  curry :
    (Σ (Fin k) (λ i → i Subset.∈ ss) → Expr Δ n)
    → (i : Fin k) → i Subset.∈ ss → Expr Δ n
  curry h i i∈ = h (i , i∈)

mutual

  substTyValueWith-cong :
    ∀ {Δ Δ′ n} {ϕ ψ : Δ →ₛ Δ′}
    → ϕ ~ ψ
    → (v : Value Δ n)
    → substTyValueWith ϕ v ≡ substTyValueWith ψ v
  substTyValueWith-cong rel (V-Const c) = refl
  substTyValueWith-cong rel (V-Var x) = refl
  substTyValueWith-cong rel (V-Abs T e)
    rewrite ⋯-cong T rel
          | substTyExprWith-cong rel e
    = refl
  substTyValueWith-cong rel (V-Rec T U v)
    rewrite ⋯-cong T rel
          | ⋯-cong U rel
          | substTyValueWith-cong rel v
    = refl
  substTyValueWith-cong rel (V-TAbs K v)
    rewrite substTyValueWith-cong (liftSub~ {K = K} rel) v
    = refl
  substTyValueWith-cong rel (V-Pair v₁ v₂)
    rewrite substTyValueWith-cong rel v₁
          | substTyValueWith-cong rel v₂
    = refl
  substTyValueWith-cong rel (V-Receive₁ T)
    rewrite ⋯-cong T rel
    = refl
  substTyValueWith-cong rel (V-Receive₂ T S)
    rewrite ⋯-cong T rel
          | ⋯-cong S rel
    = refl
  substTyValueWith-cong rel (V-Send₁ T)
    rewrite ⋯-cong T rel
    = refl
  substTyValueWith-cong rel (V-Send₂ T S)
    rewrite ⋯-cong T rel
          | ⋯-cong S rel
    = refl
  substTyValueWith-cong rel (V-Select₁ v i P)
    rewrite ⋯-cong P rel
    = refl
  substTyValueWith-cong rel (V-Select₂ v i P S)
    rewrite ⋯-cong P rel
          | ⋯-cong S rel
    = refl

  substTyExprWith-cong :
    ∀ {Δ Δ′ n} {ϕ ψ : Δ →ₛ Δ′}
    → ϕ ~ ψ
    → (e : Expr Δ n)
    → substTyExprWith ϕ e ≡ substTyExprWith ψ e
  substTyExprWith-cong rel (E-Val v)
    rewrite substTyValueWith-cong rel v
    = refl
  substTyExprWith-cong rel (E-App e₁ e₂)
    rewrite substTyExprWith-cong rel e₁
          | substTyExprWith-cong rel e₂
    = refl
  substTyExprWith-cong rel (E-TApp e T)
    rewrite substTyExprWith-cong rel e
          | ⋯-cong T rel
    = refl
  substTyExprWith-cong rel (E-LetUnit e₁ e₂)
    rewrite substTyExprWith-cong rel e₁
          | substTyExprWith-cong rel e₂
    = refl
  substTyExprWith-cong rel (E-Pair e₁ e₂)
    rewrite substTyExprWith-cong rel e₁
          | substTyExprWith-cong rel e₂
    = refl
  substTyExprWith-cong rel (E-LetPair e₁ e₂)
    rewrite substTyExprWith-cong rel e₁
          | substTyExprWith-cong rel e₂
    = refl
  substTyExprWith-cong rel (E-Match {ss = ss} e ne branches)
    rewrite substTyExprWith-cong rel e
          | branch-ext {ss = ss} (λ i i∈ → substTyExprWith-cong rel (branches i i∈))
    = refl

mutual

  renTyValue-as-subst :
    ∀ {Δ Δ′ n} (ρ : Δ →ᵣ Δ′) (v : Value Δ n)
    → renTyValue ρ v ≡ substTyValueWith (renToSub ρ) v
  renTyValue-as-subst ρ (V-Const c) = refl
  renTyValue-as-subst ρ (V-Var x) = refl
  renTyValue-as-subst ρ (V-Abs T e)
    rewrite renTy-as-subst ρ T
          | renTyExpr-as-subst ρ e
    = refl
  renTyValue-as-subst ρ (V-Rec T U v)
    rewrite renTy-as-subst ρ T
          | renTy-as-subst ρ U
          | renTyValue-as-subst ρ v
    = refl
  renTyValue-as-subst ρ (V-TAbs K v)
    rewrite renTyValue-as-subst (ρ ↑ᵣ K) v
          | substTyValueWith-cong (renToSub-↑~ ρ) v
    = refl
  renTyValue-as-subst ρ (V-Pair v₁ v₂)
    rewrite renTyValue-as-subst ρ v₁
          | renTyValue-as-subst ρ v₂
    = refl
  renTyValue-as-subst ρ (V-Receive₁ T)
    rewrite renTy-as-subst ρ T
    = refl
  renTyValue-as-subst ρ (V-Receive₂ T S)
    rewrite renTy-as-subst ρ T
          | renTy-as-subst ρ S
    = refl
  renTyValue-as-subst ρ (V-Send₁ T)
    rewrite renTy-as-subst ρ T
    = refl
  renTyValue-as-subst ρ (V-Send₂ T S)
    rewrite renTy-as-subst ρ T
          | renTy-as-subst ρ S
    = refl
  renTyValue-as-subst ρ (V-Select₁ v i P)
    rewrite renTy-as-subst ρ P
    = refl
  renTyValue-as-subst ρ (V-Select₂ v i P S)
    rewrite renTy-as-subst ρ P
          | renTy-as-subst ρ S
    = refl

  renTyExpr-as-subst :
    ∀ {Δ Δ′ n} (ρ : Δ →ᵣ Δ′) (e : Expr Δ n)
    → renTyExpr ρ e ≡ substTyExprWith (renToSub ρ) e
  renTyExpr-as-subst ρ (E-Val v)
    rewrite renTyValue-as-subst ρ v
    = refl
  renTyExpr-as-subst ρ (E-App e₁ e₂)
    rewrite renTyExpr-as-subst ρ e₁
          | renTyExpr-as-subst ρ e₂
    = refl
  renTyExpr-as-subst ρ (E-TApp e T)
    rewrite renTyExpr-as-subst ρ e
          | renTy-as-subst ρ T
    = refl
  renTyExpr-as-subst ρ (E-LetUnit e₁ e₂)
    rewrite renTyExpr-as-subst ρ e₁
          | renTyExpr-as-subst ρ e₂
    = refl
  renTyExpr-as-subst ρ (E-Pair e₁ e₂)
    rewrite renTyExpr-as-subst ρ e₁
          | renTyExpr-as-subst ρ e₂
    = refl
  renTyExpr-as-subst ρ (E-LetPair e₁ e₂)
    rewrite renTyExpr-as-subst ρ e₁
          | renTyExpr-as-subst ρ e₂
    = refl
  renTyExpr-as-subst ρ (E-Match {ss = ss} e ne branches)
    rewrite renTyExpr-as-subst ρ e
          | branch-ext {ss = ss} (λ i i∈ → renTyExpr-as-subst ρ (branches i i∈))
    = refl

substTyNfWith-weaken :
  ∀ {Δ K K′}
    (T : NfTy Δ K)
  → substTyNfWith T (weakenₛ K′) ≡ wkNfTy {K′ = K′} T
substTyNfWith-weaken {K′ = K′} T =
  trans
    (cong normalizeTy
      (sym (⋯-cong ⌞ T ⌟ (renToSub-weaken~ {K = K′}))))
    (trans
      (cong normalizeTy
        (trans
          (sym (renTy-as-subst (weakenᵣ K′) ⌞ T ⌟))
          (sym (wkNFKind-sound {K′ = K′} T))))
      (normalizeTy-id (wkNfTy {K′ = K′} T)))

substTyCtxWith-weaken :
  ∀ {Δ n K}
    (Γ : Ctx Δ n)
  → substTyCtxWith Γ (weakenₛ K) ≡ wkCtx {K = K} Γ
substTyCtxWith-weaken ∅ = refl
substTyCtxWith-weaken {K = K} (B-Lin T ▻ Γ)
  rewrite substTyNfWith-weaken {K′ = K} T
        | substTyCtxWith-weaken {K = K} Γ
  = refl
substTyCtxWith-weaken {K = K} (B-Un T ▻ Γ)
  rewrite substTyNfWith-weaken {K′ = K} T
        | substTyCtxWith-weaken {K = K} Γ
  = refl
substTyCtxWith-weaken {K = K} (B-Used T ▻ Γ)
  rewrite substTyNfWith-weaken {K′ = K} T
        | substTyCtxWith-weaken {K = K} Γ
  = refl

substTyValueWith-weaken :
  ∀ {Δ n K}
    (v : Value Δ n)
  → substTyValueWith (weakenₛ K) v ≡ wkTyValue {K = K} v
substTyValueWith-weaken {K = K} v =
  trans
    (sym (substTyValueWith-cong (renToSub-weaken~ {K = K}) v))
    (sym (renTyValue-as-subst (weakenᵣ K) v))

wkTy-preserves-value :
  ∀ {Δ n pk m K′}
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
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

liftTySub-empty-general :
  ∀ {Δ m K}
    (σ : Sub Δ 0 m)
  → liftTySub {Δ = Δ} {n = 0} {m = m} {K = K} σ ≡ (λ ())
liftTySub-empty-general σ = ext _ _ λ ()

emptySub-η :
  ∀ {Δ m}
  → (σ : Sub Δ 0 m)
  → σ ≡ (λ ())
emptySub-η σ = ext σ (λ ()) λ ()

sym~ :
  ∀ {Δ₁ Δ₂}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
  → ϕ ~ ψ
  → ψ ~ ϕ
sym~ rel K x = sym (rel K x)

trans~ :
  ∀ {Δ₁ Δ₂}
    {ϕ ψ χ : Δ₁ →ₛ Δ₂}
  → ϕ ~ ψ
  → ψ ~ χ
  → ϕ ~ χ
trans~ rel₁ rel₂ K x = trans (rel₁ K x) (rel₂ K x)

liftCancel~ :
  ∀ {Δ₁ Δ₂ K}
    {ρ : Δ₁ →ᵣ Δ₂}
    {ϕ : Δ₂ →ₛ Δ₁}
  → (ρ ·ₖ ϕ) ~ idₛ
  → ((ρ ↑ᵣ K) ·ₖ (ϕ ↑ₛ K)) ~ idₛ
liftCancel~ {K = K} {ρ = ρ} {ϕ = ϕ} rel =
  trans~
    (sym~ (dist-↑-· K ρ ϕ))
    (trans~ (liftSub~ {K = K} rel) id↑~id)

cancelTy :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (ϕ : Δ₂ →ₛ Δ₁)
  → (ρ ·ₖ ϕ) ~ idₛ
  → (T : Ty Δ₁ K)
  → (T ⋯ ρ) ⋯ ϕ ≡ T
cancelTy ρ ϕ rel T =
  trans
    (fusion T ρ ϕ)
    (⋯-id~ T rel)

mutual

  cancel-ren-sub-value :
    ∀ {Δ₁ Δ₂ n}
      (ρ : Δ₁ →ᵣ Δ₂)
      (ϕ : Δ₂ →ₛ Δ₁)
    → (ρ ·ₖ ϕ) ~ idₛ
    → (v : Value Δ₁ n)
    → substTyValueWith ϕ (renTyValue ρ v) ≡ v

  cancel-ren-sub-expr :
    ∀ {Δ₁ Δ₂ n}
      (ρ : Δ₁ →ᵣ Δ₂)
      (ϕ : Δ₂ →ₛ Δ₁)
    → (ρ ·ₖ ϕ) ~ idₛ
    → (e : Expr Δ₁ n)
    → substTyExprWith ϕ (renTyExpr ρ e) ≡ e

  cancel-ren-sub-value ρ ϕ rel (V-Const c) = refl
  cancel-ren-sub-value ρ ϕ rel (V-Var x) = refl
  cancel-ren-sub-value ρ ϕ rel (V-Abs T e)
    rewrite cancelTy ρ ϕ rel T
          | cancel-ren-sub-expr ρ ϕ rel e
    = refl
  cancel-ren-sub-value ρ ϕ rel (V-Rec T U v)
    rewrite cancelTy ρ ϕ rel T
          | cancelTy ρ ϕ rel U
          | cancel-ren-sub-value ρ ϕ rel v
    = refl
  cancel-ren-sub-value ρ ϕ rel (V-TAbs K v)
    rewrite cancel-ren-sub-value (ρ ↑ᵣ K) (ϕ ↑ₛ K) (liftCancel~ {K = K} {ρ = ρ} {ϕ = ϕ} rel) v
    = refl
  cancel-ren-sub-value ρ ϕ rel (V-Pair v₁ v₂)
    rewrite cancel-ren-sub-value ρ ϕ rel v₁
          | cancel-ren-sub-value ρ ϕ rel v₂
    = refl
  cancel-ren-sub-value ρ ϕ rel (V-Receive₁ T)
    rewrite cancelTy ρ ϕ rel T
    = refl
  cancel-ren-sub-value ρ ϕ rel (V-Receive₂ T S)
    rewrite cancelTy ρ ϕ rel T
          | cancelTy ρ ϕ rel S
    = refl
  cancel-ren-sub-value ρ ϕ rel (V-Send₁ T)
    rewrite cancelTy ρ ϕ rel T
    = refl
  cancel-ren-sub-value ρ ϕ rel (V-Send₂ T S)
    rewrite cancelTy ρ ϕ rel T
          | cancelTy ρ ϕ rel S
    = refl
  cancel-ren-sub-value ρ ϕ rel (V-Select₁ vv i P)
    rewrite cancelTy ρ ϕ rel P
    = refl
  cancel-ren-sub-value ρ ϕ rel (V-Select₂ vv i P S)
    rewrite cancelTy ρ ϕ rel P
          | cancelTy ρ ϕ rel S
    = refl

  cancel-ren-sub-expr ρ ϕ rel (E-Val v)
    rewrite cancel-ren-sub-value ρ ϕ rel v
    = refl
  cancel-ren-sub-expr ρ ϕ rel (E-App e₁ e₂)
    rewrite cancel-ren-sub-expr ρ ϕ rel e₁
          | cancel-ren-sub-expr ρ ϕ rel e₂
    = refl
  cancel-ren-sub-expr ρ ϕ rel (E-TApp e T)
    rewrite cancel-ren-sub-expr ρ ϕ rel e
          | cancelTy ρ ϕ rel T
    = refl
  cancel-ren-sub-expr ρ ϕ rel (E-LetUnit e₁ e₂)
    rewrite cancel-ren-sub-expr ρ ϕ rel e₁
          | cancel-ren-sub-expr ρ ϕ rel e₂
    = refl
  cancel-ren-sub-expr ρ ϕ rel (E-Pair e₁ e₂)
    rewrite cancel-ren-sub-expr ρ ϕ rel e₁
          | cancel-ren-sub-expr ρ ϕ rel e₂
    = refl
  cancel-ren-sub-expr ρ ϕ rel (E-LetPair e₁ e₂)
    rewrite cancel-ren-sub-expr ρ ϕ rel e₁
          | cancel-ren-sub-expr ρ ϕ rel e₂
    = refl
  cancel-ren-sub-expr ρ ϕ rel (E-Match {ss = ss} e ne branches)
    rewrite cancel-ren-sub-expr ρ ϕ rel e
          | branch-ext {ss = ss} (λ i i∈ → cancel-ren-sub-expr ρ ϕ rel (branches i i∈))
    = refl

inhabitTy : ∀ {Δ K} → Ty Δ K
inhabitTy {K = KP} = T-Up T-End
inhabitTy {K = KV KS Un} = T-End
inhabitTy {K = KV KS Lin} = T-Sub (≤k-step ≤p-refl ≤m-unl) T-End
inhabitTy {K = KV KT Un} = T-Arrow T-Base T-Base
inhabitTy {K = KV KT Lin} = T-Base

substTy-wkNfTy-id :
  ∀ {Δ K K′}
    (T : NfTy Δ K)
    (U : Ty Δ K′)
  → substTyNf (wkNfTy {K′ = K′} T) U ≡ T
substTy-wkNfTy-id {K′ = K′} T U =
  trans
    (cong (λ X → normalizeTy (X ⋯ ⦅ U ⦆ₛ)) (wkNFKind-sound {K′ = K′} T))
    (trans
      (cong normalizeTy (wk-cancels-⦅⦆-⋯ (⌞ T ⌟) U))
      (normalizeTy-id T))

substTy-wkBinding-id :
  ∀ {Δ K}
    (b : Binding Δ)
    (U : Ty Δ K)
  → substTyBinding (wkBinding {K = K} b) U ≡ b
substTy-wkBinding-id (B-Lin T) U = cong B-Lin (substTy-wkNfTy-id T U)
substTy-wkBinding-id (B-Un T) U = cong B-Un (substTy-wkNfTy-id T U)
substTy-wkBinding-id (B-Used T) U = cong B-Used (substTy-wkNfTy-id T U)

substTy-wkCtx-id :
  ∀ {Δ K n}
    (Γ : Ctx Δ n)
    (U : Ty Δ K)
  → substTyCtx (wkCtx {K = K} Γ) U ≡ Γ
substTy-wkCtx-id ∅ U = refl
substTy-wkCtx-id (b ▻ Γ) U =
  cong₂ (λ b′ Γ′ → b′ ▻ Γ′)
    (substTy-wkBinding-id b U)
    (substTy-wkCtx-id Γ U)

substTyCtx-allUsedCtx :
  ∀ {Δ n K}
    (Γ : Ctx (K ∷ Δ) n)
    (U : Ty Δ K)
  → substTyCtx (allUsedCtx Γ) U ≡ allUsedCtx (substTyCtx Γ U)
substTyCtx-allUsedCtx ∅ U = refl
substTyCtx-allUsedCtx (B-Lin T ▻ Γ) U =
  cong (B-Used _ ▻_) (substTyCtx-allUsedCtx Γ U)
substTyCtx-allUsedCtx (B-Un T ▻ Γ) U =
  cong (B-Un _ ▻_) (substTyCtx-allUsedCtx Γ U)
substTyCtx-allUsedCtx (B-Used T ▻ Γ) U =
  cong (B-Used _ ▻_) (substTyCtx-allUsedCtx Γ U)

substTy-wkAllUsedCtx-id :
  ∀ {Δ n K}
    (Γ : Ctx Δ n)
    (U : Ty Δ K)
  → substTyCtx (allUsedCtx (wkCtx {K = K} Γ)) U ≡ allUsedCtx Γ
substTy-wkAllUsedCtx-id {K = K} Γ U =
  trans
    (substTyCtx-allUsedCtx (wkCtx {K = K} Γ) U)
    (cong allUsedCtx (substTy-wkCtx-id Γ U))

substTy-wkTyValue-id :
  ∀ {Δ n K}
    (v : Value Δ n)
    (U : Ty Δ K)
  → substTyValue (wkTyValue {K = K} v) U ≡ v
substTy-wkTyValue-id {K = K} v U =
  cancel-ren-sub-value
    (weakenᵣ K)
    (⦅ U ⦆ₛ)
    (wk-cancels-⦅⦆ U)
    v

substTy-allUsed :
  ∀ {Δ n K}
    {Γ : Ctx (K ∷ Δ) n}
    (U : Ty Δ K)
  → AllUsed Γ
  → AllUsed (substTyCtx Γ U)
substTy-allUsed U AU-∅ = AU-∅
substTy-allUsed U (AU-used au) = AU-used (substTy-allUsed U au)
substTy-allUsed U (AU-un au) = AU-un (substTy-allUsed U au)

unwkAllUsed :
  ∀ {Δ n K}
    {Γ : Ctx Δ n}
  → AllUsed (wkCtx {K = K} Γ)
  → AllUsed Γ
unwkAllUsed {Γ = ∅} AU-∅ = AU-∅
unwkAllUsed {Γ = B-Lin _ ▻ _} ()
unwkAllUsed {Γ = B-Un _ ▻ _} (AU-un au) = AU-un (unwkAllUsed au)
unwkAllUsed {Γ = B-Used _ ▻ _} (AU-used au) = AU-used (unwkAllUsed au)

tailSub-liftTySub :
  ∀ {Δ n m K}
    (σ : Sub Δ (suc n) m)
  → tailSub (liftTySub {K = K} σ) ≡ liftTySub (tailSub σ)
tailSub-liftTySub σ = ext _ _ λ _ → refl

unwkMergeLeft :
  ∀ {Δ n K}
    {Γrest Γv Γt : Ctx (K ∷ Δ) n}
    {Γrest₀ : Ctx Δ n}
  → FrameCtx Γrest Γv Γt
  → Γrest ≡ wkCtx {K = K} Γrest₀
  → Σ (Ctx Δ n) λ Γv₀ →
      Σ (Ctx Δ n) λ Γt₀ →
        (Γv ≡ wkCtx Γv₀)
        × (Γt ≡ wkCtx Γt₀)
        × FrameCtx Γrest₀ Γv₀ Γt₀
unwkMergeLeft {Γrest₀ = ∅} FC-∅ refl = ∅ , ∅ , refl , refl , FC-∅
unwkMergeLeft {Γrest₀ = B-Used T₀ ▻ Γrest₀} (FC-allused m) refl
  with unwkMergeLeft {Γrest₀ = Γrest₀} m refl
... | Γv₀ , Γt₀ , eqv , eqt , m₀ =
  (B-Used _ ▻ Γv₀) , (B-Used _ ▻ Γt₀) ,
  cong (B-Used _ ▻_) eqv ,
  cong (B-Used _ ▻_) eqt ,
  FC-allused m₀
unwkMergeLeft {Γrest₀ = B-Used T₀ ▻ Γrest₀} (FC-live m) refl
  with unwkMergeLeft {Γrest₀ = Γrest₀} m refl
... | Γv₀ , Γt₀ , eqv , eqt , m₀ =
  (B-Lin _ ▻ Γv₀) , (B-Lin _ ▻ Γt₀) ,
  cong (B-Lin _ ▻_) eqv ,
  cong (B-Lin _ ▻_) eqt ,
  FC-live m₀
unwkMergeLeft {Γrest₀ = B-Lin T₀ ▻ Γrest₀} (FC-frame m) refl
  with unwkMergeLeft {Γrest₀ = Γrest₀} m refl
... | Γv₀ , Γt₀ , eqv , eqt , m₀ =
  (B-Used _ ▻ Γv₀) , (B-Lin _ ▻ Γt₀) ,
  cong (B-Used _ ▻_) eqv ,
  cong (B-Lin _ ▻_) eqt ,
  FC-frame m₀
unwkMergeLeft {Γrest₀ = B-Un T₀ ▻ Γrest₀} (FC-un m) refl
  with unwkMergeLeft {Γrest₀ = Γrest₀} m refl
... | Γv₀ , Γt₀ , eqv , eqt , m₀ =
  (B-Un _ ▻ Γv₀) , (B-Un _ ▻ Γt₀) ,
  cong (B-Un _ ▻_) eqv ,
  cong (B-Un _ ▻_) eqt ,
  FC-un m₀

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
liftTySub-preserves-σ {K = K} (S-Lin {T = T} m dv au σtail) =
  S-Lin
    (wkFrameCtx {K = K} m)
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

swapFrameCtx :
  ∀ {Δ n}
    {Γrest Γv Γt : Ctx Δ n}
  → FrameCtx Γrest Γv Γt
  → FrameCtx Γv Γrest Γt
swapFrameCtx FC-∅ = FC-∅
swapFrameCtx (FC-allused m) = FC-allused (swapFrameCtx m)
swapFrameCtx (FC-live m) = FC-frame (swapFrameCtx m)
swapFrameCtx (FC-frame m) = FC-live (swapFrameCtx m)
swapFrameCtx (FC-un m) = FC-un (swapFrameCtx m)

consume-lin-head-merge :
  ∀ {Δ n pk m}
    {Γrest Γv Γt Γv′ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
  → FrameCtx Γrest Γv Γt
  → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
  → AllUsed Γv′
  → Γt ⊢ᵥ v ⇒ T ⊣ Γrest
consume-lin-head-merge m dv au =
  replay-value-allUsed dv m au

lift-lin-through-merge :
  ∀ {Δ n pk m}
    {Γrest Γmid Γv Γt : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
  → FrameCtx Γrest Γv Γt
  → Γrest ⊢ᵥ v ⇒ T ⊣ Γmid
  → Σ (Ctx Δ n) λ Γtout →
      Σ (LinearDisjoint Γmid Γv) λ ld →
        FrameCtx Γmid Γv Γtout
        × (Γt ⊢ᵥ v ⇒ T ⊣ Γtout)
lift-lin-through-merge m d
  with frame-value d (swapFrameCtx m)
... | Γtout , f′ , d′ =
  Γtout , merge-disjoint mrg , mrg , d′
  where
  mrg : FrameCtx _ _ _
  mrg = swapFrameCtx f′

lift-un-through-merge :
  ∀ {Δ n pk}
    {Γrest Γv Γt : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk Un)}
  → FrameCtx Γrest Γv Γt
  → Γrest ⊢ᵥ v ⇒ T ⊣ Γrest
  → Γt ⊢ᵥ v ⇒ T ⊣ Γt
lift-un-through-merge m d =
  replay-value d (swapFrameCtx m) (swapFrameCtx m)

σ-target-unique :
  ∀ {Δ n m}
    {Γs : Ctx Δ n}
    {Γt₁ Γt₂ Γo : Ctx Δ m}
    {σ : Sub Δ n m}
  → Γt₁ ⊢σ σ ∶ Γs ⊣ Γo
  → Γt₂ ⊢σ σ ∶ Γs ⊣ Γo
  → Γt₁ ≡ Γt₂
σ-target-unique (S-∅ _) (S-∅ _) = refl
σ-target-unique
  (S-Lin {Γrest = Γrest₁} m₁ dv₁ au₁ σtail₁)
  (S-Lin {Γrest = Γrest₂} m₂ dv₂ au₂ σtail₂)
  with σ-target-unique σtail₁ σtail₂
... | refl =
  value-input-unique
    (consume-lin-head-merge m₁ dv₁ au₁)
    (consume-lin-head-merge m₂ dv₂ au₂)
σ-target-unique (S-Un _ σtail₁) (S-Un _ σtail₂) =
  σ-target-unique σtail₁ σtail₂
σ-target-unique (S-Used σtail₁) (S-Used σtail₂) =
  σ-target-unique σtail₁ σtail₂


merge-right-allUsed :
  ∀ {Δ n}
    (Γ : Ctx Δ n)
  → FrameCtx Γ (allUsedCtx Γ) Γ
merge-right-allUsed ∅ = FC-∅
merge-right-allUsed (B-Lin T ▻ Γ) = FC-frame (merge-right-allUsed Γ)
merge-right-allUsed (B-Un T ▻ Γ) = FC-un (merge-right-allUsed Γ)
merge-right-allUsed (B-Used T ▻ Γ) = FC-allused (merge-right-allUsed Γ)

tailSub-extSub-empty :
  ∀ {Δ m}
    (σ : Sub Δ 0 m)
  → tailSub (extSub σ) ≡ (λ ())
tailSub-extSub-empty σ = ext _ _ λ ()

mutual

  lift-tailSub-extSub-used :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Lin)}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → used∷ {T = T} Γt ⊢σ tailSub (extSub σ) ∶ Γs ⊣ used∷ {T = T} Γo

  lift-tailSub-extSub-un :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Un)}
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → (T ∷ᵘ Γt) ⊢σ tailSub (extSub σ) ∶ Γs ⊣ (T ∷ᵘ Γo)

  lift-tailSub-extSub-used {Γt = Γt} {T = T} (S-∅ au) =
    subst
      (λ τ → used∷ {T = T} Γt ⊢σ τ ∶ ∅ ⊣ used∷ {T = T} Γt)
      (sym (tailSub-extSub-empty (λ ())))
      (S-∅ (AU-used au))
  lift-tailSub-extSub-used {T = T} (S-Lin {T = U} m dv au σtail) =
    S-Lin
      (FC-allused m)
      (Ren.wk-preserves-value (B-Used T) dv)
      (AU-used au)
      (lift-tailSub-extSub-used {T = T} σtail)
  lift-tailSub-extSub-used {T = T} (S-Un {T = U} d0 σtail) =
    S-Un
      (Ren.wk-preserves-value (B-Used T) d0)
      (lift-tailSub-extSub-used {T = T} σtail)
  lift-tailSub-extSub-used {T = T} (S-Used {T = U} σtail) =
    S-Used (lift-tailSub-extSub-used {T = T} σtail)

  lift-tailSub-extSub-un {Γt = Γt} {T = T} (S-∅ au) =
    subst
      (λ τ → (T ∷ᵘ Γt) ⊢σ τ ∶ ∅ ⊣ (T ∷ᵘ Γt))
      (sym (tailSub-extSub-empty (λ ())))
      (S-∅ (AU-un au))
  lift-tailSub-extSub-un {T = T} (S-Lin {T = U} m dv au σtail) =
    S-Lin
      (FC-un m)
      (Ren.wk-preserves-value (B-Un T) dv)
      (AU-un au)
      (lift-tailSub-extSub-un {T = T} σtail)
  lift-tailSub-extSub-un {T = T} (S-Un {T = U} d0 σtail) =
    S-Un
      (Ren.wk-preserves-value (B-Un T) d0)
      (lift-tailSub-extSub-un {T = T} σtail)
  lift-tailSub-extSub-un {T = T} (S-Used {T = U} σtail) =
    S-Used (lift-tailSub-extSub-un {T = T} σtail)

extSub-preserves-σ-lin :
  ∀ {Δ n m pk}
    {Γs : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {T : NfTy Δ (KV pk Lin)}
  → Γt ⊢σ σ ∶ Γs ⊣ Γo
  → (T ∷ˡ Γt) ⊢σ extSub σ ∶ (T ∷ˡ Γs) ⊣ used∷ {T = T} Γo
extSub-preserves-σ-lin {Γt = Γt} {T = T} σok =
  S-Lin
    (FC-live (merge-right-allUsed Γt))
    (TV-Var-Lin take-here)
    (AU-used (allUsedCtx-AllUsed Γt))
    (lift-tailSub-extSub-used {T = T} σok)

extSub-preserves-σ-un :
  ∀ {Δ n m pk}
    {Γs : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {T : NfTy Δ (KV pk Un)}
  → Γt ⊢σ σ ∶ Γs ⊣ Γo
  → (T ∷ᵘ Γt) ⊢σ extSub σ ∶ (T ∷ᵘ Γs) ⊣ (T ∷ᵘ Γo)
extSub-preserves-σ-un {T = T} σok =
  S-Un
    (TV-Var-Un hereᵘ)
    (lift-tailSub-extSub-un {T = T} σok)

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
unliftTySub-preserves-σ {K = K} {Γs = ∅} {Γtwk = Γtwk} {Γo = Γo} {σ = σ} d
  with subst
        (λ τ → Γtwk ⊢σ τ ∶ ∅ ⊣ wkCtx {K = K} Γo)
        (liftTySub-empty-general {K = K} σ)
        d
... | S-∅ au =
  Γo , refl ,
  subst
    (λ τ → Γo ⊢σ τ ∶ ∅ ⊣ Γo)
    (sym (emptySub-η σ))
    (S-∅ (unwkAllUsed au))
unliftTySub-preserves-σ {K = K} {Γs = B-Lin Ts ▻ Γs′} {σ = σ}
  (S-Lin {Γrest = Γrest} {Γv = Γv} {Γv′ = Γv′} m dv au σtail)
  rewrite tailSub-liftTySub {K = K} σ
  with unliftTySub-preserves-σ {K = K} {Γs = Γs′} {σ = tailSub σ} σtail
... | Γrest₀ , eqrest , σtail₀
  with unwkMergeLeft {K = K} m eqrest
... | Γv₀ , Γt₀ , eqv , eqt , m₀
  with substTy-preserves-value {U = inhabitTy {K = K}} dv
... | dv₀ rewrite eqv
               | substTy-wkCtx-id Γv₀ (inhabitTy {K = K})
               | substTy-wkTyValue-id (σ zero) (inhabitTy {K = K})
               | substTy-wkNfTy-id Ts (inhabitTy {K = K}) =
  Γt₀ , eqt ,
  S-Lin
    m₀
    dv₀
    (substTy-allUsed (inhabitTy {K = K}) au)
    σtail₀
unliftTySub-preserves-σ {K = K} {Γs = B-Un Tu ▻ Γs′} {σ = σ}
  (S-Un d0 σtail)
  rewrite tailSub-liftTySub {K = K} σ
  with unliftTySub-preserves-σ {K = K} {Γs = Γs′} {σ = tailSub σ} σtail
... | Γt₀ , eqt , σtail₀
  with substTy-preserves-value {U = inhabitTy {K = K}} d0
... | d0′ rewrite eqt
              | substTy-wkAllUsedCtx-id Γt₀ (inhabitTy {K = K})
              | substTy-wkTyValue-id (σ zero) (inhabitTy {K = K})
              | substTy-wkNfTy-id Tu (inhabitTy {K = K}) =
  Γt₀ , refl , S-Un d0′ σtail₀
unliftTySub-preserves-σ {K = K} {Γs = B-Used Tu ▻ Γs′} {σ = σ}
  (S-Used σtail)
  rewrite tailSub-liftTySub {K = K} σ
  with unliftTySub-preserves-σ {K = K} {Γs = Γs′} {σ = tailSub σ} σtail
... | Γt₀ , eqt , σtail₀ =
  Γt₀ , eqt , S-Used σtail₀

postulate

  unextSub-used :
    ∀ {Δ n m pk}
      {Γs : Ctx Δ n}
      {Γtwk : Ctx Δ (suc m)}
      {Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {T : NfTy Δ (KV pk Lin)}
    → Γtwk ⊢σ extSub σ ∶ used∷ {T = T} Γs ⊣ used∷ {T = T} Γo
    → Σ (Ctx Δ m) λ Γt →
        (Γtwk ≡ used∷ {T = T} Γt)
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
    {Γtwk : Ctx Δ (suc (suc m))}
    {Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {T : NfTy Δ (KV pk Lin)}
    {U : NfTy Δ (KV pk′ Lin)}
  → Γtwk ⊢σ extSub2 σ ∶ used∷ {T = T} (used∷ {T = U} Γs) ⊣ used∷ {T = T} (used∷ {T = U} Γo)
  → Σ (Ctx Δ m) λ Γt →
      (Γtwk ≡ used∷ {T = T} (used∷ {T = U} Γt))
      × (Γt ⊢σ σ ∶ Γs ⊣ Γo)
unextSub2-used2 {Γs = Γs} {Γtwk = Γtwk} {Γo = Γo} {σ = σ} {T = T} {U = U} σok
  with unextSub-used {Γtwk = Γtwk} {σ = extSub σ} {T = T} σok
... | Γu , eq₁ , σu
  with unextSub-used {Γtwk = Γu} {σ = σ} {T = U} σu
... | Γt , eq₂ , σt =
  Γt ,
  trans eq₁ (cong (used∷ {T = T}) eq₂) ,
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

  substσ-lookup-lin take-here (S-Lin m dv au σtail) =
    _ , consume-lin-head-merge m dv au , S-Used σtail
  substσ-lookup-lin (take-thereˡ take) (S-Lin m dv au σtail)
    with substσ-lookup-lin take σtail
  ... | Γmid , dmid , σtail′
    with lift-lin-through-merge m dmid
  ... | Γtout , _ , mout , dout =
    Γtout , dout , S-Lin mout dv au σtail′
  substσ-lookup-lin {σ = σ} (take-thereᵘ take) (S-Un d0 σtail)
    with substσ-lookup-lin take σtail
  ... | Γt′ , d′ , σtail′
    with value-preserves-~Ctx d′
  ... | Γt~Γt′
    rewrite ~Ctx-allUsedCtx Γt~Γt′
    =
    Γt′ , d′ , S-Un d0 σtail′
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
  substσ-lookup-un (thereᵘˡ x∈) (S-Lin m dv au σtail) =
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
subst-next-ctx (B-Lin T ▻ Γs) (B-Used T ▻ G) (B-Lin T ▻ Γs′) Γt Γo (RM-drop rm) σ (S-Lin {Γrest = Γrest} {Γv} mcs dσ₀ auv ⊢σ)
  with subst-next-ctx Γs G Γs′ Γrest Γo rm (tailSub σ) ⊢σ
... | Γt′ , G′ , ⊢σ′ , au-transport , rmg
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm  = Γt″ , G′ , S-Lin mc dσ₀ auv ⊢σ′ , trans (allUsed-merge mcs) (trans au-transport (sym (allUsed-merge mc))) , rm
subst-next-ctx (B-Lin T ▻ Γs) (B-Lin T ▻ G) (B-Used T ▻ Γs′) Γt Γo (RM-lin rm) σ (S-Lin {Γrest = Γrest} {Γv} mcs dσ₀ auv ⊢σ)
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

pack-synth-result :
  ∀ {Δ n m pk m′}
    {Γs Γs′ : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk m′)}
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
  ∀ {Δ n m pk m′}
    {Γs Γs′ : Ctx Δ n}
    {Γt Γo : Ctx Δ m}
    {σ : Sub Δ n m}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m′)}
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

mutual

  substσ-preserves-value-abs-body :
    ∀ {Δ n m}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {pk₁} {T : NfTy Δ (KV pk₁ Lin)}
      {e : Expr Δ (suc n)}
      {pk₂ m₂} {U : NfTy Δ (KV pk₂ m₂)}
    → (T ∷ˡ Γs) ⊢ e ⇒ U ⊣ used∷ {T = T} Γs′
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Σ (Ctx Δ n) λ G →
        RemoveCtx Γs G Γs′ ×
        Σ (Ctx Δ m) λ Γt′ →
          ((T ∷ˡ Γt) ⊢ substExprWith (extSub σ) e ⇒ U ⊣ used∷ {T = T} Γt′)
          × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-value-abs-body d σok
    with substσ-preserves-synth d (extSub-preserves-σ-lin σok)
  ... | Γtwk , d′ , σwk
    with unextSub-used σwk
  ... | Γt′ , eq , σok′
    rewrite eq
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
      {pk₁ pk₂ m₁ m₂}
      {T : NfTy Δ (KV pk₁ m₁)} {U : NfTy Δ (KV pk₂ m₂)}
      {v : Value Δ (suc n)}
    → (unArrNf (T) (U) ∷ᵘ Γs)
        ⊢ E-Val v ⇐ unArrNf (T) (U)
        ⊣ (unArrNf (T) (U) ∷ᵘ Γs)
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → (unArrNf (T) (U) ∷ᵘ Γt)
        ⊢ E-Val (substValueWith (extSub σ) v) ⇐ unArrNf (T) (U)
        ⊣ (unArrNf (T) (U) ∷ᵘ Γt)

  substσ-preserves-value-rec-body {Γt = Γt} {σ = σ} {T = T} {U = U} d σok
    with substσ-preserves-check d (extSub-preserves-σ-un σok)
  ... | Γtwk , d′ , σwk
    with unextSub-un-fixed {Γt = Γt} {σ = σ} {T = unArrNf (T) (U)} σok σwk
  ... | eq , eqo
    rewrite eq =
      d′

  substσ-preserves-synth-letpair :
    ∀ {Δ n m pk m′}
      {Γs Γmid Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {pk₁ pk₂}
      {T : NfTy Δ (KV pk₁ Lin)}
      {U : NfTy Δ (KV pk₂ Lin)}
      {V : NfTy Δ (KV pk m′)}
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
  ... | Γtmid , d₁′ , σmid
    with substσ-preserves-synth d₂ (extSub2-preserves-σ-lin2 σmid)
  ... | Γtwk , d₂′ , σwk
    with unextSub2-used2 σwk
  ... | Γt′ , eq , σok′
    rewrite eq =
      pack-synth-result
        (T-LetPair d₁ d₂)
        (Γt′ , T-LetPair d₁′ d₂′ , σok′)

  substσ-preserves-value-abs :
    ∀ {Δ n m}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {pk₁}
      {T : Ty Δ (KV pk₁ Lin)}
      {e : Expr Δ (suc n)}
      {W : NfTy Δ (KV KT Lin)}
    → Γs ⊢ᵥ V-Abs T e ⇒ W ⊣ Γs′
    → Γt ⊢σ σ ∶ Γs ⊣ Γo
    → Σ (Ctx Δ n) λ G →
        RemoveCtx Γs G Γs′ ×
        Σ (Ctx Δ m) λ Γt′ →
          (Γt ⊢ᵥ substValueWith σ (V-Abs T e) ⇒ W ⊣ Γt′)
          × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-value-abs (TV-Abs {T = T} {U = U} d) σok
    with substσ-preserves-value-abs-body {T = normalizeTy T} {U = U} d σok
  ... | G , rm , Γt′ , d′ , σok′ =
    G , rm , Γt′ , TV-Abs {T = T} {U = U} d′ , σok′

  substσ-preserves-value-rec :
    ∀ {Δ n m}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {pk₁ pk₂ m₁ m₂}
      {T : Ty Δ (KV pk₁ m₁)} {U : Ty Δ (KV pk₂ m₂)}
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
      (TV-Rec {T = T} {U = U} d)
      (_ , TV-Rec {T = T} {U = U}
            (substσ-preserves-value-rec-body {T = normalizeTy T} {U = normalizeTy U} d σok) , σok)

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
    ∀ {Δ n m pk m′}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {v : Value Δ n}
      {T : NfTy Δ (KV pk m′)}
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
    ∀ {Δ n m k pk m′}
      {Γs Γmid Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {ss : Subset.Subset (suc k)} {v : Variance}
      {ssbranches : Subset.Subset (suc k)} {incl : ss Subset.⊆ ssbranches}
      {ne : Subset.Nonempty ssbranches}
      {P : NfTy Δ KP} {S : NfTy Δ SLin} {U : NfTy Δ (KV pk m′)}
      {e : Expr Δ n}
      {branches : (i : Fin (suc k)) → i Subset.∈ ssbranches → Expr Δ (suc n)}
      {V : (i : Fin (suc k)) → i Subset.∈ ssbranches → NfTy Δ (KV pk m′)}
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
  ... | Γt₂ , d′ , σmid
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
    ... | Γtwki , di , σwki
      with unextSub-used σwki
    ... | Γti , eqi , σoki
      rewrite eqi = Γti , di , σoki

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
    ∀ {Δ n m pk m′}
      {Γs Γs′ : Ctx Δ n}
      {Γt Γo : Ctx Δ m}
      {σ : Sub Δ n m}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk m′)}
    → (de : Γs ⊢ e ⇒ T ⊣ Γs′)
    → (⊢σ : Γt ⊢σ σ ∶ Γs ⊣ Γo)
    → Σ (Ctx Δ m) λ Γt′ →
        (Γt ⊢ substExprWith σ e ⇒ T ⊣ Γt′)
        × (Γt′ ⊢σ σ ∶ Γs′ ⊣ Γo)

  substσ-preserves-synth (T-Val d) σok
    with substσ-preserves-value d σok
  ... | _ , _ , Γt′ , d′ , σok′ =
    Γt′ , T-Val d′ , σok′
  substσ-preserves-synth (T-Pair d₁ d₂) σok
    with substσ-preserves-synth d₁ σok
  ... | Γt₂ , d₁′ , σok₂
    with substσ-preserves-synth d₂ σok₂
  ... | Γt₃ , d₂′ , σok₃ =
    Γt₃ , T-Pair d₁′ d₂′ , σok₃
  substσ-preserves-synth (T-App d₁ d₂) σok
    with substσ-preserves-synth d₁ σok
  ... | Γt₂ , d₁′ , σok₂
    with substσ-preserves-check d₂ σok₂
  ... | Γt₃ , d₂′ , σok₃ =
    Γt₃ , T-App d₁′ d₂′ , σok₃
  substσ-preserves-synth (T-LetUnit d₁ d₂) σok
    with substσ-preserves-check d₁ σok
  ... | Γt₂ , d₁′ , σok₂
    with substσ-preserves-synth d₂ σok₂
  ... | Γt₃ , d₂′ , σok₃ =
    Γt₃ , T-LetUnit d₁′ d₂′ , σok₃
  substσ-preserves-synth d@(T-LetPair d₁ d₂) σok
    with substσ-preserves-synth-letpair d₁ d₂ σok
  ... | _ , _ , Γt′ , d′ , σok′ =
    Γt′ , d′ , σok′
  substσ-preserves-synth (T-Match {ss = ss} {incl = incl} d bs j) σok =
    substσ-preserves-synth-match {ss = ss} {incl = incl} d bs j σok
  substσ-preserves-synth (T-TApp d) σok
    with substσ-preserves-synth d σok
  ... | Γt′ , d′ , σok′ =
    Γt′ , T-TApp d′ , σok′

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
  ... | Γt′ , d′ , σok′ =
    Γt′ , T-Check d′ sub , σok′
