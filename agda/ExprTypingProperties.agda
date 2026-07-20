module ExprTypingProperties where

open import Data.Fin using (Fin; zero) renaming (suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.PropositionalEquality as Eq

open import AlgorithmicNFSubtyping using (_<:ₜ_)
open import Variance using (Variance)
open import Kinds using (Kind; KV; KP; SLin; TLin; Lin; Un)
open import ExprSyntax using (NfTy; Expr; Value; E-Match)
open import ExprNormalTyping
open import ExprContextReduction using
  ( RemoveCtx; RM-∅; RM-drop; RM-allused; RM-lin; RM-un
  ; AllUsed; AU-∅; AU-used; AU-un
  ; FrameCtx; FC-∅; FC-frame; FC-allused; FC-live; FC-un
  ) public

frame-unique :
  ∀ {Δ n} {Φ Γ Γ̂₁ Γ̂₂ : Ctx Δ n}
  → FrameCtx Φ Γ Γ̂₁
  → FrameCtx Φ Γ Γ̂₂
  → Γ̂₁ ≡ Γ̂₂
frame-unique FC-∅ FC-∅ = refl
frame-unique (FC-frame f₁) (FC-frame f₂)
  rewrite frame-unique f₁ f₂ = refl
frame-unique (FC-allused f₁) (FC-allused f₂)
  rewrite frame-unique f₁ f₂ = refl
frame-unique (FC-live f₁) (FC-live f₂)
  rewrite frame-unique f₁ f₂ = refl
frame-unique (FC-un f₁) (FC-un f₂)
  rewrite frame-unique f₁ f₂ = refl

frame-cons-used :
  ∀ {Δ n pk} {Φ Γ Γ̂ : Ctx Δ n} {T : NfTy Δ (KV pk Lin)}
  → FrameCtx Φ Γ Γ̂
  → FrameCtx (B-Used T ▻ Φ) (B-Used T ▻ Γ) (B-Used T ▻ Γ̂)
frame-cons-used = FC-allused

frame-cons-lin :
  ∀ {Δ n pk} {Φ Γ Γ̂ : Ctx Δ n} {T : NfTy Δ (KV pk Lin)}
  → FrameCtx Φ Γ Γ̂
  → FrameCtx (B-Used T ▻ Φ) (B-Lin T ▻ Γ) (B-Lin T ▻ Γ̂)
frame-cons-lin = FC-live

frame-cons-un-local :
  ∀ {Δ n pk} {Φ Γ Γ̂ : Ctx Δ n} {T : NfTy Δ (KV pk Un)}
  → FrameCtx Φ Γ Γ̂
  → FrameCtx (B-Un T ▻ Φ) (B-Un T ▻ Γ) (B-Un T ▻ Γ̂)
frame-cons-un-local = FC-un

wkFrameCtx :
  ∀ {Δ n K} {Φ Γ Γ̂ : Ctx Δ n}
  → FrameCtx Φ Γ Γ̂
  → FrameCtx (wkCtx {K = K} Φ) (wkCtx Γ) (wkCtx Γ̂)
wkFrameCtx FC-∅ = FC-∅
wkFrameCtx (FC-frame f) = FC-frame (wkFrameCtx f)
wkFrameCtx (FC-allused f) = FC-allused (wkFrameCtx f)
wkFrameCtx (FC-live f) = FC-live (wkFrameCtx f)
wkFrameCtx (FC-un f) = FC-un (wkFrameCtx f)

lift-∋ᵘ :
  ∀ {Δ n pk} {Γ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Un)} (b : Binding Δ)
  → Γ ∋ᵘ x ∶ T
  → (b ▻ Γ) ∋ᵘ fsuc x ∶ T
lift-∋ᵘ (B-Lin _) = thereᵘˡ
lift-∋ᵘ (B-Un _) = thereᵘᵘ
lift-∋ᵘ (B-Used _) = thereᵘ✖

frame-∋ᵘ :
  ∀ {Δ n pk} {Φ Γ Γ̂ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Un)}
  → Γ ∋ᵘ x ∶ T
  → FrameCtx Φ Γ Γ̂
  → Γ̂ ∋ᵘ x ∶ T
frame-∋ᵘ hereᵘ (FC-un f) = hereᵘ
frame-∋ᵘ (thereᵘˡ x∈) (FC-live f) = thereᵘˡ (frame-∋ᵘ x∈ f)
frame-∋ᵘ (thereᵘᵘ x∈) (FC-un f) = thereᵘᵘ (frame-∋ᵘ x∈ f)
frame-∋ᵘ (thereᵘ✖ x∈) (FC-frame f) = thereᵘˡ (frame-∋ᵘ x∈ f)
frame-∋ᵘ (thereᵘ✖ x∈) (FC-allused f) = thereᵘ✖ (frame-∋ᵘ x∈ f)

lift-take :
  ∀ {Δ n pk} {Γ Γ′ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Lin)} (b : Binding Δ)
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
  → (b ▻ Γ) ⊢ˡ fsuc x ∶ T ⊣ (b ▻ Γ′)
lift-take (B-Lin _) = take-thereˡ
lift-take (B-Un _) = take-thereᵘ
lift-take (B-Used _) = take-there✖

frame-take :
  ∀ {Δ n pk} {Φ Γ Γ′ Γ̂ Γ̂′ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Lin)}
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
  → FrameCtx Φ Γ Γ̂
  → FrameCtx Φ Γ′ Γ̂′
  → Γ̂ ⊢ˡ x ∶ T ⊣ Γ̂′
frame-take take-here (FC-live f) (FC-allused f′)
  rewrite frame-unique f f′ = take-here
frame-take (take-thereˡ t) (FC-live f) (FC-live f′) =
  take-thereˡ (frame-take t f f′)
frame-take (take-thereᵘ t) (FC-un f) (FC-un f′) =
  take-thereᵘ (frame-take t f f′)
frame-take (take-there✖ t) (FC-frame f) (FC-frame f′) =
  take-thereˡ (frame-take t f f′)
frame-take (take-there✖ t) (FC-allused f) (FC-allused f′) =
  take-there✖ (frame-take t f f′)

frame-take-exists :
  ∀ {Δ n pk} {Φ Γ Γ′ Γ̂ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Lin)}
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
  → FrameCtx Φ Γ Γ̂
  → Σ (Ctx Δ n) λ Γ̂′ → FrameCtx Φ Γ′ Γ̂′ × (Γ̂ ⊢ˡ x ∶ T ⊣ Γ̂′)
frame-take-exists take-here (FC-live f) =
  _ , FC-allused f , take-here
frame-take-exists (take-thereˡ t) (FC-live f)
  with frame-take-exists t f
... | Γ̂′ , f′ , t′ = _ , FC-live f′ , take-thereˡ t′
frame-take-exists (take-thereᵘ t) (FC-un f)
  with frame-take-exists t f
... | Γ̂′ , f′ , t′ = _ , FC-un f′ , take-thereᵘ t′
frame-take-exists (take-there✖ t) (FC-frame f)
  with frame-take-exists t f
... | Γ̂′ , f′ , t′ = _ , FC-frame f′ , take-thereˡ t′
frame-take-exists (take-there✖ t) (FC-allused f)
  with frame-take-exists t f
... | Γ̂′ , f′ , t′ = _ , FC-allused f′ , take-there✖ t′

invert-frame-used :
  ∀ {Δ n pk} {Φ Γ : Ctx Δ n} {Γ̂ : Ctx Δ (suc n)} {T : NfTy Δ (KV pk Lin)}
  → FrameCtx (B-Used T ▻ Φ) (B-Used T ▻ Γ) Γ̂
  → Σ (Ctx Δ n) λ Γ̂₀ → (Γ̂ ≡ B-Used T ▻ Γ̂₀) × FrameCtx Φ Γ Γ̂₀
invert-frame-used (FC-allused f) = _ , refl , f

invert-frame-un-local :
  ∀ {Δ n pk} {Φ Γ : Ctx Δ n} {Γ̂ : Ctx Δ (suc n)} {T : NfTy Δ (KV pk Un)}
  → FrameCtx (B-Un T ▻ Φ) (B-Un T ▻ Γ) Γ̂
  → Σ (Ctx Δ n) λ Γ̂₀ → (Γ̂ ≡ B-Un T ▻ Γ̂₀) × FrameCtx Φ Γ Γ̂₀
invert-frame-un-local (FC-un f) = _ , refl , f

frame-un-head :
  ∀ {Δ n pk₁ pk₂} {Φ Γ : Ctx Δ n} {Γ̂ : Ctx Δ (suc n)}
    {T : NfTy Δ (KV pk₁ Un)} {U : NfTy Δ (KV pk₂ Un)}
  → FrameCtx (B-Un T ▻ Φ) (B-Un U ▻ Γ) Γ̂
  → Σ (pk₁ ≡ pk₂) λ where
      refl → T ≡ U
frame-un-head (FC-un _) = refl , refl

frame-remove :
  ∀ {Δ n} {Γ₀ G Γ₁ : Ctx Δ n}
  → FrameCtx Γ₁ G Γ₀
  → RemoveCtx Γ₀ G Γ₁
frame-remove FC-∅ = RM-∅
frame-remove (FC-frame f) = RM-drop (frame-remove f)
frame-remove (FC-allused f) = RM-allused (frame-remove f)
frame-remove (FC-live f) = RM-lin (frame-remove f)
frame-remove (FC-un f) = RM-un (frame-remove f)

allUsed-frame :
  ∀ {Δ n} {Φ Γ Γ̂ : Ctx Δ n}
  → AllUsed Γ
  → FrameCtx Φ Γ Γ̂
  → Γ̂ ≡ Φ
allUsed-frame AU-∅ FC-∅ = refl
allUsed-frame (AU-used au) (FC-frame f)
  rewrite allUsed-frame au f = refl
allUsed-frame (AU-used au) (FC-allused f)
  rewrite allUsed-frame au f = refl
allUsed-frame (AU-un au) (FC-un f)
  rewrite allUsed-frame au f = refl

frame-lin-used-head :
  ∀ {Δ n pk₁ pk₂}
    {Φ Γ : Ctx Δ n}
    {Γ̂ : Ctx Δ (suc n)}
    {T : NfTy Δ (KV pk₁ Lin)}
    {U : NfTy Δ (KV pk₂ Lin)}
  → FrameCtx (B-Lin T ▻ Φ) (B-Used U ▻ Γ) Γ̂
  → Σ (pk₁ ≡ pk₂) λ where
      refl → T ≡ U
frame-lin-used-head (FC-frame _) = refl , refl

frame-used-used-head :
  ∀ {Δ n pk₁ pk₂}
    {Φ Γ : Ctx Δ n}
    {Γ̂ : Ctx Δ (suc n)}
    {T : NfTy Δ (KV pk₁ Lin)}
    {U : NfTy Δ (KV pk₂ Lin)}
  → FrameCtx (B-Used T ▻ Φ) (B-Used U ▻ Γ) Γ̂
  → Σ (pk₁ ≡ pk₂) λ where
      refl → T ≡ U
frame-used-used-head (FC-allused _) = refl , refl

frame-used-lin-head :
  ∀ {Δ n pk₁ pk₂}
    {Φ Γ : Ctx Δ n}
    {Γ̂ : Ctx Δ (suc n)}
    {T : NfTy Δ (KV pk₁ Lin)}
    {U : NfTy Δ (KV pk₂ Lin)}
  → FrameCtx (B-Used T ▻ Φ) (B-Lin U ▻ Γ) Γ̂
  → Σ (pk₁ ≡ pk₂) λ where
      refl → T ≡ U
frame-used-lin-head (FC-live _) = refl , refl

wkFrameCtx-invert :
  ∀ {Δ n K} {Φ Γ : Ctx Δ n} {Γ̂ : Ctx (K ∷ Δ) n}
  → FrameCtx (wkCtx {K = K} Φ) (wkCtx Γ) Γ̂
  → Σ (Ctx Δ n) λ Γ̂₀ → (Γ̂ ≡ wkCtx {K = K} Γ̂₀) × FrameCtx Φ Γ Γ̂₀
wkFrameCtx-invert {Φ = ∅} {Γ = ∅} FC-∅ =
  ∅ , refl , FC-∅
wkFrameCtx-invert
  {K = K}
  {Φ = B-Lin T ▻ Φ}
  {Γ = B-Used U ▻ Γ}
  f
  with frame-lin-used-head f
... | refl , eq
  with wkNfTy-injective eq
... | refl
  with f
... | FC-frame ftail
  with wkFrameCtx-invert {K = K} ftail
... | Γ̂₀ , eq , f₀ =
  (B-Lin T ▻ Γ̂₀) ,
  Eq.cong (B-Lin (wkNfTy {K′ = K} T) ▻_) eq ,
  FC-frame f₀
wkFrameCtx-invert
  {K = K}
  {Φ = B-Used T ▻ Φ}
  {Γ = B-Used U ▻ Γ}
  f
  with frame-used-used-head f
... | refl , eq
  with wkNfTy-injective eq
... | refl
  with f
... | FC-allused ftail
  with wkFrameCtx-invert {K = K} ftail
... | Γ̂₀ , eq , f₀ =
  (B-Used T ▻ Γ̂₀) ,
  Eq.cong (B-Used (wkNfTy {K′ = K} T) ▻_) eq ,
  FC-allused f₀
wkFrameCtx-invert
  {K = K}
  {Φ = B-Used T ▻ Φ}
  {Γ = B-Lin U ▻ Γ}
  f
  with frame-used-lin-head f
... | refl , eq
  with wkNfTy-injective eq
... | refl
  with f
... | FC-live ftail
  with wkFrameCtx-invert {K = K} ftail
... | Γ̂₀ , eq , f₀ =
  (B-Lin T ▻ Γ̂₀) ,
  Eq.cong (B-Lin (wkNfTy {K′ = K} T) ▻_) eq ,
  FC-live f₀
wkFrameCtx-invert
  {K = K}
  {Φ = B-Un T ▻ Φ}
  {Γ = B-Un U ▻ Γ}
  f
  with frame-un-head f
... | refl , eq
  with wkNfTy-injective eq
... | refl
  with f
... | FC-un ftail
  with wkFrameCtx-invert {K = K} ftail
... | Γ̂₀ , eq , f₀ =
  (B-Un T ▻ Γ̂₀) ,
  Eq.cong (B-Un (wkNfTy {K′ = K} T) ▻_) eq ,
  FC-un f₀

mutual

  frame-value :
    ∀ {Δ n pk m} {Φ Γ Γ′ Γ̂ : Ctx Δ n} {v : Value Δ n} {T : NfTy Δ (KV pk m)}
    → Γ ⊢ᵥ v ⇒ T ⊣ Γ′
    → FrameCtx Φ Γ Γ̂
    → Σ (Ctx Δ n) λ Γ̂′ → FrameCtx Φ Γ′ Γ̂′ × (Γ̂ ⊢ᵥ v ⇒ T ⊣ Γ̂′)
  frame-value (TV-Const cT) f = _ , f , TV-Const cT
  frame-value (TV-Var-Lin take) f
    with frame-take-exists take f
  ... | Γ̂′ , f′ , take′ = Γ̂′ , f′ , TV-Var-Lin take′
  frame-value (TV-Var-Un x∈) f = _ , f , TV-Var-Un (frame-∋ᵘ x∈ f)
  frame-value (TV-Abs {T = T} {U = U} d) f
    with frame-synth d (frame-cons-lin f)
  ... | Γ̂body , fbody , d′
    with invert-frame-used fbody
  ... | Γ̂′ , refl , f′ = Γ̂′ , f′ , TV-Abs {T = T} {U = U} d′
  frame-value (TV-Rec d) f
    with frame-check d (frame-cons-un-local f)
  ... | Γ̂body , fbody , d′
    with invert-frame-un-local fbody
  ... | Γ̂′ , refl , f′
    with frame-unique f f′
  ... | refl = _ , f , TV-Rec d′
  frame-value (TV-TAbs d) f
    with frame-value d (wkFrameCtx f)
  ... | Γ̂wk , fwk , d′
    with wkFrameCtx-invert fwk
  ... | Γ̂′ , refl , f′ = Γ̂′ , f′ , TV-TAbs d′
  frame-value (TV-Pair d₁ d₂) f
    with frame-value d₁ f
  ... | Γ̂₂ , f₂ , d₁′
    with frame-value d₂ f₂
  ... | Γ̂₃ , f₃ , d₂′ = Γ̂₃ , f₃ , TV-Pair d₁′ d₂′
  frame-value TV-Receive₁ f = _ , f , TV-Receive₁
  frame-value TV-Receive₂ f = _ , f , TV-Receive₂
  frame-value TV-Send₁ f = _ , f , TV-Send₁
  frame-value TV-Send₂ f = _ , f , TV-Send₂
  frame-value TV-Select₁ f = _ , f , TV-Select₁
  frame-value TV-Select₂ f = _ , f , TV-Select₂

  frame-synth-match :
    ∀ {Δ n pk m} {Φ Γ₁ Γ₂ Γ₃ Γ̂₁ : Ctx Δ n} {k} {ss : Subset.Subset (suc k)}
      {e : Expr Δ n}
      {ssbranches : Subset.Subset (suc k)} {incl : ss Subset.⊆ ssbranches}
      {ne : Subset.Nonempty ssbranches} {v : Variance}
      {P : NfTy Δ KP} {S : NfTy Δ SLin}
      {branches : (i : Fin (suc k)) → i Subset.∈ ssbranches → Expr Δ (suc n)}
      {U : NfTy Δ (KV pk m)}
      {V : (i : Fin (suc k)) → i Subset.∈ ssbranches → NfTy Δ (KV pk m)}
      {sub : (i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) → V i i∈ <:ₜ U}
    → Γ₁ ⊢ e ⇒ MatchBranchInput ss v P S ⊣ Γ₂
    → ((i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) → (MatchBranchOutput ssbranches v P S i i∈ ∷ˡ Γ₂) ⊢ branches i i∈ ⇒ V i i∈ ⊣ used∷ Γ₃)
    → BranchJoin⁺ ssbranches V ≡ just (U , sub)
    → FrameCtx Φ Γ₁ Γ̂₁
    → Σ (Ctx Δ n) λ Γ̂₃ → FrameCtx Φ Γ₃ Γ̂₃ × (Γ̂₁ ⊢ E-Match {ss = ssbranches} e ne branches ⇒ U ⊣ Γ̂₃)
  frame-synth-match {Δ = Δ} {n = n} {Φ = Φ} {Γ₃ = Γ₃} {k = k} {ss = ss}
                    {ssbranches = ssbranches} {incl = incl} {ne = ne} {v = v} {P = P} {S = S}
                    {branches = branches} {U = U} {V = V} {sub = sub}
                    d bs j f
    with frame-synth d f
  ... | Γ̂₂ , f₂ , d′
    with frame-synth (bs (proj₁ ne) (proj₂ ne)) (frame-cons-lin f₂)
  ... | Γ̂zero , fzero , dzero
    with invert-frame-used fzero
  ... | Γ̂₃ , refl , f₃ =
    Γ̂₃ , f₃ ,
      T-Match {ss = ss} {ssbranches = ssbranches} {incl = incl} d′ bs′ j
    where
    branch :
      (i : Fin (suc k)) (i∈ : i Subset.∈ ssbranches)
      → Σ (Ctx Δ (suc n)) λ Γ̂i
          → FrameCtx (B-Used (MatchBranchOutput ssbranches v P S i i∈) ▻ Φ)
                     (B-Used (MatchBranchOutput ssbranches v P S i i∈) ▻ Γ₃)
                     Γ̂i
          × ((MatchBranchOutput ssbranches v P S i i∈ ∷ˡ Γ̂₂) ⊢ branches i i∈ ⇒ V i i∈ ⊣ Γ̂i)
    branch i i∈ with frame-synth (bs i i∈) (frame-cons-lin f₂)
    ... | Γ̂i , fi , di = Γ̂i , fi , di

    bs′ : (i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) →
            (MatchBranchOutput ssbranches v P S i i∈ ∷ˡ Γ̂₂)
              ⊢ branches i i∈ ⇒ V i i∈ ⊣ (B-Used (MatchBranchOutput ssbranches v P S i i∈) ▻ Γ̂₃)
    bs′ i i∈ with branch i i∈
    ... | Γ̂i , fi , di with invert-frame-used fi
    ... | Γ̂₃′ , refl , f₃′
      rewrite frame-unique f₃ f₃′ = di

  frame-synth :
    ∀ {Δ n pk m} {Φ Γ Γ′ Γ̂ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ (KV pk m)}
    → Γ ⊢ e ⇒ T ⊣ Γ′
    → FrameCtx Φ Γ Γ̂
    → Σ (Ctx Δ n) λ Γ̂′ → FrameCtx Φ Γ′ Γ̂′ × (Γ̂ ⊢ e ⇒ T ⊣ Γ̂′)
  frame-synth (T-Val d) f
    with frame-value d f
  ... | Γ̂′ , f′ , d′ = Γ̂′ , f′ , T-Val d′
  frame-synth (T-Pair d₁ d₂) f
    with frame-synth d₁ f
  ... | Γ̂₂ , f₂ , d₁′
    with frame-synth d₂ f₂
  ... | Γ̂₃ , f₃ , d₂′ = Γ̂₃ , f₃ , T-Pair d₁′ d₂′
  frame-synth (T-App d₁ d₂) f
    with frame-synth d₁ f
  ... | Γ̂₂ , f₂ , d₁′
    with frame-check d₂ f₂
  ... | Γ̂₃ , f₃ , d₂′ = Γ̂₃ , f₃ , T-App d₁′ d₂′
  frame-synth (T-LetUnit d₁ d₂) f
    with frame-check d₁ f
  ... | Γ̂₂ , f₂ , d₁′
    with frame-synth d₂ f₂
  ... | Γ̂₃ , f₃ , d₂′ = Γ̂₃ , f₃ , T-LetUnit d₁′ d₂′
  frame-synth (T-LetPair d₁ d₂) f
    with frame-synth d₁ f
  ... | Γ̂₂ , f₂ , d₁′
    with frame-synth d₂ (frame-cons-lin (frame-cons-lin f₂))
  ... | Γ̂body , fbody , d₂′
    with invert-frame-used fbody
  ... | Γ̂used₁ , refl , fbody₁
    with invert-frame-used fbody₁
  ... | Γ̂₃ , refl , f₃ = Γ̂₃ , f₃ , T-LetPair d₁′ d₂′
  frame-synth (T-Match {ss = ss} {incl = incl} d bs j) f =
    frame-synth-match {ss = ss} {incl = incl} d bs j f
  frame-synth (T-TApp d) f
    with frame-synth d f
  ... | Γ̂′ , f′ , d′ = Γ̂′ , f′ , T-TApp d′

  frame-check :
    ∀ {Δ n pk m} {Φ Γ Γ′ Γ̂ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ (KV pk m)}
    → Γ ⊢ e ⇐ T ⊣ Γ′
    → FrameCtx Φ Γ Γ̂
    → Σ (Ctx Δ n) λ Γ̂′ → FrameCtx Φ Γ′ Γ̂′ × (Γ̂ ⊢ e ⇐ T ⊣ Γ̂′)
  frame-check (T-Check d sub) f
    with frame-synth d f
  ... | Γ̂′ , f′ , d′ = Γ̂′ , f′ , T-Check d′ sub

replay-value :
  ∀ {Δ n pk m} {Φ Γ Γ′ Γ̂ Γ̂′ : Ctx Δ n} {v : Value Δ n} {T : NfTy Δ (KV pk m)}
  → Γ ⊢ᵥ v ⇒ T ⊣ Γ′
  → FrameCtx Φ Γ Γ̂
  → FrameCtx Φ Γ′ Γ̂′
  → Γ̂ ⊢ᵥ v ⇒ T ⊣ Γ̂′
replay-value d fin fout
  with frame-value d fin
... | Γ̂″ , f″ , d′
  rewrite frame-unique fout f″ = d′

replay-synth :
  ∀ {Δ n pk m} {Φ Γ Γ′ Γ̂ Γ̂′ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ (KV pk m)}
  → Γ ⊢ e ⇒ T ⊣ Γ′
  → FrameCtx Φ Γ Γ̂
  → FrameCtx Φ Γ′ Γ̂′
  → Γ̂ ⊢ e ⇒ T ⊣ Γ̂′
replay-synth d fin fout
  with frame-synth d fin
... | Γ̂″ , f″ , d′
  rewrite frame-unique fout f″ = d′

replay-check :
  ∀ {Δ n pk m} {Φ Γ Γ′ Γ̂ Γ̂′ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ (KV pk m)}
  → Γ ⊢ e ⇐ T ⊣ Γ′
  → FrameCtx Φ Γ Γ̂
  → FrameCtx Φ Γ′ Γ̂′
  → Γ̂ ⊢ e ⇐ T ⊣ Γ̂′
replay-check d fin fout
  with frame-check d fin
... | Γ̂″ , f″ , d′
  rewrite frame-unique fout f″ = d′

replay-value-allUsed :
  ∀ {Δ n pk m} {Φ Γ Γ′ Γ̂ : Ctx Δ n} {v : Value Δ n} {T : NfTy Δ (KV pk m)}
  → Γ ⊢ᵥ v ⇒ T ⊣ Γ′
  → FrameCtx Φ Γ Γ̂
  → AllUsed Γ′
  → Γ̂ ⊢ᵥ v ⇒ T ⊣ Φ
replay-value-allUsed d fin au
  with frame-value d fin
... | Γ̂″ , fout , d′
  rewrite allUsed-frame au fout = d′

replay-synth-allUsed :
  ∀ {Δ n pk m} {Φ Γ Γ′ Γ̂ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ (KV pk m)}
  → Γ ⊢ e ⇒ T ⊣ Γ′
  → FrameCtx Φ Γ Γ̂
  → AllUsed Γ′
  → Γ̂ ⊢ e ⇒ T ⊣ Φ
replay-synth-allUsed d fin au
  with frame-synth d fin
... | Γ̂″ , fout , d′
  rewrite allUsed-frame au fout = d′

replay-check-allUsed :
  ∀ {Δ n pk m} {Φ Γ Γ′ Γ̂ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ (KV pk m)}
  → Γ ⊢ e ⇐ T ⊣ Γ′
  → FrameCtx Φ Γ Γ̂
  → AllUsed Γ′
  → Γ̂ ⊢ e ⇐ T ⊣ Φ
replay-check-allUsed d fin au
  with frame-check d fin
... | Γ̂″ , fout , d′
  rewrite allUsed-frame au fout = d′
