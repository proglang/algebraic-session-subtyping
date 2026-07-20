module ExprContextProperties where

open import Data.Fin using (Fin)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Kinds
open import ExprSyntax using (NfTy)
open import ExprNormalTyping

data AllUsed {Δ} : ∀ {n} → Ctx Δ n → Set where
  AU-∅ : AllUsed ∅
  AU-used : ∀ {n} {Γ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Lin)}
    → AllUsed Γ
    → AllUsed (B-Used T ▻ Γ)
  AU-un : ∀ {n} {Γ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Un)}
    → AllUsed Γ
    → AllUsed (B-Un T ▻ Γ)

allUsedCtx : ∀ {Δ n} → Ctx Δ n → Ctx Δ n
allUsedCtx ∅ = ∅
allUsedCtx (B-Lin T ▻ Γ) = B-Used T ▻ allUsedCtx Γ
allUsedCtx (B-Un T ▻ Γ) = B-Un T ▻ allUsedCtx Γ
allUsedCtx (B-Used T ▻ Γ) = B-Used T ▻ allUsedCtx Γ

allUsedCtx-AllUsed : ∀ {Δ n} (Γ : Ctx Δ n) → AllUsed (allUsedCtx Γ)
allUsedCtx-AllUsed ∅ = AU-∅
allUsedCtx-AllUsed (B-Lin T ▻ Γ) = AU-used {T = T} (allUsedCtx-AllUsed Γ)
allUsedCtx-AllUsed (B-Un _ ▻ Γ) = AU-un (allUsedCtx-AllUsed Γ)
allUsedCtx-AllUsed (B-Used _ ▻ Γ) = AU-used (allUsedCtx-AllUsed Γ)

allUsedCtx-∋ᵘ :
  ∀ {Δ n pk}
    {Γ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Un)}
  → Γ ∋ᵘ x ∶ T
  → allUsedCtx Γ ∋ᵘ x ∶ T
allUsedCtx-∋ᵘ hereᵘ = hereᵘ
allUsedCtx-∋ᵘ (thereᵘˡ x∈) =
  thereᵘ✖ (allUsedCtx-∋ᵘ x∈)
allUsedCtx-∋ᵘ (thereᵘᵘ x∈) =
  thereᵘᵘ (allUsedCtx-∋ᵘ x∈)
allUsedCtx-∋ᵘ (thereᵘ✖ x∈) =
  thereᵘ✖ (allUsedCtx-∋ᵘ x∈)

-- Only linear resources must be kept disjoint. Unrestricted bindings may
-- appear on both sides simultaneously.
data LinearDisjoint {Δ} : ∀ {n} → Ctx Δ n → Ctx Δ n → Set where
  LD-∅ : LinearDisjoint ∅ ∅

  LD-used-used : ∀ {n} {Γ₀ Γ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Lin)}
    → LinearDisjoint Γ₀ Γ
    → LinearDisjoint (B-Used T ▻ Γ₀) (B-Used T ▻ Γ)

  LD-used-live : ∀ {n pk} {Γ₀ Γ : Ctx Δ n} {T : NfTy Δ (KV pk Lin)}
    → LinearDisjoint Γ₀ Γ
    → LinearDisjoint (B-Used T ▻ Γ₀) (B-Lin T ▻ Γ)

  LD-live-used : ∀ {n pk} {Γ₀ Γ : Ctx Δ n} {T : NfTy Δ (KV pk Lin)}
    → LinearDisjoint Γ₀ Γ
    → LinearDisjoint (B-Lin T ▻ Γ₀) (B-Used T ▻ Γ)

  LD-un-un : ∀ {n} {Γ₀ Γ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Un)}
    → LinearDisjoint Γ₀ Γ
    → LinearDisjoint (B-Un T ▻ Γ₀) (B-Un T ▻ Γ)

-- Merge the full context used to type the payload into the updated channel
-- context. Live linear positions of Γv are turned into `B-Used`; live
-- unrestricted positions leave Γx unchanged.
data FrameCtx {Δ} : ∀ {n} → Ctx Δ n → Ctx Δ n → Ctx Δ n → Set where
  FC-∅ : FrameCtx ∅ ∅ ∅

  FC-allused : ∀ {n} {Γx Γv Γ₁ : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Lin)}
    → FrameCtx Γx Γv Γ₁
    → FrameCtx (B-Used T ▻ Γx) (B-Used T ▻ Γv) (B-Used T ▻ Γ₁)

  FC-live : ∀ {n} {Γx Γv Γ₁ : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Lin)}
    → FrameCtx Γx Γv Γ₁
    → FrameCtx (B-Used T ▻ Γx) (B-Lin T ▻ Γv) (B-Lin T ▻ Γ₁)

  FC-frame : ∀ {n} {Γx Γv Γ₁ : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Lin)}
    → FrameCtx Γx Γv Γ₁
    → FrameCtx (B-Lin T ▻ Γx) (B-Used T ▻ Γv) (B-Lin T ▻ Γ₁)

  FC-un : ∀ {n} {Γx Γv Γ₁ : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Un)}
    → FrameCtx Γx Γv Γ₁
    → FrameCtx (B-Un T ▻ Γx) (B-Un T ▻ Γv) (B-Un T ▻ Γ₁)

frame-sym :
  ∀ {Δ n} {Γ₁ Γ₂ Γ : Ctx Δ n}
  → FrameCtx Γ₁ Γ₂ Γ
  → FrameCtx Γ₂ Γ₁ Γ
frame-sym FC-∅ = FC-∅
frame-sym (FC-allused f) = FC-allused (frame-sym f)
frame-sym (FC-live f) = FC-frame (frame-sym f)
frame-sym (FC-frame f) = FC-live (frame-sym f)
frame-sym (FC-un f) = FC-un (frame-sym f)

mergeDisjointContext :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
  → LinearDisjoint Γ₁ Γ₂
  → Σ (Ctx Δ n) λ Γ → FrameCtx Γ₁ Γ₂ Γ
mergeDisjointContext LD-∅ = ∅ , FC-∅
mergeDisjointContext (LD-used-used ld)
  with mergeDisjointContext ld
... | Γ , m = _ , FC-allused m
mergeDisjointContext (LD-used-live ld)
  with mergeDisjointContext ld
... | Γ , m = _ , FC-live m
mergeDisjointContext (LD-live-used ld)
  with mergeDisjointContext ld
... | Γ , m = _ , FC-frame m
mergeDisjointContext {Γ₁ = B-Un T ▻ Γ₁} {Γ₂ = B-Un .T ▻ Γ₂} (LD-un-un {T = T} ld)
  with mergeDisjointContext {Γ₁ = Γ₁} {Γ₂ = Γ₂} ld
... | Γ , m = (B-Un T ▻ Γ) , FC-un {Γ₁ = Γ} {T = T} m

-- Remove a full payload context from a full source context. Live linear
-- bindings of Γv are consumed from Γ₀; live unrestricted bindings are shared
-- and therefore remain present in the remainder.
data RemoveCtx {Δ} : ∀ {n} → Ctx Δ n → Ctx Δ n → Ctx Δ n → Set where
  RM-∅ : RemoveCtx ∅ ∅ ∅

  RM-drop : ∀ {n} {Γ₀ Γv Γx : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Lin)}
    → RemoveCtx Γ₀ Γv Γx
    → RemoveCtx (B-Lin T ▻ Γ₀) (B-Used T ▻ Γv) (B-Lin T ▻ Γx)

  RM-allused : ∀ {n} {Γ₀ Γv Γx : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Lin)}
    → RemoveCtx Γ₀ Γv Γx
    → RemoveCtx (B-Used T ▻ Γ₀) (B-Used T ▻ Γv) (B-Used T ▻ Γx)

  RM-lin : ∀ {n} {Γ₀ Γv Γx : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Lin)}
    → RemoveCtx Γ₀ Γv Γx
    → RemoveCtx (B-Lin T ▻ Γ₀) (B-Lin T ▻ Γv) (B-Used T ▻ Γx)

  RM-un : ∀ {n} {Γ₀ Γv Γx : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Un)}
    → RemoveCtx Γ₀ Γv Γx
    → RemoveCtx (B-Un T ▻ Γ₀) (B-Un T ▻ Γv) (B-Un T ▻ Γx)

remove-allUsedCtx : ∀ {Δ n} (Γ : Ctx Δ n) → RemoveCtx Γ (allUsedCtx Γ) Γ
remove-allUsedCtx ∅ = RM-∅
remove-allUsedCtx (B-Lin T ▻ Γ) = RM-drop {T = T} (remove-allUsedCtx Γ)
remove-allUsedCtx (B-Un _ ▻ Γ) = RM-un (remove-allUsedCtx Γ)
remove-allUsedCtx (B-Used _ ▻ Γ) = RM-allused (remove-allUsedCtx Γ)

strip-rm-lin :
  ∀ {Δ n pk}
    {T : NfTy Δ (KV pk Lin)}
    {Γ₀ Γ₁ : Ctx Δ n}
    {G : Ctx Δ (suc n)}
  → RemoveCtx (T ∷ˡ Γ₀) G (B-Used T ▻ Γ₁)
  → Σ (Ctx Δ n) λ G′ →
      (G ≡ T ∷ˡ G′) × RemoveCtx Γ₀ G′ Γ₁
strip-rm-lin (RM-lin r) = _ , refl , r

strip-rm-un :
  ∀ {Δ n pk}
    {T : NfTy Δ (KV pk Un)}
    {Γ₀ Γ₁ : Ctx Δ n}
    {G : Ctx Δ (suc n)}
  → RemoveCtx (T ∷ᵘ Γ₀) G (T ∷ᵘ Γ₁)
  → Σ (Ctx Δ n) λ G′ →
      (G ≡ T ∷ᵘ G′) × RemoveCtx Γ₀ G′ Γ₁
strip-rm-un (RM-un r) = _ , refl , r

allUsed-merge :
  ∀ {Δ n} {Γ₀ Γ₁ Γ₂ : Ctx Δ n}
  → FrameCtx Γ₀ Γ₁ Γ₂
  → allUsedCtx Γ₂ ≡ allUsedCtx Γ₀
allUsed-merge FC-∅ = refl
allUsed-merge (FC-allused mc) rewrite allUsed-merge mc = refl
allUsed-merge (FC-live mc) rewrite allUsed-merge mc = refl
allUsed-merge (FC-frame mc) rewrite allUsed-merge mc = refl
allUsed-merge (FC-un mc) = cong (B-Un _ ▻_) (allUsed-merge mc)

remove-unique : ∀ {Δ}{n} {Γ G₁ G₂ Γ′ : Ctx Δ n} → RemoveCtx Γ G₁ Γ′ → RemoveCtx Γ G₂ Γ′ → G₁ ≡ G₂
remove-unique RM-∅ RM-∅ = refl
remove-unique (RM-drop rm₁) (RM-drop rm₂) rewrite remove-unique rm₁ rm₂ = refl
remove-unique (RM-allused rm₁) (RM-allused rm₂) rewrite remove-unique rm₁ rm₂ = refl
remove-unique (RM-lin rm₁) (RM-lin rm₂) = cong (B-Lin _ ▻_) (remove-unique rm₁ rm₂)
remove-unique (RM-un rm₁) (RM-un rm₂) = cong (B-Un _ ▻_) (remove-unique rm₁ rm₂)

compose-merge-remove :
  ∀ {Δ n} {Γrest Γv Γt G′ Γt′ : Ctx Δ n}
  → (mcs : FrameCtx Γrest Γv Γt)
  → (rmg : RemoveCtx Γrest G′ Γt′)
  → Σ (Ctx Δ n) λ G″ → RemoveCtx Γt G″ Γt′
compose-merge-remove FC-∅ RM-∅ = ∅ , RM-∅
compose-merge-remove (FC-allused mcs) (RM-allused rmg)
  with compose-merge-remove mcs rmg
... | G″ , rm = _ , RM-allused rm
compose-merge-remove (FC-live mcs) (RM-allused rmg)
  with compose-merge-remove mcs rmg
... | G″ , rm = _ , RM-lin rm
compose-merge-remove (FC-frame mcs) (RM-drop rmg)
  with compose-merge-remove mcs rmg
... | G″ , rm = _ , RM-drop rm
compose-merge-remove (FC-frame mcs) (RM-lin rmg)
  with compose-merge-remove mcs rmg
... | G″ , rm = _ , RM-lin rm
compose-merge-remove (FC-un {T = T} mcs) (RM-un rmg)
  with compose-merge-remove mcs rmg
... | G″ , rm = B-Un T ▻ G″ , RM-un rm

compose-merge-remove2 :
  ∀ {Δ n} {Γrest Γv Γt G′ Γt′ : Ctx Δ n}
  → (mcs : FrameCtx Γrest Γv Γt)
  → (rmg : RemoveCtx Γrest G′ Γt′)
  → Σ (Ctx Δ n) λ Γt″ → FrameCtx Γt′ Γv Γt″ × RemoveCtx Γt G′ Γt″
compose-merge-remove2 FC-∅ RM-∅ = ∅ , FC-∅ , RM-∅
compose-merge-remove2 (FC-live mcs) (RM-allused rmg)
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm = _ , FC-live mc , RM-drop rm
compose-merge-remove2 (FC-frame mcs) (RM-drop rmg)
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm = _ , FC-frame mc , RM-drop rm
compose-merge-remove2 (FC-frame mcs) (RM-lin rmg)
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm = _ , FC-allused mc , RM-lin rm
compose-merge-remove2 (FC-allused mcs) (RM-allused rmg)
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm = _ , FC-allused mc , RM-allused rm
compose-merge-remove2 (FC-un mcs) (RM-un rmg)
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm = _ , FC-un mc , RM-un rm

mergeRemoveContext :
  ∀ {Δ n} {Γ₀ Γ₁ Γ₂ G₁ G₂ : Ctx Δ n}
  → RemoveCtx Γ₀ G₁ Γ₁
  → RemoveCtx Γ₁ G₂ Γ₂
  → Σ (Ctx Δ n) λ Γ →
      FrameCtx G₁ G₂ Γ × RemoveCtx Γ₀ Γ Γ₂
mergeRemoveContext RM-∅ RM-∅ = ∅ , FC-∅ , RM-∅
mergeRemoveContext (RM-drop {T = T} r₁) (RM-drop r₂)
  with mergeRemoveContext r₁ r₂
... | Γ , m , r = _ , FC-allused m , RM-drop r
mergeRemoveContext (RM-drop {T = T} r₁) (RM-lin r₂)
  with mergeRemoveContext r₁ r₂
... | Γ , m , r = _ , FC-live m , RM-lin r
mergeRemoveContext (RM-allused {T = T} r₁) (RM-allused r₂)
  with mergeRemoveContext r₁ r₂
... | Γ , m , r = _ , FC-allused m , RM-allused r
mergeRemoveContext (RM-lin {T = T} r₁) (RM-allused r₂)
  with mergeRemoveContext r₁ r₂
... | Γ , m , r = _ , FC-frame m , RM-lin r
mergeRemoveContext (RM-un r₁) (RM-un r₂)
  with mergeRemoveContext r₁ r₂
... | Γ , m , r = _ , FC-un m , RM-un r

remove-linear :
  ∀ {Δ n} {Γ₀ G Γ₁ : Ctx Δ n}
  → RemoveCtx Γ₀ G Γ₁
  → LinearDisjoint G Γ₁
remove-linear RM-∅ = LD-∅
remove-linear (RM-drop r) = LD-used-live (remove-linear r)
remove-linear (RM-allused r) = LD-used-used (remove-linear r)
remove-linear (RM-lin r) = LD-live-used (remove-linear r)
remove-linear (RM-un r) = LD-un-un (remove-linear r)

remove-allused-disjoint :
  ∀ {Δ n} {Γ₀ G Γ₁ : Ctx Δ n}
  → RemoveCtx Γ₀ G Γ₁
  → LinearDisjoint G (allUsedCtx Γ₀)
remove-allused-disjoint RM-∅ = LD-∅
remove-allused-disjoint (RM-drop r) = LD-used-used (remove-allused-disjoint r)
remove-allused-disjoint (RM-allused r) = LD-used-used (remove-allused-disjoint r)
remove-allused-disjoint (RM-lin r) = LD-live-used (remove-allused-disjoint r)
remove-allused-disjoint (RM-un r) = LD-un-un (remove-allused-disjoint r)

remove-preserves-remove :
  ∀ {Δ n}
    {Γ₀ G Γ₂ Γin Γr : Ctx Δ n}
  → RemoveCtx Γ₀ G Γ₂
  → RemoveCtx Γ₀ Γin Γr
  → LinearDisjoint G Γin
  → Σ (Ctx Δ n) λ Γr′ → RemoveCtx Γ₂ Γin Γr′
remove-preserves-remove RM-∅ RM-∅ LD-∅ = ∅ , RM-∅
remove-preserves-remove (RM-drop r₁) (RM-drop r₂) (LD-used-used ld)
  with remove-preserves-remove r₁ r₂ ld
... | Γr′ , r′ = B-Lin _ ▻ Γr′ , RM-drop r′
remove-preserves-remove (RM-drop {T = T} r₁) (RM-lin r₂) (LD-used-live ld)
  with remove-preserves-remove r₁ r₂ ld
... | Γr′ , r′ = B-Used _ ▻ Γr′ , RM-lin r′
remove-preserves-remove (RM-allused {T = T} r₁) (RM-allused r₂) (LD-used-used ld)
  with remove-preserves-remove r₁ r₂ ld
... | Γr′ , r′ = B-Used _ ▻ Γr′ , RM-allused r′
remove-preserves-remove (RM-lin {T = T} r₁) (RM-drop r₂) (LD-live-used ld)
  with remove-preserves-remove r₁ r₂ ld
... | Γr′ , r′ = B-Used _ ▻ Γr′ , RM-allused r′
remove-preserves-remove (RM-un r₁) (RM-un r₂) (LD-un-un ld)
  with remove-preserves-remove r₁ r₂ ld
... | Γr′ , r′ = B-Un _ ▻ Γr′ , RM-un r′

sym-disjoint :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
  → LinearDisjoint Γ₁ Γ₂
  → LinearDisjoint Γ₂ Γ₁
sym-disjoint LD-∅ = LD-∅
sym-disjoint (LD-used-used d) = LD-used-used (sym-disjoint d)
sym-disjoint (LD-used-live d) = LD-live-used (sym-disjoint d)
sym-disjoint (LD-live-used d) = LD-used-live (sym-disjoint d)
sym-disjoint (LD-un-un d) = LD-un-un (sym-disjoint d)

remove-preserves-disjoint :
  ∀ {Δ n}
    {Γ₀ G Γ₁ Γf : Ctx Δ n}
  → RemoveCtx Γ₀ G Γ₁
  → LinearDisjoint Γ₀ Γf
  → LinearDisjoint Γ₁ Γf
remove-preserves-disjoint RM-∅ LD-∅ = LD-∅
remove-preserves-disjoint (RM-drop r) (LD-live-used d) =
  LD-live-used (remove-preserves-disjoint r d)
remove-preserves-disjoint (RM-allused r) (LD-used-used d) =
  LD-used-used (remove-preserves-disjoint r d)
remove-preserves-disjoint (RM-allused r) (LD-used-live d) =
  LD-used-live (remove-preserves-disjoint r d)
remove-preserves-disjoint (RM-lin r) (LD-live-used d) =
  LD-used-used (remove-preserves-disjoint r d)
remove-preserves-disjoint (RM-un r) (LD-un-un d) =
  LD-un-un (remove-preserves-disjoint r d)

remove-removed-disjoint :
  ∀ {Δ n}
    {Γ₀ G Γ₁ Γf : Ctx Δ n}
  → RemoveCtx Γ₀ G Γ₁
  → LinearDisjoint Γ₀ Γf
  → LinearDisjoint G Γf
remove-removed-disjoint RM-∅ LD-∅ = LD-∅
remove-removed-disjoint (RM-drop r) (LD-live-used d) =
  LD-used-used (remove-removed-disjoint r d)
remove-removed-disjoint (RM-allused r) (LD-used-used d) =
  LD-used-used (remove-removed-disjoint r d)
remove-removed-disjoint (RM-allused r) (LD-used-live d) =
  LD-used-live (remove-removed-disjoint r d)
remove-removed-disjoint (RM-lin r) (LD-live-used d) =
  LD-live-used (remove-removed-disjoint r d)
remove-removed-disjoint (RM-un r) (LD-un-un d) =
  LD-un-un (remove-removed-disjoint r d)

restore-disjoint :
  ∀ {Δ n}
    {Γ₀ G Γ₁ Γf : Ctx Δ n}
  → RemoveCtx Γ₀ G Γ₁
  → LinearDisjoint Γ₁ Γf
  → LinearDisjoint G Γf
  → LinearDisjoint Γ₀ Γf
restore-disjoint RM-∅ LD-∅ LD-∅ = LD-∅
restore-disjoint (RM-drop r) (LD-live-used d₁) (LD-used-used d₂) =
  LD-live-used (restore-disjoint r d₁ d₂)
restore-disjoint (RM-allused r) (LD-used-used d₁) (LD-used-used d₂) =
  LD-used-used (restore-disjoint r d₁ d₂)
restore-disjoint (RM-allused r) (LD-used-live d₁) (LD-used-live d₂) =
  LD-used-live (restore-disjoint r d₁ d₂)
restore-disjoint (RM-lin r) (LD-used-used d₁) (LD-live-used d₂) =
  LD-live-used (restore-disjoint r d₁ d₂)
restore-disjoint (RM-un r) (LD-un-un d₁) (LD-un-un d₂) =
  LD-un-un (restore-disjoint r d₁ d₂)

merge-disjoint :
  ∀ {Δ n}
    {Γx Γv Γ : Ctx Δ n}
  → FrameCtx Γx Γv Γ
  → LinearDisjoint Γx Γv
merge-disjoint FC-∅ = LD-∅
merge-disjoint (FC-allused m) = LD-used-used (merge-disjoint m)
merge-disjoint (FC-live m) = LD-used-live (merge-disjoint m)
merge-disjoint (FC-frame m) = LD-live-used (merge-disjoint m)
merge-disjoint (FC-un m) = LD-un-un (merge-disjoint m)

merge-preserves-disjoint :
  ∀ {Δ n}
    {Γx Γv Γ₁ Γf : Ctx Δ n}
  → FrameCtx Γx Γv Γ₁
  → LinearDisjoint Γx Γf
  → LinearDisjoint Γv Γf
  → LinearDisjoint Γ₁ Γf
merge-preserves-disjoint FC-∅ LD-∅ LD-∅ = LD-∅
merge-preserves-disjoint (FC-allused m) (LD-used-used dx) (LD-used-used dv) =
  LD-used-used (merge-preserves-disjoint m dx dv)
merge-preserves-disjoint (FC-allused m) (LD-used-live dx) (LD-used-live dv) =
  LD-used-live (merge-preserves-disjoint m dx dv)
merge-preserves-disjoint (FC-live m) (LD-used-used dx) (LD-live-used dv) =
  LD-live-used (merge-preserves-disjoint m dx dv)
merge-preserves-disjoint (FC-frame m) (LD-live-used dx) (LD-used-used dv) =
  LD-live-used (merge-preserves-disjoint m dx dv)
merge-preserves-disjoint (FC-un m) (LD-un-un dx) (LD-un-un dv) =
  LD-un-un (merge-preserves-disjoint m dx dv)

allFrame :
  ∀ {Δ n}
  → (Γ : Ctx Δ n)
  → ∃[ Γf ] ∃[ Γl ] FrameCtx Γf Γl Γ × AllUsed Γl
allFrame ∅ = ∅ , ∅ , FC-∅ , AU-∅
allFrame (b ▻ Γ)
  with allFrame Γ
allFrame (B-Lin x ▻ Γ) | Γf , Γl , fc , au = B-Lin x ▻ Γf , B-Used x ▻ Γl , FC-frame fc , AU-used au
allFrame (B-Un x ▻ Γ) | Γf , Γl , fc , au = B-Un x ▻ Γf , B-Un x ▻ Γl , FC-un fc , AU-un au
allFrame (used∷ {x} Γ) | Γf , Γl , fc , au = B-Used x ▻ Γf , B-Used x ▻ Γl , FC-allused fc , AU-used au
