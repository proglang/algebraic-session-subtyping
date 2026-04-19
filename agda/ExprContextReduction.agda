module ExprContextReduction where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)

open import Kinds
open import Duality
open import Types
open import NormalTypes using (N-Up; N-Normal)
open import NormalTypesSubstitution using (msgNF)
open import ExprSyntax using (Value; E-Val)
open import ExprSemantics using (Label; L-β; L-Fork; L-New; L-RecvVal; L-RecvLab; L-SendVal; L-SendLab; L-Close)
open import ExprNormalTyping
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Function using (const)

-- This module proposes a context-level reduction relation on full contexts.
-- Unlike Fig. 13 in the report, it does not work on context fragments. The
-- idea is that a label updates one full incoming context directly to one full
-- outgoing context.
--
-- For `L-RecvVal x v`, the current channel binding at `x` is updated from
-- `?T.S` to `S`, and the resources used while typing `v` are merged into the
-- full context.

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
data MergeCtx {Δ} : ∀ {n} → Ctx Δ n → Ctx Δ n → Ctx Δ n → Set where
  MC-∅ : MergeCtx ∅ ∅ ∅

  MC-used-used : ∀ {n} {Γx Γv Γ₁ : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Lin)}
    → MergeCtx Γx Γv Γ₁
    → MergeCtx (B-Used T ▻ Γx) (B-Used T ▻ Γv) (B-Used T ▻ Γ₁)

  MC-used-left : ∀ {n} {Γx Γv Γ₁ : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Lin)}
    → MergeCtx Γx Γv Γ₁
    → MergeCtx (B-Used T ▻ Γx) (B-Lin T ▻ Γv) (B-Lin T ▻ Γ₁)

  MC-used-right : ∀ {n} {Γx Γv Γ₁ : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Lin)}
    → MergeCtx Γx Γv Γ₁
    → MergeCtx (B-Lin T ▻ Γx) (B-Used T ▻ Γv) (B-Lin T ▻ Γ₁)

  MC-un : ∀ {n} {Γx Γv Γ₁ : Ctx Δ n} {pk : PreKind} {T : NfTy Δ (KV pk Un)}
    → MergeCtx Γx Γv Γ₁
    → MergeCtx (B-Un T ▻ Γx) (B-Un T ▻ Γv) (B-Un T ▻ Γ₁)

mergeDisjointContext :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
  → LinearDisjoint Γ₁ Γ₂
  → Σ (Ctx Δ n) λ Γ → MergeCtx Γ₁ Γ₂ Γ
mergeDisjointContext LD-∅ = ∅ , MC-∅
mergeDisjointContext (LD-used-used ld)
  with mergeDisjointContext ld
... | Γ , m = _ , MC-used-used m
mergeDisjointContext (LD-used-live ld)
  with mergeDisjointContext ld
... | Γ , m = _ , MC-used-left m
mergeDisjointContext (LD-live-used ld)
  with mergeDisjointContext ld
... | Γ , m = _ , MC-used-right m
mergeDisjointContext {Γ₁ = B-Un T ▻ Γ₁} {Γ₂ = B-Un .T ▻ Γ₂} (LD-un-un {T = T} ld)
  with mergeDisjointContext {Γ₁ = Γ₁} {Γ₂ = Γ₂} ld
... | Γ , m = (B-Un T ▻ Γ) , MC-un {Γ₁ = Γ} {T = T} m

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

allUsed-merge :
  ∀ {Δ n} {Γ₀ Γ₁ Γ₂ : Ctx Δ n}
  → MergeCtx Γ₀ Γ₁ Γ₂
  → allUsedCtx Γ₂ ≡ allUsedCtx Γ₀
allUsed-merge MC-∅ = refl
allUsed-merge (MC-used-used mc) rewrite allUsed-merge mc = refl
allUsed-merge (MC-used-left mc) rewrite allUsed-merge mc = refl
allUsed-merge (MC-used-right mc) rewrite allUsed-merge mc = refl
allUsed-merge (MC-un mc) = cong (B-Un _ ▻_) (allUsed-merge mc)

rm-allUsed : ∀ {Δ n} (Γ : Ctx Δ n) → RemoveCtx Γ (allUsedCtx Γ) Γ
rm-allUsed = remove-allUsedCtx

remove-unique : ∀ {Δ}{n} {Γ G₁ G₂ Γ′ : Ctx Δ n} → RemoveCtx Γ G₁ Γ′ → RemoveCtx Γ G₂ Γ′ → G₁ ≡ G₂
remove-unique RM-∅ RM-∅ = refl
remove-unique (RM-drop rm₁) (RM-drop rm₂) rewrite remove-unique rm₁ rm₂ = refl
remove-unique (RM-allused rm₁) (RM-allused rm₂) rewrite remove-unique rm₁ rm₂ = refl
remove-unique (RM-lin rm₁) (RM-lin rm₂) = cong (B-Lin _ ▻_) (remove-unique rm₁ rm₂)
remove-unique (RM-un rm₁) (RM-un rm₂) = cong (B-Un _ ▻_) (remove-unique rm₁ rm₂)

compose-merge-remove :
  ∀ {Δ n} {Γrest Γv Γt G′ Γt′ : Ctx Δ n}
  → (mcs : MergeCtx Γrest Γv Γt)
  → (rmg : RemoveCtx Γrest G′ Γt′)
  → Σ (Ctx Δ n) λ G″ → RemoveCtx Γt G″ Γt′
compose-merge-remove MC-∅ RM-∅ = ∅ , RM-∅
compose-merge-remove (MC-used-used mcs) (RM-allused rmg)
  with compose-merge-remove mcs rmg
... | G″ , rm = _ , RM-allused rm
compose-merge-remove (MC-used-left mcs) (RM-allused rmg)
  with compose-merge-remove mcs rmg
... | G″ , rm = _ , RM-lin rm
compose-merge-remove (MC-used-right mcs) (RM-drop rmg)
  with compose-merge-remove mcs rmg
... | G″ , rm = _ , RM-drop rm
compose-merge-remove (MC-used-right mcs) (RM-lin rmg)
  with compose-merge-remove mcs rmg
... | G″ , rm = _ , RM-lin rm
compose-merge-remove (MC-un {T = T} mcs) (RM-un rmg)
  with compose-merge-remove mcs rmg
... | G″ , rm = B-Un T ▻ G″ , RM-un rm

compose-merge-remove2 :
  ∀ {Δ n} {Γrest Γv Γt G′ Γt′ : Ctx Δ n}
  → (mcs : MergeCtx Γrest Γv Γt)
  → (rmg : RemoveCtx Γrest G′ Γt′)
  → Σ (Ctx Δ n) λ Γt″ → MergeCtx Γt′ Γv Γt″ × RemoveCtx Γt G′ Γt″
compose-merge-remove2 MC-∅ RM-∅ = ∅ , MC-∅ , RM-∅
compose-merge-remove2 (MC-used-left mcs) (RM-allused rmg)
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm = _ , MC-used-left mc , RM-drop rm
compose-merge-remove2 (MC-used-right mcs) (RM-drop rmg)
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm = _ , MC-used-right mc , RM-drop rm
compose-merge-remove2 (MC-used-right mcs) (RM-lin rmg)
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm = _ , MC-used-used mc , RM-lin rm
compose-merge-remove2 (MC-used-used mcs) (RM-allused rmg)
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm = _ , MC-used-used mc , RM-allused rm
compose-merge-remove2 (MC-un mcs) (RM-un rmg)
  with compose-merge-remove2 mcs rmg
... | Γt″ , mc , rm = _ , MC-un mc , RM-un rm

mergeRemoveContext :
  ∀ {Δ n} {Γ₀ Γ₁ Γ₂ G₁ G₂ : Ctx Δ n}
  → RemoveCtx Γ₀ G₁ Γ₁
  → RemoveCtx Γ₁ G₂ Γ₂
  → Σ (Ctx Δ n) λ Γ →
      MergeCtx G₁ G₂ Γ × RemoveCtx Γ₀ Γ Γ₂
mergeRemoveContext RM-∅ RM-∅ = ∅ , MC-∅ , RM-∅
mergeRemoveContext (RM-drop {T = T} r₁) (RM-drop r₂)
  with mergeRemoveContext r₁ r₂
... | Γ , m , r = _ , MC-used-used m , RM-drop r
mergeRemoveContext (RM-drop {T = T} r₁) (RM-lin r₂)
  with mergeRemoveContext r₁ r₂
... | Γ , m , r = _ , MC-used-left m , RM-lin r
mergeRemoveContext (RM-allused {T = T} r₁) (RM-allused r₂)
  with mergeRemoveContext r₁ r₂
... | Γ , m , r = _ , MC-used-used m , RM-allused r
mergeRemoveContext (RM-lin {T = T} r₁) (RM-allused r₂)
  with mergeRemoveContext r₁ r₂
... | Γ , m , r = _ , MC-used-right m , RM-lin r
mergeRemoveContext (RM-un r₁) (RM-un r₂)
  with mergeRemoveContext r₁ r₂
... | Γ , m , r = _ , MC-un m , RM-un r

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
  → MergeCtx Γx Γv Γ
  → LinearDisjoint Γx Γv
merge-disjoint MC-∅ = LD-∅
merge-disjoint (MC-used-used m) = LD-used-used (merge-disjoint m)
merge-disjoint (MC-used-left m) = LD-used-live (merge-disjoint m)
merge-disjoint (MC-used-right m) = LD-live-used (merge-disjoint m)
merge-disjoint (MC-un m) = LD-un-un (merge-disjoint m)

merge-preserves-disjoint :
  ∀ {Δ n}
    {Γx Γv Γ₁ Γf : Ctx Δ n}
  → MergeCtx Γx Γv Γ₁
  → LinearDisjoint Γx Γf
  → LinearDisjoint Γv Γf
  → LinearDisjoint Γ₁ Γf
merge-preserves-disjoint MC-∅ LD-∅ LD-∅ = LD-∅
merge-preserves-disjoint (MC-used-used m) (LD-used-used dx) (LD-used-used dv) =
  LD-used-used (merge-preserves-disjoint m dx dv)
merge-preserves-disjoint (MC-used-used m) (LD-used-live dx) (LD-used-live dv) =
  LD-used-live (merge-preserves-disjoint m dx dv)
merge-preserves-disjoint (MC-used-left m) (LD-used-used dx) (LD-live-used dv) =
  LD-live-used (merge-preserves-disjoint m dx dv)
merge-preserves-disjoint (MC-used-right m) (LD-live-used dx) (LD-used-used dv) =
  LD-live-used (merge-preserves-disjoint m dx dv)
merge-preserves-disjoint (MC-un m) (LD-un-un dx) (LD-un-un dv) =
  LD-un-un (merge-preserves-disjoint m dx dv)

-- Pointwise replacement in a full context.
data ReplaceAt {Δ} : ∀ {n} → Ctx Δ n → Fin n → Binding Δ → Ctx Δ n → Set where
  R-here : ∀ {n} {Γ : Ctx Δ n} {b b′ : Binding Δ}
    → ReplaceAt (b ▻ Γ) zero b′ (b′ ▻ Γ)

  R-there : ∀ {n} {Γ Γ′ : Ctx Δ n} {x : Fin n} {b b′ : Binding Δ}
    → ReplaceAt Γ x b′ Γ′
    → ReplaceAt (b ▻ Γ) (suc x) b′ (b ▻ Γ′)

postulate
  used-head-eq :
    ∀ {Δ n pk₁ pk₂}
      {T₁ : NfTy Δ (KV pk₁ Lin)}
      {T₂ : NfTy Δ (KV pk₂ Lin)}
      {Γ : Ctx Δ n}
    → (B-Used T₁ ▻ Γ) ≡ (B-Used T₂ ▻ Γ)

replace-preserves-disjoint :
  ∀ {Δ n pk}
    {Γ₀ Γ₁ Γf : Ctx Δ n}
    {x : Fin n} {T : NfTy Δ (KV pk Lin)} {U : NfTy Δ (KV pk Lin)}
  → Γ₀ ∋ˡ x ∶ T
  → LinearDisjoint Γ₀ Γf
  → ReplaceAt Γ₀ x (B-Lin U) Γ₁
  → Σ (Ctx Δ n) λ Γf′ →
      ReplaceAt Γf x (B-Used U) Γf′ × LinearDisjoint Γ₁ Γf′
replace-preserves-disjoint hereˡ (LD-live-used d) R-here =
  _ , R-here , LD-live-used d
replace-preserves-disjoint (thereˡˡ x∈) (LD-live-used d) (R-there rep)
  with replace-preserves-disjoint x∈ d rep
... | Γf′ , rep′ , ld′ =
  _ , R-there rep′ , LD-live-used ld′
replace-preserves-disjoint (thereˡᵘ x∈) (LD-un-un d) (R-there rep)
  with replace-preserves-disjoint x∈ d rep
... | Γf′ , rep′ , ld′ =
  _ , R-there rep′ , LD-un-un ld′
replace-preserves-disjoint (thereˡ✖ x∈) (LD-used-used d) (R-there rep)
  with replace-preserves-disjoint x∈ d rep
... | Γf′ , rep′ , ld′ =
  _ , R-there rep′ , LD-used-used ld′
replace-preserves-disjoint (thereˡ✖ x∈) (LD-used-live d) (R-there rep)
  with replace-preserves-disjoint x∈ d rep
... | Γf′ , rep′ , ld′ =
  _ , R-there rep′ , LD-used-live ld′

replace-used-preserves-disjoint :
  ∀ {Δ n pk}
    {Γ₀ Γ₁ Γf : Ctx Δ n}
    {x : Fin n} {T : NfTy Δ (KV pk Lin)}
  → Γ₀ ∋ˡ x ∶ T
  → LinearDisjoint Γ₀ Γf
  → ReplaceAt Γ₀ x (B-Used T) Γ₁
  → LinearDisjoint Γ₁ Γf
replace-used-preserves-disjoint hereˡ (LD-live-used d) R-here = LD-used-used d
replace-used-preserves-disjoint (thereˡˡ x∈) (LD-live-used d) (R-there rep) =
  LD-live-used (replace-used-preserves-disjoint x∈ d rep)
replace-used-preserves-disjoint (thereˡᵘ x∈) (LD-un-un d) (R-there rep) =
  LD-un-un (replace-used-preserves-disjoint x∈ d rep)
replace-used-preserves-disjoint (thereˡ✖ x∈) (LD-used-used d) (R-there rep) =
  LD-used-used (replace-used-preserves-disjoint x∈ d rep)
replace-used-preserves-disjoint (thereˡ✖ x∈) (LD-used-live d) (R-there rep) =
  LD-used-live (replace-used-preserves-disjoint x∈ d rep)

replace-used-eq :
  ∀ {Δ n pk pk′}
    {Γ₀ Γf Γf′ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
    {U : NfTy Δ (KV pk′ Lin)}
  → Γ₀ ∋ˡ x ∶ T
  → LinearDisjoint Γ₀ Γf
  → ReplaceAt Γf x (B-Used U) Γf′
  → Γf ≡ Γf′
replace-used-eq hereˡ (LD-live-used d) R-here = used-head-eq
replace-used-eq (thereˡˡ x∈) (LD-live-used d) (R-there rep) =
  cong (B-Used _ ▻_) (replace-used-eq x∈ d rep)
replace-used-eq (thereˡᵘ x∈) (LD-un-un d) (R-there rep) =
  cong (B-Un _ ▻_) (replace-used-eq x∈ d rep)
replace-used-eq (thereˡ✖ x∈) (LD-used-used d) (R-there rep) =
  cong (B-Used _ ▻_) (replace-used-eq x∈ d rep)
replace-used-eq (thereˡ✖ x∈) (LD-used-live d) (R-there rep) =
  cong (B-Lin _ ▻_) (replace-used-eq x∈ d rep)

sessNf : NfTy [] SLin → NfTy [] TLin
sessNf = sessTyNf

unitLinNf : NfTy [] TLin
unitLinNf = unitConstNf

recvChanNf : NfTy [] TLin → NfTy [] SLin → NfTy [] TLin
recvChanNf T S = sessTyNf (msgNF ⊝ (N-Normal (N-Up T)) S)

sendChanNf : NfTy [] TLin → NfTy [] SLin → NfTy [] TLin
sendChanNf T S = sessTyNf (msgNF ⊕ (N-Normal (N-Up T)) S)

dualSessNf : NfTy [] SLin → NfTy [] TLin
dualSessNf S = normalizeTy (SessLin (T-Dual D-S ⌞ S ⌟))

selectInNf : ∀ {k} → Variance → Fin k → NfTy [] KP → NfTy [] SLin → NfTy [] TLin
selectInNf = selectInTyNf

selectOutNf : ∀ {k} → Variance → Fin k → NfTy [] KP → NfTy [] SLin → NfTy [] TLin
selectOutNf = selectOutTyNf

postulate
  SelectBranches : ∀ {k} → NfTy [] SLin → (Fin k → NfTy [] SLin) → Set

infix 4 _—ctx[_]→_

data _—ctx[_]→_ : ∀ {n Θ} → Ctx [] n → Label n Θ → Ctx [] (length Θ + n) → Set where
  Ctx-β : ∀ {n} {Γ : Ctx [] n}
    → Γ —ctx[ ExprSemantics.L-β ]→ Γ

  Ctx-New : ∀ {n} {Γ₀ : Ctx [] n} {S : Ty [] SLin}
    → Γ₀ —ctx[ L-New S ]→ (B-Lin (normalizeTy (SessLin S)) ▻ (B-Lin (dualSessNf (normalizeTy S)) ▻ Γ₀))

  Ctx-Fork : ∀ {n} {Γ₀ Γv Γv′ Γ₁ : Ctx [] n} {v : Value [] n}
    → RemoveCtx Γ₀ Γv Γ₁
    → Γv ⊢ E-Val v ⇐ linArrNf unitLinNf unitLinNf ⊣ Γv′
    → AllUsed Γv′
    → Γ₀ —ctx[ L-Fork v ]→ Γ₁

  Ctx-Rcv : ∀ {n} {Γ₀ Γv Γv′ Γx Γ₁ : Ctx [] n}
      {x : Fin n} {T : NfTy [] TLin} {S : NfTy [] SLin} {v : Value [] n}
    → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
    → AllUsed Γv′
    → LinearDisjoint Γ₀ Γv
    → Γ₀ ∋ˡ x ∶ recvChanNf T S
    → ReplaceAt Γ₀ x (B-Lin (sessNf S)) Γx
    → MergeCtx Γx Γv Γ₁
    → Γ₀ —ctx[ L-RecvVal x v ]→ Γ₁

  Ctx-Send : ∀ {n} {Γ₀ Γx Γv Γv′ Γ₁ : Ctx [] n}
      {x : Fin n} {T : NfTy [] TLin} {S : NfTy [] SLin} {v : Value [] n}
    → RemoveCtx Γ₀ Γv Γx
    → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
    → AllUsed Γv′
    → Γx ∋ˡ x ∶ sendChanNf T S
    → ReplaceAt Γx x (B-Lin (sessNf S)) Γ₁
    → Γ₀ —ctx[ L-SendVal x v ]→ Γ₁

  Ctx-Close : ∀ {n} {Γ₀ Γ₁ : Ctx [] n} {x : Fin n}
    → Γ₀ ∋ˡ x ∶ normalizeTy EndLin
    → ReplaceAt Γ₀ x (B-Used (normalizeTy EndLin)) Γ₁
    → Γ₀ —ctx[ L-Close x ]→ Γ₁

  Ctx-Match : ∀ {n k}
      {ssin ssout : Subset.Subset (suc k)} {incl : ssin Subset.⊆ ssout}
      {Γ₀ Γ₁ : Ctx [] n} {x : Fin n} {i : Fin (suc k)}
      {v : Variance} {P : NfTy [] KP} {S : NfTy [] SLin}
    → (i∈ : i Subset.∈ ssout)
    → Γ₀ ∋ˡ x ∶ MatchBranchInput ssin v P S
    → ReplaceAt Γ₀ x (B-Lin (MatchBranchOutput ssout v P S i i∈)) Γ₁
    → Γ₀ —ctx[ L-RecvLab x i ]→ Γ₁

  Ctx-Select : ∀ {n k} {Γ₀ Γ₁ : Ctx [] n} {x : Fin n} {i : Fin k}
      {v : Variance} {P : NfTy [] KP} {S : NfTy [] SLin}
    → Γ₀ ∋ˡ x ∶ selectInNf v i P S
    → ReplaceAt Γ₀ x (B-Lin (selectOutNf v i P S)) Γ₁
    → Γ₀ —ctx[ L-SendLab x i ]→ Γ₁

data _⦂_⇒_ : ∀ {n Θ} → Label n Θ → Ctx [] n → Ctx [] n → Set where

  Label-β : ∀ {n} {Γin Γv : Ctx [] n}
    → AllUsed Γin
    → AllUsed Γv
    → L-β ⦂ Γin ⇒ Γv

  Label-Fork : ∀ {n} {Γin Γv : Ctx [] n} {v : Value [] n}
    → AllUsed Γin
    → AllUsed Γv
    → L-Fork v ⦂ Γin ⇒ Γv

  Label-New : ∀ {n} {Γin Γv : Ctx [] n} {S : Ty [] SLin}
    → AllUsed Γin
    → AllUsed Γv
    → L-New S ⦂ Γin ⇒ Γv

  Label-RecvVal :
    ∀ {n} {x : Fin n}
      {Γin Γin′ Γv Γv′ : Ctx [] n}
      {T : NfTy [] TLin} {S : NfTy [] SLin} {v : Value [] n}
    → Γin ⊢ˡ x ∶ recvChanNf T S ⊣ Γin′
    → AllUsed Γin′
    → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
    → AllUsed Γv′
    → L-RecvVal x v ⦂ Γin ⇒ Γv

  Label-RecvLab : ∀ {n k} {x : Fin n} {Γin Γv : Ctx [] n} {i : Fin k}
    → AllUsed Γin
    → AllUsed Γv
    → L-RecvLab x i ⦂ Γin ⇒ Γv

  Label-SendVal :
    ∀ {n} {x : Fin n}
      {Γin Γv Γin′ : Ctx [] n}
      {T : NfTy [] TLin} {S : NfTy [] SLin} {v : Value [] n}
    → Γin ⊢ˡ x ∶ sendChanNf T S ⊣ Γv
    → Γv ⊢ᵥ v ⇒ T ⊣ Γin′
    → AllUsed Γin′
    → L-SendVal x v ⦂ Γin ⇒ Γv

  Label-SendLab :
    ∀ {n k} {x : Fin n} {Γin Γin′ : Ctx [] n} {i : Fin k}
      {v : Variance} {P : NfTy [] KP} {S : NfTy [] SLin} 
    → Γin ⊢ˡ x ∶ selectInNf v i P S ⊣ Γin′
    → AllUsed Γin′
    → L-SendLab x i ⦂ Γin ⇒ Γin′

  Label-Close : ∀ {n} {x : Fin n} {Γin Γv : Ctx [] n}
    → AllUsed Γin
    → AllUsed Γv
    → L-Close x ⦂ Γin ⇒ Γv

extendUsed : ∀ (Θ : List (Ty [] SLin)) {n} → Ctx [] n → Ctx [] (length Θ + n)
extendUsed [] Γ = Γ
extendUsed (S ∷ Θ) Γ = B-Used (normalizeTy (SessLin S)) ▻ extendUsed Θ Γ

data FrameUpdate : ∀ {n Θ} → Label n Θ → Ctx [] n → Ctx [] (length Θ + n) → Set where
  FU-β : ∀ {n} {Γ : Ctx [] n}
    → FrameUpdate L-β Γ Γ

  FU-Fork : ∀ {n} {Γ : Ctx [] n} {v : Value [] n}
    → FrameUpdate (L-Fork v) Γ Γ

  FU-New : ∀ {n} {Γ : Ctx [] n} {S : Ty [] SLin}
    → FrameUpdate (L-New S) Γ (extendUsed (S ∷ T-Dual D-S S ∷ []) Γ)

  FU-RecvVal :
    ∀ {n} {Γ Γ′ : Ctx [] n} {x : Fin n} {v : Value [] n}
    → FrameUpdate (L-RecvVal x v) Γ Γ′

  FU-SendVal :
    ∀ {n} {Γ Γ′ : Ctx [] n} {x : Fin n} {v : Value [] n}
    → FrameUpdate (L-SendVal x v) Γ Γ′

  FU-RecvLab :
    ∀ {n k} {Γ Γ′ : Ctx [] n} {x : Fin n} {i : Fin k}
    → FrameUpdate (L-RecvLab x i) Γ Γ′

  FU-SendLab :
    ∀ {n k} {Γ Γ′ : Ctx [] n} {x : Fin n} {i : Fin k}
    → FrameUpdate (L-SendLab x i) Γ Γ′

  FU-Close : ∀ {n} {Γ : Ctx [] n} {x : Fin n}
    → FrameUpdate (L-Close x) Γ Γ

postulate
  frame-update-preserves-disjoint :
    ∀ {n Θ}
      {ℓ : Label n Θ}
      {Γ₀ Γf : Ctx [] n}
      {Γ₀′ Γf′ : Ctx [] (length Θ + n)}
    → FrameUpdate ℓ Γ₀ Γ₀′
    → FrameUpdate ℓ Γf Γf′
    → LinearDisjoint Γ₀ Γf
    → LinearDisjoint Γ₀′ Γf′

data Compatible :
  ∀ {n Θ}
    {Γ₀ : Ctx [] n} {Γ₁ : Ctx [] (length Θ + n)}
    {ℓ : Label n Θ}
  → (Γ₀ —ctx[ ℓ ]→ Γ₁)
  → {Γin Γv : Ctx [] n}
  → (ℓ ⦂ Γin ⇒ Γv)
  → Set where
  Compat-β :
    ∀ {n} {Γ₀ Γin Γv : Ctx [] n}
      {auin : AllUsed Γin}
      {auv : AllUsed Γv}
    → allUsedCtx Γ₀ ≡ Γin
    → Compatible {Γ₀ = Γ₀} {Γ₁ = Γ₀} {ℓ = L-β}
        Ctx-β
        (Label-β auin auv)

  Compat-New :
    ∀ {n} {Γ₀ Γin Γv : Ctx [] n} {S : Ty [] SLin}
      {auin : AllUsed Γin}
      {auv : AllUsed Γv}
    → allUsedCtx Γ₀ ≡ Γin
    → Compatible {Γ₀ = Γ₀} {ℓ = L-New S}
        (Ctx-New {Γ₀ = Γ₀} {S = S})
        (Label-New auin auv)

  Compat-Fork :
    ∀ {n} {Γ₀ Γin Γv Γv′ Γ₁ : Ctx [] n} {v : Value [] n}
      {Γlbl : Ctx [] n} {auin : AllUsed Γin} {aulbl : AllUsed Γlbl}
      {rm : RemoveCtx Γ₀ Γv Γ₁}
      {dv : Γv ⊢ E-Val v ⇐ linArrNf unitLinNf unitLinNf ⊣ Γv′}
      {auv : AllUsed Γv′}
    → allUsedCtx Γ₀ ≡ Γin
    → Compatible (Ctx-Fork rm dv auv) (Label-Fork auin aulbl)

  Compat-RecvVal :
    ∀ {n} {Γ₀ Γv Γv′ Γx Γ₁ Γin Γin′ : Ctx [] n}
      {x : Fin n} {T : NfTy [] TLin} {S : NfTy [] SLin} {v : Value [] n}
      {ld : LinearDisjoint Γ₀ Γv}
      {x∈ : Γ₀ ∋ˡ x ∶ recvChanNf T S}
      {rep : ReplaceAt Γ₀ x (B-Lin (sessNf S)) Γx}
      {merge : MergeCtx Γx Γv Γ₁}
      {take : Γin ⊢ˡ x ∶ recvChanNf T S ⊣ Γin′}
      {auin : AllUsed Γin′}
      {dv : Γv ⊢ᵥ v ⇒ T ⊣ Γv′}
      {au : AllUsed Γv′}
    → Compatible {Γ₀ = Γ₀} {Γ₁ = Γ₁} {ℓ = L-RecvVal x v}
        (Ctx-Rcv dv au ld x∈ rep merge) (Label-RecvVal take auin dv au)

  Compat-SendVal :
    ∀ {n} {Γ₀ Γin Γx Γv Γv′ Γ₁ : Ctx [] n}
      {x : Fin n} {T : NfTy [] TLin} {S : NfTy [] SLin} {v : Value [] n}
      {rm : RemoveCtx Γ₀ Γv Γx}
      {dv : Γv ⊢ᵥ v ⇒ T ⊣ Γv′}
      {auv : AllUsed Γv′}
      {x∈ : Γx ∋ˡ x ∶ sendChanNf T S}
      {rep : ReplaceAt Γx x (B-Lin (sessNf S)) Γ₁}
      {take : Γin ⊢ˡ x ∶ sendChanNf T S ⊣ Γv}
    → Compatible {Γ₀ = Γ₀} {Γ₁ = Γ₁} {ℓ = L-SendVal x v}
        (Ctx-Send rm dv auv x∈ rep) (Label-SendVal take dv auv)

  Compat-Close :
    ∀ {n} {Γ₀ Γin Γ₁ : Ctx [] n} {x : Fin n}
      {x∈ : Γ₀ ∋ˡ x ∶ normalizeTy EndLin}
      {rep : ReplaceAt Γ₀ x (B-Used (normalizeTy EndLin)) Γ₁}
      {Γv : Ctx [] n} {auin : AllUsed Γin} {au : AllUsed Γv}
    → allUsedCtx Γ₀ ≡ Γin
    → Compatible {Γ₀ = Γ₀} {Γ₁ = Γ₁} {ℓ = L-Close x}
        (Ctx-Close x∈ rep) (Label-Close auin au)

  Compat-Match :
    ∀ {n k}
      {ssin ssout : Subset.Subset (suc k)} {incl : ssin Subset.⊆ ssout}
      {Γ₀ Γin Γ₁ : Ctx [] n} {x : Fin n} {i : Fin (suc k)}
      {v : Variance} {P : NfTy [] KP} {S : NfTy [] SLin}
      {i∈ : i Subset.∈ ssout}
      {x∈ : Γ₀ ∋ˡ x ∶ MatchBranchInput ssin v P S}
      {rep : ReplaceAt Γ₀ x (B-Lin (MatchBranchOutput ssout v P S i i∈)) Γ₁}
      {Γv : Ctx [] n} {auin : AllUsed Γin} {au : AllUsed Γv}
    → allUsedCtx Γ₀ ≡ Γin
    → Compatible {Γ₀ = Γ₀} {Γ₁ = Γ₁} {ℓ = L-RecvLab x i}
        (Ctx-Match {ssin = ssin} {ssout = ssout} {incl = incl} {v = v} {P = P} {S = S} i∈ x∈ rep)
        (Label-RecvLab auin au)

  Compat-Select :
    ∀ {n k} {Γ₀ Γin Γin′ Γ₁ : Ctx [] n} {x : Fin n} {i : Fin k}
      {v : Variance} {P : NfTy [] KP} {S : NfTy [] SLin}
      {x∈ : Γ₀ ∋ˡ x ∶ selectInNf v i P S}
      {rep : ReplaceAt Γ₀ x (B-Lin (selectOutNf v i P S)) Γ₁}
      {take : Γin ⊢ˡ x ∶ selectInNf v i P S ⊣ Γin′}
      {au : AllUsed Γin′}
    → Compatible {Γ₀ = Γ₀} {Γ₁ = Γ₁} {ℓ = L-SendLab x i}
        (Ctx-Select {v = v} {P = P} {S = S} x∈ rep)
        {Γin = Γin} {Γv = Γin′}
        (Label-SendLab {v = v} {P = P} {S = S} take au)

data InputCompatible :
  ∀ {n Θ}
    (Γ₀ : Ctx [] n)
    {Γin Γv : Ctx [] n}
    {ℓ : Label n Θ}
  → (ℓ ⦂ Γin ⇒ Γv)
  → Set where
  IC-β :
    ∀ {n} {Γ₀ Γin : Ctx [] n} {Γv : Ctx [] n}
      {auin : AllUsed Γin} {auv : AllUsed Γv}
    → allUsedCtx Γ₀ ≡ Γin
    → InputCompatible Γ₀ (Label-β auin auv)

  IC-Fork :
    ∀ {n} {Γ₀ Γin : Ctx [] n} {Γv : Ctx [] n} {v : Value [] n}
      {auin : AllUsed Γin} {auv : AllUsed Γv}
    → allUsedCtx Γ₀ ≡ Γin
    → InputCompatible Γ₀ (Label-Fork {v = v} auin auv)

  IC-New :
    ∀ {n} {Γ₀ Γin : Ctx [] n} {Γv : Ctx [] n} {S : Ty [] SLin}
      {auin : AllUsed Γin} {auv : AllUsed Γv}
    → allUsedCtx Γ₀ ≡ Γin
    → InputCompatible Γ₀ (Label-New {S = S} auin auv)

  IC-RecvVal :
    ∀ {n} {Γ₀ Γin Γr Γv : Ctx [] n}
      {x : Fin n} {v : Value [] n}
      {T : NfTy [] TLin} {S : NfTy [] SLin}
      {Γin′ Γv′ : Ctx [] n}
      {take : Γin ⊢ˡ x ∶ recvChanNf T S ⊣ Γin′}
      {auin : AllUsed Γin′}
      {dv : Γv ⊢ᵥ v ⇒ T ⊣ Γv′}
      {auv : AllUsed Γv′}
    → RemoveCtx Γ₀ Γin Γr
    → InputCompatible Γ₀ (Label-RecvVal take auin dv auv)

  IC-RecvLab :
    ∀ {n k} {Γ₀ Γin : Ctx [] n} {Γv : Ctx [] n} {x : Fin n} {i : Fin k}
      {auin : AllUsed Γin} {auv : AllUsed Γv}
    → allUsedCtx Γ₀ ≡ Γin
    → InputCompatible Γ₀ {ℓ = L-RecvLab x i} (Label-RecvLab auin auv)

  IC-SendVal :
    ∀ {n} {Γ₀ Γin Γr Γv : Ctx [] n}
      {x : Fin n} {v : Value [] n}
      {T : NfTy [] TLin} {S : NfTy [] SLin}
      {take : Γin ⊢ˡ x ∶ sendChanNf T S ⊣ Γv}
      {dv : Γv ⊢ᵥ v ⇒ T ⊣ Γr}
      {auv : AllUsed Γr}
    → RemoveCtx Γ₀ Γin Γr
    → InputCompatible Γ₀ {ℓ = L-SendVal x v} (Label-SendVal take dv auv)

  IC-SendLab :
    ∀ {n k} {Γ₀ Γin Γr Γin′ : Ctx [] n} {x : Fin n} {i : Fin k}
      {v : Variance} {P : NfTy [] KP} {S : NfTy [] SLin}
      {take : Γin ⊢ˡ x ∶ selectInNf v i P S ⊣ Γin′}
      {au : AllUsed Γin′}
    → RemoveCtx Γ₀ Γin Γr
    → InputCompatible Γ₀ {Γin = Γin} {Γv = Γin′} {ℓ = L-SendLab x i}
        (Label-SendLab {v = v} {P = P} {S = S} take au)

  IC-Close :
    ∀ {n} {Γ₀ Γin : Ctx [] n} {Γv : Ctx [] n} {x : Fin n}
      {auin : AllUsed Γin} {auv : AllUsed Γv}
    → allUsedCtx Γ₀ ≡ Γin
    → InputCompatible Γ₀ {ℓ = L-Close x} (Label-Close auin auv)

data Extract : ∀ {n Θ} → Ctx [] n → Label n Θ → Ctx [] n → Set where
  Ex-β :
    ∀ {n} {Γ₀ : Ctx [] n}
    → Extract Γ₀ L-β (allUsedCtx Γ₀)

  Ex-Fork :
    ∀ {n} {Γ₀ : Ctx [] n} {v : Value [] n}
    → Extract Γ₀ (L-Fork v) (allUsedCtx Γ₀)

  Ex-New :
    ∀ {n} {Γ₀ : Ctx [] n} {S : Ty [] SLin}
    → Extract Γ₀ (L-New S) (allUsedCtx Γ₀)

  Ex-RecvVal :
    ∀ {n}
      {Γ₀ Γin Γr Γin′ : Ctx [] n}
      {x : Fin n} {v : Value [] n}
      {T : NfTy [] TLin} {S : NfTy [] SLin}
    → RemoveCtx Γ₀ Γin Γr
    → Γin ⊢ˡ x ∶ recvChanNf T S ⊣ Γin′
    → AllUsed Γin′
    → Extract Γ₀ (L-RecvVal x v) Γin

  Ex-RecvLab :
    ∀ {n k}
      {Γ₀ : Ctx [] n}
      {x : Fin n} {i : Fin k}
    → Extract Γ₀ (L-RecvLab x i) (allUsedCtx Γ₀)

  Ex-SendVal :
    ∀ {n}
      {Γ₀ Γin Γr Γv Γin′ : Ctx [] n}
      {x : Fin n} {v : Value [] n}
      {T : NfTy [] TLin} {S : NfTy [] SLin}
    → RemoveCtx Γ₀ Γin Γr
    → Γin ⊢ˡ x ∶ sendChanNf T S ⊣ Γv
    → Γv ⊢ᵥ v ⇒ T ⊣ Γin′
    → AllUsed Γin′
    → Extract Γ₀ (L-SendVal x v) Γin

  Ex-SendLab :
    ∀ {n k}
      {Γ₀ Γin Γr Γin′ : Ctx [] n}
      {x : Fin n} {i : Fin k}
      {v : Variance} {P : NfTy [] KP} {S : NfTy [] SLin}
    → RemoveCtx Γ₀ Γin Γr
    → Γin ⊢ˡ x ∶ selectInNf v i P S ⊣ Γin′
    → Extract Γ₀ (L-SendLab x i) Γin

  Ex-Close :
    ∀ {n}
      {Γ₀ : Ctx [] n}
      {x : Fin n}
    → Extract Γ₀ (L-Close x) (allUsedCtx Γ₀)

extract-remove :
  ∀ {n Θ}
    {Γ₀ Γin : Ctx [] n}
    {ℓ : Label n Θ}
  → Extract Γ₀ ℓ Γin
  → Σ (Ctx [] n) λ Γr → RemoveCtx Γ₀ Γin Γr
extract-remove Ex-β = _ , remove-allUsedCtx _
extract-remove Ex-Fork = _ , remove-allUsedCtx _
extract-remove Ex-New = _ , remove-allUsedCtx _
extract-remove (Ex-RecvVal rm _ _) = _ , rm
extract-remove Ex-RecvLab = _ , remove-allUsedCtx _
extract-remove (Ex-SendVal rm _ _ _) = _ , rm
extract-remove (Ex-SendLab rm _) = _ , rm
extract-remove Ex-Close = _ , remove-allUsedCtx _

extract-disjoint-active :
  ∀ {n Θ}
    {Γ₀ Γ₂ Γin G : Ctx [] n}
    {ℓ : Label n Θ}
  → RemoveCtx Γ₀ G Γ₂
  → Extract Γ₂ ℓ Γin
  → LinearDisjoint G Γin
extract-disjoint-active r ex with extract-remove ex
... | Γr , rin =
  sym-disjoint
    (remove-removed-disjoint rin (sym-disjoint (remove-linear r)))

ctx-step-preserves-disjoint :
    ∀ {n Θ}
      {Γ₀ : Ctx [] n} {Γ₁ : Ctx [] (length Θ + n)}
      {Γin Γv Γf : Ctx [] n}
      {ℓ : Label n Θ}
    → (step : Γ₀ —ctx[ ℓ ]→ Γ₁)
    → (lbl : ℓ ⦂ Γin ⇒ Γv)
    → Compatible step lbl
    → LinearDisjoint Γ₀ Γf
    → LinearDisjoint Γv Γf
    → Σ (Ctx [] (length Θ + n)) λ Γf′ →
        FrameUpdate ℓ Γf Γf′ × LinearDisjoint Γ₁ Γf′
ctx-step-preserves-disjoint Ctx-β (Label-β _ _) (Compat-β _) ld0 ldv =
  _ , FU-β , ld0
ctx-step-preserves-disjoint {Γ₀ = Γ₀} {Γf = Γf} (Ctx-New {S = S}) (Label-New _ _) (Compat-New _) ld0 ldv =
  let
    eq-nf : NormalTypes.fromNormalTy (nf-normal-type ⊕
                                     (λ x₁ → dualizable-sub (d?⊥ x₁) (≤k-step (≤p-step <p-st) ≤m-refl))
                                     (T-Dual D-S ⌞ normalizeTy S ⌟))
          ≡
            NormalTypes.fromNormalTy (nf-normal-type ⊕
                                     (λ x₁ → dualizable-sub (d?⊥ x₁) (≤k-step (≤p-step <p-st) ≤m-refl))
                                     (T-Dual D-S S))
    eq-nf =
      let
        km = ≤k-step (≤p-step <p-st) ≤m-refl
        d?S = λ x₁ → dualizable-sub (d?⊥ x₁) km

        S⁺ = nf ⊕ d?⊥ S

        norm-eq :
          ⌞ normalizeTy S ⌟ ≡ S⁺
        norm-eq =
          NormalTypes.nfTyTy-fromNormalTy (nf-normal-type ⊕ d?⊥ S)

        minus-eq :
          nf ⊝ (λ _ → D-S) S⁺ ≡ nf ⊝ (λ _ → D-S) S
        minus-eq =
          nf-complete- (λ _ → D-S) (nf-sound+ S)

        dual-conv :
          T-Dual D-S S⁺ ≡c T-Dual D-S S
        dual-conv =
          ≡c-trns
            (dual-tinv S⁺)
            (≡c-trns
              (≡c-symm (nf-sound- {f = λ _ → D-S} S⁺))
              (≡c-trns
                (≡c-refl-eq minus-eq)
                (≡c-trns
                  (nf-sound- {f = λ _ → D-S} S)
                  (≡c-symm (dual-tinv S)))))

        eq-raw :
          NormalTypes.nfTyTy
            (NormalTypes.fromNormalTy
              (nf-normal-type ⊕ d?S (T-Dual D-S ⌞ normalizeTy S ⌟)))
            ≡
          NormalTypes.nfTyTy
            (NormalTypes.fromNormalTy
              (nf-normal-type ⊕ d?S (T-Dual D-S S)))
        eq-raw =
          trans
            (NormalTypes.nfTyTy-fromNormalTy
              (nf-normal-type ⊕ d?S (T-Dual D-S ⌞ normalizeTy S ⌟)))
            (trans
              (trans
                (cong
                  (λ X → nf ⊕ d?S (T-Dual D-S X))
                  norm-eq)
                (nf-complete d?S d?S dual-conv))
              (sym
                (NormalTypes.nfTyTy-fromNormalTy
                  (nf-normal-type ⊕ d?S (T-Dual D-S S)))))
      in
      NormalTypes.nfTyTy-injective eq-raw
  in
  _ , FU-New ,
  subst
    (LinearDisjoint
      (B-Lin (normalizeTy (SessLin S)) ▻ (B-Lin (dualSessNf (normalizeTy S)) ▻ Γ₀)))
    (cong (B-Used (normalizeTy (SessLin S)) ▻_)
      (cong (λ X → B-Used X ▻ Γf)
        (cong (NormalTypes.N-Sub (≤k-step (≤p-step <p-st) ≤m-refl))
          eq-nf)))
    (LD-live-used (LD-live-used ld0))
ctx-step-preserves-disjoint (Ctx-Fork rm _ _) (Label-Fork _ _) (Compat-Fork _) ld0 ldv =
  _ , FU-Fork , remove-preserves-disjoint rm ld0
ctx-step-preserves-disjoint
  (Ctx-Rcv _ _ _ x∈ rep merge)
  (Label-RecvVal _ _ _ _)
  Compat-RecvVal
  ld0 ldv
  with replace-preserves-disjoint x∈ ld0 rep
... | Γf′ , repf , ldx =
  Γf′ , FU-RecvVal ,
    merge-preserves-disjoint
      merge
      ldx
      (subst (LinearDisjoint _) (replace-used-eq x∈ ld0 repf) ldv)
ctx-step-preserves-disjoint
  (Ctx-Send rm _ _ x∈ rep)
  (Label-SendVal _ _ _)
  Compat-SendVal
  ld0 ldv
  with replace-preserves-disjoint x∈ (remove-preserves-disjoint rm ld0) rep
... | Γf′ , repf , ld′ =
  Γf′ , FU-SendVal , ld′
ctx-step-preserves-disjoint
  (Ctx-Close x∈ rep)
  (Label-Close _ _)
  (Compat-Close _)
  ld0 ldv =
  _ , FU-Close , replace-used-preserves-disjoint x∈ ld0 rep
ctx-step-preserves-disjoint
  (Ctx-Match _ x∈ rep)
  (Label-RecvLab _ _)
  (Compat-Match _)
  ld0 ldv
  with replace-preserves-disjoint x∈ ld0 rep
... | Γf′ , repf , ld′ =
  Γf′ , FU-RecvLab , ld′
ctx-step-preserves-disjoint
  (Ctx-Select {P = P} {S = S} x∈ rep)
  (Label-SendLab {v = v} {P = P} {S = S} _ _)
  (Compat-Select {v = v} {P = P} {S = S})
  ld0 ldv
  with replace-preserves-disjoint x∈ ld0 rep
... | Γf′ , repf , ld′ =
  Γf′ , FU-SendLab , ld′
