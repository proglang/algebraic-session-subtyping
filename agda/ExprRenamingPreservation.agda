module ExprRenamingPreservation where

open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Subset as Subset
open import Data.List using (List)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Kinds
open import ExprSyntax using (Expr; Value)
open import ExprSubstitution using (Ren; extRen; renameExpr; renameValue; wkValue)
open import ExprNormalTyping
open import ExprTypingProperties using (lift-∋ᵘ; lift-take)

liftRen : ∀ (k : ℕ) {n} → Ren {k + n} {k + suc n}
liftRen zero = suc
liftRen (suc k) = extRen (liftRen k)

insertAt : ∀ {Δ n} (k : ℕ) → Binding Δ → Ctx Δ (k + n) → Ctx Δ (k + suc n)
insertAt zero b Γ = b ▻ Γ
insertAt (suc k) b (b′ ▻ Γ) = b′ ▻ insertAt k b Γ

wkCtx-insertAt :
  ∀ {Δ n K}
    (k : ℕ)
    (b : Binding Δ)
    (Γ : Ctx Δ (k + n))
  → wkCtx {K = K} (insertAt k b Γ) ≡ insertAt k (wkBinding {K = K} b) (wkCtx Γ)
wkCtx-insertAt zero b Γ = refl
wkCtx-insertAt (suc k) b (b′ ▻ Γ) =
  cong (wkBinding b′ ▻_) (wkCtx-insertAt k b Γ)

cast-value-ctx :
  ∀ {Δ n K}
    {Γ₁ Γ₂ Γ₁′ Γ₂′ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ K}
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  → Γ₁ ≡ Γ₁′
  → Γ₂ ≡ Γ₂′
  → Γ₁′ ⊢ᵥ v ⇒ T ⊣ Γ₂′
cast-value-ctx d refl refl = d

lift-∋ᵘ-at :
  ∀ {Δ n pk}
    (k : ℕ)
    (b : Binding Δ)
    {Γ : Ctx Δ (k + n)}
    {x : Fin (k + n)}
    {T : NfTy Δ (KV pk Un)}
  → Γ ∋ᵘ x ∶ T
  → insertAt k b Γ ∋ᵘ liftRen k x ∶ T
lift-∋ᵘ-at zero b x∈ = lift-∋ᵘ b x∈
lift-∋ᵘ-at (suc k) b hereᵘ = hereᵘ
lift-∋ᵘ-at (suc k) b (thereᵘˡ x∈) = thereᵘˡ (lift-∋ᵘ-at k b x∈)
lift-∋ᵘ-at (suc k) b (thereᵘᵘ x∈) = thereᵘᵘ (lift-∋ᵘ-at k b x∈)
lift-∋ᵘ-at (suc k) b (thereᵘ✖ x∈) = thereᵘ✖ (lift-∋ᵘ-at k b x∈)

lift-take-at :
  ∀ {Δ n pk}
    (k : ℕ)
    (b : Binding Δ)
    {Γ Γ′ : Ctx Δ (k + n)}
    {x : Fin (k + n)}
    {T : NfTy Δ (KV pk Lin)}
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
  → insertAt k b Γ ⊢ˡ liftRen k x ∶ T ⊣ insertAt k b Γ′
lift-take-at zero b take = lift-take b take
lift-take-at (suc k) b take-here = take-here
lift-take-at (suc k) b (take-thereˡ take) = take-thereˡ (lift-take-at k b take)
lift-take-at (suc k) b (take-thereᵘ take) = take-thereᵘ (lift-take-at k b take)
lift-take-at (suc k) b (take-there✖ take) = take-there✖ (lift-take-at k b take)

mutual

  ren-preserves-value :
    ∀ {Δ n K}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ Γ₂ : Ctx Δ (k + n)}
      {v : Value Δ (k + n)}
      {T : NfTy Δ K}
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
    → insertAt k b Γ₁ ⊢ᵥ renameValue (liftRen k) v ⇒ T ⊣ insertAt k b Γ₂

  ren-preserves-synth :
    ∀ {Δ n K}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ Γ₂ : Ctx Δ (k + n)}
      {e : Expr Δ (k + n)}
      {T : NfTy Δ K}
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
    → insertAt k b Γ₁ ⊢ renameExpr (liftRen k) e ⇒ T ⊣ insertAt k b Γ₂

  ren-preserves-check :
    ∀ {Δ n pk m}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ Γ₂ : Ctx Δ (k + n)}
      {e : Expr Δ (k + n)}
      {T : NfTy Δ (KV pk m)}
    → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
    → insertAt k b Γ₁ ⊢ renameExpr (liftRen k) e ⇐ T ⊣ insertAt k b Γ₂

  ren-preserves-value k b (TV-Const cT) = TV-Const cT
  ren-preserves-value k b (TV-Var-Lin take) =
    TV-Var-Lin (lift-take-at k b take)
  ren-preserves-value k b (TV-Var-Un x∈) =
    TV-Var-Un (lift-∋ᵘ-at k b x∈)
  ren-preserves-value k b (TV-Abs d) =
    TV-Abs (ren-preserves-synth (suc k) b d)
  ren-preserves-value k b (TV-Rec d) =
    TV-Rec (ren-preserves-check (suc k) b d)
  ren-preserves-value k b {Γ₁ = Γ₁} {Γ₂ = Γ₂} (TV-TAbs {K = K} d) =
    TV-TAbs
      (cast-value-ctx
        (ren-preserves-value k (wkBinding {K = K} b) d)
        (sym (wkCtx-insertAt {K = K} k b Γ₁))
        (sym (wkCtx-insertAt {K = K} k b Γ₂)))
  ren-preserves-value k b (TV-Pair d₁ d₂) =
    TV-Pair (ren-preserves-value k b d₁) (ren-preserves-value k b d₂)
  ren-preserves-value k b TV-Receive₁ = TV-Receive₁
  ren-preserves-value k b TV-Receive₂ = TV-Receive₂
  ren-preserves-value k b TV-Send₁ = TV-Send₁
  ren-preserves-value k b TV-Send₂ = TV-Send₂
  ren-preserves-value k b TV-Select₁ = TV-Select₁
  ren-preserves-value k b TV-Select₂ = TV-Select₂

  ren-preserves-synth k b (T-Val d) =
    T-Val (ren-preserves-value k b d)
  ren-preserves-synth k b (T-Pair d₁ d₂) =
    T-Pair (ren-preserves-synth k b d₁) (ren-preserves-synth k b d₂)
  ren-preserves-synth k b (T-App d₁ d₂) =
    T-App (ren-preserves-synth k b d₁) (ren-preserves-check k b d₂)
  ren-preserves-synth k b (T-LetUnit d₁ d₂) =
    T-LetUnit (ren-preserves-check k b d₁) (ren-preserves-synth k b d₂)
  ren-preserves-synth k b (T-LetPair d₁ d₂) =
    T-LetPair (ren-preserves-synth k b d₁) (ren-preserves-synth (suc (suc k)) b d₂)
  ren-preserves-synth k b
    (T-Match
      {Γ₂ = Γ₂}
      {Γ₃ = Γ₃}
      {k = k′}
      {ss = ss}
      {v = v}
      {ssbranches = ssbranches}
      {incl = incl}
      {ne = ne}
      {P = P}
      {S = S}
      {branches = branches}
      {V = V}
      {sub = sub}
      d bs j) =
    T-Match
      {Γ₂ = insertAt k b Γ₂}
      {Γ₃ = insertAt k b Γ₃}
      {ss = ss}
      {v = v}
      {ssbranches = ssbranches}
      {incl = incl}
      {ne = ne}
      {P = P}
      {S = S}
      {branches = λ i i∈ → renameExpr (liftRen (suc k)) (branches i i∈)}
      {V = V}
      {sub = sub}
      (ren-preserves-synth k b d)
      bs′
      j
    where
      bs′ :
        (i : Fin (suc k′))
        → (i∈ : i Subset.∈ ssbranches)
        → (MatchBranchOutput ssbranches v P S i i∈ ∷ˡ insertAt k b Γ₂)
            ⊢ renameExpr (liftRen (suc k)) (branches i i∈)
              ⇒ V i i∈
              ⊣ (B-Used (MatchBranchOutput ssbranches v P S i i∈) ▻ insertAt k b Γ₃)
      bs′ i i∈ = ren-preserves-synth (suc k) b (bs i i∈)
  ren-preserves-synth k b (T-TApp d) =
    T-TApp (ren-preserves-synth k b d)

  ren-preserves-check k b (T-Check d sub) =
    T-Check (ren-preserves-synth k b d) sub

wk-preserves-value :
  ∀ {Δ n K}
    (b : Binding Δ)
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ K}
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  → (b ▻ Γ₁) ⊢ᵥ wkValue v ⇒ T ⊣ (b ▻ Γ₂)
wk-preserves-value b d = ren-preserves-value 0 b d

wk-preserves-synth :
  ∀ {Δ n K}
    (b : Binding Δ)
    {Γ₁ Γ₂ : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ K}
  → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
  → (b ▻ Γ₁) ⊢ renameExpr suc e ⇒ T ⊣ (b ▻ Γ₂)
wk-preserves-synth b d = ren-preserves-synth 0 b d

wk-preserves-check :
  ∀ {Δ n pk m}
    (b : Binding Δ)
    {Γ₁ Γ₂ : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk m)}
  → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
  → (b ▻ Γ₁) ⊢ renameExpr suc e ⇐ T ⊣ (b ▻ Γ₂)
wk-preserves-check b d = ren-preserves-check 0 b d

postulate
  unren-preserves-value :
    ∀ {Δ n K}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ Γ₂ : Ctx Δ (k + n)}
      {v : Value Δ (k + n)}
      {T : NfTy Δ K}
    → insertAt k b Γ₁ ⊢ᵥ renameValue (liftRen k) v ⇒ T ⊣ insertAt k b Γ₂
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂

  unren-preserves-synth :
    ∀ {Δ n K}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ Γ₂ : Ctx Δ (k + n)}
      {e : Expr Δ (k + n)}
      {T : NfTy Δ K}
    → insertAt k b Γ₁ ⊢ renameExpr (liftRen k) e ⇒ T ⊣ insertAt k b Γ₂
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂

  unren-preserves-check :
    ∀ {Δ n pk m}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ Γ₂ : Ctx Δ (k + n)}
      {e : Expr Δ (k + n)}
      {T : NfTy Δ (KV pk m)}
    → insertAt k b Γ₁ ⊢ renameExpr (liftRen k) e ⇐ T ⊣ insertAt k b Γ₂
    → Γ₁ ⊢ e ⇐ T ⊣ Γ₂

unwk-preserves-value :
  ∀ {Δ n K}
    (b : Binding Δ)
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ K}
  → (b ▻ Γ₁) ⊢ᵥ wkValue v ⇒ T ⊣ (b ▻ Γ₂)
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
unwk-preserves-value b d = unren-preserves-value 0 b d

unwk-preserves-synth :
  ∀ {Δ n K}
    (b : Binding Δ)
    {Γ₁ Γ₂ : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ K}
  → (b ▻ Γ₁) ⊢ renameExpr suc e ⇒ T ⊣ (b ▻ Γ₂)
  → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
unwk-preserves-synth b d = unren-preserves-synth 0 b d

unwk-preserves-check :
  ∀ {Δ n pk m}
    (b : Binding Δ)
    {Γ₁ Γ₂ : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk m)}
  → (b ▻ Γ₁) ⊢ renameExpr suc e ⇐ T ⊣ (b ▻ Γ₂)
  → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
unwk-preserves-check b d = unren-preserves-check 0 b d
