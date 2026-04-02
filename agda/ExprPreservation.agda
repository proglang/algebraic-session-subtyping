module ExprPreservation where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong; cong₂)

open import Kinds
open import Kits
open import Variance using (Variance)
open import Types using (Ty; Ty-Syntax; Ty-Traversal; fusion)
open import AlgorithmicSubtyping using (_<:ₜ_; <:ₜ-refl; <:ₜ-trans)
open import ExprSyntax using
  ( Expr
  ; E-TApp
  ; E-App
  ; E-Pair
  ; E-LetPair
  ; E-Match
  ; E-LetUnit
  ; E-Val
  ; Value
  ; V-Abs
  ; V-Const
  ; V-Pair
  ; V-Rec
  ; V-Receive₁
  ; V-Send₁
  ; V-Send₂
  ; V-Send₃
  ; V-Select₁
  ; V-Select₂
  ; V-TAbs
  ; V-Var
  ; C-Receive
  ; C-Send
  ; C-Select
  )
open import ExprSemantics using
  ( Label
  ; L-β
  ; L-RecvLab
  ; _—[_]→_
  ; Act-App
  ; Act-TApp
  ; Act-LetPair
  ; Act-LetUnit
  ; Act-PairV
  ; Act-Rec
  ; Act-Receive₁
  ; Act-Receive₂
  ; Act-Send₁
  ; Act-Send₂
  ; Act-Send₃
  ; Act-Match
  ; Act-Select₁
  ; Act-Select₂
  ; Act-AppL
  ; Act-AppR
  ; Act-MatchE
  ; Act-LetPairE
  ; Act-PairL
  ; Act-PairR
  ; Act-LetUnitE
  ; Act-TAppE
  )
open import ExprSubstitution using (substExpr; substExpr₂; substTyValue; substValue)
open import ExprNormalTyping
open import ExprSubstitutionTyping using
  ( substTy-preserves-value
  ; subst-check-preserves-synth
  ; subst2-preserves-synth
  ; subst-var-preserves-synth
  ; rec-unfold-preserves-value
  ; substTyNf
  ; substTyBinding
  ; substTyCtx
  ; substTy-normalizeTy
  ; nfTy-eq
  ; nfProto-eq
  )

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (⋯-id)
open CTraversal record { fusion = fusion }

infixr 5 _++_

_++_ : ∀ {Δ n m} → Ctx Δ n → Ctx Δ m → Ctx Δ (n + m)
∅ ++ Γ₂ = Γ₂
(b ▻ Γ₁) ++ Γ₂ = b ▻ (Γ₁ ++ Γ₂)

usedCtx : ∀ {Δ n} → Ctx Δ n → Ctx Δ n
usedCtx ∅ = ∅
usedCtx (_ ▻ Γ) = B-Used ▻ usedCtx Γ

-- A positional three-way split of a context.
-- Each live binding belongs to exactly one component; the other two record
-- that position as already unavailable via `B-Used`.
-- This matches the intended reading of the paper's Γ₁, Γ₂, Γ₃ decomposition
-- without assuming the three parts are contiguous slices.

data Split3 {Δ} : ∀ {n} → Ctx Δ n → Ctx Δ n → Ctx Δ n → Ctx Δ n → Set where
  S3-∅ : Split3 ∅ ∅ ∅ ∅

  S3-1 : ∀ {n} {Γ Γ₁ Γ₂ Γ₃ : Ctx Δ n} {b : Binding Δ}
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Split3 (b ▻ Γ) (b ▻ Γ₁) (B-Used ▻ Γ₂) (B-Used ▻ Γ₃)

  S3-2 : ∀ {n} {Γ Γ₁ Γ₂ Γ₃ : Ctx Δ n} {b : Binding Δ}
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Split3 (b ▻ Γ) (B-Used ▻ Γ₁) (b ▻ Γ₂) (B-Used ▻ Γ₃)

  S3-3 : ∀ {n} {Γ Γ₁ Γ₂ Γ₃ : Ctx Δ n} {b : Binding Δ}
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Split3 (b ▻ Γ) (B-Used ▻ Γ₁) (B-Used ▻ Γ₂) (b ▻ Γ₃)

  S3-used : ∀ {n} {Γ Γ₁ Γ₂ Γ₃ : Ctx Δ n}
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Split3 (B-Used ▻ Γ) (B-Used ▻ Γ₁) (B-Used ▻ Γ₂) (B-Used ▻ Γ₃)

-- The contiguous presentation used below is a special case of `Split3`.

split3-++ : ∀ {Δ n₁ n₂ n₃} (Γ₁ : Ctx Δ n₁) (Γ₂ : Ctx Δ n₂) (Γ₃ : Ctx Δ n₃)
  → Split3 ((Γ₁ ++ Γ₂) ++ Γ₃)
           ((Γ₁ ++ usedCtx Γ₂) ++ usedCtx Γ₃)
           ((usedCtx Γ₁ ++ Γ₂) ++ usedCtx Γ₃)
           ((usedCtx Γ₁ ++ usedCtx Γ₂) ++ Γ₃)
split3-++ ∅ Γ₂ Γ₃ = split3-++-right Γ₂ Γ₃
  where
    split3-++-right : ∀ {Δ n₂ n₃} (Γ₂ : Ctx Δ n₂) (Γ₃ : Ctx Δ n₃)
      → Split3 (Γ₂ ++ Γ₃)
               (usedCtx Γ₂ ++ usedCtx Γ₃)
               (Γ₂ ++ usedCtx Γ₃)
               (usedCtx Γ₂ ++ Γ₃)
    split3-++-right ∅ Γ₃ = split3-++-thread Γ₃
      where
        split3-++-thread : ∀ {Δ n₃} (Γ₃ : Ctx Δ n₃)
          → Split3 Γ₃ (usedCtx Γ₃) (usedCtx Γ₃) Γ₃
        split3-++-thread ∅ = S3-∅
        split3-++-thread (_ ▻ Γ₃) = S3-3 (split3-++-thread Γ₃)
    split3-++-right (_ ▻ Γ₂) Γ₃ = S3-2 (split3-++-right Γ₂ Γ₃)
split3-++ (_ ▻ Γ₁) Γ₂ Γ₃ = S3-1 (split3-++ Γ₁ Γ₂ Γ₃)

split3-allactive : ∀ {Δ n} (Γ : Ctx Δ n) → Split3 Γ (usedCtx Γ) Γ (usedCtx Γ)
split3-allactive ∅ = S3-∅
split3-allactive (B-Lin T ▻ Γ) = S3-2 (split3-allactive Γ)
split3-allactive (B-Un T ▻ Γ) = S3-2 (split3-allactive Γ)
split3-allactive (B-Used ▻ Γ) = S3-used (split3-allactive Γ)

data AllUsed {Δ} : ∀ {n} → Ctx Δ n → Set where
  AU-∅ : AllUsed ∅
  AU-used : ∀ {n} {Γ : Ctx Δ n}
    → AllUsed Γ
    → AllUsed (B-Used ▻ Γ)
  AU-un : ∀ {n} {Γ : Ctx Δ n} {K} {T : NfTy Δ K}
    → AllUsed Γ
    → AllUsed (B-Un T ▻ Γ)

-- This is the context-transition premise used in Theorem 4.1.
-- The current file only needs the interface of the relation; its concrete
-- rules can be added independently, following Fig. 8 of the report.

data _—ctx[_]→_ :
    ∀ {n₁ n₂ n₃ m₂}
    → Ctx [] n₂
    → Label ((n₁ + n₂) + n₃) ((n₁ + m₂) + n₃)
    → Ctx [] m₂
    → Set where
  Ctx-β : ∀ {n₁ n₃}
    → _—ctx[_]→_ {n₁} {0} {n₃} {0} ∅ L-β ∅

-- Generalized context transitions for the noncontiguous split presentation.
-- The active part has the full expression arity; inactive positions are marked
-- by `B-Used`.

allUsed-usedCtx : ∀ {Δ n} {Γ : Ctx Δ n} → AllUsed (usedCtx Γ)
allUsed-usedCtx {Γ = ∅} = AU-∅
allUsed-usedCtx {Γ = _ ▻ Γ} = AU-used allUsed-usedCtx

normalizeTy-id-local : ∀ {K} (T : NfTy [] K) → normalizeTy (⌞ T ⌟) ≡ T
normalizeTy-id-local {K = KV pk m} (mkNfTy T NT) = nfTy-eq (Types.nf-idempotent NT) _ NT
normalizeTy-id-local {K = KP} (mkNfTy T NT) = nfProto-eq (Types.nfp-idempotent NT) _ NT

substTy-wkNfTy-id : ∀ {K K′} (T : NfTy [] K) (U : Ty [] K′) → substTyNf (wkNfTy {K′ = K′} T) U ≡ T
substTy-wkNfTy-id {K′ = K′} (mkNfTy T NT) U =
  trans
    (substTy-normalizeTy (T ⋯ weakenᵣ K′) U)
    (trans
      (cong normalizeTy (wk-cancels-⦅⦆-⋯ T U))
      (normalizeTy-id-local (mkNfTy T NT)))

substTy-wkBinding-id : ∀ {K} (b : Binding []) (U : Ty [] K) → substTyBinding (wkBinding b) U ≡ b
substTy-wkBinding-id (B-Lin T) U = cong B-Lin (substTy-wkNfTy-id T U)
substTy-wkBinding-id (B-Un T) U = cong B-Un (substTy-wkNfTy-id T U)
substTy-wkBinding-id B-Used U = refl

substTy-wkCtx-id : ∀ {K n} (Γ : Ctx [] n) (U : Ty [] K) → substTyCtx (wkCtx Γ) U ≡ Γ
substTy-wkCtx-id ∅ U = refl
substTy-wkCtx-id (b ▻ Γ) U = cong₂ (λ b′ Γ′ → b′ ▻ Γ′) (substTy-wkBinding-id b U) (substTy-wkCtx-id Γ U)

refillˡ : ∀ {n K K′} {Γ₁ Γ₂ : Ctx [] n} {x : Fin n} {T : NfTy [] K}
  → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂
  → NfTy [] K′
  → Ctx [] n
refillˡ (take-here {Γ = Γ}) U = U ∷ˡ Γ
refillˡ (take-thereˡ {U = V} p) U = V ∷ˡ refillˡ p U
refillˡ (take-thereᵘ {U = V} p) U = V ∷ᵘ refillˡ p U
refillˡ (take-there✖ p) U = used∷ (refillˡ p U)

refillˡ-take : ∀ {n K K′} {Γ₁ Γ₂ : Ctx [] n} {x : Fin n} {T : NfTy [] K}
  (p : Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂) (U : NfTy [] K′)
  → refillˡ p U ⊢ˡ x ∶ U ⊣ Γ₂
refillˡ-take take-here U = take-here
refillˡ-take (take-thereˡ p) U = take-thereˡ (refillˡ-take p U)
refillˡ-take (take-thereᵘ p) U = take-thereᵘ (refillˡ-take p U)
refillˡ-take (take-there✖ p) U = take-there✖ (refillˡ-take p U)

data _—ctx⋆[_]→_ : ∀ {n m} → Ctx [] n → Label n m → Ctx [] m → Set where
  Ctx⋆-β : ∀ {n} {Γ : Ctx [] n}
    → Γ —ctx⋆[ L-β ]→ Γ

  Ctx⋆-RecvLab : ∀ {n k} {Γ Γ′ : Ctx [] n} {x : Fin n}
      {T : NfTy [] SLin} {B : Fin k → NfTy [] SLin} {i : Fin k}
    → (p : Γ ⊢ˡ x ∶ T ⊣ Γ′)
    → MatchBranches T B
    → Γ —ctx⋆[ L-RecvLab x i ]→ refillˡ p (B i)

record PresSynth {n m pk mult}
    (Γ₁ : Ctx [] n) (Γ₂ : Ctx [] n) (Γ₃ : Ctx [] n)
    (ℓ : Label n m) (e : Expr [] m) (T : NfTy [] (KV pk mult)) : Set where
  field
    Γ₂′    : Ctx [] m
    ctx-step : Γ₂ —ctx⋆[ ℓ ]→ Γ₂′
    Γ      : Ctx [] m
    Γ₁′    : Ctx [] m
    Γ₃′    : Ctx [] m
    T′     : NfTy [] (KV pk mult)
    split  : Split3 Γ Γ₁′ Γ₂′ Γ₃′
    synth  : Γ ⊢ e ⇒ T′ ⊣ Γ₃′
    subtype : normalTyOf T′ <:ₜ normalTyOf T

record PresCheck {n m pk mult}
    (Γ₁ : Ctx [] n) (Γ₂ : Ctx [] n) (Γ₃ : Ctx [] n)
    (ℓ : Label n m) (e : Expr [] m) (T : NfTy [] (KV pk mult)) : Set where
  field
    Γ₂′    : Ctx [] m
    ctx-step : Γ₂ —ctx⋆[ ℓ ]→ Γ₂′
    Γ      : Ctx [] m
    Γ₁′    : Ctx [] m
    Γ₃′    : Ctx [] m
    split  : Split3 Γ Γ₁′ Γ₂′ Γ₃′
    check  : Γ ⊢ e ⇐ T ⊣ Γ₃′

receive₁-rigid :
  ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {T : NfTy [] TLin}
  → Γ ⊢ E-TApp (E-Val (V-Const C-Receive)) U ⇒ T ⊣ Γ′
  → Γ ≡ Γ′
receive₁-rigid (T-TApp (T-Val (TV-Const _))) = refl

send₁-rigid :
  ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {T : NfTy [] TLin}
  → Γ ⊢ E-TApp (E-Val (V-Const C-Send)) U ⇒ T ⊣ Γ′
  → Γ ≡ Γ′
send₁-rigid (T-TApp (T-Val (TV-Const _))) = refl

postulate
  split-of-synth :
    ∀ {n pk mult}
      {Γ Γout : Ctx [] n}
      {e : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → Γ ⊢ e ⇒ T ⊣ Γout
    → Σ (Ctx [] n) λ Γ₁ →
        Σ (Ctx [] n) λ Γ₂ →
          Split3 Γ Γ₁ Γ₂ Γout

  receive₂-rigid :
    ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {S : Ty [] SLin} {T : NfTy [] TLin}
    → Γ ⊢ E-TApp (E-Val (V-Receive₁ U)) S ⇒ T ⊣ Γ′
    → Γ ≡ Γ′

  receive₁-ty :
    ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {T : NfTy [] TLin}
    → Γ ⊢ E-TApp (E-Val (V-Const C-Receive)) U ⇒ T ⊣ Γ′
    → T ≡ normalizeTy (ReceiveTy1 U)

  receive₂-ty :
    ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {S : Ty [] SLin} {T : NfTy [] TLin}
    → Γ ⊢ E-TApp (E-Val (V-Receive₁ U)) S ⇒ T ⊣ Γ′
    → T ≡ normalizeTy (ReceiveTy U S)

  send₁-ty :
    ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {T : NfTy [] TLin}
    → Γ ⊢ E-TApp (E-Val (V-Const C-Send)) U ⇒ T ⊣ Γ′
    → T ≡ normalizeTy (SendTy1 U)

  send₂-rigid :
    ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {S : Ty [] SLin} {T : NfTy [] TLin}
    → Γ ⊢ E-TApp (E-Val (V-Send₁ U)) S ⇒ T ⊣ Γ′
    → Γ ≡ Γ′

  send₂-ty :
    ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {S : Ty [] SLin} {T : NfTy [] TLin}
    → Γ ⊢ E-TApp (E-Val (V-Send₁ U)) S ⇒ T ⊣ Γ′
    → T ≡ normalizeTy (SendTy U S)

  send₃-pres :
    ∀ {n} {Γ Γ′ : Ctx [] n} {T : Ty [] TLin} {S : Ty [] SLin} {v : Value [] n}
      {U : NfTy [] TLin}
    → Γ ⊢ E-App (E-Val (V-Send₂ T S)) (E-Val v) ⇒ U ⊣ Γ′
    → Γ ⊢ᵥ V-Send₃ T S v ⇒ U ⊣ Γ′

  select₁-pres :
    ∀ {n k} {Γ Γ′ : Ctx [] n} {v : Variance} {i : Fin k} {P : Ty [] KP} {T : NfTy [] (KV KT Lin)}
    → Γ ⊢ E-TApp (E-Val (V-Const (C-Select v i))) P ⇒ T ⊣ Γ′
    → Γ ⊢ᵥ V-Select₁ v i P ⇒ T ⊣ Γ′

  select₂-pres :
    ∀ {n k} {Γ Γ′ : Ctx [] n} {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin}
      {T : NfTy [] (KV KT Lin)}
    → Γ ⊢ E-TApp (E-Val (V-Select₁ v i P)) S ⇒ T ⊣ Γ′
    → Γ ⊢ᵥ V-Select₂ v i P S ⇒ T ⊣ Γ′

  poly-sub-invert :
    ∀ {K m} {T : NfTy (K ∷ []) (KV KT m)} {U : NfTy [] (KV KT m)}
    → normalTyOf U <:ₜ normalTyOf (polyNf T)
    → Σ (NfTy (K ∷ []) (KV KT m)) λ T′ →
         U ≡ polyNf T′ × (normalTyOf T′ <:ₜ normalTyOf T)

  tapp-subtyping :
    ∀ {K m} {T₁ T₂ : NfTy (K ∷ []) (KV KT m)} {U : Ty [] K}
    → normalTyOf T₁ <:ₜ normalTyOf T₂
    → normalTyOf (normalizeTy (⌞ T₁ ⌟ ⋯ ⦅ U ⦆ₛ))
       <:ₜ
       normalTyOf (normalizeTy (⌞ T₂ ⌟ ⋯ ⦅ U ⦆ₛ))

  preserve⇒-split-tapp :
    ∀ {n m K mult}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] m}
      {T : NfTy (K ∷ []) (KV KT mult)} {U : Ty [] K} {ℓ : Label n m}
    → e₁ —[ ℓ ]→ e₂
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ e₁ ⇒ polyNf T ⊣ Γ₃
    → PresSynth Γ₁ Γ₂ Γ₃ ℓ (E-TApp e₂ U) (normalizeTy (⌞ T ⌟ ⋯ ⦅ U ⦆ₛ))

  preserve⇒-split-letunit :
    ∀ {n}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {e₁ e₁′ e₂ : Expr [] n}
      {T : NfTy [] TLin} {ℓ : Label n n}
    → e₁ —[ ℓ ]→ e₁′
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ E-LetUnit e₁ e₂ ⇒ T ⊣ Γ₃
    → PresSynth Γ₁ Γ₂ Γ₃ ℓ (E-LetUnit e₁′ e₂) T

  preserve⇒-split-pairL :
    ∀ {n}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {e₁ e₁′ e₂ : Expr [] n}
      {T : NfTy [] TLin} {ℓ : Label n n}
    → e₁ —[ ℓ ]→ e₁′
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ E-Pair e₁ e₂ ⇒ T ⊣ Γ₃
    → PresSynth Γ₁ Γ₂ Γ₃ ℓ (E-Pair e₁′ e₂) T

  preserve⇒-split-pairR :
    ∀ {n}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {v : Value [] n} {e₁ e₁′ : Expr [] n}
      {T : NfTy [] TLin} {ℓ : Label n n}
    → e₁ —[ ℓ ]→ e₁′
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ E-Pair (E-Val v) e₁ ⇒ T ⊣ Γ₃
    → PresSynth Γ₁ Γ₂ Γ₃ ℓ (E-Pair (E-Val v) e₁′) T

  preserve⇒-split-appL :
    ∀ {n}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {e₁ e₁′ e₂ : Expr [] n}
      {T : NfTy [] TLin} {ℓ : Label n n}
    → e₁ —[ ℓ ]→ e₁′
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ E-App e₁ e₂ ⇒ T ⊣ Γ₃
    → PresSynth Γ₁ Γ₂ Γ₃ ℓ (E-App e₁′ e₂) T

  preserve⇒-split-appR :
    ∀ {n}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {v : Value [] n} {e₁ e₁′ : Expr [] n}
      {T : NfTy [] TLin} {ℓ : Label n n}
    → e₁ —[ ℓ ]→ e₁′
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ E-App (E-Val v) e₁ ⇒ T ⊣ Γ₃
    → PresSynth Γ₁ Γ₂ Γ₃ ℓ (E-App (E-Val v) e₁′) T

  preserve⇒-split-match :
    ∀ {n k}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {e e′ : Expr [] n} {branches : Fin k → Expr [] (Data.Nat.suc n)}
      {T : NfTy [] TLin} {ℓ : Label n n}
    → e —[ ℓ ]→ e′
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ E-Match e branches ⇒ T ⊣ Γ₃
    → PresSynth Γ₁ Γ₂ Γ₃ ℓ (E-Match e′ branches) T

  preserve⇒-split-letpair :
    ∀ {n}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {e e′ : Expr [] n} {body : Expr [] (Data.Nat.suc (Data.Nat.suc n))}
      {T : NfTy [] TLin} {ℓ : Label n n}
    → e —[ ℓ ]→ e′
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ E-LetPair e body ⇒ T ⊣ Γ₃
    → PresSynth Γ₁ Γ₂ Γ₃ ℓ (E-LetPair e′ body) T

  preserve⇒-split-matchβ :
    ∀ {n k}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {x : Fin n} {branches : Fin k → Expr [] (Data.Nat.suc n)} {i : Fin k}
      {U : NfTy [] TLin}
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ E-Match (E-Val (V-Var x)) branches ⇒ U ⊣ Γ₃
    → PresSynth Γ₁ Γ₂ Γ₃ (L-RecvLab x i) (substExpr (branches i) (V-Var x)) U

postulate
  preserve⇒-split-hard :
    ∀ {n m pk mult}
      {Γ Γ₁ Γ₂ Γ₃ Γout : Ctx [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] m} {T : NfTy [] (KV pk mult)} {ℓ : Label n m}
    → e₁ —[ ℓ ]→ e₂
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ e₁ ⇒ T ⊣ Γout
    → PresSynth Γ₁ Γ₂ Γ₃ ℓ e₂ T

  preserve⇐-split-hard :
    ∀ {n m pk mult}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] m}
      {T : NfTy [] (KV pk mult)} {ℓ : Label n m}
    → e₁ —[ ℓ ]→ e₂
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ e₁ ⇐ T ⊣ Γ₃
    → PresCheck Γ₁ Γ₂ Γ₃ ℓ e₂ T

  preserve⇒-hard :
    ∀ {n₁ n₂ n₃ m₂ pk m}
      {Γ₁ : Ctx [] n₁} {Γ₂ : Ctx [] n₂} {Γ₂′ : Ctx [] m₂} {Γ₃ : Ctx [] n₃}
      {e₁ : Expr [] ((n₁ + n₂) + n₃)} {e₂ : Expr [] ((n₁ + m₂) + n₃)}
      {T : NfTy [] (KV pk m)} {ℓ : Label ((n₁ + n₂) + n₃) ((n₁ + m₂) + n₃)}
    → e₁ —[ ℓ ]→ e₂
    → ((Γ₁ ++ Γ₂) ++ Γ₃) ⊢ e₁ ⇒ T ⊣ ((usedCtx (Γ₁ ++ Γ₂)) ++ Γ₃)
    → _—ctx[_]→_ {n₁} {n₂} {n₃} {m₂} Γ₂ ℓ Γ₂′
    → Σ (NfTy [] (KV pk m)) λ T′ →
        (((Γ₁ ++ Γ₂′) ++ Γ₃) ⊢ e₂ ⇒ T′ ⊣ ((usedCtx (Γ₁ ++ Γ₂′)) ++ Γ₃)) ×
        (normalTyOf T′ <:ₜ normalTyOf T)

preserve⇒-split-appβ :
  ∀ {n}
    {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
    {T : Ty [] TLin} {e : Expr [] (Data.Nat.suc n)} {v : Value [] n}
    {U : NfTy [] TLin}
  → Split3 Γ Γ₁ Γ₂ Γ₃
  → Γ ⊢ E-App (E-Val (V-Abs T e)) (E-Val v) ⇒ U ⊣ Γ₃
  → PresSynth Γ₁ Γ₂ Γ₃ L-β (substExpr e v) U
preserve⇒-split-appβ {Γ = Γ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = T} {e = e} {v = v} {U = U}
  split (T-App (T-Val tv) q)
  with abs-inversion tv
... | U₀ , eq , p
  with linArrNf-injective eq
... | refl , refl =
  record
    { Γ₂′ = Γ₂
    ; ctx-step = Ctx⋆-β
    ; Γ = Γ
    ; Γ₁′ = Γ₁
    ; Γ₃′ = Γ₃
    ; T′ = U₀
    ; split = split
    ; synth = subst-check-preserves-synth
        {Γ₁ = Γ} {Γ₃ = Γ₃}
        {T = T} {v = v} {e = e} {U = U₀}
        q p
    ; subtype = <:ₜ-refl (normalTyOf U₀)
    }

preserve⇒-split-recβ :
  ∀ {n}
    {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
    {T : Ty [] TLin} {v : Value [] (Data.Nat.suc n)} {u : Expr [] n}
    {U : NfTy [] TLin}
  → Split3 Γ Γ₁ Γ₂ Γ₃
  → Γ ⊢ E-App (E-Val (V-Rec T v)) u ⇒ U ⊣ Γ₃
  → PresSynth Γ₁ Γ₂ Γ₃ L-β (E-App (E-Val (substValue v (V-Rec T v))) u) U
preserve⇒-split-recβ {Γ = Γ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = T} {v = v} {u = u} {U = U}
  split (T-App (T-Val tv) q)
  with rec-inversion tv
... | refl , eq , p =
  record
    { Γ₂′ = Γ₂
    ; ctx-step = Ctx⋆-β
    ; Γ = Γ
    ; Γ₁′ = Γ₁
    ; Γ₃′ = Γ₃
    ; T′ = U
    ; split = split
    ; synth = T-App
        (T-Val
          (subst
            (λ X → Γ ⊢ᵥ substValue v (V-Rec T v) ⇒ X ⊣ Γ)
            (sym eq)
            (rec-unfold-preserves-value (TV-Rec p))))
        q
    ; subtype = <:ₜ-refl (normalTyOf U)
    }

preserve⇒-split-letpairβ :
  ∀ {n}
    {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
    {u v : Value [] n} {e : Expr [] (Data.Nat.suc (Data.Nat.suc n))}
    {U : NfTy [] TLin}
  → Split3 Γ Γ₁ Γ₂ Γ₃
  → Γ ⊢ E-LetPair (E-Val (V-Pair u v)) e ⇒ U ⊣ Γ₃
  → PresSynth Γ₁ Γ₂ Γ₃ L-β (substExpr₂ e u v) U
preserve⇒-split-letpairβ {Γ = Γ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} {u = u} {v = v} {e = e} {U = U}
  split (T-LetPair {T = T} {U = U′} (T-Val tv) body)
  with pair-inversion′ {T = T} {U = U′} tv
... | Γmid , pu , pv =
  record
    { Γ₂′ = Γ₂
    ; ctx-step = Ctx⋆-β
    ; Γ = Γ
    ; Γ₁′ = Γ₁
    ; Γ₃′ = Γ₃
    ; T′ = U
    ; split = split
    ; synth = subst2-preserves-synth pu pv body
    ; subtype = <:ₜ-refl (normalTyOf U)
    }

preserve⇒-split-tappβ :
  ∀ {n K m}
    {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
    {T : Ty [] K} {v : Value (K ∷ []) n}
    {U : NfTy [] (KV KT m)}
  → Split3 Γ Γ₁ Γ₂ Γ₃
  → Γ ⊢ E-TApp (E-Val (V-TAbs K v)) T ⇒ U ⊣ Γ₃
  → PresSynth Γ₁ Γ₂ Γ₃ L-β (E-Val (substTyValue v T)) U
preserve⇒-split-tappβ {Γ = Γ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = T} {v = v}
  split (T-TApp {T = T₁} {U = T} (T-Val tv))
  with tabs-inversion tv
... | mkNfTy T₀ N₀ , eq , p
  rewrite polyNf-injective eq =
  record
    { Γ₂′ = Γ₂
    ; ctx-step = Ctx⋆-β
    ; Γ = Γ
    ; Γ₁′ = Γ₁
    ; Γ₃′ = Γ₃
    ; T′ = normalizeTy (T₀ ⋯ ⦅ T ⦆ₛ)
    ; split = split
    ; synth = T-Val
        (subst
          (λ X → Γ ⊢ᵥ substTyValue v T ⇒ normalizeTy (T₀ ⋯ ⦅ T ⦆ₛ) ⊣ X)
          (substTy-wkCtx-id Γ₃ T)
          (subst
            (λ X → X ⊢ᵥ substTyValue v T ⇒ normalizeTy (T₀ ⋯ ⦅ T ⦆ₛ) ⊣ substTyCtx (wkCtx Γ₃) T)
            (substTy-wkCtx-id Γ T)
            (substTy-preserves-value p)))
    ; subtype = <:ₜ-refl (normalTyOf (normalizeTy (T₀ ⋯ ⦅ T ⦆ₛ)))
    }

postulate
  preserve⇒-matchβ-exists :
    ∀ {n k}
      {Γ Γout : Ctx [] n}
      {x : Fin n} {branches : Fin k → Expr [] (Data.Nat.suc n)} {i : Fin k}
      {U : NfTy [] TLin}
    → Γ ⊢ E-Match (E-Val (V-Var x)) branches ⇒ U ⊣ Γout
    → Σ (Ctx [] n) λ Γ₁ →
        Σ (Ctx [] n) λ Γ₂ →
          Σ (Ctx [] n) λ Γ₃ →
            PresSynth Γ₁ Γ₂ Γ₃ (L-RecvLab x i) (substExpr (branches i) (V-Var x)) U

mutual

  preserve⇒-split′ :
    ∀ {n m pk mult}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] m}
      {T : NfTy [] (KV pk mult)} {ℓ : Label n m}
    → e₁ —[ ℓ ]→ e₂
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ e₁ ⇒ T ⊣ Γ₃
    → PresSynth Γ₁ Γ₂ Γ₃ ℓ e₂ T

  preserve⇒-split′ {pk = KT} {mult = Lin}
    (Act-App {T = T} {e = e} {v = v}) split synth =
    preserve⇒-split-appβ split synth

  preserve⇒-split′ {pk = KT}
    (Act-TApp {T = T} {v = v}) split synth =
    preserve⇒-split-tappβ split synth

  preserve⇒-split′ {pk = KT} {mult = Lin}
    (Act-LetPair {u = u} {v = v} {e = e}) split synth =
    preserve⇒-split-letpairβ split synth

  preserve⇒-split′ {pk = KT} {mult = Lin}
    (Act-Rec {T = T} {v = v} {u = u}) split synth =
    preserve⇒-split-recβ split synth

  preserve⇒-split′ {pk = KT} {mult = Lin}
    (Act-Match {x = x} {branches = branches} {i = i}) split synth =
    preserve⇒-split-matchβ split synth

  preserve⇒-split′ (Act-TAppE {K = K} {T = U} step) split (T-TApp synth) =
    preserve⇒-split-tapp step split synth

  preserve⇒-split′ {pk = KT} {mult = Lin} (Act-LetUnitE step) split synth =
    preserve⇒-split-letunit step split synth

  preserve⇒-split′ {pk = KT} {mult = Lin} (Act-PairL step) split synth =
    preserve⇒-split-pairL step split synth

  preserve⇒-split′ {pk = KT} {mult = Lin} (Act-PairR step) split synth =
    preserve⇒-split-pairR step split synth

  preserve⇒-split′ {pk = KT} {mult = Lin} (Act-AppL step) split synth =
    preserve⇒-split-appL step split synth

  preserve⇒-split′ {pk = KT} {mult = Lin} (Act-AppR step) split synth =
    preserve⇒-split-appR step split synth

  preserve⇒-split′ {pk = KT} {mult = Lin} (Act-MatchE step) split synth =
    preserve⇒-split-match step split synth

  preserve⇒-split′ {pk = KT} {mult = Lin} (Act-LetPairE step) split synth =
    preserve⇒-split-letpair step split synth

  preserve⇒-split′ step split synth = preserve⇒-split-hard step split synth

  preserve⇐-split′ :
    ∀ {n m pk mult}
      {Γ Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] m}
      {T : NfTy [] (KV pk mult)} {ℓ : Label n m}
    → e₁ —[ ℓ ]→ e₂
    → Split3 Γ Γ₁ Γ₂ Γ₃
    → Γ ⊢ e₁ ⇐ T ⊣ Γ₃
    → PresCheck Γ₁ Γ₂ Γ₃ ℓ e₂ T

  preserve⇐-split′ step split (T-Check synth U<:T)
    with preserve⇒-split′ step split synth
  ... | ps =
    record
      { Γ₂′ = PresSynth.Γ₂′ ps
      ; ctx-step = PresSynth.ctx-step ps
      ; Γ = PresSynth.Γ ps
      ; Γ₁′ = PresSynth.Γ₁′ ps
      ; Γ₃′ = PresSynth.Γ₃′ ps
      ; split = PresSynth.split ps
      ; check = T-Check (PresSynth.synth ps) (<:ₜ-trans (PresSynth.subtype ps) U<:T)
      }

preserve⇒-split :
  ∀ {n m pk mult}
    {Γ Γout : Ctx [] n}
    {e₁ : Expr [] n} {e₂ : Expr [] m}
    {T : NfTy [] (KV pk mult)} {ℓ : Label n m}
  → e₁ —[ ℓ ]→ e₂
  → Γ ⊢ e₁ ⇒ T ⊣ Γout
  → Σ (Ctx [] n) λ Γ₁ →
      Σ (Ctx [] n) λ Γ₂ →
        Σ (Ctx [] n) λ Γ₃ →
          PresSynth Γ₁ Γ₂ Γ₃ ℓ e₂ T
preserve⇒-split {pk = KT} {mult = Lin}
  (Act-Match {x = x} {branches = branches} {i = i}) synth =
  preserve⇒-matchβ-exists synth
preserve⇒-split step synth
  with split-of-synth synth
... | Γ₁ , Γ₂ , split = Γ₁ , Γ₂ , _ , preserve⇒-split′ step split synth

preserve⇐-split :
  ∀ {n m pk mult}
    {Γ Γout : Ctx [] n}
    {e₁ : Expr [] n} {e₂ : Expr [] m}
    {T : NfTy [] (KV pk mult)} {ℓ : Label n m}
  → e₁ —[ ℓ ]→ e₂
  → Γ ⊢ e₁ ⇐ T ⊣ Γout
  → Σ (Ctx [] n) λ Γ₁ →
      Σ (Ctx [] n) λ Γ₂ →
        Σ (Ctx [] n) λ Γ₃ →
          PresCheck Γ₁ Γ₂ Γ₃ ℓ e₂ T
preserve⇐-split step (T-Check synth U<:T)
  with preserve⇒-split step synth
... | Γ₁ , Γ₂ , Γ₃ , ps =
  Γ₁ , Γ₂ , Γ₃ ,
    record
      { Γ₂′ = PresSynth.Γ₂′ ps
      ; ctx-step = PresSynth.ctx-step ps
      ; Γ = PresSynth.Γ ps
      ; Γ₁′ = PresSynth.Γ₁′ ps
      ; Γ₃′ = PresSynth.Γ₃′ ps
      ; split = PresSynth.split ps
      ; check = T-Check (PresSynth.synth ps) (<:ₜ-trans (PresSynth.subtype ps) U<:T)
      }


-- Item (1) of Theorem 4.1.

preserve⇒ :
  ∀ {n₁ n₂ n₃ m₂ pk m}
    {Γ₁ : Ctx [] n₁} {Γ₂ : Ctx [] n₂} {Γ₂′ : Ctx [] m₂} {Γ₃ : Ctx [] n₃}
    {e₁ : Expr [] ((n₁ + n₂) + n₃)} {e₂ : Expr [] ((n₁ + m₂) + n₃)}
    {T : NfTy [] (KV pk m)} {ℓ : Label ((n₁ + n₂) + n₃) ((n₁ + m₂) + n₃)}
  → e₁ —[ ℓ ]→ e₂
  → ((Γ₁ ++ Γ₂) ++ Γ₃) ⊢ e₁ ⇒ T ⊣ ((usedCtx (Γ₁ ++ Γ₂)) ++ Γ₃)
  → _—ctx[_]→_ {n₁} {n₂} {n₃} {m₂} Γ₂ ℓ Γ₂′
  → Σ (NfTy [] (KV pk m)) λ T′ →
      (((Γ₁ ++ Γ₂′) ++ Γ₃) ⊢ e₂ ⇒ T′ ⊣ ((usedCtx (Γ₁ ++ Γ₂′)) ++ Γ₃)) ×
      (normalTyOf T′ <:ₜ normalTyOf T)

preserve⇒ {T = T}
  Act-LetUnit
  (T-LetUnit (T-Check (T-Val (TV-Const CT-Unit)) _) synth₂)
  Ctx-β =
  T , synth₂ , <:ₜ-refl (normalTyOf T)

preserve⇒ {T = T}
  Act-PairV
  (T-Pair (T-Val synth₁) (T-Val synth₂))
  Ctx-β =
  T , T-Val (TV-Pair synth₁ synth₂) , <:ₜ-refl (normalTyOf T)

preserve⇒ {pk = KT} {m = Lin}
  (Act-Receive₁ {T = T})
  synth
  Ctx-β
  rewrite receive₁-rigid synth =
  normalizeTy (ReceiveTy1 T) ,
  T-Val TV-Receive₁ ,
  subst (λ X → normalTyOf (normalizeTy (ReceiveTy1 T)) <:ₜ normalTyOf X)
    (sym (receive₁-ty synth))
    (<:ₜ-refl (normalTyOf (normalizeTy (ReceiveTy1 T))))

preserve⇒ {pk = KT} {m = Lin}
  (Act-Receive₂ {T = T} {S = S})
  synth
  Ctx-β
  rewrite receive₂-rigid synth =
  normalizeTy (ReceiveTy T S) ,
  T-Val TV-Receive₂ ,
  subst (λ X → normalTyOf (normalizeTy (ReceiveTy T S)) <:ₜ normalTyOf X)
    (sym (receive₂-ty synth))
    (<:ₜ-refl (normalTyOf (normalizeTy (ReceiveTy T S))))

preserve⇒ {pk = KT} {m = Lin}
  (Act-Send₁ {T = T})
  synth
  Ctx-β
  rewrite send₁-rigid synth =
  normalizeTy (SendTy1 T) ,
  T-Val TV-Send₁ ,
  subst (λ X → normalTyOf (normalizeTy (SendTy1 T)) <:ₜ normalTyOf X)
    (sym (send₁-ty synth))
    (<:ₜ-refl (normalTyOf (normalizeTy (SendTy1 T))))

preserve⇒ {pk = KT} {m = Lin}
  (Act-Send₂ {T = T} {S = S})
  synth
  Ctx-β
  rewrite send₂-rigid synth =
  normalizeTy (SendTy T S) ,
  T-Val TV-Send₂ ,
  subst (λ X → normalTyOf (normalizeTy (SendTy T S)) <:ₜ normalTyOf X)
    (sym (send₂-ty synth))
    (<:ₜ-refl (normalTyOf (normalizeTy (SendTy T S))))

preserve⇒ {pk = KT} {m = Lin} {T = T}
  (Act-Send₃ {T = T₁} {S = S} {v = v})
  synth
  Ctx-β =
  T , T-Val (send₃-pres synth) , <:ₜ-refl (normalTyOf T)

preserve⇒ {pk = KT} {m = Lin} {T = T}
  Act-Select₁
  synth
  Ctx-β =
  T , T-Val (select₁-pres synth) , <:ₜ-refl (normalTyOf T)

preserve⇒ {pk = KT} {m = Lin} {T = T}
  Act-Select₂
  synth
  Ctx-β =
  T , T-Val (select₂-pres synth) , <:ₜ-refl (normalTyOf T)

preserve⇒ {n₁} {n₂} {n₃} {m₂} {pk} {m}
  {Γ₁} {Γ₂} {Γ₂′} {Γ₃} {e₁} {e₂} {T} {ℓ}
  step synth ctx-step =
  preserve⇒-hard {n₁} {n₂} {n₃} {m₂} {pk} {m}
    {Γ₁} {Γ₂} {Γ₂′} {Γ₃} {e₁} {e₂} {T} {ℓ}
    step synth ctx-step

-- Item (2) follows from item (1) by the checking rule and transitivity of
-- algorithmic subtyping.

preserve⇐ :
  ∀ {n₁ n₂ n₃ m₂ pk m}
    {Γ₁ : Ctx [] n₁} {Γ₂ : Ctx [] n₂} {Γ₂′ : Ctx [] m₂} {Γ₃ : Ctx [] n₃}
    {e₁ : Expr [] ((n₁ + n₂) + n₃)} {e₂ : Expr [] ((n₁ + m₂) + n₃)}
    {T : NfTy [] (KV pk m)} {ℓ : Label ((n₁ + n₂) + n₃) ((n₁ + m₂) + n₃)}
  → e₁ —[ ℓ ]→ e₂
  → ((Γ₁ ++ Γ₂) ++ Γ₃) ⊢ e₁ ⇐ T ⊣ ((usedCtx (Γ₁ ++ Γ₂)) ++ Γ₃)
  → _—ctx[_]→_ {n₁} {n₂} {n₃} {m₂} Γ₂ ℓ Γ₂′
  → ((Γ₁ ++ Γ₂′) ++ Γ₃) ⊢ e₂ ⇐ T ⊣ ((usedCtx (Γ₁ ++ Γ₂′)) ++ Γ₃)
preserve⇐ {n₁} {n₂} {n₃} {m₂} {pk} {m}
  {Γ₁} {Γ₂} {Γ₂′} {Γ₃} {e₁} {e₂} {T} {ℓ}
  step (T-Check synth U<:T) ctx-step =
  let pres = preserve⇒ {n₁} {n₂} {n₃} {m₂} {pk} {m}
               {Γ₁} {Γ₂} {Γ₂′} {Γ₃} {e₁} {e₂} {T = _} {ℓ}
               step synth ctx-step
  in T-Check (proj₁ (proj₂ pres)) (<:ₜ-trans (proj₂ (proj₂ pres)) U<:T)
