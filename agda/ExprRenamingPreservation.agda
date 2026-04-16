module ExprRenamingPreservation where

open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Subset as Subset
open import Data.List using (List; _∷_)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Kinds
open import Variance using (Variance)
open import Types using (Ty)
open import ExprSyntax using (Expr; Value; E-Val; E-App; E-TApp; E-LetUnit; E-Pair; E-LetPair; E-Match)
open import ExprSubstitution using (Ren; extRen; renameExpr; renameValue; wkValue)
open import ExprNormalTyping
open import ExprTypingProperties using (lift-∋ᵘ; lift-take)

infixr 1 _⊎₀_
data _⊎₀_ (A B : Set) : Set where
  inj₁₀ : A → A ⊎₀ B
  inj₂₀ : B → A ⊎₀ B

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

▻-injective :
  ∀ {Δ n} {b₁ b₂ : Binding Δ} {Γ₁ Γ₂ : Ctx Δ n}
  → b₁ ▻ Γ₁ ≡ b₂ ▻ Γ₂
  → (b₁ ≡ b₂) × (Γ₁ ≡ Γ₂)
▻-injective refl = refl , refl

insertAt-output-take :
  ∀ {Δ n pk}
    (k : ℕ)
    (b : Binding Δ)
    {Γ₁ : Ctx Δ (k + n)}
    {Γ₂ : Ctx Δ (k + suc n)}
    {x : Fin (k + n)}
    {T : NfTy Δ (KV pk Lin)}
  → insertAt k b Γ₁ ⊢ˡ liftRen k x ∶ T ⊣ Γ₂
  → Σ (Ctx Δ (k + n)) λ Γ₂′ → Γ₂ ≡ insertAt k b Γ₂′
insertAt-output-take zero b (take-thereˡ {Γ′ = Γ₂′} _) = Γ₂′ , refl
insertAt-output-take zero b (take-thereᵘ {Γ′ = Γ₂′} _) = Γ₂′ , refl
insertAt-output-take zero b (take-there✖ {Γ′ = Γ₂′} _) = Γ₂′ , refl
insertAt-output-take (suc k) b
  {Γ₁ = B-Lin U ▻ Γ₁} {x = zero}
  take-here =
  (B-Used U ▻ Γ₁) , refl
insertAt-output-take (suc k) b
  {Γ₁ = B-Lin U ▻ Γ₁} {x = suc x}
  (take-thereˡ take)
  with insertAt-output-take k b take
... | Γ₂′ , eq = (B-Lin U ▻ Γ₂′) , cong (B-Lin U ▻_) eq
insertAt-output-take (suc k) b
  {Γ₁ = B-Un U ▻ Γ₁} {x = suc x}
  (take-thereᵘ take)
  with insertAt-output-take k b take
... | Γ₂′ , eq = (B-Un U ▻ Γ₂′) , cong (B-Un U ▻_) eq
insertAt-output-take (suc k) b
  {Γ₁ = B-Used U ▻ Γ₁} {x = suc x}
  (take-there✖ take)
  with insertAt-output-take k b take
... | Γ₂′ , eq = (B-Used U ▻ Γ₂′) , cong (B-Used U ▻_) eq

insertAt-suc-tail :
  ∀ {Δ n}
    (k : ℕ)
    (b : Binding Δ)
    {h : Binding Δ}
    {Γ : Ctx Δ (suc k + n)}
    {Γtail : Ctx Δ (k + suc n)}
  → (h ▻ Γtail) ≡ insertAt (suc k) b Γ
  → Σ (Ctx Δ (k + n)) λ Γ′ → Γtail ≡ insertAt k b Γ′
insertAt-suc-tail k b {Γ = h′ ▻ Γ′} eq
  with ▻-injective eq
... | _ , tailEq = Γ′ , tailEq

wkCtx-insertAt-output :
  ∀ {Δ K n}
    (k : ℕ)
    (b : Binding Δ)
    {Γ : Ctx Δ (k + suc n)}
    {Γwk : Ctx (K ∷ Δ) (k + n)}
  → wkCtx Γ ≡ insertAt k (wkBinding {K = K} b) Γwk
  → Σ (Ctx Δ (k + n)) λ Γ′ → Γ ≡ insertAt k b Γ′
wkCtx-insertAt-output zero b {Γ = b₀ ▻ Γ} eq
  with ▻-injective eq
... | headEq , _
  with wkBinding-injective headEq
... | refl = Γ , refl
wkCtx-insertAt-output (suc k) b {Γ = b₀ ▻ Γ} {Γwk = bwk ▻ Γwk} eq
  with ▻-injective eq
... | _ , tailEq
  with wkCtx-insertAt-output k b tailEq
... | Γ′ , eq′ = (b₀ ▻ Γ′) , cong (b₀ ▻_) eq′

tv-const-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {c K}
    {T : NfTy Δ K}
  → Γ₁ ⊢ᵥ Value.V-Const c ⇒ T ⊣ Γ₂
  → ConstTy c T × (Γ₁ ≡ Γ₂)
tv-const-inversion (TV-Const cT) = cT , refl

tv-var-inversion :
  ∀ {Δ n pk m}
    {Γ₁ Γ₂ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk m)}
  → Γ₁ ⊢ᵥ Value.V-Var x ⇒ T ⊣ Γ₂
  → Σ (m ≡ Lin) (λ where
       refl → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂)
    ⊎₀ (Σ (m ≡ Un) (λ where
       refl → (Γ₁ ∋ᵘ x ∶ T) × (Γ₁ ≡ Γ₂)))
tv-var-inversion (TV-Var-Lin take) = inj₁₀ (refl , take)
tv-var-inversion (TV-Var-Un x∈) = inj₂₀ (refl , (x∈ , refl))

tv-abs-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {A : Ty Δ TLin}
    {e : Expr Δ (suc n)}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Abs A e ⇒ W ⊣ Γ₂
  → Σ (NfTy Δ TLin) λ U →
      (W ≡ linArrNf (normalizeTy A) U)
      × ((normalizeTy A ∷ˡ Γ₁) ⊢ e ⇒ U ⊣ used∷ {T = normalizeTy A} Γ₂)
tv-abs-inversion (TV-Abs d) = _ , refl , d

tv-rec-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {A B : Ty Δ TLin}
    {v : Value Δ (suc n)}
    {W : NfTy Δ (KV KT Un)}
  → Γ₁ ⊢ᵥ Value.V-Rec A B v ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂)
    × ((W ≡ unArrNf (normalizeTy A) (normalizeTy B))
      × ((unArrNf (normalizeTy A) (normalizeTy B) ∷ᵘ Γ₁)
          ⊢ E-Val v ⇐ unArrNf (normalizeTy A) (normalizeTy B)
          ⊣ (unArrNf (normalizeTy A) (normalizeTy B) ∷ᵘ Γ₁)))
tv-rec-inversion (TV-Rec d) = refl , refl , d

tv-tabs-inversion :
  ∀ {Δ n K m}
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Value (K ∷ Δ) n}
    {W : NfTy Δ (KV KT m)}
  → Γ₁ ⊢ᵥ Value.V-TAbs K v ⇒ W ⊣ Γ₂
  → Σ (NfTy (K ∷ Δ) (KV KT m)) λ T →
      (W ≡ polyNf T) × (wkCtx {K = K} Γ₁ ⊢ᵥ v ⇒ T ⊣ wkCtx Γ₂)
tv-tabs-inversion (TV-TAbs d) = _ , refl , d

tv-pair-inversion :
  ∀ {Δ n m}
    {Γ₁ Γ₃ : Ctx Δ n}
    {u v : Value Δ n}
    {W : NfTy Δ (KV KT m)}
  → Γ₁ ⊢ᵥ Value.V-Pair u v ⇒ W ⊣ Γ₃
  → Σ PreKind λ pk₁ →
      Σ PreKind λ pk₂ →
      Σ (NfTy Δ (KV pk₁ m)) λ T →
      Σ (NfTy Δ (KV pk₂ m)) λ U →
      Σ (Ctx Δ n) λ Γ₂ →
        (W ≡ pairNf T U) × ((Γ₁ ⊢ᵥ u ⇒ T ⊣ Γ₂) × (Γ₂ ⊢ᵥ v ⇒ U ⊣ Γ₃))
tv-pair-inversion (TV-Pair {pk₁ = pk₁} {pk₂ = pk₂} d₁ d₂) =
  pk₁ , pk₂ , _ , _ , _ , refl , (d₁ , d₂)

tv-receive₁-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {T : Ty Δ TLin}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Receive₁ T ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ receive1Nf (normalizeTy T))
tv-receive₁-inversion TV-Receive₁ = refl , refl

tv-receive₂-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {T : Ty Δ TLin}
    {S : Ty Δ SLin}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Receive₂ T S ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ receiveNf (normalizeTy T) (normalizeTy S))
tv-receive₂-inversion TV-Receive₂ = refl , refl

tv-send₁-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {T : Ty Δ TLin}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Send₁ T ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ send1Nf (normalizeTy T))
tv-send₁-inversion TV-Send₁ = refl , refl

tv-send₂-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {T : Ty Δ TLin}
    {S : Ty Δ SLin}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Send₂ T S ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ sendNf (normalizeTy T) (normalizeTy S))
tv-send₂-inversion TV-Send₂ = refl , refl

tv-select₁-inversion :
  ∀ {Δ n k}
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Variance}
    {i : Fin k}
    {P : Ty Δ KP}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Select₁ v i P ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ select1Nf v i (normalizeTy P))
tv-select₁-inversion TV-Select₁ = refl , refl

tv-select₂-inversion :
  ∀ {Δ n k}
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Variance}
    {i : Fin k}
    {P : Ty Δ KP}
    {S : Ty Δ SLin}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Select₂ v i P S ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ selectNf v i (normalizeTy P) (normalizeTy S))
tv-select₂-inversion TV-Select₂ = refl , refl

unlift-∋ᵘ-at :
  ∀ {Δ n pk}
    (k : ℕ)
    (b : Binding Δ)
    {Γ : Ctx Δ (k + n)}
    {x : Fin (k + n)}
    {T : NfTy Δ (KV pk Un)}
  → insertAt k b Γ ∋ᵘ liftRen k x ∶ T
  → Γ ∋ᵘ x ∶ T
unlift-∋ᵘ-at zero b (thereᵘˡ x∈) = x∈
unlift-∋ᵘ-at zero b (thereᵘᵘ x∈) = x∈
unlift-∋ᵘ-at zero b (thereᵘ✖ x∈) = x∈
unlift-∋ᵘ-at (suc k) b {Γ = B-Un U ▻ Γ} {x = zero} hereᵘ = hereᵘ
unlift-∋ᵘ-at (suc k) b {Γ = B-Lin U ▻ Γ} {x = suc x} (thereᵘˡ x∈) =
  thereᵘˡ (unlift-∋ᵘ-at k b x∈)
unlift-∋ᵘ-at (suc k) b {Γ = B-Un U ▻ Γ} {x = suc x} (thereᵘᵘ x∈) =
  thereᵘᵘ (unlift-∋ᵘ-at k b x∈)
unlift-∋ᵘ-at (suc k) b {Γ = B-Used U ▻ Γ} {x = suc x} (thereᵘ✖ x∈) =
  thereᵘ✖ (unlift-∋ᵘ-at k b x∈)

cast-take-ctx :
  ∀ {Δ n pk}
    {Γ₁ Γ₂ Γ₁′ Γ₂′ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
  → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂
  → Γ₁ ≡ Γ₁′
  → Γ₂ ≡ Γ₂′
  → Γ₁′ ⊢ˡ x ∶ T ⊣ Γ₂′
cast-take-ctx d refl refl = d

insertAt-injective :
  ∀ {Δ n}
    (k : ℕ)
    (b : Binding Δ)
    {Γ₁ Γ₂ : Ctx Δ (k + n)}
  → insertAt k b Γ₁ ≡ insertAt k b Γ₂
  → Γ₁ ≡ Γ₂
insertAt-injective zero b eq
  with ▻-injective eq
... | _ , tailEq = tailEq
insertAt-injective (suc k) b {Γ₁ = b₁ ▻ Γ₁} {Γ₂ = b₂ ▻ Γ₂} eq
  with ▻-injective eq
... | headEq , tailEq
  = trans
      (cong (λ z → z ▻ Γ₁) headEq)
      (cong (b₂ ▻_) (insertAt-injective k b tailEq))

unlift-take-at′ :
  ∀ {Δ n pk}
    (k : ℕ)
    (b : Binding Δ)
    {Γ : Ctx Δ (k + n)}
    {Γout : Ctx Δ (k + suc n)}
    {x : Fin (k + n)}
    {T : NfTy Δ (KV pk Lin)}
  → insertAt k b Γ ⊢ˡ liftRen k x ∶ T ⊣ Γout
  → Σ (Ctx Δ (k + n)) λ Γ′ →
      (Γout ≡ insertAt k b Γ′) × (Γ ⊢ˡ x ∶ T ⊣ Γ′)
unlift-take-at′ zero b (take-thereˡ take) = _ , refl , take
unlift-take-at′ zero b (take-thereᵘ take) = _ , refl , take
unlift-take-at′ zero b (take-there✖ take) = _ , refl , take
unlift-take-at′
  (suc k) b
  {Γ = B-Lin U ▻ Γ}
  {Γout = B-Used U ▻ Γout}
  {x = zero}
  take-here =
  _ , refl , take-here
unlift-take-at′
  (suc k) b
  {Γ = B-Lin U ▻ Γ}
  {Γout = B-Lin U ▻ Γout}
  {x = suc x}
  (take-thereˡ take)
  with unlift-take-at′ k b {Γ = Γ} {Γout = Γout} {x = x} take
... | Γ′ , eq , take′ = (B-Lin U ▻ Γ′) , cong (B-Lin U ▻_) eq , take-thereˡ take′
unlift-take-at′
  (suc k) b
  {Γ = B-Un U ▻ Γ}
  {Γout = B-Un U ▻ Γout}
  {x = suc x}
  (take-thereᵘ take)
  with unlift-take-at′ k b {Γ = Γ} {Γout = Γout} {x = x} take
... | Γ′ , eq , take′ = (B-Un U ▻ Γ′) , cong (B-Un U ▻_) eq , take-thereᵘ take′
unlift-take-at′
  (suc k) b
  {Γ = B-Used U ▻ Γ}
  {Γout = B-Used U ▻ Γout}
  {x = suc x}
  (take-there✖ take)
  with unlift-take-at′ k b {Γ = Γ} {Γout = Γout} {x = x} take
... | Γ′ , eq , take′ = (B-Used U ▻ Γ′) , cong (B-Used U ▻_) eq , take-there✖ take′

unlift-take-at :
  ∀ {Δ n pk}
    (k : ℕ)
    (b : Binding Δ)
    {Γ Γ′ : Ctx Δ (k + n)}
    {x : Fin (k + n)}
    {T : NfTy Δ (KV pk Lin)}
  → insertAt k b Γ ⊢ˡ liftRen k x ∶ T ⊣ insertAt k b Γ′
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
unlift-take-at k b {Γ′ = Γ′} take
  with unlift-take-at′ k b take
... | Γ″ , eqout , take′
  with insertAt-injective k b eqout
... | eqΓ = cast-take-ctx take′ refl (sym eqΓ)

mutual
  insertAt-output-value :
    ∀ {Δ n pk m}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ : Ctx Δ (k + n)}
      {Γ₂ : Ctx Δ (k + suc n)}
      {v : Value Δ (k + n)}
      {T : NfTy Δ (KV pk m)}
    → insertAt k b Γ₁ ⊢ᵥ renameValue (liftRen k) v ⇒ T ⊣ Γ₂
    → Σ (Ctx Δ (k + n)) λ Γ₂′ → Γ₂ ≡ insertAt k b Γ₂′

  insertAt-output-synth :
    ∀ {Δ n pk m}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ : Ctx Δ (k + n)}
      {Γ₂ : Ctx Δ (k + suc n)}
      {e : Expr Δ (k + n)}
      {T : NfTy Δ (KV pk m)}
    → insertAt k b Γ₁ ⊢ renameExpr (liftRen k) e ⇒ T ⊣ Γ₂
    → Σ (Ctx Δ (k + n)) λ Γ₂′ → Γ₂ ≡ insertAt k b Γ₂′

  insertAt-output-check :
    ∀ {Δ n pk m}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ : Ctx Δ (k + n)}
      {Γ₂ : Ctx Δ (k + suc n)}
      {e : Expr Δ (k + n)}
      {T : NfTy Δ (KV pk m)}
    → insertAt k b Γ₁ ⊢ renameExpr (liftRen k) e ⇐ T ⊣ Γ₂
    → Σ (Ctx Δ (k + n)) λ Γ₂′ → Γ₂ ≡ insertAt k b Γ₂′

  insertAt-output-synth′ :
    ∀ {Δ n pk m}
      (k : ℕ)
      (b : Binding Δ)
      (e : Expr Δ (k + n))
      {Γ₁ : Ctx Δ (k + n)}
      {Γ₂ : Ctx Δ (k + suc n)}
      {T : NfTy Δ (KV pk m)}
    → insertAt k b Γ₁ ⊢ renameExpr (liftRen k) e ⇒ T ⊣ Γ₂
    → Σ (Ctx Δ (k + n)) λ Γ₂′ → Γ₂ ≡ insertAt k b Γ₂′

  insertAt-output-value k b {Γ₁} {v = Value.V-Const c} d with tv-const-inversion d
  ... | _ , eq = Γ₁ , sym eq
  insertAt-output-value k b {Γ₁} {v = Value.V-Var x} d with tv-var-inversion d
  ... | inj₁₀ (refl , take) = insertAt-output-take k b take
  ... | inj₂₀ (refl , (_ , eq)) = Γ₁ , sym eq
  insertAt-output-value {pk = KT} {m = Lin} k b {Γ₁} {v = Value.V-Abs A e} d with tv-abs-inversion d
  ... | _ , _ , dabs
    with insertAt-output-synth (suc k) b {Γ₁ = B-Lin (normalizeTy A) ▻ Γ₁} dabs
  ... | Γ₂′ , eq
    with insertAt-suc-tail k b {h = B-Used (normalizeTy A)} eq
  ... | Γ₂″ , tailEq = Γ₂″ , tailEq
  insertAt-output-value {pk = KT} {m = Un} k b {Γ₁} {v = Value.V-Rec A B v} d with tv-rec-inversion d
  ... | eq , _ , _ = Γ₁ , sym eq
  insertAt-output-value {pk = KT} {m = m} k b {Γ₁} {v = Value.V-TAbs K v} d with tv-tabs-inversion d
  ... | _ , _ , dtabs
    with insertAt-output-value
           k
           (wkBinding {K = K} b)
           (cast-value-ctx
             dtabs
             (wkCtx-insertAt {K = K} k b Γ₁)
             refl)
  ... | Γ₂wk , eqwk
    with wkCtx-insertAt-output k b eqwk
  ... | Γ₂′ , eq = Γ₂′ , eq
  insertAt-output-value {pk = KT} {m = m} k b {v = Value.V-Pair u v} d with tv-pair-inversion d
  ... | _ , _ , _ , _ , Γm , _ , (d₁ , d₂)
    with insertAt-output-value k b d₁
  ... | Γm′ , eqm
    with insertAt-output-value k b (cast-value-ctx d₂ eqm refl)
  ... | Γ₂′ , eq₂ = Γ₂′ , eq₂
  insertAt-output-value {pk = KT} {m = Lin} k b {Γ₁} {v = Value.V-Receive₁ T} d with tv-receive₁-inversion d
  ... | eq , _ = Γ₁ , sym eq
  insertAt-output-value {pk = KT} {m = Lin} k b {Γ₁} {v = Value.V-Receive₂ T S} d with tv-receive₂-inversion d
  ... | eq , _ = Γ₁ , sym eq
  insertAt-output-value {pk = KT} {m = Lin} k b {Γ₁} {v = Value.V-Send₁ T} d with tv-send₁-inversion d
  ... | eq , _ = Γ₁ , sym eq
  insertAt-output-value {pk = KT} {m = Lin} k b {Γ₁} {v = Value.V-Send₂ T S} d with tv-send₂-inversion d
  ... | eq , _ = Γ₁ , sym eq
  insertAt-output-value {pk = KT} {m = Lin} k b {Γ₁} {v = Value.V-Select₁ v i P} d with tv-select₁-inversion d
  ... | eq , _ = Γ₁ , sym eq
  insertAt-output-value {pk = KT} {m = Lin} k b {Γ₁} {v = Value.V-Select₂ v i P S} d with tv-select₂-inversion d
  ... | eq , _ = Γ₁ , sym eq

  insertAt-output-synth k b {e = e} d = insertAt-output-synth′ k b e d

  insertAt-output-synth′ k b (E-Val v) (T-Val d) =
    insertAt-output-value k b d
  insertAt-output-synth′ k b (E-Pair e₁ e₂) (T-Pair d₁ d₂)
    with insertAt-output-synth′ k b e₁ d₁
  ... | Γm , eq rewrite eq = insertAt-output-synth′ k b e₂ d₂
  insertAt-output-synth′ k b (E-App e₁ e₂) (T-App d₁ d₂)
    with insertAt-output-synth′ k b e₁ d₁
  ... | Γm , eq rewrite eq = insertAt-output-check k b d₂
  insertAt-output-synth′ k b (E-LetUnit e₁ e₂) (T-LetUnit d₁ d₂)
    with insertAt-output-check k b d₁
  ... | Γm , eq rewrite eq = insertAt-output-synth′ k b e₂ d₂
  insertAt-output-synth′ k b (E-LetPair e₁ e₂) (T-LetPair {T = T} {U = U} d₁ d₂)
    with insertAt-output-synth′ k b e₁ d₁
  ... | Γm , eq rewrite eq
    with insertAt-output-synth′
           (suc (suc k))
           b
           e₂
           {Γ₁ = B-Lin T ▻ B-Lin U ▻ Γm}
           d₂
  ...   | Γpair , eqpair
    with insertAt-suc-tail (suc k) b {h = B-Used T} eqpair
  ...   | Γtail , eqtail
    with insertAt-suc-tail k b {h = B-Used U} eqtail
  ...   | Γ₂′ , eq₂ = Γ₂′ , eq₂
  insertAt-output-synth′ k b (E-Match e ne branches)
    (T-Match
      {ss = ss}
      {v = v}
      {ssbranches = ssbranches}
      {incl = incl}
      {ne = ne}
      {P = P}
      {S = S}
      d bs j)
    with insertAt-output-synth′ k b e d
  ... | Γm , eq rewrite eq
    with insertAt-output-synth′
           (suc k)
           b
           (branches (proj₁ ne) (proj₂ ne))
           {Γ₁ = B-Lin (MatchBranchOutput ssbranches v P S (proj₁ ne) (proj₂ ne)) ▻ Γm}
           (bs (proj₁ ne) (proj₂ ne))
  ... | Γbranch , eqbranch
    with insertAt-suc-tail k b {h = B-Used (MatchBranchOutput ssbranches v P S (proj₁ ne) (proj₂ ne))} eqbranch
  ... | Γ₂′ , eq₂ = Γ₂′ , eq₂
  insertAt-output-synth′ k b (E-TApp e U) (T-TApp d)
    with insertAt-output-synth′ k b e d
  ... | Γ₂′ , eq₂ = Γ₂′ , eq₂

  insertAt-output-check k b (T-Check d sub) =
    insertAt-output-synth k b d

mutual
  {-# TERMINATING #-}
  unren-preserves-value :
    ∀ {Δ n pk m}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ Γ₂ : Ctx Δ (k + n)}
      {v : Value Δ (k + n)}
      {T : NfTy Δ (KV pk m)}
    → insertAt k b Γ₁ ⊢ᵥ renameValue (liftRen k) v ⇒ T ⊣ insertAt k b Γ₂
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  unren-preserves-value k b {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = Value.V-Const c} d
    with tv-const-inversion d
  ... | cT , eq
    with insertAt-injective k b eq
  ... | eqΓ =
      cast-value-ctx (TV-Const cT) refl eqΓ
  unren-preserves-value k b {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = Value.V-Var x} d
    with tv-var-inversion d
  ... | inj₁₀ (refl , take) =
      TV-Var-Lin (unlift-take-at k b take)
  ... | inj₂₀ (refl , (x∈ , eq))
    with insertAt-injective k b eq
  ... | eqΓ =
      cast-value-ctx (TV-Var-Un (unlift-∋ᵘ-at k b x∈)) refl eqΓ
  unren-preserves-value {pk = KT} {m = Lin} k b {v = Value.V-Abs A e} (TV-Abs d) =
    TV-Abs (unren-preserves-synth (suc k) b d)
  unren-preserves-value {pk = KT} {m = Un} k b {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = Value.V-Rec A B v} d
    with tv-rec-inversion d
  ... | eqCtx , eqT , drec
    with insertAt-injective k b eqCtx
  ... | eqΓ
    rewrite eqT =
      cast-value-ctx
        (TV-Rec (unren-preserves-check (suc k) b drec))
        refl
        eqΓ
  unren-preserves-value k b {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = Value.V-TAbs K v} (TV-TAbs {K = K} d)
    rewrite wkCtx-insertAt {K = K} k b Γ₁
          | wkCtx-insertAt {K = K} k b Γ₂ =
      TV-TAbs
        (unren-preserves-value
           k
           (wkBinding {K = K} b)
           d)
  unren-preserves-value k b {v = Value.V-Pair u v} (TV-Pair d₁ d₂)
    with insertAt-output-value k b d₁
  ... | Γm , eq
    rewrite eq =
      TV-Pair
        (unren-preserves-value k b d₁)
        (unren-preserves-value k b d₂)
  unren-preserves-value {pk = KT} {m = Lin} k b {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = Value.V-Receive₁ T} d
    with tv-receive₁-inversion d
  ... | eqCtx , eqT
    with insertAt-injective k b eqCtx
  ... | eqΓ
    rewrite eqT =
      cast-value-ctx TV-Receive₁ refl eqΓ
  unren-preserves-value {pk = KT} {m = Lin} k b {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = Value.V-Receive₂ T S} d
    with tv-receive₂-inversion d
  ... | eqCtx , eqT
    with insertAt-injective k b eqCtx
  ... | eqΓ
    rewrite eqT =
      cast-value-ctx TV-Receive₂ refl eqΓ
  unren-preserves-value {pk = KT} {m = Lin} k b {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = Value.V-Send₁ T} d
    with tv-send₁-inversion d
  ... | eqCtx , eqT
    with insertAt-injective k b eqCtx
  ... | eqΓ
    rewrite eqT =
      cast-value-ctx TV-Send₁ refl eqΓ
  unren-preserves-value {pk = KT} {m = Lin} k b {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = Value.V-Send₂ T S} d
    with tv-send₂-inversion d
  ... | eqCtx , eqT
    with insertAt-injective k b eqCtx
  ... | eqΓ
    rewrite eqT =
      cast-value-ctx TV-Send₂ refl eqΓ
  unren-preserves-value {pk = KT} {m = Lin} k b {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = Value.V-Select₁ v i P} d
    with tv-select₁-inversion d
  ... | eqCtx , eqT
    with insertAt-injective k b eqCtx
  ... | eqΓ
    rewrite eqT =
      cast-value-ctx TV-Select₁ refl eqΓ
  unren-preserves-value {pk = KT} {m = Lin} k b {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = Value.V-Select₂ v i P S} d
    with tv-select₂-inversion d
  ... | eqCtx , eqT
    with insertAt-injective k b eqCtx
  ... | eqΓ
    rewrite eqT =
      cast-value-ctx TV-Select₂ refl eqΓ

  {-# TERMINATING #-}
  unren-preserves-synth :
    ∀ {Δ n pk m}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ Γ₂ : Ctx Δ (k + n)}
      {e : Expr Δ (k + n)}
      {T : NfTy Δ (KV pk m)}
    → insertAt k b Γ₁ ⊢ renameExpr (liftRen k) e ⇒ T ⊣ insertAt k b Γ₂
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
  unren-preserves-synth k b {e = E-Val v} (T-Val d) =
    T-Val (unren-preserves-value k b d)
  unren-preserves-synth k b {e = E-Pair e₁ e₂} (T-Pair d₁ d₂)
    with insertAt-output-synth k b d₁
  ... | Γm , eq
    rewrite eq =
      T-Pair
        (unren-preserves-synth k b d₁)
        (unren-preserves-synth k b d₂)
  unren-preserves-synth k b {e = E-App e₁ e₂} (T-App d₁ d₂)
    with insertAt-output-synth k b d₁
  ... | Γm , eq
    rewrite eq =
      T-App
        (unren-preserves-synth k b d₁)
        (unren-preserves-check k b d₂)
  unren-preserves-synth k b {e = E-LetUnit e₁ e₂} (T-LetUnit d₁ d₂)
    with insertAt-output-check k b d₁
  ... | Γm , eq
    rewrite eq =
      T-LetUnit
        (unren-preserves-check k b d₁)
        (unren-preserves-synth k b d₂)
  unren-preserves-synth k b {e = E-LetPair e₁ e₂} (T-LetPair d₁ d₂)
    with insertAt-output-synth k b d₁
  ... | Γm , eq
    rewrite eq =
      T-LetPair
        (unren-preserves-synth k b d₁)
        (unren-preserves-synth (suc (suc k)) b d₂)
  unren-preserves-synth k b {e = E-Match e ne branches}
    (T-Match
      {ss = ss}
      {v = v}
      {ssbranches = ssbranches}
      {incl = incl}
      {ne = ne}
      {P = P}
      {S = S}
      {branches = branchesr}
      {V = V}
      {sub = sub}
      d bs j)
    with insertAt-output-synth k b d
  ... | Γm , eq
    rewrite eq =
      T-Match
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
        (unren-preserves-synth k b d)
        bs′
        j
    where
      bs′ :
        (i : Fin _)
        → (i∈ : i Subset.∈ ssbranches)
        → (MatchBranchOutput ssbranches v P S i i∈ ∷ˡ _)
            ⊢ branches i i∈
              ⇒ V i i∈
              ⊣ (B-Used (MatchBranchOutput ssbranches v P S i i∈) ▻ _)
      bs′ i i∈ = unren-preserves-synth (suc k) b (bs i i∈)
  unren-preserves-synth k b {e = E-TApp e U} (T-TApp d) =
    T-TApp (unren-preserves-synth k b d)

  {-# TERMINATING #-}
  unren-preserves-check :
    ∀ {Δ n pk m}
      (k : ℕ)
      (b : Binding Δ)
      {Γ₁ Γ₂ : Ctx Δ (k + n)}
      {e : Expr Δ (k + n)}
      {T : NfTy Δ (KV pk m)}
    → insertAt k b Γ₁ ⊢ renameExpr (liftRen k) e ⇐ T ⊣ insertAt k b Γ₂
    → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
  unren-preserves-check k b (T-Check d sub) =
    T-Check (unren-preserves-synth k b d) sub

unwk-preserves-value :
  ∀ {Δ n pk m}
    (b : Binding Δ)
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
  → (b ▻ Γ₁) ⊢ᵥ wkValue v ⇒ T ⊣ (b ▻ Γ₂)
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
unwk-preserves-value b d = unren-preserves-value 0 b d

unwk-preserves-synth :
  ∀ {Δ n pk m}
    (b : Binding Δ)
    {Γ₁ Γ₂ : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk m)}
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
