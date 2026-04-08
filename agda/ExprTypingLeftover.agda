module ExprTypingLeftover where

open import Data.Fin using (Fin; zero)
open import Data.List using (List; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Kinds
open import Duality
open import Types
open import ExprSyntax using (Expr; Value; Const; E-Val; V-Pair)
open import ExprNormalTyping
open import ExprContextReduction using (RemoveCtx; RM-∅; RM-drop; RM-allused; RM-lin; RM-un; AllUsed; AU-∅; AU-used; AU-un)
open import ExprTypingProperties using (FrameCtx; FC-∅; FC-frame; FC-allused; FC-live; FC-un; replay-value-allUsed)

usedCtx : ∀ {Δ n} → Ctx Δ n → Ctx Δ n
usedCtx ∅ = ∅
usedCtx (_ ▻ Γ) = B-Used ▻ usedCtx Γ

allUsedCtx : ∀ {Δ n} → Ctx Δ n → Ctx Δ n
allUsedCtx ∅ = ∅
allUsedCtx (B-Lin _ ▻ Γ) = B-Used ▻ allUsedCtx Γ
allUsedCtx (B-Un T ▻ Γ) = B-Un T ▻ allUsedCtx Γ
allUsedCtx (B-Used ▻ Γ) = B-Used ▻ allUsedCtx Γ

allUsedCtx-AllUsed : ∀ {Δ n} (Γ : Ctx Δ n) → AllUsed (allUsedCtx Γ)
allUsedCtx-AllUsed ∅ = AU-∅
allUsedCtx-AllUsed (B-Lin _ ▻ Γ) = AU-used (allUsedCtx-AllUsed Γ)
allUsedCtx-AllUsed (B-Un _ ▻ Γ) = AU-un (allUsedCtx-AllUsed Γ)
allUsedCtx-AllUsed (B-Used ▻ Γ) = AU-used (allUsedCtx-AllUsed Γ)

remove-allUsedCtx : ∀ {Δ n} (Γ : Ctx Δ n) → RemoveCtx Γ (allUsedCtx Γ) Γ
remove-allUsedCtx ∅ = RM-∅
remove-allUsedCtx (B-Lin _ ▻ Γ) = RM-drop (remove-allUsedCtx Γ)
remove-allUsedCtx (B-Un _ ▻ Γ) = RM-un (remove-allUsedCtx Γ)
remove-allUsedCtx (B-Used ▻ Γ) = RM-allused (remove-allUsedCtx Γ)

allUsedCtx-∋ᵘ :
  ∀ {Δ n K} {Γ : Ctx Δ n} {x : Fin n} {T : NfTy Δ K}
  → Γ ∋ᵘ x ∶ T
  → allUsedCtx Γ ∋ᵘ x ∶ T
allUsedCtx-∋ᵘ hereᵘ = hereᵘ
allUsedCtx-∋ᵘ (thereᵘˡ x∈) = thereᵘ✖ (allUsedCtx-∋ᵘ x∈)
allUsedCtx-∋ᵘ (thereᵘᵘ x∈) = thereᵘᵘ (allUsedCtx-∋ᵘ x∈)
allUsedCtx-∋ᵘ (thereᵘ✖ x∈) = thereᵘ✖ (allUsedCtx-∋ᵘ x∈)

remove-refl : ∀ {Δ n} (Γ : Ctx Δ n) → RemoveCtx Γ (allUsedCtx Γ) Γ
remove-refl = remove-allUsedCtx

remove-compose :
  ∀ {Δ n} {Γ₀ Γ₁ Γ₂ G₁ G₂ : Ctx Δ n}
  → RemoveCtx Γ₀ G₁ Γ₁
  → RemoveCtx Γ₁ G₂ Γ₂
  → Σ (Ctx Δ n) λ G → RemoveCtx Γ₀ G Γ₂
remove-compose RM-∅ RM-∅ = ∅ , RM-∅
remove-compose (RM-drop r₁) (RM-drop r₂)
  with remove-compose r₁ r₂
... | G , r = (B-Used ▻ G) , RM-drop r
remove-compose (RM-drop r₁) (RM-lin r₂)
  with remove-compose r₁ r₂
... | G , r = (B-Lin _ ▻ G) , RM-lin r
remove-compose (RM-allused r₁) (RM-allused r₂)
  with remove-compose r₁ r₂
... | G , r = (B-Used ▻ G) , RM-allused r
remove-compose (RM-lin r₁) (RM-allused r₂)
  with remove-compose r₁ r₂
... | G , r = (B-Lin _ ▻ G) , RM-lin r
remove-compose (RM-un r₁) (RM-un r₂)
  with remove-compose r₁ r₂
... | G , r = (B-Un _ ▻ G) , RM-un r

remove-compose-frame :
  ∀ {Δ n} {Γ₀ Γ₁ Γ₂ G₁ G₂ : Ctx Δ n}
  → (r₁ : RemoveCtx Γ₀ G₁ Γ₁)
  → (r₂ : RemoveCtx Γ₁ G₂ Γ₂)
  → Σ (Ctx Δ n) λ G →
      RemoveCtx Γ₀ G Γ₂ × FrameCtx G₂ G₁ G
remove-compose-frame RM-∅ RM-∅ = ∅ , RM-∅ , FC-∅
remove-compose-frame (RM-drop r₁) (RM-drop r₂)
  with remove-compose-frame r₁ r₂
... | G , r , f = (B-Used ▻ G) , RM-drop r , FC-allused f
remove-compose-frame (RM-drop r₁) (RM-lin r₂)
  with remove-compose-frame r₁ r₂
... | G , r , f = (B-Lin _ ▻ G) , RM-lin r , FC-frame f
remove-compose-frame (RM-allused r₁) (RM-allused r₂)
  with remove-compose-frame r₁ r₂
... | G , r , f = (B-Used ▻ G) , RM-allused r , FC-allused f
remove-compose-frame (RM-lin r₁) (RM-allused r₂)
  with remove-compose-frame r₁ r₂
... | G , r , f = (B-Lin _ ▻ G) , RM-lin r , FC-live f
remove-compose-frame (RM-un r₁) (RM-un r₂)
  with remove-compose-frame r₁ r₂
... | G , r , f = (B-Un _ ▻ G) , RM-un r , FC-un f

strip-lin-used :
  ∀ {Δ n K} {T : NfTy Δ K} {Γ₀ Γ₁ : Ctx Δ n} {G : Ctx Δ (suc n)}
  → RemoveCtx (B-Lin T ▻ Γ₀) G (B-Used ▻ Γ₁)
  → Σ (Ctx Δ n) λ G′ → RemoveCtx Γ₀ G′ Γ₁
strip-lin-used (RM-lin r) = _ , r

strip-lin-used₂ :
  ∀ {Δ n K K′} {T : NfTy Δ K} {U : NfTy Δ K′} {Γ₀ Γ₁ : Ctx Δ n} {G : Ctx Δ (suc (suc n))}
  → RemoveCtx (B-Lin T ▻ (B-Lin U ▻ Γ₀)) G (B-Used ▻ (B-Used ▻ Γ₁))
  → Σ (Ctx Δ n) λ G′ → RemoveCtx Γ₀ G′ Γ₁
strip-lin-used₂ r with strip-lin-used r
... | G′ , r′ with strip-lin-used r′
... | G″ , r″ = G″ , r″

strip-un-same :
  ∀ {Δ n K} {T : NfTy Δ K} {Γ₀ Γ₁ : Ctx Δ n} {G : Ctx Δ (suc n)}
  → RemoveCtx (B-Un T ▻ Γ₀) G (B-Un T ▻ Γ₁)
  → Σ (Ctx Δ n) λ G′ → RemoveCtx Γ₀ G′ Γ₁
strip-un-same (RM-un r) = _ , r

used-head :
  ∀ {Δ n} {Γ₀ Γv Γx : Ctx Δ n} {b₀ b₁ : Binding Δ}
  → RemoveCtx (b₀ ▻ Γ₀) (B-Used ▻ Γv) (b₁ ▻ Γx)
  → b₀ ≡ b₁
used-head (RM-drop _) = refl
used-head (RM-allused _) = refl

used-tail :
  ∀ {Δ n} {Γ₀ Γv Γx : Ctx Δ n} {b₀ b₁ : Binding Δ}
  → (r : RemoveCtx (b₀ ▻ Γ₀) (B-Used ▻ Γv) (b₁ ▻ Γx))
  → RemoveCtx Γ₀ Γv Γx
used-tail (RM-drop r) = r
used-tail (RM-allused r) = r

lin-tail :
  ∀ {Δ n K K′} {Γ₀ Γv Γx : Ctx Δ n} {T : NfTy Δ K} {U : NfTy Δ K′}
  → RemoveCtx (B-Lin T ▻ Γ₀) (B-Lin U ▻ Γv) (B-Used ▻ Γx)
  → Σ (K ≡ K′) λ where
      refl → (T ≡ U) × RemoveCtx Γ₀ Γv Γx
lin-tail (RM-lin r) = refl , refl , r

un-tail :
  ∀ {Δ n K K′ K″} {Γ₀ Γv Γx : Ctx Δ n}
    {T : NfTy Δ K} {U : NfTy Δ K′} {V : NfTy Δ K″}
  → RemoveCtx (B-Un T ▻ Γ₀) (B-Un U ▻ Γv) (B-Un V ▻ Γx)
  → Σ (K ≡ K′) λ where
      refl → Σ (K′ ≡ K″) λ where
        refl → (T ≡ U) × (U ≡ V) × RemoveCtx Γ₀ Γv Γx
un-tail (RM-un r) = refl , refl , refl , refl , r

un-result :
  ∀ {Δ n K} {Γ₀ Γ₁ G : Ctx Δ n} {T U : NfTy Δ K}
  → T ≡ U
  → RemoveCtx Γ₀ G Γ₁
  → RemoveCtx (B-Un T ▻ Γ₀) (B-Un T ▻ G) (B-Un U ▻ Γ₁)
un-result refl r = RM-un r

strip-wk :
  ∀ {Δ K n} {Γ₀ Γ₁ : Ctx Δ n} {G : Ctx (K ∷ Δ) n}
  → RemoveCtx (wkCtx {K = K} Γ₀) G (wkCtx Γ₁)
  → Σ (Ctx Δ n) λ G′ → RemoveCtx Γ₀ G′ Γ₁
strip-wk {Γ₀ = ∅} {Γ₁ = ∅} RM-∅ = ∅ , RM-∅
strip-wk {K = K} {Γ₀ = B-Used ▻ Γ₀} {Γ₁ = B-Used ▻ Γ₁} {G = B-Used ▻ G} (RM-allused r)
  with strip-wk {K = K} r
... | G′ , r′ = B-Used ▻ G′ , RM-allused r′
strip-wk {K = K} {Γ₀ = B-Lin T ▻ Γ₀} {Γ₁ = B-Used ▻ Γ₁} {G = B-Lin U ▻ G} r
  with lin-tail r
... | refl , refl , r₀
  with strip-wk {K = K} r₀
... | G′ , r′ = B-Lin T ▻ G′ , RM-lin r′
strip-wk {K = K} {Γ₀ = B-Lin T ▻ Γ₀} {Γ₁ = B-Lin U ▻ Γ₁} {G = B-Used ▻ G} r
  rewrite wkBinding-injective {L = K} {b₁ = B-Lin T} {b₂ = B-Lin U} (used-head r)
  with strip-wk {K = K} (used-tail r)
... | G′ , r′ = B-Used ▻ G′ , RM-drop r′
strip-wk {K = K} {Γ₀ = B-Un T ▻ Γ₀} {Γ₁ = B-Un U ▻ Γ₁} {G = B-Un V ▻ G} r
  with un-tail r
... | refl , refl , eq₁ , eq₂ , r₀
  with strip-wk {K = K} r₀
... | G′ , r′ =
  B-Un T ▻ G′ ,
  un-result (wkNfTy-injective {K′ = K} (trans eq₁ eq₂)) r′

leftover-take :
  ∀ {Δ n K} {Γ₀ Γ₁ : Ctx Δ n} {x : Fin n} {T : NfTy Δ K}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₁
  → Σ (Ctx Δ n) λ G → RemoveCtx Γ₀ G Γ₁
leftover-take take-here = _ , RM-lin (remove-refl _)
leftover-take (take-thereˡ p)
  with leftover-take p
... | G , r = _ , RM-drop r
leftover-take (take-thereᵘ p)
  with leftover-take p
... | G , r = _ , RM-un r
leftover-take (take-there✖ p)
  with leftover-take p
... | G , r = _ , RM-allused r

strip-take :
  ∀ {Δ n K} {Γ₀ Γ₁ : Ctx Δ n} {x : Fin n} {T : NfTy Δ K}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₁
  → Σ (Ctx Δ n) λ G →
      Σ (Ctx Δ n) λ G′ →
        RemoveCtx Γ₀ G Γ₁ × (G ⊢ˡ x ∶ T ⊣ G′) × AllUsed G′
strip-take {Γ₀ = _ ▻ Γ} (take-here {T = T}) =
  (T ∷ˡ (allUsedCtx Γ)) , (used∷ (allUsedCtx Γ)) ,
  (RM-lin (remove-allUsedCtx Γ)) , take-here , AU-used (allUsedCtx-AllUsed Γ)
strip-take (take-thereˡ {U = U} p)
  with strip-take p
... | G , G′ , r , p′ , au =
  (B-Used ▻ G) , (B-Used ▻ G′) ,
  RM-drop r , take-there✖ p′ , AU-used au
strip-take (take-thereᵘ {U = U} p)
  with strip-take p
... | G , G′ , r , p′ , au =
  (U ∷ᵘ G) , (U ∷ᵘ G′) ,
  RM-un r , take-thereᵘ p′ , AU-un au
strip-take (take-there✖ p)
  with strip-take p
... | G , G′ , r , p′ , au =
  (B-Used ▻ G) , (B-Used ▻ G′) ,
  RM-allused r , take-there✖ p′ , AU-used au

postulate
  strip-value-abs :
    ∀ {Δ n} {Γ₀ Γ₁ : Ctx Δ n} {T : Ty Δ TLin} {U : NfTy Δ TLin} {e : Expr Δ (suc n)}
    → (T ∷ⁿˡ Γ₀) ⊢ e ⇒ U ⊣ used∷ Γ₁
    → Σ (Ctx Δ n) λ G →
        Σ (Ctx Δ n) λ G′ →
          RemoveCtx Γ₀ G Γ₁ × ((T ∷ⁿˡ G) ⊢ e ⇒ U ⊣ used∷ G′) × AllUsed G′

  strip-value-rec :
    ∀ {Δ n} {Γ₀ : Ctx Δ n} {T U : Ty Δ TLin} {v : Value Δ (suc n)}
    → (linArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₀)
        ⊢ E-Val v ⇐ linArrNf (normalizeTy T) (normalizeTy U)
        ⊣ (linArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₀)
    → Σ (Ctx Δ n) λ G →
          RemoveCtx Γ₀ G Γ₀ × ((linArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ G)
            ⊢ E-Val v ⇐ linArrNf (normalizeTy T) (normalizeTy U)
            ⊣ (linArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ G)) × AllUsed G

  strip-value-tabs :
    ∀ {Δ n K m} {Γ₀ Γ₁ : Ctx Δ n} {v : Value (K ∷ Δ) n} {T : NfTy (K ∷ Δ) (KV KT m)}
    → wkCtx {K = K} Γ₀ ⊢ᵥ v ⇒ T ⊣ wkCtx Γ₁
    → Σ (Ctx Δ n) λ G →
        Σ (Ctx Δ n) λ G′ →
          RemoveCtx Γ₀ G Γ₁ × (wkCtx {K = K} G ⊢ᵥ v ⇒ T ⊣ wkCtx G′) × AllUsed G′

  strip-value-send₃-case :
    ∀ {Δ n} {Γ₀ Γ₁ : Ctx Δ n} {T : Ty Δ TLin} {S : Ty Δ SLin} {v : Value Δ n}
    → Γ₀ ⊢ᵥ Value.V-Send₃ T S v
        ⇒ sendResultNf (normalizeTy T) (normalizeTy S) ⊣ Γ₁
    → Σ (Ctx Δ n) λ G →
        Σ (Ctx Δ n) λ G′ →
          RemoveCtx Γ₀ G Γ₁ ×
          (G ⊢ᵥ Value.V-Send₃ T S v
            ⇒ sendResultNf (normalizeTy T) (normalizeTy S) ⊣ G′) ×
          AllUsed G′

  strip-synth :
    ∀ {Δ n K} {Γ₀ Γ₁ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ K}
    → Γ₀ ⊢ e ⇒ T ⊣ Γ₁
    → Σ (Ctx Δ n) λ G →
        Σ (Ctx Δ n) λ G′ →
          RemoveCtx Γ₀ G Γ₁ × (G ⊢ e ⇒ T ⊣ G′) × AllUsed G′

strip-value-abs-case :
  ∀ {Δ n} {Γ₀ Γ₁ : Ctx Δ n} {T : Ty Δ TLin} {U : NfTy Δ TLin} {e : Expr Δ (suc n)}
  → Γ₀ ⊢ᵥ Value.V-Abs T e ⇒ linArrNf (normalizeTy T) U ⊣ Γ₁
  → Σ (Ctx Δ n) λ G →
      Σ (Ctx Δ n) λ G′ →
        RemoveCtx Γ₀ G Γ₁ × (G ⊢ᵥ Value.V-Abs T e ⇒ linArrNf (normalizeTy T) U ⊣ G′) × AllUsed G′
strip-value-abs-case {T = T} {U = U} {e = e} d
  with abs-inversion d
... | U′ , eq , body
  with linArrNf-injective eq
... | _ , eqU
  with strip-value-abs {T = T} {U = U′} {e = e} body
... | G , G′ , r , d′ , au =
  G , G′ , r ,
  subst
    (λ X → G ⊢ᵥ Value.V-Abs T e ⇒ X ⊣ G′)
    (cong (linArrNf (normalizeTy T)) (sym eqU))
    (TV-Abs d′) ,
  au

strip-value-rec-case :
  ∀ {Δ n} {Γ₀ Γ₁ : Ctx Δ n} {T U : Ty Δ TLin} {v : Value Δ (suc n)}
  → Γ₀ ⊢ᵥ Value.V-Rec T U v ⇒ linArrNf (normalizeTy T) (normalizeTy U) ⊣ Γ₁
  → Σ (Ctx Δ n) λ G →
      Σ (Ctx Δ n) λ G′ →
        RemoveCtx Γ₀ G Γ₁ × (G ⊢ᵥ Value.V-Rec T U v ⇒ linArrNf (normalizeTy T) (normalizeTy U) ⊣ G′) × AllUsed G′
strip-value-rec-case {Γ₀ = Γ₀} {T = T} {U = U} {v = v} d
  with rec-inversion d
... | eqΓ , refl , body
  with strip-value-rec {Γ₀ = Γ₀} {T = T} {U = U} {v = v} body
... | G , r , d′ , au =
  G , G ,
  subst (λ X → RemoveCtx Γ₀ G X) eqΓ r ,
  TV-Rec d′ ,
  au

strip-value-tabs-case :
  ∀ {Δ n K m} {Γ₀ Γ₁ : Ctx Δ n} {v : Value (K ∷ Δ) n} {T : NfTy (K ∷ Δ) (KV KT m)}
  → Γ₀ ⊢ᵥ Value.V-TAbs K v ⇒ polyNf T ⊣ Γ₁
  → Σ (Ctx Δ n) λ G →
      Σ (Ctx Δ n) λ G′ →
        RemoveCtx Γ₀ G Γ₁ × (G ⊢ᵥ Value.V-TAbs K v ⇒ polyNf T ⊣ G′) × AllUsed G′
strip-value-tabs-case {K = K} {v = v} {T = T} d
  with tabs-inversion d
... | T′ , eq , body
  with polyNf-injective eq
... | eqT
  with strip-value-tabs {K = K} {v = v} {T = T′} body
... | G , G′ , r , d′ , au =
  G , G′ , r ,
  subst
    (λ X → G ⊢ᵥ Value.V-TAbs K v ⇒ X ⊣ G′)
    (cong polyNf (sym eqT))
    (TV-TAbs d′) ,
  au

strip-check :
  ∀ {Δ n pk m} {Γ₀ Γ₁ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ (KV pk m)}
  → Γ₀ ⊢ e ⇐ T ⊣ Γ₁
  → Σ (Ctx Δ n) λ G →
      Σ (Ctx Δ n) λ G′ →
        RemoveCtx Γ₀ G Γ₁ × (G ⊢ e ⇐ T ⊣ G′) × AllUsed G′
strip-check (T-Check d sub)
  with strip-synth d
... | G , G′ , r , d′ , au = G , G′ , r , T-Check d′ sub , au

mutual
  strip-value :
    ∀ {Δ n K} {Γ₀ Γ₁ : Ctx Δ n} {v : Value Δ n} {T : NfTy Δ K}
    → Γ₀ ⊢ᵥ v ⇒ T ⊣ Γ₁
    → Σ (Ctx Δ n) λ G →
        Σ (Ctx Δ n) λ G′ →
          RemoveCtx Γ₀ G Γ₁ × (G ⊢ᵥ v ⇒ T ⊣ G′) × AllUsed G′
  strip-value {Γ₀ = Γ₀} (TV-Const cT) =
    allUsedCtx Γ₀ , allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ , TV-Const cT , allUsedCtx-AllUsed Γ₀
  strip-value (TV-Var-Lin p)
    with strip-take p
  ... | G , G′ , r , p′ , au = G , G′ , r , TV-Var-Lin p′ , au
  strip-value {Γ₀ = Γ₀} (TV-Var-Un x∈) =
    allUsedCtx Γ₀ , allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ , TV-Var-Un (allUsedCtx-∋ᵘ x∈) , allUsedCtx-AllUsed Γ₀
  strip-value d@(TV-Abs _)
    with strip-value-abs-case d
  ... | G , G′ , r , d′ , au = G , G′ , r , d′ , au
  strip-value d@(TV-Rec _)
    with strip-value-rec-case d
  ... | G , G′ , r , d′ , au = G , G′ , r , d′ , au
  strip-value d@(TV-TAbs _)
    with strip-value-tabs-case d
  ... | G , G′ , r , d′ , au = G , G′ , r , d′ , au
  strip-value (TV-Pair d₁ d₂) 
    with strip-value d₁
  ... | G₁ , G₁′ , r₁ , d₁′ , au₁
    with strip-value d₂
  ... | G₂ , G₂′ , r₂ , d₂′ , au₂ 
    with remove-compose-frame r₁ r₂
  ... | G₁₂ , r₁₂ , f =
    G₁₂ , G₂′ ,
    (r₁₂ , (TV-Pair (replay-value-allUsed d₁′ f au₁) d₂′) , au₂)
  strip-value {Γ₀ = Γ₀} TV-Receive₁ =
    allUsedCtx Γ₀ , allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ , TV-Receive₁ , allUsedCtx-AllUsed Γ₀
  strip-value {Γ₀ = Γ₀} TV-Receive₂ =
    allUsedCtx Γ₀ , allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ , TV-Receive₂ , allUsedCtx-AllUsed Γ₀
  strip-value {Γ₀ = Γ₀} TV-Send₁ =
    allUsedCtx Γ₀ , allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ , TV-Send₁ , allUsedCtx-AllUsed Γ₀
  strip-value {Γ₀ = Γ₀} TV-Send₂ =
    allUsedCtx Γ₀ , allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ , TV-Send₂ , allUsedCtx-AllUsed Γ₀
  strip-value d@(TV-Send₃ _)
    with strip-value-send₃-case d
  ... | G , G′ , r , d′ , au = G , G′ , r , d′ , au
  strip-value {Γ₀ = Γ₀} TV-Select₁ =
    allUsedCtx Γ₀ , allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ , TV-Select₁ , allUsedCtx-AllUsed Γ₀
  strip-value {Γ₀ = Γ₀} TV-Select₂ =
    allUsedCtx Γ₀ , allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ , TV-Select₂ , allUsedCtx-AllUsed Γ₀

mutual
  leftover-value :
    ∀ {Δ n K} {Γ₀ Γ₁ : Ctx Δ n} {v : Value Δ n} {T : NfTy Δ K}
    → Γ₀ ⊢ᵥ v ⇒ T ⊣ Γ₁
    → Σ (Ctx Δ n) λ G → RemoveCtx Γ₀ G Γ₁
  leftover-value (TV-Const _) = _ , remove-refl _
  leftover-value (TV-Var-Lin p) = leftover-take p
  leftover-value (TV-Var-Un _) = _ , remove-refl _
  leftover-value (TV-Abs d) =
    let G , r = leftover-synth d
        G′ , r′ = strip-lin-used r
    in G′ , r′
  leftover-value (TV-Rec d) =
    let G , r = leftover-check d
        G′ , r′ = strip-un-same r
    in G′ , r′
  leftover-value (TV-TAbs d) =
    let G , r = leftover-value d
        G′ , r′ = strip-wk r
    in G′ , r′
  leftover-value (TV-Pair d₁ d₂) =
    let G₁ , r₁ = leftover-value d₁
        G₂ , r₂ = leftover-value d₂
        G , r = remove-compose r₁ r₂
    in G , r
  leftover-value TV-Receive₁ = _ , remove-refl _
  leftover-value TV-Receive₂ = _ , remove-refl _
  leftover-value TV-Send₁ = _ , remove-refl _
  leftover-value TV-Send₂ = _ , remove-refl _
  leftover-value (TV-Send₃ d) = leftover-check d
  leftover-value TV-Select₁ = _ , remove-refl _
  leftover-value TV-Select₂ = _ , remove-refl _

  leftover-synth :
    ∀ {Δ n K} {Γ₀ Γ₁ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ K}
    → Γ₀ ⊢ e ⇒ T ⊣ Γ₁
    → Σ (Ctx Δ n) λ G → RemoveCtx Γ₀ G Γ₁
  leftover-synth (T-Val d) = leftover-value d
  leftover-synth (T-Pair d₁ d₂) =
    let G₁ , r₁ = leftover-synth d₁
        G₂ , r₂ = leftover-synth d₂
        G , r = remove-compose r₁ r₂
    in G , r
  leftover-synth (T-App d₁ d₂) =
    let G₁ , r₁ = leftover-synth d₁
        G₂ , r₂ = leftover-check d₂
        G , r = remove-compose r₁ r₂
    in G , r
  leftover-synth (T-LetUnit d₁ d₂) =
    let G₁ , r₁ = leftover-check d₁
        G₂ , r₂ = leftover-synth d₂
        G , r = remove-compose r₁ r₂
    in G , r
  leftover-synth (T-LetPair d₁ d₂) =
    let G₁ , r₁ = leftover-synth d₁
        G₂ , r₂ = leftover-synth d₂
        G₂′ , r₂′ = strip-lin-used₂ r₂
        G , r = remove-compose r₁ r₂′
    in G , r
  leftover-synth (T-Match {B = B} d _ bs _) =
    let G₁ , r₁ = leftover-synth d
        G₂ , r₂ = leftover-synth (bs zero)
        G₂′ , r₂′ = strip-lin-used r₂
        G , r = remove-compose r₁ r₂′
    in G , r
  leftover-synth (T-TApp d) = leftover-synth d

  leftover-check :
    ∀ {Δ n pk m} {Γ₀ Γ₁ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ (KV pk m)}
    → Γ₀ ⊢ e ⇐ T ⊣ Γ₁
    → Σ (Ctx Δ n) λ G → RemoveCtx Γ₀ G Γ₁
  leftover-check (T-Check d _) = leftover-synth d
