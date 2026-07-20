module ExprTypingLeftover where

open import Data.Fin using (Fin)
open import Data.List using (_∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Kinds
open import ExprSyntax using (NfTy; Expr; Value; E-Match)
open import ExprNormalTyping
open import ExprContextProperties using
  ( AllUsed
  ; AU-used
  ; AU-un
  ; FrameCtx
  ; RemoveCtx
  ; RM-∅
  ; RM-drop
  ; RM-allused
  ; RM-lin
  ; RM-un
  ; allUsedCtx
  ; allUsedCtx-AllUsed
  ; allUsedCtx-∋ᵘ
  ; remove-allUsedCtx
  ; mergeRemoveContext
  ; frame-sym
  ; strip-rm-lin
  ; strip-rm-un
  )

remove-compose-frame :
  ∀ {Δ n} {Γ₀ Γ₁ Γ₂ G₁ G₂ : Ctx Δ n}
  → (r₁ : RemoveCtx Γ₀ G₁ Γ₁)
  → (r₂ : RemoveCtx Γ₁ G₂ Γ₂)
  → Σ (Ctx Δ n) λ G →
      RemoveCtx Γ₀ G Γ₂ × FrameCtx G₂ G₁ G
remove-compose-frame r₁ r₂
  with mergeRemoveContext r₁ r₂
... | G , f , r = G , r , frame-sym f

used-head :
  ∀ {Δ n pk} {Γ₀ Γv Γx : Ctx Δ n} {b₀ b₁ : Binding Δ} {T : NfTy Δ (KV pk Lin)}
  → RemoveCtx (b₀ ▻ Γ₀) (B-Used T ▻ Γv) (b₁ ▻ Γx)
  → b₀ ≡ b₁
used-head (RM-drop _) = refl
used-head (RM-allused _) = refl

used-tail :
  ∀ {Δ n pk} {Γ₀ Γv Γx : Ctx Δ n} {b₀ b₁ : Binding Δ} {T : NfTy Δ (KV pk Lin)}
  → (r : RemoveCtx (b₀ ▻ Γ₀) (B-Used T ▻ Γv) (b₁ ▻ Γx))
  → RemoveCtx Γ₀ Γv Γx
used-tail (RM-drop r) = r
used-tail (RM-allused r) = r

lin-tail :
  ∀ {Δ n pk pk′}
    {Γ₀ Γv Γx : Ctx Δ n}
    {T : NfTy Δ (KV pk Lin)} {U : NfTy Δ (KV pk′ Lin)}
  → RemoveCtx (B-Lin T ▻ Γ₀) (B-Lin U ▻ Γv) (B-Used T ▻ Γx)
  → Σ (pk ≡ pk′) λ where
      refl → (T ≡ U) × RemoveCtx Γ₀ Γv Γx
lin-tail (RM-lin r) = refl , refl , r

lin-tail′ :
  ∀ {Δ n pk pk′ pk″}
    {Γ₀ Γv Γx : Ctx Δ n}
    {T : NfTy Δ (KV pk Lin)} {U : NfTy Δ (KV pk′ Lin)} {V : NfTy Δ (KV pk″ Lin)}
  → RemoveCtx (B-Lin T ▻ Γ₀) (B-Lin U ▻ Γv) (B-Used V ▻ Γx)
  → Σ (pk ≡ pk′) λ where
      refl → Σ (pk ≡ pk″) λ where
        refl → (T ≡ U) × (T ≡ V) × RemoveCtx Γ₀ Γv Γx
lin-tail′ (RM-lin r) = refl , refl , refl , refl , r

un-tail :
  ∀ {Δ n pk₁ pk₂ pk₃} {Γ₀ Γv Γx : Ctx Δ n}
    {T : NfTy Δ (KV pk₁ Un)} {U : NfTy Δ (KV pk₂ Un)} {V : NfTy Δ (KV pk₃ Un)}
  → RemoveCtx (B-Un T ▻ Γ₀) (B-Un U ▻ Γv) (B-Un V ▻ Γx)
  → Σ (pk₁ ≡ pk₂) λ where
      refl → Σ (pk₂ ≡ pk₃) λ where
        refl → (T ≡ U) × (U ≡ V) × RemoveCtx Γ₀ Γv Γx
un-tail (RM-un r) = refl , refl , refl , refl , r

un-result :
  ∀ {Δ n pk} {Γ₀ Γ₁ G : Ctx Δ n} {T U : NfTy Δ (KV pk Un)}
  → T ≡ U
  → RemoveCtx Γ₀ G Γ₁
  → RemoveCtx (B-Un T ▻ Γ₀) (B-Un T ▻ G) (B-Un U ▻ Γ₁)
un-result refl r = RM-un r

strip-wk :
  ∀ {Δ K n} {Γ₀ Γ₁ : Ctx Δ n} {G : Ctx (K ∷ Δ) n}
  → RemoveCtx (wkCtx {K = K} Γ₀) G (wkCtx Γ₁)
  → Σ (Ctx Δ n) λ G′ → RemoveCtx Γ₀ G′ Γ₁
strip-wk {Γ₀ = ∅} {Γ₁ = ∅} RM-∅ = ∅ , RM-∅
strip-wk {K = K} {Γ₀ = B-Used T ▻ Γ₀} {Γ₁ = B-Used U ▻ Γ₁} {G = B-Used V ▻ G} r
  rewrite wkBinding-injective {L = K} {b₁ = B-Used T} {b₂ = B-Used U} (used-head r)
  with strip-wk {K = K} (used-tail r)
... | G′ , r′ = B-Used U ▻ G′ , RM-allused r′
strip-wk {K = K} {Γ₀ = B-Lin T ▻ Γ₀} {Γ₁ = B-Used U ▻ Γ₁} {G = B-Lin V ▻ G} r
  with lin-tail′ r
... | refl , refl , eqTV , eqTU , r₀
  with strip-wk {K = K} r₀
... | G′ , r′
  rewrite wkNfTy-injective {K′ = K} eqTU
  = B-Lin U ▻ G′ , RM-lin r′
strip-wk {K = K} {Γ₀ = B-Lin T ▻ Γ₀} {Γ₁ = B-Lin U ▻ Γ₁} {G = B-Used V ▻ G} r
  rewrite wkBinding-injective {L = K} {b₁ = B-Lin T} {b₂ = B-Lin U} (used-head r)
  with strip-wk {K = K} (used-tail r)
... | G′ , r′ = B-Used U ▻ G′ , RM-drop r′
strip-wk {K = K} {Γ₀ = B-Un T ▻ Γ₀} {Γ₁ = B-Un U ▻ Γ₁} {G = B-Un V ▻ G} r
  with un-tail r
... | refl , refl , eq₁ , eq₂ , r₀
  with strip-wk {K = K} r₀
... | G′ , r′ =
  B-Un T ▻ G′ ,
  un-result (wkNfTy-injective {K′ = K} (trans eq₁ eq₂)) r′

leftover-take :
  ∀ {Δ n pk} {Γ₀ Γ₁ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Lin)}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₁
  → Σ (Ctx Δ n) λ G → RemoveCtx Γ₀ G Γ₁
leftover-take take-here = _ , RM-lin (remove-allUsedCtx _)
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
  ∀ {Δ n pk} {Γ₀ Γ₁ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Lin)}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₁
  → Σ (Ctx Δ n) λ G →
      Σ (Ctx Δ n) λ G′ →
        RemoveCtx Γ₀ G Γ₁ × (G ⊢ˡ x ∶ T ⊣ G′) × AllUsed G′
strip-take {Γ₀ = _ ▻ Γ} (take-here {T = T}) =
  (T ∷ˡ (allUsedCtx Γ)) , (B-Used T ▻ (allUsedCtx Γ)) ,
  (RM-lin (remove-allUsedCtx Γ)) , take-here , AU-used (allUsedCtx-AllUsed Γ)
strip-take (take-thereˡ {U = U} p)
  with strip-take p
... | G , G′ , r , p′ , au =
  (B-Used U ▻ G) , (B-Used U ▻ G′) ,
  RM-drop r , take-there✖ p′ , AU-used au
strip-take (take-thereᵘ {U = U} p)
  with strip-take p
... | G , G′ , r , p′ , au =
  (U ∷ᵘ G) , (U ∷ᵘ G′) ,
  RM-un r , take-thereᵘ p′ , AU-un au
strip-take (take-there✖ p)
  with strip-take p
... | G , G′ , r , p′ , au =
  (B-Used _ ▻ G) , (B-Used _ ▻ G′) ,
  RM-allused r , take-there✖ p′ , AU-used au

mutual
  leftover-value :
    ∀ {Δ n pk m} {Γ₀ Γ₁ : Ctx Δ n} {v : Value Δ n} {T : NfTy Δ (KV pk m)}
    → Γ₀ ⊢ᵥ v ⇒ T ⊣ Γ₁
    → Σ (Ctx Δ n) λ G → RemoveCtx Γ₀ G Γ₁
  leftover-value (TV-Const _) = _ , remove-allUsedCtx _
  leftover-value (TV-Var-Lin p) = leftover-take p
  leftover-value (TV-Var-Un _) = _ , remove-allUsedCtx _
  leftover-value (TV-Abs d) =
    let G , r = leftover-synth d
        G′ , _ , r′ = strip-rm-lin r
    in G′ , r′
  leftover-value (TV-Rec d) =
    let G , r = leftover-check d
        G′ , _ , r′ = strip-rm-un r
    in G′ , r′
  leftover-value (TV-TAbs d) =
    let G , r = leftover-value d
        G′ , r′ = strip-wk r
    in G′ , r′
  leftover-value (TV-Pair d₁ d₂) =
    let G₁ , r₁ = leftover-value d₁
        G₂ , r₂ = leftover-value d₂
        G , _ , r = mergeRemoveContext r₁ r₂
    in G , r
  leftover-value TV-Receive₁ = _ , remove-allUsedCtx _
  leftover-value TV-Receive₂ = _ , remove-allUsedCtx _
  leftover-value TV-Send₁ = _ , remove-allUsedCtx _
  leftover-value TV-Send₂ = _ , remove-allUsedCtx _
  leftover-value TV-Select₁ = _ , remove-allUsedCtx _
  leftover-value TV-Select₂ = _ , remove-allUsedCtx _

  leftover-synth :
    ∀ {Δ n pk m} {Γ₀ Γ₁ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ (KV pk m)}
    → Γ₀ ⊢ e ⇒ T ⊣ Γ₁
    → Σ (Ctx Δ n) λ G → RemoveCtx Γ₀ G Γ₁
  leftover-synth (T-Val d) = leftover-value d
  leftover-synth (T-Pair d₁ d₂) =
    let G₁ , r₁ = leftover-synth d₁
        G₂ , r₂ = leftover-synth d₂
        G , _ , r = mergeRemoveContext r₁ r₂
    in G , r
  leftover-synth (T-App d₁ d₂) =
    let G₁ , r₁ = leftover-synth d₁
        G₂ , r₂ = leftover-check d₂
        G , _ , r = mergeRemoveContext r₁ r₂
    in G , r
  leftover-synth (T-LetUnit d₁ d₂) =
    let G₁ , r₁ = leftover-check d₁
        G₂ , r₂ = leftover-synth d₂
        G , _ , r = mergeRemoveContext r₁ r₂
    in G , r
  leftover-synth (T-LetPair d₁ d₂) =
    let G₁ , r₁ = leftover-synth d₁
        G₂ , r₂ = leftover-synth d₂
        G₂′ , _ , r₂′ = strip-rm-lin r₂
        G₂″ , _ , r₂″ = strip-rm-lin r₂′
        G , _ , r = mergeRemoveContext r₁ r₂″
    in G , r
  leftover-synth {e = E-Match _ ne _} (T-Match d bs _) with ne
  ... | i , i∈ =
    let G₁ , r₁ = leftover-synth d
        G₂ , r₂ = leftover-synth (bs i i∈)
        G₂′ , _ , r₂′ = strip-rm-lin r₂
        G , _ , r = mergeRemoveContext r₁ r₂′
    in G , r
  leftover-synth (T-TApp d) = leftover-synth d

  leftover-check :
    ∀ {Δ n pk m} {Γ₀ Γ₁ : Ctx Δ n} {e : Expr Δ n} {T : NfTy Δ (KV pk m)}
    → Γ₀ ⊢ e ⇐ T ⊣ Γ₁
    → Σ (Ctx Δ n) λ G → RemoveCtx Γ₀ G Γ₁
  leftover-check (T-Check d _) = leftover-synth d
