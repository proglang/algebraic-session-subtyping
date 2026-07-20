module ExprTypingStripFresh where

open import Data.List using (List; _∷_)
import Data.Fin.Subset as Subset
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Kinds
import NormalTypes as NT
open import ExprSyntax using (NfTy; Expr; Value; E-Val)
open import ExprNormalTyping
open import ExprContextProperties using
  ( AllUsed
  ; AU-∅
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
  ; remove-unique
  ; strip-rm-lin
  ; strip-rm-un
  )
open import ExprContextShape using
  ( _~Ctx_
  ; ∅~∅
  ; Lin~Lin
  ; Un~Un
  ; Lin~Used
  ; Used~Used
  ; value-preserves-~Ctx
  ; synth-preserves-~Ctx
  ; check-preserves-~Ctx
  )
open import ExprTypingProperties using
  ( replay-value-allUsed
  ; replay-synth-allUsed
  ; replay-check-allUsed
  )
open import ExprTypingLeftover using
  ( strip-take
  ; remove-compose-frame
  ; strip-wk
  )

allUsed-shape-stable :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
  → AllUsed Γ₁
  → Γ₁ ~Ctx Γ₂
  → Γ₁ ≡ Γ₂
allUsed-shape-stable AU-∅ ∅~∅ = refl
allUsed-shape-stable (AU-used au) (Used~Used shape) =
  cong (B-Used _ ▻_) (allUsed-shape-stable au shape)
allUsed-shape-stable (AU-un au) (Un~Un shape) =
  cong (B-Un _ ▻_) (allUsed-shape-stable au shape)

shape-allUsed-output :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
  → Γ₁ ~Ctx Γ₂
  → AllUsed Γ₂
  → Γ₂ ≡ allUsedCtx Γ₁
shape-allUsed-output ∅~∅ AU-∅ = refl
shape-allUsed-output (Lin~Lin shape) ()
shape-allUsed-output (Lin~Used shape) (AU-used au) =
  cong (B-Used _ ▻_) (shape-allUsed-output shape au)
shape-allUsed-output (Un~Un shape) (AU-un au) =
  cong (B-Un _ ▻_) (shape-allUsed-output shape au)
shape-allUsed-output (Used~Used shape) (AU-used au) =
  cong (B-Used _ ▻_) (shape-allUsed-output shape au)

wk-remove :
  ∀ {Δ n K} {Γ₀ G Γ₁ : Ctx Δ n}
  → RemoveCtx Γ₀ G Γ₁
  → RemoveCtx
      (wkCtx {K = K} Γ₀)
      (wkCtx {K = K} G)
      (wkCtx {K = K} Γ₁)
wk-remove RM-∅ = RM-∅
wk-remove (RM-drop r) = RM-drop (wk-remove r)
wk-remove (RM-allused r) = RM-allused (wk-remove r)
wk-remove (RM-lin r) = RM-lin (wk-remove r)
wk-remove (RM-un r) = RM-un (wk-remove r)

wk-allUsedCtx :
  ∀ {Δ n K}
    (Γ : Ctx Δ n)
  → allUsedCtx (wkCtx {K = K} Γ)
      ≡
    wkCtx {K = K} (allUsedCtx Γ)
wk-allUsedCtx ∅ = refl
wk-allUsedCtx (B-Lin T ▻ Γ) =
  cong (B-Used (wkNfTy T) ▻_) (wk-allUsedCtx Γ)
wk-allUsedCtx (B-Un T ▻ Γ) =
  cong (B-Un (wkNfTy T) ▻_) (wk-allUsedCtx Γ)
wk-allUsedCtx (B-Used T ▻ Γ) =
  cong (B-Used (wkNfTy T) ▻_) (wk-allUsedCtx Γ)

mutual

  strip-value :
    ∀ {Δ n pk m}
      {Γ₀ Γ₁ : Ctx Δ n}
      {v : Value Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γ₀ ⊢ᵥ v ⇒ T ⊣ Γ₁
    → Σ (Ctx Δ n) λ G →
        Σ (Ctx Δ n) λ G′ →
          RemoveCtx Γ₀ G Γ₁
          × (G ⊢ᵥ v ⇒ T ⊣ G′)
          × AllUsed G′
  strip-value {Γ₀ = Γ₀} (TV-Const cT) =
    allUsedCtx Γ₀ ,
    allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ ,
    TV-Const cT ,
    allUsedCtx-AllUsed Γ₀
  strip-value (TV-Var-Lin take)
    with strip-take take
  ... | G , G′ , r , take′ , au =
    G , G′ , r , TV-Var-Lin take′ , au
  strip-value {Γ₀ = Γ₀} (TV-Var-Un x∈) =
    allUsedCtx Γ₀ ,
    allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ ,
    TV-Var-Un (allUsedCtx-∋ᵘ x∈) ,
    allUsedCtx-AllUsed Γ₀
  strip-value (TV-Abs {T = T} {U = U} body)
    with strip-synth body
  ... | Gfull , Gout , r , body′ , au
    with strip-rm-lin r
  ... | G , refl , rtail
    =
    G ,
    allUsedCtx G ,
    rtail ,
    TV-Abs
      (subst
        (λ X → (T ∷ˡ G) ⊢ _ ⇒ U ⊣ X)
        (shape-allUsed-output
          (synth-preserves-~Ctx body′)
          au)
        body′) ,
    allUsedCtx-AllUsed G
  strip-value {Γ₀ = Γ₀} (TV-Rec {T = T} {U = U} body)
    with strip-check body
  ... | Gfull , Gout , r , body′ , au
    with strip-rm-un r
  ... | G , refl , r
    with remove-unique r (remove-allUsedCtx Γ₀)
  ... | eqG =
    G ,
    G ,
    r ,
    TV-Rec
      (subst
        (λ X →
          (NT.N-Arrow {m = Un} T U ∷ᵘ G)
            ⊢ E-Val _ ⇐ NT.N-Arrow {m = Un} T U
            ⊣ X)
        (sym
          (allUsed-shape-stable
            (AU-un
              (subst AllUsed (sym eqG)
                (allUsedCtx-AllUsed Γ₀)))
            (check-preserves-~Ctx body′)))
        body′) ,
    subst AllUsed (sym eqG) (allUsedCtx-AllUsed Γ₀)
  strip-value {Γ₀ = Γ₀} {Γ₁ = Γ₁} (TV-TAbs {K = K} body)
    with strip-value body
  ... | Gw , Gw′ , r , body′ , au
    with strip-wk r
  ... | G , rbase
    with remove-unique r (wk-remove rbase)
  ... | eqin =
    G ,
    allUsedCtx G ,
    rbase ,
    TV-TAbs
      (subst
        (λ X →
          wkCtx {K = K} G
            ⊢ᵥ _ ⇒ _
            ⊣ X)
        (trans
          (shape-allUsed-output
            (value-preserves-~Ctx body′)
            au)
          (trans
            (cong allUsedCtx eqin)
            (wk-allUsedCtx G)))
        (subst
          (λ X → X ⊢ᵥ _ ⇒ _ ⊣ Gw′)
          eqin
          body′)) ,
    allUsedCtx-AllUsed G
  strip-value (TV-Pair d₁ d₂)
    with strip-value d₁
  ... | G₁ , G₁′ , r₁ , d₁′ , au₁
    with strip-value d₂
  ... | G₂ , G₂′ , r₂ , d₂′ , au₂
    with remove-compose-frame r₁ r₂
  ... | G , r , frame =
    G ,
    G₂′ ,
    r ,
    TV-Pair
      (replay-value-allUsed d₁′ frame au₁)
      d₂′ ,
    au₂
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
  strip-value {Γ₀ = Γ₀} TV-Select₁ =
    allUsedCtx Γ₀ , allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ , TV-Select₁ , allUsedCtx-AllUsed Γ₀
  strip-value {Γ₀ = Γ₀} TV-Select₂ =
    allUsedCtx Γ₀ , allUsedCtx Γ₀ ,
    remove-allUsedCtx Γ₀ , TV-Select₂ , allUsedCtx-AllUsed Γ₀

  strip-synth :
    ∀ {Δ n pk m}
      {Γ₀ Γ₁ : Ctx Δ n}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γ₀ ⊢ e ⇒ T ⊣ Γ₁
    → Σ (Ctx Δ n) λ G →
        Σ (Ctx Δ n) λ G′ →
          RemoveCtx Γ₀ G Γ₁
          × (G ⊢ e ⇒ T ⊣ G′)
          × AllUsed G′
  strip-synth (T-Val d)
    with strip-value d
  ... | G , G′ , r , d′ , au =
    G , G′ , r , T-Val d′ , au
  strip-synth (T-Pair d₁ d₂)
    with strip-synth d₁
  ... | G₁ , G₁′ , r₁ , d₁′ , au₁
    with strip-synth d₂
  ... | G₂ , G₂′ , r₂ , d₂′ , au₂
    with remove-compose-frame r₁ r₂
  ... | G , r , frame =
    G , G₂′ , r ,
    T-Pair
      (replay-synth-allUsed d₁′ frame au₁)
      d₂′ ,
    au₂
  strip-synth (T-App d₁ d₂)
    with strip-synth d₁
  ... | G₁ , G₁′ , r₁ , d₁′ , au₁
    with strip-check d₂
  ... | G₂ , G₂′ , r₂ , d₂′ , au₂
    with remove-compose-frame r₁ r₂
  ... | G , r , frame =
    G , G₂′ , r ,
    T-App
      (replay-synth-allUsed d₁′ frame au₁)
      d₂′ ,
    au₂
  strip-synth (T-LetUnit d₁ d₂)
    with strip-check d₁
  ... | G₁ , G₁′ , r₁ , d₁′ , au₁
    with strip-synth d₂
  ... | G₂ , G₂′ , r₂ , d₂′ , au₂
    with remove-compose-frame r₁ r₂
  ... | G , r , frame =
    G , G₂′ , r ,
    T-LetUnit
      (replay-check-allUsed d₁′ frame au₁)
      d₂′ ,
    au₂
  strip-synth (T-LetPair {T = T} {U = U} d₁ d₂)
    with strip-synth d₁
  ... | G₁ , G₁′ , r₁ , d₁′ , au₁
    with strip-synth d₂
  ... | Gbody , Gout , rbody , d₂′ , au₂
    with strip-rm-lin rbody
  ... | Gtail , refl , rtail
    with strip-rm-lin rtail
  ... | G₂ , refl , r₂
    with remove-compose-frame r₁ r₂
  ... | G , r , frame =
    G , allUsedCtx G₂ , r ,
    T-LetPair
      (replay-synth-allUsed d₁′ frame au₁)
      (subst
        (λ X →
          (T ∷ˡ (U ∷ˡ G₂))
            ⊢ _ ⇒ _ ⊣ X)
        (shape-allUsed-output
          (synth-preserves-~Ctx d₂′)
          au₂)
        d₂′) ,
    allUsedCtx-AllUsed G₂
  strip-synth
      (T-Match
        {ss = ss}
        {v = variance}
        {ssbranches = ssbranches}
        {incl = incl}
        {ne = ne}
        {P = P}
        {S = S}
        {V = V}
        d bs j)
    with strip-synth d
  ... | G₁ , G₁′ , r₁ , d′ , au₁
    with strip-synth (bs (proj₁ ne) (proj₂ ne))
  ... | Gbody , Gout , rbody , b₀′ , au₂
    with strip-rm-lin rbody
  ... | G₂ , refl , r₂
    with remove-compose-frame r₁ r₂
  ... | G , r , frame =
    G ,
    allUsedCtx G₂ ,
    r ,
    T-Match
      {ss = ss}
      {v = variance}
      {ssbranches = ssbranches}
      {incl = incl}
      {ne = ne}
      (replay-synth-allUsed d′ frame au₁)
      branches′
      j ,
    allUsedCtx-AllUsed G₂
    where
    base-remove : RemoveCtx _ G₂ _
    base-remove = r₂

    branches′ :
      (i : _)
      → (i∈ : i Subset.∈ ssbranches)
      → (MatchBranchOutput ssbranches variance P S i i∈ ∷ˡ G₂)
          ⊢ _
            ⇒ V i i∈
            ⊣ (B-Used
                (MatchBranchOutput ssbranches variance P S i i∈)
                ▻ allUsedCtx G₂)
    branches′ i i∈
      with strip-synth (bs i i∈)
    ... | Gibody , Giout , ribody , bi , aui
      with strip-rm-lin ribody
    ... | Gi , refl , ri
      with remove-unique ri base-remove
    ... | refl =
      subst
        (λ X →
          (MatchBranchOutput ssbranches variance P S i i∈ ∷ˡ G₂)
            ⊢ _ ⇒ V i i∈ ⊣ X)
        (shape-allUsed-output
          (synth-preserves-~Ctx bi)
          aui)
        bi
  strip-synth (T-TApp d)
    with strip-synth d
  ... | G , G′ , r , d′ , au =
    G , G′ , r , T-TApp d′ , au

  strip-check :
    ∀ {Δ n pk m}
      {Γ₀ Γ₁ : Ctx Δ n}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk m)}
    → Γ₀ ⊢ e ⇐ T ⊣ Γ₁
    → Σ (Ctx Δ n) λ G →
        Σ (Ctx Δ n) λ G′ →
          RemoveCtx Γ₀ G Γ₁
          × (G ⊢ e ⇐ T ⊣ G′)
          × AllUsed G′
  strip-check (T-Check d sub)
    with strip-synth d
  ... | G , G′ , r , d′ , au =
    G , G′ , r , T-Check d′ sub , au
