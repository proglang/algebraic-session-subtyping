module ExprPreservationStep where

open import Data.Fin using (Fin; suc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
import Relation.Binary.PropositionalEquality as Eq

open import Kinds
import Duality
open import Kits
import ExprSemantics as ES
open import Types using (Ty; nf-⊕-ignores; nf-complete-; nf-sound+)
open import NormalTypes using (nfTyTy-fromNormalTy; N-Var; NV-Var)
open import NormalTypesSubstitution using (wkNFKind-sound; substNFTy)
open import AlgorithmicNFSubtyping using (_<:ₜ_; <:ₜ-refl; <:ₜ-trans; <:ₜ-arrow)
  renaming (<:ₜ-sub to ST-sub; <:ₜ-msg to ST-msg; <:ₜ-pair to ST-pair; <:ₚ′-up to SP-up)
open import ExprSyntax using (Expr; Value; E-App; E-Pair; E-TApp; E-Val; C-Close; C-Fork; C-New; C-Receive; C-Send; C-Unit; V-Const; V-Var; V-Pair; V-Abs; V-Rec; V-TAbs; V-Receive₁; V-Receive₂; V-Send₁; V-Send₂; V-Send₃)
open import ExprSemantics using (Label; L-Fork; L-New; L-RecvVal; L-SendVal; L-Close; Act-App; Act-TApp; Act-LetPair; Act-LetUnit; Act-PairV; Act-Rec; Act-Fork; Act-New; Act-Receive₁; Act-Receive₂; Act-Rcv; Act-Send₁; Act-Send₂; Act-Send₃; Act-Send; Act-Close; Act-AppL; _—[_]→_)
open import ExprSubstitution using (renameExpr; renameValue; substTyValue)
open import ExprSubstitutionTyping using (rec-unfold-preserves-value; subst-check-preserves-synth; subst2-preserves-synth; substTy-ReceiveTy1; substTy-SendTy1; substTyNf; substTy-normalizeTy; substTy-preserves-value; substTyNF-bridge)
open import ExprNormalTyping
open import ExprContextReduction using (_—ctx[_]→_; Ctx-β; Ctx-Fork; Ctx-New; Ctx-Rcv; Ctx-Send; Ctx-Close; ReplaceAt; R-here; R-there; MergeCtx; MC-∅; MC-used-left; MC-used-right; MC-un; RemoveCtx; RM-∅; RM-drop; RM-allused; RM-lin; RM-un; AllUsed; LinearDisjoint; LD-∅; LD-used-used; LD-used-live; LD-live-used; LD-un-un; recvChanNf; sendChanNf; sessNf; dualSessNf; unitLinNf)
  renaming (AU-∅ to AU-nil; AU-used to AU-cons-used; AU-un to AU-cons-un)
open import ExprTypingProperties using
  ( FrameCtx; FC-∅; FC-frame; FC-allused; FC-live; FC-un
  ; replay-value-allUsed; replay-check-allUsed
  )

open Kits.Syntax Types.Ty-Syntax hiding (Sort)
open Traversal Types.Ty-Traversal
open CTraversal record { fusion = Types.fusion }

sessionNfEq :
  ∀ {S : Ty [] SLin}
  → Types.nf
      Duality.⊕
      (λ x → Duality.dualizable-sub (Duality.d?⊥ x) (≤k-step (≤p-step <p-st) ≤m-refl))
      S
    ≡ ⌞ normalizeTy S ⌟
sessionNfEq {S} =
  Eq.trans
    (nf-⊕-ignores
      {T = S}
      (λ x → Duality.dualizable-sub (Duality.d?⊥ x) (≤k-step (≤p-step <p-st) ≤m-refl))
      Duality.d?⊥)
    (Eq.sym (nfTyTy-fromNormalTy (Types.nf-normal-type Duality.⊕ Duality.d?⊥ S)))

t-dual-preserves-≡c :
  ∀ {Δ m} {T U : Ty Δ (KV KS m)}
  → T Types.≡c U
  → Types.t-dual Duality.D-S T Types.≡c Types.t-dual Duality.D-S U
t-dual-preserves-≡c Types.≡c-refl = Types.≡c-refl
t-dual-preserves-≡c (Types.≡c-symm eq) =
  Types.≡c-symm (t-dual-preserves-≡c eq)
t-dual-preserves-≡c (Types.≡c-trns eq₁ eq₂) =
  Types.≡c-trns (t-dual-preserves-≡c eq₁) (t-dual-preserves-≡c eq₂)
t-dual-preserves-≡c (Types.≡c-sub (≤k-step ≤p-refl x) eq) =
  Types.≡c-sub (≤k-step ≤p-refl x) (t-dual-preserves-≡c eq)
t-dual-preserves-≡c
  {T = Types.T-Dual Duality.D-S (Types.T-Sub (≤k-step ≤p-refl x) T)}
  Types.≡c-sub-dual = Types.≡c-refl
t-dual-preserves-≡c
  {T = Types.T-Dual Duality.D-S (Types.T-Dual Duality.D-S U)}
  (Types.≡c-dual-dual Duality.D-S) =
  Types.dual-tinv U
t-dual-preserves-≡c Types.≡c-dual-end = Types.≡c-refl
t-dual-preserves-≡c
  {T = Types.T-Dual Duality.D-S (Types.T-Msg p T S)}
  Types.≡c-dual-msg
  rewrite Duality.invert-involution {p} =
    Types.≡c-msg Types.≡c-refl Types.≡c-refl
t-dual-preserves-≡c {T = Types.T-Msg p T S} (Types.≡c-msg-minus {p = p}) =
  Types.≡c-msg-minus {p = Duality.invert p}
t-dual-preserves-≡c (Types.≡c-msg eqT eqS) =
  Types.≡c-msg eqT (t-dual-preserves-≡c eqS)
t-dual-preserves-≡c (Types.≡c-fun {≤pk = ≤p-step ()} _ _)

shiftRen : ∀ (k : ℕ) {n} → Fin n → Fin (k + n)
shiftRen zero x = x
shiftRen (suc k) x = suc (shiftRen k x)

weakenValueBy : ∀ (k : ℕ) {n} → Value [] n → Value [] (k + n)
weakenValueBy k = renameValue (shiftRen k)

weakenExprBy : ∀ (k : ℕ) {n} → Expr [] n → Expr [] (k + n)
weakenExprBy k = renameExpr (shiftRen k)

extendUsed : ∀ (k : ℕ) {n} → Ctx [] n → Ctx [] (k + n)
extendUsed zero Γ = Γ
extendUsed (suc k) Γ = B-Used ▻ extendUsed k Γ

postulate
  preserve⇒-hard :
    ∀ {n k pk mult}
      {Γ₀ : Ctx [] n} {Γ₁ : Ctx [] (k + n)} {Γ₂ : Ctx [] n}
      {e₁ : Expr [] n} {e₂ : Expr [] (k + n)}
      {T : NfTy [] (KV pk mult)} {ℓ : Label n k}
    → e₁ —[ ℓ ]→ e₂
    → Γ₀ ⊢ e₁ ⇒ T ⊣ Γ₂
    → (s : Γ₀ —ctx[ ℓ ]→ Γ₁)
    → Σ (NfTy [] (KV pk mult)) λ U →
        (Γ₁ ⊢ e₂ ⇒ U ⊣ extendUsed k Γ₂)
        × (normalTyOf U <:ₜ normalTyOf T)

  weaken-synth :
    ∀ {n k K}
      {Γ₁ Γ₂ : Ctx [] n}
      {e : Expr [] n} {T : NfTy [] K}
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
    → extendUsed k Γ₁ ⊢ ES.weakenExprBy k e ⇒ T ⊣ extendUsed k Γ₂

  arrow-subtype-inversion :
    ∀ {A V U}
    → normalTyOf U <:ₜ normalTyOf (linArrNf A V)
    → Σ (NfTy [] TLin) λ A′ →
        Σ (NfTy [] TLin) λ V′ →
          (U ≡ linArrNf A′ V′)
          × (normalTyOf A <:ₜ normalTyOf A′)
          × (normalTyOf V′ <:ₜ normalTyOf V)

receiveTy-shape :
  ∀ {T : Ty [] TLin} {S : Ty [] SLin}
  → receiveNf (normalizeTy T) (normalizeTy S)
    ≡ linArrNf (recvChanNf (normalizeTy T) (normalizeTy S))
        (pairNf (normalizeTy T) (sessNf (normalizeTy S)))
sess-normalizeTy :
  ∀ {S : Ty [] SLin}
  → normalizeTy (SessLin S) ≡ sessNf (normalizeTy S)
sess-normalizeTy {S} =
  nfTyEq
    (cong (Ty.T-Sub (≤k-step (≤p-step <p-st) ≤m-refl))
      (Eq.trans
        (nfTyTy-fromNormalTy
          (Types.nf-normal-type
            Duality.⊕
            (λ x → Duality.dualizable-sub (Duality.d?⊥ x) (≤k-step (≤p-step <p-st) ≤m-refl))
            S))
        sessionNfEq))

receiveTy-shape = refl

sendTy-shape :
  ∀ {T : Ty [] TLin} {S : Ty [] SLin}
  → normalizeTy (LinArr (SessLin (Types.T-Msg Duality.⊕ (Types.T-Up T) S)) (SessLin S))
    ≡ linArrNf (sendChanNf (normalizeTy T) (normalizeTy S))
        (sessNf (normalizeTy S))
sendTy-shape {T} {S}
  =
  nfTyEq
    (cong₂ (Ty.T-Arrow (≤p-step <p-mt))
      (cong (Ty.T-Sub (≤k-step (≤p-step <p-st) ≤m-refl))
        (cong₂ (Ty.T-Msg Duality.⊕)
          refl
          (Eq.trans
            (nfTyTy-fromNormalTy
              (Types.nf-normal-type
                Duality.⊕
                (λ x → Duality.dualizable-sub (Duality.d?⊥ x) (≤k-step (≤p-step <p-st) ≤m-refl))
                S))
            sessionNfEq)))
      (cong (Ty.T-Sub (≤k-step (≤p-step <p-st) ≤m-refl))
        (Eq.trans
          (nfTyTy-fromNormalTy
            (Types.nf-normal-type
              Duality.⊕
              (λ x → Duality.dualizable-sub (Duality.d?⊥ x) (≤k-step (≤p-step <p-st) ≤m-refl))
              S))
          sessionNfEq)))

sendTy2-shape :
  ∀ {T : Ty [] TLin} {S : Ty [] SLin}
  → normalizeTy (SendTy T S)
    ≡ linArrNf (normalizeTy T)
        (linArrNf (sendChanNf (normalizeTy T) (normalizeTy S))
          (sessNf (normalizeTy S)))
sendTy2-shape {T} {S}
  =
  nfTyEq
    (cong₂ (Ty.T-Arrow (≤p-step <p-mt))
      refl
      (cong₂ (Ty.T-Arrow (≤p-step <p-mt))
        (cong (Ty.T-Sub (≤k-step (≤p-step <p-st) ≤m-refl))
          (cong₂ (Ty.T-Msg Duality.⊕)
            refl
            (Eq.trans
              (nfTyTy-fromNormalTy
                (Types.nf-normal-type
                  Duality.⊕
                  (λ x → Duality.dualizable-sub (Duality.d?⊥ x) (≤k-step (≤p-step <p-st) ≤m-refl))
                  S))
              sessionNfEq)))
        (cong (Ty.T-Sub (≤k-step (≤p-step <p-st) ≤m-refl))
          (Eq.trans
            (nfTyTy-fromNormalTy
              (Types.nf-normal-type
                Duality.⊕
                (λ x → Duality.dualizable-sub (Duality.d?⊥ x) (≤k-step (≤p-step <p-st) ≤m-refl))
                S))
            sessionNfEq))))

closeTy-shape :
  normalizeTy {Δ = []} CloseTy
    ≡ linArrNf (normalizeTy {Δ = []} EndLin) (normalizeTy {Δ = []} Types.T-Base)
closeTy-shape = refl

forkTy-shape :
  normalizeTy {Δ = []} ForkTy
    ≡ linArrNf (linArrNf unitLinNf unitLinNf) (normalizeTy {Δ = []} Types.T-Base)
forkTy-shape = refl

dualSess-normalizeTy :
  ∀ {S : Ty [] SLin}
  → normalizeTy (SessLin (Types.T-Dual Duality.D-S S)) ≡ dualSessNf (normalizeTy S)
dualSess-normalizeTy {S} =
  nfTyEq
    (Eq.trans
      (nfTyTy-fromNormalTy
        (Types.nf-normal-type
          Duality.⊕
          Duality.d?⊥
          (SessLin (Types.T-Dual Duality.D-S S))))
      (Eq.trans
        (Types.nf-complete
          Duality.d?⊥
          Duality.d?⊥
          (Types.≡c-sub
            (≤k-step (≤p-step <p-st) ≤m-refl)
            (Eq.subst
              (λ Z → Types.T-Dual Duality.D-S S Types.≡c Types.T-Dual Duality.D-S Z)
              (Eq.sym (nfTyTy-fromNormalTy (Types.nf-normal-type Duality.⊕ Duality.d?⊥ S)))
              (Types.≡c-trns
                (Types.dual-tinv S)
                (Types.≡c-trns
                  (t-dual-preserves-≡c (Types.≡c-symm (Types.nf-sound+ S)))
                  (Types.≡c-symm (Types.dual-tinv (Types.nf Duality.⊕ Duality.d?⊥ S))))))))
        (Eq.sym
          (nfTyTy-fromNormalTy
            (Types.nf-normal-type
              Duality.⊕
              Duality.d?⊥
              (SessLin (Types.T-Dual Duality.D-S ⌞ normalizeTy S ⌟)))))))

substTy-wkNfTy-id :
  ∀ {K K′} (T : NfTy [] K) (U : Ty [] K′) → substTyNf (wkNfTy {K′ = K′} T) U ≡ T
normalizeTy-id-local : ∀ {K} (T : NfTy [] K) → normalizeTy (⌞ T ⌟) ≡ T
normalizeTy-id-local = normalizeTy-id

substTy-wkNfTy-id {K′ = K′} T U =
  Eq.trans
      (cong (λ X → normalizeTy (X ⋯ ⦅ U ⦆ₛ)) (wkNFKind-sound {K′ = K′} T))
    (Eq.trans
      (cong normalizeTy (wk-cancels-⦅⦆-⋯ (⌞ T ⌟) U))
      (normalizeTy-id-local T))

substTy-wkBinding-id :
  ∀ {K} (b : Binding []) (U : Ty [] K) → ExprSubstitutionTyping.substTyBinding (wkBinding b) U ≡ b
substTy-wkBinding-id (B-Lin T) U = cong B-Lin (substTy-wkNfTy-id T U)
substTy-wkBinding-id (B-Un T) U = cong B-Un (substTy-wkNfTy-id T U)
substTy-wkBinding-id B-Used U = refl

substTy-wkCtx-id :
  ∀ {K n} (Γ : Ctx [] n) (U : Ty [] K) → ExprSubstitutionTyping.substTyCtx (wkCtx Γ) U ≡ Γ
substTy-wkCtx-id ∅ U = refl
substTy-wkCtx-id (b ▻ Γ) U =
  cong₂ (λ b′ Γ′ → b′ ▻ Γ′) (substTy-wkBinding-id b U) (substTy-wkCtx-id Γ U)

newInst-shape :
  ∀ {S : Ty [] SLin}
  → normalizeTy (Ty.T-Pair (SessLin S) (SessLin (Types.T-Dual Duality.D-S S)))
    ≡ pairNf (normalizeTy (SessLin S)) (dualSessNf (normalizeTy S))
newInst-shape {S}
  with dualSess-normalizeTy {S = S}
... | eq =
  nfTyEq
    (cong₂ Ty.T-Pair refl (cong ⌞_⌟ eq))

close-inversion :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {W : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Const C-Close ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ normalizeTy CloseTy)
close-inversion (TV-Const CT-Close) = refl , refl

fork-inversion :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {W : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Const C-Fork ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ normalizeTy ForkTy)
fork-inversion (TV-Const CT-Fork) = refl , refl

new-inversion :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {W : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Const C-New ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ normalizeTy NewTy)
new-inversion (TV-Const CT-New) = refl , refl

receive-const-shape :
  ∀ {W : NfTy [] TLin}
  → ConstTy C-Receive W
  → W ≡ receiveConstNf
receive-const-shape CT-Receive = refl

send-const-shape :
  ∀ {W : NfTy [] TLin}
  → ConstTy C-Send W
  → W ≡ sendConstNf
send-const-shape CT-Send = refl

take-from-membership :
  ∀ {n K}
    {Γ : Ctx [] n}
    {x : Fin n} {T : NfTy [] K}
  → Γ ∋ˡ x ∶ T
  → Σ (Ctx [] n) λ Γ′ → Γ ⊢ˡ x ∶ T ⊣ Γ′
take-from-membership hereˡ = _ , take-here
take-from-membership (thereˡˡ x∈) with take-from-membership x∈
... | Γ′ , take = _ , take-thereˡ take
take-from-membership (thereˡᵘ x∈) with take-from-membership x∈
... | Γ′ , take = _ , take-thereᵘ take
take-from-membership (thereˡ✖ x∈) with take-from-membership x∈
... | Γ′ , take = _ , take-there✖ take

take-unique :
  ∀ {n K}
    {Γ : Ctx [] n}
    {x : Fin n} {T U : NfTy [] K}
    {Γ₁ Γ₂ : Ctx [] n}
  → Γ ⊢ˡ x ∶ T ⊣ Γ₁
  → Γ ⊢ˡ x ∶ U ⊣ Γ₂
  → (T ≡ U) × (Γ₁ ≡ Γ₂)
take-unique take-here take-here = refl , refl
take-unique (take-thereˡ t₁) (take-thereˡ t₂)
  with take-unique t₁ t₂
... | eqT , eqΓ
  rewrite eqT | eqΓ = refl , refl
take-unique (take-thereᵘ t₁) (take-thereᵘ t₂)
  with take-unique t₁ t₂
... | eqT , eqΓ
  rewrite eqT | eqΓ = refl , refl
take-unique (take-there✖ t₁) (take-there✖ t₂)
  with take-unique t₁ t₂
... | eqT , eqΓ
  rewrite eqT | eqΓ = refl , refl

take-output-unique :
  ∀ {Δ n K K′}
    {Γ : Ctx Δ n}
    {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
    {Γ₁ Γ₂ : Ctx Δ n}
  → Γ ⊢ˡ x ∶ T ⊣ Γ₁
  → Γ ⊢ˡ x ∶ U ⊣ Γ₂
  → Γ₁ ≡ Γ₂
take-output-unique take-here take-here = refl
take-output-unique (take-thereˡ t₁) (take-thereˡ t₂)
  rewrite take-output-unique t₁ t₂ = refl
take-output-unique (take-thereᵘ t₁) (take-thereᵘ t₂)
  rewrite take-output-unique t₁ t₂ = refl
take-output-unique (take-there✖ t₁) (take-there✖ t₂)
  rewrite take-output-unique t₁ t₂ = refl

take-implies-membership :
  ∀ {Δ n K} {Γ Γ′ : Ctx Δ n} {x : Fin n} {T : NfTy Δ K}
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
  → Γ ∋ˡ x ∶ T
take-implies-membership take-here = hereˡ
take-implies-membership (take-thereˡ t) = thereˡˡ (take-implies-membership t)
take-implies-membership (take-thereᵘ t) = thereˡᵘ (take-implies-membership t)
take-implies-membership (take-there✖ t) = thereˡ✖ (take-implies-membership t)

used∷-injective :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n}
  → used∷ Γ₁ ≡ used∷ Γ₂
  → Γ₁ ≡ Γ₂
used∷-injective refl = refl

ctx-head : ∀ {Δ n} → Ctx Δ (suc n) → Binding Δ
ctx-head (b ▻ _) = b

ctx-tail : ∀ {Δ n} → Ctx Δ (suc n) → Ctx Δ n
ctx-tail (_ ▻ Γ) = Γ

lin-un-disjoint :
  ∀ {Δ n K K′}
    {Γ : Ctx Δ n}
    {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
  → Γ ∋ˡ x ∶ T
  → Γ ∋ᵘ x ∶ U
  → ⊥
lin-un-disjoint hereˡ ()
lin-un-disjoint (thereˡˡ x∈) (thereᵘˡ x∈′) = lin-un-disjoint x∈ x∈′
lin-un-disjoint (thereˡᵘ x∈) (thereᵘᵘ x∈′) = lin-un-disjoint x∈ x∈′
lin-un-disjoint (thereˡ✖ x∈) (thereᵘ✖ x∈′) = lin-un-disjoint x∈ x∈′

mutual
  postulate
    value-output-unique :
      ∀ {Δ n K K′} {Γ : Ctx Δ n} {v : Value Δ n}
        {T : NfTy Δ K} {U : NfTy Δ K′} {Γ₁ Γ₂ : Ctx Δ n}
      → Γ ⊢ᵥ v ⇒ T ⊣ Γ₁
      → Γ ⊢ᵥ v ⇒ U ⊣ Γ₂
      → Γ₁ ≡ Γ₂

    synth-output-unique :
      ∀ {Δ n K K′} {Γ : Ctx Δ n} {e : Expr Δ n}
        {T : NfTy Δ K} {U : NfTy Δ K′} {Γ₁ Γ₂ : Ctx Δ n}
      → Γ ⊢ e ⇒ T ⊣ Γ₁
      → Γ ⊢ e ⇒ U ⊣ Γ₂
      → Γ₁ ≡ Γ₂

    check-output-unique :
      ∀ {Δ n pk m pk′ m′} {Γ : Ctx Δ n} {e : Expr Δ n}
        {T : NfTy Δ (KV pk m)} {U : NfTy Δ (KV pk′ m′)} {Γ₁ Γ₂ : Ctx Δ n}
      → Γ ⊢ e ⇐ T ⊣ Γ₁
      → Γ ⊢ e ⇐ U ⊣ Γ₂
      → Γ₁ ≡ Γ₂

recvChan-subtype :
  ∀ {T₁ T₂ : NfTy [] TLin} {S₁ S₂ : NfTy [] SLin}
  → normalTyOf (recvChanNf T₁ S₁) <:ₜ normalTyOf (recvChanNf T₂ S₂)
  → (normalTyOf T₁ <:ₜ normalTyOf T₂) × (normalTyOf S₁ <:ₜ normalTyOf S₂)
recvChan-subtype (ST-sub (ST-msg (SP-up T<:T) S<:S)) = T<:T , S<:S

sendChan-subtype :
  ∀ {T₁ T₂ : NfTy [] TLin} {S₁ S₂ : NfTy [] SLin}
  → normalTyOf (sendChanNf T₁ S₁) <:ₜ normalTyOf (sendChanNf T₂ S₂)
  → (normalTyOf T₂ <:ₜ normalTyOf T₁) × (normalTyOf S₁ <:ₜ normalTyOf S₂)
sendChan-subtype (ST-sub (ST-msg (SP-up T₂<:T₁) S₁<:S₂)) = T₂<:T₁ , S₁<:S₂

sess-subtype :
  ∀ {S₁ S₂ : NfTy [] SLin}
  → normalTyOf S₁ <:ₜ normalTyOf S₂
  → normalTyOf (sessNf S₁) <:ₜ normalTyOf (sessNf S₂)
sess-subtype = ST-sub

pair-subtype :
  ∀ {pk₁ pk₂ m}
    {T₁ T₂ : NfTy [] (KV pk₁ m)}
    {U₁ U₂ : NfTy [] (KV pk₂ m)}
  → normalTyOf T₁ <:ₜ normalTyOf T₂
  → normalTyOf U₁ <:ₜ normalTyOf U₂
  → normalTyOf (pairNf T₁ U₁) <:ₜ normalTyOf (pairNf T₂ U₂)
pair-subtype = ST-pair

recvChan-injective :
  ∀ {T₁ T₂ : Ty [] TLin} {S₁ S₂ : Ty [] SLin}
  → SessLin (Types.T-Msg Duality.⊝ (Types.T-Up T₁) S₁)
      ≡ SessLin (Types.T-Msg Duality.⊝ (Types.T-Up T₂) S₂)
  → (T₁ ≡ T₂) × (S₁ ≡ S₂)
recvChan-injective refl = refl , refl

recvChanNf-injective :
  ∀ {T₁ T₂ : NfTy [] TLin} {S₁ S₂ : NfTy [] SLin}
  → recvChanNf T₁ S₁ ≡ recvChanNf T₂ S₂
  → (T₁ ≡ T₂) × (S₁ ≡ S₂)
recvChanNf-injective refl = refl , refl

receive₂-shape :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {Tᵣ : Ty [] TLin} {Sᵣ : Ty [] SLin}
    {A R : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Receive₂ Tᵣ Sᵣ ⇒ linArrNf A R ⊣ Γ₂
  → (Γ₁ ≡ Γ₂)
    × ((A ≡ recvChanNf (normalizeTy Tᵣ) (normalizeTy Sᵣ))
    × (R ≡ pairNf (normalizeTy Tᵣ) (sessNf (normalizeTy Sᵣ))))
receive₂-shape {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} vr
  with receive₂-inversion vr
... | refl , eqRecv
  with linArrNf-injective (Eq.trans eqRecv (receiveTy-shape {T = Tᵣ} {S = Sᵣ}))
... | eqA , eqR = refl , (eqA , eqR)

send₃-shape :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {Tᵣ : Ty [] TLin} {Sᵣ : Ty [] SLin}
    {v : Value [] n} {A R : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Send₃ Tᵣ Sᵣ v ⇒ linArrNf A R ⊣ Γ₂
  → (Γ₁ ⊢ E-Val v ⇐ normalizeTy Tᵣ ⊣ Γ₂)
    × ((A ≡ sendChanNf (normalizeTy Tᵣ) (normalizeTy Sᵣ))
    × (R ≡ sessNf (normalizeTy Sᵣ)))
send₃-inversion :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {T : Ty [] TLin} {S : Ty [] SLin}
    {v : Value [] n} {W : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Send₃ T S v ⇒ W ⊣ Γ₂
  → (Γ₁ ⊢ E-Val v ⇐ normalizeTy T ⊣ Γ₂)
    × (W ≡ sendResultNf (normalizeTy T) (normalizeTy S))
send₃-inversion (TV-Send₃ dv) = dv , refl

send₃-shape {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} vs
  with send₃-inversion vs
... | dv , eqSend
  with linArrNf-injective eqSend
... | eqA , eqR = dv , (eqA , eqR)

recv-app-inversion :
  ∀ {n}
    {Γ₀ Γ₂ : Ctx [] n}
    {x : Fin n}
    {Tᵣ : Ty [] TLin} {Sᵣ : Ty [] SLin}
    {T : NfTy [] TLin} {S : NfTy [] SLin}
    {R : NfTy [] TLin}
  → Γ₀ ⊢ E-App (E-Val (V-Receive₂ Tᵣ Sᵣ)) (E-Val (V-Var x)) ⇒ R ⊣ Γ₂
  → Γ₀ ∋ˡ x ∶ recvChanNf T S
  → (Γ₀ ⊢ˡ x ∶ recvChanNf T S ⊣ Γ₂)
    × ((normalTyOf T <:ₜ normalTyOf (normalizeTy Tᵣ))
    × ((normalTyOf S <:ₜ normalTyOf (normalizeTy Sᵣ))
    × (normalTyOf (pairNf T (sessNf S)) <:ₜ normalTyOf R)))
recv-app-inversion
  {Γ₀ = Γ₀} {Γ₂ = Γ₂} {x = x} {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} {T = T} {S = S} {R = R}
  (T-App (T-Val vr) (T-Check (T-Val vv) sub))
  x∈
  with receive₂-shape vr
... | refl , (eqT , eqR)
  with vv
... | TV-Var-Un x∈ᵘ = ⊥-elim (lin-un-disjoint x∈ x∈ᵘ)
... | TV-Var-Lin take
  with take-from-membership x∈
... | Γ₂′ , take₀
  with take-unique take take₀
... | eqChan , eqΓ
  rewrite eqΓ | eqChan | eqT | eqR
  with recvChan-subtype {T₁ = T} {T₂ = normalizeTy Tᵣ} {S₁ = S} {S₂ = normalizeTy Sᵣ} sub
... | T<:Tᵣ , S<:Sᵣ =
  take₀ , (T<:Tᵣ , (S<:Sᵣ ,
    pair-subtype
      {T₁ = T} {T₂ = normalizeTy Tᵣ}
      {U₁ = sessNf S} {U₂ = sessNf (normalizeTy Sᵣ)}
      T<:Tᵣ
      (sess-subtype {S₁ = S} {S₂ = normalizeTy Sᵣ} S<:Sᵣ)))

remove-frame :
  ∀ {n}
    {Γ₀ Γv Γx : Ctx [] n}
  → RemoveCtx Γ₀ Γv Γx
  → FrameCtx Γx Γv Γ₀
remove-frame RM-∅ = FC-∅
remove-frame (RM-drop rm) = FC-frame (remove-frame rm)
remove-frame (RM-allused rm) = FC-allused (remove-frame rm)
remove-frame (RM-lin rm) = FC-live (remove-frame rm)
remove-frame (RM-un rm) = FC-un (remove-frame rm)

remove-value :
  ∀ {n K}
    {Γ₀ Γv Γx Γv′ : Ctx [] n}
    {v : Value [] n} {T : NfTy [] K}
  → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
  → AllUsed Γv′
  → RemoveCtx Γ₀ Γv Γx
  → Γ₀ ⊢ᵥ v ⇒ T ⊣ Γx
remove-value dv au rm = replay-value-allUsed dv (remove-frame rm) au

remove-check :
  ∀ {n pk m}
    {Γ₀ Γv Γx Γv′ : Ctx [] n}
    {v : Value [] n} {T : NfTy [] (KV pk m)}
  → Γv ⊢ E-Val v ⇐ T ⊣ Γv′
  → AllUsed Γv′
  → RemoveCtx Γ₀ Γv Γx
  → Γ₀ ⊢ E-Val v ⇐ T ⊣ Γx
remove-check dv au rm = replay-check-allUsed dv (remove-frame rm) au

postulate
  send-payload-output :
    ∀ {n}
      {Γ₀ Γv Γx Γv′ Γm : Ctx [] n}
      {Tᵣ : Ty [] TLin} {T : NfTy [] TLin}
      {v : Value [] n}
    → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
    → AllUsed Γv′
    → RemoveCtx Γ₀ Γv Γx
    → Γ₀ ⊢ E-Val v ⇐ normalizeTy Tᵣ ⊣ Γm
    → Γm ≡ Γx

send-app-inversion-helper :
  ∀ {n}
    {Γ₀ Γv Γx Γv′ Γm Γ₂ : Ctx [] n}
    {x : Fin n}
    {Tᵣ : Ty [] TLin} {Sᵣ : Ty [] SLin}
    {T : NfTy [] TLin} {S : NfTy [] SLin}
    {A R : NfTy [] TLin} {v : Value [] n}
  → Γm ⊢ᵥ V-Var x ⇒ A ⊣ Γ₂
  → normalTyOf A <:ₜ normalTyOf (sendChanNf (normalizeTy Tᵣ) (normalizeTy Sᵣ))
  → Γx ∋ˡ x ∶ sendChanNf T S
  → RemoveCtx Γ₀ Γv Γx
  → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
  → AllUsed Γv′
  → Γ₀ ⊢ E-Val v ⇐ normalizeTy Tᵣ ⊣ Γm
  → R ≡ sessNf (normalizeTy Sᵣ)
  → (Γx ⊢ˡ x ∶ sendChanNf T S ⊣ Γ₂)
    × (normalTyOf (sessNf S) <:ₜ normalTyOf R)
send-app-inversion-helper {Tᵣ = Tᵣ} (TV-Var-Un x∈ᵘ) _ x∈ rm dv au dvsrc _
  with send-payload-output {Tᵣ = Tᵣ} dv au rm dvsrc
... | eqΓx
  rewrite eqΓx = ⊥-elim (lin-un-disjoint x∈ x∈ᵘ)
send-app-inversion-helper
  {Γ₀ = Γ₀} {Γx = Γx} {Γ₂ = Γ₂} {x = x}
  {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} {T = T} {S = S} {R = R}
  (TV-Var-Lin take) sub x∈ rm dv au dvsrc eqR
  with send-payload-output {Tᵣ = Tᵣ} dv au rm dvsrc
... | eqΓx
  rewrite eqΓx
  with take-from-membership x∈
... | Γ₂′ , take₀
  with take-unique take₀ take
... | eqChan , eqΓ
  rewrite eqΓ | eqR
  with sendChan-subtype
         {T₁ = T} {T₂ = normalizeTy Tᵣ} {S₁ = S} {S₂ = normalizeTy Sᵣ}
         (Eq.subst
           (λ X → normalTyOf X <:ₜ normalTyOf (sendChanNf (normalizeTy Tᵣ) (normalizeTy Sᵣ)))
           (Eq.sym eqChan)
           sub)
... | _ , S<:Sᵣ =
  take₀ , sess-subtype {S₁ = S} {S₂ = normalizeTy Sᵣ} S<:Sᵣ

replace-take :
  ∀ {n K}
    {Γ₀ Γx Γ₂ : Ctx [] n}
    {x : Fin n} {T U : NfTy [] K}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₂
  → ReplaceAt Γ₀ x (B-Lin U) Γx
  → Γx ⊢ˡ x ∶ U ⊣ Γ₂
replace-take take-here R-here = take-here
replace-take (take-thereˡ take) rep with rep
... | R-there rep′ = take-thereˡ (replace-take take rep′)
replace-take (take-thereᵘ take) rep with rep
... | R-there rep′ = take-thereᵘ (replace-take take rep′)
replace-take (take-there✖ take) rep with rep
... | R-there rep′ = take-there✖ (replace-take take rep′)

replace-used-output :
  ∀ {n K}
    {Γ₀ Γ₁ Γ₂ : Ctx [] n}
    {x : Fin n} {T : NfTy [] K}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₂
  → ReplaceAt Γ₀ x B-Used Γ₁
  → Γ₁ ≡ Γ₂
replace-used-output take-here R-here = refl
replace-used-output (take-thereˡ take) (R-there rep)
  rewrite replace-used-output take rep = refl
replace-used-output (take-thereᵘ take) (R-there rep)
  rewrite replace-used-output take rep = refl
replace-used-output (take-there✖ take) (R-there rep)
  rewrite replace-used-output take rep = refl

close-shape :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {A R : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Const C-Close ⇒ linArrNf A R ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (R ≡ normalizeTy Types.T-Base)
close-shape vr
  with close-inversion vr
... | refl , eqClose
  with linArrNf-injective {Δ = []} (Eq.trans eqClose closeTy-shape)
... | _ , eqR = refl , eqR

fork-shape :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {A R : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Const C-Fork ⇒ linArrNf A R ⊣ Γ₂
  → (Γ₁ ≡ Γ₂)
    × ((A ≡ linArrNf unitLinNf unitLinNf)
    × (R ≡ normalizeTy Types.T-Base))
fork-shape vr
  with fork-inversion vr
... | refl , eqFork
  with linArrNf-injective {Δ = []} (Eq.trans eqFork forkTy-shape)
... | eqA , eqR = refl , (eqA , eqR)

new-shape :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {T : NfTy (SLin ∷ []) TLin}
  → Γ₁ ⊢ᵥ V-Const C-New ⇒ polyNf T ⊣ Γ₂
  → (Γ₁ ≡ Γ₂)
    × (T ≡ normalizeTy (Ty.T-Pair (SessLin (Ty.T-Var (here refl)))
                               (SessLin (Types.T-Dual Duality.D-S (Ty.T-Var (here refl))))))
new-shape vr
  with new-inversion vr
... | refl , eqNew
  with polyNf-injective {Δ = []}
       (Eq.trans eqNew refl)
... | eqT = refl , eqT

receive₁-inversion :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {T : Ty [] TLin} {W : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Receive₁ T ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ receive1Nf (normalizeTy T))
receive₁-inversion TV-Receive₁ = refl , refl

substTy-ReceiveTy0 :
  ∀ {T : Ty [] TLin} {S : Ty [] SLin}
  → (ReceiveTy (wkTy {K′ = SLin} T) (Ty.T-Var (here refl))) ⋯ ⦅ S ⦆ₛ
    ≡ ReceiveTy T S
substTy-ReceiveTy0 {T = T} {S = S} =
  cong₂ ReceiveTy
    (wk-cancels-⦅⦆-⋯ T S)
    refl

receive₁-rigid :
  ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {T : NfTy [] TLin}
  → Γ ⊢ E-TApp (E-Val (V-Const C-Receive)) U ⇒ T ⊣ Γ′
  → Γ ≡ Γ′
receive₁-rigid (T-TApp (T-Val (TV-Const _))) = refl

receive₂-rigid :
  ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {S : Ty [] SLin} {T : NfTy [] TLin}
  → Γ ⊢ E-TApp (E-Val (V-Receive₁ U)) S ⇒ T ⊣ Γ′
  → Γ ≡ Γ′
receive₂-rigid (T-TApp (T-Val vr))
  with receive₁-inversion vr
... | refl , _ = refl

postulate
  receive₁-ty :
    ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {T : NfTy [] TLin}
    → Γ ⊢ E-TApp (E-Val (V-Const C-Receive)) U ⇒ T ⊣ Γ′
    → T ≡ normalizeTy (ReceiveTy1 U)

  receive₂-ty :
    ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {S : Ty [] SLin} {T : NfTy [] TLin}
    → Γ ⊢ E-TApp (E-Val (V-Receive₁ U)) S ⇒ T ⊣ Γ′
    → T ≡ normalizeTy (ReceiveTy U S)

  receive1Nf-shape :
    ∀ {T : Ty [] TLin}
    → receive1Nf (normalizeTy T) ≡ normalizeTy (ReceiveTy1 T)

  receiveNf-shape :
    ∀ {T : Ty [] TLin} {S : Ty [] SLin}
    → receiveNf (normalizeTy T) (normalizeTy S) ≡ normalizeTy (ReceiveTy T S)

substTy-SendTy0 :
  ∀ {T : Ty [] TLin} {S : Ty [] SLin}
  → (SendTy (wkTy {K′ = SLin} T) (Ty.T-Var (here refl))) ⋯ ⦅ S ⦆ₛ
    ≡ SendTy T S
substTy-SendTy0 {T = T} {S = S} =
  cong₂ SendTy
    (wk-cancels-⦅⦆-⋯ T S)
    refl

send₁-inversion :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {T : Ty [] TLin} {W : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Send₁ T ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ send1Nf (normalizeTy T))
send₁-inversion TV-Send₁ = refl , refl

send₂-inversion :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {T : Ty [] TLin} {S : Ty [] SLin} {W : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Send₂ T S ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ sendNf (normalizeTy T) (normalizeTy S))
send₂-inversion TV-Send₂ = refl , refl

send₁-rigid :
  ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {T : NfTy [] TLin}
  → Γ ⊢ E-TApp (E-Val (V-Const C-Send)) U ⇒ T ⊣ Γ′
  → Γ ≡ Γ′
send₁-rigid (T-TApp (T-Val (TV-Const _))) = refl

send₂-rigid :
  ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {S : Ty [] SLin} {T : NfTy [] TLin}
  → Γ ⊢ E-TApp (E-Val (V-Send₁ U)) S ⇒ T ⊣ Γ′
  → Γ ≡ Γ′
send₂-rigid (T-TApp (T-Val vr))
  with send₁-inversion vr
... | refl , _ = refl

postulate
  send₁-ty :
    ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {T : NfTy [] TLin}
    → Γ ⊢ E-TApp (E-Val (V-Const C-Send)) U ⇒ T ⊣ Γ′
    → T ≡ normalizeTy (SendTy1 U)

  send₂-ty :
    ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {S : Ty [] SLin} {T : NfTy [] TLin}
    → Γ ⊢ E-TApp (E-Val (V-Send₁ U)) S ⇒ T ⊣ Γ′
    → T ≡ normalizeTy (SendTy U S)

  send1Nf-shape :
    ∀ {T : Ty [] TLin}
    → send1Nf (normalizeTy T) ≡ normalizeTy (SendTy1 T)

  sendNf-shape :
    ∀ {T : Ty [] TLin} {S : Ty [] SLin}
    → sendNf (normalizeTy T) (normalizeTy S) ≡ normalizeTy (SendTy T S)

send₂-shape :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {Tᵣ : Ty [] TLin} {Sᵣ : Ty [] SLin}
    {A R : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Send₂ Tᵣ Sᵣ ⇒ linArrNf A R ⊣ Γ₂
  → (Γ₁ ≡ Γ₂)
    × ((A ≡ normalizeTy Tᵣ)
    × (R ≡ linArrNf (sendChanNf (normalizeTy Tᵣ) (normalizeTy Sᵣ))
             (sessNf (normalizeTy Sᵣ))))
send₂-shape {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} vr
  with send₂-inversion vr
... | refl , eqSend
  with linArrNf-injective eqSend
... | eqA , eqR = refl , (eqA , eqR)

replace-disjoint :
  ∀ {n K}
    {Γ₀ Γx Γv : Ctx [] n}
    {x : Fin n} {U : NfTy [] K} {K′} {T : NfTy [] K′}
  → Γ₀ ∋ˡ x ∶ T
  → LinearDisjoint Γ₀ Γv
  → ReplaceAt Γ₀ x (B-Lin U) Γx
  → LinearDisjoint Γx Γv
replace-disjoint hereˡ (LD-live-used ld) R-here = LD-live-used ld
replace-disjoint (thereˡˡ x∈) (LD-live-used ld) (R-there rep) =
  LD-live-used (replace-disjoint x∈ ld rep)
replace-disjoint (thereˡᵘ x∈) (LD-un-un ld) (R-there rep) =
  LD-un-un (replace-disjoint x∈ ld rep)
replace-disjoint (thereˡ✖ x∈) (LD-used-used ld) (R-there rep) =
  LD-used-used (replace-disjoint x∈ ld rep)
replace-disjoint (thereˡ✖ x∈) (LD-used-live ld) (R-there rep) =
  LD-used-live (replace-disjoint x∈ ld rep)

merge-frame :
  ∀ {n}
    {Γx Γv Γ₁ : Ctx [] n}
  → LinearDisjoint Γx Γv
  → MergeCtx Γx Γv Γ₁
  → FrameCtx Γx Γv Γ₁
merge-frame LD-∅ MC-∅ = FC-∅
merge-frame (LD-used-used ld) (MC-used-left merge) =
  FC-allused (merge-frame ld merge)
merge-frame (LD-used-used ld) (MC-used-right merge) =
  FC-allused (merge-frame ld merge)
merge-frame (LD-used-live ld) (MC-used-left {b = B-Lin _} merge) =
  FC-live (merge-frame ld merge)
merge-frame (LD-live-used ld) (MC-used-right merge) =
  FC-frame (merge-frame ld merge)
merge-frame (LD-un-un ld) (MC-un merge) =
  FC-un (merge-frame ld merge)

merge-value :
  ∀ {n K}
    {Γx Γv Γ₁ Γv′ : Ctx [] n}
    {v : Value [] n} {T : NfTy [] K}
  → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
  → AllUsed Γv′
  → LinearDisjoint Γx Γv
  → MergeCtx Γx Γv Γ₁
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γx
merge-value dv au ld merge = replay-value-allUsed dv (merge-frame ld merge) au

preserve⇒ :
  ∀ {n k pk mult}
    {Γ₀ : Ctx [] n} {Γ₁ : Ctx [] (k + n)} {Γ₂ : Ctx [] n}
    {e₁ : Expr [] n} {e₂ : Expr [] (k + n)}
    {T : NfTy [] (KV pk mult)} {ℓ : Label n k}
  → e₁ —[ ℓ ]→ e₂
  → Γ₀ ⊢ e₁ ⇒ T ⊣ Γ₂
  → (s : Γ₀ —ctx[ ℓ ]→ Γ₁)
  → Σ (NfTy [] (KV pk mult)) λ U →
      (Γ₁ ⊢ e₂ ⇒ U ⊣ extendUsed k Γ₂)
      × (normalTyOf U <:ₜ normalTyOf T)
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₂ = Γ₂}
  {T = R}
  {ℓ = ExprSemantics.L-β}
  (Act-App {T = T} {e = e} {v = v})
  (T-App {T = A} {U = R} (T-Val vr) pv)
  Ctx-β
  with abs-inversion vr
... | U , eqAbs , body
  with linArrNf-injective eqAbs
... | eqA , eqU
  rewrite eqA | eqU =
    U ,
      ( subst-check-preserves-synth {T = T} pv body
      , <:ₜ-refl (normalTyOf U))
preserve⇒
  {k = k}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₁ = Γ₁}
  {Γ₂ = Γ₃}
  {T = V}
  {ℓ = ℓ}
  (Act-AppL {e₁ = e₁} {e₂ = e₂} {e₃ = e₃} step)
  (T-App {Γ₂ = Γ₂} {Γ₃ = Γ₃} {T = A} {U = V} d₁ (T-Check pArg subArg))
  s
  with preserve⇒ step d₁ s
... | U , d₁′ , sub
  with arrow-subtype-inversion {A = A} {V = V} sub
... | A′ , V′ , eqU , A<:A′ , V′<:V =
  V′ ,
    ( T-App
        (Eq.subst
          (λ X → Γ₁ ⊢ e₂ ⇒ X ⊣ extendUsed k Γ₂)
          eqU
          d₁′)
        (T-Check (weaken-synth {k = k} pArg)
          (<:ₜ-trans subArg A<:A′))
    , V′<:V)
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = m}
  {Γ₀ = Γ₀}
  {Γ₂ = Γ₂}
  {T = R}
  {ℓ = ExprSemantics.L-β}
  (Act-TApp {K = K} {T = T} {v = v})
  (T-TApp {T = T′} (T-Val vr))
  Ctx-β
  with tabs-inversion vr
... | T₀ , eq , p
  rewrite polyNf-injective {Δ = []} eq =
    substNFTy T₀ (normalizeTy T) ,
      ( T-Val
          (Eq.subst
            (λ X → Γ₀ ⊢ᵥ substTyValue v T ⇒ X ⊣ Γ₂)
            (Eq.sym (substTyNF-bridge T₀ T))
            (Eq.subst
              (λ X → Γ₀ ⊢ᵥ substTyValue v T ⇒ substTyNf T₀ T ⊣ X)
              (substTy-wkCtx-id Γ₂ T)
              (Eq.subst
                (λ X → X ⊢ᵥ substTyValue v T ⇒ substTyNf T₀ T ⊣ ExprSubstitutionTyping.substTyCtx (wkCtx Γ₂) T)
                (substTy-wkCtx-id Γ₀ T)
                (substTy-preserves-value p))))
      , <:ₜ-refl (normalTyOf (substNFTy T₀ (normalizeTy T))))
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₂ = Γ₂}
  {T = T}
  {ℓ = ExprSemantics.L-β}
  Act-LetUnit
  (T-LetUnit (T-Check (T-Val (TV-Const CT-Unit)) _) synth₂)
  Ctx-β =
  T ,
    ( synth₂
    , <:ₜ-refl (normalTyOf T))
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₂ = Γ₂}
  {T = V}
  {ℓ = ExprSemantics.L-β}
  (Act-LetPair {u = u} {v = v} {e = e})
  (T-LetPair (T-Val pv) body)
  Ctx-β
  with pair-inversion′ pv
... | Γ₁ , pu , pv′ =
  V ,
    ( subst2-preserves-synth pu pv′ body
    , <:ₜ-refl (normalTyOf V))
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = m}
  {ℓ = ExprSemantics.L-β}
  Act-PairV
  (T-Pair {T = T} {U = U} (T-Val pu) (T-Val pv))
  Ctx-β =
  pairNf T U ,
    ( T-Val (TV-Pair pu pv)
    , <:ₜ-refl (normalTyOf (pairNf T U)))
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₂ = Γ₂}
  {T = R}
  {ℓ = ExprSemantics.L-β}
  (Act-Rec {T = T} {U = U} {v = v} {u = u})
  (T-App (T-Val vr) pu)
  Ctx-β
  with rec-inversion vr
... | refl , eqRec , _
  with linArrNf-injective eqRec
... | refl , refl =
  R ,
    ( T-App
        (T-Val (rec-unfold-preserves-value vr))
        pu
    , <:ₜ-refl (normalTyOf R))
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₂ = Γ₂}
  {T = R}
  {ℓ = ExprSemantics.L-β}
  (Act-Receive₁ {T = T})
  synth
  Ctx-β
  rewrite receive₁-rigid synth =
  normalizeTy (ReceiveTy1 T) ,
    ( T-Val
        (Eq.subst
          (λ X → Γ₀ ⊢ᵥ V-Receive₁ T ⇒ X ⊣ Γ₂)
          receive1Nf-shape
          TV-Receive₁)
    , Eq.subst
        (λ X → normalTyOf (normalizeTy (ReceiveTy1 T)) <:ₜ normalTyOf X)
        (Eq.sym (receive₁-ty synth))
        (<:ₜ-refl (normalTyOf (normalizeTy (ReceiveTy1 T)))))
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₂ = Γ₂}
  {T = R}
  {ℓ = ExprSemantics.L-β}
  (Act-Receive₂ {T = T} {S = S})
  synth
  Ctx-β
  rewrite receive₂-rigid synth =
  normalizeTy (ReceiveTy T S) ,
    ( T-Val
        (Eq.subst
          (λ X → Γ₀ ⊢ᵥ V-Receive₂ T S ⇒ X ⊣ Γ₂)
          receiveNf-shape
          TV-Receive₂)
    , Eq.subst
        (λ X → normalTyOf (normalizeTy (ReceiveTy T S)) <:ₜ normalTyOf X)
        (Eq.sym (receive₂-ty synth))
        (<:ₜ-refl (normalTyOf (normalizeTy (ReceiveTy T S)))))
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₂ = Γ₂}
  {T = R}
  {ℓ = ExprSemantics.L-β}
  (Act-Send₁ {T = T})
  synth
  Ctx-β
  rewrite send₁-rigid synth =
  normalizeTy (SendTy1 T) ,
    ( T-Val
        (Eq.subst
          (λ X → Γ₀ ⊢ᵥ V-Send₁ T ⇒ X ⊣ Γ₂)
          send1Nf-shape
          TV-Send₁)
    , Eq.subst
        (λ X → normalTyOf (normalizeTy (SendTy1 T)) <:ₜ normalTyOf X)
        (Eq.sym (send₁-ty synth))
        (<:ₜ-refl (normalTyOf (normalizeTy (SendTy1 T)))))
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₂ = Γ₂}
  {T = R}
  {ℓ = ExprSemantics.L-β}
  (Act-Send₂ {T = T} {S = S})
  synth
  Ctx-β
  rewrite send₂-rigid synth =
  normalizeTy (SendTy T S) ,
    ( T-Val
        (Eq.subst
          (λ X → Γ₀ ⊢ᵥ V-Send₂ T S ⇒ X ⊣ Γ₂)
          sendNf-shape
          TV-Send₂)
    , Eq.subst
        (λ X → normalTyOf (normalizeTy (SendTy T S)) <:ₜ normalTyOf X)
        (Eq.sym (send₂-ty synth))
        (<:ₜ-refl (normalTyOf (normalizeTy (SendTy T S)))))
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₂ = Γ₂}
  {T = R}
  {ℓ = ExprSemantics.L-β}
  (Act-Send₃ {T = T} {S = S} {v = v})
  (T-App (T-Val vr) pv)
  Ctx-β
  with send₂-shape {Tᵣ = T} {Sᵣ = S} vr
... | refl , (eqA , eqR)
  rewrite eqA | eqR =
    linArrNf (sendChanNf (normalizeTy T) (normalizeTy S)) (sessNf (normalizeTy S)) ,
      ( T-Val
          (TV-Send₃ pv)
      , <:ₜ-refl
          (normalTyOf (linArrNf (sendChanNf (normalizeTy T) (normalizeTy S))
                         (sessNf (normalizeTy S)))))
preserve⇒
  {k = suc (suc zero)}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₁ = Γ₁}
  {Γ₂ = Γ₂}
  {T = R}
  {ℓ = L-New S}
  Act-New
  (T-TApp {T = T′} (T-Val vr))
  Ctx-New
  with new-shape vr
... | refl , eqT
  rewrite eqT =
    pairNf (normalizeTy (SessLin S)) (dualSessNf (normalizeTy S)) ,
      ( T-Val
          (TV-Pair
            (TV-Var-Lin take-here)
            (TV-Var-Lin (take-there✖ take-here)))
      , Eq.subst
          (λ X → normalTyOf (pairNf (normalizeTy (SessLin S)) (dualSessNf (normalizeTy S))) <:ₜ normalTyOf X)
          (Eq.sym (newInst-shape {S = S}))
          (<:ₜ-refl (normalTyOf (pairNf (normalizeTy (SessLin S)) (dualSessNf (normalizeTy S))))))
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₁ = Γ₁}
  {Γ₂ = Γ₂}
  {e₁ = E-App (E-Val (V-Const C-Fork)) (E-Val v)}
  {e₂ = E-Val (V-Const C-Unit)}
  {T = R}
  {ℓ = L-Fork v}
  Act-Fork
  (T-App (T-Val vr) (T-Check (T-Val {T = T} vv) sub))
  (Ctx-Fork rm dv au)
  with fork-shape vr
... | refl , (eqA , eqR)
  with check-output-unique
         (Eq.subst
           (λ X → Γ₀ ⊢ E-Val v ⇐ X ⊣ Γ₂)
           eqA
           (T-Check (T-Val vv) sub))
         (remove-check dv au rm)
... | eqΓ
  rewrite eqΓ =
    normalizeTy Types.T-Base ,
      ( T-Val (TV-Const CT-Unit)
      , Eq.subst
          (λ X → normalTyOf (normalizeTy Types.T-Base) <:ₜ normalTyOf X)
          (Eq.sym eqR)
          (<:ₜ-refl (normalTyOf (normalizeTy Types.T-Base))))
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₁ = Γ₁}
  {Γ₂ = Γ₂}
  {e₁ = E-App (E-Val (V-Receive₂ Tᵣ Sᵣ)) (E-Val (V-Var x))}
  {e₂ = E-Val (V-Pair v (V-Var x))}
  {T = R}
  {ℓ = L-RecvVal x v}
  Act-Rcv d
  (Ctx-Rcv {T = T} {S = S} dv au ld x∈ rep merge)
  with recv-app-inversion {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} {T = T} {S = S} d x∈
... | take , _ , _ , sub =
    pairNf T (sessNf S) ,
      ( T-Val
          (TV-Pair
            (merge-value dv au (replace-disjoint x∈ ld rep) merge)
            (TV-Var-Lin (replace-take take rep)))
      , sub)
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₁ = Γ₁}
  {Γ₂ = Γ₂}
  {e₁ = E-App (E-Val (V-Send₃ Tᵣ Sᵣ v)) (E-Val (V-Var x))}
  {e₂ = E-Val (V-Var x)}
  {T = R}
  {ℓ = L-SendVal x v}
  Act-Send (T-App {T = A} (T-Val vr) (T-Check {U = U} (T-Val vv) sub))
  (Ctx-Send {Γx = Γx} {Γv = Γv} {Γv′ = Γv′} {T = T} {S = S} rm dv au x∈ rep)
  with send-app-inversion-helper
         {Γ₀ = Γ₀} {Γv = Γv} {Γx = Γx} {Γv′ = Γv′} {Γm = _} {Γ₂ = Γ₂}
         {x = x} {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} {T = T} {S = S} {A = U} {R = R} {v = v}
         vv
         (Eq.subst
           (λ X → normalTyOf U <:ₜ normalTyOf X)
           (proj₁ (proj₂ (send₃-shape {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} vr)))
           sub)
         x∈
         rm
         dv
         au
         (proj₁ (send₃-shape {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} vr))
         (proj₂ (proj₂ (send₃-shape {Tᵣ = Tᵣ} {Sᵣ = Sᵣ} vr)))
... | take , S<:R =
  sessNf S ,
    ( T-Val (TV-Var-Lin (replace-take take rep))
    , S<:R)
preserve⇒
  {k = 0}
  {pk = KT}
  {mult = Lin}
  {Γ₀ = Γ₀}
  {Γ₁ = Γ₁}
  {Γ₂ = Γ₂}
  {e₁ = E-App (E-Val (V-Const C-Close)) (E-Val (V-Var x))}
  {e₂ = E-Val (V-Const C-Unit)}
  {T = R}
  {ℓ = L-Close x}
  Act-Close
  (T-App (T-Val vr) (T-Check (T-Val (TV-Var-Lin take)) sub))
  (Ctx-Close x∈ rep)
  with close-shape vr
... | refl , eqR
  rewrite replace-used-output take rep =
    normalizeTy Types.T-Base ,
      ( T-Val (TV-Const CT-Unit)
      , Eq.subst
          (λ X → normalTyOf (normalizeTy Types.T-Base) <:ₜ normalTyOf X)
          (Eq.sym eqR)
          (<:ₜ-refl (normalTyOf (normalizeTy Types.T-Base))))
preserve⇒ step d s = preserve⇒-hard step d s

preserve⇐ :
  ∀ {n k pk mult}
    {Γ₀ : Ctx [] n} {Γ₁ : Ctx [] (k + n)} {Γ₂ : Ctx [] n}
    {e₁ : Expr [] n} {e₂ : Expr [] (k + n)}
    {T : NfTy [] (KV pk mult)} {ℓ : Label n k}
  → e₁ —[ ℓ ]→ e₂
  → Γ₀ ⊢ e₁ ⇐ T ⊣ Γ₂
  → (s : Γ₀ —ctx[ ℓ ]→ Γ₁)
  → Γ₁ ⊢ e₂ ⇐ T ⊣ extendUsed k Γ₂
preserve⇐ step (T-Check d U<:T) s
  with preserve⇒ step d s
... | U , d′ , U′<:U = T-Check d′ (<:ₜ-trans U′<:U U<:T)
