module ExprTypingInversion where

open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

import Duality
open import Kinds
open import Kits
open import Variance using (Variance)
import Types
open import Types using (Ty)
open import NormalTypes using (N-Var; NV-Var; nfTyTy-fromNormalTy; toNormalTy)
open import AlgorithmicNFSubtyping using (_<:ₜ_; <:ₜ-sub; <:ₜ-msg; <:ₚ′-proto)
open import ExprSyntax
  using
  ( Expr
  ; Value
  ; E-Val
  ; E-App
  ; E-TApp
  ; V-Const
  ; V-Var
  ; V-Abs
  ; V-Rec
  ; V-TAbs
  ; V-Pair
  ; V-Receive₁
  ; V-Receive₂
  ; V-Send₁
  ; V-Send₂
  ; V-Select₂
  ; C-New
  ; C-Receive
  ; C-Send
  ; C-Close
  ; C-Fork
  )
open import ExprNormalTyping
open import NormalTypesSubstitution
  using
  ( NFSub
  ; wkNFKind-sound
  ; singleNFSub
  ; singleNFSub-sound
  ; substNFTy
  ; substNFTyWith
  ; substNFTy-sound
  )
import ExprSubstitutionTyping as EST
open import SubstitutionSubtyping using (subst-preserves-≡c)
open import ExprContextReduction
  using
  ( recvChanNf
  ; sendChanNf
  ; selectInNf
  ; selectOutNf
  ; sessNf
  ; unitLinNf
  ; dualSessNf
  )

open Kits.Syntax Types.Ty-Syntax hiding (Sort)
open Traversal Types.Ty-Traversal
open CTraversal record { fusion = Types.fusion }

infixr 1 _⊎₀_
data _⊎₀_ (A B : Set) : Set where
  inj₁₀ : A → A ⊎₀ B
  inj₂₀ : B → A ⊎₀ B

tabs-inversion :
  ∀ {Δ n K m} {Γ₁ Γ₂ : Ctx Δ n} {v : Value (K ∷ Δ) n} {W : NfTy Δ (KV KT m)}
  → Γ₁ ⊢ᵥ V-TAbs K v ⇒ W ⊣ Γ₂
  → Σ (NfTy (K ∷ Δ) (KV KT m)) λ T →
      (W ≡ polyNf T) × (wkCtx {K = K} Γ₁ ⊢ᵥ v ⇒ T ⊣ wkCtx Γ₂)
tabs-inversion (TV-TAbs {T = T} p) = T , refl , p

abs-inversion :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n} {T : Ty Δ TLin} {e : Expr Δ (suc n)} {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ V-Abs T e ⇒ W ⊣ Γ₂
  → Σ (NfTy Δ TLin) λ U →
      (W ≡ linArrNf (normalizeTy T) U) × ((normalizeTy T ∷ˡ Γ₁) ⊢ e ⇒ U ⊣ (B-Used (normalizeTy T) ▻ Γ₂))
abs-inversion (TV-Abs {U = U} p) = U , refl , p

pair-inversion :
  ∀ {Δ n m} {Γ₁ Γ₃ : Ctx Δ n} {u v : Value Δ n} {W : NfTy Δ (KV KT m)}
  → Γ₁ ⊢ᵥ V-Pair u v ⇒ W ⊣ Γ₃
  → Σ PreKind λ pk₁ →
      Σ PreKind λ pk₂ →
      Σ (NfTy Δ (KV pk₁ m)) λ T →
      Σ (NfTy Δ (KV pk₂ m)) λ U →
        Σ (Ctx Δ n) λ Γ₂ →
          (W ≡ pairNf T U) × ((Γ₁ ⊢ᵥ u ⇒ T ⊣ Γ₂) × (Γ₂ ⊢ᵥ v ⇒ U ⊣ Γ₃))
pair-inversion (TV-Pair {pk₁ = pk₁} {pk₂ = pk₂} p q) = pk₁ , pk₂ , _ , _ , _ , refl , (p , q)

pair-inversion′ :
  ∀ {Δ n pk₁ pk₂ m} {Γ₁ Γ₃ : Ctx Δ n} {u v : Value Δ n}
    {T : NfTy Δ (KV pk₁ m)} {U : NfTy Δ (KV pk₂ m)}
  → Γ₁ ⊢ᵥ V-Pair u v ⇒ pairNf T U ⊣ Γ₃
  → Σ (Ctx Δ n) λ Γ₂ →
      (Γ₁ ⊢ᵥ u ⇒ T ⊣ Γ₂) × (Γ₂ ⊢ᵥ v ⇒ U ⊣ Γ₃)
pair-inversion′ (TV-Pair p q) = _ , p , q

rec-inversion :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n} {T U : Ty Δ TLin} {v : Value Δ (suc n)} {W : NfTy Δ (KV KT Un)}
  → Γ₁ ⊢ᵥ V-Rec T U v ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) ×
    ((W ≡ unArrNf (normalizeTy T) (normalizeTy U)) ×
     ((unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)
       ⊢ E-Val v ⇐ unArrNf (normalizeTy T) (normalizeTy U)
       ⊣ (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)))
rec-inversion (TV-Rec p) = refl , refl , p

receive₂-inversion :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n} {T : Ty Δ TLin} {S : Ty Δ SLin} {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ V-Receive₂ T S ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ receiveNf (normalizeTy T) (normalizeTy S))
receive₂-inversion TV-Receive₂ = refl , refl

closeTy-shape :
  normalizeTy {Δ = []} CloseTy
    ≡ linArrNf (normalizeTy {Δ = []} EndLin) (normalizeTy {Δ = []} Types.T-Base)
closeTy-shape = refl

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
  with linArrNf-injective {Δ = []} (trans eqFork refl)
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
  with polyNf-injective {Δ = []} (trans eqNew refl)
... | eqT = refl , eqT

dualSess-normalizeTy :
  ∀ {S : Ty [] SLin}
  → normalizeTy (SessLin (Types.T-Dual Duality.D-S S)) ≡ dualSessNf (normalizeTy S)
dualSess-normalizeTy {S} =
  nfTyEq
    (trans
      (nfTyTy-fromNormalTy
        (Types.nf-normal-type
          Duality.⊕
          Duality.d?⊥
          (SessLin (Types.T-Dual Duality.D-S S))))
      (trans
        (Types.nf-complete
          Duality.d?⊥
          Duality.d?⊥
          (Types.≡c-sub
            (≤k-step (≤p-step <p-st) ≤m-refl)
            (subst
              (λ Z → Types.T-Dual Duality.D-S S Types.≡c Types.T-Dual Duality.D-S Z)
              (sym (nfTyTy-fromNormalTy (Types.nf-normal-type Duality.⊕ Duality.d?⊥ S)))
              (Types.≡c-trns
                (Types.dual-tinv S)
                (Types.≡c-trns
                  (EST.t-dual-preserves-≡c (Types.≡c-symm (Types.nf-sound+ S)))
                  (Types.≡c-symm (Types.dual-tinv (Types.nf Duality.⊕ Duality.d?⊥ S))))))))
        (sym
          (nfTyTy-fromNormalTy
            (Types.nf-normal-type
              Duality.⊕
              Duality.d?⊥
              (SessLin (Types.T-Dual Duality.D-S ⌞ normalizeTy S ⌟)))))))

newInst-shape :
  ∀ {S : Ty [] SLin}
  → normalizeTy (Ty.T-Pair (SessLin S) (SessLin (Types.T-Dual Duality.D-S S)))
    ≡ pairNf (normalizeTy (SessLin S)) (dualSessNf (normalizeTy S))
newInst-shape {S}
  with dualSess-normalizeTy {S = S}
... | eq =
  nfTyEq
    (cong₂ Ty.T-Pair refl (cong ⌞_⌟ eq))

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
  with linArrNf-injective eqRecv
... | eqA , eqR = refl , (eqA , eqR)

wkNfTy-normalizeTy-subst-raw-local :
  ∀ {K Kₚ} {P : Ty [] Kₚ} {U : Ty [] K}
  → ⌞ wkNfTy {K′ = K} (normalizeTy P) ⌟ ⋯ ⦅ ⌞ normalizeTy U ⌟ ⦆ₛ
      ≡
    ⌞ normalizeTy P ⌟
wkNfTy-normalizeTy-subst-raw-local {K} {Kₚ} {P} {U} =
  trans
    (cong
      (λ X → X ⋯ ⦅ ⌞ normalizeTy U ⌟ ⦆ₛ)
      (wkNFKind-sound {K = Kₚ} {K′ = K} (normalizeTy P)))
    (wk-cancels-⦅⦆-⋯ ⌞ normalizeTy P ⌟ ⌞ normalizeTy U ⌟)

wkNfTy-normalizeTy-substTy-local :
  ∀ {K pk m} {P : Ty [] (KV pk m)} {U : Ty [] K}
  → substNFTyWith
      (singleNFSub (normalizeTy U))
      (wkNfTy {K′ = K} (normalizeTy P))
      ≡
    normalizeTy P
wkNfTy-normalizeTy-substTy-local {K} {P = P} {U = U} = nfEq raw
  where
  σ : NFSub (K ∷ []) []
  σ = singleNFSub (normalizeTy U)

  raw :
    ⌞ substNFTyWith σ (wkNfTy {K′ = K} (normalizeTy P)) ⌟
      ≡
    ⌞ normalizeTy P ⌟
  raw =
    trans
      (substNFTy-sound σ (wkNfTy {K′ = K} (normalizeTy P)))
      (trans
        (cong
          (Types.nf Duality.⊕ Duality.d?⊥)
          (trans
            (⋯-cong
              ⌞ wkNfTy {K′ = K} (normalizeTy P) ⌟
              (singleNFSub-sound (normalizeTy U)))
            (wkNfTy-normalizeTy-subst-raw-local {K = K} {P = P} {U = U})))
        (Types.nf-idempotent (toNormalTy (normalizeTy P))))

send₁-body :
  ∀ {T : Ty [] TLin}
  → substNFTy
      (send1Nf (N-Var (NV-Var (here refl))))
      (normalizeTy T)
      ≡
    send1Nf (normalizeTy T)
send₁-body = refl

send₂-body :
  ∀ {T : Ty [] TLin} {S : Ty [] SLin}
  → substNFTy
      (sendNf (wkNfTy {K′ = SLin} (normalizeTy T)) (N-Var (NV-Var (here refl))))
      (normalizeTy S)
      ≡
    sendNf (normalizeTy T) (normalizeTy S)
send₂-body {T = T} {S = S}
  rewrite wkNfTy-normalizeTy-substTy-local {K = SLin} {P = T} {U = S} =
  refl

receive₁-body :
  ∀ {T : Ty [] TLin}
  → substNFTy
      (receive1Nf (N-Var (NV-Var (here refl))))
      (normalizeTy T)
      ≡
    receive1Nf (normalizeTy T)
receive₁-body = refl

receive₂-body :
  ∀ {T : Ty [] TLin} {S : Ty [] SLin}
  → substNFTy
      (receiveNf (wkNfTy {K′ = SLin} (normalizeTy T)) (N-Var (NV-Var (here refl))))
      (normalizeTy S)
      ≡
    receiveNf (normalizeTy T) (normalizeTy S)
receive₂-body {T = T} {S = S}
  rewrite wkNfTy-normalizeTy-substTy-local {K = SLin} {P = T} {U = S} =
  refl

wkNfTy-normalizeTyTLin-local :
  ∀ {K} {T : Ty [] TLin}
  → wkNfTy {K′ = K} (normalizeTy T) ≡ normalizeTy (T ⋯ weakenᵣ K)
wkNfTy-normalizeTyTLin-local {K} {T} =
  trans
    (sym (normalizeTy-id (wkNfTy {K′ = K} (normalizeTy T))))
    (nfEq eqRaw)
  where
  eqcNorm : ⌞ normalizeTy T ⌟ Types.≡c T
  eqcNorm =
    Types.≡c-trns
      (Types.≡c-refl-eq (nfTyTy-fromNormalTy (Types.nf-normal-type Duality.⊕ Duality.d?⊥ T)))
      (Types.nf-sound+ T)

  eqcWk : ⌞ wkNfTy {K′ = K} (normalizeTy T) ⌟ Types.≡c (T ⋯ weakenᵣ K)
  eqcWk =
    subst
      (λ X → X Types.≡c (T ⋯ weakenᵣ K))
      (sym (wkNFKind-sound {K = TLin} {K′ = K} (normalizeTy T)))
      (subst-preserves-≡c eqcNorm (weakenᵣ K))

  eqRaw :
    ⌞ normalizeTy ⌞ wkNfTy {K′ = K} (normalizeTy T) ⌟ ⌟
      ≡
    ⌞ normalizeTy (T ⋯ weakenᵣ K) ⌟
  eqRaw =
    trans
      (nfTyTy-fromNormalTy (Types.nf-normal-type Duality.⊕ Duality.d?⊥ ⌞ wkNfTy {K′ = K} (normalizeTy T) ⌟))
      (trans
        (Types.nf-complete Duality.d?⊥ Duality.d?⊥ eqcWk)
        (sym (nfTyTy-fromNormalTy (Types.nf-normal-type Duality.⊕ Duality.d?⊥ (T ⋯ weakenᵣ K)))))

sessionNfEq-local :
  ∀ {S : Ty [] SLin}
  → Types.nf
      Duality.⊕
      (λ x → Duality.dualizable-sub (Duality.d?⊥ x) (≤k-step (≤p-step <p-st) ≤m-refl))
      S
    ≡ ⌞ normalizeTy S ⌟
sessionNfEq-local {S} =
  trans
    (Types.nf-⊕-ignores
      {T = S}
      (λ x → Duality.dualizable-sub (Duality.d?⊥ x) (≤k-step (≤p-step <p-st) ≤m-refl))
      Duality.d?⊥)
    (sym (nfTyTy-fromNormalTy (Types.nf-normal-type Duality.⊕ Duality.d?⊥ S)))

sendTy2-shape-local :
  ∀ {T : Ty [] TLin} {S : Ty [] SLin}
  → normalizeTy (SendTy T S) ≡ sendNf (normalizeTy T) (normalizeTy S)
sendTy2-shape-local {T} {S} =
  nfTyEq
    (cong₂ (Ty.T-Arrow (≤p-step <p-mt))
      (cong₂ Ty.T-Pair
        refl
        (cong (Ty.T-Sub (≤k-step (≤p-step <p-st) ≤m-refl))
          (cong₂ (Ty.T-Msg Duality.⊕)
            refl
            (trans
              (nfTyTy-fromNormalTy
                (Types.nf-normal-type
                  Duality.⊕
                  (λ x → Duality.dualizable-sub (Duality.d?⊥ x) (≤k-step (≤p-step <p-st) ≤m-refl))
                  S))
              (sessionNfEq-local {S = S})))))
      (cong (Ty.T-Sub (≤k-step (≤p-step <p-st) ≤m-refl))
        (trans
          (nfTyTy-fromNormalTy
            (Types.nf-normal-type
              Duality.⊕
              (λ x → Duality.dualizable-sub (Duality.d?⊥ x) (≤k-step (≤p-step <p-st) ≤m-refl))
              S))
          (sessionNfEq-local {S = S}))))

send₁-shapeNF-local :
  ∀ {T : Ty [] TLin}
  → send1Nf (normalizeTy T) ≡ normalizeTy (SendTy1 T)
send₁-shapeNF-local {T = T}
  rewrite wkNfTy-normalizeTyTLin-local {K = SLin} {T = T} =
  refl

send₁-rigid :
  ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {T : NfTy [] TLin}
  → Γ ⊢ E-TApp (E-Val (V-Const C-Send)) U ⇒ T ⊣ Γ′
  → Γ ≡ Γ′
send₁-rigid (T-TApp (T-Val (TV-Const CT-Send))) = refl

send₂-rigid :
  ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {S : Ty [] SLin} {T : NfTy [] TLin}
  → Γ ⊢ E-TApp (E-Val (V-Send₁ U)) S ⇒ T ⊣ Γ′
  → Γ ≡ Γ′
send₂-rigid (T-TApp (T-Val TV-Send₁)) = refl

send₁-ty :
  ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {T : NfTy [] TLin}
  → Γ ⊢ E-TApp (E-Val (V-Const C-Send)) U ⇒ T ⊣ Γ′
  → T ≡ normalizeTy (SendTy1 U)
send₁-ty {U = U} (T-TApp (T-Val (TV-Const CT-Send))) =
  trans (send₁-body {T = U}) (send₁-shapeNF-local {T = U})

send₂-ty :
  ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {S : Ty [] SLin} {T : NfTy [] TLin}
  → Γ ⊢ E-TApp (E-Val (V-Send₁ U)) S ⇒ T ⊣ Γ′
  → T ≡ normalizeTy (SendTy U S)
send₂-ty {U = U} {S = S} (T-TApp (T-Val TV-Send₁)) =
  trans (send₂-body {T = U} {S = S}) (sym (sendTy2-shape-local {T = U} {S = S}))

send₁-shapeNF :
  ∀ {T : Ty [] TLin}
  → send1Nf (normalizeTy T) ≡ normalizeTy (SendTy1 T)
send₁-shapeNF {T = T} =
  trans
    (sym (send₁-body {T = T}))
    (send₁-ty {Γ = ∅} {Γ′ = ∅} {U = T}
      (T-TApp (T-Val (TV-Const CT-Send))))

send₂-shapeNF :
  ∀ {T : Ty [] TLin} {S : Ty [] SLin}
  → sendNf (normalizeTy T) (normalizeTy S) ≡ normalizeTy (SendTy T S)
send₂-shapeNF {T = T} {S = S} =
  trans
    (sym (send₂-body {T = T} {S = S}))
    (send₂-ty {Γ = ∅} {Γ′ = ∅} {U = T} {S = S}
      (T-TApp (T-Val TV-Send₁)))

send₂-shape :
  ∀ {n}
    {Γ₁ Γ₂ : Ctx [] n}
    {Tᵣ : Ty [] TLin} {Sᵣ : Ty [] SLin}
    {A R : NfTy [] TLin}
  → Γ₁ ⊢ᵥ V-Send₂ Tᵣ Sᵣ ⇒ linArrNf A R ⊣ Γ₂
  → (Γ₁ ≡ Γ₂)
    × ((A ≡ pairNf (normalizeTy Tᵣ) (sendChanNf (normalizeTy Tᵣ) (normalizeTy Sᵣ)))
    × (R ≡ sessNf (normalizeTy Sᵣ)))
send₂-shape TV-Send₂ = refl , (refl , refl)

postulate
  receive₁-rigid :
    ∀ {n} {Γ Γ′ : Ctx [] n} {U : Ty [] TLin} {T : NfTy [] TLin}
    → Γ ⊢ E-TApp (E-Val (V-Const C-Receive)) U ⇒ T ⊣ Γ′
    → Γ ≡ Γ′

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

receive₁-shapeNF :
  ∀ {T : Ty [] TLin}
  → receive1Nf (normalizeTy T) ≡ normalizeTy (ReceiveTy1 T)
receive₁-shapeNF {T = T} =
  trans
    (sym (receive₁-body {T = T}))
    (receive₁-ty {Γ = ∅} {Γ′ = ∅} {U = T}
      (T-TApp (T-Val (TV-Const CT-Receive))))

receive₂-shapeNF :
  ∀ {T : Ty [] TLin} {S : Ty [] SLin}
  → receiveNf (normalizeTy T) (normalizeTy S) ≡ normalizeTy (ReceiveTy T S)
receive₂-shapeNF {T = T} {S = S} =
  trans
    (sym (receive₂-body {T = T} {S = S}))
    (receive₂-ty {Γ = ∅} {Γ′ = ∅} {U = T} {S = S}
      (T-TApp (T-Val TV-Receive₁)))

postulate
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

select₂-inversion :
  ∀ {n k}
    {Γ Γ′ : Ctx [] n}
    {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin}
    {W : NfTy [] TLin}
  → Γ ⊢ᵥ V-Select₂ v i P S ⇒ W ⊣ Γ′
  → (Γ ≡ Γ′)
    × (W ≡ linArrNf
             (selectInNf v i (normalizeTy P) (normalizeTy S))
             (selectOutNf v i (normalizeTy P) (normalizeTy S)))
select₂-inversion TV-Select₂ = refl , refl

select₂-shape :
  ∀ {n k}
    {Γ Γ′ : Ctx [] n}
    {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin}
    {A R : NfTy [] TLin}
  → Γ ⊢ᵥ V-Select₂ v i P S ⇒ linArrNf A R ⊣ Γ′
  → Γ ≡ Γ′
    × (A ≡ selectInNf v i (normalizeTy P) (normalizeTy S))
    × (R ≡ selectOutNf v i (normalizeTy P) (normalizeTy S))
select₂-shape {v = v} {i = i} {P = P} {S = S} vr
  with select₂-inversion vr
... | refl , eqSelect
  with linArrNf-injective eqSelect
... | eqA , eqR = refl , eqA , eqR

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
