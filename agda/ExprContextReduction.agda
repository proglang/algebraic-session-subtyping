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
open import ExprContextProperties public
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

-- Pointwise replacement in a full context.
data ReplaceAt {Δ} : ∀ {n} → Ctx Δ n → Fin n → Binding Δ → Ctx Δ n → Set where
  R-here : ∀ {n} {Γ : Ctx Δ n} {b b′ : Binding Δ}
    → ReplaceAt (b ▻ Γ) zero b′ (b′ ▻ Γ)

  R-there : ∀ {n} {Γ Γ′ : Ctx Δ n} {x : Fin n} {b b′ : Binding Δ}
    → ReplaceAt Γ x b′ Γ′
    → ReplaceAt (b ▻ Γ) (suc x) b′ (b ▻ Γ′)

replace-at : ∀ {n}{Δ} → (Γ : Ctx Δ n) → (x : Fin n) → (b : Binding Δ) → Σ (Ctx Δ n) λ Γ′ → ReplaceAt Γ x b Γ′
replace-at (_ ▻ Γ) zero b = (b ▻ Γ) , R-here
replace-at (_ ▻ Γ) (suc x) b
  with replace-at Γ x b
... | Γ′ , rm = _ ▻ Γ′ , R-there rm

postulate
  used-head-eq :
    ∀ {Δ n pk₁ pk₂}
      {T₁ : NfTy Δ (KV pk₁ Lin)}
      {T₂ : NfTy Δ (KV pk₂ Lin)}
      {Γ : Ctx Δ n}
    → (B-Used T₁ ▻ Γ) ≡ (B-Used T₂ ▻ Γ)

replace-frames-disjoint :
  ∀ {Δ n pk}
    {Γ₀ Γ₁ Γf Γf′ : Ctx Δ n}
    {x : Fin n} {U : NfTy Δ (KV pk Lin)}
  → LinearDisjoint Γ₀ Γf
  → ReplaceAt Γ₀ x (B-Lin U) Γ₁
  → ReplaceAt Γf x (B-Used U) Γf′
  → LinearDisjoint Γ₁ Γf′
replace-frames-disjoint (LD-used-used ld0f) R-here R-here = LD-live-used ld0f
replace-frames-disjoint (LD-used-used ld0f) (R-there replin) (R-there repused) = LD-used-used (replace-frames-disjoint ld0f replin repused)
replace-frames-disjoint (LD-used-live ld0f) R-here R-here = LD-live-used ld0f
replace-frames-disjoint (LD-used-live ld0f) (R-there replin) (R-there repused) = LD-used-live (replace-frames-disjoint ld0f replin repused)
replace-frames-disjoint (LD-live-used ld0f) R-here R-here = LD-live-used ld0f
replace-frames-disjoint (LD-live-used ld0f) (R-there replin) (R-there repused) = LD-live-used (replace-frames-disjoint ld0f replin repused)
replace-frames-disjoint (LD-un-un ld0f) R-here R-here = LD-live-used ld0f
replace-frames-disjoint (LD-un-un ld0f) (R-there replin) (R-there repused) = LD-un-un (replace-frames-disjoint ld0f replin repused)

replace-frames-used :
  ∀ {Δ n pk}
    {Γ₀ Γ₁ Γf Γf′ : Ctx Δ n}
    {x : Fin n} {U : NfTy Δ (KV pk Lin)}
  → LinearDisjoint Γ₀ Γf
  → ReplaceAt Γ₀ x (B-Used U) Γ₁
  → ReplaceAt Γf x (B-Used U) Γf′
  → LinearDisjoint Γ₁ Γf′
replace-frames-used (LD-used-used ld0f) R-here R-here = LD-used-used ld0f
replace-frames-used (LD-used-used ld0f) (R-there rep0) (R-there repf) = LD-used-used (replace-frames-used ld0f rep0 repf)
replace-frames-used (LD-used-live ld0f) R-here R-here = LD-used-used ld0f
replace-frames-used (LD-used-live ld0f) (R-there rep0) (R-there repf) = LD-used-live (replace-frames-used ld0f rep0 repf)
replace-frames-used (LD-live-used ld0f) R-here R-here = LD-used-used ld0f
replace-frames-used (LD-live-used ld0f) (R-there rep0) (R-there repf) = LD-live-used (replace-frames-used ld0f rep0 repf)
replace-frames-used (LD-un-un ld0f) R-here R-here = LD-used-used ld0f
replace-frames-used (LD-un-un ld0f) (R-there rep0) (R-there repf) = LD-un-un (replace-frames-used ld0f rep0 repf)


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

unitLinNf : NfTy [] TLin
unitLinNf = unitConstNf

recvChanNf : NfTy [] TLin → NfTy [] SLin → NfTy [] SLin
recvChanNf T S = msgNF ⊝ (N-Normal (N-Up T)) S

sendChanNf : NfTy [] TLin → NfTy [] SLin → NfTy [] SLin
sendChanNf T S = msgNF ⊕ (N-Normal (N-Up T)) S

dualSessNf : NfTy [] SLin → NfTy [] TLin
dualSessNf S = normalizeTy (SessLin (T-Dual D-S ⌞ S ⌟))

selectInNf : ∀ {k} → Variance → Fin k → NfTy [] KP → NfTy [] SLin → NfTy [] TLin
selectInNf = selectInTyNf

selectOutNf : ∀ {k} → Variance → Fin k → NfTy [] KP → NfTy [] SLin → NfTy [] TLin
selectOutNf = selectOutTyNf

infix 4 _—ctx[_]→_

data _—ctx[_]→_ : ∀ {n Θ} → Ctx [] n → Label n Θ → Ctx [] (length Θ + n) → Set where
  Ctx-β : ∀ {n} {Γ : Ctx [] n}
    → Γ —ctx[ L-β ]→ Γ

  Ctx-New : ∀ {n} {Γ₀ : Ctx [] n} {S : Ty [] SLin}
    → Γ₀ —ctx[ L-New S ]→ (B-Lin (normalizeTy S) ▻ (B-Lin (normalizeTy (T-Dual D-S S)) ▻ Γ₀))

  Ctx-Fork : ∀ {n} {Γ₀ Γv Γv′ Γ₁ : Ctx [] n} {v : Value [] n}
    → RemoveCtx Γ₀ Γv Γ₁
    → Γv ⊢ E-Val v ⇐ linArrNf unitLinNf unitLinNf ⊣ Γv′
    → AllUsed Γv′
    → Γ₀ —ctx[ L-Fork v ]→ Γ₁

  Ctx-Rcv : ∀ {n} {Γ₀ Γv-in Γv-used Γv-out Γx Γ₁ : Ctx [] n}
      {x : Fin n} {T : NfTy [] TLin} {S : NfTy [] SLin} {v : Value [] n}
    → Γv-in ⊢ᵥ v ⇒ T ⊣ Γv-used
    → AllUsed Γv-used
    → LinearDisjoint Γ₀ Γv-in
    → Γ₀ ∋ˡ x ∶ recvChanNf T S
    → ReplaceAt Γ₀ x (B-Lin S) Γx
    → ReplaceAt Γv-in x (B-Used S) Γv-out
    → FrameCtx Γx Γv-out Γ₁
    → Γ₀ —ctx[ L-RecvVal x v ]→ Γ₁

  Ctx-Send : ∀ {n} {Γ₀ Γx Γv Γv′ Γ₁ : Ctx [] n}
      {x : Fin n} {T : NfTy [] TLin} {S : NfTy [] SLin} {v : Value [] n}
    → RemoveCtx Γ₀ Γv Γx
    → Γv ⊢ᵥ v ⇒ T ⊣ Γv′
    → AllUsed Γv′
    → Γx ∋ˡ x ∶ sendChanNf T S
    → ReplaceAt Γx x (B-Lin (sessTyNf S)) Γ₁
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

infix 4 _—frm[_]→_

data _—frm[_]→_ : ∀ {n Θ} → Ctx [] n → Label n Θ → Ctx [] (length Θ + n) → Set where
  Frm-β : ∀ {n} {Γ : Ctx [] n}
    → Γ —frm[ L-β ]→ Γ

  Frm-New : ∀ {n} {Γ : Ctx [] n} {S : Ty [] SLin}
    → Γ —frm[ L-New S ]→
        (B-Used (normalizeTy S) ▻
         (B-Used (normalizeTy (T-Dual D-S S)) ▻ Γ))

  Frm-Fork : ∀ {n} {Γ : Ctx [] n} {v : Value [] n}
    → Γ —frm[ L-Fork v ]→ Γ

  Frm-Rcv : ∀ {n} {Γ₀ Γ₁ : Ctx [] n}
      {x : Fin n} {S : NfTy [] SLin} {v : Value [] n}
    → ReplaceAt Γ₀ x (B-Used S) Γ₁
    → Γ₀ —frm[ L-RecvVal x v ]→ Γ₁

  Frm-Send : ∀ {n} {Γ₀ Γ₁ : Ctx [] n}
      {x : Fin n} {S : NfTy [] SLin} {v : Value [] n}
    → ReplaceAt Γ₀ x (B-Used (sessTyNf S)) Γ₁
    → Γ₀ —frm[ L-SendVal x v ]→ Γ₁

  Frm-Close : ∀ {n} {Γ₀ Γ₁ : Ctx [] n} {x : Fin n}
    → ReplaceAt Γ₀ x (B-Used (normalizeTy EndLin)) Γ₁
    → Γ₀ —frm[ L-Close x ]→ Γ₁

  Frm-Match : ∀ {n k}
      {ssout : Subset.Subset (suc k)}
      {Γ₀ Γ₁ : Ctx [] n} {x : Fin n} {i : Fin (suc k)}
      {v : Variance} {P : NfTy [] KP} {S : NfTy [] SLin}
    → (i∈ : i Subset.∈ ssout)
    → ReplaceAt Γ₀ x (B-Used (MatchBranchOutput ssout v P S i i∈)) Γ₁
    → Γ₀ —frm[ L-RecvLab x i ]→ Γ₁

  Frm-Select : ∀ {n k} {Γ₀ Γ₁ : Ctx [] n} {x : Fin n} {i : Fin k}
      {v : Variance} {P : NfTy [] KP} {S : NfTy [] SLin}
    → ReplaceAt Γ₀ x (B-Used (selectOutNf v i P S)) Γ₁
    → Γ₀ —frm[ L-SendLab x i ]→ Γ₁

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
extendUsed (S ∷ Θ) Γ = B-Used (normalizeTy S) ▻ extendUsed Θ Γ

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

{-
frm-to-frame-update :
  ∀ {n Θ}
    {Γ : Ctx [] n} {Γ′ : Ctx [] (length Θ + n)}
    {ℓ : Label n Θ}
  → Γ —frm[ ℓ ]→ Γ′
  → FrameUpdate ℓ Γ Γ′
frm-to-frame-update Frm-β = FU-β
frm-to-frame-update Frm-New = {!!}
frm-to-frame-update Frm-Fork = FU-Fork
frm-to-frame-update (Frm-Rcv _) = FU-RecvVal
frm-to-frame-update (Frm-Send _) = FU-SendVal
frm-to-frame-update Frm-Close = FU-Close
frm-to-frame-update (Frm-Match _ _) = FU-RecvLab
frm-to-frame-update (Frm-Select _) = FU-SendLab
-}

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
    ∀ {n} {Γ₀ Γv Γv-out Γv′ Γx Γ₁ Γin Γin′ : Ctx [] n}
      {x : Fin n} {T : NfTy [] TLin} {S : NfTy [] SLin} {v : Value [] n}
      {ld : LinearDisjoint Γ₀ Γv}
      {x∈ : Γ₀ ∋ˡ x ∶ recvChanNf T S}
      {rep : ReplaceAt Γ₀ x (B-Lin S) Γx}
      {repused : ReplaceAt Γv x (B-Used S) Γv-out}
      {merge : FrameCtx Γx Γv-out Γ₁}
      {take : Γin ⊢ˡ x ∶ recvChanNf T S ⊣ Γin′}
      {auin : AllUsed Γin′}
      {dv : Γv ⊢ᵥ v ⇒ T ⊣ Γv′}
      {au : AllUsed Γv′}
    → Compatible {Γ₀ = Γ₀} {Γ₁ = Γ₁} {ℓ = L-RecvVal x v}
        (Ctx-Rcv dv au ld x∈ rep repused merge) (Label-RecvVal take auin dv au)

  Compat-SendVal :
    ∀ {n} {Γ₀ Γin Γx Γv Γv′ Γ₁ : Ctx [] n}
      {x : Fin n} {T : NfTy [] TLin} {S : NfTy [] SLin} {v : Value [] n}
      {rm : RemoveCtx Γ₀ Γv Γx}
      {dv : Γv ⊢ᵥ v ⇒ T ⊣ Γv′}
      {auv : AllUsed Γv′}
      {x∈ : Γx ∋ˡ x ∶ sendChanNf T S}
      {rep : ReplaceAt Γx x (B-Lin (sessTyNf S)) Γ₁}
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
        Γf —frm[ ℓ ]→ Γf′ × LinearDisjoint Γ₁ Γf′
ctx-step-preserves-disjoint {Γf = Γf} Ctx-β (Label-β x x₁) (Compat-β x₂) ld0 ldv =
  Γf , Frm-β , ld0
ctx-step-preserves-disjoint {Γf = Γf} Ctx-New (Label-New {S = S} au-in au-v) (Compat-New x₂) ld0 ldv =
  ((B-Used (normalizeTy S)) ▻ (B-Used (normalizeTy (T-Dual D-S S)) ▻ Γf)) , Frm-New , LD-live-used (LD-live-used ld0)
ctx-step-preserves-disjoint {Γf = Γf} (Ctx-Fork rmv ⊢v au-v′) (Label-Fork au-in au-v) (Compat-Fork x) ld0 ldv =
  Γf , Frm-Fork , (remove-preserves-disjoint rmv ld0)
ctx-step-preserves-disjoint {Γf = Γf} (Ctx-Rcv {x = x} {S = S} ⊢v au-vrest ld0v1 x∈ replin rep-v mcxv) (Label-RecvVal ⊢x au-in ⊢v' au-v'rest) Compat-RecvVal ld0 ldv
  with replace-at Γf x (B-Used S)
... | Γf′ , repused
  with replace-frames-disjoint ld0 replin repused
... | ldxf
  with replace-frames-used ldv rep-v repused
... | ld-vout-f' =
  Γf′ , Frm-Rcv repused ,  merge-preserves-disjoint mcxv ldxf ld-vout-f'
ctx-step-preserves-disjoint {Γf = Γf} (Ctx-Send {x = x} {S = S} remv ⊢v au-vrest x∈ rep-x) (Label-SendVal ⊢x ⊢v' au-v'rest) Compat-SendVal ld0 ldv
  with replace-at Γf x (B-Used (sessTyNf S))
... | Γf′ , repused
  with remove-preserves-disjoint remv ld0
... | ldxf = Γf′ , (Frm-Send repused) , replace-frames-disjoint ldxf rep-x repused
ctx-step-preserves-disjoint {Γf = Γf} (Ctx-Close {Γ₁ = Γ₁} {x = x} x∈ repused) (Label-Close au-in au-v) (Compat-Close refl) ld0 ldv
  with replace-at Γf x (B-Used (normalizeTy EndLin))
... | Γf′ , repframe  = Γf′ , Frm-Close repframe , replace-frames-used ld0 repused repframe
ctx-step-preserves-disjoint {Γf = Γf} (Ctx-Match {ssout = ssout} {x = x} {v = v} {P} {S} i∈ x∈ replin) (Label-RecvLab au-in au-v) (Compat-Match refl) ld0 ldv
  with replace-at Γf x (B-Used (MatchBranchOutput ssout v P S _ i∈))
... | Γf′ , repframe = Γf′ , Frm-Match i∈ repframe , replace-frames-disjoint ld0 replin repframe
ctx-step-preserves-disjoint {Γf = Γf} (Ctx-Select {x = x} {i} {v = v} {P} {S} x∈ rep-lin) (Label-SendLab ⊢x au-v) Compat-Select ld0 ldv
  with replace-at Γf x (B-Used (selectOutNf v i P S))
... | Γf′ , repframe = Γf′ , Frm-Select repframe , replace-frames-disjoint ld0 rep-lin repframe
