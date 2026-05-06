module ExprPreservationStep2.Properties where

open import Data.Fin using (Fin; zero)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just)
open import Data.Nat using (suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)

import Duality
open import Kinds
open import Variance using (Variance)
import Types
open import Types using (Ty)
open import NormalTypes using (N-Arrow)
open import ExprSyntax using (Expr; Value; Const; E-Val; E-LetPair; E-Match)
import ExprSemantics as ES
open import ExprSemantics using (Label)
open import ExprNormalTyping
open import AlgorithmicNFSubtyping using (_<:ₜ_; <:ₜ-sub; <:ₜ-refl)
import AlgorithmicNFSound as NFSound
import ExprContextReduction as ECR
open import ExprContextReduction using
  ( _—frm[_]→_
  ; ReplaceAt
  ; RemoveCtx
  ; FrameCtx
  ; AllUsed
  ; LinearDisjoint
  ; allUsedCtx
  ; extendUsed
  ; recvChanNf
  ; sendChanNf
  ; dualSessNf
  ; Frm-New
  )
open import ExprTypingProperties using (FrameCtx; frame-unique; replay-value-allUsed)
import ExprTypingStrengthening as ETS
import ExprSubstitutionPreservation as ESP
import ExprSubstitutionTyping as EST

take-implies-membership :
  ∀ {Δ n pk} {Γ Γ′ : Ctx Δ n} {x : Fin n} {T : NfTy Δ (KV pk Lin)}
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
  → Γ ∋ˡ x ∶ T
take-implies-membership take-here = hereˡ
take-implies-membership (take-thereˡ take) = thereˡˡ (take-implies-membership take)
take-implies-membership (take-thereᵘ take) = thereˡᵘ (take-implies-membership take)
take-implies-membership (take-there✖ take) = thereˡ✖ (take-implies-membership take)

replace-used-output :
  ∀ {n pk}
    {Γ₀ Γ₁ Γ₂ : Ctx [] n}
    {x : Fin n} {T : NfTy [] (KV pk Lin)}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₂
  → ReplaceAt Γ₀ x (B-Used T) Γ₁
  → Γ₁ ≡ Γ₂
replace-used-output take-here ECR.R-here = refl
replace-used-output (take-thereˡ take) (ECR.R-there rep)
  rewrite replace-used-output take rep = refl
replace-used-output (take-thereᵘ take) (ECR.R-there rep)
  rewrite replace-used-output take rep = refl
replace-used-output (take-there✖ take) (ECR.R-there rep)
  rewrite replace-used-output take rep = refl

take-from-membership :
  ∀ {n pk}
    {Γ : Ctx [] n}
    {x : Fin n} {T : NfTy [] (KV pk Lin)}
  → Γ ∋ˡ x ∶ T
  → Σ (Ctx [] n) λ Γ′ → Γ ⊢ˡ x ∶ T ⊣ Γ′
take-from-membership hereˡ = _ , take-here
take-from-membership (thereˡˡ x∈)
  with take-from-membership x∈
... | Γ′ , take = _ , take-thereˡ take
take-from-membership (thereˡᵘ x∈)
  with take-from-membership x∈
... | Γ′ , take = _ , take-thereᵘ take
take-from-membership (thereˡ✖ x∈)
  with take-from-membership x∈
... | Γ′ , take = _ , take-there✖ take

take-unique :
  ∀ {Δ n pk}
    {Γ : Ctx Δ n}
    {x : Fin n} {T U : NfTy Δ (KV pk Lin)}
    {Γ₁ Γ₂ : Ctx Δ n}
  → Γ ⊢ˡ x ∶ T ⊣ Γ₁
  → Γ ⊢ˡ x ∶ U ⊣ Γ₂
  → (T ≡ U) × (Γ₁ ≡ Γ₂)
take-unique take-here take-here = refl , refl
take-unique (take-thereˡ {U = U} take₁) (take-thereˡ take₂)
  with take-unique take₁ take₂
... | eqT , eqΓ = eqT , cong (λ Γ → B-Lin U ▻ Γ) eqΓ
take-unique (take-thereᵘ {U = U} take₁) (take-thereᵘ take₂)
  with take-unique take₁ take₂
... | eqT , eqΓ = eqT , cong (λ Γ → B-Un U ▻ Γ) eqΓ
take-unique (take-there✖ {U = U} take₁) (take-there✖ take₂)
  with take-unique take₁ take₂
... | eqT , eqΓ = eqT , cong (λ Γ → B-Used U ▻ Γ) eqΓ

take-output-unique :
  ∀ {Δ n pk₁ pk₂}
    {Γ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk₁ Lin)}
    {U : NfTy Δ (KV pk₂ Lin)}
    {Γ₁ Γ₂ : Ctx Δ n}
  → Γ ⊢ˡ x ∶ T ⊣ Γ₁
  → Γ ⊢ˡ x ∶ U ⊣ Γ₂
  → Γ₁ ≡ Γ₂
take-output-unique take-here take-here = refl
take-output-unique (take-thereˡ take₁) (take-thereˡ take₂)
  rewrite take-output-unique take₁ take₂ = refl
take-output-unique (take-thereᵘ take₁) (take-thereᵘ take₂)
  rewrite take-output-unique take₁ take₂ = refl
take-output-unique (take-there✖ take₁) (take-there✖ take₂)
  rewrite take-output-unique take₁ take₂ = refl

take-kind-unique :
  ∀ {Δ n pk₁ pk₂}
    {Γ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk₁ Lin)}
    {U : NfTy Δ (KV pk₂ Lin)}
    {Γ₁ Γ₂ : Ctx Δ n}
  → Γ ⊢ˡ x ∶ T ⊣ Γ₁
  → Γ ⊢ˡ x ∶ U ⊣ Γ₂
  → pk₁ ≡ pk₂
take-kind-unique take-here take-here = refl
take-kind-unique (take-thereˡ take₁) (take-thereˡ take₂) =
  take-kind-unique take₁ take₂
take-kind-unique (take-thereᵘ take₁) (take-thereᵘ take₂) =
  take-kind-unique take₁ take₂
take-kind-unique (take-there✖ take₁) (take-there✖ take₂) =
  take-kind-unique take₁ take₂

lin-un-disjoint :
  ∀ {Δ n pk₁ pk₂}
    {Γ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk₁ Lin)}
    {U : NfTy Δ (KV pk₂ Un)}
  → Γ ∋ˡ x ∶ T
  → Γ ∋ᵘ x ∶ U
  → ⊥
lin-un-disjoint hereˡ ()
lin-un-disjoint (thereˡˡ x∈) (thereᵘˡ x∈′) = lin-un-disjoint x∈ x∈′
lin-un-disjoint (thereˡᵘ x∈) (thereᵘᵘ x∈′) = lin-un-disjoint x∈ x∈′
lin-un-disjoint (thereˡ✖ x∈) (thereᵘ✖ x∈′) = lin-un-disjoint x∈ x∈′

sess-subtype :
  ∀ {S₁ S₂ : NfTy [] SLin}
  → normalTyOf S₁ <:ₜ normalTyOf S₂
  → normalTyOf (sessTyNf S₁) <:ₜ normalTyOf (sessTyNf S₂)
sess-subtype sub = <:ₜ-sub sub

arrow-subtype-inversion :
  ∀ {m pk₁ m₁ pk₂ m₂}
    {A : NfTy [] (KV pk₁ m₁)}
    {V : NfTy [] (KV pk₂ m₂)}
    {U : NfTy [] (KV KT m)}
  → normalTyOf U <:ₜ normalTyOf (N-Arrow {m = m} A V)
  → Σ (NfTy [] (KV pk₁ m₁)) λ A′ →
      Σ (NfTy [] (KV pk₂ m₂)) λ V′ →
        (U ≡ N-Arrow {m = m} A′ V′)
        × (normalTyOf A <:ₜ normalTyOf A′)
        × (normalTyOf V′ <:ₜ normalTyOf V)
arrow-subtype-inversion = ETS.arrow-subtype-inversion

substTy-wkCtx-id :
  ∀ {K n} (Γ : Ctx [] n) (U : Ty [] K) → EST.substTyCtx (wkCtx Γ) U ≡ Γ
substTy-wkCtx-id = ESP.substTy-wkCtx-id

frm-new-extendUsed :
  ∀ {n}
    {Γ : Ctx [] n}
    {S : Ty [] SLin}
  → allUsedCtx Γ —frm[ ES.L-New S ]→
      extendUsed (S ∷ Types.T-Dual Duality.D-S S ∷ []) (allUsedCtx Γ)
frm-new-extendUsed = Frm-New

remove-frame :
  ∀ {n}
    {Γ₀ Γv Γx : Ctx [] n}
  → RemoveCtx Γ₀ Γv Γx
  → FrameCtx Γx Γv Γ₀
remove-frame ECR.RM-∅ = ECR.FC-∅
remove-frame (ECR.RM-drop rm) = ECR.FC-frame (remove-frame rm)
remove-frame (ECR.RM-allused rm) = ECR.FC-allused (remove-frame rm)
remove-frame (ECR.RM-lin rm) = ECR.FC-live (remove-frame rm)
remove-frame (ECR.RM-un rm) = ECR.FC-un (remove-frame rm)

frame-replace-used :
  ∀ {Δ n pk₁ pk₂}
    {Γa Γb Γab : Ctx Δ n}
    {Γa′ Γb′ Γab′ : Ctx Δ n}
    {x : Fin n}
    {U₁ : NfTy Δ (KV pk₁ Lin)}
    {U₂ : NfTy Δ (KV pk₂ Lin)}
  → FrameCtx Γa Γb Γab
  → ReplaceAt Γa x (B-Used U₁) Γa′
  → ReplaceAt Γb x (B-Used U₂) Γb′
  → FrameCtx Γa′ Γb′ Γab′
  → ReplaceAt Γab x (B-Used U₁) Γab′
frame-replace-used (ECR.FC-allused f) ECR.R-here ECR.R-here (ECR.FC-allused f′)
  rewrite frame-unique f f′ = ECR.R-here
frame-replace-used (ECR.FC-allused f) (ECR.R-there repa) (ECR.R-there repb) (ECR.FC-allused f′) =
  ECR.R-there (frame-replace-used f repa repb f′)
frame-replace-used (ECR.FC-live f) ECR.R-here ECR.R-here (ECR.FC-allused f′)
  rewrite frame-unique f f′ = ECR.R-here
frame-replace-used (ECR.FC-live f) (ECR.R-there repa) (ECR.R-there repb) (ECR.FC-live f′) =
  ECR.R-there (frame-replace-used f repa repb f′)
frame-replace-used (ECR.FC-frame f) ECR.R-here ECR.R-here (ECR.FC-allused f′)
  rewrite frame-unique f f′ = ECR.R-here
frame-replace-used (ECR.FC-frame f) (ECR.R-there repa) (ECR.R-there repb) (ECR.FC-frame f′) =
  ECR.R-there (frame-replace-used f repa repb f′)
frame-replace-used (ECR.FC-un f) ECR.R-here ECR.R-here (ECR.FC-allused f′)
  rewrite frame-unique f f′ = ECR.R-here
frame-replace-used (ECR.FC-un f) (ECR.R-there repa) (ECR.R-there repb) (ECR.FC-un f′) =
  ECR.R-there (frame-replace-used f repa repb f′)

frame-update-merge :
  ∀ {n Θ}
    {ℓ : Label n Θ}
    {Γa Γb Γab : Ctx [] n}
    {Γa′ Γb′ Γab′ : Ctx [] (length Θ + n)}
  → FrameCtx Γa Γb Γab
  → Γa —frm[ ℓ ]→ Γa′
  → Γb —frm[ ℓ ]→ Γb′
  → FrameCtx Γa′ Γb′ Γab′
  → Γab —frm[ ℓ ]→ Γab′
frame-update-merge f ECR.Frm-β ECR.Frm-β f′
  rewrite frame-unique f f′ = ECR.Frm-β
frame-update-merge {ℓ = ES.L-New S} {Γab = Γab} f ECR.Frm-New ECR.Frm-New f′ =
  subst
    (λ Γout → Γab —frm[ ES.L-New S ]→ Γout)
    (frame-unique (ECR.FC-allused (ECR.FC-allused f)) f′)
    ECR.Frm-New
frame-update-merge f ECR.Frm-Fork ECR.Frm-Fork f′
  rewrite frame-unique f f′ = ECR.Frm-Fork
frame-update-merge f (ECR.Frm-Rcv repa) (ECR.Frm-Rcv repb) f′ =
  ECR.Frm-Rcv (frame-replace-used f repa repb f′)
frame-update-merge f (ECR.Frm-Send repa) (ECR.Frm-Send repb) f′ =
  ECR.Frm-Send (frame-replace-used f repa repb f′)
frame-update-merge f (ECR.Frm-Close repa) (ECR.Frm-Close repb) f′ =
  ECR.Frm-Close (frame-replace-used f repa repb f′)
frame-update-merge f (ECR.Frm-Match i∈a repa) (ECR.Frm-Match i∈b repb) f′ =
  ECR.Frm-Match i∈a (frame-replace-used f repa repb f′)
frame-update-merge f (ECR.Frm-Select repa) (ECR.Frm-Select repb) f′ =
  ECR.Frm-Select (frame-replace-used f repa repb f′)

replace-take :
  ∀ {n pk pk′}
    {Γ₀ Γx Γ₂ : Ctx [] n}
    {x : Fin n} {T : NfTy [] (KV pk Lin)} {U : NfTy [] (KV pk′ Lin)}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₂
  → ReplaceAt Γ₀ x (B-Lin U) Γx
  → Γx ⊢ˡ x ∶ U ⊣ Γ₂
replace-take {Γ₂ = B-Used T ▻ Γ} {T = T} {U = U} take-here ECR.R-here =
  subst
    (λ Γout → (B-Lin U ▻ Γ) ⊢ˡ zero ∶ U ⊣ Γout)
    (ECR.used-head-eq {T₁ = U} {T₂ = T} {Γ = Γ})
    take-here
replace-take (take-thereˡ take) (ECR.R-there rep) =
  take-thereˡ (replace-take take rep)
replace-take (take-thereᵘ take) (ECR.R-there rep) =
  take-thereᵘ (replace-take take rep)
replace-take (take-there✖ take) (ECR.R-there rep) =
  take-there✖ (replace-take take rep)

recv-disjoint-replace-eq :
  ∀ {n}
    {Γin Γin′ Γv Γv′ : Ctx [] n}
    {x : Fin n}
    {T : NfTy [] TLin}
    {S : NfTy [] SLin}
  → Γin ⊢ˡ x ∶ recvChanNf T S ⊣ Γin′
  → LinearDisjoint Γin Γv
  → ReplaceAt Γv x (B-Used S) Γv′
  → Γv′ ≡ Γv
recv-disjoint-replace-eq take-here (ECR.LD-live-used d) ECR.R-here =
  ECR.used-head-eq {T₁ = _} {T₂ = _}
recv-disjoint-replace-eq (take-thereˡ {U = U} take) (ECR.LD-live-used d) (ECR.R-there rep) =
  cong (B-Used U ▻_) (recv-disjoint-replace-eq take d rep)
recv-disjoint-replace-eq (take-thereᵘ {U = U} take) (ECR.LD-un-un d) (ECR.R-there rep) =
  cong (B-Un U ▻_) (recv-disjoint-replace-eq take d rep)
recv-disjoint-replace-eq (take-there✖ {U = U} take) (ECR.LD-used-used d) (ECR.R-there rep) =
  cong (B-Used U ▻_) (recv-disjoint-replace-eq take d rep)
recv-disjoint-replace-eq (take-there✖ {U = U} take) (ECR.LD-used-live d) (ECR.R-there rep) =
  cong (B-Lin U ▻_) (recv-disjoint-replace-eq take d rep)

merge-value :
  ∀ {n pk m}
    {Γin Γin′ Γx Γv-in Γ₁ Γv-used Γv-out : Ctx [] n}
    {x : Fin n}
    {Trecv : NfTy [] TLin}
    {S : NfTy [] SLin}
    {v : Value [] n} {T : NfTy [] (KV pk m)}
  → Γin ⊢ˡ x ∶ recvChanNf Trecv S ⊣ Γin′
  → LinearDisjoint Γin Γv-in
  → Γv-in ⊢ᵥ v ⇒ T ⊣ Γv-used
  → AllUsed Γv-used
  → ReplaceAt Γv-in x (B-Used S) Γv-out
  → FrameCtx Γx Γv-out Γ₁
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γx
merge-value take ld dv au rep merge
  rewrite recv-disjoint-replace-eq take ld rep =
  replay-value-allUsed dv merge au

postulate

  weaken-synth :
    ∀ {n Θ pk m}
      {Γ₁ Γ₂ : Ctx [] n}
      {e : Expr [] n} {T : NfTy [] (KV pk m)}
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
    → extendUsed Θ Γ₁ ⊢ ES.weakenExprBy (length Θ) e ⇒ T ⊣ extendUsed Θ Γ₂

  strengthen-letpair-body :
    ∀ {n pk₁ pk₂ pk m}
      {Γ₂ Γ₃ : Ctx [] n}
      {T : NfTy [] (KV pk₁ Lin)} {U : NfTy [] (KV pk₂ Lin)}
      {T′ : NfTy [] (KV pk₁ Lin)} {U′ : NfTy [] (KV pk₂ Lin)}
      {V : NfTy [] (KV pk m)}
      {e : Expr [] (suc (suc n))}
    → normalTyOf T′ <:ₜ normalTyOf T
    → normalTyOf U′ <:ₜ normalTyOf U
    → (T ∷ˡ (U ∷ˡ Γ₂)) ⊢ e ⇒ V ⊣ used∷ {T = T} (used∷ {T = U} Γ₃)
    → Σ (NfTy [] (KV pk m)) λ V′ →
        ((T′ ∷ˡ (U′ ∷ˡ Γ₂))
          ⊢ e ⇒ V′ ⊣ used∷ {T = T′} (used∷ {T = U′} Γ₃))
        × (normalTyOf V′ <:ₜ normalTyOf V)

  weaken-synth2 :
    ∀ {n Θ pk₁ pk₂ pk m}
      {Γ₂ Γ₃ : Ctx [] n}
      {T : NfTy [] (KV pk₁ Lin)} {U : NfTy [] (KV pk₂ Lin)}
      {V : NfTy [] (KV pk m)}
      {e : Expr [] (suc (suc n))}
    → (T ∷ˡ (U ∷ˡ Γ₂)) ⊢ e ⇒ V ⊣ used∷ {T = T} (used∷ {T = U} Γ₃)
    → (T ∷ˡ (U ∷ˡ extendUsed Θ Γ₂))
        ⊢ ES.weakenExprBy2 (length Θ) e ⇒ V ⊣ used∷ {T = T} (used∷ {T = U} (extendUsed Θ Γ₃))

  frame-update-value :
    ∀ {n Θ pk m}
      {ℓ : Label n Θ}
      {Γ Γ′ : Ctx [] n}
      {Γu : Ctx [] (length Θ + n)}
      {v : Value [] n}
      {T : NfTy [] (KV pk m)}
    → Γ ⊢ᵥ v ⇒ T ⊣ Γ′
    → AllUsed Γ′
    → Γ —frm[ ℓ ]→ Γu
    → Σ (Ctx [] (length Θ + n)) λ Γu′ →
        Γ′ —frm[ ℓ ]→ Γu′ × AllUsed Γu′ × (Γu ⊢ E-Val (ES.weakenValueBy (length Θ) v) ⇒ T ⊣ Γu′)

replace-used-preserves-disjoint-any :
  ∀ {Δ n pk₀ pk₁}
    {Γ₀ Γ₁ Γf Γf′ : Ctx Δ n}
    {x : Fin n}
    {U₀ : NfTy Δ (KV pk₀ Lin)}
    {U₁ : NfTy Δ (KV pk₁ Lin)}
  → LinearDisjoint Γ₀ Γf
  → ReplaceAt Γ₀ x (B-Used U₀) Γ₁
  → ReplaceAt Γf x (B-Used U₁) Γf′
  → LinearDisjoint Γ₁ Γf′
replace-used-preserves-disjoint-any
  {Γ₀ = B-Used T ▻ Γ₀} {Γf = B-Used T ▻ Γf} {U₀ = U₀} {U₁ = U₁}
  (ECR.LD-used-used ld) ECR.R-here ECR.R-here =
    subst
      (λ Γrhs → LinearDisjoint (B-Used U₀ ▻ Γ₀) Γrhs)
      (sym (ECR.used-head-eq {T₁ = U₁} {T₂ = U₀} {Γ = Γf}))
      (ECR.LD-used-used ld)
replace-used-preserves-disjoint-any
  {Γ₀ = B-Used T ▻ Γ₀} {Γf = B-Lin T ▻ Γf} {U₀ = U₀} {U₁ = U₁}
  (ECR.LD-used-live ld) ECR.R-here ECR.R-here =
    subst
      (λ Γrhs → LinearDisjoint (B-Used U₀ ▻ Γ₀) Γrhs)
      (sym (ECR.used-head-eq {T₁ = U₁} {T₂ = U₀} {Γ = Γf}))
      (ECR.LD-used-used ld)
replace-used-preserves-disjoint-any
  {Γ₀ = B-Lin T ▻ Γ₀} {Γf = B-Used T ▻ Γf} {U₀ = U₀} {U₁ = U₁}
  (ECR.LD-live-used ld) ECR.R-here ECR.R-here =
    subst
      (λ Γrhs → LinearDisjoint (B-Used U₀ ▻ Γ₀) Γrhs)
      (sym (ECR.used-head-eq {T₁ = U₁} {T₂ = U₀} {Γ = Γf}))
      (ECR.LD-used-used ld)
replace-used-preserves-disjoint-any
  {Γ₀ = B-Un T ▻ Γ₀} {Γf = B-Un T ▻ Γf} {U₀ = U₀} {U₁ = U₁}
  (ECR.LD-un-un ld) ECR.R-here ECR.R-here =
    subst
      (λ Γrhs → LinearDisjoint (B-Used U₀ ▻ Γ₀) Γrhs)
      (sym (ECR.used-head-eq {T₁ = U₁} {T₂ = U₀} {Γ = Γf}))
      (ECR.LD-used-used ld)
replace-used-preserves-disjoint-any (ECR.LD-used-used ld) (ECR.R-there rep₀) (ECR.R-there repf) =
  ECR.LD-used-used (replace-used-preserves-disjoint-any ld rep₀ repf)
replace-used-preserves-disjoint-any (ECR.LD-used-live ld) (ECR.R-there rep₀) (ECR.R-there repf) =
  ECR.LD-used-live (replace-used-preserves-disjoint-any ld rep₀ repf)
replace-used-preserves-disjoint-any (ECR.LD-live-used ld) (ECR.R-there rep₀) (ECR.R-there repf) =
  ECR.LD-live-used (replace-used-preserves-disjoint-any ld rep₀ repf)
replace-used-preserves-disjoint-any (ECR.LD-un-un ld) (ECR.R-there rep₀) (ECR.R-there repf) =
  ECR.LD-un-un (replace-used-preserves-disjoint-any ld rep₀ repf)

frame-update-preserves-disjoint :
  ∀ {n Θ}
    {ℓ : Label n Θ}
    {Γ₀ Γf : Ctx [] n}
    {Γ₀′ Γf′ : Ctx [] (length Θ + n)}
  → Γ₀ —frm[ ℓ ]→ Γ₀′
  → Γf —frm[ ℓ ]→ Γf′
  → LinearDisjoint Γ₀ Γf
  → LinearDisjoint Γ₀′ Γf′
frame-update-preserves-disjoint ECR.Frm-β ECR.Frm-β ld = ld
frame-update-preserves-disjoint ECR.Frm-New ECR.Frm-New ld =
  ECR.LD-used-used (ECR.LD-used-used ld)
frame-update-preserves-disjoint ECR.Frm-Fork ECR.Frm-Fork ld = ld
frame-update-preserves-disjoint (ECR.Frm-Rcv rep₀) (ECR.Frm-Rcv repf) ld =
  replace-used-preserves-disjoint-any ld rep₀ repf
frame-update-preserves-disjoint (ECR.Frm-Send rep₀) (ECR.Frm-Send repf) ld =
  replace-used-preserves-disjoint-any ld rep₀ repf
frame-update-preserves-disjoint (ECR.Frm-Close rep₀) (ECR.Frm-Close repf) ld =
  replace-used-preserves-disjoint-any ld rep₀ repf
frame-update-preserves-disjoint (ECR.Frm-Match i∈₀ rep₀) (ECR.Frm-Match i∈f repf) ld =
  replace-used-preserves-disjoint-any ld rep₀ repf
frame-update-preserves-disjoint (ECR.Frm-Select rep₀) (ECR.Frm-Select repf) ld =
  replace-used-preserves-disjoint-any ld rep₀ repf

ctx-tail :
  ∀ {Δ n}
  → Ctx Δ (suc n)
  → Ctx Δ n
ctx-tail (_ ▻ Γ) = Γ

used∷-injective :
  ∀ {Δ n pk}
    {T : NfTy Δ (KV pk Lin)}
    {Γ₁ Γ₂ : Ctx Δ n}
  → used∷ {T = T} Γ₁ ≡ used∷ {T = T} Γ₂
  → Γ₁ ≡ Γ₂
used∷-injective refl = refl

uvar-type-unique :
  ∀ {Δ n pk}
    {Γ : Ctx Δ n}
    {x : Fin n}
    {T U : NfTy Δ (KV pk Un)}
  → Γ ∋ᵘ x ∶ T
  → Γ ∋ᵘ x ∶ U
  → T ≡ U
uvar-type-unique hereᵘ hereᵘ = refl
uvar-type-unique (thereᵘˡ x∈) (thereᵘˡ y∈) = uvar-type-unique x∈ y∈
uvar-type-unique (thereᵘᵘ x∈) (thereᵘᵘ y∈) = uvar-type-unique x∈ y∈
uvar-type-unique (thereᵘ✖ x∈) (thereᵘ✖ y∈) = uvar-type-unique x∈ y∈

uvar-kind-unique :
  ∀ {Δ n pk₁ pk₂}
    {Γ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk₁ Un)}
    {U : NfTy Δ (KV pk₂ Un)}
  → Γ ∋ᵘ x ∶ T
  → Γ ∋ᵘ x ∶ U
  → pk₁ ≡ pk₂
uvar-kind-unique hereᵘ hereᵘ = refl
uvar-kind-unique (thereᵘˡ x∈) (thereᵘˡ y∈) = uvar-kind-unique x∈ y∈
uvar-kind-unique (thereᵘᵘ x∈) (thereᵘᵘ y∈) = uvar-kind-unique x∈ y∈
uvar-kind-unique (thereᵘ✖ x∈) (thereᵘ✖ y∈) = uvar-kind-unique x∈ y∈

constTy-unique :
  ∀ {Δ} {c : Const} {K}
    {T U : NfTy Δ K}
  → ConstTy c T
  → ConstTy c U
  → T ≡ U
constTy-unique CT-Unit CT-Unit = refl
constTy-unique CT-Fork CT-Fork = refl
constTy-unique CT-New CT-New = refl
constTy-unique CT-Receive CT-Receive = refl
constTy-unique CT-Send CT-Send = refl
constTy-unique CT-Close CT-Close = refl
constTy-unique CT-Select CT-Select = refl

arrowNf-cod-kind :
  ∀ {Δ pk₁ m₁ pk₂ m₂ pk₁′ m₁′ pk₂′ m₂′ m}
    {A : NfTy Δ (KV pk₁ m₁)}
    {B : NfTy Δ (KV pk₂ m₂)}
    {A′ : NfTy Δ (KV pk₁′ m₁′)}
    {B′ : NfTy Δ (KV pk₂′ m₂′)}
  → N-Arrow {m = m} A B ≡ N-Arrow {m = m} A′ B′
  → (pk₂ ≡ pk₂′) × (m₂ ≡ m₂′)
arrowNf-cod-kind refl = refl , refl

just-injective :
  ∀ {a} {A : Set a} {x y : A}
  → just x ≡ just y
  → x ≡ y
just-injective refl = refl

match-input-injective :
  ∀ {Δ k}
    {ss₁ ss₂ : Subset.Subset (suc k)}
    {v₁ v₂ : Variance}
    {P₁ P₂ : NfTy Δ KP}
    {S₁ S₂ : NfTy Δ SLin}
  → MatchBranchInput ss₁ v₁ P₁ S₁ ≡ MatchBranchInput ss₂ v₂ P₂ S₂
  → (ss₁ ≡ ss₂) × (v₁ ≡ v₂) × (P₁ ≡ P₂) × (S₁ ≡ S₂)
match-input-injective refl = refl , refl , refl , refl

mutual

  postulate
    value-kind-unique :
      ∀ {Δ n pk₁ m₁ pk₂ m₂}
        {Γ : Ctx Δ n}
        {v : Value Δ n}
        {T : NfTy Δ (KV pk₁ m₁)} {U : NfTy Δ (KV pk₂ m₂)}
        {Γ₁ Γ₂ : Ctx Δ n}
      → Γ ⊢ᵥ v ⇒ T ⊣ Γ₁
      → Γ ⊢ᵥ v ⇒ U ⊣ Γ₂
      → (pk₁ ≡ pk₂) × (m₁ ≡ m₂)

  synth-kind-unique :
    ∀ {Δ n pk₁ m₁ pk₂ m₂}
      {Γ : Ctx Δ n}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk₁ m₁)} {U : NfTy Δ (KV pk₂ m₂)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ e ⇒ T ⊣ Γ₁
    → Γ ⊢ e ⇒ U ⊣ Γ₂
    → (pk₁ ≡ pk₂) × (m₁ ≡ m₂)
  synth-kind-unique (T-Val d₁) (T-Val d₂) =
    value-kind-unique d₁ d₂
  synth-kind-unique (T-Pair d₁₁ d₁₂) (T-Pair d₂₁ d₂₂)
    with synth-kind-unique d₁₁ d₂₁
  ... | _ , eqm = refl , eqm
  synth-kind-unique (T-App d₁₁ d₁₂) (T-App d₂₁ d₂₂)
    with synth-kind-unique d₁₁ d₂₁
  ... | refl , refl
    with synth-unique d₁₁ d₂₁
  ... | eqArr , _
    with arrowNf-cod-kind eqArr
  ... | eqpk , eqm = eqpk , eqm
  synth-kind-unique (T-LetUnit d₁₁ d₁₂) (T-LetUnit d₂₁ d₂₂)
    with check-output-unique d₁₁ d₂₁
  ... | eqmid rewrite eqmid =
    synth-kind-unique d₁₂ d₂₂
  synth-kind-unique
    (T-LetPair {T = T} {U = U} d₁₁ d₁₂)
    (T-LetPair {T = T′} {U = U′} d₂₁ d₂₂)
    with synth-kind-unique d₁₁ d₂₁
  ... | refl , refl
    with synth-unique d₁₁ d₂₁
  ... | eqpair , eqmid
    rewrite eqmid
    with eqpair
  ... | refl =
      synth-kind-unique d₁₂ d₂₂
  synth-kind-unique
    (T-Match {ne = ne} d₁ bs₁ _)
    (T-Match {ne = .ne} d₂ bs₂ _)
    with synth-unique d₁ d₂
  ... | eqIn , eqmid
    rewrite eqmid
    with eqIn
  ... | refl
    with ne
  ... | i , i∈ = synth-kind-unique (bs₁ i i∈) (bs₂ i i∈)
  synth-kind-unique (T-TApp d₁) (T-TApp d₂)
    with synth-kind-unique d₁ d₂
  ... | refl , eqm = refl , eqm

  check-kind-unique :
    ∀ {Δ n pk₁ m₁ pk₂ m₂}
      {Γ : Ctx Δ n}
      {e : Expr Δ n}
      {T : NfTy Δ (KV pk₁ m₁)} {U : NfTy Δ (KV pk₂ m₂)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ e ⇐ T ⊣ Γ₁
    → Γ ⊢ e ⇐ U ⊣ Γ₂
    → (pk₁ ≡ pk₂) × (m₁ ≡ m₂)
  check-kind-unique (T-Check d₁ _) (T-Check d₂ _) =
    synth-kind-unique d₁ d₂

  synth-unique-match :
    ∀ {Δ n k pk m}
      {Γ Γ₃ Γ₃′ : Ctx Δ n}
      {e : Expr Δ n}
      {ssbranches : Subset.Subset (suc k)}
      {ne : Subset.Nonempty ssbranches}
      {branches : (i : Fin (suc k)) → i Subset.∈ ssbranches → Expr Δ (suc n)}
      {U₁ U₂ : NfTy Δ (KV pk m)}
    → Γ ⊢ E-Match {ss = ssbranches} e ne branches ⇒ U₁ ⊣ Γ₃
    → Γ ⊢ E-Match {ss = ssbranches} e ne branches ⇒ U₂ ⊣ Γ₃′
    → (U₁ ≡ U₂) × (Γ₃ ≡ Γ₃′)
  synth-unique-match
    {U₁ = U₁} {U₂ = U₂}
    (T-Match {Γ₂ = Γ₂} {ssbranches = ssbranches} {ne = ne} {branches = branches}
             {V = V₁} {sub = sub₁} d₁ bs₁ bj₁)
    (T-Match {Γ₂ = Γ₂′} {ssbranches = .ssbranches} {ne = .ne} {branches = .branches}
             {V = V₂} {sub = sub₂} d₂ bs₂ bj₂)
    with synth-unique d₁ d₂
  ... | eqIn , eqmid
    with match-input-injective eqIn
  ... | refl , refl , refl , refl
    rewrite eqmid
    with ne
  ... | i , i∈
    with synth-unique (bs₁ i i∈) (bs₂ i i∈)
  ... | _ , eqout =
    let eqΓ₃ = cong (λ where (_ ▻ Γtail) → Γtail) eqout in
    let V₂<:V₁ : (j : Fin _) → (j∈ : j Subset.∈ ssbranches) → V₂ j j∈ <:ₜ V₁ j j∈
        V₂<:V₁ j j∈ =
          subst
            (λ X → X <:ₜ V₁ j j∈)
            (proj₁ (synth-unique (bs₁ j j∈) (bs₂ j j∈)))
            (<:ₜ-refl (V₁ j j∈)) in
    let V₁<:V₂ : (j : Fin _) → (j∈ : j Subset.∈ ssbranches) → V₁ j j∈ <:ₜ V₂ j j∈
        V₁<:V₂ j j∈ =
          subst
            (λ X → V₁ j j∈ <:ₜ X)
            (proj₁ (synth-unique (bs₁ j j∈) (bs₂ j j∈)))
            (<:ₜ-refl (V₁ j j∈)) in
    let U₂′ , sub₂′ , bj₂′ , U₂′<:U₁ =
          ETS.branchjoin⁺-monotone
            {V = V₁}
            {V′ = V₂}
            bj₁
            V₂<:V₁ in
    let eqU₂′ : U₂′ ≡ U₂
        eqU₂′ = cong proj₁ (just-injective (trans (sym bj₂′) bj₂)) in
    let U₂<:U₁ : U₂ <:ₜ U₁
        U₂<:U₁ = subst (λ X → X <:ₜ U₁) eqU₂′ U₂′<:U₁ in
    let U₁′ , sub₁′ , bj₁′ , U₁′<:U₂ =
          ETS.branchjoin⁺-monotone
            {V = V₂}
            {V′ = V₁}
            bj₂
            V₁<:V₂ in
    let eqU₁′ : U₁′ ≡ U₁
        eqU₁′ = cong proj₁ (just-injective (trans (sym bj₁′) bj₁)) in
    let U₁<:U₂ : U₁ <:ₜ U₂
        U₁<:U₂ = subst (λ X → X <:ₜ U₂) eqU₁′ U₁′<:U₂ in
    NFSound.<:ₜ-antisym U₁<:U₂ U₂<:U₁ , eqΓ₃

  postulate
    value-unique :
      ∀ {Δ n pk m}
        {Γ : Ctx Δ n}
        {v : Value Δ n}
        {T U : NfTy Δ (KV pk m)}
        {Γ₁ Γ₂ : Ctx Δ n}
      → Γ ⊢ᵥ v ⇒ T ⊣ Γ₁
      → Γ ⊢ᵥ v ⇒ U ⊣ Γ₂
      → (T ≡ U) × (Γ₁ ≡ Γ₂)

  synth-unique :
    ∀ {Δ n pk m}
      {Γ : Ctx Δ n}
      {e : Expr Δ n}
      {T U : NfTy Δ (KV pk m)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ e ⇒ T ⊣ Γ₁
    → Γ ⊢ e ⇒ U ⊣ Γ₂
    → (T ≡ U) × (Γ₁ ≡ Γ₂)
  synth-unique (T-Val d₁) (T-Val d₂) =
    value-unique d₁ d₂
  synth-unique (T-Pair d₁₁ d₁₂) (T-Pair d₂₁ d₂₂)
    with synth-kind-unique d₁₁ d₂₁
  ... | refl , refl
    with synth-unique d₁₁ d₂₁
  ... | eqT , eqmid rewrite eqmid
    with synth-kind-unique d₁₂ d₂₂
  ... | refl , refl
    with synth-unique d₁₂ d₂₂
  ... | eqU , eqout rewrite eqT | eqU = refl , eqout
  synth-unique (T-App d₁₁ d₁₂) (T-App d₂₁ d₂₂)
    with synth-kind-unique d₁₁ d₂₁
  ... | refl , refl
    with synth-unique d₁₁ d₂₁
  ... | refl , eqmid rewrite eqmid
    with check-kind-unique d₁₂ d₂₂
  ... | refl , refl
    with check-unique d₁₂ d₂₂
  ... | eqout = refl , eqout
  synth-unique (T-LetUnit d₁₁ d₁₂) (T-LetUnit d₂₁ d₂₂)
    with check-unique d₁₁ d₂₁
  ... | eqmid rewrite eqmid =
    synth-unique d₁₂ d₂₂
  synth-unique
    (T-LetPair {T = T} {U = U} d₁₁ d₁₂)
    (T-LetPair {T = T′} {U = U′} d₂₁ d₂₂)
    with synth-kind-unique d₁₁ d₂₁
  ... | refl , refl
    with synth-unique d₁₁ d₂₁
  ... | refl , eqmid
    rewrite eqmid
    with synth-unique d₁₂ d₂₂
  ... | eqV , eqbody =
    eqV , cong (λ where (_ ▻ (_ ▻ Γtail)) → Γtail) eqbody
  synth-unique
    d₁@(T-Match {ssbranches = ssbranches} {ne = ne} {branches = branches} _ _ _)
    d₂@(T-Match {ssbranches = .ssbranches} {ne = .ne} {branches = .branches} _ _ _) =
    synth-unique-match
      {ssbranches = ssbranches}
      {ne = ne}
      {branches = branches}
      d₁ d₂
  synth-unique (T-TApp d₁) (T-TApp d₂)
    with synth-unique d₁ d₂
  ... | eqpoly , eqout rewrite polyNf-injective eqpoly = refl , eqout

  check-unique :
    ∀ {Δ n pk m}
      {Γ : Ctx Δ n} {e : Expr Δ n}
      {T U : NfTy Δ (KV pk m)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ e ⇐ T ⊣ Γ₁
    → Γ ⊢ e ⇐ U ⊣ Γ₂
    → Γ₁ ≡ Γ₂
  check-unique (T-Check d₁ _) (T-Check d₂ _) =
    proj₂ (synth-unique d₁ d₂)

  value-output-unique :
    ∀ {Δ n pk m}
      {Γ : Ctx Δ n}
      {v : Value Δ n}
      {T U : NfTy Δ (KV pk m)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ᵥ v ⇒ T ⊣ Γ₁
    → Γ ⊢ᵥ v ⇒ U ⊣ Γ₂
    → Γ₁ ≡ Γ₂
  value-output-unique d₁ d₂ = proj₂ (value-unique d₁ d₂)

  synth-output-unique-letpair :
    ∀ {Δ n pk m}
      {Γ Γ₃ Γ₃′ : Ctx Δ n}
      {e₁ : Expr Δ n} {e₂ : Expr Δ (suc (suc n))}
      {V V′ : NfTy Δ (KV pk m)}
    → Γ ⊢ E-LetPair e₁ e₂ ⇒ V ⊣ Γ₃
    → Γ ⊢ E-LetPair e₁ e₂ ⇒ V′ ⊣ Γ₃′
    → Γ₃ ≡ Γ₃′
  synth-output-unique-letpair d₁ d₂ = proj₂ (synth-unique d₁ d₂)

  synth-output-unique-match :
    ∀ {Δ n k pk m}
      {Γ Γ₃ Γ₃′ : Ctx Δ n}
      {e : Expr Δ n}
      {ssbranches : Subset.Subset (suc k)}
      {ne : Subset.Nonempty ssbranches}
      {branches : (i : Fin (suc k)) → i Subset.∈ ssbranches → Expr Δ (suc n)}
      {U₁ U₂ : NfTy Δ (KV pk m)}
    → Γ ⊢ E-Match {ss = ssbranches} e ne branches ⇒ U₁ ⊣ Γ₃
    → Γ ⊢ E-Match {ss = ssbranches} e ne branches ⇒ U₂ ⊣ Γ₃′
    → Γ₃ ≡ Γ₃′
  synth-output-unique-match d₁ d₂ = proj₂ (synth-unique-match d₁ d₂)

  synth-output-unique :
    ∀ {Δ n pk m}
      {Γ : Ctx Δ n}
      {e : Expr Δ n}
      {T U : NfTy Δ (KV pk m)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ e ⇒ T ⊣ Γ₁
    → Γ ⊢ e ⇒ U ⊣ Γ₂
    → Γ₁ ≡ Γ₂
  synth-output-unique d₁ d₂ = proj₂ (synth-unique d₁ d₂)

  check-output-unique :
    ∀ {Δ n pk m}
      {Γ : Ctx Δ n} {e : Expr Δ n}
      {T U : NfTy Δ (KV pk m)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ e ⇐ T ⊣ Γ₁
    → Γ ⊢ e ⇐ U ⊣ Γ₂
    → Γ₁ ≡ Γ₂
  check-output-unique d₁ d₂ = check-unique d₁ d₂
