module ExprPreservationStep2.Properties where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (suc; _+_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import Duality
open import Kinds
import Types
open import Types using (Ty)
open import NormalTypes using (N-Arrow)
open import ExprSyntax using (Expr; Value; E-Val)
import ExprSemantics as ES
open import ExprSemantics using (Label)
open import ExprNormalTyping
open import AlgorithmicNFSubtyping using (_<:ₜ_; <:ₜ-sub)
import ExprContextReduction as ECR
open import ExprContextReduction using
  ( _—frm[_]→_
  ; ReplaceAt
  ; RemoveCtx
  ; MergeCtx
  ; AllUsed
  ; LinearDisjoint
  ; allUsedCtx
  ; extendUsed
  ; sendChanNf
  ; dualSessNf
  ; Frm-New
  )
open import ExprTypingProperties using (FrameCtx)
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
  ∀ {n pk}
    {Γ : Ctx [] n}
    {x : Fin n} {T U : NfTy [] (KV pk Lin)}
    {Γ₁ Γ₂ : Ctx [] n}
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

sess-subtype :
  ∀ {S₁ S₂ : NfTy [] SLin}
  → normalTyOf S₁ <:ₜ normalTyOf S₂
  → normalTyOf (sessTyNf S₁) <:ₜ normalTyOf (sessTyNf S₂)
sess-subtype sub = <:ₜ-sub sub

arrow-subtype-inversion :
  ∀ {m A V U}
  → normalTyOf U <:ₜ normalTyOf (N-Arrow {m = m} (≤p-step <p-mt) A V)
  → Σ (NfTy [] TLin) λ A′ →
      Σ (NfTy [] TLin) λ V′ →
        (U ≡ N-Arrow {m = m} (≤p-step <p-mt) A′ V′)
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

postulate

  merge-value :
    ∀ {n K pk}
      {Γx Γv-in Γ₁ Γv-used Γv-out : Ctx [] n}
      {x : Fin n}
      {S : NfTy [] (KV pk Lin)}
      {v : Value [] n} {T : NfTy [] K}
    → Γv-in ⊢ᵥ v ⇒ T ⊣ Γv-used
    → AllUsed Γv-used
    → ReplaceAt Γv-in x (B-Used S) Γv-out
    → LinearDisjoint Γx Γv-out
    → MergeCtx Γx Γv-out Γ₁
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γx

  replace-take :
    ∀ {n pk pk′}
      {Γ₀ Γx Γ₂ : Ctx [] n}
      {x : Fin n} {T : NfTy [] (KV pk Lin)} {U : NfTy [] (KV pk′ Lin)}
    → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₂
    → ReplaceAt Γ₀ x (B-Lin U) Γx
    → Γx ⊢ˡ x ∶ U ⊣ Γ₂

  weaken-synth :
    ∀ {n Θ K}
      {Γ₁ Γ₂ : Ctx [] n}
      {e : Expr [] n} {T : NfTy [] K}
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
    → extendUsed Θ Γ₁ ⊢ ES.weakenExprBy (length Θ) e ⇒ T ⊣ extendUsed Θ Γ₂

  strengthen-letpair-body :
    ∀ {n pk₁ pk₂}
      {Γ₂ Γ₃ : Ctx [] n}
      {T : NfTy [] (KV pk₁ Lin)} {U : NfTy [] (KV pk₂ Lin)}
      {T′ : NfTy [] (KV pk₁ Lin)} {U′ : NfTy [] (KV pk₂ Lin)}
      {V : NfTy [] TLin}
      {e : Expr [] (suc (suc n))}
    → normalTyOf T′ <:ₜ normalTyOf T
    → normalTyOf U′ <:ₜ normalTyOf U
    → (T ∷ˡ (U ∷ˡ Γ₂)) ⊢ e ⇒ V ⊣ used∷ {T = T} (used∷ {T = U} Γ₃)
    → Σ (NfTy [] TLin) λ V′ →
        ((T′ ∷ˡ (U′ ∷ˡ Γ₂))
          ⊢ e ⇒ V′ ⊣ used∷ {T = T′} (used∷ {T = U′} Γ₃))
        × (normalTyOf V′ <:ₜ normalTyOf V)

  weaken-synth2 :
    ∀ {n Θ pk₁ pk₂}
      {Γ₂ Γ₃ : Ctx [] n}
      {T : NfTy [] (KV pk₁ Lin)} {U : NfTy [] (KV pk₂ Lin)}
      {V : NfTy [] TLin}
      {e : Expr [] (suc (suc n))}
    → (T ∷ˡ (U ∷ˡ Γ₂)) ⊢ e ⇒ V ⊣ used∷ {T = T} (used∷ {T = U} Γ₃)
    → (T ∷ˡ (U ∷ˡ extendUsed Θ Γ₂))
        ⊢ ES.weakenExprBy2 (length Θ) e ⇒ V ⊣ used∷ {T = T} (used∷ {T = U} (extendUsed Θ Γ₃))

  remove-frame :
    ∀ {n}
      {Γ₀ Γv Γx : Ctx [] n}
    → RemoveCtx Γ₀ Γv Γx
    → FrameCtx Γx Γv Γ₀

  merge-frame :
    ∀ {n}
      {Γx Γv Γ₁ : Ctx [] n}
    → LinearDisjoint Γx Γv
    → MergeCtx Γx Γv Γ₁
    → FrameCtx Γx Γv Γ₁

  frame-update-merge :
    ∀ {n Θ}
      {ℓ : Label n Θ}
      {Γa Γb Γab : Ctx [] n}
      {Γa′ Γb′ Γab′ : Ctx [] (length Θ + n)}
    → MergeCtx Γa Γb Γab
    → Γa —frm[ ℓ ]→ Γa′
    → Γb —frm[ ℓ ]→ Γb′
    → MergeCtx Γa′ Γb′ Γab′
    → Γab —frm[ ℓ ]→ Γab′

  frame-update-value :
    ∀ {n Θ K}
      {ℓ : Label n Θ}
      {Γ Γ′ : Ctx [] n}
      {Γu : Ctx [] (length Θ + n)}
      {v : Value [] n}
      {T : NfTy [] K}
    → Γ ⊢ᵥ v ⇒ T ⊣ Γ′
    → AllUsed Γ′
    → Γ —frm[ ℓ ]→ Γu
    → Σ (Ctx [] (length Θ + n)) λ Γu′ →
        Γ′ —frm[ ℓ ]→ Γu′ × AllUsed Γu′ × (Γu ⊢ E-Val (ES.weakenValueBy (length Θ) v) ⇒ T ⊣ Γu′)

  frame-update-preserves-disjoint :
    ∀ {n Θ}
      {ℓ : Label n Θ}
      {Γ₀ Γf : Ctx [] n}
      {Γ₀′ Γf′ : Ctx [] (length Θ + n)}
    → Γ₀ —frm[ ℓ ]→ Γ₀′
    → Γf —frm[ ℓ ]→ Γf′
    → LinearDisjoint Γ₀ Γf
    → LinearDisjoint Γ₀′ Γf′

