module ExprTypingStrengthening where

open import Duality
open import Variance
open import Kinds
open import Types
open import Subtyping
open import TypesProtocolConstructors
import NormalTypes as NT
open import AlgorithmicNFMerge using (joinₜ)
open import AlgorithmicNFSubtyping using (_<:ₜ_; <:ₜ-trans)

open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_; here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.Product using (Σ; _×_; _,_; proj₁;proj₂; ∃-syntax)
open import Relation.Nullary using (¬_; Dec; yes; no; map′)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; inspect; Reveal_·_is_)

open import ExprNormalTyping
open import ExprSyntax hiding (Ctx)


-- lift algorithmic subtyping relation to contexts

data _<:Γ_ : ∀ {n} (Γ₁ : Ctx Δ n)(Γ₂ : Ctx Δ n) → Set where

  <:-[] : ∀ {Δ} → ∅ {Δ} <:Γ ∅

  <:-used : ∀ {Γ₁ Γ₂ : Ctx Δ n} → Γ₁ <:Γ Γ₂ → (B-Used ▻ Γ₁) <:Γ (B-Used ▻ Γ₂)

  <:-sub-lin  : ∀ {T₁ T₂ : NT.NFTy Δ (KV pk m)} {Γ₁ Γ₂ : Ctx Δ n} → T₁ <:ₜ T₂ → Γ₁ <:Γ Γ₂ → (B-Lin T₁ ▻ Γ₁) <:Γ (B-Lin T₂ ▻ Γ₂)

  <:-sub-unr  : ∀ {T₁ T₂ : NT.NFTy Δ (KV pk m)} {Γ₁ Γ₂ : Ctx Δ n} → T₁ <:ₜ T₂ → Γ₁ <:Γ Γ₂ → (B-Un T₁ ▻ Γ₁) <:Γ (B-Un T₂ ▻ Γ₂)


-- strengthening lemma

strengthen-synth :
    ∀ {n}
      {Γ₁ Γ₂ Γ₃ : Ctx [] n}
      {V : NfTy [] TLin}
      {e : Expr [] n}
    → Γ₁ <:Γ Γ₂
    → Γ₂ ⊢ e ⇒ V ⊣ Γ₃
    → Σ (NfTy [] TLin) λ V′ →
      Σ (Ctx [] n) λ Γ₃′ →
        (Γ₁ ⊢ e ⇒ V′ ⊣ Γ₃′)
        × (normalTyOf V′ <:ₜ normalTyOf V
        × Γ₃′ <:Γ Γ₃)

