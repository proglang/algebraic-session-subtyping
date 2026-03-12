module ExprTyping where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using () renaming (suc to sucℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import Kinds
open import Kits
open import Types
open import ExprSyntax
open import Subtyping

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (_⋯_; ⋯-id)

lookupCtx : (Γ : Ctx Δ) → Fin (length Γ) → Binding Δ
lookupCtx (b ∷ Γ) zero = b
lookupCtx (b ∷ Γ) (suc x) = lookupCtx Γ x

_∷ˡ_ : ∀ {K} → Ty Δ K → Ctx Δ → Ctx Δ
T ∷ˡ Γ = B-Lin T ∷ Γ

_∷ᵘ_ : ∀ {K} → Ty Δ K → Ctx Δ → Ctx Δ
T ∷ᵘ Γ = B-Un T ∷ Γ

wkBinding : ∀ {K} → Binding Δ → Binding (K ∷ Δ)
wkBinding {K = K} (B-Lin T) = B-Lin (T ⋯ weakenᵣ K)
wkBinding {K = K} (B-Un T) = B-Un (T ⋯ weakenᵣ K)

wkCtx : ∀ {K} → Ctx Δ → Ctx (K ∷ Δ)
wkCtx [] = []
wkCtx (b ∷ Γ) = wkBinding b ∷ wkCtx Γ

length-wkCtx : ∀ {K} (Γ : Ctx Δ) → length (wkCtx {K = K} Γ) ≡ length Γ
length-wkCtx [] = refl
length-wkCtx (_ ∷ Γ) = cong sucℕ (length-wkCtx Γ)

infix 4 _∋ˡ_∶_ _∋ᵘ_∶_

data _∋ˡ_∶_ {Δ} : (Γ : Ctx Δ) → Fin (length Γ) → ∀ {K} → Ty Δ K → Set where
  hereˡ  : ∀ {Γ K} {T : Ty Δ K} → (T ∷ˡ Γ) ∋ˡ zero ∶ T
  thereˡˡ : ∀ {Γ K K′} {x : Fin (length Γ)} {T : Ty Δ K} {U : Ty Δ K′}
    → Γ ∋ˡ x ∶ T
    → (U ∷ˡ Γ) ∋ˡ suc x ∶ T
  thereˡᵘ : ∀ {Γ K K′} {x : Fin (length Γ)} {T : Ty Δ K} {U : Ty Δ K′}
    → Γ ∋ˡ x ∶ T
    → (U ∷ᵘ Γ) ∋ˡ suc x ∶ T

data _∋ᵘ_∶_ {Δ} : (Γ : Ctx Δ) → Fin (length Γ) → ∀ {K} → Ty Δ K → Set where
  hereᵘ  : ∀ {Γ K} {T : Ty Δ K} → (T ∷ᵘ Γ) ∋ᵘ zero ∶ T
  thereᵘˡ : ∀ {Γ K K′} {x : Fin (length Γ)} {T : Ty Δ K} {U : Ty Δ K′}
    → Γ ∋ᵘ x ∶ T
    → (U ∷ˡ Γ) ∋ᵘ suc x ∶ T
  thereᵘᵘ : ∀ {Γ K K′} {x : Fin (length Γ)} {T : Ty Δ K} {U : Ty Δ K′}
    → Γ ∋ᵘ x ∶ T
    → (U ∷ᵘ Γ) ∋ᵘ suc x ∶ T

LinArr : Ty Δ TLin → Ty Δ TLin → Ty Δ TLin
LinArr = T-Arrow {pk = KT} {m = Lin} (≤p-step <p-mt)

data ConstTy {Δ} : Const → ∀ {K} → Ty Δ K → Set where
  CT-Unit : ConstTy C-Unit T-Base

infix 4 _⊢_⇒_ _⊢_⇐_

data _⊢_⇒_ {Δ} (Γ : Ctx Δ) : Expr Δ (length Γ) → ∀ {K} → Ty Δ K → Set
data _⊢_⇐_ {Δ} (Γ : Ctx Δ) : Expr Δ (length Γ) → ∀ {K} → Ty Δ K → Set

data _⊢_⇒_ {Δ} Γ where
  T-Const : ∀ {c K} {T : Ty Δ K} → ConstTy c T → Γ ⊢ E-Val (V-Const c) ⇒ T

  T-Var-Lin : ∀ {K} {x : Fin (length Γ)} {T : Ty Δ K}
    → Γ ∋ˡ x ∶ T
    → Γ ⊢ E-Val (V-Var x) ⇒ T

  T-Var-Un : ∀ {K} {x : Fin (length Γ)} {T : Ty Δ K}
    → Γ ∋ᵘ x ∶ T
    → Γ ⊢ E-Val (V-Var x) ⇒ T

  T-Abs : ∀ {T U : Ty Δ TLin} {e : Expr Δ (length (T ∷ˡ Γ))}
    → (T ∷ˡ Γ) ⊢ e ⇒ U
    → Γ ⊢ E-Val (V-Abs T e) ⇒ LinArr T U

  T-Rec : ∀ {T : Ty Δ TLin} {v : Value Δ (length (T ∷ᵘ Γ))}
    → (T ∷ᵘ Γ) ⊢ E-Val v ⇐ T
    → Γ ⊢ E-Val (V-Rec T v) ⇒ T

  T-TAbs : ∀ {K m} {v : Value (K ∷ Δ) (length Γ)} {T : Ty (K ∷ Δ) (KV KT m)}
    → wkCtx {K = K} Γ ⊢ subst (Expr (K ∷ Δ)) (sym (length-wkCtx {K = K} Γ)) (E-Val v) ⇒ T
    → Γ ⊢ E-Val (V-TAbs K v) ⇒ T-Poly T

  T-Pair : ∀ {e₁ e₂ : Expr Δ (length Γ)} {T U : Ty Δ TLin}
    → Γ ⊢ e₁ ⇒ T
    → Γ ⊢ e₂ ⇒ U
    → Γ ⊢ E-Pair e₁ e₂ ⇒ T-Pair T U

  T-App : ∀ {e₁ e₂ : Expr Δ (length Γ)} {T U : Ty Δ TLin}
    → Γ ⊢ e₁ ⇒ LinArr T U
    → Γ ⊢ e₂ ⇐ T
    → Γ ⊢ E-App e₁ e₂ ⇒ U

  T-LetPair : ∀ {T U V : Ty Δ TLin} {e₁ : Expr Δ (length Γ)} {e₂ : Expr Δ (length (T ∷ˡ (U ∷ˡ Γ)))}
    → Γ ⊢ e₁ ⇒ T-Pair T U
    → (T ∷ˡ (U ∷ˡ Γ)) ⊢ e₂ ⇒ V
    → Γ ⊢ E-LetPair e₁ e₂ ⇒ V

  T-TApp : ∀ {K m} {e : Expr Δ (length Γ)} {T : Ty (K ∷ Δ) (KV KT m)} {U : Ty Δ K}
    → Γ ⊢ e ⇒ T-Poly T
    → Γ ⊢ E-TApp e U ⇒ T ⋯ ⦅ U ⦆ₛ

data _⊢_⇐_ {Δ} Γ where
  T-Check : ∀ {e : Expr Δ (length Γ)} {K} {T U : Ty Δ K}
    → Γ ⊢ e ⇒ U
    → U <: T
    → Γ ⊢ e ⇐ T
