module ExprNormalTyping where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes)

open import Kinds
open import Kits
open import Duality
open import Types
open import ExprSyntax hiding (Binding; Ctx)
open import AlgorithmicSubtyping
open import AlgorithmicMerge

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (_⋯_; ⋯-id)

Normal : ∀ {Δ K} → Ty Δ K → Set
Normal {K = KV pk m} T = NormalTy T
Normal {K = KP} T = NormalProto T

data NfTy (Δ : List Kind) (K : Kind) : Set where
  mkNfTy : (T : Ty Δ K) → Normal T → NfTy Δ K

⌞_⌟ : NfTy Δ K → Ty Δ K
⌞ mkNfTy T _ ⌟ = T

normalOf : (N : NfTy Δ K) → Normal (⌞ N ⌟)
normalOf (mkNfTy _ NT) = NT

normalTyOf : (N : NfTy Δ (KV pk m)) → NormalTy (⌞ N ⌟)
normalTyOf (mkNfTy _ NT) = NT

normalProtoOf : (N : NfTy Δ KP) → NormalProto (⌞ N ⌟)
normalProtoOf (mkNfTy _ NT) = NT

normalizeTy : ∀ {K} → Ty Δ K → NfTy Δ K
normalizeTy {K = KV pk m} T = mkNfTy (nf ⊕ d?⊥ T) (nf-normal-type ⊕ d?⊥ T)
normalizeTy {K = KP} T = mkNfTy (nf ⊕ d?⊥ T) (nf-normal-proto T)

data Binding (Δ : List Kind) : Set where
  B-Lin  : ∀ {K} → NfTy Δ K → Binding Δ
  B-Un   : ∀ {K} → NfTy Δ K → Binding Δ
  B-Used : Binding Δ

infixr 5 _▻_

data Ctx (Δ : List Kind) : ℕ → Set where
  ∅   : Ctx Δ 0
  _▻_ : ∀ {n} → Binding Δ → Ctx Δ n → Ctx Δ (suc n)

_∷ˡ_ : ∀ {n K} → NfTy Δ K → Ctx Δ n → Ctx Δ (suc n)
T ∷ˡ Γ = B-Lin T ▻ Γ

_∷ᵘ_ : ∀ {n K} → NfTy Δ K → Ctx Δ n → Ctx Δ (suc n)
T ∷ᵘ Γ = B-Un T ▻ Γ

_∷ⁿˡ_ : ∀ {n K} → Ty Δ K → Ctx Δ n → Ctx Δ (suc n)
T ∷ⁿˡ Γ = normalizeTy T ∷ˡ Γ

_∷ⁿᵘ_ : ∀ {n K} → Ty Δ K → Ctx Δ n → Ctx Δ (suc n)
T ∷ⁿᵘ Γ = normalizeTy T ∷ᵘ Γ

used∷ : ∀ {n} → Ctx Δ n → Ctx Δ (suc n)
used∷ Γ = B-Used ▻ Γ

wkNfTy : ∀ {K K′} → NfTy Δ K → NfTy (K′ ∷ Δ) K
wkNfTy {K′ = K′} (mkNfTy T _) = normalizeTy (T ⋯ weakenᵣ K′)

wkBinding : ∀ {K} → Binding Δ → Binding (K ∷ Δ)
wkBinding {K = K} (B-Lin T) = B-Lin (wkNfTy {K′ = K} T)
wkBinding {K = K} (B-Un T) = B-Un (wkNfTy {K′ = K} T)
wkBinding B-Used = B-Used

wkCtx : ∀ {n K} → Ctx Δ n → Ctx (K ∷ Δ) n
wkCtx ∅ = ∅
wkCtx (b ▻ Γ) = wkBinding b ▻ wkCtx Γ

LinArr : Ty Δ TLin → Ty Δ TLin → Ty Δ TLin
LinArr = T-Arrow {pk = KT} {m = Lin} (≤p-step <p-mt)

linArrNf : NfTy Δ TLin → NfTy Δ TLin → NfTy Δ TLin
linArrNf (mkNfTy T NT) (mkNfTy U NU) = mkNfTy (LinArr T U) (N-Arrow NT NU)

pairNf : NfTy Δ TLin → NfTy Δ TLin → NfTy Δ TLin
pairNf (mkNfTy T NT) (mkNfTy U NU) = mkNfTy (T-Pair T U) (N-Pair NT NU)

polyNf : NfTy (K ∷ Δ) (KV KT m) → NfTy Δ (KV KT m)
polyNf (mkNfTy T NT) = mkNfTy (T-Poly T) (N-Poly NT)

UnitLin : Ty Δ TLin
UnitLin = T-Sub (≤k-step (≤p-step <p-mt) ≤m-unl) T-Base

SessLin : Ty Δ SLin → Ty Δ TLin
SessLin = T-Sub (≤k-step (≤p-step <p-st) ≤m-refl)

EndLin : Ty Δ TLin
EndLin = T-Sub (≤k-step (≤p-step <p-st) ≤m-unl) T-End

ForkTy : Ty Δ TLin
ForkTy = LinArr (LinArr UnitLin UnitLin) UnitLin

NewTy : Ty Δ TLin
NewTy = T-Poly {K′ = SLin} {m = Lin}
  (T-Pair (T-Var (here refl)) (T-Dual D-S (T-Var (here refl))))

wkTy : ∀ {K K′} → Ty Δ K → Ty (K′ ∷ Δ) K
wkTy {K′ = K′} T = T ⋯ weakenᵣ K′

ReceiveTy : Ty Δ TLin → Ty Δ SLin → Ty Δ TLin
ReceiveTy T S = LinArr
  (SessLin (T-Msg ⊝ (T-Up T) S))
  (T-Pair T S)

ReceiveTy1 : Ty Δ TLin → Ty Δ TLin
ReceiveTy1 T = T-Poly {K′ = SLin} {m = Lin}
  (ReceiveTy (wkTy {K′ = SLin} T) (T-Var (here refl)))

SendTy : Ty Δ TLin → Ty Δ SLin → Ty Δ TLin
SendTy T S = LinArr T
  (LinArr (SessLin (T-Msg ⊕ (T-Up T) S)) (SessLin S))

SendTy1 : Ty Δ TLin → Ty Δ TLin
SendTy1 T = T-Poly {K′ = SLin} {m = Lin}
  (SendTy (wkTy {K′ = SLin} T) (T-Var (here refl)))

postulate
  MatchBranches : ∀ {Δ k} → NfTy Δ SLin → (Fin k → NfTy Δ SLin) → Set
  SelectConstTy : ∀ {Δ k} (i : Fin k) → ∀ {K} → NfTy Δ K → Set
  SelectInstTy  : ∀ {Δ k} (i : Fin k) (args : List (TyArg Δ)) → ∀ {K} → NfTy Δ K → Set

data BranchJoin {Δ} : ∀ {k} → (Fin (suc k) → NfTy Δ TLin) → NfTy Δ TLin → Set where
  BJ-one : ∀ {T}
    → BranchJoin {k = 0} (λ { zero → T }) T

  BJ-step : ∀ {k} {V : Fin (suc (suc k)) → NfTy Δ TLin} {U W : NfTy Δ TLin}
      {<:₁ : normalTyOf (V zero) <:ₜ normalTyOf W}
      {<:₂ : normalTyOf U <:ₜ normalTyOf W}
    → BranchJoin (λ i → V (suc i)) U
    → joinₜ (normalTyOf (V zero)) (normalTyOf U) ≡ yes (⌞ W ⌟ , normalTyOf W , <:₁ , <:₂)
    → BranchJoin V W

data ConstTy {Δ} : Const → ∀ {K} → NfTy Δ K → Set where
  CT-Unit : ConstTy C-Unit (normalizeTy T-Base)
  CT-Fork : ConstTy C-Fork (normalizeTy ForkTy)
  CT-New  : ConstTy C-New (normalizeTy NewTy)
  CT-Receive : ConstTy C-Receive
    (normalizeTy (T-Poly {K′ = TLin} {m = Lin} (ReceiveTy1 (T-Var (here refl)))))
  CT-Send : ConstTy C-Send
    (normalizeTy (T-Poly {K′ = TLin} {m = Lin} (SendTy1 (T-Var (here refl)))))
  CT-Close : ConstTy C-Close (normalizeTy (LinArr EndLin UnitLin))
  CT-Select : ∀ {k} {i : Fin k} {K} {T : NfTy Δ K}
    → SelectConstTy i T
    → ConstTy (C-Select i) T

infix 4 _∋ˡ_∶_ _∋ᵘ_∶_ _⊢ˡ_∶_⊣_ _⊢ᵥ_⇒_⊣_ _⊢_⇒_⊣_ _⊢_⇐_⊣_

data _∋ˡ_∶_ {Δ} : ∀ {n} → Ctx Δ n → Fin n → ∀ {K} → NfTy Δ K → Set where
  hereˡ : ∀ {n} {Γ : Ctx Δ n} {K} {T : NfTy Δ K}
    → (T ∷ˡ Γ) ∋ˡ zero ∶ T
  thereˡˡ : ∀ {Γ K K′} {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
    → Γ ∋ˡ x ∶ T
    → (U ∷ˡ Γ) ∋ˡ suc x ∶ T
  thereˡᵘ : ∀ {Γ K K′} {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
    → Γ ∋ˡ x ∶ T
    → (U ∷ᵘ Γ) ∋ˡ suc x ∶ T
  thereˡ✖ : ∀ {Γ K} {x : Fin n} {T : NfTy Δ K}
    → Γ ∋ˡ x ∶ T
    → used∷ Γ ∋ˡ suc x ∶ T

data _∋ᵘ_∶_ {Δ} : ∀ {n} → Ctx Δ n → Fin n → ∀ {K} → NfTy Δ K → Set where
  hereᵘ : ∀ {n} {Γ : Ctx Δ n} {K} {T : NfTy Δ K}
    → (T ∷ᵘ Γ) ∋ᵘ zero ∶ T
  thereᵘˡ : ∀ {Γ K K′} {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
    → Γ ∋ᵘ x ∶ T
    → (U ∷ˡ Γ) ∋ᵘ suc x ∶ T
  thereᵘᵘ : ∀ {Γ K K′} {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
    → Γ ∋ᵘ x ∶ T
    → (U ∷ᵘ Γ) ∋ᵘ suc x ∶ T
  thereᵘ✖ : ∀ {Γ K} {x : Fin n} {T : NfTy Δ K}
    → Γ ∋ᵘ x ∶ T
    → used∷ Γ ∋ᵘ suc x ∶ T

mutual
  data _⊢ˡ_∶_⊣_ {Δ} : ∀ {n} → Ctx Δ n → Fin n → ∀ {K} → NfTy Δ K → Ctx Δ n → Set where
    take-here : ∀ {n} {Γ : Ctx Δ n} {K} {T : NfTy Δ K}
      → (T ∷ˡ Γ) ⊢ˡ zero ∶ T ⊣ used∷ Γ

    take-thereˡ : ∀ {Γ Γ′ K K′} {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
      → Γ ⊢ˡ x ∶ T ⊣ Γ′
      → (U ∷ˡ Γ) ⊢ˡ suc x ∶ T ⊣ (U ∷ˡ Γ′)

    take-thereᵘ : ∀ {Γ Γ′ K K′} {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
      → Γ ⊢ˡ x ∶ T ⊣ Γ′
      → (U ∷ᵘ Γ) ⊢ˡ suc x ∶ T ⊣ (U ∷ᵘ Γ′)

    take-there✖ : ∀ {Γ Γ′ K} {x : Fin n} {T : NfTy Δ K}
      → Γ ⊢ˡ x ∶ T ⊣ Γ′
      → used∷ Γ ⊢ˡ suc x ∶ T ⊣ used∷ Γ′

  data _⊢ᵥ_⇒_⊣_ {Δ} : ∀ {n} → (Γ₁ : Ctx Δ n) → Value Δ n → ∀ {K} → NfTy Δ K → Ctx Δ n → Set where
    TV-Const : ∀ {n} {Γ₁ : Ctx Δ n} {c K} {T : NfTy Δ K}
      → ConstTy c T
      → Γ₁ ⊢ᵥ V-Const c ⇒ T ⊣ Γ₁

    TV-Var-Lin : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {K} {x : Fin n} {T : NfTy Δ K}
      → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂
      → Γ₁ ⊢ᵥ V-Var x ⇒ T ⊣ Γ₂

    TV-Var-Un : ∀ {n} {Γ₁ : Ctx Δ n} {K} {x : Fin n} {T : NfTy Δ K}
      → Γ₁ ∋ᵘ x ∶ T
      → Γ₁ ⊢ᵥ V-Var x ⇒ T ⊣ Γ₁

    TV-Abs : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {T : Ty Δ TLin} {U : NfTy Δ TLin} {e : Expr Δ (suc n)}
      → (T ∷ⁿˡ Γ₁) ⊢ e ⇒ U ⊣ used∷ Γ₂
      → Γ₁ ⊢ᵥ V-Abs T e ⇒ linArrNf (normalizeTy T) U ⊣ Γ₂

    TV-Rec : ∀ {n} {Γ₁ : Ctx Δ n} {T : Ty Δ TLin} {v : Value Δ (suc n)}
      → (T ∷ⁿᵘ Γ₁) ⊢ E-Val v ⇐ normalizeTy T ⊣ (T ∷ⁿᵘ Γ₁)
      → Γ₁ ⊢ᵥ V-Rec T v ⇒ normalizeTy T ⊣ Γ₁

    TV-TAbs : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {K m}
        {v : Value (K ∷ Δ) n} {T : NfTy (K ∷ Δ) (KV KT m)}
      → wkCtx {K = K} Γ₁ ⊢ᵥ v ⇒ T ⊣ wkCtx Γ₂
      → Γ₁ ⊢ᵥ V-TAbs K v ⇒ polyNf T ⊣ Γ₂

    TV-Pair : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {v₁ v₂ : Value Δ n}
        {T : NfTy Δ TLin} {U : NfTy Δ TLin}
      → Γ₁ ⊢ᵥ v₁ ⇒ T ⊣ Γ₂
      → Γ₂ ⊢ᵥ v₂ ⇒ U ⊣ Γ₃
      → Γ₁ ⊢ᵥ V-Pair v₁ v₂ ⇒ pairNf T U ⊣ Γ₃

    TV-Receive₁ : ∀ {n} {Γ₁ : Ctx Δ n} {T : Ty Δ TLin}
      → Γ₁ ⊢ᵥ V-Receive₁ T ⇒ normalizeTy (ReceiveTy1 T) ⊣ Γ₁

    TV-Receive₂ : ∀ {n} {Γ₁ : Ctx Δ n} {T : Ty Δ TLin} {S : Ty Δ SLin}
      → Γ₁ ⊢ᵥ V-Receive₂ T S ⇒ normalizeTy (ReceiveTy T S) ⊣ Γ₁

    TV-Send₁ : ∀ {n} {Γ₁ : Ctx Δ n} {T : Ty Δ TLin}
      → Γ₁ ⊢ᵥ V-Send₁ T ⇒ normalizeTy (SendTy1 T) ⊣ Γ₁

    TV-Send₂ : ∀ {n} {Γ₁ : Ctx Δ n} {T : Ty Δ TLin} {S : Ty Δ SLin}
      → Γ₁ ⊢ᵥ V-Send₂ T S ⇒ normalizeTy (SendTy T S) ⊣ Γ₁

    TV-Send₃ : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {T : Ty Δ TLin} {S : Ty Δ SLin} {v : Value Δ n}
      → Γ₁ ⊢ᵥ v ⇒ normalizeTy T ⊣ Γ₂
      → Γ₁ ⊢ᵥ V-Send₃ T S v ⇒ normalizeTy (LinArr (SessLin (T-Msg ⊕ (T-Up T) S)) (SessLin S)) ⊣ Γ₂

    TV-Selectᵀ : ∀ {n} {Γ₁ : Ctx Δ n} {k} {i : Fin k} {args : List (TyArg Δ)} {K} {T : NfTy Δ K}
      → SelectInstTy i args T
      → Γ₁ ⊢ᵥ V-Selectᵀ i args ⇒ T ⊣ Γ₁

  data _⊢_⇒_⊣_ {Δ} : ∀ {n} → (Γ₁ : Ctx Δ n) → Expr Δ n → ∀ {K} → NfTy Δ K → Ctx Δ n → Set where
    T-Val : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {v : Value Δ n} {K} {T : NfTy Δ K}
      → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
      → Γ₁ ⊢ E-Val v ⇒ T ⊣ Γ₂

    T-Pair : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n}
        {T : NfTy Δ TLin} {U : NfTy Δ TLin}
      → Γ₁ ⊢ e₁ ⇒ T ⊣ Γ₂
      → Γ₂ ⊢ e₂ ⇒ U ⊣ Γ₃
      → Γ₁ ⊢ E-Pair e₁ e₂ ⇒ pairNf T U ⊣ Γ₃

    T-App : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n}
        {T U : NfTy Δ TLin}
      → Γ₁ ⊢ e₁ ⇒ linArrNf T U ⊣ Γ₂
      → Γ₂ ⊢ e₂ ⇐ T ⊣ Γ₃
      → Γ₁ ⊢ E-App e₁ e₂ ⇒ U ⊣ Γ₃

    T-LetUnit : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n} {T : NfTy Δ TLin}
      → Γ₁ ⊢ e₁ ⇐ normalizeTy T-Base ⊣ Γ₂
      → Γ₂ ⊢ e₂ ⇒ T ⊣ Γ₃
      → Γ₁ ⊢ E-LetUnit e₁ e₂ ⇒ T ⊣ Γ₃

    T-LetPair : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {T U V : NfTy Δ TLin}
        {e₁ : Expr Δ n} {e₂ : Expr Δ (suc (suc n))}
      → Γ₁ ⊢ e₁ ⇒ pairNf T U ⊣ Γ₂
      → (T ∷ˡ (U ∷ˡ Γ₂)) ⊢ e₂ ⇒ V ⊣ used∷ (used∷ Γ₃)
      → Γ₁ ⊢ E-LetPair e₁ e₂ ⇒ V ⊣ Γ₃

    T-Match : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {k} {e : Expr Δ n}
        {branches : Fin (suc k) → Expr Δ (suc n)}
        {T : NfTy Δ SLin} {U : NfTy Δ TLin}
        {B : Fin (suc k) → NfTy Δ SLin} {V : Fin (suc k) → NfTy Δ TLin}
      → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
      → MatchBranches T B
      → ((i : Fin (suc k)) → (B i ∷ˡ Γ₂) ⊢ branches i ⇒ V i ⊣ used∷ Γ₃)
      → BranchJoin V U
      → Γ₁ ⊢ E-Match e branches ⇒ U ⊣ Γ₃

    T-TApp : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {K m}
        {e : Expr Δ n} {T : NfTy (K ∷ Δ) (KV KT m)} {U : Ty Δ K}
      → Γ₁ ⊢ e ⇒ polyNf T ⊣ Γ₂
      → Γ₁ ⊢ E-TApp e U ⇒ normalizeTy (⌞ T ⌟ ⋯ ⦅ U ⦆ₛ) ⊣ Γ₂

  data _⊢_⇐_⊣_ {Δ} : ∀ {n} → (Γ₁ : Ctx Δ n) → Expr Δ n → ∀ {pk m} → NfTy Δ (KV pk m) → Ctx Δ n → Set where
    T-Check : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {e : Expr Δ n} {pk m}
        {T U : NfTy Δ (KV pk m)}
      → Γ₁ ⊢ e ⇒ U ⊣ Γ₂
      → normalTyOf U <:ₜ normalTyOf T
      → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
