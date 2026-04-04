module ExprNormalTyping where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes)

open import Kinds
open import Kits
open import Duality
open import Types
open import TypesProperties using (renaming-injective; weakenᵣ-injective)
open import TypesProtocolConstructors using (SelectTy1; SelectTy2; SelectConstTy)
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

ren-pres-normalVar :
  ∀ {Δ Δ′ pk m} {T : Ty Δ (KV pk m)} (ρ : Δ →ᵣ Δ′)
  → NormalVar T
  → NormalVar (T ⋯ ρ)
ren-pres-normalVar ρ NV-Var = NV-Var
ren-pres-normalVar ρ (NV-Dual d x) = NV-Dual d _

ren-pres-normalProto′ :
  ∀ {Δ Δ′} {T : Ty Δ KP} (ρ : Δ →ᵣ Δ′)
  → NormalProto′ T
  → NormalProto′ (T ⋯ ρ)

ren-pres-normalProto :
  ∀ {Δ Δ′} {T : Ty Δ KP} (ρ : Δ →ᵣ Δ′)
  → NormalProto T
  → NormalProto (T ⋯ ρ)

ren-pres-normalTy :
  ∀ {Δ Δ′ pk m} {T : Ty Δ (KV pk m)} (ρ : Δ →ᵣ Δ′)
  → NormalTy T
  → NormalTy (T ⋯ ρ)

ren-pres-normalProto ρ (N-Normal NP) = N-Normal (ren-pres-normalProto′ ρ NP)
ren-pres-normalProto ρ (N-Minus NP) = N-Minus (ren-pres-normalProto′ ρ NP)

ren-pres-normalProto′ ρ (N-ProtoP #c ⊙ NP) = N-ProtoP #c ⊙ (ren-pres-normalProto ρ NP)
ren-pres-normalProto′ ρ (N-Up NT) = N-Up (ren-pres-normalTy ρ NT)
ren-pres-normalProto′ ρ N-Var = N-Var

ren-pres-normalTy ρ (N-Var NV) = N-Var (ren-pres-normalVar ρ NV)
ren-pres-normalTy ρ N-Base = N-Base
ren-pres-normalTy ρ (N-Arrow km N₁ N₂) = N-Arrow km (ren-pres-normalTy ρ N₁) (ren-pres-normalTy ρ N₂)
ren-pres-normalTy ρ (N-Pair N₁ N₂) = N-Pair (ren-pres-normalTy ρ N₁) (ren-pres-normalTy ρ N₂)
ren-pres-normalTy ρ (N-Poly K′ N) = N-Poly K′ (ren-pres-normalTy (ρ ↑ᵣ _) N)
ren-pres-normalTy ρ (N-Sub km≤ N) = N-Sub km≤ (ren-pres-normalTy ρ N)
ren-pres-normalTy ρ N-End = N-End
ren-pres-normalTy ρ (N-Msg p NP NS) = N-Msg p (ren-pres-normalProto′ ρ NP) (ren-pres-normalTy ρ NS)
ren-pres-normalTy ρ (N-ProtoD N) = N-ProtoD (ren-pres-normalTy ρ N)

ren-pres-normal :
  ∀ {Δ Δ′ K} {T : Ty Δ K} (ρ : Δ →ᵣ Δ′)
  → Normal T
  → Normal (T ⋯ ρ)
ren-pres-normal {K = KV pk m} ρ N = ren-pres-normalTy ρ N
ren-pres-normal {K = KP} ρ N = ren-pres-normalProto ρ N

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
linArrNf (mkNfTy T NT) (mkNfTy U NU) = mkNfTy (LinArr T U) (N-Arrow (≤p-step <p-mt) NT NU)

pairNf : ∀ {pk₁ pk₂ m}
  → NfTy Δ (KV pk₁ m)
  → NfTy Δ (KV pk₂ m)
  → NfTy Δ (KV KT m)
pairNf (mkNfTy T NT) (mkNfTy U NU) = mkNfTy (T-Pair T U) (N-Pair NT NU)

polyNf : NfTy (K ∷ Δ) (KV KT m) → NfTy Δ (KV KT m)
polyNf {K = K} (mkNfTy T NT) = mkNfTy (T-Poly K T) (N-Poly K NT)

UnitLin : Ty Δ TLin
UnitLin = T-Base

SessLin : Ty Δ SLin → Ty Δ TLin
SessLin = T-Sub (≤k-step (≤p-step <p-st) ≤m-refl)

EndLin : Ty Δ TLin
EndLin = T-Sub (≤k-step (≤p-step <p-st) ≤m-unl) T-End

CloseTy : Ty Δ TLin
CloseTy = LinArr EndLin UnitLin

ForkTy : Ty Δ TLin
ForkTy = LinArr (LinArr UnitLin UnitLin) UnitLin

NewTy : Ty Δ TLin
NewTy = T-Poly SLin
  (T-Pair (SessLin (T-Var (here refl)))
          (SessLin (T-Dual D-S (T-Var (here refl)))))

wkTy : ∀ {K K′} → Ty Δ K → Ty (K′ ∷ Δ) K
wkTy {K′ = K′} T = T ⋯ weakenᵣ K′

ReceiveTy : Ty Δ TLin → Ty Δ SLin → Ty Δ TLin
ReceiveTy T S = LinArr
  (SessLin (T-Msg ⊝ (T-Up T) S))
  (T-Pair T (SessLin S))

ReceiveTy1 : Ty Δ TLin → Ty Δ TLin
ReceiveTy1 T = T-Poly SLin
  (ReceiveTy (wkTy {K′ = SLin} T) (T-Var (here refl)))

SendTy : Ty Δ TLin → Ty Δ SLin → Ty Δ TLin
SendTy T S = LinArr T
  (LinArr (SessLin (T-Msg ⊕ (T-Up T) S)) (SessLin S))

SendTy1 : Ty Δ TLin → Ty Δ TLin
SendTy1 T = T-Poly SLin
  (SendTy (wkTy {K′ = SLin} T) (T-Var (here refl)))

postulate
  MatchBranches : ∀ {Δ k} → NfTy Δ SLin → (Fin k → NfTy Δ SLin) → Set

data BranchJoin {Δ} : ∀ {k} → (Fin (suc k) → NfTy Δ TLin) → NfTy Δ TLin → Set where
  BJ-one : ∀ {T}
    → BranchJoin {k = 0} (λ { zero → T }) T

  BJ-step : ∀ {k} {V : Fin (suc (suc k)) → NfTy Δ TLin} {U W : NfTy Δ TLin}
      {<:₁ : normalTyOf (V zero) <:ₜ normalTyOf W}
      {<:₂ : normalTyOf U <:ₜ normalTyOf W}
    → BranchJoin (λ i → V (suc i)) U
    → joinₜ (normalTyOf (V zero)) (normalTyOf U) ≡ yes (⌞ W ⌟ , normalTyOf W , <:₁ , <:₂)
    → BranchJoin V W

branchJoin-subtype :
  ∀ {Δ k} {V : Fin (suc k) → NfTy Δ TLin} {U : NfTy Δ TLin} (i : Fin (suc k))
  → BranchJoin V U
  → normalTyOf (V i) <:ₜ normalTyOf U
branchJoin-subtype zero (BJ-one {T = T}) = <:ₜ-refl (normalTyOf T)
branchJoin-subtype zero (BJ-step {<:₁ = <:₁} _ _) = <:₁
branchJoin-subtype (suc i) (BJ-step {<:₂ = <:₂} bj _) = <:ₜ-trans (branchJoin-subtype i bj) <:₂

data ConstTy {Δ} : Const → ∀ {K} → NfTy Δ K → Set where
  CT-Unit : ConstTy C-Unit (normalizeTy T-Base)
  CT-Fork : ConstTy C-Fork (normalizeTy ForkTy)
  CT-New  : ConstTy C-New (normalizeTy NewTy)
  CT-Receive : ConstTy C-Receive
    (normalizeTy (T-Poly TLin (ReceiveTy1 (T-Var (here refl)))))
  CT-Send : ConstTy C-Send
    (normalizeTy (T-Poly TLin (SendTy1 (T-Var (here refl)))))
  CT-Close : ConstTy C-Close (normalizeTy CloseTy)
  CT-Select : ∀ {k} {v : Variance} {i : Fin k}
    → ConstTy (C-Select v i) (normalizeTy (SelectConstTy v i))

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

    TV-Rec : ∀ {n} {Γ₁ : Ctx Δ n} {T U : Ty Δ TLin} {v : Value Δ (suc n)}
      → (linArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)
          ⊢ E-Val v ⇐ linArrNf (normalizeTy T) (normalizeTy U)
          ⊣ (linArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)
      → Γ₁ ⊢ᵥ V-Rec T U v ⇒ linArrNf (normalizeTy T) (normalizeTy U) ⊣ Γ₁

    TV-TAbs : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {K m}
        {v : Value (K ∷ Δ) n} {T : NfTy (K ∷ Δ) (KV KT m)}
      → wkCtx {K = K} Γ₁ ⊢ᵥ v ⇒ T ⊣ wkCtx Γ₂
      → Γ₁ ⊢ᵥ V-TAbs K v ⇒ polyNf T ⊣ Γ₂

    TV-Pair : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {v₁ v₂ : Value Δ n}
        {pk₁ pk₂ m}
        {T : NfTy Δ (KV pk₁ m)} {U : NfTy Δ (KV pk₂ m)}
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
      → Γ₁ ⊢ E-Val v ⇐ normalizeTy T ⊣ Γ₂
      → Γ₁ ⊢ᵥ V-Send₃ T S v ⇒ normalizeTy (LinArr (SessLin (T-Msg ⊕ (T-Up T) S)) (SessLin S)) ⊣ Γ₂

    TV-Select₁ : ∀ {n} {Γ₁ : Ctx Δ n} {k} {v : Variance} {i : Fin k} {P : Ty Δ KP}
      → Γ₁ ⊢ᵥ V-Select₁ v i P ⇒ normalizeTy (SelectTy1 v i P) ⊣ Γ₁

    TV-Select₂ : ∀ {n} {Γ₁ : Ctx Δ n} {k} {v : Variance} {i : Fin k} {P : Ty Δ KP} {S : Ty Δ SLin}
      → Γ₁ ⊢ᵥ V-Select₂ v i P S ⇒ normalizeTy (SelectTy2 v i P S) ⊣ Γ₁

  data _⊢_⇒_⊣_ {Δ} : ∀ {n} → (Γ₁ : Ctx Δ n) → Expr Δ n → ∀ {K} → NfTy Δ K → Ctx Δ n → Set where
    T-Val : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {v : Value Δ n} {K} {T : NfTy Δ K}
      → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
      → Γ₁ ⊢ E-Val v ⇒ T ⊣ Γ₂

    T-Pair : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n}
        {pk₁ pk₂ m}
        {T : NfTy Δ (KV pk₁ m)} {U : NfTy Δ (KV pk₂ m)}
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

    T-LetPair : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {pk₁ pk₂}
        {T : NfTy Δ (KV pk₁ Lin)} {U : NfTy Δ (KV pk₂ Lin)} {V : NfTy Δ TLin}
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
      (W ≡ linArrNf (normalizeTy T) U) × ((normalizeTy T ∷ˡ Γ₁) ⊢ e ⇒ U ⊣ used∷ Γ₂)
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

postulate
  pair-inversion′ :
    ∀ {Δ n pk₁ pk₂ m} {Γ₁ Γ₃ : Ctx Δ n} {u v : Value Δ n}
      {T : NfTy Δ (KV pk₁ m)} {U : NfTy Δ (KV pk₂ m)}
    → Γ₁ ⊢ᵥ V-Pair u v ⇒ pairNf T U ⊣ Γ₃
    → Σ (Ctx Δ n) λ Γ₂ →
        (Γ₁ ⊢ᵥ u ⇒ T ⊣ Γ₂) × (Γ₂ ⊢ᵥ v ⇒ U ⊣ Γ₃)

postulate
  pair-expr-inversion :
    ∀ {Δ n pk₁ pk₂ m} {Γ₁ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n}
      {T : NfTy Δ (KV pk₁ m)} {U : NfTy Δ (KV pk₂ m)}
    → Γ₁ ⊢ E-Pair e₁ e₂ ⇒ pairNf T U ⊣ Γ₃
    → Σ (Ctx Δ n) λ Γ₂ →
        (Γ₁ ⊢ e₁ ⇒ T ⊣ Γ₂) × (Γ₂ ⊢ e₂ ⇒ U ⊣ Γ₃)

pair-injective :
  ∀ {Δ pk₁ pk₂ m} {T₁ T₂ : Ty Δ (KV pk₁ m)} {U₁ U₂ : Ty Δ (KV pk₂ m)}
  → T-Pair T₁ U₁ ≡ T-Pair T₂ U₂
  → (T₁ ≡ T₂) × (U₁ ≡ U₂)
pair-injective refl = refl , refl

nfTyEq :
  ∀ {Δ pk m} {T₁ T₂ : Ty Δ (KV pk m)}
    (eq : T₁ ≡ T₂) (N₁ : NormalTy T₁) (N₂ : NormalTy T₂)
  → mkNfTy T₁ N₁ ≡ mkNfTy T₂ N₂
nfTyEq refl N₁ N₂ = cong (mkNfTy _) (nt-unique N₁ N₂)

nfEq :
  ∀ {Δ K} {T₁ T₂ : Ty Δ K}
    (eq : T₁ ≡ T₂) (N₁ : Normal T₁) (N₂ : Normal T₂)
  → mkNfTy T₁ N₁ ≡ mkNfTy T₂ N₂
nfEq {K = KV pk m} eq N₁ N₂ = nfTyEq eq N₁ N₂
nfEq {K = KP} refl N₁ N₂ = cong (mkNfTy _) (np-unique N₁ N₂)

normalizeTy-id :
  ∀ {Δ K} {T : Ty Δ K}
  → (N : Normal T)
  → normalizeTy T ≡ mkNfTy T N
normalizeTy-id {K = KV pk m} {T = T} N =
  nfEq (Types.nf-idempotent N) (Types.nf-normal-type ⊕ d?⊥ T) N
normalizeTy-id {K = KP} {T = T} N =
  nfEq (Types.nfp-idempotent N) (Types.nf-normal-proto T) N

wkNfTy-injective :
  ∀ {Δ K K′} {T U : NfTy Δ K}
  → wkNfTy {K′ = K′} T ≡ wkNfTy {K′ = K′} U
  → T ≡ U
wkNfTy-injective {K′ = K′} {T = mkNfTy T NT} {U = mkNfTy U NU} eq
  rewrite normalizeTy-id {T = T ⋯ weakenᵣ K′} (ren-pres-normal (weakenᵣ K′) NT)
        | normalizeTy-id {T = U ⋯ weakenᵣ K′} (ren-pres-normal (weakenᵣ K′) NU)
  = nfEq
      (renaming-injective (weakenᵣ K′) weakenᵣ-injective (cong ⌞_⌟ eq))
      NT
      NU

linBinding-injective :
  ∀ {Δ K K′} {T : NfTy Δ K} {U : NfTy Δ K′}
  → B-Lin T ≡ B-Lin U
  → Σ (K ≡ K′) λ where
      refl → T ≡ U
linBinding-injective refl = refl , refl

unBinding-injective :
  ∀ {Δ K K′} {T : NfTy Δ K} {U : NfTy Δ K′}
  → B-Un T ≡ B-Un U
  → Σ (K ≡ K′) λ where
      refl → T ≡ U
unBinding-injective refl = refl , refl

wkBinding-injective :
  ∀ {Δ K} {b₁ b₂ : Binding Δ}
  → wkBinding {K = K} b₁ ≡ wkBinding {K = K} b₂
  → b₁ ≡ b₂
wkBinding-injective {K = K} {b₁ = B-Lin T} {b₂ = B-Lin U} eq
  with linBinding-injective eq
... | refl , eq′
  = cong B-Lin (wkNfTy-injective {K′ = K} eq′)
wkBinding-injective {K = K} {b₁ = B-Un T} {b₂ = B-Un U} eq
  with unBinding-injective eq
... | refl , eq′
  = cong B-Un (wkNfTy-injective {K′ = K} eq′)
wkBinding-injective {b₁ = B-Used} {b₂ = B-Used} refl = refl
wkBinding-injective {b₁ = B-Lin T} {b₂ = B-Un U} ()
wkBinding-injective {b₁ = B-Lin T} {b₂ = B-Used} ()
wkBinding-injective {b₁ = B-Un T} {b₂ = B-Lin U} ()
wkBinding-injective {b₁ = B-Un T} {b₂ = B-Used} ()
wkBinding-injective {b₁ = B-Used} {b₂ = B-Lin U} ()
wkBinding-injective {b₁ = B-Used} {b₂ = B-Un U} ()

wkCtx-injective :
  ∀ {Δ n K} {Γ₁ Γ₂ : Ctx Δ n}
  → wkCtx {K = K} Γ₁ ≡ wkCtx {K = K} Γ₂
  → Γ₁ ≡ Γ₂
wkCtx-injective {Γ₁ = ∅} {Γ₂ = ∅} refl = refl
wkCtx-injective {Γ₁ = b₁ ▻ Γ₁} {Γ₂ = b₂ ▻ Γ₂} eq
  with wkBinding-injective (cong (λ where (b ▻ _) → b) eq)
     | wkCtx-injective (cong (λ where (_ ▻ Γ) → Γ) eq)
... | refl | refl = refl

pairNf-injective :
  ∀ {Δ pk₁ pk₂ m} {T₁ T₂ : NfTy Δ (KV pk₁ m)} {U₁ U₂ : NfTy Δ (KV pk₂ m)}
  → pairNf T₁ U₁ ≡ pairNf T₂ U₂
  → (T₁ ≡ T₂) × (U₁ ≡ U₂)
pairNf-injective
  {T₁ = mkNfTy T₁ NT₁} {T₂ = mkNfTy T₂ NT₂}
  {U₁ = mkNfTy U₁ NU₁} {U₂ = mkNfTy U₂ NU₂} eq
  with pair-injective (cong ⌞_⌟ eq)
... | eqT , eqU = nfTyEq eqT NT₁ NT₂ , nfTyEq eqU NU₁ NU₂

rec-inversion :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n} {T U : Ty Δ TLin} {v : Value Δ (suc n)} {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ V-Rec T U v ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) ×
    ((W ≡ linArrNf (normalizeTy T) (normalizeTy U)) ×
     ((linArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)
       ⊢ E-Val v ⇐ linArrNf (normalizeTy T) (normalizeTy U)
       ⊣ (linArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)))
rec-inversion (TV-Rec p) = refl , refl , p

receive₂-inversion :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n} {T : Ty Δ TLin} {S : Ty Δ SLin} {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ V-Receive₂ T S ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ normalizeTy (ReceiveTy T S))
receive₂-inversion TV-Receive₂ = refl , refl

linArrNf-injective :
  ∀ {Δ} {T₁ T₂ U₁ U₂ : NfTy Δ TLin}
  → linArrNf T₁ U₁ ≡ linArrNf T₂ U₂
  → (T₁ ≡ T₂) × (U₁ ≡ U₂)
linArr-injective :
  ∀ {Δ} {T₁ T₂ U₁ U₂ : Ty Δ TLin}
  → LinArr T₁ U₁ ≡ LinArr T₂ U₂
  → (T₁ ≡ T₂) × (U₁ ≡ U₂)
linArr-injective refl = refl , refl

linArrNf-injective
  {T₁ = mkNfTy T₁ NT₁} {T₂ = mkNfTy T₂ NT₂}
  {U₁ = mkNfTy U₁ NU₁} {U₂ = mkNfTy U₂ NU₂} eq
  with linArr-injective (cong ⌞_⌟ eq)
... | eqT , eqU = nfTyEq eqT NT₁ NT₂ , nfTyEq eqU NU₁ NU₂

polyNf-injective :
  ∀ {Δ K m} {T₁ T₂ : NfTy (K ∷ Δ) (KV KT m)}
  → polyNf T₁ ≡ polyNf T₂
  → T₁ ≡ T₂
tpoly-injective :
  ∀ {Δ K m} {T₁ T₂ : Ty (K ∷ Δ) (KV KT m)}
  → T-Poly K T₁ ≡ T-Poly K T₂
  → T₁ ≡ T₂
tpoly-injective refl = refl

polyNf-injective {T₁ = mkNfTy T₁ N₁} {T₂ = mkNfTy T₂ N₂} eq
  with cong ⌞_⌟ eq
... | eq′ = nfTyEq (tpoly-injective eq′) N₁ N₂
