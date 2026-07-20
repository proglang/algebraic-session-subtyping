module ExprSubstitution where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ) renaming (suc to sucℕ)
open import Data.Product using (Σ; _,_)

open import Kinds
open import Kits
open import Duality using (d?⊥; ⊕)
open import Types using (Ty; Ty-Syntax; Ty-Traversal)
open import NormalTypes using (nf-normal-proto; nf-normal-type)
open import NormalTypesRenamings using (renNFProto; renNFTy)
open import NormalTypesSubstitution
  using
  ( NFSub
  ; nfSubTy
  ; wkNFSub
  ; singleNFSub
  ; substNFProtoWith
  ; substNFTyWith
  )
open import ExprSyntax

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (⋯-id)

variable
  tn tm : ℕ
  Δ : List Kind

Ren : ∀ {tn tm} → Set
Ren {tn} {tm} = Fin tn → Fin tm

Sub : List Kind → ℕ → ℕ → Set
Sub Δ tn tm = Fin tn → Value Δ tm

extRen : ∀ {tn tm} → Ren {tn} {tm} → Ren {sucℕ tn} {sucℕ tm}
extRen ρ zero = zero
extRen ρ (suc x) = suc (ρ x)

extRen2 : ∀ {tn tm} → Ren {tn} {tm} → Ren {sucℕ (sucℕ tn)} {sucℕ (sucℕ tm)}
extRen2 ρ = extRen (extRen ρ)

renNfTy : ∀ {Δ Δ′ K} → (ϕ : Δ →ᵣ Δ′) → NfTy Δ K → NfTy Δ′ K
renNfTy {K = KP} ϕ T = renNFProto ϕ T
renNfTy {K = KV pk m} ϕ T = renNFTy ϕ T

toNFSub : ∀ {Δ Δ′} → (ϕ : Δ →ₛ Δ′) → NFSub Δ Δ′
toNFSub ϕ KP x = nf-normal-proto (ϕ KP x)
toNFSub ϕ (KV pk m) x = nf-normal-type ⊕ d?⊥ (ϕ (KV pk m) x)

substNfTyWith : ∀ {Δ Δ′ K} → (ϕ : Δ →ₛ Δ′) → NfTy Δ K → NfTy Δ′ K
substNfTyWith {K = KP} ϕ T = substNFProtoWith (toNFSub ϕ) T
substNfTyWith {K = KV pk m} ϕ T = substNFTyWith (toNFSub ϕ) T

substNFNfTyWith : ∀ {Δ Δ′ K} → NFSub Δ Δ′ → NfTy Δ K → NfTy Δ′ K
substNFNfTyWith {K = KP} = substNFProtoWith
substNFNfTyWith {K = KV pk m} = substNFTyWith

mutual

  renameValue : ∀ {Δ n m} → Ren {n} {m} → Value Δ n → Value Δ m
  renameValue ρ (V-Const c) = V-Const c
  renameValue ρ (V-Var x) = V-Var (ρ x)
  renameValue ρ (V-Abs T e) = V-Abs T (renameExpr (extRen ρ) e)
  renameValue ρ (V-Rec T U v) = V-Rec T U (renameValue (extRen ρ) v)
  renameValue ρ (V-TAbs K v) = V-TAbs K (renameValue ρ v)
  renameValue ρ (V-Pair v₁ v₂) = V-Pair (renameValue ρ v₁) (renameValue ρ v₂)
  renameValue ρ (V-Receive₁ T) = V-Receive₁ T
  renameValue ρ (V-Receive₂ T S) = V-Receive₂ T S
  renameValue ρ (V-Send₁ T) = V-Send₁ T
  renameValue ρ (V-Send₂ T S) = V-Send₂ T S
  renameValue ρ (V-Select₁ v i P) = V-Select₁ v i P
  renameValue ρ (V-Select₂ v i P S) = V-Select₂ v i P S

  renameExpr : ∀ {Δ n m} → Ren {n} {m} → Expr Δ n → Expr Δ m
  renameExpr ρ (E-Val v) = E-Val (renameValue ρ v)
  renameExpr ρ (E-App e₁ e₂) = E-App (renameExpr ρ e₁) (renameExpr ρ e₂)
  renameExpr ρ (E-TApp e T) = E-TApp (renameExpr ρ e) T
  renameExpr ρ (E-LetUnit e₁ e₂) = E-LetUnit (renameExpr ρ e₁) (renameExpr ρ e₂)
  renameExpr ρ (E-Pair e₁ e₂) = E-Pair (renameExpr ρ e₁) (renameExpr ρ e₂)
  renameExpr ρ (E-LetPair e₁ e₂) = E-LetPair (renameExpr ρ e₁) (renameExpr (extRen2 ρ) e₂)
  renameExpr ρ (E-Match e ne branches) =
    E-Match (renameExpr ρ e) ne (λ i i∈ → renameExpr (extRen ρ) (branches i i∈))

wkValue : ∀ {Δ n} → Value Δ n → Value Δ (sucℕ n)
wkValue = renameValue suc

mutual

  renTyArg : ∀ {Δ Δ′} → (ϕ : Δ →ᵣ Δ′) → TyArg Δ → TyArg Δ′
  renTyArg ϕ (K′ , T) = K′ , (T ⋯ ϕ)

  renTyArgs : ∀ {Δ Δ′} → (ϕ : Δ →ᵣ Δ′) → List (TyArg Δ) → List (TyArg Δ′)
  renTyArgs ϕ [] = []
  renTyArgs ϕ (a ∷ as) = renTyArg ϕ a ∷ renTyArgs ϕ as

  renTyValue : ∀ {Δ Δ′ n} → (ϕ : Δ →ᵣ Δ′) → Value Δ n → Value Δ′ n
  renTyValue ϕ (V-Const c) = V-Const c
  renTyValue ϕ (V-Var x) = V-Var x
  renTyValue ϕ (V-Abs T e) = V-Abs (renNfTy ϕ T) (renTyExpr ϕ e)
  renTyValue ϕ (V-Rec T U v) = V-Rec (renNfTy ϕ T) (renNfTy ϕ U) (renTyValue ϕ v)
  renTyValue ϕ (V-TAbs K v) = V-TAbs K (renTyValue (ϕ ↑ᵣ K) v)
  renTyValue ϕ (V-Pair v₁ v₂) = V-Pair (renTyValue ϕ v₁) (renTyValue ϕ v₂)
  renTyValue ϕ (V-Receive₁ T) = V-Receive₁ (renNfTy ϕ T)
  renTyValue ϕ (V-Receive₂ T S) = V-Receive₂ (renNfTy ϕ T) (renNfTy ϕ S)
  renTyValue ϕ (V-Send₁ T) = V-Send₁ (renNfTy ϕ T)
  renTyValue ϕ (V-Send₂ T S) = V-Send₂ (renNfTy ϕ T) (renNfTy ϕ S)
  renTyValue ϕ (V-Select₁ v i P) = V-Select₁ v i (renNfTy ϕ P)
  renTyValue ϕ (V-Select₂ v i P S) = V-Select₂ v i (renNfTy ϕ P) (renNfTy ϕ S)

  renTyExpr : ∀ {Δ Δ′ n} → (ϕ : Δ →ᵣ Δ′) → Expr Δ n → Expr Δ′ n
  renTyExpr ϕ (E-Val v) = E-Val (renTyValue ϕ v)
  renTyExpr ϕ (E-App e₁ e₂) = E-App (renTyExpr ϕ e₁) (renTyExpr ϕ e₂)
  renTyExpr ϕ (E-TApp e T) = E-TApp (renTyExpr ϕ e) (renNfTy ϕ T)
  renTyExpr ϕ (E-LetUnit e₁ e₂) = E-LetUnit (renTyExpr ϕ e₁) (renTyExpr ϕ e₂)
  renTyExpr ϕ (E-Pair e₁ e₂) = E-Pair (renTyExpr ϕ e₁) (renTyExpr ϕ e₂)
  renTyExpr ϕ (E-LetPair e₁ e₂) = E-LetPair (renTyExpr ϕ e₁) (renTyExpr ϕ e₂)
  renTyExpr ϕ (E-Match e ne branches) =
    E-Match (renTyExpr ϕ e) ne (λ i i∈ → renTyExpr ϕ (branches i i∈))

wkTyValue : ∀ {Δ n K} → Value Δ n → Value (K ∷ Δ) n
wkTyValue {K = K} = renTyValue (weakenᵣ K)

wkTyExpr : ∀ {Δ n K} → Expr Δ n → Expr (K ∷ Δ) n
wkTyExpr {K = K} = renTyExpr (weakenᵣ K)

extSub : ∀ {Δ n m} → Sub Δ n m → Sub Δ (sucℕ n) (sucℕ m)
extSub σ zero = V-Var zero
extSub σ (suc x) = wkValue (σ x)

extSub2 : ∀ {Δ n m} → Sub Δ n m → Sub Δ (sucℕ (sucℕ n)) (sucℕ (sucℕ m))
extSub2 σ = extSub (extSub σ)

doubleSub : ∀ {Δ n} → Value Δ n → Value Δ n → Sub Δ (sucℕ (sucℕ n)) n
doubleSub u v zero = u
doubleSub u v (suc zero) = v
doubleSub u v (suc (suc x)) = V-Var x

singleSub : ∀ {Δ n} → Value Δ n → Sub Δ (sucℕ n) n
singleSub v zero = v
singleSub v (suc x) = V-Var x

liftTySub : ∀ {Δ n m K} → Sub Δ n m → Sub (K ∷ Δ) n m
liftTySub σ x = wkTyValue (σ x)

mutual

  substValueWith : ∀ {Δ n m} → Sub Δ n m → Value Δ n → Value Δ m
  substValueWith σ (V-Const c) = V-Const c
  substValueWith σ (V-Var x) = σ x
  substValueWith σ (V-Abs T e) = V-Abs T (substExprWith (extSub σ) e)
  substValueWith σ (V-Rec T U v) = V-Rec T U (substValueWith (extSub σ) v)
  substValueWith σ (V-TAbs K v) = V-TAbs K (substValueWith (liftTySub σ) v)
  substValueWith σ (V-Pair v₁ v₂) = V-Pair (substValueWith σ v₁) (substValueWith σ v₂)
  substValueWith σ (V-Receive₁ T) = V-Receive₁ T
  substValueWith σ (V-Receive₂ T S) = V-Receive₂ T S
  substValueWith σ (V-Send₁ T) = V-Send₁ T
  substValueWith σ (V-Send₂ T S) = V-Send₂ T S
  substValueWith σ (V-Select₁ v i P) = V-Select₁ v i P
  substValueWith σ (V-Select₂ v i P S) = V-Select₂ v i P S

  substExprWith : ∀ {Δ n m} → Sub Δ n m → Expr Δ n → Expr Δ m
  substExprWith σ (E-Val v) = E-Val (substValueWith σ v)
  substExprWith σ (E-App e₁ e₂) = E-App (substExprWith σ e₁) (substExprWith σ e₂)
  substExprWith σ (E-TApp e T) = E-TApp (substExprWith σ e) T
  substExprWith σ (E-LetUnit e₁ e₂) = E-LetUnit (substExprWith σ e₁) (substExprWith σ e₂)
  substExprWith σ (E-Pair e₁ e₂) = E-Pair (substExprWith σ e₁) (substExprWith σ e₂)
  substExprWith σ (E-LetPair e₁ e₂) = E-LetPair (substExprWith σ e₁) (substExprWith (extSub2 σ) e₂)
  substExprWith σ (E-Match e ne branches) =
    E-Match (substExprWith σ e) ne (λ i i∈ → substExprWith (extSub σ) (branches i i∈))

substValue : ∀ {Δ n} → Value Δ (sucℕ n) → Value Δ n → Value Δ n
substValue v u = substValueWith (singleSub u) v

substExpr : ∀ {Δ n} → Expr Δ (sucℕ n) → Value Δ n → Expr Δ n
substExpr e v = substExprWith (singleSub v) e

substExpr₂ : ∀ {Δ n} → Expr Δ (sucℕ (sucℕ n)) → Value Δ n → Value Δ n → Expr Δ n
substExpr₂ e u v = substExprWith (doubleSub u v) e

mutual

  substTyArgWith : ∀ {Δ Δ′} → (ϕ : Δ →ₛ Δ′) → TyArg Δ → TyArg Δ′
  substTyArgWith ϕ (K′ , T) = K′ , (T ⋯ ϕ)

  substTyArgsWith : ∀ {Δ Δ′} → (ϕ : Δ →ₛ Δ′) → List (TyArg Δ) → List (TyArg Δ′)
  substTyArgsWith ϕ [] = []
  substTyArgsWith ϕ (a ∷ as) = substTyArgWith ϕ a ∷ substTyArgsWith ϕ as

  substTyValueWith : ∀ {Δ Δ′ n} → (ϕ : Δ →ₛ Δ′) → Value Δ n → Value Δ′ n
  substTyValueWith ϕ (V-Const c) = V-Const c
  substTyValueWith ϕ (V-Var x) = V-Var x
  substTyValueWith ϕ (V-Abs T e) = V-Abs (substNfTyWith ϕ T) (substTyExprWith ϕ e)
  substTyValueWith ϕ (V-Rec T U v) = V-Rec (substNfTyWith ϕ T) (substNfTyWith ϕ U) (substTyValueWith ϕ v)
  substTyValueWith ϕ (V-TAbs K v) = V-TAbs K (substTyValueWith (ϕ ↑ₛ K) v)
  substTyValueWith ϕ (V-Pair v₁ v₂) = V-Pair (substTyValueWith ϕ v₁) (substTyValueWith ϕ v₂)
  substTyValueWith ϕ (V-Receive₁ T) = V-Receive₁ (substNfTyWith ϕ T)
  substTyValueWith ϕ (V-Receive₂ T S) = V-Receive₂ (substNfTyWith ϕ T) (substNfTyWith ϕ S)
  substTyValueWith ϕ (V-Send₁ T) = V-Send₁ (substNfTyWith ϕ T)
  substTyValueWith ϕ (V-Send₂ T S) = V-Send₂ (substNfTyWith ϕ T) (substNfTyWith ϕ S)
  substTyValueWith ϕ (V-Select₁ v i P) = V-Select₁ v i (substNfTyWith ϕ P)
  substTyValueWith ϕ (V-Select₂ v i P S) = V-Select₂ v i (substNfTyWith ϕ P) (substNfTyWith ϕ S)

  substTyExprWith : ∀ {Δ Δ′ n} → (ϕ : Δ →ₛ Δ′) → Expr Δ n → Expr Δ′ n
  substTyExprWith ϕ (E-Val v) = E-Val (substTyValueWith ϕ v)
  substTyExprWith ϕ (E-App e₁ e₂) = E-App (substTyExprWith ϕ e₁) (substTyExprWith ϕ e₂)
  substTyExprWith ϕ (E-TApp e T) = E-TApp (substTyExprWith ϕ e) (substNfTyWith ϕ T)
  substTyExprWith ϕ (E-LetUnit e₁ e₂) = E-LetUnit (substTyExprWith ϕ e₁) (substTyExprWith ϕ e₂)
  substTyExprWith ϕ (E-Pair e₁ e₂) = E-Pair (substTyExprWith ϕ e₁) (substTyExprWith ϕ e₂)
  substTyExprWith ϕ (E-LetPair e₁ e₂) = E-LetPair (substTyExprWith ϕ e₁) (substTyExprWith ϕ e₂)
  substTyExprWith ϕ (E-Match e ne branches) =
    E-Match (substTyExprWith ϕ e) ne (λ i i∈ → substTyExprWith ϕ (branches i i∈))

-- Type substitution in the operational semantics starts with normal-form
-- arguments.  Keeping that substitution in the normal-form representation
-- avoids normalizing its images again at every annotation and, under a type
-- binder, uses the structural normal-form lift directly.
mutual

  substNFValueWith : ∀ {Δ Δ′ n} → NFSub Δ Δ′ → Value Δ n → Value Δ′ n
  substNFValueWith σ (V-Const c) = V-Const c
  substNFValueWith σ (V-Var x) = V-Var x
  substNFValueWith σ (V-Abs T e) =
    V-Abs (substNFTyWith σ T) (substNFExprWith σ e)
  substNFValueWith σ (V-Rec T U v) =
    V-Rec
      (substNFTyWith σ T)
      (substNFTyWith σ U)
      (substNFValueWith σ v)
  substNFValueWith σ (V-TAbs K v) =
    V-TAbs K (substNFValueWith (wkNFSub σ) v)
  substNFValueWith σ (V-Pair v₁ v₂) =
    V-Pair (substNFValueWith σ v₁) (substNFValueWith σ v₂)
  substNFValueWith σ (V-Receive₁ T) =
    V-Receive₁ (substNFTyWith σ T)
  substNFValueWith σ (V-Receive₂ T S) =
    V-Receive₂ (substNFTyWith σ T) (substNFTyWith σ S)
  substNFValueWith σ (V-Send₁ T) =
    V-Send₁ (substNFTyWith σ T)
  substNFValueWith σ (V-Send₂ T S) =
    V-Send₂ (substNFTyWith σ T) (substNFTyWith σ S)
  substNFValueWith σ (V-Select₁ v i P) =
    V-Select₁ v i (substNFProtoWith σ P)
  substNFValueWith σ (V-Select₂ v i P S) =
    V-Select₂ v i (substNFProtoWith σ P) (substNFTyWith σ S)

  substNFExprWith : ∀ {Δ Δ′ n} → NFSub Δ Δ′ → Expr Δ n → Expr Δ′ n
  substNFExprWith σ (E-Val v) = E-Val (substNFValueWith σ v)
  substNFExprWith σ (E-App e₁ e₂) =
    E-App (substNFExprWith σ e₁) (substNFExprWith σ e₂)
  substNFExprWith σ (E-TApp e T) =
    E-TApp (substNFExprWith σ e) (substNFNfTyWith σ T)
  substNFExprWith σ (E-LetUnit e₁ e₂) =
    E-LetUnit (substNFExprWith σ e₁) (substNFExprWith σ e₂)
  substNFExprWith σ (E-Pair e₁ e₂) =
    E-Pair (substNFExprWith σ e₁) (substNFExprWith σ e₂)
  substNFExprWith σ (E-LetPair e₁ e₂) =
    E-LetPair (substNFExprWith σ e₁) (substNFExprWith σ e₂)
  substNFExprWith σ (E-Match e ne branches) =
    E-Match
      (substNFExprWith σ e)
      ne
      (λ i i∈ → substNFExprWith σ (branches i i∈))

substTyValue : ∀ {Δ n K} → Value (K ∷ Δ) n → NfTy Δ K → Value Δ n
substTyValue v U = substTyValueWith (nfSubTy (singleNFSub U)) v

substTyExpr : ∀ {Δ n K} → Expr (K ∷ Δ) n → NfTy Δ K → Expr Δ n
substTyExpr e U = substTyExprWith (nfSubTy (singleNFSub U)) e
