module NormalTypesSubstitution where

open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (const)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)

open import Util
open import Kinds
open import Kits
open import Duality
open import Types using (Ty; Ty-Syntax; Ty-Traversal; nf; t-minus; t-msg)
open import NormalTypes
open import NormalTypesRenamings
import Types

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (⋯-id)

NFKind : List Kind → Kind → Set
NFKind Δ KP = NFProto Δ
NFKind Δ (KV pk m) = NFTy Δ (KV pk m)

nfKindTy : NFKind Δ K → Ty Δ K
nfKindTy {K = KP} = nfProtoTy
nfKindTy {K = KV pk m} = nfTyTy

wkNFKind : ∀ {K K′} → NFKind Δ K → NFKind (K′ ∷ Δ) K
wkNFKind {K = KP} = wkNFProto
wkNFKind {K = KV pk m} = wkNFTy

wkNFKind-sound :
  ∀ {K K′} (N : NFKind Δ K)
  → nfKindTy (wkNFKind {K′ = K′} N) ≡ nfKindTy N ⋯ weakenᵣ K′
wkNFKind-sound {K = KP} {K′ = K′} N =
  renNFProto-sound (weakenᵣ K′) N
wkNFKind-sound {K = KV pk m} {K′ = K′} N =
  renNFTy-sound (weakenᵣ K′) N

nfVarKind : ∀ {K} → K ∈ Δ → NFKind Δ K
nfVarKind {K = KP} x = N-Normal (N-Var x)
nfVarKind {K = KV pk m} x = N-Var (NV-Var x)

nfVarKind-sound :
  ∀ {K} (x : K ∈ Δ)
  → nfKindTy (nfVarKind x) ≡ Types.T-Var x
nfVarKind-sound {K = KP} x = refl
nfVarKind-sound {K = KV pk m} x = refl

nfKind-idempotent :
  ∀ {K} (N : NFKind Δ K)
  → nf ⊕ d?⊥ (nfKindTy N) ≡ nfKindTy N
nfKind-idempotent {K = KP} N =
  Types.nfp-idempotent (toNormalProto N)
nfKind-idempotent {K = KV pk m} N =
  Types.nf-idempotent (toNormalTy N)

minusNF : NFProto Δ → NFProto Δ
minusNF (N-Normal N) = N-Minus N
minusNF (N-Minus N) = N-Normal N

minusNF-sound :
  (N : NFProto Δ)
  → nfProtoTy (minusNF N) ≡ t-minus (nfProtoTy N)
minusNF-sound (N-Normal (N-ProtoP #c ⊙ N)) = refl
minusNF-sound (N-Normal (N-Up N)) = refl
minusNF-sound (N-Normal (N-Var x)) = refl
minusNF-sound (N-Minus (N-ProtoP #c ⊙ N)) = refl
minusNF-sound (N-Minus (N-Up N)) = refl
minusNF-sound (N-Minus (N-Var x)) = refl

msgNF : (p : Polarity) → NFProto Δ → NFTy Δ SLin → NFTy Δ SLin
msgNF p (N-Normal N) S = N-Msg p N S
msgNF p (N-Minus N) S = N-Msg (invert p) N S

msgNF-sound :
  (p : Polarity) (P : NFProto Δ) (S : NFTy Δ SLin)
  → nfTyTy (msgNF p P S) ≡ t-msg p (nfProtoTy P) (nfTyTy S)
msgNF-sound p (N-Normal (N-ProtoP #c ⊙ N)) S = refl
msgNF-sound p (N-Normal (N-Up N)) S = refl
msgNF-sound p (N-Normal (N-Var x)) S = refl
msgNF-sound p (N-Minus (N-ProtoP #c ⊙ N)) S = refl
msgNF-sound p (N-Minus (N-Up N)) S = refl
msgNF-sound p (N-Minus (N-Var x)) S = refl

dualNFKind : ∀ {K} → Dualizable K → NFKind Δ K → NFKind Δ K
dualNFKind {K = KV pk m} d N = nf-normal-type ⊝ (const d) (nfTyTy N)

dualNFKind-sound :
  ∀ {K} (d : Dualizable K) (N : NFKind Δ K)
  → nfKindTy (dualNFKind d N) ≡ nf ⊕ d?⊥ (Types.T-Dual d (nfKindTy N))
dualNFKind-sound {K = KV pk m} d N =
  nfTyTy-fromNormalTy (Types.nf-normal-type ⊝ (const d) (nfTyTy N))

dualNFKind-involutive :
  (S : NFTy Δ SLin)
  → dualNFKind D-S (dualNFKind D-S S) ≡ S
dualNFKind-involutive S =
  nfTyTy-injective
    (trans
      (dualNFKind-sound D-S (dualNFKind D-S S))
      (trans
        (cong
          (λ U → Types.nf ⊕ d?⊥ (Types.T-Dual D-S U))
          (dualNFKind-sound D-S S))
        (trans
          (Types.nf-complete-
            (λ _ → D-S)
            (Types.nf-sound+ {f = d?⊥}
              (Types.T-Dual D-S (nfTyTy S))))
          (trans
            (Types.nf-⊕-ignores
              {T = nfTyTy S}
              (λ _ → D-S)
              d?⊥)
            (nfKind-idempotent S)))))

NFSub : List Kind → List Kind → Set
NFSub Δ₁ Δ₂ = ∀ K → K ∈ Δ₁ → NFKind Δ₂ K

nfSubTy : NFSub Δ₁ Δ₂ → Δ₁ →ₛ Δ₂
nfSubTy σ K x = nfKindTy (σ K x)

wkNFSub : ∀ {K} → NFSub Δ₁ Δ₂ → NFSub (K ∷ Δ₁) (K ∷ Δ₂)
wkNFSub {K = K′} σ K (here refl) = nfVarKind (here refl)
wkNFSub {K = K′} σ K (there x) = wkNFKind {K′ = K′} (σ K x)

wkNFSub-sound :
  ∀ {K} (σ : NFSub Δ₁ Δ₂)
  → nfSubTy (wkNFSub {K = K} σ) ~ (nfSubTy σ ↑ₛ K)
wkNFSub-sound {K = K′} σ .K′ (here refl) = nfVarKind-sound (here refl)
wkNFSub-sound {K = K′} σ K (there x) = wkNFKind-sound {K′ = K′} (σ K x)

singleNFSub : ∀ {K} → NFKind Δ K → NFSub (K ∷ Δ) Δ
singleNFSub {K = K′} U .K′ (here refl) = U
singleNFSub {K = K′} U K (there x) = nfVarKind x

singleNFSub-sound :
  ∀ {K} (U : NFKind Δ K)
  → nfSubTy (singleNFSub U) ~ ⦅ nfKindTy U ⦆ₛ
singleNFSub-sound {K = K′} U .K′ (here refl) = refl
singleNFSub-sound {K = K′} U K (there x) = nfVarKind-sound x

mutual

  substNFProto′With : NFSub Δ₁ Δ₂ → NFProto′ Δ₁ → NFProto Δ₂
  substNFProtoWith : NFSub Δ₁ Δ₂ → NFProto Δ₁ → NFProto Δ₂
  substNFVarWith : ∀ {K} → NFSub Δ₁ Δ₂ → NFVar Δ₁ K → NFKind Δ₂ K
  substNFTyWith : ∀ {K} → NFSub Δ₁ Δ₂ → NFTy Δ₁ K → NFTy Δ₂ K

  substNFProto′With σ (N-ProtoP #c ⊙ N) = N-Normal (N-ProtoP #c ⊙ (substNFProtoWith σ N))
  substNFProto′With σ (N-Up N) = N-Normal (N-Up (substNFTyWith σ N))
  substNFProto′With σ (N-Var x) = σ KP x

  substNFProtoWith σ (N-Normal N) = substNFProto′With σ N
  substNFProtoWith σ (N-Minus N) = minusNF (substNFProto′With σ N)

  substNFVarWith σ (NV-Var x) = σ _ x
  substNFVarWith σ (NV-Dual d x) = dualNFKind d (σ _ x)

  substNFTyWith σ (N-Var N) = substNFVarWith σ N
  substNFTyWith σ N-Base = N-Base
  substNFTyWith σ (N-Arrow N₁ N₂) = N-Arrow (substNFTyWith σ N₁) (substNFTyWith σ N₂)
  substNFTyWith σ (N-Pair N₁ N₂) = N-Pair (substNFTyWith σ N₁) (substNFTyWith σ N₂)
  substNFTyWith σ (N-Poly K′ N) = N-Poly K′ (substNFTyWith (wkNFSub {K = K′} σ) N)
  substNFTyWith σ (N-Sub km≤ N) = N-Sub km≤ (substNFTyWith σ N)
  substNFTyWith σ N-End = N-End
  substNFTyWith σ (N-Msg p P S) = msgNF p (substNFProto′With σ P) (substNFTyWith σ S)
  substNFTyWith σ (N-ProtoD N) = N-ProtoD (substNFTyWith σ N)

substNFProto′ : ∀ {K} → NFProto′ (K ∷ Δ) → NFKind Δ K → NFProto Δ
substNFProto′ N U = substNFProto′With (singleNFSub U) N

substNFProto : ∀ {K} → NFProto (K ∷ Δ) → NFKind Δ K → NFProto Δ
substNFProto N U = substNFProtoWith (singleNFSub U) N

substNFVar : ∀ {K K′} → NFVar (K ∷ Δ) K′ → NFKind Δ K → NFKind Δ K′
substNFVar N U = substNFVarWith (singleNFSub U) N

substNFTy : ∀ {K K′} → NFTy (K ∷ Δ) K′ → NFKind Δ K → NFTy Δ K′
substNFTy N U = substNFTyWith (singleNFSub U) N

mutual

  substNFProto′-sound :
    (σ : NFSub Δ₁ Δ₂) (N : NFProto′ Δ₁)
    → nfProtoTy (substNFProto′With σ N) ≡ nf ⊕ d?⊥ (nfProto′Ty N ⋯ nfSubTy σ)

  substNFProto-sound :
    (σ : NFSub Δ₁ Δ₂) (N : NFProto Δ₁)
    → nfProtoTy (substNFProtoWith σ N) ≡ nf ⊕ d?⊥ (nfProtoTy N ⋯ nfSubTy σ)

  substNFVar-sound :
    ∀ {K} (σ : NFSub Δ₁ Δ₂) (N : NFVar Δ₁ K)
    → nfKindTy (substNFVarWith σ N) ≡ nf ⊕ d?⊥ (nfVarTy N ⋯ nfSubTy σ)

  substNFTy-sound :
    ∀ {K} (σ : NFSub Δ₁ Δ₂) (N : NFTy Δ₁ K)
    → nfTyTy (substNFTyWith σ N) ≡ nf ⊕ d?⊥ (nfTyTy N ⋯ nfSubTy σ)

  substNFProto′-sound σ (N-ProtoP #c ⊙ N) =
    cong (λ T → Types.T-ProtoP #c ⊙ T) (substNFProto-sound σ N)
  substNFProto′-sound σ (N-Up N) =
    cong Types.T-Up (substNFTy-sound σ N)
  substNFProto′-sound σ (N-Var x) =
    sym (nfKind-idempotent (σ KP x))

  substNFProto-sound σ (N-Normal N) = substNFProto′-sound σ N
  substNFProto-sound σ (N-Minus N) =
    trans
      (minusNF-sound (substNFProto′With σ N))
      (cong t-minus (substNFProto′-sound σ N))

  substNFVar-sound σ (NV-Var x) =
    sym (nfKind-idempotent (σ _ x))
  substNFVar-sound σ (NV-Dual d x) =
    dualNFKind-sound d (σ _ x)

  substNFTy-sound σ (N-Var N) = substNFVar-sound σ N
  substNFTy-sound σ N-Base = refl
  substNFTy-sound σ (N-Arrow N₁ N₂) =
    cong₂ Types.T-Arrow (substNFTy-sound σ N₁) (substNFTy-sound σ N₂)
  substNFTy-sound σ (N-Pair N₁ N₂) =
    cong₂ Types.T-Pair (substNFTy-sound σ N₁) (substNFTy-sound σ N₂)
  substNFTy-sound σ (N-Poly K′ N) =
    cong (Types.T-Poly K′)
      (trans
        (substNFTy-sound (wkNFSub {K = K′} σ) N)
        (cong (nf ⊕ d?⊥)
          (⋯-cong (nfTyTy N) (wkNFSub-sound {K = K′} σ))))
  substNFTy-sound σ (N-Sub km≤ N) =
    cong (Types.T-Sub km≤)
      (trans
        (substNFTy-sound σ N)
        (cong (λ d? → nf ⊕ d? (nfTyTy N ⋯ nfSubTy σ))
          (sym (dual-all-irrelevant (λ x → dualizable-sub (d?⊥ x) km≤) d?⊥))))
  substNFTy-sound σ N-End = refl
  substNFTy-sound σ (N-Msg p P S) =
    trans
      (msgNF-sound p (substNFProto′With σ P) (substNFTyWith σ S))
      (cong₂ (t-msg p) (substNFProto′-sound σ P) (substNFTy-sound σ S))
  substNFTy-sound σ (N-ProtoD N) =
    cong Types.T-ProtoD (substNFTy-sound σ N)

substNFProto′-single-sound :
  ∀ {K} (N : NFProto′ (K ∷ Δ)) (U : NFKind Δ K)
  → nfProtoTy (substNFProto′ N U) ≡ nf ⊕ d?⊥ (nfProto′Ty N ⋯ ⦅ nfKindTy U ⦆ₛ)
substNFProto′-single-sound N U =
  trans
    (substNFProto′-sound (singleNFSub U) N)
    (cong (nf ⊕ d?⊥) (⋯-cong (nfProto′Ty N) (singleNFSub-sound U)))

substNFProto-single-sound :
  ∀ {K} (N : NFProto (K ∷ Δ)) (U : NFKind Δ K)
  → nfProtoTy (substNFProto N U) ≡ nf ⊕ d?⊥ (nfProtoTy N ⋯ ⦅ nfKindTy U ⦆ₛ)
substNFProto-single-sound N U =
  trans
    (substNFProto-sound (singleNFSub U) N)
    (cong (nf ⊕ d?⊥) (⋯-cong (nfProtoTy N) (singleNFSub-sound U)))

substNFTy-single-sound :
  ∀ {K K′} (N : NFTy (K ∷ Δ) K′) (U : NFKind Δ K)
  → nfTyTy (substNFTy N U) ≡ nf ⊕ d?⊥ (nfTyTy N ⋯ ⦅ nfKindTy U ⦆ₛ)
substNFTy-single-sound N U =
  trans
    (substNFTy-sound (singleNFSub U) N)
    (cong (nf ⊕ d?⊥) (⋯-cong (nfTyTy N) (singleNFSub-sound U)))
