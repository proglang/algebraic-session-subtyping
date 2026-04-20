module NormalTypes where

open import Data.Fin.Subset as Subset using ()
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Product using (_,_)
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)

open import Util
open import Kinds
open import Duality
open import Variance
open import TypesProperties using
  ( arrow-injective
  ; pair-injective
  ; poly-injective
  ; sub-injective
  ; dual-injective
  ; msg-injective
  ; up-injective
  ; minus-injective
  ; protoD-injective
  ; protoP-injective
  )
import Types
open Types using
  ( Ty
  ; T-Var
  ; T-Base
  ; T-Arrow
  ; T-Pair
  ; T-Poly
  ; T-Sub
  ; T-Dual
  ; T-End
  ; T-Msg
  ; T-Up
  ; T-Minus
  ; T-ProtoD
  ; T-ProtoP
  )

variable
  Δ : List Kind

mutual

  data NFProto′ (Δ : List Kind) : Set
  data NFProto (Δ : List Kind) : Set
  data NFVar (Δ : List Kind) (K : Kind) : Set
  data NFTy (Δ : List Kind) : Kind → Set

  data NFProto′ Δ where
    N-ProtoP : ∀ {k} → (#c : Subset.Subset k) → (⊙ : Variance) → NFProto Δ → NFProto′ Δ
    N-Up     : NFTy Δ (KV pk m) → NFProto′ Δ
    N-Var    : (x : KP ∈ Δ) → NFProto′ Δ

  data NFProto Δ where
    N-Normal : NFProto′ Δ → NFProto Δ
    N-Minus  : NFProto′ Δ → NFProto Δ

  data NFVar Δ K where
    NV-Var  : (x : K ∈ Δ) → NFVar Δ K
    NV-Dual : (d : Dualizable K) → (x : K ∈ Δ) → NFVar Δ K

  data NFTy Δ where
    N-Var    : NFVar Δ (KV pk m) → NFTy Δ (KV pk m)
    N-Base   : NFTy Δ TLin
    N-Arrow  : (km : KM ≤p pk) → NFTy Δ TLin → NFTy Δ TLin → NFTy Δ (KV pk m)
    N-Pair   : NFTy Δ (KV pk₁ m) → NFTy Δ (KV pk₂ m) → NFTy Δ (KV KT m)
    N-Poly   : (K′ : Kind) → NFTy (K′ ∷ Δ) (KV KT m) → NFTy Δ (KV KT m)
    N-Sub    : (km≤ : KV pk m ≤k KV pk′ m′) → NFTy Δ (KV pk m) → NFTy Δ (KV pk′ m′)
    N-End    : NFTy Δ SUn
    N-Msg    : (p : Polarity) → NFProto′ Δ → NFTy Δ SLin → NFTy Δ SLin
    N-ProtoD : NFTy Δ TLin → NFTy Δ TLin

mutual

  sizeₚ′ : NFProto′ Δ → ℕ
  sizeₚ : NFProto Δ → ℕ
  sizeₜ : NFTy Δ K → ℕ

  sizeₜ N = suc (case N of λ where
    (N-Var x) → zero
    N-Base → zero
    (N-Arrow _ N₁ N₂) → sizeₜ N₁ ⊔ sizeₜ N₂
    (N-Pair N₁ N₂) → sizeₜ N₁ ⊔ sizeₜ N₂
    (N-Poly _ N) → sizeₜ N
    (N-Sub _ N) → sizeₜ N
    N-End → zero
    (N-Msg p NP NS) → sizeₚ′ NP ⊔ sizeₜ NS
    (N-ProtoD N) → sizeₜ N)

  sizeₚ′ N = suc (case N of λ where
    (N-ProtoP _ _ N) → sizeₚ N
    (N-Up N) → sizeₜ N
    (N-Var x) → zero)

  sizeₚ N = suc (case N of λ where
    (N-Normal N) → sizeₚ′ N
    (N-Minus N) → sizeₚ′ N)

mutual

  nfProto′Ty : NFProto′ Δ → Ty Δ KP
  nfProto′Ty (N-ProtoP #c ⊙ N) = T-ProtoP #c ⊙ (nfProtoTy N)
  nfProto′Ty (N-Up N) = T-Up (nfTyTy N)
  nfProto′Ty (N-Var x) = T-Var x

  nfProtoTy : NFProto Δ → Ty Δ KP
  nfProtoTy (N-Normal N) = nfProto′Ty N
  nfProtoTy (N-Minus N) = T-Minus (nfProto′Ty N)

  nfVarTy : NFVar Δ K → Ty Δ K
  nfVarTy (NV-Var x) = T-Var x
  nfVarTy (NV-Dual d x) = T-Dual d (T-Var x)

  nfTyTy : NFTy Δ K → Ty Δ K
  nfTyTy (N-Var NV) = nfVarTy NV
  nfTyTy N-Base = T-Base
  nfTyTy (N-Arrow km N₁ N₂) = T-Arrow km (nfTyTy N₁) (nfTyTy N₂)
  nfTyTy (N-Pair N₁ N₂) = T-Pair (nfTyTy N₁) (nfTyTy N₂)
  nfTyTy (N-Poly K′ N) = T-Poly K′ (nfTyTy N)
  nfTyTy (N-Sub km≤ N) = T-Sub km≤ (nfTyTy N)
  nfTyTy N-End = T-End
  nfTyTy (N-Msg p NP NS) = T-Msg p (nfProto′Ty NP) (nfTyTy NS)
  nfTyTy (N-ProtoD N) = T-ProtoD (nfTyTy N)

mutual

  toNormalProto′ : (N : NFProto′ Δ) → Types.NormalProto′ (nfProto′Ty N)
  toNormalProto : (N : NFProto Δ) → Types.NormalProto (nfProtoTy N)
  toNormalVar : ∀ {K} → (N : NFVar Δ K) → Types.NormalVar (nfVarTy N)
  toNormalTy : ∀ {pk m} → (N : NFTy Δ (KV pk m)) → Types.NormalTy (nfTyTy N)

  toNormalProto′ (N-ProtoP #c ⊙ N) = Types.N-ProtoP #c ⊙ (toNormalProto N)
  toNormalProto′ (N-Up N) = Types.N-Up (toNormalTy N)
  toNormalProto′ (N-Var x) = Types.N-Var

  toNormalProto (N-Normal N) = Types.N-Normal (toNormalProto′ N)
  toNormalProto (N-Minus N) = Types.N-Minus (toNormalProto′ N)

  toNormalVar (NV-Var x) = Types.NV-Var
  toNormalVar (NV-Dual d x) = Types.NV-Dual d x

  toNormalTy (N-Var N) = Types.N-Var (toNormalVar N)
  toNormalTy N-Base = Types.N-Base
  toNormalTy (N-Arrow km N₁ N₂) = Types.N-Arrow km (toNormalTy N₁) (toNormalTy N₂)
  toNormalTy (N-Pair N₁ N₂) = Types.N-Pair (toNormalTy N₁) (toNormalTy N₂)
  toNormalTy (N-Poly K′ N) = Types.N-Poly K′ (toNormalTy N)
  toNormalTy (N-Sub km≤ N) = Types.N-Sub km≤ (toNormalTy N)
  toNormalTy N-End = Types.N-End
  toNormalTy (N-Msg p NP NS) = Types.N-Msg p (toNormalProto′ NP) (toNormalTy NS)
  toNormalTy (N-ProtoD N) = Types.N-ProtoD (toNormalTy N)

mutual

  sizeₚ′-toNormal : (N : NFProto′ Δ) → Types.sizeₚ′ (toNormalProto′ N) ≡ sizeₚ′ N
  sizeₚ-toNormal : (N : NFProto Δ) → Types.sizeₚ (toNormalProto N) ≡ sizeₚ N
  sizeₜ-toNormal : ∀ {pk m} (N : NFTy Δ (KV pk m)) → Types.sizeₜ (toNormalTy N) ≡ sizeₜ N

  sizeₜ-toNormal (N-Var x) = refl
  sizeₜ-toNormal N-Base = refl
  sizeₜ-toNormal (N-Arrow km N₁ N₂) =
    cong suc (cong₂ _⊔_ (sizeₜ-toNormal N₁) (sizeₜ-toNormal N₂))
  sizeₜ-toNormal (N-Pair N₁ N₂) =
    cong suc (cong₂ _⊔_ (sizeₜ-toNormal N₁) (sizeₜ-toNormal N₂))
  sizeₜ-toNormal (N-Poly K′ N) = cong suc (sizeₜ-toNormal N)
  sizeₜ-toNormal (N-Sub km≤ N) = cong suc (sizeₜ-toNormal N)
  sizeₜ-toNormal N-End = refl
  sizeₜ-toNormal (N-Msg p NP NS) =
    cong suc (cong₂ _⊔_ (sizeₚ′-toNormal NP) (sizeₜ-toNormal NS))
  sizeₜ-toNormal (N-ProtoD N) = cong suc (sizeₜ-toNormal N)

  sizeₚ′-toNormal (N-ProtoP #c ⊙ N) = cong suc (sizeₚ-toNormal N)
  sizeₚ′-toNormal (N-Up N) = cong suc (sizeₜ-toNormal N)
  sizeₚ′-toNormal (N-Var x) = refl

  sizeₚ-toNormal (N-Normal N) = cong suc (sizeₚ′-toNormal N)
  sizeₚ-toNormal (N-Minus N) = cong suc (sizeₚ′-toNormal N)

mutual

  fromNormalProto′ : ∀ {T : Ty Δ KP} → Types.NormalProto′ T → NFProto′ Δ
  fromNormalProto′ (Types.N-ProtoP #c ⊙ N) = N-ProtoP #c ⊙ (fromNormalProto N)
  fromNormalProto′ (Types.N-Up N) = N-Up (fromNormalTy N)
  fromNormalProto′ {T = T-Var x} Types.N-Var = N-Var x

  fromNormalProto : ∀ {T : Ty Δ KP} → Types.NormalProto T → NFProto Δ
  fromNormalProto (Types.N-Normal N) = N-Normal (fromNormalProto′ N)
  fromNormalProto (Types.N-Minus N) = N-Minus (fromNormalProto′ N)

  fromNormalVar : ∀ {T : Ty Δ K} → Types.NormalVar T → NFVar Δ K
  fromNormalVar {T = T-Var x} Types.NV-Var = NV-Var x
  fromNormalVar (Types.NV-Dual d x) = NV-Dual d x

  fromNormalTy : ∀ {pk m} {T : Ty Δ (KV pk m)} → Types.NormalTy T → NFTy Δ (KV pk m)
  fromNormalTy (Types.N-Var NV) = N-Var (fromNormalVar NV)
  fromNormalTy Types.N-Base = N-Base
  fromNormalTy (Types.N-Arrow km N₁ N₂) = N-Arrow km (fromNormalTy N₁) (fromNormalTy N₂)
  fromNormalTy (Types.N-Pair N₁ N₂) = N-Pair (fromNormalTy N₁) (fromNormalTy N₂)
  fromNormalTy (Types.N-Poly K′ N) = N-Poly K′ (fromNormalTy N)
  fromNormalTy (Types.N-Sub km≤ N) = N-Sub km≤ (fromNormalTy N)
  fromNormalTy Types.N-End = N-End
  fromNormalTy (Types.N-Msg p NP NS) = N-Msg p (fromNormalProto′ NP) (fromNormalTy NS)
  fromNormalTy (Types.N-ProtoD N) = N-ProtoD (fromNormalTy N)

nf-normal-proto : (T : Ty Δ KP) → NFProto Δ
nf-normal-proto T = fromNormalProto (Types.nf-normal-proto T)

nf-normal-proto-inverted : (T : Ty Δ KP) → NFProto Δ
nf-normal-proto-inverted T = fromNormalProto (Types.nf-normal-proto-inverted T)

nf-normal-type : ∀ ⊙ → (d? : ⊙ ≡ ⊝ → Dualizable (KV pk m)) → (T : Ty Δ (KV pk m)) → NFTy Δ (KV pk m)
nf-normal-type ⊙ d? T = fromNormalTy (Types.nf-normal-type ⊙ d? T)

mutual

  nfProto′Ty-fromNormalProto′ :
    ∀ {T : Ty Δ KP} (N : Types.NormalProto′ T)
    → nfProto′Ty (fromNormalProto′ N) ≡ T
  nfProto′Ty-fromNormalProto′ (Types.N-ProtoP #c ⊙ N) =
    cong (λ T → T-ProtoP #c ⊙ T) (nfProtoTy-fromNormalProto N)
  nfProto′Ty-fromNormalProto′ (Types.N-Up N) =
    cong T-Up (nfTyTy-fromNormalTy N)
  nfProto′Ty-fromNormalProto′ {T = T-Var x} Types.N-Var = refl

  nfProtoTy-fromNormalProto :
    ∀ {T : Ty Δ KP} (N : Types.NormalProto T)
    → nfProtoTy (fromNormalProto N) ≡ T
  nfProtoTy-fromNormalProto (Types.N-Normal N) =
    nfProto′Ty-fromNormalProto′ N
  nfProtoTy-fromNormalProto (Types.N-Minus N) =
    cong T-Minus (nfProto′Ty-fromNormalProto′ N)

  nfVarTy-fromNormalVar :
    ∀ {T : Ty Δ K} (N : Types.NormalVar T)
    → nfVarTy (fromNormalVar N) ≡ T
  nfVarTy-fromNormalVar {T = T-Var x} Types.NV-Var = refl
  nfVarTy-fromNormalVar (Types.NV-Dual d x) = refl

  nfTyTy-fromNormalTy :
    ∀ {pk m} {T : Ty Δ (KV pk m)} (N : Types.NormalTy T)
    → nfTyTy (fromNormalTy N) ≡ T
  nfTyTy-fromNormalTy (Types.N-Var NV) =
    nfVarTy-fromNormalVar NV
  nfTyTy-fromNormalTy Types.N-Base = refl
  nfTyTy-fromNormalTy (Types.N-Arrow km N₁ N₂) =
    cong₂ (T-Arrow km) (nfTyTy-fromNormalTy N₁) (nfTyTy-fromNormalTy N₂)
  nfTyTy-fromNormalTy (Types.N-Pair N₁ N₂) =
    cong₂ T-Pair (nfTyTy-fromNormalTy N₁) (nfTyTy-fromNormalTy N₂)
  nfTyTy-fromNormalTy (Types.N-Poly K′ N) =
    cong (T-Poly K′) (nfTyTy-fromNormalTy N)
  nfTyTy-fromNormalTy (Types.N-Sub km≤ N) =
    cong (T-Sub km≤) (nfTyTy-fromNormalTy N)
  nfTyTy-fromNormalTy Types.N-End = refl
  nfTyTy-fromNormalTy (Types.N-Msg p NP NS) =
    cong₂ (T-Msg p) (nfProto′Ty-fromNormalProto′ NP) (nfTyTy-fromNormalTy NS)
  nfTyTy-fromNormalTy (Types.N-ProtoD N) =
    cong T-ProtoD (nfTyTy-fromNormalTy N)

mutual

  nfVarTy-injective :
    ∀ {K} {N₁ N₂ : NFVar Δ K}
    → nfVarTy N₁ ≡ nfVarTy N₂
    → N₁ ≡ N₂
  nfVarTy-injective {N₁ = NV-Var x} {NV-Var y} eq =
    cong NV-Var (Types.t-var-injective eq)
  nfVarTy-injective {N₁ = NV-Dual d x} {NV-Dual d′ y} eq
    with dual-injective eq
  ... | refl , eq′ = cong (NV-Dual d) (Types.t-var-injective eq′)

  nfProto′Ty-injective :
    ∀ {N₁ N₂ : NFProto′ Δ}
    → nfProto′Ty N₁ ≡ nfProto′Ty N₂
    → N₁ ≡ N₂
  nfProto′Ty-injective {N₁ = N-ProtoP #c ⊙ N₁} {N-ProtoP #c′ ⊙′ N₂} eq
    with protoP-injective eq
  ... | refl , refl , refl , eq′ =
    cong (N-ProtoP #c ⊙) (nfProtoTy-injective eq′)
  nfProto′Ty-injective {N₁ = N-Up N₁} {N-Up N₂} eq
    with up-injective eq
  ... | refl , refl , eq′ = cong N-Up (nfTyTy-injective eq′)
  nfProto′Ty-injective {N₁ = N-Var x} {N-Var y} eq =
    cong N-Var (Types.t-var-injective eq)

  nfProtoTy-injective :
    ∀ {N₁ N₂ : NFProto Δ}
    → nfProtoTy N₁ ≡ nfProtoTy N₂
    → N₁ ≡ N₂
  nfProtoTy-injective {N₁ = N-Normal N₁} {N-Normal N₂} eq =
    cong N-Normal (nfProto′Ty-injective eq)
  nfProtoTy-injective {N₁ = N-Minus N₁} {N-Minus N₂} eq =
    cong N-Minus (nfProto′Ty-injective (minus-injective eq))
  nfProtoTy-injective {N₁ = N-Normal (N-ProtoP #c ⊙ N₁)} {N-Minus N₂} ()
  nfProtoTy-injective {N₁ = N-Normal (N-Up N₁)} {N-Minus N₂} ()
  nfProtoTy-injective {N₁ = N-Normal (N-Var x)} {N-Minus N₂} ()
  nfProtoTy-injective {N₁ = N-Minus N₁} {N-Normal (N-ProtoP #c ⊙ N₂)} ()
  nfProtoTy-injective {N₁ = N-Minus N₁} {N-Normal (N-Up N₂)} ()
  nfProtoTy-injective {N₁ = N-Minus N₁} {N-Normal (N-Var x)} ()

  nfTyTy-injective :
    ∀ {K} {N₁ N₂ : NFTy Δ K}
    → nfTyTy N₁ ≡ nfTyTy N₂
    → N₁ ≡ N₂
  nfTyTy-injective {N₁ = N-Var N₁} {N-Var N₂} eq =
    cong N-Var (nfVarTy-injective eq)
  nfTyTy-injective {N₁ = N-Var (NV-Var x)} {N-Base} ()
  nfTyTy-injective {N₁ = N-Var (NV-Dual d x)} {N-Base} ()
  nfTyTy-injective {N₁ = N-Var (NV-Var x)} {N-Arrow km N₂ N₃} ()
  nfTyTy-injective {N₁ = N-Var (NV-Dual d x)} {N-Arrow km N₂ N₃} ()
  nfTyTy-injective {N₁ = N-Var (NV-Var x)} {N-Pair N₂ N₃} ()
  nfTyTy-injective {N₁ = N-Var (NV-Dual d x)} {N-Pair N₂ N₃} ()
  nfTyTy-injective {N₁ = N-Var (NV-Var x)} {N-Poly K′ N₂} ()
  nfTyTy-injective {N₁ = N-Var (NV-Dual d x)} {N-Poly K′ N₂} ()
  nfTyTy-injective {N₁ = N-Var (NV-Var x)} {N-Sub km≤ N₂} ()
  nfTyTy-injective {N₁ = N-Var (NV-Dual d x)} {N-Sub km≤ N₂} ()
  nfTyTy-injective {N₁ = N-Var (NV-Var x)} {N-End} ()
  nfTyTy-injective {N₁ = N-Var (NV-Dual d x)} {N-End} ()
  nfTyTy-injective {N₁ = N-Var (NV-Var x)} {N-Msg p NP N₂} ()
  nfTyTy-injective {N₁ = N-Var (NV-Dual d x)} {N-Msg p NP N₂} ()
  nfTyTy-injective {N₁ = N-Var (NV-Var x)} {N-ProtoD N₂} ()
  nfTyTy-injective {N₁ = N-Var (NV-Dual d x)} {N-ProtoD N₂} ()
  nfTyTy-injective {N₁ = N-Base} {N-Base} refl = refl
  nfTyTy-injective {N₁ = N-Base} {N-Var (NV-Var x)} ()
  nfTyTy-injective {N₁ = N-Base} {N-Var (NV-Dual d x)} ()
  nfTyTy-injective {N₁ = N-Arrow km N₁ N₃} {N-Var (NV-Var x)} ()
  nfTyTy-injective {N₁ = N-Arrow km N₁ N₃} {N-Var (NV-Dual d x)} ()
  nfTyTy-injective {N₁ = N-Arrow km N₁ N₃} {N-Arrow km′ N₂ N₄} eq
    with arrow-injective eq
  ... | refl , eq₁ , eq₂ =
    cong₂ (N-Arrow km) (nfTyTy-injective eq₁) (nfTyTy-injective eq₂)
  nfTyTy-injective {N₁ = N-Pair N₁ N₃} {N-Var (NV-Var x)} ()
  nfTyTy-injective {N₁ = N-Pair N₁ N₃} {N-Var (NV-Dual d x)} ()
  nfTyTy-injective {N₁ = N-Pair N₁ N₃} {N-Pair N₂ N₄} eq
    with pair-injective eq
  ... | refl , refl , eq₁ , eq₂ =
    cong₂ N-Pair (nfTyTy-injective eq₁) (nfTyTy-injective eq₂)
  nfTyTy-injective {N₁ = N-Poly K′ N₁} {N-Var (NV-Var x)} ()
  nfTyTy-injective {N₁ = N-Poly K′ N₁} {N-Var (NV-Dual d x)} ()
  nfTyTy-injective {N₁ = N-Poly K′ N₁} {N-Poly K″ N₂} eq
    with poly-injective eq
  ... | refl , eq′ = cong (N-Poly K′) (nfTyTy-injective eq′)
  nfTyTy-injective {N₁ = N-Sub km≤ N₁} {N-Var (NV-Var x)} ()
  nfTyTy-injective {N₁ = N-Sub km≤ N₁} {N-Var (NV-Dual d x)} ()
  nfTyTy-injective {N₁ = N-Sub km≤ N₁} {N-Sub km≤′ N₂} eq
    with sub-injective eq
  ... | refl , refl , refl , eq′ =
    cong (N-Sub km≤) (nfTyTy-injective eq′)
  nfTyTy-injective {N₁ = N-End} {N-End} refl = refl
  nfTyTy-injective {N₁ = N-End} {N-Var (NV-Var x)} ()
  nfTyTy-injective {N₁ = N-End} {N-Var (NV-Dual d x)} ()
  nfTyTy-injective {N₁ = N-Msg p NP₁ N₁} {N-Var (NV-Var x)} ()
  nfTyTy-injective {N₁ = N-Msg p NP₁ N₁} {N-Var (NV-Dual d x)} ()
  nfTyTy-injective {N₁ = N-Msg p NP₁ N₁} {N-Msg p′ NP₂ N₂} eq
    with msg-injective eq
  ... | refl , eq₁ , eq₂ =
    cong₂ (N-Msg p) (nfProto′Ty-injective eq₁) (nfTyTy-injective eq₂)
  nfTyTy-injective {N₁ = N-ProtoD N₁} {N-Var (NV-Var x)} ()
  nfTyTy-injective {N₁ = N-ProtoD N₁} {N-Var (NV-Dual d x)} ()
  nfTyTy-injective {N₁ = N-ProtoD N₁} {N-ProtoD N₂} eq =
    cong N-ProtoD (nfTyTy-injective (protoD-injective eq))

from-nt-idem : (S : Ty [] (KV KS Lin)) → fromNormalTy
      (Types.nf-normal-type Duality.⊝ (λ _ → Duality.D-S) S)
      ≡
      fromNormalTy
      (Types.nf-normal-type Duality.⊝ (λ _ → Duality.D-S) (Types.nf Duality.⊕ Duality.d?⊥ S))
from-nt-idem S =
  nfTyTy-injective
    (Eq.trans
      (nfTyTy-fromNormalTy
        (Types.nf-normal-type Duality.⊝ (λ _ → Duality.D-S) S))
      (Eq.trans
        (Types.nf-complete- (λ _ → Duality.D-S)
          (Types.≡c-symm (Types.nf-sound+ S)))
        (Eq.sym
          (nfTyTy-fromNormalTy
            (Types.nf-normal-type Duality.⊝ (λ _ → Duality.D-S)
              (Types.nf Duality.⊕ Duality.d?⊥ S))))))
