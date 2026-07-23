module TypesProtocolConstructors where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_)
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; inspect; Reveal_·_is_)

open import Util
open import Kinds
open import Duality
open import Variance using (Variance; vswap; vcompose)
open import Types hiding
  ( Variance
  ; vswap
  ; vcompose
  ; vcompose-⊕
  ; vcompose-⊝
  ; vcompose-⊘
  ; vcompose-sym
  )

data UsageVariance : Set where
  unused : UsageVariance
  used : Variance → UsageVariance

swapUsage : UsageVariance → UsageVariance
swapUsage unused = unused
swapUsage (used v) = used (vswap v)

composeUsage : Variance → UsageVariance → UsageVariance
composeUsage v unused = unused
composeUsage v (used v′) = used (vcompose v v′)

joinUsage : UsageVariance → UsageVariance → UsageVariance
joinUsage unused uv = uv
joinUsage uv unused = uv
joinUsage (used ⊕) (used ⊕) = used ⊕
joinUsage (used ⊝) (used ⊝) = used ⊝
joinUsage (used ⊘) (used v) = used ⊘
joinUsage (used v) (used ⊘) = used ⊘
joinUsage (used ⊕) (used ⊝) = used ⊘
joinUsage (used ⊝) (used ⊕) = used ⊘

usageVariance-Var : K ∈ Δ → KP ∈ Δ → UsageVariance
usageVariance-Var (here refl) (here refl) = used ⊕
usageVariance-Var (here refl) (there q) = unused
usageVariance-Var (there p) (here refl) = unused
usageVariance-Var (there p) (there q) = usageVariance-Var p q

usageVariance : Ty Δ K → KP ∈ Δ → UsageVariance
usageVariance (T-Var x) p = usageVariance-Var x p
usageVariance T-Base p = unused
usageVariance (T-Arrow T₁ T₂) p =
  joinUsage (swapUsage (usageVariance T₁ p)) (usageVariance T₂ p)
usageVariance (T-Pair T₁ T₂) p =
  joinUsage (usageVariance T₁ p) (usageVariance T₂ p)
usageVariance (T-Poly _ T) p = usageVariance T (there p)
usageVariance (T-Sub x T) p = usageVariance T p
usageVariance (T-Dual x T) p = swapUsage (usageVariance T p)
usageVariance T-End p = unused
usageVariance (T-Msg x T S) p =
  joinUsage
    (usageVariance S p)
    (case x of λ { ⊕ → swapUsage (usageVariance T p)
                 ; ⊝ → usageVariance T p })
usageVariance (T-Up T) p = usageVariance T p
usageVariance (T-Minus T) p = swapUsage (usageVariance T p)
usageVariance (T-ProtoD T) p = usageVariance T p
usageVariance (T-ProtoP #c⊆#d v₁ T) p = composeUsage v₁ (usageVariance T p)

allUsageVariance : List (Ty Δ KP) → KP ∈ Δ → UsageVariance
allUsageVariance [] p = unused
allUsageVariance (T ∷ Ts) p = joinUsage (usageVariance T p) (allUsageVariance Ts p)

allUsesVar : Variance → KP ∈ Δ → List (Ty Δ KP) → Set
allUsesVar v p Ts = (allUsageVariance Ts p ≡ used v) ⊎ (allUsageVariance Ts p ≡ unused)

-- ProtocolConstructors n v is the type of the constructor arguments for a protocol type
-- with n constructors and variance v.
-- The type of the constructor arguments is a list of types, where each type
-- uses its zeroth type variable of kind KP in the correct variance.
ConstructorSignature : Variance → Set
ConstructorSignature v = Σ (List (Ty (KP ∷ []) KP)) (allUsesVar v (here refl))
AllConstructorSignatures : ℕ → Variance → Set
AllConstructorSignatures n v = Fin n → ConstructorSignature v

postulate
    ProtocolConstructors : (n : ℕ) → (v : Variance) → AllConstructorSignatures n v

open import Kits
open Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (⋯-id; _⋯_)

singletonSubst : Ty Δ KP → (KP ∷ []) →ₛ Δ
singletonSubst P _ (here refl) = P
singletonSubst P _ (there ())

instantiate : 
    ⦃ KT : Kit _∋/⊢_ ⦄ → Polarity
     → (T : Ty (KP ∷ []) K)
     → Ty Δ KP → Ty Δ K
instantiate p T P = T ⋯ singletonSubst P

materializeList : List (Ty (KP ∷ []) KP) → Polarity → Ty Δ KP → Ty Δ SLin → Ty Δ SLin
materializeList [] p P S = S
materializeList (T ∷ Ts) p P S =
  T-Msg p (instantiate ⦃ Kₛ ⦄ p T P) (materializeList Ts p P S)

materialize : ∀ {v} → ConstructorSignature v → Polarity → Ty Δ KP → Ty Δ SLin → Ty Δ SLin
materialize (Ts , uv) p P S = materializeList Ts p P S

materialize-at : ∀ {n v} → AllConstructorSignatures n v → Fin n → Polarity → Ty Δ KP → Ty Δ SLin → Ty Δ SLin
materialize-at {n} {v} cs i p P S = materialize (cs i) p P S

SelectTy0 : (k : ℕ) → (v : Variance) → AllConstructorSignatures k v → (i : Fin k) → (P : Ty Δ KP) → (S : Ty Δ SLin) → Ty Δ TLin
SelectTy0 k v cs i P S = T-Arrow
                     (T-Msg ⊕ (T-ProtoP (Subset.⁅ i ⁆) v P) S)
                     (materialize-at cs i ⊕ P S)

SelectTy : (k : ℕ) → (v : Variance) → (i : Fin k) → (P : Ty Δ KP) → (S : Ty Δ SLin) → Ty Δ TLin
SelectTy k v i P S = SelectTy0 k v (ProtocolConstructors k v) i P S

SelectTy1 : ∀ {Δ k} → (v : Variance) → (i : Fin k) → (P : Ty Δ KP) → Ty Δ TLin
SelectTy1 {Δ} {k} v i P =
  T-Poly SLin
    (SelectTy k v i (P ⋯ weakenᵣ SLin) (T-Var (here refl)))

SelectTy2 : ∀ {Δ k} → (v : Variance) → (i : Fin k) → (P : Ty Δ KP) → (S : Ty Δ SLin) → Ty Δ TLin
SelectTy2 {Δ} {k} v i P S =
  SelectTy k v i P S

SelectConstTy : ∀ {Δ k} → (v : Variance) → (i : Fin k) → Ty Δ TLin
SelectConstTy v i = T-Poly KP (SelectTy1 v i (T-Var (here refl)))
