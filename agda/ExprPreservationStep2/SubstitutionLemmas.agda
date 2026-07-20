module ExprPreservationStep2.SubstitutionLemmas where

open import Data.Fin using (Fin)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; subst; inspect; Reveal_·_is_)
import Relation.Binary.PropositionalEquality as Eq

import Duality
open import Kinds
open import Kits
import Types
import TypesProtocolConstructors as TPC
import NormalTypesSubstitution
open import NormalTypes using
  ( N-Sub
  ; N-End
  ; nfProtoTy-fromNormalProto
  ; nfTyTy-fromNormalTy
  )
open import Variance using
  ( Variance
  ; ⊕
  ; ⊝
  ; ⊘
  ; vswap
  ; vcompose
  ; VarianceCovers
  ; compose-covers
  )
open import Types using (Ty; T-Base)
open import Subtyping using
  ( _<<:[_]_
  ; injᵥ
  ; <:-sub
  ; <:-fun
  ; <:-pair
  ; <:-all
  ; <:-msg
  ; <:-proto
  ; <:-minus
  ; <:-dual-lr
  ; <:-up
  ; <:-protoD
  ; conv⇒subty
  )
open import TypesProtocolConstructors using
  ( ConstructorSignature
  ; instantiate
  ; materialize
  ; singletonSubst
  ; UsageVariance
  ; unused
  ; used
  ; usageVariance
  ; swapUsage
  ; joinUsage
  ; composeUsage
  )
open import ExprSyntax using (NfTy)
open import ExprNormalTyping using
  ( ⌞_⌟
  ; normalizeTy
  ; materializeListNf
  )
open import NormalTypesSubstitution using
  ( msgNF
  ; msgNF-sound
  )
open import AlgorithmicNFSubstitution using
  ( subst-preserves-<:ₜ
  )
open import SubstitutionSubtyping using
  ( subst-preserves-≡c
  ; subst-preserves-<<:
  ; t-dual-preserves-≡c
  )

open Kits.Syntax Types.Ty-Syntax hiding (Sort)
open Traversal Types.Ty-Traversal
open CTraversal record { fusion = Types.fusion }

_≈ₛ_ : ∀ {Δ₁ Δ₂} → (Δ₁ →ₛ Δ₂) → (Δ₁ →ₛ Δ₂) → Set
_≈ₛ_ {Δ₁} ϕ ψ = ∀ K (x : K ∈ Δ₁) → (ϕ K x) Types.≡c (ψ K x)

SubstRelVar :
  ∀ {Δ K Δ′}
  → K ∈ Δ → KP ∈ Δ → Variance
  → Ty Δ′ K → Ty Δ′ K → Set
SubstRelVar (here refl) (here refl) v T U = T <<:[ v ] U
SubstRelVar (here refl) (there q) v T U = T Types.≡c U
SubstRelVar (there x) (here refl) v T U = T Types.≡c U
SubstRelVar (there x) (there p) v T U = SubstRelVar x p v T U

SubstRelates :
  ∀ {Δ₁ Δ₂}
  → (Δ₁ →ₛ Δ₂) → KP ∈ Δ₁ → Variance → (Δ₁ →ₛ Δ₂) → Set
SubstRelates {Δ₁} ϕ p v ψ =
  ∀ K (x : K ∈ Δ₁) → SubstRelVar x p v (ϕ K x) (ψ K x)

SubstRelUnused :
  ∀ {Δ K Δ′}
  → K ∈ Δ → KP ∈ Δ
  → Ty Δ′ K → Ty Δ′ K → Set
SubstRelUnused (here refl) (here refl) T U = ⊤
SubstRelUnused (here refl) (there q) T U = T Types.≡c U
SubstRelUnused (there x) (here refl) T U = T Types.≡c U
SubstRelUnused (there x) (there p) T U = SubstRelUnused x p T U

SubstIgnores :
  ∀ {Δ₁ Δ₂}
  → (Δ₁ →ₛ Δ₂) → KP ∈ Δ₁ → (Δ₁ →ₛ Δ₂) → Set
SubstIgnores {Δ₁} ϕ p ψ =
  ∀ K (x : K ∈ Δ₁) → SubstRelUnused x p (ϕ K x) (ψ K x)

≈ᵥ⇒≈ᵤ :
  ∀ {Δ₁ Δ₂}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
    {p : KP ∈ Δ₁}
    {v : Variance}
  → SubstRelates ϕ p v ψ
  → SubstIgnores ϕ p ψ
≈ᵥ⇒≈ᵤ {p = here refl} rel K (here refl) = tt
≈ᵥ⇒≈ᵤ {p = there q} rel K (here refl) = rel K (here refl)
≈ᵥ⇒≈ᵤ {p = here refl} rel K (there x) = rel K (there x)
≈ᵥ⇒≈ᵤ {p = there p} rel K (there x) = ≈ᵥ⇒≈ᵤ {p = p} (λ K′ y → rel K′ (there y)) K x

lift-≈ₛ :
  ∀ {Δ₁ Δ₂ K} {ϕ ψ : Δ₁ →ₛ Δ₂}
  → ϕ ≈ₛ ψ
  → (ϕ ↑ₛ K) ≈ₛ (ψ ↑ₛ K)
lift-≈ₛ rel K′ (here refl) = Types.≡c-refl
lift-≈ₛ rel K′ (there x) = subst-preserves-≡c (rel K′ x) (weakenᵣ _)

weaken-SubstRelUnused :
  ∀ {Δ K Δ′ K′}
    {x : K ∈ Δ} {p : KP ∈ Δ}
    {T U : Ty Δ′ K}
  → SubstRelUnused x p T U
  → SubstRelUnused x p (T ⋯ weakenᵣ K′) (U ⋯ weakenᵣ K′)
weaken-SubstRelUnused {x = here refl} {p = here refl} rel = tt
weaken-SubstRelUnused {x = here refl} {p = there q} rel =
  subst-preserves-≡c rel (weakenᵣ _)
weaken-SubstRelUnused {x = there x} {p = here refl} rel =
  subst-preserves-≡c rel (weakenᵣ _)
weaken-SubstRelUnused {x = there x} {p = there p} rel =
  weaken-SubstRelUnused {x = x} {p = p} rel

lift-≈ᵤ :
  ∀ {Δ₁ Δ₂ K}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
    {p : KP ∈ Δ₁}
  → SubstIgnores ϕ p ψ
  → SubstIgnores (ϕ ↑ₛ K) (there p) (ψ ↑ₛ K)
lift-≈ᵤ rel K′ (here refl) = Types.≡c-refl
lift-≈ᵤ {p = p} rel K′ (there x) =
  weaken-SubstRelUnused {x = x} {p = p} (rel K′ x)

subst-preserves-≡c-pointwise :
  ∀ {Δ₁ Δ₂ K} {ϕ ψ : Δ₁ →ₛ Δ₂} (T : Ty Δ₁ K)
  → ϕ ≈ₛ ψ
  → (T ⋯ ϕ) Types.≡c (T ⋯ ψ)
subst-preserves-≡c-pointwise (Types.T-Var x) rel = rel _ x
subst-preserves-≡c-pointwise T-Base rel = Types.≡c-refl
subst-preserves-≡c-pointwise (Types.T-Arrow T U) rel =
  Types.≡c-fun
    (subst-preserves-≡c-pointwise T rel)
    (subst-preserves-≡c-pointwise U rel)
subst-preserves-≡c-pointwise (Types.T-Pair T U) rel =
  Types.≡c-pair
    (subst-preserves-≡c-pointwise T rel)
    (subst-preserves-≡c-pointwise U rel)
subst-preserves-≡c-pointwise (Types.T-Poly K′ T) rel =
  Types.≡c-all (subst-preserves-≡c-pointwise T (lift-≈ₛ rel))
subst-preserves-≡c-pointwise (Types.T-Sub K≤K′ T) rel =
  Types.≡c-sub K≤K′ (subst-preserves-≡c-pointwise T rel)
subst-preserves-≡c-pointwise (Types.T-Dual Duality.D-S T) rel =
  Types.≡c-trns
    (Types.dual-tinv (T ⋯ _))
    (Types.≡c-trns
      (t-dual-preserves-≡c (subst-preserves-≡c-pointwise T rel))
      (Types.≡c-symm (Types.dual-tinv (T ⋯ _))))
subst-preserves-≡c-pointwise Types.T-End rel = Types.≡c-refl
subst-preserves-≡c-pointwise (Types.T-Msg p T S) rel =
  Types.≡c-msg
    (subst-preserves-≡c-pointwise T rel)
    (subst-preserves-≡c-pointwise S rel)
subst-preserves-≡c-pointwise (Types.T-Up T) rel =
  Types.≡c-up (subst-preserves-≡c-pointwise T rel)
subst-preserves-≡c-pointwise (Types.T-Minus T) rel =
  Types.≡c-minus (subst-preserves-≡c-pointwise T rel)
subst-preserves-≡c-pointwise (Types.T-ProtoD T) rel =
  Types.≡c-protoD (subst-preserves-≡c-pointwise T rel)
subst-preserves-≡c-pointwise (Types.T-ProtoP #c v T) rel =
  Types.≡c-protoP (subst-preserves-≡c-pointwise T rel)

singletonSubst-≈ₛ :
  ∀ {Δ} {U V : Ty Δ KP}
  → U Types.≡c V
  → singletonSubst U ≈ₛ singletonSubst V
singletonSubst-≈ₛ eq K (here refl) = eq
singletonSubst-≈ₛ eq K (there ())

singletonSubst-≈ᵤ :
  ∀ {Δ}
    {U V : Ty Δ KP}
  → SubstIgnores (singletonSubst U) (here refl) (singletonSubst V)
singletonSubst-≈ᵤ K (here refl) = tt
singletonSubst-≈ᵤ K (there ())

singletonSubst-≈ᵥ :
  ∀ {Δ}
    {U V : Ty Δ KP}
    {v : Variance}
  → U <<:[ v ] V
  → SubstRelates (singletonSubst U) (here refl) v (singletonSubst V)
singletonSubst-≈ᵥ rel K (here refl) = rel
singletonSubst-≈ᵥ rel K (there ())

singletonSubst-compose :
  ∀ {Δ₁ Δ₂}
    {P : Ty Δ₁ KP}
    {ϕ : Δ₁ →ₛ Δ₂}
  → (singletonSubst P ·ₖ ϕ) ~ singletonSubst (P ⋯ ϕ)
singletonSubst-compose KP (here refl) = refl
singletonSubst-compose K (there ())

instantiate-compose :
  ∀ {Δ₁ Δ₂ K} {p : Duality.Polarity}
    (T : Ty (KP ∷ []) K)
    {P : Ty Δ₁ KP}
    {ϕ : Δ₁ →ₛ Δ₂}
  → instantiate ⦃ Kₛ ⦄ p T P ⋯ ϕ
      ≡ instantiate ⦃ Kₛ ⦄ p T (P ⋯ ϕ)
instantiate-compose T {P} {ϕ} =
  trans
    (fusion T (singletonSubst P) ϕ)
    (⋯-cong T singletonSubst-compose)

conv⇒<<: :
  ∀ {Δ K} {T₁ T₂ : Ty Δ K} {v : Variance}
  → T₁ Types.≡c T₂
  → T₁ <<:[ v ] T₂
conv⇒<<: {v = ⊕} eq = proj₁ (conv⇒subty _ _ eq)
conv⇒<<: {v = ⊝} eq = proj₂ (conv⇒subty _ _ eq)
conv⇒<<: {v = ⊘} eq = eq

swap-<<: :
  ∀ {Δ K} {T₁ T₂ : Ty Δ K} {v : Variance}
  → T₁ <<:[ v ] T₂
  → T₂ <<:[ vswap v ] T₁
swap-<<: {v = ⊕} rel = rel
swap-<<: {v = ⊝} rel = rel
swap-<<: {v = ⊘} rel = Types.≡c-symm rel

swap-SubstRelVar :
  ∀ {Δ K Δ′}
    {x : K ∈ Δ} {p : KP ∈ Δ}
    {v : Variance}
    {T U : Ty Δ′ K}
  → SubstRelVar x p v T U
  → SubstRelVar x p (vswap v) U T
swap-SubstRelVar {x = here refl} {p = here refl} rel =
  swap-<<: rel
swap-SubstRelVar {x = here refl} {p = there q} rel =
  Types.≡c-symm rel
swap-SubstRelVar {x = there x} {p = here refl} rel =
  Types.≡c-symm rel
swap-SubstRelVar {x = there x} {p = there p} rel =
  swap-SubstRelVar {x = x} {p = p} rel

swap-≈ᵥ :
  ∀ {Δ₁ Δ₂}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
    {p : KP ∈ Δ₁}
    {v : Variance}
  → SubstRelates ϕ p v ψ
  → SubstRelates ψ p (vswap v) ϕ
swap-≈ᵥ {p = p} rel K x = swap-SubstRelVar {x = x} {p = p} (rel K x)

≈ᵥ⊘⇒≈ₛ :
  ∀ {Δ₁ Δ₂}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
    {p : KP ∈ Δ₁}
  → SubstRelates ϕ p ⊘ ψ
  → ϕ ≈ₛ ψ
≈ᵥ⊘⇒≈ₛ {p = here refl} rel K (here refl) = rel K (here refl)
≈ᵥ⊘⇒≈ₛ {p = there q} rel K (here refl) = rel K (here refl)
≈ᵥ⊘⇒≈ₛ {p = here refl} rel K (there x) = rel K (there x)
≈ᵥ⊘⇒≈ₛ {p = there p} rel K (there x) =
  ≈ᵥ⊘⇒≈ₛ {p = p} (λ K′ y → rel K′ (there y)) K x

coerce-<<: :
  ∀ {Δ K}
    {T₁ T₂ : Ty Δ K}
    {v₁ v₂ : Variance}
  → T₁ <<:[ v₁ ] T₂
  → VarianceCovers v₁ v₂
  → T₁ <<:[ v₂ ] T₂
coerce-<<: {v₁ = ⊕} {⊕} rel cov = rel
coerce-<<: {v₁ = ⊝} {⊝} rel cov = rel
coerce-<<: {v₁ = ⊘} {⊕} rel cov = conv⇒<<: {v = ⊕} rel
coerce-<<: {v₁ = ⊘} {⊝} rel cov = conv⇒<<: {v = ⊝} rel
coerce-<<: {v₁ = ⊘} {⊘} rel cov = rel

coerce-SubstRelVar :
  ∀ {Δ K Δ′}
    {x : K ∈ Δ} {p : KP ∈ Δ}
    {v₁ v₂ : Variance}
    {T U : Ty Δ′ K}
  → SubstRelVar x p v₁ T U
  → VarianceCovers v₁ v₂
  → SubstRelVar x p v₂ T U
coerce-SubstRelVar {x = here refl} {p = here refl} rel cov =
  coerce-<<: rel cov
coerce-SubstRelVar {x = here refl} {p = there q} rel cov = rel
coerce-SubstRelVar {x = there x} {p = here refl} rel cov = rel
coerce-SubstRelVar {x = there x} {p = there p} rel cov =
  coerce-SubstRelVar {x = x} {p = p} rel cov

coerce-≈ᵥ :
  ∀ {Δ₁ Δ₂}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
    {p : KP ∈ Δ₁}
    {v₁ v₂ : Variance}
  → (∀ K (x : K ∈ Δ₁) → SubstRelVar x p v₁ (ϕ K x) (ψ K x))
  → VarianceCovers v₁ v₂
  → (∀ K (x : K ∈ Δ₁) → SubstRelVar x p v₂ (ϕ K x) (ψ K x))
coerce-≈ᵥ {p = p} rel cov K x = coerce-SubstRelVar {x = x} {p = p} (rel K x) cov

swap-covers :
  ∀ {v u}
  → VarianceCovers v u
  → VarianceCovers (vswap v) (vswap u)
swap-covers {v = ⊕} {u = ⊕} cov = tt
swap-covers {v = ⊝} {u = ⊝} cov = tt
swap-covers {v = ⊘} {u = ⊕} cov = tt
swap-covers {v = ⊘} {u = ⊝} cov = tt
swap-covers {v = ⊘} {u = ⊘} cov = tt

vswap-involutive : ∀ v → vswap (vswap v) ≡ v
vswap-involutive ⊕ = refl
vswap-involutive ⊝ = refl
vswap-involutive ⊘ = refl

swap-covers-invol :
  ∀ {v u}
  → VarianceCovers v (vswap u)
  → VarianceCovers (vswap v) u
swap-covers-invol {v = v} {u = u} cov =
  subst (VarianceCovers (vswap v)) (vswap-involutive u) (swap-covers cov)

weaken-SubstRelVar :
  ∀ {Δ K Δ′ K′}
    {x : K ∈ Δ} {p : KP ∈ Δ}
    {v : Variance}
    {T U : Ty Δ′ K}
  → SubstRelVar x p v T U
  → SubstRelVar x p v (T ⋯ weakenᵣ K′) (U ⋯ weakenᵣ K′)
weaken-SubstRelVar {x = here refl} {p = here refl} rel =
  subst-preserves-<<: rel (weakenᵣ _)
weaken-SubstRelVar {x = here refl} {p = there q} rel =
  subst-preserves-≡c rel (weakenᵣ _)
weaken-SubstRelVar {x = there x} {p = here refl} rel =
  subst-preserves-≡c rel (weakenᵣ _)
weaken-SubstRelVar {x = there x} {p = there p} rel =
  weaken-SubstRelVar {x = x} {p = p} rel

lift-≈ᵥ :
  ∀ {Δ₁ Δ₂ K}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
    {p : KP ∈ Δ₁}
    {v : Variance}
  → (∀ K′ (x : K′ ∈ Δ₁) → SubstRelVar x p v (ϕ K′ x) (ψ K′ x))
  → (∀ K′ (x : K′ ∈ (K ∷ Δ₁)) →
        SubstRelVar x (there p) v ((ϕ ↑ₛ K) K′ x) ((ψ ↑ₛ K) K′ x))
lift-≈ᵥ rel K′ (here refl) = Types.≡c-refl
lift-≈ᵥ {p = p} rel K′ (there x) = weaken-SubstRelVar {x = x} {p = p} (rel K′ x)

sub-<<: :
  ∀ {Δ pk pk′ m m′}
    {K≤K′ : KV pk m ≤k KV pk′ m′}
    {T₁ T₂ : Ty Δ (KV pk m)}
    {v : Variance}
  → T₁ <<:[ v ] T₂
  → Types.T-Sub K≤K′ T₁ <<:[ v ] Types.T-Sub K≤K′ T₂
sub-<<: {K≤K′ = K≤K′} {v = ⊕} rel = <:-sub K≤K′ rel
sub-<<: {K≤K′ = K≤K′} {v = ⊝} rel = <:-sub K≤K′ rel
sub-<<: {v = ⊘} rel = Types.≡c-sub _ rel

fun-<<: :
  ∀ {Δ m}
    {pk₁ pk₂ : PreKind} {m₁ m₂ : Multiplicity}
    {T₁ T₂ : Ty Δ (KV pk₁ m₁)} {U₁ U₂ : Ty Δ (KV pk₂ m₂)}
    {v : Variance}
  → T₁ <<:[ vswap v ] T₂
  → U₁ <<:[ v ] U₂
  → Types.T-Arrow {m = m} T₁ U₁ <<:[ v ] Types.T-Arrow T₂ U₂
fun-<<: {v = ⊕} dom cod = <:-fun dom cod
fun-<<: {v = ⊝} dom cod = <:-fun dom cod
fun-<<: {v = ⊘} dom cod = Types.≡c-fun dom cod

pair-<<: :
  ∀ {Δ pk₁ pk₂ m}
    {T₁ T₂ : Ty Δ (KV pk₁ m)}
    {U₁ U₂ : Ty Δ (KV pk₂ m)}
    {v : Variance}
  → T₁ <<:[ v ] T₂
  → U₁ <<:[ v ] U₂
  → Types.T-Pair T₁ U₁ <<:[ v ] Types.T-Pair T₂ U₂
pair-<<: {v = ⊕} relT relU = <:-pair relT relU
pair-<<: {v = ⊝} relT relU = <:-pair relT relU
pair-<<: {v = ⊘} relT relU = Types.≡c-pair relT relU

all-<<: :
  ∀ {Δ K′ m}
    {T₁ T₂ : Ty (K′ ∷ Δ) (KV KT m)}
    {v : Variance}
  → T₁ <<:[ v ] T₂
  → Types.T-Poly K′ T₁ <<:[ v ] Types.T-Poly K′ T₂
all-<<: {v = ⊕} rel = <:-all rel
all-<<: {v = ⊝} rel = <:-all rel
all-<<: {v = ⊘} rel = Types.≡c-all rel

dual-<<: :
  ∀ {Δ m}
    {T₁ T₂ : Ty Δ (KV KS m)}
    {v : Variance}
  → T₁ <<:[ vswap v ] T₂
  → Types.T-Dual Duality.D-S T₁ <<:[ v ] Types.T-Dual Duality.D-S T₂
dual-<<: {v = ⊕} rel = <:-dual-lr Duality.D-S rel
dual-<<: {v = ⊝} rel = <:-dual-lr Duality.D-S rel
dual-<<: {T₁ = T₁} {T₂ = T₂} {v = ⊘} rel =
  Types.≡c-trns
    (Types.dual-tinv T₁)
    (Types.≡c-trns
      (t-dual-preserves-≡c rel)
      (Types.≡c-symm (Types.dual-tinv T₂)))

up-<<: :
  ∀ {Δ pk m}
    {T₁ T₂ : Ty Δ (KV pk m)}
    {v : Variance}
  → T₁ <<:[ v ] T₂
  → Types.T-Up T₁ <<:[ v ] Types.T-Up T₂
up-<<: {v = ⊕} rel = <:-up rel
up-<<: {v = ⊝} rel = <:-up rel
up-<<: {v = ⊘} rel = Types.≡c-up rel

minus-<<: :
  ∀ {Δ}
    {T₁ T₂ : Ty Δ KP}
    {v : Variance}
  → T₁ <<:[ vswap v ] T₂
  → Types.T-Minus T₁ <<:[ v ] Types.T-Minus T₂
minus-<<: {v = ⊕} rel = <:-minus rel
minus-<<: {v = ⊝} rel = <:-minus rel
minus-<<: {v = ⊘} rel = Types.≡c-minus rel

protoD-<<: :
  ∀ {Δ}
    {T₁ T₂ : Ty Δ TLin}
    {v : Variance}
  → T₁ <<:[ v ] T₂
  → Types.T-ProtoD T₁ <<:[ v ] Types.T-ProtoD T₂
protoD-<<: {v = ⊕} rel = <:-protoD rel
protoD-<<: {v = ⊝} rel = <:-protoD rel
protoD-<<: {v = ⊘} rel = Types.≡c-protoD rel

protoP-<<: :
  ∀ {Δ k}
    {#c : Subset.Subset k}
    {v₁ v₂ : Variance}
    {T₁ T₂ : Ty Δ KP}
  → T₁ <<:[ vcompose v₁ v₂ ] T₂
  → Types.T-ProtoP #c v₁ T₁ <<:[ v₂ ] Types.T-ProtoP #c v₁ T₂
protoP-<<: {v₁ = ⊕} {v₂ = ⊕} rel = <:-proto (λ {x} z → z) rel
protoP-<<: {v₁ = ⊝} {v₂ = ⊕} rel = <:-proto (λ {x} z → z) rel
protoP-<<: {v₁ = ⊘} {v₂ = ⊕} rel = <:-proto (λ {x} z → z) (conv⇒<<: rel)
protoP-<<: {v₁ = ⊕} {v₂ = ⊝} rel = <:-proto (λ {x} z → z) rel
protoP-<<: {v₁ = ⊝} {v₂ = ⊝} rel = <:-proto (λ {x} z → z) (swap-<<: {v = ⊕} rel)
protoP-<<: {v₁ = ⊘} {v₂ = ⊝} rel = <:-proto (λ {x} z → z) (Types.≡c-symm rel)
protoP-<<: {v₁ = ⊕} {v₂ = ⊘} rel = Types.≡c-protoP rel
protoP-<<: {v₁ = ⊝} {v₂ = ⊘} rel = Types.≡c-protoP rel
protoP-<<: {v₁ = ⊘} {v₂ = ⊘} rel = Types.≡c-protoP rel

msg-<<: :
  ∀ {Δ}
    {p : Duality.Polarity}
    {T₁ T₂ : Ty Δ KP}
    {S₁ S₂ : Ty Δ SLin}
    {v : Variance}
  → T₁ <<:[ vcompose (injᵥ p) v ] T₂
  → S₁ <<:[ v ] S₂
  → Types.T-Msg p T₁ S₁ <<:[ v ] Types.T-Msg p T₂ S₂
msg-<<: {p = Duality.⊕} {v = ⊕} relT relS = <:-msg relT relS
msg-<<: {p = Duality.⊕} {v = ⊝} relT relS = <:-msg (swap-<<: {v = ⊕} relT) relS
msg-<<: {p = Duality.⊕} {v = ⊘} relT relS = Types.≡c-msg relT relS
msg-<<: {p = Duality.⊝} {v = ⊕} relT relS = <:-msg relT relS
msg-<<: {p = Duality.⊝} {v = ⊝} relT relS = <:-msg relT relS
msg-<<: {p = Duality.⊝} {v = ⊘} relT relS = Types.≡c-msg relT relS

subst-preserves-≡c-unused :
  ∀ {Δ₁ Δ₂ K}
    (T : Ty Δ₁ K)
    {p : KP ∈ Δ₁}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
  → usageVariance T p ≡ unused
  → SubstIgnores ϕ p ψ
  → (T ⋯ ϕ) Types.≡c (T ⋯ ψ)

join-left-covers :
  ∀ {u₁ u u₂}
  → joinUsage (used u₁) u₂ ≡ used u
  → VarianceCovers u u₁

join-right-covers :
  ∀ {u₂ u u₁}
  → joinUsage u₁ (used u₂) ≡ used u
  → VarianceCovers u u₂

covers-trans :
  ∀ {v₁ v₂ v₃}
  → VarianceCovers v₁ v₂
  → VarianceCovers v₂ v₃
  → VarianceCovers v₁ v₃
covers-trans {v₁ = ⊕} {v₂ = ⊕} {v₃ = ⊕} _ _ = tt
covers-trans {v₁ = ⊝} {v₂ = ⊝} {v₃ = ⊝} _ _ = tt
covers-trans {v₁ = ⊘} _ _ = tt

composeUsage-⊕-used :
  ∀ {u v}
  → composeUsage ⊕ u ≡ used v
  → u ≡ used v
composeUsage-⊕-used {u = unused} ()
composeUsage-⊕-used {u = used u} refl = refl

composeUsage-⊘-used≢⊕ :
  ∀ {u}
  → composeUsage ⊘ u ≢ used ⊕
composeUsage-⊘-used≢⊕ {u = unused} ()
composeUsage-⊘-used≢⊕ {u = used u} ()

composeUsage-⊘-used≢⊝ :
  ∀ {u}
  → composeUsage ⊘ u ≢ used ⊝
composeUsage-⊘-used≢⊝ {u = unused} ()
composeUsage-⊘-used≢⊝ {u = used u} ()

subst-preserves-<<:-used⊕ :
  ∀ {Δ₁ Δ₂ K}
    (T : Ty Δ₁ K)
    {p : KP ∈ Δ₁}
    {u v : Variance}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
  → usageVariance T p ≡ used u
  → SubstRelates ϕ p v ψ
  → VarianceCovers v u
  → (T ⋯ ϕ) <<:[ ⊕ ] (T ⋯ ψ)
subst-preserves-<<:-used⊕ (Types.T-Var (here refl)) {p = here refl} {u = ⊕} refl rel cov =
  coerce-<<: (rel _ (here refl)) cov
subst-preserves-<<:-used⊕ (Types.T-Var (here refl)) {p = here refl} {u = ⊝} () rel cov
subst-preserves-<<:-used⊕ (Types.T-Var (here refl)) {p = here refl} {u = ⊘} () rel cov
subst-preserves-<<:-used⊕ (Types.T-Var (here refl)) {p = there q} () rel cov
subst-preserves-<<:-used⊕ (Types.T-Var (there x)) {p = here refl} () rel cov
subst-preserves-<<:-used⊕ (Types.T-Var (there x)) {p = there p} uv rel cov =
  subst-preserves-<<:-used⊕ (Types.T-Var x) {p = p} uv (λ K′ y → rel K′ (there y)) cov
subst-preserves-<<:-used⊕ T-Base () rel cov
subst-preserves-<<:-used⊕ (Types.T-Arrow T U) {p = p} {u = u} {v = v} uv rel cov
  with usageVariance T p | inspect (usageVariance T) p
     | usageVariance U p | inspect (usageVariance U) p
     | uv
... | unused | Eq.[ eqT ] | unused | Eq.[ eqU ] | ()
... | unused | Eq.[ eqT ] | used uU | Eq.[ eqU ] | refl =
  fun-<<: {v = ⊕}
    (coerce-<<: {v₁ = ⊘} {v₂ = ⊝}
      (subst-preserves-≡c-unused T eqT (≈ᵥ⇒≈ᵤ rel))
      tt)
    (subst-preserves-<<:-used⊕ U {u = uU} eqU rel cov)
... | used uT | Eq.[ eqT ] | unused | Eq.[ eqU ] | refl =
  fun-<<: {v = ⊕}
    (subst-preserves-<<:-used⊕
      T
      {u = uT}
      eqT
      (swap-≈ᵥ rel)
      (swap-covers-invol cov))
    (coerce-<<: {v₁ = ⊘} {v₂ = ⊕}
      (subst-preserves-≡c-unused U eqU (≈ᵥ⇒≈ᵤ rel))
      tt)
... | used uT | Eq.[ eqT ] | used uU | Eq.[ eqU ] | eqJoin =
  fun-<<: {v = ⊕}
    (subst-preserves-<<:-used⊕
      T
      {u = uT}
      eqT
      (swap-≈ᵥ rel)
      (swap-covers-invol
        (covers-trans
          cov
          (join-left-covers {u₁ = vswap uT} {u₂ = used uU} eqJoin))))
    (subst-preserves-<<:-used⊕
      U
      {u = uU}
      eqU
      rel
      (covers-trans
        cov
        (join-right-covers {u₂ = uU} {u₁ = used (vswap uT)} eqJoin)))
subst-preserves-<<:-used⊕ (Types.T-Pair T U) {p = p} {u = u} {v = v} uv rel cov
  with usageVariance T p | inspect (usageVariance T) p
     | usageVariance U p | inspect (usageVariance U) p
     | uv
... | unused | Eq.[ eqT ] | unused | Eq.[ eqU ] | ()
... | unused | Eq.[ eqT ] | used uU | Eq.[ eqU ] | refl =
  pair-<<: {v = ⊕}
    (coerce-<<: {v₁ = ⊘} {v₂ = ⊕}
      (subst-preserves-≡c-unused T eqT (≈ᵥ⇒≈ᵤ rel))
      tt)
    (subst-preserves-<<:-used⊕ U {u = uU} eqU rel cov)
... | used uT | Eq.[ eqT ] | unused | Eq.[ eqU ] | refl =
  pair-<<: {v = ⊕}
    (subst-preserves-<<:-used⊕ T {u = uT} eqT rel cov)
    (coerce-<<: {v₁ = ⊘} {v₂ = ⊕}
      (subst-preserves-≡c-unused U eqU (≈ᵥ⇒≈ᵤ rel))
      tt)
... | used uT | Eq.[ eqT ] | used uU | Eq.[ eqU ] | eqJoin =
  pair-<<: {v = ⊕}
    (subst-preserves-<<:-used⊕
      T
      {u = uT}
      eqT
      rel
      (covers-trans
        cov
        (join-left-covers {u₁ = uT} {u₂ = used uU} eqJoin)))
    (subst-preserves-<<:-used⊕
      U
      {u = uU}
      eqU
      rel
      (covers-trans
        cov
        (join-right-covers {u₂ = uU} {u₁ = used uT} eqJoin)))
subst-preserves-<<:-used⊕ (Types.T-Poly K′ T) {p = p} uv rel cov =
  all-<<: {v = ⊕} (subst-preserves-<<:-used⊕ T {p = there p} uv (lift-≈ᵥ rel) cov)
subst-preserves-<<:-used⊕ (Types.T-Sub K≤K′ T) uv rel cov =
  sub-<<: {v = ⊕} (subst-preserves-<<:-used⊕ T uv rel cov)
subst-preserves-<<:-used⊕ (Types.T-Dual Duality.D-S T) {p = p} uv rel cov
  with usageVariance T p | inspect (usageVariance T) p | uv
... | unused | Eq.[ eqT ] | ()
... | used uT | Eq.[ eqT ] | refl =
  dual-<<: {v = ⊕}
    (subst-preserves-<<:-used⊕
      T
      {u = uT}
      eqT
      (swap-≈ᵥ rel)
      (swap-covers-invol cov))
subst-preserves-<<:-used⊕ Types.T-End () rel cov
subst-preserves-<<:-used⊕ (Types.T-Msg Duality.⊕ T S) {p = p} {u = u} {v = v} uv rel cov
  with usageVariance S p | inspect (usageVariance S) p
     | usageVariance T p | inspect (usageVariance T) p
     | uv
... | unused | Eq.[ eqS ] | unused | Eq.[ eqT ] | ()
... | unused | Eq.[ eqS ] | used uT | Eq.[ eqT ] | refl =
  msg-<<: {p = Duality.⊕} {v = ⊕}
    (subst-preserves-<<:-used⊕
      T
      {u = uT}
      eqT
      (swap-≈ᵥ rel)
      (swap-covers-invol cov))
    (coerce-<<: {v₁ = ⊘} {v₂ = ⊕}
      (subst-preserves-≡c-unused S eqS (≈ᵥ⇒≈ᵤ rel))
      tt)
... | used uS | Eq.[ eqS ] | unused | Eq.[ eqT ] | refl =
  msg-<<: {p = Duality.⊕} {v = ⊕}
    (coerce-<<: {v₁ = ⊘} {v₂ = ⊝}
      (subst-preserves-≡c-unused T eqT (≈ᵥ⇒≈ᵤ rel))
      tt)
    (subst-preserves-<<:-used⊕ S {u = uS} eqS rel cov)
... | used uS | Eq.[ eqS ] | used uT | Eq.[ eqT ] | eqJoin =
  msg-<<: {p = Duality.⊕} {v = ⊕}
    (subst-preserves-<<:-used⊕
      T
      {u = uT}
      eqT
      (swap-≈ᵥ rel)
      (swap-covers-invol
        (covers-trans
          cov
          (join-right-covers {u₂ = vswap uT} {u₁ = used uS} eqJoin))))
    (subst-preserves-<<:-used⊕
      S
      {u = uS}
      eqS
      rel
      (covers-trans
        cov
        (join-left-covers {u₁ = uS} {u₂ = used (vswap uT)} eqJoin)))
subst-preserves-<<:-used⊕ (Types.T-Msg Duality.⊝ T S) {p = p} {u = u} {v = v} uv rel cov
  with usageVariance S p | inspect (usageVariance S) p
     | usageVariance T p | inspect (usageVariance T) p
     | uv
... | unused | Eq.[ eqS ] | unused | Eq.[ eqT ] | ()
... | unused | Eq.[ eqS ] | used uT | Eq.[ eqT ] | refl =
  msg-<<: {p = Duality.⊝} {v = ⊕}
    (subst-preserves-<<:-used⊕ T {u = uT} eqT rel cov)
    (coerce-<<: {v₁ = ⊘} {v₂ = ⊕}
      (subst-preserves-≡c-unused S eqS (≈ᵥ⇒≈ᵤ rel))
      tt)
... | used uS | Eq.[ eqS ] | unused | Eq.[ eqT ] | refl =
  msg-<<: {p = Duality.⊝} {v = ⊕}
    (coerce-<<: {v₁ = ⊘} {v₂ = ⊕}
      (subst-preserves-≡c-unused T eqT (≈ᵥ⇒≈ᵤ rel))
      tt)
    (subst-preserves-<<:-used⊕ S {u = uS} eqS rel cov)
... | used uS | Eq.[ eqS ] | used uT | Eq.[ eqT ] | eqJoin =
  msg-<<: {p = Duality.⊝} {v = ⊕}
    (subst-preserves-<<:-used⊕
      T
      {u = uT}
      eqT
      rel
      (covers-trans
        cov
        (join-right-covers {u₂ = uT} {u₁ = used uS} eqJoin)))
    (subst-preserves-<<:-used⊕
      S
      {u = uS}
      eqS
      rel
      (covers-trans
        cov
        (join-left-covers {u₁ = uS} {u₂ = used uT} eqJoin)))
subst-preserves-<<:-used⊕ (Types.T-Up T) uv rel cov =
  up-<<: {v = ⊕} (subst-preserves-<<:-used⊕ T uv rel cov)
subst-preserves-<<:-used⊕ (Types.T-Minus T) {p = p} uv rel cov
  with usageVariance T p | inspect (usageVariance T) p | uv
... | unused | Eq.[ eqT ] | ()
... | used uT | Eq.[ eqT ] | refl =
  minus-<<: {v = ⊕}
    (subst-preserves-<<:-used⊕
      T
      {u = uT}
      eqT
      (swap-≈ᵥ rel)
      (swap-covers-invol cov))
subst-preserves-<<:-used⊕ (Types.T-ProtoD T) uv rel cov =
  protoD-<<: {v = ⊕} (subst-preserves-<<:-used⊕ T uv rel cov)
subst-preserves-<<:-used⊕ (Types.T-ProtoP #c ⊕ T) uv rel cov =
  protoP-<<: {v₁ = ⊕} {v₂ = ⊕}
    (subst-preserves-<<:-used⊕ T (composeUsage-⊕-used uv) rel cov)
subst-preserves-<<:-used⊕ (Types.T-ProtoP #c ⊝ T) {p = p} uv rel cov
  with usageVariance T p | inspect (usageVariance T) p | uv
... | unused | Eq.[ eqT ] | ()
... | used uT | Eq.[ eqT ] | refl =
  protoP-<<: {v₁ = ⊝} {v₂ = ⊕}
    (subst-preserves-<<:-used⊕
      T
      {u = uT}
      eqT
      (swap-≈ᵥ rel)
      (swap-covers-invol cov))
subst-preserves-<<:-used⊕ (Types.T-ProtoP #c ⊘ T) {u = ⊕} {v = ⊕} uv rel cov =
  ⊥-elim (composeUsage-⊘-used≢⊕ uv)
subst-preserves-<<:-used⊕ (Types.T-ProtoP #c ⊘ T) {u = ⊝} {v = ⊕} uv rel cov =
  ⊥-elim (composeUsage-⊘-used≢⊝ uv)
subst-preserves-<<:-used⊕ (Types.T-ProtoP #c ⊘ T) {u = ⊘} {v = ⊕} uv rel ()
subst-preserves-<<:-used⊕ (Types.T-ProtoP #c ⊘ T) {u = ⊕} {v = ⊝} uv rel cov =
  ⊥-elim (composeUsage-⊘-used≢⊕ uv)
subst-preserves-<<:-used⊕ (Types.T-ProtoP #c ⊘ T) {u = ⊝} {v = ⊝} uv rel cov =
  ⊥-elim (composeUsage-⊘-used≢⊝ uv)
subst-preserves-<<:-used⊕ (Types.T-ProtoP #c ⊘ T) {u = ⊘} {v = ⊝} uv rel ()
subst-preserves-<<:-used⊕ (Types.T-ProtoP #c ⊘ T) {u = ⊕} {v = ⊘} uv rel cov =
  ⊥-elim (composeUsage-⊘-used≢⊕ uv)
subst-preserves-<<:-used⊕ (Types.T-ProtoP #c ⊘ T) {u = ⊝} {v = ⊘} uv rel cov =
  ⊥-elim (composeUsage-⊘-used≢⊝ uv)
subst-preserves-<<:-used⊕ (Types.T-ProtoP #c ⊘ T) {p = p} {u = ⊘} {v = ⊘} uv rel cov =
  protoP-<<: {v₁ = ⊘} {v₂ = ⊕}
    (subst-preserves-≡c-pointwise T (≈ᵥ⊘⇒≈ₛ rel))

join-left-covers {u₁ = ⊕} {u = ⊕} {u₂ = unused} refl = tt
join-left-covers {u₁ = ⊕} {u = ⊕} {u₂ = used ⊕} refl = tt
join-left-covers {u₁ = ⊕} {u = ⊘} {u₂ = used ⊝} refl = tt
join-left-covers {u₁ = ⊕} {u = ⊘} {u₂ = used ⊘} refl = tt
join-left-covers {u₁ = ⊝} {u = ⊝} {u₂ = unused} refl = tt
join-left-covers {u₁ = ⊝} {u = ⊘} {u₂ = used ⊕} refl = tt
join-left-covers {u₁ = ⊝} {u = ⊝} {u₂ = used ⊝} refl = tt
join-left-covers {u₁ = ⊝} {u = ⊘} {u₂ = used ⊘} refl = tt
join-left-covers {u₁ = ⊘} {u = ⊘} {u₂ = unused} refl = tt
join-left-covers {u₁ = ⊘} {u = ⊘} {u₂ = used ⊕} refl = tt
join-left-covers {u₁ = ⊘} {u = ⊘} {u₂ = used ⊝} refl = tt
join-left-covers {u₁ = ⊘} {u = ⊘} {u₂ = used ⊘} refl = tt

join-right-covers {u₂ = ⊕} {u = ⊕} {u₁ = unused} refl = tt
join-right-covers {u₂ = ⊕} {u = ⊕} {u₁ = used ⊕} refl = tt
join-right-covers {u₂ = ⊕} {u = ⊘} {u₁ = used ⊝} refl = tt
join-right-covers {u₂ = ⊕} {u = ⊘} {u₁ = used ⊘} refl = tt
join-right-covers {u₂ = ⊝} {u = ⊝} {u₁ = unused} refl = tt
join-right-covers {u₂ = ⊝} {u = ⊘} {u₁ = used ⊕} refl = tt
join-right-covers {u₂ = ⊝} {u = ⊝} {u₁ = used ⊝} refl = tt
join-right-covers {u₂ = ⊝} {u = ⊘} {u₁ = used ⊘} refl = tt
join-right-covers {u₂ = ⊘} {u = ⊘} {u₁ = unused} refl = tt
join-right-covers {u₂ = ⊘} {u = ⊘} {u₁ = used ⊕} refl = tt
join-right-covers {u₂ = ⊘} {u = ⊘} {u₁ = used ⊝} refl = tt
join-right-covers {u₂ = ⊘} {u = ⊘} {u₁ = used ⊘} refl = tt

unused≢used : ∀ {u} → unused ≡ used u → ⊥
unused≢used ()

used≢unused : ∀ {u} → used u ≡ unused → ⊥
used≢unused ()

joinUsage-used-used≢unused :
  ∀ {u₁ u₂}
  → joinUsage (used u₁) (used u₂) ≡ unused
  → ⊥
joinUsage-used-used≢unused {u₁ = ⊕} {u₂ = ⊕} ()
joinUsage-used-used≢unused {u₁ = ⊕} {u₂ = ⊝} ()
joinUsage-used-used≢unused {u₁ = ⊕} {u₂ = ⊘} ()
joinUsage-used-used≢unused {u₁ = ⊝} {u₂ = ⊕} ()
joinUsage-used-used≢unused {u₁ = ⊝} {u₂ = ⊝} ()
joinUsage-used-used≢unused {u₁ = ⊝} {u₂ = ⊘} ()
joinUsage-used-used≢unused {u₁ = ⊘} {u₂ = ⊕} ()
joinUsage-used-used≢unused {u₁ = ⊘} {u₂ = ⊝} ()
joinUsage-used-used≢unused {u₁ = ⊘} {u₂ = ⊘} ()

joinUsage-unused-left :
  ∀ {u₁ u₂}
  → joinUsage u₁ u₂ ≡ unused
  → u₁ ≡ unused
joinUsage-unused-left {u₁ = unused} {u₂ = unused} refl = refl
joinUsage-unused-left {u₁ = unused} {u₂ = used u} ()
joinUsage-unused-left {u₁ = used u} {u₂ = unused} ()
joinUsage-unused-left {u₁ = used u₁} {u₂ = used u₂} eq =
  ⊥-elim (joinUsage-used-used≢unused eq)

joinUsage-unused-right :
  ∀ {u₁ u₂}
  → joinUsage u₁ u₂ ≡ unused
  → u₂ ≡ unused
joinUsage-unused-right {u₁ = unused} {u₂ = unused} refl = refl
joinUsage-unused-right {u₁ = unused} {u₂ = used u} ()
joinUsage-unused-right {u₁ = used u} {u₂ = unused} ()
joinUsage-unused-right {u₁ = used u₁} {u₂ = used u₂} eq =
  ⊥-elim (joinUsage-used-used≢unused eq)

swapUsage-unused :
  ∀ {u}
  → swapUsage u ≡ unused
  → u ≡ unused
swapUsage-unused {u = unused} refl = refl
swapUsage-unused {u = used v} ()

composeUsage-unused :
  ∀ {v u}
  → composeUsage v u ≡ unused
  → u ≡ unused
composeUsage-unused {u = unused} refl = refl
composeUsage-unused {u = used u} ()

var-subst-ignores-unused :
  ∀ {Δ K Δ′}
    (x : K ∈ Δ)
    (p : KP ∈ Δ)
    {ϕ ψ : Δ →ₛ Δ′}
  → usageVariance (Types.T-Var x) p ≡ unused
  → SubstIgnores ϕ p ψ
  → (ϕ K x) Types.≡c (ψ K x)
var-subst-ignores-unused (here refl) (here refl) uv rel = ⊥-elim (used≢unused uv)
var-subst-ignores-unused (here refl) (there q) uv rel = rel _ (here refl)
var-subst-ignores-unused (there x) (here refl) uv rel = rel _ (there x)
var-subst-ignores-unused (there x) (there p) uv rel =
  var-subst-ignores-unused x p uv (λ K y → rel K (there y))

subst-preserves-≡c-unused (Types.T-Var x) {p = p} uv rel =
  var-subst-ignores-unused x p uv rel
subst-preserves-≡c-unused T-Base uv rel = Types.≡c-refl
subst-preserves-≡c-unused (Types.T-Arrow T U) {p = p} uv rel =
  Types.≡c-fun
    (subst-preserves-≡c-unused
      T
      (swapUsage-unused
        (joinUsage-unused-left
          {u₁ = swapUsage (usageVariance T p)}
          {u₂ = usageVariance U p}
          uv))
      rel)
    (subst-preserves-≡c-unused
      U
      (joinUsage-unused-right
        {u₁ = swapUsage (usageVariance T p)}
        {u₂ = usageVariance U p}
        uv)
      rel)
subst-preserves-≡c-unused (Types.T-Pair T U) {p = p} uv rel =
  Types.≡c-pair
    (subst-preserves-≡c-unused
      T
      (joinUsage-unused-left
        {u₁ = usageVariance T p}
        {u₂ = usageVariance U p}
        uv)
      rel)
    (subst-preserves-≡c-unused
      U
      (joinUsage-unused-right
        {u₁ = usageVariance T p}
        {u₂ = usageVariance U p}
        uv)
      rel)
subst-preserves-≡c-unused (Types.T-Poly K′ T) uv rel =
  Types.≡c-all (subst-preserves-≡c-unused T uv (lift-≈ᵤ rel))
subst-preserves-≡c-unused (Types.T-Sub K≤K′ T) uv rel =
  Types.≡c-sub K≤K′ (subst-preserves-≡c-unused T uv rel)
subst-preserves-≡c-unused (Types.T-Dual Duality.D-S T) uv rel =
  Types.≡c-trns
    (Types.dual-tinv (T ⋯ _))
    (Types.≡c-trns
      (t-dual-preserves-≡c
        (subst-preserves-≡c-unused T (swapUsage-unused uv) rel))
      (Types.≡c-symm (Types.dual-tinv (T ⋯ _))))
subst-preserves-≡c-unused Types.T-End uv rel = Types.≡c-refl
subst-preserves-≡c-unused (Types.T-Msg Duality.⊕ T S) {p = p} uv rel =
  Types.≡c-msg
    (subst-preserves-≡c-unused
      T
      (swapUsage-unused
        (joinUsage-unused-right
          {u₁ = usageVariance S p}
          {u₂ = swapUsage (usageVariance T p)}
          uv))
      rel)
    (subst-preserves-≡c-unused
      S
      (joinUsage-unused-left
        {u₁ = usageVariance S p}
        {u₂ = swapUsage (usageVariance T p)}
        uv)
      rel)
subst-preserves-≡c-unused (Types.T-Msg Duality.⊝ T S) {p = p} uv rel =
  Types.≡c-msg
    (subst-preserves-≡c-unused
      T
      (joinUsage-unused-right
        {u₁ = usageVariance S p}
        {u₂ = usageVariance T p}
        uv)
      rel)
    (subst-preserves-≡c-unused
      S
      (joinUsage-unused-left
        {u₁ = usageVariance S p}
        {u₂ = usageVariance T p}
        uv)
      rel)
subst-preserves-≡c-unused (Types.T-Up T) uv rel =
  Types.≡c-up (subst-preserves-≡c-unused T uv rel)
subst-preserves-≡c-unused (Types.T-Minus T) uv rel =
  Types.≡c-minus (subst-preserves-≡c-unused T (swapUsage-unused uv) rel)
subst-preserves-≡c-unused (Types.T-ProtoD T) uv rel =
  Types.≡c-protoD (subst-preserves-≡c-unused T uv rel)
subst-preserves-≡c-unused (Types.T-ProtoP #c v T) uv rel =
  Types.≡c-protoP (subst-preserves-≡c-unused T (composeUsage-unused uv) rel)

instantiate-unused-independent :
  ∀ {Δ}
    (T : Ty (KP ∷ []) KP)
    {P Q : Ty Δ KP}
  → usageVariance T (here refl) ≡ unused
  → instantiate ⦃ Kₛ ⦄ Duality.⊕ T P
      Types.≡c
    instantiate ⦃ Kₛ ⦄ Duality.⊕ T Q
instantiate-unused-independent T {P} {Q} uv =
  subst-preserves-≡c-unused
    T
    {p = here refl}
    {ϕ = singletonSubst P}
    {ψ = singletonSubst Q}
    uv
    singletonSubst-≈ᵤ

instantiate-normalized-raw :
  ∀ {Δ K} {p : Duality.Polarity}
    (T : Ty (KP ∷ []) K)
    {P : Ty Δ KP}
  → instantiate ⦃ Kₛ ⦄ p T ⌞ normalizeTy P ⌟
      Types.≡c instantiate ⦃ Kₛ ⦄ p T P
instantiate-normalized-raw T {P} =
  subst-preserves-≡c-pointwise
    {ϕ = singletonSubst ⌞ normalizeTy P ⌟}
    {ψ = singletonSubst P}
    T
    (singletonSubst-≈ₛ
      (Types.≡c-trns
        (Types.≡c-refl-eq (nfProtoTy-fromNormalProto (Types.nf-normal-proto P)))
        (Types.nf-sound+ P)))

normalizeTy-raw :
  ∀ {Δ K}
    (T : Ty Δ K)
  → ⌞ normalizeTy T ⌟ Types.≡c T
normalizeTy-raw {K = KP} T =
  Types.≡c-trns
    (Types.≡c-refl-eq (nfProtoTy-fromNormalProto (Types.nf-normal-proto T)))
    (Types.nf-sound+ T)
normalizeTy-raw {K = KV pk m} T =
  Types.≡c-trns
    (Types.≡c-refl-eq (nfTyTy-fromNormalTy (Types.nf-normal-type Duality.⊕ Duality.d?⊥ T)))
    (Types.nf-sound+ T)

msgNF-raw :
  ∀ {Δ}
    (p : Duality.Polarity)
    (P : NfTy Δ KP)
    (S : NfTy Δ SLin)
  → ⌞ msgNF p P S ⌟ Types.≡c Types.T-Msg p ⌞ P ⌟ ⌞ S ⌟
msgNF-raw p P S =
  Types.≡c-trns
    (Types.≡c-refl-eq (msgNF-sound p P S))
    (Types.t-msg-≡c ⌞ P ⌟)

materializeList-normalized-raw :
  ∀ {Δ}
  (Ts : List (Ty (KP ∷ []) KP))
  {P : Ty Δ KP} {S : Ty Δ SLin}
  → TPC.materializeList Ts Duality.⊕ ⌞ normalizeTy P ⌟ ⌞ normalizeTy S ⌟
      Types.≡c TPC.materializeList Ts Duality.⊕ P S
materializeList-normalized-raw [] {S = S} =
  Types.≡c-trns
    (Types.≡c-refl-eq
      (nfTyTy-fromNormalTy (Types.nf-normal-type Duality.⊕ Duality.d?⊥ S)))
    (Types.nf-sound+ S)
materializeList-normalized-raw (T ∷ Ts) {P} {S} =
  Types.≡c-msg
    (instantiate-normalized-raw {p = Duality.⊕} T {P = P})
    (materializeList-normalized-raw Ts {P} {S})

materialize-normalized-raw :
  ∀ {Δ v}
    (sig : ConstructorSignature v)
    {P : Ty Δ KP} {S : Ty Δ SLin}
  → materialize sig Duality.⊕ ⌞ normalizeTy P ⌟ ⌞ normalizeTy S ⌟
      Types.≡c materialize sig Duality.⊕ P S
materialize-normalized-raw (Ts , uv) {P} {S} =
  materializeList-normalized-raw Ts {P} {S}

materializeListNf-raw :
  ∀ {Δ}
    (Ts : List (Ty (KP ∷ []) KP))
    {P : NfTy Δ KP}
    {S : NfTy Δ SLin}
  → ⌞ materializeListNf Ts Duality.⊕ P S ⌟
      Types.≡c
    TPC.materializeList Ts Duality.⊕ ⌞ P ⌟ ⌞ S ⌟
materializeListNf-raw [] = Types.≡c-refl
materializeListNf-raw (T ∷ Ts) {P} {S} =
  Types.≡c-trns
    (msgNF-raw
      Duality.⊕
      (normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P ⌟))
      (materializeListNf Ts Duality.⊕ P S))
    (Types.≡c-msg
      (normalizeTy-raw (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P ⌟))
      (materializeListNf-raw Ts {P = P} {S = S}))
