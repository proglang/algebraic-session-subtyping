module ExprTypeRenamingPreservationFresh where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using () renaming (here to hereₗ; there to thereₗ)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Maybe using (just; nothing)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ) renaming (suc to sucℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (const)
import Data.Fin.Subset as Subset
open import Data.Vec using (here; there) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Kinds
open import Kits
open import Variance using (Variance)
open import Duality using (Polarity; Dualizable; D-S; ⊕; d?⊥)
open import Types using
  ( Ty
  ; Ty-Syntax
  ; Ty-Traversal
  ; _⋯_
  ; NormalTy
  ; NormalProto
  ; nf
  ; nf-complete
  ; nf-sound+
  ; nf-sound-
  ; nf-idempotent
  ; nfp-idempotent
  ; t-dual
  ; _≡c_
  ; ≡c-refl
  ; ≡c-symm
  ; ≡c-trns
  )
open import SubstitutionSubtyping using (subst-preserves-≡c)
open import NormalTypes using
  ( NFTy
  ; NFProto
  ; NFProto′
  ; NFVar
  ; nfTyTy
  ; nfProtoTy
  ; nfTyTy-injective
  ; nfProtoTy-injective
  ; toNormalTy
  ; toNormalProto
  ; nfTyTy-fromNormalTy
  ; nfProtoTy-fromNormalProto
  )
import NormalTypes as NT
open import NormalTypesRenamings using
  ( renNFTy
  ; renNFProto
  ; renNFProto′
  ; renNFVar
  ; renNFTy-sound
  ; renNFProto-sound
  )
open import ExprSyntax using (NfTy)
open import NormalTypesSubstitution using
  ( NFKind
  ; NFSub
  ; nfVarKind
  ; wkNFKind
  ; wkNFSub
  ; singleNFSub
  ; dualNFKind
  ; minusNF
  ; msgNF
  ; substNFProto′With
  ; substNFProtoWith
  ; substNFVarWith
  ; substNFTyWith
  ; substNFTy
  )
open import ExprNormalTyping using (normalizeTy; materializeListNf; BranchJoin⁺)
open import TypesProtocolConstructors using
  ( ProtocolConstructors
  ; singletonSubst
  ; instantiate
  )
open import TypesProperties using
  ( InjectiveRenaming
  ; injective-↑ᵣ
  ; renaming-injective
  ; weakenᵣ-injective
  )
open import AlgorithmicNFSubtyping using (_<:ₜ_)
open import AlgorithmicNFMerge using (joinₜ)
open import AlgorithmicNFLubGlb using (lub-joinₜ)
open import AlgorithmicNFSound using (<:ₜ-antisym)
open import ExprTypingStrengthening using
  ( ren-preserves-<:ₜ
  ; split-renTy-to-sub
  )
open import ExprSyntax using
  ( Expr
  ; Value
  ; E-TApp
  )
open import ExprSubstitution using
  ( renNfTy
  ; renTyValue
  ; renTyExpr
  ; wkTyValue
  ; wkTyExpr
  )
open import ExprNormalTyping using
  ( Binding
  ; B-Lin
  ; B-Un
  ; B-Used
  ; Ctx
  ; ∅
  ; _▻_
  ; wkBinding
  ; wkCtx
  ; wkNfTy
  ; _∋ᵘ_∶_
  ; hereᵘ
  ; thereᵘˡ
  ; thereᵘᵘ
  ; thereᵘ✖
  ; _⊢ˡ_∶_⊣_
  ; take-here
  ; take-thereˡ
  ; take-thereᵘ
  ; take-there✖
  ; ConstTy
  ; CT-Unit
  ; CT-Fork
  ; CT-New
  ; CT-Receive
  ; CT-Send
  ; CT-Close
  ; CT-Select
  ; _⊢ᵥ_⇒_⊣_
  ; TV-Const
  ; TV-Var-Lin
  ; TV-Var-Un
  ; TV-Abs
  ; TV-Rec
  ; TV-TAbs
  ; TV-Pair
  ; TV-Receive₁
  ; TV-Receive₂
  ; TV-Send₁
  ; TV-Send₂
  ; TV-Select₁
  ; TV-Select₂
  ; _⊢_⇒_⊣_
  ; T-Val
  ; T-Pair
  ; T-App
  ; T-LetUnit
  ; T-LetPair
  ; T-Match
  ; T-TApp
  ; _⊢_⇐_⊣_
  ; T-Check
  ; unitConstNf
  ; forkConstNf
  ; newConstNf
  ; receiveConstNf
  ; sendConstNf
  ; closeConstNf
  ; selectConstNf
  ; receive1Nf
  ; receiveNf
  ; send1Nf
  ; sendNf
  ; select1Nf
  ; selectNf
  ; MatchBranchInput
  ; MatchBranchOutput
  )

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (_⋯_; ⋯-id)

ren-normalizeTy :
  ∀ {Δ₁ Δ₂ pk m}
    (ρ : Δ₁ →ᵣ Δ₂)
    (T : Ty Δ₁ (KV pk m))
  → renNFTy ρ (normalizeTy T) ≡ normalizeTy (T ⋯ ρ)
ren-normalizeTy ρ T =
  nfTyTy-injective
    (trans
      eq-normal
      (trans
        (sym (nf-idempotent renamed-normal))
        (trans
          (nf-complete d?⊥ d?⊥
            (subst-preserves-≡c (nf-sound+ T) ρ))
          (sym
            (nfTyTy-fromNormalTy
              (Types.nf-normal-type ⊕ d?⊥ (T ⋯ ρ)))))))
  where
  eq-normal :
    nfTyTy (renNFTy ρ (normalizeTy T)) ≡ nf ⊕ d?⊥ T ⋯ ρ
  eq-normal =
    trans
      (renNFTy-sound ρ (normalizeTy T))
      (cong (_⋯ ρ)
        (nfTyTy-fromNormalTy
          (Types.nf-normal-type ⊕ d?⊥ T)))

  renamed-normal : NormalTy (nf ⊕ d?⊥ T ⋯ ρ)
  renamed-normal =
    subst NormalTy eq-normal
      (toNormalTy (renNFTy ρ (normalizeTy T)))

ren-normalizeProto :
  ∀ {Δ₁ Δ₂}
    (ρ : Δ₁ →ᵣ Δ₂)
    (P : Ty Δ₁ KP)
  → renNFProto ρ (normalizeTy P) ≡ normalizeTy (P ⋯ ρ)
ren-normalizeProto ρ P =
  nfProtoTy-injective
    (trans
      eq-normal
      (trans
        (sym (nfp-idempotent renamed-normal))
        (trans
          (nf-complete d?⊥ d?⊥
            (subst-preserves-≡c (nf-sound+ P) ρ))
          (sym
            (nfProtoTy-fromNormalProto
              (Types.nf-normal-proto (P ⋯ ρ)))))))
  where
  eq-normal :
    nfProtoTy (renNFProto ρ (normalizeTy P)) ≡ nf ⊕ d?⊥ P ⋯ ρ
  eq-normal =
    trans
      (renNFProto-sound ρ (normalizeTy P))
      (cong (_⋯ ρ)
        (nfProtoTy-fromNormalProto
          (Types.nf-normal-proto P)))

  renamed-normal : NormalProto (nf ⊕ d?⊥ P ⋯ ρ)
  renamed-normal =
    subst NormalProto eq-normal
      (toNormalProto (renNFProto ρ (normalizeTy P)))

ren-t-dual :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (d : Dualizable K)
    (T : Ty Δ₁ K)
  → t-dual d T ⋯ ρ ≡ t-dual d (T ⋯ ρ)
ren-t-dual ρ D-S (Types.T-Var x) = refl
ren-t-dual ρ D-S (Types.T-Sub K≤K′ T) =
  cong (Types.T-Sub K≤K′)
    (ren-t-dual ρ (Duality.dualizable-sub D-S K≤K′) T)
ren-t-dual ρ D-S (Types.T-Dual D-S T) = refl
ren-t-dual ρ D-S Types.T-End = refl
ren-t-dual ρ D-S (Types.T-Msg p P S) =
  cong₂ (Types.T-Msg _)
    refl
    (ren-t-dual ρ D-S S)

ren-normalizeTy-minus :
  ∀ {Δ₁ Δ₂ m}
    (ρ : Δ₁ →ᵣ Δ₂)
    (f : Dualizable (KV KS m))
    (T : Ty Δ₁ (KV KS m))
  → renNFTy ρ
      (NormalTypes.nf-normal-type Polarity.⊝ (const f) T)
      ≡
    NormalTypes.nf-normal-type Polarity.⊝ (const f) (T ⋯ ρ)
ren-normalizeTy-minus ρ f T =
  nfTyTy-injective
    (trans
      left-eq
      (trans
        (sym (nf-idempotent left-normal))
        (trans
          (nf-complete d?⊥ d?⊥ converted)
          (trans
            (nf-idempotent right-normal)
            (sym (nfTyTy-fromNormalTy right-normal))))))
  where
  left-eq :
    nfTyTy
      (renNFTy ρ
        (NormalTypes.nf-normal-type Polarity.⊝ (const f) T))
      ≡
    nf Polarity.⊝ (const f) T ⋯ ρ
  left-eq =
    trans
      (renNFTy-sound ρ
        (NormalTypes.nf-normal-type Polarity.⊝ (const f) T))
      (cong (_⋯ ρ)
        (nfTyTy-fromNormalTy
          (Types.nf-normal-type Polarity.⊝ (const f) T)))

  dual-eq :
    (nf Polarity.⊝ (const f) T ⋯ ρ)
      ≡c
    t-dual D-S (T ⋯ ρ)
  dual-eq =
    subst
      (λ X → (nf Polarity.⊝ (const f) T ⋯ ρ) ≡c X)
      (ren-t-dual ρ D-S T)
      (subst-preserves-≡c (nf-sound- T) ρ)

  converted :
    (nf Polarity.⊝ (const f) T ⋯ ρ)
      ≡c
    nf Polarity.⊝ (const f) (T ⋯ ρ)
  converted =
    ≡c-trns
      dual-eq
      (≡c-symm (nf-sound- (T ⋯ ρ)))

  left-normal :
    NormalTy (nf Polarity.⊝ (const f) T ⋯ ρ)
  left-normal =
    subst NormalTy left-eq
      (toNormalTy
        (renNFTy ρ
          (NormalTypes.nf-normal-type Polarity.⊝ (const f) T)))

  right-normal :
    NormalTy (nf Polarity.⊝ (const f) (T ⋯ ρ))
  right-normal =
    Types.nf-normal-type Polarity.⊝ (const f) (T ⋯ ρ)

infix 4 _≈ᵣ_

_≈ᵣ_ :
  ∀ {Δ₁ Δ₂}
  → (Δ₁ →ᵣ Δ₂)
  → (Δ₁ →ᵣ Δ₂)
  → Set
ρ ≈ᵣ ψ = ∀ K (x : K ∈ _) → ρ K x ≡ ψ K x

lift-≈ᵣ :
  ∀ {Δ₁ Δ₂ K}
    {ρ ψ : Δ₁ →ᵣ Δ₂}
  → ρ ≈ᵣ ψ
  → (ρ ↑ᵣ K) ≈ᵣ (ψ ↑ᵣ K)
lift-≈ᵣ rel K′ (hereₗ refl) = refl
lift-≈ᵣ rel K′ (thereₗ x) = cong thereₗ (rel K′ x)

mutual

  renNFProto′-cong :
    ∀ {Δ₁ Δ₂}
      (P : NFProto′ Δ₁)
      {ρ ψ : Δ₁ →ᵣ Δ₂}
    → ρ ≈ᵣ ψ
    → renNFProto′ ρ P ≡ renNFProto′ ψ P
  renNFProto′-cong (NT.N-ProtoP ss v P) rel =
    cong (NT.N-ProtoP ss v) (renNFProto-cong P rel)
  renNFProto′-cong (NT.N-Up T) rel =
    cong NT.N-Up (renNFTy-cong T rel)
  renNFProto′-cong (NT.N-Var x) rel =
    cong NT.N-Var (rel _ x)

  renNFProto-cong :
    ∀ {Δ₁ Δ₂}
      (P : NFProto Δ₁)
      {ρ ψ : Δ₁ →ᵣ Δ₂}
    → ρ ≈ᵣ ψ
    → renNFProto ρ P ≡ renNFProto ψ P
  renNFProto-cong (NT.N-Normal P) rel =
    cong NT.N-Normal (renNFProto′-cong P rel)
  renNFProto-cong (NT.N-Minus P) rel =
    cong NT.N-Minus (renNFProto′-cong P rel)

  renNFVar-cong :
    ∀ {Δ₁ Δ₂ K}
      (V : NFVar Δ₁ K)
      {ρ ψ : Δ₁ →ᵣ Δ₂}
    → ρ ≈ᵣ ψ
    → renNFVar ρ V ≡ renNFVar ψ V
  renNFVar-cong (NT.NV-Var x) rel =
    cong NT.NV-Var (rel _ x)
  renNFVar-cong (NT.NV-Dual d x) rel =
    cong (NT.NV-Dual d) (rel _ x)

  renNFTy-cong :
    ∀ {Δ₁ Δ₂ K}
      (T : NFTy Δ₁ K)
      {ρ ψ : Δ₁ →ᵣ Δ₂}
    → ρ ≈ᵣ ψ
    → renNFTy ρ T ≡ renNFTy ψ T
  renNFTy-cong (NT.N-Var V) rel =
    cong NT.N-Var (renNFVar-cong V rel)
  renNFTy-cong NT.N-Base rel = refl
  renNFTy-cong (NT.N-Arrow T U) rel =
    cong₂ NT.N-Arrow
      (renNFTy-cong T rel)
      (renNFTy-cong U rel)
  renNFTy-cong (NT.N-Pair T U) rel =
    cong₂ NT.N-Pair
      (renNFTy-cong T rel)
      (renNFTy-cong U rel)
  renNFTy-cong (NT.N-Poly K T) rel =
    cong (NT.N-Poly K) (renNFTy-cong T (lift-≈ᵣ rel))
  renNFTy-cong (NT.N-Sub K≤K′ T) rel =
    cong (NT.N-Sub K≤K′) (renNFTy-cong T rel)
  renNFTy-cong NT.N-End rel = refl
  renNFTy-cong (NT.N-Msg p P S) rel =
    cong₂ (NT.N-Msg p)
      (renNFProto′-cong P rel)
      (renNFTy-cong S rel)
  renNFTy-cong (NT.N-ProtoD T) rel =
    cong NT.N-ProtoD (renNFTy-cong T rel)

renTy-cong :
  ∀ {Δ₁ Δ₂ K}
    (T : Ty Δ₁ K)
    {ρ ψ : Δ₁ →ᵣ Δ₂}
  → ρ ≈ᵣ ψ
  → T ⋯ ρ ≡ T ⋯ ψ
renTy-cong (Types.T-Var x) rel = cong Types.T-Var (rel _ x)
renTy-cong Types.T-Base rel = refl
renTy-cong (Types.T-Arrow T U) rel =
  cong₂ Types.T-Arrow (renTy-cong T rel) (renTy-cong U rel)
renTy-cong (Types.T-Pair T U) rel =
  cong₂ Types.T-Pair (renTy-cong T rel) (renTy-cong U rel)
renTy-cong (Types.T-Poly K T) rel =
  cong (Types.T-Poly K) (renTy-cong T (lift-≈ᵣ rel))
renTy-cong (Types.T-Sub K≤K′ T) rel =
  cong (Types.T-Sub K≤K′) (renTy-cong T rel)
renTy-cong (Types.T-Dual d T) rel =
  cong (Types.T-Dual d) (renTy-cong T rel)
renTy-cong Types.T-End rel = refl
renTy-cong (Types.T-Msg p P S) rel =
  cong₂ (Types.T-Msg p) (renTy-cong P rel) (renTy-cong S rel)
renTy-cong (Types.T-Up T) rel =
  cong Types.T-Up (renTy-cong T rel)
renTy-cong (Types.T-Minus P) rel =
  cong Types.T-Minus (renTy-cong P rel)
renTy-cong (Types.T-ProtoD T) rel =
  cong Types.T-ProtoD (renTy-cong T rel)
renTy-cong (Types.T-ProtoP ss v P) rel =
  cong (Types.T-ProtoP ss v) (renTy-cong P rel)

composeRen :
  ∀ {Δ₁ Δ₂ Δ₃}
  → (Δ₁ →ᵣ Δ₂)
  → (Δ₂ →ᵣ Δ₃)
  → (Δ₁ →ᵣ Δ₃)
composeRen ρ ψ K x = ψ K (ρ K x)

lift-composeRen :
  ∀ {Δ₁ Δ₂ Δ₃ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (ψ : Δ₂ →ᵣ Δ₃)
  → composeRen (ρ ↑ᵣ K) (ψ ↑ᵣ K)
      ≈ᵣ
    (composeRen ρ ψ ↑ᵣ K)
lift-composeRen ρ ψ K′ (hereₗ refl) = refl
lift-composeRen ρ ψ K′ (thereₗ x) = refl

renTy-compose :
  ∀ {Δ₁ Δ₂ Δ₃ K}
    (T : Ty Δ₁ K)
    (ρ : Δ₁ →ᵣ Δ₂)
    (ψ : Δ₂ →ᵣ Δ₃)
  → (T ⋯ ρ) ⋯ ψ ≡ T ⋯ composeRen ρ ψ
renTy-compose (Types.T-Var x) ρ ψ = refl
renTy-compose Types.T-Base ρ ψ = refl
renTy-compose (Types.T-Arrow T U) ρ ψ =
  cong₂ Types.T-Arrow
    (renTy-compose T ρ ψ)
    (renTy-compose U ρ ψ)
renTy-compose (Types.T-Pair T U) ρ ψ =
  cong₂ Types.T-Pair
    (renTy-compose T ρ ψ)
    (renTy-compose U ρ ψ)
renTy-compose (Types.T-Poly K T) ρ ψ =
  cong (Types.T-Poly K)
    (trans
      (renTy-compose T (ρ ↑ᵣ K) (ψ ↑ᵣ K))
      (renTy-cong T (lift-composeRen ρ ψ)))
renTy-compose (Types.T-Sub K≤K′ T) ρ ψ =
  cong (Types.T-Sub K≤K′) (renTy-compose T ρ ψ)
renTy-compose (Types.T-Dual d T) ρ ψ =
  cong (Types.T-Dual d) (renTy-compose T ρ ψ)
renTy-compose Types.T-End ρ ψ = refl
renTy-compose (Types.T-Msg p P S) ρ ψ =
  cong₂ (Types.T-Msg p)
    (renTy-compose P ρ ψ)
    (renTy-compose S ρ ψ)
renTy-compose (Types.T-Up T) ρ ψ =
  cong Types.T-Up (renTy-compose T ρ ψ)
renTy-compose (Types.T-Minus P) ρ ψ =
  cong Types.T-Minus (renTy-compose P ρ ψ)
renTy-compose (Types.T-ProtoD T) ρ ψ =
  cong Types.T-ProtoD (renTy-compose T ρ ψ)
renTy-compose (Types.T-ProtoP ss v P) ρ ψ =
  cong (Types.T-ProtoP ss v) (renTy-compose P ρ ψ)

mutual

  renNFProto′-compose :
    ∀ {Δ₁ Δ₂ Δ₃}
      (P : NFProto′ Δ₁)
      (ρ : Δ₁ →ᵣ Δ₂)
      (ψ : Δ₂ →ᵣ Δ₃)
    → renNFProto′ ψ (renNFProto′ ρ P)
        ≡
      renNFProto′ (composeRen ρ ψ) P
  renNFProto′-compose (NT.N-ProtoP ss v P) ρ ψ =
    cong (NT.N-ProtoP ss v) (renNFProto-compose P ρ ψ)
  renNFProto′-compose (NT.N-Up T) ρ ψ =
    cong NT.N-Up (renNFTy-compose T ρ ψ)
  renNFProto′-compose (NT.N-Var x) ρ ψ = refl

  renNFProto-compose :
    ∀ {Δ₁ Δ₂ Δ₃}
      (P : NFProto Δ₁)
      (ρ : Δ₁ →ᵣ Δ₂)
      (ψ : Δ₂ →ᵣ Δ₃)
    → renNFProto ψ (renNFProto ρ P)
        ≡
      renNFProto (composeRen ρ ψ) P
  renNFProto-compose (NT.N-Normal P) ρ ψ =
    cong NT.N-Normal (renNFProto′-compose P ρ ψ)
  renNFProto-compose (NT.N-Minus P) ρ ψ =
    cong NT.N-Minus (renNFProto′-compose P ρ ψ)

  renNFVar-compose :
    ∀ {Δ₁ Δ₂ Δ₃ K}
      (V : NFVar Δ₁ K)
      (ρ : Δ₁ →ᵣ Δ₂)
      (ψ : Δ₂ →ᵣ Δ₃)
    → renNFVar ψ (renNFVar ρ V)
        ≡
      renNFVar (composeRen ρ ψ) V
  renNFVar-compose (NT.NV-Var x) ρ ψ = refl
  renNFVar-compose (NT.NV-Dual d x) ρ ψ = refl

  renNFTy-compose :
    ∀ {Δ₁ Δ₂ Δ₃ K}
      (T : NFTy Δ₁ K)
      (ρ : Δ₁ →ᵣ Δ₂)
      (ψ : Δ₂ →ᵣ Δ₃)
    → renNFTy ψ (renNFTy ρ T)
        ≡
      renNFTy (composeRen ρ ψ) T
  renNFTy-compose (NT.N-Var V) ρ ψ =
    cong NT.N-Var (renNFVar-compose V ρ ψ)
  renNFTy-compose NT.N-Base ρ ψ = refl
  renNFTy-compose (NT.N-Arrow T U) ρ ψ =
    cong₂ NT.N-Arrow
      (renNFTy-compose T ρ ψ)
      (renNFTy-compose U ρ ψ)
  renNFTy-compose (NT.N-Pair T U) ρ ψ =
    cong₂ NT.N-Pair
      (renNFTy-compose T ρ ψ)
      (renNFTy-compose U ρ ψ)
  renNFTy-compose (NT.N-Poly K T) ρ ψ =
    cong (NT.N-Poly K)
      (trans
        (renNFTy-compose T (ρ ↑ᵣ K) (ψ ↑ᵣ K))
        (renNFTy-cong T (lift-composeRen ρ ψ)))
  renNFTy-compose (NT.N-Sub K≤K′ T) ρ ψ =
    cong (NT.N-Sub K≤K′) (renNFTy-compose T ρ ψ)
  renNFTy-compose NT.N-End ρ ψ = refl
  renNFTy-compose (NT.N-Msg p P S) ρ ψ =
    cong₂ (NT.N-Msg p)
      (renNFProto′-compose P ρ ψ)
      (renNFTy-compose S ρ ψ)
  renNFTy-compose (NT.N-ProtoD T) ρ ψ =
    cong NT.N-ProtoD (renNFTy-compose T ρ ψ)

renTy-wk-comm :
  ∀ {Δ₁ Δ₂ K K′}
    (ρ : Δ₁ →ᵣ Δ₂)
    (T : Ty Δ₁ K)
  → (T ⋯ weakenᵣ K′) ⋯ (ρ ↑ᵣ K′)
      ≡
    (T ⋯ ρ) ⋯ weakenᵣ K′
renTy-wk-comm ρ T =
  trans
    (renTy-compose T (weakenᵣ _) (ρ ↑ᵣ _))
    (sym (renTy-compose T ρ (weakenᵣ _)))

renNFTy-wk-comm :
  ∀ {Δ₁ Δ₂ K K′}
    (ρ : Δ₁ →ᵣ Δ₂)
    (T : NFTy Δ₁ K)
  → renNFTy (ρ ↑ᵣ K′) (renNFTy (weakenᵣ K′) T)
      ≡
    renNFTy (weakenᵣ K′) (renNFTy ρ T)
renNFTy-wk-comm ρ T =
  trans
    (renNFTy-compose T (weakenᵣ _) (ρ ↑ᵣ _))
    (sym (renNFTy-compose T ρ (weakenᵣ _)))

renNFProto-wk-comm :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (P : NFProto Δ₁)
  → renNFProto (ρ ↑ᵣ K) (renNFProto (weakenᵣ K) P)
      ≡
    renNFProto (weakenᵣ K) (renNFProto ρ P)
renNFProto-wk-comm ρ P =
  trans
    (renNFProto-compose P (weakenᵣ _) (ρ ↑ᵣ _))
    (sym (renNFProto-compose P ρ (weakenᵣ _)))

renNFKind :
  ∀ {Δ₁ Δ₂ K}
  → (Δ₁ →ᵣ Δ₂)
  → NFKind Δ₁ K
  → NFKind Δ₂ K
renNFKind {K = KP} = renNFProto
renNFKind {K = KV pk m} = renNFTy

renNFKind-wk-comm :
  ∀ {Δ₁ Δ₂ K K′}
    (ρ : Δ₁ →ᵣ Δ₂)
    (N : NFKind Δ₁ K)
  → renNFKind (ρ ↑ᵣ K′) (wkNFKind {K′ = K′} N)
      ≡
    wkNFKind {K′ = K′} (renNFKind ρ N)
renNFKind-wk-comm {K = KP} ρ N =
  renNFProto-wk-comm ρ N
renNFKind-wk-comm {K = KV pk m} ρ N =
  renNFTy-wk-comm ρ N

ren-minusNF :
  ∀ {Δ₁ Δ₂}
    (ρ : Δ₁ →ᵣ Δ₂)
    (P : NFProto Δ₁)
  → renNFProto ρ (minusNF P)
      ≡
    minusNF (renNFProto ρ P)
ren-minusNF ρ (NT.N-Normal P) = refl
ren-minusNF ρ (NT.N-Minus P) = refl

ren-msgNF′ :
  ∀ {Δ₁ Δ₂}
    (ρ : Δ₁ →ᵣ Δ₂)
    (p : Polarity)
    (P : NFProto Δ₁)
    (S : NFTy Δ₁ SLin)
  → renNFTy ρ (msgNF p P S)
      ≡
    msgNF p (renNFProto ρ P) (renNFTy ρ S)
ren-msgNF′ ρ p (NT.N-Normal P) S = refl
ren-msgNF′ ρ p (NT.N-Minus P) S = refl

ren-dualNFKind :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (d : Dualizable K)
    (N : NFKind Δ₁ K)
  → renNFKind ρ (dualNFKind d N)
      ≡
    dualNFKind d (renNFKind ρ N)
ren-dualNFKind ρ D-S (NT.N-Var (NT.NV-Var x)) = refl
ren-dualNFKind ρ D-S N =
  trans
    (ren-normalizeTy-minus ρ D-S (nfTyTy N))
    (cong
      (NormalTypes.nf-normal-type Polarity.⊝ (const D-S))
      (sym (renNFTy-sound ρ N)))

NFSubRenRel :
  ∀ {Δ₁ Δ₂ Δ₃}
  → NFSub Δ₁ Δ₂
  → (Δ₂ →ᵣ Δ₃)
  → NFSub Δ₁ Δ₃
  → Set
NFSubRenRel σ ρ τ =
  ∀ K (x : K ∈ _) → renNFKind ρ (σ K x) ≡ τ K x

ren-nfVarKind :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (x : K ∈ Δ₁)
  → renNFKind ρ (nfVarKind x) ≡ nfVarKind (ρ K x)
ren-nfVarKind {K = KP} ρ x = refl
ren-nfVarKind {K = KV pk m} ρ x = refl

lift-NFSubRenRel :
  ∀ {Δ₁ Δ₂ Δ₃ K}
    {σ : NFSub Δ₁ Δ₂}
    {ρ : Δ₂ →ᵣ Δ₃}
    {τ : NFSub Δ₁ Δ₃}
  → NFSubRenRel σ ρ τ
  → NFSubRenRel (wkNFSub {K = K} σ) (ρ ↑ᵣ K) (wkNFSub {K = K} τ)
lift-NFSubRenRel {ρ = ρ} rel K′ (hereₗ refl) =
  ren-nfVarKind (ρ ↑ᵣ _) (hereₗ refl)
lift-NFSubRenRel {K = K} {σ = σ} {ρ = ρ} rel K′ (thereₗ x) =
  trans
    (renNFKind-wk-comm ρ (σ K′ x))
    (cong (wkNFKind {K′ = K}) (rel K′ x))

mutual

  ren-substNFProto′ :
    ∀ {Δ₁ Δ₂ Δ₃}
      (ρ : Δ₂ →ᵣ Δ₃)
      (σ : NFSub Δ₁ Δ₂)
      (τ : NFSub Δ₁ Δ₃)
      (P : NFProto′ Δ₁)
    → NFSubRenRel σ ρ τ
    → renNFProto ρ (substNFProto′With σ P)
        ≡
      substNFProto′With τ P
  ren-substNFProto′ ρ σ τ (NT.N-ProtoP ss v P) rel =
    cong (λ Q → NT.N-Normal (NT.N-ProtoP ss v Q))
      (ren-substNFProto ρ σ τ P rel)
  ren-substNFProto′ ρ σ τ (NT.N-Up T) rel =
    cong (λ U → NT.N-Normal (NT.N-Up U))
      (ren-substNFTy ρ σ τ T rel)
  ren-substNFProto′ ρ σ τ (NT.N-Var x) rel =
    rel _ x

  ren-substNFProto :
    ∀ {Δ₁ Δ₂ Δ₃}
      (ρ : Δ₂ →ᵣ Δ₃)
      (σ : NFSub Δ₁ Δ₂)
      (τ : NFSub Δ₁ Δ₃)
      (P : NFProto Δ₁)
    → NFSubRenRel σ ρ τ
    → renNFProto ρ (substNFProtoWith σ P)
        ≡
      substNFProtoWith τ P
  ren-substNFProto ρ σ τ (NT.N-Normal P) rel =
    ren-substNFProto′ ρ σ τ P rel
  ren-substNFProto ρ σ τ (NT.N-Minus P) rel =
    trans
      (ren-minusNF ρ (substNFProto′With σ P))
      (cong minusNF (ren-substNFProto′ ρ σ τ P rel))

  ren-substNFVar :
    ∀ {Δ₁ Δ₂ Δ₃ K}
      (ρ : Δ₂ →ᵣ Δ₃)
      (σ : NFSub Δ₁ Δ₂)
      (τ : NFSub Δ₁ Δ₃)
      (V : NFVar Δ₁ K)
    → NFSubRenRel σ ρ τ
    → renNFKind ρ (substNFVarWith σ V)
        ≡
      substNFVarWith τ V
  ren-substNFVar ρ σ τ (NT.NV-Var x) rel =
    rel _ x
  ren-substNFVar ρ σ τ (NT.NV-Dual d x) rel =
    trans
      (ren-dualNFKind ρ d (σ _ x))
      (cong (dualNFKind d) (rel _ x))

  ren-substNFTy :
    ∀ {Δ₁ Δ₂ Δ₃ K}
      (ρ : Δ₂ →ᵣ Δ₃)
      (σ : NFSub Δ₁ Δ₂)
      (τ : NFSub Δ₁ Δ₃)
      (T : NFTy Δ₁ K)
    → NFSubRenRel σ ρ τ
    → renNFTy ρ (substNFTyWith σ T)
        ≡
      substNFTyWith τ T
  ren-substNFTy ρ σ τ (NT.N-Var V) rel =
    ren-substNFVar ρ σ τ V rel
  ren-substNFTy ρ σ τ NT.N-Base rel = refl
  ren-substNFTy ρ σ τ (NT.N-Arrow T U) rel =
    cong₂ NT.N-Arrow
      (ren-substNFTy ρ σ τ T rel)
      (ren-substNFTy ρ σ τ U rel)
  ren-substNFTy ρ σ τ (NT.N-Pair T U) rel =
    cong₂ NT.N-Pair
      (ren-substNFTy ρ σ τ T rel)
      (ren-substNFTy ρ σ τ U rel)
  ren-substNFTy ρ σ τ (NT.N-Poly K T) rel =
    cong (NT.N-Poly K)
      (ren-substNFTy
        (ρ ↑ᵣ K)
        (wkNFSub {K = K} σ)
        (wkNFSub {K = K} τ)
        T
        (lift-NFSubRenRel {K = K} rel))
  ren-substNFTy ρ σ τ (NT.N-Sub K≤K′ T) rel =
    cong (NT.N-Sub K≤K′) (ren-substNFTy ρ σ τ T rel)
  ren-substNFTy ρ σ τ NT.N-End rel = refl
  ren-substNFTy ρ σ τ (NT.N-Msg p P S) rel =
    trans
      (ren-msgNF′ ρ p
        (substNFProto′With σ P)
        (substNFTyWith σ S))
      (cong₂ (msgNF p)
        (ren-substNFProto′ ρ σ τ P rel)
        (ren-substNFTy ρ σ τ S rel))
  ren-substNFTy ρ σ τ (NT.N-ProtoD T) rel =
    cong NT.N-ProtoD (ren-substNFTy ρ σ τ T rel)

RenNFSubRel :
  ∀ {Δ₁ Δ₂ Δ₃}
  → (Δ₁ →ᵣ Δ₂)
  → NFSub Δ₂ Δ₃
  → NFSub Δ₁ Δ₃
  → Set
RenNFSubRel ρ σ τ =
  ∀ K (x : K ∈ _) → σ K (ρ K x) ≡ τ K x

lift-RenNFSubRel :
  ∀ {Δ₁ Δ₂ Δ₃ K}
    {ρ : Δ₁ →ᵣ Δ₂}
    {σ : NFSub Δ₂ Δ₃}
    {τ : NFSub Δ₁ Δ₃}
  → RenNFSubRel ρ σ τ
  → RenNFSubRel (ρ ↑ᵣ K) (wkNFSub {K = K} σ) (wkNFSub {K = K} τ)
lift-RenNFSubRel rel K′ (hereₗ refl) = refl
lift-RenNFSubRel rel K′ (thereₗ x) =
  cong (wkNFKind {K′ = _}) (rel K′ x)

mutual

  subst-renNFProto′ :
    ∀ {Δ₁ Δ₂ Δ₃}
      (ρ : Δ₁ →ᵣ Δ₂)
      (σ : NFSub Δ₂ Δ₃)
      (τ : NFSub Δ₁ Δ₃)
      (P : NFProto′ Δ₁)
    → RenNFSubRel ρ σ τ
    → substNFProto′With σ (renNFProto′ ρ P)
        ≡
      substNFProto′With τ P
  subst-renNFProto′ ρ σ τ (NT.N-ProtoP ss v P) rel =
    cong (λ Q → NT.N-Normal (NT.N-ProtoP ss v Q))
      (subst-renNFProto ρ σ τ P rel)
  subst-renNFProto′ ρ σ τ (NT.N-Up T) rel =
    cong (λ U → NT.N-Normal (NT.N-Up U))
      (subst-renNFTy ρ σ τ T rel)
  subst-renNFProto′ ρ σ τ (NT.N-Var x) rel =
    rel _ x

  subst-renNFProto :
    ∀ {Δ₁ Δ₂ Δ₃}
      (ρ : Δ₁ →ᵣ Δ₂)
      (σ : NFSub Δ₂ Δ₃)
      (τ : NFSub Δ₁ Δ₃)
      (P : NFProto Δ₁)
    → RenNFSubRel ρ σ τ
    → substNFProtoWith σ (renNFProto ρ P)
        ≡
      substNFProtoWith τ P
  subst-renNFProto ρ σ τ (NT.N-Normal P) rel =
    subst-renNFProto′ ρ σ τ P rel
  subst-renNFProto ρ σ τ (NT.N-Minus P) rel =
    cong minusNF (subst-renNFProto′ ρ σ τ P rel)

  subst-renNFVar :
    ∀ {Δ₁ Δ₂ Δ₃ K}
      (ρ : Δ₁ →ᵣ Δ₂)
      (σ : NFSub Δ₂ Δ₃)
      (τ : NFSub Δ₁ Δ₃)
      (V : NFVar Δ₁ K)
    → RenNFSubRel ρ σ τ
    → substNFVarWith σ (renNFVar ρ V)
        ≡
      substNFVarWith τ V
  subst-renNFVar ρ σ τ (NT.NV-Var x) rel =
    rel _ x
  subst-renNFVar ρ σ τ (NT.NV-Dual d x) rel =
    cong (dualNFKind d) (rel _ x)

  subst-renNFTy :
    ∀ {Δ₁ Δ₂ Δ₃ K}
      (ρ : Δ₁ →ᵣ Δ₂)
      (σ : NFSub Δ₂ Δ₃)
      (τ : NFSub Δ₁ Δ₃)
      (T : NFTy Δ₁ K)
    → RenNFSubRel ρ σ τ
    → substNFTyWith σ (renNFTy ρ T)
        ≡
      substNFTyWith τ T
  subst-renNFTy ρ σ τ (NT.N-Var V) rel =
    subst-renNFVar ρ σ τ V rel
  subst-renNFTy ρ σ τ NT.N-Base rel = refl
  subst-renNFTy ρ σ τ (NT.N-Arrow T U) rel =
    cong₂ NT.N-Arrow
      (subst-renNFTy ρ σ τ T rel)
      (subst-renNFTy ρ σ τ U rel)
  subst-renNFTy ρ σ τ (NT.N-Pair T U) rel =
    cong₂ NT.N-Pair
      (subst-renNFTy ρ σ τ T rel)
      (subst-renNFTy ρ σ τ U rel)
  subst-renNFTy ρ σ τ (NT.N-Poly K T) rel =
    cong (NT.N-Poly K)
      (subst-renNFTy
        (ρ ↑ᵣ K)
        (wkNFSub {K = K} σ)
        (wkNFSub {K = K} τ)
        T
        (lift-RenNFSubRel {K = K} rel))
  subst-renNFTy ρ σ τ (NT.N-Sub K≤K′ T) rel =
    cong (NT.N-Sub K≤K′) (subst-renNFTy ρ σ τ T rel)
  subst-renNFTy ρ σ τ NT.N-End rel = refl
  subst-renNFTy ρ σ τ (NT.N-Msg p P S) rel =
    cong₂ (msgNF p)
      (subst-renNFProto′ ρ σ τ P rel)
      (subst-renNFTy ρ σ τ S rel)
  subst-renNFTy ρ σ τ (NT.N-ProtoD T) rel =
    cong NT.N-ProtoD (subst-renNFTy ρ σ τ T rel)

single-renNFSub :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (U : NFKind Δ₁ K)
  → NFSub (K ∷ Δ₁) Δ₂
single-renNFSub ρ U K′ x =
  renNFKind ρ (singleNFSub U K′ x)

single-ren-left :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (U : NFKind Δ₁ K)
  → NFSubRenRel
      (singleNFSub U)
      ρ
      (single-renNFSub ρ U)
single-ren-left ρ U K′ x = refl

single-ren-right :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (U : NFKind Δ₁ K)
  → RenNFSubRel
      (ρ ↑ᵣ K)
      (singleNFSub (renNFKind ρ U))
      (single-renNFSub ρ U)
single-ren-right ρ U K′ (hereₗ refl) = refl
single-ren-right ρ U K′ (thereₗ x) =
  sym (ren-nfVarKind ρ x)

substNFTy-ren :
  ∀ {Δ₁ Δ₂ K K′}
    (ρ : Δ₁ →ᵣ Δ₂)
    (T : NFTy (K ∷ Δ₁) K′)
    (U : NFKind Δ₁ K)
  → renNFTy ρ (substNFTy T U)
      ≡
    substNFTy
      (renNFTy (ρ ↑ᵣ K) T)
      (renNFKind ρ U)
substNFTy-ren ρ T U =
  trans
    (ren-substNFTy
      ρ
      (singleNFSub U)
      (single-renNFSub ρ U)
      T
      (single-ren-left ρ U))
    (sym
      (subst-renNFTy
        (ρ ↑ᵣ _)
        (singleNFSub (renNFKind ρ U))
        (single-renNFSub ρ U)
        T
        (single-ren-right ρ U)))

renNFKind-as-renNfTy :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (U : NFKind Δ₁ K)
  → renNFKind ρ U ≡ renNfTy ρ U
renNFKind-as-renNfTy {K = KP} ρ U = refl
renNFKind-as-renNfTy {K = KV pk m} ρ U = refl

substNFTy-ren-expr :
  ∀ {Δ₁ Δ₂ K K′}
    (ρ : Δ₁ →ᵣ Δ₂)
    (T : NFTy (K ∷ Δ₁) K′)
    (U : NFKind Δ₁ K)
  → renNFTy ρ (substNFTy T U)
      ≡
    substNFTy
      (renNFTy (ρ ↑ᵣ K) T)
      (renNfTy ρ U)
substNFTy-ren-expr ρ T U =
  trans
    (substNFTy-ren ρ T U)
    (cong (substNFTy (renNFTy (ρ ↑ᵣ _) T))
      (renNFKind-as-renNfTy ρ U))

SubRenRel :
  ∀ {Δ₁ Δ₂ Δ₃}
  → (Δ₁ →ₛ Δ₂)
  → (Δ₂ →ᵣ Δ₃)
  → (Δ₁ →ₛ Δ₃)
  → Set
SubRenRel ϕ ρ ψ =
  ∀ K (x : K ∈ _) → (ϕ K x) ⋯ ρ ≡ ψ K x

lift-SubRenRel :
  ∀ {Δ₁ Δ₂ Δ₃ K}
    {ϕ : Δ₁ →ₛ Δ₂}
    {ρ : Δ₂ →ᵣ Δ₃}
    {ψ : Δ₁ →ₛ Δ₃}
  → SubRenRel ϕ ρ ψ
  → SubRenRel (ϕ ↑ₛ K) (ρ ↑ᵣ K) (ψ ↑ₛ K)
lift-SubRenRel rel K′ (hereₗ refl) = refl
lift-SubRenRel {K = K} {ϕ = ϕ} {ρ = ρ} rel K′ (thereₗ x) =
  trans
    (renTy-wk-comm ρ (ϕ K′ x))
    (cong (λ X → X ⋯ weakenᵣ K) (rel K′ x))

subst-renTy :
  ∀ {Δ₁ Δ₂ Δ₃ K}
    (T : Ty Δ₁ K)
    (ϕ : Δ₁ →ₛ Δ₂)
    (ρ : Δ₂ →ᵣ Δ₃)
    (ψ : Δ₁ →ₛ Δ₃)
  → SubRenRel ϕ ρ ψ
  → (T ⋯ ϕ) ⋯ ρ ≡ T ⋯ ψ
subst-renTy (Types.T-Var x) ϕ ρ ψ rel = rel _ x
subst-renTy Types.T-Base ϕ ρ ψ rel = refl
subst-renTy (Types.T-Arrow T U) ϕ ρ ψ rel =
  cong₂ Types.T-Arrow
    (subst-renTy T ϕ ρ ψ rel)
    (subst-renTy U ϕ ρ ψ rel)
subst-renTy (Types.T-Pair T U) ϕ ρ ψ rel =
  cong₂ Types.T-Pair
    (subst-renTy T ϕ ρ ψ rel)
    (subst-renTy U ϕ ρ ψ rel)
subst-renTy (Types.T-Poly K T) ϕ ρ ψ rel =
  cong (Types.T-Poly K)
    (subst-renTy T (ϕ ↑ₛ K) (ρ ↑ᵣ K) (ψ ↑ₛ K)
      (lift-SubRenRel {K = K} {ϕ = ϕ} {ρ = ρ} {ψ = ψ} rel))
subst-renTy (Types.T-Sub K≤K′ T) ϕ ρ ψ rel =
  cong (Types.T-Sub K≤K′) (subst-renTy T ϕ ρ ψ rel)
subst-renTy (Types.T-Dual d T) ϕ ρ ψ rel =
  cong (Types.T-Dual d) (subst-renTy T ϕ ρ ψ rel)
subst-renTy Types.T-End ϕ ρ ψ rel = refl
subst-renTy (Types.T-Msg p P S) ϕ ρ ψ rel =
  cong₂ (Types.T-Msg p)
    (subst-renTy P ϕ ρ ψ rel)
    (subst-renTy S ϕ ρ ψ rel)
subst-renTy (Types.T-Up T) ϕ ρ ψ rel =
  cong Types.T-Up (subst-renTy T ϕ ρ ψ rel)
subst-renTy (Types.T-Minus P) ϕ ρ ψ rel =
  cong Types.T-Minus (subst-renTy P ϕ ρ ψ rel)
subst-renTy (Types.T-ProtoD T) ϕ ρ ψ rel =
  cong Types.T-ProtoD (subst-renTy T ϕ ρ ψ rel)
subst-renTy (Types.T-ProtoP ss v P) ϕ ρ ψ rel =
  cong (Types.T-ProtoP ss v) (subst-renTy P ϕ ρ ψ rel)

instantiate-ren :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (p : Polarity)
    (T : Ty (KP ∷ []) K)
    (P : NFProto Δ₁)
  → instantiate ⦃ Kₛ ⦄ p T (nfProtoTy P) ⋯ ρ
      ≡
    instantiate ⦃ Kₛ ⦄ p T (nfProtoTy (renNFProto ρ P))
instantiate-ren ρ p T P =
  subst-renTy
    T
    (singletonSubst (nfProtoTy P))
    ρ
    (singletonSubst (nfProtoTy (renNFProto ρ P)))
    rel
  where
  rel :
    SubRenRel
      (singletonSubst (nfProtoTy P))
      ρ
      (singletonSubst (nfProtoTy (renNFProto ρ P)))
  rel KP (hereₗ refl) = sym (renNFProto-sound ρ P)
  rel K (thereₗ ())

ren-msgNF :
  ∀ {Δ₁ Δ₂}
    (ρ : Δ₁ →ᵣ Δ₂)
    (p : Polarity)
    (P : NFProto Δ₁)
    (S : NFTy Δ₁ SLin)
  → renNFTy ρ (msgNF p P S)
      ≡
    msgNF p (renNFProto ρ P) (renNFTy ρ S)
ren-msgNF ρ p (NT.N-Normal P) S = refl
ren-msgNF ρ p (NT.N-Minus P) S = refl

ren-materializeListNf :
  ∀ {Δ₁ Δ₂}
    (ρ : Δ₁ →ᵣ Δ₂)
    (Ts : List (Ty (KP ∷ []) KP))
    (p : Polarity)
    (P : NFProto Δ₁)
    (S : NFTy Δ₁ SLin)
  → renNFTy ρ (materializeListNf Ts p P S)
      ≡
    materializeListNf Ts p (renNFProto ρ P) (renNFTy ρ S)
ren-materializeListNf ρ [] p P S = refl
ren-materializeListNf ρ (T ∷ Ts) p P S =
  trans
    (ren-msgNF ρ p
      (normalizeTy (instantiate ⦃ Kₛ ⦄ p T (nfProtoTy P)))
      (materializeListNf Ts p P S))
    (cong₂ (msgNF p)
      (trans
        (ren-normalizeProto ρ
          (instantiate ⦃ Kₛ ⦄ p T (nfProtoTy P)))
        (cong normalizeTy (instantiate-ren ρ p T P)))
      (ren-materializeListNf ρ Ts p P S))

renNFTy-injective :
  ∀ {Δ₁ Δ₂ pk m}
    (ρ : Δ₁ →ᵣ Δ₂)
  → InjectiveRenaming ρ
  → {T U : NFTy Δ₁ (KV pk m)}
  → renNFTy ρ T ≡ renNFTy ρ U
  → T ≡ U
renNFTy-injective ρ inj {T} {U} eq =
  nfTyTy-injective
    (renaming-injective ρ inj
      (trans
        (sym (renNFTy-sound ρ T))
        (trans
          (cong nfTyTy eq)
          (renNFTy-sound ρ U))))

yes-output :
  ∀ {a} {A : Set a}
    {P : A → Set a}
    {x y : Σ A P}
  → yes x ≡ yes y
  → proj₁ x ≡ proj₁ y
yes-output refl = refl

just-output :
  ∀ {a b} {A : Set a}
    {P : A → Set b}
    {x y : Σ A P}
  → just x ≡ just y
  → proj₁ x ≡ proj₁ y
just-output refl = refl

nothing≢just :
  ∀ {a} {A : Set a} {x : A}
  → nothing ≡ just x
  → ⊥
nothing≢just ()

joinₜ-ren :
  ∀ {Δ₁ Δ₂ pk m}
    (ρ : Δ₁ →ᵣ Δ₂)
    (inj : InjectiveRenaming ρ)
    {T U V : NFTy Δ₁ (KV pk m)}
    {T<:V : T <:ₜ V}
    {U<:V : U <:ₜ V}
  → joinₜ T U ≡ yes (V , T<:V , U<:V)
  → Σ (renNFTy ρ T <:ₜ renNFTy ρ V) λ Tρ<:Vρ →
      Σ (renNFTy ρ U <:ₜ renNFTy ρ V) λ Uρ<:Vρ →
        joinₜ (renNFTy ρ T) (renNFTy ρ U)
          ≡ yes (renNFTy ρ V , Tρ<:Vρ , Uρ<:Vρ)
joinₜ-ren ρ inj {T} {U} {V} {T<:V} {U<:V} old
  with lub-joinₜ
         (renNFTy ρ T)
         (renNFTy ρ U)
         (renNFTy ρ V)
         (ren-preserves-<:ₜ ρ T<:V)
         (ren-preserves-<:ₜ ρ U<:V)
... | J , Tρ<:J , Uρ<:J , new , J<:Vρ
  with split-renTy-to-sub ρ Tρ<:J
... | J₀ , refl , T<:J₀
  with split-renTy-to-sub ρ Uρ<:J
... | J₁ , eqJ , U<:J₁
  with renNFTy-injective ρ inj eqJ
... | refl
  with lub-joinₜ T U J₀ T<:J₀ U<:J₁
... | W , T<:W , U<:W , old′ , W<:J₀
  with yes-output (trans (sym old) old′)
... | refl
  with renNFTy-injective ρ inj
         (<:ₜ-antisym J<:Vρ (ren-preserves-<:ₜ ρ W<:J₀))
... | refl =
  Tρ<:J , Uρ<:J , new

BranchJoin⁺-ren :
  ∀ {Δ₁ Δ₂ k pk m}
    (ρ : Δ₁ →ᵣ Δ₂)
    (inj : InjectiveRenaming ρ)
    {ss : Subset.Subset k}
    {V : (i : Fin k) → i Subset.∈ ss → NFTy Δ₁ (KV pk m)}
    {U : NFTy Δ₁ (KV pk m)}
    {sub : (i : Fin k) → (i∈ : i Subset.∈ ss) → V i i∈ <:ₜ U}
  → BranchJoin⁺ ss V ≡ just (U , sub)
  → Σ ((i : Fin k) → (i∈ : i Subset.∈ ss) →
          renNFTy ρ (V i i∈) <:ₜ renNFTy ρ U) λ subρ →
      BranchJoin⁺ ss (λ i i∈ → renNFTy ρ (V i i∈))
        ≡ just (renNFTy ρ U , subρ)
BranchJoin⁺-ren ρ inj {ss = []ᵥ} ()
BranchJoin⁺-ren ρ inj
    {ss = Subset.outside ∷ᵥ ss}
    {V = V}
    {U = U}
    old
  with BranchJoin⁺ ss (λ i i∈ → V (suc i) (there i∈)) in tail
... | nothing = ⊥-elim (nothing≢just old)
... | just (N , subN)
  with BranchJoin⁺-ren
         ρ inj
         {ss = ss}
         {V = λ i i∈ → V (suc i) (there i∈)}
         tail
... | subρ , tailρ
  with just-output old
... | refl
  rewrite tailρ =
  _ , refl
BranchJoin⁺-ren ρ inj
    {ss = Subset.inside ∷ᵥ ss}
    {V = V}
    {U = U}
    old
  with BranchJoin⁺ ss (λ i i∈ → V (suc i) (there i∈)) in tail
... | nothing = ⊥-elim (nothing≢just old)
... | just (N , subN)
  with joinₜ (V zero here) N in joined
... | no ¬join = ⊥-elim (nothing≢just old)
... | yes (W , V₀<:W , N<:W)
  with BranchJoin⁺-ren
         ρ inj
         {ss = ss}
         {V = λ i i∈ → V (suc i) (there i∈)}
         tail
... | subρ , tailρ
  with joinₜ-ren ρ inj joined
... | V₀ρ<:Wρ , Nρ<:Wρ , joinedρ
  with just-output old
... | refl
  rewrite tailρ | joinedρ =
  _ , refl

renBinding :
  ∀ {Δ₁ Δ₂}
  → (Δ₁ →ᵣ Δ₂)
  → Binding Δ₁
  → Binding Δ₂
renBinding ρ (B-Lin T) = B-Lin (renNFTy ρ T)
renBinding ρ (B-Un T) = B-Un (renNFTy ρ T)
renBinding ρ (B-Used T) = B-Used (renNFTy ρ T)

renCtx :
  ∀ {Δ₁ Δ₂ n}
  → (Δ₁ →ᵣ Δ₂)
  → Ctx Δ₁ n
  → Ctx Δ₂ n
renCtx ρ ∅ = ∅
renCtx ρ (b ▻ Γ) = renBinding ρ b ▻ renCtx ρ Γ

renBinding-wk :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (b : Binding Δ₁)
  → renBinding (ρ ↑ᵣ K) (wkBinding {K = K} b)
      ≡
    wkBinding {K = K} (renBinding ρ b)
renBinding-wk ρ (B-Lin T) =
  cong B-Lin (renNFTy-wk-comm ρ T)
renBinding-wk ρ (B-Un T) =
  cong B-Un (renNFTy-wk-comm ρ T)
renBinding-wk ρ (B-Used T) =
  cong B-Used (renNFTy-wk-comm ρ T)

renCtx-wk :
  ∀ {Δ₁ Δ₂ n K}
    (ρ : Δ₁ →ᵣ Δ₂)
    (Γ : Ctx Δ₁ n)
  → renCtx (ρ ↑ᵣ K) (wkCtx {K = K} Γ)
      ≡
    wkCtx {K = K} (renCtx ρ Γ)
renCtx-wk ρ ∅ = refl
renCtx-wk ρ (b ▻ Γ) =
  cong₂ _▻_
    (renBinding-wk ρ b)
    (renCtx-wk ρ Γ)

ren-preserves-∋ᵘ :
  ∀ {Δ₁ Δ₂ n pk}
    (ρ : Δ₁ →ᵣ Δ₂)
    {Γ : Ctx Δ₁ n}
    {x : Fin n}
    {T : NfTy Δ₁ (KV pk Un)}
  → Γ ∋ᵘ x ∶ T
  → renCtx ρ Γ ∋ᵘ x ∶ renNFTy ρ T
ren-preserves-∋ᵘ ρ hereᵘ = hereᵘ
ren-preserves-∋ᵘ ρ (thereᵘˡ x∈) =
  thereᵘˡ (ren-preserves-∋ᵘ ρ x∈)
ren-preserves-∋ᵘ ρ (thereᵘᵘ x∈) =
  thereᵘᵘ (ren-preserves-∋ᵘ ρ x∈)
ren-preserves-∋ᵘ ρ (thereᵘ✖ x∈) =
  thereᵘ✖ (ren-preserves-∋ᵘ ρ x∈)

ren-preserves-take :
  ∀ {Δ₁ Δ₂ n pk}
    (ρ : Δ₁ →ᵣ Δ₂)
    {Γ₁ Γ₂ : Ctx Δ₁ n}
    {x : Fin n}
    {T : NfTy Δ₁ (KV pk Lin)}
  → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂
  → renCtx ρ Γ₁ ⊢ˡ x ∶ renNFTy ρ T ⊣ renCtx ρ Γ₂
ren-preserves-take ρ take-here = take-here
ren-preserves-take ρ (take-thereˡ take) =
  take-thereˡ (ren-preserves-take ρ take)
ren-preserves-take ρ (take-thereᵘ take) =
  take-thereᵘ (ren-preserves-take ρ take)
ren-preserves-take ρ (take-there✖ take) =
  take-there✖ (ren-preserves-take ρ take)

ren-selectNf :
  ∀ {Δ₁ Δ₂ k}
    (ρ : Δ₁ →ᵣ Δ₂)
    (v : Variance)
    (i : Fin k)
    (P : NFProto Δ₁)
    (S : NFTy Δ₁ SLin)
  → renNFTy ρ (selectNf v i P S)
      ≡
    selectNf v i (renNFProto ρ P) (renNFTy ρ S)
ren-selectNf ρ v i P S =
  cong₂ NT.N-Arrow
    refl
    (ren-materializeListNf
      ρ
      (proj₁ (ProtocolConstructors _ v i))
      Polarity.⊕
      P
      S)

ren-select1Nf :
  ∀ {Δ₁ Δ₂ k}
    (ρ : Δ₁ →ᵣ Δ₂)
    (v : Variance)
    (i : Fin k)
    (P : NFProto Δ₁)
  → renNFTy ρ (select1Nf v i P)
      ≡
    select1Nf v i (renNFProto ρ P)
ren-select1Nf ρ v i P =
  cong (NT.N-Poly SLin)
    (trans
      (ren-selectNf
        (ρ ↑ᵣ SLin)
        v
        i
        (renNFProto (weakenᵣ SLin) P)
        (NT.N-Var (NT.NV-Var (hereₗ refl))))
      (cong₂ (selectNf v i)
        (renNFProto-wk-comm ρ P)
        refl))

ren-selectConstNf :
  ∀ {Δ₁ Δ₂ k}
    (ρ : Δ₁ →ᵣ Δ₂)
    (v : Variance)
    (i : Fin k)
  → renNFTy ρ (selectConstNf v i)
      ≡
    selectConstNf v i
ren-selectConstNf ρ v i =
  cong (NT.N-Poly KP)
    (ren-select1Nf
      (ρ ↑ᵣ KP)
      v
      i
      (NT.N-Normal (NT.N-Var (hereₗ refl))))

ren-receiveNf :
  ∀ {Δ₁ Δ₂ pk}
    (ρ : Δ₁ →ᵣ Δ₂)
    (T : NFTy Δ₁ (KV pk Lin))
    (S : NFTy Δ₁ SLin)
  → renNFTy ρ (receiveNf T S)
      ≡
    receiveNf (renNFTy ρ T) (renNFTy ρ S)
ren-receiveNf ρ T S = refl

ren-receive1Nf :
  ∀ {Δ₁ Δ₂ pk}
    (ρ : Δ₁ →ᵣ Δ₂)
    (T : NFTy Δ₁ (KV pk Lin))
  → renNFTy ρ (receive1Nf T)
      ≡
    receive1Nf (renNFTy ρ T)
ren-receive1Nf ρ T =
  cong (NT.N-Poly SLin)
    (trans
      (ren-receiveNf
        (ρ ↑ᵣ SLin)
        (renNFTy (weakenᵣ SLin) T)
        (NT.N-Var (NT.NV-Var (hereₗ refl))))
      (cong₂ receiveNf
        (renNFTy-wk-comm ρ T)
        refl))

ren-sendNf :
  ∀ {Δ₁ Δ₂ pk}
    (ρ : Δ₁ →ᵣ Δ₂)
    (T : NFTy Δ₁ (KV pk Lin))
    (S : NFTy Δ₁ SLin)
  → renNFTy ρ (sendNf T S)
      ≡
    sendNf (renNFTy ρ T) (renNFTy ρ S)
ren-sendNf ρ T S = refl

ren-send1Nf :
  ∀ {Δ₁ Δ₂ pk}
    (ρ : Δ₁ →ᵣ Δ₂)
    (T : NFTy Δ₁ (KV pk Lin))
  → renNFTy ρ (send1Nf T)
      ≡
    send1Nf (renNFTy ρ T)
ren-send1Nf ρ T =
  cong (NT.N-Poly SLin)
    (trans
      (ren-sendNf
        (ρ ↑ᵣ SLin)
        (renNFTy (weakenᵣ SLin) T)
        (NT.N-Var (NT.NV-Var (hereₗ refl))))
      (cong₂ sendNf
        (renNFTy-wk-comm ρ T)
        refl))

ren-MatchBranchOutput :
  ∀ {Δ₁ Δ₂ k}
    (ρ : Δ₁ →ᵣ Δ₂)
    (ss : Subset.Subset (sucℕ k))
    (v : Variance)
    (P : NFProto Δ₁)
    (S : NFTy Δ₁ SLin)
    (i : Fin (sucℕ k))
    (i∈ : i Subset.∈ ss)
  → renNFTy ρ (MatchBranchOutput ss v P S i i∈)
      ≡
    MatchBranchOutput ss v (renNFProto ρ P) (renNFTy ρ S) i i∈
ren-MatchBranchOutput ρ ss v P S i i∈ =
  ren-materializeListNf
    ρ
    (proj₁ (ProtocolConstructors _ v i))
    Polarity.⊝
    P
    S

ren-preserves-ConstTy :
  ∀ {Δ₁ Δ₂ K}
    (ρ : Δ₁ →ᵣ Δ₂)
    {c : ExprSyntax.Const}
    {T : NfTy Δ₁ K}
  → ConstTy c T
  → ConstTy c (renNFKind ρ T)
ren-preserves-ConstTy ρ CT-Unit = CT-Unit
ren-preserves-ConstTy ρ CT-Fork = CT-Fork
ren-preserves-ConstTy ρ CT-New = CT-New
ren-preserves-ConstTy ρ CT-Receive = CT-Receive
ren-preserves-ConstTy ρ CT-Send = CT-Send
ren-preserves-ConstTy ρ CT-Close = CT-Close
ren-preserves-ConstTy ρ (CT-Select {v = v} {i = i})
  rewrite ren-selectConstNf ρ v i =
  CT-Select

mutual

  ren-preserves-value :
    ∀ {Δ₁ Δ₂ n pk m}
      (ρ : Δ₁ →ᵣ Δ₂)
      (inj : InjectiveRenaming ρ)
      {Γ₁ Γ₂ : Ctx Δ₁ n}
      {v : Value Δ₁ n}
      {T : NfTy Δ₁ (KV pk m)}
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
    → renCtx ρ Γ₁ ⊢ᵥ renTyValue ρ v
        ⇒ renNFTy ρ T
        ⊣ renCtx ρ Γ₂
  ren-preserves-value ρ inj (TV-Const cT) =
    TV-Const (ren-preserves-ConstTy ρ cT)
  ren-preserves-value ρ inj (TV-Var-Lin take) =
    TV-Var-Lin (ren-preserves-take ρ take)
  ren-preserves-value ρ inj (TV-Var-Un x∈) =
    TV-Var-Un (ren-preserves-∋ᵘ ρ x∈)
  ren-preserves-value ρ inj (TV-Abs d) =
    TV-Abs (ren-preserves-synth ρ inj d)
  ren-preserves-value ρ inj (TV-Rec d) =
    TV-Rec (ren-preserves-check ρ inj d)
  ren-preserves-value
      ρ inj
      {Γ₁ = Γ₁}
      {Γ₂ = Γ₂}
      (TV-TAbs {K = K} d)
    =
    TV-TAbs
      (subst
        (λ X →
          wkCtx {K = K} (renCtx ρ Γ₁)
            ⊢ᵥ renTyValue (ρ ↑ᵣ K) _
              ⇒ renNFTy (ρ ↑ᵣ K) _
              ⊣ X)
        (renCtx-wk ρ Γ₂)
        (subst
          (λ X →
            X
              ⊢ᵥ renTyValue (ρ ↑ᵣ K) _
                ⇒ renNFTy (ρ ↑ᵣ K) _
                ⊣ renCtx (ρ ↑ᵣ K) (wkCtx {K = K} Γ₂))
          (renCtx-wk ρ Γ₁)
          (ren-preserves-value
            (ρ ↑ᵣ K)
            (injective-↑ᵣ inj)
            {Γ₁ = wkCtx {K = K} Γ₁}
            {Γ₂ = wkCtx {K = K} Γ₂}
            d)))
  ren-preserves-value ρ inj (TV-Pair d₁ d₂) =
    TV-Pair
      (ren-preserves-value ρ inj d₁)
      (ren-preserves-value ρ inj d₂)
  ren-preserves-value ρ inj (TV-Receive₁ {T = T})
    rewrite ren-receive1Nf ρ T =
    TV-Receive₁
  ren-preserves-value ρ inj (TV-Receive₂ {T = T} {S = S})
    rewrite ren-receiveNf ρ T S =
    TV-Receive₂
  ren-preserves-value ρ inj (TV-Send₁ {T = T})
    rewrite ren-send1Nf ρ T =
    TV-Send₁
  ren-preserves-value ρ inj (TV-Send₂ {T = T} {S = S})
    rewrite ren-sendNf ρ T S =
    TV-Send₂
  ren-preserves-value ρ inj (TV-Select₁ {v = v} {i = i} {P = P})
    rewrite ren-select1Nf ρ v i P =
    TV-Select₁
  ren-preserves-value ρ inj
      (TV-Select₂ {v = v} {i = i} {P = P} {S = S})
    rewrite ren-selectNf ρ v i P S =
    TV-Select₂

  ren-preserves-synth :
    ∀ {Δ₁ Δ₂ n pk m}
      (ρ : Δ₁ →ᵣ Δ₂)
      (inj : InjectiveRenaming ρ)
      {Γ₁ Γ₂ : Ctx Δ₁ n}
      {e : Expr Δ₁ n}
      {T : NfTy Δ₁ (KV pk m)}
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
    → renCtx ρ Γ₁ ⊢ renTyExpr ρ e
        ⇒ renNFTy ρ T
        ⊣ renCtx ρ Γ₂
  ren-preserves-synth ρ inj (T-Val d) =
    T-Val (ren-preserves-value ρ inj d)
  ren-preserves-synth ρ inj (T-Pair d₁ d₂) =
    T-Pair
      (ren-preserves-synth ρ inj d₁)
      (ren-preserves-synth ρ inj d₂)
  ren-preserves-synth ρ inj (T-App d₁ d₂) =
    T-App
      (ren-preserves-synth ρ inj d₁)
      (ren-preserves-check ρ inj d₂)
  ren-preserves-synth ρ inj (T-LetUnit d₁ d₂) =
    T-LetUnit
      (ren-preserves-check ρ inj d₁)
      (ren-preserves-synth ρ inj d₂)
  ren-preserves-synth ρ inj (T-LetPair d₁ d₂) =
    T-LetPair
      (ren-preserves-synth ρ inj d₁)
      (ren-preserves-synth ρ inj d₂)
  ren-preserves-synth
      ρ inj
      (T-Match
        {ss = ss}
        {v = variance}
        {ssbranches = ssbranches}
        {incl = incl}
        {ne = ne}
        {P = P}
        {S = S}
        {V = V}
        d bs j)
    with BranchJoin⁺-ren ρ inj j
  ... | subρ , jρ =
    T-Match
      {ss = ss}
      {v = variance}
      {ssbranches = ssbranches}
      {incl = incl}
      {ne = ne}
      scrutinee
      branches
      jρ
    where
    scrutinee :
      renCtx ρ _
        ⊢ renTyExpr ρ _
          ⇒ MatchBranchInput
              ss
              variance
              (renNFProto ρ P)
              (renNFTy ρ S)
          ⊣ renCtx ρ _
    scrutinee = ren-preserves-synth ρ inj d

    branches :
      (i : Fin _)
      → (i∈ : i Subset.∈ ssbranches)
      → (MatchBranchOutput
            ssbranches
            variance
            (renNFProto ρ P)
            (renNFTy ρ S)
            i
            i∈
          ExprNormalTyping.∷ˡ
          renCtx ρ _)
          ⊢ renTyExpr ρ _
            ⇒ renNFTy ρ (V i i∈)
            ⊣ (B-Used
                (MatchBranchOutput
                  ssbranches
                  variance
                  (renNFProto ρ P)
                  (renNFTy ρ S)
                  i
                  i∈)
                ▻ renCtx ρ _)
    branches i i∈ =
      subst
        (λ X →
          (X ExprNormalTyping.∷ˡ renCtx ρ _)
            ⊢ renTyExpr ρ _
              ⇒ renNFTy ρ (V i i∈)
              ⊣ (B-Used X ▻ renCtx ρ _))
        (ren-MatchBranchOutput
          ρ ssbranches variance P S i i∈)
        (ren-preserves-synth ρ inj (bs i i∈))
  ren-preserves-synth
      ρ inj
      {Γ₁ = Γ₁}
      {Γ₂ = Γ₂}
      (T-TApp {e = e} {T = T} {U = U} d)
    =
    subst
      (λ X →
        renCtx ρ Γ₁
          ⊢ E-TApp (renTyExpr ρ e) (renNfTy ρ U)
            ⇒ X
            ⊣ renCtx ρ Γ₂)
      (sym (substNFTy-ren-expr ρ T U))
      (T-TApp (ren-preserves-synth ρ inj d))

  ren-preserves-check :
    ∀ {Δ₁ Δ₂ n pk m}
      (ρ : Δ₁ →ᵣ Δ₂)
      (inj : InjectiveRenaming ρ)
      {Γ₁ Γ₂ : Ctx Δ₁ n}
      {e : Expr Δ₁ n}
      {T : NfTy Δ₁ (KV pk m)}
    → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
    → renCtx ρ Γ₁ ⊢ renTyExpr ρ e
        ⇐ renNFTy ρ T
        ⊣ renCtx ρ Γ₂
  ren-preserves-check ρ inj (T-Check d sub) =
    T-Check
      (ren-preserves-synth ρ inj d)
      (ren-preserves-<:ₜ ρ sub)

renCtx-weaken :
  ∀ {Δ n K}
    (Γ : Ctx Δ n)
  → renCtx (weakenᵣ K) Γ ≡ wkCtx {K = K} Γ
renCtx-weaken ∅ = refl
renCtx-weaken (B-Lin T ▻ Γ) =
  cong (B-Lin (wkNfTy T) ▻_) (renCtx-weaken Γ)
renCtx-weaken (B-Un T ▻ Γ) =
  cong (B-Un (wkNfTy T) ▻_) (renCtx-weaken Γ)
renCtx-weaken (B-Used T ▻ Γ) =
  cong (B-Used (wkNfTy T) ▻_) (renCtx-weaken Γ)

wkTy-preserves-value :
  ∀ {Δ n pk m K}
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  → wkCtx {K = K} Γ₁ ⊢ᵥ wkTyValue {K = K} v
      ⇒ wkNfTy {K′ = K} T
      ⊣ wkCtx {K = K} Γ₂
wkTy-preserves-value
    {K = K}
    {Γ₁ = Γ₁}
    {Γ₂ = Γ₂}
    d =
  subst
    (λ X →
      wkCtx {K = K} Γ₁
        ⊢ᵥ wkTyValue {K = K} _
          ⇒ wkNfTy {K′ = K} _
          ⊣ X)
    (renCtx-weaken Γ₂)
    (subst
      (λ X →
        X
          ⊢ᵥ wkTyValue {K = K} _
            ⇒ wkNfTy {K′ = K} _
            ⊣ renCtx (weakenᵣ K) Γ₂)
      (renCtx-weaken Γ₁)
      (ren-preserves-value (weakenᵣ K) weakenᵣ-injective d))

wkTy-preserves-synth :
  ∀ {Δ n pk m K}
    {Γ₁ Γ₂ : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk m)}
  → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
  → wkCtx {K = K} Γ₁ ⊢ wkTyExpr {K = K} e
      ⇒ wkNfTy {K′ = K} T
      ⊣ wkCtx {K = K} Γ₂
wkTy-preserves-synth
    {K = K}
    {Γ₁ = Γ₁}
    {Γ₂ = Γ₂}
    d =
  subst
    (λ X →
      wkCtx {K = K} Γ₁
        ⊢ wkTyExpr {K = K} _
          ⇒ wkNfTy {K′ = K} _
          ⊣ X)
    (renCtx-weaken Γ₂)
    (subst
      (λ X →
        X
          ⊢ wkTyExpr {K = K} _
            ⇒ wkNfTy {K′ = K} _
            ⊣ renCtx (weakenᵣ K) Γ₂)
      (renCtx-weaken Γ₁)
      (ren-preserves-synth (weakenᵣ K) weakenᵣ-injective d))

wkTy-preserves-check :
  ∀ {Δ n pk m K}
    {Γ₁ Γ₂ : Ctx Δ n}
    {e : Expr Δ n}
    {T : NfTy Δ (KV pk m)}
  → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
  → wkCtx {K = K} Γ₁ ⊢ wkTyExpr {K = K} e
      ⇐ wkNfTy {K′ = K} T
      ⊣ wkCtx {K = K} Γ₂
wkTy-preserves-check
    {K = K}
    {Γ₁ = Γ₁}
    {Γ₂ = Γ₂}
    d =
  subst
    (λ X →
      wkCtx {K = K} Γ₁
        ⊢ wkTyExpr {K = K} _
          ⇐ wkNfTy {K′ = K} _
          ⊣ X)
    (renCtx-weaken Γ₂)
    (subst
      (λ X →
        X
          ⊢ wkTyExpr {K = K} _
            ⇐ wkNfTy {K′ = K} _
            ⊣ renCtx (weakenᵣ K) Γ₂)
      (renCtx-weaken Γ₁)
      (ren-preserves-check (weakenᵣ K) weakenᵣ-injective d))
