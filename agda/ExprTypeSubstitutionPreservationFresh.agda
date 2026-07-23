module ExprTypeSubstitutionPreservationFresh where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using () renaming (suc to sucℕ)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using ()
  renaming (here to hereₗ; there to thereₗ)
open import Data.Vec using (here; there)
  renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁)
open import Variance using (Variance)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
import Relation.Nullary
open import Util using (dependent-ext₂)

open import Kinds
open import Kits
open import Types using (Ty; Ty-Syntax; Ty-Traversal)
import Types
import NormalTypes as NT
open import NormalTypes using
  ( NFTy
  ; NFProto
  ; NFProto′
  ; NFVar
  ; nfTyTy
  ; nfTyTy-injective
  ; nfProtoTy
  ; nfProtoTy-injective
  ; nfProtoTy-fromNormalProto
  )
open import NormalTypesRenamings using (renNFTy; renNFProto)
open import NormalTypesSubstitution using
  ( NFKind
  ; NFSub
  ; dualNFKind
  ; dualNFKind-sound
  ; nfSubTy
  ; nfVarKind
  ; wkNFKind
  ; wkNFSub
  ; singleNFSub
  ; minusNF
  ; msgNF
  ; substNFProto′With
  ; substNFProtoWith
  ; substNFProto
  ; substNFProto-sound
  ; substNFProto-single-sound
  ; substNFVarWith
  ; substNFTyWith
  ; substNFTy
  ; substNFTy-sound
  )
import Duality as D
open import Duality using (Dualizable; D-S; ⊕; d?⊥)
open import SubstitutionSubtyping using
  ( subst-preserves-≡c
  ; t-dual-preserves-≡c
  )
open import AlgorithmicNFSubtyping using (_<:ₜ_)
import AlgorithmicNFMerge
open import AlgorithmicNFSubstitution using (subst-preserves-<:ₜWith)
open import AlgorithmicNFMergeSubstitution using (joinₜ-subst)
open import ExprTypeRenamingPreservationFresh using
  ( ren-normalizeTy
  ; ren-normalizeProto
  ; NFSubRenRel
  ; RenNFSubRel
  ; renNFKind
  ; ren-substNFProto
  ; ren-substNFTy
  ; subst-renNFProto
  ; subst-renNFTy
  ; just-output
  ; nothing≢just
  )
open import ExprSyntax using
  ( NfTy
  ; Expr
  ; Value
  ; E-Val
  ; E-App
  ; E-TApp
  ; E-LetUnit
  ; E-Pair
  ; E-LetPair
  ; E-Match
  ; V-Const
  ; V-Var
  ; V-Abs
  ; V-Rec
  ; V-TAbs
  ; V-Pair
  ; V-Receive₁
  ; V-Receive₂
  ; V-Send₁
  ; V-Send₂
  ; V-Select₁
  ; V-Select₂
  )
open import ExprSubstitution using
  ( toNFSub
  ; substTyValueWith
  ; substTyExprWith
  ; substTyValue
  ; substTyExpr
  ; substNFValueWith
  ; substNFExprWith
  ) renaming (substNFNfTyWith to substNFKindWith)
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
  ; wkNfTy
  ; polyNf
  ; receive1Nf
  ; receiveNf
  ; send1Nf
  ; sendNf
  ; select1Nf
  ; selectNf
  ; MatchBranchInput
  ; MatchBranchOutput
  ; BranchJoin⁺
  ; normalizeTy
  ; normalizeTy-id
  ; materializeListNf
  ; unitConstNf
  ; forkConstNf
  ; newConstNf
  ; receiveConstNf
  ; sendConstNf
  ; closeConstNf
  ; selectConstNf
  ; CT-Unit
  ; CT-Fork
  ; CT-New
  ; CT-Receive
  ; CT-Send
  ; CT-Close
  ; CT-Select
  )
open import TypesProtocolConstructors using
  (ProtocolConstructors; singletonSubst; instantiate)

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (⋯-id)

substBindingWith :
  ∀ {Δ₁ Δ₂}
  → NFSub Δ₁ Δ₂
  → Binding Δ₁
  → Binding Δ₂
substBindingWith σ (B-Lin T) = B-Lin (substNFTyWith σ T)
substBindingWith σ (B-Un T) = B-Un (substNFTyWith σ T)
substBindingWith σ (B-Used T) = B-Used (substNFTyWith σ T)

substCtxWith :
  ∀ {Δ₁ Δ₂ n}
  → NFSub Δ₁ Δ₂
  → Ctx Δ₁ n
  → Ctx Δ₂ n
substCtxWith σ ∅ = ∅
substCtxWith σ (b ▻ Γ) = substBindingWith σ b ▻ substCtxWith σ Γ

weakenNFSub :
  ∀ {Δ₁ Δ₂ K}
  → NFSub Δ₁ Δ₂
  → NFSub Δ₁ (K ∷ Δ₂)
weakenNFSub {K = K} σ K′ x = wkNFKind {K′ = K} (σ K′ x)

weaken-left :
  ∀ {Δ₁ Δ₂ K}
    (σ : NFSub Δ₁ Δ₂)
  → RenNFSubRel
      (weakenᵣ K)
      (wkNFSub {K = K} σ)
      (weakenNFSub {K = K} σ)
weaken-left σ K′ x = refl

weaken-right :
  ∀ {Δ₁ Δ₂ K}
    (σ : NFSub Δ₁ Δ₂)
  → NFSubRenRel
      σ
      (weakenᵣ K)
      (weakenNFSub {K = K} σ)
weaken-right σ KP x = refl
weaken-right σ (KV pk m) x = refl

substNFProto-wk :
  ∀ {Δ₁ Δ₂ K}
    (σ : NFSub Δ₁ Δ₂)
    (T : NFProto Δ₁)
  → substNFProtoWith (wkNFSub {K = K} σ) (renNFProto (weakenᵣ K) T)
      ≡
    renNFProto (weakenᵣ K) (substNFProtoWith σ T)
substNFProto-wk {K = K} σ T =
  trans
    (subst-renNFProto
      (weakenᵣ K)
      (wkNFSub σ)
      (weakenNFSub σ)
      T
      (weaken-left σ))
    (sym
      (ren-substNFProto
        (weakenᵣ K)
        σ
        (weakenNFSub σ)
        T
        (weaken-right σ)))

substNFTy-wk :
  ∀ {Δ₁ Δ₂ K pk m}
    (σ : NFSub Δ₁ Δ₂)
    (T : NFTy Δ₁ (KV pk m))
  → substNFTyWith (wkNFSub {K = K} σ) (renNFTy (weakenᵣ K) T)
      ≡
    renNFTy (weakenᵣ K) (substNFTyWith σ T)
substNFTy-wk {K = K} σ T =
  trans
    (subst-renNFTy
      (weakenᵣ K)
      (wkNFSub σ)
      (weakenNFSub σ)
      T
      (weaken-left σ))
    (sym
      (ren-substNFTy
        (weakenᵣ K)
        σ
        (weakenNFSub σ)
        T
        (weaken-right σ)))

substBinding-wk :
  ∀ {Δ₁ Δ₂ K}
    (σ : NFSub Δ₁ Δ₂)
    (b : Binding Δ₁)
  → substBindingWith (wkNFSub {K = K} σ) (wkBinding {K = K} b)
      ≡
    wkBinding {K = K} (substBindingWith σ b)
substBinding-wk σ (B-Lin T) = cong B-Lin (substNFTy-wk σ T)
substBinding-wk σ (B-Un T) = cong B-Un (substNFTy-wk σ T)
substBinding-wk σ (B-Used T) = cong B-Used (substNFTy-wk σ T)

substCtx-wk :
  ∀ {Δ₁ Δ₂ n K}
    (σ : NFSub Δ₁ Δ₂)
    (Γ : Ctx Δ₁ n)
  → substCtxWith (wkNFSub {K = K} σ) (wkCtx {K = K} Γ)
      ≡
    wkCtx {K = K} (substCtxWith σ Γ)
substCtx-wk σ ∅ = refl
substCtx-wk σ (b ▻ Γ) =
  cong₂ _▻_ (substBinding-wk σ b) (substCtx-wk σ Γ)

subst-preserves-∋ᵘ :
  ∀ {Δ₁ Δ₂ n pk}
    (σ : NFSub Δ₁ Δ₂)
    {Γ : Ctx Δ₁ n}
    {x : Fin n}
    {T : NFTy Δ₁ (KV pk Un)}
  → Γ ∋ᵘ x ∶ T
  → substCtxWith σ Γ ∋ᵘ x ∶ substNFTyWith σ T
subst-preserves-∋ᵘ σ hereᵘ = hereᵘ
subst-preserves-∋ᵘ σ (thereᵘˡ x∈) =
  thereᵘˡ (subst-preserves-∋ᵘ σ x∈)
subst-preserves-∋ᵘ σ (thereᵘᵘ x∈) =
  thereᵘᵘ (subst-preserves-∋ᵘ σ x∈)
subst-preserves-∋ᵘ σ (thereᵘ✖ x∈) =
  thereᵘ✖ (subst-preserves-∋ᵘ σ x∈)

subst-preserves-take :
  ∀ {Δ₁ Δ₂ n pk}
    (σ : NFSub Δ₁ Δ₂)
    {Γ₁ Γ₂ : Ctx Δ₁ n}
    {x : Fin n}
    {T : NFTy Δ₁ (KV pk Lin)}
  → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂
  → substCtxWith σ Γ₁
      ⊢ˡ x ∶ substNFTyWith σ T
      ⊣ substCtxWith σ Γ₂
subst-preserves-take σ take-here = take-here
subst-preserves-take σ (take-thereˡ take) =
  take-thereˡ (subst-preserves-take σ take)
subst-preserves-take σ (take-thereᵘ take) =
  take-thereᵘ (subst-preserves-take σ take)
subst-preserves-take σ (take-there✖ take) =
  take-there✖ (subst-preserves-take σ take)

subst-preserves-<:ₜ :
  ∀ {Δ₁ Δ₂ pk m}
    (σ : NFSub Δ₁ Δ₂)
    {T U : NFTy Δ₁ (KV pk m)}
  → T <:ₜ U
  → substNFTyWith σ T <:ₜ substNFTyWith σ U
subst-preserves-<:ₜ = subst-preserves-<:ₜWith

record SubstitutionAlgebra : Set₁ where
  field
    const :
      ∀ {Δ₁ Δ₂ K c}
        (σ : NFSub Δ₁ Δ₂)
        {T : NFKind Δ₁ K}
      → ConstTy c T
      → ConstTy c (substNFKindWith σ T)

    receive1 :
      ∀ {Δ₁ Δ₂ pk}
        (σ : NFSub Δ₁ Δ₂)
        (T : NFTy Δ₁ (KV pk Lin))
      → substNFTyWith σ (receive1Nf T)
          ≡ receive1Nf (substNFTyWith σ T)

    receive2 :
      ∀ {Δ₁ Δ₂ pk}
        (σ : NFSub Δ₁ Δ₂)
        (T : NFTy Δ₁ (KV pk Lin))
        (S : NFTy Δ₁ SLin)
      → substNFTyWith σ (receiveNf T S)
          ≡ receiveNf (substNFTyWith σ T) (substNFTyWith σ S)

    send1 :
      ∀ {Δ₁ Δ₂ pk}
        (σ : NFSub Δ₁ Δ₂)
        (T : NFTy Δ₁ (KV pk Lin))
      → substNFTyWith σ (send1Nf T)
          ≡ send1Nf (substNFTyWith σ T)

    send2 :
      ∀ {Δ₁ Δ₂ pk}
        (σ : NFSub Δ₁ Δ₂)
        (T : NFTy Δ₁ (KV pk Lin))
        (S : NFTy Δ₁ SLin)
      → substNFTyWith σ (sendNf T S)
          ≡ sendNf (substNFTyWith σ T) (substNFTyWith σ S)

    select1 :
      ∀ {Δ₁ Δ₂ k}
        (σ : NFSub Δ₁ Δ₂)
        (v : Variance)
        (i : Fin k)
        (P : NFProto Δ₁)
      → substNFTyWith σ (select1Nf v i P)
          ≡ select1Nf v i (substNFProtoWith σ P)

    select2 :
      ∀ {Δ₁ Δ₂ k}
        (σ : NFSub Δ₁ Δ₂)
        (v : Variance)
        (i : Fin k)
        (P : NFProto Δ₁)
        (S : NFTy Δ₁ SLin)
      → substNFTyWith σ (selectNf v i P S)
          ≡ selectNf v i
              (substNFProtoWith σ P)
              (substNFTyWith σ S)

    matchInput :
      ∀ {Δ₁ Δ₂ k}
        (σ : NFSub Δ₁ Δ₂)
        (ss : Subset.Subset k)
        (v : Variance)
        (P : NFProto Δ₁)
        (S : NFTy Δ₁ SLin)
      → substNFTyWith σ (MatchBranchInput ss v P S)
          ≡ MatchBranchInput ss v
              (substNFProtoWith σ P)
              (substNFTyWith σ S)

    matchOutput :
      ∀ {Δ₁ Δ₂ k}
        (σ : NFSub Δ₁ Δ₂)
        (ss : Subset.Subset (sucℕ k))
        (v : Variance)
        (P : NFProto Δ₁)
        (S : NFTy Δ₁ SLin)
        (i : Fin (sucℕ k))
        (i∈ : i Subset.∈ ss)
      → substNFTyWith σ (MatchBranchOutput ss v P S i i∈)
          ≡ MatchBranchOutput ss v
              (substNFProtoWith σ P)
              (substNFTyWith σ S)
              i i∈

    branchJoin :
      ∀ {Δ₁ Δ₂ k pk m}
        (σ : NFSub Δ₁ Δ₂)
        {ss : Subset.Subset k}
        {V : (i : Fin k) → i Subset.∈ ss → NFTy Δ₁ (KV pk m)}
        {U : NFTy Δ₁ (KV pk m)}
        {sub : (i : Fin k) → (i∈ : i Subset.∈ ss) → V i i∈ <:ₜ U}
      → BranchJoin⁺ ss V ≡ just (U , sub)
      → Σ ((i : Fin k) → (i∈ : i Subset.∈ ss) →
              substNFTyWith σ (V i i∈) <:ₜ substNFTyWith σ U)
          λ subσ →
            BranchJoin⁺ ss (λ i i∈ → substNFTyWith σ (V i i∈))
              ≡ just (substNFTyWith σ U , subσ)

    typeApplication :
      ∀ {Δ₁ Δ₂ K pk m}
        (σ : NFSub Δ₁ Δ₂)
        (T : NFTy (K ∷ Δ₁) (KV pk m))
        (U : NFKind Δ₁ K)
      → substNFTyWith σ
          (NormalTypesSubstitution.substNFTy T U)
          ≡
        NormalTypesSubstitution.substNFTy
          (substNFTyWith (wkNFSub σ) T)
          (substNFKindWith σ U)

subst-receive2 :
  ∀ {Δ₁ Δ₂ pk}
    (σ : NFSub Δ₁ Δ₂)
    (T : NFTy Δ₁ (KV pk Lin))
    (S : NFTy Δ₁ SLin)
  → substNFTyWith σ (receiveNf T S)
      ≡ receiveNf (substNFTyWith σ T) (substNFTyWith σ S)
subst-receive2 σ T S = refl

subst-receive1 :
  ∀ {Δ₁ Δ₂ pk}
    (σ : NFSub Δ₁ Δ₂)
    (T : NFTy Δ₁ (KV pk Lin))
  → substNFTyWith σ (receive1Nf T)
      ≡ receive1Nf (substNFTyWith σ T)
subst-receive1 σ T
  rewrite substNFTy-wk {K = SLin} σ T =
  refl

subst-send2 :
  ∀ {Δ₁ Δ₂ pk}
    (σ : NFSub Δ₁ Δ₂)
    (T : NFTy Δ₁ (KV pk Lin))
    (S : NFTy Δ₁ SLin)
  → substNFTyWith σ (sendNf T S)
      ≡ sendNf (substNFTyWith σ T) (substNFTyWith σ S)
subst-send2 σ T S = refl

subst-send1 :
  ∀ {Δ₁ Δ₂ pk}
    (σ : NFSub Δ₁ Δ₂)
    (T : NFTy Δ₁ (KV pk Lin))
  → substNFTyWith σ (send1Nf T)
      ≡ send1Nf (substNFTyWith σ T)
subst-send1 σ T
  rewrite substNFTy-wk {K = SLin} σ T =
  refl

subst-matchInput :
  ∀ {Δ₁ Δ₂ k}
    (σ : NFSub Δ₁ Δ₂)
    (ss : Subset.Subset k)
    (v : Variance)
    (P : NFProto Δ₁)
    (S : NFTy Δ₁ SLin)
  → substNFTyWith σ (MatchBranchInput ss v P S)
      ≡ MatchBranchInput ss v
          (substNFProtoWith σ P)
          (substNFTyWith σ S)
subst-matchInput σ ss v P S = refl

dual-preserves-≡c :
  ∀ {Δ m} {T U : Types.Ty Δ (KV KS m)}
  → T Types.≡c U
  → Types.T-Dual D-S T Types.≡c Types.T-Dual D-S U
dual-preserves-≡c {T = T} {U = U} eq =
  Types.≡c-trns
    (Types.dual-tinv T)
    (Types.≡c-trns
      (t-dual-preserves-≡c eq)
      (Types.≡c-symm (Types.dual-tinv U)))

subst-dualNFKind :
  ∀ {Δ₁ Δ₂ K}
    (σ : NFSub Δ₁ Δ₂)
    (d : Dualizable K)
    (T : NFKind Δ₁ K)
  → substNFKindWith σ (dualNFKind d T)
      ≡ dualNFKind d (substNFKindWith σ T)
subst-dualNFKind {K = KV KS m} σ D-S T =
  nfTyTy-injective
    (trans
      (substNFTy-sound σ (dualNFKind D-S T))
      (trans
        (Types.nf-complete d?⊥ d?⊥ left-common)
        (trans
          (sym (Types.nf-complete d?⊥ d?⊥ right-common))
          (sym (dualNFKind-sound D-S (substNFTyWith σ T))))))
  where
  common : Types.Ty _ (KV KS m)
  common = Types.T-Dual D-S (nfTyTy T ⋯ nfSubTy σ)

  dual-sound :
    nfTyTy (dualNFKind D-S T)
      Types.≡c
    Types.T-Dual D-S (nfTyTy T)
  dual-sound =
    Types.≡c-trns
      (Types.≡c-refl-eq (dualNFKind-sound D-S T))
      (Types.nf-sound+ {f = d?⊥} (Types.T-Dual D-S (nfTyTy T)))

  left-common :
    (nfTyTy (dualNFKind D-S T) ⋯ nfSubTy σ)
      Types.≡c common
  left-common = subst-preserves-≡c dual-sound (nfSubTy σ)

  substituted-sound :
    nfTyTy (substNFTyWith σ T)
      Types.≡c
    (nfTyTy T ⋯ nfSubTy σ)
  substituted-sound =
    Types.≡c-trns
      (Types.≡c-refl-eq (substNFTy-sound σ T))
      (Types.nf-sound+ {f = d?⊥} (nfTyTy T ⋯ nfSubTy σ))

  right-common :
    Types.T-Dual D-S (nfTyTy (substNFTyWith σ T))
      Types.≡c common
  right-common = dual-preserves-≡c substituted-sound

subst-minusNF :
  ∀ {Δ₁ Δ₂}
    (σ : NFSub Δ₁ Δ₂)
    (P : NFProto Δ₁)
  → substNFProtoWith σ (minusNF P)
      ≡ minusNF (substNFProtoWith σ P)
subst-minusNF σ (NT.N-Normal P) = refl
subst-minusNF σ (NT.N-Minus P)
  with substNFProto′With σ P
... | NT.N-Normal Q = refl
... | NT.N-Minus Q = refl

subst-msgNF :
  ∀ {Δ₁ Δ₂}
    (σ : NFSub Δ₁ Δ₂)
    (p : D.Polarity)
    (P : NFProto Δ₁)
    (S : NFTy Δ₁ SLin)
  → substNFTyWith σ (msgNF p P S)
      ≡ msgNF p (substNFProtoWith σ P) (substNFTyWith σ S)
subst-msgNF σ p (NT.N-Normal P) S = refl
subst-msgNF σ p (NT.N-Minus P) S
  with substNFProto′With σ P
... | NT.N-Normal Q = refl
... | NT.N-Minus Q
  rewrite D.invert-involution {p} =
  refl

NFSubEq :
  ∀ {Δ₁ Δ₂}
  → NFSub Δ₁ Δ₂
  → NFSub Δ₁ Δ₂
  → Set
NFSubEq σ τ = ∀ K (x : K ∈ _) → σ K x ≡ τ K x

lift-NFSubEq :
  ∀ {Δ₁ Δ₂ K}
    {σ τ : NFSub Δ₁ Δ₂}
  → NFSubEq σ τ
  → NFSubEq (wkNFSub {K = K} σ) (wkNFSub {K = K} τ)
lift-NFSubEq rel K′ (hereₗ refl) = refl
lift-NFSubEq rel K′ (thereₗ x) =
  cong (wkNFKind {K′ = _}) (rel K′ x)

mutual

  substNFProto′-cong :
    ∀ {Δ₁ Δ₂}
      (σ τ : NFSub Δ₁ Δ₂)
      (P : NFProto′ Δ₁)
    → NFSubEq σ τ
    → substNFProto′With σ P ≡ substNFProto′With τ P
  substNFProto′-cong σ τ (NT.N-ProtoP ss v P) rel =
    cong (λ Q → NT.N-Normal (NT.N-ProtoP ss v Q))
      (substNFProto-cong σ τ P rel)
  substNFProto′-cong σ τ (NT.N-Up T) rel =
    cong (λ U → NT.N-Normal (NT.N-Up U))
      (substNFTy-cong σ τ T rel)
  substNFProto′-cong σ τ (NT.N-Var x) rel = rel _ x

  substNFProto-cong :
    ∀ {Δ₁ Δ₂}
      (σ τ : NFSub Δ₁ Δ₂)
      (P : NFProto Δ₁)
    → NFSubEq σ τ
    → substNFProtoWith σ P ≡ substNFProtoWith τ P
  substNFProto-cong σ τ (NT.N-Normal P) rel =
    substNFProto′-cong σ τ P rel
  substNFProto-cong σ τ (NT.N-Minus P) rel =
    cong minusNF (substNFProto′-cong σ τ P rel)

  substNFVar-cong :
    ∀ {Δ₁ Δ₂ K}
      (σ τ : NFSub Δ₁ Δ₂)
      (V : NFVar Δ₁ K)
    → NFSubEq σ τ
    → substNFVarWith σ V ≡ substNFVarWith τ V
  substNFVar-cong σ τ (NT.NV-Var x) rel = rel _ x
  substNFVar-cong σ τ (NT.NV-Dual d x) rel =
    cong (dualNFKind d) (rel _ x)

  substNFTy-cong :
    ∀ {Δ₁ Δ₂ pk m}
      (σ τ : NFSub Δ₁ Δ₂)
      (T : NFTy Δ₁ (KV pk m))
    → NFSubEq σ τ
    → substNFTyWith σ T ≡ substNFTyWith τ T
  substNFTy-cong σ τ (NT.N-Var V) rel =
    substNFVar-cong σ τ V rel
  substNFTy-cong σ τ NT.N-Base rel = refl
  substNFTy-cong σ τ (NT.N-Arrow T U) rel =
    cong₂ NT.N-Arrow
      (substNFTy-cong σ τ T rel)
      (substNFTy-cong σ τ U rel)
  substNFTy-cong σ τ (NT.N-Pair T U) rel =
    cong₂ NT.N-Pair
      (substNFTy-cong σ τ T rel)
      (substNFTy-cong σ τ U rel)
  substNFTy-cong σ τ (NT.N-Poly K T) rel =
    cong (NT.N-Poly K)
      (substNFTy-cong
        (wkNFSub σ)
        (wkNFSub τ)
        T
        (lift-NFSubEq {K = K} rel))
  substNFTy-cong σ τ (NT.N-Sub K≤K′ T) rel =
    cong (NT.N-Sub K≤K′) (substNFTy-cong σ τ T rel)
  substNFTy-cong σ τ NT.N-End rel = refl
  substNFTy-cong σ τ (NT.N-Msg p P S) rel =
    cong₂ (msgNF p)
      (substNFProto′-cong σ τ P rel)
      (substNFTy-cong σ τ S rel)
  substNFTy-cong σ τ (NT.N-ProtoD T) rel =
    cong NT.N-ProtoD (substNFTy-cong σ τ T rel)

composeNFSub :
  ∀ {Δ₁ Δ₂ Δ₃}
  → NFSub Δ₁ Δ₂
  → NFSub Δ₂ Δ₃
  → NFSub Δ₁ Δ₃
composeNFSub σ τ K x = substNFKindWith τ (σ K x)

compose-wk :
  ∀ {Δ₁ Δ₂ Δ₃ K}
    (σ : NFSub Δ₁ Δ₂)
    (τ : NFSub Δ₂ Δ₃)
  → NFSubEq
      (composeNFSub (wkNFSub {K = K} σ) (wkNFSub τ))
      (wkNFSub (composeNFSub σ τ))
compose-wk σ τ KP (hereₗ refl) = refl
compose-wk σ τ (KV pk m) (hereₗ refl) = refl
compose-wk σ τ KP (thereₗ x) = substNFProto-wk τ (σ KP x)
compose-wk σ τ (KV pk m) (thereₗ x) = substNFTy-wk τ (σ (KV pk m) x)

mutual

  substNFProto′-compose :
    ∀ {Δ₁ Δ₂ Δ₃}
      (σ : NFSub Δ₁ Δ₂)
      (τ : NFSub Δ₂ Δ₃)
      (P : NFProto′ Δ₁)
    → substNFProtoWith τ (substNFProto′With σ P)
        ≡ substNFProto′With (composeNFSub σ τ) P
  substNFProto′-compose σ τ (NT.N-ProtoP ss v P) =
    cong (λ Q → NT.N-Normal (NT.N-ProtoP ss v Q))
      (substNFProto-compose σ τ P)
  substNFProto′-compose σ τ (NT.N-Up T) =
    cong (λ U → NT.N-Normal (NT.N-Up U))
      (substNFTy-compose σ τ T)
  substNFProto′-compose σ τ (NT.N-Var x) = refl

  substNFProto-compose :
    ∀ {Δ₁ Δ₂ Δ₃}
      (σ : NFSub Δ₁ Δ₂)
      (τ : NFSub Δ₂ Δ₃)
      (P : NFProto Δ₁)
    → substNFProtoWith τ (substNFProtoWith σ P)
        ≡ substNFProtoWith (composeNFSub σ τ) P
  substNFProto-compose σ τ (NT.N-Normal P) =
    substNFProto′-compose σ τ P
  substNFProto-compose σ τ (NT.N-Minus P) =
    trans
      (subst-minusNF τ (substNFProto′With σ P))
      (cong minusNF (substNFProto′-compose σ τ P))

  substNFVar-compose :
    ∀ {Δ₁ Δ₂ Δ₃ K}
      (σ : NFSub Δ₁ Δ₂)
      (τ : NFSub Δ₂ Δ₃)
      (V : NFVar Δ₁ K)
    → substNFKindWith τ (substNFVarWith σ V)
        ≡ substNFVarWith (composeNFSub σ τ) V
  substNFVar-compose σ τ (NT.NV-Var x) = refl
  substNFVar-compose σ τ (NT.NV-Dual d x) =
    subst-dualNFKind τ d (σ _ x)

  substNFTy-compose :
    ∀ {Δ₁ Δ₂ Δ₃ pk m}
      (σ : NFSub Δ₁ Δ₂)
      (τ : NFSub Δ₂ Δ₃)
      (T : NFTy Δ₁ (KV pk m))
    → substNFTyWith τ (substNFTyWith σ T)
        ≡ substNFTyWith (composeNFSub σ τ) T
  substNFTy-compose σ τ (NT.N-Var V) =
    substNFVar-compose σ τ V
  substNFTy-compose σ τ NT.N-Base = refl
  substNFTy-compose σ τ (NT.N-Arrow T U) =
    cong₂ NT.N-Arrow
      (substNFTy-compose σ τ T)
      (substNFTy-compose σ τ U)
  substNFTy-compose σ τ (NT.N-Pair T U) =
    cong₂ NT.N-Pair
      (substNFTy-compose σ τ T)
      (substNFTy-compose σ τ U)
  substNFTy-compose σ τ (NT.N-Poly K T) =
    cong (NT.N-Poly K)
      (trans
        (substNFTy-compose (wkNFSub σ) (wkNFSub τ) T)
        (substNFTy-cong
          (composeNFSub (wkNFSub σ) (wkNFSub τ))
          (wkNFSub (composeNFSub σ τ))
          T
          (compose-wk σ τ)))
  substNFTy-compose σ τ (NT.N-Sub K≤K′ T) =
    cong (NT.N-Sub K≤K′) (substNFTy-compose σ τ T)
  substNFTy-compose σ τ NT.N-End = refl
  substNFTy-compose σ τ (NT.N-Msg p P S) =
    trans
      (subst-msgNF τ p
        (substNFProto′With σ P)
        (substNFTyWith σ S))
      (cong₂ (msgNF p)
        (substNFProto′-compose σ τ P)
        (substNFTy-compose σ τ S))
  substNFTy-compose σ τ (NT.N-ProtoD T) =
    cong NT.N-ProtoD (substNFTy-compose σ τ T)

identityNFSub : ∀ {Δ} → NFSub Δ Δ
identityNFSub K x = nfVarKind x

mutual

  substNFProto′-identity :
    ∀ {Δ} (P : NFProto′ Δ)
    → substNFProto′With identityNFSub P ≡ NT.N-Normal P
  substNFProto′-identity (NT.N-ProtoP ss v P) =
    cong (λ Q → NT.N-Normal (NT.N-ProtoP ss v Q))
      (substNFProto-identity P)
  substNFProto′-identity (NT.N-Up T) =
    cong (λ U → NT.N-Normal (NT.N-Up U))
      (substNFTy-identity T)
  substNFProto′-identity (NT.N-Var x) = refl

  substNFProto-identity :
    ∀ {Δ} (P : NFProto Δ)
    → substNFProtoWith identityNFSub P ≡ P
  substNFProto-identity (NT.N-Normal P) =
    substNFProto′-identity P
  substNFProto-identity (NT.N-Minus P) =
    cong minusNF (substNFProto′-identity P)

  substNFTy-identity :
    ∀ {Δ pk m} (T : NFTy Δ (KV pk m))
    → substNFTyWith identityNFSub T ≡ T
  substNFTy-identity (NT.N-Var (NT.NV-Var x)) = refl
  substNFTy-identity (NT.N-Var (NT.NV-Dual D-S x)) = refl
  substNFTy-identity NT.N-Base = refl
  substNFTy-identity (NT.N-Arrow T U) =
    cong₂ NT.N-Arrow (substNFTy-identity T) (substNFTy-identity U)
  substNFTy-identity (NT.N-Pair T U) =
    cong₂ NT.N-Pair (substNFTy-identity T) (substNFTy-identity U)
  substNFTy-identity (NT.N-Poly K T) =
    cong (NT.N-Poly K)
      (trans
        (substNFTy-cong
          (wkNFSub identityNFSub)
          identityNFSub
          T
          rel)
        (substNFTy-identity T))
    where
    rel : NFSubEq (wkNFSub {K = K} identityNFSub) identityNFSub
    rel K′ (hereₗ refl) = refl
    rel KP (thereₗ x) = refl
    rel (KV pk m) (thereₗ x) = refl
  substNFTy-identity (NT.N-Sub K≤K′ T) =
    cong (NT.N-Sub K≤K′) (substNFTy-identity T)
  substNFTy-identity NT.N-End = refl
  substNFTy-identity (NT.N-Msg p P S) =
    cong₂ (msgNF p) proto′ (substNFTy-identity S)
    where
    proto′ :
      substNFProto′With identityNFSub P ≡ NT.N-Normal P
    proto′ = substNFProto′-identity P
  substNFTy-identity (NT.N-ProtoD T) =
    cong NT.N-ProtoD (substNFTy-identity T)

cancel-single-wk-proto :
  ∀ {Δ K}
    (U : NFKind Δ K)
    (P : NFProto Δ)
  → substNFProtoWith (singleNFSub U) (renNFProto (weakenᵣ K) P)
      ≡ P
cancel-single-wk-proto {K = K} U P =
  trans
    (subst-renNFProto
      (weakenᵣ K)
      (singleNFSub U)
      identityNFSub
      P
      rel)
    (substNFProto-identity P)
  where
  rel :
    RenNFSubRel (weakenᵣ K) (singleNFSub U) identityNFSub
  rel K′ x = refl

cancel-single-wk-ty :
  ∀ {Δ K pk m}
    (U : NFKind Δ K)
    (T : NFTy Δ (KV pk m))
  → substNFTyWith (singleNFSub U) (renNFTy (weakenᵣ K) T)
      ≡ T
cancel-single-wk-ty {K = K} U T =
  trans
    (subst-renNFTy
      (weakenᵣ K)
      (singleNFSub U)
      identityNFSub
      T
      rel)
    (substNFTy-identity T)
  where
  rel :
    RenNFSubRel (weakenᵣ K) (singleNFSub U) identityNFSub
  rel K′ x = refl

cancel-single-wk-binding :
  ∀ {Δ K}
    (U : NFKind Δ K)
    (b : Binding Δ)
  → substBindingWith (singleNFSub U) (wkBinding {K = K} b) ≡ b
cancel-single-wk-binding U (B-Lin T)
  rewrite cancel-single-wk-ty U T = refl
cancel-single-wk-binding U (B-Un T)
  rewrite cancel-single-wk-ty U T = refl
cancel-single-wk-binding U (B-Used T)
  rewrite cancel-single-wk-ty U T = refl

cancel-single-wk-ctx :
  ∀ {Δ K n}
    (U : NFKind Δ K)
    (Γ : Ctx Δ n)
  → substCtxWith (singleNFSub U) (wkCtx {K = K} Γ) ≡ Γ
cancel-single-wk-ctx U ∅ = refl
cancel-single-wk-ctx U (b ▻ Γ)
  rewrite cancel-single-wk-binding U b
        | cancel-single-wk-ctx U Γ = refl

single-compose-wk :
  ∀ {Δ₁ Δ₂ K}
    (σ : NFSub Δ₁ Δ₂)
    (U : NFKind Δ₁ K)
  → NFSubEq
      (composeNFSub (singleNFSub U) σ)
      (composeNFSub
        (wkNFSub σ)
        (singleNFSub (substNFKindWith σ U)))
single-compose-wk σ U KP (hereₗ refl) = refl
single-compose-wk σ U (KV pk m) (hereₗ refl) = refl
single-compose-wk σ U KP (thereₗ x) =
  sym (cancel-single-wk-proto (substNFKindWith σ U) (σ KP x))
single-compose-wk σ U (KV pk m) (thereₗ x) =
  sym
    (cancel-single-wk-ty
      (substNFKindWith σ U)
      (σ (KV pk m) x))

subst-typeApplication :
  ∀ {Δ₁ Δ₂ K pk m}
    (σ : NFSub Δ₁ Δ₂)
    (T : NFTy (K ∷ Δ₁) (KV pk m))
    (U : NFKind Δ₁ K)
  → substNFTyWith σ (substNFTy T U)
      ≡ substNFTy
          (substNFTyWith (wkNFSub σ) T)
          (substNFKindWith σ U)
subst-typeApplication σ T U =
  trans
    (substNFTy-compose (singleNFSub U) σ T)
    (trans
      (substNFTy-cong
        (composeNFSub (singleNFSub U) σ)
        (composeNFSub
          (wkNFSub σ)
          (singleNFSub (substNFKindWith σ U)))
        T
        (single-compose-wk σ U))
      (sym
        (substNFTy-compose
          (wkNFSub σ)
          (singleNFSub (substNFKindWith σ U))
          T)))

normalizeProto-sound :
  ∀ {Δ} (P : Ty Δ KP)
  → nfProtoTy (normalizeTy P) Types.≡c P
normalizeProto-sound P =
  Types.≡c-trns
    (Types.≡c-refl-eq
      (nfProtoTy-fromNormalProto (Types.nf-normal-proto P)))
    (Types.nf-sound+ {f = d?⊥} P)

RawSubEq :
  ∀ {Δ₁ Δ₂}
  → (Δ₁ →ₛ Δ₂)
  → (Δ₁ →ₛ Δ₂)
  → Set
RawSubEq ϕ ψ = ∀ K (x : K ∈ _) → ϕ K x ≡ ψ K x

lift-RawSubEq :
  ∀ {Δ₁ Δ₂ K}
    {ϕ ψ : Δ₁ →ₛ Δ₂}
  → RawSubEq ϕ ψ
  → RawSubEq (ϕ ↑ₛ K) (ψ ↑ₛ K)
lift-RawSubEq rel K′ (hereₗ refl) = refl
lift-RawSubEq {K = K} rel K′ (thereₗ x) =
  cong (λ T → T ⋯ weakenᵣ K) (rel K′ x)

substTy-cong-pointwise :
  ∀ {Δ₁ Δ₂ K}
    (T : Ty Δ₁ K)
    (ϕ ψ : Δ₁ →ₛ Δ₂)
  → RawSubEq ϕ ψ
  → T ⋯ ϕ ≡ T ⋯ ψ
substTy-cong-pointwise (Types.T-Var x) ϕ ψ rel = rel _ x
substTy-cong-pointwise Types.T-Base ϕ ψ rel = refl
substTy-cong-pointwise (Types.T-Arrow T U) ϕ ψ rel =
  cong₂ Types.T-Arrow
    (substTy-cong-pointwise T ϕ ψ rel)
    (substTy-cong-pointwise U ϕ ψ rel)
substTy-cong-pointwise (Types.T-Pair T U) ϕ ψ rel =
  cong₂ Types.T-Pair
    (substTy-cong-pointwise T ϕ ψ rel)
    (substTy-cong-pointwise U ϕ ψ rel)
substTy-cong-pointwise (Types.T-Poly K T) ϕ ψ rel =
  cong (Types.T-Poly K)
    (substTy-cong-pointwise
      T
      (ϕ ↑ₛ K)
      (ψ ↑ₛ K)
      (lift-RawSubEq {K = K} rel))
substTy-cong-pointwise (Types.T-Sub K≤K′ T) ϕ ψ rel =
  cong (Types.T-Sub K≤K′) (substTy-cong-pointwise T ϕ ψ rel)
substTy-cong-pointwise (Types.T-Dual d T) ϕ ψ rel =
  cong (Types.T-Dual d) (substTy-cong-pointwise T ϕ ψ rel)
substTy-cong-pointwise Types.T-End ϕ ψ rel = refl
substTy-cong-pointwise (Types.T-Msg p P S) ϕ ψ rel =
  cong₂ (Types.T-Msg p)
    (substTy-cong-pointwise P ϕ ψ rel)
    (substTy-cong-pointwise S ϕ ψ rel)
substTy-cong-pointwise (Types.T-Up T) ϕ ψ rel =
  cong Types.T-Up (substTy-cong-pointwise T ϕ ψ rel)
substTy-cong-pointwise (Types.T-Minus P) ϕ ψ rel =
  cong Types.T-Minus (substTy-cong-pointwise P ϕ ψ rel)
substTy-cong-pointwise (Types.T-ProtoD T) ϕ ψ rel =
  cong Types.T-ProtoD (substTy-cong-pointwise T ϕ ψ rel)
substTy-cong-pointwise (Types.T-ProtoP ss v P) ϕ ψ rel =
  cong (Types.T-ProtoP ss v) (substTy-cong-pointwise P ϕ ψ rel)

singletonNFSub :
  ∀ {Δ}
  → NFProto Δ
  → NFSub (KP ∷ []) Δ
singletonNFSub P KP (hereₗ refl) = P
singletonNFSub P K (thereₗ ())

singletonNFSub-sound :
  ∀ {Δ}
    (P : NFProto Δ)
  → RawSubEq
      (nfSubTy (singletonNFSub P))
      (singletonSubst (nfProtoTy P))
singletonNFSub-sound P KP (hereₗ refl) = refl
singletonNFSub-sound P K (thereₗ ())

normalize-instantiate :
  ∀ {Δ}
    (T : Ty (KP ∷ []) KP)
    (P : NFProto Δ)
  → normalizeTy (instantiate ⦃ Kₛ ⦄ D.⊕ T (nfProtoTy P))
      ≡ substNFProtoWith (singletonNFSub P) (normalizeTy T)
normalize-instantiate T P =
  sym
    (nfProtoTy-injective
      (trans
        (substNFProto-sound (singletonNFSub P) (normalizeTy T))
        (trans
          (Types.nf-complete d?⊥ d?⊥
            (Types.≡c-trns
              (Types.≡c-refl-eq
                (substTy-cong-pointwise
                  (nfProtoTy (normalizeTy T))
                  (nfSubTy (singletonNFSub P))
                  (singletonSubst (nfProtoTy P))
                  (singletonNFSub-sound P)))
              (subst-preserves-≡c
                (normalizeProto-sound T)
                (singletonSubst (nfProtoTy P)))))
          (sym
            (nfProtoTy-fromNormalProto
              (Types.nf-normal-proto
                (instantiate ⦃ Kₛ ⦄ D.⊕ T (nfProtoTy P))))))))

single-proto-compose :
  ∀ {Δ₁ Δ₂}
    (σ : NFSub Δ₁ Δ₂)
    (P : NFProto Δ₁)
  → NFSubEq
      (composeNFSub (singletonNFSub P) σ)
      (singletonNFSub (substNFProtoWith σ P))
single-proto-compose σ P KP (hereₗ refl) = refl
single-proto-compose σ P K (thereₗ ())

subst-normalize-instantiate :
  ∀ {Δ₁ Δ₂}
    (σ : NFSub Δ₁ Δ₂)
    (T : Ty (KP ∷ []) KP)
    (P : NFProto Δ₁)
  → substNFProtoWith σ
      (normalizeTy (instantiate ⦃ Kₛ ⦄ D.⊕ T (nfProtoTy P)))
      ≡
    normalizeTy
      (instantiate ⦃ Kₛ ⦄ D.⊕ T
        (nfProtoTy (substNFProtoWith σ P)))
subst-normalize-instantiate σ T P =
  trans
    (cong (substNFProtoWith σ) (normalize-instantiate T P))
    (trans
      (substNFProto-compose (singletonNFSub P) σ (normalizeTy T))
      (trans
        (substNFProto-cong
          (composeNFSub (singletonNFSub P) σ)
          (singletonNFSub (substNFProtoWith σ P))
          (normalizeTy T)
          (single-proto-compose σ P))
        (sym (normalize-instantiate T (substNFProtoWith σ P)))))

subst-materializeListNf :
  ∀ {Δ₁ Δ₂}
    (σ : NFSub Δ₁ Δ₂)
    (Ts : List (Ty (KP ∷ []) KP))
    (p : D.Polarity)
    (P : NFProto Δ₁)
    (S : NFTy Δ₁ SLin)
  → substNFTyWith σ (materializeListNf Ts p P S)
      ≡ materializeListNf Ts p
          (substNFProtoWith σ P)
          (substNFTyWith σ S)
subst-materializeListNf σ [] p P S = refl
subst-materializeListNf σ (T ∷ Ts) p P S =
  trans
    (subst-msgNF σ p
      (normalizeTy (instantiate ⦃ Kₛ ⦄ p T (nfProtoTy P)))
      (materializeListNf Ts p P S))
    (cong₂ (msgNF p)
      (subst-normalize-instantiate σ T P)
      (subst-materializeListNf σ Ts p P S))

subst-select2 :
  ∀ {Δ₁ Δ₂ k}
    (σ : NFSub Δ₁ Δ₂)
    (v : Variance)
    (i : Fin k)
    (P : NFProto Δ₁)
    (S : NFTy Δ₁ SLin)
  → substNFTyWith σ (selectNf v i P S)
      ≡ selectNf v i
          (substNFProtoWith σ P)
          (substNFTyWith σ S)
subst-select2 σ v i P S =
  cong₂ NT.N-Arrow
    refl
    (subst-materializeListNf
      σ
      (proj₁ (ProtocolConstructors _ v i))
      D.⊕
      P
      S)

subst-select1 :
  ∀ {Δ₁ Δ₂ k}
    (σ : NFSub Δ₁ Δ₂)
    (v : Variance)
    (i : Fin k)
    (P : NFProto Δ₁)
  → substNFTyWith σ (select1Nf v i P)
      ≡ select1Nf v i (substNFProtoWith σ P)
subst-select1 σ v i P =
  cong (NT.N-Poly SLin)
    (trans
      (subst-select2
        (wkNFSub σ)
        v
        i
        (renNFProto (weakenᵣ SLin) P)
        (NT.N-Var (NT.NV-Var (hereₗ refl))))
      (cong₂ (selectNf v i)
        (substNFProto-wk {K = SLin} σ P)
        refl))

subst-matchOutput :
  ∀ {Δ₁ Δ₂ k}
    (σ : NFSub Δ₁ Δ₂)
    (ss : Subset.Subset (sucℕ k))
    (v : Variance)
    (P : NFProto Δ₁)
    (S : NFTy Δ₁ SLin)
    (i : Fin (sucℕ k))
    (i∈ : i Subset.∈ ss)
  → substNFTyWith σ (MatchBranchOutput ss v P S i i∈)
      ≡ MatchBranchOutput ss v
          (substNFProtoWith σ P)
          (substNFTyWith σ S)
          i i∈
subst-matchOutput σ ss v P S i i∈ =
  subst-materializeListNf
    σ
    (proj₁ (ProtocolConstructors _ v i))
    D.⊝
    P
    S

subst-selectConst :
  ∀ {Δ₁ Δ₂ k}
    (σ : NFSub Δ₁ Δ₂)
    (v : Variance)
    (i : Fin k)
  → substNFTyWith σ (selectConstNf v i) ≡ selectConstNf v i
subst-selectConst σ v i =
  cong (NT.N-Poly KP)
    (subst-select1
      (wkNFSub σ)
      v
      i
      (NT.N-Normal (NT.N-Var (hereₗ refl))))

subst-preserves-ConstTy :
  ∀ {Δ₁ Δ₂ K c}
    (σ : NFSub Δ₁ Δ₂)
    {T : NFKind Δ₁ K}
  → ConstTy c T
  → ConstTy c (substNFKindWith σ T)
subst-preserves-ConstTy σ CT-Unit = CT-Unit
subst-preserves-ConstTy σ CT-Fork = CT-Fork
subst-preserves-ConstTy σ CT-New = CT-New
subst-preserves-ConstTy σ CT-Receive
  rewrite subst-receive1
    (wkNFSub {K = TLin} σ)
    (NT.N-Var (NT.NV-Var (hereₗ refl))) =
  CT-Receive
subst-preserves-ConstTy σ CT-Send
  rewrite subst-send1
    (wkNFSub {K = TLin} σ)
    (NT.N-Var (NT.NV-Var (hereₗ refl))) =
  CT-Send
subst-preserves-ConstTy σ CT-Close = CT-Close
subst-preserves-ConstTy σ (CT-Select {v = v} {i = i})
  rewrite subst-selectConst σ v i =
  CT-Select

RawNFRel :
  ∀ {Δ₁ Δ₂}
  → (Δ₁ →ₛ Δ₂)
  → NFSub Δ₁ Δ₂
  → Set
RawNFRel ϕ σ =
  ∀ K (x : K ∈ _) → toNFSub ϕ K x ≡ σ K x

lift-RawNFRel :
  ∀ {Δ₁ Δ₂ K}
    {ϕ : Δ₁ →ₛ Δ₂}
    {σ : NFSub Δ₁ Δ₂}
  → RawNFRel ϕ σ
  → RawNFRel (ϕ ↑ₛ K) (wkNFSub {K = K} σ)
lift-RawNFRel rel KP (hereₗ refl) = refl
lift-RawNFRel rel (KV pk m) (hereₗ refl) = refl
lift-RawNFRel {K = K} {ϕ = ϕ} {σ = σ} rel KP (thereₗ x) =
  trans
    (sym (ren-normalizeProto (weakenᵣ K) (ϕ KP x)))
    (cong (renNFProto (weakenᵣ K)) (rel KP x))
lift-RawNFRel {K = K} {ϕ = ϕ} {σ = σ} rel (KV pk m) (thereₗ x) =
  trans
    (sym (ren-normalizeTy (weakenᵣ K) (ϕ (KV pk m) x)))
    (cong (renNFTy (weakenᵣ K)) (rel (KV pk m) x))

nfSubTy-related :
  ∀ {Δ₁ Δ₂}
    (σ : NFSub Δ₁ Δ₂)
  → RawNFRel (nfSubTy σ) σ
nfSubTy-related σ KP x = normalizeTy-id (σ KP x)
nfSubTy-related σ (KV pk m) x = normalizeTy-id (σ (KV pk m) x)

mutual

  rawNF-value :
    ∀ {Δ₁ Δ₂ n}
      (ϕ : Δ₁ →ₛ Δ₂)
      (σ : NFSub Δ₁ Δ₂)
      (v : Value Δ₁ n)
    → RawNFRel ϕ σ
    → substTyValueWith ϕ v ≡ substNFValueWith σ v
  rawNF-value ϕ σ (V-Const c) rel = refl
  rawNF-value ϕ σ (V-Var x) rel = refl
  rawNF-value ϕ σ (V-Abs T e) rel =
    cong₂ V-Abs
      (substNFTy-cong (toNFSub ϕ) σ T rel)
      (rawNF-expr ϕ σ e rel)
  rawNF-value ϕ σ (V-Rec T U v) rel =
    trans
      (cong₂
        (λ X Y → V-Rec X Y (substTyValueWith ϕ v))
        (substNFTy-cong (toNFSub ϕ) σ T rel)
        (substNFTy-cong (toNFSub ϕ) σ U rel))
      (cong (V-Rec (substNFTyWith σ T) (substNFTyWith σ U))
        (rawNF-value ϕ σ v rel))
  rawNF-value ϕ σ (V-TAbs K v) rel =
    cong (V-TAbs K)
      (rawNF-value
        (ϕ ↑ₛ K)
        (wkNFSub σ)
        v
        (lift-RawNFRel {K = K} rel))
  rawNF-value ϕ σ (V-Pair u v) rel =
    cong₂ V-Pair (rawNF-value ϕ σ u rel) (rawNF-value ϕ σ v rel)
  rawNF-value ϕ σ (V-Receive₁ T) rel =
    cong V-Receive₁ (substNFTy-cong (toNFSub ϕ) σ T rel)
  rawNF-value ϕ σ (V-Receive₂ T S) rel =
    cong₂ V-Receive₂
      (substNFTy-cong (toNFSub ϕ) σ T rel)
      (substNFTy-cong (toNFSub ϕ) σ S rel)
  rawNF-value ϕ σ (V-Send₁ T) rel =
    cong V-Send₁ (substNFTy-cong (toNFSub ϕ) σ T rel)
  rawNF-value ϕ σ (V-Send₂ T S) rel =
    cong₂ V-Send₂
      (substNFTy-cong (toNFSub ϕ) σ T rel)
      (substNFTy-cong (toNFSub ϕ) σ S rel)
  rawNF-value ϕ σ (V-Select₁ v i P) rel =
    cong (V-Select₁ v i) (substNFProto-cong (toNFSub ϕ) σ P rel)
  rawNF-value ϕ σ (V-Select₂ v i P S) rel =
    cong₂ (V-Select₂ v i)
      (substNFProto-cong (toNFSub ϕ) σ P rel)
      (substNFTy-cong (toNFSub ϕ) σ S rel)

  rawNF-expr :
    ∀ {Δ₁ Δ₂ n}
      (ϕ : Δ₁ →ₛ Δ₂)
      (σ : NFSub Δ₁ Δ₂)
      (e : Expr Δ₁ n)
    → RawNFRel ϕ σ
    → substTyExprWith ϕ e ≡ substNFExprWith σ e
  rawNF-expr ϕ σ (E-Val v) rel =
    cong E-Val (rawNF-value ϕ σ v rel)
  rawNF-expr ϕ σ (E-App e₁ e₂) rel =
    cong₂ E-App (rawNF-expr ϕ σ e₁ rel) (rawNF-expr ϕ σ e₂ rel)
  rawNF-expr ϕ σ (E-TApp {K = KP} e P) rel =
    cong₂ E-TApp
      (rawNF-expr ϕ σ e rel)
      (substNFProto-cong (toNFSub ϕ) σ P rel)
  rawNF-expr ϕ σ (E-TApp {K = KV pk m} e T) rel =
    cong₂ E-TApp
      (rawNF-expr ϕ σ e rel)
      (substNFTy-cong (toNFSub ϕ) σ T rel)
  rawNF-expr ϕ σ (E-LetUnit e₁ e₂) rel =
    cong₂ E-LetUnit
      (rawNF-expr ϕ σ e₁ rel)
      (rawNF-expr ϕ σ e₂ rel)
  rawNF-expr ϕ σ (E-Pair e₁ e₂) rel =
    cong₂ E-Pair (rawNF-expr ϕ σ e₁ rel) (rawNF-expr ϕ σ e₂ rel)
  rawNF-expr ϕ σ (E-LetPair e₁ e₂) rel =
    cong₂ E-LetPair
      (rawNF-expr ϕ σ e₁ rel)
      (rawNF-expr ϕ σ e₂ rel)
  rawNF-expr ϕ σ (E-Match e ne branches) rel =
    cong₂ (λ e′ bs → E-Match e′ ne bs)
      (rawNF-expr ϕ σ e rel)
      (dependent-ext₂ λ i i∈ →
        rawNF-expr ϕ σ (branches i i∈) rel)

substTyValue-as-NF :
  ∀ {Δ n K}
    (v : Value (K ∷ Δ) n)
    (U : NFKind Δ K)
  → substTyValue v U ≡ substNFValueWith (singleNFSub U) v
substTyValue-as-NF v U =
  rawNF-value
    (nfSubTy (singleNFSub U))
    (singleNFSub U)
    v
    (nfSubTy-related (singleNFSub U))

substTyExpr-as-NF :
  ∀ {Δ n K}
    (e : Expr (K ∷ Δ) n)
    (U : NFKind Δ K)
  → substTyExpr e U ≡ substNFExprWith (singleNFSub U) e
substTyExpr-as-NF e U =
  rawNF-expr
    (nfSubTy (singleNFSub U))
    (singleNFSub U)
    e
    (nfSubTy-related (singleNFSub U))

BranchJoin⁺-subst :
  ∀ {Δ₁ Δ₂ k pk m}
    (σ : NFSub Δ₁ Δ₂)
    {ss : Subset.Subset k}
    {V : (i : Fin k) → i Subset.∈ ss → NFTy Δ₁ (KV pk m)}
    {U : NFTy Δ₁ (KV pk m)}
    {sub : (i : Fin k) → (i∈ : i Subset.∈ ss) → V i i∈ <:ₜ U}
  → BranchJoin⁺ ss V ≡ just (U , sub)
  → Σ ((i : Fin k) → (i∈ : i Subset.∈ ss) →
          substNFTyWith σ (V i i∈) <:ₜ substNFTyWith σ U)
      λ subσ →
        BranchJoin⁺ ss (λ i i∈ → substNFTyWith σ (V i i∈))
          ≡ just (substNFTyWith σ U , subσ)
BranchJoin⁺-subst σ {ss = []ᵥ} ()
BranchJoin⁺-subst σ
    {ss = Subset.outside ∷ᵥ ss}
    {V = V}
    {U = U}
    old
  with BranchJoin⁺ ss (λ i i∈ → V (suc i) (there i∈)) in tail
... | nothing = ⊥-elim (nothing≢just old)
... | just (N , subN)
  with BranchJoin⁺-subst
        σ
        {ss = ss}
        {V = λ i i∈ → V (suc i) (there i∈)}
        tail
... | subσ , tailσ
  with just-output old
... | refl
  rewrite tailσ =
  _ , refl
BranchJoin⁺-subst σ
    {ss = Subset.inside ∷ᵥ ss}
    {V = V}
    {U = U}
    old
  with BranchJoin⁺ ss (λ i i∈ → V (suc i) (there i∈)) in tail
... | nothing = ⊥-elim (nothing≢just old)
... | just (N , subN)
  with AlgorithmicNFMerge.joinₜ (V zero here) N in joined
... | Relation.Nullary.no _ = ⊥-elim (nothing≢just old)
... | Relation.Nullary.yes (W , V₀<:W , N<:W)
  with BranchJoin⁺-subst
        σ
        {ss = ss}
        {V = λ i i∈ → V (suc i) (there i∈)}
        tail
... | subσ , tailσ
  with joinₜ-subst σ (V zero here) N joined
... | V₀σ<:Wσ , Nσ<:Wσ , joinedσ
  with just-output old
... | refl
  rewrite tailσ | joinedσ =
  _ , refl

record BranchJoinSubstitution : Set₁ where
  field
    preserve :
      ∀ {Δ₁ Δ₂ k pk m}
        (σ : NFSub Δ₁ Δ₂)
        {ss : Subset.Subset k}
        {V : (i : Fin k) → i Subset.∈ ss → NFTy Δ₁ (KV pk m)}
        {U : NFTy Δ₁ (KV pk m)}
        {sub : (i : Fin k) → (i∈ : i Subset.∈ ss) → V i i∈ <:ₜ U}
      → BranchJoin⁺ ss V ≡ just (U , sub)
      → Σ ((i : Fin k) → (i∈ : i Subset.∈ ss) →
              substNFTyWith σ (V i i∈) <:ₜ substNFTyWith σ U)
          λ subσ →
            BranchJoin⁺ ss (λ i i∈ → substNFTyWith σ (V i i∈))
              ≡ just (substNFTyWith σ U , subσ)

substitutionAlgebra : BranchJoinSubstitution → SubstitutionAlgebra
substitutionAlgebra branch =
  record
    { const = subst-preserves-ConstTy
    ; receive1 = subst-receive1
    ; receive2 = subst-receive2
    ; send1 = subst-send1
    ; send2 = subst-send2
    ; select1 = subst-select1
    ; select2 = subst-select2
    ; matchInput = subst-matchInput
    ; matchOutput = subst-matchOutput
    ; branchJoin = BranchJoinSubstitution.preserve branch
    ; typeApplication = subst-typeApplication
    }

trustedBranchJoinSubstitution : BranchJoinSubstitution
trustedBranchJoinSubstitution =
  record { preserve = BranchJoin⁺-subst }

trustedSubstitutionAlgebra : SubstitutionAlgebra
trustedSubstitutionAlgebra =
  substitutionAlgebra trustedBranchJoinSubstitution

module Preserve (algebra : SubstitutionAlgebra) where

  open SubstitutionAlgebra algebra

  mutual

    subst-preserves-value :
      ∀ {Δ₁ Δ₂ n pk m}
        (σ : NFSub Δ₁ Δ₂)
        {Γ₁ Γ₂ : Ctx Δ₁ n}
        {v : Value Δ₁ n}
        {T : NFTy Δ₁ (KV pk m)}
      → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
      → substCtxWith σ Γ₁
          ⊢ᵥ substNFValueWith σ v
            ⇒ substNFTyWith σ T
            ⊣ substCtxWith σ Γ₂
    subst-preserves-value σ (TV-Const cT) =
      TV-Const (const σ cT)
    subst-preserves-value σ (TV-Var-Lin take) =
      TV-Var-Lin (subst-preserves-take σ take)
    subst-preserves-value σ (TV-Var-Un x∈) =
      TV-Var-Un (subst-preserves-∋ᵘ σ x∈)
    subst-preserves-value σ (TV-Abs body) =
      TV-Abs (subst-preserves-synth σ body)
    subst-preserves-value σ (TV-Rec body) =
      TV-Rec (subst-preserves-check σ body)
    subst-preserves-value
        σ
        {Γ₁ = Γ₁}
        {Γ₂ = Γ₂}
        (TV-TAbs {K = K} body) =
      TV-TAbs premise
      where
      recursive = subst-preserves-value (wkNFSub σ) body

      premise =
        subst
          (λ X →
            wkCtx {K = K} (substCtxWith σ Γ₁)
              ⊢ᵥ substNFValueWith (wkNFSub σ) _
                ⇒ _
                ⊣ X)
          (substCtx-wk σ Γ₂)
          (subst
            (λ X →
              X
                ⊢ᵥ substNFValueWith (wkNFSub σ) _
                  ⇒ _
                  ⊣ substCtxWith (wkNFSub σ) (wkCtx Γ₂))
            (substCtx-wk σ Γ₁)
            recursive)
    subst-preserves-value σ (TV-Pair left right) =
      TV-Pair
        (subst-preserves-value σ left)
        (subst-preserves-value σ right)
    subst-preserves-value σ (TV-Receive₁ {T = T})
      rewrite receive1 σ T =
      TV-Receive₁
    subst-preserves-value σ (TV-Receive₂ {T = T} {S = S})
      rewrite receive2 σ T S =
      TV-Receive₂
    subst-preserves-value σ (TV-Send₁ {T = T})
      rewrite send1 σ T =
      TV-Send₁
    subst-preserves-value σ (TV-Send₂ {T = T} {S = S})
      rewrite send2 σ T S =
      TV-Send₂
    subst-preserves-value σ (TV-Select₁ {v = v} {i = i} {P = P})
      rewrite select1 σ v i P =
      TV-Select₁
    subst-preserves-value σ
        (TV-Select₂ {v = v} {i = i} {P = P} {S = S})
      rewrite select2 σ v i P S =
      TV-Select₂

    subst-preserves-synth :
      ∀ {Δ₁ Δ₂ n pk m}
        (σ : NFSub Δ₁ Δ₂)
        {Γ₁ Γ₂ : Ctx Δ₁ n}
        {e : Expr Δ₁ n}
        {T : NFTy Δ₁ (KV pk m)}
      → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
      → substCtxWith σ Γ₁
          ⊢ substNFExprWith σ e
            ⇒ substNFTyWith σ T
            ⊣ substCtxWith σ Γ₂
    subst-preserves-synth σ (T-Val value) =
      T-Val (subst-preserves-value σ value)
    subst-preserves-synth σ (T-Pair left right) =
      T-Pair
        (subst-preserves-synth σ left)
        (subst-preserves-synth σ right)
    subst-preserves-synth σ (T-App function argument) =
      T-App
        (subst-preserves-synth σ function)
        (subst-preserves-check σ argument)
    subst-preserves-synth σ (T-LetUnit unit body) =
      T-LetUnit
        (subst-preserves-check σ unit)
        (subst-preserves-synth σ body)
    subst-preserves-synth σ (T-LetPair pair body) =
      T-LetPair
        (subst-preserves-synth σ pair)
        (subst-preserves-synth σ body)
    subst-preserves-synth
        σ
        {Γ₁ = Γin}
        {Γ₂ = Γout}
        (T-Match
          {Γ₂ = Γmid}
          {e = e}
          {ss = ss}
          {v = variance}
          {ssbranches = ssbranches}
          {incl = incl}
          {ne = ne}
          {P = P}
          {S = S}
          {U = U}
          {branches = branchExprs}
          {V = V}
          scrutinee
          branches
          joined)
      with branchJoin σ joined
    ... | subσ , joinedσ =
      T-Match
        {ss = ss}
        {v = variance}
        {ssbranches = ssbranches}
        {incl = incl}
        {ne = ne}
        {P = substNFProtoWith σ P}
        {S = substNFTyWith σ S}
        {U = substNFTyWith σ U}
        {V = λ i i∈ → substNFTyWith σ (V i i∈)}
        {sub = subσ}
        scrutineeσ
        branchesσ
        joinedσ
      where
      scrutineeσ =
        subst
          (λ X →
            substCtxWith σ Γin
              ⊢ substNFExprWith σ e
                ⇒ X
                ⊣ substCtxWith σ Γmid)
          (matchInput σ ss variance P S)
          (subst-preserves-synth σ scrutinee)

      branchesσ :
        (i : Fin _)
        → (i∈ : i Subset.∈ ssbranches)
        → (MatchBranchOutput ssbranches variance
              (substNFProtoWith σ P)
              (substNFTyWith σ S)
              i i∈
            ExprNormalTyping.∷ˡ substCtxWith σ Γmid)
            ⊢ substNFExprWith σ (branchExprs i i∈)
              ⇒ substNFTyWith σ (V i i∈)
              ⊣ (B-Used
                    (MatchBranchOutput ssbranches variance
                      (substNFProtoWith σ P)
                      (substNFTyWith σ S)
                      i i∈)
                    ▻ substCtxWith σ Γout)
      branchesσ i i∈ =
        subst
          (λ X →
            (X ExprNormalTyping.∷ˡ substCtxWith σ Γmid)
              ⊢ substNFExprWith σ (branchExprs i i∈)
                ⇒ substNFTyWith σ (V i i∈)
                ⊣ (B-Used X ▻ substCtxWith σ Γout))
          (matchOutput σ ssbranches variance P S i i∈)
          (subst-preserves-synth σ (branches i i∈))
    subst-preserves-synth σ
        (T-TApp {T = T} {U = U} premise)
      rewrite typeApplication σ T U =
      T-TApp (subst-preserves-synth σ premise)

    subst-preserves-check :
      ∀ {Δ₁ Δ₂ n pk m}
        (σ : NFSub Δ₁ Δ₂)
        {Γ₁ Γ₂ : Ctx Δ₁ n}
        {e : Expr Δ₁ n}
        {T : NFTy Δ₁ (KV pk m)}
      → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
      → substCtxWith σ Γ₁
          ⊢ substNFExprWith σ e
            ⇐ substNFTyWith σ T
            ⊣ substCtxWith σ Γ₂
    subst-preserves-check σ (T-Check synth subtyping) =
      T-Check
        (subst-preserves-synth σ synth)
        (subst-preserves-<:ₜ σ subtyping)

module TrustedPreserve = Preserve trustedSubstitutionAlgebra

substNF-preserves-value :
  ∀ {Δ₁ Δ₂ n pk m}
    (σ : NFSub Δ₁ Δ₂)
    {Γ₁ Γ₂ : Ctx Δ₁ n}
    {v : Value Δ₁ n}
    {T : NFTy Δ₁ (KV pk m)}
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  → substCtxWith σ Γ₁
      ⊢ᵥ substNFValueWith σ v
        ⇒ substNFTyWith σ T
        ⊣ substCtxWith σ Γ₂
substNF-preserves-value = TrustedPreserve.subst-preserves-value

substNF-preserves-synth :
  ∀ {Δ₁ Δ₂ n pk m}
    (σ : NFSub Δ₁ Δ₂)
    {Γ₁ Γ₂ : Ctx Δ₁ n}
    {e : Expr Δ₁ n}
    {T : NFTy Δ₁ (KV pk m)}
  → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
  → substCtxWith σ Γ₁
      ⊢ substNFExprWith σ e
        ⇒ substNFTyWith σ T
        ⊣ substCtxWith σ Γ₂
substNF-preserves-synth = TrustedPreserve.subst-preserves-synth

substNF-preserves-check :
  ∀ {Δ₁ Δ₂ n pk m}
    (σ : NFSub Δ₁ Δ₂)
    {Γ₁ Γ₂ : Ctx Δ₁ n}
    {e : Expr Δ₁ n}
    {T : NFTy Δ₁ (KV pk m)}
  → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
  → substCtxWith σ Γ₁
      ⊢ substNFExprWith σ e
        ⇐ substNFTyWith σ T
        ⊣ substCtxWith σ Γ₂
substNF-preserves-check = TrustedPreserve.subst-preserves-check

substTy-preserves-value :
  ∀ {Δ n K pk m}
    {Γ₁ Γ₂ : Ctx (K ∷ Δ) n}
    {v : Value (K ∷ Δ) n}
    {T : NFTy (K ∷ Δ) (KV pk m)}
    (U : NFKind Δ K)
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  → substCtxWith (singleNFSub U) Γ₁
      ⊢ᵥ substTyValue v U
        ⇒ substNFTy T U
        ⊣ substCtxWith (singleNFSub U) Γ₂
substTy-preserves-value
    {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = v} {T = T}
    U derivation =
  subst
    (λ v′ →
      substCtxWith (singleNFSub U) Γ₁
        ⊢ᵥ v′ ⇒ substNFTy T U
        ⊣ substCtxWith (singleNFSub U) Γ₂)
    (sym (substTyValue-as-NF v U))
    (substNF-preserves-value (singleNFSub U) derivation)

substTy-preserves-wk-value :
  ∀ {Δ n K pk m}
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Value (K ∷ Δ) n}
    {T : NFTy (K ∷ Δ) (KV pk m)}
    (U : NFKind Δ K)
  → wkCtx {K = K} Γ₁ ⊢ᵥ v ⇒ T ⊣ wkCtx Γ₂
  → Γ₁ ⊢ᵥ substTyValue v U ⇒ substNFTy T U ⊣ Γ₂
substTy-preserves-wk-value
    {Γ₁ = Γ₁} {Γ₂ = Γ₂} {v = v} {T = T}
    U derivation =
  subst
    (λ X → X ⊢ᵥ substTyValue v U ⇒ substNFTy T U ⊣ Γ₂)
    (cancel-single-wk-ctx U Γ₁)
    (subst
      (λ X →
        substCtxWith (singleNFSub U) (wkCtx Γ₁)
          ⊢ᵥ substTyValue v U ⇒ substNFTy T U ⊣ X)
      (cancel-single-wk-ctx U Γ₂)
      (substTy-preserves-value U derivation))

substTy-preserves-synth :
  ∀ {Δ n K pk m}
    {Γ₁ Γ₂ : Ctx (K ∷ Δ) n}
    {e : Expr (K ∷ Δ) n}
    {T : NFTy (K ∷ Δ) (KV pk m)}
    (U : NFKind Δ K)
  → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
  → substCtxWith (singleNFSub U) Γ₁
      ⊢ substTyExpr e U
        ⇒ substNFTy T U
        ⊣ substCtxWith (singleNFSub U) Γ₂
substTy-preserves-synth
    {Γ₁ = Γ₁} {Γ₂ = Γ₂} {e = e} {T = T}
    U derivation =
  subst
    (λ e′ →
      substCtxWith (singleNFSub U) Γ₁
        ⊢ e′ ⇒ substNFTy T U
        ⊣ substCtxWith (singleNFSub U) Γ₂)
    (sym (substTyExpr-as-NF e U))
    (substNF-preserves-synth (singleNFSub U) derivation)

substTy-preserves-check :
  ∀ {Δ n K pk m}
    {Γ₁ Γ₂ : Ctx (K ∷ Δ) n}
    {e : Expr (K ∷ Δ) n}
    {T : NFTy (K ∷ Δ) (KV pk m)}
    (U : NFKind Δ K)
  → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
  → substCtxWith (singleNFSub U) Γ₁
      ⊢ substTyExpr e U
        ⇐ substNFTy T U
        ⊣ substCtxWith (singleNFSub U) Γ₂
substTy-preserves-check
    {Γ₁ = Γ₁} {Γ₂ = Γ₂} {e = e} {T = T}
    U derivation =
  subst
    (λ e′ →
      substCtxWith (singleNFSub U) Γ₁
        ⊢ e′ ⇐ substNFTy T U
        ⊣ substCtxWith (singleNFSub U) Γ₂)
    (sym (substTyExpr-as-NF e U))
    (substNF-preserves-check (singleNFSub U) derivation)
