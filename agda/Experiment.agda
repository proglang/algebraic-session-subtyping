module Experiment where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

import Duality
open import Kinds
open import Kits
import Types
open import Variance
open import Types using (Ty; T-Base; N-Sub; N-End)
open import AlgorithmicNFSubtyping using (_<:ₜ_; <:ₜ-refl; <:ₜ-trans; <:ₜ-sub; <:ₜ-msg; <:ₚ′-proto; <:ₜ-end)
open import Subtyping using
  ( _<:_
  ; _<<:[_]_
  ; injᵥ
  ; <:-refl
  ; <:-trans
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
  ; <<:-trans
  ; conv⇒subty
  ; norm-pres-sub
  )
open import TypesProtocolConstructors using
  ( ConstructorSignature
  ; ProtocolConstructors
  ; SelectTy1
  ; SelectTy2
  ; SelectConstTy
  ; instantiate
  ; materialize
  ; singletonSubst
  ; UsageVariance
  ; unused
  ; used
  ; usageVariance
  ; allUsageVariance
  ; swapUsage
  ; joinUsage
  ; composeUsage
  )
open import ExprSyntax using (Expr; Value; Const; E-Val; E-LetUnit; E-Pair; E-App; E-TApp; V-Const; V-Var; V-Receive₁; V-Send₁; V-Send₂; V-Send₃; V-Select₁; V-Select₂; C-Receive; C-Send; C-Select; C-Close; C-Fork; C-Unit)
open import ExprSemantics using (Label; Act-App; Act-TApp; Act-LetPair; Act-LetUnit; Act-PairV; Act-Rec; Act-Fork; Act-New; Act-Receive₁; Act-Receive₂; Act-Rcv; Act-Send₁; Act-Send₂; Act-Send₃; Act-Send; Act-Sel; Act-Select₁; Act-Select₂; Act-Close; Act-AppL; Act-AppR; Act-TAppE; Act-PairL; Act-PairR; Act-MatchE; Act-LetPairE; Act-LetUnitE; _—[_]→_)
import ExprSemantics as ES
open import ExprNormalTyping
open import ExprSubstitution using (substTyValue)
open import ExprSubstitutionTyping using
  ( rec-unfold-preserves-value
  ; subst-check-preserves-synth
  ; subst2-preserves-synth
  ; substTy-preserves-value
  ; substTy-normalizeTy
  ; substTy-SelectConstTy
  ; substTy-SelectTy1
  )
import ExprSubstitutionTyping as EST
open import SubstitutionSubtyping using (subst-preserves-≡c; subst-preserves; subst-preserves-<<:)
open import AlgorithmicNFSound using (sound-algₜ; sound-<<:ₚ)
open import AlgorithmicNFComplete using (complete-algₜ)
import ExprContextReduction as ECR
open import ExprContextReduction using
  (_—ctx[_]→_; _⦂_⇒_; Compatible; Extract; ctx-step-preserves-disjoint
  ; Ctx-β; Ctx-New; Ctx-Fork; Ctx-Rcv; Ctx-Send; Ctx-Select; Ctx-Close
  ; ReplaceAt; replace-preserves-disjoint
  ; RemoveCtx; RM-∅; RM-drop; RM-allused; RM-lin; RM-un
  ; MergeCtx; MC-∅; MC-used-left; MC-used-right; MC-un
  ; mergeDisjointContext; mergeRemoveContext
  ; remove-linear; remove-allused-disjoint; remove-preserves-remove
  ; remove-preserves-disjoint; remove-removed-disjoint; restore-disjoint
  ; extract-remove
  ; AllUsed; AU-∅; AU-used; AU-un; allUsedCtx-AllUsed
  ; LinearDisjoint; LD-∅; LD-used-used; LD-used-live; LD-live-used; LD-un-un
  ; unitLinNf; dualSessNf
  ; Label-β; Label-Fork; Label-RecvVal; Label-SendVal; Label-SendLab; Label-Close
  ; recvChanNf; sendChanNf; selectInNf; selectOutNf; sessNf
  ; allUsedCtx
  ; Ex-β; Ex-Fork; Ex-New; Ex-RecvVal; Ex-RecvLab; Ex-SendVal; Ex-SendLab; Ex-Close
  ; Compat-β; Compat-New; Compat-Fork; Compat-RecvVal; Compat-SendVal; Compat-Select; Compat-Close
  )
open import ExprTypingProperties using (frame-remove; replay-synth-allUsed; replay-check-allUsed)
open import ExprTypingLeftover using (strip-value; leftover-synth)
open import ExprPreservationStep using
  ( closeTy-shape
  ; close-inversion
  ; fork-shape
  ; new-shape
  ; newInst-shape
  ; sess-normalizeTy
  ; sendTy-shape
  ; receive₂-shape
  ; send₃-shape
  ; send₁-rigid
  ; send₂-rigid
  ; send₁-ty
  ; send₂-ty
  ; send₂-shape
  ; receive₁-rigid
  ; receive₂-rigid
  ; receive₁-ty
  ; receive₂-ty
  ; recv-app-inversion
  ; check-output-unique
  ; merge-value
   ; replace-take
   ; replace-used-output
  ; take-from-membership
  ; take-unique
  ; take-implies-membership
  ; sendChan-subtype
  ; sess-subtype
  ; weaken-synth
  ; arrow-subtype-inversion
  ; substTy-wkCtx-id
  ; remove-frame
  ; merge-frame
  )
import ExprPreservationStep as EPS

open Kits.Syntax Types.Ty-Syntax hiding (Sort)
open Traversal Types.Ty-Traversal
open CTraversal record { fusion = Types.fusion }

open import ExprPreservationStep2

select-app-subtype′ :
    ∀ {n k}
      {Γ Γ′ : Ctx [] n}
      {v₁ v₂ : Variance} {i : Fin k}
      {P : Ty [] KP} {S : Ty [] SLin}
      {P′ : NfTy [] KP} {S′ : NfTy [] SLin}
      {A R T : NfTy [] TLin}
    → Γ ⊢ᵥ V-Select₂ v₁ i P S ⇒ T ⊣ Γ′
    → T ≡ linArrNf A R
    → normalTyOf (selectInNf v₂ i P′ S′) <:ₜ normalTyOf A
    → normalTyOf (selectOutNf v₂ i P′ S′) <:ₜ normalTyOf R
select-app-subtype′ {n} {k} {Γ} {Γ′} {v₁} {v₂} {i} {P} {S} {P′} {S′} {mkNfTy T₁ (N-Sub x _)} {mkNfTy T₂ (N-Sub x₃ _)} {T} TV-Select₂ eq (<:ₜ-sub (<:ₜ-msg (<:ₚ′-proto {#c₁ = #c₁} x₁ x₂) subA)) = {!x!}
