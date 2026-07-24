module ProcReductionPreservationFresh where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (suc-injective)
open import Data.Fin.Subset as Subset using (Subset)
open import Data.Fin.Subset.Properties using
  ( p─⊥≡p
  ; x∈p∧x≢y⇒x∈p-y
  )
open import Data.List as L using (List; []; _∷_; length; lookup; removeAt; map)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Binary.Permutation.Propositional as Perm using
  (_↭_; refl; prep; swap; trans; ↭-sym)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (Σ; _×_; _,_)
import Data.Vec.Base as Vec
open import Function using (const)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)

open import Kinds using (SLin)
open import Variance using (Variance)
import Duality
open import Types using (Ty; T-Base; T-Dual)
open import ExprSyntax using
  ( NfTy
  ; Expr
  ; Value
  ; C-Unit
  ; E-App
  ; E-Val
  ; V-Const
  )
open import ExprNormalTyping
import ExprContextProperties as ECP
import ExprActionResourcesFresh as EAR
import ExprReductionPreservationFresh as ERP
open import ExprContextProperties using
  ( FrameCtx
  ; FC-∅
  ; FC-allused
  ; FC-live
  ; FC-frame
  ; FC-un
  ; frame-sym
  ; RemoveCtx
  ; RM-∅
  ; RM-drop
  ; RM-allused
  ; RM-lin
  ; RM-un
  ; compose-merge-remove2
  ; allUsedCtx
  ; allUsedCtx-AllUsed
  )
open import ExprContextReduction using
  ( _⦂_⇒_
  ; Extract
  ; Label-Fork
  ; Ex-Fork
  ; Ctx-Fork
  ; Frm-Fork
  ; Label-New
  ; Ex-New
  ; Ctx-New
  ; Frm-New
  ; Ctx-Rcv
  ; Frm-Rcv
  ; Ctx-Send
  ; Frm-Send
  ; Ctx-Close
  ; Frm-Close
  ; Ctx-Match
  ; Frm-Match
  ; Ctx-Select
  ; Frm-Select
  ; Compat-SendVal
  ; Compat-RecvVal
  ; Label-RecvVal
  ; Label-RecvLab
  ; Label-SendVal
  ; Label-SendLab
  ; Label-Close
  ; Ex-RecvVal
  ; Ex-RecvLab
  ; Ex-SendVal
  ; Ex-SendLab
  ; Ex-Close
  ; recvChanNf
  ; sendChanNf
  ; selectInNf
  ; selectSetInNf
  ; selectOutNf
  )
open import ExprSubstitutionPreservationFresh using
  ( _≈ᵘ_
  ; ≈ᵘ-refl
  ; ≈ᵘ-∅
  ; ≈ᵘ-lin
  ; ≈ᵘ-un
  ; ≈ᵘ-used
  ; ≈ᵘ-sym
  ; ≈ᵘ-trans
  ; CheckResult
  ; retag-check-input
  ; allUsed-resp-≈ᵘ
  ; exchange-value-after-value
  )
open import ExprReductionPreservationFresh using
  ( beta-reduction-preserves-check
  ; reduction-preserves-check
  ; ReductionCheckResult
  ; check-resources
  ; check-disjoint-resources
  ; remove-to-rest-frame
  ; send-remove-membership-fresh
  ; linear-membership-type
  ; new-weaken-check-at
  )
open import SessionTypeDuality using
  ( normalize-dual
  ; dual-recvChanNf
  ; dual-sendChanNf
  ; recvChanNf-injective
  ; sendChanNf-injective
  ; dual-select-set-input
  ; selectSetInNf-injective
  ; dual-match-branch-output
  )
open import NormalTypesSubstitution using
  ( dualNFKind
  ; dualNFKind-involutive
  )
open import ExprSemantics using
  ( Label
  ; L-β
  ; L-Fork
  ; L-New
  ; L-RecvVal
  ; L-RecvLab
  ; L-SendVal
  ; L-SendLab
  ; L-Close
  ; _—[_]→_
  ; Act-Rcv
  ; Act-Send
  ; Act-Match
  ; Act-Sel
  ; Act-Close
  ; Act-AppL
  ; Act-AppR
  ; Act-TAppE
  ; Act-PairL
  ; Act-PairR
  ; Act-MatchE
  ; Act-LetPairE
  ; Act-LetUnitE
  ; weakenExprBy
  )
open import AlgorithmicNFSubtyping using (_<:ₜ_; <:ₜ-refl; <:ₜ-trans)
open import ExprTypingStrengthening using
  ( arrow-subtype-inversion
  ; check-subsumption
  )
open import ExprTypingStripFresh using (strip-value)
open import ExprTypingProperties using (frame-unique)
open import ExprTypingUniquenessFresh using (take-membership-fresh)
open import ExprPreservationStep2.ContextLemmas using
  ( remove-membership
  ; extract-membership
  )
open import ExprTypingInversion using
  ( recvChan-subtype-shape
  ; sendChan-subtype-shape
  )
import ProcSemanticsFresh as PSF
open PSF using
  ( Conf
  ; ConfLabel
  ; C-τ
  ; C-new
  ; _—conf[_]→_
  )
open PSF.Conf using (exps; live)
open import ProcTypingFresh

------------------------------------------------------------------------
-- Structural facts about declarative thread pools

data DualContinuations
    (Sx Sy : NfTy [] SLin) : Set where
  DC-forward :
    Sy ≡ dualNFKind Duality.D-S Sx
    → DualContinuations Sx Sy
  DC-backward :
    Sx ≡ dualNFKind Duality.D-S Sy
    → DualContinuations Sx Sy

dual-live-pair-forward :
  ∀ {n}
    {Γ : Ctx [] n}
    {x y : Fin n}
    {Sx Sy : NfTy [] SLin}
  → Γ ∋ˡ x ∶ Sx
  → Γ ∋ˡ y ∶ Sy
  → DualLivePair Γ x y
  → Sy ≡ dualNFKind Duality.D-S Sx
dual-live-pair-forward receiver sender (DLP-forward x∈ y∈) =
  Relation.Binary.PropositionalEquality.trans
    (linear-membership-type sender y∈)
    (cong
      (dualNFKind Duality.D-S)
      (sym (linear-membership-type receiver x∈)))
dual-live-pair-forward {Sx = Sx} {Sy = Sy}
    receiver sender (DLP-backward x∈ y∈) =
  Relation.Binary.PropositionalEquality.trans
    (sym (dualNFKind-involutive Sy))
    (sym
      (cong
        (dualNFKind Duality.D-S)
        (Relation.Binary.PropositionalEquality.trans
          (linear-membership-type receiver x∈)
          (cong
            (dualNFKind Duality.D-S)
            (sym (linear-membership-type sender y∈))))))
dual-action-shape :
  ∀ {n pkx pky}
    {Γ : Ctx [] n}
    {x y : Fin n}
    {Tx : NfTy [] (Kinds.KV pkx Kinds.Lin)}
    {Ty : NfTy [] (Kinds.KV pky Kinds.Lin)}
    {Sx Sy : NfTy [] SLin}
  → Γ ∋ˡ x ∶ recvChanNf Tx Sx
  → Γ ∋ˡ y ∶ sendChanNf Ty Sy
  → DualLivePair Γ x y
  → Σ (pkx ≡ pky) λ where
      refl → (Tx ≡ Ty) × DualContinuations Sx Sy
dual-action-shape {Tx = Tx} {Ty = Ty} {Sx = Sx} {Sy = Sy}
    receiver sender (DLP-forward x∈ y∈)
  with sendChanNf-injective
    (Relation.Binary.PropositionalEquality.trans
      (linear-membership-type sender y∈)
      (Relation.Binary.PropositionalEquality.trans
        (cong (dualNFKind Duality.D-S)
          (sym (linear-membership-type receiver x∈)))
        (dual-recvChanNf Tx Sx)))
... | refl , payload-eq , continuation-eq =
  refl , sym payload-eq , DC-forward continuation-eq
dual-action-shape {Tx = Tx} {Ty = Ty} {Sx = Sx} {Sy = Sy}
    receiver sender (DLP-backward x∈ y∈)
  with recvChanNf-injective
    (Relation.Binary.PropositionalEquality.trans
      (linear-membership-type receiver x∈)
      (Relation.Binary.PropositionalEquality.trans
        (cong (dualNFKind Duality.D-S)
          (sym (linear-membership-type sender y∈)))
        (dual-sendChanNf Ty Sy)))
... | refl , payload-eq , continuation-eq =
  refl , payload-eq , DC-backward continuation-eq

------------------------------------------------------------------------
-- Transport of global configuration invariants

live-replace-live :
  ∀ {n}
    {ss : Subset n}
    {Γ Γ′ : Ctx [] n}
    {x : Fin n}
    {S : NfTy [] SLin}
  → LiveCtx ss Γ
  → x Subset.∈ ss
  → ExprContextReduction.ReplaceAt Γ x (B-Lin S) Γ′
  → LiveCtx ss Γ′
live-replace-live
    (LC-live live) Vec.here ExprContextReduction.R-here =
  LC-live live
live-replace-live
    (LC-live live) (Vec.there member)
    (ExprContextReduction.R-there replaced) =
  LC-live (live-replace-live live member replaced)
live-replace-live
    (LC-dead live) () ExprContextReduction.R-here
live-replace-live
    (LC-dead live) (Vec.there member)
    (ExprContextReduction.R-there replaced) =
  LC-dead (live-replace-live live member replaced)

live-replace-dead :
  ∀ {n}
    {ss : Subset n}
    {Γ Γ′ : Ctx [] n}
    {x : Fin n}
    {S : NfTy [] SLin}
  → LiveCtx ss Γ
  → x Subset.∈ ss
  → ExprContextReduction.ReplaceAt Γ x (B-Used S) Γ′
  → LiveCtx (ss Subset.- x) Γ′
live-replace-dead
    (LC-live {ss = ss} {Γ = Γ} live)
    Vec.here ExprContextReduction.R-here =
  LC-dead
    (subst
      (λ ss′ → LiveCtx ss′ Γ)
      (sym (p─⊥≡p ss))
      live)
live-replace-dead
    (LC-live live) (Vec.there member)
    (ExprContextReduction.R-there replaced) =
  LC-live (live-replace-dead live member replaced)
live-replace-dead
    (LC-dead live) () ExprContextReduction.R-here
live-replace-dead
    (LC-dead live) (Vec.there member)
    (ExprContextReduction.R-there replaced) =
  LC-dead (live-replace-dead live member replaced)

fresh-pair-distinct :
  ∀ {n} {x y : Fin (2 + n)}
  → PSF.FinFreshPair {n} x y
  → x ≢ y
fresh-pair-distinct PSF.here-fwd ()
fresh-pair-distinct PSF.here-bwd ()
fresh-pair-distinct (PSF.there pair) equal =
  fresh-pair-distinct pair
    (suc-injective (suc-injective equal))

live-replace-pair-live :
  ∀ {n}
    {ss : Subset (2 + n)}
    {Γ Γx Γ′ : Ctx [] (2 + n)}
    {x y : Fin (2 + n)}
    {Sx Sy : NfTy [] SLin}
  → LiveCtx ss Γ
  → PSF.FinFreshPair {n} x y
  → x Subset.∈ ss
  → y Subset.∈ ss
  → ExprContextReduction.ReplaceAt Γ x (B-Lin Sx) Γx
  → ExprContextReduction.ReplaceAt Γx y (B-Lin Sy) Γ′
  → LiveCtx ss Γ′
live-replace-pair-live live pair x-live y-live replace-x replace-y =
  live-replace-live
    (live-replace-live live x-live replace-x)
    y-live
    replace-y

live-replace-pair-dead :
  ∀ {n}
    {ss : Subset (2 + n)}
    {Γ Γx Γ′ : Ctx [] (2 + n)}
    {x y : Fin (2 + n)}
    {Sx Sy : NfTy [] SLin}
  → LiveCtx ss Γ
  → (pair : PSF.FinFreshPair {n} x y)
  → x Subset.∈ ss
  → y Subset.∈ ss
  → ExprContextReduction.ReplaceAt Γ x (B-Used Sx) Γx
  → ExprContextReduction.ReplaceAt Γx y (B-Used Sy) Γ′
  → LiveCtx ((ss Subset.- x) Subset.- y) Γ′
live-replace-pair-dead live pair x-live y-live replace-x replace-y =
  live-replace-dead
    (live-replace-dead live x-live replace-x)
    (x∈p∧x≢y⇒x∈p-y
      y-live
      (λ y≡x → fresh-pair-distinct pair (sym y≡x)))
    replace-y

paired-replace-pair :
  ∀ {n}
    {Γ Γx Γ′ : Ctx [] (2 + n)}
    {x y : Fin (2 + n)}
    {bx by : Binding []}
    {Sx Sy : NfTy [] SLin}
  → PairedCtx Γ
  → PSF.FinFreshPair {n} x y
  → SessionBinding bx Sx
  → SessionBinding by Sy
  → ExprContextReduction.ReplaceAt Γ x bx Γx
  → ExprContextReduction.ReplaceAt Γx y by Γ′
  → DualContinuations Sx Sy
  → PairedCtx Γ′
paired-replace-pair
    (PC-pair first second paired)
    PSF.here-fwd sx sy
    ExprContextReduction.R-here
    (ExprContextReduction.R-there ExprContextReduction.R-here)
    (DC-forward refl) =
  PC-pair sx sy paired
paired-replace-pair {by = by}
    (PC-pair first second paired)
    PSF.here-fwd sx sy
    ExprContextReduction.R-here
    (ExprContextReduction.R-there ExprContextReduction.R-here)
    (DC-backward backward) =
  PC-pair
    sx
    (subst
      (SessionBinding by)
      (Relation.Binary.PropositionalEquality.trans
        (sym (dualNFKind-involutive _))
        (sym
          (cong
            (dualNFKind Duality.D-S)
            backward)))
      sy)
    paired
paired-replace-pair
    (PC-pair first second paired)
    PSF.here-bwd sx sy
    (ExprContextReduction.R-there ExprContextReduction.R-here)
    ExprContextReduction.R-here
    (DC-backward refl) =
  PC-pair sy sx paired
paired-replace-pair {bx = bx}
    (PC-pair first second paired)
    PSF.here-bwd sx sy
    (ExprContextReduction.R-there ExprContextReduction.R-here)
    ExprContextReduction.R-here
    (DC-forward forward) =
  PC-pair
    sy
    (subst
      (SessionBinding bx)
      (Relation.Binary.PropositionalEquality.trans
        (sym (dualNFKind-involutive _))
        (sym
          (cong
            (dualNFKind Duality.D-S)
            forward)))
      sx)
    paired
paired-replace-pair
    (PC-pair first second paired)
    (PSF.there pair) sx sy
    (ExprContextReduction.R-there
      (ExprContextReduction.R-there replace-x))
    (ExprContextReduction.R-there
      (ExprContextReduction.R-there replace-y))
    continuations =
  PC-pair first second
    (paired-replace-pair
      paired pair sx sy replace-x replace-y continuations)

paired-replace-pair-live :
  ∀ {n}
    {Γ Γx Γ′ : Ctx [] (2 + n)}
    {x y : Fin (2 + n)}
    {Sx Sy : NfTy [] SLin}
  → PairedCtx Γ
  → PSF.FinFreshPair {n} x y
  → ExprContextReduction.ReplaceAt Γ x (B-Lin Sx) Γx
  → ExprContextReduction.ReplaceAt Γx y (B-Lin Sy) Γ′
  → DualContinuations Sx Sy
  → PairedCtx Γ′
paired-replace-pair-live paired pair replace-x replace-y continuations =
  paired-replace-pair
    paired pair SB-live SB-live replace-x replace-y continuations

paired-replace-pair-dead :
  ∀ {n}
    {Γ Γx Γ′ : Ctx [] (2 + n)}
    {x y : Fin (2 + n)}
    {Sx Sy : NfTy [] SLin}
  → PairedCtx Γ
  → PSF.FinFreshPair {n} x y
  → ExprContextReduction.ReplaceAt Γ x (B-Used Sx) Γx
  → ExprContextReduction.ReplaceAt Γx y (B-Used Sy) Γ′
  → DualContinuations Sx Sy
  → PairedCtx Γ′
paired-replace-pair-dead paired pair replace-x replace-y continuations =
  paired-replace-pair
    paired pair SB-dead SB-dead replace-x replace-y continuations

split-to-frame :
  ∀ {Δ n} {Γ Γ₁ Γ₂ : Ctx Δ n}
  → Split Γ Γ₁ Γ₂
  → FrameCtx Γ₁ Γ₂ Γ
split-to-frame S-∅ = FC-∅
split-to-frame (S-Linˡ sp) = FC-frame (split-to-frame sp)
split-to-frame (S-Linʳ sp) = FC-live (split-to-frame sp)
split-to-frame (S-Un sp) = FC-un (split-to-frame sp)
split-to-frame (S-Used sp) = FC-allused (split-to-frame sp)

frame-to-split :
  ∀ {Δ n} {Γ Γ₁ Γ₂ : Ctx Δ n}
  → FrameCtx Γ₁ Γ₂ Γ
  → Split Γ Γ₁ Γ₂
frame-to-split FC-∅ = S-∅
frame-to-split (FC-allused f) = S-Used (frame-to-split f)
frame-to-split (FC-live f) = S-Linʳ (frame-to-split f)
frame-to-split (FC-frame f) = S-Linˡ (frame-to-split f)
frame-to-split (FC-un f) = S-Un (frame-to-split f)

frame-assoc :
  ∀ {Δ n}
    {A B AB C ABC : Ctx Δ n}
  → FrameCtx A B AB
  → FrameCtx AB C ABC
  → Σ (Ctx Δ n) λ BC →
      FrameCtx B C BC × FrameCtx A BC ABC
frame-assoc FC-∅ FC-∅ = ∅ , FC-∅ , FC-∅
frame-assoc (FC-allused first) (FC-allused second)
  with frame-assoc first second
... | BC , right , whole =
  _ , FC-allused right , FC-allused whole
frame-assoc (FC-allused first) (FC-live second)
  with frame-assoc first second
... | BC , right , whole =
  _ , FC-live right , FC-live whole
frame-assoc (FC-live first) (FC-frame second)
  with frame-assoc first second
... | BC , right , whole =
  _ , FC-frame right , FC-live whole
frame-assoc (FC-frame first) (FC-frame second)
  with frame-assoc first second
... | BC , right , whole =
  _ , FC-allused right , FC-frame whole
frame-assoc (FC-un first) (FC-un second)
  with frame-assoc first second
... | BC , right , whole =
  _ , FC-un right , FC-un whole

frame-unassoc :
  ∀ {Δ n}
    {B C BC A ABC : Ctx Δ n}
  → FrameCtx B C BC
  → FrameCtx A BC ABC
  → Σ (Ctx Δ n) λ AB →
      FrameCtx A B AB × FrameCtx AB C ABC
frame-unassoc right whole
  with frame-assoc (frame-sym right) (frame-sym whole)
... | BA , merged , outer =
  BA , frame-sym merged , frame-sym outer

frame-replace-live :
  ∀ {Δ n pk}
    {A P AP A′ P′ AP′ : Ctx Δ n}
    {x : Fin n}
    {S : NfTy Δ (Kinds.KV pk Kinds.Lin)}
  → FrameCtx A P AP
  → ExprContextReduction.ReplaceAt A x (B-Lin S) A′
  → ExprContextReduction.ReplaceAt P x (B-Used S) P′
  → FrameCtx A′ P′ AP′
  → ExprContextReduction.ReplaceAt AP x (B-Lin S) AP′
frame-replace-live
    (FC-frame {T = T} source) ExprContextReduction.R-here
    ExprContextReduction.R-here (FC-frame target) =
  subst
    (λ X →
      ExprContextReduction.ReplaceAt
        (B-Lin T ▻ _)
        fzero
        (B-Lin _)
        (B-Lin _ ▻ X))
    (frame-unique source target)
    ExprContextReduction.R-here
frame-replace-live
    (FC-allused {T = T} source) ExprContextReduction.R-here
    ExprContextReduction.R-here (FC-frame target) =
  subst
    (λ X →
      ExprContextReduction.ReplaceAt
        (B-Used T ▻ _)
        fzero
        (B-Lin _)
        (B-Lin _ ▻ X))
    (frame-unique source target)
    ExprContextReduction.R-here
frame-replace-live
    (FC-live {T = T} source) ExprContextReduction.R-here
    ExprContextReduction.R-here (FC-frame target) =
  subst
    (λ X →
      ExprContextReduction.ReplaceAt
        (B-Lin T ▻ _)
        fzero
        (B-Lin _)
        (B-Lin _ ▻ X))
    (frame-unique source target)
    ExprContextReduction.R-here
frame-replace-live
    (FC-un {T = T} source) ExprContextReduction.R-here
    ExprContextReduction.R-here (FC-frame target) =
  subst
    (λ X →
      ExprContextReduction.ReplaceAt
        (B-Un T ▻ _)
        fzero
        (B-Lin _)
        (B-Lin _ ▻ X))
    (frame-unique source target)
    ExprContextReduction.R-here
frame-replace-live
    (FC-allused source) (ExprContextReduction.R-there active)
    (ExprContextReduction.R-there payload) (FC-allused target) =
  ExprContextReduction.R-there
    (frame-replace-live source active payload target)
frame-replace-live
    (FC-live source) (ExprContextReduction.R-there active)
    (ExprContextReduction.R-there payload) (FC-live target) =
  ExprContextReduction.R-there
    (frame-replace-live source active payload target)
frame-replace-live
    (FC-frame source) (ExprContextReduction.R-there active)
    (ExprContextReduction.R-there payload) (FC-frame target) =
  ExprContextReduction.R-there
    (frame-replace-live source active payload target)
frame-replace-live
    (FC-un source) (ExprContextReduction.R-there active)
    (ExprContextReduction.R-there payload) (FC-un target) =
  ExprContextReduction.R-there
    (frame-replace-live source active payload target)

frame-replace-used :
  ∀ {Δ n pk}
    {A P AP A′ P′ AP′ : Ctx Δ n}
    {x : Fin n}
    {S : NfTy Δ (Kinds.KV pk Kinds.Lin)}
  → FrameCtx A P AP
  → ExprContextReduction.ReplaceAt A x (B-Used S) A′
  → ExprContextReduction.ReplaceAt P x (B-Used S) P′
  → FrameCtx A′ P′ AP′
  → ExprContextReduction.ReplaceAt AP x (B-Used S) AP′
frame-replace-used
    (FC-frame {T = T} source) ExprContextReduction.R-here
    ExprContextReduction.R-here (FC-allused target) =
  subst
    (λ X →
      ExprContextReduction.ReplaceAt
        (B-Lin T ▻ _)
        fzero
        (B-Used _)
        (B-Used _ ▻ X))
    (frame-unique source target)
    ExprContextReduction.R-here
frame-replace-used
    (FC-allused {T = T} source) ExprContextReduction.R-here
    ExprContextReduction.R-here (FC-allused target) =
  subst
    (λ X →
      ExprContextReduction.ReplaceAt
        (B-Used T ▻ _)
        fzero
        (B-Used _)
        (B-Used _ ▻ X))
    (frame-unique source target)
    ExprContextReduction.R-here
frame-replace-used
    (FC-live {T = T} source) ExprContextReduction.R-here
    ExprContextReduction.R-here (FC-allused target) =
  subst
    (λ X →
      ExprContextReduction.ReplaceAt
        (B-Lin T ▻ _)
        fzero
        (B-Used _)
        (B-Used _ ▻ X))
    (frame-unique source target)
    ExprContextReduction.R-here
frame-replace-used
    (FC-un {T = T} source) ExprContextReduction.R-here
    ExprContextReduction.R-here (FC-allused target) =
  subst
    (λ X →
      ExprContextReduction.ReplaceAt
        (B-Un T ▻ _)
        fzero
        (B-Used _)
        (B-Used _ ▻ X))
    (frame-unique source target)
    ExprContextReduction.R-here
frame-replace-used
    (FC-allused source) (ExprContextReduction.R-there active)
    (ExprContextReduction.R-there payload) (FC-allused target) =
  ExprContextReduction.R-there
    (frame-replace-used source active payload target)
frame-replace-used
    (FC-live source) (ExprContextReduction.R-there active)
    (ExprContextReduction.R-there payload) (FC-live target) =
  ExprContextReduction.R-there
    (frame-replace-used source active payload target)
frame-replace-used
    (FC-frame source) (ExprContextReduction.R-there active)
    (ExprContextReduction.R-there payload) (FC-frame target) =
  ExprContextReduction.R-there
    (frame-replace-used source active payload target)
frame-replace-used
    (FC-un source) (ExprContextReduction.R-there active)
    (ExprContextReduction.R-there payload) (FC-un target) =
  ExprContextReduction.R-there
    (frame-replace-used source active payload target)

ctx-allused-disjoint :
  ∀ {Δ n} (Γ : Ctx Δ n)
  → ECP.LinearDisjoint Γ (allUsedCtx Γ)
ctx-allused-disjoint ∅ = ECP.LD-∅
ctx-allused-disjoint (B-Lin _ ▻ Γ) =
  ECP.LD-live-used (ctx-allused-disjoint Γ)
ctx-allused-disjoint (B-Un _ ▻ Γ) =
  ECP.LD-un-un (ctx-allused-disjoint Γ)
ctx-allused-disjoint (B-Used _ ▻ Γ) =
  ECP.LD-used-used (ctx-allused-disjoint Γ)

remove-source-allused-disjoint :
  ∀ {Δ n}
    {Γ G R : Ctx Δ n}
  → RemoveCtx Γ G R
  → AllUsed G
  → ECP.LinearDisjoint Γ G
remove-source-allused-disjoint RM-∅ AU-∅ = ECP.LD-∅
remove-source-allused-disjoint (RM-drop removed) (AU-used used) =
  ECP.LD-live-used
    (remove-source-allused-disjoint removed used)
remove-source-allused-disjoint (RM-allused removed) (AU-used used) =
  ECP.LD-used-used
    (remove-source-allused-disjoint removed used)
remove-source-allused-disjoint (RM-un removed) (AU-un used) =
  ECP.LD-un-un
    (remove-source-allused-disjoint removed used)

send-label-output-disjoint :
  ∀ {Δ n pk}
    {Γ Γin Γused Γrest : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (Kinds.KV pk Kinds.Lin)}
  → RemoveCtx Γ Γin Γrest
  → Γin ⊢ˡ x ∶ T ⊣ Γused
  → AllUsed Γused
  → ECP.LinearDisjoint Γ Γused
send-label-output-disjoint
    (RM-lin removed) take-here (AU-used used) =
  ECP.LD-live-used
    (remove-source-allused-disjoint removed used)
send-label-output-disjoint
    (RM-drop removed) (take-there✖ take) (AU-used used) =
  ECP.LD-live-used
    (send-label-output-disjoint removed take used)
send-label-output-disjoint
    (RM-allused removed) (take-there✖ take) (AU-used used) =
  ECP.LD-used-used
    (send-label-output-disjoint removed take used)
send-label-output-disjoint
    (RM-un removed) (take-thereᵘ take) (AU-un used) =
  ECP.LD-un-un
    (send-label-output-disjoint removed take used)

-- Exchange two removals.  This is the pointwise resource fact used by fork:
-- the expression frame can be removed before the forked closure, or after it.

remove-exchange :
  ∀ {Δ n} {Γ₀ F A V B Γ₁ : Ctx Δ n}
  → RemoveCtx Γ₀ F A
  → RemoveCtx A V B
  → RemoveCtx Γ₁ F B
  → RemoveCtx Γ₀ V Γ₁
remove-exchange RM-∅ RM-∅ RM-∅ = RM-∅
remove-exchange (RM-drop rF) (RM-drop rV) (RM-drop rF′) =
  RM-drop (remove-exchange rF rV rF′)
remove-exchange (RM-drop rF) (RM-lin rV) (RM-allused rF′) =
  RM-lin (remove-exchange rF rV rF′)
remove-exchange (RM-lin rF) (RM-allused rV) (RM-lin rF′) =
  RM-drop (remove-exchange rF rV rF′)
remove-exchange (RM-allused rF) (RM-allused rV) (RM-allused rF′) =
  RM-allused (remove-exchange rF rV rF′)
remove-exchange (RM-un rF) (RM-un rV) (RM-un rF′) =
  RM-un (remove-exchange rF rV rF′)

remove-source-unique :
  ∀ {Δ n} {Γ₁ Γ₂ G R : Ctx Δ n}
  → RemoveCtx Γ₁ G R
  → RemoveCtx Γ₂ G R
  → Γ₁ ≡ Γ₂
remove-source-unique RM-∅ RM-∅ = refl
remove-source-unique (RM-drop r₁) (RM-drop r₂) =
  cong (_ ▻_) (remove-source-unique r₁ r₂)
remove-source-unique (RM-allused r₁) (RM-allused r₂) =
  cong (_ ▻_) (remove-source-unique r₁ r₂)
remove-source-unique (RM-lin r₁) (RM-lin r₂) =
  cong (_ ▻_) (remove-source-unique r₁ r₂)
remove-source-unique (RM-un r₁) (RM-un r₂) =
  cong (_ ▻_) (remove-source-unique r₁ r₂)

remove-target-unique :
  ∀ {Δ n} {Γ G R₁ R₂ : Ctx Δ n}
  → RemoveCtx Γ G R₁
  → RemoveCtx Γ G R₂
  → R₁ ≡ R₂
remove-target-unique RM-∅ RM-∅ = refl
remove-target-unique (RM-drop r₁) (RM-drop r₂) =
  cong (_ ▻_) (remove-target-unique r₁ r₂)
remove-target-unique (RM-allused r₁) (RM-allused r₂) =
  cong (_ ▻_) (remove-target-unique r₁ r₂)
remove-target-unique (RM-lin r₁) (RM-lin r₂) =
  cong (_ ▻_) (remove-target-unique r₁ r₂)
remove-target-unique (RM-un r₁) (RM-un r₂) =
  cong (_ ▻_) (remove-target-unique r₁ r₂)

frame-left-membership :
  ∀ {Δ n pk}
    {A B AB : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (Kinds.KV pk Kinds.Lin)}
  → FrameCtx A B AB
  → A ∋ˡ x ∶ T
  → AB ∋ˡ x ∶ T
frame-left-membership (FC-frame frame) hereˡ = hereˡ
frame-left-membership (FC-frame frame) (thereˡˡ member) =
  thereˡˡ (frame-left-membership frame member)
frame-left-membership (FC-live frame) (thereˡ✖ member) =
  thereˡˡ (frame-left-membership frame member)
frame-left-membership (FC-allused frame) (thereˡ✖ member) =
  thereˡ✖ (frame-left-membership frame member)
frame-left-membership (FC-un frame) (thereˡᵘ member) =
  thereˡᵘ (frame-left-membership frame member)

split-expand-left :
  ∀ {Δ n} {Γ AB C A B : Ctx Δ n}
  → Split Γ AB C
  → Split AB A B
  → Σ (Ctx Δ n) λ AC →
      Split Γ B AC × Split AC A C
split-expand-left S-∅ S-∅ = ∅ , S-∅ , S-∅
split-expand-left (S-Linˡ outer) (S-Linˡ inner)
  with split-expand-left outer inner
... | AC , first , second =
  _ , S-Linʳ first , S-Linˡ second
split-expand-left (S-Linˡ outer) (S-Linʳ inner)
  with split-expand-left outer inner
... | AC , first , second =
  _ , S-Linˡ first , S-Used second
split-expand-left (S-Linʳ outer) (S-Used inner)
  with split-expand-left outer inner
... | AC , first , second =
  _ , S-Linʳ first , S-Linʳ second
split-expand-left (S-Un outer) (S-Un inner)
  with split-expand-left outer inner
... | AC , first , second =
  _ , S-Un first , S-Un second
split-expand-left (S-Used outer) (S-Used inner)
  with split-expand-left outer inner
... | AC , first , second =
  _ , S-Used first , S-Used second

-- Move a resource fragment from the second thread to the first one.  The
-- global context is unchanged; only the ownership encoded by the two nested
-- split trees changes.  This is the resource-level core of message
-- synchronization.

split-transfer-left :
  ∀ {Δ n}
    {Γ A BC B R P B′ : Ctx Δ n}
  → Split Γ A BC
  → Split BC B R
  → RemoveCtx B P B′
  → Σ (Ctx Δ n) λ AP →
      Σ (Ctx Δ n) λ B′R →
        FrameCtx A P AP
        × Split Γ AP B′R
        × Split B′R B′ R
split-transfer-left S-∅ S-∅ RM-∅ =
  ∅ , ∅ , FC-∅ , S-∅ , S-∅
split-transfer-left
    (S-Linˡ outer) (S-Used inner) (RM-allused removed)
  with split-transfer-left outer inner removed
... | AP , B′R , merged , first , second =
  _ , _ ,
  FC-frame merged ,
  S-Linˡ first ,
  S-Used second
split-transfer-left
    (S-Linʳ outer) (S-Linˡ inner) (RM-lin removed)
  with split-transfer-left outer inner removed
... | AP , B′R , merged , first , second =
  _ , _ ,
  FC-live merged ,
  S-Linˡ first ,
  S-Used second
split-transfer-left
    (S-Linʳ outer) (S-Linˡ inner) (RM-drop removed)
  with split-transfer-left outer inner removed
... | AP , B′R , merged , first , second =
  _ , _ ,
  FC-allused merged ,
  S-Linʳ first ,
  S-Linˡ second
split-transfer-left
    (S-Linʳ outer) (S-Linʳ inner) (RM-allused removed)
  with split-transfer-left outer inner removed
... | AP , B′R , merged , first , second =
  _ , _ ,
  FC-allused merged ,
  S-Linʳ first ,
  S-Linʳ second
split-transfer-left
    (S-Un outer) (S-Un inner) (RM-un removed)
  with split-transfer-left outer inner removed
... | AP , B′R , merged , first , second =
  _ , _ ,
  FC-un merged ,
  S-Un first ,
  S-Un second
split-transfer-left
    (S-Used outer) (S-Used inner) (RM-allused removed)
  with split-transfer-left outer inner removed
... | AP , B′R , merged , first , second =
  _ , _ ,
  FC-allused merged ,
  S-Used first ,
  S-Used second

split-replace-left :
  ∀ {Δ n pkOld pkNew}
    {Γ A B A′ : Ctx Δ n}
    {x : Fin n}
    {Old : NfTy Δ (Kinds.KV pkOld Kinds.Lin)}
    {New : NfTy Δ (Kinds.KV pkNew Kinds.Lin)}
  → Split Γ A B
  → A ∋ˡ x ∶ Old
  → ExprContextReduction.ReplaceAt A x (B-Lin New) A′
  → Σ (Ctx Δ n) λ Γ′ →
      Σ (Ctx Δ n) λ B′ →
        Split Γ′ A′ B′
        × (B ≈ᵘ B′)
        × ExprContextReduction.ReplaceAt Γ x (B-Lin New) Γ′
        × ExprContextReduction.ReplaceAt B x (B-Used New) B′
split-replace-left
    (S-Linˡ split) hereˡ ExprContextReduction.R-here =
  _ , _ ,
  S-Linˡ split ,
  ≈ᵘ-used ≈ᵘ-refl ,
  ExprContextReduction.R-here ,
  ExprContextReduction.R-here
split-replace-left
    (S-Linˡ split) (thereˡˡ member)
    (ExprContextReduction.R-there replaced)
  with split-replace-left split member replaced
... | Γ′ , B′ , split′ , rest-eq , global-rep , other-rep =
  _ , _ ,
  S-Linˡ split′ ,
  ≈ᵘ-used rest-eq ,
  ExprContextReduction.R-there global-rep ,
  ExprContextReduction.R-there other-rep

split-replace-left
    (S-Linʳ split) (thereˡ✖ member)
    (ExprContextReduction.R-there replaced)
  with split-replace-left split member replaced
... | Γ′ , B′ , split′ , rest-eq , global-rep , other-rep =
  _ , _ ,
  S-Linʳ split′ ,
  ≈ᵘ-lin rest-eq ,
  ExprContextReduction.R-there global-rep ,
  ExprContextReduction.R-there other-rep
split-replace-left
    (S-Un split) (thereˡᵘ member)
    (ExprContextReduction.R-there replaced)
  with split-replace-left split member replaced
... | Γ′ , B′ , split′ , rest-eq , global-rep , other-rep =
  _ , _ ,
  S-Un split′ ,
  ≈ᵘ-un rest-eq ,
  ExprContextReduction.R-there global-rep ,
  ExprContextReduction.R-there other-rep
split-replace-left
    (S-Used split) (thereˡ✖ member)
    (ExprContextReduction.R-there replaced)
  with split-replace-left split member replaced
... | Γ′ , B′ , split′ , rest-eq , global-rep , other-rep =
  _ , _ ,
  S-Used split′ ,
  ≈ᵘ-used rest-eq ,
  ExprContextReduction.R-there global-rep ,
  ExprContextReduction.R-there other-rep

split-sym :
  ∀ {Δ n} {Γ A B : Ctx Δ n}
  → Split Γ A B
  → Split Γ B A
split-sym split =
  frame-to-split (frame-sym (split-to-frame split))

split-left-membership :
  ∀ {Δ n pk}
    {Γ A B : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (Kinds.KV pk Kinds.Lin)}
  → Split Γ A B
  → A ∋ˡ x ∶ T
  → Γ ∋ˡ x ∶ T
split-left-membership (S-Linˡ split) hereˡ = hereˡ
split-left-membership (S-Linˡ split) (thereˡˡ member) =
  thereˡˡ (split-left-membership split member)
split-left-membership (S-Linʳ split) (thereˡ✖ member) =
  thereˡˡ (split-left-membership split member)
split-left-membership (S-Un split) (thereˡᵘ member) =
  thereˡᵘ (split-left-membership split member)
split-left-membership (S-Used split) (thereˡ✖ member) =
  thereˡ✖ (split-left-membership split member)

split-right-membership :
  ∀ {Δ n pk}
    {Γ A B : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (Kinds.KV pk Kinds.Lin)}
  → Split Γ A B
  → B ∋ˡ x ∶ T
  → Γ ∋ˡ x ∶ T
split-right-membership split =
  split-left-membership (split-sym split)

nested-split-disjoint :
  ∀ {Δ n}
    {Γ A BC B R : Ctx Δ n}
  → Split Γ A BC
  → Split BC B R
  → ECP.LinearDisjoint A B
nested-split-disjoint S-∅ S-∅ = ECP.LD-∅
nested-split-disjoint (S-Linˡ outer) (S-Used inner) =
  ECP.LD-live-used (nested-split-disjoint outer inner)
nested-split-disjoint (S-Linʳ outer) (S-Linˡ inner) =
  ECP.LD-used-live (nested-split-disjoint outer inner)
nested-split-disjoint (S-Linʳ outer) (S-Linʳ inner) =
  ECP.LD-used-used (nested-split-disjoint outer inner)
nested-split-disjoint (S-Un outer) (S-Un inner) =
  ECP.LD-un-un (nested-split-disjoint outer inner)
nested-split-disjoint (S-Used outer) (S-Used inner) =
  ECP.LD-used-used (nested-split-disjoint outer inner)

payload-transfer-disjoint :
  ∀ {Δ n}
    {Γ A BC B R P Bminus : Ctx Δ n}
  → Split Γ A BC
  → Split BC B R
  → RemoveCtx B P Bminus
  → ECP.LinearDisjoint A P
payload-transfer-disjoint first second removed =
  ECP.sym-disjoint
    (ECP.remove-removed-disjoint
      removed
      (ECP.sym-disjoint (nested-split-disjoint first second)))

split-replace-right :
  ∀ {Δ n pkOld pkNew}
    {Γ A B B′ : Ctx Δ n}
    {x : Fin n}
    {Old : NfTy Δ (Kinds.KV pkOld Kinds.Lin)}
    {New : NfTy Δ (Kinds.KV pkNew Kinds.Lin)}
  → Split Γ A B
  → B ∋ˡ x ∶ Old
  → ExprContextReduction.ReplaceAt B x (B-Lin New) B′
  → Σ (Ctx Δ n) λ Γ′ →
      Σ (Ctx Δ n) λ A′ →
        Split Γ′ A′ B′
        × (A ≈ᵘ A′)
        × ExprContextReduction.ReplaceAt Γ x (B-Lin New) Γ′
        × ExprContextReduction.ReplaceAt A x (B-Used New) A′
split-replace-right split member replaced
  with split-replace-left (split-sym split) member replaced
... | Γ′ , A′ , split′ , left-eq , global-rep , other-rep =
  Γ′ , A′ ,
  split-sym split′ , left-eq , global-rep , other-rep

split-replace-left-used :
  ∀ {Δ n pkOld pkNew}
    {Γ A B A′ : Ctx Δ n}
    {x : Fin n}
    {Old : NfTy Δ (Kinds.KV pkOld Kinds.Lin)}
    {New : NfTy Δ (Kinds.KV pkNew Kinds.Lin)}
  → Split Γ A B
  → A ∋ˡ x ∶ Old
  → ExprContextReduction.ReplaceAt A x (B-Used New) A′
  → Σ (Ctx Δ n) λ Γ′ →
      Σ (Ctx Δ n) λ B′ →
        Split Γ′ A′ B′
        × (B ≈ᵘ B′)
        × ExprContextReduction.ReplaceAt Γ x (B-Used New) Γ′
        × ExprContextReduction.ReplaceAt B x (B-Used New) B′
split-replace-left-used
    (S-Linˡ split) hereˡ ExprContextReduction.R-here =
  _ , _ ,
  S-Used split ,
  ≈ᵘ-used ≈ᵘ-refl ,
  ExprContextReduction.R-here ,
  ExprContextReduction.R-here
split-replace-left-used
    (S-Linˡ split) (thereˡˡ member)
    (ExprContextReduction.R-there replaced)
  with split-replace-left-used split member replaced
... | Γ′ , B′ , split′ , rest-eq , global-rep , other-rep =
  _ , _ ,
  S-Linˡ split′ ,
  ≈ᵘ-used rest-eq ,
  ExprContextReduction.R-there global-rep ,
  ExprContextReduction.R-there other-rep
split-replace-left-used
    (S-Linʳ split) (thereˡ✖ member)
    (ExprContextReduction.R-there replaced)
  with split-replace-left-used split member replaced
... | Γ′ , B′ , split′ , rest-eq , global-rep , other-rep =
  _ , _ ,
  S-Linʳ split′ ,
  ≈ᵘ-lin rest-eq ,
  ExprContextReduction.R-there global-rep ,
  ExprContextReduction.R-there other-rep
split-replace-left-used
    (S-Un split) (thereˡᵘ member)
    (ExprContextReduction.R-there replaced)
  with split-replace-left-used split member replaced
... | Γ′ , B′ , split′ , rest-eq , global-rep , other-rep =
  _ , _ ,
  S-Un split′ ,
  ≈ᵘ-un rest-eq ,
  ExprContextReduction.R-there global-rep ,
  ExprContextReduction.R-there other-rep
split-replace-left-used
    (S-Used split) (thereˡ✖ member)
    (ExprContextReduction.R-there replaced)
  with split-replace-left-used split member replaced
... | Γ′ , B′ , split′ , rest-eq , global-rep , other-rep =
  _ , _ ,
  S-Used split′ ,
  ≈ᵘ-used rest-eq ,
  ExprContextReduction.R-there global-rep ,
  ExprContextReduction.R-there other-rep

split-replace-right-used :
  ∀ {Δ n pkOld pkNew}
    {Γ A B B′ : Ctx Δ n}
    {x : Fin n}
    {Old : NfTy Δ (Kinds.KV pkOld Kinds.Lin)}
    {New : NfTy Δ (Kinds.KV pkNew Kinds.Lin)}
  → Split Γ A B
  → B ∋ˡ x ∶ Old
  → ExprContextReduction.ReplaceAt B x (B-Used New) B′
  → Σ (Ctx Δ n) λ Γ′ →
      Σ (Ctx Δ n) λ A′ →
        Split Γ′ A′ B′
        × (A ≈ᵘ A′)
        × ExprContextReduction.ReplaceAt Γ x (B-Used New) Γ′
        × ExprContextReduction.ReplaceAt A x (B-Used New) A′
split-replace-right-used split member replaced
  with split-replace-left-used (split-sym split) member replaced
... | Γ′ , A′ , split′ , left-eq , global-rep , other-rep =
  Γ′ , A′ ,
  split-sym split′ , left-eq , global-rep , other-rep

live-membership-resp-≈ᵘ :
  ∀ {Δ n pk}
    {Γ Γ′ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (Kinds.KV pk Kinds.Lin)}
  → Γ ≈ᵘ Γ′
  → Γ ∋ˡ x ∶ T
  → Γ′ ∋ˡ x ∶ T
live-membership-resp-≈ᵘ (≈ᵘ-lin eq) hereˡ = hereˡ
live-membership-resp-≈ᵘ (≈ᵘ-lin eq) (thereˡˡ member) =
  thereˡˡ (live-membership-resp-≈ᵘ eq member)
live-membership-resp-≈ᵘ (≈ᵘ-un eq) (thereˡᵘ member) =
  thereˡᵘ (live-membership-resp-≈ᵘ eq member)
live-membership-resp-≈ᵘ (≈ᵘ-used eq) (thereˡ✖ member) =
  thereˡ✖ (live-membership-resp-≈ᵘ eq member)

replace-resp-≈ᵘ :
  ∀ {Δ n pkOld pk}
    {Γ Γ′ H : Ctx Δ n}
    {x : Fin n}
    {Old : NfTy Δ (Kinds.KV pkOld Kinds.Lin)}
    {New : NfTy Δ (Kinds.KV pk Kinds.Lin)}
  → Γ ≈ᵘ Γ′
  → Γ ∋ˡ x ∶ Old
  → ExprContextReduction.ReplaceAt Γ x (B-Lin New) H
  → Σ (Ctx Δ n) λ H′ →
      ExprContextReduction.ReplaceAt Γ′ x (B-Lin New) H′
      × (H ≈ᵘ H′)
replace-resp-≈ᵘ (≈ᵘ-lin eq) hereˡ ExprContextReduction.R-here =
  _ , ExprContextReduction.R-here , ≈ᵘ-lin eq
replace-resp-≈ᵘ (≈ᵘ-lin eq)
    (thereˡˡ member)
    (ExprContextReduction.R-there replaced)
  with replace-resp-≈ᵘ eq member replaced
... | H′ , replaced′ , out-eq =
  _ , ExprContextReduction.R-there replaced′ , ≈ᵘ-lin out-eq
replace-resp-≈ᵘ (≈ᵘ-un eq)
    (thereˡᵘ member)
    (ExprContextReduction.R-there replaced)
  with replace-resp-≈ᵘ eq member replaced
... | H′ , replaced′ , out-eq =
  _ , ExprContextReduction.R-there replaced′ , ≈ᵘ-un out-eq
replace-resp-≈ᵘ (≈ᵘ-used eq)
    (thereˡ✖ member)
    (ExprContextReduction.R-there replaced)
  with replace-resp-≈ᵘ eq member replaced
... | H′ , replaced′ , out-eq =
  _ , ExprContextReduction.R-there replaced′ , ≈ᵘ-used out-eq

replace-used-resp-≈ᵘ :
  ∀ {Δ n pkOld pk}
    {Γ Γ′ H : Ctx Δ n}
    {x : Fin n}
    {Old : NfTy Δ (Kinds.KV pkOld Kinds.Lin)}
    {New : NfTy Δ (Kinds.KV pk Kinds.Lin)}
  → Γ ≈ᵘ Γ′
  → Γ ∋ˡ x ∶ Old
  → ExprContextReduction.ReplaceAt Γ x (B-Used New) H
  → Σ (Ctx Δ n) λ H′ →
      ExprContextReduction.ReplaceAt Γ′ x (B-Used New) H′
      × (H ≈ᵘ H′)
replace-used-resp-≈ᵘ
    (≈ᵘ-lin eq) hereˡ ExprContextReduction.R-here =
  _ , ExprContextReduction.R-here , ≈ᵘ-used eq
replace-used-resp-≈ᵘ
    (≈ᵘ-lin eq)
    (thereˡˡ member)
    (ExprContextReduction.R-there replaced)
  with replace-used-resp-≈ᵘ eq member replaced
... | H′ , replaced′ , out-eq =
  _ , ExprContextReduction.R-there replaced′ , ≈ᵘ-lin out-eq
replace-used-resp-≈ᵘ
    (≈ᵘ-un eq)
    (thereˡᵘ member)
    (ExprContextReduction.R-there replaced)
  with replace-used-resp-≈ᵘ eq member replaced
... | H′ , replaced′ , out-eq =
  _ , ExprContextReduction.R-there replaced′ , ≈ᵘ-un out-eq
replace-used-resp-≈ᵘ
    (≈ᵘ-used eq)
    (thereˡ✖ member)
    (ExprContextReduction.R-there replaced)
  with replace-used-resp-≈ᵘ eq member replaced
... | H′ , replaced′ , out-eq =
  _ , ExprContextReduction.R-there replaced′ , ≈ᵘ-used out-eq

split-resp-≈ᵘ :
  ∀ {Δ n} {Γ Γ′ A B : Ctx Δ n}
  → Γ ≈ᵘ Γ′
  → Split Γ A B
  → Σ (Ctx Δ n) λ A′ →
      Σ (Ctx Δ n) λ B′ →
        Split Γ′ A′ B′ × (A ≈ᵘ A′) × (B ≈ᵘ B′)
split-resp-≈ᵘ ≈ᵘ-∅ S-∅ =
  ∅ , ∅ , S-∅ , ≈ᵘ-∅ , ≈ᵘ-∅
split-resp-≈ᵘ (≈ᵘ-lin eq) (S-Linˡ split)
  with split-resp-≈ᵘ eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Linˡ split′ , ≈ᵘ-lin eqA , ≈ᵘ-used eqB
split-resp-≈ᵘ (≈ᵘ-lin eq) (S-Linʳ split)
  with split-resp-≈ᵘ eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Linʳ split′ , ≈ᵘ-used eqA , ≈ᵘ-lin eqB
split-resp-≈ᵘ (≈ᵘ-un eq) (S-Un split)
  with split-resp-≈ᵘ eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Un split′ , ≈ᵘ-un eqA , ≈ᵘ-un eqB
split-resp-≈ᵘ (≈ᵘ-used eq) (S-Used split)
  with split-resp-≈ᵘ eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Used split′ , ≈ᵘ-used eqA , ≈ᵘ-used eqB

target-split-reconstruction :
  ∀ {Δ n pkX pkX′ pkY pkY′}
    {Γ A BC B R P Bminus AP ATarget BTarget : Ctx Δ n}
    {x y : Fin n}
    {OldX : NfTy Δ (Kinds.KV pkX Kinds.Lin)}
    {NewX : NfTy Δ (Kinds.KV pkX′ Kinds.Lin)}
    {OldY : NfTy Δ (Kinds.KV pkY Kinds.Lin)}
    {NewY : NfTy Δ (Kinds.KV pkY′ Kinds.Lin)}
  → Split Γ A BC
  → Split BC B R
  → RemoveCtx B P Bminus
  → FrameCtx A P AP
  → AP ∋ˡ x ∶ OldX
  → ExprContextReduction.ReplaceAt AP x (B-Lin NewX) ATarget
  → Bminus ∋ˡ y ∶ OldY
  → ExprContextReduction.ReplaceAt Bminus y (B-Lin NewY) BTarget
  → Σ (Ctx Δ n) λ Γ′ →
      Σ (Ctx Δ n) λ Γx →
        Σ (Ctx Δ n) λ BC′ →
          Σ (Ctx Δ n) λ A′ →
            Σ (Ctx Δ n) λ B′ →
              Σ (Ctx Δ n) λ R′ →
                Split Γ′ A′ BC′
                × Split BC′ B′ R′
                × (ATarget ≈ᵘ A′)
                × (BTarget ≈ᵘ B′)
                × (R ≈ᵘ R′)
                × ExprContextReduction.ReplaceAt
                    Γ x (B-Lin NewX) Γx
                × ExprContextReduction.ReplaceAt
                    Γx y (B-Lin NewY) Γ′
target-split-reconstruction
    first second removed transferred
    x-member x-replace y-member y-replace
  with split-transfer-left first second removed
... | AP′ , BminusR , transferred′ , first′ , second′
  rewrite frame-unique transferred transferred′
  with split-replace-left first′ x-member x-replace
... | Γx , BminusRx , first-x , rest-x-eq ,
      global-x-replace , rest-x-replace
  with split-resp-≈ᵘ rest-x-eq second′
... | BminusX , RX , second-x , sender-x-eq , rest-eq
  with replace-resp-≈ᵘ sender-x-eq y-member y-replace
... | BTargetX , y-replace-x , sender-target-eq
  with split-replace-left
         second-x
         (live-membership-resp-≈ᵘ sender-x-eq y-member)
         y-replace-x
... | BC′ , R′ , second-y , rest-y-eq ,
      remainder-y-replace , rest-y-replace
  with split-replace-right
         first-x
         (split-left-membership second-x
           (live-membership-resp-≈ᵘ sender-x-eq y-member))
         remainder-y-replace
... | Γ′ , A′ , first-y , receiver-target-eq ,
      global-y-replace , receiver-y-replace =
  Γ′ , Γx , BC′ , A′ , BTargetX , R′ ,
  first-y , second-y ,
  receiver-target-eq ,
  sender-target-eq ,
  ≈ᵘ-trans rest-eq rest-y-eq ,
  global-x-replace ,
  global-y-replace

target-split-reconstruction-direct :
  ∀ {Δ n pkX pkX′ pkY pkY′}
    {Γ A BC B R ATarget BTarget : Ctx Δ n}
    {x y : Fin n}
    {OldX : NfTy Δ (Kinds.KV pkX Kinds.Lin)}
    {NewX : NfTy Δ (Kinds.KV pkX′ Kinds.Lin)}
    {OldY : NfTy Δ (Kinds.KV pkY Kinds.Lin)}
    {NewY : NfTy Δ (Kinds.KV pkY′ Kinds.Lin)}
  → Split Γ A BC
  → Split BC B R
  → A ∋ˡ x ∶ OldX
  → ExprContextReduction.ReplaceAt A x (B-Lin NewX) ATarget
  → B ∋ˡ y ∶ OldY
  → ExprContextReduction.ReplaceAt B y (B-Lin NewY) BTarget
  → Σ (Ctx Δ n) λ Γ′ →
      Σ (Ctx Δ n) λ Γx →
        Σ (Ctx Δ n) λ BC′ →
          Σ (Ctx Δ n) λ A′ →
            Σ (Ctx Δ n) λ B′ →
              Σ (Ctx Δ n) λ R′ →
                Split Γ′ A′ BC′
                × Split BC′ B′ R′
                × (ATarget ≈ᵘ A′)
                × (BTarget ≈ᵘ B′)
                × (R ≈ᵘ R′)
                × ExprContextReduction.ReplaceAt
                    Γ x (B-Lin NewX) Γx
                × ExprContextReduction.ReplaceAt
                    Γx y (B-Lin NewY) Γ′
target-split-reconstruction-direct
    first second x-member x-replace y-member y-replace
  with split-replace-left first x-member x-replace
... | Γx , BCx , first-x , rest-x-eq ,
      global-x-replace , rest-x-replace
  with split-resp-≈ᵘ rest-x-eq second
... | Bx , Rx , second-x , sender-x-eq , rest-eq
  with replace-resp-≈ᵘ sender-x-eq y-member y-replace
... | BTargetX , y-replace-x , sender-target-eq
  with split-replace-left
         second-x
         (live-membership-resp-≈ᵘ sender-x-eq y-member)
         y-replace-x
... | BC′ , R′ , second-y , rest-y-eq ,
      remainder-y-replace , rest-y-replace
  with split-replace-right
         first-x
         (split-left-membership second-x
           (live-membership-resp-≈ᵘ sender-x-eq y-member))
         remainder-y-replace
... | Γ′ , A′ , first-y , receiver-target-eq ,
      global-y-replace , receiver-y-replace =
  Γ′ , Γx , BC′ , A′ , BTargetX , R′ ,
  first-y , second-y ,
  receiver-target-eq ,
  sender-target-eq ,
  ≈ᵘ-trans rest-eq rest-y-eq ,
  global-x-replace ,
  global-y-replace

target-split-reconstruction-used :
  ∀ {Δ n pkX pkX′ pkY pkY′}
    {Γ A BC B R ATarget BTarget : Ctx Δ n}
    {x y : Fin n}
    {OldX : NfTy Δ (Kinds.KV pkX Kinds.Lin)}
    {NewX : NfTy Δ (Kinds.KV pkX′ Kinds.Lin)}
    {OldY : NfTy Δ (Kinds.KV pkY Kinds.Lin)}
    {NewY : NfTy Δ (Kinds.KV pkY′ Kinds.Lin)}
  → Split Γ A BC
  → Split BC B R
  → A ∋ˡ x ∶ OldX
  → ExprContextReduction.ReplaceAt A x (B-Used NewX) ATarget
  → B ∋ˡ y ∶ OldY
  → ExprContextReduction.ReplaceAt B y (B-Used NewY) BTarget
  → Σ (Ctx Δ n) λ Γ′ →
      Σ (Ctx Δ n) λ Γx →
        Σ (Ctx Δ n) λ BC′ →
          Σ (Ctx Δ n) λ A′ →
            Σ (Ctx Δ n) λ B′ →
              Σ (Ctx Δ n) λ R′ →
                Split Γ′ A′ BC′
                × Split BC′ B′ R′
                × (ATarget ≈ᵘ A′)
                × (BTarget ≈ᵘ B′)
                × (R ≈ᵘ R′)
                × ExprContextReduction.ReplaceAt
                    Γ x (B-Used NewX) Γx
                × ExprContextReduction.ReplaceAt
                    Γx y (B-Used NewY) Γ′
target-split-reconstruction-used
    first second x-member x-replace y-member y-replace
  with split-replace-left-used first x-member x-replace
... | Γx , BCx , first-x , rest-x-eq ,
      global-x-replace , rest-x-replace
  with split-resp-≈ᵘ rest-x-eq second
... | Bx , Rx , second-x , sender-x-eq , rest-eq
  with replace-used-resp-≈ᵘ sender-x-eq y-member y-replace
... | BTargetX , y-replace-x , sender-target-eq
  with split-replace-left-used
         second-x
         (live-membership-resp-≈ᵘ sender-x-eq y-member)
         y-replace-x
... | BC′ , R′ , second-y , rest-y-eq ,
      remainder-y-replace , rest-y-replace
  with split-replace-right-used
         first-x
         (split-left-membership second-x
           (live-membership-resp-≈ᵘ sender-x-eq y-member))
         remainder-y-replace
... | Γ′ , A′ , first-y , receiver-target-eq ,
      global-y-replace , receiver-y-replace =
  Γ′ , Γx , BC′ , A′ , BTargetX , R′ ,
  first-y , second-y ,
  receiver-target-eq ,
  sender-target-eq ,
  ≈ᵘ-trans rest-eq rest-y-eq ,
  global-x-replace ,
  global-y-replace

send-result-replacement :
  ∀ {n pk m}
    {B Bout : Ctx [] n}
    {e′ : Expr [] n}
    {Expected : NfTy [] (Kinds.KV pk m)}
    {y : Fin n}
    {v : Value [] n}
    (resources : EAR.SendValueResources B y v)
    (result :
      ReductionCheckResult
        (ERP.SendInterface.Γin (ERP.send-interface resources))
        (ERP.SendInterface.Γv (ERP.send-interface resources))
        (ERP.SendInterface.label (ERP.send-interface resources))
        B Bout e′ Expected)
    (Bminus : Ctx [] n)
  → RemoveCtx
      B
      (ERP.SendInterface.Γv (ERP.send-interface resources))
      Bminus
  → Σ Kinds.PreKind λ payloadKind →
      Σ (NfTy [] (Kinds.KV payloadKind Kinds.Lin)) λ Payload →
      Σ (NfTy [] SLin) λ S →
        (Bminus ∋ˡ y ∶ sendChanNf Payload S)
        × ExprContextReduction.ReplaceAt
            Bminus y (B-Lin S)
            (ReductionCheckResult.Γ₁ result)
send-result-replacement
    resources@(EAR.send-value-resources outer-remove take payload sub used)
    record
      { src-remove = source-remove
      ; frame-update = Frm-Send frame-replace
      ; dst-remove = target-remove
      ; ctx-step =
          Ctx-Send active-remove payload′ sub′ used′
            endpoint active-replace
      ; compat = Compat-SendVal
      ; effect-aligned = refl
      }
    Bminus requested-remove
  with compose-merge-remove2
         (remove-to-rest-frame source-remove)
         active-remove
... | Bminus₁ , source-frame , whole-remove
  with send-remove-membership-fresh outer-remove take
... | Bminus₂ , payload-remove , endpoint-whole
  rewrite remove-target-unique whole-remove payload-remove
        | remove-target-unique requested-remove payload-remove =
  _ , _ , _ ,
  endpoint-whole ,
  frame-replace-live
    source-frame
    active-replace
    frame-replace
    (remove-to-rest-frame target-remove)

recv-result-replacement :
  ∀ {n pk m pkPayload}
    {A Aout P AP Γin : Ctx [] n}
    {e′ : Expr [] n}
    {Expected : NfTy [] (Kinds.KV pk m)}
    {x : Fin n}
    {v : Value [] n}
    {Payload U : NfTy [] (Kinds.KV pkPayload Kinds.Lin)}
    {Slabel : NfTy [] SLin}
    {Γin′ Pout : Ctx [] n}
    {take : Γin ⊢ˡ x ∶ recvChanNf Payload Slabel ⊣ Γin′}
    {input-used : AllUsed Γin′}
    {payload : P ⊢ᵥ v ⇒ U ⊣ Pout}
    {payload-sub :
      U <:ₜ Payload}
    {payload-used : AllUsed Pout}
    {input-payload-disjoint : ECP.LinearDisjoint Γin P}
    (result :
      ReductionCheckResult
        Γin P
        (Label-RecvVal
          take input-used payload payload-sub payload-used
          input-payload-disjoint)
        A Aout e′ Expected)
  → FrameCtx A P AP
  → Σ (NfTy [] SLin) λ S →
      (AP ∋ˡ x ∶ recvChanNf Payload S)
      × ExprContextReduction.ReplaceAt
          AP x (B-Lin S)
          (ReductionCheckResult.Γ₁ result)
recv-result-replacement
    record
      { src-remove = source-remove
      ; frame-update = Frm-Rcv frame-replace
      ; dst-remove = target-remove
      ; ctx-step =
          Ctx-Rcv payload′ sub′ used′ disjoint
            endpoint active-replace payload-replace active-merge
      ; compat = Compat-RecvVal
      ; effect-aligned = refl
      }
    transferred
  with frame-assoc (remove-to-rest-frame source-remove) transferred
... | frame-payload , merged-frame-payload , active-whole
  with frame-unassoc (frame-sym merged-frame-payload) active-whole
... | active-payload , active-merge-source , payload-frame-source =
  _ ,
  frame-left-membership transferred
    (frame-left-membership
      (remove-to-rest-frame source-remove)
      endpoint) ,
  frame-replace-live
    payload-frame-source
    (frame-replace-live
      active-merge-source
      active-replace
      payload-replace
      active-merge)
    frame-replace
    (remove-to-rest-frame target-remove)

data RecvBranchAdvance
    {n : ℕ}
    (A : Ctx [] n)
    (x : Fin n) :
    ∀ {k}
    → (i : Fin k)
    → (Target : Ctx [] n)
    → (Old New : NfTy [] SLin)
    → Set where

  recv-branch-advance :
    ∀ {q}
      {Target : Ctx [] n}
      {ssin ssout : Subset.Subset (suc q)}
      {v : Variance}
      {P : NfTy [] Kinds.KP}
      {S : NfTy [] SLin}
      {i : Fin (suc q)}
    → (i∈ : i Subset.∈ ssout)
    → A ∋ˡ x ∶ MatchBranchInput ssin v P S
    → ExprContextReduction.ReplaceAt
        A x
        (B-Lin (MatchBranchOutput ssout v P S i i∈))
        Target
    → RecvBranchAdvance
        A x i Target
        (MatchBranchInput ssin v P S)
        (MatchBranchOutput ssout v P S i i∈)

data SendBranchAdvance
    {n : ℕ}
    (A : Ctx [] n)
    (x : Fin n) :
    ∀ {k}
    → (i : Fin k)
    → (Target : Ctx [] n)
    → (Old New : NfTy [] SLin)
    → Set where

  send-branch-advance :
    ∀ {k}
      {i : Fin k}
      {Target : Ctx [] n}
      {ss : Subset.Subset k}
      {v : Variance}
      {P : NfTy [] Kinds.KP}
      {S : NfTy [] SLin}
    → (i∈ : i Subset.∈ ss)
    → A ∋ˡ x ∶ selectSetInNf ss v P S
    → ExprContextReduction.ReplaceAt
        A x (B-Lin (selectOutNf v i P S)) Target
    → SendBranchAdvance
        A x i Target
        (selectSetInNf ss v P S)
        (selectOutNf v i P S)

recv-label-result-advance :
  ∀ {n k pk m}
    {A Aout : Ctx [] n}
    {e′ : Expr [] n}
    {Expected : NfTy [] (Kinds.KV pk m)}
    {x : Fin n}
    {i : Fin k}
    {input-used output-used : AllUsed (allUsedCtx A)}
    (result :
      ReductionCheckResult
        (allUsedCtx A)
        (allUsedCtx A)
        (Label-RecvLab {x = x} {i = i}
          input-used output-used)
        A Aout e′ Expected)
  → Σ (NfTy [] SLin) λ Old →
      Σ (NfTy [] SLin) λ New →
        RecvBranchAdvance
          A x i (ReductionCheckResult.Γ₁ result) Old New
recv-label-result-advance {x = x} {i = i} result
  with ReductionCheckResult.ctx-step result
     | ReductionCheckResult.frame-update result
     | ReductionCheckResult.effect-aligned result
     | ReductionCheckResult.src-remove result
     | ReductionCheckResult.dst-remove result
... | Ctx-Match i∈ endpoint active-replace
    | Frm-Match {Γ₀ = Gf} {Γ₁ = Gf′} frame-i∈ frame-replace
    | effect-eq
    | source-remove
    | target-remove =
  let
    binding-eq =
      ERP.effect-replace-binding-injective effect-eq

    frame-replace′ =
      subst
        (λ b → ExprContextReduction.ReplaceAt Gf x b Gf′)
        (sym binding-eq)
        frame-replace
  in
  _ , _ ,
  recv-branch-advance
    i∈
    (frame-left-membership
      (remove-to-rest-frame source-remove)
      endpoint)
    (frame-replace-live
      (remove-to-rest-frame source-remove)
      active-replace
      frame-replace′
      (remove-to-rest-frame target-remove))

send-label-result-advance :
  ∀ {n k pk m}
    {A Aout Γin Γused : Ctx [] n}
    {e′ : Expr [] n}
    {Expected : NfTy [] (Kinds.KV pk m)}
    {x : Fin n}
    {i : Fin k}
    {ss : Subset.Subset k}
    {v : Variance}
    {P : NfTy [] Kinds.KP}
    {S : NfTy [] SLin}
    {i∈ : i Subset.∈ ss}
    {take :
      Γin ⊢ˡ x ∶ selectSetInNf ss v P S ⊣ Γused}
    {used : AllUsed Γused}
    (result :
      ReductionCheckResult
        Γin Γused
        (Label-SendLab i∈ take used)
        A Aout e′ Expected)
  → Σ (NfTy [] SLin) λ Old →
      Σ (NfTy [] SLin) λ New →
        SendBranchAdvance
          A x i (ReductionCheckResult.Γ₁ result) Old New
send-label-result-advance {x = x} {i = i} result
  with ReductionCheckResult.ctx-step result
     | ReductionCheckResult.frame-update result
     | ReductionCheckResult.effect-aligned result
     | ReductionCheckResult.src-remove result
     | ReductionCheckResult.dst-remove result
... | Ctx-Select selected endpoint active-replace
    | Frm-Select {Γ₀ = Gf} {Γ₁ = Gf′} frame-replace
    | effect-eq
    | source-remove
    | target-remove =
  let
    binding-eq =
      ERP.effect-replace-binding-injective effect-eq

    frame-replace′ =
      subst
        (λ b → ExprContextReduction.ReplaceAt Gf x b Gf′)
        (sym binding-eq)
        frame-replace
  in
  _ , _ ,
  send-branch-advance
    selected
    (frame-left-membership
      (remove-to-rest-frame source-remove)
      endpoint)
    (frame-replace-live
      (remove-to-rest-frame source-remove)
      active-replace
      frame-replace′
      (remove-to-rest-frame target-remove))

branch-action-shape :
  ∀ {n k}
    {Γ A B ATarget BTarget : Ctx [] n}
    {x y : Fin n}
    {i : Fin k}
    {RecvOld RecvNew SendOld SendNew : NfTy [] SLin}
  → RecvBranchAdvance A x i ATarget RecvOld RecvNew
  → SendBranchAdvance B y i BTarget SendOld SendNew
  → Γ ∋ˡ x ∶ RecvOld
  → Γ ∋ˡ y ∶ SendOld
  → DualLivePair Γ x y
  → DualContinuations RecvNew SendNew
branch-action-shape
    (recv-branch-advance
      {ssin = ssin} {ssout = ssout}
      {v = vrecv} {P = Precv} {S = Srecv}
      recv-selected receiver receiver-replace)
    (send-branch-advance
      {ss = sssend}
      {v = vsend} {P = Psend} {S = Ssend}
      send-selected sender sender-replace)
    receiver-global sender-global paired
  with selectSetInNf-injective
        (Relation.Binary.PropositionalEquality.trans
          (dual-live-pair-forward
            receiver-global sender-global paired)
          (dual-select-set-input ssin vrecv Precv Srecv))
... | refl , refl , refl , refl =
  DC-forward
    (sym
      (dual-match-branch-output
        ssout vrecv Precv Srecv _ recv-selected))

recv-branch-member :
  ∀ {n k}
    {A Target : Ctx [] n}
    {x : Fin n}
    {i : Fin k}
    {Old New : NfTy [] SLin}
  → RecvBranchAdvance A x i Target Old New
  → A ∋ˡ x ∶ Old
recv-branch-member
    (recv-branch-advance selected member replaced) =
  member

recv-branch-replacement :
  ∀ {n k}
    {A Target : Ctx [] n}
    {x : Fin n}
    {i : Fin k}
    {Old New : NfTy [] SLin}
  → RecvBranchAdvance A x i Target Old New
  → ExprContextReduction.ReplaceAt A x (B-Lin New) Target
recv-branch-replacement
    (recv-branch-advance selected member replaced) =
  replaced

send-branch-member :
  ∀ {n k}
    {A Target : Ctx [] n}
    {x : Fin n}
    {i : Fin k}
    {Old New : NfTy [] SLin}
  → SendBranchAdvance A x i Target Old New
  → A ∋ˡ x ∶ Old
send-branch-member
    (send-branch-advance selected member replaced) =
  member

send-branch-replacement :
  ∀ {n k}
    {A Target : Ctx [] n}
    {x : Fin n}
    {i : Fin k}
    {Old New : NfTy [] SLin}
  → SendBranchAdvance A x i Target Old New
  → ExprContextReduction.ReplaceAt A x (B-Lin New) Target
send-branch-replacement
    (send-branch-advance selected member replaced) =
  replaced

close-result-replacement :
  ∀ {n pk m}
    {A Aout : Ctx [] n}
    {e′ : Expr [] n}
    {Expected : NfTy [] (Kinds.KV pk m)}
    {x : Fin n}
    {input-used output-used : AllUsed (allUsedCtx A)}
    (result :
      ReductionCheckResult
        (allUsedCtx A)
        (allUsedCtx A)
        (Label-Close input-used output-used)
        A Aout e′ Expected)
  → (A ∋ˡ x ∶ normalizeTy EndLin)
      × ExprContextReduction.ReplaceAt
          A x (B-Used (normalizeTy EndLin))
          (ReductionCheckResult.Γ₁ result)
close-result-replacement {x = x} result
  with ReductionCheckResult.ctx-step result
     | ReductionCheckResult.frame-update result
     | ReductionCheckResult.effect-aligned result
     | ReductionCheckResult.src-remove result
     | ReductionCheckResult.dst-remove result
... | Ctx-Close endpoint active-replace
    | Frm-Close frame-replace
    | refl
    | source-remove
    | target-remove =
  frame-left-membership
    (remove-to-rest-frame source-remove)
    endpoint ,
  frame-replace-used
    (remove-to-rest-frame source-remove)
    active-replace
    frame-replace
    (remove-to-rest-frame target-remove)

split-retag :
  ∀ {Δ n} {Γ Γ′ A B : Ctx Δ n}
  → Γ ≈ᵘ Γ′
  → Split Γ A B
  → Σ (Ctx Δ n) λ A′ →
      Σ (Ctx Δ n) λ B′ →
        Split Γ′ A′ B′ × (A ≈ᵘ A′) × (B ≈ᵘ B′)
split-retag ≈ᵘ-∅ S-∅ = ∅ , ∅ , S-∅ , ≈ᵘ-∅ , ≈ᵘ-∅
split-retag (≈ᵘ-lin eq) (S-Linˡ split)
  with split-retag eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Linˡ split′ , ≈ᵘ-lin eqA , ≈ᵘ-used eqB
split-retag (≈ᵘ-lin eq) (S-Linʳ split)
  with split-retag eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Linʳ split′ , ≈ᵘ-used eqA , ≈ᵘ-lin eqB
split-retag (≈ᵘ-un eq) (S-Un split)
  with split-retag eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Un split′ , ≈ᵘ-un eqA , ≈ᵘ-un eqB
split-retag (≈ᵘ-used eq) (S-Used split)
  with split-retag eq split
... | A′ , B′ , split′ , eqA , eqB =
  _ , _ , S-Used split′ , ≈ᵘ-used eqA , ≈ᵘ-used eqB

threads-retag :
  ∀ {n} {Γ Γ′ : Ctx [] n} {es : List (Expr [] n)}
  → Γ ≈ᵘ Γ′
  → ThreadsTyped Γ es
  → ThreadsTyped Γ′ es
threads-retag eq (TT-[] au) =
  TT-[] (allUsed-resp-≈ᵘ eq au)
threads-retag eq (TT-∷ split d au rest)
  with split-retag eq split
... | A′ , B′ , split′ , eqA , eqB
  with retag-check-input d eqA
... | Aout′ , d′ , out-eq =
  TT-∷
    split′
    d′
    (allUsed-resp-≈ᵘ (≈ᵘ-sym out-eq) au)
    (threads-retag eqB rest)

-- Reassociate two consecutive allocations so that the second thread is
-- allocated first.  This is the context-level content of swapping adjacent
-- threads.

split-swap-nested :
  ∀ {Δ n} {Γ Γ₁ Γ₂… Γ₂ Γ₃ : Ctx Δ n}
  → Split Γ Γ₁ Γ₂…
  → Split Γ₂… Γ₂ Γ₃
  → Σ (Ctx Δ n) λ Γ₁… →
      Split Γ Γ₂ Γ₁… × Split Γ₁… Γ₁ Γ₃
split-swap-nested S-∅ S-∅ = ∅ , S-∅ , S-∅
split-swap-nested (S-Linˡ sp₁) (S-Used sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , out , inner =
  _ , S-Linʳ out , S-Linˡ inner
split-swap-nested (S-Linʳ sp₁) (S-Linˡ sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , out , inner =
  _ , S-Linˡ out , S-Used inner
split-swap-nested (S-Linʳ sp₁) (S-Linʳ sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , out , inner =
  _ , S-Linʳ out , S-Linʳ inner
split-swap-nested (S-Un sp₁) (S-Un sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , out , inner =
  _ , S-Un out , S-Un inner
split-swap-nested (S-Used sp₁) (S-Used sp₂)
  with split-swap-nested sp₁ sp₂
... | Γ₁… , out , inner =
  _ , S-Used out , S-Used inner

threads-swap :
  ∀ {n} {Γ : Ctx [] n} {e₁ e₂ : Expr [] n} {es : List (Expr [] n)}
  → ThreadsTyped Γ (e₁ ∷ e₂ ∷ es)
  → ThreadsTyped Γ (e₂ ∷ e₁ ∷ es)
threads-swap
    (TT-∷ split₁ d₁ au₁ (TT-∷ split₂ d₂ au₂ rest))
  with split-swap-nested split₁ split₂
... | Γ₁… , split₂′ , split₁′ =
  TT-∷ split₂′ d₂ au₂ (TT-∷ split₁′ d₁ au₁ rest)

threads-resp-↭ :
  ∀ {n} {Γ : Ctx [] n} {es es′ : List (Expr [] n)}
  → es ↭ es′
  → ThreadsTyped Γ es
  → ThreadsTyped Γ es′
threads-resp-↭ refl typed = typed
threads-resp-↭ (prep e permutation)
    (TT-∷ split d au rest) =
  TT-∷ split d au (threads-resp-↭ permutation rest)
threads-resp-↭ (swap e₁ e₂ permutation) typed
  with threads-swap typed
... | TT-∷ split₂ d₂ au₂ (TT-∷ split₁ d₁ au₁ rest) =
  TT-∷ split₂ d₂ au₂
    (TT-∷ split₁ d₁ au₁
      (threads-resp-↭ permutation rest))
threads-resp-↭ (trans p q) typed =
  threads-resp-↭ q (threads-resp-↭ p typed)

lookup-front :
  ∀ {A : Set} (xs : List A) (i : Fin (length xs))
  → xs ↭ lookup xs i ∷ removeAt xs i
lookup-front (x ∷ xs) fzero = refl
lookup-front (x ∷ xs) (fsuc i) =
  trans
    (prep x (lookup-front xs i))
    (swap x (lookup xs i) refl)

updateAt-front :
  ∀ {A : Set} (xs : List A) (i : Fin (length xs)) (x′ : A)
  → L.updateAt xs i (const x′) ↭ x′ ∷ removeAt xs i
updateAt-front (x ∷ xs) fzero x′ = refl
updateAt-front (x ∷ xs) (fsuc i) x′ =
  trans
    (prep x (updateAt-front xs i x′))
    (swap x x′ refl)

subst-Fin-zero-sym-cong :
  ∀ {m n} (p : m ≡ n)
  → subst Fin (sym (cong Data.Nat.suc p)) fzero ≡ fzero
subst-Fin-zero-sym-cong refl = refl

subst-Fin-suc-sym-cong :
  ∀ {m n} (p : m ≡ n) (i : Fin n)
  → subst Fin (sym (cong Data.Nat.suc p)) (fsuc i)
      ≡ fsuc (subst Fin (sym p) i)
subst-Fin-suc-sym-cong refl i = refl

map-updateAt-front :
  ∀ {A B : Set} (f : A → B) (xs : List A)
    (i : Fin (length xs)) (y : B)
  → L.updateAt (map f xs)
      (subst Fin (sym (length-map f xs)) i)
      (const y)
      ↭ y ∷ map f (removeAt xs i)
map-updateAt-front f (x ∷ xs) fzero y
  rewrite subst-Fin-zero-sym-cong (length-map f xs) = refl
map-updateAt-front f (x ∷ xs) (fsuc i) y
  rewrite subst-Fin-suc-sym-cong (length-map f xs) i =
  trans
    (prep (f x) (map-updateAt-front f xs i y))
    (swap (f x) y refl)

removeTwo :
  ∀ {A : Set} (xs : List A)
  → (i j : Fin (length xs))
  → i ≢ j
  → List A
removeTwo (x ∷ xs) fzero fzero i≠j = ⊥-elim (i≠j refl)
removeTwo (x ∷ xs) fzero (fsuc j) i≠j = removeAt xs j
removeTwo (x ∷ xs) (fsuc i) fzero i≠j = removeAt xs i
removeTwo (x ∷ xs) (fsuc i) (fsuc j) i≠j =
  x ∷ removeTwo xs i j (λ eq → i≠j (cong fsuc eq))

two-front :
  ∀ {A : Set} (xs : List A)
    (i j : Fin (length xs)) (i≠j : i ≢ j)
  → xs ↭
      lookup xs i ∷ lookup xs j ∷ removeTwo xs i j i≠j
two-front (x ∷ xs) fzero fzero i≠j = ⊥-elim (i≠j refl)
two-front (x ∷ xs) fzero (fsuc j) i≠j =
  prep x (lookup-front xs j)
two-front (x ∷ xs) (fsuc i) fzero i≠j =
  trans
    (prep x (lookup-front xs i))
    (swap x (lookup xs i) refl)
two-front (x ∷ xs) (fsuc i) (fsuc j) i≠j =
  let
    tail = two-front xs i j (λ eq → i≠j (cong fsuc eq))
  in
  trans
    (prep x tail)
    (trans
      (swap x (lookup xs i) refl)
      (prep (lookup xs i) (swap x (lookup xs j) refl)))

doubleUpdateAt :
  ∀ {A : Set} (xs : List A)
  → Fin (length xs)
  → Fin (length xs)
  → A → A → List A
doubleUpdateAt xs i j x′ y′ =
  let xs′ = L.updateAt xs i (const x′)
  in L.updateAt xs′
      (subst Fin (sym (PSF.length-updateAt xs i)) j)
      (const y′)

double-update-front :
  ∀ {A : Set} (xs : List A)
    (i j : Fin (length xs)) (i≠j : i ≢ j) (x′ y′ : A)
  → doubleUpdateAt xs i j x′ y′
      ↭ x′ ∷ y′ ∷ removeTwo xs i j i≠j
double-update-front (x ∷ xs) fzero fzero i≠j x′ y′ =
  ⊥-elim (i≠j refl)
double-update-front (x ∷ xs) fzero (fsuc j) i≠j x′ y′ =
  prep x′ (updateAt-front xs j y′)
double-update-front (x ∷ xs) (fsuc i) fzero i≠j x′ y′ =
  subst
    (λ index →
      L.updateAt (x ∷ L.updateAt xs i (const x′)) index (const y′)
        ↭ x′ ∷ y′ ∷ removeAt xs i)
    (sym (subst-Fin-zero-sym-cong (PSF.length-updateAt xs i)))
    (trans
      (prep y′ (updateAt-front xs i x′))
      (swap y′ x′ refl))
double-update-front (x ∷ xs) (fsuc i) (fsuc j) i≠j x′ y′ =
  subst
    (λ index →
      L.updateAt (x ∷ L.updateAt xs i (const x′)) index (const y′)
        ↭ x′ ∷ y′ ∷
          x ∷ removeTwo xs i j (λ eq → i≠j (cong fsuc eq)))
    (sym (subst-Fin-suc-sym-cong (PSF.length-updateAt xs i) j))
    (let
      tail = double-update-front xs i j
        (λ eq → i≠j (cong fsuc eq)) x′ y′
    in
    trans
      (prep x tail)
      (trans
        (swap x x′ refl)
        (prep x′ (swap x y′ refl))))

------------------------------------------------------------------------
-- Preservation statement and the internal beta case

record PreservationResult
    {n : ℕ}
    (C′ : Conf n) : Set where
  field
    Γ′ : Ctx [] n
    typing : Γ′ ⊢conf C′

beta-head-preserves :
  ∀ {n} {Γ : Ctx [] n} {e e′ : Expr [] n} {es : List (Expr [] n)}
  → e —[ L-β ]→ e′
  → ThreadsTyped Γ (e ∷ es)
  → ThreadsTyped Γ (e′ ∷ es)
beta-head-preserves step (TT-∷ split d au rest)
  with beta-reduction-preserves-check step d
... | result =
  TT-∷
    split
    (CheckResult.derivation result)
    (allUsed-resp-≈ᵘ (≈ᵘ-sym (CheckResult.leftover result)) au)
    rest

act-beta-preserves :
  ∀ {n} {Γ : Ctx [] n} {C : Conf n}
    {i : Fin (length (exps C))} {e′ : Expr [] n}
  → Γ ⊢conf C
  → PSF.Conf.lookup C i —[ L-β ]→ e′
  → Γ ⊢conf PSF.Conf.updateAt C i (const e′)
act-beta-preserves (T-Conf live-ok paired threads) step =
  T-Conf live-ok paired
    (threads-resp-↭
      (↭-sym (updateAt-front _ _ _))
      (beta-head-preserves step
        (threads-resp-↭ (lookup-front _ _) threads)))

fork-head-preserves :
  ∀ {n} {Γ : Ctx [] n} {e e′ : Expr [] n} {v : Value [] n}
    {es : List (Expr [] n)}
  → e —[ L-Fork v ]→ e′
  → ThreadsTyped Γ (e ∷ es)
  → ThreadsTyped Γ
      (E-App (E-Val v) (E-Val (V-Const C-Unit)) ∷ e′ ∷ es)
fork-head-preserves step (TT-∷ outer source source-au rest)
  with reduction-preserves-check
         step source
         (Label-Fork
           (allUsedCtx-AllUsed _)
           (allUsedCtx-AllUsed _))
         Ex-Fork
         (check-disjoint-resources
           source step
           (Label-Fork
             (allUsedCtx-AllUsed _)
             (allUsedCtx-AllUsed _))
           Ex-Fork
           (ctx-allused-disjoint _))
... | record
        { src-remove = src-remove
        ; frame-update = Frm-Fork
        ; dst-remove = dst-remove
        ; ctx-step = Ctx-Fork closure-remove closure-check closure-au
        ; check = reduct
        ; leftover = reduct-leftover
        }
  with remove-exchange src-remove closure-remove dst-remove
... | closure-remove-full
  with split-expand-left
         outer
         (frame-to-split (remove-to-rest-frame closure-remove-full))
... | after-closure , split-closure , split-reduct
  with closure-check
... | T-Check closure-synth closure-sub
  with arrow-subtype-inversion closure-sub
... | A , U , closure-type , unit<:A , U<:unit =
  TT-∷
    split-closure
    (T-Check
      (T-App
        (subst
          (λ X → _ ⊢ E-Val _ ⇒ X ⊣ _)
          closure-type
          closure-synth)
        (check-subsumption
          (T-Check
            (T-Val (TV-Const CT-Unit))
            (<:ₜ-refl (unitConstNf)))
          unit<:A))
      U<:unit)
    closure-au
    (TT-∷
      split-reduct
      reduct
      (allUsed-resp-≈ᵘ (≈ᵘ-sym reduct-leftover) source-au)
      rest)

act-fork-preserves :
  ∀ {n} {Γ : Ctx [] n} {C : Conf n}
    {i : Fin (length (exps C))} {e′ : Expr [] n} {v : Value [] n}
  → Γ ⊢conf C
  → PSF.Conf.lookup C i —[ L-Fork v ]→ e′
  → Γ ⊢conf
      PSF.Conf.add
        (PSF.Conf.updateAt C i (const e′))
        (E-App (E-Val v) (E-Val (V-Const C-Unit)))
act-fork-preserves (T-Conf live-ok paired threads) step =
  T-Conf live-ok paired
    (threads-resp-↭
      (prep _ (↭-sym (updateAt-front _ _ _)))
      (fork-head-preserves step
        (threads-resp-↭ (lookup-front _ _) threads)))

new-weaken-threads :
  ∀ {n} (S : Ty [] SLin) {Γ : Ctx [] n} {es : List (Expr [] n)}
  → ThreadsTyped Γ es
  → ThreadsTyped
      (B-Used (normalizeTy S) ▻
       B-Used (normalizeTy (T-Dual Duality.D-S S)) ▻ Γ)
      (map (weakenExprBy 2) es)
new-weaken-threads S (TT-[] au) =
  TT-[] (AU-used (AU-used au))
new-weaken-threads S (TT-∷ split d au rest) =
  TT-∷
    (S-Used (S-Used split))
    (new-weaken-check-at 0 S d)
    (AU-used (AU-used au))
    (new-weaken-threads S rest)

new-head-preserves :
  ∀ {n} {Γ : Ctx [] n} {e : Expr [] n}
    {e′ : Expr [] (2 + n)} {S : Ty [] SLin} {es : List (Expr [] n)}
  → e —[ L-New S ]→ e′
  → ThreadsTyped Γ (e ∷ es)
  → ThreadsTyped
      (B-Lin (normalizeTy S) ▻
       B-Lin (normalizeTy (T-Dual Duality.D-S S)) ▻ Γ)
      (e′ ∷ map (weakenExprBy 2) es)
new-head-preserves {S = S} step (TT-∷ outer source source-au rest)
  with reduction-preserves-check
         step source
         (Label-New
           (allUsedCtx-AllUsed _)
           (allUsedCtx-AllUsed _))
         Ex-New
         (check-disjoint-resources
           source step
           (Label-New
             (allUsedCtx-AllUsed _)
             (allUsedCtx-AllUsed _))
           Ex-New
           (ctx-allused-disjoint _))
... | record
        { Γ₁ = target-input
        ; src-remove = src-remove
        ; frame-update = Frm-New
        ; dst-remove = dst-remove
        ; ctx-step = Ctx-New
        ; check = reduct
        ; leftover = reduct-leftover
        } =
  let
    target-input-eq =
      remove-source-unique
        dst-remove
        (RM-drop (RM-drop src-remove))

    reduct′ =
      subst
        (λ X → X ⊢ _ ⇐ normalizeTy T-Base ⊣ _)
        target-input-eq
        reduct
  in
  TT-∷
    (S-Linˡ (S-Linˡ outer))
    reduct′
    (allUsed-resp-≈ᵘ
      (≈ᵘ-sym reduct-leftover)
      (AU-used (AU-used source-au)))
    (new-weaken-threads S rest)

act-new-preserves :
  ∀ {n} {Γ : Ctx [] n} {C : Conf n}
    {i : Fin (length (exps C))} {e′ : Expr [] (2 + n)}
    {S : Ty [] SLin}
  → Γ ⊢conf C
  → PSF.Conf.lookup C i —[ L-New S ]→ e′
  → (B-Lin (normalizeTy S) ▻
      B-Lin (normalizeTy (T-Dual Duality.D-S S)) ▻ Γ)
      ⊢conf
      PSF.Conf.updateAt
        (PSF.activateFreshPair C)
        (subst Fin (sym (length-map _ (exps C))) i)
        (const e′)
act-new-preserves {Γ = Γ} {S = S}
    (T-Conf live-ok paired threads) step =
  T-Conf
    (LC-live (LC-live live-ok))
    (subst
      (λ X →
        PairedCtx
          (B-Lin (normalizeTy S) ▻ B-Lin X ▻ Γ))
      (sym (normalize-dual S))
      (PC-pair SB-live SB-live paired))
    (threads-resp-↭
      (↭-sym (map-updateAt-front (weakenExprBy 2) _ _ _))
      (new-head-preserves step
        (threads-resp-↭ (lookup-front _ _) threads)))

------------------------------------------------------------------------
-- Typed synchronization

message-head-preserves :
  ∀ {n}
    {Γ : Ctx [] (2 + n)}
    {ss : Subset (2 + n)}
    {x y : Fin (2 + n)}
    {e₁ e₂ e₁′ e₂′ : Expr [] (2 + n)}
    {v : Value [] (2 + n)}
    {es : List (Expr [] (2 + n))}
  → LiveCtx ss Γ
  → PairedCtx Γ
  → PSF.FinFreshPair {n} x y
  → x Subset.∈ ss
  → y Subset.∈ ss
  → e₁ —[ L-RecvVal x v ]→ e₁′
  → e₂ —[ L-SendVal y v ]→ e₂′
  → ThreadsTyped Γ (e₁ ∷ e₂ ∷ es)
  → Σ (Ctx [] (2 + n)) λ Γ′ →
      LiveCtx ss Γ′
      × PairedCtx Γ′
      × ThreadsTyped Γ′ (e₁′ ∷ e₂′ ∷ es)
message-head-preserves
    live-ok paired pair x-live y-live recv send
    (TT-∷ split₁ check₁ used₁
      (TT-∷ split₂ check₂@(T-Check source₂ source₂<:base)
        used₂ rest))
  with EAR.recv-value-resources-check check₁ recv
     | EAR.send-value-resources-check check₂ send in resources-eq
... | EAR.recv-value-resources
        {T = Trecv} {S = Srecv}
        recv-remove recv-take recv-used
    | resources@(EAR.send-value-resources
        {T = Tsend} {U = U} {S = Ssend}
        send-remove send-take payload payload-sub payload-used)
  with send-remove-membership-fresh send-remove send-take
... | Bminus , payload-remove , sender-member
  with split-transfer-left split₁ split₂ payload-remove
... | AP , BminusR , transferred , first-transferred , second-transferred
  with dual-action-shape
        (split-left-membership first-transferred
          (frame-left-membership transferred
            (extract-membership recv-remove
              (take-membership-fresh recv-take))))
        (split-right-membership first-transferred
          (split-left-membership second-transferred sender-member))
        (paired-live-endpoints live-ok paired pair x-live y-live)
... | refl , payload-eq , continuations
  with reduction-preserves-check
        recv
        check₁
        (Label-RecvVal
          recv-take
          recv-used
          payload
          (subst
            (λ T →
              U <:ₜ T)
            (sym payload-eq)
            payload-sub)
          payload-used
          (ECP.remove-removed-disjoint
            recv-remove
            (payload-transfer-disjoint
              split₁ split₂ payload-remove)))
        (Ex-RecvVal recv-remove recv-take recv-used)
        (check-disjoint-resources
          check₁
          recv
          (Label-RecvVal
            recv-take
            recv-used
            payload
            (subst
              (λ T →
                U <:ₜ T)
              (sym payload-eq)
              payload-sub)
            payload-used
            (ECP.remove-removed-disjoint
              recv-remove
              (payload-transfer-disjoint
                split₁ split₂ payload-remove)))
          (Ex-RecvVal recv-remove recv-take recv-used)
          (payload-transfer-disjoint split₁ split₂ payload-remove))
... | recv-result
  with reduction-preserves-check
        send
        check₂
        (ERP.SendInterface.label (ERP.send-interface resources))
        (ERP.SendInterface.extract (ERP.send-interface resources))
        (check-resources
          (ERP.resources-send resources (sym resources-eq)))
... | send-result
  with recv-result-replacement recv-result transferred
... | Srecv′ , receiver-member , receiver-replace
  with send-result-replacement
        resources send-result Bminus payload-remove
... | payloadKind , Payload , Ssend′ ,
      sender-member′ , sender-replace
  with recvChanNf-injective
        (linear-membership-type
          receiver-member
          (frame-left-membership transferred
            (extract-membership recv-remove
              (take-membership-fresh recv-take))))
     | sendChanNf-injective
        (linear-membership-type sender-member′ sender-member)
... | refl , refl , refl | refl , refl , refl
  with target-split-reconstruction
        split₁ split₂ payload-remove transferred
        receiver-member receiver-replace
        sender-member′ sender-replace
... | Γ′ , Γx , BC′ , A′ , B′ , R′ ,
      split₁′ , split₂′ ,
      receiver-target-eq , sender-target-eq , rest-eq ,
      global-x-replace , global-y-replace
  with retag-check-input
        (ReductionCheckResult.check recv-result)
        receiver-target-eq
... | Aout′ , recv-check′ , recv-out-eq
  with retag-check-input
        (ReductionCheckResult.check send-result)
        sender-target-eq
... | Bout′ , send-check′ , send-out-eq =
  Γ′ ,
  live-replace-pair-live
    live-ok pair x-live y-live
    global-x-replace global-y-replace ,
  paired-replace-pair-live
    paired pair
    global-x-replace global-y-replace
    continuations ,
  TT-∷
    split₁′
    recv-check′
    (allUsed-resp-≈ᵘ
      (≈ᵘ-sym recv-out-eq)
      (allUsed-resp-≈ᵘ
        (≈ᵘ-sym (ReductionCheckResult.leftover recv-result))
        used₁))
    (TT-∷
      split₂′
      send-check′
      (allUsed-resp-≈ᵘ
        (≈ᵘ-sym send-out-eq)
        (allUsed-resp-≈ᵘ
          (≈ᵘ-sym (ReductionCheckResult.leftover send-result))
          used₂))
      (threads-retag rest-eq rest))

branch-head-preserves :
  ∀ {n k}
    {Γ : Ctx [] (2 + n)}
    {ss : Subset (2 + n)}
    {x y : Fin (2 + n)}
    {i : Fin k}
    {e₁ e₂ e₁′ e₂′ : Expr [] (2 + n)}
    {es : List (Expr [] (2 + n))}
  → LiveCtx ss Γ
  → PairedCtx Γ
  → PSF.FinFreshPair {n} x y
  → x Subset.∈ ss
  → y Subset.∈ ss
  → e₁ —[ L-RecvLab x i ]→ e₁′
  → e₂ —[ L-SendLab y i ]→ e₂′
  → ThreadsTyped Γ (e₁ ∷ e₂ ∷ es)
  → Σ (Ctx [] (2 + n)) λ Γ′ →
      LiveCtx ss Γ′
      × PairedCtx Γ′
      × ThreadsTyped Γ′ (e₁′ ∷ e₂′ ∷ es)
branch-head-preserves
    live-ok paired pair x-live y-live recv send
    (TT-∷ split₁ check₁ used₁
      (TT-∷ split₂ check₂ used₂ rest))
  with EAR.send-label-resources-check check₂ send
... | EAR.send-label-resources
        selected send-remove send-take send-used
  with reduction-preserves-check
        recv
        check₁
        (Label-RecvLab
          (allUsedCtx-AllUsed _)
          (allUsedCtx-AllUsed _))
        Ex-RecvLab
        (check-disjoint-resources
          check₁
          recv
          (Label-RecvLab
            (allUsedCtx-AllUsed _)
            (allUsedCtx-AllUsed _))
          Ex-RecvLab
          (ctx-allused-disjoint _))
... | result₁
  with reduction-preserves-check
        send
        check₂
        (Label-SendLab selected send-take send-used)
        (Ex-SendLab send-remove selected send-take)
        (check-disjoint-resources
          check₂
          send
          (Label-SendLab selected send-take send-used)
          (Ex-SendLab send-remove selected send-take)
          (send-label-output-disjoint
            send-remove send-take send-used))
... | result₂
  with recv-label-result-advance result₁
     | send-label-result-advance result₂
... | RecvOld , RecvNew , recv-advance
    | SendOld , SendNew , send-advance
  with branch-action-shape
        recv-advance
        send-advance
        (split-left-membership split₁
          (recv-branch-member recv-advance))
        (split-right-membership split₁
          (split-left-membership split₂
            (send-branch-member send-advance)))
        (paired-live-endpoints
          live-ok paired pair x-live y-live)
... | continuations
  with target-split-reconstruction-direct
        split₁ split₂
        (recv-branch-member recv-advance)
        (recv-branch-replacement recv-advance)
        (send-branch-member send-advance)
        (send-branch-replacement send-advance)
... | Γ′ , Γx , BC′ , A′ , B′ , R′ ,
      split₁′ , split₂′ ,
      first-target-eq , second-target-eq , rest-eq ,
      global-x-replace , global-y-replace
  with retag-check-input
        (ReductionCheckResult.check result₁)
        first-target-eq
... | Aout′ , check₁′ , out₁-eq
  with retag-check-input
        (ReductionCheckResult.check result₂)
        second-target-eq
... | Bout′ , check₂′ , out₂-eq =
  Γ′ ,
  live-replace-pair-live
    live-ok pair x-live y-live
    global-x-replace global-y-replace ,
  paired-replace-pair-live
    paired pair
    global-x-replace global-y-replace
    continuations ,
  TT-∷
    split₁′
    check₁′
    (allUsed-resp-≈ᵘ
      (≈ᵘ-sym out₁-eq)
      (allUsed-resp-≈ᵘ
        (≈ᵘ-sym (ReductionCheckResult.leftover result₁))
        used₁))
    (TT-∷
      split₂′
      check₂′
      (allUsed-resp-≈ᵘ
        (≈ᵘ-sym out₂-eq)
        (allUsed-resp-≈ᵘ
          (≈ᵘ-sym (ReductionCheckResult.leftover result₂))
          used₂))
      (threads-retag rest-eq rest))

wait-head-preserves :
  ∀ {n}
    {Γ : Ctx [] (2 + n)}
    {ss : Subset (2 + n)}
    {x y : Fin (2 + n)}
    {e₁ e₂ e₁′ e₂′ : Expr [] (2 + n)}
    {es : List (Expr [] (2 + n))}
  → LiveCtx ss Γ
  → PairedCtx Γ
  → PSF.FinFreshPair {n} x y
  → x Subset.∈ ss
  → y Subset.∈ ss
  → e₁ —[ L-Close x ]→ e₁′
  → e₂ —[ L-Close y ]→ e₂′
  → ThreadsTyped Γ (e₁ ∷ e₂ ∷ es)
  → Σ (Ctx [] (2 + n)) λ Γ′ →
      LiveCtx ((ss Subset.- x) Subset.- y) Γ′
      × PairedCtx Γ′
      × ThreadsTyped Γ′ (e₁′ ∷ e₂′ ∷ es)
wait-head-preserves
    live-ok paired pair x-live y-live close₁ close₂
    (TT-∷ split₁ check₁ used₁
      (TT-∷ split₂ check₂ used₂ rest))
  with reduction-preserves-check
        close₁
        check₁
        (Label-Close
          (allUsedCtx-AllUsed _)
          (allUsedCtx-AllUsed _))
        Ex-Close
        (check-disjoint-resources
          check₁
          close₁
          (Label-Close
            (allUsedCtx-AllUsed _)
            (allUsedCtx-AllUsed _))
          Ex-Close
          (ctx-allused-disjoint _))
... | result₁
  with reduction-preserves-check
        close₂
        check₂
        (Label-Close
          (allUsedCtx-AllUsed _)
          (allUsedCtx-AllUsed _))
        Ex-Close
        (check-disjoint-resources
          check₂
          close₂
          (Label-Close
            (allUsedCtx-AllUsed _)
            (allUsedCtx-AllUsed _))
          Ex-Close
          (ctx-allused-disjoint _))
... | result₂
  with close-result-replacement result₁
     | close-result-replacement result₂
... | endpoint₁ , replace₁ | endpoint₂ , replace₂
  with target-split-reconstruction-used
        split₁ split₂
        endpoint₁ replace₁
        endpoint₂ replace₂
... | Γ′ , Γx , BC′ , A′ , B′ , R′ ,
      split₁′ , split₂′ ,
      first-target-eq , second-target-eq , rest-eq ,
      global-x-replace , global-y-replace
  with retag-check-input
        (ReductionCheckResult.check result₁)
        first-target-eq
... | Aout′ , check₁′ , out₁-eq
  with retag-check-input
        (ReductionCheckResult.check result₂)
        second-target-eq
... | Bout′ , check₂′ , out₂-eq =
  Γ′ ,
  live-replace-pair-dead
    live-ok pair x-live y-live
    global-x-replace global-y-replace ,
  paired-replace-pair-dead
    paired pair
    global-x-replace global-y-replace
    (DC-forward refl) ,
  TT-∷
    split₁′
    check₁′
    (allUsed-resp-≈ᵘ
      (≈ᵘ-sym out₁-eq)
      (allUsed-resp-≈ᵘ
        (≈ᵘ-sym (ReductionCheckResult.leftover result₁))
        used₁))
    (TT-∷
      split₂′
      check₂′
      (allUsed-resp-≈ᵘ
        (≈ᵘ-sym out₂-eq)
        (allUsed-resp-≈ᵘ
          (≈ᵘ-sym (ReductionCheckResult.leftover result₂))
          used₂))
      (threads-retag rest-eq rest))

configuration-reduction-preserves-typing :
  ∀ {n k} {Γ : Ctx [] n} {C : Conf n}
    {π : ConfLabel n k} {C′ : Conf (k + n)}
    (typing : Γ ⊢conf C)
    (step : C —conf[ π ]→ C′)
  → PreservationResult C′
configuration-reduction-preserves-typing {C = C}
    typing (PSF.Act-Beta step) =
  record
    { Γ′ = _
    ; typing = act-beta-preserves typing step
    }
configuration-reduction-preserves-typing {C = C}
    typing (PSF.Act-Fork step) =
  record
    { Γ′ = _
    ; typing = act-fork-preserves typing step
    }
configuration-reduction-preserves-typing {C = C}
    typing (PSF.Act-New step) =
  record
    { Γ′ = _
    ; typing = act-new-preserves typing step
    }
configuration-reduction-preserves-typing
    {C = C}
    (T-Conf live-ok paired threads)
    (PSF.Act-Msg i j i≠j pair x-live y-live recv send)
  with message-head-preserves
        live-ok paired pair x-live y-live recv send
        (threads-resp-↭
          (two-front (exps C) i j i≠j)
          threads)
... | Γ′ , live-ok′ , paired′ , target-front =
  record
    { Γ′ = Γ′
    ; typing = T-Conf live-ok′ paired′
        (threads-resp-↭
          (↭-sym (double-update-front (exps C) i j i≠j _ _))
          target-front)
    }
configuration-reduction-preserves-typing
    {C = C}
    (T-Conf live-ok paired threads)
    (PSF.Act-Bra i j i≠j pair x-live y-live recv send)
  with branch-head-preserves
        live-ok paired pair x-live y-live recv send
        (threads-resp-↭
          (two-front (exps C) i j i≠j)
          threads)
... | Γ′ , live-ok′ , paired′ , target-front =
  record
    { Γ′ = Γ′
    ; typing = T-Conf live-ok′ paired′
        (threads-resp-↭
          (↭-sym (double-update-front (exps C) i j i≠j _ _))
          target-front)
    }
configuration-reduction-preserves-typing
    {C = C}
    (T-Conf live-ok paired threads)
    (PSF.Act-Wait i j i≠j pair x-live y-live close₁ close₂)
  with wait-head-preserves
        live-ok paired pair x-live y-live close₁ close₂
        (threads-resp-↭
          (two-front (exps C) i j i≠j)
          threads)
... | Γ′ , live-ok′ , paired′ , target-front =
  record
    { Γ′ = Γ′
    ; typing = T-Conf live-ok′ paired′
        (threads-resp-↭
          (↭-sym (double-update-front (exps C) i j i≠j _ _))
          target-front)
    }
