module ExprReductionPreservationFresh where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Util using (dependent-ext₂)

import Duality
import Types
open import Kinds using (Kind; PreKind; KV; KT; KP; SLin; TLin; Lin; Un)
open import Types using (Ty; T-Dual)
open import Variance using (Variance)
open import NormalTypes using
  ( N-Normal
  ; N-Var
  ; NV-Var
  ; fromNormalTy
  ; nfTyTy-fromNormalTy
  ; from-nt-idem
  )
open import NormalTypesSubstitution using
  ( dualNFKind
  ; singleNFSub
  ; substNFTy
  )
open import AlgorithmicNFSubtyping using
  ( _<:ₜ_
  ; <:ₜ-refl
  ; <:ₜ-refl-eq
  ; <:ₜ-trans
  ; <:ₜ-sub
  ; <:ₜ-pair
  )
open import AlgorithmicNFSubstitution using (subst-preserves-<:ₜ)
open import ExprSyntax using
  ( NfTy
  ; Expr
  ; Value
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
  ; E-Val
  ; E-App
  ; E-TApp
  ; E-LetUnit
  ; E-Pair
  ; E-LetPair
  ; E-Match
  )
open import ExprSubstitution using
  ( Ren
  ; extRen
  ; extRen2
  ; renameValue
  ; renameExpr
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
  ; Act-App
  ; Act-TApp
  ; Act-LetPair
  ; Act-LetUnit
  ; Act-PairV
  ; Act-Rec
  ; Act-Fork
  ; Act-New
  ; Act-Rcv
  ; Act-Send
  ; Act-Match
  ; Act-Sel
  ; Act-Close
  ; Act-Receive₁
  ; Act-Receive₂
  ; Act-Send₁
  ; Act-Send₂
  ; Act-Select₁
  ; Act-Select₂
  ; Act-AppL
  ; Act-AppR
  ; Act-TAppE
  ; Act-PairL
  ; Act-PairR
  ; Act-MatchE
  ; Act-LetPairE
  ; Act-LetUnitE
  ; weakenValueBy
  ; weakenExprBy
  ; weakenExprBy1
  ; weakenExprBy2
  ; shiftRen
  )
open import ExprNormalTyping using
  ( Binding
  ; Ctx
  ; B-Lin
  ; B-Un
  ; B-Used
  ; _▻_
  ; _∷ˡ_
  ; _∋ˡ_∶_
  ; _⊢ˡ_∶_⊣_
  ; hereˡ
  ; thereˡˡ
  ; thereˡᵘ
  ; thereˡ✖
  ; TV-Abs
  ; TV-Rec
  ; TV-TAbs
  ; TV-Pair
  ; TV-Var-Lin
  ; TV-Var-Un
  ; TV-Receive₁
  ; TV-Receive₂
  ; TV-Send₁
  ; TV-Send₂
  ; TV-Select₁
  ; TV-Select₂
  ; TV-Const
  ; take-here
  ; take-thereˡ
  ; take-thereᵘ
  ; take-there✖
  ; CT-Unit
  ; CT-Fork
  ; CT-New
  ; CT-Receive
  ; CT-Send
  ; CT-Select
  ; CT-Close
  ; normalizeTy
  ; normalTyOf
  ; unitConstNf
  ; endConstNf
  ; wkNfTy
  ; receiveNf
  ; sendNf
  ; sessTyNf
  ; selectNf
  ; select1Nf
  ; pairNf
  ; polyNf
  ; MatchBranchInput
  ; MatchBranchOutput
  ; BranchJoin⁺
  ; _⊢ᵥ_⇒_⊣_
  ; _⊢_⇒_⊣_
  ; T-Val
  ; T-App
  ; T-TApp
  ; T-LetUnit
  ; T-LetPair
  ; T-Pair
  ; T-Match
  ; _⊢_⇐_⊣_
  ; T-Check
  )
open import ExprSubstitutionPreservationFresh using
  ( _≈ᵘ_
  ; ≈ᵘ-refl
  ; ≈ᵘ-sym
  ; ≈ᵘ-lin
  ; ≈ᵘ-un
  ; ≈ᵘ-used
  ; SynthResult
  ; CheckResult
  ; RT-∅
  ; RT-lin-used
  ; RT-lin-live
  ; RT-un
  ; RT-used
  ; RetaggedTransition
  ; retagged-from-shape
  ; retagged-output
  ; retag-synth
  ; retag-value
  ; retag-value-input
  ; retag-synth-input
  ; retag-synth-input-lin-used
  ; retag-synth-input-two-lin-used
  ; retag-check-input
  ; allUsed-resp-≈ᵘ
  ; ExpressionSubstitutionPreservesTyping
  ; expression-substitution-preserves-typing
  ; variable-substitution-preserves-synth
  )
open import ExprDoubleSubstitutionPreservationFresh using
  ( double-expression-substitution-preserves-typing
  ; DoubleBinderStrengtheningResult
  ; strengthen-double-binder
  )
open import ExprTypeSubstitutionPreservationFresh using
  ( substTy-preserves-wk-value
  ; cancel-single-wk-ty
  ; cancel-single-wk-proto
  ; subst-receive2
  ; subst-send2
  ; subst-select2
  ; subst-select1
  )
open import ExprUnrestrictedSubstitutionPreservationFresh using
  ( recursive-unfolding-preserves-value
  )
open import ExprTypingStrengthening using
  ( <:Γ-refl
  ; arrow-subtype-inversion
  ; pair-subtype-inversion
  ; poly-subtype-inversion
  ; match-input-subtype-inversion
  ; strengthen-match-branches
  ; branchjoin⁺-monotone
  ; coherent-strengthened-output
  ; check-subsumption
  )
open import ExprContextShape using
  ( _~Ctx_
  ; ∅~∅
  ; Lin~Lin
  ; Un~Un
  ; Lin~Used
  ; Used~Used
  ; drop-lin-used
  ; lin-used-invert
  ; value-preserves-~Ctx
  ; synth-preserves-~Ctx
  )
open import ExprContextProperties using
  ( AllUsed
  ; AU-∅
  ; AU-used
  ; AU-un
  ; LinearDisjoint
  ; LD-∅
  ; LD-used-used
  ; LD-used-live
  ; LD-live-used
  ; LD-un-un
  ; RemoveCtx
  ; RM-∅
  ; RM-drop
  ; RM-allused
  ; RM-lin
  ; RM-un
  ; FrameCtx
  ; FC-∅
  ; FC-allused
  ; FC-live
  ; FC-frame
  ; FC-un
  ; mergeDisjointContext
  ; mergeRemoveContext
  ; remove-allused-disjoint
  ; remove-linear
  ; remove-preserves-remove
  ; remove-preserves-disjoint
  ; remove-removed-disjoint
  ; restore-disjoint
  ; sym-disjoint
  ; allUsedCtx
  ; remove-allUsedCtx
  )
open import ExprContextReduction using
  ( _—ctx[_]→_
  ; _—frm[_]→_
  ; _⦂_⇒_
  ; Compatible
  ; Extract
  ; ReplaceAt
  ; R-here
  ; R-there
  ; replace-preserves-disjoint
  ; replace-at
  ; replace-frames-disjoint
  ; replace-frames-used
  ; merge-preserves-disjoint
  ; ctx-step-preserves-disjoint
  ; extendUsed
  ; recvChanNf
  ; sendChanNf
  ; selectInNf
  ; selectOutNf
  ; Ctx-β
  ; Ctx-New
  ; Ctx-Fork
  ; Ctx-Rcv
  ; Ctx-Send
  ; Ctx-Close
  ; Ctx-Match
  ; Ctx-Select
  ; Frm-β
  ; Frm-New
  ; Frm-Fork
  ; Frm-Rcv
  ; Frm-Send
  ; Frm-Close
  ; Frm-Match
  ; Frm-Select
  ; Label-β
  ; Label-New
  ; Label-Fork
  ; Label-RecvVal
  ; Label-SendVal
  ; Label-RecvLab
  ; Label-SendLab
  ; Label-Close
  ; Compat-β
  ; Compat-New
  ; Compat-Fork
  ; Compat-RecvVal
  ; Compat-SendVal
  ; Compat-Close
  ; Compat-Match
  ; Compat-Select
  ; Ex-β
  ; Ex-New
  ; Ex-Fork
  ; Ex-RecvVal
  ; Ex-SendVal
  ; Ex-RecvLab
  ; Ex-SendLab
  ; Ex-Close
  )
open import ExprTypingProperties using
  ( frame-unique
  ; frame-remove
  ; replay-value-allUsed
  )
open import ExprTypingInversion using
  ( recvChan-subtype
  ; sendChan-subtype
  ; match-branch-subtype
  ; select-app-subtype
  )
open import ExprTypingUniquenessFresh using
  ( take-membership-fresh
  ; value-kind-unique
  ; value-output-unique
  )
open import ExprTypingStripFresh using (strip-value)
open import ExprRenamingPreservation using
  ( liftRen
  ; insertAt
  ; ren-preserves-value
  ; ren-preserves-synth
  ; ren-preserves-check
  )
open import ExprPreservationStep2.ContextLemmas using
  ( allUsedCtx-remove
  ; take-replace-lin
  ; allUsedCtx-replace-lin-at
  ; allUsedCtx-merge
  ; extract-membership
  ; take-replace
  ; allUsedCtx-take
  ; allUsedCtx-replace-used-self
  ; end-subtype-invert
  ; remove-disjoint
  ; remove-membership
  )

-- A label records the variable being updated, but not the normal type written
-- at that position.  Preservation therefore tracks that the active context
-- step and its framed update perform the same concrete effect.  This is the
-- constructive replacement for the legacy use of `used-head-eq`.

data ContextEffect (n : ℕ) : Set where
  Effect-id Effect-new : ContextEffect n
  Effect-replace : Fin n → Binding [] → ContextEffect n

replacement-binding :
  ∀ {Δ n} {Γ Γ′ : Ctx Δ n} {x : Fin n} {b : Binding Δ}
  → ReplaceAt Γ x b Γ′
  → Binding Δ
replacement-binding {b = b} _ = b

mark-linear-used : Binding [] → Binding []
mark-linear-used (B-Lin T) = B-Used T
mark-linear-used (B-Un T) = B-Un T
mark-linear-used (B-Used T) = B-Used T

effect-replace-binding-injective :
  ∀ {n} {x : Fin n} {b c : Binding []}
  → Effect-replace x b ≡ Effect-replace x c
  → b ≡ c
effect-replace-binding-injective refl = refl

ctx-effect :
  ∀ {n Θ} {Γ₀ : Ctx [] n} {Γ₁ : Ctx [] (length Θ + n)}
    {ℓ : Label n Θ}
  → Γ₀ —ctx[ ℓ ]→ Γ₁
  → ContextEffect n
ctx-effect Ctx-β = Effect-id
ctx-effect Ctx-New = Effect-new
ctx-effect (Ctx-Fork _ _ _) = Effect-id
ctx-effect (Ctx-Rcv {x = x} {S = S} _ _ _ _ _ _ _) =
  Effect-replace x (B-Used S)
ctx-effect (Ctx-Send {x = x} {S = S} _ _ _ _ _) =
  Effect-replace x (B-Used (sessTyNf S))
ctx-effect (Ctx-Close {x = x} _ _) =
  Effect-replace x (B-Used endConstNf)
ctx-effect (Ctx-Match {x = x} _ _ rep) =
  Effect-replace x (mark-linear-used (replacement-binding rep))
ctx-effect (Ctx-Select {x = x} _ rep) =
  Effect-replace x (mark-linear-used (replacement-binding rep))

frm-effect :
  ∀ {n Θ} {Γ₀ : Ctx [] n} {Γ₁ : Ctx [] (length Θ + n)}
    {ℓ : Label n Θ}
  → Γ₀ —frm[ ℓ ]→ Γ₁
  → ContextEffect n
frm-effect Frm-β = Effect-id
frm-effect Frm-New = Effect-new
frm-effect Frm-Fork = Effect-id
frm-effect (Frm-Rcv {x = x} {S = S} _) =
  Effect-replace x (B-Used S)
frm-effect (Frm-Send {x = x} {S = S} _) =
  Effect-replace x (B-Used (sessTyNf S))
frm-effect (Frm-Close {x = x} _) =
  Effect-replace x (B-Used endConstNf)
frm-effect (Frm-Match {x = x} _ rep) =
  Effect-replace x (replacement-binding rep)
frm-effect (Frm-Select {x = x} rep) =
  Effect-replace x (replacement-binding rep)

ctx-step-preserves-disjoint-aligned :
  ∀ {n Θ}
    {Γ₀ : Ctx [] n} {Γ₁ : Ctx [] (length Θ + n)}
    {Γin Γv Γf : Ctx [] n} {ℓ : Label n Θ}
  → (step : Γ₀ —ctx[ ℓ ]→ Γ₁)
  → (lbl : ℓ ⦂ Γin ⇒ Γv)
  → Compatible step lbl
  → LinearDisjoint Γ₀ Γf
  → LinearDisjoint Γv Γf
  → Σ (Ctx [] (length Θ + n)) λ Γf′ →
      Σ (Γf —frm[ ℓ ]→ Γf′) λ frm →
        LinearDisjoint Γ₁ Γf′ ×
        (ctx-effect step ≡ frm-effect frm)
ctx-step-preserves-disjoint-aligned
    {Γf = Γf} Ctx-β (Label-β _ _) (Compat-β _) ld₀ _ =
  Γf , Frm-β , ld₀ , refl
ctx-step-preserves-disjoint-aligned
    {Γf = Γf} Ctx-New (Label-New {S = S} _ _) (Compat-New _) ld₀ _ =
  _ , Frm-New , LD-live-used (LD-live-used ld₀) , refl
ctx-step-preserves-disjoint-aligned
    {Γf = Γf} (Ctx-Fork rm d au) (Label-Fork _ _) (Compat-Fork _) ld₀ _ =
  Γf , Frm-Fork , remove-preserves-disjoint rm ld₀ , refl
ctx-step-preserves-disjoint-aligned
    {Γf = Γf}
    (Ctx-Rcv {x = x} {S = S} dv au ldv x∈ rep repv merge)
    (Label-RecvVal take autake dv′ au′ ldin)
    Compat-RecvVal ld₀ ldlabel
  with replace-at Γf x (B-Used S)
... | Γf′ , repf
  with replace-frames-disjoint ld₀ rep repf
... | ldxf
  with replace-frames-used ldlabel repv repf
... | ldvf =
  Γf′ , Frm-Rcv repf , merge-preserves-disjoint merge ldxf ldvf , refl
ctx-step-preserves-disjoint-aligned
    {Γf = Γf}
    (Ctx-Send {x = x} {S = S} rm dv au x∈ rep)
    (Label-SendVal take dv′ au′)
    Compat-SendVal ld₀ _
  with replace-at Γf x (B-Used (sessTyNf S))
... | Γf′ , repf =
  Γf′ , Frm-Send repf ,
  replace-frames-disjoint (remove-preserves-disjoint rm ld₀) rep repf ,
  refl
ctx-step-preserves-disjoint-aligned
    {Γf = Γf}
    (Ctx-Close {x = x} x∈ rep)
    (Label-Close _ _) (Compat-Close refl) ld₀ _
  with replace-at Γf x (B-Used endConstNf)
... | Γf′ , repf =
  Γf′ , Frm-Close repf , replace-frames-used ld₀ rep repf , refl
ctx-step-preserves-disjoint-aligned
    {Γf = Γf}
    (Ctx-Match {x = x} i∈ x∈ rep)
    (Label-RecvLab _ _) (Compat-Match refl) ld₀ _
  with replace-at Γf x (mark-linear-used (replacement-binding rep))
... | Γf′ , repf =
  Γf′ , Frm-Match i∈ repf ,
  replace-frames-disjoint ld₀ rep repf , refl
ctx-step-preserves-disjoint-aligned
    {Γf = Γf}
    (Ctx-Select {x = x} x∈ rep)
    (Label-SendLab _ _) Compat-Select ld₀ _
  with replace-at Γf x (mark-linear-used (replacement-binding rep))
... | Γf′ , repf =
  Γf′ , Frm-Select repf ,
  replace-frames-disjoint ld₀ rep repf , refl

same-input-retagged :
  ∀ {Δ n} {Γ Γ′ : Ctx Δ n}
  → Γ ~Ctx Γ′
  → RetaggedTransition Γ Γ Γ′ Γ′
same-input-retagged ∅~∅ = RT-∅
same-input-retagged (Lin~Lin shape) =
  RT-lin-live (same-input-retagged shape)
same-input-retagged (Lin~Used shape) =
  RT-lin-used (same-input-retagged shape)
same-input-retagged (Un~Un shape) =
  RT-un (same-input-retagged shape)
same-input-retagged (Used~Used shape) =
  RT-used (same-input-retagged shape)

replace-used-retagged :
  ∀ {Δ n pkₐ pk}
    {Γactive Γ Γstep Γ′ : Ctx Δ n}
    {x : Fin n}
    {A : NfTy Δ (KV pkₐ Lin)}
    {U : NfTy Δ (KV pk Lin)}
  → Γactive ∋ˡ x ∶ A
  → LinearDisjoint Γactive Γ
  → ReplaceAt Γ x (B-Used U) Γstep
  → Γ ~Ctx Γ′
  → Σ (Ctx Δ n) λ Γstep′ →
      ReplaceAt Γ′ x (B-Used U) Γstep′ ×
      RetaggedTransition Γ Γstep Γ′ Γstep′
replace-used-retagged hereˡ (LD-live-used ld) R-here (Used~Used shape) =
  _ , R-here , RT-used (same-input-retagged shape)
replace-used-retagged
    (thereˡˡ x∈) (LD-live-used ld) (R-there rep) (Used~Used shape)
  with replace-used-retagged x∈ ld rep shape
... | Γstep′ , rep′ , tr =
  _ , R-there rep′ , RT-used tr
replace-used-retagged
    (thereˡᵘ x∈) (LD-un-un ld) (R-there rep) (Un~Un shape)
  with replace-used-retagged x∈ ld rep shape
... | Γstep′ , rep′ , tr =
  _ , R-there rep′ , RT-un tr
replace-used-retagged
    (thereˡ✖ x∈) (LD-used-live ld) (R-there rep) (Lin~Lin shape)
  with replace-used-retagged x∈ ld rep shape
... | Γstep′ , rep′ , tr =
  _ , R-there rep′ , RT-lin-live tr
replace-used-retagged
    (thereˡ✖ x∈) (LD-used-live ld) (R-there rep) (Lin~Used shape)
  with replace-used-retagged x∈ ld rep shape
... | Γstep′ , rep′ , tr =
  _ , R-there rep′ , RT-lin-used tr
replace-used-retagged
    (thereˡ✖ x∈) (LD-used-used ld) (R-there rep) (Used~Used shape)
  with replace-used-retagged x∈ ld rep shape
... | Γstep′ , rep′ , tr =
  _ , R-there rep′ , RT-used tr

linear-membership-type :
  ∀ {Δ n pk}
    {Γ : Ctx Δ n}
    {x : Fin n}
    {T U : NfTy Δ (KV pk Lin)}
  → Γ ∋ˡ x ∶ T
  → Γ ∋ˡ x ∶ U
  → T ≡ U
linear-membership-type hereˡ hereˡ = refl
linear-membership-type (thereˡˡ T∈) (thereˡˡ U∈) =
  linear-membership-type T∈ U∈
linear-membership-type (thereˡᵘ T∈) (thereˡᵘ U∈) =
  linear-membership-type T∈ U∈
linear-membership-type (thereˡ✖ T∈) (thereˡ✖ U∈) =
  linear-membership-type T∈ U∈

replace-take-fresh :
  ∀ {Δ n pk pk′}
    {Γ₀ Γx Γ₂ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
    {U : NfTy Δ (KV pk′ Lin)}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₂
  → ReplaceAt Γ₀ x (B-Lin U) Γx
  → Σ (Ctx Δ n) λ Γout →
      (Γx ⊢ˡ x ∶ U ⊣ Γout) × (Γout ≈ᵘ Γ₂)
replace-take-fresh take-here R-here =
  _ , take-here , ≈ᵘ-used ≈ᵘ-refl
replace-take-fresh (take-thereˡ take) (R-there rep)
  with replace-take-fresh take rep
... | Γout , take′ , out≈ =
  _ , take-thereˡ take′ , ≈ᵘ-lin out≈
replace-take-fresh (take-thereᵘ take) (R-there rep)
  with replace-take-fresh take rep
... | Γout , take′ , out≈ =
  _ , take-thereᵘ take′ , ≈ᵘ-un out≈
replace-take-fresh (take-there✖ take) (R-there rep)
  with replace-take-fresh take rep
... | Γout , take′ , out≈ =
  _ , take-there✖ take′ , ≈ᵘ-used out≈

recv-payload-replace-≈ᵘ :
  ∀ {n pk}
    {Γin Γin′ Γv Γv′ : Ctx [] n}
    {x : Fin n}
    {T : NfTy [] (KV pk Lin)}
    {S : NfTy [] SLin}
  → Γin ⊢ˡ x ∶ recvChanNf T S ⊣ Γin′
  → LinearDisjoint Γin Γv
  → ReplaceAt Γv x (B-Used S) Γv′
  → Γv ≈ᵘ Γv′
recv-payload-replace-≈ᵘ take-here (LD-live-used ld) R-here =
  ≈ᵘ-used ≈ᵘ-refl
recv-payload-replace-≈ᵘ
    (take-thereˡ take) (LD-live-used ld) (R-there rep) =
  ≈ᵘ-used (recv-payload-replace-≈ᵘ take ld rep)
recv-payload-replace-≈ᵘ
    (take-thereᵘ take) (LD-un-un ld) (R-there rep) =
  ≈ᵘ-un (recv-payload-replace-≈ᵘ take ld rep)
recv-payload-replace-≈ᵘ
    (take-there✖ take) (LD-used-used ld) (R-there rep) =
  ≈ᵘ-used (recv-payload-replace-≈ᵘ take ld rep)
recv-payload-replace-≈ᵘ
    (take-there✖ take) (LD-used-live ld) (R-there rep) =
  ≈ᵘ-lin (recv-payload-replace-≈ᵘ take ld rep)

send-remove-membership-fresh :
  ∀ {n pk}
    {Γ₀ Γin Γr Γv : Ctx [] n}
    {x : Fin n}
    {T : NfTy [] (KV pk Lin)}
    {S : NfTy [] SLin}
  → RemoveCtx Γ₀ Γin Γr
  → Γin ⊢ˡ x ∶ sendChanNf T S ⊣ Γv
  → Σ (Ctx [] n) λ Γx →
      RemoveCtx Γ₀ Γv Γx × (Γx ∋ˡ x ∶ sendChanNf T S)
send-remove-membership-fresh (RM-lin r) take-here =
  _ , RM-drop r , hereˡ
send-remove-membership-fresh (RM-lin r) (take-thereˡ take)
  with send-remove-membership-fresh r take
... | Γx , rm , x∈ =
  _ , RM-lin rm , thereˡ✖ x∈
send-remove-membership-fresh (RM-un r) (take-thereᵘ take)
  with send-remove-membership-fresh r take
... | Γx , rm , x∈ =
  _ , RM-un rm , thereˡᵘ x∈
send-remove-membership-fresh (RM-allused r) (take-there✖ take)
  with send-remove-membership-fresh r take
... | Γx , rm , x∈ =
  _ , RM-allused rm , thereˡ✖ x∈
send-remove-membership-fresh (RM-drop r) (take-there✖ take)
  with send-remove-membership-fresh r take
... | Γx , rm , x∈ =
  _ , RM-drop rm , thereˡˡ x∈

remove-to-rest-frame :
  ∀ {Δ n} {Γ₀ G Γx : Ctx Δ n}
  → RemoveCtx Γ₀ G Γx
  → FrameCtx Γx G Γ₀
remove-to-rest-frame RM-∅ = FC-∅
remove-to-rest-frame (RM-drop rm) = FC-frame (remove-to-rest-frame rm)
remove-to-rest-frame (RM-allused rm) = FC-allused (remove-to-rest-frame rm)
remove-to-rest-frame (RM-lin rm) = FC-live (remove-to-rest-frame rm)
remove-to-rest-frame (RM-un rm) = FC-un (remove-to-rest-frame rm)

extRen-pointwise :
  ∀ {n} {ρ : Fin n → Fin n}
  → (∀ x → ρ x ≡ x)
  → ∀ x → extRen ρ x ≡ x
extRen-pointwise rel fzero = refl
extRen-pointwise rel (fsuc x) = cong fsuc (rel x)

mutual

  rename-pointwise-preserves-value :
    ∀ {Δ : List Kind} {n pk m}
      (ρ : Fin n → Fin n)
    → (∀ x → ρ x ≡ x)
    → ∀ {Γ₁ Γ₂ : Ctx Δ n}
        {v : Value Δ n}
        {T : NfTy Δ (KV pk m)}
    → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
    → Γ₁ ⊢ᵥ renameValue ρ v ⇒ T ⊣ Γ₂
  rename-pointwise-preserves-value ρ rel (TV-Const c) = TV-Const c
  rename-pointwise-preserves-value ρ rel (TV-Var-Lin {x = x} take)
    rewrite rel x = TV-Var-Lin take
  rename-pointwise-preserves-value ρ rel (TV-Var-Un {x = x} x∈)
    rewrite rel x = TV-Var-Un x∈
  rename-pointwise-preserves-value ρ rel (TV-Abs body) =
    TV-Abs
      (rename-pointwise-preserves-synth
        (extRen ρ)
        (extRen-pointwise rel)
        body)
  rename-pointwise-preserves-value ρ rel (TV-Rec body) =
    TV-Rec
      (rename-pointwise-preserves-check
        (extRen ρ)
        (extRen-pointwise rel)
        body)
  rename-pointwise-preserves-value ρ rel (TV-TAbs body) =
    TV-TAbs (rename-pointwise-preserves-value ρ rel body)
  rename-pointwise-preserves-value ρ rel (TV-Pair left right) =
    TV-Pair
      (rename-pointwise-preserves-value ρ rel left)
      (rename-pointwise-preserves-value ρ rel right)
  rename-pointwise-preserves-value ρ rel TV-Receive₁ = TV-Receive₁
  rename-pointwise-preserves-value ρ rel TV-Receive₂ = TV-Receive₂
  rename-pointwise-preserves-value ρ rel TV-Send₁ = TV-Send₁
  rename-pointwise-preserves-value ρ rel TV-Send₂ = TV-Send₂
  rename-pointwise-preserves-value ρ rel TV-Select₁ = TV-Select₁
  rename-pointwise-preserves-value ρ rel TV-Select₂ = TV-Select₂

  rename-pointwise-preserves-synth :
    ∀ {Δ : List Kind} {n pk m}
      (ρ : Fin n → Fin n)
    → (∀ x → ρ x ≡ x)
    → ∀ {Γ₁ Γ₂ : Ctx Δ n}
        {e : Expr Δ n}
        {T : NfTy Δ (KV pk m)}
    → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
    → Γ₁ ⊢ renameExpr ρ e ⇒ T ⊣ Γ₂
  rename-pointwise-preserves-synth ρ rel (T-Val d) =
    T-Val (rename-pointwise-preserves-value ρ rel d)
  rename-pointwise-preserves-synth ρ rel (T-Pair left right) =
    T-Pair
      (rename-pointwise-preserves-synth ρ rel left)
      (rename-pointwise-preserves-synth ρ rel right)
  rename-pointwise-preserves-synth ρ rel (T-App function argument) =
    T-App
      (rename-pointwise-preserves-synth ρ rel function)
      (rename-pointwise-preserves-check ρ rel argument)
  rename-pointwise-preserves-synth ρ rel (T-LetUnit scrutinee body) =
    T-LetUnit
      (rename-pointwise-preserves-check ρ rel scrutinee)
      (rename-pointwise-preserves-synth ρ rel body)
  rename-pointwise-preserves-synth ρ rel (T-LetPair scrutinee body) =
    T-LetPair
      (rename-pointwise-preserves-synth ρ rel scrutinee)
      (rename-pointwise-preserves-synth
        (extRen2 ρ)
        (extRen-pointwise (extRen-pointwise rel))
        body)
  rename-pointwise-preserves-synth ρ rel
    (T-Match
      {Γ₂ = Γ₂}
      {Γ₃ = Γ₃}
      {ss = ss}
      {v = v}
      {ssbranches = ssbranches}
      {incl = incl}
      {ne = ne}
      {P = P}
      {S = S}
      {branches = branches₀}
      {V = V}
      {sub = sub}
      scrutinee branches join) =
    T-Match
      {Γ₂ = Γ₂}
      {Γ₃ = Γ₃}
      {ss = ss}
      {v = v}
      {ssbranches = ssbranches}
      {incl = incl}
      {ne = ne}
      {P = P}
      {S = S}
      {branches = λ i i∈ → renameExpr (extRen ρ) (branches₀ i i∈)}
      {V = V}
      {sub = sub}
      (rename-pointwise-preserves-synth ρ rel scrutinee)
      (λ i i∈ →
        rename-pointwise-preserves-synth
          (extRen ρ)
          (extRen-pointwise rel)
          (branches i i∈))
      join
  rename-pointwise-preserves-synth ρ rel (T-TApp function) =
    T-TApp (rename-pointwise-preserves-synth ρ rel function)

  rename-pointwise-preserves-check :
    ∀ {Δ : List Kind} {n pk m}
      (ρ : Fin n → Fin n)
    → (∀ x → ρ x ≡ x)
    → ∀ {Γ₁ Γ₂ : Ctx Δ n}
        {e : Expr Δ n}
        {T : NfTy Δ (KV pk m)}
    → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
    → Γ₁ ⊢ renameExpr ρ e ⇐ T ⊣ Γ₂
  rename-pointwise-preserves-check ρ rel (T-Check d sub) =
    T-Check (rename-pointwise-preserves-synth ρ rel d) sub

weaken-zero-preserves-value :
  ∀ {n pk m}
    {Γ₁ Γ₂ : Ctx [] n}
    {v : Value [] n}
    {T : NfTy [] (KV pk m)}
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  → Γ₁ ⊢ᵥ weakenValueBy 0 v ⇒ T ⊣ Γ₂
weaken-zero-preserves-value =
  rename-pointwise-preserves-value (λ x → x) (λ x → refl)

weaken-zero-preserves-synth :
  ∀ {n pk m}
    {Γ₁ Γ₂ : Ctx [] n}
    {e : Expr [] n}
    {T : NfTy [] (KV pk m)}
  → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
  → Γ₁ ⊢ weakenExprBy 0 e ⇒ T ⊣ Γ₂
weaken-zero-preserves-synth =
  rename-pointwise-preserves-synth (λ x → x) (λ x → refl)

weaken-zero-preserves-check :
  ∀ {n pk m}
    {Γ₁ Γ₂ : Ctx [] n}
    {e : Expr [] n}
    {T : NfTy [] (KV pk m)}
  → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
  → Γ₁ ⊢ weakenExprBy 0 e ⇐ T ⊣ Γ₂
weaken-zero-preserves-check =
  rename-pointwise-preserves-check (λ x → x) (λ x → refl)

weaken-zero-preserves-synth1 :
  ∀ {n pk m}
    {Γ₁ Γ₂ : Ctx [] (suc n)}
    {e : Expr [] (suc n)}
    {U : NfTy [] (KV pk m)}
  → Γ₁ ⊢ e ⇒ U ⊣ Γ₂
  → Γ₁ ⊢ weakenExprBy1 0 e ⇒ U ⊣ Γ₂
weaken-zero-preserves-synth1 =
  rename-pointwise-preserves-synth
    (extRen (λ x → x))
    (extRen-pointwise (λ x → refl))

weaken-zero-preserves-synth2 :
  ∀ {n pk m}
    {Γ₁ Γ₂ : Ctx [] (suc (suc n))}
    {e : Expr [] (suc (suc n))}
    {U : NfTy [] (KV pk m)}
  → Γ₁ ⊢ e ⇒ U ⊣ Γ₂
  → Γ₁ ⊢ weakenExprBy2 0 e ⇒ U ⊣ Γ₂
weaken-zero-preserves-synth2 =
  rename-pointwise-preserves-synth
    (extRen2 (λ x → x))
    (extRen-pointwise (extRen-pointwise (λ x → refl)))

extRen-rel :
  ∀ {n m} {ρ σ : Ren {n} {m}}
  → (∀ x → ρ x ≡ σ x)
  → ∀ x → extRen ρ x ≡ extRen σ x
extRen-rel rel fzero = refl
extRen-rel rel (fsuc x) = cong fsuc (rel x)

mutual

  rename-cong-value :
    ∀ {Δ : List Kind} {n m}
      {ρ σ : Ren {n} {m}}
    → (∀ x → ρ x ≡ σ x)
    → (v : Value Δ n)
    → renameValue ρ v ≡ renameValue σ v
  rename-cong-value rel (V-Const c) = refl
  rename-cong-value rel (V-Var x) = cong V-Var (rel x)
  rename-cong-value rel (V-Abs T e) =
    cong (V-Abs T) (rename-cong-expr (extRen-rel rel) e)
  rename-cong-value rel (V-Rec T U v) =
    cong (V-Rec T U) (rename-cong-value (extRen-rel rel) v)
  rename-cong-value rel (V-TAbs K v) =
    cong (V-TAbs K) (rename-cong-value rel v)
  rename-cong-value rel (V-Pair left right) =
    cong₂ V-Pair
      (rename-cong-value rel left)
      (rename-cong-value rel right)
  rename-cong-value rel (V-Receive₁ T) = refl
  rename-cong-value rel (V-Receive₂ T S) = refl
  rename-cong-value rel (V-Send₁ T) = refl
  rename-cong-value rel (V-Send₂ T S) = refl
  rename-cong-value rel (V-Select₁ v i P) = refl
  rename-cong-value rel (V-Select₂ v i P S) = refl

  rename-cong-expr :
    ∀ {Δ : List Kind} {n m}
      {ρ σ : Ren {n} {m}}
    → (∀ x → ρ x ≡ σ x)
    → (e : Expr Δ n)
    → renameExpr ρ e ≡ renameExpr σ e
  rename-cong-expr rel (E-Val v) =
    cong E-Val (rename-cong-value rel v)
  rename-cong-expr rel (E-App left right) =
    cong₂ E-App
      (rename-cong-expr rel left)
      (rename-cong-expr rel right)
  rename-cong-expr rel (E-TApp e T) =
    cong (λ e′ → E-TApp e′ T) (rename-cong-expr rel e)
  rename-cong-expr rel (E-LetUnit scrutinee body) =
    cong₂ E-LetUnit
      (rename-cong-expr rel scrutinee)
      (rename-cong-expr rel body)
  rename-cong-expr rel (E-Pair left right) =
    cong₂ E-Pair
      (rename-cong-expr rel left)
      (rename-cong-expr rel right)
  rename-cong-expr rel (E-LetPair scrutinee body) =
    cong₂ E-LetPair
      (rename-cong-expr rel scrutinee)
      (rename-cong-expr
        (extRen-rel (extRen-rel rel))
        body)
  rename-cong-expr rel
      (E-Match {ss = ss} scrutinee ne branches) =
    cong₂
      (λ e′ bs′ → E-Match e′ ne bs′)
      (rename-cong-expr rel scrutinee)
      (dependent-ext₂
        (λ i i∈ →
          rename-cong-expr
            (extRen-rel rel)
            (branches i i∈)))

extRen-compose-pointwise :
  ∀ {n m q}
    (ρ : Ren {n} {m})
    (σ : Ren {m} {q})
  → ∀ x →
      extRen σ (extRen ρ x)
        ≡ extRen (λ y → σ (ρ y)) x
extRen-compose-pointwise ρ σ fzero = refl
extRen-compose-pointwise ρ σ (fsuc x) = refl

extRen2-compose-pointwise :
  ∀ {n m q}
    (ρ : Ren {n} {m})
    (σ : Ren {m} {q})
  → ∀ x →
      extRen2 σ (extRen2 ρ x)
        ≡ extRen2 (λ y → σ (ρ y)) x
extRen2-compose-pointwise ρ σ fzero = refl
extRen2-compose-pointwise ρ σ (fsuc fzero) = refl
extRen2-compose-pointwise ρ σ (fsuc (fsuc x)) = refl

mutual

  rename-compose-value :
    ∀ {Δ : List Kind} {n m q}
      (ρ : Ren {n} {m})
      (σ : Ren {m} {q})
      (v : Value Δ n)
    → renameValue σ (renameValue ρ v)
        ≡ renameValue (λ x → σ (ρ x)) v
  rename-compose-value ρ σ (V-Const c) = refl
  rename-compose-value ρ σ (V-Var x) = refl
  rename-compose-value ρ σ (V-Abs T e) =
    cong (V-Abs T)
      (trans
        (rename-compose-expr (extRen ρ) (extRen σ) e)
        (rename-cong-expr
          (extRen-compose-pointwise ρ σ)
          e))
  rename-compose-value ρ σ (V-Rec T U v) =
    cong (V-Rec T U)
      (trans
        (rename-compose-value (extRen ρ) (extRen σ) v)
        (rename-cong-value
          (extRen-compose-pointwise ρ σ)
          v))
  rename-compose-value ρ σ (V-TAbs K v) =
    cong (V-TAbs K) (rename-compose-value ρ σ v)
  rename-compose-value ρ σ (V-Pair left right) =
    cong₂ V-Pair
      (rename-compose-value ρ σ left)
      (rename-compose-value ρ σ right)
  rename-compose-value ρ σ (V-Receive₁ T) = refl
  rename-compose-value ρ σ (V-Receive₂ T S) = refl
  rename-compose-value ρ σ (V-Send₁ T) = refl
  rename-compose-value ρ σ (V-Send₂ T S) = refl
  rename-compose-value ρ σ (V-Select₁ v i P) = refl
  rename-compose-value ρ σ (V-Select₂ v i P S) = refl

  rename-compose-expr :
    ∀ {Δ : List Kind} {n m q}
      (ρ : Ren {n} {m})
      (σ : Ren {m} {q})
      (e : Expr Δ n)
    → renameExpr σ (renameExpr ρ e)
        ≡ renameExpr (λ x → σ (ρ x)) e
  rename-compose-expr ρ σ (E-Val v) =
    cong E-Val (rename-compose-value ρ σ v)
  rename-compose-expr ρ σ (E-App left right) =
    cong₂ E-App
      (rename-compose-expr ρ σ left)
      (rename-compose-expr ρ σ right)
  rename-compose-expr ρ σ (E-TApp e T) =
    cong (λ e′ → E-TApp e′ T) (rename-compose-expr ρ σ e)
  rename-compose-expr ρ σ (E-LetUnit scrutinee body) =
    cong₂ E-LetUnit
      (rename-compose-expr ρ σ scrutinee)
      (rename-compose-expr ρ σ body)
  rename-compose-expr ρ σ (E-Pair left right) =
    cong₂ E-Pair
      (rename-compose-expr ρ σ left)
      (rename-compose-expr ρ σ right)
  rename-compose-expr ρ σ (E-LetPair scrutinee body) =
    cong₂ E-LetPair
      (rename-compose-expr ρ σ scrutinee)
      (trans
        (rename-compose-expr (extRen2 ρ) (extRen2 σ) body)
        (rename-cong-expr
          (extRen2-compose-pointwise ρ σ)
          body))
  rename-compose-expr ρ σ
      (E-Match {ss = ss} scrutinee ne branches) =
    cong₂
      (λ e′ bs′ → E-Match e′ ne bs′)
      (rename-compose-expr ρ σ scrutinee)
      (dependent-ext₂
        (λ i i∈ →
          trans
            (rename-compose-expr
              (extRen ρ)
              (extRen σ)
              (branches i i∈))
            (rename-cong-expr
              (extRen-compose-pointwise ρ σ)
              (branches i i∈))))

newRen :
  ∀ k {n}
  → Ren {k + n} {k + suc (suc n)}
newRen 0 = shiftRen 2
newRen (suc k) = extRen (newRen k)

liftRen-twice :
  ∀ k {n}
  → (x : Fin (k + n))
  → liftRen k (liftRen k x) ≡ newRen k x
liftRen-twice 0 x = refl
liftRen-twice (suc k) fzero = refl
liftRen-twice (suc k) (fsuc x) = cong fsuc (liftRen-twice k x)

rename-new-value :
  ∀ {Δ : List Kind} k {n}
    (v : Value Δ (k + n))
  → renameValue (liftRen k) (renameValue (liftRen k) v)
      ≡ renameValue (newRen k) v
rename-new-value k v =
  trans
    (rename-compose-value (liftRen k) (liftRen k) v)
    (rename-cong-value (liftRen-twice k) v)

rename-new-expr :
  ∀ {Δ : List Kind} k {n}
    (e : Expr Δ (k + n))
  → renameExpr (liftRen k) (renameExpr (liftRen k) e)
      ≡ renameExpr (newRen k) e
rename-new-expr k e =
  trans
    (rename-compose-expr (liftRen k) (liftRen k) e)
    (rename-cong-expr (liftRen-twice k) e)

new-weaken-value-at :
  ∀ k {n pk m}
    (S : Ty [] SLin)
    {Γ₁ Γ₂ : Ctx [] (k + n)}
    {v : Value [] (k + n)}
    {T : NfTy [] (KV pk m)}
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  → insertAt k (B-Used (normalizeTy S))
      (insertAt k
        (B-Used (normalizeTy (T-Dual Duality.D-S S))) Γ₁)
      ⊢ᵥ renameValue (newRen k) v ⇒ T
      ⊣ insertAt k (B-Used (normalizeTy S))
          (insertAt k
            (B-Used (normalizeTy (T-Dual Duality.D-S S))) Γ₂)
new-weaken-value-at k S {v = v} d =
  subst
    (λ v′ →
      insertAt k (B-Used (normalizeTy S))
        (insertAt k
          (B-Used (normalizeTy (T-Dual Duality.D-S S))) _)
        ⊢ᵥ v′ ⇒ _
        ⊣ insertAt k (B-Used (normalizeTy S))
            (insertAt k
              (B-Used (normalizeTy (T-Dual Duality.D-S S))) _))
    (rename-new-value k v)
    (ren-preserves-value k (B-Used (normalizeTy S))
      (ren-preserves-value k
        (B-Used (normalizeTy (T-Dual Duality.D-S S)))
        d))

new-weaken-synth-at :
  ∀ k {n pk m}
    (S : Ty [] SLin)
    {Γ₁ Γ₂ : Ctx [] (k + n)}
    {e : Expr [] (k + n)}
    {T : NfTy [] (KV pk m)}
  → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
  → insertAt k (B-Used (normalizeTy S))
      (insertAt k
        (B-Used (normalizeTy (T-Dual Duality.D-S S))) Γ₁)
      ⊢ renameExpr (newRen k) e ⇒ T
      ⊣ insertAt k (B-Used (normalizeTy S))
          (insertAt k
            (B-Used (normalizeTy (T-Dual Duality.D-S S))) Γ₂)
new-weaken-synth-at k S {e = e} d =
  subst
    (λ e′ →
      insertAt k (B-Used (normalizeTy S))
        (insertAt k
          (B-Used (normalizeTy (T-Dual Duality.D-S S))) _)
        ⊢ e′ ⇒ _
        ⊣ insertAt k (B-Used (normalizeTy S))
            (insertAt k
              (B-Used (normalizeTy (T-Dual Duality.D-S S))) _))
    (rename-new-expr k e)
    (ren-preserves-synth k (B-Used (normalizeTy S))
      (ren-preserves-synth k
        (B-Used (normalizeTy (T-Dual Duality.D-S S)))
        d))

new-weaken-check-at :
  ∀ k {n pk m}
    (S : Ty [] SLin)
    {Γ₁ Γ₂ : Ctx [] (k + n)}
    {e : Expr [] (k + n)}
    {T : NfTy [] (KV pk m)}
  → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
  → insertAt k (B-Used (normalizeTy S))
      (insertAt k
        (B-Used (normalizeTy (T-Dual Duality.D-S S))) Γ₁)
      ⊢ renameExpr (newRen k) e ⇐ T
      ⊣ insertAt k (B-Used (normalizeTy S))
          (insertAt k
            (B-Used (normalizeTy (T-Dual Duality.D-S S))) Γ₂)
new-weaken-check-at k S {e = e} d =
  subst
    (λ e′ →
      insertAt k (B-Used (normalizeTy S))
        (insertAt k
          (B-Used (normalizeTy (T-Dual Duality.D-S S))) _)
        ⊢ e′ ⇐ _
        ⊣ insertAt k (B-Used (normalizeTy S))
            (insertAt k
              (B-Used (normalizeTy (T-Dual Duality.D-S S))) _))
    (rename-new-expr k e)
    (ren-preserves-check k (B-Used (normalizeTy S))
      (ren-preserves-check k
        (B-Used (normalizeTy (T-Dual Duality.D-S S)))
        d))

weaken-label-value :
  ∀ {n Θ pk m}
    {Γin Γv Γ₁ Γ₂ : Ctx [] n}
    {ℓ : Label n Θ}
    {v : Value [] n}
    {T : NfTy [] (KV pk m)}
  → ℓ ⦂ Γin ⇒ Γv
  → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
  → extendUsed Θ Γ₁
      ⊢ᵥ weakenValueBy (length Θ) v ⇒ T
      ⊣ extendUsed Θ Γ₂
weaken-label-value (Label-β _ _) d = weaken-zero-preserves-value d
weaken-label-value (Label-Fork _ _) d = weaken-zero-preserves-value d
weaken-label-value (Label-New {S = S} _ _) d = new-weaken-value-at 0 S d
weaken-label-value (Label-RecvVal _ _ _ _ _) d = weaken-zero-preserves-value d
weaken-label-value (Label-RecvLab _ _) d = weaken-zero-preserves-value d
weaken-label-value (Label-SendVal _ _ _) d = weaken-zero-preserves-value d
weaken-label-value (Label-SendLab _ _) d = weaken-zero-preserves-value d
weaken-label-value (Label-Close _ _) d = weaken-zero-preserves-value d

weaken-label-synth :
  ∀ {n Θ pk m}
    {Γin Γv Γ₁ Γ₂ : Ctx [] n}
    {ℓ : Label n Θ}
    {e : Expr [] n}
    {T : NfTy [] (KV pk m)}
  → ℓ ⦂ Γin ⇒ Γv
  → Γ₁ ⊢ e ⇒ T ⊣ Γ₂
  → extendUsed Θ Γ₁
      ⊢ weakenExprBy (length Θ) e ⇒ T
      ⊣ extendUsed Θ Γ₂
weaken-label-synth (Label-β _ _) d = weaken-zero-preserves-synth d
weaken-label-synth (Label-Fork _ _) d = weaken-zero-preserves-synth d
weaken-label-synth (Label-New {S = S} _ _) d = new-weaken-synth-at 0 S d
weaken-label-synth (Label-RecvVal _ _ _ _ _) d = weaken-zero-preserves-synth d
weaken-label-synth (Label-RecvLab _ _) d = weaken-zero-preserves-synth d
weaken-label-synth (Label-SendVal _ _ _) d = weaken-zero-preserves-synth d
weaken-label-synth (Label-SendLab _ _) d = weaken-zero-preserves-synth d
weaken-label-synth (Label-Close _ _) d = weaken-zero-preserves-synth d

weaken-label-check :
  ∀ {n Θ pk m}
    {Γin Γv Γ₁ Γ₂ : Ctx [] n}
    {ℓ : Label n Θ}
    {e : Expr [] n}
    {T : NfTy [] (KV pk m)}
  → ℓ ⦂ Γin ⇒ Γv
  → Γ₁ ⊢ e ⇐ T ⊣ Γ₂
  → extendUsed Θ Γ₁
      ⊢ weakenExprBy (length Θ) e ⇐ T
      ⊣ extendUsed Θ Γ₂
weaken-label-check (Label-β _ _) d = weaken-zero-preserves-check d
weaken-label-check (Label-Fork _ _) d = weaken-zero-preserves-check d
weaken-label-check (Label-New {S = S} _ _) d = new-weaken-check-at 0 S d
weaken-label-check (Label-RecvVal _ _ _ _ _) d = weaken-zero-preserves-check d
weaken-label-check (Label-RecvLab _ _) d = weaken-zero-preserves-check d
weaken-label-check (Label-SendVal _ _ _) d = weaken-zero-preserves-check d
weaken-label-check (Label-SendLab _ _) d = weaken-zero-preserves-check d
weaken-label-check (Label-Close _ _) d = weaken-zero-preserves-check d

weaken-label-synth1 :
  ∀ {n Θ pkT pkU pk m}
    {Γin Γv Γ₁ Γ₂ : Ctx [] n}
    {ℓ : Label n Θ}
    {T : NfTy [] (KV pkT Lin)}
    {U : NfTy [] (KV pkU Lin)}
    {e : Expr [] (suc n)}
    {V : NfTy [] (KV pk m)}
  → ℓ ⦂ Γin ⇒ Γv
  → (T ∷ˡ Γ₁) ⊢ e ⇒ V ⊣ (B-Used U ▻ Γ₂)
  → (T ∷ˡ extendUsed Θ Γ₁)
      ⊢ weakenExprBy1 (length Θ) e ⇒ V
      ⊣ (B-Used U ▻ extendUsed Θ Γ₂)
weaken-label-synth1 (Label-β _ _) d = weaken-zero-preserves-synth1 d
weaken-label-synth1 (Label-Fork _ _) d = weaken-zero-preserves-synth1 d
weaken-label-synth1 (Label-New {S = S} _ _) d = new-weaken-synth-at 1 S d
weaken-label-synth1 (Label-RecvVal _ _ _ _ _) d = weaken-zero-preserves-synth1 d
weaken-label-synth1 (Label-RecvLab _ _) d = weaken-zero-preserves-synth1 d
weaken-label-synth1 (Label-SendVal _ _ _) d = weaken-zero-preserves-synth1 d
weaken-label-synth1 (Label-SendLab _ _) d = weaken-zero-preserves-synth1 d
weaken-label-synth1 (Label-Close _ _) d = weaken-zero-preserves-synth1 d

weaken-label-synth2 :
  ∀ {n Θ pkT pkU pk m}
    {Γin Γv Γ₁ Γ₂ : Ctx [] n}
    {ℓ : Label n Θ}
    {T : NfTy [] (KV pkT Lin)}
    {U : NfTy [] (KV pkU Lin)}
    {e : Expr [] (suc (suc n))}
    {V : NfTy [] (KV pk m)}
  → ℓ ⦂ Γin ⇒ Γv
  → (T ∷ˡ (U ∷ˡ Γ₁)) ⊢ e ⇒ V
      ⊣ (B-Used T ▻ (B-Used U ▻ Γ₂))
  → (T ∷ˡ (U ∷ˡ extendUsed Θ Γ₁))
      ⊢ weakenExprBy2 (length Θ) e ⇒ V
      ⊣ (B-Used T ▻ (B-Used U ▻ extendUsed Θ Γ₂))
weaken-label-synth2 (Label-β _ _) d = weaken-zero-preserves-synth2 d
weaken-label-synth2 (Label-Fork _ _) d = weaken-zero-preserves-synth2 d
weaken-label-synth2 (Label-New {S = S} _ _) d = new-weaken-synth-at 2 S d
weaken-label-synth2 (Label-RecvVal _ _ _ _ _) d = weaken-zero-preserves-synth2 d
weaken-label-synth2 (Label-RecvLab _ _) d = weaken-zero-preserves-synth2 d
weaken-label-synth2 (Label-SendVal _ _ _) d = weaken-zero-preserves-synth2 d
weaken-label-synth2 (Label-SendLab _ _) d = weaken-zero-preserves-synth2 d
weaken-label-synth2 (Label-Close _ _) d = weaken-zero-preserves-synth2 d

frame-update-value-aligned :
  ∀ {n Θ pk m}
    {Γactive Γ Γ′ : Ctx [] n}
    {Γactive′ Γstep : Ctx [] (length Θ + n)}
    {v : Value [] n} {T : NfTy [] (KV pk m)} {ℓ : Label n Θ}
  → (ctx : Γactive —ctx[ ℓ ]→ Γactive′)
  → (frm : Γ —frm[ ℓ ]→ Γstep)
  → ctx-effect ctx ≡ frm-effect frm
  → LinearDisjoint Γactive Γ
  → Γ ⊢ᵥ v ⇒ T ⊣ Γ′
  → AllUsed Γ′
  → Σ (Ctx [] (length Θ + n)) λ Γstep′ →
      (Γ′ —frm[ ℓ ]→ Γstep′) ×
      AllUsed Γstep′ ×
      (Γstep ⊢ᵥ weakenValueBy (length Θ) v ⇒ T ⊣ Γstep′)
frame-update-value-aligned Ctx-β Frm-β refl _ dv au =
  _ , Frm-β , au , weaken-zero-preserves-value dv
frame-update-value-aligned
    (Ctx-Fork _ _ _) Frm-Fork refl _ dv au =
  _ , Frm-Fork , au , weaken-zero-preserves-value dv
frame-update-value-aligned
    (Ctx-New {S = S}) Frm-New refl _ dv au =
  _ , Frm-New , AU-used (AU-used au) , new-weaken-value-at 0 S dv
frame-update-value-aligned
    (Ctx-Rcv {x = x} dvₚ auₚ ldₚ x∈ repₐ repₚ merge)
    (Frm-Rcv rep) _ ld dv au
  with replace-used-retagged x∈ ld rep (value-preserves-~Ctx dv)
... | Γstep′ , rep′ , tr =
  Γstep′ , Frm-Rcv rep′ ,
  allUsed-resp-≈ᵘ (retagged-output tr) au ,
  weaken-zero-preserves-value (retag-value dv tr)
frame-update-value-aligned
    (Ctx-Send {x = x} rm dvₚ auₚ x∈ repₐ)
    (Frm-Send rep) _ ld dv au
  with replace-used-retagged
         (remove-membership rm x∈) ld rep (value-preserves-~Ctx dv)
... | Γstep′ , rep′ , tr =
  Γstep′ , Frm-Send rep′ ,
  allUsed-resp-≈ᵘ (retagged-output tr) au ,
  weaken-zero-preserves-value (retag-value dv tr)
frame-update-value-aligned
    (Ctx-Close {x = x} x∈ repₐ)
    (Frm-Close rep) _ ld dv au
  with replace-used-retagged x∈ ld rep (value-preserves-~Ctx dv)
... | Γstep′ , rep′ , tr =
  Γstep′ , Frm-Close rep′ ,
  allUsed-resp-≈ᵘ (retagged-output tr) au ,
  weaken-zero-preserves-value (retag-value dv tr)
frame-update-value-aligned
    (Ctx-Match {x = x} i∈ x∈ repₐ)
    (Frm-Match j∈ rep) _ ld dv au
  with replace-used-retagged x∈ ld rep (value-preserves-~Ctx dv)
... | Γstep′ , rep′ , tr =
  Γstep′ , Frm-Match j∈ rep′ ,
  allUsed-resp-≈ᵘ (retagged-output tr) au ,
  weaken-zero-preserves-value (retag-value dv tr)
frame-update-value-aligned
    (Ctx-Select {x = x} x∈ repₐ)
    (Frm-Select rep) _ ld dv au
  with replace-used-retagged x∈ ld rep (value-preserves-~Ctx dv)
... | Γstep′ , rep′ , tr =
  Γstep′ , Frm-Select rep′ ,
  allUsed-resp-≈ᵘ (retagged-output tr) au ,
  weaken-zero-preserves-value (retag-value dv tr)

replace-both-used-disjoint :
  ∀ {Δ n pk}
    {Γ₀ Γf Γ₀′ Γf′ : Ctx Δ n}
    {x : Fin n} {U : NfTy Δ (KV pk Lin)}
  → LinearDisjoint Γ₀ Γf
  → ReplaceAt Γ₀ x (B-Used U) Γ₀′
  → ReplaceAt Γf x (B-Used U) Γf′
  → LinearDisjoint Γ₀′ Γf′
replace-both-used-disjoint (LD-used-used ld) R-here R-here =
  LD-used-used ld
replace-both-used-disjoint (LD-used-live ld) R-here R-here =
  LD-used-used ld
replace-both-used-disjoint (LD-live-used ld) R-here R-here =
  LD-used-used ld
replace-both-used-disjoint (LD-un-un ld) R-here R-here =
  LD-used-used ld
replace-both-used-disjoint (LD-used-used ld) (R-there rep₀) (R-there repf) =
  LD-used-used (replace-both-used-disjoint ld rep₀ repf)
replace-both-used-disjoint (LD-used-live ld) (R-there rep₀) (R-there repf) =
  LD-used-live (replace-both-used-disjoint ld rep₀ repf)
replace-both-used-disjoint (LD-live-used ld) (R-there rep₀) (R-there repf) =
  LD-live-used (replace-both-used-disjoint ld rep₀ repf)
replace-both-used-disjoint (LD-un-un ld) (R-there rep₀) (R-there repf) =
  LD-un-un (replace-both-used-disjoint ld rep₀ repf)

frame-updates-preserve-disjoint :
  ∀ {n Θ} {Γ₀ Γf : Ctx [] n}
    {Γ₀′ Γf′ : Ctx [] (length Θ + n)} {ℓ : Label n Θ}
  → (frm₀ : Γ₀ —frm[ ℓ ]→ Γ₀′)
  → (frmf : Γf —frm[ ℓ ]→ Γf′)
  → frm-effect frm₀ ≡ frm-effect frmf
  → LinearDisjoint Γ₀ Γf
  → LinearDisjoint Γ₀′ Γf′
frame-updates-preserve-disjoint Frm-β Frm-β refl ld = ld
frame-updates-preserve-disjoint Frm-New Frm-New refl ld =
  LD-used-used (LD-used-used ld)
frame-updates-preserve-disjoint Frm-Fork Frm-Fork refl ld = ld
frame-updates-preserve-disjoint
    (Frm-Rcv rep₀) (Frm-Rcv repf) refl ld =
  replace-both-used-disjoint ld rep₀ repf
frame-updates-preserve-disjoint
    (Frm-Send rep₀) (Frm-Send repf) refl ld =
  replace-both-used-disjoint ld rep₀ repf
frame-updates-preserve-disjoint
    (Frm-Close rep₀) (Frm-Close repf) refl ld =
  replace-both-used-disjoint ld rep₀ repf
frame-updates-preserve-disjoint
    {Γf = Γf} {Γf′ = Γf′}
    (Frm-Match {x = x} _ rep₀) (Frm-Match _ repf) eq ld
  with effect-replace-binding-injective {x = x} eq
... | bindingEq =
  replace-both-used-disjoint
    ld
    rep₀
    (subst (λ b → ReplaceAt Γf x b Γf′) (sym bindingEq) repf)
frame-updates-preserve-disjoint
    {Γf = Γf} {Γf′ = Γf′}
    (Frm-Select {x = x} rep₀) (Frm-Select repf) eq ld
  with effect-replace-binding-injective {x = x} eq
... | bindingEq =
  replace-both-used-disjoint
    ld
    rep₀
    (subst (λ b → ReplaceAt Γf x b Γf′) (sym bindingEq) repf)

frame-replace-used-same :
  ∀ {Δ n pk}
    {Γa Γb Γab Γa′ Γb′ Γab′ : Ctx Δ n}
    {x : Fin n} {U : NfTy Δ (KV pk Lin)}
  → FrameCtx Γa Γb Γab
  → ReplaceAt Γa x (B-Used U) Γa′
  → ReplaceAt Γb x (B-Used U) Γb′
  → FrameCtx Γa′ Γb′ Γab′
  → ReplaceAt Γab x (B-Used U) Γab′
frame-replace-used-same (FC-allused f) R-here R-here (FC-allused f′)
  rewrite frame-unique f f′ = R-here
frame-replace-used-same (FC-live f) R-here R-here (FC-allused f′)
  rewrite frame-unique f f′ = R-here
frame-replace-used-same (FC-frame f) R-here R-here (FC-allused f′)
  rewrite frame-unique f f′ = R-here
frame-replace-used-same (FC-un f) R-here R-here (FC-allused f′)
  rewrite frame-unique f f′ = R-here
frame-replace-used-same (FC-allused f) (R-there repa) (R-there repb)
    (FC-allused f′) =
  R-there (frame-replace-used-same f repa repb f′)
frame-replace-used-same (FC-live f) (R-there repa) (R-there repb)
    (FC-live f′) =
  R-there (frame-replace-used-same f repa repb f′)
frame-replace-used-same (FC-frame f) (R-there repa) (R-there repb)
    (FC-frame f′) =
  R-there (frame-replace-used-same f repa repb f′)
frame-replace-used-same (FC-un f) (R-there repa) (R-there repb)
    (FC-un f′) =
  R-there (frame-replace-used-same f repa repb f′)

frame-update-merge-aligned :
  ∀ {n Θ} {ℓ : Label n Θ}
    {Γa Γb Γab : Ctx [] n}
    {Γa′ Γb′ Γab′ : Ctx [] (length Θ + n)}
  → FrameCtx Γa Γb Γab
  → (frma : Γa —frm[ ℓ ]→ Γa′)
  → (frmb : Γb —frm[ ℓ ]→ Γb′)
  → frm-effect frma ≡ frm-effect frmb
  → FrameCtx Γa′ Γb′ Γab′
  → Σ (Γab —frm[ ℓ ]→ Γab′) λ merged →
      frm-effect merged ≡ frm-effect frma
frame-update-merge-aligned f Frm-β Frm-β refl f′
  rewrite frame-unique f f′ = Frm-β , refl
frame-update-merge-aligned {ℓ = L-New S} {Γab = Γab}
    f Frm-New Frm-New refl f′ =
  let
    merged =
      subst
        (λ Γout → Γab —frm[ L-New S ]→ Γout)
        (frame-unique (FC-allused (FC-allused f)) f′)
        Frm-New
  in
  merged , new-effect merged
  where
  new-effect :
    ∀ {n} {S : Types.Ty [] SLin} {Γ : Ctx [] n}
      {Γ′ : Ctx [] (suc (suc n))}
    → (frm : Γ —frm[ L-New S ]→ Γ′)
    → frm-effect frm ≡ Effect-new
  new-effect Frm-New = refl
frame-update-merge-aligned f Frm-Fork Frm-Fork refl f′
  rewrite frame-unique f f′ = Frm-Fork , refl
frame-update-merge-aligned f (Frm-Rcv repa) (Frm-Rcv repb) refl f′ =
  Frm-Rcv (frame-replace-used-same f repa repb f′) , refl
frame-update-merge-aligned f (Frm-Send repa) (Frm-Send repb) refl f′ =
  Frm-Send (frame-replace-used-same f repa repb f′) , refl
frame-update-merge-aligned f (Frm-Close repa) (Frm-Close repb) refl f′ =
  Frm-Close (frame-replace-used-same f repa repb f′) , refl
frame-update-merge-aligned
    {Γb = Γb} {Γb′ = Γb′}
    f (Frm-Match {x = x} i∈ repa) (Frm-Match _ repb) eq f′
  with effect-replace-binding-injective {x = x} eq
... | bindingEq =
  ( Frm-Match i∈
      (frame-replace-used-same
        f
        repa
        (subst (λ b → ReplaceAt Γb x b Γb′) (sym bindingEq) repb)
        f′)
  , refl
  )
frame-update-merge-aligned
    {Γb = Γb} {Γb′ = Γb′}
    f (Frm-Select {x = x} repa) (Frm-Select repb) eq f′
  with effect-replace-binding-injective {x = x} eq
... | bindingEq =
  ( Frm-Select
      (frame-replace-used-same
        f
        repa
        (subst (λ b → ReplaceAt Γb x b Γb′) (sym bindingEq) repb)
        f′)
  , refl
  )

remove-allused-disjoint2 :
  ∀ {n} {Γ₀ Γ₂ Γr G H : Ctx [] n}
  → RemoveCtx Γ₀ G Γ₂
  → RemoveCtx Γ₀ H Γr
  → AllUsed H
  → LinearDisjoint G H
remove-allused-disjoint2 RM-∅ RM-∅ AU-∅ = LD-∅
remove-allused-disjoint2 (RM-drop r₁) (RM-drop r₂) (AU-used au) =
  LD-used-used (remove-allused-disjoint2 r₁ r₂ au)
remove-allused-disjoint2 (RM-lin r₁) (RM-drop r₂) (AU-used au) =
  LD-live-used (remove-allused-disjoint2 r₁ r₂ au)
remove-allused-disjoint2 (RM-allused r₁) (RM-allused r₂) (AU-used au) =
  LD-used-used (remove-allused-disjoint2 r₁ r₂ au)
remove-allused-disjoint2 (RM-un r₁) (RM-un r₂) (AU-un au) =
  LD-un-un (remove-allused-disjoint2 r₁ r₂ au)

recv-input-disjoint-core :
  ∀ {n pk pk′}
    {Γ₀ Γ₂ Γin Γr Γin′ G : Ctx [] n}
    {x : Fin n}
    {T : NfTy [] (KV pk Lin)} {U : NfTy [] (KV pk′ Lin)}
  → RemoveCtx Γ₀ G Γ₂
  → RemoveCtx Γ₀ Γin Γr
  → Γin ⊢ˡ x ∶ T ⊣ Γin′
  → AllUsed Γin′
  → Γ₂ ∋ˡ x ∶ U
  → LinearDisjoint G Γin
recv-input-disjoint-core {x = fzero}
    (RM-drop r) (RM-lin rin) take-here (AU-used au) hereˡ =
  LD-used-live (remove-allused-disjoint2 r rin au)
recv-input-disjoint-core {x = fsuc x}
    (RM-drop r) (RM-drop rin) (take-there✖ take) (AU-used au)
    (thereˡˡ x∈) =
  LD-used-used (recv-input-disjoint-core {x = x} r rin take au x∈)
recv-input-disjoint-core {x = fsuc x}
    (RM-un r) (RM-un rin) (take-thereᵘ take) (AU-un au)
    (thereˡᵘ x∈) =
  LD-un-un (recv-input-disjoint-core {x = x} r rin take au x∈)
recv-input-disjoint-core {x = fsuc x}
    (RM-lin r) (RM-drop rin) (take-there✖ take) (AU-used au)
    (thereˡ✖ x∈) =
  LD-live-used (recv-input-disjoint-core {x = x} r rin take au x∈)
recv-input-disjoint-core {x = fsuc x}
    (RM-allused r) (RM-allused rin) (take-there✖ take) (AU-used au)
    (thereˡ✖ x∈) =
  LD-used-used (recv-input-disjoint-core {x = x} r rin take au x∈)

recv-extract-disjoint :
  ∀ {n pk} {Γ₀ Γ₂ Γin G : Ctx [] n}
    {x : Fin n} {v : Value [] n} {U : NfTy [] (KV pk Lin)}
  → RemoveCtx Γ₀ G Γ₂
  → Extract Γ₀ (L-RecvVal x v) Γin
  → Γ₂ ∋ˡ x ∶ U
  → LinearDisjoint G Γin
recv-extract-disjoint r (Ex-RecvVal rin take au) x∈ =
  recv-input-disjoint-core r rin take au x∈

send-input-disjoint-core :
  ∀ {n pk pkT} {Γ₀ Γ₂ Γin Γr Γv G : Ctx [] n}
    {x : Fin n} {T : NfTy [] (KV pkT Lin)} {S : NfTy [] SLin}
    {U : NfTy [] (KV pk Lin)}
  → RemoveCtx Γ₀ G Γ₂
  → RemoveCtx Γ₀ Γin Γr
  → Γin ⊢ˡ x ∶ sendChanNf T S ⊣ Γv
  → Γ₂ ∋ˡ x ∶ U
  → LinearDisjoint G Γv
  → LinearDisjoint G Γin
send-input-disjoint-core {x = fzero}
    (RM-drop r) (RM-lin rin) take-here hereˡ (LD-used-used ldv) =
  LD-used-live ldv
send-input-disjoint-core {x = fsuc x}
    (RM-drop r) (RM-lin rin) (take-thereˡ take)
    (thereˡˡ x∈) (LD-used-live ldv) =
  LD-used-live (send-input-disjoint-core {x = x} r rin take x∈ ldv)
send-input-disjoint-core {x = fsuc x}
    (RM-un r) (RM-un rin) (take-thereᵘ take)
    (thereˡᵘ x∈) (LD-un-un ldv) =
  LD-un-un (send-input-disjoint-core {x = x} r rin take x∈ ldv)
send-input-disjoint-core {x = fsuc x}
    (RM-drop r) (RM-drop rin) (take-there✖ take)
    (thereˡˡ x∈) (LD-used-used ldv) =
  LD-used-used (send-input-disjoint-core {x = x} r rin take x∈ ldv)
send-input-disjoint-core {x = fsuc x}
    (RM-lin r) (RM-drop rin) (take-there✖ take)
    (thereˡ✖ x∈) (LD-live-used ldv) =
  LD-live-used (send-input-disjoint-core {x = x} r rin take x∈ ldv)
send-input-disjoint-core {x = fsuc x}
    (RM-allused r) (RM-allused rin) (take-there✖ take)
    (thereˡ✖ x∈) (LD-used-used ldv) =
  LD-used-used (send-input-disjoint-core {x = x} r rin take x∈ ldv)

send-extract-disjoint :
  ∀ {n pk} {Γ₀ Γ₂ Γin Γv G : Ctx [] n}
    {x : Fin n} {w : Value [] n} {U : NfTy [] (KV pk Lin)}
  → RemoveCtx Γ₀ G Γ₂
  → LinearDisjoint Γ₀ Γv
  → L-SendVal x w ⦂ Γin ⇒ Γv
  → Extract Γ₀ (L-SendVal x w) Γin
  → Γ₂ ∋ˡ x ∶ U
  → LinearDisjoint G Γin
send-extract-disjoint r disj
    (Label-SendVal take dv au) (Ex-SendVal rin _ _ _) x∈ =
  send-input-disjoint-core
    r rin take x∈ (remove-removed-disjoint r disj)

mutual

  recv-live-synth-removed :
    ∀ {n pk mult} {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {v : Value [] n} {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇒ T ⊣ Γ₃
    → e₁ —[ L-RecvVal x v ]→ e₂
    → Extract Γ₀ (L-RecvVal x v) Γin
    → Σ PreKind λ pk′ →
        Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U

  recv-live-synth-removed r
      (T-App {m = Un} (T-Val ()) (T-Check (T-Val vv) sub))
      Act-Rcv (Ex-RecvVal rin take au)

  recv-live-synth-removed r
      (T-App {m = Lin} (T-Val vr) (T-Check (T-Val vv) sub))
      Act-Rcv (Ex-RecvVal rin take au)
    with vr
  ... | TV-Receive₂
    with extract-membership rin (take-membership-fresh take)
  ... | x∈₀
    with vv
  ... | TV-Var-Lin {pk = pk′} {T = U} take₂ =
    pk′ , U , take-membership-fresh take₂

  recv-live-synth-removed r (T-App d₁ d₂) (Act-AppL step) ex =
    recv-live-synth-removed r d₁ step ex
  recv-live-synth-removed r (T-App (T-Val dv) d₂) (Act-AppR step) ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with recv-live-check-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈
  recv-live-synth-removed r (T-TApp d) (Act-TAppE step) ex =
    recv-live-synth-removed r d step ex
  recv-live-synth-removed r (T-Pair d₁ d₂) (Act-PairL step) ex =
    recv-live-synth-removed r d₁ step ex
  recv-live-synth-removed r (T-Pair (T-Val dv) d₂) (Act-PairR step) ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with recv-live-synth-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈
  recv-live-synth-removed r (T-Match d bs bj) (Act-MatchE step) ex =
    recv-live-synth-removed r d step ex
  recv-live-synth-removed r (T-LetPair d body) (Act-LetPairE step) ex =
    recv-live-synth-removed r d step ex
  recv-live-synth-removed r (T-LetUnit d₁ d₂) (Act-LetUnitE step) ex =
    recv-live-check-removed r d₁ step ex

  recv-live-check-removed :
    ∀ {n pk mult} {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {v : Value [] n} {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇐ T ⊣ Γ₃
    → e₁ —[ L-RecvVal x v ]→ e₂
    → Extract Γ₀ (L-RecvVal x v) Γin
    → Σ PreKind λ pk′ →
        Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U
  recv-live-check-removed r (T-Check d sub) step ex =
    recv-live-synth-removed r d step ex

  send-live-synth-removed :
    ∀ {n pk mult} {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {w : Value [] n} {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇒ T ⊣ Γ₃
    → e₁ —[ L-SendVal x w ]→ e₂
    → Extract Γ₀ (L-SendVal x w) Γin
    → Σ PreKind λ pk′ →
        Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U

  send-live-synth-removed r
      (T-App (T-Val vr) (T-Check (T-Val vv) sub))
      Act-Send ex@(Ex-SendVal rin take dv au)
    with extract-membership rin (take-membership-fresh take)
  ... | x∈₀
    with strip-value vr
  ... | Gv , Gv′ , rv , vr′ , auv
    with vv
  ... | TV-Pair dvw (TV-Var-Lin {pk = pk′} {T = U} take₂)
    with strip-value dvw
  ... | Gw , Gw′ , rw , dw′ , auw =
    pk′ , U ,
    remove-membership rv
      (remove-membership rw (take-membership-fresh take₂))

  send-live-synth-removed r (T-App d₁ d₂) (Act-AppL step) ex =
    send-live-synth-removed r d₁ step ex
  send-live-synth-removed r (T-App (T-Val dv) d₂) (Act-AppR step) ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with send-live-check-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈
  send-live-synth-removed r (T-TApp d) (Act-TAppE step) ex =
    send-live-synth-removed r d step ex
  send-live-synth-removed r (T-Pair d₁ d₂) (Act-PairL step) ex =
    send-live-synth-removed r d₁ step ex
  send-live-synth-removed r (T-Pair (T-Val dv) d₂) (Act-PairR step) ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with send-live-synth-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈
  send-live-synth-removed r (T-Match d bs bj) (Act-MatchE step) ex =
    send-live-synth-removed r d step ex
  send-live-synth-removed r (T-LetPair d body) (Act-LetPairE step) ex =
    send-live-synth-removed r d step ex
  send-live-synth-removed r (T-LetUnit d₁ d₂) (Act-LetUnitE step) ex =
    send-live-check-removed r d₁ step ex

  send-live-check-removed :
    ∀ {n pk mult} {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {w : Value [] n} {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇐ T ⊣ Γ₃
    → e₁ —[ L-SendVal x w ]→ e₂
    → Extract Γ₀ (L-SendVal x w) Γin
    → Σ PreKind λ pk′ →
        Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U
  send-live-check-removed r (T-Check d sub) step ex =
    send-live-synth-removed r d step ex

  select-live-synth-removed :
    ∀ {n k pk mult} {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {i : Fin k} {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇒ T ⊣ Γ₃
    → e₁ —[ L-SendLab x i ]→ e₂
    → Extract Γ₀ (L-SendLab x i) Γin
    → Σ PreKind λ pk′ →
        Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U

  select-live-synth-removed r
      (T-App (T-Val vr) (T-Check (T-Val vv) sub))
      Act-Sel (Ex-SendLab rin take)
    with extract-membership rin (take-membership-fresh take)
  ... | x∈₀
    with strip-value vr
  ... | Gv , Gv′ , rv , vr′ , auv
    with vv
  ... | TV-Var-Lin {pk = pk′} {T = U} take₂ =
    pk′ , U , remove-membership rv (take-membership-fresh take₂)

  select-live-synth-removed r (T-App d₁ d₂) (Act-AppL step) ex =
    select-live-synth-removed r d₁ step ex
  select-live-synth-removed r (T-App (T-Val dv) d₂) (Act-AppR step) ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with select-live-check-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈
  select-live-synth-removed r (T-TApp d) (Act-TAppE step) ex =
    select-live-synth-removed r d step ex
  select-live-synth-removed r (T-Pair d₁ d₂) (Act-PairL step) ex =
    select-live-synth-removed r d₁ step ex
  select-live-synth-removed r (T-Pair (T-Val dv) d₂) (Act-PairR step) ex
    with strip-value dv
  ... | Gv , Gv′ , rv , dv′ , au
    with mergeRemoveContext r rv
  ... | Gm , mv , rm
    with select-live-synth-removed rm d₂ step ex
  ... | K , U , x∈ = K , U , remove-membership rv x∈
  select-live-synth-removed r (T-Match d bs bj) (Act-MatchE step) ex =
    select-live-synth-removed r d step ex
  select-live-synth-removed r (T-LetPair d body) (Act-LetPairE step) ex =
    select-live-synth-removed r d step ex
  select-live-synth-removed r (T-LetUnit d₁ d₂) (Act-LetUnitE step) ex =
    select-live-check-removed r d₁ step ex

  select-live-check-removed :
    ∀ {n k pk mult} {Γ₀ G Γ₂ Γ₃ Γin : Ctx [] n}
      {x : Fin n} {i : Fin k} {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk mult)}
    → RemoveCtx Γ₀ G Γ₂
    → Γ₂ ⊢ e₁ ⇐ T ⊣ Γ₃
    → e₁ —[ L-SendLab x i ]→ e₂
    → Extract Γ₀ (L-SendLab x i) Γin
    → Σ PreKind λ pk′ →
        Σ (NfTy [] (KV pk′ Lin)) λ U → Γ₂ ∋ˡ x ∶ U
  select-live-check-removed r (T-Check d sub) step ex =
    select-live-synth-removed r d step ex

right-check-extract-disjoint :
  ∀ {n Θ pk m} {Γ₀ G Γ₂ Γ₃ Γin Γv : Ctx [] n}
    {e₁ : Expr [] n} {e₂ : Expr [] (length Θ + n)}
    {T : NfTy [] (KV pk m)} {ℓ : Label n Θ}
  → RemoveCtx Γ₀ G Γ₂
  → Γ₂ ⊢ e₁ ⇐ T ⊣ Γ₃
  → e₁ —[ ℓ ]→ e₂
  → (lbl : ℓ ⦂ Γin ⇒ Γv)
  → (ex : Extract Γ₀ ℓ Γin)
  → LinearDisjoint Γ₀ Γv
  → LinearDisjoint G Γin
right-check-extract-disjoint r d step lbl Ex-β disj =
  remove-allused-disjoint r
right-check-extract-disjoint r d step lbl Ex-Fork disj =
  remove-allused-disjoint r
right-check-extract-disjoint r d step lbl Ex-New disj =
  remove-allused-disjoint r
right-check-extract-disjoint r d step lbl Ex-RecvLab disj =
  remove-allused-disjoint r
right-check-extract-disjoint r d step lbl Ex-Close disj =
  remove-allused-disjoint r
right-check-extract-disjoint r d step lbl ex@(Ex-RecvVal _ _ _) disj
  with recv-live-check-removed r d step ex
... | K , U , x∈ = recv-extract-disjoint r ex x∈
right-check-extract-disjoint r d step lbl@(Label-SendVal _ _ _)
    ex@(Ex-SendVal _ _ _ _) disj
  with send-live-check-removed r d step ex
... | K , U , x∈ = send-extract-disjoint r disj lbl ex x∈
right-check-extract-disjoint r d step
    (Label-SendLab {v = v} {P = P} {S = S} take au)
    ex@(Ex-SendLab rin _) disj
  with select-live-check-removed r d step ex
... | K , U , x∈ = recv-input-disjoint-core r rin take au x∈

right-synth-extract-disjoint :
  ∀ {n Θ pk m} {Γ₀ G Γ₂ Γ₃ Γin Γv : Ctx [] n}
    {e₁ : Expr [] n} {e₂ : Expr [] (length Θ + n)}
    {T : NfTy [] (KV pk m)} {ℓ : Label n Θ}
  → RemoveCtx Γ₀ G Γ₂
  → Γ₂ ⊢ e₁ ⇒ T ⊣ Γ₃
  → e₁ —[ ℓ ]→ e₂
  → (lbl : ℓ ⦂ Γin ⇒ Γv)
  → (ex : Extract Γ₀ ℓ Γin)
  → LinearDisjoint Γ₀ Γv
  → LinearDisjoint G Γin
right-synth-extract-disjoint r d step lbl Ex-β disj =
  remove-allused-disjoint r
right-synth-extract-disjoint r d step lbl Ex-Fork disj =
  remove-allused-disjoint r
right-synth-extract-disjoint r d step lbl Ex-New disj =
  remove-allused-disjoint r
right-synth-extract-disjoint r d step lbl Ex-RecvLab disj =
  remove-allused-disjoint r
right-synth-extract-disjoint r d step lbl Ex-Close disj =
  remove-allused-disjoint r
right-synth-extract-disjoint r d step lbl ex@(Ex-RecvVal _ _ _) disj
  with recv-live-synth-removed r d step ex
... | K , U , x∈ = recv-extract-disjoint r ex x∈
right-synth-extract-disjoint r d step lbl@(Label-SendVal _ _ _)
    ex@(Ex-SendVal _ _ _ _) disj
  with send-live-synth-removed r d step ex
... | K , U , x∈ = send-extract-disjoint r disj lbl ex x∈
right-synth-extract-disjoint r d step
    (Label-SendLab {v = v} {P = P} {S = S} take au)
    ex@(Ex-SendLab rin _) disj
  with select-live-synth-removed r d step ex
... | K , U , x∈ = recv-input-disjoint-core r rin take au x∈

remove-extract-fresh :
  ∀ {n Θ} {Γ₀ Γ₂ Γin G : Ctx [] n} {ℓ : Label n Θ}
  → RemoveCtx Γ₀ G Γ₂
  → LinearDisjoint G Γin
  → Extract Γ₀ ℓ Γin
  → Extract Γ₂ ℓ Γin
remove-extract-fresh {Γ₂ = Γ₂} r ld Ex-β =
  subst (λ X → Extract Γ₂ L-β X) (sym (allUsedCtx-remove r)) Ex-β
remove-extract-fresh {Γ₂ = Γ₂} r ld Ex-Fork =
  subst (λ X → Extract Γ₂ (L-Fork _) X)
    (sym (allUsedCtx-remove r)) Ex-Fork
remove-extract-fresh {Γ₂ = Γ₂} r ld Ex-New =
  subst (λ X → Extract Γ₂ (L-New _) X)
    (sym (allUsedCtx-remove r)) Ex-New
remove-extract-fresh r ld (Ex-RecvVal rin take au)
  with remove-preserves-remove r rin ld
... | Γr′ , rin′ = Ex-RecvVal rin′ take au
remove-extract-fresh {Γ₂ = Γ₂} r ld Ex-RecvLab =
  subst (λ X → Extract Γ₂ (L-RecvLab _ _) X)
    (sym (allUsedCtx-remove r)) Ex-RecvLab
remove-extract-fresh r ld (Ex-SendVal rin take dv au)
  with remove-preserves-remove r rin ld
... | Γr′ , rin′ = Ex-SendVal rin′ take dv au
remove-extract-fresh r ld (Ex-SendLab rin take)
  with remove-preserves-remove r rin ld
... | Γr′ , rin′ = Ex-SendLab rin′ take
remove-extract-fresh {Γ₂ = Γ₂} r ld Ex-Close =
  subst (λ X → Extract Γ₂ (L-Close _) X)
    (sym (allUsedCtx-remove r)) Ex-Close

receive₂-instantiation :
  ∀ {pk}
    (T : NfTy [] (KV pk Lin))
    (S : NfTy [] SLin)
  → substNFTy
      (receiveNf
        (wkNfTy {K′ = SLin} T)
        (N-Var (NV-Var (here refl))))
      S
      ≡ receiveNf T S
receive₂-instantiation T S =
  trans
    (subst-receive2
      (singleNFSub S)
      (wkNfTy T)
      (N-Var (NV-Var (here refl))))
    (cong₂ receiveNf (cancel-single-wk-ty S T) refl)

send₂-instantiation :
  ∀ {pk}
    (T : NfTy [] (KV pk Lin))
    (S : NfTy [] SLin)
  → substNFTy
      (sendNf
        (wkNfTy {K′ = SLin} T)
        (N-Var (NV-Var (here refl))))
      S
      ≡ sendNf T S
send₂-instantiation T S =
  trans
    (subst-send2
      (singleNFSub S)
      (wkNfTy T)
      (N-Var (NV-Var (here refl))))
    (cong₂ sendNf (cancel-single-wk-ty S T) refl)

select₂-instantiation :
  ∀ {k}
    (v : Variance)
    (i : Fin k)
    (P : NfTy [] KP)
    (S : NfTy [] SLin)
  → substNFTy
      (selectNf v i
        (wkNfTy {K′ = SLin} P)
        (N-Var (NV-Var (here refl))))
      S
      ≡ selectNf v i P S
select₂-instantiation v i P S =
  trans
    (subst-select2
      (singleNFSub S)
      v i
      (wkNfTy P)
      (N-Var (NV-Var (here refl))))
    (cong₂ (selectNf v i) (cancel-single-wk-proto S P) refl)

select₁-instantiation :
  ∀ {k}
    (v : Variance)
    (i : Fin k)
    (P : NfTy [] KP)
  → substNFTy
      (select1Nf v i
        (N-Normal (N-Var (here refl))))
      P
      ≡ select1Nf v i P
select₁-instantiation v i P =
  subst-select1
    (singleNFSub P)
    v i
    (N-Normal (N-Var (here refl)))

-- Each computational primitive exposes the trusted ingredient it needs:
--
-- * function beta reduction uses expression substitution;
-- * let-pair elimination uses double linear substitution;
-- * let-unit elimination is a direct premise of its typing rule;
-- * value pairing merely changes expression syntax.
--
-- Type application uses type substitution, recursion uses unrestricted
-- self-substitution, and the session/select specialization rules use their
-- normal-form constructor computations.  The mutual proof below handles every
-- head constructor carrying `L-β` and every evaluation-context closure
-- directly; no separate support evidence is required.

-- Complete preservation for the internal computation label.  Unlike the
-- legacy statement, the result records both the synthesized subtype exposed
-- by reduction and the actual leftover context up to annotations on entries
-- that were already consumed.

mutual

  beta-preserves-synth :
    ∀ {n pk m}
      {Γ₁ Γ₂ : Ctx [] n}
      {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk m)}
    → e₁ —[ L-β ]→ e₂
    → Γ₁ ⊢ e₁ ⇒ T ⊣ Γ₂
    → SynthResult Γ₁ e₂ T Γ₂

  beta-preserves-check :
    ∀ {n pk m}
      {Γ₁ Γ₂ : Ctx [] n}
      {e₁ e₂ : Expr [] n}
      {T : NfTy [] (KV pk m)}
    → e₁ —[ L-β ]→ e₂
    → Γ₁ ⊢ e₁ ⇐ T ⊣ Γ₂
    → CheckResult Γ₁ e₂ T Γ₂

  beta-preserves-synth Act-App
      (T-App (T-Val (TV-Abs body)) argument) =
    expression-substitution-preserves-typing argument body
  beta-preserves-synth Act-TApp
      (T-TApp (T-Val (TV-TAbs body))) =
    record
      { actualType = _
      ; Γactual = _
      ; derivation = T-Val (substTy-preserves-wk-value _ body)
      ; type-preservation = <:ₜ-refl _
      ; leftover = ≈ᵘ-refl
      }
  beta-preserves-synth Act-LetPair
      (T-LetPair (T-Val (TV-Pair du dv)) body) =
    record
      { actualType = _
      ; Γactual = _
      ; derivation =
          double-expression-substitution-preserves-typing du dv body
      ; type-preservation = <:ₜ-refl _
      ; leftover = ≈ᵘ-refl
      }
  beta-preserves-synth Act-LetUnit
      (T-LetUnit (T-Check (T-Val (TV-Const CT-Unit)) _) body) =
    record
      { actualType = _
      ; Γactual = _
      ; derivation = body
      ; type-preservation = <:ₜ-refl _
      ; leftover = ≈ᵘ-refl
      }
  beta-preserves-synth Act-PairV
      (T-Pair (T-Val left) (T-Val right)) =
    record
      { actualType = _
      ; Γactual = _
      ; derivation = T-Val (TV-Pair left right)
      ; type-preservation = <:ₜ-refl _
      ; leftover = ≈ᵘ-refl
      }
  beta-preserves-synth
      {Γ₁ = Γ₁}
      (Act-Rec {T = T} {U = U} {v = v})
      (T-App {m = Un} (T-Val recursive@(TV-Rec body)) argument)
    with recursive-unfolding-preserves-value recursive
  ... | record
          { actualType = functionType
          ; derivation = unfolded
          ; type-preservation = functionSub
          }
    with arrow-subtype-inversion functionSub
  ... | domain , result , functionEq , domainSub , resultSub =
    record
      { actualType = result
      ; Γactual = _
      ; derivation =
          T-App
            (T-Val
              (subst
                (λ X → Γ₁ ⊢ᵥ _ ⇒ X ⊣ Γ₁)
                functionEq
                unfolded))
            (check-subsumption argument domainSub)
      ; type-preservation = resultSub
      ; leftover = ≈ᵘ-refl
      }
  beta-preserves-synth
      (Act-Rec {T = T} {U = U} {v = v})
      (T-App {m = Lin} (T-Val ()) argument)
  beta-preserves-synth Act-Receive₁
      (T-TApp (T-Val (TV-Const CT-Receive))) =
    record
      { actualType = _
      ; Γactual = _
      ; derivation = T-Val TV-Receive₁
      ; type-preservation = <:ₜ-refl _
      ; leftover = ≈ᵘ-refl
      }
  beta-preserves-synth
      (Act-Receive₂ {T = T} {S = S})
      (T-TApp (T-Val TV-Receive₁))
    rewrite receive₂-instantiation T S =
    record
      { actualType = _
      ; Γactual = _
      ; derivation = T-Val TV-Receive₂
      ; type-preservation = <:ₜ-refl _
      ; leftover = ≈ᵘ-refl
      }
  beta-preserves-synth Act-Send₁
      (T-TApp (T-Val (TV-Const CT-Send))) =
    record
      { actualType = _
      ; Γactual = _
      ; derivation = T-Val TV-Send₁
      ; type-preservation = <:ₜ-refl _
      ; leftover = ≈ᵘ-refl
      }
  beta-preserves-synth
      (Act-Send₂ {T = T} {S = S})
      (T-TApp (T-Val TV-Send₁))
    rewrite send₂-instantiation T S =
    record
      { actualType = _
      ; Γactual = _
      ; derivation = T-Val TV-Send₂
      ; type-preservation = <:ₜ-refl _
      ; leftover = ≈ᵘ-refl
      }
  beta-preserves-synth
      (Act-Select₁ {v = v} {i = i} {P = P})
      (T-TApp (T-Val (TV-Const CT-Select)))
    rewrite select₁-instantiation v i (normalizeTy P) =
    record
      { actualType = _
      ; Γactual = _
      ; derivation = T-Val TV-Select₁
      ; type-preservation = <:ₜ-refl _
      ; leftover = ≈ᵘ-refl
      }
  beta-preserves-synth
      (Act-Select₂ {v = v} {i = i} {P = P} {S = S})
      (T-TApp (T-Val TV-Select₁))
    rewrite select₂-instantiation v i P S =
    record
      { actualType = _
      ; Γactual = _
      ; derivation = T-Val TV-Select₂
      ; type-preservation = <:ₜ-refl _
      ; leftover = ≈ᵘ-refl
      }

  beta-preserves-synth
      (Act-AppL step)
      (T-App function argument)
    with beta-preserves-synth step function
  ... | record
          { actualType = functionType
          ; Γactual = Γfunction
          ; derivation = function′
          ; type-preservation = functionSub
          ; leftover = functionLeftover
          }
    with arrow-subtype-inversion functionSub
  ... | domain , result , functionEq , domainSub , resultSub
    with retag-check-input
           (weaken-zero-preserves-check argument)
           (≈ᵘ-sym functionLeftover)
  ... | Γargument , argument′ , argumentLeftover =
    record
      { actualType = result
      ; Γactual = Γargument
      ; derivation =
          T-App
            (subst
              (λ X → _ ⊢ _ ⇒ X ⊣ Γfunction)
              functionEq
              function′)
            (check-subsumption argument′ domainSub)
      ; type-preservation = resultSub
      ; leftover = argumentLeftover
      }

  beta-preserves-synth
      (Act-AppR step)
      (T-App (T-Val function) argument)
    with beta-preserves-check step argument
  ... | record
          { Γactual = Γargument
          ; derivation = argument′
          ; leftover = argumentLeftover
          } =
    record
      { actualType = _
      ; Γactual = Γargument
      ; derivation =
          T-App
            (T-Val (weaken-zero-preserves-value function))
            argument′
      ; type-preservation = <:ₜ-refl _
      ; leftover = argumentLeftover
      }

  beta-preserves-synth
      (Act-TAppE step)
      (T-TApp function)
    with beta-preserves-synth step function
  ... | record
          { actualType = functionType
          ; Γactual = Γfunction
          ; derivation = function′
          ; type-preservation = functionSub
          ; leftover = functionLeftover
          }
    with poly-subtype-inversion functionSub
  ... | bodyType , functionEq , bodySub =
    record
      { actualType = substNFTy bodyType _
      ; Γactual = Γfunction
      ; derivation =
          T-TApp
            (subst
              (λ X → _ ⊢ _ ⇒ X ⊣ Γfunction)
              functionEq
              function′)
      ; type-preservation = subst-preserves-<:ₜ bodySub
      ; leftover = functionLeftover
      }

  beta-preserves-synth
      (Act-PairL step)
      (T-Pair left right)
    with beta-preserves-synth step left
  ... | record
          { actualType = leftType
          ; Γactual = Γleft
          ; derivation = left′
          ; type-preservation = leftSub
          ; leftover = leftLeftover
          }
    with retag-synth-input
           (weaken-zero-preserves-synth right)
           (≈ᵘ-sym leftLeftover)
  ... | Γright , right′ , rightLeftover =
    record
      { actualType = pairNf leftType _
      ; Γactual = Γright
      ; derivation = T-Pair left′ right′
      ; type-preservation = <:ₜ-pair leftSub (<:ₜ-refl _)
      ; leftover = rightLeftover
      }

  beta-preserves-synth
      (Act-PairR step)
      (T-Pair (T-Val left) right)
    with beta-preserves-synth step right
  ... | record
          { actualType = rightType
          ; Γactual = Γright
          ; derivation = right′
          ; type-preservation = rightSub
          ; leftover = rightLeftover
          } =
    record
      { actualType = pairNf _ rightType
      ; Γactual = Γright
      ; derivation =
          T-Pair
            (T-Val (weaken-zero-preserves-value left))
            right′
      ; type-preservation = <:ₜ-pair (<:ₜ-refl _) rightSub
      ; leftover = rightLeftover
      }

  beta-preserves-synth
      (Act-LetUnitE step)
      (T-LetUnit scrutinee body)
    with beta-preserves-check step scrutinee
  ... | record
          { Γactual = Γscrutinee
          ; derivation = scrutinee′
          ; leftover = scrutineeLeftover
          }
    with retag-synth-input
           (weaken-zero-preserves-synth body)
           (≈ᵘ-sym scrutineeLeftover)
  ... | Γbody , body′ , bodyLeftover =
    record
      { actualType = _
      ; Γactual = Γbody
      ; derivation = T-LetUnit scrutinee′ body′
      ; type-preservation = <:ₜ-refl _
      ; leftover = bodyLeftover
      }

  beta-preserves-synth
      (Act-MatchE step)
      (T-Match
        {Γ₂ = Γmid}
        {Γ₃ = Γout}
        {ss = ss}
        {v = v}
        {ssbranches = ssbranches}
        {incl = incl}
        {ne = ne}
        {P = P}
        {S = S}
        {branches = branches₀}
        {V = V}
        {sub = branchSub}
        scrutinee branches join)
    with beta-preserves-synth step scrutinee
  ... | record
          { actualType = scrutineeType
          ; Γactual = Γscrutinee
          ; derivation = scrutinee′
          ; type-preservation = scrutineeSub
          ; leftover = scrutineeLeftover
          }
    with match-input-subtype-inversion scrutineeSub
  ... | ss′ , P′ , S′ , scrutineeEq , ss′⊆ss , P′<:P , S′<:S
    with retagged-from-shape
           (≈ᵘ-sym scrutineeLeftover)
           (drop-lin-used
             (synth-preserves-~Ctx
               (weaken-zero-preserves-synth1
                 (branches (proj₁ ne) (proj₂ ne)))))
  ... | Γretagged , transition
    with strengthen-match-branches
           P′<:P
           S′<:S
           <:Γ-refl
           ne
           (λ i i∈ →
             retag-synth
               (weaken-zero-preserves-synth1 (branches i i∈))
               (RT-lin-used transition))
  ... | Γstrengthened , V′ , branches′ , V′<:V , relout
    with coherent-strengthened-output
           (drop-lin-used
             (synth-preserves-~Ctx
               (branches′ (proj₁ ne) (proj₂ ne))))
           (drop-lin-used
             (synth-preserves-~Ctx
               (retag-synth
                 (weaken-zero-preserves-synth1
                   (branches (proj₁ ne) (proj₂ ne)))
                 (RT-lin-used transition))))
           relout
           <:Γ-refl
  ... | refl
    with branchjoin⁺-monotone join V′<:V
  ... | resultType , resultBranches , resultJoin , resultSub =
    record
      { actualType = resultType
      ; Γactual = Γretagged
      ; derivation =
          T-Match
            {ss = ss′}
            {ssbranches = ssbranches}
            {incl = λ i∈ → incl (ss′⊆ss i∈)}
            {ne = ne}
            {P = P′}
            {S = S′}
            {branches = λ i i∈ → weakenExprBy1 0 (branches₀ i i∈)}
            {V = V′}
            {sub = resultBranches}
            (subst
              (λ X → _ ⊢ _ ⇒ X ⊣ Γscrutinee)
              scrutineeEq
              scrutinee′)
            branches′
            resultJoin
      ; type-preservation = resultSub
      ; leftover = ≈ᵘ-sym (retagged-output transition)
      }

  beta-preserves-synth
      (Act-LetPairE step)
      (T-LetPair {T = T} {U = U} scrutinee body)
    with beta-preserves-synth step scrutinee
  ... | record
          { actualType = pairType
          ; Γactual = Γscrutinee
          ; derivation = scrutinee′
          ; type-preservation = pairSub
          ; leftover = scrutineeLeftover
          }
    with pair-subtype-inversion pairSub
  ... | T′ , U′ , pairEq , T′<:T , U′<:U
    with retag-synth-input
           (weaken-zero-preserves-synth2 body)
           (≈ᵘ-lin (≈ᵘ-lin (≈ᵘ-sym scrutineeLeftover)))
  ... | (B-Used Tused ▻ (B-Used Uused ▻ Γbody)) , body′ ,
        ≈ᵘ-used (≈ᵘ-used bodyLeftover)
    with lin-used-invert (synth-preserves-~Ctx body′)
  ... | refl , refl , bodyShape
    with lin-used-invert bodyShape
  ... | refl , refl , _
    with strengthen-double-binder T′<:T U′<:U body′
  ... | record
          { actualType = resultType
          ; derivation = body″
          ; type-preservation = resultSub
          } =
    record
      { actualType = resultType
      ; Γactual = Γbody
      ; derivation =
          T-LetPair
            (subst
              (λ X → _ ⊢ _ ⇒ X ⊣ Γscrutinee)
              pairEq
              scrutinee′)
            body″
      ; type-preservation = resultSub
      ; leftover = bodyLeftover
      }

  beta-preserves-check step (T-Check source sub)
    with beta-preserves-synth step source
  ... | record
          { actualType = actualType
          ; Γactual = Γactual
          ; derivation = reduct
          ; type-preservation = actualSub
          ; leftover = outEq
          } =
    record
      { Γactual = Γactual
      ; derivation = T-Check reduct (<:ₜ-trans actualSub sub)
      ; leftover = outEq
      }

beta-reduction-preserves-synth :
  ∀ {n pk m}
    {Γ₁ Γ₂ : Ctx [] n}
    {e₁ e₂ : Expr [] n}
    {T : NfTy [] (KV pk m)}
  → e₁ —[ L-β ]→ e₂
  → Γ₁ ⊢ e₁ ⇒ T ⊣ Γ₂
  → SynthResult Γ₁ e₂ T Γ₂
beta-reduction-preserves-synth = beta-preserves-synth

beta-reduction-preserves-check :
  ∀ {n pk m}
    {Γ₁ Γ₂ : Ctx [] n}
    {e₁ e₂ : Expr [] n}
    {T : NfTy [] (KV pk m)}
  → e₁ —[ L-β ]→ e₂
  → Γ₁ ⊢ e₁ ⇐ T ⊣ Γ₂
  → CheckResult Γ₁ e₂ T Γ₂
beta-reduction-preserves-check = beta-preserves-check

new-dual-substitution :
  (S : Ty [] SLin)
  → normalizeTy (T-Dual Duality.D-S S)
      ≡ dualNFKind Duality.D-S (normalizeTy S)
new-dual-substitution S =
  trans
    (from-nt-idem S)
    (sym
      (cong
        (λ U →
          fromNormalTy
            (Types.nf-normal-type
              Duality.⊝
              (λ _ → Duality.D-S)
              U))
        (nfTyTy-fromNormalTy
          (Types.nf-normal-type Duality.⊕ Duality.d?⊥ S))))

-- `Act-Match` has an arbitrary substituted expression as its reduct.  That
-- makes its result index overlap syntactically with every other reduction
-- constructor.  This small private tag gives Agda's coverage checker an
-- ordinary discriminator while the public theorem still quantifies over an
-- arbitrary reduction proof.

data DirectMatchTag : Set where
  direct-match other-step : DirectMatchTag

direct-match-tag :
  ∀ {n Θ} {e₁ : Expr [] n} {ℓ : Label n Θ}
    {e₂ : Expr [] (length Θ + n)}
  → e₁ —[ ℓ ]→ e₂
  → DirectMatchTag
direct-match-tag (Act-Match _) = direct-match
direct-match-tag Act-App = other-step
direct-match-tag Act-TApp = other-step
direct-match-tag Act-LetPair = other-step
direct-match-tag Act-LetUnit = other-step
direct-match-tag Act-PairV = other-step
direct-match-tag Act-Rec = other-step
direct-match-tag Act-Fork = other-step
direct-match-tag Act-New = other-step
direct-match-tag Act-Receive₁ = other-step
direct-match-tag Act-Receive₂ = other-step
direct-match-tag Act-Rcv = other-step
direct-match-tag Act-Send₁ = other-step
direct-match-tag Act-Send₂ = other-step
direct-match-tag Act-Send = other-step
direct-match-tag Act-Sel = other-step
direct-match-tag Act-Select₁ = other-step
direct-match-tag Act-Select₂ = other-step
direct-match-tag Act-Close = other-step
direct-match-tag (Act-AppL _) = other-step
direct-match-tag (Act-AppR _) = other-step
direct-match-tag (Act-TAppE _) = other-step
direct-match-tag (Act-PairL _) = other-step
direct-match-tag (Act-PairR _) = other-step
direct-match-tag (Act-MatchE _) = other-step
direct-match-tag (Act-LetPairE _) = other-step
direct-match-tag (Act-LetUnitE _) = other-step

record ReductionSynthResult
    {n Θ pk m}
    (Γin Γv : Ctx [] n)
    {ℓ : Label n Θ}
    (lbl : ℓ ⦂ Γin ⇒ Γv)
    (Γ₀ Γ₂ : Ctx [] n)
    (e₂ : Expr [] (length Θ + n))
    (T : NfTy [] (KV pk m)) : Set where
  field
    Gf : Ctx [] n
    Gf′ : Ctx [] (length Θ + n)
    Γ₀′ : Ctx [] n
    Γ₁ : Ctx [] (length Θ + n)
    Γ₁′ : Ctx [] (length Θ + n)
    Γout : Ctx [] (length Θ + n)
    U : NfTy [] (KV pk m)

    src-remove : RemoveCtx Γ₀ Gf Γ₀′
    frame-update : Gf —frm[ ℓ ]→ Gf′
    dst-remove : RemoveCtx Γ₁ Gf′ Γ₁′
    ctx-step : Γ₀′ —ctx[ ℓ ]→ Γ₁′
    compat : Compatible ctx-step lbl
    effect-aligned : ctx-effect ctx-step ≡ frm-effect frame-update
    synth : Γ₁ ⊢ e₂ ⇒ U ⊣ Γout
    subtype : normalTyOf U <:ₜ normalTyOf T
    leftover : Γout ≈ᵘ extendUsed Θ Γ₂

record ReductionCheckResult
    {n Θ pk m}
    (Γin Γv : Ctx [] n)
    {ℓ : Label n Θ}
    (lbl : ℓ ⦂ Γin ⇒ Γv)
    (Γ₀ Γ₂ : Ctx [] n)
    (e₂ : Expr [] (length Θ + n))
    (T : NfTy [] (KV pk m)) : Set where
  field
    Gf : Ctx [] n
    Gf′ : Ctx [] (length Θ + n)
    Γ₀′ : Ctx [] n
    Γ₁ : Ctx [] (length Θ + n)
    Γ₁′ : Ctx [] (length Θ + n)
    Γout : Ctx [] (length Θ + n)

    src-remove : RemoveCtx Γ₀ Gf Γ₀′
    frame-update : Gf —frm[ ℓ ]→ Gf′
    dst-remove : RemoveCtx Γ₁ Gf′ Γ₁′
    ctx-step : Γ₀′ —ctx[ ℓ ]→ Γ₁′
    compat : Compatible ctx-step lbl
    effect-aligned : ctx-effect ctx-step ≡ frm-effect frame-update
    check : Γ₁ ⊢ e₂ ⇐ T ⊣ Γout
    leftover : Γout ≈ᵘ extendUsed Θ Γ₂

beta-reduction-result :
  ∀ {n pk m}
    {Γ₀ Γ₂ Γin Γv : Ctx [] n}
    {e₁ e₂ : Expr [] n} {T : NfTy [] (KV pk m)}
  → (step : e₁ —[ L-β ]→ e₂)
  → Γ₀ ⊢ e₁ ⇒ T ⊣ Γ₂
  → (lbl : L-β ⦂ Γin ⇒ Γv)
  → Extract Γ₀ L-β Γin
  → LinearDisjoint Γ₀ Γv
  → ReductionSynthResult Γin Γv lbl Γ₀ Γ₂ e₂ T
beta-reduction-result {Γ₀ = Γ₀}
    step source (Label-β auin auv) Ex-β _
  with beta-preserves-synth step source
... | record
        { actualType = U
        ; Γactual = Γout
        ; derivation = reduct
        ; type-preservation = sub
        ; leftover = out≈
        } =
  record
    { Gf = allUsedCtx Γ₀
    ; Gf′ = allUsedCtx Γ₀
    ; Γ₀′ = Γ₀
    ; Γ₁ = Γ₀
    ; Γ₁′ = Γ₀
    ; Γout = Γout
    ; U = U
    ; src-remove = remove-allUsedCtx Γ₀
    ; frame-update = Frm-β
    ; dst-remove = remove-allUsedCtx Γ₀
    ; ctx-step = Ctx-β
    ; compat = Compat-β refl
    ; effect-aligned = refl
    ; synth = reduct
    ; subtype = sub
    ; leftover = out≈
    }

reduction-preserves-synth-by-tag :
  ∀ {n Θ pk m}
    {Γ₀ Γ₂ Γin Γv : Ctx [] n}
    {e₁ : Expr [] n} {e₂ : Expr [] (length Θ + n)}
    {T : NfTy [] (KV pk m)} {ℓ : Label n Θ}
  → (tag : DirectMatchTag)
  → (step : e₁ —[ ℓ ]→ e₂)
  → tag ≡ direct-match-tag step
  → Γ₀ ⊢ e₁ ⇒ T ⊣ Γ₂
  → (lbl : ℓ ⦂ Γin ⇒ Γv)
  → Extract Γ₀ ℓ Γin
  → LinearDisjoint Γ₀ Γv
  → ReductionSynthResult Γin Γv lbl Γ₀ Γ₂ e₂ T
reduction-preserves-synth-by-tag other-step step@Act-App refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag other-step step@Act-TApp refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag other-step step@Act-LetPair refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag other-step step@Act-LetUnit refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag other-step step@Act-PairV refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag other-step step@Act-Rec refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag other-step step@Act-Receive₁ refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag other-step step@Act-Receive₂ refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag other-step step@Act-Send₁ refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag other-step step@Act-Send₂ refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag other-step step@Act-Select₁ refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag other-step step@Act-Select₂ refl source lbl ex disj =
  beta-reduction-result step source lbl ex disj
reduction-preserves-synth-by-tag
    {Θ = Θ} {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    other-step
    (Act-AppL {e₂ = e₂} {e₃ = e₃} step)
    refl
    (T-App {Γ₂ = Γ₂} {T = A} {U = V} function argument)
    lbl ex disj
  with reduction-preserves-synth-by-tag
         (direct-match-tag step) step refl function lbl ex disj
... | ps
  with arrow-subtype-inversion
         (ReductionSynthResult.subtype ps)
... | A′ , V′ , eqFunction , A<:A′ , V′<:V
  with retag-check-input
         (weaken-label-check lbl argument)
         (≈ᵘ-sym (ReductionSynthResult.leftover ps))
... | Γargument , argument′ , argument≈ =
  record
    { Gf = ReductionSynthResult.Gf ps
    ; Gf′ = ReductionSynthResult.Gf′ ps
    ; Γ₀′ = ReductionSynthResult.Γ₀′ ps
    ; Γ₁ = ReductionSynthResult.Γ₁ ps
    ; Γ₁′ = ReductionSynthResult.Γ₁′ ps
    ; Γout = Γargument
    ; U = V′
    ; src-remove = ReductionSynthResult.src-remove ps
    ; frame-update = ReductionSynthResult.frame-update ps
    ; dst-remove = ReductionSynthResult.dst-remove ps
    ; ctx-step = ReductionSynthResult.ctx-step ps
    ; compat = ReductionSynthResult.compat ps
    ; effect-aligned = ReductionSynthResult.effect-aligned ps
    ; synth =
        T-App
          (subst
            (λ X →
              ReductionSynthResult.Γ₁ ps
                ⊢ e₂ ⇒ X
                ⊣ ReductionSynthResult.Γout ps)
            eqFunction
            (ReductionSynthResult.synth ps))
          (check-subsumption argument′ A<:A′)
    ; subtype = V′<:V
    ; leftover = argument≈
    }
reduction-preserves-synth-by-tag
    {Θ = Θ} {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    other-step
    (Act-TAppE {e₂ = e₂} {T = Uarg} step)
    refl
    (T-TApp {T = Tpoly} function)
    lbl ex disj
  with reduction-preserves-synth-by-tag
         (direct-match-tag step) step refl function lbl ex disj
... | ps
  with poly-subtype-inversion
         (ReductionSynthResult.subtype ps)
... | Tpoly′ , eqPoly , Tpoly′<:Tpoly =
  record
    { Gf = ReductionSynthResult.Gf ps
    ; Gf′ = ReductionSynthResult.Gf′ ps
    ; Γ₀′ = ReductionSynthResult.Γ₀′ ps
    ; Γ₁ = ReductionSynthResult.Γ₁ ps
    ; Γ₁′ = ReductionSynthResult.Γ₁′ ps
    ; Γout = ReductionSynthResult.Γout ps
    ; U = substNFTy Tpoly′ Uarg
    ; src-remove = ReductionSynthResult.src-remove ps
    ; frame-update = ReductionSynthResult.frame-update ps
    ; dst-remove = ReductionSynthResult.dst-remove ps
    ; ctx-step = ReductionSynthResult.ctx-step ps
    ; compat = ReductionSynthResult.compat ps
    ; effect-aligned = ReductionSynthResult.effect-aligned ps
    ; synth =
        T-TApp
          (subst
            (λ X →
              ReductionSynthResult.Γ₁ ps
                ⊢ e₂ ⇒ X
                ⊣ ReductionSynthResult.Γout ps)
            eqPoly
            (ReductionSynthResult.synth ps))
    ; subtype = subst-preserves-<:ₜ Tpoly′<:Tpoly
    ; leftover = ReductionSynthResult.leftover ps
    }
reduction-preserves-synth-by-tag
    {Θ = Θ} {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    other-step
    (Act-PairL {e₂ = e₂} {e₃ = e₃} step)
    refl
    (T-Pair {Γ₂ = Γ₂} {T = T} {U = U} left right)
    lbl ex disj
  with reduction-preserves-synth-by-tag
         (direct-match-tag step) step refl left lbl ex disj
... | ps
  with retag-synth-input
         (weaken-label-synth lbl right)
         (≈ᵘ-sym (ReductionSynthResult.leftover ps))
... | Γright , right′ , right≈ =
  record
    { Gf = ReductionSynthResult.Gf ps
    ; Gf′ = ReductionSynthResult.Gf′ ps
    ; Γ₀′ = ReductionSynthResult.Γ₀′ ps
    ; Γ₁ = ReductionSynthResult.Γ₁ ps
    ; Γ₁′ = ReductionSynthResult.Γ₁′ ps
    ; Γout = Γright
    ; U = pairNf (ReductionSynthResult.U ps) U
    ; src-remove = ReductionSynthResult.src-remove ps
    ; frame-update = ReductionSynthResult.frame-update ps
    ; dst-remove = ReductionSynthResult.dst-remove ps
    ; ctx-step = ReductionSynthResult.ctx-step ps
    ; compat = ReductionSynthResult.compat ps
    ; effect-aligned = ReductionSynthResult.effect-aligned ps
    ; synth = T-Pair (ReductionSynthResult.synth ps) right′
    ; subtype =
        <:ₜ-pair
          (ReductionSynthResult.subtype ps)
          (<:ₜ-refl (normalTyOf U))
    ; leftover = right≈
    }
reduction-preserves-synth-by-tag
    {Θ = Θ} {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    other-step
    (Act-AppR {e₂ = e₂} step)
    refl
    (T-App {T = A} {U = V}
      (T-Val dv)
      argument@(T-Check argumentSynth argumentSub))
    lbl ex disj
  with strip-value dv
... | G , G′ , r , dv′ , au
  with right-check-extract-disjoint r argument step lbl ex disj
... | ldex
  with reduction-preserves-synth-by-tag
         (direct-match-tag step)
         step
         refl
         argumentSynth
         lbl
         (remove-extract-fresh r ldex ex)
         (remove-disjoint r disj)
... | ps
  with ctx-step-preserves-disjoint-aligned
         (ReductionSynthResult.ctx-step ps)
         lbl
         (ReductionSynthResult.compat ps)
         (remove-preserves-disjoint
           (ReductionSynthResult.src-remove ps)
           (sym-disjoint (remove-linear r)))
         (sym-disjoint (remove-removed-disjoint r disj))
... | Gstep , upstepFrm , ldstep , upstepAligned
  with frame-update-value-aligned
         (ReductionSynthResult.ctx-step ps)
         upstepFrm
         upstepAligned
         (remove-preserves-disjoint
           (ReductionSynthResult.src-remove ps)
           (sym-disjoint (remove-linear r)))
         dv′ au
... | Gstep′ , upstepOut , auStep , dvStep
  with frame-updates-preserve-disjoint
         (ReductionSynthResult.frame-update ps)
         upstepFrm
         (trans
           (sym (ReductionSynthResult.effect-aligned ps))
           upstepAligned)
         (remove-removed-disjoint
           (ReductionSynthResult.src-remove ps)
           (sym-disjoint (remove-linear r)))
... | ldframes
  with restore-disjoint
         (ReductionSynthResult.dst-remove ps)
         ldstep
         ldframes
... | ldtarget
  with mergeRemoveContext r (ReductionSynthResult.src-remove ps)
... | Gf , msrc , rsrc
  with mergeDisjointContext ldtarget
... | Γ₁ , mleft
  with frame-remove mleft
... | dstr
  with mergeRemoveContext dstr (ReductionSynthResult.dst-remove ps)
... | Gfdst , mdst , rdst
  with frame-update-merge-aligned
         msrc
         upstepFrm
         (ReductionSynthResult.frame-update ps)
         (trans
           (sym upstepAligned)
           (ReductionSynthResult.effect-aligned ps))
         mdst
... | mergedFrame , mergedEffect =
  record
    { Gf = Gf
    ; Gf′ = Gfdst
    ; Γ₀′ = ReductionSynthResult.Γ₀′ ps
    ; Γ₁ = Γ₁
    ; Γ₁′ = ReductionSynthResult.Γ₁′ ps
    ; Γout = ReductionSynthResult.Γout ps
    ; U = V
    ; src-remove = rsrc
    ; frame-update = mergedFrame
    ; dst-remove = rdst
    ; ctx-step = ReductionSynthResult.ctx-step ps
    ; compat = ReductionSynthResult.compat ps
    ; effect-aligned =
        trans upstepAligned (sym mergedEffect)
    ; synth =
        T-App
          (T-Val
            (replay-value-allUsed
              dvStep
              (remove-to-rest-frame dstr)
              auStep))
          (T-Check
            (ReductionSynthResult.synth ps)
            (<:ₜ-trans
              (ReductionSynthResult.subtype ps)
              argumentSub))
    ; subtype = <:ₜ-refl (normalTyOf V)
    ; leftover = ReductionSynthResult.leftover ps
    }
reduction-preserves-synth-by-tag
    {Θ = Θ} {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    other-step
    (Act-PairR {e₂ = e₂} step)
    refl
    (T-Pair {T = T} {U = U} (T-Val dv) right)
    lbl ex disj
  with strip-value dv
... | G , G′ , r , dv′ , au
  with right-synth-extract-disjoint r right step lbl ex disj
... | ldex
  with reduction-preserves-synth-by-tag
         (direct-match-tag step)
         step
         refl
         right
         lbl
         (remove-extract-fresh r ldex ex)
         (remove-disjoint r disj)
... | ps
  with ctx-step-preserves-disjoint-aligned
         (ReductionSynthResult.ctx-step ps)
         lbl
         (ReductionSynthResult.compat ps)
         (remove-preserves-disjoint
           (ReductionSynthResult.src-remove ps)
           (sym-disjoint (remove-linear r)))
         (sym-disjoint (remove-removed-disjoint r disj))
... | Gstep , upstepFrm , ldstep , upstepAligned
  with frame-update-value-aligned
         (ReductionSynthResult.ctx-step ps)
         upstepFrm
         upstepAligned
         (remove-preserves-disjoint
           (ReductionSynthResult.src-remove ps)
           (sym-disjoint (remove-linear r)))
         dv′ au
... | Gstep′ , upstepOut , auStep , dvStep
  with frame-updates-preserve-disjoint
         (ReductionSynthResult.frame-update ps)
         upstepFrm
         (trans
           (sym (ReductionSynthResult.effect-aligned ps))
           upstepAligned)
         (remove-removed-disjoint
           (ReductionSynthResult.src-remove ps)
           (sym-disjoint (remove-linear r)))
... | ldframes
  with restore-disjoint
         (ReductionSynthResult.dst-remove ps)
         ldstep
         ldframes
... | ldtarget
  with mergeRemoveContext r (ReductionSynthResult.src-remove ps)
... | Gf , msrc , rsrc
  with mergeDisjointContext ldtarget
... | Γ₁ , mleft
  with frame-remove mleft
... | dstr
  with mergeRemoveContext dstr (ReductionSynthResult.dst-remove ps)
... | Gfdst , mdst , rdst
  with frame-update-merge-aligned
         msrc
         upstepFrm
         (ReductionSynthResult.frame-update ps)
         (trans
           (sym upstepAligned)
           (ReductionSynthResult.effect-aligned ps))
         mdst
... | mergedFrame , mergedEffect =
  record
    { Gf = Gf
    ; Gf′ = Gfdst
    ; Γ₀′ = ReductionSynthResult.Γ₀′ ps
    ; Γ₁ = Γ₁
    ; Γ₁′ = ReductionSynthResult.Γ₁′ ps
    ; Γout = ReductionSynthResult.Γout ps
    ; U = pairNf T (ReductionSynthResult.U ps)
    ; src-remove = rsrc
    ; frame-update = mergedFrame
    ; dst-remove = rdst
    ; ctx-step = ReductionSynthResult.ctx-step ps
    ; compat = ReductionSynthResult.compat ps
    ; effect-aligned =
        trans upstepAligned (sym mergedEffect)
    ; synth =
        T-Pair
          (T-Val
            (replay-value-allUsed
              dvStep
              (remove-to-rest-frame dstr)
              auStep))
          (ReductionSynthResult.synth ps)
    ; subtype =
        <:ₜ-pair
          (<:ₜ-refl (normalTyOf T))
          (ReductionSynthResult.subtype ps)
    ; leftover = ReductionSynthResult.leftover ps
    }
reduction-preserves-synth-by-tag
    {Θ = Θ} {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    other-step
    (Act-LetUnitE {e₂ = e₂} {e₃ = e₃} step)
    refl
    (T-LetUnit (T-Check scrutinee scrutineeSub) body)
    lbl ex disj
  with reduction-preserves-synth-by-tag
         (direct-match-tag step) step refl scrutinee lbl ex disj
... | ps
  with retag-synth-input
         (weaken-label-synth lbl body)
         (≈ᵘ-sym (ReductionSynthResult.leftover ps))
... | Γbody , body′ , body≈ =
  record
    { Gf = ReductionSynthResult.Gf ps
    ; Gf′ = ReductionSynthResult.Gf′ ps
    ; Γ₀′ = ReductionSynthResult.Γ₀′ ps
    ; Γ₁ = ReductionSynthResult.Γ₁ ps
    ; Γ₁′ = ReductionSynthResult.Γ₁′ ps
    ; Γout = Γbody
    ; U = _
    ; src-remove = ReductionSynthResult.src-remove ps
    ; frame-update = ReductionSynthResult.frame-update ps
    ; dst-remove = ReductionSynthResult.dst-remove ps
    ; ctx-step = ReductionSynthResult.ctx-step ps
    ; compat = ReductionSynthResult.compat ps
    ; effect-aligned = ReductionSynthResult.effect-aligned ps
    ; synth =
        T-LetUnit
          (T-Check
            (ReductionSynthResult.synth ps)
            (<:ₜ-trans
              (ReductionSynthResult.subtype ps)
              scrutineeSub))
          body′
    ; subtype = <:ₜ-refl _
    ; leftover = body≈
    }
reduction-preserves-synth-by-tag
    {Θ = Θ} {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    other-step
    (Act-LetPairE {e₂ = e₂} {e₃ = e₃} step)
    refl
    (T-LetPair {T = T} {U = U} scrutinee body)
    lbl ex disj
  with reduction-preserves-synth-by-tag
         (direct-match-tag step) step refl scrutinee lbl ex disj
... | ps
  with pair-subtype-inversion (ReductionSynthResult.subtype ps)
... | T′ , U′ , pairEq , T′<:T , U′<:U
  with strengthen-double-binder T′<:T U′<:U body
... | record
        { actualType = V′
        ; derivation = bodyStrong
        ; type-preservation = V′<:V
        }
  with retag-synth-input-two-lin-used
         (weaken-label-synth2 lbl bodyStrong)
         (≈ᵘ-sym (ReductionSynthResult.leftover ps))
... | Γbody , body′ , body≈ =
  record
    { Gf = ReductionSynthResult.Gf ps
    ; Gf′ = ReductionSynthResult.Gf′ ps
    ; Γ₀′ = ReductionSynthResult.Γ₀′ ps
    ; Γ₁ = ReductionSynthResult.Γ₁ ps
    ; Γ₁′ = ReductionSynthResult.Γ₁′ ps
    ; Γout = Γbody
    ; U = V′
    ; src-remove = ReductionSynthResult.src-remove ps
    ; frame-update = ReductionSynthResult.frame-update ps
    ; dst-remove = ReductionSynthResult.dst-remove ps
    ; ctx-step = ReductionSynthResult.ctx-step ps
    ; compat = ReductionSynthResult.compat ps
    ; effect-aligned = ReductionSynthResult.effect-aligned ps
    ; synth =
        T-LetPair
          (subst
            (λ X →
              ReductionSynthResult.Γ₁ ps
                ⊢ e₂ ⇒ X
                ⊣ ReductionSynthResult.Γout ps)
            pairEq
            (ReductionSynthResult.synth ps))
          body′
    ; subtype = V′<:V
    ; leftover = body≈
    }
reduction-preserves-synth-by-tag
    {Θ = Θ} {Γ₀ = Γ₀} {Γ₂ = Γ₃}
    other-step
    (Act-MatchE {e₂ = e₂} step)
    refl
    (T-Match
      {Γ₂ = Γmid}
      {ss = ss}
      {v = v}
      {ssbranches = ssbranches}
      {incl = incl}
      {ne = ne}
      {P = P}
      {S = S}
      {branches = branches₀}
      {V = V}
      {sub = branchSub}
      scrutinee branches join)
    lbl ex disj
  with reduction-preserves-synth-by-tag
         (direct-match-tag step) step refl scrutinee lbl ex disj
... | ps
  with match-input-subtype-inversion (ReductionSynthResult.subtype ps)
... | ss′ , P′ , S′ , scrutineeEq , ss′⊆ss , P′<:P , S′<:S
  with retagged-from-shape
         (≈ᵘ-sym (ReductionSynthResult.leftover ps))
         (drop-lin-used
           (synth-preserves-~Ctx
             (weaken-label-synth1 lbl
               (branches (proj₁ ne) (proj₂ ne)))))
... | Γretagged , transition
  with strengthen-match-branches
         P′<:P
         S′<:S
         <:Γ-refl
         ne
         (λ i i∈ →
           retag-synth
             (weaken-label-synth1 lbl (branches i i∈))
             (RT-lin-used transition))
... | Γstrengthened , V′ , branches′ , V′<:V , relout
  with coherent-strengthened-output
         (drop-lin-used
           (synth-preserves-~Ctx
             (branches′ (proj₁ ne) (proj₂ ne))))
         (drop-lin-used
           (synth-preserves-~Ctx
             (retag-synth
               (weaken-label-synth1 lbl
                 (branches (proj₁ ne) (proj₂ ne)))
               (RT-lin-used transition))))
         relout
         <:Γ-refl
... | refl
  with branchjoin⁺-monotone join V′<:V
... | resultType , resultBranches , resultJoin , resultSub =
  record
    { Gf = ReductionSynthResult.Gf ps
    ; Gf′ = ReductionSynthResult.Gf′ ps
    ; Γ₀′ = ReductionSynthResult.Γ₀′ ps
    ; Γ₁ = ReductionSynthResult.Γ₁ ps
    ; Γ₁′ = ReductionSynthResult.Γ₁′ ps
    ; Γout = Γretagged
    ; U = resultType
    ; src-remove = ReductionSynthResult.src-remove ps
    ; frame-update = ReductionSynthResult.frame-update ps
    ; dst-remove = ReductionSynthResult.dst-remove ps
    ; ctx-step = ReductionSynthResult.ctx-step ps
    ; compat = ReductionSynthResult.compat ps
    ; effect-aligned = ReductionSynthResult.effect-aligned ps
    ; synth =
        T-Match
          {ss = ss′}
          {ssbranches = ssbranches}
          {incl = λ i∈ → incl (ss′⊆ss i∈)}
          {ne = ne}
          {P = P′}
          {S = S′}
          {branches =
            λ i i∈ →
              weakenExprBy1 (length Θ) (branches₀ i i∈)}
          {V = V′}
          {sub = resultBranches}
          (subst
            (λ X →
              ReductionSynthResult.Γ₁ ps
                ⊢ e₂ ⇒ X
                ⊣ ReductionSynthResult.Γout ps)
            scrutineeEq
            (ReductionSynthResult.synth ps))
          branches′
          resultJoin
    ; subtype = resultSub
    ; leftover = ≈ᵘ-sym (retagged-output transition)
    }
reduction-preserves-synth-by-tag
    {Γ₀ = Γ₀}
    other-step
    (Act-New {S = S})
    refl
    (T-TApp (T-Val (TV-Const CT-New)))
    (Label-New auin auv)
    Ex-New
    _ =
  let
    sessT = normalizeTy S
    dualT = normalizeTy (T-Dual Duality.D-S S)

    synth-new :
      (B-Lin sessT ▻ (B-Lin dualT ▻ Γ₀))
        ⊢ E-Val (V-Pair (V-Var fzero) (V-Var (fsuc fzero)))
        ⇒ pairNf sessT dualT
        ⊣ (B-Used sessT ▻ (B-Used dualT ▻ Γ₀))
    synth-new =
      T-Val
        (TV-Pair
          (TV-Var-Lin take-here)
          (TV-Var-Lin (take-there✖ take-here)))
  in
  record
    { Gf = allUsedCtx Γ₀
    ; Gf′ = extendUsed (S ∷ T-Dual Duality.D-S S ∷ []) (allUsedCtx Γ₀)
    ; Γ₀′ = Γ₀
    ; Γ₁ = B-Lin sessT ▻ (B-Lin dualT ▻ Γ₀)
    ; Γ₁′ = B-Lin sessT ▻ (B-Lin dualT ▻ Γ₀)
    ; Γout = B-Used sessT ▻ (B-Used dualT ▻ Γ₀)
    ; U = pairNf sessT dualT
    ; src-remove = remove-allUsedCtx Γ₀
    ; frame-update = Frm-New
    ; dst-remove =
        remove-allUsedCtx (B-Lin sessT ▻ (B-Lin dualT ▻ Γ₀))
    ; ctx-step = Ctx-New
    ; compat = Compat-New refl
    ; effect-aligned = refl
    ; synth = synth-new
    ; subtype =
        <:ₜ-pair
          (<:ₜ-refl sessT)
          (<:ₜ-refl-eq (new-dual-substitution S))
    ; leftover = ≈ᵘ-refl
    }
reduction-preserves-synth-by-tag
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    other-step
    (Act-Rcv {T = Tᵣ} {S = Sᵣ} {x = x} {v = v})
    refl
    (T-App
      (T-Val TV-Receive₂)
      (T-Check (T-Val (TV-Var-Lin take₀)) sub))
    (Label-RecvVal {T = T} {S = S} take auin dv au ldin)
    (Ex-RecvVal rin _ _)
    disj
  with extract-membership rin (take-membership-fresh take)
... | x∈
  with linear-membership-type
         (take-membership-fresh take₀)
         x∈
... | eqChan
  with recvChan-subtype
         (subst
           (λ X →
             normalTyOf X <:ₜ
             normalTyOf
               (recvChanNf Tᵣ Sᵣ))
           eqChan
           sub)
... | refl , T<:Tᵣ , S<:Sᵣ
  with take-replace-lin {U = S} take₀
... | Γx , rep
  with replace-preserves-disjoint x∈ disj rep
... | Γv-out , repv , ld′
  with mergeDisjointContext ld′
... | Γ₁ , merge
  with recv-payload-replace-≈ᵘ take ldin repv
... | vctx≈
  with retag-value-input dv vctx≈
... | Γv-used′ , dv′ , vout≈
  with replace-take-fresh take₀ rep
... | Γout , take′ , out≈ =
  let
    au′ = allUsed-resp-≈ᵘ (≈ᵘ-sym vout≈) au

    dv-merged = replay-value-allUsed dv′ merge au′
  in
  record
    { Gf = allUsedCtx Γ₀
    ; Gf′ = allUsedCtx Γ₁
    ; Γ₀′ = Γ₀
    ; Γ₁ = Γ₁
    ; Γ₁′ = Γ₁
    ; Γout = Γout
    ; U = pairNf T S
    ; src-remove = remove-allUsedCtx Γ₀
    ; frame-update =
        Frm-Rcv
          (subst
            (ReplaceAt (allUsedCtx Γ₀) x (B-Used S))
            (allUsedCtx-merge merge)
            (allUsedCtx-replace-lin-at x∈ rep))
    ; dst-remove = remove-allUsedCtx Γ₁
    ; ctx-step = Ctx-Rcv dv au disj x∈ rep repv merge
    ; compat = Compat-RecvVal
    ; effect-aligned = refl
    ; synth = T-Val (TV-Pair dv-merged (TV-Var-Lin take′))
    ; subtype = <:ₜ-pair T<:Tᵣ S<:Sᵣ
    ; leftover = out≈
    }
reduction-preserves-synth-by-tag
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    other-step
    (Act-Send {T = Tᵣ} {S = Sᵣ} {x = x} {v = v})
    refl
    (T-App
      (T-Val TV-Send₂)
      (T-Check
        (T-Val (TV-Pair {Γ₂ = Γv₀} dv₀ (TV-Var-Lin take₀)))
        (<:ₜ-pair Targ<:Tᵣ Uchan<:send)))
    (Label-SendVal {T = T} {S = S} take dv au)
    (Ex-SendVal rin _ _ _)
    _
  with send-remove-membership-fresh rin take
... | Γx , rm , x∈
  with value-kind-unique
         (replay-value-allUsed dv (remove-to-rest-frame rm) au)
         dv₀
... | refl , refl
  with value-output-unique
         (replay-value-allUsed dv (remove-to-rest-frame rm) au)
         dv₀
... | eqPayloadOut
  with linear-membership-type
         (take-membership-fresh take₀)
         (subst
           (λ G → G ∋ˡ x ∶ sendChanNf T S)
           eqPayloadOut
           x∈)
... | eqChan
  with sendChan-subtype
         (subst
           (λ X →
             normalTyOf X <:ₜ
             normalTyOf
               (sendChanNf Tᵣ Sᵣ))
           eqChan
           Uchan<:send)
... | refl , _ , S<:Sᵣ
  with take-replace-lin {U = sessTyNf S} take₀
... | Γ₁ , rep
  with replace-take-fresh take₀ rep
... | Γout , take′ , out≈ =
  let
    x∈₀ =
      subst
        (λ G → G ∋ˡ x ∶ sendChanNf T S)
        eqPayloadOut
        x∈

    repx =
      subst
        (λ G → ReplaceAt G x (B-Lin (sessTyNf S)) Γ₁)
        (sym eqPayloadOut)
        rep

    eqAll =
      trans
        (allUsedCtx-remove rm)
        (cong allUsedCtx eqPayloadOut)
  in
  record
    { Gf = allUsedCtx Γv₀
    ; Gf′ = allUsedCtx Γ₁
    ; Γ₀′ = Γ₀
    ; Γ₁ = Γ₁
    ; Γ₁′ = Γ₁
    ; Γout = Γout
    ; U = sessTyNf S
    ; src-remove =
        subst
          (λ Gf → RemoveCtx Γ₀ Gf Γ₀)
          eqAll
          (remove-allUsedCtx Γ₀)
    ; frame-update =
        Frm-Send (allUsedCtx-replace-lin-at x∈₀ rep)
    ; dst-remove = remove-allUsedCtx Γ₁
    ; ctx-step = Ctx-Send rm dv au x∈ repx
    ; compat = Compat-SendVal
    ; effect-aligned = refl
    ; synth = T-Val (TV-Var-Lin take′)
    ; subtype = <:ₜ-sub S<:Sᵣ
    ; leftover = out≈
    }
reduction-preserves-synth-by-tag
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    direct-match
    (Act-Match
      {ss = ss} {ne = ne} {x = x} {branches = branches} {i = i}
      i∈)
    refl
    (T-Match {ss = ssin} {incl = incl}
      (T-Val (TV-Var-Lin take₀))
      bs
      bj)
    (Label-RecvLab auin au)
    Ex-RecvLab
    _
  with take-replace-lin
         {U = MatchBranchOutput ss _ _ _ i i∈}
         take₀
... | Γ₁ , rep
  with replace-take-fresh take₀ rep
... | Γtake , take′ , take≈
  with retag-synth-input-lin-used
         (bs i i∈)
         (≈ᵘ-sym take≈)
... | Γout , body′ , out≈
  with variable-substitution-preserves-synth take′ body′
... | reduct =
  record
    { Gf = allUsedCtx Γ₀
    ; Gf′ = allUsedCtx Γ₁
    ; Γ₀′ = Γ₀
    ; Γ₁ = Γ₁
    ; Γ₁′ = Γ₁
    ; Γout = Γout
    ; U = _
    ; src-remove = remove-allUsedCtx Γ₀
    ; frame-update =
        Frm-Match i∈
          (allUsedCtx-replace-lin-at
            (take-membership-fresh take₀)
            rep)
    ; dst-remove = remove-allUsedCtx Γ₁
    ; ctx-step =
        Ctx-Match {ssin = ssin} {ssout = ss} {incl = incl}
          i∈
          (take-membership-fresh take₀)
          rep
    ; compat = Compat-Match refl
    ; effect-aligned = refl
    ; synth = reduct
    ; subtype = match-branch-subtype i i∈ bj
    ; leftover = out≈
    }
reduction-preserves-synth-by-tag
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    other-step
    (Act-Sel {v = vₛ} {i = i} {P = Pₛ} {S = Sₛ} {x = x})
    refl
    (T-App {T = A}
      (T-Val vr@TV-Select₂)
      (T-Check (T-Val (TV-Var-Lin take₀)) sub))
    (Label-SendLab {v = v} {P = P} {S = S} take au)
    (Ex-SendLab rin _)
    _
  with extract-membership rin (take-membership-fresh take)
... | x∈
  with linear-membership-type
         (take-membership-fresh take₀)
         x∈
... | eqChan
  with take-replace-lin {U = selectOutNf v i P S} take₀
... | Γ₁ , rep
  with replace-take-fresh take₀ rep
... | Γout , take′ , out≈ =
  let
    selSub =
      subst
        (λ X → normalTyOf X <:ₜ normalTyOf A)
        eqChan
        sub
  in
  record
    { Gf = allUsedCtx Γ₀
    ; Gf′ = allUsedCtx Γ₁
    ; Γ₀′ = Γ₀
    ; Γ₁ = Γ₁
    ; Γ₁′ = Γ₁
    ; Γout = Γout
    ; U = selectOutNf v i P S
    ; src-remove = remove-allUsedCtx Γ₀
    ; frame-update =
        Frm-Select (allUsedCtx-replace-lin-at x∈ rep)
    ; dst-remove = remove-allUsedCtx Γ₁
    ; ctx-step = Ctx-Select x∈ rep
    ; compat = Compat-Select
    ; effect-aligned = refl
    ; synth = T-Val (TV-Var-Lin take′)
    ; subtype =
        select-app-subtype
          {v₂ = v} {P′ = P} {S′ = S}
          vr
          selSub
    ; leftover = out≈
    }
reduction-preserves-synth-by-tag
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    other-step
    (Act-Close {x = x})
    refl
    (T-App
      (T-Val (TV-Const CT-Close))
      (T-Check (T-Val (TV-Var-Lin take)) sub))
    (Label-Close auin au)
    Ex-Close
    _
  with end-subtype-invert sub
... | eqEnd =
  let
    take′ =
      subst
        (λ X → Γ₀ ⊢ˡ x ∶ X ⊣ Γ₂)
        eqEnd
        take

    rep = take-replace take′
  in
  record
    { Gf = allUsedCtx Γ₀
    ; Gf′ = allUsedCtx Γ₀
    ; Γ₀′ = Γ₀
    ; Γ₁ = Γ₂
    ; Γ₁′ = Γ₂
    ; Γout = Γ₂
    ; U = unitConstNf
    ; src-remove = remove-allUsedCtx Γ₀
    ; frame-update =
        Frm-Close
          (allUsedCtx-replace-used-self
            (take-membership-fresh take′))
    ; dst-remove =
        subst
          (λ X → RemoveCtx Γ₂ X Γ₂)
          (sym (allUsedCtx-take take′))
          (remove-allUsedCtx Γ₂)
    ; ctx-step = Ctx-Close (take-membership-fresh take′) rep
    ; compat = Compat-Close refl
    ; effect-aligned = refl
    ; synth = T-Val (TV-Const CT-Unit)
    ; subtype = <:ₜ-refl (normalTyOf unitConstNf)
    ; leftover = ≈ᵘ-refl
    }
reduction-preserves-synth-by-tag
    {Γ₀ = Γ₀} {Γ₂ = Γ₂}
    other-step
    Act-Fork
    refl
    (T-App
      (T-Val (TV-Const CT-Fork))
      (T-Check (T-Val dv) sub))
    (Label-Fork auin aulbl)
    Ex-Fork
    _
  with strip-value dv
... | G , G′ , rm , dv′ , au =
  record
    { Gf = allUsedCtx Γ₀
    ; Gf′ = allUsedCtx Γ₀
    ; Γ₀′ = Γ₀
    ; Γ₁ = Γ₂
    ; Γ₁′ = Γ₂
    ; Γout = Γ₂
    ; U = unitConstNf
    ; src-remove = remove-allUsedCtx Γ₀
    ; frame-update = Frm-Fork
    ; dst-remove =
        subst
          (λ X → RemoveCtx Γ₂ X Γ₂)
          (sym (allUsedCtx-remove rm))
          (remove-allUsedCtx Γ₂)
    ; ctx-step = Ctx-Fork rm (T-Check (T-Val dv′) sub) au
    ; compat = Compat-Fork refl
    ; effect-aligned = refl
    ; synth = T-Val (TV-Const CT-Unit)
    ; subtype = <:ₜ-refl (normalTyOf unitConstNf)
    ; leftover = ≈ᵘ-refl
    }

reduction-preserves-synth :
  ∀ {n Θ pk m}
    {Γ₀ Γ₂ Γin Γv : Ctx [] n}
    {e₁ : Expr [] n} {e₂ : Expr [] (length Θ + n)}
    {T : NfTy [] (KV pk m)} {ℓ : Label n Θ}
  → (step : e₁ —[ ℓ ]→ e₂)
  → Γ₀ ⊢ e₁ ⇒ T ⊣ Γ₂
  → (lbl : ℓ ⦂ Γin ⇒ Γv)
  → Extract Γ₀ ℓ Γin
  → LinearDisjoint Γ₀ Γv
  → ReductionSynthResult Γin Γv lbl Γ₀ Γ₂ e₂ T
reduction-preserves-synth step =
  reduction-preserves-synth-by-tag
    (direct-match-tag step) step refl

reduction-preserves-check :
  ∀ {n Θ pk m}
    {Γ₀ Γ₂ Γin Γv : Ctx [] n}
    {e₁ : Expr [] n} {e₂ : Expr [] (length Θ + n)}
    {T : NfTy [] (KV pk m)} {ℓ : Label n Θ}
  → (step : e₁ —[ ℓ ]→ e₂)
  → Γ₀ ⊢ e₁ ⇐ T ⊣ Γ₂
  → (lbl : ℓ ⦂ Γin ⇒ Γv)
  → Extract Γ₀ ℓ Γin
  → LinearDisjoint Γ₀ Γv
  → ReductionCheckResult Γin Γv lbl Γ₀ Γ₂ e₂ T
reduction-preserves-check
    step (T-Check source source<:expected) lbl ex disjoint
  with reduction-preserves-synth
         step source lbl ex disjoint
... | record
        { Gf = Gf
        ; Gf′ = Gf′
        ; Γ₀′ = Γ₀′
        ; Γ₁ = Γ₁
        ; Γ₁′ = Γ₁′
        ; Γout = Γout
        ; U = U
        ; src-remove = src-remove
        ; frame-update = frame-update
        ; dst-remove = dst-remove
        ; ctx-step = ctx-step
        ; compat = compat
        ; effect-aligned = effect-aligned
        ; synth = reduct
        ; subtype = reduct<:source
        ; leftover = out≈
        } =
  record
    { Gf = Gf
    ; Gf′ = Gf′
    ; Γ₀′ = Γ₀′
    ; Γ₁ = Γ₁
    ; Γ₁′ = Γ₁′
    ; Γout = Γout
    ; src-remove = src-remove
    ; frame-update = frame-update
    ; dst-remove = dst-remove
    ; ctx-step = ctx-step
    ; compat = compat
    ; effect-aligned = effect-aligned
    ; check = T-Check reduct (<:ₜ-trans reduct<:source source<:expected)
    ; leftover = out≈
    }
