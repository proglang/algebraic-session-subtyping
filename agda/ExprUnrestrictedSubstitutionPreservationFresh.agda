module ExprUnrestrictedSubstitutionPreservationFresh where

open import Data.Fin using (suc)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Kinds using (Kind; PreKind; Multiplicity; KV; KT; Un)
open import AlgorithmicNFSubtyping using (_<:ₜ_)
open import ExprSyntax using (NfTy; Value; E-Val; V-Rec)
open import ExprSubstitution using
  ( singleSub
  ; substValue
  )
open import ExprNormalTyping using
  ( Ctx
  ; _∷ᵘ_
  ; unArrNf
  ; _⊢ᵥ_⇒_⊣_
  ; TV-Rec
  ; T-Val
  ; T-Check
  )
open import ExprContextProperties using
  ( AllUsed
  ; FrameCtx
  ; RemoveCtx
  ; allUsedCtx
  ; allUsedCtx-AllUsed
  ; remove-allUsedCtx
  ; remove-unique
  ; strip-rm-un
  )
open import ExprContextShape using (value-preserves-~Ctx)
open import ExprTypingStripFresh using
  ( allUsed-shape-stable
  ; strip-value
  ; strip-check
  )
open import ExprSubstitutionPreservationFresh using
  ( _≈ᵘ_
  ; ≈ᵘ-refl
  ; SynthResult
  ; _⊢σ_∶_⊣_
  ; S-Un
  ; tail-singleSub-identitySub
  ; cast-substitution-relation
  ; remove-to-frame
  ; identity-substitution-canonical
  ; substitution-preserves-check
  ; allUsed-substitution-target
  )

-- A value derivation that leaves its context unchanged can be replayed on
-- the all-used form of that context.  This is exactly the premise needed for
-- an unrestricted image in the simultaneous-substitution relation.
value-on-allUsed :
  ∀ {Δ n pk m}
    {Γ : Ctx Δ n}
    {v : Value Δ n}
    {T : NfTy Δ (KV pk m)}
  → Γ ⊢ᵥ v ⇒ T ⊣ Γ
  → allUsedCtx Γ ⊢ᵥ v ⇒ T ⊣ allUsedCtx Γ
value-on-allUsed {Γ = Γ} d
  with strip-value d
... | G , G′ , rm , d′ , au
  with remove-unique rm (remove-allUsedCtx Γ)
... | refl
  with allUsed-shape-stable
         (allUsedCtx-AllUsed Γ)
         (value-preserves-~Ctx d′)
... | refl = d′

unrestricted-single-substitution-relation :
  ∀ {Δ n pk}
    {Γ G : Ctx Δ n}
    {T : NfTy Δ (KV pk Un)}
    {v : Value Δ n}
  → Γ ⊢ᵥ v ⇒ T ⊣ Γ
  → RemoveCtx Γ G Γ
  → Γ ⊢σ singleSub v ∶ (T ∷ᵘ G) ⊣ Γ
unrestricted-single-substitution-relation {v = v} dv rm =
  S-Un
    (value-on-allUsed dv)
    (cast-substitution-relation
      (sym (tail-singleSub-identitySub v))
      (identity-substitution-canonical
        (remove-to-frame rm)))

-- Unfolding a recursive value may reveal a value whose synthesized type is
-- a proper subtype of the recursive annotation.  Consequently the trusted
-- statement uses SynthResult rather than claiming the legacy (false in
-- general) exact-type conclusion.
record RecursiveUnfoldingResult
    {Δ : List Kind}
    {n : ℕ}
    {pkT pkU : PreKind}
    {mT mU : Multiplicity}
    (Γ : Ctx Δ n)
    (v : Value Δ n)
    (T : NfTy Δ (KV pkT mT))
    (U : NfTy Δ (KV pkU mU)) : Set where
  field
    actualType : NfTy Δ (KV KT Un)
    derivation : Γ ⊢ᵥ v ⇒ actualType ⊣ Γ
    type-preservation :
      actualType
        <:ₜ
      (unArrNf T U)

recursive-unfolding-preserves-value :
  ∀ {Δ n pkT pkU mT mU}
    {Γ : Ctx Δ n}
    {T : NfTy Δ (KV pkT mT)}
    {U : NfTy Δ (KV pkU mU)}
    {v : Value Δ (Data.Nat.suc n)}
  → Γ ⊢ᵥ V-Rec T U v ⇒ unArrNf T U ⊣ Γ
  → RecursiveUnfoldingResult
      Γ
      (substValue v (V-Rec T U v))
      T U
recursive-unfolding-preserves-value
    d@(TV-Rec body)
  with strip-check body
... | Gfull , Gout , rm , body′ , au
  with strip-rm-un rm
... | G , refl , rtail
  with substitution-preserves-check
         (unrestricted-single-substitution-relation d rtail)
         body′
... | Γactual , σfinal , T-Check (T-Val value′) sub , residual
  with allUsed-substitution-target au σfinal
... | refl =
  record
    { actualType = _
    ; derivation = value′
    ; type-preservation = sub
    }

recursive-unfolding-preserves-typing :
  ∀ {Δ n pkT pkU mT mU}
    {Γ : Ctx Δ n}
    {T : NfTy Δ (KV pkT mT)}
    {U : NfTy Δ (KV pkU mU)}
    {v : Value Δ (Data.Nat.suc n)}
  → Γ ⊢ᵥ V-Rec T U v ⇒ unArrNf T U ⊣ Γ
  → SynthResult
      Γ
      (E-Val (substValue v (V-Rec T U v)))
      (unArrNf T U)
      Γ
recursive-unfolding-preserves-typing d
  with recursive-unfolding-preserves-value d
... | record
        { actualType = actualType
        ; derivation = derivation
        ; type-preservation = sub
        } =
  record
    { actualType = actualType
    ; Γactual = _
    ; derivation = T-Val derivation
    ; type-preservation = sub
    ; leftover = ≈ᵘ-refl
    }
