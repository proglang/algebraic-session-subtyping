module ExprDoubleSubstitutionPreservationFresh where

open import Data.Fin using (zero; suc)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import Ext using (ext)
open import Kinds using (Kind; KV; Lin)
open import AlgorithmicNFSubtyping using (_<:ₜ_)
open import ExprSyntax using (NfTy; Expr; Value)
open import ExprSubstitution using
  ( doubleSub
  ; singleSub
  ; substExpr₂
  )
open import ExprNormalTyping using
  ( B-Used
  ; Ctx
  ; _▻_
  ; _∷ˡ_
  ; normalTyOf
  ; _⊢ᵥ_⇒_⊣_
  ; _⊢_⇒_⊣_
  )
open import ExprContextShape using
  ( drop-lin-used
  ; synth-preserves-~Ctx
  )
open import ExprContextProperties using (RemoveCtx; strip-rm-lin)
open import ExprTypingStripFresh using
  ( strip-value
  ; strip-synth
  )
open import ExprTypingStrengthening using
  ( _<:Γ_
  ; <:-sub-lin
  ; <:Γ-refl
  ; used-tail-<:Γ
  ; lin2-used2-head-rigid
  ; coherent-strengthened-output
  ; strengthen-synth
  )
open import ExprSubstitutionPreservationFresh using
  ( _⊢σ_∶_⊣_
  ; S-Lin
  ; tailSub
  ; cast-substitution-relation
  ; remove-to-frame
  ; swapFrameCtx
  ; tail-singleSub-identitySub
  ; identity-substitution-canonical
  ; substitution-preserves-synth
  ; allUsed-substitution-target
  )

tail-doubleSub-singleSub :
  ∀ {Δ : List Kind} {n : ℕ}
    (u v : Value Δ n)
  → tailSub (doubleSub u v) ≡ singleSub v
tail-doubleSub-singleSub u v =
  ext _ _ λ where
    zero → refl
    (suc x) → refl

double-substitution-relation :
  ∀ {Δ n pkT pkU}
    {Γ₁ Γ₂ Γ₃ Γ₄ G : Ctx Δ n}
    {T : NfTy Δ (KV pkT Lin)}
    {U : NfTy Δ (KV pkU Lin)}
    {u v : Value Δ n}
  → Γ₁ ⊢ᵥ u ⇒ T ⊣ Γ₂
  → Γ₂ ⊢ᵥ v ⇒ U ⊣ Γ₃
  → RemoveCtx Γ₃ G Γ₄
  → Γ₁ ⊢σ doubleSub u v ∶ (T ∷ˡ (U ∷ˡ G)) ⊣ Γ₄
double-substitution-relation {u = u} {v = v} du dv rm
  with strip-value du
... | Gu , Gu′ , rmu , du′ , auu
  with strip-value dv
... | Gv , Gv′ , rmv , dv′ , auv =
  S-Lin
    (swapFrameCtx (remove-to-frame rmu))
    du′
    auu
    (cast-substitution-relation
      (sym (tail-doubleSub-singleSub u v))
      (S-Lin
        (swapFrameCtx (remove-to-frame rmv))
        dv′
        auv
        (cast-substitution-relation
          (sym (tail-singleSub-identitySub v))
          (identity-substitution-canonical
            (remove-to-frame rm)))))

DoubleExpressionSubstitutionPreservesTyping : Set
DoubleExpressionSubstitutionPreservesTyping =
  ∀ {Δ n pkT pkU pkV mV}
    {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx Δ n}
    {T : NfTy Δ (KV pkT Lin)}
    {U : NfTy Δ (KV pkU Lin)}
    {V : NfTy Δ (KV pkV mV)}
    {u v : Value Δ n}
    {e : Expr Δ (Data.Nat.suc (Data.Nat.suc n))}
  → Γ₁ ⊢ᵥ u ⇒ T ⊣ Γ₂
  → Γ₂ ⊢ᵥ v ⇒ U ⊣ Γ₃
  → (T ∷ˡ (U ∷ˡ Γ₃)) ⊢ e ⇒ V
      ⊣ (B-Used T ▻ (B-Used U ▻ Γ₄))
  → Γ₁ ⊢ substExpr₂ e u v ⇒ V ⊣ Γ₄

double-expression-substitution-preserves-typing :
  DoubleExpressionSubstitutionPreservesTyping
double-expression-substitution-preserves-typing du dv body
  with strip-synth body
... | Gbody , Gout , rbody , body′ , au
  with strip-rm-lin rbody
... | Gtail , refl , rtail
  with strip-rm-lin rtail
... | G , refl , rm
  with substitution-preserves-synth
         (double-substitution-relation du dv rm)
         body′
... | Γactual , σfinal , result , residual
  with allUsed-substitution-target au σfinal
... | refl = result

-- A pair-elimination body can be replayed at component subtypes without
-- changing the tail context.  This is the two-binder analogue of
-- `strengthen-substitution-binder`; keeping it here makes the result usable
-- by reduction preservation without importing the legacy postulate.

record DoubleBinderStrengtheningResult
    {Δ : List Kind}
    {n : ℕ}
    {pkT pkU pkV : Kinds.PreKind}
    {mV : Kinds.Multiplicity}
    (Γin : Ctx Δ n)
    (e : Expr Δ (Data.Nat.suc (Data.Nat.suc n)))
    (Tactual : NfTy Δ (KV pkT Lin))
    (Uactual : NfTy Δ (KV pkU Lin))
    (Vexpected : NfTy Δ (KV pkV mV))
    (Γout : Ctx Δ n) : Set where
  field
    actualType : NfTy Δ (KV pkV mV)
    derivation :
      (Tactual ∷ˡ (Uactual ∷ˡ Γin)) ⊢ e ⇒ actualType
        ⊣ (B-Used Tactual ▻ (B-Used Uactual ▻ Γout))
    type-preservation : normalTyOf actualType <:ₜ normalTyOf Vexpected

strengthen-double-binder :
  ∀ {Δ n pkT pkU pkV mV}
    {Γin Γout : Ctx Δ n}
    {T T′ : NfTy Δ (KV pkT Lin)}
    {U U′ : NfTy Δ (KV pkU Lin)}
    {V : NfTy Δ (KV pkV mV)}
    {e : Expr Δ (Data.Nat.suc (Data.Nat.suc n))}
  → normalTyOf T′ <:ₜ normalTyOf T
  → normalTyOf U′ <:ₜ normalTyOf U
  → (T ∷ˡ (U ∷ˡ Γin)) ⊢ e ⇒ V
      ⊣ (B-Used T ▻ (B-Used U ▻ Γout))
  → DoubleBinderStrengtheningResult Γin e T′ U′ V Γout
strengthen-double-binder {T′ = T′} {U′ = U′} T′<:T U′<:U body
  with strengthen-synth
         (<:-sub-lin T′<:T (<:-sub-lin U′<:U <:Γ-refl))
         body
... | V′ , Γbody′ , body′ , V′<:V , relbody
  with used-tail-<:Γ relbody
... | Tused , Γused′ , eqT , relused
  with used-tail-<:Γ relused
... | Uused , Γout′ , eqU , relout
  with subst
         (λ Γ → (T′ ∷ˡ (U′ ∷ˡ _)) ⊢ _ ⇒ V′ ⊣ Γ)
         (trans eqT (cong (B-Used Tused ▻_) eqU))
         body′
... | body″
  with lin2-used2-head-rigid body″
... | refl , refl
  with coherent-strengthened-output
         (drop-lin-used (drop-lin-used (synth-preserves-~Ctx body″)))
         (drop-lin-used (drop-lin-used (synth-preserves-~Ctx body)))
         relout
         <:Γ-refl
... | refl =
  record
    { actualType = V′
    ; derivation = body″
    ; type-preservation = V′<:V
    }
