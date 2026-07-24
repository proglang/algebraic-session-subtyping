module ExprPreservationStep2.ContextLemmas where

open import Data.Fin using (Fin)
open import Data.List using ([])
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

import Duality
open import Kinds
open import Types using (Ty)
open import NormalTypes using (N-Sub; N-End)
open import ExprNormalTyping using
  ( normalizeTy
  ; EndLin
  ; Ctx
  ; B-Lin
  ; B-Used
  ; ∅
  ; _▻_
  ; _∋ˡ_∶_
  ; _∋ᵘ_∶_
  ; _⊢ˡ_∶_⊣_
  ; hereˡ
  ; thereˡˡ
  ; thereˡᵘ
  ; thereˡ✖
  ; hereᵘ
  ; thereᵘˡ
  ; thereᵘᵘ
  ; thereᵘ✖
  ; take-here
  ; take-thereˡ
  ; take-thereᵘ
  ; take-there✖
  ; _∷ˡ_
  ; _∷ᵘ_
  ; used∷
  )
open import AlgorithmicNFSubtyping using (_<:ₜ_; <:ₜ-sub; <:ₜ-end)
open import ExprSyntax using (NfTy; Value)
open import ExprSemantics
open import ExprContextReduction using
  ( RemoveCtx
  ; RM-∅
  ; RM-drop
  ; RM-allused
  ; RM-lin
  ; RM-un
  ; ReplaceAt
  ; Extract
  ; FrameCtx
  ; FC-∅
  ; FC-allused
  ; FC-live
  ; FC-frame
  ; FC-un
  ; LinearDisjoint
  ; LD-∅
  ; LD-used-used
  ; LD-used-live
  ; LD-live-used
  ; LD-un-un
  ; allUsedCtx
  ; Ex-β
  ; Ex-Fork
  ; Ex-New
  ; Ex-Close
  )
import ExprContextReduction

take-replace :
  ∀ {n pk}
    {Γ₀ Γ₁ : Ctx [] n}
    {x : Fin n} {T : NfTy [] (KV pk Lin)}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₁
  → ReplaceAt Γ₀ x (B-Used T) Γ₁
take-replace take-here = ExprContextReduction.R-here
take-replace (take-thereˡ take) = ExprContextReduction.R-there (take-replace take)
take-replace (take-thereᵘ take) = ExprContextReduction.R-there (take-replace take)
take-replace (take-there✖ take) = ExprContextReduction.R-there (take-replace take)

take-replace-lin :
  ∀ {n pk pk′}
    {Γ₀ Γ₂ : Ctx [] n}
    {x : Fin n} {T : NfTy [] (KV pk Lin)} {U : NfTy [] (KV pk′ Lin)}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₂
  → Σ (Ctx [] n) λ Γ₁ → ReplaceAt Γ₀ x (B-Lin U) Γ₁
take-replace-lin {U = U} (take-here {Γ = Γ}) =
  U ∷ˡ Γ , ExprContextReduction.R-here
take-replace-lin {U = U} (take-thereˡ {U = V} take)
  with take-replace-lin {U = U} take
... | Γ₁ , rep = V ∷ˡ Γ₁ , ExprContextReduction.R-there rep
take-replace-lin {U = U} (take-thereᵘ {U = V} take)
  with take-replace-lin {U = U} take
... | Γ₁ , rep = V ∷ᵘ Γ₁ , ExprContextReduction.R-there rep
take-replace-lin {U = U} (take-there✖ take)
  with take-replace-lin {U = U} take
... | Γ₁ , rep = used∷ Γ₁ , ExprContextReduction.R-there rep

allUsedCtx-take :
  ∀ {n pk}
    {Γ₀ Γ₁ : Ctx [] n}
    {x : Fin n}
    {T : NfTy [] (KV pk Lin)}
  → Γ₀ ⊢ˡ x ∶ T ⊣ Γ₁
  → allUsedCtx Γ₀ ≡ allUsedCtx Γ₁
allUsedCtx-take take-here = refl
allUsedCtx-take (take-thereˡ take)
  rewrite allUsedCtx-take take = refl
allUsedCtx-take (take-thereᵘ take)
  rewrite allUsedCtx-take take = refl
allUsedCtx-take (take-there✖ take)
  rewrite allUsedCtx-take take = refl

allUsedCtx-remove :
  ∀ {n}
    {Γ₀ G Γ₁ : Ctx [] n}
  → RemoveCtx Γ₀ G Γ₁
  → allUsedCtx Γ₀ ≡ allUsedCtx Γ₁
allUsedCtx-remove RM-∅ = refl
allUsedCtx-remove (RM-drop r)
  rewrite allUsedCtx-remove r = refl
allUsedCtx-remove (RM-allused r)
  rewrite allUsedCtx-remove r = refl
allUsedCtx-remove (RM-lin r)
  rewrite allUsedCtx-remove r = refl
allUsedCtx-remove (RM-un r)
  rewrite allUsedCtx-remove r = refl

allUsedCtx-replace-lin-at :
  ∀ {n pk pk′}
    {Γ₀ Γ₁ : Ctx [] n}
    {x : Fin n} {T : NfTy [] (KV pk Lin)} {U : NfTy [] (KV pk′ Lin)}
  → Γ₀ ∋ˡ x ∶ T
  → ReplaceAt Γ₀ x (B-Lin U) Γ₁
  → ReplaceAt (allUsedCtx Γ₀) x (B-Used U) (allUsedCtx Γ₁)
allUsedCtx-replace-lin-at hereˡ ExprContextReduction.R-here = ExprContextReduction.R-here
allUsedCtx-replace-lin-at (thereˡˡ x∈) (ExprContextReduction.R-there rep) =
  ExprContextReduction.R-there (allUsedCtx-replace-lin-at x∈ rep)
allUsedCtx-replace-lin-at (thereˡᵘ x∈) (ExprContextReduction.R-there rep) =
  ExprContextReduction.R-there (allUsedCtx-replace-lin-at x∈ rep)
allUsedCtx-replace-lin-at (thereˡ✖ x∈) (ExprContextReduction.R-there rep) =
  ExprContextReduction.R-there (allUsedCtx-replace-lin-at x∈ rep)

allUsedCtx-replace-used-self :
  ∀ {n pk}
    {Γ : Ctx [] n}
    {x : Fin n}
    {T : NfTy [] (KV pk Lin)}
  → Γ ∋ˡ x ∶ T
  → ReplaceAt (allUsedCtx Γ) x (B-Used T) (allUsedCtx Γ)
allUsedCtx-replace-used-self hereˡ = ExprContextReduction.R-here
allUsedCtx-replace-used-self (thereˡˡ x∈) =
  ExprContextReduction.R-there (allUsedCtx-replace-used-self x∈)
allUsedCtx-replace-used-self (thereˡᵘ x∈) =
  ExprContextReduction.R-there (allUsedCtx-replace-used-self x∈)
allUsedCtx-replace-used-self (thereˡ✖ x∈) =
  ExprContextReduction.R-there (allUsedCtx-replace-used-self x∈)

allUsedCtx-merge :
  ∀ {n}
    {Γx Γv Γ₁ : Ctx [] n}
  → FrameCtx Γx Γv Γ₁
  → allUsedCtx Γx ≡ allUsedCtx Γ₁
allUsedCtx-merge merge = sym (ExprContextReduction.allUsed-merge merge)

end-subtype-invert :
  ∀ {U : NfTy [] SLin}
  → U <:ₜ (normalizeTy EndLin)
  → U ≡ normalizeTy EndLin
end-subtype-invert {U = N-Sub _ N-End} (<:ₜ-sub <:ₜ-end) = refl

remove-disjoint :
  ∀ {n}
    {Γ₀ Γg Γ₂ Γv : Ctx [] n}
  → RemoveCtx Γ₀ Γg Γ₂
  → LinearDisjoint Γ₀ Γv
  → LinearDisjoint Γ₂ Γv
remove-disjoint RM-∅ LD-∅ = LD-∅
remove-disjoint (RM-drop r) (LD-live-used ld) = LD-live-used (remove-disjoint r ld)
remove-disjoint (RM-allused r) (LD-used-used ld) = LD-used-used (remove-disjoint r ld)
remove-disjoint (RM-allused r) (LD-used-live ld) = LD-used-live (remove-disjoint r ld)
remove-disjoint (RM-lin r) (LD-live-used ld) = LD-used-used (remove-disjoint r ld)
remove-disjoint (RM-un r) (LD-un-un ld) = LD-un-un (remove-disjoint r ld)

remove-membership :
  ∀ {n pk}
    {Γ₀ G Γ₂ : Ctx [] n}
    {x : Fin n} {T : NfTy [] (KV pk Lin)}
  → RemoveCtx Γ₀ G Γ₂
  → Γ₂ ∋ˡ x ∶ T
  → Γ₀ ∋ˡ x ∶ T
remove-membership (RM-drop r) hereˡ = hereˡ
remove-membership (RM-drop r) (thereˡˡ x∈) = thereˡˡ (remove-membership r x∈)
remove-membership (RM-lin r) (thereˡ✖ x∈) = thereˡˡ (remove-membership r x∈)
remove-membership (RM-un r) (thereˡᵘ x∈) = thereˡᵘ (remove-membership r x∈)
remove-membership (RM-allused r) (thereˡ✖ x∈) = thereˡ✖ (remove-membership r x∈)

remove-membership-un :
  ∀ {n pk}
    {Γ₀ G Γ₂ : Ctx [] n}
    {x : Fin n} {T : NfTy [] (KV pk Un)}
  → RemoveCtx Γ₀ G Γ₂
  → Γ₂ ∋ᵘ x ∶ T
  → Γ₀ ∋ᵘ x ∶ T
remove-membership-un (RM-un r) hereᵘ = hereᵘ
remove-membership-un (RM-drop r) (thereᵘˡ x∈) = thereᵘˡ (remove-membership-un r x∈)
remove-membership-un (RM-lin r) (thereᵘ✖ x∈) = thereᵘˡ (remove-membership-un r x∈)
remove-membership-un (RM-un r) (thereᵘᵘ x∈) = thereᵘᵘ (remove-membership-un r x∈)
remove-membership-un (RM-allused r) (thereᵘ✖ x∈) = thereᵘ✖ (remove-membership-un r x∈)

extract-membership :
  ∀ {n pk}
    {Γ₀ G Γr : Ctx [] n}
    {x : Fin n} {T : NfTy [] (KV pk Lin)}
  → RemoveCtx Γ₀ G Γr
  → G ∋ˡ x ∶ T
  → Γ₀ ∋ˡ x ∶ T
extract-membership (RM-lin r) hereˡ = hereˡ
extract-membership (RM-lin r) (thereˡˡ x∈) = thereˡˡ (extract-membership r x∈)
extract-membership (RM-drop r) (thereˡ✖ x∈) = thereˡˡ (extract-membership r x∈)
extract-membership (RM-un r) (thereˡᵘ x∈) = thereˡᵘ (extract-membership r x∈)
extract-membership (RM-allused r) (thereˡ✖ x∈) = thereˡ✖ (extract-membership r x∈)

remove-self-allUsed :
  ∀ {n}
    {Γ₀ G : Ctx [] n}
  → RemoveCtx Γ₀ G Γ₀
  → G ≡ allUsedCtx Γ₀
remove-self-allUsed RM-∅ = refl
remove-self-allUsed (RM-drop r)
  rewrite remove-self-allUsed r = refl
remove-self-allUsed (RM-allused r)
  rewrite remove-self-allUsed r = refl
remove-self-allUsed (RM-un r)
  rewrite remove-self-allUsed r = refl

extract-beta-eq :
  ∀ {n}
    {Γ₀ Γin : Ctx [] n}
  → Extract Γ₀ ExprSemantics.L-β Γin
  → Γin ≡ allUsedCtx Γ₀
extract-beta-eq Ex-β = refl

extract-fork-eq :
  ∀ {n}
    {Γ₀ Γin : Ctx [] n} {v : Value [] n}
  → Extract Γ₀ (ExprSemantics.L-Fork v) Γin
  → Γin ≡ allUsedCtx Γ₀
extract-fork-eq Ex-Fork = refl

extract-new-eq :
  ∀ {n}
    {Γ₀ Γin : Ctx [] n} {S : Ty [] SLin}
  → Extract Γ₀ (ExprSemantics.L-New S) Γin
  → Γin ≡ allUsedCtx Γ₀
extract-new-eq Ex-New = refl

extract-close-eq :
  ∀ {n}
    {Γ₀ Γin : Ctx [] n} {x : Fin n}
  → Extract Γ₀ (ExprSemantics.L-Close x) Γin
  → Γin ≡ allUsedCtx Γ₀
extract-close-eq Ex-Close = refl
