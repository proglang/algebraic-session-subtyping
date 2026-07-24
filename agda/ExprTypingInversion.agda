module ExprTypingInversion where

open import Data.Fin using (Fin)
import Data.Fin.Subset as Subset
open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (suc; _⊔_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; inspect; Reveal_·_is_)
import Relation.Binary.PropositionalEquality as Eq

import Duality
open import Kinds
open import Kits
open import Variance using
  ( Variance
  ; ⊕
  ; ⊝
  ; ⊘
  ; VarianceCovers
  )
import Types
open import Types using (Ty)
open import NormalTypes using
  ( N-Var
  ; N-Arrow
  ; N-Msg
  ; N-ProtoP
  ; NV-Var
  ; nfProtoTy
  ; nfProtoTy-fromNormalProto
  ; nfTyTy-fromNormalTy
  ; toNormalTy
  ; sizeₚ
  )
open import AlgorithmicNFSubtyping using
  ( _<:ₜ_
  ; _<<:ₚ[_]_
  ; <<:ₚ-refl
  ; <:ₜ-sub
  ; <:ₜ-msg
  ; <:ₜ-pair
  ; <:ₜ-poly
  ; <:ₚ′-proto
  ; <:ₚ′-up
  )
open import Subtyping using (_<<:[_]_)
open import ExprSyntax
  using
  ( NfTy
  ; Expr
  ; Value
  ; E-Val
  ; E-App
  ; E-TApp
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
  ; V-Select₂
  ; C-New
  ; C-Receive
  ; C-Send
  ; C-Close
  ; C-Fork
  )
open import ExprNormalTyping
open import TypesProtocolConstructors using
  ( ProtocolConstructors
  ; instantiate
  ; singletonSubst
  ; used
  ; unused
  ; usageVariance
  ; allUsageVariance
  )
open import AlgorithmicNFSubstitution using (msgNF-preserves-<:)
open import AlgorithmicNFComplete using (complete-<<:ₚ)
open import NormalTypesSubstitution
  using
  ( NFSub
  ; wkNFKind-sound
  ; singleNFSub
  ; singleNFSub-sound
  ; substNFTy
    ; substNFTyWith
    ; substNFTy-sound
  )
open import SubstitutionSubtyping using (subst-preserves-≡c)
open import AlgorithmicNFSound using (sound-<<:ₚ)
open import ExprPreservationStep2.SubstitutionLemmas using
  ( singletonSubst-≈ᵥ
  ; subst-preserves-<<:-used⊕
  ; instantiate-unused-independent
  ; swap-<<:
  ; covers-trans
  ; join-left-covers
  ; join-right-covers
  ; joinUsage-used-used≢unused
  )
open import ExprContextReduction
  using
  ( recvChanNf
  ; sendChanNf
  ; selectInNf
  ; selectOutNf
  ; unitLinNf
  ; dualSessNf
  )

open Kits.Syntax Types.Ty-Syntax hiding (Sort)
open Traversal Types.Ty-Traversal
open CTraversal record { fusion = Types.fusion }

infixr 1 _⊎₀_
data _⊎₀_ (A B : Set) : Set where
  inj₁₀ : A → A ⊎₀ B
  inj₂₀ : B → A ⊎₀ B


select₂-inversion :
  ∀ {n k}
    {Γ Γ′ : Ctx [] n}
    {v : Variance} {i : Fin k} {P : NfTy [] KP} {S : NfTy [] SLin}
    {W : NfTy [] TLin}
  → Γ ⊢ᵥ V-Select₂ v i P S ⇒ W ⊣ Γ′
  → (Γ ≡ Γ′)
    × (W ≡ linArrNf
             (selectInNf v i P S)
             (selectOutNf v i P S))
select₂-inversion TV-Select₂ = refl , refl

select₂-shape :
  ∀ {n k}
    {Γ Γ′ : Ctx [] n}
    {v : Variance} {i : Fin k} {P : NfTy [] KP} {S : NfTy [] SLin}
    {A R : NfTy [] SLin}
  → Γ ⊢ᵥ V-Select₂ v i P S ⇒ linArrNf A R ⊣ Γ′
  → Γ ≡ Γ′
    × (A ≡ selectInNf v i P S)
    × (R ≡ selectOutNf v i P S)
select₂-shape {v = v} {i = i} {P = P} {S = S} vr
  with select₂-inversion vr
... | refl , eqSelect
  with linArrNf-injective eqSelect
... | eqA , eqR = refl , eqA , eqR

match-branch-subtype :
  ∀ {k pk m}
    {ss : Subset.Subset k}
    {V : (i : Fin k) → i Subset.∈ ss → NfTy [] (KV pk m)}
    {U : NfTy [] (KV pk m)}
    {sub : (i : Fin k) → (i∈ : i Subset.∈ ss) → V i i∈ <:ₜ U}
    (i : Fin k)
    (i∈ : i Subset.∈ ss)
  → BranchJoin⁺ ss V ≡ just (U , sub)
  → (V i i∈) <:ₜ U
match-branch-subtype {sub = sub} i i∈ bj = sub i i∈

recvChan-subtype :
  ∀ {pk₁ pk₂}
    {T₁ : NfTy [] (KV pk₁ Lin)}
    {T₂ : NfTy [] (KV pk₂ Lin)}
    {S₁ S₂ : NfTy [] SLin}
  → (recvChanNf T₁ S₁) <:ₜ (recvChanNf T₂ S₂)
  → Σ (pk₁ ≡ pk₂) λ where
      refl →
        (T₁ <:ₜ T₂)
        × (S₁ <:ₜ S₂)
recvChan-subtype (<:ₜ-msg (<:ₚ′-up T₁<:T₂) S₁<:S₂) =
  refl , T₁<:T₂ , S₁<:S₂

recvChan-subtype-shape :
  ∀ {pk}
    {A : NfTy [] SLin}
    {T : NfTy [] (KV pk Lin)}
    {S : NfTy [] SLin}
  → A <:ₜ (recvChanNf T S)
  → Σ (NfTy [] (KV pk Lin)) λ T₀ →
      Σ (NfTy [] SLin) λ S₀ →
        (A ≡ recvChanNf T₀ S₀)
        × (T₀ <:ₜ T)
        × (S₀ <:ₜ S)
recvChan-subtype-shape
    (<:ₜ-msg (<:ₚ′-up T₀<:T) S₀<:S) =
  _ , _ , refl , T₀<:T , S₀<:S

sendChan-subtype :
  ∀ {pk₁ pk₂}
    {T₁ : NfTy [] (KV pk₁ Lin)}
    {T₂ : NfTy [] (KV pk₂ Lin)}
    {S₁ S₂ : NfTy [] SLin}
  → (sendChanNf T₁ S₁) <:ₜ (sendChanNf T₂ S₂)
  → Σ (pk₁ ≡ pk₂) λ where
      refl →
        (T₂ <:ₜ T₁)
        × (S₁ <:ₜ S₂)
sendChan-subtype (<:ₜ-msg (<:ₚ′-up T₂<:T₁) S₁<:S₂) =
  refl , T₂<:T₁ , S₁<:S₂

sendChan-subtype-shape :
  ∀ {pk}
    {A : NfTy [] SLin}
    {T : NfTy [] (KV pk Lin)}
    {S : NfTy [] SLin}
  → A <:ₜ (sendChanNf T S)
  → Σ (NfTy [] (KV pk Lin)) λ T₀ →
      Σ (NfTy [] SLin) λ S₀ →
        (A ≡ sendChanNf T₀ S₀)
        × (T <:ₜ T₀)
        × (S₀ <:ₜ S)
sendChan-subtype-shape
    (<:ₜ-msg (<:ₚ′-up T<:T₀) S₀<:S) =
  _ , _ , refl , T<:T₀ , S₀<:S

selectIn-subtype :
  ∀ {k}
    {v₁ v₂ : Variance} {i : Fin k}
    {P₁ P₂ : NfTy [] KP}
    {S₁ S₂ : NfTy [] SLin}
  → (selectInNf v₁ i P₁ S₁) <:ₜ (selectInNf v₂ i P₂ S₂)
  → (v₁ ≡ v₂)
    × (P₂ <<:ₚ[ v₁ ] P₁)
    × (S₁ <:ₜ S₂)
selectIn-subtype
  {v₁ = v₁}
  (<:ₜ-msg (<:ₚ′-proto ss paramRel) Ssub) =
  refl , paramRel , Ssub

selectSetIn-subtype :
  ∀ {k}
    {ss : Subset.Subset k}
    {v₁ v₂ : Variance} {i : Fin k}
    {P₁ P₂ : NfTy [] KP}
    {S₁ S₂ : NfTy [] SLin}
  → (selectSetInTyNf ss v₁ P₁ S₁)
      <:ₜ (selectInNf v₂ i P₂ S₂)
  → (v₁ ≡ v₂)
    × (P₂ <<:ₚ[ v₁ ] P₁)
    × (S₁ <:ₜ S₂)
selectSetIn-subtype
  {v₁ = v₁}
  (<:ₜ-msg (<:ₚ′-proto singleton⊆ss paramRel) Ssub) =
  refl , paramRel , Ssub

selectSetIn-subtype-shape :
  ∀ {k}
    {A : NfTy [] SLin}
    {v : Variance} {i : Fin k}
    {P : NfTy [] KP}
    {S : NfTy [] SLin}
  → A <:ₜ (selectInNf v i P S)
  → Σ (Subset.Subset k) λ ss →
      Σ (NfTy [] KP) λ P₀ →
        Σ (NfTy [] SLin) λ S₀ →
          (i Subset.∈ ss)
          × (A ≡ selectSetInTyNf ss v P₀ S₀)
          × (P <<:ₚ[ v ] P₀)
          × (S₀ <:ₜ S)
selectSetIn-subtype-shape
    {i = i}
    (<:ₜ-msg
      {NP₁ = N-ProtoP ss v P₀}
      {NS₁ = S₀}
      (<:ₚ′-proto singleton⊆ss paramRel)
      Ssub) =
  ss , P₀ , S₀ ,
  singleton⊆ss (x∈⁅x⁆ i) ,
  refl ,
  paramRel ,
  Ssub

covers-refl : ∀ {v} → VarianceCovers v v
covers-refl {v = ⊕} = tt
covers-refl {v = ⊝} = tt
covers-refl {v = ⊘} = tt

materialize-head-used :
  ∀ {Δ}
    (T : Ty (KP ∷ []) KP)
    {u v : Variance}
    {P₁ P₂ : NfTy Δ KP}
  → usageVariance T (here refl) ≡ used u
  → P₂ <<:ₚ[ v ] P₁
  → VarianceCovers v u
  → normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)
       <<:ₚ[ ⊝ ]
    normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)
materialize-head-used T {u = u} {v = v} {P₁} {P₂} uv pu cov =
  complete-<<:ₚ
    (suc (sizeₚ N₁ ⊔ sizeₚ N₂))
    {⊙ = ⊝}
    {T₁ = instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟}
    {T₂ = instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟}
    rawMinus
    {f₁ = Duality.d?⊥}
    {f₂ = Duality.d?⊥}
    {N₁ = N₁}
    {N₂ = N₂}
    eqN₁
    eqN₂
    (n≤1+n _)
  where
  N₁ : NfTy _ KP
  N₁ = normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)

  N₂ : NfTy _ KP
  N₂ = normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)

  eqN₁ :
    nfProtoTy N₁
      ≡
    Types.nf Duality.⊕ Duality.d?⊥ (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)
  eqN₁ =
    nfProtoTy-fromNormalProto
      (Types.nf-normal-proto (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟))

  eqN₂ :
    nfProtoTy N₂
      ≡
    Types.nf Duality.⊕ Duality.d?⊥ (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)
  eqN₂ =
    nfProtoTy-fromNormalProto
      (Types.nf-normal-proto (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟))

  rawPlus :
    instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟
      <<:[ ⊕ ]
    instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟
  rawPlus =
    subst-preserves-<<:-used⊕
      T
      {p = here refl}
      {u = u}
      {v = v}
      {ϕ = singletonSubst ⌞ P₂ ⌟}
      {ψ = singletonSubst ⌞ P₁ ⌟}
      uv
      (singletonSubst-≈ᵥ (sound-<<:ₚ pu))
      cov

  rawMinus :
    instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟
      <<:[ ⊝ ]
    instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟
  rawMinus = swap-<<: {v = ⊕} rawPlus

materialize-head-unused :
  ∀ {Δ}
    (T : Ty (KP ∷ []) KP)
    {P₁ P₂ : NfTy Δ KP}
  → usageVariance T (here refl) ≡ unused
  → normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)
       <<:ₚ[ ⊝ ]
     normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)
materialize-head-unused T {P₁} {P₂} uv =
  subst
    (λ X →
      X <<:ₚ[ ⊝ ]
      normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟))
    (sym eqNf)
    (<<:ₚ-refl {⊙ = ⊝}
      (normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)))
  where
  eqNf :
    normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)
      ≡
    normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)
  eqNf = nfEq eqRaw
    where
    eqConv :
      instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟
        Types.≡c
      instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟
    eqConv =
      instantiate-unused-independent
        T
        {P = ⌞ P₁ ⌟}
        {Q = ⌞ P₂ ⌟}
        uv

    eqRaw :
      ⌞ normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟) ⌟
        ≡
      ⌞ normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟) ⌟
    eqRaw =
      trans
        (nfProtoTy-fromNormalProto
          (Types.nf-normal-proto (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)))
        (trans
          (Types.nf-complete Duality.d?⊥ Duality.d?⊥ eqConv)
          (sym
            (nfProtoTy-fromNormalProto
              (Types.nf-normal-proto (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)))))

mutual

  materializeListNf-sub-used :
    ∀ {Δ}
      (Ts : List (Ty (KP ∷ []) KP))
      {u v : Variance}
      {P₁ P₂ : NfTy Δ KP}
      {S₁ S₂ : NfTy Δ SLin}
    → allUsageVariance Ts (here refl) ≡ used u
    → P₂ <<:ₚ[ v ] P₁
    → VarianceCovers v u
    → S₁ <:ₜ S₂
    → materializeListNf Ts Duality.⊕ P₁ S₁
         <:ₜ
       materializeListNf Ts Duality.⊕ P₂ S₂

  materializeListNf-sub-unused :
    ∀ {Δ}
      (Ts : List (Ty (KP ∷ []) KP))
      {P₁ P₂ : NfTy Δ KP}
      {S₁ S₂ : NfTy Δ SLin}
    → allUsageVariance Ts (here refl) ≡ unused
    → S₁ <:ₜ S₂
    → materializeListNf Ts Duality.⊕ P₁ S₁
         <:ₜ
       materializeListNf Ts Duality.⊕ P₂ S₂

  materializeListNf-sub-used [] ()
  materializeListNf-sub-used (T ∷ Ts) {u = u} {v = v} {P₁} {P₂} {S₁} {S₂} eq pu cov ssub
    with usageVariance T (here refl) | inspect (usageVariance T) (here refl)
       | allUsageVariance Ts (here refl) | inspect (allUsageVariance Ts) (here refl)
       | eq
  ... | unused | Eq.[ eqT ] | used uTs | Eq.[ eqTs ] | refl =
    msgNF-preserves-<:
      (materialize-head-unused T {P₁ = P₁} {P₂ = P₂} eqT)
      (materializeListNf-sub-used Ts eqTs pu cov ssub)
  ... | used uT | Eq.[ eqT ] | unused | Eq.[ eqTs ] | refl =
    msgNF-preserves-<:
      (materialize-head-used T {u = uT} {v = v} {P₁ = P₁} {P₂ = P₂}
        eqT pu (covers-trans cov (join-left-covers {u₂ = unused} refl)))
      (materializeListNf-sub-unused Ts eqTs ssub)
  ... | used uT | Eq.[ eqT ] | used uTs | Eq.[ eqTs ] | eqJoin =
    msgNF-preserves-<:
      (materialize-head-used T {u = uT} {v = v} {P₁ = P₁} {P₂ = P₂}
        eqT pu (covers-trans cov (join-left-covers {u₂ = used uTs} eqJoin)))
      (materializeListNf-sub-used Ts eqTs pu
        (covers-trans cov (join-right-covers {u₂ = uTs} {u₁ = used uT} eqJoin))
        ssub)

  materializeListNf-sub-unused [] _ ssub = ssub
  materializeListNf-sub-unused (T ∷ Ts) {P₁} {P₂} {S₁} {S₂} eq ssub
    with usageVariance T (here refl) | inspect (usageVariance T) (here refl)
       | allUsageVariance Ts (here refl) | inspect (allUsageVariance Ts) (here refl)
       | eq
  ... | unused | Eq.[ eqT ] | unused | Eq.[ eqTs ] | refl =
    msgNF-preserves-<:
      (materialize-head-unused T {P₁ = P₁} {P₂ = P₂} eqT)
      (materializeListNf-sub-unused Ts eqTs ssub)
  ... | used uT | Eq.[ eqT ] | unused | Eq.[ eqTs ] | ()
  ... | used uT | Eq.[ eqT ] | used uTs | Eq.[ eqTs ] | eqJoin =
    ⊥-elim (joinUsage-used-used≢unused eqJoin)

materialize-head-used-input :
  ∀ {Δ}
    (T : Ty (KP ∷ []) KP)
    {u v : Variance}
    {P₁ P₂ : NfTy Δ KP}
  → usageVariance T (here refl) ≡ used u
  → P₁ <<:ₚ[ v ] P₂
  → VarianceCovers v u
  → normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)
       <<:ₚ[ ⊕ ]
    normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)
materialize-head-used-input T {P₁ = P₁} {P₂ = P₂} uv pu cov =
  materialize-head-used
    T
    {P₁ = P₂}
    {P₂ = P₁}
    uv
    pu
    cov

materialize-head-unused-input :
  ∀ {Δ}
    (T : Ty (KP ∷ []) KP)
    {P₁ P₂ : NfTy Δ KP}
  → usageVariance T (here refl) ≡ unused
  → normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₁ ⌟)
       <<:ₚ[ ⊕ ]
    normalizeTy (instantiate ⦃ Kₛ ⦄ Duality.⊕ T ⌞ P₂ ⌟)
materialize-head-unused-input T {P₁ = P₁} {P₂ = P₂} uv =
  materialize-head-unused T {P₁ = P₂} {P₂ = P₁} uv

mutual

  materializeListNf-sub-used-input :
    ∀ {Δ}
      (Ts : List (Ty (KP ∷ []) KP))
      {u v : Variance}
      {P₁ P₂ : NfTy Δ KP}
      {S₁ S₂ : NfTy Δ SLin}
    → allUsageVariance Ts (here refl) ≡ used u
    → P₁ <<:ₚ[ v ] P₂
    → VarianceCovers v u
    → S₁ <:ₜ S₂
    → materializeListNf Ts Duality.⊝ P₁ S₁
         <:ₜ
       materializeListNf Ts Duality.⊝ P₂ S₂

  materializeListNf-sub-unused-input :
    ∀ {Δ}
      (Ts : List (Ty (KP ∷ []) KP))
      {P₁ P₂ : NfTy Δ KP}
      {S₁ S₂ : NfTy Δ SLin}
    → allUsageVariance Ts (here refl) ≡ unused
    → S₁ <:ₜ S₂
    → materializeListNf Ts Duality.⊝ P₁ S₁
         <:ₜ
       materializeListNf Ts Duality.⊝ P₂ S₂

  materializeListNf-sub-used-input [] ()
  materializeListNf-sub-used-input
      (T ∷ Ts)
      {u = u} {v = v}
      {P₁} {P₂} {S₁} {S₂}
      eq pu cov ssub
    with usageVariance T (here refl) | inspect (usageVariance T) (here refl)
       | allUsageVariance Ts (here refl) | inspect (allUsageVariance Ts) (here refl)
       | eq
  ... | unused | Eq.[ eqT ] | used uTs | Eq.[ eqTs ] | refl =
    msgNF-preserves-<:
      (materialize-head-unused-input T {P₁ = P₁} {P₂ = P₂} eqT)
      (materializeListNf-sub-used-input Ts eqTs pu cov ssub)
  ... | used uT | Eq.[ eqT ] | unused | Eq.[ eqTs ] | refl =
    msgNF-preserves-<:
      (materialize-head-used-input
        T
        {u = uT} {v = v}
        {P₁ = P₁} {P₂ = P₂}
        eqT
        pu
        (covers-trans cov (join-left-covers {u₂ = unused} refl)))
      (materializeListNf-sub-unused-input Ts eqTs ssub)
  ... | used uT | Eq.[ eqT ] | used uTs | Eq.[ eqTs ] | eqJoin =
    msgNF-preserves-<:
      (materialize-head-used-input
        T
        {u = uT} {v = v}
        {P₁ = P₁} {P₂ = P₂}
        eqT
        pu
        (covers-trans cov
          (join-left-covers {u₂ = used uTs} eqJoin)))
      (materializeListNf-sub-used-input
        Ts
        eqTs
        pu
        (covers-trans cov
          (join-right-covers {u₂ = uTs} {u₁ = used uT} eqJoin))
        ssub)

  materializeListNf-sub-unused-input [] _ ssub = ssub
  materializeListNf-sub-unused-input
      (T ∷ Ts)
      {P₁} {P₂} {S₁} {S₂}
      eq ssub
    with usageVariance T (here refl) | inspect (usageVariance T) (here refl)
       | allUsageVariance Ts (here refl) | inspect (allUsageVariance Ts) (here refl)
       | eq
  ... | unused | Eq.[ eqT ] | unused | Eq.[ eqTs ] | refl =
    msgNF-preserves-<:
      (materialize-head-unused-input T {P₁ = P₁} {P₂ = P₂} eqT)
      (materializeListNf-sub-unused-input Ts eqTs ssub)
  ... | used uT | Eq.[ eqT ] | unused | Eq.[ eqTs ] | ()
  ... | used uT | Eq.[ eqT ] | used uTs | Eq.[ eqTs ] | eqJoin =
    ⊥-elim (joinUsage-used-used≢unused eqJoin)

select-app-subtype :
  ∀ {n k}
    {Γ Γ′ : Ctx [] n}
    {v₁ v₂ : Variance} {i : Fin k}
    {P : NfTy [] KP} {S : NfTy [] SLin}
    {P′ : NfTy [] KP} {S′ : NfTy [] SLin}
    {A R : NfTy [] SLin}
  → Γ ⊢ᵥ V-Select₂ v₁ i P S ⇒ linArrNf A R ⊣ Γ′
  → (selectInNf v₂ i P′ S′) <:ₜ A
  → (selectOutNf v₂ i P′ S′) <:ₜ R
select-app-subtype
  {v₁ = v₁} {i = i} {P = P} {S = S}
  {P′ = P′} {S′ = S′}
  vr selSub
  with select₂-shape vr
... | refl , refl , refl
  with selectIn-subtype selSub
... | refl , psub , ssub
  with ProtocolConstructors _ v₁ i
... | Ts , inj₁ usedTs =
  materializeListNf-sub-used
    Ts
    usedTs
    psub
    covers-refl
    ssub
... | Ts , inj₂ unusedTs =
  materializeListNf-sub-unused
    Ts
    unusedTs
    ssub

select-set-app-subtype :
  ∀ {n k}
    {ss : Subset.Subset k}
    {Γ Γ′ : Ctx [] n}
    {v₁ v₂ : Variance} {i : Fin k}
    {P : NfTy [] KP} {S : NfTy [] SLin}
    {P′ : NfTy [] KP} {S′ : NfTy [] SLin}
    {A R : NfTy [] SLin}
  → Γ ⊢ᵥ V-Select₂ v₁ i P S ⇒ linArrNf A R ⊣ Γ′
  → (selectSetInTyNf ss v₂ P′ S′)
      <:ₜ A
  → (selectOutNf v₂ i P′ S′)
      <:ₜ R
select-set-app-subtype
  {v₁ = v₁} {i = i} {P = P} {S = S}
  {P′ = P′} {S′ = S′}
  vr selSub
  with select₂-shape vr
... | refl , refl , refl
  with selectSetIn-subtype selSub
... | refl , psub , ssub
  with ProtocolConstructors _ v₁ i
... | Ts , inj₁ usedTs =
  materializeListNf-sub-used
    Ts
    usedTs
    psub
    covers-refl
    ssub
... | Ts , inj₂ unusedTs =
  materializeListNf-sub-unused
    Ts
    unusedTs
    ssub

tv-const-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {c pk m}
    {T : NfTy Δ (KV pk m)}
  → Γ₁ ⊢ᵥ Value.V-Const c ⇒ T ⊣ Γ₂
  → ConstTy c T × (Γ₁ ≡ Γ₂)
tv-const-inversion (TV-Const cT) = cT , refl

tv-var-inversion :
  ∀ {Δ n pk m}
    {Γ₁ Γ₂ : Ctx Δ n}
    {x : Fin n}
    {T : NfTy Δ (KV pk m)}
  → Γ₁ ⊢ᵥ Value.V-Var x ⇒ T ⊣ Γ₂
  → Σ (m ≡ Lin) (λ where
       refl → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂)
    ⊎₀ (Σ (m ≡ Un) (λ where
       refl → (Γ₁ ∋ᵘ x ∶ T) × (Γ₁ ≡ Γ₂)))
tv-var-inversion (TV-Var-Lin take) = inj₁₀ (refl , take)
tv-var-inversion (TV-Var-Un x∈) = inj₂₀ (refl , (x∈ , refl))

tv-abs-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {pk₁}
    {A : NfTy Δ (KV pk₁ Lin)}
    {e : Expr Δ (suc n)}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Abs A e ⇒ W ⊣ Γ₂
  → Σ PreKind (λ pk₂ →
      Σ Multiplicity (λ m₂ →
        Σ (NfTy Δ (KV pk₂ m₂)) λ U →
          (W ≡ N-Arrow {m = Lin} A U)
          × ((A ∷ˡ Γ₁) ⊢ e ⇒ U ⊣ used∷ {T = A} Γ₂)))
tv-abs-inversion (TV-Abs {pk₂ = pk₂} {m₂ = m₂} {U = U} d) =
  pk₂ , m₂ , U , refl , d

tv-rec-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {pk₁ pk₂ m₁ m₂}
    {A : NfTy Δ (KV pk₁ m₁)} {B : NfTy Δ (KV pk₂ m₂)}
    {v : Value Δ (suc n)}
    {W : NfTy Δ (KV KT Un)}
  → Γ₁ ⊢ᵥ Value.V-Rec A B v ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂)
    × ((W ≡ N-Arrow {m = Un} A B)
      × ((N-Arrow {m = Un} A B ∷ᵘ Γ₁)
          ⊢ E-Val v ⇐ N-Arrow {m = Un} A B
          ⊣ (N-Arrow {m = Un} A B ∷ᵘ Γ₁)))
tv-rec-inversion (TV-Rec d) = refl , refl , d

tv-tabs-inversion :
  ∀ {Δ n K m}
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Value (K ∷ Δ) n}
    {W : NfTy Δ (KV KT m)}
  → Γ₁ ⊢ᵥ Value.V-TAbs K v ⇒ W ⊣ Γ₂
  → Σ (NfTy (K ∷ Δ) (KV KT m)) λ T →
      (W ≡ polyNf T) × (wkCtx {K = K} Γ₁ ⊢ᵥ v ⇒ T ⊣ wkCtx Γ₂)
tv-tabs-inversion (TV-TAbs d) = _ , refl , d

tv-pair-inversion :
  ∀ {Δ n m}
    {Γ₁ Γ₃ : Ctx Δ n}
    {u v : Value Δ n}
    {W : NfTy Δ (KV KT m)}
  → Γ₁ ⊢ᵥ Value.V-Pair u v ⇒ W ⊣ Γ₃
  → Σ PreKind λ pk₁ →
      Σ PreKind λ pk₂ →
      Σ (NfTy Δ (KV pk₁ m)) λ T →
      Σ (NfTy Δ (KV pk₂ m)) λ U →
      Σ (Ctx Δ n) λ Γ₂ →
        (W ≡ pairNf T U) × ((Γ₁ ⊢ᵥ u ⇒ T ⊣ Γ₂) × (Γ₂ ⊢ᵥ v ⇒ U ⊣ Γ₃))
tv-pair-inversion (TV-Pair {pk₁ = pk₁} {pk₂ = pk₂} d₁ d₂) =
  pk₁ , pk₂ , _ , _ , _ , refl , (d₁ , d₂)

tv-receive₁-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {pk} {T : NfTy Δ (KV pk Lin)}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Receive₁ T ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ receive1Nf T)
tv-receive₁-inversion TV-Receive₁ = refl , refl

tv-receive₂-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {pk} {T : NfTy Δ (KV pk Lin)}
    {S : NfTy Δ SLin}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Receive₂ T S ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ receiveNf T S)
tv-receive₂-inversion TV-Receive₂ = refl , refl

tv-send₁-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {pk} {T : NfTy Δ (KV pk Lin)}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Send₁ T ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ send1Nf T)
tv-send₁-inversion TV-Send₁ = refl , refl

tv-send₂-inversion :
  ∀ {Δ n}
    {Γ₁ Γ₂ : Ctx Δ n}
    {pk} {T : NfTy Δ (KV pk Lin)}
    {S : NfTy Δ SLin}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Send₂ T S ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ sendNf T S)
tv-send₂-inversion TV-Send₂ = refl , refl

tv-select₁-inversion :
  ∀ {Δ n k}
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Variance}
    {i : Fin k}
    {P : NfTy Δ KP}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Select₁ v i P ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ select1Nf v i P)
tv-select₁-inversion TV-Select₁ = refl , refl

tv-select₂-inversion :
  ∀ {Δ n k}
    {Γ₁ Γ₂ : Ctx Δ n}
    {v : Variance}
    {i : Fin k}
    {P : NfTy Δ KP}
    {S : NfTy Δ SLin}
    {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ Value.V-Select₂ v i P S ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ selectNf v i P S)
tv-select₂-inversion TV-Select₂ = refl , refl
