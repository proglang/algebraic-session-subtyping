module ExprPreservationStep2.MaterializeProperties where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

import Duality
open import Kinds
open import Kits
open import Variance using (Variance)
import Types
open import Types using (Ty)
import TypesProtocolConstructors
open import TypesProtocolConstructors using (ProtocolConstructors; instantiate)
open import NormalTypes using
  ( N-Normal
  ; N-Var
  ; NV-Var
  ; nfProtoTy-fromNormalProto
  ; toNormalProto
  ; toNormalTy
  )
open import ExprSyntax using (NfTy)
open import ExprNormalTyping
open import NormalTypesSubstitution using
  ( NFSub
  ; nfSubTy
  ; wkNFSub
  ; singleNFSub
  ; singleNFSub-sound
  ; wkNFKind-sound
  ; substNFTy
  ; substNFProtoWith
  ; substNFTyWith
  ; substNFProto-sound
  ; substNFTy-sound
  )
open import SubstitutionSubtyping using (subst-preserves-≡c)
open import ExprPreservationStep2.SubstitutionLemmas using
  ( instantiate-compose
  ; materializeListNf-raw
  )

open Kits.Syntax Types.Ty-Syntax hiding (Sort)
open Traversal Types.Ty-Traversal
open CTraversal record { fusion = Types.fusion }

substNFProtoWith-normalizeTy :
  ∀ {Δ₁ Δ₂}
    (σ : NFSub Δ₁ Δ₂)
    (P : Ty Δ₁ KP)
  → substNFProtoWith σ (normalizeTy P)
      ≡ normalizeTy (P ⋯ nfSubTy σ)
substNFProtoWith-normalizeTy σ P = nfEq raw
  where
  eqcNorm : ⌞ normalizeTy P ⌟ Types.≡c P
  eqcNorm =
    Types.≡c-trns
      (Types.≡c-refl-eq (nfProtoTy-fromNormalProto (Types.nf-normal-proto P)))
      (Types.nf-sound+ P)

  eqcSubst : (⌞ normalizeTy P ⌟ ⋯ nfSubTy σ) Types.≡c (P ⋯ nfSubTy σ)
  eqcSubst =
    subst-preserves-≡c eqcNorm (nfSubTy σ)

  raw :
    ⌞ substNFProtoWith σ (normalizeTy P) ⌟
      ≡
    ⌞ normalizeTy (P ⋯ nfSubTy σ) ⌟
  raw =
    trans
      (substNFProto-sound σ (normalizeTy P))
      (trans
        (Types.nf-complete Duality.d?⊥ Duality.d?⊥ eqcSubst)
        (sym (nfProtoTy-fromNormalProto (Types.nf-normal-proto (P ⋯ nfSubTy σ)))))

select₁-materialize-head :
  ∀ (T : Ty (KP ∷ []) KP) {P : Ty [] KP}
  → substNFProtoWith
      (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))
      (normalizeTy
        (instantiate
          ⦃ Kₛ ⦄
          Duality.⊕
          T
          (Types.T-Var (there (here refl)))))
      ≡
    normalizeTy
      (instantiate
        ⦃ Kₛ ⦄
        Duality.⊕
        T
        ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟)
select₁-materialize-head T {P} =
  trans
    (substNFProtoWith-normalizeTy
      (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))
      (instantiate
        ⦃ Kₛ ⦄
        Duality.⊕
        T
        (Types.T-Var (there (here refl)))))
    (cong normalizeTy
      (instantiate-compose
        {Δ₁ = SLin ∷ KP ∷ []}
        {Δ₂ = SLin ∷ []}
        {K = KP}
        {p = Duality.⊕}
        T
        {P = Types.T-Var (there (here refl))}
        {ϕ = nfSubTy (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))}))

materializeList-select₁-compose :
  ∀ (Ts : List (Ty (KP ∷ []) KP)) {P : Ty [] KP}
  → TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      (Types.T-Var (there (here refl)))
      (Types.T-Var (here refl))
      ⋯ nfSubTy (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))
      ≡
    TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
      (Types.T-Var (here refl))
materializeList-select₁-compose [] = refl
materializeList-select₁-compose (T ∷ Ts) {P}
  rewrite instantiate-compose
            {Δ₁ = SLin ∷ KP ∷ []}
            {Δ₂ = SLin ∷ []}
            {K = KP}
            {p = Duality.⊕}
            T
            {P = Types.T-Var (there (here refl))}
            {ϕ = nfSubTy (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))}
        | materializeList-select₁-compose Ts {P} =
  refl

materializeListNf-select₁ :
  ∀ (Ts : List (Ty (KP ∷ []) KP)) {P : Ty [] KP}
  → substNFTyWith
      (wkNFSub {K = SLin} (singleNFSub (normalizeTy P)))
      (materializeListNf
        Ts
        Duality.⊕
        (normalizeTy (Types.T-Var (there (here refl))))
        (normalizeTy (Types.T-Var (here refl))))
      ≡
    materializeListNf
      Ts
      Duality.⊕
      (wkNfTy {K′ = SLin} (normalizeTy P))
      (normalizeTy (Types.T-Var (here refl)))
materializeListNf-select₁ Ts {P} = nfEq raw
  where
  σ : NFSub (SLin ∷ KP ∷ []) (SLin ∷ [])
  σ = wkNFSub {K = SLin} (singleNFSub (normalizeTy P))

  leftNF : NfTy (SLin ∷ KP ∷ []) SLin
  leftNF =
    materializeListNf
      Ts
      Duality.⊕
      (normalizeTy (Types.T-Var (there (here refl))))
      (normalizeTy (Types.T-Var (here refl)))

  rightNF : NfTy (SLin ∷ []) SLin
  rightNF =
    materializeListNf
      Ts
      Duality.⊕
      (wkNfTy {K′ = SLin} (normalizeTy P))
      (normalizeTy (Types.T-Var (here refl)))

  rightRaw :
    Ty (SLin ∷ []) SLin
  rightRaw =
    TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
      (Types.T-Var (here refl))

  raw :
    ⌞ substNFTyWith σ leftNF ⌟ ≡ ⌞ rightNF ⌟
  raw = trans eq₁ (trans eq₂ (trans eq₃ eq₄))
    where
    eq₁ :
      ⌞ substNFTyWith σ leftNF ⌟
        ≡
      Types.nf Duality.⊕ Duality.d?⊥ (⌞ leftNF ⌟ ⋯ nfSubTy σ)
    eq₁ = substNFTy-sound σ leftNF

    eq₂ :
      Types.nf Duality.⊕ Duality.d?⊥ (⌞ leftNF ⌟ ⋯ nfSubTy σ)
        ≡
      Types.nf Duality.⊕ Duality.d?⊥
        (TypesProtocolConstructors.materializeList
          Ts
          Duality.⊕
          (Types.T-Var (there (here refl)))
          (Types.T-Var (here refl))
          ⋯ nfSubTy σ)
    eq₂ =
      Types.nf-complete
        Duality.d?⊥
        Duality.d?⊥
        (subst-preserves-≡c
          (materializeListNf-raw
            Ts
            {P = normalizeTy (Types.T-Var (there (here refl)))}
            {S = normalizeTy (Types.T-Var (here refl))})
          (nfSubTy σ))

    eq₃ :
      Types.nf Duality.⊕ Duality.d?⊥
        (TypesProtocolConstructors.materializeList
          Ts
          Duality.⊕
          (Types.T-Var (there (here refl)))
          (Types.T-Var (here refl))
          ⋯ nfSubTy σ)
        ≡
      Types.nf Duality.⊕ Duality.d?⊥ rightRaw
    eq₃ =
      cong
        (Types.nf Duality.⊕ Duality.d?⊥)
        (materializeList-select₁-compose Ts {P})

    eq₄ :
      Types.nf Duality.⊕ Duality.d?⊥ rightRaw
        ≡
      ⌞ rightNF ⌟
    eq₄ = trans eq₄a eq₄b
      where
      eq₄a :
        Types.nf Duality.⊕ Duality.d?⊥ rightRaw
          ≡
        Types.nf Duality.⊕ Duality.d?⊥ ⌞ rightNF ⌟
      eq₄a =
        sym
          (Types.nf-complete
            Duality.d?⊥
            Duality.d?⊥
            (materializeListNf-raw
              Ts
              {P = wkNfTy {K′ = SLin} (normalizeTy P)}
              {S = normalizeTy (Types.T-Var (here refl))}))

      eq₄b :
        Types.nf Duality.⊕ Duality.d?⊥ ⌞ rightNF ⌟
          ≡
        ⌞ rightNF ⌟
      eq₄b = Types.nf-idempotent (toNormalTy rightNF)

wkNfTy-normalizeTy-subst-raw :
  ∀ {K Kₚ} {P : Ty [] Kₚ} {U : Ty [] K}
  → ⌞ wkNfTy {K′ = K} (normalizeTy P) ⌟ ⋯ ⦅ ⌞ normalizeTy U ⌟ ⦆ₛ
      ≡
    ⌞ normalizeTy P ⌟
wkNfTy-normalizeTy-subst-raw {K} {Kₚ} {P} {U} =
  trans
    (cong
      (λ X → X ⋯ ⦅ ⌞ normalizeTy U ⌟ ⦆ₛ)
      (wkNFKind-sound {K = Kₚ} {K′ = K} (normalizeTy P)))
    (wk-cancels-⦅⦆-⋯ ⌞ normalizeTy P ⌟ ⌞ normalizeTy U ⌟)

wkNfTy-normalizeTy-subst :
  ∀ {K} {P : Ty [] KP} {U : Ty [] K}
  → substNFProtoWith
      (singleNFSub (normalizeTy U))
      (wkNfTy {K′ = K} (normalizeTy P))
      ≡
    normalizeTy P
wkNfTy-normalizeTy-subst {K} {P} {U} = nfEq raw
  where
  σ : NFSub (K ∷ []) []
  σ = singleNFSub (normalizeTy U)

  raw :
    ⌞ substNFProtoWith σ (wkNfTy {K′ = K} (normalizeTy P)) ⌟
      ≡
    ⌞ normalizeTy P ⌟
  raw =
    trans
      (substNFProto-sound σ (wkNfTy {K′ = K} (normalizeTy P)))
      (trans
        (cong
          (Types.nf Duality.⊕ Duality.d?⊥)
          (trans
            (⋯-cong
              ⌞ wkNfTy {K′ = K} (normalizeTy P) ⌟
              (singleNFSub-sound (normalizeTy U)))
            (wkNfTy-normalizeTy-subst-raw {K = K} {P = P} {U = U})))
        (Types.nfp-idempotent (toNormalProto (normalizeTy P))))

wkNfTy-normalizeTy-substTy :
  ∀ {K pk m} {P : Ty [] (KV pk m)} {U : Ty [] K}
  → substNFTyWith
      (singleNFSub (normalizeTy U))
      (wkNfTy {K′ = K} (normalizeTy P))
      ≡
    normalizeTy P
wkNfTy-normalizeTy-substTy {K} {P = P} {U = U} = nfEq raw
  where
  σ : NFSub (K ∷ []) []
  σ = singleNFSub (normalizeTy U)

  raw :
    ⌞ substNFTyWith σ (wkNfTy {K′ = K} (normalizeTy P)) ⌟
      ≡
    ⌞ normalizeTy P ⌟
  raw =
    trans
      (substNFTy-sound σ (wkNfTy {K′ = K} (normalizeTy P)))
      (trans
        (cong
          (Types.nf Duality.⊕ Duality.d?⊥)
          (trans
            (⋯-cong
              ⌞ wkNfTy {K′ = K} (normalizeTy P) ⌟
              (singleNFSub-sound (normalizeTy U)))
            (wkNfTy-normalizeTy-subst-raw {K = K} {P = P} {U = U})))
        (Types.nf-idempotent (toNormalTy (normalizeTy P))))

materializeList-select₂-compose :
  ∀ (Ts : List (Ty (KP ∷ []) KP)) {P : Ty [] KP} {S : Ty [] SLin}
  → TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
      (Types.T-Var (here refl))
      ⋯ ⦅ ⌞ normalizeTy S ⌟ ⦆ₛ
      ≡
    TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      ⌞ normalizeTy P ⌟
      ⌞ normalizeTy S ⌟
materializeList-select₂-compose [] = refl
materializeList-select₂-compose (T ∷ Ts) {P} {S}
  rewrite instantiate-compose
            {Δ₁ = SLin ∷ []}
            {Δ₂ = []}
            {K = KP}
            {p = Duality.⊕}
            T
            {P = ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟}
            {ϕ = ⦅ ⌞ normalizeTy S ⌟ ⦆ₛ}
        | wkNfTy-normalizeTy-subst-raw {K = SLin} {P = P} {U = S}
        | materializeList-select₂-compose Ts {P} {S} =
  refl

materializeListNf-select₂ :
  ∀ (Ts : List (Ty (KP ∷ []) KP)) {P : Ty [] KP} {S : Ty [] SLin}
  → substNFTyWith
      (singleNFSub (normalizeTy S))
      (materializeListNf
        Ts
        Duality.⊕
        (wkNfTy {K′ = SLin} (normalizeTy P))
        (normalizeTy (Types.T-Var (here refl))))
      ≡
    materializeListNf
      Ts
      Duality.⊕
      (normalizeTy P)
      (normalizeTy S)
materializeListNf-select₂ Ts {P} {S} = nfEq raw
  where
  σ : NFSub (SLin ∷ []) []
  σ = singleNFSub (normalizeTy S)

  leftNF : NfTy (SLin ∷ []) SLin
  leftNF =
    materializeListNf
      Ts
      Duality.⊕
      (wkNfTy {K′ = SLin} (normalizeTy P))
      (normalizeTy (Types.T-Var (here refl)))

  rightNF : NfTy [] SLin
  rightNF =
    materializeListNf
      Ts
      Duality.⊕
      (normalizeTy P)
      (normalizeTy S)

  rightRaw : Ty [] SLin
  rightRaw =
    TypesProtocolConstructors.materializeList
      Ts
      Duality.⊕
      ⌞ normalizeTy P ⌟
      ⌞ normalizeTy S ⌟

  raw :
    ⌞ substNFTyWith σ leftNF ⌟ ≡ ⌞ rightNF ⌟
  raw = trans eq₁ (trans eq₂ (trans eq₃ eq₄))
    where
    eq₁ :
      ⌞ substNFTyWith σ leftNF ⌟
        ≡
      Types.nf Duality.⊕ Duality.d?⊥ (⌞ leftNF ⌟ ⋯ nfSubTy σ)
    eq₁ = substNFTy-sound σ leftNF

    eq₂ :
      Types.nf Duality.⊕ Duality.d?⊥ (⌞ leftNF ⌟ ⋯ nfSubTy σ)
        ≡
      Types.nf Duality.⊕ Duality.d?⊥
        (TypesProtocolConstructors.materializeList
          Ts
          Duality.⊕
          ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
          (Types.T-Var (here refl))
          ⋯ nfSubTy σ)
    eq₂ =
      Types.nf-complete
        Duality.d?⊥
        Duality.d?⊥
        (subst-preserves-≡c
          (materializeListNf-raw
            Ts
            {P = wkNfTy {K′ = SLin} (normalizeTy P)}
            {S = normalizeTy (Types.T-Var (here refl))})
          (nfSubTy σ))

    eq₃ :
      Types.nf Duality.⊕ Duality.d?⊥
        (TypesProtocolConstructors.materializeList
          Ts
          Duality.⊕
          ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
          (Types.T-Var (here refl))
          ⋯ nfSubTy σ)
        ≡
      Types.nf Duality.⊕ Duality.d?⊥ rightRaw
    eq₃ = trans eq₃a eq₃b
      where
      eq₃a :
        Types.nf Duality.⊕ Duality.d?⊥
          (TypesProtocolConstructors.materializeList
            Ts
            Duality.⊕
            ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
            (Types.T-Var (here refl))
            ⋯ nfSubTy σ)
          ≡
        Types.nf Duality.⊕ Duality.d?⊥
          (TypesProtocolConstructors.materializeList
            Ts
            Duality.⊕
            ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
            (Types.T-Var (here refl))
            ⋯ ⦅ ⌞ normalizeTy S ⌟ ⦆ₛ)
      eq₃a =
        cong
          (Types.nf Duality.⊕ Duality.d?⊥)
          (⋯-cong
            (TypesProtocolConstructors.materializeList
              Ts
              Duality.⊕
              ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
              (Types.T-Var (here refl)))
            (singleNFSub-sound (normalizeTy S)))

      eq₃b :
        Types.nf Duality.⊕ Duality.d?⊥
          (TypesProtocolConstructors.materializeList
            Ts
            Duality.⊕
            ⌞ wkNfTy {K′ = SLin} (normalizeTy P) ⌟
            (Types.T-Var (here refl))
            ⋯ ⦅ ⌞ normalizeTy S ⌟ ⦆ₛ)
          ≡
        Types.nf Duality.⊕ Duality.d?⊥ rightRaw
      eq₃b =
        cong
          (Types.nf Duality.⊕ Duality.d?⊥)
          (materializeList-select₂-compose Ts {P} {S})

    eq₄ :
      Types.nf Duality.⊕ Duality.d?⊥ rightRaw
        ≡
      ⌞ rightNF ⌟
    eq₄ = trans eq₄a eq₄b
      where
      eq₄a :
        Types.nf Duality.⊕ Duality.d?⊥ rightRaw
          ≡
        Types.nf Duality.⊕ Duality.d?⊥ ⌞ rightNF ⌟
      eq₄a =
        sym
          (Types.nf-complete
            Duality.d?⊥
            Duality.d?⊥
            (materializeListNf-raw
              Ts
              {P = normalizeTy P}
              {S = normalizeTy S}))

      eq₄b :
        Types.nf Duality.⊕ Duality.d?⊥ ⌞ rightNF ⌟
          ≡
        ⌞ rightNF ⌟
      eq₄b = Types.nf-idempotent (toNormalTy rightNF)

select₁-body :
  ∀ {k} {v : Variance} {i : Fin k} {P : Ty [] KP}
  → substNFTy
      (select1Nf v i (N-Normal (N-Var (here refl))))
      (normalizeTy P)
      ≡
    select1Nf v i (normalizeTy P)
select₁-body {v = v} {i = i} {P = P}
  rewrite materializeListNf-select₁ (proj₁ (ProtocolConstructors _ v i)) {P = P} =
  refl

select₂-body :
  ∀ {k} {v : Variance} {i : Fin k} {P : Ty [] KP} {S : Ty [] SLin}
  → substNFTy
      (selectNf v i (wkNfTy {K′ = SLin} (normalizeTy P)) (N-Var (NV-Var (here refl))))
      (normalizeTy S)
      ≡
    selectNf v i (normalizeTy P) (normalizeTy S)
select₂-body {v = v} {i = i} {P = P} {S = S}
  rewrite wkNfTy-normalizeTy-subst {K = SLin} {P = P} {U = S}
        | materializeListNf-select₂ (proj₁ (ProtocolConstructors _ v i)) {P = P} {S = S} =
  refl
