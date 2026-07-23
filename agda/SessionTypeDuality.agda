module SessionTypeDuality where

open import Data.Fin using (Fin)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

import Duality
import Types
open import Kinds using (SLin)
open import Types using (Ty; T-Dual)
open import Variance using (Variance)
open import TypesProtocolConstructors using (ProtocolConstructors)
open import NormalTypes using
  ( fromNormalTy
  ; nfTyTy-fromNormalTy
  ; from-nt-idem
  ; NFProto
  ; N-Normal
  ; N-Minus
  ; N-ProtoP
  ; N-Up
  ; N-Var
  )
open import NormalTypesSubstitution using (dualNFKind; msgNF)
open import ExprSyntax using (NfTy)
open import ExprNormalTyping using
  ( normalizeTy
  ; normalizeTy-id
  ; materializeListNf
  ; MatchBranchInput
  ; MatchBranchOutput
  )
open import ExprContextReduction using
  ( recvChanNf
  ; sendChanNf
  ; selectSetInNf
  ; selectOutNf
  )

-- Normalizing a source-level dual agrees with dualizing the already
-- normalized session type.  Keeping this fact below both expression and
-- configuration preservation avoids a dependency between those layers.

normalize-dual :
  (S : Ty [] SLin)
  → normalizeTy (T-Dual Duality.D-S S)
      ≡ dualNFKind Duality.D-S (normalizeTy S)
normalize-dual S =
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

dual-recvChanNf :
  ∀ {pk}
    (T : NfTy [] (Kinds.KV pk Kinds.Lin))
    (S : NfTy [] SLin)
  → dualNFKind Duality.D-S (recvChanNf T S)
      ≡ sendChanNf T (dualNFKind Duality.D-S S)
dual-recvChanNf T S rewrite normalizeTy-id T = refl

dual-sendChanNf :
  ∀ {pk}
    (T : NfTy [] (Kinds.KV pk Kinds.Lin))
    (S : NfTy [] SLin)
  → dualNFKind Duality.D-S (sendChanNf T S)
      ≡ recvChanNf T (dualNFKind Duality.D-S S)
dual-sendChanNf T S rewrite normalizeTy-id T = refl

recvChanNf-injective :
  ∀ {pk pk′}
    {T : NfTy [] (Kinds.KV pk Kinds.Lin)}
    {U : NfTy [] (Kinds.KV pk′ Kinds.Lin)}
    {S R : NfTy [] SLin}
  → recvChanNf T S ≡ recvChanNf U R
  → Σ (pk ≡ pk′) λ where
      refl → (T ≡ U) × (S ≡ R)
recvChanNf-injective refl = refl , refl , refl

sendChanNf-injective :
  ∀ {pk pk′}
    {T : NfTy [] (Kinds.KV pk Kinds.Lin)}
    {U : NfTy [] (Kinds.KV pk′ Kinds.Lin)}
    {S R : NfTy [] SLin}
  → sendChanNf T S ≡ sendChanNf U R
  → Σ (pk ≡ pk′) λ where
      refl → (T ≡ U) × (S ≡ R)
sendChanNf-injective refl = refl , refl , refl

dual-select-set-input :
  ∀ {k}
    (ss : Subset.Subset k)
    (v : Variance)
    (P : NfTy [] Kinds.KP)
    (S : NfTy [] SLin)
  → dualNFKind Duality.D-S (MatchBranchInput ss v P S)
      ≡ selectSetInNf ss v P (dualNFKind Duality.D-S S)
dual-select-set-input ss v P S rewrite normalizeTy-id P = refl

selectSetInNf-injective :
  ∀ {k}
    {ss₁ ss₂ : Subset.Subset k}
    {v₁ v₂ : Variance}
    {P₁ P₂ : NfTy [] Kinds.KP}
    {S₁ S₂ : NfTy [] SLin}
  → selectSetInNf ss₁ v₁ P₁ S₁
      ≡ selectSetInNf ss₂ v₂ P₂ S₂
  → (ss₁ ≡ ss₂)
    × (v₁ ≡ v₂)
    × (P₁ ≡ P₂)
    × (S₁ ≡ S₂)
selectSetInNf-injective refl =
  refl , refl , refl , refl

dual-msgNF :
  (P : NFProto [])
  → (S : NfTy [] SLin)
  → dualNFKind Duality.D-S (msgNF Duality.⊝ P S)
      ≡ msgNF Duality.⊕ P (dualNFKind Duality.D-S S)
dual-msgNF (N-Normal (N-ProtoP ss v P)) S
  rewrite normalizeTy-id P = refl
dual-msgNF (N-Normal (N-Up T)) S
  rewrite normalizeTy-id T = refl
dual-msgNF (N-Normal (N-Var ())) S
dual-msgNF (N-Minus (N-ProtoP ss v P)) S
  rewrite normalizeTy-id P = refl
dual-msgNF (N-Minus (N-Up T)) S
  rewrite normalizeTy-id T = refl
dual-msgNF (N-Minus (N-Var ())) S

dual-materializeListNf :
  (Ts : List (Ty (Kinds.KP ∷ []) Kinds.KP))
  → (P : NfTy [] Kinds.KP)
  → (S : NfTy [] SLin)
  → dualNFKind Duality.D-S
      (materializeListNf Ts Duality.⊝ P S)
      ≡ materializeListNf Ts Duality.⊕ P
          (dualNFKind Duality.D-S S)
dual-materializeListNf [] P S = refl
dual-materializeListNf (T ∷ Ts) P S =
  trans
    (dual-msgNF _ (materializeListNf Ts Duality.⊝ P S))
    (cong
      (msgNF Duality.⊕ _)
      (dual-materializeListNf Ts P S))

dual-match-branch-output :
  ∀ {k}
    (ss : Subset.Subset (suc k))
    (v : Variance)
    (P : NfTy [] Kinds.KP)
    (S : NfTy [] SLin)
    (i : Fin (suc k))
    (i∈ : i Subset.∈ ss)
  → dualNFKind Duality.D-S
      (MatchBranchOutput ss v P S i i∈)
      ≡ selectOutNf v i P (dualNFKind Duality.D-S S)
dual-match-branch-output {k} ss v P S i i∈
  with ProtocolConstructors (suc k) v i
... | Ts , usage = dual-materializeListNf Ts P S
