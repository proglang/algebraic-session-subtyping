module AlgorithmicNFMergeSubstitution where

open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≟_)
open import Data.Fin.Subset.Properties using
  (p⊆p∪q; q⊆p∪q; p∩q⊆p; p∩q⊆q)
open import Level using (Level)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import Kinds
open import Variance using (Variance; ⊕; ⊝; ⊘)
open import Variance using (⊙-equal)
import Duality as D
open import Duality using (Polarity)
open import Subtyping using (injᵥ)
open import TypesDecidable using (ty-equal; polarity-equal; polarity-equal′)
open import NormalTypes
open import NormalTypesSubstitution using
  ( NFSub
  ; wkNFSub
  ; minusNF
  ; msgNF
  ; substNFTyWith
  ; substNFProtoWith
  ; substNFProto′With
  )
open import AlgorithmicNFSubtyping
open import AlgorithmicNFSubstitution using
  ( subst-preserves-<:ₜWith
  ; subst-preserves-<:ₚWith
  ; subst-preserves-<:ₚ′With
  ; subst-preserves-<<:ₚWith
  ; subst-preserves-<<:ₚ′With
  ; substNFProtoWith-≡
  )
open import AlgorithmicNFMerge
open import AlgorithmicNFLubGlb using
  ( lub-joinₜ
  ; glb-meetₜ
  ; lub-joinₚ
  ; glb-meetₚ
  )
open import AlgorithmicNFSound using
  (<:ₜ-antisym; <:ₚ-antisym)

no≢yes :
  ∀ {a : Level} {A : Set a} {x : A} {not-A : A → Data.Empty.⊥}
  → no not-A ≡ yes x
  → Data.Empty.⊥
no≢yes ()

JoinₜResult :
  ∀ {Δ₁ Δ₂ pk m}
  → NFSub Δ₁ Δ₂
  → NFTy Δ₁ (KV pk m)
  → NFTy Δ₁ (KV pk m)
  → NFTy Δ₁ (KV pk m)
  → Set
JoinₜResult σ N₁ N₂ N =
  Σ _ λ N₁<:N → Σ _ λ N₂<:N →
  joinₜ (substNFTyWith σ N₁) (substNFTyWith σ N₂)
    ≡ yes (substNFTyWith σ N , N₁<:N , N₂<:N)

MeetₜResult :
  ∀ {Δ₁ Δ₂ pk m}
  → NFSub Δ₁ Δ₂
  → NFTy Δ₁ (KV pk m)
  → NFTy Δ₁ (KV pk m)
  → NFTy Δ₁ (KV pk m)
  → Set
MeetₜResult σ N₁ N₂ N =
  Σ _ λ N<:N₁ → Σ _ λ N<:N₂ →
  meetₜ (substNFTyWith σ N₁) (substNFTyWith σ N₂)
    ≡ yes (substNFTyWith σ N , N<:N₁ , N<:N₂)

joinₜ-self :
  ∀ {pk m} (N : NFTy Δ (KV pk m))
  → Σ _ λ N<:N₁ → Σ _ λ N<:N₂ →
      joinₜ N N ≡ yes (N , N<:N₁ , N<:N₂)
joinₜ-self N
  with lub-joinₜ N N N (<:ₜ-refl N) (<:ₜ-refl N)
... | N′ , N<:N′₁ , N<:N′₂ , eq , N′<:N
  with <:ₜ-antisym N′<:N N<:N′₁
... | refl = N<:N′₁ , N<:N′₂ , eq

meetₜ-self :
  ∀ {pk m} (N : NFTy Δ (KV pk m))
  → Σ _ λ N<:N₁ → Σ _ λ N<:N₂ →
      meetₜ N N ≡ yes (N , N<:N₁ , N<:N₂)
meetₜ-self N
  with glb-meetₜ N N N (<:ₜ-refl N) (<:ₜ-refl N)
... | N′ , N′<:N₁ , N′<:N₂ , eq , N<:N′
  with <:ₜ-antisym N<:N′ N′<:N₁
... | refl = N′<:N₁ , N′<:N₂ , eq

joinₚ-self :
  (N : NFProto Δ)
  → Σ _ λ N<:N₁ → Σ _ λ N<:N₂ →
      joinₚ N N ≡ yes (N , N<:N₁ , N<:N₂)
joinₚ-self N
  with lub-joinₚ N N N (<:ₚ-refl N) (<:ₚ-refl N)
... | N′ , N<:N′₁ , N<:N′₂ , eq , N′<:N
  with <:ₚ-antisym N′<:N N<:N′₁
... | refl = N<:N′₁ , N<:N′₂ , eq

meetₚ-self :
  (N : NFProto Δ)
  → Σ _ λ N<:N₁ → Σ _ λ N<:N₂ →
      meetₚ N N ≡ yes (N , N<:N₁ , N<:N₂)
meetₚ-self N
  with glb-meetₚ N N N (<:ₚ-refl N) (<:ₚ-refl N)
... | N′ , N′<:N₁ , N′<:N₂ , eq , N<:N′
  with <:ₚ-antisym N<:N′ N′<:N₁
... | refl = N′<:N₁ , N′<:N₂ , eq

ProtoJoinResult :
  ∀ {Δ₁ Δ₂}
  → NFSub Δ₁ Δ₂
  → NFProto′ Δ₁
  → NFProto′ Δ₁
  → NFProto′ Δ₁
  → Set
ProtoJoinResult σ P₁ P₂ P =
  Σ _ λ P₁<:P → Σ _ λ P₂<:P →
  joinₚ (substNFProto′With σ P₁) (substNFProto′With σ P₂)
    ≡ yes (substNFProto′With σ P , P₁<:P , P₂<:P)

ProtoMeetResult :
  ∀ {Δ₁ Δ₂}
  → NFSub Δ₁ Δ₂
  → NFProto′ Δ₁
  → NFProto′ Δ₁
  → NFProto′ Δ₁
  → Set
ProtoMeetResult σ P₁ P₂ P =
  Σ _ λ P<:P₁ → Σ _ λ P<:P₂ →
  meetₚ (substNFProto′With σ P₁) (substNFProto′With σ P₂)
    ≡ yes (substNFProto′With σ P , P<:P₁ , P<:P₂)

MergeJoinResult :
  ∀ {Δ₁ Δ₂}
  → NFSub Δ₁ Δ₂
  → Variance
  → NFProto Δ₁
  → NFProto Δ₁
  → NFProto Δ₁
  → Set
MergeJoinResult σ v P₁ P₂ P =
  Σ _ λ P₁<:P → Σ _ λ P₂<:P →
  mergeₚ-join v (substNFProtoWith σ P₁) (substNFProtoWith σ P₂)
    ≡ yes (substNFProtoWith σ P , P₁<:P , P₂<:P)

MergeMeetResult :
  ∀ {Δ₁ Δ₂}
  → NFSub Δ₁ Δ₂
  → Variance
  → NFProto Δ₁
  → NFProto Δ₁
  → NFProto Δ₁
  → Set
MergeMeetResult σ v P₁ P₂ P =
  Σ _ λ P<:P₁ → Σ _ λ P<:P₂ →
  mergeₚ-meet v (substNFProtoWith σ P₁) (substNFProtoWith σ P₂)
    ≡ yes (substNFProtoWith σ P , P<:P₁ , P<:P₂)

minus-join-from-meet :
  ∀ {P₁ P₂ P : NFProto Δ}
    {P<:P₁ : P <:ₚ P₁} {P<:P₂ : P <:ₚ P₂}
  → meetₚ P₁ P₂ ≡ yes (P , P<:P₁ , P<:P₂)
  → Σ _ λ P₁<:P → Σ _ λ P₂<:P →
      joinₚ (minusNF P₁) (minusNF P₂)
        ≡ yes (minusNF P , P₁<:P , P₂<:P)
minus-join-from-meet {P₁ = N-Normal P₁} {N-Normal P₂} eq
  with meetₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eq)
... | yes (P , P<:P₁ , P<:P₂)
  with eq
... | refl =
  <:ₚ-minus P<:P₁ , <:ₚ-minus P<:P₂ , refl
minus-join-from-meet {P₁ = N-Normal P₁} {N-Minus P₂} ()
minus-join-from-meet {P₁ = N-Minus P₁} {N-Normal P₂} ()
minus-join-from-meet {P₁ = N-Minus P₁} {N-Minus P₂} eq
  with joinₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eq)
... | yes (P , P₁<:P , P₂<:P)
  with eq
... | refl =
  <:ₚ-plus P₁<:P , <:ₚ-plus P₂<:P , refl

minus-meet-from-join :
  ∀ {P₁ P₂ P : NFProto Δ}
    {P₁<:P : P₁ <:ₚ P} {P₂<:P : P₂ <:ₚ P}
  → joinₚ P₁ P₂ ≡ yes (P , P₁<:P , P₂<:P)
  → Σ _ λ P<:P₁ → Σ _ λ P<:P₂ →
      meetₚ (minusNF P₁) (minusNF P₂)
        ≡ yes (minusNF P , P<:P₁ , P<:P₂)
minus-meet-from-join {P₁ = N-Normal P₁} {N-Normal P₂} eq
  with joinₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eq)
... | yes (P , P₁<:P , P₂<:P)
  with eq
... | refl =
  <:ₚ-minus P₁<:P , <:ₚ-minus P₂<:P , refl
minus-meet-from-join {P₁ = N-Normal P₁} {N-Minus P₂} ()
minus-meet-from-join {P₁ = N-Minus P₁} {N-Normal P₂} ()
minus-meet-from-join {P₁ = N-Minus P₁} {N-Minus P₂} eq
  with meetₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eq)
... | yes (P , P<:P₁ , P<:P₂)
  with eq
... | refl =
  <:ₚ-plus P<:P₁ , <:ₚ-plus P<:P₂ , refl

join-msgNF :
  ∀ (p : Polarity)
    (P₁ P₂ : NFProto Δ)
    (S₁ S₂ : NFTy Δ SLin)
    {P : NFProto Δ} {S : NFTy Δ SLin}
    {P₁<:P : P₁ <<:ₚ[ injᵥ p ] P}
    {P₂<:P : P₂ <<:ₚ[ injᵥ p ] P}
    {S₁<:S : S₁ <:ₜ S} {S₂<:S : S₂ <:ₜ S}
  → mergeₚ-join (injᵥ p) P₁ P₂ ≡ yes (P , P₁<:P , P₂<:P)
  → joinₜ S₁ S₂ ≡ yes (S , S₁<:S , S₂<:S)
  → Σ _ λ PS₁<:PS → Σ _ λ PS₂<:PS →
      joinₜ (msgNF p P₁ S₁) (msgNF p P₂ S₂)
        ≡ yes (msgNF p P S , PS₁<:PS , PS₂<:PS)
join-msgNF D.⊕ (N-Normal P₁) (N-Normal P₂) S₁ S₂ eqP eqS
  with meetₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eqP)
... | yes (P , P<:P₁ , P<:P₂)
  with eqP
... | refl
  rewrite polarity-equal′ D.⊕ | eqS =
  <:ₜ-msg P<:P₁ _ , <:ₜ-msg P<:P₂ _ , refl
join-msgNF D.⊕ (N-Normal P₁) (N-Minus P₂) S₁ S₂ () eqS
join-msgNF D.⊕ (N-Minus P₁) (N-Normal P₂) S₁ S₂ () eqS
join-msgNF D.⊕ (N-Minus P₁) (N-Minus P₂) S₁ S₂ eqP eqS
  with joinₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eqP)
... | yes (P , P₁<:P , P₂<:P)
  with eqP
... | refl
  rewrite polarity-equal′ D.⊝ | eqS =
  <:ₜ-msg P₁<:P _ , <:ₜ-msg P₂<:P _ , refl
join-msgNF D.⊝ (N-Normal P₁) (N-Normal P₂) S₁ S₂ eqP eqS
  with joinₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eqP)
... | yes (P , P₁<:P , P₂<:P)
  with eqP
... | refl
  rewrite polarity-equal′ D.⊝ | eqS =
  <:ₜ-msg P₁<:P _ , <:ₜ-msg P₂<:P _ , refl
join-msgNF D.⊝ (N-Normal P₁) (N-Minus P₂) S₁ S₂ () eqS
join-msgNF D.⊝ (N-Minus P₁) (N-Normal P₂) S₁ S₂ () eqS
join-msgNF D.⊝ (N-Minus P₁) (N-Minus P₂) S₁ S₂ eqP eqS
  with meetₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eqP)
... | yes (P , P<:P₁ , P<:P₂)
  with eqP
... | refl
  rewrite polarity-equal′ D.⊕ | eqS =
  <:ₜ-msg P<:P₁ _ , <:ₜ-msg P<:P₂ _ , refl

meet-msgNF :
  ∀ (p : Polarity)
    (P₁ P₂ : NFProto Δ)
    (S₁ S₂ : NFTy Δ SLin)
    {P : NFProto Δ} {S : NFTy Δ SLin}
    {P<:P₁ : P <<:ₚ[ injᵥ p ] P₁}
    {P<:P₂ : P <<:ₚ[ injᵥ p ] P₂}
    {S<:S₁ : S <:ₜ S₁} {S<:S₂ : S <:ₜ S₂}
  → mergeₚ-meet (injᵥ p) P₁ P₂ ≡ yes (P , P<:P₁ , P<:P₂)
  → meetₜ S₁ S₂ ≡ yes (S , S<:S₁ , S<:S₂)
  → Σ _ λ PS<:PS₁ → Σ _ λ PS<:PS₂ →
      meetₜ (msgNF p P₁ S₁) (msgNF p P₂ S₂)
        ≡ yes (msgNF p P S , PS<:PS₁ , PS<:PS₂)
meet-msgNF D.⊕ (N-Normal P₁) (N-Normal P₂) S₁ S₂ eqP eqS
  with joinₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eqP)
... | yes (P , P₁<:P , P₂<:P)
  with eqP
... | refl
  rewrite polarity-equal′ D.⊕ | eqS =
  <:ₜ-msg P₁<:P _ , <:ₜ-msg P₂<:P _ , refl
meet-msgNF D.⊕ (N-Normal P₁) (N-Minus P₂) S₁ S₂ () eqS
meet-msgNF D.⊕ (N-Minus P₁) (N-Normal P₂) S₁ S₂ () eqS
meet-msgNF D.⊕ (N-Minus P₁) (N-Minus P₂) S₁ S₂ eqP eqS
  with meetₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eqP)
... | yes (P , P<:P₁ , P<:P₂)
  with eqP
... | refl
  rewrite polarity-equal′ D.⊝ | eqS =
  <:ₜ-msg P<:P₁ _ , <:ₜ-msg P<:P₂ _ , refl
meet-msgNF D.⊝ (N-Normal P₁) (N-Normal P₂) S₁ S₂ eqP eqS
  with meetₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eqP)
... | yes (P , P<:P₁ , P<:P₂)
  with eqP
... | refl
  rewrite polarity-equal′ D.⊝ | eqS =
  <:ₜ-msg P<:P₁ _ , <:ₜ-msg P<:P₂ _ , refl
meet-msgNF D.⊝ (N-Normal P₁) (N-Minus P₂) S₁ S₂ () eqS
meet-msgNF D.⊝ (N-Minus P₁) (N-Normal P₂) S₁ S₂ () eqS
meet-msgNF D.⊝ (N-Minus P₁) (N-Minus P₂) S₁ S₂ eqP eqS
  with joinₚ′ P₁ P₂ in inner
... | no _ = ⊥-elim (no≢yes eqP)
... | yes (P , P₁<:P , P₂<:P)
  with eqP
... | refl
  rewrite polarity-equal′ D.⊕ | eqS =
  <:ₜ-msg P₁<:P _ , <:ₜ-msg P₂<:P _ , refl

mutual

  joinₜ-subst :
    ∀ {Δ₁ Δ₂ pk m}
      (σ : NFSub Δ₁ Δ₂)
      (N₁ N₂ : NFTy Δ₁ (KV pk m))
      {N : NFTy Δ₁ (KV pk m)}
      {N₁<:N : N₁ <:ₜ N}
      {N₂<:N : N₂ <:ₜ N}
    → joinₜ N₁ N₂ ≡ yes (N , N₁<:N , N₂<:N)
    → JoinₜResult σ N₁ N₂ N

  meetₜ-subst :
    ∀ {Δ₁ Δ₂ pk m}
      (σ : NFSub Δ₁ Δ₂)
      (N₁ N₂ : NFTy Δ₁ (KV pk m))
      {N : NFTy Δ₁ (KV pk m)}
      {N<:N₁ : N <:ₜ N₁}
      {N<:N₂ : N <:ₜ N₂}
    → meetₜ N₁ N₂ ≡ yes (N , N<:N₁ , N<:N₂)
    → MeetₜResult σ N₁ N₂ N

  joinₚ′-subst :
    ∀ {Δ₁ Δ₂}
      (σ : NFSub Δ₁ Δ₂)
      (P₁ P₂ : NFProto′ Δ₁)
      {P : NFProto′ Δ₁}
      {P₁<:P : P₁ <:ₚ′ P} {P₂<:P : P₂ <:ₚ′ P}
    → joinₚ′ P₁ P₂ ≡ yes (P , P₁<:P , P₂<:P)
    → ProtoJoinResult σ P₁ P₂ P

  meetₚ′-subst :
    ∀ {Δ₁ Δ₂}
      (σ : NFSub Δ₁ Δ₂)
      (P₁ P₂ : NFProto′ Δ₁)
      {P : NFProto′ Δ₁}
      {P<:P₁ : P <:ₚ′ P₁} {P<:P₂ : P <:ₚ′ P₂}
    → meetₚ′ P₁ P₂ ≡ yes (P , P<:P₁ , P<:P₂)
    → ProtoMeetResult σ P₁ P₂ P

  mergeₚ-join-subst :
    ∀ {Δ₁ Δ₂}
      (σ : NFSub Δ₁ Δ₂)
      (v : Variance)
      (P₁ P₂ : NFProto Δ₁)
      {P : NFProto Δ₁}
      {P₁<:P : P₁ <<:ₚ[ v ] P} {P₂<:P : P₂ <<:ₚ[ v ] P}
    → mergeₚ-join v P₁ P₂ ≡ yes (P , P₁<:P , P₂<:P)
    → MergeJoinResult σ v P₁ P₂ P

  mergeₚ-meet-subst :
    ∀ {Δ₁ Δ₂}
      (σ : NFSub Δ₁ Δ₂)
      (v : Variance)
      (P₁ P₂ : NFProto Δ₁)
      {P : NFProto Δ₁}
      {P<:P₁ : P <<:ₚ[ v ] P₁} {P<:P₂ : P <<:ₚ[ v ] P₂}
    → mergeₚ-meet v P₁ P₂ ≡ yes (P , P<:P₁ , P<:P₂)
    → MergeMeetResult σ v P₁ P₂ P

  joinₜ-subst σ (N-Var NV) (N-Var NV₁) eq
    with join-var NV NV₁
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq
  ... | refl = joinₜ-self (substNFTyWith σ (N-Var NV))
  joinₜ-subst σ (N-Var NV) N-Base ()
  joinₜ-subst σ (N-Var NV) (N-Arrow N₂ N₃) ()
  joinₜ-subst σ (N-Var NV) (N-Pair N₂ N₃) ()
  joinₜ-subst σ (N-Var NV) (N-Poly K N₂) ()
  joinₜ-subst σ (N-Var NV) (N-Sub km≤ N₂) ()
  joinₜ-subst σ (N-Var NV) N-End ()
  joinₜ-subst σ (N-Var NV) (N-Msg p P N₂) ()
  joinₜ-subst σ (N-Var NV) (N-ProtoD N₂) ()
  joinₜ-subst σ N-Base (N-Var NV) ()
  joinₜ-subst σ N-Base N-Base refl = <:ₜ-base , <:ₜ-base , refl
  joinₜ-subst σ N-Base (N-Arrow N₂ N₃) ()
  joinₜ-subst σ N-Base (N-Pair N₂ N₃) ()
  joinₜ-subst σ N-Base (N-Poly K N₂) ()
  joinₜ-subst σ N-Base (N-Sub km≤ N₂) ()
  joinₜ-subst σ N-Base (N-ProtoD N₂) ()
  joinₜ-subst σ (N-Arrow N₁ N₂) (N-Var NV) ()
  joinₜ-subst σ (N-Arrow N₁ N₂) N-Base ()
  joinₜ-subst σ (N-Arrow N₁ N₂) (N-Pair N₃ N₄) ()
  joinₜ-subst σ
      (N-Arrow {pk₁ = pk₁} {m₁ = m₁} {pk₂ = pk₂} {m₂ = m₂} N₁ N₂)
      (N-Arrow {pk₁ = pk₃} {m₁ = m₃} {pk₂ = pk₄} {m₂ = m₄} N₃ N₄)
      eq
    with eq-prekind pk₁ pk₃
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-multiplicity m₁ m₃
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-prekind pk₂ pk₄
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-multiplicity m₂ m₄
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with meetₜ N₃ N₁ in meet-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (M , M<:N₃ , M<:N₁)
    with joinₜ N₂ N₄ in join-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (J , N₂<:J , N₄<:J)
    with eq
  ... | refl
    with meetₜ-subst σ N₃ N₁ meet-eq
       | joinₜ-subst σ N₂ N₄ join-eq
  ... | M<:N₃σ , M<:N₁σ , meet-eqσ
      | N₂σ<:J , N₄σ<:J , join-eqσ
    rewrite meet-eqσ
          | join-eqσ =
    <:ₜ-arrow M<:N₁σ N₂σ<:J ,
    <:ₜ-arrow M<:N₃σ N₄σ<:J ,
    refl
  joinₜ-subst σ (N-Arrow N₁ N₂) (N-Poly K N₃) ()
  joinₜ-subst σ (N-Arrow N₁ N₂) (N-Sub km≤ N₃) ()
  joinₜ-subst σ (N-Arrow N₁ N₂) (N-ProtoD N₃) ()
  joinₜ-subst σ (N-Pair N₁ N₂) (N-Var NV) ()
  joinₜ-subst σ (N-Pair N₁ N₂) N-Base ()
  joinₜ-subst σ (N-Pair N₁ N₂) (N-Arrow N₃ N₄) ()
  joinₜ-subst σ
      (N-Pair {pk₁ = pk₁} {pk₂ = pk₂} N₁ N₂)
      (N-Pair {pk₁ = pk₃} {pk₂ = pk₄} N₃ N₄)
      eq
    with eq-prekind pk₁ pk₃
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-prekind pk₂ pk₄
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with joinₜ N₁ N₃ in join-eq₁
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (J₁ , N₁<:J₁ , N₃<:J₁)
    with joinₜ N₂ N₄ in join-eq₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (J₂ , N₂<:J₂ , N₄<:J₂)
    with eq
  ... | refl
    with joinₜ-subst σ N₁ N₃ join-eq₁
       | joinₜ-subst σ N₂ N₄ join-eq₂
  ... | N₁σ<:J₁ , N₃σ<:J₁ , join-eqσ₁
      | N₂σ<:J₂ , N₄σ<:J₂ , join-eqσ₂
    rewrite join-eqσ₁
          | join-eqσ₂ =
    <:ₜ-pair N₁σ<:J₁ N₂σ<:J₂ ,
    <:ₜ-pair N₃σ<:J₁ N₄σ<:J₂ ,
    refl
  joinₜ-subst σ (N-Pair N₁ N₂) (N-Poly K N₃) ()
  joinₜ-subst σ (N-Pair N₁ N₂) (N-Sub km≤ N₃) ()
  joinₜ-subst σ (N-Pair N₁ N₂) (N-ProtoD N₃) ()
  joinₜ-subst σ (N-Poly K N₁) (N-Var NV) ()
  joinₜ-subst σ (N-Poly K N₁) N-Base ()
  joinₜ-subst σ (N-Poly K N₁) (N-Pair N₂ N₃) ()
  joinₜ-subst σ (N-Poly K N₁) (N-Arrow N₂ N₃) ()
  joinₜ-subst σ (N-Poly K₁ N₁) (N-Poly K₂ N₂) eq
    with eq-kind K₁ K₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with joinₜ N₁ N₂ in join-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (J , N₁<:J , N₂<:J)
    with eq
  ... | refl
    with joinₜ-subst (wkNFSub σ) N₁ N₂ join-eq
  ... | N₁σ<:J , N₂σ<:J , join-eqσ
    rewrite join-eqσ =
    <:ₜ-poly N₁σ<:J , <:ₜ-poly N₂σ<:J , refl
  joinₜ-subst σ (N-Poly K N₁) (N-Sub km≤ N₂) ()
  joinₜ-subst σ (N-Poly K N₁) (N-ProtoD N₂) ()
  joinₜ-subst σ (N-Sub km≤ N₁) (N-Var NV) ()
  joinₜ-subst σ (N-Sub km≤ N₁) N-Base ()
  joinₜ-subst σ (N-Sub km≤ N₁) (N-Arrow N₂ N₃) ()
  joinₜ-subst σ (N-Sub km≤ N₁) (N-Poly K N₂) ()
  joinₜ-subst σ
      (N-Sub {pk₁} {m₁} km≤₁ N₁)
      (N-Sub {pk₂} {m₂} km≤₂ N₂)
      eq
    with eq-prekind pk₁ pk₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-multiplicity m₁ m₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    rewrite ≤k-irrelevant km≤₁ km≤₂
    with joinₜ N₁ N₂ in join-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (J , N₁<:J , N₂<:J)
    with eq
  ... | refl
    with joinₜ-subst σ N₁ N₂ join-eq
  ... | N₁σ<:J , N₂σ<:J , join-eqσ
    rewrite ≤k-irrelevant km≤₂ km≤₂
          | join-eqσ =
    <:ₜ-sub N₁σ<:J , <:ₜ-sub N₂σ<:J , refl
  joinₜ-subst σ (N-Sub km≤ N₁) (N-Pair N₂ N₃) ()
  joinₜ-subst σ (N-Sub km≤ N₁) N-End ()
  joinₜ-subst σ (N-Sub km≤ N₁) (N-Msg p P N₂) ()
  joinₜ-subst σ (N-Sub km≤ N₁) (N-ProtoD N₂) ()
  joinₜ-subst σ N-End (N-Var NV) ()
  joinₜ-subst σ N-End (N-Sub km≤ N₂) ()
  joinₜ-subst σ N-End N-End refl = <:ₜ-end , <:ₜ-end , refl
  joinₜ-subst σ (N-Msg p P N₁) (N-Var NV) ()
  joinₜ-subst σ (N-Msg p P N₁) (N-Sub km≤ N₂) ()
  joinₜ-subst σ (N-Msg D.⊕ P₁ S₁) (N-Msg p₂ P₂ S₂) eq
    with polarity-equal D.⊕ p₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with meetₚ′ P₁ P₂ in proto-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P<:P₁ , P<:P₂)
    with joinₜ S₁ S₂ in cont-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (S , S₁<:S , S₂<:S)
    with eq
  ... | refl
    with meetₚ′-subst σ P₁ P₂ proto-eq
       | joinₜ-subst σ S₁ S₂ cont-eq
  ... | Pσ<:P₁σ , Pσ<:P₂σ , proto-eqσ
      | S₁σ<:Sσ , S₂σ<:Sσ , cont-eqσ
    with join-msgNF D.⊕
      (substNFProto′With σ P₁)
      (substNFProto′With σ P₂)
      (substNFTyWith σ S₁)
      (substNFTyWith σ S₂)
      proto-eqσ cont-eqσ
  ... | PS₁<:PS , PS₂<:PS , joined = PS₁<:PS , PS₂<:PS , joined
  joinₜ-subst σ (N-Msg D.⊝ P₁ S₁) (N-Msg p₂ P₂ S₂) eq
    with polarity-equal D.⊝ p₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with joinₚ′ P₁ P₂ in proto-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P₁<:P , P₂<:P)
    with joinₜ S₁ S₂ in cont-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (S , S₁<:S , S₂<:S)
    with eq
  ... | refl
    with joinₚ′-subst σ P₁ P₂ proto-eq
       | joinₜ-subst σ S₁ S₂ cont-eq
  ... | P₁σ<:Pσ , P₂σ<:Pσ , proto-eqσ
      | S₁σ<:Sσ , S₂σ<:Sσ , cont-eqσ
    with join-msgNF D.⊝
      (substNFProto′With σ P₁)
      (substNFProto′With σ P₂)
      (substNFTyWith σ S₁)
      (substNFTyWith σ S₂)
      proto-eqσ cont-eqσ
  ... | PS₁<:PS , PS₂<:PS , joined = PS₁<:PS , PS₂<:PS , joined
  joinₜ-subst σ (N-ProtoD N₁) (N-Var NV) ()
  joinₜ-subst σ (N-ProtoD N₁) N-Base ()
  joinₜ-subst σ (N-ProtoD N₁) (N-Arrow N₂ N₃) ()
  joinₜ-subst σ (N-ProtoD N₁) (N-Pair N₂ N₃) ()
  joinₜ-subst σ (N-ProtoD N₁) (N-Poly K N₂) ()
  joinₜ-subst σ (N-ProtoD N₁) (N-Sub km≤ N₂) ()
  joinₜ-subst σ (N-ProtoD N₁) (N-ProtoD N₂) eq
    with joinₜ N₁ N₂ in join-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (J , N₁<:J , N₂<:J)
    with eq
  ... | refl
    with joinₜ-subst σ N₁ N₂ join-eq
  ... | N₁σ<:J , N₂σ<:J , join-eqσ
    rewrite join-eqσ =
    <:ₜ-data N₁σ<:J , <:ₜ-data N₂σ<:J , refl

  meetₜ-subst σ (N-Var NV) (N-Var NV₁) eq
    with join-var NV NV₁
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq
  ... | refl = meetₜ-self (substNFTyWith σ (N-Var NV))
  meetₜ-subst σ (N-Var NV) N-Base ()
  meetₜ-subst σ (N-Var NV) (N-Arrow N₂ N₃) ()
  meetₜ-subst σ (N-Var NV) (N-Pair N₂ N₃) ()
  meetₜ-subst σ (N-Var NV) (N-Poly K N₂) ()
  meetₜ-subst σ (N-Var NV) (N-Sub km≤ N₂) ()
  meetₜ-subst σ (N-Var NV) N-End ()
  meetₜ-subst σ (N-Var NV) (N-Msg p P N₂) ()
  meetₜ-subst σ (N-Var NV) (N-ProtoD N₂) ()
  meetₜ-subst σ N-Base (N-Var NV) ()
  meetₜ-subst σ N-Base N-Base refl = <:ₜ-base , <:ₜ-base , refl
  meetₜ-subst σ N-Base (N-Arrow N₂ N₃) ()
  meetₜ-subst σ N-Base (N-Pair N₂ N₃) ()
  meetₜ-subst σ N-Base (N-Poly K N₂) ()
  meetₜ-subst σ N-Base (N-Sub km≤ N₂) ()
  meetₜ-subst σ N-Base (N-ProtoD N₂) ()
  meetₜ-subst σ (N-Arrow N₁ N₂) (N-Var NV) ()
  meetₜ-subst σ (N-Arrow N₁ N₂) N-Base ()
  meetₜ-subst σ (N-Arrow N₁ N₂) (N-Pair N₃ N₄) ()
  meetₜ-subst σ
      (N-Arrow {pk₁ = pk₁} {m₁ = m₁} {pk₂ = pk₂} {m₂ = m₂} N₁ N₂)
      (N-Arrow {pk₁ = pk₃} {m₁ = m₃} {pk₂ = pk₄} {m₂ = m₄} N₃ N₄)
      eq
    with eq-prekind pk₁ pk₃
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-multiplicity m₁ m₃
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-prekind pk₂ pk₄
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-multiplicity m₂ m₄
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with joinₜ N₃ N₁ in join-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (J , N₃<:J , N₁<:J)
    with meetₜ N₂ N₄ in meet-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (M , M<:N₂ , M<:N₄)
    with eq
  ... | refl
    with joinₜ-subst σ N₃ N₁ join-eq
       | meetₜ-subst σ N₂ N₄ meet-eq
  ... | N₃σ<:J , N₁σ<:J , join-eqσ
      | M<:N₂σ , M<:N₄σ , meet-eqσ
    rewrite join-eqσ
          | meet-eqσ =
    <:ₜ-arrow N₁σ<:J M<:N₂σ ,
    <:ₜ-arrow N₃σ<:J M<:N₄σ ,
    refl
  meetₜ-subst σ (N-Arrow N₁ N₂) (N-Poly K N₃) ()
  meetₜ-subst σ (N-Arrow N₁ N₂) (N-Sub km≤ N₃) ()
  meetₜ-subst σ (N-Arrow N₁ N₂) (N-ProtoD N₃) ()
  meetₜ-subst σ (N-Pair N₁ N₂) (N-Var NV) ()
  meetₜ-subst σ (N-Pair N₁ N₂) N-Base ()
  meetₜ-subst σ (N-Pair N₁ N₂) (N-Arrow N₃ N₄) ()
  meetₜ-subst σ
      (N-Pair {pk₁ = pk₁} {pk₂ = pk₂} N₁ N₂)
      (N-Pair {pk₁ = pk₃} {pk₂ = pk₄} N₃ N₄)
      eq
    with eq-prekind pk₁ pk₃
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-prekind pk₂ pk₄
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with meetₜ N₁ N₃ in meet-eq₁
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (M₁ , M₁<:N₁ , M₁<:N₃)
    with meetₜ N₂ N₄ in meet-eq₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (M₂ , M₂<:N₂ , M₂<:N₄)
    with eq
  ... | refl
    with meetₜ-subst σ N₁ N₃ meet-eq₁
       | meetₜ-subst σ N₂ N₄ meet-eq₂
  ... | M₁<:N₁σ , M₁<:N₃σ , meet-eqσ₁
      | M₂<:N₂σ , M₂<:N₄σ , meet-eqσ₂
    rewrite meet-eqσ₁
          | meet-eqσ₂ =
    <:ₜ-pair M₁<:N₁σ M₂<:N₂σ ,
    <:ₜ-pair M₁<:N₃σ M₂<:N₄σ ,
    refl
  meetₜ-subst σ (N-Pair N₁ N₂) (N-Poly K N₃) ()
  meetₜ-subst σ (N-Pair N₁ N₂) (N-Sub km≤ N₃) ()
  meetₜ-subst σ (N-Pair N₁ N₂) (N-ProtoD N₃) ()
  meetₜ-subst σ (N-Poly K N₁) (N-Var NV) ()
  meetₜ-subst σ (N-Poly K N₁) N-Base ()
  meetₜ-subst σ (N-Poly K N₁) (N-Pair N₂ N₃) ()
  meetₜ-subst σ (N-Poly K N₁) (N-Arrow N₂ N₃) ()
  meetₜ-subst σ (N-Poly K₁ N₁) (N-Poly K₂ N₂) eq
    with eq-kind K₁ K₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with meetₜ N₁ N₂ in meet-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (M , M<:N₁ , M<:N₂)
    with eq
  ... | refl
    with meetₜ-subst (wkNFSub σ) N₁ N₂ meet-eq
  ... | M<:N₁σ , M<:N₂σ , meet-eqσ
    rewrite meet-eqσ =
    <:ₜ-poly M<:N₁σ , <:ₜ-poly M<:N₂σ , refl
  meetₜ-subst σ (N-Poly K N₁) (N-Sub km≤ N₂) ()
  meetₜ-subst σ (N-Poly K N₁) (N-ProtoD N₂) ()
  meetₜ-subst σ (N-Sub km≤ N₁) (N-Var NV) ()
  meetₜ-subst σ (N-Sub km≤ N₁) N-Base ()
  meetₜ-subst σ (N-Sub km≤ N₁) (N-Arrow N₂ N₃) ()
  meetₜ-subst σ (N-Sub km≤ N₁) (N-Poly K N₂) ()
  meetₜ-subst σ
      (N-Sub {pk₁} {m₁} km≤₁ N₁)
      (N-Sub {pk₂} {m₂} km≤₂ N₂)
      eq
    with eq-prekind pk₁ pk₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-multiplicity m₁ m₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    rewrite ≤k-irrelevant km≤₁ km≤₂
    with meetₜ N₁ N₂ in meet-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (M , M<:N₁ , M<:N₂)
    with eq
  ... | refl
    with meetₜ-subst σ N₁ N₂ meet-eq
  ... | M<:N₁σ , M<:N₂σ , meet-eqσ
    rewrite ≤k-irrelevant km≤₂ km≤₂
          | meet-eqσ =
    <:ₜ-sub M<:N₁σ , <:ₜ-sub M<:N₂σ , refl
  meetₜ-subst σ (N-Sub km≤ N₁) (N-Pair N₂ N₃) ()
  meetₜ-subst σ (N-Sub km≤ N₁) N-End ()
  meetₜ-subst σ (N-Sub km≤ N₁) (N-Msg p P N₂) ()
  meetₜ-subst σ (N-Sub km≤ N₁) (N-ProtoD N₂) ()
  meetₜ-subst σ N-End (N-Var NV) ()
  meetₜ-subst σ N-End (N-Sub km≤ N₂) ()
  meetₜ-subst σ N-End N-End refl = <:ₜ-end , <:ₜ-end , refl
  meetₜ-subst σ (N-Msg p P N₁) (N-Var NV) ()
  meetₜ-subst σ (N-Msg p P N₁) (N-Sub km≤ N₂) ()
  meetₜ-subst σ (N-Msg D.⊕ P₁ S₁) (N-Msg p₂ P₂ S₂) eq
    with polarity-equal D.⊕ p₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with joinₚ′ P₁ P₂ in proto-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P₁<:P , P₂<:P)
    with meetₜ S₁ S₂ in cont-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (S , S<:S₁ , S<:S₂)
    with eq
  ... | refl
    with joinₚ′-subst σ P₁ P₂ proto-eq
       | meetₜ-subst σ S₁ S₂ cont-eq
  ... | P₁σ<:Pσ , P₂σ<:Pσ , proto-eqσ
      | Sσ<:S₁σ , Sσ<:S₂σ , cont-eqσ
    with meet-msgNF D.⊕
      (substNFProto′With σ P₁)
      (substNFProto′With σ P₂)
      (substNFTyWith σ S₁)
      (substNFTyWith σ S₂)
      proto-eqσ cont-eqσ
  ... | PS<:PS₁ , PS<:PS₂ , met = PS<:PS₁ , PS<:PS₂ , met
  meetₜ-subst σ (N-Msg D.⊝ P₁ S₁) (N-Msg p₂ P₂ S₂) eq
    with polarity-equal D.⊝ p₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with meetₚ′ P₁ P₂ in proto-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P<:P₁ , P<:P₂)
    with meetₜ S₁ S₂ in cont-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (S , S<:S₁ , S<:S₂)
    with eq
  ... | refl
    with meetₚ′-subst σ P₁ P₂ proto-eq
       | meetₜ-subst σ S₁ S₂ cont-eq
  ... | Pσ<:P₁σ , Pσ<:P₂σ , proto-eqσ
      | Sσ<:S₁σ , Sσ<:S₂σ , cont-eqσ
    with meet-msgNF D.⊝
      (substNFProto′With σ P₁)
      (substNFProto′With σ P₂)
      (substNFTyWith σ S₁)
      (substNFTyWith σ S₂)
      proto-eqσ cont-eqσ
  ... | PS<:PS₁ , PS<:PS₂ , met = PS<:PS₁ , PS<:PS₂ , met
  meetₜ-subst σ (N-ProtoD N₁) (N-Var NV) ()
  meetₜ-subst σ (N-ProtoD N₁) N-Base ()
  meetₜ-subst σ (N-ProtoD N₁) (N-Arrow N₂ N₃) ()
  meetₜ-subst σ (N-ProtoD N₁) (N-Pair N₂ N₃) ()
  meetₜ-subst σ (N-ProtoD N₁) (N-Poly K N₂) ()
  meetₜ-subst σ (N-ProtoD N₁) (N-Sub km≤ N₂) ()
  meetₜ-subst σ (N-ProtoD N₁) (N-ProtoD N₂) eq
    with meetₜ N₁ N₂ in meet-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (M , M<:N₁ , M<:N₂)
    with eq
  ... | refl
    with meetₜ-subst σ N₁ N₂ meet-eq
  ... | M<:N₁σ , M<:N₂σ , meet-eqσ
    rewrite meet-eqσ =
    <:ₜ-data M<:N₁σ , <:ₜ-data M<:N₂σ , refl

  mergeₚ-join-subst σ ⊕ (N-Normal P₁) (N-Normal P₂) eq
    with joinₚ′ P₁ P₂ in inner
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P₁<:P , P₂<:P)
    with eq
  ... | refl = joinₚ′-subst σ P₁ P₂ inner
  mergeₚ-join-subst σ ⊕ (N-Normal P₁) (N-Minus P₂) ()
  mergeₚ-join-subst σ ⊕ (N-Minus P₁) (N-Normal P₂) ()
  mergeₚ-join-subst σ ⊕ (N-Minus P₁) (N-Minus P₂) eq
    with meetₚ′ P₁ P₂ in inner
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P<:P₁ , P<:P₂)
    with eq
  ... | refl
    with meetₚ′-subst σ P₁ P₂ inner
  ... | Pσ<:P₁σ , Pσ<:P₂σ , meetσ
    with minus-join-from-meet meetσ
  ... | P₁σ<:Pσ , P₂σ<:Pσ , joined =
    P₁σ<:Pσ , P₂σ<:Pσ , joined
  mergeₚ-join-subst σ ⊝ (N-Normal P₁) (N-Normal P₂) eq
    with meetₚ′ P₁ P₂ in inner
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P<:P₁ , P<:P₂)
    with eq
  ... | refl = meetₚ′-subst σ P₁ P₂ inner
  mergeₚ-join-subst σ ⊝ (N-Normal P₁) (N-Minus P₂) ()
  mergeₚ-join-subst σ ⊝ (N-Minus P₁) (N-Normal P₂) ()
  mergeₚ-join-subst σ ⊝ (N-Minus P₁) (N-Minus P₂) eq
    with joinₚ′ P₁ P₂ in inner
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P₁<:P , P₂<:P)
    with eq
  ... | refl
    with joinₚ′-subst σ P₁ P₂ inner
  ... | P₁σ<:Pσ , P₂σ<:Pσ , joinσ
    with minus-meet-from-join joinσ
  ... | Pσ<:P₁σ , Pσ<:P₂σ , met =
    Pσ<:P₁σ , Pσ<:P₂σ , met
  mergeₚ-join-subst σ ⊘ P₁ P₂ eq
    with ty-equal (nfProtoTy P₁) (nfProtoTy P₂)
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes raw
    with eq
  ... | refl
    with ty-equal
      (nfProtoTy (substNFProtoWith σ P₁))
      (nfProtoTy (substNFProtoWith σ P₂))
  ... | no neq =
    ⊥-elim (neq (substNFProtoWith-≡ σ {N₁ = P₁} {N₂ = P₂} raw))
  ... | yes rawσ = refl , sym rawσ , refl

  mergeₚ-meet-subst σ ⊕ (N-Normal P₁) (N-Normal P₂) eq
    with meetₚ′ P₁ P₂ in inner
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P<:P₁ , P<:P₂)
    with eq
  ... | refl = meetₚ′-subst σ P₁ P₂ inner
  mergeₚ-meet-subst σ ⊕ (N-Normal P₁) (N-Minus P₂) ()
  mergeₚ-meet-subst σ ⊕ (N-Minus P₁) (N-Normal P₂) ()
  mergeₚ-meet-subst σ ⊕ (N-Minus P₁) (N-Minus P₂) eq
    with joinₚ′ P₁ P₂ in inner
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P₁<:P , P₂<:P)
    with eq
  ... | refl
    with joinₚ′-subst σ P₁ P₂ inner
  ... | P₁σ<:Pσ , P₂σ<:Pσ , joinσ
    with minus-meet-from-join joinσ
  ... | Pσ<:P₁σ , Pσ<:P₂σ , met =
    Pσ<:P₁σ , Pσ<:P₂σ , met
  mergeₚ-meet-subst σ ⊝ (N-Normal P₁) (N-Normal P₂) eq
    with joinₚ′ P₁ P₂ in inner
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P₁<:P , P₂<:P)
    with eq
  ... | refl = joinₚ′-subst σ P₁ P₂ inner
  mergeₚ-meet-subst σ ⊝ (N-Normal P₁) (N-Minus P₂) ()
  mergeₚ-meet-subst σ ⊝ (N-Minus P₁) (N-Normal P₂) ()
  mergeₚ-meet-subst σ ⊝ (N-Minus P₁) (N-Minus P₂) eq
    with meetₚ′ P₁ P₂ in inner
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P<:P₁ , P<:P₂)
    with eq
  ... | refl
    with meetₚ′-subst σ P₁ P₂ inner
  ... | Pσ<:P₁σ , Pσ<:P₂σ , meetσ
    with minus-join-from-meet meetσ
  ... | P₁σ<:Pσ , P₂σ<:Pσ , joined =
    P₁σ<:Pσ , P₂σ<:Pσ , joined
  mergeₚ-meet-subst σ ⊘ P₁ P₂ eq
    with ty-equal (nfProtoTy P₁) (nfProtoTy P₂)
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes raw
    with eq
  ... | refl
    with ty-equal
      (nfProtoTy (substNFProtoWith σ P₁))
      (nfProtoTy (substNFProtoWith σ P₂))
  ... | no neq =
    ⊥-elim (neq (substNFProtoWith-≡ σ {N₁ = P₁} {N₂ = P₂} raw))
  ... | yes rawσ = refl , rawσ , refl

  joinₚ′-subst σ
      (N-ProtoP {k = k₁} #c₁ v₁ P₁)
      (N-ProtoP {k = k₂} #c₂ v₂ P₂)
      eq
    with k₁ ≟ k₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with ⊙-equal v₁ v₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with mergeₚ-join v₁ P₁ P₂ in merge-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P₁<:P , P₂<:P)
    with eq
  ... | refl
    with mergeₚ-join-subst σ v₁ P₁ P₂ merge-eq
  ... | P₁σ<:Pσ , P₂σ<:Pσ , merge-eqσ
    with k₁ ≟ k₁
  ... | no neq = ⊥-elim (neq refl)
  ... | yes refl
    with ⊙-equal v₁ v₁
  ... | no neq = ⊥-elim (neq refl)
  ... | yes refl
    rewrite merge-eqσ =
    <:ₚ-plus (<:ₚ′-proto (p⊆p∪q #c₂) P₁σ<:Pσ) ,
    <:ₚ-plus (<:ₚ′-proto (q⊆p∪q #c₁ #c₂) P₂σ<:Pσ) ,
    refl
  joinₚ′-subst σ (N-ProtoP #c v P) (N-Up N) ()
  joinₚ′-subst σ (N-ProtoP #c v P) (N-Var x) ()
  joinₚ′-subst σ (N-Up N) (N-ProtoP #c v P) ()
  joinₚ′-subst σ
      (N-Up {pk = pk₁} {m = m₁} N₁)
      (N-Up {pk = pk₂} {m = m₂} N₂)
      eq
    with eq-prekind pk₁ pk₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-multiplicity m₁ m₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with joinₜ N₁ N₂ in join-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (N , N₁<:N , N₂<:N)
    with eq
  ... | refl
    with joinₜ-subst σ N₁ N₂ join-eq
  ... | N₁σ<:Nσ , N₂σ<:Nσ , join-eqσ
    rewrite join-eqσ =
    <:ₚ-plus (<:ₚ′-up N₁σ<:Nσ) ,
    <:ₚ-plus (<:ₚ′-up N₂σ<:Nσ) ,
    refl
  joinₚ′-subst σ (N-Up N) (N-Var x) ()
  joinₚ′-subst σ (N-Var x) (N-ProtoP #c v P) ()
  joinₚ′-subst σ (N-Var x) (N-Up N) ()
  joinₚ′-subst σ (N-Var x) (N-Var y) eq
    with ty-equal (nfProto′Ty (N-Var x)) (nfProto′Ty (N-Var y))
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq
  ... | refl = joinₚ-self (substNFProto′With σ (N-Var x))

  meetₚ′-subst σ
      (N-ProtoP {k = k₁} #c₁ v₁ P₁)
      (N-ProtoP {k = k₂} #c₂ v₂ P₂)
      eq
    with k₁ ≟ k₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with ⊙-equal v₁ v₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with mergeₚ-meet v₁ P₁ P₂ in merge-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (P , P<:P₁ , P<:P₂)
    with eq
  ... | refl
    with mergeₚ-meet-subst σ v₁ P₁ P₂ merge-eq
  ... | Pσ<:P₁σ , Pσ<:P₂σ , merge-eqσ
    with k₁ ≟ k₁
  ... | no neq = ⊥-elim (neq refl)
  ... | yes refl
    with ⊙-equal v₁ v₁
  ... | no neq = ⊥-elim (neq refl)
  ... | yes refl
    rewrite merge-eqσ =
    <:ₚ-plus (<:ₚ′-proto (p∩q⊆p #c₁ #c₂) Pσ<:P₁σ) ,
    <:ₚ-plus (<:ₚ′-proto (p∩q⊆q #c₁ #c₂) Pσ<:P₂σ) ,
    refl
  meetₚ′-subst σ (N-ProtoP #c v P) (N-Up N) ()
  meetₚ′-subst σ (N-ProtoP #c v P) (N-Var x) ()
  meetₚ′-subst σ (N-Up N) (N-ProtoP #c v P) ()
  meetₚ′-subst σ
      (N-Up {pk = pk₁} {m = m₁} N₁)
      (N-Up {pk = pk₂} {m = m₂} N₂)
      eq
    with eq-prekind pk₁ pk₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq-multiplicity m₁ m₂
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with meetₜ N₁ N₂ in meet-eq
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes (N , N<:N₁ , N<:N₂)
    with eq
  ... | refl
    with meetₜ-subst σ N₁ N₂ meet-eq
  ... | Nσ<:N₁σ , Nσ<:N₂σ , meet-eqσ
    rewrite meet-eqσ =
    <:ₚ-plus (<:ₚ′-up Nσ<:N₁σ) ,
    <:ₚ-plus (<:ₚ′-up Nσ<:N₂σ) ,
    refl
  meetₚ′-subst σ (N-Up N) (N-Var x) ()
  meetₚ′-subst σ (N-Var x) (N-ProtoP #c v P) ()
  meetₚ′-subst σ (N-Var x) (N-Up N) ()
  meetₚ′-subst σ (N-Var x) (N-Var y) eq
    with ty-equal (nfProto′Ty (N-Var x)) (nfProto′Ty (N-Var y))
  ... | no _ = ⊥-elim (no≢yes eq)
  ... | yes refl
    with eq
  ... | refl = meetₚ-self (substNFProto′With σ (N-Var x))
