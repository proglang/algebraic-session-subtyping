module ExprTypingUniquenessFresh where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
import Data.Fin.Subset as Subset
open import Data.Maybe using (just)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; subst; sym; trans)
open import Util using (just-injective)

open import Kinds
open import Variance using (Variance)
open import NormalTypes using (N-Arrow)
open import ExprSyntax using
  ( NfTy
  ; Expr
  ; Value
  ; Const
  ; E-Val
  ; E-LetPair
  ; E-Match
  )
open import ExprNormalTyping
open import AlgorithmicNFSubtyping using (_<:ₜ_; <:ₜ-refl)
import AlgorithmicNFSound as NFSound
import ExprTypingStrengthening as Strengthening

take-membership-fresh :
  ∀ {Δ n pk} {Γ Γ′ : Ctx Δ n} {x : Fin n}
    {T : NfTy Δ (KV pk Lin)}
  → Γ ⊢ˡ x ∶ T ⊣ Γ′
  → Γ ∋ˡ x ∶ T
take-membership-fresh take-here = hereˡ
take-membership-fresh (take-thereˡ take) =
  thereˡˡ (take-membership-fresh take)
take-membership-fresh (take-thereᵘ take) =
  thereˡᵘ (take-membership-fresh take)
take-membership-fresh (take-there✖ take) =
  thereˡ✖ (take-membership-fresh take)

take-kind-unique :
  ∀ {Δ n pk₁ pk₂} {Γ : Ctx Δ n} {x : Fin n}
    {T : NfTy Δ (KV pk₁ Lin)} {U : NfTy Δ (KV pk₂ Lin)}
    {Γ₁ Γ₂ : Ctx Δ n}
  → Γ ⊢ˡ x ∶ T ⊣ Γ₁
  → Γ ⊢ˡ x ∶ U ⊣ Γ₂
  → pk₁ ≡ pk₂
take-kind-unique take-here take-here = refl
take-kind-unique (take-thereˡ take₁) (take-thereˡ take₂) =
  take-kind-unique take₁ take₂
take-kind-unique (take-thereᵘ take₁) (take-thereᵘ take₂) =
  take-kind-unique take₁ take₂
take-kind-unique (take-there✖ take₁) (take-there✖ take₂) =
  take-kind-unique take₁ take₂

take-unique :
  ∀ {Δ n pk} {Γ : Ctx Δ n} {x : Fin n}
    {T U : NfTy Δ (KV pk Lin)} {Γ₁ Γ₂ : Ctx Δ n}
  → Γ ⊢ˡ x ∶ T ⊣ Γ₁
  → Γ ⊢ˡ x ∶ U ⊣ Γ₂
  → (T ≡ U) × (Γ₁ ≡ Γ₂)
take-unique take-here take-here = refl , refl
take-unique (take-thereˡ {U = U} take₁) (take-thereˡ take₂)
  with take-unique take₁ take₂
... | eqT , eqΓ = eqT , cong (B-Lin U ▻_) eqΓ
take-unique (take-thereᵘ {U = U} take₁) (take-thereᵘ take₂)
  with take-unique take₁ take₂
... | eqT , eqΓ = eqT , cong (B-Un U ▻_) eqΓ
take-unique (take-there✖ {U = U} take₁) (take-there✖ take₂)
  with take-unique take₁ take₂
... | eqT , eqΓ = eqT , cong (B-Used U ▻_) eqΓ

un-kind-unique :
  ∀ {Δ n pk₁ pk₂} {Γ : Ctx Δ n} {x : Fin n}
    {T : NfTy Δ (KV pk₁ Un)} {U : NfTy Δ (KV pk₂ Un)}
  → Γ ∋ᵘ x ∶ T
  → Γ ∋ᵘ x ∶ U
  → pk₁ ≡ pk₂
un-kind-unique hereᵘ hereᵘ = refl
un-kind-unique (thereᵘˡ x∈) (thereᵘˡ y∈) = un-kind-unique x∈ y∈
un-kind-unique (thereᵘᵘ x∈) (thereᵘᵘ y∈) = un-kind-unique x∈ y∈
un-kind-unique (thereᵘ✖ x∈) (thereᵘ✖ y∈) = un-kind-unique x∈ y∈

un-type-unique :
  ∀ {Δ n pk} {Γ : Ctx Δ n} {x : Fin n}
    {T U : NfTy Δ (KV pk Un)}
  → Γ ∋ᵘ x ∶ T
  → Γ ∋ᵘ x ∶ U
  → T ≡ U
un-type-unique hereᵘ hereᵘ = refl
un-type-unique (thereᵘˡ x∈) (thereᵘˡ y∈) = un-type-unique x∈ y∈
un-type-unique (thereᵘᵘ x∈) (thereᵘᵘ y∈) = un-type-unique x∈ y∈
un-type-unique (thereᵘ✖ x∈) (thereᵘ✖ y∈) = un-type-unique x∈ y∈

lin-un-disjoint :
  ∀ {Δ n pk₁ pk₂} {Γ : Ctx Δ n} {x : Fin n}
    {T : NfTy Δ (KV pk₁ Lin)} {U : NfTy Δ (KV pk₂ Un)}
  → Γ ∋ˡ x ∶ T
  → Γ ∋ᵘ x ∶ U
  → ⊥
lin-un-disjoint hereˡ ()
lin-un-disjoint (thereˡˡ x∈) (thereᵘˡ y∈) = lin-un-disjoint x∈ y∈
lin-un-disjoint (thereˡᵘ x∈) (thereᵘᵘ y∈) = lin-un-disjoint x∈ y∈
lin-un-disjoint (thereˡ✖ x∈) (thereᵘ✖ y∈) = lin-un-disjoint x∈ y∈

const-kind-unique :
  ∀ {Δ c pk₁ m₁ pk₂ m₂}
    {T : NfTy Δ (KV pk₁ m₁)} {U : NfTy Δ (KV pk₂ m₂)}
  → ConstTy c T
  → ConstTy c U
  → (pk₁ ≡ pk₂) × (m₁ ≡ m₂)
const-kind-unique CT-Unit CT-Unit = refl , refl
const-kind-unique CT-Fork CT-Fork = refl , refl
const-kind-unique CT-New CT-New = refl , refl
const-kind-unique CT-Receive CT-Receive = refl , refl
const-kind-unique CT-Send CT-Send = refl , refl
const-kind-unique CT-Close CT-Close = refl , refl
const-kind-unique CT-Select CT-Select = refl , refl

const-type-unique :
  ∀ {Δ c K} {T U : NfTy Δ K}
  → ConstTy c T
  → ConstTy c U
  → T ≡ U
const-type-unique CT-Unit CT-Unit = refl
const-type-unique CT-Fork CT-Fork = refl
const-type-unique CT-New CT-New = refl
const-type-unique CT-Receive CT-Receive = refl
const-type-unique CT-Send CT-Send = refl
const-type-unique CT-Close CT-Close = refl
const-type-unique CT-Select CT-Select = refl

arrow-cod-kind :
  ∀ {Δ pk₁ m₁ pk₂ m₂ pk₁′ m₁′ pk₂′ m₂′ m}
    {A : NfTy Δ (KV pk₁ m₁)} {B : NfTy Δ (KV pk₂ m₂)}
    {A′ : NfTy Δ (KV pk₁′ m₁′)} {B′ : NfTy Δ (KV pk₂′ m₂′)}
  → N-Arrow {m = m} A B ≡ N-Arrow {m = m} A′ B′
  → (pk₂ ≡ pk₂′) × (m₂ ≡ m₂′)
arrow-cod-kind refl = refl , refl

match-input-injective :
  ∀ {Δ k}
    {ss₁ ss₂ : Subset.Subset (suc k)} {v₁ v₂ : Variance}
    {P₁ P₂ : NfTy Δ KP} {S₁ S₂ : NfTy Δ SLin}
  → MatchBranchInput ss₁ v₁ P₁ S₁ ≡ MatchBranchInput ss₂ v₂ P₂ S₂
  → (ss₁ ≡ ss₂) × (v₁ ≡ v₂) × (P₁ ≡ P₂) × (S₁ ≡ S₂)
match-input-injective refl = refl , refl , refl , refl

mutual

  value-kind-unique :
    ∀ {Δ n pk₁ m₁ pk₂ m₂} {Γ : Ctx Δ n} {v : Value Δ n}
      {T : NfTy Δ (KV pk₁ m₁)} {U : NfTy Δ (KV pk₂ m₂)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ᵥ v ⇒ T ⊣ Γ₁
    → Γ ⊢ᵥ v ⇒ U ⊣ Γ₂
    → (pk₁ ≡ pk₂) × (m₁ ≡ m₂)
  value-kind-unique (TV-Const c₁) (TV-Const c₂) =
    const-kind-unique c₁ c₂
  value-kind-unique (TV-Var-Lin take₁) (TV-Var-Lin take₂) =
    take-kind-unique take₁ take₂ , refl
  value-kind-unique (TV-Var-Lin take) (TV-Var-Un x∈) =
    ⊥-elim (lin-un-disjoint (take-membership-fresh take) x∈)
  value-kind-unique (TV-Var-Un x∈) (TV-Var-Lin take) =
    ⊥-elim (lin-un-disjoint (take-membership-fresh take) x∈)
  value-kind-unique (TV-Var-Un x∈) (TV-Var-Un y∈) =
    un-kind-unique x∈ y∈ , refl
  value-kind-unique (TV-Abs _) (TV-Abs _) = refl , refl
  value-kind-unique (TV-Rec _) (TV-Rec _) = refl , refl
  value-kind-unique (TV-TAbs d₁) (TV-TAbs d₂)
    with value-kind-unique d₁ d₂
  ... | _ , eqm = refl , eqm
  value-kind-unique (TV-Pair d₁ _) (TV-Pair d₂ _) =
    refl , proj₂ (value-kind-unique d₁ d₂)
  value-kind-unique TV-Receive₁ TV-Receive₁ = refl , refl
  value-kind-unique TV-Receive₂ TV-Receive₂ = refl , refl
  value-kind-unique TV-Send₁ TV-Send₁ = refl , refl
  value-kind-unique TV-Send₂ TV-Send₂ = refl , refl
  value-kind-unique TV-Select₁ TV-Select₁ = refl , refl
  value-kind-unique TV-Select₂ TV-Select₂ = refl , refl

  synth-kind-unique :
    ∀ {Δ n pk₁ m₁ pk₂ m₂} {Γ : Ctx Δ n} {e : Expr Δ n}
      {T : NfTy Δ (KV pk₁ m₁)} {U : NfTy Δ (KV pk₂ m₂)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ e ⇒ T ⊣ Γ₁
    → Γ ⊢ e ⇒ U ⊣ Γ₂
    → (pk₁ ≡ pk₂) × (m₁ ≡ m₂)
  synth-kind-unique (T-Val d₁) (T-Val d₂) = value-kind-unique d₁ d₂
  synth-kind-unique (T-Pair d₁ _) (T-Pair d₂ _)
    with synth-kind-unique d₁ d₂
  ... | _ , eqm = refl , eqm
  synth-kind-unique (T-App f₁ _) (T-App f₂ _)
    with synth-kind-unique f₁ f₂
  ... | refl , refl
    with synth-unique f₁ f₂
  ... | eqArr , _ = arrow-cod-kind eqArr
  synth-kind-unique (T-LetUnit d₁ body₁) (T-LetUnit d₂ body₂)
    with check-unique d₁ d₂
  ... | refl = synth-kind-unique body₁ body₂
  synth-kind-unique (T-LetPair d₁ body₁) (T-LetPair d₂ body₂)
    with synth-unique d₁ d₂
  ... | refl , refl = synth-kind-unique body₁ body₂
  synth-kind-unique
      (T-Match {ne = ne} d₁ bs₁ _)
      (T-Match {ne = .ne} d₂ bs₂ _)
    with synth-unique d₁ d₂
  ... | eqIn , refl
    with match-input-injective eqIn
  ... | refl , refl , refl , refl
    with ne
  ... | i , i∈ = synth-kind-unique (bs₁ i i∈) (bs₂ i i∈)
  synth-kind-unique (T-TApp d₁) (T-TApp d₂)
    with synth-kind-unique d₁ d₂
  ... | _ , eqm = refl , eqm

  check-kind-unique :
    ∀ {Δ n pk₁ m₁ pk₂ m₂} {Γ : Ctx Δ n} {e : Expr Δ n}
      {T : NfTy Δ (KV pk₁ m₁)} {U : NfTy Δ (KV pk₂ m₂)}
      {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ e ⇐ T ⊣ Γ₁
    → Γ ⊢ e ⇐ U ⊣ Γ₂
    → (pk₁ ≡ pk₂) × (m₁ ≡ m₂)
  check-kind-unique (T-Check d₁ _) (T-Check d₂ _) =
    synth-kind-unique d₁ d₂

  value-unique :
    ∀ {Δ n pk m} {Γ : Ctx Δ n} {v : Value Δ n}
      {T U : NfTy Δ (KV pk m)} {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ᵥ v ⇒ T ⊣ Γ₁
    → Γ ⊢ᵥ v ⇒ U ⊣ Γ₂
    → (T ≡ U) × (Γ₁ ≡ Γ₂)
  value-unique (TV-Const c₁) (TV-Const c₂) =
    const-type-unique c₁ c₂ , refl
  value-unique (TV-Var-Lin take₁) (TV-Var-Lin take₂) =
    take-unique take₁ take₂
  value-unique (TV-Var-Un x∈) (TV-Var-Un y∈) =
    un-type-unique x∈ y∈ , refl
  value-unique (TV-Abs body₁) (TV-Abs body₂)
    with synth-kind-unique body₁ body₂
  ... | refl , refl
    with synth-unique body₁ body₂
  ... | eqT , eqΓ =
    cong (N-Arrow _) eqT , cong (λ where (_ ▻ Γtail) → Γtail) eqΓ
  value-unique (TV-Rec _) (TV-Rec _) = refl , refl
  value-unique (TV-TAbs body₁) (TV-TAbs body₂)
    with value-unique body₁ body₂
  ... | eqT , eqΓ = cong polyNf eqT , wkCtx-injective eqΓ
  value-unique (TV-Pair d₁₁ d₁₂) (TV-Pair d₂₁ d₂₂)
    with value-kind-unique d₁₁ d₂₁
  ... | refl , refl
    with value-unique d₁₁ d₂₁
  ... | eqT , refl
    with value-kind-unique d₁₂ d₂₂
  ... | refl , refl
    with value-unique d₁₂ d₂₂
  ... | eqU , eqΓ = cong₂ pairNf eqT eqU , eqΓ
  value-unique TV-Receive₁ TV-Receive₁ = refl , refl
  value-unique TV-Receive₂ TV-Receive₂ = refl , refl
  value-unique TV-Send₁ TV-Send₁ = refl , refl
  value-unique TV-Send₂ TV-Send₂ = refl , refl
  value-unique TV-Select₁ TV-Select₁ = refl , refl
  value-unique TV-Select₂ TV-Select₂ = refl , refl

  synth-unique-match :
    ∀ {Δ n k pk m} {Γ Γ₃ Γ₃′ : Ctx Δ n} {e : Expr Δ n}
      {ssbranches : Subset.Subset (suc k)} {ne : Subset.Nonempty ssbranches}
      {branches : (i : Fin (suc k)) → i Subset.∈ ssbranches → Expr Δ (suc n)}
      {U₁ U₂ : NfTy Δ (KV pk m)}
    → Γ ⊢ E-Match {ss = ssbranches} e ne branches ⇒ U₁ ⊣ Γ₃
    → Γ ⊢ E-Match {ss = ssbranches} e ne branches ⇒ U₂ ⊣ Γ₃′
    → (U₁ ≡ U₂) × (Γ₃ ≡ Γ₃′)
  synth-unique-match
      {U₁ = U₁} {U₂ = U₂}
      (T-Match {ssbranches = ssbranches} {ne = ne} {branches = branches}
        {V = V₁} d₁ bs₁ bj₁)
      (T-Match {ssbranches = .ssbranches} {ne = .ne} {branches = .branches}
        {V = V₂} d₂ bs₂ bj₂)
    with synth-unique d₁ d₂
  ... | eqIn , eqmid
    with match-input-injective eqIn
  ... | refl , refl , refl , refl
    rewrite eqmid
    with ne
  ... | i , i∈
    with synth-unique (bs₁ i i∈) (bs₂ i i∈)
  ... | _ , eqout =
    let eqΓ₃ = cong (λ where (_ ▻ Γtail) → Γtail) eqout in
    let V₂<:V₁ = λ j j∈ →
          subst
            (λ X → X <:ₜ V₁ j j∈)
            (proj₁ (synth-unique (bs₁ j j∈) (bs₂ j j∈)))
            (<:ₜ-refl (V₁ j j∈)) in
    let V₁<:V₂ = λ j j∈ →
          subst
            (λ X → V₁ j j∈ <:ₜ X)
            (proj₁ (synth-unique (bs₁ j j∈) (bs₂ j j∈)))
            (<:ₜ-refl (V₁ j j∈)) in
    let U₂′ , sub₂′ , bj₂′ , U₂′<:U₁ =
          Strengthening.branchjoin⁺-monotone bj₁ V₂<:V₁ in
    let eqU₂′ = cong proj₁ (just-injective (trans (sym bj₂′) bj₂)) in
    let U₂<:U₁ = subst (λ X → X <:ₜ U₁) eqU₂′ U₂′<:U₁ in
    let U₁′ , sub₁′ , bj₁′ , U₁′<:U₂ =
          Strengthening.branchjoin⁺-monotone bj₂ V₁<:V₂ in
    let eqU₁′ = cong proj₁ (just-injective (trans (sym bj₁′) bj₁)) in
    let U₁<:U₂ = subst (λ X → X <:ₜ U₂) eqU₁′ U₁′<:U₂ in
    NFSound.<:ₜ-antisym U₁<:U₂ U₂<:U₁ , eqΓ₃

  synth-unique :
    ∀ {Δ n pk m} {Γ : Ctx Δ n} {e : Expr Δ n}
      {T U : NfTy Δ (KV pk m)} {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ e ⇒ T ⊣ Γ₁
    → Γ ⊢ e ⇒ U ⊣ Γ₂
    → (T ≡ U) × (Γ₁ ≡ Γ₂)
  synth-unique (T-Val d₁) (T-Val d₂) = value-unique d₁ d₂
  synth-unique (T-Pair d₁₁ d₁₂) (T-Pair d₂₁ d₂₂)
    with synth-kind-unique d₁₁ d₂₁
  ... | refl , refl
    with synth-unique d₁₁ d₂₁
  ... | eqT , refl
    with synth-kind-unique d₁₂ d₂₂
  ... | refl , refl
    with synth-unique d₁₂ d₂₂
  ... | eqU , eqout = cong₂ pairNf eqT eqU , eqout
  synth-unique (T-App f₁ a₁) (T-App f₂ a₂)
    with synth-kind-unique f₁ f₂
  ... | refl , refl
    with synth-unique f₁ f₂
  ... | refl , refl
    with check-kind-unique a₁ a₂
  ... | refl , refl
    with check-unique a₁ a₂
  ... | eqout = refl , eqout
  synth-unique (T-LetUnit d₁ body₁) (T-LetUnit d₂ body₂)
    with check-unique d₁ d₂
  ... | refl = synth-unique body₁ body₂
  synth-unique (T-LetPair d₁ body₁) (T-LetPair d₂ body₂)
    with synth-kind-unique d₁ d₂
  ... | refl , refl
    with synth-unique d₁ d₂
  ... | refl , refl
    with synth-unique body₁ body₂
  ... | eqT , eqbody =
    eqT , cong (λ where (_ ▻ (_ ▻ Γtail)) → Γtail) eqbody
  synth-unique
      d₁@(T-Match {ssbranches = ssbranches} {ne = ne} {branches = branches} _ _ _)
      d₂@(T-Match {ssbranches = .ssbranches} {ne = .ne} {branches = .branches} _ _ _) =
    synth-unique-match
      {ssbranches = ssbranches} {ne = ne} {branches = branches} d₁ d₂
  synth-unique (T-TApp d₁) (T-TApp d₂)
    with synth-unique d₁ d₂
  ... | eqpoly , eqout
    rewrite polyNf-injective eqpoly = refl , eqout

  check-unique :
    ∀ {Δ n pk m} {Γ : Ctx Δ n} {e : Expr Δ n}
      {T U : NfTy Δ (KV pk m)} {Γ₁ Γ₂ : Ctx Δ n}
    → Γ ⊢ e ⇐ T ⊣ Γ₁
    → Γ ⊢ e ⇐ U ⊣ Γ₂
    → Γ₁ ≡ Γ₂
  check-unique (T-Check d₁ _) (T-Check d₂ _) = proj₂ (synth-unique d₁ d₂)

value-output-unique :
  ∀ {Δ n pk m} {Γ : Ctx Δ n} {v : Value Δ n}
    {T U : NfTy Δ (KV pk m)} {Γ₁ Γ₂ : Ctx Δ n}
  → Γ ⊢ᵥ v ⇒ T ⊣ Γ₁
  → Γ ⊢ᵥ v ⇒ U ⊣ Γ₂
  → Γ₁ ≡ Γ₂
value-output-unique d₁ d₂ = proj₂ (value-unique d₁ d₂)
