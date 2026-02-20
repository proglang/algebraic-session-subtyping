module Kinds where

open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)

open import Util

data Multiplicity : Set where
  Lin Un : Multiplicity

variable
  m m′ m₁ m₂ m₃ : Multiplicity

data _≤m_ : Rel Multiplicity where
  ≤m-refl : m ≤m m
  ≤m-unl  : Un ≤m Lin

data PreKind : Set where
  KM KS KT : PreKind

variable
  pk pk′ pk₁ pk₂ pk₃ : PreKind

data _<p_ : Rel PreKind where
  <p-sm : KS <p KM
  <p-mt : KM <p KT
  <p-st : KS <p KT

data _≤p_ : Rel PreKind where
  ≤p-refl : pk ≤p pk
  ≤p-step : pk₁ <p pk₂ → pk₁ ≤p pk₂

data Kind : Set where
  KV : PreKind → Multiplicity → Kind
  KP : Kind

variable
  K K′ K₁ K₂ K₃ : Kind

data _≤k_ : Rel Kind where
  ≤k-top    : KP ≤k KP
  ≤k-step   : pk₁ ≤p pk₂ → m₁ ≤m m₂ → KV pk₁ m₁ ≤k KV pk₂ m₂

TLin = KV KT Lin
SLin = KV KS Lin
SUn  = KV KS Un
MUn  = KV KM Un

-- properties

-- irrelevance

≤m-irrelevant : ∀ {m₁ m₂} (≤m₁ ≤m₂ : m₁ ≤m m₂) → ≤m₁ ≡ ≤m₂
≤m-irrelevant ≤m-refl ≤m-refl = refl
≤m-irrelevant ≤m-unl ≤m-unl = refl

<p-irrelevant : ∀ {pk₁ pk₂} (<p₁ <p₂ : pk₁ <p pk₂) → <p₁ ≡ <p₂
<p-irrelevant <p-sm <p-sm = refl
<p-irrelevant <p-mt <p-mt = refl
<p-irrelevant <p-st <p-st = refl

≤p-irrelevant : ∀ {pk₁ pk₂} (≤pk₁ ≤pk₂ : pk₁ ≤p pk₂) → ≤pk₁ ≡ ≤pk₂
≤p-irrelevant ≤p-refl ≤p-refl = refl
≤p-irrelevant (≤p-step <p-sm) (≤p-step <p-sm) = refl
≤p-irrelevant (≤p-step <p-mt) (≤p-step <p-mt) = refl
≤p-irrelevant (≤p-step <p-st) (≤p-step <p-st) = refl

≤k-irrelevant : ∀ {K₁ K₂} (≤k₁ ≤k₂ : K₁ ≤k K₂) → ≤k₁ ≡ ≤k₂
≤k-irrelevant ≤k-top ≤k-top = refl
≤k-irrelevant (≤k-step ≤pk₁ ≤m₁) (≤k-step ≤pk₂ ≤m₂) = cong₂ ≤k-step (≤p-irrelevant ≤pk₁ ≤pk₂) (≤m-irrelevant ≤m₁ ≤m₂)

-- reflexivity

≤k-refl : K ≤k K
≤k-refl {KV pk m} = ≤k-step ≤p-refl ≤m-refl
≤k-refl {KP} = ≤k-top

-- transitivity

≤m-trans : m₁ ≤m m₂ → m₂ ≤m m₃ → m₁ ≤m m₃
≤m-trans ≤m-refl ≤m-refl = ≤m-refl
≤m-trans ≤m-refl ≤m-unl = ≤m-unl
≤m-trans ≤m-unl ≤m-refl = ≤m-unl

≤p-trans : pk₁ ≤p pk₂ → pk₂ ≤p pk₃ → pk₁ ≤p pk₃
≤p-trans ≤p-refl pk₂≤pk₃ = pk₂≤pk₃
≤p-trans (≤p-step <p-sm) ≤p-refl = ≤p-step <p-sm
≤p-trans (≤p-step <p-sm) (≤p-step <p-mt) = ≤p-step <p-st
≤p-trans (≤p-step <p-mt) ≤p-refl = ≤p-step <p-mt
≤p-trans (≤p-step <p-st) ≤p-refl = ≤p-step <p-st

≤k-trans : K₁ ≤k K₂ → K₂ ≤k K₃ → K₁ ≤k K₃
≤k-trans ≤k-top ≤k-top = ≤k-top
≤k-trans (≤k-step pk₁≤pk₂ m₁≤m₂) (≤k-step pk₂≤pk₃ m₂≤m₃) = ≤k-step (≤p-trans pk₁≤pk₂ pk₂≤pk₃) (≤m-trans m₁≤m₂ m₂≤m₃)

-- decidability

eq-multiplicity : ∀ (m₁ m₂ : Multiplicity) → Dec (m₁ ≡ m₂)
eq-multiplicity Lin Lin = yes refl
eq-multiplicity Lin Un = no λ()
eq-multiplicity Un Lin = no λ()
eq-multiplicity Un Un = yes refl

eq-prekind : ∀ (pk₁ pk₂ : PreKind) → Dec (pk₁ ≡ pk₂)
eq-prekind KM KM = yes refl
eq-prekind KM KS = no λ()
eq-prekind KM KT = no λ()
eq-prekind KS KM = no λ()
eq-prekind KS KS = yes refl
eq-prekind KS KT = no λ()
eq-prekind KT KM = no λ()
eq-prekind KT KS = no λ()
eq-prekind KT KT = yes refl

eq-kind : ∀ (K₁ K₂ : Kind) → Dec (K₁ ≡ K₂)
eq-kind (KV pk₁ m₁) (KV pk₂ m₂)
  with eq-prekind pk₁ pk₂
... | no pk≢ = no (λ{ refl → pk≢ refl})
... | yes refl
  with eq-multiplicity m₁ m₂
... | no m≢ = no (λ{refl → m≢ refl})
... | yes refl = yes refl
eq-kind (KV _ _) KP = no λ()
eq-kind KP (KV _ _) = no λ()
eq-kind KP KP = yes refl

