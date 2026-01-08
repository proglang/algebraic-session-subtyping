module Kinds where

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
