module Kinds where

open import Util

data Multiplicity : Set where
  Lin Un : Multiplicity

variable
  m m′ m₁ m₂ : Multiplicity

data _≤m_ : Rel Multiplicity where
  ≤m-refl : m ≤m m
  ≤m-unl  : Un ≤m Lin

data PreKind : Set where
  KM KS KT : PreKind

variable
  pk pk′ pk₁ pk₂ : PreKind

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
  K K′ K₁ K₂ : Kind

data _≤k_ : Rel Kind where
  ≤k-top    : KP ≤k KP
  ≤k-step   : pk₁ ≤p pk₂ → m₁ ≤m m₂ → KV pk₁ m₁ ≤k KV pk₂ m₂

TLin = KV KT Lin
SLin = KV KS Lin
SUn  = KV KS Un
MUn  = KV KM Un

