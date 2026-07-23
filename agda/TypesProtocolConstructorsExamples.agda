module TypesProtocolConstructorsExamples where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans)
open import Util
open import Kinds
open import Duality
open import Variance using (Variance; vswap; vcompose)
open import Types

open import TypesProtocolConstructors using (
    UsageVariance; swapUsage; composeUsage; joinUsage; usageVariance-Var; usageVariance;
    AllConstructorSignatures; ProtocolConstructors; ConstructorSignature;
    materialize; SelectTy0)

-- some examples for constructors of protocol types, to make sure the definitions are consistent and to have some test cases for the proofs about them
-- * three one-parameter protocols with one constructor each, with different variances
-- the first one is covariant, so the constructor takes the parameter of the protocol type itself
-- the second one is contravariant, so the constructor takes the negated parameter of the protocol type
-- the third one is invariant, so the constructor takes both the parameter of the protocol type and the negated parameter of the protocol type
-- * one two-parameter protocol with two constructors, both covariant in the first parameter and invariant in the second parameter

myProtocolConstructors : (n : ℕ) → (v : Variance) → AllConstructorSignatures n v
myProtocolConstructors zero v ()
myProtocolConstructors (suc zero) ⊕ fzero = ((T-Var (here refl)) ∷ []) , inj₁ refl
myProtocolConstructors (suc zero) ⊝ fzero = ((T-Minus (T-Var (here refl))) ∷ []) , inj₁ refl
myProtocolConstructors (suc zero) ⊘ fzero = (T-Var (here refl) ∷ (T-Minus (T-Var (here refl))) ∷ []) , inj₁ refl
myProtocolConstructors (suc (suc zero)) ⊕ fzero = [] , inj₂ refl
myProtocolConstructors (suc (suc zero)) ⊕ (fsuc fzero) = (T-Var (here refl) ∷ T-ProtoP {k = 2} Subset.⊤ ⊕ (T-Var (here refl)) ∷ []) 
                                                        , inj₁ refl
myProtocolConstructors (suc (suc zero)) v i = ProtocolConstructors (suc (suc zero)) v i
myProtocolConstructors (suc (suc (suc n))) v i = ProtocolConstructors (suc (suc (suc n))) v i

module Example0 where
    -- check that application of SelectTy0 to the constructor signature of the covariant protocol example gives the expected type

    example : Ty [] SLin → Ty [] TLin
    example S = SelectTy0 (suc zero) ⊕ 
                (myProtocolConstructors (suc zero) ⊕) 
                fzero
                (T-Up T-Base)
                S
    
    example1 : Ty [] SLin → Ty [] TLin
    example1 S = T-Arrow
                        (example S)
                        (T-Sub (≤k-step (≤p-step <p-st) ≤m-refl)
                             (T-Msg ⊕ (T-ProtoP {k = 2} Subset.⊤ ⊕ (T-Up T-Base)) S))
    _ : example ≡ λ S → T-Arrow
                             (T-Msg ⊕ (T-ProtoP Subset.⁅ fzero ⁆ ⊕ (T-Up T-Base)) S)
                             (T-Msg ⊕ (T-Up T-Base) S)
    _ = refl

module Example1 where
    -- one covariant protocol with one constructor, which takes the parameter of the protocol type itself
    -- protocol P-Example1 x = C-Example1 x

  example : AllConstructorSignatures (suc zero) ⊕
  example = myProtocolConstructors (suc zero) ⊕

  example0 : ConstructorSignature ⊕
  example0 = myProtocolConstructors (suc zero) ⊕ fzero

  mat-example0 : Ty [] SLin → Ty [] SLin
  mat-example0 S = materialize example0 ⊕ (T-Up T-Base) S

  _ : mat-example0 ≡ λ S → T-Msg ⊕ (T-Up T-Base) S
  _ = refl

  mat-example1 : Ty (KP ∷ []) SLin → Ty (KP ∷ []) SLin
  mat-example1 S = materialize example0 ⊕ (T-Var (here refl)) S

  _ : mat-example1 ≡ λ S → T-Msg ⊕ (T-Var (here refl)) S
  _ = refl

module Example2 where
    -- one contravariant protocol with one constructor, which takes the negated parameter of the protocol type
    -- protocol P-Example2 x = C-Example2 -x

    example : AllConstructorSignatures (suc zero) ⊝
    example = myProtocolConstructors (suc zero) ⊝

    example0 : ConstructorSignature ⊝
    example0 = example fzero

    mat-example0 : Ty [] SLin → Ty [] SLin
    mat-example0 S = materialize example0 ⊕ (T-Up T-Base) S

    _ : mat-example0 ≡ λ S → T-Msg ⊕ (T-Minus (T-Up T-Base)) S
    _ = refl

    mat-example1 : Ty (KP ∷ []) SLin → Ty (KP ∷ []) SLin
    mat-example1 S = materialize example0 ⊕ (T-Var (here refl)) S

    _ : mat-example1 ≡ λ S → T-Msg ⊕ (T-Minus (T-Var (here refl))) S
    _ = refl
