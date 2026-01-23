module Types where

open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Fin.Subset as Subset using ()
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Sum
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst; inspect; Reveal_·_is_)
open import Function using (const)

open import Util
open import Kinds
open import Duality
open import Kits

variable
  n : ℕ
  Δ Δ₁ Δ₂ Δ₃ Δ′ : List Kind

-- variance of parameter of protocol type constructor
-- ⊕ : covariant - parameter appears under even number of T-Minus operators
-- ⊝ : contravariant - parameter appears under odd number of T-Minus operators
-- ⊙ : invariant - parameter appears under even and odd numbers of T-Minus operators

data Variance : Set where
  ⊕ ⊝ ⊘ : Variance

variable ⊙ : Variance

module _ where

  variable k : ℕ

  data Ty (Δ : List Kind) : Kind → Set where
    T-Var   : K ∈ Δ → Ty Δ K
    T-Base  : Ty Δ MUn
    T-Arrow : KM ≤p pk → Ty Δ TLin → Ty Δ TLin → Ty Δ (KV pk m)
    T-Poly  : Ty (K′ ∷ Δ) (KV KT m) → Ty Δ (KV KT m)
    T-Sub   : KV pk m ≤k KV pk′ m′ → Ty Δ (KV pk m) → Ty Δ (KV pk′ m′)

    -- session types

    T-Dual  : Dualizable K → Ty Δ K → Ty Δ K
    T-End   : Ty Δ SUn
    T-Msg   : Polarity → Ty Δ KP → Ty Δ SLin → Ty Δ SLin

    -- protocol types

    T-Up    : Ty Δ (KV pk m) → Ty Δ KP
    T-Minus : Ty Δ KP → Ty Δ KP

    T-ProtoD : Ty Δ TLin → Ty Δ TLin      -- a data protocol
    T-ProtoP : Subset.Subset k → Variance → Ty Δ KP → Ty Δ KP          -- a general protocol with k constructors

  t-var-injective : {x y : K ∈ Δ} → T-Var x ≡ T-Var y → x ≡ y
  t-var-injective refl = refl

  Ty-Syntax : Syntax
  Ty-Syntax = record
    { Sort = Kind
    ; _⊢_  = Ty
    ; `_   = T-Var
    ; `-injective = t-var-injective
    }

  open Syntax Ty-Syntax hiding (Sort)

  _⋯_ : ⦃ KT : Kit _∋/⊢_ ⦄ → Ty Δ₁ K → Δ₁ –[ KT ]→ Δ₂ → Ty Δ₂ K
  T-Var x ⋯ ϕ = `/id (ϕ _ x)
  T-Base ⋯ ϕ = T-Base
  T-Arrow x t u ⋯ ϕ = T-Arrow x (t ⋯ ϕ) (u ⋯ ϕ)
  T-Poly t ⋯ ϕ = T-Poly (t ⋯ (ϕ ↑ _))
  T-Sub x t ⋯ ϕ = T-Sub x (t ⋯ ϕ)
  T-Dual x t ⋯ ϕ = T-Dual x (t ⋯ ϕ)
  T-End ⋯ ϕ = T-End
  T-Msg x t u ⋯ ϕ = T-Msg x (t ⋯ ϕ) (u ⋯ ϕ)
  T-Up t ⋯ ϕ = T-Up (t ⋯ ϕ)
  T-Minus t ⋯ ϕ = T-Minus (t ⋯ ϕ)
  T-ProtoD t ⋯ ϕ = T-ProtoD (t ⋯ ϕ)
  T-ProtoP x v t ⋯ ϕ = T-ProtoP x v (t ⋯ ϕ)

  ⋯-id : ⦃ KT : Kit _∋/⊢_ ⦄ (t : Ty Δ K) → t ⋯ id ≡ t
  ⋯-id (T-Var x) = `/`-is-` x
  ⋯-id T-Base = refl
  ⋯-id (T-Arrow x t u) = cong₂ (T-Arrow x) (⋯-id t) (⋯-id u)
  ⋯-id (T-Poly t) = cong T-Poly (trans (cong (t ⋯_) (~-ext id↑~id)) (⋯-id t))
  ⋯-id (T-Sub x t) = cong (T-Sub x) (⋯-id t)
  ⋯-id (T-Dual x t) = cong (T-Dual x) (⋯-id t)
  ⋯-id T-End = refl
  ⋯-id (T-Msg x t u) = cong₂ (T-Msg x) (⋯-id t) (⋯-id u)
  ⋯-id (T-Up t) = cong T-Up (⋯-id t)
  ⋯-id (T-Minus t) = cong T-Minus (⋯-id t)
  ⋯-id (T-ProtoD t) = cong T-ProtoD (⋯-id t)
  ⋯-id (T-ProtoP x v t) = cong (T-ProtoP x v) (⋯-id t)

  Ty-Traversal : Traversal
  Ty-Traversal = record
    { _⋯_ = _⋯_
    ; ⋯-var = λ x ϕ → refl
    ; ⋯-id = ⋯-id
    }

  open Traversal Ty-Traversal hiding (_⋯_; ⋯-id)

  fusion :
    ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ KT : Kit _∋/⊢_ ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ KT ⦄
    (t : Ty Δ₁ K) (ϕ₁ : Δ₁ –[ K₁ ]→ Δ₂) (ϕ₂ : Δ₂ –[ K₂ ]→ Δ₃) →
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₖ ϕ₂)
  fusion (T-Var x) ϕ₁ ϕ₂ = sym (&/⋯-⋯ _ ϕ₂)
  fusion T-Base ϕ₁ ϕ₂ = refl
  fusion (T-Arrow x t u) ϕ₁ ϕ₂ = cong₂ (T-Arrow x) (fusion t ϕ₁ ϕ₂) (fusion u ϕ₁ ϕ₂)
  fusion (T-Poly t) ϕ₁ ϕ₂ = cong T-Poly (trans (fusion t (ϕ₁ ↑ _) (ϕ₂ ↑ _)) (cong (t ⋯_) (sym (~-ext (dist-↑-· _ ϕ₁ ϕ₂)))))
  fusion (T-Sub x t) ϕ₁ ϕ₂ = cong (T-Sub x) (fusion t ϕ₁ ϕ₂)
  fusion (T-Dual x t) ϕ₁ ϕ₂ = cong (T-Dual x) (fusion t ϕ₁ ϕ₂)
  fusion T-End ϕ₁ ϕ₂ = refl
  fusion (T-Msg x t u) ϕ₁ ϕ₂ = cong₂ (T-Msg x) (fusion t ϕ₁ ϕ₂) (fusion u ϕ₁ ϕ₂)
  fusion (T-Up t) ϕ₁ ϕ₂ = cong T-Up (fusion t ϕ₁ ϕ₂)
  fusion (T-Minus t) ϕ₁ ϕ₂ = cong T-Minus (fusion t ϕ₁ ϕ₂)
  fusion (T-ProtoD t) ϕ₁ ϕ₂ = cong T-ProtoD (fusion t ϕ₁ ϕ₂)
  fusion (T-ProtoP x v t) ϕ₁ ϕ₂ = cong (T-ProtoP x v) (fusion t ϕ₁ ϕ₂)

  open CTraversal record { fusion = fusion } hiding (fusion)

  t-dual : Dualizable K → Ty Δ K → Ty Δ K
  t-dual D-S (T-Var x) = T-Dual D-S (T-Var x)
  t-dual D-S (T-Arrow ((≤p-step ())) T T₁)
  t-dual D-S (T-Sub K≤K′ T) = T-Sub K≤K′ (t-dual (dualizable-sub D-S K≤K′) T)
  t-dual D-S (T-Dual x T) = T
  t-dual D-S T-End = T-End
  t-dual D-S (T-Msg p T S) = T-Msg (invert p) T (t-dual D-S S)

  tmult : (p : Polarity) → (p ≡ ⊕ ⊎ Dualizable K) → Ty Δ K → Ty Δ K
  tmult ⊕ ok t = t
  tmult ⊝ (inj₂ d) t = t-dual d t


  variable
    T T₁ T₂ T₃ T₄ T′ : Ty Δ K
    Tl Tl₁ Tl₂ : Ty Δ (KV KT Lin)
    S S₁ S₂ S′ : Ty Δ (KV KS Lin)
    P P₁ : Ty Δ KP
    #c #c₁ #c₂ : Subset.Subset k

  data NormalTy {Δ} : Ty Δ (KV pk m) → Set
  data NormalProto {Δ} : Ty Δ KP → Set
  data NormalProto′ {Δ} : Ty Δ KP → Set where
    N-ProtoP : NormalProto T → NormalProto′ (T-ProtoP #c ⊙ T)
    N-Up     : NormalTy T → NormalProto′ (T-Up T)
    N-Var    : {x : KP ∈ Δ} → NormalProto′ (T-Var x)

  data NormalProto {Δ} where
    N-Normal : NormalProto′ T → NormalProto T
    N-Minus  : NormalProto′ T → NormalProto (T-Minus T)

  data NormalVar {Δ} : Ty Δ K → Set where
    NV-Var  : {x : K ∈ Δ} → NormalVar (T-Var x)
    NV-Dual : (d : Dualizable K) → (x : K ∈ Δ) → NormalVar (T-Dual d (T-Var x))

  data NormalTy {Δ} where
    N-Var    : NormalVar T → NormalTy T
    N-Base   : NormalTy T-Base
    N-Arrow  : {km : KM ≤p pk}{m : Multiplicity} → NormalTy T₁ → NormalTy T₂ → NormalTy (T-Arrow {m = m} km T₁ T₂)
    N-Poly   : ∀ {m}{T : Ty (K′ ∷ Δ) (KV KT m)} → NormalTy T → NormalTy (T-Poly T)
    N-Sub    : {km≤ : KV pk m ≤k KV pk′ m′} → NormalTy T → NormalTy (T-Sub km≤ T)
    N-End    : NormalTy T-End
    N-Msg    : ∀ p → NormalProto′ T → NormalTy S → NormalTy (T-Msg p T S)
    N-ProtoD : NormalTy T → NormalTy (T-ProtoD T)

  -- type conversion

  data _≡c_ {Δ} : {K : Kind} → Rel (Ty Δ K) where
    ≡c-refl : T ≡c T
    ≡c-symm : T₁ ≡c T₂ → T₂ ≡c T₁
    ≡c-trns : T₁ ≡c T₂ → T₂ ≡c T₃ → T₁ ≡c T₃
    ≡c-sub  : (K≤K′ : KV pk m ≤k KV pk′ m′) → T₁ ≡c T₂ → T-Sub K≤K′ T₁ ≡c T-Sub K≤K′ T₂

    ≡c-sub-dual : {T : Ty Δ (KV KS m)} {K≤K′ : KV KS m ≤k KV KS m′} → T-Dual D-S (T-Sub K≤K′ T) ≡c T-Sub K≤K′ (T-Dual D-S T)

    ≡c-dual-dual : (d : Dualizable K) → T-Dual d (T-Dual d T) ≡c T
    ≡c-dual-end  : T-Dual D-S T-End ≡c T-End
    ≡c-dual-msg  : T-Dual D-S (T-Msg p T S) ≡c T-Msg (invert p) T (T-Dual D-S S)

    ≡c-msg-minus : T-Msg p (T-Minus T) S ≡c T-Msg (invert p) T S

    ≡c-minus-p   : T-Minus (T-Minus T) ≡c T

  -- congruence rules as needed
    
    ≡c-fun : ∀ {pk : PreKind} {≤pk : KM ≤p pk} {m} →
             T ≡c T₂ → T₁ ≡c T₃ → T-Arrow {m = m} ≤pk T T₁ ≡c T-Arrow ≤pk T₂ T₃
    ≡c-all : ∀ {m} {T₁ T₂ : Ty (K′ ∷ Δ) (KV KT m)} → T₁ ≡c T₂ → T-Poly T₁ ≡c T-Poly T₂
    ≡c-msg : T₁ ≡c T₂ → S₁ ≡c S₂ → T-Msg p T₁ S₁ ≡c T-Msg p T₂ S₂
    ≡c-protoD : T₁ ≡c T₂ → T-ProtoD T₁ ≡c T-ProtoD T₂
    ≡c-protoP : T₁ ≡c T₂ → T-ProtoP #c ⊙ T₁ ≡c T-ProtoP #c ⊙ T₂
    ≡c-up : T₁ ≡c T₂ → T-Up T₁ ≡c T-Up T₂
    ≡c-minus : T₁ ≡c T₂ → T-Minus T₁ ≡c T-Minus T₂

  -- smart constructors

  t-loop : Polarity → Ty Δ KP → Polarity × Ty Δ KP
  t-loop p T@(T-Var x) = p , T
  t-loop p T@(T-Up _)  = p , T
  t-loop p (T-Minus T) = t-loop (invert p) T
  t-loop p T@(T-ProtoP _ _ _) = p , T
  
  t-msg : Polarity → Ty Δ KP → Ty Δ SLin → Ty Δ SLin
  t-msg p T = let p′ , T′ = t-loop p T in T-Msg p′ T′

  t-plus  : Ty Δ KP → Ty Δ KP
  t-minus : Ty Δ KP → Ty Δ KP

  t-plus (T-Var x) = T-Var x
  t-plus (T-Up T) = T-Up T
  t-plus (T-Minus T) = t-minus T
  t-plus (T-ProtoP #c ⊙ T) = T-ProtoP #c ⊙ T

  t-minus T@(T-Var x) = T-Minus T
  t-minus T@(T-Up _) = T-Minus T
  t-minus (T-Minus T) = t-plus T
  t-minus T@(T-ProtoP _ _ _) = T-Minus T

  -- properties of smart constructors

  -- t-plus and t-minus are sound for conversion

  t-plus-≡c : ∀ (T : Ty Δ KP) → t-plus T ≡c T
  t-minus-≡c : ∀ (T : Ty Δ KP) → t-minus T ≡c T-Minus T

  t-plus-≡c (T-Var x) = ≡c-refl
  t-plus-≡c (T-Up T) = ≡c-refl
  t-plus-≡c (T-Minus T) = t-minus-≡c T
  t-plus-≡c (T-ProtoP _ _ T) = ≡c-refl

  t-minus-≡c (T-Var x) = ≡c-refl
  t-minus-≡c (T-Up T) = ≡c-refl
  t-minus-≡c (T-Minus T) = ≡c-trns (t-plus-≡c T) (≡c-symm ≡c-minus-p)
  t-minus-≡c (T-ProtoP _ _ T) = ≡c-refl

  -- t-msg is sound for conversion

  t-msg-≡c : ∀ T → t-msg p T S ≡c T-Msg p T S
  t-msg-≡c (T-Var x) = ≡c-refl
  t-msg-≡c (T-Up T) = ≡c-refl
  t-msg-≡c (T-Minus T) = ≡c-trns (t-msg-≡c T) (≡c-symm ≡c-msg-minus)
  t-msg-≡c (T-ProtoP _ _ T) = ≡c-refl

  -- t-dual is sound for conversion

  dual-tinv : ∀ (T : Ty Δ (KV KS m)) → T-Dual D-S T ≡c t-dual D-S T
  dual-tinv (T-Var x) = ≡c-refl
  dual-tinv (T-Arrow (≤p-step ()) T T₁)
  dual-tinv (T-Sub (≤k-step ≤p-refl x₁) T) = ≡c-trns ≡c-sub-dual (≡c-sub (≤k-step ≤p-refl x₁) (dual-tinv T))
  dual-tinv (T-Dual D-S T) = ≡c-dual-dual D-S
  dual-tinv T-End = ≡c-dual-end
  dual-tinv (T-Msg x T T₁) = ≡c-trns (≡c-dual-msg {p = x} {T = T} {S = T₁}) (≡c-msg (≡c-refl{T = T}) (dual-tinv T₁))

  tinv-dual : ∀ (T : Ty Δ (KV KS m)) → T ≡c t-dual D-S (T-Dual D-S T)
  tinv-dual (T-Var x) = ≡c-refl
  tinv-dual (T-Arrow (≤p-step ()) T T₁)
  tinv-dual (T-Sub x T) = ≡c-refl
  tinv-dual (T-Dual x T) = ≡c-refl
  tinv-dual T-End = ≡c-refl
  tinv-dual (T-Msg x T T₁) = ≡c-refl

  t-loop-plus : (T : Ty Δ KP) → t-loop p (t-plus T) ≡ t-loop p T 
  t-loop-minus : (T : Ty Δ KP) → t-loop p (t-minus T) ≡ t-loop (invert p) T

  t-loop-plus (T-Var x) = refl
  t-loop-plus (T-Up T) = refl
  t-loop-plus (T-Minus T) = t-loop-minus T
  t-loop-plus (T-ProtoP x x₁ T) = refl

  t-loop-minus (T-Var x) = refl
  t-loop-minus (T-Up T) = refl
  t-loop-minus {p = p} (T-Minus T) rewrite invert-involution {p} = t-loop-plus T
  t-loop-minus (T-ProtoP x x₁ T) = refl

  t-msg-plus : (T : Ty Δ KP) → t-msg p (t-plus T) S ≡ t-msg p T S
  t-msg-minus : (T : Ty Δ KP) → t-msg p (t-minus T) S ≡ t-msg (invert p) T S

  t-msg-plus (T-Var x) = refl
  t-msg-plus (T-Up T) = refl
  t-msg-plus (T-Minus T) = t-msg-minus T
  t-msg-plus (T-ProtoP _ _ T) = refl

  t-msg-minus (T-Var x) = refl
  t-msg-minus (T-Up T) = refl
  t-msg-minus {p = p} (T-Minus T) rewrite invert-involution{p} = t-msg-plus T
  t-msg-minus (T-ProtoP _ _ T) = refl

  t-minus-reify : (T : Ty Δ KP) → NormalProto′ T → t-minus T ≡ T-Minus T
  t-minus-reify (T-Var x) N-Var = refl
  t-minus-reify (T-Dual x T) ()
  t-minus-reify (T-Up T) (N-Up nT) = refl
  t-minus-reify (T-Minus T) ()
  t-minus-reify (T-ProtoP _ _ T) (N-ProtoP nT) = refl

  t-minus-normal : (T : Ty Δ KP) → NormalProto T → NormalProto (t-minus T)
  t-minus-normal (T-Var x) (N-Normal N-Var) = N-Minus N-Var
  t-minus-normal (T-Up T) (N-Normal (N-Up x)) =  N-Minus (N-Up x)
  t-minus-normal (T-Minus (T-ProtoP _ _ _)) (N-Minus (N-ProtoP nT)) = N-Normal (N-ProtoP nT)
  t-minus-normal (T-Minus (T-Up _)) (N-Minus (N-Up x)) = N-Normal (N-Up x)
  t-minus-normal (T-Minus (T-Var _)) (N-Minus N-Var) = N-Normal N-Var
  t-minus-normal (T-ProtoP _ _ T) (N-Normal (N-ProtoP x)) =  N-Minus (N-ProtoP x)

  t-minus-involution : (T : Ty Δ KP) → NormalProto T → t-minus (t-minus T) ≡ T
  t-minus-involution (T-Var x) (N-Normal x₁) = refl
  t-minus-involution (T-Up T) (N-Normal x) = refl
  t-minus-involution (T-Minus (T-ProtoP _ _ _)) (N-Minus (N-ProtoP nT)) = refl
  t-minus-involution (T-Minus (T-Up _)) (N-Minus (N-Up x)) = refl
  t-minus-involution (T-Minus (T-Var _)) (N-Minus N-Var) = refl
  t-minus-involution (T-ProtoP _ _ T) (N-Normal x) = refl

  -- normal form

  nf-var : (p : Polarity) → (p ≡ ⊝ → Dualizable K) → K ∈ Δ → Ty Δ K
  nf-var ⊕ d? x = T-Var x
  nf-var ⊝ d? x = T-Dual (d? refl) (T-Var x)

  nf : (p : Polarity) → (p ≡ ⊝ → Dualizable K) → Ty Δ K → Ty Δ K
  nf p d? (T-Var x) = nf-var p d? x
  nf p d? T-Base = T-Base
  nf p d? (T-Arrow x T U) = T-Arrow x (nf ⊕ d?⊥ T) (nf ⊕ d?⊥ U)
  nf p d? (T-Poly T) = T-Poly (nf ⊕ d?⊥ T)
  -- nf p d? (T-Sub (≤k-step ≤p-refl ≤m-refl) T) = nf p d? T
  nf p d? (T-Sub x T) = T-Sub x (nf p (λ x₁ → dualizable-sub (d? x₁) x) T)
  nf p d? (T-Dual dK T) = nf (invert p) (λ x₁ → dK) T
  nf p d? T-End = T-End
  nf p d? (T-Msg q T S) = t-msg (mult p q) (nf ⊕ d?⊥ T) (nf p d? S)
  nf p d? (T-Up T) = T-Up (nf ⊕ d?⊥ T)
  nf p d? (T-Minus T) = t-minus (nf ⊕ d?⊥ T)
  nf p d? (T-ProtoD T) = T-ProtoD (nf ⊕ d?⊥ T)
  nf p d? (T-ProtoP #c ⊙ T) = T-ProtoP #c ⊙ (nf ⊕ d?⊥ T)

  -- the nf algorithm returns a normal form

  -- t-msg returns a normal form
  nf-t-msg-loop : (p : Polarity) → {T : Ty Δ KP} → (nT : NormalProto T) → let p′ , T′ = t-loop p T in Polarity × NormalProto′ T′
  nf-t-msg-loop p (N-Normal (N-ProtoP x)) = p , N-ProtoP x
  nf-t-msg-loop p (N-Normal (N-Up x)) = p , N-Up x
  nf-t-msg-loop p (N-Normal N-Var) = p , N-Var
  nf-t-msg-loop p (N-Minus (N-ProtoP x)) = invert p , N-ProtoP x
  nf-t-msg-loop p (N-Minus (N-Up x)) = invert p , N-Up x
  nf-t-msg-loop p (N-Minus N-Var) = invert p , N-Var
  
  nf-t-msg : (p : Polarity) → {T : Ty Δ KP} → (nT : NormalProto T) → {S : Ty Δ SLin} → (nS : NormalTy S) → NormalTy (t-msg p T S)
  nf-t-msg p {T} NP NS =
    let p′ , T′ = t-loop p T in
    let p″ , N″ = nf-t-msg-loop p NP in
    -- it holds that p′ ≡ p″ (unproved)
    N-Msg p′ N″ NS

  nf-normal-proto : (T : Ty Δ KP) → NormalProto (nf ⊕ d?⊥ T)

  nf-normal-proto-inverted : (T : Ty Δ KP) → NormalProto (t-minus (nf ⊕ d?⊥ T))

  nf-normal-type-var : ∀ (⊙ : Polarity) → (d? : ⊙ ≡ ⊝ → Dualizable K)  (x : K ∈ Δ) → NormalVar (nf ⊙ d? (T-Var x))
  nf-normal-type-var ⊕ d? x = NV-Var
  nf-normal-type-var ⊝ d? x = NV-Dual (d? refl) x

  nf-normal-type : ∀ ⊙ → (d? : ⊙ ≡ ⊝ → Dualizable (KV pk m)) (T : Ty Δ (KV pk m)) → NormalTy (nf ⊙ d? T)
  nf-normal-type ⊙ d? (T-Var x) = N-Var (nf-normal-type-var ⊙ d? x)
  nf-normal-type ⊙ d? T-Base = N-Base
  nf-normal-type ⊙ d? (T-Arrow x T T₁) =  N-Arrow (nf-normal-type ⊕ d?⊥ T) (nf-normal-type ⊕ d?⊥ T₁)
  nf-normal-type ⊙ d? (T-Poly T) = N-Poly (nf-normal-type ⊕ d?⊥ T)
  nf-normal-type ⊙ d? (T-Sub x T) = N-Sub (nf-normal-type ⊙ (λ x₁ → dualizable-sub (d? x₁) x) T)
  nf-normal-type ⊙ d? (T-Dual x T) = nf-normal-type (invert ⊙) (const x) T
  nf-normal-type ⊙ d? T-End = N-End
  nf-normal-type ⊙ d? (T-Msg p T T₁) = nf-t-msg (mult ⊙ p) (nf-normal-proto T) (nf-normal-type ⊙ d? T₁)
  nf-normal-type ⊙ d? (T-ProtoD T) = N-ProtoD (nf-normal-type ⊕ d?⊥ T)

  nf-normal-proto (T-Var x) = N-Normal N-Var
  nf-normal-proto (T-Up T) = N-Normal (N-Up (nf-normal-type ⊕ d?⊥ T))
  nf-normal-proto (T-Minus T) with inspect (nf ⊕ d?⊥) T | nf-normal-proto T
  ... | Eq.[ eq ] | nf-t-normal = t-minus-normal ((nf ⊕ d?⊥) T) nf-t-normal
  nf-normal-proto (T-ProtoP #c ⊙ T) = N-Normal (N-ProtoP (nf-normal-proto T))

  nf-normal-proto-inverted (T-Var x) = N-Minus N-Var
  nf-normal-proto-inverted (T-Up T) = N-Minus (N-Up (nf-normal-type ⊕ d?⊥ T))
  nf-normal-proto-inverted (T-Minus T)
    rewrite t-minus-involution (nf ⊕ d?⊥ T) (nf-normal-proto T) = nf-normal-proto T  
  nf-normal-proto-inverted (T-ProtoP #c ⊙ T) = N-Minus (N-ProtoP (nf-normal-proto T))

  nf-tmsg-invert-minus  : ∀ (⊙ : Polarity) (d? : ⊙ ≡ ⊝ → Dualizable (KV KS Lin)) → (T : Ty Δ KP)
    → t-msg (invert ⊙) (nf ⊕ d?⊥ T) S ≡ t-msg ⊙ (t-minus (nf ⊕ d?⊥ T)) S
  nf-tmsg-invert-minus ⊙ d? (T-Var x) = refl
  nf-tmsg-invert-minus ⊙ d? (T-Up T) = refl
  nf-tmsg-invert-minus ⊙ d? (T-Minus T) = sym (t-msg-minus (t-minus (nf ⊕ d?⊥ T)))
  nf-tmsg-invert-minus ⊙ d? (T-ProtoP x x₁ T) = refl

  nf-invert-minus : ∀ (⊙ : Polarity) (d? : ⊙ ≡ ⊝ → Dualizable (KV KS Lin)) → ∀ T → nf ⊙ d? (T-Msg (invert p) T S) ≡ nf ⊙ d? (T-Msg p (T-Minus T) S)
  nf-invert-minus {p} ⊙ d? T
    rewrite sym (invert-mult-⊙ p {⊙}) = nf-tmsg-invert-minus (mult ⊙ p) d?S T

  -- nf ⊕ ignores dualizability

  nf-⊕-ignores : ∀ f g → nf ⊕ f T ≡ nf ⊕ g T
  nf-⊕-ignores {T = T-Var x} f g = refl
  nf-⊕-ignores {T = T-Base} f g = refl
  nf-⊕-ignores {T = T-Arrow x T T₁} f g = refl
  nf-⊕-ignores {T = T-Poly T} f g = refl
  nf-⊕-ignores {T = T-Sub x T} f g = cong (T-Sub x) (nf-⊕-ignores {T = T} (λ x₁ → dualizable-sub (f x₁) x) (λ x₁ → dualizable-sub (g x₁) x))
  nf-⊕-ignores {T = T-Dual x T} f g = refl
  nf-⊕-ignores {T = T-End} f g = refl
  nf-⊕-ignores {T = T-Msg x T T₁} f g = cong (t-msg (mult ⊕ x) (nf ⊕ d?⊥ T)) (nf-⊕-ignores {T = T₁} f g)
  nf-⊕-ignores {T = T-Up T} f g = refl
  nf-⊕-ignores {T = T-Minus T} f g = refl
  nf-⊕-ignores {T = T-ProtoD T} f g = refl
  nf-⊕-ignores {T = T-ProtoP _ _ T} f g = refl

  -- completeness

  nf-complete : ∀ f g → T₁ ≡c T₂ → nf ⊕ f T₁ ≡ nf ⊕ g T₂
  nf-complete {T₁ = T₁} f g ≡c-refl = nf-⊕-ignores {T = T₁} f g
  nf-complete f g (≡c-symm T1=T2) = sym (nf-complete g f T1=T2)
  nf-complete f g (≡c-trns T1=T2 T1=T3) = trans (nf-complete f d?⊥ T1=T2) (nf-complete d?⊥ g T1=T3)
  nf-complete f g (≡c-sub K≤K′ T1=T2) = cong (T-Sub K≤K′) (nf-complete (λ x₁ → dualizable-sub (f x₁) K≤K′) (λ x₁ → dualizable-sub (g x₁) K≤K′) T1=T2)
  nf-complete {T₂ = T₂} f g (≡c-dual-dual d) = nf-⊕-ignores {T = T₂} (λ x₁ → d) g
  nf-complete f g ≡c-dual-end = refl
  nf-complete f g (≡c-dual-msg {p = p}) rewrite mult-invert{p = p} = refl
  nf-complete f g (≡c-msg-minus {p = p} {T = T} {S = S}) rewrite nf-⊕-ignores{T = S} f g = t-msg-minus {p = p} (nf ⊕ d?⊥ T)
  nf-complete {T₂ = T₂} f g ≡c-minus-p rewrite nf-⊕-ignores {T = T₂} g d?⊥ = t-minus-involution (nf ⊕ d?⊥ T₂) (nf-normal-proto T₂)
  nf-complete f g (≡c-fun {≤pk = ≤pk} T1=T2 T1=T3) = cong₂ (T-Arrow ≤pk) (nf-complete d?⊥ d?⊥ T1=T2) (nf-complete d?⊥ d?⊥ T1=T3)
  nf-complete f g (≡c-all T1=T2) = cong T-Poly (nf-complete d?⊥ d?⊥ T1=T2)
  nf-complete f g (≡c-msg {p = p} T1=T2 T1=T3) = cong₂ (t-msg (mult ⊕ p)) (nf-complete d?⊥ d?⊥ T1=T2) (nf-complete f g T1=T3)
  nf-complete f g (≡c-protoD T1=T2) = cong T-ProtoD (nf-complete d?⊥ d?⊥ T1=T2)
  nf-complete f g (≡c-protoP T1=T2) = cong (T-ProtoP _ _) (nf-complete d?⊥ d?⊥ T1=T2)
  nf-complete f g (≡c-sub-dual {K≤K′ = ≤k-step ≤p-refl x₁}) = refl
  nf-complete f g (≡c-up T1=T2) = cong T-Up (nf-complete d?⊥ d?⊥ T1=T2)
  nf-complete f g (≡c-minus T1=T2) = cong t-minus (nf-complete _ _ T1=T2)

  nf-complete- : ∀ f → T₁ ≡c T₂ → nf ⊝ f T₁ ≡ nf ⊝ f T₂
  nf-complete- f ≡c-refl = refl
  nf-complete- f (≡c-symm t1≡t2) = sym (nf-complete- f t1≡t2)
  nf-complete- f (≡c-trns t1≡t2 t1≡t3) = trans (nf-complete- f t1≡t2) (nf-complete- f t1≡t3)
  nf-complete- f (≡c-sub K≤K′ t1≡t2) rewrite nf-complete- (λ x → dualizable-sub (f x) K≤K′) t1≡t2 = refl
  nf-complete- f (≡c-sub-dual {K≤K′ = ≤k-step ≤p-refl _}) = refl
  nf-complete- f (≡c-dual-dual d) rewrite dual-irrelevant f (λ x → d) = refl
  nf-complete- f ≡c-dual-end = refl
  nf-complete- f (≡c-dual-msg {p = p}) rewrite invert-involution {p} = refl
  nf-complete- f (≡c-msg-minus {p = p}{T = T}{S = S}) = subst (λ x → x ≡ t-msg (mult ⊝ (invert p)) (nf ⊕ d?⊥ T) (nf ⊝ f S)) (sym (t-msg-minus {p = (mult ⊝ p)}{nf ⊝ f S} (nf ⊕ d?⊥ T))) (cong (λ q → t-msg q (nf ⊕ d?⊥ T) (nf ⊝ f S)) (invert-mult-⊙ p))
  nf-complete- f ≡c-minus-p with () ← f refl
  nf-complete- f (≡c-fun {≤pk = ≤p-refl} t1≡t2 t1≡t3) with () ← f refl
  nf-complete- f (≡c-fun {≤pk = ≤p-step <p-mt} t1≡t2 t1≡t3) with () ← f refl
  nf-complete- f (≡c-all t1≡t2) with () ← f refl
  nf-complete- f (≡c-msg {S₂ = S₂} {p = p} t1≡t2 t1≡t3) rewrite nf-complete- f t1≡t3 = cong (λ nft → t-msg (mult ⊝ p) nft (nf ⊝ f S₂)) ( nf-complete d?⊥ d?⊥ t1≡t2)
  nf-complete- f (≡c-protoD t1≡t2) with () ← f refl
  nf-complete- f (≡c-protoP t1≡t2) with () ← f refl
  nf-complete- f (≡c-up t1≡t2) with () ← f refl
  nf-complete- f (≡c-minus t1≡t2) with () ← f refl

  -- soundness

  nf-sound+ : ∀ {f} → (T : Ty Δ K)         → nf ⊕ f T ≡c T
  nf-sound- : ∀ {f} → (T : Ty Δ (KV KS m)) → nf ⊝ f T ≡c t-dual D-S T

  nf-sound+ (T-Var x) = ≡c-refl
  nf-sound+ T-Base = ≡c-refl
  nf-sound+ (T-Arrow x T T₁) = ≡c-fun (nf-sound+ T) (nf-sound+ T₁)
  nf-sound+ (T-Poly T) = ≡c-all (nf-sound+ T)
  nf-sound+ (T-Sub x T) = ≡c-sub x (nf-sound+ T)
  nf-sound+ (T-Dual D-S T) = ≡c-trns (nf-sound- T) (≡c-symm (dual-tinv T))
  nf-sound+ T-End = ≡c-refl
  nf-sound+ (T-Msg ⊕ T S) = ≡c-trns (t-msg-≡c (nf ⊕ d?⊥ T)) (≡c-msg (nf-sound+ T) (nf-sound+ S))
  nf-sound+ (T-Msg ⊝ T S) = ≡c-trns (t-msg-≡c (nf ⊕ d?⊥ T)) (≡c-msg (nf-sound+ T) (nf-sound+ S))
  nf-sound+ (T-Up T) = ≡c-up (nf-sound+ T)
  nf-sound+ (T-Minus T) = ≡c-trns (t-minus-≡c (nf ⊕ d?⊥ T)) (≡c-minus (nf-sound+ T))
  nf-sound+ (T-ProtoD T) = ≡c-protoD (nf-sound+ T)
  nf-sound+ (T-ProtoP _ _ T) = ≡c-protoP (nf-sound+ T)

  nf-sound- {f = f} (T-Var x) rewrite ext-dual-s-irrelevant f (λ x → D-S) = ≡c-refl
  nf-sound- (T-Arrow (≤p-step ()) T T₁)
  nf-sound- (T-Sub (≤k-step ≤p-refl x₁) T) = ≡c-sub (≤k-step ≤p-refl x₁) (nf-sound- T)
  nf-sound- (T-Dual D-S T) = nf-sound+ T
  nf-sound- T-End = ≡c-refl
  nf-sound- (T-Msg ⊕ T S) = ≡c-trns (t-msg-≡c (nf ⊕ d?⊥ T)) (≡c-msg (nf-sound+ T) (nf-sound- S))
  nf-sound- (T-Msg ⊝ T S) = ≡c-trns (t-msg-≡c (nf ⊕ d?⊥ T)) (≡c-msg (nf-sound+ T) (nf-sound- S))

  -- normal types are determined by their type index

  nv-unique : ∀ {T : Ty Δ (KV pk m)} (NV₁ NV₂ : NormalVar T) → NV₁ ≡ NV₂
  nv-unique NV-Var NV-Var = refl
  nv-unique (NV-Dual d x) (NV-Dual d₁ x₁) = refl

  nt-unique : ∀ {T : Ty Δ (KV pk m)}(N₁ N₂ : NormalTy T) → N₁ ≡ N₂
  np′-unique : ∀ {P : Ty Δ KP} (NP₁ NP₂ : NormalProto′ P) → NP₁ ≡ NP₂
  np-unique : ∀ {P : Ty Δ KP} (NP₁ NP₂ : NormalProto P) → NP₁ ≡ NP₂

  np-unique (N-Normal NP₁) (N-Normal NP₂) = cong N-Normal (np′-unique NP₁ NP₂)
  np-unique (N-Minus NP₁) (N-Minus NP₂) = cong N-Minus (np′-unique NP₁ NP₂)

  np′-unique (N-ProtoP NP₁) (N-ProtoP NP₂) = cong N-ProtoP (np-unique NP₁ NP₂)
  np′-unique (N-Up N₁) (N-Up N₂) = cong N-Up (nt-unique N₁ N₂)
  np′-unique N-Var N-Var = refl

  nt-unique (N-Var NV₁) (N-Var NV₂) = cong N-Var (nv-unique NV₁ NV₂)
  nt-unique N-Base N-Base = refl
  nt-unique (N-Arrow N₁ N₃) (N-Arrow N₂ N₄) = cong₂ N-Arrow (nt-unique N₁ N₂) (nt-unique N₃ N₄)
  nt-unique (N-Poly N₁) (N-Poly N₂) = cong N-Poly (nt-unique N₁ N₂)
  nt-unique (N-Sub N₁) (N-Sub N₂) = cong N-Sub (nt-unique N₁ N₂)
  nt-unique N-End N-End = refl
  nt-unique (N-Msg {T = T} p NP₁ N₁) (N-Msg p₁ NP₂ N₂) = cong₂ (N-Msg p) (np′-unique {P = T} NP₁ NP₂) (nt-unique N₁ N₂)
  nt-unique (N-ProtoD N₁) (N-ProtoD N₂) = cong N-ProtoD (nt-unique N₁ N₂)


  t-loop-nf-ident : ∀ {p} (T : Ty Δ KP) → NormalProto T
    → t-loop p T ≡ (p , T) ⊎ t-loop p T ≡ (invert p , t-minus T)
  t-loop-nf-ident (T-Var x₁) (N-Normal N′) = inj₁ refl
  t-loop-nf-ident (T-Up T) (N-Normal N′) = inj₁ refl
  t-loop-nf-ident (T-ProtoP #c ⊙ T) (N-Normal N′) = inj₁ refl
  t-loop-nf-ident (T-Minus (T-ProtoP #c ⊙ T)) (N-Minus (N-ProtoP x)) = inj₂ refl
  t-loop-nf-ident (T-Minus T) (N-Minus (N-Up x)) = inj₂ refl
  t-loop-nf-ident (T-Minus T) (N-Minus N-Var) = inj₂ refl

  t-loop-nf-ident′ : ∀ {p} (T : Ty Δ KP) → NormalProto′ T → t-loop p T ≡ (p , T)
  t-loop-nf-ident′ T (N-ProtoP x) = refl
  t-loop-nf-ident′ T (N-Up x) = refl
  t-loop-nf-ident′ T N-Var = refl

  -- normal form is idempotent

  nf-idempotent : NormalTy T → nf ⊕ d?⊥ T ≡ T
  nfp-idempotent : NormalProto T → nf ⊕ d?⊥ T ≡ T
  nfp′-idempotent : NormalProto′ T → nf ⊕ d?⊥ T ≡ T


  nf-idempotent {T = T-Var x₁} (N-Var x) = refl
  nf-idempotent {T = T-Dual x₁ (T-Var x₂)} (N-Var x) = refl
  nf-idempotent N-Base = refl
  nf-idempotent (N-Arrow N₁ N₂) = cong₂ (T-Arrow _) (nf-idempotent N₁) (nf-idempotent N₂)
  nf-idempotent (N-Poly N) = cong T-Poly (nf-idempotent N)
  nf-idempotent {T = T-Sub km≤ T} (N-Sub N) = cong (T-Sub _) (trans (cong (λ d? → nf ⊕ d? T) (dual-all-irrelevant (λ x₁ → dualizable-sub (d?⊥ x₁) km≤) d?⊥)) (nf-idempotent N))
  nf-idempotent N-End = refl
  nf-idempotent (N-Msg p (N-ProtoP NT) NS) = cong₂ (T-Msg p) (cong (T-ProtoP _ _) (nfp-idempotent NT)) (nf-idempotent NS)
  nf-idempotent (N-Msg p (N-Up NT) NS) = cong₂ (T-Msg p) (cong T-Up (nf-idempotent NT)) (nf-idempotent NS)
  nf-idempotent (N-Msg p N-Var NS) = cong₂ (T-Msg p) refl (nf-idempotent NS)
  nf-idempotent (N-ProtoD N) = cong T-ProtoD (nf-idempotent N)

  nfp-idempotent (N-Normal NP) = nfp′-idempotent NP
  nfp-idempotent (N-Minus (N-ProtoP NP)) = cong T-Minus (cong (T-ProtoP _ _) (nfp-idempotent NP))
  nfp-idempotent (N-Minus (N-Up NT)) = cong T-Minus (cong T-Up (nf-idempotent NT))
  nfp-idempotent (N-Minus N-Var) = cong T-Minus refl

  nfp′-idempotent (N-ProtoP NP) = cong (T-ProtoP _ _) (nfp-idempotent NP)
  nfp′-idempotent (N-Up NT) = cong T-Up (nf-idempotent NT)
  nfp′-idempotent N-Var = refl
