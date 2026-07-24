module ExprNormalTyping where

open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Subset as Subset
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec using (Vec; []; _∷_; here; there)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no; Dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; head; tail; _∷_; foldr₁; map)


open import Kinds
open import Kits
open import Duality
open import Types hiding
  ( NormalTy
  ; NormalProto
  ; NormalProto′
  ; NormalVar
  ; N-Var
  ; N-Base
  ; N-Arrow
  ; N-Pair
  ; N-Poly
  ; N-Sub
  ; N-End
  ; N-Msg
  ; N-ProtoD
  ; N-ProtoP
  ; N-Up
  ; N-Normal
  ; N-Minus
  ; NV-Var
  ; NV-Dual
  ; nt-unique
  ; nt-unique-eq
  ; np-unique
  ; np-unique-eq
  ; np′-unique
  ; nf-normal-proto
  ; nf-normal-type
  )
open import TypesProperties using (renaming-injective; weakenᵣ-injective)
open import TypesProtocolConstructors using (ConstructorSignature; ProtocolConstructors; instantiate)
open import NormalTypes using
  ( NFProto
  ; NFProto′
  ; NFVar
  ; NFTy
  ; nfProtoTy
  ; nfTyTy
  ; nfProtoTy-injective
  ; nfTyTy-injective
  ; nfProtoTy-fromNormalProto
  ; nfTyTy-fromNormalTy
  ; nf-normal-proto
  ; nf-normal-type
  ; toNormalProto
  ; toNormalTy
  ; N-Var
  ; N-Base
  ; N-Arrow
  ; N-Pair
  ; N-Poly
  ; N-Sub
  ; N-End
  ; N-Msg
  ; N-ProtoD
  ; N-ProtoP
  ; N-Up
  ; N-Normal
  ; N-Minus
  ; NV-Var
  ; NV-Dual
  )
open import NormalTypesRenamings using (renNFProto′; renNFProto; renNFTy)
open import NormalTypesSubstitution using
  ( NFKind
  ; nfKindTy
  ; wkNFKind
  ; wkNFKind-sound
  ; substNFTy
  ; msgNF
  )
open import ExprSyntax
open import AlgorithmicNFSubtyping
open import AlgorithmicNFMerge

open Kits.Syntax Ty-Syntax hiding (Sort)
open Traversal Ty-Traversal hiding (_⋯_; ⋯-id)

⌞_⌟ : NfTy Δ K → Ty Δ K
⌞_⌟ = nfKindTy

normalProtoOf : (N : NfTy Δ KP) → NFProto Δ
normalProtoOf N = N

normalizeTy : ∀ {K} → Ty Δ K → NfTy Δ K
normalizeTy {K = KV pk m} T = nf-normal-type ⊕ d?⊥ T
normalizeTy {K = KP} T = nf-normal-proto T

data Binding (Δ : List Kind) : Set where
  B-Lin  : ∀ {pk} → NfTy Δ (KV pk Lin) → Binding Δ
  B-Un   : ∀ {pk} → NfTy Δ (KV pk Un) → Binding Δ
  B-Used : ∀ {pk} → NfTy Δ (KV pk Lin) → Binding Δ

infixr 5 _▻_

data Ctx (Δ : List Kind) : ℕ → Set where
  ∅   : Ctx Δ 0
  _▻_ : ∀ {n} → Binding Δ → Ctx Δ n → Ctx Δ (suc n)

_∷ˡ_ : ∀ {n pk} → NfTy Δ (KV pk Lin) → Ctx Δ n → Ctx Δ (suc n)
T ∷ˡ Γ = B-Lin T ▻ Γ

_∷ᵘ_ : ∀ {n pk} → NfTy Δ (KV pk Un) → Ctx Δ n → Ctx Δ (suc n)
T ∷ᵘ Γ = B-Un T ▻ Γ

_∷ⁿˡ_ : ∀ {n pk} → Ty Δ (KV pk Lin) → Ctx Δ n → Ctx Δ (suc n)
T ∷ⁿˡ Γ = normalizeTy T ∷ˡ Γ

_∷ⁿᵘ_ : ∀ {n pk} → Ty Δ (KV pk Un) → Ctx Δ n → Ctx Δ (suc n)
T ∷ⁿᵘ Γ = normalizeTy T ∷ᵘ Γ

pattern used∷ {T = T} Γ = B-Used T ▻ Γ

wkNfTy : ∀ {K K′} → NfTy Δ K → NfTy (K′ ∷ Δ) K
wkNfTy = wkNFKind

wkBinding : ∀ {K} → Binding Δ → Binding (K ∷ Δ)
wkBinding {K = K} (B-Lin T) = B-Lin (wkNfTy {K′ = K} T)
wkBinding {K = K} (B-Un T) = B-Un (wkNfTy {K′ = K} T)
wkBinding {K = K} (B-Used T) = B-Used (wkNfTy {K′ = K} T)

wkCtx : ∀ {n K} → Ctx Δ n → Ctx (K ∷ Δ) n
wkCtx ∅ = ∅
wkCtx (b ▻ Γ) = wkBinding b ▻ wkCtx Γ

LinArr : Ty Δ TLin → Ty Δ TLin → Ty Δ TLin
LinArr = T-Arrow {m = Lin}

linArrNf : NfTy Δ (KV pk₁ m₁) → NfTy Δ (KV pk₂ m₂) → NfTy Δ (KV KT Lin)
linArrNf = N-Arrow

unArrNf : NfTy Δ (KV pk₁ m₁) → NfTy Δ (KV pk₂ m₂) → NfTy Δ (KV KT Un)
unArrNf = N-Arrow

pairNf : ∀ {pk₁ pk₂ m}
  → NfTy Δ (KV pk₁ m)
  → NfTy Δ (KV pk₂ m)
  → NfTy Δ (KV KT m)
pairNf = N-Pair

polyNf : NfTy (K ∷ Δ) (KV KT m) → NfTy Δ (KV KT m)
polyNf {K = K} = N-Poly K

UnitLin : Ty Δ TLin
UnitLin = T-Base

SessLin : Ty Δ SLin → Ty Δ TLin
SessLin = T-Sub (≤k-step (≤p-step <p-st) ≤m-refl)

EndLin : Ty Δ SLin
EndLin = T-Sub (≤k-step ≤p-refl ≤m-unl) T-End

CloseTy : Ty Δ TLin
CloseTy = T-Arrow {m = Lin} EndLin UnitLin

ForkTy : Ty Δ TLin
ForkTy = LinArr (LinArr UnitLin UnitLin) UnitLin

NewTy : Ty Δ TLin
NewTy = T-Poly SLin
  (T-Pair (T-Var (here refl))
          (T-Dual D-S (T-Var (here refl))))

wkTy : ∀ {K K′} → Ty Δ K → Ty (K′ ∷ Δ) K
wkTy {K′ = K′} T = T ⋯ weakenᵣ K′

ReceiveTy : Ty Δ (KV pk Lin) → Ty Δ SLin → Ty Δ TLin
ReceiveTy T S = T-Arrow {m = Lin}
  (T-Msg ⊝ (T-Up T) S)
  (T-Pair T S)

ReceiveTy1 : Ty Δ (KV pk Lin) → Ty Δ TLin
ReceiveTy1 T = T-Poly SLin
  (ReceiveTy (wkTy {K′ = SLin} T) (T-Var (here refl)))

SendTy : Ty Δ (KV pk Lin) → Ty Δ SLin → Ty Δ TLin
SendTy T S = T-Arrow {m = Lin}
  (T-Pair T (T-Msg ⊕ (T-Up T) S))
  S

SendTy1 : Ty Δ (KV pk Lin) → Ty Δ TLin
SendTy1 T = T-Poly SLin
  (SendTy (wkTy {K′ = SLin} T) (T-Var (here refl)))

unitConstNf : NfTy Δ TLin
unitConstNf = N-Base

sessTyNf : NfTy Δ SLin → NfTy Δ TLin
sessTyNf = N-Sub (≤k-step (≤p-step <p-st) ≤m-refl)

endConstNf : NfTy Δ SLin
endConstNf = N-Sub (≤k-step ≤p-refl ≤m-unl) N-End

closeConstNf : NfTy Δ TLin
closeConstNf = linArrNf endConstNf unitConstNf

forkConstNf : NfTy Δ TLin
forkConstNf = linArrNf (linArrNf unitConstNf unitConstNf) unitConstNf

newConstNf : NfTy Δ TLin
newConstNf =
  polyNf
    (pairNf
      (N-Var (NV-Var (here refl)))
      (N-Var (NV-Dual D-S (here refl))))

receiveNf : NfTy Δ (KV pk Lin) → NfTy Δ SLin → NfTy Δ TLin
receiveNf T S =
  linArrNf
    (msgNF ⊝ (N-Normal (N-Up T)) S)
    (pairNf T S)

receive1Nf : NfTy Δ (KV pk Lin) → NfTy Δ TLin
receive1Nf {Δ = Δ} T =
  polyNf {K = SLin}
    (receiveNf (wkNfTy {K′ = SLin} T) (N-Var (NV-Var (here refl))))

receiveConstNf : NfTy Δ TLin
receiveConstNf =
  polyNf {K = TLin} (receive1Nf (N-Var (NV-Var (here refl))))

sendResultNf : NfTy Δ (KV pk Lin) → NfTy Δ SLin → NfTy Δ SLin
sendResultNf T S = S

sendNf : NfTy Δ (KV pk Lin) → NfTy Δ SLin → NfTy Δ TLin
sendNf T S =
  linArrNf
    (pairNf T (msgNF ⊕ (N-Normal (N-Up T)) S))
    S

send1Nf : NfTy Δ (KV pk Lin) → NfTy Δ TLin
send1Nf {Δ = Δ} T =
  polyNf {K = SLin}
    (sendNf (wkNfTy {K′ = SLin} T) (N-Var (NV-Var (here refl))))

sendConstNf : NfTy Δ TLin
sendConstNf =
  polyNf {K = TLin} (send1Nf (N-Var (NV-Var (here refl))))

materializeListNf : List (Ty (KP ∷ []) KP) → Polarity → NfTy Δ KP → NfTy Δ SLin → NfTy Δ SLin
materializeListNf [] p P S = S
materializeListNf (T ∷ Ts) p P S =
  msgNF p (normalizeTy (instantiate ⦃ Kₛ ⦄ p T ⌞ P ⌟)) (materializeListNf Ts p P S)

materializeNf : ∀ {v} → ConstructorSignature v → Polarity → NfTy Δ KP → NfTy Δ SLin → NfTy Δ SLin
materializeNf (Ts , _) p P S = materializeListNf Ts p P S

materialize-atNf : ∀ {c v} → (Fin c → ConstructorSignature v) → Fin c → Polarity → NfTy Δ KP → NfTy Δ SLin → NfTy Δ SLin
materialize-atNf cs i p P S = materializeNf (cs i) p P S

selectSetInTyNf :
  ∀ {c}
  → Subset.Subset c
  → Variance
  → NfTy Δ KP
  → NfTy Δ SLin
  → NfTy Δ SLin
selectSetInTyNf ss v P S =
  msgNF ⊕ (N-Normal (N-ProtoP ss v P)) S

selectInTyNf : ∀ {c} → Variance → Fin c → NfTy Δ KP → NfTy Δ SLin → NfTy Δ SLin
selectInTyNf v i P S =
  selectSetInTyNf (Subset.⁅ i ⁆) v P S

selectOutTyNf : ∀ {c} → Variance → Fin c → NfTy Δ KP → NfTy Δ SLin → NfTy Δ SLin
selectOutTyNf {c} v i P S =
  materialize-atNf (ProtocolConstructors _ v) i ⊕ P S

selectNf : ∀ {c} → Variance → Fin c → NfTy Δ KP → NfTy Δ SLin → NfTy Δ TLin
selectNf v i P S = linArrNf (selectInTyNf v i P S) (selectOutTyNf v i P S)

select1Nf : ∀ {c} → Variance → Fin c → NfTy Δ KP → NfTy Δ TLin
select1Nf {c} v i P =
  polyNf {K = SLin}
    (selectNf v i (wkNfTy {K′ = SLin} P) (N-Var (NV-Var (here refl))))

selectConstNf : ∀ {c} → Variance → Fin c → NfTy Δ TLin
selectConstNf {c} v i =
  polyNf {K = KP} (select1Nf v i (N-Normal (N-Var (here refl))))


MatchBranchInput : ∀ {k} → Subset.Subset k → Variance → NfTy Δ KP → NfTy Δ SLin → NfTy Δ SLin
MatchBranchInput ss v P S = N-Msg ⊝ (N-ProtoP ss v P) S

MatchBranchOutput : ∀ {k} → (ss : Subset.Subset (suc k)) → Variance → NfTy Δ KP → NfTy Δ SLin → ((i : Fin (suc k)) → i Subset.∈ ss → NfTy Δ SLin)
MatchBranchOutput {k = k} ss v P S i x = materialize-atNf (ProtocolConstructors (suc k) v) i ⊝ P S


BranchJoin⁺ : ∀ {k pk m} (ss : Subset.Subset k)
    → (V : ∀ i → i Subset.∈ ss → NfTy Δ (KV pk m))
    → Maybe (Σ (NfTy Δ (KV pk m)) λ N → ∀ i → (i∈ : i Subset.∈ ss) → V i i∈ <:ₜ N)
BranchJoin⁺ {Δ} {k} [] V = nothing
BranchJoin⁺ {Δ} {k} (Subset.outside ∷ ss) V
  with BranchJoin⁺ ss (λ i i∈ → V (suc i) (there i∈))
... | nothing = nothing
... | just (N , sub) = just (N , (λ{ (suc i) (there i∈) → sub i i∈}))
BranchJoin⁺ {Δ} {k} (Subset.inside ∷ ss) V
  with BranchJoin⁺ ss (λ i i∈ → V (suc i) (there i∈))
... | nothing = nothing
... | just (N , sub)
  with joinₜ (V zero here) N
... | no ¬joinable = nothing
... | yes (N′ , V₀<:N′ , N<:N′) = just (N′ , (λ{ zero here → V₀<:N′ ; (suc i) (there i∈) → <:ₜ-trans (sub i i∈) N<:N′}))

data ConstTy {Δ} : Const → ∀ {K} → NfTy Δ K → Set where
  CT-Unit : ConstTy C-Unit unitConstNf
  CT-Fork : ConstTy C-Fork forkConstNf
  CT-New  : ConstTy C-New newConstNf
  CT-Receive : ConstTy C-Receive receiveConstNf
  CT-Send : ConstTy C-Send sendConstNf
  CT-Close : ConstTy C-Close closeConstNf
  CT-Select : ∀ {k} {v : Variance} {i : Fin k}
    → ConstTy (C-Select v i) (selectConstNf v i)

infix 4 _∋ˡ_∶_ _∋ᵘ_∶_ _⊢ˡ_∶_⊣_ _⊢ᵥ_⇒_⊣_ _⊢_⇒_⊣_ _⊢_⇐_⊣_

data _∋ˡ_∶_ {Δ} : ∀ {n} → Ctx Δ n → Fin n → ∀ {pk} → NfTy Δ (KV pk Lin) → Set where
  hereˡ : ∀ {n} {Γ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Lin)}
    → (T ∷ˡ Γ) ∋ˡ zero ∶ T
  thereˡˡ : ∀ {Γ pk pk′} {x : Fin n} {T : NfTy Δ (KV pk Lin)} {U : NfTy Δ (KV pk′ Lin)}
    → Γ ∋ˡ x ∶ T
    → (U ∷ˡ Γ) ∋ˡ suc x ∶ T
  thereˡᵘ : ∀ {Γ pk pk′} {x : Fin n} {T : NfTy Δ (KV pk Lin)} {U : NfTy Δ (KV pk′ Un)}
    → Γ ∋ˡ x ∶ T
    → (U ∷ᵘ Γ) ∋ˡ suc x ∶ T
  thereˡ✖ : ∀ {Γ pk pk′} {x : Fin n}
      {T : NfTy Δ (KV pk Lin)} {U : NfTy Δ (KV pk′ Lin)}
    → Γ ∋ˡ x ∶ T
    → (B-Used U ▻ Γ) ∋ˡ suc x ∶ T

data _∋ᵘ_∶_ {Δ} : ∀ {n} → Ctx Δ n → Fin n → ∀ {pk} → NfTy Δ (KV pk Un) → Set where
  hereᵘ : ∀ {n} {Γ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Un)}
    → (T ∷ᵘ Γ) ∋ᵘ zero ∶ T
  thereᵘˡ : ∀ {Γ pk pk′} {x : Fin n} {T : NfTy Δ (KV pk Un)} {U : NfTy Δ (KV pk′ Lin)}
    → Γ ∋ᵘ x ∶ T
    → (U ∷ˡ Γ) ∋ᵘ suc x ∶ T
  thereᵘᵘ : ∀ {Γ pk pk′} {x : Fin n} {T : NfTy Δ (KV pk Un)} {U : NfTy Δ (KV pk′ Un)}
    → Γ ∋ᵘ x ∶ T
    → (U ∷ᵘ Γ) ∋ᵘ suc x ∶ T
  thereᵘ✖ : ∀ {Γ pk pk′} {x : Fin n}
      {T : NfTy Δ (KV pk Un)} {U : NfTy Δ (KV pk′ Lin)}
    → Γ ∋ᵘ x ∶ T
    → (B-Used U ▻ Γ) ∋ᵘ suc x ∶ T

mutual
  data _⊢ˡ_∶_⊣_ {Δ} : ∀ {n} → Ctx Δ n → Fin n → ∀ {pk} → NfTy Δ (KV pk Lin) → Ctx Δ n → Set where
    take-here : ∀ {n} {Γ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Lin)}
      → (T ∷ˡ Γ) ⊢ˡ zero ∶ T ⊣ (B-Used T ▻ Γ)

    take-thereˡ : ∀ {Γ Γ′ pk pk′} {x : Fin n} {T : NfTy Δ (KV pk Lin)} {U : NfTy Δ (KV pk′ Lin)}
      → Γ ⊢ˡ x ∶ T ⊣ Γ′
      → (U ∷ˡ Γ) ⊢ˡ suc x ∶ T ⊣ (U ∷ˡ Γ′)

    take-thereᵘ : ∀ {Γ Γ′ pk pk′} {x : Fin n} {T : NfTy Δ (KV pk Lin)} {U : NfTy Δ (KV pk′ Un)}
      → Γ ⊢ˡ x ∶ T ⊣ Γ′
      → (U ∷ᵘ Γ) ⊢ˡ suc x ∶ T ⊣ (U ∷ᵘ Γ′)

    take-there✖ : ∀ {Γ Γ′ pk pk′} {x : Fin n}
        {T : NfTy Δ (KV pk Lin)} {U : NfTy Δ (KV pk′ Lin)}
      → Γ ⊢ˡ x ∶ T ⊣ Γ′
      → (B-Used U ▻ Γ) ⊢ˡ suc x ∶ T ⊣ (B-Used U ▻ Γ′)

  data _⊢ᵥ_⇒_⊣_ {Δ} : ∀ {n} → (Γ₁ : Ctx Δ n) → Value Δ n → ∀ {pk m} → NfTy Δ (KV pk m) → Ctx Δ n → Set where
    TV-Const : ∀ {n} {Γ₁ : Ctx Δ n} {c pk m} {T : NfTy Δ (KV pk m)}
      → ConstTy c T
      → Γ₁ ⊢ᵥ V-Const c ⇒ T ⊣ Γ₁

    TV-Var-Lin : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {pk} {x : Fin n} {T : NfTy Δ (KV pk Lin)}
      → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂
      → Γ₁ ⊢ᵥ V-Var x ⇒ T ⊣ Γ₂

    TV-Var-Un : ∀ {n} {Γ₁ : Ctx Δ n} {pk} {x : Fin n} {T : NfTy Δ (KV pk Un)}
      → Γ₁ ∋ᵘ x ∶ T
      → Γ₁ ⊢ᵥ V-Var x ⇒ T ⊣ Γ₁

    TV-Abs : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n}
        {pk₁ pk₂ m₂}
        {T : NfTy Δ (KV pk₁ Lin)} {U : NfTy Δ (KV pk₂ m₂)} {e : Expr Δ (suc n)}
      → (T ∷ˡ Γ₁) ⊢ e ⇒ U ⊣ (B-Used T ▻ Γ₂)
      → Γ₁ ⊢ᵥ V-Abs T e ⇒ N-Arrow {m = Lin} T U ⊣ Γ₂

    TV-Rec : ∀ {n} {Γ₁ : Ctx Δ n}
        {pk₁ pk₂ m₁ m₂}
        {T : NfTy Δ (KV pk₁ m₁)} {U : NfTy Δ (KV pk₂ m₂)} {v : Value Δ (suc n)}
      → (N-Arrow {m = Un} T U ∷ᵘ Γ₁)
          ⊢ E-Val v ⇐ N-Arrow {m = Un} T U
          ⊣ (N-Arrow {m = Un} T U ∷ᵘ Γ₁)
      → Γ₁ ⊢ᵥ V-Rec T U v ⇒ N-Arrow {m = Un} T U ⊣ Γ₁

    TV-TAbs : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {K m}
        {v : Value (K ∷ Δ) n} {T : NfTy (K ∷ Δ) (KV KT m)}
      → wkCtx {K = K} Γ₁ ⊢ᵥ v ⇒ T ⊣ wkCtx Γ₂
      → Γ₁ ⊢ᵥ V-TAbs K v ⇒ polyNf T ⊣ Γ₂

    TV-Pair : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {v₁ v₂ : Value Δ n}
        {pk₁ pk₂ m}
        {T : NfTy Δ (KV pk₁ m)} {U : NfTy Δ (KV pk₂ m)}
      → Γ₁ ⊢ᵥ v₁ ⇒ T ⊣ Γ₂
      → Γ₂ ⊢ᵥ v₂ ⇒ U ⊣ Γ₃
      → Γ₁ ⊢ᵥ V-Pair v₁ v₂ ⇒ pairNf T U ⊣ Γ₃

    TV-Receive₁ : ∀ {n} {Γ₁ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Lin)}
      → Γ₁ ⊢ᵥ V-Receive₁ T ⇒ receive1Nf T ⊣ Γ₁

    TV-Receive₂ : ∀ {n} {Γ₁ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Lin)} {S : NfTy Δ SLin}
      → Γ₁ ⊢ᵥ V-Receive₂ T S ⇒ receiveNf T S ⊣ Γ₁

    TV-Send₁ : ∀ {n} {Γ₁ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Lin)}
      → Γ₁ ⊢ᵥ V-Send₁ T ⇒ send1Nf T ⊣ Γ₁

    TV-Send₂ : ∀ {n} {Γ₁ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Lin)} {S : NfTy Δ SLin}
      → Γ₁ ⊢ᵥ V-Send₂ T S ⇒ sendNf T S ⊣ Γ₁

    TV-Select₁ : ∀ {n} {Γ₁ : Ctx Δ n} {k} {v : Variance} {i : Fin k} {P : NfTy Δ KP}
      → Γ₁ ⊢ᵥ V-Select₁ v i P ⇒ select1Nf v i P ⊣ Γ₁

    TV-Select₂ : ∀ {n} {Γ₁ : Ctx Δ n} {k} {v : Variance} {i : Fin k} {P : NfTy Δ KP} {S : NfTy Δ SLin}
      → Γ₁ ⊢ᵥ V-Select₂ v i P S ⇒ selectNf v i P S ⊣ Γ₁

  data _⊢_⇒_⊣_ {Δ} : ∀ {n} → (Γ₁ : Ctx Δ n) → Expr Δ n → ∀ {pk m} → NfTy Δ (KV pk m) → Ctx Δ n → Set where
    T-Val : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {v : Value Δ n} {pk m} {T : NfTy Δ (KV pk m)}
      → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
      → Γ₁ ⊢ E-Val v ⇒ T ⊣ Γ₂

    T-Pair : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n}
        {pk₁ pk₂ m}
        {T : NfTy Δ (KV pk₁ m)} {U : NfTy Δ (KV pk₂ m)}
      → Γ₁ ⊢ e₁ ⇒ T ⊣ Γ₂
      → Γ₂ ⊢ e₂ ⇒ U ⊣ Γ₃
      → Γ₁ ⊢ E-Pair e₁ e₂ ⇒ pairNf T U ⊣ Γ₃

    T-App : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n}
        {m m₁ m₂ : Multiplicity} {pk₁ pk₂ : PreKind}
        {T : NfTy Δ (KV pk₁ m₁)} {U : NfTy Δ (KV pk₂ m₂)}
      → Γ₁ ⊢ e₁ ⇒ N-Arrow {m = m} T U ⊣ Γ₂
      → Γ₂ ⊢ e₂ ⇐ T ⊣ Γ₃
      → Γ₁ ⊢ E-App e₁ e₂ ⇒ U ⊣ Γ₃

    T-LetUnit : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n}
        {pk : PreKind} {m : Multiplicity}
        {T : NfTy Δ (KV pk m)}
      → Γ₁ ⊢ e₁ ⇐ unitConstNf ⊣ Γ₂
      → Γ₂ ⊢ e₂ ⇒ T ⊣ Γ₃
      → Γ₁ ⊢ E-LetUnit e₁ e₂ ⇒ T ⊣ Γ₃

    T-LetPair : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n}
        {pk₁ pk₂ : PreKind} {pk : PreKind} {m : Multiplicity}
        {T : NfTy Δ (KV pk₁ Lin)} {U : NfTy Δ (KV pk₂ Lin)} {V : NfTy Δ (KV pk m)}
        {e₁ : Expr Δ n} {e₂ : Expr Δ (suc (suc n))}
      → Γ₁ ⊢ e₁ ⇒ pairNf T U ⊣ Γ₂
      → (T ∷ˡ (U ∷ˡ Γ₂)) ⊢ e₂ ⇒ V ⊣ (B-Used T ▻ (B-Used U ▻ Γ₃))
      → Γ₁ ⊢ E-LetPair e₁ e₂ ⇒ V ⊣ Γ₃

    T-Match : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {k} {e : Expr Δ n}
        {ss : Subset.Subset (suc k)} {v : Variance}
        {ssbranches : Subset.Subset (suc k)} {incl : ss Subset.⊆ ssbranches} {ne : Subset.Nonempty ssbranches}
        {P : NfTy Δ KP} {S : NfTy Δ SLin} {pk : PreKind} {m : Multiplicity}
        {U : NfTy Δ (KV pk m)}
        {branches : ∀ i → (i∈ : i Subset.∈ ssbranches) → Expr Δ (suc n)}
        {V : ∀ i →  i Subset.∈ ssbranches → NfTy Δ (KV pk m)}
        {sub : ∀ i → (i∈ : i Subset.∈ ssbranches) → V i i∈ <:ₜ U}
      → Γ₁ ⊢ e ⇒ MatchBranchInput ss v P S ⊣ Γ₂
      → ((i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) →
          (MatchBranchOutput ssbranches v P S i i∈ ∷ˡ Γ₂)
            ⊢ branches i i∈ ⇒ V i i∈ ⊣ (B-Used (MatchBranchOutput ssbranches v P S i i∈) ▻ Γ₃))
      → BranchJoin⁺ ssbranches V ≡ just (U , sub)
      → Γ₁ ⊢ E-Match e ne branches ⇒ U ⊣ Γ₃

    T-TApp : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {K m}
        {e : Expr Δ n} {T : NfTy (K ∷ Δ) (KV KT m)} {U : NfTy Δ K}
      → Γ₁ ⊢ e ⇒ polyNf T ⊣ Γ₂
      → Γ₁ ⊢ E-TApp e U ⇒ substNFTy T U ⊣ Γ₂

  data _⊢_⇐_⊣_ {Δ} : ∀ {n} → (Γ₁ : Ctx Δ n) → Expr Δ n → ∀ {pk m} → NfTy Δ (KV pk m) → Ctx Δ n → Set where
    T-Check : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {e : Expr Δ n} {pk m}
        {T U : NfTy Δ (KV pk m)}
      → Γ₁ ⊢ e ⇒ U ⊣ Γ₂
      → U <:ₜ T
      → Γ₁ ⊢ e ⇐ T ⊣ Γ₂

pair-injective :
  ∀ {Δ pk₁ pk₂ m} {T₁ T₂ : Ty Δ (KV pk₁ m)} {U₁ U₂ : Ty Δ (KV pk₂ m)}
  → T-Pair T₁ U₁ ≡ T-Pair T₂ U₂
  → (T₁ ≡ T₂) × (U₁ ≡ U₂)
pair-injective refl = refl , refl

nfTyEq :
  ∀ {Δ pk m} {T₁ T₂ : NfTy Δ (KV pk m)}
  → ⌞ T₁ ⌟ ≡ ⌞ T₂ ⌟
  → T₁ ≡ T₂
nfTyEq = nfTyTy-injective

nfEq :
  ∀ {Δ K} {T₁ T₂ : NfTy Δ K}
  → ⌞ T₁ ⌟ ≡ ⌞ T₂ ⌟
  → T₁ ≡ T₂
nfEq {K = KV pk m} = nfTyTy-injective
nfEq {K = KP} = nfProtoTy-injective

normalizeTy-id :
  ∀ {Δ K} (T : NfTy Δ K)
  → normalizeTy (⌞ T ⌟) ≡ T
normalizeTy-id {K = KV pk m} T =
  nfTyTy-injective
    (trans
      (nfTyTy-fromNormalTy (Types.nf-normal-type ⊕ d?⊥ (nfTyTy T)))
      (Types.nf-idempotent (toNormalTy T)))
normalizeTy-id {K = KP} T =
  nfProtoTy-injective
    (trans
      (nfProtoTy-fromNormalProto (Types.nf-normal-proto (nfProtoTy T)))
      (Types.nfp-idempotent (toNormalProto T)))

wkNfTy-injective :
  ∀ {Δ K K′} {T U : NfTy Δ K}
  → wkNfTy {K′ = K′} T ≡ wkNfTy {K′ = K′} U
  → T ≡ U
wkNfTy-injective {K = K} {K′ = K′} {T = T} {U = U} eq =
  nfEq {K = K}
    (renaming-injective
      (weakenᵣ K′)
      weakenᵣ-injective
      (trans
        (sym (wkNFKind-sound {K′ = K′} T))
        (trans (cong ⌞_⌟ eq) (wkNFKind-sound {K′ = K′} U))))

linBinding-injective :
  {T₁ : NfTy Δ (KV pk₁ Lin)} {T₂ : NfTy Δ (KV pk₂ Lin)}
  → Binding.B-Lin T₁ ≡ Binding.B-Lin T₂
  → pk₁ ≡ pk₂
linBinding-injective refl = refl

linBinding-injective₂ :
  {T₁ : NfTy Δ (KV pk Lin)} {T₂ : NfTy Δ (KV pk Lin)}
  → Binding.B-Lin T₁ ≡ Binding.B-Lin T₂
  → T₁ ≡ T₂
linBinding-injective₂ refl = refl

unBinding-injective :
  {T₁ : NfTy Δ (KV pk₁ Un)} {T₂ : NfTy Δ (KV pk₂ Un)}
  → Binding.B-Un T₁ ≡ Binding.B-Un T₂
  → pk₁ ≡ pk₂
unBinding-injective refl = refl

unBinding-injective₂ :
  {T₁ : NfTy Δ (KV pk Un)} {T₂ : NfTy Δ (KV pk Un)}
  → Binding.B-Un T₁ ≡ Binding.B-Un T₂
  → T₁ ≡ T₂
unBinding-injective₂ refl = refl

usedBinding-injective :
  {T₁ : NfTy Δ (KV pk₁ Lin)} {T₂ : NfTy Δ (KV pk₂ Lin)}
  → Binding.B-Used T₁ ≡ Binding.B-Used T₂
  → pk₁ ≡ pk₂
usedBinding-injective refl = refl

usedBinding-injective₂ :
  {T₁ : NfTy Δ (KV pk Lin)} {T₂ : NfTy Δ (KV pk Lin)}
  → Binding.B-Used T₁ ≡ Binding.B-Used T₂
  → T₁ ≡ T₂
usedBinding-injective₂ refl = refl

wkBinding-injective :
  ∀ {Δ L} {b₁ b₂ : Binding Δ}
  → wkBinding {K = L} b₁ ≡ wkBinding {K = L} b₂
  → b₁ ≡ b₂
wkBinding-injective {Δ} {L} {B-Lin T₁} {B-Lin T₂} eq
  with linBinding-injective eq
... | refl = cong B-Lin (wkNfTy-injective (linBinding-injective₂ eq))
wkBinding-injective {Δ} {L} {B-Un T₁} {B-Un T₂} eq
  with unBinding-injective eq
... | refl  = cong B-Un (wkNfTy-injective (unBinding-injective₂ eq))
wkBinding-injective {Δ} {L} {B-Used T₁} {B-Used T₂} eq
  with usedBinding-injective eq
... | refl = cong B-Used (wkNfTy-injective (usedBinding-injective₂ eq))

wkCtx-injective :
  ∀ {Δ n K} {Γ₁ Γ₂ : Ctx Δ n}
  → wkCtx {K = K} Γ₁ ≡ wkCtx {K = K} Γ₂
  → Γ₁ ≡ Γ₂
wkCtx-injective {Γ₁ = ∅} {Γ₂ = ∅} refl = refl
wkCtx-injective {Γ₁ = b₁ ▻ Γ₁} {Γ₂ = b₂ ▻ Γ₂} eq
  with wkBinding-injective (cong (λ where (b ▻ _) → b) eq)
     | wkCtx-injective (cong (λ where (_ ▻ Γ) → Γ) eq)
... | refl | refl = refl

pairNf-injective :
  ∀ {Δ pk₁ pk₂ m} {T₁ T₂ : NfTy Δ (KV pk₁ m)} {U₁ U₂ : NfTy Δ (KV pk₂ m)}
  → pairNf T₁ U₁ ≡ pairNf T₂ U₂
  → (T₁ ≡ T₂) × (U₁ ≡ U₂)
pairNf-injective refl = refl , refl

linArrNf-injective :
  ∀ {Δ pk₁ pk₂ m₁ m₂}
    {T₁ T₂ : NfTy Δ (KV pk₁ m₁)}
    {U₁ U₂ : NfTy Δ (KV pk₂ m₂)}
  → linArrNf T₁ U₁ ≡ linArrNf T₂ U₂
  → (T₁ ≡ T₂) × (U₁ ≡ U₂)
linArrNf-injective refl = refl , refl

unArrNf-injective :
  ∀ {Δ} {T₁ T₂ U₁ U₂ : NfTy Δ TLin}
  → unArrNf T₁ U₁ ≡ unArrNf T₂ U₂
  → (T₁ ≡ T₂) × (U₁ ≡ U₂)
unArrNf-injective refl = refl , refl

polyNf-injective :
  ∀ {Δ K m} {T₁ T₂ : NfTy (K ∷ Δ) (KV KT m)}
  → polyNf T₁ ≡ polyNf T₂
  → T₁ ≡ T₂
polyNf-injective refl = refl
