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

NfTy : List Kind → Kind → Set
NfTy = NFKind

⌞_⌟ : NfTy Δ K → Ty Δ K
⌞_⌟ = nfKindTy

normalTyOf : (N : NfTy Δ (KV pk m)) → NFTy Δ (KV pk m)
normalTyOf N = N

normalProtoOf : (N : NfTy Δ KP) → NFProto Δ
normalProtoOf N = N

normalizeTy : ∀ {K} → Ty Δ K → NfTy Δ K
normalizeTy {K = KV pk m} T = nf-normal-type ⊕ d?⊥ T
normalizeTy {K = KP} T = nf-normal-proto T

data Binding (Δ : List Kind) : Set where
  B-Lin  : ∀ {K} → NfTy Δ K → Binding Δ
  B-Un   : ∀ {K} → NfTy Δ K → Binding Δ
  B-Used : Binding Δ

infixr 5 _▻_

data Ctx (Δ : List Kind) : ℕ → Set where
  ∅   : Ctx Δ 0
  _▻_ : ∀ {n} → Binding Δ → Ctx Δ n → Ctx Δ (suc n)

_∷ˡ_ : ∀ {n K} → NfTy Δ K → Ctx Δ n → Ctx Δ (suc n)
T ∷ˡ Γ = B-Lin T ▻ Γ

_∷ᵘ_ : ∀ {n K} → NfTy Δ K → Ctx Δ n → Ctx Δ (suc n)
T ∷ᵘ Γ = B-Un T ▻ Γ

_∷ⁿˡ_ : ∀ {n K} → Ty Δ K → Ctx Δ n → Ctx Δ (suc n)
T ∷ⁿˡ Γ = normalizeTy T ∷ˡ Γ

_∷ⁿᵘ_ : ∀ {n K} → Ty Δ K → Ctx Δ n → Ctx Δ (suc n)
T ∷ⁿᵘ Γ = normalizeTy T ∷ᵘ Γ

used∷ : ∀ {n} → Ctx Δ n → Ctx Δ (suc n)
used∷ Γ = B-Used ▻ Γ

wkNfTy : ∀ {K K′} → NfTy Δ K → NfTy (K′ ∷ Δ) K
wkNfTy = wkNFKind

wkBinding : ∀ {K} → Binding Δ → Binding (K ∷ Δ)
wkBinding {K = K} (B-Lin T) = B-Lin (wkNfTy {K′ = K} T)
wkBinding {K = K} (B-Un T) = B-Un (wkNfTy {K′ = K} T)
wkBinding B-Used = B-Used

wkCtx : ∀ {n K} → Ctx Δ n → Ctx (K ∷ Δ) n
wkCtx ∅ = ∅
wkCtx (b ▻ Γ) = wkBinding b ▻ wkCtx Γ

LinArr : Ty Δ TLin → Ty Δ TLin → Ty Δ TLin
LinArr = T-Arrow {pk = KT} {m = Lin} (≤p-step <p-mt)

linArrNf : NfTy Δ TLin → NfTy Δ TLin → NfTy Δ TLin
linArrNf = N-Arrow (≤p-step <p-mt)

unArrNf : NfTy Δ TLin → NfTy Δ TLin → NfTy Δ (KV KT Un)
unArrNf = N-Arrow (≤p-step <p-mt)

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

EndLin : Ty Δ TLin
EndLin = T-Sub (≤k-step (≤p-step <p-st) ≤m-unl) T-End

CloseTy : Ty Δ TLin
CloseTy = LinArr EndLin UnitLin

ForkTy : Ty Δ TLin
ForkTy = LinArr (LinArr UnitLin UnitLin) UnitLin

NewTy : Ty Δ TLin
NewTy = T-Poly SLin
  (T-Pair (SessLin (T-Var (here refl)))
          (SessLin (T-Dual D-S (T-Var (here refl)))))

wkTy : ∀ {K K′} → Ty Δ K → Ty (K′ ∷ Δ) K
wkTy {K′ = K′} T = T ⋯ weakenᵣ K′

ReceiveTy : Ty Δ TLin → Ty Δ SLin → Ty Δ TLin
ReceiveTy T S = LinArr
  (SessLin (T-Msg ⊝ (T-Up T) S))
  (T-Pair T (SessLin S))

ReceiveTy1 : Ty Δ TLin → Ty Δ TLin
ReceiveTy1 T = T-Poly SLin
  (ReceiveTy (wkTy {K′ = SLin} T) (T-Var (here refl)))

SendTy : Ty Δ TLin → Ty Δ SLin → Ty Δ TLin
SendTy T S = LinArr T
  (LinArr (SessLin (T-Msg ⊕ (T-Up T) S)) (SessLin S))

SendTy1 : Ty Δ TLin → Ty Δ TLin
SendTy1 T = T-Poly SLin
  (SendTy (wkTy {K′ = SLin} T) (T-Var (here refl)))

unitConstNf : NfTy Δ TLin
unitConstNf = N-Base

sessTyNf : NfTy Δ SLin → NfTy Δ TLin
sessTyNf = N-Sub (≤k-step (≤p-step <p-st) ≤m-refl)

endConstNf : NfTy Δ TLin
endConstNf = N-Sub (≤k-step (≤p-step <p-st) ≤m-unl) N-End

closeConstNf : NfTy Δ TLin
closeConstNf = linArrNf endConstNf unitConstNf

forkConstNf : NfTy Δ TLin
forkConstNf = linArrNf (linArrNf unitConstNf unitConstNf) unitConstNf

newConstNf : NfTy Δ TLin
newConstNf =
  polyNf
    (pairNf
      (sessTyNf (N-Var (NV-Var (here refl))))
      (sessTyNf (N-Var (NV-Dual D-S (here refl)))))

receiveNf : NfTy Δ TLin → NfTy Δ SLin → NfTy Δ TLin
receiveNf T S =
  linArrNf
    (sessTyNf (msgNF ⊝ (N-Normal (N-Up T)) S))
    (pairNf T (sessTyNf S))

receive1Nf : NfTy Δ TLin → NfTy Δ TLin
receive1Nf {Δ = Δ} T =
  polyNf {K = SLin}
    (receiveNf (wkNfTy {K′ = SLin} T) (N-Var (NV-Var (here refl))))

receiveConstNf : NfTy Δ TLin
receiveConstNf =
  polyNf {K = TLin} (receive1Nf (N-Var (NV-Var (here refl))))

sendResultNf : NfTy Δ TLin → NfTy Δ SLin → NfTy Δ TLin
sendResultNf T S =
  linArrNf
    (sessTyNf (msgNF ⊕ (N-Normal (N-Up T)) S))
    (sessTyNf S)

sendNf : NfTy Δ TLin → NfTy Δ SLin → NfTy Δ TLin
sendNf T S = linArrNf T (sendResultNf T S)

send1Nf : NfTy Δ TLin → NfTy Δ TLin
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

selectInTyNf : ∀ {c} → Variance → Fin c → NfTy Δ KP → NfTy Δ SLin → NfTy Δ TLin
selectInTyNf v i P S =
  sessTyNf (msgNF ⊕ (N-Normal (N-ProtoP (Subset.⁅ i ⁆) v P)) S)

selectOutTyNf : ∀ {c} → Variance → Fin c → NfTy Δ KP → NfTy Δ SLin → NfTy Δ TLin
selectOutTyNf {c} v i P S =
  sessTyNf (materialize-atNf (ProtocolConstructors _ v) i ⊕ P S)

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


BranchJoin⁺ : ∀ {k} (ss : Subset.Subset k)
    → (V : ∀ i → i Subset.∈ ss → NfTy Δ TLin)
    → Maybe (Σ (NfTy Δ TLin) λ N → ∀ i → (i∈ : i Subset.∈ ss) → V i i∈ <:ₜ N)
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

data _∋ˡ_∶_ {Δ} : ∀ {n} → Ctx Δ n → Fin n → ∀ {K} → NfTy Δ K → Set where
  hereˡ : ∀ {n} {Γ : Ctx Δ n} {K} {T : NfTy Δ K}
    → (T ∷ˡ Γ) ∋ˡ zero ∶ T
  thereˡˡ : ∀ {Γ K K′} {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
    → Γ ∋ˡ x ∶ T
    → (U ∷ˡ Γ) ∋ˡ suc x ∶ T
  thereˡᵘ : ∀ {Γ K K′} {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
    → Γ ∋ˡ x ∶ T
    → (U ∷ᵘ Γ) ∋ˡ suc x ∶ T
  thereˡ✖ : ∀ {Γ K} {x : Fin n} {T : NfTy Δ K}
    → Γ ∋ˡ x ∶ T
    → used∷ Γ ∋ˡ suc x ∶ T

data _∋ᵘ_∶_ {Δ} : ∀ {n} → Ctx Δ n → Fin n → ∀ {pk} → NfTy Δ (KV pk Un) → Set where
  hereᵘ : ∀ {n} {Γ : Ctx Δ n} {pk} {T : NfTy Δ (KV pk Un)}
    → (T ∷ᵘ Γ) ∋ᵘ zero ∶ T
  thereᵘˡ : ∀ {Γ pk K′} {x : Fin n} {T : NfTy Δ (KV pk Un)} {U : NfTy Δ K′}
    → Γ ∋ᵘ x ∶ T
    → (U ∷ˡ Γ) ∋ᵘ suc x ∶ T
  thereᵘᵘ : ∀ {Γ pk K′} {x : Fin n} {T : NfTy Δ (KV pk Un)} {U : NfTy Δ K′}
    → Γ ∋ᵘ x ∶ T
    → (U ∷ᵘ Γ) ∋ᵘ suc x ∶ T
  thereᵘ✖ : ∀ {Γ pk} {x : Fin n} {T : NfTy Δ (KV pk Un)}
    → Γ ∋ᵘ x ∶ T
    → used∷ Γ ∋ᵘ suc x ∶ T

mutual
  data _⊢ˡ_∶_⊣_ {Δ} : ∀ {n} → Ctx Δ n → Fin n → ∀ {K} → NfTy Δ K → Ctx Δ n → Set where
    take-here : ∀ {n} {Γ : Ctx Δ n} {K} {T : NfTy Δ K}
      → (T ∷ˡ Γ) ⊢ˡ zero ∶ T ⊣ used∷ Γ

    take-thereˡ : ∀ {Γ Γ′ K K′} {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
      → Γ ⊢ˡ x ∶ T ⊣ Γ′
      → (U ∷ˡ Γ) ⊢ˡ suc x ∶ T ⊣ (U ∷ˡ Γ′)

    take-thereᵘ : ∀ {Γ Γ′ K K′} {x : Fin n} {T : NfTy Δ K} {U : NfTy Δ K′}
      → Γ ⊢ˡ x ∶ T ⊣ Γ′
      → (U ∷ᵘ Γ) ⊢ˡ suc x ∶ T ⊣ (U ∷ᵘ Γ′)

    take-there✖ : ∀ {Γ Γ′ K} {x : Fin n} {T : NfTy Δ K}
      → Γ ⊢ˡ x ∶ T ⊣ Γ′
      → used∷ Γ ⊢ˡ suc x ∶ T ⊣ used∷ Γ′

  data _⊢ᵥ_⇒_⊣_ {Δ} : ∀ {n} → (Γ₁ : Ctx Δ n) → Value Δ n → ∀ {K} → NfTy Δ K → Ctx Δ n → Set where
    TV-Const : ∀ {n} {Γ₁ : Ctx Δ n} {c K} {T : NfTy Δ K}
      → ConstTy c T
      → Γ₁ ⊢ᵥ V-Const c ⇒ T ⊣ Γ₁

    TV-Var-Lin : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {K} {x : Fin n} {T : NfTy Δ K}
      → Γ₁ ⊢ˡ x ∶ T ⊣ Γ₂
      → Γ₁ ⊢ᵥ V-Var x ⇒ T ⊣ Γ₂

    TV-Var-Un : ∀ {n} {Γ₁ : Ctx Δ n} {pk} {x : Fin n} {T : NfTy Δ (KV pk Un)}
      → Γ₁ ∋ᵘ x ∶ T
      → Γ₁ ⊢ᵥ V-Var x ⇒ T ⊣ Γ₁

    TV-Abs : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {T : Ty Δ TLin} {U : NfTy Δ TLin} {e : Expr Δ (suc n)}
      → (T ∷ⁿˡ Γ₁) ⊢ e ⇒ U ⊣ used∷ Γ₂
      → Γ₁ ⊢ᵥ V-Abs T e ⇒ linArrNf (normalizeTy T) U ⊣ Γ₂

    TV-Rec : ∀ {n} {Γ₁ : Ctx Δ n} {T U : Ty Δ TLin} {v : Value Δ (suc n)}
      → (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)
          ⊢ E-Val v ⇐ unArrNf (normalizeTy T) (normalizeTy U)
          ⊣ (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)
      → Γ₁ ⊢ᵥ V-Rec T U v ⇒ unArrNf (normalizeTy T) (normalizeTy U) ⊣ Γ₁

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

    TV-Receive₁ : ∀ {n} {Γ₁ : Ctx Δ n} {T : Ty Δ TLin}
      → Γ₁ ⊢ᵥ V-Receive₁ T ⇒ receive1Nf (normalizeTy T) ⊣ Γ₁

    TV-Receive₂ : ∀ {n} {Γ₁ : Ctx Δ n} {T : Ty Δ TLin} {S : Ty Δ SLin}
      → Γ₁ ⊢ᵥ V-Receive₂ T S ⇒ receiveNf (normalizeTy T) (normalizeTy S) ⊣ Γ₁

    TV-Send₁ : ∀ {n} {Γ₁ : Ctx Δ n} {T : Ty Δ TLin}
      → Γ₁ ⊢ᵥ V-Send₁ T ⇒ send1Nf (normalizeTy T) ⊣ Γ₁

    TV-Send₂ : ∀ {n} {Γ₁ : Ctx Δ n} {T : Ty Δ TLin} {S : Ty Δ SLin}
      → Γ₁ ⊢ᵥ V-Send₂ T S ⇒ sendNf (normalizeTy T) (normalizeTy S) ⊣ Γ₁

    TV-Send₃ : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {T : Ty Δ TLin} {S : Ty Δ SLin} {v : Value Δ n}
      → Γ₁ ⊢ E-Val v ⇐ normalizeTy T ⊣ Γ₂
      → Γ₁ ⊢ᵥ V-Send₃ T S v ⇒ sendResultNf (normalizeTy T) (normalizeTy S) ⊣ Γ₂

    TV-Select₁ : ∀ {n} {Γ₁ : Ctx Δ n} {k} {v : Variance} {i : Fin k} {P : Ty Δ KP}
      → Γ₁ ⊢ᵥ V-Select₁ v i P ⇒ select1Nf v i (normalizeTy P) ⊣ Γ₁

    TV-Select₂ : ∀ {n} {Γ₁ : Ctx Δ n} {k} {v : Variance} {i : Fin k} {P : Ty Δ KP} {S : Ty Δ SLin}
      → Γ₁ ⊢ᵥ V-Select₂ v i P S ⇒ selectNf v i (normalizeTy P) (normalizeTy S) ⊣ Γ₁

  data _⊢_⇒_⊣_ {Δ} : ∀ {n} → (Γ₁ : Ctx Δ n) → Expr Δ n → ∀ {K} → NfTy Δ K → Ctx Δ n → Set where
    T-Val : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {v : Value Δ n} {K} {T : NfTy Δ K}
      → Γ₁ ⊢ᵥ v ⇒ T ⊣ Γ₂
      → Γ₁ ⊢ E-Val v ⇒ T ⊣ Γ₂

    T-Pair : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n}
        {pk₁ pk₂ m}
        {T : NfTy Δ (KV pk₁ m)} {U : NfTy Δ (KV pk₂ m)}
      → Γ₁ ⊢ e₁ ⇒ T ⊣ Γ₂
      → Γ₂ ⊢ e₂ ⇒ U ⊣ Γ₃
      → Γ₁ ⊢ E-Pair e₁ e₂ ⇒ pairNf T U ⊣ Γ₃

    T-App : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n}
        {m : Multiplicity}
        {T U : NfTy Δ TLin}
      → Γ₁ ⊢ e₁ ⇒ N-Arrow {m = m} (≤p-step <p-mt) T U ⊣ Γ₂
      → Γ₂ ⊢ e₂ ⇐ T ⊣ Γ₃
      → Γ₁ ⊢ E-App e₁ e₂ ⇒ U ⊣ Γ₃

    T-LetUnit : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n} {T : NfTy Δ TLin}
      → Γ₁ ⊢ e₁ ⇐ unitConstNf ⊣ Γ₂
      → Γ₂ ⊢ e₂ ⇒ T ⊣ Γ₃
      → Γ₁ ⊢ E-LetUnit e₁ e₂ ⇒ T ⊣ Γ₃

    T-LetPair : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {pk₁ pk₂}
        {T : NfTy Δ (KV pk₁ Lin)} {U : NfTy Δ (KV pk₂ Lin)} {V : NfTy Δ TLin}
        {e₁ : Expr Δ n} {e₂ : Expr Δ (suc (suc n))}
      → Γ₁ ⊢ e₁ ⇒ pairNf T U ⊣ Γ₂
      → (T ∷ˡ (U ∷ˡ Γ₂)) ⊢ e₂ ⇒ V ⊣ used∷ (used∷ Γ₃)
      → Γ₁ ⊢ E-LetPair e₁ e₂ ⇒ V ⊣ Γ₃

    T-Match : ∀ {n} {Γ₁ Γ₂ Γ₃ : Ctx Δ n} {k} {e : Expr Δ n}
        {ss : Subset.Subset (suc k)} {v : Variance}
        {ssbranches : Subset.Subset (suc k)} {incl : ss Subset.⊆ ssbranches} {ne : Subset.Nonempty ssbranches}
        {P : NfTy Δ KP} {S : NfTy Δ SLin} {U : NfTy Δ TLin}
        {branches : ∀ i → (i∈ : i Subset.∈ ssbranches) → Expr Δ (suc n)}
        {V : ∀ i →  i Subset.∈ ssbranches → NfTy Δ TLin}
        {sub : ∀ i → (i∈ : i Subset.∈ ssbranches) → V i i∈ <:ₜ U}
      → Γ₁ ⊢ e ⇒ MatchBranchInput ss v P S ⊣ Γ₂
      → ((i : Fin (suc k)) → (i∈ : i Subset.∈ ssbranches) → (MatchBranchOutput ssbranches v P S i i∈ ∷ˡ Γ₂) ⊢ branches i i∈ ⇒ V i i∈ ⊣ used∷ Γ₃)
      → BranchJoin⁺ ssbranches V ≡ just (U , sub)
      → Γ₁ ⊢ E-Match e ne branches ⇒ U ⊣ Γ₃

    T-TApp : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {K m}
        {e : Expr Δ n} {T : NfTy (K ∷ Δ) (KV KT m)} {U : Ty Δ K}
      → Γ₁ ⊢ e ⇒ polyNf T ⊣ Γ₂
      → Γ₁ ⊢ E-TApp e U ⇒ substNFTy T (normalizeTy U) ⊣ Γ₂

  data _⊢_⇐_⊣_ {Δ} : ∀ {n} → (Γ₁ : Ctx Δ n) → Expr Δ n → ∀ {pk m} → NfTy Δ (KV pk m) → Ctx Δ n → Set where
    T-Check : ∀ {n} {Γ₁ Γ₂ : Ctx Δ n} {e : Expr Δ n} {pk m}
        {T U : NfTy Δ (KV pk m)}
      → Γ₁ ⊢ e ⇒ U ⊣ Γ₂
      → normalTyOf U <:ₜ normalTyOf T
      → Γ₁ ⊢ e ⇐ T ⊣ Γ₂

tabs-inversion :
  ∀ {Δ n K m} {Γ₁ Γ₂ : Ctx Δ n} {v : Value (K ∷ Δ) n} {W : NfTy Δ (KV KT m)}
  → Γ₁ ⊢ᵥ V-TAbs K v ⇒ W ⊣ Γ₂
  → Σ (NfTy (K ∷ Δ) (KV KT m)) λ T →
      (W ≡ polyNf T) × (wkCtx {K = K} Γ₁ ⊢ᵥ v ⇒ T ⊣ wkCtx Γ₂)
tabs-inversion (TV-TAbs {T = T} p) = T , refl , p

abs-inversion :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n} {T : Ty Δ TLin} {e : Expr Δ (suc n)} {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ V-Abs T e ⇒ W ⊣ Γ₂
  → Σ (NfTy Δ TLin) λ U →
      (W ≡ linArrNf (normalizeTy T) U) × ((normalizeTy T ∷ˡ Γ₁) ⊢ e ⇒ U ⊣ used∷ Γ₂)
abs-inversion (TV-Abs {U = U} p) = U , refl , p

pair-inversion :
  ∀ {Δ n m} {Γ₁ Γ₃ : Ctx Δ n} {u v : Value Δ n} {W : NfTy Δ (KV KT m)}
  → Γ₁ ⊢ᵥ V-Pair u v ⇒ W ⊣ Γ₃
  → Σ PreKind λ pk₁ →
      Σ PreKind λ pk₂ →
      Σ (NfTy Δ (KV pk₁ m)) λ T →
      Σ (NfTy Δ (KV pk₂ m)) λ U →
        Σ (Ctx Δ n) λ Γ₂ →
          (W ≡ pairNf T U) × ((Γ₁ ⊢ᵥ u ⇒ T ⊣ Γ₂) × (Γ₂ ⊢ᵥ v ⇒ U ⊣ Γ₃))
pair-inversion (TV-Pair {pk₁ = pk₁} {pk₂ = pk₂} p q) = pk₁ , pk₂ , _ , _ , _ , refl , (p , q)

pair-inversion′ :
  ∀ {Δ n pk₁ pk₂ m} {Γ₁ Γ₃ : Ctx Δ n} {u v : Value Δ n}
    {T : NfTy Δ (KV pk₁ m)} {U : NfTy Δ (KV pk₂ m)}
  → Γ₁ ⊢ᵥ V-Pair u v ⇒ pairNf T U ⊣ Γ₃
  → Σ (Ctx Δ n) λ Γ₂ →
      (Γ₁ ⊢ᵥ u ⇒ T ⊣ Γ₂) × (Γ₂ ⊢ᵥ v ⇒ U ⊣ Γ₃)
pair-inversion′ (TV-Pair p q) = _ , p , q

postulate
  pair-expr-inversion :
    ∀ {Δ n pk₁ pk₂ m} {Γ₁ Γ₃ : Ctx Δ n} {e₁ e₂ : Expr Δ n}
      {T : NfTy Δ (KV pk₁ m)} {U : NfTy Δ (KV pk₂ m)}
    → Γ₁ ⊢ E-Pair e₁ e₂ ⇒ pairNf T U ⊣ Γ₃
    → Σ (Ctx Δ n) λ Γ₂ →
        (Γ₁ ⊢ e₁ ⇒ T ⊣ Γ₂) × (Γ₂ ⊢ e₂ ⇒ U ⊣ Γ₃)

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

linBinding-injective : {T₁ : NfTy Δ K₁}{T₂ : NfTy Δ K₂} → Binding.B-Lin T₁ ≡ Binding.B-Lin T₂ → K₁ ≡ K₂
linBinding-injective refl = refl

linBinding-injective₂ : {T₁ : NfTy Δ K}{T₂ : NfTy Δ K} → Binding.B-Lin T₁ ≡ Binding.B-Lin T₂ → T₁ ≡ T₂
linBinding-injective₂ refl = refl

unBinding-injective : {T₁ : NfTy Δ K₁}{T₂ : NfTy Δ K₂} → Binding.B-Un T₁ ≡ Binding.B-Un T₂ → K₁ ≡ K₂
unBinding-injective refl = refl

unBinding-injective₂ : {T₁ : NfTy Δ K}{T₂ : NfTy Δ K} → Binding.B-Un T₁ ≡ Binding.B-Un T₂ → T₁ ≡ T₂
unBinding-injective₂ refl = refl

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
wkBinding-injective {Δ} {L} {B-Used} {B-Used} eq = refl

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

rec-inversion :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n} {T U : Ty Δ TLin} {v : Value Δ (suc n)} {W : NfTy Δ (KV KT Un)}
  → Γ₁ ⊢ᵥ V-Rec T U v ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) ×
    ((W ≡ unArrNf (normalizeTy T) (normalizeTy U)) ×
     ((unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)
       ⊢ E-Val v ⇐ unArrNf (normalizeTy T) (normalizeTy U)
       ⊣ (unArrNf (normalizeTy T) (normalizeTy U) ∷ᵘ Γ₁)))
rec-inversion (TV-Rec p) = refl , refl , p

receive₂-inversion :
  ∀ {Δ n} {Γ₁ Γ₂ : Ctx Δ n} {T : Ty Δ TLin} {S : Ty Δ SLin} {W : NfTy Δ TLin}
  → Γ₁ ⊢ᵥ V-Receive₂ T S ⇒ W ⊣ Γ₂
  → (Γ₁ ≡ Γ₂) × (W ≡ receiveNf (normalizeTy T) (normalizeTy S))
receive₂-inversion TV-Receive₂ = refl , refl

linArrNf-injective :
  ∀ {Δ} {T₁ T₂ U₁ U₂ : NfTy Δ TLin}
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
