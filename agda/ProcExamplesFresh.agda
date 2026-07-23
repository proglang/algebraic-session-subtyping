module ProcExamplesFresh where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Subset as Subset
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Data.Vec using (here; there) renaming (_∷_ to _∷ᵥ_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Kinds
open import Types using (Ty; T-Base; T-End; T-Sub; T-Up)
import Variance
open import ExprSyntax
open import ExprNormalTyping using (normalizeTy)
import ExprSemantics as ES
open import ExprSemantics using
  ( freshPair
  )
import ProcSemanticsFresh as PS
open PS using
  ( Conf
  ; C-τ
  ; C-new
  ; _—conf[_]→_
  )

-- These are operational examples for the flat configuration semantics.  A
-- configuration contains no parallel or restriction syntax: list entries are
-- the parallel threads, and Act-New makes its fresh endpoint pair globally
-- available at indices zero and one.

endLin : Ty [] SLin
endLin = T-Sub (≤k-step ≤p-refl ≤m-unl) T-End

oneProtocol : Ty [] KP
oneProtocol = T-Up T-Base

unitValue : ∀ {n} → Value [] n
unitValue = V-Const C-Unit

unitExpr : ∀ {n} → Expr [] n
unitExpr = E-Val unitValue

betaExpr : ∀ {n} → Expr [] n
betaExpr = E-LetUnit unitExpr unitExpr

closeExpr : ∀ {n} → Fin n → Expr [] n
closeExpr ch = E-App (E-Val (V-Const C-Close)) (E-Val (V-Var ch))

receiveValueExpr : ∀ {n} → Fin n → Expr [] n
receiveValueExpr ch =
  E-App
    (E-Val (V-Receive₂ (normalizeTy T-Base) (normalizeTy endLin)))
    (E-Val (V-Var ch))

receiveValueResult : ∀ {n} → Fin n → Value [] n → Expr [] n
receiveValueResult ch v = E-Val (V-Pair v (V-Var ch))

sendValueExpr : ∀ {n} → Fin n → Value [] n → Expr [] n
sendValueExpr ch v =
  E-App
    (E-Val (V-Send₂ (normalizeTy T-Base) (normalizeTy endLin)))
    (E-Val (V-Pair v (V-Var ch)))

sendValueResult : ∀ {n} → Fin n → Expr [] n
sendValueResult ch = E-Val (V-Var ch)

------------------------------------------------------------------------
-- Internal expression actions

beta-source beta-target : Conf 0
beta-source = record
  { exps = betaExpr ∷ []
  ; live = Subset.⊥
  }
beta-target = record
  { exps = unitExpr ∷ []
  ; live = Subset.⊥
  }

configuration-beta : beta-source —conf[ C-τ ]→ beta-target
configuration-beta = PS.Act-Beta {i = fzero} ES.Act-LetUnit

-- The old process examples needed separate Act-ParL/Act-ParR rules.  In the
-- flat semantics their distinction is just the selected list position.

parallel-beta-source parallel-beta-left-target parallel-beta-right-target : Conf 0
parallel-beta-source = record
  { exps = betaExpr ∷ betaExpr ∷ []
  ; live = Subset.⊥
  }
parallel-beta-left-target = record
  { exps = unitExpr ∷ betaExpr ∷ []
  ; live = Subset.⊥
  }
parallel-beta-right-target = record
  { exps = betaExpr ∷ unitExpr ∷ []
  ; live = Subset.⊥
  }

parallel-left-beta :
  parallel-beta-source —conf[ C-τ ]→ parallel-beta-left-target
parallel-left-beta = PS.Act-Beta {i = fzero} ES.Act-LetUnit

parallel-right-beta :
  parallel-beta-source —conf[ C-τ ]→ parallel-beta-right-target
parallel-right-beta = PS.Act-Beta {i = fsuc fzero} ES.Act-LetUnit

forkExpr : Expr [] 0
forkExpr =
  E-App
    (E-Val (V-Const C-Fork))
    (E-Val (V-Const C-Unit))

forkedExpr : Expr [] 0
forkedExpr =
  E-App
    (E-Val (V-Const C-Unit))
    (E-Val (V-Const C-Unit))

fork-source fork-target : Conf 0
fork-source = record
  { exps = forkExpr ∷ []
  ; live = Subset.⊥
  }
fork-target = record
  { exps = forkedExpr ∷ unitExpr ∷ []
  ; live = Subset.⊥
  }

configuration-fork : fork-source —conf[ C-τ ]→ fork-target
configuration-fork =
  PS.Act-Fork {i = fzero} (ES.Act-Fork {v = V-Const C-Unit})

newExpr : Expr [] 0
newExpr =
  E-TApp (E-Val (V-Const C-New)) (normalizeTy endLin)

new-source : Conf 0
new-source = record
  { exps = newExpr ∷ []
  ; live = Subset.⊥
  }

new-target : Conf 2
new-target = record
  { exps = freshPair ∷ []
  ; live = Subset.⊤
  }

configuration-new : new-source —conf[ C-new ]→ new-target
configuration-new =
  PS.Act-New {i = fzero} (ES.Act-New {S = endLin})

------------------------------------------------------------------------
-- Value synchronization: endpoint and depth symmetry

left₂ : Fin 2
left₂ = fzero

right₂ : Fin 2
right₂ = fsuc fzero

zero≠one : left₂ ≢ right₂
zero≠one ()

left-live₂ : left₂ Subset.∈ Subset.⊤
left-live₂ = here

right-live₂ : right₂ Subset.∈ Subset.⊤
right-live₂ = there here

message-source-forward message-target-forward : Conf 2
message-source-forward = record
  { exps = receiveValueExpr left₂ ∷ sendValueExpr right₂ unitValue ∷ []
  ; live = Subset.⊤
  }
message-target-forward = record
  { exps = receiveValueResult left₂ unitValue ∷ sendValueResult right₂ ∷ []
  ; live = Subset.⊤
  }

message-forward :
  message-source-forward —conf[ C-τ ]→ message-target-forward
message-forward =
  PS.Act-Msg left₂ right₂ zero≠one
    PS.here-fwd
    left-live₂
    right-live₂
    (ES.Act-Rcv
      {T = normalizeTy T-Base} {S = normalizeTy endLin}
      {x = left₂} {v = unitValue})
    (ES.Act-Send
      {T = normalizeTy T-Base} {S = normalizeTy endLin}
      {x = right₂} {v = unitValue})

message-source-backward message-target-backward : Conf 2
message-source-backward = record
  { exps = receiveValueExpr right₂ ∷ sendValueExpr left₂ unitValue ∷ []
  ; live = Subset.⊤
  }
message-target-backward = record
  { exps = receiveValueResult right₂ unitValue ∷ sendValueResult left₂ ∷ []
  ; live = Subset.⊤
  }

message-backward :
  message-source-backward —conf[ C-τ ]→ message-target-backward
message-backward =
  PS.Act-Msg left₂ right₂ zero≠one
    PS.here-bwd
    right-live₂
    left-live₂
    (ES.Act-Rcv
      {T = normalizeTy T-Base} {S = normalizeTy endLin}
      {x = right₂} {v = unitValue})
    (ES.Act-Send
      {T = normalizeTy T-Base} {S = normalizeTy endLin}
      {x = left₂} {v = unitValue})

deepLeft₄ : Fin 4
deepLeft₄ = fsuc (fsuc fzero)

deepRight₄ : Fin 4
deepRight₄ = fsuc (fsuc (fsuc fzero))

deepLive₄ : Subset.Subset 4
deepLive₄ =
  Subset.outside ∷ᵥ
  Subset.outside ∷ᵥ
  Subset.inside ∷ᵥ
  Subset.inside ∷ᵥ
  Subset.⊥

deep-left-live : deepLeft₄ Subset.∈ deepLive₄
deep-left-live = there (there here)

deep-right-live : deepRight₄ Subset.∈ deepLive₄
deep-right-live = there (there (there here))

message-source-deep message-target-deep : Conf 4
message-source-deep = record
  { exps = receiveValueExpr deepLeft₄ ∷ sendValueExpr deepRight₄ unitValue ∷ []
  ; live = deepLive₄
  }
message-target-deep = record
  { exps = receiveValueResult deepLeft₄ unitValue ∷ sendValueResult deepRight₄ ∷ []
  ; live = deepLive₄
  }

message-deep : message-source-deep —conf[ C-τ ]→ message-target-deep
message-deep =
  PS.Act-Msg left₂ right₂ zero≠one
    (PS.there PS.here-fwd)
    deep-left-live
    deep-right-live
    (ES.Act-Rcv
      {T = normalizeTy T-Base} {S = normalizeTy endLin}
      {x = deepLeft₄} {v = unitValue})
    (ES.Act-Send
      {T = normalizeTy T-Base} {S = normalizeTy endLin}
      {x = deepRight₄} {v = unitValue})

------------------------------------------------------------------------
-- Branch synchronization

oneSubset : Subset.Subset 1
oneSubset = Subset.⁅ fzero ⁆

oneMember : fzero Subset.∈ oneSubset
oneMember = here

oneNonempty : Subset.Nonempty oneSubset
oneNonempty = fzero , oneMember

oneBranches :
  ∀ {n}
  → (i : Fin 1)
  → i Subset.∈ oneSubset
  → Expr [] (suc n)
oneBranches i i∈ = unitExpr

receiveBranchExpr : ∀ {n} → Fin n → Expr [] n
receiveBranchExpr ch =
  E-Match (E-Val (V-Var ch)) oneNonempty oneBranches

sendBranchExpr : ∀ {n} → Fin n → Expr [] n
sendBranchExpr ch =
  E-App
    (E-Val
      (V-Select₂
        {k = 1}
        Variance.⊕
        fzero
        (normalizeTy oneProtocol)
        (normalizeTy endLin)))
    (E-Val (V-Var ch))

branch-source-forward branch-target-forward : Conf 2
branch-source-forward = record
  { exps = receiveBranchExpr left₂ ∷ sendBranchExpr right₂ ∷ []
  ; live = Subset.⊤
  }
branch-target-forward = record
  { exps = unitExpr ∷ E-Val (V-Var right₂) ∷ []
  ; live = Subset.⊤
  }

branch-forward : branch-source-forward —conf[ C-τ ]→ branch-target-forward
branch-forward =
  PS.Act-Bra left₂ right₂ zero≠one
    PS.here-fwd
    left-live₂
    right-live₂
    (ES.Act-Match
      {ss = oneSubset}
      {ne = oneNonempty}
      {x = left₂}
      {branches = oneBranches}
      {i = fzero}
      oneMember)
    (ES.Act-Sel
      {k = 1}
      {v = Variance.⊕}
      {i = fzero}
      {P = normalizeTy oneProtocol}
      {S = normalizeTy endLin}
      {x = right₂})

branch-source-backward branch-target-backward : Conf 2
branch-source-backward = record
  { exps = receiveBranchExpr right₂ ∷ sendBranchExpr left₂ ∷ []
  ; live = Subset.⊤
  }
branch-target-backward = record
  { exps = unitExpr ∷ E-Val (V-Var left₂) ∷ []
  ; live = Subset.⊤
  }

branch-backward :
  branch-source-backward —conf[ C-τ ]→ branch-target-backward
branch-backward =
  PS.Act-Bra left₂ right₂ zero≠one
    PS.here-bwd
    right-live₂
    left-live₂
    (ES.Act-Match
      {ss = oneSubset}
      {ne = oneNonempty}
      {x = right₂}
      {branches = oneBranches}
      {i = fzero}
      oneMember)
    (ES.Act-Sel
      {k = 1}
      {v = Variance.⊕}
      {i = fzero}
      {P = normalizeTy oneProtocol}
      {S = normalizeTy endLin}
      {x = left₂})

------------------------------------------------------------------------
-- Closing a pair marks both channel entries dead

wait-source wait-target : Conf 2
wait-source = record
  { exps = closeExpr left₂ ∷ closeExpr right₂ ∷ []
  ; live = Subset.⊤
  }
wait-target = record
  { exps = unitExpr ∷ unitExpr ∷ []
  ; live = Subset.⊥
  }

wait-forward : wait-source —conf[ C-τ ]→ wait-target
wait-forward =
  PS.Act-Wait left₂ right₂ zero≠one
    PS.here-fwd
    left-live₂
    right-live₂
    (ES.Act-Close {x = left₂})
    (ES.Act-Close {x = right₂})

wait-source-backward : Conf 2
wait-source-backward = record
  { exps = closeExpr right₂ ∷ closeExpr left₂ ∷ []
  ; live = Subset.⊤
  }

wait-backward : wait-source-backward —conf[ C-τ ]→ wait-target
wait-backward =
  PS.Act-Wait left₂ right₂ zero≠one
    PS.here-bwd
    right-live₂
    left-live₂
    (ES.Act-Close {x = right₂})
    (ES.Act-Close {x = left₂})

-- There are intentionally no separate reconstructions of the old
-- Act-Session, Act-Par, Act-Open, or restriction-propagation examples.
-- Observable expression actions occur only as premises of the three direct
-- synchronization rules; parallel components are list entries; and Act-New
-- replaces scope opening/extrusion by extending the shared namespace and
-- marking the new pair live.  The examples above cover every constructor of
-- the fresh configuration reduction relation under that representation.
