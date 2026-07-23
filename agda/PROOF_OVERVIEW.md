# Proof architecture and preservation status

This document maps the active Agda development and its current proof
architecture.  The status descriptions refer to the current working tree.

## Status terminology

- **Constructive**: the module contains definitions and proof terms for the
  result in question.
- **Accepted foundation**: one of the explicit assumptions listed below.
- **Trusted**: constructive relative only to the accepted foundations.

The command `agda -i . README.agda` currently succeeds. This means the module
graph type-checks, but it does not mean that the development is axiom-free.
For the trusted preservation track, `Ext.ext`,
`TypesProtocolConstructors.ProtocolConstructors`, and
`Kits.Syntax._.~-ext` are accepted foundational assumptions.  No other
active postulates occur in the maintained module graph.

## High-level dependency graph

```text
Kinds / Variance / Duality / Kits
                 |
                 v
              Types
                 |
       +---------+----------+
       |                    |
       v                    v
  NormalTypes          Subtyping
       |                    |
       +---------+----------+
                 v
      AlgorithmicNFSubtyping
                 |
                 v
           ExprNormalTyping
          /       |         \
         v        v          v
 ExprSubstitution |   ExprContextProperties
         |        |          |
         v        v          v
 fresh expression/type substitution proofs
                 \           /
                  v         v
       ExprReductionPreservationFresh
                       |
                       v
       ProcReductionPreservationFresh
```

The `Algorithmic*` family works directly with normalized raw types.  Expression
typing and preservation use the `AlgorithmicNF*` family over the separate
normal-form syntax.

## Foundations and type syntax

| Module | Main contents | Status and dependencies |
|---|---|---|
| `Ext` | Function extensionality helper. | `ext` is postulated and accepted as a foundation for the trusted track. |
| `Util` | General list/membership helpers plus shared dependent extensionality and `just` injectivity. | Defined/proved relative to accepted `Ext.ext`. |
| `Kinds` | Kinds, pre-kinds, multiplicities, kind inclusions, decidable equality. | Defined/proved; depends on `Util`. |
| `Variance` | Positive, negative, and invariant variance operations. | Defined/proved. |
| `Duality` | Polarity and duality operations and their algebraic properties. | Defined/proved under `Ext`. |
| `Kits` | Generic renaming and substitution kits. | Mostly defined/proved; equality from pointwise equality (`~-ext`) is postulated. |
| `Types` | Raw kinds-indexed type syntax, renaming/substitution traversal, conversion, normalization, and normality witnesses. | Central defined/proved layer; depends on the preceding modules. |
| `TypesProperties` | Structural facts about type renaming, especially injectivity of weakening. | Defined/proved over `Types`. |
| `TypesDecidable` | Decidable equality and related decision procedures for raw type syntax. | Defined/proved. |
| `TypesProtocolConstructors` | Constructor signatures, instantiation, materialization, and variance-indexed protocol constructors. | Most infrastructure is defined; `ProtocolConstructors` itself is postulated and accepted as a foundation for the trusted track. |
| `TypesProtocolConstructorsExamples` | Small concrete examples of constructor signatures and materialization. | Defined under `ProtocolConstructors`. |

## Normal forms and subtyping

| Module | Main contents | Status and dependencies |
|---|---|---|
| `NormalTypes` | Separate normal-form syntax (`NFProto`, `NFTy`) and bridges to raw types. | Defined/proved over `Types`. |
| `NormalTypesRenamings` | Renaming normal forms and soundness with respect to raw renaming. | Defined/proved. |
| `NormalTypesSubstitution` | Normal-form substitutions, weakening, single substitution, and soundness bridges. | Defined/proved. |
| `Subtyping` | Declarative subtyping and conversion relations for raw types. | Defined/proved. |
| `SubtypingProperties` | Structural and normalization properties of declarative subtyping. | Defined/proved. |
| `SubtypingSize` | Size measures for subtyping derivations. | Defined/proved. |
| `SubstitutionSubtyping` | Preservation of declarative subtyping and conversion by substitution, plus congruence of session dualization under conversion. | Defined/proved under the foundational extensionality assumptions. |
| `AlgorithmicSubtyping` | Original algorithmic subtyping over normalized raw types. | Defines the original algorithmic judgments. |
| `AlgorithmicSound` | Soundness of the original algorithm. | Defined/proved. |
| `AlgorithmicMerge` | Algorithmic joins and meets for the original system. | Defined/proved. |
| `AlgorithmicLubGlb` | LUB/GLB properties of the original joins and meets. | Defined/proved. |
| `AlgorithmicInference` | Decision procedures for the original algorithm. | Defined/proved. |
| `AlgorithmicComplete` | Completeness of the original algorithm. | Defined/proved. |
| `AlgorithmicSubstitution` | Preservation of original algorithmic subtyping by substitution. | Defined/proved from declarative substitution, soundness, and completeness. |
| `AlgorithmicNFSubtyping` | Algorithmic subtyping over the separate normal-form syntax. | Defines the judgments used by expression typing. |
| `AlgorithmicNFSound` | Soundness of normal-form algorithmic subtyping. | Defined/proved. |
| `AlgorithmicNFMerge` | Normal-form joins and meets. | Defined/proved. |
| `AlgorithmicNFLubGlb` | LUB/GLB properties for normal-form joins and meets. | Defined/proved. |
| `AlgorithmicNFInference` | Decision procedures for normal-form subtyping. | Defined/proved. |
| `AlgorithmicNFComplete` | Completeness of normal-form algorithmic subtyping. | Defined/proved by relating the normal-form and original algorithms. |
| `AlgorithmicNFSubstitution` | Preservation of normal-form algorithmic subtyping by substitution. | Defined/proved. |
| `AlgorithmicNFMergeSubstitution` | Exact preservation of normal-form type/protocol joins and meets by substitution. | Constructively proved, including polarity changes caused by protocol substitution. |

## Expressions, typing, and structural lemmas

| Module | Main contents | Status and dependencies |
|---|---|---|
| `ExprSyntax` | Expressions, values, constants, and normal-form type annotations. | Expressions and values retain an explicit kind context; runtime parallelism and fresh channels are represented by `ProcSemanticsFresh.Conf`. |
| `ExprSubstitution` | Term renaming, term substitution, type renaming, and type substitution on expressions and values. | Defined; no typing claim is made here. |
| `ExprTypingStripFresh` | Constructive stripping of value, synthesis, and checking derivations to their consumed resource fragments. | Proved from the canonical removal destructors in `ExprContextProperties`. |
| `ExprTypeRenamingPreservationFresh` | Type-context renaming preservation for value, synthesis, and checking derivations. | Proved relative to accepted `Ext.ext` and `ProtocolConstructors`, without `Kits.Syntax._.~-ext`. |
| `ExprTypeSubstitutionPreservationFresh` | Type-context substitution preservation for value, synthesis, and checking derivations. | Complete constructive proof relative to accepted `Ext.ext` and `ProtocolConstructors`; its match case uses exact merge-substitution. |
| `ExprSubstitutionPreservationFresh` | Complete simultaneous and single expression substitution with context equivalence up to annotations on used entries. | Proved relative to the accepted foundations; includes residual tracking, binder lifting, all typing cases, inhabited exact and checked-value substitution statements, and the specialized variable substitution used by match reduction. |
| `ExprDoubleSubstitutionPreservationFresh` | Double linear expression substitution and two-binder strengthening. | Derived constructively from the trusted simultaneous theorem and context strengthening; contains no local postulates. |
| `ExprUnrestrictedSubstitutionPreservationFresh` | Unrestricted self-substitution for recursive unfolding. | Derived from the trusted simultaneous theorem; correctly permits the unfolded value to synthesize a proper subtype. |
| `ExprTypingUniquenessFresh` | Constructive uniqueness of synthesized kinds, types, and threaded output contexts. | Proved mutually for value, synthesis, and checking derivations. |
| `ExprReductionPreservationFresh` | Trusted expression reduction preservation using the fresh substitution interfaces. | Proves unconditional synthesis and checking preservation for every `L-β` head rule, every direct labelled head action (fork, new, receive, send, match, select, and close), and all eight evaluation-context closure rules. The result carries an actual reduct type below the source type and an actual leftover equivalent up to used annotations. |
| `ExprSemantics` | Labelled small-step expression semantics. | Defined over `ExprSyntax` and `ExprSubstitution`. |
| `ExprNormalTyping` | Linear/unrestricted/used bindings, threaded contexts, value typing, synthesis, checking, branch joins, and primitive types. | Central typing definition; depends on normal-form algorithmic subtyping and merge. Receive, select, and close consume raw `SLin` endpoints; select also returns its raw `SLin` continuation. |
| `ExprContextProperties` | `AllUsed`, linear disjointness, context frames/merges, removable subcontexts, and their algebra. | Defined/proved. This is the canonical home of `allUsedCtx`, unrestricted membership preservation, removal of all-used contexts, frame symmetry, and linear/unrestricted removal destructors. |
| `ExprContextShape` | The context-shape relation `~Ctx` and proofs that typing only changes live linear entries to used entries. | Defined/proved. |
| `ExprRenamingPreservation` | Context insertion, weakening, unweakening, and renaming preservation. | Defined/proved. The primitive receive/send/select cases are direct typing-constructor applications. |
| `ExprTypingInversion` | Constructor inversion, channel-subtyping inversion, select-application, and protocol-materialization lemmas. | Defined/proved relative to the accepted foundations. |
| `ExprTypingLeftover` | Existence of removable subcontexts corresponding to resources consumed by typing derivations. | Defined/proved; general constructive stripping lives in `ExprTypingStripFresh`. |
| `ExprTypingProperties` | Frame/replay lemmas saying a derivation can be replayed in a larger compatible context. | Defined/proved, including inversion of weakened frames and the mutual value/synthesis/checking replay family. |
| `ExprTypingStrengthening` | Context subtyping/strengthening and branch-coherence results. | Branch coherence uses an explicit nonempty-branch premise; branch-join and match-output monotonicity are proved from joins and constructor-signature variance. The general strengthening theorem is relative to `ProtocolConstructors`. |

## Expression substitution

The maintained substitution path is the fresh trusted development:

- `ExprTypeSubstitutionPreservationFresh` proves arbitrary normal-form type
  substitution and the single-substitution corollaries used by expression
  reduction;
- `ExprSubstitutionPreservationFresh` proves simultaneous and single term
  substitution with leftover equality up to used annotations;
- `ExprDoubleSubstitutionPreservationFresh` and
  `ExprUnrestrictedSubstitutionPreservationFresh` derive the let-pair and
  recursive-unfolding instances.

The shared `t-dual-preserves-≡c` lemma has its canonical home in
`SubstitutionSubtyping`; both the type-substitution proof and the preservation
support lemmas import it there.

## Context reduction and preservation

| Module | Main contents | Status and dependencies |
|---|---|---|
| `ExprContextReduction` | Pointwise context replacement, context reduction for expression labels, frame updates, label-resource descriptions, compatibility, and extraction. | Defined/proved relative to the accepted foundations. |
| `ExprPreservationStep2.ContextLemmas` | Removal, replacement, membership, and all-used helper lemmas. | Defined/proved under imported assumptions. |
| `ExprPreservationStep2.SubstitutionLemmas` | Variance-aware substitution and normalization bridges used in session action cases. | Defined/proved under imported assumptions. |
| `ExprPreservationStep2.MaterializeProperties` | Materialization/substitution equalities for protocol constructors and selected branches. | Defined/proved under `ProtocolConstructors` and substitution assumptions. |
| `ExprReductionPreservationFresh` | Expression reduction preservation with actual reduct types and leftovers related up to annotations on used bindings. | Constructively covers every expression reduction constructor relative only to the accepted foundations. |

## Process layer

| Module | Main contents | Status and dependencies |
|---|---|---|
| `ProcSemanticsFresh` | Flat configuration semantics over a list of expressions sharing one channel namespace and a finite set of live channel entries. | Contains no postulates. `Act-New` shifts existing liveness and inserts the new endpoint pair; message, branch, and wait synchronization require live endpoints. `Act-Wait` removes the closed endpoints from `live` while retaining their slots in the flat namespace. |
| `ProcExamplesFresh` | Flat-configuration operational examples. | Contains no postulates. It demonstrates beta at either list position, fork, fresh-pair activation, both endpoint orientations, a pair below two older slots, branch synchronization, and closing with liveness removal. |
| `ProcExamples` | Empty compatibility module. | Operational examples live in `ProcExamplesFresh`. |
| `ProcTypingFresh` | Declarative typing for flat configurations from `ProcSemanticsFresh`. | Contains no postulates. It reexports the canonical `ExprContextProperties.AllUsed` and defines the process-specific `Split`; `LiveCtx` equates live slots with available raw `SLin` bindings and dead slots with used bindings. The receive, select, and close primitive inputs use the same endpoint kind. `ThreadsTyped` splits live resources across the expression list and requires each assigned resource to be consumed exactly once. |
| `ProcProgressFresh` | Terminal, communication-deadlock, and progress predicates for flat configurations. | Contains no postulates or holes. `GlobalDeadlock` positively classifies all threads, requires at least one communication-blocked thread, and excludes both independent and synchronizing actions; `deadlock-cannot-step` proves that it is genuinely stuck. `configuration-progress` proves the global lifting theorem from the still-open local expression-progress theorem and finite action-decision procedures, all supplied as explicit arguments. |
| `ProcReductionPreservationFresh` | Configuration subject reduction built on `ExprReductionPreservationFresh`. | Contains no postulates or holes. Beta, fork, and new preserve typing unconditionally and at arbitrary list positions. Message, branch, and wait preserve typing under `BinaryCompatibility`, which supplies the endpoint/session coherence absent from `LiveCtx`; `ReductionTyping` distinguishes those typed synchronization steps from raw operational steps. The conclusion returns the actual target context and a fresh configuration-typing derivation. |

## Examples and maintained index

`Examples` contains small declarative subtyping examples, including examples
showing substitution through positive and negative protocol occurrences.

`README.agda` is the checked aggregate module. Its prose descriptions provide
a short linear index, while this document gives the dependency and proof-status
view. It directly lists the maintained context, fresh substitution,
fresh reduction, and preservation-support modules.

## Expression substitution and reduction preservation

The current approach replaces exact equality of leftover contexts by
the relation `_≈ᵘ_` from `ExprSubstitutionPreservationFresh`.  This relation
requires exact agreement on live linear and unrestricted entries and ignores
only the type annotations stored in `B-Used` entries.

The preservation records can accommodate this by returning the actual
type and leftover context:

```text
actual-type   : NfTy [] (KV pk m)
actual-output : Ctx [] (length Θ + n)
typing        : Γ₁ ⊢ e₂ ⇒ actual-type ⊣ actual-output
subtype       : actual-type <:ₜ U
leftover      : actual-output ≈ᵘ extendUsed Θ Γ₂
```

and analogously for checking.  The context step, frame update, compatibility,
and result-subtyping fields remain exact and do not need to be weakened.

This result shape fits the expression entry of fresh configuration typing:

```text
TT-∷ : Split Γ Γe Γrest
     → Γe ⊢ e ⇐ unit ⊣ Γe′
     → AllUsed Γe′
     → ThreadsTyped Γrest es
     → ThreadsTyped Γ (e ∷ es)
```

At the configuration layer, the same canonical `AllUsed` predicate is used
by expression and process typing.  The shared `allUsed-resp-≈ᵘ` lemma
therefore transfers all-used evidence directly, without a process-local copy
or conversion function.  Fresh channel extensions are handled directly by
the reduction-preservation construction.

Evaluation-context cases type an unchanged subexpression after the recursively
reduced subexpression.  They use a replay lemma saying that typing is invariant
under retagging entries that were already used before the derivation.  Plain
`_≈ᵘ_` is too weak to recover which used entries were inherited and which were
newly consumed, so the proof uses the strengthened four-context relation:

```text
RetaggedTransition Γin Γin′ Γout Γout′
```

which combines:

- `Γin ≈ᵘ Γin′`;
- the ordinary live-to-used shape change from `Γin` to `Γout`;
- preservation of the original live type when that entry is newly consumed;
- arbitrary retagging only at entries already used in `Γin`.

`retag-take-transition` proves the first nontrivial instance of this invariant
for linear variable consumption.  The central replay statements are proved
mutually for values, synthesis, and checking:

```text
Γin ⊢ e ⇒ T ⊣ Γout
→ RetaggedTransition Γin Γin′ Γout Γout′
→ Γin′ ⊢ e ⇒ T ⊣ Γout′
```

The full substitution induction also needs to commute the substitution value
past a suffix of the source derivation.  A second four-context relation,
`ReplayTransition`, permits an unused live resource in the old run to be
already used in the reordered run.  From a trusted `RemoveCtx` witness and a
trusted frame, `remove-frame-replay` constructs this transition.  The checked
exchange lemmas are:

```text
exchange-value-after-value
exchange-value-after-synth
exchange-check-after-synth
```

These transitions discharge the resource-ordering part of the full proof.

The type-directed strengthening infrastructure is constructive:

- branch outputs are coherent because typing shape plus context subtyping
  determines a unique output context;
- `BranchJoin⁺` is monotone by the least-upper-bound property of `joinₜ`;
- materialized match outputs are monotone by the variance certificate carried
  by each constructor signature.

The fresh module uses the general strengthening theorem relative to the
accepted `ProtocolConstructors` foundation and packages the needed instance
as `strengthen-substitution-binder`.

The exact intermediate statement,
`ExactExpressionSubstitutionPreservesTyping`, assumes that the replacement
value synthesizes exactly the binder type.  The theorem
`expression-substitution-from-exact` shows:

```text
ExpressionBinderStrengthening
→ ExactExpressionSubstitutionPreservesTyping
→ ExpressionSubstitutionPreservesTyping
```

Both statements are proved.  The mutual
`substitution-preserves-value/synth/check` induction carries a `Residual`
witness through each constructor.  Type abstraction lifts the substitution
relation structurally, using the accepted `Ext.ext` only for equality of the
underlying substitution functions.  Match branches are aligned with
`residual-target-unique`.  Finally,
`exact-expression-substitution-preserves-typing` instantiates the simultaneous
theorem with `singleSub`, and `expression-substitution-preserves-typing`
provides the full result.

## Trusted internal reduction preservation

`ExprReductionPreservationFresh` uses this substitution result in the
application beta case.  Its generic head theorem takes a proof of the type
alias:

```text
ExpressionSubstitutionPreservesTyping
```

The alias follows evaluation order:

```text
Γ₂ ⊢ value ⇐ binder-type ⊣ Γ₃
binder-type ∷ Γ₁ ⊢ body ⇒ body-type ⊣ used binder-type ∷ Γ₂
```

and returns a reduct that may synthesize a subtype of `body-type`.  This type
weakening is necessary: a value checked against the binder type may synthesize
a proper subtype.

That premise is supplied by
`ExprSubstitutionPreservationFresh.expression-substitution-preserves-typing`.

The direct `beta-preserves-synth/check` proof contains every `L-β` head rule:

- application beta, using the trusted expression-substitution theorem;
- let-pair elimination, using the trusted double linear substitution
  corollary;
- let-unit elimination, using the second typing premise directly;
- conversion of a value pair expression to a pair value.
- type application, recursive unfolding, receive/send specialization, and
  select specialization.

The mutual `beta-preserves-synth/check` theorem closes this head result under
all evaluation contexts.  Its match case uses branch strengthening and join
monotonicity; its let-pair case uses constructive two-binder strengthening.
Checking preservation composes the reduct/source subtyping proof with the
source checking derivation.

The unconditional `reduction-preserves-synth/check` layer additionally proves
every direct labelled head action: fork, new, receive-value, send-value,
match, select, and close.  The receive proof is constructive after aligning
`ReceiveTy` and `receiveNf` with the raw
`recvChanNf` channel kind: it inverts channel subtyping, advances the endpoint
  to its continuation, merges and replays the payload typing context, and
  types the reduct pair.

The send input uses the raw `sendChanNf` kind.  Its result uses `sessTyNf S`
consistently in both expression typing and context reduction.  The
constructive send proof uses fresh typing uniqueness to align
the payload-first expression derivation with the channel-first label
derivation, then advances and returns the endpoint.

Match preservation replaces the matched endpoint by the selected branch
continuation, retags that branch to the leftover produced by consuming the
updated endpoint, and applies the fresh specialized variable-substitution
theorem.  Exact preservation of the consumed binder annotation is exposed by
`retag-synth-input-lin-used`; the branch-join witness supplies the result
subtyping proof.  Select preservation extracts the label channel, identifies
its source type by linear-membership uniqueness, advances it with
`selectOutNf`, and uses `select-app-subtype`.  Close preservation uses
`end-subtype-invert` and the constructive `take-replace` lemma.

The same theorem propagates arbitrary observable actions through `Act-AppL`,
`Act-AppR`, `Act-TAppE`, `Act-PairL`, `Act-PairR`,
`Act-MatchE`, `Act-LetPairE`, and `Act-LetUnitE`.  Left contexts use trusted
renaming preservation to weaken typing by the label extension, including the
two fresh bindings introduced by `Act-New`.  Right contexts strip the leading
value with `ExprTypingStripFresh`, prove that its resources are disjoint from
the inner action, retag and replay it after the context update, and merge the
aligned frame effects.  Thus every expression transition constructor is
covered; process preservation is a separate theorem.

## Future investigation

- Prove the local expression canonical-forms/progress result needed to
  instantiate `ProcProgressFresh.configuration-progress` without external
  premises.
- Decide whether endpoint compatibility should become an invariant of
  configuration typing.  Doing so could internalize `BinaryCompatibility`
  and yield unconditional preservation for message, branch, and wait
  synchronization.
