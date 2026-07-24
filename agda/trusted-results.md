# Trusted results for expression substitution and preservation

Last audited: 2026-07-24.

This ledger covers the active dependency cone relevant to expression
substitution and expression reduction preservation.

Trust is tracked per declaration, not per import.  A declaration is trusted
when every non-constructive dependency is one of the accepted foundations
listed below.

## Accepted foundational assumptions

The following three postulates are accepted foundations.

- `TypesProtocolConstructors.ProtocolConstructors` supplies the signatures of
  abstract protocol constructors in place of a concrete syntax and semantics
  for those constructors.
- `Ext.ext` supplies ordinary function extensionality.
- `Kits.Syntax._.~-ext` supplies extensional equality for generalized
  renamings and substitutions from pointwise equality.

Results whose only non-constructive dependencies are drawn from this list are
called trusted below, relative to the accepted foundations.  In particular,
accepting `~-ext` makes the generic traversal congruence/composition library
and the binder cases of `Types.⋯-id` and `Types.fusion` trusted.  It does
not add any further assumptions.

## Trust closure

The active module graph contains only the three accepted postulates above.
Important dependency consequences are:

- the `Kits` extensional traversal lemmas, including `⋯-cong`, `⋯-id~`,
  `⋯-↑-wk`, `wk-cancels-⦅⦆-⋯`, and `dist-↑-⦅⦆-⋯`, are trusted relative
  to `~-ext`;
- `Types.⋯-id` and `Types.fusion` are trusted relative to `~-ext`, including
  their type-binder cases;
- `Duality.ext-dual-s-irrelevant`, `dual-irrelevant`, and
  `dual-all-irrelevant` are trusted relative to `Ext.ext`;
- consequently `Types.nf-idempotent`, `Types.nfp-idempotent`, and
  `Types.nf-sound-` are trusted relative to the accepted extensionality
  foundations.

## Trusted module-wide results

Every proof declaration in the following modules is trusted, with
protocol-related declarations interpreted relative to the accepted
`ProtocolConstructors` assumption.

- `Util`
- `Kinds`
- `Variance`
- `Kits`, relative to `Kits.Syntax._.~-ext`
- `Duality`, relative to `Ext.ext`
- `Types`, relative to `Ext.ext` and `Kits.Syntax._.~-ext`
- `TypesProperties`
- `TypesDecidable`
- `Subtyping`
- `SubtypingProperties`
- `SubstitutionSubtyping`
- `NormalTypes`
- `NormalTypesRenamings`
- `NormalTypesSubstitution`
- `AlgorithmicNFSubtyping`
- `AlgorithmicNFSubstitution`
- `AlgorithmicNFSound`
- `AlgorithmicNFMerge`
- `AlgorithmicNFLubGlb`
- `ExprSyntax`
- `ExprNormalTyping`, relative to `ProtocolConstructors`
- `ExprSemantics`
- `ExprSubstitution`
- `ExprContextProperties`
- `ExprContextReduction`, relative to the accepted foundations
- `ExprContextShape`
- `ExprTypingInversion`, relative to the accepted foundations
- `ExprTypingLeftover`
- `ExprTypingUniquenessFresh`, relative to `ProtocolConstructors`
- `ExprRenamingPreservation`
- `ExprTypingProperties`
- `ExprTypingStrengthening`, relative to `ProtocolConstructors`
- `ProcTypingFresh`
- `ProcProgressFreshDefinitions`
- `ProcLocalProgressFresh`
- `ProcProgressFreshDecidable`
- `ProcProgressFresh`
- `ProcSemanticsFresh`
- `ProcSemanticsPermutationFresh`
- `ProcExamples`
- `ProcExamplesFresh`
- `ExprActionResourcesFresh`
- `ProcReductionPreservationFresh`
- `ProcSafetyFresh`
- `ExprTypingStripFresh`
- `ExprPreservationStep2.ContextLemmas`
- `ExprPreservationStep2.SubstitutionLemmas`, relative to the accepted
  foundations
- `ExprPreservationStep2.MaterializeProperties`, relative to the accepted
  foundations

Preservation-relevant highlights are:

- `ProcTypingFresh`: the flat-configuration judgment reuses the canonical
  polymorphic `ExprContextProperties.AllUsed` predicate and defines its own
  process-specific `Split`.  Fresh progress and preservation consume these
  definitions directly.

- `ProcProgressFreshDefinitions` collects the predicates shared by local and
  global progress, including `SessionCtx`, `LocalProgress`,
  `SynchronizationPossible`, `GlobalDeadlock`, and the theorem signatures.

- `ProcLocalProgressFresh.local-progress` proves the local canonical-forms
  theorem for an expression typed in a session-only run-time context.  Every
  such expression is a value, can take an independent beta/fork/new action,
  or exposes a message, branch, or close communication action.

- `ProcProgressFreshDecidable.runnable-at?` decides whether some thread has
  an independent action.  `synchronization-possible?` decides whether two
  distinct threads can synchronize on live endpoints forming a fresh pair;
  its finite search covers message, branch, and close synchronization.
  `terminal?` and `global-deadlock?` directly decide the two non-stepping
  outcomes; the latter constructively decides incoming and outgoing
  communication for arbitrary expressions before checking quiescence,
  blocked communication, and absence of global actions.

- `ProcSemanticsPermutationFresh` contains no postulates or holes.
  `step-resp-≈ᶜ` transports every configuration transition across a
  permutation of the thread list and returns a matching target
  configuration; `typing-resp-≈ᶜ` transports configuration typing while
  retaining both `LiveCtx` and `PairedCtx`.

- `ProcProgressFresh`: `Terminal` says that every thread is an expression
  value.  `GlobalDeadlock` positively records that every thread is a value or
  has an observable communication transition, that at least one thread is
  communication-blocked, and that no live peer endpoints can synchronize.
  `deadlock-cannot-step` proves that this characterization excludes every
  configuration transition.  The assumption-free `configuration-progress`
  combines `local-progress`, `runnable-at?`, and
  `synchronization-possible?` to establish the terminal / deadlock / step
  trichotomy.

- `ExprContextProperties`: `AllUsed`, `LinearDisjoint`, `FrameCtx`,
  `RemoveCtx`, `allUsedCtx`, `allUsedCtx-∋ᵘ`, `remove-allUsedCtx`,
  `strip-rm-lin`, `strip-rm-un`, `frame-sym`, `remove-unique`, the merge and
  remove composition lemmas, and the disjointness lemmas.
- `ExprContextShape`: `_~Ctx_`, `drop-lin-used`, and
  `value-preserves-~Ctx`, `synth-preserves-~Ctx`, and
  `check-preserves-~Ctx`.
- `ExprRenamingPreservation`: insertion at an arbitrary term-variable
  position, `ren-preserves-value/synth/check`, and
  `wk-preserves-value/synth/check`.
- `ExprTypingProperties`: frame uniqueness, frame/replay for value,
  synthesis, and checking derivations, and the all-used replay variants.
- `ExprTypingUniquenessFresh`: constructive kind, type, and output-context
  uniqueness for value, synthesis, and checking derivations.  Its match case
  uses trusted branch-join monotonicity and normal-form subtyping
  antisymmetry.
- `ExprTypingStripFresh`: `allUsed-shape-stable`,
  `shape-allUsed-output`, `wk-remove`, `wk-allUsedCtx`, and the constructive
  mutual `strip-value/synth/check`.  It consumes the canonical membership and
  removal destructors from `ExprContextProperties`.

The overlap cleanup gives the following small shared results one canonical
home: dependent two-argument extensionality and `just` injectivity in `Util`;
session-dual congruence in `SubstitutionSubtyping`; `tailSub` cancellation for
`singleSub` in `ExprSubstitutionPreservationFresh`; and namespace weakening
in `ExprSemantics`.  The algorithmic and normal-form algorithmic families are
still intentionally separate because they operate on different syntax.

## Trusted declaration details

### Syntax, typing, and reduction

The datatypes and constructors in `ExprSyntax`, `ExprNormalTyping`, and
`ExprSemantics` are trusted foundational declarations.  This includes all
expression/value constructors, contexts and bindings, variable lookup and
take judgments, typing judgments, labels, and reduction rules.

The following `ExprNormalTyping` computations and structural results are also
trusted:

- `normalizeTy` and `normalProtoOf`; the former identity wrapper
  `normalTyOf` has been eliminated from statements and proofs;
- `wkNfTy`, `wkBinding`, `wkCtx` and their injectivity lemmas;
- `linArrNf`, `unArrNf`, `pairNf`, `polyNf`;
- receive, send, select, materialization, and match branch type
  computations, relative to `ProtocolConstructors`; `ReceiveTy`/`receiveNf`,
  `SelectTy`/`selectNf`, and `CloseTy`/`closeConstNf` take raw `SLin`
  endpoints as their linear-arrow inputs, and select returns its raw `SLin`
  continuation;
- `pair-injective`, `nfTyEq`, `nfEq`, and the normal-form constructor
  injectivity lemmas, including the generalized `linArrNf-injective` for
  arbitrary value prekind and multiplicity at both ends of an arrow.

`normalizeTy-id` is trusted relative to `Ext.ext`: it calls
`Types.nf-idempotent` or `Types.nfp-idempotent`.

The term-level definitions in `ExprSubstitution` are trusted:

- `Ren`, `Sub`, `extRen`, `extRen2`, `renameValue`, `renameExpr`, `wkValue`;
- `extSub`, `extSub2`, `singleSub`, `doubleSub`, `liftTySub`;
- `substValueWith`, `substExprWith`, `substValue`, `substExpr`, and
  `substExpr₂`.

These are syntax transformations, not typing-preservation proofs.

From `AlgorithmicNFSubtyping`, the judgment constructors and the structural
proofs `<:ₜ-refl` and `<:ₜ-trans` are trusted.  The normal-form
substitution-preservation proof used by strengthening is structurally
recursive and does not require assumptions beyond the accepted foundations.

### Context reduction

All declarations in `ExprContextReduction` are trusted.  In particular,
`ReplaceAt`, `replace-at`, the proved replacement/disjointness lemmas,
`extendUsed`, the context/frame/label relations, `Compatible`,
`InputCompatible`, `Extract`, and the extraction lemmas are available.

### Leftovers and inversion

All remaining declarations in `ExprTypingLeftover` are trusted.  They include:

- `remove-compose-frame`, derived from the canonical
  `mergeRemoveContext` and `frame-sym`;
- `strip-wk`;
- `used-head`, `used-tail`, `lin-tail`, `lin-tail′`, `un-tail`,
  `un-result`;
- `leftover-take`, `strip-take`;
- `leftover-value`, `leftover-synth`, `leftover-check`.

The general constructive stripping theorem is `ExprTypingStripFresh`.

Every remaining declaration in `ExprTypingInversion` is trusted.  The
canonical `tv-*` family covers constants, variables, abstraction, recursion,
type abstraction, pairs, receive, send, and select.  In particular,
`tv-receive₂-inversion` derives `W ≡ receiveNf T S` with the receive
channel at raw `SLin`, without a `sessTyNf` wrapper.  The module also retains
the select shape needed by `select-app-subtype`, structural
`recvChan-subtype`/`sendChan-subtype` inversions, and the generalized
materialization lemmas relative to `ProtocolConstructors`.  Redundant closed
specializations are kept out of this module in favor of the generalized
inversions.

### Strengthening

`ExprTypingStrengthening` contains no local postulates.  Its context
subtyping relation and structural lemmas, subtyping inversion, checking
subsumption, branch coherence, `match-output-subtype`, and the mutual
`strengthen-value/synth/check` proof are trusted relative to
`ProtocolConstructors`.

Consequently
`ExprSubstitutionPreservationFresh.strengthen-substitution-binder` is a
trusted implementation of `ExpressionBinderStrengthening`.

## Fresh substitution development

`ExprSubstitutionPreservationFresh` contains no postulates or holes.  It uses
the accepted `Ext.ext` for function equalities needed by structural type
lifting, and otherwise relies only on the trusted results recorded above.
The following groups are trusted relative to the accepted foundations:

- used-annotation equivalence: `_≈ᵘ_`,
  `≈ᵘ-refl`, `≈ᵘ-sym`, `≈ᵘ-trans`, and `used-head-≈ᵘ`;
- retag/replay: `RetaggedTransition`, `ReplayTransition`, their uniqueness,
  weakening, splitting, lookup, and typing replay lemmas, including the exact
  consumed-head interface `retag-synth-input-lin-used`;
- resource exchange: `remove-to-frame`, `remove-frame-replay`, and the three
  `exchange-*-after-*` lemmas;
- simultaneous substitutions: `_⊢σ_∶_⊣_`, `Residual`,
  `residual-refl`, `residual-target-unique`, and `residual-compose`;
- type-binder and relation infrastructure: `renTy-rename-value`,
  `renTy-rename-expr`, `wkTy-wkValue`, `lift-substitution-relation`,
  `lift-residual`, `advance-substitution`, and
  `allUsed-substitution-target`;
- relation construction and lookup: `identity-substitution-canonical`,
  `tail-singleSub-identitySub`, `single-substitution-relation`, the
  binder-extension lemmas, `substitution-lookup-lin`, and
  `substitution-lookup-un`;
- the mutual simultaneous-substitution proof:
  `substitution-preserves-value`, `substitution-preserves-synth`,
  `substitution-preserves-check`, and the linear-body helpers;
- result records and bridges: `SynthResult`, `CheckResult`,
  `BinderStrengtheningResult`, `strengthen-substitution-binder`,
  `substitution-variable-base`, `expression-substitution-from-exact`, and
  `expression-substitution-from-exact-trusted`;
- specialized variable substitution: `shape-allUsed-frame`,
  `identity-shape-advance`, and `variable-substitution-preserves-synth`, used
  to substitute an existing linear variable into a branch whose binder is
  known to be consumed.

`ExpressionSubstitutionPreservesTyping` and
`ExactExpressionSubstitutionPreservesTyping` are inhabited respectively by
`expression-substitution-preserves-typing` and
`exact-expression-substitution-preserves-typing`.  Thus the full expression
substitution theorem is complete.

`ExprDoubleSubstitutionPreservationFresh` contains no postulates or holes and
uses only the trusted simultaneous-substitution infrastructure above.  The
following declarations are trusted:

- `tail-doubleSub-singleSub` (the shared
  `tail-singleSub-identitySub` lemma is imported from the simultaneous
  substitution module);
- `double-substitution-relation`;
- `DoubleExpressionSubstitutionPreservesTyping` and its inhabitant
  `double-expression-substitution-preserves-typing`.
- `DoubleBinderStrengtheningResult` and `strengthen-double-binder`, the
  constructive two-binder strengthening used by let-pair context closure.

`ExprUnrestrictedSubstitutionPreservationFresh` contains no postulates or
holes.  It constructs the unrestricted self-substitution relation needed for
recursive unfolding and proves `recursive-unfolding-preserves-value` and
`recursive-unfolding-preserves-typing`.  The result deliberately permits the
unfolded body to synthesize a proper subtype of its recursive annotation.

### Type renaming

`ExprTypeRenamingPreservationFresh` has no local postulate.  It uses
structural congruence proofs for expression traversal and accepted `Ext.ext`
through normalization:

```text
wkTy-preserves-value/synth/check
  -> ren-preserves-value/synth/check
  -> normalization/materialization or T-TApp renaming lemmas
  -> ren-normalizeTy / ren-normalizeProto / ren-normalizeTy-minus
  -> Types.nf-idempotent / Types.nfp-idempotent / Types.nf-sound-
  -> Duality.dual-all-irrelevant / ext-dual-s-irrelevant
  -> Ext.ext (accepted)
```

Therefore its structural renaming lemmas, normalization and constructor
naturality lemmas, public `ren-preserves-value/synth/check` theorem, and
`wkTy-preserves-value/synth/check` corollaries are trusted relative to
`Ext.ext` and `ProtocolConstructors`.  The module does not depend on `~-ext`.

### Type substitution

`AlgorithmicNFMergeSubstitution` contains no postulates, holes, or termination
pragmas.  Its mutually recursive `joinₜ-subst`, `meetₜ-subst`,
`joinₚ′-subst`, `meetₚ′-subst`, `mergeₚ-join-subst`, and
`mergeₚ-meet-subst` proofs show that exact algorithmic join and meet results
are preserved by arbitrary normal-form substitutions.  The proof explicitly
handles protocol polarity changes caused by substituting a protocol variable
with a negative normal form.  These declarations depend only on the trusted
normal-form substitution, subtyping, merge, LUB/GLB, and antisymmetry results.

`ExprTypeSubstitutionPreservationFresh` contains a complete constructive
proof of type substitution preservation.  In particular, the following are
trusted relative to `Ext.ext`, `Kits.Syntax._.~-ext`, and
`ProtocolConstructors` (the `~-ext` dependency is inherited through the
normal-type substitution soundness lemmas):

- the context, lookup, take, constant, constructor, materialization, and
  type-application substitution lemmas;
- `BranchJoin⁺-subst`, obtained from `joinₜ-subst`;
- `trustedBranchJoinSubstitution` and `trustedSubstitutionAlgebra`;
- the mutual normal-substitution theorem
  `substNF-preserves-value/synth/check` for arbitrary `NFSub`;
- the single type-substitution corollaries
  `substTy-preserves-value/synth/check`, stated for the existing
  `substTyValue` and `substTyExpr` syntax operations;
- `cancel-single-wk-binding`, `cancel-single-wk-ctx`, and
  `substTy-preserves-wk-value`, which discharge the context cancellation
  required by `Act-TApp`.

## Fresh reduction development

Every declaration currently present in `ExprReductionPreservationFresh` is
trusted:

- pointwise-identity renaming preservation and its zero-weakening
  corollaries;
- `beta-preserves-synth`, `beta-preserves-check`, and the public aliases
  `beta-reduction-preserves-synth/check`;
- the generalized `ReductionSynthResult` and `ReductionCheckResult`
  declarations;
- `new-dual-substitution`, relating normalization of a dual session type to
  normal-form dual substitution;
- `linear-membership-type`, together with the imported canonical
  `ExprTypingUniquenessFresh.take-membership-fresh`, recovers the unique
  normal type stored at a linear variable position;
- `replace-take-fresh`, which replays a linear take after replacing that
  position by its receive continuation and relates the two leftovers by
  `_≈ᵘ_`;
- `recv-payload-replace-≈ᵘ`, which shows that replacing the already-used
  channel position in the payload context changes only a used annotation;
- `send-remove-membership-fresh`, which removes the send-label input while
  retaining the consumed channel as a live member of the remainder;
- `remove-to-rest-frame`, which turns that removal into the frame orientation
  needed to replay the payload derivation;
- `reduction-preserves-synth/check`, covering every beta reduction and every
  direct labelled head step: `Act-Fork`, `Act-New`, `Act-Rcv`, `Act-Send`,
  `Act-Match`, `Act-Sel`, and `Act-Close`, and recursively propagating any
  observable step through `Act-AppL`, `Act-AppR`,
  `Act-TAppE`, `Act-PairL`, `Act-PairR`, `Act-MatchE`, `Act-LetPairE`, and
  `Act-LetUnitE`.

The beta theorem uses the completed trusted expression-substitution proof
directly.  Its head-rule clauses cover every constructor labelled `L-β`:

- `Act-App`, using
  `expression-substitution-preserves-typing`;
- `Act-LetPair`, using
  `double-expression-substitution-preserves-typing`;
- `Act-LetUnit`, constructively;
- `Act-PairV`, constructively;
- `Act-TApp`, using trusted type substitution and weakening cancellation;
- `Act-Rec`, using trusted unrestricted self-substitution and arrow
  strengthening;
- `Act-Receive₁/₂`, `Act-Send₁/₂`, and `Act-Select₁/₂`, using
  trusted primitive type computations.

The mutually recursive `beta-preserves-synth/check` theorem additionally
covers every evaluation-context constructor: `Act-AppL/R`, `Act-TAppE`,
`Act-PairL/R`, `Act-MatchE`, `Act-LetPairE`, and `Act-LetUnitE`.  Match closure
uses trusted branch strengthening and join monotonicity.  Let-pair closure uses
the trusted two-binder strengthening theorem.  Its conclusion retains the
actual reduct subtype and `_≈ᵘ_` leftover required by expression substitution.

The generalized result records handle reducts of arity `length Θ + n`, carry
the source/frame/context transitions and their `Compatible` witness, and keep
the actual leftover related to `extendUsed Θ Γ₂` by `_≈ᵘ_`.  The trusted
`Act-Fork` case uses `ExprTypingStripFresh.strip-value` to isolate exactly the
resources consumed by the forked value, constructs `Ctx-Fork` and `Frm-Fork`,
and types the unit reduct.

The trusted `Act-New` case handles its arity increase directly.  It extends
the active context by the fresh session endpoint and its dual, types
`freshPair` by consuming both endpoints, constructs `Ctx-New` and `Frm-New`,
and relates the synthesized pair type to the instantiated type of `C-New`.
The only non-structural equality needed is `new-dual-substitution`, derived
from trusted normalization results relative to the accepted extensionality
foundations.

The `S-Rcv` case is constructive and non-vacuous.  `ReceiveTy`/`receiveNf`
align the expression-level receive argument with the
raw `recvChanNf T S` required by `Label-RecvVal`, `Ctx-Rcv`, and
`Ex-RecvVal`.  The proof:

1. extracts the label's channel membership into the source context and uses
   `linear-membership-type` to identify it with the type synthesized by the
   source variable;
2. applies `recvChan-subtype` to obtain payload and continuation subtyping;
3. replaces the source channel by `S`, transports the corresponding frame
   replacement, and merges the payload resources with the updated channel
   context;
4. retags and replays the payload value derivation in that merged context;
5. types the reduct pair and relates its leftover to the source leftover by
   `_≈ᵘ_`.

The `S-Send` case is also constructive.  Its input convention is uniform:
`sendNf`, `Label-SendVal`, `Ctx-Send`, and `Ex-SendVal` all use the raw
`sendChanNf T S : SLin`.  Both `sendNf` and the replacement performed by
`Ctx-Send` produce the raw continuation `S`.  The label and context
relations permit a synthesized payload subtype of the message payload type.

The proof removes the label input, replays its payload derivation in the
source context, and uses `ExprTypingUniquenessFresh.value-output-unique` to
align that result with the payload-first source pair derivation.  It then
inverts `sendChanNf` subtyping, advances the channel to `S`, builds
the context and frame reductions, and types the reduct variable.  The changed
used annotation is accounted for by `_≈ᵘ_`.

The `S-Match` case advances the matched channel with `Ctx-Match`, retags the
selected branch from the scrutinee leftover to the updated channel leftover,
and applies `variable-substitution-preserves-synth`.  The supporting
`retag-synth-input-lin-used` lemma retains the exact annotation on the
consumed branch binder; `match-branch-subtype` obtains the reduct/source
subtyping proof from the branch join.

The `S-Sel` case extracts the label channel into the source context, uses
`linear-membership-type` to align it with the expression argument, advances
it to `selectOutNf`, and derives result subtyping with
`select-set-app-subtype` for the selector's actual protocol subset.  The
`S-Close` case uses `end-subtype-invert`,
`take-replace`, and the corresponding all-used-context lemmas to consume the
endpoint and type the unit reduct.  The selected and closed endpoints have
kind `SLin`, matching `ProcTypingFresh.LiveCtx`.  Both cases are
constructive.

Observable evaluation-context propagation is also constructive.  The
left-hand contexts use weakening by the complete label extension `Θ`, proved
from `ExprRenamingPreservation` both at top level and underneath one or two
term binders.  `Act-MatchE` then reuses trusted branch strengthening, and
`Act-LetPairE` reuses trusted double-binder strengthening.

The `Act-AppR` and `Act-PairR` cases use
`ExprTypingStripFresh.strip-value` to isolate the resources consumed by the
already-evaluated left value.  Structural live-channel lemmas show that this
fragment is disjoint from the observable inner step.  The proof records that
the active context step and inactive frame update perform the same concrete
replacement effect, retags and replays the left value across that update, and
merges the two frame transitions.  The explicit effect agreement keeps the
newly consumed live type exact while permitting annotations on entries that
were already used to differ.

## Reduction-preservation status

The fresh expression theorem covers every constructor of the expression
reduction relation: all internal `L-β` heads, all direct observable heads, and
all eight evaluation-context transitions.  Resource evidence is
action-specific.  Ordinary actions retain the linear-disjointness premise,
while `L-SendVal` uses the exact `SendValueResources` decomposition inferred
from the source typing derivation and transition.  This admits linear
payloads without asserting that the sender is disjoint from its own payload.
At the configuration layer, `ProcReductionPreservationFresh` proves:

- permutation invariance of declarative `ThreadsTyped` pools and the
  structural split/reassociation lemmas needed to select arbitrary entries;
- unconditional preservation for `Act-Beta`, `Act-Fork`, and `Act-New`;
- reconstruction of the forked application typing from arrow-subtyping
  inversion, and weakening/used-slot framing of every passive thread under
  `Act-New`;
- preservation of the new `PairedCtx` invariant by `Act-New`, using the
  trusted normalization bridge `SessionTypeDuality.normalize-dual`;
- normalized session duality involution,
  `NormalTypesSubstitution.dualNFKind-involutive`;
- `paired-live-endpoints`, which derives the two dual typed memberships for
  either orientation of any live `FinFreshPair`;
- constructive receive/send action-resource extraction in
  `ExprActionResourcesFresh`, including channel-first reordering of a send
  and payload subtyping through every evaluation context;
- `target-split-reconstruction`, which transfers the payload fragment from
  the sender allocation to the receiver allocation and reconstructs both
  nested target splits after the two continuation-endpoint replacements; it
  also returns those sequential global `ReplaceAt` witnesses;
- `live-replace-pair-live` and `live-replace-pair-dead`, which respectively
  preserve the live set across endpoint advancement and remove both endpoints
  from it during closing;
- `paired-replace-pair-live` and `paired-replace-pair-dead`, which preserve
  `PairedCtx` across either orientation of a live or closed `FinFreshPair`;
- unconditional preservation for `Act-Msg`, `Act-Bra`, and `Act-Wait`;
- the public `configuration-reduction-preserves-typing` theorem for every
  constructor of `ProcSemanticsFresh`, requiring only a source configuration
  typing derivation and the reduction derivation.

Endpoint compatibility is no longer missing from configuration typing:
`ProcTypingFresh.PairedCtx` relates every allocated pair by normalized
duality, and `SessionTypeDuality` proves the receive/send head equations used
to expose compatible payload and continuation components.

The invalid sender-side whole-context disjointness premise is absent.
`Act-Msg` instead uses `SendValueResources` to transfer exactly the payload
fragment to the receiver before reconstructing the two target splits.
`Act-Bra` extracts a `SendLabelResources` witness whose protocol subset may
contain labels other than the chosen label, then derives dual continuation
types from `PairedCtx`.  `Act-Wait` reconstructs both used endpoint slots.
Each case feeds the resulting endpoint replacements to the proved `LiveCtx`
and `PairedCtx` transports.  The former `BinaryCompatibility` and
`ReductionTyping` wrappers have therefore been removed.

`ProcSafetyFresh` closes the preservation/progress loop.  Its heterogeneous
finite-trace relation accommodates the two endpoint slots introduced by every
`Act-New` step.  `finite-reduction-preserves-typing` iterates configuration
preservation over such traces, and `finite-reduction-progress` applies global
progress at their endpoints.  The public `closed-unit-finite-progress`
theorem constructs the empty-live, singleton configuration from a closed
unit-checking derivation and proves that every finitely reachable
configuration is terminal, globally deadlocked, or can step.

## Verification status

At this audit point the following commands succeed:

```text
agda -i . ExprTypingStripFresh.agda
agda -i . ExprTypingUniquenessFresh.agda
agda -i . ExprTypeRenamingPreservationFresh.agda
agda -i . AlgorithmicNFMergeSubstitution.agda
agda -i . ExprTypeSubstitutionPreservationFresh.agda
agda -i . ExprSubstitutionPreservationFresh.agda
agda -i . ExprDoubleSubstitutionPreservationFresh.agda
agda -i . ExprUnrestrictedSubstitutionPreservationFresh.agda
agda -i . SessionTypeDuality.agda
agda -i . ExprActionResourcesFresh.agda
agda -i . ExprReductionPreservationFresh.agda
agda -i . ProcExamplesFresh.agda
agda -i . ProcLocalProgressFresh.agda
agda -i . ProcProgressFreshDecidable.agda
agda -i . ProcProgressFresh.agda
agda -i . ProcSemanticsPermutationFresh.agda
agda -i . ProcReductionPreservationFresh.agda
agda -i . ProcSafetyFresh.agda
agda -i . README.agda
```

Successful type checking establishes that the files are internally well
typed; the declaration-level dependency audit above is what distinguishes
compiled proofs from trusted proofs.
