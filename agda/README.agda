module README where

-- Basic extensionality and helper lemmas
-- used throughout the development.
import Ext

-- Small general-purpose utilities and arithmetic/order
-- lemmas.
import Util

-- Kinds, prekinds, multiplicities, and their
-- decidable equalities.
import Kinds

-- Variance markers and algebra for positive,
-- negative, and invariant protocol positions.
import Variance

-- Duality infrastructure for session-like structure
-- on types and protocols.
import Duality

-- Generic renaming and substitution
-- kits.
import Kits

-- Core abstract syntax of kinds-indexed types
-- and their normal forms.
import Types

-- Structural properties of type renaming,
-- including injective renamings.
import TypesProperties

-- Decidable equality for types and
-- related syntax.
import TypesDecidable

-- Protocol constructor signatures and materialization
-- operations derived from variance information.
import TypesProtocolConstructors

-- Worked examples for protocol constructor signatures
-- and their selected branch types.
import TypesProtocolConstructorsExamples

-- Normal-form syntax for types and protocols,
-- separated from raw type syntax.
import NormalTypes

-- Renaming operations on normal forms together
-- with their soundness lemmas.
import NormalTypesRenamings

-- Substitution operations on normal forms and
-- bridges back to normalized raw types.
import NormalTypesSubstitution

-- Declarative subtyping and conversion
-- relations.
import Subtyping

-- Size lemmas for subtyping derivations
-- and normal forms.
import SubtypingSize

-- Structural properties of subtyping, especially
-- size preservation.
import SubtypingProperties

-- Preservation of subtyping and conversion
-- under substitution.
import SubstitutionSubtyping

-- Abstract syntax of expressions and values
-- from Section 4.
import ExprSyntax

-- Renaming and substitution operations
-- for expressions and values.
import ExprSubstitution

-- Small-step labelled semantics for expressions
-- and their observable actions.
import ExprSemantics

-- Renaming preservation for expressions and values
-- under context extension.
import ExprRenamingPreservation

-- Constructive type-renaming algebra for normalized constructor types
-- and injective-renaming preservation of branch joins.
import ExprTypeRenamingPreservationFresh

-- Constructive type-substitution preservation for expression
-- value, synthesis, and checking derivations.
import ExprTypeSubstitutionPreservationFresh

-- Complete fresh proof of expression substitution preservation
-- using equality only up to annotations on already-used bindings.
import ExprSubstitutionPreservationFresh

-- Trusted double linear substitution derived from
-- the fresh simultaneous-substitution theorem.
import ExprDoubleSubstitutionPreservationFresh

-- Trusted unrestricted self-substitution for recursive values,
-- derived from the fresh simultaneous-substitution theorem.
import ExprUnrestrictedSubstitutionPreservationFresh

-- Constructive receive/send action-resource extraction through all
-- observable evaluation contexts, including linear send payloads.
import ExprActionResourcesFresh

-- Trusted preservation for all expression head actions and
-- their propagation using action-specific resource evidence.
import ExprReductionPreservationFresh

-- Algorithmic subtyping on declarative normal forms,
-- predating the separate normal-form syntax.
import AlgorithmicSubtyping

-- Soundness of the original algorithmic subtyping
-- judgments with respect to declarative subtyping.
import AlgorithmicSound

-- Decidable joins and meets for the original
-- algorithmic subtyping system.
import AlgorithmicMerge

-- Least upper bounds and greatest lower bounds
-- derived from original joins and meets.
import AlgorithmicLubGlb

-- Decision procedures for the original
-- algorithmic subtyping judgments.
import AlgorithmicInference

-- Completeness of the original algorithmic system
-- with respect to declarative subtyping.
import AlgorithmicComplete

-- Preservation of original algorithmic subtyping
-- under type substitution.
import AlgorithmicSubstitution

-- Algorithmic subtyping on normal forms.
-- The normal-form variant feeds the later typing and preservation proofs.
import AlgorithmicNFSubtyping

-- Soundness of the algorithmic subtyping
-- judgments.
import AlgorithmicNFSound

-- Decidable joins and meets for
-- algorithmic subtyping.
import AlgorithmicNFMerge

-- Least upper bounds and greatest lower bounds
-- derived from joins and meets.
import AlgorithmicNFLubGlb

-- Decision procedures for algorithmic
-- subtyping judgments.
import AlgorithmicNFInference

-- Completeness of the algorithmic system with
-- respect to declarative subtyping.
import AlgorithmicNFComplete

-- Preservation of algorithmic subtyping
-- under type substitution.
import AlgorithmicNFSubstitution

-- Exact preservation of normal-form joins and meets
-- under normal-form type substitution.
import AlgorithmicNFMergeSubstitution

-- Algorithmic expression typing with normalized environments,
-- result types, and primitives over raw session endpoints.
import ExprNormalTyping

-- Normalization bridges and communication-head laws for dual session
-- endpoint types; general dual involution lives with normal substitution.
import SessionTypeDuality

-- Structural context relations for all-used, disjoint,
-- framed, and removable resource contexts.
import ExprContextProperties

-- Shape preservation for threaded typing contexts,
-- tracking live entries that become used.
import ExprContextShape

-- Constructive uniqueness of synthesized kinds, types, and output contexts
-- for value, synthesis, and checking derivations.
import ExprTypingUniquenessFresh

-- Constructive inversion and shape lemmas for expression typing
-- derivations and primitive typing forms.
import ExprTypingInversion

-- Constructive labelled reduction of full typing contexts
-- for expression actions.
import ExprContextReduction

-- Flat configuration semantics tracking live channel entries, with direct
-- synchronization between distinct threads on live paired endpoints.
import ProcSemanticsFresh

-- Equivariance of flat-configuration reduction and process typing under
-- standard-library list permutations, with matching target configurations.
import ProcSemanticsPermutationFresh

-- Flat-configuration reconstructions of the process examples, covering
-- indexed internal steps, fresh pairs, symmetric communication, and closing.
import ProcExamplesFresh

-- Compatibility module with no active declarations;
-- operational process examples are indexed above.
import ProcExamples

-- Constructive existence of removed subcontexts corresponding
-- to leftover typing contexts.
import ExprTypingLeftover

-- Constructive minimal-resource extraction for value, synthesis,
-- and checking derivations from canonical context-removal lemmas.
import ExprTypingStripFresh

-- Frame and replay lemmas for leftover contexts
-- used by the preservation development.
import ExprTypingProperties

-- Context strengthening for expression typing,
-- including subcontext and merge lemmas.
import ExprTypingStrengthening

-- Context and extraction lemmas factored out of the preservation proof.
-- These helpers organize RemoveCtx, ReplaceAt, and all-used context arguments.
import ExprPreservationStep2.ContextLemmas

-- Substitution and materialization lemmas factored out of the preservation proof.
-- These helpers package variance-aware substitution relations and normalization bridges.
import ExprPreservationStep2.SubstitutionLemmas

-- Materialization and substitution properties for protocol
-- constructors used by the preservation action cases.
import ExprPreservationStep2.MaterializeProperties

-- Declarative typing of flat configurations with live/dead consistency,
-- dual fresh-pair coherence, and exact linear resource allocation.
import ProcTypingFresh

-- Shared local/global progress predicates, session-only contexts,
-- and the terminal/deadlock/step trichotomy for flat configurations.
import ProcProgressFreshDefinitions

-- Canonical-forms and local progress for expressions typed in
-- session-only run-time contexts.
import ProcLocalProgressFresh

-- Constructive decisions for terminal states, global deadlocks, independent
-- expression actions, and compatible live-endpoint synchronization.
import ProcProgressFreshDecidable

-- Terminal, communication-deadlock, and stepping predicates for flat
-- configurations, with an assumption-free global progress theorem.
import ProcProgressFresh

-- Unconditional preservation of flat-configuration typing, using constructive
-- action resources, target splits, and live/paired invariant transports.
import ProcReductionPreservationFresh

-- Finite-trace preservation and the end-to-end terminal/deadlock/step
-- theorem for a singleton closed unit-typed initial configuration.
import ProcSafetyFresh

-- Small example developments exercising
-- the formalization.
import Examples
