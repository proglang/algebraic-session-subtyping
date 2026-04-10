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

-- Abstract syntax of expressions and
-- processes from Section 4.
import ExprSyntax

-- Renaming and substitution operations
-- for expressions and values.
import ExprSubstitution

-- Small-step labelled semantics for expressions
-- and their observable actions.
import ExprSemantics

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

-- Algorithmic expression typing with normalized
-- environments and result types.
import ExprNormalTyping

-- Labelled reduction of full typing contexts
-- for expression actions.
import ExprContextReduction

-- Labelled transition system for
-- processes.
import ProcSemantics

-- Context reduction for process labels, extending
-- expression context reduction.
import ProcContextReduction

-- Preservation interfaces for term and type
-- substitution on typed expressions.
import ExprSubstitutionTyping

-- Existence of removed subcontexts corresponding
-- to leftover typing contexts.
import ExprTypingLeftover

-- Frame and replay lemmas for leftover contexts
-- used by the preservation development.
import ExprTypingProperties

-- Context strengthening for expression typing,
-- including subcontext and merge lemmas.
import ExprTypingStrengthening

-- Original single-module preservation proof for
-- expression reduction steps.
import ExprPreservationStep

-- Context and extraction lemmas factored out
-- of the preservation proof.
-- These helpers organize RemoveCtx, ReplaceAt, and all-used context arguments.
import ExprPreservationStep2.ContextLemmas

-- Substitution and materialization lemmas factored
-- out of the preservation proof.
-- These helpers package variance-aware substitution relations and normalization bridges.
import ExprPreservationStep2.SubstitutionLemmas

-- Revised preservation setup using removable frames
-- around the active context.
import ExprPreservationStep2

-- Declarative typing of processes using context
-- splitting and fully used leftovers.
import ProcTyping

-- Small example developments exercising
-- the formalization.
import Examples

-- Experimental scratch developments exploring
-- protocol constructors and subtyping interactions.
import Experiment
