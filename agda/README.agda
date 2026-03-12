module README where

-- Basic extensionality and helper lemmas used throughout the development.
import Ext

-- Small general-purpose utilities and arithmetic/order lemmas.
import Util

-- Kinds, prekinds, multiplicities, and their decidable equalities.
import Kinds

-- Duality infrastructure for session-like structure on types and protocols.
import Duality

-- Generic renaming and substitution kits.
import Kits

-- Core abstract syntax of kinds-indexed types and their normal forms.
import Types

-- Decidable equality for types and related syntax.
import TypesDecidable

-- Declarative subtyping and conversion relations.
import Subtyping

-- Size lemmas for subtyping derivations and normal forms.
import SubtypingSize

-- Structural properties of subtyping, especially size preservation.
import SubtypingProperties

-- Preservation of subtyping and conversion under substitution.
import SubstitutionSubtyping

-- Abstract syntax of expressions and processes from Section 4.
import ExprSyntax

-- Algorithmic expression typing with normalized environments and result types.
import ExprNormalTyping

-- Algorithmic subtyping on normal forms.
import AlgorithmicSubtyping

-- Soundness of the algorithmic subtyping judgments.
import AlgorithmicSound

-- Decidable joins and meets for algorithmic subtyping.
import AlgorithmicMerge

-- Least upper bounds and greatest lower bounds derived from joins and meets.
import AlgorithmicLubGlb

-- Decision procedures for algorithmic subtyping judgments.
import AlgorithmicInference

-- Completeness of the algorithmic system with respect to declarative subtyping.
import AlgorithmicComplete

-- Small example developments exercising the formalization.
import Examples
