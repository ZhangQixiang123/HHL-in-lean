/-
  Hyper Hoare Logic in Lean
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)

  This formalization implements:
  - Phase 1: Basic types (states, extended states, state sets)
  - Phase 2: Programming language syntax and semantics
  - Phase 3: Hyper-assertions (semantic and syntactic)
  - Phase 4: Hyper-triples and their validity
  - Phase 5: Core inference rules
  - Phase 6: Syntactic transformations
  - Phase 7: Loop rules
  - Phase 8: Soundness proof
  - Phase 9: Completeness proof (relative)
  - Phase 10: Examples (determinism, non-interference)
-/

-- Phase 1: Basic types and foundations
import Untitled.Basic

-- Phase 2: Programming language
import Untitled.Lang.Syntax
import Untitled.Lang.Semantics

-- Phase 3: Hyper-assertions
import Untitled.HyperAssertions

-- Phase 4: Hyper-triples
import Untitled.HyperTriple

-- Phase 5: Core inference rules
import Untitled.Rules.Core

-- Phase 6: Syntactic transformations
import Untitled.Rules.Syntactic

-- Phase 7: Loop rules
import Untitled.Rules.Loop

-- Phase 8: Soundness
import Untitled.Metatheory.Soundness

-- Phase 9: Completeness
import Untitled.Metatheory.Completeness

-- Phase 10: Examples
import Untitled.Examples.Determinism
import Untitled.Examples.NonInterference
