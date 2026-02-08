/-
  Hyper Hoare Logic - Basic Types and Foundations
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Ext

/-!
# Phase 1: Basic Types and Foundations

This file defines the fundamental types for Hyper Hoare Logic:
- Program variables and values
- Program states
- Logical variables and values (for quantification over executions)
- Extended states (pairs of logical and program state)
- Sets of states (for hyper-assertions)
-/

namespace HHL

/-! ## Program Variables and Values -/

/-- Program variable names -/
def PVar := String
deriving DecidableEq, Hashable, Repr

/-- Program values (integers for simplicity) -/
abbrev PVal := Int

/-! ## Program States -/

/-- A program state maps program variables to values.
    We use a total function with a default value of 0. -/
def PState := PVar → PVal

namespace PState

/-- The initial/empty program state (all variables are 0) -/
def empty : PState := fun _ => 0

/-- Update a program state at a given variable -/
def update (σ : PState) (x : PVar) (v : PVal) : PState :=
  fun y => if y = x then v else σ y

/-- Notation for state update -/
scoped notation:max σ "[" x " ↦ " v "]" => update σ x v

/-- Looking up a variable in a state -/
def lookup (σ : PState) (x : PVar) : PVal := σ x

theorem update_same (σ : PState) (x : PVar) (v : PVal) :
    (σ[x ↦ v]) x = v := by simp [update]

theorem update_other (σ : PState) (x y : PVar) (v : PVal) (h : y ≠ x) :
    (σ[x ↦ v]) y = σ y := by simp [update, h]

theorem update_override (σ : PState) (x : PVar) (v₁ v₂ : PVal) :
    (σ[x ↦ v₁])[x ↦ v₂] = σ[x ↦ v₂] := by
  funext y
  simp only [update]
  split_ifs <;> rfl

theorem update_commute (σ : PState) (x y : PVar) (v₁ v₂ : PVal) (h : x ≠ y) :
    (σ[x ↦ v₁])[y ↦ v₂] = (σ[y ↦ v₂])[x ↦ v₁] := by
  funext z
  simp only [update]
  split_ifs with h1 h2 h3
  · simp_all
  · rfl
  · rfl
  · rfl

end PState

/-! ## Logical Variables and Values -/

/-- Logical variable names (for quantifying over executions) -/
def LVar := String
deriving DecidableEq, Hashable, Repr

/-- Logical values (same type as program values) -/
abbrev LVal := Int

/-! ## Logical States -/

/-- A logical state maps logical variables to values -/
def LState := LVar → LVal

namespace LState

/-- The empty logical state -/
def empty : LState := fun _ => 0

/-- Update a logical state -/
def update (ls : LState) (x : LVar) (v : LVal) : LState :=
  fun y => if y = x then v else ls y

scoped notation:max ls "[" x " ↦ " v "]" => update ls x v

theorem update_same (ls : LState) (x : LVar) (v : LVal) :
    (ls[x ↦ v]) x = v := by simp [update]

theorem update_other (ls : LState) (x y : LVar) (v : LVal) (h : y ≠ x) :
    (ls[x ↦ v]) y = ls y := by simp [update, h]

end LState

/-! ## Extended States -/

/-- An extended state is a pair of a logical state and a program state.
    The logical state tracks which execution we're referring to in hyper-assertions. -/
@[ext]
structure ExtState where
  lstate : LState
  pstate : PState

namespace ExtState

/-- The empty extended state -/
def empty : ExtState := ⟨LState.empty, PState.empty⟩

/-- Update the program state component -/
def updatePState (σ : ExtState) (x : PVar) (v : PVal) : ExtState :=
  { σ with pstate := PState.update σ.pstate x v }

/-- Update the logical state component -/
def updateLState (σ : ExtState) (x : LVar) (v : LVal) : ExtState :=
  { σ with lstate := LState.update σ.lstate x v }

/-- Create an extended state from just a program state (empty logical state) -/
def fromPState (ps : PState) : ExtState :=
  ⟨LState.empty, ps⟩

/-- Two extended states agree on program state -/
def agreeOnPState (σ₁ σ₂ : ExtState) : Prop :=
  σ₁.pstate = σ₂.pstate

end ExtState

/-! ## Sets of States -/

/-- A set of extended states - the domain of hyper-assertions -/
abbrev StateSet := Set ExtState

namespace StateSet

/-- The empty set of states -/
def empty : StateSet := ∅

/-- The universal set of states -/
def univ : StateSet := Set.univ

/-- Singleton set -/
def singleton (σ : ExtState) : StateSet := {σ}

/-- Union of state sets -/
def union (S₁ S₂ : StateSet) : StateSet := S₁ ∪ S₂

/-- Intersection of state sets -/
def inter (S₁ S₂ : StateSet) : StateSet := S₁ ∩ S₂

/-- Filter states by a predicate -/
def filter (S : StateSet) (p : ExtState → Prop) : StateSet :=
  {σ ∈ S | p σ}

/-- Map a function over program states, preserving logical states -/
def mapPState (S : StateSet) (f : PState → PState) : StateSet :=
  { σ' | ∃ σ ∈ S, σ' = ⟨σ.lstate, f σ.pstate⟩ }

/-- Lift a set of program states to extended states with empty logical state -/
def liftPStates (ps : Set PState) : StateSet :=
  { σ | ∃ p ∈ ps, σ = ExtState.fromPState p }

end StateSet

/-! ## Utility: Low-equivalence for information flow -/

/-- A set of "low" (public) variables -/
abbrev LowVars := Set PVar

/-- Two program states are low-equivalent if they agree on all low variables -/
def lowEquiv (low : LowVars) (σ₁ σ₂ : PState) : Prop :=
  ∀ x ∈ low, σ₁ x = σ₂ x

theorem lowEquiv_refl (low : LowVars) (σ : PState) : lowEquiv low σ σ :=
  fun _ _ => rfl

theorem lowEquiv_symm (low : LowVars) {σ₁ σ₂ : PState} :
    lowEquiv low σ₁ σ₂ → lowEquiv low σ₂ σ₁ :=
  fun h x hx => (h x hx).symm

theorem lowEquiv_trans (low : LowVars) {σ₁ σ₂ σ₃ : PState} :
    lowEquiv low σ₁ σ₂ → lowEquiv low σ₂ σ₃ → lowEquiv low σ₁ σ₃ :=
  fun h₁ h₂ x hx => (h₁ x hx).trans (h₂ x hx)

end HHL
