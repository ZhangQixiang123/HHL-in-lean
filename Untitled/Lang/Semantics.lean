/-
  Hyper Hoare Logic - Programming Language Semantics
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)
-/

import Untitled.Lang.Syntax
import Mathlib.Data.Set.Lattice

set_option linter.style.emptyLine false

/-!
# Phase 2b: Programming Language Semantics

This file defines:
- Big-step operational semantics for individual executions
- Set-based semantics for sets of states (used in hyper-triples)
-/

namespace HHL

open PState

/-! ## Big-Step Semantics

The big-step semantics relates input states to output states for terminating executions.
Non-terminating executions and stuck states (e.g., failing assumes) have no outputs.
-/

/-- Big-step operational semantics: `BigStep c σ σ'` means
    executing command `c` from state `σ` can terminate in state `σ'` -/
inductive BigStep : Cmd → PState → PState → Prop where
  | skip : ∀ σ, BigStep Cmd.skip σ σ
  | assign : ∀ σ x e, BigStep (Cmd.assign x e) σ (σ[x ↦ e.eval σ])
  | seq : ∀ c₁ c₂ σ σ' σ'',
      BigStep c₁ σ σ' → BigStep c₂ σ' σ'' → BigStep (Cmd.seq c₁ c₂) σ σ''
  | choiceLeft : ∀ c₁ c₂ σ σ',
      BigStep c₁ σ σ' → BigStep (Cmd.choice c₁ c₂) σ σ'
  | choiceRight : ∀ c₁ c₂ σ σ',
      BigStep c₂ σ σ' → BigStep (Cmd.choice c₁ c₂) σ σ'
  | assume : ∀ σ b,
      b.eval σ = true → BigStep (Cmd.assume b) σ σ
  | havoc : ∀ σ x v,
      BigStep (Cmd.havoc x) σ (σ[x ↦ v])
  | whileFalse : ∀ σ b body,
      b.eval σ = false → BigStep (Cmd.whileLoop b body) σ σ
  | whileTrue : ∀ σ σ' σ'' b body,
      b.eval σ = true → BigStep body σ σ' →
      BigStep (Cmd.whileLoop b body) σ' σ'' →
      BigStep (Cmd.whileLoop b body) σ σ''

namespace BigStep

/-- Skip produces equal states -/
theorem skip_eq {σ σ' : PState} (h : BigStep Cmd.skip σ σ') : σ' = σ := by
  cases h; rfl

/-- Assign is deterministic -/
theorem assign_eq {x : PVar} {e : Expr} {σ σ' : PState}
    (h : BigStep (Cmd.assign x e) σ σ') : σ' = σ[x ↦ e.eval σ] := by
  cases h; rfl

/-- Assume produces equal states -/
theorem assume_eq {b : BExpr} {σ σ' : PState}
    (h : BigStep (Cmd.assume b) σ σ') : σ' = σ := by
  cases h; rfl

/-- Assume requires the condition to hold -/
theorem assume_cond {b : BExpr} {σ σ' : PState}
    (h : BigStep (Cmd.assume b) σ σ') : b.eval σ = true := by
  cases h with
  | assume _ _ hb => exact hb

/-- Havoc produces an updated state for some value -/
theorem havoc_result {x : PVar} {σ σ' : PState}
    (h : BigStep (Cmd.havoc x) σ σ') : ∃ v, σ' = σ[x ↦ v] := by
  cases h with
  | havoc _ _ v => exact ⟨v, rfl⟩

/-- If-then-else semantics -/
theorem ite_true {b : BExpr} {c₁ c₂ : Cmd} {σ σ' : PState}
    (hb : b.eval σ = true) (hc : BigStep c₁ σ σ') :
    BigStep (Cmd.ite b c₁ c₂) σ σ' := by
  unfold Cmd.ite
  apply choiceLeft
  exact seq (Cmd.assume b) c₁ σ σ σ' (assume σ b hb) hc

theorem ite_false {b : BExpr} {c₁ c₂ : Cmd} {σ σ' : PState}
    (hb : b.eval σ = false) (hc : BigStep c₂ σ σ') :
    BigStep (Cmd.ite b c₁ c₂) σ σ' := by
  unfold Cmd.ite
  apply choiceRight
  apply seq (Cmd.assume b.not) c₂ σ σ σ'
  · apply assume
    simp [BExpr.eval, hb]
  · exact hc

end BigStep

/-! ## Set-Based Semantics (Extended Semantics)

For hyper-properties, we need to reason about sets of states.
The extended semantics `sem c S` computes the set of all states
reachable by executing `c` from any state in `S`.
-/

/-- The set of output program states reachable from a set of input states -/
def semPState (c : Cmd) (S : Set PState) : Set PState :=
  {σ' | ∃ σ ∈ S, BigStep c σ σ'}

/-- Extended semantics: execute command on a set of extended states.
    Logical state is preserved during execution. -/
def sem (c : Cmd) (S : StateSet) : StateSet :=
  {σ' | ∃ σ ∈ S, BigStep c σ.pstate σ'.pstate ∧ σ'.lstate = σ.lstate}

namespace Sem

/-- Semantic equivalence of commands -/
def equiv (c₁ c₂ : Cmd) : Prop :=
  ∀ S, sem c₁ S = sem c₂ S

/-- Skip is the identity on state sets -/
theorem skip_id (S : StateSet) : sem Cmd.skip S = S := by
  ext σ
  constructor
  · intro ⟨σ', hσ', hstep, heq⟩
    -- Use the lemma that works at PState level (no projection issues)
    have hpeq : σ.pstate = σ'.pstate := BigStep.skip_eq hstep
    -- Now prove σ = σ' using extensionality
    have hσeq : σ = σ' := by
      ext
      · exact heq  -- σ.lstate = σ'.lstate
      · exact hpeq -- σ.pstate = σ'.pstate
    rw [hσeq]; exact hσ'
  · intro hσ
    exact ⟨σ, hσ, BigStep.skip σ.pstate, rfl⟩

/-- Empty set produces empty set -/
theorem empty_sem (c : Cmd) : sem c ∅ = ∅ := by
  ext σ
  simp only [sem, Set.mem_setOf_eq, Set.mem_empty_iff_false]
  -- Goal: (∃ σ', σ' ∈ ∅ ∧ ...) ↔ False
  -- The existential requires σ' ∈ ∅, which is False
  simp only [false_and, exists_false]

/-- Semantics is monotonic -/
theorem mono {c : Cmd} {S₁ S₂ : StateSet} (h : S₁ ⊆ S₂) :
    sem c S₁ ⊆ sem c S₂ := by
  intro σ ⟨σ', hσ', hstep, heq⟩
  exact ⟨σ', h hσ', hstep, heq⟩

/-- Semantics distributes over union -/
theorem union_sem (c : Cmd) (S₁ S₂ : StateSet) :
    sem c (S₁ ∪ S₂) = sem c S₁ ∪ sem c S₂ := by
  ext σ
  simp only [sem, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨σ', hσ', hstep, heq⟩
    cases hσ' with
    | inl h => left; exact ⟨σ', h, hstep, heq⟩
    | inr h => right; exact ⟨σ', h, hstep, heq⟩
  · rintro (⟨σ', hσ', hstep, heq⟩ | ⟨σ', hσ', hstep, heq⟩)
    · exact ⟨σ', Or.inl hσ', hstep, heq⟩
    · exact ⟨σ', Or.inr hσ', hstep, heq⟩

/-- Semantics of sequential composition -/
theorem seq_sem (c₁ c₂ : Cmd) (S : StateSet) :
    sem (Cmd.seq c₁ c₂) S = sem c₂ (sem c₁ S) := by
  ext σ
  simp only [sem, Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ₀, hσ₀, hstep, heq⟩
    -- Invert the seq step to get intermediate state
    cases hstep with
    | seq _ _ _ σ₁ _ h₁ h₂ =>
      exact ⟨⟨σ₀.lstate, σ₁⟩, ⟨σ₀, hσ₀, h₁, rfl⟩, h₂, heq⟩
  · rintro ⟨σ₁, ⟨σ₀, hσ₀, h₁, heq₁⟩, h₂, heq₂⟩
    refine ⟨σ₀, hσ₀, ?_, ?_⟩
    · exact BigStep.seq c₁ c₂ σ₀.pstate σ₁.pstate σ.pstate h₁ h₂
    · simp_all

/-- Semantics of choice -/
theorem choice_sem (c₁ c₂ : Cmd) (S : StateSet) :
    sem (Cmd.choice c₁ c₂) S = sem c₁ S ∪ sem c₂ S := by
  ext σ
  simp only [sem, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨σ₀, hσ₀, hstep, heq⟩
    cases hstep with
    | choiceLeft _ _ _ _ h => left; exact ⟨σ₀, hσ₀, h, heq⟩
    | choiceRight _ _ _ _ h => right; exact ⟨σ₀, hσ₀, h, heq⟩
  · rintro (⟨σ₀, hσ₀, h, heq⟩ | ⟨σ₀, hσ₀, h, heq⟩)
    · exact ⟨σ₀, hσ₀, BigStep.choiceLeft _ _ _ _ h, heq⟩
    · exact ⟨σ₀, hσ₀, BigStep.choiceRight _ _ _ _ h, heq⟩

/-- Semantics of assume -/
theorem assume_sem (b : BExpr) (S : StateSet) :
    sem (Cmd.assume b) S = {σ ∈ S | b.eval σ.pstate = true} := by
  ext σ
  simp only [sem, Set.mem_setOf_eq]
  constructor
  · intro ⟨σ₀, hσ₀, hstep, heq⟩
    -- Use lemmas at PState level to avoid projection issues
    have hpeq : σ.pstate = σ₀.pstate := BigStep.assume_eq hstep
    have hcond : b.eval σ₀.pstate = true := BigStep.assume_cond hstep
    have hσeq : σ = σ₀ := by
      ext
      · exact heq  -- σ.lstate = σ₀.lstate
      · exact hpeq -- σ.pstate = σ₀.pstate
    rw [hσeq]
    exact ⟨hσ₀, hcond⟩
  · rintro ⟨hσ, hb⟩
    exact ⟨σ, hσ, BigStep.assume σ.pstate b hb, rfl⟩

end Sem

/-! ## Iteration (for completeness) -/

/-- Iterate a command n times -/
def iterN : Cmd → ℕ → Cmd
  | _, 0 => Cmd.skip
  | c, n + 1 => Cmd.seq c (iterN c n)

/-- Reflexive transitive closure of a command -/
def iterStar (c : Cmd) : StateSet → StateSet :=
  fun S => ⋃ n, sem (iterN c n) S

namespace IterStar

theorem zero_mem (c : Cmd) (S : StateSet) : S ⊆ iterStar c S := by
  intro σ hσ
  simp only [iterStar, Set.mem_iUnion]
  use 0
  simp only [iterN, Sem.skip_id, hσ]

end IterStar

end HHL
