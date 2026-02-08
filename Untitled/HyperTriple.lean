/-
  Hyper Hoare Logic - Hyper-Triples
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)
-/

import Untitled.HyperAssertions

/-!
# Phase 4: Hyper-Triples

This file defines hyper-triples {P} C {Q} and their validity semantics.
A hyper-triple relates hyper-assertions before and after program execution.
-/

namespace HHL

/-! ## Hyper-Triple Definition -/

/-- A hyper-triple consists of:
    - P: precondition (hyper-assertion)
    - c: command
    - Q: postcondition (hyper-assertion)
-/
structure HyperTriple where
  pre : HyperAssertion
  cmd : Cmd
  post : HyperAssertion

/-- A hyper-triple is valid if for any set of states satisfying the precondition,
    the set of output states (after executing the command) satisfies the postcondition. -/
def HyperTriple.valid (t : HyperTriple) : Prop :=
  ∀ S : StateSet, t.pre S → t.post (sem t.cmd S)

/-- Alternative definition using explicit components -/
def validTriple (P : HyperAssertion) (c : Cmd) (Q : HyperAssertion) : Prop :=
  ∀ S : StateSet, P S → Q (sem c S)

-- Use ⊨ᴴ as notation to avoid conflict with { } for sets
notation:25 "⊨ᴴ" P ", " c ", " Q => validTriple P c Q

/-! ## Basic Properties of Valid Triples -/

namespace ValidTriple

/-- Skip preserves any assertion -/
theorem skip (P : HyperAssertion) : ⊨ᴴ P, Cmd.skip, P := by
  intro S hP
  rw [Sem.skip_id]
  exact hP

/-- Consequence rule: strengthen precondition, weaken postcondition -/
theorem consequence {P P' Q Q' : HyperAssertion} {c : Cmd}
    (hPre : P ⊢ P') (hTriple : ⊨ᴴ P', c, Q') (hPost : Q' ⊢ Q) :
    ⊨ᴴ P, c, Q := by
  intro S hP
  exact hPost (sem c S) (hTriple S (hPre S hP))

/-- Sequence rule -/
theorem seq {P Q R : HyperAssertion} {c₁ c₂ : Cmd}
    (h₁ : ⊨ᴴ P, c₁, Q) (h₂ : ⊨ᴴ Q, c₂, R) :
    ⊨ᴴ P, (Cmd.seq c₁ c₂), R := by
  intro S hP
  rw [Sem.seq_sem]
  exact h₂ (sem c₁ S) (h₁ S hP)

/-- Choice rule (requires union-closed postcondition).
    See `Rules.Core.choice_unionClosed` for the proper version with the union-closed hypothesis.
    See `Rules.Core.choice_tensor` for the ⊗ formulation from the paper. -/
theorem choice {P Q : HyperAssertion} {c₁ c₂ : Cmd}
    (hUC : ∀ S₁ S₂, Q S₁ → Q S₂ → Q (S₁ ∪ S₂))
    (h₁ : ⊨ᴴ P, c₁, Q) (h₂ : ⊨ᴴ P, c₂, Q) :
    ⊨ᴴ P, (Cmd.choice c₁ c₂), Q := by
  intro S hP
  rw [Sem.choice_sem]
  exact hUC (sem c₁ S) (sem c₂ S) (h₁ S hP) (h₂ S hP)

/-- Frame rule (requires R to be preserved by c).
    See `Rules.Core.frame_indep` for the version with variable independence. -/
theorem frame {P Q R : HyperAssertion} {c : Cmd}
    (hTriple : ⊨ᴴ P, c, Q)
    (hMono : ∀ S, R S → R (sem c S)) :
    ⊨ᴴ HyperAssertion.and P R, c, HyperAssertion.and Q R := by
  intro S ⟨hP, hR⟩
  exact ⟨hTriple S hP, hMono S hR⟩

end ValidTriple

/-! ## Specialized Validity for Common Patterns -/

/-- Validity for determinism checking -/
def isDeterministic (c : Cmd) : Prop :=
  ⊨ᴴ deterministic, c, deterministic

/-- Validity for non-interference -/
def isNonInterfering (c : Cmd) (low : LowVars) : Prop :=
  ⊨ᴴ nonInterference low, c, nonInterference low

/-! ## Partial Correctness and Total Correctness -/

/-- Partial correctness: if the program terminates, the postcondition holds.
    This is what hyper-triples express by default. -/
def partialCorrect (P : HyperAssertion) (c : Cmd) (Q : HyperAssertion) : Prop :=
  validTriple P c Q

-- Note: Total correctness would additionally require termination.
-- For now, we focus on partial correctness.

/-! ## Derived Triple Constructors -/

/-- Triple for if-then-else (requires downward-closed P and union-closed Q).
    See `Rules.Core.ite_triple_dc` for the full version. -/
theorem ite_triple {P Q : HyperAssertion} {b : BExpr} {c₁ c₂ : Cmd}
    (hDC : ∀ S S', S' ⊆ S → P S → P S')
    (hUC : ∀ S₁ S₂, Q S₁ → Q S₂ → Q (S₁ ∪ S₂))
    (h₁ : ⊨ᴴ HyperAssertion.and P (allSatisfy fun σ => b.eval σ.pstate = true), c₁, Q)
    (h₂ : ⊨ᴴ HyperAssertion.and P (allSatisfy fun σ => b.eval σ.pstate = false), c₂, Q) :
    ⊨ᴴ P, (Cmd.ite b c₁ c₂), Q := by
  unfold Cmd.ite
  intro S hP
  rw [Sem.choice_sem]
  apply hUC
  · rw [Sem.seq_sem, Sem.assume_sem]
    apply h₁
    refine ⟨?_, ?_⟩
    · exact hDC S _ (fun σ hσ => hσ.1) hP
    · intro σ hσ
      exact hσ.2
  · rw [Sem.seq_sem, Sem.assume_sem]
    apply h₂
    refine ⟨?_, ?_⟩
    · exact hDC S _ (fun σ hσ => hσ.1) hP
    · intro σ hσ
      simp only [BExpr.eval] at hσ
      simp only [Bool.not_eq_true'] at hσ
      exact hσ.2

/-! ## Examples: Specifying Hyperproperties -/

/-
  Note: Assignment does NOT preserve determinism in general!
  Counter-example: If S = {σ₁, σ₂} where σ₁.pstate differs from σ₂.pstate only at x,
  then after x := c, both have the same pstate but possibly different lstates.
  Determinism is preserved when the assignment doesn't "merge" distinct traces.
-/

/-- Skip preserves determinism -/
theorem skip_deterministic : isDeterministic Cmd.skip := by
  unfold isDeterministic validTriple
  intro S hDet
  rw [Sem.skip_id]
  exact hDet

/-- Example: Skip is non-interfering for any set of low variables -/
theorem skip_nonInterfering (low : LowVars) : isNonInterfering Cmd.skip low := by
  unfold isNonInterfering validTriple
  intro S hNI
  rw [Sem.skip_id]
  exact hNI

/-! ## Connection to Classical Hoare Logic -/

/-- A classical Hoare triple can be embedded as a hyper-triple -/
def classicalTriple (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  validTriple ⟦P⟧ c ⟦Q⟧

/-- Classical Hoare logic is a special case of Hyper Hoare Logic
    where all assertions are lifted from single-state predicates -/
theorem classical_skip (P : Assertion) : classicalTriple P Cmd.skip P := by
  unfold classicalTriple validTriple
  intro S hP
  rw [Sem.skip_id]
  exact hP

theorem classical_seq {P Q R : Assertion} {c₁ c₂ : Cmd}
    (h₁ : classicalTriple P c₁ Q) (h₂ : classicalTriple Q c₂ R) :
    classicalTriple P (Cmd.seq c₁ c₂) R := by
  unfold classicalTriple validTriple at *
  intro S hP
  rw [Sem.seq_sem]
  exact h₂ (sem c₁ S) (h₁ S hP)

/-! ## Semantic Characterization of Hyperproperties -/

/-- A property is a hyperproperty (in the sense that it relates multiple traces) -/
def isHyperproperty (P : HyperAssertion) : Prop :=
  ¬∃ (p : ExtState → Prop), P = allSatisfy p

/-- Determinism is a genuine hyperproperty -/
theorem determinism_is_hyperproperty : isHyperproperty deterministic := by
  intro ⟨p, heq⟩
  -- Strategy: deterministic is true on singletons, so p must hold everywhere
  -- But then allSatisfy p is true on all sets, contradicting that deterministic
  -- is false on some sets (e.g., two states with same pstate, different lstate)

  -- First, show p holds for all states (from singleton sets)
  have hp : ∀ σ, p σ := by
    intro σ
    -- deterministic holds on {σ} (vacuously: only one state)
    have hdet : deterministic {σ} := by
      simp only [deterministic, allPairsSatisfy, Set.mem_singleton_iff]
      intro σ₁ hσ₁ σ₂ hσ₂ _
      rw [hσ₁, hσ₂]
    -- So allSatisfy p {σ} holds
    rw [heq] at hdet
    simp only [allSatisfy, Set.mem_singleton_iff] at hdet
    exact hdet σ rfl

  -- But allSatisfy p is true everywhere if p is true everywhere
  have hall : ∀ S, allSatisfy p S := by
    intro S σ _
    exact hp σ

  -- Now find a set where deterministic is false
  -- Take two states with same pstate but different lstate
  let σ₁ : ExtState := ⟨fun _ => 0, fun _ => 0⟩
  let σ₂ : ExtState := ⟨fun _ => 1, fun _ => 0⟩
  have hne : σ₁ ≠ σ₂ := by
    intro h
    have : σ₁.lstate = σ₂.lstate := by rw [h]
    simp only [σ₁, σ₂] at this
    have : (0 : Int) = 1 := congr_fun this ""
    omega

  have hpeq : σ₁.pstate = σ₂.pstate := rfl

  -- deterministic should be false on {σ₁, σ₂}
  have hnotdet : ¬deterministic {σ₁, σ₂} := by
    simp only [deterministic, allPairsSatisfy]
    push_neg
    exact ⟨σ₁, Or.inl rfl, σ₂, Or.inr rfl, hpeq, hne⟩

  -- But heq says deterministic = allSatisfy p
  rw [heq] at hnotdet
  exact hnotdet (hall {σ₁, σ₂})

/-! ## Proof Outline Structures -/

/-- A proof outline tracks intermediate assertions -/
inductive ProofOutline where
  | triple : HyperAssertion → Cmd → HyperAssertion → ProofOutline
  | seq : ProofOutline → ProofOutline → ProofOutline
  | branch : HyperAssertion → ProofOutline → ProofOutline → HyperAssertion → ProofOutline

/-- Extract the final triple from a proof outline -/
def ProofOutline.toTriple : ProofOutline → HyperTriple
  | triple P c Q => ⟨P, c, Q⟩
  | seq o₁ o₂ =>
    let t₁ := o₁.toTriple
    let t₂ := o₂.toTriple
    ⟨t₁.pre, Cmd.seq t₁.cmd t₂.cmd, t₂.post⟩
  | branch P o₁ o₂ Q =>
    let t₁ := o₁.toTriple
    let t₂ := o₂.toTriple
    ⟨P, Cmd.choice t₁.cmd t₂.cmd, Q⟩

end HHL
