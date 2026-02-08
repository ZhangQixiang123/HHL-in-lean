/-
  Hyper Hoare Logic - Loop Rules
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)

  Phase 7: While Loop Rules
-/

import Untitled.Rules.Syntactic

namespace HHL

/-! ## While Loop Semantics

The semantics of while loops in terms of iteration.
-/

/-- While loop unfolds to: if b then (body ; while b body) else skip -/
theorem whileLoop_unfold (b : BExpr) (body : Cmd) (S : StateSet) :
    sem (Cmd.whileLoop b body) S =
    sem (Cmd.ite b (Cmd.seq body (Cmd.whileLoop b body)) Cmd.skip) S := by
  -- This is a standard unfolding property of while loops
  -- The proof requires careful handling of big-step semantics
  sorry

/-! ## Synchronized While Rule

When all executions iterate the same number of times.
-/

/-- WhileSync rule: synchronized iterations with invariant I -/
theorem whileSync {I : HyperAssertion} {b : BExpr} {body : Cmd}
    (hInv : ⊨ᴴ HyperAssertion.and I (allSatisfy fun σ => b.eval σ.pstate = true),
            body, I) :
    ⊨ᴴ I, Cmd.whileLoop b body,
       HyperAssertion.and I (allSatisfy fun σ => b.eval σ.pstate = false) := by
  -- The key insight: if all states in the set have the same truth value for b,
  -- and I is preserved by body, then after the loop I holds and b is false everywhere.
  intro S hI
  -- This requires proving that the loop terminates with b false everywhere
  -- The challenge is that different states might iterate different numbers of times
  sorry

/-! ## Iteration-based While Rules -/

/-- Helper: n iterations of body followed by assume ¬b -/
def whileBody (b : BExpr) (body : Cmd) (n : ℕ) : Cmd :=
  Cmd.seq (iterN (Cmd.seq (Cmd.assume b) body) n) (Cmd.assume b.not)

/-- The while loop equals the union of all finite iterations -/
theorem whileLoop_as_union (b : BExpr) (body : Cmd) (S : StateSet) :
    sem (Cmd.whileLoop b body) S = ⋃ n, sem (whileBody b body n) S := by
  ext σ
  simp only [Set.mem_iUnion, sem, Set.mem_setOf_eq]
  constructor
  · intro ⟨σ₀, hσ₀, hstep, heq⟩
    -- Count iterations and construct the witness
    sorry -- Requires induction on the big-step derivation
  · intro ⟨n, σ₀, hσ₀, hstep, heq⟩
    refine ⟨σ₀, hσ₀, ?_, heq⟩
    -- Convert whileBody execution to whileLoop execution
    sorry

/-! ## While-∀*∃* Rule

For when different executions may iterate different numbers of times.
Uses the ⊗ operator to handle asynchronous iterations.
-/

/-- Indexed invariants for the While-∀*∃* rule -/
structure WhileInvariant (b : BExpr) (body : Cmd) where
  /-- Invariant at each iteration count -/
  I : ℕ → HyperAssertion
  /-- I 0 contains states where b is false -/
  base : ∀ S, I 0 S → allSatisfy (fun σ => b.eval σ.pstate = false) S
  /-- Each step preserves the invariant structure -/
  step : ∀ n, ⊨ᴴ HyperAssertion.and (I (n + 1)) (allSatisfy fun σ => b.eval σ.pstate = true),
              body, I n

/-- While-∀*∃* rule using indexed tensor -/
theorem while_forall_exists {b : BExpr} {body : Cmd} (inv : WhileInvariant b body) :
    ⊨ᴴ (⊗ᵢ inv.I), Cmd.whileLoop b body, inv.I 0 := by
  -- The proof proceeds by showing that each component of ⊗ᵢ inv.I
  -- corresponds to a set of states that will terminate in inv.I 0
  intro S hPre
  simp only [otimesNat] at hPre
  obtain ⟨f, hSeq, hI⟩ := hPre
  -- Each f n satisfies inv.I n
  -- After the loop, everything ends up in inv.I 0
  sorry

/-! ## While-∃ Rule

For existentially quantified single-trace properties.
-/

/-- While-∃ rule: existential invariant -/
theorem while_exists {I : HyperAssertion} {b : BExpr} {body : Cmd}
    (hInv : ∀ S, I S → ∃ σ ∈ S, b.eval σ.pstate = true →
            I (sem body {σ})) :
    ⊨ᴴ I, Cmd.whileLoop b body, I := by
  -- This rule allows for existential reasoning about loop invariants
  intro S hI
  sorry

/-! ## Partial Correctness for Loops -/

/-- Standard while rule (partial correctness) -/
theorem while_partial {I : HyperAssertion} {b : BExpr} {body : Cmd}
    (hDC : downwardClosed I)
    (hInv : ⊨ᴴ HyperAssertion.and I (allSatisfy fun σ => b.eval σ.pstate = true),
            body, I) :
    ⊨ᴴ I, Cmd.whileLoop b body,
       HyperAssertion.and I (allSatisfy fun σ => b.eval σ.pstate = false) := by
  intro S hI
  -- The proof needs to handle all possible execution paths
  -- Each path has finitely many iterations (partial correctness)
  sorry

/-! ## Loop Termination Helpers -/

/-- Decreasing variant for termination proofs -/
def hasVariant (c : Cmd) (v : ExtState → ℕ) : Prop :=
  ∀ σ σ', BigStep c σ.pstate σ'.pstate → σ'.lstate = σ.lstate → v σ' < v σ

/-- Well-founded induction on loop iterations -/
theorem while_wf {I : HyperAssertion} {b : BExpr} {body : Cmd} {v : ExtState → ℕ}
    (hVar : hasVariant body v)
    (hInv : ⊨ᴴ HyperAssertion.and I (allSatisfy fun σ => b.eval σ.pstate = true),
            body, I) :
    ⊨ᴴ I, Cmd.whileLoop b body,
       HyperAssertion.and I (allSatisfy fun σ => b.eval σ.pstate = false) := by
  -- Total correctness: the variant ensures termination
  sorry

end HHL
