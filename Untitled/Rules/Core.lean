/-
  Hyper Hoare Logic - Core Inference Rules
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)

  Phase 5: Complete Core Rules
-/

import Untitled.HyperTriple

namespace HHL

open Cmd
open PState (update)

/-! ## Additional Semantic Lemmas -/

/-- Semantics of assign -/
theorem Sem.assign_sem (x : PVar) (e : Expr) (S : StateSet) :
    sem (Cmd.assign x e) S =
    { σ' | ∃ σ ∈ S, σ'.pstate = update σ.pstate x (e.eval σ.pstate) ∧
                    σ'.lstate = σ.lstate } := by
  ext σ
  simp only [sem, Set.mem_setOf_eq]
  constructor
  · intro ⟨σ₀, hσ₀, hstep, heq⟩
    -- Use helper lemma to avoid dependent elimination issues
    have hpeq : σ.pstate = update σ₀.pstate x (e.eval σ₀.pstate) := BigStep.assign_eq hstep
    exact ⟨σ₀, hσ₀, hpeq, heq⟩
  · intro ⟨σ₀, hσ₀, hpeq, heq⟩
    refine ⟨σ₀, hσ₀, ?_, heq⟩
    rw [hpeq]
    exact BigStep.assign σ₀.pstate x e

/-- Semantics of havoc -/
theorem Sem.havoc_sem (x : PVar) (S : StateSet) :
    sem (Cmd.havoc x) S =
    { σ' | ∃ σ ∈ S, ∃ v : PVal, σ'.pstate = update σ.pstate x v ∧
                                 σ'.lstate = σ.lstate } := by
  ext σ
  simp only [sem, Set.mem_setOf_eq]
  constructor
  · intro ⟨σ₀, hσ₀, hstep, heq⟩
    -- Use helper lemma to avoid dependent elimination issues
    obtain ⟨v, hpeq⟩ := BigStep.havoc_result hstep
    exact ⟨σ₀, hσ₀, v, hpeq, heq⟩
  · intro ⟨σ₀, hσ₀, v, hpeq, heq⟩
    refine ⟨σ₀, hσ₀, ?_, heq⟩
    rw [hpeq]
    exact BigStep.havoc σ₀.pstate x v

/-! ## Properties of Hyper-Assertions -/

/-- A hyper-assertion is union-closed if Q(S₁) ∧ Q(S₂) → Q(S₁ ∪ S₂) -/
def unionClosed (Q : HyperAssertion) : Prop :=
  ∀ S₁ S₂, Q S₁ → Q S₂ → Q (S₁ ∪ S₂)

/-- A hyper-assertion is downward-closed if Q(S) and S' ⊆ S implies Q(S') -/
def downwardClosed (Q : HyperAssertion) : Prop :=
  ∀ S S', S' ⊆ S → Q S → Q S'

/-- allSatisfy predicates are downward-closed -/
theorem allSatisfy_downwardClosed (p : ExtState → Prop) :
    downwardClosed (allSatisfy p) := by
  intro S S' hSub hQ σ hσ
  exact hQ σ (hSub hσ)

/-- allSatisfy predicates are union-closed -/
theorem allSatisfy_unionClosed (p : ExtState → Prop) :
    unionClosed (allSatisfy p) := by
  intro S₁ S₂ hQ₁ hQ₂ σ hσ
  cases hσ with
  | inl h => exact hQ₁ σ h
  | inr h => exact hQ₂ σ h

/-! ## Core Inference Rules -/

namespace ValidTriple

/-- Choice rule for union-closed postconditions -/
theorem choice_unionClosed {P Q : HyperAssertion} {c₁ c₂ : Cmd}
    (hUC : unionClosed Q)
    (h₁ : ⊨ᴴ P, c₁, Q) (h₂ : ⊨ᴴ P, c₂, Q) :
    ⊨ᴴ P, (Cmd.choice c₁ c₂), Q := by
  intro S hP
  rw [Sem.choice_sem]
  exact hUC (sem c₁ S) (sem c₂ S) (h₁ S hP) (h₂ S hP)

/-- Choice rule using ⊗ operator (paper's formulation) -/
theorem choice_tensor {P Q₁ Q₂ : HyperAssertion} {c₁ c₂ : Cmd}
    (h₁ : ⊨ᴴ P, c₁, Q₁) (h₂ : ⊨ᴴ P, c₂, Q₂) :
    ⊨ᴴ P, (Cmd.choice c₁ c₂), (Q₁ ⊗ Q₂) := by
  intro S hP
  rw [Sem.choice_sem]
  simp only [otimes]
  exact ⟨sem c₁ S, sem c₂ S, rfl, h₁ S hP, h₂ S hP⟩

/-- Assume rule (requires downward-closed precondition) -/
theorem assume_rule_dc {P : HyperAssertion} {b : BExpr}
    (hDC : downwardClosed P) :
    ⊨ᴴ P, Cmd.assume b, HyperAssertion.and P (allSatisfy fun σ => b.eval σ.pstate = true) := by
  intro S hP
  rw [Sem.assume_sem]
  simp only [HyperAssertion.and, allSatisfy]
  constructor
  · apply hDC S
    · intro σ ⟨hσS, _⟩
      exact hσS
    · exact hP
  · intro σ ⟨_, hb⟩
    exact hb

/-- Assume rule for allSatisfy predicates (which are downward-closed) -/
theorem assume_rule_allSatisfy {p : ExtState → Prop} {b : BExpr} :
    ⊨ᴴ allSatisfy p, Cmd.assume b,
       HyperAssertion.and (allSatisfy p) (allSatisfy fun σ => b.eval σ.pstate = true) := by
  apply assume_rule_dc
  exact allSatisfy_downwardClosed p

/-- Assign rule (weakest precondition style) -/
theorem assign_wp {Q : HyperAssertion} {x : PVar} {e : Expr} :
    ⊨ᴴ (fun S => Q (StateSet.mapPState S (fun σ => update σ x (e.eval σ)))),
       Cmd.assign x e, Q := by
  intro S hPre
  rw [Sem.assign_sem]
  -- The output set equals mapPState S (update)
  convert hPre using 1
  ext σ
  simp only [StateSet.mapPState, Set.mem_setOf_eq]
  constructor
  · intro ⟨σ₀, hσ₀, hpeq, heq⟩
    exact ⟨σ₀, hσ₀, by ext <;> simp_all⟩
  · intro ⟨σ₀, hσ₀, hσeq⟩
    refine ⟨σ₀, hσ₀, ?_, ?_⟩
    · simp only [hσeq]
    · simp only [hσeq]

/-- Havoc rule (universal over all possible values) -/
theorem havoc_wp {Q : HyperAssertion} {x : PVar}
    (hUC : unionClosed Q) :
    ⊨ᴴ (fun S => ∀ v : PVal, Q (StateSet.mapPState S (fun σ => update σ x v))),
       Cmd.havoc x, Q := by
  intro S hPre
  rw [Sem.havoc_sem]
  -- Need to show Q holds on the union over all values
  -- For each value v, the pre gives Q on the mapped set
  -- This is subtle: havoc produces ⋃ᵥ (mapPState S (update x v))
  -- We need Q to be union-closed or have additional structure
  -- For now, we prove for union-closed Q
  sorry -- Requires more infrastructure for union over all values

/-- Exist rule (existential introduction on precondition) -/
theorem exist_rule {α : Type*} {P : α → HyperAssertion} {c : Cmd} {Q : HyperAssertion}
    (h : ∀ a, ⊨ᴴ P a, c, Q) :
    ⊨ᴴ (fun S => ∃ a, P a S), c, Q := by
  intro S ⟨a, hPa⟩
  exact h a S hPa

/-- Forall rule (universal introduction on postcondition) -/
theorem forall_rule {α : Type*} {P : HyperAssertion} {c : Cmd} {Q : α → HyperAssertion}
    (h : ∀ a, ⊨ᴴ P, c, Q a) :
    ⊨ᴴ P, c, (fun S => ∀ a, Q a S) := by
  intro S hP a
  exact h a S hP

/-- Disjunction rule -/
theorem disj_rule {P₁ P₂ Q : HyperAssertion} {c : Cmd}
    (h₁ : ⊨ᴴ P₁, c, Q) (h₂ : ⊨ᴴ P₂, c, Q) :
    ⊨ᴴ HyperAssertion.or P₁ P₂, c, Q := by
  intro S hP
  cases hP with
  | inl hP₁ => exact h₁ S hP₁
  | inr hP₂ => exact h₂ S hP₂

/-- Conjunction rule -/
theorem conj_rule {P Q₁ Q₂ : HyperAssertion} {c : Cmd}
    (h₁ : ⊨ᴴ P, c, Q₁) (h₂ : ⊨ᴴ P, c, Q₂) :
    ⊨ᴴ P, c, HyperAssertion.and Q₁ Q₂ := by
  intro S hP
  exact ⟨h₁ S hP, h₂ S hP⟩

end ValidTriple

/-! ## Assertion Independence for Frame Rule -/

/-- An assertion depends only on certain variables -/
def dependsOnlyOn (P : HyperAssertion) (vars : Set PVar) : Prop :=
  ∀ S₁ S₂,
    (∀ σ₁ ∈ S₁, ∃ σ₂ ∈ S₂, σ₁.lstate = σ₂.lstate ∧ ∀ x ∈ vars, σ₁.pstate x = σ₂.pstate x) →
    (∀ σ₂ ∈ S₂, ∃ σ₁ ∈ S₁, σ₁.lstate = σ₂.lstate ∧ ∀ x ∈ vars, σ₁.pstate x = σ₂.pstate x) →
    (P S₁ ↔ P S₂)

/-- An assertion is independent of certain variables -/
def independentOf (P : HyperAssertion) (vars : Set PVar) : Prop :=
  ∀ S₁ S₂,
    (∀ σ₁ ∈ S₁, ∃ σ₂ ∈ S₂, σ₁.lstate = σ₂.lstate ∧ ∀ x ∉ vars, σ₁.pstate x = σ₂.pstate x) →
    (∀ σ₂ ∈ S₂, ∃ σ₁ ∈ S₁, σ₁.lstate = σ₂.lstate ∧ ∀ x ∉ vars, σ₁.pstate x = σ₂.pstate x) →
    (P S₁ ↔ P S₂)

/-- Frame rule with independence condition -/
theorem ValidTriple.frame_indep {P Q R : HyperAssertion} {c : Cmd}
    (hTriple : ⊨ᴴ P, c, Q)
    (hIndep : independentOf R (Cmd.writtenVars c)) :
    ⊨ᴴ HyperAssertion.and P R, c, HyperAssertion.and Q R := by
  intro S ⟨hP, hR⟩
  constructor
  · exact hTriple S hP
  · -- Need to show R (sem c S) given R S and independence
    -- The key insight: sem c only modifies writtenVars c
    -- So the bijection between S and sem c S preserves non-written vars
    sorry

/-! ## Iteration Rule -/

/-- The iter rule for reflexive-transitive closure -/
theorem ValidTriple.iter {P : HyperAssertion} {c : Cmd}
    (hInv : ⊨ᴴ P, c, P) :
    ∀ n, ⊨ᴴ P, iterN c n, P := by
  intro n
  induction n with
  | zero =>
    simp only [iterN]
    exact ValidTriple.skip P
  | succ n ih =>
    -- iterN c (n+1) = seq c (iterN c n)
    simp only [iterN]
    -- Need: ⊨ᴴ P, seq c (iterN c n), P
    -- By seq: need ⊨ᴴ P, c, P and ⊨ᴴ P, iterN c n, P
    exact ValidTriple.seq hInv ih

/-! ## If-Then-Else Rule -/

/-- If-then-else rule using assume filtering -/
theorem ite_triple_dc {P Q : HyperAssertion} {b : BExpr} {c₁ c₂ : Cmd}
    (hDC : downwardClosed P)
    (hUC : unionClosed Q)
    (h₁ : ⊨ᴴ HyperAssertion.and P (allSatisfy fun σ => b.eval σ.pstate = true), c₁, Q)
    (h₂ : ⊨ᴴ HyperAssertion.and P (allSatisfy fun σ => b.eval σ.pstate = false), c₂, Q) :
    ⊨ᴴ P, (Cmd.ite b c₁ c₂), Q := by
  unfold Cmd.ite
  -- Cmd.ite b c₁ c₂ = choice (seq (assume b) c₁) (seq (assume (not b)) c₂)
  intro S hP
  rw [Sem.choice_sem]
  apply hUC
  · -- Left branch: assume b ; c₁
    rw [Sem.seq_sem]
    rw [Sem.assume_sem]
    apply h₁
    constructor
    · -- P holds on filtered set (downward-closed)
      apply hDC S
      · intro σ ⟨hσS, _⟩
        exact hσS
      · exact hP
    · -- All states satisfy b
      intro σ ⟨_, hb⟩
      exact hb
  · -- Right branch: assume (not b) ; c₂
    rw [Sem.seq_sem]
    rw [Sem.assume_sem]
    apply h₂
    constructor
    · apply hDC S
      · intro σ ⟨hσS, _⟩
        exact hσS
      · exact hP
    · intro σ ⟨_, hb⟩
      simp only [BExpr.eval] at hb
      simp only [Bool.not_eq_true'] at hb
      exact hb

end HHL
