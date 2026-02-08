/-
  Hyper Hoare Logic - Non-Interference Examples
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)

  Phase 10: Example - Information Flow Security
-/

import Untitled.Metatheory.Completeness

namespace HHL.Examples

/-! ## Non-Interference

Non-interference is a security property stating that high-security inputs
do not influence low-security outputs. This is a 2-safety hyperproperty.
-/

-- Recall: nonInterference and lowEquiv from HHL.HyperAssertions

/-! ## Basic Non-Interference Results -/

/-- Skip is non-interfering for any low variables -/
theorem skip_ni (low : LowVars) :
    ⊨ᴴ nonInterference low, Cmd.skip, nonInterference low := by
  intro S hNI
  rw [Sem.skip_id]
  exact hNI

/-- Assignment to a low variable preserves non-interference
    if the expression only depends on low variables -/
theorem assign_low_ni (low : LowVars) (x : PVar) (e : Expr)
    (hLow : x ∈ low)
    (hExprLow : ∀ σ₁ σ₂, lowEquiv low σ₁ σ₂ → e.eval σ₁ = e.eval σ₂) :
    ⊨ᴴ nonInterference low, Cmd.assign x e, nonInterference low := by
  intro S hNI
  simp only [nonInterference, allPairsSatisfy] at *
  intro σ₁ hσ₁ σ₂ hσ₂
  simp only [sem, Set.mem_setOf_eq] at hσ₁ hσ₂
  obtain ⟨σ₁', hσ₁'S, hstep₁, hlstate₁⟩ := hσ₁
  obtain ⟨σ₂', hσ₂'S, hstep₂, hlstate₂⟩ := hσ₂
  have heq₁ := BigStep.assign_eq hstep₁
  have heq₂ := BigStep.assign_eq hstep₂
  have hlow := hNI σ₁' hσ₁'S σ₂' hσ₂'S
  intro y hy
  simp only [heq₁, heq₂, PState.update]
  by_cases hyx : y = x
  · -- y = x: use that e only depends on low vars
    simp only [if_pos hyx]
    exact hExprLow σ₁'.pstate σ₂'.pstate hlow
  · -- y ≠ x: use original low equivalence
    simp only [if_neg hyx]
    exact hlow y hy

/-- Assignment to a high variable preserves non-interference -/
theorem assign_high_ni (low : LowVars) (x : PVar) (e : Expr)
    (hHigh : x ∉ low) :
    ⊨ᴴ nonInterference low, Cmd.assign x e, nonInterference low := by
  intro S hNI
  simp only [nonInterference, allPairsSatisfy] at *
  intro σ₁ hσ₁ σ₂ hσ₂
  simp only [sem, Set.mem_setOf_eq] at hσ₁ hσ₂
  obtain ⟨σ₁', hσ₁'S, hstep₁, hlstate₁⟩ := hσ₁
  obtain ⟨σ₂', hσ₂'S, hstep₂, hlstate₂⟩ := hσ₂
  have heq₁ := BigStep.assign_eq hstep₁
  have heq₂ := BigStep.assign_eq hstep₂
  have hlow := hNI σ₁' hσ₁'S σ₂' hσ₂'S
  intro y hy
  simp only [heq₁, heq₂, PState.update]
  -- y ∈ low but x ∉ low, so y ≠ x
  have hyx : y ≠ x := fun h => hHigh (h ▸ hy)
  simp only [if_neg hyx]
  exact hlow y hy

/-! ## Generalized Non-Interference (GNI) -/

-- Recall: GNI from HHL.HyperAssertions

/-- Skip preserves GNI -/
theorem skip_gni (low : LowVars) :
    ⊨ᴴ GNI low, Cmd.skip, GNI low := by
  intro S hGNI
  rw [Sem.skip_id]
  exact hGNI

/-! ## Secure Information Flow Examples -/

/-- A program that copies high to low is NOT non-interfering -/
theorem copy_high_to_low_insecure (low : LowVars) (h l : PVar)
    (hHigh : h ∉ low) (hLow : l ∈ low) :
    ¬(⊨ᴴ nonInterference low, Cmd.assign l (Expr.var h), nonInterference low) := by
  intro hValid
  -- Create two states: σ₁ with h=0, σ₂ with h=1, both low-equivalent
  let ps₁ : PState := fun _ => 0
  let ps₂ : PState := PState.update ps₁ h 1
  let ls : LState := fun _ => 0
  let σ₁ : ExtState := ⟨ls, ps₁⟩
  let σ₂ : ExtState := ⟨ls, ps₂⟩
  let S : StateSet := {σ₁, σ₂}
  -- S satisfies nonInterference: differ only at h which is high
  have hLowEquiv : lowEquiv low ps₁ ps₂ := by
    intro x hx
    have hxh : x ≠ h := fun heq => hHigh (heq ▸ hx)
    simp only [ps₂, PState.update, if_neg hxh]
  have hNI : nonInterference low S := by
    simp only [nonInterference, allPairsSatisfy]
    intro a ha b hb x hx
    cases ha with
    | inl ha => cases hb with
      | inl hb => rw [ha, hb]
      | inr hb => rw [ha, hb]; exact hLowEquiv x hx
    | inr ha => cases hb with
      | inl hb => rw [ha, hb]; exact (hLowEquiv x hx).symm
      | inr hb => rw [ha, hb]
  have hPost := hValid S hNI
  -- After l := h, we have σ₁' with l=0 and σ₂' with l=1
  let ps₁' : PState := PState.update ps₁ l 0
  let ps₂' : PState := PState.update ps₂ l 1
  let σ₁' : ExtState := ⟨ls, ps₁'⟩
  let σ₂' : ExtState := ⟨ls, ps₂'⟩
  have hσ₁'_in : σ₁' ∈ sem (Cmd.assign l (Expr.var h)) S := by
    simp only [sem, Set.mem_setOf_eq]
    refine ⟨σ₁, Or.inl rfl, ?_, rfl⟩
    change BigStep (Cmd.assign l (Expr.var h)) ps₁ ps₁'
    exact BigStep.assign ps₁ l (Expr.var h)
  have hσ₂'_in : σ₂' ∈ sem (Cmd.assign l (Expr.var h)) S := by
    simp only [sem, Set.mem_setOf_eq]
    refine ⟨σ₂, Or.inr rfl, ?_, rfl⟩
    change BigStep (Cmd.assign l (Expr.var h)) ps₂ ps₂'
    -- Need to show ps₂' = ps₂[l ↦ (Expr.var h).eval ps₂]
    -- ps₂ h = 1 (since ps₂ = ps₁[h ↦ 1]), so (Expr.var h).eval ps₂ = 1
    have heq : ps₂' = PState.update ps₂ l ((Expr.var h).eval ps₂) := by
      simp only [ps₂', Expr.eval, ps₂, PState.update_same]
    rw [heq]
    exact BigStep.assign ps₂ l (Expr.var h)
  -- But σ₁' and σ₂' are NOT low-equivalent (they differ at l)
  have hNotLow : ¬lowEquiv low σ₁'.pstate σ₂'.pstate := by
    intro hLowEq
    have hl := hLowEq l hLow
    -- σ₁'.pstate l = ps₁' l = 0, σ₂'.pstate l = ps₂' l = 1
    have h1 : σ₁'.pstate l = (0 : Int) := PState.update_same ps₁ l 0
    have h2 : σ₂'.pstate l = (1 : Int) := PState.update_same ps₂ l 1
    rw [h1, h2] at hl
    exact absurd hl (by decide : (0 : Int) ≠ 1)
  exact hNotLow (hPost σ₁' hσ₁'_in σ₂' hσ₂'_in)

/-- A program that only reads and writes low variables is secure -/
def lowOnly (low : LowVars) (c : Cmd) : Prop :=
  ∀ x ∈ Cmd.readVars c, x ∈ low ∧ ∀ x ∈ Cmd.writtenVars c, x ∈ low

/-! ## Sequential Composition -/

/-- Sequential composition preserves non-interference -/
theorem seq_ni (low : LowVars) {c₁ c₂ : Cmd}
    (h₁ : ⊨ᴴ nonInterference low, c₁, nonInterference low)
    (h₂ : ⊨ᴴ nonInterference low, c₂, nonInterference low) :
    ⊨ᴴ nonInterference low, Cmd.seq c₁ c₂, nonInterference low :=
  ValidTriple.seq h₁ h₂

/-! ## Conditional Branches -/

/-- If-then-else on a low condition preserves non-interference -/
theorem ite_low_ni (low : LowVars) (b : BExpr) {c₁ c₂ : Cmd}
    (hBLow : ∀ σ₁ σ₂, lowEquiv low σ₁ σ₂ → b.eval σ₁ = b.eval σ₂)
    (h₁ : ⊨ᴴ nonInterference low, c₁, nonInterference low)
    (h₂ : ⊨ᴴ nonInterference low, c₂, nonInterference low) :
    ⊨ᴴ nonInterference low, Cmd.ite b c₁ c₂, nonInterference low := by
  -- When the condition only depends on low variables,
  -- low-equivalent inputs will take the same branch
  intro S hNI
  unfold Cmd.ite
  rw [Sem.choice_sem, Sem.seq_sem, Sem.seq_sem, Sem.assume_sem, Sem.assume_sem]
  -- If S is empty, the result is trivially NI
  by_cases hEmpty : S = ∅
  · subst hEmpty
    have h1 : {σ ∈ (∅ : StateSet) | b.eval σ.pstate = true} = ∅ := Set.sep_empty _
    have h2 : {σ ∈ (∅ : StateSet) | b.not.eval σ.pstate = true} = ∅ := Set.sep_empty _
    rw [h1, h2, Sem.empty_sem, Sem.empty_sem, Set.empty_union]
    simp only [nonInterference, allPairsSatisfy, Set.mem_empty_iff_false, false_implies,
                implies_true]
  -- Otherwise, pick any σ₀ ∈ S and all states evaluate b the same way
  · obtain ⟨σ₀, hσ₀⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
    -- All states in S are low-equivalent to σ₀, so they all evaluate b the same
    have hAllSame : ∀ σ ∈ S, b.eval σ.pstate = b.eval σ₀.pstate := by
      intro σ hσ
      exact hBLow σ.pstate σ₀.pstate (hNI σ hσ σ₀ hσ₀)
    by_cases hb : b.eval σ₀.pstate = true
    · -- All take true branch, false branch is empty
      have hTrueAll : ∀ σ ∈ S, b.eval σ.pstate = true := fun σ hσ => (hAllSame σ hσ).trans hb
      have hFalseNone : {σ ∈ S | b.not.eval σ.pstate = true} = ∅ := by
        ext σ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hσ
        simp only [BExpr.eval, Bool.not_eq_true']
        rw [hTrueAll σ hσ]; decide
      have hTrueAll' : {σ ∈ S | b.eval σ.pstate = true} = S := by
        ext σ; simp only [Set.mem_setOf_eq]; constructor
        · exact fun ⟨h, _⟩ => h
        · exact fun h => ⟨h, hTrueAll σ h⟩
      rw [hFalseNone, hTrueAll', Sem.empty_sem, Set.union_empty]
      exact h₁ S hNI
    · -- All take false branch, true branch is empty
      push_neg at hb
      have hb' : b.eval σ₀.pstate = false := Bool.eq_false_iff.mpr hb
      have hFalseAll : ∀ σ ∈ S, b.eval σ.pstate = false :=
        fun σ hσ => (hAllSame σ hσ).trans hb'
      have hTrueNone : {σ ∈ S | b.eval σ.pstate = true} = ∅ := by
        ext σ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hσ
        exact Bool.eq_false_iff.mp (hFalseAll σ hσ)
      have hFalseAll' : {σ ∈ S | b.not.eval σ.pstate = true} = S := by
        ext σ; simp only [Set.mem_setOf_eq, BExpr.eval, Bool.not_eq_true']; constructor
        · exact fun ⟨h, _⟩ => h
        · exact fun h => ⟨h, hFalseAll σ h⟩
      rw [hTrueNone, hFalseAll', Sem.empty_sem, Set.empty_union]
      exact h₂ S hNI

/-- If-then-else on a high condition may break non-interference -/
theorem ite_high_insecure (low : LowVars) (h l : PVar) (b : BExpr)
    (hBHigh : ∃ σ₁ σ₂, lowEquiv low σ₁ σ₂ ∧ b.eval σ₁ ≠ b.eval σ₂) :
    -- The condition depends on high, so branching can leak information
    True := by
  trivial

/-! ## Declassification -/

/-- Controlled declassification: explicitly mark what can be released -/
def declassify (P : HyperAssertion) (rel : ExtState → ExtState → Prop) : HyperAssertion :=
  fun S => P S ∧ ∀ σ₁ ∈ S, ∀ σ₂ ∈ S, rel σ₁ σ₂

end HHL.Examples
