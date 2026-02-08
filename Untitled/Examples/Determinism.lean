/-
  Hyper Hoare Logic - Determinism Examples
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)

  Phase 10: Example - Determinism Properties
-/

import Untitled.Metatheory.Completeness

namespace HHL.Examples

/-! ## Determinism

A program is deterministic if running it from the same initial state
always produces the same final state. This is a 2-safety hyperproperty.
-/

-- Recall: deterministic means equal pstates imply equal states
-- HHL.deterministic : HyperAssertion

/-! ## Deterministic Programs -/

/-- Skip is deterministic -/
theorem skip_preserves_det : ⊨ᴴ deterministic, Cmd.skip, deterministic := by
  exact ValidTriple.skip deterministic

/-- Sequential composition of deterministic programs is deterministic -/
theorem seq_preserves_det {c₁ c₂ : Cmd}
    (h₁ : ⊨ᴴ deterministic, c₁, deterministic)
    (h₂ : ⊨ᴴ deterministic, c₂, deterministic) :
    ⊨ᴴ deterministic, Cmd.seq c₁ c₂, deterministic :=
  ValidTriple.seq h₁ h₂

/-! ## Non-Deterministic Programs -/

/-- Havoc is NOT deterministic: it can merge distinct traces.
    Counterexample: Start with two states differing only at x but with different lstates.
    After havoc x with the same value, they have equal pstates but different lstates. -/
theorem havoc_not_deterministic (x : PVar) :
    ¬(⊨ᴴ deterministic, Cmd.havoc x, deterministic) := by
  intro hValid
  -- Construct counterexample
  let ls₁ : LState := fun _ => 0
  let ls₂ : LState := fun _ => 1
  let ps₁ : PState := fun _ => 0
  let ps₂ : PState := PState.update ps₁ x 1
  let σ₁ : ExtState := ⟨ls₁, ps₁⟩
  let σ₂ : ExtState := ⟨ls₂, ps₂⟩
  let S : StateSet := {σ₁, σ₂}
  -- S satisfies deterministic (pstates differ at x)
  have hDet : deterministic S := by
    intro a ha b hb hpeq
    cases ha with
    | inl ha => cases hb with
      | inl hb => rw [ha, hb]
      | inr hb =>
        exfalso
        rw [ha, hb] at hpeq
        have hx : ps₁ x = ps₂ x := congr_fun hpeq x
        simp only [ps₁, ps₂, PState.update_same] at hx
        exact absurd hx (by decide : (0 : Int) ≠ 1)
    | inr ha => cases hb with
      | inl hb =>
        exfalso
        rw [ha, hb] at hpeq
        have hx : ps₂ x = ps₁ x := congr_fun hpeq x
        simp only [ps₁, ps₂, PState.update_same] at hx
        exact absurd hx.symm (by decide : (0 : Int) ≠ 1)
      | inr hb => rw [ha, hb]
  have hPost := hValid S hDet
  -- After havoc x with value 0, both become ps₁
  let σ₁' : ExtState := ⟨ls₁, ps₁⟩
  let σ₂' : ExtState := ⟨ls₂, ps₁⟩
  -- Key observation: ps₁[x ↦ 0] = ps₁ since ps₁ x = 0
  have hps₁_eq : PState.update ps₁ x 0 = ps₁ := by
    funext y
    simp only [PState.update]
    split_ifs with h <;> rfl
  -- ps₂[x ↦ 0] = ps₁ since ps₂ = ps₁[x ↦ 1] and then we set x back to 0
  have hps₂_eq : PState.update ps₂ x 0 = ps₁ := by
    funext y
    simp only [ps₂, PState.update]
    split_ifs with h <;> rfl
  have hσ₁'_in : σ₁' ∈ sem (Cmd.havoc x) S := by
    simp only [sem, Set.mem_setOf_eq]
    refine ⟨σ₁, Or.inl rfl, ?_, rfl⟩
    change BigStep (Cmd.havoc x) ps₁ ps₁
    conv_rhs => rw [← hps₁_eq]
    exact BigStep.havoc ps₁ x 0
  have hσ₂'_in : σ₂' ∈ sem (Cmd.havoc x) S := by
    simp only [sem, Set.mem_setOf_eq]
    refine ⟨σ₂, Or.inr rfl, ?_, rfl⟩
    change BigStep (Cmd.havoc x) ps₂ ps₁
    conv_rhs => rw [← hps₂_eq]
    exact BigStep.havoc ps₂ x 0
  have hpeq' : σ₁'.pstate = σ₂'.pstate := rfl
  have hne' : σ₁' ≠ σ₂' := by
    intro h
    have : σ₁'.lstate = σ₂'.lstate := by rw [h]
    have hls : ls₁ "" = ls₂ "" := congr_fun this ""
    exact absurd hls (by decide : (0 : Int) ≠ 1)
  exact hne' (hPost σ₁' hσ₁'_in σ₂' hσ₂'_in hpeq')

/-- Choice between different assignments is not deterministic.
    Similar to havoc: can merge distinct traces into same pstate. -/
theorem choice_not_deterministic (x : PVar) (v₁ v₂ : PVal) (hne : v₁ ≠ v₂) :
    ¬(⊨ᴴ deterministic,
       Cmd.choice (Cmd.assign x (Expr.const v₁)) (Cmd.assign x (Expr.const v₂)),
       deterministic) := by
  intro hValid
  let ls₁ : LState := fun _ => 0
  let ls₂ : LState := fun _ => 1
  let ps₁ : PState := fun _ => 0
  let ps₂ : PState := PState.update ps₁ x 1
  let σ₁ : ExtState := ⟨ls₁, ps₁⟩
  let σ₂ : ExtState := ⟨ls₂, ps₂⟩
  let S : StateSet := {σ₁, σ₂}
  have hDet : deterministic S := by
    intro a ha b hb hpeq
    cases ha with
    | inl ha => cases hb with
      | inl hb => rw [ha, hb]
      | inr hb =>
        exfalso
        rw [ha, hb] at hpeq
        have hx : ps₁ x = ps₂ x := congr_fun hpeq x
        simp only [ps₁, ps₂, PState.update_same] at hx
        exact absurd hx (by decide : (0 : Int) ≠ 1)
    | inr ha => cases hb with
      | inl hb =>
        exfalso
        rw [ha, hb] at hpeq
        have hx : ps₂ x = ps₁ x := congr_fun hpeq x
        simp only [ps₁, ps₂, PState.update_same] at hx
        exact absurd hx.symm (by decide : (0 : Int) ≠ 1)
      | inr hb => rw [ha, hb]
  have hPost := hValid S hDet
  -- After x := v₁, both have pstate with x = v₁
  let ps_out : PState := PState.update ps₁ x v₁
  let σ₁' : ExtState := ⟨ls₁, ps_out⟩
  let σ₂' : ExtState := ⟨ls₂, ps_out⟩
  have hσ₁'_in : σ₁' ∈ sem (Cmd.choice (Cmd.assign x (Expr.const v₁)) (Cmd.assign x (Expr.const v₂))) S := by
    rw [Sem.choice_sem]; left
    simp only [sem, Set.mem_setOf_eq, σ₁', σ₁, ps_out]
    exact ⟨σ₁, Or.inl rfl, BigStep.assign ps₁ x (Expr.const v₁), rfl⟩
  have hσ₂'_in : σ₂' ∈ sem (Cmd.choice (Cmd.assign x (Expr.const v₁)) (Cmd.assign x (Expr.const v₂))) S := by
    rw [Sem.choice_sem]; left
    simp only [sem, Set.mem_setOf_eq, σ₂', σ₂, ps_out, ps₂]
    refine ⟨σ₂, Or.inr rfl, ?_, rfl⟩
    convert BigStep.assign ps₂ x (Expr.const v₁) using 1
    funext y; simp only [ps₁, ps₂, PState.update, Expr.eval]
    split_ifs <;> rfl
  have hpeq' : σ₁'.pstate = σ₂'.pstate := rfl
  have hne' : σ₁' ≠ σ₂' := by
    intro h
    have : σ₁'.lstate = σ₂'.lstate := by rw [h]
    have hls : ls₁ "" = ls₂ "" := congr_fun this ""
    exact absurd hls (by decide : (0 : Int) ≠ 1)
  exact hne' (hPost σ₁' hσ₁'_in σ₂' hσ₂'_in hpeq')

/-! ## Determinism Under Conditions -/

/-- A restricted determinism that only considers states satisfying a condition -/
def conditionalDeterministic (p : ExtState → Prop) : HyperAssertion :=
  allPairsSatisfy fun σ₁ σ₂ =>
    p σ₁ → p σ₂ → σ₁.pstate = σ₂.pstate → σ₁ = σ₂

/-- Skip preserves conditional determinism -/
theorem skip_cond_det (p : ExtState → Prop) :
    ⊨ᴴ conditionalDeterministic p, Cmd.skip, conditionalDeterministic p := by
  intro S hDet
  rw [Sem.skip_id]
  exact hDet

/-! ## Functional Determinism -/

/-- A program is functionally deterministic if it computes a function -/
def functionallyDeterministic (c : Cmd) : Prop :=
  ∀ σ σ₁' σ₂' : PState,
    BigStep c σ σ₁' → BigStep c σ σ₂' → σ₁' = σ₂'

/-- Skip is functionally deterministic -/
theorem skip_functional : functionallyDeterministic Cmd.skip := by
  intro σ σ₁' σ₂' h₁ h₂
  have eq₁ := BigStep.skip_eq h₁
  have eq₂ := BigStep.skip_eq h₂
  rw [eq₁, eq₂]

/-- Assignment is functionally deterministic -/
theorem assign_functional (x : PVar) (e : Expr) :
    functionallyDeterministic (Cmd.assign x e) := by
  intro σ σ₁' σ₂' h₁ h₂
  have eq₁ := BigStep.assign_eq h₁
  have eq₂ := BigStep.assign_eq h₂
  rw [eq₁, eq₂]

/-- Sequential composition preserves functional determinism -/
theorem seq_functional {c₁ c₂ : Cmd}
    (h₁ : functionallyDeterministic c₁)
    (h₂ : functionallyDeterministic c₂) :
    functionallyDeterministic (Cmd.seq c₁ c₂) := by
  intro σ σ₁' σ₂' hstep₁ hstep₂
  cases hstep₁ with
  | seq _ _ _ σ₁'' _ h₁₁ h₁₂ =>
    cases hstep₂ with
    | seq _ _ _ σ₂'' _ h₂₁ h₂₂ =>
      have heq := h₁ σ σ₁'' σ₂'' h₁₁ h₂₁
      rw [← heq] at h₂₂
      exact h₂ σ₁'' σ₁' σ₂' h₁₂ h₂₂

/-- Havoc is NOT functionally deterministic -/
theorem havoc_not_functional (x : PVar) :
    ¬functionallyDeterministic (Cmd.havoc x) := by
  intro h
  -- havoc x from empty state can produce different results
  let σ := PState.empty
  let σ₀ := PState.update σ x 0
  let σ₁ := PState.update σ x 1
  have h₁ : BigStep (Cmd.havoc x) σ σ₀ := BigStep.havoc σ x 0
  have h₂ : BigStep (Cmd.havoc x) σ σ₁ := BigStep.havoc σ x 1
  have heq := h σ σ₀ σ₁ h₁ h₂
  -- σ₀ ≠ σ₁
  have hne : σ₀ ≠ σ₁ := by
    intro heq'
    have hval : σ₀ x = σ₁ x := congr_fun heq' x
    simp only [σ₀, σ₁, PState.update_same] at hval
    exact absurd hval (by decide : (0 : Int) ≠ 1)
  exact hne heq

open PState in
/-- Choice is NOT functionally deterministic -/
theorem choice_not_functional {c₁ c₂ : Cmd} {σ σ₁' σ₂' : PState}
    (h₁ : BigStep c₁ σ σ₁') (h₂ : BigStep c₂ σ σ₂') (hne : σ₁' ≠ σ₂') :
    ¬functionallyDeterministic (Cmd.choice c₁ c₂) := by
  intro hFun
  have hstep₁ : BigStep (Cmd.choice c₁ c₂) σ σ₁' := BigStep.choiceLeft c₁ c₂ σ σ₁' h₁
  have hstep₂ : BigStep (Cmd.choice c₁ c₂) σ σ₂' := BigStep.choiceRight c₁ c₂ σ σ₂' h₂
  exact hne (hFun σ σ₁' σ₂' hstep₁ hstep₂)

end HHL.Examples
