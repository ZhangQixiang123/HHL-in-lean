/-
  Hyper Hoare Logic - Syntactic Rules and Transformations
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)

  Phase 6: Syntactic Transformations for Assertion Manipulation
-/

import Untitled.Rules.Core

namespace HHL

open PState (update)

/-! ## Expression Substitution

The paper uses syntactic transformations to compute weakest preconditions.
These transformations substitute expressions for variables in assertions.
-/

namespace StateExpr

/-- Convert an Expr to a StateExpr -/
def ofExpr : Expr → StateExpr
  | Expr.const v => const v
  | Expr.var x => pvar x
  | Expr.binop op e₁ e₂ => binop op (ofExpr e₁) (ofExpr e₂)

/-- Substitute a program variable with an expression in a state expression -/
def substExpr (se : StateExpr) (x : PVar) (e : Expr) : StateExpr :=
  match se with
  | const v => const v
  | pvar y => if y = x then ofExpr e else pvar y
  | lvar y => lvar y
  | binop op se₁ se₂ => binop op (se₁.substExpr x e) (se₂.substExpr x e)

/-- ofExpr preserves evaluation -/
theorem ofExpr_eval (e : Expr) (σ : ExtState) :
    (ofExpr e).eval σ = e.eval σ.pstate := by
  induction e with
  | const v => rfl
  | var x => rfl
  | binop op e₁ e₂ ih₁ ih₂ =>
    simp only [ofExpr, eval, Expr.eval, ih₁, ih₂]

/-- Substitution correctness: evaluation after substitution equals
    evaluation with updated state -/
theorem substExpr_correct (se : StateExpr) (x : PVar) (e : Expr) (σ : ExtState) :
    (se.substExpr x e).eval σ = se.eval ⟨σ.lstate, update σ.pstate x (e.eval σ.pstate)⟩ := by
  induction se with
  | const v => rfl
  | pvar y =>
    simp only [substExpr, eval]
    split_ifs with h
    · -- y = x case
      subst h
      simp only [update, ite_true, ofExpr_eval]
    · -- y ≠ x case
      simp only [eval, update, if_neg h]
  | lvar y => rfl
  | binop op se₁ se₂ ih₁ ih₂ =>
    simp only [substExpr, eval, ih₁, ih₂]

end StateExpr

namespace StateFormula

/-- Substitute a program variable with an expression in a state formula -/
def substExpr (φ : StateFormula) (x : PVar) (e : Expr) : StateFormula :=
  match φ with
  | .true => .true
  | .false => .false
  | cmp op se₁ se₂ => cmp op (se₁.substExpr x e) (se₂.substExpr x e)
  | not φ' => not (φ'.substExpr x e)
  | and φ₁ φ₂ => and (φ₁.substExpr x e) (φ₂.substExpr x e)
  | or φ₁ φ₂ => or (φ₁.substExpr x e) (φ₂.substExpr x e)

end StateFormula

/-! ## BExpr to StateFormula Conversion -/

/-- Convert a BExpr to a StateFormula -/
def bexprToFormula : BExpr → StateFormula
  | .tt => StateFormula.true
  | .ff => StateFormula.false
  | .cmp op e₁ e₂ => StateFormula.cmp op (StateExpr.ofExpr e₁) (StateExpr.ofExpr e₂)
  | .not b => StateFormula.not (bexprToFormula b)
  | .and b₁ b₂ => StateFormula.and (bexprToFormula b₁) (bexprToFormula b₂)
  | .or b₁ b₂ => StateFormula.or (bexprToFormula b₁) (bexprToFormula b₂)

/-! ## Syntactic Hyper-Assertion Transformations -/

namespace SynHyperAssertion

/-- Assignment transformation A_x^e[_]: backward substitution for assignments.
    Transforms the postcondition to get the weakest precondition. -/
def transformAssign (x : PVar) (e : Expr) : SynHyperAssertion → SynHyperAssertion
  | forallState l φ A => forallState l (φ.substExpr x e) (transformAssign x e A)
  | existsState l φ A => existsState l (φ.substExpr x e) (transformAssign x e A)
  | prop φ => prop (φ.substExpr x e)
  | pure P => pure P
  | and A₁ A₂ => and (transformAssign x e A₁) (transformAssign x e A₂)
  | or A₁ A₂ => or (transformAssign x e A₁) (transformAssign x e A₂)
  | implies A₁ A₂ => implies (transformAssign x e A₁) (transformAssign x e A₂)

/-- Assume transformation Π_b[_]: adds condition b as a guard.
    Used for assume statements. -/
def transformAssume (b : BExpr) : SynHyperAssertion → SynHyperAssertion
  | forallState l φ A =>
      forallState l (StateFormula.and φ (bexprToFormula b)) (transformAssume b A)
  | existsState l φ A =>
      existsState l (StateFormula.and φ (bexprToFormula b)) (transformAssume b A)
  | prop φ => prop (StateFormula.implies (bexprToFormula b) φ)
  | pure P => pure P
  | and A₁ A₂ => and (transformAssume b A₁) (transformAssume b A₂)
  | or A₁ A₂ => or (transformAssume b A₁) (transformAssume b A₂)
  | implies A₁ A₂ => implies (transformAssume b A₁) (transformAssume b A₂)

/-- Havoc transformation H_x[_]: existentially quantifies over x.
    This is more complex as it needs to introduce a fresh variable. -/
def transformHavoc (x : PVar) (freshVar : LVar) : SynHyperAssertion → SynHyperAssertion
  | forallState l φ A => forallState l φ (transformHavoc x freshVar A)
  | existsState l φ A => existsState l φ (transformHavoc x freshVar A)
  | prop φ => prop φ  -- Simplified: proper implementation needs fresh variable handling
  | pure P => pure P
  | and A₁ A₂ => and (transformHavoc x freshVar A₁) (transformHavoc x freshVar A₂)
  | or A₁ A₂ => or (transformHavoc x freshVar A₁) (transformHavoc x freshVar A₂)
  | implies A₁ A₂ => implies (transformHavoc x freshVar A₁) (transformHavoc x freshVar A₂)

end SynHyperAssertion

/-! ## Soundness of Syntactic Transformations -/

/-- Assignment transformation is sound: transforming the postcondition gives
    the weakest precondition for the assignment. -/
theorem assign_transform_sound {x : PVar} {e : Expr} {A : SynHyperAssertion} :
    ⊨ᴴ (SynHyperAssertion.transformAssign x e A).toHyperAssertion,
       Cmd.assign x e,
       A.toHyperAssertion := by
  intro S hPre
  sorry -- Requires detailed analysis of the interpretation function

/-- Assume transformation is sound -/
theorem assume_transform_sound {b : BExpr} {A : SynHyperAssertion} :
    ⊨ᴴ (SynHyperAssertion.transformAssume b A).toHyperAssertion,
       Cmd.assume b,
       A.toHyperAssertion := by
  intro S hPre
  sorry -- Requires analysis of assume filtering

/-! ## Weakest Precondition Computation -/

/-- Compute the weakest precondition for a command and postcondition -/
def wp (c : Cmd) (Q : SynHyperAssertion) : SynHyperAssertion :=
  match c with
  | Cmd.skip => Q
  | Cmd.assign x e => Q.transformAssign x e
  | Cmd.seq c₁ c₂ => wp c₁ (wp c₂ Q)
  | Cmd.choice c₁ c₂ => SynHyperAssertion.and (wp c₁ Q) (wp c₂ Q)
  | Cmd.assume b => Q.transformAssume b
  | Cmd.havoc x => Q.transformHavoc x "fresh"
  | Cmd.whileLoop _ _ => Q  -- Loops require invariants

/-- Weakest precondition is sound -/
theorem wp_sound (c : Cmd) (Q : SynHyperAssertion) :
    ⊨ᴴ (wp c Q).toHyperAssertion, c, Q.toHyperAssertion := by
  induction c generalizing Q with
  | skip =>
    simp only [wp]
    exact ValidTriple.skip Q.toHyperAssertion
  | assign x e =>
    simp only [wp]
    exact assign_transform_sound
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [wp]
    exact ValidTriple.seq (ih₁ (wp c₂ Q)) (ih₂ Q)
  | choice c₁ c₂ ih₁ ih₂ =>
    simp only [wp]
    intro S ⟨hP₁, hP₂⟩
    rw [Sem.choice_sem]
    sorry -- Requires union-closed condition
  | assume b =>
    simp only [wp]
    exact assume_transform_sound
  | havoc x =>
    simp only [wp]
    intro S hPre
    sorry -- Requires havoc transformation soundness
  | whileLoop b body ih =>
    simp only [wp]
    intro S hPre
    sorry -- Loops need invariants

/-! ## Derived Syntactic Rules -/

/-- Syntactic consequence rule -/
theorem syn_consequence {P P' Q Q' : SynHyperAssertion} {c : Cmd}
    (hPre : ∀ S, P.toHyperAssertion S → P'.toHyperAssertion S)
    (hTriple : ⊨ᴴ P'.toHyperAssertion, c, Q'.toHyperAssertion)
    (hPost : ∀ S, Q'.toHyperAssertion S → Q.toHyperAssertion S) :
    ⊨ᴴ P.toHyperAssertion, c, Q.toHyperAssertion :=
  ValidTriple.consequence hPre hTriple hPost

end HHL
