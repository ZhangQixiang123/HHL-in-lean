/-
  Hyper Hoare Logic - Hyper-Assertions
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)
-/

import Untitled.Lang.Semantics

/-!
# Phase 3: Hyper-Assertions

This file defines hyper-assertions, which are predicates over sets of extended states.
Unlike classical Hoare logic assertions (predicates over single states),
hyper-assertions can express relationships between multiple executions.

We provide both:
- Semantic hyper-assertions (arbitrary predicates over state sets)
- Syntactic hyper-assertions (a restricted syntax for decidability/automation)
-/

namespace HHL

/-! ## Semantic Hyper-Assertions -/

/-- A hyper-assertion is a predicate over sets of extended states -/
def HyperAssertion := StateSet → Prop

namespace HyperAssertion

/-- The trivially true hyper-assertion -/
def true : HyperAssertion := fun _ => True

/-- The trivially false hyper-assertion -/
def false : HyperAssertion := fun _ => False

/-- Conjunction of hyper-assertions -/
def and (P Q : HyperAssertion) : HyperAssertion :=
  fun S => P S ∧ Q S

/-- Disjunction of hyper-assertions -/
def or (P Q : HyperAssertion) : HyperAssertion :=
  fun S => P S ∨ Q S

/-- Negation of a hyper-assertion -/
def not (P : HyperAssertion) : HyperAssertion :=
  fun S => ¬P S

/-- Implication of hyper-assertions -/
def implies (P Q : HyperAssertion) : HyperAssertion :=
  fun S => P S → Q S

/-- Universal quantification over a type -/
def forall' {α : Type*} (P : α → HyperAssertion) : HyperAssertion :=
  fun S => ∀ a, P a S

/-- Existential quantification over a type -/
def exists' {α : Type*} (P : α → HyperAssertion) : HyperAssertion :=
  fun S => ∃ a, P a S

instance : AndOp HyperAssertion := ⟨and⟩
instance : OrOp HyperAssertion := ⟨or⟩

/-- Entailment between hyper-assertions -/
def entails (P Q : HyperAssertion) : Prop :=
  ∀ S, P S → Q S

notation:25 P " ⊢ " Q => entails P Q

theorem entails_refl (P : HyperAssertion) : P ⊢ P := fun _ h => h

theorem entails_trans {P Q R : HyperAssertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  fun S hP => h₂ S (h₁ S hP)

end HyperAssertion

/-! ## Common Hyper-Assertions -/

/-- The set is empty -/
def isEmpty : HyperAssertion := fun S => S = ∅

/-- The set is non-empty -/
def isNonEmpty : HyperAssertion := fun S => S.Nonempty

/-- The set is a singleton -/
def isSingleton : HyperAssertion := fun S => ∃ σ, S = {σ}

/-- All states in the set satisfy a property -/
def allSatisfy (P : ExtState → Prop) : HyperAssertion :=
  fun S => ∀ σ ∈ S, P σ

/-- Some state in the set satisfies a property -/
def someSatisfy (P : ExtState → Prop) : HyperAssertion :=
  fun S => ∃ σ ∈ S, P σ

/-- All pairs of states satisfy a relation -/
def allPairsSatisfy (R : ExtState → ExtState → Prop) : HyperAssertion :=
  fun S => ∀ σ₁ ∈ S, ∀ σ₂ ∈ S, R σ₁ σ₂

/-- Some pair of states satisfies a relation -/
def somePairSatisfies (R : ExtState → ExtState → Prop) : HyperAssertion :=
  fun S => ∃ σ₁ ∈ S, ∃ σ₂ ∈ S, R σ₁ σ₂

/-! ## Example Hyper-Assertions for Security Properties -/

/-- Determinism: all states with the same input have the same output.
    Here we check that states with equal program states are equal. -/
def deterministic : HyperAssertion :=
  allPairsSatisfy fun σ₁ σ₂ => σ₁.pstate = σ₂.pstate → σ₁ = σ₂

/-- Non-interference: low-equivalent inputs produce low-equivalent outputs -/
def nonInterference (low : LowVars) : HyperAssertion :=
  allPairsSatisfy fun σ₁ σ₂ => lowEquiv low σ₁.pstate σ₂.pstate

/-- Generalized non-interference (GNI) -/
def GNI (low : LowVars) : HyperAssertion :=
  fun S => ∀ σ₁ ∈ S, ∀ σ₂ ∈ S,
    lowEquiv low σ₁.pstate σ₂.pstate →
    ∃ σ₃ ∈ S, σ₃.pstate = σ₂.pstate

/-! ## Syntactic Hyper-Assertions (Section 4 of paper) -/

/-- State expressions: expressions that can refer to program or logical variables -/
inductive StateExpr where
  | const : PVal → StateExpr
  | pvar : PVar → StateExpr           -- program variable
  | lvar : LVar → StateExpr           -- logical variable
  | binop : BinOp → StateExpr → StateExpr → StateExpr
deriving Repr

namespace StateExpr

/-- Evaluate a state expression in an extended state -/
def eval : StateExpr → ExtState → PVal
  | const v, _ => v
  | pvar x, σ => σ.pstate x
  | lvar x, σ => σ.lstate x
  | binop op e₁ e₂, σ => op.eval (e₁.eval σ) (e₂.eval σ)

end StateExpr

/-- State formulas: formulas over a single extended state -/
inductive StateFormula where
  | true : StateFormula
  | false : StateFormula
  | cmp : CmpOp → StateExpr → StateExpr → StateFormula
  | not : StateFormula → StateFormula
  | and : StateFormula → StateFormula → StateFormula
  | or : StateFormula → StateFormula → StateFormula
deriving Repr

namespace StateFormula

/-- Evaluate a state formula in an extended state -/
def eval : StateFormula → ExtState → Bool
  | true, _ => .true
  | false, _ => .false
  | cmp op e₁ e₂, σ => op.eval (e₁.eval σ) (e₂.eval σ)
  | not φ, σ => !(φ.eval σ)
  | and φ₁ φ₂, σ => φ₁.eval σ && φ₂.eval σ
  | or φ₁ φ₂, σ => φ₁.eval σ || φ₂.eval σ

/-- Semantic interpretation as a predicate -/
def toProp (φ : StateFormula) : ExtState → Prop :=
  fun σ => φ.eval σ = .true

-- Convenient constructors
def eq (e₁ e₂ : StateExpr) : StateFormula := cmp .eq e₁ e₂
def ne (e₁ e₂ : StateExpr) : StateFormula := cmp .ne e₁ e₂
def lt (e₁ e₂ : StateExpr) : StateFormula := cmp .lt e₁ e₂
def le (e₁ e₂ : StateExpr) : StateFormula := cmp .le e₁ e₂
def gt (e₁ e₂ : StateExpr) : StateFormula := cmp .gt e₁ e₂
def ge (e₁ e₂ : StateExpr) : StateFormula := cmp .ge e₁ e₂

def implies (φ₁ φ₂ : StateFormula) : StateFormula := or (not φ₁) φ₂

end StateFormula

/-- Syntactic hyper-assertions: a restricted syntax with quantifiers over states.
    - `forallState l φ A`: for all states σ satisfying φ, bind σ to logical var l and check A
    - `existsState l φ A`: exists a state σ satisfying φ, bind σ to logical var l and check A
    - `prop φ`: a state formula that must hold (checked on each state individually)
    - `pure P`: a pure proposition (independent of states) -/
inductive SynHyperAssertion where
  | forallState : LVar → StateFormula → SynHyperAssertion → SynHyperAssertion
  | existsState : LVar → StateFormula → SynHyperAssertion → SynHyperAssertion
  | prop : StateFormula → SynHyperAssertion
  | pure : Prop → SynHyperAssertion
  | and : SynHyperAssertion → SynHyperAssertion → SynHyperAssertion
  | or : SynHyperAssertion → SynHyperAssertion → SynHyperAssertion
  | implies : SynHyperAssertion → SynHyperAssertion → SynHyperAssertion

namespace SynHyperAssertion

/-- Semantic interpretation of syntactic hyper-assertions.
    The interpretation depends on:
    - S: the set of states we're asserting over
    - ls: the current logical state (bindings of logical variables) -/
def interp : SynHyperAssertion → StateSet → LState → Prop
  | forallState l φ A, S, ls =>
      ∀ σ ∈ S, φ.toProp σ → A.interp S (LState.update ls l (σ.pstate "x"))  -- simplified binding
  | existsState l φ A, S, ls =>
      ∃ σ ∈ S, φ.toProp σ ∧ A.interp S (LState.update ls l (σ.pstate "x"))  -- simplified binding
  | prop φ, S, _ =>
      ∀ σ ∈ S, φ.toProp σ
  | pure P, _, _ => P
  | and A₁ A₂, S, ls => A₁.interp S ls ∧ A₂.interp S ls
  | or A₁ A₂, S, ls => A₁.interp S ls ∨ A₂.interp S ls
  | implies A₁ A₂, S, ls => A₁.interp S ls → A₂.interp S ls

/-- Convert a syntactic hyper-assertion to a semantic one -/
def toHyperAssertion (A : SynHyperAssertion) : HyperAssertion :=
  fun S => A.interp S LState.empty

end SynHyperAssertion

/-! ## The ⊗ Operator (for loop rules) -/

/-- The tensor operator combines two hyper-assertions by partitioning states.
    (P ⊗ Q)(S) holds iff S can be split into S₁ ∪ S₂ where P(S₁) and Q(S₂) -/
def otimes (P Q : HyperAssertion) : HyperAssertion :=
  fun S => ∃ S₁ S₂, S = S₁ ∪ S₂ ∧ P S₁ ∧ Q S₂

infixl:70 " ⊗ " => otimes

/-- Indexed tensor: combine assertions for each natural number -/
def otimesNat (Q : ℕ → HyperAssertion) : HyperAssertion :=
  fun S => ∃ f : ℕ → StateSet, S = ⋃ n, f n ∧ ∀ n, Q n (f n)

notation "⊗ᵢ" => otimesNat

namespace Otimes

theorem comm (P Q : HyperAssertion) : ∀ S, (P ⊗ Q) S → (Q ⊗ P) S := by
  intro S ⟨S₁, S₂, heq, hP, hQ⟩
  exact ⟨S₂, S₁, by rw [heq, Set.union_comm], hQ, hP⟩

theorem assoc (P Q R : HyperAssertion) :
    ∀ S, ((P ⊗ Q) ⊗ R) S → (P ⊗ (Q ⊗ R)) S := by
  intro S ⟨S₁₂, S₃, heq₁, ⟨S₁, S₂, heq₂, hP, hQ⟩, hR⟩
  refine ⟨S₁, S₂ ∪ S₃, ?_, hP, ⟨S₂, S₃, rfl, hQ, hR⟩⟩
  rw [heq₁, heq₂, Set.union_assoc]

theorem unit_left (P : HyperAssertion) :
    ∀ S, (isEmpty ⊗ P) S → P S := by
  intro S ⟨S₁, S₂, heq, hempty, hP⟩
  simp [isEmpty] at hempty
  rw [heq, hempty, Set.empty_union]
  exact hP

end Otimes

/-! ## Lifting Classical Assertions to Hyper-Assertions -/

/-- A classical assertion (predicate over single program states) -/
def Assertion := PState → Prop

/-- Lift a classical assertion to a hyper-assertion:
    all states in the set satisfy the assertion -/
def liftAssertion (P : Assertion) : HyperAssertion :=
  fun S => ∀ σ ∈ S, P σ.pstate

/-- Notation for lifted assertions -/
notation "⟦" P "⟧" => liftAssertion P

theorem lift_and (P Q : Assertion) :
    (⟦fun σ => P σ ∧ Q σ⟧ : HyperAssertion) = HyperAssertion.and ⟦P⟧ ⟦Q⟧ := by
  funext S
  simp only [liftAssertion, HyperAssertion.and]
  apply propext
  constructor
  · intro h
    exact ⟨fun σ hσ => (h σ hσ).1, fun σ hσ => (h σ hσ).2⟩
  · intro ⟨h₁, h₂⟩ σ hσ
    exact ⟨h₁ σ hσ, h₂ σ hσ⟩

end HHL
