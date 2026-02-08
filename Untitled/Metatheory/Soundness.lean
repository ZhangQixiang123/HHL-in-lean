/-
  Hyper Hoare Logic - Soundness
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)

  Phase 8: Soundness of the Proof System
-/

import Untitled.Rules.Loop

namespace HHL

/-! ## Derivability Relation

The derivability relation defines which hyper-triples can be derived
using the inference rules of Hyper Hoare Logic.
-/

/-- Derivable hyper-triples: the proof system -/
inductive Derivable : HyperAssertion → Cmd → HyperAssertion → Prop where
  /-- Skip rule -/
  | skip : ∀ P, Derivable P Cmd.skip P

  /-- Sequence rule -/
  | seq : ∀ P Q R c₁ c₂,
      Derivable P c₁ Q →
      Derivable Q c₂ R →
      Derivable P (Cmd.seq c₁ c₂) R

  /-- Choice rule (with union-closed postcondition) -/
  | choice : ∀ P Q c₁ c₂,
      unionClosed Q →
      Derivable P c₁ Q →
      Derivable P c₂ Q →
      Derivable P (Cmd.choice c₁ c₂) Q

  /-- Consequence rule -/
  | consequence : ∀ P P' Q Q' c,
      (∀ S, P S → P' S) →
      Derivable P' c Q' →
      (∀ S, Q' S → Q S) →
      Derivable P c Q

  /-- Assume rule (with downward-closed precondition) -/
  | assume_dc : ∀ P b,
      downwardClosed P →
      Derivable P (Cmd.assume b)
        (HyperAssertion.and P (allSatisfy fun σ => b.eval σ.pstate = true))

  /-- Assign rule -/
  | assign : ∀ Q x e,
      Derivable (fun S => Q (StateSet.mapPState S (fun σ => PState.update σ x (e.eval σ))))
                (Cmd.assign x e) Q

  /-- Conjunction rule -/
  | conj : ∀ P Q₁ Q₂ c,
      Derivable P c Q₁ →
      Derivable P c Q₂ →
      Derivable P c (HyperAssertion.and Q₁ Q₂)

  /-- Disjunction rule -/
  | disj : ∀ P₁ P₂ Q c,
      Derivable P₁ c Q →
      Derivable P₂ c Q →
      Derivable (HyperAssertion.or P₁ P₂) c Q

  /-- Iteration rule -/
  | iter : ∀ P c n,
      Derivable P c P →
      Derivable P (iterN c n) P

  /-- While rule (partial correctness with downward-closed invariant) -/
  | whileLoop : ∀ I b body,
      downwardClosed I →
      Derivable (HyperAssertion.and I (allSatisfy fun σ => b.eval σ.pstate = true)) body I →
      Derivable I (Cmd.whileLoop b body)
        (HyperAssertion.and I (allSatisfy fun σ => b.eval σ.pstate = false))

notation:25 P " ⊢ᴴ " c " : " Q => Derivable P c Q

/-! ## Soundness Theorem

Every derivable triple is valid (semantically true).
-/

/-- Main soundness theorem -/
theorem soundness {P : HyperAssertion} {c : Cmd} {Q : HyperAssertion} :
    Derivable P c Q → ⊨ᴴ P, c, Q := by
  intro hDeriv
  induction hDeriv with
  | skip P =>
    exact ValidTriple.skip P
  | seq P Q R c₁ c₂ _ _ ih₁ ih₂ =>
    exact ValidTriple.seq ih₁ ih₂
  | choice P Q c₁ c₂ hUC _ _ ih₁ ih₂ =>
    exact ValidTriple.choice_unionClosed hUC ih₁ ih₂
  | consequence P P' Q Q' c hPre _ hPost ih =>
    exact ValidTriple.consequence hPre ih hPost
  | assume_dc P b hDC =>
    exact ValidTriple.assume_rule_dc hDC
  | assign Q x e =>
    exact ValidTriple.assign_wp
  | conj P Q₁ Q₂ c _ _ ih₁ ih₂ =>
    exact ValidTriple.conj_rule ih₁ ih₂
  | disj P₁ P₂ Q c _ _ ih₁ ih₂ =>
    exact ValidTriple.disj_rule ih₁ ih₂
  | iter P c n _ ih =>
    exact ValidTriple.iter ih n
  | whileLoop I b body hDC _ ih =>
    exact while_partial hDC ih

/-! ## Derived Soundness Results -/

/-- Soundness for the tensor choice rule -/
theorem soundness_choice_tensor {P Q₁ Q₂ : HyperAssertion} {c₁ c₂ : Cmd}
    (h₁ : Derivable P c₁ Q₁) (h₂ : Derivable P c₂ Q₂) :
    ⊨ᴴ P, (Cmd.choice c₁ c₂), (Q₁ ⊗ Q₂) := by
  exact ValidTriple.choice_tensor (soundness h₁) (soundness h₂)

/-- Soundness for if-then-else -/
theorem soundness_ite {P Q : HyperAssertion} {b : BExpr} {c₁ c₂ : Cmd}
    (hDC : downwardClosed P)
    (hUC : unionClosed Q)
    (h₁ : Derivable (HyperAssertion.and P (allSatisfy fun σ => b.eval σ.pstate = true)) c₁ Q)
    (h₂ : Derivable (HyperAssertion.and P (allSatisfy fun σ => b.eval σ.pstate = false)) c₂ Q) :
    ⊨ᴴ P, (Cmd.ite b c₁ c₂), Q := by
  exact ite_triple_dc hDC hUC (soundness h₁) (soundness h₂)

/-! ## Soundness for Syntactic Assertions -/

/-- Soundness when working with syntactic hyper-assertions -/
theorem soundness_syntactic {P Q : SynHyperAssertion} {c : Cmd}
    (hDeriv : Derivable P.toHyperAssertion c Q.toHyperAssertion) :
    ⊨ᴴ P.toHyperAssertion, c, Q.toHyperAssertion :=
  soundness hDeriv

end HHL
