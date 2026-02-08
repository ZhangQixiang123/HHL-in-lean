/-
  Hyper Hoare Logic - Completeness
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)

  Phase 9: Relative Completeness of the Proof System
-/

import Untitled.Metatheory.Soundness

namespace HHL

/-! ## Relative Completeness

The proof system is complete relative to an oracle for the underlying logic.
This means that if a triple is valid, it is derivable (assuming we can decide
validity of assertions in the underlying logic).
-/

/-! ## Weakest Liberal Precondition

For completeness, we define the weakest liberal precondition.
-/

/-- Weakest liberal precondition: the weakest P such that {P} c {Q} is valid -/
def wlp (c : Cmd) (Q : HyperAssertion) : HyperAssertion :=
  fun S => Q (sem c S)

/-- wlp is indeed the weakest precondition -/
theorem wlp_valid (c : Cmd) (Q : HyperAssertion) : ⊨ᴴ wlp c Q, c, Q := by
  intro S hPre
  exact hPre

/-- wlp is the weakest: any valid precondition implies wlp -/
theorem wlp_weakest (c : Cmd) (P Q : HyperAssertion)
    (hValid : ⊨ᴴ P, c, Q) : ∀ S, P S → wlp c Q S := by
  intro S hP
  exact hValid S hP

/-! ## Expressibility

For completeness, we need that wlp is expressible in our assertion language.
This is the "relative" part of relative completeness.
-/

/-- Assumption: wlp is expressible for syntactic assertions -/
axiom wlp_expressible : ∀ (c : Cmd) (Q : SynHyperAssertion),
  ∃ P : SynHyperAssertion, P.toHyperAssertion = wlp c Q.toHyperAssertion

/-! ## Completeness Theorem -/

/-- Helper: consequences are derivable when assertions are expressible -/
theorem derive_consequence {P P' Q Q' : HyperAssertion} {c : Cmd}
    (hPre : ∀ S, P S → P' S)
    (hDeriv : Derivable P' c Q')
    (hPost : ∀ S, Q' S → Q S) :
    Derivable P c Q :=
  Derivable.consequence P P' Q Q' c hPre hDeriv hPost

/-- Completeness for skip -/
theorem complete_skip (Q : HyperAssertion) : Derivable Q Cmd.skip Q :=
  Derivable.skip Q

/-- Completeness for sequence -/
theorem complete_seq {P Q R : HyperAssertion} {c₁ c₂ : Cmd}
    (h₁ : Derivable P c₁ Q)
    (h₂ : Derivable Q c₂ R) :
    Derivable P (Cmd.seq c₁ c₂) R :=
  Derivable.seq P Q R c₁ c₂ h₁ h₂

/-- Relative completeness theorem (sketch)

This theorem states that if a hyper-triple is valid, then it is derivable
(assuming expressibility of weakest preconditions).

The proof proceeds by induction on the command structure:
- For skip: use the skip rule
- For seq: use wlp to find the intermediate assertion
- For choice: requires union-closed or ⊗ decomposition
- For assign: use the assign rule with wlp
- For assume: use the assume rule
- For havoc: requires existential reasoning
- For while: requires finding an invariant
-/
theorem relative_completeness {P Q : HyperAssertion} {c : Cmd}
    (hValid : ⊨ᴴ P, c, Q)
    (hExpressP : ∃ P' : SynHyperAssertion, P'.toHyperAssertion = P)
    (hExpressQ : ∃ Q' : SynHyperAssertion, Q'.toHyperAssertion = Q) :
    Derivable P c Q := by
  -- The full proof requires induction on c and careful handling of
  -- the expressibility assumptions
  sorry

/-! ## Completeness for Specific Command Classes -/

/-- Completeness for assignment commands -/
theorem complete_assign {Q : HyperAssertion} {x : PVar} {e : Expr} :
    Derivable (wlp (Cmd.assign x e) Q) (Cmd.assign x e) Q := by
  -- wlp (assign x e) Q = fun S => Q (sem (assign x e) S)
  --                     = fun S => Q (mapPState S (update x (e.eval)))
  apply Derivable.consequence
  · -- P implies the assign precondition
    intro S hP
    -- Need to show mapPState produces the right set
    simp only [wlp] at hP
    -- This requires more detailed analysis
    sorry
  · exact Derivable.assign Q x e
  · intro S hQ
    exact hQ

/-- Completeness for assume commands -/
theorem complete_assume {P : HyperAssertion} {b : BExpr}
    (hDC : downwardClosed P) :
    Derivable P (Cmd.assume b)
      (HyperAssertion.and P (allSatisfy fun σ => b.eval σ.pstate = true)) :=
  Derivable.assume_dc P b hDC

/-! ## Cook's Completeness Result

The relative completeness result can be strengthened to show that
the proof system is complete relative to any sound oracle for the
underlying assertion logic.
-/

/-- Oracle assumption: we can decide validity of assertions -/
class AssertionOracle where
  /-- The oracle can decide if P implies Q -/
  implies : HyperAssertion → HyperAssertion → Bool
  /-- The oracle is sound -/
  sound : ∀ P Q, implies P Q = true → ∀ S, P S → Q S

/-- With an oracle, completeness becomes decidable -/
theorem complete_with_oracle [AssertionOracle] {P Q : HyperAssertion} {c : Cmd}
    (hValid : ⊨ᴴ P, c, Q) :
    Derivable P c Q := by
  -- Using the oracle, we can construct derivations
  sorry

/-! ## Completeness for Syntactic Fragment -/

/-- For the syntactic fragment, completeness is more tractable -/
theorem syntactic_completeness {P Q : SynHyperAssertion} {c : Cmd}
    (hValid : ⊨ᴴ P.toHyperAssertion, c, Q.toHyperAssertion) :
    Derivable P.toHyperAssertion c Q.toHyperAssertion := by
  -- The syntactic fragment has decidable wlp computation
  -- (via the wp function from Syntactic.lean)
  sorry

end HHL
