import CommutatorTheorem.Epsilon.BTRSClosedAssembly
import CommutatorTheorem.Epsilon.BTFellExactDescartes
import CommutatorTheorem.Epsilon.BTFellCountParity
import CommutatorTheorem.Epsilon.BTFellSignLocal
import CommutatorTheorem.Epsilon.BTFellCountLocal
import CommutatorTheorem.Epsilon.BTFellSignWordCrossing
import CommutatorTheorem.Epsilon.BTFellCountInduction
import CommutatorTheorem.Epsilon.BTRootMotionContinuity

/-!
# Automation harness for Bourgain--Tzafriri

This module is the small proof-search boundary for replacing the legacy
`bourgain_tzafriri_central_submatrix` axiom.  All matrix, determinant,
stability, deletion, and spectral arguments are already discharged upstream.
The two goals below are the remaining one-variable statements.

The final theorem in this file is deliberately assembled without importing
`CommutatorTheorem.BourgainTzafriri`, so a successful axiom audit cannot pick
up the legacy assumption accidentally.
-/

namespace CommutatorTheorem.BTAutomationHarness

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
  Matrix.instL2OpNormedSpace Matrix.instL2OpNormedRing Matrix.instCStarRing

open Polynomial
open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTMDPJointControl

/-- Proof-search target A: the affine-pencil root-motion lemma used in RS
Proposition 16. -/
abbrev RootMotionGoal : Prop :=
  AffineRealRootedPencilLargestRootMonotoneFromMoment

/-- Proof-search target B: the root-disjoint Fell converse in every degree
where it is needed by the mixed-characteristic-polynomial argument. -/
abbrev FellConverseGoal : Prop :=
  ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d

/-- The general root-motion target, obtained from moment escape and
continuity of the largest root. -/
theorem rootMotionGoal : RootMotionGoal :=
  CommutatorTheorem.BTRootMotionContinuity.affineRealRootedPencilLargestRootMonotoneFromMoment

/-- The general root-disjoint Fell target, obtained from the degree induction
on half-line root counts. -/
theorem fellConverseGoal : FellConverseGoal :=
  CommutatorTheorem.BTFellCountInduction.rootDisjointPairFellConverseAtDegree_all

/-- The degree-two instance of target A is already closed.  This is a useful
regression test for automated changes to the general root-motion proof. -/
theorem rootMotionGoal_degree_two
    (r s : ℝ[X])
    (hmonic : ∀ t : ℝ, 0 ≤ t → (r + t • s).Monic)
    (hdegree : ∀ t : ℝ, 0 ≤ t → (r + t • s).natDegree = 2)
    (hreal : ∀ t : ℝ, 0 ≤ t → RealRooted (r + t • s))
    (hnext : ∀ t : ℝ, 0 ≤ t → (r + t • s).nextCoeff = r.nextCoeff)
    (hslope : s.coeff 0 < 0) (x : ℝ)
    (hx : IsRootUpperBound (r + s) x) : IsRootUpperBound r x :=
  affineRealRootedPencilLargestRootMonotoneFromMoment_degree_two
    r s hmonic hdegree hreal hnext hslope x hx

/-- Closing the two proof-search targets gives the exact central-submatrix
statement, with the explicit absolute constant `4 * sqrt 6`. -/
theorem bourgain_tzafriri_central_submatrix_of_goals
    (rootMotion : RootMotionGoal) (fellConverse : FellConverseGoal) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
        ZeroDiag A →
        ∀ (ε : ℝ), 0 < ε → ε < 1 →
          ∃ f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m,
            Function.Injective f ∧
            ‖A.submatrix f f‖ ≤ K * ε * ‖A‖ := by
  refine ⟨4 * Real.sqrt 6, by positivity, ?_⟩
  exact CommutatorTheorem.BTRSClosedAssembly.bourgainTzafriri_of_rootMotion
    rootMotion fellConverse

end CommutatorTheorem.BTAutomationHarness
