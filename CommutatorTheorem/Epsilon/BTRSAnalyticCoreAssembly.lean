import CommutatorTheorem.Epsilon.BTRSExactMDPHarness
import CommutatorTheorem.Epsilon.BTMDPFinalAssembly

/-!
# Assembly of the exact-MDP analytic core from RS stability

This file replaces the omnibus stability half of `BTMDPAnalyticCore` by the
three precise mathematical statements developed in the stability harness:

* multivariate Gauss--Lucas/Hurwitz closure;
* the finite exact-MDP determinant expansion;
* the root-disjoint pair Fell converse in every degree.

The independent one-coordinate zeroing monotonicity statement is retained,
since it belongs to the root-shrinking comparison rather than stability.
-/

namespace CommutatorTheorem.BTRSAnalyticCoreAssembly

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
  Matrix.instL2OpNormedSpace Matrix.instL2OpNormedRing Matrix.instCStarRing

open scoped Polynomial
open CommutatorTheorem
open CommutatorTheorem.BTRealStabilityClosure
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTMDPSelection
open CommutatorTheorem.BTMDPJointControl
open CommutatorTheorem.BTMDPRootShrinkAssembly
open CommutatorTheorem.BTMDPFinalAssembly
open CommutatorTheorem.BTRSExactMDPHarness

/-- The RS stability package supplies both real-rootedness of the ambient
exact MDP and every conditional deletion interlacing tree. -/
theorem btMDPAnalyticCore_of_rsStability
    (Z : MDPOneCoordinateZeroingMonotonicity)
    (H : MultivariateGaussLucasHurwitz)
    (E : RSExactConditionalMDPExpansion)
    (F : ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d) :
    BTMDPAnalyticCore := by
  refine ⟨Z, ?_⟩
  intro n k hk A hA _hzd _hnorm
  constructor
  · have hnodes := conditionalNodesRealRooted_of_rsExpansion
      (d := n) H E hk A hA
    have hroot := hnodes (Finset.univ : Finset (Fin n)) (by simp)
    rw [normalizedConditionalMDP_univ] at hroot
    simpa using hroot
  · intro d hd hdn
    exact mdpConditionalInterlacing_of_rsExpansion
      H E F hk hd A hA

/-- Equivalent assembly from the smaller base-and-one-deletion finite
determinant expansion. -/
theorem btMDPAnalyticCore_of_rsBaseDeletion
    (Z : MDPOneCoordinateZeroingMonotonicity)
    (H : MultivariateGaussLucasHurwitz)
    (B : RSExactMDPBaseDeletionExpansion)
    (F : ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d) :
    BTMDPAnalyticCore :=
  btMDPAnalyticCore_of_rsStability Z H
    (rsExactConditionalMDPExpansion_of_baseDeletion B) F

/-- Consequently the precise RS package implies the one-sided four-Hermitian
selection theorem with denominator `24`. -/
theorem fourHermitianUpperSelection24_of_rsStability
    (Z : MDPOneCoordinateZeroingMonotonicity)
    (H : MultivariateGaussLucasHurwitz)
    (E : RSExactConditionalMDPExpansion)
    (F : ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d) :
    FourHermitianUpperSelection24 :=
  fourHermitianUpperSelection24_of_mdpAnalyticCore
    (btMDPAnalyticCore_of_rsStability Z H E F)

/-- Final Bourgain--Tzafriri central-submatrix estimate, with the explicit
constant `4 * sqrt 6`, from the four isolated RS/root-shrinking statements. -/
theorem bourgainTzafriri_of_rsStability
    (Z : MDPOneCoordinateZeroingMonotonicity)
    (H : MultivariateGaussLucasHurwitz)
    (E : RSExactConditionalMDPExpansion)
    (F : ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d) :
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ (4 * Real.sqrt 6) * ε * ‖A‖ :=
  bourgainTzafriri_of_mdpAnalyticCore
    (btMDPAnalyticCore_of_rsStability Z H E F)

/-- Final theorem from the smaller base-and-one-deletion expansion. -/
theorem bourgainTzafriri_of_rsBaseDeletion
    (Z : MDPOneCoordinateZeroingMonotonicity)
    (H : MultivariateGaussLucasHurwitz)
    (B : RSExactMDPBaseDeletionExpansion)
    (F : ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d) :
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ (4 * Real.sqrt 6) * ε * ‖A‖ :=
  bourgainTzafriri_of_mdpAnalyticCore
    (btMDPAnalyticCore_of_rsBaseDeletion Z H B F)

end CommutatorTheorem.BTRSAnalyticCoreAssembly
