import CommutatorTheorem.Epsilon.BTRSAnalyticCoreAssembly
import CommutatorTheorem.Epsilon.BTRSBaseExpansionClose
import CommutatorTheorem.Epsilon.BTGaussLucasHurwitz

/-!
# Assembly after closing exact-MDP expansion and multivariate Gauss--Lucas

Only the root-shrinking comparison inputs remain explicit here.
-/

namespace CommutatorTheorem.BTRSClosedAssembly

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
  Matrix.instL2OpNormedSpace Matrix.instL2OpNormedRing Matrix.instCStarRing

open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTMDPJointControl
open CommutatorTheorem.BTMDPRootShrinkAssembly
open CommutatorTheorem.BTMDPFinalAssembly
open CommutatorTheorem.BTRSAnalyticCoreAssembly
open CommutatorTheorem.BTRSExactMDPHarness

/-- Exact MDP real-rootedness is already unconditional after the finite
determinant expansion and multivariate Gauss--Lucas closure proved in the
preceding files.  Keeping this theorem separate makes the remaining
one-variable root-motion input completely explicit. -/
theorem exactMDPRealRootedness : ExactMDPRealRootedness := by
  intro n k hk A hA
  have hnodes := conditionalNodesRealRooted_of_rsExpansion
    (d := n) BTGaussLucasHurwitz.multivariateGaussLucasHurwitz
    (rsExactConditionalMDPExpansion_of_baseDeletion
      BTRSBaseExpansionClose.rsExactMDPBaseDeletionExpansion)
    hk A hA
  have hroot := hnodes (Finset.univ : Finset (Fin n)) (by simp)
  rw [normalizedConditionalMDP_univ] at hroot
  simpa using hroot

/-- RS Proposition 16 after discharging its exact-MDP real-rootedness
premise.  Only the generic affine root-motion theorem remains. -/
theorem mdpOneCoordinateZeroingMonotonicity
    (R : AffineRealRootedPencilLargestRootMonotoneFromMoment) :
    MDPOneCoordinateZeroingMonotonicity :=
  mdpOneCoordinateZeroingMonotonicity_of_rootMotion R
    exactMDPRealRootedness

/-- The exact-MDP analytic core after discharging both the determinant
expansion and multivariate stability assumptions. -/
theorem btMDPAnalyticCore
    (Z : MDPOneCoordinateZeroingMonotonicity)
    (F : ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d) :
    BTMDPAnalyticCore :=
  btMDPAnalyticCore_of_rsBaseDeletion Z
    BTGaussLucasHurwitz.multivariateGaussLucasHurwitz
    BTRSBaseExpansionClose.rsExactMDPBaseDeletionExpansion F

/-- The same analytic core with Proposition 16 supplied by the isolated
one-variable root-motion theorem. -/
theorem btMDPAnalyticCore_of_rootMotion
    (R : AffineRealRootedPencilLargestRootMonotoneFromMoment)
    (F : ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d) :
    BTMDPAnalyticCore :=
  btMDPAnalyticCore (mdpOneCoordinateZeroingMonotonicity R) F

/-- The one-sided four-Hermitian selection theorem now depends only on the
two root-shrinking comparison statements. -/
theorem fourHermitianUpperSelection24
    (Z : MDPOneCoordinateZeroingMonotonicity)
    (F : ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d) :
    FourHermitianUpperSelection24 :=
  fourHermitianUpperSelection24_of_mdpAnalyticCore
    (btMDPAnalyticCore Z F)

/-- Bourgain--Tzafriri with explicit constant `4 * sqrt 6`, after closing
all real-stability and finite determinant-expansion inputs. -/
theorem bourgainTzafriri
    (Z : MDPOneCoordinateZeroingMonotonicity)
    (F : ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d) :
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ (4 * Real.sqrt 6) * ε * ‖A‖ :=
  bourgainTzafriri_of_mdpAnalyticCore (btMDPAnalyticCore Z F)

/-- Bourgain--Tzafriri reduced to two purely one-variable real-root
comparison theorems; all multivariate stability and determinant algebra is
now discharged. -/
theorem bourgainTzafriri_of_rootMotion
    (R : AffineRealRootedPencilLargestRootMonotoneFromMoment)
    (F : ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d) :
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ (4 * Real.sqrt 6) * ε * ‖A‖ :=
  bourgainTzafriri
    (mdpOneCoordinateZeroingMonotonicity R) F

end CommutatorTheorem.BTRSClosedAssembly
