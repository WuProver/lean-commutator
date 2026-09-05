import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The exact no-epsilon target

The declaration below is a proposition defining the intended goal, not an assertion
that the proposition has been proved. The scoped matrix norm is the Euclidean
operator norm. Both factors have exactly the same index type as the input.
-/

open scoped Matrix.Norms.L2Operator

namespace NoEpsilon

/-- Uniform bounded single-commutator representation in the original dimension. -/
def UniformCommutatorBound : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
    Matrix.trace A = 0 →
      ∃ B C : Matrix (Fin n) (Fin n) ℂ, A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ K * ‖A‖

end NoEpsilon
