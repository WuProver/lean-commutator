import CommutatorTheorem.NoEpsilon.ExplicitBound

-- Explicit @ applications expose all arguments, including possible implicit parameters.
#check @NoEpsilon.commutator_bound_two_pow_3200
#check @NoEpsilon.commutator_bound_two_pow_3200_euclideanOperatorNorm
#print axioms NoEpsilon.Absorption.eliminate_simultaneously
#print axioms NoEpsilon.identityCornerNormBudget_le_monomial
#print axioms NoEpsilon.simultaneousBudget_fixed_le
#print axioms NoEpsilon.highMassNormBudget_fixed_le
#print axioms NoEpsilon.globalNormBudget_le_explicit
#print axioms NoEpsilon.commutator_bound_two_pow_3200
#print axioms NoEpsilon.commutator_bound_two_pow_3200_euclideanOperatorNorm

open scoped Matrix.Norms.L2Operator
-- A second, independent statement check fixes the literal bound and original dimension.
example (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : Matrix.trace A = 0) :
    ∃ B C : Matrix (Fin n) (Fin n) ℂ,
      A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ (2 : ℝ) ^ 3200 * ‖A‖ :=
  NoEpsilon.commutator_bound_two_pow_3200 n A hA
