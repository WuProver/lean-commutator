import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Scalar contraction estimate

The final matrix induction uses this estimate directly. The historical namespace and
statement are retained for compatibility with the abstract induction interface.
-/

namespace CommutatorTheorem.NoEpsilon

/-- The exact numerical constants used in the candidate proof satisfy the contraction
budget whenever the global constant dominates twice the additive assembly cost. -/
theorem candidate_budget_closes (K : ℝ) (hK : (2 : ℝ) ^ 43 ≤ K) :
    (8 * 8192 : ℝ) * (319 / (2 : ℝ) ^ 26) * K + (2 : ℝ) ^ 42 ≤ K := by
  norm_num at hK ⊢
  linarith

end CommutatorTheorem.NoEpsilon
