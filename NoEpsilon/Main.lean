import NoEpsilon.GlobalInduction
import NoEpsilon.LowMassTheorem
import NoEpsilon.GoalSemantics

/-! # The dimension-independent single-commutator theorem

Every trace-zero complex matrix is one commutator of matrices in its original
dimension, with a universal product bound in the Euclidean operator norm.
All branch inputs are proved in the imported modules.
-/

namespace NoEpsilon

open scoped Matrix.Norms.L2Operator

theorem lowMassPavingInput_proved : lowMassPavingInput := by
  intro k hk A hNorm hTrace hLow
  exact normalized_low_mass_paving (k := k) (h := 26) hk A hNorm hTrace hLow

/-- The complete epsilon-free theorem, with no additional mathematical hypotheses. -/
theorem uniformCommutatorBound : UniformCommutatorBound :=
  uniformCommutatorBound_of_lowMassPaving lowMassPavingInput_proved

/-- The same theorem stated using the continuous-linear-map Euclidean operator norm. -/
theorem uniformCommutatorBound_euclideanOperatorNorm :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace A = 0 →
        ∃ B C : Matrix (Fin n) (Fin n) ℂ,
          A = B * C - C * B ∧
          ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B‖ *
            ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) C‖ ≤
            K * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ :=
  uniformCommutatorBound_iff_euclideanOperatorNorm.mp uniformCommutatorBound

end NoEpsilon
