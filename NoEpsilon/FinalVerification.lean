import NoEpsilon.Main

open scoped Matrix.Norms.L2Operator

/-! The expanded public statement is checked directly, independently of its proposition name. -/

example : ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
    Matrix.trace A = 0 →
      ∃ B C : Matrix (Fin n) (Fin n) ℂ,
        A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ K * ‖A‖ :=
  NoEpsilon.uniformCommutatorBound

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A‖ = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ := rfl

#check NoEpsilon.uniformCommutatorBound
#print axioms NoEpsilon.uniformCommutatorBound
#print axioms NoEpsilon.uniformCommutatorBound_euclideanOperatorNorm
