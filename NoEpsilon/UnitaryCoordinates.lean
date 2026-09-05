import NoEpsilon.OrthonormalCompletion

/-!
# Exact commutator transport through orthonormal coordinates

The coordinate matrices may have different finite index types. Their dimensions agree
because both products with the adjoint are identities.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem isometry_compression_norm_le (U : Matrix ι κ ℂ) (hU : Uᴴ * U = 1)
    (A : Matrix ι ι ℂ) : ‖Uᴴ * A * U‖ ≤ ‖A‖ := by
  have hAdj := norm_isometry_adjoint_le_one U hU
  have hUnit : ‖U‖ ≤ 1 := by rwa [Matrix.l2_opNorm_conjTranspose] at hAdj
  calc
    _ ≤ ‖Uᴴ * A‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Uᴴ‖ * ‖A‖) * ‖U‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖A‖) * 1 := by gcongr
    _ = ‖A‖ := by ring

theorem basis_compression_trace (b : OrthonormalBasis κ ℂ (EuclideanSpace ℂ ι))
    (A : Matrix ι ι ℂ) :
    Matrix.trace ((familyMatrix b)ᴴ * A * familyMatrix b) = Matrix.trace A := by
  rw [Matrix.trace_mul_cycle, (basisMatrix_unitary b).2, Matrix.one_mul]

theorem rectangular_unitary_conjugate_mul (U : Matrix ι κ ℂ) (hU : Uᴴ * U = 1)
    (B C : Matrix κ κ ℂ) :
    (U * B * Uᴴ) * (U * C * Uᴴ) = U * (B * C) * Uᴴ := by
  calc
    _ = U * B * (Uᴴ * U) * C * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * (B * C) * Uᴴ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc U B C]

/-- A commutator in complete orthonormal coordinates pulls back with the same product bound. -/
theorem basis_compression_commutator_pullback (b : OrthonormalBasis κ ℂ (EuclideanSpace ℂ ι))
    (A : Matrix ι ι ℂ) (K : ℝ)
    (h : ∃ B C : Matrix κ κ ℂ, (familyMatrix b)ᴴ * A * familyMatrix b = B * C - C * B ∧
      ‖B‖ * ‖C‖ ≤ K) :
    ∃ B C : Matrix ι ι ℂ, A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ K := by
  let U := familyMatrix b
  obtain ⟨B, C, hBC, hBound⟩ := h
  change Uᴴ * A * U = B * C - C * B at hBC
  have hU := basisMatrix_unitary b
  have hAdj : (Uᴴ)ᴴ * Uᴴ = 1 := by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2
  refine ⟨U * B * Uᴴ, U * C * Uᴴ, ?_, ?_⟩
  · rw [rectangular_unitary_conjugate_mul U hU.1,
      rectangular_unitary_conjugate_mul U hU.1, ← Matrix.sub_mul, ← Matrix.mul_sub, ← hBC]
    calc
      A = (U * Uᴴ) * A * (U * Uᴴ) := by rw [hU.2, Matrix.one_mul, Matrix.mul_one]
      _ = U * (Uᴴ * A * U) * Uᴴ := by simp only [Matrix.mul_assoc]
  · have hB : ‖U * B * Uᴴ‖ ≤ ‖B‖ := by
      simpa only [Matrix.conjTranspose_conjTranspose] using isometry_compression_norm_le Uᴴ hAdj B
    have hC : ‖U * C * Uᴴ‖ ≤ ‖C‖ := by
      simpa only [Matrix.conjTranspose_conjTranspose] using isometry_compression_norm_le Uᴴ hAdj C
    exact (mul_le_mul hB hC (norm_nonneg _) (norm_nonneg _)).trans hBound

end NoEpsilon
