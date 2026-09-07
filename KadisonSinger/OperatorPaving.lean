import KadisonSinger.Infinite
import KadisonSinger.FiniteCompression

/-!
# Paving bounded operators on the canonical countable Hilbert space
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace KadisonSinger

/-- The coordinate kernel of a self-adjoint bounded operator is Hermitian. -/
theorem matrixEntry_isHermitian (A : Operator) (hA : IsSelfAdjoint A) :
    Matrix.IsHermitian (matrixEntry A) := by
  ext i j
  change star (matrixEntry A j i) = matrixEntry A i j
  have h := ContinuousLinearMap.adjoint_inner_left A (basisVector j) (basisVector i)
  change inner ℂ ((star A) (basisVector i)) (basisVector j) =
    inner ℂ (basisVector i) (A (basisVector j)) at h
  rw [hA.star_eq] at h
  simpa [matrixEntry, basisVector, lp.inner_single_left, lp.inner_single_right] using h

/-- Matrix entries of left and right multiplication by diagonal operators. -/
theorem matrixEntry_diagonal_mul (a b : Diagonal) (A : Operator) (i j : ℕ) :
    matrixEntry (diagonalRepresentation a * A * diagonalRepresentation b) i j =
      a i * matrixEntry A i j * b j := by
  have hb : diagonalRepresentation b (basisVector j) = b j • basisVector j := by
    ext k
    by_cases h : k = j <;> simp [h]
  change (diagonalRepresentation a) (A (diagonalRepresentation b (basisVector j))) i = _
  rw [hb, map_smul, diagonalRepresentation_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, matrixEntry]
  ring

/-- Infinite operator compressions have precisely the masked finite principal sections. -/
theorem finiteSection_color_compression {r : ℕ} (c : ℕ → Fin r) (j : Fin r)
    (A : Operator) (s : Finset ℕ) :
    finiteSection (matrixEntry (diagonalRepresentation (colorIndicator c j) * A *
      diagonalRepresentation (colorIndicator c j))) s =
      PavingSeparation.compression
        (PavingSeparation.colorClass (fun i : s ↦ c i) j) (finiteSection (matrixEntry A) s) := by
  ext a b
  simp only [finiteSection, Matrix.submatrix_apply, matrixEntry_diagonal_mul,
    colorIndicator_apply, PavingSeparation.compression_apply, PavingSeparation.mem_colorClass]
  split_ifs <;> simp_all

/-- Anderson paving for bounded self-adjoint zero-diagonal operators on `ℓ²(ℕ)`,
with a number of coordinate projections depending only on the error. -/
theorem selfAdjoint_operator_paving (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ ∀ A : Operator, IsSelfAdjoint A →
      (∀ i, matrixEntry A i i = 0) → ∃ c : ℕ → Fin r, ∀ j,
        ‖diagonalRepresentation (colorIndicator c j) * A *
          diagonalRepresentation (colorIndicator c j)‖ ≤ ε * ‖A‖ := by
  obtain ⟨r, hr, hp⟩ := hermitian_kernel_paving ε hε
  refine ⟨r, hr, fun A hA hdiag ↦ ?_⟩
  obtain ⟨c, hc⟩ := hp ℕ (matrixEntry A) (matrixEntry_isHermitian A hA) hdiag
    ‖A‖ (finiteSection_norm_le A)
  refine ⟨c, fun j ↦ ?_⟩
  apply norm_le_of_finiteSection _ (ε * ‖A‖) (mul_nonneg hε.le (norm_nonneg A))
  intro s
  change ‖finiteSection (matrixEntry (diagonalRepresentation (colorIndicator c j) * A *
    diagonalRepresentation (colorIndicator c j))) s‖ ≤ ε * ‖A‖
  rw [finiteSection_color_compression]
  exact hc s j

end KadisonSinger
