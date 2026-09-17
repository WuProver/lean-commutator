import CommutatorTheorem.NoEpsilon.GlobalAssembly
import CommutatorTheorem.NoEpsilon.HighMassTheorem

/-! # Homogeneity, coordinates, and the small dimensions -/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem commutator_reindex_pullback (A : Matrix ι ι ℂ) (e : κ ≃ ι) (p : ℝ)
    (h : ∃ B C : Matrix κ κ ℂ, A.submatrix e e = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ p) :
    ∃ B C : Matrix ι ι ℂ, A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ p := by
  obtain ⟨B, C, heq, hnorm⟩ := h
  refine ⟨B.submatrix e.symm e.symm, C.submatrix e.symm e.symm, ?_, ?_⟩
  · have h := congrArg (fun M : Matrix κ κ ℂ ↦ M.submatrix e.symm e.symm) heq
    simpa [Matrix.submatrix_submatrix, Matrix.submatrix_sub,
      Matrix.submatrix_mul_equiv] using h
  · simpa only [submatrix_operator_norm_equiv] using hnorm

omit [Fintype κ] [DecidableEq κ] in
theorem commutator_smul (A : Matrix ι ι ℂ) (c : ℝ) (p : ℝ)
    (h : ∃ B C : Matrix ι ι ℂ, A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ p) :
    ∃ B C : Matrix ι ι ℂ, (c : ℂ) • A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ |c| * p := by
  obtain ⟨B, C, heq, hnorm⟩ := h
  refine ⟨(c : ℂ) • B, C, ?_, ?_⟩
  · simp only [heq, smul_sub, smul_mul_assoc, mul_smul_comm]
  · simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc] using
      mul_le_mul_of_nonneg_left hnorm (abs_nonneg c)

omit [Fintype κ] [DecidableEq κ] in
theorem normalized_matrix_norm (A : Matrix ι ι ℂ) (hA : A ≠ 0) :
    ‖((‖A‖⁻¹ : ℝ) : ℂ) • A‖ = 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg
    A))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA)

omit [Fintype κ] [DecidableEq κ] in
theorem commutator_of_normalized (A : Matrix ι ι ℂ) (hA : A ≠ 0) (p : ℝ)
    (h : ∃ B C : Matrix ι ι ℂ, ((‖A‖⁻¹ : ℝ) : ℂ) • A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ p) :
    ∃ B C : Matrix ι ι ℂ, A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ p * ‖A‖ := by
  have hn := norm_ne_zero_iff.mpr hA
  simpa [smul_smul, hn, abs_of_nonneg (norm_nonneg A), mul_comm p] using
    commutator_smul (((‖A‖⁻¹ : ℝ) : ℂ) • A) ‖A‖ p h

def singletonPartitionEquiv (n : ℕ) : Fin n ≃ Sigma (fun _ : Fin n ↦ Fin 1) where
  toFun i := ⟨i, 0⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨i, j⟩; simp [Fin.eq_zero j]

/-- Small zero-diagonal matrices are assembled directly from singleton zero blocks. -/
theorem zeroDiag_small_commutator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hz : ∀ i, A i i = 0) (hn : n ≤ 2 * 2 ^ 26 - 1) :
    ∃ B C : Matrix (Fin n) (Fin n) ℂ, A = B * C - C * B ∧
      ‖B‖ * ‖C‖ ≤ 2 ^ 42 * ‖A‖ := by
  have h := BlockAssembly.assemble_reindexed A (singletonPartitionEquiv n) 0 le_rfl
    (by simpa using hn) (fun i ↦ ?_)
  · simpa using h
  · refine ⟨0, 0, ?_, by simp⟩
    ext j l
    simp [BlockAssembly.block, singletonPartitionEquiv, hz]

/-- Fillmore's zero-diagonalization transfers a uniform bound to every trace-zero matrix. -/
theorem traceZero_bound_of_zeroDiag_at (n : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ (A : Matrix (Fin n) (Fin n) ℂ), (∀ i, A i i = 0) →
      ∃ B C : Matrix (Fin n) (Fin n) ℂ, A = B * C - C * B ∧
        ‖B‖ * ‖C‖ ≤ K * ‖A‖)
    (A : Matrix (Fin n) (Fin n) ℂ) (hTrace : Matrix.trace A = 0) :
    ∃ B C : Matrix (Fin n) (Fin n) ℂ, A = B * C - C * B ∧
      ‖B‖ * ‖C‖ ≤ K * ‖A‖ := by
  obtain ⟨U, X, hU, hz, heq⟩ := CommutatorTheorem.fillmore A hTrace
  have hX : Uᴴ * A * U = X := by
    rw [heq]
    calc
      _ = (Uᴴ * U) * X * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hU.2]; simp
  have hn : ‖X‖ ≤ ‖A‖ := hX ▸ isometry_compression_norm_le U hU.2 A
  obtain ⟨B, C, hBC, hnorm⟩ := h X hz
  apply unitary_commutator_pullback U hU.2 hU.1 A
  exact ⟨B, C, hX.trans hBC, hnorm.trans (mul_le_mul_of_nonneg_left hn hK)⟩

theorem uniform_bound_of_zeroDiag (K : ℝ) (hK : 0 < K)
    (h : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), (∀ i, A i i = 0) →
      ∃ B C : Matrix (Fin n) (Fin n) ℂ, A = B * C - C * B ∧
        ‖B‖ * ‖C‖ ≤ K * ‖A‖) : UniformCommutatorBound :=
  ⟨K, hK, fun n ↦ traceZero_bound_of_zeroDiag_at n K hK.le (h n)⟩

end NoEpsilon
