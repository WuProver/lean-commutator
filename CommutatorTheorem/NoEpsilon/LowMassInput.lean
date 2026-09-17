import CommutatorTheorem.NoEpsilon.HighMassCompression
import Mathlib.Analysis.Matrix.Order

/-! # The positive majorant in the low trace-mass branch -/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spectral absolute value is a positive contraction dominating both signs of `H`.
Its trace is exactly the absolute eigenvalue mass used in the high/low dichotomy. -/
theorem exists_absolute_majorant (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hNorm : ‖H‖ ≤ 1) :
    ∃ E : Matrix ι ι ℂ, E.PosSemidef ∧ E ≤ 1 ∧ -E ≤ H ∧ H ≤ E ∧
      (Matrix.trace E).re = ∑ i, |hH.eigenvalues i| := by
  let U : Matrix ι ι ℂ := hH.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i ↦ ((|hH.eigenvalues i| : ℝ) : ℂ))
  let D₀ : Matrix ι ι ℂ := Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))
  let E := U * D * Uᴴ
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hU' : Uᴴ * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hspec : H = U * D₀ * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply] using hH.spectral_theorem
  have heig (i : ι) : |hH.eigenvalues i| ≤ 1 :=
    (abs_hermitian_eigenvalue_le_opNorm H hH i).trans hNorm
  have hconj (M : Matrix ι ι ℂ) (hM : M.PosSemidef) : (U * M * Uᴴ).PosSemidef := by
    simpa using hM.conjTranspose_mul_mul_same Uᴴ
  refine ⟨E, hconj D (Matrix.posSemidef_diagonal_iff.mpr (by
    intro i; exact_mod_cast abs_nonneg (hH.eigenvalues i))), ?_, ?_, ?_, ?_⟩
  · apply Matrix.le_iff.mpr
    have h : (1 - D).PosSemidef := by
      have hd : (1 : Matrix ι ι ℂ) - D =
          Matrix.diagonal (fun i ↦ ((1 - |hH.eigenvalues i| : ℝ) : ℂ)) := by
        ext i j
        by_cases hij : i = j <;> simp [D, hij]
      rw [hd]
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      exact_mod_cast sub_nonneg.mpr (heig i)
    simpa [Matrix.mul_sub, Matrix.sub_mul, E, hU] using hconj (1 - D) h
  · apply Matrix.le_iff.mpr
    have h : (D₀ + D).PosSemidef := by
      dsimp only [D₀, D]
      rw [Matrix.diagonal_add]
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      exact_mod_cast (show 0 ≤ hH.eigenvalues i + |hH.eigenvalues i| by
        linarith [neg_le_abs (hH.eigenvalues i)])
    simpa [hspec, E, Matrix.mul_add, Matrix.add_mul] using hconj (D₀ + D) h
  · apply Matrix.le_iff.mpr
    have h : (D - D₀).PosSemidef := by
      dsimp only [D₀, D]
      rw [Matrix.diagonal_sub]
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      exact_mod_cast sub_nonneg.mpr (le_abs_self (hH.eigenvalues i))
    simpa [hspec, E, Matrix.mul_sub, Matrix.sub_mul] using hconj (D - D₀) h
  · dsimp only [E]
    rw [Matrix.trace_mul_cycle, hU', Matrix.one_mul, Matrix.trace_diagonal]
    simp

/-- Failure of the rotation-uniform mass bound supplies the exact low-branch input.
The unit scalar is retained so the resulting paving can be transported back to `A`. -/
theorem low_mass_input {k R : ℕ} (hR : 0 < R)
    (A : Matrix (Fin (k * R)) (Fin (k * R)) ℂ)
    (hNorm : ‖A‖ ≤ 1) (hTrace : Matrix.trace A = 0)
    (hLow : ¬ HasHighTraceMass A (2 / R)) :
    ∃ (c : ℂ) (H G E : Matrix (Fin (k * R)) (Fin (k * R)) ℂ),
      ‖c‖ = 1 ∧ c • A = H + Complex.I • G ∧
      H.IsHermitian ∧ G.IsHermitian ∧ Matrix.trace H = 0 ∧ Matrix.trace G = 0 ∧
      ‖G‖ ≤ 1 ∧ E.PosSemidef ∧ E ≤ 1 ∧ -E ≤ H ∧ H ≤ E ∧
      (Matrix.trace E).re ≤ 2 * k := by
  classical
  simp only [HasHighTraceMass, not_forall, not_le] at hLow
  obtain ⟨c, hc, hMass⟩ := hLow
  have hRot : ‖c • A‖ ≤ 1 := by simpa [norm_smul, hc] using hNorm
  have hRotTrace : Matrix.trace (c • A) = 0 := by simp [Matrix.trace_smul, hTrace]
  let H := hermitianRealPart (c • A)
  let G := hermitianImaginaryPart (c • A)
  have hH := hermitianRealPart_isHermitian (c • A)
  obtain ⟨E, hE, hE₁, hLower, hUpper, hEt⟩ := exists_absolute_majorant H hH
    ((hermitianRealPart_norm_le (c • A)).trans hRot)
  refine ⟨c, H, G, E, hc, (hermitian_split (c • A)).symm, hH,
    hermitianImaginaryPart_isHermitian (c • A),
    hermitianRealPart_trace_zero _ hRotTrace, hermitianImaginaryPart_trace_zero _ hRotTrace,
    (hermitianImaginaryPart_norm_le _).trans hRot, hE, hE₁, hLower, hUpper, ?_⟩
  rw [hEt]
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hBudget : (2 / (R : ℝ)) * Fintype.card (Fin (k * R)) = 2 * k := by
    simp only [Fintype.card_fin, Nat.cast_mul]
    field_simp
  exact (hMass.trans_eq hBudget).le

end NoEpsilon
