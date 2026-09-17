import CommutatorTheorem.NoEpsilon.LowMassBasis
import CommutatorTheorem.NoEpsilon.LowMassInput
import CommutatorTheorem.NoEpsilon.MSSPaired

/-! # Low-mass paving in the original matrix coordinates -/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace NoEpsilon

/-- Transfer the constructed low-mass basis back through the unit scalar rotation.
The paired-selection input is explicit in this reduction theorem. -/
theorem normalized_low_mass_paving_of_selection {k h : ℕ} (hk : 0 < k)
    (selection : LowMassPaving.PairedHalfSelection (Fin (k * 2 ^ h)))
    (A : Matrix (Fin (k * 2 ^ h)) (Fin (k * 2 ^ h)) ℂ)
    (hNorm : ‖A‖ ≤ 1) (hTrace : Matrix.trace A = 0)
    (hLow : ¬ HasHighTraceMass A (2 / (2 : ℝ) ^ h)) :
    ∃ b : OrthonormalBasis (Fin (2 ^ h) × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * 2 ^ h))),
      ∀ a, let W := familyMatrix (fun j ↦ b (a, j))
        Matrix.trace (Wᴴ * A * W) = 0 ∧ ‖Wᴴ * A * W‖ ≤ 319 / (2 : ℝ) ^ h := by
  obtain ⟨c, H, G, E, hc, hsplit, hH, hG, hHt, hGt, hGn, hE, hE₁, hlo, hup, hEt⟩ :=
    low_mass_input (by positivity) A hNorm hTrace
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hLow)
  obtain ⟨b, hb⟩ := LowMassPaving.exists_paving_basis hk selection H G E
    hH hHt hG hGn hGt hE hE₁ hEt hlo hup
  have hc₀ : c ≠ 0 := by intro h; simp [h] at hc
  refine ⟨b, ?_⟩
  intro a
  let W := familyMatrix (fun j ↦ b (a, j))
  obtain ⟨ht, hn⟩ := hb a
  change Matrix.trace (Wᴴ * (H + Complex.I • G) * W) = 0 at ht
  change ‖Wᴴ * (H + Complex.I • G) * W‖ ≤ 319 / (2 : ℝ) ^ h at hn
  rw [← hsplit, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul] at ht
  rw [← hsplit, Matrix.mul_smul, Matrix.smul_mul, norm_smul, hc, one_mul] at hn
  exact ⟨(smul_eq_zero.mp ht).resolve_left hc₀, hn⟩

/-- Every normalized low-mass matrix admits an exact equal-rank orthonormal paving with
zero traces and the fixed bound `319 / 2^h`. All analytic selection inputs are discharged. -/
theorem normalized_low_mass_paving {k h : ℕ} (hk : 0 < k)
    (A : Matrix (Fin (k * 2 ^ h)) (Fin (k * 2 ^ h)) ℂ)
    (hNorm : ‖A‖ ≤ 1) (hTrace : Matrix.trace A = 0)
    (hLow : ¬ HasHighTraceMass A (2 / (2 : ℝ) ^ h)) :
    ∃ b : OrthonormalBasis (Fin (2 ^ h) × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * 2 ^ h))),
      ∀ a, let W := familyMatrix (fun j ↦ b (a, j))
        Matrix.trace (Wᴴ * A * W) = 0 ∧ ‖Wᴴ * A * W‖ ≤ 319 / (2 : ℝ) ^ h :=
  normalized_low_mass_paving_of_selection hk
    (LowMassPaving.pairedHalfSelection _) A hNorm hTrace hLow

end NoEpsilon
