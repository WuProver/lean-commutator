import NoEpsilon.MSSScaled
import NoEpsilon.PairedCovarianceBound
import NoEpsilon.LowMassTransversals

/-!
# Unconditional paired half-selection

The four local outcomes have the exact paired covariance and energy. Applying the
proved scaled finite MSS theorem supplies the analytic premise used by the quota tree.
-/

namespace NoEpsilon.LowMassPaving

open MSSSelection MSSScaled
open scoped BigOperators Matrix.Norms.L2Operator

/-- The paired half-selection assertion is a theorem, with both zero parameters included. -/
theorem pairedHalfSelection (ι : Type*) [Fintype ι] [DecidableEq ι] :
    PairedHalfSelection ι := by
  intro κ _ a b δ L hδ hL ha hb hparent
  let v : κ → Bool × Bool → (ι ⊕ ι) → ℂ := fun i q ↦ pairedVector (a i) (b i) q
  let p : κ → Bool × Bool → ℝ := fun _ _ ↦ 1 / 4
  have hp : ∀ i q, 0 ≤ p i q := by intro i q; norm_num [p]
  have hsum : ∀ i, ∑ q, p i q = 1 := by
    intro i
    norm_num [p, Fintype.sum_prod_type]
  have hcov : ‖∑ i, ∑ q, (p i q : ℂ) • outer (v i q)‖ ≤ L := by
    simpa only [p, v, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
      using paired_covariance_norm_le a b L hL hparent
  have henergy : ∀ i, ∑ q, p i q * energy (v i q) ≤ 4 * δ := by
    intro i
    calc
      (∑ q, p i q * energy (v i q)) ≤ ∑ q : Bool × Bool, (1 / 4 : ℝ) * (4 * δ) := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (paired_energy_le (a i) (b i) δ (ha i) (hb i) q)
          (by norm_num)
      _ = 4 * δ := by norm_num [Fintype.sum_prod_type]; ring
  obtain ⟨q, hq⟩ := finite_mss_scaled v p hp hsum L (4 * δ) hL (by positivity) hcov henergy
  have hsqrt : Real.sqrt (4 * δ) = 2 * Real.sqrt δ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hsqrt] at hq
  have hchildren := paired_children_bound_of_outcome a b q
    ((Real.sqrt L + 2 * Real.sqrt δ)^2) hq
  exact ⟨q, hchildren⟩

end NoEpsilon.LowMassPaving
