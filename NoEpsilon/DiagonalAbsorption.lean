import NoEpsilon.AbsorptionCore

/-!
# From a uniformly invertible diagonal bridge to the identity-corner theorem

A diagonal similarity turns the bridge into an identity. Both the similarity and
its inverse are explicit, and the final factors remain in the original space.
-/

open scoped Matrix.Norms.L2Operator
open Matrix

namespace NoEpsilon.Absorption

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {d : ι → Type} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

/-- The first half of the core is scaled; all other coordinates are fixed. -/
def bridgeWeights (δ : Fin r → ℝ) : Ambient r d → ℂ
  | ⟨none, Sum.inl i⟩ => δ i
  | ⟨none, Sum.inr _⟩ => 1
  | ⟨some _, _⟩ => 1

/-- A diagonal bridge bounded below by rho gives a dimension-independent commutator bound. -/
theorem diagonal_corner_absorption (X : Matrix (Ambient r d) (Ambient r d) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (δ : Fin r → ℝ)
    (hδ : ∀ i, ρ ≤ δ i ∧ δ i ≤ 1)
    (hX : ‖X‖ ≤ 1) (hTrace : trace X = 0)
    (hbridge : (BlockAssembly.block X none none).toBlocks₁₂ =
      Matrix.diagonal (fun i ↦ (δ i : ℂ)))
    (hsize : ∀ i, Fintype.card (d i) ≤ r) :
    ∃ B C : Matrix (Ambient r d) (Ambient r d) ℂ,
      X = B * C - C * B ∧
        ‖B‖ * ‖C‖ ≤ ρ⁻¹ ^ 2 * absorptionBudget ρ⁻¹ (Fintype.card ι) := by
  classical
  let w := bridgeWeights (d := d) δ
  let S := Matrix.diagonal w
  let T := Matrix.diagonal (fun i ↦ (w i)⁻¹)
  have hδpos (i : Fin r) : 0 < δ i := hρ.trans_le (hδ i).1
  have hwn (i : Ambient r d) : w i ≠ 0 := by
    rcases i with ⟨_ | i, j⟩
    · rcases j with j | j
      · change (δ j : ℂ) ≠ 0
        exact_mod_cast (ne_of_gt (hδpos j))
      · simp [w, bridgeWeights]
    · simp [w, bridgeWeights]
  have hST : S * T = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hwn i)
  have hTS : T * S = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hwn i)
  have hS : ‖S‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    rcases i with ⟨_ | i, j⟩
    · rcases j with j | j
      · change ‖(δ j : ℂ)‖ ≤ 1
        simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hδpos j)] using (hδ j).2
      · norm_num [w, bridgeWeights]
    · norm_num [w, bridgeWeights]
  have hT : ‖T‖ ≤ ρ⁻¹ := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hρ.le)).mpr
    intro i
    rw [norm_inv]
    rcases i with ⟨_ | i, j⟩
    · rcases j with j | j
      · change ‖(δ j : ℂ)‖⁻¹ ≤ ρ⁻¹
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hδpos j)]
        simpa only [one_div] using one_div_le_one_div_of_le hρ (hδ j).1
      · have h : (1 : ℝ) ≤ 1 / ρ := (le_div_iff₀ hρ).mpr (by simpa using hρ1)
        simpa [w, bridgeWeights, one_div] using h
    · have h : (1 : ℝ) ≤ 1 / ρ := (le_div_iff₀ hρ).mpr (by simpa using hρ1)
      simpa [w, bridgeWeights, one_div] using h
  let Y := T * X * S
  have hY : ‖Y‖ ≤ ρ⁻¹ := by
    calc
      _ ≤ (‖T‖ * ‖S‖) * ‖X‖ := norm_conjugation_le T X S
      _ ≤ (ρ⁻¹ * 1) * 1 := by gcongr
      _ = ρ⁻¹ := by ring
  have htraceY : trace Y = 0 := by
    change trace (T * X * S) = 0
    rw [trace_mul_cycle, hST, Matrix.one_mul, hTrace]
  have hbridgeY : (BlockAssembly.block Y none none).toBlocks₁₂ = 1 := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ ↦ M i j) hbridge
    change X ⟨none, Sum.inl i⟩ ⟨none, Sum.inr j⟩ = _ at hij
    change (T * X * S) ⟨none, Sum.inl i⟩ ⟨none, Sum.inr j⟩ = _
    simp only [T, S, Matrix.mul_diagonal, Matrix.diagonal_mul,
      w, bridgeWeights, mul_one]
    rw [hij]
    by_cases h : i = j
    · subst j
      simp [ne_of_gt (hδpos i)]
    · simp [h]
  obtain ⟨B, C, hcomm, hcost⟩ :=
    identity_corner_absorption Y ρ⁻¹ (inv_pos.mpr hρ) hY htraceY hbridgeY hsize
  have hback : S * Y * T = X := by
    dsimp [Y]
    calc
      _ = (S * T) * X * (S * T) := by noncomm_ring
      _ = X := by rw [hST]; simp
  refine ⟨S * B * T, S * C * T, ?_, ?_⟩
  · change X = ringCommutator (S * B * T) (S * C * T)
    rw [conjugation_commutator S T B C hTS, ringCommutator, ← hcomm, hback]
  · have hcond : ‖S‖ * ‖T‖ ≤ ρ⁻¹ := by
      calc
        _ ≤ 1 * ρ⁻¹ := by gcongr
        _ = ρ⁻¹ := one_mul _
    calc
      _ ≤ (‖S‖ * ‖T‖) ^ 2 * (‖B‖ * ‖C‖) := norm_conjugation_product_le S T B C
      _ ≤ ρ⁻¹ ^ 2 * absorptionBudget ρ⁻¹ (Fintype.card ι) := by gcongr

end NoEpsilon.Absorption
