import CommutatorTheorem.NoEpsilon.Main

/-! # The explicit bound 2^3200

The simultaneous-shear budget is inserted into the existing same-dimension induction.
All matrix norms in the final theorem are Euclidean operator norms.
-/

open scoped Matrix.Norms.L2Operator

namespace NoEpsilon

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
-- Exact powers of two up to 3200 are small integers for kernel arithmetic.
set_option exponentiation.threshold 10000

/-- A convenient monomial majorant for the identity-corner cost. -/
theorem identityCornerNormBudget_le_monomial (x : ℝ) (hx : 1 ≤ x) :
    identityCornerNormBudget x ≤ 2 ^ 29 * x ^ 9 := by
  have hx0 : 0 ≤ x := by linarith
  have hx2 : x ≤ x ^ 2 := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hs : identityCornerScale x ≤ 138 * x ^ 2 := by
    unfold identityCornerScale
    have h₁ : (5 * x + 1) ^ 2 + (2 * x + 1) * (5 * x + 1) + (14 * x + 1) ≤
        69 * x ^ 2 := by nlinarith
    have h₂ : 2 * (5 * x + 1) + 2 * x + 1 ≤ 69 * x ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left (max_le h₁ h₂) (by norm_num)).trans (by ring_nf; rfl)
  have hs0 := (identityCornerScale_pos x hx0).le
  have hfirst : 1 + (5 * x + 1) ≤ 7 * x := by linarith
  have hsecond : identityCornerScale x + 3 ≤ 141 * x ^ 2 := by nlinarith
  have hthird : (identityCornerScale x + 5) * (2 * x) + 2 ≤ 288 * x ^ 3 := by
    have h : identityCornerScale x + 5 ≤ 143 * x ^ 2 := by nlinarith
    have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx
    nlinarith [mul_le_mul_of_nonneg_right h (show 0 ≤ 2 * x by positivity)]
  calc
    _ ≤ (7 * x) ^ 4 * (141 * x ^ 2) * (288 * x ^ 3) := by
      unfold identityCornerNormBudget
      gcongr
    _ ≤ 2 ^ 29 * x ^ 9 := by
      ring_nf
      nlinarith [pow_nonneg hx0 9]

/-- The two-shear transformed norm is at most 2^281 at the fixed high-mass parameters. -/
theorem simultaneousBudget_fixed_le :
    Absorption.simultaneousBudget ((2 : ℝ) ^ 27) (2 ^ 29) ≤ (2 : ℝ) ^ 281 := by
  let q : ℝ := Real.sqrt ((2 ^ 29 : ℕ) : ℝ)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq : q ≤ (2 : ℝ) ^ 15 := Real.sqrt_le_iff.mpr ⟨by positivity, by norm_num⟩
  let u := 1 + (2 : ℝ) ^ 27 + q
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu : u ≤ (2 : ℝ) ^ 28 := by dsimp [u]; norm_num at hq ⊢; linarith
  let a₁ := (2 : ℝ) ^ 27 * u ^ 2
  have ha₁0 : 0 ≤ a₁ := by dsimp [a₁]; positivity
  have ha₁ : a₁ ≤ (2 : ℝ) ^ 83 := by
    calc
      _ ≤ (2 : ℝ) ^ 27 * ((2 : ℝ) ^ 28) ^ 2 := by dsimp [a₁]; gcongr
      _ = _ := by norm_num
  have hv : 1 + q * a₁ ≤ (2 : ℝ) ^ 99 := by
    calc
      _ ≤ 1 + (2 : ℝ) ^ 15 * (2 : ℝ) ^ 83 := by gcongr
      _ ≤ _ := by norm_num
  change a₁ * (1 + q * a₁) ^ 2 ≤ _
  calc
    _ ≤ (2 : ℝ) ^ 83 * ((2 : ℝ) ^ 99) ^ 2 := by gcongr
    _ = _ := by norm_num

/-- The transformed norm is at least one, so the monomial majorant applies. -/
theorem simultaneousBudget_fixed_ge_one :
    1 ≤ Absorption.simultaneousBudget ((2 : ℝ) ^ 27) (2 ^ 29) := by
  have hq : 0 ≤ Real.sqrt ((2 ^ 29 : ℕ) : ℝ) := Real.sqrt_nonneg _
  unfold Absorption.simultaneousBudget
  have hu : 1 ≤ 1 + (2 : ℝ) ^ 27 + Real.sqrt ((2 ^ 29 : ℕ) : ℝ) := by linarith
  have ha : 1 ≤ (2 : ℝ) ^ 27 *
      (1 + (2 : ℝ) ^ 27 + Real.sqrt ((2 ^ 29 : ℕ) : ℝ)) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hu)
  exact one_le_mul_of_one_le_of_one_le ha (one_le_pow₀ (by
    have : 0 ≤ Real.sqrt ((2 ^ 29 : ℕ) : ℝ) * ((2 : ℝ) ^ 27 *
        (1 + (2 : ℝ) ^ 27 + Real.sqrt ((2 ^ 29 : ℕ) : ℝ)) ^ 2) := by positivity
    linarith))

/-- The high-trace-mass branch has the bound stated in the referee's estimate. -/
theorem highMassNormBudget_fixed_le :
    highMassNormBudget (2 / (2 : ℝ) ^ 26) ≤ (2 : ℝ) ^ 3153 := by
  have heq : highMassNormBudget (2 / (2 : ℝ) ^ 26) =
      ((2 : ℝ) ^ 27) ^ 2 * Absorption.absorptionBudget ((2 : ℝ) ^ 27) (2 ^ 29) := by
    norm_num [highMassNormBudget]
  rw [heq]
  let h := Absorption.simultaneousBudget ((2 : ℝ) ^ 27) (2 ^ 29)
  have hh : h ≤ (2 : ℝ) ^ 281 := simultaneousBudget_fixed_le
  have hh1 : 1 ≤ h := simultaneousBudget_fixed_ge_one
  have hh0 : 0 ≤ h := by linarith
  have hp0 : 0 ≤ identityCornerNormBudget h := by
    have hs0 := (identityCornerScale_pos h hh0).le
    unfold identityCornerNormBudget
    positivity
  have hp : identityCornerNormBudget h ≤ (2 : ℝ) ^ 2558 := by
    calc
      _ ≤ (2 : ℝ) ^ 29 * h ^ 9 := identityCornerNormBudget_le_monomial h hh1
      _ ≤ (2 : ℝ) ^ 29 * ((2 : ℝ) ^ 281) ^ 9 := by gcongr
      _ = _ := by norm_num
  have hk : ((2 ^ 29 : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ 30 := by norm_num
  have he : ((2 : ℝ) ^ 27) ^ 2 * Absorption.absorptionBudget ((2 : ℝ) ^ 27) (2 ^ 29) =
      h ^ 2 * (4 * (((2 ^ 29 : ℕ) : ℝ) + 1) * identityCornerNormBudget h +
        2 * (((2 ^ 29 : ℕ) : ℝ) + 1) ^ 2 * h) := by
    unfold Absorption.absorptionBudget
    dsimp [h]
    ring
  rw [he]
  calc
    _ ≤ ((2 : ℝ) ^ 281) ^ 2 *
        (4 * (2 : ℝ) ^ 30 * (2 : ℝ) ^ 2558 + 2 * ((2 : ℝ) ^ 30) ^ 2 * (2 : ℝ) ^ 281) := by
      gcongr
    _ ≤ (2 : ℝ) ^ 3153 := by norm_num

/-- The complete induction budget is below 2^3200. -/
theorem globalNormBudget_le_explicit : globalNormBudget ≤ (2 : ℝ) ^ 3200 := by
  unfold globalNormBudget
  have hh := highMassNormBudget_fixed_le
  have hm : max (highMassNormBudget (2 / (2 : ℝ) ^ 26)) 0 ≤ (2 : ℝ) ^ 3153 :=
    max_le hh (by positivity)
  apply max_le
  · calc
      _ ≤ 65536 * (2 : ℝ) ^ 3153 + 2 ^ 42 := by gcongr
      _ ≤ (2 : ℝ) ^ 3200 := by norm_num
  · norm_num

/-- Every trace-zero complex matrix is a same-dimension commutator with constant 2^3200. -/
theorem commutator_bound_two_pow_3200 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : Matrix.trace A = 0) :
    ∃ B C : Matrix (Fin n) (Fin n) ℂ,
      A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ (2 : ℝ) ^ 3200 * ‖A‖ := by
  obtain ⟨B, C, hBC, hbound⟩ := boundedCommutator_of_lowMassBlocksAt pavingRank rfl
    (lowMassPavingBlocksInput_of_basis pavingRank lowMassPavingInput_proved) n A hA
  exact ⟨B, C, hBC, hbound.trans
    (mul_le_mul_of_nonneg_right globalNormBudget_le_explicit (norm_nonneg A))⟩

/-- The same explicit estimate stated with the actual continuous-linear-map operator norm. -/
theorem commutator_bound_two_pow_3200_euclideanOperatorNorm
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : Matrix.trace A = 0) :
    ∃ B C : Matrix (Fin n) (Fin n) ℂ,
      A = B * C - C * B ∧
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B‖ *
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) C‖ ≤
          (2 : ℝ) ^ 3200 * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ :=
  commutator_bound_two_pow_3200 n A hA

end NoEpsilon
