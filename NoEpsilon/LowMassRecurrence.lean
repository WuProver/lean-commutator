import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# The balanced paving recurrence

This file solves the actual square-root recurrence produced by paired MSS
selection. Its constants are independent of the number of groups.
-/

namespace NoEpsilon.LowMassPaving

noncomputable def transversalConstant (D : ℝ) : ℝ :=
  (1 + 2 * (Real.sqrt 2 + 1) * Real.sqrt D) ^ 2

/-- A closed upper bound for every level of the paired-selection recurrence. -/
theorem binary_recurrence_sqrt_bound (δ : ℝ) (hδ : 0 ≤ δ) (L : ℕ → ℝ)
    (hL : ∀ j, 0 ≤ L j) (h₀ : L 0 ≤ 1)
    (hstep : ∀ j, L (j + 1) ≤ (Real.sqrt (L j) + 2 * Real.sqrt δ) ^ 2 / 2) :
    ∀ j, Real.sqrt (L j) ≤ (Real.sqrt 2)⁻¹ ^ j +
      2 * (Real.sqrt 2 + 1) * Real.sqrt δ := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs₂ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfixed : (2 * (Real.sqrt 2 + 1) + 2) / Real.sqrt 2 =
      2 * (Real.sqrt 2 + 1) := by
    apply (div_eq_iff hs.ne').mpr
    nlinarith
  intro j
  induction j with
  | zero =>
    have h := Real.sqrt_le_sqrt h₀
    simp only [Real.sqrt_one] at h
    simp only [pow_zero]
    have hnonneg : 0 ≤ 2 * (Real.sqrt 2 + 1) * Real.sqrt δ := by positivity
    linarith
  | succ j ih =>
    calc
      Real.sqrt (L (j + 1)) ≤
          Real.sqrt ((Real.sqrt (L j) + 2 * Real.sqrt δ) ^ 2 / 2) :=
        Real.sqrt_le_sqrt (hstep j)
      _ = (Real.sqrt (L j) + 2 * Real.sqrt δ) / Real.sqrt 2 := by
        rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by positivity)]
      _ ≤ ((Real.sqrt 2)⁻¹ ^ j +
          2 * (Real.sqrt 2 + 1) * Real.sqrt δ + 2 * Real.sqrt δ) / Real.sqrt 2 := by
        exact div_le_div_of_nonneg_right (by linarith) hs.le
      _ = (Real.sqrt 2)⁻¹ ^ (j + 1) +
          2 * (Real.sqrt 2 + 1) * Real.sqrt δ := by
        calc
          _ = (Real.sqrt 2)⁻¹ ^ j / Real.sqrt 2 +
              ((2 * (Real.sqrt 2 + 1) + 2) / Real.sqrt 2) * Real.sqrt δ := by ring
          _ = _ := by rw [hfixed, pow_succ]; ring

/-- At depth `h`, with individual energy budget `D / 2^h`, every leaf
has bound `C_D / 2^h`. -/
theorem binary_recurrence_leaf_bound (D : ℝ) (hD : 0 ≤ D) (h : ℕ) (L : ℕ → ℝ)
    (hL : ∀ j, 0 ≤ L j) (h₀ : L 0 ≤ 1)
    (hstep : ∀ j, L (j + 1) ≤
      (Real.sqrt (L j) + 2 * Real.sqrt (D / (2 : ℝ) ^ h)) ^ 2 / 2) :
    L h ≤ transversalConstant D / (2 : ℝ) ^ h := by
  have hR : 0 < (2 : ℝ) ^ h := by positivity
  have hs : 0 < Real.sqrt 2 := by positivity
  have hpow : ((Real.sqrt 2) ^ h) ^ 2 = (2 : ℝ) ^ h := by
    rw [← pow_mul, Nat.mul_comm h 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hgeom : (Real.sqrt 2)⁻¹ ^ h = 1 / Real.sqrt ((2 : ℝ) ^ h) := by
    rw [← hpow, Real.sqrt_sq (by positivity), one_div, inv_pow]
  have hbound := binary_recurrence_sqrt_bound (D / (2 : ℝ) ^ h)
    (div_nonneg hD hR.le) L hL h₀ hstep h
  rw [hgeom, Real.sqrt_div hD] at hbound
  have hbound' : Real.sqrt (L h) ≤
      (1 + 2 * (Real.sqrt 2 + 1) * Real.sqrt D) / Real.sqrt ((2 : ℝ) ^ h) := by
    convert hbound using 1 <;> ring
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (L h)) (by positivity)).mpr hbound'
  simpa only [Real.sq_sqrt (hL h), div_pow, Real.sq_sqrt hR.le,
    transversalConstant] using hsq

/-- The manuscript's fixed numerical budget, with room for the imaginary part. -/
theorem transversalConstant_twelve_add_four_lt : transversalConstant 12 + 4 < 319 := by
  have hs₂ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs₁₂ : Real.sqrt 12 ^ 2 = 12 := Real.sq_sqrt (by norm_num)
  have h₂ : Real.sqrt 2 < 1.415 := by nlinarith [Real.sqrt_nonneg 2]
  have h₁₂ : Real.sqrt 12 < 3.465 := by nlinarith [Real.sqrt_nonneg 12]
  have hprod : 2 * (Real.sqrt 2 + 1) * Real.sqrt 12 < 2 * (1.415 + 1) * 3.465 := by
    have hpos : 0 < Real.sqrt 12 := by positivity
    nlinarith [mul_lt_mul_of_pos_right h₂ hpos]
  have hnonneg : 0 ≤ 1 + 2 * (Real.sqrt 2 + 1) * Real.sqrt 12 := by positivity
  dsimp [transversalConstant]
  nlinarith

end NoEpsilon.LowMassPaving
