import PavingSeparation.Family
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Dyadic block counts and compression estimates

The dyadic rounding lemma retains the exact power when the target is already a power of two.
-/

namespace PavingSeparation

/-- Round a real number at least one upwards to a power of two, with strict factor-two loss. -/
theorem exists_dyadic_ge_lt_two_mul {x : ℝ} (hx : 1 ≤ x) :
    ∃ L : ℕ, x ≤ (2 : ℝ) ^ L ∧ (2 : ℝ) ^ L < 2 * x := by
  obtain ⟨L, hL, hnext⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  by_cases heq : (2 : ℝ) ^ L = x
  · refine ⟨L, heq.ge, ?_⟩
    rw [heq]
    linarith
  · refine ⟨L + 1, hnext.le, ?_⟩
    have hlt : (2 : ℝ) ^ L < x := lt_of_le_of_ne hL heq
    rw [pow_succ]
    linarith

/-- The strict block-count bound used for the explicit epsilon paving. -/
theorem exists_dyadic_inverse_sq (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ L : ℕ, 1 / ε ^ 2 ≤ (2 : ℝ) ^ L ∧ (2 : ℝ) ^ L < 2 / ε ^ 2 := by
  have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hx : (1 : ℝ) ≤ 1 / ε ^ 2 := by
    apply (le_div_iff₀ hsq).2
    nlinarith
  obtain ⟨L, hL, hlt⟩ := exists_dyadic_ge_lt_two_mul hx
  refine ⟨L, hL, ?_⟩
  simpa only [mul_one_div] using hlt

/-- The dyadic recursive compression is no larger than the reciprocal square root of the
number of blocks. -/
theorem dyadic_compression_sqrt_le {m l : ℕ} (hm : 0 < m) (hl : l ≤ m) :
    Real.sqrt (((2 : ℝ) ^ (m - l) - 1) / ((2 : ℝ) ^ m - 1)) ≤
      Real.sqrt (1 / (2 : ℝ) ^ l) := by
  apply Real.sqrt_le_sqrt
  have hden := order_sub_one_pos hm
  have hpow : (0 : ℝ) < 2 ^ l := pow_pos (by norm_num) _
  have hprod : (2 : ℝ) ^ (m - l) * 2 ^ l = 2 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hl]
  have hone : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
  apply (div_le_div_iff₀ hden hpow).2
  nlinarith

/-- Apply the dyadic compression estimate at a block count at least epsilon inverse square. -/
theorem dyadic_compression_sqrt_le_epsilon {m l : ℕ} (hm : 0 < m) (hl : l ≤ m)
    {ε : ℝ} (hε : 0 < ε) (hpow : 1 / ε ^ 2 ≤ (2 : ℝ) ^ l) :
    Real.sqrt (((2 : ℝ) ^ (m - l) - 1) / ((2 : ℝ) ^ m - 1)) ≤ ε := by
  refine (dyadic_compression_sqrt_le hm hl).trans ?_
  apply (Real.sqrt_le_iff).2
  refine ⟨hε.le, ?_⟩
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) l)).2
  have h := (div_le_iff₀ (sq_pos_of_pos hε)).1 hpow
  simpa only [mul_comm] using h

end PavingSeparation
