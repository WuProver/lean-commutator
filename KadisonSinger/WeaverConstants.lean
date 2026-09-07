import CommutatorTheorem.NoEpsilon.MSSPadding

/-!
# Numerical constants in Weaver's KS₂

The MSS partition bound at `r = 2` and `δ = 1 / 18` gives the universal
constants `η = 18` and `θ = 2` in Conjecture 1.2 of Marcus--Spielman--Srivastava.
-/

namespace KadisonSinger

/-- Rescaling the two-colour MSS estimate gives exactly `18 - 2 = 16`. -/
theorem weaver_bound_eq :
    (18 : ℝ) * (1 / Real.sqrt 2 + Real.sqrt (1 / 18)) ^ 2 = 16 := by
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs18 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 18 by norm_num)
  have hnon : 0 ≤ Real.sqrt 2 * Real.sqrt (1 / 18) := by positivity
  have hprod : Real.sqrt 2 * Real.sqrt (1 / 18) = 1 / 3 := by
    nlinarith [sq_nonneg (Real.sqrt 2 * Real.sqrt (1 / 18) + 1 / 3),
      show (Real.sqrt 2 * Real.sqrt (1 / 18)) ^ 2 = 1 / 9 by
        rw [mul_pow, hs2, hs18]
        norm_num]
  have hne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

end KadisonSinger
