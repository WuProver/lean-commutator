import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# A bounded Riccati fixed point

This module proves the contraction argument used in the identity-corner construction.
The algebra is allowed to be noncommutative. The analytic assumptions are those of
a complete normed real algebra. No expander theorem is assumed in this module.
-/

namespace NoEpsilon

open scoped NNReal

section NormBounds

variable {E : Type*} [NormedRing E]

/-- The quadratic expression appearing in the fixed-point equation. -/
def quadratic (c d e x : E) : E := x * x + c * x + x * d + e

/-- A submultiplicative norm bound for the quadratic expression. -/
theorem norm_quadratic_le (c d e x : E) :
    ‖quadratic c d e x‖ ≤ ‖x‖ ^ 2 + (‖c‖ + ‖d‖) * ‖x‖ + ‖e‖ := by
  calc
    ‖quadratic c d e x‖
        ≤ ‖x * x‖ + ‖c * x‖ + ‖x * d‖ + ‖e‖ := by
          dsimp [quadratic]
          linarith [norm_add_le (x * x) (c * x),
            norm_add_le (x * x + c * x) (x * d),
            norm_add_le (x * x + c * x + x * d) e]
    _ ≤ ‖x‖ * ‖x‖ + ‖c‖ * ‖x‖ + ‖x‖ * ‖d‖ + ‖e‖ := by
          gcongr <;> exact norm_mul_le _ _
    _ = _ := by ring

/-- Difference estimate retaining the order of noncommuting factors. -/
theorem norm_quadratic_sub_le (c d e x y : E) :
    ‖quadratic c d e x - quadratic c d e y‖ ≤
      (‖x‖ + ‖y‖ + ‖c‖ + ‖d‖) * ‖x - y‖ := by
  have hid : quadratic c d e x - quadratic c d e y =
      (x - y) * x + y * (x - y) + c * (x - y) + (x - y) * d := by
    dsimp [quadratic]
    noncomm_ring
  rw [hid]
  calc
    ‖(x - y) * x + y * (x - y) + c * (x - y) + (x - y) * d‖
        ≤ ‖(x - y) * x‖ + ‖y * (x - y)‖ + ‖c * (x - y)‖ +
            ‖(x - y) * d‖ := by
          linarith [norm_add_le ((x - y) * x) (y * (x - y)),
            norm_add_le ((x - y) * x + y * (x - y)) (c * (x - y)),
            norm_add_le ((x - y) * x + y * (x - y) + c * (x - y)) ((x - y) * d)]
    _ ≤ ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ + ‖c‖ * ‖x - y‖ +
          ‖x - y‖ * ‖d‖ := by
          gcongr <;> exact norm_mul_le _ _
    _ = _ := by ring

end NormBounds

section FixedPoint

variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

/-- The Riccati map with a scalar parameter and specified centre. -/
noncomputable def riccatiMap (b c d e : E) (ε : ℝ) (x : E) : E :=
  b + ε • quadratic c d e x

/-- Quantitative smallness conditions give an exact fixed point in the unit ball
about the specified centre. The output remains in the original algebra. -/
theorem exists_riccati_fixedPoint (b c d e : E) (ε : ℝ) (hε : 0 ≤ ε)
    (hmap : ε * ((‖b‖ + 1) ^ 2 + (‖c‖ + ‖d‖) * (‖b‖ + 1) + ‖e‖) ≤ 1)
    (hcontract : ε * (2 * (‖b‖ + 1) + ‖c‖ + ‖d‖) ≤ 1 / 2) :
    ∃ x : E, ‖x - b‖ ≤ 1 ∧ x = b + ε • quadratic c d e x := by
  let f := riccatiMap b c d e ε
  let s := Metric.closedBall b 1
  have hnorm (x : E) (hx : x ∈ s) : ‖x‖ ≤ ‖b‖ + 1 := by
    have hx' : ‖x - b‖ ≤ 1 := by
      simpa only [s, Metric.mem_closedBall, dist_eq_norm] using hx
    calc
      ‖x‖ ≤ ‖x - b‖ + ‖b‖ := norm_le_norm_sub_add x b
      _ ≤ ‖b‖ + 1 := by linarith
  have hself : Set.MapsTo f s s := by
    intro x hx
    have hxn := hnorm x hx
    have hpoly : ‖quadratic c d e x‖ ≤
        (‖b‖ + 1) ^ 2 + (‖c‖ + ‖d‖) * (‖b‖ + 1) + ‖e‖ := by
      apply (norm_quadratic_le c d e x).trans
      gcongr
    change dist (f x) b ≤ 1
    rw [dist_eq_norm]
    calc
      ‖f x - b‖ = ε * ‖quadratic c d e x‖ := by
        simp [f, riccatiMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
      _ ≤ ε * ((‖b‖ + 1) ^ 2 + (‖c‖ + ‖d‖) * (‖b‖ + 1) + ‖e‖) :=
        mul_le_mul_of_nonneg_left hpoly hε
      _ ≤ 1 := hmap
  have hdist (x y : E) (hx : x ∈ s) (hy : y ∈ s) :
      dist (f x) (f y) ≤ (1 / 2 : ℝ) * dist x y := by
    have hxy : ‖x‖ + ‖y‖ + ‖c‖ + ‖d‖ ≤ 2 * (‖b‖ + 1) + ‖c‖ + ‖d‖ := by
      linarith [hnorm x hx, hnorm y hy]
    rw [dist_eq_norm, dist_eq_norm]
    have hid : f x - f y = ε • (quadratic c d e x - quadratic c d e y) := by
      simp [f, riccatiMap, smul_sub]
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
    calc
      ε * ‖quadratic c d e x - quadratic c d e y‖
          ≤ ε * ((‖x‖ + ‖y‖ + ‖c‖ + ‖d‖) * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left (norm_quadratic_sub_le c d e x y) hε
      _ ≤ ε * ((2 * (‖b‖ + 1) + ‖c‖ + ‖d‖) * ‖x - y‖) := by
        gcongr
      _ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hcontract (norm_nonneg _)
  have hf : ContractingWith (1 / 2 : ℝ≥0) (hself.restrict f s s) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simpa using
      hdist x.val y.val x.property y.property
  have hb : b ∈ s := Metric.mem_closedBall_self (by norm_num)
  obtain ⟨x, hx, hfix, _⟩ := hf.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hself hb
    (edist_ne_top _ _)
  refine ⟨x, ?_, hfix.symm⟩
  simpa only [s, Metric.mem_closedBall, dist_eq_norm] using hx

/-- A sufficiently large positive scalar gives the fixed point with inverse parameter. -/
theorem exists_riccati_fixedPoint_large_scale (b c d e : E) (lam : ℝ) (hlam : 0 < lam)
    (hsize : 2 * ((‖b‖ + 1) ^ 2 + (‖c‖ + ‖d‖) * (‖b‖ + 1) + ‖e‖) ≤ lam)
    (hlip : 2 * (2 * (‖b‖ + 1) + ‖c‖ + ‖d‖) ≤ lam) :
    ∃ x : E, ‖x - b‖ ≤ 1 ∧ x = b + lam⁻¹ • quadratic c d e x := by
  have hsize₀ : 0 ≤ (‖b‖ + 1) ^ 2 + (‖c‖ + ‖d‖) * (‖b‖ + 1) + ‖e‖ := by
    positivity
  apply exists_riccati_fixedPoint b c d e lam⁻¹ (inv_nonneg.mpr hlam.le)
  · rw [← div_eq_inv_mul]
    apply (div_le_iff₀ hlam).mpr
    linarith
  · rw [← div_eq_inv_mul]
    apply (div_le_iff₀ hlam).mpr
    linarith

/-- An explicit positive scale determined by the coefficient norms. -/
noncomputable def riccatiScale (b c d e : E) : ℝ :=
  2 * (((‖b‖ + 1) ^ 2 + (‖c‖ + ‖d‖) * (‖b‖ + 1) + ‖e‖) +
    (2 * (‖b‖ + 1) + ‖c‖ + ‖d‖) + 1)

omit [NormedAlgebra ℝ E] [CompleteSpace E] in
theorem riccatiScale_pos (b c d e : E) : 0 < riccatiScale b c d e := by
  unfold riccatiScale
  positivity

/-- Existence with the explicit scale, without additional smallness hypotheses. -/
theorem exists_riccati_fixedPoint_explicit (b c d e : E) :
    ∃ x : E, ‖x - b‖ ≤ 1 ∧
      x = b + (riccatiScale b c d e)⁻¹ • quadratic c d e x := by
  apply exists_riccati_fixedPoint_large_scale b c d e _ (riccatiScale_pos b c d e)
  · unfold riccatiScale
    have : 0 ≤ 2 * (‖b‖ + 1) + ‖c‖ + ‖d‖ := by positivity
    linarith
  · unfold riccatiScale
    have : 0 ≤ (‖b‖ + 1) ^ 2 + (‖c‖ + ‖d‖) * (‖b‖ + 1) + ‖e‖ := by positivity
    linarith

end FixedPoint

end NoEpsilon
