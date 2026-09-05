import NoEpsilon.MSSBarrier

/-!
# Exact algebra of one MSS barrier update

Mixed coordinate derivatives commute. The logarithmic-derivative update and its
scalar estimate are proved with explicit nonzero denominators.
-/

namespace NoEpsilon.MSSBarrierAlgebra

open MvPolynomial MSSBarrier

theorem pderiv_commute {R σ : Type*} [CommRing R] (p : MvPolynomial σ R) (i j : σ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [pderiv_mul, Pi.single_apply] <;> ring

theorem rational_update (a b c d : ℝ) (ha : a ≠ 0) (hac : a - c ≠ 0) :
    (b - d) / (a - c) = b / a - ((d * a - b * c) / a ^ 2) / (1 - c / a) := by
  have hden : 1 - c / a ≠ 0 := by
    intro h
    have hc : c / a = 1 := by linarith
    have he := (div_eq_one_iff_eq ha).mp hc
    exact hac (sub_eq_zero.mpr he.symm)
  field_simp
  ring

theorem barrier_sub_pderiv {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℝ) (i j : σ) (z : σ → ℝ)
    (hp : MvPolynomial.eval z p ≠ 0) (hb : barrier p j z ≠ 1) :
    barrier (p - pderiv j p) i z =
      barrier p i z - mixedBarrierDerivative p i j z / (1 - barrier p j z) := by
  have hsub : MvPolynomial.eval z p - MvPolynomial.eval z (pderiv j p) ≠ 0 := by
    intro h
    apply hb
    dsimp [barrier]
    rw [← sub_eq_zero.mp h]
    exact div_self hp
  simp only [barrier, mixedBarrierDerivative, map_sub, pderiv_commute p i j]
  exact rational_update _ _ _ _ hp hsub

/-- The final scalar inequality in the quantitative MSS shift, without dividing by
the potentially zero mixed derivative d. -/
theorem scalar_shift (δ bnew bold d fnew fold : ℝ)
    (hδ : 0 < δ) (hb : bnew ≤ bold) (hbold : bold ≤ 1 - 1 / δ)
    (hd : d ≤ 0) (htangent : fnew - δ * d ≤ fold) :
    fnew - d / (1 - bnew) ≤ fold := by
  have hb' : bnew ≤ 1 - 1 / δ := hb.trans hbold
  have hinvpos : 0 < 1 / δ := one_div_pos.mpr hδ
  have hden : 0 < 1 - bnew := by linarith
  have hmul : 1 ≤ δ * (1 - bnew) := by
    have h := mul_le_mul_of_nonneg_left hb' hδ.le
    have hid : δ * (1 / δ) = 1 := by field_simp
    nlinarith
  have hinv : 1 / (1 - bnew) ≤ δ := (div_le_iff₀ hden).mpr hmul
  have hterm := mul_le_mul_of_nonneg_right hinv (neg_nonneg.mpr hd)
  simp only [div_eq_mul_inv, one_mul] at hterm ⊢
  nlinarith

end NoEpsilon.MSSBarrierAlgebra
