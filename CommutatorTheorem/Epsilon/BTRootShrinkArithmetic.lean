import Mathlib

/-!
# The numerical endgame of joint restricted invertibility

Ravichandran--Srivastava's root-shrinking estimate bounds the largest
root by

`c * (1 - α) + 2 * sqrt (c * (1 - c) * α)`.

For a family of `k` Hermitian contractions the mixed determinantal
polynomial has second root moment `α ≤ 1 / k`.  The restricted
invertibility proof takes `c = ε² / (6k)` and then multiplies the root
bound by `k`.  This file verifies, without any analytic assumptions,
that the resulting number is strictly smaller than `ε`.
-/

namespace CommutatorTheorem

/-- The constant calculation at the end of the joint restricted
invertibility proof.  It is separated from the polynomial argument so
that a future root-shrinking implementation can use it directly. -/
theorem jointRI_rootShrink_constant
    {k : ℕ} (hk : 0 < k) {ε α : ℝ}
    (hε : 0 < ε) (hε_one : ε < 1)
    (hα_nonneg : 0 ≤ α) (hα : α ≤ 1 / (k : ℝ)) :
    let c := ε ^ 2 / (6 * (k : ℝ))
    (k : ℝ) * (c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α)) < ε := by
  let κ : ℝ := k
  let c : ℝ := ε ^ 2 / (6 * κ)
  have hκ : 0 < κ := by
    dsimp [κ]
    exact_mod_cast hk
  have hκ_one : 1 ≤ κ := by
    dsimp [κ]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk.ne')
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc_lt_one : c < 1 := by
    dsimp [c]
    have hεsq : ε ^ 2 < 1 := by nlinarith
    have hden : 1 ≤ 6 * κ := by nlinarith
    apply (div_lt_one (by positivity)).2
    nlinarith
  have hterm_nonneg : 0 ≤ c * (1 - c) * α := by
    exact mul_nonneg (mul_nonneg hc_nonneg (sub_nonneg.mpr hc_lt_one.le)) hα_nonneg
  have hradicand :
      c * (1 - c) * α ≤ ε ^ 2 / (6 * κ ^ 2) := by
    have hα' : α ≤ 1 / κ := by simpa [κ] using hα
    have h₁c : 0 ≤ 1 - c := sub_nonneg.mpr hc_lt_one.le
    have h₁c_le : 1 - c ≤ 1 := by linarith
    calc
      c * (1 - c) * α ≤ c * 1 * (1 / κ) := by
        gcongr
      _ = ε ^ 2 / (6 * κ ^ 2) := by
        dsimp [c]
        field_simp
  have hsix_pos : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hsix_sq : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hsqrt_bound :
      Real.sqrt (c * (1 - c) * α) ≤ ε / (Real.sqrt 6 * κ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hright_sq :
          (ε / (Real.sqrt 6 * κ)) ^ 2 = ε ^ 2 / (6 * κ ^ 2) := by
          field_simp
          nlinarith
      rw [hright_sq]
      exact hradicand
  have hfirst : κ * (c * (1 - α)) ≤ ε / 6 := by
    have hα_one : α ≤ 1 := hα.trans (by
      have : 1 / κ ≤ 1 := (div_le_one (by positivity)).2 hκ_one
      exact this)
    have hfirst₀ : κ * (c * (1 - α)) ≤ κ * c := by
      have : 1 - α ≤ 1 := by linarith
      have hinside : c * (1 - α) ≤ c * 1 :=
        mul_le_mul_of_nonneg_left this hc_nonneg
      simpa using mul_le_mul_of_nonneg_left hinside hκ.le
    have hκc : κ * c = ε ^ 2 / 6 := by
      dsimp [c]
      field_simp
    calc
      κ * (c * (1 - α)) ≤ κ * c := hfirst₀
      _ = ε ^ 2 / 6 := hκc
      _ ≤ ε / 6 := by nlinarith
  have hsix_gt : (12 / 5 : ℝ) < Real.sqrt 6 := by
    have hsix_nonneg := Real.sqrt_nonneg 6
    nlinarith
  have htwo_div_six : 2 / Real.sqrt 6 < (5 / 6 : ℝ) := by
    apply (div_lt_iff₀ hsix_pos).2
    nlinarith
  have hsecond :
      κ * (2 * Real.sqrt (c * (1 - c) * α)) < 5 * ε / 6 := by
    have hscaled :
        κ * (2 * Real.sqrt (c * (1 - c) * α)) ≤
          2 * ε / Real.sqrt 6 := by
      calc
        κ * (2 * Real.sqrt (c * (1 - c) * α))
            ≤ κ * (2 * (ε / (Real.sqrt 6 * κ))) := by
              gcongr
        _ = 2 * ε / Real.sqrt 6 := by
              field_simp
    have : 2 * ε / Real.sqrt 6 < 5 * ε / 6 := by
      have := mul_lt_mul_of_pos_right htwo_div_six hε
      convert this using 1 <;> ring
    exact hscaled.trans_lt this
  dsimp
  change κ * (c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α)) < ε
  rw [mul_add]
  linarith

/-- Monotone-cardinality form of `jointRI_rootShrink_constant`.  Rounding the
target cardinality down replaces the retained fraction by some
`c ≤ ε² / (6k)`; the same strict numerical bound still applies. -/
theorem jointRI_rootShrink_constant_of_c_le
    {k : ℕ} (hk : 0 < k) {ε α c : ℝ}
    (hε : 0 < ε) (hε_one : ε < 1)
    (hα_nonneg : 0 ≤ α) (hα : α ≤ 1 / (k : ℝ))
    (hc_nonneg : 0 ≤ c) (hc : c ≤ ε ^ 2 / (6 * (k : ℝ))) :
    (k : ℝ) * (c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α)) < ε := by
  let κ : ℝ := k
  have hκ : 0 < κ := by
    dsimp [κ]
    exact_mod_cast hk
  have hκ_one : 1 ≤ κ := by
    dsimp [κ]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk.ne')
  have hc' : c ≤ ε ^ 2 / (6 * κ) := by simpa [κ] using hc
  have htarget_lt_one : ε ^ 2 / (6 * κ) < 1 := by
    have hεsq : ε ^ 2 < 1 := by nlinarith
    apply (div_lt_one (by positivity)).2
    nlinarith
  have hc_lt_one : c < 1 := hc'.trans_lt htarget_lt_one
  have hterm_nonneg : 0 ≤ c * (1 - c) * α :=
    mul_nonneg (mul_nonneg hc_nonneg (sub_nonneg.mpr hc_lt_one.le)) hα_nonneg
  have hα' : α ≤ 1 / κ := by simpa [κ] using hα
  have hradicand :
      c * (1 - c) * α ≤ ε ^ 2 / (6 * κ ^ 2) := by
    calc
      c * (1 - c) * α ≤ c * 1 * (1 / κ) := by
        gcongr
        linarith
      _ ≤ (ε ^ 2 / (6 * κ)) * (1 / κ) := by
        gcongr
        simpa using hc'
      _ = ε ^ 2 / (6 * κ ^ 2) := by field_simp
  have hsix_pos : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hsix_sq : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hsqrt_bound :
      Real.sqrt (c * (1 - c) * α) ≤ ε / (Real.sqrt 6 * κ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hright_sq :
          (ε / (Real.sqrt 6 * κ)) ^ 2 = ε ^ 2 / (6 * κ ^ 2) := by
          field_simp
          nlinarith
      rw [hright_sq]
      exact hradicand
  have hfirst : κ * (c * (1 - α)) ≤ ε / 6 := by
    have hα_one : α ≤ 1 := hα'.trans ((div_le_one (by positivity)).2 hκ_one)
    calc
      κ * (c * (1 - α)) ≤ κ * c := by
        have hinside : c * (1 - α) ≤ c * 1 := by
          gcongr
          linarith
        simpa using mul_le_mul_of_nonneg_left hinside hκ.le
      _ ≤ ε ^ 2 / 6 := by
        have := mul_le_mul_of_nonneg_left hc' hκ.le
        calc
          κ * c ≤ κ * (ε ^ 2 / (6 * κ)) := this
          _ = ε ^ 2 / 6 := by field_simp
      _ ≤ ε / 6 := by nlinarith
  have hsix_gt : (12 / 5 : ℝ) < Real.sqrt 6 := by
    have hsix_nonneg := Real.sqrt_nonneg 6
    nlinarith
  have htwo_div_six : 2 / Real.sqrt 6 < (5 / 6 : ℝ) := by
    apply (div_lt_iff₀ hsix_pos).2
    nlinarith
  have hsecond :
      κ * (2 * Real.sqrt (c * (1 - c) * α)) < 5 * ε / 6 := by
    have hscaled :
        κ * (2 * Real.sqrt (c * (1 - c) * α)) ≤ 2 * ε / Real.sqrt 6 := by
      calc
        κ * (2 * Real.sqrt (c * (1 - c) * α))
            ≤ κ * (2 * (ε / (Real.sqrt 6 * κ))) := by gcongr
        _ = 2 * ε / Real.sqrt 6 := by field_simp
    have hstrict : 2 * ε / Real.sqrt 6 < 5 * ε / 6 := by
      have := mul_lt_mul_of_pos_right htwo_div_six hε
      convert this using 1 <;> ring
    exact hscaled.trans_lt hstrict
  rw [mul_add]
  linarith

end CommutatorTheorem
