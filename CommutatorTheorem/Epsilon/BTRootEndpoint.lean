import CommutatorTheorem.Epsilon.BTRootShrinkingClose

/-!
# Endpoint cases of refined root shrinking

The strictly admissible positive-variance case is proved in
`BTRootShrinkingClose`.  This file closes the two algebraic endpoints without
a limiting argument:

* at `c = (1+α)⁻¹` the claimed upper bound simplifies exactly to `1`, and
  differentiation preserves the original upper root bound;
* at `α = 0`, all roots vanish, so the polynomial is a power of `X`.
-/

namespace CommutatorTheorem

open scoped Polynomial BigOperators
open Polynomial Finset

/-- A non-strict upper root bound is preserved by one derivative as long as
the original polynomial has degree at least two. -/
theorem derivative_rootUpperBound_of_realRooted
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 2 ≤ p.natDegree)
    {b : ℝ} (hb : IsRootUpperBound p b) :
    IsRootUpperBound p.derivative b := by
  intro r hr
  by_contra hnot
  have hbr : b < r := lt_of_not_ge hnot
  let y := (b + r) / 2
  have hby : b < y := by dsimp [y]; linarith
  have hyr : y < r := by dsimp [y]; linarith
  have hystrict : IsStrictRootUpperBound p y := by
    intro z hz
    exact lt_of_le_of_lt (hb z hz) hby
  have hderiv := hp.derivative_strictRootUpperBound
    (lt_of_lt_of_le (by omega) hdeg) hystrict
  exact (not_lt_of_ge hyr.le) (hderiv r hr)

/-- Every derivative below the degree retains any upper root bound of a
real-rooted polynomial. -/
theorem iterate_derivative_rootUpperBound_of_realRooted
    {p : ℝ[X]} (hp : RealRooted p) {b : ℝ}
    (hb : IsRootUpperBound p b) {d : ℕ} (hd : d < p.natDegree) :
    IsRootUpperBound (Polynomial.derivative^[d] p) b := by
  induction d with
  | zero => simpa using hb
  | succ d ih =>
      have hd0 : d < p.natDegree := by omega
      have hdeg : 2 ≤ (Polynomial.derivative^[d] p).natDegree := by
        rw [natDegree_iterate_derivative_eq_sub_real hd0.le]
        omega
      rw [Function.iterate_succ_apply']
      exact derivative_rootUpperBound_of_realRooted
        (hp.iterate_derivative d) hdeg (ih hd0)

/-- At the admissibility endpoint, the refined target is exactly the original
upper endpoint `1`; hence no barrier limiting argument is needed. -/
theorem rootUpperBound_iterate_derivative_at_admissibility_endpoint
    {p : ℝ[X]} (hp : RealRooted p) {c α : ℝ}
    (hα : 0 < α) (hc : c = (1 + α)⁻¹)
    (hroots : ∀ r, p.IsRoot r → r ≤ 1)
    {d : ℕ} (hd : d < p.natDegree) :
    IsRootUpperBound (Polynomial.derivative^[d] p)
      (c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α)) := by
  have h1α : 0 < 1 + α := by linarith
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcone : c * (1 + α) = 1 := by
    rw [hc]
    exact inv_mul_cancel₀ h1α.ne'
  have hone : 1 - c = c * α := by nlinarith [hcone]
  have hrad : 0 ≤ c * (1 - c) * α := by
    rw [hone]
    positivity
  have hsqrt : Real.sqrt (c * (1 - c) * α) = c * α := by
    apply (Real.sqrt_eq_iff_eq_sq hrad (mul_nonneg hcpos.le hα.le)).2
    rw [hone]
    ring
  have htarget : c * (1 - α) +
      2 * Real.sqrt (c * (1 - c) * α) = 1 := by
    rw [hsqrt]
    nlinarith [hcone]
  rw [htarget]
  exact iterate_derivative_rootUpperBound_of_realRooted hp hroots hd

/-- Zero second moment forces every real root to vanish. -/
theorem roots_eq_zero_of_sum_sq_eq_zero
    {p : ℝ[X]} (hsq : (p.roots.map fun r ↦ r ^ 2).sum = 0) :
    ∀ r ∈ p.roots, r = 0 := by
  let l := p.roots.sort (· ≤ ·)
  have hsum : ∑ i : Fin l.length, (l.get i) ^ 2 = 0 := by
    calc
      ∑ i : Fin l.length, (l.get i) ^ 2 =
          (p.roots.map fun r ↦ r ^ 2).sum := by
        exact (multiset_map_sum_eq_fin_sum_sort p.roots (fun r ↦ r ^ 2)).symm
      _ = 0 := hsq
  have heach : ∀ i : Fin l.length, (l.get i) ^ 2 = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_hj : j ∈ (Finset.univ : Finset (Fin l.length))) ↦ sq_nonneg (l.get j))).mp
      hsum i (Finset.mem_univ i)
  intro r hr
  have hrlist : r ∈ l := by
    exact (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mpr hr
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrlist
  rw [← hi]
  exact sq_eq_zero_iff.mp (heach i)

/-- A monic split polynomial with zero second root moment is a pure power of
`X`. -/
theorem eq_X_pow_of_sum_sq_roots_eq_zero
    {p : ℝ[X]} (hp : RealRooted p) (hmonic : p.Monic)
    (hsq : (p.roots.map fun r ↦ r ^ 2).sum = 0) :
    p = X ^ p.natDegree := by
  have hzero := roots_eq_zero_of_sum_sq_eq_zero (p := p) hsq
  have hroots : p.roots = Multiset.replicate p.roots.card 0 :=
    Multiset.eq_replicate_card.mpr hzero
  rw [hp.eq_prod_roots_of_monic hmonic, hroots]
  simp

/-- The refined root-shrinking conclusion in the zero-variance case. -/
theorem rootUpperBound_iterate_derivative_of_second_moment_zero
    {p : ℝ[X]} (hp : RealRooted p) (hmonic : p.Monic)
    {c : ℝ} (hc : 0 ≤ c)
    (hsq : (p.roots.map fun r ↦ r ^ 2).sum = 0)
    {d : ℕ} (hd : d < p.natDegree) :
    IsRootUpperBound (Polynomial.derivative^[d] p) c := by
  have hpX := eq_X_pow_of_sum_sq_roots_eq_zero hp hmonic hsq
  rw [hpX, Polynomial.iterate_derivative_X_pow_eq_natCast_mul]
  intro r hr
  change Polynomial.eval r
    ((p.natDegree.descFactorial d : ℝ[X]) * X ^ (p.natDegree - d)) = 0 at hr
  simp only [eval_mul, eval_natCast, eval_pow, eval_X] at hr
  have hdesc : (p.natDegree.descFactorial d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hd.le))
  have hrpow : r ^ (p.natDegree - d) = 0 :=
    (mul_eq_zero.mp hr).resolve_left hdesc
  have hr0 : r = 0 := eq_zero_of_pow_eq_zero hrpow
  simpa [hr0] using hc

/-- The complete refined root-shrinking theorem on the closed admissible
parameter range.  The proof combines the strictly admissible theorem with
the two algebraic endpoint arguments above. -/
theorem rootUpperBound_iterate_derivative_of_mean_zero_second_moment_le
    {p : ℝ[X]} (hp : RealRooted p) (hmonic : p.Monic)
    (hdeg : 0 < p.natDegree)
    {c α : ℝ} (hc : 0 < c) (hc1 : c < 1) (hα : 0 ≤ α)
    (hcα : c ≤ (1 + α)⁻¹)
    (hroots : ∀ r, p.IsRoot r → r ≤ 1)
    (hmean : p.roots.sum = 0)
    (hsq : (p.roots.map fun r ↦ r ^ 2).sum = (p.natDegree : ℝ) * α)
    (d : ℕ) (hd : d < p.natDegree)
    (hdc : (d : ℝ) = (p.natDegree : ℝ) * (1 - c)) :
    IsRootUpperBound (Polynomial.derivative^[d] p)
      (c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α)) := by
  by_cases hα0 : α = 0
  · subst α
    have hsq0 : (p.roots.map fun r ↦ r ^ 2).sum = 0 := by
      simpa using hsq
    simpa using rootUpperBound_iterate_derivative_of_second_moment_zero
      hp hmonic hc.le hsq0 hd
  · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    rcases hcα.lt_or_eq with hcαlt | hcαeq
    · exact rootUpperBound_iterate_derivative_of_mean_zero_second_moment
        hp hdeg hc hc1 hαpos hcαlt hroots hmean hsq d hd hdc
    · exact rootUpperBound_iterate_derivative_at_admissibility_endpoint
        hp hαpos hcαeq hroots hd

end CommutatorTheorem
