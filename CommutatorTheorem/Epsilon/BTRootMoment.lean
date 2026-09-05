import CommutatorTheorem.Epsilon.BTRootShrinking

/-!
# Root moments and the optimized initial barrier

This file formalizes the moment algebra behind the refined
Ravichandran--Srivastava root-shrinking bound.  It contains three independent
pieces:

* the first two root moments in terms of the first two lower coefficients;
* a quadratic majorant for the reciprocal barrier using only mean zero and
  the second moment;
* the exact scalar optimization which produces
  `c * (1 - α) + 2 * sqrt (c * (1 - c) * α)` and explains the condition
  `c ≤ (1 + α)⁻¹`.

There are no axioms or placeholders in this file.
-/

namespace CommutatorTheorem

open scoped Polynomial BigOperators
open Polynomial Finset

/-! ## Vieta/Newton identities for the first two root moments -/

/-- Average of the roots, counted with multiplicity. -/
noncomputable def rootMean (p : ℝ[X]) : ℝ :=
  p.roots.sum / (p.natDegree : ℝ)

/-- Average of the squares of the roots, counted with multiplicity. -/
noncomputable def rootMeanSquare (p : ℝ[X]) : ℝ :=
  (p.roots.map fun r ↦ r ^ 2).sum / (p.natDegree : ℝ)

/-- For a monic split polynomial, the sum of the roots is the negative of the
next coefficient. -/
theorem sum_roots_eq_neg_nextCoeff {p : ℝ[X]} (hp : RealRooted p)
    (hmonic : p.Monic) :
    p.roots.sum = -p.nextCoeff := by
  rw [hp.nextCoeff_eq_neg_sum_roots_of_monic hmonic]
  simp

/-- Coefficient form of the normalized root mean. -/
theorem rootMean_eq_neg_nextCoeff_div_natDegree
    {p : ℝ[X]} (hp : RealRooted p) (hmonic : p.Monic) :
    rootMean p = -p.nextCoeff / (p.natDegree : ℝ) := by
  rw [rootMean, sum_roots_eq_neg_nextCoeff hp hmonic]

/-- In positive degree, mean zero is exactly vanishing next coefficient. -/
theorem rootMean_eq_zero_iff_nextCoeff_eq_zero
    {p : ℝ[X]} (hp : RealRooted p) (hmonic : p.Monic)
    (hdeg : 0 < p.natDegree) :
    rootMean p = 0 ↔ p.nextCoeff = 0 := by
  rw [rootMean_eq_neg_nextCoeff_div_natDegree hp hmonic]
  have hn : (p.natDegree : ℝ) ≠ 0 := by exact_mod_cast hdeg.ne'
  constructor
  · intro h
    apply neg_eq_zero.mp
    exact (div_eq_zero_iff.mp h).resolve_right hn
  · intro h
    simp [h]

set_option linter.flexible false in
/-- The degree-two Newton identity for an arbitrary real multiset. -/
theorem two_mul_esymm_two_real (s : Multiset ℝ) :
    2 * s.esymm 2 = s.sum ^ 2 - (s.map fun z ↦ z ^ 2).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm]
  | cons z s ih =>
      have hesymm : (z ::ₘ s).esymm 2 = s.esymm 2 + z * s.sum := by
        simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]
        rw [Multiset.sum_map_mul_left]
        simp
      rw [hesymm, mul_add, ih]
      simp only [Multiset.sum_cons, Multiset.map_cons]
      ring

/-- The coefficient two below the leading term is half the second Newton
numerator of the roots. -/
theorem coeff_sub_two_eq_root_moments {p : ℝ[X]} (hp : RealRooted p)
    (hmonic : p.Monic) (hdeg : 2 ≤ p.natDegree) :
    p.coeff (p.natDegree - 2) =
      (p.roots.sum ^ 2 - (p.roots.map fun z ↦ z ^ 2).sum) / 2 := by
  have hle : p.natDegree - 2 ≤ p.natDegree := Nat.sub_le _ _
  have hcoeff := Polynomial.coeff_eq_esymm_roots_of_splits
    (k := p.natDegree - 2) hp hle
  have hsub : p.natDegree - (p.natDegree - 2) = 2 := by omega
  have hc : p.coeff (p.natDegree - 2) = p.roots.esymm 2 := by
    simpa [hsub, hmonic.leadingCoeff] using hcoeff
  rw [hc]
  apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  rw [mul_comm, two_mul_esymm_two_real]

/-- In the mean-zero case the second root moment is exactly minus twice the
second lower coefficient. -/
theorem sum_sq_roots_eq_neg_two_mul_coeff_sub_two
    {p : ℝ[X]} (hp : RealRooted p) (hmonic : p.Monic)
    (hdeg : 2 ≤ p.natDegree) (hmean : p.roots.sum = 0) :
    (p.roots.map fun z ↦ z ^ 2).sum =
      -2 * p.coeff (p.natDegree - 2) := by
  rw [coeff_sub_two_eq_root_moments hp hmonic hdeg, hmean]
  ring

/-- Mean-zero coefficient form of the normalized second root moment. -/
theorem rootMeanSquare_eq_neg_two_mul_coeff_div_natDegree
    {p : ℝ[X]} (hp : RealRooted p) (hmonic : p.Monic)
    (hdeg : 2 ≤ p.natDegree) (hmean : rootMean p = 0) :
    rootMeanSquare p =
      (-2 * p.coeff (p.natDegree - 2)) / (p.natDegree : ℝ) := by
  have hn : (p.natDegree : ℝ) ≠ 0 := by
    exact_mod_cast (show p.natDegree ≠ 0 by omega)
  have hsum : p.roots.sum = 0 := by
    dsimp [rootMean] at hmean
    exact (div_eq_zero_iff.mp hmean).resolve_right hn
  rw [rootMeanSquare, sum_sq_roots_eq_neg_two_mul_coeff_sub_two
    hp hmonic hdeg hsum]

/-- With mean zero, prescribing the second root moment is equivalent to
prescribing the coefficient two below the leading term. -/
theorem rootMeanSquare_eq_iff_coeff_sub_two_eq
    {p : ℝ[X]} (hp : RealRooted p) (hmonic : p.Monic)
    (hdeg : 2 ≤ p.natDegree) (hmean : rootMean p = 0) (α : ℝ) :
    rootMeanSquare p = α ↔
      p.coeff (p.natDegree - 2) = -(p.natDegree : ℝ) * α / 2 := by
  rw [rootMeanSquare_eq_neg_two_mul_coeff_div_natDegree hp hmonic hdeg hmean]
  have hn : (p.natDegree : ℝ) ≠ 0 := by
    exact_mod_cast (show p.natDegree ≠ 0 by omega)
  constructor <;> intro h
  · field_simp [hn] at h ⊢
    linarith
  · field_simp [hn] at h ⊢
    linarith

/-! ## A moment majorant for the initial barrier -/

/-- The quadratic which majorizes `r ↦ (b-r)⁻¹` on `r ≤ 1` and is tangent at
`r = -α`. -/
noncomputable def rootMomentMajorant (b α r : ℝ) : ℝ :=
  1 / (b + α) + (r + α) / (b + α) ^ 2 +
    (r + α) ^ 2 / ((b - 1) * (b + α) ^ 2)

/-- Pointwise reciprocal majorization.  The difference factors as a positive
multiple of `(1-r)(r+α)²`. -/
theorem one_div_sub_le_rootMomentMajorant {b α r : ℝ}
    (hb : 1 < b) (hα : 0 ≤ α) (hr : r ≤ 1) :
    1 / (b - r) ≤ rootMomentMajorant b α r := by
  have hbα : 0 < b + α := by linarith
  have hbr : 0 < b - r := by linarith
  have hb1 : 0 < b - 1 := by linarith
  have hid :
      rootMomentMajorant b α r - 1 / (b - r) =
        (1 - r) * (r + α) ^ 2 /
          ((b - 1) * (b + α) ^ 2 * (b - r)) := by
    dsimp [rootMomentMajorant]
    field_simp [hbα.ne', hbr.ne', hb1.ne']
    ring
  rw [← sub_nonneg, hid]
  apply div_nonneg
  · exact mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg _)
  · exact (mul_pos (mul_pos hb1 (sq_pos_of_pos hbα)) hbr).le

/-- Summing the quadratic majorant eliminates its linear term under the
mean-zero hypothesis and replaces its quadratic term by the second moment. -/
theorem sum_rootMomentMajorant_of_moments
    {ι : Type*} [Fintype ι] (r : ι → ℝ) {b α : ℝ}
    (hb : 1 < b) (hα : 0 ≤ α)
    (hmean : ∑ i, r i = 0)
    (hsq : ∑ i, (r i) ^ 2 = (Fintype.card ι : ℝ) * α) :
    ∑ i, rootMomentMajorant b α (r i) =
      (Fintype.card ι : ℝ) *
        ((b + α - 1) / ((b - 1) * (b + α))) := by
  classical
  let N : ℝ := Fintype.card ι
  have hshift : ∑ i, (r i + α) = N * α := by
    dsimp [N]
    rw [Finset.sum_add_distrib, hmean]
    simp
  have hshiftSq : ∑ i, (r i + α) ^ 2 = N * (α + α ^ 2) := by
    calc
      ∑ i, (r i + α) ^ 2 =
          ∑ i, ((r i) ^ 2 + 2 * α * r i + α ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (r i) ^ 2) + 2 * α * (∑ i, r i) + N * α ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
        dsimp [N]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = N * (α + α ^ 2) := by rw [hmean, hsq]; ring
  dsimp [rootMomentMajorant]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.sum_div, hshift, ← Finset.sum_div, hshiftSq]
  dsimp [N]
  have hbα : b + α ≠ 0 := (by linarith : 0 < b + α).ne'
  have hb1 : b - 1 ≠ 0 := (by linarith : 0 < b - 1).ne'
  field_simp [hbα, hb1]
  ring

/-- Finite moment form of the refined initial-barrier estimate. -/
theorem sum_reciprocal_le_of_mean_zero_second_moment
    {ι : Type*} [Fintype ι] (r : ι → ℝ) {b α : ℝ}
    (hb : 1 < b) (hα : 0 ≤ α) (hr : ∀ i, r i ≤ 1)
    (hmean : ∑ i, r i = 0)
    (hsq : ∑ i, (r i) ^ 2 = (Fintype.card ι : ℝ) * α) :
    ∑ i, 1 / (b - r i) ≤
      (Fintype.card ι : ℝ) *
        ((b + α - 1) / ((b - 1) * (b + α))) := by
  calc
    ∑ i, 1 / (b - r i) ≤ ∑ i, rootMomentMajorant b α (r i) := by
      exact Finset.sum_le_sum fun i _ ↦ one_div_sub_le_rootMomentMajorant hb hα (hr i)
    _ = _ := sum_rootMomentMajorant_of_moments r hb hα hmean hsq

/-- Polynomial form of the same potential estimate, with roots counted with
multiplicity. -/
theorem rootBarrierPotential_le_of_mean_zero_second_moment
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 0 < p.natDegree)
    {b α : ℝ} (hb : 1 < b) (hα : 0 ≤ α)
    (hroots : ∀ r, p.IsRoot r → r ≤ 1)
    (hmean : p.roots.sum = 0)
    (hsq : (p.roots.map fun r ↦ r ^ 2).sum = (p.natDegree : ℝ) * α) :
    rootBarrierPotential p b ≤
      (p.natDegree : ℝ) *
        ((b + α - 1) / ((b - 1) * (b + α))) := by
  have hp0 : p ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  have hbeval : p.eval b ≠ 0 := by
    intro hzero
    have := hroots b hzero
    linarith
  rw [rootBarrierPotential_eq_sum_roots hp hbeval]
  rw [multiset_map_sum_eq_fin_sum_sort]
  let l := p.roots.sort (· ≤ ·)
  have hlen : l.length = p.natDegree := by
    simp [l, hp.natDegree_eq_card_roots]
  have hmean' : ∑ i : Fin l.length, l.get i = 0 := by
    rw [← list_sum_eq_fin_sum]
    dsimp [l]
    rw [← Multiset.sum_coe, Multiset.sort_eq]
    exact hmean
  have hsq' : ∑ i : Fin l.length, (l.get i) ^ 2 =
      (Fintype.card (Fin l.length) : ℝ) * α := by
    calc
      ∑ i : Fin l.length, (l.get i) ^ 2 =
          (p.roots.map fun r ↦ r ^ 2).sum := by
        exact (multiset_map_sum_eq_fin_sum_sort p.roots (fun r ↦ r ^ 2)).symm
      _ = (p.natDegree : ℝ) * α := hsq
      _ = (Fintype.card (Fin l.length) : ℝ) * α := by
        simp only [Fintype.card_fin]
        rw [hlen]
  have hr' : ∀ i : Fin l.length, l.get i ≤ 1 := by
    intro i
    have hmem : l.get i ∈ p.roots := by
      exact (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mp (l.get_mem i)
    exact hroots _ ((mem_roots hp0).mp hmem)
  simpa [l, hlen] using
    (sum_reciprocal_le_of_mean_zero_second_moment
      (fun i : Fin l.length ↦ l.get i) hb hα hr' hmean' hsq')

/-! ## The monotone-potential bridge for fixed-`φ` iteration -/

/-- To the right of every root, the barrier potential of a real-rooted
polynomial is antitone. -/
theorem rootBarrierPotential_anti_of_strictRootUpperBound
    {p : ℝ[X]} (hp : RealRooted p) {x y : ℝ}
    (hx : IsStrictRootUpperBound p x) (hxy : x ≤ y) :
    rootBarrierPotential p y ≤ rootBarrierPotential p x := by
  have hp0 : p ≠ 0 := by
    intro hzero
    have hroot : p.IsRoot x := by simp [hzero]
    exact (lt_irrefl x) (hx x hroot)
  have hy : IsStrictRootUpperBound p y := by
    intro r hr
    exact lt_of_lt_of_le (hx r hr) hxy
  have hxeval : p.eval x ≠ 0 := by
    intro hzero
    exact (lt_irrefl x) (hx x hzero)
  have hyeval : p.eval y ≠ 0 := by
    intro hzero
    exact (lt_irrefl y) (hy y hzero)
  rw [rootBarrierPotential_eq_sum_roots hp hyeval,
    rootBarrierPotential_eq_sum_roots hp hxeval]
  rw [multiset_map_sum_eq_fin_sum_sort, multiset_map_sum_eq_fin_sum_sort]
  apply Finset.sum_le_sum
  intro i _
  have hmem : (p.roots.sort (· ≤ ·)).get i ∈ p.roots := by
    exact (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mp
      ((p.roots.sort (· ≤ ·)).get_mem i)
  have hgap : 0 < x - (p.roots.sort (· ≤ ·)).get i := by
    exact sub_pos.mpr (hx _ ((mem_roots hp0).mp hmem))
  exact one_div_le_one_div_of_le hgap (by linarith)

/-- Over `ℝ`, every derivative below the degree drops the degree by exactly
one, hence an iterated derivative has the expected degree. -/
theorem natDegree_iterate_derivative_eq_sub_real
    {p : ℝ[X]} {k : ℕ} (hk : k ≤ p.natDegree) :
    (Polynomial.derivative^[k] p).natDegree = p.natDegree - k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk0 : k ≤ p.natDegree := by omega
      have hklt : k < p.natDegree := by omega
      have hdegk : (Polynomial.derivative^[k] p).natDegree = p.natDegree - k := ih hk0
      have hpos : 0 < (Polynomial.derivative^[k] p).natDegree := by
        rw [hdegk]
        omega
      rw [Function.iterate_succ_apply']
      have hdegree := Polynomial.degree_derivative_eq
        (Polynomial.derivative^[k] p) hpos
      have hnat := Polynomial.natDegree_eq_of_degree_eq_some hdegree
      rw [hdegk] at hnat
      simpa only [Nat.succ_eq_add_one, Nat.sub_add_eq] using hnat

/-! ## Exact optimization of the barrier objective -/

/-- The scalar objective obtained after inserting the moment bound into the
iterated barrier displacement. -/
noncomputable def rootShrinkMomentObjective (b c α : ℝ) : ℝ :=
  b - (1 - c) * (b - 1) * (b + α) / (b + α - 1)

/-- Reparameterizing by `v = b + α - 1` exposes the AM--GM optimization. -/
theorem rootShrinkMomentObjective_eq {b c α : ℝ}
    (hv : b + α - 1 ≠ 0) :
    rootShrinkMomentObjective b c α =
      c * (1 - α) + c * (b + α - 1) +
        (1 - c) * α / (b + α - 1) := by
  dsimp [rootShrinkMomentObjective]
  field_simp [hv]
  ring

/-- At the optimizing barrier, the objective is exactly the refined
root-shrinking expression. -/
theorem rootShrinkMomentObjective_at_optimum
    {c α : ℝ} (hc : 0 < c) (hc1 : c < 1) (hα : 0 < α) :
    let v := Real.sqrt ((1 - c) * α / c)
    let b := 1 - α + v
    rootShrinkMomentObjective b c α =
      c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α) := by
  dsimp only
  let v := Real.sqrt ((1 - c) * α / c)
  let b := 1 - α + v
  change rootShrinkMomentObjective b c α =
    c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α)
  have hrad : 0 < (1 - c) * α / c :=
    div_pos (mul_pos (sub_pos.mpr hc1) hα) hc
  have hv : 0 < v := Real.sqrt_pos.2 hrad
  have hvsq : v ^ 2 = (1 - c) * α / c := Real.sq_sqrt hrad.le
  have hvb : b + α - 1 = v := by dsimp [b]; ring
  rw [rootShrinkMomentObjective_eq (by rw [hvb]; exact hv.ne')]
  rw [hvb]
  have hsqrt : Real.sqrt (c * (1 - c) * α) = c * v := by
    apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hc1.le)) hα.le)
      (mul_nonneg hc.le hv.le)).2
    rw [mul_pow, hvsq]
    field_simp [hc.ne']
  rw [hsqrt]
  have hkey : c * v ^ 2 = (1 - c) * α := by
    rw [hvsq]
    field_simp [hc.ne']
  have hfrac : (1 - c) * α / v = c * v := by
    apply (div_eq_iff hv.ne').2
    calc
      (1 - c) * α = c * v ^ 2 := hkey.symm
      _ = (c * v) * v := by ring
  rw [hfrac]
  ring

/-- The admissibility condition `c ≤ (1+α)⁻¹` puts the optimizing barrier at
or to the right of `1`, exactly as required by the root interval hypothesis. -/
theorem one_le_optimal_rootMoment_barrier
    {c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hcα : c ≤ (1 + α)⁻¹) :
    1 ≤ 1 - α + Real.sqrt ((1 - c) * α / c) := by
  have h1α : 0 < 1 + α := by linarith
  have hc1 : c < 1 := lt_of_le_of_lt hcα (by
    rw [inv_lt_one₀ h1α]
    linarith)
  have hrad : 0 ≤ (1 - c) * α / c :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hc1.le) hα.le) hc.le
  have hsquare : α ^ 2 ≤ (1 - c) * α / c := by
    rw [le_div_iff₀ hc]
    have hcineq : c * (1 + α) ≤ 1 := by
      exact (le_div_iff₀ h1α).mp (by simpa [one_div] using hcα)
    nlinarith
  have hsqrt : α ≤ Real.sqrt ((1 - c) * α / c) := by
    calc
      α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα.le).symm
      _ ≤ Real.sqrt ((1 - c) * α / c) := Real.sqrt_le_sqrt hsquare
  linarith

end CommutatorTheorem
