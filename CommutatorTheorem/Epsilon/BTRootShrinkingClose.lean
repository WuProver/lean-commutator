import CommutatorTheorem.Epsilon.BTRootShrinking
import CommutatorTheorem.Epsilon.BTRootMoment

/-!
# Closing the one-step derivative barrier

This file turns the finite reciprocal-gap inequality from `BTRootShrinking` into the
logarithmic-derivative identity used by the root-shrinking argument.
-/

namespace CommutatorTheorem

open scoped Polynomial BigOperators
open Polynomial Finset

/-- The curvature identity, divided through by the two nonzero polynomial values. -/
lemma rootBarrierPotential_derivative_eq_sub_curvature
    {p : ℝ[X]} (hp : RealRooted p) {x : ℝ}
    (hp0 : p.eval x ≠ 0) (hdp0 : p.derivative.eval x ≠ 0) :
    rootBarrierPotential p.derivative x =
      rootBarrierPotential p x -
        rootBarrierCurvature p x / rootBarrierPotential p x := by
  have hcurv := rootBarrier_curvature_identity hp hp0
  have hpot0 : rootBarrierPotential p x ≠ 0 := by
    rw [rootBarrierPotential]
    exact div_ne_zero hdp0 hp0
  rw [rootBarrierPotential, rootBarrierPotential]
  field_simp [hp0, hdp0]
  nlinarith

/-- If a point is strictly to the right of every root of a split polynomial, its barrier
potential is positive. -/
lemma rootBarrierPotential_pos_of_strictRootUpperBound
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 0 < p.natDegree) {x : ℝ}
    (hx : IsStrictRootUpperBound p x) : 0 < rootBarrierPotential p x := by
  have hp0 : p ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  have heval : p.eval x ≠ 0 := by
    intro hzero
    exact (lt_irrefl x) (hx x hzero)
  rw [rootBarrierPotential_eq_sum_roots hp heval]
  rw [multiset_map_sum_eq_fin_sum_sort]
  let l := p.roots.sort (· ≤ ·)
  have hlen : 0 < l.length := by
    simpa [l, hp.natDegree_eq_card_roots] using hdeg
  haveI : Nonempty (Fin l.length) := Fin.pos_iff_nonempty.mp hlen
  apply Finset.sum_pos (s := (Finset.univ : Finset (Fin l.length)))
  · intro i _
    have hmem : l.get i ∈ p.roots := by
      exact (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mp (l.get_mem i)
    exact one_div_pos.mpr (sub_pos.mpr (hx _ ((mem_roots hp0).mp hmem)))
  · exact Finset.univ_nonempty

/-- A strict upper bound for the roots of `p` is also a strict upper bound for the roots of
`p'`, provided `p` is split and has positive degree.  The proof uses positivity of the
logarithmic derivative to the right of all roots. -/
lemma RealRooted.derivative_strictRootUpperBound
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 0 < p.natDegree) {x : ℝ}
    (hx : IsStrictRootUpperBound p x) : IsStrictRootUpperBound p.derivative x := by
  have hp0 : p ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  intro r hr
  by_contra hnot
  have hxr : x ≤ r := le_of_not_gt hnot
  have hstrict_r : IsStrictRootUpperBound p r := by
    intro y hy
    exact lt_of_lt_of_le (hx y hy) hxr
  have hpeval : p.eval r ≠ 0 := by
    intro hzero
    exact (lt_irrefl r) (hstrict_r r hzero)
  have hbarrier_pos := rootBarrierPotential_pos_of_strictRootUpperBound hp hdeg hstrict_r
  rw [rootBarrierPotential] at hbarrier_pos
  have hderiv_ne : p.derivative.eval r ≠ 0 := by
    intro hzero
    simp [hzero] at hbarrier_pos
  exact hderiv_ne hr

/-- Elementary reciprocal-gap algebra, kept separate so that root-list accessors do not obscure
the field normalization. -/
lemma reciprocal_gap_at_shift {b r A : ℝ} (hA : A ≠ 0) (hgap : b - r ≠ 0) :
    1 / (b - 1 / A - r) =
      (1 / (b - r)) * A / (A - 1 / (b - r)) := by
  field_simp [hA, hgap]
  ring

/-- Over the reals, taking a derivative lowers every positive natural degree by exactly one. -/
lemma natDegree_derivative_eq_sub_one {p : ℝ[X]} (hdeg : 0 < p.natDegree) :
    p.derivative.natDegree = p.natDegree - 1 := by
  exact natDegree_eq_of_degree_eq_some (degree_derivative_eq p hdeg)

/-- Exact degree bookkeeping for an iterated real derivative before it vanishes. -/
lemma natDegree_iterate_derivative_eq_sub {p : ℝ[X]} {j : ℕ}
    (hj : j ≤ p.natDegree) :
    (Polynomial.derivative^[j] p).natDegree = p.natDegree - j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjle : j ≤ p.natDegree := Nat.le_trans (Nat.le_succ j) hj
      have hpos : 0 < (Polynomial.derivative^[j] p).natDegree := by
        rw [ih hjle]
        omega
      rw [Function.iterate_succ_apply', natDegree_derivative_eq_sub_one hpos, ih hjle]
      omega

/-- The barrier potential is antitone as its argument moves right while staying beyond all
roots. -/
lemma rootBarrierPotential_antitone
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 0 < p.natDegree) {x y : ℝ}
    (hx : IsStrictRootUpperBound p x) (hxy : x ≤ y) :
    rootBarrierPotential p y ≤ rootBarrierPotential p x := by
  have hp0 : p ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
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
  have hroot := (mem_roots hp0).mp hmem
  apply one_div_le_one_div_of_le (sub_pos.mpr (hx _ hroot))
  linarith

/-- The complete one-step barrier shift.  For a split polynomial of degree at least two,
the logarithmic derivative at any strict upper root bound supplies a barrier certificate one
derivative later, shifted left by its reciprocal.

This is the one-variable step in the Ravichandran--Srivastava root-shrinking argument. -/
theorem derivativeBarrierStep_of_realRooted
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 2 ≤ p.natDegree) {b : ℝ}
    (hb : IsStrictRootUpperBound p b) :
    DerivativeBarrierStep p b (rootBarrierPotential p b) := by
  have hp0 : p ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  have hdegpos : 0 < p.natDegree := lt_of_lt_of_le (by omega) hdeg
  have hbeval : p.eval b ≠ 0 := by
    intro hzero
    exact (lt_irrefl b) (hb b hzero)
  let l := p.roots.sort (· ≤ ·)
  let a : Fin l.length → ℝ := fun i ↦ 1 / (b - l.get i)
  let A : ℝ := ∑ i, a i
  have hlen : 2 ≤ l.length := by
    simpa [l, hp.natDegree_eq_card_roots] using hdeg
  have ha : ∀ i, 0 < a i := by
    intro i
    have hmem : l.get i ∈ p.roots := by
      exact (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mp (l.get_mem i)
    exact one_div_pos.mpr (sub_pos.mpr (hb _ ((mem_roots hp0).mp hmem)))
  haveI : Nonempty (Fin l.length) := Fin.pos_iff_nonempty.mp (lt_of_lt_of_le (by omega) hlen)
  have hA : 0 < A := by
    exact Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
  have hproper : ∀ i, a i < A := by
    intro i
    obtain ⟨u, v, huv⟩ :=
      Fintype.one_lt_card_iff.mp (show 1 < Fintype.card (Fin l.length) by simpa using hlen)
    let j := if u = i then v else u
    have hji : j ≠ i := by
      dsimp [j]
      split_ifs with hui
      · intro hvi
        apply huv
        exact hui.trans hvi.symm
      · exact hui
    exact Finset.single_lt_sum hji (Finset.mem_univ i) (Finset.mem_univ j) (ha j)
      (fun k _ _ ↦ (ha k).le)
  have hpot_old : rootBarrierPotential p b = A := by
    rw [rootBarrierPotential_eq_sum_roots hp hbeval]
    rw [multiset_map_sum_eq_fin_sum_sort]
  have hshift_strict : IsStrictRootUpperBound p (b - 1 / A) := by
    intro r hr
    have hrmem : r ∈ l := by
      exact (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mpr
        ((mem_roots hp0).mpr hr)
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrmem
    have hai := ha i
    have haiA := hproper i
    have hgap : 0 < b - l.get i := one_div_pos.mp hai
    have hcalc : l.get i < b - 1 / A := by
      dsimp [a] at haiA
      have hinv : 1 / A < b - l.get i := (one_div_lt hgap hA).mp haiA
      linarith
    rw [← hi]
    exact hcalc
  have hshift_eval : p.eval (b - 1 / A) ≠ 0 := by
    intro hzero
    exact (lt_irrefl (b - 1 / A)) (hshift_strict _ hzero)
  have hderiv_strict : IsStrictRootUpperBound p.derivative (b - 1 / A) :=
    hp.derivative_strictRootUpperBound hdegpos hshift_strict
  have hderiv_eval : p.derivative.eval (b - 1 / A) ≠ 0 := by
    intro hzero
    exact (lt_irrefl (b - 1 / A)) (hderiv_strict _ hzero)
  let t : Fin l.length → ℝ := fun i ↦ a i * A / (A - a i)
  have htransform : ∀ i, 1 / (b - 1 / A - l.get i) = t i := by
    intro i
    have hgap : 0 < b - l.get i := one_div_pos.mp (ha i)
    have hdenA : A ≠ 0 := hA.ne'
    have hdenGap : b - l.get i ≠ 0 := hgap.ne'
    dsimp [t, a]
    exact reciprocal_gap_at_shift hdenA hdenGap
  have hpot_shift : rootBarrierPotential p (b - 1 / A) = ∑ i, t i := by
    rw [rootBarrierPotential_eq_sum_roots hp hshift_eval]
    rw [multiset_map_sum_eq_fin_sum_sort]
    apply Finset.sum_congr rfl
    intro i _
    exact htransform i
  have hcurv_shift : rootBarrierCurvature p (b - 1 / A) = ∑ i, (t i) ^ 2 := by
    rw [rootBarrierCurvature, multiset_map_sum_eq_fin_sum_sort]
    apply Finset.sum_congr rfl
    intro i _
    rw [htransform i]
  have hscalar := reciprocal_gap_barrier_sum a ha hA hproper
  have hderiv_potential := rootBarrierPotential_derivative_eq_sub_curvature
    hp hshift_eval hderiv_eval
  refine ⟨?_, hb, ?_, ?_⟩
  · simpa [hpot_old] using hA
  · simpa [hpot_old] using hderiv_strict
  · rw [hpot_old]
    rw [hderiv_potential, hpot_shift, hcurv_shift]
    simpa [t, A] using hscalar

/-- Fixed-potential form of the one-step lemma.  This is the form that iterates: an upper
bound `φ` for the current potential remains an upper bound after differentiating and moving
left by `1 / φ`. -/
theorem derivativeBarrierStep_of_realRooted_le
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 2 ≤ p.natDegree) {b φ : ℝ}
    (hb : IsStrictRootUpperBound p b) (hφ : 0 < φ)
    (hpot : rootBarrierPotential p b ≤ φ) :
    DerivativeBarrierStep p b φ := by
  let A := rootBarrierPotential p b
  have hA : 0 < A := rootBarrierPotential_pos_of_strictRootUpperBound hp
    (lt_of_lt_of_le (by omega) hdeg) hb
  have hAle : A ≤ φ := hpot
  have hstep := derivativeBarrierStep_of_realRooted hp hdeg hb
  have hpoints : b - 1 / A ≤ b - 1 / φ := by
    have hinv : 1 / φ ≤ 1 / A := one_div_le_one_div_of_le hA hAle
    linarith
  have hstrict : IsStrictRootUpperBound p.derivative (b - 1 / φ) := by
    intro r hr
    exact lt_of_lt_of_le (hstep.2.2.1 r hr) hpoints
  have hderivdeg : 0 < p.derivative.natDegree := by
    rw [natDegree_derivative_eq_sub_one (lt_of_lt_of_le (by omega) hdeg)]
    omega
  have hmono := rootBarrierPotential_antitone hp.derivative hderivdeg hstep.2.2.1 hpoints
  refine ⟨hφ, hb, hstrict, ?_⟩
  exact hmono.trans (hstep.2.2.2.trans hAle)

/-- Automatic fixed-potential iteration.  As long as fewer derivatives are taken than the
degree, every root of the iterated derivative stays below the linearly shifted barrier. -/
theorem iterate_derivative_rootUpperBound_of_initial_barrier
    {p : ℝ[X]} (hp : RealRooted p) {b φ : ℝ} (hφ : 0 < φ)
    (hb : IsStrictRootUpperBound p b) (hpot : rootBarrierPotential p b ≤ φ)
    (d : ℕ) (hd : d < p.natDegree) :
    IsRootUpperBound (Polynomial.derivative^[d] p) (b - (d : ℝ) / φ) := by
  have hinvariant : ∀ j ≤ d,
      IsStrictRootUpperBound (Polynomial.derivative^[j] p) (b - (j : ℝ) / φ) ∧
        rootBarrierPotential (Polynomial.derivative^[j] p) (b - (j : ℝ) / φ) ≤ φ := by
    intro j hj
    induction j with
    | zero => simpa using And.intro hb hpot
    | succ j ih =>
        have hjle : j ≤ d := Nat.le_trans (Nat.le_succ j) hj
        obtain ⟨hjstrict, hjpot⟩ := ih hjle
        have hjltdeg : j < p.natDegree := lt_of_le_of_lt hjle hd
        have hdegexact := natDegree_iterate_derivative_eq_sub
          (p := p) (j := j) hjltdeg.le
        have hdeg2 : 2 ≤ (Polynomial.derivative^[j] p).natDegree := by
          rw [hdegexact]
          omega
        have hreal := hp.iterate_derivative j
        have hstep := derivativeBarrierStep_of_realRooted_le hreal hdeg2 hjstrict hφ hjpot
        have hpoly : Polynomial.derivative^[j + 1] p =
            (Polynomial.derivative^[j] p).derivative := by
          rw [Function.iterate_succ_apply']
        have hpoint : b - ((j + 1 : ℕ) : ℝ) / φ =
            b - (j : ℝ) / φ - 1 / φ := by
          push_cast
          field_simp [hφ.ne']
          ring
        rw [hpoly, hpoint]
        exact ⟨hstep.2.2.1, hstep.2.2.2⟩
  have hfinal := (hinvariant d le_rfl).1
  intro r hr
  exact (hfinal r hr).le

/-- Strict admissibility puts the optimized moment barrier strictly to the right of `1`.
The non-strict endpoint is available as `one_le_optimal_rootMoment_barrier`; the strict form is
what lets the barrier proof avoid evaluating at a possible root equal to `1`. -/
lemma one_lt_optimal_rootMoment_barrier
    {c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hcα : c < (1 + α)⁻¹) :
    1 < 1 - α + Real.sqrt ((1 - c) * α / c) := by
  have h1α : 0 < 1 + α := by linarith
  have hcineq : c * (1 + α) < 1 := by
    apply (lt_div_iff₀ h1α).mp
    simpa [one_div] using hcα
  have hsquare : α ^ 2 < (1 - c) * α / c := by
    rw [lt_div_iff₀ hc]
    nlinarith [mul_pos hα (sub_pos.mpr hcineq)]
  have hsqrt : α < Real.sqrt ((1 - c) * α / c) := by
    calc
      α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα.le).symm
      _ < Real.sqrt ((1 - c) * α / c) := Real.sqrt_lt_sqrt (sq_nonneg α) hsquare
  linarith

/-- The refined mean/second-moment root-shrinking theorem at every strictly admissible
parameter.  Roots are counted with multiplicity in the moment assumptions, and `d` is the
number of derivatives, related to the retained fraction by `d/n = 1-c`.

The endpoint `c = (1+α)⁻¹` requires a limiting argument when `1` itself is a root; the
strict inequality here is the exact algebraic theorem obtained without that topological
closure step. -/
theorem rootUpperBound_iterate_derivative_of_mean_zero_second_moment
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 0 < p.natDegree)
    {c α : ℝ} (hc : 0 < c) (hc1 : c < 1) (hα : 0 < α)
    (hcα : c < (1 + α)⁻¹)
    (hroots : ∀ r, p.IsRoot r → r ≤ 1)
    (hmean : p.roots.sum = 0)
    (hsq : (p.roots.map fun r ↦ r ^ 2).sum = (p.natDegree : ℝ) * α)
    (d : ℕ) (hd : d < p.natDegree)
    (hdc : (d : ℝ) = (p.natDegree : ℝ) * (1 - c)) :
    IsRootUpperBound (Polynomial.derivative^[d] p)
      (c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α)) := by
  let b := 1 - α + Real.sqrt ((1 - c) * α / c)
  let φ := (p.natDegree : ℝ) * ((b + α - 1) / ((b - 1) * (b + α)))
  have hb : 1 < b := one_lt_optimal_rootMoment_barrier hc hα hcα
  have hbα : 0 < b + α := by linarith
  have hbnum : 0 < b + α - 1 := by linarith
  have hn : 0 < (p.natDegree : ℝ) := by exact_mod_cast hdeg
  have hφ : 0 < φ := by
    dsimp [φ]
    exact mul_pos hn (div_pos hbnum (mul_pos (sub_pos.mpr hb) hbα))
  have hbstrict : IsStrictRootUpperBound p b := by
    intro r hr
    exact lt_of_le_of_lt (hroots r hr) hb
  have hpot : rootBarrierPotential p b ≤ φ := by
    exact rootBarrierPotential_le_of_mean_zero_second_moment
      hp hdeg hb hα.le hroots hmean hsq
  have hiter := iterate_derivative_rootUpperBound_of_initial_barrier
    hp hφ hbstrict hpot d hd
  have hphi_formula : b - (d : ℝ) / φ = rootShrinkMomentObjective b c α := by
    dsimp [φ, rootShrinkMomentObjective]
    rw [hdc]
    have hn0 : (p.natDegree : ℝ) ≠ 0 := hn.ne'
    have hb1 : b - 1 ≠ 0 := (sub_pos.mpr hb).ne'
    have hbα0 : b + α ≠ 0 := hbα.ne'
    have hbnum0 : b + α - 1 ≠ 0 := hbnum.ne'
    field_simp [hn0, hb1, hbα0, hbnum0]
  rw [hphi_formula] at hiter
  have hopt := rootShrinkMomentObjective_at_optimum hc hc1 hα
  dsimp only at hopt
  change rootShrinkMomentObjective b c α =
      c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α) at hopt
  rwa [hopt] at hiter

end CommutatorTheorem
