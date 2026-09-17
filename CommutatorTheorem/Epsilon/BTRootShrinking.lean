import CommutatorTheorem.Epsilon.BTInterlacing
import CommutatorTheorem.Epsilon.BTRootShrinkArithmetic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Barrier potentials for root shrinking

This file isolates the one-variable barrier argument used in the
Ravichandran--Srivastava root-shrinking theorem.  Roots are counted with
multiplicity throughout.
-/

namespace CommutatorTheorem

open scoped Polynomial BigOperators
open Polynomial Finset

/-- The upper barrier potential of a polynomial, written as its logarithmic derivative. -/
noncomputable def rootBarrierPotential (p : ℝ[X]) (b : ℝ) : ℝ :=
  p.derivative.eval b / p.eval b

/-- The sum-of-squares curvature term attached to the roots of `p`. -/
noncomputable def rootBarrierCurvature (p : ℝ[X]) (b : ℝ) : ℝ :=
  (p.roots.map fun r ↦ (1 / (b - r)) ^ 2).sum

/-- For a split polynomial away from its roots, the logarithmic derivative is the sum of the
reciprocal root gaps. -/
lemma rootBarrierPotential_eq_sum_roots {p : ℝ[X]} (hp : RealRooted p) {b : ℝ}
    (hb : p.eval b ≠ 0) :
    rootBarrierPotential p b = (p.roots.map fun r ↦ 1 / (b - r)).sum := by
  exact hp.eval_derivative_div_eval_of_ne_zero hb

/-- The derivative of a finite reciprocal-gap sum is minus its sum of squared reciprocal gaps. -/
lemma hasDerivAt_sum_reciprocal_gaps (s : Multiset ℝ) (b : ℝ)
    (hb : ∀ r ∈ s, b ≠ r) :
    HasDerivAt (fun x ↦ (s.map fun r ↦ 1 / (x - r)).sum)
      (-(s.map fun r ↦ (1 / (b - r)) ^ 2).sum) b := by
  induction s using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const b (0 : ℝ)
  | @cons r s ih =>
      have hbr : b - r ≠ 0 := sub_ne_zero.mpr (hb r (by simp))
      have hbs : ∀ z ∈ s, b ≠ z := by
        intro z hz
        exact hb z (by simp [hz])
      have hterm : HasDerivAt (fun x : ℝ ↦ 1 / (x - r)) (-(1 / (b - r)) ^ 2) b := by
        convert ((hasDerivAt_id b).sub_const r).inv hbr using 1
        · ext x
          simp only [one_div, Pi.inv_apply, id_eq]
        · simp only [id_eq]
          field_simp
      convert hterm.add (ih hbs) using 1
      · ext x
        simp only [Multiset.map_cons, Multiset.sum_cons, one_div, Pi.add_apply]
      · simp only [Multiset.map_cons, Multiset.sum_cons, one_div, pow_two]
        ring

/-- The analytic derivative of the logarithmic derivative is minus the root curvature. -/
lemma hasDerivAt_rootBarrierPotential {p : ℝ[X]} (hp : RealRooted p) {b : ℝ}
    (hb : p.eval b ≠ 0) :
    HasDerivAt (rootBarrierPotential p) (-rootBarrierCurvature p b) b := by
  have hevent : Filter.Eventually (fun x ↦ p.eval x ≠ 0) (nhds b) :=
    (p.continuousAt.eventually_ne hb)
  have hfun : Filter.EventuallyEq (nhds b) (rootBarrierPotential p)
      (fun x ↦ (p.roots.map fun r ↦ 1 / (x - r)).sum) := by
    filter_upwards [hevent] with x hx
    exact hp.eval_derivative_div_eval_of_ne_zero hx
  have hroot : HasDerivAt
      (fun x ↦ (p.roots.map fun r ↦ 1 / (x - r)).sum)
      (-rootBarrierCurvature p b) b := by
    apply hasDerivAt_sum_reciprocal_gaps
    have hp0 : p ≠ 0 := by
      intro hpzero
      simp [hpzero] at hb
    intro r hr hbr
    apply hb
    rw [hbr]
    exact (mem_roots hp0).mp hr
  exact hroot.congr_of_eventuallyEq hfun

/-- A convenient pointwise curvature identity. -/
lemma rootBarrier_curvature_identity {p : ℝ[X]} (hp : RealRooted p) {b : ℝ}
    (hb : p.eval b ≠ 0) :
    p.derivative.derivative.eval b * p.eval b - p.derivative.eval b ^ 2 =
      -rootBarrierCurvature p b * p.eval b ^ 2 := by
  have hquot := ((p.derivative.hasDerivAt b).div (p.hasDerivAt b) hb)
  have hbarrier := hasDerivAt_rootBarrierPotential hp hb
  have huniq := hquot.unique hbarrier
  field_simp [hb] at huniq
  nlinarith

/-! ## The finite-dimensional algebra in one barrier step -/

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
/-- A weighted rearrangement inequality in exactly the form needed by the barrier step. -/
lemma weighted_rearrangement_barrier
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a t : ι → ℝ)
    (hpair : ∀ i j, 0 ≤ (t i - t j) * (a j * t i - a i * t j)) :
    (∑ i, t i) * (∑ i, a i * t i) ≤
      (∑ i, a i) * (∑ i, t i ^ 2) := by
  have hsum : 0 ≤ ∑ i, ∑ j, (t i - t j) * (a j * t i - a i * t j) := by
    exact sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ hpair i j
  have h₁ : (∑ i, ∑ j, t i * (a j * t i)) =
      (∑ i, a i) * (∑ i, t i ^ 2) := by
    calc
      _ = ∑ i, ∑ j, a j * t i ^ 2 := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        ring
      _ = ∑ i, (∑ j, a j) * t i ^ 2 := by simp only [Finset.sum_mul]
      _ = _ := by rw [Finset.mul_sum]
  have h₂ : (∑ i, ∑ j, t j * (a j * t i)) =
      (∑ i, t i) * (∑ i, a i * t i) := by
    calc
      _ = ∑ i, ∑ j, (a j * t j) * t i := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        ring
      _ = ∑ i, (∑ j, a j * t j) * t i := by simp only [Finset.sum_mul]
      _ = _ := by rw [← Finset.mul_sum]; ring
  have h₃ : (∑ i, ∑ j, t i * (a i * t j)) =
      (∑ i, t i) * (∑ i, a i * t i) := by
    calc
      _ = ∑ i, (a i * t i) * (∑ j, t j) := by
        apply sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [← Finset.sum_mul]; ring
  have h₄ : (∑ i, ∑ j, t j * (a i * t j)) =
      (∑ i, a i) * (∑ i, t i ^ 2) := by
    calc
      _ = ∑ i, a i * (∑ j, t j ^ 2) := by
        apply sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [Finset.sum_mul]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, h₁, h₂, h₃, h₄] at hsum
  nlinarith [hsum]

/-- The reciprocal-gap transform is ordered strongly enough for the weighted rearrangement
inequality. -/
lemma reciprocal_gap_pair_nonneg {A ai aj : ℝ}
    (hA : 0 < A) (hai : 0 < ai) (haj : 0 < aj)
    (haiA : ai < A) (hajA : aj < A) :
    let ti := ai * A / (A - ai)
    let tj := aj * A / (A - aj)
    0 ≤ (ti - tj) * (aj * ti - ai * tj) := by
  dsimp
  have hi : 0 < A - ai := sub_pos.mpr haiA
  have hj : 0 < A - aj := sub_pos.mpr hajA
  have hfirst :
      ai * A / (A - ai) - aj * A / (A - aj) =
        A ^ 2 * (ai - aj) / ((A - ai) * (A - aj)) := by
    field_simp
    ring
  have hsecond :
      aj * (ai * A / (A - ai)) - ai * (aj * A / (A - aj)) =
        ai * aj * A * (ai - aj) / ((A - ai) * (A - aj)) := by
    field_simp
    ring
  rw [hfirst, hsecond]
  rw [div_mul_div_comm]
  apply div_nonneg
  · have :
        A ^ 2 * (ai - aj) * (ai * aj * A * (ai - aj)) =
          ai * aj * A ^ 3 * (ai - aj) ^ 2 := by ring
    rw [this]
    positivity
  · positivity

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
/-- The scalar heart of one barrier step.  If `a i` are the reciprocal gaps at the old
barrier and `A` is their sum, then `t i` are the reciprocal gaps one step to the left. -/
lemma reciprocal_gap_barrier_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hA : 0 < ∑ i, a i)
    (hproper : ∀ i, a i < ∑ j, a j) :
    let A := ∑ i, a i
    let t := fun i ↦ a i * A / (A - a i)
    (∑ i, t i) - (∑ i, t i ^ 2) / (∑ i, t i) ≤ A := by
  dsimp only
  let A : ℝ := ∑ i, a i
  let t : ι → ℝ := fun i ↦ a i * A / (A - a i)
  have ht : ∀ i, 0 < t i := by
    intro i
    dsimp [t]
    exact div_pos (mul_pos (ha i) hA) (sub_pos.mpr (hproper i))
  have huniv : (Finset.univ : Finset ι).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hA
    simp at hA
  have hS : 0 < ∑ i, t i := Finset.sum_pos (fun i _ ↦ ht i) huniv
  have hpair : ∀ i j, 0 ≤ (t i - t j) * (a j * t i - a i * t j) := by
    intro i j
    exact reciprocal_gap_pair_nonneg hA (ha i) (ha j) (hproper i) (hproper j)
  have hrearrange := weighted_rearrangement_barrier a t hpair
  have hpoint : ∀ i, A * (t i - a i) = a i * t i := by
    intro i
    have hden : A - a i ≠ 0 := (sub_pos.mpr (hproper i)).ne'
    dsimp [t]
    field_simp
    ring
  have hsumIdentity : A * ((∑ i, t i) - (∑ i, a i)) = ∑ i, a i * t i := by
    calc
      _ = ∑ i, A * (t i - a i) := by
        rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
        simpa only [mul_sub] using
          (Finset.sum_sub_distrib (s := (Finset.univ : Finset ι))
            (f := fun i ↦ A * t i) (g := fun i ↦ A * a i)).symm
      _ = _ := sum_congr rfl fun i _ ↦ hpoint i
  have htarget : ((∑ i, t i) - A) * (∑ i, t i) ≤ ∑ i, t i ^ 2 := by
    dsimp [A] at hsumIdentity ⊢
    nlinarith [hrearrange]
  have hcancel : ((∑ i, t i ^ 2) / (∑ i, t i)) * (∑ i, t i) =
      ∑ i, t i ^ 2 := div_mul_cancel₀ _ hS.ne'
  dsimp [A] at htarget ⊢
  nlinarith

/-! ## Moving between root multisets and finite sums -/

/-- A list sum can be written as a sum over its position type. -/
lemma list_sum_eq_fin_sum {l : List ℝ} : l.sum = ∑ i : Fin l.length, l.get i := by
  simpa only [List.ofFn_get] using (List.sum_ofFn (f := l.get))

/-- Sorting a multiset exposes its multiplicities as an honest finite index type without changing
any mapped sum. -/
lemma multiset_map_sum_eq_fin_sum_sort (s : Multiset ℝ) (f : ℝ → ℝ) :
    (s.map f).sum = ∑ i : Fin (s.sort (· ≤ ·)).length, f ((s.sort (· ≤ ·)).get i) := by
  let l := s.sort (· ≤ ·)
  have hcoe : (↑l : Multiset ℝ) = s := by simp [l]
  calc
    (s.map f).sum = ((↑l : Multiset ℝ).map f).sum := by rw [hcoe]
    _ = (l.map f).sum := by rfl
    _ = ∑ i : Fin l.length, f (l.get i) := by
      simp [list_sum_eq_fin_sum]

/-! ## A reusable conditional iteration harness -/

/-- The one-step barrier property needed by the iteration.  It is a plain proposition: clients
may prove it from the concrete root geometry available in their application. -/
def DerivativeBarrierStep (p : ℝ[X]) (b φ : ℝ) : Prop :=
  0 < φ ∧
    IsStrictRootUpperBound p b ∧
    IsStrictRootUpperBound p.derivative (b - 1 / φ) ∧
    rootBarrierPotential p.derivative (b - 1 / φ) ≤ φ

/-- Iterating a supplied one-step barrier certificate gives the linear barrier displacement used
in root shrinking.  The conclusion is an upper bound for every root of the iterated derivative. -/
theorem iterate_derivative_rootUpperBound_of_barrier_steps
    {p : ℝ[X]} {b φ : ℝ} (hφ : 0 < φ) (hbase : IsRootUpperBound p b) (d : ℕ)
    (hsteps : ∀ j < d,
      DerivativeBarrierStep (Polynomial.derivative^[j] p) (b - (j : ℝ) / φ) φ) :
    IsRootUpperBound (Polynomial.derivative^[d] p) (b - (d : ℝ) / φ) := by
  by_cases hd : d = 0
  · subst d
    simpa using hbase
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    have hj := hsteps j (Nat.lt_succ_self j)
    have hderivative :
        Polynomial.derivative^[j + 1] p =
          (Polynomial.derivative^[j] p).derivative := by
      rw [Function.iterate_succ_apply']
    rw [hderivative]
    have hbound : b - ((j + 1 : ℕ) : ℝ) / φ = b - (j : ℝ) / φ - 1 / φ := by
      push_cast
      field_simp [hφ.ne']
      ring
    rw [hbound]
    intro r hr
    exact (hj.2.2.1 r hr).le

end CommutatorTheorem
