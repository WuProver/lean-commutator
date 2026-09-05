import NoEpsilon.MSSBarrier
import NoEpsilon.MSSPick
import Mathlib.Analysis.Polynomial.Basic

/-!
# Real specialization of stable multivariate polynomials

The nonvanishing proof uses the sign of the logarithmic derivative and its
explicit Laurent residue, rather than taking Hurwitz closure as a hypothesis.
-/

namespace NoEpsilon.MSSSpecialization

open Polynomial NoEpsilon.MSSStability NoEpsilon.MSSBarrier NoEpsilon.MSSPick

variable {σ : Type*} [DecidableEq σ]

noncomputable def coordinatePolynomial {R : Type*} [CommRing R]
    (p : MvPolynomial σ R) (z : σ → R) (j : σ) : R[X] :=
  MvPolynomial.eval₂ Polynomial.C
    (fun k ↦ Polynomial.C (z k) + if k = j then Polynomial.X else 0) p

@[simp] theorem eval_coordinatePolynomial {R : Type*} [CommRing R]
    (p : MvPolynomial σ R) (z : σ → R) (j : σ) (t : R) :
    (coordinatePolynomial p z j).eval t =
      MvPolynomial.eval (coordinateShift z j t) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [coordinatePolynomial]
  | add p q hp hq => simpa [coordinatePolynomial] using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
    simp only [coordinatePolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X] at *
    rw [hp]
    congr 1
    by_cases hk : k = j <;> simp [coordinateShift, hk]

@[simp] theorem map_coordinatePolynomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : MvPolynomial σ R) (z : σ → R) (j : σ) :
    (coordinatePolynomial p z j).map f =
      coordinatePolynomial (p.map f) (fun k ↦ f (z k)) j := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [coordinatePolynomial]
  | add p q hp hq => simpa [coordinatePolynomial] using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
    simp only [coordinatePolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      Polynomial.map_mul, map_mul, MvPolynomial.map_X] at *
    rw [hp]
    congr 1
    by_cases hk : k = j <;> simp [hk]

/-- Substitution into one coordinate commutes with the corresponding formal
derivative, over any commutative coefficient ring. -/
theorem derivative_coordinatePolynomial {R : Type*} [CommRing R]
    (p : MvPolynomial σ R) (z : σ → R) (j : σ) :
    (coordinatePolynomial p z j).derivative =
      coordinatePolynomial (MvPolynomial.pderiv j p) z j := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [coordinatePolynomial]
  | add p q hp hq => simpa [coordinatePolynomial] using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
    by_cases hk : k = j
    · subst k
      simp only [coordinatePolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
        if_true, derivative_mul, derivative_add, derivative_C, derivative_X,
        zero_add, mul_one] at *
      rw [hp]
      simp [mul_comm, add_comm]
    · simp only [coordinatePolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
        if_neg hk, add_zero, derivative_mul, derivative_C, mul_zero, add_zero] at *
      rw [hp]
      simp [hk, mul_comm]

variable [Fintype σ]

/-- The derivative of a coordinate polynomial is evaluation of the multivariate
partial at the same (possibly complex) coordinate point. -/
theorem derivative_eval_coordinatePolynomial (p : MvPolynomial σ ℂ)
    (z : σ → ℂ) (j : σ) (t : ℂ) :
    (coordinatePolynomial p z j).derivative.eval t =
      MvPolynomial.eval (coordinateShift z j t) (MvPolynomial.pderiv j p) := by
  have hh := hasDerivAt_coordinateEval_zero p (coordinateShift z j t) j
  have hin : HasDerivAt (fun s : ℂ ↦ s - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have hh' := hh.comp_of_eq t hin (by simp)
  simp only [Function.comp_def, coordinateShift_twice, mul_one] at hh'
  have heq : ∀ s : ℂ, t + (s-t) = s := fun s ↦ by ring
  simp only [heq] at hh'
  have hd := (coordinatePolynomial p z j).hasDerivAt t
  simp only [eval_coordinatePolynomial] at hd
  exact hd.unique hh'

/-- Fixing every coordinate except one at real values preserves nonvanishing
in that variable, as long as the specialization is nonzero. -/
theorem coordinatePolynomial_upperStable {p : MvPolynomial σ ℂ} (hp : UpperStable p)
    (z : σ → ℝ) (j : σ)
    (hne : coordinatePolynomial p (fun k ↦ (z k : ℂ)) j ≠ 0) :
    ∀ t : ℂ, 0 < t.im → (coordinatePolynomial p (fun k ↦ (z k : ℂ)) j).eval t ≠ 0 := by
  apply upperStable_of_logDerivative_sign _ hne
  intro t ht hzero
  rw [derivative_eval_coordinatePolynomial, eval_coordinatePolynomial]
  apply logDerivative_im_nonpos_closed hp _ _ (by simpa using hzero) j
  intro k
  by_cases hk : k = j <;> simp [coordinateShift, hk, ht.le]

/-- Real polynomials whose complexifications are upper stable split over `ℝ`.
The proof is adapted from the source repository's `BTRealStabilityClosure`. -/
theorem splits_of_complexification_upperStable {p : ℝ[X]}
    (hp : ∀ z : ℂ, 0 < z.im → (p.map Complex.ofRealHom).eval z ≠ 0) : p.Splits := by
  have hp0 : p ≠ 0 := by
    intro hzero
    subst p
    exact hp Complex.I (by simp) (by simp)
  have hmap0 : p.map Complex.ofRealHom ≠ 0 :=
    fun h ↦ hp0 ((Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp h)
  apply Polynomial.Splits.of_splits_map_of_injective
    (i := Complex.ofRealHom) Complex.ofReal_injective (IsAlgClosed.splits _)
  intro z hz
  have hzroot : (p.map Complex.ofRealHom).IsRoot z := (Polynomial.mem_roots hmap0).mp hz
  have hmapEq : p.map Complex.ofRealHom = p.map (algebraMap ℝ ℂ) := by congr 1
  have hzeval : Polynomial.aeval z p = 0 := by
    rw [← Polynomial.eval_map_algebraMap, ← hmapEq]
    exact hzroot
  have hnotPos : ¬ 0 < z.im := fun hzpos ↦ hp z hzpos hzroot
  have hnotNeg : ¬ z.im < 0 := by
    intro hzneg
    have hconjPos : 0 < (starRingEnd ℂ z).im := by simp; linarith
    apply hp (starRingEnd ℂ z) hconjPos
    rw [hmapEq, Polynomial.eval_map_algebraMap, Polynomial.aeval_conj, hzeval]
    simp
  have hzim : z.im = 0 := by linarith
  refine ⟨z.re, ?_⟩
  apply Complex.ext
  · simp
  · simpa using hzim.symm

/-- A nonzero real coordinate specialization of a real stable multivariate
polynomial has only real roots. -/
theorem coordinatePolynomial_splits {p : MvPolynomial σ ℝ} (hp : RealStable p)
    (z : σ → ℝ) (j : σ) (hne : coordinatePolynomial p z j ≠ 0) :
    (coordinatePolynomial p z j).Splits := by
  apply splits_of_complexification_upperStable
  rw [map_coordinatePolynomial]
  apply coordinatePolynomial_upperStable hp z j
  have hm : (coordinatePolynomial p z j).map Complex.ofRealHom ≠ 0 :=
    fun h ↦ hne ((Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp h)
  simpa only [map_coordinatePolynomial] using hm

omit [Fintype σ] in
/-- Every root of an above-roots coordinate restriction is strictly negative. -/
theorem coordinatePolynomial_roots_neg {p : MvPolynomial σ ℝ} {z : σ → ℝ}
    (hz : AboveRoots p z) (j : σ) {r : ℝ}
    (hr : r ∈ (coordinatePolynomial p z j).roots) : r < 0 := by
  have hne : coordinatePolynomial p z j ≠ 0 := by
    intro h
    have he := hz.eval_pos
    rw [← coordinateShift_zero z j, ← eval_coordinatePolynomial, h] at he
    simp at he
  by_contra hnot
  have hr0 : 0 ≤ r := le_of_not_gt hnot
  have heval := (mem_roots hne).mp hr
  have hpos := hz _ (le_coordinateShift z j hr0)
  rw [← eval_coordinatePolynomial] at hpos
  exact hpos.ne' heval

/-- Above all roots, every coordinate barrier is nonnegative. -/
theorem barrier_nonneg {p : MvPolynomial σ ℝ} (hp : RealStable p)
    {z : σ → ℝ} (hz : AboveRoots p z) (i : σ) : 0 ≤ barrier p i z := by
  let h := coordinatePolynomial p z i
  have heval : 0 < h.eval 0 := by simpa [h] using hz.eval_pos
  have hne : h ≠ 0 := fun hh ↦ heval.ne' (by rw [hh]; simp)
  have hsplit := coordinatePolynomial_splits hp z i hne
  have hb : barrier p i z = h.derivative.eval 0 / h.eval 0 := by
    simp [h, derivative_coordinatePolynomial, barrier]
  rw [hb, hsplit.eval_derivative_div_eval_of_ne_zero heval.ne']
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
  exact (one_div_pos.mpr (sub_pos.mpr (coordinatePolynomial_roots_neg hz i hr))).le

/-- A polynomial quotient bounded on the positive ray cannot have numerator
degree larger than denominator degree. -/
theorem natDegree_le_of_bounded_quotient (g h : ℝ[X]) (hzero : h ≠ 0) (C : ℝ)
    (hbound : ∀ x : ℝ, 0 ≤ x → |g.eval x / h.eval x| ≤ C) :
    g.natDegree ≤ h.natDegree := by
  by_contra hnot
  have hdeg := Polynomial.degree_lt_degree (Nat.lt_of_not_ge hnot)
  have ht := g.abs_div_tendsto_atTop_atTop_of_degree_gt h hdeg hzero
  have he : ∀ᶠ x : ℝ in Filter.atTop, C < |g.eval x / h.eval x| :=
    ht.eventually (Filter.eventually_gt_atTop C)
  obtain ⟨x, hx, hx0⟩ := (he.and (Filter.eventually_ge_atTop (0 : ℝ))).exists
  exact (not_lt_of_ge (hbound x hx0)) hx

/-- The cross-direction barrier has a bounded rational numerator degree. -/
theorem barrier_quotient_natDegree_le {p : MvPolynomial σ ℝ} (hp : RealStable p)
    {z : σ → ℝ} (hz : AboveRoots p z) (i j : σ) :
    (coordinatePolynomial (MvPolynomial.pderiv i p) z j).natDegree ≤
      (coordinatePolynomial p z j).natDegree := by
  have hne : coordinatePolynomial p z j ≠ 0 := by
    intro hh
    have heval : 0 < (coordinatePolynomial p z j).eval 0 := by simpa using hz.eval_pos
    rw [hh] at heval
    simp at heval
  apply natDegree_le_of_bounded_quotient _ _ hne (barrier p i z)
  intro t ht
  have hz' := hz.mono (le_coordinateShift z j ht)
  rw [eval_coordinatePolynomial, eval_coordinatePolynomial]
  change |barrier p i (coordinateShift z j t)| ≤ barrier p i z
  rw [abs_of_nonneg (barrier_nonneg hp hz' i)]
  exact barrier_antitone_aboveRoots hp hz (le_coordinateShift z j ht) i

/-- The cross-coordinate rational barrier retains the Pick sign on the closed
upper half-plane wherever its denominator is nonzero. -/
theorem coordinate_quotient_pick {p : MvPolynomial σ ℝ} (hp : RealStable p)
    (z : σ → ℝ) (i j : σ) (t : ℂ) (ht : 0 ≤ t.im)
    (hzero : ((coordinatePolynomial p z j).map Complex.ofRealHom).eval t ≠ 0) :
    (((coordinatePolynomial (MvPolynomial.pderiv i p) z j).map Complex.ofRealHom).eval t /
      ((coordinatePolynomial p z j).map Complex.ofRealHom).eval t).im ≤ 0 := by
  simp only [map_coordinatePolynomial, eval_coordinatePolynomial] at hzero ⊢
  rw [← MvPolynomial.pderiv_map]
  apply logDerivative_im_nonpos_closed hp _ _ hzero i
  intro k
  by_cases hk : k = j <;> simp [coordinateShift, hk, ht]

end NoEpsilon.MSSSpecialization
