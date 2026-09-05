import CommutatorTheorem.Epsilon.BTRealStabilityClosure

/-!
# Affine line restrictions of stable multivariate polynomials

This file records the elementary specialization used in the logarithmic-
derivative proof that nonnegative directional derivatives preserve upper
half-plane stability.  The analytic open-mapping step is deliberately kept
out of this small algebraic module.
-/

namespace CommutatorTheorem.BTStableLine

open Polynomial
open CommutatorTheorem.BTRealStabilityClosure

/-- Restrict a multivariate polynomial to the affine complex line
`t ↦ z + t w`. -/
noncomputable def stableLinePolynomial {sigma : Type*}
    (z : sigma → ℂ) (w : sigma → ℝ) (p : MvPolynomial sigma ℂ) : ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i ↦ Polynomial.C (z i) + Polynomial.C (w i : ℂ) * Polynomial.X) p

/-- Evaluation of the affine-line restriction is literal substitution along
that line. -/
theorem eval_stableLinePolynomial {sigma : Type*}
    (z : sigma → ℂ) (w : sigma → ℝ) (p : MvPolynomial sigma ℂ)
    (t : ℂ) :
    (stableLinePolynomial z w p).eval t =
      MvPolynomial.eval (fun i ↦ z i + (w i : ℂ) * t) p := by
  change Polynomial.evalRingHom t
      (MvPolynomial.eval₂ Polynomial.C
        (fun i ↦ Polynomial.C (z i) + Polynomial.C (w i : ℂ) * Polynomial.X) p) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
    ext a
    simp
  have hx :
      (⇑(Polynomial.evalRingHom t) ∘
          (fun i : sigma ↦
            Polynomial.C (z i) + Polynomial.C (w i : ℂ) * Polynomial.X)) =
        (fun i ↦ z i + (w i : ℂ) * t) := by
    funext i
    simp
  rw [hc, hx, MvPolynomial.eval₂_id]

/-- The derivative at the base point of the affine-line restriction is the
evaluation of the corresponding nonnegative directional derivative. -/
theorem derivative_stableLinePolynomial_eval_zero
    {sigma : Type*} [Fintype sigma]
    (z : sigma → ℂ) (w : sigma → ℝ) (p : MvPolynomial sigma ℂ) :
    (stableLinePolynomial z w p).derivative.eval 0 =
      MvPolynomial.eval z (nonnegativeDirectionalDerivative w p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [stableLinePolynomial, nonnegativeDirectionalDerivative]
  | add p q hp hq =>
      have hline : stableLinePolynomial z w (p + q) =
          stableLinePolynomial z w p + stableLinePolynomial z w q := by
        simp [stableLinePolynomial]
      have hdir : nonnegativeDirectionalDerivative w (p + q) =
          nonnegativeDirectionalDerivative w p +
            nonnegativeDirectionalDerivative w q := by
        simp [nonnegativeDirectionalDerivative, mul_add,
          Finset.sum_add_distrib]
      rw [hline, derivative_add, eval_add, hdir, map_add, hp, hq]
  | mul_X p i hp =>
      calc
        (stableLinePolynomial z w (p * MvPolynomial.X i)).derivative.eval 0 =
            (stableLinePolynomial z w p).derivative.eval 0 * z i +
              (stableLinePolynomial z w p).eval 0 * (w i : ℂ) := by
                simp [stableLinePolynomial, derivative_mul]
        _ = MvPolynomial.eval z (nonnegativeDirectionalDerivative w p) * z i +
              MvPolynomial.eval z p * (w i : ℂ) := by
                rw [hp, eval_stableLinePolynomial]
                simp
        _ = MvPolynomial.eval z
              (nonnegativeDirectionalDerivative w (p * MvPolynomial.X i)) := by
                simp only [nonnegativeDirectionalDerivative,
                  MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
                  map_sum, map_add, map_mul, MvPolynomial.eval_C,
                  MvPolynomial.eval_X]
                simp_rw [mul_add]
                rw [Finset.sum_add_distrib]
                have hfirst :
                    (∑ x : sigma, (w x : ℂ) *
                      (MvPolynomial.eval z (MvPolynomial.pderiv x p) * z i)) =
                      (∑ x : sigma, (w x : ℂ) *
                        MvPolynomial.eval z (MvPolynomial.pderiv x p)) * z i := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro x _
                  ring
                have hsecond :
                    (∑ x : sigma, (w x : ℂ) *
                      (MvPolynomial.eval z p *
                        MvPolynomial.eval z
                          (Pi.single
                            (M := fun _ : sigma ↦ MvPolynomial sigma ℂ)
                            x 1 i))) =
                      MvPolynomial.eval z p * (w i : ℂ) := by
                  rw [Finset.sum_eq_single i]
                  · simp
                    ring
                  · intro j _ hji
                    simp [hji]
                  · simp
                rw [hfirst, hsecond]

/-- Starting in the open upper half-plane and moving in a nonnegative real
direction stays there for every parameter in the closed upper half-plane. -/
theorem affineLine_inUpperHalfPlane {sigma : Type*}
    (z : sigma → ℂ) (w : sigma → ℝ)
    (hz : ∀ i, InUpperHalfPlane (z i)) (hw : ∀ i, 0 ≤ w i)
    {t : ℂ} (ht : 0 ≤ t.im) :
    ∀ i, InUpperHalfPlane (z i + (w i : ℂ) * t) := by
  intro i
  unfold InUpperHalfPlane at hz ⊢
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  exact add_pos_of_pos_of_nonneg (hz i) (mul_nonneg (hw i) ht)

/-- A nonzero stable polynomial restricts to a nonzero univariate
polynomial on every such line. -/
theorem stableLinePolynomial_ne_zero {sigma : Type*}
    {p : MvPolynomial sigma ℂ}
    (hp : ∀ z : sigma → ℂ, (∀ i, InUpperHalfPlane (z i)) →
      MvPolynomial.eval z p ≠ 0)
    (z : sigma → ℂ) (w : sigma → ℝ)
    (hz : ∀ i, InUpperHalfPlane (z i)) :
    stableLinePolynomial z w p ≠ 0 := by
  intro hzero
  have heval := congrArg (fun q : ℂ[X] ↦ q.eval 0) hzero
  change (stableLinePolynomial z w p).eval 0 = (0 : ℂ[X]).eval 0 at heval
  rw [eval_stableLinePolynomial] at heval
  simp only [mul_zero, add_zero, eval_zero] at heval
  exact hp z hz heval

/-- Every root of a stable affine-line restriction lies strictly in the
lower half-plane.  The strictness comes from the positive imaginary part of
the base point, so it also holds for real line parameters. -/
theorem root_im_neg_of_stableLinePolynomial {sigma : Type*}
    {p : MvPolynomial sigma ℂ}
    (hp : ∀ z : sigma → ℂ, (∀ i, InUpperHalfPlane (z i)) →
      MvPolynomial.eval z p ≠ 0)
    (z : sigma → ℂ) (w : sigma → ℝ)
    (hz : ∀ i, InUpperHalfPlane (z i)) (hw : ∀ i, 0 ≤ w i)
    {a : ℂ} (ha : (stableLinePolynomial z w p).IsRoot a) :
    a.im < 0 := by
  by_contra hnot
  have haim : 0 ≤ a.im := le_of_not_gt hnot
  have hline := affineLine_inUpperHalfPlane z w hz hw haim
  apply hp (fun i ↦ z i + (w i : ℂ) * a) hline
  rw [← eval_stableLinePolynomial]
  exact ha

/-- The reciprocal displacement from `0` to a strict lower-half-plane point
also has strictly negative imaginary part. -/
theorem one_div_neg_im_neg {a : ℂ} (ha : a.im < 0) :
    (1 / (0 - a)).im < 0 := by
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp at ha
  rw [show 0 - a = -a by simp, one_div, Complex.inv_im]
  have hnum : -(-a).im = a.im := by simp
  rw [hnum, Complex.normSq_neg]
  exact div_neg_of_neg_of_pos ha (Complex.normSq_pos.mpr ha0)

private theorem im_multiset_sum (s : Multiset ℂ) :
    s.sum.im = (s.map Complex.im).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp [ih, Complex.add_im]

/-- The logarithmic derivative of a stable affine-line restriction at the
real parameter `0` lies in the closed lower half-plane.  This is the sign
input for the open-mapping proof of directional-derivative stability. -/
theorem stableLine_logDerivative_im_nonpos {sigma : Type*}
    {p : MvPolynomial sigma ℂ}
    (hp : ∀ z : sigma → ℂ, (∀ i, InUpperHalfPlane (z i)) →
      MvPolynomial.eval z p ≠ 0)
    (z : sigma → ℂ) (w : sigma → ℝ)
    (hz : ∀ i, InUpperHalfPlane (z i)) (hw : ∀ i, 0 ≤ w i) :
    (((stableLinePolynomial z w p).derivative.eval 0) /
        ((stableLinePolynomial z w p).eval 0)).im ≤ 0 := by
  let f := stableLinePolynomial z w p
  have hf0 : f.eval 0 ≠ 0 := by
    rw [eval_stableLinePolynomial]
    simpa using hp z hz
  have hfne : f ≠ 0 := fun h ↦ hf0 (by rw [h]; simp)
  rw [(IsAlgClosed.splits f).eval_derivative_div_eval_of_ne_zero hf0]
  rw [im_multiset_sum]
  apply (Multiset.sum_le_card_nsmul _ 0 ?_).trans
  · simp
  intro y hy
  obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hy
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hu
  exact (one_div_neg_im_neg
    (root_im_neg_of_stableLinePolynomial hp z w hz hw
      ((Polynomial.mem_roots hfne).mp ha))).le

/-- Multivariate form of the preceding sign: at every point of the upper
half-plane product, the directional logarithmic derivative has nonpositive
imaginary part. -/
theorem directional_logDerivative_im_nonpos
    {sigma : Type*} [Fintype sigma]
    {p : MvPolynomial sigma ℂ}
    (hp : ∀ z : sigma → ℂ, (∀ i, InUpperHalfPlane (z i)) →
      MvPolynomial.eval z p ≠ 0)
    (z : sigma → ℂ) (w : sigma → ℝ)
    (hz : ∀ i, InUpperHalfPlane (z i)) (hw : ∀ i, 0 ≤ w i) :
    ((MvPolynomial.eval z (nonnegativeDirectionalDerivative w p)) /
        (MvPolynomial.eval z p)).im ≤ 0 := by
  simpa [derivative_stableLinePolynomial_eval_zero,
    eval_stableLinePolynomial] using
      stableLine_logDerivative_im_nonpos hp z w hz hw

end CommutatorTheorem.BTStableLine
