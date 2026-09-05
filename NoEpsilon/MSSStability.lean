import NoEpsilon.MixedCharacteristic
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Stability under the MSS operator `1 - ∂`

The affine-line restriction algebra below is ported from the original
`CommutatorTheorem.Epsilon.BTStableLine` source. The target is the MSS difference
operator, not an assumed common interlacer or outcome-selection statement.
-/

namespace NoEpsilon
namespace MSSStability

open Polynomial
open scoped BigOperators

def InUpperHalfPlane (z : ℂ) : Prop := 0 < z.im

def UpperStable {σ : Type*} (p : MvPolynomial σ ℂ) : Prop :=
  ∀ z : σ → ℂ, (∀ i, InUpperHalfPlane (z i)) → MvPolynomial.eval z p ≠ 0

noncomputable def nonnegativeDirectionalDerivative {σ : Type*} [Fintype σ]
    (w : σ → ℝ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ i, MvPolynomial.C (w i : ℂ) * MvPolynomial.pderiv i p

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


/-- A logarithmic derivative on a strict lower-root line cannot equal the positive real
number one. This strengthens the nonpositive-imaginary-part estimate by treating the
constant polynomial separately and using a strict sign for every root otherwise. -/
theorem stableLine_logDerivative_ne_one {σ : Type*}
    {p : MvPolynomial σ ℂ} (hp : UpperStable p)
    (z : σ → ℂ) (w : σ → ℝ)
    (hz : ∀ i, InUpperHalfPlane (z i)) (hw : ∀ i, 0 ≤ w i) :
    (stableLinePolynomial z w p).derivative.eval 0 /
      (stableLinePolynomial z w p).eval 0 ≠ 1 := by
  let f := stableLinePolynomial z w p
  have hf0 : f.eval 0 ≠ 0 := by
    rw [eval_stableLinePolynomial]
    simpa using hp z hz
  have hfne : f ≠ 0 := fun h ↦ hf0 (by rw [h]; simp)
  by_cases hdeg : f.natDegree = 0
  · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdeg
    change f.derivative.eval 0 / f.eval 0 ≠ 1
    rw [← hc]
    simp
  · have hroot : f.roots ≠ 0 := (IsAlgClosed.splits f).roots_ne_zero hdeg
    have hneg : ∀ a ∈ f.roots, (1 / (0 - a)).im < 0 := by
      intro a ha
      exact one_div_neg_im_neg
        (root_im_neg_of_stableLinePolynomial hp z w hz hw ((mem_roots hfne).mp ha))
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hroot
    have hsum : (f.roots.map (fun a ↦ (1 / (0 - a)).im)).sum < 0 := by
      simpa using (Multiset.sum_lt_sum
        (s := f.roots) (f := fun a ↦ (1 / (0 - a)).im) (g := fun _ ↦ (0 : ℝ))
        (fun a ha ↦ (hneg a ha).le) ⟨a, ha, hneg a ha⟩)
    have him : (f.derivative.eval 0 / f.eval 0).im < 0 := by
      rw [(IsAlgClosed.splits f).eval_derivative_div_eval_of_ne_zero hf0,
        im_multiset_sum, Multiset.map_map]
      exact hsum
    intro h
    change f.derivative.eval 0 / f.eval 0 = 1 at h
    rw [h] at him
    simp at him

/-- The MSS difference operator preserves upper-half-plane stability in any
nonnegative real direction. This is a proved stability theorem, with no outcome
selection or common-interlacing hypothesis. -/
theorem UpperStable.sub_nonnegativeDirectionalDerivative
    {σ : Type*} [Fintype σ] {p : MvPolynomial σ ℂ} (hp : UpperStable p)
    (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) :
    UpperStable (p - nonnegativeDirectionalDerivative w p) := by
  intro z hz hzero
  have heq : MvPolynomial.eval z p =
      MvPolynomial.eval z (nonnegativeDirectionalDerivative w p) := by
    apply sub_eq_zero.mp
    simpa only [map_sub] using hzero
  apply stableLine_logDerivative_ne_one hp z w hz hw
  rw [derivative_stableLinePolynomial_eval_zero, eval_stableLinePolynomial]
  simp only [mul_zero, add_zero]
  rw [← heq, div_self (hp z hz)]

/-- In particular, each coordinate operator `1 - ∂ₓ` preserves stability. -/
theorem UpperStable.sub_pderiv {σ : Type*} [Finite σ]
    {p : MvPolynomial σ ℂ} (hp : UpperStable p) (x : σ) :
    UpperStable (p - MvPolynomial.pderiv x p) := by
  classical
  letI := Fintype.ofFinite σ
  let w : σ → ℝ := fun i ↦ if i = x then 1 else 0
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    dsimp [w]
    split_ifs <;> norm_num
  have heq : nonnegativeDirectionalDerivative w p = MvPolynomial.pderiv x p := by
    unfold nonnegativeDirectionalDerivative
    rw [Finset.sum_eq_single x]
    · simp [w]
    · intro i _ hi
      simp [w, hi]
    · simp
  simpa only [heq] using hp.sub_nonnegativeDirectionalDerivative w hw

/-- A finite composition of the MSS coordinate operators remains stable. -/
theorem UpperStable.fold_sub_pderiv {σ : Type*} [Finite σ]
    {p : MvPolynomial σ ℂ} (hp : UpperStable p) (xs : List σ) :
    UpperStable (xs.foldl (fun q x ↦ q - MvPolynomial.pderiv x q) p) := by
  induction xs generalizing p with
  | nil => exact hp
  | cons x xs ih => exact ih (hp.sub_pderiv x)

section DeterminantPencil

open scoped ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- A positive semidefinite matrix pencil with positive definite total coefficient is
nonsingular whenever all its coefficients have positive imaginary part. -/
theorem det_psd_pencil_ne_zero (A : κ → Matrix ι ι ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hTotal : (∑ i, A i).PosDef)
    (z : κ → ℂ) (hz : ∀ i, 0 < (z i).im) :
    (∑ i, z i • A i).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let q : κ → ℂ := fun i ↦ star v ⬝ᵥ ((A i).mulVec v)
  have hq : ∀ i, 0 ≤ (q i).re :=
    fun i ↦ (Complex.nonneg_iff.mp ((hA i).dotProduct_mulVec_nonneg v)).1
  have hqi : ∀ i, (q i).im = 0 :=
    fun i ↦ (Complex.nonneg_iff.mp ((hA i).dotProduct_mulVec_nonneg v)).2.symm
  have hsum : 0 < ∑ i, (q i).re := by
    have ht := (Complex.pos_iff.mp (hTotal.dotProduct_mulVec_pos hv)).1
    simpa only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum] using ht
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hq i)).mp hsum
  have hpos : 0 < ∑ i, (z i).im * (q i).re := by
    apply Finset.sum_pos'
    · exact fun i _ ↦ mul_nonneg (hz i).le (hq i)
    · exact ⟨i, Finset.mem_univ i, mul_pos (hz i) hi⟩
  have him : (star v ⬝ᵥ ((∑ i, z i • A i).mulVec v)).im =
      ∑ i, (z i).im * (q i).re := by
    simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, Complex.im_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (z i * q i).im = _
    rw [Complex.mul_im, hqi, mul_zero, zero_add]
  rw [hker, dotProduct_zero] at him
  simp only [Complex.zero_im] at him
  linarith

/-- The determinant polynomial of a positive semidefinite matrix family. -/
noncomputable def psdPencil (A : κ → Matrix ι ι ℂ) : MvPolynomial κ ℂ :=
  (∑ i, (MvPolynomial.X i : MvPolynomial κ ℂ) • (A i).map MvPolynomial.C).det

theorem eval_psdPencil (A : κ → Matrix ι ι ℂ) (z : κ → ℂ) :
    MvPolynomial.eval z (psdPencil A) = (∑ i, z i • A i).det := by
  unfold psdPencil
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply]

/-- The stable initial determinant pencil required by MSS. -/
theorem psdPencil_upperStable (A : κ → Matrix ι ι ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hTotal : (∑ i, A i).PosDef) :
    UpperStable (psdPencil A) := by
  intro z hz
  rw [eval_psdPencil]
  exact det_psd_pencil_ne_zero A hA hTotal z hz

/-- Stability after applying any finite list of MSS coordinate operators to the PSD pencil. -/
theorem psdPencil_fold_sub_pderiv_upperStable (A : κ → Matrix ι ι ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hTotal : (∑ i, A i).PosDef) (xs : List κ) :
    UpperStable (xs.foldl (fun p i ↦ p - MvPolynomial.pderiv i p) (psdPencil A)) :=
  (psdPencil_upperStable A hA hTotal).fold_sub_pderiv xs

/-- Exact coordinate derivative of the PSD determinant pencil. -/
theorem pderiv_psdPencil (A : κ → Matrix ι ι ℂ) (x : κ) :
    MvPolynomial.pderiv x (psdPencil A) =
      MixedCharacteristic.firstVariation
        (∑ i, (MvPolynomial.X i : MvPolynomial κ ℂ) • (A i).map MvPolynomial.C)
        ((A x).map MvPolynomial.C) := by
  classical
  unfold psdPencil
  rw [MixedCharacteristic.pderiv_det_eq_firstVariation]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
    mul_zero, add_zero]
  rw [Finset.sum_eq_single x]
  · simp
  · intro k _ hk
    simp [MvPolynomial.pderiv_X, hk]
  · simp

/-- Evaluated coordinate derivative, valid at every point, as a matrix first variation. -/
theorem eval_pderiv_psdPencil (A : κ → Matrix ι ι ℂ) (z : κ → ℂ) (x : κ) :
    MvPolynomial.eval z (MvPolynomial.pderiv x (psdPencil A)) =
      MixedCharacteristic.firstVariation (∑ i, z i • A i) (A x) := by
  rw [pderiv_psdPencil, MixedCharacteristic.map_firstVariation]
  have hM : (∑ i, (MvPolynomial.X i : MvPolynomial κ ℂ) •
      (A i).map MvPolynomial.C).map (MvPolynomial.eval z) = ∑ i, z i • A i := by
    ext i j
    simp [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply]
  have hB : ((A x).map MvPolynomial.C).map (MvPolynomial.eval z) = A x := by
    ext i j
    simp
  rw [hM, hB]

/-- At the scalar starting point and for total covariance identity, the MSS barrier
coordinate is exactly the trace of its covariance divided by the starting scalar. -/
theorem psdPencil_initial_logDerivative [Nonempty ι]
    (A : κ → Matrix ι ι ℂ) (hTotal : ∑ i, A i = 1)
    (t : ℂ) (ht : t ≠ 0) (x : κ) :
    MvPolynomial.eval (fun _ : κ ↦ t) (MvPolynomial.pderiv x (psdPencil A)) /
      MvPolynomial.eval (fun _ : κ ↦ t) (psdPencil A) = Matrix.trace (A x) / t := by
  rw [eval_pderiv_psdPencil, eval_psdPencil, ← Finset.smul_sum, hTotal]
  exact MixedCharacteristic.firstVariation_scalar_ratio t ht (A x)

end DeterminantPencil

end MSSStability
end NoEpsilon
