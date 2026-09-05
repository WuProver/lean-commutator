import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The determinantal base case for exact-MDP stability

For a Hermitian matrix `A`, the polynomial-valued determinant
`det (diag z - A)` cannot vanish when every coordinate of `z` lies in the
open upper half-plane.  This is the elementary definite-determinantal input
to the real-stability argument used for mixed determinantal polynomials.
-/

namespace CommutatorTheorem.BTDeterminantStability

open scoped BigOperators ComplexConjugate
open Matrix Finset MvPolynomial

/-- A complex multivariate polynomial is stable if it does not vanish when
every variable lies in the open upper half-plane. -/
def ComplexStable {ι : Type*} (p : MvPolynomial ι ℂ) : Prop :=
  ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) → MvPolynomial.eval z p ≠ 0

/-- The real-coefficient version of upper-half-plane stability. -/
def RealStable {ι : Type*} (p : MvPolynomial ι ℝ) : Prop :=
  ∀ z : ι → ℂ, (∀ i, 0 < (z i).im) →
    MvPolynomial.eval₂ (algebraMap ℝ ℂ) z p ≠ 0

/-- The multivariate determinant `det (diag X - A)`. -/
noncomputable def hermitianDetPoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : MvPolynomial ι ℂ :=
  (Matrix.diagonal (fun i => MvPolynomial.X i) -
    A.map MvPolynomial.C).det

theorem eval_hermitianDetPoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z : ι → ℂ) :
    MvPolynomial.eval z (hermitianDetPoly A) =
      (Matrix.diagonal z - A).det := by
  unfold hermitianDetPoly
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j
    simp [MvPolynomial.eval_X]
  · simp [h]

/-- The imaginary part of the diagonal quadratic form is the weighted sum of
the coordinate imaginary parts. -/
theorem im_star_dotProduct_diagonal_mulVec
    {n : Type*} [Fintype n] [DecidableEq n]
    (z v : n → ℂ) :
    (star v ⬝ᵥ (Matrix.diagonal z *ᵥ v)).im =
      ∑ i, Complex.normSq (v i) * (z i).im := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.star_apply]
  rw [Complex.star_def]
  rw [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.mul_im]
  rw [Complex.normSq_apply]
  ring

/-- A nonzero vector gives a strictly positive imaginary diagonal quadratic
form when all diagonal entries lie in the open upper half-plane. -/
theorem im_star_dotProduct_diagonal_mulVec_pos
    {n : Type*} [Fintype n] [DecidableEq n]
    (z v : n → ℂ) (hz : ∀ i, 0 < (z i).im) (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ (Matrix.diagonal z *ᵥ v)).im := by
  rw [im_star_dotProduct_diagonal_mulVec]
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (Complex.normSq_nonneg _) (hz j).le
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_pos (Complex.normSq_pos.mpr hi) (hz i)

/-- If `A` is Hermitian and every `z i` is in the open upper half-plane,
then `diag z - A` is nonsingular. -/
theorem det_diagonal_sub_hermitian_ne_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (z : n → ℂ) (hz : ∀ i, 0 < (z i).im) :
    (Matrix.diagonal z - A).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hker⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hquad : star v ⬝ᵥ ((Matrix.diagonal z - A) *ᵥ v) = 0 := by
    rw [hker, dotProduct_zero]
  have himquad :
      (star v ⬝ᵥ (Matrix.diagonal z *ᵥ v)).im -
        (star v ⬝ᵥ (A *ᵥ v)).im = 0 := by
    have h := congrArg Complex.im hquad
    simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im,
      Complex.zero_im] using h
  have himA : (star v ⬝ᵥ (A *ᵥ v)).im = 0 :=
    hA.im_star_dotProduct_mulVec_self v
  have himDiag : (star v ⬝ᵥ (Matrix.diagonal z *ᵥ v)).im = 0 := by
    linarith
  exact (ne_of_gt (im_star_dotProduct_diagonal_mulVec_pos z v hz hv)) himDiag

/-- Definite determinantal polynomials of Hermitian matrices are complex
stable. -/
theorem hermitianDetPoly_complexStable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ComplexStable (hermitianDetPoly A) := by
  intro z hz
  rw [eval_hermitianDetPoly]
  exact det_diagonal_sub_hermitian_ne_zero A hA z hz

/-- Hermitian symmetry makes every coefficient of the determinantal
polynomial fixed by complex conjugation. -/
theorem map_star_hermitianDetPoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    MvPolynomial.map (starRingEnd ℂ) (hermitianDetPoly A) =
      hermitianDetPoly A := by
  unfold hermitianDetPoly
  rw [RingHom.map_det]
  calc
    ((MvPolynomial.map (starRingEnd ℂ)).mapMatrix
        (Matrix.diagonal (fun i => MvPolynomial.X i) -
          A.map MvPolynomial.C)).det =
        (Matrix.diagonal (fun i => MvPolynomial.X i) -
          A.map MvPolynomial.C).transpose.det := by
      congr 1
      apply Matrix.ext
      intro i j
      by_cases hij : i = j
      · subst j
        have hd : star (A i i) = A i i := hA.apply i i
        simp [starRingEnd_apply, hd]
      · have hentry : star (A i j) = A j i := hA.apply j i
        simp [hij, Ne.symm hij, starRingEnd_apply, hentry]
    _ = _ := Matrix.det_transpose _

/-- The real-coefficient form obtained by taking real parts coefficientwise. -/
noncomputable def realHermitianDetPoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : MvPolynomial ι ℝ :=
  Finsupp.mapRange Complex.re Complex.zero_re (hermitianDetPoly A)

/-- Complexifying the real coefficient form recovers the original
determinantal polynomial. -/
theorem map_realHermitianDetPoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    MvPolynomial.map Complex.ofRealHom (realHermitianDetPoly A) =
      hermitianDetPoly A := by
  unfold realHermitianDetPoly
  rw [MvPolynomial.map_mapRange_eq_iff]
  intro d
  change ((coeff d (hermitianDetPoly A)).re : ℂ) =
    coeff d (hermitianDetPoly A)
  rw [← Complex.conj_eq_iff_re]
  have hcoeff := congrArg (MvPolynomial.coeff d)
    (map_star_hermitianDetPoly A hA)
  rw [MvPolynomial.coeff_map] at hcoeff
  exact hcoeff

/-- The real-coefficient definite determinantal polynomial is real stable. -/
theorem realHermitianDetPoly_realStable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    RealStable (realHermitianDetPoly A) := by
  intro z hz
  have hs := hermitianDetPoly_complexStable A hA z hz
  rw [← map_realHermitianDetPoly A hA] at hs
  simpa [MvPolynomial.eval₂_map] using hs

end CommutatorTheorem.BTDeterminantStability
