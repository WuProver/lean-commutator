import CommutatorTheorem.Epsilon.BTMDPDeletionIdentity
import CommutatorTheorem.Epsilon.BTExactSecondMoment

/-!
# Algebraic single-matrix specialization of the exact MDP

The exact mixed determinantal polynomial becomes a scaled ordinary
characteristic polynomial when only one member of the matrix family is
nonzero.  This file develops the finite algebra needed for that specialization.
-/

open scoped BigOperators Polynomial

namespace CommutatorTheorem.BTMDPJointControl

open CommutatorTheorem
open CommutatorTheorem.BTMixedDet
open CommutatorTheorem.BTMixedDeterminantal
open CommutatorTheorem.BTMDPSelection
open CommutatorTheorem.BTMDPDeletionIdentity
open CommutatorTheorem.BTMDPStability
open CommutatorTheorem.BTExactSecondMoment
open Polynomial Finset

/-- A matrix family supported at one distinguished color. -/
def singleMatrixFamily {n k : ℕ} (a₀ : Fin k)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    Fin k → Matrix (Fin n) (Fin n) ℂ :=
  fun a ↦ if a = a₀ then A else 0

theorem singleMatrixFamily_isHermitian {n k : ℕ} (a₀ : Fin k)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ∀ a, (singleMatrixFamily a₀ A a).IsHermitian := by
  intro a
  by_cases ha : a = a₀
  · simp [singleMatrixFamily, ha, hA]
  · simp [singleMatrixFamily, ha]

/-- Substitution `X ↦ kX`. -/
noncomputable def scaleVariable (k : ℝ) (p : ℝ[X]) : ℝ[X] :=
  p.comp (C k * X)

/-- The closed form expected for the single-matrix exact MDP. -/
noncomputable def normalizedScaledRealCharpoly {n : ℕ} (k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) : ℝ[X] :=
  ((k : ℝ) ^ n)⁻¹ • scaleVariable k (realCharpoly A hA)

lemma derivative_scaleVariable (k : ℝ) (p : ℝ[X]) :
    (scaleVariable k p).derivative =
      C k * scaleVariable k p.derivative := by
  rw [scaleVariable, Polynomial.derivative_comp]
  simp [scaleVariable]

/-- Dimension-zero base case of the closed form. -/
theorem singleMatrixMDP_closedForm_zero
    {k : ℕ} (_hk : 0 < k) (a₀ : Fin k)
    (A : Matrix (Fin 0) (Fin 0) ℂ) (hA : A.IsHermitian) :
    realMixedDeterminantalPolynomial (singleMatrixFamily a₀ A)
      (singleMatrixFamily_isHermitian a₀ hA) =
        normalizedScaledRealCharpoly k A hA := by
  simp [realMixedDeterminantalPolynomial, realColoringPolynomial,
    realCharpoly, normalizedScaledRealCharpoly, scaleVariable]

/-- The proposed closed form obeys the same coordinate-deletion differential
recurrence as the exact MDP. -/
theorem derivative_normalizedScaledRealCharpoly
    {n k : ℕ} (hk : 0 < k)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) :
    (normalizedScaledRealCharpoly k A hA).derivative =
      ∑ i : Fin (n + 1),
        normalizedScaledRealCharpoly k
          (A.submatrix i.succAbove i.succAbove) (hA.submatrix i.succAbove) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  calc
    (normalizedScaledRealCharpoly k A hA).derivative =
        ((k : ℝ) ^ n)⁻¹ •
          scaleVariable k (realCharpoly A hA).derivative := by
      rw [normalizedScaledRealCharpoly, Polynomial.derivative_smul,
        derivative_scaleVariable]
      rw [pow_succ]
      rw [Polynomial.C_mul']
      rw [smul_smul]
      congr 1
      field_simp
    _ = ((k : ℝ) ^ n)⁻¹ • scaleVariable k
          (∑ i : Fin (n + 1),
            realCharpoly (A.submatrix i.succAbove i.succAbove)
              (hA.submatrix i.succAbove)) := by
      rw [realCharpoly_derivative_eq_sum_principal_fin_succ]
    _ = _ := by
      simp [normalizedScaledRealCharpoly, scaleVariable,
        Polynomial.sum_comp, Finset.smul_sum]

/-- Two real polynomials with the same derivative and the same value at zero
are equal. -/
lemma polynomial_eq_of_derivative_eq_of_eval_zero_eq {p q : ℝ[X]}
    (hderiv : p.derivative = q.derivative) (hzero : p.eval 0 = q.eval 0) :
    p = q := by
  have hdifference : (p - q).derivative = 0 := by
    rw [Polynomial.derivative_sub, hderiv, sub_self]
  have hconstant := Polynomial.eq_C_of_derivative_eq_zero hdifference
  apply sub_eq_zero.mp
  calc
    p - q = C ((p - q).coeff 0) := hconstant
    _ = C ((p - q).eval 0) := by rw [Polynomial.coeff_zero_eq_eval_zero]
    _ = 0 := by simp [hzero]

private theorem deleteFamilyAt_singleMatrixFamily_aux {n k : ℕ} (a₀ : Fin k)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    deleteFamilyAt (singleMatrixFamily a₀ A) i =
      singleMatrixFamily a₀ (A.submatrix i.succAbove i.succAbove) := by
  funext a
  by_cases ha : a = a₀
  · simp [singleMatrixFamily, deleteFamilyAt, ha]
  · simp [singleMatrixFamily, deleteFamilyAt, ha]

/-- Inductive step for the closed form.  The deletion recurrence settles all
positive-degree coefficients; only the displayed value-at-zero identity is
left for the finite coloring count. -/
theorem singleMatrixMDP_closedForm_succ_of_eval_zero
    {n k : ℕ} (hk : 0 < k) (a₀ : Fin k)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian)
    (hminor : ∀ i : Fin (n + 1),
      realMixedDeterminantalPolynomial
          (singleMatrixFamily a₀ (A.submatrix i.succAbove i.succAbove))
          (singleMatrixFamily_isHermitian a₀ (hA.submatrix i.succAbove)) =
        normalizedScaledRealCharpoly k
          (A.submatrix i.succAbove i.succAbove) (hA.submatrix i.succAbove))
    (hzero :
      (realMixedDeterminantalPolynomial (singleMatrixFamily a₀ A)
        (singleMatrixFamily_isHermitian a₀ hA)).eval 0 =
      (normalizedScaledRealCharpoly k A hA).eval 0) :
    realMixedDeterminantalPolynomial (singleMatrixFamily a₀ A)
      (singleMatrixFamily_isHermitian a₀ hA) =
        normalizedScaledRealCharpoly k A hA := by
  apply polynomial_eq_of_derivative_eq_of_eval_zero_eq _ hzero
  rw [derivative_realMixedDeterminantalPolynomial_eq_sum_deleteFamilyAt hk]
  rw [derivative_normalizedScaledRealCharpoly hk]
  apply Finset.sum_congr rfl
  intro i _
  calc
    realMixedDeterminantalPolynomial
        (deleteFamilyAt (singleMatrixFamily a₀ A) i)
        (deleteFamilyAt_isHermitian (singleMatrixFamily_isHermitian a₀ hA) i) =
      realMixedDeterminantalPolynomial
        (singleMatrixFamily a₀ (A.submatrix i.succAbove i.succAbove))
        (singleMatrixFamily_isHermitian a₀ (hA.submatrix i.succAbove)) := by
          exact realMixedDeterminantalPolynomial_congr _ _ _ _
            (deleteFamilyAt_singleMatrixFamily_aux a₀ A i)
    _ = _ := hminor i

/-- Deleting a coordinate commutes with forming a singly supported family. -/
theorem deleteFamilyAt_singleMatrixFamily {n k : ℕ} (a₀ : Fin k)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    deleteFamilyAt (singleMatrixFamily a₀ A) i =
      singleMatrixFamily a₀ (A.submatrix i.succAbove i.succAbove) := by
  funext a
  by_cases ha : a = a₀
  · simp [singleMatrixFamily, deleteFamilyAt, ha]
  · simp [singleMatrixFamily, deleteFamilyAt, ha]

private lemma eval_zero_realCharpoly_zero_of_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (realCharpoly (0 : Matrix ι ι ℂ) Matrix.isHermitian_zero).eval 0 = 0 := by
  apply Complex.ofReal_injective
  calc
    Complex.ofReal
        ((realCharpoly (0 : Matrix ι ι ℂ) Matrix.isHermitian_zero).eval 0) =
        ((realCharpoly (0 : Matrix ι ι ℂ) Matrix.isHermitian_zero).map
          Complex.ofRealHom).eval 0 := by
      rw [Polynomial.eval_map]
      simpa using
        (Polynomial.eval₂_at_apply Complex.ofRealHom (0 : ℝ)
          (p := realCharpoly (0 : Matrix ι ι ℂ) Matrix.isHermitian_zero)).symm
    _ = (0 : Matrix ι ι ℂ).charpoly.eval 0 := by
      rw [realCharpoly_map_complex]
    _ = 0 := by
      rw [Matrix.charpoly_zero]
      simp [Fintype.card_ne_zero]

private lemma eval_zero_realColoringPolynomial_single_of_ne_constant
    {n k : ℕ} (a₀ : Fin k) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (c : Coloring n k)
    (hc : c ≠ fun _ ↦ a₀) :
    (realColoringPolynomial (singleMatrixFamily a₀ A)
      (singleMatrixFamily_isHermitian a₀ hA) c).eval 0 = 0 := by
  have hexists : ∃ i : Fin n, c i ≠ a₀ := by
    by_contra hnone
    push Not at hnone
    apply hc
    funext i
    exact hnone i
  obtain ⟨i, hi⟩ := hexists
  let a : Fin k := c i
  have ha : a ≠ a₀ := hi
  let ii : ColorFiber c a := ⟨i, rfl⟩
  letI : Nonempty (ColorFiber c a) := ⟨ii⟩
  rw [realColoringPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  let M := BTMixedDet.principalCompression (singleMatrixFamily a₀ A a) c a
  let hM := BTMixedDet.principalCompression_isHermitian
    (singleMatrixFamily_isHermitian a₀ hA a) c a
  have hMzero : M = 0 := by
    ext u v
    simp [M, singleMatrixFamily, ha]
  have hpoly : realCharpoly M hM =
      realCharpoly (0 : Matrix (ColorFiber c a) (ColorFiber c a) ℂ)
        Matrix.isHermitian_zero := by
    apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
    rw [realCharpoly_map_complex, realCharpoly_map_complex, hMzero]
  change (realCharpoly M hM).eval 0 = 0
  rw [hpoly]
  convert (eval_zero_realCharpoly_zero_of_nonempty
    (ι := ColorFiber c a)) using 1

private def constantColorFiberEquiv {n k : ℕ} (a₀ : Fin k) :
    ColorFiber (fun _ : Fin n ↦ a₀) a₀ ≃ Fin n where
  toFun i := i.1
  invFun i := ⟨i, rfl⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

private lemma realCharpoly_constant_mainFiber
    {n k : ℕ} (a₀ : Fin k) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) :
    realCharpoly
        (BTMixedDet.principalCompression A (fun _ ↦ a₀) a₀)
        (BTMixedDet.principalCompression_isHermitian hA (fun _ ↦ a₀) a₀) =
      realCharpoly A hA := by
  let e := constantColorFiberEquiv (n := n) a₀
  have hreindex : Matrix.reindex e e
      (BTMixedDet.principalCompression A (fun _ ↦ a₀) a₀) = A := by
    ext i j
    rfl
  exact (realCharpoly_eq_of_reindex_eq e _ _ _ _ hreindex).symm

private lemma eval_zero_realColoringPolynomial_single_constant
    {n k : ℕ} (a₀ : Fin k) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) :
    (realColoringPolynomial (singleMatrixFamily a₀ A)
      (singleMatrixFamily_isHermitian a₀ hA) (fun _ ↦ a₀)).eval 0 =
        (realCharpoly A hA).eval 0 := by
  rw [realColoringPolynomial]
  have hprod :
      (∏ a : Fin k,
        realCharpoly
          (BTMixedDet.principalCompression (singleMatrixFamily a₀ A a)
            (fun _ ↦ a₀) a)
          (BTMixedDet.principalCompression_isHermitian
            (singleMatrixFamily_isHermitian a₀ hA a) (fun _ ↦ a₀) a)) =
        realCharpoly A hA := by
    rw [Finset.prod_eq_single a₀]
    · simpa [singleMatrixFamily] using realCharpoly_constant_mainFiber a₀ A hA
    · intro b _hb hba
      rw [realCharpoly]
      apply Finset.prod_eq_one
      intro z _hz
      exact False.elim (hba (by simpa using z.2.symm))
    · simp
  rw [hprod]

/-- Only the constant distinguished-color coloring contributes to the exact
MDP at `X = 0`. -/
theorem eval_zero_realMixedDeterminantalPolynomial_single
    {n k : ℕ} (a₀ : Fin k)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    (realMixedDeterminantalPolynomial (singleMatrixFamily a₀ A)
      (singleMatrixFamily_isHermitian a₀ hA)).eval 0 =
        ((k : ℝ) ^ n)⁻¹ * (realCharpoly A hA).eval 0 := by
  have hsum :
      (∑ c : Coloring n k,
        (realColoringPolynomial (singleMatrixFamily a₀ A)
          (singleMatrixFamily_isHermitian a₀ hA) c).eval 0) =
        (realCharpoly A hA).eval 0 := by
    rw [Finset.sum_eq_single (fun _ : Fin n ↦ a₀)]
    · exact eval_zero_realColoringPolynomial_single_constant a₀ A hA
    · intro c _hc hcne
      exact eval_zero_realColoringPolynomial_single_of_ne_constant a₀ A hA c hcne
    · simp
  have hevalsum := map_sum (Polynomial.evalRingHom (0 : ℝ))
    (fun c : Coloring n k ↦ realColoringPolynomial (singleMatrixFamily a₀ A)
      (singleMatrixFamily_isHermitian a₀ hA) c) Finset.univ
  change
    (Polynomial.eval 0 (∑ c : Coloring n k,
      realColoringPolynomial (singleMatrixFamily a₀ A)
        (singleMatrixFamily_isHermitian a₀ hA) c)) =
      ∑ c : Coloring n k,
        Polynomial.eval 0 (realColoringPolynomial (singleMatrixFamily a₀ A)
          (singleMatrixFamily_isHermitian a₀ hA) c) at hevalsum
  rw [realMixedDeterminantalPolynomial, Polynomial.eval_smul, hevalsum]
  rw [hsum, BTMixedDet.coloring_card]
  simp only [smul_eq_mul, Nat.cast_pow]

theorem eval_zero_normalizedScaledRealCharpoly
    {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    (normalizedScaledRealCharpoly k A hA).eval 0 =
      ((k : ℝ) ^ n)⁻¹ * (realCharpoly A hA).eval 0 := by
  simp [normalizedScaledRealCharpoly, scaleVariable, Polynomial.eval_comp,
    Polynomial.eval_mul]

/-- The exact closed form whose finite coloring proof is developed in this
file.  It is an ordinary proposition so downstream spectral reductions can
already use precisely the remaining algebraic input. -/
def SingleMatrixMDPClosedForm : Prop :=
  ∀ (n k : ℕ) (_hk : 0 < k) (a₀ : Fin k)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian),
    realMixedDeterminantalPolynomial (singleMatrixFamily a₀ A)
      (singleMatrixFamily_isHermitian a₀ hA) =
        normalizedScaledRealCharpoly k A hA

/-- Exact closed form for a family with a single nonzero member:
`MDP[A, 0, …, 0](X) = k⁻ⁿ χ_A(kX)`. -/
theorem singleMatrixMDP_closedForm : SingleMatrixMDPClosedForm := by
  intro n
  induction n with
  | zero =>
      intro k hk a₀ A hA
      exact singleMatrixMDP_closedForm_zero hk a₀ A hA
  | succ n ih =>
      intro k hk a₀ A hA
      apply singleMatrixMDP_closedForm_succ_of_eval_zero hk a₀ A hA
      · intro i
        exact ih k hk a₀
          (A.submatrix i.succAbove i.succAbove) (hA.submatrix i.succAbove)
      · rw [eval_zero_realMixedDeterminantalPolynomial_single a₀ A hA,
          eval_zero_normalizedScaledRealCharpoly]

/-! ## Reduction of joint control to one-coordinate zeroing

Theorem 15 of Ravichandran--Srivastava is obtained by repeatedly applying
their Proposition 16: setting one row and the matching column of a
zero-diagonal Hermitian member to zero cannot increase the largest root.
The definitions and finite inductions below formalize that reduction. -/

/-- Set row `i` and column `i` of a matrix to zero. -/
def zeroRowCol {ι : Type*} [DecidableEq ι] (M : Matrix ι ι ℂ) (i : ι) :
    Matrix ι ι ℂ :=
  fun r c ↦ if r = i ∨ c = i then 0 else M r c

theorem zeroRowCol_isHermitian {ι : Type*} [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (i : ι) :
    (zeroRowCol M i).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro r c
  by_cases hr : r = i <;> by_cases hc : c = i <;>
    simp [zeroRowCol, hr, hc, hM.apply]

theorem zeroRowCol_zeroDiag {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : ZeroDiag M) (i : Fin n) :
    ZeroDiag (zeroRowCol M i) := by
  intro r
  by_cases hr : r = i
  · simp [zeroRowCol, hr]
  · simp [zeroRowCol, hr, hM r]

/-- The quadratic trace of a Hermitian matrix is the real scalar given by its
entrywise squared Hilbert--Schmidt norm. -/
theorem trace_mul_self_eq_ofReal_sum_normSq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
    (M * M).trace =
      (↑(∑ r : Fin n, ∑ c : Fin n, Complex.normSq (M r c)) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  rw [← hM.apply c r]
  simpa only [starRingEnd_apply] using Complex.mul_conj (M r c)

theorem trace_mul_self_re_eq_sum_normSq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
    (M * M).trace.re = ∑ r : Fin n, ∑ c : Fin n, Complex.normSq (M r c) := by
  rw [trace_mul_self_eq_ofReal_sum_normSq M hM]
  simp

/-- Zeroing a nonzero matching row and column strictly decreases the
quadratic trace. -/
theorem trace_zeroRowCol_mul_self_re_lt {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) (i : Fin n)
    (hi : ∃ j : Fin n, M i j ≠ 0) :
    ((zeroRowCol M i) * zeroRowCol M i).trace.re < (M * M).trace.re := by
  rw [trace_mul_self_re_eq_sum_normSq (zeroRowCol M i)
      (zeroRowCol_isHermitian hM i),
    trace_mul_self_re_eq_sum_normSq M hM]
  apply Finset.sum_lt_sum
  · intro r _
    apply Finset.sum_le_sum
    intro c _
    by_cases hr : r = i <;> by_cases hc : c = i
    <;> simp [zeroRowCol, hr, hc, Complex.normSq_nonneg]
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    simp only [zeroRowCol, true_or, if_true, Complex.normSq_zero,
      Finset.sum_const_zero]
    apply Finset.sum_pos'
    · intro c _
      exact Complex.normSq_nonneg _
    · obtain ⟨j, hj⟩ := hi
      exact ⟨j, Finset.mem_univ j, Complex.normSq_pos.mpr hj⟩

/-- Scale one row.  This asymmetric auxiliary matrix is useful because its
characteristic polynomial is affine in the scale parameter. -/
def rowScale {ι : Type*} [DecidableEq ι]
    (t : ℂ) (M : Matrix ι ι ℂ) (i : ι) : Matrix ι ι ℂ :=
  fun r c ↦ if r = i then t * M r c else M r c

/-- If the distinguished diagonal entry vanishes, row scaling gives an
affine characteristic-polynomial pencil.  This is the determinant
multilinearity step behind the coordinate-scaled MDP pencil. -/
theorem charpoly_rowScale_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℂ) (M : Matrix ι ι ℂ) (i : ι) (hdiag : M i i = 0) :
    (rowScale t M i).charpoly =
      (rowScale 0 M i).charpoly + C t *
        ((rowScale 1 M i).charpoly - (rowScale 0 M i).charpoly) := by
  let N₀ := Matrix.charmatrix (rowScale 0 M i)
  let N₁ := Matrix.charmatrix (rowScale 1 M i)
  have hNt : Matrix.charmatrix (rowScale t M i) =
      N₀.updateRow i (N₀ i + C t • (N₁ i - N₀ i)) := by
    ext r c
    by_cases hri : r = i
    · subst r
      by_cases hci : c = i
      · subst c
        simp [N₀, N₁, rowScale, hdiag]
      · simp [N₀, N₁, Matrix.charmatrix_apply, rowScale]
        ring
    · simp [N₀, N₁, Matrix.charmatrix_apply, rowScale, hri]
  have hN₁ : N₁ = N₀.updateRow i (N₁ i) := by
    ext r c
    by_cases hri : r = i
    · subst r
      simp
    · simp [N₀, N₁, Matrix.charmatrix_apply, rowScale, hri]
  have hdiff : (N₀.updateRow i (N₁ i - N₀ i)).det = N₁.det - N₀.det := by
    have hadd := Matrix.det_updateRow_add N₀ i (N₀ i) (N₁ i - N₀ i)
    have hrow : N₀ i + (N₁ i - N₀ i) = N₁ i := by
      module
    rw [hrow, Matrix.updateRow_eq_self, ← hN₁] at hadd
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using hadd.symm
  simp only [Matrix.charpoly]
  rw [hNt, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self, hdiff]

/-- The real coordinate scaling matrix with entry `√t` in coordinate `i` and
ones elsewhere.  Congruence by this matrix preserves Hermitian matrices. -/
noncomputable def coordinateScaleDiagonal {ι : Type*} [DecidableEq ι]
    (t : ℝ) (i : ι) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun j ↦ if j = i then (Real.sqrt t : ℂ) else 1)

/-- Symmetrically scale coordinate `i` by `√t`.  This interpolates between
zeroing the matching row and column (`t = 0`) and the original matrix
(`t = 1`). -/
noncomputable def coordinateScale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (M : Matrix ι ι ℂ) (i : ι) : Matrix ι ι ℂ :=
  coordinateScaleDiagonal t i * M * coordinateScaleDiagonal t i

theorem coordinateScale_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (M : Matrix ι ι ℂ) (i r c : ι) :
    coordinateScale t M i r c =
      (if r = i then (Real.sqrt t : ℂ) else 1) * M r c *
        (if c = i then (Real.sqrt t : ℂ) else 1) := by
  simp [coordinateScale, coordinateScaleDiagonal]

theorem coordinateScale_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (i : ι) :
    (coordinateScale t M i).IsHermitian := by
  let D := coordinateScaleDiagonal t i
  have hD : Matrix.conjTranspose D = D := by
    ext r c
    by_cases hrc : r = c
    · subst c
      by_cases hr : r = i <;>
        simp [D, coordinateScaleDiagonal, Matrix.conjTranspose_apply, hr]
    · have hcr : c ≠ r := Ne.symm hrc
      simp [D, coordinateScaleDiagonal, Matrix.conjTranspose_apply, hrc, hcr]
  simpa [coordinateScale, D, hD] using
    Matrix.isHermitian_conjTranspose_mul_mul D hM

theorem coordinateScale_zeroDiag {n : ℕ} (t : ℝ)
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : ZeroDiag M) (i : Fin n) :
    ZeroDiag (coordinateScale t M i) := by
  intro r
  rw [coordinateScale_apply, hM r]
  simp

theorem coordinateScale_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (i : ι) :
    coordinateScale 0 M i = zeroRowCol M i := by
  ext r c
  rw [coordinateScale_apply]
  by_cases hr : r = i <;> by_cases hc : c = i <;>
    simp [zeroRowCol, hr, hc]

theorem coordinateScale_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (i : ι) :
    coordinateScale 1 M i = M := by
  ext r c
  simp [coordinateScale_apply]

/-- Symmetric coordinate scaling has the same characteristic polynomial as
asymmetric row scaling.  This follows from `χ(AB) = χ(BA)` and is the bridge
between Hermitian real-rootedness and determinant multilinearity. -/
theorem charpoly_coordinateScale_eq_rowScale
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) (ht : 0 ≤ t)
    (M : Matrix ι ι ℂ) (i : ι) :
    (coordinateScale t M i).charpoly = (rowScale (t : ℂ) M i).charpoly := by
  let D := coordinateScaleDiagonal t i
  have hsq : (Real.sqrt t : ℂ) * Real.sqrt t = t := by
    norm_cast
    simpa [pow_two] using Real.sq_sqrt ht
  have hmat : D * (D * M) = rowScale (t : ℂ) M i := by
    ext r c
    by_cases hr : r = i
    · subst r
      simp only [coordinateScaleDiagonal, Matrix.diagonal_mul, ↓reduceIte, rowScale, D]
      rw [← mul_assoc, hsq]
    · simp [D, coordinateScaleDiagonal, rowScale, hr]
  calc
    (coordinateScale t M i).charpoly = ((D * M) * D).charpoly := by
      rfl
    _ = (D * (D * M)).charpoly := Matrix.charpoly_mul_comm (D * M) D
    _ = (rowScale (t : ℂ) M i).charpoly := by rw [hmat]

/-- Although scaling a row by zero need not literally zero the matching
column, it has the same characteristic polynomial as matching row/column
zeroing. -/
theorem charpoly_rowScale_zero_eq_zeroRowCol
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (i : ι) :
    (rowScale 0 M i).charpoly = (zeroRowCol M i).charpoly := by
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun j ↦ if j = i then 0 else 1)
  have hDsq : D * D = D := by
    ext r c
    by_cases hr : r = i <;> by_cases hc : c = i <;>
      simp [D, hr, hc]
  have hrow : D * M = rowScale 0 M i := by
    ext r c
    by_cases hr : r = i <;> simp [D, rowScale, hr]
  have hzero : (D * M) * D = zeroRowCol M i := by
    ext r c
    by_cases hr : r = i <;> by_cases hc : c = i <;>
      simp [D, zeroRowCol, hr, hc]
  calc
    (rowScale 0 M i).charpoly = (D * M).charpoly := by rw [hrow]
    _ = ((D * D) * M).charpoly := by rw [hDsq]
    _ = (D * (D * M)).charpoly := by rw [Matrix.mul_assoc]
    _ = ((D * M) * D).charpoly := (Matrix.charpoly_mul_comm (D * M) D).symm
    _ = (zeroRowCol M i).charpoly := by rw [hzero]

/-- For a zero diagonal entry, the Hermitian coordinate-scaled characteristic
polynomial is exactly affine in the nonnegative parameter `t`. -/
theorem charpoly_coordinateScale_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) (ht : 0 ≤ t)
    (M : Matrix ι ι ℂ) (i : ι) (hdiag : M i i = 0) :
    (coordinateScale t M i).charpoly =
      (coordinateScale 0 M i).charpoly + C (t : ℂ) *
        ((coordinateScale 1 M i).charpoly - (coordinateScale 0 M i).charpoly) := by
  rw [charpoly_coordinateScale_eq_rowScale t ht,
    charpoly_rowScale_affine (t : ℂ) M i hdiag,
    coordinateScale_zero, coordinateScale_one,
    charpoly_rowScale_zero_eq_zeroRowCol]
  have hrow1 : rowScale 1 M i = M := by
    ext r c
    simp [rowScale]
  rw [hrow1]

/-- Apply `zeroRowCol` to one selected member of a matrix family. -/
def zeroRowColFamily {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin k) (i : Fin n) :
    Fin k → Matrix (Fin n) (Fin n) ℂ :=
  fun b ↦ if b = a then zeroRowCol (A b) i else A b

theorem zeroRowColFamily_isHermitian {n k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ a, (A a).IsHermitian) (a : Fin k) (i : Fin n) :
    ∀ b, (zeroRowColFamily A a i b).IsHermitian := by
  intro b
  by_cases hba : b = a
  · subst b
    simp only [zeroRowColFamily, if_pos]
    exact zeroRowCol_isHermitian (hA a) i
  · simp [zeroRowColFamily, hba, hA b]

theorem zeroRowColFamily_zeroDiag {n k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ a, ZeroDiag (A a)) (a : Fin k) (i : Fin n) :
    ∀ b, ZeroDiag (zeroRowColFamily A a i b) := by
  intro b
  by_cases hba : b = a
  · subst b
    simp only [zeroRowColFamily, if_pos]
    exact zeroRowCol_zeroDiag (hA a) i
  · simpa [zeroRowColFamily, hba] using hA b

/-- Scale coordinate `i` in one selected member of a matrix family. -/
noncomputable def coordinateScaleFamily {n k : ℕ} (t : ℝ)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin k) (i : Fin n) :
    Fin k → Matrix (Fin n) (Fin n) ℂ :=
  fun b ↦ if b = a then coordinateScale t (A b) i else A b

theorem coordinateScaleFamily_isHermitian {n k : ℕ} (t : ℝ)
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ a, (A a).IsHermitian) (a : Fin k) (i : Fin n) :
    ∀ b, (coordinateScaleFamily t A a i b).IsHermitian := by
  intro b
  by_cases hba : b = a
  · subst b
    simp only [coordinateScaleFamily, if_pos]
    exact coordinateScale_isHermitian t (hA a) i
  · simp [coordinateScaleFamily, hba, hA b]

theorem coordinateScaleFamily_zeroDiag {n k : ℕ} (t : ℝ)
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ a, ZeroDiag (A a)) (a : Fin k) (i : Fin n) :
    ∀ b, ZeroDiag (coordinateScaleFamily t A a i b) := by
  intro b
  by_cases hba : b = a
  · subst b
    simp only [coordinateScaleFamily, if_pos]
    exact coordinateScale_zeroDiag t (hA a) i
  · simp [coordinateScaleFamily, hba, hA b]

/-- Coordinate scaling commutes with principal compression when the scaled
coordinate belongs to the fiber. -/
theorem principalCompression_coordinateScale_of_mem {n k : ℕ} (t : ℝ)
    (M : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n k) (a : Fin k)
    (i : Fin n) (hi : c i = a) :
    BTMixedDet.principalCompression (coordinateScale t M i) c a =
      coordinateScale t (BTMixedDet.principalCompression M c a) ⟨i, hi⟩ := by
  ext r s
  rw [BTMixedDet.principalCompression_apply, coordinateScale_apply,
    coordinateScale_apply, BTMixedDet.principalCompression_apply]
  have hr : (r.1 = i) ↔ r = ⟨i, hi⟩ := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  have hs : (s.1 = i) ↔ s = ⟨i, hi⟩ := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  simp only [hr, hs]

/-- Coordinate scaling is invisible to a principal compression whose fiber
does not contain the scaled coordinate. -/
theorem principalCompression_coordinateScale_of_not_mem {n k : ℕ} (t : ℝ)
    (M : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n k) (a : Fin k)
    (i : Fin n) (hi : c i ≠ a) :
    BTMixedDet.principalCompression (coordinateScale t M i) c a =
      BTMixedDet.principalCompression M c a := by
  ext r s
  rw [BTMixedDet.principalCompression_apply, coordinateScale_apply,
    BTMixedDet.principalCompression_apply]
  have hr : r.1 ≠ i := by
    intro h
    apply hi
    simpa [h] using r.2
  have hs : s.1 ≠ i := by
    intro h
    apply hi
    simpa [h] using s.2
  simp [hr, hs]

theorem coordinateScaleFamily_zero {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin k) (i : Fin n) :
    coordinateScaleFamily 0 A a i = zeroRowColFamily A a i := by
  funext b
  by_cases hba : b = a
  · subst b
    simp [coordinateScaleFamily, zeroRowColFamily, coordinateScale_zero]
  · simp [coordinateScaleFamily, zeroRowColFamily, hba]

theorem coordinateScaleFamily_one {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin k) (i : Fin n) :
    coordinateScaleFamily 1 A a i = A := by
  funext b
  by_cases hba : b = a
  · subst b
    simp [coordinateScaleFamily, coordinateScale_one]
  · simp [coordinateScaleFamily, hba]

private theorem coloringPolynomial_coordinateScaleFamily_factor {n k : ℕ}
    (t : ℝ) (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (a : Fin k) (i : Fin n) (c : Coloring n k) :
    coloringPolynomial (coordinateScaleFamily t A a i) c =
      (BTMixedDet.principalCompression (coordinateScale t (A a) i) c a).charpoly *
        ∏ b ∈ Finset.univ.erase a,
          (BTMixedDet.principalCompression (A b) c b).charpoly := by
  rw [coloringPolynomial,
    ← Finset.mul_prod_erase Finset.univ
      (fun b ↦ (BTMixedDet.principalCompression
        (coordinateScaleFamily t A a i b) c b).charpoly)
      (Finset.mem_univ a)]
  simp only [coordinateScaleFamily, if_pos]
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  simp [hba]

/-- Every exact-MDP leaf is affine under one-coordinate scaling. -/
theorem coloringPolynomial_coordinateScaleFamily_affine {n k : ℕ}
    (t : ℝ) (ht : 0 ≤ t) (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (a : Fin k) (i : Fin n) (hdiag : A a i i = 0) (c : Coloring n k) :
    coloringPolynomial (coordinateScaleFamily t A a i) c =
      coloringPolynomial (coordinateScaleFamily 0 A a i) c + C (t : ℂ) *
        (coloringPolynomial (coordinateScaleFamily 1 A a i) c -
          coloringPolynomial (coordinateScaleFamily 0 A a i) c) := by
  rw [coloringPolynomial_coordinateScaleFamily_factor,
    coloringPolynomial_coordinateScaleFamily_factor,
    coloringPolynomial_coordinateScaleFamily_factor]
  by_cases hci : c i = a
  · rw [principalCompression_coordinateScale_of_mem t (A a) c a i hci,
      principalCompression_coordinateScale_of_mem 0 (A a) c a i hci,
      principalCompression_coordinateScale_of_mem 1 (A a) c a i hci,
      charpoly_coordinateScale_affine t ht
        (BTMixedDet.principalCompression (A a) c a) ⟨i, hci⟩ (by simpa using hdiag)]
    ring
  · rw [principalCompression_coordinateScale_of_not_mem t (A a) c a i hci,
      principalCompression_coordinateScale_of_not_mem 0 (A a) c a i hci,
      principalCompression_coordinateScale_of_not_mem 1 (A a) c a i hci]
    ring

/-- Averaging the leaf identities gives the exact complex MDP affine pencil. -/
theorem mixedDeterminantalPolynomial_coordinateScaleFamily_affine {n k : ℕ}
    (t : ℝ) (ht : 0 ≤ t) (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (a : Fin k) (i : Fin n) (hdiag : A a i i = 0) :
    mixedDeterminantalPolynomial (coordinateScaleFamily t A a i) =
      mixedDeterminantalPolynomial (coordinateScaleFamily 0 A a i) + C (t : ℂ) *
        (mixedDeterminantalPolynomial (coordinateScaleFamily 1 A a i) -
          mixedDeterminantalPolynomial (coordinateScaleFamily 0 A a i)) := by
  have hsum :
      (∑ c : Coloring n k,
          coloringPolynomial (coordinateScaleFamily t A a i) c) =
        (∑ c : Coloring n k,
          coloringPolynomial (coordinateScaleFamily 0 A a i) c) + C (t : ℂ) *
          ((∑ c : Coloring n k,
              coloringPolynomial (coordinateScaleFamily 1 A a i) c) -
            ∑ c : Coloring n k,
              coloringPolynomial (coordinateScaleFamily 0 A a i) c) := by
    simp_rw [coloringPolynomial_coordinateScaleFamily_affine t ht A a i hdiag]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [mixedDeterminantalPolynomial]
  rw [hsum]
  simp only [Polynomial.smul_eq_C_mul]
  ring

/-- Real-coefficient form of the exact MDP affine pencil. -/
theorem realMixedDeterminantalPolynomial_coordinateScaleFamily_affine
    {n k : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (a : Fin k) (i : Fin n)
    (hdiag : A a i i = 0) :
    realMixedDeterminantalPolynomial (coordinateScaleFamily t A a i)
        (coordinateScaleFamily_isHermitian t hA a i) =
      realMixedDeterminantalPolynomial (coordinateScaleFamily 0 A a i)
          (coordinateScaleFamily_isHermitian 0 hA a i) +
        t • (realMixedDeterminantalPolynomial (coordinateScaleFamily 1 A a i)
            (coordinateScaleFamily_isHermitian 1 hA a i) -
          realMixedDeterminantalPolynomial (coordinateScaleFamily 0 A a i)
            (coordinateScaleFamily_isHermitian 0 hA a i)) := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  simp only [realMixedDeterminantalPolynomial_map_complex,
    Polynomial.map_add, Polynomial.map_smul, Polynomial.map_sub]
  rw [Polynomial.smul_eq_C_mul]
  exact mixedDeterminantalPolynomial_coordinateScaleFamily_affine
    t ht A a i hdiag

/-- Endpoint form of the affine pencil: `t = 0` is row/column zeroing and
`t = 1` is the original exact MDP. -/
theorem realMixedDeterminantalPolynomial_coordinateScaleFamily_eq_endpoints
    {n k : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (a : Fin k) (i : Fin n)
    (hdiag : A a i i = 0) :
    realMixedDeterminantalPolynomial (coordinateScaleFamily t A a i)
        (coordinateScaleFamily_isHermitian t hA a i) =
      realMixedDeterminantalPolynomial (zeroRowColFamily A a i)
          (zeroRowColFamily_isHermitian hA a i) +
        t • (realMixedDeterminantalPolynomial A hA -
          realMixedDeterminantalPolynomial (zeroRowColFamily A a i)
            (zeroRowColFamily_isHermitian hA a i)) := by
  have hzero := realMixedDeterminantalPolynomial_congr
    (coordinateScaleFamily 0 A a i) (zeroRowColFamily A a i)
    (coordinateScaleFamily_isHermitian 0 hA a i)
    (zeroRowColFamily_isHermitian hA a i)
    (coordinateScaleFamily_zero A a i)
  have hone := realMixedDeterminantalPolynomial_congr
    (coordinateScaleFamily 1 A a i) A
    (coordinateScaleFamily_isHermitian 1 hA a i) hA
    (coordinateScaleFamily_one A a i)
  rw [realMixedDeterminantalPolynomial_coordinateScaleFamily_affine
    t ht A hA a i hdiag, hzero, hone]

/-- Real form of the exact second-lower coefficient, expressed directly as
the entrywise Hilbert--Schmidt energy of the family. -/
theorem realMixedDeterminantalPolynomial_coeff_sub_two_eq_neg_energy
    {n k : ℕ} (hn : 2 ≤ n)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a)) :
    (realMixedDeterminantalPolynomial A hA).coeff (n - 2) =
      -(((k : ℝ) ^ 2)⁻¹ *
        ∑ a : Fin k, ∑ r : Fin n, ∑ c : Fin n,
          Complex.normSq (A a r c)) / 2 := by
  apply Complex.ofReal_injective
  rw [BTExactSecondMoment.realMixedDeterminantalPolynomial_coeff_sub_two
    hn A hA hzd]
  simp_rw [trace_mul_self_eq_ofReal_sum_normSq (A _) (hA _)]
  push_cast
  rfl

/-- Zeroing a genuinely nonzero coordinate in one Hermitian family member
strictly decreases the total Hilbert--Schmidt energy. -/
theorem familyEnergy_zeroRowColFamily_lt {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (a : Fin k) (i : Fin n)
    (hi : ∃ j : Fin n, A a i j ≠ 0) :
    (∑ b : Fin k, ∑ r : Fin n, ∑ c : Fin n,
        Complex.normSq (zeroRowColFamily A a i b r c)) <
      ∑ b : Fin k, ∑ r : Fin n, ∑ c : Fin n,
        Complex.normSq (A b r c) := by
  have hselected := trace_zeroRowCol_mul_self_re_lt (A a) (hA a) i hi
  rw [trace_mul_self_re_eq_sum_normSq (zeroRowCol (A a) i)
      (zeroRowCol_isHermitian (hA a) i),
    trace_mul_self_re_eq_sum_normSq (A a) (hA a)] at hselected
  apply Finset.sum_lt_sum
  · intro b _
    by_cases hba : b = a
    · subst b
      simpa [zeroRowColFamily] using hselected.le
    · simp [zeroRowColFamily, hba]
  · refine ⟨a, Finset.mem_univ a, ?_⟩
    simpa [zeroRowColFamily] using hselected

/-- The affine direction from the zeroed MDP to the original MDP has strictly
negative second-lower coefficient whenever the selected row is nonzero. -/
theorem coordinateZeroingDirection_coeff_sub_two_neg
    {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a))
    (a : Fin k) (i : Fin n) (hi : ∃ j : Fin n, A a i j ≠ 0) :
    (realMixedDeterminantalPolynomial A hA -
      realMixedDeterminantalPolynomial (zeroRowColFamily A a i)
        (zeroRowColFamily_isHermitian hA a i)).coeff (n - 2) < 0 := by
  rw [Polynomial.coeff_sub,
    realMixedDeterminantalPolynomial_coeff_sub_two_eq_neg_energy hn A hA hzd,
    realMixedDeterminantalPolynomial_coeff_sub_two_eq_neg_energy hn
      (zeroRowColFamily A a i) (zeroRowColFamily_isHermitian hA a i)
      (fun b ↦ by
        by_cases hba : b = a
        · subst b
          simp only [zeroRowColFamily, if_pos]
          exact zeroRowCol_zeroDiag (hzd a) i
        · simpa [zeroRowColFamily, hba] using hzd b)]
  have henergy := familyEnergy_zeroRowColFamily_lt A hA a i hi
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hscale : 0 < ((k : ℝ) ^ 2)⁻¹ := by positivity
  have hpos : 0 < ((k : ℝ) ^ 2)⁻¹ *
      ((∑ b : Fin k, ∑ r : Fin n, ∑ c : Fin n, Complex.normSq (A b r c)) -
        ∑ b : Fin k, ∑ r : Fin n, ∑ c : Fin n,
          Complex.normSq (zeroRowColFamily A a i b r c)) / 2 := by
    exact div_pos (mul_pos hscale (sub_pos.mpr henergy)) (by norm_num)
  linarith

/-- If all roots of a monic real-rooted polynomial lie below `x`, then its
second root moment is bounded using only `x`, the degree, and the root sum.
This is the compactness estimate needed to orient the affine pencil at a
large parameter. -/
theorem sum_sq_roots_le_of_rootUpperBound {p : ℝ[X]}
    (hp : RealRooted p) (hmonic : p.Monic) {x : ℝ}
    (hx : IsRootUpperBound p x) :
    (p.roots.map fun z ↦ z ^ 2).sum ≤
      (p.natDegree : ℝ) * x ^ 2 -
          2 * x * ((p.natDegree : ℝ) * x - p.roots.sum) +
        ((p.natDegree : ℝ) * x - p.roots.sum) ^ 2 := by
  let l := p.roots.sort (· ≤ ·)
  have hlen : l.length = p.natDegree := by
    simp [l, hp.natDegree_eq_card_roots]
  have hroot (j : Fin l.length) : p.IsRoot (l.get j) := by
    apply (mem_roots hmonic.ne_zero).mp
    exact (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mp (l.get_mem j)
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin l.length)),
      0 ≤ x - l.get j := by
    intro j _
    exact sub_nonneg.mpr (hx _ (hroot j))
  have hsquare := Finset.sum_sq_le_sq_sum_of_nonneg hnonneg
  have hsuml : (∑ j : Fin l.length, l.get j) = p.roots.sum := by
    simpa [l] using (multiset_map_sum_eq_fin_sum_sort p.roots id).symm
  have hsum : (∑ j : Fin l.length, (x - l.get j)) =
      (p.natDegree : ℝ) * x - p.roots.sum := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    simp only [hlen, hsuml]
  have hsq : (∑ j : Fin l.length, (l.get j) ^ 2) =
      (p.roots.map fun z ↦ z ^ 2).sum := by
    exact (multiset_map_sum_eq_fin_sum_sort p.roots (fun z ↦ z ^ 2)).symm
  rw [hsum] at hsquare
  rw [← hsq]
  calc
    ∑ j : Fin l.length, (l.get j) ^ 2 =
        (p.natDegree : ℝ) * x ^ 2 -
            2 * x * ((p.natDegree : ℝ) * x - p.roots.sum) +
          ∑ j : Fin l.length, (x - l.get j) ^ 2 := by
      rw [← hsum]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      simp only [hlen]
      rw [hsuml]
      ring_nf
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hlen]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hsuml]
      ring
    _ ≤ _ := by linarith

/-- A negative affine slope in the coefficient two below the lead forces
the second root moment past every bound.  Consequently, for any fixed `x`,
some member of the nonnegative pencil has a root strictly above `x`. -/
theorem exists_parameter_not_rootUpperBound_of_coeff_sub_two_neg
    (d : ℕ) (r s : ℝ[X]) (hd : 2 ≤ d)
    (hmonic : ∀ t : ℝ, 0 ≤ t → (r + t • s).Monic)
    (hdegree : ∀ t : ℝ, 0 ≤ t → (r + t • s).natDegree = d)
    (hreal : ∀ t : ℝ, 0 ≤ t → RealRooted (r + t • s))
    (hnext : ∀ t : ℝ, 0 ≤ t →
      (r + t • s).nextCoeff = r.nextCoeff)
    (hslope : s.coeff (d - 2) < 0) (x : ℝ) :
    ∃ t : ℝ, 1 ≤ t ∧ ¬ IsRootUpperBound (r + t • s) x := by
  let B : ℝ :=
    (d : ℝ) * x ^ 2 -
      2 * x * ((d : ℝ) * x - (-r.nextCoeff)) +
        ((d : ℝ) * x - (-r.nextCoeff)) ^ 2
  let A : ℝ := (-r.nextCoeff) ^ 2 - 2 * r.coeff (d - 2)
  let c : ℝ := -2 * s.coeff (d - 2)
  have hc : 0 < c := by dsimp [c]; linarith
  let t : ℝ := max 1 ((B - A) / c + 1)
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  refine ⟨t, ht1, ?_⟩
  intro hub
  let p := r + t • s
  have hpmonic : p.Monic := hmonic t ht0
  have hpdegree : p.natDegree = d := hdegree t ht0
  have hpreal : RealRooted p := hreal t ht0
  have hpsum : p.roots.sum = -r.nextCoeff := by
    have hv := hpreal.nextCoeff_eq_neg_sum_roots_of_monic hpmonic
    rw [hnext t ht0] at hv
    linarith
  have hpsq : (p.roots.map fun z ↦ z ^ 2).sum = A + c * t := by
    have hmom := coeff_sub_two_eq_root_moments hpreal hpmonic
      (by simpa [hpdegree] using hd)
    rw [hpdegree, hpsum] at hmom
    have hcoeff : p.coeff (d - 2) =
        r.coeff (d - 2) + t * s.coeff (d - 2) := by
      simp [p, coeff_add, coeff_smul]
    rw [hcoeff] at hmom
    dsimp [A, c]
    linarith
  have hbound := sum_sq_roots_le_of_rootUpperBound
    hpreal hpmonic hub
  rw [hpdegree, hpsum] at hbound
  change (p.roots.map fun z ↦ z ^ 2).sum ≤ B at hbound
  rw [hpsq] at hbound
  have htlarge : (B - A) / c + 1 ≤ t := le_max_right _ _
  have hcne : c ≠ 0 := hc.ne'
  have hdiv : c * ((B - A) / c) = B - A := by
    field_simp
  nlinarith

/-- The sole topological root-motion lemma used in the proof of
Ravichandran--Srivastava Proposition 16.

The pencil `r + t s` has fixed degree and leading coefficient, is real-rooted
for every `t ≥ 0`, and has fixed root sum.  A negative `X^(d-2)` slope
makes its second root moment diverge.  Continuity of the largest root and the
fact that two distinct pencil members can share a root only when `r` and `s`
share it then force the largest root to move in the increasing direction. -/
def AffineRealRootedPencilLargestRootMonotoneFromMoment : Prop :=
  ∀ (d : ℕ) (r s : ℝ[X]), 2 ≤ d →
    (∀ t : ℝ, 0 ≤ t → (r + t • s).Monic) →
    (∀ t : ℝ, 0 ≤ t → (r + t • s).natDegree = d) →
    (∀ t : ℝ, 0 ≤ t → RealRooted (r + t • s)) →
    (∀ t : ℝ, 0 ≤ t → (r + t • s).nextCoeff = r.nextCoeff) →
    s.coeff (d - 2) < 0 →
    ∀ x : ℝ, IsRootUpperBound (r + s) x → IsRootUpperBound r x

/-- Global real-rootedness of the exact mixed determinantal polynomial for
finite Hermitian families.  The RS stable-polynomial construction supplies
this proposition independently of the root-motion argument. -/
def ExactMDPRealRootedness : Prop :=
  ∀ (n k : ℕ), 0 < k →
    ∀ (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
      (hA : ∀ a, (A a).IsHermitian),
      RealRooted (realMixedDeterminantalPolynomial A hA)

/-- The root-motion lemma is unconditional in degree two.  In this case the
fixed leading and next-to-leading coefficients force the direction polynomial
`s` to be a negative constant.  Hence every root of `r` lies strictly below
some root of `r + s`, which gives the desired upper-bound comparison directly. -/
theorem affineRealRootedPencilLargestRootMonotoneFromMoment_degree_two
    (r s : ℝ[X])
    (hmonic : ∀ t : ℝ, 0 ≤ t → (r + t • s).Monic)
    (hdegree : ∀ t : ℝ, 0 ≤ t → (r + t • s).natDegree = 2)
    (hreal : ∀ t : ℝ, 0 ≤ t → RealRooted (r + t • s))
    (hnext : ∀ t : ℝ, 0 ≤ t → (r + t • s).nextCoeff = r.nextCoeff)
    (hslope : s.coeff 0 < 0) (x : ℝ)
    (hx : IsRootUpperBound (r + s) x) : IsRootUpperBound r x := by
  have hrmonic : r.Monic := by simpa using hmonic 0 le_rfl
  have hpmonic : (r + s).Monic := by simpa using hmonic 1 zero_le_one
  have hrdeg : r.natDegree = 2 := by simpa using hdegree 0 le_rfl
  have hpdeg : (r + s).natDegree = 2 := by simpa using hdegree 1 zero_le_one
  have hpreal : RealRooted (r + s) := by simpa using hreal 1 zero_le_one
  have hcoeffTwo : s.coeff 2 = 0 := by
    have hr : r.coeff 2 = 1 := by simpa [hrdeg] using hrmonic.coeff_natDegree
    have hp : (r + s).coeff 2 = 1 := by simpa [hpdeg] using hpmonic.coeff_natDegree
    simpa [coeff_add, hr] using hp
  have hcoeffOne : s.coeff 1 = 0 := by
    have hn : (r + s).nextCoeff = r.nextCoeff := by
      simpa using hnext 1 zero_le_one
    have hrpos : 0 < r.natDegree := by omega
    have hppos : 0 < (r + s).natDegree := by omega
    rw [nextCoeff_of_natDegree_pos hppos, nextCoeff_of_natDegree_pos hrpos,
      hpdeg, hrdeg] at hn
    simpa [coeff_add] using hn
  have hsdeg : s.natDegree ≤ 0 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    by_cases hN1 : N = 1
    · simpa [hN1] using hcoeffOne
    by_cases hN2 : N = 2
    · simpa [hN2] using hcoeffTwo
    have hNgt : 2 < N := by omega
    have hsrepr : s = (r + s) - r := by module
    rw [hsrepr, coeff_sub,
      coeff_eq_zero_of_natDegree_lt (hpdeg.symm ▸ hNgt),
      coeff_eq_zero_of_natDegree_lt (hrdeg.symm ▸ hNgt), sub_zero]
  have hsconst : s = C (s.coeff 0) := eq_C_of_natDegree_le_zero hsdeg
  intro a ha
  have haeval : r.eval a = 0 := ha
  have hpeval : (r + s).eval a < 0 := by
    rw [eval_add, haeval, hsconst]
    simpa using hslope
  have hnot : ¬ IsRootUpperBound (r + s) a := by
    intro haub
    have hnonneg := hpreal.eval_nonneg_of_rootUpperBound hpmonic haub
    linarith
  rw [IsRootUpperBound] at hnot
  push Not at hnot
  obtain ⟨y, hyroot, hay⟩ := hnot
  exact (le_of_lt hay).trans (hx y hyroot)

/-- The single analytic monotonicity step, exactly Proposition 16 of the
reference: zeroing one matching row and column of a zero-diagonal member
cannot move the largest MDP root to the right. -/
def MDPOneCoordinateZeroingMonotonicity : Prop :=
  ∀ (n k : ℕ) (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (_hzd : ∀ a, ZeroDiag (A a))
    (a : Fin k)
    (i : Fin n) (x : ℝ),
    IsRootUpperBound (realMixedDeterminantalPolynomial A hA) x →
      IsRootUpperBound
        (realMixedDeterminantalPolynomial (zeroRowColFamily A a i)
          (zeroRowColFamily_isHermitian hA a i)) x

/-- Proposition 16 is elementary when the coordinate type is a singleton:
zero diagonal already forces the selected matrix to be zero. -/
theorem rootUpperBound_zeroRowColFamily_of_subsingleton
    {n k : ℕ} [Subsingleton (Fin n)]
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a))
    (a : Fin k) (i : Fin n) (x : ℝ)
    (hx : IsRootUpperBound (realMixedDeterminantalPolynomial A hA) x) :
    IsRootUpperBound
      (realMixedDeterminantalPolynomial (zeroRowColFamily A a i)
        (zeroRowColFamily_isHermitian hA a i)) x := by
  have hzero : A a = 0 := by
    ext r c
    have hrc : r = c := Subsingleton.elim r c
    subst c
    exact hzd a r
  have hfamily : zeroRowColFamily A a i = A := by
    funext b
    by_cases hba : b = a
    · subst b
      simp only [zeroRowColFamily, if_pos]
      rw [hzero]
      ext r c
      simp [zeroRowCol]
    · simp [zeroRowColFamily, hba]
  rw [realMixedDeterminantalPolynomial_congr _ _ _ _ hfamily]
  exact hx

/-- All algebraic and matrix-theoretic parts of RS Proposition 16: exact-MDP
real-rootedness plus the single abstract root-motion lemma imply one-coordinate
zeroing monotonicity. -/
theorem mdpOneCoordinateZeroingMonotonicity_of_rootMotion
    (hmotion : AffineRealRootedPencilLargestRootMonotoneFromMoment)
    (hrooted : ExactMDPRealRootedness) :
    MDPOneCoordinateZeroingMonotonicity := by
  intro n k A hA hzd a i x hx
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le a.1) a.2
  by_cases hn : 2 ≤ n
  · by_cases hi : ∃ j : Fin n, A a i j ≠ 0
    · let p0 := realMixedDeterminantalPolynomial (zeroRowColFamily A a i)
          (zeroRowColFamily_isHermitian hA a i)
      let p1 := realMixedDeterminantalPolynomial A hA
      let s := p1 - p0
      have haff : ∀ t : ℝ, 0 ≤ t →
          realMixedDeterminantalPolynomial (coordinateScaleFamily t A a i)
              (coordinateScaleFamily_isHermitian t hA a i) = p0 + t • s := by
        intro t ht
        simpa [p0, p1, s] using
          realMixedDeterminantalPolynomial_coordinateScaleFamily_eq_endpoints
            t ht A hA a i (hzd a i)
      have hmonic : ∀ t : ℝ, 0 ≤ t → (p0 + t • s).Monic := by
        intro t ht
        rw [← haff t ht]
        exact realMixedDeterminantalPolynomial_monic hk
          (coordinateScaleFamily t A a i)
          (coordinateScaleFamily_isHermitian t hA a i)
      have hdegree : ∀ t : ℝ, 0 ≤ t → (p0 + t • s).natDegree = n := by
        intro t ht
        rw [← haff t ht]
        exact realMixedDeterminantalPolynomial_natDegree hk
          (coordinateScaleFamily t A a i)
          (coordinateScaleFamily_isHermitian t hA a i)
      have hreal : ∀ t : ℝ, 0 ≤ t → RealRooted (p0 + t • s) := by
        intro t ht
        rw [← haff t ht]
        exact hrooted n k hk (coordinateScaleFamily t A a i)
          (coordinateScaleFamily_isHermitian t hA a i)
      have hnext : ∀ t : ℝ, 0 ≤ t →
          (p0 + t • s).nextCoeff = p0.nextCoeff := by
        intro t ht
        have hleft : (p0 + t • s).nextCoeff = 0 := by
          rw [← haff t ht]
          exact realMixedDeterminantalPolynomial_nextCoeff_eq_zero hk
            (coordinateScaleFamily t A a i)
            (coordinateScaleFamily_isHermitian t hA a i)
            (coordinateScaleFamily_zeroDiag t hzd a i)
        have hright : p0.nextCoeff = 0 := by
          dsimp [p0]
          exact realMixedDeterminantalPolynomial_nextCoeff_eq_zero hk
            (zeroRowColFamily A a i) (zeroRowColFamily_isHermitian hA a i)
            (zeroRowColFamily_zeroDiag hzd a i)
        rw [hleft, hright]
      have hslope : s.coeff (n - 2) < 0 := by
        simpa [s, p1, p0] using
          coordinateZeroingDirection_coeff_sub_two_neg hn hk A hA hzd a i hi
      have hp1 : p0 + s = p1 := by
        dsimp [s]
        module
      have hxin : IsRootUpperBound (p0 + s) x := by
        rw [hp1]
        exact hx
      change IsRootUpperBound p0 x
      exact hmotion n p0 s hn hmonic hdegree hreal hnext hslope x hxin
    · push Not at hi
      have hmatrix : zeroRowCol (A a) i = A a := by
        ext r c
        by_cases hr : r = i
        · subst r
          simp [zeroRowCol, hi c]
        · by_cases hc : c = i
          · subst c
            have hcol : A a r i = 0 := by
              rw [← (hA a).apply r i, hi r]
              simp
            simp [zeroRowCol, hr, hcol]
          · simp [zeroRowCol, hr, hc]
      have hfamily : zeroRowColFamily A a i = A := by
        funext b
        by_cases hba : b = a
        · subst b
          simpa [zeroRowColFamily] using hmatrix
        · simp [zeroRowColFamily, hba]
      rw [realMixedDeterminantalPolynomial_congr _ _ _ _ hfamily]
      exact hx
  · have hnle : n ≤ 1 := by omega
    letI : Subsingleton (Fin n) :=
      Fintype.card_le_one_iff_subsingleton.mp (by simpa using hnle)
    exact rootUpperBound_zeroRowColFamily_of_subsingleton A hA hzd a i x hx

/-- Set the first `s` rows and columns to zero. -/
def zeroPrefix {n : ℕ} (s : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ if i.1 < s ∨ j.1 < s then 0 else M i j

theorem zeroPrefix_isHermitian {n s : ℕ}
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    (zeroPrefix s M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hi : i.1 < s <;> by_cases hj : j.1 < s <;>
    simp [zeroPrefix, hi, hj, hM.apply]

theorem zeroPrefix_zeroDiag {n s : ℕ}
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : ZeroDiag M) :
    ZeroDiag (zeroPrefix s M) := by
  intro i
  by_cases hi : i.1 < s
  · simp [zeroPrefix, hi]
  · simp [zeroPrefix, hi, hM i]

private theorem zeroRowCol_zeroPrefix {n s : ℕ} (hs : s < n)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    zeroRowCol (zeroPrefix s M) ⟨s, hs⟩ = zeroPrefix (s + 1) M := by
  ext i j
  simp only [zeroRowCol, zeroPrefix]
  have hcond :
      (i = ⟨s, hs⟩ ∨ j = ⟨s, hs⟩) ∨ (i.1 < s ∨ j.1 < s) ↔
        i.1 < s + 1 ∨ j.1 < s + 1 := by
    constructor
    · rintro ((hi | hj) | (hi | hj))
      · left
        subst i
        simp
      · right
        subst j
        simp
      · exact Or.inl (hi.trans_le (Nat.le_add_right s 1))
      · exact Or.inr (hj.trans_le (Nat.le_add_right s 1))
    · rintro (hi | hj)
      · by_cases his : i.1 < s
        · exact Or.inr (Or.inl his)
        · left
          left
          apply Fin.ext
          simp
          omega
      · by_cases hjs : j.1 < s
        · exact Or.inr (Or.inr hjs)
        · left
          right
          apply Fin.ext
          simp
          omega
  by_cases houter : i = ⟨s, hs⟩ ∨ j = ⟨s, hs⟩
  · have hrhs := hcond.mp (Or.inl houter)
    rw [if_pos houter, if_pos hrhs]
  · by_cases hinner : i.1 < s ∨ j.1 < s
    · have hrhs := hcond.mp (Or.inr hinner)
      rw [if_neg houter, if_pos hinner, if_pos hrhs]
    · have hrhs : ¬ (i.1 < s + 1 ∨ j.1 < s + 1) := by
        intro h
        exact (hcond.mpr h).elim houter hinner
      rw [if_neg houter, if_neg hinner, if_neg hrhs]

/-- Set a prefix of coordinates to zero in one selected family member. -/
def zeroPrefixFamily {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin k) (s : ℕ) :
    Fin k → Matrix (Fin n) (Fin n) ℂ :=
  fun b ↦ if b = a then zeroPrefix s (A b) else A b

theorem zeroPrefixFamily_isHermitian {n k s : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ a, (A a).IsHermitian) (a : Fin k) :
    ∀ b, (zeroPrefixFamily A a s b).IsHermitian := by
  intro b
  by_cases hba : b = a
  · subst b
    simp only [zeroPrefixFamily, if_pos]
    exact zeroPrefix_isHermitian (hA a)
  · simp [zeroPrefixFamily, hba, hA b]

theorem zeroPrefixFamily_zeroDiag {n k s : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ a, ZeroDiag (A a)) (a : Fin k) :
    ∀ b, ZeroDiag (zeroPrefixFamily A a s b) := by
  intro b
  by_cases hba : b = a
  · subst b
    simpa [zeroPrefixFamily] using zeroPrefix_zeroDiag (s := s) (hA a)
  · simpa [zeroPrefixFamily, hba] using hA b

private theorem zeroRowColFamily_zeroPrefixFamily {n k s : ℕ}
    (hs : s < n) (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin k) :
    zeroRowColFamily (zeroPrefixFamily A a s) a ⟨s, hs⟩ =
      zeroPrefixFamily A a (s + 1) := by
  funext b
  by_cases hba : b = a
  · subst b
    simp only [zeroRowColFamily, zeroPrefixFamily, if_pos]
    exact zeroRowCol_zeroPrefix hs (A a)
  · simp [zeroRowColFamily, zeroPrefixFamily, hba]

/-- Replace one member of a family by the zero matrix. -/
def zeroMember {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin k) :
    Fin k → Matrix (Fin n) (Fin n) ℂ :=
  fun b ↦ if b = a then 0 else A b

theorem zeroMember_isHermitian {n k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ a, (A a).IsHermitian) (a : Fin k) :
    ∀ b, (zeroMember A a b).IsHermitian := by
  intro b
  by_cases hba : b = a
  · simp [zeroMember, hba]
  · simp [zeroMember, hba, hA b]

private theorem zeroPrefixFamily_dim_eq_zeroMember {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin k) :
    zeroPrefixFamily A a n = zeroMember A a := by
  funext b
  by_cases hba : b = a
  · subst b
    ext i j
    simp [zeroPrefixFamily, zeroMember, zeroPrefix, i.isLt]
  · simp [zeroPrefixFamily, zeroMember, hba]

/-- Iterating Proposition 16 through every coordinate replaces one
zero-diagonal member by zero without increasing the largest root. -/
theorem rootUpperBound_zeroMember_of_oneCoordinate
    (hone : MDPOneCoordinateZeroingMonotonicity)
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a))
    (a : Fin k)
    (x : ℝ) (hx : IsRootUpperBound
      (realMixedDeterminantalPolynomial A hA) x) :
    IsRootUpperBound
      (realMixedDeterminantalPolynomial (zeroMember A a)
        (zeroMember_isHermitian hA a)) x := by
  have hprefix : ∀ s : ℕ, s ≤ n →
      IsRootUpperBound
        (realMixedDeterminantalPolynomial (zeroPrefixFamily A a s)
          (zeroPrefixFamily_isHermitian hA a)) x := by
    intro s hs
    induction s with
    | zero =>
        have hfamily : zeroPrefixFamily A a 0 = A := by
          funext b
          by_cases hba : b = a
          · subst b
            ext i j
            simp [zeroPrefixFamily, zeroPrefix]
          · simp [zeroPrefixFamily, hba]
        rw [realMixedDeterminantalPolynomial_congr _ _ _ _ hfamily]
        exact hx
    | succ s ih =>
        have hslt : s < n := by omega
        have hprev := ih (by omega)
        let As := zeroPrefixFamily A a s
        let hAs : ∀ b, (As b).IsHermitian := zeroPrefixFamily_isHermitian hA a
        have hzAs : ∀ b, ZeroDiag (As b) := zeroPrefixFamily_zeroDiag hzd a
        have hstep := hone n k As hAs hzAs a ⟨s, hslt⟩ x hprev
        have hfamily : zeroRowColFamily As a ⟨s, hslt⟩ =
            zeroPrefixFamily A a (s + 1) := by
          exact zeroRowColFamily_zeroPrefixFamily hslt A a
        rw [realMixedDeterminantalPolynomial_congr _ _ _ _ hfamily] at hstep
        simpa [Nat.succ_eq_add_one] using hstep
  have hfinal := hprefix n le_rfl
  have hfamily := zeroPrefixFamily_dim_eq_zeroMember A a
  rw [realMixedDeterminantalPolynomial_congr _ _ _ _ hfamily] at hfinal
  exact hfinal

/-- Replace every member indexed by `S` with zero. -/
def zeroMembers {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (S : Finset (Fin k)) :
    Fin k → Matrix (Fin n) (Fin n) ℂ :=
  fun a ↦ if a ∈ S then 0 else A a

theorem zeroMembers_isHermitian {n k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ a, (A a).IsHermitian) (S : Finset (Fin k)) :
    ∀ a, (zeroMembers A S a).IsHermitian := by
  intro a
  by_cases ha : a ∈ S
  · simp [zeroMembers, ha]
  · simp [zeroMembers, ha, hA a]

theorem zeroMembers_zeroDiag {n k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ a, ZeroDiag (A a)) (S : Finset (Fin k)) :
    ∀ a, ZeroDiag (zeroMembers A S a) := by
  intro a
  by_cases ha : a ∈ S
  · simp [zeroMembers, ha, ZeroDiag]
  · simpa [zeroMembers, ha] using hA a

private theorem zeroMember_zeroMembers {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (S : Finset (Fin k))
    {a : Fin k} :
    zeroMember (zeroMembers A S) a = zeroMembers A (insert a S) := by
  funext b
  by_cases hba : b = a
  · subst b
    simp [zeroMember, zeroMembers]
  · by_cases hbS : b ∈ S <;>
      simp [zeroMember, zeroMembers, hba, hbS]

/-- Finite iteration of the one-member theorem. -/
theorem rootUpperBound_zeroMembers_of_oneCoordinate
    (hone : MDPOneCoordinateZeroingMonotonicity)
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a))
    (S : Finset (Fin k)) (x : ℝ)
    (hx : IsRootUpperBound (realMixedDeterminantalPolynomial A hA) x) :
    IsRootUpperBound
      (realMixedDeterminantalPolynomial (zeroMembers A S)
        (zeroMembers_isHermitian hA S)) x := by
  induction S using Finset.induction_on with
  | empty => simpa [zeroMembers] using hx
  | @insert a S ha ih =>
      have hprev := ih
      have htarget : ∀ b, ZeroDiag (zeroMembers A S b) :=
        zeroMembers_zeroDiag hzd S
      have hstep := rootUpperBound_zeroMember_of_oneCoordinate hone
        (zeroMembers A S) (zeroMembers_isHermitian hA S) htarget a x hprev
      have hfamily := zeroMember_zeroMembers A S (a := a)
      rw [realMixedDeterminantalPolynomial_congr _ _ _ _ hfamily] at hstep
      exact hstep

private theorem zeroMembers_erase_eq_singleMatrixFamily {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a₀ : Fin k) :
    zeroMembers A (Finset.univ.erase a₀) = singleMatrixFamily a₀ (A a₀) := by
  funext a
  by_cases ha : a = a₀
  · subst a
    simp [zeroMembers, singleMatrixFamily]
  · simp [zeroMembers, singleMatrixFamily, ha]

/-- The spectral monotonicity still required for joint control, stated in the
root-upper-bound direction used by the selection argument.  The zero-diagonal
hypothesis is essential and is the one present in the reference theorem. -/
def MDPJointRootMonotonicity : Prop :=
  ∀ (n k : ℕ) (_hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (_hzd : ∀ a, ZeroDiag (A a))
    (a₀ : Fin k) (x : ℝ),
    IsRootUpperBound (realMixedDeterminantalPolynomial A hA) x →
      IsRootUpperBound
        (realMixedDeterminantalPolynomial (singleMatrixFamily a₀ (A a₀))
          (singleMatrixFamily_isHermitian a₀ (hA a₀))) x

/-- Ravichandran--Srivastava Theorem 15, and hence joint control, follows by
finite iteration from their one-coordinate Proposition 16. -/
theorem mdpJointRootMonotonicity_of_oneCoordinate
    (hone : MDPOneCoordinateZeroingMonotonicity) :
    MDPJointRootMonotonicity := by
  intro n k _hk A hA hzd a₀ x hx
  have hzeroed := rootUpperBound_zeroMembers_of_oneCoordinate
    hone A hA hzd (Finset.univ.erase a₀) x hx
  have hfamily := zeroMembers_erase_eq_singleMatrixFamily A a₀
  rw [realMixedDeterminantalPolynomial_congr _ _ _ _ hfamily] at hzeroed
  exact hzeroed

/-- The closed form turns an MDP root bound into the expected factor-`k`
ordinary characteristic-polynomial root bound. -/
theorem realCharpoly_rootUpperBound_of_singleMatrixMDP
    {n k : ℕ} (hk : 0 < k) (a₀ : Fin k)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) {x : ℝ}
    (hx : IsRootUpperBound
      (realMixedDeterminantalPolynomial (singleMatrixFamily a₀ A)
        (singleMatrixFamily_isHermitian a₀ hA)) x) :
    IsRootUpperBound (realCharpoly A hA) ((k : ℝ) * x) := by
  intro r hr
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hreval : (realCharpoly A hA).eval r = 0 := hr
  have hrootScaled :
      (normalizedScaledRealCharpoly k A hA).IsRoot (r / (k : ℝ)) := by
    have hk0 : (k : ℝ) ≠ 0 := hkR.ne'
    have harg : (k : ℝ) * (r / (k : ℝ)) = r := by
      field_simp
    rw [Polynomial.IsRoot, normalizedScaledRealCharpoly, Polynomial.eval_smul,
      scaleVariable, Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, harg, hreval,
      smul_zero]
  have hrootMDP :
      (realMixedDeterminantalPolynomial (singleMatrixFamily a₀ A)
        (singleMatrixFamily_isHermitian a₀ hA)).IsRoot (r / (k : ℝ)) := by
    rw [singleMatrixMDP_closedForm n k hk a₀ A hA]
    exact hrootScaled
  have hry : r / (k : ℝ) ≤ x := hx _ hrootMDP
  simpa [mul_comm] using (div_le_iff₀ hkR).mp hry

/-- Consequently, the closed form plus the one explicit monotonicity property
give simultaneous factor-`k` spectral control for every member of a family. -/
theorem joint_realCharpoly_rootUpperBound_of_MDP
    (hmono : MDPJointRootMonotonicity)
    {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a)) {x : ℝ}
    (hx : IsRootUpperBound (realMixedDeterminantalPolynomial A hA) x) :
    ∀ a : Fin k, IsRootUpperBound (realCharpoly (A a) (hA a)) ((k : ℝ) * x) := by
  intro a
  exact realCharpoly_rootUpperBound_of_singleMatrixMDP hk a (A a) (hA a)
    (hmono n k hk A hA hzd a x hx)

end CommutatorTheorem.BTMDPJointControl
