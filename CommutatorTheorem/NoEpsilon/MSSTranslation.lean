import CommutatorTheorem.NoEpsilon.MSSCharpoly

/-!
# Translating the mixed-characteristic formula to the MSS barrier pencil

When the covariances sum to the identity, adding `x I` to the base matrix is
simultaneous translation of every covariance variable by `x`.
-/

namespace NoEpsilon.MSSTranslation

open NoEpsilon.MSSExpectation NoEpsilon.MSSCharpoly
open scoped BigOperators Polynomial

variable {R σ : Type*} [CommRing R]

/-- Translation by the same scalar in every variable. -/
noncomputable def translateAll (x : R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ MvPolynomial.X i + MvPolynomial.C x)

@[simp] theorem translateAll_C (x a : R) :
    translateAll (σ := σ) x (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [translateAll]

@[simp] theorem translateAll_X (x : R) (i : σ) :
    translateAll x (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C x := by
  simp [translateAll]

/-- Constant translations commute with every partial derivative. -/
theorem pderiv_translateAll (x : R) (i : σ) (p : MvPolynomial σ R) :
    MvPolynomial.pderiv i (translateAll x p) =
      translateAll x (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    by_cases h : j = i
    · subst j; simp [hp, mul_add, add_mul]; ring
    · simp [hp, h, mul_add, add_mul]

theorem mixedDifference_translateAll (x : R) (xs : List σ) (p : MvPolynomial σ R) :
    mixedDifference xs (translateAll x p) = translateAll x (mixedDifference xs p) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [mixedDifference, List.foldr_cons] at ih ⊢
    rw [ih, pderiv_translateAll, map_sub]

/-- Evaluation at zero after translation is diagonal evaluation at the translation scalar. -/
theorem eval_zero_translateAll (x : R) (p : MvPolynomial σ R) :
    MvPolynomial.eval (fun _ ↦ (0 : R)) (translateAll x p) =
      MvPolynomial.eval (fun _ ↦ x) p := by
  have h : (MvPolynomial.eval (fun _ : σ ↦ (0 : R))).comp (translateAll x) =
      MvPolynomial.eval (fun _ : σ ↦ x) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp
  exact RingHom.congr_fun h p

/-- The flat operator uses the reverse list for the iterative barrier convention. -/
theorem mixedDifference_eq_foldl_reverse (xs : List σ) (p : MvPolynomial σ R) :
    mixedDifference xs p = xs.reverse.foldl (fun q i ↦ q - MvPolynomial.pderiv i q) p := by
  simp only [mixedDifference, List.foldr_eq_foldl_reverse]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Translation of the PSD pencil adds the scalar multiple of the total covariance. -/
theorem translateAll_psdPencil (n : ℕ) (A : Fin n → Matrix ι ι ℂ) (x : ℂ) :
    translateAll x (MSSStability.psdPencil A) =
      affinePencil n (x • ∑ i, A i) A := by
  unfold MSSStability.psdPencil affinePencil
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, Finset.mul_sum, Finset.sum_add_distrib, add_mul]
  ring

/-- The expected-characteristic flat determinant is the diagonal differential pencil. -/
theorem flatMixedDet_smul_sum (n : ℕ) (A : Fin n → Matrix ι ι ℂ) (x : ℂ) :
    flatMixedDet n (x • ∑ i, A i) A =
      MvPolynomial.eval (fun _ ↦ x)
        ((List.finRange n).reverse.foldl (fun q i ↦ q - MvPolynomial.pderiv i q)
          (MSSStability.psdPencil A)) := by
  unfold flatMixedDet
  rw [← translateAll_psdPencil, mixedDifference_translateAll, eval_zero_translateAll,
    mixedDifference_eq_foldl_reverse]

/-- Scalar evaluation of the expected characteristic polynomial agrees with the
original determinant expectation, with arbitrary fixed Hermitian base. -/
theorem eval_map_realExpectedCharpoly {Ω : Type*} [Fintype Ω]
    (n : ℕ) (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (v : Fin n → Ω → ι → ℂ) (p : Fin n → Ω → ℝ)
    (hp : ∀ i, ∑ ω, p i ω = 1) (x : ℂ) :
    ((realExpectedCharpoly n B hB v p).map Complex.ofRealHom).eval x =
      flatMixedDet n (Matrix.scalar ι x - B)
        (fun i ↦ ∑ ω, (p i ω : ℂ) • Matrix.vecMulVec (v i ω) (star (v i ω))) := by
  rw [map_realExpectedCharpoly]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Matrix.eval_charpoly]
  have hsum : ∀ i, ∑ ω, (p i ω : ℂ) = 1 := fun i ↦ by exact_mod_cast hp i
  rw [← expected_determinant_eq_flatMixedDet n (Matrix.scalar ι x - B) v
    (fun i ω ↦ star (v i ω)) (fun i ω ↦ (p i ω : ℂ)) hsum]
  apply Finset.sum_congr rfl
  intro q _
  congr 2
  abel

/-- Under identity covariance, the expected characteristic polynomial is exactly
the diagonal polynomial bounded by the MSS barrier theorem. -/
theorem eval_expected_eq_psdPencil {Ω : Type*} [Fintype Ω]
    (n : ℕ) (v : Fin n → Ω → ι → ℂ) (p : Fin n → Ω → ℝ)
    (hp : ∀ i, ∑ ω, p i ω = 1)
    (hTotal : (∑ i, ∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))) = 1) (x : ℂ) :
    ((realExpectedCharpoly n 0 Matrix.isHermitian_zero v p).map Complex.ofRealHom).eval x =
      MvPolynomial.eval (fun _ ↦ x)
        ((List.finRange n).reverse.foldl (fun q i ↦ q - MvPolynomial.pderiv i q)
          (MSSStability.psdPencil
            (fun i ↦ ∑ ω, (p i ω : ℂ) • Matrix.vecMulVec (v i ω) (star (v i ω))))) := by
  rw [eval_map_realExpectedCharpoly n 0 Matrix.isHermitian_zero v p hp x, sub_zero,
    ← flatMixedDet_smul_sum, hTotal]
  congr 1
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

end NoEpsilon.MSSTranslation
