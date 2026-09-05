import NoEpsilon.MSSFlatten
import NoEpsilon.MSSInterlacing
import NoEpsilon.MSSSpecialization
import NoEpsilon.MSSRealPencil

/-!
# Characteristic polynomials of finite rank-one ensembles

The algebraic mixed-characteristic formula and the stability of a Hermitian affine
pencil are connected here. The deterministic Hermitian base matrix is retained for
the conditional-expectation recursion.
-/

namespace NoEpsilon.MSSCharpoly

set_option maxHeartbeats 800000

open Polynomial NoEpsilon.MSSStability NoEpsilon.MSSExpectation
open CommutatorTheorem CommutatorTheorem.BTMDPSelection
open scoped BigOperators Polynomial ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- A Hermitian constant term does not affect the positive imaginary quadratic form
of a positive semidefinite pencil. -/
theorem det_hermitian_affine_pencil_ne_zero (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hTotal : (∑ i, A i).PosDef) (z : κ → ℂ) (hz : ∀ i, 0 < (z i).im) :
    (B + ∑ i, z i • A i).det ≠ 0 := by
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
  have hBim : (star v ⬝ᵥ B.mulVec v).im = 0 := hB.im_star_dotProduct_mulVec_self v
  have him : (star v ⬝ᵥ ((B + ∑ i, z i • A i).mulVec v)).im =
      ∑ i, (z i).im * (q i).re := by
    simp only [Matrix.add_mulVec, dotProduct_add, Complex.add_im,
      hBim, zero_add, Matrix.sum_mulVec, dotProduct_sum,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.im_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (z i * q i).im = _
    rw [Complex.mul_im, hqi, mul_zero, zero_add]
  rw [hker, dotProduct_zero] at him
  simp only [Complex.zero_im] at him
  linarith

/-- The complex affine determinant pencil is upper stable. -/
theorem hermitian_affine_pencil_upperStable (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hTotal : (∑ i, A i).PosDef) :
    UpperStable ((B.map MvPolynomial.C : Matrix ι ι (MvPolynomial κ ℂ)) +
      ∑ i, (MvPolynomial.X i : MvPolynomial κ ℂ) •
        ((A i).map MvPolynomial.C : Matrix ι ι (MvPolynomial κ ℂ))).det := by
  intro z hz
  rw [RingHom.map_det]
  have heq :
      (B.map MvPolynomial.C + ∑ i, (MvPolynomial.X i : MvPolynomial κ ℂ) •
        (A i).map MvPolynomial.C).map (MvPolynomial.eval z) = B + ∑ i, z i • A i := by
    ext i j
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply]
  rw [show (MvPolynomial.eval z).mapMatrix _ = _ from heq]
  exact det_hermitian_affine_pencil_ne_zero B hB A hA hTotal z hz

/-- Stability of the flat sequence of MSS differential operators. -/
theorem mixedDifference_upperStable {σ : Type*} [Finite σ]
    (xs : List σ) {p : MvPolynomial σ ℂ} (hp : UpperStable p) :
    UpperStable (mixedDifference xs p) := by
  induction xs with
  | nil => exact hp
  | cons i xs ih => exact ih.sub_pderiv i

/-- The characteristic polynomial identity for all finite independent rank-one laws,
with an arbitrary deterministic base matrix. -/
theorem expected_charpoly_eq_flatMixedDet {R Ω : Type*} [CommRing R] [Fintype Ω]
    (n : ℕ) (B : Matrix ι ι R) (u v : Fin n → Ω → ι → R)
    (p : Fin n → Ω → R) (hp : ∀ i, ∑ ω, p i ω = 1) :
    (∑ q : Fin n → Ω, Polynomial.C (∏ i, p i (q i)) *
      (B + ∑ i, Matrix.vecMulVec (u i (q i)) (v i (q i))).charpoly) =
      flatMixedDet n B.charmatrix
        (fun i ↦ (∑ ω, p i ω • Matrix.vecMulVec (u i ω) (v i ω)).map Polynomial.C) := by
  let C : R →+* R[X] := Polynomial.C
  have hc (i : Fin n) :
      (∑ ω, p i ω • Matrix.vecMulVec (u i ω) (v i ω)).map C =
        ∑ ω, C (p i ω) •
          Matrix.vecMulVec (fun j ↦ C (u i ω j)) (fun j ↦ C (v i ω j)) :=
    map_covariance C (u i) (v i) (p i)
  change _ = flatMixedDet n B.charmatrix
    (fun i ↦ (∑ ω, p i ω • Matrix.vecMulVec (u i ω) (v i ω)).map C)
  simp_rw [hc]
  have h := expected_determinant_eq_flatMixedDet n B.charmatrix
    (fun i ω j ↦ C (u i ω j)) (fun i ω j ↦ C (v i ω j))
    (fun i ω ↦ C (p i ω)) (fun i ↦ by simp only [← map_sum, hp, map_one])
  rw [← h]
  apply Finset.sum_congr rfl
  intro q _
  rw [← map_prod]
  congr 1
  unfold Matrix.charpoly
  congr 1
  apply Matrix.ext
  intro i j
  simp [Matrix.charmatrix, C, Matrix.map_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.sum_apply, Matrix.vecMulVec]
  ring

section CharacteristicSpecialization

variable {R σ : Type*} [CommRing R]

/-- Regard the distinguished coordinate as the univariate coefficient variable. -/
noncomputable def optionToIter : MvPolynomial (Option σ) R →+* MvPolynomial σ R[X] :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp Polynomial.C)
    (fun o ↦ o.elim (MvPolynomial.C Polynomial.X) MvPolynomial.X)

@[simp] theorem optionToIter_C (a : R) :
    optionToIter (σ := σ) (MvPolynomial.C a) = MvPolynomial.C (Polynomial.C a) := by
  simp [optionToIter]

@[simp] theorem optionToIter_X_none :
    optionToIter (MvPolynomial.X none : MvPolynomial (Option σ) R) =
      MvPolynomial.C Polynomial.X := by simp [optionToIter]

@[simp] theorem optionToIter_X_some (i : σ) :
    optionToIter (MvPolynomial.X (some i) : MvPolynomial (Option σ) R) =
      MvPolynomial.X i := by simp [optionToIter]

/-- Only the nondistinguished variables are differentiated by MSS. -/
theorem pderiv_optionToIter (i : σ) (p : MvPolynomial (Option σ) R) :
    MvPolynomial.pderiv i (optionToIter p) =
      optionToIter (MvPolynomial.pderiv (some i) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    cases j with
    | none => simp [hp]
    | some j =>
      by_cases h : j = i
      · subst j; simp [hp]
      · simp [hp, h]

theorem mixedDifference_optionToIter (xs : List σ) (p : MvPolynomial (Option σ) R) :
    mixedDifference xs (optionToIter p) =
      optionToIter (mixedDifference (xs.map some) p) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [mixedDifference, List.foldr_cons, List.map_cons] at ih ⊢
    rw [ih, pderiv_optionToIter, map_sub]

/-- Setting the nondistinguished variables to zero leaves the coordinate polynomial. -/
theorem eval_zero_optionToIter [DecidableEq σ] (p : MvPolynomial (Option σ) R) :
    MvPolynomial.eval (fun _ ↦ (0 : R[X])) (optionToIter p) =
      MSSSpecialization.coordinatePolynomial p (fun _ ↦ 0) none := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MSSSpecialization.coordinatePolynomial]
  | add p q hp hq =>
    simpa [MSSSpecialization.coordinatePolynomial] using congrArg₂ (· + ·) hp hq
  | mul_X p j hp =>
    cases j with
    | none =>
      simpa [MSSSpecialization.coordinatePolynomial] using congrArg (· * Polynomial.X) hp
    | some j => simp [MSSSpecialization.coordinatePolynomial]

/-- The full characteristic pencil, with its spectral variable distinguished. -/
noncomputable def characteristicPencil (n : ℕ) (B : Matrix ι ι R)
    (A : Fin n → Matrix ι ι R) : MvPolynomial (Option (Fin n)) R :=
  (((-B).map MvPolynomial.C : Matrix ι ι (MvPolynomial (Option (Fin n)) R)) +
    ∑ i : Option (Fin n), (MvPolynomial.X i : MvPolynomial (Option (Fin n)) R) •
      ((i.elim 1 A).map MvPolynomial.C :
        Matrix ι ι (MvPolynomial (Option (Fin n)) R))).det

/-- Moving the spectral variable into the coefficient ring gives the characteristic matrix. -/
theorem optionToIter_characteristicPencil (n : ℕ) (B : Matrix ι ι R)
    (A : Fin n → Matrix ι ι R) :
    optionToIter (characteristicPencil n B A) =
      affinePencil n B.charmatrix (fun i ↦ (A i).map Polynomial.C) := by
  unfold characteristicPencil affinePencil
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_sum, map_mul, map_neg, Fintype.sum_option, Option.elim,
    optionToIter_C, optionToIter_X_none, optionToIter_X_some]
  simp [Matrix.charmatrix, Matrix.map_apply, Matrix.sub_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs
  · ring
  · rw [MvPolynomial.C_0]
    ring

/-- The flat mixed characteristic polynomial is the spectral coordinate restriction
of the stable multivariate differential polynomial. -/
theorem flatMixedDet_charmatrix_eq_coordinate (n : ℕ) (B : Matrix ι ι R)
    (A : Fin n → Matrix ι ι R) :
    flatMixedDet n B.charmatrix (fun i ↦ (A i).map Polynomial.C) =
      MSSSpecialization.coordinatePolynomial
        (mixedDifference ((List.finRange n).map some) (characteristicPencil n B A))
        (fun _ ↦ 0) none := by
  unfold flatMixedDet
  rw [← optionToIter_characteristicPencil, mixedDifference_optionToIter,
    eval_zero_optionToIter]

end CharacteristicSpecialization

/-- The spectral variable contributes the identity, so no nondegeneracy condition
on the sum of the covariance matrices is necessary. -/
theorem characteristicPencil_upperStable (n : ℕ) (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (A : Fin n → Matrix ι ι ℂ)
    (hA : ∀ i, (A i).PosSemidef) : UpperStable (characteristicPencil n B A) := by
  unfold characteristicPencil
  apply hermitian_affine_pencil_upperStable (-B) hB.neg
    (fun i : Option (Fin n) ↦ i.elim 1 A)
  · intro i
    cases i with
    | none => exact Matrix.PosSemidef.one
    | some i => exact hA i
  · simp only [Fintype.sum_option, Option.elim]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_sum _ (fun i _ ↦ hA i))

/-- Upper stability of the full differential polynomial underlying an arbitrary
finite conditional expected characteristic polynomial. -/
theorem characteristic_mixedDifference_upperStable (n : ℕ) (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (A : Fin n → Matrix ι ι ℂ)
    (hA : ∀ i, (A i).PosSemidef) :
    UpperStable (mixedDifference ((List.finRange n).map some) (characteristicPencil n B A)) :=
  mixedDifference_upperStable _ (characteristicPencil_upperStable n B hB A hA)

section RealExpectedPolynomial

variable {Ω : Type*} [Fintype Ω]

/-- The rank-one sum at a fixed outcome is Hermitian. -/
theorem outcome_isHermitian (n : ℕ) (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (v : Fin n → Ω → ι → ℂ) (q : Fin n → Ω) :
    (B + ∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i)))).IsHermitian :=
  hB.add (Matrix.posSemidef_sum _
    (fun i _ ↦ Matrix.posSemidef_vecMulVec_self_star (v i (q i)))).1

/-- A finite expected characteristic polynomial over the real coefficient field. -/
noncomputable def realExpectedCharpoly (n : ℕ) (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (v : Fin n → Ω → ι → ℂ) (p : Fin n → Ω → ℝ) : ℝ[X] :=
  ∑ q : Fin n → Ω, (∏ i, p i (q i)) •
    realCharpoly (B + ∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i))))
      (outcome_isHermitian n B hB v q)

/-- Independent product weights remain normalized. -/
theorem sum_product_weights {S : Type*} [CommSemiring S]
    (n : ℕ) (p : Fin n → Ω → S) (hp : ∀ i, ∑ ω, p i ω = 1) :
    (∑ q : Fin n → Ω, ∏ i, p i (q i)) = 1 := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset Ω)) p
  simpa only [hp, Finset.prod_const_one, Fintype.piFinset_univ] using h.symm

/-- The finite expected polynomial is monic of exactly the original matrix dimension. -/
theorem realExpectedCharpoly_monic_natDegree (n : ℕ) (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (v : Fin n → Ω → ι → ℂ) (p : Fin n → Ω → ℝ)
    (hp : ∀ i, ∑ ω, p i ω = 1) :
    (realExpectedCharpoly n B hB v p).Monic ∧
      (realExpectedCharpoly n B hB v p).natDegree = Fintype.card ι := by
  apply MSSInterlacing.weightedSum_monic_natDegree _ _ _ (sum_product_weights n p hp)
  · intro q; exact realCharpoly_monic _ _
  · intro q; exact realCharpoly_natDegree _ _

/-- Complexification is the ordinary expected characteristic polynomial. -/
theorem map_realExpectedCharpoly (n : ℕ) (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (v : Fin n → Ω → ι → ℂ) (p : Fin n → Ω → ℝ) :
    (realExpectedCharpoly n B hB v p).map Complex.ofRealHom =
      ∑ q : Fin n → Ω, Polynomial.C (∏ i, (p i (q i) : ℂ)) *
        (B + ∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i)))).charpoly := by
  unfold realExpectedCharpoly
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Polynomial.map_smul, realCharpoly_map_complex]
  simp only [Polynomial.smul_eq_C_mul, map_prod, Complex.ofRealHom_eq_coe]

/-- The expected real polynomial is precisely the spectral coordinate restriction
of the mean-covariance differential pencil. -/
theorem map_realExpectedCharpoly_eq_coordinate (n : ℕ) (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (v : Fin n → Ω → ι → ℂ) (p : Fin n → Ω → ℝ)
    (hp : ∀ i, ∑ ω, p i ω = 1) :
    (realExpectedCharpoly n B hB v p).map Complex.ofRealHom =
      MSSSpecialization.coordinatePolynomial
        (mixedDifference ((List.finRange n).map some) (characteristicPencil n B
          (fun i ↦ ∑ ω, (p i ω : ℂ) • Matrix.vecMulVec (v i ω) (star (v i ω)))))
        (fun _ ↦ 0) none := by
  rw [map_realExpectedCharpoly]
  have hsum : ∀ i, ∑ ω, (p i ω : ℂ) = 1 := fun i ↦ by exact_mod_cast hp i
  rw [expected_charpoly_eq_flatMixedDet n B v (fun i ω ↦ star (v i ω))
    (fun i ω ↦ (p i ω : ℂ)) hsum]
  exact flatMixedDet_charmatrix_eq_coordinate n B _

/-- Every finite independent rank-one expected characteristic polynomial is real-rooted,
also after adding any fixed Hermitian matrix. This theorem has no interlacing premise. -/
theorem realExpectedCharpoly_realRooted (n : ℕ) (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (v : Fin n → Ω → ι → ℂ) (p : Fin n → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1) :
    RealRooted (realExpectedCharpoly n B hB v p) := by
  let A : Fin n → Matrix ι ι ℂ :=
    fun i ↦ ∑ ω, (p i ω : ℂ) • Matrix.vecMulVec (v i ω) (star (v i ω))
  have hA : ∀ i, (A i).PosSemidef := by
    intro i
    apply Matrix.posSemidef_sum
    intro ω _
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul
      (show (0 : ℂ) ≤ (p i ω : ℂ) from by exact_mod_cast hp i ω)
  have hstable := characteristic_mixedDifference_upperStable n B hB A hA
  have heq := map_realExpectedCharpoly_eq_coordinate n B hB v p hsum
  have hne : (realExpectedCharpoly n B hB v p).map Complex.ofRealHom ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr
      (realExpectedCharpoly_monic_natDegree n B hB v p hsum).1.ne_zero
  apply MSSSpecialization.splits_of_complexification_upperStable
  rw [heq]
  apply MSSSpecialization.coordinatePolynomial_upperStable hstable (fun _ ↦ 0) none
  simpa only [A, Complex.ofReal_zero, ← heq] using hne

end RealExpectedPolynomial

end NoEpsilon.MSSCharpoly
