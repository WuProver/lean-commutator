import CommutatorTheorem.NoEpsilon.MSSSelection
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Rank-one determinant identities for the MSS mixed characteristic polynomial

This file proves determinant identities directly over arbitrary commutative rings.
No MSS selection statement is assumed. These are the algebraic input for a future
mixed-characteristic-polynomial and multivariate-barrier proof.
-/

namespace NoEpsilon
namespace MixedCharacteristic

open scoped BigOperators

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Adding a rank-one matrix is affine in its row coefficients. The proof removes the
coefficients one by one; all terms with two proportional replacement rows vanish. -/
theorem det_add_vecMulVec_of_support (s : Finset ι) (A : Matrix ι ι R)
    (u v : ι → R) (hu : ∀ i, i ∉ s → u i = 0) :
    (A + Matrix.vecMulVec u v).det = A.det + ∑ i ∈ s, u i * (A.updateRow i v).det := by
  classical
  induction s using Finset.induction_on generalizing u with
  | empty =>
    have hz : u = 0 := funext (fun i ↦ hu i (by simp))
    have hzero : Matrix.vecMulVec u v = 0 := by ext i j; simp [hz, Matrix.vecMulVec]
    simp [hzero]
  | @insert i s hi ih =>
    let u' := Function.update u i 0
    let B := A + Matrix.vecMulVec u' v
    have hu' : ∀ j, j ∉ s → u' j = 0 := by
      intro j hj
      by_cases hji : j = i
      · simp [u', hji]
      · simp [u', hji, hu j (by simp [hj, hji])]
    have hBi : B i = A i := by
      funext j
      simp [B, u', Matrix.vecMulVec, Matrix.add_apply]
    have hupdate : A + Matrix.vecMulVec u v = B.updateRow i (A i + u i • v) := by
      ext j k
      by_cases hji : j = i
      · subst j
        simp [Matrix.vecMulVec, Matrix.add_apply]
      · simp [B, u', Matrix.vecMulVec, Matrix.add_apply, Matrix.updateRow_apply, hji]
    have hfixed : (B.updateRow i v).det = (A.updateRow i v).det := by
      apply Matrix.det_eq_of_forall_row_eq_smul_add_const u' i (by simp [u'])
      intro j k
      by_cases hji : j = i
      · subst j
        simp [u']
      · simp [B, u', Matrix.vecMulVec, Matrix.updateRow_apply, hji]
    rw [hupdate, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
      ← hBi, Matrix.updateRow_eq_self, hfixed]
    change (A + Matrix.vecMulVec u' v).det + u i * (A.updateRow i v).det = _
    rw [ih u' hu', Finset.sum_insert hi]
    have hsum : (∑ j ∈ s, u' j * (A.updateRow j v).det) =
        ∑ j ∈ s, u j * (A.updateRow j v).det := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := fun h ↦ hi (h ▸ hj)
      simp [u', hji]
    rw [hsum]
    ring

/-- The rank-one determinant formula, valid even for singular base matrices. -/
theorem det_add_vecMulVec (A : Matrix ι ι R) (u v : ι → R) :
    (A + Matrix.vecMulVec u v).det = A.det + ∑ i, u i * (A.updateRow i v).det :=
  det_add_vecMulVec_of_support Finset.univ A u v (by simp)

/-- The first variation of the determinant at an arbitrary base matrix, as a genuine
linear map of the perturbation. Its definition does not require invertibility. -/
noncomputable def firstVariation (A : Matrix ι ι R) : Matrix ι ι R →ₗ[R] R where
  toFun B := ∑ i, (A.updateRow i (B i)).det
  map_add' B C := by
    change (∑ i, (A.updateRow i (B i + C i)).det) = _
    simp only [Matrix.det_updateRow_add, Finset.sum_add_distrib]
  map_smul' c B := by
    change (∑ i, (A.updateRow i (c • B i)).det) = c * _
    simp only [Matrix.det_updateRow_smul, Finset.mul_sum]

/-- A rank-one determinant update has no terms beyond its first variation. -/
theorem det_add_vecMulVec_firstVariation (A : Matrix ι ι R) (u v : ι → R) :
    (A + Matrix.vecMulVec u v).det = A.det + firstVariation A (Matrix.vecMulVec u v) := by
  rw [det_add_vecMulVec]
  congr 1
  change (∑ i, u i * (A.updateRow i v).det) =
    ∑ i, (A.updateRow i (u i • v)).det
  simp only [Matrix.det_updateRow_smul]

/-- Exact one-step expected determinant identity for arbitrary finite rank-one choices.
The normalized weights may be arbitrary ring elements; positivity is needed only later
for real-rooted selection, not for this algebraic identity. -/
theorem weighted_rank_one_expected_determinant {Ω : Type*} [Fintype Ω]
    (A : Matrix ι ι R) (u v : Ω → ι → R) (p : Ω → R) (hp : ∑ ω, p ω = 1) :
    (∑ ω, p ω * (A + Matrix.vecMulVec (u ω) (v ω)).det) =
      A.det + firstVariation A (∑ ω, p ω • Matrix.vecMulVec (u ω) (v ω)) := by
  simp_rw [det_add_vecMulVec_firstVariation, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul]
  congr 1
  simp only [map_sum, map_smul, smul_eq_mul]

/-- The subtraction form used for covariance matrices in the MSS characteristic polynomial. -/
theorem det_sub_vecMulVec_firstVariation (A : Matrix ι ι R) (u v : ι → R) :
    (A - Matrix.vecMulVec u v).det = A.det - firstVariation A (Matrix.vecMulVec u v) := by
  have hneg : Matrix.vecMulVec (-u) v = -Matrix.vecMulVec u v := by
    ext i j
    simp [Matrix.vecMulVec]
  have h := det_add_vecMulVec_firstVariation A (-u) v
  simpa only [hneg, map_neg, sub_eq_add_neg] using h

/-- Finite expected determinant after subtracting an independently chosen rank-one matrix.
This is the essential expectation-linearization identity, including singular base matrices. -/
theorem weighted_rank_one_expected_determinant_sub {Ω : Type*} [Fintype Ω]
    (A : Matrix ι ι R) (u v : Ω → ι → R) (p : Ω → R) (hp : ∑ ω, p ω = 1) :
    (∑ ω, p ω * (A - Matrix.vecMulVec (u ω) (v ω)).det) =
      A.det - firstVariation A (∑ ω, p ω • Matrix.vecMulVec (u ω) (v ω)) := by
  simp_rw [det_sub_vecMulVec_firstVariation, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul]
  congr 1
  simp only [map_sum, map_smul, smul_eq_mul]

/- The following general Jacobi calculation is ported from the already proved
`CommutatorTheorem.Epsilon.BTHermitianDetPDeriv` source, keeping its proof explicit. -/

/-- Product rule for a finite product, written in deletion form. -/
theorem pderiv_prod_finset {σ ι R : Type*} [CommSemiring R]
    [DecidableEq ι] (x : σ) (s : Finset ι)
    (f : ι → MvPolynomial σ R) :
    MvPolynomial.pderiv x (∏ i ∈ s, f i) =
      ∑ i ∈ s,
        (∏ j ∈ s.erase i, f j) * MvPolynomial.pderiv x (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, MvPolynomial.pderiv_mul,
        Finset.sum_insert ha]
      rw [Finset.erase_insert_eq_erase]
      simp only [Finset.erase_eq_of_notMem ha]
      rw [ih]
      simp only [Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · ac_rfl
      · apply Finset.sum_congr rfl
        intro i hi
        have hai : a ≠ i := by
          intro h
          apply ha
          simpa [h] using hi
        have herase : (insert a s).erase i = insert a (s.erase i) := by
          ext y
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · intro hy
            rcases hy.2 with rfl | hys
            · exact Or.inl rfl
            · exact Or.inr ⟨hy.1, hys⟩
          · intro hy
            rcases hy with rfl | ⟨hyi, hys⟩
            · exact ⟨hai, Or.inl rfl⟩
            · exact ⟨hyi, Or.inr hys⟩
        rw [herase, Finset.prod_insert]
        · ac_rfl
        · exact fun hmem => ha (Finset.mem_of_mem_erase hmem)

/-- Formal differentiation of a multivariate determinant is the sum of the
determinants obtained by differentiating one column. -/
theorem pderiv_det_eq_sum_updateCol
    {ι σ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (x : σ) (M : Matrix ι ι (MvPolynomial σ R)) :
    MvPolynomial.pderiv x M.det =
      ∑ j : ι, (M.updateCol j (fun i ↦ MvPolynomial.pderiv x (M i j))).det := by
  have pderiv_intCast (z : ℤ) :
      MvPolynomial.pderiv x (z : MvPolynomial σ R) = 0 := by
    change MvPolynomial.pderiv x (MvPolynomial.C (z : R)) = 0
    rw [MvPolynomial.pderiv_C]
  rw [Matrix.det_apply', map_sum]
  simp_rw [MvPolynomial.pderiv_mul, pderiv_intCast, zero_mul, zero_add,
    pderiv_prod_finset]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro π _
  congr 1
  rw [← Finset.prod_erase_mul Finset.univ
    (fun i => M.updateCol j (fun i ↦ MvPolynomial.pderiv x (M i j)) (π i) i)
    (Finset.mem_univ j)]
  simp only [Matrix.updateCol_apply, ↓reduceIte]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [hi.1]
  · simp


/-- First variation commutes with every coefficient-ring homomorphism. -/
theorem map_firstVariation {S : Type*} [CommRing S] (f : R →+* S)
    (A B : Matrix ι ι R) :
    f (firstVariation A B) = firstVariation (A.map f) (B.map f) := by
  change f (∑ i, (A.updateRow i (B i)).det) =
    ∑ i, ((A.map f).updateRow i ((B.map f) i)).det
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [RingHom.map_det]
  congr 1
  ext j k
  by_cases h : j = i <;> simp [Matrix.map_apply, Matrix.updateRow_apply, h]

/-- The multivariate Jacobi formula in row form, identifying the derivative with the
linear first variation proved above. -/
theorem pderiv_det_eq_firstVariation {σ : Type*} (x : σ)
    (M : Matrix ι ι (MvPolynomial σ R)) :
    MvPolynomial.pderiv x M.det = firstVariation M (M.map (MvPolynomial.pderiv x)) := by
  change MvPolynomial.pderiv x M.det =
    ∑ j, (M.updateRow j (fun i ↦ MvPolynomial.pderiv x (M j i))).det
  rw [← Matrix.det_transpose M, pderiv_det_eq_sum_updateCol]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.det_transpose]
  congr 1
  ext i k
  simp [Matrix.updateCol_apply, Matrix.updateRow_apply, Matrix.transpose_apply]

/-- Differentiating a matrix pencil in its scalar variable gives the first variation. -/
theorem pderiv_pencil_det {σ : Type*} (x : σ)
    (A B : Matrix ι ι R) :
    MvPolynomial.pderiv x
      (A.map MvPolynomial.C + (MvPolynomial.X x : MvPolynomial σ R) • B.map MvPolynomial.C).det =
      firstVariation
        (A.map MvPolynomial.C + (MvPolynomial.X x : MvPolynomial σ R) • B.map MvPolynomial.C)
        (B.map MvPolynomial.C) := by
  classical
  rw [pderiv_det_eq_firstVariation]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]

/-- Evaluating the differentiated determinant pencil at zero gives exactly the linear
first variation, without assuming the base matrix invertible. -/
theorem eval_zero_pderiv_pencil_det {σ : Type*} (x : σ)
    (A B : Matrix ι ι R) :
    MvPolynomial.eval (fun _ : σ ↦ (0 : R))
      (MvPolynomial.pderiv x
        (A.map MvPolynomial.C + (MvPolynomial.X x : MvPolynomial σ R) • B.map MvPolynomial.C).det) =
      firstVariation A B := by
  rw [pderiv_pencil_det, map_firstVariation]
  have hA :
      (A.map MvPolynomial.C + (MvPolynomial.X x : MvPolynomial σ R) • B.map MvPolynomial.C).map
      (MvPolynomial.eval (fun _ : σ ↦ (0 : R))) = A := by
    ext i j
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
  have hB : (B.map MvPolynomial.C).map
      (MvPolynomial.eval (fun _ : σ ↦ (0 : R))) = B := by
    ext i j
    simp
  rw [hA, hB]

/-- The constant term of a determinant pencil is the determinant of its base matrix. -/
theorem eval_zero_pencil_det {σ : Type*} (x : σ) (A B : Matrix ι ι R) :
    MvPolynomial.eval (fun _ : σ ↦ (0 : R))
      (A.map MvPolynomial.C + (MvPolynomial.X x : MvPolynomial σ R) •
        B.map MvPolynomial.C).det = A.det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]

/-- The full one-step mixed-characteristic identity: averaging a rank-one subtraction
is precisely applying `1 - ∂ₓ` to the mean-covariance determinant pencil and then
specializing its variable to zero. No invertibility, positivity, or outcome selection
hypothesis is used. The ring can itself be a polynomial ring in all remaining variables. -/
theorem weighted_rank_one_mixed_characteristic_step
    {Ω σ : Type*} [Fintype Ω] (x : σ)
    (A : Matrix ι ι R) (u v : Ω → ι → R) (p : Ω → R) (hp : ∑ ω, p ω = 1) :
    let B := ∑ ω, p ω • Matrix.vecMulVec (u ω) (v ω)
    let P := (A.map MvPolynomial.C + (MvPolynomial.X x : MvPolynomial σ R) •
      B.map MvPolynomial.C).det
    (∑ ω, p ω * (A - Matrix.vecMulVec (u ω) (v ω)).det) =
      MvPolynomial.eval (fun _ : σ ↦ (0 : R)) (P - MvPolynomial.pderiv x P) := by
  dsimp only
  rw [map_sub, eval_zero_pencil_det, eval_zero_pderiv_pencil_det]
  exact weighted_rank_one_expected_determinant_sub A u v p hp

/-- Replacing one row of the identity has determinant equal to its diagonal coordinate. -/
theorem det_updateRow_one (i : ι) (v : ι → R) :
    ((1 : Matrix ι ι R).updateRow i v).det = v i := by
  have h := Matrix.det_updateRow_sum (1 : Matrix ι ι R) i v
  have hv : (∑ k, v k • (1 : Matrix ι ι R) k) = v := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [hv] at h
  simpa using h

/-- The first variation of determinant at the identity is the trace. -/
theorem firstVariation_one (B : Matrix ι ι R) :
    firstVariation (1 : Matrix ι ι R) B = Matrix.trace B := by
  change (∑ i, ((1 : Matrix ι ι R).updateRow i (B i)).det) = ∑ i, B i i
  simp only [det_updateRow_one]

/-- Exact first variation at a scalar matrix, including the empty dimension. -/
theorem firstVariation_smul_one (t : R) (B : Matrix ι ι R) :
    firstVariation (t • (1 : Matrix ι ι R)) B =
      t ^ (Fintype.card ι - 1) * Matrix.trace B := by
  change (∑ i, ((t • (1 : Matrix ι ι R)).updateRow i (B i)).det) = _
  simp only [Matrix.det_updateRow_smul_left, det_updateRow_one,
    ← Finset.mul_sum, Matrix.trace, Matrix.diag]

/-- The initial logarithmic derivative of a scalar matrix is `trace B / t`.
This is the exact normalization used at the start of the MSS barrier argument. -/
theorem firstVariation_scalar_ratio {K : Type*} [Field K] [Nonempty ι]
    (t : K) (ht : t ≠ 0) (B : Matrix ι ι K) :
    firstVariation (t • (1 : Matrix ι ι K)) B /
      (t • (1 : Matrix ι ι K)).det = Matrix.trace B / t := by
  rw [firstVariation_smul_one, Matrix.det_smul, Matrix.det_one, mul_one]
  have hc : 0 < Fintype.card ι := Fintype.card_pos
  have hpow : t ^ Fintype.card ι = t ^ (Fintype.card ι - 1) * t := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  field_simp

end MixedCharacteristic
end NoEpsilon
