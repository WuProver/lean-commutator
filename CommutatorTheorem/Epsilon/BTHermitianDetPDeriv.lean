import CommutatorTheorem.Epsilon.BTDeterminantStability
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Coordinate partial derivatives of Hermitian determinant polynomials

This file proves the multivariate Jacobi identity needed in the exact mixed
determinantal-polynomial expansion.  In particular, differentiating
`det (diag X - A)` in one coordinate deletes that coordinate's row and
column, with the remaining variables renamed along `Fin.succAbove`.
-/

namespace CommutatorTheorem.BTHermitianDetPDeriv

open scoped BigOperators
open Finset
open CommutatorTheorem.BTDeterminantStability

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

private theorem det_updateCol_single_self
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (j : ι) :
    (M.updateCol j (Pi.single j 1)).det = Matrix.adjugate M j j := by
  calc
    (M.updateCol j (Pi.single j 1)).det =
        (M.updateCol j (Pi.single j 1)).transpose.det :=
      (Matrix.det_transpose _).symm
    _ = (M.transpose.updateRow j (Pi.single j 1)).det := by
      rw [Matrix.updateRow_transpose]
    _ = Matrix.adjugate M.transpose j j :=
      (Matrix.adjugate_apply M.transpose j j).symm
    _ = Matrix.adjugate M j j := by
      have h := congrArg (fun N => N j j) (Matrix.adjugate_transpose M)
      simpa using h.symm

/-- A coordinate partial derivative of `det (diag X - A)` is its corresponding
diagonal cofactor. -/
theorem pderiv_hermitianDetPoly_eq_adjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i : ι) :
    MvPolynomial.pderiv i (hermitianDetPoly A) =
      Matrix.adjugate
        (Matrix.diagonal (fun j => MvPolynomial.X j) -
          A.map MvPolynomial.C) i i := by
  unfold hermitianDetPoly
  rw [pderiv_det_eq_sum_updateCol]
  let M := Matrix.diagonal (fun j : ι => MvPolynomial.X j) -
    A.map MvPolynomial.C
  have hcol (j : ι) :
      (fun r => MvPolynomial.pderiv i (M r j)) =
        if i = j then Pi.single j 1 else 0 := by
    funext r
    by_cases hij : i = j
    · subst j
      by_cases hri : r = i
      · subst r
        simp [M]
      · simp [M, hri]
    · by_cases hrj : r = j
      · subst r
        simp [M, hij]
      · simp [M, hij, hrj]
  change (∑ j : ι, (M.updateCol j
    (fun r => MvPolynomial.pderiv i (M r j))).det) = _
  rw [Finset.sum_eq_single i]
  · rw [hcol, if_pos rfl, det_updateCol_single_self]
  · intro j _ hji
    rw [hcol, if_neg (Ne.symm hji)]
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro r
    simp
  · simp

/-- Coordinate deletion formula for the multivariate Hermitian determinant.
The variables of the principal submatrix are embedded by `i.succAbove`. -/
theorem pderiv_hermitianDetPoly_fin_succ
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) :
    MvPolynomial.pderiv i (hermitianDetPoly A) =
      MvPolynomial.rename i.succAbove
        (hermitianDetPoly (A.submatrix i.succAbove i.succAbove)) := by
  rw [pderiv_hermitianDetPoly_eq_adjugate]
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Nat.succ_eq_add_one]
  have hsign : (-1 : MvPolynomial (Fin (n + 1)) ℂ) ^
      ((i : ℕ) + (i : ℕ)) = 1 := by
    rw [← two_mul]
    simp [pow_mul]
  rw [hsign, one_mul]
  unfold hermitianDetPoly
  change _ = (MvPolynomial.rename i.succAbove).toRingHom
    ((Matrix.diagonal (fun r : Fin n => MvPolynomial.X r) -
      (A.submatrix i.succAbove i.succAbove).map MvPolynomial.C).det)
  rw [RingHom.map_det]
  congr 1
  ext r c
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.map_apply]
  by_cases hrc : r = c
  · subst c
    simp
  · have hsucc : i.succAbove r ≠ i.succAbove c :=
      fun h => hrc (Fin.succAbove_right_injective h)
    simp [hrc, hsucc]

/-- Coordinate partial derivatives commute over every commutative semiring. -/
theorem pderiv_comm {σ R : Type*} [CommSemiring R]
    (i j : σ) (p : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
      by_cases hij : i = j
      · subst j
        rfl
      · simp only [MvPolynomial.pderiv_monomial]
        have hd : (d - Finsupp.single j 1) - Finsupp.single i 1 =
            (d - Finsupp.single i 1) - Finsupp.single j 1 := by
          ext x
          by_cases hxi : x = i
          · subst x
            simp [hij]
          · by_cases hxj : x = j
            · subst x
              simp [Ne.symm hij]
            · simp [hxi, hxj]
        rw [hd]
        congr 1
        simp [hij, Ne.symm hij, mul_comm, mul_left_comm, mul_assoc]
  | add p q hp hq =>
      simpa using congrArg₂ (· + ·) hp hq

/-- The Hermitian determinant polynomial is multiaffine: differentiating
twice in one coordinate gives zero. -/
theorem pderiv_self_hermitianDetPoly_fin_succ
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) :
    MvPolynomial.pderiv i
        (MvPolynomial.pderiv i (hermitianDetPoly A)) = 0 := by
  rw [pderiv_hermitianDetPoly_fin_succ]
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hi
  obtain ⟨j, _hj, heq⟩ := MvPolynomial.mem_vars_rename
    i.succAbove (hermitianDetPoly (A.submatrix i.succAbove i.succAbove)) hi
  exact Fin.succAbove_ne i j heq

/-- Real-coefficient coordinate deletion formula for a Hermitian determinant
polynomial. -/
theorem pderiv_realHermitianDetPoly_fin_succ
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : A.IsHermitian) (i : Fin (n + 1)) :
    MvPolynomial.pderiv i (realHermitianDetPoly A) =
      MvPolynomial.rename i.succAbove
        (realHermitianDetPoly (A.submatrix i.succAbove i.succAbove)) := by
  apply MvPolynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  rw [← MvPolynomial.pderiv_map, map_realHermitianDetPoly A hA,
    pderiv_hermitianDetPoly_fin_succ, MvPolynomial.map_rename,
    map_realHermitianDetPoly _ (hA.submatrix i.succAbove)]

/-- The real Hermitian determinant polynomial is multiaffine. -/
theorem pderiv_self_realHermitianDetPoly_fin_succ
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : A.IsHermitian) (i : Fin (n + 1)) :
    MvPolynomial.pderiv i
        (MvPolynomial.pderiv i (realHermitianDetPoly A)) = 0 := by
  rw [pderiv_realHermitianDetPoly_fin_succ A hA i]
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hi
  obtain ⟨j, _hj, heq⟩ := MvPolynomial.mem_vars_rename
    i.succAbove
    (realHermitianDetPoly (A.submatrix i.succAbove i.succAbove)) hi
  exact Fin.succAbove_ne i j heq

end CommutatorTheorem.BTHermitianDetPDeriv
