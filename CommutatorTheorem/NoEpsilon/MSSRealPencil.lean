import CommutatorTheorem.NoEpsilon.MSSBarrier

/-!
# Real coefficients of a Hermitian determinant pencil

Conjugating the coefficients transposes the matrix pencil and therefore fixes its
determinant. This supplies an actual real polynomial to the real MSS barrier lemmas.
-/

open scoped BigOperators ComplexOrder
open Matrix MvPolynomial

namespace NoEpsilon.MSSRealPencil

noncomputable def realPartPolynomial {σ : Type*} (p : MvPolynomial σ ℂ) :
    MvPolynomial σ ℝ := Finsupp.mapRange Complex.re (by rfl) p

theorem map_realPartPolynomial {σ : Type*} (p : MvPolynomial σ ℂ)
    (hp : p.map (starRingEnd ℂ) = p) :
    (realPartPolynomial p).map Complex.ofRealHom = p := by
  ext m
  have hc := congrArg (MvPolynomial.coeff m) hp
  simp only [MvPolynomial.coeff_map, starRingEnd_apply] at hc
  have hi := congrArg Complex.im hc
  simp only [Complex.star_def, Complex.conj_im] at hi
  simp only [MvPolynomial.coeff_map, realPartPolynomial, MvPolynomial.coeff_mapRange,
    Complex.ofRealHom_eq_coe]
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem psdPencil_conjugate (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian) :
    (MSSStability.psdPencil A).map (starRingEnd ℂ) = MSSStability.psdPencil A := by
  let P : Matrix ι ι (MvPolynomial κ ℂ) :=
    ∑ i, (MvPolynomial.X i : MvPolynomial κ ℂ) • (A i).map MvPolynomial.C
  change MvPolynomial.map (starRingEnd ℂ) (Matrix.det P) = Matrix.det P
  rw [RingHom.map_det, ← Matrix.det_transpose P]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, P, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, starRingEnd_apply,
    Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [(hA a).apply j i]

noncomputable def realPencil (A : κ → Matrix ι ι ℂ) : MvPolynomial κ ℝ :=
  realPartPolynomial (MSSStability.psdPencil A)

theorem map_realPencil (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian) :
    (realPencil A).map Complex.ofRealHom = MSSStability.psdPencil A :=
  map_realPartPolynomial _ (psdPencil_conjugate A hA)

theorem realPencil_realStable (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hTotal : (∑ i, A i).PosDef) : MSSBarrier.RealStable (realPencil A) := by
  unfold MSSBarrier.RealStable
  rw [map_realPencil A (fun i ↦ (hA i).1)]
  exact MSSStability.psdPencil_upperStable A hA hTotal

omit [Fintype κ] [DecidableEq κ] in
theorem map_fold_sub_pderiv (p : MvPolynomial κ ℝ) (xs : List κ) :
    (xs.foldl (fun p i ↦ p - MvPolynomial.pderiv i p) p).map Complex.ofRealHom =
      xs.foldl (fun p i ↦ p - MvPolynomial.pderiv i p) (p.map Complex.ofRealHom) := by
  induction xs generalizing p with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldl_cons, ih, map_sub, MvPolynomial.pderiv_map]

theorem realPencil_fold_realStable (A : κ → Matrix ι ι ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hTotal : (∑ i, A i).PosDef) (xs : List κ) :
    MSSBarrier.RealStable
      (xs.foldl (fun p i ↦ p - MvPolynomial.pderiv i p) (realPencil A)) := by
  unfold MSSBarrier.RealStable
  rw [map_fold_sub_pderiv, map_realPencil A (fun i ↦ (hA i).1)]
  exact MSSStability.psdPencil_fold_sub_pderiv_upperStable A hA hTotal xs


/-- A determinant pencil with an arbitrary Hermitian constant term. -/
noncomputable def affinePencil (B : Matrix ι ι ℂ) (A : κ → Matrix ι ι ℂ) :
    MvPolynomial κ ℂ :=
  (B.map MvPolynomial.C +
    ∑ i, (MvPolynomial.X i : MvPolynomial κ ℂ) • (A i).map MvPolynomial.C).det

theorem affinePencil_conjugate (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian) :
    (affinePencil B A).map (starRingEnd ℂ) = affinePencil B A := by
  let P : Matrix ι ι (MvPolynomial κ ℂ) :=
    B.map MvPolynomial.C +
      ∑ i, (MvPolynomial.X i : MvPolynomial κ ℂ) • (A i).map MvPolynomial.C
  change MvPolynomial.map (starRingEnd ℂ) (Matrix.det P) = Matrix.det P
  rw [RingHom.map_det, ← Matrix.det_transpose P]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, P, Matrix.map_apply, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_sum, map_mul,
    MvPolynomial.map_X, MvPolynomial.map_C, starRingEnd_apply, Matrix.transpose_apply]
  rw [hB.apply j i]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [(hA a).apply j i]

noncomputable def realAffinePencil (B : Matrix ι ι ℂ) (A : κ → Matrix ι ι ℂ) :
    MvPolynomial κ ℝ := realPartPolynomial (affinePencil B A)

theorem map_realAffinePencil (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian) :
    (realAffinePencil B A).map Complex.ofRealHom = affinePencil B A :=
  map_realPartPolynomial _ (affinePencil_conjugate B hB A hA)

end NoEpsilon.MSSRealPencil
