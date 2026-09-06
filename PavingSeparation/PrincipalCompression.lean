import PavingSeparation.PavingBasic

/-! The ambient coordinate compression has exactly the principal submatrix's operator norm. -/

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace PavingSeparation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Principal submatrix on the selected original coordinates, including the empty case. -/
def principalSubmatrix (s : Finset ι) (A : Matrix ι ι ℂ) : Matrix s s ℂ :=
  A.submatrix Subtype.val Subtype.val

theorem compression_eq_inclusion (s : Finset ι) (A : Matrix ι ι ℂ) :
    compression s A = coordinateInclusion (Subtype.val : s → ι) * principalSubmatrix s A *
      (coordinateInclusion (Subtype.val : s → ι)).conjTranspose := by
  have hs (i : ι) (f : ι → ℂ) :
      (∑ x : s, if i = (x : ι) then f x else 0) = if i ∈ s then f i else 0 := by
    rw [Finset.sum_coe_sort s (fun x ↦ if i = x then f x else 0)]
    simpa only [eq_comm] using Finset.sum_ite_eq' s i f
  ext i j
  simp only [Matrix.mul_apply, coordinateInclusion, Matrix.conjTranspose_apply,
    principalSubmatrix, Matrix.submatrix_apply, apply_ite star, star_one, star_zero,
    mul_ite, ite_mul, one_mul, zero_mul, mul_one, mul_zero]
  have hinner (x : s) :
      (∑ y : s, if i = (y : ι) then A y x else 0) = if i ∈ s then A i x else 0 :=
    hs i (fun y ↦ A y x)
  simp_rw [hinner]
  rw [hs j (fun x ↦ if i ∈ s then A i x else 0)]
  simp only [compression_apply]
  split_ifs <;> simp_all

/-- Paving was defined using ambient masks; this proves agreement with the PDF convention. -/
theorem compression_norm_eq_principal (s : Finset ι) (A : Matrix ι ι ℂ) :
    ‖compression s A‖ = ‖principalSubmatrix s A‖ := by
  let J := coordinateInclusion (Subtype.val : s → ι)
  have hJ : ‖J‖ ≤ 1 := coordinateInclusion_norm_le _ Subtype.val_injective
  apply le_antisymm
  · rw [compression_eq_inclusion]
    change ‖J * principalSubmatrix s A * J.conjTranspose‖ ≤ _
    calc
      _ ≤ ‖J‖ * ‖principalSubmatrix s A‖ * ‖J.conjTranspose‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ 1 * ‖principalSubmatrix s A‖ * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
      _ = _ := by ring
  · have h := submatrix_operator_norm_le (compression s A)
      (Subtype.val : s → ι) (Subtype.val : s → ι)
      Subtype.val_injective Subtype.val_injective
    have heq : (compression s A).submatrix (Subtype.val : s → ι) Subtype.val =
        principalSubmatrix s A := by
      ext i j
      simp [principalSubmatrix, i.property, j.property]
    rwa [heq] at h

end PavingSeparation
