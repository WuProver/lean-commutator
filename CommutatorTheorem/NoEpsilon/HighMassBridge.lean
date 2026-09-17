import CommutatorTheorem.NoEpsilon.HighMassGreedy

/-!
# A proportionate invertible bridge from high trace mass

The columns of `P` are the greedy neutral frame. The columns of `Q` are their
normalized images. Both matrices are isometries, their ranges are orthogonal, and
`Q* A P` is a real positive diagonal matrix with entries between `t / 4` and `1`.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A vector family, represented as the columns of a rectangular matrix. -/
def familyMatrix (p : κ → EuclideanSpace ℂ ι) : Matrix ι κ ℂ := fun i j ↦ p j i

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedSectionVars false in
/-- Matrix Gram entries are the actual Euclidean inner products. -/
theorem familyMatrix_gram_entry (p q : κ → EuclideanSpace ℂ ι) (j k : κ) :
    ((familyMatrix p)ᴴ * familyMatrix q) j k = inner ℂ (p j) (q k) := by
  simp only [familyMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
theorem familyMatrix_isometry (p : κ → EuclideanSpace ℂ ι) (hp : Orthonormal ℂ p) :
    (familyMatrix p)ᴴ * familyMatrix p = 1 := by
  ext i j
  rw [familyMatrix_gram_entry, orthonormal_iff_ite.mp hp, Matrix.one_apply]

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedSectionVars false in
/-- Applying a matrix to every column agrees with its Euclidean operator. -/
theorem mul_familyMatrix (A : Matrix ι ι ℂ) (p : κ → EuclideanSpace ℂ ι) :
    A * familyMatrix p =
      familyMatrix (fun j ↦ Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A (p j)) := rfl

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
theorem familyMatrix_compression_entry (A : Matrix ι ι ℂ)
    (p q : κ → EuclideanSpace ℂ ι) (i j : κ) :
    ((familyMatrix p)ᴴ * A * familyMatrix q) i j =
      inner ℂ (p i) (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A (q j)) := by
  rw [Matrix.mul_assoc, mul_familyMatrix, familyMatrix_gram_entry]

set_option backward.isDefEq.respectTransparency false in
/-- An orthogonal neutral frame with large images yields a well-conditioned diagonal bridge. -/
theorem neutral_frame_to_bridge (A : Matrix ι ι ℂ) (r : ℝ) (hr : 0 < r)
    (hNorm : ‖A‖ ≤ 1) {k : ℕ} (p : Fin k → EuclideanSpace ℂ ι)
    (hp : IsLargeNeutralFrame (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) r p) :
    ∃ (P Q : Matrix ι (Fin k) ℂ) (d : Fin k → ℝ),
      Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Pᴴ * Q = 0 ∧ Pᴴ * A * P = 0 ∧
      A * P = Q * Matrix.diagonal (fun i ↦ (d i : ℂ)) ∧
      Qᴴ * A * P = Matrix.diagonal (fun i ↦ (d i : ℂ)) ∧
      ∀ i, r ≤ d i ∧ d i ≤ 1 := by
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  let d : Fin k → ℝ := fun i ↦ ‖T (p i)‖
  have hd (i : Fin k) : 0 < d i := hr.trans_le (hp.2.2.2 i)
  let c : Fin k → ℂ := fun i ↦ ((d i)⁻¹ : ℝ)
  let q : Fin k → EuclideanSpace ℂ ι := fun i ↦ c i • T (p i)
  have hqUnit (i : Fin k) : ‖q i‖ = 1 := by
    simp only [q, norm_smul, c, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hd i))]
    exact inv_mul_cancel₀ (hd i).ne'
  have hqOrth (i j : Fin k) (hij : i ≠ j) : inner ℂ (q i) (q j) = 0 := by
    have h : inner ℂ (T (p i)) (T (p j)) = 0 := hp.2.2.1 i j hij
    simp only [q, inner_smul_left, inner_smul_right, h, mul_zero]
  have hq : Orthonormal ℂ q := ⟨hqUnit, hqOrth⟩
  have hPq (i j : Fin k) : inner ℂ (p i) (q j) = 0 := by
    have h : inner ℂ (p i) (T (p j)) = 0 := hp.2.1 i j
    simp only [q, inner_smul_right, h, mul_zero]
  have hScale (i : Fin k) : (d i : ℂ) • q i = T (p i) := by
    simp only [q, smul_smul, c, ← Complex.ofReal_mul, mul_inv_cancel₀ (hd i).ne',
      Complex.ofReal_one, one_smul]
  have hAP : A * familyMatrix p = familyMatrix q * Matrix.diagonal (fun i ↦ (d i : ℂ)) := by
    rw [mul_familyMatrix]
    ext i j
    change (T (p j)) i = (familyMatrix q * Matrix.diagonal (fun i ↦ (d i : ℂ))) i j
    rw [← hScale j, Matrix.mul_diagonal]
    simp only [PiLp.smul_apply, smul_eq_mul, familyMatrix]
    exact mul_comm _ _
  refine ⟨familyMatrix p, familyMatrix q, d, familyMatrix_isometry p hp.1,
    familyMatrix_isometry q hq, ?_, ?_, hAP, ?_, ?_⟩
  · ext i j
    rw [familyMatrix_gram_entry, hPq, Matrix.zero_apply]
  · ext i j
    rw [familyMatrix_compression_entry, hp.2.1, Matrix.zero_apply]
  · rw [Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, familyMatrix_isometry q hq, Matrix.one_mul]
  · intro i
    refine ⟨hp.2.2.2 i, ?_⟩
    have hBound := T.le_opNorm (p i)
    rw [hp.1.1 i, mul_one] at hBound
    exact hBound.trans hNorm

set_option backward.isDefEq.respectTransparency false in
/-- The high-mass branch has a bridge of rank exactly `ceil(t n / 16)`, in the original
dimension. No enlargement and no zero compression of the image range are assumed. -/
theorem highMass_exists_diagonal_bridge [Nonempty ι]
    (A : Matrix ι ι ℂ) (t : ℝ) (ht : 0 < t) (hNorm : ‖A‖ ≤ 1)
    (hTrace : Matrix.trace A = 0) (hMass : HasHighTraceMass A t) :
    ∃ (P Q : Matrix ι (Fin ⌈t * Fintype.card ι / 16⌉₊) ℂ)
      (d : Fin ⌈t * Fintype.card ι / 16⌉₊ → ℝ),
      Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Pᴴ * Q = 0 ∧ Pᴴ * A * P = 0 ∧
      A * P = Q * Matrix.diagonal (fun i ↦ (d i : ℂ)) ∧
      Qᴴ * A * P = Matrix.diagonal (fun i ↦ (d i : ℂ)) ∧
      ∀ i, t / 4 ≤ d i ∧ d i ≤ 1 := by
  obtain ⟨p, hp⟩ := highMass_exists_neutral_frame A t ht hNorm hTrace hMass
  exact neutral_frame_to_bridge A (t / 4) (by linarith) hNorm p hp

end NoEpsilon
