import NoEpsilon.Sylvester
import NoEpsilon.BlockCompression
import NoEpsilon.GridCenters
import Mathlib.Data.Matrix.Block

/-!
# Finite block assembly in the Euclidean operator norm

The blocks have arbitrary finite index types, and may have different dimensions.
-/

open scoped BigOperators Matrix.Norms.L2Operator

set_option maxHeartbeats 2000000

namespace NoEpsilon
namespace BlockAssembly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d : ι → Type*} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

/-- A rectangular block of a matrix indexed by a dependent disjoint union. -/
def block (A : Matrix (Sigma d) (Sigma d) ℂ) (i j : ι) : Matrix (d i) (d j) ℂ :=
  A.submatrix (Sigma.mk i) (Sigma.mk j)

/-- Restrict a Euclidean vector to one block. -/
def vectorBlock (x : EuclideanSpace ℂ (Sigma d)) (i : ι) : EuclideanSpace ℂ (d i) :=
  WithLp.toLp 2 (fun a ↦ x ⟨i, a⟩)

theorem norm_sq_eq_sum_vectorBlock (x : EuclideanSpace ℂ (Sigma d)) :
    ‖x‖ ^ 2 = ∑ i, ‖vectorBlock x i‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, vectorBlock, PiLp.toLp_apply]
  exact Fintype.sum_sigma _

theorem block_mulVec (A : Matrix (Sigma d) (Sigma d) ℂ)
    (x : EuclideanSpace ℂ (Sigma d)) (i : ι) :
    vectorBlock (Matrix.toEuclideanLin A x) i =
      ∑ j, Matrix.toEuclideanLin (block A i j) (vectorBlock x j) := by
  ext a
  simp only [vectorBlock, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply,
    Matrix.toLpLin_apply, block, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  exact Fintype.sum_sigma _

theorem diagonal_mulVec (D : ∀ i, Matrix (d i) (d i) ℂ)
    (x : EuclideanSpace ℂ (Sigma d)) (i : ι) :
    vectorBlock (Matrix.toEuclideanLin (Matrix.blockDiagonal' D) x) i =
      Matrix.toEuclideanLin (D i) (vectorBlock x i) := by
  ext a
  simp only [vectorBlock, PiLp.toLp_apply, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sigma]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hji
    apply Finset.sum_eq_zero
    intro b _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hji.symm, zero_mul]

/-- A block diagonal matrix is bounded by a common bound for its diagonal blocks. -/
theorem norm_blockDiagonal_le (D : ∀ i, Matrix (d i) (d i) ℂ)
    (q : ℝ) (hq : 0 ≤ q) (hD : ∀ i, ‖D i‖ ≤ q) :
    ‖Matrix.blockDiagonal' D‖ ≤ q := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro x
  change ‖Matrix.toEuclideanLin (Matrix.blockDiagonal' D) x‖ ≤ q * ‖x‖
  apply le_of_sq_le_sq _ (mul_nonneg hq (norm_nonneg _))
  rw [norm_sq_eq_sum_vectorBlock, mul_pow, norm_sq_eq_sum_vectorBlock]
  simp_rw [diagonal_mulVec]
  calc
    ∑ i, ‖Matrix.toEuclideanLin (D i) (vectorBlock x i)‖ ^ 2 ≤
        ∑ i, q ^ 2 * ‖vectorBlock x i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := Matrix.l2_opNorm_mulVec (D i) (vectorBlock x i)
      have h' : ‖Matrix.toEuclideanLin (D i) (vectorBlock x i)‖ ≤
          q * ‖vectorBlock x i‖ :=
        h.trans (mul_le_mul_of_nonneg_right (hD i) (norm_nonneg _))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h' 2
    _ = q ^ 2 * ∑ i, ‖vectorBlock x i‖ ^ 2 := by rw [Finset.mul_sum]

/-- A common bound for all rectangular blocks gives a bound linear in the block count. -/
theorem norm_le_card_mul_block_bound (A : Matrix (Sigma d) (Sigma d) ℂ)
    (q : ℝ) (hq : 0 ≤ q) (hA : ∀ i j, ‖block A i j‖ ≤ q) :
    ‖A‖ ≤ Fintype.card ι * q := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hq)
  intro x
  change ‖Matrix.toEuclideanLin A x‖ ≤ (Fintype.card ι : ℝ) * q * ‖x‖
  have hrow (i : ι) : ‖vectorBlock (Matrix.toEuclideanLin A x) i‖ ≤
      q * ∑ j, ‖vectorBlock x j‖ := by
    rw [block_mulVec]
    calc
      ‖∑ j, Matrix.toEuclideanLin (block A i j) (vectorBlock x j)‖ ≤
          ∑ j, ‖Matrix.toEuclideanLin (block A i j) (vectorBlock x j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j, q * ‖vectorBlock x j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (Matrix.l2_opNorm_mulVec (block A i j) (vectorBlock x j)).trans
          (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _))
      _ = q * ∑ j, ‖vectorBlock x j‖ := (Finset.mul_sum _ _ _).symm
  have hCS : (∑ j, ‖vectorBlock x j‖) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ j, ‖vectorBlock x j‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : ι ↦ (1 : ℝ)) (fun j ↦ ‖vectorBlock x j‖)
  apply le_of_sq_le_sq _ (by positivity)
  rw [norm_sq_eq_sum_vectorBlock]
  calc
    ∑ i, ‖vectorBlock (Matrix.toEuclideanLin A x) i‖ ^ 2 ≤
        ∑ _i : ι, (q * ∑ j, ‖vectorBlock x j‖) ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2)
    _ = (Fintype.card ι : ℝ) * q ^ 2 * (∑ j, ‖vectorBlock x j‖) ^ 2 := by
      simp [mul_pow, mul_assoc]
    _ ≤ (Fintype.card ι : ℝ) * q ^ 2 *
        ((Fintype.card ι : ℝ) * ∑ j, ‖vectorBlock x j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = ((Fintype.card ι : ℝ) * q * ‖x‖) ^ 2 := by
      rw [← norm_sq_eq_sum_vectorBlock]
      ring

theorem block_diagonal_mul (D : ∀ i, Matrix (d i) (d i) ℂ)
    (A : Matrix (Sigma d) (Sigma d) ℂ) (i j : ι) :
    block (Matrix.blockDiagonal' D * A) i j = D i * block A i j := by
  ext a b
  simp only [block, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fintype.sum_sigma, Fintype.sum_eq_single i]
  · simp
  · intro k hki
    apply Finset.sum_eq_zero
    intro c _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hki.symm, zero_mul]

theorem block_mul_diagonal (D : ∀ i, Matrix (d i) (d i) ℂ)
    (A : Matrix (Sigma d) (Sigma d) ℂ) (i j : ι) :
    block (A * Matrix.blockDiagonal' D) i j = block A i j * D j := by
  ext a b
  simp only [block, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fintype.sum_sigma, Fintype.sum_eq_single j]
  · simp
  · intro k hkj
    apply Finset.sum_eq_zero
    intro c _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkj, mul_zero]

@[simp]
theorem block_add (A B : Matrix (Sigma d) (Sigma d) ℂ) (i j : ι) :
    block (A + B) i j = block A i j + block B i j := rfl

@[simp]
theorem block_sub (A B : Matrix (Sigma d) (Sigma d) ℂ) (i j : ι) :
    block (A - B) i j = block A i j - block B i j := rfl

@[simp]
theorem block_diagonal_same (D : ∀ i, Matrix (d i) (d i) ℂ) (i : ι) :
    block (Matrix.blockDiagonal' D) i i = D i := by
  ext a b
  exact Matrix.blockDiagonal'_apply_eq D i a b

theorem block_diagonal_ne (D : ∀ i, Matrix (d i) (d i) ℂ) (i j : ι) (h : i ≠ j) :
    block (Matrix.blockDiagonal' D) i j = 0 := by
  ext a b
  exact Matrix.blockDiagonal'_apply_ne D a b h

/-- Inverse rescaling makes the first commutator factor small at no product cost. -/
theorem normalize_factors {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix n n ℂ) (p : ℝ) (hp : 0 ≤ p) (hcost : ‖U‖ * ‖V‖ ≤ p) :
    ∃ U' V' : Matrix n n ℂ,
      U' * V' - V' * U' = U * V - V * U ∧ ‖U'‖ ≤ 1 / 4 ∧ ‖V'‖ ≤ 4 * p := by
  by_cases hU : U = 0
  · refine ⟨0, 0, by simp [hU], by norm_num, ?_⟩
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hp
  have hUn : 0 < ‖U‖ := norm_pos_iff.mpr hU
  let c : ℂ := (4 * ‖U‖ : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 4) hUn)
  have hcnorm : ‖c‖ = 4 * ‖U‖ := by
    simp only [c, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  refine ⟨c⁻¹ • U, c • V, ?_, ?_, ?_⟩
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [inv_mul_cancel₀ hc, mul_inv_cancel₀ hc, one_smul, one_smul]
  · rw [norm_smul, norm_inv, hcnorm]
    have hne : ‖U‖ ≠ 0 := ne_of_gt hUn
    field_simp
    nlinarith
  · rw [norm_smul, hcnorm]
    nlinarith

/-- Assemble normalized diagonal commutators using separated scalar centers. -/
theorem assemble_normalized
    (A : Matrix (Sigma d) (Sigma d) ℂ) (U V : ∀ i, Matrix (d i) (d i) ℂ)
    (q b : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b)
    (hdiag : ∀ i, block A i i = U i * V i - V i * U i)
    (hU : ∀ i, ‖U i‖ ≤ 1 / 4) (hV : ∀ i, ‖V i‖ ≤ q)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ + 1 / 4 ≤ b)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖z i - z j‖) :
    ∃ B C : Matrix (Sigma d) (Sigma d) ℂ,
      A = B * C - C * B ∧ ‖B‖ ≤ b ∧ ‖C‖ ≤ q + 2 * Fintype.card ι * ‖A‖ := by
  let D : ∀ i, Matrix (d i) (d i) ℂ := fun i ↦ z i • 1 + U i
  have hD : ∀ i, ‖D i‖ ≤ b := by
    intro i
    calc
      ‖D i‖ ≤ ‖z i • (1 : Matrix (d i) (d i) ℂ)‖ + ‖U i‖ := norm_add_le _ _
      _ ≤ ‖z i‖ * 1 + 1 / 4 := by
        rw [norm_smul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left coordinate_identity_norm_le (norm_nonneg _)) (hU i)
      _ ≤ b := by simpa using hz i
  have hsol : ∀ i j, i ≠ j → ∃ X : Matrix (d i) (d j) ℂ,
      D i * X - X * D j = block A i j ∧ ‖X‖ ≤ 2 * ‖A‖ := by
    intro i j hij
    have hgap : (1 / 2 : ℝ) ≤ ‖z i - z j‖ - ‖U i‖ - ‖U j‖ := by
      have := hsep i j hij
      have := hU i
      have := hU j
      linarith
    have hgap' : ‖U i‖ + ‖U j‖ < ‖z i - z j‖ := by linarith
    obtain ⟨X, hX, hnorm⟩ := exists_sylvester_solution_scalar_centers
      (U i) (U j) (z i) (z j) hgap' (block A i j)
    refine ⟨X, hX, hnorm.trans ?_⟩
    have hblock : ‖block A i j‖ ≤ ‖A‖ :=
      submatrix_operator_norm_le A (Sigma.mk i) (Sigma.mk j)
        (fun _ _ h ↦ by cases h; rfl) (fun _ _ h ↦ by cases h; rfl)
    apply (div_le_iff₀ (by linarith : 0 < ‖z i - z j‖ - ‖U i‖ - ‖U j‖)).2
    nlinarith [norm_nonneg A]
  choose X hX hXnorm using hsol
  let E : Matrix (Sigma d) (Sigma d) ℂ := fun a b ↦
    if h : a.1 = b.1 then 0 else X a.1 b.1 h a.2 b.2
  have hEdiag (i : ι) : block E i i = 0 := by
    ext a b
    simp [E, block]
  have hEoff (i j : ι) (hij : i ≠ j) : block E i j = X i j hij := by
    ext a b
    simp [E, block, hij]
  have hEnorm : ‖E‖ ≤ (Fintype.card ι : ℝ) * (2 * ‖A‖) := by
    apply norm_le_card_mul_block_bound E _ (by positivity)
    intro i j
    by_cases hij : i = j
    · subst j
      rw [hEdiag, norm_zero]
      positivity
    · rw [hEoff i j hij]
      exact hXnorm i j hij
  let B := Matrix.blockDiagonal' D
  let C := Matrix.blockDiagonal' V + E
  refine ⟨B, C, ?_, norm_blockDiagonal_le D b hb hD, ?_⟩
  · have hblocks (i j : ι) : block (B * C - C * B) i j = block A i j := by
      simp only [B, block_sub, block_diagonal_mul, block_mul_diagonal, C, block_add]
      by_cases hij : i = j
      · subst j
        rw [block_diagonal_same, hEdiag, add_zero, hdiag]
        dsimp [D]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, Matrix.mul_one]
        abel
      · rw [block_diagonal_ne V i j hij, zero_add, hEoff i j hij]
        exact hX i j hij
    ext ⟨i, a⟩ ⟨j, c⟩
    exact congrFun (congrFun (hblocks i j).symm a) c
  · calc
      ‖C‖ ≤ ‖Matrix.blockDiagonal' V‖ + ‖E‖ := norm_add_le _ _
      _ ≤ q + (Fintype.card ι : ℝ) * (2 * ‖A‖) :=
        add_le_add (norm_blockDiagonal_le V q hq hV) hEnorm
      _ = q + 2 * Fintype.card ι * ‖A‖ := by ring

/-- Product-cost assembly for arbitrary diagonal commutator representations and scalar centers. -/
theorem assemble_with_centers
    (A : Matrix (Sigma d) (Sigma d) ℂ) (p b : ℝ) (hp : 0 ≤ p) (hb : 0 ≤ b)
    (hdiag : ∀ i, ∃ U V : Matrix (d i) (d i) ℂ,
      block A i i = U * V - V * U ∧ ‖U‖ * ‖V‖ ≤ p)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ + 1 / 4 ≤ b)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖z i - z j‖) :
    ∃ B C : Matrix (Sigma d) (Sigma d) ℂ,
      A = B * C - C * B ∧
      ‖B‖ * ‖C‖ ≤ 4 * b * p + 2 * b * Fintype.card ι * ‖A‖ := by
  choose U V hrep hcost using hdiag
  have hnormalized := fun i ↦ normalize_factors (U i) (V i) p hp (hcost i)
  choose U' V' hcomm hU' hV' using hnormalized
  have hrep' (i : ι) : block A i i = U' i * V' i - V' i * U' i :=
    (hrep i).trans (hcomm i).symm
  obtain ⟨B, C, heq, hB, hC⟩ := assemble_normalized A U' V' (4 * p) b
    (by positivity) hb hrep' hU' hV' z hz hsep
  refine ⟨B, C, heq, ?_⟩
  calc
    ‖B‖ * ‖C‖ ≤ b * (4 * p + 2 * Fintype.card ι * ‖A‖) :=
      mul_le_mul hB hC (norm_nonneg _) hb
    _ = 4 * b * p + 2 * b * Fintype.card ι * ‖A‖ := by ring

/-- The constants of the no-epsilon induction, with the scalar centers still explicit. -/
theorem assemble_fixed_constants_with_centers
    (A : Matrix (Sigma d) (Sigma d) ℂ) (p : ℝ) (hp : 0 ≤ p)
    (hcard : Fintype.card ι ≤ 2 * 2 ^ 26 - 1)
    (hdiag : ∀ i, ∃ U V : Matrix (d i) (d i) ℂ,
      block A i i = U * V - V * U ∧ ‖U‖ * ‖V‖ ≤ p)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ + 1 / 4 ≤ 16384)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖z i - z j‖) :
    ∃ B C : Matrix (Sigma d) (Sigma d) ℂ,
      A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ 65536 * p + 2 ^ 42 * ‖A‖ := by
  obtain ⟨B, C, heq, hbound⟩ := assemble_with_centers A p 16384 hp
    (by norm_num) hdiag z hz hsep
  refine ⟨B, C, heq, hbound.trans ?_⟩
  have hcard' : (Fintype.card ι : ℝ) ≤ 134217728 := by
    exact_mod_cast (show Fintype.card ι ≤ 134217728 by norm_num at hcard; omega)
  nlinarith [mul_le_mul_of_nonneg_right hcard' (norm_nonneg A)]

/-- Finite-block assembly with the fixed constants of the no-epsilon proof.
The scalar grid and all off-diagonal Sylvester solutions are constructed internally. -/
theorem assemble_fixed_constants
    (A : Matrix (Sigma d) (Sigma d) ℂ) (p : ℝ) (hp : 0 ≤ p)
    (hcard : Fintype.card ι ≤ 2 * 2 ^ 26 - 1)
    (hdiag : ∀ i, ∃ U V : Matrix (d i) (d i) ℂ,
      block A i i = U * V - V * U ∧ ‖U‖ * ‖V‖ ≤ p) :
    ∃ B C : Matrix (Sigma d) (Sigma d) ℂ,
      A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ 65536 * p + 2 ^ 42 * ‖A‖ := by
  obtain ⟨z, hz, hsep⟩ := exists_assembly_centers hcard
  exact assemble_fixed_constants_with_centers A p hp hcard hdiag z hz hsep

/-- The assembled commutator stays in the original dimension under a partition equivalence. -/
theorem assemble_reindexed {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (e : n ≃ Sigma d) (p : ℝ) (hp : 0 ≤ p)
    (hcard : Fintype.card ι ≤ 2 * 2 ^ 26 - 1)
    (hdiag : ∀ i, ∃ U V : Matrix (d i) (d i) ℂ,
      block (A.submatrix e.symm e.symm) i i = U * V - V * U ∧ ‖U‖ * ‖V‖ ≤ p) :
    ∃ B C : Matrix n n ℂ,
      A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ 65536 * p + 2 ^ 42 * ‖A‖ := by
  obtain ⟨B, C, heq, hbound⟩ := assemble_fixed_constants
    (A.submatrix e.symm e.symm) p hp hcard hdiag
  refine ⟨B.submatrix e e, C.submatrix e e, ?_, ?_⟩
  · have h := congrArg (fun M : Matrix (Sigma d) (Sigma d) ℂ ↦ M.submatrix e e) heq
    simpa [Matrix.submatrix_submatrix, Matrix.submatrix_sub,
      Matrix.submatrix_mul_equiv] using h
  · simpa only [submatrix_operator_norm_equiv] using hbound

/-- Assembly for an arbitrary finite number of blocks. This bound is used after the
high-mass absorption, where the number of blocks is fixed by the mass threshold. -/
theorem assemble_any
    (A : Matrix (Sigma d) (Sigma d) ℂ) (p : ℝ) (hp : 0 ≤ p)
    (hdiag : ∀ i, ∃ U V : Matrix (d i) (d i) ℂ,
      block A i i = U * V - V * U ∧ ‖U‖ * ‖V‖ ≤ p) :
    ∃ B C : Matrix (Sigma d) (Sigma d) ℂ,
      A = B * C - C * B ∧
      ‖B‖ * ‖C‖ ≤ 4 * Fintype.card ι * p + 2 * (Fintype.card ι : ℝ) ^ 2 * ‖A‖ := by
  obtain ⟨z, hz, hsep⟩ := exists_assembly_centers_any (ι := ι)
  obtain ⟨B, C, hcomm, hbound⟩ := assemble_with_centers A p (Fintype.card ι) hp
    (Nat.cast_nonneg _) hdiag z hz hsep
  refine ⟨B, C, hcomm, ?_⟩
  convert hbound using 1 <;> ring

end BlockAssembly
end NoEpsilon
