import NoEpsilon.MSSSelection

/-! # The exact operator norm budget for paired covariance -/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace NoEpsilon.MSSSelection

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Duplicating a diagonal block preserves any common Euclidean operator norm bound. -/
theorem norm_duplicate_diagonal_le (A : Matrix ι ι ℂ) (L : ℝ)
    (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) : ‖Matrix.fromBlocks A 0 0 A‖ ≤ L := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hL
  intro x
  let x₀ : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i ↦ x (Sum.inl i))
  let x₁ : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i ↦ x (Sum.inr i))
  have hx : ‖x‖ ^ 2 = ‖x₀‖ ^ 2 + ‖x₁‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x₀, x₁, PiLp.toLp_apply]
  have hAx : ‖Matrix.toEuclideanLin (Matrix.fromBlocks A 0 0 A) x‖ ^ 2 =
      ‖Matrix.toEuclideanLin A x₀‖ ^ 2 + ‖Matrix.toEuclideanLin A x₁‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Matrix.toLpLin_apply,
      Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
      Sum.elim_inl, Sum.elim_inr, x₀, x₁, Function.comp_def]
  have h₀ : ‖Matrix.toEuclideanLin A x₀‖ ≤ L * ‖x₀‖ :=
    (Matrix.l2_opNorm_mulVec A x₀).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have h₁ : ‖Matrix.toEuclideanLin A x₁‖ ≤ L * ‖x₁‖ :=
    (Matrix.l2_opNorm_mulVec A x₁).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  change ‖Matrix.toEuclideanLin (Matrix.fromBlocks A 0 0 A) x‖ ≤ L * ‖x‖
  apply le_of_sq_le_sq _ (mul_nonneg hL (norm_nonneg _))
  rw [hAx, mul_pow, hx]
  have h₀sq := pow_le_pow_left₀ (norm_nonneg _) h₀ 2
  have h₁sq := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  calc
    _ ≤ (L * ‖x₀‖) ^ 2 + (L * ‖x₁‖) ^ 2 := add_le_add h₀sq h₁sq
    _ = _ := by ring

/-- The four-outcome mean consists of two copies of the parent frame, so it has the same
operator norm budget, with no factor two loss. -/
theorem paired_covariance_norm_le (a b : κ → ι → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hframe : ‖∑ i, (outer (a i) + outer (b i))‖ ≤ L) :
    ‖∑ i, ∑ q : Bool × Bool, (1 / 4 : ℂ) • outer (pairedVector (a i) (b i) q)‖ ≤ L := by
  have hmean : (∑ i, ∑ q : Bool × Bool,
      (1 / 4 : ℂ) • outer (pairedVector (a i) (b i) q)) =
      Matrix.fromBlocks (∑ i, (outer (a i) + outer (b i))) 0 0
        (∑ i, (outer (a i) + outer (b i))) := by
    calc
      _ = ∑ i, (1 / 4 : ℂ) • ∑ q : Bool × Bool,
          outer (pairedVector (a i) (b i) q) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.smul_sum]
      _ = _ := paired_total_covariance a b
  rw [hmean]
  exact norm_duplicate_diagonal_le _ L hL hframe

end NoEpsilon.MSSSelection
