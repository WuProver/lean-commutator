import KadisonSinger.DiagonalOperators

/-!
# Finite principal sections determine bounded-operator norm
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ENNReal Matrix
open Filter

namespace KadisonSinger

private noncomputable def finiteInclusionLinear (s : Finset ℕ) :
    EuclideanSpace ℂ s →ₗ[ℂ] Hilbert where
  toFun x := ∑ i : s, lp.single (E := fun _ : ℕ ↦ ℂ) 2 (i : ℕ) (x i)
  map_add' x y := by
    simp only [PiLp.add_apply, lp.single_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [PiLp.smul_apply, lp.single_smul, Finset.smul_sum, RingHom.id_apply]

private theorem finiteInclusionLinear_inner (s : Finset ℕ) (x y : EuclideanSpace ℂ s) :
    inner ℂ (finiteInclusionLinear s x) (finiteInclusionLinear s y) = inner ℂ x y := by
  change inner ℂ (∑ i : s, lp.single (E := fun _ : ℕ ↦ ℂ) 2 (i : ℕ) (x i))
    (∑ i : s, lp.single (E := fun _ : ℕ ↦ ℂ) 2 (i : ℕ) (y i)) = _
  simp only [sum_inner, lp.inner_single_left, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change (∑ j : s, lp.single (E := fun _ : ℕ ↦ ℂ) 2 (j : ℕ) (y j)) (i : ℕ) = y i
  simp only [lp.coeFn_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · exact lp.single_apply_self _ _ _
  · intro j _ hji
    exact lp.single_apply_ne _ _ _ (by intro hij; exact hji (Subtype.ext hij.symm))
  · simp

/-- The isometric coordinate inclusion of a finite coordinate set into `ℓ²(ℕ)`. -/
noncomputable def finiteInclusion (s : Finset ℕ) : EuclideanSpace ℂ s →ₗᵢ[ℂ] Hilbert :=
  (finiteInclusionLinear s).isometryOfInner (finiteInclusionLinear_inner s)

@[simp] theorem finiteInclusion_apply (s : Finset ℕ) (x : EuclideanSpace ℂ s) :
    finiteInclusion s x = ∑ i : s, lp.single (E := fun _ : ℕ ↦ ℂ) 2 (i : ℕ) (x i) := rfl

/-- A principal matrix is the matrix of the corresponding coordinate compression. -/
theorem inner_finiteSection (A : Operator) (s : Finset ℕ) (x y : EuclideanSpace ℂ s) :
    inner ℂ (finiteInclusion s x) (A (finiteInclusion s y)) =
      inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := s)
        (Matrix.submatrix (matrixEntry A) (fun i : s ↦ (i : ℕ)) (fun i : s ↦ (i : ℕ))) y) := by
  simp only [finiteInclusion_apply, map_sum, sum_inner, inner_sum, lp.inner_single_left]
  have hs (i : ℕ) (z : ℂ) :
      lp.single (E := fun _ : ℕ ↦ ℂ) 2 i z = z • basisVector i := by
    simp [basisVector, ← lp.single_smul]
  simp_rw [hs, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  simp only [Matrix.ofLp_toEuclideanCLM]
  rw [Finset.sum_comm]
  change (∑ i : s, ∑ j : s, (y j * A (basisVector j) i) * star (x i)) =
    ∑ i : s, ((Matrix.submatrix (matrixEntry A) (fun i : s ↦ (i : ℕ))
      (fun i : s ↦ (i : ℕ))) *ᵥ (fun j ↦ y j)) i * star (x i)
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, matrixEntry, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every finite principal matrix of a bounded operator has norm at most the operator norm. -/
theorem finiteSection_norm_le (A : Operator) (s : Finset ℕ) :
    ‖Matrix.submatrix (matrixEntry A) (fun i : s ↦ (i : ℕ)) (fun i : s ↦ (i : ℕ))‖ ≤ ‖A‖ := by
  let M := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := s)
    (Matrix.submatrix (matrixEntry A) (fun i : s ↦ (i : ℕ)) (fun i : s ↦ (i : ℕ)))
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro y
  change ‖M y‖ ≤ ‖A‖ * ‖y‖
  have h := inner_finiteSection A s (M y) y
  have he := norm_inner_le_norm (𝕜 := ℂ) (finiteInclusion s (M y)) (A (finiteInclusion s y))
  rw [h, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _), (finiteInclusion s).norm_map] at he
  have ha := A.le_opNorm (finiteInclusion s y)
  rw [(finiteInclusion s).norm_map] at ha
  have hh := mul_le_mul_of_nonneg_left ha (norm_nonneg (M y))
  by_cases hz : ‖M y‖ = 0
  · rw [hz]; positivity
  · have hp : 0 < ‖M y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact (mul_le_mul_iff_right₀ hp).mp (by simpa [pow_two] using he.trans hh)

/-- The operator norm is bounded once all finite principal sections have a common bound. -/
theorem norm_le_of_finiteSection (A : Operator) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ s : Finset ℕ,
      ‖Matrix.submatrix (matrixEntry A) (fun i : s ↦ (i : ℕ)) (fun i : s ↦ (i : ℕ))‖ ≤ C) :
    ‖A‖ ≤ C := by
  have hinner (x y : Hilbert) : ‖inner ℂ x (A y)‖ ≤ ‖x‖ * (C * ‖y‖) := by
    have hfin (s : Finset ℕ) :
        ‖inner ℂ (∑ i ∈ s, lp.single (E := fun _ : ℕ ↦ ℂ) 2 i (x i))
          (A (∑ i ∈ s, lp.single (E := fun _ : ℕ ↦ ℂ) 2 i (y i)))‖ ≤
            ‖∑ i ∈ s, lp.single (E := fun _ : ℕ ↦ ℂ) 2 i (x i)‖ *
              (C * ‖∑ i ∈ s, lp.single (E := fun _ : ℕ ↦ ℂ) 2 i (y i)‖) := by
      let xs : EuclideanSpace ℂ s := WithLp.toLp 2 (fun i ↦ x i)
      let ys : EuclideanSpace ℂ s := WithLp.toLp 2 (fun i ↦ y i)
      have hx : finiteInclusion s xs =
          ∑ i ∈ s, lp.single (E := fun _ : ℕ ↦ ℂ) 2 i (x i) := by
        simp [finiteInclusion_apply, xs]
      have hy : finiteInclusion s ys =
          ∑ i ∈ s, lp.single (E := fun _ : ℕ ↦ ℂ) 2 i (y i) := by
        simp [finiteInclusion_apply, ys]
      rw [← hx, ← hy, inner_finiteSection, (finiteInclusion s).norm_map,
        (finiteInclusion s).norm_map]
      apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
      gcongr
      exact (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := s) _).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_right (h s) (norm_nonneg ys))
    have hx := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x
    have hy := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) y
    apply le_of_tendsto_of_tendsto
      ((hx.inner (A.continuous.tendsto _ |>.comp hy)).norm)
      (hx.norm.mul (tendsto_const_nhds.mul hy.norm))
      (Eventually.of_forall hfin)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro y
  have hh := hinner (A y) y
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)] at hh
  by_cases hz : ‖A y‖ = 0
  · rw [hz]; positivity
  · have hp : 0 < ‖A y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact (mul_le_mul_iff_right₀ hp).mp (by simpa [pow_two] using hh)

end KadisonSinger
