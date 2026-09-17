import CommutatorTheorem.NoEpsilon.HighMassCompression

/-!
# Intrinsic subspace form of the high-mass selection theorem

An orthonormal basis supplies the rectangular isometry required by the compression
theorem. The subspace itself carries the inherited Euclidean inner product.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix whose columns are the ambient vectors of an orthonormal subspace basis. -/
def subspaceBasisMatrix (W : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Matrix ι (Fin (Module.finrank ℂ W)) ℂ :=
  fun i j ↦ ((stdOrthonormalBasis ℂ W) j : EuclideanSpace ℂ ι) i

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
theorem subspaceBasisMatrix_isometry (W : Submodule ℂ (EuclideanSpace ℂ ι)) :
    (subspaceBasisMatrix W)ᴴ * subspaceBasisMatrix W = 1 := by
  let b := stdOrthonormalBasis ℂ W
  have hGram (j k : Fin (Module.finrank ℂ W)) :
      ((subspaceBasisMatrix W)ᴴ * subspaceBasisMatrix W) j k = inner ℂ (b j) (b k) := by
    change (∑ i, star ((b j : EuclideanSpace ℂ ι) i) * (b k : EuclideanSpace ℂ ι) i) =
      inner ℂ (b j : EuclideanSpace ℂ ι) (b k : EuclideanSpace ℂ ι)
    simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  ext j k
  rw [hGram, b.inner_eq_ite, Matrix.one_apply]

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
theorem subspaceBasisMatrix_mulVec (W : Submodule ℂ (EuclideanSpace ℂ ι))
    (x : Fin (Module.finrank ℂ W) → ℂ) :
    (WithLp.toLp 2 (subspaceBasisMatrix W *ᵥ x) : EuclideanSpace ℂ ι) =
      ∑ j, x j • ((stdOrthonormalBasis ℂ W) j : EuclideanSpace ℂ ι) := by
  ext i
  simp [Matrix.mulVec, dotProduct, subspaceBasisMatrix, mul_comm]

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
/-- Its isometric range is exactly the given Euclidean subspace. -/
theorem mem_range_subspaceBasisMatrix_iff (W : Submodule ℂ (EuclideanSpace ℂ ι))
    (v : ι → ℂ) :
    v ∈ (subspaceBasisMatrix W).mulVecLin.range ↔
      (WithLp.toLp 2 v : EuclideanSpace ℂ ι) ∈ W := by
  constructor
  · rintro ⟨x, rfl⟩
    change (WithLp.toLp 2 (subspaceBasisMatrix W *ᵥ x) : EuclideanSpace ℂ ι) ∈ W
    rw [subspaceBasisMatrix_mulVec]
    exact W.sum_mem (fun j _ ↦ W.smul_mem _ ((stdOrthonormalBasis ℂ W) j).property)
  · intro hv
    let w : W := ⟨WithLp.toLp 2 v, hv⟩
    let b := stdOrthonormalBasis ℂ W
    refine ⟨fun j ↦ b.repr w j, ?_⟩
    apply (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.injective
    change (WithLp.toLp 2 (subspaceBasisMatrix W *ᵥ (fun j ↦ b.repr w j)) :
      EuclideanSpace ℂ ι) = WithLp.toLp 2 v
    rw [subspaceBasisMatrix_mulVec]
    have h := congrArg (fun z : W ↦ (z : EuclideanSpace ℂ ι)) (b.sum_repr w)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h

set_option backward.isDefEq.respectTransparency false in
/-- Every low-codimension Euclidean subspace contains a unit neutral vector with a large
image under a high-mass matrix. No embedding is supplied as a hypothesis. -/
theorem highMass_subspace_has_large_neutral [Nonempty ι]
    (A : Matrix ι ι ℂ) (W : Submodule ℂ (EuclideanSpace ℂ ι))
    (t : ℝ) (ht : 0 < t) (hNorm : ‖A‖ ≤ 1) (hTrace : Matrix.trace A = 0)
    (hMass : HasHighTraceMass A t)
    (hCodim : (Fintype.card ι : ℝ) - Module.finrank ℂ W ≤ t * Fintype.card ι / 4) :
    ∃ v : EuclideanSpace ℂ ι, v ∈ W ∧ ‖v‖ = 1 ∧
      inner ℂ v (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A v) = 0 ∧
      t / 4 ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A v‖ := by
  let V := subspaceBasisMatrix W
  have hV := subspaceBasisMatrix_isometry W
  have hCodim' : (Fintype.card ι : ℝ) - Module.finrank ℂ V.mulVecLin.range ≤
      t * Fintype.card ι / 4 := by
    rw [finrank_range_isometry V hV, Fintype.card_fin]
    exact hCodim
  obtain ⟨v, hvRange, hvUnit, hvNeutral, hvLarge⟩ :=
    highMass_range_has_large_neutral A V hV t ht hNorm hTrace hMass hCodim'
  refine ⟨WithLp.toLp 2 v, (mem_range_subspaceBasisMatrix_iff W v).mp hvRange, ?_, ?_, ?_⟩
  · rw [vectorEnergy_eq_norm_sq] at hvUnit
    nlinarith [norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ ι)]
  · rwa [rayleighValue_eq_inner] at hvNeutral
  · exact hvLarge

end NoEpsilon
