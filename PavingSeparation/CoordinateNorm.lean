import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! Coordinate inclusions, contractive compressions and invariance under relabeling. -/

open scoped BigOperators Matrix.Norms.L2Operator

namespace PavingSeparation

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The Euclidean coordinate inclusion associated to an injective map. -/
def coordinateInclusion (f : α → β) : Matrix β α ℂ :=
  fun b a ↦ if b = f a then 1 else 0

omit [Fintype α] in
theorem coordinateInclusion_isometry (f : α → β) (hf : Function.Injective f) :
    (coordinateInclusion f).conjTranspose * coordinateInclusion f = 1 := by
  ext a a'
  simp [Matrix.mul_apply, coordinateInclusion, Matrix.conjTranspose_apply,
    Matrix.one_apply, hf.eq_iff, eq_comm]

theorem coordinate_identity_norm_le : ‖(1 : Matrix α α ℂ)‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def, map_one]
  exact ContinuousLinearMap.norm_id_le

theorem coordinateInclusion_norm_le (f : α → β) (hf : Function.Injective f) :
    ‖coordinateInclusion f‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (coordinateInclusion f)
  rw [coordinateInclusion_isometry f hf] at h
  have hle := coordinate_identity_norm_le (α := α)
  rw [h] at hle
  nlinarith [norm_nonneg (coordinateInclusion f)]

omit [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ] in
theorem submatrix_eq_coordinate_compression (A : Matrix β β ℂ)
    (f : α → β) (g : γ → β) :
    A.submatrix f g = (coordinateInclusion f).conjTranspose * A * coordinateInclusion g := by
  ext a c
  simp [Matrix.mul_apply, coordinateInclusion, Matrix.conjTranspose_apply,
    mul_ite, ite_mul, Finset.sum_ite_eq']

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
/-- Rectangular coordinate compression is contractive in the Euclidean operator norm. -/
theorem submatrix_operator_norm_le (A : Matrix β β ℂ)
    (f : α → β) (g : γ → β) (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖A.submatrix f g‖ ≤ ‖A‖ := by
  rw [submatrix_eq_coordinate_compression]
  calc
    ‖(coordinateInclusion f).conjTranspose * A * coordinateInclusion g‖ ≤
        ‖(coordinateInclusion f).conjTranspose * A‖ * ‖coordinateInclusion g‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(coordinateInclusion f).conjTranspose‖ * ‖A‖) * ‖coordinateInclusion g‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖A‖) * 1 := by
      rw [Matrix.l2_opNorm_conjTranspose]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (coordinateInclusion_norm_le f hf) (norm_nonneg _))
        (coordinateInclusion_norm_le g hg) (norm_nonneg _) (by positivity)
    _ = ‖A‖ := by ring

/-- Reindexing both coordinates by an equivalence preserves the Euclidean operator norm. -/
theorem submatrix_operator_norm_equiv (A : Matrix β β ℂ) (e : α ≃ β) :
    ‖A.submatrix e e‖ = ‖A‖ := by
  apply le_antisymm (submatrix_operator_norm_le A e e e.injective e.injective)
  have h := submatrix_operator_norm_le (A.submatrix e e) e.symm e.symm
    e.symm.injective e.symm.injective
  simpa [Matrix.submatrix_submatrix] using h

end PavingSeparation
