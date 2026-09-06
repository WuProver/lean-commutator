import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# Separated scalar centers and the Sylvester equation

The matrix norm throughout this file is the operator norm for Euclidean spaces,
including on rectangular matrices. The main theorem includes the precise
separation denominator and does not assume that either coefficient is normal.
-/

open scoped NNReal Matrix.Norms.L2Operator

namespace NoEpsilon

/-- A Lipschitz perturbation of a nonzero scalar has a quantitatively bounded inverse. -/
theorem exists_scalar_add_lipschitz_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : E → E) (δ : ℝ≥0) (hf : LipschitzWith δ f) (hf0 : f 0 = 0)
    (c : ℂ) (hsep : (δ : ℝ) < ‖c‖) (y : E) :
    ∃ x : E, c • x + f x = y ∧ ‖x‖ ≤ ‖y‖ / (‖c‖ - δ) := by
  have hcpos : 0 < ‖c‖ := lt_of_le_of_lt δ.coe_nonneg hsep
  have hc : c ≠ 0 := norm_pos_iff.mp hcpos
  let F : E → E := fun x ↦ c⁻¹ • (y - f x)
  let K : ℝ≥0 := ‖c⁻¹‖₊ * δ
  have hK : K < 1 := by
    change ‖c⁻¹‖₊ * δ < 1
    rw [← NNReal.coe_lt_coe]
    simp only [NNReal.coe_mul, coe_nnnorm, NNReal.coe_one, norm_inv]
    rw [inv_mul_lt_iff₀ hcpos]
    simpa using hsep
  have hF : ContractingWith K F := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
    intro x x'
    calc
      dist (F x) (F x') = ‖c⁻¹‖ * dist (f x) (f x') := by
        simp only [F, dist_eq_norm, ← smul_sub, norm_smul]
        rw [sub_sub_sub_cancel_left, norm_sub_rev]
      _ ≤ ‖c⁻¹‖ * (δ * dist x x') :=
        mul_le_mul_of_nonneg_left (hf.dist_le_mul x x') (norm_nonneg _)
      _ = K * dist x x' := by simp [K, mul_assoc]
  let x := hF.fixedPoint F
  have hx : c⁻¹ • (y - f x) = x := hF.fixedPoint_isFixedPt
  have hcx : c • x = y - f x := by
    calc
      c • x = c • (c⁻¹ • (y - f x)) := congrArg (c • ·) hx.symm
      _ = y - f x := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hfx : ‖f x‖ ≤ δ * ‖x‖ := by
    simpa [hf0, dist_eq_norm] using hf.dist_le_mul x 0
  refine ⟨x, ?_, ?_⟩
  · rw [hcx, sub_add_cancel]
  · have hnorm : ‖c‖ * ‖x‖ ≤ ‖y‖ + δ * ‖x‖ := by
      calc
        ‖c‖ * ‖x‖ = ‖y - f x‖ := by rw [← hcx, norm_smul]
        _ ≤ ‖y‖ + ‖f x‖ := norm_sub_le _ _
        _ ≤ ‖y‖ + δ * ‖x‖ := by linarith
    apply (le_div_iff₀ (sub_pos.mpr hsep)).2
    nlinarith

section Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The rectangular commutator map is Lipschitz for Euclidean operator norms. -/
theorem rectangular_commutator_lipschitz
    (U : Matrix m m ℂ) (V : Matrix n n ℂ) :
    LipschitzWith (‖U‖₊ + ‖V‖₊) (fun X : Matrix m n ℂ ↦ U * X - X * V) := by
  apply LipschitzWith.of_dist_le_mul
  intro X X'
  rw [dist_eq_norm, dist_eq_norm]
  have hid : U * X - X * V - (U * X' - X' * V) =
      U * (X - X') - (X - X') * V := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [hid]
  calc
    ‖U * (X - X') - (X - X') * V‖ ≤ ‖U * (X - X')‖ + ‖(X - X') * V‖ :=
      norm_sub_le _ _
    _ ≤ ‖U‖ * ‖X - X'‖ + ‖X - X'‖ * ‖V‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = ↑(‖U‖₊ + ‖V‖₊) * ‖X - X'‖ := by
      simp only [NNReal.coe_add, coe_nnnorm]
      ring

/-- The Sylvester equation with separated scalar centers has a solution with the sharp
Neumann-series denominator. Both coefficient matrices may be nonnormal. -/
theorem exists_sylvester_solution
    (U : Matrix m m ℂ) (V : Matrix n n ℂ) (z w : ℂ)
    (hsep : ‖U‖ + ‖V‖ < ‖z - w‖) (Y : Matrix m n ℂ) :
    ∃ X : Matrix m n ℂ,
      (z - w) • X + U * X - X * V = Y ∧
      ‖X‖ ≤ ‖Y‖ / (‖z - w‖ - ‖U‖ - ‖V‖) := by
  obtain ⟨X, hX, hbound⟩ := exists_scalar_add_lipschitz_solution
    (fun X : Matrix m n ℂ ↦ U * X - X * V) (‖U‖₊ + ‖V‖₊)
    (rectangular_commutator_lipschitz U V) (by simp) (z - w)
    (by simpa using hsep) Y
  refine ⟨X, ?_, ?_⟩
  · simpa only [add_sub_assoc] using hX
  · simpa only [NNReal.coe_add, coe_nnnorm, sub_sub] using hbound

/-- The same estimate in the usual two-coefficient notation for the Sylvester equation. -/
theorem exists_sylvester_solution_scalar_centers
    (U : Matrix m m ℂ) (V : Matrix n n ℂ) (z w : ℂ)
    (hsep : ‖U‖ + ‖V‖ < ‖z - w‖) (Y : Matrix m n ℂ) :
    ∃ X : Matrix m n ℂ,
      (z • (1 : Matrix m m ℂ) + U) * X - X * (w • (1 : Matrix n n ℂ) + V) = Y ∧
      ‖X‖ ≤ ‖Y‖ / (‖z - w‖ - ‖U‖ - ‖V‖) := by
  obtain ⟨X, hX, hbound⟩ := exists_sylvester_solution U V z w hsep Y
  refine ⟨X, ?_, hbound⟩
  calc
    (z • (1 : Matrix m m ℂ) + U) * X - X * (w • (1 : Matrix n n ℂ) + V) =
        (z - w) • X + U * X - X * V := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, sub_smul]
      abel
    _ = Y := hX

end Matrix

end NoEpsilon
