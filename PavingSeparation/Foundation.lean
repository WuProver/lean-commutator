import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Elementary matrix and Frobenius norm lemmas

These elementary lemmas are copied from the parent project into the standalone package.
No parent project theorem or additional axiom is used.
-/

-- Enable the L2 operator norm on square complex matrices
attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing

namespace PavingSeparation.Foundation

/-! ## Commutator bracket -/

/-- The matrix commutator [A, B] = AB - BA. -/
noncomputable def matComm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

notation:65 "⁅" A ", " B "⁆ₘ" => matComm A B

/-! ## Zero-diagonal predicate -/

/-- A matrix has zero diagonal if all diagonal entries vanish. -/
def ZeroDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i, A i i = 0

/-- A matrix is diagonal if all off-diagonal entries vanish. -/
def IsDiagMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j : Fin n, i ≠ j → A i j = 0

/-! ## Operator norm bridge lemma -/

/-- The default norm on `Matrix (Fin n) (Fin n) ℂ` (from `Matrix.instL2OpNormedRing`)
    equals the operator norm of the corresponding continuous linear map. -/
lemma matOpNorm_eq_clm_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A‖ = ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖ :=
  Matrix.l2_opNorm_def A

/-! ## Hilbert-Schmidt norm -/

/-- The Hilbert-Schmidt (Frobenius) norm of a matrix,
    defined as the square root of the sum of squared entry absolute values.
    We define it directly as a `def` (not via a `NormedSpace` instance)
    to avoid conflicts with the L2 operator norm instance. -/
noncomputable def hsNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j))

scoped[PavingSeparation.Foundation] notation:max "‖" A "‖ₕₛ" => hsNorm A

lemma hsNorm_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsNorm A := by
  unfold hsNorm
  exact Real.sqrt_nonneg _

lemma hsNorm_zero {n : ℕ} : hsNorm (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  unfold hsNorm
  simp [Complex.normSq_zero]

lemma hsNorm_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    hsNorm (c • A) = ‖c‖ * hsNorm A := by
  simp only [hsNorm, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, ← Finset.mul_sum]
  rw [Real.sqrt_mul (Complex.normSq_nonneg c), Complex.norm_def]

private lemma complex_normSq_sum_mul_le {n : ℕ} (f g : Fin n → ℂ) :
    Complex.normSq (∑ j, f j * g j) ≤
      (∑ j, Complex.normSq (f j)) * (∑ j, Complex.normSq (g j)) := by
  calc Complex.normSq (∑ j, f j * g j)
      = ‖∑ j, f j * g j‖ ^ 2 := by rw [Complex.normSq_eq_norm_sq]
    _ ≤ (∑ j, ‖f j * g j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ = (∑ j, ‖f j‖ * ‖g j‖) ^ 2 := by
        congr 1; congr 1; ext j; exact norm_mul _ _
    _ ≤ (∑ j, ‖f j‖ ^ 2) * (∑ j, ‖g j‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ j, Complex.normSq (f j)) * (∑ j, Complex.normSq (g j)) := by
        congr 1 <;> (congr 1; ext j; rw [Complex.normSq_eq_norm_sq])

/-- The operator norm is at most the Hilbert-Schmidt norm. -/
lemma le_hsNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ≤ hsNorm A := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (hsNorm_nonneg A)
  intro x
  simp only [LinearEquiv.trans_apply]
  change ‖Matrix.toEuclideanLin A x‖ ≤ hsNorm A * ‖x‖
  rw [show Matrix.toEuclideanLin A x = WithLp.toLp 2 (A.mulVec x.ofLp) from
    Matrix.toLpLin_apply 2 2 A x]
  set v := x.ofLp
  set w := A.mulVec v
  apply le_of_sq_le_sq _ (mul_nonneg (hsNorm_nonneg A) (norm_nonneg x))
  have norm_x_sq : ‖x‖ ^ 2 = ∑ j, Complex.normSq (v j) := by
    rw [EuclideanSpace.norm_eq x,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ pow_nonneg (norm_nonneg _) 2))]
    congr 1; ext j; rw [Complex.normSq_eq_norm_sq]
  rw [show ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ =
      Real.sqrt (∑ i, ‖w i‖ ^ 2) from EuclideanSpace.norm_eq _,
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ pow_nonneg (norm_nonneg _) 2)),
      mul_pow,
      show hsNorm A ^ 2 = ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j) from by
        unfold hsNorm; rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦
          Finset.sum_nonneg (fun j _ ↦ Complex.normSq_nonneg _)))],
      norm_x_sq]
  have hw : ∀ i, ‖w i‖ ^ 2 = Complex.normSq (∑ j, A i j * v j) := by
    intro i; rw [← Complex.normSq_eq_norm_sq]; rfl
  simp_rw [hw]
  calc ∑ i, Complex.normSq (∑ j, A i j * v j)
      ≤ ∑ i, (∑ j, Complex.normSq (A i j)) * (∑ j, Complex.normSq (v j)) :=
        Finset.sum_le_sum (fun i _ ↦ complex_normSq_sum_mul_le _ _)
    _ = _ := by rw [← Finset.sum_mul]

/-- The Hilbert-Schmidt norm is at most √n times the operator norm. -/
lemma hsNorm_le_sqrt_n_mul_opNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    hsNorm A ≤ Real.sqrt n * ‖A‖ := by
  unfold hsNorm
  rw [show Real.sqrt ↑n * ‖A‖ = Real.sqrt (↑n * ‖A‖ ^ 2) from by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg A)]]
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_comm]
  have hcol : ∀ j : Fin n, ∑ i, Complex.normSq (A i j) ≤ ‖A‖ ^ 2 := by
    intro j
    set f := (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A
    set ej := EuclideanSpace.single j (1 : ℂ)
    have hfej : ‖f ej‖ ≤ ‖A‖ := by
      calc ‖f ej‖ ≤ ‖f‖ * ‖ej‖ := ContinuousLinearMap.le_opNorm f ej
        _ = ‖A‖ * 1 := by rw [← Matrix.l2_opNorm_def, PiLp.norm_single 2, norm_one]
        _ = ‖A‖ := mul_one _
    suffices h : ∑ i, Complex.normSq (A i j) = ‖f ej‖ ^ 2 by
      rw [h]; exact pow_le_pow_left₀ (norm_nonneg _) hfej 2
    have : f ej = WithLp.toLp 2 (A.mulVec (Pi.single j 1)) := by
      change (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A ej = _
      simp [LinearEquiv.trans_apply, Matrix.toLpLin_apply, ej, EuclideanSpace.single]
    rw [this, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ pow_nonneg (norm_nonneg _) 2))]
    congr 1; ext i
    rw [Complex.normSq_eq_norm_sq]
    congr 1
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
  calc ∑ j : Fin n, ∑ i, Complex.normSq (A i j)
      ≤ ∑ _j : Fin n, ‖A‖ ^ 2 := Finset.sum_le_sum (fun j _ ↦ hcol j)
    _ = ↑n * ‖A‖ ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The square normalization used for the fixed-dimensional existence bound. -/
def InUnitSquare (z : ℂ) : Prop := |z.re| ≤ 1 ∧ |z.im| ≤ 1

end PavingSeparation.Foundation
