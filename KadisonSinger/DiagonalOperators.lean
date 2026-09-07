import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# Diagonal operators on the canonical countable Hilbert space
-/

noncomputable section
open scoped BigOperators ComplexOrder ENNReal

namespace KadisonSinger

abbrev Hilbert : Type := lp (fun _ : ℕ ↦ ℂ) 2
abbrev Operator := Hilbert →L[ℂ] Hilbert
abbrev Diagonal : Type := lp (fun _ : ℕ ↦ ℂ) ∞

def basisVector (i : ℕ) : Hilbert := lp.single 2 i 1

def matrixEntry (A : Operator) (i j : ℕ) : ℂ := A (basisVector j) i

@[simp] theorem basisVector_apply (i j : ℕ) : basisVector i j = if j = i then 1 else 0 := by
  by_cases h : j = i <;> simp [basisVector, lp.single_apply, h, Pi.single_apply]

@[simp] theorem norm_basisVector (i : ℕ) : ‖basisVector i‖ = 1 := by
  simp [basisVector, lp.norm_single]

private def diagonalAction (a : Diagonal) (x : Hilbert) : Hilbert :=
  ⟨fun i ↦ a i * x i,
    (lp.memℓp ((‖a‖ : ℂ) • x)).mono' fun i ↦ by
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_norm]
      exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero a i)
        (norm_nonneg _)⟩

private theorem diagonalAction_norm (a : Diagonal) (x : Hilbert) :
    ‖diagonalAction a x‖ ≤ ‖a‖ * ‖x‖ := by
  calc
    ‖diagonalAction a x‖ ≤ ‖(‖a‖ : ℂ) • x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      change ‖a i * x i‖ ≤ ‖(‖a‖ : ℂ) * x i‖
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
      exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero a i)
        (norm_nonneg _)
    _ = ‖a‖ * ‖x‖ := by
      rw [norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]

private def diagonalLinear (a : Diagonal) : Hilbert →ₗ[ℂ] Hilbert where
  toFun := diagonalAction a
  map_add' x y := by
    ext i
    change a i * (x i + y i) = a i * x i + a i * y i
    ring
  map_smul' c x := by ext i; simp [diagonalAction, mul_left_comm]

private def diagonalOperator (a : Diagonal) : Operator :=
  (diagonalLinear a).mkContinuous ‖a‖ (diagonalAction_norm a)

@[simp] private theorem diagonalOperator_apply (a : Diagonal) (x : Hilbert) (i : ℕ) :
    diagonalOperator a x i = a i * x i := rfl

private theorem diagonalOperator_star (a : Diagonal) :
    diagonalOperator (star a) = star (diagonalOperator a) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  funext i
  have h := ContinuousLinearMap.adjoint_inner_right (diagonalOperator a) (basisVector i) x
  change inner ℂ (basisVector i) ((star (diagonalOperator a)) x) =
    inner ℂ (diagonalOperator a (basisVector i)) x at h
  have hb : diagonalOperator a (basisVector i) = (a i) • basisVector i := by
    ext j
    by_cases hij : j = i <;> simp [hij]
  rw [hb, inner_smul_left] at h
  simpa [basisVector, diagonalOperator_apply, lp.inner_single_left] using h.symm

/-- Multiplication by bounded sequences, represented as bounded operators on `ℓ²(ℕ)`. -/
def diagonalRepresentation : Diagonal →⋆ₐ[ℂ] Operator where
  toFun := diagonalOperator
  map_zero' := by ext x i; change (0 : ℂ) * x i = 0; simp
  map_one' := by ext x i; simp
  map_add' a b := by
    ext x i
    change (a i + b i) * x i = a i * x i + b i * x i
    ring
  map_mul' a b := by ext x i; simp [mul_assoc]
  commutes' c := by ext x i; simp [Algebra.algebraMap_eq_smul_one]
  map_star' := diagonalOperator_star

@[simp] theorem diagonalRepresentation_apply (a : Diagonal) (x : Hilbert) (i : ℕ) :
    diagonalRepresentation a x i = a i * x i := rfl

/-- The characteristic sequence of one color class. -/
def colorIndicator {r : ℕ} (c : ℕ → Fin r) (j : Fin r) : Diagonal :=
  ⟨fun i ↦ if c i = j then 1 else 0, memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩
    dsimp
    split_ifs <;> simp⟩⟩

@[simp] theorem colorIndicator_apply {r : ℕ} (c : ℕ → Fin r) (j : Fin r) (i : ℕ) :
    colorIndicator c j i = if c i = j then 1 else 0 := rfl

theorem colorIndicator_projection {r : ℕ} (c : ℕ → Fin r) (j : Fin r) :
    IsStarProjection (colorIndicator c j) := by
  constructor
  · ext i
    by_cases h : c i = j <;> simp [h]
  · change star (colorIndicator c j) = colorIndicator c j
    ext i
    by_cases h : c i = j <;> simp [h]

theorem sum_colorIndicator {r : ℕ} (c : ℕ → Fin r) :
    ∑ j, colorIndicator c j = 1 := by
  ext i
  simp only [lp.coeFn_sum, Finset.sum_apply, colorIndicator_apply,
    lp.infty_coeFn_one, Pi.one_apply]
  simp [eq_comm]

end KadisonSinger
