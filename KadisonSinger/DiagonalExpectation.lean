import KadisonSinger.DiagonalOperators
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# The positive diagonal expectation

The bounded diagonal sequence of a bounded operator defines a positive unital linear map, left
inverse to the diagonal representation. The order on bounded sequences is the pointwise order.
-/

noncomputable section
open scoped ComplexOrder ENNReal

namespace KadisonSinger

instance diagonalPartialOrder : PartialOrder Diagonal :=
  PartialOrder.lift (fun d : Diagonal ↦ (d : ℕ → ℂ)) (fun _ _ h ↦ lp.ext h)

@[simp] theorem diagonal_le_iff (a b : Diagonal) : a ≤ b ↔ ∀ i, a i ≤ b i := Iff.rfl

/-- The square root of a pointwise nonnegative bounded diagonal sequence is bounded. -/
private def diagonalSqrt (a : Diagonal) : Diagonal :=
  ⟨fun i ↦ (Real.sqrt (a i).re : ℂ), memℓp_infty ⟨Real.sqrt ‖a‖, by
    rintro _ ⟨i, rfl⟩
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((Complex.re_le_norm (a i)).trans
      (lp.norm_apply_le_norm ENNReal.top_ne_zero a i))⟩⟩

instance diagonalStarOrderedRing : StarOrderedRing Diagonal :=
  StarOrderedRing.of_nonneg_iff'
    (by
      intro x y h z i
      change z i + x i ≤ z i + y i
      exact add_le_add_right (h i) (z i)) (fun a ↦ by
      constructor
      · intro ha
        refine ⟨diagonalSqrt a, ?_⟩
        ext i
        have hi := Complex.nonneg_iff.mp (ha i)
        change a i = star (Real.sqrt (a i).re : ℂ) * (Real.sqrt (a i).re : ℂ)
        apply Complex.ext
        · simp [Real.mul_self_sqrt hi.1]
        · simpa using hi.2.symm
      · rintro ⟨s, rfl⟩ i
        exact star_mul_self_nonneg (s i))

/-- Each diagonal coefficient of a bounded operator is bounded by its operator norm. -/
theorem norm_matrixEntry_diagonal_le (T : Operator) (i : ℕ) :
    ‖matrixEntry T i i‖ ≤ ‖T‖ := by
  calc
    ‖matrixEntry T i i‖ ≤ ‖T (basisVector i)‖ :=
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ _
    _ ≤ ‖T‖ * ‖basisVector i‖ := T.le_opNorm _
    _ = ‖T‖ := by rw [norm_basisVector, mul_one]

/-- The bounded sequence consisting of the diagonal entries of an operator. -/
def diagonalSequence (T : Operator) : Diagonal :=
  ⟨fun i ↦ matrixEntry T i i, memℓp_infty ⟨‖T‖, by
    rintro _ ⟨i, rfl⟩
    exact norm_matrixEntry_diagonal_le T i⟩⟩

@[simp] theorem diagonalSequence_apply (T : Operator) (i : ℕ) :
    diagonalSequence T i = matrixEntry T i i := rfl

/-- The standard diagonal expectation, viewed as a positive linear map into bounded sequences. -/
def diagonalExpectation : Operator →ₚ[ℂ] Diagonal :=
  PositiveLinearMap.mk₀
    { toFun := diagonalSequence
      map_add' := by intro S T; ext i; rfl
      map_smul' := by intro c T; ext i; simp [diagonalSequence, matrixEntry] }
    (by
      intro T hT i
      have h := ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT).inner_nonneg_right
        (basisVector i)
      simpa [diagonalSequence, matrixEntry, basisVector, lp.inner_single_left] using h)

@[simp] theorem diagonalExpectation_apply (T : Operator) (i : ℕ) :
    diagonalExpectation T i = matrixEntry T i i := rfl

@[simp] theorem diagonalExpectation_one : diagonalExpectation 1 = 1 := by
  ext i
  simp [matrixEntry]

@[simp] theorem diagonalExpectation_representation (d : Diagonal) :
    diagonalExpectation (diagonalRepresentation d) = d := by
  ext i
  simp [matrixEntry]

end KadisonSinger
