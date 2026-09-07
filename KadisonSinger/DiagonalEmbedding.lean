import KadisonSinger.DiagonalOperators
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Faithful isometric realization of the diagonal algebra

Bounded sequences act faithfully on the standard orthonormal basis of `ℓ²(ℕ)`.
Thus the chosen model of the diagonal algebra is isometrically the usual algebra
of bounded diagonal operators.
-/

noncomputable section
namespace KadisonSinger

@[simp] theorem diagonalRepresentation_matrixEntry (a : Diagonal) (i j : ℕ) :
    matrixEntry (diagonalRepresentation a) i j = if i = j then a i else 0 := by
  simp only [matrixEntry, diagonalRepresentation_apply, basisVector_apply]
  split_ifs <;> simp

/-- The representation is faithful: its values on basis vectors recover every coordinate. -/
theorem diagonalRepresentation_injective : Function.Injective diagonalRepresentation := by
  intro a b hab
  apply Subtype.ext
  funext i
  have h := congrArg (fun T : Operator ↦ matrixEntry T i i) hab
  simpa only [diagonalRepresentation_matrixEntry, if_pos rfl] using h

/-- The operator norm of a diagonal operator is the supremum norm of its diagonal. -/
@[simp] theorem norm_diagonalRepresentation (a : Diagonal) :
    ‖diagonalRepresentation a‖ = ‖a‖ := by
  letI : CStarAlgebra Operator := {}
  exact NonUnitalStarAlgHom.norm_map diagonalRepresentation diagonalRepresentation_injective a

/-- The bounded diagonal operators are realized as an isometric subalgebra. -/
theorem diagonalRepresentation_isometry : Isometry diagonalRepresentation := by
  letI : CStarAlgebra Operator := {}
  exact NonUnitalStarAlgHom.isometry diagonalRepresentation diagonalRepresentation_injective

end KadisonSinger
