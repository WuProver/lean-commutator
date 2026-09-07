import KadisonSinger.DiagonalEmbedding
import KadisonSinger.DiagonalExpectation

/-!
# Identification of the usual diagonal operator algebra

The bounded-sequence representation has exactly the bounded operators whose matrix,
in the canonical orthonormal basis, vanishes off the diagonal.
-/

noncomputable section
open scoped ENNReal

namespace KadisonSinger

/-- A bounded operator on `ℓ²(ℕ)` is determined by its canonical matrix entries. -/
theorem operator_ext_matrixEntry {A B : Operator}
    (h : ∀ i j, matrixEntry A i j = matrixEntry B i j) : A = B := by
  apply lp.ext_continuousLinearMap (𝕜 := ℂ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro j
  apply ContinuousLinearMap.ext
  intro z
  apply Subtype.ext
  funext i
  change A (lp.single 2 j z) i = B (lp.single 2 j z) i
  have hz : lp.single (E := fun _ : ℕ ↦ ℂ) 2 j z = z • basisVector j := by
    simp [basisVector, ← lp.single_smul]
  rw [hz, map_smul, map_smul]
  change z * matrixEntry A i j = z * matrixEntry B i j
  rw [h]

/-- A coordinate-diagonal operator is multiplication by its bounded diagonal sequence. -/
theorem diagonalRepresentation_expectation_of_offDiagonal_zero (A : Operator)
    (h : ∀ i j, i ≠ j → matrixEntry A i j = 0) :
    diagonalRepresentation (diagonalExpectation A) = A := by
  apply operator_ext_matrixEntry
  intro i j
  rw [diagonalRepresentation_matrixEntry]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, h i j hij]

/-- The representation identifies bounded sequences with precisely the usual diagonal operators. -/
theorem mem_range_diagonalRepresentation_iff (A : Operator) :
    A ∈ Set.range diagonalRepresentation ↔ ∀ i j, i ≠ j → matrixEntry A i j = 0 := by
  constructor
  · rintro ⟨a, rfl⟩ i j hij
    simp [hij]
  · intro h
    exact ⟨diagonalExpectation A, diagonalRepresentation_expectation_of_offDiagonal_zero A h⟩

end KadisonSinger
