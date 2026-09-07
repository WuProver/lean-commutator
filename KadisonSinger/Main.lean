import KadisonSinger.OperatorPaving
import KadisonSinger.DiagonalExpectation
import KadisonSinger.PureExtension
import KadisonSinger.DiagonalEmbedding

/-!
# The Kadison--Singer theorem

Every pure state of the bounded diagonal operators on `ℓ²(ℕ)` has a unique
state extension to all bounded operators, and that extension is pure.

The diagonal algebra is represented by bounded complex sequences with their
supremum norm; `diagonalRepresentation` is its faithful isometric representation.
The proof discharges paving using finite MSS selection, finite matrix paving,
Rado compactness, and the finite-section characterization of operator norm.
-/

noncomputable section
open scoped BigOperators ComplexOrder

namespace KadisonSinger

/-- The standard diagonal expectation satisfies self-adjoint projection paving. -/
theorem diagonal_selfAdjoint_paving :
    SelfAdjointProjectionPaving diagonalRepresentation diagonalExpectation := by
  intro A hA hdiag ε hε
  have hpos : 0 < ‖A‖ + 1 := by positivity
  obtain ⟨r, _, hp⟩ := selfAdjoint_operator_paving
    (ε / (‖A‖ + 1)) (div_pos hε hpos)
  have hz (i : ℕ) : matrixEntry A i i = 0 := by
    have hi := congrArg (fun d : Diagonal ↦ d i) hdiag
    simpa using hi
  obtain ⟨c, hc⟩ := hp A hA hz
  refine ⟨r, colorIndicator c, colorIndicator_projection c, sum_colorIndicator c, fun j ↦ ?_⟩
  apply (hc j).trans
  calc
    ε / (‖A‖ + 1) * ‖A‖ = (ε * ‖A‖) / (‖A‖ + 1) := by ring
    _ ≤ ε := (div_le_iff₀ hpos).mpr (by nlinarith)

/-- A pure state on the diagonal algebra has a unique extension among all states
on the bounded operators on `ℓ²(ℕ)`. No paving or extension hypothesis remains. -/
theorem kadison_singer_state_extension (φ : State Diagonal) (hφ : φ.IsPure) :
    ∃! ψ : State Operator, ∀ d : Diagonal,
      ψ.val (diagonalRepresentation d) = φ.val d :=
  State.existsUnique_extension_of_selfAdjoint_paving diagonalRepresentation diagonalExpectation
    diagonalExpectation_one diagonalExpectation_representation diagonal_selfAdjoint_paving φ hφ

/-- The Kadison--Singer theorem in its original pure-state extension formulation. -/
theorem kadison_singer (φ : State Diagonal) (hφ : φ.IsPure) :
    ∃! ψ : State Operator, ψ.IsPure ∧ ∀ d : Diagonal,
      ψ.val (diagonalRepresentation d) = φ.val d :=
  State.existsUnique_pure_extension diagonalRepresentation φ hφ
    (kadison_singer_state_extension φ hφ)

end KadisonSinger
