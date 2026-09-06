import CommutatorTheorem.NoEpsilon.GlobalReduction

/-! # Generic coordinate conversion for a paved orthonormal basis

The block count is a symbolic parameter here, so specializing the theorem does not
ask the elaborator to enumerate a large closed finite index type.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator

theorem paving_basis_to_blocks_generic {R k : ℕ}
    (A : Matrix (Fin (k * R)) (Fin (k * R)) ℂ)
    (b : OrthonormalBasis (Fin R × Fin k) ℂ
      (EuclideanSpace ℂ (Fin (k * R))))
    (θ : ℝ) (hb : ∀ i, let W := familyMatrix (fun j ↦ b (i, j))
      Matrix.trace (Wᴴ * A * W) = 0 ∧ ‖Wᴴ * A * W‖ ≤ θ) :
    ∃ U : Matrix (Fin (k * R)) (Sigma fun _ : Fin R ↦ Fin k) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ ∀ i,
        Matrix.trace (BlockAssembly.block (Uᴴ * A * U) i i) = 0 ∧
          ‖BlockAssembly.block (Uᴴ * A * U) i i‖ ≤ θ := by
  let b' := b.reindex (Equiv.sigmaEquivProd (Fin R) (Fin k)).symm
  refine ⟨familyMatrix b', (basisMatrix_unitary b').1, (basisMatrix_unitary b').2, ?_⟩
  intro i
  have heq : BlockAssembly.block ((familyMatrix b')ᴴ * A * familyMatrix b') i i =
      (familyMatrix (fun j ↦ b (i, j)))ᴴ * A * familyMatrix (fun j ↦ b (i, j)) := by
    ext j l
    change ((familyMatrix b')ᴴ * A * familyMatrix b') ⟨i, j⟩ ⟨i, l⟩ = _
    rw [familyMatrix_compression_entry, familyMatrix_compression_entry]
    dsimp only [b']
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.reindex_apply]
    rfl
  rw [heq]
  exact hb i

end NoEpsilon
