import CommutatorTheorem.NoEpsilon.CyclicCommutator
import CommutatorTheorem.NoEpsilon.NormBounds

/-!
# The bounded identity-corner theorem without an auxiliary commutator hypothesis

The adaptive two-commutator input is discharged by the proved Hermitian and cyclic
construction. The final theorem assumes only the trace and Euclidean operator norm
conditions on the whole identity-corner matrix.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace NoEpsilon

/-- The bounded core theorem with no supplied first factors or two-commutator hypothesis. -/
theorem identityCorner_bounded_from_trace (n : ℕ) (A F D : Matrix (Fin n) (Fin n) ℂ)
    (a : ℝ) (hTrace : Matrix.trace (A + D) = 0)
    (hA : ‖A‖ ≤ a) (hF : ‖F‖ ≤ a) (hD : ‖D‖ ≤ a) :
    ∃ B C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ,
      identityCorner A F D = ringCommutator B C ∧
        ‖B‖ * ‖C‖ ≤ identityCornerNormBudget a := by
  obtain ⟨U, K, V, T, _, _, hSum, hU, hK, hV, hT⟩ :=
    adaptiveTwoCommutatorBound n (A + D) hTrace
  have hAD : ‖A + D‖ ≤ 2 * a := by
    have h := norm_add_le A D
    linarith
  exact exists_identityCorner_commutator_bounded A F D U K V T a hA hF hD hU hK
    (hV.trans hAD) (hT.trans hAD) hSum

section Compression

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem norm_compression_sandwich_le (E F : Matrix (ι ⊕ ι) ι ℂ)
    (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (hE : ‖E‖ ≤ 1) (hF : ‖F‖ ≤ 1) :
    ‖Eᴴ * M * F‖ ≤ ‖M‖ := by
  calc
    ‖Eᴴ * M * F‖ ≤ ‖Eᴴ * M‖ * ‖F‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖E‖ * ‖M‖) * ‖F‖ := by
      rw [← Matrix.l2_opNorm_conjTranspose E]
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by gcongr
    _ = ‖M‖ := by ring

/-- The three target blocks are genuine contractive compressions in operator norm. -/
theorem identityCorner_block_norms_le (A F D : Matrix ι ι ℂ) :
    ‖A‖ ≤ ‖identityCorner A F D‖ ∧ ‖F‖ ≤ ‖identityCorner A F D‖ ∧
      ‖D‖ ≤ ‖identityCorner A F D‖ := by
  let E := Matrix.fromRows (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)
  let J := Matrix.fromRows (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
  have hE : ‖E‖ ≤ 1 := norm_rowEmbedding_left_le
  have hJ : ‖J‖ ≤ 1 := norm_rowEmbedding_right_le
  have hA : Eᴴ * identityCorner A F D * E = A := by
    simp [E, identityCorner, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  have hF : Jᴴ * identityCorner A F D * E = F := by
    simp [E, J, identityCorner, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  have hD : Jᴴ * identityCorner A F D * J = D := by
    simp [J, identityCorner, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hA] using norm_compression_sandwich_le E E (identityCorner A F D) hE hE
  · simpa only [hF] using norm_compression_sandwich_le J E (identityCorner A F D) hJ hE
  · simpa only [hD] using norm_compression_sandwich_le J J (identityCorner A F D) hJ hJ

theorem trace_identityCorner (A F D : Matrix ι ι ℂ) :
    Matrix.trace (identityCorner A F D) = Matrix.trace (A + D) := by
  simp [identityCorner, Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks,
    Finset.sum_add_distrib]

end Compression

/-- The paper interface: only the trace and norm of the whole matrix are assumed.
The factors remain indexed by the same `Fin n ⊕ Fin n` as the target. -/
theorem identityCorner_bounded_from_whole_norm (n : ℕ)
    (A F D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ)
    (hTrace : Matrix.trace (identityCorner A F D) = 0)
    (hNorm : ‖identityCorner A F D‖ ≤ a) :
    ∃ B C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ,
      identityCorner A F D = ringCommutator B C ∧
        ‖B‖ * ‖C‖ ≤ identityCornerNormBudget a := by
  obtain ⟨hA, hF, hD⟩ := identityCorner_block_norms_le A F D
  rw [trace_identityCorner] at hTrace
  exact identityCorner_bounded_from_trace n A F D a hTrace
    (hA.trans hNorm) (hF.trans hNorm) (hD.trans hNorm)

end NoEpsilon
