import CommutatorTheorem.NoEpsilon.Goal

/-!
# Semantic checks for the exact target

These equivalences spell out the induced Euclidean operator norm and preserve the
original matrix index type in both factors. They prove that the target is neither
an entrywise norm estimate nor a stabilization to a larger matrix space.
-/

namespace NoEpsilon

open scoped Matrix.Norms.L2Operator

/-- The norm in the final target is definitionally the induced Euclidean operator norm. -/
theorem uniformCommutatorBound_iff_euclideanOperatorNorm :
    UniformCommutatorBound ↔
      ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        Matrix.trace A = 0 →
          ∃ B C : Matrix (Fin n) (Fin n) ℂ,
            A = B * C - C * B ∧
            ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B‖ *
              ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) C‖ ≤
              K * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ := Iff.rfl

/-- A witness to the target gives two endomorphisms of the same Euclidean space,
with their actual continuous-linear-map operator norms. -/
theorem sameSpace_operator_commutator_of_uniform_bound (h : UniformCommutatorBound) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace A = 0 →
        ∃ B C : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
          Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤
            K * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ := by
  obtain ⟨K, hK, h⟩ := uniformCommutatorBound_iff_euclideanOperatorNorm.mp h
  refine ⟨K, hK, ?_⟩
  intro n A hA
  obtain ⟨B, C, hBC, hn⟩ := h n A hA
  refine ⟨Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B,
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) C, ?_, hn⟩
  rw [hBC, map_sub, map_mul, map_mul]

end NoEpsilon
