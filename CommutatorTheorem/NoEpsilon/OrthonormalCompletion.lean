import CommutatorTheorem.NoEpsilon.HighMassBridge
import Mathlib.LinearAlgebra.Matrix.BaseChange
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Completing a rectangular isometry

An orthonormal family is completed on a sum index whose right summand has exactly the
remaining dimension. No additional zero coordinates are added to the ambient space.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
/-- Complete a prescribed orthonormal family, preserving the original order of its columns. -/
theorem exists_orthonormalBasis_sum_extension (p : κ → EuclideanSpace ℂ ι)
    (hp : Orthonormal ℂ p) :
    ∃ b : OrthonormalBasis (κ ⊕ Fin (Fintype.card ι - Fintype.card κ)) ℂ
      (EuclideanSpace ℂ ι), ∀ i, b (Sum.inl i) = p i := by
  classical
  have hCard : Fintype.card κ ≤ Fintype.card ι := by
    simpa only [finrank_euclideanSpace] using hp.linearIndependent.fintype_card_le_finrank
  let p' : κ ⊕ Fin (Fintype.card ι - Fintype.card κ) → EuclideanSpace ℂ ι :=
    Sum.elim p (fun _ ↦ 0)
  let s : Set (κ ⊕ Fin (Fintype.card ι - Fintype.card κ)) := Set.range Sum.inl
  have hp' : Orthonormal ℂ (s.restrict p') := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, ⟨i', rfl⟩⟩ ⟨j, ⟨j', rfl⟩⟩
    simpa only [Set.restrict_apply, p', Sum.elim_inl, Subtype.mk.injEq, Sum.inl.injEq] using
      (orthonormal_iff_ite.mp hp i' j')
  have hDim : Module.finrank ℂ (EuclideanSpace ℂ ι) =
      Fintype.card (κ ⊕ Fin (Fintype.card ι - Fintype.card κ)) := by
    simp only [finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨b, hb⟩ := hp'.exists_orthonormalBasis_extension_of_card_eq hDim
  exact ⟨b, fun i ↦ hb (Sum.inl i) ⟨i, rfl⟩⟩

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- The columns of a rectangular isometry form an orthonormal family in Euclidean space. -/
theorem orthonormal_columns_of_isometry (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) :
    Orthonormal ℂ (fun j ↦ (WithLp.toLp 2 (fun i ↦ V i j) : EuclideanSpace ℂ ι)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrArg (fun M : Matrix κ κ ℂ ↦ M i j) hV
  have hGram := familyMatrix_gram_entry
    (fun j ↦ (WithLp.toLp 2 (fun i ↦ V i j) : EuclideanSpace ℂ ι))
    (fun j ↦ (WithLp.toLp 2 (fun i ↦ V i j) : EuclideanSpace ℂ ι)) i j
  change (Vᴴ * V) i j = _ at hGram
  rw [← hGram, hV, Matrix.one_apply]

/-- A complete orthonormal basis gives inverse rectangular change-of-coordinate matrices. -/
theorem basisMatrix_unitary (b : OrthonormalBasis κ ℂ (EuclideanSpace ℂ ι)) :
    (familyMatrix b)ᴴ * familyMatrix b = 1 ∧ familyMatrix b * (familyMatrix b)ᴴ = 1 := by
  have hLeft := familyMatrix_isometry b b.orthonormal
  have hCard : Fintype.card ι = Fintype.card κ := by
    simpa only [finrank_euclideanSpace] using Module.finrank_eq_card_basis b.toBasis
  exact ⟨hLeft, (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hCard.symm)).mp hLeft⟩

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
/-- Complete two orthogonal isometries, placing `Q` first and `P` second in the core. -/
theorem orthogonal_pair_basis_completion {r : ℕ} (P Q : Matrix ι (Fin r) ℂ)
    (hP : Pᴴ * P = 1) (hQ : Qᴴ * Q = 1) (hPQ : Pᴴ * Q = 0) :
    ∃ (m : ℕ) (b : OrthonormalBasis ((Fin r ⊕ Fin r) ⊕ Fin m) ℂ (EuclideanSpace ℂ ι)),
      2 * r + m = Fintype.card ι ∧
      (∀ i, b (Sum.inl (Sum.inl i)) = WithLp.toLp 2 (fun j ↦ Q j i)) ∧
      (∀ i, b (Sum.inl (Sum.inr i)) = WithLp.toLp 2 (fun j ↦ P j i)) := by
  classical
  have hQP : Qᴴ * P = 0 := by
    have h := congrArg Matrix.conjTranspose hPQ
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using h
  let V : Matrix ι (Fin r ⊕ Fin r) ℂ := Matrix.fromCols Q P
  have hV : Vᴴ * V = 1 := by
    simp only [V, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols, hP, hQ, hPQ, hQP, Matrix.fromBlocks_one]
  let p : (Fin r ⊕ Fin r) → EuclideanSpace ℂ ι :=
    fun i ↦ WithLp.toLp 2 (fun j ↦ V j i)
  have hp : Orthonormal ℂ p := orthonormal_columns_of_isometry V hV
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_sum_extension p hp
  have hCard : 2 * r ≤ Fintype.card ι := by
    have h := hp.linearIndependent.fintype_card_le_finrank
    simpa only [Fintype.card_sum, Fintype.card_fin, finrank_euclideanSpace, two_mul] using h
  refine ⟨Fintype.card ι - Fintype.card (Fin r ⊕ Fin r), b, ?_, ?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · intro i
    exact hb (Sum.inl i)
  · intro i
    exact hb (Sum.inr i)

end NoEpsilon
