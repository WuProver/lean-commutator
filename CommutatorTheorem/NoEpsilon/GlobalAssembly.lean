import CommutatorTheorem.NoEpsilon.UnitaryCoordinates
import CommutatorTheorem.NoEpsilon.BlockAssembly

/-! # Assembly after changing coordinates in the divisible part

The leftover coordinates remain individual zero diagonal blocks. This permits one
application of the fixed assembly estimate even when the original dimension is not divisible.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator

theorem unitary_commutator_pullback {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (U : Matrix n m ℂ) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (A : Matrix n n ℂ) (p : ℝ)
    (h : ∃ B C : Matrix m m ℂ, Uᴴ * A * U = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ p) :
    ∃ B C : Matrix n n ℂ, A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ p := by
  obtain ⟨B, C, hBC, hBound⟩ := h
  have hAdj : (Uᴴ)ᴴ * Uᴴ = 1 := by simpa using hU'
  refine ⟨U * B * Uᴴ, U * C * Uᴴ, ?_, ?_⟩
  · rw [rectangular_unitary_conjugate_mul U hU,
      rectangular_unitary_conjugate_mul U hU, ← Matrix.sub_mul, ← Matrix.mul_sub, ← hBC]
    calc
      A = (U * Uᴴ) * A * (U * Uᴴ) := by rw [hU', Matrix.one_mul, Matrix.mul_one]
      _ = U * (Uᴴ * A * U) * Uᴴ := by simp only [Matrix.mul_assoc]
  · have hB : ‖U * B * Uᴴ‖ ≤ ‖B‖ := by
      simpa using isometry_compression_norm_le Uᴴ hAdj B
    have hC : ‖U * C * Uᴴ‖ ≤ ‖C‖ := by
      simpa using isometry_compression_norm_le Uᴴ hAdj C
    exact (mul_le_mul hB hC (norm_nonneg _) (norm_nonneg _)).trans hBound

namespace GlobalAssembly

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (d : ι → Type) [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

abbrev appendShape (q : ℕ) : ι ⊕ Fin q → Type := Sum.elim d (fun _ ↦ Fin 1)

instance {q : ℕ} (i : ι ⊕ Fin q) : Fintype (appendShape d q i) := by
  cases i <;> dsimp [appendShape] <;> infer_instance

instance {q : ℕ} (i : ι ⊕ Fin q) : DecidableEq (appendShape d q i) := by
  cases i <;> dsimp [appendShape] <;> infer_instance

def appendEquiv (q : ℕ) : Sigma (appendShape d q) ≃ (Sigma d) ⊕ Fin q where
  toFun x := match x with
    | ⟨Sum.inl i, j⟩ => Sum.inl ⟨i, j⟩
    | ⟨Sum.inr i, _⟩ => Sum.inr i
  invFun x := match x with
    | Sum.inl ⟨i, j⟩ => ⟨Sum.inl i, j⟩
    | Sum.inr i => ⟨Sum.inr i, (0 : Fin 1)⟩
  left_inv x := by
    rcases x with ⟨i, j⟩
    cases i with
    | inl i => rfl
    | inr i => simp [Fin.eq_zero j]
  right_inv x := by cases x <;> rfl

variable {d}

def extendUnitary {N q : ℕ} (U : Matrix (Fin N) (Sigma d) ℂ) :
    Matrix (Fin N ⊕ Fin q) (Sigma d ⊕ Fin q) ℂ := Matrix.fromBlocks U 0 0 1

theorem extendUnitary_unitary {N q : ℕ} (U : Matrix (Fin N) (Sigma d) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) :
    (extendUnitary (q := q) U)ᴴ * extendUnitary (q := q) U = 1 ∧
      extendUnitary (q := q) U * (extendUnitary (q := q) U)ᴴ = 1 := by
  simp [extendUnitary, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    hU, hU', Matrix.fromBlocks_one]

theorem extendUnitary_compression {N q : ℕ} (U : Matrix (Fin N) (Sigma d) ℂ)
    (A : Matrix (Fin N ⊕ Fin q) (Fin N ⊕ Fin q) ℂ) :
    (extendUnitary (q := q) U)ᴴ * A * extendUnitary (q := q) U =
      Matrix.fromBlocks (Uᴴ * A.toBlocks₁₁ * U) (Uᴴ * A.toBlocks₁₂)
        (A.toBlocks₂₁ * U) A.toBlocks₂₂ := by
  conv_lhs => arg 1; arg 2; rw [← Matrix.fromBlocks_toBlocks A]
  simp [extendUnitary, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

set_option backward.isDefEq.respectTransparency false in
/-- Refine the large block by a unitary basis and keep every leftover coordinate as a
singleton. The fixed assembly cost is paid once for the whole original matrix. -/
theorem assemble_with_leftovers {N q : ℕ}
    (A : Matrix (Fin N ⊕ Fin q) (Fin N ⊕ Fin q) ℂ)
    (U : Matrix (Fin N) (Sigma d) ℂ) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hz : ∀ j : Fin q, A (Sum.inr j) (Sum.inr j) = 0)
    (p : ℝ) (hp : 0 ≤ p) (hCard : Fintype.card ι + q ≤ 2 * 2 ^ 26 - 1)
    (hDiag : ∀ i, ∃ B C : Matrix (d i) (d i) ℂ,
      BlockAssembly.block (Uᴴ * A.toBlocks₁₁ * U) i i = B * C - C * B ∧
        ‖B‖ * ‖C‖ ≤ p) :
    ∃ B C : Matrix (Fin N ⊕ Fin q) (Fin N ⊕ Fin q) ℂ,
      A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ 65536 * p + 2 ^ 42 * ‖A‖ := by
  let V := extendUnitary (q := q) U
  have hV := extendUnitary_unitary (q := q) U hU hU'
  let X := Vᴴ * A * V
  have hX : ‖X‖ ≤ ‖A‖ := isometry_compression_norm_le V hV.1 A
  have hBlocks : ∀ i, ∃ B C : Matrix (appendShape d q i) (appendShape d q i) ℂ,
      BlockAssembly.block (X.submatrix (appendEquiv d q) (appendEquiv d q)) i i =
        B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ p := by
    intro i
    cases i with
    | inl i =>
      obtain ⟨B, C, heq, hnorm⟩ := hDiag i
      refine ⟨B, C, ?_, hnorm⟩
      convert heq using 1
      ext j l
      simp [BlockAssembly.block, X, V, appendEquiv, extendUnitary_compression]
    | inr i =>
      refine ⟨(0 : Matrix (Fin 1) (Fin 1) ℂ), (0 : Matrix (Fin 1) (Fin 1) ℂ), ?_, ?_⟩
      · ext j l
        simp [BlockAssembly.block, X, V, appendEquiv, extendUnitary_compression,
          Matrix.toBlocks₂₂, hz]
      · simpa using hp
  obtain ⟨B, C, heq, hnorm⟩ := BlockAssembly.assemble_reindexed X
    (appendEquiv d q).symm p hp (by simpa using hCard) hBlocks
  apply unitary_commutator_pullback V hV.1 hV.2 A
  refine ⟨B, C, heq, hnorm.trans ?_⟩
  gcongr

end GlobalAssembly

def oneBlockEquiv (N : ℕ) : (Sigma fun _ : Fin 1 ↦ Fin N) ≃ Fin N where
  toFun x := x.2
  invFun i := ⟨0, i⟩
  left_inv x := by rcases x with ⟨i, j⟩; simp [Fin.eq_zero i]
  right_inv _ := rfl

/-- A complete rectangular coordinate equivalence is a unitary change of basis. -/
theorem coordinateInclusion_unitary {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (e : m ≃ n) :
    (coordinateInclusion e)ᴴ * coordinateInclusion e = 1 ∧
      coordinateInclusion e * (coordinateInclusion e)ᴴ = 1 := by
  have h := coordinateInclusion_isometry e e.injective
  exact ⟨h, (Matrix.mul_eq_one_comm_of_equiv e).mp h⟩

/-- The direct branch uses the same single assembly step as the shrinking branch. -/
theorem assemble_one_with_leftovers {N q : ℕ}
    (A : Matrix (Fin N ⊕ Fin q) (Fin N ⊕ Fin q) ℂ)
    (hz : ∀ j : Fin q, A (Sum.inr j) (Sum.inr j) = 0)
    (p : ℝ) (hp : 0 ≤ p) (hCard : 1 + q ≤ 2 * 2 ^ 26 - 1)
    (hDiag : ∃ B C : Matrix (Fin N) (Fin N) ℂ,
      A.toBlocks₁₁ = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ p) :
    ∃ B C : Matrix (Fin N ⊕ Fin q) (Fin N ⊕ Fin q) ℂ,
      A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ 65536 * p + 2 ^ 42 * ‖A‖ := by
  let U := coordinateInclusion (oneBlockEquiv N)
  have hU := coordinateInclusion_unitary (oneBlockEquiv N)
  apply GlobalAssembly.assemble_with_leftovers A U hU.1 hU.2 hz p hp
    (by simpa using hCard)
  intro i
  obtain ⟨B, C, heq, hnorm⟩ := hDiag
  refine ⟨B, C, ?_, hnorm⟩
  convert heq using 1
  dsimp only [U]
  rw [← submatrix_eq_coordinate_compression]
  rfl

end NoEpsilon
