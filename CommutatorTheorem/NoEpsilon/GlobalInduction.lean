import CommutatorTheorem.NoEpsilon.GlobalReduction
import CommutatorTheorem.NoEpsilon.PavingCoordinates
import CommutatorTheorem.NoEpsilon.Budget

/-! # The final dimension induction

This reduction takes the precise low-mass paving theorem as its only branch input.
The high-mass branch, all changes of coordinates, and all dimensions are handled internally.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator

abbrev pavingRank : ℕ := 2 ^ 26

def lowMassPavingInputAt (R : ℕ) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ A : Matrix (Fin (k * R)) (Fin (k * R)) ℂ,
    ‖A‖ ≤ 1 → Matrix.trace A = 0 → ¬ HasHighTraceMass A (2 / (2 : ℝ) ^ 26) →
    ∃ b : OrthonormalBasis (Fin R × Fin k) ℂ
      (EuclideanSpace ℂ (Fin (k * R))),
      ∀ i, let W := familyMatrix (fun j ↦ b (i, j))
        Matrix.trace (Wᴴ * A * W) = 0 ∧ ‖Wᴴ * A * W‖ ≤ 319 / (2 : ℝ) ^ 26

def lowMassPavingBlocksInputAt (R : ℕ) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ A : Matrix (Fin (k * R)) (Fin (k * R)) ℂ,
    ‖A‖ ≤ 1 → Matrix.trace A = 0 → ¬ HasHighTraceMass A (2 / (2 : ℝ) ^ 26) →
    ∃ U : Matrix (Fin (k * R)) (Sigma fun _ : Fin R ↦ Fin k) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ ∀ i,
        Matrix.trace (BlockAssembly.block (Uᴴ * A * U) i i) = 0 ∧
          ‖BlockAssembly.block (Uᴴ * A * U) i i‖ ≤ 319 / (2 : ℝ) ^ 26

abbrev lowMassPavingInput : Prop := lowMassPavingInputAt pavingRank

def globalNormBudget : ℝ :=
  max (65536 * max (highMassNormBudget (2 / (2 : ℝ) ^ 26)) 0 + 2 ^ 42) (2 ^ 43)

theorem globalNormBudget_pos : 0 < globalNormBudget := by
  have h : (2 : ℝ) ^ 43 ≤ globalNormBudget := le_max_right _ _
  exact lt_of_lt_of_le (by norm_num) h

theorem globalNormBudget_closes :
    65536 * (319 / (2 : ℝ) ^ 26) * globalNormBudget + 2 ^ 42 ≤ globalNormBudget := by
  simpa only [show (8 * 8192 : ℝ) = 65536 by norm_num] using
    CommutatorTheorem.NoEpsilon.candidate_budget_closes globalNormBudget
      (show (2 : ℝ) ^ 43 ≤ globalNormBudget from le_max_right _ _)

theorem lowMassPavingBlocksInput_of_basis (R : ℕ) (paving : lowMassPavingInputAt R) :
    lowMassPavingBlocksInputAt R := by
  intro k hk A hNorm hTrace hLow
  obtain ⟨b, hb⟩ := paving k hk A hNorm hTrace hLow
  exact paving_basis_to_blocks_generic (R := R) (k := k) A b
    (319 / (2 : ℝ) ^ 26) hb

/-- The final induction with its explicit, dimension-independent budget exposed. -/
theorem boundedCommutator_of_lowMassBlocksAt (R : ℕ) (hR : R = 2 ^ 26)
    (paving : lowMassPavingBlocksInputAt R) :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), Matrix.trace A = 0 →
      ∃ B C : Matrix (Fin n) (Fin n) ℂ,
        A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ globalNormBudget * ‖A‖ := by
  let K := globalNormBudget
  have hK : 0 ≤ K := globalNormBudget_pos.le
  have hBase : (2 : ℝ) ^ 42 ≤ K := by
    have h : (2 : ℝ) ^ 43 ≤ K := le_max_right _ _
    linarith
  let H := max (highMassNormBudget (2 / (2 : ℝ) ^ 26)) 0
  have hH : 0 ≤ H := le_max_right _ _
  have hDirect : 65536 * H + 2 ^ 42 ≤ K := le_max_left _ _
  have hClose : 65536 * (319 / (2 : ℝ) ^ 26) * K + 2 ^ 42 ≤ K :=
    globalNormBudget_closes
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    apply traceZero_bound_of_zeroDiag_at n K hK
    intro A hz
    by_cases hSmall : n < R
    · obtain ⟨B, C, heq, hnorm⟩ := zeroDiag_small_commutator A hz (by
        rw [hR] at hSmall
        omega)
      exact ⟨B, C, heq, hnorm.trans (mul_le_mul_of_nonneg_right hBase (norm_nonneg A))⟩
    · have hn : R ≤ n := le_of_not_gt hSmall
      let k := n / R
      let q := n % R
      have hk : 0 < k := Nat.div_pos hn (by rw [hR]; norm_num)
      have hq : q < R := Nat.mod_lt n (by rw [hR]; norm_num)
      have hklt : k < n := Nat.div_lt_self (by omega) (by rw [hR]; norm_num)
      have hdim : k * R + q = n := by
        simpa [k, q, Nat.mul_comm] using Nat.div_add_mod n R
      let e : (Fin (k * R) ⊕ Fin q) ≃ Fin n :=
        finSumFinEquiv.trans (finCongr hdim)
      let X := A.submatrix e e
      have hXnorm : ‖X‖ = ‖A‖ := submatrix_operator_norm_equiv A e
      have hXz (i) : X i i = 0 := hz (e i)
      let T := X.toBlocks₁₁
      have hTtrace : Matrix.trace T = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact hXz (Sum.inl i)
      have hTnorm : ‖T‖ ≤ ‖X‖ :=
        submatrix_operator_norm_le X Sum.inl Sum.inl Sum.inl_injective Sum.inl_injective
      apply commutator_reindex_pullback A e (K * ‖A‖)
      have hzq (j : Fin q) : X (Sum.inr j) (Sum.inr j) = 0 := hXz _
      have hSlots : 1 + q ≤ 2 * 2 ^ 26 - 1 := by
        rw [hR] at hq
        omega
      by_cases hTzero : T = 0
      · obtain ⟨B, C, heq, hnorm⟩ := assemble_one_with_leftovers X hzq 0 le_rfl hSlots
          ⟨0, 0, by simpa only [Matrix.zero_mul, sub_zero] using hTzero, by simp⟩
        refine ⟨B, C, heq, ?_⟩
        simp only [mul_zero, zero_add, hXnorm] at hnorm
        exact hnorm.trans (mul_le_mul_of_nonneg_right hBase (norm_nonneg A))
      · let T₁ := ((‖T‖⁻¹ : ℝ) : ℂ) • T
        have hT₁norm : ‖T₁‖ ≤ 1 := (normalized_matrix_norm T hTzero).le
        have hT₁trace : Matrix.trace T₁ = 0 := by
          dsimp only [T₁]
          rw [Matrix.trace_smul, hTtrace, smul_zero]
        have hTscale : T = (‖T‖ : ℂ) • T₁ := by
          dsimp only [T₁]
          rw [smul_smul, ← Complex.ofReal_mul,
            mul_inv_cancel₀ (norm_ne_zero_iff.mpr hTzero), Complex.ofReal_one, one_smul]
        by_cases hMass : HasHighTraceMass T₁ (2 / (2 : ℝ) ^ 26)
        · haveI : Nonempty (Fin (k * R)) :=
            Fin.pos_iff_nonempty.mp (Nat.mul_pos hk (by rw [hR]; norm_num))
          obtain ⟨B, C, heq, hnorm⟩ := highMass_bounded_commutator T₁
            (2 / (2 : ℝ) ^ 26) (by positivity) hT₁norm hT₁trace hMass
          have hTsol := commutator_of_normalized T hTzero H
            ⟨B, C, heq, hnorm.trans (le_max_left _ _)⟩
          have hp : 0 ≤ H * ‖X‖ := mul_nonneg hH (norm_nonneg X)
          obtain ⟨D, E, hDE, hDEbound⟩ := hTsol
          have hTsol' : ∃ D E : Matrix (Fin (k * R)) (Fin (k * R)) ℂ,
              T = D * E - E * D ∧ ‖D‖ * ‖E‖ ≤ H * ‖X‖ :=
            ⟨D, E, hDE, hDEbound.trans (mul_le_mul_of_nonneg_left hTnorm hH)⟩
          obtain ⟨F, G, hFG, hFGbound⟩ := assemble_one_with_leftovers X hzq
            (H * ‖X‖) hp hSlots hTsol'
          refine ⟨F, G, hFG, hFGbound.trans ?_⟩
          rw [hXnorm]
          nlinarith [mul_le_mul_of_nonneg_right hDirect (norm_nonneg A)]
        · obtain ⟨U, hU, hU', hBlocks⟩ := paving k hk T₁ hT₁norm hT₁trace hMass
          let p := K * (319 / (2 : ℝ) ^ 26) * ‖X‖
          have hp : 0 ≤ p := by positivity
          have hDiag : ∀ i : Fin R, ∃ B C : Matrix (Fin k) (Fin k) ℂ,
              BlockAssembly.block (Uᴴ * T * U) i i = B * C - C * B ∧
                ‖B‖ * ‖C‖ ≤ p := by
            intro i
            have hscale : BlockAssembly.block (Uᴴ * T * U) i i =
                (‖T‖ : ℂ) • BlockAssembly.block (Uᴴ * T₁ * U) i i := by
              conv_lhs => rw [hTscale]
              simp only [Matrix.mul_smul, Matrix.smul_mul, BlockAssembly.block,
                Matrix.submatrix_smul]
              rfl
            have ht : Matrix.trace (BlockAssembly.block (Uᴴ * T * U) i i) = 0 := by
              rw [hscale, Matrix.trace_smul, (hBlocks i).1, smul_zero]
            have hnBlock : ‖BlockAssembly.block (Uᴴ * T * U) i i‖ ≤
                (319 / (2 : ℝ) ^ 26) * ‖X‖ := by
              rw [hscale, norm_smul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (norm_nonneg T)]
              calc
                _ ≤ ‖T‖ * (319 / (2 : ℝ) ^ 26) :=
                  mul_le_mul_of_nonneg_left (hBlocks i).2 (norm_nonneg T)
                _ ≤ (319 / (2 : ℝ) ^ 26) * ‖X‖ := by
                  rw [mul_comm]
                  exact mul_le_mul_of_nonneg_left hTnorm (by positivity)
            obtain ⟨B, C, heq, hnorm⟩ := ih k hklt (BlockAssembly.block (Uᴴ * T * U) i i) ht
            refine ⟨B, C, heq, hnorm.trans ?_⟩
            simpa only [p, mul_assoc] using mul_le_mul_of_nonneg_left hnBlock hK
          obtain ⟨B, C, heq, hnorm⟩ := GlobalAssembly.assemble_with_leftovers X U hU hU'
            hzq p hp (by simp only [Fintype.card_fin]; rw [hR] at hq ⊢; omega) hDiag
          refine ⟨B, C, heq, hnorm.trans ?_⟩
          dsimp only [p]
          rw [hXnorm]
          nlinarith [mul_le_mul_of_nonneg_right hClose (norm_nonneg A)]

/-- Full same-dimension induction, reduced only to the quantitative low-mass basis theorem. -/
theorem uniformCommutatorBound_of_lowMassBlocksAt (R : ℕ) (hR : R = 2 ^ 26)
    (paving : lowMassPavingBlocksInputAt R) :
    UniformCommutatorBound :=
  ⟨globalNormBudget, globalNormBudget_pos,
    boundedCommutator_of_lowMassBlocksAt R hR paving⟩

/-- The orthonormal paving interface supplies the block form used in the full induction. -/
theorem uniformCommutatorBound_of_lowMassPaving (paving : lowMassPavingInput) :
    UniformCommutatorBound :=
  uniformCommutatorBound_of_lowMassBlocksAt pavingRank rfl
    (lowMassPavingBlocksInput_of_basis pavingRank paving)

end NoEpsilon
