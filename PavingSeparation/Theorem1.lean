import PavingSeparation.Normal
import PavingSeparation.Lambda
import PavingSeparation.LowerBounds
import PavingSeparation.PrincipalCompression

/-!
# Paving and commutator cost separation

`pavingMatrix m` is the explicitly defined matrix of order `2 ^ m`. Its indexing type `Cube m`
records the original recursive coordinates; it is not an eigenbasis chosen for the input.
All unlabelled matrix norms below are Euclidean operator norms.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace PavingSeparation

/-- The exact numerical lower bound from formulas (3) and (12). -/
def separationLowerBound (k : ℕ) : ℝ :=
  Real.sqrt ((((3 : ℝ) * k - 1) * (4 : ℝ) ^ k + 1) /
    (32 * ((4 : ℝ) ^ k - 1)))

/-- Formula (2), written using the actual order divided by the number of blocks. -/
theorem pavingMinimum_dyadic_ratio (m l : ℕ) (hl : l ≤ m) :
    pavingMinimum (pavingMatrix m) (2 ^ l) =
      Real.sqrt ((((2 : ℝ) ^ m / (2 : ℝ) ^ l) - 1) / ((2 : ℝ) ^ m - 1)) := by
  rw [pavingMinimum_dyadic m l hl, pow_sub₀ 2 (by norm_num) hl]
  simp only [div_eq_mul_inv]

theorem separationLowerBound_sqrt (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt (k : ℝ) / 4 ≤ separationLowerBound k := by
  have hn : 1 < 4 ^ k := one_lt_pow₀ (by norm_num) (by omega)
  simpa only [separationLowerBound, Nat.cast_pow, Nat.cast_ofNat] using
    DiagonalCost.sqrt_k_lower_bound k hk (4 ^ k) hn

theorem family_square_normalized_lower (k : ℕ) (hk : 1 ≤ k)
    (z : Cube (2 * k) → ℂ) (C : Matrix (Cube (2 * k)) (Cube (2 * k)) ℂ)
    (hz : ∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1)
    (hc : pavingMatrix (2 * k) = Matrix.diagonal z * C - C * Matrix.diagonal z) :
    separationLowerBound k ≤ ‖C‖ := by
  have hf : ∀ i j : Cube (2 * k), i ≠ j →
      ‖pavingMatrix (2 * k) i j‖ ^ 2 = ((Fintype.card (Cube (2 * k)) : ℝ) - 1)⁻¹ := by
    intro i j hij
    simpa only [card_cube, Nat.cast_pow, Nat.cast_ofNat, one_div] using
      family_offdiag_norm_sq (2 * k) hij
  simpa only [separationLowerBound, card_cube_even, Nat.cast_pow, Nat.cast_ofNat] using
    DiagonalCost.diagonal_commutator_cost k hk (card_cube_even k)
      (pavingMatrix (2 * k)) C z hz hf hc

/-- Paving and commutator cost separation (Theorem 1.4), with no additional hypotheses. -/
theorem paving_commutator_separation :
    -- The matrices have the prescribed order and are zero-diagonal Hermitian unitaries.
    (∀ m : ℕ, 0 < m →
      Fintype.card (Cube m) = 2 ^ m ∧
      (∀ i, pavingMatrix m i i = 0) ∧ (pavingMatrix m).IsHermitian ∧
      pavingMatrix m * pavingMatrix m = 1 ∧ ‖pavingMatrix m‖ = 1) ∧
    -- The optimal paving cost is exactly formula (2).
    (∀ m l : ℕ, 0 < m → l ≤ m →
      pavingMinimum (pavingMatrix m) (2 ^ l) =
        Real.sqrt ((((2 : ℝ) ^ m / (2 : ℝ) ^ l) - 1) / ((2 : ℝ) ^ m - 1))) ∧
    -- A single block budget, strictly below 2 / ε², works in every dimension.
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ r : ℕ, 0 < r ∧ (r : ℝ) < 2 / ε ^ 2 ∧
        ∀ m : ℕ, 0 < m → ∃ c : Cube m → Fin r,
          ∀ a : Fin r, ‖compression (colorClass c a) (pavingMatrix m)‖ ≤ ε) ∧
    -- The optimal cost with both commutator factors normal is 1/2.
    (∀ m : ℕ, 0 < m → normalCost (pavingMatrix m) = 1 / 2) ∧
    -- Formula (3): the diagonal cost has the precise lower bound, at least √k / 4.
    (∀ k : ℕ, 1 ≤ k →
      separationLowerBound k ≤ diagonalCost (pavingMatrix (2 * k)) ∧
      Real.sqrt (k : ℝ) / 4 ≤ separationLowerBound k) ∧
    -- The same precise lower bound holds for diagonal entries in the prescribed square.
    (∀ k : ℕ, 1 ≤ k →
      ∀ z : Cube (2 * k) → ℂ, ∀ C : Matrix (Cube (2 * k)) (Cube (2 * k)) ℂ,
        (∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1) →
        pavingMatrix (2 * k) = Matrix.diagonal z * C - C * Matrix.diagonal z →
        separationLowerBound k ≤ ‖C‖) := by
  refine ⟨?_, ?_, exists_uniform_family_paving, ?_, ?_, family_square_normalized_lower⟩
  · intro m hm
    exact ⟨card_cube m, family_diag m, family_isHermitian m,
      family_mul_self hm, family_norm hm⟩
  · intro m l _ hl
    exact pavingMinimum_dyadic_ratio m l hl
  · intro m hm
    cases m with
    | zero => omega
    | succ m => exact family_normalCost m
  · intro k hk
    exact ⟨family_diagonalCost_lower_bound k hk, separationLowerBound_sqrt k hk⟩

/-- Section 5: the unrestricted infimum equals the both-normal infimum on this family. -/
theorem section5_unrestricted (m : ℕ) (hm : 0 < m) :
    unrestrictedCost (pavingMatrix m) = 1 / 2 ∧ normalCost (pavingMatrix m) = 1 / 2 := by
  cases m with
  | zero => omega
  | succ m => exact ⟨family_unrestrictedCost m, family_normalCost m⟩

/-- Formula (12), using `Fin n` and the PDF's norm-one convention for `λ(n)`. -/
theorem section5_lambda (k : ℕ) (hk : 1 ≤ k) :
    separationLowerBound k ≤ lambdaM (4 ^ k) ∧
    Real.sqrt (k : ℝ) / 4 ≤ separationLowerBound k :=
  ⟨lambdaM_four_pow_lower_bound k hk, separationLowerBound_sqrt k hk⟩

/-- Every fixed dimension has finite cost, but there is no dimension-independent bound. -/
theorem section5_finite_but_unbounded :
    (∀ n : ℕ, lambdaM n ≤ ((n : ℝ) + 1) ^ 2) ∧
    (∀ M : ℝ, ∃ n : ℕ, M < lambdaM n) :=
  ⟨lambdaM_le_polynomial, lambdaM_unbounded⟩

end PavingSeparation
