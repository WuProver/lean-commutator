import PavingSeparation.Normal
import PavingSeparation.Lambda
import PavingSeparation.LowerBounds
import PavingSeparation.PrincipalCompression

/-!
# Theorem 1 and Section 5 of the supplied PDF

`family m` is the explicitly defined matrix of order `2 ^ m`. Its indexing type `Cube m`
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
    pavingMinimum (family m) (2 ^ l) =
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
    (hc : family (2 * k) = Matrix.diagonal z * C - C * Matrix.diagonal z) :
    separationLowerBound k ≤ ‖C‖ := by
  have hf : ∀ i j : Cube (2 * k), i ≠ j →
      ‖family (2 * k) i j‖ ^ 2 = ((Fintype.card (Cube (2 * k)) : ℝ) - 1)⁻¹ := by
    intro i j hij
    simpa only [card_cube, Nat.cast_pow, Nat.cast_ofNat, one_div] using
      family_offdiag_norm_sq (2 * k) hij
  simpa only [separationLowerBound, card_cube_even, Nat.cast_pow, Nat.cast_ofNat] using
    DiagonalCost.diagonal_commutator_cost k hk (card_cube_even k)
      (family (2 * k)) C z hz hf hc

/-- Exact statement of Theorem 1 for the explicitly constructed family. -/
structure TheoremOne : Prop where
  /-- The construction has the prescribed order and is zero-diagonal Hermitian unitary. -/
  matrices : ∀ m : ℕ, 0 < m →
    Fintype.card (Cube m) = 2 ^ m ∧
    (∀ i, family m i i = 0) ∧ (family m).IsHermitian ∧
    family m * family m = 1 ∧ ‖family m‖ = 1
  /-- The actual minimum over all original-coordinate partitions equals formula (2). -/
  optimal_paving : ∀ m l : ℕ, 0 < m → l ≤ m →
    pavingMinimum (family m) (2 ^ l) =
      Real.sqrt ((((2 : ℝ) ^ m / (2 : ℝ) ^ l) - 1) / ((2 : ℝ) ^ m - 1))
  /-- One block budget works for every dimension and is strictly below `2 / ε²`. -/
  uniform_paving : ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ r : ℕ, 0 < r ∧ (r : ℝ) < 2 / ε ^ 2 ∧
      ∀ m : ℕ, 0 < m → ∃ c : Cube m → Fin r,
        ∀ a : Fin r, ‖compression (colorClass c a) (family m)‖ ≤ ε
  /-- Both commutator factors are normal in this infimum. -/
  optimal_normal : ∀ m : ℕ, 0 < m → normalCost (family m) = 1 / 2
  /-- Formula (3) with its exact constant, for the original-coordinate diagonal algebra. -/
  diagonal_lower : ∀ k : ℕ, 1 ≤ k →
    separationLowerBound k ≤ diagonalCost (family (2 * k)) ∧
    Real.sqrt (k : ℝ) / 4 ≤ separationLowerBound k
  /-- The same first lower bound when the diagonal entries lie in the prescribed square. -/
  square_lower : ∀ k : ℕ, 1 ≤ k →
    ∀ z : Cube (2 * k) → ℂ, ∀ C : Matrix (Cube (2 * k)) (Cube (2 * k)) ℂ,
      (∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1) →
      family (2 * k) = Matrix.diagonal z * C - C * Matrix.diagonal z →
      separationLowerBound k ≤ ‖C‖

/-- The supplied PDF's Theorem 1, with all parts proved and no additional hypotheses. -/
theorem theorem1 : TheoremOne where
  matrices m hm := ⟨card_cube m, family_diag m, family_isHermitian m,
    family_mul_self hm, family_norm hm⟩
  optimal_paving m l _ hl := pavingMinimum_dyadic_ratio m l hl
  uniform_paving := exists_uniform_family_paving
  optimal_normal m hm := by
    cases m with
    | zero => omega
    | succ m => exact family_normalCost m
  diagonal_lower k hk :=
    ⟨family_diagonalCost_lower_bound k hk, separationLowerBound_sqrt k hk⟩
  square_lower := family_square_normalized_lower

/-- Section 5: the unrestricted infimum equals the both-normal infimum on this family. -/
theorem section5_unrestricted (m : ℕ) (hm : 0 < m) :
    unrestrictedCost (family m) = 1 / 2 ∧ normalCost (family m) = 1 / 2 := by
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
