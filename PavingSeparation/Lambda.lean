import PavingSeparation.DiagonalInfimum

/-!
# The square-normalized diagonal invariant on `Fin n`

The definitions use genuine real infima and suprema, with the norm-one convention of the PDF.
All matrix norms in this file are the operator norms for the Euclidean norm.
-/

noncomputable section

namespace PavingSeparation

open scoped BigOperators Matrix Matrix.Norms.L2Operator

/-- Costs of original-coordinate diagonal representations with diagonal entries in the square. -/
def lambdaCosts {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set ℝ :=
  {t | ∃ z : Fin n → ℂ, ∃ C : Matrix (Fin n) (Fin n) ℂ,
    (∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1) ∧
    A = Matrix.diagonal z * C - C * Matrix.diagonal z ∧ t = ‖C‖}

/-- The PDF/JOS square-normalized original-coordinate diagonal cost. -/
def lambdaA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := sInf (lambdaCosts A)

/-- The norm-one, zero-diagonal class in dimension `n`. -/
def lambdaClass (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {A | (∀ i, A i i = 0) ∧ ‖A‖ = 1}

/-- The PDF/JOS dimension-dependent invariant, with its original norm-one convention. -/
def lambdaM (n : ℕ) : ℝ := sSup (lambdaA '' lambdaClass n)

theorem lambdaCosts_bddBelow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    BddBelow (lambdaCosts A) := by
  refine ⟨0, ?_⟩
  rintro t ⟨z, C, hz, hc, rfl⟩
  exact norm_nonneg C

theorem lambdaCosts_nonempty {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hzd : ∀ i, A i i = 0) : (lambdaCosts A).Nonempty := by
  obtain ⟨z, C, hz, hc, _⟩ := zeroDiag_square_representation_bounded A hzd
  exact ⟨‖C‖, z, C, hz, hc, rfl⟩

/-- A pointwise bound passes to the actual infimum using a nonempty cost set. -/
theorem le_lambdaA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hzd : ∀ i, A i i = 0) (L : ℝ)
    (hL : ∀ z C, (∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1) →
      A = Matrix.diagonal z * C - C * Matrix.diagonal z → L ≤ ‖C‖) :
    L ≤ lambdaA A := by
  apply le_csInf (lambdaCosts_nonempty A hzd)
  rintro t ⟨z, C, hz, hc, rfl⟩
  exact hL z C hz hc

theorem lambdaA_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hzd : ∀ i, A i i = 0) : 0 ≤ lambdaA A := by
  apply le_lambdaA A hzd 0
  intro z C _ _
  exact norm_nonneg C

theorem lambdaA_le {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ)
    (hz : ∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1)
    (hc : A = Matrix.diagonal z * C - C * Matrix.diagonal z) :
    lambdaA A ≤ ‖C‖ :=
  csInf_le (lambdaCosts_bddBelow A) ⟨z, C, hz, hc, rfl⟩

/-- The fixed-dimensional infimum is bounded above by an explicit finite budget. -/
theorem lambdaA_le_polynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hzd : ∀ i, A i i = 0) : lambdaA A ≤ ((n : ℝ) + 1) ^ 2 * ‖A‖ := by
  obtain ⟨z, C, hz, hc, hb⟩ := zeroDiag_square_representation_bounded A hzd
  exact (lambdaA_le A C z hz hc).trans hb

/-- Every fixed-dimensional supremum has a genuine upper-bound guard. -/
theorem lambdaClass_costs_bddAbove (n : ℕ) : BddAbove (lambdaA '' lambdaClass n) := by
  refine ⟨((n : ℝ) + 1) ^ 2, ?_⟩
  rintro t ⟨A, ⟨hzd, hn⟩, rfl⟩
  simpa only [hn, mul_one] using lambdaA_le_polynomial A hzd

theorem lambdaA_le_lambdaM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hzd : ∀ i, A i i = 0) (hn : ‖A‖ = 1) : lambdaA A ≤ lambdaM n :=
  le_csSup (lambdaClass_costs_bddAbove n) ⟨A, ⟨hzd, hn⟩, rfl⟩

/-- The upper bound includes the empty norm-one classes in dimensions zero and one. -/
theorem lambdaM_le_polynomial (n : ℕ) : lambdaM n ≤ ((n : ℝ) + 1) ^ 2 := by
  by_cases h : (lambdaA '' lambdaClass n).Nonempty
  · apply csSup_le h
    rintro t ⟨A, ⟨hzd, hn⟩, rfl⟩
    simpa only [hn, mul_one] using lambdaA_le_polynomial A hzd
  · have he : lambdaA '' lambdaClass n = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp only [lambdaM, he, Real.sSup_empty]
    positivity

/-- Only a coordinate permutation identifies the recursive index set with `Fin (4^k)`. -/
def cubeEvenEquivFin (k : ℕ) : Cube (2 * k) ≃ Fin (4 ^ k) :=
  (Fintype.equivFin (Cube (2 * k))).trans (finCongr (card_cube_even k))

/-- The explicit matrices on the conventional `Fin n` index set. -/
def finFamily (k : ℕ) : Matrix (Fin (4 ^ k)) (Fin (4 ^ k)) ℂ :=
  (pavingMatrix (2 * k)).submatrix (cubeEvenEquivFin k).symm (cubeEvenEquivFin k).symm

@[simp] theorem finFamily_diag (k : ℕ) (i : Fin (4 ^ k)) : finFamily k i i = 0 :=
  family_diag (2 * k) _

theorem finFamily_isHermitian (k : ℕ) : (finFamily k).IsHermitian :=
  (family_isHermitian (2 * k)).submatrix _

theorem finFamily_mul_self {k : ℕ} (hk : 1 ≤ k) : finFamily k * finFamily k = 1 := by
  unfold finFamily
  rw [Matrix.submatrix_mul_equiv, family_mul_self (by omega), Matrix.submatrix_one_equiv]

theorem finFamily_norm {k : ℕ} (hk : 1 ≤ k) : ‖finFamily k‖ = 1 := by
  apply CStarRing.norm_of_mem_unitary
  rw [← Matrix.unitaryGroup, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    (finFamily_isHermitian k).eq]
  exact finFamily_mul_self hk

theorem finFamily_offdiag_norm_sq (k : ℕ) {i j : Fin (4 ^ k)} (hij : i ≠ j) :
    ‖finFamily k i j‖ ^ 2 = ((4 : ℝ) ^ k - 1)⁻¹ := by
  have h := family_offdiag_norm_sq (2 * k) ((cubeEvenEquivFin k).symm.injective.ne hij)
  simpa only [finFamily, Matrix.submatrix_apply, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num,
    one_div] using h

/-- The precise square-normalized infimum bound for the reindexed explicit family. -/
theorem finFamily_lambdaA_lower_bound (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt ((((3 : ℝ) * k - 1) * (4 : ℝ) ^ k + 1) /
      (32 * ((4 : ℝ) ^ k - 1))) ≤ lambdaA (finFamily k) := by
  apply le_lambdaA (finFamily k) (finFamily_diag k)
  intro z C hz hc
  have hf : ∀ i j : Fin (4 ^ k), i ≠ j →
      ‖finFamily k i j‖ ^ 2 = ((Fintype.card (Fin (4 ^ k)) : ℝ) - 1)⁻¹ := by
    intro i j hij
    simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
      finFamily_offdiag_norm_sq k hij
  have h := DiagonalCost.diagonal_commutator_cost k hk (Fintype.card_fin (4 ^ k))
    (finFamily k) C z hz hf hc
  simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The precise dimension-dependent lower bound from Section 5 of the PDF. -/
theorem lambdaM_four_pow_lower_bound (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt ((((3 : ℝ) * k - 1) * (4 : ℝ) ^ k + 1) /
      (32 * ((4 : ℝ) ^ k - 1))) ≤ lambdaM (4 ^ k) :=
  (finFamily_lambdaA_lower_bound k hk).trans
    (lambdaA_le_lambdaM (finFamily k) (finFamily_diag k) (finFamily_norm hk))

theorem lambdaM_four_pow_sqrt_lower_bound (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt (k : ℝ) / 4 ≤ lambdaM (4 ^ k) := by
  have hn : 1 < 4 ^ k := by
    have h : 4 ^ 1 ≤ 4 ^ k := Nat.pow_le_pow_right (by omega) hk
    norm_num at h
    omega
  have h := DiagonalCost.sqrt_k_lower_bound k hk (4 ^ k) hn
  have h' : Real.sqrt (k : ℝ) / 4 ≤
      Real.sqrt ((((3 : ℝ) * k - 1) * (4 : ℝ) ^ k + 1) /
        (32 * ((4 : ℝ) ^ k - 1))) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  exact h'.trans (lambdaM_four_pow_lower_bound k hk)

/-- No dimension-independent upper bound exists for the original square-normalized invariant. -/
theorem lambdaM_unbounded (M : ℝ) : ∃ n : ℕ, M < lambdaM n := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((4 * (|M| + 1)) ^ 2)
  have hkpos : 1 ≤ k := by
    have hknonneg : (0 : ℝ) < k := lt_of_le_of_lt (sq_nonneg _) hk
    exact_mod_cast (show 0 < k by exact_mod_cast hknonneg)
  have hsqrt : 4 * (|M| + 1) < Real.sqrt (k : ℝ) := by
    apply (Real.lt_sqrt (by positivity)).2
    exact hk
  refine ⟨4 ^ k, lt_of_lt_of_le ?_ (lambdaM_four_pow_sqrt_lower_bound k hkpos)⟩
  nlinarith [le_abs_self M]

theorem lambdaM_not_bddAbove : ¬ BddAbove (Set.range lambdaM) := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := lambdaM_unbounded M
  exact (not_le_of_gt hn) (hM (Set.mem_range_self n))

end PavingSeparation
