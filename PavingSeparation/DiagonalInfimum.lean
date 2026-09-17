import PavingSeparation.Foundation
import PavingSeparation.Family
import PavingSeparation.DiagonalCost

/-!
# The actual diagonal product-cost infimum

An explicit diagonal representation proves nonemptiness in every finite dimension.
The precise flat-matrix lower bound therefore passes to the real infimum.
-/

noncomputable section

namespace PavingSeparation

open PavingSeparation.Foundation
open scoped BigOperators Matrix Matrix.Norms.L2Operator

/-- Fixed separated real points in the unit square. -/
private noncomputable def gridPoint (m : ℕ) (i : Fin m) : ℂ :=
  (i.val : ℂ) / ((m + 1 : ℕ) : ℂ)

private theorem gridPoint_injective (m : ℕ) : Function.Injective (gridPoint m) := by
  intro i j hij
  have hd : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hval : (i.val : ℂ) = (j.val : ℂ) := (div_left_inj' hd).mp hij
  exact Fin.ext (by exact_mod_cast hval)

private theorem gridPoint_inUnitSquare (m : ℕ) (i : Fin m) : InUnitSquare (gridPoint m i) := by
  have heq : gridPoint m i = Complex.ofReal ((i.val : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
    simp [gridPoint]
  rw [heq]
  change |(i.val : ℝ) / ((m + 1 : ℕ) : ℝ)| ≤ 1 ∧ |(0 : ℝ)| ≤ 1
  constructor
  · rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
    exact_mod_cast (show i.val ≤ m + 1 by omega)
  · norm_num

private theorem gridPoint_norm_sub_ge (m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    (1 : ℝ) / (m + 1) ≤ ‖gridPoint m i - gridPoint m j‖ := by
  have hdiff : (1 : ℝ) ≤ ‖(i.val : ℂ) - (j.val : ℂ)‖ := by
    rw [show (i.val : ℂ) - (j.val : ℂ) = ((i.val : ℤ) - (j.val : ℤ) : ℤ) from by
      push_cast
      rfl]
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs
      (sub_ne_zero.mpr (by exact_mod_cast Fin.val_ne_of_ne hij :
        (i.val : ℤ) ≠ (j.val : ℤ)))
  dsimp only [gridPoint]
  rw [div_sub_div_same, norm_div, Complex.norm_natCast]
  simpa only [Nat.cast_add, Nat.cast_one] using
    div_le_div_of_nonneg_right hdiff (Nat.cast_nonneg (m + 1))

/-- An explicit finite-dimensional decomposition with a deliberately loose polynomial bound. -/
private theorem zeroDiag_decomp_bounded {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (hzd : ZeroDiag A) :
    ∃ B C : Matrix (Fin m) (Fin m) ℂ,
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = matComm B C ∧
        ‖C‖ ≤ ((m : ℝ) + 1)^2 * ‖A‖ := by
  let b := gridPoint m
  let B : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal b
  let C : Matrix (Fin m) (Fin m) ℂ := fun i j ↦ A i j / (b i - b j)
  refine ⟨B, C, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact Matrix.diagonal_apply_ne _ hij
  · intro i
    simpa [B, b] using gridPoint_inUnitSquare m i
  · ext i j
    change A i j = (Matrix.diagonal b * C - C * Matrix.diagonal b) i j
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, C]
    rw [mul_comm (A i j / (b i - b j)) (b j), ← sub_mul]
    by_cases hij : i = j
    · subst j
      simp [hzd i]
    · exact (mul_div_cancel₀ (A i j)
        (sub_ne_zero.mpr ((gridPoint_injective m).ne hij))).symm
  · have hCentry (i j : Fin m) : ‖C i j‖ ≤ ((m : ℝ) + 1) * ‖A i j‖ := by
      by_cases hij : i = j
      · subst j
        simp only [C, sub_self, div_zero, norm_zero]
        positivity
      · dsimp only [C]
        rw [norm_div]
        have hsep := gridPoint_norm_sub_ge m i j hij
        calc
          ‖A i j‖ / ‖b i - b j‖ ≤ ‖A i j‖ / (1 / ((m : ℝ) + 1)) :=
            div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hsep
          _ = ((m : ℝ) + 1) * ‖A i j‖ := by simp [div_eq_mul_inv, mul_comm]
    have hhs : hsNorm C ≤ ((m : ℝ) + 1) * hsNorm A := by
      unfold hsNorm
      rw [show ((m : ℝ) + 1) * Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) =
          Real.sqrt (((m : ℝ) + 1)^2 * ∑ i, ∑ j, Complex.normSq (A i j)) by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_le_sqrt
      calc
        (∑ i, ∑ j, Complex.normSq (C i j)) ≤
            ∑ i, ∑ j, ((m : ℝ) + 1)^2 * Complex.normSq (A i j) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          simp only [Complex.normSq_eq_norm_sq, ← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hCentry i j) 2
        _ = ((m : ℝ) + 1)^2 * ∑ i, ∑ j, Complex.normSq (A i j) := by
          simp only [Finset.mul_sum]
    have hsqrt : Real.sqrt (m : ℝ) ≤ (m : ℝ) + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [sq_nonneg (m : ℝ), Nat.cast_nonneg (α := ℝ) m]
    calc
      ‖C‖ ≤ hsNorm C := le_hsNorm C
      _ ≤ ((m : ℝ) + 1) * hsNorm A := hhs
      _ ≤ ((m : ℝ) + 1) * (Real.sqrt m * ‖A‖) := by
        gcongr
        exact hsNorm_le_sqrt_n_mul_opNorm A
      _ ≤ ((m : ℝ) + 1) * (((m : ℝ) + 1) * ‖A‖) := by gcongr
      _ = ((m : ℝ) + 1)^2 * ‖A‖ := by ring

/-- A square-normalized diagonal representation with a finite dimension-dependent bound. -/
theorem zeroDiag_square_representation_bounded {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hzd : ∀ i, A i i = 0) :
    ∃ z : Fin n → ℂ, ∃ C : Matrix (Fin n) (Fin n) ℂ,
      (∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1) ∧
      A = Matrix.diagonal z * C - C * Matrix.diagonal z ∧
      ‖C‖ ≤ ((n : ℝ) + 1) ^ 2 * ‖A‖ := by
  obtain ⟨B, C, hB, hs, hc, hnorm⟩ := zeroDiag_decomp_bounded A hzd
  have hd : Matrix.diagonal (fun i ↦ B i i) = B := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply_ne _ hij, hB i j hij]
  exact ⟨(fun i ↦ B i i), C, hs, by simpa only [hd, matComm] using hc, hnorm⟩

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
/-- Every finite zero-diagonal matrix admits an original-coordinate diagonal commutator. -/
theorem zeroDiag_diagonal_representation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hzd : ∀ i, A i i = 0) :
    ∃ D C : Matrix ι ι ℂ, D.IsDiag ∧ A = D * C - C * D := by
  let e := Fintype.equivFin ι
  let z : ι → ℂ := fun i ↦ ((e i).val : ℂ)
  have hz : Function.Injective z := by
    intro i j h
    apply e.injective
    apply Fin.ext
    dsimp only [z] at h
    exact_mod_cast h
  let C : Matrix ι ι ℂ := fun i j ↦ A i j / (z i - z j)
  refine ⟨Matrix.diagonal z, C, Matrix.isDiag_diagonal z, ?_⟩
  ext i j
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, C]
  rw [mul_comm (A i j / (z i - z j)) (z j), ← sub_mul]
  by_cases hij : i = j
  · subst j
    simp [hzd i]
  · exact (mul_div_cancel₀ (A i j) (sub_ne_zero.mpr (hz.ne hij))).symm

/-- The exact attainable product costs of diagonal commutator representations. -/
def diagonalCosts {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Set ℝ :=
  {t : ℝ | ∃ D C : Matrix ι ι ℂ,
    D.IsDiag ∧ A = D * C - C * D ∧ t = ‖D‖ * ‖C‖}

/-- The PDF's `κ_diag`, with the diagonal algebra fixed in the original coordinates. -/
def diagonalCost {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  sInf (diagonalCosts A)

theorem diagonalCosts_bddBelow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : BddBelow (diagonalCosts A) := by
  refine ⟨0, ?_⟩
  rintro t ⟨D, C, _, _, rfl⟩
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem diagonalCosts_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hzd : ∀ i, A i i = 0) : (diagonalCosts A).Nonempty := by
  obtain ⟨D, C, hD, hc⟩ := zeroDiag_diagonal_representation A hzd
  exact ⟨‖D‖ * ‖C‖, D, C, hD, hc, rfl⟩

/-- Pointwise lower bounds pass to the actual infimum because the cost set is nonempty. -/
theorem le_diagonalCost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hzd : ∀ i, A i i = 0) (L : ℝ)
    (hL : ∀ D C : Matrix ι ι ℂ, D.IsDiag → A = D * C - C * D → L ≤ ‖D‖ * ‖C‖) :
    L ≤ diagonalCost A := by
  apply le_csInf (diagonalCosts_nonempty A hzd)
  rintro t ⟨D, C, hD, hc, rfl⟩
  exact hL D C hD hc

theorem diagonalCost_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hzd : ∀ i, A i i = 0) : 0 ≤ diagonalCost A := by
  apply le_diagonalCost A hzd 0
  intro D C hD hc
  positivity

theorem diagonalCost_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D C : Matrix ι ι ℂ) (hD : D.IsDiag) (hc : A = D * C - C * D) :
    diagonalCost A ≤ ‖D‖ * ‖C‖ :=
  csInf_le (diagonalCosts_bddBelow A) ⟨D, C, hD, hc, rfl⟩

/-- Even recursive depth has exactly the order used by the dyadic energy estimate. -/
theorem card_cube_even (k : ℕ) : Fintype.card (Cube (2 * k)) = 4 ^ k := by
  rw [card_cube, pow_mul]
  norm_num

/-- The precise diagonal cost lower bound in Theorem 1 of the supplied PDF. -/
theorem family_diagonalCost_lower_bound (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt ((((3 : ℝ) * k - 1) * (4 : ℝ) ^ k + 1) /
      (32 * ((4 : ℝ) ^ k - 1))) ≤ diagonalCost (pavingMatrix (2 * k)) := by
  apply le_diagonalCost (pavingMatrix (2 * k)) (family_diag (2 * k))
  intro D C hD hc
  have hf : ∀ i j : Cube (2 * k), i ≠ j →
      ‖pavingMatrix (2 * k) i j‖ ^ 2 = ((Fintype.card (Cube (2 * k)) : ℝ) - 1)⁻¹ := by
    intro i j hij
    simpa only [card_cube, Nat.cast_pow, Nat.cast_ofNat, one_div] using
      family_offdiag_norm_sq (2 * k) hij
  have h := DiagonalCost.isDiag_commutator_product_cost k hk (card_cube_even k)
    (pavingMatrix (2 * k)) D C hD hf hc
  rw [card_cube_even] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

/-- The simpler divergent lower bound for `κ_diag` along the same family. -/
theorem family_diagonalCost_sqrt_lower_bound (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt (k : ℝ) / 4 ≤ diagonalCost (pavingMatrix (2 * k)) := by
  have hn : 1 < 4 ^ k := by
    have h : 4 ^ 1 ≤ 4 ^ k := Nat.pow_le_pow_right (by omega) hk
    norm_num at h
    omega
  have h := DiagonalCost.sqrt_k_lower_bound k hk (4 ^ k) hn
  have h' : Real.sqrt (k : ℝ) / 4 ≤
      Real.sqrt ((((3 : ℝ) * k - 1) * (4 : ℝ) ^ k + 1) /
        (32 * ((4 : ℝ) ^ k - 1))) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  exact h'.trans (family_diagonalCost_lower_bound k hk)

end PavingSeparation
