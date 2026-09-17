import PavingSeparation.PlanarEnergy
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Explicit bounds for the diagonal-commutator cost of flat matrices

The explicit planar energy bound controls every original-coordinate diagonal
commutator representation, both with square-normalized entries and after scaling
an arbitrary diagonal factor. All norms are Euclidean operator norms.
No optimality is claimed for the coefficients in these lower bounds.
-/

noncomputable section

namespace PavingSeparation.DiagonalCost

open scoped BigOperators Matrix Matrix.Norms.L2Operator

private theorem total_entry_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) :
    (∑ i : ι, ∑ j : ι, ‖C i j‖ ^ 2) ≤ (Fintype.card ι : ℝ) * ‖C‖ ^ 2 := by
  have hcol : ∀ j : ι, ∑ i : ι, ‖C i j‖ ^ 2 ≤ ‖C‖ ^ 2 := by
    intro j
    set f := (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) C
    set ej := EuclideanSpace.single j (1 : ℂ)
    have hfej : ‖f ej‖ ≤ ‖C‖ := by
      calc
        ‖f ej‖ ≤ ‖f‖ * ‖ej‖ := ContinuousLinearMap.le_opNorm f ej
        _ = ‖C‖ * 1 := by rw [← Matrix.l2_opNorm_def, PiLp.norm_single 2, norm_one]
        _ = ‖C‖ := mul_one _
    suffices h : ∑ i : ι, ‖C i j‖ ^ 2 = ‖f ej‖ ^ 2 by
      rw [h]
      exact pow_le_pow_left₀ (norm_nonneg _) hfej 2
    have hvec : f ej = WithLp.toLp 2 (C.mulVec (Pi.single j 1)) := by
      change (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) C ej = _
      simp [LinearEquiv.trans_apply, Matrix.toLpLin_apply, ej, EuclideanSpace.single]
    rw [hvec, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ pow_nonneg (norm_nonneg _) 2))]
    congr 1
    ext i
    congr 2
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j : ι, ‖C‖ ^ 2 := Finset.sum_le_sum fun j _ ↦ hcol j
    _ = _ := by simp

private theorem card_one_lt {ι : Type*} [Fintype ι] (k : ℕ) (hk : 1 ≤ k)
    (hn : Fintype.card ι = 4 ^ k) : 1 < Fintype.card ι := by
  have hpow : 4 ^ 1 ≤ 4 ^ k := Nat.pow_le_pow_right (by omega) hk
  rw [hn]
  norm_num at hpow
  omega

/-- An explicit bound for the squared cost with a square-normalized diagonal factor
and a flat matrix. -/
theorem diagonal_commutator_cost_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k) (hn : Fintype.card ι = 4 ^ k)
    (A C : Matrix ι ι ℂ) (z : ι → ℂ)
    (hz : ∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1)
    (hflat : ∀ i j, i ≠ j → ‖A i j‖ ^ 2 = ((Fintype.card ι : ℝ) - 1)⁻¹)
    (hcomm : A = Matrix.diagonal z * C - C * Matrix.diagonal z) :
    (((3 : ℝ) * k - 1) * Fintype.card ι + 1) /
      (32 * ((Fintype.card ι : ℝ) - 1)) ≤ ‖C‖ ^ 2 := by
  have hn1 := card_one_lt k hk hn
  have hnreal : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hn1
  have hmpos : 0 < (Fintype.card ι : ℝ) - 1 := by linarith
  have hentry (i j : ι) : A i j = (z i - z j) * C i j := by
    rw [hcomm]
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hinj : Function.Injective z := by
    intro i j h
    by_contra hij
    have hf := hflat i j hij
    rw [hentry i j, h, sub_self, zero_mul, norm_zero, zero_pow (by omega : 2 ≠ 0)] at hf
    exact (ne_of_gt (inv_pos.mpr hmpos)) hf.symm
  have hpairs (i j : ι) (hij : j ≠ i) :
      (‖z i - z j‖ ^ 2)⁻¹ ≤ ((Fintype.card ι : ℝ) - 1) * ‖C i j‖ ^ 2 := by
    have hd : 0 < ‖z i - z j‖ ^ 2 := by
      exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hinj.ne (Ne.symm hij))))
    have hf := hflat i j (Ne.symm hij)
    rw [hentry i j, norm_mul, mul_pow] at hf
    have hm := congrArg (fun t : ℝ ↦ ((Fintype.card ι : ℝ) - 1) * t) hf
    dsimp only at hm
    rw [mul_inv_cancel₀ (ne_of_gt hmpos)] at hm
    apply (inv_le_iff_one_le_mul₀' hd).mpr
    nlinarith
  have henergy := PlanarEnergy.energy_lower_bound k hn z hz hinj
  have hsum : (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j ↦ j ≠ i),
      (‖z i - z j‖ ^ 2)⁻¹) ≤
      ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) * ‖C‖ ^ 2) := by
    calc
      _ ≤ ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j ↦ j ≠ i),
          ((Fintype.card ι : ℝ) - 1) * ‖C i j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hpairs i j (Finset.mem_filter.mp hj).2
      _ ≤ ∑ i : ι, ∑ j : ι, ((Fintype.card ι : ℝ) - 1) * ‖C i j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j hj hji ↦ mul_nonneg hmpos.le (sq_nonneg _))
      _ = ((Fintype.card ι : ℝ) - 1) * (∑ i : ι, ∑ j : ι, ‖C i j‖ ^ 2) := by
        simp_rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (total_entry_sq_le C) hmpos.le
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 32) hmpos)).mpr
  have hnpos : (0 : ℝ) < Fintype.card ι := by linarith
  have hcancel : (Fintype.card ι : ℝ) *
      (((3 : ℝ) * k - 1) * Fintype.card ι + 1) ≤ (Fintype.card ι : ℝ) *
      (‖C‖ ^ 2 * (32 * ((Fintype.card ι : ℝ) - 1))) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hnpos).mp hcancel

/-- An explicit bound in square-root form for the finite-dimensional separation theorem. -/
theorem diagonal_commutator_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k) (hn : Fintype.card ι = 4 ^ k)
    (A C : Matrix ι ι ℂ) (z : ι → ℂ)
    (hz : ∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1)
    (hflat : ∀ i j, i ≠ j → ‖A i j‖ ^ 2 = ((Fintype.card ι : ℝ) - 1)⁻¹)
    (hcomm : A = Matrix.diagonal z * C - C * Matrix.diagonal z) :
    Real.sqrt ((((3 : ℝ) * k - 1) * Fintype.card ι + 1) /
      (32 * ((Fintype.card ι : ℝ) - 1))) ≤ ‖C‖ := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨norm_nonneg _, diagonal_commutator_cost_sq k hk hn A C z hz hflat hcomm⟩

/-- The explicit bound is at least the simpler lower bound √k / 4. -/
theorem sqrt_k_lower_bound (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 < n) :
    Real.sqrt (k : ℝ) / 4 ≤
      Real.sqrt ((((3 : ℝ) * k - 1) * n + 1) / (32 * ((n : ℝ) - 1))) := by
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hratio : (k : ℝ) / 16 ≤
      (((3 : ℝ) * k - 1) * n + 1) / (32 * ((n : ℝ) - 1)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 32)
      (by linarith : 0 < (n : ℝ) - 1))).mpr
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) - 1 by linarith) (Nat.cast_nonneg n)]
  have hs := Real.sqrt_le_sqrt hratio
  norm_num [Real.sqrt_div (Nat.cast_nonneg k)] at hs ⊢
  exact hs

/-- Normalizing an arbitrary diagonal factor preserves the product cost. -/
theorem diagonal_commutator_product_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k) (hn : Fintype.card ι = 4 ^ k)
    (A C : Matrix ι ι ℂ) (z : ι → ℂ)
    (hflat : ∀ i j, i ≠ j → ‖A i j‖ ^ 2 = ((Fintype.card ι : ℝ) - 1)⁻¹)
    (hcomm : A = Matrix.diagonal z * C - C * Matrix.diagonal z) :
    Real.sqrt ((((3 : ℝ) * k - 1) * Fintype.card ι + 1) /
      (32 * ((Fintype.card ι : ℝ) - 1))) ≤ ‖Matrix.diagonal z‖ * ‖C‖ := by
  let r : ℝ := ‖(Matrix.diagonal z : Matrix ι ι ℂ)‖
  have hn1 := card_one_lt k hk hn
  have hnreal : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hn1
  have hr : 0 < r := by
    apply lt_of_le_of_ne (norm_nonneg _) ?_
    intro h
    have hz0 : (Matrix.diagonal z : Matrix ι ι ℂ) = 0 := norm_eq_zero.mp h.symm
    obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.mp hn1
    have hf := hflat i j hij
    rw [hcomm, hz0, zero_mul, mul_zero, sub_self] at hf
    simp only [Matrix.zero_apply, norm_zero, zero_pow (by omega : 2 ≠ 0)] at hf
    exact (ne_of_gt (inv_pos.mpr (by linarith : 0 < (Fintype.card ι : ℝ) - 1))) hf.symm
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  let z' : ι → ℂ := fun i ↦ z i / (r : ℂ)
  let C' : Matrix ι ι ℂ := (r : ℂ) • C
  have hz' : ∀ i, |(z' i).re| ≤ 1 ∧ |(z' i).im| ≤ 1 := by
    intro i
    have hzi : ‖z i‖ ≤ r := by
      dsimp [r]
      rw [Matrix.l2_opNorm_diagonal]
      exact norm_le_pi_norm z i
    have hnz : ‖z' i‖ ≤ 1 := by
      dsimp [z']
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (div_le_one hr).mpr hzi
    exact ⟨(Complex.abs_re_le_norm _).trans hnz, (Complex.abs_im_le_norm _).trans hnz⟩
  have hcomm' : A = Matrix.diagonal z' * C' - C' * Matrix.diagonal z' := by
    rw [hcomm]
    ext i j
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.smul_apply, smul_eq_mul, z', C']
    field_simp
  have hc := diagonal_commutator_cost k hk hn A C' z' hz' hflat hcomm'
  have hnorm : ‖C'‖ = r * ‖C‖ := by
    dsimp [C']
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  rwa [hnorm] at hc

/-- The same explicit lower bound for the product cost of a matrix satisfying `Matrix.IsDiag`. -/
theorem isDiag_commutator_product_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k) (hn : Fintype.card ι = 4 ^ k)
    (A D C : Matrix ι ι ℂ) (hD : D.IsDiag)
    (hflat : ∀ i j, i ≠ j → ‖A i j‖ ^ 2 = ((Fintype.card ι : ℝ) - 1)⁻¹)
    (hcomm : A = D * C - C * D) :
    Real.sqrt ((((3 : ℝ) * k - 1) * Fintype.card ι + 1) /
      (32 * ((Fintype.card ι : ℝ) - 1))) ≤ ‖D‖ * ‖C‖ := by
  have hdiag := hD.diagonal_diag
  have hc := diagonal_commutator_product_cost k hk hn A C (Matrix.diag D) hflat
    (by simpa only [hdiag] using hcomm)
  simpa only [hdiag] using hc

/-- A convenient weaker product lower bound, uniform over all diagonal normalizations. -/
theorem isDiag_commutator_sqrt_k_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k) (hn : Fintype.card ι = 4 ^ k)
    (A D C : Matrix ι ι ℂ) (hD : D.IsDiag)
    (hflat : ∀ i j, i ≠ j → ‖A i j‖ ^ 2 = ((Fintype.card ι : ℝ) - 1)⁻¹)
    (hcomm : A = D * C - C * D) :
    Real.sqrt (k : ℝ) / 4 ≤ ‖D‖ * ‖C‖ :=
  (sqrt_k_lower_bound k hk (Fintype.card ι) (card_one_lt k hk hn)).trans
    (isDiag_commutator_product_cost k hk hn A D C hD hflat hcomm)

end PavingSeparation.DiagonalCost
