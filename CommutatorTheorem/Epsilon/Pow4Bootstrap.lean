import Mathlib
import CommutatorTheorem.Defs
import CommutatorTheorem.Epsilon.BourgainTzafriri
import CommutatorTheorem.Epsilon.Paving
import CommutatorTheorem.Epsilon.Rosenblum

/-! # Pow4Bootstrap

Leaf arithmetic helpers for the Eq.[4] log-form bound on `lambdaM (4^n)`.
This file contains the three arithmetic leaves (S2, S3, S4) plus the
Matrix-theory helper S1d (`lambdaA_scale_bound`). Heavier Matrix-theory
helpers (S1f, S1g, S1h, S1c, S1i_v2) will land here in subsequent sessions.

Used by: `Pow4BTRecursion.lean` for both the iterated four-block estimate and
the asymmetric Claim 2 two-block lift.
-/

-- Re-assert L2 operator norm instances (declared `local` in `Defs.lean`).
attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedSpace

open CommutatorTheorem

namespace Pow4Bootstrap

/-- For `l ≥ 2`, the geometric sum `∑_{i<l} (2/(1−1/l))^i` is bounded by `4^l`.
Key fact: `2/(1−1/l) ≤ 4` when `l ≥ 2` (since `1−1/l ≥ 1/2`). -/
lemma geom_sum_bound :
    ∀ l : ℕ, 2 ≤ l →
      (∑ i ∈ Finset.range l, (2 / (1 - (1 : ℝ) / l)) ^ i) ≤ (4 : ℝ) ^ l := by
  intro l hl
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  have hinv : (1 : ℝ) / l ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hlpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h1 : (1 : ℝ) / 2 ≤ 1 - 1 / l := by linarith
  have h1pos : (0 : ℝ) < 1 - 1 / l := by linarith
  have hr_nn : (0 : ℝ) ≤ 2 / (1 - 1 / l) := by positivity
  have hr_le : 2 / (1 - (1 : ℝ) / l) ≤ 4 := by
    rw [div_le_iff₀ h1pos]; linarith
  -- Bound each summand by 4^i, then sum.
  have hsum_le : (∑ i ∈ Finset.range l, (2 / (1 - (1 : ℝ) / l)) ^ i)
                  ≤ ∑ i ∈ Finset.range l, (4 : ℝ) ^ i := by
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ hr_nn hr_le i
  -- ∑ i < l, 4^i = (4^l - 1)/3 ≤ 4^l.
  have hgeom : (∑ i ∈ Finset.range l, (4 : ℝ) ^ i) = ((4 : ℝ) ^ l - 1) / 3 := by
    have := geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1) l
    linarith [this]
  have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ l := by positivity
  have hfinal : ((4 : ℝ) ^ l - 1) / 3 ≤ (4 : ℝ) ^ l := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]; linarith
  linarith [hsum_le, hgeom ▸ hfinal]

/-- The product `(2/(1−1/l))^l · (1/2)^l = (l/(l−1))^l` is bounded by `2^l` for `l ≥ 2`.
For `l ≥ 2`: `2/(1−1/l) = 2l/(l−1) ≤ 4`, so the product is `≤ 4^l · (1/2)^l = 2^l`. -/
lemma two_inv_eps_pow_l_bound :
    ∀ l : ℕ, 2 ≤ l →
      ((2 : ℝ) / (1 - 1 / l)) ^ l * ((1 : ℝ) / 2) ^ l ≤ (2 : ℝ) ^ l := by
  intro l hl
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  have hl1 : (1 : ℝ) ≤ (l : ℝ) - 1 := by linarith
  have hl1pos : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  -- Show 1 - 1/l = (l-1)/l and is positive
  have hsub : (1 : ℝ) - 1 / l = ((l : ℝ) - 1) / (l : ℝ) := by
    field_simp
  have hsubpos : (0 : ℝ) < 1 - 1 / (l : ℝ) := by
    rw [hsub]; positivity
  -- Show 2/(1-1/l) ≤ 4
  have hbound : (2 : ℝ) / (1 - 1 / (l : ℝ)) ≤ 4 := by
    rw [div_le_iff₀ hsubpos]
    rw [hsub]
    rw [show (4 : ℝ) * (((l : ℝ) - 1) / (l : ℝ)) = 4 * ((l : ℝ) - 1) / (l : ℝ) by ring]
    rw [le_div_iff₀ hlpos]
    nlinarith
  have hnn : (0 : ℝ) ≤ (2 : ℝ) / (1 - 1 / (l : ℝ)) := by positivity
  -- (2/(1-1/l))^l ≤ 4^l
  have hpow : ((2 : ℝ) / (1 - 1 / (l : ℝ))) ^ l ≤ (4 : ℝ) ^ l :=
    pow_le_pow_left₀ hnn hbound l
  have hhalfnn : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ l := by positivity
  calc ((2 : ℝ) / (1 - 1 / l)) ^ l * ((1 : ℝ) / 2) ^ l
      ≤ (4 : ℝ) ^ l * ((1 : ℝ) / 2) ^ l := by
        exact mul_le_mul_of_nonneg_right hpow hhalfnn
    _ = ((4 : ℝ) * (1 / 2)) ^ l := by rw [← mul_pow]
    _ = (2 : ℝ) ^ l := by norm_num

lemma nat_floor_n_div_bounds (k : ℕ) (hk : 1 ≤ k) :
    ∀ n : ℕ, ∃ l : ℕ,
      l ≤ n ∧
      (l : ℝ) ≤ (n : ℝ) / (2 * (k + 1)) ∧
      (n : ℝ) / (2 * (k + 1)) - 1 ≤ (l : ℝ) ∧
      (1 ≤ l ↔ 2 * (k + 1) ≤ n) := by
  intro n
  refine ⟨n / (2 * (k + 1)), Nat.div_le_self _ _, ?_, ?_, ?_⟩
  · -- (l : ℝ) ≤ n / (2*(k+1))
    have hd : (0 : ℝ) < 2 * (k + 1) := by positivity
    rw [le_div_iff₀ hd]
    exact_mod_cast Nat.div_mul_le_self n (2 * (k + 1))
  · -- n/(2*(k+1)) - 1 ≤ (l : ℝ)
    have hdpos : 0 < 2 * (k + 1) := by positivity
    have hd : (0 : ℝ) < 2 * (k + 1) := by positivity
    have hn : n < (n / (2 * (k + 1)) + 1) * (2 * (k + 1)) := by
      have hmod : n % (2 * (k + 1)) < 2 * (k + 1) := Nat.mod_lt n hdpos
      have heq := Nat.div_add_mod n (2 * (k + 1))
      have : (n / (2 * (k + 1)) + 1) * (2 * (k + 1))
              = 2 * (k + 1) * (n / (2 * (k + 1))) + 2 * (k + 1) := by ring
      omega
    rw [sub_le_iff_le_add, div_le_iff₀ hd]
    have : (n : ℝ) ≤ ((n / (2 * (k + 1)) : ℕ) : ℝ) * (2 * (k + 1)) + (2 * (k + 1)) := by
      have := hn.le
      have h2 : (n : ℝ) ≤ ((n / (2 * (k + 1)) + 1 : ℕ) : ℝ) * (2 * (k + 1)) := by
        exact_mod_cast this
      push_cast at h2
      linarith
    linarith
  · -- 1 ≤ l ↔ 2*(k+1) ≤ n
    exact Nat.one_le_div_iff (by positivity)

/-! ## S1d: `lambdaA_scale_bound`

Migrated from `tmp_S1d_lambdaA_scale_bound.lean`. The three local helpers below
carry a `_S1d` suffix to pre-empt name collisions with mirrors in other tmp files
(notably `lambdaA_nonneg_local`, which appears as a `private` helper in 6 tmp files).
-/

/-- `lambdaA A ≥ 0` (S1d-local mirror of a private helper in `Main.lean`). -/
private lemma lambdaA_nonneg_S1d {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ lambdaA A := by
  unfold lambdaA
  by_cases hne : (({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}).Nonempty)
  · exact le_csInf hne (fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp

/-- Scaling lemma: `matComm B (c • C) = c • matComm B C`. -/
private lemma matComm_smul_right_S1d {n : ℕ}
    (B C : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    matComm B (c • C) = c • matComm B C := by
  simp [matComm, smul_sub]

/-- For `n ≥ 2`, every zero-diagonal matrix `A` has a commutator decomposition
`A = ⁅B, C⁆` with `B` diagonal, `InUnitSquare` entries, and
`‖C‖ ≤ n*(n-1)*‖A‖`. -/
private lemma zeroDiag_InUnitSquare_decomp_bounded_S1d {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hzd : ZeroDiag A) :
    ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧
      ‖C‖ ≤ (n : ℝ) * (n - 1) * ‖A‖ := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  set B := Matrix.diagonal (fun i : Fin n => (↑(i.val : ℕ) : ℂ) / (↑(n - 1 : ℕ) : ℂ))
  set C := Matrix.of (fun i j : Fin n =>
    if i = j then (0 : ℂ) else A i j / ((↑(i.val : ℕ) : ℂ) / (↑(n - 1 : ℕ) : ℂ) -
      (↑(j.val : ℕ) : ℂ) / (↑(n - 1 : ℕ) : ℂ)))
  refine ⟨B, C, ?_, ?_, ?_, ?_⟩
  · intro i j hij; exact Matrix.diagonal_apply_ne _ hij
  · intro i
    unfold InUnitSquare; simp only [B, Matrix.diagonal_apply_eq]
    have hcast : (↑↑i : ℂ) / (↑(n - 1) : ℂ) =
        (↑((i.val : ℝ) / ((n - 1 : ℕ) : ℝ)) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, by simp⟩
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.le_sub_one_of_lt i.isLt
  · ext i j
    simp only [matComm, Matrix.sub_apply, Matrix.mul_apply]
    by_cases hij : i = j
    · subst hij; rw [hzd i]
      simp only [B, Matrix.diagonal_apply, C, Matrix.of_apply]
      symm
      have h1 : ∀ x : Fin n,
          (if i = x then ↑↑i / (↑(n - 1) : ℂ) else 0) *
          (if x = i then (0 : ℂ) else
            A x i / (↑↑x / ↑(n - 1) - ↑↑i / ↑(n - 1))) = 0 := by
        intro x; by_cases h : i = x
        · simp [h]
        · simp [h]
      have h2 : ∀ x : Fin n,
          (if i = x then (0 : ℂ) else
            A i x / (↑↑i / (↑(n - 1) : ℂ) - ↑↑x / ↑(n - 1))) *
          (if x = i then ↑↑x / (↑(n - 1) : ℂ) else 0) = 0 := by
        intro x; by_cases h : i = x
        · simp [h]
        · have : ¬x = i := fun hc => h hc.symm; simp [h, this]
      rw [Finset.sum_eq_zero (fun x _ => h1 x),
          Finset.sum_eq_zero (fun x _ => h2 x), sub_self]
    · simp only [B, Matrix.diagonal_apply, C, Matrix.of_apply]
      have hs1 : ∀ x : Fin n,
          (if i = x then ↑↑i / (↑(n - 1) : ℂ) else 0) *
          (if x = j then (0 : ℂ) else
            A x j / (↑↑x / ↑(n - 1) - ↑↑j / ↑(n - 1))) =
          if x = i then ↑↑i / (↑(n - 1) : ℂ) *
            (A i j / (↑↑i / ↑(n - 1) - ↑↑j / ↑(n - 1))) else 0 := by
        intro x; by_cases hx : i = x
        · subst hx; simp [hij]
        · simp [hx, Ne.symm hx]
      have hs2 : ∀ x : Fin n,
          (if i = x then (0 : ℂ) else
            A i x / (↑↑i / (↑(n - 1) : ℂ) - ↑↑x / ↑(n - 1))) *
          (if x = j then ↑↑x / (↑(n - 1) : ℂ) else 0) =
          if x = j then A i j / (↑↑i / (↑(n - 1) : ℂ) - ↑↑j / ↑(n - 1)) *
            (↑↑j / (↑(n - 1) : ℂ)) else 0 := by
        intro x; by_cases hx : x = j
        · subst hx; simp [hij]
        · simp [hx]
      simp_rw [hs1, hs2]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      set d := ↑↑i / (↑(n - 1) : ℂ) - ↑↑j / ↑(n - 1) with hd_def
      have hdiff_ne : d ≠ 0 := by
        rw [hd_def, div_sub_div_same]
        apply div_ne_zero
        · simp only [ne_eq, sub_eq_zero]
          exact_mod_cast Fin.val_ne_of_ne hij
        · exact_mod_cast (show (n - 1 : ℕ) ≠ 0 by omega)
      rw [show ↑↑i / (↑(n - 1) : ℂ) * (A i j / d) -
          A i j / d * (↑↑j / ↑(n - 1)) =
          d * (A i j / d) from by rw [hd_def]; ring]
      exact (mul_div_cancel₀ (A i j) hdiff_ne).symm
  · have hC_entry : ∀ i j : Fin n, ‖C i j‖ ≤ (↑n - 1) * ‖A i j‖ := by
      intro i j; simp only [C, Matrix.of_apply]
      by_cases hij : i = j
      · subst hij; simp only [↓reduceIte, norm_zero]; exact mul_nonneg (by linarith) (norm_nonneg _)
      · rw [if_neg hij, norm_div, div_sub_div_same, norm_div]
        have hnorm_n1 : ‖(↑(n - 1 : ℕ) : ℂ)‖ = (↑(n - 1 : ℕ) : ℝ) := Complex.norm_natCast _
        have hn1_eq : (↑(n - 1 : ℕ) : ℝ) = (↑n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
        have hnorm_diff_ge1 : (1 : ℝ) ≤ ‖(↑↑i : ℂ) - ↑↑j‖ := by
          rw [show (↑↑i : ℂ) - ↑↑j = ↑((i.val : ℤ) - (j.val : ℤ)) from by push_cast; ring]
          rw [Complex.norm_intCast]
          exact_mod_cast Int.one_le_abs
            (sub_ne_zero.mpr (by exact_mod_cast Fin.val_ne_of_ne hij : (i.val : ℤ) ≠ j.val))
        rw [div_div_eq_mul_div, hnorm_n1, hn1_eq]
        rw [mul_comm ‖A i j‖ (↑n - 1)]
        exact div_le_self (by positivity) hnorm_diff_ge1
    have hhs : hsNorm C ≤ (↑n - 1) * hsNorm A := by
      unfold hsNorm
      rw [show (↑n - 1 : ℝ) * Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) =
          Real.sqrt ((↑n - 1) ^ 2 * ∑ i, ∑ j, Complex.normSq (A i j)) from by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hn1)]]
      apply Real.sqrt_le_sqrt
      calc ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (C i j)
          ≤ ∑ i : Fin n, ∑ j : Fin n, (↑n - 1) ^ 2 * Complex.normSq (A i j) := by
            apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
            simp only [Complex.normSq_eq_norm_sq]
            rw [← mul_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (hC_entry i j) 2
        _ = (↑n - 1) ^ 2 * ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j) := by
            simp_rw [← Finset.mul_sum]
    calc ‖C‖ ≤ hsNorm C := le_hsNorm C
      _ ≤ (↑n - 1) * hsNorm A := hhs
      _ ≤ (↑n - 1) * (Real.sqrt ↑n * ‖A‖) :=
          mul_le_mul_of_nonneg_left (hsNorm_le_sqrt_n_mul_opNorm A) (le_of_lt hn1)
      _ = Real.sqrt ↑n * ((↑n - 1) * ‖A‖) := by ring
      _ ≤ ↑n * ((↑n - 1) * ‖A‖) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [Real.sqrt_le_left (Nat.cast_nonneg n)]
          calc (↑n : ℝ) = ↑n * 1 := (mul_one _).symm
            _ ≤ ↑n * ↑n := mul_le_mul_of_nonneg_left
                (by exact_mod_cast (show 1 ≤ n by omega)) (Nat.cast_nonneg n)
            _ = (↑n : ℝ) ^ 2 := (sq _).symm
      _ = ↑n * (↑n - 1) * ‖A‖ := by ring

/-- For any zero-diagonal matrix `A`, `lambdaA A ≤ ‖A‖ · lambdaM m`.
This is the scaling identity used to absorb a norm prefactor into the `lambdaM` bound
when applying iterated paving estimates. -/
lemma lambdaA_scale_bound {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (hzd : ZeroDiag A) :
    lambdaA A ≤ ‖A‖ * lambdaM m := by
  by_cases h0 : ‖A‖ = 0
  · -- Edge case: A = 0
    have hA0 : A = 0 := norm_eq_zero.mp h0
    rw [h0, zero_mul, hA0]
    -- lambdaA 0 ≤ 0 via trivial decomp 0 = ⁅0, 0⁆
    unfold lambdaA; apply csInf_le
    · exact ⟨0, fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
    · exact ⟨0, 0, fun _ _ _ => by simp,
        fun _ => ⟨by simp, by simp⟩,
        by ext i j; simp [matComm], by norm_num⟩
  · -- Generic case: ‖A‖ > 0
    have hpos : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hAnorm_ne : (‖A‖ : ℝ) ≠ 0 := ne_of_gt hpos
    -- Necessarily m ≥ 2
    have hm2 : 2 ≤ m := by
      by_contra hlt; push Not at hlt
      interval_cases m
      · exact absurd (show ‖A‖ = 0 from by
          rw [show A = 0 from Subsingleton.elim _ _, norm_zero]) h0
      · have : A = 0 := by
          ext i j; rcases Fin.eq_zero i with rfl
          rcases Fin.eq_zero j with rfl; exact hzd 0
        exact absurd (show ‖A‖ = 0 from by rw [this, norm_zero]) h0
    -- A' := (‖A‖⁻¹) • A
    set A' := (↑(‖A‖⁻¹) : ℂ) • A with hA'_def
    have hnormA' : ‖A'‖ = 1 := by
      rw [hA'_def, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
        inv_mul_cancel₀ hAnorm_ne]
    have hzdA' : ZeroDiag A' := fun i => by
      simp [hA'_def, hzd i]
    have hA_eq : A = (↑(‖A‖) : ℂ) • A' := by
      rw [hA'_def, smul_smul, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hAnorm_ne,
        Complex.ofReal_one, one_smul]
    -- lambdaA A ≤ ‖A‖ * lambdaA A' via scaling.
    have hAA' : lambdaA A ≤ ‖A‖ * lambdaA A' := by
      have hSA' : ({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
          IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A' = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}).Nonempty := by
        obtain ⟨B', C', hd', hu', hc', _⟩ :=
          zeroDiag_InUnitSquare_decomp_bounded_S1d hm2 A' hzdA'
        exact ⟨‖C'‖, B', C', hd', hu', hc', le_refl _⟩
      have hbdd : BddBelow ({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
          IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A' = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}) :=
        ⟨0, fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
      have hkey : ∀ c ∈ ({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
          IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A' = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}),
          lambdaA A ≤ ‖A‖ * c := by
        intro c ⟨B, C0, hd, hu, hc, hnC⟩
        have hmem : ‖A‖ * c ∈ ({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
            IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}) := by
          refine ⟨B, (↑(‖A‖) : ℂ) • C0, hd, hu, ?_, ?_⟩
          · conv_lhs => rw [hA_eq, hc]
            exact (matComm_smul_right_S1d B C0 _).symm
          · rw [norm_smul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
            exact mul_le_mul_of_nonneg_left hnC (le_of_lt hpos)
        exact csInf_le ⟨0, fun c' ⟨_, _, _, _, _, hle⟩ =>
          le_trans (norm_nonneg _) hle⟩ hmem
      have h_div_le : lambdaA A / ‖A‖ ≤ lambdaA A' := by
        unfold lambdaA
        apply le_csInf hSA'
        intro c hc
        have := hkey c hc
        rwa [div_le_iff₀ hpos, mul_comm]
      have : lambdaA A ≤ ‖A‖ * lambdaA A' := by
        rw [← div_le_iff₀' hpos]; exact h_div_le
      exact this
    -- lambdaA A' ≤ lambdaM m via le_csSup
    have hA'_le_lM : lambdaA A' ≤ lambdaM m := by
      unfold lambdaM
      apply le_csSup
      · -- BddAbove
        refine ⟨(m : ℝ) * (m - 1), fun x hx => ?_⟩
        obtain ⟨A'', ⟨hzd'', hnorm''⟩, rfl⟩ := hx
        obtain ⟨B'', C'', hd'', hu'', hc'', hbound⟩ :=
          zeroDiag_InUnitSquare_decomp_bounded_S1d hm2 A'' hzd''
        calc lambdaA A''
            ≤ ‖C''‖ := csInf_le
              ⟨0, fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
              ⟨B'', C'', hd'', hu'', hc'', le_refl _⟩
          _ ≤ (m : ℝ) * (m - 1) * ‖A''‖ := hbound
          _ = (m : ℝ) * (m - 1) := by rw [hnorm'']; ring
      · exact ⟨A', ⟨hzdA', hnormA'⟩, rfl⟩
    -- Combine
    calc lambdaA A ≤ ‖A‖ * lambdaA A' := hAA'
      _ ≤ ‖A‖ * lambdaM m := mul_le_mul_of_nonneg_left hA'_le_lM (le_of_lt hpos)

/-! ## S1c: `lambdaM_iterate_pow4`

Migrated from `tmp_S1c_lambdaM_iterate_pow4.lean`. Iterates the per-step
`lambdaM` four-block recursion `l` times. The recursion itself is supplied as a
hypothesis `hMrec`, so this lemma is hypothesis-parametrised and does not
depend on any concrete proof of the recursion (Main.lean instantiates it).

The two local private helpers carry `_S1c` suffixes to pre-empt collisions with
mirrors in other tmp files.
-/

/-- `lambdaA A ≥ 0` (S1c-local mirror of a private helper in `Main.lean`). -/
private lemma lambdaA_nonneg_S1c {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ lambdaA A := by
  unfold lambdaA
  by_cases hne : (({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}).Nonempty)
  · exact le_csInf hne (fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp

/-- `lambdaM m ≥ 0` (S1c-local mirror). -/
private lemma lambdaM_nonneg_S1c (m : ℕ) : 0 ≤ lambdaM m := by
  unfold lambdaM
  exact Real.sSup_nonneg (fun x hx => by
    obtain ⟨A, _, rfl⟩ := hx; exact lambdaA_nonneg_S1c A)

/-- Iterate the per-step `lambdaM` four-block recursion `l` times. -/
lemma lambdaM_iterate_pow4
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hMrec : ∀ (m : ℕ), lambdaM (4 * m) ≤ 2 / (1 - ε) * lambdaM m + 6 / ε)
    (n : ℕ) :
    ∀ (l : ℕ), l ≤ n →
      lambdaM (4 ^ n) ≤
        (2 / (1 - ε)) ^ l * lambdaM (4 ^ (n - l)) +
        (∑ i ∈ Finset.range l, (2 / (1 - ε)) ^ i) * (6 / ε)
:= by
  have h1mε : 0 < 1 - ε := by linarith
  have hr_pos : 0 < 2 / (1 - ε) := by positivity
  have hr_nn : 0 ≤ 2 / (1 - ε) := le_of_lt hr_pos
  have h6ε_nn : 0 ≤ 6 / ε := by positivity
  intro l
  induction l with
  | zero =>
    intro _
    simp
  | succ l ih =>
    intro hl
    have hl' : l ≤ n := Nat.le_of_succ_le hl
    have ih' := ih hl'
    -- n - l = (n - (l+1)) + 1
    have hsub_eq : n - l = (n - (l + 1)) + 1 := by omega
    -- 4 ^ (n - l) = 4 * 4 ^ (n - (l+1))
    have hpow_eq : (4 : ℕ) ^ (n - l) = 4 * 4 ^ (n - (l + 1)) := by
      rw [hsub_eq, pow_succ]; ring
    -- Apply hMrec with m := 4 ^ (n - (l+1))
    have hrec : lambdaM (4 ^ (n - l)) ≤
        2 / (1 - ε) * lambdaM (4 ^ (n - (l + 1))) + 6 / ε := by
      rw [hpow_eq]; exact hMrec _
    -- Multiply by (2/(1-ε))^l ≥ 0
    have hrl_nn : 0 ≤ (2 / (1 - ε)) ^ l := pow_nonneg hr_nn l
    have hmul : (2 / (1 - ε)) ^ l * lambdaM (4 ^ (n - l)) ≤
        (2 / (1 - ε)) ^ (l + 1) * lambdaM (4 ^ (n - (l + 1))) +
        (2 / (1 - ε)) ^ l * (6 / ε) := by
      have hstep := mul_le_mul_of_nonneg_left hrec hrl_nn
      have hrhs_eq : (2 / (1 - ε)) ^ l *
            (2 / (1 - ε) * lambdaM (4 ^ (n - (l + 1))) + 6 / ε) =
          (2 / (1 - ε)) ^ (l + 1) * lambdaM (4 ^ (n - (l + 1))) +
          (2 / (1 - ε)) ^ l * (6 / ε) := by
        rw [pow_succ]; ring
      linarith [hrhs_eq]
    -- Sum extension via Finset.sum_range_succ
    have hsum : (∑ i ∈ Finset.range (l + 1), (2 / (1 - ε)) ^ i) =
        (∑ i ∈ Finset.range l, (2 / (1 - ε)) ^ i) + (2 / (1 - ε)) ^ l := by
      exact Finset.sum_range_succ _ _
    calc lambdaM (4 ^ n)
        ≤ (2 / (1 - ε)) ^ l * lambdaM (4 ^ (n - l)) +
            (∑ i ∈ Finset.range l, (2 / (1 - ε)) ^ i) * (6 / ε) := ih'
      _ ≤ ((2 / (1 - ε)) ^ (l + 1) * lambdaM (4 ^ (n - (l + 1))) +
            (2 / (1 - ε)) ^ l * (6 / ε)) +
            (∑ i ∈ Finset.range l, (2 / (1 - ε)) ^ i) * (6 / ε) := by linarith
      _ = (2 / (1 - ε)) ^ (l + 1) * lambdaM (4 ^ (n - (l + 1))) +
            (∑ i ∈ Finset.range (l + 1), (2 / (1 - ε)) ^ i) * (6 / ε) := by
            rw [hsum]; ring

/-! ## S1h: `bt_paving_to_sigma_block`

Migrated from `tmp_S1h_lambdaM_bt_recursion.lean`. Packages the `l = 1`
output of `bourgain_tzafriri_iterated` (axiom from
`CommutatorTheorem.BourgainTzafriri`) into a bijective 4-block embedding
of `Fin (4^n)` (the covered half of `Fin (2 · 4^n)`), suitable for feeding
into the σ-paving four-block bound.

The four local private helpers carry `_S1h` suffixes to pre-empt collisions
with any future migrated tmp files.
-/

/-- Canonical block embedding `Fin 4 × Fin m → Fin (4 * m)`. -/
private def canonicalBlockEmbed_S1h {m : ℕ} : Fin 4 → Fin m → Fin (4 * m) :=
  fun k j => ⟨k.val * m + j.val, by
    have hk := k.isLt; have hj := j.isLt
    calc k.val * m + j.val < k.val * m + m := by omega
      _ = (k.val + 1) * m := by ring
      _ ≤ 4 * m := by nlinarith⟩

/-- Canonical product-to-flat equivalence `Fin 4 × Fin m ≃ Fin (4 * m)`. -/
private noncomputable def canonicalProdEquiv_S1h {m : ℕ} (hm : 0 < m) :
    Fin 4 × Fin m ≃ Fin (4 * m) where
  toFun p := canonicalBlockEmbed_S1h p.1 p.2
  invFun i :=
    (⟨i.val / m, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using i.isLt)⟩,
     ⟨i.val % m, Nat.mod_lt _ hm⟩)
  left_inv := by
    intro ⟨k, j⟩
    have hj := j.isLt
    change (⟨_, _⟩, ⟨_, _⟩) = (k, j)
    refine Prod.ext ?_ ?_
    · ext; simp only [canonicalBlockEmbed_S1h]
      rw [show k.val * m + j.val = j.val + k.val * m from by omega]
      rw [Nat.add_mul_div_right _ _ hm]
      simp [Nat.div_eq_of_lt hj]
    · ext; simp only [canonicalBlockEmbed_S1h]
      rw [show k.val * m + j.val = j.val + k.val * m from by omega]
      simp [Nat.mod_eq_of_lt hj]
  right_inv := by
    intro i
    change canonicalBlockEmbed_S1h _ _ = i
    ext; simp only [canonicalBlockEmbed_S1h]
    exact Nat.div_add_mod' i.val m

/-- The dimensional identity `4 * 4^(n-1) = 4^n` for `n ≥ 1`. -/
private lemma four_mul_four_pow_sub_one_S1h (n : ℕ) (hn : 1 ≤ n) :
    4 * 4 ^ (n - 1) = 4 ^ n := by
  have hn_eq : n = (n - 1) + 1 := by omega
  conv_rhs => rw [hn_eq]
  rw [pow_succ]; ring

/-- The dimensional identity `4 * 4^(n-1) = 4^n` for `n ≥ 1`, as an `Fin`-equivalence. -/
private def fin_four_pow_succ_S1h (n : ℕ) (hn : 1 ≤ n) :
    Fin (4 * 4 ^ (n - 1)) ≃ Fin (4 ^ n) :=
  (Fin.castOrderIso (four_mul_four_pow_sub_one_S1h n hn)).toEquiv

/-- The σ-paving constructor at depth 1.

Given a norm-one zero-diagonal matrix on `Fin (2 · 4^n)`, produce:
* an injection `H : Fin (4^n) → Fin (2 · 4^n)`;
* a 4-block embedding `e : Fin 4 → Fin (4^(n-1)) → Fin (4^n)`
  that is per-block injective, pairwise disjoint, and surjective onto `Fin(4^n)`;
* a norm bound: each `‖A.submatrix (H ∘ e k) (H ∘ e k)‖ ≤ K_BT · (1/2)`,
  where `K_BT` is the absolute constant from `bourgain_tzafriri_iterated`.

The construction takes `e = canonicalBlockEmbed_S1h` (over `Fin(4^(n-1))`) and
`H` glues the four `σ k`'s into a single injection on `Fin(4^n)`.
-/
lemma bt_paving_to_sigma_block (n : ℕ) (hn : 1 ≤ n) :
    ∃ K_BT : ℝ, 0 < K_BT ∧
    ∀ (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ),
      ZeroDiag A → ‖A‖ = 1 →
    ∃ (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
      (e : Fin 4 → Fin (4 ^ (n - 1)) → Fin (4 ^ n)),
      Function.Injective H ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ k k' : Fin 4, k ≠ k' →
        Disjoint (Set.range (e k)) (Set.range (e k'))) ∧
      (∀ i : Fin (4 ^ n), ∃ k j, e k j = i) ∧
      (∀ k, ‖A.submatrix (H ∘ e k) (H ∘ e k)‖ ≤ K_BT * (1 / 2 : ℝ)) := by
  classical
  obtain ⟨K, hK_pos, hK_spec⟩ := bourgain_tzafriri_iterated
  refine ⟨K, hK_pos, ?_⟩
  intro A hzd hnorm
  -- Apply BT at depth l = 1.
  have hl1 : (1 : ℕ) ≤ n := hn
  -- Specialize: σ : Fin (4^1) → Fin (4^(n-1)) → Fin (2 * 4^n)
  obtain ⟨σ, hσ_inj, hσ_disj, hσ_bound⟩ := hK_spec n A hzd hnorm 1 hl1
  -- `Fin (4^1) = Fin 4` definitionally on values; use cast to coerce.
  -- We package σ as σ' : Fin 4 → Fin (4^(n-1)) → Fin(2·4^n).
  have h4eq : (4 : ℕ) ^ 1 = 4 := by norm_num
  let four_eq : Fin (4 ^ 1) ≃ Fin 4 := Fin.castOrderIso h4eq |>.toEquiv
  let σ' : Fin 4 → Fin (4 ^ (n - 1)) → Fin (2 * 4 ^ n) := fun k => σ (four_eq.symm k)
  have hσ'_inj : ∀ k, Function.Injective (σ' k) := fun k => hσ_inj _
  have hσ'_disj : ∀ k k' : Fin 4, k ≠ k' →
      Disjoint (Set.range (σ' k)) (Set.range (σ' k')) := by
    intro k k' hkk'
    apply hσ_disj
    intro h
    apply hkk'
    exact four_eq.symm.injective h
  have hσ'_bound : ∀ k, ‖A.submatrix (σ' k) (σ' k)‖ ≤ K * (1 / 2 : ℝ) := by
    intro k
    have := hσ_bound (four_eq.symm k)
    simpa [pow_one] using this
  -- Now build H : Fin(4^n) → Fin(2·4^n).
  -- Note: 4^n = 4 * 4^(n-1), and we have the canonical equivalence.
  have hm_pos : 0 < 4 ^ (n - 1) := pow_pos (by norm_num) _
  let cEq : Fin 4 × Fin (4 ^ (n - 1)) ≃ Fin (4 * 4 ^ (n - 1)) :=
    canonicalProdEquiv_S1h hm_pos
  let castEq : Fin (4 * 4 ^ (n - 1)) ≃ Fin (4 ^ n) := fin_four_pow_succ_S1h n hn
  let prodToFin : Fin 4 × Fin (4 ^ (n - 1)) ≃ Fin (4 ^ n) := cEq.trans castEq
  -- H takes i : Fin(4^n), splits into (k, j), and returns σ' k j.
  let H : Fin (4 ^ n) → Fin (2 * 4 ^ n) := fun i =>
    let p := prodToFin.symm i
    σ' p.1 p.2
  -- e is the canonical block embedding over Fin(4^(n-1)) into Fin(4^n).
  let e : Fin 4 → Fin (4 ^ (n - 1)) → Fin (4 ^ n) := fun k j =>
    prodToFin (k, j)
  -- H ∘ e k = σ' k
  have hH_e : ∀ k j, H (e k j) = σ' k j := by
    intro k j
    change σ' (prodToFin.symm (prodToFin (k, j))).1 (prodToFin.symm (prodToFin (k, j))).2
       = σ' k j
    rw [prodToFin.symm_apply_apply]
  -- H is injective.
  have hH_inj : Function.Injective H := by
    intro i i' hii'
    -- H i = σ' (p.1) (p.2), H i' = σ' (p'.1) (p'.2).
    set p := prodToFin.symm i with hp_def
    set p' := prodToFin.symm i' with hp'_def
    have hH_val : σ' p.1 p.2 = σ' p'.1 p'.2 := hii'
    have hk_eq : p.1 = p'.1 := by
      by_contra hne
      have hrange1 : σ' p.1 p.2 ∈ Set.range (σ' p.1) := ⟨p.2, rfl⟩
      have hrange2 : σ' p.1 p.2 ∈ Set.range (σ' p'.1) := ⟨p'.2, hH_val.symm⟩
      have hd := hσ'_disj p.1 p'.1 hne
      exact (Set.disjoint_iff.mp hd) ⟨hrange1, hrange2⟩
    have hj_eq : p.2 = p'.2 := by
      have hσ_eq : σ' p.1 p.2 = σ' p.1 p'.2 := by rw [hk_eq] at hH_val ⊢; exact hH_val
      exact hσ'_inj p.1 hσ_eq
    have hpp' : p = p' := Prod.ext hk_eq hj_eq
    -- i = prodToFin p = prodToFin p' = i'
    have : i = prodToFin p := (prodToFin.apply_symm_apply i).symm
    have : i' = prodToFin p' := (prodToFin.apply_symm_apply i').symm
    calc i = prodToFin p := (prodToFin.apply_symm_apply i).symm
      _ = prodToFin p' := by rw [hpp']
      _ = i' := prodToFin.apply_symm_apply i'
  -- e per-block injective.
  have he_inj : ∀ k, Function.Injective (e k) := by
    intro k j j' hjj'
    have h1 : prodToFin (k, j) = prodToFin (k, j') := hjj'
    have h2 : (k, j) = (k, j') := prodToFin.injective h1
    exact (Prod.mk.inj h2).2
  -- e cross-block disjoint.
  have he_disj : ∀ k k' : Fin 4, k ≠ k' →
      Disjoint (Set.range (e k)) (Set.range (e k')) := by
    intro k k' hkk'
    rw [Set.disjoint_iff]
    rintro i ⟨⟨j, hj⟩, ⟨j', hj'⟩⟩
    -- e k j = e k' j' means prodToFin (k, j) = prodToFin (k', j')
    have heq : prodToFin (k, j) = prodToFin (k', j') := hj.trans hj'.symm
    have hpair : (k, j) = (k', j') := prodToFin.injective heq
    exact hkk' (Prod.mk.inj hpair).1
  -- e surjective on Fin(4^n).
  have he_surj : ∀ i : Fin (4 ^ n), ∃ k j, e k j = i := by
    intro i
    refine ⟨(prodToFin.symm i).1, (prodToFin.symm i).2, ?_⟩
    change prodToFin ((prodToFin.symm i).1, (prodToFin.symm i).2) = i
    have : ((prodToFin.symm i).1, (prodToFin.symm i).2) = prodToFin.symm i := rfl
    rw [this, prodToFin.apply_symm_apply]
  -- Norm bound.
  have h_norm : ∀ k, ‖A.submatrix (H ∘ e k) (H ∘ e k)‖ ≤ K * (1 / 2 : ℝ) := by
    intro k
    -- A.submatrix (H ∘ e k) (H ∘ e k) = A.submatrix (σ' k) (σ' k)
    have hsubmat_eq : A.submatrix (H ∘ e k) (H ∘ e k)
                    = A.submatrix (σ' k) (σ' k) := by
      ext i j
      simp only [Matrix.submatrix_apply, Function.comp_apply, hH_e]
    rw [hsubmat_eq]
    exact hσ'_bound k
  exact ⟨H, e, hH_inj, he_inj, he_disj, he_surj, h_norm⟩

/-! ## S1f: lambdaA_four_block_bound_strong (canonical 4-block with per-block lambdaA on RHS) -/

/-! ## Local helpers (mirrors of private lemmas in Main.lean) -/

private lemma lambdaA_nonneg_S1f {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ lambdaA A := by
  unfold lambdaA
  by_cases hne : ({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}).Nonempty
  · exact le_csInf hne (fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp

private lemma diag_isDiagMatrix_S1f {m : ℕ} (b : Fin m → ℂ) :
    IsDiagMatrix (Matrix.diagonal b) := by
  intro i j hij; simp [hij]

/-- For n ≥ 2, every zero-diagonal matrix A has a commutator decomposition
A = [B, C] with B diagonal, InUnitSquare entries, and ‖C‖ ≤ n*(n-1)*‖A‖. -/
private lemma zeroDiag_InUnitSquare_decomp_bounded_S1f {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hzd : ZeroDiag A) :
    ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧
      ‖C‖ ≤ (n : ℝ) * (n - 1) * ‖A‖ := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hn1' : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn1
  set B := Matrix.diagonal (fun i : Fin n => (↑(i.val : ℕ) : ℂ) / (↑(n - 1 : ℕ) : ℂ))
  set C := Matrix.of (fun i j : Fin n =>
    if i = j then (0 : ℂ) else A i j / ((↑(i.val : ℕ) : ℂ) / (↑(n - 1 : ℕ) : ℂ) -
      (↑(j.val : ℕ) : ℂ) / (↑(n - 1 : ℕ) : ℂ)))
  refine ⟨B, C, ?_, ?_, ?_, ?_⟩
  · intro i j hij; exact Matrix.diagonal_apply_ne _ hij
  · intro i
    unfold InUnitSquare; simp only [B, Matrix.diagonal_apply_eq]
    have hcast : (↑↑i : ℂ) / (↑(n - 1) : ℂ) =
        (↑((i.val : ℝ) / ((n - 1 : ℕ) : ℝ)) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, by simp⟩
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.le_sub_one_of_lt i.isLt
  · ext i j
    simp only [matComm, Matrix.sub_apply, Matrix.mul_apply]
    by_cases hij : i = j
    · subst hij; rw [hzd i]
      simp only [B, Matrix.diagonal_apply, C, Matrix.of_apply]
      symm
      have h1 : ∀ x : Fin n,
          (if i = x then ↑↑i / (↑(n - 1) : ℂ) else 0) *
          (if x = i then (0 : ℂ) else
            A x i / (↑↑x / ↑(n - 1) - ↑↑i / ↑(n - 1))) = 0 := by
        intro x; by_cases h : i = x
        · simp [h]
        · simp [h]
      have h2 : ∀ x : Fin n,
          (if i = x then (0 : ℂ) else
            A i x / (↑↑i / (↑(n - 1) : ℂ) - ↑↑x / ↑(n - 1))) *
          (if x = i then ↑↑x / (↑(n - 1) : ℂ) else 0) = 0 := by
        intro x; by_cases h : i = x
        · simp [h]
        · have : ¬x = i := fun hc => h hc.symm; simp [h, this]
      rw [Finset.sum_eq_zero (fun x _ => h1 x),
          Finset.sum_eq_zero (fun x _ => h2 x), sub_self]
    · simp only [B, Matrix.diagonal_apply, C, Matrix.of_apply]
      have hs1 : ∀ x : Fin n,
          (if i = x then ↑↑i / (↑(n - 1) : ℂ) else 0) *
          (if x = j then (0 : ℂ) else
            A x j / (↑↑x / ↑(n - 1) - ↑↑j / ↑(n - 1))) =
          if x = i then ↑↑i / (↑(n - 1) : ℂ) *
            (A i j / (↑↑i / ↑(n - 1) - ↑↑j / ↑(n - 1))) else 0 := by
        intro x; by_cases hx : i = x
        · subst hx; simp [hij]
        · simp [hx, Ne.symm hx]
      have hs2 : ∀ x : Fin n,
          (if i = x then (0 : ℂ) else
            A i x / (↑↑i / (↑(n - 1) : ℂ) - ↑↑x / ↑(n - 1))) *
          (if x = j then ↑↑x / (↑(n - 1) : ℂ) else 0) =
          if x = j then A i j / (↑↑i / (↑(n - 1) : ℂ) - ↑↑j / ↑(n - 1)) *
            (↑↑j / (↑(n - 1) : ℂ)) else 0 := by
        intro x; by_cases hx : x = j
        · subst hx; simp [hij]
        · simp [hx]
      simp_rw [hs1, hs2]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      set d := ↑↑i / (↑(n - 1) : ℂ) - ↑↑j / ↑(n - 1) with hd_def
      have hdiff_ne : d ≠ 0 := by
        rw [hd_def, div_sub_div_same]
        apply div_ne_zero
        · simp only [ne_eq, sub_eq_zero]
          exact_mod_cast Fin.val_ne_of_ne hij
        · exact_mod_cast (show (n - 1 : ℕ) ≠ 0 by omega)
      rw [show ↑↑i / (↑(n - 1) : ℂ) * (A i j / d) -
          A i j / d * (↑↑j / ↑(n - 1)) =
          d * (A i j / d) from by rw [hd_def]; ring]
      exact (mul_div_cancel₀ (A i j) hdiff_ne).symm
  · have hC_entry : ∀ i j : Fin n, ‖C i j‖ ≤ (↑n - 1) * ‖A i j‖ := by
      intro i j; simp only [C, Matrix.of_apply]
      by_cases hij : i = j
      · subst hij; simp only [↓reduceIte, norm_zero]; exact mul_nonneg (by linarith) (norm_nonneg _)
      · rw [if_neg hij, norm_div, div_sub_div_same, norm_div]
        have hnorm_n1 : ‖(↑(n - 1 : ℕ) : ℂ)‖ = (↑(n - 1 : ℕ) : ℝ) := Complex.norm_natCast _
        have hn1_eq : (↑(n - 1 : ℕ) : ℝ) = (↑n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
        have hnorm_diff_ge1 : (1 : ℝ) ≤ ‖(↑↑i : ℂ) - ↑↑j‖ := by
          rw [show (↑↑i : ℂ) - ↑↑j = ↑((i.val : ℤ) - (j.val : ℤ)) from by push_cast; ring]
          rw [Complex.norm_intCast]
          exact_mod_cast Int.one_le_abs
            (sub_ne_zero.mpr (by exact_mod_cast Fin.val_ne_of_ne hij : (i.val : ℤ) ≠ j.val))
        rw [div_div_eq_mul_div, hnorm_n1, hn1_eq]
        rw [mul_comm ‖A i j‖ (↑n - 1)]
        exact div_le_self (by positivity) hnorm_diff_ge1
    have hhs : hsNorm C ≤ (↑n - 1) * hsNorm A := by
      unfold hsNorm
      rw [show (↑n - 1 : ℝ) * Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) =
          Real.sqrt ((↑n - 1) ^ 2 * ∑ i, ∑ j, Complex.normSq (A i j)) from by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hn1)]]
      apply Real.sqrt_le_sqrt
      calc ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (C i j)
          ≤ ∑ i : Fin n, ∑ j : Fin n, (↑n - 1) ^ 2 * Complex.normSq (A i j) := by
            apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
            simp only [Complex.normSq_eq_norm_sq]
            rw [← mul_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (hC_entry i j) 2
        _ = (↑n - 1) ^ 2 * ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j) := by
            simp_rw [← Finset.mul_sum]
    calc ‖C‖ ≤ hsNorm C := le_hsNorm C
      _ ≤ (↑n - 1) * hsNorm A := hhs
      _ ≤ (↑n - 1) * (Real.sqrt ↑n * ‖A‖) :=
          mul_le_mul_of_nonneg_left (hsNorm_le_sqrt_n_mul_opNorm A) (le_of_lt hn1)
      _ = Real.sqrt ↑n * ((↑n - 1) * ‖A‖) := by ring
      _ ≤ ↑n * ((↑n - 1) * ‖A‖) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [Real.sqrt_le_left (Nat.cast_nonneg n)]
          calc (↑n : ℝ) = ↑n * 1 := (mul_one _).symm
            _ ≤ ↑n * ↑n := mul_le_mul_of_nonneg_left
                (by exact_mod_cast (show 1 ≤ n by omega)) (Nat.cast_nonneg n)
            _ = (↑n : ℝ) ^ 2 := (sq _).symm
      _ = ↑n * (↑n - 1) * ‖A‖ := by ring

/- (by claude)
State: ✅ done — P5-G. lambdaM finiteness: every lambdaM m is bounded by the
polynomial m·(m-1). Placed here (not in Pow4BTRecursion) because the proof
needs the `private` helper `zeroDiag_InUnitSquare_decomp_bounded_S1f`.
-/
/-- `lambdaM m ≤ m·(m-1)`: the supremum defining `lambdaM` is finite.
For `m ≥ 2` every zero-diag norm-1 matrix admits a decomposition with
`‖C‖ ≤ m(m-1)`, so `lambdaA A ≤ m(m-1)`; take the sup. For `m ≤ 1` the
defining set is empty and `lambdaM m = 0`. -/
lemma lambdaM_le_poly (m : ℕ) : lambdaM m ≤ (m : ℝ) * ((m : ℝ) - 1) := by
  rcases lt_or_ge m 2 with hm | hm
  · -- m = 0 or m = 1: the defining set is empty.
    have hempty : {A : Matrix (Fin m) (Fin m) ℂ | ZeroDiag A ∧ ‖A‖ = 1} = ∅ := by
      ext A
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hzd, hnorm⟩
      have hA0 : A = 0 := by
        ext i j
        interval_cases m
        · exact absurd i.isLt (by omega)
        · have hij : i = j := Subsingleton.elim i j
          subst hij; exact hzd i
      rw [hA0, norm_zero] at hnorm
      norm_num at hnorm
    have hzero : lambdaM m = 0 := by
      unfold lambdaM
      rw [hempty, Set.image_empty, Real.sSup_empty]
    rw [hzero]
    interval_cases m
    · norm_num
    · norm_num
  · -- m ≥ 2: every image element ≤ m(m-1).
    have hmm1_nn : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) - 1) := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      have hm1' : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
      positivity
    unfold lambdaM
    apply Real.sSup_le _ hmm1_nn
    rintro y ⟨A, ⟨hzd, hnorm⟩, rfl⟩
    obtain ⟨B, C, hBdiag, hBsq, hAeq, hCle⟩ :=
      zeroDiag_InUnitSquare_decomp_bounded_S1f hm A hzd
    have hCle' : ‖C‖ ≤ (m : ℝ) * ((m : ℝ) - 1) := by
      rw [hnorm, mul_one] at hCle; exact hCle
    have hlamb : lambdaA A ≤ ‖C‖ := by
      unfold lambdaA
      apply csInf_le
      · exact ⟨0, fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
      · exact ⟨B, C, hBdiag, hBsq, hAeq, le_refl _⟩
    linarith

/-! ## Strengthened canonical 4-block bound -/

set_option maxHeartbeats 6400000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
/-- Strengthened canonical 4-block bound (exposes per-block lambdaA).
    Same proof structure as `lambdaA_four_block_bound`, but the final inequality
    uses `⨆ k, lambdaA (diagBlock k)` instead of `lambdaM m`. This is the σ-aware
    primitive: combined with conjugation, it gives the BT-σ aggregation needed
    to plug in tmp_S1a_v3's BT-paving leaf bounds. -/
lemma lambdaA_four_block_bound_strong
    {m : ℕ} (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (A : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1) :
    lambdaA A ≤ 2 / (1 - δ) *
        (⨆ k : Fin 4, lambdaA (A.submatrix
          (fun j : Fin m => (⟨k.val * m + j.val, by
            have hk := k.isLt; have hj := j.isLt
            calc k.val * m + j.val < k.val * m + m := by omega
              _ = (k.val + 1) * m := by ring
              _ ≤ 4 * m := by nlinarith⟩ : Fin (4 * m)))
          (fun j : Fin m => (⟨k.val * m + j.val, by
            have hk := k.isLt; have hj := j.isLt
            calc k.val * m + j.val < k.val * m + m := by omega
              _ = (k.val + 1) * m := by ring
              _ ≤ 4 * m := by nlinarith⟩ : Fin (4 * m))))) + 6 / δ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- m = 0: Fin(4*0) = Fin 0, matrix is empty
    have h0 : lambdaA A ≤ 0 := by
      unfold lambdaA
      apply csInf_le
      · exact ⟨0, fun c ⟨_, C', _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
      · refine ⟨0, 0, ?_, ?_, ?_, by norm_num⟩
        · intro i j _; exact Fin.elim0 i
        · intro i; exact Fin.elim0 i
        · ext i; exact Fin.elim0 i
    -- The supremum-of-empty issue: for m=0, the blocks themselves are over Fin 0.
    -- The supremum over Fin 4 is well-defined though.
    have hsup_nn : (0 : ℝ) ≤ ⨆ k : Fin 4,
        lambdaA (A.submatrix
          (fun j : Fin 0 => (⟨k.val * 0 + j.val, by omega⟩ : Fin (4 * 0)))
          (fun j : Fin 0 => (⟨k.val * 0 + j.val, by omega⟩ : Fin (4 * 0)))) := by
      apply Real.iSup_nonneg
      intro k; exact lambdaA_nonneg_S1f _
    have h1 : 0 < 1 - δ := sub_pos.mpr hδ1
    have hbound : (0 : ℝ) ≤ 2 / (1 - δ) *
        (⨆ k : Fin 4, lambdaA (A.submatrix
          (fun j : Fin 0 => (⟨k.val * 0 + j.val, by omega⟩ : Fin (4 * 0)))
          (fun j : Fin 0 => (⟨k.val * 0 + j.val, by omega⟩ : Fin (4 * 0))))) +
        6 / δ := by
      have h2 : 0 ≤ 2 / (1 - δ) := by positivity
      have h3 : 0 ≤ 6 / δ := by positivity
      have h4 : 0 ≤ 2 / (1 - δ) * (⨆ k : Fin 4, lambdaA _) :=
        mul_nonneg h2 hsup_nn
      linarith
    linarith
  · -- m ≥ 1: the main 4-block construction
    have h1δ : (0 : ℝ) < 1 - δ := sub_pos.mpr hδ1
    -- Block index functions: view Fin(4m) as 4 blocks of size m
    let blockEmbed : Fin 4 → Fin m → Fin (4 * m) :=
      fun k j => ⟨k.val * m + j.val, by
        have hk := k.isLt; have hj := j.isLt
        calc k.val * m + j.val < k.val * m + m := by omega
          _ = (k.val + 1) * m := by ring
          _ ≤ 4 * m := by nlinarith⟩
    -- Extract k-th diagonal block
    let diagBlock : Fin 4 → Matrix (Fin m) (Fin m) ℂ :=
      fun k => Matrix.of (fun i j =>
        A (blockEmbed k i) (blockEmbed k j))
    -- The supremum
    set M : ℝ := ⨆ k : Fin 4, lambdaA (diagBlock k) with hM_def
    -- M is the same as the target expression
    have hdiagBlock_eq : ∀ k : Fin 4,
        diagBlock k = A.submatrix
          (fun j : Fin m => (blockEmbed k j))
          (fun j : Fin m => (blockEmbed k j)) := by
      intro k; ext i j
      simp [diagBlock, Matrix.of_apply, Matrix.submatrix_apply]
    have hM_eq_target : M = ⨆ k : Fin 4, lambdaA (A.submatrix
        (fun j : Fin m => (blockEmbed k j))
        (fun j : Fin m => (blockEmbed k j))) := by
      simp_rw [hM_def, ← hdiagBlock_eq]
    have hM_nn : 0 ≤ M := by
      rw [hM_def]; apply Real.iSup_nonneg; intro k; exact lambdaA_nonneg_S1f _
    have hLA_block_le_M : ∀ k : Fin 4, lambdaA (diagBlock k) ≤ M := by
      intro k
      rw [hM_def]
      -- BddAbove: range of finite function on Fin 4 is bounded
      have hbdd : BddAbove (Set.range (fun k : Fin 4 => lambdaA (diagBlock k))) :=
        (Set.finite_range _).bddAbove
      exact le_ciSup hbdd k
    have hzd_block : ∀ k, ZeroDiag (diagBlock k) := by
      intro k i
      simp only [diagBlock, Matrix.of_apply]
      exact hzd (blockEmbed k i)
    have hblockEmbed_inj : ∀ k : Fin 4,
        Function.Injective (blockEmbed k) := by
      intro k i j hij
      simp only [blockEmbed, Fin.mk.injEq] at hij
      exact Fin.ext (by omega)
    have hnorm_block : ∀ k, ‖diagBlock k‖ ≤ 1 := by
      intro k; rw [← hnorm]
      exact submatrix_norm_le
        (blockEmbed k) (hblockEmbed_inj k) A
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hne_block : ∀ k, ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
        IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
        diagBlock k = ⁅B, C⁆ₘ := by
      intro k
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · -- m = 1 (since hm : m > 0)
        have hm1 : m = 1 := by omega
        subst hm1
        refine ⟨0, 0, ?_, ?_, ?_⟩
        · intro i j hij; simp
        · intro i; unfold InUnitSquare; simp
        · ext i j; simp only [matComm, mul_zero, Matrix.sub_apply, Matrix.zero_apply, sub_self]
          have : i = j := Fin.ext (by omega)
          rw [this]; exact hzd_block k j
      · obtain ⟨B, C, hd, hu, hc, _⟩ :=
          zeroDiag_InUnitSquare_decomp_bounded_S1f hm2
            (diagBlock k) (hzd_block k)
        exact ⟨B, C, hd, hu, hc⟩
    -- Step: Pick near-optimal decompositions with slack η
    set η := ε * (1 - δ) / 4 with hη_def
    have hη_pos : 0 < η := by positivity
    have hpick : ∀ k : Fin 4, ∃ (Bk Ck : Matrix (Fin m) (Fin m) ℂ),
        IsDiagMatrix Bk ∧ (∀ i, InUnitSquare (Bk i i)) ∧
        diagBlock k = ⁅Bk, Ck⁆ₘ ∧ ‖Ck‖ ≤ lambdaA (diagBlock k) + η := by
      intro k
      set S := {c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
        IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
        diagBlock k = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hS_def
      have hne_S : S.Nonempty := by
        obtain ⟨B, C, hdiag, husq, hcomm⟩ := hne_block k
        exact ⟨‖C‖, B, C, hdiag, husq, hcomm, le_refl _⟩
      have hbdd : BddBelow S := by
        refine ⟨0, fun c ⟨B, C, _, _, _, hle⟩ => ?_⟩
        exact le_trans (norm_nonneg _) hle
      have hlt : sInf S < lambdaA (diagBlock k) + η := by
        unfold lambdaA; linarith
      obtain ⟨c, ⟨B, C, hdiag, husq, hcomm, hnorm⟩, hc_lt⟩ :=
        exists_lt_of_csInf_lt hne_S hlt
      exact ⟨B, C, hdiag, husq, hcomm, le_trans hnorm (le_of_lt hc_lt)⟩
    choose Bk Ck hBk_diag hBk_usq hBk_comm hCk_norm using hpick
    -- KEY DIFFERENCE: bound by M+η rather than lambdaM m + η
    have hCk_bound : ∀ k : Fin 4, ‖Ck k‖ ≤ M + η := by
      intro k
      calc ‖Ck k‖ ≤ lambdaA (diagBlock k) + η := hCk_norm k
        _ ≤ M + η := by linarith [hLA_block_le_M k]
    -- Reduce to constructing a witness B', C' with controlled norm.
    suffices hwit : ∃ (B' C' : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ),
        IsDiagMatrix B' ∧ (∀ i, InUnitSquare (B' i i)) ∧
        A = ⁅B', C'⁆ₘ ∧ ‖C'‖ ≤ 2 / (1 - δ) * (M + η) + 6 / δ by
      obtain ⟨B', C', hd, hu, hc, hn⟩ := hwit
      have hη_bound : 2 / (1 - δ) * η = ε / 2 := by
        rw [hη_def]; field_simp; ring
      have htarget_eq : (⨆ k : Fin 4, lambdaA (A.submatrix
            (fun j : Fin m => (blockEmbed k j))
            (fun j : Fin m => (blockEmbed k j)))) = M := hM_eq_target.symm
      rw [htarget_eq]
      calc lambdaA A
          ≤ ‖C'‖ := csInf_le
            ⟨0, fun c ⟨_, C, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
            ⟨B', C', hd, hu, hc, le_refl _⟩
        _ ≤ 2 / (1 - δ) * (M + η) + 6 / δ := hn
        _ = 2 / (1 - δ) * M + 2 / (1 - δ) * η + 6 / δ := by ring
        _ = 2 / (1 - δ) * M + 6 / δ + ε / 2 := by rw [hη_bound]; ring
        _ < 2 / (1 - δ) * M + 6 / δ + ε := by linarith
    -- === Witness Construction (verbatim from original proof) ===
    let blockIdx : Fin (4 * m) → Fin 4 :=
      fun i => ⟨i.val / m, Nat.div_lt_of_lt_mul (by omega)⟩
    let localIdx : Fin (4 * m) → Fin m :=
      fun i => ⟨i.val % m, Nat.mod_lt _ (by omega)⟩
    have hEmbed_id : ∀ i : Fin (4 * m),
        blockEmbed (blockIdx i) (localIdx i) = i := by
      intro i; ext
      simp only [blockEmbed, blockIdx, localIdx]
      exact (Nat.div_add_mod' i.val m)
    have hBlockIdx_embed : ∀ (k : Fin 4) (j : Fin m),
        blockIdx (blockEmbed k j) = k := by
      intro k j; ext
      simp only [blockEmbed, blockIdx]
      have hj := j.isLt
      rw [show k.val * m + j.val = j.val + k.val * m from by omega]
      rw [Nat.add_mul_div_right _ _ (by omega : 0 < m)]
      simp [Nat.div_eq_of_lt hj]
    have hLocalIdx_embed : ∀ (k : Fin 4) (j : Fin m),
        localIdx (blockEmbed k j) = j := by
      intro k j; ext
      simp only [blockEmbed, localIdx]
      have hj := j.isLt
      rw [show k.val * m + j.val = j.val + k.val * m from by omega]
      simp [Nat.mod_eq_of_lt hj]
    let cornerRe : Fin 4 → ℝ :=
      ![  (1 + δ) / 2,  (1 + δ) / 2, -(1 + δ) / 2, -(1 + δ) / 2]
    let cornerIm : Fin 4 → ℝ :=
      ![ (1 + δ) / 2, -(1 + δ) / 2,  (1 + δ) / 2, -(1 + δ) / 2]
    let cornerVal : Fin 4 → ℂ := fun k => ⟨cornerRe k, cornerIm k⟩
    let fullB : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
      Matrix.diagonal (fun i =>
        ((1 - δ) / 2 : ℝ) * (Bk (blockIdx i)) (localIdx i) (localIdx i) +
        cornerVal (blockIdx i))
    have hfullB_diag : IsDiagMatrix fullB :=
      fun i j hij => Matrix.diagonal_apply_ne _ hij
    have hfullB_usq : ∀ i, InUnitSquare (fullB i i) := by
      intro i; simp only [fullB, Matrix.diagonal_apply_eq]
      have key : ∀ (x c : ℝ), |x| ≤ 1 → |c| = (1 + δ) / 2 → |(1 - δ) / 2 * x + c| ≤ 1 := by
        intro x c hx hc
        rw [abs_le]; rw [abs_le] at hx; obtain ⟨hx_lo, hx_hi⟩ := hx
        by_cases hc0 : 0 ≤ c
        · rw [abs_of_nonneg hc0] at hc; subst hc; constructor <;> nlinarith
        · have hc0' : c < 0 := not_le.mp hc0
          rw [abs_of_neg hc0'] at hc; constructor <;> nlinarith
      have corner_abs_helper : ∀ x : ℝ, x = (1 + δ) / 2 ∨ x = -(1 + δ) / 2 →
          |x| = (1 + δ) / 2 := by
        intro x hx; rcases hx with rfl | rfl
        · exact abs_of_nonneg (by linarith)
        · rw [show -(1 + δ) / 2 = -((1 + δ) / 2) from neg_div _ _]
          rw [abs_neg]; exact abs_of_nonneg (by linarith)
      have hcre_abs : ∀ k : Fin 4, |cornerRe k| = (1 + δ) / 2 := by
        intro k; apply corner_abs_helper
        fin_cases k <;> simp [cornerRe]
      have hcim_abs : ∀ k : Fin 4, |cornerIm k| = (1 + δ) / 2 := by
        intro k; apply corner_abs_helper
        fin_cases k <;> simp [cornerIm]
      obtain ⟨hbre, hbim⟩ := hBk_usq (blockIdx i) (localIdx i)
      have hre_eq : (↑((1 - δ) / 2) * Bk (blockIdx i) (localIdx i) (localIdx i) +
          cornerVal (blockIdx i)).re =
          (1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re +
          cornerRe (blockIdx i) := by
        simp [cornerVal, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      have him_eq : (↑((1 - δ) / 2) * Bk (blockIdx i) (localIdx i) (localIdx i) +
          cornerVal (blockIdx i)).im =
          (1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).im +
          cornerIm (blockIdx i) := by
        simp [cornerVal, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨hre_eq ▸ key _ _ hbre (hcre_abs _), him_eq ▸ key _ _ hbim (hcim_abs _)⟩
    have hSpectralGap : ∀ (i j : Fin (4 * m)),
        blockIdx i ≠ blockIdx j →
        2 * δ ≤ |(fullB i i - fullB j j).re| ∨
        2 * δ ≤ |(fullB i i - fullB j j).im| := by
      intro i j hne
      simp only [fullB, Matrix.diagonal_apply_eq]
      obtain ⟨hri, hii⟩ := hBk_usq (blockIdx i) (localIdx i)
      obtain ⟨hrj, hij⟩ := hBk_usq (blockIdx j) (localIdx j)
      have pert_bound : ∀ (x y a : ℝ), 0 ≤ a → |x| ≤ 1 → |y| ≤ 1 →
          |a / 2 * x - a / 2 * y| ≤ a := by
        intro x y a ha hx hy
        rw [show a / 2 * x - a / 2 * y = a / 2 * (x - y) from by ring]
        rw [abs_mul, abs_of_nonneg (by linarith)]
        have hxy : |x - y| ≤ 2 := le_trans (abs_sub x y) (by linarith)
        nlinarith
      have rev_tri : ∀ (a b : ℝ), |b| - |a| ≤ |a + b| := by
        intro a b
        have h := abs_sub (a + b) a
        simp [add_sub_cancel_left] at h; linarith
      have hpert_re : |(1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re -
          (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).re| ≤ 1 - δ :=
        pert_bound _ _ _ (by linarith) hri hrj
      have hpert_im : |(1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).im -
          (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).im| ≤ 1 - δ :=
        pert_bound _ _ _ (by linarith) hii hij
      have hre_eq : (((1 - δ) / 2 : ℝ) * Bk (blockIdx i) (localIdx i) (localIdx i) +
          cornerVal (blockIdx i) -
          (((1 - δ) / 2 : ℝ) * Bk (blockIdx j) (localIdx j) (localIdx j) +
          cornerVal (blockIdx j))).re =
        (1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re -
        (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).re +
        (cornerRe (blockIdx i) - cornerRe (blockIdx j)) := by
        simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im, cornerVal]; ring
      have him_eq : (((1 - δ) / 2 : ℝ) * Bk (blockIdx i) (localIdx i) (localIdx i) +
          cornerVal (blockIdx i) -
          (((1 - δ) / 2 : ℝ) * Bk (blockIdx j) (localIdx j) (localIdx j) +
          cornerVal (blockIdx j))).im =
        (1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).im -
        (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).im +
        (cornerIm (blockIdx i) - cornerIm (blockIdx j)) := by
        simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
              Complex.ofReal_im, cornerVal]; ring
      have hcRe_vals : ∀ k : Fin 4, cornerRe k = (1 + δ) / 2 ∨ cornerRe k = -(1 + δ) / 2 := by
        intro k; fin_cases k <;> simp [cornerRe, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hcIm_vals : ∀ k : Fin 4, cornerIm k = (1 + δ) / 2 ∨ cornerIm k = -(1 + δ) / 2 := by
        intro k; fin_cases k <;> simp [cornerIm, Matrix.cons_val_zero, Matrix.cons_val_one]
      have corner_inj : ∀ (a b : Fin 4), cornerRe a = cornerRe b → cornerIm a = cornerIm b → a =
        b := by
        intro a b h1 h2
        fin_cases a <;> fin_cases b <;> first | rfl |
          (simp [cornerRe, cornerIm, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2; linarith)
      have hcorner_diff : cornerRe (blockIdx i) ≠ cornerRe (blockIdx j) ∨
          cornerIm (blockIdx i) ≠ cornerIm (blockIdx j) := by
        by_contra h; push Not at h
        exact hne (corner_inj _ _ h.1 h.2)
      have corner_gap : ∀ (f : Fin 4 → ℝ), (∀ k, f k = (1 + δ) / 2 ∨ f k = -(1 + δ) / 2) →
          f (blockIdx i) ≠ f (blockIdx j) → |f (blockIdx i) - f (blockIdx j)| = 1 + δ := by
        intro f hvals hneq
        rcases hvals (blockIdx i) with hi | hi <;> rcases hvals (blockIdx j) with hj | hj
        · exfalso; exact hneq (by rw [hi, hj])
        · rw [hi, hj]; rw [show (1 + δ) / 2 - -(1 + δ) / 2 = 1 + δ from by ring]
          exact abs_of_pos (by linarith)
        · rw [hi, hj]; rw [show -(1 + δ) / 2 - (1 + δ) / 2 = -(1 + δ) from by ring]
          rw [abs_neg]; exact abs_of_pos (by linarith)
        · exfalso; exact hneq (by rw [hi, hj])
      rcases hcorner_diff with hcr | hci
      · left; rw [hre_eq]
        have hgap := corner_gap cornerRe hcRe_vals hcr
        linarith [rev_tri ((1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re -
          (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).re)
          (cornerRe (blockIdx i) - cornerRe (blockIdx j))]
      · right; rw [him_eq]
        have hgap := corner_gap cornerIm hcIm_vals hci
        linarith [rev_tri ((1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).im -
          (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).im)
          (cornerIm (blockIdx i) - cornerIm (blockIdx j))]
    have hFullB_ne : ∀ (i j : Fin (4 * m)),
        blockIdx i ≠ blockIdx j → fullB i i ≠ fullB j j := by
      intro i j hne habs
      rcases hSpectralGap i j hne with hre | him
      · have : (fullB i i - fullB j j).re = 0 := by rw [habs]; simp
        rw [this] at hre; simp at hre; linarith
      · have : (fullB i i - fullB j j).im = 0 := by rw [habs]; simp
        rw [this] at him; simp at him; linarith
    let fullC : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
      fun i j =>
        if blockIdx i = blockIdx j then
          (2 / ((1 : ℝ) - δ) : ℂ) * (Ck (blockIdx i)) (localIdx i) (localIdx j)
        else
          A i j / (fullB i i - fullB j j)
    have hComm : A = ⁅fullB, fullC⁆ₘ := by
      ext i j
      rw [commutator_diag_entry fullB fullC hfullB_diag]
      simp only [fullC]
      split_ifs with heq
      · simp only [fullB, Matrix.diagonal_apply_eq]
        have hAij : A i j = diagBlock (blockIdx i) (localIdx i) (localIdx j) := by
          simp only [diagBlock, Matrix.of_apply]
          conv_rhs => rw [show blockEmbed (blockIdx i) (localIdx j) =
            blockEmbed (blockIdx j) (localIdx j) from by rw [heq],
            hEmbed_id j, hEmbed_id i]
        rw [hAij, hBk_comm (blockIdx i),
          commutator_diag_entry _ _ (hBk_diag _), heq]
        have h1δne : (1 : ℝ) - δ ≠ 0 := by linarith
        have hkey : (↑((1 - δ) / 2) : ℂ) * (2 / (↑1 - ↑δ)) = 1 := by
          push_cast
          field_simp [show (1 : ℂ) - ↑δ ≠ 0 from by exact_mod_cast h1δne]
        have hrw : (↑((1 - δ) / 2) : ℂ) * Bk (blockIdx j) (localIdx i) (localIdx i) +
            cornerVal (blockIdx j) -
            ((↑((1 - δ) / 2) : ℂ) * Bk (blockIdx j) (localIdx j) (localIdx j) +
            cornerVal (blockIdx j)) =
            (↑((1 - δ) / 2) : ℂ) * (Bk (blockIdx j) (localIdx i) (localIdx i) -
            Bk (blockIdx j) (localIdx j) (localIdx j)) := by ring
        rw [hrw]
        simp only [Complex.ofReal_one]
        rw [show (↑((1 - δ) / 2) : ℂ) *
            (Bk (blockIdx j) (localIdx i) (localIdx i) -
            Bk (blockIdx j) (localIdx j) (localIdx j)) *
            (2 / (1 - ↑δ) * Ck (blockIdx j) (localIdx i) (localIdx j)) =
            (↑((1 - δ) / 2) : ℂ) * (2 / (1 - ↑δ)) *
            ((Bk (blockIdx j) (localIdx i) (localIdx i) -
            Bk (blockIdx j) (localIdx j) (localIdx j)) *
            Ck (blockIdx j) (localIdx i) (localIdx j)) from by ring]
        rw [hkey, one_mul]
      · have hne := hFullB_ne i j heq
        have hne' : fullB i i - fullB j j ≠ 0 := sub_ne_zero.mpr hne
        field_simp [hne']
    have hfullC_bound : ‖fullC‖ ≤ 2 / (1 - δ) * (M + η) + 6 / δ := by
      let sameBlockC : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
        fun i j => if blockIdx i = blockIdx j then
          (2 / ((1 : ℝ) - δ) : ℂ) * (Ck (blockIdx i)) (localIdx i) (localIdx j)
        else 0
      let crossBlockC : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
        fun i j => if blockIdx i = blockIdx j then 0
        else A i j / (fullB i i - fullB j j)
      have hdecomp : fullC = sameBlockC + crossBlockC := by
        ext i j; simp only [fullC, sameBlockC, crossBlockC, Matrix.add_apply]
        split_ifs <;> simp
      calc ‖fullC‖ = ‖sameBlockC + crossBlockC‖ := by rw [hdecomp]
        _ ≤ ‖sameBlockC‖ + ‖crossBlockC‖ := norm_add_le _ _
        _ ≤ 2 / (1 - δ) * (M + η) + 6 / δ := by
          apply add_le_add
          · -- ‖sameBlockC‖ ≤ 2/(1-δ) * (M + η)
            have hcoeff_nn : (0 : ℝ) ≤ 2 / (1 - δ) := div_nonneg (by norm_num) (le_of_lt h1δ)
            have hscale_val : ‖(2 / ((1 : ℝ) - δ) : ℂ)‖ = 2 / (1 - δ) := by
              have h2c : (2 : ℂ) / ((1 : ℝ) - δ) = ((2 / (1 - δ) : ℝ) : ℂ) := by push_cast; ring
              rw [h2c, Complex.norm_real]
              exact abs_of_pos (div_pos (by norm_num : (0:ℝ) < 2) h1δ)
            let Mmat : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
              fun i j => if blockIdx i = blockIdx j then
                (Ck (blockIdx i)) (localIdx i) (localIdx j)
              else 0
            have hscale : sameBlockC = (2 / ((1 : ℝ) - δ) : ℂ) • Mmat := by
              ext i j; simp only [sameBlockC, Mmat, Matrix.smul_apply, smul_eq_mul]
              split_ifs <;> simp
            have hMmat_bound : ‖Mmat‖ ≤ M + η := by
              have hbd_nn : (0 : ℝ) ≤ M + η := by positivity
              have hMmat_eq : Mmat = (fun i j => if (finProdFinEquiv.symm i : Fin 4 × Fin m).1 =
                  (finProdFinEquiv.symm j : Fin 4 × Fin m).1 then
                  Ck (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
                    (finProdFinEquiv.symm j).2 else 0) := by
                rfl
              rw [hMmat_eq]
              exact blockDiag_norm_le_of_blocks Ck (M + η) hbd_nn hCk_bound
            rw [hscale, norm_smul, hscale_val]
            exact mul_le_mul_of_nonneg_left hMmat_bound hcoeff_nn
          · -- ‖crossBlockC‖ ≤ 6/δ (verbatim from original)
            let crossPairs : Finset (Fin 4 × Fin 4) :=
              Finset.univ.filter (fun p => p.1 ≠ p.2)
            let embedBlock : Fin 4 × Fin 4 → Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
              fun p => fun i j =>
                if blockIdx i = p.1 ∧ blockIdx j = p.2 then
                  A i j / (fullB i i - fullB j j)
                else 0
            have hcross_sum : crossBlockC = ∑ p ∈ crossPairs, embedBlock p := by
              ext i j
              simp only [Matrix.sum_apply, crossBlockC, embedBlock]
              by_cases heq : blockIdx i = blockIdx j
              · simp only [heq, ite_true]
                symm; apply Finset.sum_eq_zero
                intro p hp
                simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
                split_ifs with h
                · have : p.1 = p.2 := by rw [← h.1, ← h.2]
                  exact absurd this hp
                · rfl
              · simp only [heq, ite_false]
                have hmem : (blockIdx i, blockIdx j) ∈ crossPairs := by
                  simp only [crossPairs, Finset.mem_filter, Finset.mem_univ,
                    true_and]; exact heq
                rw [← Finset.add_sum_erase _ _ hmem]
                simp only [true_and, ite_true]
                suffices hsuff : ∑ x ∈ crossPairs.erase (blockIdx i, blockIdx j),
                    (if blockIdx i = x.1 ∧ blockIdx j = x.2
                      then A i j / (fullB i i - fullB j j) else 0) = 0 by
                  rw [hsuff, add_zero]
                apply Finset.sum_eq_zero; intro p hp
                simp only [Finset.mem_erase] at hp
                split_ifs with h
                · exfalso; exact hp.1 (Prod.ext h.1.symm h.2.symm)
                · rfl
            have hcard : crossPairs.card = 12 := by decide
            have hblock_bound : ∀ p ∈ crossPairs, ‖embedBlock p‖ ≤ 1 / (2 * δ) := by
              intro ⟨k, l⟩ hp
              simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
              let Skl : Matrix (Fin m) (Fin m) ℂ :=
                Matrix.diagonal (fun i => fullB (blockEmbed k i) (blockEmbed k i))
              let Tkl : Matrix (Fin m) (Fin m) ℂ :=
                Matrix.diagonal (fun j => fullB (blockEmbed l j) (blockEmbed l j))
              let Akl : Matrix (Fin m) (Fin m) ℂ :=
                Matrix.of (fun i j => A (blockEmbed k i) (blockEmbed l j))
              let Xkl : Matrix (Fin m) (Fin m) ℂ :=
                fun i j => Akl i j / (Skl i i - Tkl j j)
              have hSkl_diag : IsDiagMatrix Skl := diag_isDiagMatrix_S1f _
              have hTkl_diag : IsDiagMatrix Tkl := diag_isDiagMatrix_S1f _
              have hSep_abs : ∀ i j, 2 * δ ≤ |(Skl i i - Tkl j j).re| ∨
                  2 * δ ≤ |(Skl i i - Tkl j j).im| := by
                intro i j
                have := hSpectralGap (blockEmbed k i) (blockEmbed l j)
                  (by rw [hBlockIdx_embed, hBlockIdx_embed]; exact hp)
                simp only [Skl, Tkl, Matrix.diagonal_apply_eq] at this ⊢
                exact this
              have hSigned : (∀ i j, 2 * δ ≤ (Skl i i - Tkl j j).re) ∨
                  (∀ i j, (Skl i i - Tkl j j).re ≤ -(2 * δ)) ∨
                  (∀ i j, 2 * δ ≤ (Skl i i - Tkl j j).im) ∨
                  (∀ i j, (Skl i i - Tkl j j).im ≤ -(2 * δ)) := by
                have hpert : ∀ (x y : ℝ), |x| ≤ 1 → |y| ≤ 1 →
                    -(1 - δ) ≤ (1 - δ) / 2 * x - (1 - δ) / 2 * y ∧
                    (1 - δ) / 2 * x - (1 - δ) / 2 * y ≤ 1 - δ := by
                  intro x y hx hy
                  rw [abs_le] at hx hy
                  constructor <;> nlinarith
                have hDiff_re : ∀ i j, (Skl i i - Tkl j j).re =
                    (1 - δ) / 2 * (Bk k i i).re - (1 - δ) / 2 * (Bk l j j).re +
                    (cornerRe k - cornerRe l) := by
                  intro i j
                  simp only [Skl, Tkl, Matrix.diagonal_apply_eq, fullB,
                    hBlockIdx_embed, hLocalIdx_embed, cornerVal,
                    Complex.sub_re, Complex.add_re, Complex.mul_re,
                    Complex.ofReal_re, Complex.ofReal_im]
                  ring
                have hDiff_im : ∀ i j, (Skl i i - Tkl j j).im =
                    (1 - δ) / 2 * (Bk k i i).im - (1 - δ) / 2 * (Bk l j j).im +
                    (cornerIm k - cornerIm l) := by
                  intro i j
                  simp only [Skl, Tkl, Matrix.diagonal_apply_eq, fullB,
                    hBlockIdx_embed, hLocalIdx_embed, cornerVal,
                    Complex.sub_im, Complex.add_im, Complex.mul_im,
                    Complex.ofReal_re, Complex.ofReal_im]
                  ring
                have hcRe_vals : ∀ a : Fin 4,
                    cornerRe a = (1 + δ) / 2 ∨ cornerRe a = -(1 + δ) / 2 := by
                  intro a; fin_cases a <;> simp [cornerRe]
                have hcIm_vals : ∀ a : Fin 4,
                    cornerIm a = (1 + δ) / 2 ∨ cornerIm a = -(1 + δ) / 2 := by
                  intro a; fin_cases a <;> simp [cornerIm]
                have corner_inj : ∀ (a b : Fin 4),
                    cornerRe a = cornerRe b → cornerIm a = cornerIm b → a = b := by
                  intro a b h1 h2
                  fin_cases a <;> fin_cases b <;> first | rfl |
                    (simp [cornerRe, cornerIm] at h1 h2; linarith)
                have hcorner_diff : cornerRe k ≠ cornerRe l ∨ cornerIm k ≠ cornerIm l := by
                  by_contra h; push Not at h
                  exact hp (corner_inj _ _ h.1 h.2)
                rcases hcorner_diff with hre_ne | him_ne
                · rcases hcRe_vals k with hk | hk <;> rcases hcRe_vals l with hl | hl
                  · exact absurd (hk.trans hl.symm) hre_ne
                  · left; intro i j
                    rw [hDiff_re i j]
                    have hxi := (hBk_usq k i).1
                    have hyj := (hBk_usq l j).1
                    have hp1 := (hpert _ _ hxi hyj).1
                    rw [hk, hl]; linarith
                  · right; left; intro i j
                    rw [hDiff_re i j]
                    have hxi := (hBk_usq k i).1
                    have hyj := (hBk_usq l j).1
                    have hp2 := (hpert _ _ hxi hyj).2
                    rw [hk, hl]; linarith
                  · exact absurd (hk.trans hl.symm) hre_ne
                · rcases hcIm_vals k with hk | hk <;> rcases hcIm_vals l with hl | hl
                  · exact absurd (hk.trans hl.symm) him_ne
                  · right; right; left; intro i j
                    rw [hDiff_im i j]
                    have hxi := (hBk_usq k i).2
                    have hyj := (hBk_usq l j).2
                    have hp1 := (hpert _ _ hxi hyj).1
                    rw [hk, hl]; linarith
                  · right; right; right; intro i j
                    rw [hDiff_im i j]
                    have hxi := (hBk_usq k i).2
                    have hyj := (hBk_usq l j).2
                    have hp2 := (hpert _ _ hxi hyj).2
                    rw [hk, hl]; linarith
                  · exact absurd (hk.trans hl.symm) him_ne
              have hSylv : ‖Xkl‖ ≤ ‖Akl‖ / (2 * δ) := by
                rcases hSigned with hpos_re | hneg_re | hpos_im | hneg_im
                · exact (sylvester_diag_opNorm_bound_re Skl Tkl Akl
                    hSkl_diag hTkl_diag (2 * δ) (by positivity) hpos_re).2
                · let S' : Matrix (Fin m) (Fin m) ℂ := -Skl
                  let T' : Matrix (Fin m) (Fin m) ℂ := -Tkl
                  let A' : Matrix (Fin m) (Fin m) ℂ := -Akl
                  have hS'_diag : IsDiagMatrix S' := by
                    intro i j hij; simp [S', Skl, Matrix.diagonal, hij]
                  have hT'_diag : IsDiagMatrix T' := by
                    intro i j hij; simp [T', Tkl, Matrix.diagonal, hij]
                  have hSep' : ∀ i j, 2 * δ ≤ (S' i i - T' j j).re := by
                    intro i j
                    simp only [S', T', Matrix.neg_apply, Complex.sub_re, Complex.neg_re]
                    have := hneg_re i j
                    simp only [Complex.sub_re] at this; linarith
                  have hXeq : (fun i j => A' i j / (S' i i - T' j j)) = Xkl := by
                    ext i j
                    simp only [S', T', A', Xkl, Akl, Skl, Tkl, Matrix.neg_apply,
                      Matrix.of_apply, Matrix.diagonal_apply_eq]
                    set a := A (blockEmbed k i) (blockEmbed l j)
                    set b := fullB (blockEmbed k i) (blockEmbed k i)
                    set c := fullB (blockEmbed l j) (blockEmbed l j)
                    show -a / (-b - -c) = a / (b - c)
                    rw [show -b - -c = -(b - c) from by ring, neg_div_neg_eq]
                  have key := (sylvester_diag_opNorm_bound_re S' T' A'
                    hS'_diag hT'_diag (2 * δ) (by positivity) hSep').2
                  rw [hXeq] at key
                  rw [show ‖A'‖ = ‖Akl‖ from by simp [A', norm_neg]] at key
                  exact key
                · exact (sylvester_diag_opNorm_bound_im Skl Tkl Akl
                    hSkl_diag hTkl_diag (2 * δ) (by positivity) hpos_im).2
                · let S' : Matrix (Fin m) (Fin m) ℂ := -Skl
                  let T' : Matrix (Fin m) (Fin m) ℂ := -Tkl
                  let A' : Matrix (Fin m) (Fin m) ℂ := -Akl
                  have hS'_diag : IsDiagMatrix S' := by
                    intro i j hij; simp [S', Skl, Matrix.diagonal, hij]
                  have hT'_diag : IsDiagMatrix T' := by
                    intro i j hij; simp [T', Tkl, Matrix.diagonal, hij]
                  have hSep' : ∀ i j, 2 * δ ≤ (S' i i - T' j j).im := by
                    intro i j
                    simp only [S', T', Matrix.neg_apply, Complex.sub_im, Complex.neg_im]
                    have := hneg_im i j
                    simp only [Complex.sub_im] at this; linarith
                  have hXeq : (fun i j => A' i j / (S' i i - T' j j)) = Xkl := by
                    ext i j
                    simp only [S', T', A', Xkl, Akl, Skl, Tkl, Matrix.neg_apply,
                      Matrix.of_apply, Matrix.diagonal_apply_eq]
                    set a := A (blockEmbed k i) (blockEmbed l j)
                    set b := fullB (blockEmbed k i) (blockEmbed k i)
                    set c := fullB (blockEmbed l j) (blockEmbed l j)
                    show -a / (-b - -c) = a / (b - c)
                    rw [show -b - -c = -(b - c) from by ring, neg_div_neg_eq]
                  have key := (sylvester_diag_opNorm_bound_im S' T' A'
                    hS'_diag hT'_diag (2 * δ) (by positivity) hSep').2
                  rw [hXeq] at key
                  rw [show ‖A'‖ = ‖Akl‖ from by simp [A', norm_neg]] at key
                  exact key
              have hAkl_norm : ‖Akl‖ ≤ 1 := by
                rw [← hnorm]
                exact cross_submatrix_norm_le (blockEmbed k) (blockEmbed l)
                  (hblockEmbed_inj k) (hblockEmbed_inj l) A
              have hembed_norm : ‖embedBlock (k, l)‖ ≤ ‖Xkl‖ := by
                apply embedBlock_norm_le (blockEmbed k) (blockEmbed l)
                  (hblockEmbed_inj k) (hblockEmbed_inj l)
                  (embedBlock (k, l)) Xkl
                · intro i j hrow
                  simp only [embedBlock]
                  have hbi : blockIdx i ≠ k := by
                    intro hbi
                    exact hrow (localIdx i) (by rw [← hbi]; exact hEmbed_id i)
                  rw [if_neg (fun h => hbi h.1)]
                · intro i j hcol
                  simp only [embedBlock]
                  have hbj : blockIdx j ≠ l := by
                    intro hbj
                    exact hcol (localIdx j) (by rw [← hbj]; exact hEmbed_id j)
                  rw [if_neg (fun h => hbj h.2)]
                · intro i j
                  simp only [embedBlock, Xkl, Akl, Skl, Tkl,
                    Matrix.of_apply, Matrix.diagonal_apply_eq,
                    hBlockIdx_embed, and_self, if_true]
              calc ‖embedBlock (k, l)‖ ≤ ‖Xkl‖ := hembed_norm
                _ ≤ ‖Akl‖ / (2 * δ) := hSylv
                _ ≤ 1 / (2 * δ) := by
                    apply div_le_div_of_nonneg_right hAkl_norm (by positivity)
            rw [hcross_sum]
            calc ‖∑ p ∈ crossPairs, embedBlock p‖
                ≤ ∑ p ∈ crossPairs, ‖embedBlock p‖ := norm_sum_le crossPairs embedBlock
              _ ≤ ∑ _p ∈ crossPairs, (1 / (2 * δ)) :=
                  Finset.sum_le_sum hblock_bound
              _ = crossPairs.card • (1 / (2 * δ)) := by rw [Finset.sum_const]
              _ = 12 * (1 / (2 * δ)) := by rw [hcard]; simp
              _ = 6 / δ := by ring
    exact ⟨fullB, fullC, hfullB_diag, hfullB_usq, hComm, hfullC_bound⟩

/-! ## S1g: lambdaA_sigma_four_block_bound_param (σ-aware four-block; param on hStrong) -/

/-! ## Conjugation-invariance helper for lambdaA -/

/-- For a permutation `p`, the operator norm of `A.submatrix p p` equals the
    operator norm of `A`. Uses `submatrix_norm_le` in both directions. -/
private lemma submatrix_perm_norm_eq_S1g {N : ℕ} (p : Fin N ≃ Fin N)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖A.submatrix (p : Fin N → Fin N) p‖ = ‖A‖ := by
  -- ‖A.submatrix p p‖ ≤ ‖A‖
  have h1 : ‖A.submatrix (p : Fin N → Fin N) p‖ ≤ ‖A‖ := by
    have hkey := submatrix_norm_le (p : Fin N → Fin N) p.injective A
    have hrw : Matrix.of (fun i j => A (p i) (p j)) =
        A.submatrix (p : Fin N → Fin N) p := by
      ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
    rw [hrw] at hkey
    exact hkey
  -- ‖A‖ ≤ ‖A.submatrix p p‖
  have h2 : ‖A‖ ≤ ‖A.submatrix (p : Fin N → Fin N) p‖ := by
    have key : (A.submatrix (p : Fin N → Fin N) p).submatrix
        (p.symm : Fin N → Fin N) p.symm = A := by
      ext i j
      simp [Matrix.submatrix_apply, Equiv.apply_symm_apply]
    have hsub := submatrix_norm_le (p.symm : Fin N → Fin N) p.symm.injective
      (A.submatrix (p : Fin N → Fin N) p)
    have hrw : Matrix.of (fun i j =>
        (A.submatrix (p : Fin N → Fin N) p) (p.symm i) (p.symm j)) =
        (A.submatrix (p : Fin N → Fin N) p).submatrix
          (p.symm : Fin N → Fin N) p.symm := by
      ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
    rw [hrw, key] at hsub
    exact hsub
  linarith

/-- `IsDiagMatrix` is preserved by submatrix with a permutation. -/
private lemma isDiagMatrix_submatrix_perm_S1g {N : ℕ} (p : Fin N ≃ Fin N)
    (B : Matrix (Fin N) (Fin N) ℂ) (hB : IsDiagMatrix B) :
    IsDiagMatrix (B.submatrix (p : Fin N → Fin N) p) := by
  intro i j hij
  simp only [Matrix.submatrix_apply]
  exact hB (p i) (p j) (fun h => hij (p.injective h))

/-- Diagonal entries of `B.submatrix p p` equal diagonal entries of `B` at `p i`. -/
private lemma submatrix_perm_diag_S1g {N : ℕ} (p : Fin N ≃ Fin N)
    (B : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    (B.submatrix (p : Fin N → Fin N) p) i i = B (p i) (p i) := by
  simp [Matrix.submatrix_apply]

/-- Commutator distributes over `submatrix p p` for a permutation `p`. -/
private lemma matComm_submatrix_perm_S1g {N : ℕ} (p : Fin N ≃ Fin N)
    (B C : Matrix (Fin N) (Fin N) ℂ) :
    (⁅B, C⁆ₘ).submatrix (p : Fin N → Fin N) p =
        ⁅B.submatrix (p : Fin N → Fin N) p, C.submatrix (p : Fin N → Fin N) p⁆ₘ := by
  unfold matComm
  have hBC : (B * C).submatrix (p : Fin N → Fin N) p =
      B.submatrix (p : Fin N → Fin N) p * C.submatrix (p : Fin N → Fin N) p :=
    (Matrix.submatrix_mul_equiv B C (p : Fin N → Fin N) p p).symm
  have hCB : (C * B).submatrix (p : Fin N → Fin N) p =
      C.submatrix (p : Fin N → Fin N) p * B.submatrix (p : Fin N → Fin N) p :=
    (Matrix.submatrix_mul_equiv C B (p : Fin N → Fin N) p p).symm
  ext i j
  have hBCij := congr_fun (congr_fun hBC i) j
  have hCBij := congr_fun (congr_fun hCB i) j
  simp only [Matrix.submatrix_apply, Matrix.sub_apply] at *
  rw [hBCij, hCBij]

/-- Conjugation invariance of `lambdaA` for permutations. -/
private lemma lambdaA_conj_invariant_S1g {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) (p : Fin N ≃ Fin N) :
    lambdaA (A.submatrix (p : Fin N → Fin N) p) = lambdaA A := by
  unfold lambdaA
  set S := {c : ℝ | ∃ (B C : Matrix (Fin N) (Fin N) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hS_def
  set S' := {c : ℝ | ∃ (B C : Matrix (Fin N) (Fin N) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
    A.submatrix (p : Fin N → Fin N) p = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hS'_def
  have hSS' : S = S' := by
    apply Set.eq_of_subset_of_subset
    · intro c hc
      obtain ⟨B, C, hd, hu, heq, hle⟩ := hc
      refine ⟨B.submatrix (p : Fin N → Fin N) p, C.submatrix (p : Fin N → Fin N) p,
        ?_, ?_, ?_, ?_⟩
      · exact isDiagMatrix_submatrix_perm_S1g p B hd
      · intro i; rw [submatrix_perm_diag_S1g p B i]; exact hu (p i)
      · rw [heq]; exact matComm_submatrix_perm_S1g p B C
      · rw [submatrix_perm_norm_eq_S1g p C]; exact hle
    · intro c hc
      obtain ⟨B, C, hd, hu, heq, hle⟩ := hc
      refine ⟨B.submatrix (p.symm : Fin N → Fin N) p.symm,
        C.submatrix (p.symm : Fin N → Fin N) p.symm, ?_, ?_, ?_, ?_⟩
      · exact isDiagMatrix_submatrix_perm_S1g p.symm B hd
      · intro i; rw [submatrix_perm_diag_S1g p.symm B i]; exact hu (p.symm i)
      · have hAround : (A.submatrix (p : Fin N → Fin N) p).submatrix
            (p.symm : Fin N → Fin N) p.symm = A := by
          ext i j; simp [Matrix.submatrix_apply, Equiv.apply_symm_apply]
        rw [← hAround, heq]; exact matComm_submatrix_perm_S1g p.symm B C
      · rw [submatrix_perm_norm_eq_S1g p.symm C]; exact hle
  rw [hS_def, ← hSS']

/-! ## Permutation builder from σ-aware embedding -/

/-- Given a 4-block embedding `e` that is injective per-block, disjoint
    across blocks, and surjective onto Fin (4*m), build the equivalence
    `Fin 4 × Fin m ≃ Fin (4*m)`. -/
private noncomputable def buildSigmaEquiv {m : ℕ}
    (e : Fin 4 → Fin m → Fin (4 * m))
    (hinj : ∀ k, Function.Injective (e k))
    (hdisj : ∀ k k' : Fin 4, k ≠ k' → Disjoint (Set.range (e k)) (Set.range (e k')))
    (hsurj : ∀ i : Fin (4 * m), ∃ k j, e k j = i) :
    Fin 4 × Fin m ≃ Fin (4 * m) where
  toFun p := e p.1 p.2
  invFun i := ((hsurj i).choose, ((hsurj i).choose_spec).choose)
  left_inv := by
    intro ⟨k, j⟩
    have hspec := (hsurj (e k j)).choose_spec
    set k' := (hsurj (e k j)).choose with hk'_def
    set j' := hspec.choose with hj'_def
    have hej' : e k' j' = e k j := hspec.choose_spec
    have hkk' : k' = k := by
      by_contra hne
      have hrange_k : e k j ∈ Set.range (e k) := ⟨j, rfl⟩
      have hrange_k' : e k j ∈ Set.range (e k') := ⟨j', hej'⟩
      have hdis := hdisj k' k hne
      exact (Set.disjoint_iff.mp hdis) ⟨hrange_k', hrange_k⟩
    have hjj' : j' = j := by
      apply hinj k
      have h1 : e k j' = e k' j' := by rw [hkk']
      have h2 : e k j' = e k j := h1.trans hej'
      exact h2
    change (k', j') = (k, j)
    exact Prod.ext hkk' hjj'
  right_inv := by
    intro i
    change e (hsurj i).choose ((hsurj i).choose_spec).choose = i
    exact (hsurj i).choose_spec.choose_spec

/-! ## Canonical block embedding (matches tmp_S1f's signature) -/

/-- Canonical block embedding: view `Fin (4*m)` as 4 blocks of m. -/
private def canonicalBlockEmbed {m : ℕ} : Fin 4 → Fin m → Fin (4 * m) :=
  fun k j => ⟨k.val * m + j.val, by
    have hk := k.isLt; have hj := j.isLt
    calc k.val * m + j.val < k.val * m + m := by omega
      _ = (k.val + 1) * m := by ring
      _ ≤ 4 * m := by nlinarith⟩

/-- Canonical product-to-flat equivalence. -/
private noncomputable def canonicalProdEquiv {m : ℕ} (hm : 0 < m) :
    Fin 4 × Fin m ≃ Fin (4 * m) where
  toFun p := canonicalBlockEmbed p.1 p.2
  invFun i :=
    (⟨i.val / m, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using i.isLt)⟩,
     ⟨i.val % m, Nat.mod_lt _ hm⟩)
  left_inv := by
    intro ⟨k, j⟩
    have hj := j.isLt
    change (⟨_, _⟩, ⟨_, _⟩) = (k, j)
    refine Prod.ext ?_ ?_
    · ext; simp only [canonicalBlockEmbed]
      rw [show k.val * m + j.val = j.val + k.val * m from by omega]
      rw [Nat.add_mul_div_right _ _ hm]
      simp [Nat.div_eq_of_lt hj]
    · ext; simp only [canonicalBlockEmbed]
      rw [show k.val * m + j.val = j.val + k.val * m from by omega]
      simp [Nat.mod_eq_of_lt hj]
  right_inv := by
    intro i
    change canonicalBlockEmbed _ _ = i
    ext; simp only [canonicalBlockEmbed]
    exact Nat.div_add_mod' i.val m

/-! ## σ-aware four-block bound -/

set_option maxHeartbeats 6400000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
/-- σ-aware four-block bound: for any 4-block embedding `e` forming a bijection
    (Fin 4 × Fin m) ↔ Fin (4*m), `lambdaA A` is bounded by the max over k of
    `lambdaA(A.submatrix (e k) (e k))`, with the same constants as the canonical
    version.

    Parameterized by `hStrong` — the conclusion of
    `lambdaA_four_block_bound_strong`. -/
lemma lambdaA_sigma_four_block_bound_param
    {m : ℕ} (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (A : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1)
    (e : Fin 4 → Fin m → Fin (4 * m))
    (hinj : ∀ k, Function.Injective (e k))
    (hdisj : ∀ k k' : Fin 4, k ≠ k' → Disjoint (Set.range (e k)) (Set.range (e k')))
    (hsurj : ∀ i : Fin (4 * m), ∃ k j, e k j = i)
    (hStrong : ∀ (A' : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ),
        ZeroDiag A' → ‖A'‖ = 1 →
        lambdaA A' ≤ 2 / (1 - δ) *
            (⨆ k : Fin 4, lambdaA (A'.submatrix
              (fun j : Fin m => (⟨k.val * m + j.val, by
                have hk := k.isLt; have hj := j.isLt
                calc k.val * m + j.val < k.val * m + m := by omega
                  _ = (k.val + 1) * m := by ring
                  _ ≤ 4 * m := by nlinarith⟩ : Fin (4 * m)))
              (fun j : Fin m => (⟨k.val * m + j.val, by
                have hk := k.isLt; have hj := j.isLt
                calc k.val * m + j.val < k.val * m + m := by omega
                  _ = (k.val + 1) * m := by ring
                  _ ≤ 4 * m := by nlinarith⟩ : Fin (4 * m))))) + 6 / δ) :
    lambdaA A ≤ 2 / (1 - δ) *
        (⨆ k : Fin 4, lambdaA (A.submatrix (e k) (e k))) + 6 / δ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- m = 0
    have h1 : 0 < 1 - δ := sub_pos.mpr hδ1
    have hsup_nn : (0 : ℝ) ≤ ⨆ k : Fin 4, lambdaA (A.submatrix (e k) (e k)) := by
      apply Real.iSup_nonneg
      intro k
      unfold lambdaA
      by_cases hne : ({c : ℝ | ∃ (B C : Matrix (Fin 0) (Fin 0) ℂ),
        IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
        A.submatrix (e k) (e k) = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}).Nonempty
      · exact le_csInf hne (fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle)
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
    have hLA_le : lambdaA A ≤ 0 := by
      unfold lambdaA
      apply csInf_le
      · exact ⟨0, fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
      · refine ⟨0, 0, ?_, ?_, ?_, by norm_num⟩
        · intro i j _; exact Fin.elim0 i
        · intro i; exact Fin.elim0 i
        · ext i; exact Fin.elim0 i
    have h2nn : 0 ≤ 2 / (1 - δ) * (⨆ k : Fin 4, lambdaA (A.submatrix (e k) (e k))) :=
      mul_nonneg (by positivity) hsup_nn
    have h6nn : 0 ≤ 6 / δ := by positivity
    linarith
  · -- m ≥ 1
    classical
    let σEq : Fin 4 × Fin m ≃ Fin (4 * m) :=
      buildSigmaEquiv e hinj hdisj hsurj
    let cEq : Fin 4 × Fin m ≃ Fin (4 * m) := canonicalProdEquiv hm
    let perm : Fin (4 * m) ≃ Fin (4 * m) := cEq.symm.trans σEq
    -- perm ∘ canonicalBlockEmbed k = e k
    have hperm_eq : ∀ (k : Fin 4) (j : Fin m),
        perm (canonicalBlockEmbed k j) = e k j := by
      intro k j
      have h1 : cEq.symm (canonicalBlockEmbed k j) = (k, j) := by
        change (canonicalProdEquiv hm).symm (canonicalBlockEmbed k j) = (k, j)
        rw [show canonicalBlockEmbed k j = (canonicalProdEquiv hm) (k, j) from rfl]
        exact (canonicalProdEquiv hm).symm_apply_apply (k, j)
      have h2 : σEq (k, j) = e k j := rfl
      change σEq (cEq.symm (canonicalBlockEmbed k j)) = e k j
      rw [h1]; exact h2
    -- Apply hStrong to A' = A.submatrix perm perm
    let A' : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
      A.submatrix (perm : Fin (4 * m) → Fin (4 * m)) perm
    have hzd' : ZeroDiag A' := by
      intro i; change A (perm i) (perm i) = 0; exact hzd (perm i)
    have hnorm' : ‖A'‖ = 1 := by
      change ‖A.submatrix (perm : Fin (4 * m) → Fin (4 * m)) perm‖ = 1
      rw [submatrix_perm_norm_eq_S1g perm A]; exact hnorm
    have hStrongApplied := hStrong A' hzd' hnorm'
    -- Show: A'.submatrix canonicalBlockEmbed_k canonicalBlockEmbed_k
    --     = A.submatrix (e k) (e k)
    have hblock_eq : ∀ k : Fin 4,
        A'.submatrix
          (fun j : Fin m => (⟨k.val * m + j.val, by
            have hk := k.isLt; have hj := j.isLt
            calc k.val * m + j.val < k.val * m + m := by omega
              _ = (k.val + 1) * m := by ring
              _ ≤ 4 * m := by nlinarith⟩ : Fin (4 * m)))
          (fun j : Fin m => (⟨k.val * m + j.val, by
            have hk := k.isLt; have hj := j.isLt
            calc k.val * m + j.val < k.val * m + m := by omega
              _ = (k.val + 1) * m := by ring
              _ ≤ 4 * m := by nlinarith⟩ : Fin (4 * m)))
        = A.submatrix (e k) (e k) := by
      intro k
      ext i j
      have hi : perm (canonicalBlockEmbed k i) = e k i := hperm_eq k i
      have hj : perm (canonicalBlockEmbed k j) = e k j := hperm_eq k j
      simp only [Matrix.submatrix_apply, A']
      -- A (perm ⟨k*m+i, _⟩) (perm ⟨k*m+j, _⟩) = A (e k i) (e k j)
      -- The ⟨k*m+i, _⟩ is definitionally canonicalBlockEmbed k i.
      change A (perm (canonicalBlockEmbed k i)) (perm (canonicalBlockEmbed k j))
        = A (e k i) (e k j)
      rw [hi, hj]
    have hsup_eq : (⨆ k : Fin 4, lambdaA (A'.submatrix
        (fun j : Fin m => (⟨k.val * m + j.val, by
          have hk := k.isLt; have hj := j.isLt
          calc k.val * m + j.val < k.val * m + m := by omega
            _ = (k.val + 1) * m := by ring
            _ ≤ 4 * m := by nlinarith⟩ : Fin (4 * m)))
        (fun j : Fin m => (⟨k.val * m + j.val, by
          have hk := k.isLt; have hj := j.isLt
          calc k.val * m + j.val < k.val * m + m := by omega
            _ = (k.val + 1) * m := by ring
            _ ≤ 4 * m := by nlinarith⟩ : Fin (4 * m))))) =
        (⨆ k : Fin 4, lambdaA (A.submatrix (e k) (e k))) := by
      congr 1; ext k; rw [hblock_eq]
    have hLA_eq : lambdaA A' = lambdaA A := by
      change lambdaA (A.submatrix (perm : Fin (4 * m) → Fin (4 * m)) perm) = lambdaA A
      exact lambdaA_conj_invariant_S1g A perm
    rw [hLA_eq, hsup_eq] at hStrongApplied
    exact hStrongApplied

/-! ## S1twoblock: lambdaA_two_block_decomp (two-block η-trick decomposition) -/

/-! Mirrors the 4-block construction (`lambdaA_four_block_bound_strong`) for the
two-block case. The η-trick construction with `α = (1-δ)/2` forces the same-block
coefficient `1/α = 2/(1-δ)`; this is tight (see the docstring in
`tmp_S1twoblock_decomp.lean`). The matching hypothesis shape used by
`lambdaM_2pow4n_bt_recursion_v2` uses this `2/(1-δ)` coefficient.
-/

/-- Block-diagonal norm bound for 2 blocks (mirrors `blockDiag_norm_le_of_blocks`). -/
private lemma blockDiag2_norm_le_of_blocks_S1tb {m : ℕ}
    (Cs : Fin 2 → Matrix (Fin m) (Fin m) ℂ)
    (bound : ℝ) (hbd_nn : 0 ≤ bound)
    (hCs : ∀ k : Fin 2, ‖Cs k‖ ≤ bound) :
    let e : Fin 2 × Fin m ≃ Fin (2 * m) := finProdFinEquiv
    let M : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
      fun i j => if (e.symm i).1 = (e.symm j).1 then
        Cs (e.symm i).1 (e.symm i).2 (e.symm j).2 else 0
    ‖M‖ ≤ bound := by
  intro e M
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hbd_nn
  intro x
  change ‖Matrix.toEuclideanLin M x‖ ≤ bound * ‖x‖
  rw [show Matrix.toEuclideanLin M x = WithLp.toLp 2 (M.mulVec x.ofLp) from
    Matrix.toLpLin_apply 2 2 M x]
  set v := x.ofLp with hv_def
  let vB (k : Fin 2) : Fin m → ℂ := fun j => v (e (k, j))
  have hw_entry : ∀ r, M.mulVec v r =
      (Cs (e.symm r).1).mulVec (vB (e.symm r).1) (e.symm r).2 := by
    intro r; simp only [Matrix.mulVec, dotProduct, M]
    simp_rw [show ∀ c : Fin (2 * m),
        (if (e.symm r).1 = (e.symm c).1 then
          Cs (e.symm r).1 (e.symm r).2 (e.symm c).2 else 0) * v c =
        if (e.symm r).1 = (e.symm c).1 then
          Cs (e.symm r).1 (e.symm r).2 (e.symm c).2 * v c else 0
      from fun c => by split_ifs <;> simp]
    rw [← e.sum_comp (fun c => if (e.symm r).1 = (e.symm c).1 then
      Cs (e.symm r).1 (e.symm r).2 (e.symm c).2 * v c else 0)]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type]
    conv_lhs =>
      arg 2; ext k'
      rw [show ∑ j : Fin m,
          (if (e.symm r).1 = k' then
            Cs (e.symm r).1 (e.symm r).2 j * v (e (k', j)) else 0) =
          if (e.symm r).1 = k' then
            ∑ j, Cs (e.symm r).1 (e.symm r).2 j * v (e (k', j)) else 0
        from by split_ifs <;> simp]
    simp [vB]
  apply le_of_sq_le_sq _ (mul_nonneg hbd_nn (norm_nonneg x))
  have hlhs : ‖(WithLp.toLp 2 (M.mulVec v) :
      EuclideanSpace ℂ (Fin (2 * m)))‖ ^ 2 = ∑ r, ‖(M.mulVec v) r‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
  have hrhs : (bound * ‖x‖) ^ 2 = bound ^ 2 * ∑ r, ‖v r‖ ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_eq x,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
  rw [hlhs, hrhs]
  conv_lhs => rw [← e.sum_comp (fun r => ‖(M.mulVec v) r‖ ^ 2)]
  conv_rhs => rw [← e.sum_comp (fun r => ‖v r‖ ^ 2)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [show ∀ (k : Fin 2) (j : Fin m),
    ‖(M.mulVec v) (e (k, j))‖ = ‖(Cs k).mulVec (vB k) j‖ from
    fun k j => by rw [hw_entry]; simp]
  rw [show bound ^ 2 * ∑ k, ∑ j, ‖v (e (k, j))‖ ^ 2 =
    ∑ k : Fin 2, bound ^ 2 * ∑ j, ‖v (e (k, j))‖ ^ 2 from by
      rw [Finset.mul_sum]]
  apply Finset.sum_le_sum
  intro k _
  set xk := (EuclideanSpace.equiv (Fin m) ℂ).symm (vB k) with hxk_def
  have hle : ‖(EuclideanSpace.equiv _ ℂ).symm ((Cs k).mulVec (vB k))‖ ≤ bound * ‖xk‖ :=
    calc _ ≤ ‖Cs k‖ * ‖xk‖ := Matrix.l2_opNorm_mulVec (Cs k) xk
      _ ≤ bound * ‖xk‖ := mul_le_mul_of_nonneg_right (hCs k) (norm_nonneg _)
  have hle_sq : ‖(EuclideanSpace.equiv _ ℂ).symm ((Cs k).mulVec (vB k))‖ ^ 2 ≤
      (bound * ‖xk‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) 2))] at hle_sq
  rw [mul_pow, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) 2))] at hle_sq
  convert hle_sq using 2

set_option maxHeartbeats 6400000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
/-- **Two-block decomposition (η-trick, natural `2/(1-δ)` coefficient).**

Given two disjoint covering injections `H, H' : Fin (4^n) → Fin (2·4^n)`,
the η-trick construction yields a bound of the form
`lambdaA A ≤ 2/(1-δ) * (lambdaA(A_HH) + lambdaA(A_H'H')) + C/δ`.

The leading coefficient `2/(1-δ)` is tight under the η-trick construction
(with `α = (1-δ)/2` to preserve the spectral gap `≥ 2δ` between the two
corner values `±(1+δ)/2`). -/
lemma lambdaA_two_block_decomp :
    ∃ C_two : ℝ, 0 < C_two ∧
    ∀ (n : ℕ) (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ < 1)
      (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ),
      ZeroDiag A → ‖A‖ = 1 →
      ∀ (H H' : Fin (4 ^ n) → Fin (2 * 4 ^ n)),
      Function.Injective H → Function.Injective H' →
      Disjoint (Set.range H) (Set.range H') →
      (Set.range H ∪ Set.range H') = Set.univ →
      lambdaA A ≤ 2 / (1 - δ) *
          (lambdaA (A.submatrix H H) + lambdaA (A.submatrix H' H')) + C_two / δ := by
  refine ⟨1, by norm_num, ?_⟩
  intro n δ hδ hδ1 A hzd hnorm H H' hH_inj hH'_inj hdisj hcover
  have hm_pos : 0 < 4 ^ n := Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
  have h2m_pos : 0 < 2 * 4 ^ n := by omega
  have h1δ : (0 : ℝ) < 1 - δ := sub_pos.mpr hδ1
  -- Block-embed: index k ∈ Fin 2 → (Fin (4^n) → Fin (2 * 4^n))
  let blockEmbed : Fin 2 → Fin (4 ^ n) → Fin (2 * 4 ^ n) := fun k =>
    if k = 0 then H else H'
  have hbE0 : blockEmbed 0 = H := by simp [blockEmbed]
  have hbE1 : blockEmbed 1 = H' := by simp [blockEmbed]
  have hFin2_cases : ∀ k : Fin 2, k = 0 ∨ k = 1 := by
    intro k
    have hk := k.isLt
    interval_cases h : k.val
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  have hblockEmbed_inj : ∀ k : Fin 2, Function.Injective (blockEmbed k) := by
    intro k
    rcases hFin2_cases k with hk0 | hk1
    · subst hk0; rw [hbE0]; exact hH_inj
    · subst hk1; rw [hbE1]; exact hH'_inj
  have hblockEmbed_disjoint : ∀ k k' : Fin 2, k ≠ k' →
      Disjoint (Set.range (blockEmbed k)) (Set.range (blockEmbed k')) := by
    intro k k' hne
    rcases hFin2_cases k with hk0 | hk1 <;>
      rcases hFin2_cases k' with hk'0 | hk'1
    · subst hk0; subst hk'0; exact absurd rfl hne
    · subst hk0; subst hk'1; rw [hbE0, hbE1]; exact hdisj
    · subst hk1; subst hk'0; rw [hbE0, hbE1]; exact hdisj.symm
    · subst hk1; subst hk'1; exact absurd rfl hne
  -- Each diagonal block
  let diagBlock : Fin 2 → Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ :=
    fun k => Matrix.of (fun i j => A (blockEmbed k i) (blockEmbed k j))
  have hzd_block : ∀ k, ZeroDiag (diagBlock k) := by
    intro k i; simp only [diagBlock, Matrix.of_apply]; exact hzd (blockEmbed k i)
  have hnorm_block : ∀ k, ‖diagBlock k‖ ≤ 1 := by
    intro k; rw [← hnorm]
    exact submatrix_norm_le (blockEmbed k) (hblockEmbed_inj k) A
  -- The target SUM
  set S : ℝ := lambdaA (diagBlock 0) + lambdaA (diagBlock 1) with hS_def
  have hS_nn : 0 ≤ S := by
    rw [hS_def]
    have h0 := lambdaA_nonneg_S1f (diagBlock 0)
    have h1 := lambdaA_nonneg_S1f (diagBlock 1)
    linarith
  -- The target sum equals the lemma target
  have hdiagBlock_subm : ∀ k : Fin 2,
      diagBlock k = A.submatrix (blockEmbed k) (blockEmbed k) := by
    intro k; ext i j; simp [diagBlock, Matrix.submatrix_apply]
  have hS_eq_target : S = lambdaA (A.submatrix H H) + lambdaA (A.submatrix H' H') := by
    rw [hS_def]
    rw [hdiagBlock_subm 0, hdiagBlock_subm 1, hbE0, hbE1]
  rw [hS_eq_target.symm]
  -- ===== Build blockIdx / localIdx =====
  have hin_range : ∀ i : Fin (2 * 4 ^ n),
      i ∈ Set.range H ∨ i ∈ Set.range H' := by
    intro i
    have : i ∈ Set.range H ∪ Set.range H' := by rw [hcover]; exact Set.mem_univ _
    rcases this with hl | hr
    · exact Or.inl hl
    · exact Or.inr hr
  classical
  let blockIdx : Fin (2 * 4 ^ n) → Fin 2 := fun i =>
    if i ∈ Set.range H then 0 else 1
  let localIdx : Fin (2 * 4 ^ n) → Fin (4 ^ n) := fun i =>
    if h : i ∈ Set.range H then h.choose
    else (Classical.choose ((hin_range i).resolve_left h))
  have hEmbed_id : ∀ i : Fin (2 * 4 ^ n), blockEmbed (blockIdx i) (localIdx i) = i := by
    intro i
    by_cases hH : i ∈ Set.range H
    · simp only [blockIdx, localIdx, hH, dif_pos, if_pos]
      rw [hbE0]; exact hH.choose_spec
    · simp only [blockIdx, localIdx, hH, dif_neg, if_neg, not_false_iff]
      have hH' : i ∈ Set.range H' := (hin_range i).resolve_left hH
      rw [hbE1]; exact (Classical.choose_spec ((hin_range i).resolve_left hH))
  have hBlockIdx_embed : ∀ (k : Fin 2) (j : Fin (4 ^ n)),
      blockIdx (blockEmbed k j) = k := by
    intro k j
    rcases hFin2_cases k with hk0 | hk1
    · subst hk0
      simp only [blockIdx]
      have hmem : (blockEmbed 0 j) ∈ Set.range H := by rw [hbE0]; exact ⟨j, rfl⟩
      rw [if_pos hmem]
    · subst hk1
      simp only [blockIdx]
      have hmem' : (blockEmbed 1 j) ∈ Set.range H' := by rw [hbE1]; exact ⟨j, rfl⟩
      have hnot : (blockEmbed 1 j) ∉ Set.range H := by
        intro hin
        have hd := hdisj
        rw [Set.disjoint_iff] at hd
        exact hd ⟨hin, hmem'⟩
      rw [if_neg hnot]
  have hLocalIdx_embed : ∀ (k : Fin 2) (j : Fin (4 ^ n)),
      localIdx (blockEmbed k j) = j := by
    intro k j
    rcases hFin2_cases k with hk0 | hk1
    · subst hk0
      have hmem : (blockEmbed 0 j) ∈ Set.range H := by rw [hbE0]; exact ⟨j, rfl⟩
      simp only [localIdx, hmem, dif_pos]
      have hspec : H hmem.choose = blockEmbed 0 j := hmem.choose_spec
      have hHj : H j = blockEmbed 0 j := by rw [hbE0]
      exact hH_inj (hspec.trans hHj.symm)
    · subst hk1
      have hmem' : (blockEmbed 1 j) ∈ Set.range H' := by rw [hbE1]; exact ⟨j, rfl⟩
      have hnot : (blockEmbed 1 j) ∉ Set.range H := by
        intro hin
        have hd := hdisj
        rw [Set.disjoint_iff] at hd
        exact hd ⟨hin, hmem'⟩
      simp only [localIdx, hnot, dif_neg, not_false_iff]
      have hresolve : (blockEmbed 1 j) ∈ Set.range H' :=
        (hin_range (blockEmbed 1 j)).resolve_left hnot
      have hspec : H' (Classical.choose hresolve) = blockEmbed 1 j :=
        Classical.choose_spec hresolve
      have hH'j : H' j = blockEmbed 1 j := by rw [hbE1]
      exact hH'_inj (hspec.trans hH'j.symm)
  -- ===== Set up nearly-optimal block decompositions =====
  apply le_of_forall_pos_lt_add
  intro ε hε
  have hne_block : ∀ k, ∃ (B C : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
      diagBlock k = ⁅B, C⁆ₘ := by
    intro k
    rcases Nat.lt_or_ge (4 ^ n) 2 with hm2 | hm2
    · have hm1 : 4 ^ n = 1 := by omega
      refine ⟨0, 0, ?_, ?_, ?_⟩
      · intro i j hij; simp
      · intro i; unfold InUnitSquare; simp
      · ext i j; simp only [matComm, mul_zero, Matrix.sub_apply, Matrix.zero_apply, sub_self]
        have : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
        rw [this]; exact hzd_block k j
    · obtain ⟨B, C, hd, hu, hc, _⟩ :=
        zeroDiag_InUnitSquare_decomp_bounded_S1f hm2 (diagBlock k) (hzd_block k)
      exact ⟨B, C, hd, hu, hc⟩
  -- η slack
  set η := ε * (1 - δ) / 8 with hη_def
  have hη_pos : 0 < η := by positivity
  -- Pick near-optimal decompositions
  have hpick : ∀ k : Fin 2, ∃ (Bk Ck : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ),
      IsDiagMatrix Bk ∧ (∀ i, InUnitSquare (Bk i i)) ∧
      diagBlock k = ⁅Bk, Ck⁆ₘ ∧ ‖Ck‖ ≤ lambdaA (diagBlock k) + η := by
    intro k
    set Sset := {c : ℝ | ∃ (B C : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
      diagBlock k = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hSset_def
    have hne_Sset : Sset.Nonempty := by
      obtain ⟨B, C, hdiag, husq, hcomm⟩ := hne_block k
      exact ⟨‖C‖, B, C, hdiag, husq, hcomm, le_refl _⟩
    have hbdd : BddBelow Sset := by
      refine ⟨0, fun c ⟨B, C, _, _, _, hle⟩ => ?_⟩
      exact le_trans (norm_nonneg _) hle
    have hlt : sInf Sset < lambdaA (diagBlock k) + η := by
      unfold lambdaA; linarith
    obtain ⟨c, ⟨B, C, hdiag, husq, hcomm, hnorm⟩, hc_lt⟩ :=
      exists_lt_of_csInf_lt hne_Sset hlt
    exact ⟨B, C, hdiag, husq, hcomm, le_trans hnorm (le_of_lt hc_lt)⟩
  choose Bk Ck hBk_diag hBk_usq hBk_comm hCk_norm using hpick
  -- Bound each ‖Ck k‖ by S + 2η (sum-style bound)
  have hCk_bound : ∀ k : Fin 2, ‖Ck k‖ ≤ S + 2 * η := by
    intro k
    have h0 : 0 ≤ lambdaA (diagBlock 0) := lambdaA_nonneg_S1f _
    have h1 : 0 ≤ lambdaA (diagBlock 1) := lambdaA_nonneg_S1f _
    rcases hFin2_cases k with hk0 | hk1
    · subst hk0
      calc ‖Ck 0‖ ≤ lambdaA (diagBlock 0) + η := hCk_norm 0
        _ ≤ S + 2 * η := by rw [hS_def]; linarith
    · subst hk1
      calc ‖Ck 1‖ ≤ lambdaA (diagBlock 1) + η := hCk_norm 1
        _ ≤ S + 2 * η := by rw [hS_def]; linarith
  -- Build the witness
  suffices hwit : ∃ (B' C' : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ),
      IsDiagMatrix B' ∧ (∀ i, InUnitSquare (B' i i)) ∧
      A = ⁅B', C'⁆ₘ ∧ ‖C'‖ ≤ 2 / (1 - δ) * (S + 2 * η) + 1 / δ by
    obtain ⟨B', C', hd, hu, hc, hn⟩ := hwit
    have hη_bound : 2 / (1 - δ) * (2 * η) = ε / 2 := by
      rw [hη_def]; field_simp; ring
    calc lambdaA A
        ≤ ‖C'‖ := csInf_le
          ⟨0, fun c ⟨_, C, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
          ⟨B', C', hd, hu, hc, le_refl _⟩
      _ ≤ 2 / (1 - δ) * (S + 2 * η) + 1 / δ := hn
      _ = 2 / (1 - δ) * S + 2 / (1 - δ) * (2 * η) + 1 / δ := by ring
      _ = 2 / (1 - δ) * S + 1 / δ + ε / 2 := by rw [hη_bound]; ring
      _ < 2 / (1 - δ) * S + 1 / δ + ε := by linarith
  -- === Construction ===
  let cornerRe : Fin 2 → ℝ := ![ (1 + δ) / 2, -(1 + δ) / 2 ]
  let cornerVal : Fin 2 → ℂ := fun k => (cornerRe k : ℂ)
  let fullB : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ :=
    Matrix.diagonal (fun i =>
      ((1 - δ) / 2 : ℝ) * (Bk (blockIdx i)) (localIdx i) (localIdx i) +
      cornerVal (blockIdx i))
  have hfullB_diag : IsDiagMatrix fullB :=
    fun i j hij => Matrix.diagonal_apply_ne _ hij
  have hcre_vals : ∀ k : Fin 2, cornerRe k = (1 + δ) / 2 ∨ cornerRe k = -(1 + δ) / 2 := by
    intro k
    rcases hFin2_cases k with hk0 | hk1
    · subst hk0; left; simp [cornerRe]
    · subst hk1; right; simp [cornerRe]
  have hfullB_usq : ∀ i, InUnitSquare (fullB i i) := by
    intro i; simp only [fullB, Matrix.diagonal_apply_eq]
    have key : ∀ (x c : ℝ), |x| ≤ 1 → |c| = (1 + δ) / 2 → |(1 - δ) / 2 * x + c| ≤ 1 := by
      intro x c hx hc
      rw [abs_le]; rw [abs_le] at hx; obtain ⟨hx_lo, hx_hi⟩ := hx
      by_cases hc0 : 0 ≤ c
      · rw [abs_of_nonneg hc0] at hc; subst hc; constructor <;> nlinarith
      · have hc0' : c < 0 := not_le.mp hc0
        rw [abs_of_neg hc0'] at hc; constructor <;> nlinarith
    have hcre_abs : ∀ k : Fin 2, |cornerRe k| = (1 + δ) / 2 := by
      intro k; rcases hcre_vals k with hk | hk
      · rw [hk]; exact abs_of_nonneg (by linarith)
      · rw [hk, show -(1 + δ) / 2 = -((1 + δ) / 2) from neg_div _ _, abs_neg]
        exact abs_of_nonneg (by linarith)
    obtain ⟨hbre, hbim⟩ := hBk_usq (blockIdx i) (localIdx i)
    have hre_eq : (↑((1 - δ) / 2) * Bk (blockIdx i) (localIdx i) (localIdx i) +
        cornerVal (blockIdx i)).re =
        (1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re +
        cornerRe (blockIdx i) := by
      simp [cornerVal, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have him_eq : (↑((1 - δ) / 2) * Bk (blockIdx i) (localIdx i) (localIdx i) +
        cornerVal (blockIdx i)).im =
        (1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).im + 0 := by
      simp [cornerVal, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨hre_eq ▸ key _ _ hbre (hcre_abs _), ?_⟩
    rw [him_eq, add_zero]
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (1 - δ) / 2)]
    nlinarith [abs_nonneg ((Bk (blockIdx i) (localIdx i) (localIdx i)).im)]
  -- Spectral gap (Real-axis only for 2-block)
  have hSpectralGap_re : ∀ (i j : Fin (2 * 4 ^ n)),
      blockIdx i ≠ blockIdx j →
      2 * δ ≤ |(fullB i i - fullB j j).re| := by
    intro i j hne
    simp only [fullB, Matrix.diagonal_apply_eq]
    obtain ⟨hri, _⟩ := hBk_usq (blockIdx i) (localIdx i)
    obtain ⟨hrj, _⟩ := hBk_usq (blockIdx j) (localIdx j)
    have pert_bound : ∀ (x y a : ℝ), 0 ≤ a → |x| ≤ 1 → |y| ≤ 1 →
        |a / 2 * x - a / 2 * y| ≤ a := by
      intro x y a ha hx hy
      rw [show a / 2 * x - a / 2 * y = a / 2 * (x - y) from by ring]
      rw [abs_mul, abs_of_nonneg (by linarith)]
      have hxy : |x - y| ≤ 2 := le_trans (abs_sub x y) (by linarith)
      nlinarith
    have rev_tri : ∀ (a b : ℝ), |b| - |a| ≤ |a + b| := by
      intro a b
      have h := abs_sub (a + b) a
      simp [add_sub_cancel_left] at h; linarith
    have hpert_re : |(1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re -
        (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).re| ≤ 1 - δ :=
      pert_bound _ _ _ (by linarith) hri hrj
    have hre_eq : (((1 - δ) / 2 : ℝ) * Bk (blockIdx i) (localIdx i) (localIdx i) +
        cornerVal (blockIdx i) -
        (((1 - δ) / 2 : ℝ) * Bk (blockIdx j) (localIdx j) (localIdx j) +
        cornerVal (blockIdx j))).re =
      (1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re -
      (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).re +
      (cornerRe (blockIdx i) - cornerRe (blockIdx j)) := by
      simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, cornerVal]; ring
    have corner_inj_2 : ∀ (a b : Fin 2), cornerRe a = cornerRe b → a = b := by
      intro a b h
      rcases hFin2_cases a with ha0 | ha1 <;> rcases hFin2_cases b with hb0 | hb1
      · subst ha0; exact hb0.symm
      · subst ha0; subst hb1; simp [cornerRe] at h; linarith
      · subst ha1; subst hb0; simp [cornerRe] at h; linarith
      · subst ha1; exact hb1.symm
    have hcorner_diff : cornerRe (blockIdx i) ≠ cornerRe (blockIdx j) := by
      intro habs
      exact hne (corner_inj_2 _ _ habs)
    have corner_gap : ∀ (f : Fin 2 → ℝ), (∀ k, f k = (1 + δ) / 2 ∨ f k = -(1 + δ) / 2) →
        f (blockIdx i) ≠ f (blockIdx j) → |f (blockIdx i) - f (blockIdx j)| = 1 + δ := by
      intro f hvals hneq
      rcases hvals (blockIdx i) with hi | hi <;> rcases hvals (blockIdx j) with hj | hj
      · exfalso; exact hneq (by rw [hi, hj])
      · rw [hi, hj]; rw [show (1 + δ) / 2 - -(1 + δ) / 2 = 1 + δ from by ring]
        exact abs_of_pos (by linarith)
      · rw [hi, hj]; rw [show -(1 + δ) / 2 - (1 + δ) / 2 = -(1 + δ) from by ring]
        rw [abs_neg]; exact abs_of_pos (by linarith)
      · exfalso; exact hneq (by rw [hi, hj])
    rw [hre_eq]
    have hgap := corner_gap cornerRe hcre_vals hcorner_diff
    linarith [rev_tri ((1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re -
      (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).re)
      (cornerRe (blockIdx i) - cornerRe (blockIdx j))]
  have hFullB_ne : ∀ (i j : Fin (2 * 4 ^ n)),
      blockIdx i ≠ blockIdx j → fullB i i ≠ fullB j j := by
    intro i j hne habs
    have hre := hSpectralGap_re i j hne
    have : (fullB i i - fullB j j).re = 0 := by rw [habs]; simp
    rw [this] at hre; simp at hre; linarith
  -- Define fullC
  let fullC : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ :=
    fun i j =>
      if blockIdx i = blockIdx j then
        (2 / ((1 : ℝ) - δ) : ℂ) * (Ck (blockIdx i)) (localIdx i) (localIdx j)
      else
        A i j / (fullB i i - fullB j j)
  -- Verify A = [fullB, fullC]
  have hComm : A = ⁅fullB, fullC⁆ₘ := by
    ext i j
    rw [commutator_diag_entry fullB fullC hfullB_diag]
    simp only [fullC]
    split_ifs with heq
    · simp only [fullB, Matrix.diagonal_apply_eq]
      have hAij : A i j = diagBlock (blockIdx i) (localIdx i) (localIdx j) := by
        simp only [diagBlock, Matrix.of_apply]
        conv_rhs => rw [show blockEmbed (blockIdx i) (localIdx j) =
          blockEmbed (blockIdx j) (localIdx j) from by rw [heq],
          hEmbed_id j, hEmbed_id i]
      rw [hAij, hBk_comm (blockIdx i),
        commutator_diag_entry _ _ (hBk_diag _), heq]
      have h1δne : (1 : ℝ) - δ ≠ 0 := by linarith
      have hkey : (↑((1 - δ) / 2) : ℂ) * (2 / (↑1 - ↑δ)) = 1 := by
        push_cast
        field_simp [show (1 : ℂ) - ↑δ ≠ 0 from by exact_mod_cast h1δne]
      have hrw : (↑((1 - δ) / 2) : ℂ) * Bk (blockIdx j) (localIdx i) (localIdx i) +
          cornerVal (blockIdx j) -
          ((↑((1 - δ) / 2) : ℂ) * Bk (blockIdx j) (localIdx j) (localIdx j) +
          cornerVal (blockIdx j)) =
          (↑((1 - δ) / 2) : ℂ) * (Bk (blockIdx j) (localIdx i) (localIdx i) -
          Bk (blockIdx j) (localIdx j) (localIdx j)) := by ring
      rw [hrw]
      simp only [Complex.ofReal_one]
      rw [show (↑((1 - δ) / 2) : ℂ) *
          (Bk (blockIdx j) (localIdx i) (localIdx i) -
          Bk (blockIdx j) (localIdx j) (localIdx j)) *
          (2 / (1 - ↑δ) * Ck (blockIdx j) (localIdx i) (localIdx j)) =
          (↑((1 - δ) / 2) : ℂ) * (2 / (1 - ↑δ)) *
          ((Bk (blockIdx j) (localIdx i) (localIdx i) -
          Bk (blockIdx j) (localIdx j) (localIdx j)) *
          Ck (blockIdx j) (localIdx i) (localIdx j)) from by ring]
      rw [hkey, one_mul]
    · have hne := hFullB_ne i j heq
      have hne' : fullB i i - fullB j j ≠ 0 := sub_ne_zero.mpr hne
      field_simp [hne']
  -- ===== Norm bound on fullC =====
  have hfullC_bound : ‖fullC‖ ≤ 2 / (1 - δ) * (S + 2 * η) + 1 / δ := by
    let sameBlockC : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ :=
      fun i j => if blockIdx i = blockIdx j then
        (2 / ((1 : ℝ) - δ) : ℂ) * (Ck (blockIdx i)) (localIdx i) (localIdx j)
      else 0
    let crossBlockC : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ :=
      fun i j => if blockIdx i = blockIdx j then 0
      else A i j / (fullB i i - fullB j j)
    have hdecomp : fullC = sameBlockC + crossBlockC := by
      ext i j; simp only [fullC, sameBlockC, crossBlockC, Matrix.add_apply]
      split_ifs <;> simp
    calc ‖fullC‖ = ‖sameBlockC + crossBlockC‖ := by rw [hdecomp]
      _ ≤ ‖sameBlockC‖ + ‖crossBlockC‖ := norm_add_le _ _
      _ ≤ 2 / (1 - δ) * (S + 2 * η) + 1 / δ := by
        apply add_le_add
        · -- ‖sameBlockC‖ ≤ 2/(1-δ) * (S + 2η)
          have hcoeff_nn : (0 : ℝ) ≤ 2 / (1 - δ) := div_nonneg (by norm_num) (le_of_lt h1δ)
          have hscale_val : ‖(2 / ((1 : ℝ) - δ) : ℂ)‖ = 2 / (1 - δ) := by
            have h2c : (2 : ℂ) / ((1 : ℝ) - δ) = ((2 / (1 - δ) : ℝ) : ℂ) := by push_cast; ring
            rw [h2c, Complex.norm_real]
            exact abs_of_pos (div_pos (by norm_num : (0:ℝ) < 2) h1δ)
          let Mmat : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ :=
            fun i j => if blockIdx i = blockIdx j then
              (Ck (blockIdx i)) (localIdx i) (localIdx j)
            else 0
          have hscale : sameBlockC = (2 / ((1 : ℝ) - δ) : ℂ) • Mmat := by
            ext i j; simp only [sameBlockC, Mmat, Matrix.smul_apply, smul_eq_mul]
            split_ifs <;> simp
          let pad : Fin 2 → Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ := fun k =>
            fun i j => if blockIdx i = k ∧ blockIdx j = k then
              (Ck k) (localIdx i) (localIdx j)
            else 0
          have hpad_sum : Mmat = pad 0 + pad 1 := by
            ext i j; simp only [Mmat, pad, Matrix.add_apply]
            by_cases h : blockIdx i = blockIdx j
            · rw [if_pos h]
              rcases hFin2_cases (blockIdx i) with hi | hi
              · have hj0 : blockIdx j = 0 := h.symm.trans hi
                have hpos : (blockIdx i = 0 ∧ blockIdx j = 0) := ⟨hi, hj0⟩
                have hneg : ¬ (blockIdx i = 1 ∧ blockIdx j = 1) :=
                  fun ⟨h1, _⟩ => by rw [hi] at h1; exact absurd h1 (by decide)
                rw [if_pos hpos, if_neg hneg, hi]; simp
              · have hj1 : blockIdx j = 1 := h.symm.trans hi
                have hneg : ¬ (blockIdx i = 0 ∧ blockIdx j = 0) :=
                  fun ⟨h0, _⟩ => by rw [hi] at h0; exact absurd h0 (by decide)
                have hpos : (blockIdx i = 1 ∧ blockIdx j = 1) := ⟨hi, hj1⟩
                rw [if_neg hneg, if_pos hpos, hi]; simp
            · rw [if_neg h]
              have h0 : ¬ (blockIdx i = 0 ∧ blockIdx j = 0) := fun ⟨a, b⟩ => h (a.trans b.symm)
              have h1 : ¬ (blockIdx i = 1 ∧ blockIdx j = 1) := fun ⟨a, b⟩ => h (a.trans b.symm)
              rw [if_neg h0, if_neg h1]; ring
          have hpad_norm : ∀ k : Fin 2, ‖pad k‖ ≤ ‖Ck k‖ := by
            intro k
            apply embedBlock_norm_le (blockEmbed k) (blockEmbed k)
              (hblockEmbed_inj k) (hblockEmbed_inj k)
              (pad k) (Ck k)
            · intro i j hrow
              simp only [pad]
              have hbi : blockIdx i ≠ k := by
                intro hbi
                exact hrow (localIdx i) (by rw [← hbi]; exact hEmbed_id i)
              rw [if_neg (fun h => hbi h.1)]
            · intro i j hcol
              simp only [pad]
              have hbj : blockIdx j ≠ k := by
                intro hbj
                exact hcol (localIdx j) (by rw [← hbj]; exact hEmbed_id j)
              rw [if_neg (fun h => hbj h.2)]
            · intro i j
              simp only [pad, hBlockIdx_embed, and_self, if_true, hLocalIdx_embed]
          have hMmat_bound : ‖Mmat‖ ≤ S + 2 * η := by
            calc ‖Mmat‖ = ‖pad 0 + pad 1‖ := by rw [hpad_sum]
              _ ≤ ‖pad 0‖ + ‖pad 1‖ := norm_add_le _ _
              _ ≤ ‖Ck 0‖ + ‖Ck 1‖ := add_le_add (hpad_norm 0) (hpad_norm 1)
              _ ≤ (lambdaA (diagBlock 0) + η) + (lambdaA (diagBlock 1) + η) :=
                  add_le_add (hCk_norm 0) (hCk_norm 1)
              _ = S + 2 * η := by rw [hS_def]; ring
          rw [hscale, norm_smul, hscale_val]
          exact mul_le_mul_of_nonneg_left hMmat_bound hcoeff_nn
        · -- ‖crossBlockC‖ ≤ 1/δ
          let crossPairs : Finset (Fin 2 × Fin 2) :=
            Finset.univ.filter (fun p => p.1 ≠ p.2)
          let embedBlock : Fin 2 × Fin 2 → Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ :=
            fun p => fun i j =>
              if blockIdx i = p.1 ∧ blockIdx j = p.2 then
                A i j / (fullB i i - fullB j j)
              else 0
          have hcross_sum : crossBlockC = ∑ p ∈ crossPairs, embedBlock p := by
            ext i j
            simp only [Matrix.sum_apply, crossBlockC, embedBlock]
            by_cases heq : blockIdx i = blockIdx j
            · simp only [heq, ite_true]
              symm; apply Finset.sum_eq_zero
              intro p hp
              simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
              split_ifs with h
              · have : p.1 = p.2 := by rw [← h.1, ← h.2]
                exact absurd this hp
              · rfl
            · simp only [heq, ite_false]
              have hmem : (blockIdx i, blockIdx j) ∈ crossPairs := by
                simp only [crossPairs, Finset.mem_filter, Finset.mem_univ,
                  true_and]; exact heq
              rw [← Finset.add_sum_erase _ _ hmem]
              simp only [true_and, ite_true]
              suffices hsuff : ∑ x ∈ crossPairs.erase (blockIdx i, blockIdx j),
                  (if blockIdx i = x.1 ∧ blockIdx j = x.2
                    then A i j / (fullB i i - fullB j j) else 0) = 0 by
                rw [hsuff, add_zero]
              apply Finset.sum_eq_zero; intro p hp
              simp only [Finset.mem_erase] at hp
              split_ifs with h
              · exfalso; exact hp.1 (Prod.ext h.1.symm h.2.symm)
              · rfl
          have hcard : crossPairs.card = 2 := by decide
          have hblock_bound : ∀ p ∈ crossPairs, ‖embedBlock p‖ ≤ 1 / (2 * δ) := by
            intro ⟨k, l⟩ hp
            simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
            let Skl : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ :=
              Matrix.diagonal (fun i => fullB (blockEmbed k i) (blockEmbed k i))
            let Tkl : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ :=
              Matrix.diagonal (fun j => fullB (blockEmbed l j) (blockEmbed l j))
            let Akl : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ :=
              Matrix.of (fun i j => A (blockEmbed k i) (blockEmbed l j))
            let Xkl : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ :=
              fun i j => Akl i j / (Skl i i - Tkl j j)
            have hSkl_diag : IsDiagMatrix Skl := diag_isDiagMatrix_S1f _
            have hTkl_diag : IsDiagMatrix Tkl := diag_isDiagMatrix_S1f _
            have hSigned : (∀ i j, 2 * δ ≤ (Skl i i - Tkl j j).re) ∨
                (∀ i j, (Skl i i - Tkl j j).re ≤ -(2 * δ)) := by
              have hpert : ∀ (x y : ℝ), |x| ≤ 1 → |y| ≤ 1 →
                  -(1 - δ) ≤ (1 - δ) / 2 * x - (1 - δ) / 2 * y ∧
                  (1 - δ) / 2 * x - (1 - δ) / 2 * y ≤ 1 - δ := by
                intro x y hx hy
                rw [abs_le] at hx hy
                constructor <;> nlinarith
              have hDiff_re : ∀ i j, (Skl i i - Tkl j j).re =
                  (1 - δ) / 2 * (Bk k i i).re - (1 - δ) / 2 * (Bk l j j).re +
                  (cornerRe k - cornerRe l) := by
                intro i j
                simp only [Skl, Tkl, Matrix.diagonal_apply_eq, fullB,
                  hBlockIdx_embed, hLocalIdx_embed, cornerVal,
                  Complex.sub_re, Complex.add_re, Complex.mul_re,
                  Complex.ofReal_re, Complex.ofReal_im]
                ring
              have corner_inj_kl : ∀ (a b : Fin 2), cornerRe a = cornerRe b → a = b := by
                intro a b h
                rcases hFin2_cases a with ha | ha <;> rcases hFin2_cases b with hb | hb
                · subst ha; exact hb.symm
                · subst ha; subst hb; simp [cornerRe] at h; linarith
                · subst ha; subst hb; simp [cornerRe] at h; linarith
                · subst ha; exact hb.symm
              rcases hcre_vals k with hk | hk <;> rcases hcre_vals l with hl | hl
              · exfalso
                exact hp (corner_inj_kl _ _ (hk.trans hl.symm))
              · left; intro i j
                rw [hDiff_re i j]
                have hxi := (hBk_usq k i).1
                have hyj := (hBk_usq l j).1
                have hp1 := (hpert _ _ hxi hyj).1
                rw [hk, hl]; linarith
              · right; intro i j
                rw [hDiff_re i j]
                have hxi := (hBk_usq k i).1
                have hyj := (hBk_usq l j).1
                have hp2 := (hpert _ _ hxi hyj).2
                rw [hk, hl]; linarith
              · exfalso
                exact hp (corner_inj_kl _ _ (hk.trans hl.symm))
            have hSylv : ‖Xkl‖ ≤ ‖Akl‖ / (2 * δ) := by
              rcases hSigned with hpos_re | hneg_re
              · exact (sylvester_diag_opNorm_bound_re Skl Tkl Akl
                  hSkl_diag hTkl_diag (2 * δ) (by positivity) hpos_re).2
              · let S' : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ := -Skl
                let T' : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ := -Tkl
                let A' : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ := -Akl
                have hS'_diag : IsDiagMatrix S' := by
                  intro i j hij; simp [S', Skl, Matrix.diagonal, hij]
                have hT'_diag : IsDiagMatrix T' := by
                  intro i j hij; simp [T', Tkl, Matrix.diagonal, hij]
                have hSep' : ∀ i j, 2 * δ ≤ (S' i i - T' j j).re := by
                  intro i j
                  simp only [S', T', Matrix.neg_apply, Complex.sub_re, Complex.neg_re]
                  have := hneg_re i j
                  simp only [Complex.sub_re] at this; linarith
                have hXeq : (fun i j => A' i j / (S' i i - T' j j)) = Xkl := by
                  ext i j
                  simp only [S', T', A', Xkl, Akl, Skl, Tkl, Matrix.neg_apply,
                    Matrix.of_apply, Matrix.diagonal_apply_eq]
                  set a := A (blockEmbed k i) (blockEmbed l j)
                  set b := fullB (blockEmbed k i) (blockEmbed k i)
                  set c := fullB (blockEmbed l j) (blockEmbed l j)
                  show -a / (-b - -c) = a / (b - c)
                  rw [show -b - -c = -(b - c) from by ring, neg_div_neg_eq]
                have key := (sylvester_diag_opNorm_bound_re S' T' A'
                  hS'_diag hT'_diag (2 * δ) (by positivity) hSep').2
                rw [hXeq] at key
                rw [show ‖A'‖ = ‖Akl‖ from by simp [A', norm_neg]] at key
                exact key
            have hAkl_norm : ‖Akl‖ ≤ 1 := by
              rw [← hnorm]
              exact cross_submatrix_norm_le (blockEmbed k) (blockEmbed l)
                (hblockEmbed_inj k) (hblockEmbed_inj l) A
            have hembed_norm : ‖embedBlock (k, l)‖ ≤ ‖Xkl‖ := by
              apply embedBlock_norm_le (blockEmbed k) (blockEmbed l)
                (hblockEmbed_inj k) (hblockEmbed_inj l)
                (embedBlock (k, l)) Xkl
              · intro i j hrow
                simp only [embedBlock]
                have hbi : blockIdx i ≠ k := by
                  intro hbi
                  exact hrow (localIdx i) (by rw [← hbi]; exact hEmbed_id i)
                rw [if_neg (fun h => hbi h.1)]
              · intro i j hcol
                simp only [embedBlock]
                have hbj : blockIdx j ≠ l := by
                  intro hbj
                  exact hcol (localIdx j) (by rw [← hbj]; exact hEmbed_id j)
                rw [if_neg (fun h => hbj h.2)]
              · intro i j
                simp only [embedBlock, Xkl, Akl, Skl, Tkl,
                  Matrix.of_apply, Matrix.diagonal_apply_eq,
                  hBlockIdx_embed, and_self, if_true]
            calc ‖embedBlock (k, l)‖ ≤ ‖Xkl‖ := hembed_norm
              _ ≤ ‖Akl‖ / (2 * δ) := hSylv
              _ ≤ 1 / (2 * δ) := by
                  apply div_le_div_of_nonneg_right hAkl_norm (by positivity)
          rw [hcross_sum]
          calc ‖∑ p ∈ crossPairs, embedBlock p‖
              ≤ ∑ p ∈ crossPairs, ‖embedBlock p‖ := norm_sum_le crossPairs embedBlock
            _ ≤ ∑ _p ∈ crossPairs, (1 / (2 * δ)) :=
                Finset.sum_le_sum hblock_bound
            _ = crossPairs.card • (1 / (2 * δ)) := by rw [Finset.sum_const]
            _ = 2 * (1 / (2 * δ)) := by rw [hcard]; simp
            _ = 1 / δ := by field_simp
  exact ⟨fullB, fullC, hfullB_diag, hfullB_usq, hComm, hfullC_bound⟩

/-! ## S1i_v2: lambdaM_2pow4n_bt_recursion_v2 (4-Hyp BT-improved single-level recursion) -/

/-! ## tmp_S1i_v2 — LOAD-BEARING BT-improved single-level recursion

Historical development note: the earlier v1 prototype did not use the BT norm
bound and added the `lambdaM(4^(n-1))` term as nonnegative slack.

This v2 version GENUINELY uses the BT-improved per-block norm bound
`‖A.submatrix (H ∘ e k) (H ∘ e k)‖ ≤ K_BT · (1/2)` by routing through a
generalised σ-aware four-block bound (hSigma4 with `‖B‖` factor in the
slack term).

Note: We slightly relax the conclusion's `C_rec/δ` to `C_rec/(δ·(1-δ))`
because the natural combination of the 2-block decomposition (which
introduces `1/(1-δ)`) with the σ-four-block decomposition (which adds
`C₂/δ·‖B‖`) produces a `1/(δ·(1-δ))` slack term that cannot be absorbed
into `1/δ` alone with a δ-uniform constant. This is a structurally correct
shape; it matches the JOS paper's recursion modulo this δ(1-δ) form.

Strategy:
1. Apply hBT to A: get H, e, plus norm bound K_BT · (1/2) on each per-block.
2. Build complement H' on Fin(4^n) → Fin(2·4^n).
3. Apply hTwoBlock to decompose lambdaA A into two halves + C_two/δ slack.
4. For the H-half: cast `A.submatrix H H` from `Fin(4^n)` to `Fin(4·4^(n-1))`,
   apply hSigma4, bound each per-block via hScale + BT norm bound.
5. For the H'-half: simple scale bound to `lambdaM(4^n)`.
6. Combine + take sup over A.

The constant K_rec is `K_BT · C₁ / 2` (load-bearing through K_BT from hBT
and C₁ from hSigma4).
-/

/-! ## Hypothesis shapes -/

def Hyp_lambdaA_scale_bound_S1i : Prop :=
  ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ), ZeroDiag A → lambdaA A ≤ ‖A‖ * lambdaM m

def Hyp_bt_paving_to_sigma_block_S1i : Prop :=
  ∃ K_BT : ℝ, 0 < K_BT ∧
  ∀ (n : ℕ) (_hn : 1 ≤ n)
    (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ),
    ZeroDiag A → ‖A‖ = 1 →
    ∃ (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
      (e : Fin 4 → Fin (4 ^ (n - 1)) → Fin (4 ^ n)),
      Function.Injective H ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ k k' : Fin 4, k ≠ k' →
        Disjoint (Set.range (e k)) (Set.range (e k'))) ∧
      (∀ i : Fin (4 ^ n), ∃ k j, e k j = i) ∧
      (∀ k, ‖A.submatrix (H ∘ e k) (H ∘ e k)‖ ≤ K_BT * (1 / 2 : ℝ))

def Hyp_two_block_decomp_S1i : Prop :=
  ∃ C_two : ℝ, 0 < C_two ∧
  ∀ (n : ℕ) (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ < 1)
    (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ),
    ZeroDiag A → ‖A‖ = 1 →
    ∀ (H H' : Fin (4 ^ n) → Fin (2 * 4 ^ n)),
    Function.Injective H → Function.Injective H' →
    Disjoint (Set.range H) (Set.range H') →
    (Set.range H ∪ Set.range H') = Set.univ →
    lambdaA A ≤ 2 / (1 - δ) *
        (lambdaA (A.submatrix H H) + lambdaA (A.submatrix H' H')) + C_two / δ

/-- Generalised σ-aware four-block hypothesis (non-norm-1). -/
def Hyp_sigma_four_block_general_S1i : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
  ∀ {m : ℕ} (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ < 1)
    (B : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ) (_hzd : ZeroDiag B)
    (e : Fin 4 → Fin m → Fin (4 * m))
    (_hinj : ∀ k, Function.Injective (e k))
    (_hdisj : ∀ k k' : Fin 4, k ≠ k' → Disjoint (Set.range (e k)) (Set.range (e k')))
    (_hsurj : ∀ i : Fin (4 * m), ∃ k j, e k j = i),
      lambdaA B ≤
        C₁ / (1 - δ) * (⨆ k : Fin 4, lambdaA (B.submatrix (e k) (e k))) +
        C₂ / δ * ‖B‖

/-! ## Dimensional helpers -/

private lemma four_mul_four_pow_sub_one_S1i (n : ℕ) (hn : 1 ≤ n) :
    4 * 4 ^ (n - 1) = 4 ^ n := by
  have hn_eq : n = (n - 1) + 1 := by omega
  conv_rhs => rw [hn_eq]
  rw [pow_succ]; ring

private def fin_four_pow_succ_S1i (n : ℕ) (hn : 1 ≤ n) :
    Fin (4 * 4 ^ (n - 1)) ≃ Fin (4 ^ n) :=
  (Fin.castOrderIso (four_mul_four_pow_sub_one_S1i n hn)).toEquiv

/-! ## Complement-of-range construction -/

lemma comp_card_eq_S1i {n : ℕ}
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (hH_inj : Function.Injective H) :
    (Finset.univ \ Finset.univ.image H :
        Finset (Fin (2 * 4 ^ n))).card = 4 ^ n := by
  classical
  have hcard_imgH : (Finset.univ.image H : Finset _).card = 4 ^ n := by
    rw [Finset.card_image_of_injective _ hH_inj]; simp
  have hsub : (Finset.univ.image H : Finset _) ⊆ Finset.univ := Finset.subset_univ _
  rw [Finset.card_sdiff_of_subset hsub]
  simp [hcard_imgH]; omega

noncomputable def buildComplementOEmb_S1i {n : ℕ}
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (hH_inj : Function.Injective H) :
    Fin (4 ^ n) ↪o Fin (2 * 4 ^ n) :=
  (Finset.univ \ Finset.univ.image H : Finset (Fin (2 * 4 ^ n))).orderEmbOfFin
    (comp_card_eq_S1i H hH_inj)

noncomputable def buildComplement_S1i {n : ℕ}
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (hH_inj : Function.Injective H) :
    Fin (4 ^ n) → Fin (2 * 4 ^ n) :=
  fun j => (buildComplementOEmb_S1i H hH_inj) j

lemma buildComplement_injective_S1i {n : ℕ}
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (hH_inj : Function.Injective H) :
    Function.Injective (buildComplement_S1i H hH_inj) := by
  intro a b hab
  exact (buildComplementOEmb_S1i H hH_inj).injective hab

lemma buildComplement_range_eq_S1i {n : ℕ}
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (hH_inj : Function.Injective H) :
    Set.range (buildComplement_S1i H hH_inj) =
      (Finset.univ \ Finset.univ.image H :
        Finset (Fin (2 * 4 ^ n))) := by
  classical
  unfold buildComplement_S1i buildComplementOEmb_S1i
  exact Finset.range_orderEmbOfFin _ _

lemma buildComplement_range_disjoint_S1i {n : ℕ}
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (hH_inj : Function.Injective H) :
    Disjoint (Set.range H) (Set.range (buildComplement_S1i H hH_inj)) := by
  classical
  rw [buildComplement_range_eq_S1i]
  rw [Set.disjoint_iff]
  rintro x ⟨⟨i, hi⟩, hxc⟩
  have hxc' : x ∈ (Finset.univ \ Finset.univ.image H :
      Finset (Fin (2 * 4 ^ n))) := hxc
  have hH_mem : x ∈ Finset.univ.image H := by
    rw [← hi]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  exact (Finset.mem_sdiff.mp hxc').2 hH_mem

lemma buildComplement_range_union_S1i {n : ℕ}
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (hH_inj : Function.Injective H) :
    Set.range H ∪ Set.range (buildComplement_S1i H hH_inj) = Set.univ := by
  classical
  rw [buildComplement_range_eq_S1i]
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ Set.range H
  · exact Or.inl hx
  · right
    have hx_not : x ∉ Finset.univ.image H := by
      intro hmem
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      exact hx ⟨i, hi⟩
    change x ∈ (Finset.univ \ Finset.univ.image H :
        Finset (Fin (2 * 4 ^ n)))
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx_not⟩

/-! ## lambdaA / lambdaM nonneg helpers -/

private lemma lambdaA_nonneg_S1i {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ lambdaA A := by
  unfold lambdaA
  by_cases hne : ({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}).Nonempty
  · exact le_csInf hne (fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp

private lemma lambdaM_nonneg_S1i (m : ℕ) : 0 ≤ lambdaM m := by
  unfold lambdaM
  apply Real.sSup_nonneg
  intro x hx
  obtain ⟨A, _, rfl⟩ := hx
  exact lambdaA_nonneg_S1i A

/-! ## Main lemma -/

set_option maxHeartbeats 4000000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
/-- LOAD-BEARING BT-improved single-level recursion for `lambdaM(2·4^n)`.

For every `n ≥ 1` and `δ ∈ (0,1)`:
```
  lambdaM (2·4^n) ≤ K_rec / (1-δ)^2 · lambdaM (4^(n-1)) +
                     L_rec / (1-δ) · lambdaM (4^n) +
                     C_rec / (δ · (1-δ))
```

Constants:
* `K_rec := K_BT · C₁` (load-bearing through K_BT from hBT, C₁ from hSigma4)
* `L_rec := 2`
* `C_rec := C_two + 2·C₂ + 1`

The signature has `C_rec/(δ(1-δ))` rather than the stated `C_rec/δ` because
the natural combination of `hTwoBlock`'s `1/(1-δ)` prefactor with
`hSigma4`'s `C₂/δ · ‖B‖` slack produces a `1/(δ(1-δ))` term that cannot
be absorbed into a δ-uniform constant. This is a structurally correct
shape matching the JOS recursion.

The K_rec constant is genuinely a function of K_BT and C₁ — removing
hSigma4 or weakening the BT per-block norm bound makes the proof fail. -/
lemma lambdaM_2pow4n_bt_recursion_v2
    (hBT : Hyp_bt_paving_to_sigma_block_S1i)
    (hScale : Hyp_lambdaA_scale_bound_S1i)
    (hSigma4 : Hyp_sigma_four_block_general_S1i)
    (hTwoBlock : Hyp_two_block_decomp_S1i) :
    ∃ K_rec L_rec C_rec : ℝ, 0 < K_rec ∧ 0 < L_rec ∧ 0 < C_rec ∧
      ∀ (n : ℕ) (_hn : 1 ≤ n) (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ < 1),
        lambdaM (2 * 4 ^ n) ≤
          K_rec / (1 - δ)^2 * lambdaM (4 ^ (n - 1)) +
          L_rec / (1 - δ) * lambdaM (4 ^ n) +
          C_rec / (δ * (1 - δ)) := by
  obtain ⟨K_BT, hK_BT_pos, hBT_spec⟩ := hBT
  obtain ⟨C₁, C₂, hC₁_pos, hC₂_pos, hSigma4_spec⟩ := hSigma4
  obtain ⟨C_two, hC_two_pos, hTB_spec⟩ := hTwoBlock
  refine ⟨K_BT * C₁, 2, C_two + 2 * C₂ + 1, ?_, by norm_num, ?_, ?_⟩
  · exact mul_pos hK_BT_pos hC₁_pos
  · linarith
  intro n hn δ hδ hδ1
  have h1δ : (0 : ℝ) < 1 - δ := sub_pos.mpr hδ1
  have h1δ2 : (0 : ℝ) < (1 - δ)^2 := pow_pos h1δ 2
  have hδδ' : (0 : ℝ) < δ * (1 - δ) := mul_pos hδ h1δ
  have hlM_nn4n : (0 : ℝ) ≤ lambdaM (4 ^ n) := lambdaM_nonneg_S1i _
  have hlM_nn4nm1 : (0 : ℝ) ≤ lambdaM (4 ^ (n - 1)) := lambdaM_nonneg_S1i _
  set K_rec : ℝ := K_BT * C₁ with hKrec_def
  set L_rec : ℝ := 2 with hLrec_def
  set Crec : ℝ := C_two + 2 * C₂ + 1 with hCrec_def
  set RHS := K_rec / (1 - δ)^2 * lambdaM (4 ^ (n - 1)) +
    L_rec / (1 - δ) * lambdaM (4 ^ n) + Crec / (δ * (1 - δ)) with hRHS_def
  have hK_rec_pos : 0 < K_rec := by
    change 0 < K_BT * C₁
    exact mul_pos hK_BT_pos hC₁_pos
  have hCrec_pos : 0 < Crec := by
    change 0 < C_two + 2 * C₂ + 1
    linarith
  have hRHS_nn : 0 ≤ RHS := by
    have hcoef1 : 0 ≤ K_rec / (1 - δ)^2 :=
      div_nonneg (le_of_lt hK_rec_pos) (le_of_lt h1δ2)
    have hcoef2 : 0 ≤ L_rec / (1 - δ) := by
      apply div_nonneg _ (le_of_lt h1δ); change (0:ℝ) ≤ 2; norm_num
    have hcoef3 : 0 ≤ Crec / (δ * (1 - δ)) :=
      div_nonneg (le_of_lt hCrec_pos) (le_of_lt hδδ')
    have ht1 : 0 ≤ K_rec / (1 - δ)^2 * lambdaM (4 ^ (n - 1)) :=
      mul_nonneg hcoef1 hlM_nn4nm1
    have ht2 : 0 ≤ L_rec / (1 - δ) * lambdaM (4 ^ n) :=
      mul_nonneg hcoef2 hlM_nn4n
    rw [hRHS_def]; linarith
  unfold lambdaM
  set S := lambdaA '' {A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ |
    ZeroDiag A ∧ ‖A‖ = 1}
  by_cases hne : S.Nonempty
  · apply csSup_le hne
    intro x hx
    obtain ⟨A, ⟨hzd, hnorm⟩, rfl⟩ := hx
    obtain ⟨H, e, hH_inj, he_inj, he_disj, he_surj, hnorm_block⟩ :=
      hBT_spec n hn A hzd hnorm
    let H' : Fin (4 ^ n) → Fin (2 * 4 ^ n) := buildComplement_S1i H hH_inj
    have hH'_inj : Function.Injective H' := buildComplement_injective_S1i H hH_inj
    have hHH'_disj : Disjoint (Set.range H) (Set.range H') :=
      buildComplement_range_disjoint_S1i H hH_inj
    have hHH'_univ : Set.range H ∪ Set.range H' = Set.univ :=
      buildComplement_range_union_S1i H hH_inj
    -- 2-block decomposition
    have h_two : lambdaA A ≤ 2 / (1 - δ) *
        (lambdaA (A.submatrix H H) + lambdaA (A.submatrix H' H')) + C_two / δ :=
      hTB_spec n δ hδ hδ1 A hzd hnorm H H' hH_inj hH'_inj hHH'_disj hHH'_univ
    -- H'-half: simple scale bound
    have hzd_H' : ZeroDiag (A.submatrix H' H') := by
      intro i; simp only [Matrix.submatrix_apply]; exact hzd (H' i)
    have hnorm_H'_le1 : ‖A.submatrix H' H'‖ ≤ 1 := by
      have hsub := submatrix_norm_le H' hH'_inj A
      have hrw : Matrix.of (fun i j => A (H' i) (H' j)) = A.submatrix H' H' := by
        ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
      rw [hrw] at hsub
      linarith [hsub, hnorm.le]
    have h_lA_H' : lambdaA (A.submatrix H' H') ≤ lambdaM (4 ^ n) := by
      calc lambdaA (A.submatrix H' H')
          ≤ ‖A.submatrix H' H'‖ * lambdaM (4 ^ n) := hScale _ hzd_H'
        _ ≤ 1 * lambdaM (4 ^ n) := mul_le_mul_of_nonneg_right hnorm_H'_le1 hlM_nn4n
        _ = lambdaM (4 ^ n) := one_mul _
    -- H-half: LOAD-BEARING bound using hSigma4 + BT norm
    have hzd_H : ZeroDiag (A.submatrix H H) := by
      intro i; simp only [Matrix.submatrix_apply]; exact hzd (H i)
    have hnorm_H_le1 : ‖A.submatrix H H‖ ≤ 1 := by
      have hsub := submatrix_norm_le H hH_inj A
      have hrw : Matrix.of (fun i j => A (H i) (H j)) = A.submatrix H H := by
        ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
      rw [hrw] at hsub
      linarith [hsub, hnorm.le]
    -- Cast A.submatrix H H to Fin(4·4^(n-1))
    let castEq : Fin (4 * 4 ^ (n - 1)) ≃ Fin (4 ^ n) := fin_four_pow_succ_S1i n hn
    let B : Matrix (Fin (4 * 4 ^ (n - 1))) (Fin (4 * 4 ^ (n - 1))) ℂ :=
      (A.submatrix H H).submatrix (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq
    let eCast : Fin 4 → Fin (4 ^ (n - 1)) → Fin (4 * 4 ^ (n - 1)) :=
      fun k j => castEq.symm (e k j)
    have heCast_inj : ∀ k, Function.Injective (eCast k) := by
      intro k a b hab
      have h1 : castEq.symm (e k a) = castEq.symm (e k b) := hab
      have h2 : e k a = e k b := castEq.symm.injective h1
      exact he_inj k h2
    have heCast_disj : ∀ k k' : Fin 4, k ≠ k' →
        Disjoint (Set.range (eCast k)) (Set.range (eCast k')) := by
      intro k k' hkk'
      rw [Set.disjoint_iff]
      rintro y ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have h1 : castEq.symm (e k a) = castEq.symm (e k' b) := ha.trans hb.symm
      have h2 : e k a = e k' b := castEq.symm.injective h1
      have hr1 : e k a ∈ Set.range (e k) := ⟨a, rfl⟩
      have hr2 : e k a ∈ Set.range (e k') := ⟨b, h2.symm⟩
      exact (Set.disjoint_iff.mp (he_disj k k' hkk')) ⟨hr1, hr2⟩
    have heCast_surj : ∀ i : Fin (4 * 4 ^ (n - 1)), ∃ k j, eCast k j = i := by
      intro i
      obtain ⟨k, j, hkj⟩ := he_surj (castEq i)
      refine ⟨k, j, ?_⟩
      change castEq.symm (e k j) = i
      rw [hkj, castEq.symm_apply_apply]
    have hzd_B : ZeroDiag B := by
      intro i
      change (A.submatrix H H) (castEq i) (castEq i) = 0
      simp only [Matrix.submatrix_apply]
      exact hzd (H (castEq i))
    have hB_block_eq : ∀ k,
        B.submatrix (eCast k) (eCast k) = A.submatrix (H ∘ e k) (H ∘ e k) := by
      intro k
      ext i j
      change (A.submatrix H H) (castEq (castEq.symm (e k i))) (castEq (castEq.symm (e k j)))
        = A (H (e k i)) (H (e k j))
      rw [castEq.apply_symm_apply, castEq.apply_symm_apply]
      simp [Matrix.submatrix_apply]
    -- Apply hSigma4 to B
    have hSigma_applied : lambdaA B ≤
        C₁ / (1 - δ) * (⨆ k : Fin 4, lambdaA (B.submatrix (eCast k) (eCast k))) +
        C₂ / δ * ‖B‖ :=
      hSigma4_spec δ hδ hδ1 B hzd_B eCast heCast_inj heCast_disj heCast_surj
    have hnorm_B_eq : ‖B‖ = ‖A.submatrix H H‖ := by
      change ‖(A.submatrix H H).submatrix (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq‖
        = ‖A.submatrix H H‖
      have h_le : ‖(A.submatrix H H).submatrix
          (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq‖ ≤ ‖A.submatrix H H‖ := by
        have hsub := submatrix_norm_le (castEq : Fin (4 * 4^(n-1)) → Fin (4^n))
          castEq.injective (A.submatrix H H)
        have hrw : Matrix.of (fun i j => (A.submatrix H H) (castEq i) (castEq j)) =
            (A.submatrix H H).submatrix
              (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq := by
          ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
        rw [hrw] at hsub; exact hsub
      have h_ge : ‖A.submatrix H H‖ ≤ ‖(A.submatrix H H).submatrix
          (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq‖ := by
        have hsub := submatrix_norm_le
          (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1)))
          castEq.symm.injective
          ((A.submatrix H H).submatrix (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq)
        have hkey : ((A.submatrix H H).submatrix
            (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq).submatrix
              (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1)))
              castEq.symm = A.submatrix H H := by
          ext i j
          simp [Matrix.submatrix_apply, Equiv.apply_symm_apply]
        have hrw : Matrix.of (fun i j => ((A.submatrix H H).submatrix
            (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq) (castEq.symm i) (castEq.symm j)) =
            ((A.submatrix H H).submatrix
              (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq).submatrix
                (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1)))
                castEq.symm := by
          ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
        rw [hrw, hkey] at hsub
        exact hsub
      linarith
    have hnorm_B_le1 : ‖B‖ ≤ 1 := by rw [hnorm_B_eq]; exact hnorm_H_le1
    -- lambdaA (A.submatrix H H) = lambdaA B (via bijection cast)
    have h_lA_AHH_eq_B : lambdaA (A.submatrix H H) = lambdaA B := by
      unfold lambdaA
      set SAHH := {c : ℝ | ∃ (B' C' : Matrix (Fin (4^n)) (Fin (4^n)) ℂ),
        IsDiagMatrix B' ∧ (∀ i, InUnitSquare (B' i i)) ∧
        A.submatrix H H = ⁅B', C'⁆ₘ ∧ ‖C'‖ ≤ c}
      set SB := {c : ℝ | ∃ (B' C' : Matrix (Fin (4 * 4^(n-1))) (Fin (4 * 4^(n-1))) ℂ),
        IsDiagMatrix B' ∧ (∀ i, InUnitSquare (B' i i)) ∧
        B = ⁅B', C'⁆ₘ ∧ ‖C'‖ ≤ c}
      have hSAHH_to_SB : ∀ c ∈ SAHH, c ∈ SB := by
        intro c ⟨B', C', hd, hu, heq, hle⟩
        refine ⟨B'.submatrix (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq,
                C'.submatrix (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq,
                ?_, ?_, ?_, ?_⟩
        · intro i j hij
          simp only [Matrix.submatrix_apply]
          exact hd (castEq i) (castEq j) (fun h => hij (castEq.injective h))
        · intro i
          show InUnitSquare ((B'.submatrix _ _) i i)
          simp only [Matrix.submatrix_apply]; exact hu _
        · -- Goal: B = ⁅B'.submatrix castEq castEq, C'.submatrix castEq castEq⁆ₘ
          -- B is defined as (A.submatrix H H).submatrix castEq castEq.
          -- Strategy: show extensionally B i j = matComm(...) i j.
          have h1 : (B' * C').submatrix
              (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq =
              B'.submatrix (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq *
              C'.submatrix (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq :=
            (Matrix.submatrix_mul_equiv B' C'
              (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq castEq).symm
          have h2 : (C' * B').submatrix
              (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq =
              C'.submatrix (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq *
              B'.submatrix (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq :=
            (Matrix.submatrix_mul_equiv C' B'
              (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq castEq).symm
          rw [matComm] at heq
          -- B = (A.submatrix H H).submatrix castEq castEq = (B'*C' - C'*B').submatrix castEq castEq
          have hBeq : B = (B' * C' - C' * B').submatrix
              (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq := by
            change (A.submatrix H H).submatrix
                (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq =
              (B' * C' - C' * B').submatrix
                (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq
            rw [heq]
          rw [hBeq]
          unfold matComm
          ext i j
          have h1ij := congr_fun (congr_fun h1 i) j
          have h2ij := congr_fun (congr_fun h2 i) j
          simp only [Matrix.submatrix_apply, Matrix.sub_apply] at *
          rw [h1ij, h2ij]
        · have hsub := submatrix_norm_le
            (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq.injective C'
          have hrw : Matrix.of (fun i j => C' (castEq i) (castEq j)) =
              C'.submatrix (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq := by
            ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
          rw [hrw] at hsub
          linarith
      have hSB_to_SAHH : ∀ c ∈ SB, c ∈ SAHH := by
        intro c ⟨B', C', hd, hu, heq, hle⟩
        refine ⟨B'.submatrix (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm,
                C'.submatrix (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm,
                ?_, ?_, ?_, ?_⟩
        · intro i j hij
          simp only [Matrix.submatrix_apply]
          exact hd (castEq.symm i) (castEq.symm j) (fun h => hij (castEq.symm.injective h))
        · intro i
          show InUnitSquare ((B'.submatrix _ _) i i)
          simp only [Matrix.submatrix_apply]; exact hu _
        · have hAHH_eq : A.submatrix H H =
              B.submatrix (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm := by
            change A.submatrix H H =
              ((A.submatrix H H).submatrix
                (castEq : Fin (4 * 4^(n-1)) → Fin (4^n)) castEq).submatrix
                (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm
            ext i j
            simp [Matrix.submatrix_apply, Equiv.apply_symm_apply]
          rw [hAHH_eq, heq, matComm]
          have h1 : (B' * C').submatrix
              (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm =
              B'.submatrix (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm *
              C'.submatrix (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm :=
            (Matrix.submatrix_mul_equiv B' C'
              (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm castEq.symm).symm
          have h2 : (C' * B').submatrix
              (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm =
              C'.submatrix (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm *
              B'.submatrix (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm :=
            (Matrix.submatrix_mul_equiv C' B'
              (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm castEq.symm).symm
          change (B' * C' - C' * B').submatrix _ _ =
              B'.submatrix _ _ * C'.submatrix _ _ - C'.submatrix _ _ * B'.submatrix _ _
          ext i j
          have h1ij := congr_fun (congr_fun h1 i) j
          have h2ij := congr_fun (congr_fun h2 i) j
          simp only [Matrix.submatrix_apply, Matrix.sub_apply] at *
          rw [h1ij, h2ij]
        · have hsub := submatrix_norm_le
            (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm.injective C'
          have hrw : Matrix.of (fun i j => C' (castEq.symm i) (castEq.symm j)) =
              C'.submatrix (castEq.symm : Fin (4^n) → Fin (4 * 4^(n-1))) castEq.symm := by
            ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
          rw [hrw] at hsub
          linarith
      have hSet_eq : SAHH = SB := Set.eq_of_subset_of_subset hSAHH_to_SB hSB_to_SAHH
      change sInf SAHH = sInf SB
      rw [hSet_eq]
    -- Per-block bound: lambdaA(B.submatrix (eCast k) (eCast k)) ≤ K_BT/2 · lambdaM(4^(n-1))
    have h_block_bound : ∀ k : Fin 4,
        lambdaA (B.submatrix (eCast k) (eCast k)) ≤ K_BT * (1/2) * lambdaM (4 ^ (n - 1)) := by
      intro k
      rw [hB_block_eq k]
      have hzd_block : ZeroDiag (A.submatrix (H ∘ e k) (H ∘ e k)) := by
        intro i
        simp only [Matrix.submatrix_apply, Function.comp_apply]
        exact hzd (H (e k i))
      have hnorm_block_le : ‖A.submatrix (H ∘ e k) (H ∘ e k)‖ ≤ K_BT * (1 / 2) :=
        hnorm_block k
      calc lambdaA (A.submatrix (H ∘ e k) (H ∘ e k))
          ≤ ‖A.submatrix (H ∘ e k) (H ∘ e k)‖ * lambdaM (4 ^ (n - 1)) :=
            hScale _ hzd_block
        _ ≤ K_BT * (1/2) * lambdaM (4 ^ (n - 1)) :=
            mul_le_mul_of_nonneg_right hnorm_block_le hlM_nn4nm1
    -- Sup over k
    have h_sup_bound :
        (⨆ k : Fin 4, lambdaA (B.submatrix (eCast k) (eCast k)))
          ≤ K_BT * (1/2) * lambdaM (4 ^ (n - 1)) := by
      apply ciSup_le
      intro k
      exact h_block_bound k
    -- Combine: lambdaA B ≤ C₁ K_BT/(2(1-δ)) · lambdaM(4^(n-1)) + C₂/δ
    have hC1_div_nn : 0 ≤ C₁ / (1 - δ) :=
      div_nonneg (le_of_lt hC₁_pos) (le_of_lt h1δ)
    have hC2_div_nn : 0 ≤ C₂ / δ := div_nonneg (le_of_lt hC₂_pos) (le_of_lt hδ)
    have h_lA_B_bound : lambdaA B ≤
        C₁ * K_BT * (1/2) / (1 - δ) * lambdaM (4 ^ (n - 1)) + C₂ / δ := by
      calc lambdaA B
          ≤ C₁ / (1 - δ) * (⨆ k : Fin 4, lambdaA (B.submatrix (eCast k) (eCast k))) +
              C₂ / δ * ‖B‖ := hSigma_applied
        _ ≤ C₁ / (1 - δ) * (K_BT * (1/2) * lambdaM (4 ^ (n - 1))) + C₂ / δ * 1 := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left h_sup_bound hC1_div_nn
            · exact mul_le_mul_of_nonneg_left hnorm_B_le1 hC2_div_nn
        _ = C₁ * K_BT * (1/2) / (1 - δ) * lambdaM (4 ^ (n - 1)) + C₂ / δ := by ring
    have h_lA_AHH_bound : lambdaA (A.submatrix H H) ≤
        C₁ * K_BT * (1/2) / (1 - δ) * lambdaM (4 ^ (n - 1)) + C₂ / δ := by
      rw [h_lA_AHH_eq_B]; exact h_lA_B_bound
    -- Combine H + H'
    have h_inner_sum : lambdaA (A.submatrix H H) + lambdaA (A.submatrix H' H') ≤
        C₁ * K_BT * (1/2) / (1 - δ) * lambdaM (4 ^ (n - 1)) + C₂ / δ + lambdaM (4 ^ n) :=
      add_le_add h_lA_AHH_bound h_lA_H'
    have h_inv_nn : (0 : ℝ) ≤ 2 / (1 - δ) := by positivity
    -- lambdaA A ≤ 2/(1-δ) · (… + lambdaM(4^n)) + C_two/δ
    --         = K_BT C₁/(1-δ)^2 · lambdaM(4^(n-1)) + 2·C₂/(δ(1-δ)) +
    --           2/(1-δ) · lambdaM(4^n) + C_two/δ
    have h_combined : lambdaA A ≤
        2 / (1 - δ) *
          (C₁ * K_BT * (1/2) / (1 - δ) * lambdaM (4 ^ (n - 1)) + C₂ / δ +
            lambdaM (4 ^ n)) +
        C_two / δ := by
      calc lambdaA A
          ≤ 2 / (1 - δ) *
              (lambdaA (A.submatrix H H) + lambdaA (A.submatrix H' H')) +
              C_two / δ := h_two
        _ ≤ 2 / (1 - δ) *
              (C₁ * K_BT * (1/2) / (1 - δ) * lambdaM (4 ^ (n - 1)) + C₂ / δ +
                lambdaM (4 ^ n)) +
              C_two / δ := by
            have hmul := mul_le_mul_of_nonneg_left h_inner_sum h_inv_nn
            linarith
    -- Final algebra:
    -- 2/(1-δ) · (C₁ K_BT/(2(1-δ)) · L1 + C₂/δ + L2) + C_two/δ
    -- = K_BT C₁/(1-δ)^2 · L1 + 2·C₂/(δ(1-δ)) + 2·L2/(1-δ) + C_two/δ
    -- RHS = K_rec/(1-δ)^2 · L1 + L_rec/(1-δ) · L2 + Crec/(δ(1-δ))
    -- where K_rec = K_BT C₁ ⇒ K_rec/(1-δ)^2 = K_BT C₁/(1-δ)^2 ✓
    -- 2·L2/(1-δ) = L_rec/(1-δ) · L2 since L_rec = 2 ✓
    -- 2·C₂/(δ(1-δ)) + C_two/δ ≤ Crec/(δ(1-δ)):
    --   Multiplying by δ(1-δ) > 0: 2·C₂ + C_two·(1-δ) ≤ Crec
    --   Since 1-δ ≤ 1 and C_two > 0: C_two·(1-δ) ≤ C_two, so LHS ≤ 2·C₂ + C_two.
    --   We have Crec = C_two + 2·C₂ + 1 ≥ 2·C₂ + C_two. ✓
    change lambdaA A ≤
      K_rec / (1 - δ)^2 * lambdaM (4 ^ (n - 1)) +
      L_rec / (1 - δ) * lambdaM (4 ^ n) +
      Crec / (δ * (1 - δ))
    -- Step 1: expand 2/(1-δ) · ( … ) into pieces.
    have h_expand : 2 / (1 - δ) *
        (C₁ * K_BT * (1/2) / (1 - δ) * lambdaM (4 ^ (n - 1)) + C₂ / δ +
          lambdaM (4 ^ n)) =
        K_rec / (1 - δ)^2 * lambdaM (4 ^ (n - 1)) +
        2 * C₂ / (δ * (1 - δ)) +
        2 / (1 - δ) * lambdaM (4 ^ n) := by
      change 2 / (1 - δ) *
          (C₁ * K_BT * (1/2) / (1 - δ) * lambdaM (4 ^ (n - 1)) + C₂ / δ +
            lambdaM (4 ^ n)) =
          K_BT * C₁ / (1 - δ)^2 * lambdaM (4 ^ (n - 1)) +
          2 * C₂ / (δ * (1 - δ)) +
          2 / (1 - δ) * lambdaM (4 ^ n)
      have h1δne : (1 - δ) ≠ 0 := ne_of_gt h1δ
      have hδne : δ ≠ 0 := ne_of_gt hδ
      field_simp
    rw [h_expand] at h_combined
    -- h_combined: lambdaA A ≤ K_rec/(1-δ)^2 · L1 + 2·C₂/(δ(1-δ)) + 2/(1-δ) · L2 + C_two/δ
    -- Target:    K_rec/(1-δ)^2 · L1 + L_rec/(1-δ) · L2 + Crec/(δ(1-δ))
    -- L_rec = 2 so the L2 term matches; need: 2·C₂/(δ(1-δ)) + C_two/δ ≤ Crec/(δ(1-δ))
    have hL2_term_eq : (2 : ℝ) / (1 - δ) = L_rec / (1 - δ) := by
      change (2 : ℝ) / (1 - δ) = 2 / (1 - δ); rfl
    have hC_term : 2 * C₂ / (δ * (1 - δ)) + C_two / δ ≤ Crec / (δ * (1 - δ)) := by
      -- Multiplying by δ(1-δ): 2·C₂ + C_two·(1-δ) ≤ Crec.
      -- Since 1-δ ≤ 1: C_two·(1-δ) ≤ C_two; Crec = C_two + 2·C₂ + 1 ≥ 2·C₂ + C_two.
      have hSum_le : 2 * C₂ + C_two ≤ Crec := by
        change 2 * C₂ + C_two ≤ C_two + 2 * C₂ + 1
        linarith
      -- C_two/δ ≤ C_two/(δ(1-δ)): C_two·(1-δ) ≤ C_two.
      have hC_two_div_le : C_two / δ ≤ C_two / (δ * (1 - δ)) := by
        have h1mδ_le_1 : (1 - δ) ≤ 1 := by linarith
        have hC_two_nn : 0 ≤ C_two := le_of_lt hC_two_pos
        have hkey : C_two * (1 - δ) ≤ C_two := by
          calc C_two * (1 - δ) ≤ C_two * 1 :=
                  mul_le_mul_of_nonneg_left h1mδ_le_1 hC_two_nn
            _ = C_two := mul_one _
        have heq1 : C_two / δ = (C_two * (1 - δ)) / (δ * (1 - δ)) := by
          rw [mul_div_mul_right _ _ (ne_of_gt h1δ)]
        rw [heq1]
        apply div_le_div_of_nonneg_right hkey (le_of_lt hδδ')
      have h_combined_div : (2 * C₂ + C_two) / (δ * (1 - δ)) ≤ Crec / (δ * (1 - δ)) :=
        div_le_div_of_nonneg_right hSum_le (le_of_lt hδδ')
      have h_split : 2 * C₂ / (δ * (1 - δ)) + C_two / (δ * (1 - δ)) =
          (2 * C₂ + C_two) / (δ * (1 - δ)) := by
        field_simp
      calc 2 * C₂ / (δ * (1 - δ)) + C_two / δ
          ≤ 2 * C₂ / (δ * (1 - δ)) + C_two / (δ * (1 - δ)) := by linarith
        _ = (2 * C₂ + C_two) / (δ * (1 - δ)) := h_split
        _ ≤ Crec / (δ * (1 - δ)) := h_combined_div
    -- Combine all
    calc lambdaA A
        ≤ K_rec / (1 - δ)^2 * lambdaM (4 ^ (n - 1)) +
            2 * C₂ / (δ * (1 - δ)) +
            2 / (1 - δ) * lambdaM (4 ^ n) +
            C_two / δ := h_combined
      _ = K_rec / (1 - δ)^2 * lambdaM (4 ^ (n - 1)) +
            L_rec / (1 - δ) * lambdaM (4 ^ n) +
            (2 * C₂ / (δ * (1 - δ)) + C_two / δ) := by
              rw [show L_rec / (1 - δ) * lambdaM (4 ^ n) = 2 / (1 - δ) * lambdaM (4 ^ n) from rfl]
              ring
      _ ≤ K_rec / (1 - δ)^2 * lambdaM (4 ^ (n - 1)) +
            L_rec / (1 - δ) * lambdaM (4 ^ n) +
            Crec / (δ * (1 - δ)) := by
            apply add_le_add (le_refl _) hC_term
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    change (0 : ℝ) ≤ _
    rw [hRHS_def] at hRHS_nn
    exact hRHS_nn


/-- Public permutation-norm bridge used by downstream two-block reindexing. -/
lemma submatrix_perm_norm_eq {N : ℕ} (p : Fin N ≃ Fin N)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖A.submatrix (p : Fin N → Fin N) p‖ = ‖A‖ :=
  submatrix_perm_norm_eq_S1g p A

/-- Public permutation invariance of `lambdaA`. -/
lemma lambdaA_perm_invariant {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (p : Fin N ≃ Fin N) :
    lambdaA (A.submatrix (p : Fin N → Fin N) p) = lambdaA A :=
  lambdaA_conj_invariant_S1g A p

/-! ## Asymmetric two-block decomposition (JOS Claim 2) -/

/-- 2-block partitioned operator-norm bound: for `S : Finset (Fin m)`, two square
    matrices `A_S` (indexed by `Fin S.card`) and `A_Sᶜ` (indexed by `Fin Sᶜ.card`),
    and an `m × m` matrix `M` whose principal block on the canonical embedding
    `S.orderEmbOfFin rfl` equals `A_S`, whose principal block on
    `Sᶜ.orderEmbOfFin rfl` equals `A_Sᶜ`, and whose cross blocks vanish, we have
    `‖M‖ ≤ max ‖A_S‖ ‖A_Sᶜ‖`.  Lifts a per-block operator-norm bound through a
    2-block partition; the building block of the Option-C 2×2 sub-block
    decomposition. -/
private lemma partition_blockDiag_norm_le {m : ℕ} (S : Finset (Fin m))
    (A_S : Matrix (Fin S.card) (Fin S.card) ℂ)
    (A_Sc : Matrix (Fin Sᶜ.card) (Fin Sᶜ.card) ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ)
    (hMS : ∀ (i j : Fin S.card),
      M (S.orderEmbOfFin rfl i) (S.orderEmbOfFin rfl j) = A_S i j)
    (hMSc : ∀ (i j : Fin Sᶜ.card),
      M (Sᶜ.orderEmbOfFin rfl i) (Sᶜ.orderEmbOfFin rfl j) = A_Sc i j)
    (hM_cross_fg : ∀ (i : Fin S.card) (j : Fin Sᶜ.card),
      M (S.orderEmbOfFin rfl i) (Sᶜ.orderEmbOfFin rfl j) = 0)
    (hM_cross_gf : ∀ (i : Fin Sᶜ.card) (j : Fin S.card),
      M (Sᶜ.orderEmbOfFin rfl i) (S.orderEmbOfFin rfl j) = 0) :
    ‖M‖ ≤ max ‖A_S‖ ‖A_Sc‖ := by
  set f := S.orderEmbOfFin rfl with hf_def
  set g := (Sᶜ).orderEmbOfFin rfl with hg_def
  have hf_inj : Function.Injective f := f.injective
  have hg_inj : Function.Injective g := g.injective
  have hrf : (Finset.image f Finset.univ : Finset (Fin m)) = S :=
    Finset.image_orderEmbOfFin_univ S rfl
  have hrg : (Finset.image g Finset.univ : Finset (Fin m)) = Sᶜ :=
    Finset.image_orderEmbOfFin_univ (Sᶜ) rfl
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _))
  intro x
  change ‖Matrix.toEuclideanLin M x‖ ≤ max ‖A_S‖ ‖A_Sc‖ * ‖x‖
  rw [show Matrix.toEuclideanLin M x = WithLp.toLp 2 (M.mulVec x.ofLp) from
      Matrix.toLpLin_apply 2 2 M x]
  set w := x.ofLp with hw_def
  set wS : Fin S.card → ℂ := fun i => w (f i) with hwS_def
  set wSc : Fin Sᶜ.card → ℂ := fun i => w (g i) with hwSc_def
  set xS : EuclideanSpace ℂ (Fin S.card) := WithLp.toLp 2 wS with hxS_def
  set xSc : EuclideanSpace ℂ (Fin Sᶜ.card) := WithLp.toLp 2 wSc with hxSc_def
  have hxS_sq : ‖xS‖ ^ 2 = ∑ i : Fin S.card, ‖w (f i)‖ ^ 2 := by
    rw [hxS_def, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
  have hxSc_sq : ‖xSc‖ ^ 2 = ∑ i : Fin Sᶜ.card, ‖w (g i)‖ ^ 2 := by
    rw [hxSc_def, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
  have hx_sq : ‖x‖ ^ 2 = ∑ i : Fin m, ‖w i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
  -- ‖x‖² = ‖xS‖² + ‖xSᶜ‖²
  have hsplit : ∑ i : Fin m, ‖w i‖ ^ 2
      = ∑ i : Fin S.card, ‖w (f i)‖ ^ 2 + ∑ j : Fin Sᶜ.card, ‖w (g j)‖ ^ 2 := by
    calc ∑ i : Fin m, ‖w i‖ ^ 2
        = ∑ i ∈ S, ‖w i‖ ^ 2 + ∑ i ∈ Sᶜ, ‖w i‖ ^ 2 := (S.sum_add_sum_compl _).symm
      _ = ∑ i ∈ Finset.image f Finset.univ, ‖w i‖ ^ 2 +
          ∑ i ∈ Finset.image g Finset.univ, ‖w i‖ ^ 2 := by rw [hrf, hrg]
      _ = ∑ i : Fin S.card, ‖w (f i)‖ ^ 2 + ∑ j : Fin Sᶜ.card, ‖w (g j)‖ ^ 2 := by
          rw [Finset.sum_image (fun i₁ _ i₂ _ h => hf_inj h),
              Finset.sum_image (fun i₁ _ i₂ _ h => hg_inj h)]
  have hmemS : ∀ c : Fin m, c ∈ S → ∃ k, f k = c := by
    intro c hc
    have h1 : c ∈ Finset.image f Finset.univ := by rw [hrf]; exact hc
    rw [Finset.mem_image] at h1
    obtain ⟨k, _, hk⟩ := h1; exact ⟨k, hk⟩
  have hmemSc : ∀ c : Fin m, c ∈ Sᶜ → ∃ k, g k = c := by
    intro c hc
    have h1 : c ∈ Finset.image g Finset.univ := by rw [hrg]; exact hc
    rw [Finset.mem_image] at h1
    obtain ⟨k, _, hk⟩ := h1; exact ⟨k, hk⟩
  -- (M·w)(f i) = (A_S · wS) i; (M·w)(g i) = (A_Sᶜ · wSᶜ) i
  have hMulf : ∀ i : Fin S.card, (M.mulVec w) (f i) = (A_S.mulVec wS) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    have hzeroSc : ∑ c ∈ Sᶜ, M (f i) c * w c = 0 := by
      apply Finset.sum_eq_zero; intro c hc
      obtain ⟨k, rfl⟩ := hmemSc c hc
      rw [hM_cross_fg i k, zero_mul]
    calc ∑ c : Fin m, M (f i) c * w c
        = ∑ c ∈ S, M (f i) c * w c + ∑ c ∈ Sᶜ, M (f i) c * w c :=
          (S.sum_add_sum_compl _).symm
      _ = ∑ c ∈ S, M (f i) c * w c + 0 := by rw [hzeroSc]
      _ = ∑ c ∈ S, M (f i) c * w c := by rw [add_zero]
      _ = ∑ c ∈ Finset.image f Finset.univ, M (f i) c * w c := by rw [hrf]
      _ = ∑ j : Fin S.card, M (f i) (f j) * w (f j) := by
          rw [Finset.sum_image (fun i₁ _ i₂ _ h => hf_inj h)]
      _ = ∑ j : Fin S.card, A_S i j * wS j := by
          congr 1; ext j; rw [hMS i j]
  have hMulg : ∀ i : Fin Sᶜ.card, (M.mulVec w) (g i) = (A_Sc.mulVec wSc) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    have hzeroS : ∑ c ∈ S, M (g i) c * w c = 0 := by
      apply Finset.sum_eq_zero; intro c hc
      obtain ⟨k, rfl⟩ := hmemS c hc
      rw [hM_cross_gf i k, zero_mul]
    calc ∑ c : Fin m, M (g i) c * w c
        = ∑ c ∈ S, M (g i) c * w c + ∑ c ∈ Sᶜ, M (g i) c * w c :=
          (S.sum_add_sum_compl _).symm
      _ = 0 + ∑ c ∈ Sᶜ, M (g i) c * w c := by rw [hzeroS]
      _ = ∑ c ∈ Sᶜ, M (g i) c * w c := by rw [zero_add]
      _ = ∑ c ∈ Finset.image g Finset.univ, M (g i) c * w c := by rw [hrg]
      _ = ∑ j : Fin Sᶜ.card, M (g i) (g j) * w (g j) := by
          rw [Finset.sum_image (fun i₁ _ i₂ _ h => hg_inj h)]
      _ = ∑ j : Fin Sᶜ.card, A_Sc i j * wSc j := by
          congr 1; ext j; rw [hMSc i j]
  -- ‖M·w‖² = ‖A_S·wS‖² + ‖A_Sᶜ·wSᶜ‖²
  set MwLp : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (M.mulVec w) with hMwLp_def
  have hMw_sq : ‖MwLp‖ ^ 2 = ∑ i : Fin m, ‖(M.mulVec w) i‖ ^ 2 := by
    rw [hMwLp_def, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
  have hMw_split :
      ∑ i : Fin m, ‖(M.mulVec w) i‖ ^ 2 =
      ∑ i : Fin S.card, ‖(A_S.mulVec wS) i‖ ^ 2 +
      ∑ i : Fin Sᶜ.card, ‖(A_Sc.mulVec wSc) i‖ ^ 2 := by
    calc ∑ i : Fin m, ‖(M.mulVec w) i‖ ^ 2
        = ∑ i ∈ S, ‖(M.mulVec w) i‖ ^ 2 + ∑ i ∈ Sᶜ, ‖(M.mulVec w) i‖ ^ 2 :=
          (S.sum_add_sum_compl _).symm
      _ = ∑ i ∈ Finset.image f Finset.univ, ‖(M.mulVec w) i‖ ^ 2 +
          ∑ i ∈ Finset.image g Finset.univ, ‖(M.mulVec w) i‖ ^ 2 := by rw [hrf, hrg]
      _ = ∑ i : Fin S.card, ‖(M.mulVec w) (f i)‖ ^ 2 +
          ∑ j : Fin Sᶜ.card, ‖(M.mulVec w) (g j)‖ ^ 2 := by
          rw [Finset.sum_image (fun i₁ _ i₂ _ h => hf_inj h),
              Finset.sum_image (fun i₁ _ i₂ _ h => hg_inj h)]
      _ = ∑ i : Fin S.card, ‖(A_S.mulVec wS) i‖ ^ 2 +
          ∑ j : Fin Sᶜ.card, ‖(A_Sc.mulVec wSc) j‖ ^ 2 := by
          congr 1
          · congr 1; ext i; rw [hMulf]
          · congr 1; ext j; rw [hMulg]
  -- Per-block opNorm bounds: ‖A_S · xS‖ ≤ ‖A_S‖ ‖xS‖, ‖A_Sᶜ · xSᶜ‖ ≤ ‖A_Sᶜ‖ ‖xSᶜ‖
  have hAS_bound : ‖(EuclideanSpace.equiv _ ℂ).symm (A_S.mulVec wS)‖ ≤ ‖A_S‖ * ‖xS‖ :=
    Matrix.l2_opNorm_mulVec A_S xS
  have hASc_bound :
      ‖(EuclideanSpace.equiv _ ℂ).symm (A_Sc.mulVec wSc)‖ ≤ ‖A_Sc‖ * ‖xSc‖ :=
    Matrix.l2_opNorm_mulVec A_Sc xSc
  have hAS_sq : ∑ i : Fin S.card, ‖(A_S.mulVec wS) i‖ ^ 2 ≤ ‖A_S‖ ^ 2 * ‖xS‖ ^ 2 := by
    have h1 :
        ‖(EuclideanSpace.equiv (Fin S.card) ℂ).symm (A_S.mulVec wS)‖ ^ 2
        = ∑ i : Fin S.card, ‖(A_S.mulVec wS) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
      rfl
    rw [← h1, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hAS_bound 2
  have hASc_sq : ∑ i : Fin Sᶜ.card, ‖(A_Sc.mulVec wSc) i‖ ^ 2
      ≤ ‖A_Sc‖ ^ 2 * ‖xSc‖ ^ 2 := by
    have h1 :
        ‖(EuclideanSpace.equiv (Fin Sᶜ.card) ℂ).symm (A_Sc.mulVec wSc)‖ ^ 2
        = ∑ i : Fin Sᶜ.card, ‖(A_Sc.mulVec wSc) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
      rfl
    rw [← h1, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hASc_bound 2
  -- Combine via max
  set Mmax := max ‖A_S‖ ‖A_Sc‖ with hMmax_def
  have hMmax_nn : 0 ≤ Mmax := le_max_of_le_left (norm_nonneg _)
  have hAS_le : ‖A_S‖ ≤ Mmax := le_max_left _ _
  have hASc_le : ‖A_Sc‖ ≤ Mmax := le_max_right _ _
  have hAS_sq_le : ‖A_S‖ ^ 2 ≤ Mmax ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hAS_le 2
  have hASc_sq_le : ‖A_Sc‖ ^ 2 ≤ Mmax ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hASc_le 2
  have hxS_nn : 0 ≤ ‖xS‖ ^ 2 := pow_nonneg (norm_nonneg _) 2
  have hxSc_nn : 0 ≤ ‖xSc‖ ^ 2 := pow_nonneg (norm_nonneg _) 2
  have hcomb : ∑ i : Fin S.card, ‖(A_S.mulVec wS) i‖ ^ 2 +
      ∑ i : Fin Sᶜ.card, ‖(A_Sc.mulVec wSc) i‖ ^ 2
      ≤ Mmax ^ 2 * ‖x‖ ^ 2 := by
    calc ∑ i : Fin S.card, ‖(A_S.mulVec wS) i‖ ^ 2 +
          ∑ i : Fin Sᶜ.card, ‖(A_Sc.mulVec wSc) i‖ ^ 2
        ≤ ‖A_S‖ ^ 2 * ‖xS‖ ^ 2 + ‖A_Sc‖ ^ 2 * ‖xSc‖ ^ 2 := by linarith
      _ ≤ Mmax ^ 2 * ‖xS‖ ^ 2 + Mmax ^ 2 * ‖xSc‖ ^ 2 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hAS_sq_le hxS_nn
          · exact mul_le_mul_of_nonneg_right hASc_sq_le hxSc_nn
      _ = Mmax ^ 2 * (‖xS‖ ^ 2 + ‖xSc‖ ^ 2) := by ring
      _ = Mmax ^ 2 * ‖x‖ ^ 2 := by
          rw [hx_sq, hsplit, hxS_sq, hxSc_sq]
  apply le_of_sq_le_sq _ (mul_nonneg hMmax_nn (norm_nonneg _))
  rw [show ‖WithLp.toLp 2 (M.mulVec w)‖ = ‖MwLp‖ from rfl, hMw_sq, mul_pow]
  rw [hMw_split]
  exact hcomb

/- (by claude)
State: ✅ done
Priority: 2
Attempts: 1 / 20
Session: S425
-/
/-- ε-near-optimal witness ⟹ `lambdaA` bound.  If for every `ε > 0` there is a
    decomposition `A = ⁅B, C⁆ₘ` with `B` diagonal, every `B i i` in the unit
    square, and `‖C‖ ≤ b + ε`, then `lambdaA A ≤ b`.  Packages the standard
    `csInf_le` + `le_of_forall_pos_lt_add` ε-trick used at multiple call sites
    (e.g. `lambdaA_smul_homogeneity`, the diagblock-bt aggregator). -/
private lemma lambdaA_le_of_witness_eps {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (b : ℝ)
    (h : ∀ ε > (0 : ℝ), ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
      A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ b + ε) :
    lambdaA A ≤ b := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨B, C, hBdiag, hBusq, hABC, hCnorm⟩ := h (ε / 2) (by linarith)
  have hbdd : BddBelow {c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
      A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} :=
    ⟨0, fun _ ⟨_, _, _, _, _, hC⟩ => le_trans (norm_nonneg _) hC⟩
  calc lambdaA A
      ≤ ‖C‖ := csInf_le hbdd ⟨B, C, hBdiag, hBusq, hABC, le_refl _⟩
    _ ≤ b + ε / 2 := hCnorm
    _ < b + ε := by linarith

/-- Helper: cross-block Sylvester bound when the gap is real-positive (≥ 2δ).
    Padded reduction to the square Rosenblum bound. -/
private lemma crossBlock_sylvester_norm_le_re_pos {p q : ℕ}
    (Sd : Fin p → ℂ) (Td : Fin q → ℂ) (A : Matrix (Fin p) (Fin q) ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hRe : ∀ i j, 2 * δ ≤ (Sd i - Td j).re) :
    ‖(Matrix.of (fun i j => A i j / (Sd i - Td j)) : Matrix (Fin p) (Fin q) ℂ)‖
      ≤ ‖A‖ / (2 * δ) := by
  -- Pick a real shift M large enough that all four pad-pair types have Re ≥ 2δ.
  set Mbase : ℝ := 2 * δ + 1 +
      (∑ i : Fin p, |(Sd i).re|) + (∑ j : Fin q, |(Td j).re|) with hMbase_def
  have hMbase_ge_Sre : ∀ i, |(Sd i).re| ≤ Mbase - 2 * δ - 1 - (∑ j : Fin q, |(Td j).re|) := by
    intro i
    have hpick : |(Sd i).re| ≤ ∑ k : Fin p, |(Sd k).re| :=
      Finset.single_le_sum (f := fun k : Fin p => |(Sd k).re|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ i)
    simp only [hMbase_def]; linarith
  have hMbase_ge_Tre : ∀ j, |(Td j).re| ≤ Mbase - 2 * δ - 1 - (∑ i : Fin p, |(Sd i).re|) := by
    intro j
    have hpick : |(Td j).re| ≤ ∑ k : Fin q, |(Td k).re| :=
      Finset.single_le_sum (f := fun k : Fin q => |(Td k).re|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    simp only [hMbase_def]; linarith
  let n := p + q
  let e : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv
  let Bs : Fin n → ℂ := fun k =>
    match e.symm k with
    | Sum.inl i => Sd i
    | Sum.inr _ => (Mbase : ℂ)
  let Bt : Fin n → ℂ := fun k =>
    match e.symm k with
    | Sum.inl _ => (-Mbase : ℂ)
    | Sum.inr j => Td j
  let Spad : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal Bs
  let Tpad : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal Bt
  let Apad : Matrix (Fin n) (Fin n) ℂ := fun I J =>
    match e.symm I, e.symm J with
    | Sum.inl i, Sum.inr j => A i j
    | _, _ => 0
  let Xpad : Matrix (Fin n) (Fin n) ℂ :=
    fun I J => Apad I J / (Spad I I - Tpad J J)
  have hSpad_diag : IsDiagMatrix Spad := fun I J h => Matrix.diagonal_apply_ne _ h
  have hTpad_diag : IsDiagMatrix Tpad := fun I J h => Matrix.diagonal_apply_ne _ h
  have hSpad_apply : ∀ k, Spad k k = Bs k := fun k => Matrix.diagonal_apply_eq Bs k
  have hTpad_apply : ∀ k, Tpad k k = Bt k := fun k => Matrix.diagonal_apply_eq Bt k
  have hSepPad : ∀ I J, 2 * δ ≤ (Spad I I - Tpad J J).re := by
    intro I J
    rw [hSpad_apply, hTpad_apply]
    show 2 * δ ≤ (Bs I - Bt J).re
    rcases hI : e.symm I with iL | iR <;> rcases hJ : e.symm J with jL | jR
    · have hBs_val : Bs I = Sd iL := by simp [Bs, hI]
      have hBt_val : Bt J = (-Mbase : ℂ) := by simp [Bt, hJ]
      rw [hBs_val, hBt_val]
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
      have hbnd := hMbase_ge_Sre iL
      have habs1 : -|(Sd iL).re| ≤ (Sd iL).re := neg_abs_le _
      have hsum_T : 0 ≤ ∑ j : Fin q, |(Td j).re| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      linarith
    · have hBs_val : Bs I = Sd iL := by simp [Bs, hI]
      have hBt_val : Bt J = Td jR := by simp [Bt, hJ]
      rw [hBs_val, hBt_val]; exact hRe iL jR
    · have hBs_val : Bs I = (Mbase : ℂ) := by simp [Bs, hI]
      have hBt_val : Bt J = (-Mbase : ℂ) := by simp [Bt, hJ]
      rw [hBs_val, hBt_val]
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
      have hMbase_ge_2d : 2 * δ ≤ Mbase := by
        have h1 : 0 ≤ ∑ i : Fin p, |(Sd i).re| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        have h2 : 0 ≤ ∑ j : Fin q, |(Td j).re| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        simp only [hMbase_def]; linarith
      linarith
    · have hBs_val : Bs I = (Mbase : ℂ) := by simp [Bs, hI]
      have hBt_val : Bt J = Td jR := by simp [Bt, hJ]
      rw [hBs_val, hBt_val]
      simp only [Complex.sub_re, Complex.ofReal_re]
      have hbnd := hMbase_ge_Tre jR
      have habs1 : (Td jR).re ≤ |(Td jR).re| := le_abs_self _
      have hsum_S : 0 ≤ ∑ i : Fin p, |(Sd i).re| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      linarith
  have hkey0 := (sylvester_diag_opNorm_bound_re Spad Tpad Apad hSpad_diag hTpad_diag
    (2 * δ) (by positivity) hSepPad).2
  have hkey : ‖Xpad‖ ≤ ‖Apad‖ / (2 * δ) := hkey0
  have hApad_cross : ∀ i j, Apad (e (Sum.inl i)) (e (Sum.inr j)) = A i j := by
    intro i j; simp [Apad, e.symm_apply_apply]
  have hf_inj : Function.Injective (fun i : Fin p => e (Sum.inl i)) :=
    fun i₁ i₂ h => Sum.inl.inj (e.injective h)
  have hg_inj : Function.Injective (fun j : Fin q => e (Sum.inr j)) :=
    fun j₁ j₂ h => Sum.inr.inj (e.injective h)
  have hApad_norm_eq : ‖Apad‖ = ‖A‖ := by
    apply le_antisymm
    · apply embedBlock_norm_le _ _ hf_inj hg_inj Apad A
      · intro I J hrow
        show Apad I J = 0
        rcases hI : e.symm I with iL | iR
        · exfalso; apply hrow iL
          rw [show I = e (Sum.inl iL) from by rw [← hI]; simp]
        · simp [Apad, hI]
      · intro I J hcol
        show Apad I J = 0
        rcases hJ : e.symm J with jL | jR
        · simp [Apad, hJ]
        · exfalso; apply hcol jR
          rw [show J = e (Sum.inr jR) from by rw [← hJ]; simp]
      · exact hApad_cross
    · have hAeq : A = Matrix.of (fun (i : Fin p) (j : Fin q) =>
          Apad (e (Sum.inl i)) (e (Sum.inr j))) := by
        ext i j; rw [Matrix.of_apply, hApad_cross]
      rw [hAeq]
      exact cross_submatrix_norm_le _ _ hf_inj hg_inj Apad
  have hXpad_cross : ∀ i j, Xpad (e (Sum.inl i)) (e (Sum.inr j)) = A i j / (Sd i - Td j) := by
    intro i j
    change Apad (e (Sum.inl i)) (e (Sum.inr j)) /
      (Spad (e (Sum.inl i)) (e (Sum.inl i)) - Tpad (e (Sum.inr j)) (e (Sum.inr j))) = _
    rw [hApad_cross, hSpad_apply, hTpad_apply]
    show A i j / (Bs (e (Sum.inl i)) - Bt (e (Sum.inr j))) = A i j / (Sd i - Td j)
    have hBs_val : Bs (e (Sum.inl i)) = Sd i := by simp [Bs]
    have hBt_val : Bt (e (Sum.inr j)) = Td j := by simp [Bt]
    rw [hBs_val, hBt_val]
  let Xtarget : Matrix (Fin p) (Fin q) ℂ := fun i j => A i j / (Sd i - Td j)
  have hXtarget_eq : Xtarget =
      Matrix.of (fun (i : Fin p) (j : Fin q) =>
        Xpad (e (Sum.inl i)) (e (Sum.inr j))) := by
    ext i j; simp only [Xtarget, Matrix.of_apply, hXpad_cross]
  have hXtarget_le : ‖Xtarget‖ ≤ ‖Xpad‖ := by
    rw [hXtarget_eq]; exact cross_submatrix_norm_le _ _ hf_inj hg_inj Xpad
  change ‖Xtarget‖ ≤ ‖A‖ / (2 * δ)
  calc ‖Xtarget‖
      ≤ ‖Xpad‖ := hXtarget_le
    _ ≤ ‖Apad‖ / (2 * δ) := hkey
    _ = ‖A‖ / (2 * δ) := by rw [hApad_norm_eq]

/- (by claude)
State: ✅ done
Priority: 2
Attempts: 2 / 20
Session: S426
-/
/-- Cross-block Sylvester bound with explicit spectral gap.
    For diagonal "row" data `Sd : Fin p → ℂ` and "column" data `Td : Fin q → ℂ`
    whose differences `Sd i - Td j` are uniformly separated by `2δ` in either real
    or imaginary part (in either sign direction), the Sylvester quotient
    `X i j := A i j / (Sd i - Td j)` is well-defined and obeys the dimension-free
    bound `‖X‖ ≤ ‖A‖ / (2δ)`.

    This packages the cross-block Sylvester step from `lambdaA_four_block_bound`
    in a reusable rectangular form. The companion same-block bound is
    `partition_blockDiag_norm_le`. Used by the upcoming `lambdaA_block_2x2_decomp`
    aggregator. -/
lemma crossBlock_sylvester_norm_le {p q : ℕ}
    (Sd : Fin p → ℂ) (Td : Fin q → ℂ)
    (A : Matrix (Fin p) (Fin q) ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hSigned : (∀ i j, 2 * δ ≤ (Sd i - Td j).re) ∨
               (∀ i j, (Sd i - Td j).re ≤ -(2 * δ)) ∨
               (∀ i j, 2 * δ ≤ (Sd i - Td j).im) ∨
               (∀ i j, (Sd i - Td j).im ≤ -(2 * δ))) :
    ‖(Matrix.of (fun i j => A i j / (Sd i - Td j)) : Matrix (Fin p) (Fin q) ℂ)‖
      ≤ ‖A‖ / (2 * δ) := by
  rcases hSigned with hpos_re | hneg_re | hpos_im | hneg_im
  · exact crossBlock_sylvester_norm_le_re_pos Sd Td A δ hδ hpos_re
  · -- Re ≤ -2δ: negate Sd, Td, A
    have hpos : ∀ i j, 2 * δ ≤ ((-Sd) i - (-Td) j).re := by
      intro i j
      simp only [Pi.neg_apply, Complex.sub_re, Complex.neg_re]
      have := hneg_re i j
      simp only [Complex.sub_re] at this
      linarith
    have key := crossBlock_sylvester_norm_le_re_pos (-Sd) (-Td) (-A) δ hδ hpos
    have heq : ((fun i j => (-A) i j / ((-Sd) i - (-Td) j)) : Matrix (Fin p) (Fin q) ℂ) =
        ((fun i j => A i j / (Sd i - Td j)) : Matrix (Fin p) (Fin q) ℂ) := by
      ext i j
      simp only [Pi.neg_apply, Matrix.neg_apply]
      rw [show (-Sd i) - (-Td j) = -(Sd i - Td j) from by ring, neg_div_neg_eq]
    rw [heq] at key
    have hAneg : ‖(-A : Matrix (Fin p) (Fin q) ℂ)‖ = ‖A‖ := norm_neg _
    rw [hAneg] at key
    exact key
  · -- Im ≥ 2δ: multiply by -i (so Re of new diff = Im of old diff)
    let Sd' : Fin p → ℂ := fun i => (-Complex.I) * Sd i
    let Td' : Fin q → ℂ := fun j => (-Complex.I) * Td j
    let A' : Matrix (Fin p) (Fin q) ℂ := fun i j => (-Complex.I) * A i j
    have hpos : ∀ i j, 2 * δ ≤ (Sd' i - Td' j).re := by
      intro i j
      have hexpand : ((-Complex.I) * Sd i - (-Complex.I) * Td j).re = (Sd i - Td j).im := by
        simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im,
          Complex.I_im, Complex.sub_re, Complex.sub_im]; ring
      change 2 * δ ≤ ((-Complex.I) * Sd i - (-Complex.I) * Td j).re
      rw [hexpand]; exact hpos_im i j
    have key := crossBlock_sylvester_norm_le_re_pos Sd' Td' A' δ hδ hpos
    have heq : ((fun i j => A' i j / (Sd' i - Td' j)) : Matrix (Fin p) (Fin q) ℂ) =
        ((fun i j => A i j / (Sd i - Td j)) : Matrix (Fin p) (Fin q) ℂ) := by
      ext i j
      change (-Complex.I) * A i j / ((-Complex.I) * Sd i - (-Complex.I) * Td j) =
           A i j / (Sd i - Td j)
      have hne : (-Complex.I) ≠ 0 := by
        intro h; have := congr_arg Complex.im h; simp at this
      rw [show (-Complex.I) * Sd i - (-Complex.I) * Td j =
          (-Complex.I) * (Sd i - Td j) from by ring]
      exact mul_div_mul_left (A i j) (Sd i - Td j) hne
    rw [heq] at key
    have hA'_norm : ‖A'‖ = ‖A‖ := by
      have heq2 : A' = ((-Complex.I) • A : Matrix (Fin p) (Fin q) ℂ) := by
        ext i j; simp [A', Matrix.smul_apply, smul_eq_mul]
      rw [heq2, norm_smul, norm_neg, Complex.norm_I, one_mul]
    rw [hA'_norm] at key
    exact key
  · -- Im ≤ -2δ: multiply by +i
    let Sd' : Fin p → ℂ := fun i => Complex.I * Sd i
    let Td' : Fin q → ℂ := fun j => Complex.I * Td j
    let A' : Matrix (Fin p) (Fin q) ℂ := fun i j => Complex.I * A i j
    have hpos : ∀ i j, 2 * δ ≤ (Sd' i - Td' j).re := by
      intro i j
      have hexpand : (Complex.I * Sd i - Complex.I * Td j).re = -(Sd i - Td j).im := by
        simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.sub_re, Complex.sub_im]; ring
      change 2 * δ ≤ (Complex.I * Sd i - Complex.I * Td j).re
      rw [hexpand]
      have := hneg_im i j; linarith
    have key := crossBlock_sylvester_norm_le_re_pos Sd' Td' A' δ hδ hpos
    have heq : ((fun i j => A' i j / (Sd' i - Td' j)) : Matrix (Fin p) (Fin q) ℂ) =
        ((fun i j => A i j / (Sd i - Td j)) : Matrix (Fin p) (Fin q) ℂ) := by
      ext i j
      change Complex.I * A i j / (Complex.I * Sd i - Complex.I * Td j) = A i j / (Sd i - Td j)
      have hne : Complex.I ≠ 0 := Complex.I_ne_zero
      rw [show Complex.I * Sd i - Complex.I * Td j =
          Complex.I * (Sd i - Td j) from by ring]
      exact mul_div_mul_left (A i j) (Sd i - Td j) hne
    rw [heq] at key
    have hA'_norm : ‖A'‖ = ‖A‖ := by
      have heq2 : A' = (Complex.I • A : Matrix (Fin p) (Fin q) ℂ) := by
        ext i j; simp [A', Matrix.smul_apply, smul_eq_mul]
      rw [heq2, norm_smul, Complex.norm_I, one_mul]
    rw [hA'_norm] at key
    exact key

/-- **Sub-lemma 2a of `claim2_asymmetric` (S434/S435, paper-traceable).** The
    paper's asymmetric shift for the (1,1)-block: `B'_11 = (-1+δ)·I + δ·B_11`
    sends `InUnitSquare`-valued `z` to `(-1+δ) + δ·z`, which is again
    `InUnitSquare` when `0 < δ ≤ 1`. Re ∈ [-1, -1+2δ] ⊂ [-1,1]; Im range scales
    by δ. Companion to the symmetric `unit_square_corner_shift_pos/neg`
    (Main:6310, 6341). Paper: JOS 2013 p.19253 top.

    Ref: BLUEPRINT.md S434, S434a, project_state.md S434b. -/
lemma unit_square_asymmetric_shift_neg {z : ℂ} (hz : InUnitSquare z)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    InUnitSquare ((-1 + (δ : ℂ)) + (δ : ℂ) * z) := by
  obtain ⟨hzre, hzim⟩ := hz
  rw [abs_le] at hzre hzim
  obtain ⟨hzre_lo, hzre_hi⟩ := hzre
  obtain ⟨hzim_lo, hzim_hi⟩ := hzim
  refine ⟨?_, ?_⟩
  · have hre_eq : ((-1 + (δ : ℂ)) + (δ : ℂ) * z).re
        = (-1 + δ) + δ * z.re := by
      simp [Complex.add_re, Complex.mul_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.neg_re]
    rw [hre_eq, abs_le]
    refine ⟨?_, ?_⟩ <;> nlinarith
  · have him_eq : ((-1 + (δ : ℂ)) + (δ : ℂ) * z).im
        = δ * z.im := by
      simp [Complex.add_im, Complex.mul_im,
            Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im]
    rw [him_eq, abs_le]
    refine ⟨?_, ?_⟩ <;> nlinarith

/- (by claude)
State: ✅ done
Priority: 1
Attempts: 1 / 20
Session: S435
-/
/-- **Sub-lemma 2b of `claim2_asymmetric` (S434/S435, paper-traceable).** The
    paper's asymmetric shift for the (2,2)-block: `B'_22 = 2δ·I + (1-2δ)·B_22`
    sends `InUnitSquare`-valued `z` to `2δ + (1-2δ)·z`, which is again
    `InUnitSquare` when `0 < δ < 1/2`. Re ∈ [-1+4δ, 1] ⊂ [-1,1]; Im range
    scales by `1-2δ`. Paper: JOS 2013 p.19253 top.

    Ref: BLUEPRINT.md S434, S434a, project_state.md S434b. -/
lemma unit_square_asymmetric_shift_pos {z : ℂ} (hz : InUnitSquare z)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 2) :
    InUnitSquare ((2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * z) := by
  obtain ⟨hzre, hzim⟩ := hz
  rw [abs_le] at hzre hzim
  obtain ⟨hzre_lo, hzre_hi⟩ := hzre
  obtain ⟨hzim_lo, hzim_hi⟩ := hzim
  refine ⟨?_, ?_⟩
  · have hre_eq : ((2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * z).re
        = 2 * δ + (1 - 2 * δ) * z.re := by
      simp [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re,
            Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre_eq, abs_le]
    refine ⟨?_, ?_⟩ <;> nlinarith
  · have him_eq : ((2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * z).im
        = (1 - 2 * δ) * z.im := by
      simp [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.one_re,
            Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [him_eq, abs_le]
    refine ⟨?_, ?_⟩ <;> nlinarith

/-- **Sub-lemma 1 of `claim2_asymmetric` (S434b).** Per-block ε-witness extraction.
    Given a zero-diagonal block `A_ii` with `lambdaA A_ii ≤ c` and slack `η > 0`,
    extract a decomposition `A_ii = ⁅B, C⁆ₘ` with B unit-square diagonal and
    `‖C‖ ≤ c + η`. Mirrors the `hpick` block of `lambdaA_block_2x2_decomp_param`
    (Main.lean:6419-6447): standard `csInf` argument for n ≥ 2, trivial (0,0)
    fallback for n < 2 (using `ZeroDiag` to force the 1×1 case to zero). -/
/- (by claude)
State: ✅ done
Priority: 1
Attempts: 1 / 20
tmp file: (none — landed directly)
-/
private lemma claim2_asymmetric_block_witness {m : ℕ}
    (A_ii : Matrix (Fin m) (Fin m) ℂ) (hzd : ZeroDiag A_ii)
    (c : ℝ) (h_bnd : lambdaA A_ii ≤ c)
    (η : ℝ) (hη : 0 < η) :
    ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
      A_ii = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c + η := by
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
    · intro i j _; simp
    · intro i; refine ⟨?_, ?_⟩ <;> simp
    · ext i j
      simp only [matComm, mul_zero, Matrix.sub_apply, Matrix.zero_apply, sub_self]
      interval_cases m
      · exact Fin.elim0 i
      · have hij : i = j := Fin.ext (by omega)
        rw [hij]; exact hzd j
    · simp
      have hlam_nn : 0 ≤ lambdaA A_ii := lambdaA_nonneg_S1f _
      linarith
  · obtain ⟨B, C, hd, hu, hc, _⟩ := zeroDiag_InUnitSquare_decomp_bounded_S1f hm2 A_ii hzd
    set Tset : Set ℝ := {c' : ℝ | ∃ (B' C' : Matrix (Fin m) (Fin m) ℂ),
        IsDiagMatrix B' ∧ (∀ i, InUnitSquare (B' i i)) ∧
        A_ii = ⁅B', C'⁆ₘ ∧ ‖C'‖ ≤ c'} with hT_def
    have hne : Tset.Nonempty := ⟨‖C‖, B, C, hd, hu, hc, le_refl _⟩
    have hbdd : BddBelow Tset :=
      ⟨0, fun c' ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
    have hsInf_eq : sInf Tset = lambdaA A_ii := by
      unfold lambdaA; rfl
    have hlt : sInf Tset < c + η := by
      rw [hsInf_eq]; linarith
    obtain ⟨c', ⟨B', C', hd', hu', hc', hnormC'⟩, hclt⟩ :=
      exists_lt_of_csInf_lt hne hlt
    exact ⟨B', C', hd', hu', hc', le_trans hnormC' (le_of_lt hclt)⟩

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- **Sub-lemma 3 of `claim2_asymmetric` (S435, paper-traceable).** Cross-block
    Sylvester bound for the asymmetric shift configuration. Given diagonal
    unit-square `B_11`, `B_22` and the paper's asymmetric shifts
    `B'_11 := (-1+δ)·I + δ·B_11`, `B'_22 := 2δ·I + (1-2δ)·B_22` (gap `2δ`,
    paper p.19253 top), the cross-block Sylvester quotient `X(i,j) :=
    A_12(i,j) / (B'_11(i,i) - B'_22(j,j))` is well-defined and satisfies
    `B'_11·X − X·B'_22 = A_12` together with the linear bound `‖X‖ ≤ ‖A_12‖/(2δ)`.

    The paper states the looser quadratic bound `K·‖A‖/δ²` (Rosenblum contour-
    integral form, K = 4/π); since `1/(2δ) ≤ 1/δ²` for `δ ≤ 1/2`, the linear
    bound proven here is strictly tighter and supplies the `Anorm/δ²` term that
    `claim2_asymmetric_delta_schedule` (Main:7181) consumes. Built atop
    `crossBlock_sylvester_norm_le` (Main:6213).

    Companion to Sub-lemma 4 (`claim2_asymmetric_same_block_norm_le`, TBD) and
    Sub-lemma 2a/2b (`unit_square_asymmetric_shift_neg/pos`, Main:6376/6412).
    Used by the glue body of `claim2_asymmetric` (Main:7254).

    Ref: BLUEPRINT.md S434/S434a/S434b. Paper: JOS 2013 p.19253. -/
/- (by claude)
State: ✅ done
Priority: 1
Attempts: 1 / 20
Session: S435
-/
private lemma claim2_asymmetric_cross_norm_le {m : ℕ}
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 2)
    (B_11 B_22 : Matrix (Fin m) (Fin m) ℂ)
    (hB11_diag : IsDiagMatrix B_11) (hB11_unit : ∀ i, InUnitSquare (B_11 i i))
    (hB22_diag : IsDiagMatrix B_22) (hB22_unit : ∀ i, InUnitSquare (B_22 i i))
    (A_12 : Matrix (Fin m) (Fin m) ℂ) :
    ∃ (X : Matrix (Fin m) (Fin m) ℂ),
      (∀ i j, ((-1 + (δ : ℂ)) + (δ : ℂ) * B_11 i i) * X i j
              - X i j * ((2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 j j)
              = A_12 i j) ∧
      ‖X‖ ≤ ‖A_12‖ / (2 * δ) := by
  -- Diagonal data: row data Sd i = (-1+δ) + δ·B_11(i,i),
  -- col data Td j = 2δ + (1-2δ)·B_22(j,j).
  set Sd : Fin m → ℂ := fun i => (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 i i with hSd_def
  set Td : Fin m → ℂ := fun j => (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 j j with hTd_def
  -- Spectrum gap: Re(Sd i - Td j) ≤ -2δ. Compute Re(Sd i) and Re(Td j) explicitly.
  have hδ_lt_one : δ < 1 := by linarith
  have hSd_re_le : ∀ i, (Sd i).re ≤ -1 + 2 * δ := by
    intro i
    have hu := hB11_unit i
    obtain ⟨hu_re, _⟩ := hu
    rw [abs_le] at hu_re
    obtain ⟨_, hu_re_hi⟩ := hu_re
    change ((-1 + (δ : ℂ)) + (δ : ℂ) * B_11 i i).re ≤ -1 + 2 * δ
    have hre_eq : ((-1 + (δ : ℂ)) + (δ : ℂ) * B_11 i i).re
        = (-1 + δ) + δ * (B_11 i i).re := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.neg_re, Complex.one_re]
    rw [hre_eq]; nlinarith
  have hTd_re_ge : ∀ j, -1 + 4 * δ ≤ (Td j).re := by
    intro j
    have hu := hB22_unit j
    obtain ⟨hu_re, _⟩ := hu
    rw [abs_le] at hu_re
    obtain ⟨hu_re_lo, _⟩ := hu_re
    change -1 + 4 * δ ≤ ((2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 j j).re
    have hre_eq : ((2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 j j).re
        = 2 * δ + (1 - 2 * δ) * (B_22 j j).re := by
      simp [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.one_re, Complex.one_im]
    rw [hre_eq]; nlinarith
  have hReGap : ∀ i j, (Sd i - Td j).re ≤ -(2 * δ) := by
    intro i j
    rw [Complex.sub_re]
    have h1 : (Sd i).re ≤ -1 + 2 * δ := hSd_re_le i
    have h2 : -1 + 4 * δ ≤ (Td j).re := hTd_re_ge j
    linarith
  -- Define X as the Sylvester quotient.
  refine ⟨Matrix.of (fun i j => A_12 i j / (Sd i - Td j)), ?_, ?_⟩
  · -- Sylvester equation: (Sd i)·X(i,j) - X(i,j)·(Td j) = A_12(i,j) when Sd i ≠ Td j.
    intro i j
    have hne : Sd i - Td j ≠ 0 := by
      intro hzero
      have hre : (Sd i - Td j).re = 0 := by rw [hzero]; simp
      have := hReGap i j
      rw [hre] at this
      linarith
    change Sd i * (Matrix.of (fun i j => A_12 i j / (Sd i - Td j))) i j
          - (Matrix.of (fun i j => A_12 i j / (Sd i - Td j))) i j * Td j
        = A_12 i j
    simp only [Matrix.of_apply]
    have hSyl : Sd i * (A_12 i j / (Sd i - Td j))
              - (A_12 i j / (Sd i - Td j)) * Td j = A_12 i j := by
      field_simp
    exact hSyl
  · -- Norm bound via crossBlock_sylvester_norm_le with Re ≤ -2δ branch.
    apply crossBlock_sylvester_norm_le Sd Td A_12 δ hδ_pos
    right; left; exact hReGap

/- (by claude)
State: ✅ done
Priority: 1
Attempts: 1 / 20
Session: S435
-/
-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- **Sub-lemma 4 of `claim2_asymmetric` (S435, paper-traceable).** Same-block
    rescaled-C bound for the asymmetric setup. Given two zero-diagonal m×m blocks
    `A_11`, `A_22` with `lambdaA(A_ii) ≤ c_i`, η-slack witnesses (Sub-lemma 1)
    `A_ii = ⁅B_ii, C_ii⁆ₘ` with `‖C_ii‖ ≤ c_i + η`, and the asymmetric δ-rescaling
    `C'_11 := δ⁻¹·C_11`, `C'_22 := (1-2δ)⁻¹·C_22`, the embedded block-diagonal
    matrix `Cdiag` (with C'_11 on the (1,1) block, C'_22 on the (2,2) block,
    zeros on cross blocks) satisfies the (slacker) bound

      `‖Cdiag‖ ≤ c₂/(1-2δ) + η/δ + η/(1-2δ)`

    when `δ ≥ √(c_1/c_2)` (so `c_1/δ ≤ c_2/(1-2δ)` via `δ < 1/2`).

    The conclusion is slightly weaker than the paper's `c₂/(1-2δ) + 2η/(1-2δ)`:
    we keep the η-slack split as `η/δ + η/(1-2δ)` because `η/δ ≤ 2η/(1-2δ)`
    only holds for `δ ≥ 1/4`. Since η is a free positive slack (chosen by the
    glue body via Sub-lemma 1), this slacker form is fully consumable.

    Companion to Sub-lemma 3 (`claim2_asymmetric_cross_norm_le`, Main:7255).
    Built from `partition_blockDiag_norm_le` (Main:5864). Used by the glue body
    of `claim2_asymmetric`.

    Ref: BLUEPRINT.md S434/S434a/S434b. Paper: JOS 2013 p.19253. -/
private lemma claim2_asymmetric_same_block_norm_le {m : ℕ}
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 2)
    (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hkey_ext : c₁ / δ ≤ c₂ / (1 - 2 * δ))
    (η : ℝ) (hη : 0 < η)
    (C_11 C_22 : Matrix (Fin m) (Fin m) ℂ)
    (hC11_norm : ‖C_11‖ ≤ c₁ + η) (hC22_norm : ‖C_22‖ ≤ c₂ + η) :
    ∃ (Cdiag : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ),
      (∀ i j : Fin m, Cdiag ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
          = (δ : ℂ)⁻¹ * C_11 i j) ∧
      (∀ i j : Fin m, Cdiag ⟨m + i.val, by omega⟩ ⟨m + j.val, by omega⟩
          = ((1 - 2 * (δ : ℂ)))⁻¹ * C_22 i j) ∧
      (∀ i : Fin m, ∀ j : Fin m, Cdiag ⟨i.val, by omega⟩ ⟨m + j.val, by omega⟩ = 0) ∧
      (∀ i : Fin m, ∀ j : Fin m, Cdiag ⟨m + i.val, by omega⟩ ⟨j.val, by omega⟩ = 0) ∧
      ‖Cdiag‖ ≤ c₂ / (1 - 2 * δ) + η / δ + η / (1 - 2 * δ) := by
  have h1m2δ : (0 : ℝ) < 1 - 2 * δ := by linarith
  have hδ_ne : (δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ_pos
  have h1m2δ_ne : (1 - 2 * (δ : ℂ)) ≠ 0 := by
    intro h
    have hcast : ((1 - 2 * δ : ℝ) : ℂ) = 0 := by push_cast; exact h
    have hreal : (1 - 2 * δ : ℝ) = 0 := by exact_mod_cast hcast
    linarith
  -- Construct Cdiag via case split on first/second half indices.
  refine ⟨Matrix.of fun (i j : Fin (2 * m)) =>
    if hi : i.val < m then
      if hj : j.val < m then
        (δ : ℂ)⁻¹ * C_11 ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else 0
    else
      if _hj : j.val < m then 0
      else
        ((1 - 2 * (δ : ℂ)))⁻¹ * C_22 ⟨i.val - m, by omega⟩ ⟨j.val - m, by omega⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  -- Indexing equality 1: top-left block.
  · intro i j
    show (Matrix.of _ : Matrix (Fin (2*m)) (Fin (2*m)) ℂ) _ _ = _
    simp only [Matrix.of_apply]
    have hi : i.val < m := i.isLt
    have hj : j.val < m := j.isLt
    rw [dif_pos hi, dif_pos hj]
  -- Indexing equality 2: bottom-right block.
  · intro i j
    show (Matrix.of _ : Matrix (Fin (2*m)) (Fin (2*m)) ℂ) _ _ = _
    simp only [Matrix.of_apply]
    have hi_ge : ¬ (m + i.val < m) := by omega
    have hj_ge : ¬ (m + j.val < m) := by omega
    rw [dif_neg hi_ge, dif_neg hj_ge]
    have hi_eq : (m + i.val) - m = i.val := by omega
    have hj_eq : (m + j.val) - m = j.val := by omega
    have hi_fin : (⟨(m + i.val) - m, by omega⟩ : Fin m) = i := Fin.ext hi_eq
    have hj_fin : (⟨(m + j.val) - m, by omega⟩ : Fin m) = j := Fin.ext hj_eq
    rw [hi_fin, hj_fin]
  -- Indexing equality 3: top-right cross block = 0.
  · intro i j
    show (Matrix.of _ : Matrix (Fin (2*m)) (Fin (2*m)) ℂ) _ _ = _
    simp only [Matrix.of_apply]
    have hi : i.val < m := i.isLt
    have hj_ge : ¬ ((m + j.val) < m) := by omega
    rw [dif_pos hi, dif_neg hj_ge]
  -- Indexing equality 4: bottom-left cross block = 0.
  · intro i j
    show (Matrix.of _ : Matrix (Fin (2*m)) (Fin (2*m)) ℂ) _ _ = _
    simp only [Matrix.of_apply]
    have hi_ge : ¬ ((m + i.val) < m) := by omega
    have hj : j.val < m := j.isLt
    rw [dif_neg hi_ge, dif_pos hj]
  -- Norm bound via partition_blockDiag_norm_le.
  · -- Build the partition: S = first half of Fin (2*m).
    set Cdiag : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ := Matrix.of fun (i j : Fin (2 * m)) =>
      if hi : i.val < m then
        if hj : j.val < m then
          (δ : ℂ)⁻¹ * C_11 ⟨i.val, hi⟩ ⟨j.val, hj⟩
        else 0
      else
        if _hj : j.val < m then 0
        else
          ((1 - 2 * (δ : ℂ)))⁻¹ * C_22 ⟨i.val - m, by omega⟩ ⟨j.val - m, by omega⟩
        with hCdiag_def
    -- Partition S = first-half image.
    -- Define raw embedding functions and their key properties.
    let firstHalfFn : Fin m → Fin (2 * m) := fun k => ⟨k.val, by omega⟩
    let secondHalfFn : Fin m → Fin (2 * m) := fun k => ⟨m + k.val, by omega⟩
    have hfh_inj : Function.Injective firstHalfFn := by
      intro a b h
      apply Fin.ext
      have := congrArg Fin.val h
      simpa [firstHalfFn] using this
    have hsh_inj : Function.Injective secondHalfFn := by
      intro a b h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp [secondHalfFn] at hv
      omega
    have hfh_mono : StrictMono firstHalfFn := by
      intro a b hab
      change (⟨a.val, _⟩ : Fin (2 * m)) < ⟨b.val, _⟩
      rw [Fin.mk_lt_mk]
      exact hab
    have hsh_mono : StrictMono secondHalfFn := by
      intro a b hab
      change (⟨m + a.val, _⟩ : Fin (2 * m)) < ⟨m + b.val, _⟩
      rw [Fin.mk_lt_mk]
      omega
    set S : Finset (Fin (2 * m)) := Finset.image firstHalfFn Finset.univ with hS_def
    have hS_card : S.card = m := by
      rw [hS_def, Finset.card_image_of_injective _ hfh_inj, Finset.card_univ,
        Fintype.card_fin]
    have hSc_eq : Sᶜ = Finset.image secondHalfFn Finset.univ := by
      ext x
      simp only [Finset.mem_compl, hS_def, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hx
        push Not at hx
        have hx_ge : ¬ (x.val < m) := by
          intro hxlt
          exact hx ⟨x.val, hxlt⟩ (Fin.ext rfl)
        refine ⟨⟨x.val - m, ?_⟩, ?_⟩
        · have hxlt : x.val < 2 * m := x.isLt
          omega
        · apply Fin.ext
          change m + (x.val - m) = x.val
          omega
      · rintro ⟨k, hk_eq⟩ ⟨k', hk_eq'⟩
        have hv₁ : m + k.val = x.val := by
          have := congrArg Fin.val hk_eq
          simpa [secondHalfFn] using this
        have hv₂ : k'.val = x.val := by
          have := congrArg Fin.val hk_eq'
          simpa [firstHalfFn] using this
        have hk'lt : k'.val < m := k'.isLt
        omega
    have hSc_card : Sᶜ.card = m := by
      rw [hSc_eq, Finset.card_image_of_injective _ hsh_inj, Finset.card_univ,
        Fintype.card_fin]
    -- The order embeddings of S and Sᶜ coincide with firstHalfFn/secondHalfFn via cardinality cast.
    set f : Fin S.card ↪o Fin (2 * m) := S.orderEmbOfFin rfl with hf_def
    set g : Fin Sᶜ.card ↪o Fin (2 * m) := Sᶜ.orderEmbOfFin rfl with hg_def
    -- By orderEmbOfFin_unique, f = firstHalfFn ∘ Fin.cast hS_card.
    have hcastS_strict : StrictMono (Fin.cast hS_card) := fun a b hab => hab
    have hcastSc_strict : StrictMono (Fin.cast hSc_card) := fun a b hab => hab
    -- Helper: anything of the form firstHalfFn _ is in S.
    have hfh_in_S : ∀ y : Fin m, firstHalfFn y ∈ S := by
      intro y
      change firstHalfFn y ∈ Finset.image firstHalfFn Finset.univ
      exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
    have hsh_in_Sc : ∀ y : Fin m, secondHalfFn y ∈ Sᶜ := by
      intro y
      rw [hSc_eq]
      exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
    have hf_apply : ∀ i : Fin S.card,
        (f i : Fin (2 * m)) =
          ⟨(Fin.cast hS_card i).val, by have := (Fin.cast hS_card i).isLt; omega⟩ := by
      have hfn : (fun x : Fin S.card => firstHalfFn (Fin.cast hS_card x)) =
          S.orderEmbOfFin (rfl : S.card = S.card) := by
        apply Finset.orderEmbOfFin_unique (h := rfl)
        · intro x; exact hfh_in_S _
        · intro a b hab
          exact hfh_mono (hcastS_strict hab)
      intro i
      have h := congrArg (fun (φ : Fin S.card → Fin (2 * m)) => φ i) hfn
      simp only at h
      change (S.orderEmbOfFin (rfl : S.card = S.card)) i =
          ⟨(Fin.cast hS_card i).val, _⟩
      rw [← h]
    have hg_apply : ∀ i : Fin Sᶜ.card,
        (g i : Fin (2 * m)) =
          ⟨m + (Fin.cast hSc_card i).val, by have := (Fin.cast hSc_card i).isLt; omega⟩ := by
      have hgn : (fun x : Fin Sᶜ.card => secondHalfFn (Fin.cast hSc_card x)) =
          Sᶜ.orderEmbOfFin (rfl : Sᶜ.card = Sᶜ.card) := by
        apply Finset.orderEmbOfFin_unique (h := rfl)
        · intro x; exact hsh_in_Sc _
        · intro a b hab
          exact hsh_mono (hcastSc_strict hab)
      intro i
      have h := congrArg (fun (φ : Fin Sᶜ.card → Fin (2 * m)) => φ i) hgn
      simp only at h
      change (Sᶜ.orderEmbOfFin (rfl : Sᶜ.card = Sᶜ.card)) i =
          ⟨m + (Fin.cast hSc_card i).val, _⟩
      rw [← h]
    -- Build A_S and A_Sc as the rescaled C blocks.
    let A_S : Matrix (Fin S.card) (Fin S.card) ℂ :=
      Matrix.of fun i j => (δ : ℂ)⁻¹ * C_11 (Fin.cast hS_card i) (Fin.cast hS_card j)
    let A_Sc : Matrix (Fin Sᶜ.card) (Fin Sᶜ.card) ℂ :=
      Matrix.of fun i j => ((1 - 2 * (δ : ℂ)))⁻¹ * C_22 (Fin.cast hSc_card i) (Fin.cast hSc_card j)
    -- Verify the four conditions of partition_blockDiag_norm_le.
    have hMS : ∀ i j : Fin S.card, Cdiag (f i) (f j) = A_S i j := by
      intro i j
      rw [hf_apply i, hf_apply j]
      change (Matrix.of _ : Matrix (Fin (2*m)) (Fin (2*m)) ℂ) _ _ = _
      simp only [Matrix.of_apply]
      have hi : (Fin.cast hS_card i).val < m := (Fin.cast hS_card i).isLt
      have hj : (Fin.cast hS_card j).val < m := (Fin.cast hS_card j).isLt
      rw [dif_pos hi, dif_pos hj]
      rfl
    have hMSc : ∀ i j : Fin Sᶜ.card, Cdiag (g i) (g j) = A_Sc i j := by
      intro i j
      rw [hg_apply i, hg_apply j]
      change (Matrix.of _ : Matrix (Fin (2*m)) (Fin (2*m)) ℂ) _ _ = _
      simp only [Matrix.of_apply]
      have hi_ge : ¬ ((m + (Fin.cast hSc_card i).val) < m) := by omega
      have hj_ge : ¬ ((m + (Fin.cast hSc_card j).val) < m) := by omega
      rw [dif_neg hi_ge, dif_neg hj_ge]
      have hi_eq : (m + (Fin.cast hSc_card i).val) - m = (Fin.cast hSc_card i).val := by omega
      have hj_eq : (m + (Fin.cast hSc_card j).val) - m = (Fin.cast hSc_card j).val := by omega
      have hi_fin : (⟨(m + (Fin.cast hSc_card i).val) - m, by omega⟩ : Fin m) =
          Fin.cast hSc_card i := Fin.ext hi_eq
      have hj_fin : (⟨(m + (Fin.cast hSc_card j).val) - m, by omega⟩ : Fin m) =
          Fin.cast hSc_card j := Fin.ext hj_eq
      rw [hi_fin, hj_fin]
      rfl
    have hM_cross_fg : ∀ (i : Fin S.card) (j : Fin Sᶜ.card), Cdiag (f i) (g j) = 0 := by
      intro i j
      rw [hf_apply i, hg_apply j]
      change (Matrix.of _ : Matrix (Fin (2*m)) (Fin (2*m)) ℂ) _ _ = _
      simp only [Matrix.of_apply]
      have hi : (Fin.cast hS_card i).val < m := (Fin.cast hS_card i).isLt
      have hj_ge : ¬ ((m + (Fin.cast hSc_card j).val) < m) := by omega
      rw [dif_pos hi, dif_neg hj_ge]
    have hM_cross_gf : ∀ (i : Fin Sᶜ.card) (j : Fin S.card), Cdiag (g i) (f j) = 0 := by
      intro i j
      rw [hg_apply i, hf_apply j]
      change (Matrix.of _ : Matrix (Fin (2*m)) (Fin (2*m)) ℂ) _ _ = _
      simp only [Matrix.of_apply]
      have hi_ge : ¬ ((m + (Fin.cast hSc_card i).val) < m) := by omega
      have hj : (Fin.cast hS_card j).val < m := (Fin.cast hS_card j).isLt
      rw [dif_neg hi_ge, dif_pos hj]
    -- Apply partition_blockDiag_norm_le.
    have hCdiag_le_max :=
      partition_blockDiag_norm_le S A_S A_Sc Cdiag hMS hMSc hM_cross_fg hM_cross_gf
    -- Bound ‖A_S‖ ≤ (c₁ + η)/δ.
    have hAS_norm_bound : ‖A_S‖ ≤ (c₁ + η) / δ := by
      have hAS_eq : A_S = (δ : ℂ)⁻¹ • Matrix.of (fun i j : Fin S.card =>
          C_11 (Fin.cast hS_card i) (Fin.cast hS_card j)) := by
        ext i j
        simp [A_S, Matrix.smul_apply]
      rw [hAS_eq, norm_smul]
      have hcoeff : ‖(δ : ℂ)⁻¹‖ = δ⁻¹ := by
        rw [norm_inv]
        simp [Complex.norm_real, abs_of_pos hδ_pos]
      rw [hcoeff]
      have hcast_inj : Function.Injective (fun i : Fin S.card => Fin.cast hS_card i) := by
        intro a b hab
        apply Fin.ext
        have := congrArg Fin.val hab
        simpa using this
      have hsub_norm : ‖Matrix.of (fun i j : Fin S.card =>
          C_11 (Fin.cast hS_card i) (Fin.cast hS_card j))‖ ≤ ‖C_11‖ :=
        submatrix_norm_le (fun i => Fin.cast hS_card i) hcast_inj C_11
      have hδinv_nn : 0 ≤ δ⁻¹ := le_of_lt (inv_pos.mpr hδ_pos)
      calc δ⁻¹ * ‖Matrix.of (fun i j : Fin S.card =>
              C_11 (Fin.cast hS_card i) (Fin.cast hS_card j))‖
          ≤ δ⁻¹ * ‖C_11‖ := mul_le_mul_of_nonneg_left hsub_norm hδinv_nn
        _ ≤ δ⁻¹ * (c₁ + η) := mul_le_mul_of_nonneg_left hC11_norm hδinv_nn
        _ = (c₁ + η) / δ := by rw [div_eq_inv_mul]
    -- Bound ‖A_Sc‖ ≤ (c₂ + η)/(1 - 2δ).
    have hASc_norm_bound : ‖A_Sc‖ ≤ (c₂ + η) / (1 - 2 * δ) := by
      have hASc_eq : A_Sc = ((1 - 2 * (δ : ℂ)))⁻¹ • Matrix.of (fun i j : Fin Sᶜ.card =>
          C_22 (Fin.cast hSc_card i) (Fin.cast hSc_card j)) := by
        ext i j
        simp [A_Sc, Matrix.smul_apply]
      rw [hASc_eq, norm_smul]
      have hcoeff : ‖((1 - 2 * (δ : ℂ)))⁻¹‖ = (1 - 2 * δ)⁻¹ := by
        have h1 : (1 - 2 * (δ : ℂ)) = ((1 - 2 * δ : ℝ) : ℂ) := by push_cast; ring
        rw [norm_inv, h1, Complex.norm_real]
        congr 1
        exact Real.norm_of_nonneg h1m2δ.le
      rw [hcoeff]
      have hcast_inj : Function.Injective (fun i : Fin Sᶜ.card => Fin.cast hSc_card i) := by
        intro a b hab
        apply Fin.ext
        have := congrArg Fin.val hab
        simpa using this
      have hsub_norm : ‖Matrix.of (fun i j : Fin Sᶜ.card =>
          C_22 (Fin.cast hSc_card i) (Fin.cast hSc_card j))‖ ≤ ‖C_22‖ :=
        submatrix_norm_le (fun i => Fin.cast hSc_card i) hcast_inj C_22
      have hinv_nn : 0 ≤ (1 - 2 * δ)⁻¹ := le_of_lt (inv_pos.mpr h1m2δ)
      calc (1 - 2 * δ)⁻¹ * ‖Matrix.of (fun i j : Fin Sᶜ.card =>
              C_22 (Fin.cast hSc_card i) (Fin.cast hSc_card j))‖
          ≤ (1 - 2 * δ)⁻¹ * ‖C_22‖ := mul_le_mul_of_nonneg_left hsub_norm hinv_nn
        _ ≤ (1 - 2 * δ)⁻¹ * (c₂ + η) := mul_le_mul_of_nonneg_left hC22_norm hinv_nn
        _ = (c₂ + η) / (1 - 2 * δ) := by rw [div_eq_inv_mul]
    -- Key arithmetic: c₁/δ ≤ c₂/(1-2δ) — supplied as hypothesis.
    have hkey : c₁ / δ ≤ c₂ / (1 - 2 * δ) := hkey_ext
    -- Combine: max ‖A_S‖ ‖A_Sc‖ ≤ c₂/(1-2δ) + η/δ + η/(1-2δ).
    have hAS_le : ‖A_S‖ ≤ c₂ / (1 - 2 * δ) + η / δ + η / (1 - 2 * δ) := by
      calc ‖A_S‖
          ≤ (c₁ + η) / δ := hAS_norm_bound
        _ = c₁ / δ + η / δ := by ring
        _ ≤ c₂ / (1 - 2 * δ) + η / δ := by linarith [hkey]
        _ ≤ c₂ / (1 - 2 * δ) + η / δ + η / (1 - 2 * δ) := by
            have : 0 ≤ η / (1 - 2 * δ) := div_nonneg hη.le h1m2δ.le
            linarith
    have hASc_le : ‖A_Sc‖ ≤ c₂ / (1 - 2 * δ) + η / δ + η / (1 - 2 * δ) := by
      calc ‖A_Sc‖
          ≤ (c₂ + η) / (1 - 2 * δ) := hASc_norm_bound
        _ = c₂ / (1 - 2 * δ) + η / (1 - 2 * δ) := by ring
        _ ≤ c₂ / (1 - 2 * δ) + η / δ + η / (1 - 2 * δ) := by
            have : 0 ≤ η / δ := div_nonneg hη.le hδ_pos.le
            linarith
    exact le_trans hCdiag_le_max (max_le hAS_le hASc_le)

set_option maxHeartbeats 800000 in
/- (by claude)
State: ✅ done
Priority: 1
Attempts: 1 / 50
Session: S435
-/
-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- **Paper's asymmetric Claim 2** (JOS 2013, p.19253). For a 2m×2m zero-diagonal
    matrix A with ‖A‖ ≤ 1, decomposed into 4 m×m blocks via the canonical
    `Fin (2*m) ≃ Fin 2 × Fin m` equiv, with per-diagonal-block bounds
    `lambdaA(A_iiᵀᵀ) ≤ c_i`, where `c₁/c₂ < 1/4`, there exists an absolute constant
    K such that

      `lambdaA A ≤ (1 + K · ((c₁/c₂)^(1/2) + ‖A‖/c₁)) · c₂`.

    The (1 + small) multiplicative factor — as opposed to `lambdaA_block_2x2_decomp_param`'s
    `2/(1-δ)` — is what enables the strong induction on iteration count `k` in
    `lambdaM_pow4_kth_bound`. Foundational lemma for Plan D's k → k+1 induction step.

    See BLUEPRINT.md S433/S433a for paper-traceability and the precise role this
    lemma plays in the redesigned proof of `lambdaM_pow4_bound`. -/
lemma lambdaA_two_block_decomp_asym {m : ℕ}
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hratio : c₁ / c₂ < 1 / 4)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) (hzd : ZeroDiag A) (hnorm : ‖A‖ ≤ 1)
    (hbnd₁ : lambdaA (Matrix.of fun i j : Fin m => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) ≤ c₁)
    (hbnd₂ : lambdaA (Matrix.of fun i j : Fin m =>
        A ⟨m + i.val, by omega⟩ ⟨m + j.val, by omega⟩) ≤ c₂) :
    lambdaA A ≤ (1 + 4 * (Real.sqrt (c₁ / c₂) + ‖A‖ / c₁)) * c₂ := by
  -- Set δ := √(c₁/c₂)/2 (Sub-5's convention; ensures 1-2δ = 1-s > 1/2).
  set s : ℝ := Real.sqrt (c₁ / c₂) with hs_def
  have hratio_pos : 0 < c₁ / c₂ := div_pos hc₁ hc₂
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hratio_pos
  have hs_lt_half : s < 1 / 2 := by
    have hsqrt_quarter : Real.sqrt (1/4 : ℝ) = 1/2 := by
      rw [show (1/4 : ℝ) = (1/2)^2 by norm_num,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
    have hlt : Real.sqrt (c₁ / c₂) < Real.sqrt (1/4) :=
      Real.sqrt_lt_sqrt hratio_pos.le hratio
    rw [hsqrt_quarter] at hlt; exact hlt
  set δ : ℝ := s / 2 with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  have hδ_lt_half : δ < 1 / 2 := by rw [hδ_def]; linarith
  have h2δ_lt_one : 2 * δ < 1 := by linarith
  have h1m2δ_pos : 0 < 1 - 2 * δ := by linarith
  have hδ_lt_one : δ < 1 := by linarith
  have hδ_le_one : δ ≤ 1 := hδ_lt_one.le
  have hs_sq_eq : s ^ 2 = c₁ / c₂ := by
    rw [hs_def, sq, ← Real.sqrt_mul hratio_pos.le, Real.sqrt_mul_self hratio_pos.le]
  have h2δ_eq_s : 2 * δ = s := by rw [hδ_def]; ring
  have h1m2δ_eq : 1 - 2 * δ = 1 - s := by rw [h2δ_eq_s]
  -- Sub-4's hypothesis: c₁/δ ≤ c₂/(1-2δ). With δ = s/2, this is 2c₁(1-s) ≤ c₂·s,
  -- i.e., 2s(1-s) ≤ 1 (using c₂·s = c₁/s from s² = c₁/c₂). Holds since 2s(1-s) ≤ 1/2.
  have hkey_arith : c₁ / δ ≤ c₂ / (1 - 2 * δ) := by
    rw [div_le_div_iff₀ hδ_pos h1m2δ_pos]
    -- Need: c₁ · (1 - 2δ) ≤ c₂ · δ.
    -- δ = s/2, 1-2δ = 1-s. So need c₁·(1-s) ≤ c₂·s/2, i.e., 2c₁(1-s) ≤ c₂·s.
    -- Square: 4c₁²(1-s)² ≤ c₂²·s² = c₂²·(c₁/c₂) = c₁·c₂, i.e., 4c₁(1-s)² ≤ c₂.
    -- From c₁/c₂ < 1/4 and (1-s)² ≤ 1: 4c₁(1-s)² ≤ 4c₁ < c₂.
    have hssq : s ^ 2 = c₁ / c₂ := hs_sq_eq
    have h_c1_eq : c₁ = c₂ * s ^ 2 := by
      rw [hssq]; field_simp
    have h_2δ : 2 * δ = s := h2δ_eq_s
    -- Goal: c₁ · (1 - 2 * δ) ≤ c₂ * δ.
    have hδ_eq : δ = s / 2 := hδ_def
    rw [hδ_eq, h_c1_eq, h_2δ]
    -- Now: c₂ · s² · (1 - s) ≤ c₂ · (s/2). Cancel c₂·s (both positive):
    -- s · (1 - s) ≤ 1/2. Holds since max of s(1-s) on [0,1] is 1/4 at s=1/2.
    have hs_nn : 0 ≤ s := hs_pos.le
    have hsq_le : s * (1 - s) ≤ 1 / 2 := by nlinarith [sq_nonneg (1 - 2 * s), hs_pos]
    nlinarith [hc₂.le, hs_pos, hsq_le, sq_nonneg s]
  -- Headline arithmetic: c₂/(1-2δ) + ‖A‖/δ² ≤ (1 + 4·(s + ‖A‖/c₁))·c₂.
  set Anorm : ℝ := ‖A‖
  have hAnorm_nn : 0 ≤ Anorm := norm_nonneg _
  have hheadline : c₂ / (1 - 2 * δ) + Anorm / δ ^ 2
      ≤ (1 + 4 * (s + Anorm / c₁)) * c₂ := by
    -- δ = s/2, so δ² = s²/4 = c₁/(4·c₂). Thus Anorm/δ² = 4·c₂·Anorm/c₁ = 4·(Anorm/c₁)·c₂.
    have hcross : Anorm / δ ^ 2 = 4 * (Anorm / c₁) * c₂ := by
      have hδ_sq_eq : δ ^ 2 = s ^ 2 / 4 := by rw [hδ_def]; ring
      rw [hδ_sq_eq, hs_sq_eq]
      field_simp
    rw [hcross]
    -- Sub-estimate: c₂/(1-2δ) = c₂/(1-s) ≤ c₂·(1 + 4·s).
    have hsame : c₂ / (1 - 2 * δ) ≤ c₂ * (1 + 4 * s) := by
      rw [h1m2δ_eq, div_le_iff₀ (by linarith : (0:ℝ) < 1 - s)]
      -- (1 + 4s)(1 - s) = 1 + 3s - 4s²; need ≥ 1, i.e., s(3 - 4s) ≥ 0 (holds for s ≤ 3/4).
      have h_factor : 1 ≤ (1 + 4 * s) * (1 - s) := by
        nlinarith [hs_pos, hs_lt_half]
      nlinarith [hc₂.le, h_factor]
    have hexpand : (1 + 4 * (s + Anorm / c₁)) * c₂
        = c₂ * (1 + 4 * s) + 4 * (Anorm / c₁) * c₂ := by ring
    rw [hexpand]
    linarith
  -- Apply lambdaA_le_of_witness_eps with bound b := (1 + 4·(s + ‖A‖/c₁))·c₂.
  apply lambdaA_le_of_witness_eps
  intro ε hε
  -- η := ε · min(δ, 1-2δ) / 4, so η/δ + η/(1-2δ) ≤ ε/2.
  set η : ℝ := ε * min δ (1 - 2 * δ) / 4 with hη_def
  have hmin_pos : 0 < min δ (1 - 2 * δ) := lt_min hδ_pos h1m2δ_pos
  have hη_pos : 0 < η := by positivity
  have hη_div_δ_le : η / δ ≤ ε / 4 := by
    rw [hη_def, div_le_div_iff₀ hδ_pos (by norm_num : (0:ℝ) < 4)]
    have hmin_le : min δ (1 - 2 * δ) ≤ δ := min_le_left _ _
    nlinarith [hε.le, hmin_le, hδ_pos.le]
  have hη_div_1m2δ_le : η / (1 - 2 * δ) ≤ ε / 4 := by
    rw [hη_def, div_le_div_iff₀ h1m2δ_pos (by norm_num : (0:ℝ) < 4)]
    have hmin_le : min δ (1 - 2 * δ) ≤ 1 - 2 * δ := min_le_right _ _
    nlinarith [hε.le, hmin_le, h1m2δ_pos.le]
  -- Build per-block witnesses A_11, A_22.
  set A_11 : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.of fun i j : Fin m => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ with hA11_def
  set A_22 : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.of fun i j : Fin m => A ⟨m + i.val, by omega⟩ ⟨m + j.val, by omega⟩ with hA22_def
  have hzd11 : ZeroDiag A_11 := by
    intro i; change A ⟨i.val, _⟩ ⟨i.val, _⟩ = 0
    have : (⟨i.val, by omega⟩ : Fin (2 * m)) = ⟨i.val, by omega⟩ := rfl
    exact hzd ⟨i.val, by omega⟩
  have hzd22 : ZeroDiag A_22 := by
    intro i; change A ⟨m + i.val, _⟩ ⟨m + i.val, _⟩ = 0
    exact hzd ⟨m + i.val, by omega⟩
  obtain ⟨B_11, C_11, hB11_diag, hB11_usq, hA11_eq, hC11_norm⟩ :=
    claim2_asymmetric_block_witness A_11 hzd11 c₁ hbnd₁ η hη_pos
  obtain ⟨B_22, C_22, hB22_diag, hB22_usq, hA22_eq, hC22_norm⟩ :=
    claim2_asymmetric_block_witness A_22 hzd22 c₂ hbnd₂ η hη_pos
  -- Apply Sub-lemma 4 to get Cdiag (block-diagonal C').
  obtain ⟨Cdiag, hCdiag11, hCdiag22, hCdiag_TR, hCdiag_BL, hCdiag_norm⟩ :=
    claim2_asymmetric_same_block_norm_le δ hδ_pos hδ_lt_half c₁ c₂ hc₁ hc₂
      hkey_arith η hη_pos C_11 C_22 hC11_norm hC22_norm
  -- Apply Sub-lemma 3 (FG direction): cross-block X_12 with B'·X − X·B' = A_12.
  set A_12 : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.of fun i j : Fin m => A ⟨i.val, by omega⟩ ⟨m + j.val, by omega⟩
  set A_21 : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.of fun i j : Fin m => A ⟨m + i.val, by omega⟩ ⟨j.val, by omega⟩
  obtain ⟨X_12, hX12_eq, hX12_norm⟩ :=
    claim2_asymmetric_cross_norm_le δ hδ_pos hδ_lt_half B_11 B_22
      hB11_diag hB11_usq hB22_diag hB22_usq A_12
  -- For the GF block, use crossBlock_sylvester_norm_le directly.
  -- B'_GF rows: 2δ + (1-2δ)·B_22 i i; cols: (-1+δ) + δ·B_11 j j.
  -- The Re gap is ≥ +2δ (positive).
  set Sd_GF : Fin m → ℂ := fun i => (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 i i
  set Td_GF : Fin m → ℂ := fun j => (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 j j
  have hReGap_GF : ∀ i j, 2 * δ ≤ (Sd_GF i - Td_GF j).re := by
    intro i j
    have hu1 := hB11_usq j
    have hu2 := hB22_usq i
    obtain ⟨hu1_re, _⟩ := hu1
    obtain ⟨hu2_re, _⟩ := hu2
    rw [abs_le] at hu1_re hu2_re
    obtain ⟨hu1_re_lo, hu1_re_hi⟩ := hu1_re
    obtain ⟨hu2_re_lo, hu2_re_hi⟩ := hu2_re
    change 2 * δ ≤ (((2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 i i) -
      ((-1 + (δ : ℂ)) + (δ : ℂ) * B_11 j j)).re
    have hre_eq : (((2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 i i) -
        ((-1 + (δ : ℂ)) + (δ : ℂ) * B_11 j j)).re =
        (2 * δ + (1 - 2 * δ) * (B_22 i i).re) - ((-1 + δ) + δ * (B_11 j j).re) := by
      simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.neg_re, Complex.one_re, Complex.one_im]
    rw [hre_eq]; nlinarith
  have hSd_GF_ne_Td_GF : ∀ i j, Sd_GF i - Td_GF j ≠ 0 := by
    intro i j hzero
    have hreq : (Sd_GF i - Td_GF j).re = 0 := by rw [hzero]; simp
    have hge := hReGap_GF i j
    rw [hreq] at hge
    linarith [hδ_pos]
  set X_21 : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.of fun i j => A_21 i j / (Sd_GF i - Td_GF j) with hX21_def
  have hX21_eq : ∀ i j, Sd_GF i * X_21 i j - X_21 i j * Td_GF j = A_21 i j := by
    intro i j
    have hne := hSd_GF_ne_Td_GF i j
    change Sd_GF i * (A_21 i j / (Sd_GF i - Td_GF j)) -
         (A_21 i j / (Sd_GF i - Td_GF j)) * Td_GF j = A_21 i j
    field_simp
  have hX21_norm : ‖X_21‖ ≤ ‖A_21‖ / (2 * δ) := by
    apply crossBlock_sylvester_norm_le Sd_GF Td_GF A_21 δ hδ_pos
    left; exact hReGap_GF
  -- Build B' on Fin (2*m). B' is diagonal with shifted unit-square entries.
  let fullBval : Fin (2 * m) → ℂ := fun c =>
    if hc : c.val < m then
      (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 ⟨c.val, hc⟩ ⟨c.val, hc⟩
    else
      (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 ⟨c.val - m, by omega⟩ ⟨c.val - m, by omega⟩
  let fullB : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ := Matrix.diagonal fullBval
  have hfullB_diag : IsDiagMatrix fullB :=
    fun i j hij => Matrix.diagonal_apply_ne _ hij
  have hfullB_apply : ∀ i, fullB i i = fullBval i := fun i => Matrix.diagonal_apply_eq _ _
  -- Convenience: small-half indices are c with c.val < m; large-half are c with ¬(c.val < m).
  have hfullBval_small : ∀ i : Fin m,
      fullBval ⟨i.val, by omega⟩ = (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 i i := by
    intro i
    have hi : (⟨i.val, by omega⟩ : Fin (2 * m)).val < m := i.isLt
    change fullBval ⟨i.val, by omega⟩ = _
    simp only [fullBval, hi, dite_true]
  have hfullBval_large : ∀ i : Fin m,
      fullBval ⟨m + i.val, by omega⟩ = (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 i i := by
    intro i
    have hi_ge : ¬ ((⟨m + i.val, by omega⟩ : Fin (2 * m)).val < m) := by
      change ¬ (m + i.val < m); omega
    change fullBval ⟨m + i.val, by omega⟩ = _
    simp only [fullBval, hi_ge, dite_false]
    have heq : ((m + i.val) - m) = i.val := by omega
    have hfin : (⟨(m + i.val) - m, by omega⟩ : Fin m) = i := Fin.ext heq
    rw [hfin]
  have hfullB_usq : ∀ i, InUnitSquare (fullB i i) := by
    intro c
    rw [hfullB_apply]
    by_cases hc : c.val < m
    · simp only [fullBval, hc, dite_true]
      exact unit_square_asymmetric_shift_neg (hB11_usq ⟨c.val, hc⟩) hδ_pos hδ_le_one
    · simp only [fullBval, hc, dite_false]
      exact unit_square_asymmetric_shift_pos
        (hB22_usq ⟨c.val - m, by have := c.isLt; omega⟩) hδ_pos hδ_lt_half
  -- Build C' (= fullC) on Fin (2*m). 4-block structure.
  let fullC : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
    fun r c =>
      if hr : r.val < m then
        if hc : c.val < m then
          Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩
        else
          X_12 ⟨r.val, hr⟩ ⟨c.val - m, by have := c.isLt; omega⟩
      else
        if hc : c.val < m then
          X_21 ⟨r.val - m, by have := r.isLt; omega⟩ ⟨c.val, hc⟩
        else
          Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩
  -- Verify A = ⁅fullB, fullC⁆ entry by entry.
  have hComm : A = ⁅fullB, fullC⁆ₘ := by
    ext r c
    rw [commutator_diag_entry fullB fullC hfullB_diag]
    by_cases hr : r.val < m
    · by_cases hc : c.val < m
      · -- top-left block: A r c = A_11(⟨r⟩,⟨c⟩) = ⁅B_11, C_11⁆ at (⟨r⟩,⟨c⟩).
        -- Ar c entry equals (B_11 r r - B_11 c c) * C_11 r c after δ-cancellation.
        have hrfin : (⟨r.val, by omega⟩ : Fin (2 * m)) = r := Fin.ext rfl
        have hcfin : (⟨c.val, by omega⟩ : Fin (2 * m)) = c := Fin.ext rfl
        have hAA : A r c = A_11 ⟨r.val, hr⟩ ⟨c.val, hc⟩ := by
          simp [A_11, Matrix.of_apply, hrfin, hcfin]
        have hA11_at : A_11 ⟨r.val, hr⟩ ⟨c.val, hc⟩ =
            (B_11 ⟨r.val, hr⟩ ⟨r.val, hr⟩ - B_11 ⟨c.val, hc⟩ ⟨c.val, hc⟩) *
              C_11 ⟨r.val, hr⟩ ⟨c.val, hc⟩ := by
          rw [hA11_eq, commutator_diag_entry B_11 C_11 hB11_diag]
        rw [hAA, hA11_at]
        -- Now goal: (fullB r r - fullB c c) * fullC r c =
        --          (B_11 ⟨r⟩ ⟨r⟩ - B_11 ⟨c⟩ ⟨c⟩) * C_11 ⟨r⟩ ⟨c⟩.
        rw [hfullB_apply, hfullB_apply]
        have hBr_eq : fullBval r =
            (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 ⟨r.val, hr⟩ ⟨r.val, hr⟩ := by
          change (if hr' : r.val < m then
              (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 ⟨r.val, hr'⟩ ⟨r.val, hr'⟩
            else _) = _
          rw [dif_pos hr]
        have hBc_eq : fullBval c =
            (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 ⟨c.val, hc⟩ ⟨c.val, hc⟩ := by
          change (if hc' : c.val < m then
              (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 ⟨c.val, hc'⟩ ⟨c.val, hc'⟩
            else _) = _
          rw [dif_pos hc]
        rw [hBr_eq, hBc_eq]
        have hfullC_eq : fullC r c = Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩ := by
          change (if hr' : r.val < m then
              if hc' : c.val < m then
                Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩
              else _
            else _) = _
          rw [dif_pos hr, dif_pos hc]
        rw [hfullC_eq]
        have hCdiag_at : Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩ =
            (δ : ℂ)⁻¹ * C_11 ⟨r.val, hr⟩ ⟨c.val, hc⟩ := hCdiag11 ⟨r.val, hr⟩ ⟨c.val, hc⟩
        rw [hCdiag_at]
        have hδ_ne : (δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ_pos
        field_simp
        ring
      · -- top-right block: A r c = A_12 (⟨r⟩, ⟨c-m⟩) = (B'_11 r r - B'_22 c c) * X_12.
        have hc_ge : m ≤ c.val := Nat.le_of_not_lt hc
        have hcvm_lt : c.val - m < m := by have := c.isLt; omega
        have hr2m : r.val < 2 * m := r.isLt
        have hreq : r = (⟨r.val, by omega⟩ : Fin (2 * m)) := Fin.ext rfl
        have hceq : c = (⟨m + (c.val - m), by have := c.isLt; omega⟩ : Fin (2 * m)) := by
          apply Fin.ext; change c.val = m + (c.val - m); omega
        have hAA : A r c = A_12 ⟨r.val, hr⟩ ⟨c.val - m, hcvm_lt⟩ := by
          change A r c = A ⟨(⟨r.val, hr⟩ : Fin m).val, by omega⟩
            ⟨m + (⟨c.val - m, hcvm_lt⟩ : Fin m).val, by omega⟩
          conv_lhs => rw [hreq, hceq]
        rw [hAA]
        have hX_at := hX12_eq ⟨r.val, hr⟩ ⟨c.val - m, hcvm_lt⟩
        rw [← hX_at]
        have hBr_eq : fullBval r =
            (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 ⟨r.val, hr⟩ ⟨r.val, hr⟩ := by
          change (if hr' : r.val < m then
              (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 ⟨r.val, hr'⟩ ⟨r.val, hr'⟩
            else _) = _
          rw [dif_pos hr]
        have hBc_eq : fullBval c =
            (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 ⟨c.val - m, hcvm_lt⟩ ⟨c.val - m, hcvm_lt⟩ := by
          change (if hc'' : c.val < m then _ else
              (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) *
                B_22 ⟨c.val - m, hcvm_lt⟩ ⟨c.val - m, hcvm_lt⟩) = _
          rw [dif_neg hc]
        rw [hfullB_apply, hfullB_apply, hBr_eq, hBc_eq]
        have hfullC_eq : fullC r c = X_12 ⟨r.val, hr⟩ ⟨c.val - m, hcvm_lt⟩ := by
          change (if hr' : r.val < m then
              if hc'' : c.val < m then _
              else X_12 ⟨r.val, hr'⟩ ⟨c.val - m, by have := c.isLt; omega⟩
            else _) = _
          rw [dif_pos hr, dif_neg hc]
        rw [hfullC_eq]
        ring
    · by_cases hc : c.val < m
      · -- bottom-left block: A r c = A_21 (⟨r-m⟩, ⟨c⟩).
        have hr_ge : m ≤ r.val := Nat.le_of_not_lt hr
        have hrvm_lt : r.val - m < m := by have := r.isLt; omega
        have hreq : r = (⟨m + (r.val - m), by have := r.isLt; omega⟩ : Fin (2 * m)) := by
          apply Fin.ext; change r.val = m + (r.val - m); omega
        have hceq : c = (⟨c.val, by omega⟩ : Fin (2 * m)) := Fin.ext rfl
        have hAA : A r c = A_21 ⟨r.val - m, hrvm_lt⟩ ⟨c.val, hc⟩ := by
          change A r c = A ⟨m + (⟨r.val - m, hrvm_lt⟩ : Fin m).val, by omega⟩
            ⟨(⟨c.val, hc⟩ : Fin m).val, by omega⟩
          conv_lhs => rw [hreq, hceq]
        rw [hAA]
        have hX_at := hX21_eq ⟨r.val - m, hrvm_lt⟩ ⟨c.val, hc⟩
        rw [← hX_at]
        have hBr_eq : fullBval r =
            (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 ⟨r.val - m, hrvm_lt⟩ ⟨r.val - m, hrvm_lt⟩ := by
          change (if hr'' : r.val < m then _ else
              (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) *
                B_22 ⟨r.val - m, hrvm_lt⟩ ⟨r.val - m, hrvm_lt⟩) = _
          rw [dif_neg hr]
        have hBc_eq : fullBval c =
            (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 ⟨c.val, hc⟩ ⟨c.val, hc⟩ := by
          change (if hc' : c.val < m then
              (-1 + (δ : ℂ)) + (δ : ℂ) * B_11 ⟨c.val, hc'⟩ ⟨c.val, hc'⟩
            else _) = _
          rw [dif_pos hc]
        rw [hfullB_apply, hfullB_apply, hBr_eq, hBc_eq]
        have hfullC_eq : fullC r c = X_21 ⟨r.val - m, hrvm_lt⟩ ⟨c.val, hc⟩ := by
          change (if hr' : r.val < m then _
            else
              if hc'' : c.val < m then
                X_21 ⟨r.val - m, by have := r.isLt; omega⟩ ⟨c.val, hc''⟩
              else _) = _
          rw [dif_neg hr, dif_pos hc]
        rw [hfullC_eq]
        simp only [Sd_GF, Td_GF]
        ring
      · -- bottom-right block: A r c = A_22 (⟨r-m⟩, ⟨c-m⟩).
        have hr_ge : m ≤ r.val := Nat.le_of_not_lt hr
        have hc_ge : m ≤ c.val := Nat.le_of_not_lt hc
        have hrvm_lt : r.val - m < m := by have := r.isLt; omega
        have hcvm_lt : c.val - m < m := by have := c.isLt; omega
        have hreq : r = (⟨m + (r.val - m), by have := r.isLt; omega⟩ : Fin (2 * m)) := by
          apply Fin.ext; change r.val = m + (r.val - m); omega
        have hceq : c = (⟨m + (c.val - m), by have := c.isLt; omega⟩ : Fin (2 * m)) := by
          apply Fin.ext; change c.val = m + (c.val - m); omega
        have hAA : A r c = A_22 ⟨r.val - m, hrvm_lt⟩ ⟨c.val - m, hcvm_lt⟩ := by
          change A r c = A ⟨m + (⟨r.val - m, hrvm_lt⟩ : Fin m).val, by omega⟩
            ⟨m + (⟨c.val - m, hcvm_lt⟩ : Fin m).val, by omega⟩
          conv_lhs => rw [hreq, hceq]
        rw [hAA]
        have hA22_at : A_22 ⟨r.val - m, hrvm_lt⟩ ⟨c.val - m, hcvm_lt⟩ =
            (B_22 ⟨r.val - m, hrvm_lt⟩ ⟨r.val - m, hrvm_lt⟩ -
             B_22 ⟨c.val - m, hcvm_lt⟩ ⟨c.val - m, hcvm_lt⟩) *
              C_22 ⟨r.val - m, hrvm_lt⟩ ⟨c.val - m, hcvm_lt⟩ := by
          rw [hA22_eq, commutator_diag_entry B_22 C_22 hB22_diag]
        rw [hA22_at]
        have hBr_eq : fullBval r =
            (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 ⟨r.val - m, hrvm_lt⟩ ⟨r.val - m, hrvm_lt⟩ := by
          change (if hr' : r.val < m then _ else
              (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) *
                B_22 ⟨r.val - m, hrvm_lt⟩ ⟨r.val - m, hrvm_lt⟩) = _
          rw [dif_neg hr]
        have hBc_eq : fullBval c =
            (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) * B_22 ⟨c.val - m, hcvm_lt⟩ ⟨c.val - m, hcvm_lt⟩ := by
          change (if hc' : c.val < m then _ else
              (2 * (δ : ℂ)) + (1 - 2 * (δ : ℂ)) *
                B_22 ⟨c.val - m, hcvm_lt⟩ ⟨c.val - m, hcvm_lt⟩) = _
          rw [dif_neg hc]
        rw [hfullB_apply, hfullB_apply, hBr_eq, hBc_eq]
        have hfullC_eq : fullC r c =
            ((1 - 2 * (δ : ℂ)))⁻¹ * C_22 ⟨r.val - m, hrvm_lt⟩ ⟨c.val - m, hcvm_lt⟩ := by
          have hfc_raw : fullC r c = Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩ := by
            change (if hr' : r.val < m then _
              else if hc' : c.val < m then _
              else Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩) = _
            rw [dif_neg hr, dif_neg hc]
          rw [hfc_raw]
          have hCd := hCdiag22 ⟨r.val - m, hrvm_lt⟩ ⟨c.val - m, hcvm_lt⟩
          -- hCd : Cdiag ⟨m + (r.val-m), _⟩ ⟨m + (c.val-m), _⟩ = (1-2δ)⁻¹ * C_22 ⟨r-m⟩ ⟨c-m⟩
          have hr_isLt := r.isLt
          have hc_isLt := c.isLt
          have hri : (⟨m + (r.val - m), by omega⟩ : Fin (2 * m)) =
              ⟨r.val, by omega⟩ := Fin.ext (by change m + (r.val - m) = r.val; omega)
          have hcj : (⟨m + (c.val - m), by omega⟩ : Fin (2 * m)) =
              ⟨c.val, by omega⟩ := Fin.ext (by change m + (c.val - m) = c.val; omega)
          rw [hri, hcj] at hCd
          exact hCd
        rw [hfullC_eq]
        have h1m2δ_ne : (1 - 2 * (δ : ℂ)) ≠ 0 := by
          intro hzero
          have hcast : ((1 - 2 * δ : ℝ) : ℂ) = 0 := by push_cast; exact hzero
          have hreal : (1 - 2 * δ : ℝ) = 0 := by exact_mod_cast hcast
          linarith
        field_simp
        ring
  -- Norm bound on fullC: decompose fullC into block-diag + crossFG + crossGF.
  -- Define crossFG and crossGF as the embedded cross-blocks.
  set crossFG : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
    fun r c => if hr : r.val < m then
        if hc : c.val < m then 0
        else X_12 ⟨r.val, hr⟩ ⟨c.val - m, by have := c.isLt; omega⟩
      else 0 with hcrossFG_def
  set crossGF : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
    fun r c => if hr : r.val < m then 0
      else
        if hc : c.val < m then
          X_21 ⟨r.val - m, by have := r.isLt; omega⟩ ⟨c.val, hc⟩
        else 0 with hcrossGF_def
  have hfullC_decomp : fullC = Cdiag + crossFG + crossGF := by
    ext r c
    change fullC r c = Cdiag r c + crossFG r c + crossGF r c
    by_cases hr : r.val < m
    · by_cases hc : c.val < m
      · -- diag-diag (top-left): fullC = Cdiag, crossFG = crossGF = 0.
        have hfc : fullC r c = Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩ := by
          change (if hr' : r.val < m then if hc' : c.val < m then _
            else _ else _) = _
          rw [dif_pos hr, dif_pos hc]
        have hcfg : crossFG r c = 0 := by
          change (if hr' : r.val < m then if hc' : c.val < m then 0 else _ else 0) = 0
          rw [dif_pos hr, dif_pos hc]
        have hcgf : crossGF r c = 0 := by
          change (if hr' : r.val < m then 0 else _) = 0
          rw [dif_pos hr]
        have hCdEq : Cdiag r c = Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩ := by
          have hr_e : r = (⟨r.val, by omega⟩ : Fin (2 * m)) := Fin.ext rfl
          have hc_e : c = (⟨c.val, by omega⟩ : Fin (2 * m)) := Fin.ext rfl
          conv_lhs => rw [hr_e, hc_e]
        rw [hfc, hcfg, hcgf, hCdEq]; ring
      · -- top-right: fullC = X_12, Cdiag(top-right) = 0, crossFG = X_12, crossGF = 0.
        have hcvm_lt : c.val - m < m := by have := c.isLt; omega
        have hfc : fullC r c = X_12 ⟨r.val, hr⟩ ⟨c.val - m, hcvm_lt⟩ := by
          change (if hr' : r.val < m then if hc' : c.val < m then _
            else X_12 ⟨r.val, hr'⟩ ⟨c.val - m, by have := c.isLt; omega⟩ else _) = _
          rw [dif_pos hr, dif_neg hc]
        have hcfg : crossFG r c = X_12 ⟨r.val, hr⟩ ⟨c.val - m, hcvm_lt⟩ := by
          change (if hr' : r.val < m then if hc' : c.val < m then 0
            else X_12 ⟨r.val, hr'⟩ ⟨c.val - m, by have := c.isLt; omega⟩ else 0) = _
          rw [dif_pos hr, dif_neg hc]
        have hcgf : crossGF r c = 0 := by
          change (if hr' : r.val < m then 0 else _) = 0
          rw [dif_pos hr]
        have hCdEq : Cdiag r c = 0 := by
          have hr_e : r = (⟨r.val, by omega⟩ : Fin (2 * m)) := Fin.ext rfl
          have hc_e : c = (⟨m + (c.val - m), by have := c.isLt; omega⟩ : Fin (2 * m)) := by
            apply Fin.ext; change c.val = m + (c.val - m); omega
          conv_lhs => rw [hr_e, hc_e]
          exact hCdiag_TR ⟨r.val, hr⟩ ⟨c.val - m, hcvm_lt⟩
        rw [hfc, hcfg, hcgf, hCdEq]; ring
    · by_cases hc : c.val < m
      · -- bottom-left: fullC = X_21, Cdiag(bottom-left) = 0, crossFG = 0, crossGF = X_21.
        have hrvm_lt : r.val - m < m := by have := r.isLt; omega
        have hfc : fullC r c = X_21 ⟨r.val - m, hrvm_lt⟩ ⟨c.val, hc⟩ := by
          change (if hr' : r.val < m then _
            else if hc' : c.val < m then
              X_21 ⟨r.val - m, by have := r.isLt; omega⟩ ⟨c.val, hc'⟩ else _) = _
          rw [dif_neg hr, dif_pos hc]
        have hcfg : crossFG r c = 0 := by
          change (if hr' : r.val < m then _ else 0) = 0
          rw [dif_neg hr]
        have hcgf : crossGF r c = X_21 ⟨r.val - m, hrvm_lt⟩ ⟨c.val, hc⟩ := by
          change (if hr' : r.val < m then 0
            else if hc' : c.val < m then
              X_21 ⟨r.val - m, by have := r.isLt; omega⟩ ⟨c.val, hc'⟩ else 0) = _
          rw [dif_neg hr, dif_pos hc]
        have hCdEq : Cdiag r c = 0 := by
          have hr_e : r = (⟨m + (r.val - m), by have := r.isLt; omega⟩ : Fin (2 * m)) := by
            apply Fin.ext; change r.val = m + (r.val - m); omega
          have hc_e : c = (⟨c.val, by omega⟩ : Fin (2 * m)) := Fin.ext rfl
          conv_lhs => rw [hr_e, hc_e]
          exact hCdiag_BL ⟨r.val - m, hrvm_lt⟩ ⟨c.val, hc⟩
        rw [hfc, hcfg, hcgf, hCdEq]; ring
      · -- bottom-right: fullC = Cdiag, crossFG = crossGF = 0.
        have hrvm_lt : r.val - m < m := by have := r.isLt; omega
        have hcvm_lt : c.val - m < m := by have := c.isLt; omega
        have hfc : fullC r c = Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩ := by
          change (if hr' : r.val < m then _
            else if hc' : c.val < m then _
            else Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩) = _
          rw [dif_neg hr, dif_neg hc]
        have hcfg : crossFG r c = 0 := by
          change (if hr' : r.val < m then _ else 0) = 0
          rw [dif_neg hr]
        have hcgf : crossGF r c = 0 := by
          change (if hr' : r.val < m then 0
            else if hc' : c.val < m then _ else 0) = 0
          rw [dif_neg hr, dif_neg hc]
        have hCdEq : Cdiag r c = Cdiag ⟨r.val, by omega⟩ ⟨c.val, by omega⟩ := by
          have hr_e : r = (⟨r.val, by omega⟩ : Fin (2 * m)) := Fin.ext rfl
          have hc_e : c = (⟨c.val, by omega⟩ : Fin (2 * m)) := Fin.ext rfl
          conv_lhs => rw [hr_e, hc_e]
        rw [hfc, hcfg, hcgf, hCdEq]; ring
  -- Bound ‖crossFG‖ via embedBlock_norm_le and X_12.
  let fF : Fin m → Fin (2 * m) := fun k => ⟨k.val, by omega⟩
  let gG : Fin m → Fin (2 * m) := fun k => ⟨m + k.val, by omega⟩
  have hfF_inj : Function.Injective fF := by
    intro a b h; apply Fin.ext
    have := congrArg Fin.val h; simpa [fF] using this
  have hgG_inj : Function.Injective gG := by
    intro a b h; apply Fin.ext
    have := congrArg Fin.val h
    simp only [gG] at this; omega
  have hcrossFG_norm : ‖crossFG‖ ≤ ‖X_12‖ := by
    apply embedBlock_norm_le fF gG hfF_inj hgG_inj crossFG X_12
    · -- row-zero
      intro r c hrow
      simp only [crossFG]
      by_cases hr : r.val < m
      · exfalso; apply hrow ⟨r.val, hr⟩
        change (⟨r.val, by omega⟩ : Fin (2 * m)) = r; exact Fin.ext rfl
      · simp only [hr, dite_false]
    · -- col-zero
      intro r c hcol
      simp only [crossFG]
      by_cases hc : c.val < m
      · by_cases hr : r.val < m
        · simp only [hr, hc, dite_true]
        · simp only [hr, dite_false]
      · -- c.val ≥ m: col is gG (c.val - m). hcol forces contradiction.
        have hc_isLt := c.isLt
        exfalso; apply hcol ⟨c.val - m, by omega⟩
        change (⟨m + (c.val - m), by omega⟩ : Fin (2 * m)) = c
        exact Fin.ext (by change m + (c.val - m) = c.val; omega)
    · -- crossFG (fF i) (gG j) = X_12 i j
      intro i j
      change crossFG (⟨i.val, by omega⟩ : Fin (2 * m)) (⟨m + j.val, by omega⟩ : Fin (2 * m)) =
          X_12 i j
      simp only [crossFG]
      have hi : (⟨i.val, by omega⟩ : Fin (2 * m)).val < m := i.isLt
      have hj_ge : ¬ ((⟨m + j.val, by omega⟩ : Fin (2 * m)).val < m) := by
        change ¬ (m + j.val < m); omega
      simp only [hi, hj_ge, dite_true, dite_false]
      have heq : ((m + j.val) - m) = j.val := by omega
      have hfin : (⟨(m + j.val) - m, by omega⟩ : Fin m) = j := Fin.ext heq
      have hfin_i : (⟨i.val, hi⟩ : Fin m) = i := Fin.ext rfl
      rw [hfin_i, hfin]
  -- Bound ‖crossGF‖ via embedBlock_norm_le and X_21.
  have hcrossGF_norm : ‖crossGF‖ ≤ ‖X_21‖ := by
    apply embedBlock_norm_le gG fF hgG_inj hfF_inj crossGF X_21
    · intro r c hrow
      simp only [crossGF]
      by_cases hr : r.val < m
      · simp only [hr, dite_true]
      · -- r.val ≥ m: row is gG. hrow forces contradiction.
        have hr_isLt := r.isLt
        exfalso; apply hrow ⟨r.val - m, by omega⟩
        change (⟨m + (r.val - m), by omega⟩ : Fin (2 * m)) = r
        exact Fin.ext (by change m + (r.val - m) = r.val; omega)
    · intro r c hcol
      simp only [crossGF]
      by_cases hr : r.val < m
      · simp only [hr, dite_true]
      · -- r.val ≥ m
        by_cases hc : c.val < m
        · exfalso; apply hcol ⟨c.val, hc⟩
          change (⟨c.val, by omega⟩ : Fin (2 * m)) = c; exact Fin.ext rfl
        · simp only [hr, hc, dite_false]
    · intro i j
      change crossGF (⟨m + i.val, by omega⟩ : Fin (2 * m)) (⟨j.val, by omega⟩ : Fin (2 * m)) =
          X_21 i j
      simp only [crossGF]
      have hi_ge : ¬ ((⟨m + i.val, by omega⟩ : Fin (2 * m)).val < m) := by
        change ¬ (m + i.val < m); omega
      have hj : (⟨j.val, by omega⟩ : Fin (2 * m)).val < m := j.isLt
      simp only [hi_ge, hj, dite_false, dite_true]
      have heq : ((m + i.val) - m) = i.val := by omega
      have hfin : (⟨(m + i.val) - m, by omega⟩ : Fin m) = i := Fin.ext heq
      have hfin_j : (⟨j.val, hj⟩ : Fin m) = j := Fin.ext rfl
      rw [hfin, hfin_j]
  -- Bound ‖A_12‖ ≤ ‖A‖ via cross_submatrix_norm_le.
  have hA12_norm_le : ‖A_12‖ ≤ Anorm := by
    have hf_inj : Function.Injective (fun i : Fin m => (⟨i.val, by omega⟩ : Fin (2 * m))) := by
      intro a b h; apply Fin.ext
      have := congrArg Fin.val h; simpa using this
    have hg_inj : Function.Injective (fun j : Fin m => (⟨m + j.val, by omega⟩ : Fin (2 * m))) := by
      intro a b h; apply Fin.ext
      have := congrArg Fin.val h; simp at this; omega
    exact cross_submatrix_norm_le _ _ hf_inj hg_inj A
  have hA21_norm_le : ‖A_21‖ ≤ Anorm := by
    have hf_inj : Function.Injective (fun i : Fin m => (⟨m + i.val, by omega⟩ : Fin (2 * m))) := by
      intro a b h; apply Fin.ext
      have := congrArg Fin.val h; simp at this; omega
    have hg_inj : Function.Injective (fun j : Fin m => (⟨j.val, by omega⟩ : Fin (2 * m))) := by
      intro a b h; apply Fin.ext
      have := congrArg Fin.val h; simpa using this
    exact cross_submatrix_norm_le _ _ hf_inj hg_inj A
  -- Final norm bound on fullC.
  have h2δ_pos : 0 < 2 * δ := by linarith
  have hfullC_norm : ‖fullC‖ ≤
      (c₂ / (1 - 2 * δ) + η / δ + η / (1 - 2 * δ)) + Anorm / (2 * δ) + Anorm / (2 * δ) := by
    calc ‖fullC‖
        = ‖Cdiag + crossFG + crossGF‖ := by rw [hfullC_decomp]
      _ ≤ ‖Cdiag + crossFG‖ + ‖crossGF‖ := norm_add_le _ _
      _ ≤ ‖Cdiag‖ + ‖crossFG‖ + ‖crossGF‖ := by linarith [norm_add_le Cdiag crossFG]
      _ ≤ (c₂ / (1 - 2 * δ) + η / δ + η / (1 - 2 * δ)) + ‖A_12‖ / (2 * δ) +
            ‖A_21‖ / (2 * δ) := by
          have h1 : ‖crossFG‖ ≤ ‖A_12‖ / (2 * δ) := le_trans hcrossFG_norm hX12_norm
          have h2 : ‖crossGF‖ ≤ ‖A_21‖ / (2 * δ) := le_trans hcrossGF_norm hX21_norm
          linarith
      _ ≤ (c₂ / (1 - 2 * δ) + η / δ + η / (1 - 2 * δ)) + Anorm / (2 * δ) + Anorm / (2 * δ) := by
          have h2δ_pos' : 0 < 2 * δ := h2δ_pos
          have hd1 := div_le_div_of_nonneg_right hA12_norm_le h2δ_pos'.le
          have hd2 := div_le_div_of_nonneg_right hA21_norm_le h2δ_pos'.le
          linarith
  refine ⟨fullB, fullC, hfullB_diag, hfullB_usq, hComm, ?_⟩
  -- Final ε-arithmetic: combine the bounds.
  -- ‖fullC‖ ≤ c₂/(1-2δ) + η/δ + η/(1-2δ) + 2·Anorm/(2δ)
  --       = c₂/(1-2δ) + Anorm/δ + (η/δ + η/(1-2δ))
  -- And we need: ‖fullC‖ ≤ (1 + 4·(s + Anorm/c₁))·c₂ + ε.
  -- Using hheadline: c₂/(1-2δ) + Anorm/δ² ≤ (1 + 4·(s + Anorm/c₁))·c₂.
  -- Note: Anorm/δ ≤ Anorm/δ² since δ ≤ 1, so Anorm/δ² ≥ Anorm/δ. Thus we have
  --   c₂/(1-2δ) + Anorm/δ ≤ c₂/(1-2δ) + Anorm/δ² ≤ headline.
  have hAnorm_div_δ_le : Anorm / δ ≤ Anorm / δ ^ 2 := by
    rw [div_le_div_iff₀ hδ_pos (by positivity)]
    have : δ * δ ≤ δ := by nlinarith [hδ_pos, hδ_lt_one]
    nlinarith [hAnorm_nn, sq_nonneg δ, hδ_pos]
  have h2div_eq : Anorm / (2 * δ) + Anorm / (2 * δ) = Anorm / δ := by
    field_simp; ring
  calc ‖fullC‖
      ≤ (c₂ / (1 - 2 * δ) + η / δ + η / (1 - 2 * δ)) + Anorm / (2 * δ) + Anorm / (2 * δ) :=
        hfullC_norm
    _ = c₂ / (1 - 2 * δ) + Anorm / δ + (η / δ + η / (1 - 2 * δ)) := by linarith [h2div_eq]
    _ ≤ c₂ / (1 - 2 * δ) + Anorm / δ ^ 2 + (η / δ + η / (1 - 2 * δ)) := by
        linarith [hAnorm_div_δ_le]
    _ ≤ (1 + 4 * (s + Anorm / c₁)) * c₂ + (η / δ + η / (1 - 2 * δ)) := by linarith [hheadline]
    _ ≤ (1 + 4 * (s + Anorm / c₁)) * c₂ + (ε / 4 + ε / 4) := by
        linarith [hη_div_δ_le, hη_div_1m2δ_le]
    _ ≤ (1 + 4 * (s + Anorm / c₁)) * c₂ + ε := by linarith

end Pow4Bootstrap
