import CommutatorTheorem.Defs
import CommutatorTheorem.Epsilon.SylvesterBound
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Rosenblum's Theorem and Spectral Separation Bounds

This file formalizes Rosenblum's operator equation theorem (1956) and the
spectral separation bound for diagonal matrices with entries in the lattice Λ.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra

open CommutatorTheorem Polynomial

namespace CommutatorTheorem

/-! ## Rosenblum's theorem -/

/-- The Sylvester linear map L(X) = S * X - X * T -/
private noncomputable def sylvesterMap {n : ℕ} (S T : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := S * X - X * T
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by
    simp only [RingHom.id_apply]
    have h1 : S * (c • X) = c • (S * X) := by
      ext i j; simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm c]
    have h2 : (c • X) * T = c • (X * T) := by
      ext i j; simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc c]
    rw [h1, h2, smul_sub]

/-- If SX = XT then S^k X = X T^k for all k -/
private lemma pow_commute_of_commute {n : ℕ} (S T X : Matrix (Fin n) (Fin n) ℂ)
    (h : S * X = X * T) : ∀ k : ℕ, S ^ k * X = X * T ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc S ^ (k + 1) * X = S ^ k * S * X := by rw [pow_succ]
      _ = S ^ k * (S * X) := by rw [mul_assoc]
      _ = S ^ k * (X * T) := by rw [h]
      _ = S ^ k * X * T := by rw [mul_assoc]
      _ = X * T ^ k * T := by rw [ih]
      _ = X * (T ^ k * T) := by rw [mul_assoc]
      _ = X * T ^ (k + 1) := by rw [← pow_succ]

/-- If SX = XT then p(S) X = X p(T) for any polynomial p -/
private lemma aeval_commute_of_commute {n : ℕ} (S T X : Matrix (Fin n) (Fin n) ℂ)
    (h : S * X = X * T) (p : Polynomial ℂ) :
    (aeval S) p * X = X * (aeval T) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, add_mul, mul_add, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    have hpow : S ^ n * X = X * T ^ n := pow_commute_of_commute S T X h n
    calc a • (S ^ n * X) = a • (X * T ^ n) := by rw [hpow]
      _ = X * (a • T ^ n) := by
          ext i j; simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm a]

/-- Rosenblum 1956: if the spectra of S and T are disjoint, then the operator equation
    SX - XT = A has a unique solution X.
    Proof via Cayley-Hamilton: if SX = XT then p(S)X = Xp(T) for any polynomial p;
    taking p = χ_T gives χ_T(S)X = 0, and disjoint spectra imply χ_T(S) is invertible. -/
theorem rosenblum_solution {n : ℕ} (S T A : Matrix (Fin n) (Fin n) ℂ)
    (hSep : Disjoint (spectrum ℂ S) (spectrum ℂ T)) :
    ∃! X : Matrix (Fin n) (Fin n) ℂ, S * X - X * T = A := by
  -- Handle n = 0 case: the matrix space is trivial
  by_cases hn : n = 0
  · subst hn
    exact ⟨0, by ext i; exact Fin.elim0 i, fun Y _ => by ext i; exact Fin.elim0 i⟩
  -- Now n ≥ 1
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  haveI : Nontrivial (Matrix (Fin n) (Fin n) ℂ) := Matrix.nonempty
  let L := sylvesterMap S T
  suffices hbij : Function.Bijective L by
    exact (Function.bijective_iff_existsUnique L).mp hbij A
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro X hX
    simp only [L, sylvesterMap, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk] at hX
    have hcomm : S * X = X * T := sub_eq_zero.mp hX
    have hCH : (aeval T) T.charpoly = 0 := Matrix.aeval_self_charpoly T
    have hpSX : (aeval S) T.charpoly * X = X * (aeval T) T.charpoly :=
      aeval_commute_of_commute S T X hcomm T.charpoly
    rw [hCH, mul_zero] at hpSX
    -- Show charpoly(T)(S) is invertible using spectrum argument
    have hunit : IsUnit ((Polynomial.aeval S) T.charpoly) := by
      rw [← spectrum.zero_notMem_iff ℂ]
      rw [spectrum.map_polynomial_aeval_of_nonempty (a := S) (p := T.charpoly)]
      · rintro ⟨s, hs, heval⟩
        have hs_spec_T : s ∈ spectrum ℂ T := by
          rwa [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot]
        exact Set.disjoint_iff.mp hSep ⟨hs, hs_spec_T⟩
      · exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ S
    obtain ⟨u, hu⟩ := hunit
    have hux : (u : Matrix (Fin n) (Fin n) ℂ) * X = 0 := hu ▸ hpSX
    have : X = (u⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ).val * (u.val * X) := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [this, hux, mul_zero]
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

/-! ## Spectral separation for matrices with entries in Λ -/

/-- Minimum distance between distinct elements in cornerSet is 2. -/
lemma cornerSet_min_dist (z₁ z₂ : ℂ)
    (h₁ : z₁ ∈ (cornerSet : Set ℂ))
    (h₂ : z₂ ∈ (cornerSet : Set ℂ))
    (hne : z₁ ≠ z₂) :
    2 ≤ ‖z₁ - z₂‖ := by
  simp only [cornerSet, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl | rfl <;>
    rcases h₂ with rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl hne) <;>
    simp only [Complex.norm_eq_sqrt_sq_add_sq,
      Complex.sub_re, Complex.sub_im] <;>
    (apply Real.le_sqrt_of_sq_le; norm_num)

/-- Corner re values are ±1. -/
private lemma cornerSet_re (δ : ℂ) (hδ : δ ∈ (cornerSet : Set ℂ)) :
    δ.re = 1 ∨ δ.re = -1 := by
  simp only [cornerSet, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
  rcases hδ with rfl | rfl | rfl | rfl <;> simp

/-- Corner im values are ±1. -/
private lemma cornerSet_im (δ : ℂ) (hδ : δ ∈ (cornerSet : Set ℂ)) :
    δ.im = 1 ∨ δ.im = -1 := by
  simp only [cornerSet, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
  rcases hδ with rfl | rfl | rfl | rfl <;> simp

/-- For w ∈ Lambda ε n, |w.re| * ((1+ε)/2) ≤ 1 - ((1-ε)/2)^(n+1). -/
lemma Lambda_abs_re_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ (n : ℕ) (w : ℂ), w ∈ (Lambda ε n : Set ℂ) →
    |w.re| * ((1 + ε) / 2) ≤ 1 - ((1 - ε) / 2) ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro w hw
    simp only [Lambda, cornerSet, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> simp <;> nlinarith
  | succ n ih =>
    intro w hw
    simp only [Lambda, Finset.coe_biUnion, Finset.coe_image,
      Set.mem_iUnion, Set.mem_image] at hw
    obtain ⟨δ, hδmem, z, hz, rfl⟩ := hw
    have hre : (((1 - ↑ε) / 2 : ℂ) * z + δ).re = (1 - ε) / 2 * z.re + δ.re := by
      simp [Complex.mul_re, Complex.sub_re]
    rw [hre]
    have hδ_re : |δ.re| ≤ 1 := by
      rcases cornerSet_re δ (by exact_mod_cast hδmem) with h | h <;> simp [h]
    have hr_pos : 0 ≤ (1 - ε) / 2 := by linarith
    have hε2_pos : 0 ≤ (1 + ε) / 2 := by linarith
    calc |((1 - ε) / 2) * z.re + δ.re| * ((1 + ε) / 2)
        ≤ ((1 - ε) / 2 * |z.re| + |δ.re|) * ((1 + ε) / 2) := by
          apply mul_le_mul_of_nonneg_right _ hε2_pos
          calc |((1 - ε) / 2) * z.re + δ.re|
              ≤ |((1 - ε) / 2) * z.re| + |δ.re| := abs_add_le _ _
            _ = (1 - ε) / 2 * |z.re| + |δ.re| := by rw [abs_mul, abs_of_nonneg hr_pos]
      _ ≤ ((1 - ε) / 2 * |z.re| + 1) * ((1 + ε) / 2) := by
          apply mul_le_mul_of_nonneg_right _ hε2_pos; linarith
      _ = (1 - ε) / 2 * (|z.re| * ((1 + ε) / 2)) + (1 + ε) / 2 := by ring
      _ ≤ (1 - ε) / 2 * (1 - ((1 - ε) / 2) ^ (n + 1)) + (1 + ε) / 2 := by
          linarith [mul_le_mul_of_nonneg_left (ih z hz) hr_pos]
      _ = 1 - ((1 - ε) / 2) ^ (n + 1 + 1) := by ring

/-- For w ∈ Lambda ε n, |w.im| * ((1+ε)/2) ≤ 1 - ((1-ε)/2)^(n+1). -/
lemma Lambda_abs_im_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ (n : ℕ) (w : ℂ), w ∈ (Lambda ε n : Set ℂ) →
    |w.im| * ((1 + ε) / 2) ≤ 1 - ((1 - ε) / 2) ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro w hw
    simp only [Lambda, cornerSet, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> simp <;> nlinarith
  | succ n ih =>
    intro w hw
    simp only [Lambda, Finset.coe_biUnion, Finset.coe_image,
      Set.mem_iUnion, Set.mem_image] at hw
    obtain ⟨δ, hδmem, z, hz, rfl⟩ := hw
    have him : (((1 - ↑ε) / 2 : ℂ) * z + δ).im = (1 - ε) / 2 * z.im + δ.im := by
      simp [Complex.mul_im, Complex.sub_im]
    rw [him]
    have hδ_im : |δ.im| ≤ 1 := by
      rcases cornerSet_im δ (by exact_mod_cast hδmem) with h | h <;> simp [h]
    have hr_pos : 0 ≤ (1 - ε) / 2 := by linarith
    have hε2_pos : 0 ≤ (1 + ε) / 2 := by linarith
    calc |((1 - ε) / 2) * z.im + δ.im| * ((1 + ε) / 2)
        ≤ ((1 - ε) / 2 * |z.im| + |δ.im|) * ((1 + ε) / 2) := by
          apply mul_le_mul_of_nonneg_right _ hε2_pos
          calc |((1 - ε) / 2) * z.im + δ.im|
              ≤ |((1 - ε) / 2) * z.im| + |δ.im| := abs_add_le _ _
            _ = (1 - ε) / 2 * |z.im| + |δ.im| := by rw [abs_mul, abs_of_nonneg hr_pos]
      _ ≤ ((1 - ε) / 2 * |z.im| + 1) * ((1 + ε) / 2) := by
          apply mul_le_mul_of_nonneg_right _ hε2_pos; linarith
      _ = (1 - ε) / 2 * (|z.im| * ((1 + ε) / 2)) + (1 + ε) / 2 := by ring
      _ ≤ (1 - ε) / 2 * (1 - ((1 - ε) / 2) ^ (n + 1)) + (1 + ε) / 2 := by
          linarith [mul_le_mul_of_nonneg_left (ih z hz) hr_pos]
      _ = 1 - ((1 - ε) / 2) ^ (n + 1 + 1) := by ring

/-- Correct level-dependent separation bound for the recursive lattice.
    Distinct elements of Λ_n(ε) are separated by at least 2·((1-ε)/2)^n,
    provided 0 < ε < 1. This is the correct bound that shrinks geometrically
    with the level, unlike the incorrect fixed bound ε/√2. -/
private lemma lambda_sep_level {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ (n : ℕ) (z₁ z₂ : ℂ),
    z₁ ∈ (Lambda ε n : Set ℂ) →
    z₂ ∈ (Lambda ε n : Set ℂ) →
    z₁ ≠ z₂ →
    2 * ((1 - ε) / 2) ^ n ≤ ‖z₁ - z₂‖ := by
  intro n
  induction n with
  | zero =>
    intro z₁ z₂ h₁ h₂ hne
    simp only [Lambda] at h₁ h₂
    simp only [pow_zero, mul_one]
    exact cornerSet_min_dist z₁ z₂ h₁ h₂ hne
  | succ n ih =>
    intro z₁ z₂ h₁ h₂ hne
    -- z₁ = ((1-ε)/2)*w₁ + δ₁, z₂ = ((1-ε)/2)*w₂ + δ₂
    -- with w₁, w₂ ∈ Lambda ε n, δ₁, δ₂ ∈ cornerSet
    simp only [Lambda, Finset.coe_biUnion, Finset.coe_image,
      Set.mem_iUnion, Set.mem_image] at h₁ h₂
    obtain ⟨δ₁, hδ₁mem, w₁, hw₁, rfl⟩ := h₁
    obtain ⟨δ₂, hδ₂mem, w₂, hw₂, rfl⟩ := h₂
    -- Case split on whether δ₁ = δ₂
    by_cases hδ : δ₁ = δ₂
    · -- Same corner: distance = |(1-ε)/2| · ‖w₁ - w₂‖
      subst hδ
      have hne_w : w₁ ≠ w₂ := by
        intro heq; apply hne; rw [heq]
      -- z₁ - z₂ = ((1-ε)/2) * (w₁ - w₂)
      have hdiff : ((1 - ε) / 2 : ℂ) * w₁ + δ₁ -
          (((1 - ε) / 2 : ℂ) * w₂ + δ₁) =
          ((1 - ε) / 2 : ℂ) * (w₁ - w₂) := by ring
      rw [hdiff, norm_mul]
      have hcast : ((1 - ε) / 2 : ℂ) = (((1 - ε) / 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, Complex.norm_of_nonneg (by linarith)]
      have hpos : (0 : ℝ) < (1 - ε) / 2 := by linarith
      rw [show 2 * ((1 - ε) / 2) ^ (n + 1) =
        (1 - ε) / 2 * (2 * ((1 - ε) / 2) ^ n) from by ring]
      exact mul_le_mul_of_nonneg_left
        (ih w₁ w₂ hw₁ hw₂ hne_w) (le_of_lt hpos)
    · -- Different corners: use Re/Im reverse triangle inequality
      -- Rewrite the difference
      have hdiff : (1 - ↑ε) / 2 * w₁ + δ₁ - ((1 - ↑ε) / 2 * w₂ + δ₂) =
          ((1 - ↑ε) / 2 : ℂ) * (w₁ - w₂) + (δ₁ - δ₂) := by ring
      rw [hdiff]
      have hr_nn : (0 : ℝ) ≤ (1 - ε) / 2 := by linarith
      -- Since δ₁ ≠ δ₂ ∈ {±1±i}, either Re or Im differs by 2
      by_cases hre_eq : δ₁.re = δ₂.re
      · -- Re equal ⟹ Im must differ
        have him_ne : δ₁.im ≠ δ₂.im := by
          intro h; exact hδ (Complex.ext hre_eq h)
        have him_diff : |δ₁.im - δ₂.im| = 2 := by
          rcases cornerSet_im δ₁ hδ₁mem with h1 | h1 <;>
            rcases cornerSet_im δ₂ hδ₂mem with h2 | h2 <;>
            simp [h1, h2] at him_ne ⊢ <;> norm_num
        -- ‖a‖ ≥ |Im(a)|
        calc 2 * ((1 - ε) / 2) ^ (n + 1)
            ≤ |(((1 - ↑ε) / 2 : ℂ) * (w₁ - w₂) + (δ₁ - δ₂)).im| := by
              -- Im(r*(w₁-w₂) + (δ₁-δ₂)) = r*(w₁.im-w₂.im) + (δ₁.im-δ₂.im)
              have him_eq : (((1 - ↑ε) / 2 : ℂ) * (w₁ - w₂) + (δ₁ - δ₂)).im =
                  (1 - ε) / 2 * (w₁.im - w₂.im) + (δ₁.im - δ₂.im) := by
                simp [Complex.mul_im, Complex.sub_im, Complex.add_im]
              rw [him_eq]
              -- Reverse triangle: |a+b| ≥ |b| - |a|
              suffices h : 2 * ((1 - ε) / 2) ^ (n + 1) ≤
                  |δ₁.im - δ₂.im| - (1 - ε) / 2 * |w₁.im - w₂.im| by
                have h_rev : |δ₁.im - δ₂.im| - |(1 - ε) / 2 * (w₁.im - w₂.im)| ≤
                    |(1 - ε) / 2 * (w₁.im - w₂.im) + (δ₁.im - δ₂.im)| := by
                  have := abs_sub_abs_le_abs_sub (δ₁.im - δ₂.im)
                      (-(((1 - ε) / 2) * (w₁.im - w₂.im)))
                  rwa [abs_neg, show δ₁.im - δ₂.im - -(((1 - ε) / 2) * (w₁.im - w₂.im)) =
                    (1 - ε) / 2 * (w₁.im - w₂.im) + (δ₁.im - δ₂.im) from by ring] at this
                rw [abs_mul, abs_of_nonneg hr_nn] at h_rev; linarith
              rw [him_diff]
              -- |w₁.im - w₂.im| ≤ |w₁.im| + |w₂.im|
              have h_sub : |w₁.im - w₂.im| ≤ |w₁.im| + |w₂.im| := by
                have := abs_sub_le w₁.im 0 w₂.im
                simp only [sub_zero, zero_sub, abs_neg] at this; exact this
              -- From Lambda_abs_im_le: r*(|w₁.im|+|w₂.im|) ≤ 2*(1-r^{n+1})
              have h1 := Lambda_abs_im_le hε hε1 n w₁ hw₁
              have h2 := Lambda_abs_im_le hε hε1 n w₂ hw₂
              nlinarith [abs_nonneg w₁.im, abs_nonneg w₂.im]
          _ ≤ ‖((1 - ↑ε) / 2 : ℂ) * (w₁ - w₂) + (δ₁ - δ₂)‖ :=
              Complex.abs_im_le_norm _
      · -- Re parts differ ⟹ |Re(δ₁-δ₂)| = 2
        have hre_diff : |δ₁.re - δ₂.re| = 2 := by
          rcases cornerSet_re δ₁ hδ₁mem with h1 | h1 <;>
            rcases cornerSet_re δ₂ hδ₂mem with h2 | h2 <;>
            simp [h1, h2] at hre_eq ⊢ <;> norm_num
        -- ‖a‖ ≥ |Re(a)|
        calc 2 * ((1 - ε) / 2) ^ (n + 1)
            ≤ |(((1 - ↑ε) / 2 : ℂ) * (w₁ - w₂) + (δ₁ - δ₂)).re| := by
              have hre_eq : (((1 - ↑ε) / 2 : ℂ) * (w₁ - w₂) + (δ₁ - δ₂)).re =
                  (1 - ε) / 2 * (w₁.re - w₂.re) + (δ₁.re - δ₂.re) := by
                simp [Complex.mul_re, Complex.sub_re, Complex.add_re]
              rw [hre_eq]
              suffices h : 2 * ((1 - ε) / 2) ^ (n + 1) ≤
                  |δ₁.re - δ₂.re| - (1 - ε) / 2 * |w₁.re - w₂.re| by
                have h_rev : |δ₁.re - δ₂.re| - |(1 - ε) / 2 * (w₁.re - w₂.re)| ≤
                    |(1 - ε) / 2 * (w₁.re - w₂.re) + (δ₁.re - δ₂.re)| := by
                  have := abs_sub_abs_le_abs_sub (δ₁.re - δ₂.re)
                      (-(((1 - ε) / 2) * (w₁.re - w₂.re)))
                  rwa [abs_neg, show δ₁.re - δ₂.re - -(((1 - ε) / 2) * (w₁.re - w₂.re)) =
                    (1 - ε) / 2 * (w₁.re - w₂.re) + (δ₁.re - δ₂.re) from by ring] at this
                rw [abs_mul, abs_of_nonneg hr_nn] at h_rev; linarith
              rw [hre_diff]
              have h_sub : |w₁.re - w₂.re| ≤ |w₁.re| + |w₂.re| := by
                have := abs_sub_le w₁.re 0 w₂.re
                simp only [sub_zero, zero_sub, abs_neg] at this; exact this
              have h1 := Lambda_abs_re_le hε hε1 n w₁ hw₁
              have h2 := Lambda_abs_re_le hε hε1 n w₂ hw₂
              nlinarith [abs_nonneg w₁.re, abs_nonneg w₂.re]
          _ ≤ ‖((1 - ↑ε) / 2 : ℂ) * (w₁ - w₂) + (δ₁ - δ₂)‖ :=
              Complex.abs_re_le_norm _

/-- For a diagonal matrix B with entries in Λ_n(ε), any two distinct eigenvalues
    are separated by at least 2·((1-ε)/2)^n. -/
lemma lambda_spectrum_sep {n m : ℕ} (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (B : Matrix (Fin m) (Fin m) ℂ)
    (hDiag : IsDiagMatrix B)
    (hSpec : ∀ i, B i i ∈ (Lambda ε n : Set ℂ)) :
    ∀ μ₁ ∈ spectrum ℂ B, ∀ μ₂ ∈ spectrum ℂ B, μ₁ ≠ μ₂ →
      2 * ((1 - ε) / 2) ^ n ≤ ‖μ₁ - μ₂‖ := by
  intro μ₁ hμ₁ μ₂ hμ₂ hne
  -- Convert local IsDiagMatrix to Mathlib's Matrix.IsDiag
  have hBdiag : B.IsDiag := fun i j hij => hDiag i j hij
  -- B = Matrix.diagonal (Matrix.diag B) since B is diagonal
  have hBeq : Matrix.diagonal B.diag = B := (Matrix.isDiag_iff_diagonal_diag B).mp hBdiag
  -- spectrum ℂ (Matrix.diagonal d) = Set.range d
  rw [← hBeq, spectrum_diagonal] at hμ₁ hμ₂
  -- Extract indices; μ₁ = B.diag i = B i i and μ₂ = B.diag j = B j j
  obtain ⟨i, rfl⟩ := hμ₁
  obtain ⟨j, rfl⟩ := hμ₂
  simp only [Matrix.diag_apply] at hne ⊢
  exact lambda_sep_level hε hε1 n (B i i) (B j j) (hSpec i) (hSpec j) hne

/-! ## Helper lemmas for Sylvester equations with diagonal matrices -/

/-- When both S and T are diagonal with S_{ii} ≠ T_{jj} for all i,j,
    the entrywise formula X_{ij} = A_{ij}/(S_{ii} - T_{jj}) solves SX - XT = A. -/
lemma sylvester_diag_diag_solution {m : ℕ} (S T A : Matrix (Fin m) (Fin m) ℂ)
    (hS : IsDiagMatrix S) (hT : IsDiagMatrix T)
    (hST : ∀ i j, S i i ≠ T j j) :
    let X : Matrix (Fin m) (Fin m) ℂ := fun i j => A i j / (S i i - T j j)
    S * X - X * T = A := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  have hSX : ∑ k, S i k * (A k j / (S k k - T j j)) =
      S i i * (A i j / (S i i - T j j)) := by
    apply Finset.sum_eq_single i
    · intro k _ hki; rw [hS i k (fun h => hki (h ▸ rfl)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hXT : ∑ k, (A i k / (S i i - T k k)) * T k j =
      (A i j / (S i i - T j j)) * T j j := by
    apply Finset.sum_eq_single j
    · intro k _ hkj; rw [hT k j (fun h => hkj (h ▸ rfl)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hSX, hXT]
  have hne : S i i - T j j ≠ 0 := sub_ne_zero.mpr (hST i j)
  field_simp

/-- For diagonal S,T with ‖S_{ii} - T_{jj}‖ ≥ δ > 0 for all i,j,
    the entrywise solution has ‖X‖_HS ≤ ‖A‖_HS / δ. -/
lemma sylvester_diag_diag_hsNorm_bound {m : ℕ} (S T A : Matrix (Fin m) (Fin m) ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hSep : ∀ i j, δ ≤ ‖S i i - T j j‖) :
    let X : Matrix (Fin m) (Fin m) ℂ := fun i j => A i j / (S i i - T j j)
    hsNorm X ≤ hsNorm A / δ := by
  intro X
  have hhs_nn : 0 ≤ hsNorm A / δ := div_nonneg (hsNorm_nonneg A) (le_of_lt hδ)
  apply le_of_sq_le_sq _ hhs_nn
  rw [div_pow]
  unfold hsNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))),
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)))]
  rw [Finset.sum_div]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.sum_div]
  apply Finset.sum_le_sum; intro j _
  change Complex.normSq (A i j / (S i i - T j j)) ≤ Complex.normSq (A i j) / δ ^ 2
  rw [Complex.normSq_div]
  apply div_le_div_of_nonneg_left (Complex.normSq_nonneg _)
  · positivity
  · rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (by positivity) (hSep i j) 2

/-- For diagonal S,T with ‖S_{ii} - T_{jj}‖ ≥ δ > 0 for all i,j,
    the entrywise solution has ‖X‖ ≤ (√m / δ) · ‖A‖. -/
lemma sylvester_diag_diag_norm_bound {m : ℕ} (S T A : Matrix (Fin m) (Fin m) ℂ)
    (hS : IsDiagMatrix S) (hT : IsDiagMatrix T)
    (δ : ℝ) (hδ : 0 < δ)
    (hSep : ∀ i j, δ ≤ ‖S i i - T j j‖) :
    let X : Matrix (Fin m) (Fin m) ℂ := fun i j => A i j / (S i i - T j j)
    S * X - X * T = A ∧ ‖X‖ ≤ (Real.sqrt m / δ) * ‖A‖ := by
  refine ⟨sylvester_diag_diag_solution S T A hS hT (fun i j =>
    fun h => by have := hSep i j; simp [h] at this; linarith), ?_⟩
  set X : Matrix (Fin m) (Fin m) ℂ := fun i j => A i j / (S i i - T j j) with hX_def
  calc ‖X‖ ≤ hsNorm X := le_hsNorm X
    _ ≤ hsNorm A / δ := by
        change hsNorm (fun i j => A i j / (S i i - T j j)) ≤ hsNorm A / δ
        exact sylvester_diag_diag_hsNorm_bound S T A δ hδ hSep
    _ ≤ (Real.sqrt m * ‖A‖) / δ :=
        div_le_div_of_nonneg_right (hsNorm_le_sqrt_n_mul_opNorm A) (le_of_lt hδ)
    _ = (Real.sqrt m / δ) * ‖A‖ := by ring

/-- Dimension-free operator norm bound for diagonal Sylvester equations (Re separation).
    When both S and T are diagonal with Re(S_{ii} - T_{jj}) ≥ δ > 0 for all i,j,
    the unique solution X satisfies ‖X‖ ≤ ‖A‖/δ.
    This is the sharp bound from the integral representation C = ∫₀^∞ e^{-uS} A e^{uT} du
    (reference note, Proposition 1 part (iii)).
    The proof uses the Bochner integral: ‖X‖ = ‖∫₀^∞ f(u)du‖ ≤ ∫₀^∞ ‖f(u)‖ du
    where ‖f(u)‖ ≤ ‖A‖·e^{-δu}, so the bound is ‖A‖/δ. -/
lemma sylvester_diag_opNorm_bound_re {m : ℕ} (S T A : Matrix (Fin m) (Fin m) ℂ)
    (hS : IsDiagMatrix S) (hT : IsDiagMatrix T)
    (δ : ℝ) (hδ : 0 < δ)
    (hRe : ∀ i j, δ ≤ (S i i - T j j).re) :
    let X : Matrix (Fin m) (Fin m) ℂ := fun i j => A i j / (S i i - T j j)
    S * X - X * T = A ∧ ‖X‖ ≤ ‖A‖ / δ := by
  have hST : ∀ i j, S i i ≠ T j j := fun i j h => by
    have := hRe i j; rw [h, sub_self] at this; simp at this; linarith
  refine ⟨sylvester_diag_diag_solution S T A hS hT hST, ?_⟩
  -- The tight operator norm bound ‖X‖ ≤ ‖A‖/δ (without √m factor)
  -- uses the integral representation X = ∫₀^∞ e^{-uS} A e^{uT} du.
  -- Define the integrand F(u) = diag(e^{-Su}) · A · diag(e^{Tu})
  by_cases hm : m = 0
  · subst hm; have : (fun i j => A i j / (S i i - T j j)) = (0 : Matrix (Fin 0) (Fin 0) ℂ) := by
      ext i; exact i.elim0
    rw [this, norm_zero]; positivity
  haveI : NeZero m := ⟨hm⟩
  open MeasureTheory Set in
  -- Define F(u) = diag(e^{-S·u}) · A · diag(e^{T·u})
  set F : ℝ → Matrix (Fin m) (Fin m) ℂ :=
    fun u => Matrix.diagonal (fun i => Complex.exp (-(S i i) * ↑u)) * A *
             Matrix.diagonal (fun j => Complex.exp ((T j j) * ↑u)) with hF_def
  -- F is integrable on (0,∞): dominated by ‖A‖ · e^{-δu}
  have hF_int : IntegrableOn F (Ioi (0 : ℝ)) := by
    apply MeasureTheory.Integrable.mono'
    · exact (exp_neg_integrableOn_Ioi 0 hδ).const_mul ‖A‖
    · -- F is AEStronglyMeasurable (continuous hence measurable)
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact integrand_norm_bound S T A δ hδ hRe u (le_of_lt hu)
  -- Key identity: X = ∫₀^∞ F(u) du (entrywise via scalar exponential integrals)
  -- Commute Bochner integral with entry extraction, then evaluate each
  -- scalar integral ∫₀^∞ A_{ij} e^{-(S_{ii}-T_{jj})u} du = A_{ij}/(S_{ii}-T_{jj})
  -- Entry extraction as a ContinuousLinearMap (finite-dim → automatic continuity)
  have entry_clm : ∀ i j : Fin m,
      ∃ L : Matrix (Fin m) (Fin m) ℂ →L[ℂ] ℂ, ∀ M, L M = M i j := by
    intro i j
    let L₀ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => M i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact ⟨LinearMap.toContinuousLinearMap L₀, fun M => rfl⟩
  -- Entrywise integral identity: (∫ F u) i j = ∫ (F u) i j
  have integral_entry : ∀ i j : Fin m,
      (∫ u in Ioi (0 : ℝ), F u) i j = ∫ u in Ioi (0 : ℝ), (F u) i j := by
    intro i j
    obtain ⟨L, hL⟩ := entry_clm i j
    have := ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ) L hF_int
    simp only [hL] at this
    exact this.symm
  -- Each entry of F(u) simplifies to A_{ij} * exp(-(S_{ii}-T_{jj}) * u)
  have entry_F : ∀ i j : Fin m, ∀ u : ℝ,
      (F u) i j = A i j * Complex.exp (-(S i i - T j j) * u) := by
    intro i j u
    simp only [hF_def, Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, mul_ite, mul_zero, Finset.sum_ite_eq]
    rw [show Complex.exp (-S i i * ↑u) * A i j * Complex.exp (T j j * ↑u) =
        A i j * (Complex.exp (-S i i * ↑u) * Complex.exp (T j j * ↑u)) by ring,
        ← Complex.exp_add]
    ring_nf
  -- Scalar integral: ∫₀^∞ A_{ij} * exp(-(s-t)*u) du = A_{ij}/(s-t)
  have scalar_int : ∀ i j : Fin m,
      ∫ u in Ioi (0 : ℝ), A i j * Complex.exp (-(S i i - T j j) * ↑u) =
      A i j / (S i i - T j j) := by
    intro i j
    have hre : (-(S i i - T j j)).re < 0 := by
      have h1 := hRe i j
      rw [show (-(S i i - T j j)).re = -((S i i - T j j).re) from Complex.neg_re _]
      linarith
    -- Pull constant A_ij out of the set integral
    have : ∫ u in Ioi (0 : ℝ), A i j * Complex.exp (-(S i i - T j j) * ↑u) =
        A i j * ∫ u in Ioi (0 : ℝ), Complex.exp (-(S i i - T j j) * ↑u) :=
      MeasureTheory.integral_const_mul _ _
    rw [this, integral_exp_mul_complex_Ioi hre 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hne : S i i - T j j ≠ 0 := sub_ne_zero.mpr (hST i j)
    field_simp
  have hX_eq : (fun i j => A i j / (S i i - T j j)) =
      (∫ u in Ioi (0 : ℝ), F u : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    rw [integral_entry i j]
    simp only [entry_F i j]
    rw [scalar_int i j]
  -- Step 3: Norm bound via ‖∫ f‖ ≤ ∫ ‖f‖ ≤ ‖A‖/δ
  rw [hX_eq]
  calc ‖∫ u in Ioi (0 : ℝ), F u‖
      ≤ ∫ u in Ioi (0 : ℝ), ‖F u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), ‖A‖ * Real.exp (-δ * u) := by
        apply MeasureTheory.setIntegral_mono_on hF_int.norm
        · exact (exp_neg_integrableOn_Ioi 0 hδ).const_mul ‖A‖
        · exact measurableSet_Ioi
        · intro u hu
          exact integrand_norm_bound S T A δ hδ hRe u (le_of_lt hu)
    _ = ‖A‖ / δ := by
        have : ∫ u in Ioi (0 : ℝ), ‖A‖ * Real.exp (-δ * u) =
            ‖A‖ * ∫ u in Ioi (0 : ℝ), Real.exp (-δ * u) := by
          rw [← MeasureTheory.integral_const_mul]
        rw [this]
        have h2 : ∫ u in Ioi (0 : ℝ), Real.exp (-δ * u) = 1 / δ := by
          have h3 : (fun u => Real.exp (-δ * u)) = (fun u => Real.exp ((-δ) * u)) := by ring_nf
          rw [h3, integral_exp_mul_Ioi (by linarith : -δ < 0) 0]
          simp [mul_zero, Real.exp_zero, neg_div]
        rw [h2]; ring

/-- Imaginary-part separation version of the dimension-free bound.
    Reduces to the Re-separation case via multiplication by ±i:
    Im(s-t) ≥ δ ⟹ Re(-i·s - (-i·t)) = Im(s-t) ≥ δ. -/
lemma sylvester_diag_opNorm_bound_im {m : ℕ} (S T A : Matrix (Fin m) (Fin m) ℂ)
    (hS : IsDiagMatrix S) (hT : IsDiagMatrix T)
    (δ : ℝ) (hδ : 0 < δ)
    (hIm : ∀ i j, δ ≤ (S i i - T j j).im) :
    let X : Matrix (Fin m) (Fin m) ℂ := fun i j => A i j / (S i i - T j j)
    S * X - X * T = A ∧ ‖X‖ ≤ ‖A‖ / δ := by
  have hST : ∀ i j, S i i ≠ T j j := fun i j h => by
    have := hIm i j; rw [h, sub_self] at this; simp at this; linarith
  refine ⟨sylvester_diag_diag_solution S T A hS hT hST, ?_⟩
  -- Reduce to the Re-separation case via multiplication by -i
  -- Re(-i·(s-t)) = Im(s-t) ≥ δ, so we apply the Re bound to S'=-iS, T'=-iT, A'=-iA
  set S' := (-Complex.I) • S with hS'_def
  set T' := (-Complex.I) • T with hT'_def
  set A' := (-Complex.I) • A with hA'_def
  have hS' : IsDiagMatrix S' := fun i j hij => by simp [hS'_def, hS i j hij]
  have hT' : IsDiagMatrix T' := fun i j hij => by simp [hT'_def, hT i j hij]
  have hRe' : ∀ i j, δ ≤ (S' i i - T' j j).re := by
    intro i j
    simp only [hS'_def, hT'_def, Matrix.smul_apply, smul_eq_mul]
    have : ((-Complex.I) * S i i - (-Complex.I) * T j j).re =
        (S i i - T j j).im := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im,
        Complex.I_im, Complex.sub_re, Complex.sub_im]; ring
    rw [this]; exact hIm i j
  have key := (sylvester_diag_opNorm_bound_re S' T' A' hS' hT' δ hδ hRe').2
  -- The entrywise solutions coincide: (-i·A_{ij})/(-i·(S_{ii}-T_{jj})) = A_{ij}/(S_{ii}-T_{jj})
  have sol_eq : (fun i j => A' i j / (S' i i - T' j j) : Matrix (Fin m) (Fin m) ℂ) =
      (fun i j => A i j / (S i i - T j j)) := by
    ext i j
    simp only [hA'_def, hS'_def, hT'_def, Matrix.smul_apply, smul_eq_mul]
    have hne : (-Complex.I) ≠ 0 := by
      intro h; have := congr_arg Complex.im h; simp at this
    rw [show (-Complex.I) * S i i - (-Complex.I) * T j j =
        (-Complex.I) * (S i i - T j j) from by ring]
    exact mul_div_mul_left (A i j) (S i i - T j j) hne
  rw [sol_eq] at key
  have hA'_norm : ‖A'‖ = ‖A‖ := by
    simp [hA'_def, norm_smul, norm_neg, Complex.norm_I]
  rw [hA'_norm] at key; exact key

/-! ## Rosenblum norm bound -/

/-- Alias: Re-separation version of the dimension-free operator norm bound. -/
theorem sylvester_diag_diag_opNorm_bound {m : ℕ} (S T A : Matrix (Fin m) (Fin m) ℂ)
    (hS : IsDiagMatrix S) (hT : IsDiagMatrix T)
    (δ : ℝ) (hδ : 0 < δ)
    (hSep : ∀ i j, δ ≤ (S i i - T j j).re) :
    let X : Matrix (Fin m) (Fin m) ℂ := fun i j => A i j / (S i i - T j j)
    S * X - X * T = A ∧ ‖X‖ ≤ ‖A‖ / δ :=
  sylvester_diag_opNorm_bound_re S T A hS hT δ hδ hSep

/-- Combined Re-or-Im separation bound: if ALL pairs have Re separation ≥ δ,
    or ALL pairs have Im separation ≥ δ, the solution satisfies ‖X‖ ≤ ‖A‖/δ. -/
lemma sylvester_diag_opNorm_bound_re_or_im {m : ℕ} (S T A : Matrix (Fin m) (Fin m) ℂ)
    (hS : IsDiagMatrix S) (hT : IsDiagMatrix T)
    (δ : ℝ) (hδ : 0 < δ)
    (hSep : (∀ i j, δ ≤ (S i i - T j j).re) ∨ (∀ i j, δ ≤ (S i i - T j j).im)) :
    let X : Matrix (Fin m) (Fin m) ℂ := fun i j => A i j / (S i i - T j j)
    S * X - X * T = A ∧ ‖X‖ ≤ ‖A‖ / δ := by
  cases hSep with
  | inl hRe => exact sylvester_diag_opNorm_bound_re S T A hS hT δ hδ hRe
  | inr hIm => exact sylvester_diag_opNorm_bound_im S T A hS hT δ hδ hIm

end CommutatorTheorem
