import CommutatorTheorem.NoEpsilon.Steinitz
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Trace-controlled groups from the two-dimensional Steinitz lemma

The permutation partitions kR entries into k groups of exactly R entries.
The first coordinate has group sums bounded by four, and a nonnegative second
coordinate of total mass at most 2k has group sums bounded by six.
-/

open scoped BigOperators

namespace NoEpsilon.SteinitzGrouping

theorem interval_sum_eq_sub_prefix {n : ℕ} (z : Fin n → ℂ) (a b : ℕ) (hab : a ≤ b) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ a ≤ i.val ∧ i.val < b), z i) =
      (∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ i.val < b), z i) -
        ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ i.val < a), z i := by
  classical
  apply eq_sub_iff_add_eq.mpr
  rw [← Finset.sum_union]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    omega

theorem group_sum_eq_interval {k R : ℕ} (z : Fin (k * R) → ℂ) (j : Fin k) :
    (∑ b : Fin R, z (finProdFinEquiv (j, b))) =
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (k * R) ↦ j.val * R ≤ i.val ∧ i.val < (j.val + 1) * R), z i := by
  classical
  apply Finset.sum_bij (fun b _ ↦ finProdFinEquiv (j, b))
  · intro b _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change j.val * R ≤ b.val + R * j.val ∧ b.val + R * j.val < (j.val + 1) * R
    have hb := b.isLt
    constructor <;> nlinarith
  · intro b _ c _ h
    exact congrArg Prod.snd (finProdFinEquiv.injective h)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hlt : i.val - j.val * R < R := by
      have hu : i.val < j.val * R + R := by nlinarith [hi.2]
      omega
    refine ⟨⟨i.val - j.val * R, hlt⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change i.val - j.val * R + R * j.val = i.val
    nlinarith [Nat.sub_add_cancel hi.1]
  · intro b _
    rfl

/-- Consecutive length-R groups inherit coordinate bounds four from prefix bounds two. -/
theorem group_coordinates_le_four {k R : ℕ} (z : Fin (k * R) → ℂ)
    (hprefix : ∀ m : ℕ,
      |(∑ i ∈ Finset.univ.filter (fun i : Fin (k * R) ↦ i.val < m), z i).re| ≤ 2 ∧
      |(∑ i ∈ Finset.univ.filter (fun i : Fin (k * R) ↦ i.val < m), z i).im| ≤ 2)
    (j : Fin k) :
    |(∑ b : Fin R, z (finProdFinEquiv (j, b))).re| ≤ 4 ∧
      |(∑ b : Fin R, z (finProdFinEquiv (j, b))).im| ≤ 4 := by
  rw [group_sum_eq_interval, interval_sum_eq_sub_prefix _ _ _ (by nlinarith)]
  obtain ⟨hlre, hlim⟩ := hprefix (j.val * R)
  obtain ⟨hhre, hhim⟩ := hprefix ((j.val + 1) * R)
  simp only [Complex.sub_re, Complex.sub_im]
  constructor
  · exact (abs_sub _ _).trans (by linarith)
  · exact (abs_sub _ _).trans (by linarith)

/-- The exact balanced grouping required by low-mass paving. -/
theorem exists_trace_controlled_groups {k R : ℕ} (hk : 0 < k) (hR : 0 < R)
    (x y : Fin (k * R) → ℝ) (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hxsum : ∑ i, x i = 0) (hysum : ∑ i, y i ≤ 2 * k) :
    ∃ e : (Fin k × Fin R) ≃ Fin (k * R),
      ∀ j : Fin k, |∑ b : Fin R, x (e (j, b))| ≤ 4 ∧
        ∑ b : Fin R, y (e (j, b)) ≤ 6 := by
  classical
  let μ : ℝ := (∑ i, y i) / (k * R : ℕ)
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hR' : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have hn : (0 : ℝ) < (k * R : ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hk hR)
  have hsumNonneg : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ ↦ (hy i).1)
  have hμ0 : 0 ≤ μ := div_nonneg hsumNonneg hn.le
  have hμ1 : μ ≤ 1 := by
    apply (div_le_iff₀ hn).mpr
    calc
      _ ≤ ∑ _ : Fin (k * R), (1 : ℝ) := Finset.sum_le_sum (fun i _ ↦ (hy i).2)
      _ = _ := by simp
  have hμR : μ * R ≤ 2 := by
    have hid : μ * R = (∑ i, y i) / k := by
      dsimp [μ]
      push_cast
      field_simp
    rw [hid]
    exact (div_le_iff₀ hk').mpr hysum
  let z : Fin (k * R) → ℂ := fun i ↦ ⟨x i, y i - μ⟩
  have hzre (i : Fin (k * R)) : |(z i).re| ≤ 1 := hx i
  have hzim (i : Fin (k * R)) : |(z i).im| ≤ 1 := by
    change |y i - μ| ≤ 1
    apply abs_le.mpr
    have hi := hy i
    constructor <;> linarith
  have hzsum : ∑ i, z i = 0 := by
    apply Complex.ext
    · simpa [z] using hxsum
    · simp only [Complex.im_sum, z, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Complex.zero_im]
      dsimp [μ]
      field_simp
      ring
  obtain ⟨σ, hσ⟩ := NoEpsilon.Steinitz.exists_complex_permutation z hzre hzim hzsum
  refine ⟨finProdFinEquiv.trans σ, ?_⟩
  intro j
  obtain ⟨hre, him⟩ := group_coordinates_le_four (fun i ↦ z (σ i)) hσ j
  have hreal : (∑ b : Fin R, z (σ (finProdFinEquiv (j, b)))).re =
      ∑ b : Fin R, x (σ (finProdFinEquiv (j, b))) := by simp [z]
  have himag : (∑ b : Fin R, z (σ (finProdFinEquiv (j, b)))).im =
      (∑ b : Fin R, y (σ (finProdFinEquiv (j, b)))) - μ * R := by
    simp [z, Finset.sum_sub_distrib, mul_comm]
  rw [hreal] at hre
  rw [himag] at him
  refine ⟨hre, ?_⟩
  have hupper := (abs_le.mp him).2
  change (∑ b : Fin R, y (σ (finProdFinEquiv (j, b)))) ≤ 6
  linarith

end NoEpsilon.SteinitzGrouping
