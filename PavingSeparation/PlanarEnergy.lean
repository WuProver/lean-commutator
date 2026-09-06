import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Inverse-square energy in a bounded planar square

A clipped grid has exactly four to the scale many cells, including the boundary.
Retaining the exact collision count gives the constant stated in the supplied PDF.
-/

namespace PavingSeparation.PlanarEnergy

open scoped BigOperators

private theorem geom_sum_exact (p : ℕ) :
    ∑ s ∈ Finset.range p, (4 : ℝ) ^ s = ((4 : ℝ) ^ p - 1) / 3 := by
  induction p with
  | zero => norm_num
  | succ p ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

private theorem geom_sum_bound (p : ℕ) :
    ∑ s ∈ Finset.range p, (4 : ℝ) ^ s ≤ (4 : ℝ) ^ p / 3 := by
  rw [geom_sum_exact]
  linarith

private theorem scale_sum_bound (p : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (d : ℝ) (hd : 0 ≤ d) (hP : ∀ k < p, P k → (4 : ℝ) ^ k * d ≤ 8) :
    (∑ k ∈ Finset.range p, if P k then (4 : ℝ) ^ k else 0) * d ≤ 32 / 3 := by
  induction p with
  | zero => norm_num
  | succ p ih =>
    by_cases hp : P p
    · have hlast := hP p (Nat.lt_succ_self p) hp
      have hsum : (∑ k ∈ Finset.range p, if P k then (4 : ℝ) ^ k else 0) ≤
          (4 : ℝ) ^ p / 3 := by
        calc
          _ ≤ ∑ k ∈ Finset.range p, (4 : ℝ) ^ k := by
            apply Finset.sum_le_sum
            intro k hk
            split_ifs
            · exact le_rfl
            · positivity
          _ ≤ _ := geom_sum_bound p
      have hmul := mul_le_mul_of_nonneg_right hsum hd
      rw [Finset.sum_range_succ, if_pos hp]
      nlinarith
    · rw [Finset.sum_range_succ, if_neg hp, add_zero]
      exact ih (fun k hk ↦ hP k (Nat.lt_trans hk (Nat.lt_succ_self p)))

private theorem collision_identity {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (f : ι → α) :
    (∑ a : α, (∑ i : ι, if f i = a then (1 : ℝ) else 0) ^ 2) =
      ∑ i : ι, ∑ j : ι, if f i = f j then (1 : ℝ) else 0 := by
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  rw [Finset.sum_comm]
  congr 1
  funext j
  by_cases h : f i = f j
  · simp [h]
  · simp [mul_ite, h]

private theorem collision_cauchy {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (f : ι → α) :
    (Fintype.card ι : ℝ) ^ 2 ≤ (Fintype.card α : ℝ) *
      (∑ i : ι, ∑ j : ι, if f i = f j then (1 : ℝ) else 0) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) (Finset.univ : Finset α)
    (fun _ ↦ 1) (fun a ↦ ∑ i : ι, if f i = a then (1 : ℝ) else 0)
  have hc : (∑ a : α, ∑ i : ι, if f i = a then (1 : ℝ) else 0) =
      Fintype.card ι := by
    rw [Finset.sum_comm]
    simp
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, hc, collision_identity] using h

private noncomputable def coordColor (q : ℕ) (hq : 0 < q) (x : ℝ) : Fin q :=
  ⟨min ⌊(x + 1) * q / 2⌋₊ (q - 1),
    lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

private theorem coordColor_bounds (q : ℕ) (hq : 0 < q) (x : ℝ) (hx : |x| ≤ 1) :
    (coordColor q hq x : ℝ) ≤ (x + 1) * q / 2 ∧
      (x + 1) * q / 2 ≤ (coordColor q hq x : ℝ) + 1 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hx0 : 0 ≤ (x + 1) * (q : ℝ) / 2 := by
    have hx1 : 0 ≤ x + 1 := by linarith [(abs_le.mp hx).1]
    exact div_nonneg (mul_nonneg hx1 hq0) (by norm_num)
  have hxq : (x + 1) * (q : ℝ) / 2 ≤ q := by
    have := (abs_le.mp hx).2
    nlinarith
  have hfloor := Nat.floor_le hx0
  constructor
  · exact le_trans (by exact_mod_cast (min_le_left ⌊(x + 1) * q / 2⌋₊ (q - 1)))
      hfloor
  · change (x + 1) * (q : ℝ) / 2 ≤
      (min ⌊(x + 1) * (q : ℝ) / 2⌋₊ (q - 1) : ℕ) + (1 : ℝ)
    by_cases h : ⌊(x + 1) * (q : ℝ) / 2⌋₊ ≤ q - 1
    · rw [min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · rw [min_eq_right (by omega)]
      have hsub : ((q - 1 : ℕ) : ℝ) + 1 = q := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ q))
      rwa [hsub]

private theorem coordColor_close (q : ℕ) (hq : 0 < q) (x y : ℝ)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (h : coordColor q hq x = coordColor q hq y) :
    |(x - y) * q| ≤ 2 := by
  obtain ⟨hxl, hxu⟩ := coordColor_bounds q hq x hx
  obtain ⟨hyl, hyu⟩ := coordColor_bounds q hq y hy
  rw [h] at hxl hxu
  apply abs_le.mpr
  constructor <;> nlinarith

private noncomputable def pointColor {ι : Type*} (z : ι → ℂ)
    (_hz : ∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1) (k : ℕ) (i : ι) :
    Fin (2 ^ k) × Fin (2 ^ k) :=
  (coordColor (2 ^ k) (by positivity) (z i).re, coordColor (2 ^ k) (by positivity) (z i).im)

private theorem pointColor_close {ι : Type*} (z : ι → ℂ)
    (hz : ∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1) (k : ℕ) (i j : ι)
    (h : pointColor z hz k i = pointColor z hz k j) :
    (4 : ℝ) ^ k * ‖z i - z j‖ ^ 2 ≤ 8 := by
  have hr := coordColor_close (2 ^ k) (by positivity) (z i).re (z j).re (hz i).1 (hz j).1
    (congrArg Prod.fst h)
  have hi := coordColor_close (2 ^ k) (by positivity) (z i).im (z j).im (hz i).2 (hz j).2
    (congrArg Prod.snd h)
  have hr2 : (((z i).re - (z j).re) * (2 ^ k : ℕ)) ^ 2 ≤ (2 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using hr)
  have hi2 : (((z i).im - (z j).im) * (2 ^ k : ℕ)) ^ 2 ≤ (2 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using hi)
  have hpow : ((2 ^ k : ℕ) : ℝ) ^ 2 = (4 : ℝ) ^ k := by
    push_cast
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  rw [mul_pow, hpow] at hr2 hi2
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith

private theorem color_card (s : ℕ) :
    (Fintype.card (Fin (2 ^ s) × Fin (2 ^ s)) : ℝ) = (4 : ℝ) ^ s := by
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

private theorem collision_offdiag {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (f : ι → α) :
    (∑ i : ι, ∑ j : ι, if f i = f j then (1 : ℝ) else 0) =
      (∑ i : ι, ∑ j : ι, if j ≠ i ∧ f i = f j then (1 : ℝ) else 0) +
        Fintype.card ι := by
  have h (i j : ι) : (if f i = f j then (1 : ℝ) else 0) =
      (if j ≠ i ∧ f i = f j then (1 : ℝ) else 0) + (if j = i then 1 else 0) := by
    by_cases hji : j = i <;> by_cases hf : f i = f j <;> simp_all
  simp_rw [h, Finset.sum_add_distrib]
  simp

private theorem scale_collision_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℂ) (hz : ∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1) (s : ℕ) :
    (Fintype.card ι : ℝ) ^ 2 - Fintype.card ι * (4 : ℝ) ^ s ≤ (4 : ℝ) ^ s *
      (∑ i : ι, ∑ j : ι,
        if j ≠ i ∧ pointColor z hz s i = pointColor z hz s j then (1 : ℝ) else 0) := by
  have hc := collision_cauchy (pointColor z hz s)
  rw [collision_offdiag, color_card] at hc
  nlinarith

/-- The sharp dyadic lower bound, with ordered distinct pairs and all boundary points. -/
theorem energy_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hn : Fintype.card ι = 4 ^ k) (z : ι → ℂ)
    (hz : ∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1) (hinj : Function.Injective z) :
    (((3 : ℝ) * k - 1) * (Fintype.card ι : ℝ) ^ 2 + Fintype.card ι) / 32 ≤
      ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j ↦ j ≠ i), (‖z i - z j‖ ^ 2)⁻¹ := by
  classical
  let W : ℝ := ∑ i : ι, ∑ j : ι, ∑ s ∈ Finset.range k,
    if j ≠ i ∧ pointColor z hz s i = pointColor z hz s j then (4 : ℝ) ^ s else 0
  have hnreal : (4 : ℝ) ^ k = Fintype.card ι := by exact_mod_cast hn.symm
  have hW : (((3 : ℝ) * k - 1) * (Fintype.card ι : ℝ) ^ 2 + Fintype.card ι) / 3 ≤ W := by
    calc
      _ = ∑ s ∈ Finset.range k,
          ((Fintype.card ι : ℝ) ^ 2 - Fintype.card ι * (4 : ℝ) ^ s) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, geom_sum_exact,
          hnreal]
        simp only [Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ ∑ s ∈ Finset.range k, (4 : ℝ) ^ s *
          (∑ i : ι, ∑ j : ι,
            if j ≠ i ∧ pointColor z hz s i = pointColor z hz s j then (1 : ℝ) else 0) := by
        exact Finset.sum_le_sum fun s _ ↦ scale_collision_lower z hz s
      _ = W := by
        simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
  have hpair (i j : ι) :
      (∑ s ∈ Finset.range k,
        if j ≠ i ∧ pointColor z hz s i = pointColor z hz s j then (4 : ℝ) ^ s else 0) ≤
      (32 / 3) * (if j ≠ i then (‖z i - z j‖ ^ 2)⁻¹ else 0) := by
    by_cases hij : j = i
    · subst j
      simp
    · have hdist : 0 < ‖z i - z j‖ ^ 2 := by
        apply sq_pos_of_pos
        apply norm_pos_iff.mpr
        exact sub_ne_zero.mpr (fun h ↦ hij (hinj h).symm)
      have h := scale_sum_bound k
        (fun k ↦ j ≠ i ∧ pointColor z hz k i = pointColor z hz k j)
        (‖z i - z j‖ ^ 2) (le_of_lt hdist)
        (fun k hk h ↦ pointColor_close z hz k i j h.2)
      simpa only [if_pos hij, div_eq_mul_inv] using (le_div_iff₀ hdist).mpr h
  have hupper : W ≤ (32 / 3) *
      (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j ↦ j ≠ i), (‖z i - z j‖ ^ 2)⁻¹) := by
    simp_rw [Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦ hpair i j
  linarith

end PavingSeparation.PlanarEnergy
