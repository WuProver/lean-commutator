import PavingSeparation.Paving

/-! # Lower bounds for arbitrary original-coordinate partitions -/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace PavingSeparation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Some color class is at least as large as the real-valued average. -/
theorem exists_colorClass_card_ge_average (r : ℕ) [NeZero r] (c : ι → Fin r) :
    ∃ a : Fin r, (Fintype.card ι : ℝ) / r ≤ ((colorClass c a).card : ℝ) := by
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have heq : (r : ℝ) * ((Fintype.card ι : ℝ) / r) = Fintype.card ι := by
    field_simp
  have hb : Fintype.card (Fin r) • ((Fintype.card ι : ℝ) / r) ≤
      (Fintype.card ι : ℝ) := by
    simpa only [Fintype.card_fin, nsmul_eq_mul, heq] using le_refl (Fintype.card ι : ℝ)
  obtain ⟨a, ha⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card c hb
  exact ⟨a, ha⟩

/-- The ceiling lower bound holds for every coloring, not just dyadic colorings. -/
theorem family_paving_ceiling_lower (m r : ℕ) [NeZero r] (c : Cube m → Fin r) :
    Real.sqrt
        (((Nat.ceil ((2 : ℝ) ^ m / r) : ℝ) - 1) / ((2 : ℝ) ^ m - 1)) ≤
      pavingNorm (pavingMatrix m) c := by
  obtain ⟨a, ha⟩ := exists_colorClass_card_ge_average r c
  simp only [card_cube, Nat.cast_pow, Nat.cast_ofNat] at ha
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have havg : 0 < (2 : ℝ) ^ m / r := div_pos (by positivity) hr
  have hs : (colorClass c a).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast havg.trans_le ha
  have hceil : Nat.ceil ((2 : ℝ) ^ m / r) ≤ (colorClass c a).card :=
    Nat.ceil_le.mpr ha
  have hcast : (Nat.ceil ((2 : ℝ) ^ m / r) : ℝ) ≤ ((colorClass c a).card : ℝ) := by
    exact_mod_cast hceil
  calc
    Real.sqrt (((Nat.ceil ((2 : ℝ) ^ m / r) : ℝ) - 1) / ((2 : ℝ) ^ m - 1))
        ≤ Real.sqrt ((((colorClass c a).card : ℝ) - 1) / ((2 : ℝ) ^ m - 1)) := by
          apply Real.sqrt_le_sqrt
          exact div_le_div_of_nonneg_right (by linarith) (order_sub_one_nonneg m)
    _ ≤ ‖compression (colorClass c a) (pavingMatrix m)‖ := family_compression_lower m _ hs
    _ ≤ pavingNorm (pavingMatrix m) c := compression_norm_le_pavingNorm _ _ _

theorem pavingMinimum_ceiling_lower (m r : ℕ) [NeZero r] :
    Real.sqrt
        (((Nat.ceil ((2 : ℝ) ^ m / r) : ℝ) - 1) / ((2 : ℝ) ^ m - 1)) ≤
      pavingMinimum (pavingMatrix m) r :=
  le_pavingMinimum _ _ _ (fun c ↦ family_paving_ceiling_lower m r c)

/-- Any epsilon paving needs at least n / (1 + epsilon squared times (n - 1)) colors. -/
theorem family_paving_card_lower (m r : ℕ) (hm : 0 < m) [NeZero r]
    (ε : ℝ) (c : Cube m → Fin r)
    (hc : ∀ a, ‖compression (colorClass c a) (pavingMatrix m)‖ ≤ ε) :
    (2 : ℝ) ^ m / (1 + ε ^ 2 * ((2 : ℝ) ^ m - 1)) ≤ r := by
  obtain ⟨a, ha⟩ := exists_colorClass_card_ge_average r c
  simp only [card_cube, Nat.cast_pow, Nat.cast_ofNat] at ha
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have havg : 0 < (2 : ℝ) ^ m / r := div_pos (by positivity) hr
  have hs : (colorClass c a).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast havg.trans_le ha
  have hflat := flat_compression_sq_lower (pavingMatrix m) (1 / ((2 : ℝ) ^ m - 1))
    (family_diag m) (fun i j hij ↦ family_offdiag_norm_sq m hij) (colorClass c a) hs
  have hsq : ‖compression (colorClass c a) (pavingMatrix m)‖ ^ 2 ≤ ε ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hc a) 2
  have hcard : 1 ≤ (colorClass c a).card := hs.card_pos
  rw [Nat.cast_sub hcard, Nat.cast_one] at hflat
  have hquot : (((colorClass c a).card : ℝ) - 1) / ((2 : ℝ) ^ m - 1) ≤ ε ^ 2 := by
    simpa only [div_eq_mul_inv, one_mul] using hflat.trans hsq
  have hnum := (div_le_iff₀ (order_sub_one_pos hm)).mp hquot
  have hbound : (2 : ℝ) ^ m / r ≤ 1 + ε ^ 2 * ((2 : ℝ) ^ m - 1) := by
    linarith
  have hmul := (div_le_iff₀ hr).mp hbound
  have hden : 0 < 1 + ε ^ 2 * ((2 : ℝ) ^ m - 1) := by
    have := order_sub_one_nonneg m
    positivity
  apply (div_le_iff₀ hden).mpr
  simpa only [mul_comm] using hmul

theorem family_pavingMinimum_card_lower (m r : ℕ) (hm : 0 < m) [NeZero r]
    (ε : ℝ) (h : pavingMinimum (pavingMatrix m) r ≤ ε) :
    (2 : ℝ) ^ m / (1 + ε ^ 2 * ((2 : ℝ) ^ m - 1)) ≤ r := by
  obtain ⟨c, hc⟩ := exists_pavingMinimum (pavingMatrix m) r
  apply family_paving_card_lower m r hm ε c
  intro a
  exact (compression_norm_le_pavingNorm _ _ a).trans (hc ▸ h)

end PavingSeparation
