import PavingSeparation.PavingBasic
import PavingSeparation.Family
import PavingSeparation.Arithmetic

/-! # Exact optimal dyadic paving for the explicit family -/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace PavingSeparation

/-- Coloring by the first l branches of the original recursive coordinate tree. -/
def dyadicColor : (m l : ℕ) → l ≤ m → Cube m → Cube l
  | _, 0, _ => fun _ ↦ 0
  | 0, l + 1, h => False.elim (by omega)
  | m + 1, l + 1, h =>
      Sum.map (dyadicColor m l (Nat.le_of_succ_le_succ h))
        (dyadicColor m l (Nat.le_of_succ_le_succ h))

theorem dyadic_skew_compression_norm (m l : ℕ) (h : l ≤ m) (a : Cube l) :
    ‖compression (colorClass (dyadicColor m l h) a) (skew m)‖ =
      Real.sqrt ((2 : ℝ) ^ (m - l) - 1) := by
  induction l generalizing m with
  | zero =>
      have ha : (0 : Cube 0) = a := Subsingleton.elim _ _
      simp [dyadicColor, colorClass, ha, skew_norm]
  | succ l ih =>
      cases m with
      | zero => omega
      | succ m =>
          have hl : l ≤ m := Nat.le_of_succ_le_succ h
          cases a with
          | inl a =>
              have heq :
                  compression (colorClass (dyadicColor (m + 1) (l + 1) h)
                    (Sum.inl a)) (skew (m + 1)) =
                    Matrix.fromBlocks
                      (compression (colorClass (dyadicColor m l hl) a) (skew m)) 0 0 0 := by
                ext i j
                cases i <;> cases j <;>
                  simp [compression_apply, colorClass, dyadicColor, Cube]
              rw [heq, norm_fromBlocks_zero_left]
              simpa using ih m hl a
          | inr a =>
              have heq :
                  compression (colorClass (dyadicColor (m + 1) (l + 1) h)
                    (Sum.inr a)) (skew (m + 1)) =
                    Matrix.fromBlocks 0 0 0
                      (-compression (colorClass (dyadicColor m l hl) a) (skew m)) := by
                ext i j
                cases i <;> cases j <;>
                  simp [compression_apply, colorClass, dyadicColor, Cube]
                split_ifs <;> simp
              rw [heq, norm_fromBlocks_zero_right, norm_neg]
              simpa using ih m hl a

theorem dyadic_family_compression_norm (m l : ℕ) (h : l ≤ m) (a : Cube l) :
    ‖compression (colorClass (dyadicColor m l h) a) (family m)‖ =
      Real.sqrt (((2 : ℝ) ^ (m - l) - 1) / ((2 : ℝ) ^ m - 1)) := by
  rw [family, compression_smul, norm_smul, dyadic_skew_compression_norm]
  rw [norm_div, Complex.norm_I, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sqrt_div (order_sub_one_nonneg (m - l))]
  ring

theorem dyadic_pavingNorm (m l : ℕ) (h : l ≤ m) :
    pavingNorm (family m) (dyadicColor m l h) =
      Real.sqrt (((2 : ℝ) ^ (m - l) - 1) / ((2 : ℝ) ^ m - 1)) := by
  apply le_antisymm
  · exact pavingNorm_le _ _ _ (fun a ↦ (dyadic_family_compression_norm m l h a).le)
  · rw [← dyadic_family_compression_norm m l h (origin l)]
    exact compression_norm_le_pavingNorm _ _ _

theorem family_compression_lower (m : ℕ) (s : Finset (Cube m)) (hs : s.Nonempty) :
    Real.sqrt (((s.card : ℝ) - 1) / ((2 : ℝ) ^ m - 1)) ≤
      ‖compression s (family m)‖ := by
  have h := flat_compression_sq_lower (family m) (1 / ((2 : ℝ) ^ m - 1))
    (family_diag m) (fun i j hij ↦ family_offdiag_norm_sq m hij) s hs
  have hcard : 1 ≤ s.card := hs.card_pos
  rw [Nat.cast_sub hcard, Nat.cast_one] at h
  apply (Real.sqrt_le_iff).2
  exact ⟨norm_nonneg _, by simpa [div_eq_mul_inv] using h⟩

/-- Every coloring, including those unrelated to the recursive tree, obeys the lower bound. -/
theorem dyadic_paving_lower (m l : ℕ) (h : l ≤ m) (c : Cube m → Fin (2 ^ l)) :
    Real.sqrt (((2 : ℝ) ^ (m - l) - 1) / ((2 : ℝ) ^ m - 1)) ≤
      pavingNorm (family m) c := by
  have hcard : Fintype.card (Fin (2 ^ l)) * 2 ^ (m - l) ≤ Fintype.card (Cube m) := by
    simp only [Fintype.card_fin, card_cube]
    rw [← pow_add, Nat.add_sub_of_le h]
  obtain ⟨a, ha⟩ := Fintype.exists_le_card_fiber_of_mul_le_card c hcard
  have hs : (colorClass c a).Nonempty := by
    apply Finset.card_pos.mp
    exact lt_of_lt_of_le (by positivity : 0 < 2 ^ (m - l)) ha
  have hcast : (2 : ℝ) ^ (m - l) ≤ ((colorClass c a).card : ℝ) := by
    exact_mod_cast ha
  calc
    Real.sqrt (((2 : ℝ) ^ (m - l) - 1) / ((2 : ℝ) ^ m - 1))
        ≤ Real.sqrt ((((colorClass c a).card : ℝ) - 1) / ((2 : ℝ) ^ m - 1)) := by
          apply Real.sqrt_le_sqrt
          exact div_le_div_of_nonneg_right (by linarith) (order_sub_one_nonneg m)
    _ ≤ ‖compression (colorClass c a) (family m)‖ := family_compression_lower m _ hs
    _ ≤ pavingNorm (family m) c := compression_norm_le_pavingNorm _ _ _

/-- The optimal value is the true minimum over all original-coordinate partitions. -/
theorem pavingMinimum_dyadic (m l : ℕ) (h : l ≤ m) :
    pavingMinimum (family m) (2 ^ l) =
      Real.sqrt (((2 : ℝ) ^ (m - l) - 1) / ((2 : ℝ) ^ m - 1)) := by
  apply le_antisymm
  · let e : Cube l ≃ Fin (2 ^ l) := Fintype.equivOfCardEq (by simp)
    calc
      pavingMinimum (family m) (2 ^ l)
          ≤ pavingNorm (family m) (e ∘ dyadicColor m l h) := pavingMinimum_le _ _ _
      _ = pavingNorm (family m) (dyadicColor m l h) := pavingNorm_relabel _ _ e
      _ = _ := dyadic_pavingNorm m l h
  · exact le_pavingMinimum _ _ _ (fun c ↦ dyadic_paving_lower m l h c)

/-- A prescribed dyadic number of colors works also when it exceeds the matrix dimension. -/
theorem family_paving_at_dyadic_count (m L : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (hpow : 1 / ε ^ 2 ≤ (2 : ℝ) ^ L) :
    ∃ c : Cube m → Fin (2 ^ L), pavingNorm (family m) c ≤ ε := by
  by_cases hLm : L ≤ m
  · let e : Cube L ≃ Fin (2 ^ L) := Fintype.equivOfCardEq (by simp)
    refine ⟨e ∘ dyadicColor m L hLm, ?_⟩
    rw [pavingNorm_relabel, dyadic_pavingNorm]
    exact dyadic_compression_sqrt_le_epsilon hm hLm hε hpow
  · have hmL : m ≤ L := by omega
    have hcard : 2 ^ m ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hmL
    let e : Cube m ≃ Fin (2 ^ m) := Fintype.equivOfCardEq (by simp)
    let c : Cube m → Fin (2 ^ L) := Fin.castLE hcard ∘ e
    have hc : Function.Injective c := (Fin.castLE_injective hcard).comp e.injective
    refine ⟨c, ?_⟩
    rw [pavingNorm_eq_zero_of_injective _ (family_diag m) c hc]
    exact hε.le

/-- A single dimension-independent color bound, strictly below twice epsilon inverse square. -/
theorem exists_uniform_family_paving (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ r : ℕ, 0 < r ∧ (r : ℝ) < 2 / ε ^ 2 ∧
      ∀ m : ℕ, 0 < m → ∃ c : Cube m → Fin r,
        ∀ a : Fin r, ‖compression (colorClass c a) (family m)‖ ≤ ε := by
  obtain ⟨L, hL, hcount⟩ := exists_dyadic_inverse_sq ε hε hε1
  refine ⟨2 ^ L, by positivity, ?_, ?_⟩
  · exact_mod_cast hcount
  · intro m hm
    obtain ⟨c, hc⟩ := family_paving_at_dyadic_count m L hm ε hε hL
    exact ⟨c, fun a ↦ (compression_norm_le_pavingNorm _ _ a).trans hc⟩

end PavingSeparation
