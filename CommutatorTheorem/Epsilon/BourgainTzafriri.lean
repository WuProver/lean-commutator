import CommutatorTheorem.Epsilon.BTElementary
import CommutatorTheorem.Epsilon.BTAutomationHarness
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Bourgain–Tzafriri Central Submatrix / Restricted Invertibility (Theorem 2, JOS 2013)

This file formalizes **Theorem 2** of

  Johnson, Ozawa, Schechtman, *A quantitative version of the commutator theorem for zero
  trace matrices*, **PNAS 110 (2013) 19252–19255**, page 19253,

which packages the deep harmonic-analysis content of Bourgain–Tzafriri's solution to a
problem of Kadison and Singer:

  Bourgain, Tzafriri, *On a problem of Kadison and Singer*,
  **J. Reine Angew. Math. 420 (1991) 1–43**.

The theorem has two equivalent forms.  Part (ii) follows from part (i) by iteration,
and the central-submatrix form is supplied by the verified mixed-determinant
and real-stability development.

## Statement

**(i) Central submatrix.**  For some absolute constant `K > 0`, if `A` is an `m × m`
matrix with zero diagonal then for all `ε > 0` there is a central (i.e. whose diagonal
is a subset of the diagonal of `A`) submatrix `A'` of dimension `⌊ε² m⌋ × ⌊ε² m⌋` whose
norm is at most `K ε ‖A‖`.

**(ii) Iterated paving.**  Consequently, if `A` is a norm-one `2 · 4ⁿ × 2 · 4ⁿ` matrix
with zero diagonal then for all `l ≤ n` there are `4ˡ` disjoint subsets `σᵢ` of
`{1, 2, …, 2 · 4ⁿ}` each of size `4ⁿ⁻ˡ` such that all the submatrices corresponding to
the entries in `σᵢ × σᵢ` have norm at most `K · 2⁻ˡ`.

In Lean we encode each `σᵢ` as an injective map `Fin (4 ^ (n - l)) → Fin (2 * 4 ^ n)`
whose range plays the role of the subset; pairwise disjointness of the σᵢ is the
disjointness of these ranges, and the submatrix is `A.submatrix (σ i) (σ i)`.

The same absolute constant `K` appears in both parts.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing

namespace CommutatorTheorem

/-- **Bourgain–Tzafriri central submatrix theorem (Theorem 2 (i), JOS 2013).**

There exists an absolute constant `K > 0` such that for every `m × m` complex matrix
`A` with zero diagonal and every `ε > 0`, there is an injective index map
`f : Fin ⌊ε² m⌋ → Fin m` such that the central (principal) submatrix
`A.submatrix f f` has operator norm at most `K · ε · ‖A‖`.

This is the *restricted invertibility* statement of Bourgain–Tzafriri (1991),
in the formulation used by Johnson–Ozawa–Schechtman (2013). -/
theorem bourgain_tzafriri_central_submatrix :
    ∃ K : ℝ, 0 < K ∧
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) (_hzd : ZeroDiag A)
      (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1),
      ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
        Function.Injective f ∧
        ‖A.submatrix f f‖ ≤ K * ε * ‖A‖ :=
  CommutatorTheorem.BTAutomationHarness.bourgain_tzafriri_central_submatrix_of_goals
    CommutatorTheorem.BTAutomationHarness.rootMotionGoal
    CommutatorTheorem.BTAutomationHarness.fellConverseGoal

/-- **Bourgain–Tzafriri iterated paving (Theorem 2 (ii), JOS 2013).**

There exists an absolute constant `K > 0` such that for every norm-one `2 · 4ⁿ × 2 · 4ⁿ`
complex matrix `A` with zero diagonal and every `l ≤ n`, there exist `4ˡ` pairwise
disjoint subsets of `{1, 2, …, 2 · 4ⁿ}` — encoded as a family of injective maps
`σ : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (2 * 4 ^ n)` — each of size `4 ^ (n - l)`,
such that the principal submatrix `A.submatrix (σ i) (σ i)` has operator norm at most
`K · 2⁻ˡ` for every `i : Fin (4 ^ l)`.

This is the iterated form of `bourgain_tzafriri_central_submatrix`, obtained by
repeated application of part (i) with `ε = (1/2)^l` over `4^l` extractions:
at extraction step `s`, the remaining index set has size `2·4^n − s·4^(n−l)`, which
stays `≥ 4^n` for `s ≤ 4^l − 1`, so `⌊ε² · |R|⌋₊ ≥ 4^(n−l)` and a fresh paving
subset can always be extracted with norm `≤ K · (1/2)^l`. -/
theorem bourgain_tzafriri_iterated :
    ∃ K : ℝ, 0 < K ∧
    ∀ (n : ℕ) (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ)
      (_hzd : ZeroDiag A) (_hnorm : ‖A‖ = 1) (l : ℕ) (_hl : l ≤ n),
      ∃ (σ : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (2 * 4 ^ n)),
        (∀ i, Function.Injective (σ i)) ∧
        (∀ i j, i ≠ j → Disjoint (Set.range (σ i)) (Set.range (σ j))) ∧
        (∀ i, ‖A.submatrix (σ i) (σ i)‖ ≤ K * (1 / 2 : ℝ) ^ l) := by
  obtain ⟨K_BT, hK_pos, hBT⟩ := bourgain_tzafriri_central_submatrix
  -- We need K ≥ 1 to absorb the trivial l = 0 case (where the bound K · 1 must
  -- dominate ‖A.submatrix σ_0 σ_0‖ ≤ ‖A‖ = 1).
  refine ⟨max K_BT 1, lt_of_lt_of_le hK_pos (le_max_left _ _), ?_⟩
  set K_final : ℝ := max K_BT 1 with hK_final_def
  have hK_final_ge_KBT : K_BT ≤ K_final := le_max_left _ _
  have hK_final_ge_one : (1 : ℝ) ≤ K_final := le_max_right _ _
  have hK_final_pos : 0 < K_final := lt_of_lt_of_le hK_pos hK_final_ge_KBT
  intro n A hzd hnorm l hl
  classical
  -- Case l = 0: bound is K_final · 1 ≥ 1 ≥ ‖submatrix‖.
  rcases Nat.eq_zero_or_pos l with hl0 | hl_pos_nat
  · subst hl0
    -- σ : Fin (4^0) → Fin (4^n) → Fin (2·4^n) = Fin 1 → Fin (4^n) → Fin (2·4^n)
    -- Use Fin.castLE with 4^(n-0) = 4^n ≤ 2·4^n.
    have hbound : 4 ^ (n - 0) ≤ 2 * 4 ^ n := by
      have h4n_pos : 1 ≤ 4 ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
      have : n - 0 = n := by omega
      rw [this]
      omega
    let σ₀ : Fin (4 ^ (n - 0)) → Fin (2 * 4 ^ n) := Fin.castLE hbound
    refine ⟨fun _ => σ₀, ?_, ?_, ?_⟩
    · intro _; exact Fin.castLE_injective _
    · intro i j hij
      exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega : i.val = j.val)) hij
    · intro _
      have hf_inj_loc : Function.Injective σ₀ := Fin.castLE_injective _
      have hsub_norm := submatrix_norm_le σ₀ hf_inj_loc A
      have hrw_loc :
          Matrix.of (fun a b => A (σ₀ a) (σ₀ b)) = A.submatrix σ₀ σ₀ := by
        ext a b; simp [Matrix.submatrix_apply, Matrix.of_apply]
      rw [hrw_loc] at hsub_norm
      have h_pow_0 : ((1 : ℝ) / 2) ^ 0 = 1 := pow_zero _
      rw [h_pow_0, mul_one]
      calc ‖A.submatrix σ₀ σ₀‖
          ≤ ‖A‖ := hsub_norm
        _ = 1 := hnorm
        _ ≤ K_final := hK_final_ge_one
  -- Case l ≥ 1: use BT_central iteratively with ε = (1/2)^l < 1.
  set ε : ℝ := (1 / 2 : ℝ) ^ l with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; positivity
  have hε_lt_one : ε < 1 := by
    rw [hε_def]
    have h_half_lt : (1 / 2 : ℝ) < 1 := by norm_num
    have h_half_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
    calc (1 / 2 : ℝ) ^ l ≤ (1 / 2 : ℝ) ^ 1 := by
            apply pow_le_pow_of_le_one h_half_nn (le_of_lt h_half_lt) hl_pos_nat
      _ = 1 / 2 := pow_one _
      _ < 1 := by norm_num
  have hε_sq : ε ^ 2 = (1 / 4 : ℝ) ^ l := by
    rw [hε_def, ← pow_mul,
        show 1 / (4 : ℝ) = (1 / 2 : ℝ) ^ 2 from by norm_num, ← pow_mul, mul_comm]
  have hpow_split : 4 ^ l * 4 ^ (n - l) = 4 ^ n := by
    rw [← pow_add]; congr 1; omega
  -- The result is the `s = 4^l` case of a more general inductive statement.
  suffices build : ∀ s, s ≤ 4 ^ l →
      ∃ (σ : Fin s → Fin (4 ^ (n - l)) → Fin (2 * 4 ^ n)),
        (∀ i, Function.Injective (σ i)) ∧
        (∀ i j, i ≠ j → Disjoint (Set.range (σ i)) (Set.range (σ j))) ∧
        (∀ i, ‖A.submatrix (σ i) (σ i)‖ ≤ K_final * (1 / 2 : ℝ) ^ l) by
    exact build (4 ^ l) le_rfl
  intro s
  induction s with
  | zero =>
    intro _
    refine ⟨fun i => Fin.elim0 i, ?_, ?_, ?_⟩
    all_goals (intro i; exact Fin.elim0 i)
  | succ s ih =>
    intro hs_succ
    have hs : s ≤ 4 ^ l := Nat.le_of_succ_le hs_succ
    obtain ⟨σ', hinj', hdisj', hnorm'⟩ := ih hs
    -- Build the union of already-extracted ranges as a Finset.
    set U : Finset (Fin (2 * 4 ^ n)) :=
      (Finset.univ : Finset (Fin s)).biUnion
        (fun i => (Finset.univ : Finset (Fin (4 ^ (n - l)))).image (σ' i)) with hU_def
    have hImg_card : ∀ i : Fin s,
        ((Finset.univ : Finset (Fin (4 ^ (n - l)))).image (σ' i)).card = 4 ^ (n - l) := by
      intro i
      rw [Finset.card_image_of_injective _ (hinj' i), Finset.card_univ, Fintype.card_fin]
    have hImg_disj : ∀ (i j : Fin s), i ≠ j →
        Disjoint ((Finset.univ : Finset (Fin (4 ^ (n - l)))).image (σ' i))
          ((Finset.univ : Finset (Fin (4 ^ (n - l)))).image (σ' j)) := by
      intro i j hij
      rw [Finset.disjoint_iff_ne]
      rintro a ha b hb hab
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨d, hd⟩ := hb
      have h1 : σ' i c ∈ Set.range (σ' i) := ⟨c, rfl⟩
      have h2 : σ' i c ∈ Set.range (σ' j) := ⟨d, hd.trans hab.symm⟩
      exact (Set.disjoint_iff.mp (hdisj' i j hij)) ⟨h1, h2⟩
    have hU_card : U.card = s * 4 ^ (n - l) := by
      rw [hU_def,
          Finset.card_biUnion (fun i _ j _ hij => hImg_disj i j hij)]
      simp [hImg_card]
    -- Complement R of U
    set R : Finset (Fin (2 * 4 ^ n)) := Finset.univ \ U with hR_def
    have hU_subset_univ : U ⊆ Finset.univ := Finset.subset_univ _
    have hR_card : R.card = 2 * 4 ^ n - s * 4 ^ (n - l) := by
      rw [hR_def, Finset.card_sdiff_of_subset hU_subset_univ, Finset.card_univ,
          Fintype.card_fin, hU_card]
    -- (s + 1) * 4 ^ (n - l) ≤ 4 ^ l * 4 ^ (n - l)
    have h_succ_mul : (s + 1) * 4 ^ (n - l) ≤ 4 ^ l * 4 ^ (n - l) :=
      Nat.mul_le_mul_right _ hs_succ
    have hU_plus_le : U.card + 4 ^ (n - l) ≤ 4 ^ n := by
      rw [hU_card, ← hpow_split]
      have : s * 4 ^ (n - l) + 4 ^ (n - l) = (s + 1) * 4 ^ (n - l) := by ring
      linarith [h_succ_mul]
    have h_smul_le : s * 4 ^ (n - l) ≤ 4 ^ n := by
      have h_s_le : s * 4 ^ (n - l) ≤ (s + 1) * 4 ^ (n - l) :=
        Nat.mul_le_mul_right _ (Nat.le_succ _)
      linarith [h_succ_mul, hpow_split]
    have hR_ge : 4 ^ n ≤ R.card := by
      rw [hR_card]
      omega
    -- Order-preserving embedding of R into Fin (2 * 4^n).
    set g : Fin R.card ↪o Fin (2 * 4 ^ n) := R.orderEmbOfFin rfl with hg_def
    have hg_inj : Function.Injective (g : Fin R.card → Fin (2 * 4 ^ n)) := g.injective
    have hg_mem : ∀ i, (g : Fin R.card → Fin (2 * 4 ^ n)) i ∈ R := fun i =>
      Finset.orderEmbOfFin_mem _ _ _
    have hg_not_mem_U : ∀ i, (g : Fin R.card → Fin (2 * 4 ^ n)) i ∉ U := by
      intro i
      have hmem : (g : Fin R.card → Fin (2 * 4 ^ n)) i ∈ Finset.univ \ U := hg_mem i
      exact (Finset.mem_sdiff.mp hmem).2
    -- Restricted matrix A.submatrix g g
    set Ag : Matrix (Fin R.card) (Fin R.card) ℂ :=
      A.submatrix (g : Fin R.card → Fin (2 * 4 ^ n)) g with hAg_def
    have hAg_zd : ZeroDiag Ag := by
      intro i
      show A (g i) (g i) = 0
      exact hzd _
    have hAg_norm_le : ‖Ag‖ ≤ 1 := by
      have h := submatrix_norm_le (g : Fin R.card → Fin (2 * 4 ^ n)) hg_inj A
      have hrw : Matrix.of (fun i j => A (g i) (g j)) = Ag := by
        ext i j; simp [Ag, Matrix.submatrix_apply, Matrix.of_apply]
      rw [hrw] at h
      linarith [h, hnorm.le]
    -- Apply BT_central to Ag with ε = (1/2)^l.
    obtain ⟨f, hf_inj, hf_norm⟩ := hBT R.card Ag hAg_zd ε hε_pos hε_lt_one
    -- 4^(n-l) ≤ ⌊ε² · R.card⌋₊
    have h_floor : 4 ^ (n - l) ≤ ⌊ε ^ 2 * (R.card : ℝ)⌋₊ := by
      rw [Nat.le_floor_iff (by positivity)]
      rw [hε_sq]
      have h4l_pos : (0 : ℝ) < (4 : ℝ) ^ l := by positivity
      have h1_4l : (1 / 4 : ℝ) ^ l = 1 / 4 ^ l := by
        rw [div_pow, one_pow]
      rw [h1_4l, div_mul_eq_mul_div, le_div_iff₀ h4l_pos]
      have h_combine : (4 : ℝ) ^ (n - l) * (4 : ℝ) ^ l = (4 : ℝ) ^ n := by
        rw [← pow_add]; congr 1; omega
      have h_cast_n : (((4 : ℕ) ^ n : ℕ) : ℝ) = (4 : ℝ) ^ n := by push_cast; rfl
      have h_cast_R : ((R.card : ℕ) : ℝ) = (R.card : ℝ) := by norm_cast
      have h_main : ((4 ^ (n - l) : ℕ) : ℝ) * (4 : ℝ) ^ l ≤ ((R.card : ℕ) : ℝ) :=
        calc ((4 ^ (n - l) : ℕ) : ℝ) * (4 : ℝ) ^ l
            = (4 : ℝ) ^ (n - l) * (4 : ℝ) ^ l := by push_cast; rfl
          _ = (4 : ℝ) ^ n := h_combine
          _ = (((4 : ℕ) ^ n : ℕ) : ℝ) := h_cast_n.symm
          _ ≤ ((R.card : ℕ) : ℝ) := by exact_mod_cast hR_ge
      linarith
    -- Truncate f to Fin (4^(n-l)).
    let σ_s : Fin (4 ^ (n - l)) → Fin (2 * 4 ^ n) :=
      fun j => g (f (Fin.castLE h_floor j))
    have hσ_s_inj : Function.Injective σ_s := by
      intro a b hab
      have : f (Fin.castLE h_floor a) = f (Fin.castLE h_floor b) := hg_inj hab
      have : Fin.castLE h_floor a = Fin.castLE h_floor b := hf_inj this
      exact (Fin.castLE_injective h_floor) this
    -- Range of σ_s is contained in R.
    have hσ_s_range_in_R : ∀ j, σ_s j ∈ R := by
      intro j
      exact hg_mem _
    have hσ_s_disj_U : ∀ i : Fin s,
        Disjoint (Set.range (σ' i)) (Set.range σ_s) := by
      intro i
      apply Set.disjoint_left.mpr
      rintro x ⟨a, ha⟩ ⟨b, hb⟩
      have hx_in_U : x ∈ U := by
        rw [hU_def]
        refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        exact ⟨a, Finset.mem_univ _, ha⟩
      have hx_not_in_U : x ∉ U := by
        rw [← hb]; exact hg_not_mem_U _
      exact hx_not_in_U hx_in_U
    -- Norm bound for σ_s.
    have hσ_s_norm : ‖A.submatrix σ_s σ_s‖ ≤ K_final * (1 / 2 : ℝ) ^ l := by
      -- A.submatrix σ_s σ_s = (Ag.submatrix f f).submatrix (Fin.castLE h_floor) (Fin.castLE h_floor)
      have h_eq : A.submatrix σ_s σ_s =
          (Ag.submatrix f f).submatrix (Fin.castLE h_floor) (Fin.castLE h_floor) := by
        ext i j; rfl
      have hcastLE_inj : Function.Injective (Fin.castLE h_floor) := Fin.castLE_injective _
      have h_submatrix_norm_le :
          ‖(Ag.submatrix f f).submatrix (Fin.castLE h_floor) (Fin.castLE h_floor)‖ ≤
          ‖Ag.submatrix f f‖ := by
        have hsub := submatrix_norm_le
          (Fin.castLE h_floor : Fin (4 ^ (n - l)) → Fin _) hcastLE_inj (Ag.submatrix f f)
        have hrw : Matrix.of (fun i j =>
              (Ag.submatrix f f) (Fin.castLE h_floor i) (Fin.castLE h_floor j)) =
            (Ag.submatrix f f).submatrix (Fin.castLE h_floor) (Fin.castLE h_floor) := by
          ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
        rw [hrw] at hsub; exact hsub
      have h_BT_bound : ‖Ag.submatrix f f‖ ≤ K_BT * ε * ‖Ag‖ := hf_norm
      have h_chain : ‖A.submatrix σ_s σ_s‖ ≤ K_BT * ε * ‖Ag‖ := by
        rw [h_eq]
        linarith [h_submatrix_norm_le, h_BT_bound]
      have h_eps_pow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ l := by positivity
      have hε_val : K_BT * ε * ‖Ag‖ ≤ K_final * (1 / 2 : ℝ) ^ l := by
        have hK_nn : 0 ≤ K_BT := le_of_lt hK_pos
        have hε_nn : 0 ≤ ε := le_of_lt hε_pos
        have hK_eps_nn : 0 ≤ K_BT * ε := mul_nonneg hK_nn hε_nn
        calc K_BT * ε * ‖Ag‖
            ≤ K_BT * ε * 1 := mul_le_mul_of_nonneg_left hAg_norm_le hK_eps_nn
          _ = K_BT * ε := by ring
          _ = K_BT * (1 / 2 : ℝ) ^ l := by rw [hε_def]
          _ ≤ K_final * (1 / 2 : ℝ) ^ l :=
              mul_le_mul_of_nonneg_right hK_final_ge_KBT h_eps_pow_nn
      linarith
    -- Extend σ' by σ_s using Fin.snoc.
    refine ⟨Fin.snoc σ' σ_s, ?_, ?_, ?_⟩
    · -- All injective.
      intro i
      induction i using Fin.lastCases with
      | last => simpa [Fin.snoc_last] using hσ_s_inj
      | cast i => simpa [Fin.snoc_castSucc] using hinj' i
    · -- Pairwise disjoint.
      intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          exact Disjoint.symm (hσ_s_disj_U j)
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          exact hσ_s_disj_U i
        | cast j =>
          simp only [Fin.snoc_castSucc]
          apply hdisj'
          intro h
          exact hij (by simp [h])
    · -- Norm bounds.
      intro i
      induction i using Fin.lastCases with
      | last => simpa [Fin.snoc_last] using hσ_s_norm
      | cast i => simpa [Fin.snoc_castSucc] using hnorm' i

end CommutatorTheorem
