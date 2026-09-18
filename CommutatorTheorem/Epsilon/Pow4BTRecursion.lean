import CommutatorTheorem.Epsilon.Pow4Bootstrap

/-!
# Pow4 BT-iterated recursion at the supremum level

This file proves **paper Eq. [2] + Claim 2 lift** at the `lambdaM`
supremum level.  The faithful full-matrix output is the one-step recurrence
```
λ(4ⁿ⁺¹) ≤ (1 + 8/l²)² · max(T(K,n,l), λ(4ⁿ)),
```
where `T` contains the selected-half Eq. [2] bound.  It implies directly that
`λ(4ⁿ) = O(rⁿ)` for every `r > 1`.

## Status

The full proof is structured in 5 phases:
* **Phase 1 (arithmetic helpers):** tightened bound `(l/(l−1))^l ≤ 8` for `l ≥ 2`,
  yielding `(1/(1−1/l))^l ≤ 8` (a *constant*, not exponential in `l`).  This is the
  cancellation that makes the BT-iterated coefficient constant.
* **Phase 2 (per-leaf BT lambdaA bound):** `lambdaA_BT_paving_descent` — packaging
  `bourgain_tzafriri_iterated` + `lambdaA_scale_bound`.
* **Phase 3 (H/H' construction):** implemented by
  `bt_paving_depth_l_construction` and `bt_paving_depth_l_complement`.
* **Phase 4 (iterated Claim 1):** implemented and packaged by
  `lambdaA_BT_small_side`.
* **Phase 5 (Claim 2 lift):** implemented via two asymmetric two-block lifts.
  The first passes from a selected half to size `2·4ⁿ`; the second joins two
  selected quarters and passes to size `4ⁿ⁺¹`.  Their combination and the
  fixed-depth geometric iteration are fully proved below.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedSpace

open CommutatorTheorem Pow4Bootstrap

namespace CommutatorTheorem

/-! ## Phase 1: tighter arithmetic helpers -/

/-- For `l ≥ 2`, `(l / (l − 1 : ℝ))^l ≤ 8`. The maximum is attained at `l = 2`
(value `4`); for `l ≥ 3` the value strictly decreases towards `e ≈ 2.718`.
We use the loose bound `8` for clean algebra downstream. -/
private lemma l_over_l_minus_one_pow_l_le_eight :
    ∀ l : ℕ, 2 ≤ l → ((l : ℝ) / ((l : ℝ) - 1)) ^ l ≤ 8 := by
  intro l hl
  have hl_pos : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  have hne : ((l : ℝ) - 1) ≠ 0 := ne_of_gt hl_pos
  -- l/(l-1) = 1 + 1/(l-1)
  have h_id : (l : ℝ) / ((l : ℝ) - 1) = 1 + 1 / ((l : ℝ) - 1) := by field_simp; ring
  rw [h_id]
  -- Decompose (1 + 1/(l-1))^l = (1 + 1/(l-1))^(l-1) · (1 + 1/(l-1)).
  have hl1 : 1 ≤ l := by omega
  have h_l_decomp : (1 + 1 / ((l : ℝ) - 1)) ^ l =
      (1 + 1 / ((l : ℝ) - 1)) ^ (l - 1) * (1 + 1 / ((l : ℝ) - 1)) := by
    have h_succ_eq : l = (l - 1) + 1 := by omega
    conv_lhs => rw [h_succ_eq]
    rw [pow_succ]
    have h_cast_eq : ((l - 1 + 1 : ℕ) : ℝ) = (l : ℝ) := by
      have h_nat_eq : (l - 1 + 1 : ℕ) = l := by omega
      exact_mod_cast h_nat_eq
    rw [h_cast_eq]
  rw [h_l_decomp]
  -- (1 + 1/(l-1))^(l-1) ≤ exp 1 = e.
  have h_pow_lm1 : (1 + 1 / ((l : ℝ) - 1)) ^ (l - 1) ≤ Real.exp 1 := by
    have hbase : 1 + 1 / ((l : ℝ) - 1) ≤ Real.exp (1 / ((l : ℝ) - 1)) := by
      have := Real.add_one_le_exp (1 / ((l : ℝ) - 1))
      linarith
    have h_pos : 0 ≤ 1 + 1 / ((l : ℝ) - 1) := by positivity
    have h_pow : (1 + 1 / ((l : ℝ) - 1)) ^ (l - 1) ≤
        (Real.exp (1 / ((l : ℝ) - 1))) ^ (l - 1) :=
      pow_le_pow_left₀ h_pos hbase _
    have h_exp_pow :
        (Real.exp (1 / ((l : ℝ) - 1))) ^ (l - 1) =
        Real.exp (((l - 1 : ℕ) : ℝ) * (1 / ((l : ℝ) - 1))) := by
      rw [← Real.exp_nat_mul]
    rw [h_exp_pow] at h_pow
    have h_lm1_cast : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
      rw [Nat.cast_sub hl1]; norm_cast
    have h_mul : ((l - 1 : ℕ) : ℝ) * (1 / ((l : ℝ) - 1)) = 1 := by
      rw [h_lm1_cast]; field_simp
    rw [h_mul] at h_pow
    exact h_pow
  have h_exp_le : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; linarith
  -- 1 + 1/(l-1) ≤ 2.
  have h_l1_le_two : 1 + 1 / ((l : ℝ) - 1) ≤ 2 := by
    have hl_ge_2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    have h_inv : 1 / ((l : ℝ) - 1) ≤ 1 := by rw [div_le_one hl_pos]; linarith
    linarith
  have h_l1_pos : 0 < 1 + 1 / ((l : ℝ) - 1) := by positivity
  have h_factor_le : (1 + 1 / ((l : ℝ) - 1)) ^ (l - 1) * (1 + 1 / ((l : ℝ) - 1)) ≤
      Real.exp 1 * 2 :=
    mul_le_mul h_pow_lm1 h_l1_le_two (le_of_lt h_l1_pos) (le_of_lt (Real.exp_pos 1))
  -- exp 1 * 2 ≤ 6 ≤ 8.
  linarith

/-- Consequence: `(1/(1−1/l))^l ≤ 8` for `l ≥ 2`.

This is the crucial BT-cancellation factor: combined with the per-leaf `(1/2)^l`,
the `(2/(1−1/l))^l` from iterated Claim 1 cancels to `(1/(1−1/l))^l ≤ 8` (a
*constant*, not exponential in `l`). -/
private lemma one_inv_eps_pow_l_le_eight :
    ∀ l : ℕ, 2 ≤ l → ((1 : ℝ) / (1 - 1 / l)) ^ l ≤ 8 := by
  intro l hl
  have hl_R : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hl_pos : (0 : ℝ) < (l : ℝ) := by linarith
  have h_id : (1 : ℝ) / (1 - 1 / l) = (l : ℝ) / ((l : ℝ) - 1) := by
    have h_denom : (1 : ℝ) - 1 / l = ((l : ℝ) - 1) / l := by field_simp
    rw [h_denom, one_div_div]
  rw [h_id]
  exact l_over_l_minus_one_pow_l_le_eight l hl

/-! ## Phase 2: per-leaf BT lambdaA bound -/

/-- BT-iterated lambdaA descent: for any `2 · 4ⁿ × 2 · 4ⁿ` zero-diagonal
norm-one matrix `A`, BT-paving at depth `l ≤ n` produces `4ˡ` disjoint paving
subsets, each of size `4ⁿ⁻ˡ`, on which the principal sub-matrices have
`lambdaA ≤ K_BT · (1/2)ˡ · lambdaM(4ⁿ⁻ˡ)`.

This is `lambdaA_BT_paving_descent` from `tmp_S1a_v3_bt_paving_descent.lean`,
inlined and trimmed of the `hScale` hypothesis (replaced by direct use of
`lambdaA_scale_bound`). -/
lemma lambdaA_BT_paving_descent
    (n l : ℕ) (hl : l ≤ n)
    (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1) :
    ∃ K_BT : ℝ, 0 < K_BT ∧
      ∃ σ : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (2 * 4 ^ n),
        (∀ i, Function.Injective (σ i)) ∧
        (∀ i j, i ≠ j → Disjoint (Set.range (σ i)) (Set.range (σ j))) ∧
        (∀ i, lambdaA (A.submatrix (σ i) (σ i)) ≤
              K_BT * (1 / 2 : ℝ) ^ l * lambdaM (4 ^ (n - l))) := by
  obtain ⟨K_BT, hK_pos, hBT⟩ := bourgain_tzafriri_iterated
  obtain ⟨σ, hσ_inj, hσ_disj, hσ_norm⟩ := hBT n A hzd hnorm l hl
  refine ⟨K_BT, hK_pos, σ, hσ_inj, hσ_disj, ?_⟩
  intro i
  have hzd_sub : ZeroDiag (A.submatrix (σ i) (σ i)) := by
    intro j; simp only [Matrix.submatrix_apply]; exact hzd _
  have h_scale := Pow4Bootstrap.lambdaA_scale_bound (A.submatrix (σ i) (σ i)) hzd_sub
  have h_norm_le : ‖A.submatrix (σ i) (σ i)‖ ≤ K_BT * (1 / 2 : ℝ) ^ l := hσ_norm i
  have hlM_nn : (0 : ℝ) ≤ lambdaM (4 ^ (n - l)) := by
    unfold lambdaM
    apply Real.sSup_nonneg
    intro x hx
    obtain ⟨B, _, rfl⟩ := hx
    unfold lambdaA
    by_cases hne : ({c : ℝ | ∃ (B' C' : Matrix (Fin (4^(n - l))) (Fin (4^(n - l))) ℂ),
        IsDiagMatrix B' ∧ (∀ i, InUnitSquare (B' i i)) ∧ B = ⁅B', C'⁆ₘ ∧ ‖C'‖ ≤ c}).Nonempty
    · exact le_csInf hne (fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
  calc lambdaA (A.submatrix (σ i) (σ i))
      ≤ ‖A.submatrix (σ i) (σ i)‖ * lambdaM (4 ^ (n - l)) := h_scale
    _ ≤ K_BT * (1 / 2 : ℝ) ^ l * lambdaM (4 ^ (n - l)) :=
        mul_le_mul_of_nonneg_right h_norm_le hlM_nn

/-! ## Phase-2.5: lambdaM-level four-block recursion

The four-block bound `lambdaM(4m) ≤ 2/(1-δ)·lambdaM(m) + 6/δ` is needed to feed
into `lambdaM_iterate_pow4`.  The proof packages `lambdaA_four_block_bound_strong`
(supremum-of-blocks form) together with `lambdaA_scale_bound` to convert the
per-block `lambdaA` bound into a single `lambdaM m` upper bound (using that
each canonical sub-block has norm `≤ ‖A‖ = 1`).

(This is essentially `lambdaM_four_block_recursion` from `Main.lean`, but
restated here so `Pow4BTRecursion.lean` does not depend on `Main.lean`.) -/
private lemma lambdaM_four_block_recursion_local (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ (m : ℕ), lambdaM (4 * m) ≤ 2 / (1 - δ) * lambdaM m + 6 / δ := by
  intro m
  have h1δ : (0 : ℝ) < 1 - δ := sub_pos.mpr hδ1
  have h2_nn : (0 : ℝ) ≤ 2 / (1 - δ) := by positivity
  have h6_nn : (0 : ℝ) ≤ 6 / δ := by positivity
  have hlM_m_nn : (0 : ℝ) ≤ lambdaM m := by
    unfold lambdaM
    apply Real.sSup_nonneg
    intro x hx
    obtain ⟨A, _, rfl⟩ := hx
    unfold lambdaA
    by_cases hne :
        ({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
            IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}).Nonempty
    · exact le_csInf hne (fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
  change sSup (lambdaA '' {A : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ | ZeroDiag A ∧ ‖A‖ = 1}) ≤
      2 / (1 - δ) * lambdaM m + 6 / δ
  set S := lambdaA '' {A : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ | ZeroDiag A ∧ ‖A‖ = 1}
  by_cases hne : S.Nonempty
  · apply csSup_le hne
    intro x hx
    obtain ⟨A, ⟨hzd, hnorm⟩, rfl⟩ := hx
    -- canonical block embedding
    let blockEmbed : Fin 4 → Fin m → Fin (4 * m) := fun k j =>
      ⟨k.val * m + j.val, by
        have hk := k.isLt; have hj := j.isLt
        calc k.val * m + j.val < k.val * m + m := by omega
          _ = (k.val + 1) * m := by ring
          _ ≤ 4 * m := by nlinarith⟩
    have hStrong := Pow4Bootstrap.lambdaA_four_block_bound_strong δ hδ hδ1 A hzd hnorm
    -- bound the supremum-over-Fin-4 of lambdaA(block) by lambdaM m
    have hinj_be : ∀ k, Function.Injective (blockEmbed k) := by
      intro k a b hab
      have : k.val * m + a.val = k.val * m + b.val := Fin.mk.inj_iff.mp hab
      exact Fin.ext (by omega)
    have hzd_block : ∀ k, ZeroDiag (A.submatrix (blockEmbed k) (blockEmbed k)) := by
      intro k i; simp only [Matrix.submatrix_apply]; exact hzd _
    have hnorm_block_le : ∀ k, ‖A.submatrix (blockEmbed k) (blockEmbed k)‖ ≤ 1 := by
      intro k
      have hsub := submatrix_norm_le (blockEmbed k) (hinj_be k) A
      have hrw : Matrix.of (fun i j => A (blockEmbed k i) (blockEmbed k j)) =
          A.submatrix (blockEmbed k) (blockEmbed k) := by
        ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
      rw [hrw] at hsub
      linarith [hsub, hnorm.le]
    have h_block_le : ∀ k, lambdaA (A.submatrix (blockEmbed k) (blockEmbed k)) ≤ lambdaM m := by
      intro k
      have h_scale := Pow4Bootstrap.lambdaA_scale_bound
        (A.submatrix (blockEmbed k) (blockEmbed k)) (hzd_block k)
      calc lambdaA (A.submatrix (blockEmbed k) (blockEmbed k))
          ≤ ‖A.submatrix (blockEmbed k) (blockEmbed k)‖ * lambdaM m := h_scale
        _ ≤ 1 * lambdaM m := mul_le_mul_of_nonneg_right (hnorm_block_le k) hlM_m_nn
        _ = lambdaM m := one_mul _
    have hsup_le : (⨆ k : Fin 4, lambdaA (A.submatrix (blockEmbed k) (blockEmbed k))) ≤ lambdaM
      m := by
      apply ciSup_le
      intro k; exact h_block_le k
    -- combine
    have hcoef_le : 2 / (1 - δ) *
        (⨆ k : Fin 4, lambdaA (A.submatrix (blockEmbed k) (blockEmbed k))) ≤
        2 / (1 - δ) * lambdaM m :=
      mul_le_mul_of_nonneg_left hsup_le h2_nn
    linarith [hStrong, hcoef_le]
  · show sSup S ≤ 2 / (1 - δ) * lambdaM m + 6 / δ
    rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp only [Real.sSup_empty]
    have h_coef_nn : 0 ≤ 2 / (1 - δ) * lambdaM m := mul_nonneg h2_nn hlM_m_nn
    linarith

/-! ## Phase 3: H/H' construction at depth l

Given the σ-paving from `lambdaA_BT_paving_descent` (which packages
`bourgain_tzafriri_iterated`), we assemble a single injection
`H : Fin (4^n) → Fin (2·4^n)` whose range is the disjoint union of the
σ-leaves, plus the complement injection `H' : Fin (4^n) → Fin (2·4^n)`
covering the remaining `4^n` indices.

The construction is the depth-`l` analogue of `bt_paving_to_sigma_block`
(`l = 1` in `Pow4Bootstrap`), packaging σ at depth `l`:

* domain `Fin (4^n) ≃ Fin (4^l) × Fin (4^(n-l))` (canonical split);
* `H (k, j) := σ k j` glues the `4^l` σ-leaves into one injection;
* `H' := buildComplement_S1i H` is the order-embedding complement.

These helpers are reused by Phase 4 (iterated four-block on `A.submatrix H H`)
and Phase 5 (two-block decomposition lifting `lambdaA (A.submatrix H H)`
back to `lambdaA A`).
-/

/-- Dimensional identity: `4^l · 4^(n-l) = 4^n` for `l ≤ n`. -/
private lemma four_pow_mul_pow_sub (n l : ℕ) (hl : l ≤ n) :
    (4 : ℕ) ^ l * 4 ^ (n - l) = 4 ^ n := by
  rw [← pow_add]; congr 1; omega

/-- Canonical equivalence `Fin (4^l) × Fin (4^(n-l)) ≃ Fin (4^n)` for `l ≤ n`. -/
private noncomputable def fin_four_pow_split (n l : ℕ) (hl : l ≤ n) :
    Fin (4 ^ l) × Fin (4 ^ (n - l)) ≃ Fin (4 ^ n) :=
  finProdFinEquiv.trans
    ((Fin.castOrderIso (four_pow_mul_pow_sub n l hl)).toEquiv)

/-- Depth-`l` σ-paving constructor for `lambdaM(4^n)` Phase 3.

Given a norm-one zero-diagonal matrix on `Fin (2·4^n)` and `2 ≤ l ≤ n`, produce:
* an injection `H : Fin (4^n) → Fin (2·4^n)` (the σ-leaves glued together);
* a 4-block embedding `e : Fin (4^l) → Fin (4^(n-l)) → Fin (4^n)` (the
  canonical `Fin (4^l) × Fin (4^(n-l)) ≃ Fin (4^n)` viewed as a per-leaf
  embedding);
* per-leaf injectivity, pairwise-disjoint ranges, surjectivity onto
  `Fin (4^n)`;
* the BT norm bound `‖A.submatrix (H ∘ e k) (H ∘ e k)‖ ≤ K_BT · (1/2)^l`.

The companion complement `H' := buildComplement_S1i H` (from
`Pow4Bootstrap`) is automatically injective with disjoint range and
union `Set.univ`. -/
lemma bt_paving_depth_l_construction_uniform :
    ∃ K_BT : ℝ, 0 < K_BT ∧
    ∀ (n l : ℕ), l ≤ n →
    ∀ (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ),
      ZeroDiag A → ‖A‖ = 1 →
    ∃ (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
      (e : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (4 ^ n)),
      Function.Injective H ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ k k' : Fin (4 ^ l), k ≠ k' →
        Disjoint (Set.range (e k)) (Set.range (e k'))) ∧
      (∀ i : Fin (4 ^ n), ∃ k j, e k j = i) ∧
      (∀ k, ‖A.submatrix (H ∘ e k) (H ∘ e k)‖ ≤ K_BT * (1 / 2 : ℝ) ^ l) := by
  classical
  obtain ⟨K, hK_pos, hK_spec⟩ := bourgain_tzafriri_iterated
  refine ⟨K, hK_pos, ?_⟩
  intro n l hl A hzd hnorm
  -- Apply BT at depth l.
  obtain ⟨σ, hσ_inj, hσ_disj, hσ_bound⟩ := hK_spec n A hzd hnorm l hl
  -- The canonical split equivalence.
  let splitEq : Fin (4 ^ l) × Fin (4 ^ (n - l)) ≃ Fin (4 ^ n) :=
    fin_four_pow_split n l hl
  -- `e k j := splitEq (k, j)` — the canonical per-leaf embedding into `Fin(4^n)`.
  let e : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (4 ^ n) := fun k j =>
    splitEq (k, j)
  -- `H := σ k j` where (k, j) := splitEq.symm i — glues all σ-leaves.
  let H : Fin (4 ^ n) → Fin (2 * 4 ^ n) := fun i =>
    let p := splitEq.symm i
    σ p.1 p.2
  -- H ∘ e k = σ k.
  have hH_e : ∀ k j, H (e k j) = σ k j := by
    intro k j
    change σ (splitEq.symm (splitEq (k, j))).1 (splitEq.symm (splitEq (k, j))).2
       = σ k j
    rw [splitEq.symm_apply_apply]
  -- H injective.
  have hH_inj : Function.Injective H := by
    intro i i' hii'
    set p := splitEq.symm i with hp_def
    set p' := splitEq.symm i' with hp'_def
    have hH_val : σ p.1 p.2 = σ p'.1 p'.2 := hii'
    have hk_eq : p.1 = p'.1 := by
      by_contra hne
      have hrange1 : σ p.1 p.2 ∈ Set.range (σ p.1) := ⟨p.2, rfl⟩
      have hrange2 : σ p.1 p.2 ∈ Set.range (σ p'.1) := ⟨p'.2, hH_val.symm⟩
      have hd := hσ_disj p.1 p'.1 hne
      exact (Set.disjoint_iff.mp hd) ⟨hrange1, hrange2⟩
    have hj_eq : p.2 = p'.2 := by
      have hσ_eq : σ p.1 p.2 = σ p.1 p'.2 := by rw [hk_eq] at hH_val ⊢; exact hH_val
      exact hσ_inj p.1 hσ_eq
    have hpp' : p = p' := Prod.ext hk_eq hj_eq
    calc i = splitEq p := (splitEq.apply_symm_apply i).symm
      _ = splitEq p' := by rw [hpp']
      _ = i' := splitEq.apply_symm_apply i'
  -- e per-block injective.
  have he_inj : ∀ k, Function.Injective (e k) := by
    intro k j j' hjj'
    have h1 : splitEq (k, j) = splitEq (k, j') := hjj'
    have h2 : (k, j) = (k, j') := splitEq.injective h1
    exact (Prod.mk.inj h2).2
  -- e cross-block disjoint.
  have he_disj : ∀ k k' : Fin (4 ^ l), k ≠ k' →
      Disjoint (Set.range (e k)) (Set.range (e k')) := by
    intro k k' hkk'
    rw [Set.disjoint_iff]
    rintro i ⟨⟨j, hj⟩, ⟨j', hj'⟩⟩
    have heq : splitEq (k, j) = splitEq (k', j') := hj.trans hj'.symm
    have hpair : (k, j) = (k', j') := splitEq.injective heq
    exact hkk' (Prod.mk.inj hpair).1
  -- e surjective on Fin(4^n).
  have he_surj : ∀ i : Fin (4 ^ n), ∃ k j, e k j = i := by
    intro i
    refine ⟨(splitEq.symm i).1, (splitEq.symm i).2, ?_⟩
    change splitEq ((splitEq.symm i).1, (splitEq.symm i).2) = i
    have : ((splitEq.symm i).1, (splitEq.symm i).2) = splitEq.symm i := rfl
    rw [this, splitEq.apply_symm_apply]
  -- Norm bound: A.submatrix (H ∘ e k) (H ∘ e k) = A.submatrix (σ k) (σ k).
  have h_norm : ∀ k, ‖A.submatrix (H ∘ e k) (H ∘ e k)‖ ≤ K * (1 / 2 : ℝ) ^ l := by
    intro k
    have hsubmat_eq : A.submatrix (H ∘ e k) (H ∘ e k)
                    = A.submatrix (σ k) (σ k) := by
      ext i j
      simp only [Matrix.submatrix_apply, Function.comp_apply, hH_e]
    rw [hsubmat_eq]
    exact hσ_bound k
  exact ⟨H, e, hH_inj, he_inj, he_disj, he_surj, h_norm⟩

/-- Fixed-depth wrapper around `bt_paving_depth_l_construction_uniform`. -/
lemma bt_paving_depth_l_construction (n l : ℕ) (hl : l ≤ n) :
    ∃ K_BT : ℝ, 0 < K_BT ∧
    ∀ (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ),
      ZeroDiag A → ‖A‖ = 1 →
    ∃ (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
      (e : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (4 ^ n)),
      Function.Injective H ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ k k' : Fin (4 ^ l), k ≠ k' →
        Disjoint (Set.range (e k)) (Set.range (e k'))) ∧
      (∀ i : Fin (4 ^ n), ∃ k j, e k j = i) ∧
      (∀ k, ‖A.submatrix (H ∘ e k) (H ∘ e k)‖ ≤ K_BT * (1 / 2 : ℝ) ^ l) := by
  obtain ⟨K_BT, hK_BT, hspec⟩ := bt_paving_depth_l_construction_uniform
  exact ⟨K_BT, hK_BT, hspec n l hl⟩

/-- Companion to `bt_paving_depth_l_construction`: the complement `H'` to `H`
covering the remaining `4^n` indices, with disjoint range and union `univ`.

Reuses `Pow4Bootstrap.buildComplement_S1i` (the `Finset.orderEmbOfFin`
construction on the complement set). -/
lemma bt_paving_depth_l_complement (n : ℕ)
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n)) (hH_inj : Function.Injective H) :
    ∃ H' : Fin (4 ^ n) → Fin (2 * 4 ^ n),
      Function.Injective H' ∧
      Disjoint (Set.range H) (Set.range H') ∧
      (Set.range H ∪ Set.range H') = Set.univ := by
  refine ⟨Pow4Bootstrap.buildComplement_S1i H hH_inj,
    Pow4Bootstrap.buildComplement_injective_S1i H hH_inj,
    Pow4Bootstrap.buildComplement_range_disjoint_S1i H hH_inj,
    Pow4Bootstrap.buildComplement_range_union_S1i H hH_inj⟩

/-! ## Phase 3.5 (BT-level lambdaA descent on H-submatrix)

A direct consequence of `bt_paving_depth_l_construction` plus
`lambdaA_BT_paving_descent`: at each σ-leaf, the principal submatrix
of `A` has `lambdaA ≤ K_BT · (1/2)^l · lambdaM(4^(n-l))`.  In the
H/e packaging, the leaves correspond exactly to
`A.submatrix (H ∘ e k) (H ∘ e k)`. -/
lemma lambdaA_BT_paving_descent_via_He
    (n l : ℕ) (hl : l ≤ n)
    (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1) :
    ∃ K_BT : ℝ, 0 < K_BT ∧
      ∃ (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
        (e : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (4 ^ n)),
        Function.Injective H ∧
        (∀ k, Function.Injective (e k)) ∧
        (∀ k k' : Fin (4 ^ l), k ≠ k' →
          Disjoint (Set.range (e k)) (Set.range (e k'))) ∧
        (∀ i : Fin (4 ^ n), ∃ k j, e k j = i) ∧
        (∀ k, lambdaA (A.submatrix (H ∘ e k) (H ∘ e k)) ≤
              K_BT * (1 / 2 : ℝ) ^ l * lambdaM (4 ^ (n - l))) := by
  obtain ⟨K_BT, hK_pos, hPaving⟩ := bt_paving_depth_l_construction n l hl
  obtain ⟨H, e, hH_inj, he_inj, he_disj, he_surj, h_norm⟩ := hPaving A hzd hnorm
  refine ⟨K_BT, hK_pos, H, e, hH_inj, he_inj, he_disj, he_surj, ?_⟩
  intro k
  -- The leaf submatrix is zero-diagonal.
  have hzd_leaf : ZeroDiag (A.submatrix (H ∘ e k) (H ∘ e k)) := by
    intro j; simp only [Matrix.submatrix_apply]; exact hzd _
  have h_scale := Pow4Bootstrap.lambdaA_scale_bound
    (A.submatrix (H ∘ e k) (H ∘ e k)) hzd_leaf
  have hlM_nn : (0 : ℝ) ≤ lambdaM (4 ^ (n - l)) := by
    unfold lambdaM
    apply Real.sSup_nonneg
    intro x hx
    obtain ⟨B, _, rfl⟩ := hx
    unfold lambdaA
    by_cases hne : ({c : ℝ | ∃ (B' C' : Matrix (Fin (4^(n - l))) (Fin (4^(n - l))) ℂ),
        IsDiagMatrix B' ∧ (∀ i, InUnitSquare (B' i i)) ∧ B = ⁅B', C'⁆ₘ ∧ ‖C'‖ ≤ c}).Nonempty
    · exact le_csInf hne (fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
  calc lambdaA (A.submatrix (H ∘ e k) (H ∘ e k))
      ≤ ‖A.submatrix (H ∘ e k) (H ∘ e k)‖ * lambdaM (4 ^ (n - l)) := h_scale
    _ ≤ K_BT * (1 / 2 : ℝ) ^ l * lambdaM (4 ^ (n - l)) :=
        mul_le_mul_of_nonneg_right (h_norm k) hlM_nn

/-! ## Phase 4 helpers (moved from `tmp_phase4_helper.lean`, session 16)

This section contains the Phase 4 sub-helpers needed for the iterated
`lambdaA_four_block_bound_strong` recursion over the H/e packaging.

Outline:
* Local non-negativity helpers (`lambdaA_nonneg_phase4`, `lambdaM_nonneg_phase4`).
* BT-cancellation arithmetic: `one_inv_eps_cancel_le_eight`,
  `two_inv_eps_pow_l_le_eight_two_pow`, `geom_sum_tight`.
* Positive homogeneity of `lambdaA`: `lambdaA_smul_le_nonneg`,
  `lambdaA_le_smul_pos`.
* σ-four-block step at norm ≤ 1: `four_block_step_norm_le_one`.
* Refinement Prop + perm-invariance helpers.
* Embedding-chain construction: `iter_4block_chain_He` (and its Fin-arithmetic
  equivalences).
* Per-step engine + induction algebra: `iter_4block_per_step_He`,
  `iter_4block_induct_He`.
* Depth-zero collapse: `lambdaA_depth_zero_collapse_He`.
* Top-level Phase 4 wrapper: `iter_4block_step_He` and
  `lambdaA_four_block_iterated_He`.
-/

/-! ### Local non-negativity helpers. -/

private lemma lambdaA_nonneg_phase4 {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ lambdaA A := by
  unfold lambdaA
  by_cases hne : ({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}).Nonempty
  · exact le_csInf hne (fun c ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp

private lemma lambdaM_nonneg_phase4 (m : ℕ) : 0 ≤ lambdaM m := by
  unfold lambdaM
  apply Real.sSup_nonneg
  intro x hx
  obtain ⟨B, _, rfl⟩ := hx
  exact lambdaA_nonneg_phase4 B

/- Historical development log (statuses below refer only to that earlier draft).
State: ✅ done — P5-D. `lambdaM 1 = 0`: any `Fin 1` zero-diag matrix is the
zero matrix (norm 0 ≠ 1), so the defining set is empty and the supremum is
`sSup ∅ = 0`. Proof adapted from the inline copy in `Main.lean`.
-/
/-- `lambdaM 1 = 0`: the only `1×1` zero-diagonal matrix is `0`, whose norm is
`0 ≠ 1`, so the set defining `lambdaM 1` is empty. -/
lemma lambdaM_one_eq_zero : lambdaM 1 = 0 := by
  unfold lambdaM
  by_cases hne :
      (lambdaA '' {A : Matrix (Fin 1) (Fin 1) ℂ | ZeroDiag A ∧ ‖A‖ = 1}).Nonempty
  · exfalso
    obtain ⟨_, A, ⟨hzd, hnorm⟩, rfl⟩ := hne
    have : A = 0 := by ext i j; fin_cases i; fin_cases j; exact hzd 0
    rw [this, norm_zero] at hnorm; linarith
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact Real.sSup_empty

/-! ### BT cancellation: `(2/(1-1/l))^l · (1/2)^l ≤ 8`. -/

/-- The crucial BT-cancellation: combined with the per-leaf `(1/2)^l`,
the `(2/(1-1/l))^l` from iterated Claim 1 cancels to a *constant*. -/
private lemma one_inv_eps_cancel_le_eight :
    ∀ l : ℕ, 2 ≤ l →
      ((2 : ℝ) / (1 - 1 / l)) ^ l * ((1 : ℝ) / 2) ^ l ≤ 8 := by
  intro l hl
  have hl_R : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hl_pos : (0 : ℝ) < (l : ℝ) := by linarith
  have hsub : (1 : ℝ) - 1 / l = ((l : ℝ) - 1) / (l : ℝ) := by field_simp
  have hsubpos : (0 : ℝ) < 1 - 1 / (l : ℝ) := by
    have hlm1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
    rw [hsub]; positivity
  -- (2/(1-1/l))^l · (1/2)^l = ((2/(1-1/l)) · (1/2))^l = (1/(1-1/l))^l
  have hprod : ((2 : ℝ) / (1 - 1 / l)) * ((1 : ℝ) / 2) = (1 : ℝ) / (1 - 1 / l) := by
    field_simp
  have hpow_eq : ((2 : ℝ) / (1 - 1 / l)) ^ l * ((1 : ℝ) / 2) ^ l =
      ((1 : ℝ) / (1 - 1 / l)) ^ l := by
    rw [← mul_pow, hprod]
  rw [hpow_eq]
  exact one_inv_eps_pow_l_le_eight l hl

/-- Bound on `(2/(1-1/l))^l ≤ 8 · 2^l` for `l ≥ 2`. -/
private lemma two_inv_eps_pow_l_le_eight_two_pow :
    ∀ l : ℕ, 2 ≤ l → ((2 : ℝ) / (1 - 1 / l)) ^ l ≤ 8 * (2 : ℝ) ^ l := by
  intro l hl
  have hl_R : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hl_pos : (0 : ℝ) < (l : ℝ) := by linarith
  have hsub : (1 : ℝ) - 1 / l = ((l : ℝ) - 1) / (l : ℝ) := by field_simp
  have hsubpos : (0 : ℝ) < 1 - 1 / (l : ℝ) := by
    have hlm1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
    rw [hsub]; positivity
  have hcanc := one_inv_eps_cancel_le_eight l hl
  -- (1/2)^l > 0; multiply both sides by 2^l
  have h2lpos : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have hhalf : ((1 : ℝ) / 2) ^ l * (2 : ℝ) ^ l = 1 := by
    rw [div_pow, one_pow, div_mul_cancel₀]
    exact ne_of_gt h2lpos
  -- Multiply `(2/(1-1/l))^l · (1/2)^l ≤ 8` by `2^l`.
  have hcanc2 :
      ((2 : ℝ) / (1 - 1 / l)) ^ l * ((1 : ℝ) / 2) ^ l * (2 : ℝ) ^ l
        ≤ 8 * (2 : ℝ) ^ l :=
    mul_le_mul_of_nonneg_right hcanc (le_of_lt h2lpos)
  have hrewrite :
      ((2 : ℝ) / (1 - 1 / l)) ^ l * ((1 : ℝ) / 2) ^ l * (2 : ℝ) ^ l =
      ((2 : ℝ) / (1 - 1 / l)) ^ l := by
    rw [mul_assoc, hhalf, mul_one]
  rw [hrewrite] at hcanc2
  exact hcanc2

/-- Geometric-sum tight bound: `∑_{i<l} (2/(1-1/l))^i ≤ 8 · 2^l` for `l ≥ 2`.

Uses `(2/(1-1/l))^l ≤ 8 · 2^l` and `∑_{i<l} r^i ≤ l · r^(l-1) ≤ r^l` when `r ≥ 2`. -/
private lemma geom_sum_tight :
    ∀ l : ℕ, 2 ≤ l →
      (∑ i ∈ Finset.range l, ((2 : ℝ) / (1 - 1 / l)) ^ i) ≤ 8 * (2 : ℝ) ^ l := by
  intro l hl
  have hl_R : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hl_pos : (0 : ℝ) < (l : ℝ) := by linarith
  have hsubpos : (0 : ℝ) < 1 - 1 / (l : ℝ) := by
    have hsub : (1 : ℝ) - 1 / l = ((l : ℝ) - 1) / (l : ℝ) := by field_simp
    have hlm1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
    rw [hsub]; positivity
  have hrpos : (0 : ℝ) < 2 / (1 - 1 / (l : ℝ)) := by positivity
  have hrnn : (0 : ℝ) ≤ 2 / (1 - 1 / (l : ℝ)) := le_of_lt hrpos
  -- r ≥ 2 ≥ 1, so 1 ≤ r, hence each term r^i ≤ r^(l-1) for i < l, and the sum ≤ l · r^(l-1).
  have h2_le_r : (2 : ℝ) ≤ 2 / (1 - 1 / (l : ℝ)) := by
    rw [le_div_iff₀ hsubpos]
    have h_inv : (0 : ℝ) ≤ 1 / (l : ℝ) := by positivity
    nlinarith
  have h1_le_r : (1 : ℝ) ≤ 2 / (1 - 1 / (l : ℝ)) := le_trans (by norm_num) h2_le_r
  have hterm_le : ∀ i ∈ Finset.range l,
      ((2 : ℝ) / (1 - 1 / l)) ^ i ≤ ((2 : ℝ) / (1 - 1 / l)) ^ l := by
    intro i hi
    have hi_lt : i < l := Finset.mem_range.mp hi
    exact pow_le_pow_right₀ h1_le_r (le_of_lt hi_lt)
  have hsum_le :
      (∑ i ∈ Finset.range l, ((2 : ℝ) / (1 - 1 / l)) ^ i) ≤
      ∑ _i ∈ Finset.range l, ((2 : ℝ) / (1 - 1 / l)) ^ l :=
    Finset.sum_le_sum hterm_le
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_le
  -- Use the geometric-sum formula: ∑ r^i = (r^l - 1)/(r-1).  r-1 ≥ 1, so sum ≤ r^l ≤ 8·2^l.
  have hrm1_pos : (0 : ℝ) < 2 / (1 - 1 / (l : ℝ)) - 1 := by linarith
  have hrm1_ge1 : (1 : ℝ) ≤ 2 / (1 - 1 / (l : ℝ)) - 1 := by linarith
  have hrne : (2 : ℝ) / (1 - 1 / (l : ℝ)) ≠ 1 := by linarith
  have hgeom := geom_sum_eq hrne l
  -- (r^l - 1)/(r-1) = ∑ r^i
  have hgeom' :
      (∑ i ∈ Finset.range l, ((2 : ℝ) / (1 - 1 / l)) ^ i) =
      (((2 : ℝ) / (1 - 1 / l)) ^ l - 1) / ((2 : ℝ) / (1 - 1 / l) - 1) := by
    linarith [hgeom]
  rw [hgeom']
  -- Bound (r^l - 1)/(r-1) ≤ r^l using r-1 ≥ 1.
  have hrl_nn : (0 : ℝ) ≤ ((2 : ℝ) / (1 - 1 / l)) ^ l := by positivity
  have hnum_nn : (0 : ℝ) ≤ ((2 : ℝ) / (1 - 1 / l)) ^ l - 1 := by
    have : (1 : ℝ) ≤ ((2 : ℝ) / (1 - 1 / l)) ^ l :=
      one_le_pow₀ h1_le_r
    linarith
  have hdiv_le : (((2 : ℝ) / (1 - 1 / l)) ^ l - 1) / ((2 : ℝ) / (1 - 1 / l) - 1) ≤
      ((2 : ℝ) / (1 - 1 / l)) ^ l := by
    rw [div_le_iff₀ hrm1_pos]
    nlinarith [hrl_nn]
  have hrl_le := two_inv_eps_pow_l_le_eight_two_pow l hl
  linarith

/- Historical development log (statuses below refer only to that earlier draft).
State: ✅ done — P5-A. Pure real-arithmetic facts underlying the asymmetric
η-trick: the `1/(1-2δ) ≤ 1+4δ` coefficient bound, two `InUnitSquare`
preservation bounds for the perturbed corner blocks, and the real-axis
spectral gap `≥ 2δ`. All four conjuncts are `nlinarith`/`abs_le` facts.
-/
/-- Asymmetric η-trick real arithmetic (for `0 < δ ≤ 1/4`):
1. `1/(1-2δ) ≤ 1+4δ` (the `(1+ε)` leading-coefficient bound);
2. `B'₁₁`-entries `(-1+δ)+δx` stay in `[-1,1]` when `|x| ≤ 1`;
3. `B'₂₂`-entries `2δ+(1-2δ)x` stay in `[-1,1]` when `|x| ≤ 1`;
4. the real-axis gap between the two perturbed blocks is `≥ 2δ`. -/
lemma asym_eta_trick_arith (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    (1 / (1 - 2*δ) ≤ 1 + 4*δ) ∧
    (∀ x : ℝ, |x| ≤ 1 → |(-1 + δ) + δ*x| ≤ 1) ∧
    (∀ x : ℝ, |x| ≤ 1 → |(2*δ) + (1 - 2*δ)*x| ≤ 1) ∧
    (∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 →
      2*δ ≤ ((2*δ) + (1-2*δ)*y) - ((-1+δ) + δ*x)) := by
  have h1m2δ : (0 : ℝ) < 1 - 2*δ := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ h1m2δ]
    nlinarith [hδ0, hδ]
  · intro x hx
    rw [abs_le] at hx ⊢
    constructor <;> nlinarith [hx.1, hx.2, hδ0, hδ]
  · intro x hx
    rw [abs_le] at hx ⊢
    constructor <;> nlinarith [hx.1, hx.2, hδ0, hδ]
  · intro x y hx hy
    rw [abs_le] at hx hy
    nlinarith [hx.1, hx.2, hy.1, hy.2, hδ0, hδ]

set_option maxHeartbeats 800000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
/-- Reindexed form of the paper's asymmetric Claim 2.

The analytical theorem in `Pow4Bootstrap` is stated for the canonical first
and second halves of `Fin (2 * m)`.  This wrapper turns any two disjoint,
covering injections `H` and `H'` into a permutation and transports the
bound to their principal submatrices. -/
lemma lambdaA_two_block_decomp_asym_reindex
    (m : ℕ)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1)
    (H H' : Fin m → Fin (2 * m))
    (hH_inj : Function.Injective H) (hH'_inj : Function.Injective H')
    (hdisj : Disjoint (Set.range H) (Set.range H'))
    (hcover : Set.range H ∪ Set.range H' = Set.univ)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hratio : c₁ / c₂ < 1 / 4)
    (hbnd₁ : lambdaA (A.submatrix H H) ≤ c₁)
    (hbnd₂ : lambdaA (A.submatrix H' H') ≤ c₂) :
    lambdaA A ≤
      (1 + 4 * (Real.sqrt (c₁ / c₂) + ‖A‖ / c₁)) * c₂ := by
  let splitMap : Fin (2 * m) → Fin (2 * m) := fun x =>
    if hx : x.val < m then
      H ⟨x.val, hx⟩
    else
      H' ⟨x.val - m, by have := x.isLt; omega⟩
  have hsplit_inj : Function.Injective splitMap := by
    intro x y hxy
    by_cases hx : x.val < m
    · by_cases hy : y.val < m
      · have hHxy : H ⟨x.val, hx⟩ = H ⟨y.val, hy⟩ := by
          simpa only [splitMap, hx, hy, dite_true] using hxy
        have hfin := hH_inj hHxy
        exact Fin.ext (congrArg (fun z : Fin m => z.val) hfin)
      · have hxH : splitMap x ∈ Set.range H := by
          refine ⟨⟨x.val, hx⟩, ?_⟩
          simp only [splitMap, hx, dite_true]
        have hyH' : splitMap y ∈ Set.range H' := by
          refine ⟨⟨y.val - m, by have := y.isLt; omega⟩, ?_⟩
          simp only [splitMap, hy, dite_false]
        rw [hxy] at hxH
        exact (Set.disjoint_left.1 hdisj hxH hyH').elim
    · by_cases hy : y.val < m
      · have hxH' : splitMap x ∈ Set.range H' := by
          refine ⟨⟨x.val - m, by have := x.isLt; omega⟩, ?_⟩
          simp only [splitMap, hx, dite_false]
        have hyH : splitMap y ∈ Set.range H := by
          refine ⟨⟨y.val, hy⟩, ?_⟩
          simp only [splitMap, hy, dite_true]
        rw [hxy] at hxH'
        exact (Set.disjoint_left.1 hdisj hyH hxH').elim
      · have hH'xy :
            H' ⟨x.val - m, by have := x.isLt; omega⟩ =
              H' ⟨y.val - m, by have := y.isLt; omega⟩ := by
          simpa only [splitMap, hx, hy, dite_false] using hxy
        have hfin := hH'_inj hH'xy
        apply Fin.ext
        have hvals := congrArg Fin.val hfin
        simp only [] at hvals
        omega
  have hsplit_surj : Function.Surjective splitMap := by
    intro z
    have hz : z ∈ Set.range H ∪ Set.range H' := by
      rw [hcover]
      exact Set.mem_univ z
    rcases hz with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · refine ⟨⟨i.val, by have := i.isLt; omega⟩, ?_⟩
      simp only [splitMap, i.isLt, dite_true]
    · refine ⟨⟨m + j.val, by have := j.isLt; omega⟩, ?_⟩
      have hnot : ¬(m + j.val < m) := by omega
      simp only [splitMap, hnot, dite_false]
      have hfin :
          (⟨(m + j.val) - m, by have := j.isLt; omega⟩ : Fin m) = j := by
        apply Fin.ext
        simp
      exact congrArg H' hfin
  let p : Fin (2 * m) ≃ Fin (2 * m) :=
    Equiv.ofBijective splitMap ⟨hsplit_inj, hsplit_surj⟩
  let A' : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
    A.submatrix (p : Fin (2 * m) → Fin (2 * m)) p
  have hzd' : ZeroDiag A' := by
    intro i
    simp only [A', Matrix.submatrix_apply]
    exact hzd (p i)
  have hnorm_eq : ‖A'‖ = ‖A‖ := by
    change ‖A.submatrix (p : Fin (2 * m) → Fin (2 * m)) p‖ = ‖A‖
    exact Pow4Bootstrap.submatrix_perm_norm_eq p A
  have hnorm' : ‖A'‖ ≤ 1 := by
    rw [hnorm_eq, hnorm]
  have hTL :
      (Matrix.of fun i j : Fin m =>
        A' ⟨i.val, by have := i.isLt; omega⟩
          ⟨j.val, by have := j.isLt; omega⟩) =
        A.submatrix H H := by
    ext i j
    simp only [A', Matrix.of_apply, Matrix.submatrix_apply, p,
      Equiv.ofBijective_apply, splitMap, i.isLt, j.isLt, dite_true]
  have hBR :
      (Matrix.of fun i j : Fin m =>
        A' ⟨m + i.val, by have := i.isLt; omega⟩
          ⟨m + j.val, by have := j.isLt; omega⟩) =
        A.submatrix H' H' := by
    ext i j
    have hi : ¬(m + i.val < m) := by omega
    have hj : ¬(m + j.val < m) := by omega
    simp only [A', Matrix.of_apply, Matrix.submatrix_apply, p,
      Equiv.ofBijective_apply, splitMap, hi, hj, dite_false]
    congr <;> omega
  have hclaim :=
    Pow4Bootstrap.lambdaA_two_block_decomp_asym c₁ c₂ hc₁ hc₂ hratio
      A' hzd' hnorm' (by simpa only [hTL] using hbnd₁)
        (by simpa only [hBR] using hbnd₂)
  rw [Pow4Bootstrap.lambdaA_perm_invariant A p] at hclaim
  rw [hnorm_eq] at hclaim
  exact hclaim

/-! ### Positive-homogeneity helper: `lambdaA ((c:ℂ) • A) ≤ c · lambdaA A`. -/

/-- Local commutator-scaling identity: `⁅B, c • C⁆ = c • ⁅B, C⁆`. -/
private lemma matComm_smul_right_phase4 {n : ℕ}
    (B C : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    matComm B (c • C) = c • matComm B C := by
  simp [matComm, smul_sub]

/-- One direction of positive homogeneity of `lambdaA`: for `c ≥ 0`,
`lambdaA ((c:ℂ) • A) ≤ c · lambdaA A`.

Holds for **all** matrices (no zero-diag hypothesis): the decomp set for
`c • A` is nonempty when `c = 0` (trivial `0 = ⁅0, 0⁆`), and inherits
nonemptiness from `A` when `c > 0` (via the witness `(B, c • C)`). -/
private lemma lambdaA_smul_le_nonneg {n : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    lambdaA ((c : ℂ) • A) ≤ c * lambdaA A := by
  rcases eq_or_lt_of_le hc with hc0 | hc_pos
  · -- c = 0: LHS = lambdaA 0 ≤ 0, RHS = 0
    rw [← hc0, Complex.ofReal_zero, zero_smul, zero_mul]
    unfold lambdaA
    apply csInf_le
    · exact ⟨0, fun c' ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
    · refine ⟨0, 0, ?_, ?_, ?_, by norm_num⟩
      · intro i j _; exact Matrix.zero_apply i j
      · intro i; refine ⟨?_, ?_⟩ <;> simp
      · ext i j; simp [matComm]
  · -- c > 0
    -- Case split on whether decomp set for A is nonempty.
    set S_A : Set ℝ := {c' : ℝ | ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
        IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c'} with hSA_def
    set S_cA : Set ℝ := {c' : ℝ | ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
        IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
        ((c : ℂ) • A) = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c'} with hScA_def
    have hbdd_A : BddBelow S_A :=
      ⟨0, fun c' ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
    have hbdd_cA : BddBelow S_cA :=
      ⟨0, fun c' ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
    -- Map: every witness for A produces a witness for c • A with c-scaled norm.
    have hmap : ∀ c' ∈ S_A, c * c' ∈ S_cA := by
      intro c' ⟨B, C, hd, hu, heq, hnC⟩
      refine ⟨B, (c : ℂ) • C, hd, hu, ?_, ?_⟩
      · rw [heq, ← matComm_smul_right_phase4]
      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
        exact mul_le_mul_of_nonneg_left hnC hc
    by_cases hne : S_A.Nonempty
    · -- S_A nonempty: standard csInf manipulation.
      have hne_cA : S_cA.Nonempty := by
        obtain ⟨c', hc'⟩ := hne
        exact ⟨c * c', hmap c' hc'⟩
      have hbound : ∀ c' ∈ S_A, lambdaA ((c : ℂ) • A) ≤ c * c' := by
        intro c' hc'
        exact csInf_le hbdd_cA (hmap c' hc')
      have hdiv : lambdaA ((c : ℂ) • A) / c ≤ lambdaA A := by
        unfold lambdaA
        rw [show {c' : ℝ | ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
            IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c'} = S_A
            from rfl]
        apply le_csInf hne
        intro c' hc'
        have := hbound c' hc'
        rwa [div_le_iff₀ hc_pos, mul_comm]
      rwa [div_le_iff₀ hc_pos, mul_comm] at hdiv
    · -- S_A empty: then S_cA is also empty (since `c•A = ⁅B,C⁆ → A = ⁅B, c⁻¹•C⁆`).
      have hc_ne : (c : ℂ) ≠ 0 := by
        rw [Ne, ← Complex.ofReal_zero, Complex.ofReal_inj]
        exact ne_of_gt hc_pos
      have hne_cA_empty : S_cA = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro c' ⟨B, C', hd, hu, heq_cA, _⟩
        apply hne
        -- Build a witness for S_A from the witness for S_cA.
        refine ⟨‖((c : ℂ)⁻¹ • C')‖, B, (c : ℂ)⁻¹ • C', hd, hu, ?_, le_refl _⟩
        -- A = ⁅B, c⁻¹ • C'⁆
        have hkey : A = (c : ℂ)⁻¹ • ((c : ℂ) • A) := by
          rw [smul_smul, inv_mul_cancel₀ hc_ne, one_smul]
        rw [hkey, heq_cA, ← matComm_smul_right_phase4]
      -- lambdaA(c•A) = sInf ∅ = 0; combined with nonneg this gives = 0.
      have hLA_cA : lambdaA ((c : ℂ) • A) ≤ 0 := by
        unfold lambdaA
        rw [show {c' : ℝ | ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
            IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
            ((c : ℂ) • A) = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c'} = S_cA from rfl, hne_cA_empty,
            Real.sInf_empty]
      -- lambdaA A = sInf ∅ = 0
      have hLA_A : lambdaA A = 0 := by
        unfold lambdaA
        rw [show {c' : ℝ | ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
            IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c'} = S_A
            from rfl, Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]
      rw [hLA_A, mul_zero]
      exact hLA_cA

/-- Reverse direction of positive homogeneity (for strictly positive c):
`c · lambdaA A ≤ lambdaA ((c:ℂ) • A)`.  Combined with
`lambdaA_smul_le_nonneg` this gives the full equality
`lambdaA ((c:ℂ) • A) = c · lambdaA A` for `c > 0`. -/
private lemma lambdaA_le_smul_pos {n : ℕ} (c : ℝ) (hc : 0 < c)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    c * lambdaA A ≤ lambdaA ((c : ℂ) • A) := by
  have hc_inv_pos : 0 < c⁻¹ := inv_pos.mpr hc
  have hc_inv_nn : 0 ≤ c⁻¹ := le_of_lt hc_inv_pos
  have hc_ne : (c : ℂ) ≠ 0 := by
    rw [Ne, ← Complex.ofReal_zero, Complex.ofReal_inj]; exact ne_of_gt hc
  -- Apply forward direction with c⁻¹ to (c • A):
  -- lambdaA(c⁻¹ • (c • A)) ≤ c⁻¹ * lambdaA(c • A)
  -- but c⁻¹ • (c • A) = A, so lambdaA A ≤ c⁻¹ * lambdaA(c • A),
  -- multiplying by c: c * lambdaA A ≤ lambdaA(c • A).
  have h := lambdaA_smul_le_nonneg c⁻¹ hc_inv_nn ((c : ℂ) • A)
  have hcc : ((c⁻¹ : ℝ) : ℂ) • ((c : ℝ) : ℂ) • A = A := by
    rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hc),
        Complex.ofReal_one, one_smul]
  rw [hcc] at h
  -- h : lambdaA A ≤ c⁻¹ * lambdaA ((c : ℂ) • A)
  -- Multiply by c > 0:
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hc)
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul] at hmul
  exact hmul

/-- Norm-≤-1 σ-four-block step bound: extends
`Pow4Bootstrap.lambdaA_sigma_four_block_bound_param` to matrices of norm
≤ 1 (rather than exactly 1) by rescaling.

**Mathematical proof**: If `‖M‖ = c ≤ 1` and `c > 0`, set
`N := c⁻¹ • M` so `‖N‖ = 1`.  Applying
`lambdaA_sigma_four_block_bound_param` to N (with `hStrong :=
lambdaA_four_block_bound_strong`) gives
  `lambdaA N ≤ 2/(1-δ) · sup_k lambdaA(N.sub e_k) + 6/δ`.
Multiplying by c ≥ 0:
  `c · lambdaA N ≤ 2/(1-δ) · c · sup_k lambdaA(N.sub e_k) + c · 6/δ`.
By positive homogeneity (`lambdaA_smul_le_nonneg`) and the
identities `c • N = M` (definitionally up to a `smul_smul`) and
`c • N.submatrix e_k e_k = M.submatrix e_k e_k`,
`lambdaA M ≤ c · lambdaA N` and `c · lambdaA(N.sub e_k) ≥
lambdaA(M.sub e_k)`. Hence:
  `lambdaA M ≤ 2/(1-δ) · sup_k lambdaA(M.sub e_k) + c · 6/δ
            ≤ 2/(1-δ) · sup_k lambdaA(M.sub e_k) + 6/δ`
since `c ≤ 1`.  If c = 0, then M = 0 and both sides reduce trivially. -/
private lemma four_block_step_norm_le_one
    {m : ℕ} (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (M : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ)
    (hzd : ZeroDiag M) (hnorm : ‖M‖ ≤ 1)
    (e : Fin 4 → Fin m → Fin (4 * m))
    (hinj : ∀ k, Function.Injective (e k))
    (hdisj : ∀ k k' : Fin 4, k ≠ k' → Disjoint (Set.range (e k)) (Set.range (e k')))
    (hsurj : ∀ i : Fin (4 * m), ∃ k j, e k j = i) :
    lambdaA M ≤ 2 / (1 - δ) *
        (⨆ k : Fin 4, lambdaA (M.submatrix (e k) (e k))) + 6 / δ := by
  classical
  -- Positivity of various RHS constants.
  have h1δ_pos : (0 : ℝ) < 1 - δ := sub_pos.mpr hδ1
  have h2_div_pos : (0 : ℝ) < 2 / (1 - δ) := by positivity
  have h6δ_pos : (0 : ℝ) < 6 / δ := by positivity
  have hsup_nn : (0 : ℝ) ≤ ⨆ k : Fin 4, lambdaA (M.submatrix (e k) (e k)) := by
    apply Real.iSup_nonneg
    intro k; exact lambdaA_nonneg_phase4 _
  have hRHS_nn : (0 : ℝ) ≤ 2 / (1 - δ) *
      (⨆ k : Fin 4, lambdaA (M.submatrix (e k) (e k))) + 6 / δ := by
    have := mul_nonneg (le_of_lt h2_div_pos) hsup_nn
    linarith
  -- Case split on ‖M‖ = 0 vs > 0.
  by_cases hM0 : ‖M‖ = 0
  · -- M = 0: lambdaA 0 ≤ 0 ≤ RHS.
    have hM_eq : M = 0 := norm_eq_zero.mp hM0
    have hLA0 : lambdaA M ≤ 0 := by
      rw [hM_eq]
      unfold lambdaA
      apply csInf_le
      · exact ⟨0, fun c' ⟨_, _, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
      · refine ⟨0, 0, ?_, ?_, ?_, by norm_num⟩
        · intro i j _; exact Matrix.zero_apply i j
        · intro i; refine ⟨?_, ?_⟩ <;> simp
        · ext i j; simp [matComm]
    linarith
  · -- ‖M‖ > 0: rescale.
    have hM_pos : 0 < ‖M‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hM0)
    have hM_ne : ‖M‖ ≠ 0 := ne_of_gt hM_pos
    set c : ℝ := ‖M‖ with hc_def
    have hc_pos : 0 < c := hM_pos
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have hc_le_one : c ≤ 1 := hnorm
    have hcC_ne : (c : ℂ) ≠ 0 := by
      rw [Ne, ← Complex.ofReal_zero, Complex.ofReal_inj]; exact ne_of_gt hc_pos
    have hc_inv_pos : 0 < c⁻¹ := inv_pos.mpr hc_pos
    -- N := c⁻¹ • M, satisfies ‖N‖ = 1, ZeroDiag N, and c • N = M.
    set N : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ := ((c⁻¹ : ℝ) : ℂ) • M with hN_def
    have hcN_eq_M : ((c : ℝ) : ℂ) • N = M := by
      rw [hN_def, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hM_ne,
          Complex.ofReal_one, one_smul]
    have hN_norm : ‖N‖ = 1 := by
      rw [hN_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hc_inv_pos, inv_mul_cancel₀ hM_ne]
    have hN_zd : ZeroDiag N := by
      intro i
      simp only [hN_def, Matrix.smul_apply, smul_eq_mul, hzd i, mul_zero]
    -- Apply lambdaA_sigma_four_block_bound_param to N (with hStrong =
    -- lambdaA_four_block_bound_strong).
    have hStrong :
        ∀ (A' : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ),
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
                    _ ≤ 4 * m := by nlinarith⟩ : Fin (4 * m))))) + 6 / δ :=
      fun A' hzd' hnorm' => Pow4Bootstrap.lambdaA_four_block_bound_strong δ hδ hδ1 A' hzd' hnorm'
    have hN_bound :=
      Pow4Bootstrap.lambdaA_sigma_four_block_bound_param δ hδ hδ1 N hN_zd hN_norm
        e hinj hdisj hsurj hStrong
    -- Multiply by c ≥ 0.
    have hN_bound_c : c * lambdaA N ≤
        c * (2 / (1 - δ) * (⨆ k : Fin 4, lambdaA (N.submatrix (e k) (e k))) + 6 / δ) :=
      mul_le_mul_of_nonneg_left hN_bound hc_nn
    -- Step A: lambdaA M ≤ c * lambdaA N.
    have hLA_M_le : lambdaA M ≤ c * lambdaA N := by
      have h := lambdaA_smul_le_nonneg c hc_nn N
      rwa [hcN_eq_M] at h
    -- Step B: c * lambdaA(N.sub e_k) ≤ lambdaA(M.sub e_k) for each k.
    -- Key equality: M.submatrix (e k) (e k) = (c : ℂ) • N.submatrix (e k) (e k).
    have hSubEq : ∀ k : Fin 4,
        M.submatrix (e k) (e k) = ((c : ℝ) : ℂ) • N.submatrix (e k) (e k) := by
      intro k
      conv_lhs => rw [← hcN_eq_M]
      rfl
    have hLeaf_ge : ∀ k : Fin 4,
        c * lambdaA (N.submatrix (e k) (e k)) ≤ lambdaA (M.submatrix (e k) (e k)) := by
      intro k
      rw [hSubEq k]
      exact lambdaA_le_smul_pos c hc_pos _
    -- Step C: c * sup_k lambdaA(N.sub e_k) ≤ sup_k lambdaA(M.sub e_k).
    have hbddM : BddAbove (Set.range
        (fun k : Fin 4 => lambdaA (M.submatrix (e k) (e k)))) :=
      (Set.finite_range _).bddAbove
    have hSupN_le_SupM_div :
        (⨆ k : Fin 4, lambdaA (N.submatrix (e k) (e k))) ≤
        (⨆ k : Fin 4, lambdaA (M.submatrix (e k) (e k))) / c := by
      apply ciSup_le
      intro k
      rw [le_div_iff₀ hc_pos]
      calc lambdaA (N.submatrix (e k) (e k)) * c
          = c * lambdaA (N.submatrix (e k) (e k)) := by ring
        _ ≤ lambdaA (M.submatrix (e k) (e k)) := hLeaf_ge k
        _ ≤ (⨆ k' : Fin 4, lambdaA (M.submatrix (e k') (e k'))) := le_ciSup hbddM k
    -- Combine: c * sup_N ≤ sup_M (after multiplying by c).
    have hcSupN_le_SupM :
        c * (⨆ k : Fin 4, lambdaA (N.submatrix (e k) (e k))) ≤
        (⨆ k : Fin 4, lambdaA (M.submatrix (e k) (e k))) := by
      have hmul := mul_le_mul_of_nonneg_left hSupN_le_SupM_div hc_nn
      have hcanc : c * ((⨆ k : Fin 4, lambdaA (M.submatrix (e k) (e k))) / c) =
          (⨆ k : Fin 4, lambdaA (M.submatrix (e k) (e k))) := by
        field_simp
      linarith [hcanc]
    -- Assemble.
    have hstep1 :
        c * (2 / (1 - δ) * (⨆ k : Fin 4, lambdaA (N.submatrix (e k) (e k))) + 6 / δ) =
        2 / (1 - δ) * (c * (⨆ k : Fin 4, lambdaA (N.submatrix (e k) (e k)))) +
        c * (6 / δ) := by ring
    have hstep2 :
        2 / (1 - δ) * (c * (⨆ k : Fin 4, lambdaA (N.submatrix (e k) (e k)))) ≤
        2 / (1 - δ) * (⨆ k : Fin 4, lambdaA (M.submatrix (e k) (e k))) :=
      mul_le_mul_of_nonneg_left hcSupN_le_SupM (le_of_lt h2_div_pos)
    have hstep3 : c * (6 / δ) ≤ 6 / δ := by
      have := mul_le_mul_of_nonneg_right hc_le_one (le_of_lt h6δ_pos)
      linarith
    linarith

/-! ### Refinement Prop + perm-invariance helpers. -/

/-- **Refinement certificate**: depth-`(d+1)` embedding `e'` is a 4-block
refinement of depth-`d` embedding `e`.

Concretely: there exists a per-`k` 4-block embedding
`split k : Fin 4 → Fin(4^(n-d-1)) → Fin(4^(n-d))` and a
`combine k : Fin 4 → Fin(4^(d+1))` such that for each `k : Fin(4^d)`:

* `split k` is per-block injective, pairwise disjoint, and surjective
  onto `Fin(4^(n-d))`;
* coherence: `e k (split k k' j') = e' (combine k k') j'`. -/
private def FourBlockRefine (n d : ℕ)
    (_hd : d + 1 ≤ n)
    (e : Fin (4 ^ d) → Fin (4 ^ (n - d)) → Fin (4 ^ n))
    (e' : Fin (4 ^ (d + 1)) → Fin (4 ^ (n - (d + 1))) → Fin (4 ^ n))
    : Prop :=
  ∃ (split : Fin (4 ^ d) → Fin 4 → Fin (4 ^ (n - (d + 1))) → Fin (4 ^ (n - d)))
    (combine : Fin (4 ^ d) → Fin 4 → Fin (4 ^ (d + 1))),
    (∀ k k', Function.Injective (split k k')) ∧
    (∀ k (k₁ k₂ : Fin 4), k₁ ≠ k₂ →
      Disjoint (Set.range (split k k₁)) (Set.range (split k k₂))) ∧
    (∀ k j, ∃ k' j', split k k' j' = j) ∧
    (∀ k k' j', e k (split k k' j') = e' (combine k k') j')

/-- **Local helper: norm of submatrix by permutation equals original norm.** -/
private lemma submatrix_perm_norm_eq_He {N : ℕ} (p : Fin N ≃ Fin N)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖A.submatrix (p : Fin N → Fin N) p‖ = ‖A‖ := by
  have h1 : ‖A.submatrix (p : Fin N → Fin N) p‖ ≤ ‖A‖ := by
    have hkey := submatrix_norm_le (p : Fin N → Fin N) p.injective A
    have hrw : Matrix.of (fun i j => A (p i) (p j)) =
        A.submatrix (p : Fin N → Fin N) p := by
      ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
    rw [hrw] at hkey
    exact hkey
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

/-- **Local helper**: IsDiagMatrix is preserved by submatrix with a permutation. -/
private lemma isDiagMatrix_submatrix_perm_He {N : ℕ} (p : Fin N ≃ Fin N)
    (B : Matrix (Fin N) (Fin N) ℂ) (hB : IsDiagMatrix B) :
    IsDiagMatrix (B.submatrix (p : Fin N → Fin N) p) := by
  intro i j hij
  simp only [Matrix.submatrix_apply]
  exact hB (p i) (p j) (fun h => hij (p.injective h))

/-- **Local helper**: diagonal entries of `B.submatrix p p` equal diagonal
entries of `B` at `p i`. -/
private lemma submatrix_perm_diag_He {N : ℕ} (p : Fin N ≃ Fin N)
    (B : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    (B.submatrix (p : Fin N → Fin N) p) i i = B (p i) (p i) := by
  simp [Matrix.submatrix_apply]

/-- **Local helper**: commutator distributes over `submatrix p p`. -/
private lemma matComm_submatrix_perm_He {N : ℕ} (p : Fin N ≃ Fin N)
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

/-- **Cross-type reindexing invariance of lambdaA**.  Given a bijection
`p : Fin N₁ ≃ Fin N₂` (necessarily `N₁ = N₂`) and a matrix `M` of size N₂,
`lambdaA(M.submatrix p p) = lambdaA M`. -/
private lemma lambdaA_reindex_invariant_He {N₁ N₂ : ℕ}
    (M : Matrix (Fin N₂) (Fin N₂) ℂ) (p : Fin N₁ ≃ Fin N₂) :
    lambdaA (M.submatrix (p : Fin N₁ → Fin N₂) p) = lambdaA M := by
  unfold lambdaA
  set S := {c : ℝ | ∃ (B C : Matrix (Fin N₂) (Fin N₂) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ M = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hS_def
  set S' := {c : ℝ | ∃ (B C : Matrix (Fin N₁) (Fin N₁) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
    M.submatrix (p : Fin N₁ → Fin N₂) p = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hS'_def
  have hSS' : S = S' := by
    apply Set.eq_of_subset_of_subset
    · intro c hc
      obtain ⟨B, C, hd, hu, heq, hle⟩ := hc
      refine ⟨B.submatrix (p : Fin N₁ → Fin N₂) p, C.submatrix (p : Fin N₁ → Fin N₂) p,
        ?_, ?_, ?_, ?_⟩
      · intro i j hij
        simp only [Matrix.submatrix_apply]
        exact hd (p i) (p j) (fun h => hij (p.injective h))
      · intro i
        have : (B.submatrix (p : Fin N₁ → Fin N₂) p) i i = B (p i) (p i) := by
          simp [Matrix.submatrix_apply]
        rw [this]; exact hu (p i)
      · rw [heq]
        unfold matComm
        have hBC : (B * C).submatrix (p : Fin N₁ → Fin N₂) p =
            B.submatrix (p : Fin N₁ → Fin N₂) p * C.submatrix (p : Fin N₁ → Fin N₂) p :=
          (Matrix.submatrix_mul_equiv B C (p : Fin N₁ → Fin N₂) p p).symm
        have hCB : (C * B).submatrix (p : Fin N₁ → Fin N₂) p =
            C.submatrix (p : Fin N₁ → Fin N₂) p * B.submatrix (p : Fin N₁ → Fin N₂) p :=
          (Matrix.submatrix_mul_equiv C B (p : Fin N₁ → Fin N₂) p p).symm
        ext i j
        have hBCij := congr_fun (congr_fun hBC i) j
        have hCBij := congr_fun (congr_fun hCB i) j
        simp only [Matrix.submatrix_apply, Matrix.sub_apply] at *
        rw [hBCij, hCBij]
      · -- Need: ‖C.submatrix p p‖ ≤ c.
        have hsub := submatrix_norm_le (p : Fin N₁ → Fin N₂) p.injective C
        have hrw : Matrix.of (fun i j => C (p i) (p j)) =
            C.submatrix (p : Fin N₁ → Fin N₂) p := by
          ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
        rw [hrw] at hsub
        linarith
    · intro c hc
      obtain ⟨B, C, hd, hu, heq, hle⟩ := hc
      refine ⟨B.submatrix (p.symm : Fin N₂ → Fin N₁) p.symm,
        C.submatrix (p.symm : Fin N₂ → Fin N₁) p.symm, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        simp only [Matrix.submatrix_apply]
        exact hd (p.symm i) (p.symm j) (fun h => hij (p.symm.injective h))
      · intro i
        have : (B.submatrix (p.symm : Fin N₂ → Fin N₁) p.symm) i i = B (p.symm i) (p.symm i) := by
          simp [Matrix.submatrix_apply]
        rw [this]; exact hu (p.symm i)
      · -- M = (M.submatrix p p).submatrix p.symm p.symm
        have hAround : (M.submatrix (p : Fin N₁ → Fin N₂) p).submatrix
            (p.symm : Fin N₂ → Fin N₁) p.symm = M := by
          ext i j; simp [Matrix.submatrix_apply, Equiv.apply_symm_apply]
        rw [← hAround, heq]
        unfold matComm
        have hBC : (B * C).submatrix (p.symm : Fin N₂ → Fin N₁) p.symm =
            B.submatrix (p.symm : Fin N₂ → Fin N₁) p.symm *
            C.submatrix (p.symm : Fin N₂ → Fin N₁) p.symm :=
          (Matrix.submatrix_mul_equiv B C (p.symm : Fin N₂ → Fin N₁) p.symm p.symm).symm
        have hCB : (C * B).submatrix (p.symm : Fin N₂ → Fin N₁) p.symm =
            C.submatrix (p.symm : Fin N₂ → Fin N₁) p.symm *
            B.submatrix (p.symm : Fin N₂ → Fin N₁) p.symm :=
          (Matrix.submatrix_mul_equiv C B (p.symm : Fin N₂ → Fin N₁) p.symm p.symm).symm
        ext i j
        have hBCij := congr_fun (congr_fun hBC i) j
        have hCBij := congr_fun (congr_fun hCB i) j
        simp only [Matrix.submatrix_apply, Matrix.sub_apply] at *
        rw [hBCij, hCBij]
      · -- ‖C.submatrix p.symm p.symm‖ ≤ c.
        have hsub := submatrix_norm_le (p.symm : Fin N₂ → Fin N₁) p.symm.injective C
        have hrw : Matrix.of (fun i j => C (p.symm i) (p.symm j)) =
            C.submatrix (p.symm : Fin N₂ → Fin N₁) p.symm := by
          ext i j; simp [Matrix.submatrix_apply, Matrix.of_apply]
        rw [hrw] at hsub
        linarith
  rw [hS_def, ← hSS']

/-- **Permutation invariance of lambdaA** (local mirror of
`Pow4Bootstrap.lambdaA_conj_invariant_S1g`).  For any permutation
`p : Fin N ≃ Fin N` and matrix `M`, `lambdaA(M.submatrix p p) = lambdaA M`. -/
private lemma lambdaA_perm_invariant_He {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ) (p : Fin N ≃ Fin N) :
    lambdaA (M.submatrix (p : Fin N → Fin N) p) = lambdaA M := by
  unfold lambdaA
  set S := {c : ℝ | ∃ (B C : Matrix (Fin N) (Fin N) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ M = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hS_def
  set S' := {c : ℝ | ∃ (B C : Matrix (Fin N) (Fin N) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
    M.submatrix (p : Fin N → Fin N) p = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hS'_def
  have hSS' : S = S' := by
    apply Set.eq_of_subset_of_subset
    · intro c hc
      obtain ⟨B, C, hd, hu, heq, hle⟩ := hc
      refine ⟨B.submatrix (p : Fin N → Fin N) p, C.submatrix (p : Fin N → Fin N) p,
        ?_, ?_, ?_, ?_⟩
      · exact isDiagMatrix_submatrix_perm_He p B hd
      · intro i; rw [submatrix_perm_diag_He p B i]; exact hu (p i)
      · rw [heq]; exact matComm_submatrix_perm_He p B C
      · rw [submatrix_perm_norm_eq_He p C]; exact hle
    · intro c hc
      obtain ⟨B, C, hd, hu, heq, hle⟩ := hc
      refine ⟨B.submatrix (p.symm : Fin N → Fin N) p.symm,
        C.submatrix (p.symm : Fin N → Fin N) p.symm, ?_, ?_, ?_, ?_⟩
      · exact isDiagMatrix_submatrix_perm_He p.symm B hd
      · intro i; rw [submatrix_perm_diag_He p.symm B i]; exact hu (p.symm i)
      · have hAround : (M.submatrix (p : Fin N → Fin N) p).submatrix
            (p.symm : Fin N → Fin N) p.symm = M := by
          ext i j; simp [Matrix.submatrix_apply, Equiv.apply_symm_apply]
        rw [← hAround, heq]; exact matComm_submatrix_perm_He p.symm B C
      · rw [submatrix_perm_norm_eq_He p.symm C]; exact hle
  rw [hS_def, ← hSS']

/-! ### Per-step engine. -/

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- Per-step engine.  Given a depth-`d` embedding and a refining
depth-`(d+1)` embedding, the iSup at depth `d` is bounded by
`2/(1-δ) · iSup at depth (d+1) + 6/δ`. -/
private lemma iter_4block_per_step_He
    (n d : ℕ) (hd : d + 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1)
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (hH_inj : Function.Injective H)
    (e : Fin (4 ^ d) → Fin (4 ^ (n - d)) → Fin (4 ^ n))
    (he_inj : ∀ k, Function.Injective (e k))
    (he_disj : ∀ k k' : Fin (4 ^ d), k ≠ k' →
      Disjoint (Set.range (e k)) (Set.range (e k')))
    (he_surj : ∀ i : Fin (4 ^ n), ∃ k j, e k j = i)
    (e' : Fin (4 ^ (d + 1)) → Fin (4 ^ (n - (d + 1))) → Fin (4 ^ n))
    (he'_inj : ∀ k, Function.Injective (e' k))
    (he'_disj : ∀ k k' : Fin (4 ^ (d + 1)), k ≠ k' →
      Disjoint (Set.range (e' k)) (Set.range (e' k')))
    (he'_surj : ∀ i : Fin (4 ^ n), ∃ k j, e' k j = i)
    (_href : FourBlockRefine n d hd e e') :
    (⨆ k : Fin (4 ^ d), lambdaA (A.submatrix (H ∘ e k) (H ∘ e k))) ≤
      2 / (1 - δ) *
        (⨆ k : Fin (4 ^ (d + 1)),
          lambdaA (A.submatrix (H ∘ e' k) (H ∘ e' k))) + 6 / δ := by
  classical
  -- Unpack the refinement certificate.
  obtain ⟨split, combine, hsplit_inj, hsplit_disj, hsplit_surj, hcoh⟩ := _href
  -- Numerical setup.
  have h1δ_pos : (0 : ℝ) < 1 - δ := sub_pos.mpr hδ1
  have h2_div_pos : (0 : ℝ) < 2 / (1 - δ) := by positivity
  have h6δ_pos : (0 : ℝ) < 6 / δ := by positivity
  -- Type-bridge: 4^(n-d) = 4 * 4^(n - (d+1)).
  have hpow_eq : (4 : ℕ) ^ (n - d) = 4 * 4 ^ (n - (d + 1)) := by
    rw [show n - d = (n - (d + 1)) + 1 from by omega, pow_succ]; ring
  -- castEq : Fin(4 * 4^(n - (d+1))) ≃ Fin(4^(n-d)).
  let castEq : Fin (4 * 4 ^ (n - (d + 1))) ≃ Fin (4 ^ (n - d)) :=
    (Fin.castOrderIso hpow_eq.symm).toEquiv
  -- For each k : Fin(4^d), define the H/e-composed map shifted through castEq.
  let f : Fin (4 ^ d) → Fin (4 * 4 ^ (n - (d + 1))) → Fin (2 * 4 ^ n) :=
    fun k j => H (e k (castEq j))
  -- f k is injective.
  have hf_inj : ∀ k, Function.Injective (f k) := by
    intro k a b hab
    have h1 : H (e k (castEq a)) = H (e k (castEq b)) := hab
    have h2 : e k (castEq a) = e k (castEq b) := hH_inj h1
    have h3 : castEq a = castEq b := he_inj k h2
    exact castEq.injective h3
  -- N k := A.submatrix (f k) (f k).
  set N : Fin (4 ^ d) →
      Matrix (Fin (4 * 4 ^ (n - (d + 1)))) (Fin (4 * 4 ^ (n - (d + 1)))) ℂ :=
    fun k => A.submatrix (f k) (f k) with hN_def
  -- ZeroDiag N k for each k.
  have hN_zd : ∀ k, ZeroDiag (N k) := by
    intro k i
    simp only [hN_def, Matrix.submatrix_apply]
    exact hzd _
  -- ‖N k‖ ≤ 1 for each k.
  have hN_norm_le : ∀ k, ‖N k‖ ≤ 1 := by
    intro k
    have hsub := submatrix_norm_le (f k) (hf_inj k) A
    have hrw : Matrix.of (fun i j => A (f k i) (f k j)) = N k := by
      ext i j; simp [hN_def, Matrix.submatrix_apply, Matrix.of_apply]
    rw [hrw] at hsub
    linarith [hsub, hnorm.le]
  -- Inner block embedding for the per-step bound.
  let e_loc : Fin (4 ^ d) → Fin 4 → Fin (4 ^ (n - (d + 1))) → Fin (4 * 4 ^ (n - (d + 1))) :=
    fun k k' j => castEq.symm (split k k' j)
  -- e_loc k is per-block injective.
  have he_loc_inj : ∀ k k', Function.Injective (e_loc k k') := by
    intro k k' a b hab
    have h1 : castEq.symm (split k k' a) = castEq.symm (split k k' b) := hab
    have h2 : split k k' a = split k k' b := castEq.symm.injective h1
    exact hsplit_inj k k' h2
  -- e_loc k blocks pairwise disjoint.
  have he_loc_disj : ∀ k (k₁ k₂ : Fin 4), k₁ ≠ k₂ →
      Disjoint (Set.range (e_loc k k₁)) (Set.range (e_loc k k₂)) := by
    intro k k₁ k₂ hne
    rw [Set.disjoint_iff]
    rintro y ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have h1 : castEq.symm (split k k₁ a) = castEq.symm (split k k₂ b) := ha.trans hb.symm
    have h2 : split k k₁ a = split k k₂ b := castEq.symm.injective h1
    have hr1 : split k k₁ a ∈ Set.range (split k k₁) := ⟨a, rfl⟩
    have hr2 : split k k₁ a ∈ Set.range (split k k₂) := ⟨b, h2.symm⟩
    exact (Set.disjoint_iff.mp (hsplit_disj k k₁ k₂ hne)) ⟨hr1, hr2⟩
  -- e_loc k is surjective onto Fin(4 * 4^(n-(d+1))).
  have he_loc_surj : ∀ k (i : Fin (4 * 4 ^ (n - (d + 1)))), ∃ k' j, e_loc k k' j = i := by
    intro k i
    obtain ⟨k', j, hkj⟩ := hsplit_surj k (castEq i)
    refine ⟨k', j, ?_⟩
    change castEq.symm (split k k' j) = i
    rw [hkj, castEq.symm_apply_apply]
  -- Apply four_block_step_norm_le_one to each N k.
  have hstep : ∀ k : Fin (4 ^ d),
      lambdaA (N k) ≤ 2 / (1 - δ) *
        (⨆ k' : Fin 4, lambdaA ((N k).submatrix (e_loc k k') (e_loc k k'))) + 6 / δ := by
    intro k
    exact four_block_step_norm_le_one δ hδ hδ1 (N k) (hN_zd k) (hN_norm_le k)
      (e_loc k) (he_loc_inj k) (he_loc_disj k) (he_loc_surj k)
  -- Per-leaf identity.
  have h_leaf_eq : ∀ k (k' : Fin 4),
      (N k).submatrix (e_loc k k') (e_loc k k') =
      A.submatrix (H ∘ e' (combine k k')) (H ∘ e' (combine k k')) := by
    intro k k'
    ext i j
    change A (f k (castEq.symm (split k k' i))) (f k (castEq.symm (split k k' j))) =
      A (H (e' (combine k k') i)) (H (e' (combine k k') j))
    simp only [f, castEq, Equiv.apply_symm_apply]
    rw [hcoh k k' i, hcoh k k' j]
  -- Show lambdaA (M k) = lambdaA (N k) via cast-permutation invariance.
  have hMN_eq : ∀ k : Fin (4 ^ d),
      lambdaA (A.submatrix (H ∘ e k) (H ∘ e k)) = lambdaA (N k) := by
    intro k
    have hsub_eq :
        N k = (A.submatrix (H ∘ e k) (H ∘ e k)).submatrix
          (castEq : Fin (4 * 4 ^ (n - (d + 1))) → Fin (4 ^ (n - d))) castEq := by
      ext i j
      simp [hN_def, Matrix.submatrix_apply, f, Function.comp]
    rw [hsub_eq]
    exact (lambdaA_reindex_invariant_He _ castEq).symm
  -- Bound: lambdaA(M k) ≤ 2/(1-δ) · sup_{k' : Fin 4} ... + 6/δ.
  have hstep' : ∀ k : Fin (4 ^ d),
      lambdaA (A.submatrix (H ∘ e k) (H ∘ e k)) ≤
        2 / (1 - δ) *
          (⨆ k' : Fin 4, lambdaA
            (A.submatrix (H ∘ e' (combine k k')) (H ∘ e' (combine k k')))) + 6 / δ := by
    intro k
    have hsup_eq :
        (⨆ k' : Fin 4, lambdaA ((N k).submatrix (e_loc k k') (e_loc k k'))) =
        (⨆ k' : Fin 4, lambdaA
          (A.submatrix (H ∘ e' (combine k k')) (H ∘ e' (combine k k')))) := by
      apply iSup_congr
      intro k'
      rw [h_leaf_eq k k']
    have := hstep k
    rw [hsup_eq] at this
    rw [hMN_eq k]
    exact this
  -- Bound the inner sup over Fin 4 by the full sup over Fin(4^(d+1)).
  have hbdd_full : BddAbove (Set.range
      (fun K : Fin (4 ^ (d + 1)) => lambdaA (A.submatrix (H ∘ e' K) (H ∘ e' K)))) :=
    (Set.finite_range _).bddAbove
  have hinner_le : ∀ k : Fin (4 ^ d),
      (⨆ k' : Fin 4, lambdaA
        (A.submatrix (H ∘ e' (combine k k')) (H ∘ e' (combine k k')))) ≤
      (⨆ K : Fin (4 ^ (d + 1)), lambdaA (A.submatrix (H ∘ e' K) (H ∘ e' K))) := by
    intro k
    apply ciSup_le
    intro k'
    exact le_ciSup hbdd_full (combine k k')
  -- Bound per-k.
  have hstep_full : ∀ k : Fin (4 ^ d),
      lambdaA (A.submatrix (H ∘ e k) (H ∘ e k)) ≤
        2 / (1 - δ) *
          (⨆ K : Fin (4 ^ (d + 1)), lambdaA (A.submatrix (H ∘ e' K) (H ∘ e' K))) +
          6 / δ := by
    intro k
    have h1 := hstep' k
    have h2 := hinner_le k
    have h2mul := mul_le_mul_of_nonneg_left h2 (le_of_lt h2_div_pos)
    linarith
  -- Take sup over k : Fin(4^d) on the LHS.
  apply ciSup_le
  intro k
  exact hstep_full k

/-! ### Helper equivalences for the embedding chain. -/

/-- Canonical equivalence `Fin(4^a) × Fin(4^b) ≃ Fin(4^(a+b))`. -/
private noncomputable def finPowProdEquiv (a b : ℕ) :
    Fin (4 ^ a) × Fin (4 ^ b) ≃ Fin (4 ^ (a + b)) :=
  finProdFinEquiv.trans (Fin.castOrderIso (by rw [← pow_add])).toEquiv

/-- Canonical equivalence `Fin(4^d) × Fin(4^(n-d)) ≃ Fin(4^n)` for `d ≤ n`. -/
private noncomputable def finPowDecompEquiv (n d : ℕ) (hd : d ≤ n) :
    Fin (4 ^ d) × Fin (4 ^ (n - d)) ≃ Fin (4 ^ n) :=
  (finPowProdEquiv d (n - d)).trans (Fin.castOrderIso (by rw [Nat.add_sub_cancel' hd])).toEquiv

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- Promote a user-given paving `e : Fin(4^l) → Fin(4^(n-l)) → Fin(4^n)` to a
genuine equivalence using injective/disjoint/surjective hypotheses. -/
private noncomputable def chainEEq (n l : ℕ) (hl : l ≤ n)
    (e : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (4 ^ n))
    (he_inj : ∀ k, Function.Injective (e k))
    (he_disj : ∀ k k' : Fin (4 ^ l), k ≠ k' →
      Disjoint (Set.range (e k)) (Set.range (e k')))
    (he_surj : ∀ i : Fin (4 ^ n), ∃ k j, e k j = i) :
    Fin (4 ^ l) × Fin (4 ^ (n - l)) ≃ Fin (4 ^ n) := by
  classical
  -- Total e : Fin(4^l) × Fin(4^(n-l)) → Fin(4^n) given by (k, j) ↦ e k j.
  let f : Fin (4 ^ l) × Fin (4 ^ (n - l)) → Fin (4 ^ n) := fun p => e p.1 p.2
  -- f is injective (from inj + disj).
  have hf_inj : Function.Injective f := by
    intro ⟨k1, j1⟩ ⟨k2, j2⟩ heq
    show (k1, j1) = (k2, j2)
    by_cases hk : k1 = k2
    · subst hk
      have hj : j1 = j2 := he_inj k1 heq
      rw [hj]
    · -- Then ranges disjoint, contradicting f (k1,j1) = f (k2,j2).
      exfalso
      have hr1 : f (k1, j1) ∈ Set.range (e k1) := ⟨j1, rfl⟩
      have hr2 : f (k1, j1) ∈ Set.range (e k2) := ⟨j2, heq.symm⟩
      exact (Set.disjoint_iff.mp (he_disj k1 k2 hk)) ⟨hr1, hr2⟩
  -- f is surjective.
  have hf_surj : Function.Surjective f := by
    intro i
    obtain ⟨k, j, hkj⟩ := he_surj i
    refine ⟨(k, j), ?_⟩
    change e k j = i
    exact hkj
  -- Build equivalence via Equiv.ofBijective.
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-- The rebracket equivalence `Fin(4^d) × Fin(4^(n-d)) ≃ Fin(4^l) × Fin(4^(n-l))`
for `d ≤ l ≤ n`, obtained by flattening both sides to `Fin(4^n)`. -/
private noncomputable def chainRebracket (n l d : ℕ) (hdl : d ≤ l) (hln : l ≤ n) :
    Fin (4 ^ d) × Fin (4 ^ (n - d)) ≃ Fin (4 ^ l) × Fin (4 ^ (n - l)) :=
  (finPowDecompEquiv n d (le_trans hdl hln)).trans (finPowDecompEquiv n l hln).symm

/-- **Embedding chain constructor.**  Given a depth-`l` embedding `e`
matching the user input, produce for each `d ≤ l` a depth-`d` embedding
plus a refinement certificate linking depths `d` and `d+1`. -/
private lemma iter_4block_chain_He
    (n l : ℕ) (hl : l ≤ n) (hl_pos : 1 ≤ l)
    (e : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (4 ^ n))
    (he_inj : ∀ k, Function.Injective (e k))
    (he_disj : ∀ k k' : Fin (4 ^ l), k ≠ k' →
      Disjoint (Set.range (e k)) (Set.range (e k')))
    (he_surj : ∀ i : Fin (4 ^ n), ∃ k j, e k j = i) :
    ∃ (E : ∀ d : ℕ, d ≤ l →
      (Fin (4 ^ d) → Fin (4 ^ (n - d)) → Fin (4 ^ n))),
      -- Each E d is injective/disjoint/surjective.
      (∀ d (hd : d ≤ l) k, Function.Injective (E d hd k)) ∧
      (∀ d (hd : d ≤ l) (k k' : Fin (4 ^ d)), k ≠ k' →
        Disjoint (Set.range (E d hd k)) (Set.range (E d hd k'))) ∧
      (∀ d (hd : d ≤ l) i, ∃ k j, E d hd k j = i) ∧
      -- E l = e.
      (∀ (hl' : l ≤ l), E l hl' = e) ∧
      -- Depth-0 collapse.
      (∀ (h0 : 0 ≤ l) (j : Fin (4 ^ (n - 0))),
          E 0 h0 0 j = Fin.cast (by simp) j) ∧
      -- Refinement between consecutive depths.
      (∀ d (hd : d + 1 ≤ l),
        FourBlockRefine n d (le_trans hd hl)
          (E d (Nat.le_of_succ_le hd)) (E (d + 1) hd)) := by
  classical
  let eEq : Fin (4 ^ l) × Fin (4 ^ (n - l)) ≃ Fin (4 ^ n) :=
    chainEEq n l hl e he_inj he_disj he_surj
  have heEq_apply : ∀ k j, eEq (k, j) = e k j := by
    intro k j; rfl
  let E : ∀ d : ℕ, d ≤ l → Fin (4 ^ d) → Fin (4 ^ (n - d)) → Fin (4 ^ n) :=
    fun d _hd k j =>
      if hd0 : d = 0 then
        Fin.cast (by rw [hd0]; simp) j
      else
        eEq (chainRebracket n l d (by omega) hl (k, j))
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Injectivity.
    intro d hd k a b hab
    simp only [E] at hab
    by_cases hd0 : d = 0
    · subst hd0
      simp only [dite_true] at hab
      have := (Fin.castOrderIso (by simp : 4 ^ (n - 0) = 4 ^ n)).toEquiv.injective hab
      exact this
    · simp only [dif_neg hd0] at hab
      have h1 := eEq.injective hab
      have h2 := (chainRebracket n l d (by omega) hl).injective h1
      exact (Prod.mk.inj h2).2
  · -- Disjointness.
    intro d hd k k' hkk'
    rw [Set.disjoint_iff]
    rintro i ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    simp only [E] at ha hb
    by_cases hd0 : d = 0
    · subst hd0
      exfalso
      apply hkk'
      have hk0 : k.val = 0 := by
        have hkLt : k.val < 4 ^ 0 := k.isLt
        have h40 : (4 : ℕ) ^ 0 = 1 := pow_zero 4
        omega
      have hk'0 : k'.val = 0 := by
        have hkLt : k'.val < 4 ^ 0 := k'.isLt
        have h40 : (4 : ℕ) ^ 0 = 1 := pow_zero 4
        omega
      apply Fin.ext; rw [hk0, hk'0]
    · simp only [dif_neg hd0] at ha hb
      exfalso
      apply hkk'
      have heq : eEq (chainRebracket n l d (by omega) hl (k, a)) =
                 eEq (chainRebracket n l d (by omega) hl (k', b)) := ha.trans hb.symm
      have h1 := eEq.injective heq
      have h2 := (chainRebracket n l d (by omega) hl).injective h1
      exact (Prod.mk.inj h2).1
  · -- Surjectivity.
    intro d hd i
    simp only [E]
    by_cases hd0 : d = 0
    · subst hd0
      refine ⟨0, Fin.cast (by simp : 4 ^ n = 4 ^ (n - 0)) i, ?_⟩
      simp only [dite_true]
      ext
      simp [Fin.cast]
    · let p : Fin (4 ^ d) × Fin (4 ^ (n - d)) :=
        (chainRebracket n l d (by omega) hl).symm (eEq.symm i)
      refine ⟨p.1, p.2, ?_⟩
      simp only [dif_neg hd0]
      show eEq (chainRebracket n l d (by omega) hl (p.1, p.2)) = i
      rw [show (p.1, p.2) = p from rfl]
      simp only [p, Equiv.apply_symm_apply]
  · -- E l = e.
    intro hl'
    funext k j
    simp only [E]
    by_cases hd0 : l = 0
    · exfalso; omega
    · simp only [dif_neg hd0]
      have hrebr : chainRebracket n l l le_rfl hl (k, j) = (k, j) := by
        unfold chainRebracket
        simp only [Equiv.trans_apply]
        rw [show (le_trans (le_refl l) hl) = hl from rfl]
        exact (finPowDecompEquiv n l hl).symm_apply_apply (k, j)
      rw [hrebr]
      exact heEq_apply k j
  · -- Depth-0 collapse.
    intro h0 j
    simp only [E, dite_true]
  · -- Refinement.
    intro d hd
    have hdl : d ≤ l := Nat.le_of_succ_le hd
    have hd1l : d + 1 ≤ l := hd
    have hd1n : d + 1 ≤ n := le_trans hd1l hl
    have hdn : d ≤ n := le_trans hdl hl
    have hpow_d1 : (4 : ℕ) ^ (d + 1) = 4 ^ d * 4 := by rw [pow_succ]
    have hpow_nd : (4 : ℕ) ^ (n - d) = 4 * 4 ^ (n - (d + 1)) := by
      rw [show n - d = (n - (d + 1)) + 1 from by omega, pow_succ]; ring
    let combineEq : Fin (4 ^ d) × Fin 4 ≃ Fin (4 ^ (d + 1)) :=
      finProdFinEquiv.trans (Fin.castOrderIso hpow_d1.symm).toEquiv
    let splitEq : Fin 4 × Fin (4 ^ (n - (d + 1))) ≃ Fin (4 ^ (n - d)) :=
      finProdFinEquiv.trans (Fin.castOrderIso hpow_nd.symm).toEquiv
    by_cases hd0 : d = 0
    · -- d = 0 case.
      subst hd0
      let combine : Fin (4 ^ 0) → Fin 4 → Fin (4 ^ 1) :=
        fun _ k₁ => combineEq (0, k₁)
      let split : Fin (4 ^ 0) → Fin 4 → Fin (4 ^ (n - 1)) → Fin (4 ^ (n - 0)) :=
        fun _ k₁ j' => Fin.cast (by simp : 4 ^ n = 4 ^ (n - 0))
          (E 1 hd1l (combineEq (0, k₁)) j')
      refine ⟨split, combine, ?_, ?_, ?_, ?_⟩
      · intro k k₁ a b hab
        have h1 : E 1 hd1l (combineEq (0, k₁)) a = E 1 hd1l (combineEq (0, k₁)) b := by
          have : (Fin.castOrderIso (by simp : 4 ^ n = 4 ^ (n - 0))).toEquiv
                  (E 1 hd1l (combineEq (0, k₁)) a) =
                 (Fin.castOrderIso (by simp : 4 ^ n = 4 ^ (n - 0))).toEquiv
                  (E 1 hd1l (combineEq (0, k₁)) b) := hab
          exact (Fin.castOrderIso (by simp : 4 ^ n = 4 ^ (n - 0))).toEquiv.injective this
        simp only [E] at h1
        rw [dif_neg (by decide : (1 : ℕ) ≠ 0)] at h1
        have h2 := eEq.injective h1
        have h3 := (chainRebracket n l 1 hd1l hl).injective h2
        exact (Prod.mk.inj h3).2
      · intro k k₁ k₂ hkk'
        rw [Set.disjoint_iff]
        rintro i ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        exfalso
        apply hkk'
        have h1 : Fin.cast (by simp : 4 ^ n = 4 ^ (n - 0))
                    (E 1 hd1l (combineEq (0, k₁)) a) =
                  Fin.cast (by simp : 4 ^ n = 4 ^ (n - 0))
                    (E 1 hd1l (combineEq (0, k₂)) b) := ha.trans hb.symm
        have h2 : E 1 hd1l (combineEq (0, k₁)) a = E 1 hd1l (combineEq (0, k₂)) b :=
          (Fin.castOrderIso (by simp : 4 ^ n = 4 ^ (n - 0))).toEquiv.injective h1
        simp only [E] at h2
        rw [dif_neg (by decide : (1 : ℕ) ≠ 0)] at h2
        have h3 := eEq.injective h2
        have h4 := (chainRebracket n l 1 hd1l hl).injective h3
        have h5 : combineEq (0, k₁) = combineEq (0, k₂) := (Prod.mk.inj h4).1
        have h6 : ((0 : Fin (4 ^ 0)), k₁) = ((0 : Fin (4 ^ 0)), k₂) := combineEq.injective h5
        exact (Prod.mk.inj h6).2
      · intro k j
        let i : Fin (4 ^ n) := Fin.cast (by simp : 4 ^ (n - 0) = 4 ^ n) j
        have hE1_surj : ∀ i' : Fin (4 ^ n), ∃ K J, E 1 hd1l K J = i' := by
          intro i'
          let p : Fin (4 ^ 1) × Fin (4 ^ (n - 1)) :=
            (chainRebracket n l 1 hd1l hl).symm (eEq.symm i')
          refine ⟨p.1, p.2, ?_⟩
          simp only [E]
          rw [dif_neg (by decide : (1 : ℕ) ≠ 0)]
          show eEq (chainRebracket n l 1 hd1l hl (p.1, p.2)) = i'
          rw [show (p.1, p.2) = p from rfl]
          simp only [p, Equiv.apply_symm_apply]
        obtain ⟨K, J, hKJ⟩ := hE1_surj i
        let kk : Fin (4 ^ 0) × Fin 4 := combineEq.symm K
        refine ⟨kk.2, J, ?_⟩
        change Fin.cast (by simp : 4 ^ n = 4 ^ (n - 0))
              (E 1 hd1l (combineEq (0, kk.2)) J) = j
        have hkk1 : kk.1 = 0 := by
          have : kk.1.val < 4 ^ 0 := kk.1.isLt
          have h40 : (4 : ℕ) ^ 0 = 1 := pow_zero 4
          apply Fin.ext; omega
        have hKeq : K = combineEq (0, kk.2) := by
          have : combineEq (kk.1, kk.2) = K := by
            change combineEq kk = K
            simp only [kk, Equiv.apply_symm_apply]
          rw [← this, hkk1]
        rw [← hKeq, hKJ]
        change (Fin.castOrderIso (by simp : 4 ^ n = 4 ^ (n - 0))).toEquiv
              ((Fin.castOrderIso (by simp : 4 ^ (n - 0) = 4 ^ n)).toEquiv j) = j
        exact (Fin.castOrderIso (by simp : 4 ^ n = 4 ^ (n - 0))).toEquiv.left_inv j
      · intro k k₁ j'
        have hk0 : k = 0 := by
          have hkLt : k.val < 4 ^ 0 := k.isLt
          have h40 : (4 : ℕ) ^ 0 = 1 := pow_zero 4
          apply Fin.ext; omega
        rw [hk0]
        change E 0 hdl (0 : Fin (4 ^ 0)) (split 0 k₁ j') = E 1 hd1l (combine 0 k₁) j'
        change E 0 hdl (0 : Fin (4 ^ 0))
              (Fin.cast (by simp : 4 ^ n = 4 ^ (n - 0))
                (E 1 hd1l (combineEq (0, k₁)) j')) =
              E 1 hd1l (combineEq (0, k₁)) j'
        simp only [E, dite_true]
        change (Fin.castOrderIso (by simp : 4 ^ (n - 0) = 4 ^ n)).toEquiv
              ((Fin.castOrderIso (by simp : 4 ^ n = 4 ^ (n - 0))).toEquiv
                (E 1 hd1l (combineEq (0, k₁)) j')) =
              E 1 hd1l (combineEq (0, k₁)) j'
        exact (Fin.castOrderIso (by simp : 4 ^ (n - 0) = 4 ^ n)).toEquiv.right_inv _
    · -- d ≥ 1 case.
      let combine : Fin (4 ^ d) → Fin 4 → Fin (4 ^ (d + 1)) :=
        fun k k₁ => combineEq (k, k₁)
      let split : Fin (4 ^ d) → Fin 4 → Fin (4 ^ (n - (d + 1))) → Fin (4 ^ (n - d)) :=
        fun _ k₁ j' => splitEq (k₁, j')
      refine ⟨split, combine, ?_, ?_, ?_, ?_⟩
      · intro k k₁ a b hab
        have h1 : splitEq (k₁, a) = splitEq (k₁, b) := hab
        have h2 := splitEq.injective h1
        exact (Prod.mk.inj h2).2
      · intro k k₁ k₂ hkk'
        rw [Set.disjoint_iff]
        rintro i ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        exfalso
        apply hkk'
        have h1 : splitEq (k₁, a) = splitEq (k₂, b) := ha.trans hb.symm
        have h2 := splitEq.injective h1
        exact (Prod.mk.inj h2).1
      · intro k j
        let p : Fin 4 × Fin (4 ^ (n - (d + 1))) := splitEq.symm j
        refine ⟨p.1, p.2, ?_⟩
        change splitEq (p.1, p.2) = j
        rw [show (p.1, p.2) = p from rfl]
        simp only [p, Equiv.apply_symm_apply]
      · intro k k₁ j'
        simp only [E]
        have hd1_ne : d + 1 ≠ 0 := Nat.succ_ne_zero _
        simp only [dif_neg hd1_ne]
        simp only [dif_neg hd0]
        congr 1
        unfold chainRebracket
        simp only [Equiv.trans_apply]
        congr 1
        apply Fin.ext
        have hLHS : (finPowDecompEquiv n d (le_trans hdl hl) (k, splitEq (k₁, j'))).val =
            (splitEq (k₁, j')).val + 4 ^ (n - d) * k.val := by
          unfold finPowDecompEquiv finPowProdEquiv
          simp [Fin.castOrderIso, Fin.cast, finProdFinEquiv]
        have hsplit_val : (splitEq (k₁, j')).val = j'.val + 4 ^ (n - (d + 1)) * k₁.val := by
          show (splitEq (k₁, j')).val = j'.val + 4 ^ (n - (d + 1)) * k₁.val
          simp [splitEq, Fin.castOrderIso, Fin.cast, finProdFinEquiv]
        have hRHS : (finPowDecompEquiv n (d+1) hd1n (combineEq (k, k₁), j')).val =
            j'.val + 4 ^ (n - (d + 1)) * (combineEq (k, k₁)).val := by
          unfold finPowDecompEquiv finPowProdEquiv
          simp [Fin.castOrderIso, Fin.cast, finProdFinEquiv]
        have hcombine_val : (combineEq (k, k₁)).val = k₁.val + 4 * k.val := by
          show (combineEq (k, k₁)).val = k₁.val + 4 * k.val
          simp [combineEq, Fin.castOrderIso, Fin.cast, finProdFinEquiv]
        rw [hLHS, hsplit_val, hRHS, hcombine_val]
        have hpow_eq : (4 : ℕ) ^ (n - d) = 4 ^ (n - (d + 1)) * 4 := by
          rw [show n - d = (n - (d + 1)) + 1 from by omega, pow_succ]
        rw [hpow_eq]
        ring

/-- **Induction algebra**: combine the per-step bound across depths
`0, 1, …, l-1` into the geometric-sum form. -/
private lemma iter_4block_induct_He
    (n l : ℕ) (hl1 : 2 ≤ l) (hl : l ≤ n)
    (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1)
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (hH_inj : Function.Injective H)
    (E : ∀ d : ℕ, d ≤ l →
      (Fin (4 ^ d) → Fin (4 ^ (n - d)) → Fin (4 ^ n)))
    (hE_inj : ∀ d (hd : d ≤ l) k, Function.Injective (E d hd k))
    (hE_disj : ∀ d (hd : d ≤ l) (k k' : Fin (4 ^ d)), k ≠ k' →
      Disjoint (Set.range (E d hd k)) (Set.range (E d hd k')))
    (hE_surj : ∀ d (hd : d ≤ l) i, ∃ k j, E d hd k j = i)
    (hE_refine : ∀ d (hd : d + 1 ≤ l),
      FourBlockRefine n d (le_trans hd hl)
        (E d (Nat.le_of_succ_le hd)) (E (d + 1) hd)) :
    ∀ (d : ℕ) (hd : d ≤ l),
      (⨆ k : Fin (4 ^ 0), lambdaA (A.submatrix (H ∘ E 0 (by omega) k)
          (H ∘ E 0 (by omega) k))) ≤
        ((2 : ℝ) / (1 - 1 / l)) ^ d *
          (⨆ k : Fin (4 ^ d), lambdaA (A.submatrix (H ∘ E d hd k)
            (H ∘ E d hd k))) +
        (∑ i ∈ Finset.range d, ((2 : ℝ) / (1 - 1 / l)) ^ i) * (6 * (l : ℝ)) := by
  classical
  set δ : ℝ := 1 / (l : ℝ) with hδ_def
  have hl_R : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
  have hl_pos : (0 : ℝ) < (l : ℝ) := by linarith
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  have hδ_lt1 : δ < 1 := by
    rw [hδ_def, div_lt_one hl_pos]; linarith
  have h1mδ_pos : (0 : ℝ) < 1 - δ := by linarith
  have hr_pos : (0 : ℝ) < 2 / (1 - δ) := by positivity
  have hr_nn : (0 : ℝ) ≤ 2 / (1 - δ) := le_of_lt hr_pos
  have h6δ_eq : 6 / δ = 6 * (l : ℝ) := by
    rw [hδ_def]; field_simp
  intro d
  induction d with
  | zero =>
    intro _
    simp
  | succ d ih =>
    intro hd
    have hd' : d ≤ l := Nat.le_of_succ_le hd
    have ih' := ih hd'
    have hd1l : d + 1 ≤ l := hd
    have hper :=
      iter_4block_per_step_He n d (le_trans hd1l hl) δ hδ_pos hδ_lt1
        A hzd hnorm H hH_inj
        (E d hd') (hE_inj d hd') (hE_disj d hd') (hE_surj d hd')
        (E (d + 1) hd) (hE_inj (d + 1) hd) (hE_disj (d + 1) hd) (hE_surj (d + 1) hd)
        (hE_refine d hd1l)
    have hrd_nn : (0 : ℝ) ≤ (2 / (1 - δ)) ^ d := pow_nonneg hr_nn d
    have hmul_step : (2 / (1 - δ)) ^ d *
        (⨆ k : Fin (4 ^ d), lambdaA (A.submatrix (H ∘ E d hd' k) (H ∘ E d hd' k))) ≤
      (2 / (1 - δ)) ^ (d + 1) *
        (⨆ k : Fin (4 ^ (d + 1)), lambdaA (A.submatrix (H ∘ E (d + 1) hd k)
          (H ∘ E (d + 1) hd k))) +
      (2 / (1 - δ)) ^ d * (6 / δ) := by
      have hstep := mul_le_mul_of_nonneg_left hper hrd_nn
      have hpow_eq : (2 / (1 - δ)) ^ (d + 1) = (2 / (1 - δ)) ^ d * (2 / (1 - δ)) :=
        pow_succ _ _
      have hrhs_eq : (2 / (1 - δ)) ^ d *
          (2 / (1 - δ) *
            (⨆ k : Fin (4 ^ (d + 1)), lambdaA (A.submatrix (H ∘ E (d + 1) hd k)
              (H ∘ E (d + 1) hd k))) + 6 / δ) =
          (2 / (1 - δ)) ^ (d + 1) *
            (⨆ k : Fin (4 ^ (d + 1)), lambdaA (A.submatrix (H ∘ E (d + 1) hd k)
              (H ∘ E (d + 1) hd k))) +
          (2 / (1 - δ)) ^ d * (6 / δ) := by
        rw [hpow_eq]; ring
      linarith [hrhs_eq]
    have hsum : (∑ i ∈ Finset.range (d + 1), ((2 : ℝ) / (1 - 1 / l)) ^ i) =
        (∑ i ∈ Finset.range d, ((2 : ℝ) / (1 - 1 / l)) ^ i) +
        ((2 : ℝ) / (1 - 1 / l)) ^ d := by
      exact Finset.sum_range_succ _ _
    have hδ_eq : (2 : ℝ) / (1 - δ) = (2 : ℝ) / (1 - 1 / l) := by rw [hδ_def]
    set Td1 : ℝ := ⨆ k : Fin (4 ^ (d + 1)),
      lambdaA (A.submatrix (H ∘ E (d + 1) hd k) (H ∘ E (d + 1) hd k)) with hTd1_def
    set Td : ℝ := ⨆ k : Fin (4 ^ d),
      lambdaA (A.submatrix (H ∘ E d hd' k) (H ∘ E d hd' k)) with hTd_def
    set T0 : ℝ := ⨆ k : Fin (4 ^ 0),
      lambdaA (A.submatrix (H ∘ E 0 (by omega) k) (H ∘ E 0 (by omega) k)) with hT0_def
    have ih'' : T0 ≤ ((2 : ℝ) / (1 - 1 / l)) ^ d * Td +
        (∑ i ∈ Finset.range d, ((2 : ℝ) / (1 - 1 / l)) ^ i) * (6 * (l : ℝ)) := ih'
    have hper' : Td ≤ 2 / (1 - δ) * Td1 + 6 / δ := hper
    have hmul_step' : ((2 : ℝ) / (1 - 1 / l)) ^ d * Td ≤
        ((2 : ℝ) / (1 - 1 / l)) ^ (d + 1) * Td1 +
          ((2 : ℝ) / (1 - 1 / l)) ^ d * (6 * (l : ℝ)) := by
      have hrd_nn' : 0 ≤ ((2 : ℝ) / (1 - 1 / l)) ^ d := by
        rw [← hδ_eq]; exact hrd_nn
      have hper'' : Td ≤ (2 : ℝ) / (1 - 1 / l) * Td1 + 6 * (l : ℝ) := by
        rw [← hδ_eq, ← h6δ_eq]; exact hper'
      have hstep' := mul_le_mul_of_nonneg_left hper'' hrd_nn'
      have hpow_eq' : ((2 : ℝ) / (1 - 1 / l)) ^ (d + 1) =
          ((2 : ℝ) / (1 - 1 / l)) ^ d * ((2 : ℝ) / (1 - 1 / l)) := pow_succ _ _
      nlinarith [hstep', hpow_eq']
    have hgoal : T0 ≤ ((2 : ℝ) / (1 - 1 / l)) ^ (d + 1) * Td1 +
        (∑ i ∈ Finset.range (d + 1), ((2 : ℝ) / (1 - 1 / l)) ^ i) * (6 * (l : ℝ)) := by
      have hsum_expand : (∑ i ∈ Finset.range (d + 1), ((2 : ℝ) / (1 - 1 / l)) ^ i) *
          (6 * (l : ℝ)) =
          (∑ i ∈ Finset.range d, ((2 : ℝ) / (1 - 1 / l)) ^ i) * (6 * (l : ℝ)) +
          ((2 : ℝ) / (1 - 1 / l)) ^ d * (6 * (l : ℝ)) := by
        rw [hsum]; ring
      linarith [ih'', hmul_step', hsum_expand]
    exact hgoal

/-- **Depth-zero collapse**: the iSup over `Fin(4^0)` of the lambdaA of the
submatrix indexed by `H ∘ E 0 _ k` reduces to `lambdaA (A.submatrix H H)`. -/
private lemma lambdaA_depth_zero_collapse_He
    (n l : ℕ)
    (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ)
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (E : ∀ d : ℕ, d ≤ l →
      (Fin (4 ^ d) → Fin (4 ^ (n - d)) → Fin (4 ^ n)))
    (hE_zero : ∀ (j : Fin (4 ^ (n - 0))),
        E 0 (by omega) 0 j = Fin.cast (by simp) j) :
    (⨆ k : Fin (4 ^ 0),
      lambdaA (A.submatrix (H ∘ E 0 (by omega) k) (H ∘ E 0 (by omega) k))) =
    lambdaA (A.submatrix H H) := by
  have hsupcollapse :
      (⨆ k : Fin (4 ^ 0),
        lambdaA (A.submatrix (H ∘ E 0 (by omega) k) (H ∘ E 0 (by omega) k))) =
      lambdaA (A.submatrix (H ∘ E 0 (by omega) (0 : Fin (4 ^ 0)))
        (H ∘ E 0 (by omega) (0 : Fin (4 ^ 0)))) := by
    apply le_antisymm
    · apply ciSup_le
      intro k
      have hk0 : k = 0 := by
        have hklt : k.val < 4 ^ 0 := k.isLt
        have h40 : (4 : ℕ) ^ 0 = 1 := pow_zero 4
        have hkval : k.val = 0 := by
          have : k.val < 1 := h40 ▸ hklt
          omega
        apply Fin.ext
        rw [hkval]
        simp
      rw [hk0]
    · exact le_ciSup
        (f := fun k : Fin (4 ^ 0) =>
          lambdaA (A.submatrix (H ∘ E 0 (by omega) k) (H ∘ E 0 (by omega) k)))
        (Set.finite_range _).bddAbove
        (0 : Fin (4 ^ 0))
  rw [hsupcollapse]
  have heq_sub :
      A.submatrix (H ∘ E 0 (by omega) (0 : Fin (4 ^ 0)))
        (H ∘ E 0 (by omega) (0 : Fin (4 ^ 0))) =
      (A.submatrix H H).submatrix
        (Fin.cast (by simp : 4 ^ (n - 0) = 4 ^ n))
        (Fin.cast (by simp : 4 ^ (n - 0) = 4 ^ n)) := by
    ext i j
    simp only [Matrix.submatrix_apply, Function.comp]
    rw [hE_zero i, hE_zero j]
  rw [heq_sub]
  have hcast_eq : Fin.cast (by simp : 4 ^ (n - 0) = 4 ^ n) =
      (Fin.castOrderIso (by simp : 4 ^ (n - 0) = 4 ^ n)).toEquiv := rfl
  rw [hcast_eq]
  exact lambdaA_perm_invariant_He _
    ((Fin.castOrderIso (by simp : 4 ^ (n - 0) = 4 ^ n)).toEquiv)

/-- The inner inductive step. -/
private lemma iter_4block_step_He
    (n l : ℕ) (hl1 : 2 ≤ l) (hl : l ≤ n)
    (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1)
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (e : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (4 ^ n))
    (hH_inj : Function.Injective H)
    (he_inj : ∀ k, Function.Injective (e k))
    (he_disj : ∀ k k' : Fin (4 ^ l), k ≠ k' →
      Disjoint (Set.range (e k)) (Set.range (e k')))
    (he_surj : ∀ i : Fin (4 ^ n), ∃ k j, e k j = i) :
    lambdaA (A.submatrix H H) ≤
      ((2 : ℝ) / (1 - 1 / l)) ^ l *
        (⨆ k : Fin (4 ^ l), lambdaA (A.submatrix (H ∘ e k) (H ∘ e k))) +
      (∑ i ∈ Finset.range l, ((2 : ℝ) / (1 - 1 / l)) ^ i) * (6 * (l : ℝ)) := by
  classical
  obtain ⟨E, hE_inj, hE_disj, hE_surj, hEl_eq, hE_zero, hE_refine⟩ :=
    iter_4block_chain_He n l hl (by omega : 1 ≤ l) e he_inj he_disj he_surj
  have hind :=
    iter_4block_induct_He n l hl1 hl A hzd hnorm H hH_inj E
      hE_inj hE_disj hE_surj hE_refine l le_rfl
  have hRHS_eq :
      (⨆ k : Fin (4 ^ l), lambdaA (A.submatrix (H ∘ E l le_rfl k)
        (H ∘ E l le_rfl k))) =
      (⨆ k : Fin (4 ^ l), lambdaA (A.submatrix (H ∘ e k) (H ∘ e k))) := by
    have heq := hEl_eq le_rfl
    rw [heq]
  have hLHS_eq :
      (⨆ k : Fin (4 ^ 0),
        lambdaA (A.submatrix (H ∘ E 0 (by omega) k) (H ∘ E 0 (by omega) k))) =
      lambdaA (A.submatrix H H) :=
    lambdaA_depth_zero_collapse_He n l A H E (hE_zero (by omega))
  rw [hLHS_eq, hRHS_eq] at hind
  exact hind

/-! ### Phase 4 main helper: `lambdaA_four_block_iterated_He`. -/

/-- Combines `iter_4block_step_He` with the per-leaf BT bound to derive
a constant-coefficient upper bound on `lambdaA(A.submatrix H H)`.

The leading factor cancels via `(2/(1-1/l))^l · (1/2)^l ≤ 8` and the
residual is bounded by `48 · l^3 · 2^l`, so `K_iter := max (8·K_BT) 48`. -/
lemma lambdaA_four_block_iterated_He
    (K_BT : ℝ) (hK_BT_pos : 0 < K_BT)
    (n l : ℕ) (hl1 : 2 ≤ l) (hl : l ≤ n)
    (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1)
    (H : Fin (4 ^ n) → Fin (2 * 4 ^ n))
    (e : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (4 ^ n))
    (hH_inj : Function.Injective H)
    (he_inj : ∀ k, Function.Injective (e k))
    (he_disj : ∀ k k' : Fin (4 ^ l), k ≠ k' →
      Disjoint (Set.range (e k)) (Set.range (e k')))
    (he_surj : ∀ i : Fin (4 ^ n), ∃ k j, e k j = i)
    (hLeaf_norm : ∀ k, ‖A.submatrix (H ∘ e k) (H ∘ e k)‖ ≤ K_BT * (1 / 2 : ℝ) ^ l) :
    lambdaA (A.submatrix H H) ≤
      max (8 * K_BT) 48 * lambdaM (4 ^ (n - l)) +
        max (8 * K_BT) 48 * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
  classical
  set K_iter : ℝ := max (8 * K_BT) 48 with hK_iter_def
  have hK8_pos : (0 : ℝ) < 8 * K_BT := by positivity
  have h48_pos : (0 : ℝ) < (48 : ℝ) := by norm_num
  have hK_iter_pos : (0 : ℝ) < K_iter := lt_of_lt_of_le hK8_pos (le_max_left _ _)
  have hK_iter_ge_8KBT : (8 * K_BT) ≤ K_iter := le_max_left _ _
  have hK_iter_ge_48 : (48 : ℝ) ≤ K_iter := le_max_right _ _
  have hl_R : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
  have hl_pos : (0 : ℝ) < (l : ℝ) := by linarith
  have hlM_nn : (0 : ℝ) ≤ lambdaM (4 ^ (n - l)) := lambdaM_nonneg_phase4 _
  have hε_pos : (0 : ℝ) < 1 / (l : ℝ) := by positivity
  have hε_lt_one : (1 : ℝ) / (l : ℝ) < 1 := by
    rw [div_lt_one hl_pos]; linarith
  have h1mε_pos : (0 : ℝ) < 1 - 1 / (l : ℝ) := by linarith
  have h2lpos : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have hhalflpos : (0 : ℝ) < ((1 : ℝ) / 2) ^ l := by positivity
  have hIter := iter_4block_step_He n l hl1 hl A hzd hnorm H e hH_inj he_inj he_disj he_surj
  have hzd_leaf : ∀ k, ZeroDiag (A.submatrix (H ∘ e k) (H ∘ e k)) := by
    intro k j; simp only [Matrix.submatrix_apply]; exact hzd _
  have h_leaf_le : ∀ k,
      lambdaA (A.submatrix (H ∘ e k) (H ∘ e k)) ≤
        K_BT * (1 / 2 : ℝ) ^ l * lambdaM (4 ^ (n - l)) := by
    intro k
    have h_scale := Pow4Bootstrap.lambdaA_scale_bound
      (A.submatrix (H ∘ e k) (H ∘ e k)) (hzd_leaf k)
    calc lambdaA (A.submatrix (H ∘ e k) (H ∘ e k))
        ≤ ‖A.submatrix (H ∘ e k) (H ∘ e k)‖ * lambdaM (4 ^ (n - l)) := h_scale
      _ ≤ K_BT * (1 / 2 : ℝ) ^ l * lambdaM (4 ^ (n - l)) :=
          mul_le_mul_of_nonneg_right (hLeaf_norm k) hlM_nn
  have h4l_pos : 0 < 4 ^ l := Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
  have h_leaves_bdd : BddAbove (Set.range
      (fun k : Fin (4 ^ l) => lambdaA (A.submatrix (H ∘ e k) (H ∘ e k)))) :=
    (Set.finite_range _).bddAbove
  have h_sup_le :
      (⨆ k : Fin (4 ^ l), lambdaA (A.submatrix (H ∘ e k) (H ∘ e k))) ≤
      K_BT * (1 / 2 : ℝ) ^ l * lambdaM (4 ^ (n - l)) := by
    apply ciSup_le
    intro k; exact h_leaf_le k
  set r : ℝ := ((2 : ℝ) / (1 - 1 / l)) ^ l with hr_def
  set S : ℝ := ∑ i ∈ Finset.range l, ((2 : ℝ) / (1 - 1 / l)) ^ i with hS_def
  have hr_nn : (0 : ℝ) ≤ r := by rw [hr_def]; positivity
  have hKBT_half_nn : (0 : ℝ) ≤ K_BT * (1 / 2 : ℝ) ^ l := by positivity
  have h_iter_leaf :
      r * (⨆ k : Fin (4 ^ l), lambdaA (A.submatrix (H ∘ e k) (H ∘ e k))) ≤
      r * (K_BT * (1 / 2 : ℝ) ^ l * lambdaM (4 ^ (n - l))) :=
    mul_le_mul_of_nonneg_left h_sup_le hr_nn
  have h_cancel : r * (K_BT * (1 / 2 : ℝ) ^ l) ≤ 8 * K_BT := by
    have hrhalf : r * ((1 : ℝ) / 2) ^ l ≤ 8 := by
      rw [hr_def]; exact one_inv_eps_cancel_le_eight l hl1
    have hrearrange : r * (K_BT * (1 / 2 : ℝ) ^ l) = K_BT * (r * ((1 : ℝ) / 2) ^ l) := by
      ring
    rw [hrearrange]
    have hKBT_nn : (0 : ℝ) ≤ K_BT := le_of_lt hK_BT_pos
    calc K_BT * (r * ((1 : ℝ) / 2) ^ l)
        ≤ K_BT * 8 := mul_le_mul_of_nonneg_left hrhalf hKBT_nn
      _ = 8 * K_BT := by ring
  have h_iter_leaf' :
      r * (⨆ k : Fin (4 ^ l), lambdaA (A.submatrix (H ∘ e k) (H ∘ e k))) ≤
      8 * K_BT * lambdaM (4 ^ (n - l)) := by
    calc r * (⨆ k : Fin (4 ^ l), lambdaA (A.submatrix (H ∘ e k) (H ∘ e k)))
        ≤ r * (K_BT * (1 / 2 : ℝ) ^ l * lambdaM (4 ^ (n - l))) := h_iter_leaf
      _ = (r * (K_BT * (1 / 2 : ℝ) ^ l)) * lambdaM (4 ^ (n - l)) := by ring
      _ ≤ (8 * K_BT) * lambdaM (4 ^ (n - l)) :=
          mul_le_mul_of_nonneg_right h_cancel hlM_nn
      _ = 8 * K_BT * lambdaM (4 ^ (n - l)) := by ring
  have hS_le : S ≤ 8 * (2 : ℝ) ^ l := by rw [hS_def]; exact geom_sum_tight l hl1
  have hS_nn : (0 : ℝ) ≤ S := by
    rw [hS_def]; apply Finset.sum_nonneg; intro i _; positivity
  have h6l_nn : (0 : ℝ) ≤ 6 * (l : ℝ) := by positivity
  have hS6l_le : S * (6 * (l : ℝ)) ≤ 48 * (l : ℝ) * (2 : ℝ) ^ l := by
    calc S * (6 * (l : ℝ))
        ≤ (8 * (2 : ℝ) ^ l) * (6 * (l : ℝ)) :=
          mul_le_mul_of_nonneg_right hS_le h6l_nn
      _ = 48 * (l : ℝ) * (2 : ℝ) ^ l := by ring
  have hl_le_lcubed : (l : ℝ) ≤ (l : ℝ) ^ 3 := by
    have h1l : (1 : ℝ) ≤ (l : ℝ) := by linarith
    calc (l : ℝ) = (l : ℝ) * 1 := (mul_one _).symm
      _ ≤ (l : ℝ) * ((l : ℝ) * (l : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ (l : ℝ))
          nlinarith
      _ = (l : ℝ) ^ 3 := by ring
  have h_residual : S * (6 * (l : ℝ)) ≤ 48 * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
    calc S * (6 * (l : ℝ))
        ≤ 48 * (l : ℝ) * (2 : ℝ) ^ l := hS6l_le
      _ ≤ 48 * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
          have hl3_nn : (0 : ℝ) ≤ (l : ℝ) ^ 3 := by positivity
          have h2l_nn : (0 : ℝ) ≤ (2 : ℝ) ^ l := le_of_lt h2lpos
          have h48_nn : (0 : ℝ) ≤ (48 : ℝ) := by norm_num
          have := mul_le_mul_of_nonneg_left hl_le_lcubed h48_nn
          have := mul_le_mul_of_nonneg_right this h2l_nn
          linarith
  have h_assembled :
      lambdaA (A.submatrix H H) ≤
        8 * K_BT * lambdaM (4 ^ (n - l)) + 48 * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
    calc lambdaA (A.submatrix H H)
        ≤ r * (⨆ k : Fin (4 ^ l), lambdaA (A.submatrix (H ∘ e k) (H ∘ e k))) +
            S * (6 * (l : ℝ)) := by
            simpa [hr_def, hS_def] using hIter
      _ ≤ 8 * K_BT * lambdaM (4 ^ (n - l)) + 48 * (l : ℝ) ^ 3 * (2 : ℝ) ^ l :=
          add_le_add h_iter_leaf' h_residual
  have h_absorb1 : 8 * K_BT * lambdaM (4 ^ (n - l)) ≤ K_iter * lambdaM (4 ^ (n - l)) :=
    mul_le_mul_of_nonneg_right hK_iter_ge_8KBT hlM_nn
  have hl3_2l_nn : (0 : ℝ) ≤ (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by positivity
  have h_absorb2 : 48 * (l : ℝ) ^ 3 * (2 : ℝ) ^ l ≤ K_iter * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
    have h48_le_K : (48 : ℝ) ≤ K_iter := hK_iter_ge_48
    have hl3_nn : (0 : ℝ) ≤ (l : ℝ) ^ 3 := by positivity
    have h2l_nn : (0 : ℝ) ≤ (2 : ℝ) ^ l := le_of_lt h2lpos
    have h1 := mul_le_mul_of_nonneg_right h48_le_K hl3_nn
    have h2 := mul_le_mul_of_nonneg_right h1 h2l_nn
    linarith
  linarith

/-! ## Phase 5 sub-lemmas (two-block lift + bridge to `lambdaM(4^n)`)

The Phase 4 helper `lambdaA_four_block_iterated_He` gives the per-A bound on
`lambdaA(A.submatrix H H)`. The following helpers provide the two-block lift
and monotonicity bridge:

* `lambdaA_pow4_BT_iterated_per_A`: combine Phase 4 with `lambdaA_two_block_decomp`
  to get a per-A bound `lambdaA A ≤ K_full · lambdaM(4^(n-l)) + K_full · l^3 · 2^l`
  for ZeroDiag norm-1 `A : Matrix (Fin (2 · 4^n)) (Fin (2 · 4^n)) ℂ`.
* `lambdaM_le_lambdaM_double_phase4`: the monotonicity bridge
  `lambdaM(4^n) ≤ lambdaM(2 · 4^n)`.

Historical development note: an early draft isolated the Phase 5 absorption
step as a placeholder in `lambdaA_pow4_BT_iterated_per_A`. This is a record
of that draft, not a statement that the current proof is unfinished. -/

/-! ### Zero-padding/restriction infrastructure for the monotonicity bridge

These helpers are local copies of the `finEmbed`/`zeroPad`/`restrict`
infrastructure in `Main.lean` (which is downstream of this file).  They are
kept `private` so they do not leak into the public namespace.  -/

/-- The canonical embedding `Fin n → Fin m` for `n ≤ m`. -/
private def finEmbed_p4bt {n m : ℕ} (h : n ≤ m) : Fin n → Fin m :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩

private lemma finEmbed_p4bt_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (finEmbed_p4bt h) :=
  fun _ _ hab => Fin.ext (Fin.mk.inj hab)

/-- Zero-pad an `n×n` matrix into an `m×m` matrix (`n ≤ m`). -/
private noncomputable def zeroPad_p4bt {n m : ℕ} (_h : n ≤ m)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j =>
    if hi : i.val < n then
      if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else 0
    else 0

private lemma zeroPad_p4bt_zeroDiag {n m : ℕ} (h : n ≤ m)
    {A : Matrix (Fin n) (Fin n) ℂ} (hzd : ZeroDiag A) :
    ZeroDiag (zeroPad_p4bt h A) := by
  intro i
  simp only [zeroPad_p4bt, Matrix.of_apply]
  by_cases hi : i.val < n
  · simp only [hi, dite_true]; exact hzd ⟨i.val, hi⟩
  · simp [hi]

/-- Restrict an `m×m` matrix to its upper-left `n×n` block. -/
private noncomputable def restrict_p4bt {n m : ℕ} (h : n ≤ m)
    (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => A (finEmbed_p4bt h i) (finEmbed_p4bt h j)

private lemma restrict_p4bt_zeroPad {n m : ℕ} (h : n ≤ m)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    restrict_p4bt h (zeroPad_p4bt h A) = A := by
  ext i j
  simp only [restrict_p4bt, zeroPad_p4bt, finEmbed_p4bt, Matrix.of_apply,
    i.isLt, j.isLt, dite_true]

private lemma sum_finEmbed_p4bt_eq {n m : ℕ} (h : n ≤ m) {α : Type*}
    [AddCommMonoid α] (f : Fin m → α)
    (hf : ∀ i : Fin m, ¬(i.val < n) → f i = 0) :
    ∑ i : Fin m, f i = ∑ i : Fin n, f (finEmbed_p4bt h i) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin m => i.val < n)]
  rw [show ∑ i ∈ Finset.filter (fun i : Fin m => ¬(i.val < n)) Finset.univ,
        f i = 0 from
    Finset.sum_eq_zero (fun i hi => hf i (Finset.mem_filter.mp hi).2),
    add_zero]
  symm
  show ∑ i : Fin n, f (finEmbed_p4bt h i) =
    ∑ i ∈ Finset.filter (fun i : Fin m => i.val < n) Finset.univ, f i
  apply Finset.sum_bij (fun i _ => finEmbed_p4bt h i)
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
  · intro i₁ _ i₂ _ h12; exact finEmbed_p4bt_injective h h12
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨⟨j.val, hj⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i _; rfl

private lemma restrict_p4bt_norm_le {n m : ℕ} (h : n ≤ m)
    (A : Matrix (Fin m) (Fin m) ℂ) :
    ‖restrict_p4bt h A‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simp only [LinearEquiv.trans_apply]
  change ‖Matrix.toEuclideanLin (restrict_p4bt h A) x‖ ≤ ‖A‖ * ‖x‖
  rw [show Matrix.toEuclideanLin (restrict_p4bt h A) x =
      WithLp.toLp 2 ((restrict_p4bt h A).mulVec x.ofLp) from
    Matrix.toLpLin_apply 2 2 (restrict_p4bt h A) x]
  set w := x.ofLp
  set padW : Fin m → ℂ :=
    fun i => if hi : i.val < n then w ⟨i.val, hi⟩ else 0
  set v : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 padW
  have hcomp : ∀ i : Fin n,
      ((restrict_p4bt h A).mulVec w) i = (A.mulVec padW) (finEmbed_p4bt h i) := by
    intro i
    simp only [restrict_p4bt, Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [show (fun j : Fin m => A (finEmbed_p4bt h i) j * padW j) =
        (fun j => if hj : j.val < n then
          A (finEmbed_p4bt h i) j * w ⟨j.val, hj⟩ else 0) from by
      ext j; simp only [padW]; split_ifs <;> simp]
    rw [sum_finEmbed_p4bt_eq h _ (fun j hj => by simp [hj])]
    congr 1; ext j; simp [finEmbed_p4bt, j.isLt]
  have sum_embed_le : ∀ (g : Fin m → ℝ), (∀ j, 0 ≤ g j) →
      ∑ i : Fin n, g (finEmbed_p4bt h i) ≤ ∑ j : Fin m, g j := by
    intro g hg
    calc ∑ i : Fin n, g (finEmbed_p4bt h i)
        = ∑ j ∈ Finset.image (finEmbed_p4bt h) Finset.univ, g j := by
          symm
          exact Finset.sum_image
            (fun i₁ _ i₂ _ h12 => finEmbed_p4bt_injective h h12)
      _ ≤ ∑ j : Fin m, g j :=
          Finset.sum_le_univ_sum_of_nonneg hg
  have hnorm_sq_le :
      ∑ i : Fin n, ‖((restrict_p4bt h A).mulVec w) i‖ ^ 2 ≤
      ∑ i : Fin m, ‖(A.mulVec padW) i‖ ^ 2 :=
    calc ∑ i : Fin n, ‖((restrict_p4bt h A).mulVec w) i‖ ^ 2
        = ∑ i : Fin n, ‖(A.mulVec padW) (finEmbed_p4bt h i)‖ ^ 2 := by
          congr 1; ext i; rw [hcomp]
      _ ≤ ∑ i : Fin m, ‖(A.mulVec padW) i‖ ^ 2 :=
          sum_embed_le _ (fun j => pow_nonneg (norm_nonneg _) 2)
  have hv_norm : ‖v‖ = ‖x‖ := by
    simp only [EuclideanSpace.norm_eq]
    congr 1
    rw [show ∑ i : Fin m, ‖(v : EuclideanSpace ℂ (Fin m)).ofLp i‖ ^ 2 =
        ∑ i : Fin m, ‖padW i‖ ^ 2 from rfl]
    rw [show ∑ i : Fin m, ‖padW i‖ ^ 2 =
          ∑ i : Fin n, ‖padW (finEmbed_p4bt h i)‖ ^ 2 from
      sum_finEmbed_p4bt_eq h (fun i => ‖padW i‖ ^ 2) (fun i hi => by
        simp [padW, show ¬(i.val < n) from hi])]
    congr 1; ext i
    simp only [padW, finEmbed_p4bt, i.isLt, dite_true]; rfl
  apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg
        (fun i _ => pow_nonneg (norm_nonneg _) 2)),
      mul_pow]
  have hAv : ‖(EuclideanSpace.equiv (Fin m) ℂ).symm
      (A.mulVec v.ofLp)‖ ≤ ‖A‖ * ‖v‖ :=
    Matrix.l2_opNorm_mulVec A v
  have hAv_sq :
      ∑ i : Fin m, ‖(A.mulVec padW) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖x‖ ^ 2 := by
    set Av := (EuclideanSpace.equiv (Fin m) ℂ).symm (A.mulVec v.ofLp)
    have hAv_sq : ‖Av‖ ^ 2 = ∑ i : Fin m, ‖Av.ofLp i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg
            (fun i _ => pow_nonneg (norm_nonneg _) 2))]
    have hAv_ofLp : ∀ i, Av.ofLp i = (A.mulVec padW) i := fun _ => rfl
    calc ∑ i : Fin m, ‖(A.mulVec padW) i‖ ^ 2
        = ∑ i : Fin m, ‖Av.ofLp i‖ ^ 2 := by congr 1
      _ = ‖Av‖ ^ 2 := hAv_sq.symm
      _ ≤ (‖A‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hAv 2
      _ = ‖A‖ ^ 2 * ‖v‖ ^ 2 := mul_pow _ _ _
      _ = ‖A‖ ^ 2 * ‖x‖ ^ 2 := by rw [hv_norm]
  linarith

private lemma zeroPad_p4bt_norm_eq {n m : ℕ} (h : n ≤ m)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖zeroPad_p4bt h A‖ = ‖A‖ := by
  apply le_antisymm
  · rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simp only [LinearEquiv.trans_apply]
    change ‖Matrix.toEuclideanLin (zeroPad_p4bt h A) x‖ ≤ ‖A‖ * ‖x‖
    rw [show Matrix.toEuclideanLin (zeroPad_p4bt h A) x =
        WithLp.toLp 2 ((zeroPad_p4bt h A).mulVec x.ofLp) from
      Matrix.toLpLin_apply 2 2 (zeroPad_p4bt h A) x]
    set v := x.ofLp
    set w : Fin n → ℂ := fun i => v (finEmbed_p4bt h i)
    set xn : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 w
    have hcomp_lt : ∀ (i : Fin m) (hi : i.val < n),
        ((zeroPad_p4bt h A).mulVec v) i = (A.mulVec w) ⟨i.val, hi⟩ := by
      intro i hi
      simp only [zeroPad_p4bt, Matrix.mulVec, dotProduct, Matrix.of_apply,
        hi, dite_true]
      rw [show (fun j : Fin m =>
          (if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0) * v j) =
          (fun j => if hj : j.val < n then
            A ⟨i.val, hi⟩ ⟨j.val, hj⟩ * v j else 0) from by
        ext j; split_ifs <;> simp]
      rw [sum_finEmbed_p4bt_eq h _ (fun j hj => by simp [hj])]
      congr 1; ext j
      change (if hj : j.val < n then
        A ⟨i.val, hi⟩ ⟨j.val, hj⟩ * v ⟨j.val, _⟩ else 0) =
          A ⟨i.val, hi⟩ j * w j
      simp only [j.isLt, dite_true, w, finEmbed_p4bt]
    have hcomp_ge : ∀ i : Fin m, ¬(i.val < n) →
        ((zeroPad_p4bt h A).mulVec v) i = 0 := by
      intro i hi
      simp only [zeroPad_p4bt, Matrix.mulVec, dotProduct, Matrix.of_apply,
        hi, dite_false]
      exact Finset.sum_eq_zero (fun _ _ => zero_mul _)
    apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg
          (fun i _ => pow_nonneg (norm_nonneg _) 2)),
        mul_pow]
    have hsum_eq : ∑ i : Fin m, ‖((zeroPad_p4bt h A).mulVec v) i‖ ^ 2 =
        ∑ i : Fin n, ‖(A.mulVec w) i‖ ^ 2 := by
      rw [sum_finEmbed_p4bt_eq h _ (fun i hi => by simp [hcomp_ge i hi])]
      congr 1; ext i
      rw [hcomp_lt (finEmbed_p4bt h i) i.isLt]; simp [finEmbed_p4bt]
    rw [hsum_eq]
    have hAxn := Matrix.l2_opNorm_mulVec A xn
    set Aw := (EuclideanSpace.equiv (Fin n) ℂ).symm (A.mulVec xn.ofLp)
    have hAw_sq : ‖Aw‖ ^ 2 = ∑ i : Fin n, ‖(A.mulVec w) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg
            (fun i _ => pow_nonneg (norm_nonneg _) 2))]
      congr 1
    have hxn_le : ‖xn‖ ≤ ‖x‖ := by
      simp only [EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      have sum_embed_le : ∀ (g : Fin m → ℝ), (∀ j, 0 ≤ g j) →
          ∑ i : Fin n, g (finEmbed_p4bt h i) ≤ ∑ j : Fin m, g j := by
        intro g hg
        calc ∑ i : Fin n, g (finEmbed_p4bt h i)
            = ∑ j ∈ Finset.image (finEmbed_p4bt h) Finset.univ, g j := by
              symm
              exact Finset.sum_image
                (fun i₁ _ i₂ _ h12 => finEmbed_p4bt_injective h h12)
          _ ≤ ∑ j : Fin m, g j := Finset.sum_le_univ_sum_of_nonneg hg
      exact sum_embed_le _ (fun j => pow_nonneg (norm_nonneg _) 2)
    calc ∑ i : Fin n, ‖(A.mulVec w) i‖ ^ 2
        = ‖Aw‖ ^ 2 := hAw_sq.symm
      _ ≤ (‖A‖ * ‖xn‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hAxn 2
      _ = ‖A‖ ^ 2 * ‖xn‖ ^ 2 := mul_pow _ _ _
      _ ≤ ‖A‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
  · calc ‖A‖
        = ‖restrict_p4bt h (zeroPad_p4bt h A)‖ := by rw [restrict_p4bt_zeroPad]
      _ ≤ ‖zeroPad_p4bt h A‖ := restrict_p4bt_norm_le h _

private lemma restrict_p4bt_matComm_of_diag {n m : ℕ} (h : n ≤ m)
    (B C : Matrix (Fin m) (Fin m) ℂ) (hdiag : IsDiagMatrix B) :
    restrict_p4bt h (⁅B, C⁆ₘ) = ⁅restrict_p4bt h B, restrict_p4bt h C⁆ₘ := by
  ext i j
  simp only [restrict_p4bt, matComm, Matrix.of_apply, Matrix.sub_apply,
    Matrix.mul_apply]
  set ei := finEmbed_p4bt h i
  set ej := finEmbed_p4bt h j
  have hBC : ∑ l : Fin m, B ei l * C l ej = B ei ei * C ei ej := by
    apply Fintype.sum_eq_single ei
    intro l hl
    have : B ei l = 0 := hdiag ei l (Ne.symm hl)
    simp [this]
  have hCB : ∑ l : Fin m, C ei l * B l ej = C ei ej * B ej ej := by
    apply Fintype.sum_eq_single ej
    intro l hl
    have : B l ej = 0 := hdiag l ej hl
    simp [this]
  have hBC' : ∑ x : Fin n, B ei (finEmbed_p4bt h x) * C (finEmbed_p4bt h x) ej =
      B ei ei * C ei ej := by
    apply Fintype.sum_eq_single i
    intro l hl
    have hne : finEmbed_p4bt h l ≠ ei :=
      fun heq => hl (finEmbed_p4bt_injective h heq)
    have : B ei (finEmbed_p4bt h l) = 0 :=
      hdiag ei (finEmbed_p4bt h l) (Ne.symm hne)
    simp [this]
  have hCB' : ∑ x : Fin n, C ei (finEmbed_p4bt h x) * B (finEmbed_p4bt h x) ej =
      C ei ej * B ej ej := by
    apply Fintype.sum_eq_single j
    intro l hl
    have hne : finEmbed_p4bt h l ≠ ej :=
      fun heq => hl (finEmbed_p4bt_injective h heq)
    have : B (finEmbed_p4bt h l) ej = 0 :=
      hdiag (finEmbed_p4bt h l) ej hne
    simp [this]
  rw [hBC, hCB, hBC', hCB']

private lemma lambdaA_p4bt_nonneg {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ lambdaA A := by
  unfold lambdaA
  by_cases hne : (({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧
      ‖C‖ ≤ c}).Nonempty)
  · exact le_csInf hne
      (fun c ⟨_, C', _, _, _, hle⟩ => le_trans (norm_nonneg _) hle)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp

/-- **Monotonicity bridge** `lambdaM(4^n) ≤ lambdaM(2 · 4^n)`.

A specialisation of the general `lambdaM_mono` lemma (proved in `Main.lean`
via the `zeroPad`/`restrict` infrastructure).  Restated here as a private
helper so that `Pow4BTRecursion.lean` does not depend on `Main.lean`.

The mathematical content: every norm-one ZeroDiag matrix on `Fin (4^n)` can
be zero-padded to a norm-one ZeroDiag matrix on `Fin (2·4^n)` whose
`lambdaA` is at least as large (any valid `[B, C]`-decomposition restricts
back), so the supremum over the larger size dominates. -/
private lemma lambdaM_le_lambdaM_double_phase4 (n : ℕ) :
    lambdaM (4 ^ n) ≤ lambdaM (2 * 4 ^ n) := by
  have h : 4 ^ n ≤ 2 * 4 ^ n := by
    have : 1 * 4 ^ n ≤ 2 * 4 ^ n :=
      Nat.mul_le_mul_right _ (by norm_num)
    simp
  set m₁ := 4 ^ n with hm₁_def
  set m₂ := 2 * 4 ^ n with hm₂_def
  -- The supremum target is nonneg (used in the empty branch).
  have hlM₂_nonneg : 0 ≤ lambdaM m₂ := by
    unfold lambdaM
    exact Real.sSup_nonneg (fun x hx => by
      obtain ⟨A, _, rfl⟩ := hx; exact lambdaA_p4bt_nonneg A)
  -- Main: every `lambdaA A` for `A` ZeroDiag norm-1 on `Fin m₁` is
  -- bounded by `lambdaM m₂` via the zero-pad embedding.
  have hkey : ∀ (A : Matrix (Fin m₁) (Fin m₁) ℂ),
      ZeroDiag A → ‖A‖ = 1 → lambdaA A ≤ lambdaM m₂ := by
    intro A hzd hnorm
    set A' := zeroPad_p4bt h A with hA'_def
    have hzd' : ZeroDiag A' := zeroPad_p4bt_zeroDiag h hzd
    have hnorm' : ‖A'‖ = 1 := by
      rw [hA'_def, zeroPad_p4bt_norm_eq]; exact hnorm
    -- `lambdaA A ≤ lambdaA A'` via restriction of any A'-decomp to A.
    have hle_lambda : lambdaA A ≤ lambdaA A' := by
      set T_A' := {c : ℝ | ∃ (B C : Matrix (Fin m₂) (Fin m₂) ℂ),
        IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
          A' = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hT_A'_def
      set T_A := {c : ℝ | ∃ (B C : Matrix (Fin m₁) (Fin m₁) ℂ),
        IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
          A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hT_A_def
      by_cases hT : T_A'.Nonempty
      · -- Standard csInf_le_csInf via restriction.
        unfold lambdaA
        apply csInf_le_csInf
        · exact ⟨0, fun c ⟨_, C, _, _, _, hle⟩ =>
            le_trans (norm_nonneg _) hle⟩
        · exact hT
        · intro c ⟨B', C', hdiag', husq', hcomm', hnormC'⟩
          refine ⟨restrict_p4bt h B', restrict_p4bt h C', ?_, ?_, ?_, ?_⟩
          · intro i j hij
            simp only [restrict_p4bt, Matrix.of_apply]
            exact hdiag' _ _
              (fun heq => hij (finEmbed_p4bt_injective h heq))
          · intro i
            simp only [restrict_p4bt, Matrix.of_apply]
            exact husq' (finEmbed_p4bt h i)
          · rw [← restrict_p4bt_matComm_of_diag h B' C' hdiag', ← hcomm',
                restrict_p4bt_zeroPad]
          · exact le_trans (restrict_p4bt_norm_le h C') hnormC'
      · -- T_A' empty ⇒ T_A empty (else we could lift a decomp).  Then
        -- `lambdaA A = sInf ∅ = 0 ≤ 0 = lambdaA A'`.
        exfalso
        apply hT
        -- We construct a decomp of A' from a decomp of A, but A may
        -- have no decomp either; in that case use the trivial fact that
        -- `0 = ⁅0, 0⁆ₘ`, which is only useful when A' = 0.  Since `‖A'‖ = 1 ≠ 0`,
        -- A' ≠ 0, so we cannot use that trivial decomp.  Instead, we
        -- exhibit a decomp of A' directly using the same construction as
        -- `zeroDiag_InUnitSquare_decomp_bounded_S1d` but built locally.
        -- However a simpler route: we know `lambdaA_scale_bound` is
        -- conditional on a decomp existing for the *scaled* matrix.  In
        -- practice every ZeroDiag A on `Fin m` with `m ≥ 2` has a decomp.
        -- We invoke the standard divisor-of-position construction.
        have hm₂2 : 2 ≤ m₂ := by
          have hm₁_pos : 1 ≤ m₁ := by
            rw [hm₁_def]
            exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))
          rw [hm₂_def]; omega
        -- Local clone of the S1d explicit decomposition.
        have hn1 : (0 : ℝ) < (m₂ : ℝ) - 1 := by
          have h1 : (1 : ℝ) < m₂ := by exact_mod_cast (show 1 < m₂ by omega)
          linarith
        set B := Matrix.diagonal (fun i : Fin m₂ =>
          (↑(i.val : ℕ) : ℂ) / (↑(m₂ - 1 : ℕ) : ℂ)) with hB_def
        set C := Matrix.of (fun i j : Fin m₂ =>
          if i = j then (0 : ℂ) else
            A' i j / ((↑(i.val : ℕ) : ℂ) / (↑(m₂ - 1 : ℕ) : ℂ) -
              (↑(j.val : ℕ) : ℂ) / (↑(m₂ - 1 : ℕ) : ℂ))) with hC_def
        refine ⟨‖C‖, B, C, ?_, ?_, ?_, le_refl _⟩
        · intro i j hij; exact Matrix.diagonal_apply_ne _ hij
        · intro i
          unfold InUnitSquare
          simp only [hB_def, Matrix.diagonal_apply_eq]
          have hcast : (↑↑i : ℂ) / (↑(m₂ - 1) : ℂ) =
              (↑((i.val : ℝ) / ((m₂ - 1 : ℕ) : ℝ)) : ℂ) := by push_cast; rfl
          rw [hcast, Complex.ofReal_re, Complex.ofReal_im]
          refine ⟨?_, by simp⟩
          rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
          apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
          exact_mod_cast Nat.le_sub_one_of_lt i.isLt
        · ext i j
          simp only [matComm, Matrix.sub_apply, Matrix.mul_apply]
          by_cases hij : i = j
          · subst hij; rw [hzd' i]
            simp only [hB_def, Matrix.diagonal_apply, hC_def, Matrix.of_apply]
            symm
            have h1 : ∀ x : Fin m₂,
                (if i = x then ↑↑i / (↑(m₂ - 1) : ℂ) else 0) *
                (if x = i then (0 : ℂ) else
                  A' x i / (↑↑x / ↑(m₂ - 1) - ↑↑i / ↑(m₂ - 1))) = 0 := by
              intro x; by_cases h : i = x
              · simp [h]
              · simp [h]
            have h2 : ∀ x : Fin m₂,
                (if i = x then (0 : ℂ) else
                  A' i x / (↑↑i / (↑(m₂ - 1) : ℂ) - ↑↑x / ↑(m₂ - 1))) *
                (if x = i then ↑↑x / (↑(m₂ - 1) : ℂ) else 0) = 0 := by
              intro x; by_cases h : i = x
              · simp [h]
              · have : ¬x = i := fun hc => h hc.symm; simp [h, this]
            rw [Finset.sum_eq_zero (fun x _ => h1 x),
                Finset.sum_eq_zero (fun x _ => h2 x), sub_self]
          · simp only [hB_def, Matrix.diagonal_apply, hC_def, Matrix.of_apply]
            have hs1 : ∀ x : Fin m₂,
                (if i = x then ↑↑i / (↑(m₂ - 1) : ℂ) else 0) *
                (if x = j then (0 : ℂ) else
                  A' x j / (↑↑x / ↑(m₂ - 1) - ↑↑j / ↑(m₂ - 1))) =
                if x = i then ↑↑i / (↑(m₂ - 1) : ℂ) *
                  (A' i j / (↑↑i / ↑(m₂ - 1) - ↑↑j / ↑(m₂ - 1))) else 0 := by
              intro x; by_cases hx : i = x
              · subst hx; simp [hij]
              · simp [hx, Ne.symm hx]
            have hs2 : ∀ x : Fin m₂,
                (if i = x then (0 : ℂ) else
                  A' i x / (↑↑i / (↑(m₂ - 1) : ℂ) - ↑↑x / ↑(m₂ - 1))) *
                (if x = j then ↑↑x / (↑(m₂ - 1) : ℂ) else 0) =
                if x = j then A' i j /
                  (↑↑i / (↑(m₂ - 1) : ℂ) - ↑↑j / ↑(m₂ - 1)) *
                  (↑↑j / (↑(m₂ - 1) : ℂ)) else 0 := by
              intro x; by_cases hx : x = j
              · subst hx; simp [hij]
              · simp [hx]
            simp_rw [hs1, hs2]
            simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
            set d := ↑↑i / (↑(m₂ - 1) : ℂ) - ↑↑j / ↑(m₂ - 1) with hd_def
            have hdiff_ne : d ≠ 0 := by
              rw [hd_def, div_sub_div_same]
              apply div_ne_zero
              · simp only [ne_eq, sub_eq_zero]
                exact_mod_cast Fin.val_ne_of_ne hij
              · exact_mod_cast (show (m₂ - 1 : ℕ) ≠ 0 by omega)
            rw [show ↑↑i / (↑(m₂ - 1) : ℂ) * (A' i j / d) -
                A' i j / d * (↑↑j / ↑(m₂ - 1)) =
                d * (A' i j / d) from by rw [hd_def]; ring]
            exact (mul_div_cancel₀ (A' i j) hdiff_ne).symm
    -- `lambdaA A' ≤ ‖A'‖ * lambdaM m₂ = lambdaM m₂` via `lambdaA_scale_bound`.
    have hscale : lambdaA A' ≤ ‖A'‖ * lambdaM m₂ :=
      lambdaA_scale_bound A' hzd'
    rw [hnorm', one_mul] at hscale
    exact le_trans hle_lambda hscale
  -- Wrap up: `lambdaM m₁ = sSup S₁ ≤ lambdaM m₂` by csSup_le.
  unfold lambdaM
  set S₁ := lambdaA ''
    {A : Matrix (Fin m₁) (Fin m₁) ℂ | ZeroDiag A ∧ ‖A‖ = 1} with hS₁_def
  by_cases hne : S₁.Nonempty
  · apply csSup_le hne
    intro x hx
    obtain ⟨A, ⟨hzd, hnorm⟩, rfl⟩ := hx
    exact hkey A hzd hnorm
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,
      show sSup (∅ : Set ℝ) = 0 from by simp]
    exact hlM₂_nonneg

/- Historical development log (statuses below refer only to that earlier draft).
State: ✅ done — P5-C. Packages the proven Phase-4 H-side bound. Pure glue
of `bt_paving_depth_l_construction`, `bt_paving_depth_l_complement`, and
`lambdaA_four_block_iterated_He` — produces the BT-paving union `H`, its
complement `H'`, and the iterated H-side `lambdaA` bound. Consumed by P5-B/P5-F.
-/
/- Historical development log (statuses below refer only to that earlier draft). State: ✅ done — P5-E. -/
/-- The finite products arising from repeated Claim 2 lifts are uniformly
bounded.  The proof uses `1 + x ≤ exp x` and the telescoping majorant
`1/(s+2)^2 ≤ 1/(s+1) - 1/(s+2)`. -/
lemma convergent_eta_product_bound (K : ℝ) (hK : 0 < K) :
    ∃ Pbound : ℝ, 1 ≤ Pbound ∧
      ∀ (a b : ℕ),
        ∏ s ∈ Finset.Ico a b, (1 + K / ((s : ℝ) + 2) ^ 2) ≤ Pbound := by
  refine ⟨Real.exp K, Real.one_le_exp hK.le, ?_⟩
  intro a b
  -- Step 1: each factor ≤ exp of the corresponding term.
  have hfactor : ∀ s ∈ Finset.Ico a b,
      (1 + K / ((s : ℝ) + 2) ^ 2) ≤ Real.exp (K / ((s : ℝ) + 2) ^ 2) := by
    intro s _
    have h := Real.add_one_le_exp (K / ((s : ℝ) + 2) ^ 2)
    linarith
  -- factors are nonneg
  have hnn : ∀ s ∈ Finset.Ico a b, (0 : ℝ) ≤ 1 + K / ((s : ℝ) + 2) ^ 2 := by
    intro s _
    have : (0 : ℝ) ≤ K / ((s : ℝ) + 2) ^ 2 := by positivity
    linarith
  -- Step 2: product ≤ product of exps
  have hprod_le : ∏ s ∈ Finset.Ico a b, (1 + K / ((s : ℝ) + 2) ^ 2) ≤
      ∏ s ∈ Finset.Ico a b, Real.exp (K / ((s : ℝ) + 2) ^ 2) :=
    Finset.prod_le_prod hnn hfactor
  -- Step 3: product of exps = exp of sum
  have hexp_sum : ∏ s ∈ Finset.Ico a b, Real.exp (K / ((s : ℝ) + 2) ^ 2) =
      Real.exp (∑ s ∈ Finset.Ico a b, K / ((s : ℝ) + 2) ^ 2) :=
    (Real.exp_sum _ _).symm
  -- Step 4: the telescoping sum bound  ∑ 1/(s+2)^2 ≤ 1
  have htel : ∀ s ∈ Finset.Ico a b,
      (1 : ℝ) / ((s : ℝ) + 2) ^ 2 ≤
        1 / ((s : ℝ) + 1) - 1 / ((s : ℝ) + 2) := by
    intro s _
    have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    have hs2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
    rw [div_sub_div _ _ (ne_of_gt hs1) (ne_of_gt hs2),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hs1, hs2]
  -- The telescoping sum itself: ∑_{Ico a b} (1/(s+1) - 1/(s+2)) = 1/(a+1) - 1/(b+1) ≤ 1
  have htelescope : ∀ (a b : ℕ), a ≤ b →
      ∑ s ∈ Finset.Ico a b, (1 / ((s : ℝ) + 1) - 1 / ((s : ℝ) + 2)) =
        1 / ((a : ℝ) + 1) - 1 / ((b : ℝ) + 1) := by
    intro a b hab
    induction b with
    | zero =>
      have : a = 0 := Nat.le_zero.mp hab
      subst this
      simp
    | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · have hab' : a ≤ b := Nat.lt_succ_iff.mp hlt
        rw [Finset.sum_Ico_succ_top hab', ih hab']
        push_cast
        ring
      · -- a ≥ b+1, and a ≤ b+1, so a = b+1
        have : a = b + 1 := le_antisymm hab hge
        subst this
        simp
  -- Now bound the sum
  have hsum_le : ∑ s ∈ Finset.Ico a b, K / ((s : ℝ) + 2) ^ 2 ≤ K := by
    rcases Nat.lt_or_ge b a with hba | hab
    · -- b < a: Ico is empty
      rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      exact hK.le
    · -- ∑ K/(s+2)^2 = K * ∑ 1/(s+2)^2
      have hfactored : ∑ s ∈ Finset.Ico a b, K / ((s : ℝ) + 2) ^ 2 =
          K * ∑ s ∈ Finset.Ico a b, 1 / ((s : ℝ) + 2) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      rw [hfactored]
      have hsum1 : ∑ s ∈ Finset.Ico a b, (1 : ℝ) / ((s : ℝ) + 2) ^ 2 ≤
          ∑ s ∈ Finset.Ico a b, (1 / ((s : ℝ) + 1) - 1 / ((s : ℝ) + 2)) :=
        Finset.sum_le_sum htel
      rw [htelescope a b hab] at hsum1
      have hle1 : 1 / ((a : ℝ) + 1) - 1 / ((b : ℝ) + 1) ≤ 1 := by
        have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
        have haR : (0 : ℝ) ≤ (a : ℝ) := by positivity
        have ha1 : 1 / ((a : ℝ) + 1) ≤ 1 := by
          rw [div_le_one ha]; linarith
        have hpos : (0 : ℝ) ≤ 1 / ((b : ℝ) + 1) := by positivity
        linarith
      have hsumle : ∑ s ∈ Finset.Ico a b, (1 : ℝ) / ((s : ℝ) + 2) ^ 2 ≤ 1 :=
        le_trans hsum1 hle1
      nlinarith [hsumle, hK]
  -- Combine
  rw [hexp_sum] at hprod_le
  refine le_trans hprod_le ?_
  exact Real.exp_le_exp.mpr hsum_le

/-- **Phase-4 H-side bound, packaged.** For a zero-diag norm-1 matrix on
`Fin (2·4^n)` with `2 ≤ l ≤ n`, produces the BT-paving union `H`, its
complement `H'` (with injectivity, disjointness, and `univ`-covering), and
the iterated bound
`lambdaA (A.submatrix H H) ≤ K_iter·λM(4^(n-l)) + K_iter·l³·2^l`. -/
lemma lambdaA_BT_small_side
    (n l : ℕ) (hl1 : 2 ≤ l) (hl : l ≤ n)
    (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1) :
    ∃ (K_iter : ℝ) (H H' : Fin (4 ^ n) → Fin (2 * 4 ^ n)),
      0 < K_iter ∧
      Function.Injective H ∧ Function.Injective H' ∧
      Disjoint (Set.range H) (Set.range H') ∧
      (Set.range H ∪ Set.range H') = Set.univ ∧
      lambdaA (A.submatrix H H) ≤
        K_iter * lambdaM (4 ^ (n - l)) + K_iter * (l : ℝ)^3 * (2 : ℝ)^l := by
  obtain ⟨K_BT, hK_BT_pos, hconstr⟩ := bt_paving_depth_l_construction n l hl
  obtain ⟨H, e, hH_inj, he_inj, he_disj, he_surj, hLeaf_norm⟩ := hconstr A hzd hnorm
  obtain ⟨H', hH'_inj, hHH'_disj, hHH'_union⟩ :=
    bt_paving_depth_l_complement n H hH_inj
  set K_iter : ℝ := max (8 * K_BT) 48
  have hK_iter_pos : 0 < K_iter := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 48) (le_max_right _ _)
  have hbound :=
    lambdaA_four_block_iterated_He K_BT hK_BT_pos n l hl1 hl A hzd hnorm
      H e hH_inj he_inj he_disj he_surj hLeaf_norm
  exact ⟨K_iter, H, H', hK_iter_pos, hH_inj, hH'_inj, hHH'_disj, hHH'_union, hbound⟩

/-- Uniform, norm-`≤ 1` form of the BT-selected-half estimate.  The constant is
chosen once, before `n`, `l`, and the matrix.  This quantifier order is needed
when the estimate is passed through `lambdaM` and iterated across dimensions. -/
lemma lambdaA_BT_small_side_uniform :
    ∃ K_iter : ℝ, 48 ≤ K_iter ∧
      ∀ (n l : ℕ), 2 ≤ l → l ≤ n →
      ∀ (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ),
        ZeroDiag A → ‖A‖ ≤ 1 →
        ∃ (H H' : Fin (4 ^ n) → Fin (2 * 4 ^ n)),
          Function.Injective H ∧ Function.Injective H' ∧
          Disjoint (Set.range H) (Set.range H') ∧
          (Set.range H ∪ Set.range H') = Set.univ ∧
          lambdaA (A.submatrix H H) ≤
            K_iter * lambdaM (4 ^ (n - l)) +
              K_iter * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
  classical
  obtain ⟨K_BT, hK_BT_pos, hconstruct⟩ := bt_paving_depth_l_construction_uniform
  set K_iter : ℝ := max (8 * K_BT) 48 with hK_iter_def
  have hK_iter_ge : (48 : ℝ) ≤ K_iter := by
    rw [hK_iter_def]
    exact le_max_right _ _
  refine ⟨K_iter, hK_iter_ge, ?_⟩
  intro n l hl1 hl A hzd hnorm
  by_cases hA0 : ‖A‖ = 0
  · have hAzero : A = 0 := norm_eq_zero.mp hA0
    let H : Fin (4 ^ n) → Fin (2 * 4 ^ n) := fun i =>
      ⟨i.val, by have := i.isLt; omega⟩
    have hH_inj : Function.Injective H := by
      intro i j hij
      apply Fin.ext
      simpa [H] using congrArg Fin.val hij
    obtain ⟨H', hH'_inj, hdisj, hcover⟩ :=
      bt_paving_depth_l_complement n H hH_inj
    refine ⟨H, H', hH_inj, hH'_inj, hdisj, hcover, ?_⟩
    have hlam_zero : lambdaA (A.submatrix H H) ≤ 0 := by
      rw [hAzero]
      simpa using lambdaA_smul_le_nonneg (n := 4 ^ n) 0 (by norm_num)
        (0 : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℂ)
    have hM_nn : 0 ≤ lambdaM (4 ^ (n - l)) := lambdaM_nonneg_phase4 _
    have hK_nn : 0 ≤ K_iter := le_trans (by norm_num) hK_iter_ge
    have hRHS_nn : 0 ≤
        K_iter * lambdaM (4 ^ (n - l)) +
          K_iter * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by positivity
    exact le_trans hlam_zero hRHS_nn
  · have hApos : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg A) (Ne.symm hA0)
    have hAne : (‖A‖ : ℝ) ≠ 0 := ne_of_gt hApos
    set N : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ :=
      (↑(‖A‖⁻¹) : ℂ) • A with hN_def
    have hNzd : ZeroDiag N := by
      intro i
      simp [hN_def, hzd i]
    have hNnorm : ‖N‖ = 1 := by
      rw [hN_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hApos), inv_mul_cancel₀ hAne]
    obtain ⟨H, e, hH_inj, he_inj, he_disj, he_surj, hLeaf_norm⟩ :=
      hconstruct n l hl N hNzd hNnorm
    obtain ⟨H', hH'_inj, hdisj, hcover⟩ :=
      bt_paving_depth_l_complement n H hH_inj
    have hNbound :=
      lambdaA_four_block_iterated_He K_BT hK_BT_pos n l hl1 hl N hNzd hNnorm
        H e hH_inj he_inj he_disj he_surj hLeaf_norm
    refine ⟨H, H', hH_inj, hH'_inj, hdisj, hcover, ?_⟩
    have hsub_eq : A.submatrix H H =
        (↑‖A‖ : ℂ) • N.submatrix H H := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.smul_apply, hN_def]
      rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hAne, Complex.ofReal_one, one_mul]
    have hscale : lambdaA (A.submatrix H H) ≤ ‖A‖ * lambdaA (N.submatrix H H) := by
      rw [hsub_eq]
      exact lambdaA_smul_le_nonneg ‖A‖ (norm_nonneg A) _
    have hRHS_nn : 0 ≤
        K_iter * lambdaM (4 ^ (n - l)) +
          K_iter * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
      have hK_nn : 0 ≤ K_iter := le_trans (by norm_num) hK_iter_ge
      have hM_nn : 0 ≤ lambdaM (4 ^ (n - l)) := lambdaM_nonneg_phase4 _
      positivity
    calc
      lambdaA (A.submatrix H H)
          ≤ ‖A‖ * lambdaA (N.submatrix H H) := hscale
      _ ≤ ‖A‖ * (K_iter * lambdaM (4 ^ (n - l)) +
            K_iter * (l : ℝ) ^ 3 * (2 : ℝ) ^ l) :=
          mul_le_mul_of_nonneg_left hNbound (norm_nonneg A)
      _ ≤ 1 * (K_iter * lambdaM (4 ^ (n - l)) +
            K_iter * (l : ℝ) ^ 3 * (2 : ℝ) ^ l) :=
          mul_le_mul_of_nonneg_right hnorm hRHS_nn
      _ = K_iter * lambdaM (4 ^ (n - l)) +
            K_iter * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := one_mul _

/-! ### Paper Claim 2 recurrences -/

/-- The logarithmic threshold used in the Claim 2 lift.  The fourth power is
exactly the safety margin which turns the asymmetric square-root term into an
`O(l⁻²)` multiplicative loss. -/
noncomputable def btClaimThreshold (K : ℝ) (n l : ℕ) : ℝ :=
  16 * (l : ℝ) ^ 4 *
    (K * lambdaM (4 ^ (n - l)) + K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l +
      (l : ℝ) ^ 2 + 1)

/-- Multiplicative loss in one Claim 2 lift. -/
noncomputable def btClaimFactor (l : ℕ) : ℝ :=
  1 + 8 / (l : ℝ) ^ 2

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- Numerical wrapper around the reindexed asymmetric Claim 2.  Supplying a
bound `small` on the selected half and `large` on the complement yields the
standard logarithmic threshold recurrence. -/
private lemma claim2_threshold_lift {m l : ℕ} (hl2 : 2 ≤ l)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1)
    (H H' : Fin m → Fin (2 * m))
    (hHinj : Function.Injective H) (hH'inj : Function.Injective H')
    (hdisj : Disjoint (Set.range H) (Set.range H'))
    (hcover : Set.range H ∪ Set.range H' = Set.univ)
    (small large : ℝ) (hsmall_nn : 0 ≤ small) (hlarge_nn : 0 ≤ large)
    (hbnd₁ : lambdaA (A.submatrix H H) ≤ small)
    (hbnd₂ : lambdaA (A.submatrix H' H') ≤ large) :
    lambdaA A ≤ btClaimFactor l *
      max (16 * (l : ℝ) ^ 4 * (small + (l : ℝ) ^ 2 + 1)) large := by
  have hlR : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  have hl2pos : (0 : ℝ) < (l : ℝ) ^ 2 := by positivity
  have hl4pos : (0 : ℝ) < (l : ℝ) ^ 4 := by positivity
  set c₁ : ℝ := small + (l : ℝ) ^ 2 + 1 with hc₁_def
  set threshold : ℝ := 16 * (l : ℝ) ^ 4 * c₁ with hthreshold_def
  set c₂ : ℝ := max threshold large with hc₂_def
  have hc₁_pos : 0 < c₁ := by rw [hc₁_def]; positivity
  have hthreshold_pos : 0 < threshold := by rw [hthreshold_def]; positivity
  have hc₂_pos : 0 < c₂ := lt_of_lt_of_le hthreshold_pos (le_max_left _ _)
  have hc₂_ge_threshold : threshold ≤ c₂ := le_max_left _ _
  have hc₂_ge_large : large ≤ c₂ := le_max_right _ _
  have hratio_nn : 0 ≤ c₁ / c₂ := div_nonneg hc₁_pos.le hc₂_pos.le
  have hratio_upper : c₁ / c₂ ≤ 1 / (16 * (l : ℝ) ^ 4) := by
    rw [div_le_iff₀ hc₂_pos]
    have hrewrite : 1 / (16 * (l : ℝ) ^ 4) * c₂ =
        c₂ / (16 * (l : ℝ) ^ 4) := by ring
    rw [hrewrite, le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (l : ℝ) ^ 4)]
    rw [hthreshold_def] at hc₂_ge_threshold
    nlinarith
  have hquarter_upper : 1 / (16 * (l : ℝ) ^ 4) < (1 : ℝ) / 4 := by
    apply one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4)
    have hl_sq_ge : (4 : ℝ) ≤ (l : ℝ) ^ 2 := by nlinarith [sq_nonneg ((l : ℝ) - 2)]
    have hl_four_ge : (16 : ℝ) ≤ (l : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((l : ℝ) ^ 2 - 4)]
    nlinarith
  have hratio : c₁ / c₂ < (1 : ℝ) / 4 :=
    lt_of_le_of_lt hratio_upper hquarter_upper
  have hsqrt_le : Real.sqrt (c₁ / c₂) ≤ 1 / (l : ℝ) ^ 2 := by
    have hratio_square : c₁ / c₂ ≤ (1 / (l : ℝ) ^ 2) ^ 2 := by
      calc
        c₁ / c₂ ≤ 1 / (16 * (l : ℝ) ^ 4) := hratio_upper
        _ ≤ (1 / (l : ℝ) ^ 2) ^ 2 := by
          rw [div_pow, one_pow]
          apply one_div_le_one_div_of_le
            (by positivity : (0 : ℝ) < ((l : ℝ) ^ 2) ^ 2)
          nlinarith [hl4pos]
    have hrhs_nn : 0 ≤ 1 / (l : ℝ) ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hratio_nn, Real.sqrt_nonneg (c₁ / c₂),
      sq_nonneg (Real.sqrt (c₁ / c₂) + 1 / (l : ℝ) ^ 2)]
  have hnorm_div : ‖A‖ / c₁ ≤ 1 / (l : ℝ) ^ 2 := by
    rw [hnorm, div_le_div_iff₀ hc₁_pos hl2pos, hc₁_def]
    nlinarith
  have hfactor_bound :
      1 + 4 * (Real.sqrt (c₁ / c₂) + ‖A‖ / c₁) ≤ btClaimFactor l := by
    calc
      1 + 4 * (Real.sqrt (c₁ / c₂) + ‖A‖ / c₁)
          ≤ 1 + 4 * (1 / (l : ℝ) ^ 2 + 1 / (l : ℝ) ^ 2) := by gcongr
      _ = btClaimFactor l := by rw [btClaimFactor]; ring
  have hbnd₁' : lambdaA (A.submatrix H H) ≤ c₁ := by
    rw [hc₁_def]
    nlinarith [sq_nonneg (l : ℝ)]
  have hbnd₂' : lambdaA (A.submatrix H' H') ≤ c₂ :=
    le_trans hbnd₂ hc₂_ge_large
  have hclaim := lambdaA_two_block_decomp_asym_reindex m A hzd hnorm H H'
    hHinj hH'inj hdisj hcover c₁ c₂ hc₁_pos hc₂_pos hratio hbnd₁' hbnd₂'
  have hcoef := mul_le_mul_of_nonneg_right hfactor_bound hc₂_pos.le
  have hc₂_eq : c₂ = max (16 * (l : ℝ) ^ 4 *
      (small + (l : ℝ) ^ 2 + 1)) large := by
    rw [hc₂_def, hthreshold_def, hc₁_def]
  calc
    lambdaA A ≤ (1 + 4 * (Real.sqrt (c₁ / c₂) + ‖A‖ / c₁)) * c₂ := hclaim
    _ ≤ btClaimFactor l * c₂ := hcoef
    _ = btClaimFactor l *
        max (16 * (l : ℝ) ^ 4 * (small + (l : ℝ) ^ 2 + 1)) large := by rw [hc₂_eq]

/-- Join maps selected inside the two canonical halves of `Fin (2*(2*m))`.
The first copy lands below `2*m`; the second is shifted by `2*m`. -/
private def joinHalfMaps {m : ℕ}
    (F₀ F₁ : Fin m → Fin (2 * m)) : Fin (2 * m) → Fin (2 * (2 * m)) := fun x =>
  if hx : x.val < m then
    ⟨(F₀ ⟨x.val, hx⟩).val, by have := (F₀ ⟨x.val, hx⟩).isLt; omega⟩
  else
    ⟨2 * m + (F₁ ⟨x.val - m, by have := x.isLt; omega⟩).val,
      by have := (F₁ ⟨x.val - m, by have := x.isLt; omega⟩).isLt; omega⟩

private lemma joinHalfMaps_injective {m : ℕ}
    {F₀ F₁ : Fin m → Fin (2 * m)}
    (hF₀ : Function.Injective F₀) (hF₁ : Function.Injective F₁) :
    Function.Injective (joinHalfMaps F₀ F₁) := by
  intro x y hxy
  by_cases hx : x.val < m
  · by_cases hy : y.val < m
    · have hval := congrArg Fin.val hxy
      simp only [joinHalfMaps, hx, hy, dite_true] at hval
      have hloc : F₀ ⟨x.val, hx⟩ = F₀ ⟨y.val, hy⟩ := Fin.ext hval
      have := congrArg Fin.val (hF₀ hloc)
      exact Fin.ext this
    · have hval := congrArg Fin.val hxy
      simp only [joinHalfMaps, hx, hy, dite_true, dite_false] at hval
      have hlt := (F₀ ⟨x.val, hx⟩).isLt
      omega
  · by_cases hy : y.val < m
    · have hval := congrArg Fin.val hxy
      simp only [joinHalfMaps, hx, hy, dite_true, dite_false] at hval
      have hlt := (F₀ ⟨y.val, hy⟩).isLt
      omega
    · have hval := congrArg Fin.val hxy
      simp only [joinHalfMaps, hx, hy, dite_false] at hval
      have hloc :
          F₁ ⟨x.val - m, by have := x.isLt; omega⟩ =
            F₁ ⟨y.val - m, by have := y.isLt; omega⟩ := by
        apply Fin.ext
        omega
      have hpre := congrArg Fin.val (hF₁ hloc)
      simp only [] at hpre
      apply Fin.ext
      omega

private lemma joinHalfMaps_disjoint {m : ℕ}
    {F₀ F₁ F₀' F₁' : Fin m → Fin (2 * m)}
    (hdisj₀ : Disjoint (Set.range F₀) (Set.range F₀'))
    (hdisj₁ : Disjoint (Set.range F₁) (Set.range F₁')) :
    Disjoint (Set.range (joinHalfMaps F₀ F₁))
      (Set.range (joinHalfMaps F₀' F₁')) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, rfl⟩ ⟨y, hxy⟩
  by_cases hx : x.val < m
  · by_cases hy : y.val < m
    · have hval := congrArg Fin.val hxy
      simp only [joinHalfMaps, hx, hy, dite_true] at hval
      have heq : F₀ ⟨x.val, hx⟩ = F₀' ⟨y.val, hy⟩ := Fin.ext hval.symm
      have hz₀ : F₀ ⟨x.val, hx⟩ ∈ Set.range F₀ := ⟨_, rfl⟩
      have hz₀' : F₀ ⟨x.val, hx⟩ ∈ Set.range F₀' := ⟨_, heq.symm⟩
      exact (Set.disjoint_left.1 hdisj₀ hz₀ hz₀').elim
    · have hval := congrArg Fin.val hxy
      simp only [joinHalfMaps, hx, hy, dite_true, dite_false] at hval
      have hlt := (F₀ ⟨x.val, hx⟩).isLt
      omega
  · by_cases hy : y.val < m
    · have hval := congrArg Fin.val hxy
      simp only [joinHalfMaps, hx, hy, dite_true, dite_false] at hval
      have hlt := (F₀' ⟨y.val, hy⟩).isLt
      omega
    · have hval := congrArg Fin.val hxy
      simp only [joinHalfMaps, hx, hy, dite_false] at hval
      have heq :
          F₁ ⟨x.val - m, by have := x.isLt; omega⟩ =
            F₁' ⟨y.val - m, by have := y.isLt; omega⟩ := by
        apply Fin.ext
        omega
      have hz₁ : F₁ ⟨x.val - m, by have := x.isLt; omega⟩ ∈ Set.range F₁ := ⟨_, rfl⟩
      have hz₁' : F₁ ⟨x.val - m, by have := x.isLt; omega⟩ ∈ Set.range F₁' :=
        ⟨_, heq.symm⟩
      exact (Set.disjoint_left.1 hdisj₁ hz₁ hz₁').elim

private lemma joinHalfMaps_cover {m : ℕ}
    {F₀ F₁ F₀' F₁' : Fin m → Fin (2 * m)}
    (hcover₀ : Set.range F₀ ∪ Set.range F₀' = Set.univ)
    (hcover₁ : Set.range F₁ ∪ Set.range F₁' = Set.univ) :
    Set.range (joinHalfMaps F₀ F₁) ∪ Set.range (joinHalfMaps F₀' F₁') = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hz : z.val < 2 * m
  · let z₀ : Fin (2 * m) := ⟨z.val, hz⟩
    have hzmem : z₀ ∈ Set.range F₀ ∪ Set.range F₀' := by rw [hcover₀]; exact Set.mem_univ _
    rcases hzmem with ⟨i, hi⟩ | ⟨i, hi⟩
    · left
      refine ⟨⟨i.val, by have := i.isLt; omega⟩, ?_⟩
      apply Fin.ext
      simp only [joinHalfMaps, i.isLt, dite_true]
      exact congrArg Fin.val hi
    · right
      refine ⟨⟨i.val, by have := i.isLt; omega⟩, ?_⟩
      apply Fin.ext
      simp only [joinHalfMaps, i.isLt, dite_true]
      exact congrArg Fin.val hi
  · let z₁ : Fin (2 * m) := ⟨z.val - 2 * m, by have := z.isLt; omega⟩
    have hzmem : z₁ ∈ Set.range F₁ ∪ Set.range F₁' := by rw [hcover₁]; exact Set.mem_univ _
    rcases hzmem with ⟨i, hi⟩ | ⟨i, hi⟩
    · left
      refine ⟨⟨m + i.val, by have := i.isLt; omega⟩, ?_⟩
      apply Fin.ext
      have hnot : ¬(m + i.val < m) := by omega
      simp only [joinHalfMaps, hnot, dite_false]
      have hi_fin :
          (⟨(m + i.val) - m, by have := i.isLt; omega⟩ : Fin m) = i := by
        apply Fin.ext
        simp
      rw [hi_fin]
      have hival := congrArg Fin.val hi
      dsimp [z₁] at hival
      omega
    · right
      refine ⟨⟨m + i.val, by have := i.isLt; omega⟩, ?_⟩
      apply Fin.ext
      have hnot : ¬(m + i.val < m) := by omega
      simp only [joinHalfMaps, hnot, dite_false]
      have hi_fin :
          (⟨(m + i.val) - m, by have := i.isLt; omega⟩ : Fin m) = i := by
        apply Fin.ext
        simp
      rw [hi_fin]
      have hival := congrArg Fin.val hi
      dsimp [z₁] at hival
      omega

/-- First paper recurrence: a matrix of size `2·4^n` has a BT-selected half
controlled by Eq. [2], while the complementary half is controlled by
`lambdaM (4^n)`.  Claim 2 combines the two with a factor `1 + O(l⁻²)`. -/
lemma lambdaM_two_pow4_claim2_recursion :
    ∃ K : ℝ, 48 ≤ K ∧
      ∀ (n l : ℕ), 2 ≤ l → l ≤ n →
        lambdaM (2 * 4 ^ n) ≤
          btClaimFactor l * max (btClaimThreshold K n l) (lambdaM (4 ^ n)) := by
  obtain ⟨K, hK48, hsmall⟩ := lambdaA_BT_small_side_uniform
  refine ⟨K, hK48, ?_⟩
  intro n l hl2 hln
  have hlR : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  have hl2pos : (0 : ℝ) < (l : ℝ) ^ 2 := by positivity
  have hl4pos : (0 : ℝ) < (l : ℝ) ^ 4 := by positivity
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK48
  have hMn : (0 : ℝ) ≤ lambdaM (4 ^ n) := lambdaM_nonneg_phase4 _
  have hMnl : (0 : ℝ) ≤ lambdaM (4 ^ (n - l)) := lambdaM_nonneg_phase4 _
  set small : ℝ :=
    K * lambdaM (4 ^ (n - l)) + K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l
    with hsmall_def
  set c₁ : ℝ := small + (l : ℝ) ^ 2 + 1 with hc₁_def
  set threshold : ℝ := 16 * (l : ℝ) ^ 4 * c₁ with hthreshold_def
  set c₂ : ℝ := max threshold (lambdaM (4 ^ n)) with hc₂_def
  have hsmall_nn : 0 ≤ small := by
    rw [hsmall_def]
    positivity
  have hc₁_pos : 0 < c₁ := by rw [hc₁_def]; positivity
  have hthreshold_pos : 0 < threshold := by rw [hthreshold_def]; positivity
  have hc₂_pos : 0 < c₂ := lt_of_lt_of_le hthreshold_pos (le_max_left _ _)
  have hc₂_ge_threshold : threshold ≤ c₂ := le_max_left _ _
  have hc₂_ge_M : lambdaM (4 ^ n) ≤ c₂ := le_max_right _ _
  have hratio_nn : 0 ≤ c₁ / c₂ := div_nonneg hc₁_pos.le hc₂_pos.le
  have hratio_upper : c₁ / c₂ ≤ 1 / (16 * (l : ℝ) ^ 4) := by
    rw [div_le_iff₀ hc₂_pos]
    have hrewrite : 1 / (16 * (l : ℝ) ^ 4) * c₂ =
        c₂ / (16 * (l : ℝ) ^ 4) := by ring
    rw [hrewrite, le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (l : ℝ) ^ 4)]
    rw [hthreshold_def] at hc₂_ge_threshold
    nlinarith
  have hquarter_upper : 1 / (16 * (l : ℝ) ^ 4) < (1 : ℝ) / 4 := by
    apply one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4)
    have hl_sq_ge : (4 : ℝ) ≤ (l : ℝ) ^ 2 := by nlinarith [sq_nonneg ((l : ℝ) - 2)]
    have hl_four_ge : (16 : ℝ) ≤ (l : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((l : ℝ) ^ 2 - 4)]
    nlinarith
  have hratio : c₁ / c₂ < (1 : ℝ) / 4 :=
    lt_of_le_of_lt hratio_upper hquarter_upper
  have hsqrt_le : Real.sqrt (c₁ / c₂) ≤ 1 / (l : ℝ) ^ 2 := by
    have hinv_sq_nn : 0 ≤ 1 / (l : ℝ) ^ 2 := by positivity
    have hratio_square : c₁ / c₂ ≤ (1 / (l : ℝ) ^ 2) ^ 2 := by
      calc
        c₁ / c₂ ≤ 1 / (16 * (l : ℝ) ^ 4) := hratio_upper
        _ ≤ (1 / (l : ℝ) ^ 2) ^ 2 := by
          rw [div_pow, one_pow]
          apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ((l : ℝ) ^ 2) ^ 2)
          nlinarith [hl4pos]
    nlinarith [Real.sq_sqrt hratio_nn]
  have hnorm_div : (1 : ℝ) / c₁ ≤ 1 / (l : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hc₁_pos hl2pos]
    rw [hc₁_def]
    nlinarith
  have hfactor_bound :
      1 + 4 * (Real.sqrt (c₁ / c₂) + 1 / c₁) ≤ btClaimFactor l := by
    calc
      1 + 4 * (Real.sqrt (c₁ / c₂) + 1 / c₁)
          ≤ 1 + 4 * (1 / (l : ℝ) ^ 2 + 1 / (l : ℝ) ^ 2) := by
            gcongr
      _ = btClaimFactor l := by rw [btClaimFactor]; ring
  have hRHS_nn : 0 ≤ btClaimFactor l * c₂ := by
    have hfac : 0 ≤ btClaimFactor l := by rw [btClaimFactor]; positivity
    positivity
  change sSup (lambdaA ''
    {A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ | ZeroDiag A ∧ ‖A‖ = 1}) ≤
      btClaimFactor l * max (btClaimThreshold K n l) (lambdaM (4 ^ n))
  set S := lambdaA ''
    {A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ | ZeroDiag A ∧ ‖A‖ = 1}
    with hS_def
  by_cases hSne : S.Nonempty
  · apply csSup_le hSne
    intro x hx
    obtain ⟨A, ⟨hzd, hnorm⟩, rfl⟩ := hx
    obtain ⟨H, H', hHinj, hH'inj, hdisj, hcover, hHsmall⟩ :=
      hsmall n l hl2 hln A hzd hnorm.le
    have hH'zd : ZeroDiag (A.submatrix H' H') := by
      intro i
      exact hzd (H' i)
    have hH'norm : ‖A.submatrix H' H'‖ ≤ 1 := by
      have hsub := submatrix_norm_le H' hH'inj A
      have hrw : Matrix.of (fun i j => A (H' i) (H' j)) = A.submatrix H' H' := by
        ext i j
        simp [Matrix.submatrix_apply, Matrix.of_apply]
      rw [hrw, hnorm] at hsub
      exact hsub
    have hH'lambda : lambdaA (A.submatrix H' H') ≤ lambdaM (4 ^ n) := by
      have hscale := Pow4Bootstrap.lambdaA_scale_bound (A.submatrix H' H') hH'zd
      have hmul : ‖A.submatrix H' H'‖ * lambdaM (4 ^ n) ≤ lambdaM (4 ^ n) := by
        nlinarith
      exact le_trans hscale hmul
    have hbnd₁ : lambdaA (A.submatrix H H) ≤ c₁ := by
      rw [hc₁_def]
      exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg hHsmall (sq_nonneg _)) zero_le_one
    have hbnd₂ : lambdaA (A.submatrix H' H') ≤ c₂ :=
      le_trans hH'lambda hc₂_ge_M
    have hclaim := lambdaA_two_block_decomp_asym_reindex (4 ^ n) A hzd hnorm H H'
      hHinj hH'inj hdisj hcover c₁ c₂ hc₁_pos hc₂_pos hratio hbnd₁ hbnd₂
    have hclaim' : lambdaA A ≤
        (1 + 4 * (Real.sqrt (c₁ / c₂) + 1 / c₁)) * c₂ := by
      simpa [hnorm] using hclaim
    have hc₂_nn : 0 ≤ c₂ := hc₂_pos.le
    have hcoef := mul_le_mul_of_nonneg_right hfactor_bound hc₂_nn
    have htoRHS : btClaimFactor l * c₂ =
        btClaimFactor l * max (btClaimThreshold K n l) (lambdaM (4 ^ n)) := by
      rw [hc₂_def, btClaimThreshold, hthreshold_def, hc₁_def, hsmall_def]
    rw [← htoRHS]
    exact le_trans hclaim' hcoef
  · rw [Set.not_nonempty_iff_eq_empty.mp hSne, Real.sSup_empty]
    simpa [hc₂_def] using hRHS_nn

set_option maxHeartbeats 800000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
/-- Apply the BT selected-half estimate separately in the two canonical
`2·4^n` halves of a `4·4^n` matrix, then join the two selected quarters.
The joined principal submatrix is a half of the original matrix and is still
controlled by the Eq. [2] scale.  This is the indexing step needed for the
second Claim 2 recurrence. -/
lemma lambdaA_pow4_good_half_uniform :
    ∃ K : ℝ, 48 ≤ K ∧
      ∀ (n l : ℕ), 2 ≤ l → l ≤ n →
      ∀ (A : Matrix (Fin (2 * (2 * 4 ^ n))) (Fin (2 * (2 * 4 ^ n))) ℂ),
        ZeroDiag A → ‖A‖ = 1 →
        ∃ (G G' : Fin (2 * 4 ^ n) → Fin (2 * (2 * 4 ^ n))),
          Function.Injective G ∧ Function.Injective G' ∧
          Disjoint (Set.range G) (Set.range G') ∧
          (Set.range G ∪ Set.range G') = Set.univ ∧
          lambdaA (A.submatrix G G) ≤
            K * lambdaM (4 ^ (n - l)) +
              K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
  classical
  obtain ⟨K₀, hK₀48, hsmall⟩ := lambdaA_BT_small_side_uniform
  set K : ℝ := 45 * (K₀ + 1) with hK_def
  have hK₀pos : (0 : ℝ) < K₀ := lt_of_lt_of_le (by norm_num) hK₀48
  have hK48 : (48 : ℝ) ≤ K := by rw [hK_def]; nlinarith
  refine ⟨K, hK48, ?_⟩
  intro n l hl2 hln A hzd hnorm
  let E₀ : Fin (2 * 4 ^ n) → Fin (2 * (2 * 4 ^ n)) := fun i =>
    ⟨i.val, by have := i.isLt; omega⟩
  let E₁ : Fin (2 * 4 ^ n) → Fin (2 * (2 * 4 ^ n)) := fun i =>
    ⟨2 * 4 ^ n + i.val, by have := i.isLt; omega⟩
  have hE₀inj : Function.Injective E₀ := by
    intro i j hij
    apply Fin.ext
    simpa [E₀] using congrArg Fin.val hij
  have hE₁inj : Function.Injective E₁ := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    simp only [E₁] at hval
    omega
  set A₀ := A.submatrix E₀ E₀ with hA₀_def
  set A₁ := A.submatrix E₁ E₁ with hA₁_def
  have hA₀zd : ZeroDiag A₀ := by
    intro i
    simp only [hA₀_def, Matrix.submatrix_apply]
    exact hzd (E₀ i)
  have hA₁zd : ZeroDiag A₁ := by
    intro i
    simp only [hA₁_def, Matrix.submatrix_apply]
    exact hzd (E₁ i)
  have hA₀norm : ‖A₀‖ ≤ 1 := by
    have hsub := submatrix_norm_le E₀ hE₀inj A
    have hrw : Matrix.of (fun i j => A (E₀ i) (E₀ j)) = A₀ := by
      ext i j
      simp [hA₀_def, Matrix.submatrix_apply, Matrix.of_apply]
    rw [hrw, hnorm] at hsub
    exact hsub
  have hA₁norm : ‖A₁‖ ≤ 1 := by
    have hsub := submatrix_norm_le E₁ hE₁inj A
    have hrw : Matrix.of (fun i j => A (E₁ i) (E₁ j)) = A₁ := by
      ext i j
      simp [hA₁_def, Matrix.submatrix_apply, Matrix.of_apply]
    rw [hrw, hnorm] at hsub
    exact hsub
  obtain ⟨H₀, H₀', hH₀inj, hH₀'inj, hdisj₀, hcover₀, hbnd₀⟩ :=
    hsmall n l hl2 hln A₀ hA₀zd hA₀norm
  obtain ⟨H₁, H₁', hH₁inj, hH₁'inj, hdisj₁, hcover₁, hbnd₁⟩ :=
    hsmall n l hl2 hln A₁ hA₁zd hA₁norm
  set G : Fin (2 * 4 ^ n) → Fin (2 * (2 * 4 ^ n)) :=
    joinHalfMaps H₀ H₁ with hG_def
  set G' : Fin (2 * 4 ^ n) → Fin (2 * (2 * 4 ^ n)) :=
    joinHalfMaps H₀' H₁' with hG'_def
  have hGinj : Function.Injective G := by
    rw [hG_def]
    exact joinHalfMaps_injective hH₀inj hH₁inj
  have hG'inj : Function.Injective G' := by
    rw [hG'_def]
    exact joinHalfMaps_injective hH₀'inj hH₁'inj
  have hGdisj : Disjoint (Set.range G) (Set.range G') := by
    rw [hG_def, hG'_def]
    exact joinHalfMaps_disjoint hdisj₀ hdisj₁
  have hGcover : Set.range G ∪ Set.range G' = Set.univ := by
    rw [hG_def, hG'_def]
    exact joinHalfMaps_cover hcover₀ hcover₁
  set AG := A.submatrix G G with hAG_def
  have hAGzd : ZeroDiag AG := by
    intro i
    simp only [hAG_def, Matrix.submatrix_apply]
    exact hzd (G i)
  have hAGnorm : ‖AG‖ ≤ 1 := by
    have hsub := submatrix_norm_le G hGinj A
    have hrw : Matrix.of (fun i j => A (G i) (G j)) = AG := by
      ext i j
      simp [hAG_def, Matrix.submatrix_apply, Matrix.of_apply]
    rw [hrw, hnorm] at hsub
    exact hsub
  set small : ℝ :=
    K₀ * lambdaM (4 ^ (n - l)) + K₀ * (l : ℝ) ^ 3 * (2 : ℝ) ^ l
    with hsmall_def
  set c₁ : ℝ := small + 1 with hc₁_def
  set c₂ : ℝ := 5 * c₁ with hc₂_def
  have hMnn : 0 ≤ lambdaM (4 ^ (n - l)) := lambdaM_nonneg_phase4 _
  have hsmall_nn : 0 ≤ small := by rw [hsmall_def]; positivity
  have hc₁pos : 0 < c₁ := by rw [hc₁_def]; linarith
  have hc₂pos : 0 < c₂ := by rw [hc₂_def]; positivity
  have hratio : c₁ / c₂ < (1 : ℝ) / 4 := by
    rw [hc₂_def]
    field_simp
    norm_num
  have hblock₀ :
      Matrix.of (fun i j : Fin (4 ^ n) =>
        AG ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) =
        A₀.submatrix H₀ H₀ := by
    ext i j
    simp [hAG_def, hG_def, joinHalfMaps, hA₀_def, E₀,
      Matrix.submatrix_apply, Matrix.of_apply]
  have hblock₁ :
      Matrix.of (fun i j : Fin (4 ^ n) =>
        AG ⟨4 ^ n + i.val, by omega⟩ ⟨4 ^ n + j.val, by omega⟩) =
        A₁.submatrix H₁ H₁ := by
    ext i j
    have hi : ¬(4 ^ n + i.val < 4 ^ n) := by omega
    have hj : ¬(4 ^ n + j.val < 4 ^ n) := by omega
    simp [hAG_def, hG_def, joinHalfMaps, hA₁_def, E₁,
      Matrix.submatrix_apply, Matrix.of_apply]
  have hbnd₀' : lambdaA
      (Matrix.of (fun i j : Fin (4 ^ n) =>
        AG ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)) ≤ c₁ := by
    rw [hblock₀, hc₁_def]
    linarith
  have hbnd₁' : lambdaA
      (Matrix.of (fun i j : Fin (4 ^ n) =>
        AG ⟨4 ^ n + i.val, by omega⟩ ⟨4 ^ n + j.val, by omega⟩)) ≤ c₂ := by
    rw [hblock₁, hc₂_def, hc₁_def]
    nlinarith
  have hclaim := Pow4Bootstrap.lambdaA_two_block_decomp_asym
    c₁ c₂ hc₁pos hc₂pos hratio AG hAGzd hAGnorm hbnd₀' hbnd₁'
  have hratio_eq : c₁ / c₂ = (1 : ℝ) / 5 := by
    rw [hc₂_def]
    field_simp
  have hsqrt_le : Real.sqrt (c₁ / c₂) ≤ 1 := by
    rw [hratio_eq]
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 5)
    nlinarith [Real.sqrt_nonneg (1 / 5)]
  have hnorm_div : ‖AG‖ / c₁ ≤ 1 := by
    rw [div_le_iff₀ hc₁pos, one_mul]
    calc
      ‖AG‖ ≤ 1 := hAGnorm
      _ ≤ c₁ := by rw [hc₁_def]; linarith
  have hcoef : 1 + 4 * (Real.sqrt (c₁ / c₂) + ‖AG‖ / c₁) ≤ 9 := by
    nlinarith
  have hc₂nn : 0 ≤ c₂ := hc₂pos.le
  have hAGbound : lambdaA AG ≤ 45 * c₁ := by
    calc
      lambdaA AG ≤
          (1 + 4 * (Real.sqrt (c₁ / c₂) + ‖AG‖ / c₁)) * c₂ := hclaim
      _ ≤ 9 * c₂ := mul_le_mul_of_nonneg_right hcoef hc₂nn
      _ = 45 * c₁ := by rw [hc₂_def]; ring
  have hlR : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
  have herr_one : (1 : ℝ) ≤ (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
    have hl_one : (1 : ℝ) ≤ (l : ℝ) := by linarith
    have hl3_one : (1 : ℝ) ≤ (l : ℝ) ^ 3 := one_le_pow₀ hl_one
    have h2_one : (1 : ℝ) ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
    nlinarith [mul_le_mul hl3_one h2_one (by norm_num) (by positivity)]
  refine ⟨G, G', hGinj, hG'inj, hGdisj, hGcover, ?_⟩
  change lambdaA AG ≤ _
  calc
    lambdaA AG ≤ 45 * c₁ := hAGbound
    _ ≤ K * lambdaM (4 ^ (n - l)) +
        K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
      rw [hc₁_def, hsmall_def, hK_def]
      nlinarith

set_option maxHeartbeats 800000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
/-- Second paper recurrence.  Two BT-selected quarters form a controlled half
of a `4^(n+1)` matrix; Claim 2 combines it with the complementary half, whose
scale is `lambdaM (2·4^n)`. -/
lemma lambdaM_pow4_succ_claim2_recursion :
    ∃ K : ℝ, 48 ≤ K ∧
      ∀ (n l : ℕ), 2 ≤ l → l ≤ n →
        lambdaM (4 ^ (n + 1)) ≤
          btClaimFactor l *
            max (btClaimThreshold K n l) (lambdaM (2 * 4 ^ n)) := by
  obtain ⟨K, hK48, hgood⟩ := lambdaA_pow4_good_half_uniform
  refine ⟨K, hK48, ?_⟩
  intro n l hl2 hln
  have hsize : 4 ^ (n + 1) = 2 * (2 * 4 ^ n) := by
    rw [pow_succ]
    ring
  rw [hsize]
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK48
  have hMnl : 0 ≤ lambdaM (4 ^ (n - l)) := lambdaM_nonneg_phase4 _
  have hMhalf : 0 ≤ lambdaM (2 * 4 ^ n) := lambdaM_nonneg_phase4 _
  set small : ℝ :=
    K * lambdaM (4 ^ (n - l)) + K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l
    with hsmall_def
  have hsmall_nn : 0 ≤ small := by rw [hsmall_def]; positivity
  have hfac_nn : 0 ≤ btClaimFactor l := by rw [btClaimFactor]; positivity
  have hthreshold_nn : 0 ≤ btClaimThreshold K n l := by
    rw [btClaimThreshold]
    positivity
  have hRHS_nn : 0 ≤ btClaimFactor l *
      max (btClaimThreshold K n l) (lambdaM (2 * 4 ^ n)) := by positivity
  change sSup (lambdaA ''
    {A : Matrix (Fin (2 * (2 * 4 ^ n))) (Fin (2 * (2 * 4 ^ n))) ℂ |
      ZeroDiag A ∧ ‖A‖ = 1}) ≤
      btClaimFactor l *
        max (btClaimThreshold K n l) (lambdaM (2 * 4 ^ n))
  set S := lambdaA ''
    {A : Matrix (Fin (2 * (2 * 4 ^ n))) (Fin (2 * (2 * 4 ^ n))) ℂ |
      ZeroDiag A ∧ ‖A‖ = 1} with hS_def
  by_cases hSne : S.Nonempty
  · apply csSup_le hSne
    intro x hx
    obtain ⟨A, ⟨hzd, hnorm⟩, rfl⟩ := hx
    obtain ⟨G, G', hGinj, hG'inj, hdisj, hcover, hGsmall⟩ :=
      hgood n l hl2 hln A hzd hnorm
    have hG'zd : ZeroDiag (A.submatrix G' G') := by
      intro i
      exact hzd (G' i)
    have hG'norm : ‖A.submatrix G' G'‖ ≤ 1 := by
      have hsub := submatrix_norm_le G' hG'inj A
      have hrw : Matrix.of (fun i j => A (G' i) (G' j)) =
          A.submatrix G' G' := by
        ext i j
        simp [Matrix.submatrix_apply, Matrix.of_apply]
      rw [hrw, hnorm] at hsub
      exact hsub
    have hG'lambda : lambdaA (A.submatrix G' G') ≤ lambdaM (2 * 4 ^ n) := by
      have hscale := Pow4Bootstrap.lambdaA_scale_bound (A.submatrix G' G') hG'zd
      have hmul : ‖A.submatrix G' G'‖ * lambdaM (2 * 4 ^ n) ≤
          lambdaM (2 * 4 ^ n) := by
        nlinarith
      exact le_trans hscale hmul
    have hclaim := claim2_threshold_lift hl2 A hzd hnorm G G'
      hGinj hG'inj hdisj hcover small (lambdaM (2 * 4 ^ n))
      hsmall_nn hMhalf (by simpa [small] using hGsmall) hG'lambda
    simpa [btClaimThreshold, hsmall_def] using hclaim
  · rw [Set.not_nonempty_iff_eq_empty.mp hSne, Real.sSup_empty]
    exact hRHS_nn

private lemma btClaimThreshold_mono {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂)
    (n l : ℕ) : btClaimThreshold K₁ n l ≤ btClaimThreshold K₂ n l := by
  have hM : 0 ≤ lambdaM (4 ^ (n - l)) := lambdaM_nonneg_phase4 _
  have herr : 0 ≤ (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by positivity
  have hKM := mul_le_mul_of_nonneg_right hK hM
  have hKE := mul_le_mul_of_nonneg_right hK herr
  rw [btClaimThreshold]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith

/-- The two Claim 2 lifts combined into the genuine one-step `4^n`
recurrence.  Its multiplicative loss is summable once `l` grows linearly
with `n`; unlike the former legacy statement, no full matrix is claimed to
satisfy the selected-half Eq. [2] bound. -/
theorem lambdaM_pow4_claim2_recursion :
    ∃ K : ℝ, 48 ≤ K ∧
      ∀ (n l : ℕ), 2 ≤ l → l ≤ n →
        lambdaM (4 ^ (n + 1)) ≤
          (btClaimFactor l) ^ 2 *
            max (btClaimThreshold K n l) (lambdaM (4 ^ n)) := by
  obtain ⟨K₁, hK₁48, hfirst⟩ := lambdaM_two_pow4_claim2_recursion
  obtain ⟨K₂, hK₂48, hsecond⟩ := lambdaM_pow4_succ_claim2_recursion
  set K : ℝ := max K₁ K₂ with hK_def
  have hK48 : (48 : ℝ) ≤ K := by
    rw [hK_def]
    exact le_trans hK₁48 (le_max_left _ _)
  refine ⟨K, hK48, ?_⟩
  intro n l hl2 hln
  set f : ℝ := btClaimFactor l with hf_def
  set T : ℝ := btClaimThreshold K n l with hT_def
  set Y : ℝ := lambdaM (4 ^ n) with hY_def
  set X : ℝ := lambdaM (2 * 4 ^ n) with hX_def
  have hK₁K : K₁ ≤ K := by rw [hK_def]; exact le_max_left _ _
  have hK₂K : K₂ ≤ K := by rw [hK_def]; exact le_max_right _ _
  have hT₁ : btClaimThreshold K₁ n l ≤ T := by
    rw [hT_def]
    exact btClaimThreshold_mono hK₁K n l
  have hT₂ : btClaimThreshold K₂ n l ≤ T := by
    rw [hT_def]
    exact btClaimThreshold_mono hK₂K n l
  have hf_one : (1 : ℝ) ≤ f := by
    rw [hf_def, btClaimFactor]
    have : 0 ≤ 8 / (l : ℝ) ^ 2 := by positivity
    linarith
  have hf_nn : 0 ≤ f := le_trans zero_le_one hf_one
  have hT_nn : 0 ≤ T := by
    rw [hT_def, btClaimThreshold]
    have hK_nn : 0 ≤ K := le_trans (by norm_num) hK48
    have hM_nn : 0 ≤ lambdaM (4 ^ (n - l)) := lambdaM_nonneg_phase4 _
    positivity
  have hY_nn : 0 ≤ Y := by rw [hY_def]; exact lambdaM_nonneg_phase4 _
  have hmax_nn : 0 ≤ max T Y := le_trans hT_nn (le_max_left _ _)
  have hXraw := hfirst n l hl2 hln
  have hX : X ≤ f * max T Y := by
    rw [hX_def, hf_def, hY_def]
    calc
      lambdaM (2 * 4 ^ n) ≤
          btClaimFactor l *
            max (btClaimThreshold K₁ n l) (lambdaM (4 ^ n)) := hXraw
      _ ≤ btClaimFactor l * max T (lambdaM (4 ^ n)) := by
        apply mul_le_mul_of_nonneg_left _ hf_nn
        exact max_le_max_right _ hT₁
      _ = btClaimFactor l * max T Y := by rw [hY_def]
  have hT_le : T ≤ f * max T Y := by
    calc
      T ≤ max T Y := le_max_left _ _
      _ ≤ f * max T Y := by nlinarith
  have hmax_TX : max T X ≤ f * max T Y := max_le hT_le hX
  have hZraw := hsecond n l hl2 hln
  calc
    lambdaM (4 ^ (n + 1)) ≤
        btClaimFactor l *
          max (btClaimThreshold K₂ n l) (lambdaM (2 * 4 ^ n)) := hZraw
    _ ≤ f * max T X := by
      rw [hf_def, hX_def]
      apply mul_le_mul_of_nonneg_left _ hf_nn
      exact max_le_max_right _ hT₂
    _ ≤ f * (f * max T Y) := mul_le_mul_of_nonneg_left hmax_TX hf_nn
    _ = (btClaimFactor l) ^ 2 *
        max (btClaimThreshold K n l) (lambdaM (4 ^ n)) := by
      rw [hf_def, hT_def, hY_def]
      ring

set_option maxHeartbeats 1200000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
/-- A direct consequence of the genuine Claim 2 recurrence: for every fixed
base `r > 1`, `lambdaM (4^n)` is `O(r^n)`.  We choose one sufficiently large
BT depth `l`.  The loss `(1+8/l²)^2` is then below `r`, while exponential
decay in the delayed term absorbs the fixed factor `16·l^4·K`. -/
theorem lambdaM_pow4_geometric_bound (r : ℝ) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, lambdaM (4 ^ n) ≤ C * r ^ n := by
  obtain ⟨K, hK48, hrec⟩ := lambdaM_pow4_claim2_recursion
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK48
  set s : ℝ := (r + 1) / 2 with hs_def
  have hs_one : (1 : ℝ) < s := by rw [hs_def]; linarith
  have hs_r : s < r := by rw [hs_def]; linarith
  have hrs_pos : 0 < r - s := by linarith
  have hc_pos : 0 < (1 : ℝ) / (16 * K) := by positivity
  have hpoly_event :=
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 4 hr).def hc_pos
  rw [Filter.eventually_atTop] at hpoly_event
  obtain ⟨Npoly, hNpoly⟩ := hpoly_event
  set B : ℝ := 80 / (s - 1) with hB_def
  have hs1_pos : (0 : ℝ) < s - 1 := by linarith
  have hB_pos : 0 < B := by rw [hB_def]; exact div_pos (by norm_num) hs1_pos
  have hcast_event : ∀ᶠ q : ℕ in Filter.atTop, B ≤ (q : ℝ) :=
    Filter.tendsto_atTop.1 tendsto_natCast_atTop_atTop B
  rw [Filter.eventually_atTop] at hcast_event
  obtain ⟨Ncast, hNcast⟩ := hcast_event
  set l : ℕ := max 2 (max Npoly Ncast) with hl_def
  have hl2 : 2 ≤ l := by rw [hl_def]; exact le_max_left _ _
  have hlNpoly : Npoly ≤ l := by
    rw [hl_def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hlNcast : Ncast ≤ l := by
    rw [hl_def]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hlR : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  have hB_l : B ≤ (l : ℝ) := hNcast l hlNcast
  have hpoly_l := hNpoly l hlNpoly
  have hl4_nn : 0 ≤ (l : ℝ) ^ 4 := by positivity
  have hrl_nn : 0 ≤ r ^ l := pow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, abs_of_nonneg hl4_nn,
    Real.norm_eq_abs, abs_of_nonneg hrl_nn] at hpoly_l
  have hcoeff : 16 * (l : ℝ) ^ 4 * K ≤ r ^ l := by
    calc
      16 * (l : ℝ) ^ 4 * K = (16 * K) * (l : ℝ) ^ 4 := by ring
      _ ≤ (16 * K) * ((1 / (16 * K)) * r ^ l) :=
        mul_le_mul_of_nonneg_left hpoly_l (by positivity)
      _ = r ^ l := by field_simp
  have h80div : 80 / (l : ℝ) ≤ s - 1 := by
    have hBlower : 80 / (s - 1) ≤ (l : ℝ) := by simpa [B, hB_def] using hB_l
    rw [div_le_iff₀ hlpos]
    rw [div_le_iff₀ hs1_pos] at hBlower
    nlinarith
  have hfactor_aux : (1 + 8 / (l : ℝ) ^ 2) ^ 2 ≤
      1 + 80 / (l : ℝ) := by
    have hlone : (1 : ℝ) ≤ (l : ℝ) := by linarith
    field_simp
    nlinarith [sq_nonneg ((l : ℝ) - 1),
      mul_nonneg (sq_nonneg (l : ℝ)) (by linarith : 0 ≤ (l : ℝ) - 1)]
  have hfactor : (btClaimFactor l) ^ 2 ≤ s := by
    rw [btClaimFactor]
    linarith
  set b : ℝ := 16 * (l : ℝ) ^ 4 *
    (K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l + (l : ℝ) ^ 2 + 1) with hb_def
  have hb_nn : 0 ≤ b := by rw [hb_def]; positivity
  set Cbase : ℝ := ((4 : ℝ) ^ l) ^ 2 with hCbase_def
  have hCbase_pos : 0 < Cbase := by rw [hCbase_def]; positivity
  set C : ℝ := Cbase + s * b / (r - s) + 1 with hC_def
  have hsb_nn : 0 ≤ s * b :=
    mul_nonneg (le_of_lt (lt_trans zero_lt_one hs_one)) hb_nn
  have hC_pos : 0 < C := by rw [hC_def]; positivity
  have hCbase_le : Cbase ≤ C := by
    rw [hC_def]
    have : 0 ≤ s * b / (r - s) := div_nonneg hsb_nn hrs_pos.le
    linarith
  have hsb_absorb : s * b ≤ (r - s) * C := by
    have hdiv_le : s * b / (r - s) ≤ C := by
      rw [hC_def]
      nlinarith [hCbase_pos]
    rw [div_le_iff₀ hrs_pos] at hdiv_le
    simpa [mul_comm] using hdiv_le
  refine ⟨C, hC_pos, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnl : n ≤ l
      · have hpoly := Pow4Bootstrap.lambdaM_le_poly (4 ^ n)
        have h4n_nn : 0 ≤ ((4 ^ n : ℕ) : ℝ) := Nat.cast_nonneg _
        have hpow_nl : (4 : ℝ) ^ n ≤ (4 : ℝ) ^ l :=
          pow_le_pow_right₀ (by norm_num) hnl
        have hrn_one : (1 : ℝ) ≤ r ^ n := one_le_pow₀ hr.le
        calc
          lambdaM (4 ^ n) ≤
              ((4 ^ n : ℕ) : ℝ) * (((4 ^ n : ℕ) : ℝ) - 1) := hpoly
          _ ≤ (((4 ^ n : ℕ) : ℝ)) ^ 2 := by nlinarith
          _ = ((4 : ℝ) ^ n) ^ 2 := by norm_cast
          _ ≤ ((4 : ℝ) ^ l) ^ 2 := by gcongr
          _ = Cbase := hCbase_def.symm
          _ ≤ C := hCbase_le
          _ ≤ C * r ^ n := by nlinarith
      · push Not at hnl
        cases n with
        | zero => omega
        | succ m =>
            have hlm : l ≤ m := by omega
            have hm_lt : m < m + 1 := Nat.lt_succ_self m
            have hml_lt : m - l < m + 1 := by omega
            have hYm : lambdaM (4 ^ m) ≤ C * r ^ m := ih m hm_lt
            have hYml : lambdaM (4 ^ (m - l)) ≤ C * r ^ (m - l) :=
              ih (m - l) hml_lt
            have hT : btClaimThreshold K m l ≤ C * r ^ m + b := by
              rw [btClaimThreshold, hb_def]
              have hK_nn : 0 ≤ K := hKpos.le
              have hscale_nn : 0 ≤ 16 * (l : ℝ) ^ 4 := by positivity
              calc
                16 * (l : ℝ) ^ 4 *
                    (K * lambdaM (4 ^ (m - l)) +
                      K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l + (l : ℝ) ^ 2 + 1)
                    = (16 * (l : ℝ) ^ 4 * K) * lambdaM (4 ^ (m - l)) +
                      16 * (l : ℝ) ^ 4 *
                        (K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l + (l : ℝ) ^ 2 + 1) := by ring
                _ ≤ (16 * (l : ℝ) ^ 4 * K) * (C * r ^ (m - l)) + b := by
                  gcongr
                _ ≤ r ^ l * (C * r ^ (m - l)) + b := by
                  gcongr
                _ = C * r ^ m + b := by
                  rw [show r ^ l * (C * r ^ (m - l)) =
                      C * (r ^ (m - l) * r ^ l) by ring,
                    ← pow_add, Nat.sub_add_cancel hlm]
            have hYm_b : lambdaM (4 ^ m) ≤ C * r ^ m + b :=
              le_trans hYm (le_add_of_nonneg_right hb_nn)
            have hmax : max (btClaimThreshold K m l) (lambdaM (4 ^ m)) ≤
                C * r ^ m + b := max_le hT hYm_b
            have hsum_nn : 0 ≤ C * r ^ m + b := by positivity
            have hrm_one : (1 : ℝ) ≤ r ^ m := one_le_pow₀ hr.le
            have hfinal : s * (C * r ^ m + b) ≤ C * r ^ (m + 1) := by
              rw [pow_succ]
              have hC_nn : 0 ≤ C := hC_pos.le
              nlinarith [hsb_absorb,
                mul_le_mul_of_nonneg_left hrm_one
                  (mul_nonneg (sub_nonneg.mpr hs_r.le) hC_nn)]
            calc
              lambdaM (4 ^ (m + 1)) ≤
                  (btClaimFactor l) ^ 2 *
                    max (btClaimThreshold K m l) (lambdaM (4 ^ m)) :=
                hrec m l hl2 hlm
              _ ≤ (btClaimFactor l) ^ 2 * (C * r ^ m + b) :=
                mul_le_mul_of_nonneg_left hmax (sq_nonneg _)
              _ ≤ s * (C * r ^ m + b) :=
                mul_le_mul_of_nonneg_right hfactor hsum_nn
              _ ≤ C * r ^ (m + 1) := hfinal

/-! The former over-strong full-matrix Eq. [2] statement is retained below
only as historical design commentary.  It is mathematically replaced by the
two genuine Claim 2 recurrences and `lambdaM_pow4_claim2_recursion` above. -/
/-
/-- **Per-`A` BT-iterated bound** at size `2 · 4^n`, with a *globally uniform*
constant `K_full` (independent of `n`, `l`, `A`).

The constant is derived from the global uniform constants `K_BT_global` and
`C_two_global` extracted from `bourgain_tzafriri_iterated` and
`lambdaA_two_block_decomp` (both yield single constants independent of
`n, l`, baked into the existentials at the top of the file).

**Historical proof plan (Phase 3-5 assembly, not the current proof status):**
1. Obtain `K_BT, H, e` from `bt_paving_depth_l_construction` (Phase 3).
2. Obtain `H'` from `bt_paving_depth_l_complement` (Phase 3 complement).
3. Apply `lambdaA_four_block_iterated_He` (Phase 4) on the H side:
   `lambdaA(A.submatrix H H) ≤ K_iter · lambdaM(4^(n-l)) + K_iter · l^3 · 2^l`.
4. Apply `Pow4Bootstrap.lambdaA_two_block_decomp` (Phase 5) at δ = 1/l:
   `lambdaA A ≤ 2/(1-1/l) · (lambdaA(H side) + lambdaA(H' side)) + C_two · l`.
5. **Algebraic absorption of H' side** (a placeholder in the early draft): bound
   `lambdaA(A.submatrix H' H')` by a `K · lambdaM(4^(n-l)) + K · l^3 · 2^l`
   expression, either by re-applying BT-paving on the H' coordinates
   (re-deriving a σ-paving for the H' side) or by the JOS-paper-style
   self-recursive argument absorbing `lambdaM(4^n)` into the recursion. -/
/- Historical development log (statuses below refer only to that earlier draft).
State: 🔄 partial
Priority: 1
Attempts: 0 / 50
tmp file:
Plan (see BLUEPRINT.md §"Phase 5 per-A decomposition", 2026-05-17):
The sum-form `lambdaA_two_block_decomp` (coeff 2/(1-δ) > 1) is provably
insufficient — it gives a non-closing fixed-point inequality. Correct route is
the paper's Claim 2 max-form via an *asymmetric* η-trick + induction on n.
Split into 7 sub-lemmas (P5-G/D/A/B/C/E done; F pending):
  P5-G lambdaM_le_poly: λM finiteness (DONE, in Pow4Bootstrap.lean).
  P5-A asym_eta_trick_arith: asymmetric η-trick real arithmetic (DONE).
  P5-C lambdaA_BT_small_side: Phase-4 H-side bound, packaged (DONE).
  P5-D lambdaM_one_eq_zero: base-case helper (DONE).
  P5-B lambdaA_two_block_decomp_asym: asymmetric max-form two-block (DONE,
    in Pow4Bootstrap.lean), plus arbitrary-partition reindexing (DONE here).
  P5-E convergent_eta_product_bound: telescoped ∏(1+Ks⁻²) ≤ const (DONE).
  P5-F this lemma: BLOCKED ON STATEMENT REFACTOR. Paper Eq. [2] bounds the
    selected half `A'`, whereas this lemma asserts the Eq. [2] bound for the
    entire `2·4^n` matrix. Claim 2 does not preserve that RHS; it introduces
    the paper's `max{K(log m)^7 m^(1/4), λ(A'')}` recurrence instead.
See the 2026-08-05 audit in BLUEPRINT.md before attempting P5-F. -/
private lemma lambdaA_pow4_BT_iterated_per_A :
    ∃ K_full : ℝ, 0 < K_full ∧
      ∀ (n l : ℕ) (_hl1 : 2 ≤ l) (_hl : l ≤ n)
        (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ),
        ZeroDiag A → ‖A‖ = 1 →
        lambdaA A ≤
          K_full * lambdaM (4 ^ (n - l)) + K_full * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
  -- Extract global uniform constants from the BT axiom and the two-block decomp.
  obtain ⟨K_BT, hK_BT_pos, _hBT_spec⟩ := bourgain_tzafriri_iterated
  obtain ⟨C_two, hC_two_pos, _h_two_block⟩ := Pow4Bootstrap.lambdaA_two_block_decomp
  -- The K_iter from Phase 4 depends on K_BT (it is `max (8·K_BT) 48`).
  set K_iter : ℝ := max (8 * K_BT) 48 with hK_iter_def
  have hK_iter_pos : 0 < K_iter := by
    rw [hK_iter_def]; positivity
  -- Final constant absorbs both Phase 4 and Phase 5 factors.
  -- Concretely: `2/(1-1/l) ≤ 4` for l ≥ 2, so the leading factor on the
  -- H-side bound is ≤ 8·K_iter.  The H'-side, after the Phase 5
  -- absorption argument, contributes a comparable factor.  The error
  -- term from `C_two/δ = C_two · l` is dominated by `C_two · l^3 · 2^l`.
  set K_full : ℝ := max (16 * K_iter) (16 * C_two) with hK_full_def
  have hK_full_pos : 0 < K_full := by
    rw [hK_full_def]
    have h1 : 0 < 16 * K_iter := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  refine ⟨K_full, hK_full_pos, ?_⟩
  intro n l _hl1 _hl A _hzd _hnorm
  -- The Phase 5 algebraic assembly: combines Phase 4 on H, scale_bound on H',
  -- the two-block decomp, and the absorption of the residual `lambdaM(4^n)`
  -- term back into the recursion via `lambdaM(4^n) ≤ lambdaM(2·4^n)`.
  -- This is the genuine mathematical gap left for a future session.
  --
  -- Concrete plan (per the prompt):
  --   * Obtain H, e from `bt_paving_depth_l_construction n l _hl` applied to A.
  --   * Obtain H' from `bt_paving_depth_l_complement`.
  --   * Apply `lambdaA_four_block_iterated_He` on H.
  --   * Apply `lambdaA_two_block_decomp n (1/l) ... A _hzd _hnorm H H' ...`.
  --   * Bound `lambdaA(A.submatrix H' H') ≤ ‖A.submatrix H' H'‖ · lambdaM(4^n)`
  --     by `Pow4Bootstrap.lambdaA_scale_bound`.
  --   * Either: (a) apply BT-paving + Phase 4 again on H' coordinates (most
  --     likely route to constant K), or (b) absorb `lambdaM(4^n)` into the
  --     recursion via a fixed-point/self-recursion argument.
  --
  -- The sub-step (a)/(b) is the residual mathematical work (~150-250 LOC
  -- of Phase 4-style iteration on H' plus algebraic bookkeeping).
  -- Historical proof hole; this entire legacy declaration is inside a block comment.

/-! ## Main theorem (legacy target awaiting the Phase-5 recurrence refactor) -/

/-- **JOS 2013 paper Eq. [2] + Claim 2 lift, supremum-level form with ε = 1/l.**

For every `n` and `2 ≤ l ≤ n`,
```
λ(4ⁿ) ≤ K · λ(4ⁿ⁻ˡ) + K · l³ · 2ˡ
```
for some absolute constant `K`.

This is **paper Eq. [2] (p. 19254)** specialised to `ε = 1/l` and combined with
the **Claim 2** (p. 19252–19253) two-block lift, both then taken to the
supremum level.

## Proof outline (current state)

The proof requires reconciling a fundamental algebraic gap.  Plugging
`ε = 1/l` into the supremum-level iterate of `lambdaM_four_block_recursion`
(via `Pow4Bootstrap.lambdaM_iterate_pow4`) yields:

```
lambdaM(4ⁿ) ≤ (2/(1-1/l))ˡ · lambdaM(4ⁿ⁻ˡ) + (∑_{i<l} (2/(1-1/l))ⁱ) · (6l).
```

By Phase 1 lemmas:
* `(2/(1-1/l))ˡ = 2ˡ · (1/(1-1/l))ˡ ≤ 2ˡ · 8 = 8 · 2ˡ`;
* `∑_{i<l} (2/(1-1/l))ⁱ ≤ 4ˡ` (Pow4Bootstrap.geom_sum_bound).

This gives the *intermediate bound*:
```
lambdaM(4ⁿ) ≤ 8 · 2ˡ · lambdaM(4ⁿ⁻ˡ) + 6 · l · 4ˡ.    (★)
```

The target requires a **constant** factor on the recursive `lambdaM(4ⁿ⁻ˡ)`
term and `O(l³ · 2ˡ)` (not `l · 4ˡ`) error.  The discrepancy between (★)
and the target is the **BT-cancellation gap**: it requires applying Claim 1
(iterated four-block) *inside* the BT σ-paving (`lambdaA_BT_paving_descent`
gives the per-leaf `(1/2)ˡ` factor) so that `(2/(1-1/l))ˡ · (1/2)ˡ` cancels
to a constant via `one_inv_eps_pow_l_le_eight`, **at the lambdaA level**, *before*
taking the supremum.  The clean form is:

```
lambdaA A ≤ 8·K_BT · lambdaM(4ⁿ⁻ˡ) + O(l³ · 2ˡ)
```

obtained by:
1. (Phase 3) Build `H, H' : Fin (4ⁿ) → Fin (2·4ⁿ)` from the σ-paving (σ-leaves
   union covers `4ˡ · 4ⁿ⁻ˡ = 4ⁿ` indices; H' is the complement).
2. (Phase 4) Iterate `lambdaA_four_block_bound_strong` `l` times on
   `A.submatrix H H` with `δ = 1/l`, producing `(2/(1-1/l))ˡ · sup_leaf
   lambdaA(leaf) + (∑ (2/(1-1/l))ⁱ) · l`.  The sup of leaves combined with
   `lambdaA_BT_paving_descent` yields the desired constant factor.
3. (Phase 5) Apply `lambdaA_two_block_decomp` with `δ = 1/l` to lift
   `lambdaA(A.submatrix H H)` back to `lambdaA A`, picking up an
   `O(l)` error from `C_two/δ` and an `lambdaA(A.submatrix H' H')`
   term that absorbs into the recursive `lambdaM(4ⁿ-l)` slot via
   `lambdaA_scale_bound`.

This Phase 3-5 program (~700-1000 LOC) is left for a future session.

**Phase 3 status (Session 13):** the H/H' construction is implemented as
private helpers above: `bt_paving_depth_l_construction` packages the
σ-paving into `H : Fin(4^n) → Fin(2·4^n)` + canonical leaf embedding
`e : Fin(4^l) → Fin(4^(n-l)) → Fin(4^n)`;
`bt_paving_depth_l_complement` builds the complement `H'` via
`Pow4Bootstrap.buildComplement_S1i`; `lambdaA_BT_paving_descent_via_He`
combines them with `lambdaA_scale_bound` to give the per-leaf
`lambdaA ≤ K_BT·(1/2)^l · lambdaM(4^(n-l))` bound in H/e-packaged form,
ready to be fed to Phase 4 (iterated `lambdaA_four_block_bound_strong`).

There is also a *target-size mismatch*: `bourgain_tzafriri_iterated` and
`lambdaA_two_block_decomp` are stated at size `2·4ⁿ`, while our target
supremum is `lambdaM(4ⁿ)` — Phase 3 must therefore work either via embedding
`Fin(4ⁿ) ↪ Fin(2·4ⁿ)` (using a padded-with-zero matrix) or by re-deriving
a `Fin(4ⁿ)`-version of `bourgain_tzafriri_iterated` from
`bourgain_tzafriri_central_submatrix`. -/
theorem lambdaM_pow4_BT_iterated_recursion :
    ∃ K : ℝ, 0 < K ∧
    ∀ (n l : ℕ) (_hl1 : 2 ≤ l) (_hl : l ≤ n),
      lambdaM (4 ^ n) ≤ K * lambdaM (4 ^ (n - l)) + K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
  -- Extract the uniform constant from `lambdaA_pow4_BT_iterated_per_A`.
  obtain ⟨K, hK_pos, hper_A⟩ := lambdaA_pow4_BT_iterated_per_A
  refine ⟨K, hK_pos, ?_⟩
  intro n l hl1 hl
  -- Step 1: bound `lambdaM(2·4^n)` via the supremum of the per-A bound.
  have hStep1 : lambdaM (2 * 4 ^ n) ≤
      K * lambdaM (4 ^ (n - l)) + K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
    have hlM_def : lambdaM (2 * 4 ^ n) =
        sSup (lambdaA ''
          {A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ |
            ZeroDiag A ∧ ‖A‖ = 1}) := rfl
    rw [hlM_def]
    have hRHS_nn : (0 : ℝ) ≤
        K * lambdaM (4 ^ (n - l)) + K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
      have hlM_nn : (0 : ℝ) ≤ lambdaM (4 ^ (n - l)) := lambdaM_nonneg_phase4 _
      have h1 : (0 : ℝ) ≤ K * lambdaM (4 ^ (n - l)) :=
        mul_nonneg hK_pos.le hlM_nn
      have h2 : (0 : ℝ) ≤ K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by positivity
      linarith
    by_cases hne :
        (lambdaA '' {A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ |
          ZeroDiag A ∧ ‖A‖ = 1}).Nonempty
    · apply csSup_le hne
      rintro x ⟨A, ⟨hzd, hnorm⟩, rfl⟩
      exact hper_A n l hl1 hl A hzd hnorm
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
      exact hRHS_nn
  -- Step 2: bridge from `lambdaM(4^n)` to `lambdaM(2·4^n)` via monotonicity.
  exact le_trans (lambdaM_le_lambdaM_double_phase4 n) hStep1
-/

end CommutatorTheorem
