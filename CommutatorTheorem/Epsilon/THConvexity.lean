import CommutatorTheorem.Defs
import CommutatorTheorem.Epsilon.Rosenblum
import CommutatorTheorem.Epsilon.Paving
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open Complex Finset

namespace CommutatorTheorem.THConvexity

-- For any x with ‖x‖ < 1 and nonzero k in kernel of L, ∃ y on unit sphere with L(y) = L(x).
set_option maxHeartbeats 800000 in
lemma exists_unit_preimage_of_kernel {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : E →ₗ[ℝ] F)
    (hker : ∃ k : E, k ≠ 0 ∧ L k = 0)
    (x : E) (hx : ‖x‖ < 1) :
    ∃ y : E, ‖y‖ = 1 ∧ L y = L x := by
  obtain ⟨k, hk_ne, hk_ker⟩ := hker
  have hk_norm_pos : (0 : ℝ) < ‖k‖ := norm_pos_iff.mpr hk_ne
  have hk_sq_pos : (0 : ℝ) < ‖k‖ ^ 2 := by positivity
  have hx_sq_lt : ‖x‖ ^ 2 < 1 := by
    have := sq_lt_sq' (by linarith [norm_nonneg x]) hx; linarith
  set a := ‖k‖ ^ 2
  set b := 2 * @inner ℝ E _ x k
  set c := ‖x‖ ^ 2 - 1
  have ha_pos : 0 < a := hk_sq_pos
  have hc_neg : c < 0 := by linarith
  have hdisc : 0 < b ^ 2 - 4 * a * c := by
    nlinarith [sq_nonneg (@inner ℝ E _ x k)]
  set D := b ^ 2 - 4 * a * c
  set t₀ := (-b + Real.sqrt D) / (2 * a)
  have hroot : a * t₀ ^ 2 + b * t₀ + c = 0 := by
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt (le_of_lt hdisc)
    have key : (2 * a) ^ 2 * (a * t₀ ^ 2 + b * t₀ + c) = 0 := by
      have ht₀ : t₀ * (2 * a) = -b + Real.sqrt D := by
        simp only [t₀]; field_simp
      have h1 : (t₀ * (2 * a)) ^ 2 = (-b + Real.sqrt D) ^ 2 := by rw [ht₀]
      have h3 : (2 * a) ^ 2 * (a * t₀ ^ 2 + b * t₀ + c) =
        a * (t₀ * (2 * a)) ^ 2 + b * (t₀ * (2 * a)) * (2 * a) + c * (2 * a) ^ 2 := by ring
      rw [h3, ht₀]; nlinarith [hsq]
    exact (mul_eq_zero.mp key).resolve_left (by positivity)
  refine ⟨x + t₀ • k, ?_, ?_⟩
  · rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs]
    rw [show (|t₀| * ‖k‖) ^ 2 = t₀ ^ 2 * ‖k‖ ^ 2 by rw [mul_pow, sq_abs]]
    linarith [hroot]
  · rw [map_add, map_smul, hk_ker, smul_zero, add_zero]

-- Vector construction from S² coords, Y₀ > -1
set_option maxHeartbeats 6400000 in
private lemma construct_vector_from_sphere (M : Matrix (Fin 2) (Fin 2) ℂ)
    (Y₀ Y₁ Y₂ : ℝ)
    (hy_sq : Y₀ ^ 2 + Y₁ ^ 2 + Y₂ ^ 2 = 1)
    (hY0_gt : -1 < Y₀) :
    ∃ v : Fin 2 → ℂ,
      (∑ i, ∑ j, (starRingEnd ℂ) (v i) * M i j * v j =
        (M 0 0 + M 1 1) / 2 +
        ((M 0 0 - M 1 1) / 2 * ↑Y₀ + (M 0 1 + M 1 0) / 2 * ↑Y₁ +
         Complex.I * ((M 0 1 - M 1 0) / 2) * ↑Y₂)) ∧
      (∑ i, Complex.normSq (v i) = 1) := by
  have hα_arg_pos : 0 < (1 + Y₀) / 2 := by linarith
  set α := Real.sqrt ((1 + Y₀) / 2)
  have hα_pos : 0 < α := Real.sqrt_pos.mpr hα_arg_pos
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have hα_sq : α * α = (1 + Y₀) / 2 := by
    have := Real.sq_sqrt (le_of_lt hα_arg_pos); linarith [sq (α)]
  have h_Y_sum : Y₁ ^ 2 + Y₂ ^ 2 = 1 - Y₀ ^ 2 := by linarith
  set v₁ : ℂ := (↑Y₁ + Complex.I * ↑Y₂) / (2 * ↑α)
  have hv1_normSq : Complex.normSq v₁ = (1 - Y₀) / 2 := by
    rw [show v₁ = (↑Y₁ + Complex.I * ↑Y₂) / (2 * ↑α) from rfl, Complex.normSq_div]
    have hnum : Complex.normSq (↑Y₁ + Complex.I * ↑Y₂ : ℂ) = Y₁ ^ 2 + Y₂ ^ 2 := by
      simp [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_I,
        Complex.normSq_ofReal]; ring
    have hden : Complex.normSq (2 * (↑α : ℂ)) = 4 * (α * α) := by
      rw [show (2 : ℂ) * ↑α = ↑(2 * α) from by push_cast; ring,
        Complex.normSq_ofReal]; ring
    rw [hnum, hden, h_Y_sum, hα_sq]
    have : (1 : ℝ) + Y₀ ≠ 0 := by linarith
    field_simp; ring
  have h_conj_v1 : starRingEnd ℂ v₁ = (↑Y₁ - Complex.I * ↑Y₂) / (2 * ↑α) := by
    rw [show v₁ = (↑Y₁ + Complex.I * ↑Y₂) / (2 * ↑α) from rfl]
    have hstar2 : starRingEnd ℂ (2 : ℂ) = 2 := by
      rw [show (2 : ℂ) = ↑(2 : ℝ) from by norm_cast]; exact Complex.conj_ofReal 2
    rw [map_div₀, map_mul, hstar2, Complex.conj_ofReal,
      map_add, Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  have hα_c_ne : (↑α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα_ne
  have h_mul_v1 : (↑α : ℂ) * v₁ = (↑Y₁ + Complex.I * ↑Y₂) / 2 := by
    rw [show v₁ = (↑Y₁ + Complex.I * ↑Y₂) / (2 * ↑α) from rfl]; field_simp
  have h_mul_cv1 : (↑α : ℂ) * starRingEnd ℂ v₁ = (↑Y₁ - Complex.I * ↑Y₂) / 2 := by
    rw [h_conj_v1]; field_simp
  have h_cv1_v1 : starRingEnd ℂ v₁ * v₁ = ↑(Complex.normSq v₁) := by
    rw [show starRingEnd ℂ v₁ * v₁ = v₁ * starRingEnd ℂ v₁ from by ring]
    exact Complex.mul_conj v₁
  set v : Fin 2 → ℂ := ![↑α, v₁]
  refine ⟨v, ?_, ?_⟩
  · simp only [v, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const]
    rw [Complex.conj_ofReal]
    have t1 : (↑α : ℂ) * M 0 0 * ↑α = ↑((1 + Y₀) / 2) * M 0 0 := by
      rw [show (↑α : ℂ) * M 0 0 * ↑α = ↑(α * α) * M 0 0 from by push_cast; ring, hα_sq]
    have t2 : (↑α : ℂ) * M 0 1 * v₁ = (↑Y₁ + Complex.I * ↑Y₂) / 2 * M 0 1 := by
      rw [show (↑α : ℂ) * M 0 1 * v₁ = (↑α * v₁) * M 0 1 from by ring, h_mul_v1]
    have t3 : starRingEnd ℂ v₁ * M 1 0 * ↑α =
        (↑Y₁ - Complex.I * ↑Y₂) / 2 * M 1 0 := by
      rw [show starRingEnd ℂ v₁ * M 1 0 * ↑α = (↑α * starRingEnd ℂ v₁) * M 1 0 from by ring,
        h_mul_cv1]
    have t4 : starRingEnd ℂ v₁ * M 1 1 * v₁ = ↑((1 - Y₀) / 2) * M 1 1 := by
      rw [show starRingEnd ℂ v₁ * M 1 1 * v₁ = (starRingEnd ℂ v₁ * v₁) * M 1 1 from by ring,
        h_cv1_v1, hv1_normSq]
    rw [t1, t2, t3, t4]; push_cast; ring
  · simp only [v, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const]
    rw [Complex.normSq_ofReal, hv1_normSq, show α * α = (1 + Y₀) / 2 from hα_sq]; ring

-- Helper to simplify WithLp access
private lemma withLp_symm_ofLp_eq {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    ((WithLp.equiv 2 (Fin n → ℝ)).symm x).ofLp i = x i := rfl

-- [M₀₀, M₁₁] ⊆ NR(M) for any 2×2 matrix M
set_option maxHeartbeats 3200000 in
theorem segment_diag_in_nr_2x2
    (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ v : Fin 2 → ℂ,
      (∑ i, ∑ j, starRingEnd ℂ (v i) * M i j * v j =
        ↑t * M 0 0 + ↑(1 - t) * M 1 1) ∧
      (∑ i, Complex.normSq (v i) = 1) := by
  by_cases ht_end : t = 0 ∨ t = 1
  · rcases ht_end with rfl | rfl
    · refine ⟨![0, 1], ?_, ?_⟩
      · simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Complex.normSq_zero, Complex.normSq_one]
    · refine ⟨![1, 0], ?_, ?_⟩
      · simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Complex.normSq_zero, Complex.normSq_one]
  · push_neg at ht_end
    have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_end.1)
    have ht_lt1 : t < 1 := lt_of_le_of_ne ht1 ht_end.2
    set p := (M 0 0 - M 1 1) / 2
    set b := M 0 1
    set c := M 1 0
    let L₀ : (Fin 3 → ℝ) →ₗ[ℝ] ℂ :=
      { toFun := fun x => p * ↑(x 0) + ((b + c) / 2) * ↑(x 1) +
          Complex.I * ((b - c) / 2) * ↑(x 2)
        map_add' := by intro x y; simp only [Pi.add_apply, Complex.ofReal_add]; ring
        map_smul' := by
          intro r x
          change p * ↑(r * x 0) + ((b + c) / 2) * ↑(r * x 1) +
            Complex.I * ((b - c) / 2) * ↑(r * x 2) =
            (RingHom.id ℝ) r • (p * ↑(x 0) + ((b + c) / 2) * ↑(x 1) +
              Complex.I * ((b - c) / 2) * ↑(x 2))
          simp only [RingHom.id_apply, Complex.ofReal_mul, real_smul]; ring }
    let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℂ :=
      L₀.comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
    have hker : ∃ k : EuclideanSpace ℝ (Fin 3), k ≠ 0 ∧ L k = 0 := by
      have : L.ker ≠ ⊥ := by
        apply LinearMap.ker_ne_bot_of_finrank_lt
        simp [Complex.finrank_real_complex, Fintype.card_fin]
      exact Submodule.exists_mem_ne_zero_of_ne_bot this |>.imp
        fun k hk => ⟨hk.2, LinearMap.mem_ker.mp hk.1⟩
    set x₀ : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm ![2*t-1, 0, 0]
    have hx₀_norm : ‖x₀‖ < 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm,
        ← Real.sqrt_sq (norm_nonneg _)]
      apply Real.sqrt_lt_sqrt (sq_nonneg _)
      rw [EuclideanSpace.norm_sq_eq]
      simp only [x₀, Fin.sum_univ_three, withLp_symm_ofLp_eq,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const, Real.norm_eq_abs]
      rw [show (![2 * t - 1, 0, 0] : Fin 3 → ℝ) 2 = 0 from rfl,
        show |2 * t - 1| ^ 2 = (2 * t - 1) ^ 2 from sq_abs _,
        show |(0:ℝ)| ^ 2 = 0 from by simp]
      nlinarith
    obtain ⟨y, hy_norm, hy_eq⟩ := exists_unit_preimage_of_kernel L hker x₀ hx₀_norm
    set Y₀ := y.ofLp 0
    set Y₁ := y.ofLp 1
    set Y₂ := y.ofLp 2
    have hy_sq : Y₀ ^ 2 + Y₁ ^ 2 + Y₂ ^ 2 = 1 := by
      have h1 : ∑ i : Fin 3, ‖y.ofLp i‖ ^ 2 = 1 := by
        have : ‖y‖ ^ 2 = 1 := by rw [hy_norm]; norm_num
        rwa [EuclideanSpace.norm_sq_eq] at this
      simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at h1
      convert h1 using 1
    have hLy : p * ↑Y₀ + ((b + c) / 2) * ↑Y₁ + Complex.I * ((b - c) / 2) * ↑Y₂ =
        p * ↑(2 * t - 1) := by
      have h1 : L y = L x₀ := hy_eq
      change L₀ (y.ofLp) = L₀ (x₀.ofLp) at h1
      simp only [L₀, LinearMap.coe_mk, AddHom.coe_mk] at h1
      simp only [x₀, withLp_symm_ofLp_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const] at h1
      rw [show (![2 * t - 1, 0, 0] : Fin 3 → ℝ) 2 = 0 from rfl] at h1
      simp only [Complex.ofReal_zero, mul_zero, add_zero] at h1
      exact h1
    have htarget : (M 0 0 + M 1 1) / 2 + p * ↑(2 * t - 1) =
        ↑t * M 0 0 + ↑(1 - t) * M 1 1 := by
      simp only [p]; push_cast; ring
    by_cases hY0 : -1 < Y₀
    · obtain ⟨v, hR, hN⟩ := construct_vector_from_sphere M Y₀ Y₁ Y₂ hy_sq hY0
      refine ⟨v, ?_, hN⟩
      rw [hR, show (M 0 0 - M 1 1) / 2 = p from rfl,
        show (M 0 1 + M 1 0) / 2 = (b + c) / 2 from rfl,
        show (M 0 1 - M 1 0) / 2 = (b - c) / 2 from rfl]
      rw [show (M 0 0 + M 1 1) / 2 +
        (p * ↑Y₀ + (b + c) / 2 * ↑Y₁ + Complex.I * ((b - c) / 2) * ↑Y₂) =
        (M 0 0 + M 1 1) / 2 + p * ↑(2 * t - 1) from by rw [hLy]]
      exact htarget
    · push_neg at hY0
      have hY0_eq : Y₀ = -1 := le_antisymm hY0
        (by nlinarith [hy_sq, sq_nonneg Y₁, sq_nonneg Y₂])
      have hY1 : Y₁ = 0 := by nlinarith [sq_nonneg Y₁, sq_nonneg Y₂, hY0_eq]
      have hY2 : Y₂ = 0 := by nlinarith [sq_nonneg Y₁, sq_nonneg Y₂, hY0_eq]
      have hp_zero : p = 0 := by
        rw [hY0_eq, hY1, hY2] at hLy
        simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero,
          mul_zero, add_zero, mul_neg, mul_one] at hLy
        have h1 : p * (↑(2 * t - 1) + 1) = 0 := by linear_combination -hLy
        rw [show (↑(2 * t - 1) : ℂ) + 1 = ↑(2 * t) from by push_cast; ring] at h1
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exfalso; exact ne_of_gt (show (0 : ℝ) < 2 * t by positivity)
            (Complex.ofReal_eq_zero.mp h)
      have hM_eq : M 0 0 = M 1 1 := by
        have : M 0 0 - M 1 1 = 0 := by
          rcases mul_eq_zero.mp (show (M 0 0 - M 1 1) * (1/2 : ℂ) = 0 from by
            rw [show (M 0 0 - M 1 1) * (1/2 : ℂ) = (M 0 0 - M 1 1) / 2 from by ring]
            exact hp_zero) with h | h
          · exact h
          · norm_num at h
        exact sub_eq_zero.mp this
      refine ⟨![0, 1], ?_, ?_⟩
      · simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [hM_eq]; ring
      · simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Complex.normSq_zero, Complex.normSq_one]

end CommutatorTheorem.THConvexity
