import CommutatorTheorem.Defs
import CommutatorTheorem.Epsilon.SylvesterBound
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Rectangular Sylvester Equation Norm Estimate (范数估计)

This file formalizes Proposition 1 of `reference/范数估计.pdf` for rectangular `A`.

Let `S = diag(s₁,…,s_p) ∈ ℂ^{p×p}` and `T = diag(t₁,…,t_q) ∈ ℂ^{q×q}` be complex
diagonal matrices, and suppose there exists `δ > 0` such that
`Re(s_a − t_b) ≥ δ` for all `1 ≤ a ≤ p`, `1 ≤ b ≤ q`. Then for any rectangular
matrix `A ∈ ℂ^{p×q}`, the Sylvester equation `A = SC − CT` admits a unique
solution `C : Matrix (Fin p) (Fin q) ℂ` with:

* (i)   `C_{ab} = A_{ab} / (s_a − t_b)`;
* (ii)  `C = ∫₀^∞ e^{-uS} · A · e^{uT} du`;
* (iii) `‖C‖ ≤ ‖A‖ / δ`.

The square case is in `Rosenblum.lean` as `sylvester_diag_opNorm_bound_re`;
the proofs here mirror that file's structure but adapted for rectangular `A`.
-/

attribute [local instance] Matrix.instL2OpMetricSpace
                           Matrix.instL2OpNormedAddCommGroup
                           Matrix.instL2OpNormedSpace

open MeasureTheory Set Complex Finset

namespace CommutatorTheorem

/-! ## Rectangular helper lemmas (analogues of `SylvesterBound`) -/

private lemma rect_norm_diag_mul_mul_diag {p q : ℕ}
    (d : Fin p → ℂ) (e : Fin q → ℂ) (A : Matrix (Fin p) (Fin q) ℂ) :
    ‖Matrix.diagonal d * A * Matrix.diagonal e‖ ≤ ‖d‖ * ‖A‖ * ‖e‖ := by
  calc ‖Matrix.diagonal d * A * Matrix.diagonal e‖
      ≤ ‖Matrix.diagonal d * A‖ * ‖Matrix.diagonal e‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Matrix.diagonal d‖ * ‖A‖) * ‖Matrix.diagonal e‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖d‖ * ‖A‖ * ‖e‖ := by
        rw [Matrix.l2_opNorm_diagonal, Matrix.l2_opNorm_diagonal]

private lemma rect_pi_norm_mul_pi_norm_le {p q : ℕ} [NeZero p] [NeZero q]
    {f : Fin p → ℂ} {g : Fin q → ℂ} {C : ℝ} (_hC : 0 ≤ C)
    (h : ∀ a b, ‖f a‖ * ‖g b‖ ≤ C) :
    ‖f‖ * ‖g‖ ≤ C := by
  have hfi : ∃ a₀ : Fin p, ‖f‖ = ‖f a₀‖ := by
    rw [Pi.norm_def]
    have := Finset.exists_mem_eq_sup (univ : Finset (Fin p))
      ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne p)⟩, mem_univ _⟩ (fun a => ‖f a‖₊)
    obtain ⟨a₀, _, ha₀⟩ := this
    exact ⟨a₀, by rw [ha₀]; exact (coe_nnnorm _).symm⟩
  have hgj : ∃ b₀ : Fin q, ‖g‖ = ‖g b₀‖ := by
    rw [Pi.norm_def]
    have := Finset.exists_mem_eq_sup (univ : Finset (Fin q))
      ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne q)⟩, mem_univ _⟩ (fun b => ‖g b‖₊)
    obtain ⟨b₀, _, hb₀⟩ := this
    exact ⟨b₀, by rw [hb₀]; exact (coe_nnnorm _).symm⟩
  obtain ⟨a₀, ha₀⟩ := hfi
  obtain ⟨b₀, hb₀⟩ := hgj
  rw [ha₀, hb₀]
  exact h a₀ b₀

private lemma rect_norm_cexp_neg_mul_real (z : ℂ) (u : ℝ) :
    ‖Complex.exp (-z * ↑u)‖ = Real.exp (-z.re * u) := by
  rw [Complex.norm_exp]; congr 1
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- Rectangular analogue of `integrand_norm_bound`: under Re-separation
`Re(s_a − t_b) ≥ δ > 0`, the integrand `F(u) = diag(e^{-Su}) · A · diag(e^{Tu})`
has operator norm at most `‖A‖ · e^{-δu}` for `u ≥ 0`. -/
private lemma rect_integrand_norm_bound {p q : ℕ} [NeZero p] [NeZero q]
    (S : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ)
    (A : Matrix (Fin p) (Fin q) ℂ)
    (δ : ℝ) (_hδ : 0 < δ)
    (hRe : ∀ a b, δ ≤ (S a a - T b b).re) (u : ℝ) (hu : 0 ≤ u) :
    ‖Matrix.diagonal (fun a => Complex.exp (-(S a a) * ↑u)) * A *
      Matrix.diagonal (fun b => Complex.exp ((T b b) * ↑u))‖
      ≤ ‖A‖ * Real.exp (-δ * u) := by
  set d := fun a : Fin p => Complex.exp (-(S a a) * (↑u : ℂ))
  set e := fun b : Fin q => Complex.exp ((T b b) * (↑u : ℂ))
  calc ‖Matrix.diagonal d * A * Matrix.diagonal e‖
      ≤ ‖d‖ * ‖A‖ * ‖e‖ := rect_norm_diag_mul_mul_diag d e A
    _ = ‖A‖ * (‖d‖ * ‖e‖) := by ring
    _ ≤ ‖A‖ * Real.exp (-δ * u) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg A)
        apply rect_pi_norm_mul_pi_norm_le (Real.exp_pos _).le
        intro a b
        rw [rect_norm_cexp_neg_mul_real (S a a) u]
        change Real.exp (-(S a a).re * u) * ‖Complex.exp ((T b b) * ↑u)‖ ≤ _
        rw [Complex.norm_exp]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        rw [← Real.exp_add]
        apply Real.exp_le_exp_of_le
        have hst := hRe a b
        rw [Complex.sub_re] at hst
        nlinarith

/-! ## Proposition 1 (i): entrywise solution -/

/-- Rectangular Sylvester equation, entry-wise solution.
    For diagonal `S` (p×p) and `T` (q×q) with `S_{aa} ≠ T_{bb}` for all `a, b`,
    the rectangular matrix `C_{ab} = A_{ab} / (S_{aa} − T_{bb})` solves `SC − CT = A`. -/
lemma sylvester_rect_diag_solution {p q : ℕ}
    (S : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ)
    (A : Matrix (Fin p) (Fin q) ℂ)
    (hS : IsDiagMatrix S) (hT : IsDiagMatrix T)
    (hST : ∀ a b, S a a ≠ T b b) :
    let C : Matrix (Fin p) (Fin q) ℂ := fun a b => A a b / (S a a - T b b)
    S * C - C * T = A := by
  ext a b
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  have hSC : ∑ k, S a k * (A k b / (S k k - T b b)) =
      S a a * (A a b / (S a a - T b b)) := by
    apply Finset.sum_eq_single a
    · intro k _ hki; rw [hS a k (fun h => hki (h ▸ rfl)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hCT : ∑ k, (A a k / (S a a - T k k)) * T k b =
      (A a b / (S a a - T b b)) * T b b := by
    apply Finset.sum_eq_single b
    · intro k _ hkj; rw [hT k b (fun h => hkj (h ▸ rfl)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ b) h
  rw [hSC, hCT]
  have hne : S a a - T b b ≠ 0 := sub_ne_zero.mpr (hST a b)
  field_simp

/-! ## Proposition 1: combined statement (i) + (ii) + (iii)

For diagonal `S` (p×p), `T` (q×q) with `Re(S_{aa} - T_{bb}) ≥ δ > 0` for all
`a, b`, the rectangular Sylvester equation `SC − CT = A` has the unique
solution given entrywise by `C_{ab} = A_{ab} / (S_{aa} − T_{bb})`, equal to
the Bochner integral `∫₀^∞ e^{-uS} · A · e^{uT} du`, with operator norm
`‖C‖ ≤ ‖A‖ / δ`. -/
theorem sylvester_rect_diag_opNorm_bound_re {p q : ℕ}
    (S : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ)
    (A : Matrix (Fin p) (Fin q) ℂ)
    (hS : IsDiagMatrix S) (hT : IsDiagMatrix T)
    (δ : ℝ) (hδ : 0 < δ)
    (hRe : ∀ a b, δ ≤ (S a a - T b b).re) :
    let C : Matrix (Fin p) (Fin q) ℂ := fun a b => A a b / (S a a - T b b)
    (S * C - C * T = A) ∧
    (C = ∫ u in Ioi (0 : ℝ),
      Matrix.diagonal (fun a => Complex.exp (-(S a a) * ↑u)) * A *
      Matrix.diagonal (fun b => Complex.exp ((T b b) * ↑u))) ∧
    (‖C‖ ≤ ‖A‖ / δ) := by
  intro C
  have hST : ∀ a b, S a a ≠ T b b := fun a b h => by
    have := hRe a b; rw [h, sub_self] at this; simp at this; linarith
  -- (i): entrywise solution
  have h_eq : S * C - C * T = A := sylvester_rect_diag_solution S T A hS hT hST
  -- Handle p = 0 or q = 0 cases: the matrix space is trivial
  by_cases hp : p = 0
  · subst hp
    have hC_zero : C = 0 := by funext a; exact a.elim0
    refine ⟨h_eq, ?_, ?_⟩
    · rw [hC_zero]; ext a; exact a.elim0
    · rw [hC_zero, norm_zero]; positivity
  by_cases hq : q = 0
  · subst hq
    have hC_zero : C = 0 := by funext a b; exact b.elim0
    refine ⟨h_eq, ?_, ?_⟩
    · rw [hC_zero]; ext a b; exact b.elim0
    · rw [hC_zero, norm_zero]; positivity
  haveI : NeZero p := ⟨hp⟩
  haveI : NeZero q := ⟨hq⟩
  -- Define the integrand F(u) = diag(e^{-S·u}) · A · diag(e^{T·u})
  set F : ℝ → Matrix (Fin p) (Fin q) ℂ :=
    fun u => Matrix.diagonal (fun a => Complex.exp (-(S a a) * ↑u)) * A *
             Matrix.diagonal (fun b => Complex.exp ((T b b) * ↑u)) with hF_def
  -- F is integrable on (0,∞): dominated by ‖A‖ · e^{-δu}
  have hF_int : IntegrableOn F (Ioi (0 : ℝ)) := by
    apply MeasureTheory.Integrable.mono'
    · exact (exp_neg_integrableOn_Ioi 0 hδ).const_mul ‖A‖
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact rect_integrand_norm_bound S T A δ hδ hRe u (le_of_lt hu)
  -- Entry extraction as a ContinuousLinearMap
  have entry_clm : ∀ a : Fin p, ∀ b : Fin q,
      ∃ L : Matrix (Fin p) (Fin q) ℂ →L[ℂ] ℂ, ∀ M, L M = M a b := by
    intro a b
    let L₀ : Matrix (Fin p) (Fin q) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => M a b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact ⟨LinearMap.toContinuousLinearMap L₀, fun M => rfl⟩
  -- Entrywise integral identity: (∫ F u) a b = ∫ (F u) a b
  have integral_entry : ∀ a : Fin p, ∀ b : Fin q,
      (∫ u in Ioi (0 : ℝ), F u) a b = ∫ u in Ioi (0 : ℝ), (F u) a b := by
    intro a b
    obtain ⟨L, hL⟩ := entry_clm a b
    have := ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ) L hF_int
    simp only [hL] at this
    exact this.symm
  -- Each entry of F(u) simplifies to A_{ab} · exp(-(S_{aa}-T_{bb}) · u)
  have entry_F : ∀ a : Fin p, ∀ b : Fin q, ∀ u : ℝ,
      (F u) a b = A a b * Complex.exp (-(S a a - T b b) * u) := by
    intro a b u
    simp only [hF_def, Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, mul_ite, mul_zero, Finset.sum_ite_eq]
    rw [show Complex.exp (-S a a * ↑u) * A a b * Complex.exp (T b b * ↑u) =
        A a b * (Complex.exp (-S a a * ↑u) * Complex.exp (T b b * ↑u)) by ring,
        ← Complex.exp_add]
    ring_nf
  -- Scalar integral: ∫₀^∞ A_{ab} · exp(-(s-t)·u) du = A_{ab}/(s-t)
  have scalar_int : ∀ a : Fin p, ∀ b : Fin q,
      ∫ u in Ioi (0 : ℝ), A a b * Complex.exp (-(S a a - T b b) * ↑u) =
      A a b / (S a a - T b b) := by
    intro a b
    have hre : (-(S a a - T b b)).re < 0 := by
      have h1 := hRe a b
      rw [show (-(S a a - T b b)).re = -((S a a - T b b).re) from Complex.neg_re _]
      linarith
    have : ∫ u in Ioi (0 : ℝ), A a b * Complex.exp (-(S a a - T b b) * ↑u) =
        A a b * ∫ u in Ioi (0 : ℝ), Complex.exp (-(S a a - T b b) * ↑u) :=
      MeasureTheory.integral_const_mul _ _
    rw [this, integral_exp_mul_complex_Ioi hre 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hne : S a a - T b b ≠ 0 := sub_ne_zero.mpr (hST a b)
    field_simp
  -- (ii): Integral representation C = ∫₀^∞ F(u) du
  have hC_eq : C = (∫ u in Ioi (0 : ℝ), F u : Matrix (Fin p) (Fin q) ℂ) := by
    ext a b
    rw [integral_entry a b]
    simp only [entry_F a b]
    rw [scalar_int a b]
  refine ⟨h_eq, hC_eq, ?_⟩
  -- (iii): Norm bound via Bochner integral
  rw [hC_eq]
  calc ‖∫ u in Ioi (0 : ℝ), F u‖
      ≤ ∫ u in Ioi (0 : ℝ), ‖F u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), ‖A‖ * Real.exp (-δ * u) := by
        apply MeasureTheory.setIntegral_mono_on hF_int.norm
        · exact (exp_neg_integrableOn_Ioi 0 hδ).const_mul ‖A‖
        · exact measurableSet_Ioi
        · intro u hu
          exact rect_integrand_norm_bound S T A δ hδ hRe u (le_of_lt hu)
    _ = ‖A‖ / δ := by
        have : ∫ u in Ioi (0 : ℝ), ‖A‖ * Real.exp (-δ * u) =
            ‖A‖ * ∫ u in Ioi (0 : ℝ), Real.exp (-δ * u) := by
          rw [← MeasureTheory.integral_const_mul]
        rw [this]
        have h2 : ∫ u in Ioi (0 : ℝ), Real.exp (-δ * u) = 1 / δ := by
          have h3 : (fun u => Real.exp (-δ * u)) = (fun u => Real.exp ((-δ) * u)) := by
            ring_nf
          rw [h3, integral_exp_mul_Ioi (by linarith : -δ < 0) 0]
          simp [mul_zero, Real.exp_zero, neg_div]
        rw [h2]; ring

end CommutatorTheorem
