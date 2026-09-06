import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Local poles of rational Pick functions

These analytic lemmas supply the simple-pole and residue-sign ingredients for
an elementary MSS barrier proof, without a determinantal representation theorem.
-/

namespace NoEpsilon.MSSPick

open Filter Polynomial
open scoped Topology

/-- The upper half-plane contains an `n`th root of `I` for every positive `n`. -/
theorem exists_upper_pow_I {n : ℕ} (hn : 0 < n) :
    ∃ w : ℂ, 0 < w.im ∧ w ^ n = Complex.I := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnR)
  let θ : ℝ := (Real.pi / 2) / (n : ℝ)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    rw [div_lt_iff₀ hnR]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  refine ⟨Complex.exp ((θ : ℂ) * Complex.I), ?_, ?_⟩
  · simpa using Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  · rw [← Complex.exp_nat_mul]
    convert Complex.exp_pi_div_two_mul_I using 2
    dsimp [θ]
    push_cast
    field_simp [hnC]

/-- For order at least two, there is also an upper-half-plane root of `-I`. -/
theorem exists_upper_pow_neg_I {n : ℕ} (hn : 2 ≤ n) :
    ∃ w : ℂ, 0 < w.im ∧ w ^ n = -Complex.I := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnR)
  let θ : ℝ := (3 * Real.pi / 2) / (n : ℝ)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    rw [div_lt_iff₀ hnR]
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  refine ⟨Complex.exp ((θ : ℂ) * Complex.I), ?_, ?_⟩
  · simpa using Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  · rw [← Complex.exp_nat_mul]
    have he : (n : ℂ) * ((θ : ℂ) * Complex.I) =
        (Real.pi : ℂ) / 2 * Complex.I + (Real.pi : ℂ) * Complex.I := by
      dsimp [θ]
      push_cast
      field_simp [hnC]
      ring
    rw [he, Complex.exp_add_pi_mul_I, Complex.exp_pi_div_two_mul_I]

/-- A nonzero real leading Laurent coefficient with the Pick sign on every
upper ray must be a positive simple-pole coefficient. -/
theorem pole_order_eq_one_of_power_sign {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : a ≠ 0)
    (hsign : ∀ w : ℂ, 0 < w.im → ((a : ℂ) / w ^ n).im ≤ 0) :
    n = 1 ∧ 0 < a := by
  obtain ⟨w, hw, hwpow⟩ := exists_upper_pow_I hn
  have hapos := hsign w hw
  rw [hwpow] at hapos
  have ha0 : 0 ≤ a := by simpa [Complex.div_im] using hapos
  have hapos' : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
  refine ⟨?_, hapos'⟩
  by_contra hn1
  have hn2 : 2 ≤ n := by omega
  obtain ⟨v, hv, hvpow⟩ := exists_upper_pow_neg_I hn2
  have haneg := hsign v hv
  rw [hvpow] at haneg
  have ha1 : a ≤ 0 := by simpa [Complex.div_im] using haneg
  exact (not_lt_of_ge ha1) hapos'

/-- Reading a Laurent leading coefficient along an arbitrary nonzero ray. -/
theorem laurent_ray_limit {f : ℂ → ℂ} {c a : ℂ} {n : ℕ}
    (hlim : Tendsto (fun z : ℂ ↦ (z - c) ^ n * f z) (𝓝[≠] c) (𝓝 a))
    {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun t : ℝ ↦ (t : ℂ)^n * f (c + (t : ℂ) * w))
      (𝓝[>] 0) (𝓝 (a / w^n)) := by
  have hpath : Tendsto (fun t : ℝ ↦ c + (t : ℂ) * w) (𝓝[>] 0) (𝓝[≠] c) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ ↦ c + (t : ℂ) * w) := by fun_prop
      simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change c + (t : ℂ) * w ≠ c
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      simpa using mul_ne_zero ht0 hw
  have hl := (hlim.comp hpath).div_const (w ^ n)
  have heq : ∀ t : ℝ,
      ((c + (t : ℂ) * w - c)^n * f (c + (t : ℂ) * w)) / w^n =
        (t : ℂ)^n * f (c + (t : ℂ) * w) := by
    intro t
    have hsub : c + (t : ℂ) * w - c = (t : ℂ) * w := by ring
    rw [hsub, mul_pow]
    field_simp
  simpa only [Function.comp_def, heq] using hl

/-- A nonzero real Laurent leading term of a function with the Pick sign on
upper rays has pole order exactly one and positive residue. The proof takes
limits along two explicit upper rays; it does not assume a residue theorem. -/
theorem simple_pole_of_laurent_limit {f : ℂ → ℂ} (r : ℝ) {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : a ≠ 0)
    (hlim : Tendsto (fun z : ℂ ↦ (z - (r : ℂ)) ^ n * f z)
      (𝓝[≠] (r : ℂ)) (𝓝 (a : ℂ)))
    (hsign : ∀ w : ℂ, 0 < w.im →
      ∀ᶠ t : ℝ in 𝓝[>] 0, (f ((r : ℂ) + (t : ℂ) * w)).im ≤ 0) :
    n = 1 ∧ 0 < a := by
  apply pole_order_eq_one_of_power_sign hn ha
  intro w hw
  have hw0 : w ≠ 0 := by intro h; subst w; simp at hw
  have hpath : Tendsto (fun t : ℝ ↦ (r : ℂ) + (t : ℂ) * w)
      (𝓝[>] 0) (𝓝[≠] (r : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ ↦ (r : ℂ) + (t : ℂ) * w) := by fun_prop
      simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change (r : ℂ) + (t : ℂ) * w ≠ (r : ℂ)
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      simpa using mul_ne_zero ht0 hw0
  have hl := (hlim.comp hpath).div_const (w ^ n)
  have heq : ∀ t : ℝ,
      (((r : ℂ) + (t : ℂ) * w - (r : ℂ)) ^ n *
        f ((r : ℂ) + (t : ℂ) * w)) / w ^ n =
        (t : ℂ) ^ n * f ((r : ℂ) + (t : ℂ) * w) := by
    intro t
    have hsub : (r : ℂ) + (t : ℂ) * w - (r : ℂ) = (t : ℂ) * w := by ring
    rw [hsub, mul_pow]
    field_simp
  have hli : Tendsto (fun t : ℝ ↦
      ((t : ℂ)^n * f ((r : ℂ) + (t : ℂ) * w)).im)
      (𝓝[>] 0) (𝓝 ((a : ℂ) / w^n).im) := by
    have hh := Complex.continuous_im.continuousAt.tendsto.comp hl
    simpa only [Function.comp_def, heq] using hh
  apply le_of_tendsto hli
  filter_upwards [hsign w hw, self_mem_nhdsWithin] with t ht htpos
  have ht0 : 0 ≤ t := le_of_lt htpos
  simpa [← Complex.ofReal_pow, Complex.mul_im] using
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht0 n) ht

/-- A factored rational function with the Pick sign cannot have a real pole of
order greater than one. This specializes the preceding analytic limit lemma to
actual polynomials, deriving the Laurent limit by cancellation. -/
theorem simple_real_pole_of_factorization (g h h₀ : ℂ[X]) (r : ℝ)
    {n : ℕ} (hn : 0 < n) (hfactor : h = (X - C (r : ℂ)) ^ n * h₀)
    (hh₀ : h₀.eval (r : ℂ) ≠ 0) {a : ℝ} (ha : a ≠ 0)
    (hvalue : g.eval (r : ℂ) / h₀.eval (r : ℂ) = (a : ℂ))
    (hsign : ∀ z : ℂ, 0 < z.im → h.eval z ≠ 0 → (g.eval z / h.eval z).im ≤ 0) :
    n = 1 ∧ 0 < a := by
  let f : ℂ → ℂ := fun z ↦ g.eval z / h.eval z
  apply simple_pole_of_laurent_limit (f := f) r hn ha
  · have hc : ContinuousAt (fun z : ℂ ↦ g.eval z / h₀.eval z) (r : ℂ) :=
      g.continuous.continuousAt.div h₀.continuous.continuousAt hh₀
    have hl : Tendsto (fun z : ℂ ↦ g.eval z / h₀.eval z)
        (𝓝[≠] (r : ℂ)) (𝓝 (a : ℂ)) := by
      rw [← hvalue]
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z - (r : ℂ) ≠ 0 := sub_ne_zero.mpr hz
    dsimp [f]
    rw [hfactor, eval_mul, eval_pow, eval_sub, eval_X, eval_C, ← mul_div_assoc,
      mul_div_mul_left _ _ (pow_ne_zero n hz0)]
  · intro w hw
    have hw0 : w ≠ 0 := by intro h; subst w; simp at hw
    have hc : Continuous (fun t : ℝ ↦ h₀.eval ((r : ℂ) + (t : ℂ) * w)) := by
      apply h₀.continuous.comp
      fun_prop
    have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0,
        h₀.eval ((r : ℂ) + (t : ℂ) * w) ≠ 0 :=
      ((hc.continuousAt (x := 0)).eventually_ne (by simpa using hh₀)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hevent, self_mem_nhdsWithin] with t ht htpos
    change 0 < t at htpos
    apply hsign
    · simpa [Complex.add_im, Complex.mul_im] using mul_pos htpos hw
    · have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
      have heq : (r : ℂ) + (t : ℂ) * w - (r : ℂ) = (t : ℂ) * w := by ring
      rw [hfactor, eval_mul, eval_pow, eval_sub, eval_X, eval_C, heq]
      exact mul_ne_zero (pow_ne_zero n (mul_ne_zero ht0 hw0)) ht

/-- The logarithmic derivative of a polynomial factorization, with an explicit
multiplicity. All denominator conditions are stated at the evaluation point. -/
theorem logDerivative_of_factorization (h h₀ : ℂ[X]) (c z : ℂ) (n : ℕ)
    (hfactor : h = (X - C c) ^ (n + 1) * h₀) (hz : z ≠ c) (hh₀ : h₀.eval z ≠ 0) :
    h.derivative.eval z / h.eval z = (n+1 : ℂ) / (z-c) + h₀.derivative.eval z / h₀.eval z := by
  have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz
  rw [hfactor]
  simp only [derivative_mul, derivative_pow, derivative_sub, derivative_X,
    derivative_C, sub_zero, mul_one, eval_add, eval_mul, eval_pow,
    eval_sub, eval_X, eval_C, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  field_simp

/-- Every root of a polynomial is a simple pole of its logarithmic derivative;
the residue is exactly the root multiplicity. -/
theorem logDerivative_laurent_limit (h h₀ : ℂ[X]) (c : ℂ) (n : ℕ)
    (hfactor : h = (X - C c) ^ (n + 1) * h₀) (hh₀ : h₀.eval c ≠ 0) :
    Tendsto (fun z : ℂ ↦ (z-c) * (h.derivative.eval z / h.eval z))
      (𝓝[≠] c) (𝓝 (n+1 : ℂ)) := by
  have hc : ContinuousAt (fun z : ℂ ↦ (n+1 : ℂ) +
      (z-c) * (h₀.derivative.eval z / h₀.eval z)) c := by
    apply continuousAt_const.add
    apply (continuousAt_id.sub continuousAt_const).mul
    exact h₀.derivative.continuous.continuousAt.div h₀.continuous.continuousAt hh₀
  have hl : Tendsto (fun z : ℂ ↦ (n+1 : ℂ) +
      (z-c) * (h₀.derivative.eval z / h₀.eval z)) (𝓝[≠] c) (𝓝 (n+1 : ℂ)) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin,
    (h₀.continuous.continuousAt.eventually_ne hh₀).filter_mono nhdsWithin_le_nhds]
      with z hz hhz
  have hz0 : z - c ≠ 0 := sub_ne_zero.mpr hz
  rw [logDerivative_of_factorization h h₀ c z n hfactor hz hhz]
  field_simp [hz0]

/-- A polynomial is upper-half-plane nonvanishing if its logarithmic derivative
has the Pick sign wherever defined there. A hypothetical upper root is approached
from below; its positive multiplicity then gives the opposite sign. -/
theorem upperStable_of_logDerivative_sign (h : ℂ[X]) (hzero : h ≠ 0)
    (hsign : ∀ z : ℂ, 0 < z.im → h.eval z ≠ 0 →
      (h.derivative.eval z / h.eval z).im ≤ 0) :
    ∀ z : ℂ, 0 < z.im → h.eval z ≠ 0 := by
  intro c hc hroot
  have hmult : 0 < h.rootMultiplicity c :=
    (rootMultiplicity_pos hzero).mpr hroot
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hmult.ne'
  let h₀ := h /ₘ (X - C c) ^ h.rootMultiplicity c
  have hfactor : h = (X - C c) ^ (n + 1) * h₀ := by
    simpa only [h₀, hn] using (h.pow_mul_divByMonic_rootMultiplicity_eq c).symm
  have hh₀ : h₀.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hzero
  have hl := logDerivative_laurent_limit h h₀ c n hfactor hh₀
  have hl' : Tendsto (fun z : ℂ ↦ (z-c)^1 * (h.derivative.eval z / h.eval z))
      (𝓝[≠] c) (𝓝 (n+1 : ℂ)) := by simpa using hl
  have hray := laurent_ray_limit hl' (show -Complex.I ≠ 0 by simp)
  have hreal : Tendsto (fun t : ℝ ↦
      ((t : ℂ) * (h.derivative.eval (c + (t : ℂ) * (-Complex.I)) /
        h.eval (c + (t : ℂ) * (-Complex.I)))).im)
      (𝓝[>] 0) (𝓝 ((n : ℝ)+1)) := by
    have hi := Complex.continuous_im.continuousAt.tendsto.comp hray
    simpa [Function.comp_def, Complex.div_im] using hi
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] 0, t < c.im := by
    have he : ∀ᶠ t : ℝ in 𝓝 0, t < c.im := eventually_lt_nhds hc
    exact he.filter_mono nhdsWithin_le_nhds
  have hc₀ : Continuous (fun t : ℝ ↦ h₀.eval (c + (t : ℂ) * (-Complex.I))) := by
    apply h₀.continuous.comp
    fun_prop
  have hnonzero : ∀ᶠ t : ℝ in 𝓝[>] 0,
      h₀.eval (c + (t : ℂ) * (-Complex.I)) ≠ 0 :=
    ((hc₀.continuousAt (x := 0)).eventually_ne (by simpa using hh₀)).filter_mono
      nhdsWithin_le_nhds
  have hbad : (n : ℝ)+1 ≤ 0 := by
    apply le_of_tendsto hreal
    filter_upwards [hnear, hnonzero, self_mem_nhdsWithin] with t ht htn htpos
    change 0 < t at htpos
    have him : 0 < (c + (t : ℂ) * (-Complex.I)).im := by
      simpa using sub_pos.mpr ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
    have heval : h.eval (c + (t : ℂ) * (-Complex.I)) ≠ 0 := by
      rw [hfactor, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      apply mul_ne_zero _ htn
      apply pow_ne_zero
      simpa using mul_ne_zero ht0 (show -Complex.I ≠ 0 by simp)
    have hs := hsign _ him heval
    simpa [Complex.mul_im] using mul_nonpos_of_nonneg_of_nonpos htpos.le hs
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end NoEpsilon.MSSPick
