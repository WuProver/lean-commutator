import NoEpsilon.MSSPick
import Mathlib.FieldTheory.Separable

/-!
# Positive residues for coprime rational Pick functions

The pole multiplicities and residue signs are proved from the upper-half-plane
sign, using the Laurent analysis in `MSSPick`.
-/

namespace NoEpsilon.MSSResidues

open Polynomial NoEpsilon.MSSPick

@[simp] theorem eval_map_ofReal (p : ℝ[X]) (r : ℝ) :
    (p.map Complex.ofRealHom).eval (r : ℂ) = ((p.eval r : ℝ) : ℂ) := by
  change (p.map Complex.ofRealHom).eval (Complex.ofRealHom r) = Complex.ofRealHom (p.eval r)
  rw [Polynomial.eval_map_apply]

/-- Two coprime polynomials cannot vanish at the same point. -/
theorem eval_ne_zero_of_coprime_of_root {g h : ℝ[X]} (hcop : IsCoprime g h)
    {r : ℝ} (hr : h.eval r = 0) : g.eval r ≠ 0 := by
  intro hg
  rcases hcop with ⟨a, b, hab⟩
  have he := congrArg (fun p : ℝ[X] ↦ p.eval r) hab
  simp [hg, hr] at he

/-- Every real pole of a reduced rational Pick function is simple, with positive
residue. No partial-fraction expansion is assumed in this result. -/
theorem real_root_simple_and_residue_pos (g h : ℝ[X]) (hzero : h ≠ 0)
    (hcop : IsCoprime g h)
    (hsign : ∀ z : ℂ, 0 < z.im → (h.map Complex.ofRealHom).eval z ≠ 0 →
      ((g.map Complex.ofRealHom).eval z / (h.map Complex.ofRealHom).eval z).im ≤ 0)
    (r : ℝ) (hr : h.eval r = 0) :
    h.rootMultiplicity r = 1 ∧ 0 < g.eval r / h.derivative.eval r := by
  have hg : g.eval r ≠ 0 := eval_ne_zero_of_coprime_of_root hcop hr
  let h₀ := h /ₘ (X - C r) ^ h.rootMultiplicity r
  have hh₀ : h₀.eval r ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero r hzero
  have hfactor : h = (X - C r) ^ h.rootMultiplicity r * h₀ :=
    (h.pow_mul_divByMonic_rootMultiplicity_eq r).symm
  have hn : 0 < h.rootMultiplicity r := (rootMultiplicity_pos hzero).mpr hr
  have hcomplex : h.map Complex.ofRealHom =
      (X - C (r : ℂ)) ^ h.rootMultiplicity r * h₀.map Complex.ofRealHom := by
    have hc := congrArg (Polynomial.map Complex.ofRealHom) hfactor
    simpa using hc
  have hhcomplex : (h₀.map Complex.ofRealHom).eval (r : ℂ) ≠ 0 := by
    simpa using Complex.ofReal_ne_zero.mpr hh₀
  have hvalue : (g.map Complex.ofRealHom).eval (r : ℂ) /
      (h₀.map Complex.ofRealHom).eval (r : ℂ) = (g.eval r / h₀.eval r : ℝ) := by
    simp
  obtain ⟨hmult, hpos⟩ := simple_real_pole_of_factorization
    (g.map Complex.ofRealHom) (h.map Complex.ofRealHom) (h₀.map Complex.ofRealHom)
    r hn hcomplex hhcomplex (div_ne_zero hg hh₀) hvalue hsign
  refine ⟨hmult, ?_⟩
  have hd : h.derivative.eval r = h₀.eval r := by
    rw [hfactor, hmult]
    simp
  rwa [hd]

/-- A split denominator of a coprime rational Pick function is separable. -/
theorem denominator_separable (g h : ℝ[X]) (hzero : h ≠ 0) (hsplit : h.Splits)
    (hcop : IsCoprime g h)
    (hsign : ∀ z : ℂ, 0 < z.im → (h.map Complex.ofRealHom).eval z ≠ 0 →
      ((g.map Complex.ofRealHom).eval z / (h.map Complex.ofRealHom).eval z).im ≤ 0) :
    h.Separable := by
  classical
  apply (nodup_roots_iff_of_splits hzero hsplit).mp
  rw [Multiset.nodup_iff_count_le_one]
  intro r
  rw [count_roots]
  by_cases hr : h.eval r = 0
  · rw [(real_root_simple_and_residue_pos g h hzero hcop hsign r hr).1]
  · rw [rootMultiplicity_eq_zero hr]
    exact Nat.zero_le _

end NoEpsilon.MSSResidues
