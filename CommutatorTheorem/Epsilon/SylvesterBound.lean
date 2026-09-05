import CommutatorTheorem.Defs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.ExpDecay

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra

open CommutatorTheorem MeasureTheory Set Complex Finset

namespace CommutatorTheorem

/-! ### Helper lemmas for the exponential integral bound -/

private lemma norm_cexp_neg_mul_real (z : ℂ) (u : ℝ) :
    ‖Complex.exp (-z * ↑u)‖ = Real.exp (-z.re * u) := by
  rw [Complex.norm_exp]; congr 1
  simp [mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma norm_diag_mul_mul_diag' {m : ℕ} (d e : Fin m → ℂ) (A : Matrix (Fin m) (Fin m) ℂ) :
    ‖Matrix.diagonal d * A * Matrix.diagonal e‖ ≤ ‖d‖ * ‖A‖ * ‖e‖ := by
  calc ‖Matrix.diagonal d * A * Matrix.diagonal e‖
      ≤ ‖Matrix.diagonal d * A‖ * ‖Matrix.diagonal e‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Matrix.diagonal d‖ * ‖A‖) * ‖Matrix.diagonal e‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖d‖ * ‖A‖ * ‖e‖ := by
        rw [Matrix.l2_opNorm_diagonal, Matrix.l2_opNorm_diagonal]

private lemma pi_norm_mul_pi_norm_le {m : ℕ} [NeZero m]
    {f : Fin m → ℂ} {g : Fin m → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i j, ‖f i‖ * ‖g j‖ ≤ C) :
    ‖f‖ * ‖g‖ ≤ C := by
  have hfi : ∃ i₀ : Fin m, ‖f‖ = ‖f i₀‖ := by
    rw [Pi.norm_def]
    have := Finset.exists_mem_eq_sup (univ : Finset (Fin m))
      ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩, mem_univ _⟩ (fun i => ‖f i‖₊)
    obtain ⟨i₀, _, hi₀⟩ := this
    exact ⟨i₀, by rw [hi₀]; exact (coe_nnnorm _).symm⟩
  have hgj : ∃ j₀ : Fin m, ‖g‖ = ‖g j₀‖ := by
    rw [Pi.norm_def]
    have := Finset.exists_mem_eq_sup (univ : Finset (Fin m))
      ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩, mem_univ _⟩ (fun j => ‖g j‖₊)
    obtain ⟨j₀, _, hj₀⟩ := this
    exact ⟨j₀, by rw [hj₀]; exact (coe_nnnorm _).symm⟩
  obtain ⟨i₀, hi₀⟩ := hfi
  obtain ⟨j₀, hj₀⟩ := hgj
  rw [hi₀, hj₀]
  exact h i₀ j₀

lemma integrand_norm_bound {m : ℕ} [NeZero m]
    (S T A : Matrix (Fin m) (Fin m) ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hRe : ∀ i j, δ ≤ (S i i - T j j).re) (u : ℝ) (hu : 0 ≤ u) :
    ‖Matrix.diagonal (fun i => Complex.exp (-(S i i) * ↑u)) * A *
      Matrix.diagonal (fun j => Complex.exp ((T j j) * ↑u))‖ ≤ ‖A‖ * Real.exp (-δ * u) := by
  set d := fun i : Fin m => Complex.exp (-(S i i) * (↑u : ℂ))
  set e := fun j : Fin m => Complex.exp ((T j j) * (↑u : ℂ))
  calc ‖Matrix.diagonal d * A * Matrix.diagonal e‖
      ≤ ‖d‖ * ‖A‖ * ‖e‖ := norm_diag_mul_mul_diag' d e A
    _ = ‖A‖ * (‖d‖ * ‖e‖) := by ring
    _ ≤ ‖A‖ * Real.exp (-δ * u) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg A)
        apply pi_norm_mul_pi_norm_le (Real.exp_pos _).le
        intro i j
        rw [norm_cexp_neg_mul_real (S i i) u]
        show Real.exp (-(S i i).re * u) * ‖Complex.exp ((T j j) * ↑u)‖ ≤ _
        rw [Complex.norm_exp]
        simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        rw [← Real.exp_add]
        apply Real.exp_le_exp_of_le
        have hst := hRe i j
        rw [sub_re] at hst
        nlinarith

end CommutatorTheorem
