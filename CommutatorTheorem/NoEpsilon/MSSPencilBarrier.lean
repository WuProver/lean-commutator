import CommutatorTheorem.NoEpsilon.MSSBarrierIteration
import CommutatorTheorem.NoEpsilon.MSSRealPencil
import Mathlib.Analysis.Matrix.PosDef

/-!
# The deterministic MSS root bound for positive semidefinite pencils

Starting from total covariance identity and small traces, the proved quantitative
barrier iteration bounds the diagonal roots by `(1 + sqrt ε)^2`.
-/

namespace NoEpsilon.MSSPencilBarrier

open Matrix NoEpsilon.MSSStability NoEpsilon.MSSBarrier
open NoEpsilon.MSSBarrierIteration NoEpsilon.MSSRealPencil
open scoped BigOperators ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The real determinant pencil is positive on the entire orthant above every
positive scalar vector when the total covariance is the identity. -/
theorem realPencil_aboveRoots (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hTotal : ∑ i, A i = 1) (t : ℝ) (ht : 0 < t) :
    AboveRoots (realPencil A) (fun _ : κ ↦ t) := by
  intro y hy
  have hsmall : ((t : ℂ) • (1 : Matrix ι ι ℂ)).PosDef :=
    PosDef.one.smul (by exact_mod_cast ht)
  have hrest : (∑ i : κ, ((y i - t : ℝ) : ℂ) • A i).PosSemidef := by
    apply posSemidef_sum
    intro i _
    have hyt : 0 ≤ y i - t := sub_nonneg.mpr (hy i)
    exact (hA i).smul (by exact_mod_cast hyt)
  have heq : (∑ i : κ, (y i : ℂ) • A i) =
      (t : ℂ) • 1 + ∑ i : κ, ((y i - t : ℝ) : ℂ) • A i := by
    rw [← hTotal, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← add_smul]
    congr 1
    push_cast
    ring
  have hpos : (∑ i : κ, (y i : ℂ) • A i).PosDef := by
    rw [heq]
    exact hsmall.add_posSemidef hrest
  have heval : ((MvPolynomial.eval y (realPencil A) : ℝ) : ℂ) =
      (∑ i : κ, (y i : ℂ) • A i).det := by
    rw [← eval_complexification, map_realPencil A (fun i ↦ (hA i).isHermitian),
      eval_psdPencil]
  have hdet := hpos.det_pos
  rw [← heval] at hdet
  exact_mod_cast hdet

/-- The real initial barrier equals the real trace divided by the starting
scalar, by the exact determinant first-variation formula. -/
theorem realPencil_initial_barrier [Nonempty ι]
    (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hTotal : ∑ i, A i = 1) (t : ℝ) (ht : t ≠ 0) (i : κ) :
    barrier (realPencil A) i (fun _ : κ ↦ t) = (A i).trace.re / t := by
  have he := psdPencil_initial_logDerivative A hTotal (t : ℂ)
    (Complex.ofReal_ne_zero.mpr ht) i
  rw [← map_realPencil A hA, MvPolynomial.pderiv_map] at he
  simp only [eval_complexification] at he
  have hr := congrArg Complex.re he
  simpa [barrier] using hr

/-- The complete deterministic MSS barrier bound, with no supplied barrier
monotonicity, convexity, or root-selection hypothesis. -/
theorem realPencil_fold_aboveRoots [Nonempty ι]
    (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hTotal : ∑ i, A i = 1) (ε : ℝ) (hε : 0 < ε)
    (htrace : ∀ i : κ, (A i).trace.re ≤ ε)
    (xs : List κ) (hxs : xs.Nodup) :
    AboveRoots (xs.foldl (fun p i ↦ p - MvPolynomial.pderiv i p) (realPencil A))
      (fun _ : κ ↦ (1 + Real.sqrt ε)^2) := by
  have hstable := realPencil_realStable A hA (by rw [hTotal]; exact PosDef.one)
  have ht : 0 < ε + Real.sqrt ε := (optimized_parameters hε).1
  apply aboveRoots_fold_optimized hstable ε hε (realPencil_aboveRoots A hA hTotal _ ht)
    _ xs hxs
  intro i
  rw [realPencil_initial_barrier A (fun i ↦ (hA i).isHermitian) hTotal _ ht.ne']
  exact div_le_div_of_nonneg_right (htrace i) ht.le

/-- The complex diagonal evaluation of the mixed difference polynomial has no
root at or beyond the MSS bound. This is the interface to expected characteristic
polynomials and interlacing selection. -/
theorem psdPencil_fold_eval_ne_zero [Nonempty ι]
    (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hTotal : ∑ i, A i = 1) (ε : ℝ) (hε : 0 < ε)
    (htrace : ∀ i : κ, (A i).trace.re ≤ ε)
    (xs : List κ) (hxs : xs.Nodup) (x : ℝ) (hx : (1 + Real.sqrt ε)^2 ≤ x) :
    MvPolynomial.eval (fun _ : κ ↦ (x : ℂ))
      (xs.foldl (fun p i ↦ p - MvPolynomial.pderiv i p) (psdPencil A)) ≠ 0 := by
  have ha := realPencil_fold_aboveRoots A hA hTotal ε hε htrace xs hxs
  have hpos : 0 < MvPolynomial.eval (fun _ : κ ↦ x)
      (xs.foldl (fun p i ↦ p - MvPolynomial.pderiv i p) (realPencil A)) :=
    ha _ (fun _ ↦ hx)
  rw [← map_realPencil A (fun i ↦ (hA i).isHermitian), ← map_fold_sub_pderiv,
    eval_complexification]
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

end NoEpsilon.MSSPencilBarrier
