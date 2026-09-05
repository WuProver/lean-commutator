import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# Quantitative estimates for a finite positive-residue expansion

The estimates are proved directly for the reciprocal summands. In the MSS proof
the residues and pole locations are supplied by the stable-polynomial argument.
-/

open scoped BigOperators

namespace NoEpsilon.MSSResidueBounds

theorem reciprocal_tangent (a pole x δ : ℝ) (ha : 0 ≤ a) (hx : pole < x) (hδ : 0 ≤ δ) :
    a / (x + δ - pole) + δ * (a / (x + δ - pole) ^ 2) ≤ a / (x - pole) := by
  have hu : 0 < x - pole := sub_pos.mpr hx
  have hv : 0 < x + δ - pole := by linarith
  have hid : a / (x - pole) - a / (x + δ - pole) -
      δ * (a / (x + δ - pole) ^ 2) =
        a * δ ^ 2 / ((x - pole) * (x + δ - pole) ^ 2) := by
    field_simp
    ring
  have hnonneg : 0 ≤ a * δ ^ 2 / ((x - pole) * (x + δ - pole) ^ 2) := by positivity
  linarith

theorem finite_residue_tangent {ι : Type*} (s : Finset ι) (a pole : ι → ℝ)
    (x δ : ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hx : ∀ i ∈ s, pole i < x) (hδ : 0 ≤ δ) :
    (∑ i ∈ s, a i / (x + δ - pole i)) +
      δ * (∑ i ∈ s, a i / (x + δ - pole i) ^ 2) ≤
        ∑ i ∈ s, a i / (x - pole i) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i hi ↦ reciprocal_tangent (a i) (pole i) x δ (ha i hi) (hx i hi) hδ

theorem hasDerivAt_reciprocal (a pole x : ℝ) (hx : x ≠ pole) :
    HasDerivAt (fun t : ℝ ↦ a / (t - pole)) (-a / (x - pole) ^ 2) x := by
  convert (hasDerivAt_const x a).div ((hasDerivAt_id x).sub_const pole)
    (sub_ne_zero.mpr hx) using 1
  simp

theorem hasDerivAt_finite_residues {ι : Type*} (s : Finset ι) (a pole : ι → ℝ)
    (c x : ℝ) (hx : ∀ i ∈ s, x ≠ pole i) :
    HasDerivAt (fun t : ℝ ↦ c + ∑ i ∈ s, a i / (t - pole i))
      (-(∑ i ∈ s, a i / (x - pole i) ^ 2)) x := by
  simpa only [zero_add, neg_div, Finset.sum_neg_distrib] using (hasDerivAt_const x c).add
    (HasDerivAt.fun_sum (fun i hi ↦ hasDerivAt_reciprocal (a i) (pole i) x (hx i hi)))

/-- The tangent estimate includes a constant term, with no restriction on its sign. -/
theorem finite_residue_tangent_with_constant {ι : Type*} (s : Finset ι) (a pole : ι → ℝ)
    (c x δ : ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hx : ∀ i ∈ s, pole i < x) (hδ : 0 ≤ δ) :
    (c + ∑ i ∈ s, a i / (x + δ - pole i)) +
      δ * (∑ i ∈ s, a i / (x + δ - pole i) ^ 2) ≤
        c + ∑ i ∈ s, a i / (x - pole i) := by
  linarith [finite_residue_tangent s a pole x δ ha hx hδ]

end NoEpsilon.MSSResidueBounds
