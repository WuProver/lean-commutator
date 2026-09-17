import CommutatorTheorem.NoEpsilon.MSSSpecialization
import CommutatorTheorem.NoEpsilon.MSSResidues
import CommutatorTheorem.NoEpsilon.MSSReducedFraction
import CommutatorTheorem.NoEpsilon.MSSPartialFractions
import CommutatorTheorem.NoEpsilon.MSSResidueBounds

/-!
# The cross-coordinate MSS barrier as a finite positive-residue sum

Real stability supplies every hypothesis of the partial-fraction expansion:
real poles, simple reduced denominator, positive residues, and bounded degree.
-/

namespace NoEpsilon.MSSCrossBarrier

open Polynomial NoEpsilon.MSSStability NoEpsilon.MSSBarrier
open NoEpsilon.MSSSpecialization NoEpsilon.MSSResidues NoEpsilon.MSSReducedFraction
open NoEpsilon.MSSPartialFractions NoEpsilon.MSSResidueBounds
open scoped BigOperators Topology

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedFintypeInType false in
/-- Every cross-coordinate barrier above the roots is a constant plus a finite
sum of positive residues at strictly negative poles. -/
theorem exists_barrier_residue_expansion {p : MvPolynomial σ ℝ} (hp : RealStable p)
    {z : σ → ℝ} (hz : AboveRoots p z) (i j : σ) :
    ∃ (s : Finset ℝ) (a : ℝ → ℝ) (c : ℝ),
      (∀ r ∈ s, r < 0 ∧ 0 < a r) ∧
      ∀ t : ℝ, MvPolynomial.eval (coordinateShift z j t) p ≠ 0 →
        barrier p i (coordinateShift z j t) = c + ∑ r ∈ s, a r / (t-r) := by
  classical
  let g := coordinatePolynomial (MvPolynomial.pderiv i p) z j
  let h := coordinatePolynomial p z j
  have hpos : 0 < h.eval 0 := by simpa [h] using hz.eval_pos
  have hzero : h ≠ 0 := fun he ↦ hpos.ne' (by rw [he]; simp)
  have hsplit := coordinatePolynomial_splits hp z j hzero
  have hdeg := barrier_quotient_natDegree_le hp hz i j
  obtain ⟨D, G, H, hD, hH, hg, hh, hcop, hsplitH, hdegH⟩ :=
    exists_reduced_fraction g h hzero hsplit hdeg
  have hupper : ∀ w : ℂ, 0 < w.im → (h.map Complex.ofRealHom).eval w ≠ 0 := by
    rw [show h = coordinatePolynomial p z j from rfl, map_coordinatePolynomial]
    apply coordinatePolynomial_upperStable hp z j
    have hmap : h.map Complex.ofRealHom ≠ 0 :=
      fun he ↦ hzero ((Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp he)
    simpa only [h, map_coordinatePolynomial] using hmap
  have hsign : ∀ w : ℂ, 0 < w.im → (H.map Complex.ofRealHom).eval w ≠ 0 →
      ((G.map Complex.ofRealHom).eval w / (H.map Complex.ofRealHom).eval w).im ≤ 0 := by
    intro w hw _
    have hnonzero := hupper w hw
    have hcancel := eval₂_reduced_fraction Complex.ofRealHom g h D G H hg hh w
      (by simpa only [Polynomial.eval_map] using hnonzero)
    simp only [← Polynomial.eval_map] at hcancel
    rw [hcancel.2]
    exact coordinate_quotient_pick hp z i j w hw.le hnonzero
  have hsep := denominator_separable G H hH hsplitH hcop hsign
  obtain ⟨c, hc⟩ := partial_fractions_of_natDegree_le G H hH hsplitH hsep hdegH
  refine ⟨H.roots.toFinset, (fun r ↦ G.eval r / H.derivative.eval r), c, ?_, ?_⟩
  · intro r hr
    have hHr : H.eval r = 0 := (mem_roots hH).mp (Multiset.mem_toFinset.mp hr)
    have hhr : h.eval r = 0 := by rw [hh, eval_mul, hHr, mul_zero]
    refine ⟨coordinatePolynomial_roots_neg hz j ((mem_roots hzero).mpr hhr), ?_⟩
    exact (real_root_simple_and_residue_pos G H hH hcop hsign r hHr).2
  · intro t ht
    have hht : h.eval t ≠ 0 := by simpa [h] using ht
    obtain ⟨hHt, hcancel⟩ := eval_reduced_fraction g h D G H hg hh t hht
    have hbarrier : barrier p i (coordinateShift z j t) = g.eval t / h.eval t := by
      simp [g, h, barrier]
    rw [hbarrier, ← hcancel, hc t hHt]

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedFintypeInType false in
/-- The supporting-tangent estimate in MSS Lemma 5.7. This is the required
cross-coordinate convexity consequence, derived entirely from real stability. -/
theorem barrier_coordinate_tangent {p : MvPolynomial σ ℝ} (hp : RealStable p)
    {z : σ → ℝ} (hz : AboveRoots p z) (i j : σ) (δ : ℝ) (hδ : 0 ≤ δ) :
    barrier p i (coordinateShift z j δ) -
      δ * mixedBarrierDerivative p i j (coordinateShift z j δ) ≤ barrier p i z := by
  obtain ⟨s, a, c, ha, hrep⟩ := exists_barrier_residue_expansion hp hz i j
  have hδeval : MvPolynomial.eval (coordinateShift z j δ) p ≠ 0 :=
    (hz _ (le_coordinateShift z j hδ)).ne'
  have h0eval : MvPolynomial.eval (coordinateShift z j 0) p ≠ 0 := by
    simpa using hz.eval_pos.ne'
  have hrep0 := hrep 0 h0eval
  have hrepδ := hrep δ hδeval
  have hc : Continuous (fun t : ℝ ↦ MvPolynomial.eval (coordinateShift z j t) p) := by
    simpa only [eval_coordinatePolynomial] using (coordinatePolynomial p z j).continuous
  have hlocal : (fun t : ℝ ↦ barrier p i (coordinateShift z j t)) =ᶠ[𝓝 δ]
      (fun t ↦ c + ∑ r ∈ s, a r / (t-r)) := by
    filter_upwards [hc.continuousAt.eventually_ne hδeval] with t ht
    exact hrep t ht
  have hdbarrier := hasDerivAt_barrier_coordinate p z i j δ hδeval
  have hdresidue := hasDerivAt_finite_residues s a id c δ (by
    intro r hr
    exact ne_of_gt ((ha r hr).1.trans_le hδ))
  have hdeq : mixedBarrierDerivative p i j (coordinateShift z j δ) =
      -(∑ r ∈ s, a r / (δ-r)^2) :=
    hdbarrier.unique (hdresidue.congr_of_eventuallyEq hlocal)
  have htangent := finite_residue_tangent_with_constant s a id c 0 δ
    (fun r hr ↦ (ha r hr).2.le) (fun r hr ↦ (ha r hr).1) hδ
  simp only [id_eq, zero_add] at htangent
  rw [hrepδ, hdeq]
  simpa only [coordinateShift_zero, sub_neg_eq_add, mul_neg] using
    (show (c + ∑ r ∈ s, a r / (δ-r)) + δ * (∑ r ∈ s, a r / (δ-r)^2) ≤
        barrier p i (coordinateShift z j 0) by rw [hrep0]; exact htangent)

end NoEpsilon.MSSCrossBarrier
