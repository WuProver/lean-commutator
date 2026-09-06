import Mathlib.LinearAlgebra.Lagrange
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-!
# Simple-pole partial fractions for the MSS barrier

This file proves the algebraic expansion without any sign or stability assumptions.
The analytic argument can then establish nonnegative residues separately.
-/

open scoped BigOperators

namespace NoEpsilon.MSSPartialFractions

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

theorem splits_eq_leadingCoeff_mul_nodal (h : F[X]) (hsplit : h.Splits)
    (hsep : h.Separable) :
    h = C h.leadingCoeff * Lagrange.nodal h.roots.toFinset id := by
  calc
    h = C h.leadingCoeff * (h.roots.map (fun x ↦ X - C x)).prod := hsplit.eq_prod_roots
    _ = C h.leadingCoeff * Lagrange.nodal h.roots.toFinset id := by
      congr 1
      change (h.roots.map (fun x ↦ X - C x)).prod =
        (h.roots.toFinset.val.map (fun x ↦ X - C x)).prod
      rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (nodup_roots hsep)]

/-- A proper rational function with split simple denominator has the usual residue expansion. -/
theorem partial_fractions_of_degree_lt (g h : F[X]) (h0 : h ≠ 0)
    (hsplit : h.Splits) (hsep : h.Separable) (hdeg : g.degree < h.degree)
    (x : F) (hx : h.eval x ≠ 0) :
    g.eval x / h.eval x =
      ∑ r ∈ h.roots.toFinset, (g.eval r / h.derivative.eval r) / (x - r) := by
  let s := h.roots.toFinset
  let H := Lagrange.nodal s (id : F → F)
  have hfactor : h = C h.leadingCoeff * H := splits_eq_leadingCoeff_mul_nodal h hsplit hsep
  have hlead : h.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr h0
  have hcard : h.degree = s.card := by
    rw [hsplit.degree_eq_card_roots h0]
    rw [show s.card = h.roots.card from Multiset.toFinset_card_of_nodup (nodup_roots hsep)]
  have hg : g = Lagrange.interpolate s id (fun r ↦ g.eval r) :=
    Lagrange.eq_interpolate (fun _ _ _ _ h ↦ h) (hcard ▸ hdeg)
  have hnodes (r : F) (hr : r ∈ s) : x ≠ r := by
    intro hxr
    subst r
    exact hx ((mem_roots h0).mp (Multiset.mem_toFinset.mp hr))
  have hinterp := Lagrange.eval_interpolate_not_at_node (v := id) (fun r ↦ g.eval r) hnodes
  rw [← hg] at hinterp
  simp only [id_eq] at hinterp
  have heval : h.eval x = h.leadingCoeff * H.eval x := by
    have he := congrArg (Polynomial.eval x) hfactor
    simpa only [eval_mul, eval_C] using he
  have hH : H.eval x ≠ 0 := by
    intro he
    rw [heval, he, mul_zero] at hx
    exact hx rfl
  have hder (r : F) : h.derivative.eval r = h.leadingCoeff * H.derivative.eval r := by
    have he := congrArg (fun p : F[X] ↦ p.derivative.eval r) hfactor
    simpa only [derivative_C_mul, eval_mul, eval_C] using he
  calc
    g.eval x / h.eval x =
        (∑ r ∈ s, Lagrange.nodalWeight s id r * (x - r)⁻¹ * g.eval r) / h.leadingCoeff := by
      rw [hinterp, heval]
      change (H.eval x * _) / (h.leadingCoeff * H.eval x) = _
      field_simp
    _ = ∑ r ∈ s, (g.eval r / h.derivative.eval r) / (x - r) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hr, hder]
      dsimp only [H]
      simp only [div_eq_mul_inv, mul_inv_rev, id_eq]
      ring
    _ = _ := rfl


/-- A rational function of degree at most its split simple denominator differs from
its residue sum by a constant. This includes equal degree and constant denominators. -/
theorem partial_fractions_of_natDegree_le (g h : F[X]) (h0 : h ≠ 0)
    (hsplit : h.Splits) (hsep : h.Separable) (hdeg : g.natDegree ≤ h.natDegree) :
    ∃ c : F, ∀ x : F, h.eval x ≠ 0 →
      g.eval x / h.eval x =
        c + ∑ r ∈ h.roots.toFinset, (g.eval r / h.derivative.eval r) / (x - r) := by
  by_cases hlt : g.degree < h.degree
  · refine ⟨0, ?_⟩
    intro x hx
    simpa only [zero_add] using partial_fractions_of_degree_lt g h h0 hsplit hsep hlt x hx
  have hle : g.degree ≤ h.degree := by
    rw [degree_eq_natDegree h0]
    exact degree_le_of_natDegree_le hdeg
  have heq : g.degree = h.degree := le_antisymm hle (le_of_not_gt hlt)
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg, degree_zero] at heq
    exact h0 (degree_eq_bot.mp heq.symm)
  let c : F := g.leadingCoeff / h.leadingCoeff
  have hleadg : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have hleadh : h.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr h0
  have hc : c ≠ 0 := div_ne_zero hleadg hleadh
  let q := g - C c * h
  have hqdeg : q.degree < h.degree := by
    have hdc : (C c * h).degree = h.degree := degree_C_mul hc
    have hlc : g.leadingCoeff = (C c * h).leadingCoeff := by
      rw [leadingCoeff_mul, leadingCoeff_C]
      dsimp [c]
      field_simp
    exact (degree_sub_lt (heq.trans hdc.symm) hg0 hlc).trans_eq heq
  have hqr (r : F) (hr : r ∈ h.roots.toFinset) : q.eval r = g.eval r := by
    have he : h.eval r = 0 := (mem_roots h0).mp (Multiset.mem_toFinset.mp hr)
    simp only [q, eval_sub, eval_mul, eval_C, he, mul_zero, sub_zero]
  refine ⟨c, ?_⟩
  intro x hx
  have hp := partial_fractions_of_degree_lt q h h0 hsplit hsep hqdeg x hx
  calc
    g.eval x / h.eval x = c + q.eval x / h.eval x := by
      simp only [q, eval_sub, eval_mul, eval_C]
      field_simp
      ring
    _ = c + ∑ r ∈ h.roots.toFinset, (q.eval r / h.derivative.eval r) / (x - r) := by rw [hp]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [hqr r hr]

end NoEpsilon.MSSPartialFractions
