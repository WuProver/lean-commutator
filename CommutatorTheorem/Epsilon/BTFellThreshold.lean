import CommutatorTheorem.Epsilon.BTFellPair

/-!
# Threshold crossings in a root-disjoint affine polynomial pencil

This module isolates the algebraic part of the half-line root-count argument
for the Pair Fell converse.  If the endpoint polynomials have no common real
root, a fixed threshold can be a root of at most one member of their affine
pencil.  The remaining analytic step is to show that crossing such an isolated
parameter changes the number of roots to the right by at most one.
-/

open scoped Polynomial

namespace CommutatorTheorem.BTFellThreshold

open Polynomial
open CommutatorTheorem.BTFellPair

/-- Evaluation of the affine pencil, written so that its slope in the
parameter is explicit. -/
theorem eval_convex_eq
    (p q : ℝ[X]) (t x : ℝ) :
    (t • p + (1 - t) • q).eval x =
      t * (p.eval x - q.eval x) + q.eval x := by
  simp only [eval_add, eval_smul, smul_eq_mul]
  ring

/-- For a root-disjoint pair, the parameter at which a fixed threshold is a
root of the affine pencil is unique. -/
theorem convex_isRoot_parameter_injective
    {p q : ℝ[X]}
    (hdisjoint : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    {s t x : ℝ}
    (hs : (s • p + (1 - s) • q).IsRoot x)
    (ht : (t • p + (1 - t) • q).IsRoot x) :
    s = t := by
  by_contra hst
  exact hdisjoint x (endpoints_isRoot_of_two_convex_isRoot hst hs ht)

/-- Equivalently, the set of pencil parameters having a prescribed real root
is a subsingleton. -/
theorem subsingleton_setOf_convex_isRoot
    {p q : ℝ[X]}
    (hdisjoint : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    (x : ℝ) :
    Set.Subsingleton
      {t : ℝ | (t • p + (1 - t) • q).IsRoot x} := by
  intro s hs t ht
  exact convex_isRoot_parameter_injective hdisjoint hs ht

/-- At a crossing of a root-disjoint pencil, the scalar affine evaluation
has nonzero slope. -/
theorem eval_sub_ne_zero_of_convex_isRoot
    {p q : ℝ[X]}
    (hdisjoint : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    {t x : ℝ}
    (ht : (t • p + (1 - t) • q).IsRoot x) :
    p.eval x - q.eval x ≠ 0 := by
  intro hslope
  have heq : p.eval x = q.eval x := sub_eq_zero.mp hslope
  have hzero : q.eval x = 0 := by
    rw [IsRoot, eval_convex_eq] at ht
    rw [hslope, mul_zero, zero_add] at ht
    exact ht
  apply hdisjoint x
  rw [IsRoot, IsRoot, heq]
  exact ⟨hzero, hzero⟩

/-- The unique crossing parameter has the expected quotient formula. -/
theorem parameter_eq_of_convex_isRoot
    {p q : ℝ[X]} {t x : ℝ}
    (hslope : p.eval x - q.eval x ≠ 0)
    (ht : (t • p + (1 - t) • q).IsRoot x) :
    t = -q.eval x / (p.eval x - q.eval x) := by
  rw [IsRoot, eval_convex_eq] at ht
  apply (eq_div_iff hslope).2
  linarith

/-- Once `x` is a root at parameter `t₀`, evaluation at every other
parameter is the parameter displacement times the nonzero pencil slope. -/
theorem eval_convex_eq_sub_mul_of_isRoot
    {p q : ℝ[X]} {t₀ x : ℝ}
    (hroot : (t₀ • p + (1 - t₀) • q).IsRoot x)
    (t : ℝ) :
    (t • p + (1 - t) • q).eval x =
      (t - t₀) * (p.eval x - q.eval x) := by
  rw [IsRoot, eval_convex_eq] at hroot
  rw [eval_convex_eq]
  linarith

/-- Evaluation at a fixed threshold changes sign when the parameter passes
through its unique crossing. -/
theorem eval_convex_mul_eval_convex_neg_of_crossing
    {p q : ℝ[X]}
    (hdisjoint : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    {s t t₀ x : ℝ} (hs : s < t₀) (ht : t₀ < t)
    (hroot : (t₀ • p + (1 - t₀) • q).IsRoot x) :
    (s • p + (1 - s) • q).eval x *
        (t • p + (1 - t) • q).eval x < 0 := by
  rw [eval_convex_eq_sub_mul_of_isRoot hroot,
    eval_convex_eq_sub_mul_of_isRoot hroot]
  have hslope := eval_sub_ne_zero_of_convex_isRoot hdisjoint hroot
  have hsneg : s - t₀ < 0 := sub_neg.mpr hs
  have htpos : 0 < t - t₀ := sub_pos.mpr ht
  have hsquare : 0 < (p.eval x - q.eval x) ^ 2 := sq_pos_of_ne_zero hslope
  calc
    (s - t₀) * (p.eval x - q.eval x) *
        ((t - t₀) * (p.eval x - q.eval x)) =
      ((s - t₀) * (t - t₀)) * (p.eval x - q.eval x) ^ 2 := by ring
    _ < 0 := mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos hsneg htpos) hsquare

/-- Conversely, opposite endpoint signs force a threshold crossing at a
strictly intermediate parameter.  This is the scalar intermediate-value
step; no real-rootedness hypothesis is needed. -/
theorem exists_convex_isRoot_between_of_eval_mul_eval_neg
    {p q : ℝ[X]} {s t x : ℝ} (hst : s < t)
    (hneg :
      (s • p + (1 - s) • q).eval x *
          (t • p + (1 - t) • q).eval x < 0) :
    ∃ u : ℝ, s < u ∧ u < t ∧
      (u • p + (1 - u) • q).IsRoot x := by
  let f : ℝ → ℝ := fun u ↦ (u • p + (1 - u) • q).eval x
  have hf : Continuous f := by
    have hf_eq : f = fun u ↦
        u * (p.eval x - q.eval x) + q.eval x := by
      funext u
      exact eval_convex_eq p q u x
    rw [hf_eq]
    fun_prop
  rcases (mul_neg_iff.mp hneg) with ⟨hfs, hft⟩ | ⟨hfs, hft⟩
  · have hmem : (0 : ℝ) ∈ Set.Icc (f t) (f s) := ⟨hft.le, hfs.le⟩
    obtain ⟨u, huIcc, huzero⟩ :=
      intermediate_value_Icc' hst.le hf.continuousOn hmem
    refine ⟨u, ?_, ?_, ?_⟩
    · exact lt_of_le_of_ne huIcc.1 (fun hus ↦ by
        subst u
        simp only [f] at huzero
        linarith)
    · exact lt_of_le_of_ne huIcc.2 (fun hut ↦ by
        subst u
        simp only [f] at huzero
        linarith)
    · rw [IsRoot]
      simpa [f] using huzero
  · have hmem : (0 : ℝ) ∈ Set.Icc (f s) (f t) := ⟨hfs.le, hft.le⟩
    obtain ⟨u, huIcc, huzero⟩ :=
      intermediate_value_Icc hst.le hf.continuousOn hmem
    refine ⟨u, ?_, ?_, ?_⟩
    · exact lt_of_le_of_ne huIcc.1 (fun hus ↦ by
        subst u
        simp only [f] at huzero
        linarith)
    · exact lt_of_le_of_ne huIcc.2 (fun hut ↦ by
        subst u
        simp only [f] at huzero
        linarith)
    · rw [IsRoot]
      simpa [f] using huzero

/-- For a root-disjoint pencil, opposite signs at two parameters are exactly
the assertion that the fixed threshold is crossed strictly between them. -/
theorem eval_mul_eval_neg_iff_exists_convex_isRoot_between
    {p q : ℝ[X]}
    (hdisjoint : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    {s t x : ℝ} (hst : s < t) :
    (s • p + (1 - s) • q).eval x *
          (t • p + (1 - t) • q).eval x < 0 ↔
      ∃ u : ℝ, s < u ∧ u < t ∧
        (u • p + (1 - u) • q).IsRoot x := by
  constructor
  · exact exists_convex_isRoot_between_of_eval_mul_eval_neg hst
  · rintro ⟨u, hsu, hut, hroot⟩
    exact eval_convex_mul_eval_convex_neg_of_crossing
      hdisjoint hsu hut hroot

/-- Thus equal endpoint signs are equivalent to absence of a crossing in the
open parameter interval. -/
theorem eval_mul_eval_pos_iff_no_convex_isRoot_between
    {p q : ℝ[X]}
    (hdisjoint : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    {s t x : ℝ} (hst : s < t)
    (hsroot : ¬ (s • p + (1 - s) • q).IsRoot x)
    (htroot : ¬ (t • p + (1 - t) • q).IsRoot x) :
    0 < (s • p + (1 - s) • q).eval x *
          (t • p + (1 - t) • q).eval x ↔
      ¬ ∃ u : ℝ, s < u ∧ u < t ∧
        (u • p + (1 - u) • q).IsRoot x := by
  let fs := (s • p + (1 - s) • q).eval x
  let ft := (t • p + (1 - t) • q).eval x
  have hfs : fs ≠ 0 := by
    simpa [fs, IsRoot] using hsroot
  have hft : ft ≠ 0 := by
    simpa [ft, IsRoot] using htroot
  rw [← eval_mul_eval_neg_iff_exists_convex_isRoot_between
    hdisjoint hst]
  change 0 < fs * ft ↔ ¬ fs * ft < 0
  have hprod : fs * ft ≠ 0 := mul_ne_zero hfs hft
  constructor
  · exact not_lt_of_ge ∘ le_of_lt
  · intro hnneg
    exact lt_of_le_of_ne (le_of_not_gt hnneg) (Ne.symm hprod)

end CommutatorTheorem.BTFellThreshold
