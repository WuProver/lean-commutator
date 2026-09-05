import CommutatorTheorem.Epsilon.BTFellExactDescartes

/-!
# Parity invariance for root-disjoint Fell pencils

This module records the coefficient and root-count invariants of an affine
real-rooted pencil on an interval where a fixed threshold is not crossed.
-/

open scoped Polynomial

namespace CommutatorTheorem.BTFellCountParity

open Polynomial
open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTFellThreshold
open CommutatorTheorem.BTFellCrossGap

/-- Taylor translation commutes with the convex affine pencil. -/
theorem taylor_convex (p q : ℝ[X]) (t x : ℝ) :
    (t • p + (1 - t) • q).taylor x =
      t • p.taylor x + (1 - t) • q.taylor x := by
  simp only [map_add, map_smul]

/-- Equal nonzero evaluation signs force equal parity of the exact
right-half-line root counts. -/
theorem even_rootsGTCount_iff_of_eval_mul_pos
    {p q : ℝ[X]} (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpreal : RealRooted p) (hqreal : RealRooted q) {x : ℝ}
    (hpx : ¬ p.IsRoot x) (hqx : ¬ q.IsRoot x)
    (hsign : 0 < p.eval x * q.eval x) :
    Even (rootsGTCount p x) ↔ Even (rootsGTCount q x) := by
  have hp := signed_eval_pos_by_roots_gt_count hpmonic hpreal hpx
  have hq := signed_eval_pos_by_roots_gt_count hqmonic hqreal hqx
  have hp' : 0 < (-1 : ℝ) ^ rootsGTCount p x * p.eval x := by
    simpa [rootsGTCount, Multiset.countP_eq_card_filter] using hp
  have hq' : 0 < (-1 : ℝ) ^ rootsGTCount q x * q.eval x := by
    simpa [rootsGTCount, Multiset.countP_eq_card_filter] using hq
  have hpows : (-1 : ℝ) ^ rootsGTCount p x =
      (-1 : ℝ) ^ rootsGTCount q x := by
    rcases neg_one_pow_eq_or ℝ (rootsGTCount p x) with hpone | hpneg <;>
      rcases neg_one_pow_eq_or ℝ (rootsGTCount q x) with hqone | hqneg
    · rw [hpone, hqone]
    · exfalso
      rw [hpone] at hp'
      rw [hqneg] at hq'
      nlinarith
    · exfalso
      rw [hpneg] at hp'
      rw [hqone] at hq'
      nlinarith
    · rw [hpneg, hqneg]
  constructor
  · intro heven
    apply (neg_one_pow_eq_one_iff_even (R := ℝ) (by norm_num)).mp
    rw [← hpows, heven.neg_one_pow]
  · intro heven
    apply (neg_one_pow_eq_one_iff_even (R := ℝ) (by norm_num)).mp
    rw [hpows, heven.neg_one_pow]

/-- In a root-disjoint pencil, absence of a threshold crossing between two
parameters preserves the parity of the right-half-line root count. -/
theorem even_rootsGTCount_iff_of_no_crossing
    {p q : ℝ[X]}
    (hdisjoint : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    {s t x : ℝ} (hst : s < t)
    (hsmonic : (s • p + (1 - s) • q).Monic)
    (htmonic : (t • p + (1 - t) • q).Monic)
    (hsreal : RealRooted (s • p + (1 - s) • q))
    (htreal : RealRooted (t • p + (1 - t) • q))
    (hsroot : ¬ (s • p + (1 - s) • q).IsRoot x)
    (htroot : ¬ (t • p + (1 - t) • q).IsRoot x)
    (hcross : ¬ ∃ u : ℝ, s < u ∧ u < t ∧
      (u • p + (1 - u) • q).IsRoot x) :
    Even (rootsGTCount (s • p + (1 - s) • q) x) ↔
      Even (rootsGTCount (t • p + (1 - t) • q) x) := by
  apply even_rootsGTCount_iff_of_eval_mul_pos hsmonic htmonic
    hsreal htreal hsroot htroot
  exact (eval_mul_eval_pos_iff_no_convex_isRoot_between
    hdisjoint hst hsroot htroot).2 hcross

end CommutatorTheorem.BTFellCountParity
