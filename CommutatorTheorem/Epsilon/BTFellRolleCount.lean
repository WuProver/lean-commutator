import CommutatorTheorem.Epsilon.BTFellCrossGap
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

/-!
# Rolle bounds for half-line root counts

This module localizes mathlib's multiplicity-sensitive polynomial Rolle
argument to an open right half-line.  It is the order-theoretic bridge between
the root count of a real-rooted polynomial and that of its derivative.
-/

open scoped Polynomial

namespace CommutatorTheorem.BTFellRolleCount

open Polynomial
open CommutatorTheorem.BTFellCrossGap

/-- Strict left- and right-half-line counts never exceed the total multiset
cardinality. -/
theorem countP_lt_add_countP_gt_le_card (s : Multiset ℝ) (b : ℝ) :
    s.countP (· < b) + s.countP (b < ·) ≤ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.countP_cons, Multiset.card_cons]
      rcases lt_trichotomy a b with hab | hab | hab
      · simp [hab, not_lt_of_ge hab.le]
        omega
      · subst a
        simp
        omega
      · simp [hab, not_lt_of_ge hab.le]
        omega

/-- If the threshold is absent, the two strict half-lines partition the
whole multiset. -/
theorem countP_lt_add_countP_gt_eq_card_of_not_mem
    (s : Multiset ℝ) (b : ℝ) (hb : b ∉ s) :
    s.countP (· < b) + s.countP (b < ·) = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have hab : a ≠ b := by
        intro h
        subst a
        exact hb (by simp)
      have hbs : b ∉ s := by
        intro h
        exact hb (by simp [h])
      have ih' := ih hbs
      simp only [Multiset.countP_cons, Multiset.card_cons]
      rcases lt_or_gt_of_ne hab with halt | hbalt
      · simp [halt, not_lt_of_ge halt.le]
        omega
      · simp [hbalt, not_lt_of_ge hbalt.le]
        omega

/-- The two strict half-lines together with the multiplicity at the
threshold partition a multiset. -/
theorem countP_lt_add_count_add_countP_gt_eq_card
    (s : Multiset ℝ) (b : ℝ) :
    s.countP (· < b) + s.count b + s.countP (b < ·) = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.countP_cons, Multiset.count_cons,
        Multiset.card_cons]
      rcases lt_trichotomy a b with hab | hab | hab
      · simp [hab, Ne.symm hab.ne, not_lt_of_ge hab.le]
        omega
      · subst a
        simp
        omega
      · simp [hab, hab.ne, not_lt_of_ge hab.le]
        omega

theorem countP_le_eq_countP_lt_add_count (s : Multiset ℝ) (b : ℝ) :
    s.countP (· ≤ b) = s.countP (· < b) + s.count b := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.countP_cons, Multiset.count_cons]
      rcases lt_trichotomy a b with hab | hab | hab
      · simp [hab, hab.le, Ne.symm hab.ne, ih]
        omega
      · subst a
        simp [ih]
        omega
      · simp [not_le_of_gt hab, not_lt_of_ge hab.le,
          hab.ne, ih]

/-- Between consecutive distinct roots strictly to the right of `x`, Rolle's
theorem supplies a derivative root which is still strictly to the right of
`x`. -/
theorem card_roots_filter_toFinset_le_derivative_diff_succ
    (p : ℝ[X]) (P : ℝ → Prop) [DecidablePred P]
    (hconv : ∀ a b z : ℝ, P a → P b → a < z → z < b → P z) :
    (p.roots.toFinset.filter P).card ≤
      ((p.derivative.roots.toFinset.filter P) \
        (p.roots.toFinset.filter P)).card + 1 := by
  rcases eq_or_ne p.derivative 0 with hp' | hp'
  · rw [eq_C_of_derivative_eq_zero hp', roots_C,
      Multiset.toFinset_zero, Finset.filter_empty, Finset.card_empty]
    exact Nat.zero_le _
  have hp : p ≠ 0 := ne_of_apply_ne derivative (by rwa [derivative_zero])
  refine Finset.card_le_diff_of_interleaved fun a ha b hb hab hba ↦ ?_
  simp only [Finset.mem_filter, Multiset.mem_toFinset] at ha hb
  obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero hab p.continuousOn
    ((mem_roots hp).mp ha.1 |>.trans ((mem_roots hp).mp hb.1).symm)
  refine ⟨z, ?_, hz1⟩
  rw [Finset.mem_filter, Multiset.mem_toFinset]
  refine ⟨(mem_roots hp').mpr ?_, hconv a b z ha.2 hb.2 hz1.1 hz1.2⟩
  · rw [IsRoot, ← p.deriv]
    exact hz2

/-- Multiplicity-sensitive localized Rolle bound: the number of positive
roots of `p` is at most the number of positive roots of `p.derivative` plus
one. -/
theorem roots_countP_le_derivative_succ_of_intervalConvex
    (p : ℝ[X]) (P : ℝ → Prop) [DecidablePred P]
    (hconv : ∀ a b z : ℝ, P a → P b → a < z → z < b → P z) :
    p.roots.countP P ≤ p.derivative.roots.countP P + 1 := by
  let S := p.roots.toFinset.filter P
  let D := p.derivative.roots.toFinset.filter P
  have hS : S.card ≤ (D \ S).card + 1 := by
    simpa [S, D] using
      card_roots_filter_toFinset_le_derivative_diff_succ p P hconv
  have hsum (m : Multiset ℝ) :
      m.countP P = ∑ x ∈ m.toFinset.filter P, m.count x := by
    calc
      m.countP P = (m.filter P).card :=
        Multiset.countP_eq_card_filter (p := P) m
      _ = ∑ x ∈ (m.filter P).toFinset,
          (m.filter P).count x :=
        (Multiset.toFinset_sum_count_eq _).symm
      _ = ∑ x ∈ m.toFinset.filter P, m.count x := by
        apply Finset.sum_congr
        · ext x
          simp
        · intro x hx
          rw [Multiset.count_filter_of_pos]
          exact (Finset.mem_filter.mp hx).2
  calc
    p.roots.countP P = ∑ x ∈ S, p.roots.count x := by
      simpa [S] using hsum p.roots
    _ = ∑ x ∈ S, (p.roots.count x - 1 + 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply (Nat.sub_add_cancel ?_).symm
      rw [Nat.succ_le_iff, Multiset.count_pos]
      exact Multiset.mem_toFinset.mp (Finset.mem_filter.mp hx).1
    _ = (∑ x ∈ S, (p.rootMultiplicity x - 1)) + S.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones,
        count_roots]
    _ ≤ (∑ x ∈ S, p.derivative.rootMultiplicity x) +
          ((D \ S).card + 1) :=
      add_le_add
        (Finset.sum_le_sum fun _ _ ↦
          rootMultiplicity_sub_one_le_derivative_rootMultiplicity p _)
        hS
    _ ≤ (∑ x ∈ S, p.derivative.roots.count x) +
          ((∑ x ∈ D \ S, p.derivative.roots.count x) + 1) := by
      simp only [← count_roots, Finset.card_eq_sum_ones]
      gcongr with x hx
      rw [Nat.succ_le_iff, Multiset.count_pos, ← Multiset.mem_toFinset]
      have hxD : x ∈ D := (Finset.mem_sdiff.mp hx).1
      exact (Finset.mem_filter.mp hxD).1
    _ = p.derivative.roots.countP P + 1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union, hsum p.derivative.roots]
      congr 1
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro x hxUnion hxD
      rw [Multiset.count_eq_zero]
      intro hxroot
      apply hxD
      exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hxroot,
        (Finset.mem_union.mp hxUnion).elim
          (fun hxS ↦ (Finset.mem_filter.mp hxS).2)
          (fun hxD' ↦ (Finset.mem_filter.mp hxD').2)⟩

/-- Right-half-line specialization of localized Rolle. -/
theorem roots_countP_gt_le_derivative_succ (p : ℝ[X]) (b : ℝ) :
    p.roots.countP (b < ·) ≤
      p.derivative.roots.countP (b < ·) + 1 := by
  apply roots_countP_le_derivative_succ_of_intervalConvex
  intro a c z ha hc haz hzc
  exact ha.trans haz

/-- Left-half-line specialization of localized Rolle. -/
theorem roots_countP_lt_le_derivative_succ (p : ℝ[X]) (b : ℝ) :
    p.roots.countP (· < b) ≤
      p.derivative.roots.countP (· < b) + 1 := by
  apply roots_countP_le_derivative_succ_of_intervalConvex
  intro a c z ha hc haz hzc
  exact hzc.trans hc

/-- The positive-root specialization. -/
theorem roots_countP_pos_le_derivative_succ (p : ℝ[X]) :
    p.roots.countP (0 < ·) ≤
      p.derivative.roots.countP (0 < ·) + 1 :=
  roots_countP_gt_le_derivative_succ p 0

/-- In the notation used by the Fell reduction, differentiation can remove
at most one root from any open right half-line. -/
theorem rootsGTCount_le_derivative_succ (p : ℝ[X]) (b : ℝ) :
    rootsGTCount p b ≤ rootsGTCount p.derivative b + 1 := by
  simpa [rootsGTCount, Multiset.countP_eq_card_filter] using
    roots_countP_gt_le_derivative_succ p b

/-- For a nonconstant monic real-rooted polynomial, at a threshold which is
not a root, the derivative has either the same number of roots to the right
or one fewer.  This is the two-sided localized Rolle count. -/
theorem derivative_rootsGTCount_le
    {p : ℝ[X]} {d : ℕ} (hd : 0 < d)
    (hmonic : p.Monic) (hreal : CommutatorTheorem.RealRooted p)
    (hdegree : p.natDegree = d) {b : ℝ} (hb : ¬ p.IsRoot b) :
    rootsGTCount p.derivative b ≤ rootsGTCount p b := by
  let Lp := p.roots.countP (· < b)
  let Np := rootsGTCount p b
  let Ld := p.derivative.roots.countP (· < b)
  let Nd := rootsGTCount p.derivative b
  have hbmem : b ∉ p.roots := by
    intro hmem
    exact hb ((mem_roots hmonic.ne_zero).mp hmem)
  have hpPart : Lp + Np = d := by
    have hpart := countP_lt_add_countP_gt_eq_card_of_not_mem p.roots b hbmem
    dsimp [Lp, Np]
    rw [hreal.natDegree_eq_card_roots.symm, hdegree] at hpart
    simpa [rootsGTCount, Multiset.countP_eq_card_filter] using hpart
  have hpdegpos : 0 < p.natDegree := by omega
  have hdreal : CommutatorTheorem.RealRooted p.derivative :=
    CommutatorTheorem.BTFellPair.realRooted_derivative hreal hpdegpos
  have hddegree : p.derivative.natDegree = d - 1 := by
    apply (degree_eq_iff_natDegree_eq ?_).mp
    · simpa [hdegree] using degree_derivative_eq p hpdegpos
    · intro hzero
      have hdegzero : p.derivative.degree = ⊥ := by simp [hzero]
      rw [degree_derivative_eq p hpdegpos, hdegree] at hdegzero
      simp at hdegzero
  have hdPart : Ld + Nd ≤ d - 1 := by
    have hpart := countP_lt_add_countP_gt_le_card p.derivative.roots b
    dsimp [Ld, Nd]
    rw [hdreal.natDegree_eq_card_roots.symm, hddegree] at hpart
    simpa [rootsGTCount, Multiset.countP_eq_card_filter] using hpart
  have hleft : Lp ≤ Ld + 1 := by
    dsimp [Lp, Ld]
    exact roots_countP_lt_le_derivative_succ p b
  omega

/-- The derivative never has more roots on a strict right half-line than a
nonconstant real-rooted polynomial, even when the threshold itself is a
multiple root. -/
theorem derivative_rootsGTCount_le_unconditional
    {p : ℝ[X]} {d : ℕ} (hd : 0 < d)
    (hmonic : p.Monic) (hreal : CommutatorTheorem.RealRooted p)
    (hdegree : p.natDegree = d) (b : ℝ) :
    rootsGTCount p.derivative b ≤ rootsGTCount p b := by
  by_cases hb : p.IsRoot b
  · let Lp := p.roots.countP (· < b)
    let Np := rootsGTCount p b
    let mp := p.roots.count b
    let Ld := p.derivative.roots.countP (· < b)
    let Nd := rootsGTCount p.derivative b
    let md := p.derivative.roots.count b
    have hpPart : Lp + mp + Np = d := by
      have hpart := countP_lt_add_count_add_countP_gt_eq_card p.roots b
      dsimp [Lp, mp, Np]
      rw [hreal.natDegree_eq_card_roots.symm, hdegree] at hpart
      simpa [rootsGTCount, Multiset.countP_eq_card_filter] using hpart
    have hpdegpos : 0 < p.natDegree := by omega
    have hdreal : CommutatorTheorem.RealRooted p.derivative :=
      CommutatorTheorem.BTFellPair.realRooted_derivative hreal hpdegpos
    have hddegree : p.derivative.natDegree = d - 1 := by
      apply (degree_eq_iff_natDegree_eq ?_).mp
      · simpa [hdegree] using degree_derivative_eq p hpdegpos
      · intro hzero
        have hdegzero : p.derivative.degree = ⊥ := by simp [hzero]
        rw [degree_derivative_eq p hpdegpos, hdegree] at hdegzero
        simp at hdegzero
    have hdPart : Ld + md + Nd = d - 1 := by
      have hpart := countP_lt_add_count_add_countP_gt_eq_card
        p.derivative.roots b
      dsimp [Ld, md, Nd]
      rw [hdreal.natDegree_eq_card_roots.symm, hddegree] at hpart
      simpa [rootsGTCount, Multiset.countP_eq_card_filter] using hpart
    have hclosed := roots_countP_le_derivative_succ_of_intervalConvex
      p (· ≤ b) (by
        intro a c z ha hc haz hzc
        exact hzc.le.trans hc)
    rw [countP_le_eq_countP_lt_add_count,
      countP_le_eq_countP_lt_add_count] at hclosed
    have hmd : md = mp - 1 := by
      dsimp [md, mp]
      simpa only [count_roots] using derivative_rootMultiplicity_of_root hb
    omega
  · exact derivative_rootsGTCount_le hd hmonic hreal hdegree hb
/-
  let Lp := p.roots.countP (· < b)
  let Np := rootsGTCount p b
  let mp := p.roots.count b
  let Ld := p.derivative.roots.countP (· < b)
  let Nd := rootsGTCount p.derivative b
  let md := p.derivative.roots.count b
  have hpPart : Lp + mp + Np = d := by
    have hpart := countP_lt_add_count_add_countP_gt_eq_card p.roots b
    dsimp [Lp, mp, Np]
    rw [hreal.natDegree_eq_card_roots.symm, hdegree] at hpart
    simpa [rootsGTCount, Multiset.countP_eq_card_filter] using hpart
  have hpdegpos : 0 < p.natDegree := by omega
  have hdreal : CommutatorTheorem.RealRooted p.derivative :=
    CommutatorTheorem.BTFellPair.realRooted_derivative hreal hpdegpos
  have hddegree : p.derivative.natDegree = d - 1 := by
    apply (degree_eq_iff_natDegree_eq ?_).mp
    · simpa [hdegree] using degree_derivative_eq p hpdegpos
    · intro hzero
      have hdegzero : p.derivative.degree = ⊥ := by simp [hzero]
      rw [degree_derivative_eq p hpdegpos, hdegree] at hdegzero
      simp at hdegzero
  have hdPart : Ld + md + Nd = d - 1 := by
    have hpart := countP_lt_add_count_add_countP_gt_eq_card
      p.derivative.roots b
    dsimp [Ld, md, Nd]
    rw [hdreal.natDegree_eq_card_roots.symm, hddegree] at hpart
    simpa [rootsGTCount, Multiset.countP_eq_card_filter] using hpart
  have hleft : Lp ≤ Ld + 1 := by
    dsimp [Lp, Ld]
    exact roots_countP_lt_le_derivative_succ p b
  have hmult : mp - 1 ≤ md := by
    dsimp [mp, md]
    simpa only [count_roots] using
      rootMultiplicity_sub_one_le_derivative_rootMultiplicity p b
  omega
-/

end CommutatorTheorem.BTFellRolleCount
