import CommutatorTheorem.Epsilon.BTFellThreshold

/-!
# A finite cross-gap interface for the Pair Fell converse

For two sorted root lists of the same positive length, a common interlacing
list exists exactly when each left endpoint of either list lies below the
next endpoint of the other list.  This file packages the constructive
direction needed by the root-disjoint Pair Fell core.  The common list takes
the maximum of the two left endpoints in every gap.
-/

open scoped Polynomial

namespace CommutatorTheorem.BTFellCrossGap

open Polynomial
open CommutatorTheorem
open CommutatorTheorem.BTFellPair

/-- The two cross inequalities which characterize overlap of the `k`-th
root gaps of two equal-length root lists. -/
def CrossGapCompatible (u v : List ℝ) : Prop :=
  u.length = v.length ∧
    ∀ (k : ℕ) (hku : k + 1 < u.length) (hkv : k + 1 < v.length),
      u.get ⟨k, by omega⟩ ≤ v.get ⟨k + 1, hkv⟩ ∧
        v.get ⟨k, by omega⟩ ≤ u.get ⟨k + 1, hku⟩

/-- Number of roots, with multiplicity, strictly to the right of `x`. -/
noncomputable def rootsGTCount (p : ℝ[X]) (x : ℝ) : ℕ :=
  (p.roots.filter fun r ↦ x < r).card

theorem rootsGTCount_eq_sorted_filter_length (p : ℝ[X]) (x : ℝ) :
    rootsGTCount p x =
      ((p.roots.sort (· ≤ ·)).filter fun r ↦ x < r).length := by
  unfold rootsGTCount
  calc
    (Multiset.filter (fun r ↦ x < r) p.roots).card =
        (Multiset.filter (fun r ↦ x < r)
          (↑(p.roots.sort (· ≤ ·)) : Multiset ℝ)).card := by
      rw [Multiset.sort_eq]
    _ = ((p.roots.sort (· ≤ ·)).filter fun r ↦ x < r).length := by
      rw [Multiset.filter_coe]
      rfl

/-- If the `k`-th entry of a sorted list is strictly to the right of `x`,
then at least the suffix beginning at `k` is to the right of `x`. -/
theorem length_sub_le_filter_length_of_lt_get
    {l : List ℝ} (hsorted : l.Pairwise (· ≤ ·))
    {x : ℝ} {k : ℕ} (hk : k < l.length)
    (hx : x < l.get ⟨k, hk⟩) :
    l.length - k ≤ (l.filter fun r ↦ x < r).length := by
  have hsuffix : (l.drop k).filter (fun r ↦ x < r) = l.drop k := by
    apply List.filter_eq_self.mpr
    intro y hy
    apply decide_eq_true
    rw [List.mem_iff_getElem] at hy
    obtain ⟨j, hj, hy⟩ := hy
    subst y
    have hjOrig : k + j < l.length := by
      simp only [List.length_drop] at hj
      omega
    rw [List.getElem_drop]
    exact hx.trans_le (hsorted.rel_get_of_le
      (show (⟨k, hk⟩ : Fin l.length) ≤ ⟨k + j, hjOrig⟩ by
        exact Fin.mk_le_mk.mpr (Nat.le_add_right k j)))
  calc
    l.length - k = (l.drop k).length := (List.length_drop ..).symm
    _ = ((l.drop k).filter fun r ↦ x < r).length :=
      congrArg List.length hsuffix.symm
    _ ≤ (l.filter fun r ↦ x < r).length :=
      ((List.drop_sublist k l).filter (fun r ↦ x < r)).length_le

/-- If the `k`-th entry of a sorted list lies strictly to the left of `x`,
then only the suffix after `k` can contribute roots to the right of `x`. -/
theorem filter_length_le_length_sub_succ_of_get_lt
    {l : List ℝ} (hsorted : l.Pairwise (· ≤ ·))
    {x : ℝ} {k : ℕ} (hk : k < l.length)
    (hx : l.get ⟨k, hk⟩ < x) :
    (l.filter fun r ↦ x < r).length ≤ l.length - (k + 1) := by
  have hprefix : (l.take (k + 1)).filter (fun r ↦ x < r) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro y hy hydec
    rw [List.mem_iff_getElem] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    simp only [List.length_take] at hj
    have hjOrig : j < l.length := by omega
    have hylt : x < l.get ⟨j, hjOrig⟩ := by
      apply of_decide_eq_true
      simpa only [List.getElem_take] using hydec
    have hle : l.get ⟨j, by omega⟩ ≤ l.get ⟨k, hk⟩ :=
      hsorted.rel_get_of_le (Fin.mk_le_mk.mpr (by omega))
    exact not_lt_of_ge (hle.trans hx.le) hylt
  have hdecomp :
      (l.filter fun r ↦ x < r) =
        ((l.drop (k + 1)).filter fun r ↦ x < r) := by
    calc
      (l.filter fun r ↦ x < r) =
          ((l.take (k + 1) ++ l.drop (k + 1)).filter fun r ↦ x < r) := by
        rw [List.take_append_drop]
      _ = ((l.drop (k + 1)).filter fun r ↦ x < r) := by
        rw [List.filter_append, hprefix, List.nil_append]
  rw [hdecomp]
  simpa only [List.length_drop] using
    List.length_filter_le (fun r : ℝ ↦ x < r) (l.drop (k + 1))

/-- At every threshold, the endpoint root counts differ by at most one. -/
def RootsGTCountBalanced (p q : ℝ[X]) : Prop :=
  ∀ x : ℝ,
    rootsGTCount p x ≤ rootsGTCount q x + 1 ∧
      rootsGTCount q x ≤ rootsGTCount p x + 1

/-- Half-line root-count balance implies all cross-gap inequalities.  This
is the finite order-statistics step behind the analytic Pair Fell converse. -/
theorem crossGapCompatible_of_rootsGTCountBalanced
    {p q : ℝ[X]} {d : ℕ}
    (hpsplits : RealRooted p) (hqsplits : RealRooted q)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    (hbalance : RootsGTCountBalanced p q) :
    CrossGapCompatible
      (p.roots.sort (· ≤ ·)) (q.roots.sort (· ≤ ·)) := by
  let up := p.roots.sort (· ≤ ·)
  let uq := q.roots.sort (· ≤ ·)
  have hup : up.length = d := by
    calc
      up.length = p.roots.card := by simp [up]
      _ = p.natDegree := hpsplits.natDegree_eq_card_roots.symm
      _ = d := hpdegree
  have huq : uq.length = d := by
    calc
      uq.length = q.roots.card := by simp [uq]
      _ = q.natDegree := hqsplits.natDegree_eq_card_roots.symm
      _ = d := hqdegree
  have hupsorted : up.Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort (s := p.roots) (r := (· ≤ ·))
  have huqsorted : uq.Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort (s := q.roots) (r := (· ≤ ·))
  constructor
  · change up.length = uq.length
    omega
  · intro k hku hkv
    change k + 1 < up.length at hku
    change k + 1 < uq.length at hkv
    change
      up.get ⟨k, by omega⟩ ≤ uq.get ⟨k + 1, hkv⟩ ∧
        uq.get ⟨k, by omega⟩ ≤ up.get ⟨k + 1, hku⟩
    have hkD : k + 1 < d := by omega
    constructor
    · by_contra hnot
      have hsep : uq.get ⟨k + 1, hkv⟩ < up.get ⟨k, by omega⟩ :=
        lt_of_not_ge hnot
      let a := uq.get ⟨k + 1, hkv⟩
      let b := up.get ⟨k, by omega⟩
      have hab : a < b := by simpa [a, b] using hsep
      let x := (a + b) / 2
      have hqx : uq.get ⟨k + 1, hkv⟩ < x := by
        change a < x
        dsimp [x]
        linarith
      have hxp : x < up.get ⟨k, by omega⟩ := by
        change x < b
        dsimp [x]
        linarith
      have hpLower : d - k ≤ rootsGTCount p x := by
        rw [rootsGTCount_eq_sorted_filter_length]
        change d - k ≤ (up.filter fun r ↦ x < r).length
        rw [← hup]
        exact length_sub_le_filter_length_of_lt_get
          hupsorted (by omega) hxp
      have hqUpper : rootsGTCount q x ≤ d - (k + 2) := by
        rw [rootsGTCount_eq_sorted_filter_length]
        change (uq.filter fun r ↦ x < r).length ≤ d - (k + 2)
        rw [← huq]
        simpa [Nat.add_assoc] using
          filter_length_le_length_sub_succ_of_get_lt
            huqsorted hkv hqx
      have hbal := (hbalance x).1
      omega
    · by_contra hnot
      have hsep : up.get ⟨k + 1, hku⟩ < uq.get ⟨k, by omega⟩ :=
        lt_of_not_ge hnot
      let a := up.get ⟨k + 1, hku⟩
      let b := uq.get ⟨k, by omega⟩
      have hab : a < b := by simpa [a, b] using hsep
      let x := (a + b) / 2
      have hpx : up.get ⟨k + 1, hku⟩ < x := by
        change a < x
        dsimp [x]
        linarith
      have hxq : x < uq.get ⟨k, by omega⟩ := by
        change x < b
        dsimp [x]
        linarith
      have hqLower : d - k ≤ rootsGTCount q x := by
        rw [rootsGTCount_eq_sorted_filter_length]
        change d - k ≤ (uq.filter fun r ↦ x < r).length
        rw [← huq]
        exact length_sub_le_filter_length_of_lt_get
          huqsorted (by omega) hxq
      have hpUpper : rootsGTCount p x ≤ d - (k + 2) := by
        rw [rootsGTCount_eq_sorted_filter_length]
        change (up.filter fun r ↦ x < r).length ≤ d - (k + 2)
        rw [← hup]
        simpa [Nat.add_assoc] using
          filter_length_le_length_sub_succ_of_get_lt
            hupsorted hku hpx
      have hbal := (hbalance x).2
      omega

/-- The canonical common interlacing list: in the `k`-th gap, take the
larger of the two left endpoints. -/
noncomputable def crossGapList (u v : List ℝ) (d : ℕ)
    (hu : u.length = d) (hv : v.length = d) : List ℝ :=
  List.ofFn (fun k : Fin (d - 1) ↦
    max (u.get ⟨k, by rw [hu]; omega⟩)
      (v.get ⟨k, by rw [hv]; omega⟩))

@[simp] theorem crossGapList_length (u v : List ℝ) (d : ℕ)
    (hu : u.length = d) (hv : v.length = d) :
    (crossGapList u v d hu hv).length = d - 1 := by
  simp [crossGapList]

/-- Any common interlacing list forces the cross-gap inequalities. -/
theorem crossGapCompatible_of_common_listsInterlace
    {lower u v : List ℝ}
    (hu : ListsInterlace lower u) (hv : ListsInterlace lower v) :
    CrossGapCompatible u v := by
  obtain ⟨hulen, huEntries⟩ := hu
  obtain ⟨hvlen, hvEntries⟩ := hv
  constructor
  · omega
  · intro k hku hkv
    have hkLower : k < lower.length := by omega
    exact ⟨(huEntries k hkLower).1.trans (hvEntries k hkLower).2,
      (hvEntries k hkLower).1.trans (huEntries k hkLower).2⟩

/-- Cross-gap compatibility constructs a single sorted list interlacing
both input lists. -/
theorem exists_common_listsInterlace_of_crossGapCompatible
    (u v : List ℝ) (d : ℕ) (hd : 0 < d)
    (hu : u.length = d) (hv : v.length = d)
    (husorted : u.Pairwise (· ≤ ·))
    (hvsorted : v.Pairwise (· ≤ ·))
    (hcross : CrossGapCompatible u v) :
    ∃ lower : List ℝ,
      lower.Pairwise (· ≤ ·) ∧
        ListsInterlace lower u ∧ ListsInterlace lower v := by
  let lower := crossGapList u v d hu hv
  have hlower : lower.length = d - 1 := by
    simp [lower]
  have hlowerSorted : lower.Pairwise (· ≤ ·) := by
    rw [List.pairwise_iff_getElem]
    intro k l hk hl hkl
    have hk' : k < d - 1 := by simpa [hlower] using hk
    have hl' : l < d - 1 := by simpa [hlower] using hl
    have hul : u.get ⟨k, by rw [hu]; omega⟩ ≤
        u.get ⟨l, by rw [hu]; omega⟩ :=
      husorted.rel_get_of_le hkl.le
    have hvl : v.get ⟨k, by rw [hv]; omega⟩ ≤
        v.get ⟨l, by rw [hv]; omega⟩ :=
      hvsorted.rel_get_of_le hkl.le
    change lower[k] ≤ lower[l]
    simp only [lower, crossGapList, List.getElem_ofFn]
    exact max_le_max hul hvl
  refine ⟨lower, hlowerSorted, ?_, ?_⟩
  · refine ⟨by omega, ?_⟩
    intro k hk
    have hkGap : k < d - 1 := by simpa [hlower] using hk
    have huMono : u.get ⟨k, by rw [hu]; omega⟩ ≤
        u.get ⟨k + 1, by rw [hu]; omega⟩ :=
      husorted.rel_get_of_le (Fin.mk_le_mk.mpr (Nat.le_succ k))
    have hvCross : v.get ⟨k, by rw [hv]; omega⟩ ≤
        u.get ⟨k + 1, by rw [hu]; omega⟩ := by
      exact (hcross.2 k (by rw [hu]; omega) (by rw [hv]; omega)).2
    constructor
    · change u.get _ ≤ lower.get _
      simp only [lower, crossGapList, List.get_ofFn]
      exact le_max_left _ _
    · change lower.get _ ≤ u.get _
      simp only [lower, crossGapList, List.get_ofFn]
      exact max_le huMono hvCross
  · refine ⟨by omega, ?_⟩
    intro k hk
    have hkGap : k < d - 1 := by simpa [hlower] using hk
    have hvMono : v.get ⟨k, by rw [hv]; omega⟩ ≤
        v.get ⟨k + 1, by rw [hv]; omega⟩ :=
      hvsorted.rel_get_of_le (Fin.mk_le_mk.mpr (Nat.le_succ k))
    have huCross : u.get ⟨k, by rw [hu]; omega⟩ ≤
        v.get ⟨k + 1, by rw [hv]; omega⟩ := by
      exact (hcross.2 k (by rw [hu]; omega) (by rw [hv]; omega)).1
    constructor
    · change v.get _ ≤ lower.get _
      simp only [lower, crossGapList, List.get_ofFn]
      exact le_max_right _ _
    · change lower.get _ ≤ v.get _
      simp only [lower, crossGapList, List.get_ofFn]
      exact max_le huCross hvMono

/-- For sorted equal-length positive lists, cross-gap compatibility is
equivalent to existence of a single common interlacing list. -/
theorem crossGapCompatible_iff_exists_common_listsInterlace
    (u v : List ℝ) (d : ℕ) (hd : 0 < d)
    (hu : u.length = d) (hv : v.length = d)
    (husorted : u.Pairwise (· ≤ ·))
    (hvsorted : v.Pairwise (· ≤ ·)) :
    CrossGapCompatible u v ↔
      ∃ lower : List ℝ,
        ListsInterlace lower u ∧ ListsInterlace lower v := by
  constructor
  · intro hcross
    obtain ⟨lower, _hlowerSorted, hlu, hlv⟩ :=
      exists_common_listsInterlace_of_crossGapCompatible
        u v d hd hu hv husorted hvsorted hcross
    exact ⟨lower, hlu, hlv⟩
  · rintro ⟨lower, hlu, hlv⟩
    exact crossGapCompatible_of_common_listsInterlace hlu hlv

/-- For same-degree monic real-rooted polynomials, the two finite cross-gap
inequalities are sufficient for a common polynomial interlacer. -/
theorem hasCommonInterlacer_of_crossGapCompatible
    {p q : ℝ[X]} {d : ℕ} (hd : 0 < d)
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpsplits : RealRooted p) (hqsplits : RealRooted q)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    (hcross : CrossGapCompatible
      (p.roots.sort (· ≤ ·)) (q.roots.sort (· ≤ ·))) :
    HasCommonInterlacer ({false, true} : Finset Bool)
      (fun e ↦ if e then p else q) := by
  classical
  let up := p.roots.sort (· ≤ ·)
  let uq := q.roots.sort (· ≤ ·)
  have hup : up.length = d := by
    calc
      up.length = p.roots.card := by simp [up]
      _ = p.natDegree := hpsplits.natDegree_eq_card_roots.symm
      _ = d := hpdegree
  have huq : uq.length = d := by
    calc
      uq.length = q.roots.card := by simp [uq]
      _ = q.natDegree := hqsplits.natDegree_eq_card_roots.symm
      _ = d := hqdegree
  have hupsorted : up.Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort (s := p.roots) (r := (· ≤ ·))
  have huqsorted : uq.Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort (s := q.roots) (r := (· ≤ ·))
  obtain ⟨lower, hlowerSorted, hlowerp, hlowerq⟩ :=
    exists_common_listsInterlace_of_crossGapCompatible
      up uq d hd hup huq hupsorted huqsorted (by simpa [up, uq] using hcross)
  let rootsMultiset : Multiset ℝ := lower
  let r : ℝ[X] := (rootsMultiset.map (fun x ↦ X - C x)).prod
  have hrmonic : r.Monic := monic_multisetProd_X_sub_C rootsMultiset
  have hr0 : r ≠ 0 := hrmonic.ne_zero
  have hrroots : r.roots = rootsMultiset :=
    roots_multiset_prod_X_sub_C rootsMultiset
  have hrsplits : RealRooted r := by
    apply Splits.multisetProd
    intro f hf
    obtain ⟨x, _hx, rfl⟩ := Multiset.mem_map.mp hf
    exact Splits.X_sub_C x
  have hsortedRoots : r.roots.sort (· ≤ ·) = lower := by
    have hperm : List.Perm (r.roots.sort (· ≤ ·)) lower := by
      rw [← Multiset.coe_eq_coe, Multiset.sort_eq, hrroots]
    exact List.Perm.eq_of_pairwise
      (fun a b _ _ hab hba ↦ le_antisymm hab hba)
      (Multiset.pairwise_sort (s := r.roots) (r := (· ≤ ·)))
      hlowerSorted hperm
  refine ⟨r, ?_⟩
  intro e he
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨hr0, hqmonic.ne_zero, hrmonic, hqmonic,
      hrsplits, hqsplits, ?_⟩
    rw [hsortedRoots]
    simpa [uq] using hlowerq
  · simp only [↓reduceIte]
    refine ⟨hr0, hpmonic.ne_zero, hrmonic, hpmonic,
      hrsplits, hpsplits, ?_⟩
    rw [hsortedRoots]
    simpa [up] using hlowerp

/-- Under the usual same-degree monic real-rooted hypotheses, common
interlacing is exactly the finite cross-gap condition on sorted roots. -/
theorem hasCommonInterlacer_iff_crossGapCompatible
    {p q : ℝ[X]} {d : ℕ} (hd : 0 < d)
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpsplits : RealRooted p) (hqsplits : RealRooted q)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d) :
    HasCommonInterlacer ({false, true} : Finset Bool)
        (fun e ↦ if e then p else q) ↔
      CrossGapCompatible
        (p.roots.sort (· ≤ ·)) (q.roots.sort (· ≤ ·)) := by
  constructor
  · rintro ⟨r, hr⟩
    have hrq := hr false (by simp)
    have hrp := hr true (by simp)
    simp only [Bool.false_eq_true, ↓reduceIte] at hrq
    simp only [↓reduceIte] at hrp
    exact crossGapCompatible_of_common_listsInterlace
      hrp.2.2.2.2.2.2 hrq.2.2.2.2.2.2
  · exact hasCommonInterlacer_of_crossGapCompatible hd hpmonic hqmonic
      hpsplits hqsplits hpdegree hqdegree

/-- Root-count balance on all right half-lines is sufficient for a common
interlacer. -/
theorem hasCommonInterlacer_of_rootsGTCountBalanced
    {p q : ℝ[X]} {d : ℕ} (hd : 0 < d)
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpsplits : RealRooted p) (hqsplits : RealRooted q)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    (hbalance : RootsGTCountBalanced p q) :
    HasCommonInterlacer ({false, true} : Finset Bool)
      (fun e ↦ if e then p else q) := by
  apply hasCommonInterlacer_of_crossGapCompatible hd hpmonic hqmonic
    hpsplits hqsplits hpdegree hqdegree
  exact crossGapCompatible_of_rootsGTCountBalanced
    hpsplits hqsplits hpdegree hqdegree hbalance

/-- The full root-disjoint Pair Fell gap is reduced to explicit inequalities
between consecutive sorted endpoint roots. -/
theorem rootDisjointPairFellConverseAtDegree_of_crossGap
    (d : ℕ) (hd : 2 ≤ d)
    (hgap : ∀ (p q : ℝ[X]),
      p.Monic → q.Monic → RealRooted p → RealRooted q →
      p.natDegree = d → q.natDegree = d →
      (∀ a : ℝ, ¬ (p.IsRoot a ∧ q.IsRoot a)) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        RealRooted (t • p + (1 - t) • q)) →
      CrossGapCompatible
        (p.roots.sort (· ≤ ·)) (q.roots.sort (· ≤ ·))) :
    RootDisjointPairFellConverseAtDegree d := by
  intro p q hpmonic hqmonic hpsplits hqsplits hpdegree hqdegree
    hdisjoint hall
  exact hasCommonInterlacer_of_crossGapCompatible (by omega)
    hpmonic hqmonic hpsplits hqsplits hpdegree hqdegree
    (hgap p q hpmonic hqmonic hpsplits hqsplits hpdegree hqdegree
      hdisjoint hall)

/-- Therefore the arbitrary-degree root-disjoint Fell core is reduced to
the endpoint half-line root-count estimate.  This is the smallest remaining
analytic statement: roots in an affine real-rooted pencil can cross a fixed
threshold at most once in total, since threshold evaluation is affine and
the endpoint polynomials are root-disjoint. -/
theorem rootDisjointPairFellConverseAtDegree_of_rootsGTCountBalanced
    (d : ℕ) (hd : 2 ≤ d)
    (hcount : ∀ (p q : ℝ[X]),
      p.Monic → q.Monic → RealRooted p → RealRooted q →
      p.natDegree = d → q.natDegree = d →
      (∀ a : ℝ, ¬ (p.IsRoot a ∧ q.IsRoot a)) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        RealRooted (t • p + (1 - t) • q)) →
      RootsGTCountBalanced p q) :
    RootDisjointPairFellConverseAtDegree d := by
  intro p q hpmonic hqmonic hpsplits hqsplits hpdegree hqdegree
    hdisjoint hall
  exact hasCommonInterlacer_of_rootsGTCountBalanced (by omega)
    hpmonic hqmonic hpsplits hqsplits hpdegree hqdegree
    (hcount p q hpmonic hqmonic hpsplits hqsplits hpdegree hqdegree
      hdisjoint hall)

end CommutatorTheorem.BTFellCrossGap
