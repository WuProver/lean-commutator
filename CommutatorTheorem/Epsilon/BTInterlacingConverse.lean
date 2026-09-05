import CommutatorTheorem.Epsilon.BTInterlacing

/-!
# Finite converse infrastructure for common interlacing

Fell's converse says that a finite family of same-degree real-rooted
polynomials has a common interlacer when all its convex combinations are
real-rooted.  The analytic two-polynomial implication is the difficult core.

This file first closes the finite Helly step: pairwise common interlacing is
already enough for a single interlacer for the whole finite family.  The proof
is constructive.  At each root gap it takes the largest lower endpoint among
the family; pairwise common interlacing says that this endpoint lies below
every upper endpoint.  We first prove the statement for sorted root lists and
then package it for polynomials.
-/

open scoped BigOperators Polynomial

namespace CommutatorTheorem.BTInterlacingConverse

open Polynomial
open CommutatorTheorem

/-! ## Finite maximizers -/

/-- A selected point at which a real-valued function on a nonempty finset is
maximal. -/
noncomputable def maximizingIndex {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) : ι :=
  Classical.choose (Finset.exists_max_image s f hs)

theorem maximizingIndex_mem {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    maximizingIndex s hs f ∈ s :=
  (Classical.choose_spec (Finset.exists_max_image s f hs)).1

theorem le_maximizingIndex {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) :
    f i ≤ f (maximizingIndex s hs f) :=
  (Classical.choose_spec (Finset.exists_max_image s f hs)).2 i hi

/-! ## The interval-Helly step for root lists -/

/-- The `k`-th entry of an equal-length family of lists. -/
noncomputable def listEntry {ι : Type*} (upper : ι → List ℝ)
    (d : ℕ) (hlen : ∀ i, (upper i).length = d)
    (i : ι) (k : Fin d) : ℝ :=
  (upper i).get ⟨k, by simp [hlen i]⟩

@[simp] theorem listEntry_eq_get {ι : Type*} (upper : ι → List ℝ)
    (d : ℕ) (hlen : ∀ i, (upper i).length = d)
    (i : ι) (k : Fin d) :
    listEntry upper d hlen i k =
      (upper i).get ⟨k, by simp [hlen i]⟩ := rfl

/-- At gap `k`, choose a member whose lower endpoint is largest. -/
noncomputable def gapMaximizer {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (upper : ι → List ℝ)
    (d : ℕ) (hlen : ∀ i, (upper i).length = d)
    (k : Fin (d - 1)) : ι :=
  maximizingIndex s hs (fun i ↦
    listEntry upper d hlen i ⟨k, by omega⟩)

/-- The candidate common interlacer list: largest lower endpoint in every
root gap. -/
noncomputable def commonGapList {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (upper : ι → List ℝ)
    (d : ℕ) (hlen : ∀ i, (upper i).length = d) : List ℝ :=
  List.ofFn (fun k : Fin (d - 1) ↦
    listEntry upper d hlen (gapMaximizer s hs upper d hlen k)
      ⟨k, by omega⟩)

@[simp] theorem commonGapList_length {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (upper : ι → List ℝ)
    (d : ℕ) (hlen : ∀ i, (upper i).length = d) :
    (commonGapList s hs upper d hlen).length = d - 1 := by
  simp [commonGapList]

/-- Pairwise interlacing supplies the cross-gap inequality: the lower
endpoint from any member is below the upper endpoint from any other member. -/
theorem cross_gap_le_of_pairwise_listsInterlace
    {ι : Type*}
    {s : Finset ι} {upper : ι → List ℝ} {d : ℕ}
    (hlen : ∀ i ∈ s, (upper i).length = d)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      ∃ lower : List ℝ,
        ListsInterlace lower (upper i) ∧ ListsInterlace lower (upper j))
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (k : ℕ) (hk : k + 1 < d) :
    (upper i).get ⟨k, by rw [hlen i hi]; omega⟩ ≤
      (upper j).get ⟨k + 1, by rw [hlen j hj]; omega⟩ := by
  obtain ⟨lower, hil, hjl⟩ := hpair i hi j hj
  obtain ⟨hilen, hiEntries⟩ := hil
  obtain ⟨hjlen, hjEntries⟩ := hjl
  have hlower : lower.length = d - 1 := by
    rw [hlen i hi] at hilen
    omega
  have hkLower : k < lower.length := by omega
  exact (hiEntries k hkLower).1.trans (hjEntries k hkLower).2

/-- Finite interval Helly for interlacing root lists. -/
theorem exists_common_list_of_pairwise_interlacing
    {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty)
    (upper : ι → List ℝ) (d : ℕ) (hd : 0 < d)
    (hlen : ∀ i ∈ s, (upper i).length = d)
    (hsorted : ∀ i ∈ s, (upper i).Pairwise (· ≤ ·))
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      ∃ lower : List ℝ,
        ListsInterlace lower (upper i) ∧ ListsInterlace lower (upper j)) :
    ∃ lower : List ℝ,
      lower.Pairwise (· ≤ ·) ∧
      ∀ i ∈ s, ListsInterlace lower (upper i) := by
  classical
  let i₀ : ι := Classical.choose hs
  have hi₀ : i₀ ∈ s := Classical.choose_spec hs
  let upper' : ι → List ℝ := fun i ↦ if i ∈ s then upper i else upper i₀
  have hupper' : ∀ i ∈ s, upper' i = upper i := by
    intro i hi
    simp [upper', hi]
  have hlenAll : ∀ i, (upper' i).length = d := by
    intro i
    by_cases hi : i ∈ s
    · rw [hupper' i hi]
      exact hlen i hi
    · simp [upper', hi, hlen i₀ hi₀]
  have hpair' : ∀ i ∈ s, ∀ j ∈ s,
      ∃ l : List ℝ,
        ListsInterlace l (upper' i) ∧ ListsInterlace l (upper' j) := by
    intro i hi j hj
    simpa [upper', hi, hj] using hpair i hi j hj
  let lower := commonGapList s hs upper' d hlenAll
  have hlowerLen : lower.length = d - 1 := commonGapList_length s hs upper' d hlenAll
  refine ⟨lower, ?_, ?_⟩
  · rw [List.pairwise_iff_getElem]
    intro k l hk hl hkl
    have hk' : k < d - 1 := by simpa [hlowerLen] using hk
    have hl' : l < d - 1 := by simpa [hlowerLen] using hl
    let ik : Fin (d - 1) := ⟨k, hk'⟩
    let il : Fin (d - 1) := ⟨l, hl'⟩
    let ak := gapMaximizer s hs upper' d hlenAll ik
    let al := gapMaximizer s hs upper' d hlenAll il
    have hak : ak ∈ s := maximizingIndex_mem s hs
      (fun i ↦ listEntry upper' d hlenAll i ⟨ik, by omega⟩)
    have hal : al ∈ s := maximizingIndex_mem s hs
      (fun i ↦ listEntry upper' d hlenAll i ⟨il, by omega⟩)
    have hrootmono :
        listEntry upper' d hlenAll ak ⟨k, by omega⟩ ≤
          listEntry upper' d hlenAll ak ⟨l, by omega⟩ := by
      have hsorted' : (upper' ak).Pairwise (· ≤ ·) := by
        simpa [upper', hak] using hsorted ak hak
      apply hsorted'.rel_get_of_le
      exact hkl.le
    have hmax :
        listEntry upper' d hlenAll ak ⟨l, by omega⟩ ≤
          listEntry upper' d hlenAll al ⟨l, by omega⟩ := by
      exact le_maximizingIndex s hs
        (fun i ↦ listEntry upper' d hlenAll i ⟨il, by omega⟩) hak
    change lower[k] ≤ lower[l]
    simp only [lower, commonGapList, List.getElem_ofFn]
    exact hrootmono.trans hmax
  · intro i hi
    refine ⟨by rw [hlen i hi, hlowerLen]; omega, ?_⟩
    intro k hk
    have hkGap : k < d - 1 := by simpa [hlowerLen] using hk
    let ik : Fin (d - 1) := ⟨k, hkGap⟩
    let a := gapMaximizer s hs upper' d hlenAll ik
    have ha : a ∈ s := maximizingIndex_mem s hs
      (fun j ↦ listEntry upper' d hlenAll j ⟨ik, by omega⟩)
    constructor
    · change (upper i).get _ ≤ lower.get _
      simp only [lower, commonGapList, List.get_ofFn]
      have hle := le_maximizingIndex s hs
        (fun j ↦ listEntry upper' d hlenAll j ⟨ik, by omega⟩) hi
      simpa [listEntry, hupper' i hi] using hle
    · change lower.get _ ≤ (upper i).get _
      simp only [lower, commonGapList, List.get_ofFn]
      have hcross := cross_gap_le_of_pairwise_listsInterlace
        (fun j _ ↦ hlenAll j) hpair' ha hi k (by omega)
      simpa [listEntry, a, ik, upper', ha, hi] using hcross

/-! ## Pairwise common interlacing implies finite common interlacing -/

/-- A finite family of same-degree monic real-rooted polynomials has a common
interlacer as soon as every pair has one.  This is the finite one-dimensional
Helly step in Fell's converse. -/
theorem hasCommonInterlacer_of_pairwise
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (p : ι → ℝ[X])
    (d : ℕ) (hd : 0 < d)
    (hmonic : ∀ i ∈ s, (p i).Monic)
    (hsplits : ∀ i ∈ s, RealRooted (p i))
    (hdegree : ∀ i ∈ s, (p i).natDegree = d)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      HasCommonInterlacer ({i, j} : Finset ι) p) :
    HasCommonInterlacer s p := by
  classical
  let upper : ι → List ℝ := fun i ↦ (p i).roots.sort (· ≤ ·)
  have hlen : ∀ i ∈ s, (upper i).length = d := by
    intro i hi
    calc
      (upper i).length = (p i).roots.card := by simp [upper]
      _ = (p i).natDegree := (hsplits i hi).natDegree_eq_card_roots.symm
      _ = d := hdegree i hi
  have hsorted : ∀ i ∈ s, (upper i).Pairwise (· ≤ ·) := by
    intro i _
    exact Multiset.pairwise_sort (s := (p i).roots) (r := (· ≤ ·))
  have hpairLists : ∀ i ∈ s, ∀ j ∈ s,
      ∃ lower : List ℝ,
        ListsInterlace lower (upper i) ∧ ListsInterlace lower (upper j) := by
    intro i hi j hj
    obtain ⟨q, hq⟩ := hpair i hi j hj
    refine ⟨q.roots.sort (· ≤ ·), ?_, ?_⟩
    · exact (hq i (by simp)).2.2.2.2.2.2
    · exact (hq j (by simp)).2.2.2.2.2.2
  obtain ⟨lower, hlowerSorted, hlower⟩ :=
    exists_common_list_of_pairwise_interlacing
      s hs upper d hd hlen hsorted hpairLists
  let rootsMultiset : Multiset ℝ := lower
  let q : ℝ[X] := (rootsMultiset.map (fun r ↦ X - C r)).prod
  have hqmonic : q.Monic := by
    exact monic_multisetProd_X_sub_C rootsMultiset
  have hq0 : q ≠ 0 := hqmonic.ne_zero
  have hqroots : q.roots = rootsMultiset := by
    exact roots_multiset_prod_X_sub_C rootsMultiset
  have hqsplit : RealRooted q := by
    apply Splits.multisetProd
    intro f hf
    obtain ⟨r, _hr, rfl⟩ := Multiset.mem_map.mp hf
    exact Splits.X_sub_C r
  have hsortedRoots : q.roots.sort (· ≤ ·) = lower := by
    have hperm : List.Perm (q.roots.sort (· ≤ ·)) lower := by
      rw [← Multiset.coe_eq_coe, Multiset.sort_eq, hqroots]
    exact List.Perm.eq_of_pairwise
      (fun a b _ _ hab hba ↦ le_antisymm hab hba)
      (Multiset.pairwise_sort (s := q.roots) (r := (· ≤ ·)))
      hlowerSorted hperm
  refine ⟨q, ?_⟩
  intro i hi
  refine ⟨hq0, (hmonic i hi).ne_zero, hqmonic, hmonic i hi,
    hqsplit, hsplits i hi, ?_⟩
  rw [hsortedRoots]
  exact hlower i hi

/-- It is enough to establish the analytic two-polynomial Fell implication:
the finite-family conclusion then follows automatically from
`hasCommonInterlacer_of_pairwise`. -/
theorem finite_fell_of_pair_fell
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (p : ι → ℝ[X])
    (d : ℕ) (hd : 0 < d)
    (hmonic : ∀ i ∈ s, (p i).Monic)
    (hsplits : ∀ i ∈ s, RealRooted (p i))
    (hdegree : ∀ i ∈ s, (p i).natDegree = d)
    (pairFell : ∀ i ∈ s, ∀ j ∈ s,
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        RealRooted (t • p i + (1 - t) • p j)) →
      HasCommonInterlacer ({i, j} : Finset ι) p)
    (hall : ∀ i ∈ s, ∀ j ∈ s, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p i + (1 - t) • p j)) :
    HasCommonInterlacer s p := by
  apply hasCommonInterlacer_of_pairwise s hs p d hd hmonic hsplits hdegree
  intro i hi j hj
  exact pairFell i hi j hj (hall i hi j hj)

/-! ## The degree-one Fell base case -/

/-- Every finite family of monic real-rooted linear polynomials has the
constant polynomial `1` as a common interlacer. -/
theorem hasCommonInterlacer_of_natDegree_one
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ[X])
    (hmonic : ∀ i ∈ s, (p i).Monic)
    (hsplits : ∀ i ∈ s, RealRooted (p i))
    (hdegree : ∀ i ∈ s, (p i).natDegree = 1) :
    HasCommonInterlacer s p := by
  refine ⟨1, ?_⟩
  intro i hi
  have hp0 : p i ≠ 0 := (hmonic i hi).ne_zero
  have hrootsLen : ((p i).roots.sort (· ≤ ·)).length = 1 := by
    calc
      ((p i).roots.sort (· ≤ ·)).length = (p i).roots.card := by simp
      _ = (p i).natDegree := (hsplits i hi).natDegree_eq_card_roots.symm
      _ = 1 := hdegree i hi
  refine ⟨one_ne_zero, hp0, monic_one, hmonic i hi,
    Splits.one, hsplits i hi, ?_⟩
  have honeRoots : ((1 : ℝ[X]).roots.sort (· ≤ ·)) = [] := by simp
  rw [honeRoots]
  refine ⟨by simpa using hrootsLen, ?_⟩
  intro k hk
  simp at hk

/-- In particular, the analytic pair Fell converse is completely settled in
degree one. -/
theorem pair_fell_natDegree_one
    (p q : ℝ[X])
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpsplits : RealRooted p) (hqsplits : RealRooted q)
    (hpdegree : p.natDegree = 1) (hqdegree : q.natDegree = 1)
    (_hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q)) :
    HasCommonInterlacer ({false, true} : Finset Bool)
      (fun b ↦ if b then p else q) := by
  apply hasCommonInterlacer_of_natDegree_one
  · intro b hb
    cases b <;> simp [hpmonic, hqmonic]
  · intro b hb
    cases b <;> simp [hpsplits, hqsplits]
  · intro b hb
    cases b <;> simp [hpdegree, hqdegree]

end CommutatorTheorem.BTInterlacingConverse
