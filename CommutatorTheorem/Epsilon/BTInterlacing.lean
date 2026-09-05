import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.List.Count

/-!
# Elementary interlacing-polynomial infrastructure

This file supplies an axiom-free interface for the interlacing-family route to paving and
restricted invertibility.  Mathlib currently has polynomial roots, splitting, and Rolle's
theorem, but no bundled definition of interlacing families.
-/

namespace CommutatorTheorem

open scoped Polynomial
open Polynomial

/-! ## Real-rooted polynomials and upper root bounds -/

/-- For a real polynomial, splitting over `ℝ` is exactly the real-rootedness condition used here. -/
abbrev RealRooted (p : ℝ[X]) : Prop := p.Splits

/-- `x` is an upper bound for all real roots of `p`. -/
def IsRootUpperBound (p : ℝ[X]) (x : ℝ) : Prop :=
  ∀ r : ℝ, p.IsRoot r → r ≤ x

/-- `x` is strictly larger than every real root of `p`. -/
def IsStrictRootUpperBound (p : ℝ[X]) (x : ℝ) : Prop :=
  ∀ r : ℝ, p.IsRoot r → r < x

/-- `x` is a largest root of `p`. -/
structure IsLargestRoot (p : ℝ[X]) (x : ℝ) : Prop where
  isRoot : p.IsRoot x
  upperBound : IsRootUpperBound p x

/-- A monic real-rooted polynomial is nonnegative to the right of all its roots. -/
lemma RealRooted.eval_nonneg_of_rootUpperBound {p : ℝ[X]} (hp : RealRooted p)
    (hmonic : p.Monic) {x : ℝ} (hx : IsRootUpperBound p x) :
    0 ≤ p.eval x := by
  rw [hp.eval_eq_prod_roots_of_monic hmonic]
  apply Multiset.prod_map_nonneg
  intro r hr
  exact sub_nonneg.mpr (hx r ((mem_roots hmonic.ne_zero).mp hr))

/-- A monic real-rooted polynomial is positive strictly to the right of all its roots. -/
lemma RealRooted.eval_pos_of_strictRootUpperBound {p : ℝ[X]} (hp : RealRooted p)
    (hmonic : p.Monic) {x : ℝ} (hx : IsStrictRootUpperBound p x) :
    0 < p.eval x := by
  rw [hp.eval_eq_prod_roots_of_monic hmonic]
  apply Multiset.prod_pos
  intro y hy
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
  exact sub_pos.mpr (hx r ((mem_roots hmonic.ne_zero).mp hr))

/-- Every nonconstant real-rooted polynomial has a largest real root. -/
lemma RealRooted.exists_largestRoot {p : ℝ[X]} (hp : RealRooted p)
    (hdeg : 0 < p.natDegree) : ∃ x, IsLargestRoot p x := by
  have hp0 : p ≠ 0 := by
    intro hpzero
    simp [hpzero] at hdeg
  obtain ⟨x, hx⟩ := p.exists_max_root hp0
  have hroots : p.roots ≠ 0 := hp.roots_ne_zero hdeg.ne'
  obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hroots
  have hrroot : p.IsRoot r := (mem_roots hp0).mp hr
  let rootsFinset := p.roots.toFinset
  have hne : rootsFinset.Nonempty := ⟨r, by simpa [rootsFinset] using hr⟩
  let xmax := rootsFinset.max' hne
  have hxmem : xmax ∈ p.roots := by
    have : xmax ∈ rootsFinset := Finset.max'_mem rootsFinset hne
    simpa [rootsFinset] using this
  refine ⟨xmax, (mem_roots hp0).mp hxmem, ?_⟩
  intro y hy
  have hymem : y ∈ rootsFinset := by
    simpa [rootsFinset, mem_roots hp0] using hy
  exact Finset.le_max' rootsFinset y hymem

/-- The final entry of the ascending sorted root list is a largest root. -/
lemma sortedRoots_getLast_isLargest {p : ℝ[X]} (hp0 : p ≠ 0)
    (hne : p.roots.sort (· ≤ ·) ≠ []) :
    IsLargestRoot p ((p.roots.sort (· ≤ ·)).getLast hne) := by
  let rootsList := p.roots.sort (· ≤ ·)
  have hlastmem : rootsList.getLast hne ∈ rootsList := List.getLast_mem hne
  have hlastroot : p.IsRoot (rootsList.getLast hne) := by
    apply (mem_roots hp0).mp
    exact (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mp hlastmem
  refine ⟨hlastroot, ?_⟩
  intro r hr
  have hrmem : r ∈ rootsList := by
    simpa [rootsList] using (mem_roots hp0).mpr hr
  have hsorted : rootsList.Pairwise (· ≤ ·) := by
    exact Multiset.pairwise_sort (s := p.roots) (r := (· ≤ ·))
  exact hsorted.rel_getLast_of_rel_getLast_getLast hrmem le_rfl

/-! ## List and polynomial interlacing -/

/-- Ascending lists `upper = [u₀, ..., uₙ]` and `lower = [l₀, ..., lₙ₋₁]` interlace when
`uₖ ≤ lₖ ≤ uₖ₊₁` for every `k`.

The equality proof is stored explicitly so that the two `List.get` bounds remain definitionally
available to Lean. -/
def ListsInterlace (lower upper : List ℝ) : Prop :=
  ∃ hlen : upper.length = lower.length + 1,
    ∀ (k : ℕ) (hk : k < lower.length),
      upper.get ⟨k, by omega⟩ ≤ lower.get ⟨k, hk⟩ ∧
        lower.get ⟨k, hk⟩ ≤ upper.get ⟨k + 1, by omega⟩

/-- In an interlacing pair, the penultimate entry of the longer list is at most the final entry of
the shorter list. -/
lemma ListsInterlace.penultimate_le_last {lower upper : List ℝ}
    (h : ListsInterlace lower upper) (hlower : lower ≠ []) :
    ∃ k : Fin upper.length,
      upper.get k ≤ lower.getLast hlower ∧ k.val + 2 = upper.length := by
  obtain ⟨hlen, hinterlace⟩ := h
  have hlpos : 0 < lower.length := List.length_pos_of_ne_nil hlower
  have hklower : lower.length - 1 < lower.length := by omega
  have hkupper : lower.length - 1 < upper.length := by omega
  let k : Fin upper.length := ⟨lower.length - 1, hkupper⟩
  refine ⟨k, ?_, ?_⟩
  · have hleft := (hinterlace (lower.length - 1) hklower).1
    simpa [k, List.getLast_eq_getElem] using hleft
  · simp [k]
    omega

/-- Every entry of the longer list except its final one is bounded by the final entry of the
shorter list. -/
lemma ListsInterlace.dropLast_le_last {lower upper : List ℝ}
    (h : ListsInterlace lower upper) (hlower : lower ≠ [])
    (hsorted : lower.Pairwise (· ≤ ·)) :
    ∀ u ∈ upper.dropLast, u ≤ lower.getLast hlower := by
  obtain ⟨hlen, hinterlace⟩ := h
  rw [List.forall_mem_iff_getElem]
  intro j hj
  have hjlower : j < lower.length := by
    simp only [List.length_dropLast] at hj
    omega
  have hleft := (hinterlace j hjlower).1
  have hlowerlast : lower[j] ≤ lower.getLast hlower := by
    exact hsorted.rel_getLast (List.get_mem lower ⟨j, hjlower⟩)
  calc
    upper.dropLast[j] = upper[j] := by simp
    _ ≤ lower[j] := hleft
    _ ≤ lower.getLast hlower := hlowerlast

/-- A real polynomial `q` interlaces `p` when their ascending root lists interlace. -/
def PolynomialInterlaces (q p : ℝ[X]) : Prop :=
  q ≠ 0 ∧ p ≠ 0 ∧ q.Monic ∧ p.Monic ∧ q.Splits ∧ p.Splits ∧
    ListsInterlace (q.roots.sort (· ≤ ·)) (p.roots.sort (· ≤ ·))

/-- Interlacing fixes the degree difference: the longer polynomial has degree exactly one more
than its interlacer. -/
lemma PolynomialInterlaces.natDegree_eq_succ {q p : ℝ[X]}
    (h : PolynomialInterlaces q p) : p.natDegree = q.natDegree + 1 := by
  rcases h with ⟨_hq0, _hp0, _hqmonic, _hpmonic, hqsplit, hpsplit, hinterlace⟩
  obtain ⟨hlen, _hentries⟩ := hinterlace
  calc
    p.natDegree = (p.roots.sort (· ≤ ·)).length := by
      rw [hpsplit.natDegree_eq_card_roots]
      simp
    _ = (q.roots.sort (· ≤ ·)).length + 1 := hlen
    _ = q.natDegree + 1 := by
      rw [hqsplit.natDegree_eq_card_roots]
      simp

/-- Every polynomial interlaced by `q` has the same weak alternating sign at the indexed roots
of `q`.  Multiplication by the displayed power of `-1` makes that sign nonnegative.

This is the root-interval sign input to the usual IVT proof that convex combinations preserve a
common interlacer.  It is stated with multiplicities, so it remains valid at repeated roots. -/
lemma PolynomialInterlaces.eval_at_interlacerRoot_sign
    {q p : ℝ[X]} (h : PolynomialInterlaces q p)
    (k : ℕ) (hk : k < (q.roots.sort (· ≤ ·)).length) :
    0 ≤ p.eval ((q.roots.sort (· ≤ ·)).get ⟨k, hk⟩) *
      (-1 : ℝ) ^ ((q.roots.sort (· ≤ ·)).length - k) := by
  rcases h with ⟨_hq0, _hp0, _hqmonic, hpmonic, _hqsplit, hpsplit, hinterlace⟩
  let lower := q.roots.sort (· ≤ ·)
  let upper := p.roots.sort (· ≤ ·)
  let x := lower.get ⟨k, by simpa [lower] using hk⟩
  let pre := upper.take (k + 1)
  let suf := upper.drop (k + 1)
  obtain ⟨hlen, hentries⟩ := hinterlace
  change upper.length = lower.length + 1 at hlen
  have hkLower : k < lower.length := by simpa [lower] using hk
  have hkUpper : k + 1 < upper.length := by omega
  have hlowerSorted : lower.Pairwise (· ≤ ·) := by
    exact Multiset.pairwise_sort (s := q.roots) (r := (· ≤ ·))
  have hupperSorted : upper.Pairwise (· ≤ ·) := by
    exact Multiset.pairwise_sort (s := p.roots) (r := (· ≤ ·))
  have hprefixLength : pre.length = k + 1 := by
    simp [pre]
    omega
  have hprefixBound : ∀ r ∈ pre, r ≤ x := by
    rw [List.forall_mem_iff_getElem]
    intro j hj
    have hjk : j ≤ k := by rw [hprefixLength] at hj; omega
    have hjLower : j < lower.length := lt_of_le_of_lt hjk hkLower
    have hjUpper : j < upper.length := lt_of_le_of_lt hjk (by omega)
    have hleft := (hentries j hjLower).1
    have hlowerjk :
        lower.get ⟨j, hjLower⟩ ≤ lower.get ⟨k, hkLower⟩ :=
      hlowerSorted.rel_get_of_le (by simpa using hjk)
    change pre.get ⟨j, hj⟩ ≤ x
    rw [show pre.get ⟨j, hj⟩ = upper.get ⟨j, hjUpper⟩ by simp [pre]]
    exact hleft.trans hlowerjk
  have hsuffixBound : ∀ r ∈ suf, x ≤ r := by
    rw [List.forall_mem_iff_getElem]
    intro j hj
    have hjIndex : k + 1 + j < upper.length := by
      simp [suf] at hj
      omega
    have hright := (hentries k hkLower).2
    have hupperkj :
        upper.get ⟨k + 1, hkUpper⟩ ≤ upper.get ⟨k + 1 + j, hjIndex⟩ :=
      hupperSorted.rel_get_of_le (by simp)
    change x ≤ suf.get ⟨j, hj⟩
    rw [show suf.get ⟨j, hj⟩ = upper.get ⟨k + 1 + j, hjIndex⟩ by
      simp [suf, Nat.add_assoc]]
    exact hright.trans hupperkj
  have hprefixNonneg :
      0 ≤ (pre.map (fun r => x - r)).prod := by
    apply List.prod_nonneg
    intro y hy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
    exact sub_nonneg.mpr (hprefixBound r hr)
  have hsuffixNonneg :
      0 ≤ (suf.map (fun r => r - x)).prod := by
    apply List.prod_nonneg
    intro y hy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
    exact sub_nonneg.mpr (hsuffixBound r hr)
  have hsuffixSign :
      (suf.map (fun r => x - r)).prod * (-1 : ℝ) ^ suf.length =
        (suf.map (fun r => r - x)).prod := by
    induction suf with
    | nil => simp
    | cons a l ih =>
        calc
          ((a :: l).map (fun r => x - r)).prod * (-1 : ℝ) ^ (a :: l).length =
              -(x - a) * ((l.map (fun r => x - r)).prod * (-1 : ℝ) ^ l.length) := by
                simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
                ring
          _ = -(x - a) * (l.map (fun r => r - x)).prod := by rw [ih]
          _ = ((a :: l).map (fun r => r - x)).prod := by simp
  have hsuffixLength : suf.length = lower.length - k := by
    simp [suf]
    omega
  have heval :
      p.eval x = (pre.map (fun r => x - r)).prod *
        (suf.map (fun r => x - r)).prod := by
    rw [hpsplit.eval_eq_prod_roots_of_monic hpmonic]
    rw [← Multiset.sort_eq (s := p.roots) (r := (· ≤ ·))]
    change (upper.map (fun r => x - r)).prod = _
    rw [show upper = pre ++ suf by simp [pre, suf]]
    simp
  change 0 ≤ p.eval x * (-1 : ℝ) ^ (lower.length - k)
  rw [heval, ← hsuffixLength]
  calc
    0 ≤ (pre.map (fun r => x - r)).prod *
        (suf.map (fun r => r - x)).prod :=
      mul_nonneg hprefixNonneg hsuffixNonneg
    _ = (pre.map (fun r => x - r)).prod *
        (suf.map (fun r => x - r)).prod * (-1 : ℝ) ^ suf.length := by
      rw [mul_assoc, hsuffixSign]

/-! Repeated roots of a weak interlacer require a multiplicity argument: applying the
intermediate value theorem separately to collapsed intervals only rediscovers the same root.
The following counting lemma records the missing information directly. -/

/-- For a list, the number of entries at most `a` is the number strictly below `a` plus the
number equal to `a`.  This index-cardinality form is convenient for comparing interlacing
lists of different lengths. -/
private lemma card_fin_get_le_eq_add_lt_eq (l : List ℝ) (a : ℝ) :
    Fintype.card {k : Fin l.length // l.get k ≤ a} =
      Fintype.card {k : Fin l.length // l.get k < a} +
        Fintype.card {k : Fin l.length // l.get k = a} := by
  classical
  simp_rw [Fintype.card_subtype]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact le_iff_lt_or_eq
  · rw [Finset.disjoint_left]
    intro k hklt hkeq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hklt hkeq
    exact (ne_of_lt hklt) hkeq

/-- Interlacing gives at least as many entries at most `a` in the longer list as in the
shorter list. -/
private lemma ListsInterlace.card_get_le_le {lower upper : List ℝ}
    (h : ListsInterlace lower upper) (a : ℝ) :
    Fintype.card {k : Fin lower.length // lower.get k ≤ a} ≤
      Fintype.card {k : Fin upper.length // upper.get k ≤ a} := by
  classical
  obtain ⟨hlen, hentries⟩ := h
  let f : {k : Fin lower.length // lower.get k ≤ a} →
      {k : Fin upper.length // upper.get k ≤ a} := fun k =>
    ⟨⟨k.1.1, by omega⟩, (hentries k.1.1 k.1.2).1.trans k.2⟩
  exact Fintype.card_le_of_injective f fun x y hxy => by
    apply Subtype.ext
    apply Fin.ext
    exact congr_arg (fun z => z.1.1) hxy

/-- The longer interlacing list has at most one more entry strictly below `a` than the shorter
list.  The possible extra entry is its first one. -/
private lemma ListsInterlace.card_get_lt_le_add_one {lower upper : List ℝ}
    (h : ListsInterlace lower upper) (a : ℝ) :
    Fintype.card {k : Fin upper.length // upper.get k < a} ≤
      Fintype.card {k : Fin lower.length // lower.get k < a} + 1 := by
  classical
  obtain ⟨hlen, hentries⟩ := h
  let f : {k : Fin upper.length // upper.get k < a} →
      Option {k : Fin lower.length // lower.get k < a} := fun k =>
    if hk0 : k.1.1 = 0 then none else
      some ⟨⟨k.1.1 - 1, by omega⟩,
        (hentries (k.1.1 - 1) (by omega)).2.trans_lt (by
          have heq :
              (⟨k.1.1 - 1 + 1, by omega⟩ : Fin upper.length) = k.1 := by
            apply Fin.ext
            exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)
          rw [heq]
          exact k.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    dsimp [f] at hxy
    split at hxy <;> split at hxy
    · apply Subtype.ext
      apply Fin.ext
      omega
    · contradiction
    · contradiction
    · simp only [Option.some.injEq, Subtype.mk.injEq, Fin.mk.injEq] at hxy
      apply Subtype.ext
      apply Fin.ext
      omega
  simpa using Fintype.card_le_of_injective f hf

/-- The two distribution-function inequalities used above also characterize interlacing for
sorted lists of the correct lengths. -/
private lemma ListsInterlace.of_card_bounds {lower upper : List ℝ}
    (hlower : lower.Pairwise (· ≤ ·)) (hupper : upper.Pairwise (· ≤ ·))
    (hlen : upper.length = lower.length + 1)
    (hle : ∀ a : ℝ,
      Fintype.card {k : Fin lower.length // lower.get k ≤ a} ≤
        Fintype.card {k : Fin upper.length // upper.get k ≤ a})
    (hlt : ∀ a : ℝ,
      Fintype.card {k : Fin upper.length // upper.get k < a} ≤
        Fintype.card {k : Fin lower.length // lower.get k < a} + 1) :
    ListsInterlace lower upper := by
  classical
  refine ⟨hlen, ?_⟩
  intro k hk
  let x := lower.get ⟨k, hk⟩
  have hlowerDownLE : ∀ i j : Fin lower.length, j ≤ i →
      lower.get i ≤ x → lower.get j ≤ x := by
    intro i j hji hi
    exact (hlower.rel_get_of_le hji).trans hi
  have hupperDownLE : ∀ i j : Fin upper.length, j ≤ i →
      upper.get i ≤ x → upper.get j ≤ x := by
    intro i j hji hi
    exact (hupper.rel_get_of_le hji).trans hi
  have hlowerDownLT : ∀ i j : Fin lower.length, j ≤ i →
      lower.get i < x → lower.get j < x := by
    intro i j hji hi
    exact (hlower.rel_get_of_le hji).trans_lt hi
  have hupperDownLT : ∀ i j : Fin upper.length, j ≤ i →
      upper.get i < x → upper.get j < x := by
    intro i j hji hi
    exact (hupper.rel_get_of_le hji).trans_lt hi
  have hle' := hle x
  have hlt' := hlt x
  simp_rw [Fintype.card_subtype] at hle' hlt'
  have hkLowerCard : k <
      (Finset.filter (fun i : Fin lower.length => lower.get i ≤ x) Finset.univ).card :=
    (Fin.lt_card_filter_univ_iff_apply_of_imp _ hlowerDownLE).2 le_rfl
  have hkUpper : k < upper.length := by omega
  have hkUpperCard : k <
      (Finset.filter (fun i : Fin upper.length => upper.get i ≤ x) Finset.univ).card := by omega
  have hleft : upper.get ⟨k, hkUpper⟩ ≤ x :=
    (Fin.lt_card_filter_univ_iff_apply_of_imp _ hupperDownLE).1 hkUpperCard
  have hkOneUpper : k + 1 < upper.length := by omega
  have hright : x ≤ upper.get ⟨k + 1, hkOneUpper⟩ := by
    by_contra hnot
    have hupperlt : upper.get ⟨k + 1, hkOneUpper⟩ < x := lt_of_not_ge hnot
    have hkOneCard : k + 1 <
        (Finset.filter (fun i : Fin upper.length => upper.get i < x) Finset.univ).card :=
      (Fin.lt_card_filter_univ_iff_apply_of_imp _ hupperDownLT).2 hupperlt
    have hlowerCardLe :
        (Finset.filter (fun i : Fin lower.length => lower.get i < x) Finset.univ).card ≤ k := by
      by_contra hnotle
      have hkcard : k <
          (Finset.filter (fun i : Fin lower.length => lower.get i < x) Finset.univ).card := by
        omega
      have hkcardFin : (⟨k, hk⟩ : Fin lower.length) <
          (Finset.filter (fun i : Fin lower.length => lower.get i < x) Finset.univ).card :=
        hkcard
      have := (Fin.lt_card_filter_univ_iff_apply_of_imp _ hlowerDownLT).1 hkcardFin
      exact (lt_irrefl x) this
    omega
  exact ⟨hleft, hright⟩

/-- Index-cardinality is the Boolean `countP` of the corresponding predicate. -/
private lemma card_fin_get_eq_countP (l : List ℝ) (P : ℝ → Prop) [DecidablePred P] :
    Fintype.card {k : Fin l.length // P (l.get k)} =
      l.countP (fun x => decide (P x)) := by
  classical
  let v : List.Vector Bool l.length :=
    ⟨l.map (fun x => decide (P x)), by simp⟩
  rw [Fintype.card_subtype]
  calc
    (Finset.filter (fun k : Fin l.length => P (l.get k)) Finset.univ).card =
        (Finset.filter (fun k : Fin l.length => v.get k = true) Finset.univ).card := by
          congr 1
          ext k
          simp [v, List.Vector.get]
    _ = v.toList.count true := Fin.card_filter_univ_eq_vector_get_eq_count true v
    _ = l.countP (fun x => decide (P x)) := by
      simp [v, List.count, List.countP_map, Function.comp_def]

/-- Inserting the same value into two sorted interlacing lists preserves
weak interlacing.  This is the list-level form of multiplying both
polynomials by the same linear factor. -/
lemma ListsInterlace.orderedInsert_same {lower upper : List ℝ}
    (h : ListsInterlace lower upper)
    (hlower : lower.Pairwise (· ≤ ·)) (hupper : upper.Pairwise (· ≤ ·))
    (a : ℝ) :
    ListsInterlace (lower.orderedInsert (· ≤ ·) a)
      (upper.orderedInsert (· ≤ ·) a) := by
  classical
  have hlowerInsert : (lower.orderedInsert (· ≤ ·) a).Pairwise (· ≤ ·) :=
    hlower.orderedInsert a lower
  have hupperInsert : (upper.orderedInsert (· ≤ ·) a).Pairwise (· ≤ ·) :=
    hupper.orderedInsert a upper
  apply ListsInterlace.of_card_bounds hlowerInsert hupperInsert
  · obtain ⟨hlen, _⟩ := h
    simp [List.orderedInsert_length, hlen]
  · intro x
    have hold := h.card_get_le_le x
    rw [card_fin_get_eq_countP lower (fun y ↦ y ≤ x),
      card_fin_get_eq_countP upper (fun y ↦ y ≤ x)] at hold
    rw [card_fin_get_eq_countP (lower.orderedInsert (· ≤ ·) a) (fun y ↦ y ≤ x),
      card_fin_get_eq_countP (upper.orderedInsert (· ≤ ·) a) (fun y ↦ y ≤ x)]
    rw [(List.perm_orderedInsert (· ≤ ·) a lower).countP_eq,
      (List.perm_orderedInsert (· ≤ ·) a upper).countP_eq]
    simp only [List.countP_cons]
    omega
  · intro x
    have hold := h.card_get_lt_le_add_one x
    rw [card_fin_get_eq_countP upper (fun y ↦ y < x),
      card_fin_get_eq_countP lower (fun y ↦ y < x)] at hold
    rw [card_fin_get_eq_countP (upper.orderedInsert (· ≤ ·) a) (fun y ↦ y < x),
      card_fin_get_eq_countP (lower.orderedInsert (· ≤ ·) a) (fun y ↦ y < x)]
    rw [(List.perm_orderedInsert (· ≤ ·) a upper).countP_eq,
      (List.perm_orderedInsert (· ≤ ·) a lower).countP_eq]
    simp only [List.countP_cons]
    omega

/-- Removing one occurrence of a repeated lower entry and one forced matching upper entry
preserves weak interlacing.  Distribution functions make the proof independent of where the
equal entries occur in the two sorted lists. -/
lemma ListsInterlace.erase_of_count_ge_two {lower upper : List ℝ}
    (h : ListsInterlace lower upper)
    (hlower : lower.Pairwise (· ≤ ·)) (hupper : upper.Pairwise (· ≤ ·))
    (a : ℝ) (ha : 2 ≤ lower.count a) :
    ListsInterlace (lower.erase a) (upper.erase a) := by
  classical
  have halower : a ∈ lower := List.count_pos_iff.mp (by omega)
  have hcountineq : lower.count a - 1 ≤ upper.count a := by
    have hle := h.card_get_le_le a
    have hlt := h.card_get_lt_le_add_one a
    have hlpart := card_fin_get_le_eq_add_lt_eq lower a
    have hupart := card_fin_get_le_eq_add_lt_eq upper a
    have hcount (l : List ℝ) :
        Fintype.card {k : Fin l.length // l.get k = a} = l.count a := by
      rw [Fintype.card_subtype]
      exact Fin.card_filter_univ_eq_vector_get_eq_count a ⟨l, rfl⟩
    rw [hcount lower] at hlpart
    rw [hcount upper] at hupart
    omega
  have haupperCount : 0 < upper.count a := by
    omega
  have haupper : a ∈ upper := List.count_pos_iff.mp haupperCount
  have hlowerErase : (lower.erase a).Pairwise (· ≤ ·) :=
    hlower.sublist List.erase_sublist
  have hupperErase : (upper.erase a).Pairwise (· ≤ ·) :=
    hupper.sublist List.erase_sublist
  apply ListsInterlace.of_card_bounds hlowerErase hupperErase
  · obtain ⟨hlen, _⟩ := h
    have hlpos : 0 < lower.length := List.length_pos_of_mem halower
    simp [List.length_erase_of_mem halower, List.length_erase_of_mem haupper, hlen]
    omega
  · intro x
    have hold := h.card_get_le_le x
    rw [card_fin_get_eq_countP lower (fun y => y ≤ x),
      card_fin_get_eq_countP upper (fun y => y ≤ x)] at hold
    rw [card_fin_get_eq_countP (lower.erase a) (fun y => y ≤ x),
      card_fin_get_eq_countP (upper.erase a) (fun y => y ≤ x)]
    rw [List.countP_erase, List.countP_erase]
    by_cases hax : a ≤ x
    · simp [halower, haupper, hax] at hold ⊢
      omega
    · simp [halower, haupper, hax] at hold ⊢
      exact hold
  · intro x
    have hold := h.card_get_lt_le_add_one x
    rw [card_fin_get_eq_countP upper (fun y => y < x),
      card_fin_get_eq_countP lower (fun y => y < x)] at hold
    rw [card_fin_get_eq_countP (upper.erase a) (fun y => y < x),
      card_fin_get_eq_countP (lower.erase a) (fun y => y < x)]
    rw [List.countP_erase, List.countP_erase]
    by_cases hax : a < x
    · simp [halower, haupper, hax] at hold ⊢
      omega
    · simp [halower, haupper, hax] at hold ⊢
      exact hold

/-- A weakly interlacing longer list contains every repeated value of the shorter list with
all but possibly one copy.  This is the multiplicity statement lost by intervalwise IVT. -/
lemma ListsInterlace.count_sub_one_le_count {lower upper : List ℝ}
    (h : ListsInterlace lower upper) (a : ℝ) :
    lower.count a - 1 ≤ upper.count a := by
  classical
  have hle := h.card_get_le_le a
  have hlt := h.card_get_lt_le_add_one a
  have hlpart := card_fin_get_le_eq_add_lt_eq lower a
  have hupart := card_fin_get_le_eq_add_lt_eq upper a
  have hcount (l : List ℝ) :
      Fintype.card {k : Fin l.length // l.get k = a} = l.count a := by
    rw [Fintype.card_subtype]
    exact Fin.card_filter_univ_eq_vector_get_eq_count a ⟨l, rfl⟩
  rw [hcount lower] at hlpart
  rw [hcount upper] at hupart
  omega

/-- Consequently, every polynomial interlaced by `q` has each root of `q` with multiplicity
at least `q`'s multiplicity minus one. -/
lemma PolynomialInterlaces.rootMultiplicity_sub_one_le
    {q p : ℝ[X]} (h : PolynomialInterlaces q p) (a : ℝ) :
    q.rootMultiplicity a - 1 ≤ p.rootMultiplicity a := by
  rcases h with ⟨_q0, _p0, _qm, _pm, _qs, _ps, hl⟩
  have hc := hl.count_sub_one_le_count a
  rw [← Multiset.coe_count a (q.roots.sort (· ≤ ·)),
    ← Multiset.coe_count a (p.roots.sort (· ≤ ·))] at hc
  rw [Multiset.sort_eq, Multiset.sort_eq, count_roots, count_roots] at hc
  exact hc

/-- If `a` is a repeated root of an interlacer, then `a` is a forced common root.  Dividing one
copy from both polynomials preserves interlacing. -/
lemma PolynomialInterlaces.divByMonic_X_sub_C_of_two_le_rootMultiplicity
    {q p : ℝ[X]} (h : PolynomialInterlaces q p) (a : ℝ)
    (ha : 2 ≤ q.rootMultiplicity a) :
    PolynomialInterlaces (q /ₘ (X - C a)) (p /ₘ (X - C a)) := by
  classical
  rcases h with ⟨hq0, hp0, hqmonic, hpmonic, hqsplit, hpsplit, hlists⟩
  have hqroot : q.IsRoot a := (rootMultiplicity_pos hq0).mp (by omega)
  have hpmult : 1 ≤ p.rootMultiplicity a := by
    have := PolynomialInterlaces.rootMultiplicity_sub_one_le
      ⟨hq0, hp0, hqmonic, hpmonic, hqsplit, hpsplit, hlists⟩ a
    omega
  have hproot : p.IsRoot a := (rootMultiplicity_pos hp0).mp (by omega)
  let q' := q /ₘ (X - C a)
  let p' := p /ₘ (X - C a)
  have hqmul : (X - C a) * q' = q := by
    simpa [q'] using (mul_divByMonic_eq_iff_isRoot.mpr hqroot)
  have hpmul : (X - C a) * p' = p := by
    simpa [p'] using (mul_divByMonic_eq_iff_isRoot.mpr hproot)
  have hqprodMonic : ((X - C a) * q').Monic := by rw [hqmul]; exact hqmonic
  have hpprodMonic : ((X - C a) * p').Monic := by rw [hpmul]; exact hpmonic
  have hq'monic : q'.Monic := (monic_X_sub_C a).of_mul_monic_left hqprodMonic
  have hp'monic : p'.Monic := (monic_X_sub_C a).of_mul_monic_left hpprodMonic
  have hq'split : q'.Splits := by
    have hprod : ((X - C a) * q').Splits := by rw [hqmul]; exact hqsplit
    exact (splits_mul_iff (X_sub_C_ne_zero a) hq'monic.ne_zero).mp hprod |>.2
  have hp'split : p'.Splits := by
    have hprod : ((X - C a) * p').Splits := by rw [hpmul]; exact hpsplit
    exact (splits_mul_iff (X_sub_C_ne_zero a) hp'monic.ne_zero).mp hprod |>.2
  let lower := q.roots.sort (· ≤ ·)
  let upper := p.roots.sort (· ≤ ·)
  have hlower : lower.Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort (s := q.roots) (r := (· ≤ ·))
  have hupper : upper.Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort (s := p.roots) (r := (· ≤ ·))
  have hacount : 2 ≤ lower.count a := by
    rw [← Multiset.coe_count a lower, Multiset.sort_eq, count_roots]
    exact ha
  have herased : ListsInterlace (lower.erase a) (upper.erase a) :=
    hlists.erase_of_count_ge_two hlower hupper a hacount
  have hqroots : q'.roots = q.roots.erase a := by
    have heq : q.roots = {a} + q'.roots := by
      rw [← hqmul, roots_mul (mul_ne_zero (X_sub_C_ne_zero a) hq'monic.ne_zero),
        roots_X_sub_C]
    rw [heq]
    symm
    simpa only [Multiset.singleton_add] using Multiset.erase_cons_head a q'.roots
  have hproots : p'.roots = p.roots.erase a := by
    have heq : p.roots = {a} + p'.roots := by
      rw [← hpmul, roots_mul (mul_ne_zero (X_sub_C_ne_zero a) hp'monic.ne_zero),
        roots_X_sub_C]
    rw [heq]
    symm
    simpa only [Multiset.singleton_add] using Multiset.erase_cons_head a p'.roots
  have hqsort : q'.roots.sort (· ≤ ·) = lower.erase a := by
    apply List.Perm.eq_of_pairwise'
      (Multiset.pairwise_sort (s := q'.roots) (r := (· ≤ ·)))
      (hlower.sublist List.erase_sublist)
    apply Multiset.coe_eq_coe.mp
    rw [Multiset.sort_eq, hqroots]
    rw [← Multiset.coe_erase, Multiset.sort_eq]
  have hpsort : p'.roots.sort (· ≤ ·) = upper.erase a := by
    apply List.Perm.eq_of_pairwise'
      (Multiset.pairwise_sort (s := p'.roots) (r := (· ≤ ·)))
      (hupper.sublist List.erase_sublist)
    apply Multiset.coe_eq_coe.mp
    rw [Multiset.sort_eq, hproots]
    rw [← Multiset.coe_erase, Multiset.sort_eq]
  refine ⟨hq'monic.ne_zero, hp'monic.ne_zero, hq'monic, hp'monic, hq'split, hp'split, ?_⟩
  rw [hqsort, hpsort]
  exact herased

/-! ## A sign criterion at distinct test points -/

/-- A monic polynomial of degree one more than a strictly increasing list of test points splits
if its values have the weak alternating signs dictated by interlacing.

The proof removes the last test point.  If it is already a root, use it; otherwise the final
sign is negative and monicity supplies a root to its right.  Dividing by that linear factor
flips all earlier signs and gives the induction hypothesis.  This argument deliberately permits
zero endpoint values. -/
lemma splits_of_monic_of_pairwise_lt_of_alternating_sign
    (p : ℝ[X]) (l : List ℝ) (hp : p.Monic)
    (hdeg : p.natDegree = l.length + 1)
    (hl : l.Pairwise (· < ·))
    (hsign : ∀ (k : ℕ) (hk : k < l.length),
      0 ≤ p.eval (l.get ⟨k, hk⟩) * (-1 : ℝ) ^ (l.length - k)) :
    p.Splits := by
  induction l using List.reverseRecOn generalizing p with
  | nil =>
      exact Splits.of_natDegree_eq_one (by simpa using hdeg)
  | append_singleton l a ih =>
      have hl' : l.Pairwise (· < ·) := (List.pairwise_append.mp hl).1
      have hxa : ∀ x ∈ l, x < a := by
        intro x hx
        exact (List.pairwise_append.mp hl).2.2 x hx a (by simp)
      have hlastSign := hsign l.length (by simp)
      have hpa : p.eval a ≤ 0 := by
        simpa using hlastSign
      have hroot : ∃ r : ℝ, a ≤ r ∧ p.IsRoot r := by
        by_cases hpa0 : p.eval a = 0
        · exact ⟨a, le_rfl, hpa0⟩
        · have hpalt : p.eval a < 0 := lt_of_le_of_ne hpa hpa0
          have hpdegNat : 0 < p.natDegree := by
            rw [hdeg]
            simp
          have hpdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp hpdegNat
          have heventually : ∀ᶠ b in Filter.atTop, 0 < p.eval b :=
            (p.tendsto_atTop_of_leadingCoeff_nonneg hpdeg (by simp [hp.leadingCoeff])).eventually_gt_atTop 0
          obtain ⟨z, hz⟩ := Filter.Eventually.exists_forall_of_atTop heventually
          let b := max (a + 1) z
          have hab : a ≤ b := le_trans (by linarith) (le_max_left _ _)
          have hpb : 0 < p.eval b := hz b (le_max_right _ _)
          obtain ⟨r, hr, hreval⟩ := (Set.mem_image _ _ _).mp
            (intermediate_value_Icc hab p.continuous.continuousOn ⟨hpalt.le, hpb.le⟩)
          exact ⟨r, hr.1, by simpa [IsRoot] using hreval⟩
      obtain ⟨r, har, hr⟩ := hroot
      let R := p /ₘ (X - C r)
      have hmul : (X - C r) * R = p := by
        simpa [R] using (mul_divByMonic_eq_iff_isRoot.mpr hr)
      have hprodMonic : ((X - C r) * R).Monic := by rw [hmul]; exact hp
      have hRmonic : R.Monic := (monic_X_sub_C r).of_mul_monic_left hprodMonic
      have hRdeg : R.natDegree = l.length + 1 := by
        dsimp [R]
        rw [natDegree_divByMonic p (monic_X_sub_C r), natDegree_X_sub_C, hdeg]
        simp
      have hRsign : ∀ (k : ℕ) (hk : k < l.length),
          0 ≤ R.eval (l.get ⟨k, hk⟩) * (-1 : ℝ) ^ (l.length - k) := by
        intro k hk
        let x := l.get ⟨k, hk⟩
        have hxmem : x ∈ l := List.get_mem l ⟨k, hk⟩
        have hxr : x < r := (hxa x hxmem).trans_le har
        have hsold := hsign k (by simp; omega)
        have hget : (l ++ [a]).get ⟨k, by simp; omega⟩ = x := by
          change (l ++ [a])[k]'(by simp; omega) = l[k]'hk
          exact List.getElem_append_left hk
        rw [hget] at hsold
        change 0 ≤ p.eval x * (-1 : ℝ) ^ ((l ++ [a]).length - k) at hsold
        have hexp : (l ++ [a]).length - k = (l.length - k) + 1 := by
          simp
          omega
        have heval :
            p.eval x * (-1 : ℝ) ^ ((l ++ [a]).length - k) =
              (r - x) * (R.eval x * (-1 : ℝ) ^ (l.length - k)) := by
          rw [hexp, pow_succ, ← hmul, eval_mul, eval_sub, eval_X, eval_C]
          ring
        rw [heval] at hsold
        rw [mul_comm] at hsold
        exact nonneg_of_mul_nonneg_left hsold (sub_pos.mpr hxr)
      have hRsplit : R.Splits := ih R hRmonic hRdeg hl' hRsign
      rw [← hmul]
      exact (splits_mul_iff (X_sub_C_ne_zero r) hRmonic.ne_zero).mpr
        ⟨Splits.X_sub_C r, hRsplit⟩

/-- If `q` interlaces `p` and `q` is nonconstant, the penultimate sorted root of `p` is bounded by
the largest root of `q`. -/
lemma PolynomialInterlaces.penultimate_root_le_interlacer_largest
    {q p : ℝ[X]} (h : PolynomialInterlaces q p) (hqdeg : 0 < q.natDegree) :
    ∃ (a r : ℝ), IsLargestRoot q a ∧ p.IsRoot r ∧ r ≤ a := by
  rcases h with ⟨hq0, hp0, _hqmonic, _hpmonic, hqsplit, _hpsplit, hinterlace⟩
  let lower := q.roots.sort (· ≤ ·)
  let upper := p.roots.sort (· ≤ ·)
  have hlower_pos : 0 < lower.length := by
    calc
      0 < q.natDegree := hqdeg
      _ = q.roots.card := hqsplit.natDegree_eq_card_roots
      _ = lower.length := by simp [lower]
  have hlower : lower ≠ [] := List.ne_nil_of_length_pos hlower_pos
  obtain ⟨k, hk, _hkpos⟩ := hinterlace.penultimate_le_last hlower
  let a := lower.getLast hlower
  let r := upper.get k
  have ha : IsLargestRoot q a := by
    simpa [a, lower] using sortedRoots_getLast_isLargest hq0 hlower
  have hrmem : r ∈ p.roots := by
    exact (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mp
      (List.get_mem upper k)
  have hr : p.IsRoot r := (mem_roots hp0).mp hrmem
  exact ⟨a, r, ha, hr, by simpa [a, r, lower, upper] using hk⟩

/-- Strict upper-tail sign control supplied by a genuine common interlacer.

The strict inequality is essential for weak interlacing: if `p` and its interlacer share a root
at `x`, then `p.eval x = 0` need not imply that `x` bounds the final root of `p`. -/
lemma PolynomialInterlaces.rootUpperBound_of_eval_pos
    {q p : ℝ[X]} (h : PolynomialInterlaces q p) {x : ℝ}
    (hqx : IsRootUpperBound q x) (hpx : 0 < p.eval x) :
    IsRootUpperBound p x := by
  rcases h with ⟨hq0, hp0, _hqmonic, hpmonic, _hqsplit, hpsplit, hinterlace⟩
  let lower := q.roots.sort (· ≤ ·)
  let upper := p.roots.sort (· ≤ ·)
  obtain ⟨hlen, hentries⟩ := hinterlace
  change upper.length = lower.length + 1 at hlen
  have hinterlace' : ListsInterlace lower upper := ⟨hlen, hentries⟩
  have hupper_pos : 0 < upper.length := by
    rw [hlen]
    omega
  have hupper : upper ≠ [] := List.ne_nil_of_length_pos hupper_pos
  have hdrop : ∀ r ∈ upper.dropLast, r ≤ x := by
    by_cases hlower : lower = []
    · have hdropnil : upper.dropLast = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hlower_len : lower.length = 0 := by simp [hlower]
        have hupper_len : upper.length = 1 := by omega
        simp [hupper_len]
      simp [hdropnil]
    · have hlowerSorted : lower.Pairwise (· ≤ ·) := by
        exact Multiset.pairwise_sort (s := q.roots) (r := (· ≤ ·))
      have hlastmem : lower.getLast hlower ∈ q.roots :=
        (Multiset.mem_sort (s := q.roots) (r := (· ≤ ·))).mp (List.getLast_mem hlower)
      have hlastle : lower.getLast hlower ≤ x :=
        hqx _ ((mem_roots hq0).mp hlastmem)
      intro r hr
      exact (hinterlace'.dropLast_le_last hlower hlowerSorted r hr).trans hlastle
  have hprefix_nonneg :
      0 ≤ ((upper.dropLast).map (fun r => x - r)).prod := by
    apply List.prod_nonneg
    intro y hy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
    exact sub_nonneg.mpr (hdrop r hr)
  have heval :
      p.eval x = ((upper.dropLast).map (fun r => x - r)).prod *
        (x - upper.getLast hupper) := by
    rw [hpsplit.eval_eq_prod_roots_of_monic hpmonic]
    rw [← Multiset.sort_eq (s := p.roots) (r := (· ≤ ·))]
    change (upper.map (fun r => x - r)).prod = _
    conv_lhs => rw [← List.dropLast_append_getLast hupper]
    simp
  have hlastlt : upper.getLast hupper < x := by
    by_contra hnot
    have hfactor : x - upper.getLast hupper ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
    have : p.eval x ≤ 0 := by
      rw [heval]
      exact mul_nonpos_of_nonneg_of_nonpos hprefix_nonneg hfactor
    linarith
  have hlargest : IsLargestRoot p (upper.getLast hupper) := by
    simpa [upper] using sortedRoots_getLast_isLargest hp0 hupper
  intro r hr
  exact (hlargest.upperBound r hr).trans hlastlt.le

/-- If `q` interlaces `p`, every root of `q` is bounded by every largest-root bound for `p`. -/
lemma PolynomialInterlaces.interlacer_rootUpperBound
    {q p : ℝ[X]} (h : PolynomialInterlaces q p) {x : ℝ}
    (hpx : IsRootUpperBound p x) : IsRootUpperBound q x := by
  rcases h with ⟨hq0, hp0, _hqmonic, _hpmonic, _hqsplit, _hpsplit, hinterlace⟩
  let lower := q.roots.sort (· ≤ ·)
  let upper := p.roots.sort (· ≤ ·)
  obtain ⟨hlen, hentries⟩ := hinterlace
  change upper.length = lower.length + 1 at hlen
  intro r hr
  have hrmem : r ∈ lower := by
    exact (Multiset.mem_sort (s := q.roots) (r := (· ≤ ·))).mpr
      ((mem_roots hq0).mpr hr)
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hrmem
  have hright := (hentries k.val k.isLt).2
  have hkupper : k.val + 1 < upper.length := by omega
  have huppermem : upper.get ⟨k.val + 1, hkupper⟩ ∈ p.roots := by
    apply (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mp
    exact List.get_mem upper _
  have hupperroot : p.IsRoot (upper.get ⟨k.val + 1, hkupper⟩) :=
    (mem_roots hp0).mp huppermem
  rw [← hk]
  exact hright.trans (hpx _ hupperroot)

/-- A finite family has a common interlacer if one polynomial interlaces every member. -/
def HasCommonInterlacer {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ[X]) : Prop :=
  ∃ q : ℝ[X], ∀ i ∈ s, PolynomialInterlaces q (p i)

/-- All members of a common-interlacing family have the same degree. -/
lemma HasCommonInterlacer.same_natDegree {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {p : ι → ℝ[X]} (h : HasCommonInterlacer s p)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) : (p i).natDegree = (p j).natDegree := by
  obtain ⟨q, hq⟩ := h
  rw [(hq i hi).natDegree_eq_succ, (hq j hj).natDegree_eq_succ]

/-- Restricting the index set preserves a common interlacer. -/
lemma HasCommonInterlacer.mono {ι : Type*} [DecidableEq ι]
    {s t : Finset ι} {p : ι → ℝ[X]} (h : HasCommonInterlacer t p) (hst : s ⊆ t) :
    HasCommonInterlacer s p := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, fun i hi => hq i (hst hi)⟩

/-- Deleting one polynomial from a family preserves its common interlacer. -/
lemma HasCommonInterlacer.erase {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {p : ι → ℝ[X]} (h : HasCommonInterlacer s p) (i : ι) :
    HasCommonInterlacer (s.erase i) p :=
  h.mono (Finset.erase_subset i s)

/-! ## Convex combinations and the elementary selection step -/

/-- A finite weighted sum of real polynomials. -/
noncomputable def polynomialWeightedSum {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (p : ι → ℝ[X]) : ℝ[X] :=
  ∑ i ∈ s, w i • p i

@[simp] lemma eval_polynomialWeightedSum {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (p : ι → ℝ[X]) (x : ℝ) :
    (polynomialWeightedSum s w p).eval x = ∑ i ∈ s, w i * (p i).eval x := by
  simp [polynomialWeightedSum, eval_finset_sum, eval_smul, smul_eq_mul]

/-- Nonnegative weights preserve the weak alternating endpoint signs supplied by a common
interlacer. -/
lemma eval_polynomialWeightedSum_at_commonInterlacerRoot_sign
    {ι : Type*} {s : Finset ι} (w : ι → ℝ) (p : ι → ℝ[X]) (q : ℝ[X])
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hq : ∀ i ∈ s, PolynomialInterlaces q (p i))
    (k : ℕ) (hk : k < (q.roots.sort (· ≤ ·)).length) :
    0 ≤ (polynomialWeightedSum s w p).eval
        ((q.roots.sort (· ≤ ·)).get ⟨k, hk⟩) *
      (-1 : ℝ) ^ ((q.roots.sort (· ≤ ·)).length - k) := by
  rw [eval_polynomialWeightedSum, Finset.sum_mul]
  apply Finset.sum_nonneg
  intro i hi
  rw [mul_assoc]
  exact mul_nonneg (hw i hi) ((hq i hi).eval_at_interlacerRoot_sign k hk)

/-- The IVT consequence of the alternating-sign lemma: a nonnegatively weighted sum has a root
between every two consecutive (multiplicity-indexed) roots of the common interlacer.

When the two endpoints coincide this still gives the forced common root.  The remaining issue in
the full weak-interlacing closure theorem is to recover the required *multiplicity count* when
several such intervals collapse to the same repeated endpoint. -/
lemma exists_weightedSum_root_between_interlacerRoots
    {ι : Type*} {s : Finset ι} (w : ι → ℝ) (p : ι → ℝ[X]) (q : ℝ[X])
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hq : ∀ i ∈ s, PolynomialInterlaces q (p i))
    (k : ℕ) (hk : k + 1 < (q.roots.sort (· ≤ ·)).length) :
    ∃ x : ℝ,
      (q.roots.sort (· ≤ ·)).get ⟨k, by omega⟩ ≤ x ∧
      x ≤ (q.roots.sort (· ≤ ·)).get ⟨k + 1, hk⟩ ∧
      (polynomialWeightedSum s w p).IsRoot x := by
  let lower := q.roots.sort (· ≤ ·)
  let P := polynomialWeightedSum s w p
  have hkLower : k + 1 < lower.length := by simpa [lower] using hk
  let a := lower.get ⟨k, by omega⟩
  let b := lower.get ⟨k + 1, hkLower⟩
  let m := lower.length - (k + 1)
  have hk0 : k < lower.length := by omega
  have hab : a ≤ b := by
    have hsorted : lower.Pairwise (· ≤ ·) := by
      exact Multiset.pairwise_sort (s := q.roots) (r := (· ≤ ·))
    dsimp [a, b]
    exact hsorted.rel_get_of_le (by simp)
  have haSign :
      0 ≤ P.eval a * (-1 : ℝ) ^ (m + 1) := by
    have ha := eval_polynomialWeightedSum_at_commonInterlacerRoot_sign
      w p q hw hq k (by simpa [lower] using hk0)
    change 0 ≤ P.eval a * (-1 : ℝ) ^ (lower.length - k) at ha
    rw [show lower.length - k = m + 1 by dsimp [m]; omega] at ha
    exact ha
  have hbSign : 0 ≤ P.eval b * (-1 : ℝ) ^ m := by
    have hb := eval_polynomialWeightedSum_at_commonInterlacerRoot_sign
      w p q hw hq (k + 1) (by simpa [lower] using hk)
    change 0 ≤ P.eval b * (-1 : ℝ) ^ (lower.length - (k + 1)) at hb
    change 0 ≤ P.eval b * (-1 : ℝ) ^ m
    exact hb
  rcases neg_one_pow_eq_or ℝ m with hm | hm
  · have haNonpos : P.eval a ≤ 0 := by
      rw [pow_succ, hm] at haSign
      norm_num at haSign ⊢
      exact haSign
    have hbNonneg : 0 ≤ P.eval b := by simpa [hm] using hbSign
    obtain ⟨x, hx, hxeval⟩ := (Set.mem_image _ _ _).mp
      (intermediate_value_Icc hab P.continuous.continuousOn ⟨haNonpos, hbNonneg⟩)
    exact ⟨x, by simpa [a, lower] using hx.1, by simpa [b, lower] using hx.2,
      by simpa [P, IsRoot] using hxeval⟩
  · have haNonneg : 0 ≤ P.eval a := by
      rw [pow_succ, hm] at haSign
      norm_num at haSign ⊢
      exact haSign
    have hbNonpos : P.eval b ≤ 0 := by
      rw [hm] at hbSign
      norm_num at hbSign ⊢
      exact hbSign
    obtain ⟨x, hx, hxeval⟩ := (Set.mem_image _ _ _).mp
      (intermediate_value_Icc' hab P.continuous.continuousOn ⟨hbNonpos, haNonneg⟩)
    exact ⟨x, by simpa [a, lower] using hx.1, by simpa [b, lower] using hx.2,
      by simpa [P, IsRoot] using hxeval⟩

/-- The algebraic half of convex closure.  A normalized weighted sum of polynomials sharing an
interlacer is monic and retains their common degree.  Positivity of the weights is not needed for
this coefficient calculation. -/
lemma monic_polynomialWeightedSum_of_commonInterlacer
    {ι : Type*} {s : Finset ι}
    (w : ι → ℝ) (p : ι → ℝ[X]) (q : ℝ[X])
    (hq : ∀ i ∈ s, PolynomialInterlaces q (p i))
    (hwsum : ∑ i ∈ s, w i = 1) :
    (polynomialWeightedSum s w p).Monic ∧
      (polynomialWeightedSum s w p).natDegree = q.natDegree + 1 := by
  classical
  let d := q.natDegree + 1
  have hdegree : ∀ i ∈ s, (p i).natDegree = d := by
    intro i hi
    simpa [d] using (hq i hi).natDegree_eq_succ
  have hdegree_le : (polynomialWeightedSum s w p).natDegree ≤ d := by
    rw [polynomialWeightedSum]
    apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_smul_le (w i) (p i)).trans_eq (hdegree i hi)
  have hcoeff : (polynomialWeightedSum s w p).coeff d = 1 := by
    rw [polynomialWeightedSum]
    rw [finset_sum_coeff]
    simp_rw [coeff_smul, smul_eq_mul]
    calc
      ∑ i ∈ s, w i * (p i).coeff d = ∑ i ∈ s, w i * 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hdegree i hi, (hq i hi).2.2.2.1.coeff_natDegree]
      _ = 1 := by simpa using hwsum
  have hmonic : (polynomialWeightedSum s w p).Monic :=
    monic_of_natDegree_le_of_coeff_eq_one d hdegree_le hcoeff
  refine ⟨hmonic, ?_⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero hdegree_le (hcoeff.trans_ne one_ne_zero)

/-- Repeated roots of the common interlacer survive a normalized weighted sum with all but
possibly one copy.  Unlike the IVT interval argument, this statement counts multiplicity. -/
lemma rootMultiplicity_sub_one_le_polynomialWeightedSum
    {ι : Type*} {s : Finset ι}
    (w : ι → ℝ) (p : ι → ℝ[X]) (q : ℝ[X])
    (hq : ∀ i ∈ s, PolynomialInterlaces q (p i))
    (hwsum : ∑ i ∈ s, w i = 1) (a : ℝ) :
    q.rootMultiplicity a - 1 ≤
      (polynomialWeightedSum s w p).rootMultiplicity a := by
  classical
  have hmonic := (monic_polynomialWeightedSum_of_commonInterlacer w p q hq hwsum).1
  rw [le_rootMultiplicity_iff hmonic.ne_zero]
  rw [polynomialWeightedSum]
  apply Finset.dvd_sum
  intro i hi
  rw [Polynomial.smul_eq_C_mul]
  exact dvd_mul_of_dvd_right
    ((le_rootMultiplicity_iff (hq i hi).2.1).mp
      ((hq i hi).rootMultiplicity_sub_one_le a)) _

/-- Convex closure when the common interlacer has no repeated roots.  The weighted endpoint
signs and the preceding distinct-point sign criterion give real-rootedness directly. -/
lemma realRooted_polynomialWeightedSum_of_commonInterlacer_of_roots_nodup
    {ι : Type*} {s : Finset ι}
    (w : ι → ℝ) (p : ι → ℝ[X]) (q : ℝ[X])
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hq : ∀ i ∈ s, PolynomialInterlaces q (p i))
    (hwsum : ∑ i ∈ s, w i = 1) (hqnodup : q.roots.Nodup) :
    RealRooted (polynomialWeightedSum s w p) := by
  classical
  let lower := q.roots.sort (· ≤ ·)
  let P := polynomialWeightedSum s w p
  have hmonoDeg := monic_polynomialWeightedSum_of_commonInterlacer w p q hq hwsum
  have hlpair : lower.Pairwise (· < ·) := by
    apply List.SortedLT.pairwise
    apply List.SortedLE.sortedLT_of_nodup
    · exact (Multiset.pairwise_sort (s := q.roots) (r := (· ≤ ·))).sortedLE
    · apply Multiset.coe_nodup.mp
      rw [Multiset.sort_eq]
      exact hqnodup
  have hdeg : P.natDegree = lower.length + 1 := by
    rw [hmonoDeg.2]
    congr 1
    obtain ⟨i, hi⟩ : s.Nonempty := by
      by_contra hs0
      simp only [Finset.not_nonempty_iff_eq_empty] at hs0
      simp [hs0] at hwsum
    have hqsplit := (hq i hi).2.2.2.2.1
    rw [hqsplit.natDegree_eq_card_roots]
    simp [lower]
  apply splits_of_monic_of_pairwise_lt_of_alternating_sign P lower hmonoDeg.1 hdeg hlpair
  intro k hk
  simpa [P, lower] using
    eval_polynomialWeightedSum_at_commonInterlacerRoot_sign w p q hw hq k
      (by simpa [lower] using hk)

/-- Nonnegative normalized weighted sums of a common-interlacing family are real-rooted.

Repeated roots are removed recursively.  Such a root is forced in every family member, and the
preceding division lemma preserves common interlacing.  The recursion terminates at a squarefree
interlacer, where the alternating-sign criterion applies. -/
lemma realRooted_polynomialWeightedSum_of_commonInterlacer
    {ι : Type*} {s : Finset ι}
    (w : ι → ℝ) (p : ι → ℝ[X]) (q : ℝ[X])
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hq : ∀ i ∈ s, PolynomialInterlaces q (p i))
    (hwsum : ∑ i ∈ s, w i = 1) :
    RealRooted (polynomialWeightedSum s w p) := by
  classical
  let motive := fun n : ℕ => ∀ (p : ι → ℝ[X]) (q : ℝ[X]),
    q.natDegree = n → (∀ i ∈ s, PolynomialInterlaces q (p i)) →
      RealRooted (polynomialWeightedSum s w p)
  suffices hall : ∀ n, motive n by
    exact hall q.natDegree p q rfl hq
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p q hn hq
      by_cases hqnodup : q.roots.Nodup
      · exact realRooted_polynomialWeightedSum_of_commonInterlacer_of_roots_nodup
          w p q hw hq hwsum hqnodup
      · have hcountNot : ¬ ∀ a : ℝ, q.roots.count a ≤ 1 := by
          intro hall
          exact hqnodup (Multiset.nodup_iff_count_le_one.mpr hall)
        push Not at hcountNot
        obtain ⟨a, haCount⟩ := hcountNot
        have ha : 2 ≤ q.rootMultiplicity a := by
          rw [← count_roots]
          omega
        let q' := q /ₘ (X - C a)
        let p' := fun i => p i /ₘ (X - C a)
        have hq' : ∀ i ∈ s, PolynomialInterlaces q' (p' i) := by
          intro i hi
          exact (hq i hi).divByMonic_X_sub_C_of_two_le_rootMultiplicity a ha
        have hqNat : 2 ≤ q.natDegree := by
          obtain ⟨i, hi⟩ : s.Nonempty := by
            by_contra hs0
            simp only [Finset.not_nonempty_iff_eq_empty] at hs0
            simp [hs0] at hwsum
          have hqsplit := (hq i hi).2.2.2.2.1
          calc
            2 ≤ q.roots.count a := by simpa [count_roots] using ha
            _ ≤ q.roots.card := Multiset.count_le_card _ _
            _ = q.natDegree := hqsplit.natDegree_eq_card_roots.symm
        have hq'deg : q'.natDegree < n := by
          dsimp [q']
          rw [natDegree_divByMonic q (monic_X_sub_C a), natDegree_X_sub_C, hn]
          omega
        have hrec : RealRooted (polynomialWeightedSum s w p') :=
          ih q'.natDegree hq'deg p' q' rfl hq'
        have hfactor : polynomialWeightedSum s w p =
            (X - C a) * polynomialWeightedSum s w p' := by
          rw [polynomialWeightedSum, polynomialWeightedSum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hproot : (p i).IsRoot a := by
            have hmult := (hq i hi).rootMultiplicity_sub_one_le a
            exact (rootMultiplicity_pos (hq i hi).2.1).mp (by omega)
          have hmul : (X - C a) * p' i = p i := by
            simpa [p'] using (mul_divByMonic_eq_iff_isRoot.mpr hproot)
          rw [← hmul]
          simp only [Polynomial.smul_eq_C_mul]
          ring
        rw [hfactor]
        exact (Splits.X_sub_C a).mul hrec

/-- In particular, convex combinations of a common-interlacing family are automatically monic. -/
lemma HasCommonInterlacer.monic_polynomialWeightedSum
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {p : ι → ℝ[X]}
    (h : HasCommonInterlacer s p) (w : ι → ℝ)
    (hwsum : ∑ i ∈ s, w i = 1) : (polynomialWeightedSum s w p).Monic := by
  obtain ⟨q, hq⟩ := h
  exact (monic_polynomialWeightedSum_of_commonInterlacer w p q hq hwsum).1

/-- At a root of a convex combination, at least one positively weighted member is nonnegative.

This is the order-theoretic selection step in the common-interlacer argument; it requires no
polynomial root theory. -/
lemma exists_nonnegative_eval_of_convex_root {ι : Type*}
    {s : Finset ι} (w : ι → ℝ) (p : ι → ℝ[X])
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1) (x : ℝ)
    (hx : (polynomialWeightedSum s w p).IsRoot x) :
    ∃ i ∈ s, 0 < w i ∧ 0 ≤ (p i).eval x := by
  have hsum_eval : ∑ i ∈ s, w i * (p i).eval x = 0 := by
    simpa [IsRoot] using hx
  have hwpos : ∃ i ∈ s, 0 < w i := by
    rw [← Finset.sum_pos_iff_of_nonneg hw, hwsum]
    norm_num
  by_contra h
  push Not at h
  have hle : ∀ i ∈ s, w i * (p i).eval x ≤ 0 := by
    intro i hi
    by_cases hwi : w i = 0
    · simp [hwi]
    · exact mul_nonpos_of_nonneg_of_nonpos (hw i hi)
        (le_of_lt (h i hi (lt_of_le_of_ne (hw i hi) (Ne.symm hwi))))
  obtain ⟨j, hjs, hwj⟩ := hwpos
  have hjlt : w j * (p j).eval x < 0 :=
    mul_neg_of_pos_of_neg hwj (h j hjs hwj)
  have : ∑ i ∈ s, w i * (p i).eval x < ∑ _i ∈ s, (0 : ℝ) :=
    Finset.sum_lt_sum hle ⟨j, hjs, by simpa using hjlt⟩
  simp [hsum_eval] at this

/-- If a nonnegatively weighted sum has positive value, one positively weighted member has
positive value. -/
lemma exists_positive_eval_of_weightedSum_pos {ι : Type*}
    {s : Finset ι} (w : ι → ℝ) (p : ι → ℝ[X])
    (hw : ∀ i ∈ s, 0 ≤ w i) (x : ℝ)
    (hx : 0 < (polynomialWeightedSum s w p).eval x) :
    ∃ i ∈ s, 0 < w i ∧ 0 < (p i).eval x := by
  have hsum : 0 < ∑ i ∈ s, w i * (p i).eval x := by simpa using hx
  have hterm : ∃ i ∈ s, 0 < w i * (p i).eval x := by
    by_contra h
    push Not at h
    have hnonpos : ∑ i ∈ s, w i * (p i).eval x ≤ 0 :=
      Finset.sum_nonpos fun i hi => h i hi
    linarith
  obtain ⟨i, hi, hprod⟩ := hterm
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact ⟨i, hi, hpos.1, hpos.2⟩
  · exact (not_lt_of_ge (hw i hi) hneg.1).elim

/-- A finite-family closedness principle for largest-root bounds.  If arbitrarily close points to
the right of `x` bound all roots of some family member, then one fixed member is already bounded by
`x`. -/
lemma exists_rootUpperBound_at_of_forall_gt
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (p : ι → ℝ[X]) (x : ℝ)
    (hnear : ∀ y, x < y → ∃ i ∈ s, IsRootUpperBound (p i) y) :
    ∃ i ∈ s, IsRootUpperBound (p i) x := by
  classical
  by_contra hnone
  simp only [not_exists, not_and] at hnone
  let S := {i // i ∈ s}
  letI : Nonempty S := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have hroot : ∀ i : S, ∃ r : ℝ, (p i).IsRoot r ∧ x < r := by
    intro i
    have hi := hnone i i.property
    rw [IsRootUpperBound] at hi
    push Not at hi
    exact hi
  choose r hrroot hrgt using hroot
  obtain ⟨j, _hj, hjmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset S) (fun i => r i - x)
      Finset.univ_nonempty
  let δ : ℝ := (r j - x) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [hrgt j]
  obtain ⟨i, hi, hibound⟩ := hnear (x + δ) (by linarith)
  let iS : S := ⟨i, hi⟩
  have hmin : r j - x ≤ r iS - x := hjmin iS (Finset.mem_univ _)
  have hrile : r iS ≤ x + δ := hibound (r iS) (hrroot iS)
  dsimp [δ] at hδ hrile
  linarith

/-! ## Common-interlacer selection -/

/-- A common interlacer together with its now-proved strict upper-tail sign consequence. -/
structure CommonUpperInterlacerCertificate {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ[X]) where
  interlacer : ℝ[X]
  common : ∀ i ∈ s, PolynomialInterlaces interlacer (p i)
  controlsUpperSign : ∀ i ∈ s, ∀ x : ℝ,
    IsRootUpperBound interlacer x → 0 < (p i).eval x → IsRootUpperBound (p i) x

/-- Every genuine common interlacer canonically supplies the upper-tail certificate. -/
noncomputable def HasCommonInterlacer.toUpperCertificate
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {p : ι → ℝ[X]}
    (h : HasCommonInterlacer s p) : CommonUpperInterlacerCertificate s p := by
  classical
  let q := h.choose
  have hq : ∀ i ∈ s, PolynomialInterlaces q (p i) := h.choose_spec
  exact
    { interlacer := q
      common := hq
      controlsUpperSign := fun i hi x hqx hpx =>
        (hq i hi).rootUpperBound_of_eval_pos hqx hpx }

/-- At a largest root of a monic real-rooted convex combination, a finite perturbation to the
right and compactness of the finite index set select one member with no larger root. -/
lemma exists_member_below_convexLargestRoot
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (w : ι → ℝ) (p : ι → ℝ[X])
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (cert : CommonUpperInterlacerCertificate s p)
    (hreal : RealRooted (polynomialWeightedSum s w p))
    (hmonic : (polynomialWeightedSum s w p).Monic) (x : ℝ)
    (hx : IsLargestRoot (polynomialWeightedSum s w p) x)
    (hqx : IsRootUpperBound cert.interlacer x) :
    ∃ i ∈ s, IsRootUpperBound (p i) x := by
  have hs : s.Nonempty := by
    by_contra hs0
    simp only [Finset.not_nonempty_iff_eq_empty] at hs0
    simp [hs0] at hwsum
  apply exists_rootUpperBound_at_of_forall_gt hs p x
  intro y hxy
  have hstrict : IsStrictRootUpperBound (polynomialWeightedSum s w p) y := by
    intro r hr
    exact (hx.upperBound r hr).trans_lt hxy
  have hsumpos : 0 < (polynomialWeightedSum s w p).eval y :=
    hreal.eval_pos_of_strictRootUpperBound hmonic hstrict
  obtain ⟨i, hi, _hwi, hpipos⟩ :=
    exists_positive_eval_of_weightedSum_pos w p hw y hsumpos
  have hqy : IsRootUpperBound cert.interlacer y := by
    intro r hr
    exact (hqx r hr).trans hxy.le
  exact ⟨i, hi, cert.controlsUpperSign i hi y hqy hpipos⟩

/-- The largest root of a real-rooted normalized weighted sum automatically bounds its common
interlacer.  Full interlacing of the sum is not needed: at the largest root of the interlacer,
the alternating endpoint sign says that the sum is nonpositive, whereas a monic real-rooted
polynomial is positive strictly beyond its largest root. -/
lemma commonInterlacer_rootUpperBound_of_weightedSum_largest
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (w : ι → ℝ) (p : ι → ℝ[X])
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (cert : CommonUpperInterlacerCertificate s p)
    (hreal : RealRooted (polynomialWeightedSum s w p)) (x : ℝ)
    (hx : IsLargestRoot (polynomialWeightedSum s w p) x) :
    IsRootUpperBound cert.interlacer x := by
  classical
  let P := polynomialWeightedSum s w p
  let q := cert.interlacer
  have hs : s.Nonempty := by
    by_contra hs0
    simp only [Finset.not_nonempty_iff_eq_empty] at hs0
    simp [hs0] at hwsum
  obtain ⟨i, hi⟩ := hs
  have hqi := cert.common i hi
  have hq0 : q ≠ 0 := hqi.1
  have hqmonic : q.Monic := hqi.2.2.1
  have hqsplit : RealRooted q := hqi.2.2.2.2.1
  have hPmonic : P.Monic := by
    simpa [P, q] using
      (monic_polynomialWeightedSum_of_commonInterlacer w p q cert.common hwsum).1
  by_cases hqdeg : q.natDegree = 0
  · intro r hr
    have hrmem : r ∈ q.roots := (mem_roots hq0).mpr hr
    have hcard : q.roots.card = 0 := by
      rw [← hqsplit.natDegree_eq_card_roots, hqdeg]
    have hroots0 : q.roots = 0 := Multiset.card_eq_zero.mp hcard
    rw [hroots0] at hrmem
    simp at hrmem
  · let lower := q.roots.sort (· ≤ ·)
    have hlowerlen : lower.length = q.natDegree := by
      rw [hqsplit.natDegree_eq_card_roots]
      simp [lower]
    have hlowerpos : 0 < lower.length := by
      rw [hlowerlen]
      omega
    have hlower : lower ≠ [] := List.ne_nil_of_length_pos hlowerpos
    let k := lower.length - 1
    have hk : k < lower.length := by dsimp [k]; omega
    let a := lower.get ⟨k, hk⟩
    have ha : IsLargestRoot q a := by
      have hlast : lower.get ⟨k, hk⟩ = lower.getLast hlower := by
        simp [k, List.getLast_eq_getElem]
      change IsLargestRoot q (lower.get ⟨k, hk⟩)
      rw [hlast]
      simpa [lower] using sortedRoots_getLast_isLargest hq0 hlower
    have hasign := eval_polynomialWeightedSum_at_commonInterlacerRoot_sign
      w p q hw cert.common k (by simpa [lower] using hk)
    have hlen_sub : lower.length - k = 1 := by dsimp [k]; omega
    have hPa_nonpos : P.eval a ≤ 0 := by
      change 0 ≤ P.eval a * (-1 : ℝ) ^ (lower.length - k) at hasign
      rw [hlen_sub] at hasign
      norm_num at hasign ⊢
      exact hasign
    have hax : a ≤ x := by
      by_contra hnot
      have hstrict : IsStrictRootUpperBound P a := by
        intro r hr
        exact (hx.upperBound r hr).trans_lt (lt_of_not_ge hnot)
      have hPapos : 0 < P.eval a := hreal.eval_pos_of_strictRootUpperBound hPmonic hstrict
      linarith
    intro r hr
    exact (ha.upperBound r hr).trans hax

/-- Selection with no explicit interlacing proof for the convex combination.  Once its
real-rootedness is known, normalization and the genuine common interlacer supply all remaining
hypotheses automatically. -/
lemma exists_largestRoot_and_member_below_of_realRooted
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (w : ι → ℝ) (p : ι → ℝ[X])
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (cert : CommonUpperInterlacerCertificate s p)
    (hreal : RealRooted (polynomialWeightedSum s w p)) :
    ∃ x, IsLargestRoot (polynomialWeightedSum s w p) x ∧
      ∃ i ∈ s, IsRootUpperBound (p i) x := by
  have hmonic : (polynomialWeightedSum s w p).Monic :=
    (monic_polynomialWeightedSum_of_commonInterlacer
      w p cert.interlacer cert.common hwsum).1
  have hdegree : (polynomialWeightedSum s w p).natDegree =
      cert.interlacer.natDegree + 1 :=
    (monic_polynomialWeightedSum_of_commonInterlacer
      w p cert.interlacer cert.common hwsum).2
  have hdeg : 0 < (polynomialWeightedSum s w p).natDegree := by omega
  obtain ⟨x, hx⟩ := hreal.exists_largestRoot hdeg
  have hqx : IsRootUpperBound cert.interlacer x :=
    commonInterlacer_rootUpperBound_of_weightedSum_largest
      w p hw hwsum cert hreal x hx
  exact ⟨x, hx,
    exists_member_below_convexLargestRoot w p hw hwsum cert hreal hmonic x hx hqx⟩

/-- `HasCommonInterlacer` convenience wrapper for the real-rooted weighted-sum selection
theorem. -/
lemma HasCommonInterlacer.exists_largestRoot_and_member_below_of_realRooted
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {p : ι → ℝ[X]}
    (h : HasCommonInterlacer s p) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hreal : RealRooted (polynomialWeightedSum s w p)) :
    ∃ x, IsLargestRoot (polynomialWeightedSum s w p) x ∧
      ∃ i ∈ s, IsRootUpperBound (p i) x :=
  CommutatorTheorem.exists_largestRoot_and_member_below_of_realRooted
    w p hw hwsum h.toUpperCertificate hreal

/-- Fully automatic common-interlacer selection: convex real-rootedness is supplied by the
common-interlacer closure theorem, so a prefix-tree caller only provides weights. -/
lemma exists_largestRoot_and_member_below_of_commonInterlacer
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (w : ι → ℝ) (p : ι → ℝ[X])
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (cert : CommonUpperInterlacerCertificate s p) :
    ∃ x, IsLargestRoot (polynomialWeightedSum s w p) x ∧
      ∃ i ∈ s, IsRootUpperBound (p i) x := by
  have hreal : RealRooted (polynomialWeightedSum s w p) :=
    realRooted_polynomialWeightedSum_of_commonInterlacer
      w p cert.interlacer hw cert.common hwsum
  exact exists_largestRoot_and_member_below_of_realRooted
    w p hw hwsum cert hreal

/-- `HasCommonInterlacer` form of the automatic selection theorem, intended for direct use at
each node of an interlacing-family prefix tree. -/
lemma HasCommonInterlacer.exists_largestRoot_and_member_below_automatic
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {p : ι → ℝ[X]}
    (h : HasCommonInterlacer s p) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1) :
    ∃ x, IsLargestRoot (polynomialWeightedSum s w p) x ∧
      ∃ i ∈ s, IsRootUpperBound (p i) x :=
  exists_largestRoot_and_member_below_of_commonInterlacer
    w p hw hwsum h.toUpperCertificate

/-- Existence form.  If the same common interlacer also interlaces the convex combination, its
largest root automatically bounds the interlacer, so the member-selection theorem applies.

Real-rootedness, monicity, and nonconstancy of the weighted sum are all consequences of
`hcombo`; they therefore do not appear as redundant hypotheses. -/
lemma exists_largestRoot_and_member_below
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (w : ι → ℝ) (p : ι → ℝ[X])
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (cert : CommonUpperInterlacerCertificate s p)
    (hcombo : PolynomialInterlaces cert.interlacer (polynomialWeightedSum s w p)) :
    ∃ x, IsLargestRoot (polynomialWeightedSum s w p) x ∧
      ∃ i ∈ s, IsRootUpperBound (p i) x := by
  have hreal : RealRooted (polynomialWeightedSum s w p) := hcombo.2.2.2.2.2.1
  exact exists_largestRoot_and_member_below_of_realRooted
    w p hw hwsum cert hreal

/-! ## Rolle/derivative wrappers -/

/-- The derivative of a real-rooted real polynomial is real-rooted.

This is not currently available as a direct Mathlib lemma.  It follows by combining Mathlib's
Rolle root-count estimate with its splitting criterion. -/
lemma RealRooted.derivative {p : ℝ[X]} (hp : RealRooted p) : RealRooted p.derivative := by
  by_cases hdeg0 : p.natDegree = 0
  · rw [derivative_of_natDegree_zero hdeg0]
    exact Splits.zero
  have hroots_p : p.roots.card = p.natDegree := hp.natDegree_eq_card_roots.symm
  have hrolle : p.natDegree ≤ p.derivative.roots.card + 1 := by
    rw [← hroots_p]
    exact p.card_roots_le_derivative
  have hroots_deriv_le : p.derivative.roots.card ≤ p.derivative.natDegree :=
    card_roots' p.derivative
  have hdeg_deriv_le : p.derivative.natDegree ≤ p.natDegree - 1 :=
    natDegree_derivative_le p
  have hcard_eq : p.derivative.roots.card = p.derivative.natDegree := by
    omega
  exact splits_iff_card_roots.mpr hcard_eq

/-- Every iterated derivative of a real-rooted real polynomial is real-rooted. -/
lemma RealRooted.iterate_derivative {p : ℝ[X]} (hp : RealRooted p) (k : ℕ) :
    RealRooted (Polynomial.derivative^[k] p) := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.derivative

end CommutatorTheorem
