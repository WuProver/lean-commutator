import CommutatorTheorem.Epsilon.BTFellCountInduction
import CommutatorTheorem.Epsilon.BTMDPSelection

/-!
# Finite weighted interlacing selection

Fell's converse is invoked through its proved arbitrary-degree theorem. Thus the
selection statements below require real-rooted convex combinations, not an assumed
common interlacer or an assumed good outcome. The last theorem performs every step
of a finite, nonuniform conditional-expectation tree.
-/

namespace NoEpsilon.MSSInterlacing

open Polynomial CommutatorTheorem
open CommutatorTheorem.BTInterlacingConverse CommutatorTheorem.BTFellPair
open scoped BigOperators Polynomial

/-- The full two-polynomial Fell converse in each positive degree. -/
theorem pairFell (d : ℕ) (hd : 0 < d) : PairFellConverseAtDegree d :=
  pairFellConverseAtDegree_of_rootDisjoint_all
    CommutatorTheorem.BTFellCountInduction.rootDisjointPairFellConverseAtDegree_all d hd

/-- Pairwise convex real-rootedness produces a common interlacer for a finite family. -/
theorem commonInterlacer_of_pairwise_convex {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (f : Ω → ℝ[X]) (d : ℕ) (hd : 0 < d)
    (hmonic : ∀ ω, (f ω).Monic) (hdegree : ∀ ω, (f ω).natDegree = d)
    (hconvex : ∀ ω η, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • f ω + (1 - t) • f η)) :
    HasCommonInterlacer Finset.univ f := by
  classical
  have hreal : ∀ ω, RealRooted (f ω) := by
    intro ω
    simpa using hconvex ω ω 1 (by norm_num) (by norm_num)
  apply hasCommonInterlacer_of_pairwise Finset.univ Finset.univ_nonempty f d hd
    (fun ω _ ↦ hmonic ω) (fun ω _ ↦ hreal ω) (fun ω _ ↦ hdegree ω)
  intro ω _ η _
  obtain ⟨q, hq⟩ := pairFell d hd (f ω) (f η) (hmonic ω) (hmonic η)
    (hreal ω) (hreal η) (hdegree ω) (hdegree η) (hconvex ω η)
  refine ⟨q, ?_⟩
  intro x hx
  have hx' : x = ω ∨ x = η := by simpa using hx
  rcases hx' with rfl | rfl
  · exact hq true (by simp)
  · exact hq false (by simp)

/-- A normalized, nonnegative finite average admits a member whose roots are no
larger than its largest root. Only pairwise convex real-rootedness is an input. -/
theorem exists_member_below_weighted_largestRoot {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ[X]) (p : Ω → ℝ) (d : ℕ) (hd : 0 < d)
    (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (hmonic : ∀ ω, (f ω).Monic) (hdegree : ∀ ω, (f ω).natDegree = d)
    (hconvex : ∀ ω η, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • f ω + (1 - t) • f η)) :
    ∃ x, IsLargestRoot (∑ ω, p ω • f ω) x ∧
      ∃ ω, IsRootUpperBound (f ω) x := by
  classical
  haveI : Nonempty Ω := by
    by_contra h
    haveI : IsEmpty Ω := not_nonempty_iff.mp h
    simp at hsum
  have hc := commonInterlacer_of_pairwise_convex f d hd hmonic hdegree hconvex
  obtain ⟨x, hx, ω, _, hω⟩ :=
    hc.exists_largestRoot_and_member_below_automatic p (fun ω _ ↦ hp ω) hsum
  exact ⟨x, hx, ω, hω⟩

/-- The selected member simultaneously inherits every upper root bound of the average. -/
theorem exists_member_inheriting_rootBounds {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ[X]) (p : Ω → ℝ) (d : ℕ) (hd : 0 < d)
    (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (hmonic : ∀ ω, (f ω).Monic) (hdegree : ∀ ω, (f ω).natDegree = d)
    (hconvex : ∀ ω η, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • f ω + (1 - t) • f η)) :
    ∃ ω, ∀ x, IsRootUpperBound (∑ η, p η • f η) x →
      IsRootUpperBound (f ω) x := by
  obtain ⟨y, hy, ω, hω⟩ := exists_member_below_weighted_largestRoot
    f p d hd hp hsum hmonic hdegree hconvex
  exact ⟨ω, fun x hx r hr ↦ (hω r hr).trans (hx y hy.isRoot)⟩

/-- Normalized weighted sums preserve monicity and the common degree. -/
theorem weightedSum_monic_natDegree {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ[X]) (p : Ω → ℝ) (d : ℕ) (hsum : ∑ ω, p ω = 1)
    (hmonic : ∀ ω, (f ω).Monic) (hdegree : ∀ ω, (f ω).natDegree = d) :
    (∑ ω, p ω • f ω).Monic ∧ (∑ ω, p ω • f ω).natDegree = d := by
  classical
  have hle : (∑ ω, p ω • f ω).natDegree ≤ d := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro ω _
    exact (Polynomial.natDegree_smul_le _ _).trans (hdegree ω).le
  have hc : (∑ ω, p ω • f ω).coeff d = 1 := by
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul, smul_eq_mul]
    have hf : ∀ ω, (f ω).coeff d = 1 := fun ω ↦ by
      rw [← hdegree ω]; exact (hmonic ω).coeff_natDegree
    simpa only [hf, mul_one] using hsum
  have hm : (∑ ω, p ω • f ω).Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one d hle hc
  exact ⟨hm, le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (hc ▸ one_ne_zero))⟩

/-- The exact conditional average for independent finite choices, allowing a different
law at each depth. Leaves are indexed by complete lists of outcomes. -/
noncomputable def conditionalAverage {Ω : Type*} [Fintype Ω]
    (p : ℕ → Ω → ℝ) (leaf : List Ω → ℝ[X]) : ℕ → List Ω → ℝ[X]
  | 0, pref => leaf pref
  | n + 1, pref =>
      ∑ ω, p pref.length ω • conditionalAverage p leaf n (pref ++ [ω])

/-- All conditional averages retain the leaf degree and leading coefficient. -/
theorem conditionalAverage_monic_natDegree {Ω : Type*} [Fintype Ω]
    (p : ℕ → Ω → ℝ) (leaf : List Ω → ℝ[X]) (n d : ℕ)
    (hsum : ∀ k, ∑ ω, p k ω = 1)
    (hleaf : ∀ q, q.length = n → (leaf q).Monic ∧ (leaf q).natDegree = d)
    (remaining : ℕ) (pref : List Ω) (hvalid : pref.length + remaining = n) :
    (conditionalAverage p leaf remaining pref).Monic ∧
      (conditionalAverage p leaf remaining pref).natDegree = d := by
  induction remaining generalizing pref with
  | zero => exact hleaf pref (by simpa using hvalid)
  | succ remaining ih =>
    apply weightedSum_monic_natDegree _ _ d (hsum pref.length)
    · intro ω
      exact (ih (pref ++ [ω]) (by simp only [List.length_append,
          List.length_singleton]; omega)).1
    · intro ω
      exact (ih (pref ++ [ω]) (by simp only [List.length_append,
          List.length_singleton]; omega)).2

/-- The complete finite interlacing-tree selection argument. Every valid internal node
needs only real-rooted convex combinations of two children. A full outcome list is
constructed, and its polynomial inherits every upper root bound of the initial node. -/
theorem select_complete_outcome {Ω : Type*} [Fintype Ω]
    (p : ℕ → Ω → ℝ) (leaf : List Ω → ℝ[X]) (n d : ℕ) (hd : 0 < d)
    (hp : ∀ k ω, 0 ≤ p k ω) (hsum : ∀ k, ∑ ω, p k ω = 1)
    (hleaf : ∀ q, q.length = n → (leaf q).Monic ∧ (leaf q).natDegree = d)
    (hconvex : ∀ remaining pref, pref.length + (remaining + 1) = n →
      ∀ ω η, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        RealRooted (t • conditionalAverage p leaf remaining (pref ++ [ω]) +
          (1 - t) • conditionalAverage p leaf remaining (pref ++ [η])))
    (remaining : ℕ) (pref : List Ω) (hvalid : pref.length + remaining = n) :
    ∃ q : List Ω, q.length = n ∧ pref.IsPrefix q ∧
      ∀ x, IsRootUpperBound (conditionalAverage p leaf remaining pref) x →
        IsRootUpperBound (leaf q) x := by
  induction remaining generalizing pref with
  | zero => exact ⟨pref, by simpa using hvalid, List.prefix_refl _, fun _ hx ↦ hx⟩
  | succ remaining ih =>
    let f : Ω → ℝ[X] := fun ω ↦ conditionalAverage p leaf remaining (pref ++ [ω])
    have hf (ω : Ω) : (f ω).Monic ∧ (f ω).natDegree = d :=
      conditionalAverage_monic_natDegree p leaf n d hsum hleaf remaining (pref ++ [ω])
        (by simp only [List.length_append, List.length_singleton]; omega)
    obtain ⟨ω, hω⟩ := exists_member_inheriting_rootBounds f (p pref.length) d hd
      (hp pref.length) (hsum pref.length) (fun ω ↦ (hf ω).1)
      (fun ω ↦ (hf ω).2) (hconvex remaining pref hvalid)
    obtain ⟨q, hq, hpref, hbound⟩ := ih (pref ++ [ω])
      (by simp only [List.length_append, List.length_singleton]; omega)
    refine ⟨q, hq, (List.prefix_append pref [ω]).trans hpref, ?_⟩
    intro x hx
    exact hbound x (hω x hx)

end NoEpsilon.MSSInterlacing
