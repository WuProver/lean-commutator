import CommutatorTheorem.Epsilon.BTMDPDeletionIdentity
import CommutatorTheorem.Epsilon.BTFellPair
import CommutatorTheorem.Epsilon.BTRootMoment

/-!
# From convex real-rootedness to conditional MDP interlacing

This file closes the finite Fell/interlacing part of the exact-MDP stability
argument.  Once every conditional node and every two-child convex combination
is real-rooted, the normalized conditional MDPs form the deletion
interlacing tree used by the selector.

The proof includes the degree and monicity bookkeeping for the normalized
iterated derivatives.  No stability theorem is assumed implicitly here.
-/

open scoped BigOperators Polynomial

namespace CommutatorTheorem.BTMDPInterlacingFromConvex

open Polynomial Finset
open CommutatorTheorem
open CommutatorTheorem.BTMDPSelection
open CommutatorTheorem.BTMDPStability
open CommutatorTheorem.BTMDPDeletionIdentity
open CommutatorTheorem.BTInterlacingConverse
open CommutatorTheorem.BTFellPair

/-- Every compressed exact MDP remains monic. -/
theorem restrictedMDP_monic {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (s : Finset (Fin n)) :
    (restrictedMDP A hA s).Monic := by
  unfold restrictedMDP
  exact realMixedDeterminantalPolynomial_monic hk _ _

/-- Its degree is the cardinality of the compressed coordinate set. -/
theorem restrictedMDP_natDegree {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (s : Finset (Fin n)) :
    (restrictedMDP A hA s).natDegree = s.card := by
  unfold restrictedMDP
  exact realMixedDeterminantalPolynomial_natDegree hk _ _

/-- Descending-factorial normalization makes the conditional derivative
monic of the target degree. -/
theorem normalizedConditionalMDP_isMonicOfDegree
    {n k d : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (s : Finset (Fin n)) (hds : d ≤ s.card) :
    IsMonicOfDegree (normalizedConditionalMDP (d := d) A hA s) d := by
  let p := restrictedMDP A hA s
  let r := s.card - d
  have hpmonic : p.Monic := restrictedMDP_monic hk A hA s
  have hpdegree : p.natDegree = s.card :=
    restrictedMDP_natDegree hk A hA s
  have hrle : r ≤ p.natDegree := by
    dsimp [r]
    rw [hpdegree]
    omega
  have hdfpos : 0 < s.card.descFactorial r :=
    Nat.descFactorial_pos.mpr (by dsimp [r]; omega)
  have hdf : (s.card.descFactorial r : ℝ) ≠ 0 := by
    exact_mod_cast hdfpos.ne'
  apply (isMonicOfDegree_iff
    (normalizedConditionalMDP (d := d) A hA s) d).mpr
  constructor
  · rw [normalizedConditionalMDP]
    dsimp [p, r] at hrle ⊢
    rw [Polynomial.natDegree_smul _ (inv_ne_zero hdf)]
    rw [natDegree_iterate_derivative_eq_sub_real hrle, hpdegree]
    omega
  · rw [normalizedConditionalMDP, Polynomial.coeff_smul,
      Polynomial.coeff_iterate_derivative]
    have hsum : d + (s.card - d) = s.card := Nat.add_sub_of_le hds
    rw [hsum]
    have hpcoeff : p.coeff s.card = 1 := by
      rw [← hpdegree]
      exact hpmonic.coeff_natDegree
    change (s.card.descFactorial (s.card - d) : ℝ)⁻¹ *
      ((s.card.descFactorial (s.card - d) : ℕ) • p.coeff s.card) = 1
    rw [hpcoeff]
    simp only [nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hdf

/-- In particular, every valid conditional polynomial is monic. -/
theorem normalizedConditionalMDP_monic
    {n k d : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (s : Finset (Fin n)) (hds : d ≤ s.card) :
    (normalizedConditionalMDP (d := d) A hA s).Monic :=
  (normalizedConditionalMDP_isMonicOfDegree hk A hA s hds).monic

/-- In particular, every valid conditional polynomial has degree `d`. -/
theorem normalizedConditionalMDP_natDegree
    {n k d : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (s : Finset (Fin n)) (hds : d ≤ s.card) :
    (normalizedConditionalMDP (d := d) A hA s).natDegree = d :=
  (normalizedConditionalMDP_isMonicOfDegree hk A hA s hds).natDegree_eq

/-- Real-rootedness of all valid normalized conditional nodes. -/
def MDPConditionalNodesRealRooted {n k d : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) : Prop :=
  ∀ s : Finset (Fin n), d ≤ s.card →
    RealRooted (normalizedConditionalMDP (d := d) A hA s)

/-- Real-rootedness of every convex combination of two deletion siblings. -/
def MDPDeletionPairConvexRealRooted {n k d : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) : Prop :=
  ∀ (s : Finset (Fin n)) (_ : d < s.card)
    (i j : {x // x ∈ s}) (t : ℝ), 0 ≤ t → t ≤ 1 →
      RealRooted
        (t • deletionChildPolynomial
            (normalizedConditionalMDP (d := d) A hA) s i +
          (1 - t) • deletionChildPolynomial
            (normalizedConditionalMDP (d := d) A hA) s j)

private theorem pair_commonInterlacer_of_pairFell
    {ι : Type*} [DecidableEq ι]
    {p : ι → ℝ[X]} {i j : ι} {d : ℕ}
    (pairFell : PairFellConverseAtDegree d)
    (hpmonic : (p i).Monic) (hqmonic : (p j).Monic)
    (hpsplits : RealRooted (p i)) (hqsplits : RealRooted (p j))
    (hpdegree : (p i).natDegree = d) (hqdegree : (p j).natDegree = d)
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p i + (1 - t) • p j)) :
    HasCommonInterlacer ({i, j} : Finset ι) p := by
  obtain ⟨r, hr⟩ := pairFell (p i) (p j) hpmonic hqmonic
    hpsplits hqsplits hpdegree hqdegree hall
  refine ⟨r, ?_⟩
  intro x hx
  have hx' : x = i ∨ x = j := by simpa using hx
  rcases hx' with rfl | rfl
  · exact hr true (by simp)
  · exact hr false (by simp)

/-- General finite Fell converts pairwise convex real-rootedness into a
common interlacer for all deletion children. -/
theorem deletionChildren_commonInterlacer_of_pairFell
    {n k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (hnodes : MDPConditionalNodesRealRooted (d := d) A hA)
    (hconvex : MDPDeletionPairConvexRealRooted (d := d) A hA)
    (pairFell : PairFellConverseAtDegree d)
    (s : Finset (Fin n)) (hds : d < s.card) :
    HasCommonInterlacer (Finset.univ : Finset {i // i ∈ s})
      (deletionChildPolynomial
        (normalizedConditionalMDP (d := d) A hA) s) := by
  let child := deletionChildPolynomial
    (normalizedConditionalMDP (d := d) A hA) s
  have hs : s.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le d) hds)
  have huniv : (Finset.univ : Finset {i // i ∈ s}).Nonempty := by
    simpa using hs
  apply finite_fell_of_pair_fell Finset.univ huniv child d hd
  · intro i _
    apply normalizedConditionalMDP_monic hk A hA
    rw [Finset.card_erase_of_mem i.2]
    omega
  · intro i _
    apply hnodes
    rw [Finset.card_erase_of_mem i.2]
    omega
  · intro i _
    apply normalizedConditionalMDP_natDegree hk A hA
    rw [Finset.card_erase_of_mem i.2]
    omega
  · intro i _ j _ hall
    apply pair_commonInterlacer_of_pairFell pairFell
      (p := child)
    · apply normalizedConditionalMDP_monic hk A hA
      rw [Finset.card_erase_of_mem i.2]
      omega
    · apply normalizedConditionalMDP_monic hk A hA
      rw [Finset.card_erase_of_mem j.2]
      omega
    · apply hnodes
      rw [Finset.card_erase_of_mem i.2]
      omega
    · apply hnodes
      rw [Finset.card_erase_of_mem j.2]
      omega
    · apply normalizedConditionalMDP_natDegree hk A hA
      rw [Finset.card_erase_of_mem i.2]
      omega
    · apply normalizedConditionalMDP_natDegree hk A hA
      rw [Finset.card_erase_of_mem j.2]
      omega
    · exact hall
  · intro i _ j _ t ht0 ht1
    exact hconvex s hds i j t ht0 ht1

/-- The exact deletion identity and finite Fell theorem assemble the full
conditional interlacing tree. -/
theorem mdpConditionalInterlacing_of_convexRealRooted
    {n k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (hnodes : MDPConditionalNodesRealRooted (d := d) A hA)
    (hconvex : MDPDeletionPairConvexRealRooted (d := d) A hA)
    (pairFell : PairFellConverseAtDegree d) :
    MDPConditionalInterlacing (d := d) A hA := by
  apply DeletionCommonInterlacingTree.toDeletionInterlacingTree
  refine
    { leaf_realRooted := ?_
      natDegree := ?_
      children_common := ?_
      parent_average := ?_ }
  · intro s hsd
    exact hnodes s (by omega)
  · intro s hds
    exact normalizedConditionalMDP_natDegree hk A hA s hds
  · intro s hds
    exact deletionChildren_commonInterlacer_of_pairFell
      hk hd A hA hnodes hconvex pairFell s hds
  · intro s hds
    exact normalizedConditionalMDP_parent_average_of_deletionIdentity
      A hA (mdpDeletionDerivativeIdentity_of_pos hk A hA) s hds

/-- If the root-disjoint pair core is known in all degrees, the common-root
induction in `BTFellPair` supplies the fixed-degree pair Fell theorem needed
above. -/
theorem mdpConditionalInterlacing_of_rootDisjointFell
    {n k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (hnodes : MDPConditionalNodesRealRooted (d := d) A hA)
    (hconvex : MDPDeletionPairConvexRealRooted (d := d) A hA)
    (hcore : ∀ e : ℕ, 2 ≤ e → RootDisjointPairFellConverseAtDegree e) :
    MDPConditionalInterlacing (d := d) A hA := by
  apply mdpConditionalInterlacing_of_convexRealRooted
    hk hd A hA hnodes hconvex
  exact pairFellConverseAtDegree_of_rootDisjoint_all hcore d hd

end CommutatorTheorem.BTMDPInterlacingFromConvex
