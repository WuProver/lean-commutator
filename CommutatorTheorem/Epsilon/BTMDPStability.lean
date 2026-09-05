import CommutatorTheorem.Epsilon.BTMDPSelection

/-!
# Reducing exact-MDP stability to common interlacing of siblings

The prefix selector in `BTMDPSelection` was initially packaged with two
stability fields: real-rootedness of every conditional average and common
interlacing of every family of children.  The first field is redundant.

Indeed, leaves are products of Hermitian characteristic polynomials and hence
are real-rooted.  At every internal node the parent is the uniform convex
combination of its children.  The convex-closure theorem from
`BTInterlacing` therefore propagates real-rootedness upward from the leaves as
soon as the children have a common interlacer.

Consequently the exact finite selection layer now has only one genuine
real-stability input: common interlacing of sibling conditional MDPs.  This
file contains no axiom or placeholder.
-/

open scoped BigOperators Polynomial

namespace CommutatorTheorem.BTMDPStability

open CommutatorTheorem
open CommutatorTheorem.BTMixedDet
open CommutatorTheorem.BTMDPSelection
open Polynomial

/-! ## Deletion trees: real-rootedness is also redundant -/

/-- A deletion tree carrying only the data that are not automatic from common
interlacing: real-rooted leaves, sibling common interlacers, and the exact
parent-average identity. -/
structure DeletionCommonInterlacingTree {α : Type*} [DecidableEq α]
    (d : ℕ) (p : Finset α → ℝ[X]) : Prop where
  leaf_realRooted : ∀ s, s.card = d → RealRooted (p s)
  natDegree : ∀ s, d ≤ s.card → (p s).natDegree = d
  children_common : ∀ s, d < s.card →
    HasCommonInterlacer (Finset.univ : Finset {i // i ∈ s})
      (deletionChildPolynomial p s)
  parent_average : ∀ s, d < s.card →
    p s = polynomialWeightedSum (Finset.univ : Finset {i // i ∈ s})
      (deletionWeight s) (deletionChildPolynomial p s)

private lemma deletionWeight_nonneg' {α : Type*} [DecidableEq α]
    (s : Finset α) (i : {i // i ∈ s}) : 0 ≤ deletionWeight s i := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

private lemma sum_deletionWeight_eq_one' {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) :
    ∑ i ∈ (Finset.univ : Finset {i // i ∈ s}), deletionWeight s i = 1 := by
  simp only [deletionWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast hs.card_ne_zero)

/-- Common interlacing makes the real-rootedness field of
`DeletionInterlacingTree` automatic away from the leaves. -/
theorem DeletionCommonInterlacingTree.toDeletionInterlacingTree
    {α : Type*} [DecidableEq α] {d : ℕ} {p : Finset α → ℝ[X]}
    (T : DeletionCommonInterlacingTree d p) :
    DeletionInterlacingTree d p where
  realRooted := by
    intro s hds
    by_cases hleaf : s.card = d
    · exact T.leaf_realRooted s hleaf
    · have hlt : d < s.card := lt_of_le_of_ne hds (Ne.symm hleaf)
      have hs : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hs0
        rw [hs0] at hlt
        simp at hlt
      obtain ⟨q, hq⟩ := T.children_common s hlt
      rw [T.parent_average s hlt]
      exact realRooted_polynomialWeightedSum_of_commonInterlacer
        (deletionWeight s) (deletionChildPolynomial p s) q
        (fun i _ ↦ deletionWeight_nonneg' s i) hq
        (sum_deletionWeight_eq_one' hs)
  natDegree := T.natDegree
  children_common := T.children_common
  parent_average := T.parent_average

/-- Coordinate deletion selection requires no separate real-rootedness proof
at internal nodes. -/
theorem DeletionCommonInterlacingTree.select_subset
    {α : Type*} [Finite α] [DecidableEq α]
    {d : ℕ} {p : Finset α → ℝ[X]}
    (T : DeletionCommonInterlacingTree d p) (hd : 0 < d)
    (s : Finset α) (hds : d ≤ s.card) :
    ∃ t : Finset α, t ⊆ s ∧ t.card = d ∧
      ∀ x, IsRootUpperBound (p s) x → IsRootUpperBound (p t) x := by
  letI := Fintype.ofFinite α
  exact T.toDeletionInterlacingTree.select_subset hd s hds

/-! ## Jacobi's coordinate-deletion formula for characteristic polynomials -/

/-- Formal differentiation of a determinant is the sum of determinants in
which one column has been differentiated.  This works over every commutative
coefficient ring and is the determinant-algebra core of the MDP deletion
identity. -/
theorem derivative_det_eq_sum_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R[X]) :
    derivative M.det =
      ∑ j : ι, (M.updateCol j (fun i ↦ derivative (M i j))).det := by
  rw [Matrix.det_apply', Polynomial.derivative_sum]
  simp_rw [Polynomial.derivative_mul, Polynomial.derivative_intCast, zero_mul, zero_add,
    Polynomial.derivative_prod_finset]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [← Finset.prod_erase_mul Finset.univ
    (fun i => M.updateCol j (fun i ↦ derivative (M i j)) (σ i) i)
    (Finset.mem_univ j)]
  simp only [Matrix.updateCol_apply, ↓reduceIte]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [hi.1]
  · simp

private theorem det_updateCol_single_self
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (j : ι) :
    (M.updateCol j (Pi.single j 1)).det = Matrix.adjugate M j j := by
  calc
    (M.updateCol j (Pi.single j 1)).det =
        (M.updateCol j (Pi.single j 1)).transpose.det :=
      (Matrix.det_transpose _).symm
    _ = (M.transpose.updateRow j (Pi.single j 1)).det := by
      rw [Matrix.updateRow_transpose]
    _ = Matrix.adjugate M.transpose j j :=
      (Matrix.adjugate_apply M.transpose j j).symm
    _ = Matrix.adjugate M j j := by
      have h := congrArg (fun N => N j j) (Matrix.adjugate_transpose M)
      simpa using h.symm

private theorem derivative_charmatrix_apply
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (i j : ι) :
    derivative (Matrix.charmatrix M i j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp
  · rw [Matrix.charmatrix_apply_ne _ _ _ h]
    simp [h]

/-- Jacobi's formula in coordinate-deletion form: the derivative of a
characteristic polynomial is the sum of the characteristic polynomials of all
principal submatrices obtained by deleting one coordinate. -/
theorem charpoly_derivative_eq_sum_principal_fin_succ
    {n : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    derivative M.charpoly =
      ∑ j : Fin (n + 1), (M.submatrix j.succAbove j.succAbove).charpoly := by
  rw [Matrix.charpoly, derivative_det_eq_sum_updateCol]
  apply Finset.sum_congr rfl
  intro j _
  have hcol :
      (fun i => derivative (Matrix.charmatrix M i j)) = Pi.single j 1 := by
    funext i
    rw [derivative_charmatrix_apply]
    simp [Pi.single_apply, eq_comm]
  rw [hcol, det_updateCol_single_self]
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Nat.succ_eq_add_one]
  have hsign : (-1 : R[X]) ^ ((j : ℕ) + (j : ℕ)) = 1 := by
    rw [← two_mul]
    simp [pow_mul]
  rw [hsign, one_mul]
  rw [Matrix.charpoly]
  congr 1
  ext i l
  simp only [Matrix.submatrix_apply]
  by_cases hil : i = l
  · subst l
    simp
  · have hsne : j.succAbove i ≠ j.succAbove l := by
      exact fun h => hil (Fin.succAbove_right_injective h)
    rw [Matrix.charmatrix_apply_ne _ _ _ hil,
      Matrix.charmatrix_apply_ne _ _ _ hsne]
    rfl

/-- Real-coefficient Hermitian form of Jacobi's coordinate-deletion formula.
This is the exact local identity needed when differentiating a real MDP leaf. -/
theorem realCharpoly_derivative_eq_sum_principal_fin_succ
    {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hM : M.IsHermitian) :
    derivative (realCharpoly M hM) =
      ∑ j : Fin (n + 1),
        realCharpoly (M.submatrix j.succAbove j.succAbove)
          (hM.submatrix j.succAbove) := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  rw [← Polynomial.derivative_map, realCharpoly_map_complex]
  rw [charpoly_derivative_eq_sum_principal_fin_succ]
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (realCharpoly_map_complex
    (M.submatrix j.succAbove j.succAbove) (hM.submatrix j.succAbove)).symm

/-! ## The first two algebraic steps for exact-MDP deletion -/

/-- Product-rule expansion of the derivative of one exact real MDP leaf.
The only derivatives left on the right are derivatives of individual
Hermitian characteristic polynomials, to which Jacobi's formula applies. -/
theorem derivative_realColoringPolynomial {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) :
    derivative (realColoringPolynomial A hA c) =
      ∑ a : Fin k,
        (∏ b ∈ (Finset.univ : Finset (Fin k)).erase a,
          realCharpoly (BTMixedDet.principalCompression (A b) c b)
            (BTMixedDet.principalCompression_isHermitian (hA b) c b)) *
        derivative
          (realCharpoly (BTMixedDet.principalCompression (A a) c a)
            (BTMixedDet.principalCompression_isHermitian (hA a) c a)) := by
  rw [realColoringPolynomial]
  exact Polynomial.derivative_prod_finset

/-- Formal differentiation commutes with the uniform finite average defining
the real exact MDP. -/
theorem derivative_realMixedDeterminantalPolynomial_eq_average
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    derivative (realMixedDeterminantalPolynomial A hA) =
      ((Fintype.card (Coloring n k) : ℝ)⁻¹) •
        ∑ c : Coloring n k, derivative (realColoringPolynomial A hA c) := by
  rw [realMixedDeterminantalPolynomial, Polynomial.derivative_smul]
  congr 1
  exact Polynomial.derivative_sum

/-- Combined product-rule/average expansion.  After the local Jacobi formula,
the only step remaining for `MDPDeletionDerivativeIdentity` is the finite
reindexing of a coloring together with a coordinate in one of its fibers as a
deleted coordinate, a coloring of the complement, and one of its `k`
extensions. -/
theorem derivative_realMixedDeterminantalPolynomial_expanded
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    derivative (realMixedDeterminantalPolynomial A hA) =
      ((Fintype.card (Coloring n k) : ℝ)⁻¹) •
        ∑ c : Coloring n k, ∑ a : Fin k,
          (∏ b ∈ (Finset.univ : Finset (Fin k)).erase a,
            realCharpoly (BTMixedDet.principalCompression (A b) c b)
              (BTMixedDet.principalCompression_isHermitian (hA b) c b)) *
          derivative
            (realCharpoly (BTMixedDet.principalCompression (A a) c a)
              (BTMixedDet.principalCompression_isHermitian (hA a) c a)) := by
  rw [derivative_realMixedDeterminantalPolynomial_eq_average]
  apply congrArg (fun p : ℝ[X] =>
    ((Fintype.card (Coloring n k) : ℝ)⁻¹) • p)
  apply Finset.sum_congr rfl
  intro c _
  exact derivative_realColoringPolynomial A hA c

/-! ## Propagation of the exact deletion-derivative identity -/

/-- One deletion-derivative identity automatically propagates through every
further iterated derivative.  This is the algebraic form used at a normalized
conditional-MDP node. -/
theorem iterateDerivative_restrictedMDP_eq_sum_of_deletionIdentity
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (H : MDPDeletionDerivativeIdentity A hA)
    (s : Finset (Fin n)) (r : ℕ) :
    Polynomial.derivative^[r + 1] (restrictedMDP A hA s) =
      ∑ i : {i // i ∈ s},
        Polynomial.derivative^[r] (restrictedMDP A hA (s.erase i.1)) := by
  rw [Function.iterate_add_apply]
  simp only [Function.iterate_one, H s]
  exact Polynomial.iterate_derivative_sum r Finset.univ
    (fun i : {i // i ∈ s} ↦ restrictedMDP A hA (s.erase i.1))

/-- At target degree `d`, the derivative order at a parent is exactly one
larger than the derivative order at each coordinate-deletion child. -/
theorem conditionalIterate_restrictedMDP_eq_sum_of_deletionIdentity
    {n k d : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (H : MDPDeletionDerivativeIdentity A hA)
    (s : Finset (Fin n)) (hds : d < s.card) :
    Polynomial.derivative^[s.card - d] (restrictedMDP A hA s) =
      ∑ i : {i // i ∈ s},
        Polynomial.derivative^[(s.erase i.1).card - d]
          (restrictedMDP A hA (s.erase i.1)) := by
  have hs : s.Nonempty := by
    exact Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le d) hds)
  have hparent : s.card - d = (s.card - d - 1) + 1 := by omega
  rw [hparent]
  rw [iterateDerivative_restrictedMDP_eq_sum_of_deletionIdentity A hA H]
  apply Finset.sum_congr rfl
  intro i _
  have hr : s.card - d - 1 = (s.erase i.1).card - d := by
    rw [Finset.card_erase_of_mem i.2]
    omega
  rw [hr]

private lemma descFactorial_sub_eq_mul_descFactorial_pred_sub
    {m d : ℕ} (hdm : d < m) :
    m.descFactorial (m - d) =
      m * (m - 1).descFactorial ((m - 1) - d) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hr : m + 1 - d = (m - d) + 1 := by omega
  rw [hr, Nat.succ_descFactorial_succ]
  congr 2

/-- After descending-factorial normalization, the raw deletion-derivative
identity is exactly the uniform parent-average identity required by the
deletion tree. -/
theorem normalizedConditionalMDP_parent_average_of_deletionIdentity
    {n k d : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (H : MDPDeletionDerivativeIdentity A hA)
    (s : Finset (Fin n)) (hds : d < s.card) :
    normalizedConditionalMDP (d := d) A hA s =
      polynomialWeightedSum (Finset.univ : Finset {i // i ∈ s})
        (deletionWeight s)
        (deletionChildPolynomial (normalizedConditionalMDP (d := d) A hA) s) := by
  classical
  rw [normalizedConditionalMDP]
  rw [conditionalIterate_restrictedMDP_eq_sum_of_deletionIdentity A hA H s hds]
  rw [polynomialWeightedSum]
  simp only [deletionWeight, deletionChildPolynomial, normalizedConditionalMDP]
  have hdf := descFactorial_sub_eq_mul_descFactorial_pred_sub hds
  rw [hdf, Nat.cast_mul, mul_inv_rev]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hcard : (s.erase i.1).card = s.card - 1 :=
    Finset.card_erase_of_mem i.2
  rw [hcard]
  simp only [smul_smul]
  congr 1
  ring

/-- The irreducible prefix-tree stability statement: at every valid internal
node, its `k` one-color extensions have a common interlacer. -/
def PrefixMDPChildrenCommon {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) : Prop :=
  ∀ remaining p, p.length + (remaining + 1) = n →
    HasCommonInterlacer (Finset.univ : Finset (Fin k))
      (fun a ↦ prefixConditionalAverage A hA remaining (p ++ [a]))

private lemma prefixWeight_nonneg {k : ℕ} (a : Fin k) :
    0 ≤ prefixWeight a := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

private lemma sum_prefixWeight_eq_one {k : ℕ} (hk : 0 < k) :
    ∑ a ∈ (Finset.univ : Finset (Fin k)), prefixWeight a = 1 := by
  simp only [prefixWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hk))

/-- Common interlacing of siblings alone implies real-rootedness of every
valid conditional average.  The proof is induction from the leaf level and
uses the now-unconditional convex-closure theorem for common interlacers. -/
theorem realRooted_prefixConditionalAverage_of_childrenCommon
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hk : 0 < k)
    (H : PrefixMDPChildrenCommon A hA) :
    ∀ remaining p, p.length + remaining = n →
      RealRooted (prefixConditionalAverage A hA remaining p) := by
  intro remaining
  induction remaining with
  | zero =>
      intro p hvalid
      have hp : p.length = n := by omega
      simpa [prefixConditionalAverage, hp] using
        realColoringPolynomial_realRooted A hA (coloringOfFullList p hp)
  | succ remaining ih =>
      intro p hvalid
      let child : Fin k → ℝ[X] := fun a ↦
        prefixConditionalAverage A hA remaining (p ++ [a])
      obtain ⟨q, hq⟩ := H remaining p hvalid
      have hw : ∀ a ∈ (Finset.univ : Finset (Fin k)),
          0 ≤ prefixWeight a := by
        intro a _
        exact prefixWeight_nonneg a
      have hwsum :
          ∑ a ∈ (Finset.univ : Finset (Fin k)), prefixWeight a = 1 :=
        sum_prefixWeight_eq_one hk
      have hroot :
          RealRooted
            (polynomialWeightedSum (Finset.univ : Finset (Fin k))
              prefixWeight child) := by
        apply realRooted_polynomialWeightedSum_of_commonInterlacer
          prefixWeight child q hw
        · simpa [child] using hq
        · exact hwsum
      rw [prefixConditionalAverage_succ_eq_weightedSum A hA p]
      exact hroot

/-- The original two-field prefix stability package follows from the single
common-interlacing statement. -/
theorem prefixMDPInterlacing_of_childrenCommon
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hk : 0 < k)
    (H : PrefixMDPChildrenCommon A hA) :
    PrefixMDPInterlacing A hA where
  realRooted :=
    realRooted_prefixConditionalAverage_of_childrenCommon A hA hk H
  children_common := H

/-- Exact-MDP leaf selection assuming only common interlacing of siblings.
All conditional real-rootedness obligations are discharged automatically by
`prefixMDPInterlacing_of_childrenCommon`. -/
theorem select_coloring_of_childrenCommon
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hk : 0 < k)
    (H : PrefixMDPChildrenCommon A hA) :
    ∃ c : Coloring n k,
      ∀ x, IsRootUpperBound (prefixConditionalAverage A hA n []) x →
        IsRootUpperBound (realColoringPolynomial A hA c) x := by
  exact select_coloring_from_root A hA hk
    (prefixMDPInterlacing_of_childrenCommon A hA hk H)

end CommutatorTheorem.BTMDPStability
