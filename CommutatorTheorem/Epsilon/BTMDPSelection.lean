import CommutatorTheorem.Epsilon.BTMixedDeterminantal
import CommutatorTheorem.Epsilon.BTInterlacing
import CommutatorTheorem.Epsilon.BTDirectProof

/-!
# Real mixed-determinantal polynomials and the finite selection layer

This file isolates the exact finite selection argument in the
Ravichandran--Srivastava restricted-invertibility proof.  The leaf attached to
a coloring is the product of the characteristic polynomials of the color
compressions.  For Hermitian matrices those polynomials have real
coefficients; we construct the real polynomial directly from the real
eigenvalues, avoiding a noncomputable choice of real parts of complex
coefficients.

The last section packages the real-stability input as a *property* of the
concrete MDP deletion tree and proves the whole coordinate-by-coordinate
selection step from that property.  No theorem in this file introduces an
axiom.  The remaining analytic work is therefore sharply separated into:

* real stability/common interlacing for the conditional MDP averages;
* the univariate derivative root bound; and
* the root-shrinking comparison between an MDP and its matrix family.
-/

open scoped BigOperators Polynomial

namespace CommutatorTheorem.BTMDPSelection

open CommutatorTheorem
open CommutatorTheorem.BTMixedDet
open CommutatorTheorem.BTMixedDeterminantal
open Polynomial

/-! ## Real forms of the Hermitian characteristic polynomials -/

/-- The characteristic polynomial of a Hermitian complex matrix, written over
`ℝ` using its real eigenvalues. -/
noncomputable def realCharpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ)
    (hM : M.IsHermitian) : ℝ[X] :=
  ∏ i : ι, (X - C (hM.eigenvalues i))

/-- Extending coefficients from `ℝ` to `ℂ` recovers the ordinary
characteristic polynomial. -/
theorem realCharpoly_map_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ)
    (hM : M.IsHermitian) :
    (realCharpoly M hM).map Complex.ofRealHom = M.charpoly := by
  rw [hM.charpoly_eq]
  simp [realCharpoly, Polynomial.map_prod]

/-- The real Hermitian characteristic polynomial is monic. -/
theorem realCharpoly_monic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ)
    (hM : M.IsHermitian) : (realCharpoly M hM).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i _
  exact monic_X_sub_C _

/-- Its degree is the matrix dimension. -/
theorem realCharpoly_natDegree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ)
    (hM : M.IsHermitian) : (realCharpoly M hM).natDegree = Fintype.card ι := by
  rw [realCharpoly, Polynomial.natDegree_prod_of_monic]
  · simp
  · intro i _
    exact monic_X_sub_C _

/-- The real Hermitian characteristic polynomial is real-rooted. -/
theorem realCharpoly_realRooted {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ)
    (hM : M.IsHermitian) : RealRooted (realCharpoly M hM) := by
  apply Polynomial.Splits.prod
  intro i _
  exact Polynomial.Splits.X_sub_C _

/-! ## Real exact-MDP leaves and their average -/

/-- Real form of one exact mixed-determinantal leaf. -/
noncomputable def realColoringPolynomial {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) : ℝ[X] :=
  ∏ a : Fin k,
    realCharpoly (BTMixedDet.principalCompression (A a) c a)
      (BTMixedDet.principalCompression_isHermitian (hA a) c a)

/-- The real leaf maps to the complex leaf already defined in
`BTMixedDeterminantal`. -/
theorem realColoringPolynomial_map_complex {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) :
    (realColoringPolynomial A hA c).map Complex.ofRealHom =
      coloringPolynomial A c := by
  simp only [realColoringPolynomial, coloringPolynomial]
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro a _
  exact realCharpoly_map_complex _ _

/-- Every real exact-MDP leaf is monic. -/
theorem realColoringPolynomial_monic {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) :
    (realColoringPolynomial A hA c).Monic := by
  rw [realColoringPolynomial]
  apply Polynomial.monic_prod_of_monic
  intro a _
  exact realCharpoly_monic _ _

/-- Every real exact-MDP leaf has degree `n`. -/
theorem realColoringPolynomial_natDegree {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) :
    (realColoringPolynomial A hA c).natDegree = n := by
  have hmap := congrArg Polynomial.natDegree
    (realColoringPolynomial_map_complex A hA c)
  rw [Polynomial.natDegree_map Complex.ofRealHom] at hmap
  simpa [coloringPolynomial_natDegree A c] using hmap

/-- Every Hermitian leaf is real-rooted, without any stability input. -/
theorem realColoringPolynomial_realRooted {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) :
    RealRooted (realColoringPolynomial A hA c) := by
  rw [realColoringPolynomial]
  apply Polynomial.Splits.prod
  intro a _
  exact realCharpoly_realRooted _ _

/-- Uniform real average of the exact mixed-determinantal leaves. -/
noncomputable def realMixedDeterminantalPolynomial {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) : ℝ[X] :=
  ((Fintype.card (Coloring n k) : ℝ)⁻¹) •
    ∑ c : Coloring n k, realColoringPolynomial A hA c

/-- The real uniform average maps to the complex exact MDP. -/
theorem realMixedDeterminantalPolynomial_map_complex {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    (realMixedDeterminantalPolynomial A hA).map Complex.ofRealHom =
      mixedDeterminantalPolynomial A := by
  simp only [realMixedDeterminantalPolynomial, mixedDeterminantalPolynomial,
    Polynomial.map_smul, Polynomial.map_sum, realColoringPolynomial_map_complex]
  congr 1
  simp

/-- The real exact MDP is monic when the family is nonempty. -/
theorem realMixedDeterminantalPolynomial_monic {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    (realMixedDeterminantalPolynomial A hA).Monic := by
  apply Polynomial.monic_of_injective Complex.ofRealHom.injective
  rw [realMixedDeterminantalPolynomial_map_complex]
  exact mixedDeterminantalPolynomial_monic hk A

/-- The real exact MDP has degree `n`. -/
theorem realMixedDeterminantalPolynomial_natDegree {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    (realMixedDeterminantalPolynomial A hA).natDegree = n := by
  have hmap := congrArg Polynomial.natDegree
    (realMixedDeterminantalPolynomial_map_complex A hA)
  rw [Polynomial.natDegree_map Complex.ofRealHom] at hmap
  simpa [mixedDeterminantalPolynomial_natDegree hk A] using hmap

/-- The real exact MDP has zero next coefficient for a zero-diagonal family. -/
theorem realMixedDeterminantalPolynomial_nextCoeff_eq_zero {n k : ℕ}
    (hk : 0 < k) (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (hzd : ∀ a, ZeroDiag (A a)) :
    (realMixedDeterminantalPolynomial A hA).nextCoeff = 0 := by
  have hmap := congrArg Polynomial.nextCoeff
    (realMixedDeterminantalPolynomial_map_complex A hA)
  rw [Polynomial.nextCoeff_map Complex.ofRealHom.injective] at hmap
  rw [mixedDeterminantalPolynomial_nextCoeff_eq_zero hk hzd] at hmap
  exact Complex.ofReal_injective (by simpa using hmap)

/-! ## A reusable finite deletion-tree selector -/

/-- Uniform weight on the coordinates of a nonempty finite set. -/
noncomputable def deletionWeight {α : Type*} [DecidableEq α]
    (s : Finset α) (_i : {i // i ∈ s}) : ℝ := (s.card : ℝ)⁻¹

/-- The polynomial family obtained by deleting one coordinate from `s`. -/
noncomputable def deletionChildPolynomial {α : Type*} [DecidableEq α]
    (p : Finset α → ℝ[X]) (s : Finset α) (i : {i // i ∈ s}) : ℝ[X] :=
  p (s.erase i.1)

/-- A normalized conditional interlacing tree down to cardinality `d`.

`parent_average` is the exact conditional-expectation identity.  In the MDP
application its proof is obtained from
`derivative q_s = ∑_{i∈s} q_{s.erase i}` after normalizing iterated
derivatives by their descending factorial leading coefficient. -/
structure DeletionInterlacingTree {α : Type*} [DecidableEq α]
    (d : ℕ) (p : Finset α → ℝ[X]) : Prop where
  realRooted : ∀ s, d ≤ s.card → RealRooted (p s)
  natDegree : ∀ s, d ≤ s.card → (p s).natDegree = d
  children_common : ∀ s, d < s.card →
    HasCommonInterlacer (Finset.univ : Finset {i // i ∈ s})
      (deletionChildPolynomial p s)
  parent_average : ∀ s, d < s.card →
    p s = polynomialWeightedSum (Finset.univ : Finset {i // i ∈ s})
      (deletionWeight s) (deletionChildPolynomial p s)

private lemma sum_deletionWeight_eq_one {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) :
    ∑ i ∈ (Finset.univ : Finset {i // i ∈ s}), deletionWeight s i = 1 := by
  simp only [deletionWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast hs.card_ne_zero)

private lemma deletionWeight_nonneg {α : Type*} [DecidableEq α]
    (s : Finset α) (i : {i // i ∈ s}) : 0 ≤ deletionWeight s i := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedFintypeInType false in
/-- Coordinate-by-coordinate selection in any normalized deletion tree.

The selected `t` has exactly the target cardinality and every root of its
polynomial is bounded by every upper root bound for the initial polynomial.
This transitive formulation is what permits iteration without choosing a
largest root at every recursive call. -/
theorem DeletionInterlacingTree.select_subset
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : ℕ} {p : Finset α → ℝ[X]}
    (T : DeletionInterlacingTree d p) (hd : 0 < d)
    (s : Finset α) (hds : d ≤ s.card) :
    ∃ t : Finset α, t ⊆ s ∧ t.card = d ∧
      ∀ x, IsRootUpperBound (p s) x → IsRootUpperBound (p t) x := by
  classical
  let motive : ℕ → Prop := fun gap =>
    ∀ s : Finset α, d ≤ s.card → s.card - d = gap →
      ∃ t : Finset α, t ⊆ s ∧ t.card = d ∧
        ∀ x, IsRootUpperBound (p s) x → IsRootUpperBound (p t) x
  have hmot : ∀ gap, (∀ smaller, smaller < gap → motive smaller) → motive gap := by
    intro gap ih s hds hgap
    by_cases hbase : s.card = d
    · refine ⟨s, Finset.Subset.rfl, hbase, ?_⟩
      intro x hx
      exact hx
    · have hlt : d < s.card := lt_of_le_of_ne hds (Ne.symm hbase)
      have hs : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hs0
        rw [hs0] at hlt
        simp at hlt
      let I := {i // i ∈ s}
      let child : I → ℝ[X] := deletionChildPolynomial p s
      let w : I → ℝ := deletionWeight s
      have hw : ∀ i ∈ (Finset.univ : Finset I), 0 ≤ w i := by
        intro i _
        exact deletionWeight_nonneg s i
      have hwsum : ∑ i ∈ (Finset.univ : Finset I), w i = 1 := by
        exact sum_deletionWeight_eq_one hs
      have hcommon : HasCommonInterlacer (Finset.univ : Finset I) child := by
        simpa [I, child] using T.children_common s hlt
      have havg :
          polynomialWeightedSum (Finset.univ : Finset I) w child = p s := by
        simpa [I, w, child] using (T.parent_average s hlt).symm
      have hrealAvg :
          RealRooted (polynomialWeightedSum (Finset.univ : Finset I) w child) := by
        rw [havg]
        exact T.realRooted s hds
      obtain ⟨y, hyLargest, i, _hi, hiBound⟩ :=
        hcommon.exists_largestRoot_and_member_below_of_realRooted
          w hw hwsum hrealAvg
      let s' := s.erase i.1
      have hi_mem : i.1 ∈ s := i.2
      have hs'card : s'.card = s.card - 1 := by
        simp [s', Finset.card_erase_of_mem hi_mem]
      have hds' : d ≤ s'.card := by
        rw [hs'card]
        omega
      have hgap' : s'.card - d < gap := by
        rw [← hgap]
        rw [hs'card]
        omega
      obtain ⟨t, hts', htcard, htroot⟩ :=
        ih (s'.card - d) hgap' s' hds' rfl
      refine ⟨t, hts'.trans (Finset.erase_subset _ _), htcard, ?_⟩
      intro x hsBound
      have hyx : y ≤ x := hsBound y (by simpa [havg] using hyLargest.isRoot)
      have hchildY : IsRootUpperBound (p s') y := by
        simpa [I, child, s'] using hiBound
      have htY : IsRootUpperBound (p t) y := htroot y hchildY
      intro r hr
      exact (htY r hr).trans hyx
  have hall : ∀ gap, motive gap := fun gap => Nat.strong_induction_on gap hmot
  exact hall (s.card - d) s hds rfl

/-! ## The concrete conditional MDP deletion tree -/

/-- Compress a Hermitian family to a concrete coordinate finset. -/
noncomputable def restrictFamilyToFinset {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n))
    (a : Fin k) : Matrix (Fin s.card) (Fin s.card) ℂ :=
  (A a).submatrix (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl)

theorem restrictFamilyToFinset_isHermitian {n k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ a, (A a).IsHermitian) (s : Finset (Fin n)) (a : Fin k) :
    (restrictFamilyToFinset A s a).IsHermitian :=
  (hA a).submatrix (s.orderEmbOfFin rfl)

/-- Exact real MDP of the common compression to `s`. -/
noncomputable def restrictedMDP {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (s : Finset (Fin n)) : ℝ[X] :=
  realMixedDeterminantalPolynomial (restrictFamilyToFinset A s)
    (restrictFamilyToFinset_isHermitian hA s)

/-- The normalized conditional polynomial at `s` for a final cardinality `d`.
It is an iterated derivative of the restricted exact MDP, divided by its
descending-factorial leading coefficient. -/
noncomputable def normalizedConditionalMDP {n k d : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (s : Finset (Fin n)) : ℝ[X] :=
  ((s.card.descFactorial (s.card - d) : ℝ)⁻¹) •
    Polynomial.derivative^[s.card - d] (restrictedMDP A hA s)

/-- The exact one-coordinate derivative identity for restricted MDPs.

This is deliberately an ordinary proposition: proving it is finite
determinant algebra, while the stronger common-interlacing property below is
the real-stability theorem. -/
def MDPDeletionDerivativeIdentity {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) : Prop :=
  ∀ s : Finset (Fin n),
    (restrictedMDP A hA s).derivative =
      ∑ i : {i // i ∈ s}, restrictedMDP A hA (s.erase i.1)

/-- Concrete real-stability/common-interlacing input for the normalized MDP
deletion tree.  Once this proposition is proved, `select_restrictedMDP`
performs every remaining coordinate choice. -/
def MDPConditionalInterlacing {n k d : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) : Prop :=
  DeletionInterlacingTree d (normalizedConditionalMDP (d := d) A hA)

/-- Exact MDP selection from the conditional real-stability input. -/
theorem select_restrictedMDP {n k d : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (hd : 0 < d) (hdn : d ≤ n)
    (hstable : MDPConditionalInterlacing (d := d) A hA) :
    ∃ s : Finset (Fin n), s.card = d ∧
      ∀ x,
        IsRootUpperBound
          (normalizedConditionalMDP (d := d) A hA Finset.univ) x →
        IsRootUpperBound (restrictedMDP A hA s) x := by
  have hcard : d ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hdn
  change DeletionInterlacingTree d
    (normalizedConditionalMDP (d := d) A hA) at hstable
  obtain ⟨s, _hsub, hscard, hsroot⟩ :=
    DeletionInterlacingTree.select_subset hstable hd
      (Finset.univ : Finset (Fin n)) hcard
  refine ⟨s, hscard, ?_⟩
  have hleaf : normalizedConditionalMDP (d := d) A hA s = restrictedMDP A hA s := by
    simp [normalizedConditionalMDP, hscard]
  intro x hx
  simpa [hleaf] using hsroot x hx

/-! ## Conditional prefix averages for the exact coloring-product MDP -/

/-- A full coloring represented by a list of exactly `n` colors. -/
def coloringOfFullList {n k : ℕ} (p : List (Fin k)) (hp : p.length = n) :
    Coloring n k := fun i => p.get (Fin.cast hp.symm i)

/-- The exact conditional average below a coloring prefix.

The first argument is the number of coordinates that remain to be colored.
At an internal node this is *definitionally* the uniform average of the `k`
children; at a leaf it is the real coloring-product polynomial.  Calls for
which `prefix.length + remaining ≠ n` are harmless and are used nowhere in the
selection theorem. -/
noncomputable def prefixConditionalAverage {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) : ℕ → List (Fin k) → ℝ[X]
  | 0, p =>
      if hp : p.length = n then
        realColoringPolynomial A hA (coloringOfFullList p hp)
      else 0
  | remaining + 1, p =>
      ((k : ℝ)⁻¹) •
        ∑ a : Fin k, prefixConditionalAverage A hA remaining (p ++ [a])

/-- Uniform weights on the `k` next-color choices. -/
noncomputable def prefixWeight {k : ℕ} (_a : Fin k) : ℝ := (k : ℝ)⁻¹

private lemma sum_prefixWeight_eq_one {k : ℕ} (hk : 0 < k) :
    ∑ a ∈ (Finset.univ : Finset (Fin k)), prefixWeight a = 1 := by
  simp only [prefixWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hk))

private lemma prefixWeight_nonneg {k : ℕ} (a : Fin k) :
    0 ≤ prefixWeight a := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- The parent conditional average is exactly the uniform convex combination
of its one-coordinate extensions. -/
theorem prefixConditionalAverage_succ_eq_weightedSum {n k remaining : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (p : List (Fin k)) :
    prefixConditionalAverage A hA (remaining + 1) p =
      polynomialWeightedSum (Finset.univ : Finset (Fin k)) prefixWeight
        (fun a => prefixConditionalAverage A hA remaining (p ++ [a])) := by
  simp [prefixConditionalAverage, polynomialWeightedSum, prefixWeight,
    Finset.smul_sum]

/-- The only real-stability input needed by the prefix selector.

It asserts real-rootedness of every valid conditional average and a common
interlacer for its children.  The conditional-expectation identity itself is
not part of this input: it is the theorem immediately above. -/
structure PrefixMDPInterlacing {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) : Prop where
  realRooted : ∀ remaining p, p.length + remaining = n →
    RealRooted (prefixConditionalAverage A hA remaining p)
  children_common : ∀ remaining p, p.length + (remaining + 1) = n →
    HasCommonInterlacer (Finset.univ : Finset (Fin k))
      (fun a => prefixConditionalAverage A hA remaining (p ++ [a]))

/-- Starting at any valid prefix, repeated common-interlacer selection reaches
a complete coloring whose largest root is no larger than the largest root of
the conditional average at that prefix. -/
theorem PrefixMDPInterlacing.select_coloring
    {n k : ℕ} {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    {hA : ∀ a, (A a).IsHermitian}
    (H : PrefixMDPInterlacing A hA) (hk : 0 < k)
    (remaining : ℕ) (p : List (Fin k))
    (hvalid : p.length + remaining = n) :
    ∃ c : Coloring n k,
      ∀ x, IsRootUpperBound (prefixConditionalAverage A hA remaining p) x →
        IsRootUpperBound (realColoringPolynomial A hA c) x := by
  induction remaining generalizing p with
  | zero =>
      have hp : p.length = n := by omega
      refine ⟨coloringOfFullList p hp, ?_⟩
      intro x hx
      simpa [prefixConditionalAverage, hp] using hx
  | succ remaining ih =>
      let child : Fin k → ℝ[X] := fun a =>
        prefixConditionalAverage A hA remaining (p ++ [a])
      let w : Fin k → ℝ := prefixWeight
      have hw : ∀ a ∈ (Finset.univ : Finset (Fin k)), 0 ≤ w a := by
        intro a _
        exact prefixWeight_nonneg a
      have hwsum : ∑ a ∈ (Finset.univ : Finset (Fin k)), w a = 1 := by
        exact sum_prefixWeight_eq_one hk
      have hcommon : HasCommonInterlacer (Finset.univ : Finset (Fin k)) child := by
        simpa [child] using H.children_common remaining p hvalid
      have havg :
          polynomialWeightedSum (Finset.univ : Finset (Fin k)) w child =
            prefixConditionalAverage A hA (remaining + 1) p := by
        simpa [w, child] using
          (prefixConditionalAverage_succ_eq_weightedSum A hA p).symm
      have hrealAvg :
          RealRooted (polynomialWeightedSum (Finset.univ : Finset (Fin k)) w child) := by
        rw [havg]
        exact H.realRooted (remaining + 1) p hvalid
      obtain ⟨y, hyLargest, a, _ha, haBound⟩ :=
        hcommon.exists_largestRoot_and_member_below_of_realRooted
          w hw hwsum hrealAvg
      have hchildvalid : (p ++ [a]).length + remaining = n := by
        simp only [List.length_append, List.length_singleton]
        omega
      obtain ⟨c, hc⟩ := ih (p ++ [a]) hchildvalid
      refine ⟨c, ?_⟩
      intro x hx
      have hyx : y ≤ x := hx y (by simpa [havg] using hyLargest.isRoot)
      have hchildY :
          IsRootUpperBound
            (prefixConditionalAverage A hA remaining (p ++ [a])) y := by
        simpa [child] using haBound
      have hleafY : IsRootUpperBound (realColoringPolynomial A hA c) y :=
        hc y hchildY
      intro r hr
      exact (hleafY r hr).trans hyx

/-- Root-level exact-MDP leaf selection.  This is the complete finite
interlacing-family argument: after `PrefixMDPInterlacing` is supplied, no
further choice or polynomial fact is assumed. -/
theorem select_coloring_from_root {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hk : 0 < k)
    (H : PrefixMDPInterlacing A hA) :
    ∃ c : Coloring n k,
      ∀ x, IsRootUpperBound (prefixConditionalAverage A hA n []) x →
        IsRootUpperBound (realColoringPolynomial A hA c) x := by
  apply H.select_coloring hk n []
  simp

end CommutatorTheorem.BTMDPSelection
