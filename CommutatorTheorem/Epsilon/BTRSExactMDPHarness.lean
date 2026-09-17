import CommutatorTheorem.Epsilon.BTRSStabilityBridge
import CommutatorTheorem.Epsilon.BTMDPInterlacingFromConvex

/-!
# Exact-MDP harness for the Ravichandran--Srivastava stability proof

This file constructs the precise stable multivariate polynomials whose
diagonalizations represent conditional exact MDPs and convex combinations of
deletion siblings.  From the finite determinant-expansion identities it
derives all real-rootedness and interlacing conclusions.

The expansion identities themselves are collected in the ordinary
proposition `RSExactConditionalMDPExpansion`.  It contains no analytic claim:
it says only that two explicitly defined real polynomials are equal up to a
positive scalar.  This cleanly separates finite determinant algebra from the
single multivariate Gauss--Lucas/Hurwitz closure proposition.
-/

namespace CommutatorTheorem.BTRSExactMDPHarness

open scoped BigOperators Polynomial
open Polynomial Finset
open CommutatorTheorem
open CommutatorTheorem.BTRealStabilityClosure
open CommutatorTheorem.BTDeterminantStability
open CommutatorTheorem.BTRSStabilityBridge
open CommutatorTheorem.BTMDPSelection
open CommutatorTheorem.BTMDPInterlacingFromConvex
open CommutatorTheorem.BTFellPair

/-- A list containing every coordinate exactly `r` times.  Its particular
order is irrelevant because coordinate partial derivatives commute, but a
list gives a convenient definitional iteration. -/
noncomputable def repeatedCoordinateList (σ : Type*) [Fintype σ]
    [DecidableEq σ] (r : ℕ) : List σ :=
  (Finset.univ.toList).flatMap (List.replicate r)

/-- The real nonnegative directional derivative. -/
noncomputable def realDirectionalDerivative
    {σ : Type*} [Fintype σ] (w : σ → ℝ) (p : MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ :=
  ∑ i : σ, MvPolynomial.C (w i) * MvPolynomial.pderiv i p

/-- Complexification commutes with real directional differentiation. -/
theorem map_realDirectionalDerivative
    {σ : Type*} [Fintype σ]
    (w : σ → ℝ) (p : MvPolynomial σ ℝ) :
    MvPolynomial.map Complex.ofRealHom (realDirectionalDerivative w p) =
      nonnegativeDirectionalDerivative w
        (MvPolynomial.map Complex.ofRealHom p) := by
  classical
  simp only [realDirectionalDerivative, nonnegativeDirectionalDerivative,
    map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.pderiv_map]
  congr 1

/-- Iterated differentiation in the all-ones direction.  On diagonal
specialization this is ordinary univariate differentiation. -/
noncomputable def iteratedUniformDirectionalDerivative
    {σ : Type*} [Fintype σ] :
    ℕ → MvPolynomial σ ℝ → MvPolynomial σ ℝ
  | 0, p => p
  | r + 1, p => iteratedUniformDirectionalDerivative r
      (realDirectionalDerivative (fun _ ↦ 1) p)

@[simp] theorem iteratedUniformDirectionalDerivative_zero
    {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) :
    iteratedUniformDirectionalDerivative 0 p = p := rfl

@[simp] theorem iteratedUniformDirectionalDerivative_succ
    {σ : Type*} [Fintype σ] (r : ℕ) (p : MvPolynomial σ ℝ) :
    iteratedUniformDirectionalDerivative (r + 1) p =
      iteratedUniformDirectionalDerivative r
        (realDirectionalDerivative (fun _ ↦ 1) p) := rfl

/-- Complexification commutes with the iterated all-ones derivative. -/
theorem map_iteratedUniformDirectionalDerivative
    {σ : Type*} [Fintype σ]
    (r : ℕ) (p : MvPolynomial σ ℝ) :
    MvPolynomial.map Complex.ofRealHom
        (iteratedUniformDirectionalDerivative r p) =
      ((nonnegativeDirectionalDerivative (fun _ : σ ↦ 1))^[r])
        (MvPolynomial.map Complex.ofRealHom p) := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
      rw [iteratedUniformDirectionalDerivative_succ, ih,
        Function.iterate_succ_apply]
      rw [map_realDirectionalDerivative]

/-- The determinant product after differentiating each coordinate `k - 1`
times, the standard exact-MDP base polynomial. -/
noncomputable def rsExactMDPBase {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin n) ℝ :=
  iteratedPDeriv (repeatedCoordinateList (Fin n) (k - 1))
    (realHermitianDetProduct A)

/-- The multivariate representative of a degree-`d` conditional MDP. -/
noncomputable def rsConditionalPolynomial {n k d : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin n) ℝ :=
  iteratedUniformDirectionalDerivative (n - d) (rsExactMDPBase A)

/-- The index in the canonical `Fin s.card` enumeration corresponding to an
element of `s`. -/
noncomputable def finIndexOfMem {n : ℕ} (s : Finset (Fin n))
    (i : {x // x ∈ s}) : Fin s.card :=
  (s.orderIsoOfFin rfl).symm i

/-- Direction with weights `t` and `1-t` on two deletion coordinates. -/
noncomputable def deletionPairDirection {n : ℕ}
    (s : Finset (Fin n)) (i j : {x // x ∈ s}) (t : ℝ) :
    Fin s.card → ℝ :=
  fun x ↦ (if x = finIndexOfMem s i then t else 0) +
    (if x = finIndexOfMem s j then 1 - t else 0)

theorem deletionPairDirection_nonneg {n : ℕ}
    (s : Finset (Fin n)) (i j : {x // x ∈ s})
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ x, 0 ≤ deletionPairDirection s i j t x := by
  intro x
  unfold deletionPairDirection
  split_ifs <;> linarith

/-- The stable multivariate representative of a convex combination of two
degree-`d` deletion siblings. -/
noncomputable def rsDeletionPairPolynomial {n k d : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (t : ℝ) : MvPolynomial (Fin n) ℝ :=
  iteratedUniformDirectionalDerivative (n - 1 - d)
    (realDirectionalDerivative
      (fun x ↦ (if x = i then t else 0) +
        (if x = j then 1 - t else 0))
      (rsExactMDPBase A))

/-- The base determinant derivative remains stable-or-zero. -/
theorem rsExactMDPBase_stable
    (H : MultivariateGaussLucasHurwitz)
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    MvStableOrZero
      (MvPolynomial.map Complex.ofRealHom (rsExactMDPBase A)) := by
  exact iteratedPDeriv_realHermitianDetProduct_stable H A hA _

/-- Iterated all-ones differentiation preserves stability-or-zero. -/
theorem iteratedUniformDirectionalDerivative_stable
    (H : MultivariateGaussLucasHurwitz)
    {σ : Type} [Fintype σ]
    (r : ℕ) (p : MvPolynomial σ ℝ)
    (hp : MvStableOrZero (MvPolynomial.map Complex.ofRealHom p)) :
    MvStableOrZero
      (MvPolynomial.map Complex.ofRealHom
        (iteratedUniformDirectionalDerivative r p)) := by
  rw [map_iteratedUniformDirectionalDerivative]
  induction r with
  | zero => exact hp
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact H σ inferInstance _ (fun _ ↦ 1) ih (by simp)

/-- Every conditional representative is stable-or-zero. -/
theorem rsConditionalPolynomial_stable
    (H : MultivariateGaussLucasHurwitz)
    {n k d : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    MvStableOrZero
      (MvPolynomial.map Complex.ofRealHom
        (rsConditionalPolynomial (d := d) A)) := by
  exact iteratedUniformDirectionalDerivative_stable H _ _
    (rsExactMDPBase_stable H A hA)

/-- Every pair-deletion representative with convex weights is
stable-or-zero. -/
theorem rsDeletionPairPolynomial_stable
    (H : MultivariateGaussLucasHurwitz)
    {n k d : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (i j : Fin n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MvStableOrZero
      (MvPolynomial.map Complex.ofRealHom
        (rsDeletionPairPolynomial (d := d) A i j t)) := by
  unfold rsDeletionPairPolynomial
  apply iteratedUniformDirectionalDerivative_stable H
  rw [map_realDirectionalDerivative]
  apply H (Fin n) inferInstance _ _ (rsExactMDPBase_stable H A hA)
  intro x
  split_ifs <;> linarith

/-! ## Diagonal differentiation identities -/

/-- Diagonalization sends a directional derivative to the corresponding
weighted sum of diagonalized coordinate derivatives. -/
theorem diagonalizeReal_realDirectionalDerivative
    {σ : Type*} [Fintype σ] (w : σ → ℝ)
    (p : MvPolynomial σ ℝ) :
    diagonalizeReal (realDirectionalDerivative w p) =
      ∑ i : σ, w i • diagonalizeReal (MvPolynomial.pderiv i p) := by
  classical
  simp [realDirectionalDerivative, diagonalizeReal, smul_eq_C_mul]

/-- Differentiating a diagonal specialization is the same as taking the
all-ones multivariate directional derivative before specialization. -/
theorem derivative_diagonalizeReal
    {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) :
    Polynomial.derivative (diagonalizeReal p) =
      diagonalizeReal (realDirectionalDerivative (fun _ ↦ 1) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [diagonalizeReal, realDirectionalDerivative]
  | add p q hp hq =>
      rw [show diagonalizeReal (p + q) =
        diagonalizeReal p + diagonalizeReal q by simp [diagonalizeReal]]
      rw [Polynomial.derivative_add, hp, hq]
      simp [realDirectionalDerivative, diagonalizeReal,
        Finset.sum_add_distrib, mul_add]
  | mul_X p i hp =>
      rw [show diagonalizeReal (p * MvPolynomial.X i) =
        diagonalizeReal p * Polynomial.X by simp [diagonalizeReal]]
      rw [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one, hp]
      rw [show realDirectionalDerivative (fun _ ↦ 1)
        (p * MvPolynomial.X i) =
          realDirectionalDerivative (fun _ ↦ 1) p * MvPolynomial.X i + p by
        unfold realDirectionalDerivative
        simp only [MvPolynomial.C_1, one_mul, MvPolynomial.pderiv_mul,
          MvPolynomial.pderiv_X]
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        congr 1
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [hji]
        · simp]
      simp [diagonalizeReal]

/-- The preceding identity iterates. -/
theorem diagonalizeReal_iteratedUniformDirectionalDerivative
    {σ : Type*} [Fintype σ] (r : ℕ) (p : MvPolynomial σ ℝ) :
    diagonalizeReal (iteratedUniformDirectionalDerivative r p) =
      Polynomial.derivative^[r] (diagonalizeReal p) := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
      rw [iteratedUniformDirectionalDerivative_succ, ih,
        ← derivative_diagonalizeReal]
      rw [Function.iterate_succ_apply]

/-- Iterated polynomial differentiation is additive. -/
theorem iterateDerivative_add (r : ℕ) (p q : ℝ[X]) :
    Polynomial.derivative^[r] (p + q) =
      Polynomial.derivative^[r] p + Polynomial.derivative^[r] q := by
  induction r generalizing p q with
  | zero => rfl
  | succ r ih =>
      simp only [Function.iterate_succ_apply', ih, Polynomial.derivative_add]

/-- The additive two-coordinate direction diagonalizes to the desired convex
linear combination, including the coincident-coordinate case. -/
theorem diagonalizeReal_deletionPairDerivative
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℝ) (i j : σ) (t : ℝ) :
    diagonalizeReal
        (realDirectionalDerivative
          (fun x ↦ (if x = i then t else 0) +
            (if x = j then 1 - t else 0)) p) =
      t • diagonalizeReal (MvPolynomial.pderiv i p) +
        (1 - t) • diagonalizeReal (MvPolynomial.pderiv j p) := by
  classical
  rw [diagonalizeReal_realDirectionalDerivative]
  simp_rw [add_smul]
  rw [Finset.sum_add_distrib]
  simp

/-! ## The finite determinant-algebra sub-harness -/

/-- The unrestricted draft of the local determinant expansion.  It is kept
for boundary auditing: at `k = 0` it is false because the determinant product
is the empty product while the coloring average is zero. -/
def RSExactMDPBaseDeletionExpansionUnrestricted : Prop :=
  ∀ (n k : ℕ) (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (s : Finset (Fin n)),
    (∃ b : ℝ, 0 < b ∧
      diagonalizeReal
          (rsExactMDPBase (restrictFamilyToFinset A s)) =
        b • restrictedMDP A hA s) ∧
    (s.Nonempty → ∃ c : ℝ, 0 < c ∧
      ∀ i : {x // x ∈ s},
        diagonalizeReal
            (MvPolynomial.pderiv (finIndexOfMem s i)
              (rsExactMDPBase (restrictFamilyToFinset A s))) =
          c • restrictedMDP A hA (s.erase i.1))

/-- A smaller, local form of the exact determinant expansion for a nonempty
color set.  It asks only for the base exact MDP and its one-coordinate
deletions, with a common positive deletion scalar at each node.  The calculus
in this file propagates these identities to every conditional derivative and
sibling convex combination. -/
def RSExactMDPBaseDeletionExpansion : Prop :=
  ∀ (n k : ℕ), 0 < k →
    ∀ (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
      (hA : ∀ a, (A a).IsHermitian) (s : Finset (Fin n)),
    (∃ b : ℝ, 0 < b ∧
      diagonalizeReal
          (rsExactMDPBase (restrictFamilyToFinset A s)) =
        b • restrictedMDP A hA s) ∧
    (s.Nonempty → ∃ c : ℝ, 0 < c ∧
      ∀ i : {x // x ∈ s},
        diagonalizeReal
            (MvPolynomial.pderiv (finIndexOfMem s i)
              (rsExactMDPBase (restrictFamilyToFinset A s))) =
          c • restrictedMDP A hA (s.erase i.1))

/-- The purely algebraic determinant-expansion statement needed for all
conditional nodes and all deletion-sibling convex combinations.  The family
is first compressed to `s`, so all matrices and directions use the canonical
index type `Fin s.card`.

The constants are deliberately existential: only positivity matters for
real-rootedness, while the explicit expansion gives factorial ratios. -/
def RSExactConditionalMDPExpansion : Prop :=
  ∀ (n k d : ℕ), 0 < k →
    ∀ (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian),
    (∀ (s : Finset (Fin n)), d ≤ s.card →
      ∃ c : ℝ, 0 < c ∧
        diagonalizeReal
            (rsConditionalPolynomial (d := d)
              (restrictFamilyToFinset A s)) =
          c • normalizedConditionalMDP (d := d) A hA s) ∧
    (∀ (s : Finset (Fin n)), d < s.card →
      ∀ (i j : {x // x ∈ s}) (t : ℝ), 0 ≤ t → t ≤ 1 →
        ∃ c : ℝ, 0 < c ∧
          diagonalizeReal
              (rsDeletionPairPolynomial (d := d)
                (restrictFamilyToFinset A s)
                (finIndexOfMem s i) (finIndexOfMem s j) t) =
            c •
              (t • deletionChildPolynomial
                  (normalizedConditionalMDP (d := d) A hA) s i +
                (1 - t) • deletionChildPolynomial
                  (normalizedConditionalMDP (d := d) A hA) s j))

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- The base exact-MDP identity already implies every conditional-node
identity by all-ones differentiation and descending-factorial
normalization. -/
theorem rsConditionalNodeExpansion_of_baseDeletion
    (B : RSExactMDPBaseDeletionExpansion)
    {n k d : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hk : 0 < k)
    (s : Finset (Fin n)) (hds : d ≤ s.card) :
    ∃ c : ℝ, 0 < c ∧
      diagonalizeReal
          (rsConditionalPolynomial (d := d)
            (restrictFamilyToFinset A s)) =
        c • normalizedConditionalMDP (d := d) A hA s := by
  obtain ⟨b, hb, hbase⟩ := (B n k hk A hA s).1
  let D : ℕ := s.card.descFactorial (s.card - d)
  have hDpos : 0 < D := by
    exact Nat.descFactorial_pos.mpr (Nat.sub_le _ _)
  have hDRpos : 0 < (D : ℝ) := by exact_mod_cast hDpos
  refine ⟨b * D, mul_pos hb hDRpos, ?_⟩
  rw [rsConditionalPolynomial,
    diagonalizeReal_iteratedUniformDirectionalDerivative]
  rw [hbase, Polynomial.iterate_derivative_smul]
  rw [normalizedConditionalMDP]
  simp only [smul_smul]
  congr 1
  dsimp [D]
  have hD0 : (s.card.descFactorial (s.card - d) : ℝ) ≠ 0 :=
    ne_of_gt hDRpos
  field_simp

/-- The one-coordinate deletion identities imply every two-sibling convex
identity; subsequent all-ones derivatives give the conditional target
degree. -/
theorem rsDeletionPairExpansion_of_baseDeletion
    (B : RSExactMDPBaseDeletionExpansion)
    {n k d : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hk : 0 < k)
    (s : Finset (Fin n)) (hds : d < s.card)
    (i j : {x // x ∈ s}) (t : ℝ) :
    ∃ c : ℝ, 0 < c ∧
      diagonalizeReal
          (rsDeletionPairPolynomial (d := d)
            (restrictFamilyToFinset A s)
            (finIndexOfMem s i) (finIndexOfMem s j) t) =
        c •
          (t • deletionChildPolynomial
              (normalizedConditionalMDP (d := d) A hA) s i +
            (1 - t) • deletionChildPolynomial
              (normalizedConditionalMDP (d := d) A hA) s j) := by
  have hs : s.Nonempty :=
    Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le d) hds)
  obtain ⟨c, hc, hdelete⟩ := (B n k hk A hA s).2 hs
  let D : ℕ := (s.card - 1).descFactorial ((s.card - 1) - d)
  have hDpos : 0 < D := by
    apply Nat.descFactorial_pos.mpr
    exact Nat.sub_le _ _
  have hDRpos : 0 < (D : ℝ) := by exact_mod_cast hDpos
  refine ⟨c * D, mul_pos hc hDRpos, ?_⟩
  rw [rsDeletionPairPolynomial,
    diagonalizeReal_iteratedUniformDirectionalDerivative]
  rw [diagonalizeReal_deletionPairDerivative,
    hdelete i, hdelete j]
  simp only [deletionChildPolynomial, normalizedConditionalMDP]
  have hcardi : (s.erase i.1).card = s.card - 1 :=
    Finset.card_erase_of_mem i.2
  have hcardj : (s.erase j.1).card = s.card - 1 :=
    Finset.card_erase_of_mem j.2
  rw [hcardi, hcardj]
  rw [iterateDerivative_add]
  simp only [Polynomial.iterate_derivative_smul]
  simp only [smul_add, smul_smul]
  congr 1 <;> dsimp [D]
  all_goals
    have hD0 : ((s.card - 1).descFactorial ((s.card - 1) - d) : ℝ) ≠ 0 :=
      ne_of_gt hDRpos
    field_simp

/-- The local base-and-deletion determinant expansion implies the full
conditional expansion harness. -/
theorem rsExactConditionalMDPExpansion_of_baseDeletion
    (B : RSExactMDPBaseDeletionExpansion) :
    RSExactConditionalMDPExpansion := by
  intro n k d hk A hA
  constructor
  · intro s hds
    exact rsConditionalNodeExpansion_of_baseDeletion B A hA hk s hds
  · intro s hds i j t _ht0 _ht1
    exact rsDeletionPairExpansion_of_baseDeletion B A hA hk s hds i j t

private theorem realRooted_of_stable_diagonal_eq_pos_smul
    {σ : Type*} {q : MvPolynomial σ ℝ} {p : ℝ[X]} {c : ℝ}
    (hstable : MvStableOrZero (MvPolynomial.map Complex.ofRealHom q))
    (hp0 : p ≠ 0) (hc : 0 < c)
    (heq : diagonalizeReal q = c • p) : RealRooted p := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hreal0 : diagonalizeReal q ≠ 0 := by
    rw [heq]
    exact smul_ne_zero hc0 hp0
  have hcomplex0 : diagonalize (MvPolynomial.map Complex.ofRealHom q) ≠ 0 := by
    rw [← map_diagonalizeReal]
    exact (Polynomial.map_ne_zero_iff Complex.ofReal_injective).2 hreal0
  have hdiag : RealRooted (diagonalizeReal q) :=
    realRooted_diagonalizeReal_of_stable hstable hcomplex0
  rw [heq, smul_eq_C_mul] at hdiag
  exact (splits_mul_iff (C_ne_zero.mpr hc0) hp0).mp hdiag |>.2

/-- The exact expansion plus multivariate derivative closure proves
real-rootedness of every normalized conditional node. -/
theorem conditionalNodesRealRooted_of_rsExpansion
    (H : MultivariateGaussLucasHurwitz)
    (E : RSExactConditionalMDPExpansion)
    {n k d : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    MDPConditionalNodesRealRooted (d := d) A hA := by
  intro s hds
  obtain ⟨c, hc, heq⟩ := (E n k d hk A hA).1 s hds
  apply realRooted_of_stable_diagonal_eq_pos_smul
    (q := rsConditionalPolynomial (d := d) (restrictFamilyToFinset A s))
    (p := normalizedConditionalMDP (d := d) A hA s)
    (c := c)
  · exact rsConditionalPolynomial_stable H _
      (restrictFamilyToFinset_isHermitian hA s)
  · exact (normalizedConditionalMDP_monic hk A hA s hds).ne_zero
  · exact hc
  · exact heq

/-- The exact expansion plus nonnegative directional closure proves
real-rootedness of every two-child convex combination. -/
theorem deletionPairConvexRealRooted_of_rsExpansion
    (H : MultivariateGaussLucasHurwitz)
    (E : RSExactConditionalMDPExpansion)
    {n k d : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    MDPDeletionPairConvexRealRooted (d := d) A hA := by
  intro s hds i j t ht0 ht1
  obtain ⟨c, hc, heq⟩ := (E n k d hk A hA).2 s hds i j t ht0 ht1
  let child := deletionChildPolynomial
    (normalizedConditionalMDP (d := d) A hA) s
  have himonic : (child i).Monic := by
    apply normalizedConditionalMDP_monic hk A hA
    rw [Finset.card_erase_of_mem i.2]
    omega
  have hjmonic : (child j).Monic := by
    apply normalizedConditionalMDP_monic hk A hA
    rw [Finset.card_erase_of_mem j.2]
    omega
  have hidegree : (child i).natDegree = d := by
    apply normalizedConditionalMDP_natDegree hk A hA
    rw [Finset.card_erase_of_mem i.2]
    omega
  have hjdegree : (child j).natDegree = d := by
    apply normalizedConditionalMDP_natDegree hk A hA
    rw [Finset.card_erase_of_mem j.2]
    omega
  have hpmonic : (t • child i + (1 - t) • child j).Monic :=
    monic_convex_combination_of_same_natDegree
      himonic hjmonic hidegree hjdegree t
  apply realRooted_of_stable_diagonal_eq_pos_smul
    (q := rsDeletionPairPolynomial (d := d)
      (restrictFamilyToFinset A s)
      (finIndexOfMem s i) (finIndexOfMem s j) t)
    (p := t • child i + (1 - t) • child j) (c := c)
  · exact rsDeletionPairPolynomial_stable H _
      (restrictFamilyToFinset_isHermitian hA s) _ _ t ht0 ht1
  · exact hpmonic.ne_zero
  · exact hc
  · exact heq

/-- Final stability-to-interlacing assembly: the exact finite expansion,
multivariate Gauss--Lucas/Hurwitz closure, and the root-disjoint pair Fell
core imply the concrete conditional MDP interlacing property. -/
theorem mdpConditionalInterlacing_of_rsExpansion
    (H : MultivariateGaussLucasHurwitz)
    (E : RSExactConditionalMDPExpansion)
    (F : ∀ e : ℕ, 2 ≤ e → RootDisjointPairFellConverseAtDegree e)
    {n k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    MDPConditionalInterlacing (d := d) A hA := by
  exact mdpConditionalInterlacing_of_rootDisjointFell
    hk hd A hA
    (conditionalNodesRealRooted_of_rsExpansion H E hk A hA)
    (deletionPairConvexRealRooted_of_rsExpansion H E hk A hA) F

end CommutatorTheorem.BTRSExactMDPHarness
