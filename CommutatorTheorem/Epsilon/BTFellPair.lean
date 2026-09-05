import CommutatorTheorem.Epsilon.BTInterlacingConverse
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# The two-polynomial Fell converse

This file develops the analytic pair step needed by the finite Fell converse.
The arbitrary-degree statement remains the main real-stability problem; here
we close it completely in degree two (degree one is in
`BTInterlacingConverse`).

For monic quadratics, real-rootedness is nonnegativity of the discriminant.
If the two closed root intervals are disjoint, an explicit convex parameter
makes the discriminant negative.  Therefore the intervals overlap, and any
point in their intersection is the root of a common linear interlacer.
-/

open scoped Polynomial

namespace CommutatorTheorem.BTFellPair

open Polynomial
open CommutatorTheorem

/-- A monic quadratic specified by its two roots. -/
noncomputable def rootQuadratic (a b : ℝ) : ℝ[X] :=
  (X - C a) * (X - C b)

/-- A monic quadratic specified by its linear and constant coefficients. -/
noncomputable def coefficientQuadratic (B C₀ : ℝ) : ℝ[X] :=
  X ^ 2 + C B * X + C C₀

theorem rootQuadratic_eq_coefficientQuadratic (a b : ℝ) :
    rootQuadratic a b = coefficientQuadratic (-(a + b)) (a * b) := by
  simp [rootQuadratic, coefficientQuadratic]
  ring

/-- Discriminant of a convex combination of two root-specified monic
quadratics. -/
theorem convex_rootQuadratic_discrim
    (a b c d t : ℝ) :
    discrim 1
        (-(t * (a + b) + (1 - t) * (c + d)))
        (t * (a * b) + (1 - t) * (c * d)) =
      t * (b - a) ^ 2 + (1 - t) * (d - c) ^ 2 -
        t * (1 - t) * (c + d - a - b) ^ 2 := by
  rw [discrim]
  ring

/-- If `[a,b]` lies strictly to the left of `[c,d]`, an explicit convex
parameter gives negative discriminant. -/
theorem exists_convex_discrim_neg_of_separated
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hbc : b < c) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      discrim 1
        (-(t * (a + b) + (1 - t) * (c + d)))
        (t * (a * b) + (1 - t) * (c * d)) < 0 := by
  let R := b - a
  let S := d - c
  let g := c - b
  let D := R + S + 2 * g
  let t := (S + g) / D
  have hR : 0 ≤ R := sub_nonneg.mpr hab
  have hS : 0 ≤ S := sub_nonneg.mpr hcd
  have hg : 0 < g := sub_pos.mpr hbc
  have hD : 0 < D := by dsimp [D]; positivity
  have hnum : 0 < S + g := by positivity
  have hrest : 0 < R + g := by positivity
  have ht : 0 < t := div_pos hnum hD
  have ht1 : t < 1 := by
    rw [div_lt_one hD]
    dsimp [D]
    linarith
  refine ⟨t, ht, ht1, ?_⟩
  rw [convex_rootQuadratic_discrim]
  have hDformula : c + d - a - b = D := by
    dsimp [D, R, S, g]
    ring
  have hRformula : b - a = R := rfl
  have hSformula : d - c = S := rfl
  rw [hDformula, hRformula, hSformula]
  have hone : 1 - t = (R + g) / D := by
    dsimp [t]
    field_simp [ne_of_gt hD]
    dsimp [D]
    ring
  rw [hone]
  have hfactor :
      t * R ^ 2 + ((R + g) / D) * S ^ 2 -
          t * ((R + g) / D) * D ^ 2 =
        -g * (4 * R * S + 3 * R * g + 3 * S * g + 2 * g ^ 2) / D := by
    dsimp [t]
    field_simp [ne_of_gt hD]
    ring
  rw [hfactor]
  have hinner : 0 < 4 * R * S + 3 * R * g + 3 * S * g + 2 * g ^ 2 := by
    positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hg) hinner) hD

/-- A monic quadratic with negative discriminant cannot split over `ℝ`. -/
theorem not_realRooted_coefficientQuadratic_of_discrim_neg
    {B C₀ : ℝ} (hdisc : discrim 1 B C₀ < 0) :
    ¬ RealRooted (coefficientQuadratic B C₀) := by
  intro hsplits
  have hdegree : 0 < (coefficientQuadratic B C₀).natDegree := by
    have hcoeff : (coefficientQuadratic B C₀).coeff 2 ≠ 0 := by
      simp [coefficientQuadratic]
    exact lt_of_lt_of_le (by norm_num) (le_natDegree_of_ne_zero hcoeff)
  obtain ⟨x, hx⟩ := RealRooted.exists_largestRoot hsplits hdegree
  have heval : 1 * (x * x) + B * x + C₀ = 0 := by
    have := hx.isRoot
    simpa [IsRoot, coefficientQuadratic, eval_add, eval_mul, eval_pow,
      pow_two] using this
  have hsq := discrim_eq_sq_of_quadratic_eq_zero heval
  nlinarith [sq_nonneg (2 * 1 * x + B)]

/-- The convex combination of two root quadratics in coefficient form. -/
theorem convex_rootQuadratic_eq_coefficientQuadratic
    (a b c d t : ℝ) :
    t • rootQuadratic a b + (1 - t) • rootQuadratic c d =
      coefficientQuadratic
        (-(t * (a + b) + (1 - t) * (c + d)))
        (t * (a * b) + (1 - t) * (c * d)) := by
  rw [rootQuadratic_eq_coefficientQuadratic,
    rootQuadratic_eq_coefficientQuadratic]
  simp [coefficientQuadratic, smul_add, smul_eq_C_mul]
  ring

/-! ## Removing and restoring a common linear factor -/

/-- Dividing a monic polynomial by one of its linear root factors preserves
monicity. -/
theorem monic_divByMonic_X_sub_C_of_isRoot
    {p : ℝ[X]} {a : ℝ} (hmonic : p.Monic) (hroot : p.IsRoot a) :
    (p /ₘ (X - C a)).Monic := by
  have hmul : (X - C a) * (p /ₘ (X - C a)) = p :=
    mul_divByMonic_eq_iff_isRoot.mpr hroot
  apply (monic_X_sub_C a).of_mul_monic_left
  simpa [hmul] using hmonic

/-- Removing one real root from a real-rooted polynomial leaves a
real-rooted quotient. -/
theorem realRooted_divByMonic_X_sub_C_of_isRoot
    {p : ℝ[X]} {a : ℝ} (hsplits : RealRooted p)
    (hmonic : p.Monic) (hroot : p.IsRoot a) :
    RealRooted (p /ₘ (X - C a)) := by
  let p' := p /ₘ (X - C a)
  have hp'monic : p'.Monic := by
    exact monic_divByMonic_X_sub_C_of_isRoot hmonic hroot
  have hmul : (X - C a) * p' = p := by
    simpa [p'] using (mul_divByMonic_eq_iff_isRoot.mpr hroot)
  have hprod : ((X - C a) * p').Splits := by simpa [hmul] using hsplits
  exact (splits_mul_iff (X_sub_C_ne_zero a) hp'monic.ne_zero).mp hprod |>.2

/-- Removing a linear factor lowers the natural degree by exactly one. -/
theorem natDegree_divByMonic_X_sub_C
    (p : ℝ[X]) (a : ℝ) :
    (p /ₘ (X - C a)).natDegree = p.natDegree - 1 := by
  rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C]

/-- Division by a common linear root factor commutes with taking a convex
combination. -/
theorem convex_divByMonic_X_sub_C
    {p q : ℝ[X]} {a t : ℝ}
    (hproot : p.IsRoot a) (hqroot : q.IsRoot a) :
    (t • p + (1 - t) • q) /ₘ (X - C a) =
      t • (p /ₘ (X - C a)) + (1 - t) • (q /ₘ (X - C a)) := by
  have hpmul : (X - C a) * (p /ₘ (X - C a)) = p :=
    mul_divByMonic_eq_iff_isRoot.mpr hproot
  have hqmul : (X - C a) * (q /ₘ (X - C a)) = q :=
    mul_divByMonic_eq_iff_isRoot.mpr hqroot
  have hfactor :
      (X - C a) *
          (t • (p /ₘ (X - C a)) + (1 - t) • (q /ₘ (X - C a))) =
        t • p + (1 - t) • q := by
    rw [mul_add, mul_smul_comm, mul_smul_comm, hpmul, hqmul]
  rw [← hfactor, mul_divByMonic_cancel_left _ (monic_X_sub_C a)]

/-- Sorting the roots after adjoining one linear factor is ordered
insertion into the old sorted root list. -/
theorem sortedRoots_X_sub_C_mul
    (p : ℝ[X]) (a : ℝ) (hp0 : p ≠ 0) :
    ((X - C a) * p).roots.sort (· ≤ ·) =
      (p.roots.sort (· ≤ ·)).orderedInsert (· ≤ ·) a := by
  classical
  have hroots : ((X - C a) * p).roots = {a} + p.roots := by
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero a) hp0), roots_X_sub_C]
  have hrightSorted :
      ((p.roots.sort (· ≤ ·)).orderedInsert (· ≤ ·) a).Pairwise (· ≤ ·) :=
    (Multiset.pairwise_sort (s := p.roots) (r := (· ≤ ·))).orderedInsert a _
  have hperm :
      List.Perm (((X - C a) * p).roots.sort (· ≤ ·))
        ((p.roots.sort (· ≤ ·)).orderedInsert (· ≤ ·) a) := by
    apply Multiset.coe_eq_coe.mp
    calc
      (↑(((X - C a) * p).roots.sort (· ≤ ·)) : Multiset ℝ) =
          ((X - C a) * p).roots := by rw [Multiset.sort_eq]
      _ = {a} + p.roots := hroots
      _ = (↑(a :: p.roots.sort (· ≤ ·)) : Multiset ℝ) := by
        change a ::ₘ p.roots = a ::ₘ ↑(p.roots.sort (· ≤ ·))
        rw [Multiset.sort_eq]
      _ = ↑((p.roots.sort (· ≤ ·)).orderedInsert (· ≤ ·) a) := by
        exact (Multiset.coe_eq_coe.mpr
          (List.perm_orderedInsert (· ≤ ·) a (p.roots.sort (· ≤ ·)))).symm
  exact List.Perm.eq_of_pairwise
    (fun x y _ _ hxy hyx ↦ le_antisymm hxy hyx)
    (Multiset.pairwise_sort (s := ((X - C a) * p).roots) (r := (· ≤ ·)))
    hrightSorted hperm

/-- Multiplying both members of an interlacing pair by the same real linear
factor preserves interlacing. -/
theorem polynomialInterlaces_X_sub_C_mul
    {r p : ℝ[X]} (h : PolynomialInterlaces r p) (a : ℝ) :
    PolynomialInterlaces ((X - C a) * r) ((X - C a) * p) := by
  rcases h with ⟨hr0, hp0, hrmonic, hpmonic, hrsplits, hpsplits, hlists⟩
  refine ⟨mul_ne_zero (X_sub_C_ne_zero a) hr0,
    mul_ne_zero (X_sub_C_ne_zero a) hp0,
    (monic_X_sub_C a).mul hrmonic, (monic_X_sub_C a).mul hpmonic,
    (Splits.X_sub_C a).mul hrsplits, (Splits.X_sub_C a).mul hpsplits, ?_⟩
  rw [sortedRoots_X_sub_C_mul r a hr0, sortedRoots_X_sub_C_mul p a hp0]
  exact hlists.orderedInsert_same
    (Multiset.pairwise_sort (s := r.roots) (r := (· ≤ ·)))
    (Multiset.pairwise_sort (s := p.roots) (r := (· ≤ ·))) a

/-- A convex combination of two monic polynomials of the same natural
degree is again monic of that degree. -/
theorem monic_convex_combination_of_same_natDegree
    {p q : ℝ[X]} {d : ℕ} (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d) (t : ℝ) :
    (t • p + (1 - t) • q).Monic := by
  have hpc : p.coeff d = 1 := by
    rw [← hpdegree]
    exact hpmonic.coeff_natDegree
  have hqc : q.coeff d = 1 := by
    rw [← hqdegree]
    exact hqmonic.coeff_natDegree
  have hisMonicOfDegree : IsMonicOfDegree (t • p + (1 - t) • q) d := by
    apply (isMonicOfDegree_iff (t • p + (1 - t) • q) d).mpr
    constructor
    · exact (natDegree_add_le _ _).trans
        (max_le ((natDegree_smul_le t p).trans (hpdegree.le))
          ((natDegree_smul_le (1 - t) q).trans (hqdegree.le)))
    · simp [coeff_add, coeff_smul, hpc, hqc]
  exact hisMonicOfDegree.monic

/-- If every convex combination of two same-degree monic polynomials is
real-rooted and they share `a`, the corresponding convex combinations of
their quotients by `X - C a` are real-rooted as well. -/
theorem convex_quotients_realRooted_of_common_root
    {p q : ℝ[X]} {a : ℝ} {d : ℕ}
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    (hproot : p.IsRoot a) (hqroot : q.IsRoot a)
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q)) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted
        (t • (p /ₘ (X - C a)) + (1 - t) • (q /ₘ (X - C a))) := by
  intro t ht0 ht1
  rw [← convex_divByMonic_X_sub_C hproot hqroot]
  apply realRooted_divByMonic_X_sub_C_of_isRoot
    (hall t ht0 ht1)
    (monic_convex_combination_of_same_natDegree
      hpmonic hqmonic hpdegree hqdegree t)
  rw [IsRoot] at hproot hqroot ⊢
  simp only [eval_add, eval_smul]
  rw [hproot, hqroot]
  simp

/-- The analytic two-polynomial Fell converse at a fixed positive degree. -/
def PairFellConverseAtDegree (d : ℕ) : Prop :=
  ∀ (p q : ℝ[X]),
    p.Monic → q.Monic → RealRooted p → RealRooted q →
    p.natDegree = d → q.natDegree = d →
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q)) →
    HasCommonInterlacer ({false, true} : Finset Bool)
      (fun e ↦ if e then p else q)

/-- The remaining analytic core at degree `d`: the Pair Fell converse only
for pairs with no common real root.  Since both polynomials are real-rooted,
this is precisely the root-coprime case. -/
def RootDisjointPairFellConverseAtDegree (d : ℕ) : Prop :=
  ∀ (p q : ℝ[X]),
    p.Monic → q.Monic → RealRooted p → RealRooted q →
    p.natDegree = d → q.natDegree = d →
    (∀ a : ℝ, ¬ (p.IsRoot a ∧ q.IsRoot a)) →
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q)) →
    HasCommonInterlacer ({false, true} : Finset Bool)
      (fun e ↦ if e then p else q)

/-! ## Algebraic and sign lemmas for the root-disjoint core -/

/-- A root shared by two distinct affine combinations is necessarily a
common root of both endpoints. -/
theorem endpoints_isRoot_of_two_convex_isRoot
    {p q : ℝ[X]} {s t x : ℝ} (hst : s ≠ t)
    (hs : (s • p + (1 - s) • q).IsRoot x)
    (ht : (t • p + (1 - t) • q).IsRoot x) :
    p.IsRoot x ∧ q.IsRoot x := by
  rw [IsRoot] at hs ht ⊢
  simp only [eval_add, eval_smul, smul_eq_mul] at hs ht
  let P := p.eval x
  let Q := q.eval x
  have hdiff : (s - t) * (P - Q) = 0 := by
    calc
      (s - t) * (P - Q) =
          (s * P + (1 - s) * Q) - (t * P + (1 - t) * Q) := by ring
      _ = 0 := by simp [P, Q, hs, ht]
  have hPQ : P = Q := by
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hst))
  have hP : P = 0 := by
    have hs' : s * P + (1 - s) * Q = 0 := by simpa [P, Q] using hs
    rw [hPQ] at hs'
    linarith
  exact ⟨by simpa [P] using hP, by simpa [P, Q, hPQ] using hP⟩

/-- Hence a root-disjoint pair has root-disjoint convex combinations at
any two distinct parameters. -/
theorem convex_combinations_root_disjoint
    {p q : ℝ[X]}
    (hdisjoint : ∀ a : ℝ, ¬ (p.IsRoot a ∧ q.IsRoot a))
    {s t : ℝ} (hst : s ≠ t) :
    ∀ x : ℝ,
      ¬ ((s • p + (1 - s) • q).IsRoot x ∧
        (t • p + (1 - t) • q).IsRoot x) := by
  intro x hx
  exact hdisjoint x
    (endpoints_isRoot_of_two_convex_isRoot hst hx.1 hx.2)

/-- If a monic real-rooted polynomial has no root in `[a,b]`, then its
endpoint evaluations have strictly positive product. -/
theorem eval_mul_eval_pos_of_no_root_Icc
    {p : ℝ[X]} (hmonic : p.Monic) (hsplits : RealRooted p)
    {a b : ℝ} (hab : a < b)
    (hno : ∀ r : ℝ, p.IsRoot r → r < a ∨ b < r) :
    0 < p.eval a * p.eval b := by
  rw [hsplits.eval_eq_prod_roots_of_monic hmonic,
    hsplits.eval_eq_prod_roots_of_monic hmonic,
    ← Multiset.prod_map_mul]
  apply Multiset.prod_pos
  intro y hy
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
  have hrroot : p.IsRoot r := (mem_roots hmonic.ne_zero).mp hr
  rcases hno r hrroot with hra | hrb
  · exact mul_pos (sub_pos.mpr hra) (sub_pos.mpr (hra.trans hab))
  · exact mul_pos_of_neg_of_neg
      (sub_neg.mpr (hab.trans hrb)) (sub_neg.mpr hrb)

/-- The preceding sign statement in interval language. -/
theorem eval_mul_eval_pos_of_no_root_mem_Icc
    {p : ℝ[X]} (hmonic : p.Monic) (hsplits : RealRooted p)
    {a b : ℝ} (hab : a < b)
    (hno : ∀ r : ℝ, p.IsRoot r → r ∉ Set.Icc a b) :
    0 < p.eval a * p.eval b := by
  apply eval_mul_eval_pos_of_no_root_Icc hmonic hsplits hab
  intro r hr
  have hout := hno r hr
  rw [Set.mem_Icc, not_and_or] at hout
  exact hout.imp lt_of_not_ge lt_of_not_ge

/-- A product of linear factors has sign `(-1)` to the number of factors
strictly to the right of the evaluation point. -/
theorem signed_prod_sub_pos_by_gt_count
    (s : Multiset ℝ) {x : ℝ} (hne : ∀ r ∈ s, r ≠ x) :
    0 < (-1 : ℝ) ^ (s.filter fun r ↦ x < r).card *
      (s.map fun r ↦ x - r).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
      have hrne : r ≠ x := hne r (by simp)
      have hsne : ∀ z ∈ s, z ≠ x := by
        intro z hz
        exact hne z (by simp [hz])
      have hpos := ih hsne
      by_cases hxr : x < r
      · calc
          0 < (r - x) *
              ((-1 : ℝ) ^ (s.filter fun z ↦ x < z).card *
                (s.map fun z ↦ x - z).prod) :=
            mul_pos (sub_pos.mpr hxr) hpos
          _ = (-1 : ℝ) ^ (((r ::ₘ s).filter fun z ↦ x < z).card) *
              (((r ::ₘ s).map fun z ↦ x - z).prod) := by
            simp [hxr, pow_succ]
            ring
      · have hrx : r < x := lt_of_le_of_ne (le_of_not_gt hxr) hrne
        calc
          0 < (x - r) *
              ((-1 : ℝ) ^ (s.filter fun z ↦ x < z).card *
                (s.map fun z ↦ x - z).prod) :=
            mul_pos (sub_pos.mpr hrx) hpos
          _ = (-1 : ℝ) ^ (((r ::ₘ s).filter fun z ↦ x < z).card) *
              (((r ::ₘ s).map fun z ↦ x - z).prod) := by
            simp [hxr]
            ring

/-- Exact sign of a monic real-rooted polynomial away from its roots. -/
theorem signed_eval_pos_by_roots_gt_count
    {p : ℝ[X]} (hmonic : p.Monic) (hsplits : RealRooted p)
    {x : ℝ} (hx : ¬ p.IsRoot x) :
    0 < (-1 : ℝ) ^ (p.roots.filter fun r ↦ x < r).card * p.eval x := by
  rw [hsplits.eval_eq_prod_roots_of_monic hmonic]
  apply signed_prod_sub_pos_by_gt_count
  intro r hr hre
  apply hx
  rw [← hre]
  exact (mem_roots hmonic.ne_zero).mp hr

/-- At a root of `p`, the sign of `q` is the root-count sign of every
nontrivial convex combination. -/
theorem signed_q_eval_at_p_root_by_convex_roots
    {p q : ℝ[X]} {d : ℕ}
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    (hdisjoint : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q))
    {a t : ℝ} (hpa : p.IsRoot a) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < (-1 : ℝ) ^
        ((t • p + (1 - t) • q).roots.filter fun r ↦ a < r).card *
      q.eval a := by
  let f := t • p + (1 - t) • q
  have hfa : ¬ f.IsRoot a := by
    intro hroot
    apply hdisjoint a
    refine ⟨hpa, ?_⟩
    rw [IsRoot] at hpa hroot ⊢
    dsimp [f] at hroot
    simp only [eval_add, eval_smul, smul_eq_mul, hpa, mul_zero, zero_add] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left (sub_ne_zero.mpr ht1.ne')
  have hsign := signed_eval_pos_by_roots_gt_count
    (monic_convex_combination_of_same_natDegree
      hpmonic hqmonic hpdegree hqdegree t)
    (hall t ht0 ht1.le) hfa
  have heval : f.eval a = (1 - t) * q.eval a := by
    rw [IsRoot] at hpa
    simp [f, hpa]
  rw [heval] at hsign
  have hreorder :
      0 < (1 - t) *
        ((-1 : ℝ) ^ (f.roots.filter fun r ↦ a < r).card * q.eval a) := by
    nlinarith
  have hdesired := pos_of_mul_pos_right hreorder (sub_nonneg.mpr ht1.le)
  simpa [f] using hdesired

/-- Symmetrically, at a root of `q`, the sign of `p` is read from every
convex combination with positive `p`-weight. -/
theorem signed_p_eval_at_q_root_by_convex_roots
    {p q : ℝ[X]} {d : ℕ}
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    (hdisjoint : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q))
    {a t : ℝ} (hqa : q.IsRoot a) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 < (-1 : ℝ) ^
        ((t • p + (1 - t) • q).roots.filter fun r ↦ a < r).card *
      p.eval a := by
  let f := t • p + (1 - t) • q
  have hfa : ¬ f.IsRoot a := by
    intro hroot
    apply hdisjoint a
    refine ⟨?_, hqa⟩
    rw [IsRoot] at hqa hroot ⊢
    dsimp [f] at hroot
    simp only [eval_add, eval_smul, smul_eq_mul, hqa, mul_zero, add_zero] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left ht0.ne'
  have hsign := signed_eval_pos_by_roots_gt_count
    (monic_convex_combination_of_same_natDegree
      hpmonic hqmonic hpdegree hqdegree t)
    (hall t ht0.le ht1) hfa
  have heval : f.eval a = t * p.eval a := by
    rw [IsRoot] at hqa
    simp [f, hqa]
  rw [heval] at hsign
  have hreorder :
      0 < t *
        ((-1 : ℝ) ^ (f.roots.filter fun r ↦ a < r).card * p.eval a) := by
    nlinarith
  have hdesired := pos_of_mul_pos_right hreorder ht0.le
  simpa [f] using hdesired

/-- Two powers of `-1` multiplying the same nonzero real number positively
must have the same parity. -/
theorem even_iff_of_neg_one_pow_mul_pos
    {m n : ℕ} {x : ℝ}
    (hm : 0 < (-1 : ℝ) ^ m * x)
    (hn : 0 < (-1 : ℝ) ^ n * x) :
    Even m ↔ Even n := by
  have hpows : (-1 : ℝ) ^ m = (-1 : ℝ) ^ n := by
    rcases neg_one_pow_eq_or ℝ m with hm1 | hm1 <;>
      rcases neg_one_pow_eq_or ℝ n with hn1 | hn1
    · rw [hm1, hn1]
    · exfalso
      rw [hm1] at hm
      rw [hn1] at hn
      norm_num at hm hn
      linarith
    · exfalso
      rw [hm1] at hm
      rw [hn1] at hn
      norm_num at hm hn
      linarith
    · rw [hm1, hn1]
  constructor
  · intro hmeven
    apply (neg_one_pow_eq_one_iff_even (R := ℝ) (by norm_num)).mp
    rw [← hpows, hmeven.neg_one_pow]
  · intro hneven
    apply (neg_one_pow_eq_one_iff_even (R := ℝ) (by norm_num)).mp
    rw [hpows, hneven.neg_one_pow]

/-- Along the open part of the pencil ending at `p`, the parity of the
number of roots to the right of any fixed root of `p` is constant. -/
theorem even_roots_gt_p_root_iff
    {p q : ℝ[X]} {d : ℕ}
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    (hdisjoint : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q))
    {a s t : ℝ} (hpa : p.IsRoot a)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Even (((s • p + (1 - s) • q).roots.filter fun r ↦ a < r).card) ↔
      Even (((t • p + (1 - t) • q).roots.filter fun r ↦ a < r).card) := by
  exact even_iff_of_neg_one_pow_mul_pos
    (signed_q_eval_at_p_root_by_convex_roots hpmonic hqmonic
      hpdegree hqdegree hdisjoint hall hpa hs0 hs1)
    (signed_q_eval_at_p_root_by_convex_roots hpmonic hqmonic
      hpdegree hqdegree hdisjoint hall hpa ht0 ht1)

/-- The analogous root-count parity conservation along the open part of
the pencil starting at `q`. -/
theorem even_roots_gt_q_root_iff
    {p q : ℝ[X]} {d : ℕ}
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    (hdisjoint : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q))
    {a s t : ℝ} (hqa : q.IsRoot a)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    Even (((s • p + (1 - s) • q).roots.filter fun r ↦ a < r).card) ↔
      Even (((t • p + (1 - t) • q).roots.filter fun r ↦ a < r).card) := by
  exact even_iff_of_neg_one_pow_mul_pos
    (signed_p_eval_at_q_root_by_convex_roots hpmonic hqmonic
      hpdegree hqdegree hdisjoint hall hqa hs0 hs1)
    (signed_p_eval_at_q_root_by_convex_roots hpmonic hqmonic
      hpdegree hqdegree hdisjoint hall hqa ht0 ht1)

/-! ## Derivative induction data -/

/-- The derivative normalized to retain leading coefficient one. -/
noncomputable def normalizedDerivative (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (d : ℝ)⁻¹ • p.derivative

/-- The normalized derivative of a degree-`d` monic polynomial is monic of
degree `d - 1`. -/
theorem normalizedDerivative_isMonicOfDegree
    {p : ℝ[X]} {d : ℕ} (hd : 0 < d)
    (hmonic : p.Monic) (hdegree : p.natDegree = d) :
    IsMonicOfDegree (normalizedDerivative d p) (d - 1) := by
  apply (isMonicOfDegree_iff (normalizedDerivative d p) (d - 1)).mpr
  constructor
  · exact (natDegree_smul_le (d : ℝ)⁻¹ p.derivative).trans
      ((natDegree_derivative_le p).trans_eq (congrArg (· - 1) hdegree))
  · have hdcast : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have htop : p.coeff d = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    simp only [normalizedDerivative, coeff_smul, coeff_derivative]
    rw [show d - 1 + 1 = d by omega, htop]
    have hcast : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ d))
    rw [hcast]
    simp [hdcast]

/-- Rolle's theorem, including multiplicities, implies that the derivative
of a nonconstant real-rooted polynomial is real-rooted. -/
theorem realRooted_derivative
    {p : ℝ[X]} (hsplits : RealRooted p) (hdegree : 0 < p.natDegree) :
    RealRooted p.derivative := by
  have hrootCount := p.card_roots_le_derivative
  have hpCard : p.roots.card = p.natDegree :=
    hsplits.natDegree_eq_card_roots.symm
  have hlower : p.natDegree - 1 ≤ p.derivative.roots.card := by
    rw [hpCard] at hrootCount
    omega
  have hupper : p.derivative.roots.card ≤ p.derivative.natDegree :=
    Polynomial.card_roots' p.derivative
  have hdegreeUpper : p.derivative.natDegree ≤ p.natDegree - 1 :=
    natDegree_derivative_le p
  change p.derivative.Splits
  apply splits_iff_card_roots.mpr
  exact le_antisymm hupper (hdegreeUpper.trans hlower)

/-- Consequently the normalized derivative is real-rooted. -/
theorem realRooted_normalizedDerivative
    {p : ℝ[X]} {d : ℕ} (hd : 0 < d)
    (hsplits : RealRooted p) (hdegree : p.natDegree = d) :
    RealRooted (normalizedDerivative d p) := by
  have hpdeg : 0 < p.natDegree := by omega
  have hderiv := realRooted_derivative hsplits hpdeg
  simpa [normalizedDerivative, smul_eq_C_mul] using
    hderiv.C_mul ((d : ℝ)⁻¹)

/-- Normalized differentiation commutes with the affine combination used
in Pair Fell. -/
theorem normalizedDerivative_convex
    (d : ℕ) (p q : ℝ[X]) (t : ℝ) :
    normalizedDerivative d (t • p + (1 - t) • q) =
      t • normalizedDerivative d p +
        (1 - t) • normalizedDerivative d q := by
  simp [normalizedDerivative, derivative_add]
  module

/-- The Pair Fell hypotheses descend to the normalized derivatives. -/
theorem normalizedDerivatives_haveCommonInterlacer
    {d : ℕ} (hd : 2 ≤ d)
    (hprev : PairFellConverseAtDegree (d - 1))
    (p q : ℝ[X])
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpsplits : RealRooted p) (hqsplits : RealRooted q)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q)) :
    HasCommonInterlacer ({false, true} : Finset Bool)
      (fun e ↦ if e then normalizedDerivative d p else
        normalizedDerivative d q) := by
  have hdp : 0 < d := by omega
  apply hprev (normalizedDerivative d p) (normalizedDerivative d q)
  · exact (normalizedDerivative_isMonicOfDegree hdp hpmonic hpdegree).monic
  · exact (normalizedDerivative_isMonicOfDegree hdp hqmonic hqdegree).monic
  · exact realRooted_normalizedDerivative hdp hpsplits hpdegree
  · exact realRooted_normalizedDerivative hdp hqsplits hqdegree
  · exact (normalizedDerivative_isMonicOfDegree hdp hpmonic hpdegree).natDegree_eq
  · exact (normalizedDerivative_isMonicOfDegree hdp hqmonic hqdegree).natDegree_eq
  · intro t ht0 ht1
    rw [← normalizedDerivative_convex]
    apply realRooted_normalizedDerivative hdp
      (hall t ht0 ht1)
    have hpc : p.coeff d = 1 := by
      rw [← hpdegree]
      exact hpmonic.coeff_natDegree
    have hqc : q.coeff d = 1 := by
      rw [← hqdegree]
      exact hqmonic.coeff_natDegree
    apply le_antisymm
    · exact (natDegree_add_le _ _).trans
        (max_le ((natDegree_smul_le t p).trans hpdegree.le)
          ((natDegree_smul_le (1 - t) q).trans hqdegree.le))
    · apply le_natDegree_of_ne_zero
      simp [coeff_add, coeff_smul, hpc, hqc]

/-- The common-root induction step for the analytic Pair Fell converse.
Once degree `d - 1` is known, a common real root closes degree `d`: remove
the common factor, apply the lower-degree theorem, and restore it on the
common interlacer and both polynomials. -/
theorem pair_fell_of_common_root
    {d : ℕ} (_hd : 2 ≤ d)
    (hprev : PairFellConverseAtDegree (d - 1))
    (p q : ℝ[X])
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpsplits : RealRooted p) (hqsplits : RealRooted q)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    {a : ℝ} (hproot : p.IsRoot a) (hqroot : q.IsRoot a)
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q)) :
    HasCommonInterlacer ({false, true} : Finset Bool)
      (fun e ↦ if e then p else q) := by
  let p' := p /ₘ (X - C a)
  let q' := q /ₘ (X - C a)
  have hp'monic : p'.Monic := by
    exact monic_divByMonic_X_sub_C_of_isRoot hpmonic hproot
  have hq'monic : q'.Monic := by
    exact monic_divByMonic_X_sub_C_of_isRoot hqmonic hqroot
  have hp'splits : RealRooted p' := by
    exact realRooted_divByMonic_X_sub_C_of_isRoot hpsplits hpmonic hproot
  have hq'splits : RealRooted q' := by
    exact realRooted_divByMonic_X_sub_C_of_isRoot hqsplits hqmonic hqroot
  have hp'degree : p'.natDegree = d - 1 := by
    dsimp [p']
    rw [natDegree_divByMonic_X_sub_C, hpdegree]
  have hq'degree : q'.natDegree = d - 1 := by
    dsimp [q']
    rw [natDegree_divByMonic_X_sub_C, hqdegree]
  have hquotientConvex : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p' + (1 - t) • q') := by
    simpa [p', q'] using convex_quotients_realRooted_of_common_root
      hpmonic hqmonic hpdegree hqdegree hproot hqroot hall
  obtain ⟨r, hr⟩ := hprev p' q' hp'monic hq'monic hp'splits hq'splits
    hp'degree hq'degree hquotientConvex
  have hpmul : (X - C a) * p' = p := by
    simpa [p'] using (mul_divByMonic_eq_iff_isRoot.mpr hproot)
  have hqmul : (X - C a) * q' = q := by
    simpa [q'] using (mul_divByMonic_eq_iff_isRoot.mpr hqroot)
  refine ⟨(X - C a) * r, ?_⟩
  intro e he
  cases e
  · have hinterlace := polynomialInterlaces_X_sub_C_mul (hr false (by simp)) a
    simp only [Bool.false_eq_true, ↓reduceIte] at hinterlace ⊢
    rw [hqmul] at hinterlace
    exact hinterlace
  · have hinterlace := polynomialInterlaces_X_sub_C_mul (hr true (by simp)) a
    simp only [↓reduceIte] at hinterlace ⊢
    rw [hpmul] at hinterlace
    exact hinterlace

/-- At degree at least two, the full analytic Pair Fell converse follows
from the preceding degree and the root-disjoint core at the current degree. -/
theorem pairFellConverseAtDegree_of_rootDisjoint
    {d : ℕ} (hd : 2 ≤ d)
    (hprev : PairFellConverseAtDegree (d - 1))
    (hcore : RootDisjointPairFellConverseAtDegree d) :
    PairFellConverseAtDegree d := by
  intro p q hpmonic hqmonic hpsplits hqsplits hpdegree hqdegree hall
  by_cases hcommon : ∃ a : ℝ, p.IsRoot a ∧ q.IsRoot a
  · obtain ⟨a, hproot, hqroot⟩ := hcommon
    exact pair_fell_of_common_root hd hprev p q hpmonic hqmonic
      hpsplits hqsplits hpdegree hqdegree hproot hqroot hall
  · apply hcore p q hpmonic hqmonic hpsplits hqsplits hpdegree hqdegree
    · intro a ha
      exact hcommon ⟨a, ha⟩
    · exact hall

/-! ## Root intervals of monic real-rooted quadratics -/

/-- A monic real-rooted quadratic is its product over two ordered real
roots.  We retain the sorted-root-list equation because it is the convenient
interface for `PolynomialInterlaces`. -/
theorem exists_ordered_roots_eq_rootQuadratic
    (p : ℝ[X]) (hmonic : p.Monic) (hsplits : RealRooted p)
    (hdegree : p.natDegree = 2) :
    ∃ a b : ℝ, a ≤ b ∧
      p.roots.sort (· ≤ ·) = [a, b] ∧ p = rootQuadratic a b := by
  have hlength : (p.roots.sort (· ≤ ·)).length = 2 := by
    calc
      (p.roots.sort (· ≤ ·)).length = p.roots.card := by simp
      _ = p.natDegree := hsplits.natDegree_eq_card_roots.symm
      _ = 2 := hdegree
  obtain ⟨a, b, hroots⟩ := List.length_eq_two.mp hlength
  have hab : a ≤ b := by
    have hsorted :=
      Multiset.pairwise_sort (s := p.roots) (r := (· ≤ ·))
    rw [hroots] at hsorted
    simpa using hsorted
  refine ⟨a, b, hab, hroots, ?_⟩
  have hrootsMultiset : p.roots = ({a, b} : Multiset ℝ) := by
    rw [← Multiset.sort_eq (s := p.roots) (r := (· ≤ ·)), hroots]
    rfl
  rw [hsplits.eq_prod_roots_of_monic hmonic, hrootsMultiset]
  simp [rootQuadratic]

/-- A point in the closed interval between the two sorted roots defines a
linear interlacer. -/
theorem linear_interlaces_of_sortedRoots_eq_pair
    (p : ℝ[X]) (hmonic : p.Monic) (hsplits : RealRooted p)
    {a b x : ℝ} (hroots : p.roots.sort (· ≤ ·) = [a, b])
    (hax : a ≤ x) (hxb : x ≤ b) :
    PolynomialInterlaces (X - C x) p := by
  have hlinearRoots : (X - C x : ℝ[X]).roots.sort (· ≤ ·) = [x] := by
    simp
  refine ⟨(X_sub_C_ne_zero x), hmonic.ne_zero, monic_X_sub_C x,
    hmonic, Splits.X_sub_C x, hsplits, ?_⟩
  rw [hlinearRoots, hroots]
  refine ⟨by simp, ?_⟩
  intro k hk
  have hkzero : k = 0 := by simpa using hk
  subst k
  simpa using And.intro hax hxb

/-! ## The degree-two analytic Fell converse -/

/-- For two monic real-rooted quadratics, real-rootedness of every convex
combination forces a common linear interlacer. -/
theorem pair_fell_natDegree_two
    (p q : ℝ[X])
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpsplits : RealRooted p) (hqsplits : RealRooted q)
    (hpdegree : p.natDegree = 2) (hqdegree : q.natDegree = 2)
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q)) :
    HasCommonInterlacer ({false, true} : Finset Bool)
      (fun e ↦ if e then p else q) := by
  obtain ⟨a, b, hab, hproots, hpeq⟩ :=
    exists_ordered_roots_eq_rootQuadratic p hpmonic hpsplits hpdegree
  obtain ⟨c, d, hcd, hqroots, hqeq⟩ :=
    exists_ordered_roots_eq_rootQuadratic q hqmonic hqsplits hqdegree
  have hcb : c ≤ b := by
    by_contra hnot
    have hbc : b < c := lt_of_not_ge hnot
    obtain ⟨t, ht0, ht1, hdisc⟩ :=
      exists_convex_discrim_neg_of_separated hab hcd hbc
    have hreal := hall t ht0.le ht1.le
    rw [hpeq, hqeq, convex_rootQuadratic_eq_coefficientQuadratic] at hreal
    exact (not_realRooted_coefficientQuadratic_of_discrim_neg hdisc) hreal
  have had : a ≤ d := by
    by_contra hnot
    have hda : d < a := lt_of_not_ge hnot
    obtain ⟨t, ht0, ht1, hdisc⟩ :=
      exists_convex_discrim_neg_of_separated hcd hab hda
    have hreal := hall (1 - t) (sub_nonneg.mpr ht1.le) (by linarith)
    have hreal' : RealRooted (t • q + (1 - t) • p) := by
      simpa [sub_sub, add_comm] using hreal
    rw [hqeq, hpeq, convex_rootQuadratic_eq_coefficientQuadratic] at hreal'
    exact (not_realRooted_coefficientQuadratic_of_discrim_neg hdisc) hreal'
  let x : ℝ := max a c
  have hpx : PolynomialInterlaces (X - C x) p := by
    apply linear_interlaces_of_sortedRoots_eq_pair p hpmonic hpsplits hproots
    · exact le_max_left _ _
    · exact max_le hab hcb
  have hqx : PolynomialInterlaces (X - C x) q := by
    apply linear_interlaces_of_sortedRoots_eq_pair q hqmonic hqsplits hqroots
    · exact le_max_right _ _
    · exact max_le had hcd
  refine ⟨X - C x, ?_⟩
  intro e he
  cases e
  · simpa using hqx
  · simpa using hpx

/-- The fixed-degree predicate is available in degree one from the constant
interlacer base case. -/
theorem pairFellConverseAtDegree_one : PairFellConverseAtDegree 1 := by
  intro p q hpmonic hqmonic hpsplits hqsplits hpdegree hqdegree hall
  exact CommutatorTheorem.BTInterlacingConverse.pair_fell_natDegree_one
    p q hpmonic hqmonic hpsplits hqsplits hpdegree hqdegree hall

/-- The discriminant argument above establishes the fixed-degree predicate
in degree two. -/
theorem pairFellConverseAtDegree_two : PairFellConverseAtDegree 2 := by
  intro p q hpmonic hqmonic hpsplits hqsplits hpdegree hqdegree hall
  exact pair_fell_natDegree_two p q hpmonic hqmonic hpsplits hqsplits
    hpdegree hqdegree hall

/-- Thus, for every positive degree, it is enough to prove only the
root-disjoint analytic core.  Strong induction automatically removes every
common linear factor, including repeated common factors. -/
theorem pairFellConverseAtDegree_of_rootDisjoint_all
    (hcore : ∀ d : ℕ, 2 ≤ d → RootDisjointPairFellConverseAtDegree d) :
    ∀ d : ℕ, 1 ≤ d → PairFellConverseAtDegree d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro hdpos
      by_cases hd1 : d = 1
      · simpa [hd1] using pairFellConverseAtDegree_one
      · have hd2 : 2 ≤ d := by omega
        apply pairFellConverseAtDegree_of_rootDisjoint hd2
        · exact ih (d - 1) (by omega) (by omega)
        · exact hcore d hd2

/-- Consequently, the degree-three Pair Fell converse is already closed
whenever the two cubics have a common real root. -/
theorem pair_fell_natDegree_three_of_common_root
    (p q : ℝ[X])
    (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpsplits : RealRooted p) (hqsplits : RealRooted q)
    (hpdegree : p.natDegree = 3) (hqdegree : q.natDegree = 3)
    {a : ℝ} (hproot : p.IsRoot a) (hqroot : q.IsRoot a)
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q)) :
    HasCommonInterlacer ({false, true} : Finset Bool)
      (fun e ↦ if e then p else q) := by
  exact pair_fell_of_common_root (d := 3) (by norm_num)
    pairFellConverseAtDegree_two p q hpmonic hqmonic hpsplits hqsplits
    hpdegree hqdegree hproot hqroot hall

/-- Finite Fell converse for monic real-rooted quadratics, obtained by
combining the analytic pair result above with the finite interval-Helly
theorem. -/
theorem finite_fell_natDegree_two
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (p : ι → ℝ[X])
    (hmonic : ∀ i ∈ s, (p i).Monic)
    (hsplits : ∀ i ∈ s, RealRooted (p i))
    (hdegree : ∀ i ∈ s, (p i).natDegree = 2)
    (hall : ∀ i ∈ s, ∀ j ∈ s, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p i + (1 - t) • p j)) :
    HasCommonInterlacer s p := by
  apply CommutatorTheorem.BTInterlacingConverse.finite_fell_of_pair_fell
    s hs p 2 (by norm_num) hmonic hsplits hdegree
  · intro i hi j hj hpq
    obtain ⟨r, hr⟩ := pair_fell_natDegree_two
      (p i) (p j) (hmonic i hi) (hmonic j hj)
      (hsplits i hi) (hsplits j hj) (hdegree i hi) (hdegree j hj) hpq
    refine ⟨r, ?_⟩
    intro k hk
    have hk' : k = i ∨ k = j := by simpa using hk
    rcases hk' with rfl | rfl
    · exact hr true (by simp)
    · exact hr false (by simp)
  · exact hall

end CommutatorTheorem.BTFellPair
