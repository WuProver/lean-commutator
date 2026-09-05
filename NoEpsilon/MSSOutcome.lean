import NoEpsilon.MSSCharpoly

/-!
# An actual finite MSS interlacing outcome

The two-child convex real-rootedness needed by the finite selector is proved by
changing the next independent law to a two-point law. No common-interlacer,
real-rootedness, or good-outcome hypothesis is retained in the final theorem.
-/

namespace NoEpsilon.MSSOutcome

open Polynomial CommutatorTheorem CommutatorTheorem.BTMDPSelection
open NoEpsilon.MSSCharpoly NoEpsilon.MSSInterlacing
open scoped BigOperators Polynomial ComplexOrder

set_option maxHeartbeats 800000

/-- Splitting the first independent coordinate is valid for every module-valued average. -/
theorem sum_smul_independent_succ {R M Ω : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [Fintype Ω]
    (n : ℕ) (p : Fin (n + 1) → Ω → R) (f : (Fin (n + 1) → Ω) → M) :
    (∑ q, (∏ i, p i (q i)) • f q) =
      ∑ ω, p 0 ω • ∑ q : Fin n → Ω,
        (∏ i, p i.succ (q i)) • f (Fin.cons ω q) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Ω)).sum_comp,
    Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.smul_sum, mul_smul]

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

/-- Exact first-coordinate recursion of the real expected characteristic polynomial. -/
theorem realExpectedCharpoly_succ (n : ℕ) (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (v : Fin (n + 1) → Ω → ι → ℂ) (p : Fin (n + 1) → Ω → ℝ) :
    realExpectedCharpoly (n + 1) B hB v p =
      ∑ ω, p 0 ω • realExpectedCharpoly n
        (B + Matrix.vecMulVec (v 0 ω) (star (v 0 ω)))
        (hB.add (Matrix.posSemidef_vecMulVec_self_star _).1)
        (fun i ↦ v i.succ) (fun i ↦ p i.succ) := by
  unfold realExpectedCharpoly
  rw [sum_smul_independent_succ]
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  have hm : B + ∑ i, Matrix.vecMulVec (v i ((Fin.cons ω q : Fin (n + 1) → Ω) i))
      (star (v i ((Fin.cons ω q : Fin (n + 1) → Ω) i))) =
        B + Matrix.vecMulVec (v 0 ω) (star (v 0 ω)) +
          ∑ i, Matrix.vecMulVec (v i.succ (q i)) (star (v i.succ (q i))) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, add_assoc]
  congr 1

/-- A two-point probability law, allowing its two points to coincide. -/
noncomputable def twoPointLaw (a b : Ω) (t : ℝ) (ω : Ω) : ℝ := by
  classical
  exact (if ω = a then t else 0) + (if ω = b then 1 - t else 0)

theorem twoPointLaw_nonneg (a b : Ω) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (ω : Ω) :
    0 ≤ twoPointLaw a b t ω := by
  classical
  unfold twoPointLaw
  split_ifs <;> linarith

theorem sum_twoPointLaw (a b : Ω) (t : ℝ) : ∑ ω, twoPointLaw a b t ω = 1 := by
  classical
  simp [twoPointLaw, Finset.sum_add_distrib]

theorem sum_twoPointLaw_smul {M : Type*} [AddCommGroup M] [Module ℝ M]
    (a b : Ω) (t : ℝ) (f : Ω → M) :
    (∑ ω, twoPointLaw a b t ω • f ω) = t • f a + (1 - t) • f b := by
  classical
  simp [twoPointLaw, add_smul, Finset.sum_add_distrib, ite_smul]

/-- Convex combinations of any two conditional children are real-rooted, because they
are themselves expectations for a different independent law in the next coordinate. -/
theorem children_pairwise_convex_realRooted (n : ℕ) (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (v : Fin (n + 1) → Ω → ι → ℂ)
    (p : Fin n → Ω → ℝ) (hp : ∀ i ω, 0 ≤ p i ω)
    (hsum : ∀ i, ∑ ω, p i ω = 1) (a b : Ω) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    RealRooted
      (t • realExpectedCharpoly n (B + Matrix.vecMulVec (v 0 a) (star (v 0 a)))
        (hB.add (Matrix.posSemidef_vecMulVec_self_star _).1) (fun i ↦ v i.succ) p +
      (1 - t) • realExpectedCharpoly n (B + Matrix.vecMulVec (v 0 b) (star (v 0 b)))
        (hB.add (Matrix.posSemidef_vecMulVec_self_star _).1) (fun i ↦ v i.succ) p) := by
  let p' : Fin (n + 1) → Ω → ℝ := Fin.cons (twoPointLaw a b t) p
  have hp' : ∀ i ω, 0 ≤ p' i ω := by
    intro i ω
    induction i using Fin.cases with
    | zero => exact twoPointLaw_nonneg a b t ht ht1 ω
    | succ i => exact hp i ω
  have hsum' : ∀ i, ∑ ω, p' i ω = 1 := by
    intro i
    induction i using Fin.cases with
    | zero => exact sum_twoPointLaw a b t
    | succ i => exact hsum i
  have h := realExpectedCharpoly_realRooted (n + 1) B hB v
    p' hp' hsum'
  rw [realExpectedCharpoly_succ] at h
  simp only [p', Fin.cons_zero, Fin.cons_succ, sum_twoPointLaw_smul] at h
  exact h

/-- A complete outcome inherits every upper root bound of the expected polynomial.
All real-rootedness and interlacing assertions are proved internally. -/
theorem exists_outcome_inheriting_rootBounds [Nonempty ι]
    (n : ℕ) (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (v : Fin n → Ω → ι → ℂ) (p : Fin n → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1) :
    ∃ q : Fin n → Ω, ∀ x, IsRootUpperBound (realExpectedCharpoly n B hB v p) x →
      IsRootUpperBound
        (realCharpoly (B + ∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i))))
          (outcome_isHermitian n B hB v q)) x := by
  induction n generalizing B with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    intro x hx
    simpa [realExpectedCharpoly] using hx
  | succ n ih =>
    let f : Ω → ℝ[X] := fun ω ↦ realExpectedCharpoly n
      (B + Matrix.vecMulVec (v 0 ω) (star (v 0 ω)))
      (hB.add (Matrix.posSemidef_vecMulVec_self_star _).1)
      (fun i ↦ v i.succ) (fun i ↦ p i.succ)
    have hf (ω : Ω) : (f ω).Monic ∧ (f ω).natDegree = Fintype.card ι :=
      realExpectedCharpoly_monic_natDegree n _ _ _ _ (fun i ↦ hsum i.succ)
    obtain ⟨ω, hω⟩ := exists_member_inheriting_rootBounds f (p 0) (Fintype.card ι)
      Fintype.card_pos (hp 0) (hsum 0) (fun ω ↦ (hf ω).1) (fun ω ↦ (hf ω).2)
      (children_pairwise_convex_realRooted n B hB v (fun i ↦ p i.succ)
        (fun i ↦ hp i.succ) (fun i ↦ hsum i.succ))
    obtain ⟨q, hq⟩ := ih (B + Matrix.vecMulVec (v 0 ω) (star (v 0 ω)))
      (hB.add (Matrix.posSemidef_vecMulVec_self_star _).1)
      (fun i ↦ v i.succ) (fun i ↦ p i.succ)
      (fun i ↦ hp i.succ) (fun i ↦ hsum i.succ)
    refine ⟨Fin.cons ω q, ?_⟩
    intro x hx
    rw [realExpectedCharpoly_succ] at hx
    have hselected := hq x (hω x hx)
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]
      using hselected

/-- In particular, some actual outcome is bounded by the largest root of its
expected characteristic polynomial. -/
theorem exists_outcome_below_expected_largestRoot [Nonempty ι]
    (n : ℕ) (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (v : Fin n → Ω → ι → ℂ) (p : Fin n → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1) :
    ∃ x, IsLargestRoot (realExpectedCharpoly n B hB v p) x ∧
      ∃ q : Fin n → Ω,
        IsRootUpperBound
          (realCharpoly (B + ∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i))))
            (outcome_isHermitian n B hB v q)) x := by
  have hreal := realExpectedCharpoly_realRooted n B hB v p hp hsum
  have hdegree := (realExpectedCharpoly_monic_natDegree n B hB v p hsum).2
  obtain ⟨x, hx⟩ := hreal.exists_largestRoot (by rw [hdegree]; exact Fintype.card_pos)
  obtain ⟨q, hq⟩ := exists_outcome_inheriting_rootBounds n B hB v p hp hsum
  exact ⟨x, hx, q, hq x hx.upperBound⟩

end NoEpsilon.MSSOutcome
