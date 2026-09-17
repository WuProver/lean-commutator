import CommutatorTheorem.NoEpsilon.MSSOutcome
import CommutatorTheorem.NoEpsilon.MSSTranslation
import CommutatorTheorem.NoEpsilon.MSSPencilBarrier
import Mathlib.Analysis.Matrix.PosDef

/-!
# Finite complex-vector MSS selection

This module connects the proved mixed-characteristic formula, the proved finite
interlacing selector, and the proved quantitative barrier estimate. Matrix norms
are the Euclidean operator norm throughout.
-/

namespace NoEpsilon.MSSFinite

open Polynomial CommutatorTheorem CommutatorTheorem.BTMDPSelection
open NoEpsilon.MSSCharpoly NoEpsilon.MSSOutcome NoEpsilon.MSSTranslation
open scoped BigOperators Polynomial ComplexOrder Matrix.Norms.L2Operator

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

/-- An upper bound for every real root of the characteristic polynomial controls
the Euclidean operator norm of a positive semidefinite matrix. -/
theorem norm_le_of_realCharpoly_rootBound (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (x : ℝ) (hx : 0 ≤ x) (hroot : IsRootUpperBound (realCharpoly A hA.1) x) :
    ‖A‖ ≤ x := by
  have heig (i : ι) : hA.1.eigenvalues i ≤ x := by
    apply hroot
    simp only [Polynomial.IsRoot, realCharpoly, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  rw [hA.1.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hx).mpr
  intro i
  simpa only [Function.comp_apply, RCLike.norm_ofReal, Real.norm_eq_abs,
    abs_of_nonneg (hA.eigenvalues_nonneg i)] using heig i

/-- The expected characteristic polynomial has no root above the MSS bound. -/
theorem expected_rootBound [Nonempty ι]
    (n : ℕ) (v : Fin n → Ω → ι → ℂ) (p : Fin n → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1)
    (hTotal : (∑ i, ∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))) = 1)
    (ε : ℝ) (hε : 0 < ε)
    (htrace : ∀ i, (∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))).trace.re ≤ ε) :
    IsRootUpperBound (realExpectedCharpoly n 0 Matrix.isHermitian_zero v p)
      ((1 + Real.sqrt ε)^2) := by
  let A : Fin n → Matrix ι ι ℂ :=
    fun i ↦ ∑ ω, (p i ω : ℂ) • Matrix.vecMulVec (v i ω) (star (v i ω))
  have hA : ∀ i, (A i).PosSemidef := by
    intro i
    apply Matrix.posSemidef_sum
    intro ω _
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul
      (show (0 : ℂ) ≤ (p i ω : ℂ) from by exact_mod_cast hp i ω)
  intro r hr
  by_contra hn
  have hbound : (1 + Real.sqrt ε)^2 ≤ r := (lt_of_not_ge hn).le
  have hne := MSSPencilBarrier.psdPencil_fold_eval_ne_zero A hA hTotal ε hε htrace
    (List.finRange n).reverse (by simpa using List.nodup_finRange n) r hbound
  apply hne
  rw [← eval_expected_eq_psdPencil n v p hsum hTotal (r : ℂ)]
  rw [Polynomial.eval_map]
  change Polynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom r) _ = 0
  rw [Polynomial.eval₂_at_apply, hr, map_zero]

/-- Finite MSS selection for complex vectors, with the exact operator norm bound.
The covariance trace hypothesis is the expected squared Euclidean vector norm. -/
theorem exists_outcome_norm_le [Nonempty ι]
    (n : ℕ) (v : Fin n → Ω → ι → ℂ) (p : Fin n → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1)
    (hTotal : (∑ i, ∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))) = 1)
    (ε : ℝ) (hε : 0 < ε)
    (htrace : ∀ i, (∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))).trace.re ≤ ε) :
    ∃ q : Fin n → Ω,
      ‖∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i)))‖ ≤ (1 + Real.sqrt ε)^2 := by
  obtain ⟨q, hq⟩ := exists_outcome_inheriting_rootBounds n 0 Matrix.isHermitian_zero
    v p hp hsum
  have hbound := hq _ (expected_rootBound n v p hp hsum hTotal ε hε htrace)
  have hA := Matrix.posSemidef_sum Finset.univ
    (fun i _ ↦ Matrix.posSemidef_vecMulVec_self_star (v i (q i)))
  refine ⟨q, norm_le_of_realCharpoly_rootBound _ hA _ (sq_nonneg _) ?_⟩
  simpa only [zero_add] using hbound

/-- Finite MSS with an arbitrary finite index type, without changing the vector space
or adding zero coordinates. -/
theorem exists_outcome_norm_le_fintype {κ : Type*} [Fintype κ] [Nonempty ι]
    (v : κ → Ω → ι → ℂ) (p : κ → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1)
    (hTotal : (∑ i, ∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))) = 1)
    (ε : ℝ) (hε : 0 < ε)
    (htrace : ∀ i, (∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))).trace.re ≤ ε) :
    ∃ q : κ → Ω,
      ‖∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i)))‖ ≤ (1 + Real.sqrt ε)^2 := by
  classical
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have ht : (∑ i, ∑ ω, (p (e i) ω : ℂ) •
      Matrix.vecMulVec (v (e i) ω) (star (v (e i) ω))) = 1 := by
    exact (e.sum_comp (fun i : κ ↦ ∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω)))).trans hTotal
  obtain ⟨q, hq⟩ := exists_outcome_norm_le (Fintype.card κ)
    (fun i ↦ v (e i)) (fun i ↦ p (e i)) (fun i ↦ hp (e i))
    (fun i ↦ hsum (e i)) ht ε hε (fun i ↦ htrace (e i))
  refine ⟨fun i ↦ q (e.symm i), ?_⟩
  have heq : (∑ i : κ, Matrix.vecMulVec (v i (q (e.symm i)))
      (star (v i (q (e.symm i))))) =
        ∑ i, Matrix.vecMulVec (v (e i) (q i)) (star (v (e i) (q i))) := by
    rw [← e.sum_comp]
    simp
  rw [heq]
  exact hq

/-- The trace of an outer product is its squared Euclidean vector norm. -/
theorem trace_outer_re (v : ι → ℂ) :
    (Matrix.vecMulVec v (star v)).trace.re = MSSSelection.energy v := by
  simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec, Complex.re_sum, MSSSelection.energy,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]

/-- Covariance trace is the expected squared Euclidean norm. -/
theorem trace_mean_outer_re (v : Ω → ι → ℂ) (p : Ω → ℝ) :
    (∑ ω, (p ω : ℂ) • Matrix.vecMulVec (v ω) (star (v ω))).trace.re =
      ∑ ω, p ω * MSSSelection.energy (v ω) := by
  simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    trace_outer_re]

/-- The full finite complex-vector MSS statement in expected-energy form.
Empty ambient vector spaces are included. -/
theorem finite_mss {κ : Type*} [Fintype κ]
    (v : κ → Ω → ι → ℂ) (p : κ → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1)
    (hTotal : (∑ i, ∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))) = 1)
    (ε : ℝ) (hε : 0 < ε)
    (henergy : ∀ i, ∑ ω, p i ω * MSSSelection.energy (v i ω) ≤ ε) :
    ∃ q : κ → Ω,
      ‖∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i)))‖ ≤ (1 + Real.sqrt ε)^2 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inr hn =>
    haveI : Nonempty ι := hn
    apply exists_outcome_norm_le_fintype v p hp hsum hTotal ε hε
    intro i
    rw [trace_mean_outer_re]
    exact henergy i
  | inl he =>
    haveI : IsEmpty ι := he
    have hΩ (i : κ) : Nonempty Ω := by
      by_contra hn
      haveI : IsEmpty Ω := not_nonempty_iff.mp hn
      have hi := hsum i
      simp at hi
    let q : κ → Ω := fun i ↦ Classical.choice (hΩ i)
    refine ⟨q, ?_⟩
    have hz : (∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i)))) = 0 :=
      Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact sq_nonneg _

/-- Finite MSS selection in the positive support of each marginal distribution.
Zero-weight vector values do not affect the covariance or expected energy. -/
theorem finite_mss_supported {κ : Type*} [Fintype κ]
    (v : κ → Ω → ι → ℂ) (p : κ → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1)
    (hTotal : (∑ i, ∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))) = 1)
    (ε : ℝ) (hε : 0 < ε)
    (henergy : ∀ i, ∑ ω, p i ω * MSSSelection.energy (v i ω) ≤ ε) :
    ∃ q : κ → Ω, (∀ i, 0 < p i (q i)) ∧
      ‖∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i)))‖ ≤
        (1 + Real.sqrt ε)^2 := by
  classical
  have hex (i : κ) : ∃ ω, 0 < p i ω := by
    by_contra h
    have hz : ∀ ω, p i ω = 0 := fun ω ↦
      le_antisymm (le_of_not_gt (fun hpos ↦ h ⟨ω, hpos⟩)) (hp i ω)
    have hi := hsum i
    simp [hz] at hi
  choose s hs using hex
  let repair : κ → Ω → Ω := fun i ω ↦ if 0 < p i ω then ω else s i
  have hsupport (i : κ) (ω : Ω) : 0 < p i (repair i ω) := by
    dsimp [repair]
    split_ifs with h
    · exact h
    · exact hs i
  let w : κ → Ω → ι → ℂ := fun i ω ↦ v i (repair i ω)
  have hcov (i : κ) (ω : Ω) :
      (p i ω : ℂ) • Matrix.vecMulVec (w i ω) (star (w i ω)) =
        (p i ω : ℂ) • Matrix.vecMulVec (v i ω) (star (v i ω)) := by
    by_cases h : 0 < p i ω
    · simp [w, repair, h]
    · have hz : p i ω = 0 := le_antisymm (le_of_not_gt h) (hp i ω)
      simp [hz]
  have henergy' (i : κ) : ∑ ω, p i ω * MSSSelection.energy (w i ω) ≤ ε := by
    have heq (ω : Ω) : p i ω * MSSSelection.energy (w i ω) =
        p i ω * MSSSelection.energy (v i ω) := by
      by_cases h : 0 < p i ω
      · simp [w, repair, h]
      · have hz : p i ω = 0 := le_antisymm (le_of_not_gt h) (hp i ω)
        simp [hz]
    simpa only [heq] using henergy i
  obtain ⟨q, hq⟩ := finite_mss w p hp hsum (by simpa only [hcov] using hTotal)
    ε hε henergy'
  exact ⟨fun i ↦ repair i (q i), fun i ↦ hsupport i (q i), hq⟩

/-- The supported MSS outcome has strictly positive joint weight under the finite
product distribution, exhibiting a positive-probability good outcome. -/
theorem finite_mss_positive_probability {κ : Type*} [Fintype κ]
    (v : κ → Ω → ι → ℂ) (p : κ → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1)
    (hTotal : (∑ i, ∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))) = 1)
    (ε : ℝ) (hε : 0 < ε)
    (henergy : ∀ i, ∑ ω, p i ω * MSSSelection.energy (v i ω) ≤ ε) :
    ∃ q : κ → Ω, 0 < ∏ i, p i (q i) ∧
      ‖∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i)))‖ ≤
        (1 + Real.sqrt ε)^2 := by
  obtain ⟨q, hsupport, hq⟩ := finite_mss_supported v p hp hsum hTotal ε hε henergy
  exact ⟨q, Finset.prod_pos (fun i _ ↦ hsupport i), hq⟩

end NoEpsilon.MSSFinite
