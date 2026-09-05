import CommutatorTheorem.Epsilon.BTExactSecondMoment
import CommutatorTheorem.Epsilon.BTExactRootInterval
import CommutatorTheorem.Epsilon.BTRootEndpoint
import CommutatorTheorem.Epsilon.BTRootShrinkArithmetic
import CommutatorTheorem.Epsilon.BTMDPDeletionIdentity

/-!
# Exact-MDP root-shrinking assembly

This file assembles the algebraic exact-MDP facts with the closed-parameter
root-shrinking theorem.  The only analytic/stability input of the ambient
result is real-rootedness of the exact MDP itself.
-/

namespace CommutatorTheorem.BTMDPRootShrinkAssembly

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
  Matrix.instL2OpNormedSpace Matrix.instL2OpNormedRing Matrix.instCStarRing

open scoped BigOperators Polynomial
open Polynomial Finset
open CommutatorTheorem
open CommutatorTheorem.BTMixedDet
open CommutatorTheorem.BTMDPSelection
open CommutatorTheorem.BTMDPDeletionIdentity
open CommutatorTheorem.BTExactSecondMoment
open CommutatorTheorem.BTExactRootInterval

/-- The MDP restricted to all ambient coordinates is the ambient MDP. -/
theorem restrictedMDP_univ {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    restrictedMDP A hA Finset.univ =
      realMixedDeterminantalPolynomial A hA := by
  let s : Finset (Fin n) := Finset.univ
  have hcard : s.card = n := by simp [s]
  have hemb : s.orderEmbOfFin rfl =
      (Fin.castOrderIso hcard).toOrderEmbedding := by
    symm
    apply Finset.orderEmbOfFin_unique' rfl
    intro i
    simp [s]
  have hfamily :
      reindexFamilyByFinCast hcard (restrictFamilyToFinset A s) = A := by
    funext a
    ext i j
    change A a
      (s.orderEmbOfFin rfl ((Fin.castOrderIso hcard).symm i))
      (s.orderEmbOfFin rfl ((Fin.castOrderIso hcard).symm j)) = A a i j
    rw [hemb]
    simp
  change realMixedDeterminantalPolynomial (restrictFamilyToFinset A s)
      (restrictFamilyToFinset_isHermitian hA s) = _
  calc
    realMixedDeterminantalPolynomial (restrictFamilyToFinset A s)
        (restrictFamilyToFinset_isHermitian hA s) =
      realMixedDeterminantalPolynomial
        (reindexFamilyByFinCast hcard (restrictFamilyToFinset A s))
        (reindexFamilyByFinCast_isHermitian hcard
          (restrictFamilyToFinset_isHermitian hA s)) :=
      realMixedDeterminantalPolynomial_reindexFamilyByFinCast
        hcard (restrictFamilyToFinset A s)
          (restrictFamilyToFinset_isHermitian hA s)
    _ = realMixedDeterminantalPolynomial A hA :=
      realMixedDeterminantalPolynomial_congr _ _ _ _ hfamily

/-- At the root of the deletion tree, the normalized conditional MDP is the
normalized `(n-d)`-fold derivative of the ambient exact MDP. -/
theorem normalizedConditionalMDP_univ {n k d : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    normalizedConditionalMDP (d := d) A hA Finset.univ =
      ((n.descFactorial (n - d) : ℝ)⁻¹) •
        Polynomial.derivative^[n - d]
          (realMixedDeterminantalPolynomial A hA) := by
  simp [normalizedConditionalMDP, restrictedMDP_univ]

/-- Multiplication by the nonzero normalization constant does not alter the
roots of the root-node derivative. -/
theorem normalizedConditionalMDP_univ_rootUpperBound_of_derivative
    {n k d : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) {x : ℝ}
    (hx : IsRootUpperBound
      (Polynomial.derivative^[n - d]
        (realMixedDeterminantalPolynomial A hA)) x) :
    IsRootUpperBound
      (normalizedConditionalMDP (d := d) A hA Finset.univ) x := by
  rw [normalizedConditionalMDP_univ]
  intro r hr
  apply hx r
  have hdesc : n.descFactorial (n - d) ≠ 0 :=
    (Nat.descFactorial_pos.mpr (Nat.sub_le n d)).ne'
  have hscalar : ((n.descFactorial (n - d) : ℝ)⁻¹) ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast hdesc)
  rw [Polynomial.IsRoot] at hr ⊢
  simpa [hscalar] using hr

/-- Root shrinking for the ambient exact MDP.  Here `d` is the retained
dimension, so the polynomial is differentiated `n-d` times. -/
theorem exactMDP_iterateDerivative_strictRootUpperBound
    {n k d : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (hd : 0 < d) (hdn : d < n)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1)
    (hfrac : (d : ℝ) / (n : ℝ) ≤ ε ^ 2 / (6 * (k : ℝ)))
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (hzd : ∀ a, ZeroDiag (A a))
    (hAnorm : ∀ a, ‖A a‖ ≤ 1)
    (hp : RealRooted (realMixedDeterminantalPolynomial A hA)) :
    IsStrictRootUpperBound
      (Polynomial.derivative^[n - d]
        (realMixedDeterminantalPolynomial A hA))
      (ε / (k : ℝ)) := by
  let p := realMixedDeterminantalPolynomial A hA
  let α := CommutatorTheorem.rootMeanSquare p
  let c : ℝ := (d : ℝ) / (n : ℝ)
  have hnR : 0 < (n : ℝ) := by positivity
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hpdeg : p.natDegree = n :=
    realMixedDeterminantalPolynomial_natDegree hk A hA
  have hpmonic : p.Monic := realMixedDeterminantalPolynomial_monic hk A hA
  have hpdegpos : 0 < p.natDegree := by rw [hpdeg]; omega
  have hαnonneg : 0 ≤ α := by
    have hsum : 0 ≤ (p.roots.map fun r ↦ r ^ 2).sum := by
      apply Multiset.sum_nonneg
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨r, _, rfl⟩ := hx
      exact sq_nonneg r
    dsimp [α, CommutatorTheorem.rootMeanSquare]
    exact div_nonneg hsum (Nat.cast_nonneg _)
  have hαbound : α ≤ 1 / (k : ℝ) := by
    dsimp [α, p]
    exact rootMeanSquare_realMixedDeterminantalPolynomial_le_inv
      hn hk A hA hzd hAnorm hp
  have hmean : p.roots.sum = 0 := by
    rw [CommutatorTheorem.sum_roots_eq_neg_nextCoeff hp hpmonic]
    simp [realMixedDeterminantalPolynomial_nextCoeff_eq_zero hk A hA hzd]
  have hsq : (p.roots.map fun r ↦ r ^ 2).sum =
      (p.natDegree : ℝ) * α := by
    dsimp [α, CommutatorTheorem.rootMeanSquare]
    field_simp [show (p.natDegree : ℝ) ≠ 0 by exact_mod_cast hpdegpos.ne']
  have hroots : ∀ r, p.IsRoot r → r ≤ 1 := by
    dsimp [p]
    exact realMixedDeterminantalPolynomial_rootUpperBound_one hk A hA hAnorm
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hcone : c < 1 := by
    dsimp [c]
    exact (div_lt_one hnR).2 (by exact_mod_cast hdn)
  have hc_nonneg : 0 ≤ c := hcpos.le
  have hc_target : c ≤ ε ^ 2 / (6 * (k : ℝ)) := by
    simpa [c] using hfrac
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk.ne')
  have hαone : α ≤ 1 := by
    calc
      α ≤ 1 / (k : ℝ) := hαbound
      _ ≤ 1 := (div_le_one hkR).2 hkone
  have hcsmall : c ≤ (1 : ℝ) / 6 := by
    apply hc_target.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * (k : ℝ))).2
    have hεsq : ε ^ 2 < 1 := by nlinarith
    nlinarith
  have hcα : c ≤ (1 + α)⁻¹ := by
    have hprod : c * (1 + α) ≤ ((1 : ℝ) / 6) * 2 := by
      calc
        c * (1 + α) ≤ ((1 : ℝ) / 6) * (1 + α) :=
          mul_le_mul_of_nonneg_right hcsmall (by linarith)
        _ ≤ ((1 : ℝ) / 6) * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < 1 + α)).2
    linarith
  have hderivlt : n - d < p.natDegree := by
    rw [hpdeg]
    omega
  have hderivfrac : ((n - d : ℕ) : ℝ) =
      (p.natDegree : ℝ) * (1 - c) := by
    rw [hpdeg, Nat.cast_sub hdn.le]
    dsimp [c]
    field_simp
  have hroot := CommutatorTheorem.rootUpperBound_iterate_derivative_of_mean_zero_second_moment_le
    hp hpmonic hpdegpos hcpos hcone hαnonneg hcα hroots hmean hsq
      (n - d) hderivlt hderivfrac
  have hnumeric := CommutatorTheorem.jointRI_rootShrink_constant_of_c_le
    hk hε hεone hαnonneg hαbound hc_nonneg hc_target
  have htarget :
      c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α) < ε / (k : ℝ) := by
    apply (lt_div_iff₀ hkR).2
    simpa [mul_comm] using hnumeric
  intro r hr
  exact (hroot r hr).trans_lt htarget

/-- Conditional interlacing selects a `d`-coordinate restriction whose exact
MDP inherits the strict ambient root bound.  The midpoint with the largest
ambient derivative root converts the weak selection theorem into a strict
bound. -/
theorem exists_restrictedMDP_strictRootUpperBound
    {n k d : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (hd : 0 < d) (hdn : d < n)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1)
    (hfrac : (d : ℝ) / (n : ℝ) ≤ ε ^ 2 / (6 * (k : ℝ)))
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (hzd : ∀ a, ZeroDiag (A a))
    (hAnorm : ∀ a, ‖A a‖ ≤ 1)
    (hp : RealRooted (realMixedDeterminantalPolynomial A hA))
    (hstable : MDPConditionalInterlacing (d := d) A hA) :
    ∃ s : Finset (Fin n), s.card = d ∧
      IsStrictRootUpperBound (restrictedMDP A hA s) (ε / (k : ℝ)) := by
  let p := realMixedDeterminantalPolynomial A hA
  let q := Polynomial.derivative^[n - d] p
  have hpdeg : p.natDegree = n :=
    realMixedDeterminantalPolynomial_natDegree hk A hA
  have hiterle : n - d ≤ p.natDegree := by
    rw [hpdeg]
    exact Nat.sub_le n d
  have hqdeg : q.natDegree = d := by
    dsimp [q]
    rw [CommutatorTheorem.natDegree_iterate_derivative_eq_sub_real hiterle,
      hpdeg]
    omega
  have hqdegpos : 0 < q.natDegree := by rw [hqdeg]; exact hd
  have hqreal : RealRooted q := by
    dsimp [q, p]
    exact hp.iterate_derivative (n - d)
  have hstrict : IsStrictRootUpperBound q (ε / (k : ℝ)) := by
    dsimp [q, p]
    exact exactMDP_iterateDerivative_strictRootUpperBound
      hn hk hd hdn hε hεone hfrac A hA hzd hAnorm hp
  obtain ⟨ℓ, hℓ⟩ := hqreal.exists_largestRoot hqdegpos
  have hℓtarget : ℓ < ε / (k : ℝ) := hstrict ℓ hℓ.isRoot
  let x : ℝ := (ℓ + ε / (k : ℝ)) / 2
  have hℓx : ℓ ≤ x := by dsimp [x]; linarith
  have hxtarget : x < ε / (k : ℝ) := by dsimp [x]; linarith
  have hqbound : IsRootUpperBound q x := by
    intro r hr
    exact (hℓ.upperBound r hr).trans hℓx
  have hnormalized : IsRootUpperBound
      (normalizedConditionalMDP (d := d) A hA Finset.univ) x := by
    apply normalizedConditionalMDP_univ_rootUpperBound_of_derivative
    simpa [q, p] using hqbound
  obtain ⟨s, hscard, hselect⟩ :=
    select_restrictedMDP A hA hd hdn.le hstable
  have hsbound : IsRootUpperBound (restrictedMDP A hA s) x :=
    hselect x hnormalized
  refine ⟨s, hscard, ?_⟩
  intro r hr
  exact (hsbound r hr).trans_lt hxtarget

end CommutatorTheorem.BTMDPRootShrinkAssembly
