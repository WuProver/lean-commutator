import CommutatorTheorem.Epsilon.BTRootMoment
import CommutatorTheorem.Epsilon.BTMDPSelection

/-!
# Exact second moment of the mixed determinantal polynomial

This file computes the second lower coefficient of the exact MDP from its
coloring leaves.  The calculation is separated into a leaf spectral identity
and the finite same-color count.
-/

namespace CommutatorTheorem.BTExactSecondMoment

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
  Matrix.instL2OpNormedSpace Matrix.instL2OpNormedRing Matrix.instCStarRing

open scoped BigOperators Polynomial
open Polynomial Finset
open CommutatorTheorem
open CommutatorTheorem.BTMixedDet
open CommutatorTheorem.BTMixedDeterminantal
open CommutatorTheorem.BTMDPSelection

private theorem roots_realCharpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    (realCharpoly M hM).roots =
      (Finset.univ : Finset ι).1.map fun i ↦ hM.eigenvalues i := by
  rw [realCharpoly]
  rw [Polynomial.roots_prod]
  · simp
  · exact (realCharpoly_monic M hM).ne_zero

private theorem trace_mul_self_eq_sum_eigenvalues_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    (M * M).trace = ∑ i : ι, (hM.eigenvalues i : ℂ) ^ 2 := by
  let D : Matrix ι ι ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
  let U := hM.eigenvectorUnitary
  calc
    (M * M).trace =
        ((Unitary.conjStarAlgAut ℂ _ U D) *
          (Unitary.conjStarAlgAut ℂ _ U D)).trace := by
            rw [hM.spectral_theorem]
    _ = (Unitary.conjStarAlgAut ℂ _ U (D * D)).trace := by rw [map_mul]
    _ = (D * D).trace := by
      simp only [Unitary.conjStarAlgAut_apply]
      rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
    _ = ∑ i : ι, (hM.eigenvalues i : ℂ) ^ 2 := by
      simp [D, Matrix.trace, pow_two]

private theorem sum_sq_roots_realCharpoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    (↑((realCharpoly M hM).roots.map fun r : ℝ ↦ (r ^ 2 : ℝ)).sum : ℂ) =
      (M * M).trace := by
  rw [roots_realCharpoly, Multiset.map_map]
  simpa [Function.comp_def] using (trace_mul_self_eq_sum_eigenvalues_sq M hM).symm

private theorem roots_realColoringPolynomial {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) :
    (realColoringPolynomial A hA c).roots =
      (Finset.univ : Finset (Fin k)).1.bind fun a ↦
        (realCharpoly (BTMixedDet.principalCompression (A a) c a)
          (BTMixedDet.principalCompression_isHermitian (hA a) c a)).roots := by
  rw [realColoringPolynomial]
  rw [Polynomial.roots_prod]
  exact (realColoringPolynomial_monic A hA c).ne_zero

/-- The squared roots of one exact MDP leaf are the sum of the squared
Hilbert--Schmidt traces of its color compressions. -/
theorem sum_sq_roots_realColoringPolynomial {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) :
    (↑((realColoringPolynomial A hA c).roots.map
      fun r : ℝ ↦ (r ^ 2 : ℝ)).sum : ℂ) =
      ∑ a : Fin k,
        (BTMixedDet.principalCompression (A a) c a *
          BTMixedDet.principalCompression (A a) c a).trace := by
  rw [roots_realColoringPolynomial]
  simp only [Multiset.map_bind, Multiset.sum_bind]
  change Complex.ofRealHom _ = _
  rw [map_multiset_sum Complex.ofRealHom]
  simp only [Multiset.map_map]
  change (∑ a : Fin k,
      (↑((realCharpoly (BTMixedDet.principalCompression (A a) c a)
        (BTMixedDet.principalCompression_isHermitian (hA a) c a)).roots.map
          fun r : ℝ ↦ (r ^ 2 : ℝ)).sum : ℂ)) = _
  apply Finset.sum_congr rfl
  intro a _
  simpa [Function.comp_def] using
    sum_sq_roots_realCharpoly (BTMixedDet.principalCompression (A a) c a)
      (BTMixedDet.principalCompression_isHermitian (hA a) c a)

/-- The real exact-MDP leaf inherits the zero next coefficient of its complex
form. -/
theorem realColoringPolynomial_nextCoeff_eq_zero {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a))
    (c : Coloring n k) :
    (realColoringPolynomial A hA c).nextCoeff = 0 := by
  have hmap := congrArg Polynomial.nextCoeff
    (realColoringPolynomial_map_complex A hA c)
  rw [Polynomial.nextCoeff_map Complex.ofRealHom.injective] at hmap
  rw [coloringPolynomial_nextCoeff_eq_zero hzd c] at hmap
  exact Complex.ofReal_injective (by simpa using hmap)

/-- Exact second-lower coefficient of a coloring leaf.  The statement is
placed in `ℂ` so that the compression traces can be used without inserting
real-part coercions. -/
theorem realColoringPolynomial_coeff_sub_two_eq_neg_trace_sq_div
    {n k : ℕ} (hn : 2 ≤ n)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a))
    (c : Coloring n k) :
    ((realColoringPolynomial A hA c).coeff (n - 2) : ℂ) =
      -(∑ a : Fin k,
        (BTMixedDet.principalCompression (A a) c a *
          BTMixedDet.principalCompression (A a) c a).trace) / 2 := by
  let p := realColoringPolynomial A hA c
  have hp : RealRooted p := realColoringPolynomial_realRooted A hA c
  have hmonic : p.Monic := realColoringPolynomial_monic A hA c
  have hdeg : 2 ≤ p.natDegree := by
    simpa [p, realColoringPolynomial_natDegree A hA c] using hn
  have hmean : p.roots.sum = 0 := by
    rw [CommutatorTheorem.sum_roots_eq_neg_nextCoeff hp hmonic]
    simp [p, realColoringPolynomial_nextCoeff_eq_zero A hA hzd c]
  have hs := CommutatorTheorem.sum_sq_roots_eq_neg_two_mul_coeff_sub_two
    hp hmonic hdeg hmean
  have hsC := congrArg Complex.ofReal hs
  have htrace := sum_sq_roots_realColoringPolynomial A hA c
  change (↑(p.roots.map fun r : ℝ ↦ (r ^ 2 : ℝ)).sum : ℂ) = _ at htrace
  rw [htrace] at hsC
  push_cast at hsC
  change (∑ a : Fin k,
      (BTMixedDet.principalCompression (A a) c a *
        BTMixedDet.principalCompression (A a) c a).trace) =
      -(2 : ℂ) * (p.coeff (p.natDegree - 2) : ℂ) at hsC
  have hpdeg : p.natDegree = n := realColoringPolynomial_natDegree A hA c
  rw [hpdeg] at hsC
  change (p.coeff (n - 2) : ℂ) = _
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  rw [hsC]
  ring

private theorem trace_principalCompression_mul_self_eq_pairSum
    {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n k) (a : Fin k) :
    (BTMixedDet.principalCompression M c a *
      BTMixedDet.principalCompression M c a).trace =
      ∑ i : Fin n, ∑ l : Fin n,
        if c i = a ∧ c l = a then M i l * M l i else 0 := by
  classical
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.diag_apply,
    BTMixedDet.principalCompression_apply]
  calc
    (∑ i : {i : Fin n // c i = a},
        ∑ l : {l : Fin n // c l = a}, M i.1 l.1 * M l.1 i.1) =
        ∑ i ∈ (Finset.univ.filter fun i : Fin n ↦ c i = a),
          ∑ l ∈ (Finset.univ.filter fun l : Fin n ↦ c l = a),
            M i l * M l i := by
      symm
      rw [Finset.sum_subtype (p := fun i : Fin n ↦ c i = a) _ (by simp)]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_subtype (p := fun l : Fin n ↦ c l = a) _ (by simp)]
    _ = ∑ i : Fin n, ∑ l : Fin n,
        if c i = a ∧ c l = a then M i l * M l i else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c i = a
      · rw [if_pos hi, Finset.sum_filter]
        simp [hi]
      · simp [hi]

/-- A fixed zero-diagonal matrix contributes its squared trace to its
designated color fiber with probability exactly `1/k²`. -/
theorem average_trace_principalCompression_sq {n k : ℕ}
    (hn : 2 ≤ n) (M : Matrix (Fin n) (Fin n) ℂ)
    (hzd : ZeroDiag M) (a : Fin k) :
    (Fintype.card (Coloring n k) : ℂ)⁻¹ *
        ∑ c : Coloring n k,
          (BTMixedDet.principalCompression M c a *
            BTMixedDet.principalCompression M c a).trace =
      ((k : ℂ) ^ 2)⁻¹ * (M * M).trace := by
  let w : Fin n → Fin n → ℂ := fun i l ↦ M i l * M l i
  have hwdiag : ∀ i, w i i = 0 := by
    intro i
    simp [w, hzd i]
  calc
    (Fintype.card (Coloring n k) : ℂ)⁻¹ *
        ∑ c : Coloring n k,
          (BTMixedDet.principalCompression M c a *
            BTMixedDet.principalCompression M c a).trace =
        averagePairWeight w a := by
      rw [averagePairWeight]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      rw [trace_principalCompression_mul_self_eq_pairSum]
    _ = ((k : ℂ) ^ 2)⁻¹ * ∑ i : Fin n, ∑ l : Fin n, w i l :=
      averagePairWeight_of_diagonal_eq_zero hn w hwdiag a
    _ = ((k : ℂ) ^ 2)⁻¹ * (M * M).trace := by
      simp only [w, Matrix.trace, Matrix.mul_apply, Matrix.diag_apply]

/-- Summing the preceding count over the matrix/color labels gives the exact
second-trace average of an MDP leaf. -/
theorem average_leaf_trace_sum {n k : ℕ} (hn : 2 ≤ n)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hzd : ∀ a, ZeroDiag (A a)) :
    (Fintype.card (Coloring n k) : ℂ)⁻¹ *
        ∑ c : Coloring n k, ∑ a : Fin k,
          (BTMixedDet.principalCompression (A a) c a *
            BTMixedDet.principalCompression (A a) c a).trace =
      ((k : ℂ) ^ 2)⁻¹ * ∑ a : Fin k, (A a * A a).trace := by
  calc
    (Fintype.card (Coloring n k) : ℂ)⁻¹ *
        ∑ c : Coloring n k, ∑ a : Fin k,
          (BTMixedDet.principalCompression (A a) c a *
            BTMixedDet.principalCompression (A a) c a).trace =
        ∑ a : Fin k, (Fintype.card (Coloring n k) : ℂ)⁻¹ *
          ∑ c : Coloring n k,
            (BTMixedDet.principalCompression (A a) c a *
              BTMixedDet.principalCompression (A a) c a).trace := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ = ∑ a : Fin k, ((k : ℂ) ^ 2)⁻¹ * (A a * A a).trace := by
      apply Finset.sum_congr rfl
      intro a _
      exact average_trace_principalCompression_sq hn (A a) (hzd a) a
    _ = ((k : ℂ) ^ 2)⁻¹ * ∑ a : Fin k, (A a * A a).trace := by
      rw [Finset.mul_sum]

private theorem coeff_sum_realColoringPolynomial {n k d : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    (∑ c : Coloring n k, realColoringPolynomial A hA c).coeff d =
      ∑ c : Coloring n k, (realColoringPolynomial A hA c).coeff d := by
  let s : Finset (Coloring n k) := Finset.univ
  change (∑ c ∈ s, realColoringPolynomial A hA c).coeff d =
    ∑ c ∈ s, (realColoringPolynomial A hA c).coeff d
  induction s using Finset.induction_on with
  | empty => simp
  | @insert c s hc ih => simp [Finset.sum_insert hc, ih]

/-- Exact second-lower coefficient of the real mixed determinantal
polynomial. -/
theorem realMixedDeterminantalPolynomial_coeff_sub_two
    {n k : ℕ} (hn : 2 ≤ n)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a)) :
    ((realMixedDeterminantalPolynomial A hA).coeff (n - 2) : ℂ) =
      -(((k : ℂ) ^ 2)⁻¹ * ∑ a : Fin k, (A a * A a).trace) / 2 := by
  rw [realMixedDeterminantalPolynomial, Polynomial.coeff_smul,
    coeff_sum_realColoringPolynomial]
  change (↑((Fintype.card (Coloring n k) : ℝ)⁻¹ *
    ∑ c : Coloring n k,
      (realColoringPolynomial A hA c).coeff (n - 2)) : ℂ) = _
  push_cast
  simp_rw [realColoringPolynomial_coeff_sub_two_eq_neg_trace_sq_div
    hn A hA hzd]
  have havg := average_leaf_trace_sum hn A hzd
  rw [← havg]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  ring

/-- Exact squared-root sum of a real-rooted exact MDP.  Real-rootedness is
the stability input; all coefficient and coloring computations are discharged
in this file. -/
theorem sum_sq_roots_realMixedDeterminantalPolynomial
    {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a))
    (hp : RealRooted (realMixedDeterminantalPolynomial A hA)) :
    (↑((realMixedDeterminantalPolynomial A hA).roots.map
      fun r : ℝ ↦ (r ^ 2 : ℝ)).sum : ℂ) =
      ((k : ℂ) ^ 2)⁻¹ * ∑ a : Fin k, (A a * A a).trace := by
  let p := realMixedDeterminantalPolynomial A hA
  have hmonic : p.Monic := realMixedDeterminantalPolynomial_monic hk A hA
  have hdeg : 2 ≤ p.natDegree := by
    rw [realMixedDeterminantalPolynomial_natDegree hk A hA]
    exact hn
  have hmean : p.roots.sum = 0 := by
    rw [CommutatorTheorem.sum_roots_eq_neg_nextCoeff hp hmonic]
    simp [realMixedDeterminantalPolynomial_nextCoeff_eq_zero hk A hA hzd]
  have hs := CommutatorTheorem.sum_sq_roots_eq_neg_two_mul_coeff_sub_two
    hp hmonic hdeg hmean
  have hsC := congrArg Complex.ofReal hs
  push_cast at hsC
  have hpdeg : p.natDegree = n :=
    realMixedDeterminantalPolynomial_natDegree hk A hA
  rw [hpdeg] at hsC
  change (↑(p.roots.map fun r : ℝ ↦ (r ^ 2 : ℝ)).sum : ℂ) = _
  calc
    (↑(p.roots.map fun r : ℝ ↦ (r ^ 2 : ℝ)).sum : ℂ) =
        -(2 : ℂ) * (p.coeff (n - 2) : ℂ) := hsC
    _ = ((k : ℂ) ^ 2)⁻¹ * ∑ a : Fin k, (A a * A a).trace := by
      rw [realMixedDeterminantalPolynomial_coeff_sub_two hn A hA hzd]
      ring

/-- Normalized exact second-root-moment formula. -/
theorem rootMeanSquare_realMixedDeterminantalPolynomial
    {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a))
    (hp : RealRooted (realMixedDeterminantalPolynomial A hA)) :
    (↑(CommutatorTheorem.rootMeanSquare
      (realMixedDeterminantalPolynomial A hA)) : ℂ) =
      (((k : ℂ) ^ 2)⁻¹ * ∑ a : Fin k, (A a * A a).trace) / (n : ℂ) := by
  rw [CommutatorTheorem.rootMeanSquare]
  push_cast
  rw [sum_sq_roots_realMixedDeterminantalPolynomial hn hk A hA hzd hp,
    realMixedDeterminantalPolynomial_natDegree hk A hA]

/-- Real form of the exact (unnormalized) squared-root sum. -/
theorem sum_sq_roots_realMixedDeterminantalPolynomial_real
    {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a))
    (hp : RealRooted (realMixedDeterminantalPolynomial A hA)) :
    ((realMixedDeterminantalPolynomial A hA).roots.map
      fun r : ℝ ↦ (r ^ 2 : ℝ)).sum =
      ((k : ℝ) ^ 2)⁻¹ * ∑ a : Fin k, (A a * A a).trace.re := by
  have h := congrArg Complex.re
    (sum_sq_roots_realMixedDeterminantalPolynomial hn hk A hA hzd hp)
  have hscalar : ((k : ℂ) ^ 2)⁻¹ = (↑(((k : ℝ) ^ 2)⁻¹) : ℂ) := by
    apply Complex.ext <;> simp
  rw [hscalar] at h
  change ((realMixedDeterminantalPolynomial A hA).roots.map
      fun r : ℝ ↦ (r ^ 2 : ℝ)).sum =
    Complex.re ((↑(((k : ℝ) ^ 2)⁻¹) : ℂ) *
      ∑ a : Fin k, (A a * A a).trace) at h
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_sum, zero_mul, sub_zero] using h

/-- Every eigenvalue of a Hermitian contraction has square at most one, so
the sum of eigenvalue squares is bounded by the dimension. -/
theorem sum_sq_eigenvalues_le_card {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian)
    (hMnorm : ‖M‖ ≤ 1) :
    ∑ i : Fin n, (hM.eigenvalues i) ^ 2 ≤ n := by
  have hdiagNorm : ‖fun i : Fin n ↦ (hM.eigenvalues i : ℂ)‖ ≤ 1 := by
    have hMnorm' := hMnorm
    rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal] at hMnorm'
    exact hMnorm'
  calc
    ∑ i : Fin n, (hM.eigenvalues i) ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have habs : |hM.eigenvalues i| ≤ 1 := by
        calc
          |hM.eigenvalues i| = ‖(hM.eigenvalues i : ℂ)‖ := by
            symm
            simp [Real.norm_eq_abs]
          _ ≤ ‖fun j : Fin n ↦ (hM.eigenvalues j : ℂ)‖ :=
            norm_le_pi_norm (fun j : Fin n ↦ (hM.eigenvalues j : ℂ)) i
          _ ≤ 1 := hdiagNorm
      have hb := (abs_le.mp habs)
      have hminus : 0 ≤ 1 - hM.eigenvalues i := sub_nonneg.mpr hb.2
      have hplus : 0 ≤ 1 + hM.eigenvalues i := by linarith [hb.1]
      nlinarith [mul_nonneg hminus hplus]
    _ = n := by simp

/-- Real part of the squared trace of a Hermitian contraction is at most the
ambient dimension. -/
theorem trace_mul_self_re_le_card {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian)
    (hMnorm : ‖M‖ ≤ 1) :
    (M * M).trace.re ≤ n := by
  rw [trace_mul_self_eq_sum_eigenvalues_sq M hM]
  simpa [pow_two] using sum_sq_eigenvalues_le_card M hM hMnorm

/-- The exact MDP of `k` zero-diagonal Hermitian contractions has normalized
second root moment at most `1/k`. -/
theorem rootMeanSquare_realMixedDeterminantalPolynomial_le_inv
    {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hzd : ∀ a, ZeroDiag (A a))
    (hAnorm : ∀ a, ‖A a‖ ≤ 1)
    (hp : RealRooted (realMixedDeterminantalPolynomial A hA)) :
    CommutatorTheorem.rootMeanSquare
        (realMixedDeterminantalPolynomial A hA) ≤ 1 / (k : ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hnR : 0 < (n : ℝ) := by positivity
  have htrace :
      ∑ a : Fin k, (A a * A a).trace.re ≤ (k : ℝ) * (n : ℝ) := by
    calc
      ∑ a : Fin k, (A a * A a).trace.re ≤ ∑ _a : Fin k, (n : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        exact trace_mul_self_re_le_card (A a) (hA a) (hAnorm a)
      _ = (k : ℝ) * (n : ℝ) := by simp
  rw [CommutatorTheorem.rootMeanSquare,
    realMixedDeterminantalPolynomial_natDegree hk A hA,
    sum_sq_roots_realMixedDeterminantalPolynomial_real hn hk A hA hzd hp]
  calc
    ((k : ℝ) ^ 2)⁻¹ * (∑ a : Fin k, (A a * A a).trace.re) / (n : ℝ) ≤
        ((k : ℝ) ^ 2)⁻¹ * ((k : ℝ) * (n : ℝ)) / (n : ℝ) := by
      gcongr
    _ = 1 / (k : ℝ) := by
      field_simp

end CommutatorTheorem.BTExactSecondMoment
