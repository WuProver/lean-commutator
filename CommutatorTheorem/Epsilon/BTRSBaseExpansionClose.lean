import CommutatorTheorem.Epsilon.BTRSColoringLeaf

/-!
# Closing the exact-MDP base expansion

This file combines the differentiated determinant-product coloring expansion
with the principal-compression interpretation of every coloring leaf.  The
only remaining calculation is the normalization
`(k!)^n / k^n = ((k - 1)!)^n` for `0 < k`.
-/

namespace CommutatorTheorem.BTRSBaseExpansionClose

open scoped BigOperators Polynomial
open Polynomial Finset
open CommutatorTheorem
open CommutatorTheorem.BTMixedDet
open CommutatorTheorem.BTMixedDeterminantal
open CommutatorTheorem.BTDeterminantStability
open CommutatorTheorem.BTMDPSelection
open CommutatorTheorem.BTRealStabilityClosure
open CommutatorTheorem.BTRSStabilityBridge
open CommutatorTheorem.BTRSExactMDPHarness
open CommutatorTheorem.BTRSBaseExpansion
open CommutatorTheorem.BTRSColoringLeaf

private theorem factorial_succ_pow_mul_inv_coloring_card
    (n m : ℕ) :
    (((m + 1).factorial : ℂ) ^ n) *
        ((Fintype.card (Coloring n (m + 1)) : ℂ)⁻¹) =
      ((m.factorial : ℂ) ^ n) := by
  rw [coloring_card, Nat.factorial_succ]
  push_cast
  rw [mul_pow]
  have hm : (m + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero m
  field_simp

/-- The exact determinant derivative has precisely the factorial
normalization required by the uniform exact mixed-determinantal polynomial. -/
theorem rsExactMDPFactorialBaseIdentity :
    RSExactMDPFactorialBaseIdentity := by
  intro n k hk A hA
  cases k with
  | zero => omega
  | succ m =>
      apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
      rw [map_diagonalizeReal]
      unfold rsExactMDPBase
      rw [← iteratedPDeriv_map, map_realHermitianDetProduct A hA]
      rw [show m + 1 - 1 = m by omega]
      rw [iteratedDetProduct_eq_sum_coloringDerivativeTerm A]
      rw [Polynomial.map_smul,
        realMixedDeterminantalPolynomial_map_complex A hA]
      rw [mixedDeterminantalPolynomial]
      simp only [diagonalize, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum]
      have hleaf (c : Coloring n (m + 1)) :
          MvPolynomial.eval₂ Polynomial.C (fun _ : Fin n ↦ Polynomial.X)
              (coloringDerivativeTerm (fun i : Fin n ↦ i) c
                (fun a ↦ hermitianDetPoly (A a))) =
            coloringPolynomial A c := by
        simpa only [diagonalize] using
          diagonalize_coloringDerivativeTerm A hA c
      simp_rw [hleaf]
      rw [smul_eq_C_mul, smul_eq_C_mul]
      rw [← mul_assoc, ← map_mul]
      have hcast :
          Complex.ofRealHom (((m + 1).factorial : ℝ) ^ n) =
            (((m + 1).factorial : ℂ) ^ n) := by
        norm_num
      rw [hcast, factorial_succ_pow_mul_inv_coloring_card n m]

/-- The corrected base-and-deletion expansion harness is now a theorem. -/
theorem rsExactMDPBaseDeletionExpansion :
    RSExactMDPBaseDeletionExpansion :=
  rsExactMDPBaseDeletionExpansion_of_factorialBase
    rsExactMDPFactorialBaseIdentity

end CommutatorTheorem.BTRSBaseExpansionClose
