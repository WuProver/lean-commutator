import CommutatorTheorem.Epsilon.BTFellTaylorCount
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Exact Descartes count for real-rooted polynomials

For a monic polynomial all of whose roots are real, Descartes' upper bound is
an equality.  The proof combines the localized Rolle sandwiches with the
endpoint parity rule.  A zero constant coefficient is removed by `divX`.
-/

open scoped Polynomial

namespace CommutatorTheorem.BTFellExactDescartes

open Polynomial
open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTFellRolleCount
open CommutatorTheorem.BTFellDescartes
open CommutatorTheorem.BTFellTaylorCount
open CommutatorTheorem.BTFellCrossGap

/-- For a monic real-rooted polynomial, coefficient sign variations count
positive roots exactly, including multiplicity. -/
theorem roots_countP_pos_eq_signVariations
    {p : ℝ[X]} (hmonic : p.Monic) (hreal : RealRooted p) :
    p.roots.countP (0 < ·) = p.signVariations := by
  let motive := fun d : ℕ ↦ ∀ p : ℝ[X], p.natDegree = d →
    p.Monic → RealRooted p →
      p.roots.countP (0 < ·) = p.signVariations
  refine Nat.strong_induction_on (p := motive) p.natDegree ?_
    p rfl hmonic hreal
  intro d ih p hdegree hmonic hreal
  by_cases hd : d = 0
  · have hroots : p.roots.card = 0 := by
      rw [← hreal.natDegree_eq_card_roots, hdegree, hd]
    have hcount : p.roots.countP (0 < ·) = 0 := by
      exact Nat.eq_zero_of_le_zero
        ((Multiset.countP_le_card _ _).trans_eq hroots)
    have hvar : p.signVariations = 0 := by
      exact Nat.eq_zero_of_le_zero
        ((signVariations_le_natDegree p).trans_eq (hdegree.trans hd))
    rw [hcount, hvar]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hpdeg : 0 < p.natDegree := by simpa [hdegree] using hdpos
    by_cases hconst : p.coeff 0 = 0
    · let q := p.divX
      have hpEq : p = q * X := by
        dsimp [q]
        simpa [hconst] using (p.divX_mul_X_add).symm
      have hqne : q ≠ 0 := by
        intro hq
        rw [hq, zero_mul] at hpEq
        exact hmonic.ne_zero hpEq
      have hqmonic : q.Monic := by
        apply (monic_X).of_mul_monic_right
        simpa [hpEq] using hmonic
      have hqreal : RealRooted q := by
        rw [hpEq] at hreal
        have hx : RealRooted ((X - C (0 : ℝ)) * q) := by
          simpa [mul_comm] using hreal
        exact splits_X_sub_C_mul_iff.mp hx
      have hqdeg : q.natDegree = d - 1 := by
        dsimp [q]
        rw [natDegree_divX_eq_natDegree_tsub_one, hdegree]
      have hqdlt : q.natDegree < d := by omega
      have hiq := ih q.natDegree hqdlt q rfl hqmonic hqreal
      have hrootsEq : p.roots.countP (0 < ·) =
          q.roots.countP (0 < ·) := by
        rw [hpEq, roots_mul (mul_ne_zero hqne X_ne_zero), roots_X]
        rw [Multiset.countP_add]
        have hz : ({0} : Multiset ℝ).countP (0 < ·) = 0 := by
          rw [Multiset.countP_eq_zero]
          simp
        omega
      rw [hrootsEq, hiq, hpEq, signVariations_mul_X hqne]
    · have hconst' : p.coeff 0 ≠ 0 := hconst
      let q := normalizedDerivative d p
      have hdcast : (d : ℝ) ≠ 0 := by exact_mod_cast hd
      have hqmonic : q.Monic :=
        (normalizedDerivative_isMonicOfDegree hdpos hmonic hdegree).monic
      have hqdeg : q.natDegree = d - 1 :=
        (normalizedDerivative_isMonicOfDegree hdpos hmonic hdegree).natDegree_eq
      have hqreal : RealRooted q := by
        dsimp [q, normalizedDerivative]
        rw [smul_eq_C_mul]
        exact (realRooted_derivative hreal hpdeg).C_mul _
      have hqdlt : q.natDegree < d := by omega
      have hiq := ih q.natDegree hqdlt q rfl hqmonic hqreal
      have hqroots : q.roots = p.derivative.roots := by
        dsimp [q, normalizedDerivative]
        exact roots_smul_nonzero p.derivative (inv_ne_zero hdcast)
      have hqsign : q.signVariations = p.derivative.signVariations := by
        dsimp [q, normalizedDerivative]
        rw [smul_eq_C_mul,
          signVariations_C_mul p.derivative (inv_ne_zero hdcast)]
      have hderivExact : p.derivative.roots.countP (0 < ·) =
          p.derivative.signVariations := by
        rw [← hqroots, ← hqsign]
        exact hiq
      let N := p.roots.countP (0 < ·)
      let M := p.derivative.roots.countP (0 < ·)
      let S := p.signVariations
      let T := p.derivative.signVariations
      have hnotroot : ¬ p.IsRoot 0 := by
        intro hr
        apply hconst'
        rw [IsRoot, ← eval₂_id, eval₂_at_zero] at hr
        exact hr
      have hMN : M ≤ N := by
        simpa [M, N, rootsGTCount, Multiset.countP_eq_card_filter] using
          derivative_rootsGTCount_le hdpos hmonic hreal hdegree
            (b := 0) hnotroot
      have hNM : N ≤ M + 1 := roots_countP_pos_le_derivative_succ p
      have hTS : T ≤ S := signVariations_derivative_le hpdeg hconst'
      have hST : S ≤ T + 1 :=
        signVariations_le_derivative_add_one hpdeg hconst'
      have hMT : M = T := by simpa [M, T] using hderivExact
      have hparity : Even N ↔ Even S := by
        simpa [N, S, rootsGTCount, Multiset.countP_eq_card_filter] using
          even_rootsGTCount_iff_even_signVariations_taylor
            hmonic hreal (x := 0) hnotroot
      rcases hparity with ⟨hNS, hSN⟩
      by_cases hNeven : Even N
      · rcases hNeven with ⟨a, ha⟩
        rcases hNS ⟨a, ha⟩ with ⟨b, hb⟩
        simp only [N, M, S, T] at hMN hNM hTS hST hMT ⊢
        omega
      · have hSeven : ¬ Even S := fun hs ↦ hNeven (hSN hs)
        rw [Nat.not_even_iff_odd] at hNeven hSeven
        rcases hNeven with ⟨a, ha⟩
        rcases hSeven with ⟨b, hb⟩
        simp only [N, M, S, T] at hMN hNM hTS hST hMT ⊢
        omega

/-- Taylor translation upgrades exact Descartes to an exact formula for the
number of roots on every strict right half-line. -/
theorem rootsGTCount_eq_signVariations_taylor
    {p : ℝ[X]} (hmonic : p.Monic) (hreal : RealRooted p) (x : ℝ) :
    rootsGTCount p x = (p.taylor x).signVariations := by
  rw [rootsGTCount_eq_taylor_roots_countP_pos hmonic hreal]
  apply roots_countP_pos_eq_signVariations
  · rw [Monic, leadingCoeff_taylor]
    exact hmonic
  · change (p.taylor x).Splits
    apply splits_iff_card_roots.mpr
    rw [roots_taylor_eq_map_sub hmonic hreal]
    simp [natDegree_taylor, hreal.natDegree_eq_card_roots]

end CommutatorTheorem.BTFellExactDescartes
