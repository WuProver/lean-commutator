import CommutatorTheorem.Epsilon.BTMDPRootShrinkAssembly
import CommutatorTheorem.Epsilon.BTMDPJointControl
import CommutatorTheorem.Epsilon.BTLeafSpectral

/-!
# Final exact-MDP assembly for Bourgain--Tzafriri

This file isolates the remaining analytic input in one proposition and proves
the complete finite-dimensional reduction from that input to the one-sided
four-Hermitian selection theorem and hence to the Bourgain--Tzafriri central
submatrix estimate.
-/

namespace CommutatorTheorem.BTMDPFinalAssembly

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
  Matrix.instL2OpNormedSpace Matrix.instL2OpNormedRing Matrix.instCStarRing

open scoped MatrixOrder Polynomial
open Polynomial Finset
open CommutatorTheorem
open CommutatorTheorem.BTMixedDet
open CommutatorTheorem.BTMDPSelection
open CommutatorTheorem.BTMDPDeletionIdentity
open CommutatorTheorem.BTMDPJointControl
open CommutatorTheorem.BTMDPRootShrinkAssembly

/-- The minimal global analytic package used by the exact-MDP route.

The quantifiers are restricted to the zero-diagonal Hermitian contractions
which occur in Bourgain--Tzafriri.  The determinant algebra, exact moments,
root shrinking, deletion identities, leaf selection, reindexing and spectral
consequences are all proved elsewhere and are not part of this input. -/
def BTMDPAnalyticCore : Prop :=
  MDPOneCoordinateZeroingMonotonicity ∧
  ∀ (n k : ℕ) (_hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (_hzd : ∀ a, ZeroDiag (A a))
    (_hnorm : ∀ a, ‖A a‖ ≤ 1),
      RealRooted (realMixedDeterminantalPolynomial A hA) ∧
      ∀ d : ℕ, 0 < d → d < n →
        MDPConditionalInterlacing (d := d) A hA

/-- The analytic core supplies exactly the common characteristic-polynomial
root selection needed by the four-Hermitian spectral bridge. -/
theorem fourHermitianCommonRootSelection24_of_mdpAnalyticCore
    (hcore : BTMDPAnalyticCore) : FourHermitianCommonRootSelection24 := by
  intro m M hzd hM hnorm t ht ht1
  let d : ℕ := ⌊(t ^ 2 / 24) * (m : ℝ)⌋₊
  change ∃ f : Fin d → Fin m, Function.Injective f ∧
    ∀ j : Fin 4,
      IsRootUpperBound
        (realCharpoly ((M j).submatrix f f) ((hM j).submatrix f)) t
  by_cases hd : 0 < d
  · have hm : 0 < m := by
      by_contra hm0
      have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
      subst m
      simp [d] at hd
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have harg0 : 0 ≤ (t ^ 2 / 24) * (m : ℝ) := by positivity
    have htSq : t ^ 2 < 1 := by nlinarith
    have hscaleLt : t ^ 2 / 24 < 1 := by nlinarith
    have hargLt : (t ^ 2 / 24) * (m : ℝ) < (m : ℝ) := by
      simpa only [one_mul] using
        (mul_lt_mul_of_pos_right hscaleLt hmR)
    have hdn : d < m := by
      dsimp [d]
      exact (Nat.floor_lt harg0).2 hargLt
    have hn : 2 ≤ m := by omega
    have hfloor : (d : ℝ) ≤ (t ^ 2 / 24) * (m : ℝ) := by
      dsimp [d]
      exact Nat.floor_le harg0
    have hfrac : (d : ℝ) / (m : ℝ) ≤
        t ^ 2 / (6 * (4 : ℝ)) := by
      apply (div_le_iff₀ hmR).2
      norm_num
      simpa only [div_eq_mul_inv, mul_assoc] using hfloor
    obtain ⟨hone, hanalytic⟩ := hcore
    have hmono : MDPJointRootMonotonicity :=
      mdpJointRootMonotonicity_of_oneCoordinate hone
    obtain ⟨hrooted, hconditional⟩ :=
      hanalytic m 4 (by norm_num) M hM hzd hnorm
    have hstable : MDPConditionalInterlacing (d := d) M hM :=
      hconditional d hd hdn
    obtain ⟨s, hscard, hsrootStrict⟩ :=
      exists_restrictedMDP_strictRootUpperBound
        hn (by norm_num) hd hdn ht ht1 hfrac M hM hzd hnorm
          hrooted hstable
    have hsroot : IsRootUpperBound (restrictedMDP M hM s) (t / 4) := by
      intro r hr
      exact (hsrootStrict r hr).le
    have hzdRestricted : ∀ j, ZeroDiag (restrictFamilyToFinset M s j) := by
      intro j i
      exact hzd j (s.orderEmbOfFin rfl i)
    have hjoint : ∀ j : Fin 4,
        IsRootUpperBound
          (realCharpoly (restrictFamilyToFinset M s j)
            (restrictFamilyToFinset_isHermitian hM s j))
          ((4 : ℝ) * (t / 4)) := by
      apply joint_realCharpoly_rootUpperBound_of_MDP hmono (by norm_num)
        (restrictFamilyToFinset M s)
        (restrictFamilyToFinset_isHermitian hM s)
        hzdRestricted
      simpa only [restrictedMDP] using hsroot
    let f : Fin d → Fin m := s.orderEmbOfFin hscard
    have hf : Function.Injective f := (s.orderEmbOfFin hscard).injective
    refine ⟨f, hf, ?_⟩
    intro j
    let e : Fin s.card ≃ Fin d := (Fin.castOrderIso hscard).toEquiv
    let B : Matrix (Fin s.card) (Fin s.card) ℂ :=
      restrictFamilyToFinset M s j
    let N : Matrix (Fin d) (Fin d) ℂ := (M j).submatrix f f
    let hB : B.IsHermitian := restrictFamilyToFinset_isHermitian hM s j
    let hN : N.IsHermitian := (hM j).submatrix f
    have hemb :
        (fun i : Fin d ↦
          s.orderEmbOfFin rfl ((Fin.castOrderIso hscard).symm i)) =
        s.orderEmbOfFin hscard := by
      apply Finset.orderEmbOfFin_unique hscard
      · intro i
        exact Finset.orderEmbOfFin_mem s rfl _
      · exact (s.orderEmbOfFin rfl).strictMono.comp
          (Fin.castOrderIso hscard).symm.strictMono
    have hBN : Matrix.reindex e e B = N := by
      ext i l
      change M j
          (s.orderEmbOfFin rfl ((Fin.castOrderIso hscard).symm i))
          (s.orderEmbOfFin rfl ((Fin.castOrderIso hscard).symm l)) =
        M j (s.orderEmbOfFin hscard i) (s.orderEmbOfFin hscard l)
      change M j
          ((fun x : Fin d ↦
            s.orderEmbOfFin rfl ((Fin.castOrderIso hscard).symm x)) i)
          ((fun x : Fin d ↦
            s.orderEmbOfFin rfl ((Fin.castOrderIso hscard).symm x)) l) = _
      rw [hemb]
    have hpoly : realCharpoly N hN = realCharpoly B hB :=
      realCharpoly_eq_of_reindex_eq e B N hB hN hBN
    have hBroot : IsRootUpperBound (realCharpoly B hB) t := by
      have hj := hjoint j
      have heq : (4 : ℝ) * (t / 4) = t := by ring
      rw [heq] at hj
      simpa [B, hB] using hj
    have hNroot : IsRootUpperBound (realCharpoly N hN) t := by
      rw [hpoly]
      exact hBroot
    simpa [N, hN] using hNroot
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    rw [hd0]
    let f : Fin 0 → Fin m := Fin.elim0
    refine ⟨f, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro j r hr
      rw [Polynomial.IsRoot] at hr
      simp [realCharpoly] at hr

/-- The exact-MDP analytic package implies the one-sided four-Hermitian
selection theorem with denominator `24`. -/
theorem fourHermitianUpperSelection24_of_mdpAnalyticCore
    (hcore : BTMDPAnalyticCore) : FourHermitianUpperSelection24 :=
  fourHermitianUpperSelection24_of_commonRootSelection
    (fourHermitianCommonRootSelection24_of_mdpAnalyticCore hcore)

/-- The resulting explicit Bourgain--Tzafriri central-submatrix estimate. -/
theorem bourgainTzafriri_of_mdpAnalyticCore
    (hcore : BTMDPAnalyticCore) :
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ (4 * Real.sqrt 6) * ε * ‖A‖ :=
  bourgainTzafriri_of_fourHermitianUpperSelection24
    (fourHermitianUpperSelection24_of_mdpAnalyticCore hcore)

/-- A theorem with the same existential interface as the repository's former
Bourgain--Tzafriri central-submatrix assumption, now derived from the explicit
analytic core. -/
theorem bourgain_tzafriri_central_submatrix_of_mdpAnalyticCore
    (hcore : BTMDPAnalyticCore) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
        ZeroDiag A →
        ∀ (ε : ℝ), 0 < ε → ε < 1 →
          ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
            Function.Injective f ∧
            ‖A.submatrix f f‖ ≤ K * ε * ‖A‖ := by
  refine ⟨4 * Real.sqrt 6, by positivity, ?_⟩
  exact bourgainTzafriri_of_mdpAnalyticCore hcore

end CommutatorTheorem.BTMDPFinalAssembly
