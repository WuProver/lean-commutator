import NoEpsilon.MSSPadding
import NoEpsilon.MSSFinite

/-!
# Scaling and zero-parameter closure for finite MSS

The covariance norm bound is arbitrary. The closure argument chooses a minimizing
outcome in the finite outcome set, so the same result survives the limits at zero
covariance or zero expected energy.
-/

namespace NoEpsilon.MSSScaled

open NoEpsilon.MSSSelection NoEpsilon.MSSPadding
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype Ω]

/-- The whole weighted covariance scales by the square of the real vector scale. -/
theorem mean_outer_real_mul (v : κ → Ω → ι → ℂ) (p : κ → Ω → ℝ) (c : ℝ) :
    (∑ i, ∑ ω, (p i ω : ℂ) • outer (fun j ↦ (c : ℂ) * v i ω j)) =
      c ^ 2 • ∑ i, ∑ ω, (p i ω : ℂ) • outer (v i ω) := by
  simp only [outer_real_mul, smul_comm (p _ _ : ℂ) (c ^ 2), Finset.smul_sum]

/-- Positive-parameter scaling of the unit-covariance-inequality MSS theorem. -/
theorem finite_mss_scaled_pos (v : κ → Ω → ι → ℂ) (p : κ → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1)
    (L ε : ℝ) (hL : 0 < L) (hε : 0 < ε)
    (hCov : ‖∑ i, ∑ ω, (p i ω : ℂ) • outer (v i ω)‖ ≤ L)
    (henergy : ∀ i, ∑ ω, p i ω * energy (v i ω) ≤ ε) :
    ∃ q : κ → Ω, ‖∑ i, outer (v i (q i))‖ ≤ (Real.sqrt L + Real.sqrt ε)^2 := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := {}
  let c : ℝ := (Real.sqrt L)⁻¹
  let v' : κ → Ω → ι → ℂ := fun i ω j ↦ (c : ℂ) * v i ω j
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hL)
  have hcsq : c ^ 2 = L⁻¹ := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hL.le]
  have hmean : (∑ i, ∑ ω, (p i ω : ℂ) • outer (v' i ω)) =
      L⁻¹ • ∑ i, ∑ ω, (p i ω : ℂ) • outer (v i ω) := by
    simpa only [v', hcsq] using mean_outer_real_mul v p c
  have hPSD : (∑ i, ∑ ω, (p i ω : ℂ) • outer (v' i ω)).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    apply Matrix.posSemidef_sum
    intro ω _
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul
      (show (0 : ℂ) ≤ (p i ω : ℂ) from by exact_mod_cast hp i ω)
  have hnorm : ‖∑ i, ∑ ω, (p i ω : ℂ) • outer (v' i ω)‖ ≤ 1 := by
    rw [hmean, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    calc
      L⁻¹ * ‖∑ i, ∑ ω, (p i ω : ℂ) • outer (v i ω)‖ ≤ L⁻¹ * L := by
        gcongr
      _ = 1 := inv_mul_cancel₀ hL.ne'
  have hdef : (1 - ∑ i, ∑ ω, (p i ω : ℂ) • outer (v' i ω)).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    exact sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hPSD.nonneg).mp hnorm)
  have henergy' : ∀ i, ∑ ω, p i ω * energy (v' i ω) ≤ ε / L := by
    intro i
    simp only [v', energy_real_mul, hcsq]
    calc
      (∑ ω, p i ω * (L⁻¹ * energy (v i ω))) =
          L⁻¹ * ∑ ω, p i ω * energy (v i ω) := by rw [Finset.mul_sum]; congr 1; ext; ring
      _ ≤ L⁻¹ * ε := by gcongr; exact henergy i
      _ = ε / L := by ring
  obtain ⟨q, hq⟩ := finite_mss_le v' p hp hsum hdef (ε / L) (div_pos hε hL) henergy'
  change ‖∑ i, outer (v' i (q i))‖ ≤ (1 + Real.sqrt (ε / L))^2 at hq
  have hselected : (∑ i, outer (v' i (q i))) = L⁻¹ • ∑ i, outer (v i (q i)) := by
    simp only [v', outer_real_mul, hcsq, Finset.smul_sum]
  rw [hselected, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] at hq
  have hbound : ‖∑ i, outer (v i (q i))‖ ≤ L * (1 + Real.sqrt (ε / L))^2 := by
    calc
      ‖∑ i, outer (v i (q i))‖ = L * (L⁻¹ * ‖∑ i, outer (v i (q i))‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
      _ ≤ L * (1 + Real.sqrt (ε / L))^2 := mul_le_mul_of_nonneg_left hq hL.le
  refine ⟨q, hbound.trans_eq ?_⟩
  rw [Real.sqrt_div hε.le]
  have hs := Real.sq_sqrt hL.le
  have hn := (Real.sqrt_pos.mpr hL).ne'
  calc
    L * (1 + Real.sqrt ε / Real.sqrt L)^2 =
        (Real.sqrt L * (1 + Real.sqrt ε / Real.sqrt L))^2 := by rw [mul_pow, hs]
    _ = (Real.sqrt L + Real.sqrt ε)^2 := by
      congr 1
      field_simp

/-- The scaled finite MSS estimate, including both zero-parameter cases. -/
theorem finite_mss_scaled (v : κ → Ω → ι → ℂ) (p : κ → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1)
    (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hCov : ‖∑ i, ∑ ω, (p i ω : ℂ) • outer (v i ω)‖ ≤ L)
    (henergy : ∀ i, ∑ ω, p i ω * energy (v i ω) ≤ ε) :
    ∃ q : κ → Ω, ‖∑ i, outer (v i (q i))‖ ≤ (Real.sqrt L + Real.sqrt ε)^2 := by
  classical
  have hΩ (i : κ) : Nonempty Ω := by
    by_contra hn
    haveI : IsEmpty Ω := not_nonempty_iff.mp hn
    have hi := hsum i
    simp at hi
  haveI : Nonempty (κ → Ω) := ⟨fun i ↦ Classical.choice (hΩ i)⟩
  let cost : (κ → Ω) → ℝ := fun q ↦ ‖∑ i, outer (v i (q i))‖
  obtain ⟨q, _, hq⟩ := Finset.exists_min_image Finset.univ cost Finset.univ_nonempty
  refine ⟨q, ?_⟩
  have happrox (η : ℝ) (hη : 0 < η) :
      cost q ≤ (Real.sqrt (L + η) + Real.sqrt (ε + η))^2 := by
    obtain ⟨r, hr⟩ := finite_mss_scaled_pos v p hp hsum (L + η) (ε + η)
      (by linarith) (by linarith) (by linarith) (fun i ↦ (henergy i).trans (by linarith))
    exact (hq r (Finset.mem_univ r)).trans hr
  have ht : Filter.Tendsto
      (fun η : ℝ ↦ (Real.sqrt (L + η) + Real.sqrt (ε + η))^2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Real.sqrt L + Real.sqrt ε)^2)) := by
    have hc : Continuous (fun η : ℝ ↦ (Real.sqrt (L + η) + Real.sqrt (ε + η))^2) := by
      fun_prop
    simpa using (hc.tendsto 0).mono_left
      (nhdsWithin_le_nhds : nhdsWithin 0 (Set.Ioi 0) ≤ nhds (0 : ℝ))
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact happrox η hη

end NoEpsilon.MSSScaled
