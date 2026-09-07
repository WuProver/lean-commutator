import KadisonSinger.VectorPartition
import KadisonSinger.WeaverConstants

/-!
# Weaver's two-colour discrepancy theorem

The constants `η = 18` and `θ = 2` follow from the MSS vector partition
bound. The covariance and energy hypotheses are the matrix form of
Conjecture 1.2 in Marcus--Spielman--Srivastava (2015).
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace KadisonSinger

open NoEpsilon.MSSSelection NoEpsilon.MSSPadding

/-- Weaver's KS₂ with the universal constants `η = 18` and `θ = 2`.
The input and both parts are measured in the Euclidean operator norm. -/
theorem weaver_ks2 {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (w : κ → ι → ℂ)
    (hsum : (∑ i, Matrix.vecMulVec (w i) (star (w i))) = (18 : ℝ) • 1)
    (henergy : ∀ i, energy (w i) ≤ 1) :
    ∃ c : κ → Fin 2, ∀ j,
      ‖∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (w i) (star (w i))‖ ≤ 16 := by
  classical
  let u : κ → ι → ℂ := fun i a ↦ ((1 / Real.sqrt 18 : ℝ) : ℂ) * w i a
  have hscale : (1 / Real.sqrt (18 : ℝ)) ^ 2 = 1 / 18 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hout (i : κ) : outer (u i) = (1 / 18 : ℝ) • outer (w i) := by
    dsimp [u]
    rw [outer_real_mul, hscale]
  have htotal : (∑ i, Matrix.vecMulVec (u i) (star (u i))) = 1 := by
    change (∑ i, outer (u i)) = 1
    simp_rw [hout]
    rw [← Finset.smul_sum]
    change (1 / 18 : ℝ) • (∑ i, Matrix.vecMulVec (w i) (star (w i))) = 1
    rw [hsum, smul_smul]
    norm_num
  have hen (i : κ) : energy (u i) ≤ 1 / 18 := by
    dsimp [u]
    rw [energy_real_mul, hscale]
    have hi := henergy i
    linarith
  obtain ⟨c, hc⟩ := vector_partition 2 (by decide) u htotal (1 / 18) (by norm_num) hen
  refine ⟨c, fun j ↦ ?_⟩
  have hj := hc j
  change ‖∑ i ∈ Finset.univ.filter (fun i ↦ c i = j), outer (u i)‖ ≤ _ at hj
  simp_rw [hout] at hj
  rw [← Finset.smul_sum] at hj
  have hsmul (B : Matrix ι ι ℂ) : (1 / 18 : ℝ) • B = (1 / 18 : ℂ) • B := by
    ext a b
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [hsmul] at hj
  rw [norm_smul] at hj
  norm_num at hj
  have heq := weaver_bound_eq
  norm_num at heq
  change ‖∑ i ∈ Finset.univ.filter (fun i ↦ c i = j), outer (w i)‖ ≤ 16
  nlinarith

end KadisonSinger
