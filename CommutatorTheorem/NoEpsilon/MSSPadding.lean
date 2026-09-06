import CommutatorTheorem.NoEpsilon.MSSSelection
import CommutatorTheorem.NoEpsilon.MSSFinite
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Deterministic small-energy padding of a positive covariance deficit

Every finite positive semidefinite matrix is exactly a finite sum of vector outer
products of arbitrarily small prescribed positive energy. This is the genuine
padding existence step needed to pass from covariance equality to inequality in MSS.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace NoEpsilon.MSSPadding

open NoEpsilon.MSSSelection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma energy_nonneg (v : ι → ℂ) : 0 ≤ energy v :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma outer_real_mul (c : ℝ) (v : ι → ℂ) :
    outer (fun i ↦ (c : ℂ) * v i) = (c ^ 2 : ℝ) • outer v := by
  ext i j
  simp [outer, star_mul, pow_two, mul_assoc, mul_left_comm, mul_comm]

lemma energy_real_mul (c : ℝ) (v : ι → ℂ) :
    energy (fun i ↦ (c : ℂ) * v i) = c ^ 2 * energy v := by
  simp only [energy, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Finset.mul_sum]

lemma sum_outer_columns (S : Matrix ι ι ℂ) :
    (∑ j, outer (fun i ↦ S i j)) = S * Sᴴ := by
  ext i j
  simp [Matrix.sum_apply, outer, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma exists_outer_decomposition (D : Matrix ι ι ℂ) (hD : D.PosSemidef) :
    ∃ v : ι → ι → ℂ, ∑ j, outer (v j) = D := by
  obtain ⟨S, hS, -, hSq⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hD.isHermitian
      (QuasispectrumRestricts.nnreal_of_nonneg hD.nonneg)
  refine ⟨fun j i ↦ S i j, ?_⟩
  rw [sum_outer_columns]
  change S * star S = D
  rw [hS.star_eq, hSq]

lemma energy_le_total (v : ι → ι → ℂ) (j : ι) :
    energy (v j) ≤ ∑ k, energy (v k) :=
  Finset.single_le_sum (fun k _ ↦ energy_nonneg (v k)) (Finset.mem_univ j)

/-- Repeat and rescale each vector to make every energy at most `ε`, retaining
exactly the same covariance sum. The index type is explicitly finite. -/
theorem exists_small_energy_decomposition (D : Matrix ι ι ℂ)
    (hD : D.PosSemidef) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∃ v : ι × Fin K → ι → ℂ,
      (∑ j, outer (v j)) = D ∧ ∀ j, energy (v j) ≤ ε := by
  obtain ⟨w, hw⟩ := exists_outer_decomposition D hD
  let E : ℝ := ∑ j, energy (w j)
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ ↦ energy_nonneg _
  obtain ⟨K, hK⟩ := exists_nat_gt (E / ε)
  have hKreal : 0 < (K : ℝ) := lt_of_le_of_lt (div_nonneg hE hε.le) hK
  have hKnat : 0 < K := by exact_mod_cast hKreal
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKreal
  have hscale : (1 / Real.sqrt (K : ℝ)) ^ 2 = 1 / (K : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hKreal.le]
  let v : ι × Fin K → ι → ℂ := fun j i ↦
    ((1 / Real.sqrt (K : ℝ) : ℝ) : ℂ) * w j.1 i
  refine ⟨K, hKnat, v, ?_, ?_⟩
  · change (∑ j : ι × Fin K, outer (fun i ↦
      ((1 / Real.sqrt (K : ℝ) : ℝ) : ℂ) * w j.1 i)) = D
    simp only [outer_real_mul, hscale, Fintype.sum_prod_type]
    convert hw using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [hKne]
  · intro j
    change energy (fun i ↦ ((1 / Real.sqrt (K : ℝ) : ℝ) : ℂ) * w j.1 i) ≤ ε
    rw [energy_real_mul, hscale, one_div_mul_eq_div]
    apply (div_le_iff₀ hKreal).2
    have hEK : E < ε * K := by
      have := (div_lt_iff₀ hε).1 hK
      nlinarith
    exact (energy_le_total w j.1).trans hEK.le

open scoped Matrix.Norms.L2Operator

/-- Discarding a positive summand can only decrease the Euclidean operator norm. -/
theorem norm_le_norm_add_of_posSemidef (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : ‖A‖ ≤ ‖A + B‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := {}
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le hA.nonneg
    (le_add_of_nonneg_right hB.nonneg)

/-- The finite MSS theorem for total covariance at most the identity. Deterministic
padding is constructed here and then removed by positive operator monotonicity. -/
theorem finite_mss_le {κ Ω : Type*} [Fintype κ] [Fintype Ω]
    (v : κ → Ω → ι → ℂ) (p : κ → Ω → ℝ)
    (hp : ∀ i ω, 0 ≤ p i ω) (hsum : ∀ i, ∑ ω, p i ω = 1)
    (hdef : (1 - ∑ i, ∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))).PosSemidef)
    (ε : ℝ) (hε : 0 < ε)
    (henergy : ∀ i, ∑ ω, p i ω * energy (v i ω) ≤ ε) :
    ∃ q : κ → Ω,
      ‖∑ i, Matrix.vecMulVec (v i (q i)) (star (v i (q i)))‖ ≤
        (1 + Real.sqrt ε)^2 := by
  classical
  cases isEmpty_or_nonempty κ with
  | inl he =>
    haveI : IsEmpty κ := he
    refine ⟨isEmptyElim, ?_⟩
    simpa using sq_nonneg (1 + Real.sqrt ε)
  | inr hn =>
    haveI : Nonempty κ := hn
    let i₀ : κ := Classical.choice hn
    let A : Matrix ι ι ℂ := ∑ i, ∑ ω, (p i ω : ℂ) •
      Matrix.vecMulVec (v i ω) (star (v i ω))
    obtain ⟨K, -, w, hw, hwε⟩ := exists_small_energy_decomposition (1 - A) hdef ε hε
    let v' : (κ ⊕ (ι × Fin K)) → Ω → ι → ℂ :=
      Sum.elim v (fun j _ ↦ w j)
    let p' : (κ ⊕ (ι × Fin K)) → Ω → ℝ :=
      Sum.elim p (fun _ ↦ p i₀)
    have hp' : ∀ i ω, 0 ≤ p' i ω := by
      intro i ω
      cases i with
      | inl i => exact hp i ω
      | inr j => exact hp i₀ ω
    have hsum' : ∀ i, ∑ ω, p' i ω = 1 := by
      intro i
      cases i with
      | inl i => exact hsum i
      | inr j => exact hsum i₀
    have hconst (j : ι × Fin K) :
        (∑ ω, (p i₀ ω : ℂ) • Matrix.vecMulVec (w j) (star (w j))) = outer (w j) := by
      rw [← Finset.sum_smul, ← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_smul]
      rfl
    have hTotal : (∑ i, ∑ ω, (p' i ω : ℂ) •
        Matrix.vecMulVec (v' i ω) (star (v' i ω))) = 1 := by
      rw [Fintype.sum_sum_type]
      change A + (∑ j, ∑ ω, (p i₀ ω : ℂ) •
        Matrix.vecMulVec (w j) (star (w j))) = 1
      simp_rw [hconst]
      rw [hw, add_sub_cancel]
    have henergy' : ∀ i, ∑ ω, p' i ω * energy (v' i ω) ≤ ε := by
      intro i
      cases i with
      | inl i => exact henergy i
      | inr j =>
        change (∑ ω, p i₀ ω * energy (w j)) ≤ ε
        rw [← Finset.sum_mul, hsum, one_mul]
        exact hwε j
    obtain ⟨q, hq⟩ := MSSFinite.finite_mss v' p' hp' hsum' hTotal ε hε henergy'
    refine ⟨fun i ↦ q (.inl i), ?_⟩
    have hq' : ‖(∑ i, outer (v i (q (.inl i)))) + ∑ j, outer (w j)‖ ≤
        (1 + Real.sqrt ε)^2 := by
      simpa only [Fintype.sum_sum_type, v', Sum.elim_inl, Sum.elim_inr] using hq
    apply le_trans (norm_le_norm_add_of_posSemidef _ _ ?_ ?_) hq'
    · exact Matrix.posSemidef_sum _ fun i _ ↦ outer_posSemidef _
    · exact Matrix.posSemidef_sum _ fun i _ ↦ outer_posSemidef _

end NoEpsilon.MSSPadding
