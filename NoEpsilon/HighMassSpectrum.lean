import NoEpsilon.HighMassGeometry
import NoEpsilon.HermitianSplit
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Spectral counting for the high trace-mass branch

The scalar count and dimension intersection are proved separately from numerical-range
geometry. This keeps the codimension cost explicit.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a zero-sum real family, half of its absolute mass is its positive mass. -/
theorem twice_sum_positive_eq_sum_abs (f : ι → ℝ) (hf : ∑ i, f i = 0) :
    2 * (∑ i, max (f i) 0) = ∑ i, |f i| := by
  have hpoint (i : ι) : 2 * max (f i) 0 = |f i| + f i := by
    by_cases hi : 0 ≤ f i
    · rw [max_eq_left hi, abs_of_nonneg hi]
      ring
    · rw [max_eq_right (le_of_not_ge hi), abs_of_neg (lt_of_not_ge hi)]
      ring
  rw [Finset.mul_sum]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, hf, add_zero]

/-- Positive trace mass forces a proportionate number of eigenvalues above `t / 4`.
The conclusion is strict, so it can be paired directly with a codimension upper bound. -/
theorem high_mass_many_large_coordinates [Nonempty ι] (f : ι → ℝ) (t : ℝ)
    (ht : 0 < t) (hBound : ∀ i, f i ≤ 1) (hTrace : ∑ i, f i = 0)
    (hMass : t * Fintype.card ι ≤ ∑ i, |f i|) :
    t * Fintype.card ι / 4 <
      ((Finset.univ.filter (fun i ↦ t / 4 ≤ f i)).card : ℝ) := by
  classical
  have hPos := twice_sum_positive_eq_sum_abs f hTrace
  have hpoint (i : ι) : max (f i) 0 <
      (if t / 4 ≤ f i then (1 : ℝ) else 0) + t / 4 := by
    split_ifs with hi
    · have hm : max (f i) 0 ≤ 1 := max_le (hBound i) (by norm_num)
      linarith
    · have hfi : f i < t / 4 := lt_of_not_ge hi
      simpa only [zero_add] using max_lt hfi (by linarith : (0 : ℝ) < t / 4)
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hSum := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) ↦ (hpoint j).le)
    ⟨i, Finset.mem_univ i, hpoint i⟩
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hSum
  nlinarith

/-- More coordinate directions than the codimension of a subspace leave a nonzero
vector supported in those directions inside the subspace. -/
theorem exists_supported_nonzero_in_submodule (W : Submodule ℂ (ι → ℂ)) (s : Finset ι)
    (hDim : Fintype.card ι < Module.finrank ℂ W + s.card) :
    ∃ v : ι → ℂ, v ∈ W ∧ v ≠ 0 ∧ ∀ i ∉ s, v i = 0 := by
  classical
  let E : Submodule ℂ (ι → ℂ) := Pi.spanSubset ℂ (s : Set ι)
  have hE : Module.finrank ℂ E = s.card := by simp [E]
  by_contra hNone
  have hDisjoint : Disjoint W E := by
    apply Submodule.disjoint_def.mpr
    intro v hvW hvE
    by_contra hv
    apply hNone
    exact ⟨v, hvW, hv, Pi.mem_spanSubset_iff.mp hvE⟩
  have hLe := Submodule.finrank_add_finrank_le_of_disjoint hDisjoint
  rw [hE, Module.finrank_pi] at hLe
  simpa using (not_lt_of_ge hLe) hDim

/-- The dimension intersection can be normalized without changing support or subspace. -/
theorem exists_supported_unit_in_submodule (W : Submodule ℂ (ι → ℂ)) (s : Finset ι)
    (hDim : Fintype.card ι < Module.finrank ℂ W + s.card) :
    ∃ v : ι → ℂ, v ∈ W ∧ vectorEnergy v = 1 ∧ ∀ i ∉ s, v i = 0 := by
  obtain ⟨v, hvW, hv, hSupport⟩ := exists_supported_nonzero_in_submodule W s hDim
  let a : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖
  have ha : 0 < a := norm_pos_iff.mpr (by
    intro hz
    exact hv ((WithLp.toLp_eq_zero 2).mp hz))
  have haE : vectorEnergy v = a ^ 2 := vectorEnergy_eq_norm_sq v
  let c : ℂ := (a⁻¹ : ℝ)
  have hc : Complex.normSq c = (a ^ 2)⁻¹ := by
    simp [c, Complex.normSq_ofReal, pow_two]
  refine ⟨c • v, W.smul_mem c hvW, ?_, ?_⟩
  · rw [vectorEnergy_smul, hc, haE, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne')]
  · intro i hi
    simp only [Pi.smul_apply, hSupport i hi, smul_zero]

/-- A low-codimension subspace retains a large direction for any diagonal zero-trace
Hermitian form with high absolute spectral mass. -/
theorem exists_large_diagonal_rayleigh_in_submodule [Nonempty ι]
    (f : ι → ℝ) (W : Submodule ℂ (ι → ℂ)) (t : ℝ) (ht : 0 < t)
    (hBound : ∀ i, f i ≤ 1) (hTrace : ∑ i, f i = 0)
    (hMass : t * Fintype.card ι ≤ ∑ i, |f i|)
    (hCodim : (Fintype.card ι : ℝ) - Module.finrank ℂ W ≤ t * Fintype.card ι / 4) :
    ∃ v : ι → ℂ, v ∈ W ∧ vectorEnergy v = 1 ∧
      t / 4 ≤ ∑ i, f i * Complex.normSq (v i) := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i ↦ t / 4 ≤ f i)
  have hMany : t * Fintype.card ι / 4 < (s.card : ℝ) :=
    high_mass_many_large_coordinates f t ht hBound hTrace hMass
  have hDim : Fintype.card ι < Module.finrank ℂ W + s.card := by
    have hDimR : (Fintype.card ι : ℝ) < Module.finrank ℂ W + s.card := by linarith
    exact_mod_cast hDimR
  obtain ⟨v, hvW, hvUnit, hSupport⟩ := exists_supported_unit_in_submodule W s hDim
  refine ⟨v, hvW, hvUnit, ?_⟩
  calc
    t / 4 = t / 4 * vectorEnergy v := by rw [hvUnit, mul_one]
    _ = ∑ i, t / 4 * Complex.normSq (v i) := Finset.mul_sum ..
    _ ≤ ∑ i, f i * Complex.normSq (v i) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ s
      · exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hi).2
          (Complex.normSq_nonneg _)
      · simp only [hSupport i hi, map_zero, mul_zero, le_refl]

/-- Unitary coordinates as a linear equivalence on ordinary coordinate functions. -/
def unitaryCoordinateEquiv (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
  LinearEquiv.ofLinear U.mulVecLin Uᴴ.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, hU, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, hU', Matrix.mulVecLin_one])

/-- Left multiplication by a unitary matrix preserves Euclidean vector energy. -/
theorem vectorEnergy_unitary_mulVec (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (v : ι → ℂ) :
    vectorEnergy (U *ᵥ v) = vectorEnergy v := by
  let X : Matrix ι Unit ℂ := fun i _ ↦ v i
  have hGram : (U * X)ᴴ * (U * X) = Xᴴ * X := by
    calc
      _ = Xᴴ * (Uᴴ * U) * X := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Xᴴ * X := by rw [hU, Matrix.mul_one]
  have h := congrArg (fun M : Matrix Unit Unit ℂ ↦ (Matrix.trace M).re) hGram
  simp only [gram_trace_re, Fintype.sum_unique] at h
  exact h

/-- Numerical-range values are invariant under a simultaneous unitary change of coordinates. -/
theorem rayleighValue_unitary_conjugate (U H : Matrix ι ι ℂ)
    (hU : Uᴴ * U = 1) (v : ι → ℂ) :
    rayleighValue (U * H * Uᴴ) (U *ᵥ v) = rayleighValue H v := by
  let X : Matrix ι Unit ℂ := fun i _ ↦ v i
  have hGram : (U * X)ᴴ * (U * H * Uᴴ) * (U * X) = Xᴴ * H * X := by
    calc
      _ = Xᴴ * (Uᴴ * U) * H * (Uᴴ * U) * X := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Xᴴ * H * X := by rw [hU, Matrix.mul_one, Matrix.mul_one]
  have h := congrArg (fun M : Matrix Unit Unit ℂ ↦ M () ()) hGram
  simpa only [gram_diagonal] using h

/-- The Rayleigh value of a real diagonal matrix is its weighted coordinate energy. -/
theorem rayleighValue_real_diagonal_re (f : ι → ℝ) (v : ι → ℂ) :
    (rayleighValue (Matrix.diagonal (fun i ↦ (f i : ℂ))) v).re =
      ∑ i, f i * Complex.normSq (v i) := by
  have h : rayleighValue (Matrix.diagonal (fun i ↦ (f i : ℂ))) v =
      ∑ i, (f i : ℂ) * (Complex.normSq (v i) : ℂ) := by
    simp only [rayleighValue, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  rw [h]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]

/-- Spectral values of a Hermitian matrix are bounded by its Euclidean operator norm. -/
theorem abs_hermitian_eigenvalue_le_opNorm (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (i : ι) : |hH.eigenvalues i| ≤ ‖H‖ := by
  have hDiag : ‖Matrix.diagonal (fun j ↦ (hH.eigenvalues j : ℂ))‖ = ‖H‖ := by
    change ‖Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)‖ = ‖H‖
    rw [← hH.conjStarAlgAut_star_eigenvectorUnitary, Unitary.conjStarAlgAut_apply]
    change ‖((star hH.eigenvectorUnitary : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) * H *
      (star (star hH.eigenvectorUnitary) : Matrix.unitaryGroup ι ℂ)‖ = ‖H‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  calc
    |hH.eigenvalues i| = ‖(hH.eigenvalues i : ℂ)‖ := by simp
    _ ≤ ‖fun j ↦ (hH.eigenvalues j : ℂ)‖ := norm_le_pi_norm (fun j : ι ↦ (hH.eigenvalues j : ℂ)) i
    _ = ‖Matrix.diagonal (fun j ↦ (hH.eigenvalues j : ℂ))‖ :=
      (Matrix.l2_opNorm_diagonal _).symm
    _ = ‖H‖ := hDiag

/-- A Hermitian contraction with zero trace and high absolute spectral mass retains a
Rayleigh value at least `t / 4` in every subspace of codimension at most `t n / 4`. -/
theorem exists_large_hermitian_rayleigh_in_submodule [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (W : Submodule ℂ (ι → ℂ))
    (t : ℝ) (ht : 0 < t) (hNorm : ‖H‖ ≤ 1) (hTrace : Matrix.trace H = 0)
    (hMass : t * Fintype.card ι ≤ ∑ i, |hH.eigenvalues i|)
    (hCodim : (Fintype.card ι : ℝ) - Module.finrank ℂ W ≤ t * Fintype.card ι / 4) :
    ∃ v : ι → ℂ, v ∈ W ∧ vectorEnergy v = 1 ∧ t / 4 ≤ (rayleighValue H v).re := by
  let U : Matrix ι ι ℂ := hH.eigenvectorUnitary
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hU' : Uᴴ * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  let e := unitaryCoordinateEquiv U hU hU'
  let W' := W.comap e.toLinearMap
  have hDim : Module.finrank ℂ W' = Module.finrank ℂ W := by
    have hW' : W' = W.map e.symm.toLinearMap :=
      Submodule.comap_equiv_eq_map_symm e W
    exact (congrArg (fun S : Submodule ℂ (ι → ℂ) ↦ Module.finrank ℂ S) hW').trans
      (e.symm.finrank_map_eq W)
  have hBound (i : ι) : hH.eigenvalues i ≤ 1 :=
    (le_abs_self _).trans ((abs_hermitian_eigenvalue_le_opNorm H hH i).trans hNorm)
  have hSum : ∑ i, hH.eigenvalues i = 0 := by
    have h := congrArg Complex.re (hH.trace_eq_sum_eigenvalues.symm.trans hTrace)
    simpa using h
  have hCodim' : (Fintype.card ι : ℝ) - Module.finrank ℂ W' ≤
      t * Fintype.card ι / 4 := by rwa [hDim]
  obtain ⟨v, hvW, hvUnit, hvLarge⟩ :=
    exists_large_diagonal_rayleigh_in_submodule hH.eigenvalues W' t ht
      hBound hSum hMass hCodim'
  refine ⟨U *ᵥ v, hvW, ?_, ?_⟩
  · rwa [vectorEnergy_unitary_mulVec U hU']
  · have hSpectral : H = U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * Uᴴ := by
      simpa only [Unitary.conjStarAlgAut_apply] using hH.spectral_theorem
    rw [hSpectral, rayleighValue_unitary_conjugate U _ hU',
      rayleighValue_real_diagonal_re]
    exact hvLarge

end NoEpsilon
