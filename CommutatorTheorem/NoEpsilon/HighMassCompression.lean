import CommutatorTheorem.NoEpsilon.HighMassSpectrum
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Numerical-range disks in low-codimension compressions

High trace mass is imposed on every unit complex rotation of the Hermitian real part.
The norm used for matrices is the Euclidean operator norm.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Numerical-range values commute with rectangular compression. -/
theorem rayleighValue_compression (A : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (v : κ → ℂ) :
    rayleighValue (Vᴴ * A * V) v = rayleighValue A (V *ᵥ v) := by
  let X : Matrix κ Unit ℂ := fun i _ ↦ v i
  have hGram : Xᴴ * (Vᴴ * A * V) * X = (V * X)ᴴ * A * (V * X) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h := congrArg (fun M : Matrix Unit Unit ℂ ↦ M () ()) hGram
  simpa only [gram_diagonal] using h

/-- A rectangular isometry preserves Euclidean energy. -/
theorem vectorEnergy_isometry_mulVec (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) (v : κ → ℂ) :
    vectorEnergy (V *ᵥ v) = vectorEnergy v := by
  have h := rayleighValue_compression (1 : Matrix ι ι ℂ) V v
  rw [Matrix.mul_one, hV, rayleighValue_one, rayleighValue_one] at h
  exact_mod_cast h.symm

omit [Fintype κ] [DecidableEq κ] in
theorem rayleighValue_adjoint (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    rayleighValue Aᴴ v = star (rayleighValue A v) := by
  let X : Matrix ι Unit ℂ := fun i _ ↦ v i
  have hGram : Xᴴ * Aᴴ * X = (Xᴴ * A * X)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have h := congrArg (fun M : Matrix Unit Unit ℂ ↦ M () ()) hGram
  simpa only [gram_diagonal, Matrix.conjTranspose_apply] using h

omit [Fintype κ] [DecidableEq κ] in
theorem rayleighValue_smul_matrix (A : Matrix ι ι ℂ) (c : ℂ) (v : ι → ℂ) :
    rayleighValue (c • A) v = c * rayleighValue A v := by
  simp only [rayleighValue, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

omit [Fintype κ] [DecidableEq κ] in
set_option backward.isDefEq.respectTransparency false in
theorem rayleighValue_hermitianRealPart_re (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    (rayleighValue (hermitianRealPart A) v).re = (rayleighValue A v).re := by
  have hAdj := rayleighValue_adjoint A v
  simp only [hermitianRealPart, realPart_apply_coe, Matrix.star_eq_conjTranspose,
    rayleighValue, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul,
    dotProduct_add] at ⊢ hAdj
  rw [hAdj]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.star_def, Complex.conj_re, zero_mul, sub_zero]
  ring

/-- The high-mass condition uses the absolute eigenvalue sum of each Hermitian rotation. -/
def HasHighTraceMass (A : Matrix ι ι ℂ) (t : ℝ) : Prop :=
  ∀ c : ℂ, ‖c‖ = 1 → t * Fintype.card ι ≤
    ∑ i, |(hermitianRealPart_isHermitian (c • A)).eigenvalues i|

omit [Fintype κ] [DecidableEq κ] in
/-- Every unit rotation has a large numerical-range support value on a low-codimension
subspace. All hypotheses refer to the original matrix. -/
theorem exists_subspace_rotation_support [Nonempty ι]
    (A : Matrix ι ι ℂ) (W : Submodule ℂ (ι → ℂ)) (t : ℝ) (ht : 0 < t)
    (hNorm : ‖A‖ ≤ 1) (hTrace : Matrix.trace A = 0) (hMass : HasHighTraceMass A t)
    (hCodim : (Fintype.card ι : ℝ) - Module.finrank ℂ W ≤ t * Fintype.card ι / 4)
    (c : ℂ) (hc : ‖c‖ = 1) :
    ∃ v : ι → ℂ, v ∈ W ∧ vectorEnergy v = 1 ∧
      t / 4 ≤ (c * rayleighValue A v).re := by
  have hHNorm : ‖hermitianRealPart (c • A)‖ ≤ 1 := by
    calc
      _ ≤ ‖c • A‖ := hermitianRealPart_norm_le _
      _ = ‖A‖ := by rw [norm_smul, hc, one_mul]
      _ ≤ 1 := hNorm
  have hHTrace : Matrix.trace (hermitianRealPart (c • A)) = 0 :=
    hermitianRealPart_trace_zero _ (by rw [Matrix.trace_smul, hTrace, smul_zero])
  obtain ⟨v, hvW, hvUnit, hvLarge⟩ := exists_large_hermitian_rayleigh_in_submodule
    (hermitianRealPart (c • A)) (hermitianRealPart_isHermitian _) W t ht
      hHNorm hHTrace (hMass c hc) hCodim
  refine ⟨v, hvW, hvUnit, ?_⟩
  rwa [rayleighValue_hermitianRealPart_re, rayleighValue_smul_matrix] at hvLarge

omit [Fintype κ] [DecidableEq κ] in
set_option backward.isDefEq.respectTransparency false in
/-- Rotation support is equivalent to the real-dual support required by separation. -/
theorem exists_subspace_dual_support [Nonempty ι]
    (A : Matrix ι ι ℂ) (W : Submodule ℂ (ι → ℂ)) (t : ℝ) (ht : 0 < t)
    (hNorm : ‖A‖ ≤ 1) (hTrace : Matrix.trace A = 0) (hMass : HasHighTraceMass A t)
    (hCodim : (Fintype.card ι : ℝ) - Module.finrank ℂ W ≤ t * Fintype.card ι / 4)
    (f : ℂ →L[ℝ] ℝ) :
    ∃ v : ι → ℂ, v ∈ W ∧ vectorEnergy v = 1 ∧
      t / 4 * ‖f‖ ≤ f (rayleighValue A v) := by
  by_cases hf : f = 0
  · obtain ⟨v, hvW, hvUnit, _⟩ := exists_subspace_rotation_support A W t ht
      hNorm hTrace hMass hCodim 1 (by simp)
    exact ⟨v, hvW, hvUnit, by simp [hf]⟩
  let w : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm f
  have hwNorm : ‖w‖ = ‖f‖ := (InnerProductSpace.toDual ℝ ℂ).symm.norm_map f
  have hw : w ≠ 0 := by
    intro hwZero
    have hfNorm : ‖f‖ = 0 := by rw [← hwNorm, hwZero, norm_zero]
    exact hf (norm_eq_zero.mp hfNorm)
  let c : ℂ := conj w / (‖w‖ : ℂ)
  have hc : ‖c‖ = 1 := by
    simp only [c, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg w), div_self (norm_ne_zero_iff.mpr hw)]
  obtain ⟨v, hvW, hvUnit, hvLarge⟩ := exists_subspace_rotation_support A W t ht
    hNorm hTrace hMass hCodim c hc
  have hRiesz (z : ℂ) : (conj w * z).re = f z := by
    rw [← InnerProductSpace.toDual_symm_apply]
    change (conj w * z).re = (z * conj w).re
    rw [mul_comm]
  have hFactor : conj w = (‖w‖ : ℂ) * c := by
    dsimp [c]
    have hCast : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hw)
    field_simp
  have hValue : f (rayleighValue A v) = ‖w‖ * (c * rayleighValue A v).re := by
    rw [← hRiesz, hFactor, mul_assoc, Complex.re_ofReal_mul]
  refine ⟨v, hvW, hvUnit, ?_⟩
  rw [hValue, ← hwNorm]
  nlinarith [norm_nonneg w]

set_option backward.isDefEq.respectTransparency false in
/-- High trace mass of the original matrix puts a radius `t / 4` disk in every
isometric compression whose range has codimension at most `t n / 4`. -/
theorem highMass_compression_contains_disk [Nonempty ι]
    (A : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1)
    (t : ℝ) (ht : 0 < t) (hNorm : ‖A‖ ≤ 1) (hTrace : Matrix.trace A = 0)
    (hMass : HasHighTraceMass A t)
    (hCodim : (Fintype.card ι : ℝ) - Module.finrank ℂ V.mulVecLin.range ≤
      t * Fintype.card ι / 4) :
    Metric.closedBall 0 (t / 4) ⊆ unitNumericalRange (Vᴴ * A * V) := by
  apply closedBall_subset_unitNumericalRange_of_support
  intro f
  obtain ⟨w, hwRange, hwUnit, hwLarge⟩ := exists_subspace_dual_support
    A V.mulVecLin.range t ht hNorm hTrace hMass hCodim f
  obtain ⟨v, hv⟩ := hwRange
  have hv' : V *ᵥ v = w := hv
  refine ⟨rayleighValue (Vᴴ * A * V) v, ?_, ?_⟩
  · refine ⟨v, ?_, rfl⟩
    rw [← vectorEnergy_isometry_mulVec V hV, hv', hwUnit]
  · rwa [rayleighValue_compression, hv']

set_option backward.isDefEq.respectTransparency false in
/-- The high-mass compression disk supplies a normalized neutral vector with large
compressed image, using the proved finite-ensemble selection theorem. -/
theorem highMass_compression_has_large_neutral [Nonempty ι]
    (A : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1)
    (t : ℝ) (ht : 0 < t) (hNorm : ‖A‖ ≤ 1) (hTrace : Matrix.trace A = 0)
    (hMass : HasHighTraceMass A t)
    (hCodim : (Fintype.card ι : ℝ) - Module.finrank ℂ V.mulVecLin.range ≤
      t * Fintype.card ι / 4) :
    ∃ w : EuclideanSpace ℂ κ, ‖w‖ = 1 ∧
      inner ℂ w (WithLp.toLp 2 ((Vᴴ * A * V) *ᵥ WithLp.ofLp w)) = 0 ∧
      t / 4 ≤ ‖(WithLp.toLp 2 ((Vᴴ * A * V) *ᵥ WithLp.ofLp w) :
        EuclideanSpace ℂ κ)‖ := by
  have hDisk := highMass_compression_contains_disk A V hV t ht hNorm hTrace hMass hCodim
  apply exists_unit_neutral_large_image_of_numericalRange (Vᴴ * A * V) (t / 4)
  · apply hDisk
    simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < t / 4), le_refl]
  · apply hDisk
    simp only [Metric.mem_closedBall, dist_zero_right, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < t / 4), le_refl]

/-- An isometry has range dimension equal to its number of columns. -/
theorem finrank_range_isometry (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) :
    Module.finrank ℂ V.mulVecLin.range = Fintype.card κ := by
  have hInj : Function.Injective V.mulVecLin := by
    intro x y hxy
    have h := congrArg (fun z ↦ Vᴴ *ᵥ z) hxy
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hV, Matrix.one_mulVec] using h
  rw [LinearMap.finrank_range_of_inj hInj, Module.finrank_pi]

set_option backward.isDefEq.respectTransparency false in
/-- A dimension-only version of the high-mass numerical-range disk theorem. -/
theorem highMass_compression_contains_disk_of_card [Nonempty ι]
    (A : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1)
    (t : ℝ) (ht : 0 < t) (hNorm : ‖A‖ ≤ 1) (hTrace : Matrix.trace A = 0)
    (hMass : HasHighTraceMass A t)
    (hCodim : (Fintype.card ι : ℝ) - Fintype.card κ ≤ t * Fintype.card ι / 4) :
    Metric.closedBall 0 (t / 4) ⊆ unitNumericalRange (Vᴴ * A * V) := by
  apply highMass_compression_contains_disk A V hV t ht hNorm hTrace hMass
  rwa [finrank_range_isometry V hV]

/-- Rectangular matrix multiplication obeys the Euclidean operator norm bound. -/
theorem euclideanNorm_mulVec_le (V : Matrix ι κ ℂ) (v : κ → ℂ) :
    ‖(WithLp.toLp 2 (V *ᵥ v) : EuclideanSpace ℂ ι)‖ ≤
      ‖V‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ κ)‖ := by
  let L : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ ι :=
    (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) V
  change ‖L (WithLp.toLp 2 v)‖ ≤ ‖L‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ κ)‖
  exact L.le_opNorm _

/-- The adjoint of a rectangular isometry is a contraction. -/
theorem norm_isometry_adjoint_le_one (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) : ‖Vᴴ‖ ≤ 1 := by
  have hOne : ‖(1 : Matrix κ κ ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ ↦ by simp)
  have hSquare := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [hV] at hSquare
  rw [Matrix.l2_opNorm_conjTranspose]
  nlinarith [norm_nonneg V]

set_option backward.isDefEq.respectTransparency false in
/-- The compressed neutral vector has a large image under the original matrix, not only
under its compression. It lies in the specified isometric range. -/
theorem highMass_range_has_large_neutral [Nonempty ι]
    (A : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1)
    (t : ℝ) (ht : 0 < t) (hNorm : ‖A‖ ≤ 1) (hTrace : Matrix.trace A = 0)
    (hMass : HasHighTraceMass A t)
    (hCodim : (Fintype.card ι : ℝ) - Module.finrank ℂ V.mulVecLin.range ≤
      t * Fintype.card ι / 4) :
    ∃ v : ι → ℂ, v ∈ V.mulVecLin.range ∧ vectorEnergy v = 1 ∧
      rayleighValue A v = 0 ∧
      t / 4 ≤ ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ ι)‖ := by
  obtain ⟨w, hwUnit, hwNeutral, hwLarge⟩ :=
    highMass_compression_has_large_neutral A V hV t ht hNorm hTrace hMass hCodim
  let x : κ → ℂ := WithLp.ofLp w
  have hxUnit : vectorEnergy x = 1 := by
    rw [vectorEnergy_eq_norm_sq, show WithLp.toLp 2 x = w from WithLp.toLp_ofLp 2 w,
      hwUnit, one_pow]
  refine ⟨V *ᵥ x, ⟨x, rfl⟩, ?_, ?_, ?_⟩
  · rwa [vectorEnergy_isometry_mulVec V hV]
  · rw [← rayleighValue_compression, rayleighValue_eq_inner]
    exact hwNeutral
  · have hBound := euclideanNorm_mulVec_le Vᴴ (A *ᵥ (V *ᵥ x))
    have hNormAdj := norm_isometry_adjoint_le_one V hV
    have hCompressed : (Vᴴ * A * V) *ᵥ x = Vᴴ *ᵥ (A *ᵥ (V *ᵥ x)) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    change t / 4 ≤ ‖(WithLp.toLp 2 ((Vᴴ * A * V) *ᵥ x) : EuclideanSpace ℂ κ)‖ at hwLarge
    rw [hCompressed] at hwLarge
    exact hwLarge.trans (hBound.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hNormAdj
        (norm_nonneg (WithLp.toLp 2 (A *ᵥ (V *ᵥ x)) : EuclideanSpace ℂ ι))))

end NoEpsilon
