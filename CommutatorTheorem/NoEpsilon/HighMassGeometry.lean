import CommutatorTheorem.Shared.Fillmore
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Neutral vectors with a large image

The squared energies below use the Euclidean norm. In particular they do not use the
default supremum norm on a function type. Unitary mixing of two input vectors will
produce a zero-expectation vector without losing their averaged image energy.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix ComplexConjugate

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The squared Euclidean norm of a complex vector. -/
def vectorEnergy (v : ι → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

/-- The unnormalized numerical-range value of a vector. -/
def rayleighValue (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  star v ⬝ᵥ (A *ᵥ v)

theorem vectorEnergy_eq_norm_sq (v : ι → ℂ) :
    vectorEnergy v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ ^ 2 := by
  simp [vectorEnergy, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]

theorem vectorEnergy_nonneg (v : ι → ℂ) : 0 ≤ vectorEnergy v := by
  rw [vectorEnergy_eq_norm_sq]
  positivity

@[simp] theorem vectorEnergy_eq_zero (v : ι → ℂ) : vectorEnergy v = 0 ↔ v = 0 := by
  rw [vectorEnergy_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero]
  exact WithLp.toLp_eq_zero 2

theorem vectorEnergy_smul (c : ℂ) (v : ι → ℂ) :
    vectorEnergy (c • v) = Complex.normSq c * vectorEnergy v := by
  simp [vectorEnergy, Complex.normSq_mul, Finset.mul_sum]

theorem rayleighValue_smul (A : Matrix ι ι ℂ) (c : ℂ) (v : ι → ℂ) :
    rayleighValue A (c • v) = (Complex.normSq c : ℂ) * rayleighValue A v := by
  simp only [rayleighValue, Matrix.mulVec_smul, star_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, ← mul_assoc, Complex.normSq_eq_conj_mul_self]
  rw [mul_comm c (star c)]
  rfl

theorem rayleighValue_eq_inner (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    rayleighValue A v = inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ ι)
      (WithLp.toLp 2 (A *ᵥ v)) := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rfl

omit [Fintype κ] in
/-- The diagonal of a compressed matrix is the corresponding vector expectation. -/
theorem gram_diagonal (A : Matrix ι ι ℂ) (X : Matrix ι κ ℂ) (j : κ) :
    (Xᴴ * A * X) j j = rayleighValue A (fun i ↦ X i j) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    rayleighValue, dotProduct, Pi.star_apply, Matrix.mulVec]

theorem gram_trace_re (X : Matrix ι κ ℂ) :
    (Matrix.trace (Xᴴ * X)).re = ∑ j, vectorEnergy (fun i ↦ X i j) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum,
    Complex.ofReal_re, vectorEnergy]

/-- A right unitary change of columns preserves their total Euclidean energy. -/
theorem column_energy_mul_unitary [DecidableEq κ] (X : Matrix ι κ ℂ)
    (U : Matrix κ κ ℂ) (hU : U * Uᴴ = 1) :
    (∑ j, vectorEnergy (fun i ↦ (X * U) i j)) =
      ∑ j, vectorEnergy (fun i ↦ X i j) := by
  rw [← gram_trace_re, ← gram_trace_re]
  congr 1
  have hGram : (X * U)ᴴ * (X * U) = Uᴴ * (Xᴴ * X) * U := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hGram, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

/-- A nonzero zero-expectation vector can be normalized while retaining an energy ratio. -/
theorem exists_normalized_neutral_of_energy_ratio (A : Matrix ι ι ℂ) (v : ι → ℂ)
    (r : ℝ) (hv : v ≠ 0) (hNeutral : rayleighValue A v = 0)
    (hRatio : r ^ 2 * vectorEnergy v ≤ vectorEnergy (A *ᵥ v)) :
    ∃ w : ι → ℂ, vectorEnergy w = 1 ∧ rayleighValue A w = 0 ∧
      r ^ 2 ≤ vectorEnergy (A *ᵥ w) := by
  let s : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖
  have hs : 0 < s := norm_pos_iff.mpr (by
    intro hz
    exact hv ((WithLp.toLp_eq_zero 2).mp hz))
  have hsE : vectorEnergy v = s ^ 2 := vectorEnergy_eq_norm_sq v
  let c : ℂ := (s⁻¹ : ℝ)
  have hc : Complex.normSq c = (s ^ 2)⁻¹ := by
    simp [c, Complex.normSq_ofReal, pow_two]
  refine ⟨c • v, ?_, ?_, ?_⟩
  · rw [vectorEnergy_smul, hc, hsE, inv_mul_cancel₀ (pow_ne_zero 2 hs.ne')]
  · rw [rayleighValue_smul, hNeutral, mul_zero]
  · rw [Matrix.mulVec_smul, vectorEnergy_smul, hc]
    rw [mul_comm ((s ^ 2)⁻¹)]
    apply (le_mul_inv_iff₀ (sq_pos_of_pos hs)).2
    simpa only [hsE] using hRatio

/-- Cauchy--Schwarz translates a numerical-range value into an image-energy bound. -/
theorem rayleigh_sq_le_image_energy (A : Matrix ι ι ℂ) (v : ι → ℂ)
    (hv : vectorEnergy v = 1) : ‖rayleighValue A v‖ ^ 2 ≤ vectorEnergy (A *ᵥ v) := by
  have hn : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ = 1 := by
    have := (vectorEnergy_eq_norm_sq v).symm.trans hv
    nlinarith [norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ ι)]
  have hCS := norm_inner_le_norm (𝕜 := ℂ)
    (WithLp.toLp 2 v : EuclideanSpace ℂ ι) (WithLp.toLp 2 (A *ᵥ v))
  rw [← rayleighValue_eq_inner, hn, one_mul] at hCS
  rw [vectorEnergy_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hCS 2

/-- A family with a large averaged image contains a nonzero column with a large ratio. -/
theorem exists_column_energy_ratio (A : Matrix ι ι ℂ) (X : Matrix ι κ ℂ) (r : ℝ)
    (hPos : 0 < ∑ j, vectorEnergy (fun i ↦ X i j))
    (hEnergy : r ^ 2 * (∑ j, vectorEnergy (fun i ↦ X i j)) ≤
      ∑ j, vectorEnergy (A *ᵥ (fun i ↦ X i j))) :
    ∃ j, (fun i ↦ X i j) ≠ 0 ∧
      r ^ 2 * vectorEnergy (fun i ↦ X i j) ≤ vectorEnergy (A *ᵥ (fun i ↦ X i j)) := by
  classical
  by_contra hNone
  push Not at hNone
  have hle (j : κ) : vectorEnergy (A *ᵥ (fun i ↦ X i j)) ≤
      r ^ 2 * vectorEnergy (fun i ↦ X i j) := by
    by_cases hj : (fun i ↦ X i j) = 0
    · rw [hj]
      simp [vectorEnergy]
    · exact (hNone j hj).le
  have hSome : ∃ j, (fun i ↦ X i j) ≠ 0 := by
    by_contra h
    push Not at h
    have hZero : (∑ j, vectorEnergy (fun i ↦ X i j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact (vectorEnergy_eq_zero _).mpr (h j)
    linarith
  obtain ⟨j, hj⟩ := hSome
  have hlt := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) ↦ hle j)
    ⟨j, Finset.mem_univ j, hNone j hj⟩
  rw [← Finset.mul_sum] at hlt
  exact (not_lt_of_ge hEnergy) hlt

/-- Hollow Gram compression plus an averaged image bound yields a unit neutral vector. -/
theorem exists_neutral_of_hollow_columns (A : Matrix ι ι ℂ) (X : Matrix ι κ ℂ)
    (r : ℝ) (hHollow : ∀ j, (Xᴴ * A * X) j j = 0)
    (hPos : 0 < ∑ j, vectorEnergy (fun i ↦ X i j))
    (hEnergy : r ^ 2 * (∑ j, vectorEnergy (fun i ↦ X i j)) ≤
      ∑ j, vectorEnergy (A *ᵥ (fun i ↦ X i j))) :
    ∃ w : ι → ℂ, vectorEnergy w = 1 ∧ rayleighValue A w = 0 ∧
      r ^ 2 ≤ vectorEnergy (A *ᵥ w) := by
  obtain ⟨j, hj, hRatio⟩ := exists_column_energy_ratio A X r hPos hEnergy
  exact exists_normalized_neutral_of_energy_ratio A _ r hj
    ((gram_diagonal A X j).symm.trans (hHollow j)) hRatio

/-- Any finite positive-energy ensemble with zero averaged expectation has a neutral
unit vector attaining at least its averaged image-energy ratio. -/
theorem exists_neutral_large_image_of_zero_trace_gram (m : ℕ)
    (A : Matrix ι ι ℂ) (X : Matrix ι (Fin m) ℂ) (r : ℝ)
    (hTrace : Matrix.trace (Xᴴ * A * X) = 0)
    (hPos : 0 < ∑ j, vectorEnergy (fun i ↦ X i j))
    (hEnergy : r ^ 2 * (∑ j, vectorEnergy (fun i ↦ X i j)) ≤
      ∑ j, vectorEnergy (A *ᵥ (fun i ↦ X i j))) :
    ∃ w : ι → ℂ, vectorEnergy w = 1 ∧ rayleighValue A w = 0 ∧
      r ^ 2 ≤ vectorEnergy (A *ᵥ w) := by
  classical
  obtain ⟨U, B, hU, hB, hGram⟩ := CommutatorTheorem.fillmore (Xᴴ * A * X) hTrace
  have hHollow : ∀ j, ((X * U)ᴴ * A * (X * U)) j j = 0 := by
    have hG : (X * U)ᴴ * A * (X * U) = B := by
      calc
        _ = Uᴴ * (Xᴴ * A * X) * U := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Uᴴ * (U * B * Uᴴ) * U := by rw [hGram]
        _ = (Uᴴ * U) * B * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
        _ = B := by rw [hU.2, Matrix.one_mul, Matrix.mul_one]
    intro j
    rw [hG]
    exact hB j
  have hImage : (∑ j, vectorEnergy (A *ᵥ (fun i ↦ (X * U) i j))) =
      ∑ j, vectorEnergy (A *ᵥ (fun i ↦ X i j)) := by
    have hCol (Y : Matrix ι (Fin m) ℂ) (j : Fin m) :
        A *ᵥ (fun i ↦ Y i j) = (fun i ↦ (A * Y) i j) := rfl
    simp_rw [hCol]
    rw [← Matrix.mul_assoc, column_energy_mul_unitary (A * X) U hU.1]
  apply exists_neutral_of_hollow_columns A (X * U) r hHollow
  · rwa [column_energy_mul_unitary X U hU.1]
  · rwa [column_energy_mul_unitary X U hU.1, hImage]

/-- Opposite numerical-range values force a unit neutral vector with a large image.

The proof hollows the two-dimensional Gram compression. This is stronger than merely
using convexity to find a neutral vector: it also preserves total image energy.
-/
theorem exists_neutral_large_image_of_opposite_rayleigh
    (A : Matrix ι ι ℂ) (x y : ι → ℂ) (r : ℝ)
    (hx : vectorEnergy x = 1) (hy : vectorEnergy y = 1)
    (hRx : rayleighValue A x = (r : ℂ)) (hRy : rayleighValue A y = -(r : ℂ)) :
    ∃ w : ι → ℂ, vectorEnergy w = 1 ∧ rayleighValue A w = 0 ∧
      r ^ 2 ≤ vectorEnergy (A *ᵥ w) := by
  classical
  let X : Matrix ι (Fin 2) ℂ := fun i ↦ ![x i, y i]
  have hX0 : (fun i ↦ X i 0) = x := rfl
  have hX1 : (fun i ↦ X i 1) = y := rfl
  have hTrace : Matrix.trace (Xᴴ * A * X) = 0 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, gram_diagonal,
      hX0, hX1, hRx, hRy, add_neg_cancel]
  obtain ⟨U, B, hU, hB, hGram⟩ := CommutatorTheorem.fillmore (Xᴴ * A * X) hTrace
  let Z : Matrix ι (Fin 2) ℂ := X * U
  have hHollow : ∀ j, (Zᴴ * A * Z) j j = 0 := by
    have hG : Zᴴ * A * Z = B := by
      calc
        Zᴴ * A * Z = Uᴴ * (Xᴴ * A * X) * U := by
          simp only [Z, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Uᴴ * (U * B * Uᴴ) * U := by rw [hGram]
        _ = B := by
          calc
            _ = (Uᴴ * U) * B * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
            _ = B := by rw [hU.2, Matrix.one_mul, Matrix.mul_one]
    intro j
    rw [hG]
    exact hB j
  have hTotal : (∑ j, vectorEnergy (fun i ↦ Z i j)) = 2 := by
    rw [show Z = X * U from rfl, column_energy_mul_unitary X U hU.1]
    simp only [Fin.sum_univ_two, hX0, hX1, hx, hy]
    norm_num
  have hImage : (∑ j, vectorEnergy (A *ᵥ (fun i ↦ Z i j))) =
      vectorEnergy (A *ᵥ x) + vectorEnergy (A *ᵥ y) := by
    have hCol (Y : Matrix ι (Fin 2) ℂ) (j : Fin 2) :
        A *ᵥ (fun i ↦ Y i j) = (fun i ↦ (A * Y) i j) := rfl
    simp_rw [hCol]
    change (∑ j, vectorEnergy (fun i ↦ (A * (X * U)) i j)) = _
    rw [← Matrix.mul_assoc, column_energy_mul_unitary (A * X) U hU.1]
    simp only [Fin.sum_univ_two, ← hCol, hX0, hX1]
  have hxImage := rayleigh_sq_le_image_energy A x hx
  have hyImage := rayleigh_sq_le_image_energy A y hy
  rw [hRx, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hxImage
  rw [hRy, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hyImage
  apply exists_neutral_of_hollow_columns A Z r hHollow
  · rw [hTotal]
    norm_num
  · rw [hTotal, hImage]
    linarith

/-- The numerical range is defined using unit Euclidean vectors. -/
def unitNumericalRange (A : Matrix ι ι ℂ) : Set ℂ :=
  {z | ∃ v : ι → ℂ, vectorEnergy v = 1 ∧ rayleighValue A v = z}

theorem rayleighValue_one [DecidableEq ι] (v : ι → ℂ) :
    rayleighValue (1 : Matrix ι ι ℂ) v = (vectorEnergy v : ℂ) := by
  simp only [rayleighValue, Matrix.one_mulVec, dotProduct, Pi.star_apply,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, vectorEnergy, Complex.ofReal_sum]

theorem rayleighValue_sub_smul_one [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z : ℂ) (v : ι → ℂ) :
    rayleighValue (A - z • 1) v = rayleighValue A v - z * (vectorEnergy v : ℂ) := by
  change star v ⬝ᵥ ((A - z • 1) *ᵥ v) = _
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
  change rayleighValue A v - z • rayleighValue 1 v = _
  rw [rayleighValue_one, smul_eq_mul]

/-- Toeplitz--Hausdorff convexity, obtained by hollowing a weighted two-column Gram matrix. -/
theorem convex_unitNumericalRange (A : Matrix ι ι ℂ) : Convex ℝ (unitNumericalRange A) := by
  classical
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  obtain ⟨x, hx, hRx⟩ := hz₁
  obtain ⟨y, hy, hRy⟩ := hz₂
  let z : ℂ := a • z₁ + b • z₂
  let x' : ι → ℂ := (Real.sqrt a : ℂ) • x
  let y' : ι → ℂ := (Real.sqrt b : ℂ) • y
  let X : Matrix ι (Fin 2) ℂ := fun i ↦ ![x' i, y' i]
  have hX0 : (fun i ↦ X i 0) = x' := rfl
  have hX1 : (fun i ↦ X i 1) = y' := rfl
  have hna : Complex.normSq (Real.sqrt a : ℂ) = a := by
    rw [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt ha]
  have hnb : Complex.normSq (Real.sqrt b : ℂ) = b := by
    rw [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt hb]
  have hEx : vectorEnergy x' = a := by rw [vectorEnergy_smul, hna, hx, mul_one]
  have hEy : vectorEnergy y' = b := by rw [vectorEnergy_smul, hnb, hy, mul_one]
  have hRx' : rayleighValue A x' = (a : ℂ) * z₁ := by
    rw [rayleighValue_smul, hna, hRx]
  have hRy' : rayleighValue A y' = (b : ℂ) * z₂ := by
    rw [rayleighValue_smul, hnb, hRy]
  have hTrace : Matrix.trace (Xᴴ * (A - z • 1) * X) = 0 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, gram_diagonal, hX0, hX1,
      rayleighValue_sub_smul_one, hRx', hRy', hEx, hEy]
    have habC : (a : ℂ) + b = 1 := by exact_mod_cast hab
    change (a : ℂ) * z₁ - z * a + (b * z₂ - z * b) = 0
    calc
      _ = z - z * ((a : ℂ) + b) := by simp only [z, Complex.real_smul]; ring
      _ = 0 := by rw [habC, mul_one, sub_self]
  have hPos : 0 < ∑ j, vectorEnergy (fun i ↦ X i j) := by
    simpa only [Fin.sum_univ_two, hX0, hX1, hEx, hEy, hab] using zero_lt_one
  have hEnergy : (0 : ℝ) ^ 2 * (∑ j, vectorEnergy (fun i ↦ X i j)) ≤
      ∑ j, vectorEnergy ((A - z • 1) *ᵥ (fun i ↦ X i j)) := by
    simp only [zero_pow (by decide : 2 ≠ 0), zero_mul]
    exact Finset.sum_nonneg (fun j _ ↦ vectorEnergy_nonneg _)
  obtain ⟨w, hw, hRw, _⟩ :=
    exists_neutral_large_image_of_zero_trace_gram 2 (A - z • 1) X 0 hTrace hPos hEnergy
  refine ⟨w, hw, ?_⟩
  rw [rayleighValue_sub_smul_one, hw, Complex.ofReal_one, mul_one, sub_eq_zero] at hRw
  exact hRw

/-- The numerical range of a finite matrix is compact, with its genuine Euclidean sphere. -/
theorem isCompact_unitNumericalRange (A : Matrix ι ι ℂ) : IsCompact (unitNumericalRange A) := by
  have hCont : Continuous (fun v : EuclideanSpace ℂ ι ↦ rayleighValue A (WithLp.ofLp v)) := by
    unfold rayleighValue Matrix.mulVec dotProduct
    fun_prop
  have hSet : unitNumericalRange A =
      (fun v : EuclideanSpace ℂ ι ↦ rayleighValue A (WithLp.ofLp v)) ''
        Metric.sphere 0 1 := by
    ext z
    constructor
    · rintro ⟨v, hv, hRv⟩
      refine ⟨WithLp.toLp 2 v, ?_, hRv⟩
      rw [Metric.mem_sphere, dist_zero_right]
      rw [vectorEnergy_eq_norm_sq] at hv
      nlinarith [norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ ι)]
    · rintro ⟨v, hv, hRv⟩
      refine ⟨WithLp.ofLp v, ?_, hRv⟩
      rw [vectorEnergy_eq_norm_sq, WithLp.toLp_ofLp]
      rw [Metric.mem_sphere, dist_zero_right] at hv
      rw [hv, one_pow]
  rw [hSet]
  exact (isCompact_sphere (0 : EuclideanSpace ℂ ι) 1).image hCont

set_option backward.isDefEq.respectTransparency false in
/-- A uniform lower bound for every supporting functional puts the entire disk in the
numerical range. Compactness and convexity discharge the separation step. -/
theorem closedBall_subset_unitNumericalRange_of_support (A : Matrix ι ι ℂ) (r : ℝ)
    (hSupport : ∀ f : ℂ →L[ℝ] ℝ, ∃ z ∈ unitNumericalRange A, r * ‖f‖ ≤ f z) :
    Metric.closedBall 0 r ⊆ unitNumericalRange A := by
  intro z hz
  by_contra hOutside
  obtain ⟨f, u, hUpper, hSep⟩ := geometric_hahn_banach_closed_point
    (convex_unitNumericalRange A) (isCompact_unitNumericalRange A).isClosed hOutside
  obtain ⟨w, hw, hLower⟩ := hSupport f
  have hNorm : ‖z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hf : f z ≤ ‖f‖ * ‖z‖ := le_trans (le_abs_self _) (f.le_opNorm z)
  have hBound := mul_le_mul_of_nonneg_left hNorm (norm_nonneg f)
  have hStrict := hUpper w hw
  nlinarith

/-- Only the two real endpoints of a numerical-range disk are needed for a large neutral
vector. The displayed norm is the Euclidean norm on vectors. -/
theorem exists_unit_neutral_large_image_of_numericalRange
    (A : Matrix ι ι ℂ) (r : ℝ)
    (hPlus : (r : ℂ) ∈ unitNumericalRange A)
    (hMinus : -(r : ℂ) ∈ unitNumericalRange A) :
    ∃ w : EuclideanSpace ℂ ι, ‖w‖ = 1 ∧
      inner ℂ w (WithLp.toLp 2 (A *ᵥ WithLp.ofLp w)) = 0 ∧
      r ≤ ‖(WithLp.toLp 2 (A *ᵥ WithLp.ofLp w) : EuclideanSpace ℂ ι)‖ := by
  obtain ⟨x, hx, hRx⟩ := hPlus
  obtain ⟨y, hy, hRy⟩ := hMinus
  obtain ⟨v, hv, hRv, hImage⟩ :=
    exists_neutral_large_image_of_opposite_rayleigh A x y r hx hy hRx hRy
  refine ⟨WithLp.toLp 2 v, ?_, ?_, ?_⟩
  · rw [vectorEnergy_eq_norm_sq] at hv
    nlinarith [norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ ι)]
  · exact (rayleighValue_eq_inner A v).symm.trans hRv
  · rw [vectorEnergy_eq_norm_sq] at hImage
    change r ≤ ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ ι)‖
    nlinarith [norm_nonneg (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ ι)]

end NoEpsilon
