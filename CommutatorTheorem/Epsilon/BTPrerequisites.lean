import CommutatorTheorem.Defs
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.UniformOn

/-!
# Reusable prerequisites for a future Bourgain--Tzafriri proof

This file contains elementary, axiom-free infrastructure that is useful on both standard
routes to the Bourgain--Tzafriri central-submatrix theorem:

* finite uniform probability spaces and a finite Markov inequality;
* the Sauer--Shelah cardinality estimate in the form needed for a family of subsets;
* coordinate projections and principal matrix compressions;
* norm bounds for Hilbert-space orthogonal projections and matrix compressions.

It deliberately does **not** claim the Bourgain--Tzafriri theorem.  The missing analytic
restricted-invertibility estimate is substantially deeper than these prerequisites.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing

namespace CommutatorTheorem

open MeasureTheory ProbabilityTheory Set

/-! ## Finite probability spaces -/

/-- The uniform probability measure on a finite, nonempty type. -/
noncomputable def finiteUniformMeasure (Ω : Type*) [MeasurableSpace Ω] : Measure Ω :=
  uniformOn Set.univ

/-- The uniform measure on a finite, nonempty type is a probability measure. -/
lemma finiteUniformMeasure_isProbability
    (Ω : Type*) [MeasurableSpace Ω] [Finite Ω] [Nonempty Ω] :
    IsProbabilityMeasure (finiteUniformMeasure Ω) := by
  unfold finiteUniformMeasure
  infer_instance

/-- On a finite type, uniform expectation is the ordinary arithmetic average. -/
lemma finiteUniform_integral_eq_average
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    ∫ ω, f ω ∂finiteUniformMeasure Ω =
      (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, f ω := by
  simp [finiteUniformMeasure, uniformOn, ProbabilityTheory.cond,
    MeasureTheory.integral_smul_measure]

/-- Markov's inequality specialized to the uniform distribution on a finite type.

This formulation uses `Measure.real`, so it can be combined directly with ordinary real-valued
expectations and matrix-norm estimates. -/
lemma finiteUniform_markov
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Finite Ω] [Nonempty Ω]
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) (t : ℝ) :
    t * (finiteUniformMeasure Ω).real {ω | t ≤ f ω} ≤
      ∫ ω, f ω ∂finiteUniformMeasure Ω := by
  letI : IsProbabilityMeasure (finiteUniformMeasure Ω) :=
    finiteUniformMeasure_isProbability Ω
  apply MeasureTheory.mul_meas_ge_le_integral_of_nonneg
  · exact Filter.Eventually.of_forall hf
  · exact Integrable.of_finite

/-! ## Uniform random subsets -/

/-- A Boolean selector, viewed as the finite set of coordinates on which it is true. -/
def selectedCoordinates {n : ℕ} (ω : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ω i = true

@[simp] lemma mem_selectedCoordinates {n : ℕ} (ω : Fin n → Bool) (i : Fin n) :
    i ∈ selectedCoordinates ω ↔ ω i = true := by
  simp [selectedCoordinates]

/-- Boolean selector vectors and subsets of `Fin n` are equivalent.  Thus the uniform measure on
Boolean vectors is exactly a canonical model of a uniformly random subset. -/
def boolVectorEquivFinset (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun := selectedCoordinates
  invFun := fun s i => if i ∈ s then true else false
  left_inv := by
    intro ω
    funext i
    cases h : ω i <;> simp [selectedCoordinates, h]
  right_inv := by
    intro s
    ext i
    simp [selectedCoordinates]

/-- Every finite set of coordinates is represented by a Boolean selector. -/
lemma selectedCoordinates_surjective (n : ℕ) :
    Function.Surjective (@selectedCoordinates n) :=
  (boolVectorEquivFinset n).surjective

/-- The uniform Boolean-vector law is the product of the uniform Boolean laws.  In particular,
the coordinate selectors are independent Bernoulli selectors; downstream proofs can use the
standard `Measure.pi` independence API directly after rewriting by this lemma. -/
lemma boolVector_uniform_eq_pi (n : ℕ) :
    finiteUniformMeasure (Fin n → Bool) =
      Measure.pi (fun _ : Fin n => finiteUniformMeasure Bool) := by
  unfold finiteUniformMeasure
  have hset :
      Set.univ.pi (fun _ : Fin n => (Set.univ : Set Bool)) =
        (Set.univ : Set (Fin n → Bool)) :=
    Set.pi_univ Set.univ
  rw [← hset]
  exact uniformOn_pi

/-- Each coordinate of the uniform Boolean selector is selected with probability `1/2`. -/
lemma boolSelector_true_probability {n : ℕ} (i : Fin n) :
    (finiteUniformMeasure (Fin n → Bool)) {ω | ω i = true} = (1 : ENNReal) / 2 := by
  letI : IsProbabilityMeasure (finiteUniformMeasure Bool) :=
    finiteUniformMeasure_isProbability Bool
  rw [boolVector_uniform_eq_pi]
  have hevent :
      {ω : Fin n → Bool | ω i = true} =
        (({i} : Finset (Fin n)) : Set (Fin n)).pi
          (fun _ => ({true} : Set Bool)) := by
    ext ω
    simp
  rw [hevent, Measure.pi_pi_finset]
  simp only [Finset.prod_singleton]
  unfold finiteUniformMeasure
  rw [ProbabilityTheory.uniformOn_univ]
  norm_num

/-! ## Sauer--Shelah -/

/-- A directly usable Sauer--Shelah estimate for a finite family of finite subsets. -/
lemma setFamily_card_le_sum_choose
    {α : Type*} [DecidableEq α] [Fintype α]
    (𝒜 : Finset (Finset α)) :
    𝒜.card ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card α).choose k := by
  exact (Finset.card_le_card_shatterer 𝒜).trans Finset.card_shatterer_le_sum_vcDim

/-! ## Coordinate projections and principal compressions -/

/-- The diagonal matrix of the orthogonal projection onto the coordinates in `s`. -/
noncomputable def coordinateProjection {n : ℕ} (s : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => if i ∈ s then 1 else 0

@[simp] lemma coordinateProjection_apply {n : ℕ} (s : Finset (Fin n)) (i j : Fin n) :
    coordinateProjection s i j = if i = j ∧ i ∈ s then 1 else 0 := by
  by_cases hij : i = j <;> by_cases hi : i ∈ s <;>
    simp [coordinateProjection, hij, hi]

/-- Coordinate projections are idempotent. -/
lemma coordinateProjection_mul_self {n : ℕ} (s : Finset (Fin n)) :
    coordinateProjection s * coordinateProjection s = coordinateProjection s := by
  rw [coordinateProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- Coordinate projections are self-adjoint. -/
lemma coordinateProjection_conjTranspose {n : ℕ} (s : Finset (Fin n)) :
    (coordinateProjection s).conjTranspose = coordinateProjection s := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ s <;> simp [coordinateProjection_apply, hi]
  · have hji : j ≠ i := Ne.symm hij
    simp [Matrix.conjTranspose_apply, coordinateProjection_apply, hij, hji]

/-- Coordinate projections have operator norm at most one. -/
lemma coordinateProjection_norm_le_one {n : ℕ} (s : Finset (Fin n)) :
    ‖coordinateProjection s‖ ≤ 1 := by
  rw [coordinateProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  split_ifs <;> simp

/-- Compress a matrix to a finite set of coordinates, using its increasing enumeration. -/
noncomputable def principalCompression {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) :
    Matrix (Fin s.card) (Fin s.card) ℂ :=
  A.submatrix (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl)

@[simp] lemma principalCompression_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) (i j : Fin s.card) :
    principalCompression A s i j = A (s.orderEmbOfFin rfl i) (s.orderEmbOfFin rfl j) := rfl

/-- Principal compression preserves the zero-diagonal property. -/
lemma principalCompression_zeroDiag {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : ZeroDiag A) (s : Finset (Fin n)) :
    ZeroDiag (principalCompression A s) := by
  intro i
  exact hA (s.orderEmbOfFin rfl i)

/-- A principal compression cannot increase the `ℓ₂` operator norm. -/
lemma principalCompression_norm_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) :
    ‖principalCompression A s‖ ≤ ‖A‖ := by
  simpa [principalCompression] using
    submatrix_norm_le (s.orderEmbOfFin rfl : Fin s.card → Fin n)
      (s.orderEmbOfFin rfl).injective A

/-- Multiplication by coordinate projections keeps exactly the entries in `s × s`. -/
lemma coordinateProjection_mul_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) (i j : Fin n) :
    (coordinateProjection s * A * coordinateProjection s) i j =
      if i ∈ s ∧ j ∈ s then A i j else 0 := by
  classical
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
  · simp [coordinateProjection, hi, hj]
  · simp [coordinateProjection, hi, hj]
  · simp [coordinateProjection, hi, hj]
  · simp [coordinateProjection, hi, hj]

/-- The matrix compression `Pₛ A Pₛ` has norm at most `‖A‖`. -/
lemma coordinateProjection_compression_norm_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) :
    ‖coordinateProjection s * A * coordinateProjection s‖ ≤ ‖A‖ := by
  calc
    ‖coordinateProjection s * A * coordinateProjection s‖
        ≤ ‖coordinateProjection s‖ * ‖A‖ * ‖coordinateProjection s‖ := by
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖A‖ * 1 := by
      gcongr <;> exact coordinateProjection_norm_le_one s
    _ = ‖A‖ := by ring

/-! ## Hilbert-space projection bridge -/

/-- Orthogonal projection onto any closed subspace is contractive. -/
lemma orthogonalProjection_norm_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    ‖U.starProjection‖ ≤ 1 :=
  U.starProjection_norm_le

/-- Pointwise contractivity of an orthogonal projection. -/
lemma orthogonalProjection_apply_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] (x : E) :
    ‖U.starProjection x‖ ≤ ‖x‖ :=
  U.norm_starProjection_apply_le x

end CommutatorTheorem
