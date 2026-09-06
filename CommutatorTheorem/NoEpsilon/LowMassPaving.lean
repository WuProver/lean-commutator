import CommutatorTheorem.NoEpsilon.ThreeHermitianBasis
import CommutatorTheorem.NoEpsilon.SteinitzGrouping
import CommutatorTheorem.NoEpsilon.MSSSelection
import Mathlib.Analysis.Matrix.Order

/-!
# Matrix interfaces for low-mass paving

The basis, frame, trace, and norm identities in this file are independent of
the MSS good-outcome existence theorem. Selection hypotheses are kept explicit
until that theorem is connected to the balanced binary tree.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace NoEpsilon
namespace LowMassPaving

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem right_unitary_preserves_range (Q : Matrix ι κ ℂ) (U : Matrix κ κ ℂ)
    (hU : U * Uᴴ = 1) : (Q * U) * (Q * U)ᴴ = Q * Qᴴ := by
  simp only [Matrix.conjTranspose_mul]
  calc
    Q * U * (Uᴴ * Qᴴ) = Q * (U * Uᴴ) * Qᴴ := by simp only [Matrix.mul_assoc]
    _ = Q * Qᴴ := by rw [hU, Matrix.mul_one]

theorem right_unitary_preserves_isometry (Q : Matrix ι κ ℂ) (U : Matrix κ κ ℂ)
    (hQ : Qᴴ * Q = 1) (hU : Uᴴ * U = 1) : (Q * U)ᴴ * (Q * U) = 1 := by
  simp only [Matrix.conjTranspose_mul]
  calc
    Uᴴ * Qᴴ * (Q * U) = Uᴴ * (Qᴴ * Q) * U := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hQ, Matrix.mul_one, hU]

theorem compression_right_mul (A : Matrix ι ι ℂ) (Q : Matrix ι κ ℂ)
    (U : Matrix κ κ ℂ) :
    (Q * U)ᴴ * A * (Q * U) = Uᴴ * (Qᴴ * A * Q) * U := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The exact local basis construction, including the `12/R` energy bound.
Each supplied group is an isometric copy of `ℂ^R`; no selection theorem is assumed. -/
theorem exists_flat_group_bases {k R : ℕ} (hR : 0 < R)
    (H G E : Matrix ι ι ℂ) (hH : H.IsHermitian) (hG : G.IsHermitian)
    (hE : E.PosSemidef) (Q : Fin k → Matrix ι (Fin R) ℂ)
    (hQ : ∀ j, (Q j)ᴴ * Q j = 1)
    (hMass : ∀ j, (Matrix.trace ((Q j)ᴴ * E * Q j)).re ≤ 6) :
    ∃ V : Fin k → Matrix ι (Fin R) ℂ, ∀ j,
      (V j)ᴴ * V j = 1 ∧ V j * (V j)ᴴ = Q j * (Q j)ᴴ ∧
      (∀ a, rayleighValue H (fun i ↦ V j i a) =
        Matrix.trace ((Q j)ᴴ * H * Q j) / (R : ℂ)) ∧
      (∀ a, rayleighValue G (fun i ↦ V j i a) =
        Matrix.trace ((Q j)ᴴ * G * Q j) / (R : ℂ)) ∧
      (∀ a, (rayleighValue E (fun i ↦ V j i a)).re ≤ 12 / (R : ℝ)) := by
  have hlocal (j : Fin k) := ThreeHermitian.exists_diagonal_control
    ((Q j)ᴴ * H * Q j) ((Q j)ᴴ * G * Q j) ((Q j)ᴴ * E * Q j)
    (ThreeHermitian.isHermitian_compression H hH (Q j))
    (ThreeHermitian.isHermitian_compression G hG (Q j))
    (hE.conjTranspose_mul_mul_same (Q j))
  choose U hU hHU hGU hEU using hlocal
  refine ⟨fun j ↦ Q j * U j, fun j ↦ ?_⟩
  refine ⟨right_unitary_preserves_isometry _ _ (hQ j) (hU j).2,
    right_unitary_preserves_range _ _ (hU j).1, ?_, ?_, ?_⟩
  · intro a
    rw [← gram_diagonal, compression_right_mul]
    exact hHU j a
  · intro a
    rw [← gram_diagonal, compression_right_mul]
    exact hGU j a
  · intro a
    rw [← gram_diagonal, compression_right_mul]
    exact (hEU j a).trans (by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg R)
      linarith [hMass j])

/-- The column outer products sum to the matrix frame operator. -/
theorem sum_outer_columns (X : Matrix ι κ ℂ) :
    (∑ a, MSSSelection.outer (fun i ↦ X i a)) = X * Xᴴ := by
  ext i j
  simp [Matrix.sum_apply, MSSSelection.outer, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Euclidean energy after a factor map is its Gram quadratic form. -/
theorem image_energy_eq_gram (S : Matrix ι κ ℂ) (v : κ → ℂ) :
    vectorEnergy (S *ᵥ v) = (rayleighValue (Sᴴ * S) v).re := by
  have h := congrArg Complex.re (rayleighValue_compression (1 : Matrix ι ι ℂ) S v)
  simpa only [Matrix.mul_one, rayleighValue_one, Complex.ofReal_re] using h.symm

theorem mss_energy_eq_vectorEnergy (v : ι → ℂ) : MSSSelection.energy v = vectorEnergy v := by
  simp only [MSSSelection.energy, vectorEnergy, Complex.normSq_eq_norm_sq]

/-- A positive semidefinite matrix admits an exact Hermitian square-root factor. -/
theorem exists_hermitian_square_root (E : Matrix ι ι ℂ) (hE : E.PosSemidef) :
    ∃ S : Matrix ι ι ℂ, Sᴴ = S ∧ S * S = E := by
  have hpos : (CFC.sqrt E).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg E)
  refine ⟨CFC.sqrt E, hpos.1.eq, ?_⟩
  exact CFC.sqrt_mul_sqrt_self E hE.nonneg

/-- Mapping a complete orthonormal basis through a Hermitian square root gives
exactly the prescribed covariance, and each vector has the correct scalar energy. -/
theorem square_root_frame (E S : Matrix ι ι ℂ) (V : Matrix ι κ ℂ)
    (hS : Sᴴ = S) (hSS : S * S = E) (hV : V * Vᴴ = 1) :
    (∑ a, MSSSelection.outer (fun i ↦ (S * V) i a)) = E ∧
      ∀ a, MSSSelection.energy (fun i ↦ (S * V) i a) =
        (rayleighValue E (fun i ↦ V i a)).re := by
  constructor
  · rw [sum_outer_columns, Matrix.conjTranspose_mul, hS]
    calc
      S * V * (Vᴴ * S) = S * (V * Vᴴ) * S := by simp only [Matrix.mul_assoc]
      _ = E := by rw [hV, Matrix.mul_one, hSS]
  · intro a
    have hcol : (fun i ↦ (S * V) i a) = S *ᵥ (fun i ↦ V i a) := rfl
    rw [mss_energy_eq_vectorEnergy, hcol, image_energy_eq_gram, hS, hSS]

/-- Rectangular `X*Xᴴ` and `Xᴴ*X` have equal Euclidean operator norm. -/
theorem norm_mul_adjoint_eq_norm_adjoint_mul (X : Matrix ι κ ℂ) :
    ‖X * Xᴴ‖ = ‖Xᴴ * X‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self Xᴴ
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose,
    Matrix.l2_opNorm_conjTranspose_mul_self] using h

/-- The covariance bound on selected square-root vectors is exactly the norm
bound on the compression of the original positive matrix. -/
theorem norm_compression_eq_frame (E S : Matrix ι ι ℂ) (V : Matrix ι κ ℂ)
    (hGram : Sᴴ * S = E) :
    ‖Vᴴ * E * V‖ = ‖∑ a, MSSSelection.outer (fun i ↦ (S * V) i a)‖ := by
  rw [sum_outer_columns, norm_mul_adjoint_eq_norm_adjoint_mul]
  congr 1
  simp only [Matrix.conjTranspose_mul, ← hGram, Matrix.mul_assoc]

/-- The coordinate isometry for one group of an exact finite regrouping. -/
def groupInclusion {k R : ℕ} (e : (Fin k × Fin R) ≃ ι) (j : Fin k) :
    Matrix ι (Fin R) ℂ := coordinateInclusion (fun a ↦ e (j, a))

theorem groupInclusion_gram {k R : ℕ} (e : (Fin k × Fin R) ≃ ι) (j l : Fin k) :
    (groupInclusion e j)ᴴ * groupInclusion e l = if j = l then 1 else 0 := by
  by_cases hj : j = l
  · subst l
    simp only [if_pos rfl, groupInclusion]
    apply coordinateInclusion_isometry
    intro a b hab
    exact congrArg Prod.snd (e.injective hab)
  · rw [if_neg hj]
    ext a b
    simp [groupInclusion, coordinateInclusion, Matrix.mul_apply,
      Matrix.conjTranspose_apply, mul_ite, ite_mul, e.injective.eq_iff, hj, Ne.symm hj]

/-- The group ranges are disjoint and cover the original coordinate space exactly. -/
theorem sum_groupInclusion_ranges {k R : ℕ} (e : (Fin k × Fin R) ≃ ι) :
    (∑ j, groupInclusion e j * (groupInclusion e j)ᴴ) = 1 := by
  ext i l
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    groupInclusion, coordinateInclusion]
  rw [← Fintype.sum_prod_type (fun p : Fin k × Fin R ↦
    (if i = e p then (1 : ℂ) else 0) * star (if l = e p then (1 : ℂ) else 0))]
  rw [e.sum_comp (fun x ↦
    (if i = x then (1 : ℂ) else 0) * star (if l = x then (1 : ℂ) else 0))]
  simp [Matrix.one_apply, mul_ite, ite_mul, eq_comm]

theorem left_isometry_preserves_gram (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1)
    (C D : Matrix ι κ ℂ) : (U * C)ᴴ * (U * D) = Cᴴ * D := by
  simp only [Matrix.conjTranspose_mul]
  calc
    Cᴴ * Uᴴ * (U * D) = Cᴴ * (Uᴴ * U) * D := by simp only [Matrix.mul_assoc]
    _ = Cᴴ * D := by rw [hU, Matrix.mul_one]

theorem sum_unitary_group_ranges {k R : ℕ} (e : (Fin k × Fin R) ≃ ι)
    (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    (∑ j, (U * groupInclusion e j) * (U * groupInclusion e j)ᴴ) = 1 := by
  calc
    _ = U * (∑ j, groupInclusion e j * (groupInclusion e j)ᴴ) * Uᴴ := by
      simp only [Finset.mul_sum, Finset.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [sum_groupInclusion_ranges, Matrix.mul_one, hU]

theorem compression_left_mul (A U : Matrix ι ι ℂ) (C D : Matrix ι κ ℂ) :
    (U * C)ᴴ * A * (U * D) = Cᴴ * (Uᴴ * A * U) * D := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem group_compression_trace {k R : ℕ} (e : (Fin k × Fin R) ≃ ι)
    (A : Matrix ι ι ℂ) (j : Fin k) :
    Matrix.trace ((groupInclusion e j)ᴴ * A * groupInclusion e j) =
      ∑ a : Fin R, A (e (j, a)) (e (j, a)) := by
  dsimp only [groupInclusion]
  rw [← submatrix_eq_coordinate_compression]
  rfl

/-- Steinitz grouping applied to an actual eigenbasis of `G`. The resulting
rank-`R` isometries have orthogonal ranges covering the full space, reduce `G`,
and satisfy both quantitative trace estimates. -/
theorem exists_spectral_groups {k R : ℕ} (hk : 0 < k) (hR : 0 < R)
    (G E : Matrix (Fin (k * R)) (Fin (k * R)) ℂ)
    (hG : G.IsHermitian) (hGn : ‖G‖ ≤ 1) (hGt : Matrix.trace G = 0)
    (hE : E.PosSemidef) (hE₁ : E ≤ 1) (hEt : (Matrix.trace E).re ≤ 2 * k) :
    ∃ Q : Fin k → Matrix (Fin (k * R)) (Fin R) ℂ,
      (∀ j l, (Q j)ᴴ * Q l = if j = l then 1 else 0) ∧
      (∑ j, Q j * (Q j)ᴴ) = 1 ∧
      (∀ j l, j ≠ l → (Q j)ᴴ * G * Q l = 0) ∧
      (∀ j, |(Matrix.trace ((Q j)ᴴ * G * Q j)).re| ≤ 4 ∧
        (Matrix.trace ((Q j)ᴴ * E * Q j)).re ≤ 6) := by
  let U : Matrix (Fin (k * R)) (Fin (k * R)) ℂ := hG.eigenvectorUnitary
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hG.eigenvectorUnitary
  have hU' : Uᴴ * U = 1 := Unitary.coe_star_mul_self hG.eigenvectorUnitary
  let eig := hG.eigenvalues
  have hDiag : Uᴴ * G * U = Matrix.diagonal (fun i ↦ (eig i : ℂ)) := by
    have hspec : G = U * Matrix.diagonal (fun i ↦ (eig i : ℂ)) * Uᴴ := by
      simpa only [Unitary.conjStarAlgAut_apply] using hG.spectral_theorem
    rw [hspec]
    calc
      _ = (Uᴴ * U) * Matrix.diagonal (fun i ↦ (eig i : ℂ)) * (Uᴴ * U) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU']; simp
  let F := Uᴴ * E * U
  have hF : F.PosSemidef := hE.conjTranspose_mul_mul_same U
  have hF₁ : (1 - F).PosSemidef := by
    have h := (Matrix.le_iff.mp hE₁).conjTranspose_mul_mul_same U
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU', F] using h
  have heig (i : Fin (k * R)) : |eig i| ≤ 1 :=
    (abs_hermitian_eigenvalue_le_opNorm G hG i).trans hGn
  have hd (i : Fin (k * R)) : 0 ≤ (F i i).re ∧ (F i i).re ≤ 1 := by
    refine ⟨(Complex.nonneg_iff.mp hF.diag_nonneg).1, ?_⟩
    have h := (Complex.nonneg_iff.mp (hF₁.diag_nonneg (i := i))).1
    simpa only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re,
      sub_nonneg] using h
  have heigsum : ∑ i, eig i = 0 := by
    have h := congrArg Complex.re (hG.trace_eq_sum_eigenvalues.symm.trans hGt)
    simpa [eig] using h
  have hdSum : ∑ i, (F i i).re ≤ 2 * k := by
    rw [← Complex.re_sum]
    change (Matrix.trace F).re ≤ 2 * k
    dsimp [F]
    rwa [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  obtain ⟨e, he⟩ := SteinitzGrouping.exists_trace_controlled_groups hk hR
    eig (fun i ↦ (F i i).re) heig hd heigsum hdSum
  let Q : Fin k → Matrix (Fin (k * R)) (Fin R) ℂ := fun j ↦ U * groupInclusion e j
  have hcomp (j : Fin k) :
      (Q j)ᴴ * G * Q j = Matrix.diagonal (fun a ↦ (eig (e (j, a)) : ℂ)) := by
    dsimp [Q]
    rw [compression_left_mul, hDiag]
    change (coordinateInclusion (fun a ↦ e (j, a)))ᴴ *
      Matrix.diagonal (fun i ↦ (eig i : ℂ)) * coordinateInclusion (fun a ↦ e (j, a)) = _
    rw [← submatrix_eq_coordinate_compression]
    exact Matrix.submatrix_diagonal _ _ (fun a b hab ↦ congrArg Prod.snd (e.injective hab))
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro j l
    exact (left_isometry_preserves_gram U hU' _ _).trans (groupInclusion_gram e j l)
  · exact sum_unitary_group_ranges e U hU
  · intro j l hjl
    dsimp [Q]
    rw [compression_left_mul, hDiag]
    change (coordinateInclusion (fun a ↦ e (j, a)))ᴴ *
      Matrix.diagonal (fun i ↦ (eig i : ℂ)) * coordinateInclusion (fun a ↦ e (l, a)) = 0
    rw [← submatrix_eq_coordinate_compression]
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg]
    intro h
    exact hjl (congrArg Prod.fst (e.injective h))
  · intro j
    constructor
    · rw [hcomp, Matrix.trace_diagonal]
      simpa only [Complex.re_sum, Complex.ofReal_re] using (he j).1
    · dsimp [Q]
      rw [compression_left_mul, group_compression_trace, Complex.re_sum]
      exact (he j).2

/-- Cross-compression vanishing depends only on the two ranges, so it survives
the independent unitary changes made inside every spectral group. -/
theorem cross_compression_zero_of_same_ranges (A : Matrix ι ι ℂ)
    (Q T V W : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (hVQ : V * Vᴴ = Q * Qᴴ) (hWT : W * Wᴴ = T * Tᴴ) (hQT : Qᴴ * A * T = 0) :
    Vᴴ * A * W = 0 := by
  calc
    Vᴴ * A * W = (Vᴴ * V) * Vᴴ * A * W * (Wᴴ * W) := by
      rw [hV, hW, Matrix.one_mul, Matrix.mul_one]
    _ = Vᴴ * (V * Vᴴ) * A * (W * Wᴴ) * W := by simp only [Matrix.mul_assoc]
    _ = Vᴴ * (Q * Qᴴ) * A * (T * Tᴴ) * W := by rw [hVQ, hWT]
    _ = (Vᴴ * Q) * (Qᴴ * A * T) * (Tᴴ * W) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hQT]; simp

theorem sum_group_traces {k R : ℕ} (Q : Fin k → Matrix ι (Fin R) ℂ)
    (hQ : (∑ j, Q j * (Q j)ᴴ) = 1) (A : Matrix ι ι ℂ) :
    (∑ j, Matrix.trace ((Q j)ᴴ * A * Q j)) = Matrix.trace A := by
  calc
    _ = ∑ j, Matrix.trace (Q j * (Q j)ᴴ * A) :=
      Finset.sum_congr rfl (fun j _ ↦ Matrix.trace_mul_cycle _ _ _)
    _ = Matrix.trace A := by
      rw [← Matrix.trace_sum, ← Finset.sum_mul, hQ, Matrix.one_mul]

theorem norm_trace_hermitian (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ‖Matrix.trace A‖ = |(Matrix.trace A).re| := by
  have h := congrArg Complex.im (Matrix.trace_conjTranspose A)
  rw [hA.eq] at h
  simp only [Complex.star_def, Complex.conj_im] at h
  exact (Complex.abs_re_eq_norm.mpr (by linarith)).symm

/-- The entire pre-selection basis construction. Every returned group consists
of orthonormal columns, all groups together form a complete orthonormal basis,
and each possible one-per-group selection has the required constant diagonal data. -/
theorem exists_prepared_groups {k R : ℕ} (hk : 0 < k) (hR : 0 < R)
    (H G E : Matrix (Fin (k * R)) (Fin (k * R)) ℂ)
    (hH : H.IsHermitian) (hHt : Matrix.trace H = 0)
    (hG : G.IsHermitian) (hGn : ‖G‖ ≤ 1) (hGt : Matrix.trace G = 0)
    (hE : E.PosSemidef) (hE₁ : E ≤ 1) (hEt : (Matrix.trace E).re ≤ 2 * k) :
    ∃ (V : Fin k → Matrix (Fin (k * R)) (Fin R) ℂ) (h g : Fin k → ℂ),
      (∀ j l, (V j)ᴴ * V l = if j = l then 1 else 0) ∧
      (∑ j, V j * (V j)ᴴ) = 1 ∧
      (∀ j l, j ≠ l → (V j)ᴴ * G * V l = 0) ∧
      (∑ j, h j) = 0 ∧ (∑ j, g j) = 0 ∧
      (∀ j, ‖g j‖ ≤ 4 / (R : ℝ) ∧ ∀ a,
        rayleighValue H (fun i ↦ V j i a) = h j ∧
        rayleighValue G (fun i ↦ V j i a) = g j ∧
        (rayleighValue E (fun i ↦ V j i a)).re ≤ 12 / (R : ℝ)) := by
  obtain ⟨Q, hQ, hQsum, hQG, hTrace⟩ :=
    exists_spectral_groups hk hR G E hG hGn hGt hE hE₁ hEt
  obtain ⟨V, hV⟩ := exists_flat_group_bases hR H G E hH hG hE Q
    (fun j ↦ by simpa using hQ j j) (fun j ↦ (hTrace j).2)
  let h : Fin k → ℂ := fun j ↦ Matrix.trace ((Q j)ᴴ * H * Q j) / (R : ℂ)
  let g : Fin k → ℂ := fun j ↦ Matrix.trace ((Q j)ᴴ * G * Q j) / (R : ℂ)
  refine ⟨V, h, g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j l
    by_cases hjl : j = l
    · subst l
      simpa using (hV j).1
    · rw [if_neg hjl]
      have hzero := cross_compression_zero_of_same_ranges (1 : Matrix _ _ ℂ)
        (Q j) (Q l) (V j) (V l) (hV j).1 (hV l).1 (hV j).2.1 (hV l).2.1
        (by simpa only [Matrix.mul_one, if_neg hjl] using hQ j l)
      simpa only [Matrix.mul_one] using hzero
  · calc
      _ = ∑ j, Q j * (Q j)ᴴ := Finset.sum_congr rfl (fun j _ ↦ (hV j).2.1)
      _ = 1 := hQsum
  · intro j l hjl
    exact cross_compression_zero_of_same_ranges G (Q j) (Q l) (V j) (V l)
      (hV j).1 (hV l).1 (hV j).2.1 (hV l).2.1 (hQG j l hjl)
  · simp only [h, ← Finset.sum_div, sum_group_traces Q hQsum H, hHt, zero_div]
  · simp only [g, ← Finset.sum_div, sum_group_traces Q hQsum G, hGt, zero_div]
  · intro j
    refine ⟨?_, fun a ↦ ⟨(hV j).2.2.1 a, (hV j).2.2.2.1 a, (hV j).2.2.2.2 a⟩⟩
    dsimp [g]
    rw [norm_div, Complex.norm_natCast,
      norm_trace_hermitian _ (ThreeHermitian.isHermitian_compression G hG (Q j))]
    exact div_le_div_of_nonneg_right (hTrace j).1 (Nat.cast_nonneg R)

def concatenateGroups {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ) :
    Matrix ι (Fin k × Fin R) ℂ := fun i p ↦ V p.1 i p.2

theorem concatenateGroups_range {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ) :
    concatenateGroups V * (concatenateGroups V)ᴴ = ∑ j, V j * (V j)ᴴ := by
  ext i l
  simp [concatenateGroups, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]

theorem concatenateGroups_gram_entry {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ)
    (j l : Fin k) (a b : Fin R) :
    ((concatenateGroups V)ᴴ * concatenateGroups V) (j, a) (l, b) =
      ((V j)ᴴ * V l) a b := rfl

theorem concatenateGroups_isometry {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ)
    (hV : ∀ j l, (V j)ᴴ * V l = if j = l then 1 else 0) :
    (concatenateGroups V)ᴴ * concatenateGroups V = 1 := by
  ext ⟨j, a⟩ ⟨l, b⟩
  rw [concatenateGroups_gram_entry, hV]
  by_cases hjl : j = l <;> simp [hjl, Matrix.one_apply]

def selectedColumns {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ) (a : Fin k → Fin R) :
    Matrix ι (Fin k) ℂ := fun i j ↦ V j i (a j)

theorem selectedColumns_compression_entry {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ)
    (a : Fin k → Fin R) (A : Matrix ι ι ℂ) (j l : Fin k) :
    ((selectedColumns V a)ᴴ * A * selectedColumns V a) j l =
      ((V j)ᴴ * A * V l) (a j) (a l) := rfl

theorem selectedColumns_isometry {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ)
    (a : Fin k → Fin R) (hV : ∀ j l, (V j)ᴴ * V l = if j = l then 1 else 0) :
    (selectedColumns V a)ᴴ * selectedColumns V a = 1 := by
  ext j l
  have h := selectedColumns_compression_entry V a (1 : Matrix ι ι ℂ) j l
  simp only [Matrix.mul_one] at h
  rw [h, hV]
  by_cases hjl : j = l <;> simp [hjl, Matrix.one_apply]

/-- The trace of every one-per-group selection is fixed before MSS chooses it. -/
theorem selectedColumns_trace {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ)
    (a : Fin k → Fin R) (A : Matrix ι ι ℂ) (d : Fin k → ℂ)
    (hd : ∀ j b, rayleighValue A (fun i ↦ V j i b) = d j) :
    Matrix.trace ((selectedColumns V a)ᴴ * A * selectedColumns V a) = ∑ j, d j := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro j _
  rw [gram_diagonal]
  exact hd j (a j)

/-- Since different original groups reduce `G`, every selected compression is
diagonal, with the already fixed group means as its diagonal entries. -/
theorem selectedColumns_diagonal {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ)
    (a : Fin k → Fin R) (G : Matrix ι ι ℂ) (g : Fin k → ℂ)
    (hcross : ∀ j l, j ≠ l → (V j)ᴴ * G * V l = 0)
    (hdiag : ∀ j b, rayleighValue G (fun i ↦ V j i b) = g j) :
    (selectedColumns V a)ᴴ * G * selectedColumns V a = Matrix.diagonal g := by
  ext j l
  by_cases hjl : j = l
  · subst l
    rw [gram_diagonal, Matrix.diagonal_apply_eq]
    exact hdiag j (a j)
  · rw [selectedColumns_compression_entry, hcross j l hjl]
    simp [Matrix.diagonal_apply, hjl]

theorem selectedColumns_norm_le {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ)
    (a : Fin k → Fin R) (G : Matrix ι ι ℂ) (g : Fin k → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hcross : ∀ j l, j ≠ l → (V j)ᴴ * G * V l = 0)
    (hdiag : ∀ j b, rayleighValue G (fun i ↦ V j i b) = g j)
    (hbound : ∀ j, ‖g j‖ ≤ c) :
    ‖(selectedColumns V a)ᴴ * G * selectedColumns V a‖ ≤ c := by
  rw [selectedColumns_diagonal V a G g hcross hdiag, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hc).mpr hbound

/-- Order domination in a C⋆-algebra, stated generically to avoid scalar-algebra diamonds. -/
theorem selfAdjoint_norm_le_of_order_interval {𝒜 : Type*} [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] (H E : 𝒜) (hH : IsSelfAdjoint H)
    (hE : IsSelfAdjoint E) (hlower : -E ≤ H) (hupper : H ≤ E) : ‖H‖ ≤ ‖E‖ := by
  obtain hsub | hnontriv := subsingleton_or_nontrivial 𝒜
  · simp [Subsingleton.elim H 0, Subsingleton.elim E 0]
  · have hEbound : E ≤ algebraMap ℝ 𝒜 ‖E‖ := hE.le_algebraMap_norm_self
    have hUpperSpec : ∀ x ∈ spectrum ℝ H, x ≤ ‖E‖ :=
      (le_algebraMap_iff_spectrum_le hH).mp (hupper.trans hEbound)
    have hLowerSpec : ∀ x ∈ spectrum ℝ H, -‖E‖ ≤ x :=
      (algebraMap_le_iff_le_spectrum hH).mp (by
        simpa only [map_neg] using (neg_le_neg hEbound).trans hlower)
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hH with h | h
    · exact hUpperSpec _ h
    · have := hLowerSpec _ h
      linarith

/-- Hermitian order domination gives the sharp operator norm bound. -/
theorem norm_le_of_hermitian_order_interval (H E : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hE : E.PosSemidef) (hlower : -E ≤ H) (hupper : H ≤ E) :
    ‖H‖ ≤ ‖E‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := {}
  exact selfAdjoint_norm_le_of_order_interval H E
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hH)
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hE.1) hlower hupper

theorem compression_mono (A B : Matrix ι ι ℂ) (hAB : A ≤ B) (V : Matrix ι κ ℂ) :
    Vᴴ * A * V ≤ Vᴴ * B * V := by
  apply Matrix.le_iff.mpr
  have h := (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same V
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using h

/-- The same sharp order comparison survives every rectangular compression. -/
theorem norm_compression_le_of_order_interval (H E : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hE : E.PosSemidef) (hlower : -E ≤ H) (hupper : H ≤ E)
    (V : Matrix ι κ ℂ) : ‖Vᴴ * H * V‖ ≤ ‖Vᴴ * E * V‖ := by
  apply norm_le_of_hermitian_order_interval _ _
    (ThreeHermitian.isHermitian_compression H hH V) (hE.conjTranspose_mul_mul_same V)
  · simpa only [Matrix.mul_neg, Matrix.neg_mul] using compression_mono (-E) H hlower V
  · exact compression_mono H E hupper V

end LowMassPaving
end NoEpsilon
