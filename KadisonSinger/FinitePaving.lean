import CommutatorTheorem.NoEpsilon.LowMassPaving
import PavingSeparation.PavingBasic
import KadisonSinger.VectorPartition

/-!
# Finite Anderson paving from the MSS vector partition theorem

We apply MSS to the columns of the square roots of the positive contractions
`(1 + T) / 2` and `(1 - T) / 2`, then refine the two partitions. Every
compression uses the original coordinate projections. The final theorem chooses
one finite number of colors before the ambient finite type and matrix.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open PavingSeparation NoEpsilon
namespace KadisonSinger
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma coordProjection_hermitian (s : Finset ι) : (coordProjection s).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  split_ifs <;> simp

lemma coordProjection_sq (s : Finset ι) :
    coordProjection s * coordProjection s = coordProjection s := by
  rw [coordProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  split_ifs <;> simp

lemma compression_hermitian (s : Finset ι) (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (compression s A).IsHermitian := by
  simpa only [compression, (coordProjection_hermitian s).eq] using
    ThreeHermitian.isHermitian_compression A hA (coordProjection s)

lemma compression_posSemidef (s : Finset ι) (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    (compression s A).PosSemidef := by
  simpa only [compression, (coordProjection_hermitian s).eq] using
    hA.conjTranspose_mul_mul_same (coordProjection s)

lemma compression_add (s : Finset ι) (A B : Matrix ι ι ℂ) :
    compression s (A+B) = compression s A + compression s B := by
  simp [compression, Matrix.mul_add, Matrix.add_mul]

lemma compression_sub (s : Finset ι) (A B : Matrix ι ι ℂ) :
    compression s (A-B) = compression s A - compression s B := by
  simp [compression, Matrix.mul_sub, Matrix.sub_mul]

lemma compression_real_smul (s : Finset ι) (c : ℝ) (A : Matrix ι ι ℂ) :
    compression s (c • A) = c • compression s A := by
  simp [compression]

lemma compression_one (s : Finset ι) :
    compression s (1 : Matrix ι ι ℂ) = coordProjection s := by
  simp [compression, coordProjection_sq]

lemma compression_outer_frame (s : Finset ι) (A S : Matrix ι ι ℂ)
    (hS : Sᴴ = S) (hSS : S * S = A) :
    ‖compression s A‖ = ‖∑ i ∈ s, MSSSelection.outer (fun j ↦ S j i)‖ := by
  have h := LowMassPaving.norm_compression_eq_frame A S (coordProjection s)
    (by rw [hS,hSS])
  rw [(coordProjection_hermitian s).eq] at h
  change ‖compression s A‖ = _ at h
  rw [h]
  congr 1
  ext a b
  simp [coordProjection, Matrix.mul_diagonal, MSSSelection.outer, Matrix.sum_apply,
    Finset.sum_ite_mem, apply_ite]

lemma hermitian_le_norm_smul (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    A ≤ ‖A‖ • (1 : Matrix ι ι ℂ) := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := {}
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hA).le_algebraMap_norm_self

lemma hermitian_le_scalar_of_norm (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (a : ℝ) (ha : ‖A‖ ≤ a) : A ≤ a • (1 : Matrix ι ι ℂ) := by
  apply (hermitian_le_norm_smul A hA).trans
  apply Matrix.le_iff.mpr
  have hp : (((a-‖A‖ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr ha)
  convert hp using 1
  ext i j
  simp [Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul, sub_mul]

lemma compression_le_scalar_projection (s : Finset ι) (A : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (a : ℝ) (ha : ‖compression s A‖ ≤ a) :
    compression s A ≤ a • coordProjection s := by
  have h := LowMassPaving.compression_mono _ _
    (hermitian_le_scalar_of_norm _ (compression_hermitian s A hA.1) a ha)
    (coordProjection s)
  rw [(coordProjection_hermitian s).eq] at h
  change compression s (compression s A) ≤ compression s (a • (1 : Matrix ι ι ℂ)) at h
  simpa [compression_compression_of_subset s s (Finset.Subset.refl s),
    compression_real_smul, compression_one] using h

/-- A positive contraction with small diagonal has a paving in its original coordinates. -/
theorem positive_contraction_paving (r : ℕ) (hr : 0 < r)
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (hdef : (1 - A).PosSemidef)
    (δ : ℝ) (hδ : 0 < δ) (hdiag : ∀ i, (A i i).re ≤ δ) :
    ∃ c : ι → Fin r, ∀ j,
      ‖compression (Finset.univ.filter (fun i ↦ c i = j)) A‖ ≤
        (1 / Real.sqrt (r : ℝ) + Real.sqrt δ)^2 := by
  obtain ⟨S, hS, hSS⟩ := LowMassPaving.exists_hermitian_square_root A hA
  have hframe := LowMassPaving.square_root_frame A S (1 : Matrix ι ι ℂ) hS hSS
    (by simp)
  have hsum : (∑ i, MSSSelection.outer (fun j ↦ S j i)) = A := by
    simpa only [Matrix.mul_one] using hframe.1
  have he : ∀ i, MSSSelection.energy (fun j ↦ S j i) ≤ δ := by
    intro i
    have hh := hframe.2 i
    simp only [Matrix.mul_one] at hh
    rw [hh]
    convert hdiag i using 1
    simp [rayleighValue, Matrix.one_apply, Matrix.mulVec,
      dotProduct, mul_ite, ite_mul, eq_comm]
  obtain ⟨c, hc⟩ := vector_partition_le r hr (fun i j ↦ S j i)
    (by change (1 - ∑ i, MSSSelection.outer (fun j ↦ S j i)).PosSemidef; rw [hsum]; exact hdef)
    δ hδ he
  refine ⟨c, fun j ↦ ?_⟩
  rw [compression_outer_frame _ A S hS hSS]
  exact hc j

lemma half_identity_add_pos (T : Matrix ι ι ℂ) (hT : T.IsHermitian) (hTn : ‖T‖ ≤ 1) :
    ((1 / 2 : ℝ) • (1 + T)).PosSemidef := by
  have hn : -T ≤ (1 : Matrix ι ι ℂ) := by
    convert hermitian_le_scalar_of_norm (-T) hT.neg 1 (by simpa using hTn) using 1
    ext i j
    simp [Matrix.smul_apply]
  have hp : (1 + T).PosSemidef := by simpa using Matrix.le_iff.mp hn
  have h := hp.smul (show (0 : ℂ) ≤ ((1 / 2 : ℝ) : ℂ) by
    exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num))
  convert h using 1

lemma half_identity_add_deficit (T : Matrix ι ι ℂ) (hT : T.IsHermitian) (hTn : ‖T‖ ≤ 1) :
    (1 - (1 / 2 : ℝ) • (1 + T)).PosSemidef := by
  have hp := half_identity_add_pos (-T) hT.neg (by simpa using hTn)
  convert hp using 1
  ext i j
  simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  ring

lemma norm_of_two_half_compressions (T : Matrix ι ι ℂ) (hT : T.IsHermitian)
    (hTn : ‖T‖ ≤ 1) (s : Finset ι) (a : ℝ) (ha : 0 ≤ 2 * a - 1)
    (hp : ‖compression s ((1 / 2 : ℝ) • (1 + T))‖ ≤ a)
    (hm : ‖compression s ((1 / 2 : ℝ) • (1 - T))‖ ≤ a) :
    ‖compression s T‖ ≤ 2 * a - 1 := by
  have hplus := compression_le_scalar_projection s _ (half_identity_add_pos T hT hTn) a hp
  have hminus := compression_le_scalar_projection s _
    (show ((1 / 2 : ℝ) • (1 - T)).PosSemidef from by
      simpa only [sub_eq_add_neg] using half_identity_add_pos (-T) hT.neg (by simpa using hTn)) a hm
  have hP : (coordProjection s).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> simp
  have hE : ((2 * a - 1) • coordProjection s).PosSemidef := by
    have h := hP.smul (show (0 : ℂ) ≤ ((2 * a - 1:ℝ) : ℂ) from by exact_mod_cast ha)
    convert h using 1
  have hu : compression s T ≤ (2 * a - 1) • coordProjection s := by
    apply Matrix.le_iff.mpr
    have h := (Matrix.le_iff.mp hplus).smul (show (0 : ℂ) ≤ 2 by norm_num)
    convert h using 1
    rw [compression_real_smul, compression_add, compression_one]
    ext i j
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    split_ifs <;> ring
  have hl : -((2 * a - 1) • coordProjection s) ≤ compression s T := by
    apply Matrix.le_iff.mpr
    have h := (Matrix.le_iff.mp hminus).smul (show (0 : ℂ) ≤ 2 by norm_num)
    convert h using 1
    rw [compression_real_smul, compression_sub, compression_one]
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
    split_ifs <;> ring
  have h := LowMassPaving.norm_le_of_hermitian_order_interval _ _
    (compression_hermitian s T hT) hE hl hu
  apply h.trans
  change ‖((2 * a - 1:ℝ) : ℂ) • coordProjection s‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ha]
  exact mul_le_of_le_one_right ha (coordProjection_norm_le s)

/-- Pave the two positive contractions and take the common refinement. -/
theorem hermitian_contraction_paving (r : ℕ) (hr : 0 < r)
    (T : Matrix ι ι ℂ) (hT : T.IsHermitian) (hTn : ‖T‖ ≤ 1)
    (hdiag : ∀ i, T i i = 0) :
    ∃ c : ι → Fin (r * r), ∀ j,
      ‖compression (Finset.univ.filter (fun i ↦ c i = j)) T‖ ≤
        2 * (1 / Real.sqrt (r : ℝ) + Real.sqrt (1 / 2)) ^ 2 - 1 := by
  have hd : ∀ i, (((1 / 2:ℝ) • (1 + T)) i i).re ≤ 1 / 2 := by
    intro i
    simp [Matrix.smul_apply, Matrix.add_apply, hdiag, Complex.real_smul]
  have hm : ∀ i, (((1 / 2:ℝ) • (1 + (-T))) i i).re ≤ 1 / 2 := by
    intro i
    simp [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, hdiag, Complex.real_smul]
  obtain ⟨cp, hcp⟩ := positive_contraction_paving r hr _
    (half_identity_add_pos T hT hTn) (half_identity_add_deficit T hT hTn)
    (1 / 2) (by norm_num) hd
  obtain ⟨cm, hcm⟩ := positive_contraction_paving r hr _
    (half_identity_add_pos (-T) hT.neg (by simpa using hTn))
    (half_identity_add_deficit (-T) hT.neg (by simpa using hTn))
    (1 / 2) (by norm_num) hm
  let c : ι → Fin (r * r) := fun i ↦ finProdFinEquiv (cp i,cm i)
  refine ⟨c, fun j ↦ ?_⟩
  let s := Finset.univ.filter (fun i ↦ c i = j)
  have hs (i : ι) (hi : i ∈ s) : (cp i,cm i) = finProdFinEquiv.symm j := by
    have h := congrArg finProdFinEquiv.symm (Finset.mem_filter.mp hi).2
    change finProdFinEquiv.symm (finProdFinEquiv (cp i,cm i)) = _ at h
    simpa only [Equiv.symm_apply_apply] using h
  have hsp : s ⊆ Finset.univ.filter (fun i ↦ cp i = (finProdFinEquiv.symm j).1) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.fst (hs i hi)⟩
  have hsm : s ⊆ Finset.univ.filter (fun i ↦ cm i = (finProdFinEquiv.symm j).2) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.snd (hs i hi)⟩
  apply norm_of_two_half_compressions T hT hTn s _
  · have h0 := Real.sqrt_nonneg (1 / 2:ℝ)
    have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    have hx : 0 ≤ 1 / Real.sqrt (r : ℝ) := by positivity
    nlinarith [mul_nonneg hx h0, sq_nonneg (1 / Real.sqrt (r : ℝ))]
  · exact (compression_norm_le_of_subset _ _ hsp _).trans (hcp _)
  · simpa only [sub_eq_add_neg] using
      (compression_norm_le_of_subset _ _ hsm _).trans (hcm _)

/-- Choose a number of parts depending only on the desired error. -/
lemma exists_paving_parameter (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ 2 * (1 / Real.sqrt (r : ℝ) + Real.sqrt (1 / 2)) ^ 2 - 1 ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (6/ε))
  have hn : 1 < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hn0 : 0 < (N : ℝ) := lt_trans zero_lt_one hn
  have hngt : 6/ε < (N : ℝ) := (le_max_right _ _).trans_lt hN
  have hNe : 6 < ε*N := by
    have := (div_lt_iff₀ hε).mp hngt
    nlinarith
  have hx : 0 ≤ 1 / (N : ℝ) := by positivity
  have hx1 : 1 / (N : ℝ) ≤ 1 := (div_le_one hn0).mpr hn.le
  have hxe : 1 / (N : ℝ) ≤ ε/6 := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  have hy := Real.sqrt_nonneg (1 / 2:ℝ)
  have hy2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hy1 : Real.sqrt (1 / 2:ℝ) ≤ 1 := by nlinarith
  refine ⟨N ^ 2, pow_pos (by exact_mod_cast hn0) _, ?_⟩
  rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg N)]
  have hx2 : (1 / (N : ℝ))^2 ≤ 1 / (N : ℝ) := by nlinarith [mul_le_mul_of_nonneg_left hx1 hx]
  have hxy : (1 / (N : ℝ))*Real.sqrt (1 / 2:ℝ) ≤ 1 / (N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hy1 hx]
  nlinarith

/-- Anderson paving for all finite Hermitian zero-diagonal matrices, with a
number of colors independent of the matrix dimension. -/
theorem hermitian_paving (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ ∀ (ι : Type*) [Fintype ι] [DecidableEq ι]
      (T : Matrix ι ι ℂ), T.IsHermitian → (∀ i, T i i = 0) →
      ∃ c : ι → Fin r, ∀ j,
        ‖compression (Finset.univ.filter (fun i ↦ c i = j)) T‖ ≤ ε * ‖T‖ := by
  obtain ⟨r, hr, hb⟩ := exists_paving_parameter ε hε
  refine ⟨r * r, Nat.mul_pos hr hr, fun ι _ _ T hT hdiag ↦ ?_⟩
  letI : NeZero (r * r) := ⟨ne_of_gt (Nat.mul_pos hr hr)⟩
  by_cases hz : T = 0
  · refine ⟨fun _ ↦ 0, fun j ↦ ?_⟩
    simp [hz, compression]
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr hz
  let N : Matrix ι ι ℂ := ((‖T‖⁻¹ : ℝ) : ℂ) • T
  have hN : N.IsHermitian := hT.smul (k := Complex.ofReal (‖T‖⁻¹)) (by
    change star (Complex.ofReal (‖T‖⁻¹)) = _
    simp)
  have hNn : ‖N‖ ≤ 1 := by
    change ‖(Complex.ofReal (‖T‖⁻¹)) • T‖ ≤ 1
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg T)),
      inv_mul_cancel₀ hn.ne']
  have hNd : ∀ i, N i i = 0 := by
    intro i
    change Complex.ofReal (‖T‖⁻¹) * T i i = 0
    rw [hdiag, mul_zero]
  obtain ⟨c, hc⟩ := hermitian_contraction_paving r hr N hN hNn hNd
  refine ⟨c, fun j ↦ ?_⟩
  have h : ‖compression (Finset.univ.filter (fun i ↦ c i = j)) N‖ ≤ ε := (hc j).trans hb
  dsimp only [N] at h
  rw [compression_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg T))] at h
  have h' : ‖compression (Finset.univ.filter (fun i ↦ c i = j)) T‖ / ‖T‖ ≤ ε := by
    simpa only [div_eq_mul_inv, mul_comm] using h
  exact (div_le_iff₀ hn).mp h'
end KadisonSinger
