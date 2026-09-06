import PavingSeparation.CoordinateNorm
import Mathlib.Combinatorics.Pigeonhole

/-! # Original-coordinate compressions and finite optimal paving values -/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace PavingSeparation

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- The orthogonal projection onto an explicitly specified set of original coordinates. -/
def coordProjection (s : Finset ι) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i ↦ if i ∈ s then 1 else 0)

/-- Compression in the ambient original coordinate space, including zero padding. -/
def compression (s : Finset ι) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  coordProjection s * A * coordProjection s

@[simp] theorem compression_apply (s : Finset ι) (A : Matrix ι ι ℂ) (i j : ι) :
    compression s A i j = if i ∈ s ∧ j ∈ s then A i j else 0 := by
  simp [compression, coordProjection, Matrix.diagonal_mul, Matrix.mul_diagonal]
  split_ifs <;> simp_all

theorem coordProjection_norm_le (s : Finset ι) : ‖coordProjection s‖ ≤ 1 := by
  rw [coordProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs <;> simp

theorem compression_norm_le (s : Finset ι) (A : Matrix ι ι ℂ) :
    ‖compression s A‖ ≤ ‖A‖ := by
  calc
    ‖compression s A‖ ≤ ‖coordProjection s‖ * ‖A‖ * ‖coordProjection s‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖A‖ * 1 := by
      gcongr <;> exact coordProjection_norm_le s
    _ = ‖A‖ := by ring

@[simp] theorem compression_univ (A : Matrix ι ι ℂ) :
    compression Finset.univ A = A := by
  ext i j
  simp

@[simp] theorem compression_empty (A : Matrix ι ι ℂ) :
    compression ∅ A = 0 := by
  ext i j
  simp

@[simp] theorem compression_smul (s : Finset ι) (z : ℂ) (A : Matrix ι ι ℂ) :
    compression s (z • A) = z • compression s A := by
  ext i j
  simp only [compression_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

@[simp] theorem compression_neg (s : Finset ι) (A : Matrix ι ι ℂ) :
    compression s (-A) = -compression s A := by
  ext i j
  simp only [compression_apply, Matrix.neg_apply]
  split_ifs <;> simp

theorem compression_compression_of_subset (s t : Finset ι) (h : s ⊆ t)
    (A : Matrix ι ι ℂ) : compression s (compression t A) = compression s A := by
  ext i j
  simp only [compression_apply]
  split_ifs with hs ht
  · rfl
  · exact False.elim (ht ⟨h hs.1, h hs.2⟩)
  · rfl

theorem compression_norm_le_of_subset (s t : Finset ι) (h : s ⊆ t)
    (A : Matrix ι ι ℂ) : ‖compression s A‖ ≤ ‖compression t A‖ := by
  rw [← compression_compression_of_subset s t h A]
  exact compression_norm_le s _

section Coloring

variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- The original-coordinate block belonging to a color, allowing empty color classes. -/
def colorClass (c : ι → κ) (a : κ) : Finset ι :=
  Finset.univ.filter (fun i ↦ c i = a)

omit [DecidableEq ι] [Fintype κ] [Nonempty κ] in
@[simp] theorem mem_colorClass (c : ι → κ) (a : κ) (i : ι) :
    i ∈ colorClass c a ↔ c i = a := by simp [colorClass]

/-- The actual maximum of the finitely many compressed operator norms. -/
def pavingNorm (A : Matrix ι ι ℂ) (c : ι → κ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a ↦ ‖compression (colorClass c a) A‖)

theorem compression_norm_le_pavingNorm (A : Matrix ι ι ℂ) (c : ι → κ) (a : κ) :
    ‖compression (colorClass c a) A‖ ≤ pavingNorm A c := by
  exact Finset.le_sup' (fun a ↦ ‖compression (colorClass c a) A‖) (Finset.mem_univ a)

theorem pavingNorm_le (A : Matrix ι ι ℂ) (c : ι → κ) (b : ℝ)
    (h : ∀ a, ‖compression (colorClass c a) A‖ ≤ b) : pavingNorm A c ≤ b := by
  exact Finset.sup'_le _ _ (fun a _ ↦ h a)

theorem pavingNorm_nonneg (A : Matrix ι ι ℂ) (c : ι → κ) : 0 ≤ pavingNorm A c := by
  obtain ⟨a⟩ := ‹Nonempty κ›
  exact (norm_nonneg _).trans (compression_norm_le_pavingNorm A c a)

theorem pavingNorm_le_norm (A : Matrix ι ι ℂ) (c : ι → κ) : pavingNorm A c ≤ ‖A‖ := by
  exact pavingNorm_le A c _ (fun a ↦ compression_norm_le _ A)

theorem pavingNorm_eq_zero_of_injective (A : Matrix ι ι ℂ) (hdiag : ∀ i, A i i = 0)
    (c : ι → κ) (hc : Function.Injective c) : pavingNorm A c = 0 := by
  apply le_antisymm
  · apply pavingNorm_le
    intro a
    have heq : compression (colorClass c a) A = 0 := by
      ext i j
      simp only [compression_apply, mem_colorClass, Matrix.zero_apply]
      split_ifs with h
      · have hij : i = j := hc (h.1.trans h.2.symm)
        subst j
        exact hdiag i
      · rfl
    simp [heq]
  · exact pavingNorm_nonneg A c

end Coloring

/-- The genuine minimum over all colorings by at most r colors. -/
def pavingMinimum (A : Matrix ι ι ℂ) (r : ℕ) [NeZero r] : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun c : ι → Fin r ↦ pavingNorm A c)

theorem pavingMinimum_le (A : Matrix ι ι ℂ) (r : ℕ) [NeZero r] (c : ι → Fin r) :
    pavingMinimum A r ≤ pavingNorm A c := by
  exact Finset.inf'_le (fun c : ι → Fin r ↦ pavingNorm A c) (Finset.mem_univ c)

theorem le_pavingMinimum (A : Matrix ι ι ℂ) (r : ℕ) [NeZero r] (b : ℝ)
    (h : ∀ c : ι → Fin r, b ≤ pavingNorm A c) : b ≤ pavingMinimum A r := by
  exact Finset.le_inf' _ _ (fun c _ ↦ h c)

theorem pavingMinimum_nonneg (A : Matrix ι ι ℂ) (r : ℕ) [NeZero r] :
    0 ≤ pavingMinimum A r :=
  le_pavingMinimum A r 0 (fun c ↦ pavingNorm_nonneg A c)

theorem exists_pavingMinimum (A : Matrix ι ι ℂ) (r : ℕ) [NeZero r] :
    ∃ c : ι → Fin r, pavingNorm A c = pavingMinimum A r := by
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (ι → Fin r)).Nonempty)
    (fun c ↦ pavingNorm A c)
  exact ⟨c, hc.symm⟩

/-- The squared Euclidean norm of each column is bounded by the squared operator norm. -/
theorem column_sq_sum_le (A : Matrix ι ι ℂ) (j : ι) :
    ∑ i, ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  let ej : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j (1 : ℂ))
  have h := Matrix.l2_opNorm_mulVec A ej
  have he : ‖ej‖ = 1 := by simp [ej, PiLp.norm_single]
  rw [he, mul_one] at h
  have hv : (EuclideanSpace.equiv ι ℂ).symm (A.mulVec ej.ofLp) =
      WithLp.toLp 2 (fun i ↦ A i j) := by
    ext i
    simp [ej]
  rw [hv] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa [EuclideanSpace.norm_sq_eq] using hsq

/-- Flat entries give the Frobenius lower bound already from one compressed column. -/
theorem flat_compression_sq_lower (A : Matrix ι ι ℂ) (d : ℝ)
    (hdiag : ∀ i, A i i = 0) (hflat : ∀ i j, i ≠ j → ‖A i j‖ ^ 2 = d)
    (s : Finset ι) (hs : s.Nonempty) :
    ((s.card - 1 : ℕ) : ℝ) * d ≤ ‖compression s A‖ ^ 2 := by
  obtain ⟨j, hj⟩ := hs
  have hentry (i : ι) :
      ‖compression s A i j‖ ^ 2 = if i ∈ s.erase j then d else 0 := by
    by_cases hij : i = j
    · subst i
      simp [hdiag]
    · by_cases hi : i ∈ s
      · simp [compression_apply, hi, hj, hij, hflat i j hij]
      · simp [compression_apply, hi, hij]
  have hsum : ∑ i, ‖compression s A i j‖ ^ 2 =
      ((s.card - 1 : ℕ) : ℝ) * d := by
    simp_rw [hentry]
    rw [Fintype.sum_ite_mem]
    simp [Finset.card_erase_of_mem hj]
  rw [← hsum]
  exact column_sq_sum_le _ j

section SumBlocks

variable {β : Type*} [Fintype β] [DecidableEq β]

theorem norm_fromBlocks_zero_left (A : Matrix ι ι ℂ) :
    ‖(Matrix.fromBlocks A 0 0 0 : Matrix (ι ⊕ β) (ι ⊕ β) ℂ)‖ = ‖A‖ := by
  let J : Matrix (ι ⊕ β) ι ℂ := coordinateInclusion Sum.inl
  have hJ : ‖J‖ ≤ 1 :=
    coordinateInclusion_norm_le Sum.inl Sum.inl_injective
  have heq : (Matrix.fromBlocks A 0 0 0 : Matrix (ι ⊕ β) (ι ⊕ β) ℂ) =
      J * A * J.conjTranspose := by
    ext i j
    cases i <;> cases j <;>
      simp [J, coordinateInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply le_antisymm
  · rw [heq]
    calc
      ‖J * A * J.conjTranspose‖ ≤ ‖J‖ * ‖A‖ * ‖J.conjTranspose‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ 1 * ‖A‖ * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
      _ = ‖A‖ := by ring
  · simpa using submatrix_operator_norm_le
      (Matrix.fromBlocks A 0 0 0 : Matrix (ι ⊕ β) (ι ⊕ β) ℂ)
      Sum.inl Sum.inl Sum.inl_injective Sum.inl_injective

theorem norm_fromBlocks_zero_right (A : Matrix β β ℂ) :
    ‖(Matrix.fromBlocks 0 0 0 A : Matrix (ι ⊕ β) (ι ⊕ β) ℂ)‖ = ‖A‖ := by
  have h := submatrix_operator_norm_equiv
    (Matrix.fromBlocks 0 0 0 A : Matrix (ι ⊕ β) (ι ⊕ β) ℂ) (Equiv.sumComm β ι)
  have heq :
      (Matrix.fromBlocks 0 0 0 A : Matrix (ι ⊕ β) (ι ⊕ β) ℂ).submatrix
        (Equiv.sumComm β ι) (Equiv.sumComm β ι) = Matrix.fromBlocks A 0 0 0 := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [heq, norm_fromBlocks_zero_left] at h
  exact h.symm

end SumBlocks

section Relabel

variable {γ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype γ] [DecidableEq γ] [Nonempty γ]

theorem pavingNorm_relabel (A : Matrix ι ι ℂ) (c : ι → κ) (e : κ ≃ γ) :
    pavingNorm A (e ∘ c) = pavingNorm A c := by
  have hc (b : γ) : colorClass (e ∘ c) b = colorClass c (e.symm b) := by
    ext i
    simp only [mem_colorClass, Function.comp_apply, Equiv.apply_eq_iff_eq_symm_apply]
  apply le_antisymm
  · apply pavingNorm_le
    intro b
    rw [hc]
    exact compression_norm_le_pavingNorm A c _
  · apply pavingNorm_le
    intro a
    have h := compression_norm_le_pavingNorm A (e ∘ c) (e a)
    simpa only [hc, Equiv.symm_apply_apply] using h

end Relabel

end PavingSeparation
