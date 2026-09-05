import NoEpsilon.ThreeHermitian

/-!
# A simultaneous hollow and almost-hollow basis

The common-neutral-vector theorem is iterated until only two dimensions remain.
The resulting unitary makes the first two Hermitian matrices hollow and the third
zero in its first `n - 2` diagonal entries.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace NoEpsilon
namespace ThreeHermitian

/-- Extend a Euclidean unit vector to the first column of a unitary matrix. -/
theorem unitary_first_column {n : ℕ} (v : Fin (n + 1) → ℂ) (hv : vectorEnergy v = 1) :
    ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      CommutatorTheorem.IsUnitaryMatrix U ∧ (∀ i, U i 0 = v i) := by
  let ve : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 v
  have hnorm : ‖ve‖ = 1 := by
    rw [vectorEnergy_eq_norm_sq] at hv
    change ‖ve‖ ^ 2 = 1 at hv
    nlinarith [norm_nonneg ve]
  let w : Fin (n + 1) → EuclideanSpace ℂ (Fin (n + 1)) :=
    fun i ↦ if i = 0 then ve else 0
  have horth : Orthonormal ℂ (({(0 : Fin (n + 1))} : Set (Fin (n + 1))).restrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst i
    subst j
    simp only [Set.restrict_apply, w, ite_true]
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 1))) =
      Fintype.card (Fin (n + 1)) := by simp
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  have hb₀ : b 0 = ve := by simpa [w] using hb 0 (Set.mem_singleton 0)
  let e := EuclideanSpace.basisFun (Fin (n + 1)) ℂ
  let U := e.toBasis.toMatrix (fun i ↦ b i)
  have hU : U ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ :=
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary e b
  refine ⟨U, ?_, ?_⟩
  · rw [Matrix.unitaryGroup, Unitary.mem_iff] at hU
    simp only [Matrix.star_eq_conjTranspose] at hU
    exact ⟨hU.2, hU.1⟩
  · intro i
    simp only [U, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      hb₀]
    rfl

/-- Put a scalar identity before a matrix, using `Fin.succ` for the lower block. -/
def extendUnitary {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j ↦ Fin.cases (Fin.cases 1 (fun _ ↦ 0) j)
    (fun i ↦ Fin.cases 0 (fun j ↦ V i j) j) i

@[simp] theorem extendUnitary_zero_zero {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) :
    extendUnitary V 0 0 = 1 := rfl

@[simp] theorem extendUnitary_zero_succ {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (j : Fin n) : extendUnitary V 0 j.succ = 0 := rfl

@[simp] theorem extendUnitary_succ_zero {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) : extendUnitary V i.succ 0 = 0 := rfl

@[simp] theorem extendUnitary_succ_succ {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : extendUnitary V i.succ j.succ = V i j := rfl

theorem extendUnitary_one {n : ℕ} :
    extendUnitary (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [Matrix.one_apply, eq_comm]

theorem extendUnitary_adjoint {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) :
    (extendUnitary V)ᴴ = extendUnitary Vᴴ := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [Matrix.conjTranspose_apply]

theorem extendUnitary_mul {n : ℕ} (V W : Matrix (Fin n) (Fin n) ℂ) :
    extendUnitary V * extendUnitary W = extendUnitary (V * W) := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    refine Fin.cases ?_ (fun j ↦ ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem extendUnitary_isUnitary {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : CommutatorTheorem.IsUnitaryMatrix V) :
    CommutatorTheorem.IsUnitaryMatrix (extendUnitary V) := by
  constructor
  · rw [extendUnitary_adjoint, extendUnitary_mul, hV.1, extendUnitary_one]
  · rw [extendUnitary_adjoint, extendUnitary_mul, hV.2, extendUnitary_one]

theorem extendUnitary_conjugate_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (V : Matrix (Fin n) (Fin n) ℂ) :
    ((extendUnitary V)ᴴ * A * extendUnitary V) 0 0 = A 0 0 := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem extendUnitary_conjugate_succ {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    ((extendUnitary V)ᴴ * A * extendUnitary V) i.succ j.succ =
      (Vᴴ * A.submatrix Fin.succ Fin.succ * V) i j := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem trace_submatrix_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix.trace (A.submatrix Fin.succ Fin.succ) = Matrix.trace A - A 0 0 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

/-- Damm--Faßbender's simultaneous hollowization conclusion: the first two
trace-zero Hermitian matrices become hollow and the third has at most its last
two diagonal entries nonzero. -/
theorem exists_almost_hollow (n : ℕ) :
    ∀ H G E : Matrix (Fin n) (Fin n) ℂ,
    H.IsHermitian → G.IsHermitian → E.IsHermitian →
    Matrix.trace H = 0 → Matrix.trace G = 0 → Matrix.trace E = 0 →
    ∃ U : Matrix (Fin n) (Fin n) ℂ, CommutatorTheorem.IsUnitaryMatrix U ∧
      (∀ i, (Uᴴ * H * U) i i = 0) ∧ (∀ i, (Uᴴ * G * U) i i = 0) ∧
      (∀ i, i.val + 2 < n → (Uᴴ * E * U) i i = 0) := by
  induction n with
  | zero =>
    intro H G E hH hG hE htrH htrG htrE
    exact ⟨1, ⟨by simp, by simp⟩, fun i ↦ i.elim0, fun i ↦ i.elim0,
      fun i ↦ i.elim0⟩
  | succ n ih =>
    intro H G E hH hG hE htrH htrG htrE
    by_cases hsmall : n + 1 ≤ 2
    · obtain ⟨U, hU, hHU, hGU⟩ := exists_simultaneously_hollow H G hH hG htrH htrG
      exact ⟨U, hU, hHU, hGU, fun i hi ↦ by omega⟩
    have hn : 3 ≤ n + 1 := by omega
    obtain ⟨v, hv, hHv, hGv, hEv⟩ := exists_unit_common_neutral
      H G E hH hG hE htrH htrG htrE hn
    obtain ⟨U, hU, hcol⟩ := unitary_first_column v hv
    have hcorner (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (hAv : rayleighValue A v = 0) : (Uᴴ * A * U) 0 0 = 0 := by
      rw [gram_diagonal]
      convert hAv using 1
      exact congrArg (rayleighValue A) (funext hcol)
    have htrace (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (htrA : Matrix.trace A = 0) (hAv : rayleighValue A v = 0) :
        Matrix.trace ((Uᴴ * A * U).submatrix Fin.succ Fin.succ) = 0 := by
      rw [trace_submatrix_succ, hcorner A hAv, sub_zero, Matrix.trace_mul_cycle,
        hU.1, Matrix.one_mul, htrA]
    obtain ⟨V, hV, hHV, hGV, hEV⟩ := ih
      ((Uᴴ * H * U).submatrix Fin.succ Fin.succ)
      ((Uᴴ * G * U).submatrix Fin.succ Fin.succ)
      ((Uᴴ * E * U).submatrix Fin.succ Fin.succ)
      ((isHermitian_compression H hH U).submatrix Fin.succ)
      ((isHermitian_compression G hG U).submatrix Fin.succ)
      ((isHermitian_compression E hE U).submatrix Fin.succ)
      (htrace H htrH hHv) (htrace G htrG hGv) (htrace E htrE hEv)
    let S := extendUnitary V
    have hS := extendUnitary_isUnitary V hV
    have hUS : CommutatorTheorem.IsUnitaryMatrix (U * S) := by
      constructor
      · simp only [Matrix.conjTranspose_mul]
        calc
          U * S * (Sᴴ * Uᴴ) = U * (S * Sᴴ) * Uᴴ := by noncomm_ring
          _ = 1 := by rw [hS.1, Matrix.mul_one, hU.1]
      · simp only [Matrix.conjTranspose_mul]
        calc
          Sᴴ * Uᴴ * (U * S) = Sᴴ * (Uᴴ * U) * S := by noncomm_ring
          _ = 1 := by rw [hU.2, Matrix.mul_one, hS.2]
    have hcomp (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
        (U * S)ᴴ * A * (U * S) = Sᴴ * (Uᴴ * A * U) * S := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    refine ⟨U * S, hUS, ?_, ?_, ?_⟩
    · intro i
      rw [hcomp]
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact (extendUnitary_conjugate_zero _ V).trans (hcorner H hHv)
      · exact (extendUnitary_conjugate_succ _ V j j).trans (hHV j)
    · intro i
      rw [hcomp]
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact (extendUnitary_conjugate_zero _ V).trans (hcorner G hGv)
      · exact (extendUnitary_conjugate_succ _ V j j).trans (hGV j)
    · intro i
      rw [hcomp]
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · intro _
        exact (extendUnitary_conjugate_zero _ V).trans (hcorner E hEv)
      · intro hj
        exact (extendUnitary_conjugate_succ _ V j j).trans (hEV j (by
          simp only [Fin.val_succ] at hj
          omega))

/-- If a nonnegative family is equal to its average except possibly at its final
two indices, every entry is at most twice that average. -/
theorem diagonal_le_two_mean (n : ℕ) :
    ∀ (f : Fin n → ℝ) (a : ℝ), 0 ≤ a → (∀ i, 0 ≤ f i) →
    (∑ i, f i) = n * a → (∀ i, i.val + 2 < n → f i = a) →
    ∀ i, f i ≤ 2 * a := by
  induction n with
  | zero => intro f a ha hf hsum hflat i; exact i.elim0
  | succ n ih =>
    intro f a ha hf hsum hflat
    by_cases hn : n + 1 ≤ 2
    · intro i
      calc
        f i ≤ ∑ j, f j := Finset.single_le_sum (fun j _ ↦ hf j) (Finset.mem_univ i)
        _ = (n + 1) * a := by simpa only [Nat.cast_add, Nat.cast_one] using hsum
        _ ≤ 2 * a := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ha
    have hf₀ : f 0 = a := hflat 0 (by simp only [Fin.val_zero]; omega)
    have hsum' : (∑ i : Fin n, f i.succ) = n * a := by
      rw [Fin.sum_univ_succ, hf₀, Nat.cast_add, Nat.cast_one] at hsum
      linarith
    have hchild := ih (fun i ↦ f i.succ) a ha (fun i ↦ hf i.succ) hsum'
      (fun i hi ↦ hflat i.succ (by simp only [Fin.val_succ]; omega))
    intro i
    refine Fin.cases ?_ (fun j ↦ hchild j) i
    rw [hf₀]
    linarith

def centered {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A - (Matrix.trace A / (n : ℂ)) • 1

theorem centered_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) : (centered A).IsHermitian := by
  apply hA.sub
  apply Matrix.isHermitian_one.smul
  change star (Matrix.trace A / (n : ℂ)) = Matrix.trace A / (n : ℂ)
  rw [star_div₀, star_natCast, ← Matrix.trace_conjTranspose, hA.eq]

theorem centered_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hn : n ≠ 0) :
    Matrix.trace (centered A) = 0 := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [centered, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, div_mul_cancel₀ _ hn', sub_self]

theorem centered_unitary_diagonal {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : CommutatorTheorem.IsUnitaryMatrix U) (i : Fin n) :
    (Uᴴ * centered A * U) i i = (Uᴴ * A * U) i i - Matrix.trace A / (n : ℂ) := by
  simp [centered, Matrix.mul_sub, Matrix.sub_mul, hU.2]

/-- The quantitative three-Hermitian basis used by the low-mass paving argument.
The first two diagonals are exactly constant. For a positive semidefinite third
matrix every new diagonal is at most twice its mean. The zero-dimensional case
is included, with vacuous diagonal conclusions. -/
theorem exists_diagonal_control {n : ℕ} (H G E : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hG : G.IsHermitian) (hE : E.PosSemidef) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, CommutatorTheorem.IsUnitaryMatrix U ∧
      (∀ i, (Uᴴ * H * U) i i = Matrix.trace H / (n : ℂ)) ∧
      (∀ i, (Uᴴ * G * U) i i = Matrix.trace G / (n : ℂ)) ∧
      (∀ i, ((Uᴴ * E * U) i i).re ≤ 2 * (Matrix.trace E).re / (n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨1, ⟨by simp, by simp⟩, fun i ↦ i.elim0, fun i ↦ i.elim0,
      fun i ↦ i.elim0⟩
  obtain ⟨U, hU, hHd, hGd, hEd⟩ := exists_almost_hollow n
    (centered H) (centered G) (centered E)
    (centered_isHermitian H hH) (centered_isHermitian G hG)
    (centered_isHermitian E hE.1) (centered_trace H hn)
    (centered_trace G hn) (centered_trace E hn)
  have hHd' (i : Fin n) : (Uᴴ * H * U) i i = Matrix.trace H / (n : ℂ) := by
    exact sub_eq_zero.mp ((centered_unitary_diagonal H U hU i).symm.trans (hHd i))
  have hGd' (i : Fin n) : (Uᴴ * G * U) i i = Matrix.trace G / (n : ℂ) := by
    exact sub_eq_zero.mp ((centered_unitary_diagonal G U hU i).symm.trans (hGd i))
  let a : ℝ := (Matrix.trace E).re / (n : ℝ)
  have ha : 0 ≤ a := div_nonneg (Complex.nonneg_iff.mp hE.trace_nonneg).1 (Nat.cast_nonneg n)
  have hpos : (Uᴴ * E * U).PosSemidef := hE.conjTranspose_mul_mul_same U
  have hflat (i : Fin n) (hi : i.val + 2 < n) : ((Uᴴ * E * U) i i).re = a := by
    have h := sub_eq_zero.mp ((centered_unitary_diagonal E U hU i).symm.trans (hEd i hi))
    simpa only [a, Complex.div_natCast_re] using congrArg Complex.re h
  have hsum : (∑ i, ((Uᴴ * E * U) i i).re) = n * a := by
    rw [← Complex.re_sum]
    change (Matrix.trace (Uᴴ * E * U)).re = n * a
    rw [Matrix.trace_mul_cycle, hU.1, Matrix.one_mul]
    dsimp [a]
    field_simp
  have hbound := diagonal_le_two_mean n (fun i ↦ ((Uᴴ * E * U) i i).re) a ha
    (fun _ ↦ (Complex.nonneg_iff.mp hpos.diag_nonneg).1) hsum hflat
  refine ⟨U, hU, hHd', hGd', fun i ↦ ?_⟩
  simpa only [a, mul_div_assoc] using hbound i

end ThreeHermitian
end NoEpsilon
