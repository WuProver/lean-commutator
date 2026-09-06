import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# The recursive skew-Hadamard family

The indexing type records the original recursive coordinates. All matrix norms in this file are
the Euclidean operator norm.
-/

open scoped ComplexConjugate
open Matrix

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedSpace Matrix.instCStarRing

namespace PavingSeparation

/-- Original coordinates of a matrix of order `2 ^ m`. -/
@[reducible] def Cube : ℕ → Type
  | 0 => Fin 1
  | m + 1 => Cube m ⊕ Cube m

@[reducible] def cubeFintype : (m : ℕ) → Fintype (Cube m)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | m + 1 => letI := cubeFintype m; inferInstanceAs (Fintype (Cube m ⊕ Cube m))

attribute [instance] cubeFintype

@[reducible] def cubeDecidableEq : (m : ℕ) → DecidableEq (Cube m)
  | 0 => inferInstanceAs (DecidableEq (Fin 1))
  | m + 1 => letI := cubeDecidableEq m; inferInstanceAs (DecidableEq (Cube m ⊕ Cube m))

attribute [instance] cubeDecidableEq

def origin : (m : ℕ) → Cube m
  | 0 => 0
  | m + 1 => Sum.inl (origin m)

instance (m : ℕ) : Inhabited (Cube m) := ⟨origin m⟩

@[simp] theorem card_cube (m : ℕ) : Fintype.card (Cube m) = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change Fintype.card (Cube m ⊕ Cube m) = 2 ^ (m + 1)
      simp [ih, pow_succ, Nat.mul_two]

/-- The skew-Hadamard doubling recursion in the original coordinates. -/
noncomputable def skew : (m : ℕ) → Matrix (Cube m) (Cube m) ℂ
  | 0 => 0
  | m + 1 => fromBlocks (skew m) (skew m + 1) (skew m - 1) (-skew m)

@[simp] theorem skew_zero : skew 0 = 0 := rfl

theorem skew_succ (m : ℕ) :
    skew (m + 1) = fromBlocks (skew m) (skew m + 1) (skew m - 1) (-skew m) := rfl

@[simp] theorem skew_inl_inl (m : ℕ) (i j : Cube m) :
    skew (m + 1) (Sum.inl i) (Sum.inl j) = skew m i j := rfl

@[simp] theorem skew_inr_inr (m : ℕ) (i j : Cube m) :
    skew (m + 1) (Sum.inr i) (Sum.inr j) = -skew m i j := rfl

@[simp] theorem skew_inl_inr (m : ℕ) (i j : Cube m) :
    skew (m + 1) (Sum.inl i) (Sum.inr j) = (skew m + 1) i j := rfl

@[simp] theorem skew_inr_inl (m : ℕ) (i j : Cube m) :
    skew (m + 1) (Sum.inr i) (Sum.inl j) = (skew m - 1) i j := rfl

@[simp] theorem skew_diag (m : ℕ) (i : Cube m) : skew m i i = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => cases i <;> simp [ih]

theorem skew_offdiag_eq_one_or_neg_one (m : ℕ) {i j : Cube m} (hij : i ≠ j) :
    skew m i j = 1 ∨ skew m i j = -1 := by
  induction m with
  | zero => exact (hij (Subsingleton.elim _ _)).elim
  | succ m ih =>
      cases i with
      | inl i =>
          cases j with
          | inl j => exact ih (fun h ↦ hij (congrArg Sum.inl h))
          | inr j =>
              by_cases h : i = j
              · subst j; simp
              · simpa [h] using ih h
      | inr i =>
          cases j with
          | inl j =>
              by_cases h : i = j
              · subst j; simp
              · simpa [h] using ih h
          | inr j =>
              rcases ih (fun h ↦ hij (congrArg Sum.inr h)) with h | h
              · simp [h]
              · simp [h]

@[simp] theorem skew_offdiag_norm (m : ℕ) {i j : Cube m} (hij : i ≠ j) :
    ‖skew m i j‖ = 1 := by
  rcases skew_offdiag_eq_one_or_neg_one m hij with h | h <;> simp [h]

@[simp] theorem skew_conj_apply (m : ℕ) (i j : Cube m) :
    star (skew m i j) = skew m i j := by
  by_cases hij : i = j
  · subst j; simp
  · rcases skew_offdiag_eq_one_or_neg_one m hij with h | h <;> simp [h]

theorem skew_conjTranspose (m : ℕ) : (skew m)ᴴ = -skew m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [skew_succ, fromBlocks_conjTranspose, fromBlocks_neg]
      simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_neg, conjTranspose_one, ih]
      congr 1 <;> abel

theorem skew_transpose (m : ℕ) : (skew m)ᵀ = -skew m := by
  ext i j
  have h := congrFun (congrFun (skew_conjTranspose m) i) j
  simpa only [conjTranspose_apply, skew_conj_apply, transpose_apply] using h

theorem skew_mul_self (m : ℕ) :
    skew m * skew m = (-((2 : ℂ) ^ m - 1)) • (1 : Matrix (Cube m) (Cube m) ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [skew_succ, fromBlocks_multiply]
      have hdiag : skew m * skew m + (skew m + 1) * (skew m - 1) =
          (-((2 : ℂ) ^ (m + 1) - 1)) • (1 : Matrix (Cube m) (Cube m) ℂ) := by
        calc
          _ = skew m * skew m + skew m * skew m - 1 := by noncomm_ring
          _ = _ := by
            rw [ih]
            ext i j
            simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
            rw [pow_succ]
            ring
      have hoff : skew m * (skew m + 1) + (skew m + 1) * -skew m = 0 := by
        noncomm_ring
      have hother : (skew m - 1) * skew m + -skew m * (skew m - 1) = 0 := by
        noncomm_ring
      have hdiag' : (skew m - 1) * (skew m + 1) + -skew m * -skew m =
          (-((2 : ℂ) ^ (m + 1) - 1)) • (1 : Matrix (Cube m) (Cube m) ℂ) := by
        convert hdiag using 1; noncomm_ring
      rw [hdiag, hoff, hother, hdiag']
      rw [← fromBlocks_one, fromBlocks_smul]
      simp

theorem order_sub_one_nonneg (m : ℕ) : 0 ≤ (2 : ℝ) ^ m - 1 := by
  have h : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  linarith

theorem order_sub_one_pos {m : ℕ} (hm : 0 < m) : 0 < (2 : ℝ) ^ m - 1 := by
  have h : (1 : ℝ) < 2 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
  linarith

theorem skew_norm (m : ℕ) : ‖skew m‖ = Real.sqrt ((2 : ℝ) ^ m - 1) := by
  have hstar : (skew m)ᴴ * skew m =
      (((2 : ℝ) ^ m - 1 : ℝ) : ℂ) • (1 : Matrix (Cube m) (Cube m) ℂ) := by
    rw [skew_conjTranspose, neg_mul, skew_mul_self, ← neg_smul, neg_neg]
    congr 1
    push_cast
    rfl
  have hn := Matrix.l2_opNorm_conjTranspose_mul_self (skew m)
  rw [hstar, norm_smul, CStarRing.norm_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (order_sub_one_nonneg m)] at hn
  apply le_antisymm
  · apply (Real.le_sqrt (norm_nonneg _) (order_sub_one_nonneg m)).2
    nlinarith
  · apply (Real.sqrt_le_iff).2
    exact ⟨norm_nonneg _, by nlinarith⟩

/-- The normalized Hermitian skew-Hadamard family; at depth zero it is zero. -/
noncomputable def family (m : ℕ) : Matrix (Cube m) (Cube m) ℂ :=
  (Complex.I / (Real.sqrt ((2 : ℝ) ^ m - 1) : ℂ)) • skew m

@[simp] theorem family_zero : family 0 = 0 := by simp [family]

@[simp] theorem family_diag (m : ℕ) (i : Cube m) : family m i i = 0 := by
  simp [family]

@[simp] theorem family_trace (m : ℕ) : Matrix.trace (family m) = 0 := by
  simp [Matrix.trace]

theorem family_isHermitian (m : ℕ) : (family m).IsHermitian := by
  change (family m)ᴴ = family m
  rw [family, conjTranspose_smul, skew_conjTranspose]
  simp only [star_div₀, Complex.star_def, Complex.conj_I, Complex.conj_ofReal, neg_div,
    neg_smul_neg]

theorem family_mul_self {m : ℕ} (hm : 0 < m) :
    family m * family m = (1 : Matrix (Cube m) (Cube m) ℂ) := by
  have hr : Real.sqrt ((2 : ℝ) ^ m - 1) ≠ 0 :=
    (Real.sqrt_pos.2 (order_sub_one_pos hm)).ne'
  have hrc : (Real.sqrt ((2 : ℝ) ^ m - 1) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hsq : (Real.sqrt ((2 : ℝ) ^ m - 1) : ℂ) ^ 2 = (2 : ℂ) ^ m - 1 := by
    have h := Real.sq_sqrt (order_sub_one_nonneg m)
    exact_mod_cast h
  rw [family, smul_mul_smul, skew_mul_self, smul_smul]
  have hcoef :
      (Complex.I / (Real.sqrt ((2 : ℝ) ^ m - 1) : ℂ) *
        (Complex.I / (Real.sqrt ((2 : ℝ) ^ m - 1) : ℂ))) *
        (-((2 : ℂ) ^ m - 1)) = 1 := by
    field_simp
    rw [← hsq]
    simp [Complex.I_sq]
  rw [hcoef, one_smul]

theorem family_mem_unitaryGroup {m : ℕ} (hm : 0 < m) :
    family m ∈ Matrix.unitaryGroup (Cube m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    (family_isHermitian m).eq]
  exact family_mul_self hm

theorem family_norm {m : ℕ} (hm : 0 < m) : ‖family m‖ = 1 := by
  have hr := Real.sqrt_pos.2 (order_sub_one_pos hm)
  rw [family, norm_smul, norm_div, Complex.norm_I, Complex.norm_real,
    Real.norm_of_nonneg hr.le, skew_norm]
  exact one_div_mul_cancel hr.ne'

theorem family_offdiag_norm (m : ℕ) {i j : Cube m} (hij : i ≠ j) :
    ‖family m i j‖ = 1 / Real.sqrt ((2 : ℝ) ^ m - 1) := by
  simp only [family, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_div, Complex.norm_I,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), skew_offdiag_norm m hij,
    mul_one]

theorem family_offdiag_norm_sq (m : ℕ) {i j : Cube m} (hij : i ≠ j) :
    ‖family m i j‖ ^ 2 = 1 / ((2 : ℝ) ^ m - 1) := by
  rw [family_offdiag_norm m hij, div_pow, one_pow,
    Real.sq_sqrt (order_sub_one_nonneg m)]

theorem family_offdiag_normSq (m : ℕ) {i j : Cube m} (hij : i ≠ j) :
    Complex.normSq (family m i j) = 1 / ((2 : ℝ) ^ m - 1) := by
  rw [Complex.normSq_eq_norm_sq, family_offdiag_norm_sq m hij]

end PavingSeparation
