import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Core Definitions for the Quantitative Commutator Theorem

This file contains the core definitions used in the formalization of the
quantitative commutator theorem (JOS 2013).
-/

-- Enable the L2 operator norm on square complex matrices
attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing

namespace CommutatorTheorem

/-! ## Commutator bracket -/

/-- The matrix commutator [A, B] = AB - BA. -/
noncomputable def matComm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

notation:65 "⁅" A ", " B "⁆ₘ" => matComm A B

/-! ## Zero-diagonal predicate -/

/-- A matrix has zero diagonal if all diagonal entries vanish. -/
def ZeroDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i, A i i = 0

/-- A matrix is diagonal if all off-diagonal entries vanish. -/
def IsDiagMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j : Fin n, i ≠ j → A i j = 0

/-! ## Operator norm bridge lemma -/

/-- The default norm on `Matrix (Fin n) (Fin n) ℂ` (from `Matrix.instL2OpNormedRing`)
    equals the operator norm of the corresponding continuous linear map. -/
lemma matOpNorm_eq_clm_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A‖ = ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖ :=
  Matrix.l2_opNorm_def A

/-! ## Hilbert-Schmidt norm -/

/-- The Hilbert-Schmidt (Frobenius) norm of a matrix,
    defined as the square root of the sum of squared entry absolute values.
    We define it directly as a `def` (not via a `NormedSpace` instance)
    to avoid conflicts with the L2 operator norm instance. -/
noncomputable def hsNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j))

scoped[CommutatorTheorem] notation:max "‖" A "‖ₕₛ" => hsNorm A

lemma hsNorm_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsNorm A := by
  unfold hsNorm
  exact Real.sqrt_nonneg _

lemma hsNorm_zero {n : ℕ} : hsNorm (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  unfold hsNorm
  simp [Complex.normSq_zero]

lemma hsNorm_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    hsNorm (c • A) = ‖c‖ * hsNorm A := by
  simp only [hsNorm, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, ← Finset.mul_sum]
  rw [Real.sqrt_mul (Complex.normSq_nonneg c), Complex.norm_def]

private lemma complex_normSq_sum_mul_le {n : ℕ} (f g : Fin n → ℂ) :
    Complex.normSq (∑ j, f j * g j) ≤
      (∑ j, Complex.normSq (f j)) * (∑ j, Complex.normSq (g j)) := by
  calc Complex.normSq (∑ j, f j * g j)
      = ‖∑ j, f j * g j‖ ^ 2 := by rw [Complex.normSq_eq_norm_sq]
    _ ≤ (∑ j, ‖f j * g j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ = (∑ j, ‖f j‖ * ‖g j‖) ^ 2 := by
        congr 1; congr 1; ext j; exact norm_mul _ _
    _ ≤ (∑ j, ‖f j‖ ^ 2) * (∑ j, ‖g j‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ j, Complex.normSq (f j)) * (∑ j, Complex.normSq (g j)) := by
        congr 1 <;> (congr 1; ext j; rw [Complex.normSq_eq_norm_sq])

/-- The operator norm is at most the Hilbert-Schmidt norm. -/
lemma le_hsNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ≤ hsNorm A := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (hsNorm_nonneg A)
  intro x
  simp only [LinearEquiv.trans_apply]
  change ‖Matrix.toEuclideanLin A x‖ ≤ hsNorm A * ‖x‖
  rw [show Matrix.toEuclideanLin A x = WithLp.toLp 2 (A.mulVec x.ofLp) from
    Matrix.toLpLin_apply 2 2 A x]
  set v := x.ofLp
  set w := A.mulVec v
  apply le_of_sq_le_sq _ (mul_nonneg (hsNorm_nonneg A) (norm_nonneg x))
  have norm_x_sq : ‖x‖ ^ 2 = ∑ j, Complex.normSq (v j) := by
    rw [EuclideanSpace.norm_eq x,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
    congr 1; ext j; rw [Complex.normSq_eq_norm_sq]
  rw [show ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ =
      Real.sqrt (∑ i, ‖w i‖ ^ 2) from EuclideanSpace.norm_eq _,
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2)),
      mul_pow,
      show hsNorm A ^ 2 = ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j) from by
        unfold hsNorm; rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ =>
          Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)))],
      norm_x_sq]
  have hw : ∀ i, ‖w i‖ ^ 2 = Complex.normSq (∑ j, A i j * v j) := by
    intro i; rw [← Complex.normSq_eq_norm_sq]; rfl
  simp_rw [hw]
  calc ∑ i, Complex.normSq (∑ j, A i j * v j)
      ≤ ∑ i, (∑ j, Complex.normSq (A i j)) * (∑ j, Complex.normSq (v j)) :=
        Finset.sum_le_sum (fun i _ => complex_normSq_sum_mul_le _ _)
    _ = _ := by rw [← Finset.sum_mul]

/-- The Hilbert-Schmidt norm is at most √n times the operator norm. -/
lemma hsNorm_le_sqrt_n_mul_opNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    hsNorm A ≤ Real.sqrt n * ‖A‖ := by
  unfold hsNorm
  rw [show Real.sqrt ↑n * ‖A‖ = Real.sqrt (↑n * ‖A‖ ^ 2) from by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg A)]]
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_comm]
  have hcol : ∀ j : Fin n, ∑ i, Complex.normSq (A i j) ≤ ‖A‖ ^ 2 := by
    intro j
    set f := (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A
    set ej := EuclideanSpace.single j (1 : ℂ)
    have hfej : ‖f ej‖ ≤ ‖A‖ := by
      calc ‖f ej‖ ≤ ‖f‖ * ‖ej‖ := ContinuousLinearMap.le_opNorm f ej
        _ = ‖A‖ * 1 := by rw [← Matrix.l2_opNorm_def, PiLp.norm_single 2, norm_one]
        _ = ‖A‖ := mul_one _
    suffices h : ∑ i, Complex.normSq (A i j) = ‖f ej‖ ^ 2 by
      rw [h]; exact pow_le_pow_left₀ (norm_nonneg _) hfej 2
    have : f ej = WithLp.toLp 2 (A.mulVec (Pi.single j 1)) := by
      change (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A ej = _
      simp [LinearEquiv.trans_apply, Matrix.toLpLin_apply, ej, EuclideanSpace.single]
    rw [this, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
    congr 1; ext i
    rw [Complex.normSq_eq_norm_sq]
    congr 1
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
  calc ∑ j : Fin n, ∑ i, Complex.normSq (A i j)
      ≤ ∑ _j : Fin n, ‖A‖ ^ 2 := Finset.sum_le_sum (fun j _ => hcol j)
    _ = ↑n * ‖A‖ ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]

/-! ## Recursive lattice Λ -/

/-- The four corner points {±1 ± i} in ℂ used to build the lattice. -/
noncomputable def cornerSet : Finset ℂ :=
  {⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩}

/-- The recursive lattice Λ_n(ε). At level 0, Λ = {±1 ± i}.
    At level n+1, each point of Λ_n is scaled by (1-ε)/2 and shifted by a corner. -/
noncomputable def Lambda (ε : ℝ) : ℕ → Finset ℂ
  | 0 => cornerSet
  | (n + 1) => cornerSet.biUnion fun δ =>
      (Lambda ε n).image (fun z => ((1 - ε) / 2 : ℂ) * z + δ)

/-! ## Minimum norm over decompositions μ(A, n) -/

/-- `mu ε n A` is the infimum of ‖C‖ over all decompositions A = [B, C]
    with B diagonal having entries in Λ_n(ε). -/
noncomputable def mu {m : ℕ} (ε : ℝ) (n : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sInf {c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
    IsDiagMatrix B ∧
    (∀ i, B i i ∈ (Lambda ε n : Set ℂ)) ∧
    A = ⁅B, C⁆ₘ ∧
    ‖C‖ ≤ c}

/-! ## Maximum of μ over unit-norm zero-diagonal matrices Λ(m) -/

/-- `Lambda_m ε m` is the supremum of `mu ε m A` over all unit-norm zero-diagonal m×m matrices. -/
noncomputable def Lambda_m (ε : ℝ) (m : ℕ) : ℝ :=
  sSup {y : ℝ | ∃ (A : Matrix (Fin m) (Fin m) ℂ),
    ZeroDiag A ∧ ‖A‖ = 1 ∧ y = mu ε m A}

/-! ## Unit square predicate -/

/-- The complex number is in the unit square if its real and imaginary parts are in [-1, 1]. -/
def InUnitSquare (z : ℂ) : Prop := |z.re| ≤ 1 ∧ |z.im| ≤ 1

/-! ## The paper's λ(A) and λ(m) (JOS 2013, Section "The Main Result") -/

/-- `lambdaA A` is the infimum of ‖C‖ over all decompositions A = [B, C]
    where B is diagonal with entries in the unit square [-1,1]×[-i,i].
    This is the paper's λ(A). -/
noncomputable def lambdaA {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sInf {c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
    IsDiagMatrix B ∧
    (∀ i, InUnitSquare (B i i)) ∧
    A = ⁅B, C⁆ₘ ∧
    ‖C‖ ≤ c}

/-- `lambdaM m` is the supremum of `lambdaA A` over all m×m zero-diagonal norm-one matrices.
    This is the paper's λ(m). -/
noncomputable def lambdaM (m : ℕ) : ℝ :=
  sSup (lambdaA '' {A : Matrix (Fin m) (Fin m) ℂ | ZeroDiag A ∧ ‖A‖ = 1})

/-! ## Submatrix / block operator norm bounds -/

/-- Submatrix norm bound: for an injective embedding `f : Fin n → Fin m`, the
    principal submatrix `A(f·, f·)` has operator norm at most `‖A‖`. -/
lemma submatrix_norm_le {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (A : Matrix (Fin m) (Fin m) ℂ) :
    ‖Matrix.of (fun i j => A (f i) (f j))‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simp only [LinearEquiv.trans_apply]
  change ‖Matrix.toEuclideanLin
    (Matrix.of (fun i j => A (f i) (f j))) x‖ ≤ ‖A‖ * ‖x‖
  rw [show Matrix.toEuclideanLin
      (Matrix.of (fun i j => A (f i) (f j))) x =
      WithLp.toLp 2
        ((Matrix.of (fun i j => A (f i) (f j))).mulVec x.ofLp)
    from Matrix.toLpLin_apply 2 2 _ x]
  set w := x.ofLp
  -- Pad w into Fin m via f
  set padW : Fin m → ℂ := fun i =>
    if h : ∃ j, f j = i then w (h.choose) else 0
  set v : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 padW
  -- padW at f j = w j
  have hpadW_f : ∀ j, padW (f j) = w j := by
    intro j
    simp only [padW]
    have h : ∃ k, f k = f j := ⟨j, rfl⟩
    simp only [h, dite_true]
    congr 1; exact hf h.choose_spec
  -- Component identity
  have hcomp : ∀ i : Fin n,
      ((Matrix.of (fun i j => A (f i) (f j))).mulVec w) i =
      (A.mulVec padW) (f i) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    symm
    calc ∑ j : Fin m, A (f i) j * padW j
        = ∑ j ∈ Finset.image f Finset.univ,
            A (f i) j * padW j +
          ∑ j ∈ (Finset.image f Finset.univ)ᶜ,
            A (f i) j * padW j := by
          rw [Finset.sum_add_sum_compl]
      _ = ∑ j ∈ Finset.image f Finset.univ,
            A (f i) j * padW j + 0 := by
          congr 1
          apply Finset.sum_eq_zero; intro j hj
          simp only [Finset.mem_compl, Finset.mem_image,
            Finset.mem_univ, true_and] at hj
          have : padW j = 0 := by
            simp only [padW]
            have : ¬∃ k, f k = j :=
              fun ⟨k, hk⟩ => hj ⟨k, hk⟩
            simp [this]
          rw [this, mul_zero]
      _ = ∑ j ∈ Finset.image f Finset.univ,
            A (f i) j * padW j := by rw [add_zero]
      _ = ∑ j : Fin n, A (f i) (f j) * padW (f j) := by
          rw [Finset.sum_image
            (fun i₁ _ i₂ _ h12 => hf h12)]
      _ = ∑ j : Fin n, A (f i) (f j) * w j := by
          congr 1; ext j; rw [hpadW_f]
  -- Squared norm comparison via embedding
  have sum_embed_le :
      ∀ (g : Fin m → ℝ), (∀ j, 0 ≤ g j) →
      ∑ i : Fin n, g (f i) ≤ ∑ j : Fin m, g j := by
    intro g hg
    calc ∑ i : Fin n, g (f i)
        = ∑ j ∈ Finset.image f Finset.univ, g j := by
          symm
          exact Finset.sum_image
            (fun i₁ _ i₂ _ h12 => hf h12)
      _ ≤ ∑ j : Fin m, g j :=
          Finset.sum_le_univ_sum_of_nonneg hg
  have hnorm_sq_le :
      ∑ i : Fin n,
        ‖((Matrix.of (fun i j =>
          A (f i) (f j))).mulVec w) i‖ ^ 2 ≤
      ∑ i : Fin m, ‖(A.mulVec padW) i‖ ^ 2 :=
    calc ∑ i : Fin n,
        ‖((Matrix.of (fun i j =>
          A (f i) (f j))).mulVec w) i‖ ^ 2
        = ∑ i : Fin n, ‖(A.mulVec padW) (f i)‖ ^ 2 := by
          congr 1; ext i; rw [hcomp]
      _ ≤ ∑ i : Fin m, ‖(A.mulVec padW) i‖ ^ 2 :=
          sum_embed_le _
            (fun j => pow_nonneg (norm_nonneg _) 2)
  -- ‖v‖ = ‖x‖
  have hv_norm : ‖v‖ = ‖x‖ := by
    simp only [EuclideanSpace.norm_eq]; congr 1
    have hsum_img :
        ∑ i : Fin m, ‖padW i‖ ^ 2 =
        ∑ i ∈ Finset.image f Finset.univ, ‖padW i‖ ^ 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not
        Finset.univ (· ∈ Finset.image f Finset.univ)]
      have : ∑ i ∈ Finset.univ.filter
          (· ∉ Finset.image f Finset.univ), ‖padW i‖ ^ 2 = 0 := by
        apply Finset.sum_eq_zero; intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_image] at hi
        simp [padW, hi]
      rw [this, add_zero]
      congr 1; ext i
      simp [Finset.mem_image]
    rw [hsum_img,
        Finset.sum_image (fun i₁ _ i₂ _ h12 => hf h12)]
    congr 1; ext i; rw [hpadW_f]
  -- Final bound
  apply le_of_sq_le_sq _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg
        (fun i _ => pow_nonneg (norm_nonneg _) 2)),
      mul_pow]
  set Av := (EuclideanSpace.equiv (Fin m) ℂ).symm
    (A.mulVec v.ofLp)
  have hAv : ‖Av‖ ≤ ‖A‖ * ‖v‖ :=
    Matrix.l2_opNorm_mulVec A v
  calc ∑ i : Fin n,
      ‖((Matrix.of (fun i j =>
        A (f i) (f j))).mulVec w) i‖ ^ 2
      ≤ ∑ i : Fin m, ‖(A.mulVec padW) i‖ ^ 2 :=
        hnorm_sq_le
    _ = ∑ i : Fin m, ‖Av.ofLp i‖ ^ 2 := by congr 1
    _ = ‖Av‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq,
            Real.sq_sqrt (Finset.sum_nonneg
              (fun i _ => pow_nonneg (norm_nonneg _) 2))]
    _ ≤ (‖A‖ * ‖v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hAv 2
    _ = ‖A‖ ^ 2 * ‖v‖ ^ 2 := mul_pow _ _ _
    _ = ‖A‖ ^ 2 * ‖x‖ ^ 2 := by rw [hv_norm]

/-- Cross-submatrix norm bound: for injective row/column embeddings f, g,
    the cross-submatrix A(f·, g·) has operator norm ≤ ‖A‖. -/
lemma cross_submatrix_norm_le {n p q : ℕ}
    (f : Fin p → Fin n) (g : Fin q → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.of (fun i j => A (f i) (g j))‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖Matrix.toEuclideanLin
    (Matrix.of (fun i j => A (f i) (g j))) x‖ ≤ ‖A‖ * ‖x‖
  rw [show Matrix.toEuclideanLin
      (Matrix.of (fun i j => A (f i) (g j))) x =
      WithLp.toLp 2
        ((Matrix.of (fun i j => A (f i) (g j))).mulVec x.ofLp)
    from Matrix.toLpLin_apply 2 2 _ x]
  set w := x.ofLp
  -- Pad w into Fin n via g
  set padW : Fin n → ℂ := fun i =>
    if h : ∃ j, g j = i then w (h.choose) else 0
  set v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 padW
  -- padW at g j = w j
  have hpadW_g : ∀ j, padW (g j) = w j := by
    intro j
    simp only [padW]
    have h : ∃ k, g k = g j := ⟨j, rfl⟩
    simp only [h, dite_true]
    congr 1; exact hg h.choose_spec
  -- Component identity: (A(f·,g·) * w)_i = (A * padW)(f i)
  have hcomp : ∀ i : Fin p,
      ((Matrix.of (fun i j => A (f i) (g j))).mulVec w) i =
      (A.mulVec padW) (f i) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    symm
    calc ∑ j : Fin n, A (f i) j * padW j
        = ∑ j ∈ Finset.image g Finset.univ,
            A (f i) j * padW j +
          ∑ j ∈ (Finset.image g Finset.univ)ᶜ,
            A (f i) j * padW j := by
          rw [Finset.sum_add_sum_compl]
      _ = ∑ j ∈ Finset.image g Finset.univ,
            A (f i) j * padW j + 0 := by
          congr 1
          apply Finset.sum_eq_zero; intro j hj
          simp only [Finset.mem_compl, Finset.mem_image,
            Finset.mem_univ, true_and] at hj
          have : padW j = 0 := by
            simp only [padW]
            have : ¬∃ k, g k = j :=
              fun ⟨k, hk⟩ => hj ⟨k, hk⟩
            simp [this]
          rw [this, mul_zero]
      _ = ∑ j ∈ Finset.image g Finset.univ,
            A (f i) j * padW j := by rw [add_zero]
      _ = ∑ j : Fin q, A (f i) (g j) * padW (g j) := by
          rw [Finset.sum_image
            (fun i₁ _ i₂ _ h12 => hg h12)]
      _ = ∑ j : Fin q, A (f i) (g j) * w j := by
          congr 1; ext j; rw [hpadW_g]
  -- ‖v‖ = ‖x‖
  have hv_norm : ‖v‖ = ‖x‖ := by
    simp only [EuclideanSpace.norm_eq]; congr 1
    have hsum_img :
        ∑ i : Fin n, ‖padW i‖ ^ 2 =
        ∑ i ∈ Finset.image g Finset.univ, ‖padW i‖ ^ 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not
        Finset.univ (· ∈ Finset.image g Finset.univ)]
      have : ∑ i ∈ Finset.univ.filter
          (· ∉ Finset.image g Finset.univ), ‖padW i‖ ^ 2 = 0 := by
        apply Finset.sum_eq_zero; intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_image] at hi
        simp [padW, hi]
      rw [this, add_zero]
      congr 1; ext i
      simp [Finset.mem_image]
    rw [hsum_img,
        Finset.sum_image (fun i₁ _ i₂ _ h12 => hg h12)]
    congr 1; ext i; rw [hpadW_g]
  -- Final bound
  set Av := (EuclideanSpace.equiv (Fin n) ℂ).symm
    (A.mulVec v.ofLp)
  have hAv : ‖Av‖ ≤ ‖A‖ * ‖v‖ :=
    Matrix.l2_opNorm_mulVec A v
  have hAv_def : Av.ofLp = A.mulVec padW := by ext i; rfl
  -- Squared norm comparison via embedding
  have sum_embed_le_f :
      ∀ (h : Fin n → ℝ), (∀ j, 0 ≤ h j) →
      ∑ i : Fin p, h (f i) ≤ ∑ j : Fin n, h j := by
    intro h hh
    calc ∑ i : Fin p, h (f i)
        = ∑ j ∈ Finset.image f Finset.univ, h j := by
          symm; exact Finset.sum_image (fun i₁ _ i₂ _ h12 => hf h12)
      _ ≤ ∑ j : Fin n, h j := Finset.sum_le_univ_sum_of_nonneg hh
  have hnorm_sq_le :
      ∑ i : Fin p,
        ‖((Matrix.of (fun i j =>
          A (f i) (g j))).mulVec w) i‖ ^ 2 ≤
      ∑ i : Fin n, ‖(A.mulVec padW) i‖ ^ 2 :=
    calc ∑ i : Fin p,
        ‖((Matrix.of (fun i j =>
          A (f i) (g j))).mulVec w) i‖ ^ 2
        = ∑ i : Fin p, ‖(A.mulVec padW) (f i)‖ ^ 2 := by
          congr 1; ext i; rw [hcomp]
      _ ≤ ∑ i : Fin n, ‖(A.mulVec padW) i‖ ^ 2 :=
          sum_embed_le_f _ (fun j => pow_nonneg (norm_nonneg _) 2)
  apply le_of_sq_le_sq _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg
        (fun i _ => pow_nonneg (norm_nonneg _) 2)),
      mul_pow]
  calc ∑ i : Fin p,
      ‖((Matrix.of (fun i j =>
        A (f i) (g j))).mulVec w) i‖ ^ 2
      ≤ ∑ i : Fin n, ‖(A.mulVec padW) i‖ ^ 2 :=
        hnorm_sq_le
    _ = ∑ i : Fin n, ‖Av.ofLp i‖ ^ 2 := by congr 1
    _ = ‖Av‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq,
            Real.sq_sqrt (Finset.sum_nonneg
              (fun i _ => pow_nonneg (norm_nonneg _) 2))]
    _ ≤ (‖A‖ * ‖v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hAv 2
    _ = ‖A‖ ^ 2 * ‖v‖ ^ 2 := mul_pow _ _ _
    _ = ‖A‖ ^ 2 * ‖x‖ ^ 2 := by rw [hv_norm]

/-- The operator norm of a block-diagonal matrix (4 blocks of size m)
    is at most the sup of the block norms.
    Proof: Pythagorean decomposition of ‖Mv‖² into block contributions. -/
lemma blockDiag_norm_le_of_blocks {m : ℕ}
    (Cs : Fin 4 → Matrix (Fin m) (Fin m) ℂ)
    (bound : ℝ) (hbd_nn : 0 ≤ bound)
    (hCs : ∀ k : Fin 4, ‖Cs k‖ ≤ bound) :
    let e : Fin 4 × Fin m ≃ Fin (4 * m) := finProdFinEquiv
    let M : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
      fun i j => if (e.symm i).1 = (e.symm j).1 then
        Cs (e.symm i).1 (e.symm i).2 (e.symm j).2 else 0
    ‖M‖ ≤ bound := by
  intro e M
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hbd_nn
  intro x
  change ‖Matrix.toEuclideanLin M x‖ ≤ bound * ‖x‖
  rw [show Matrix.toEuclideanLin M x = WithLp.toLp 2 (M.mulVec x.ofLp) from
    Matrix.toLpLin_apply 2 2 M x]
  set v := x.ofLp with hv_def
  let vB (k : Fin 4) : Fin m → ℂ := fun j => v (e (k, j))
  have hw_entry : ∀ r, M.mulVec v r =
      (Cs (e.symm r).1).mulVec (vB (e.symm r).1) (e.symm r).2 := by
    intro r; simp only [Matrix.mulVec, dotProduct, M]
    simp_rw [show ∀ c : Fin (4 * m),
        (if (e.symm r).1 = (e.symm c).1 then
          Cs (e.symm r).1 (e.symm r).2 (e.symm c).2 else 0) * v c =
        if (e.symm r).1 = (e.symm c).1 then
          Cs (e.symm r).1 (e.symm r).2 (e.symm c).2 * v c else 0
      from fun c => by split_ifs <;> simp]
    rw [← e.sum_comp (fun c => if (e.symm r).1 = (e.symm c).1 then
      Cs (e.symm r).1 (e.symm r).2 (e.symm c).2 * v c else 0)]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type]
    conv_lhs =>
      arg 2; ext k'
      rw [show ∑ j : Fin m,
          (if (e.symm r).1 = k' then
            Cs (e.symm r).1 (e.symm r).2 j * v (e (k', j)) else 0) =
          if (e.symm r).1 = k' then
            ∑ j, Cs (e.symm r).1 (e.symm r).2 j * v (e (k', j)) else 0
        from by split_ifs <;> simp]
    simp [vB]
  apply le_of_sq_le_sq _ (mul_nonneg hbd_nn (norm_nonneg x))
  have hlhs : ‖(WithLp.toLp 2 (M.mulVec v) :
      EuclideanSpace ℂ (Fin (4 * m)))‖ ^ 2 = ∑ r, ‖(M.mulVec v) r‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
  have hrhs : (bound * ‖x‖) ^ 2 = bound ^ 2 * ∑ r, ‖v r‖ ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_eq x,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
  rw [hlhs, hrhs]
  conv_lhs => rw [← e.sum_comp (fun r => ‖(M.mulVec v) r‖ ^ 2)]
  conv_rhs => rw [← e.sum_comp (fun r => ‖v r‖ ^ 2)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [show ∀ (k : Fin 4) (j : Fin m),
    ‖(M.mulVec v) (e (k, j))‖ = ‖(Cs k).mulVec (vB k) j‖ from
    fun k j => by rw [hw_entry]; simp]
  rw [show bound ^ 2 * ∑ k, ∑ j, ‖v (e (k, j))‖ ^ 2 =
    ∑ k : Fin 4, bound ^ 2 * ∑ j, ‖v (e (k, j))‖ ^ 2 from by
      rw [Finset.mul_sum]]
  apply Finset.sum_le_sum
  intro k _
  set xk := (EuclideanSpace.equiv (Fin m) ℂ).symm (vB k) with hxk_def
  have hle : ‖(EuclideanSpace.equiv _ ℂ).symm ((Cs k).mulVec (vB k))‖ ≤ bound * ‖xk‖ :=
    calc _ ≤ ‖Cs k‖ * ‖xk‖ := Matrix.l2_opNorm_mulVec (Cs k) xk
      _ ≤ bound * ‖xk‖ := mul_le_mul_of_nonneg_right (hCs k) (norm_nonneg _)
  have hle_sq : ‖(EuclideanSpace.equiv _ ℂ).symm ((Cs k).mulVec (vB k))‖ ^ 2 ≤
      (bound * ‖xk‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) 2))] at hle_sq
  rw [mul_pow, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) 2))] at hle_sq
  convert hle_sq using 2

/-- Embedded block norm bound: if M is an n×n matrix supported only on rows in the
    image of an injective `f : Fin p → Fin n` and columns in the image of an injective
    `g : Fin q → Fin n`, with `M (f i) (g j) = X i j` for the p×q matrix X, then
    `‖M‖ ≤ ‖X‖`. -/
lemma embedBlock_norm_le {n p q : ℕ}
    (f : Fin p → Fin n) (g : Fin q → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin p) (Fin q) ℂ)
    (hM_row_zero : ∀ i j, (∀ i' : Fin p, f i' ≠ i) → M i j = 0)
    (hM_col_zero : ∀ i j, (∀ j' : Fin q, g j' ≠ j) → M i j = 0)
    (hM_eq : ∀ (i : Fin p) (j : Fin q), M (f i) (g j) = X i j) :
    ‖M‖ ≤ ‖X‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖Matrix.toEuclideanLin M x‖ ≤ ‖X‖ * ‖x‖
  rw [show Matrix.toEuclideanLin M x = WithLp.toLp 2 (M.mulVec x.ofLp) from
    Matrix.toLpLin_apply 2 2 M x]
  set w := x.ofLp with hw_def
  -- Define the restricted col-block vector
  set vX : Fin q → ℂ := fun j => w (g j) with hvX_def
  set xX : EuclideanSpace ℂ (Fin q) := WithLp.toLp 2 vX with hxX_def
  -- For row i in image of f: (M·w)(f i) = (X·vX)(i).
  have hrow_f : ∀ i : Fin p, M.mulVec w (f i) = X.mulVec vX i := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    calc ∑ c : Fin n, M (f i) c * w c
        = ∑ c ∈ Finset.image g Finset.univ, M (f i) c * w c +
          ∑ c ∈ (Finset.image g Finset.univ)ᶜ, M (f i) c * w c := by
          rw [Finset.sum_add_sum_compl]
      _ = ∑ c ∈ Finset.image g Finset.univ, M (f i) c * w c + 0 := by
          congr 1
          apply Finset.sum_eq_zero; intro c hc
          simp only [Finset.mem_compl, Finset.mem_image, Finset.mem_univ,
            true_and] at hc
          have hMc : M (f i) c = 0 :=
            hM_col_zero (f i) c (fun j' hj' => hc ⟨j', hj'⟩)
          rw [hMc, zero_mul]
      _ = ∑ c ∈ Finset.image g Finset.univ, M (f i) c * w c := by rw [add_zero]
      _ = ∑ j : Fin q, M (f i) (g j) * w (g j) := by
          rw [Finset.sum_image (fun j₁ _ j₂ _ h12 => hg h12)]
      _ = ∑ j : Fin q, X i j * vX j := by
          congr 1; ext j; rw [hM_eq i j]
  -- For row i not in image of f: (M·w) i = 0.
  have hrow_notf : ∀ i : Fin n, (∀ i' : Fin p, f i' ≠ i) → M.mulVec w i = 0 := by
    intro i hi
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero; intro c _
    rw [hM_row_zero i c hi, zero_mul]
  -- Sum of squares comparison
  set Xv := (EuclideanSpace.equiv (Fin p) ℂ).symm (X.mulVec vX) with hXv_def
  have hXv_norm : ‖Xv‖ ≤ ‖X‖ * ‖xX‖ :=
    Matrix.l2_opNorm_mulVec X xX
  -- ‖vX‖² = sum over g · of |w|² ≤ ‖x‖²
  have hxX_sq_eq : ‖xX‖ ^ 2 = ∑ j : Fin q, ‖vX j‖ ^ 2 := by
    rw [hxX_def, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
  have hx_sq_eq : ‖x‖ ^ 2 = ∑ i : Fin n, ‖w i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
  have hxX_sq : ‖xX‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hxX_sq_eq, hx_sq_eq]
    calc ∑ j : Fin q, ‖vX j‖ ^ 2
        = ∑ j : Fin q, ‖w (g j)‖ ^ 2 := by simp [vX]
      _ = ∑ c ∈ Finset.image g Finset.univ, ‖w c‖ ^ 2 := by
          rw [Finset.sum_image (fun j₁ _ j₂ _ h12 => hg h12)]
      _ ≤ ∑ c : Fin n, ‖w c‖ ^ 2 :=
          Finset.sum_le_univ_sum_of_nonneg
            (fun _ => pow_nonneg (norm_nonneg _) 2)
  -- ‖Mw‖² = sum over f · |Xv|² ≤ ‖Xv‖² ≤ ‖X‖² ‖xX‖² ≤ ‖X‖² ‖x‖²
  have hMw_sq : ∑ r : Fin n, ‖M.mulVec w r‖ ^ 2 ≤ ‖Xv‖ ^ 2 := by
    have hXv_sq_eq : ‖Xv‖ ^ 2 = ∑ i : Fin p, ‖X.mulVec vX i‖ ^ 2 := by
      rw [hXv_def, EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
      simp
    rw [hXv_sq_eq]
    -- Split sum over Fin n into image of f and complement; complement part is zero.
    rw [show ∑ r : Fin n, ‖M.mulVec w r‖ ^ 2 =
          ∑ r ∈ Finset.image f Finset.univ, ‖M.mulVec w r‖ ^ 2 +
          ∑ r ∈ (Finset.image f Finset.univ)ᶜ, ‖M.mulVec w r‖ ^ 2 from
        (Finset.sum_add_sum_compl _ _).symm]
    have hcompl_zero :
        ∑ r ∈ (Finset.image f Finset.univ)ᶜ, ‖M.mulVec w r‖ ^ 2 = 0 := by
      apply Finset.sum_eq_zero; intro r hr
      simp only [Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and] at hr
      rw [hrow_notf r (fun i' hi' => hr ⟨i', hi'⟩)]
      simp
    rw [hcompl_zero, add_zero,
        Finset.sum_image (fun i₁ _ i₂ _ h12 => hf h12)]
    apply le_of_eq
    congr 1; ext i; rw [hrow_f i]
  -- Final: square both sides
  apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)),
      mul_pow]
  calc ∑ r : Fin n, ‖M.mulVec w r‖ ^ 2
      ≤ ‖Xv‖ ^ 2 := hMw_sq
    _ ≤ (‖X‖ * ‖xX‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hXv_norm 2
    _ = ‖X‖ ^ 2 * ‖xX‖ ^ 2 := mul_pow _ _ _
    _ ≤ ‖X‖ ^ 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hxX_sq (pow_nonneg (norm_nonneg _) 2)

/-- Block-HS operator norm bound (squared form).

For a matrix `C : Matrix (Fin N) (Fin N) ℂ` decomposed via `e : Fin N ≃ Fin B × Fin M`,
`‖C‖² ≤ Σ_{α,β} ‖C_αβ‖²` where `C_αβ(i,j) := C(e⁻¹(α,i), e⁻¹(β,j))`.

Proof: Cauchy-Schwarz on block projections —
  `‖Cv‖² = Σ_α ‖(Cv)_α‖² ≤ Σ_α (Σ_β ‖C_αβ‖·‖v_β‖)² ≤ (Σ_αβ ‖C_αβ‖²) ‖v‖²`. -/
lemma block_hs_opNorm_sq_le {N B M : ℕ}
    (e : Fin N ≃ Fin B × Fin M)
    (C : Matrix (Fin N) (Fin N) ℂ) :
    ‖C‖ ^ 2 ≤ ∑ p : Fin B × Fin B,
      ‖Matrix.of (fun i j => C (e.symm (p.1, i)) (e.symm (p.2, j)))‖ ^ 2 := by
  set Cblk : Fin B × Fin B → Matrix (Fin M) (Fin M) ℂ :=
    fun p => Matrix.of (fun i j => C (e.symm (p.1, i)) (e.symm (p.2, j))) with hCblk_def
  set S : ℝ := ∑ p : Fin B × Fin B, ‖Cblk p‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)
  have hSα : S = ∑ α : Fin B, ∑ β : Fin B, ‖Cblk (α, β)‖ ^ 2 :=
    Fintype.sum_prod_type _
  rw [show (‖C‖ ^ 2 : ℝ) = ‖C‖ * ‖C‖ from sq _, Matrix.l2_opNorm_def]
  set T := (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) C with hT_def
  have hT_bound : ‖T‖ ≤ Real.sqrt S := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    set w : Fin N → ℂ := v.ofLp with hw_def
    have hTv_eq : T v = WithLp.toLp 2 (C.mulVec w) := Matrix.toLpLin_apply 2 2 C v
    have hTv_sq : ‖T v‖ ^ 2 = ∑ r : Fin N, ‖(C.mulVec w) r‖ ^ 2 := by
      rw [hTv_eq, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
    have hTv_sq_reind : ‖T v‖ ^ 2 =
        ∑ α : Fin B, ∑ i : Fin M, ‖(C.mulVec w) (e.symm (α, i))‖ ^ 2 := by
      rw [hTv_sq, ← Equiv.sum_comp e.symm (fun r => ‖(C.mulVec w) r‖ ^ 2)]
      exact Fintype.sum_prod_type _
    set wblk : Fin B → (Fin M → ℂ) := fun β j => w (e.symm (β, j)) with hwblk_def
    set wblkLp : Fin B → EuclideanSpace ℂ (Fin M) :=
      fun β => WithLp.toLp 2 (wblk β) with hwblkLp_def
    have hentry : ∀ α i,
        (C.mulVec w) (e.symm (α, i)) =
          ∑ β : Fin B, ((Cblk (α, β)).mulVec (wblk β)) i := by
      intro α i
      simp only [Matrix.mulVec, dotProduct]
      rw [← Equiv.sum_comp e.symm (fun c => C (e.symm (α, i)) c * w c)]
      rw [show (∑ p : Fin B × Fin M, C (e.symm (α, i)) (e.symm p) * w (e.symm p)) =
          ∑ β, ∑ j, C (e.symm (α, i)) (e.symm (β, j)) * w (e.symm (β, j)) from
        Fintype.sum_prod_type _]
      simp only [Cblk, Matrix.of_apply, wblk]
    have h_α_bound : ∀ α : Fin B,
        ∑ i : Fin M, ‖(C.mulVec w) (e.symm (α, i))‖ ^ 2 ≤
        (∑ β : Fin B, ‖Cblk (α, β)‖ ^ 2) *
        (∑ β : Fin B, ‖wblkLp β‖ ^ 2) := by
      intro α
      set yβ : Fin B → (Fin M → ℂ) :=
        fun β => (Cblk (α, β)).mulVec (wblk β) with hyβ_def
      set ylpβ : Fin B → EuclideanSpace ℂ (Fin M) :=
        fun β => WithLp.toLp 2 (yβ β) with hylpβ_def
      have hsum_apply : ∀ i : Fin M,
          ((∑ β : Fin B, ylpβ β) : EuclideanSpace ℂ (Fin M)).ofLp i = ∑ β, yβ β i := by
        intro i
        rw [WithLp.ofLp_sum]
        simp [ylpβ]
      have hLHS : ∑ i : Fin M, ‖(C.mulVec w) (e.symm (α, i))‖ ^ 2 =
          ‖(∑ β : Fin B, ylpβ β : EuclideanSpace ℂ (Fin M))‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
        congr 1; ext i
        rw [hsum_apply i, hentry α i]
      rw [hLHS]
      have htri : ‖(∑ β : Fin B, ylpβ β)‖ ≤ ∑ β : Fin B, ‖ylpβ β‖ := norm_sum_le _ _
      have hindiv : ∀ β, ‖ylpβ β‖ ≤ ‖Cblk (α, β)‖ * ‖wblkLp β‖ := by
        intro β
        have hmv := Matrix.l2_opNorm_mulVec (Cblk (α, β)) (wblkLp β)
        have heq : (wblkLp β).ofLp = wblk β := rfl
        rw [heq] at hmv
        simp only [yβ, ylpβ] at *
        convert hmv
      have hsum_le : (∑ β : Fin B, ‖ylpβ β‖) ≤
          ∑ β : Fin B, ‖Cblk (α, β)‖ * ‖wblkLp β‖ :=
        Finset.sum_le_sum (fun β _ => hindiv β)
      have hchain : ‖(∑ β : Fin B, ylpβ β)‖ ≤
          ∑ β : Fin B, ‖Cblk (α, β)‖ * ‖wblkLp β‖ :=
        le_trans htri hsum_le
      have hchain_nn : (0 : ℝ) ≤ ‖(∑ β : Fin B, ylpβ β)‖ := norm_nonneg _
      have hchain_sq : ‖(∑ β : Fin B, ylpβ β)‖ ^ 2 ≤
          (∑ β : Fin B, ‖Cblk (α, β)‖ * ‖wblkLp β‖) ^ 2 :=
        pow_le_pow_left₀ hchain_nn hchain 2
      have hCS : (∑ β : Fin B, ‖Cblk (α, β)‖ * ‖wblkLp β‖) ^ 2 ≤
          (∑ β : Fin B, ‖Cblk (α, β)‖ ^ 2) * (∑ β : Fin B, ‖wblkLp β‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      linarith
    have hTv_bound : ‖T v‖ ^ 2 ≤ S * (∑ β : Fin B, ‖wblkLp β‖ ^ 2) := by
      rw [hTv_sq_reind]
      calc ∑ α : Fin B, ∑ i : Fin M, ‖(C.mulVec w) (e.symm (α, i))‖ ^ 2
          ≤ ∑ α : Fin B, (∑ β : Fin B, ‖Cblk (α, β)‖ ^ 2) *
              (∑ β : Fin B, ‖wblkLp β‖ ^ 2) :=
            Finset.sum_le_sum (fun α _ => h_α_bound α)
        _ = (∑ α : Fin B, ∑ β : Fin B, ‖Cblk (α, β)‖ ^ 2) *
              (∑ β : Fin B, ‖wblkLp β‖ ^ 2) := by rw [← Finset.sum_mul]
        _ = S * (∑ β : Fin B, ‖wblkLp β‖ ^ 2) := by rw [← hSα]
    have hv_sq : ∑ β : Fin B, ‖wblkLp β‖ ^ 2 = ‖v‖ ^ 2 := by
      have hβ : ∀ β, ‖wblkLp β‖ ^ 2 = ∑ j : Fin M, ‖w (e.symm (β, j))‖ ^ 2 := by
        intro β
        rw [EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
      simp_rw [hβ]
      rw [← Fintype.sum_prod_type (fun p : Fin B × Fin M => ‖w (e.symm p)‖ ^ 2),
        Equiv.sum_comp e.symm (fun r => ‖w r‖ ^ 2)]
      rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))]
    rw [hv_sq] at hTv_bound
    have h_rhs_sq : (Real.sqrt S * ‖v‖) ^ 2 = S * ‖v‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hS_nn]
    have h_rhs_nn : 0 ≤ Real.sqrt S * ‖v‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    exact le_of_sq_le_sq (by rw [h_rhs_sq]; exact hTv_bound) h_rhs_nn
  calc ‖T‖ * ‖T‖ ≤ Real.sqrt S * Real.sqrt S :=
        mul_le_mul hT_bound hT_bound (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = S := Real.mul_self_sqrt hS_nn

end CommutatorTheorem
