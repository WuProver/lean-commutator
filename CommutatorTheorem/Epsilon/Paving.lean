import CommutatorTheorem.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Finset.Basic

/-!
# Paving Machinery and Bourgain-Tzafriri

This file formalizes the paving constructions used in the proof of the
quantitative commutator theorem (JOS 2013, Section 3).
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing

open CommutatorTheorem

namespace CommutatorTheorem

/-! ## Block decomposition induced by a partition -/

/-- The (i,j)-th block of matrix A induced by the partition σ.
    Entry (r,c) of the result equals A r c if r ∈ σ i and c ∈ σ j, and 0 otherwise. -/
noncomputable def blockOf {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (A : Matrix (Fin m) (Fin m) ℂ) (i j : Fin k) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun r c => if r ∈ σ i ∧ c ∈ σ j then A r c else 0

/-! ## Paving norm -/

/-- The paving norm of A with respect to partition σ: the supremum of diagonal block norms. -/
noncomputable def pavingNorm {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (A : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ⨆ i : Fin k, ‖blockOf σ A i i‖

/-! ## Helper lemmas for the paving construction -/

/-- When B is diagonal, the commutator [B, C] has entries (B r r - B c c) * C r c. -/
lemma commutator_diag_entry {m : ℕ} (B C : Matrix (Fin m) (Fin m) ℂ)
    (hDiag : IsDiagMatrix B) (r c : Fin m) :
    (⁅B, C⁆ₘ) r c = (B r r - B c c) * C r c := by
  simp only [matComm, Matrix.sub_apply, Matrix.mul_apply]
  have h1 : ∑ k, B r k * C k c = B r r * C r c := by
    rw [Finset.sum_eq_single r]
    · intro k _ hk; rw [hDiag r k (Ne.symm hk)]; ring
    · simp
  have h2 : ∑ k, C r k * B k c = C r c * B c c := by
    rw [Finset.sum_eq_single c]
    · intro k _ hk; rw [hDiag k c hk]; ring
    · simp
  rw [h1, h2]; ring

/-- Assign a real number in [-1, 1] to a box index in {0, ..., N-1}. -/
noncomputable def boxIndex (N : ℕ) (x : ℝ) : ℕ :=
  min (⌊(x + 1) * (N : ℝ) / 2⌋₊) (N - 1)

lemma boxIndex_lt {N : ℕ} (hN : 0 < N) (x : ℝ) : boxIndex N x < N := by
  simp only [boxIndex]; omega

/-- Encode a 2D box index (re_box, im_box) as a single index < N². -/
noncomputable def boxEncode {m : ℕ} (N : ℕ) (B : Matrix (Fin m) (Fin m) ℂ)
    (i : Fin m) : ℕ :=
  boxIndex N (B i i).re * N + boxIndex N (B i i).im

lemma boxEncode_lt {m : ℕ} {N : ℕ} (hN : 0 < N) (B : Matrix (Fin m) (Fin m) ℂ)
    (i : Fin m) : boxEncode N B i < N ^ 2 := by
  simp only [boxEncode, Nat.pow_two]
  have h1 := boxIndex_lt hN (B i i).re
  have h3 : boxIndex N (B i i).re ≤ N - 1 := by omega
  nlinarith [boxIndex_lt hN (B i i).im]

/-- ⌊2/ε⌋₊ ≥ 2 when ε ∈ (0, 1). -/
lemma floor_two_div_ge_two {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) : 2 ≤ ⌊2 / ε⌋₊ := by
  rw [Nat.le_floor_iff (by positivity)]
  exact le_div_iff₀ hε |>.mpr (by linarith : (2 : ℝ) * ε ≤ 2)

/-- If two reals have the same boxIndex in an N-grid, they differ by at most 2/N.
    This is the key box diameter bound. -/
lemma boxIndex_same_box {N : ℕ} (hN : 0 < N) {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ Set.Icc (-1 : ℝ) 1) (hx₂ : x₂ ∈ Set.Icc (-1 : ℝ) 1)
    (hbox : boxIndex N x₁ = boxIndex N x₂) :
    |x₁ - x₂| ≤ 2 / (N : ℝ) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  -- Helper: for any x ∈ [-1,1] with boxIndex N x = k, we have k ≤ (x+1)*N/2 ≤ k+1
  suffices hbounds : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      ∀ j : ℕ, boxIndex N x = j →
      (j : ℝ) ≤ (x + 1) * N / 2 ∧ (x + 1) * N / 2 ≤ (j : ℝ) + 1 by
    obtain ⟨lo₁, hi₁⟩ := hbounds x₁ hx₁ _ rfl
    obtain ⟨lo₂, hi₂⟩ := hbounds x₂ hx₂ _ hbox.symm
    rw [abs_sub_le_iff]
    constructor <;> (rw [le_div_iff₀ hN_pos]; nlinarith)
  intro x hx j hbx
  have harg : 0 ≤ (x + 1) * N / 2 := by nlinarith [hx.1]
  simp only [boxIndex] at hbx
  constructor
  · -- Lower bound: j = min(⌊...⌋₊, N-1) ≤ ⌊...⌋₊ ≤ (x+1)*N/2
    calc (j : ℝ) ≤ ↑(⌊(x + 1) * ↑N / 2⌋₊) := by
            exact_mod_cast hbx ▸ Nat.min_le_left _ _
      _ ≤ (x + 1) * ↑N / 2 := Nat.floor_le harg
  · -- Upper bound: (x+1)*N/2 ≤ j+1
    by_cases h : ⌊(x + 1) * ↑N / 2⌋₊ ≤ N - 1
    · rw [min_eq_left h] at hbx
      calc (x + 1) * ↑N / 2 ≤ ↑(⌊(x + 1) * ↑N / 2⌋₊) + 1 :=
            le_of_lt (Nat.lt_floor_add_one _)
        _ = (j : ℝ) + 1 := by rw [hbx]
    · push Not at h
      rw [min_eq_right (le_of_lt h)] at hbx
      have hNj : (N : ℝ) = (j : ℝ) + 1 := by
        have : j + 1 = N := by omega
        exact_mod_cast this.symm
      calc (x + 1) * ↑N / 2 ≤ ↑N := by nlinarith [hx.2]
        _ = (j : ℝ) + 1 := hNj

/-- N = ⌊2/ε⌋₊ + 1 satisfies 2/N < ε when ε > 0. -/
lemma two_div_floor_succ_lt {ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ) / (↑(⌊2 / ε⌋₊ + 1)) < ε := by
  have hN_pos : (0 : ℝ) < ↑(⌊2 / ε⌋₊ + 1) := by positivity
  rw [div_lt_iff₀ hN_pos]
  have h := Nat.lt_floor_add_one (2 / ε)
  -- h : 2 / ε < ↑(⌊2 / ε⌋₊ + 1)
  calc (2 : ℝ) = ε * (2 / ε) := by field_simp
    _ < ε * (↑(⌊2 / ε⌋₊ + 1)) := by
        exact mul_lt_mul_of_pos_left (by exact_mod_cast h) hε

/-- The projection matrix P_σ_i: diagonal with 1 on indices in σ i. -/
noncomputable def projBlock {m k : ℕ} (σ : Fin k → Finset (Fin m)) (i : Fin k) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal (fun r => if r ∈ σ i then 1 else 0)

/-- blockOf σ C i i = projBlock σ i * C * projBlock σ i. -/
lemma blockOf_eq_proj_mul {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (C : Matrix (Fin m) (Fin m) ℂ) (i : Fin k) :
    blockOf σ C i i = projBlock σ i * C * projBlock σ i := by
  -- Both sides have entry (r,c) = if r ∈ σ i ∧ c ∈ σ i then C r c else 0
  -- P * C * P at (r,c) = ∑_{x,y} P(r,x) C(x,y) P(y,c) = P(r,r) C(r,c) P(c,c)
  --   since P is diagonal. = (if r ∈ σ i then 1 else 0) * C r c * (if c ∈ σ i then 1 else 0)
  ext r c
  simp only [blockOf, projBlock, Matrix.of_apply, Matrix.mul_apply,
    Matrix.diagonal_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> simp_all

/-- The norm of projBlock is at most 1. -/
lemma norm_projBlock_le_one {m k : ℕ} (σ : Fin k → Finset (Fin m)) (i : Fin k) :
    ‖projBlock σ i‖ ≤ 1 := by
  -- projBlock is a diagonal 0/1 matrix, so ‖P‖ = sup_r |P_rr| ≤ 1
  rw [show projBlock σ i = Matrix.diagonal (fun r => if r ∈ σ i then (1 : ℂ) else 0) from rfl]
  rw [Matrix.l2_opNorm_diagonal]
  -- Goal: ‖fun r => if r ∈ σ i then 1 else 0‖ ≤ 1
  -- The pi norm is the sup of ‖v r‖ over r, each of which is ≤ 1.
  simp only [Pi.norm_def]
  norm_cast
  apply Finset.sup_le
  intro b _
  split_ifs <;> simp

/-- The norm of a diagonal block is at most the norm of the full matrix. -/
lemma norm_blockOf_le {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (C : Matrix (Fin m) (Fin m) ℂ) (i : Fin k) :
    ‖blockOf σ C i i‖ ≤ ‖C‖ := by
  rw [blockOf_eq_proj_mul]
  calc ‖projBlock σ i * C * projBlock σ i‖
      ≤ ‖projBlock σ i * C‖ * ‖projBlock σ i‖ := norm_mul_le _ _
    _ ≤ (‖projBlock σ i‖ * ‖C‖) * ‖projBlock σ i‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ 1 * ‖C‖ * 1 := by
        gcongr <;> exact norm_projBlock_le_one σ i
    _ = ‖C‖ := by ring

/-- When B is diagonal, the diagonal block of [B,C] equals the commutator of diagonal blocks.
    Both sides have entry (B r r - B c c) * C r c when r,c ∈ σ i, and 0 otherwise. -/
lemma blockOf_matComm_diag {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (B C : Matrix (Fin m) (Fin m) ℂ) (hDiag : IsDiagMatrix B) (i : Fin k) :
    blockOf σ (⁅B, C⁆ₘ) i i = ⁅blockOf σ B i i, blockOf σ C i i⁆ₘ := by
  -- LHS(r,c) = if r,c ∈ σ i then [B,C](r,c) else 0
  --          = if r,c ∈ σ i then (B r r - B c c) * C r c else 0  (by commutator_diag_entry)
  -- RHS(r,c) = ∑_x blockOf(B)(r,x) * blockOf(C)(x,c) - blockOf(C)(r,x) * blockOf(B)(x,c)
  --   First sum: only x=r survives (B diagonal)
  --     → (if r∈σi then B_rr else 0)*(if r,c∈σi then C_rc else 0)
  --   Second sum: only x=c survives → (if r,c∈σi then C_rc else 0)*(if c∈σi then B_cc else 0)
  --   = if r,c ∈ σ i then (B_rr * C_rc - C_rc * B_cc) else 0
  --   = if r,c ∈ σ i then (B r r - B c c) * C r c else 0  (by ring)
  ext r c
  simp only [blockOf, Matrix.of_apply, matComm, Matrix.sub_apply, Matrix.mul_apply]
  by_cases hr : r ∈ σ i <;> by_cases hc : c ∈ σ i
  · simp only [hr, hc, true_and, ite_true]
    congr 1
    · apply Finset.sum_congr rfl; intro x _
      by_cases hx : x ∈ σ i
      · simp [hx]
      · simp only [hx, ite_false, zero_mul]
        have hxr : x ≠ r := fun h => hx (h ▸ hr)
        rw [hDiag r x (Ne.symm hxr)]; ring
    · apply Finset.sum_congr rfl; intro x _
      by_cases hx : x ∈ σ i
      · simp [hx]
      · simp only [hx, ite_false, zero_mul]
        have hxc : x ≠ c := fun h => hx (h ▸ hc)
        rw [hDiag x c hxc]; ring
  · simp only [hr, hc, true_and, and_false, ite_false]; simp [mul_zero]
  · simp only [hr, hc, false_and, and_true, ite_false]; simp
  · simp only [hr, hc, false_and, and_false, ite_false]; simp

/-- Commutator norm bound: ‖[A, B]‖ ≤ 2 * ‖A‖ * ‖B‖. -/
lemma matComm_norm_le {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    ‖⁅A, B⁆ₘ‖ ≤ 2 * ‖A‖ * ‖B‖ := by
  unfold matComm
  calc ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := by
        gcongr <;> exact norm_mul_le _ _
    _ = 2 * ‖A‖ * ‖B‖ := by ring

/-- Shifting the diagonal block by a scalar multiple of the projection doesn't change
    the commutator with the corresponding block of C. [D - c₀·P, C'] = [D, C'] since [P,C'] = 0. -/
lemma matComm_blockOf_shift {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (B C : Matrix (Fin m) (Fin m) ℂ) (i : Fin k) (c₀ : ℂ) :
    ⁅blockOf σ B i i - c₀ • projBlock σ i, blockOf σ C i i⁆ₘ =
    ⁅blockOf σ B i i, blockOf σ C i i⁆ₘ := by
  -- Key: projBlock σ i acts as the identity on blockOf σ C i i,
  -- i.e. P * C_i = C_i = C_i * P. So [c₀ P, C_i] = c₀(P C_i - C_i P) = 0.
  have hPC : projBlock σ i * blockOf σ C i i = blockOf σ C i i := by
    ext r c
    simp only [Matrix.mul_apply, projBlock, Matrix.diagonal_apply, blockOf, Matrix.of_apply]
    rw [Finset.sum_eq_single r]
    · split_ifs <;> simp_all
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ r) h
  have hCP : blockOf σ C i i * projBlock σ i = blockOf σ C i i := by
    ext r c
    simp only [Matrix.mul_apply, projBlock, Matrix.diagonal_apply, blockOf, Matrix.of_apply]
    rw [Finset.sum_eq_single c]
    · split_ifs <;> simp_all
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ c) h
  simp only [matComm, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hPC, hCP]
  abel

/-! ## Claim 3 helpers -/


/-- For x ∈ [-1,1] with boxIndex N x = k, the distance from x to the box center
    (-1 + (2k+1)/N) is at most 1/N. -/
lemma boxIndex_half_width {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) {k : ℕ} (hk : boxIndex N x = k) :
    |x - (-1 + (2 * (k : ℝ) + 1) / (N : ℝ))| ≤ 1 / (N : ℝ) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have harg : 0 ≤ (x + 1) * N / 2 := by nlinarith [hx.1]
  simp only [boxIndex] at hk
  have hlo : (k : ℝ) ≤ (x + 1) * N / 2 := by
    calc (k : ℝ) ≤ ↑(⌊(x + 1) * ↑N / 2⌋₊) := by exact_mod_cast hk ▸ Nat.min_le_left _ _
      _ ≤ (x + 1) * ↑N / 2 := Nat.floor_le harg
  have hhi : (x + 1) * N / 2 ≤ (k : ℝ) + 1 := by
    by_cases h : ⌊(x + 1) * ↑N / 2⌋₊ ≤ N - 1
    · rw [min_eq_left h] at hk
      calc (x + 1) * ↑N / 2 ≤ ↑(⌊(x + 1) * ↑N / 2⌋₊) + 1 :=
            le_of_lt (Nat.lt_floor_add_one _)
        _ = (k : ℝ) + 1 := by rw [hk]
    · push Not at h
      rw [min_eq_right (le_of_lt h)] at hk
      have hNk : (N : ℝ) = (k : ℝ) + 1 := by exact_mod_cast (show k + 1 = N by omega).symm
      calc (x + 1) * ↑N / 2 ≤ ↑N := by nlinarith [hx.2]
        _ = (k : ℝ) + 1 := hNk
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have key : |x - (-1 + (2 * ↑k + 1) / ↑N)| =
      |(x + 1) * ↑N - (2 * ↑k + 1)| / ↑N := by
    rw [show x - (-1 + (2 * ↑k + 1) / ↑N) =
        ((x + 1) * ↑N - (2 * ↑k + 1)) / ↑N by field_simp; ring]
    rw [abs_div, abs_of_pos hN_pos]
  rw [key, div_le_div_iff_of_pos_right hN_pos]
  rw [abs_le]; constructor <;> nlinarith

/-- When B is diagonal, blockOf σ B i i equals a diagonal matrix. -/
lemma blockOf_diag_eq_diagonal {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (B : Matrix (Fin m) (Fin m) ℂ) (hDiag : IsDiagMatrix B) (i : Fin k) :
    blockOf σ B i i = Matrix.diagonal (fun r => if r ∈ σ i then B r r else 0) := by
  ext r c
  simp only [blockOf, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hrc : r = c
  · subst hrc; simp [and_self]
  · simp only [hrc, ite_false]
    split_ifs with h
    · exact hDiag r c hrc
    · rfl

/-- Complex norm bounded by √2 times max of coordinate absolute values. -/
private lemma complex_norm_le_sqrt2_mul {z : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hRe : |z.re| ≤ d) (hIm : |z.im| ≤ d) :
    ‖z‖ ≤ Real.sqrt 2 * d := by
  have hre2 : z.re ^ 2 ≤ d ^ 2 :=
    sq_le_sq' (by linarith [abs_le.mp hRe]) (abs_le.mp hRe).2
  have him2 : z.im ^ 2 ≤ d ^ 2 :=
    sq_le_sq' (by linarith [abs_le.mp hIm]) (abs_le.mp hIm).2
  rw [show ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) from by
    rw [Complex.norm_def, Complex.normSq_apply]; ring_nf]
  rw [show Real.sqrt 2 * d = Real.sqrt (2 * d ^ 2) from by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq hd]]
  exact Real.sqrt_le_sqrt (by linarith)

/-- The shifted diagonal block has bounded norm when entries are in the same box. -/
lemma shifted_block_norm_le {m : ℕ} {N : ℕ} (hN : 0 < N)
    (B : Matrix (Fin m) (Fin m) ℂ) (_hDiag : IsDiagMatrix B)
    (hSpec : ∀ i, InUnitSquare (B i i))
    {S : Finset (Fin m)} {a b : ℕ}
    (hS : ∀ r ∈ S, boxIndex N (B r r).re = a ∧ boxIndex N (B r r).im = b) :
    let c₀ : ℂ := ⟨-1 + (2 * (a : ℝ) + 1) / N, -1 + (2 * (b : ℝ) + 1) / N⟩
    let v : Fin m → ℂ := fun r => if r ∈ S then B r r - c₀ else 0
    ‖Matrix.diagonal v‖ ≤ Real.sqrt 2 / N := by
  intro c₀ v
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [Matrix.l2_opNorm_diagonal, Pi.norm_def]
  -- Goal: ↑(Finset.univ.sup fun b => ‖v b‖₊) ≤ √2/N
  have hb : ∀ r ∈ Finset.univ, ‖v r‖₊ ≤ ⟨Real.sqrt 2 / N, by positivity⟩ := by
    intro r _
    apply NNReal.coe_le_coe.mp
    simp only [v]
    split_ifs with hr
    · -- r ∈ S: ‖B r r - c₀‖ ≤ √2/N
      obtain ⟨hre, him⟩ := hS r hr
      have hSpec_r := hSpec r
      have hRe : |((B r r) - c₀).re| ≤ 1 / N := by
        simp only [Complex.sub_re, c₀]
        exact boxIndex_half_width hN
          ⟨by linarith [abs_le.mp hSpec_r.1],
           by linarith [abs_le.mp hSpec_r.1]⟩ hre
      have hIm : |((B r r) - c₀).im| ≤ 1 / N := by
        simp only [Complex.sub_im, c₀]
        exact boxIndex_half_width hN
          ⟨by linarith [abs_le.mp hSpec_r.2],
           by linarith [abs_le.mp hSpec_r.2]⟩ him
      calc ‖B r r - c₀‖ ≤ Real.sqrt 2 * (1 / N) :=
              complex_norm_le_sqrt2_mul (by positivity) hRe hIm
        _ = Real.sqrt 2 / N := by ring
    · simp
  exact_mod_cast Finset.sup_le hb

/-- Claim 3 from JOS 2013: if A = [B, C] with B diagonal, eigenvalues in the unit square,
    then for ε ∈ (0,1), A has a paving of length ≤ (⌊2/ε⌋₊+1)² with norm ≤ √2 * ε * ‖C‖. -/
theorem claim3 {m : ℕ} (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (B C : Matrix (Fin m) (Fin m) ℂ) (A : Matrix (Fin m) (Fin m) ℂ)
    (hDiag : IsDiagMatrix B)
    (hSpec : ∀ i, InUnitSquare (B i i))
    (hComm : A = ⁅B, C⁆ₘ) :
    ∃ (k : ℕ) (σ : Fin k → Finset (Fin m)),
      k ≤ (⌊2 / ε⌋₊ + 1) ^ 2 ∧
      pavingNorm σ A ≤ Real.sqrt 2 * ε * ‖C‖ := by
  set N := ⌊2 / ε⌋₊ + 1 with hN_def
  have hN_pos : 0 < N := by omega
  have hN_cast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
  have h2N : (2 : ℝ) / N < ε := two_div_floor_succ_lt hε
  let σ : Fin (N ^ 2) → Finset (Fin m) :=
    fun p => Finset.univ.filter (fun i => boxEncode N B i = p.val)
  refine ⟨N ^ 2, σ, le_refl _, ?_⟩
  -- Goal: pavingNorm σ A ≤ √2 * ε * ‖C‖
  change ⨆ i : Fin (N ^ 2), ‖blockOf σ A i i‖ ≤ Real.sqrt 2 * ε * ‖C‖
  haveI : Nonempty (Fin (N ^ 2)) := ⟨⟨0, by positivity⟩⟩
  apply ciSup_le
  intro p
  -- Bound each block: ‖blockOf σ A p p‖ ≤ √2 * ε * ‖C‖
  rw [hComm, blockOf_matComm_diag σ B C hDiag p]
  -- Define box center for block p
  set a_idx := p.val / N
  set b_idx := p.val % N
  set c₀ : ℂ := ⟨-1 + (2 * (a_idx : ℝ) + 1) / N,
                   -1 + (2 * (b_idx : ℝ) + 1) / N⟩
  rw [← matComm_blockOf_shift σ B C p c₀]
  -- ‖[D - c₀P, C']‖ ≤ 2 * ‖D - c₀P‖ * ‖C'‖ ≤ 2 * (√2/N) * ‖C‖ ≤ √2*ε*‖C‖
  calc ‖⁅blockOf σ B p p - c₀ • projBlock σ p, blockOf σ C p p⁆ₘ‖
      ≤ 2 * ‖blockOf σ B p p - c₀ • projBlock σ p‖ * ‖blockOf σ C p p‖ :=
        matComm_norm_le _ _
    _ ≤ 2 * (Real.sqrt 2 / N) * ‖C‖ := by
        gcongr
        · -- ‖blockOf σ B p p - c₀ • projBlock σ p‖ ≤ √2/N
          -- This matrix is diagonal with entries (B r r - c₀) for r ∈ σ p, 0 otherwise
          have heq : blockOf σ B p p - c₀ • projBlock σ p =
              Matrix.diagonal (fun r => if r ∈ σ p then B r r - c₀ else 0) := by
            rw [blockOf_diag_eq_diagonal σ B hDiag p]
            ext r c; simp [projBlock, Matrix.diagonal_apply, Matrix.sub_apply,
              Matrix.smul_apply, smul_eq_mul]
            split_ifs <;> ring
          rw [heq]
          exact shifted_block_norm_le hN_pos B hDiag hSpec
            (fun r hr => by
              simp only [σ, Finset.mem_filter, Finset.mem_univ, true_and] at hr
              simp only [boxEncode] at hr
              -- hr : boxIndex N re * N + boxIndex N im = p.val
              -- Need: re_idx = a_idx and im_idx = b_idx
              have him_lt := boxIndex_lt hN_pos (B r r).im
              have ⟨hdiv, hmod⟩ := show
                  boxIndex N (B r r).re = p.val / N ∧
                  boxIndex N (B r r).im = p.val % N by
                constructor
                · rw [← hr,
                    show boxIndex N (B r r).re * N + boxIndex N (B r r).im =
                      boxIndex N (B r r).im + boxIndex N (B r r).re * N
                      from by ring,
                    Nat.add_mul_div_right _ _ hN_pos,
                    Nat.div_eq_of_lt him_lt, zero_add]
                · rw [← hr,
                    show boxIndex N (B r r).re * N + boxIndex N (B r r).im =
                      boxIndex N (B r r).im + N * boxIndex N (B r r).re
                      from by ring,
                    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt him_lt]
              exact ⟨hdiv, hmod⟩)
        · exact norm_blockOf_le σ C p
    _ ≤ Real.sqrt 2 * ε * ‖C‖ := by
        -- 2 * (√2/N) ≤ √2*ε since 2/N < ε and √2 > 0
        have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := by positivity
        have h_coeff : 2 * (Real.sqrt 2 / ↑N) ≤ Real.sqrt 2 * ε := by
          have : 2 / ↑N ≤ ε := le_of_lt h2N
          calc 2 * (Real.sqrt 2 / ↑N) = Real.sqrt 2 * (2 / ↑N) := by ring
            _ ≤ Real.sqrt 2 * ε := by gcongr
        nlinarith [norm_nonneg C]


end CommutatorTheorem
