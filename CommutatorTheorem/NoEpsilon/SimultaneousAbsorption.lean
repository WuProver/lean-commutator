import CommutatorTheorem.NoEpsilon.FiniteAbsorption

/-! # Simultaneous elimination of the outside diagonal blocks

Two square-zero shears suffice for the whole family. The orthogonality estimates
charge the square root of the number of blocks, rather than iterating a polynomial.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace NoEpsilon.Absorption

variable {ι n r : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]

omit [DecidableEq ι] [DecidableEq n] in
theorem orthogonal_sum_norm_sq (X : ι → Matrix n r ℂ)
    (h : ∀ i j, i ≠ j → (X i)ᴴ * X j = 0) :
    ‖∑ i, X i‖ ^ 2 ≤ ∑ i, ‖X i‖ ^ 2 := by
  have heq : (∑ i, X i)ᴴ * (∑ i, X i) = ∑ i, (X i)ᴴ * X i := by
    simp only [Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_eq_single i (fun j _ hji ↦ h j i hji) (by simp)
  simp only [pow_two]
  rw [← Matrix.l2_opNorm_conjTranspose_mul_self, heq]
  calc
    _ ≤ ∑ i, ‖(X i)ᴴ * X i‖ := norm_sum_le _ _
    _ = _ := by simp only [Matrix.l2_opNorm_conjTranspose_mul_self]

variable (d : ι → Type*) [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

omit [DecidableEq ι] in
theorem outside_projection_norm_le (V : ∀ i, Matrix n (d i) ℂ)
    (hVV : ∀ i, (V i)ᴴ * V i = 1)
    (hOrth : ∀ i j, i ≠ j → (V i)ᴴ * V j = 0) :
    ‖∑ i, V i * (V i)ᴴ‖ ≤ 1 := by
  let E := ∑ i, V i * (V i)ᴴ
  have hE : Eᴴ = E := by simp only [E, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  have hEE : E * E = E := by
    dsimp [E]
    rw [Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_sum]
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (V i)ᴴ, hVV, Matrix.one_mul]
    · intro j _ hji
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (V i)ᴴ, hOrth i j hji.symm,
        Matrix.zero_mul, Matrix.mul_zero]
    · simp
  have hs := Matrix.l2_opNorm_conjTranspose_mul_self E
  rw [hE, hEE] at hs
  nlinarith [norm_nonneg E]

/-- The polynomial growth budget of two simultaneous shears. -/
noncomputable def simultaneousBudget (a : ℝ) (m : ℕ) : ℝ :=
  let u := 1 + a + Real.sqrt m
  let a₁ := a * u ^ 2
  a₁ * (1 + Real.sqrt m * a₁) ^ 2

set_option maxHeartbeats 1600000 in
-- The two-shear construction combines block identities and nonlinear norm estimates.
omit [DecidableEq ι] in
theorem eliminate_simultaneously
    (P Q : Matrix n r ℂ) (V : ∀ i, Matrix n (d i) ℂ)
    (J : ∀ i, Matrix r (d i) ℂ)
    (hPP : Pᴴ * P = 1) (hQQ : Qᴴ * Q = 1) (hPQ : Pᴴ * Q = 0)
    (hVV : ∀ i, (V i)ᴴ * V i = 1) (hPV : ∀ i, Pᴴ * V i = 0)
    (hVQ : ∀ i, (V i)ᴴ * Q = 0)
    (hOrth : ∀ i j, i ≠ j → (V i)ᴴ * V j = 0)
    (hJJ : ∀ i, (J i)ᴴ * J i = 1)
    (A : Matrix n n ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hbridge : Pᴴ * A * Q = 1) (hA : ‖A‖ ≤ a) :
    ∃ S T : Matrix n n ℂ,
      S * T = 1 ∧ T * S = 1 ∧ Pᴴ * (T * A * S) * Q = 1 ∧
      (∀ i, (V i)ᴴ * (T * A * S) * V i = 0) ∧
      trace (T * A * S) = trace A ∧
      ‖T * A * S‖ ≤ simultaneousBudget a (Fintype.card ι) ∧
      a * (‖S‖ * ‖T‖) ≤ simultaneousBudget a (Fintype.card ι) := by
  classical
  let E := ∑ i, V i * (V i)ᴴ
  let L := ∑ i, J i * (V i)ᴴ
  let X := L - Pᴴ * A * E
  let N := Q * X
  let A' := shear A N
  let Y := ∑ i, V i * ((V i)ᴴ * A' * V i * (J i)ᴴ)
  let M := Y * Pᴴ
  have hEV (j : ι) : E * V j = V j := by
    dsimp [E]
    rw [Matrix.sum_mul, Finset.sum_eq_single j]
    · simp [Matrix.mul_assoc, hVV]
    · intro i _ hij
      rw [Matrix.mul_assoc, hOrth i j hij, Matrix.mul_zero]
    · simp
  have hLV (j : ι) : L * V j = J j := by
    dsimp [L]
    rw [Matrix.sum_mul, Finset.sum_eq_single j]
    · simp [Matrix.mul_assoc, hVV]
    · intro i _ hij
      rw [Matrix.mul_assoc, hOrth i j hij, Matrix.mul_zero]
    · simp
  have hEQ : E * Q = 0 := by simp [E, Matrix.sum_mul, Matrix.mul_assoc, hVQ]
  have hLQ : L * Q = 0 := by simp [L, Matrix.sum_mul, Matrix.mul_assoc, hVQ]
  have hXQ : X * Q = 0 := by
    simp [X, Matrix.sub_mul, Matrix.mul_assoc, hEQ, hLQ]
  have hNQ : N * Q = 0 := by simp [N, Matrix.mul_assoc, hXQ]
  have hPN : Pᴴ * N = 0 := by simp [N, ← Matrix.mul_assoc, hPQ]
  have hNN : N * N = 0 := by simp [N, ← Matrix.mul_assoc, hNQ]
  have hbridge' : Pᴴ * A' * Q = 1 := by
    rw [compression_shear_eq A N Pᴴ Q hPN hNQ, hbridge]
  have hnew (j : ι) : Pᴴ * A' * V j = J j := by
    have hx : X * V j = J j - Pᴴ * A * V j := by
      simp [X, Matrix.sub_mul, Matrix.mul_assoc, hLV, hEV]
    have hl : Pᴴ * (1 - N) = Pᴴ := by simp [Matrix.mul_sub, hPN]
    calc
      _ = Pᴴ * A * V j + (Pᴴ * A * Q) * (X * V j) := by
        dsimp [A', shear]
        simp only [← Matrix.mul_assoc]
        rw [hl]
        simp [Matrix.mul_add, Matrix.add_mul, N, Matrix.mul_assoc]
      _ = J j := by rw [hbridge, Matrix.one_mul, hx]; abel
  have hPY : Pᴴ * Y = 0 := by
    simp [Y, Matrix.mul_sum, ← Matrix.mul_assoc, hPV]
  have hVY (j : ι) : (V j)ᴴ * Y = (V j)ᴴ * A' * V j * (J j)ᴴ := by
    dsimp [Y]
    rw [Matrix.mul_sum, Finset.sum_eq_single j]
    · simp [← Matrix.mul_assoc, hVV]
    · intro i _ hij
      rw [← Matrix.mul_assoc, hOrth j i hij.symm, Matrix.zero_mul]
    · simp
  have hMM : M * M = 0 := by simp [M, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, hPY]
  have hPM : Pᴴ * M = 0 := by simp [M, ← Matrix.mul_assoc, hPY]
  have hMQ : M * Q = 0 := by simp [M, Matrix.mul_assoc, hPQ]
  have hMV (j : ι) : M * V j = 0 := by simp [M, Matrix.mul_assoc, hPV]
  have hzero (j : ι) : (V j)ᴴ * shear A' M * V j = 0 := by
    have hr : (1 + M) * V j = V j := by simp [Matrix.add_mul, hMV]
    calc
      _ = ((V j)ᴴ - ((V j)ᴴ * A' * V j * (J j)ᴴ) * Pᴴ) * A' * V j := by
        dsimp [shear]
        calc
          _ = ((V j)ᴴ * (1 - M)) * A' * ((1 + M) * V j) := by
            simp only [Matrix.mul_assoc]
          _ = _ := by
            rw [hr]
            congr 2
            simp only [Matrix.mul_sub, Matrix.mul_one, M, ← Matrix.mul_assoc, hVY]
      _ = (V j)ᴴ * A' * V j -
          ((V j)ᴴ * A' * V j) * ((J j)ᴴ * (Pᴴ * A' * V j)) := by
        simp [Matrix.sub_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hnew, hJJ, Matrix.mul_one, sub_self]
  have hP := isometry_norm_le P hPP
  have hQ := isometry_norm_le Q hQQ
  have hV (i) := isometry_norm_le (V i) (hVV i)
  have hJ (i) := isometry_norm_le (J i) (hJJ i)
  let q : ℝ := Real.sqrt (Fintype.card ι)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hqs : q ^ 2 = Fintype.card ι := Real.sq_sqrt (by positivity)
  have hL : ‖L‖ ≤ q := by
    have hs := orthogonal_sum_norm_sq (fun i ↦ V i * (J i)ᴴ) (by
      intro i j hij
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc, ← Matrix.mul_assoc (V i)ᴴ, hOrth i j hij,
        Matrix.zero_mul, Matrix.mul_zero])
    have heq : (∑ i, V i * (J i)ᴴ)ᴴ = L := by
      simp only [L, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    have hn (i) : ‖V i * (J i)ᴴ‖ ≤ 1 := by
      calc
        _ ≤ ‖V i‖ * ‖J i‖ := by
          simpa only [Matrix.l2_opNorm_conjTranspose] using Matrix.l2_opNorm_mul (V i) (J i)ᴴ
        _ ≤ 1 * 1 := mul_le_mul (hV i) (hJ i) (norm_nonneg _) zero_le_one
        _ = 1 := by ring
    have hb : ∑ i, ‖V i * (J i)ᴴ‖ ^ 2 ≤ (Fintype.card ι : ℝ) := by
      calc
        _ ≤ ∑ i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ ↦ by
          nlinarith [norm_nonneg (V i * (J i)ᴴ), hn i])
        _ = _ := by simp
    have ht : ‖L‖ = ‖∑ i, V i * (J i)ᴴ‖ := by
      rw [← heq, Matrix.l2_opNorm_conjTranspose]
    rw [← ht] at hs
    nlinarith [norm_nonneg L]
  have hE := outside_projection_norm_le d V hVV hOrth
  have hX : ‖X‖ ≤ q + a := by
    apply (norm_sub_le L (Pᴴ * A * E)).trans
    have hc : ‖Pᴴ * A * E‖ ≤ a := by
      calc
        _ ≤ (‖P‖ * ‖A‖) * ‖E‖ := by
          simpa only [Matrix.l2_opNorm_conjTranspose] using (Matrix.l2_opNorm_mul (Pᴴ * A) E).trans
            (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul Pᴴ A) (norm_nonneg E))
        _ ≤ (1 * a) * 1 := by gcongr
        _ = a := by ring
    exact add_le_add hL hc
  have hN : ‖N‖ ≤ q + a := by
    calc
      _ ≤ ‖Q‖ * ‖X‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * (q + a) := by gcongr
      _ = q + a := one_mul _
  let u := 1 + a + q
  let a₁ := a * u ^ 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ha₁ : 0 ≤ a₁ := by dsimp [a₁]; positivity
  have hA' : ‖A'‖ ≤ a₁ := by
    calc
      _ ≤ ‖A‖ * (1 + ‖N‖) ^ 2 := shear_norm_le A N
      _ ≤ a * (1 + (q + a)) ^ 2 := by gcongr
      _ = a₁ := by dsimp [a₁, u]; ring
  have hY : ‖Y‖ ≤ q * a₁ := by
    let Z := fun i ↦ (V i)ᴴ * A' * V i * (J i)ᴴ
    have hZ (i) : ‖Z i‖ ≤ a₁ := by
      calc
        _ ≤ ‖(V i)ᴴ * A' * V i‖ * ‖J i‖ := by
          simpa only [Z, Matrix.l2_opNorm_conjTranspose] using
            Matrix.l2_opNorm_mul ((V i)ᴴ * A' * V i) (J i)ᴴ
        _ ≤ a₁ * 1 := by
          gcongr
          · exact (compression_norm_le A' (V i) (V i) (hV i) (hV i)).trans hA'
          · exact hJ i
        _ = a₁ := mul_one _
    have hs := orthogonal_sum_norm_sq (fun i ↦ V i * Z i) (by
      intro i j hij
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (V i)ᴴ, hOrth i j hij, Matrix.zero_mul, Matrix.mul_zero])
    have hn (i) : ‖V i * Z i‖ ≤ a₁ := by
      calc
        _ ≤ ‖V i‖ * ‖Z i‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ 1 * a₁ := mul_le_mul (hV i) (hZ i) (norm_nonneg _) zero_le_one
        _ = a₁ := one_mul _
    have hb : ∑ i, ‖V i * Z i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * a₁ ^ 2 := by
      calc
        _ ≤ ∑ i : ι, a₁ ^ 2 := Finset.sum_le_sum (fun i _ ↦ by
          nlinarith [norm_nonneg (V i * Z i), hn i])
        _ = _ := by simp
    change ‖Y‖ ^ 2 ≤ _ at hs
    nlinarith [sq_nonneg (‖Y‖ - q * a₁), norm_nonneg Y, mul_nonneg hq ha₁]
  have hM : ‖M‖ ≤ q * a₁ := by
    calc
      _ ≤ ‖Y‖ * ‖P‖ := by
        simpa only [M, Matrix.l2_opNorm_conjTranspose] using Matrix.l2_opNorm_mul Y Pᴴ
      _ ≤ (q * a₁) * 1 := by gcongr
      _ = q * a₁ := mul_one _
  let v := 1 + q * a₁
  have hv : 0 ≤ v := by dsimp [v]; positivity
  let S := (1 + N) * (1 + M)
  let T := (1 - M) * (1 - N)
  have hST : S * T = 1 := by
    dsimp [S, T]
    calc
      _ = (1 + N) * ((1 + M) * (1 - M)) * (1 - N) := by noncomm_ring
      _ = 1 := by rw [NoEpsilon.Shear.one_add_mul_one_sub M hMM,
        Matrix.mul_one, NoEpsilon.Shear.one_add_mul_one_sub N hNN]
  have hTS : T * S = 1 := by
    dsimp [S, T]
    calc
      _ = (1 - M) * ((1 - N) * (1 + N)) * (1 + M) := by noncomm_ring
      _ = 1 := by rw [NoEpsilon.Shear.one_sub_mul_one_add N hNN,
        Matrix.mul_one, NoEpsilon.Shear.one_sub_mul_one_add M hMM]
  have heq : T * A * S = shear A' M := by dsimp [S, T, A', shear]; noncomm_ring
  have hNpm : ‖1 - N‖ ≤ u ∧ ‖1 + N‖ ≤ u := by
    obtain ⟨hm, hp⟩ := shear_factor_norm_le N
    dsimp [u]
    constructor <;> linarith
  have hMpm : ‖1 - M‖ ≤ v ∧ ‖1 + M‖ ≤ v := by
    obtain ⟨hm, hp⟩ := shear_factor_norm_le M
    dsimp [v]
    constructor <;> linarith
  have hS : ‖S‖ ≤ u * v := (norm_mul_le _ _).trans
    (mul_le_mul hNpm.2 hMpm.2 (norm_nonneg _) hu)
  have hT : ‖T‖ ≤ v * u := (norm_mul_le _ _).trans
    (mul_le_mul hMpm.1 hNpm.1 (norm_nonneg _) hv)
  refine ⟨S, T, hST, hTS, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heq, compression_shear_eq A' M Pᴴ Q hPM hMQ, hbridge']
  · intro i; rw [heq]; exact hzero i
  · rw [heq, shear_trace A' M hMM, shear_trace A N hNN]
  · rw [heq]
    calc
      _ ≤ ‖A'‖ * (1 + ‖M‖) ^ 2 := shear_norm_le A' M
      _ ≤ a₁ * (1 + q * a₁) ^ 2 := by gcongr
      _ = simultaneousBudget a (Fintype.card ι) := rfl
  · calc
      _ ≤ a * ((u * v) * (v * u)) := by gcongr
      _ = simultaneousBudget a (Fintype.card ι) := by
        change a * ((u * v) * (v * u)) = a₁ * v ^ 2
        dsimp [a₁]; ring

end NoEpsilon.Absorption
