import CommutatorTheorem.NoEpsilon.Shear
import CommutatorTheorem.NoEpsilon.BlockCompression
import CommutatorTheorem.NoEpsilon.NormBounds

/-!
# Absorption in an arbitrary ambient coordinate space

The formulas use rectangular isometries for the first, second, and selected outside
blocks. This lets the same two shears be iterated without changing the ambient index type.
All norms below are Euclidean operator norms.
-/

open scoped Matrix.Norms.L2Operator
open Matrix

namespace NoEpsilon.Absorption

variable {n r k l : Type*}
  [Fintype n] [Fintype r] [Fintype k] [Fintype l]
  [DecidableEq n] [DecidableEq r] [DecidableEq k] [DecidableEq l]

/-- Conjugation by an elementary shear and its explicit inverse. -/
noncomputable def shear (A N : Matrix n n ℂ) : Matrix n n ℂ := (1 - N) * A * (1 + N)

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
theorem compression_shear_eq (A N : Matrix n n ℂ)
    (L : Matrix k n ℂ) (R : Matrix n l ℂ) (hL : L * N = 0) (hR : N * R = 0) :
    L * shear A N * R = L * A * R := by
  have hleft : L * (1 - N) = L := by simp [Matrix.mul_sub, hL]
  have hright : (1 + N) * R = R := by simp [Matrix.add_mul, hR]
  calc
    L * shear A N * R = (L * (1 - N)) * A * ((1 + N) * R) := by
      simp only [shear, Matrix.mul_assoc]
    _ = L * A * R := by rw [hleft, hright]

omit [DecidableEq n] [DecidableEq r] [DecidableEq k] in
theorem square_zero_insertion (Q : Matrix n r ℂ) (X : Matrix r k ℂ)
    (V : Matrix n k ℂ) (hVQ : Vᴴ * Q = 0) :
    (Q * X * Vᴴ) * (Q * X * Vᴴ) = 0 := by
  calc
    _ = Q * X * (Vᴴ * Q) * X * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hVQ]; simp

theorem shear_trace (A N : Matrix n n ℂ) (hN : N * N = 0) :
    trace (shear A N) = trace A := by
  rw [shear, trace_mul_cycle, NoEpsilon.Shear.one_add_mul_one_sub N hN, Matrix.one_mul]

omit [DecidableEq r] [DecidableEq k] in
theorem first_shear_bridge (A : Matrix n n ℂ)
    (P Q : Matrix n r ℂ) (V : Matrix n k ℂ) (X : Matrix r k ℂ)
    (hPQ : Pᴴ * Q = 0) (hVQ : Vᴴ * Q = 0) :
    Pᴴ * shear A (Q * X * Vᴴ) * Q = Pᴴ * A * Q := by
  apply compression_shear_eq
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ]; simp
  · rw [Matrix.mul_assoc, hVQ]; simp

theorem first_shear_new_bridge (A : Matrix n n ℂ)
    (P Q : Matrix n r ℂ) (V : Matrix n k ℂ) (J : Matrix r k ℂ)
    (hPQ : Pᴴ * Q = 0) (hVV : Vᴴ * V = 1) (hA : Pᴴ * A * Q = 1) :
    Pᴴ * shear A (Q * (J - Pᴴ * A * V) * Vᴴ) * V = J := by
  let X := J - Pᴴ * A * V
  have hleft : Pᴴ * (1 - Q * X * Vᴴ) = Pᴴ := by
    simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPQ, Matrix.zero_mul, sub_zero]
  have hright : (1 + Q * X * Vᴴ) * V = V + Q * X := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hVV, Matrix.mul_one]
  calc
    Pᴴ * shear A (Q * X * Vᴴ) * V =
        (Pᴴ * (1 - Q * X * Vᴴ)) * A * ((1 + Q * X * Vᴴ) * V) := by
      simp only [shear, Matrix.mul_assoc]
    _ = Pᴴ * A * (V + Q * X) := by rw [hleft, hright]
    _ = Pᴴ * A * V + (Pᴴ * A * Q) * X := by rw [Matrix.mul_add, ← Matrix.mul_assoc]
    _ = J := by rw [hA, Matrix.one_mul]; dsimp [X]; abel

omit [DecidableEq r] [DecidableEq k] in
theorem second_shear_bridge (A : Matrix n n ℂ)
    (P Q : Matrix n r ℂ) (V : Matrix n k ℂ) (Y : Matrix k r ℂ)
    (hPV : Pᴴ * V = 0) (hPQ : Pᴴ * Q = 0) :
    Pᴴ * shear A (V * Y * Pᴴ) * Q = Pᴴ * A * Q := by
  apply compression_shear_eq
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPV]; simp
  · rw [Matrix.mul_assoc, hPQ]; simp

omit [DecidableEq r] in
theorem second_shear_zero (A : Matrix n n ℂ)
    (P : Matrix n r ℂ) (V : Matrix n k ℂ) (J : Matrix r k ℂ)
    (hPV : Pᴴ * V = 0) (hVV : Vᴴ * V = 1) (hJ : Jᴴ * J = 1)
    (hA : Pᴴ * A * V = J) :
    Vᴴ * shear A (V * (Vᴴ * A * V * Jᴴ) * Pᴴ) * V = 0 := by
  let Y := Vᴴ * A * V * Jᴴ
  have hleft : Vᴴ * (1 - V * Y * Pᴴ) = Vᴴ - Y * Pᴴ := by
    simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
  have hright : (1 + V * Y * Pᴴ) * V = V := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hPV, Matrix.mul_zero, add_zero]
  calc
    Vᴴ * shear A (V * Y * Pᴴ) * V =
        (Vᴴ * (1 - V * Y * Pᴴ)) * A * ((1 + V * Y * Pᴴ) * V) := by
      simp only [shear, Matrix.mul_assoc]
    _ = (Vᴴ - Y * Pᴴ) * A * V := by rw [hleft, hright]
    _ = Vᴴ * A * V - Y * (Pᴴ * A * V) := by simp only [Matrix.sub_mul, Matrix.mul_assoc]
    _ = 0 := by
      rw [hA]
      dsimp [Y]
      rw [Matrix.mul_assoc (Vᴴ * A * V) Jᴴ J, hJ, Matrix.mul_one, sub_self]

omit [DecidableEq r] [DecidableEq k] [Fintype l] [DecidableEq l] in
theorem outside_shear_unchanged (A : Matrix n n ℂ)
    (Q : Matrix n r ℂ) (V : Matrix n k ℂ) (W : Matrix n l ℂ)
    (X : Matrix r k ℂ) (hWQ : Wᴴ * Q = 0) (hVW : Vᴴ * W = 0) :
    Wᴴ * shear A (Q * X * Vᴴ) * W = Wᴴ * A * W := by
  apply compression_shear_eq
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hWQ]; simp
  · rw [Matrix.mul_assoc, hVW]; simp

/-- The two shears preserve the identity corner and clear the selected outside block. -/
theorem two_shear_elimination (A : Matrix n n ℂ)
    (P Q : Matrix n r ℂ) (V : Matrix n k ℂ) (J : Matrix r k ℂ)
    (hPQ : Pᴴ * Q = 0) (hPV : Pᴴ * V = 0) (hVQ : Vᴴ * Q = 0)
    (hVV : Vᴴ * V = 1) (hJ : Jᴴ * J = 1) (hA : Pᴴ * A * Q = 1) :
    let N := Q * (J - Pᴴ * A * V) * Vᴴ
    let A' := shear A N
    let M := V * (Vᴴ * A' * V * Jᴴ) * Pᴴ
    Pᴴ * shear A' M * Q = 1 ∧ Vᴴ * shear A' M * V = 0 ∧
      trace (shear A' M) = trace A := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [second_shear_bridge _ P Q V _ hPV hPQ,
      first_shear_bridge _ P Q V _ hPQ hVQ, hA]
  · exact second_shear_zero _ P V J hPV hVV hJ
      (first_shear_new_bridge A P Q V J hPQ hVV hA)
  · rw [shear_trace _ _ (square_zero_insertion V _ P hPV),
      shear_trace _ _ (square_zero_insertion Q _ V hVQ)]

omit [DecidableEq n] in
/-- Any rectangular isometry has operator norm at most one, including an empty domain. -/
theorem isometry_norm_le (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) : ‖V‖ ≤ 1 := by
  have hs := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [hV] at hs
  have hn := NoEpsilon.matrix_norm_one_le (ι := k)
  rw [hs] at hn
  nlinarith [norm_nonneg V]

theorem compression_norm_le (A : Matrix n n ℂ)
    (P : Matrix n r ℂ) (V : Matrix n k ℂ) (hP : ‖P‖ ≤ 1) (hV : ‖V‖ ≤ 1) :
    ‖Pᴴ * A * V‖ ≤ ‖A‖ := by
  calc
    _ ≤ (‖Pᴴ‖ * ‖A‖) * ‖V‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * ‖A‖) * 1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = ‖A‖ := by ring

theorem insertion_norm_le (Q : Matrix n r ℂ) (V : Matrix n k ℂ)
    (X : Matrix r k ℂ) (hQ : ‖Q‖ ≤ 1) (hV : ‖V‖ ≤ 1) :
    ‖Q * X * Vᴴ‖ ≤ ‖X‖ := by
  calc
    _ ≤ (‖Q‖ * ‖X‖) * ‖Vᴴ‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * ‖X‖) * 1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = ‖X‖ := by ring

set_option maxHeartbeats 2000000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
theorem shear_factor_norm_le (N : Matrix n n ℂ) :
    ‖1 - N‖ ≤ 1 + ‖N‖ ∧ ‖1 + N‖ ≤ 1 + ‖N‖ := by
  have hOne : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := NoEpsilon.matrix_norm_one_le
  constructor
  · exact (norm_sub_le (1 : Matrix n n ℂ) N).trans (add_le_add hOne le_rfl)
  · exact (norm_add_le (1 : Matrix n n ℂ) N).trans (add_le_add hOne le_rfl)

theorem shear_norm_le (A N : Matrix n n ℂ) :
    ‖shear A N‖ ≤ ‖A‖ * (1 + ‖N‖) ^ 2 := by
  obtain ⟨hminus, hplus⟩ := shear_factor_norm_le N
  calc
    _ ≤ (‖1 - N‖ * ‖1 + N‖) * ‖A‖ := norm_conjugation_le _ _ _
    _ ≤ ((1 + ‖N‖) * (1 + ‖N‖)) * ‖A‖ := by gcongr
    _ = ‖A‖ * (1 + ‖N‖) ^ 2 := by ring

/-- Norm growth after the first of the two outside-block shears. -/
def firstBudget (a : ℝ) : ℝ := a * (a + 2) ^ 2

/-- Norm growth after clearing one outside block. -/
def stepBudget (a : ℝ) : ℝ := firstBudget a * (1 + firstBudget a) ^ 2

theorem two_shear_generators_le (A : Matrix n n ℂ)
    (P Q : Matrix n r ℂ) (V : Matrix n k ℂ) (J : Matrix r k ℂ) (a : ℝ)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hV : ‖V‖ ≤ 1) (hJ : ‖J‖ ≤ 1)
    (hA : ‖A‖ ≤ a) :
    let N := Q * (J - Pᴴ * A * V) * Vᴴ
    let A' := shear A N
    let M := V * (Vᴴ * A' * V * Jᴴ) * Pᴴ
    ‖N‖ ≤ 1 + a ∧ ‖A'‖ ≤ firstBudget a ∧ ‖M‖ ≤ firstBudget a := by
  let N := Q * (J - Pᴴ * A * V) * Vᴴ
  let A' := shear A N
  let M := V * (Vᴴ * A' * V * Jᴴ) * Pᴴ
  have ha : 0 ≤ a := (norm_nonneg A).trans hA
  have hN : ‖N‖ ≤ 1 + a := by
    exact (insertion_norm_le Q V _ hQ hV).trans
      ((norm_sub_le _ _).trans (add_le_add hJ ((compression_norm_le A P V hP hV).trans hA)))
  have hA' : ‖A'‖ ≤ firstBudget a := by
    calc
      _ ≤ ‖A‖ * (1 + ‖N‖) ^ 2 := shear_norm_le A N
      _ ≤ a * (1 + (1 + a)) ^ 2 := by gcongr
      _ = firstBudget a := by dsimp [firstBudget]; ring
  have hb : 0 ≤ firstBudget a := (norm_nonneg A').trans hA'
  have hM : ‖M‖ ≤ firstBudget a := by
    apply (insertion_norm_le V P _ hV hP).trans
    calc
      _ ≤ ‖Vᴴ * A' * V‖ * ‖Jᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ firstBudget a * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact mul_le_mul ((compression_norm_le A' V V hV hV).trans hA')
          hJ (norm_nonneg _) hb
      _ = firstBudget a := mul_one _
  exact ⟨hN, hA', hM⟩

theorem two_shear_norm_bound (A : Matrix n n ℂ)
    (P Q : Matrix n r ℂ) (V : Matrix n k ℂ) (J : Matrix r k ℂ) (a : ℝ)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hV : ‖V‖ ≤ 1) (hJ : ‖J‖ ≤ 1)
    (hA : ‖A‖ ≤ a) :
    let N := Q * (J - Pᴴ * A * V) * Vᴴ
    let A' := shear A N
    let M := V * (Vᴴ * A' * V * Jᴴ) * Pᴴ
    ‖shear A' M‖ ≤ stepBudget a := by
  let N := Q * (J - Pᴴ * A * V) * Vᴴ
  let A' := shear A N
  let M := V * (Vᴴ * A' * V * Jᴴ) * Pᴴ
  obtain ⟨hN, hA', hM⟩ := two_shear_generators_le A P Q V J a hP hQ hV hJ hA
  have hb : 0 ≤ firstBudget a := (norm_nonneg A').trans hA'
  calc
    _ ≤ ‖A'‖ * (1 + ‖M‖) ^ 2 := shear_norm_le A' M
    _ ≤ firstBudget a * (1 + firstBudget a) ^ 2 := by gcongr
    _ = stepBudget a := rfl


/-- The condition-number budget of one complete absorption step. -/
def stepCondition (a : ℝ) : ℝ := (a + 2) ^ 2 * (1 + firstBudget a) ^ 2

theorem stepBudget_eq (a : ℝ) : stepBudget a = a * stepCondition a := by
  unfold stepBudget stepCondition firstBudget
  ring

universe u

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedFintypeInType false in
/-- Clear one external block by explicit invertible factors, with quantitative control.
Every orthogonal outside compression is preserved, so the operation can be iterated. -/
theorem eliminate_one (A : Matrix n n ℂ)
    (P Q : Matrix n r ℂ) (V : Matrix n k ℂ) (J : Matrix r k ℂ) (a : ℝ)
    (hPP : Pᴴ * P = 1) (hQQ : Qᴴ * Q = 1) (hVV : Vᴴ * V = 1)
    (hPQ : Pᴴ * Q = 0) (hPV : Pᴴ * V = 0) (hVQ : Vᴴ * Q = 0)
    (hJJ : Jᴴ * J = 1) (hbridge : Pᴴ * A * Q = 1) (hA : ‖A‖ ≤ a) :
    ∃ S T : Matrix n n ℂ,
      S * T = 1 ∧ T * S = 1 ∧
      Pᴴ * (T * A * S) * Q = 1 ∧ Vᴴ * (T * A * S) * V = 0 ∧
      trace (T * A * S) = trace A ∧ ‖T * A * S‖ ≤ stepBudget a ∧
      ‖S‖ * ‖T‖ ≤ stepCondition a ∧
      ∀ (l : Type u) (W : Matrix n l ℂ),
        Wᴴ * Q = 0 → Vᴴ * W = 0 → Wᴴ * V = 0 → Pᴴ * W = 0 →
        Wᴴ * (T * A * S) * W = Wᴴ * A * W := by
  let N := Q * (J - Pᴴ * A * V) * Vᴴ
  let A' := shear A N
  let M := V * (Vᴴ * A' * V * Jᴴ) * Pᴴ
  let S := (1 + N) * (1 + M)
  let T := (1 - M) * (1 - N)
  have hN : N * N = 0 := square_zero_insertion Q _ V hVQ
  have hM : M * M = 0 := square_zero_insertion V _ P hPV
  have hST : S * T = 1 := by
    dsimp [S, T]
    calc
      _ = (1 + N) * ((1 + M) * (1 - M)) * (1 - N) := by noncomm_ring
      _ = 1 := by rw [NoEpsilon.Shear.one_add_mul_one_sub M hM,
        Matrix.mul_one, NoEpsilon.Shear.one_add_mul_one_sub N hN]
  have hTS : T * S = 1 := by
    dsimp [S, T]
    calc
      _ = (1 - M) * ((1 - N) * (1 + N)) * (1 + M) := by noncomm_ring
      _ = 1 := by rw [NoEpsilon.Shear.one_sub_mul_one_add N hN,
        Matrix.mul_one, NoEpsilon.Shear.one_sub_mul_one_add M hM]
  have heq : T * A * S = shear A' M := by
    dsimp [S, T, A', shear]
    noncomm_ring
  have hP := isometry_norm_le P hPP
  have hQ := isometry_norm_le Q hQQ
  have hV := isometry_norm_le V hVV
  have hJ := isometry_norm_le J hJJ
  obtain ⟨hnew, hzero, htrace⟩ := two_shear_elimination A P Q V J
    hPQ hPV hVQ hVV hJJ hbridge
  obtain ⟨hNnorm, hA'norm, hMnorm⟩ := two_shear_generators_le A P Q V J a
    hP hQ hV hJ hA
  have ha : 0 ≤ a := (norm_nonneg A).trans hA
  have hb : 0 ≤ firstBudget a := (norm_nonneg A').trans hA'norm
  have hS : ‖S‖ ≤ (a + 2) * (1 + firstBudget a) := by
    calc
      _ ≤ ‖1 + N‖ * ‖1 + M‖ := norm_mul_le _ _
      _ ≤ (1 + ‖N‖) * (1 + ‖M‖) := by
        gcongr
        · exact (shear_factor_norm_le N).2
        · exact (shear_factor_norm_le M).2
      _ ≤ (1 + (1 + a)) * (1 + firstBudget a) := by gcongr
      _ = (a + 2) * (1 + firstBudget a) := by ring
  have hT : ‖T‖ ≤ (a + 2) * (1 + firstBudget a) := by
    calc
      _ ≤ ‖1 - M‖ * ‖1 - N‖ := norm_mul_le _ _
      _ ≤ (1 + ‖M‖) * (1 + ‖N‖) := by
        gcongr
        · exact (shear_factor_norm_le M).1
        · exact (shear_factor_norm_le N).1
      _ ≤ (1 + firstBudget a) * (1 + (1 + a)) := by gcongr
      _ = (a + 2) * (1 + firstBudget a) := by ring
  refine ⟨S, T, hST, hTS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [heq] using hnew
  · simpa only [heq] using hzero
  · simpa only [heq] using htrace
  · rw [heq]
    exact two_shear_norm_bound A P Q V J a hP hQ hV hJ hA
  · calc
      _ ≤ ((a + 2) * (1 + firstBudget a)) ^ 2 := by
        nlinarith [mul_le_mul hS hT (norm_nonneg T) (by positivity)]
      _ = stepCondition a := by dsimp [stepCondition]; ring
  · intro l W hWQ hVW hWV hPW
    rw [heq, outside_shear_unchanged A' V P W _ hWV hPW,
      outside_shear_unchanged A Q V W _ hWQ hVW]


-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- Clear any finite family of outside blocks. The ambient dimension stays fixed, and
the total condition-number estimate telescopes through the same norm-growth function. -/
theorem eliminate_finset {ι : Type*} [DecidableEq ι]
    (d : ι → Type u) [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
    (P Q : Matrix n r ℂ) (V : ∀ i, Matrix n (d i) ℂ)
    (J : ∀ i, Matrix r (d i) ℂ)
    (hPP : Pᴴ * P = 1) (hQQ : Qᴴ * Q = 1) (hPQ : Pᴴ * Q = 0)
    (hVV : ∀ i, (V i)ᴴ * V i = 1) (hPV : ∀ i, Pᴴ * V i = 0)
    (hVQ : ∀ i, (V i)ᴴ * Q = 0)
    (hOrth : ∀ i j, i ≠ j → (V i)ᴴ * V j = 0)
    (hJJ : ∀ i, (J i)ᴴ * J i = 1)
    (s : Finset ι) (A : Matrix n n ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hbridge : Pᴴ * A * Q = 1) (hA : ‖A‖ ≤ a) :
    ∃ S T : Matrix n n ℂ,
      S * T = 1 ∧ T * S = 1 ∧ Pᴴ * (T * A * S) * Q = 1 ∧
      (∀ i ∈ s, (V i)ᴴ * (T * A * S) * V i = 0) ∧
      (∀ i ∉ s, (V i)ᴴ * (T * A * S) * V i = (V i)ᴴ * A * V i) ∧
      trace (T * A * S) = trace A ∧
      ‖T * A * S‖ ≤ (stepBudget^[s.card]) a ∧
      a * (‖S‖ * ‖T‖) ≤ (stepBudget^[s.card]) a := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, 1, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hbridge
    · simp
    · simp
    · simp
    · simpa using hA
    · have hOne : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := NoEpsilon.matrix_norm_one_le
      have hc : ‖(1 : Matrix n n ℂ)‖ * ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
        nlinarith [norm_nonneg (1 : Matrix n n ℂ)]
      simpa using mul_le_mul_of_nonneg_left hc ha
  | @insert j s hjs ih =>
    obtain ⟨S₀, T₀, hST₀, hTS₀, hbridge₀, hzero₀, hother₀, htr₀, hnorm₀, hc₀⟩ := ih
    let A₀ := T₀ * A * S₀
    let b := (stepBudget^[s.card]) a
    have hb : 0 ≤ b := (norm_nonneg A₀).trans hnorm₀
    obtain ⟨S₁, T₁, hST₁, hTS₁, hbridge₁, hzero₁, htr₁, hnorm₁, hc₁, hother₁⟩ :=
      eliminate_one A₀ P Q (V j) (J j) b
        hPP hQQ (hVV j) hPQ (hPV j) (hVQ j) (hJJ j) hbridge₀ hnorm₀
    have heq : (T₁ * T₀) * A * (S₀ * S₁) = T₁ * A₀ * S₁ := by
      dsimp [A₀]
      simp only [Matrix.mul_assoc]
    have hbudget : (stepBudget^[(insert j s).card]) a = stepBudget b := by
      rw [Finset.card_insert_of_notMem hjs, Function.iterate_succ_apply']
    have hunchanged (i : ι) (hij : i ≠ j) :
        (V i)ᴴ * (T₁ * A₀ * S₁) * V i = (V i)ᴴ * A₀ * V i :=
      hother₁ (d i) (V i) (hVQ i) (hOrth j i hij.symm) (hOrth i j hij) (hPV i)
    refine ⟨S₀ * S₁, T₁ * T₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        _ = S₀ * (S₁ * T₁) * T₀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hST₁, Matrix.mul_one, hST₀]
    · calc
        _ = T₁ * (T₀ * S₀) * S₁ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hTS₀, Matrix.mul_one, hTS₁]
    · simpa only [heq] using hbridge₁
    · intro i hi
      rw [heq]
      rcases Finset.mem_insert.mp hi with rfl | his
      · exact hzero₁
      · rw [hunchanged i (by intro hij; subst i; exact hjs his)]
        exact hzero₀ i his
    · intro i hi
      rw [Finset.mem_insert, not_or] at hi
      rw [heq, hunchanged i hi.1]
      exact hother₀ i hi.2
    · rw [heq, htr₁]
      exact htr₀
    · simpa only [heq, hbudget] using hnorm₁
    · rw [hbudget]
      calc
        a * (‖S₀ * S₁‖ * ‖T₁ * T₀‖) ≤
            a * ((‖S₀‖ * ‖S₁‖) * (‖T₁‖ * ‖T₀‖)) := by
          gcongr <;> apply norm_mul_le
        _ = (a * (‖S₀‖ * ‖T₀‖)) * (‖S₁‖ * ‖T₁‖) := by ring
        _ ≤ b * stepCondition b :=
          mul_le_mul hc₀ hc₁ (mul_nonneg (norm_nonneg S₁) (norm_nonneg T₁)) hb
        _ = stepBudget b := (stepBudget_eq b).symm

end NoEpsilon.Absorption
