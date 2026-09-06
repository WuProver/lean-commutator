import CommutatorTheorem.NoEpsilon.BlockAlgebra
import CommutatorTheorem.NoEpsilon.Riccati
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic

/-!
# Norm budgets for the identity-corner construction

The ring estimates use any submultiplicative norm. Matrix estimates below explicitly
activate the Euclidean operator norm, including for rectangular embedding matrices.
-/

namespace NoEpsilon

section RingBounds

variable {E : Type*} [NormedRing E]

theorem norm_ringCommutator_le (X Y : E) :
    ‖ringCommutator X Y‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
  calc
    ‖ringCommutator X Y‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖X‖ * ‖Y‖ := by ring

/-- A similarity costs at most the product of the norms of its two explicit factors. -/
theorem norm_conjugation_le (S X S' : E) :
    ‖S * X * S'‖ ≤ (‖S‖ * ‖S'‖) * ‖X‖ := by
  calc
    ‖S * X * S'‖ ≤ ‖S * X‖ * ‖S'‖ := norm_mul_le _ _
    _ ≤ (‖S‖ * ‖X‖) * ‖S'‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = (‖S‖ * ‖S'‖) * ‖X‖ := by ring

theorem norm_conjugation_product_le (S S' B C : E) :
    ‖S * B * S'‖ * ‖S * C * S'‖ ≤ (‖S‖ * ‖S'‖) ^ 2 * (‖B‖ * ‖C‖) := by
  calc
    ‖S * B * S'‖ * ‖S * C * S'‖ ≤
        ((‖S‖ * ‖S'‖) * ‖B‖) * ((‖S‖ * ‖S'‖) * ‖C‖) := by
      gcongr <;> apply norm_conjugation_le
    _ = (‖S‖ * ‖S'‖) ^ 2 * (‖B‖ * ‖C‖) := by ring

theorem norm_firstDefect_le (A U V : E) (a p : ℝ)
    (hA : ‖A‖ ≤ a) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ p) :
    ‖ringCommutator U V - A‖ ≤ 2 * p + a := by
  calc
    ‖ringCommutator U V - A‖ ≤ ‖ringCommutator U V‖ + ‖A‖ := norm_sub_le _ _
    _ ≤ 2 * ‖U‖ * ‖V‖ + a := add_le_add (norm_ringCommutator_le _ _) hA
    _ ≤ 2 * 1 * p + a := by gcongr
    _ = 2 * p + a := by ring

theorem norm_secondDefect_le (A F U K V T : E) (a p : ℝ)
    (hA : ‖A‖ ≤ a) (hF : ‖F‖ ≤ a) (hU : ‖U‖ ≤ 1) (hK : ‖K‖ ≤ 1)
    (hV : ‖V‖ ≤ p) (hT : ‖T‖ ≤ p) :
    ‖ringCommutator K V + (ringCommutator U V - A) * U - K +
      ringCommutator U (T * K) - F‖ ≤ 6 * p + 2 * a + 1 := by
  have hp : 0 ≤ p := (norm_nonneg V).trans hV
  have ha : 0 ≤ a := (norm_nonneg A).trans hA
  have hTK : ‖T * K‖ ≤ p := by
    calc
      ‖T * K‖ ≤ ‖T‖ * ‖K‖ := norm_mul_le _ _
      _ ≤ p * 1 := by gcongr
      _ = p := mul_one p
  have hFirst := norm_firstDefect_le A U V a p hA hU hV
  have hFirstMul : ‖(ringCommutator U V - A) * U‖ ≤ 2 * p + a := by
    calc
      ‖(ringCommutator U V - A) * U‖ ≤ ‖ringCommutator U V - A‖ * ‖U‖ :=
        norm_mul_le _ _
      _ ≤ (2 * p + a) * 1 := by gcongr
      _ = 2 * p + a := mul_one _
  have hCommKV : ‖ringCommutator K V‖ ≤ 2 * p := by
    apply (norm_ringCommutator_le K V).trans
    calc
      2 * ‖K‖ * ‖V‖ ≤ 2 * 1 * p := by gcongr
      _ = 2 * p := by ring
  have hCommUTK : ‖ringCommutator U (T * K)‖ ≤ 2 * p := by
    apply (norm_ringCommutator_le U (T * K)).trans
    calc
      2 * ‖U‖ * ‖T * K‖ ≤ 2 * 1 * p := by gcongr
      _ = 2 * p := by ring
  calc
    ‖ringCommutator K V + (ringCommutator U V - A) * U - K +
        ringCommutator U (T * K) - F‖ ≤
      ‖ringCommutator K V‖ + ‖(ringCommutator U V - A) * U‖ + ‖K‖ +
        ‖ringCommutator U (T * K)‖ + ‖F‖ := by
      calc
        _ ≤ ‖ringCommutator K V + (ringCommutator U V - A) * U - K +
            ringCommutator U (T * K)‖ + ‖F‖ := norm_sub_le _ _
        _ ≤ (‖ringCommutator K V + (ringCommutator U V - A) * U - K‖ +
            ‖ringCommutator U (T * K)‖) + ‖F‖ := by gcongr; apply norm_add_le
        _ ≤ ((‖ringCommutator K V + (ringCommutator U V - A) * U‖ + ‖K‖) +
            ‖ringCommutator U (T * K)‖) + ‖F‖ := by gcongr; apply norm_sub_le
        _ ≤ _ := by gcongr; apply norm_add_le
    _ ≤ 6 * p + 2 * a + 1 := by linarith

theorem norm_companion_lowerLeft_le (A U K V T Q : E) (p : ℝ)
    (hK : ‖K‖ ≤ 1) (hT : ‖T‖ ≤ p) (hQ : ‖Q - (ringCommutator U V - A)‖ ≤ 1) :
    ‖A + Q - ringCommutator U V + T * K‖ ≤ 1 + p := by
  have hp : 0 ≤ p := (norm_nonneg T).trans hT
  have hId : A + Q - ringCommutator U V + T * K =
      (Q - (ringCommutator U V - A)) + T * K := by noncomm_ring
  rw [hId]
  calc
    _ ≤ ‖Q - (ringCommutator U V - A)‖ + ‖T * K‖ := norm_add_le _ _
    _ ≤ 1 + ‖T‖ * ‖K‖ := add_le_add hQ (norm_mul_le _ _)
    _ ≤ 1 + p * 1 := by gcongr
    _ = 1 + p := by ring

end RingBounds

/-- The dimension-free scale with the two supplied second factors bounded by `2 * a`. -/
noncomputable def identityCornerScale (a : ℝ) : ℝ :=
  2 * max ((5 * a + 1) ^ 2 + (2 * a + 1) * (5 * a + 1) + (14 * a + 1))
    (2 * (5 * a + 1) + 2 * a + 1)

/-- The explicit uniform product budget used by the bounded identity-corner theorem. -/
noncomputable def identityCornerNormBudget (a : ℝ) : ℝ :=
  (1 + (5 * a + 1)) ^ 4 * (identityCornerScale a + 3) *
    ((identityCornerScale a + 5) * (2 * a) + 2)

theorem identityCornerScale_pos (a : ℝ) (ha : 0 ≤ a) : 0 < identityCornerScale a := by
  unfold identityCornerScale
  apply mul_pos (by norm_num)
  exact lt_of_lt_of_le (by positivity) (le_max_right _ _)

section MatrixBounds

open scoped Matrix Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Valid also for an empty index type, where the identity matrix has norm zero. -/
theorem matrix_norm_one_le : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ ↦ by simp)

theorem norm_rowEmbedding_left_le :
    ‖Matrix.fromRows (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)‖ ≤ 1 := by
  let J := Matrix.fromRows (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)
  have hJJ : Jᴴ * J = 1 := by
    simp [J, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  have hNorm := Matrix.l2_opNorm_conjTranspose_mul_self J
  rw [hJJ] at hNorm
  have hOne : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := matrix_norm_one_le
  change ‖J‖ ≤ 1
  nlinarith [norm_nonneg J]

theorem norm_rowEmbedding_right_le :
    ‖Matrix.fromRows (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)‖ ≤ 1 := by
  let J := Matrix.fromRows (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
  have hJJ : Jᴴ * J = 1 := by
    simp [J, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  have hNorm := Matrix.l2_opNorm_conjTranspose_mul_self J
  rw [hJJ] at hNorm
  have hOne : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := matrix_norm_one_le
  change ‖J‖ ≤ 1
  nlinarith [norm_nonneg J]

private theorem norm_embedding_sandwich_le (E F : Matrix (ι ⊕ ι) ι ℂ)
    (A : Matrix ι ι ℂ) (hE : ‖E‖ ≤ 1) (hF : ‖F‖ ≤ 1) :
    ‖E * A * Fᴴ‖ ≤ ‖A‖ := by
  calc
    ‖E * A * Fᴴ‖ ≤ ‖E * A‖ * ‖Fᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖E‖ * ‖A‖) * ‖F‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖A‖) * 1 := by gcongr
    _ = ‖A‖ := by ring

/-- A block sum estimate in Euclidean operator norm, with no dimension factor. -/
theorem norm_fromBlocks_le (A B C D : Matrix ι ι ℂ) :
    ‖Matrix.fromBlocks A B C D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  let E := Matrix.fromRows (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)
  let F := Matrix.fromRows (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
  have hE : ‖E‖ ≤ 1 := norm_rowEmbedding_left_le
  have hF : ‖F‖ ≤ 1 := norm_rowEmbedding_right_le
  have hDecomp : Matrix.fromBlocks A B C D =
      E * A * Eᴴ + E * B * Fᴴ + F * C * Eᴴ + F * D * Fᴴ := by
    simp only [E, F, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.fromRows_mul,
      one_mul, zero_mul]
    simp only [Matrix.mul_fromCols, mul_one, mul_zero, Matrix.fromCols_zero]
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.fromCols, Matrix.fromRows]
  rw [hDecomp]
  have hA := norm_embedding_sandwich_le E E A hE hE
  have hB := norm_embedding_sandwich_le E F B hE hF
  have hC := norm_embedding_sandwich_le F E C hF hE
  have hD := norm_embedding_sandwich_le F F D hF hF
  linarith [norm_add_le (E * A * Eᴴ) (E * B * Fᴴ),
    norm_add_le (E * A * Eᴴ + E * B * Fᴴ) (F * C * Eᴴ),
    norm_add_le (E * A * Eᴴ + E * B * Fᴴ + F * C * Eᴴ) (F * D * Fᴴ)]

theorem norm_lowerShear_le (Q : Matrix ι ι ℂ) : ‖lowerShear Q‖ ≤ 1 + ‖Q‖ := by
  have hId : lowerShear Q = 1 + Matrix.fromBlocks 0 0 Q 0 := by
    ext i j
    cases i <;> cases j <;> simp [lowerShear, Matrix.fromBlocks, Matrix.one_apply]
  rw [hId]
  have hBlock := norm_fromBlocks_le (0 : Matrix ι ι ℂ) 0 Q 0
  simp only [norm_zero, zero_add, add_zero] at hBlock
  exact (norm_add_le _ _).trans (add_le_add matrix_norm_one_le hBlock)

theorem norm_lowerShearInverse_le (Q : Matrix ι ι ℂ) :
    ‖lowerShearInverse Q‖ ≤ 1 + ‖Q‖ := by
  simpa only [lowerShearInverse, lowerShear, norm_neg] using norm_lowerShear_le (-Q)

theorem norm_scalar_shift_le (lam : ℝ) (hLam : 0 ≤ lam) (U : Matrix ι ι ℂ)
    (hU : ‖U‖ ≤ 1) : ‖lam • 1 + U‖ ≤ lam + 1 := by
  letI : NormedSpace ℝ (Matrix ι ι ℂ) := NormedSpace.restrictScalars ℝ ℂ _
  calc
    ‖lam • 1 + U‖ ≤ ‖lam • (1 : Matrix ι ι ℂ)‖ + ‖U‖ := norm_add_le _ _
    _ ≤ ‖lam‖ * ‖(1 : Matrix ι ι ℂ)‖ + ‖U‖ :=
      add_le_add (NormedSpace.norm_smul_le lam (1 : Matrix ι ι ℂ)) le_rfl
    _ = lam * ‖(1 : Matrix ι ι ℂ)‖ + ‖U‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hLam]
    _ ≤ lam * 1 + 1 := by gcongr; exact matrix_norm_one_le
    _ = lam + 1 := by ring

theorem norm_companionFirst_le (U K : Matrix ι ι ℂ) (hK : ‖K‖ ≤ 1) :
    ‖companionFirst U K‖ ≤ ‖U‖ + 2 := by
  have h := norm_fromBlocks_le U 1 K 0
  simp only [norm_zero, add_zero] at h
  have hOne : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := matrix_norm_one_le
  simpa only [companionFirst, norm_zero, add_zero] using
    h.trans (by linarith)

theorem norm_companionFirst_shift_le (lam : ℝ) (hLam : 0 ≤ lam)
    (U K : Matrix ι ι ℂ) (hU : ‖U‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    ‖companionFirst (lam • 1 + U) K‖ ≤ lam + 3 := by
  have hFirst := norm_companionFirst_le (lam • 1 + U) K hK
  have hShift := norm_scalar_shift_le lam hLam U hU
  linarith

theorem norm_riccatiConstant_le (A F U K V T : Matrix ι ι ℂ) (a p : ℝ)
    (hA : ‖A‖ ≤ a) (hF : ‖F‖ ≤ a) (hU : ‖U‖ ≤ 1) (hK : ‖K‖ ≤ 1)
    (hV : ‖V‖ ≤ p) (hT : ‖T‖ ≤ p) :
    ‖riccatiConstant A F U K V T‖ ≤ 6 * p + 2 * a + 1 := by
  exact norm_secondDefect_le A F U K V T a p hA hF hU hK hV hT

theorem norm_riccati_point_le (A U V Q : Matrix ι ι ℂ) (a p : ℝ)
    (hA : ‖A‖ ≤ a) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ p)
    (hQ : ‖Q - (ringCommutator U V - A)‖ ≤ 1) :
    ‖Q‖ ≤ 2 * p + a + 1 := by
  have hFirst := norm_firstDefect_le A U V a p hA hU hV
  have h := norm_le_norm_sub_add Q (ringCommutator U V - A)
  linarith

theorem norm_companionSecond_shift_le (lam : ℝ) (hLam : 0 ≤ lam)
    (A U K V T Q : Matrix ι ι ℂ) (p : ℝ)
    (hU : ‖U‖ ≤ 1) (hK : ‖K‖ ≤ 1) (hV : ‖V‖ ≤ p) (hT : ‖T‖ ≤ p)
    (hQ : ‖Q - (ringCommutator U V - A)‖ ≤ 1) :
    ‖companionSecond A (lam • 1 + U) K V T Q‖ ≤ (lam + 5) * p + 2 := by
  have hp : 0 ≤ p := (norm_nonneg V).trans hV
  have hShift := norm_scalar_shift_le lam hLam U hU
  have hOne : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := matrix_norm_one_le
  have hLower : ‖A + Q - ringCommutator (lam • 1 + U) V + T * K‖ ≤ 1 + p := by
    rw [ringCommutator_scalar_shift]
    exact norm_companion_lowerLeft_le A U K V T Q p hK hT hQ
  have hRight : ‖V + 1 - (lam • 1 + U) * T‖ ≤ 1 + (lam + 2) * p := by
    calc
      _ ≤ ‖V + 1‖ + ‖(lam • 1 + U) * T‖ := norm_sub_le _ _
      _ ≤ (‖V‖ + ‖(1 : Matrix ι ι ℂ)‖) + ‖lam • 1 + U‖ * ‖T‖ :=
        add_le_add (norm_add_le _ _) (norm_mul_le _ _)
      _ ≤ (p + 1) + (lam + 1) * p := by gcongr
      _ = 1 + (lam + 2) * p := by ring
  have hBlocks := norm_fromBlocks_le V T
    (A + Q - ringCommutator (lam • 1 + U) V + T * K) (V + 1 - (lam • 1 + U) * T)
  change ‖Matrix.fromBlocks V T _ _‖ ≤ _
  linarith

/-- The entire explicit factor pair has a dimension-free product budget. -/
theorem norm_identityCorner_factors_le (lam : ℝ) (hLam : 0 ≤ lam)
    (A U K V T Q : Matrix ι ι ℂ) (p q : ℝ)
    (hU : ‖U‖ ≤ 1) (hK : ‖K‖ ≤ 1) (hV : ‖V‖ ≤ p) (hT : ‖T‖ ≤ p)
    (hQ : ‖Q - (ringCommutator U V - A)‖ ≤ 1) (hq : ‖Q‖ ≤ q) :
    ‖lowerShear Q * companionFirst (lam • 1 + U) K * lowerShearInverse Q‖ *
      ‖lowerShear Q * companionSecond A (lam • 1 + U) K V T Q * lowerShearInverse Q‖ ≤
        (1 + q) ^ 4 * (lam + 3) * ((lam + 5) * p + 2) := by
  have hp : 0 ≤ p := (norm_nonneg V).trans hV
  have hq₀ : 0 ≤ q := (norm_nonneg Q).trans hq
  have hS : ‖lowerShear Q‖ ≤ 1 + q := (norm_lowerShear_le Q).trans (by linarith)
  have hS' : ‖lowerShearInverse Q‖ ≤ 1 + q :=
    (norm_lowerShearInverse_le Q).trans (by linarith)
  have hB := norm_companionFirst_shift_le lam hLam U K hU hK
  have hC := norm_companionSecond_shift_le lam hLam A U K V T Q p hU hK hV hT hQ
  calc
    _ ≤ (‖lowerShear Q‖ * ‖lowerShearInverse Q‖) ^ 2 *
        (‖companionFirst (lam • 1 + U) K‖ *
          ‖companionSecond A (lam • 1 + U) K V T Q‖) := norm_conjugation_product_le _ _ _ _
    _ ≤ ((1 + q) * (1 + q)) ^ 2 * ((lam + 3) * ((lam + 5) * p + 2)) := by gcongr
    _ = (1 + q) ^ 4 * (lam + 3) * ((lam + 5) * p + 2) := by ring

/-- The Riccati existence theorem and the complete operator-norm budget are joined here.
Only the supplied bounded two-commutator representation remains an input assumption. -/
theorem exists_identityCorner_commutator_bounded (A F D U K V T : Matrix ι ι ℂ)
    (a : ℝ) (hA : ‖A‖ ≤ a) (hF : ‖F‖ ≤ a) (hD : ‖D‖ ≤ a)
    (hU : ‖U‖ ≤ 1) (hK : ‖K‖ ≤ 1) (hV : ‖V‖ ≤ 2 * a) (hT : ‖T‖ ≤ 2 * a)
    (hSum : A + D = ringCommutator U V + ringCommutator K T) :
    ∃ B C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ,
      identityCorner A F D = ringCommutator B C ∧
        ‖B‖ * ‖C‖ ≤ identityCornerNormBudget a := by
  letI : NormedAlgebra ℝ (Matrix ι ι ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _
  have ha : 0 ≤ a := (norm_nonneg A).trans hA
  let b := ringCommutator U V - A
  let c := -D
  let d := A - U
  let e := riccatiConstant A F U K V T
  let lam := identityCornerScale a
  have hLam : 0 < lam := identityCornerScale_pos a ha
  have hb : ‖b‖ ≤ 5 * a := by
    have h := norm_firstDefect_le A U V a (2 * a) hA hU hV
    change ‖ringCommutator U V - A‖ ≤ 5 * a
    linarith
  have hc : ‖c‖ ≤ a := by simpa only [c, norm_neg] using hD
  have hd : ‖d‖ ≤ a + 1 := (norm_sub_le A U).trans (add_le_add hA hU)
  have he : ‖e‖ ≤ 14 * a + 1 := by
    have h := norm_riccatiConstant_le A F U K V T a (2 * a) hA hF hU hK hV hT
    change ‖riccatiConstant A F U K V T‖ ≤ 14 * a + 1
    linarith
  have hb' : ‖b‖ + 1 ≤ 5 * a + 1 := by linarith
  have hcd : ‖c‖ + ‖d‖ ≤ 2 * a + 1 := by linarith
  have hPoly : (‖b‖ + 1) ^ 2 + (‖c‖ + ‖d‖) * (‖b‖ + 1) + ‖e‖ ≤
      (5 * a + 1) ^ 2 + (2 * a + 1) * (5 * a + 1) + (14 * a + 1) := by
    gcongr
  have hLip : 2 * (‖b‖ + 1) + ‖c‖ + ‖d‖ ≤ 2 * (5 * a + 1) + 2 * a + 1 := by
    linarith
  have hSize : 2 * ((‖b‖ + 1) ^ 2 + (‖c‖ + ‖d‖) * (‖b‖ + 1) + ‖e‖) ≤ lam := by
    apply (mul_le_mul_of_nonneg_left hPoly (by norm_num)).trans
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  have hContract : 2 * (2 * (‖b‖ + 1) + ‖c‖ + ‖d‖) ≤ lam := by
    apply (mul_le_mul_of_nonneg_left hLip (by norm_num)).trans
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  obtain ⟨Q, hQ, hFixed⟩ :=
    exists_riccati_fixedPoint_large_scale b c d e lam hLam hSize hContract
  have hq : ‖Q‖ ≤ 5 * a + 1 := by
    have h := norm_le_norm_sub_add Q b
    linarith
  refine ⟨lowerShear Q * companionFirst (lam • 1 + U) K * lowerShearInverse Q,
    lowerShear Q * companionSecond A (lam • 1 + U) K V T Q * lowerShearInverse Q, ?_, ?_⟩
  · apply identityCorner_eq_commutator_of_fixedPoint lam (ne_of_gt hLam) A F D U K V T Q hSum
    simpa only [b, c, d, e, quadratic] using hFixed
  · exact norm_identityCorner_factors_le lam hLam.le A U K V T Q (2 * a) (5 * a + 1)
      hU hK hV hT hQ hq

end MatrixBounds

end NoEpsilon
