import CommutatorTheorem.NoEpsilon.LowMassPaving
import CommutatorTheorem.NoEpsilon.LowMassTransversals
import CommutatorTheorem.NoEpsilon.OrthonormalCompletion

/-!
# The low-mass orthonormal paving basis

This file joins spectral grouping, the three-Hermitian basis theorem, exact transversals,
and the square-root covariance estimate. Paired MSS selection remains an explicit analytic
premise until it is supplied by the independently formalized MSS theorem.
-/

open scoped BigOperators Matrix ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace NoEpsilon.LowMassPaving

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rearrange the complete groups so that each first coordinate labels one transversal. -/
def transversalColumns {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ)
    (σ : Fin k → Equiv.Perm (Fin R)) : Matrix ι (Fin R × Fin k) ℂ :=
  fun i p ↦ V p.2 i (σ p.2 p.1)

theorem transversalColumns_isometry {k R : ℕ} (V : Fin k → Matrix ι (Fin R) ℂ)
    (σ : Fin k → Equiv.Perm (Fin R))
    (hV : ∀ j l, (V j)ᴴ * V l = if j = l then 1 else 0) :
    (transversalColumns V σ)ᴴ * transversalColumns V σ = 1 := by
  ext ⟨a, j⟩ ⟨b, l⟩
  change ((V j)ᴴ * V l) (σ j a) (σ l b) = (1 : Matrix _ _ ℂ) (a, j) (b, l)
  rw [hV]
  by_cases hjl : j = l
  · subst l
    simp [Matrix.one_apply, (σ j).injective.eq_iff]
  · simp [hjl, Matrix.one_apply, Prod.mk.injEq]

/-- A square-cardinality rectangular isometry specifies an orthonormal basis on its own index. -/
theorem exists_basis_of_isometry {κ : Type*} [Fintype κ] [DecidableEq κ]
    (W : Matrix ι κ ℂ) (hW : Wᴴ * W = 1) (hcard : Fintype.card ι = Fintype.card κ) :
    ∃ b : OrthonormalBasis κ ℂ (EuclideanSpace ℂ ι), familyMatrix b = W := by
  let p : κ → EuclideanSpace ℂ ι := fun j ↦ WithLp.toLp 2 (fun i ↦ W i j)
  have hp : Orthonormal ℂ p := orthonormal_columns_of_isometry W hW
  have hpu : Orthonormal ℂ ((Set.univ : Set κ).restrict p) :=
    hp.comp _ Subtype.val_injective
  obtain ⟨b, hb⟩ := hpu.exists_orthonormalBasis_extension_of_card_eq
    (by simpa only [finrank_euclideanSpace] using hcard)
  refine ⟨b, ?_⟩
  ext i j
  change b j i = W i j
  rw [hb j (Set.mem_univ j)]

theorem mul_concatenateGroups {k R : ℕ} (S : Matrix ι ι ℂ)
    (V : Fin k → Matrix ι (Fin R) ℂ) :
    S * concatenateGroups V = concatenateGroups (fun j ↦ S * V j) := rfl

theorem prepared_square_root_frame {k R : ℕ} (E S : Matrix ι ι ℂ)
    (V : Fin k → Matrix ι (Fin R) ℂ) (hS : Sᴴ = S) (hSS : S * S = E)
    (hV : (∑ j, V j * (V j)ᴴ) = 1) :
    (∑ j, ∑ a, MSSSelection.outer (fun i ↦ (S * V j) i a)) = E ∧
      ∀ j a, MSSSelection.energy (fun i ↦ (S * V j) i a) =
        (rayleighValue E (fun i ↦ V j i a)).re := by
  have h := square_root_frame E S (concatenateGroups V) hS hSS
    ((concatenateGroups_range V).trans hV)
  constructor
  · simpa only [mul_concatenateGroups, concatenateGroups, Fintype.sum_prod_type] using h.1
  · intro j a
    simpa only [mul_concatenateGroups, concatenateGroups] using h.2 (j, a)

theorem positive_contraction_norm_le (E : Matrix ι ι ℂ)
    (hE : E.PosSemidef) (hE₁ : E ≤ 1) : ‖E‖ ≤ 1 := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := {}
  exact (CStarAlgebra.norm_le_norm_of_nonneg_of_le hE.nonneg hE₁).trans
    (coordinate_identity_norm_le (α := ι))

/-- Leaf matrices before the final basis packaging. -/
theorem exists_paving_columns {k h : ℕ} (hk : 0 < k)
    (selection : PairedHalfSelection (Fin (k * 2 ^ h)))
    (H G E : Matrix (Fin (k * 2 ^ h)) (Fin (k * 2 ^ h)) ℂ)
    (hH : H.IsHermitian) (hHt : Matrix.trace H = 0)
    (hG : G.IsHermitian) (hGn : ‖G‖ ≤ 1) (hGt : Matrix.trace G = 0)
    (hE : E.PosSemidef) (hE₁ : E ≤ 1) (hEt : (Matrix.trace E).re ≤ 2 * k)
    (hlower : -E ≤ H) (hupper : H ≤ E) :
    ∃ (V : Fin k → Matrix (Fin (k * 2 ^ h)) (Fin (2 ^ h)) ℂ)
      (σ : Fin k → Equiv.Perm (Fin (2 ^ h))),
      (∀ j l, (V j)ᴴ * V l = if j = l then 1 else 0) ∧
      ∀ a, let W := selectedColumns V (fun j ↦ σ j a)
        Matrix.trace (Wᴴ * (H + Complex.I • G) * W) = 0 ∧
        ‖Wᴴ * (H + Complex.I • G) * W‖ ≤ 319 / (2 : ℝ) ^ h := by
  obtain ⟨V, d, g, hV, hVsum, hcross, hd, hg, hdiag⟩ :=
    exists_prepared_groups hk (by positivity) H G E hH hHt hG hGn hGt hE hE₁ hEt
  obtain ⟨S, hS, hSS⟩ := exists_hermitian_square_root E hE
  obtain ⟨hframe, henergy⟩ := prepared_square_root_frame E S V hS hSS hVsum
  let f : Fin k → Fin (2 ^ h) → Fin (k * 2 ^ h) → ℂ :=
    fun j a i ↦ (S * V j) i a
  have hf : ∀ j a, MSSSelection.energy (f j a) ≤ 12 / (2 : ℝ) ^ h := by
    intro j a
    rw [show f j a = (fun i ↦ (S * V j) i a) from rfl, henergy]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (hdiag j).2 a |>.2.2
  have hf₁ : ‖∑ j, ∑ a, MSSSelection.outer (f j a)‖ ≤ 1 := by
    change ‖∑ j, ∑ a, MSSSelection.outer (fun i ↦ (S * V j) i a)‖ ≤ 1
    rw [hframe]
    exact positive_contraction_norm_le E hE hE₁
  obtain ⟨σ, hσ⟩ := exists_transversals selection k h 12 (by norm_num) f hf hf₁
  refine ⟨V, σ, hV, ?_⟩
  intro a
  let W := selectedColumns V (fun j ↦ σ j a)
  have htraceH : Matrix.trace (Wᴴ * H * W) = 0 :=
    (selectedColumns_trace V _ H d (fun j b ↦ ((hdiag j).2 b).1)).trans hd
  have htraceG : Matrix.trace (Wᴴ * G * W) = 0 :=
    (selectedColumns_trace V _ G g (fun j b ↦ ((hdiag j).2 b).2.1)).trans hg
  have hnormG : ‖Wᴴ * G * W‖ ≤ 4 / (2 : ℝ) ^ h := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      selectedColumns_norm_le V (fun j ↦ σ j a) G g (4 / (2 ^ h : ℕ))
        (by positivity) hcross (fun j b ↦ ((hdiag j).2 b).2.1) (fun j ↦ (hdiag j).1)
  have hnormE : ‖Wᴴ * E * W‖ ≤ transversalConstant 12 / (2 : ℝ) ^ h := by
    rw [norm_compression_eq_frame E S W (by rw [hS, hSS])]
    exact hσ a
  have hnormH : ‖Wᴴ * H * W‖ ≤ transversalConstant 12 / (2 : ℝ) ^ h :=
    (norm_compression_le_of_order_interval H E hH hE hlower hupper W).trans hnormE
  have hsplit : Wᴴ * (H + Complex.I • G) * W = Wᴴ * H * W + Complex.I • (Wᴴ * G * W) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · rw [hsplit, Matrix.trace_add, Matrix.trace_smul, htraceH, htraceG, smul_zero, add_zero]
  · rw [hsplit]
    calc
      _ ≤ ‖Wᴴ * H * W‖ + ‖Complex.I • (Wᴴ * G * W)‖ := norm_add_le _ _
      _ = ‖Wᴴ * H * W‖ + ‖Wᴴ * G * W‖ := by rw [norm_smul, Complex.norm_I, one_mul]
      _ ≤ transversalConstant 12 / (2 : ℝ) ^ h + 4 / (2 : ℝ) ^ h :=
        add_le_add hnormH hnormG
      _ ≤ 319 / (2 : ℝ) ^ h := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right transversalConstant_twelve_add_four_lt.le
          (by positivity)

/-- The complete low-mass paving basis, with genuine Euclidean operator norm and exact trace
zero on every leaf. The only remaining analytic premise is paired MSS selection. -/
theorem exists_paving_basis {k h : ℕ} (hk : 0 < k)
    (selection : PairedHalfSelection (Fin (k * 2 ^ h)))
    (H G E : Matrix (Fin (k * 2 ^ h)) (Fin (k * 2 ^ h)) ℂ)
    (hH : H.IsHermitian) (hHt : Matrix.trace H = 0)
    (hG : G.IsHermitian) (hGn : ‖G‖ ≤ 1) (hGt : Matrix.trace G = 0)
    (hE : E.PosSemidef) (hE₁ : E ≤ 1) (hEt : (Matrix.trace E).re ≤ 2 * k)
    (hlower : -E ≤ H) (hupper : H ≤ E) :
    ∃ b : OrthonormalBasis (Fin (2 ^ h) × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * 2 ^ h))),
      ∀ a, let W := familyMatrix (fun j ↦ b (a, j))
        Matrix.trace (Wᴴ * (H + Complex.I • G) * W) = 0 ∧
        ‖Wᴴ * (H + Complex.I • G) * W‖ ≤ 319 / (2 : ℝ) ^ h := by
  obtain ⟨V, σ, hV, hleaf⟩ := exists_paving_columns hk selection H G E
    hH hHt hG hGn hGt hE hE₁ hEt hlower hupper
  obtain ⟨b, hb⟩ := exists_basis_of_isometry (transversalColumns V σ)
    (transversalColumns_isometry V σ hV)
    (by simp only [Fintype.card_fin, Fintype.card_prod, Nat.mul_comm])
  refine ⟨b, ?_⟩
  intro a
  have hW : familyMatrix (fun j ↦ b (a, j)) = selectedColumns V (fun j ↦ σ j a) := by
    ext i j
    exact congrArg (fun M ↦ M i (a, j)) hb
  simpa only [hW] using hleaf a

end NoEpsilon.LowMassPaving
