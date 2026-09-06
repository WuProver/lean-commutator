import CommutatorTheorem.NoEpsilon.FiniteAbsorption
import CommutatorTheorem.NoEpsilon.BlockAssembly
import CommutatorTheorem.NoEpsilon.CoreTheorem

/-!
# A bounded identity corner absorbs finitely many smaller outside blocks

The coordinate space is the dependent disjoint union of one two-by-two core and an
arbitrary finite family of outside blocks. No padding or enlargement is performed.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace NoEpsilon.Absorption

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (r : ℕ) (d : ι → Type) [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

/-- The core is indexed by none; the outside blocks are indexed by some i. -/
def blockShape : Option ι → Type
  | none => Fin r ⊕ Fin r
  | some i => d i

instance blockShapeFintype (i : Option ι) : Fintype (blockShape r d i) := by
  cases i <;> dsimp [blockShape] <;> infer_instance

instance blockShapeDecidableEq (i : Option ι) : DecidableEq (blockShape r d i) := by
  cases i <;> dsimp [blockShape] <;> infer_instance

abbrev Ambient := Sigma (blockShape r d)

def firstIndex (j : Fin r) : Ambient r d := ⟨none, Sum.inl j⟩

def secondIndex (j : Fin r) : Ambient r d := ⟨none, Sum.inr j⟩

def outsideIndex (i : ι) (j : d i) : Ambient r d := ⟨some i, j⟩

theorem firstIndex_injective : Function.Injective (firstIndex r d) := by
  intro x y h
  exact Sum.inl_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

theorem secondIndex_injective : Function.Injective (secondIndex r d) := by
  intro x y h
  exact Sum.inr_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

theorem outsideIndex_injective (i : ι) : Function.Injective (outsideIndex r d i) := by
  intro x y h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

variable {r d}

theorem coordinateInclusion_orthogonal {α β γ : Type*}
    [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → γ) (g : β → γ) (h : ∀ a b, f a ≠ g b) :
    (coordinateInclusion f)ᴴ * coordinateInclusion g = 0 := by
  ext a b
  simpa [Matrix.mul_apply, coordinateInclusion, Matrix.conjTranspose_apply]
    using (h a b).symm

/-- The trace of the full matrix is the sum of the traces of its diagonal blocks. -/
theorem trace_eq_sum_blocks (A : Matrix (Ambient r d) (Ambient r d) ℂ) :
    trace A = trace (BlockAssembly.block A none none) +
      ∑ i, trace (BlockAssembly.block A (some i) (some i)) := by
  simp only [Matrix.trace, Matrix.diag, BlockAssembly.block, Matrix.submatrix_apply]
  rw [Fintype.sum_sigma, Fintype.sum_option]

/-- The explicit norm budget depends only on the initial norm and the number of
outside blocks, and is independent of their individual dimensions. -/
noncomputable def absorptionBudget (a : ℝ) (m : ℕ) : ℝ :=
  let b := (stepBudget^[m]) a
  (b / a) ^ 2 *
    (4 * (m + 1) * identityCornerNormBudget b + 2 * (m + 1) ^ 2 * b)

/-- Finite absorption followed by the bounded core theorem and actual Sylvester assembly. -/
theorem identity_corner_absorption (A : Matrix (Ambient r d) (Ambient r d) ℂ)
    (a : ℝ) (ha : 0 < a) (hA : ‖A‖ ≤ a) (hTrace : trace A = 0)
    (hbridge : (BlockAssembly.block A none none).toBlocks₁₂ = 1)
    (hsize : ∀ i, Fintype.card (d i) ≤ r) :
    ∃ B C : Matrix (Ambient r d) (Ambient r d) ℂ,
      A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ absorptionBudget a (Fintype.card ι) := by
  classical
  let P := coordinateInclusion (firstIndex r d)
  let Q := coordinateInclusion (secondIndex r d)
  let V := fun i ↦ coordinateInclusion (outsideIndex r d i)
  have hemb (i : ι) : Nonempty (d i ↪ Fin r) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hsize i)
  let e := fun i ↦ Classical.choice (hemb i)
  let J := fun i ↦ coordinateInclusion (e i)
  have hPP : Pᴴ * P = 1 :=
    coordinateInclusion_isometry _ (firstIndex_injective r d)
  have hQQ : Qᴴ * Q = 1 :=
    coordinateInclusion_isometry _ (secondIndex_injective r d)
  have hVV (i : ι) : (V i)ᴴ * V i = 1 :=
    coordinateInclusion_isometry _ (outsideIndex_injective r d i)
  have hJJ (i : ι) : (J i)ᴴ * J i = 1 :=
    coordinateInclusion_isometry _ (e i).injective
  have hPQ : Pᴴ * Q = 0 := by
    apply coordinateInclusion_orthogonal
    intro x y
    simp [firstIndex, secondIndex]
  have hPV (i : ι) : Pᴴ * V i = 0 := by
    apply coordinateInclusion_orthogonal
    intro x y
    simp [firstIndex, outsideIndex]
  have hVQ (i : ι) : (V i)ᴴ * Q = 0 := by
    apply coordinateInclusion_orthogonal
    intro x y
    simp [outsideIndex, secondIndex]
  have hOrth (i j : ι) (hij : i ≠ j) : (V i)ᴴ * V j = 0 := by
    apply coordinateInclusion_orthogonal
    intro x y
    simp [outsideIndex, hij]
  have hPbridge : Pᴴ * A * Q = 1 := by
    rw [← submatrix_eq_coordinate_compression]
    exact hbridge
  obtain ⟨S, T, hST, hTS, hbridge', hzero, _, htr, hnorm, hcondition⟩ :=
    eliminate_finset d P Q V J hPP hQQ hPQ hVV hPV hVQ hOrth hJJ
      Finset.univ A a ha.le hPbridge hA
  let M := T * A * S
  let b := (stepBudget^[Fintype.card ι]) a
  have hnormM : ‖M‖ ≤ b := by simpa using hnorm
  have hb : 0 ≤ b := (norm_nonneg M).trans hnormM
  have hzero' (i : ι) : BlockAssembly.block M (some i) (some i) = 0 := by
    have hi := hzero i (Finset.mem_univ i)
    rw [← submatrix_eq_coordinate_compression] at hi
    exact hi
  have htraceM : trace M = 0 := htr.trans hTrace
  have htraceCore : trace (BlockAssembly.block M none none) = 0 := by
    rw [trace_eq_sum_blocks] at htraceM
    simpa only [hzero', Matrix.trace_zero, Finset.sum_const_zero, add_zero] using htraceM
  let core := BlockAssembly.block M none none
  have hcorebridge : core.toBlocks₁₂ = 1 := by
    rw [← submatrix_eq_coordinate_compression] at hbridge'
    exact hbridge'
  have hcore : core = identityCorner core.toBlocks₁₁ core.toBlocks₂₁ core.toBlocks₂₂ := by
    rw [identityCorner, ← hcorebridge, Matrix.fromBlocks_toBlocks]
  have hcoreNorm : ‖core‖ ≤ b :=
    (submatrix_operator_norm_le M (Sigma.mk none) (Sigma.mk none)
      (fun _ _ h ↦ eq_of_heq (Sigma.mk.inj_iff.mp h).2)
      (fun _ _ h ↦ eq_of_heq (Sigma.mk.inj_iff.mp h).2)).trans hnormM
  obtain ⟨U, W, hcoreComm, hcoreCost⟩ := identityCorner_bounded_from_whole_norm r
    core.toBlocks₁₁ core.toBlocks₂₁ core.toBlocks₂₂ b
      (by rwa [← hcore]) (by rwa [← hcore])
  have hp : 0 ≤ identityCornerNormBudget b :=
    (mul_nonneg (norm_nonneg U) (norm_nonneg W)).trans hcoreCost
  have hdiag (i : Option ι) :
      ∃ U W : Matrix (blockShape r d i) (blockShape r d i) ℂ,
        BlockAssembly.block M i i = U * W - W * U ∧
          ‖U‖ * ‖W‖ ≤ identityCornerNormBudget b := by
    cases i with
    | none => exact ⟨U, W, hcore.trans hcoreComm, hcoreCost⟩
    | some i => exact ⟨0, 0, by simp [hzero'], by simpa using hp⟩
  obtain ⟨B, C, hcomm, hcost⟩ := BlockAssembly.assemble_any M
    (identityCornerNormBudget b) hp hdiag
  have hback : S * M * T = A := by
    dsimp [M]
    calc
      _ = (S * T) * A * (S * T) := by noncomm_ring
      _ = A := by rw [hST]; simp
  have hcond : ‖S‖ * ‖T‖ ≤ b / a := by
    apply (le_div_iff₀ ha).mpr
    simpa [mul_comm] using hcondition
  refine ⟨S * B * T, S * C * T, ?_, ?_⟩
  · change A = ringCommutator (S * B * T) (S * C * T)
    rw [conjugation_commutator S T B C hTS, ringCommutator, ← hcomm, hback]
  · calc
      _ ≤ (‖S‖ * ‖T‖) ^ 2 * (‖B‖ * ‖C‖) := norm_conjugation_product_le S T B C
      _ ≤ (b / a) ^ 2 *
          (4 * Fintype.card (Option ι) * identityCornerNormBudget b +
            2 * (Fintype.card (Option ι) : ℝ) ^ 2 * ‖M‖) := by gcongr
      _ ≤ (b / a) ^ 2 *
          (4 * Fintype.card (Option ι) * identityCornerNormBudget b +
            2 * (Fintype.card (Option ι) : ℝ) ^ 2 * b) := by gcongr
      _ = absorptionBudget a (Fintype.card ι) := by
        simp [absorptionBudget, b, Fintype.card_option]

end NoEpsilon.Absorption
