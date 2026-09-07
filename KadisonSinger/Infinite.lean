import KadisonSinger.FinitePaving
import Mathlib.Combinatorics.Compactness
import CommutatorTheorem.NoEpsilon.BlockCompression

/-!
# Compactness for coordinate paving

Rado selection glues finite pavings into one coloring of an arbitrary index set.
Every finite principal section of every resulting color compression obeys the
same norm bound. This is the compactness step from finite matrices to kernels.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace KadisonSinger

open PavingSeparation

/-- The finite principal section of a possibly infinite matrix kernel. -/
def finiteSection {α : Type*} (A : Matrix α α ℂ) (s : Finset α) : Matrix s s ℂ :=
  A.submatrix Subtype.val Subtype.val

/-- A single global coloring is obtained from uniformly bounded finite pavings. -/
theorem kernel_paving_of_finite_sections {α : Type*} [DecidableEq α] (A : Matrix α α ℂ)
    (r : ℕ) (b : ℝ)
    (hlocal : ∀ s : Finset α, ∃ c : s → Fin r, ∀ j,
      ‖compression (colorClass c j) (finiteSection A s)‖ ≤ b) :
    ∃ c : α → Fin r, ∀ s : Finset α, ∀ j,
      ‖compression (colorClass (fun i : s ↦ c i) j) (finiteSection A s)‖ ≤ b := by
  classical
  choose g hg using hlocal
  obtain ⟨c, hc⟩ := Finset.rado_selection_subtype (β := fun _ : α ↦ Fin r) g
  refine ⟨c, fun s j ↦ ?_⟩
  obtain ⟨t, hst, hagree⟩ := hc s
  let e : s → t := Set.inclusion hst
  have he : Function.Injective e := Set.inclusion_injective hst
  have hcomp :
      (compression (colorClass (g t) j) (finiteSection A t)).submatrix e e =
        compression (colorClass (fun i : s ↦ c i) j) (finiteSection A s) := by
    ext i k
    simp only [Matrix.submatrix_apply, compression_apply, mem_colorClass]
    rw [hagree i, hagree k]
    rfl
  rw [← hcomp]
  exact (NoEpsilon.submatrix_operator_norm_le _ e e he he).trans (hg t j)

/-- Uniform coordinate paving of a Hermitian zero-diagonal kernel whose finite
principal sections have a common norm bound. The number of colors depends only on `ε`. -/
theorem hermitian_kernel_paving (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ ∀ (α : Type*) [DecidableEq α]
      (A : Matrix α α ℂ), A.IsHermitian → (∀ i, A i i = 0) →
      ∀ C : ℝ, (∀ s : Finset α, ‖finiteSection A s‖ ≤ C) →
      ∃ c : α → Fin r, ∀ s : Finset α, ∀ j,
        ‖compression (colorClass (fun i : s ↦ c i) j) (finiteSection A s)‖ ≤ ε * C := by
  obtain ⟨r, hr, hp⟩ := hermitian_paving ε hε
  refine ⟨r, hr, fun α _ A hA hdiag C hC ↦ ?_⟩
  apply kernel_paving_of_finite_sections A r (ε * C)
  intro s
  have hAs : (finiteSection A s).IsHermitian := hA.submatrix _
  obtain ⟨c, hc⟩ := hp s (finiteSection A s) hAs (fun i ↦ hdiag i)
  refine ⟨c, fun j ↦ ?_⟩
  exact (hc j).trans (mul_le_mul_of_nonneg_left (hC s) hε.le)

end KadisonSinger
