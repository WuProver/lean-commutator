import CommutatorTheorem.NoEpsilon.HighMassCoordinates
import CommutatorTheorem.NoEpsilon.UnitaryCoordinates
import CommutatorTheorem.NoEpsilon.DiagonalAbsorption

/-!
# A dimension-independent commutator bound for high trace mass

The high-mass geometry, greedy frame, exact coordinate completion, bounded partition,
diagonal normalization, finite absorption, and unitary pullback are connected here.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator

/-- An explicit dimension-independent bound for normalized matrices in the high-mass branch. -/
def highMassNormBudget (t : ℝ) : ℝ :=
  (t / 4)⁻¹ ^ 2 * Absorption.absorptionBudget (t / 4)⁻¹ ⌈16 / t⌉₊

/-- The bridge rank times the fixed number of outside slots covers the original dimension. -/
theorem highMass_rank_times_slots (n : ℕ) (t : ℝ) (ht : 0 < t) :
    n ≤ ⌈16 / t⌉₊ * ⌈t * n / 16⌉₊ := by
  let L := ⌈16 / t⌉₊
  let r := ⌈t * n / 16⌉₊
  have hr : t * n ≤ 16 * (r : ℝ) := by
    have h := Nat.le_ceil (t * n / 16)
    change t * n / 16 ≤ (r : ℝ) at h
    linarith
  have hL : 16 ≤ t * (L : ℝ) := by
    have h := (div_le_iff₀ ht).mp (Nat.le_ceil (16 / t))
    change 16 ≤ (L : ℝ) * t at h
    nlinarith
  have hProduct : t * (n : ℝ) ≤ t * ((L : ℝ) * r) := by
    calc
      _ ≤ 16 * (r : ℝ) := hr
      _ ≤ (t * (L : ℝ)) * r := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg r)
      _ = t * ((L : ℝ) * r) := by ring
  have h := (mul_le_mul_iff_right₀ ht).mp hProduct
  exact_mod_cast h

set_option backward.isDefEq.respectTransparency false in
/-- The complete high-mass branch: a normalized trace-zero matrix has a single commutator
representation with an explicit bound depending only on its trace-mass parameter. -/
theorem highMass_bounded_commutator {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (t : ℝ) (ht : 0 < t) (hNorm : ‖A‖ ≤ 1)
    (hTrace : Matrix.trace A = 0) (hMass : HasHighTraceMass A t) :
    ∃ B C : Matrix ι ι ℂ, A = B * C - C * B ∧ ‖B‖ * ‖C‖ ≤ highMassNormBudget t := by
  classical
  let r := ⌈t * Fintype.card ι / 16⌉₊
  let L := ⌈16 / t⌉₊
  have hr : 0 < r := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨P, Q, δ, hP, hQ, hPQ, _, _, hBridge, hδ⟩ :=
    highMass_exists_diagonal_bridge A t ht hNorm hTrace hMass
  have hCard : Fintype.card ι ≤ L * r := highMass_rank_times_slots _ t ht
  obtain ⟨m, f, b, _, hSize, hFirst, hSecond⟩ :=
    orthogonal_pair_partitioned_basis (r := r) (L := L) P Q hP hQ hPQ hCard
  let d := fun i : Fin L ↦ {x : Fin m // f x = i}
  let U := familyMatrix b
  let X : Matrix (Absorption.Ambient r d) (Absorption.Ambient r d) ℂ := Uᴴ * A * U
  have hXNorm : ‖X‖ ≤ 1 :=
    (isometry_compression_norm_le U (basisMatrix_unitary b).1 A).trans hNorm
  have hXTrace : Matrix.trace X = 0 := (basis_compression_trace b A).trans hTrace
  have hXBridge : (BlockAssembly.block X none none).toBlocks₁₂ =
      Matrix.diagonal (fun i ↦ (δ i : ℂ)) := by
    ext i j
    change (Uᴴ * A * U) ⟨none, Sum.inl i⟩ ⟨none, Sum.inr j⟩ = _
    rw [familyMatrix_compression_entry, hFirst i, hSecond j]
    have hEntry := familyMatrix_compression_entry A
      (fun i ↦ (WithLp.toLp 2 (fun j ↦ Q j i) : EuclideanSpace ℂ ι))
      (fun i ↦ (WithLp.toLp 2 (fun j ↦ P j i) : EuclideanSpace ℂ ι)) i j
    change (Qᴴ * A * P) i j = _ at hEntry
    rw [← hEntry, hBridge]
  have hρ : 0 < t / 4 := by linarith
  have hρ1 : t / 4 ≤ 1 := (hδ ⟨0, hr⟩).1.trans (hδ ⟨0, hr⟩).2
  have hBound := Absorption.diagonal_corner_absorption X (t / 4) hρ hρ1 δ hδ
    hXNorm hXTrace hXBridge hSize
  apply basis_compression_commutator_pullback b A (highMassNormBudget t)
  simpa only [Fintype.card_fin, highMassNormBudget] using hBound

end NoEpsilon
