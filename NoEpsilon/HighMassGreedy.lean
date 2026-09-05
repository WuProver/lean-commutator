import NoEpsilon.HighMassSubspace
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Greedy neutral subspaces in the high-mass branch

At step `k` we remove the span of four families: the previously selected vectors,
their images, their adjoint images, and their images under `T* T`. Thus the next
selection costs at most `4 k` dimensions and makes the image vectors orthogonal.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A neutral orthonormal family whose images are orthogonal and uniformly large. -/
def IsLargeNeutralFrame (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (r : ℝ) {k : ℕ} (p : Fin k → EuclideanSpace ℂ ι) : Prop :=
  Orthonormal ℂ p ∧ (∀ i j, inner ℂ (p i) (T (p j)) = 0) ∧
    (∀ i j, i ≠ j → inner ℂ (T (p i)) (T (p j)) = 0) ∧
    ∀ i, r ≤ ‖T (p i)‖

/-- Four constraints per old vector make both the new vector and its image orthogonal
to the appropriate old families. -/
def frameConstraintFamily (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    {k : ℕ} (p : Fin k → EuclideanSpace ℂ ι) : Fin 4 × Fin k → EuclideanSpace ℂ ι :=
  fun a ↦ ![p a.2, T (p a.2), T.adjoint (p a.2), T.adjoint (T (p a.2))] a.1

set_option backward.isDefEq.respectTransparency false in
/-- One greedy step uses the already proved intrinsic high-mass selection theorem. -/
theorem highMass_frame_extension [Nonempty ι]
    (A : Matrix ι ι ℂ) (t : ℝ) (ht : 0 < t) (hNorm : ‖A‖ ≤ 1)
    (hTrace : Matrix.trace A = 0) (hMass : HasHighTraceMass A t)
    {k : ℕ} (p : Fin k → EuclideanSpace ℂ ι)
    (hp : IsLargeNeutralFrame (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (t / 4) p)
    (hk : (4 : ℝ) * k ≤ t * Fintype.card ι / 4) :
    ∃ q : Fin (k + 1) → EuclideanSpace ℂ ι,
      IsLargeNeutralFrame (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (t / 4) q := by
  classical
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  let g := frameConstraintFamily T p
  let S : Submodule ℂ (EuclideanSpace ℂ ι) := Submodule.span ℂ (Set.range g)
  have hSdim : Module.finrank ℂ S ≤ 4 * k := by
    have h := finrank_range_le_card (R := ℂ) g
    simpa only [Fintype.card_prod, Fintype.card_fin] using h
  have hOrthDim := S.finrank_add_finrank_orthogonal
  have hCodim : (Fintype.card ι : ℝ) - Module.finrank ℂ Sᗮ ≤
      t * Fintype.card ι / 4 := by
    have hOrthDimR : (Module.finrank ℂ S : ℝ) + Module.finrank ℂ Sᗮ = Fintype.card ι := by
      exact_mod_cast (by simpa only [finrank_euclideanSpace] using hOrthDim)
    have hSdimR : (Module.finrank ℂ S : ℝ) ≤ 4 * k := by exact_mod_cast hSdim
    linarith
  obtain ⟨v, hvW, hvUnit, hvNeutral, hvLarge⟩ :=
    highMass_subspace_has_large_neutral A Sᗮ t ht hNorm hTrace hMass hCodim
  have hOrth (d : Fin 4) (i : Fin k) : inner ℂ v (g (d, i)) = 0 :=
    S.inner_left_of_mem_orthogonal (Submodule.subset_span ⟨(d, i), rfl⟩) hvW
  have hvP (i : Fin k) : inner ℂ v (p i) = 0 := hOrth 0 i
  have hvAP (i : Fin k) : inner ℂ v (T (p i)) = 0 := hOrth 1 i
  have hAvP (i : Fin k) : inner ℂ (T v) (p i) = 0 := by
    have h : inner ℂ v (T.adjoint (p i)) = 0 := hOrth 2 i
    rwa [ContinuousLinearMap.adjoint_inner_right] at h
  have hAvAP (i : Fin k) : inner ℂ (T v) (T (p i)) = 0 := by
    have h : inner ℂ v (T.adjoint (T (p i))) = 0 := hOrth 3 i
    rwa [ContinuousLinearMap.adjoint_inner_right] at h
  refine ⟨Fin.cons v p, ?_, ?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero => simp [inner_self_eq_norm_sq_to_K, hvUnit]
        | succ j => simpa using hvP j
    | succ i =>
        induction j using Fin.cases with
        | zero => simpa using (inner_eq_zero_symm.mp (hvP i))
        | succ j => simpa using (orthonormal_iff_ite.mp hp.1 i j)
  · intro i j
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero => exact hvNeutral
        | succ j => exact hvAP j
    | succ i =>
        induction j using Fin.cases with
        | zero => exact inner_eq_zero_symm.mp (hAvP i)
        | succ j => exact hp.2.1 i j
  · intro i j hij
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact hAvAP j
    | succ i =>
        induction j using Fin.cases with
        | zero => exact inner_eq_zero_symm.mp (hAvAP i)
        | succ j => exact hp.2.2.1 i j (fun h ↦ hij (congrArg Fin.succ h))
  · intro i
    induction i using Fin.cases with
    | zero => exact hvLarge
    | succ i => exact hp.2.2.2 i

set_option backward.isDefEq.respectTransparency false in
/-- The greedy construction reaches every size up to `ceil(t n / 16)`. -/
theorem highMass_exists_neutral_frame_of_le [Nonempty ι]
    (A : Matrix ι ι ℂ) (t : ℝ) (ht : 0 < t) (hNorm : ‖A‖ ≤ 1)
    (hTrace : Matrix.trace A = 0) (hMass : HasHighTraceMass A t)
    (k : ℕ) (hk : k ≤ ⌈t * Fintype.card ι / 16⌉₊) :
    ∃ p : Fin k → EuclideanSpace ℂ ι,
      IsLargeNeutralFrame (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (t / 4) p := by
  induction k with
  | zero =>
      refine ⟨Fin.elim0, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · intro i
        exact i.elim0
      · intro i
        exact i.elim0
      · intro i
        exact i.elim0
      · intro i
        exact i.elim0
      · intro i
        exact i.elim0
  | succ k ih =>
      obtain ⟨p, hp⟩ := ih (Nat.le_trans (Nat.le_succ k) hk)
      have hLt : (k : ℝ) < t * Fintype.card ι / 16 :=
        Nat.lt_ceil.mp (Nat.lt_of_succ_le hk)
      exact highMass_frame_extension A t ht hNorm hTrace hMass p hp (by linarith)

set_option backward.isDefEq.respectTransparency false in
/-- High mass produces a proportionate neutral subspace with pairwise orthogonal large images. -/
theorem highMass_exists_neutral_frame [Nonempty ι]
    (A : Matrix ι ι ℂ) (t : ℝ) (ht : 0 < t) (hNorm : ‖A‖ ≤ 1)
    (hTrace : Matrix.trace A = 0) (hMass : HasHighTraceMass A t) :
    ∃ p : Fin ⌈t * Fintype.card ι / 16⌉₊ → EuclideanSpace ℂ ι,
      IsLargeNeutralFrame (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (t / 4) p :=
  highMass_exists_neutral_frame_of_le A t ht hNorm hTrace hMass _ le_rfl

end NoEpsilon
