import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Uniform scalar centers for block assembly

A centered integer grid provides as many separated complex scalars as needed by the
fixed-size block assembly. All norm and separation bounds are independent of matrix sizes.
-/

namespace NoEpsilon

/-- The centered complex grid with q coordinates in each direction. -/
noncomputable def gridCenter (q : ℕ) (x : Fin q × Fin q) : ℂ :=
  ⟨(x.1.val : ℝ) - ((q : ℝ) - 1) / 2,
    (x.2.val : ℝ) - ((q : ℝ) - 1) / 2⟩

private theorem grid_coordinate_abs_le (q : ℕ) (x : Fin q) :
    |(x.val : ℝ) - ((q : ℝ) - 1) / 2| ≤ ((q : ℝ) - 1) / 2 := by
  have hx0 : (0 : ℝ) ≤ x.val := Nat.cast_nonneg _
  have hx1 : (x.val : ℝ) + 1 ≤ q := by exact_mod_cast x.isLt
  apply abs_le.mpr
  constructor <;> linarith

theorem gridCenter_norm_le (q : ℕ) (x : Fin q × Fin q) :
    ‖gridCenter q x‖ ≤ (q : ℝ) - 1 := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  change |(x.1.val : ℝ) - ((q : ℝ) - 1) / 2| +
    |(x.2.val : ℝ) - ((q : ℝ) - 1) / 2| ≤ (q : ℝ) - 1
  linarith [grid_coordinate_abs_le q x.1, grid_coordinate_abs_le q x.2]

private theorem nat_cast_separated {a b : ℕ} (h : a ≠ b) :
    (1 : ℝ) ≤ |(a : ℝ) - b| := by
  rcases lt_or_gt_of_ne h with hab | hba
  · have hcast : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
    have h := neg_le_abs ((a : ℝ) - b)
    linarith
  · have hcast : (b : ℝ) + 1 ≤ a := by exact_mod_cast hba
    have h := le_abs_self ((a : ℝ) - b)
    linarith

theorem gridCenter_separated (q : ℕ) (x y : Fin q × Fin q) (hxy : x ≠ y) :
    (1 : ℝ) ≤ ‖gridCenter q x - gridCenter q y‖ := by
  by_cases hfst : x.1 = y.1
  · have hsnd : x.2.val ≠ y.2.val := by
      intro h
      exact hxy (Prod.ext hfst (Fin.ext h))
    have h := Complex.abs_im_le_norm (gridCenter q x - gridCenter q y)
    have hid : (gridCenter q x - gridCenter q y).im = (x.2.val : ℝ) - y.2.val := by
      simp only [gridCenter, Complex.sub_im]
      ring
    rw [hid] at h
    exact (nat_cast_separated hsnd).trans h
  · have hfst' : x.1.val ≠ y.1.val := fun h ↦ hfst (Fin.ext h)
    have h := Complex.abs_re_le_norm (gridCenter q x - gridCenter q y)
    have hid : (gridCenter q x - gridCenter q y).re = (x.1.val : ℝ) - y.1.val := by
      simp only [gridCenter, Complex.sub_re]
      ring
    rw [hid] at h
    exact (nat_cast_separated hfst').trans h

/-- A finite family of scalar centers, with room for a norm-1/4 perturbation
in every diagonal block of the first commutator factor. -/
theorem exists_assembly_centers {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι ≤ 2 * 2 ^ 26 - 1) :
    ∃ z : ι → ℂ, (∀ i, ‖z i‖ + (1 / 4 : ℝ) ≤ 16384) ∧
      ∀ i j, i ≠ j → (1 : ℝ) ≤ ‖z i - z j‖ := by
  have hgrid : Fintype.card ι ≤ Fintype.card (Fin 16384 × Fin 16384) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hgrid
  refine ⟨fun i ↦ gridCenter 16384 (e i), ?_, ?_⟩
  · intro i
    have h := gridCenter_norm_le 16384 (e i)
    norm_num at h ⊢
    linarith
  · intro i j hij
    exact gridCenter_separated 16384 (e i) (e j) (fun h ↦ hij (e.injective h))

/-- Scalar centers for any finite number of blocks, with a linear radius bound. -/
theorem exists_assembly_centers_any {ι : Type*} [Fintype ι] :
    ∃ z : ι → ℂ, (∀ i, ‖z i‖ + (1 / 4 : ℝ) ≤ Fintype.card ι) ∧
      ∀ i j, i ≠ j → (1 : ℝ) ≤ ‖z i - z j‖ := by
  let e := Fintype.equivFin ι
  refine ⟨fun i ↦ gridCenter (Fintype.card ι) (e i, e i), ?_, ?_⟩
  · intro i
    have h := gridCenter_norm_le (Fintype.card ι) (e i, e i)
    linarith
  · intro i j hij
    apply gridCenter_separated
    intro h
    exact hij (e.injective (congrArg Prod.fst h))

end NoEpsilon
