import CommutatorTheorem.NoEpsilon.MSSSelection
import CommutatorTheorem.NoEpsilon.LowMassRecurrence

/-!
# Exact quotas in the balanced binary selection tree

The analytic paired-selection assertion is an explicit premise here. All index permutations,
quotas, coverage, and propagation of the operator norm bound are proved in this file.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NoEpsilon.LowMassPaving

open MSSSelection

noncomputable def splitBound (δ L : ℝ) : ℝ :=
  (Real.sqrt L + 2 * Real.sqrt δ) ^ 2 / 2

theorem splitBound_nonneg (δ L : ℝ) : 0 ≤ splitBound δ L := by
  unfold splitBound
  positivity

/-- The sole analytic input to the finite quota construction. -/
def PairedHalfSelection (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ {κ : Type} [Fintype κ] (a b : κ → ι → ℂ) (δ L : ℝ),
    0 ≤ δ → 0 ≤ L → (∀ i, energy (a i) ≤ δ) → (∀ i, energy (b i) ≤ δ) →
    ‖∑ i, (outer (a i) + outer (b i))‖ ≤ L →
    ∃ q : κ → Bool × Bool,
      ‖∑ i, outer (firstVector a b q i)‖ ≤ splitBound δ L ∧
      ‖∑ i, outer (secondVector a b q i)‖ ≤ splitBound δ L

/-- A depth-indexed binary type without arithmetic casts at a split. -/
def BinaryIndex : ℕ → Type
  | 0 => Unit
  | h + 1 => Bool × BinaryIndex h

instance binaryIndexFintype : (h : ℕ) → Fintype (BinaryIndex h)
  | 0 => inferInstanceAs (Fintype Unit)
  | h + 1 =>
    letI := binaryIndexFintype h
    inferInstanceAs (Fintype (Bool × BinaryIndex h))

instance binaryIndexDecidableEq : (h : ℕ) → DecidableEq (BinaryIndex h)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | h + 1 =>
    letI := binaryIndexDecidableEq h
    inferInstanceAs (DecidableEq (Bool × BinaryIndex h))

theorem binaryIndex_card (h : ℕ) : Fintype.card (BinaryIndex h) = 2 ^ h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change Fintype.card (Bool × BinaryIndex h) = 2 ^ (h + 1)
    rw [Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    omega

def branchPermutation {α : Type*} (e : Bool → Equiv.Perm α) :
    Equiv.Perm (Bool × α) where
  toFun p := (p.1, e p.1 p.2)
  invFun p := (p.1, (e p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

def flipPermutation {α : Type*} (s : α → Bool) : Equiv.Perm (Bool × α) where
  toFun p := (p.1.xor (s p.2), p.2)
  invFun p := (p.1.xor (s p.2), p.2)
  left_inv p := by
    rcases p with ⟨b, x⟩
    change ((b.xor (s x)).xor (s x), x) = (b, x)
    cases b <;> cases s x <;> rfl
  right_inv p := by
    rcases p with ⟨b, x⟩
    change ((b.xor (s x)).xor (s x), x) = (b, x)
    cases b <;> cases s x <;> rfl

noncomputable def treeBound (δ : ℝ) (h : ℕ) (L : ℝ) : ℝ :=
  (splitBound δ)^[h] L

theorem treeBound_nonneg (δ : ℝ) (h : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ treeBound δ h L := by
  induction h with
  | zero => exact hL
  | succ h ih =>
    simpa only [treeBound, Function.iterate_succ_apply'] using
      splitBound_nonneg δ (treeBound δ h L)

theorem binary_sum_split {ι : Type*} [Fintype ι] {k h : ℕ}
    (f : Fin k → BinaryIndex (h + 1) → ι → ℂ) :
    (∑ j, ∑ x, outer (f j x)) =
      ∑ p : Fin k × BinaryIndex h,
        (outer (f p.1 (false, p.2)) + outer (f p.1 (true, p.2))) := by
  change (∑ j, ∑ x : Bool × BinaryIndex h, outer (f j x)) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  exact add_comm _ _

/-- Every group is permuted independently. Hence every leaf contains exactly one element of
each group, and all leaves together contain every original vector exactly once. -/
theorem exists_binary_transversals {ι : Type*} [Fintype ι] [DecidableEq ι]
    (selection : PairedHalfSelection ι) (k h : ℕ) (δ L : ℝ) (hδ : 0 ≤ δ)
    (hL : 0 ≤ L) (f : Fin k → BinaryIndex h → ι → ℂ)
    (hf : ∀ j x, energy (f j x) ≤ δ) (hframe : ‖∑ j, ∑ x, outer (f j x)‖ ≤ L) :
    ∃ σ : Fin k → Equiv.Perm (BinaryIndex h),
      ∀ x, ‖∑ j, outer (f j (σ j x))‖ ≤ treeBound δ h L := by
  induction h generalizing L with
  | zero =>
    refine ⟨fun _ ↦ Equiv.refl _, ?_⟩
    intro x
    cases x
    simpa [treeBound, BinaryIndex] using hframe
  | succ h ih =>
    let a : (Fin k × BinaryIndex h) → ι → ℂ := fun p ↦ f p.1 (false, p.2)
    let b : (Fin k × BinaryIndex h) → ι → ℂ := fun p ↦ f p.1 (true, p.2)
    have hparent : ‖∑ p, (outer (a p) + outer (b p))‖ ≤ L := by
      simpa only [a, b, ← binary_sum_split f] using hframe
    obtain ⟨q, hfirst, hsecond⟩ := selection a b δ L hδ hL
      (fun p ↦ hf p.1 (false, p.2)) (fun p ↦ hf p.1 (true, p.2)) hparent
    let child : Bool → Fin k → BinaryIndex h → ι → ℂ :=
      fun t j x ↦ f j (t.xor (q (j, x)).1, x)
    have hchildEnergy : ∀ t j x, energy (child t j x) ≤ δ :=
      fun t j x ↦ hf j (t.xor (q (j, x)).1, x)
    have hchildFrame : ∀ t, ‖∑ j, ∑ x, outer (child t j x)‖ ≤ splitBound δ L := by
      intro t
      cases t
      · convert hfirst using 1
        rw [Fintype.sum_prod_type]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        dsimp [child, firstVector, a, b]
        cases (q (j, x)).1 <;> rfl
      · convert hsecond using 1
        rw [Fintype.sum_prod_type]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        dsimp [child, secondVector, a, b]
        cases (q (j, x)).1 <;> rfl
    have hchildren : ∀ t, ∃ σ : Fin k → Equiv.Perm (BinaryIndex h),
        ∀ x, ‖∑ j, outer (child t j (σ j x))‖ ≤
          treeBound δ h (splitBound δ L) := by
      intro t
      exact ih (splitBound δ L) (splitBound_nonneg δ L) (child t)
        (hchildEnergy t) (hchildFrame t)
    choose σ hσ using hchildren
    refine ⟨fun j ↦ (branchPermutation (fun t ↦ σ t j)).trans
      (flipPermutation (fun x ↦ (q (j, x)).1)), ?_⟩
    rintro ⟨t, x⟩
    simpa only [treeBound, Function.iterate_succ_apply, Equiv.trans_apply,
      branchPermutation, flipPermutation, Equiv.coe_fn_mk, child] using hσ t x

/-- Quantitative transversals on the ordinary finite interval. -/
theorem exists_transversals {ι : Type*} [Fintype ι] [DecidableEq ι]
    (selection : PairedHalfSelection ι) (k h : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (f : Fin k → Fin (2 ^ h) → ι → ℂ)
    (hf : ∀ j x, energy (f j x) ≤ D / (2 : ℝ) ^ h)
    (hframe : ‖∑ j, ∑ x, outer (f j x)‖ ≤ 1) :
    ∃ σ : Fin k → Equiv.Perm (Fin (2 ^ h)),
      ∀ x, ‖∑ j, outer (f j (σ j x))‖ ≤ transversalConstant D / (2 : ℝ) ^ h := by
  let e : BinaryIndex h ≃ Fin (2 ^ h) :=
    Fintype.equivOfCardEq (by rw [binaryIndex_card, Fintype.card_fin])
  let g : Fin k → BinaryIndex h → ι → ℂ := fun j x ↦ f j (e x)
  have hg : ‖∑ j, ∑ x, outer (g j x)‖ ≤ 1 := by
    have he : (∑ j, ∑ x, outer (g j x)) = ∑ j, ∑ x, outer (f j x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact e.sum_comp (fun x ↦ outer (f j x))
    rw [he]
    exact hframe
  obtain ⟨τ, hτ⟩ := exists_binary_transversals selection k h
    (D / (2 : ℝ) ^ h) 1 (by positivity) (by norm_num) g (fun j x ↦ hf j (e x)) hg
  have hfinal : treeBound (D / (2 : ℝ) ^ h) h 1 ≤
      transversalConstant D / (2 : ℝ) ^ h := by
    apply binary_recurrence_leaf_bound D hD h
      (fun j ↦ treeBound (D / (2 : ℝ) ^ h) j 1)
      (fun j ↦ treeBound_nonneg _ j (by norm_num))
    · rfl
    · intro j
      simp only [treeBound, Function.iterate_succ_apply', splitBound, le_refl]
  refine ⟨fun j ↦ (e.symm.trans (τ j)).trans e, ?_⟩
  intro x
  exact (hτ (e.symm x)).trans hfinal

theorem sum_permuted_vectors {ι κ : Type*} [Fintype ι] [Fintype κ]
    {k : ℕ} (f : Fin k → κ → ι → ℂ) (σ : Fin k → Equiv.Perm κ) :
    (∑ x, ∑ j, outer (f j (σ j x))) = ∑ j, ∑ x, outer (f j x) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ ↦ Equiv.sum_comp (σ j) (fun x ↦ outer (f j x)))

end NoEpsilon.LowMassPaving
