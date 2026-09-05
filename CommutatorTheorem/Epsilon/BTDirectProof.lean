import CommutatorTheorem.Epsilon.BTJointReduction
import CommutatorTheorem.Epsilon.BTPrerequisites
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# A direct finite-paving harness for Bourgain--Tzafriri

This file separates the purely finite-dimensional extraction step in the
Bourgain--Tzafriri central-submatrix theorem from its deep analytic input.
The input is stated as a simultaneous paving theorem for two Hermitian
zero-diagonal contractions.  Everything after that paving statement is proved
here, without axioms.

The constant `24` is chosen to match `JointRestrictedInvertibility` in
`BTJointReduction.lean`.  Thus the only remaining statement is a concrete
finite coloring theorem: at most `24 / t^2` colors, with every color compression
of both matrices having norm at most `t`.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
  Matrix.instL2OpNormedSpace Matrix.instL2OpNormedRing Matrix.instCStarRing

namespace CommutatorTheorem

open scoped BigOperators
open scoped MatrixOrder

/-- The coordinates assigned a fixed color. -/
def colorFiberFinset {m r : ℕ} (c : Fin m → Fin r) (a : Fin r) :
    Finset (Fin m) :=
  Finset.univ.filter fun i ↦ c i = a

@[simp] lemma mem_colorFiberFinset {m r : ℕ} (c : Fin m → Fin r)
    (a : Fin r) (i : Fin m) :
    i ∈ colorFiberFinset c a ↔ c i = a := by
  simp [colorFiberFinset]

/-- The color fibers partition the coordinate set, expressed as a cardinality
identity. -/
lemma sum_card_colorFiberFinset {m r : ℕ} (c : Fin m → Fin r) :
    ∑ a : Fin r, (colorFiberFinset c a).card = m := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin m)))
    (t := (Finset.univ : Finset (Fin r)))
    (f := c) (fun _ _ ↦ Finset.mem_univ _)
  simpa [colorFiberFinset] using h.symm

/-- Pigeonhole extraction in the multiplicative form needed below. -/
lemma exists_colorFiber_card_ge {m r k : ℕ} (hr : 0 < r)
    (c : Fin m → Fin r) (hsize : r * k ≤ m) :
    ∃ a : Fin r, k ≤ (colorFiberFinset c a).card := by
  classical
  by_contra h
  push Not at h
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hsum_lt :
      ∑ a : Fin r, (colorFiberFinset c a).card < ∑ _a : Fin r, k := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _ ↦ h a)
  have hsum := sum_card_colorFiberFinset c
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul] at hsum_lt
  omega

/-- Passing from a principal compression to a smaller coordinate subset cannot
increase the operator norm. -/
lemma principalCompression_subset_norm_le {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) {t s : Finset (Fin m)} (hts : t ⊆ s) :
    ‖principalCompression A t‖ ≤ ‖principalCompression A s‖ := by
  classical
  let g : Fin t.card → Fin s.card := fun i ↦
    (s.orderIsoOfFin rfl).symm
      ⟨t.orderEmbOfFin rfl i, hts (t.orderEmbOfFin_mem rfl i)⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply (t.orderEmbOfFin rfl).injective
    have hsub :
        (⟨t.orderEmbOfFin rfl i, hts (t.orderEmbOfFin_mem rfl i)⟩ : s) =
          ⟨t.orderEmbOfFin rfl j, hts (t.orderEmbOfFin_mem rfl j)⟩ := by
      exact (s.orderIsoOfFin rfl).symm.injective (by simpa [g] using hij)
    exact congrArg (fun x : s ↦ (x : Fin m)) hsub
  have heq :
      principalCompression A t =
        (principalCompression A s).submatrix g g := by
    ext i j
    simp only [principalCompression_apply, Matrix.submatrix_apply]
    have hi : s.orderEmbOfFin rfl (g i) = t.orderEmbOfFin rfl i := by
      change (((s.orderIsoOfFin rfl)
        ((s.orderIsoOfFin rfl).symm
          ⟨t.orderEmbOfFin rfl i, hts (t.orderEmbOfFin_mem rfl i)⟩) : s) : Fin m) = _
      simp
    have hj : s.orderEmbOfFin rfl (g j) = t.orderEmbOfFin rfl j := by
      change (((s.orderIsoOfFin rfl)
        ((s.orderIsoOfFin rfl).symm
          ⟨t.orderEmbOfFin rfl j, hts (t.orderEmbOfFin_mem rfl j)⟩) : s) : Fin m) = _
      simp
    rw [hi, hj]
  rw [heq]
  simpa only [Matrix.submatrix] using
    submatrix_norm_le g hg (principalCompression A s)

/-- Sized version of `principalCompression_subset_norm_le`: enumerate a
`k`-element subset directly by `Fin k`. -/
lemma submatrix_orderEmb_subset_norm_le {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) {t s : Finset (Fin m)}
    (hts : t ⊆ s) (htcard : t.card = k) :
    ‖A.submatrix (t.orderEmbOfFin htcard) (t.orderEmbOfFin htcard)‖ ≤
      ‖principalCompression A s‖ := by
  classical
  let g : Fin k → Fin s.card := fun i ↦
    (s.orderIsoOfFin rfl).symm
      ⟨t.orderEmbOfFin htcard i, hts (t.orderEmbOfFin_mem htcard i)⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply (t.orderEmbOfFin htcard).injective
    have hsub :
        (⟨t.orderEmbOfFin htcard i, hts (t.orderEmbOfFin_mem htcard i)⟩ : s) =
          ⟨t.orderEmbOfFin htcard j, hts (t.orderEmbOfFin_mem htcard j)⟩ := by
      exact (s.orderIsoOfFin rfl).symm.injective (by simpa [g] using hij)
    exact congrArg (fun x : s ↦ (x : Fin m)) hsub
  have heq :
      A.submatrix (t.orderEmbOfFin htcard) (t.orderEmbOfFin htcard) =
        (principalCompression A s).submatrix g g := by
    ext i j
    simp only [principalCompression_apply, Matrix.submatrix_apply]
    have hi : s.orderEmbOfFin rfl (g i) = t.orderEmbOfFin htcard i := by
      change (((s.orderIsoOfFin rfl)
        ((s.orderIsoOfFin rfl).symm
          ⟨t.orderEmbOfFin htcard i, hts (t.orderEmbOfFin_mem htcard i)⟩) : s) : Fin m) = _
      simp
    have hj : s.orderEmbOfFin rfl (g j) = t.orderEmbOfFin htcard j := by
      change (((s.orderIsoOfFin rfl)
        ((s.orderIsoOfFin rfl).symm
          ⟨t.orderEmbOfFin htcard j, hts (t.orderEmbOfFin_mem htcard j)⟩) : s) : Fin m) = _
      simp
    rw [hi, hj]
  rw [heq]
  simpa only [Matrix.submatrix] using
    submatrix_norm_le g hg (principalCompression A s)

/-- A Hermitian matrix whose spectrum is order-bounded by `[-t,t]` has
operator norm at most `t`.  This is the spectral bridge used to combine the
one-sided bounds for `H` and `-H`. -/
lemma hermitian_norm_le_of_order_bounds {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    {t : ℝ} (ht : 0 ≤ t)
    (hlower : algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) (-t) ≤ A)
    (hupper : A ≤ algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) t) :
    ‖A‖ ≤ t := by
  have hu : ∀ x ∈ spectrum ℝ A, x ≤ t :=
    (le_algebraMap_iff_spectrum_le hA.isSelfAdjoint).mp hupper
  have hl : ∀ x ∈ spectrum ℝ A, -t ≤ x :=
    (algebraMap_le_iff_le_spectrum hA.isSelfAdjoint).mp hlower
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg ht).2
  intro i
  have hi := hA.eigenvalues_mem_spectrum_real i
  have habs : |hA.eigenvalues i| ≤ t := abs_le.2 ⟨hl _ hi, hu _ hi⟩
  simpa [Function.comp_apply, Complex.norm_real] using habs

/-- The one-sided four-matrix selection theorem delivered by the
multi-paving/root-shrinking route.

For four Hermitian zero-diagonal contractions, a common coordinate set of
size `floor (t^2 m / 24)` makes the largest eigenvalue of every compression at
most `t`; matrix order is the eigenvalue-free way to state that conclusion.
This matches the `n ε² / (6k)` size with `k = 4`.
-/
def FourHermitianUpperSelection24 : Prop :=
  ∀ (m : ℕ) (M : Fin 4 → Matrix (Fin m) (Fin m) ℂ),
    (∀ j, ZeroDiag (M j)) →
    (∀ j, (M j).IsHermitian) →
    (∀ j, ‖M j‖ ≤ 1) →
    ∀ (t : ℝ), 0 < t → t < 1 →
      ∃ f : Fin ⌊(t ^ 2 / 24) * (m : ℝ)⌋₊ → Fin m,
        Function.Injective f ∧
        ∀ j : Fin 4,
          (M j).submatrix f f ≤
            algebraMap ℝ
              (Matrix (Fin ⌊(t ^ 2 / 24) * (m : ℝ)⌋₊)
                (Fin ⌊(t ^ 2 / 24) * (m : ℝ)⌋₊) ℂ) t

/-- The one-sided four-matrix theorem implies the two-sided norm formulation
`JointRestrictedInvertibility`: apply it to `H,-H,G,-G` and use the spectral
order bridge above. -/
theorem jointRestrictedInvertibility_of_fourHermitianUpperSelection24
    (hselect : FourHermitianUpperSelection24) :
    JointRestrictedInvertibility := by
  intro m H G hHzd hHherm hHnorm hGzd hGherm hGnorm t ht ht1
  let M : Fin 4 → Matrix (Fin m) (Fin m) ℂ := ![H, -H, G, -G]
  have hMzd : ∀ j, ZeroDiag (M j) := by
    intro j
    fin_cases j
    · change ZeroDiag H
      exact hHzd
    · change ZeroDiag (-H)
      intro i
      exact neg_eq_zero.mpr (hHzd i)
    · change ZeroDiag G
      exact hGzd
    · change ZeroDiag (-G)
      intro i
      exact neg_eq_zero.mpr (hGzd i)
  have hMherm : ∀ j, (M j).IsHermitian := by
    intro j
    fin_cases j
    · change H.IsHermitian
      exact hHherm
    · change (-H).IsHermitian
      exact hHherm.neg
    · change G.IsHermitian
      exact hGherm
    · change (-G).IsHermitian
      exact hGherm.neg
  have hMnorm : ∀ j, ‖M j‖ ≤ 1 := by
    intro j
    fin_cases j
    · change ‖H‖ ≤ 1
      exact hHnorm
    · change ‖-H‖ ≤ 1
      simpa only [norm_neg] using hHnorm
    · change ‖G‖ ≤ 1
      exact hGnorm
    · change ‖-G‖ ≤ 1
      simpa only [norm_neg] using hGnorm
  obtain ⟨f, hf, hupper⟩ := hselect m M hMzd hMherm hMnorm t ht ht1
  let N := ⌊(t ^ 2 / 24) * (m : ℝ)⌋₊
  have hHu := hupper (0 : Fin 4)
  have hHneg := hupper (1 : Fin 4)
  have hGu := hupper (2 : Fin 4)
  have hGneg := hupper (3 : Fin 4)
  change H.submatrix f f ≤ _ at hHu
  change (-H).submatrix f f ≤ _ at hHneg
  change G.submatrix f f ≤ _ at hGu
  change (-G).submatrix f f ≤ _ at hGneg
  rw [Matrix.submatrix_neg] at hHneg hGneg
  have hHl :
      algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) (-t) ≤ H.submatrix f f := by
    have := (neg_le.mp hHneg)
    simpa [N] using this
  have hGl :
      algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) (-t) ≤ G.submatrix f f := by
    have := (neg_le.mp hGneg)
    simpa [N] using this
  refine ⟨f, hf, ?_, ?_⟩
  · exact hermitian_norm_le_of_order_bounds (H.submatrix f f)
      (hHherm.submatrix f) ht.le hHl (by simpa [N] using hHu)
  · exact hermitian_norm_le_of_order_bounds (G.submatrix f f)
      (hGherm.submatrix f) ht.le hGl (by simpa [N] using hGu)

/-- The published one-sided four-matrix selection statement is therefore
already sufficient for the full Bourgain--Tzafriri central-submatrix estimate,
with explicit constant `4 * sqrt 6`. -/
theorem bourgainTzafriri_of_fourHermitianUpperSelection24
    (hselect : FourHermitianUpperSelection24) :
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ (4 * Real.sqrt 6) * ε * ‖A‖ :=
  central_submatrix_of_jointRestrictedInvertibility
    (jointRestrictedInvertibility_of_fourHermitianUpperSelection24 hselect)

/-- The exact analytic statement left by the direct paving route.

For every pair of zero-diagonal Hermitian contractions and `0 < t < 1`, it
produces a coloring with a positive number `r` of colors, with
`r * t^2 ≤ 24`, such that every color compression of both matrices has norm
at most `t`.  This is a finite, simultaneous Anderson-paving statement; it is
the remaining deep input in this harness, not an axiom declaration. -/
def JointHermitianPaving24 : Prop :=
  ∀ (m : ℕ) (H G : Matrix (Fin m) (Fin m) ℂ),
    ZeroDiag H → H.IsHermitian → ‖H‖ ≤ 1 →
    ZeroDiag G → G.IsHermitian → ‖G‖ ≤ 1 →
    ∀ (t : ℝ), 0 < t → t < 1 →
      ∃ (r : ℕ), 0 < r ∧ (r : ℝ) * t ^ 2 ≤ 24 ∧
        ∃ c : Fin m → Fin r,
          ∀ a : Fin r,
            ‖principalCompression H (colorFiberFinset c a)‖ ≤ t ∧
            ‖principalCompression G (colorFiberFinset c a)‖ ≤ t

/-- The finite simultaneous-paving statement implies the exact
joint-restricted-invertibility proposition used by the Bourgain--Tzafriri
reduction. -/
theorem jointRestrictedInvertibility_of_jointHermitianPaving24
    (hpaving : JointHermitianPaving24) :
    JointRestrictedInvertibility := by
  intro m H G hHzd hHherm hHnorm hGzd hGherm hGnorm t ht ht1
  obtain ⟨r, hr, hrscale, c, hc⟩ :=
    hpaving m H G hHzd hHherm hHnorm hGzd hGherm hGnorm t ht ht1
  let k : ℕ := ⌊(t ^ 2 / 24) * (m : ℝ)⌋₊
  have harg_nonneg : 0 ≤ (t ^ 2 / 24) * (m : ℝ) := by positivity
  have hk_cast : (k : ℝ) ≤ (t ^ 2 / 24) * (m : ℝ) := by
    exact Nat.floor_le harg_nonneg
  have hr_nonneg : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hm_nonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hrk_real : (r : ℝ) * (k : ℝ) ≤ (m : ℝ) := by
    calc
      (r : ℝ) * (k : ℝ)
          ≤ (r : ℝ) * ((t ^ 2 / 24) * (m : ℝ)) :=
            mul_le_mul_of_nonneg_left hk_cast hr_nonneg
      _ = (((r : ℝ) * t ^ 2) / 24) * (m : ℝ) := by ring
      _ ≤ 1 * (m : ℝ) := by
        gcongr
        exact (div_le_one (by norm_num : (0 : ℝ) < 24)).2 hrscale
      _ = (m : ℝ) := one_mul _
  have hrk : r * k ≤ m := by exact_mod_cast hrk_real
  obtain ⟨a, ha⟩ := exists_colorFiber_card_ge hr c hrk
  let s : Finset (Fin m) := colorFiberFinset c a
  obtain ⟨u, hus, hucard⟩ := Finset.exists_subset_card_eq ha
  let f : Fin k → Fin m := u.orderEmbOfFin hucard
  have hf : Function.Injective f := (u.orderEmbOfFin hucard).injective
  refine ⟨f, hf, ?_, ?_⟩
  · calc
      ‖H.submatrix f f‖
          ≤ ‖principalCompression H s‖ := by
            exact submatrix_orderEmb_subset_norm_le H hus hucard
      _ ≤ t := (hc a).1
  · calc
      ‖G.submatrix f f‖
          ≤ ‖principalCompression G s‖ := by
            exact submatrix_orderEmb_subset_norm_le G hus hucard
      _ ≤ t := (hc a).2

/-- Consequently, simultaneous paving proves the full central-submatrix
Bourgain--Tzafriri conclusion, with the explicit constant `4 * sqrt 6`. -/
theorem bourgainTzafriri_of_jointHermitianPaving24
    (hpaving : JointHermitianPaving24) :
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ (4 * Real.sqrt 6) * ε * ‖A‖ :=
  central_submatrix_of_jointRestrictedInvertibility
    (jointRestrictedInvertibility_of_jointHermitianPaving24 hpaving)

end CommutatorTheorem
