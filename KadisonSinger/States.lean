import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Tactic

open scoped ComplexOrder

/-!
# State extensions from projection paving

This file proves the functional-analytic implication from arbitrarily fine projection paving to
unique extension of pure states across an expected commutative C*-subalgebra. States are normalized
positive linear functionals; purity is the ordinary extreme-point condition, not a substitute paving
condition. The concrete inclusion, positive expectation, and paving theorem remain explicit inputs
of `State.existsUnique_extension_of_paving`.
-/

noncomputable section

namespace KadisonSinger

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A state is a positive complex linear functional taking the unit to one. -/
def State := {φ : A →ₚ[ℂ] ℂ // φ 1 = 1}

namespace State

variable {A}

/-- Purity is the usual extreme-point condition in the convex set of states. -/
def IsPure (φ : State A) : Prop :=
  ∀ (ψ χ : State A) (t : ℝ), 0 < t → t < 1 →
    (∀ a, φ.val a = t • ψ.val a + (1 - t) • χ.val a) → ψ = φ

omit [StarOrderedRing A] in
lemma apply_one (φ : State A) : φ.val 1 = 1 := φ.property

lemma apply_mul_eq_zero_of_projection (φ : State A) {p : A} (hp : IsStarProjection p)
    (hφp : φ.val p = 0) (a : A) : φ.val (p * a) = 0 := by
  have hn : ‖φ.val.toPreGNS p‖ = 0 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq, hφp]
  have h := norm_inner_le_norm (𝕜 := ℂ) (φ.val.toPreGNS p) (φ.val.toPreGNS a)
  rw [hn, zero_mul] at h
  have hz := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  simpa [PositiveLinearMap.preGNS_inner_def, hp.isSelfAdjoint.star_eq] using hz

lemma apply_mul_eq_zero_of_projection_right (φ : State A) {p : A}
    (hp : IsStarProjection p) (hφp : φ.val p = 0) (a : A) : φ.val (a * p) = 0 := by
  have hn : ‖φ.val.toPreGNS p‖ = 0 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq, hφp]
  have h := norm_inner_le_norm (𝕜 := ℂ) (φ.val.toPreGNS (star a)) (φ.val.toPreGNS p)
  rw [hn, mul_zero] at h
  have hz := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  simpa [PositiveLinearMap.preGNS_inner_def] using hz

lemma apply_eq_compression (φ : State A) {p : A} (hp : IsStarProjection p)
    (hφp : φ.val p = 1) (a : A) : φ.val a = φ.val (p * a * p) := by
  have hq : φ.val (1 - p) = 0 := by simp [map_sub, φ.apply_one, hφp]
  have hl := φ.apply_mul_eq_zero_of_projection hp.one_sub hq a
  have hr := φ.apply_mul_eq_zero_of_projection_right hp.one_sub hq (p * a)
  rw [sub_mul, one_mul, map_sub, sub_eq_zero] at hl
  rw [mul_sub, mul_one, map_sub, sub_eq_zero] at hr
  exact hl.trans hr

/-- The state obtained by conditioning on a projection of nonzero state mass. -/
def corner (φ : State A) {p : A} (hp : IsStarProjection p)
    (ht : 0 < (φ.val p).re) : State A :=
  ⟨PositiveLinearMap.mk₀
    { toFun := fun a ↦ ((φ.val p).re)⁻¹ • φ.val (p * a * p)
      map_add' := by intro a b; simp [mul_add, add_mul]
      map_smul' := by intro c a; simp [mul_left_comm] }
    (by
      intro a ha
      exact smul_nonneg (inv_nonneg.mpr ht.le)
        (φ.val.map_nonneg (hp.isSelfAdjoint.conjugate_nonneg ha))), by
    change ((φ.val p).re)⁻¹ • φ.val (p * 1 * p) = 1
    rw [mul_one, hp.isIdempotentElem.eq]
    have hi := (Complex.nonneg_iff.mp (φ.val.map_nonneg hp.nonneg)).2
    apply Complex.ext <;> simp [hi.symm, ht.ne']⟩

lemma corner_apply (φ : State A) {p : A} (hp : IsStarProjection p)
    (ht : 0 < (φ.val p).re) (a : A) :
    (φ.corner hp ht).val a = ((φ.val p).re)⁻¹ • φ.val (p * a * p) := rfl

/-- A pure state takes every central projection to either zero or one. -/
theorem apply_central_projection_eq_zero_or_one (φ : State A) (hφ : φ.IsPure)
    {p : A} (hp : IsStarProjection p) (hcentral : ∀ a, Commute p a) :
    φ.val p = 0 ∨ φ.val p = 1 := by
  have hnonneg := Complex.nonneg_iff.mp (φ.val.map_nonneg hp.nonneg)
  have hle := OrderHomClass.mono φ.val hp.le_one
  rw [φ.apply_one] at hle
  by_cases hzero : φ.val p = 0
  · exact Or.inl hzero
  by_cases hone : φ.val p = 1
  · exact Or.inr hone
  have ht : 0 < (φ.val p).re := by
    refine lt_of_le_of_ne hnonneg.1 ?_
    intro h
    apply hzero
    exact Complex.ext h.symm hnonneg.2.symm
  have ht' : (φ.val p).re < 1 := by
    refine lt_of_le_of_ne hle.1 ?_
    intro h
    apply hone
    exact Complex.ext h hnonneg.2.symm
  have hqt : 0 < (φ.val (1 - p)).re := by
    simp only [map_sub, φ.apply_one, Complex.sub_re, Complex.one_re]
    linarith
  have hdecomp (a : A) :
      p * a * p + (1 - p) * a * (1 - p) = a := by
    have hpa : p * a * p = p * a := by
      rw [(hcentral a).eq, mul_assoc, hp.isIdempotentElem.eq]
    have hqa : (1 - p) * a * (1 - p) = (1 - p) * a := by
      have hqcentral : Commute (1 - p) a := (Commute.one_left a).sub_left (hcentral a)
      rw [hqcentral.eq, mul_assoc, hp.one_sub.isIdempotentElem.eq]
    rw [hpa, hqa, ← add_mul, add_sub_cancel, one_mul]
  have heq : φ.corner hp ht = φ := by
    apply hφ (φ.corner hp ht) (φ.corner hp.one_sub hqt) (φ.val p).re ht ht'
    intro a
    have hqre : (φ.val (1 - p)).re = 1 - (φ.val p).re := by
      simp [map_sub, φ.apply_one]
    simp only [corner_apply, hqre]
    have hqn : (1 : ℂ) - ((φ.val p).re : ℂ) ≠ 0 := by
      exact_mod_cast (sub_pos.mpr ht').ne'
    simp [ht.ne', hqn, ← map_add, hdecomp]
  have hcorner : (φ.corner hp ht).val p = 1 := by
    rw [corner_apply]
    simp only [hp.isIdempotentElem.eq]
    have h := (φ.corner hp ht).apply_one
    rw [corner_apply, mul_one, hp.isIdempotentElem.eq] at h
    exact h
  rw [heq] at hcorner
  exact Or.inr hcorner

end State

variable {A}
variable {D : Type*} [CommCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- Projection paving relative to an inclusion and a diagonal expectation. This is an explicit
hypothesis for the state-extension bridge, not a definition of the Kadison--Singer conjecture. -/
def ProjectionPaving (ι : D →⋆ₐ[ℂ] A) (E : A →ₚ[ℂ] D) : Prop :=
  ∀ a : A, E a = 0 → ∀ ε : ℝ, 0 < ε →
    ∃ (r : ℕ) (p : Fin r → D), (∀ i, IsStarProjection (p i)) ∧
      (∑ i, p i) = 1 ∧ ∀ i, ‖ι (p i) * a * ι (p i)‖ ≤ ε

/-- The self-adjoint version of projection paving. -/
def SelfAdjointProjectionPaving (ι : D →⋆ₐ[ℂ] A) (E : A →ₚ[ℂ] D) : Prop :=
  ∀ a : A, IsSelfAdjoint a → E a = 0 → ∀ ε : ℝ, 0 < ε →
    ∃ (r : ℕ) (p : Fin r → D), (∀ i, IsStarProjection (p i)) ∧
      (∑ i, p i) = 1 ∧ ∀ i, ‖ι (p i) * a * ι (p i)‖ ≤ ε

namespace State

/-- Composition with a positive unital expectation gives a state extension. -/
def throughExpectation (φ : State D) (E : A →ₚ[ℂ] D) (hE : E 1 = 1) : State A :=
  ⟨{ toLinearMap := φ.val.toLinearMap.comp E.toLinearMap
     monotone' := fun _ _ h ↦ OrderHomClass.mono φ.val (OrderHomClass.mono E h) }, by
    change φ.val (E 1) = 1
    rw [hE, φ.apply_one]⟩

omit [StarOrderedRing A] [StarOrderedRing D] in
lemma throughExpectation_apply (φ : State D) (E : A →ₚ[ℂ] D) (hE : E 1 = 1) (a : A) :
    (φ.throughExpectation E hE).val a = φ.val (E a) := rfl

/-- Arbitrarily small projection compressions force a pure-state extension to vanish. -/
theorem apply_eq_zero_of_projection_compressions (ι : D →⋆ₐ[ℂ] A)
    (φ : State D) (hφ : φ.IsPure) (ψ : State A)
    (hψ : ∀ d, ψ.val (ι d) = φ.val d) {a : A}
    (hpaving : ∀ ε : ℝ, 0 < ε → ∃ (r : ℕ) (p : Fin r → D),
      (∀ i, IsStarProjection (p i)) ∧ (∑ i, p i) = 1 ∧
        ∀ i, ‖ι (p i) * a * ι (p i)‖ ≤ ε) : ψ.val a = 0 := by
  obtain ⟨C, hC⟩ := PositiveLinearMap.exists_norm_apply_le ψ.val
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hCp : 0 < (C : ℝ) + 1 := by positivity
  obtain ⟨r, p, hp, hsum, hnorm⟩ := hpaving (δ / (C + 1)) (div_pos hδ hCp)
  have hone : ∃ i, φ.val (p i) = 1 := by
    by_contra! hnone
    have hz : ∀ i, φ.val (p i) = 0 := by
      intro i
      exact (φ.apply_central_projection_eq_zero_or_one hφ (hp i)
        (fun a ↦ Commute.all _ _)).resolve_right (hnone i)
    have heq := congrArg φ.val hsum
    simp only [map_sum, hz, Finset.sum_const_zero, φ.apply_one] at heq
    exact zero_ne_one heq
  obtain ⟨i, hi⟩ := hone
  have hψp : ψ.val (ι (p i)) = 1 := (hψ _).trans hi
  rw [ψ.apply_eq_compression ((hp i).map ι) hψp a]
  calc
    ‖ψ.val (ι (p i) * a * ι (p i))‖ ≤ C * ‖ι (p i) * a * ι (p i)‖ := hC _
    _ ≤ C * (δ / (C + 1)) := mul_le_mul_of_nonneg_left (hnorm i) C.coe_nonneg
    _ ≤ 0 + δ := by
      rw [zero_add, ← mul_div_assoc, div_le_iff₀ hCp]
      nlinarith [C.coe_nonneg]

/-- An extension of a pure diagonal state vanishes on every operator with zero expectation,
provided arbitrarily fine projection pavings exist. -/
theorem apply_eq_zero_of_paving (ι : D →⋆ₐ[ℂ] A) (E : A →ₚ[ℂ] D)
    (hpaving : ProjectionPaving ι E) (φ : State D) (hφ : φ.IsPure)
    (ψ : State A) (hψ : ∀ d, ψ.val (ι d) = φ.val d) {a : A} (ha : E a = 0) :
    ψ.val a = 0 :=
  apply_eq_zero_of_projection_compressions ι φ hφ ψ hψ (hpaving a ha)

/-- Projection paving implies unique extension of pure states across an expected commutative
C*-subalgebra. The inclusion, expectation, and paving property are hypotheses to be instantiated. -/
theorem existsUnique_extension_of_paving (ι : D →⋆ₐ[ℂ] A) (E : A →ₚ[ℂ] D)
    (hE : E 1 = 1) (hleft : ∀ d, E (ι d) = d) (hpaving : ProjectionPaving ι E)
    (φ : State D) (hφ : φ.IsPure) :
    ∃! ψ : State A, ∀ d, ψ.val (ι d) = φ.val d := by
  refine ⟨φ.throughExpectation E hE, ?_, ?_⟩
  · intro d
    simp only [throughExpectation_apply, hleft]
  · intro ψ hψ
    apply Subtype.ext
    apply PositiveLinearMap.ext
    intro a
    have ha : E (a - ι (E a)) = 0 := by simp [map_sub, hleft]
    have hz := apply_eq_zero_of_paving ι E hpaving φ hφ ψ hψ ha
    rw [map_sub, sub_eq_zero] at hz
    exact hz.trans (hψ (E a))

/-- Self-adjoint paving suffices for vanishing on the entire kernel of the expectation. -/
theorem apply_eq_zero_of_selfAdjoint_paving (ι : D →⋆ₐ[ℂ] A) (E : A →ₚ[ℂ] D)
    (hpaving : SelfAdjointProjectionPaving ι E) (φ : State D) (hφ : φ.IsPure)
    (ψ : State A) (hψ : ∀ d, ψ.val (ι d) = φ.val d) {a : A} (ha : E a = 0) :
    ψ.val a = 0 := by
  have hre : E (realPart a : A) = 0 := by
    simp [realPart_apply_coe, ← Complex.coe_smul, map_add, map_star, ha]
  have him : E (imaginaryPart a : A) = 0 := by
    simp [imaginaryPart_apply_coe, ← Complex.coe_smul, map_sub, map_star, ha]
  have hψre := apply_eq_zero_of_projection_compressions ι φ hφ ψ hψ
    (hpaving (realPart a) (realPart a).property hre)
  have hψim := apply_eq_zero_of_projection_compressions ι φ hφ ψ hψ
    (hpaving (imaginaryPart a) (imaginaryPart a).property him)
  rw [← realPart_add_I_smul_imaginaryPart a, map_add, map_smul, hψre, hψim]
  simp

/-- The pure-state extension theorem needs only self-adjoint projection paving. -/
theorem existsUnique_extension_of_selfAdjoint_paving (ι : D →⋆ₐ[ℂ] A)
    (E : A →ₚ[ℂ] D) (hE : E 1 = 1) (hleft : ∀ d, E (ι d) = d)
    (hpaving : SelfAdjointProjectionPaving ι E) (φ : State D) (hφ : φ.IsPure) :
    ∃! ψ : State A, ∀ d, ψ.val (ι d) = φ.val d := by
  refine ⟨φ.throughExpectation E hE, ?_, ?_⟩
  · intro d
    simp only [throughExpectation_apply, hleft]
  · intro ψ hψ
    apply Subtype.ext
    apply PositiveLinearMap.ext
    intro a
    have ha : E (a - ι (E a)) = 0 := by simp [map_sub, hleft]
    have hz := apply_eq_zero_of_selfAdjoint_paving ι E hpaving φ hφ ψ hψ ha
    rw [map_sub, sub_eq_zero] at hz
    exact hz.trans (hψ (E a))

end State
end KadisonSinger
