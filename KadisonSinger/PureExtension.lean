import KadisonSinger.States

/-!
# Purity of the unique state extension

An extension unique among all states is pure whenever its restriction is pure.
This is the elementary extreme-point argument, separate from the paving theorem.
-/

noncomputable section
open scoped ComplexOrder
namespace KadisonSinger.State

variable {A D : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [StarOrderedRing A] in
/-- The one-endpoint definition of purity is equivalent to the usual requirement
that both endpoints of every nontrivial convex decomposition equal the state. -/
theorem isPure_iff_extreme (φ : KadisonSinger.State A) :
    φ.IsPure ↔ ∀ (ψ χ : KadisonSinger.State A) (t : ℝ), 0 < t → t < 1 →
      (∀ a, φ.val a = t • ψ.val a + (1-t) • χ.val a) → ψ = φ ∧ χ = φ := by
  constructor
  · intro hφ ψ χ t ht ht' hdecomp
    refine ⟨hφ ψ χ t ht ht' hdecomp, ?_⟩
    apply hφ χ ψ (1-t) (sub_pos.mpr ht') (by linarith)
    intro a
    simpa only [sub_sub_cancel, add_comm] using hdecomp a
  · intro hφ ψ χ t ht ht' hdecomp
    exact (hφ ψ χ t ht ht' hdecomp).1

/-- Restrict a state along a unital star-algebra homomorphism. -/
def restrict (ψ : KadisonSinger.State A) (ι : D →⋆ₐ[ℂ] A) : KadisonSinger.State D :=
  ⟨{ toLinearMap := ψ.val.toLinearMap.comp ι.toAlgHom.toLinearMap
     monotone' := fun _ _ h ↦ OrderHomClass.mono ψ.val (OrderHomClass.mono ι h) }, by
    change ψ.val (ι 1) = 1
    rw [map_one, ψ.apply_one]⟩

lemma restrict_apply (ψ : KadisonSinger.State A) (ι : D →⋆ₐ[ℂ] A) (d : D) :
    (ψ.restrict ι).val d = ψ.val (ι d) := rfl

/-- The unique extension of a pure state is itself pure. Uniqueness here is among
all states, not merely among pure states. -/
theorem isPure_of_unique_extension (ι : D →⋆ₐ[ℂ] A)
    (φ : KadisonSinger.State D) (hφ : φ.IsPure) (ψ : KadisonSinger.State A)
    (hψ : ∀ d, ψ.val (ι d) = φ.val d)
    (hunique : ∀ χ : KadisonSinger.State A, (∀ d, χ.val (ι d) = φ.val d) → χ = ψ) :
    ψ.IsPure := by
  intro χ ξ t ht ht' hdecomp
  have hrestrict : χ.restrict ι = φ := by
    apply hφ (χ.restrict ι) (ξ.restrict ι) t ht ht'
    intro d
    simpa only [restrict_apply, hψ] using hdecomp (ι d)
  apply hunique χ
  intro d
  have h := congrArg (fun ρ : KadisonSinger.State D ↦ ρ.val d) hrestrict
  exact h

/-- Unique state extension supplies a unique pure extension as well. -/
theorem existsUnique_pure_extension (ι : D →⋆ₐ[ℂ] A)
    (φ : KadisonSinger.State D) (hφ : φ.IsPure)
    (h : ∃! ψ : KadisonSinger.State A, ∀ d, ψ.val (ι d) = φ.val d) :
    ∃! ψ : KadisonSinger.State A, ψ.IsPure ∧ ∀ d, ψ.val (ι d) = φ.val d := by
  obtain ⟨ψ, hψ, huniq⟩ := h
  refine ⟨ψ, ⟨isPure_of_unique_extension ι φ hφ ψ hψ huniq, hψ⟩, ?_⟩
  intro χ hχ
  exact huniq χ hχ.2

end KadisonSinger.State

namespace KadisonSinger.State
variable {A D : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CommCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- Self-adjoint projection paving gives the original pure-state conclusion. -/
theorem existsUnique_pure_extension_of_selfAdjoint_paving (ι : D →⋆ₐ[ℂ] A)
    (E : A →ₚ[ℂ] D) (hE : E 1 = 1) (hleft : ∀ d, E (ι d) = d)
    (hpaving : SelfAdjointProjectionPaving ι E) (φ : KadisonSinger.State D)
    (hφ : φ.IsPure) :
    ∃! ψ : KadisonSinger.State A, ψ.IsPure ∧ ∀ d, ψ.val (ι d) = φ.val d :=
  existsUnique_pure_extension ι φ hφ
    (existsUnique_extension_of_selfAdjoint_paving ι E hE hleft hpaving φ hφ)

/-- Projection paving gives the original pure-state conclusion. -/
theorem existsUnique_pure_extension_of_paving (ι : D →⋆ₐ[ℂ] A)
    (E : A →ₚ[ℂ] D) (hE : E 1 = 1) (hleft : ∀ d, E (ι d) = d)
    (hpaving : ProjectionPaving ι E) (φ : KadisonSinger.State D) (hφ : φ.IsPure) :
    ∃! ψ : KadisonSinger.State A, ψ.IsPure ∧ ∀ d, ψ.val (ι d) = φ.val d :=
  existsUnique_pure_extension ι φ hφ
    (existsUnique_extension_of_paving ι E hE hleft hpaving φ hφ)

end KadisonSinger.State
