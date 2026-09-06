import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic

/-!
# A finite partition into a prescribed number of bounded-size fibers

Empty fibers are permitted. The associated sigma equivalence preserves exactly the
original index set, so this construction does not add matrix coordinates.
-/

open scoped Classical

namespace NoEpsilon

/-- Partition a finite type into L fibers, each of cardinality at most r. -/
theorem exists_bounded_fibers {ν : Type*} [Fintype ν] (L r : ℕ)
    (hcard : Fintype.card ν ≤ L * r) :
    ∃ f : ν → Fin L, ∀ i, Fintype.card {x : ν // f x = i} ≤ r := by
  have hgrid : Fintype.card ν ≤ Fintype.card (Fin L × Fin r) := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hgrid
  let f : ν → Fin L := fun x ↦ (e x).1
  refine ⟨f, ?_⟩
  intro i
  let g : {x : ν // f x = i} → Fin r := fun x ↦ (e x.val).2
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · exact x.property.trans y.property.symm
    · exact hxy
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective g hg

/-- The fibers reassemble to the original type without adding coordinates. -/
def boundedFiberEquiv {ν : Type*} {L : ℕ} (f : ν → Fin L) :
    ν ≃ Σ i : Fin L, {x : ν // f x = i} :=
  (Equiv.sigmaFiberEquiv f).symm

end NoEpsilon
