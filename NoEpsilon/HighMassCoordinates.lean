import NoEpsilon.OrthonormalCompletion
import NoEpsilon.FinitePartition
import NoEpsilon.AbsorptionCore

/-!
# Coordinates adapted to a proportionate bridge

The unused coordinates are partitioned into exactly `L` fibers, each of dimension at
most the bridge rank. Empty fibers are permitted; no extra ambient coordinates are created.
-/

noncomputable section

namespace NoEpsilon

open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The option-indexed absorption space is its core plus its outside fibers. -/
def absorptionAmbientEquiv {L : ℕ} (r : ℕ) (d : Fin L → Type) :
    Absorption.Ambient r d ≃ (Fin r ⊕ Fin r) ⊕ (Σ i, d i) where
  toFun x := match x with
    | ⟨none, y⟩ => Sum.inl y
    | ⟨some i, y⟩ => Sum.inr ⟨i, y⟩
  invFun x := match x with
    | Sum.inl y => ⟨none, y⟩
    | Sum.inr ⟨i, y⟩ => ⟨some i, y⟩
  left_inv x := by rcases x with ⟨i, y⟩; cases i <;> rfl
  right_inv x := by cases x <;> rfl

/-- Complete the two bridge frames and divide all remaining coordinates into bounded fibers. -/
theorem orthogonal_pair_partitioned_basis {r L : ℕ} (P Q : Matrix ι (Fin r) ℂ)
    (hP : Pᴴ * P = 1) (hQ : Qᴴ * Q = 1) (hPQ : Pᴴ * Q = 0)
    (hCard : Fintype.card ι ≤ L * r) :
    ∃ (m : ℕ) (f : Fin m → Fin L)
      (b : OrthonormalBasis (Absorption.Ambient r (fun i ↦ {x : Fin m // f x = i})) ℂ
        (EuclideanSpace ℂ ι)),
      2 * r + m = Fintype.card ι ∧ (∀ i, Fintype.card {x : Fin m // f x = i} ≤ r) ∧
      (∀ i, b ⟨none, Sum.inl i⟩ = WithLp.toLp 2 (fun j ↦ Q j i)) ∧
      (∀ i, b ⟨none, Sum.inr i⟩ = WithLp.toLp 2 (fun j ↦ P j i)) := by
  classical
  obtain ⟨m, b, hm, hFirst, hSecond⟩ := orthogonal_pair_basis_completion P Q hP hQ hPQ
  have hmCard : Fintype.card (Fin m) ≤ L * r := by simpa using (show m ≤ L * r by omega)
  obtain ⟨f, hf⟩ := exists_bounded_fibers (ν := Fin m) L r hmCard
  let d := fun i ↦ {x : Fin m // f x = i}
  let e : Absorption.Ambient r d ≃ (Fin r ⊕ Fin r) ⊕ Fin m :=
    (absorptionAmbientEquiv r d).trans
      (Equiv.sumCongr (Equiv.refl _) (boundedFiberEquiv f).symm)
  refine ⟨m, f, b.reindex e.symm, hm, hf, ?_, ?_⟩
  · intro i
    simpa [OrthonormalBasis.reindex_apply, e, absorptionAmbientEquiv] using hFirst i
  · intro i
    simpa [OrthonormalBasis.reindex_apply, e, absorptionAmbientEquiv] using hSecond i

end NoEpsilon
