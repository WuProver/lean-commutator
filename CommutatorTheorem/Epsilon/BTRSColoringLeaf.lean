import CommutatorTheorem.Epsilon.BTRSBaseExpansion

/-!
# Determinant leaves in the exact-MDP coloring expansion

For a fixed coloring and color, differentiate the definite determinant in
every coordinate outside that color.  Its diagonal specialization is exactly
the characteristic polynomial of the corresponding principal compression.
-/

namespace CommutatorTheorem.BTRSColoringLeaf

open scoped BigOperators Polynomial
open Finset Polynomial
open CommutatorTheorem
open CommutatorTheorem.BTMixedDet
open CommutatorTheorem.BTDeterminantStability
open CommutatorTheorem.BTRealStabilityClosure
open CommutatorTheorem.BTMDPSelection
open CommutatorTheorem.BTMDPDeletionIdentity
open CommutatorTheorem.BTRSStabilityBridge
open CommutatorTheorem.BTRSExactMDPHarness
open CommutatorTheorem.BTRSBaseExpansion
open CommutatorTheorem.BTHermitianDetPDeriv

/-- The coordinates not carrying color `a`, in an arbitrary fixed order. -/
noncomputable def colorComplementList {n k : ℕ}
    (c : Coloring n k) (a : Fin k) : List (Fin n) :=
  ((Finset.univ : Finset (Fin n)).filter fun i ↦ c i ≠ a).toList

private theorem colorComplementList_nodup {n k : ℕ}
    (c : Coloring n k) (a : Fin k) :
    (colorComplementList c a).Nodup := by
  exact Finset.nodup_toList _

theorem finRange_filter_perm_colorComplement {n k : ℕ}
    (c : Coloring n k) (a : Fin k) :
    ((List.finRange n).filter fun i ↦ c i != a).Perm
      (colorComplementList c a) := by
  classical
  refine (List.perm_ext_iff_of_nodup
    ((List.nodup_finRange n).filter (fun i ↦ c i != a))
    (colorComplementList_nodup c a)).2 ?_
  intro i
  simp [colorComplementList]

private theorem colorComplementList_delete_perm {n k : ℕ}
    (c : Coloring (n + 1) k) (a : Fin k) (i : Fin (n + 1))
    (hi : c i ≠ a) :
    (colorComplementList c a).Perm
      (i :: List.map i.succAbove
        (colorComplementList (deleteColoring i c) a)) := by
  classical
  refine (List.perm_ext_iff_of_nodup
    (colorComplementList_nodup c a) ?_).2 ?_
  · exact List.nodup_cons.mpr ⟨by
      intro himem
      obtain ⟨j, _hj, hji⟩ := List.mem_map.mp himem
      exact Fin.succAbove_ne i j hji, (colorComplementList_nodup _ _).map
        Fin.succAbove_right_injective⟩
  · intro x
    simp only [colorComplementList, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and, List.mem_cons, List.mem_map]
    constructor
    · intro hx
      by_cases hxi : x = i
      · exact Or.inl hxi
      · right
        obtain ⟨j, hji⟩ := Fin.exists_succAbove_eq hxi
        refine ⟨j, ?_, hji⟩
        change c (i.succAbove j) ≠ a
        simpa [hji] using hx
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact hi
      · change c (i.succAbove j) ≠ a
        simpa using hj

/-- A fixed branch of the recursive coloring expansion is precisely the
characteristic polynomial of the principal compression on that color fiber. -/
theorem diagonalizeReal_iteratedPDeriv_colorComplement
    {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ b, (A b).IsHermitian)
    (c : Coloring n k) (a : Fin k) :
    diagonalizeReal
        (iteratedPDeriv (colorComplementList c a)
          (realHermitianDetPoly (A a))) =
      realCharpoly (BTMixedDet.principalCompression (A a) c a)
        (BTMixedDet.principalCompression_isHermitian (hA a) c a) := by
  induction n with
  | zero =>
      have hlist : colorComplementList c a = [] := by
        simp [colorComplementList]
      rw [hlist]
      simp only [iteratedPDeriv_nil]
      rw [diagonalizeReal_realHermitianDetPoly (A a) (hA a)]
      let e : Fin 0 ≃ ColorFiber c a :=
        { toFun := fun i ↦ Fin.elim0 i
          invFun := fun i ↦ Fin.elim0 i.1
          left_inv := fun i ↦ Fin.elim0 i
          right_inv := fun i ↦ Fin.elim0 i.1 }
      symm
      apply realCharpoly_eq_of_reindex_eq e (A a)
        (BTMixedDet.principalCompression (A a) c a) (hA a)
        (BTMixedDet.principalCompression_isHermitian (hA a) c a)
      ext i
      exact Fin.elim0 i
  | succ n ih =>
      classical
      by_cases hall : ∀ i, c i = a
      · have hlist : colorComplementList c a = [] := by
          simp [colorComplementList, hall]
        rw [hlist]
        simp only [iteratedPDeriv_nil]
        rw [diagonalizeReal_realHermitianDetPoly (A a) (hA a)]
        let e : Fin (n + 1) ≃ ColorFiber c a :=
          { toFun := fun i ↦ ⟨i, hall i⟩
            invFun := fun i ↦ i.1
            left_inv := fun _ ↦ rfl
            right_inv := fun i ↦ Subtype.ext rfl }
        symm
        apply realCharpoly_eq_of_reindex_eq e (A a)
          (BTMixedDet.principalCompression (A a) c a) (hA a)
          (BTMixedDet.principalCompression_isHermitian (hA a) c a)
        ext i j
        rfl
      · push_neg at hall
        obtain ⟨i, hi⟩ := hall
        let D := deleteFamilyAt A i
        let d := deleteColoring i c
        have hD : ∀ b, (D b).IsHermitian :=
          deleteFamilyAt_isHermitian hA i
        have hperm := colorComplementList_delete_perm c a i hi
        calc
          diagonalizeReal
              (iteratedPDeriv (colorComplementList c a)
                (realHermitianDetPoly (A a))) =
              diagonalizeReal
                (iteratedPDeriv
                  (i :: List.map i.succAbove (colorComplementList d a))
                  (realHermitianDetPoly (A a))) := by
                    rw [iteratedPDeriv_perm hperm]
          _ = diagonalizeReal
                (iteratedPDeriv (List.map i.succAbove (colorComplementList d a))
                  (MvPolynomial.pderiv i
                    (realHermitianDetPoly (A a)))) := rfl
          _ = diagonalizeReal
                (iteratedPDeriv (List.map i.succAbove (colorComplementList d a))
                  (MvPolynomial.rename i.succAbove
                    (realHermitianDetPoly (D a)))) := by
                    rw [pderiv_realHermitianDetPoly_fin_succ
                      (A a) (hA a) i]
                    rfl
          _ = diagonalizeReal
                (MvPolynomial.rename i.succAbove
                  (iteratedPDeriv (colorComplementList d a)
                    (realHermitianDetPoly (D a)))) := by
                    rw [iteratedPDeriv_rename _ Fin.succAbove_right_injective]
          _ = diagonalizeReal
                (iteratedPDeriv (colorComplementList d a)
                  (realHermitianDetPoly (D a))) :=
                    diagonalizeReal_rename _ _
          _ = realCharpoly (BTMixedDet.principalCompression (D a) d a)
                (BTMixedDet.principalCompression_isHermitian (hD a) d a) :=
                  ih D hD d
          _ = realCharpoly (BTMixedDet.principalCompression (A a) c a)
                (BTMixedDet.principalCompression_isHermitian (hA a) c a) := by
                  have hunchanged :=
                    deletedCompression_realCharpoly_eq_unchanged
                      A hA i (c i) a d (Ne.symm hi)
                  rw [← extendColoring_self_deleteColoring i c]
                  simpa [D, d] using hunchanged

/-- Complex form, with the `finRange` ordering used by
`coloringDerivativeTerm`. -/
theorem diagonalize_iteratedPDeriv_finRange_filter
    {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ b, (A b).IsHermitian)
    (c : Coloring n k) (a : Fin k) :
    diagonalize
        (iteratedPDeriv
          ((List.finRange n).filter fun i ↦ c i != a)
          (hermitianDetPoly (A a))) =
      (BTMixedDet.principalCompression (A a) c a).charpoly := by
  have h := congrArg (Polynomial.map Complex.ofRealHom)
    (diagonalizeReal_iteratedPDeriv_colorComplement A hA c a)
  rw [map_diagonalizeReal, ← iteratedPDeriv_map,
    map_realHermitianDetPoly (A a) (hA a),
    realCharpoly_map_complex] at h
  rw [iteratedPDeriv_perm (finRange_filter_perm_colorComplement c a)]
  exact h

/-- Every summand of the algebraic coloring expansion diagonalizes to the
corresponding exact-MDP leaf. -/
theorem diagonalize_coloringDerivativeTerm
    {n m : ℕ}
    (A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ b, (A b).IsHermitian)
    (c : Coloring n (m + 1)) :
    diagonalize
        (coloringDerivativeTerm (fun i : Fin n ↦ i) c
          (fun a ↦ hermitianDetPoly (A a))) =
      BTMixedDeterminantal.coloringPolynomial A c := by
  unfold coloringDerivativeTerm BTMixedDeterminantal.coloringPolynomial
  unfold diagonalize
  change MvPolynomial.eval₂Hom Polynomial.C (fun _ : Fin n ↦ Polynomial.X)
      (∏ a,
        iteratedPDeriv
          (List.map (fun i : Fin n ↦ i)
            ((List.finRange n).filter fun i ↦ c i != a))
          (hermitianDetPoly (A a))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro a _
  simpa using diagonalize_iteratedPDeriv_finRange_filter A hA c a

end CommutatorTheorem.BTRSColoringLeaf
