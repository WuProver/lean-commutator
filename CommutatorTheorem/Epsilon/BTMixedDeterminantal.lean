import CommutatorTheorem.Defs
import CommutatorTheorem.Epsilon.BTMixedDet

/-!
# The mixed determinantal polynomial used by joint restricted invertibility

`BTMixedDet.averageCharpoly` records useful coefficient-counting lemmas for
uniform coordinate colorings.  The polynomial used in the
Ravichandran--Srivastava proof is slightly different: for each coloring it is
the *product* of the characteristic polynomials of the corresponding
principal compressions, one compression for each member of the matrix family.

This file defines that exact polynomial and proves the elementary degree,
monicity, Hermitian-splitting, and permutation-invariance facts.  The deep
remaining statement is that the relevant conditional averages are
real-rooted; that is the real-stability/interlacing input.
-/

open scoped BigOperators Polynomial

namespace CommutatorTheorem.BTMixedDeterminantal

open CommutatorTheorem.BTMixedDet

/-- The disjoint union of all color fibers is canonically the original
coordinate type. -/
def sigmaColorFiberEquiv {n r : ℕ} (c : Coloring n r) :
    (Σ a : Fin r, ColorFiber c a) ≃ Fin n where
  toFun x := x.2.1
  invFun i := ⟨c i, ⟨i, rfl⟩⟩
  left_inv := by
    rintro ⟨a, i, hi⟩
    subst a
    rfl
  right_inv := by
    intro i
    rfl

/-- The cardinalities of the color fibers sum to the ambient dimension. -/
lemma sum_card_colorFiber {n r : ℕ} (c : Coloring n r) :
    ∑ a : Fin r, Fintype.card (ColorFiber c a) = n := by
  rw [← Fintype.card_sigma]
  simpa using Fintype.card_congr (sigmaColorFiberEquiv c)

/-- One leaf in the mixed-determinantal interlacing family. -/
noncomputable def coloringPolynomial {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (c : Coloring n k) : ℂ[X] :=
  ∏ a : Fin k, (principalCompression (A a) c a).charpoly

/-- Each coloring polynomial is monic. -/
theorem coloringPolynomial_monic {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (c : Coloring n k) :
    (coloringPolynomial A c).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro a _
  exact Matrix.charpoly_monic _

/-- Every coloring polynomial has degree exactly `n`: the color fibers form a
partition of the coordinates. -/
theorem coloringPolynomial_natDegree {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (c : Coloring n k) :
    (coloringPolynomial A c).natDegree = n := by
  rw [coloringPolynomial, Polynomial.natDegree_prod_of_monic]
  · simpa using sum_card_colorFiber c
  · intro a _
    exact Matrix.charpoly_monic _

/-- For a Hermitian family, every leaf polynomial splits over `ℂ`, and all
of its roots are real. -/
theorem coloringPolynomial_splits {n k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) :
    (coloringPolynomial A c).Splits := by
  apply Polynomial.Splits.prod
  intro a _
  exact (principalCompression_isHermitian (hA a) c a).splits_charpoly

/-- Uniform average of the exact mixed-determinantal leaves.  The factor is
`k⁻ⁿ`, written as the inverse of the finite coloring count. -/
noncomputable def mixedDeterminantalPolynomial {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) : ℂ[X] :=
  ((Fintype.card (Coloring n k) : ℂ)⁻¹) •
    ∑ c : Coloring n k, coloringPolynomial A c

private lemma coeff_natDegree_coloringPolynomial {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (c : Coloring n k) :
    (coloringPolynomial A c).coeff n = 1 := by
  have h := (coloringPolynomial_monic A c).coeff_natDegree
  simpa only [coloringPolynomial_natDegree A c] using h

private lemma coeff_sum_coloringPolynomial {n k d : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    (∑ c : Coloring n k, coloringPolynomial A c).coeff d =
      ∑ c : Coloring n k, (coloringPolynomial A c).coeff d := by
  let s : Finset (Coloring n k) := Finset.univ
  change (∑ c ∈ s, coloringPolynomial A c).coeff d =
    ∑ c ∈ s, (coloringPolynomial A c).coeff d
  induction s using Finset.induction_on with
  | empty => simp
  | @insert c s hc ih => simp [Finset.sum_insert hc, ih]

private lemma mixedDeterminantalPolynomial_coeff_dim {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    (mixedDeterminantalPolynomial A).coeff n = 1 := by
  rw [mixedDeterminantalPolynomial, Polynomial.coeff_smul,
    coeff_sum_coloringPolynomial]
  simp_rw [coeff_natDegree_coloringPolynomial]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  have hcard : Fintype.card (Coloring n k) ≠ 0 := by
    rw [coloring_card]
    exact pow_ne_zero _ (Nat.ne_of_gt hk)
  have hcardC : ((Fintype.card (Coloring n k) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hcard
  exact inv_mul_cancel₀ hcardC

/-- The exact mixed determinantal polynomial is monic whenever the color set
is nonempty. -/
theorem mixedDeterminantalPolynomial_monic {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    (mixedDeterminantalPolynomial A).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
  · rw [mixedDeterminantalPolynomial]
    apply le_trans (Polynomial.natDegree_smul_le _ _)
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro c _
    exact (coloringPolynomial_natDegree A c).le
  · exact mixedDeterminantalPolynomial_coeff_dim hk A

/-- Its degree is exactly the ambient dimension. -/
theorem mixedDeterminantalPolynomial_natDegree {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    (mixedDeterminantalPolynomial A).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [mixedDeterminantalPolynomial]
    apply le_trans (Polynomial.natDegree_smul_le _ _)
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro c _
    exact (coloringPolynomial_natDegree A c).le
  · rw [mixedDeterminantalPolynomial_coeff_dim hk A]
    exact one_ne_zero

/-- The coefficient below the leading term of every Hermitian zero-diagonal
leaf is zero.  This is the elementary trace part of the root-moment argument. -/
theorem coloringPolynomial_nextCoeff_eq_zero {n k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hzd : ∀ a, CommutatorTheorem.ZeroDiag (A a))
    (c : Coloring n k) :
    (coloringPolynomial A c).nextCoeff = 0 := by
  rw [coloringPolynomial]
  rw [Polynomial.Monic.nextCoeff_prod Finset.univ
    (fun a => (principalCompression (A a) c a).charpoly)
    (fun a _ => Matrix.charpoly_monic _)]
  apply Finset.sum_eq_zero
  intro a _
  have htrace : (principalCompression (A a) c a).trace = 0 := by
    rw [trace_principalCompression]
    apply Finset.sum_eq_zero
    intro i _
    exact hzd a i.1
  have hnext := Matrix.trace_eq_neg_charpoly_nextCoeff
    (principalCompression (A a) c a)
  rw [htrace] at hnext
  simpa using hnext

/-- Consequently the mixed determinantal average has zero next coefficient. -/
theorem mixedDeterminantalPolynomial_nextCoeff_eq_zero {n k : ℕ} (hk : 0 < k)
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hzd : ∀ a, CommutatorTheorem.ZeroDiag (A a)) :
    (mixedDeterminantalPolynomial A).nextCoeff = 0 := by
  by_cases hn : n = 0
  · subst n
    apply Polynomial.nextCoeff_eq_zero.mpr
    exact Or.inl (mixedDeterminantalPolynomial_natDegree hk A)
  · have hdeg := mixedDeterminantalPolynomial_natDegree hk A
    rw [Polynomial.nextCoeff_of_natDegree_pos (hdeg.symm ▸ Nat.pos_of_ne_zero hn)]
    rw [hdeg, mixedDeterminantalPolynomial, Polynomial.coeff_smul,
      coeff_sum_coloringPolynomial]
    have hleaf :
        ∀ c : Coloring n k, (coloringPolynomial A c).coeff (n - 1) = 0 := by
      intro c
      have hcdeg := coloringPolynomial_natDegree A c
      have hcpos : 0 < (coloringPolynomial A c).natDegree := by
        rw [hcdeg]
        exact Nat.pos_of_ne_zero hn
      have hnext := coloringPolynomial_nextCoeff_eq_zero hzd c
      rw [Polynomial.nextCoeff_of_natDegree_pos hcpos, hcdeg] at hnext
      exact hnext
    simp [hleaf]

end CommutatorTheorem.BTMixedDeterminantal
