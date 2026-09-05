import CommutatorTheorem.Epsilon.BTMDPSelection
import CommutatorTheorem.Epsilon.BTDirectProof

/-!
# From mixed-determinantal leaves to spectral matrix bounds

This file extracts the matrix consequence of an upper root bound for a real
mixed-determinantal leaf.  It also packages the exact common-compression
root-bound input which suffices for the four-Hermitian selection statement.
-/

open scoped BigOperators Polynomial MatrixOrder ComplexOrder

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
  Matrix.instL2OpNormedSpace Matrix.instL2OpNormedRing Matrix.instCStarRing

namespace CommutatorTheorem

open Polynomial Finset
open BTMixedDet
open BTMDPSelection

/-- Every Hermitian eigenvalue is a root of the real form of its characteristic
polynomial. -/
lemma isRoot_realCharpoly_eigenvalue
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (i : ι) :
    (realCharpoly M hM).IsRoot (hM.eigenvalues i) := by
  rw [Polynomial.IsRoot, realCharpoly, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

/-- The eigenvalues of every color compression occur among the roots of the
whole product leaf. -/
lemma isRoot_realColoringPolynomial_compression_eigenvalue
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k)
    (a : Fin k) (i : ColorFiber c a) :
    (realColoringPolynomial A hA c).IsRoot
      ((principalCompression_isHermitian (hA a) c a).eigenvalues i) := by
  rw [Polynomial.IsRoot, realColoringPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  exact isRoot_realCharpoly_eigenvalue _ _ i

/-- An upper root bound for a leaf bounds every eigenvalue of every matrix
compression represented by that leaf. -/
lemma eigenvalue_le_of_realColoringPolynomial_rootUpperBound
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) {x : ℝ}
    (hx : IsRootUpperBound (realColoringPolynomial A hA c) x)
    (a : Fin k) (i : ColorFiber c a) :
    (principalCompression_isHermitian (hA a) c a).eigenvalues i ≤ x := by
  exact hx _ (isRoot_realColoringPolynomial_compression_eigenvalue A hA c a i)

/-- Spectral form of the leaf-to-matrix bridge: every represented principal
compression lies below `x • I` in the Hermitian matrix order. -/
theorem principalCompression_le_of_realColoringPolynomial_rootUpperBound
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) {x : ℝ}
    (hx : IsRootUpperBound (realColoringPolynomial A hA c) x)
    (a : Fin k) :
    BTMixedDet.principalCompression (A a) c a ≤
      algebraMap ℝ (Matrix (ColorFiber c a) (ColorFiber c a) ℂ) x := by
  let M := BTMixedDet.principalCompression (A a) c a
  let hM : M.IsHermitian := principalCompression_isHermitian (hA a) c a
  apply (le_algebraMap_iff_spectrum_le hM.isSelfAdjoint).2
  intro y hy
  rw [hM.spectrum_real_eq_range_eigenvalues] at hy
  obtain ⟨i, rfl⟩ := hy
  exact eigenvalue_le_of_realColoringPolynomial_rootUpperBound A hA c hx a i

/-- Hermitian matrix order is preserved by taking the same submatrix on rows
and columns. -/
lemma submatrix_le_submatrix_of_le
    {m n : Type*}
    {A B : Matrix n n ℂ} (hAB : A ≤ B) (f : m → n) :
    A.submatrix f f ≤ B.submatrix f f := by
  rw [Matrix.le_iff] at hAB ⊢
  simpa only [Matrix.submatrix_sub] using (Matrix.PosSemidef.submatrix hAB f)

/-- If one color fiber is large enough, its leaf root bound yields a
prescribed-size principal submatrix with the same one-sided order bound. -/
theorem exists_submatrix_le_of_leaf_rootUpperBound_of_card_le
    {n k d : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k) {x : ℝ}
    (hx : IsRootUpperBound (realColoringPolynomial A hA c) x)
    (a : Fin k) (hcard : d ≤ Fintype.card (ColorFiber c a)) :
    ∃ f : Fin d → Fin n, Function.Injective f ∧
      (A a).submatrix f f ≤
        algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) x := by
  let e : Fin d ↪ ColorFiber c a :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hcard))
  let f : Fin d → Fin n := fun i ↦ (e i).1
  have hf : Function.Injective f := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hleaf := principalCompression_le_of_realColoringPolynomial_rootUpperBound
    A hA c hx a
  have hsub := submatrix_le_submatrix_of_le hleaf e
  have hleft :
      (BTMixedDet.principalCompression (A a) c a).submatrix e e =
        (A a).submatrix f f := by
    rfl
  have hright :
      (algebraMap ℝ (Matrix (ColorFiber c a) (ColorFiber c a) ℂ) x).submatrix e e =
        algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) x := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    rw [Matrix.submatrix_smul]
    change x • ((1 : Matrix (ColorFiber c a) (ColorFiber c a) ℂ).submatrix e e) =
      x • (1 : Matrix (Fin d) (Fin d) ℂ)
    rw [Matrix.submatrix_one e e.injective]
  refine ⟨f, hf, ?_⟩
  rwa [hleft, hright] at hsub

/-- A root upper bound for the real characteristic polynomial is exactly the
one-sided Hermitian matrix bound needed in restricted invertibility. -/
theorem matrix_le_of_realCharpoly_rootUpperBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) {x : ℝ}
    (hx : IsRootUpperBound (realCharpoly M hM) x) :
    M ≤ algebraMap ℝ (Matrix ι ι ℂ) x := by
  apply (le_algebraMap_iff_spectrum_le hM.isSelfAdjoint).2
  intro y hy
  rw [hM.spectrum_real_eq_range_eigenvalues] at hy
  obtain ⟨i, rfl⟩ := hy
  exact hx _ (isRoot_realCharpoly_eigenvalue M hM i)

/-- The precise common-compression root-bound output which suffices for the
four-Hermitian one-sided selection theorem.  This is stated as a proposition,
not an axiom: an MDP selection/root-shrinking argument can prove it directly. -/
def FourHermitianCommonRootSelection24 : Prop :=
  ∀ (m : ℕ) (M : Fin 4 → Matrix (Fin m) (Fin m) ℂ),
    ∀ (_hzd : ∀ j, ZeroDiag (M j)) (hM : ∀ j, (M j).IsHermitian)
      (_hnorm : ∀ j, ‖M j‖ ≤ 1),
    ∀ (t : ℝ), 0 < t → t < 1 →
      ∃ f : Fin ⌊(t ^ 2 / 24) * (m : ℝ)⌋₊ → Fin m,
        Function.Injective f ∧
        ∀ j : Fin 4,
          IsRootUpperBound
            (realCharpoly ((M j).submatrix f f) ((hM j).submatrix f)) t

/-- Once the MDP layer supplies common-compression characteristic-polynomial
root bounds, the published four-matrix order statement follows with no further
analytic input. -/
theorem fourHermitianUpperSelection24_of_commonRootSelection
    (hroot : FourHermitianCommonRootSelection24) :
    FourHermitianUpperSelection24 := by
  intro m M hzd hherm hnorm t ht ht1
  obtain ⟨f, hf, hroots⟩ := hroot m M hzd hherm hnorm t ht ht1
  refine ⟨f, hf, ?_⟩
  intro j
  exact matrix_le_of_realCharpoly_rootUpperBound
    ((M j).submatrix f f) ((hherm j).submatrix f) (hroots j)

end CommutatorTheorem
