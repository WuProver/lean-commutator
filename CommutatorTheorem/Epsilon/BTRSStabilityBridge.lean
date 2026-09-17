import CommutatorTheorem.Epsilon.BTRealStabilityClosure
import CommutatorTheorem.Epsilon.BTDeterminantStability

/-!
# Ravichandran--Srivastava stability bridge

This file connects the definite-determinant stability theorem to the minimal
stable-or-zero closure API.  It packages repeated coordinate differentiation
without making any assertion about the subsequent finite determinant
expansion into coloring polynomials.

Thus the only analytic hypothesis in this layer is the explicitly named
multivariate Gauss--Lucas/Hurwitz closure proposition.  All product,
complexification, differentiation, and diagonal-specialization steps below
are proved theorems.
-/

namespace CommutatorTheorem.BTRSStabilityBridge

open scoped BigOperators Polynomial
open Polynomial Finset
open CommutatorTheorem.BTRealStabilityClosure
open CommutatorTheorem.BTDeterminantStability

/-- A genuinely stable polynomial belongs to the stable-or-zero class. -/
theorem mvStableOrZero_of_complexStable {σ : Type*}
    {p : MvPolynomial σ ℂ} (hp : ComplexStable p) :
    MvStableOrZero p :=
  Or.inr hp

/-- Complexification transports the determinant file's real-stability
predicate into the stable-or-zero closure class. -/
theorem mvStableOrZero_map_of_realStable {σ : Type*}
    {p : MvPolynomial σ ℝ} (hp : RealStable p) :
    MvStableOrZero (MvPolynomial.map Complex.ofRealHom p) := by
  right
  intro z hz
  change MvPolynomial.eval₂ (RingHom.id ℂ) z
    (MvPolynomial.map Complex.ofRealHom p) ≠ 0
  rw [MvPolynomial.eval₂_map]
  have hof : (RingHom.id ℂ).comp Complex.ofRealHom = algebraMap ℝ ℂ := by
    ext x
    simp
  rw [hof]
  exact hp z hz

/-- Repeated coordinate partial differentiation, in the order recorded by a
list. -/
noncomputable def iteratedPDeriv {σ R : Type*} [CommSemiring R] :
    List σ → MvPolynomial σ R → MvPolynomial σ R
  | [], p => p
  | i :: is, p => iteratedPDeriv is (MvPolynomial.pderiv i p)

@[simp] theorem iteratedPDeriv_nil {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) :
    iteratedPDeriv [] p = p := rfl

@[simp] theorem iteratedPDeriv_cons {σ R : Type*} [CommSemiring R]
    (i : σ) (is : List σ) (p : MvPolynomial σ R) :
    iteratedPDeriv (i :: is) p =
      iteratedPDeriv is (MvPolynomial.pderiv i p) := rfl

/-- Repeated partial differentiation commutes with coefficient maps. -/
theorem iteratedPDeriv_map {σ R S : Type*}
    [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (is : List σ) (p : MvPolynomial σ R) :
    iteratedPDeriv is (MvPolynomial.map φ p) =
      MvPolynomial.map φ (iteratedPDeriv is p) := by
  induction is generalizing p with
  | nil => rfl
  | cons i is ih =>
      change iteratedPDeriv is
          (MvPolynomial.pderiv i (MvPolynomial.map φ p)) =
        MvPolynomial.map φ
          (iteratedPDeriv is (MvPolynomial.pderiv i p))
      rw [MvPolynomial.pderiv_map, ih]

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- The multivariate Gauss--Lucas/Hurwitz statement propagates stability
through any finite sequence of coordinate derivatives. -/
theorem mvStableOrZero_iteratedPDeriv
    (H : MultivariateGaussLucasHurwitz)
    {σ : Type} [Fintype σ] [DecidableEq σ]
    (is : List σ) (p : MvPolynomial σ ℂ) (hp : MvStableOrZero p) :
    MvStableOrZero (iteratedPDeriv is p) := by
  induction is generalizing p with
  | nil => exact hp
  | cons i is ih =>
      exact ih (MvPolynomial.pderiv i p)
        (mvStableOrZero_pderiv_of_gaussLucasHurwitz H p i hp)

/-- Product of the real definite-determinantal polynomials for a finite
Hermitian family. -/
noncomputable def realHermitianDetProduct
    {κ σ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype σ] [DecidableEq σ]
    (A : κ → Matrix σ σ ℂ) : MvPolynomial σ ℝ :=
  ∏ a : κ, realHermitianDetPoly (A a)

/-- Complexifying the real determinant product gives the product of the
complex determinant polynomials. -/
theorem map_realHermitianDetProduct
    {κ σ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype σ] [DecidableEq σ]
    (A : κ → Matrix σ σ ℂ) (hA : ∀ a, (A a).IsHermitian) :
    MvPolynomial.map Complex.ofRealHom (realHermitianDetProduct A) =
      ∏ a : κ, hermitianDetPoly (A a) := by
  simp only [realHermitianDetProduct, map_prod]
  apply Finset.prod_congr rfl
  intro a _
  exact map_realHermitianDetPoly (A a) (hA a)

/-- The complexification of a finite Hermitian determinant product is
stable. -/
theorem realHermitianDetProduct_complexification_stable
    {κ σ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype σ] [DecidableEq σ]
    (A : κ → Matrix σ σ ℂ) (hA : ∀ a, (A a).IsHermitian) :
    MvStableOrZero
      (MvPolynomial.map Complex.ofRealHom (realHermitianDetProduct A)) := by
  rw [map_realHermitianDetProduct A hA]
  apply mvStableOrZero_prod
  intro a _
  exact mvStableOrZero_of_complexStable
    (hermitianDetPoly_complexStable (A a) (hA a))

/-- Hence every finite coordinate-derivative sequence of the determinant
product remains stable-or-zero. -/
theorem iteratedPDeriv_realHermitianDetProduct_stable
    (H : MultivariateGaussLucasHurwitz)
    {κ σ : Type} [Fintype κ] [DecidableEq κ]
    [Fintype σ] [DecidableEq σ]
    (A : κ → Matrix σ σ ℂ) (hA : ∀ a, (A a).IsHermitian)
    (is : List σ) :
    MvStableOrZero
      (MvPolynomial.map Complex.ofRealHom
        (iteratedPDeriv is (realHermitianDetProduct A))) := by
  rw [← iteratedPDeriv_map]
  exact mvStableOrZero_iteratedPDeriv H is _
    (realHermitianDetProduct_complexification_stable A hA)

/-- Real diagonal specialization of a multivariate polynomial. -/
noncomputable def diagonalizeReal {σ : Type*}
    (p : MvPolynomial σ ℝ) : ℝ[X] :=
  MvPolynomial.eval₂ Polynomial.C (fun _ : σ ↦ Polynomial.X) p

/-- Complexification commutes with diagonal specialization. -/
theorem map_diagonalizeReal {σ : Type*} (p : MvPolynomial σ ℝ) :
    (diagonalizeReal p).map Complex.ofRealHom =
      diagonalize (MvPolynomial.map Complex.ofRealHom p) := by
  unfold diagonalizeReal diagonalize
  change Polynomial.mapRingHom Complex.ofRealHom
      (MvPolynomial.eval₂ Polynomial.C (fun _ : σ ↦ Polynomial.X) p) =
    MvPolynomial.eval₂ Polynomial.C (fun _ : σ ↦ Polynomial.X)
      (MvPolynomial.map Complex.ofRealHom p)
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_map]
  congr 1
  · ext x
    simp
  · funext i
    simp

/-- A nonzero stable-or-zero complexification has a real-rooted real
diagonal specialization. -/
theorem realRooted_diagonalizeReal_of_stable
    {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : MvStableOrZero (MvPolynomial.map Complex.ofRealHom p))
    (hdiag : diagonalize (MvPolynomial.map Complex.ofRealHom p) ≠ 0) :
    CommutatorTheorem.RealRooted (diagonalizeReal p) := by
  apply realRooted_of_map_upperStable
  rw [map_diagonalizeReal]
  rcases (MvStableOrZero.diagonalize hp) with hzero | hstable
  · exact (hdiag hzero).elim
  · exact hstable

/-- The complete formal stability conclusion for a repeated partial
derivative of a Hermitian determinant product.  Nonzeroness is kept explicit:
in the exact-MDP application it follows from the monic coloring expansion. -/
theorem realRooted_diagonal_iteratedPDeriv_detProduct
    (H : MultivariateGaussLucasHurwitz)
    {κ σ : Type} [Fintype κ] [DecidableEq κ]
    [Fintype σ] [DecidableEq σ]
    (A : κ → Matrix σ σ ℂ) (hA : ∀ a, (A a).IsHermitian)
    (is : List σ)
    (hne : diagonalize
      (MvPolynomial.map Complex.ofRealHom
        (iteratedPDeriv is (realHermitianDetProduct A))) ≠ 0) :
    CommutatorTheorem.RealRooted
      (diagonalizeReal (iteratedPDeriv is (realHermitianDetProduct A))) := by
  apply realRooted_diagonalizeReal_of_stable
  · exact iteratedPDeriv_realHermitianDetProduct_stable H A hA is
  · exact hne

end CommutatorTheorem.BTRSStabilityBridge
