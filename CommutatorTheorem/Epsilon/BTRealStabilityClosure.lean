import CommutatorTheorem.Epsilon.BTFellPair
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Polynomial.GaussLucas

/-!
# Minimal finite-variable real-stability closure API

Mathlib has no bundled multivariate real-stability theory.  This file defines
the semantic upper-half-plane notion needed by the mixed-determinantal route,
proves its elementary product, renaming and diagonalization closures, and
isolates the sole remaining multivariate analytic closure statement as an
ordinary proposition.

The corresponding univariate derivative theorem is proved from Gauss--Lucas;
this records precisely why the multivariate statement is a Hurwitz-type
strengthening rather than determinant algebra.
-/

namespace CommutatorTheorem.BTRealStabilityClosure

open scoped BigOperators Polynomial ComplexConjugate
open Polynomial Finset Set

/-- A complex number lies in the open upper half-plane. -/
def InUpperHalfPlane (z : ℂ) : Prop := 0 < z.im

/-- A complex univariate polynomial has no zero in the open upper half-plane. -/
def UnivariateUpperStable (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, InUpperHalfPlane z → p.eval z ≠ 0

/-- The zero polynomial is included in the closure class, as is standard for
limits and derivatives of stable polynomials. -/
def UnivariateStableOrZero (p : ℂ[X]) : Prop :=
  p = 0 ∨ UnivariateUpperStable p

/-- The closed lower half-plane is convex over `ℝ`. -/
theorem convex_closedLowerHalfPlane :
    Convex ℝ {z : ℂ | z.im ≤ 0} :=
  convex_halfSpace_le Complex.imCLM.isLinear 0

/-- Gauss--Lucas gives the one-variable derivative closure without any extra
analytic input. -/
theorem UnivariateStableOrZero.derivative {p : ℂ[X]}
    (hp : UnivariateStableOrZero p) :
    UnivariateStableOrZero p.derivative := by
  rcases hp with rfl | hp
  · simp [UnivariateStableOrZero]
  by_cases hderiv : p.derivative = 0
  · exact Or.inl hderiv
  right
  intro z hz hzroot
  have hpdeg : 0 < p.natDegree := by
    by_contra hdeg
    have hdeg0 : p.natDegree = 0 := Nat.eq_zero_of_not_pos hdeg
    exact hderiv (Polynomial.derivative_of_natDegree_zero hdeg0)
  have hpdegree : 0 < p.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hpdeg
  have hrootDeriv : z ∈ p.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet_of_ne hderiv,
      Polynomial.coe_aeval_eq_eval]
    exact hzroot
  have hconvexRoot :=
    Polynomial.rootSet_derivative_subset_convexHull_rootSet hpdegree hrootDeriv
  have hrootsLower : p.rootSet ℂ ⊆ {w : ℂ | w.im ≤ 0} := by
    intro w hw
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hw
    exact le_of_not_gt fun hwpos ↦ hp w hwpos hw.2
  have hzLower : z.im ≤ 0 :=
    convexHull_min hrootsLower convex_closedLowerHalfPlane hconvexRoot
  exact (not_lt_of_ge hzLower) hz

/-- A finite-variable complex polynomial is stable when it is zero or is
nonvanishing whenever every variable lies in the upper half-plane. -/
def MvStableOrZero {σ : Type*} (p : MvPolynomial σ ℂ) : Prop :=
  p = 0 ∨ ∀ z : σ → ℂ, (∀ i, InUpperHalfPlane (z i)) →
    MvPolynomial.eval z p ≠ 0

theorem mvStableOrZero_zero {σ : Type*} :
    MvStableOrZero (0 : MvPolynomial σ ℂ) := Or.inl rfl

theorem mvStableOrZero_one {σ : Type*} :
    MvStableOrZero (1 : MvPolynomial σ ℂ) := by
  right
  simp

/-- Stability is closed under products. -/
theorem MvStableOrZero.mul {σ : Type*} {p q : MvPolynomial σ ℂ}
    (hp : MvStableOrZero p) (hq : MvStableOrZero q) :
    MvStableOrZero (p * q) := by
  rcases hp with rfl | hp
  · simp [mvStableOrZero_zero]
  rcases hq with rfl | hq
  · simp [mvStableOrZero_zero]
  right
  intro z hz
  rw [MvPolynomial.eval_mul]
  exact mul_ne_zero (hp z hz) (hq z hz)

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
/-- A finite product of stable-or-zero polynomials is stable-or-zero. -/
theorem mvStableOrZero_prod {ι σ : Type*} [DecidableEq ι]
    {s : Finset ι} {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ i ∈ s, MvStableOrZero (p i)) :
    MvStableOrZero (∏ i ∈ s, p i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (mvStableOrZero_one (σ := σ))
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hp i (by simp)).mul (ih fun j hj ↦ hp j (by simp [hj]))

/-- Identifying variables preserves stability; if the identification makes
the polynomial identically zero, the zero alternative applies. -/
theorem MvStableOrZero.rename {σ τ : Type*}
    {p : MvPolynomial σ ℂ} (hp : MvStableOrZero p) (f : σ → τ) :
    MvStableOrZero (MvPolynomial.rename f p) := by
  rcases hp with rfl | hp
  · simp [mvStableOrZero_zero]
  by_cases hzero : MvPolynomial.rename f p = 0
  · exact Or.inl hzero
  right
  intro z hz
  rw [MvPolynomial.eval_rename]
  exact hp (z ∘ f) fun i ↦ hz (f i)

/-- Diagonalize all variables to one polynomial variable. -/
noncomputable def diagonalize {σ : Type*} (p : MvPolynomial σ ℂ) : ℂ[X] :=
  MvPolynomial.eval₂ Polynomial.C (fun _ : σ ↦ Polynomial.X) p

theorem eval_diagonalize {σ : Type*} (p : MvPolynomial σ ℂ) (z : ℂ) :
    (diagonalize p).eval z = MvPolynomial.eval (fun _ ↦ z) p := by
  change Polynomial.evalRingHom z
      (MvPolynomial.eval₂ Polynomial.C (fun _ : σ ↦ Polynomial.X) p) =
    MvPolynomial.eval (fun _ ↦ z) p
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom z).comp Polynomial.C = RingHom.id ℂ := by
    ext x
    simp
  have hx : (⇑(Polynomial.evalRingHom z) ∘ fun _ : σ ↦ Polynomial.X) =
      (fun _ : σ ↦ z) := by
    funext i
    simp
  rw [hc, hx, MvPolynomial.eval₂_id]

/-- Multivariate stability descends to the diagonal univariate polynomial. -/
theorem MvStableOrZero.diagonalize {σ : Type*}
    {p : MvPolynomial σ ℂ} (hp : MvStableOrZero p) :
    UnivariateStableOrZero (diagonalize p) := by
  rcases hp with rfl | hp
  · exact Or.inl rfl
  right
  intro z hz
  rw [eval_diagonalize]
  exact hp (fun _ ↦ z) fun _ ↦ hz

/-- A nonnegative directional derivative of a multivariate polynomial. -/
noncomputable def nonnegativeDirectionalDerivative
    {σ : Type*} [Fintype σ] (w : σ → ℝ) (p : MvPolynomial σ ℂ) :
    MvPolynomial σ ℂ :=
  ∑ i : σ, MvPolynomial.C (w i : ℂ) * MvPolynomial.pderiv i p

/-- The sole multivariate analytic closure lemma still absent from Mathlib.
It is the finite-variable Gauss--Lucas/Hurwitz statement in exactly the
nonnegative directional form used by the Ravichandran--Srivastava proof. -/
def MultivariateGaussLucasHurwitz : Prop :=
  ∀ (σ : Type) (_ : Fintype σ) (p : MvPolynomial σ ℂ)
    (w : σ → ℝ),
    MvStableOrZero p → (∀ i, 0 ≤ w i) →
      MvStableOrZero (nonnegativeDirectionalDerivative w p)

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- The Hurwitz closure implies ordinary coordinate partial-derivative
closure. -/
theorem mvStableOrZero_pderiv_of_gaussLucasHurwitz
    (H : MultivariateGaussLucasHurwitz)
    {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℂ) (i : σ) (hp : MvStableOrZero p) :
    MvStableOrZero (MvPolynomial.pderiv i p) := by
  let w : σ → ℝ := fun j ↦ if j = i then 1 else 0
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w]
    split_ifs <;> norm_num
  have hstable := H σ inferInstance p w hp hw
  have hdir : nonnegativeDirectionalDerivative w p =
      MvPolynomial.pderiv i p := by
    classical
    simp only [nonnegativeDirectionalDerivative, w]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  rwa [hdir] at hstable

/-- If the complexification of a real polynomial is upper-half-plane
nonvanishing, then all of its complex roots are real, hence it splits over
`ℝ`. -/
theorem realRooted_of_map_upperStable {p : ℝ[X]}
    (hp : UnivariateUpperStable (p.map Complex.ofRealHom)) :
    CommutatorTheorem.RealRooted p := by
  have hp0 : p ≠ 0 := by
    intro hzero
    subst p
    exact hp Complex.I (by simp [InUpperHalfPlane]) (by simp)
  have hmap0 : p.map Complex.ofRealHom ≠ 0 :=
    fun h ↦ hp0 ((Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp h)
  apply Polynomial.Splits.of_splits_map_of_injective
    (i := Complex.ofRealHom) Complex.ofReal_injective (IsAlgClosed.splits _)
  intro z hz
  have hzroot : (p.map Complex.ofRealHom).IsRoot z :=
    (Polynomial.mem_roots hmap0).mp hz
  have hmapEq : p.map Complex.ofRealHom =
      p.map (algebraMap ℝ ℂ) := by
    congr 1
  have hzeval : Polynomial.aeval z p = 0 := by
    rw [← Polynomial.eval_map_algebraMap]
    rw [← hmapEq]
    exact hzroot
  have hnotPos : ¬ 0 < z.im := by
    intro hzpos
    exact hp z hzpos (by simpa [Polynomial.IsRoot] using hzroot)
  have hnotNeg : ¬ z.im < 0 := by
    intro hzneg
    have hconjPos : 0 < (starRingEnd ℂ z).im := by
      simp
      linarith
    apply hp (starRingEnd ℂ z) hconjPos
    rw [hmapEq, Polynomial.eval_map_algebraMap]
    rw [Polynomial.aeval_conj, hzeval]
    simp
  have hzim : z.im = 0 := by linarith
  refine ⟨z.re, ?_⟩
  apply Complex.ext
  · simp
  · simpa using hzim.symm

end CommutatorTheorem.BTRealStabilityClosure
