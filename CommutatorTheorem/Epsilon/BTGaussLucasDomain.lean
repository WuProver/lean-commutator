import CommutatorTheorem.Epsilon.BTStableLine
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.MvPolynomial.Funext

/-! # The product upper-half-plane domain used in multivariate Gauss--Lucas -/

namespace CommutatorTheorem.BTGaussLucasDomain

open Set
open CommutatorTheorem.BTRealStabilityClosure

/-- The Cartesian product of open upper half-planes. -/
def upperHalfPlaneProduct (sigma : Type*) : Set (sigma → ℂ) :=
  {z | ∀ i, InUpperHalfPlane (z i)}

@[simp] theorem mem_upperHalfPlaneProduct {sigma : Type*} {z : sigma → ℂ} :
    z ∈ upperHalfPlaneProduct sigma ↔ ∀ i, InUpperHalfPlane (z i) :=
  Iff.rfl

theorem isOpen_upperHalfPlaneProduct (sigma : Type*) [Finite sigma] :
    IsOpen (upperHalfPlaneProduct sigma) := by
  have hset : upperHalfPlaneProduct sigma =
      Set.univ.pi (fun _ : sigma ↦ {z : ℂ | 0 < z.im}) := by
    ext z
    simp [upperHalfPlaneProduct, InUpperHalfPlane]
  rw [hset]
  exact isOpen_set_pi Set.finite_univ fun _ _ ↦
    isOpen_lt continuous_const Complex.continuous_im

theorem convex_upperHalfPlaneProduct (sigma : Type*) [Fintype sigma] :
    Convex ℝ (upperHalfPlaneProduct sigma) := by
  have hset : upperHalfPlaneProduct sigma =
      Set.univ.pi (fun _ : sigma ↦ {z : ℂ | 0 < z.im}) := by
    ext z
    simp [upperHalfPlaneProduct, InUpperHalfPlane]
  rw [hset]
  apply convex_pi
  intro i _
  exact convex_halfSpace_gt Complex.imCLM.isLinear 0

theorem isPreconnected_upperHalfPlaneProduct (sigma : Type*) [Fintype sigma] :
    IsPreconnected (upperHalfPlaneProduct sigma) :=
  (convex_upperHalfPlaneProduct sigma).isPreconnected

theorem nonempty_upperHalfPlaneProduct (sigma : Type*) :
    (upperHalfPlaneProduct sigma).Nonempty := by
  refine ⟨fun _ ↦ Complex.I, ?_⟩
  simp [upperHalfPlaneProduct, InUpperHalfPlane]

/-- The open upper half-plane is infinite; the horizontal line `x + I`
already gives an injective infinite subset. -/
theorem infinite_upperHalfPlane :
    ({z : ℂ | InUpperHalfPlane z} : Set ℂ).Infinite := by
  let f : ℝ → ℂ := fun x ↦ (x : ℂ) + Complex.I
  have hf : Function.Injective f := by
    intro x y hxy
    have hre := congrArg Complex.re hxy
    simpa [f] using hre
  apply (Set.infinite_range_of_injective hf).mono
  rintro z ⟨x, rfl⟩
  simp [f, InUpperHalfPlane]

/-- An open subset of `ℂ` containing zero cannot stay inside the closed
lower half-plane. -/
theorem not_isOpen_of_zero_mem_of_im_nonpos {s : Set ℂ}
    (hzero : 0 ∈ s) (him : ∀ z ∈ s, z.im ≤ 0) : ¬ IsOpen s := by
  intro hs
  have hsnhds : s ∈ nhds (0 : ℂ) := hs.mem_nhds hzero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hsnhds
  let z : ℂ := (ε / 2 : ℝ) * Complex.I
  have hzball : z ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball]
    simp only [dist_zero_right, z, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hz := him z (hball hzball)
  have hzim : z.im = ε / 2 := by simp [z]
  rw [hzim] at hz
  linarith

/-- A multivariate complex polynomial vanishing throughout the product upper
half-plane is the zero polynomial. -/
theorem mvPolynomial_eq_zero_of_eval_zero_upper
    {sigma : Type*} {q : MvPolynomial sigma ℂ}
    (hq : ∀ z ∈ upperHalfPlaneProduct sigma,
      MvPolynomial.eval z q = 0) :
    q = 0 := by
  apply MvPolynomial.funext_set
    (fun _ : sigma ↦ {z : ℂ | InUpperHalfPlane z})
    (fun _ ↦ infinite_upperHalfPlane)
  intro z hz
  rw [hq z]
  · simp
  · intro i
    exact hz i (Set.mem_univ i)

end CommutatorTheorem.BTGaussLucasDomain
