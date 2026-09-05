import CommutatorTheorem.Epsilon.BTGaussLucasDomain
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Multivariate Gauss--Lucas--Hurwitz closure

This file closes the analytic step in the real-stability argument.  The
logarithmic directional derivative maps the product of upper half-planes to
the closed lower half-plane.  If it vanished at an interior point, the open
mapping theorem would force it to be constant; polynomial extensionality then
forces the directional derivative itself to be the zero polynomial.
-/

namespace CommutatorTheorem.BTGaussLucasHurwitz

open scoped BigOperators
open Set
open CommutatorTheorem.BTRealStabilityClosure
open CommutatorTheorem.BTStableLine
open CommutatorTheorem.BTGaussLucasDomain

/-- Nonnegative directional derivatives preserve multivariate upper-half-plane
stability, with the zero polynomial included as the degenerate case. -/
theorem multivariateGaussLucasHurwitz : MultivariateGaussLucasHurwitz := by
  intro σ inst p w hp hw
  letI : Fintype σ := inst
  rcases hp with rfl | hp
  · left
    simp [nonnegativeDirectionalDerivative]
  let q : MvPolynomial σ ℂ := nonnegativeDirectionalDerivative w p
  by_cases hq : q = 0
  · exact Or.inl hq
  right
  intro z hz hqz
  let U : Set (σ → ℂ) := upperHalfPlaneProduct σ
  let g : (σ → ℂ) → ℂ := fun x ↦
    MvPolynomial.eval x q / MvPolynomial.eval x p
  have hzU : z ∈ U := hz
  have hpU : ∀ x ∈ U, MvPolynomial.eval x p ≠ 0 := by
    intro x hx
    exact hp x hx
  have hgAnalytic : AnalyticOnNhd ℂ g U := by
    intro x hx
    exact
      ((AnalyticOnNhd.eval_mvPolynomial q) x (Set.mem_univ x)).div
        ((AnalyticOnNhd.eval_mvPolynomial p) x (Set.mem_univ x))
        (hpU x hx)
  have hUPreconnected : IsPreconnected U :=
    isPreconnected_upperHalfPlaneProduct σ
  have hUOpen : IsOpen U := isOpen_upperHalfPlaneProduct σ
  have hgLower : ∀ x ∈ U, (g x).im ≤ 0 := by
    intro x hx
    exact directional_logDerivative_im_nonpos hp x w hx hw
  have hgz : g z = 0 := by
    simp only [g, q, hqz, zero_div]
  rcases hgAnalytic.is_constant_or_isOpen hUPreconnected with
    ⟨c, hc⟩ | hgOpen
  · have hc0 : c = 0 := by
      rw [← hgz]
      exact (hc z hzU).symm
    have hqEval : ∀ x ∈ U, MvPolynomial.eval x q = 0 := by
      intro x hx
      have hgx : g x = 0 := by simpa [hc0] using hc x hx
      exact (div_eq_zero_iff.mp hgx).resolve_right (hpU x hx)
    exact hq (mvPolynomial_eq_zero_of_eval_zero_upper hqEval)
  · have hImageOpen : IsOpen (g '' U) := hgOpen U (Set.Subset.rfl) hUOpen
    have hzeroImage : (0 : ℂ) ∈ g '' U := ⟨z, hzU, hgz⟩
    exact (not_isOpen_of_zero_mem_of_im_nonpos hzeroImage (by
      rintro y ⟨x, hxU, rfl⟩
      exact hgLower x hxU)) hImageOpen

end CommutatorTheorem.BTGaussLucasHurwitz
