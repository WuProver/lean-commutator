import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-!
# Cancelling common factors of the rational MSS barrier

The reduced denominator retains real splitting and the numerator degree bound.
The evaluation identity holds over any target field, including the complex numbers.
-/

open Polynomial

namespace NoEpsilon.MSSReducedFraction

variable {F : Type*} [Field F]

theorem exists_reduced_fraction (g h : F[X]) (h0 : h ≠ 0) (hsplit : h.Splits)
    (hdeg : g.natDegree ≤ h.natDegree) :
    ∃ D G H : F[X], D ≠ 0 ∧ H ≠ 0 ∧
      g = D * G ∧ h = D * H ∧ IsCoprime G H ∧ H.Splits ∧
      G.natDegree ≤ H.natDegree := by
  classical
  letI := EuclideanDomain.gcdMonoid F[X]
  let D := GCDMonoid.gcd g h
  let G := g / D
  let H := h / D
  have hD : D ≠ 0 := gcd_ne_zero_of_right h0
  have hH : H ≠ 0 := right_div_gcd_ne_zero h0
  have hg : g = D * G :=
    (EuclideanDomain.mul_div_cancel' hD (GCDMonoid.gcd_dvd_left g h)).symm
  have hh : h = D * H :=
    (EuclideanDomain.mul_div_cancel' hD (GCDMonoid.gcd_dvd_right g h)).symm
  have hcop : IsCoprime G H := isCoprime_div_gcd_div_gcd h0
  have hs : H.Splits := hsplit.of_dvd h0 ⟨D, by simpa only [mul_comm] using hh⟩
  refine ⟨D, G, H, hD, hH, hg, hh, hcop, hs, ?_⟩
  by_cases hG : G = 0
  · simp [hG]
  · rw [hg, hh, natDegree_mul hD hG, natDegree_mul hD hH] at hdeg
    omega

/-- Cancellation preserves the rational function at every point where its original
denominator is nonzero, even after extending the coefficient field. -/
theorem eval₂_reduced_fraction {K : Type*} [Field K] (f : F →+* K)
    (g h D G H : F[X]) (hg : g = D * G) (hh : h = D * H) (x : K)
    (hx : h.eval₂ f x ≠ 0) :
    H.eval₂ f x ≠ 0 ∧
      G.eval₂ f x / H.eval₂ f x = g.eval₂ f x / h.eval₂ f x := by
  have hhx : h.eval₂ f x = D.eval₂ f x * H.eval₂ f x := by rw [hh, eval₂_mul]
  have hDx : D.eval₂ f x ≠ 0 := (mul_ne_zero_iff.mp (hhx ▸ hx)).1
  have hHx : H.eval₂ f x ≠ 0 := (mul_ne_zero_iff.mp (hhx ▸ hx)).2
  refine ⟨hHx, ?_⟩
  rw [hg, hh, eval₂_mul, eval₂_mul]
  field_simp

theorem eval_reduced_fraction (g h D G H : F[X]) (hg : g = D * G) (hh : h = D * H)
    (x : F) (hx : h.eval x ≠ 0) :
    H.eval x ≠ 0 ∧ G.eval x / H.eval x = g.eval x / h.eval x := by
  simpa only [eval₂_id] using eval₂_reduced_fraction (RingHom.id F) g h D G H hg hh x hx

end NoEpsilon.MSSReducedFraction
