import CommutatorTheorem.NoEpsilon.MSSCrossBarrier
import CommutatorTheorem.NoEpsilon.MSSBarrierAlgebra

/-!
# The complete quantitative MSS barrier step

This is Lemma 5.10 of Marcus--Spielman--Srivastava, with the above-roots
conclusion included. Every analytic input is proved in the imported modules.
-/

namespace NoEpsilon.MSSBarrierStep

open NoEpsilon.MSSBarrier NoEpsilon.MSSCrossBarrier NoEpsilon.MSSBarrierAlgebra

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- If the old barrier in coordinate `j` is at most `1 - 1/δ`, applying
`1 - ∂ⱼ` and moving by `δ` in coordinate `j` keeps the point above all roots
and does not increase any coordinate barrier. -/
theorem quantitative_barrier_step {p : MvPolynomial σ ℝ} (hp : RealStable p)
    {z : σ → ℝ} (hz : AboveRoots p z) (j : σ) (δ : ℝ) (hδ : 0 < δ)
    (hbound : barrier p j z ≤ 1 - 1 / δ) :
    AboveRoots (p - MvPolynomial.pderiv j p) (coordinateShift z j δ) ∧
      ∀ i : σ, barrier (p - MvPolynomial.pderiv j p) i (coordinateShift z j δ) ≤
        barrier p i z := by
  have hle := le_coordinateShift z j hδ.le
  have hinv : 0 < 1 / δ := one_div_pos.mpr hδ
  have hlt : barrier p j z < 1 := by linarith
  refine ⟨(aboveRoots_sub_pderiv hp hz j hlt).mono hle, ?_⟩
  intro i
  have hmono : barrier p j (coordinateShift z j δ) ≤ barrier p j z :=
    barrier_antitone_aboveRoots hp hz hle j
  have hneq : barrier p j (coordinateShift z j δ) ≠ 1 :=
    (hmono.trans_lt hlt).ne
  have hzero : MvPolynomial.eval (coordinateShift z j δ) p ≠ 0 :=
    (hz _ hle).ne'
  rw [barrier_sub_pderiv p i j _ hzero hneq]
  exact scalar_shift δ _ _ _ _ _ hδ hmono hbound
    (mixedBarrierDerivative_nonpos hp _ hzero i j)
    (barrier_coordinate_tangent hp hz i j δ hδ.le)

end NoEpsilon.MSSBarrierStep
