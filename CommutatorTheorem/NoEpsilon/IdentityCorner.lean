import CommutatorTheorem.NoEpsilon.BlockAlgebra
import CommutatorTheorem.NoEpsilon.Riccati
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Combining the analytic fixed point and the block identity

This is a conditional construction from a supplied two-commutator decomposition.
The fixed point is proved to exist here; it is not assumed. A uniform bound on the
two supplied second factors, and the resulting product bound, are separate obligations.
-/

open scoped Matrix.Norms.L2Operator

namespace NoEpsilon

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An actual same-dimension single commutator from a supplied two-commutator sum. -/
theorem exists_identityCorner_commutator (A F D U K V T : Matrix ι ι ℂ)
    (hSum : A + D = ringCommutator U V + ringCommutator K T) :
    ∃ B C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ, identityCorner A F D = ringCommutator B C := by
  let b := ringCommutator U V - A
  let c := -D
  let d := A - U
  let e := riccatiConstant A F U K V T
  let lam := riccatiScale b c d e
  obtain ⟨Q, _, hQ⟩ := exists_riccati_fixedPoint_explicit b c d e
  have hLam : lam ≠ 0 := ne_of_gt (riccatiScale_pos b c d e)
  refine ⟨lowerShear Q * companionFirst (lam • 1 + U) K * lowerShearInverse Q,
    lowerShear Q * companionSecond A (lam • 1 + U) K V T Q * lowerShearInverse Q, ?_⟩
  apply identityCorner_eq_commutator_of_fixedPoint lam hLam A F D U K V T Q hSum
  simpa only [b, c, d, e, lam, quadratic] using hQ

end NoEpsilon
