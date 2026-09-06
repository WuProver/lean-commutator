import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.NoncommRing

/-!
# Algebra for an identity-corner commutator

The identities in this file are valid over an arbitrary ring. The indices of the block
matrices are sums, so a target with two blocks indexed by `ι` stays indexed by `ι ⊕ ι`.
No analytic existence assertion is postulated: the final theorem states explicitly the
two-commutator identity and the Riccati equation that its algebraic construction requires.
-/

namespace NoEpsilon

/-- The additive ring commutator, also applicable to square matrices. -/
def ringCommutator {R : Type*} [Ring R] (X Y : R) : R := X * Y - Y * X

section RingConjugation

variable {R : Type*} [Ring R]

theorem conjugation_mul (S S' B C : R) (hInverse : S' * S = 1) :
    (S * B * S') * (S * C * S') = S * (B * C) * S' := by
  calc
    (S * B * S') * (S * C * S') = S * B * (S' * S) * C * S' := by noncomm_ring
    _ = S * (B * C) * S' := by rw [hInverse]; noncomm_ring

theorem conjugation_commutator (S S' B C : R) (hInverse : S' * S = 1) :
    ringCommutator (S * B * S') (S * C * S') = S * ringCommutator B C * S' := by
  simp only [ringCommutator, conjugation_mul S S' B C hInverse,
    conjugation_mul S S' C B hInverse]
  noncomm_ring

end RingConjugation

section ScalarShift

variable {𝕜 R : Type*} [CommRing 𝕜] [Ring R] [Algebra 𝕜 R]

/-- Adding a scalar multiple of the identity does not change an additive commutator. -/
theorem ringCommutator_scalar_shift (lam : 𝕜) (U X : R) :
    ringCommutator (lam • 1 + U) X = ringCommutator U X := by
  simp only [ringCommutator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]
  abel

end ScalarShift

section MatrixBlocks

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The lower triangular block shear used to normalize the target. -/
def lowerShear (Q : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks 1 0 Q 1

/-- An explicit inverse; no matrix invertibility hypothesis is needed. -/
def lowerShearInverse (Q : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks 1 0 (-Q) 1

/-- The arbitrary target whose upper-right block is the identity. -/
def identityCorner (A F D : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks A 1 F D

/-- The first factor before the lower triangular similarity. -/
def companionFirst (U K : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks U 1 K 0

/-- The second factor before the lower triangular similarity. -/
def companionSecond (A U K V T Q : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks V T (A + Q - ringCommutator U V + T * K) (V + 1 - U * T)

/-- The constant term in the lower-left block, before subtracting `Q * U`. -/
def companionDefect (A U K V T : Matrix ι ι R) : Matrix ι ι R :=
  ringCommutator K V + (ringCommutator U V - A) * U - K + ringCommutator U (T * K)

theorem lowerShear_mul_inverse (Q : Matrix ι ι R) :
    lowerShear Q * lowerShearInverse Q = 1 := by
  simp [lowerShear, lowerShearInverse, Matrix.fromBlocks_multiply]

theorem lowerShear_inverse_mul (Q : Matrix ι ι R) :
    lowerShearInverse Q * lowerShear Q = 1 := by
  simp [lowerShear, lowerShearInverse, Matrix.fromBlocks_multiply]

omit [Fintype ι] [DecidableEq ι] in
private theorem fromBlocks_sub_blocks (A B C D A' B' C' D' : Matrix ι ι R) :
    Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D' =
      Matrix.fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i j
  cases i <;> cases j <;> rfl

/-- All four blocks of the conjugated target, with multiplication order made explicit. -/
theorem identityCorner_shear (A F D Q : Matrix ι ι R) :
    lowerShearInverse Q * identityCorner A F D * lowerShear Q =
      Matrix.fromBlocks (A + Q) 1 (F + D * Q - Q * A - Q * Q) (D - Q) := by
  simp only [lowerShearInverse, identityCorner, lowerShear, Matrix.fromBlocks_multiply]
  apply Matrix.fromBlocks_inj.mpr
  constructor
  · noncomm_ring
  constructor
  · noncomm_ring
  constructor <;> noncomm_ring

/-- The four blocks of the companion commutator, without any hypothesis on the target. -/
theorem companion_commutator_blocks (A U K V T Q : Matrix ι ι R) :
    ringCommutator (companionFirst U K) (companionSecond A U K V T Q) =
      Matrix.fromBlocks (A + Q) 1 (companionDefect A U K V T - Q * U)
        (ringCommutator U V + ringCommutator K T - A - Q) := by
  simp only [ringCommutator, companionFirst, companionSecond, Matrix.fromBlocks_multiply,
    fromBlocks_sub_blocks, companionDefect]
  apply Matrix.fromBlocks_inj.mpr
  constructor
  · noncomm_ring
  constructor
  · noncomm_ring
  constructor <;> noncomm_ring [ringCommutator]

/-- Using the two-commutator identity fixes the lower-right block of the target. -/
theorem companion_commutator_of_sum (A D U K V T Q : Matrix ι ι R)
    (hSum : A + D = ringCommutator U V + ringCommutator K T) :
    ringCommutator (companionFirst U K) (companionSecond A U K V T Q) =
      Matrix.fromBlocks (A + Q) 1 (companionDefect A U K V T - Q * U) (D - Q) := by
  rw [companion_commutator_blocks, ← hSum]
  congr 1
  noncomm_ring

/-- The Riccati equation gives the full target after conjugation, not just its diagonal. -/
theorem companion_commutator_of_riccati (A F D U K V T Q : Matrix ι ι R)
    (hSum : A + D = ringCommutator U V + ringCommutator K T)
    (hRiccati : Q * Q - D * Q + Q * (A - U) + companionDefect A U K V T - F = 0) :
    ringCommutator (companionFirst U K) (companionSecond A U K V T Q) =
      lowerShearInverse Q * identityCorner A F D * lowerShear Q := by
  rw [companion_commutator_of_sum A D U K V T Q hSum, identityCorner_shear]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨rfl, rfl, ?_, rfl⟩
  apply sub_eq_zero.mp
  calc
    (companionDefect A U K V T - Q * U) - (F + D * Q - Q * A - Q * Q) =
        Q * Q - D * Q + Q * (A - U) + companionDefect A U K V T - F := by
      noncomm_ring
    _ = 0 := hRiccati

/-- Explicit single-commutator factors in the same sum-indexed matrix ring as the target. -/
theorem identityCorner_eq_commutator (A F D U K V T Q : Matrix ι ι R)
    (hSum : A + D = ringCommutator U V + ringCommutator K T)
    (hRiccati : Q * Q - D * Q + Q * (A - U) + companionDefect A U K V T - F = 0) :
    identityCorner A F D =
      ringCommutator
        (lowerShear Q * companionFirst U K * lowerShearInverse Q)
        (lowerShear Q * companionSecond A U K V T Q * lowerShearInverse Q) := by
  symm
  rw [conjugation_commutator _ _ _ _ (lowerShear_inverse_mul Q),
    companion_commutator_of_riccati A F D U K V T Q hSum hRiccati]
  calc
    lowerShear Q * (lowerShearInverse Q * identityCorner A F D * lowerShear Q) *
        lowerShearInverse Q =
      (lowerShear Q * lowerShearInverse Q) * identityCorner A F D *
        (lowerShear Q * lowerShearInverse Q) := by noncomm_ring
    _ = identityCorner A F D := by simp only [lowerShear_mul_inverse, one_mul, mul_one]

section ScalarFixedPoint

variable {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 R]

/-- The term denoted by `D₁` in the scalar-shifted fixed-point equation. -/
def riccatiConstant (A F U K V T : Matrix ι ι R) : Matrix ι ι R :=
  ringCommutator K V + (ringCommutator U V - A) * U - K +
    ringCommutator U (T * K) - F

theorem companionDefect_scalar_shift (lam : 𝕜) (A F U K V T : Matrix ι ι R) :
    companionDefect A (lam • 1 + U) K V T =
      lam • (ringCommutator U V - A) + riccatiConstant A F U K V T + F := by
  simp only [companionDefect, ringCommutator_scalar_shift, riccatiConstant,
    mul_add, mul_smul_comm, mul_one]
  abel

/-- A Banach fixed point supplies the exact Riccati equation used by the block algebra. -/
theorem riccati_of_scalar_fixedPoint (lam : 𝕜) (hLam : lam ≠ 0)
    (A F D U K V T Q : Matrix ι ι R)
    (hFixed : Q = ringCommutator U V - A +
      lam⁻¹ • (Q * Q + (-D) * Q + Q * (A - U) + riccatiConstant A F U K V T)) :
    Q * Q - D * Q + Q * (A - (lam • 1 + U)) +
      companionDefect A (lam • 1 + U) K V T - F = 0 := by
  have hScaled : lam • Q = lam • (ringCommutator U V - A) +
      (Q * Q + (-D) * Q + Q * (A - U) + riccatiConstant A F U K V T) := by
    have h := congrArg (fun X : Matrix ι ι R ↦ lam • X) hFixed
    simpa only [smul_add, smul_smul, mul_inv_cancel₀ hLam, one_smul] using h
  calc
    Q * Q - D * Q + Q * (A - (lam • 1 + U)) +
        companionDefect A (lam • 1 + U) K V T - F =
      (lam • (ringCommutator U V - A) +
        (Q * Q + (-D) * Q + Q * (A - U) + riccatiConstant A F U K V T)) - lam • Q := by
      rw [companionDefect_scalar_shift lam A F U K V T]
      simp only [mul_sub, mul_add, mul_smul_comm, mul_one]
      noncomm_ring
    _ = 0 := by rw [← hScaled]; exact sub_self _

/-- The scalar fixed-point formulation yields the same-dimension explicit factorization. -/
theorem identityCorner_eq_commutator_of_fixedPoint (lam : 𝕜) (hLam : lam ≠ 0)
    (A F D U K V T Q : Matrix ι ι R)
    (hSum : A + D = ringCommutator U V + ringCommutator K T)
    (hFixed : Q = ringCommutator U V - A +
      lam⁻¹ • (Q * Q + (-D) * Q + Q * (A - U) + riccatiConstant A F U K V T)) :
    identityCorner A F D =
      ringCommutator
        (lowerShear Q * companionFirst (lam • 1 + U) K * lowerShearInverse Q)
        (lowerShear Q * companionSecond A (lam • 1 + U) K V T Q * lowerShearInverse Q) := by
  apply identityCorner_eq_commutator
  · simpa only [ringCommutator_scalar_shift] using hSum
  · exact riccati_of_scalar_fixedPoint lam hLam A F D U K V T Q hFixed

end ScalarFixedPoint

end MatrixBlocks

end NoEpsilon
