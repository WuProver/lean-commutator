import NoEpsilon.MixedCharacteristic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The complete finite mixed-characteristic expectation identity

The mixed determinant is first expressed using nested polynomial coefficient rings.
This keeps each variable fresh by construction. Each recursive step applies the
literal operator `1 - ∂` and then evaluates that variable at zero.
-/

namespace NoEpsilon.MSSExpectation

open scoped BigOperators
open MixedCharacteristic

universe u

/-- Apply `1 - ∂` in a single fresh variable and then specialize it to zero. -/
noncomputable def differenceAtZero (R : Type u) [CommRing R] :
    MvPolynomial Unit R →ₗ[R] R where
  toFun f := MvPolynomial.eval (fun _ ↦ (0 : R)) (f - MvPolynomial.pderiv () f)
  map_add' f g := by simp only [map_add, map_sub]; ring
  map_smul' c f := by
    simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul,
      ← mul_sub, map_mul, MvPolynomial.eval_C, smul_eq_mul, RingHom.id_apply]

/-- A rank-one expectation equals the one-variable difference operator. -/
theorem differenceAtZero_pencil {R ι Ω : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (B : Matrix ι ι R) (u v : Ω → ι → R) (p : Ω → R) (hp : ∑ ω, p ω = 1) :
    differenceAtZero R
      (B.map MvPolynomial.C + (MvPolynomial.X () : MvPolynomial Unit R) •
        (∑ ω, p ω • Matrix.vecMulVec (u ω) (v ω)).map MvPolynomial.C).det =
      ∑ ω, p ω * (B - Matrix.vecMulVec (u ω) (v ω)).det :=
  (weighted_rank_one_mixed_characteristic_step () B u v p hp).symm

/-- A mixed determinant with one fresh nested polynomial variable for each covariance.
The base matrix is arbitrary, including singular matrices and polynomial matrices. -/
noncomputable def nestedMixedDet {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (n : ℕ) → (R : Type u) → [CommRing R] →
      Matrix ι ι R → (Fin n → Matrix ι ι R) → R
  | 0, _, _, B, _ => B.det
  | n + 1, R, _, B, A =>
      differenceAtZero R (nestedMixedDet n (MvPolynomial Unit R)
        (B.map MvPolynomial.C + (MvPolynomial.X () : MvPolynomial Unit R) •
          (A 0).map MvPolynomial.C)
        (fun i ↦ (A i.succ).map MvPolynomial.C))

/-- Split the first coordinate of a finite independent expectation. -/
theorem sum_independent_succ {R Ω : Type*} [CommSemiring R] [Fintype Ω]
    (n : ℕ) (p : Fin (n + 1) → Ω → R) (f : (Fin (n + 1) → Ω) → R) :
    (∑ q, (∏ i, p i (q i)) * f q) =
      ∑ ω, p 0 ω * ∑ q : Fin n → Ω,
        (∏ i, p i.succ (q i)) * f (Fin.cons ω q) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Ω)).sum_comp,
    Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.mul_sum, mul_assoc]

/-- Mapping a mean rank-one covariance into any coefficient ring commutes with
the finite weighted average. -/
theorem map_covariance {R S ι Ω : Type*} [CommRing R] [CommRing S]
    [Fintype Ω] (f : R →+* S) (u v : Ω → ι → R) (p : Ω → R) :
    (∑ ω, p ω • Matrix.vecMulVec (u ω) (v ω)).map f =
      ∑ ω, f (p ω) • Matrix.vecMulVec (fun i ↦ f (u ω i)) (fun i ↦ f (v ω i)) := by
  ext i j
  simp [Matrix.map_apply, Matrix.sum_apply, Matrix.vecMulVec]

/-- All finite independent rank-one expectations equal the iterated mixed determinant.
No positivity or stability premise is used; the equality holds in every commutative ring. -/
theorem expected_determinant_eq_nestedMixedDet {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (n : ℕ) (R : Type u) [CommRing R] (B : Matrix ι ι R)
    (u v : Fin n → Ω → ι → R) (p : Fin n → Ω → R)
    (hp : ∀ i, ∑ ω, p i ω = 1) :
    (∑ q : Fin n → Ω, (∏ i, p i (q i)) *
      (B - ∑ i, Matrix.vecMulVec (u i (q i)) (v i (q i))).det) =
      nestedMixedDet n R B (fun i ↦ ∑ ω, p i ω • Matrix.vecMulVec (u i ω) (v i ω)) := by
  induction n generalizing R with
  | zero => simp [nestedMixedDet]
  | succ n ih =>
    let A : Fin (n + 1) → Matrix ι ι R :=
      fun i ↦ ∑ ω, p i ω • Matrix.vecMulVec (u i ω) (v i ω)
    let C : R →+* MvPolynomial Unit R := MvPolynomial.C
    let B' : Matrix ι ι (MvPolynomial Unit R) :=
      B.map C + (MvPolynomial.X () : MvPolynomial Unit R) • (A 0).map C
    let u' : Fin n → Ω → ι → MvPolynomial Unit R := fun i ω j ↦ C (u i.succ ω j)
    let v' : Fin n → Ω → ι → MvPolynomial Unit R := fun i ω j ↦ C (v i.succ ω j)
    let p' : Fin n → Ω → MvPolynomial Unit R := fun i ω ↦ C (p i.succ ω)
    have hp' : ∀ i, ∑ ω, p' i ω = 1 := by
      intro i
      simp only [p', ← map_sum, hp, map_one]
    have hcov (i : Fin n) :
        (A i.succ).map C = ∑ ω, p' i ω • Matrix.vecMulVec (u' i ω) (v' i ω) :=
      map_covariance C (u i.succ) (v i.succ) (p i.succ)
    have hrec := ih (MvPolynomial Unit R) B' u' v' p' hp'
    have heq :
        nestedMixedDet n (MvPolynomial Unit R) B' (fun i ↦ (A i.succ).map C) =
          ∑ q : Fin n → Ω, C (∏ i, p i.succ (q i)) *
            (B' - ∑ i, Matrix.vecMulVec (u' i (q i)) (v' i (q i))).det := by
      simp_rw [hcov]
      simpa only [p', ← map_prod] using hrec.symm
    change _ = differenceAtZero R
      (nestedMixedDet n (MvPolynomial Unit R) B' (fun i ↦ (A i.succ).map C))
    rw [heq, map_sum]
    have hterm (q : Fin n → Ω) :
        B' - ∑ i, Matrix.vecMulVec (u' i (q i)) (v' i (q i)) =
          (B - ∑ i, Matrix.vecMulVec (u i.succ (q i)) (v i.succ (q i))).map C +
            (MvPolynomial.X () : MvPolynomial Unit R) • (A 0).map C := by
      ext i j
      simp [B', u', v', C, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.vecMulVec]
      ring
    simp_rw [hterm]
    simp only [C, ← MvPolynomial.smul_eq_C_mul]
    simp_rw [map_smul, smul_eq_mul]
    simp_rw [show A 0 = ∑ ω, p 0 ω • Matrix.vecMulVec (u 0 ω) (v 0 ω) from rfl]
    simp_rw [differenceAtZero_pencil _ (u 0) (v 0) (p 0) (hp 0)]
    rw [sum_independent_succ]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω _
    apply Finset.sum_congr rfl
    intro q _
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hB : B - (Matrix.vecMulVec (u 0 q) (v 0 q) +
        ∑ i, Matrix.vecMulVec (u i.succ (ω i)) (v i.succ (ω i))) =
        B - ∑ i, Matrix.vecMulVec (u i.succ (ω i)) (v i.succ (ω i)) -
          Matrix.vecMulVec (u 0 q) (v 0 q) := by abel
    rw [hB]
    ring

end NoEpsilon.MSSExpectation
