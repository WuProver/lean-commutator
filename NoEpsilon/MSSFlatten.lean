import NoEpsilon.MSSExpectation

/-!
# Fresh-variable and flat mixed-characteristic operators

These algebraic identities compare nested fresh variables with a single finite
multivariate polynomial. All coefficient rings are arbitrary commutative rings.
-/

namespace NoEpsilon.MSSExpectation

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Move the first variable into the coefficient ring, leaving the other variables free. -/
noncomputable def splitHead (n : ℕ) : MvPolynomial (Fin (n + 1)) R →+*
    MvPolynomial (Fin n) (MvPolynomial Unit R) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (Fin.cases (MvPolynomial.C (MvPolynomial.X ())) MvPolynomial.X)

/-- Restrict to the first coordinate axis, retaining its polynomial variable. -/
noncomputable def headRestriction (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial Unit R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Fin.cases (MvPolynomial.X ()) (fun _ ↦ 0))

@[simp] theorem headRestriction_C (n : ℕ) (a : R) :
    headRestriction n (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [headRestriction]

@[simp] theorem headRestriction_X_zero (n : ℕ) :
    headRestriction n (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.X () := by simp [headRestriction]

@[simp] theorem headRestriction_X_succ (n : ℕ) (i : Fin n) :
    headRestriction n (MvPolynomial.X i.succ : MvPolynomial (Fin (n + 1)) R) = 0 := by
  simp [headRestriction]

@[simp] theorem splitHead_C (n : ℕ) (a : R) :
    splitHead n (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := by
  simp [splitHead]

@[simp] theorem splitHead_X_zero (n : ℕ) :
    splitHead n (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.C (MvPolynomial.X ()) := by simp [splitHead]

@[simp] theorem splitHead_X_succ (n : ℕ) (i : Fin n) :
    splitHead n (MvPolynomial.X i.succ : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.X i := by simp [splitHead]

/-- Differentiation in each remaining variable commutes with splitting off the first one. -/
theorem pderiv_splitHead (n : ℕ) (i : Fin n) (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.pderiv i (splitHead n p) = splitHead n (MvPolynomial.pderiv i.succ p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    induction j using Fin.cases with
    | zero => simp [hp]
    | succ j =>
      by_cases h : j = i
      · subst j; simp [hp]
      · simp [hp, h, Fin.succ_inj]

/-- Evaluating the remaining variables at zero gives restriction to the first axis. -/
theorem eval_zero_splitHead (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.eval (fun _ ↦ (0 : MvPolynomial Unit R)) (splitHead n p) =
      headRestriction n p := by
  have h : (MvPolynomial.eval (fun _ : Fin n ↦ (0 : MvPolynomial Unit R))).comp
      (splitHead n) = headRestriction (R := R) n := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i
      induction i using Fin.cases <;> simp [headRestriction]
  exact RingHom.congr_fun h p

/-- Restriction to the first axis commutes with differentiation in that coordinate. -/
theorem pderiv_headRestriction (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.pderiv () (headRestriction n p) =
      headRestriction n (MvPolynomial.pderiv 0 p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    induction j using Fin.cases <;> simp [hp]

/-- Evaluating the retained first coordinate too is simultaneous evaluation at zero. -/
theorem eval_zero_headRestriction (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.eval (fun _ ↦ (0 : R)) (headRestriction n p) =
      MvPolynomial.eval (fun _ ↦ (0 : R)) p := by
  have h : (MvPolynomial.eval (fun _ : Unit ↦ (0 : R))).comp (headRestriction n) =
      MvPolynomial.eval (fun _ : Fin (n + 1) ↦ (0 : R)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i
      induction i using Fin.cases <;> simp [headRestriction]
  exact RingHom.congr_fun h p

/-- A finite sequence of the literal MSS differential operators. -/
noncomputable def mixedDifference {σ : Type*} (xs : List σ)
    (p : MvPolynomial σ R) : MvPolynomial σ R :=
  xs.foldr (fun i q ↦ q - MvPolynomial.pderiv i q) p

/-- Splitting off the head commutes with every remaining differential operator. -/
theorem mixedDifference_splitHead (n : ℕ) (xs : List (Fin n))
    (p : MvPolynomial (Fin (n + 1)) R) :
    mixedDifference xs (splitHead n p) =
      splitHead n (mixedDifference (xs.map Fin.succ) p) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [mixedDifference, List.foldr_cons, List.map_cons] at ih ⊢
    rw [ih, pderiv_splitHead, map_sub]

/-- Exact recursion for the flat mixed-difference functional. -/
theorem differenceAtZero_splitHead (n : ℕ) (xs : List (Fin n))
    (p : MvPolynomial (Fin (n + 1)) R) :
    differenceAtZero R
      (MvPolynomial.eval (fun _ ↦ (0 : MvPolynomial Unit R))
        (mixedDifference xs (splitHead n p))) =
      MvPolynomial.eval (fun _ ↦ (0 : R))
        (mixedDifference (0 :: xs.map Fin.succ) p) := by
  rw [mixedDifference_splitHead, eval_zero_splitHead]
  change MvPolynomial.eval (fun _ ↦ (0 : R))
    (headRestriction n _ - MvPolynomial.pderiv () (headRestriction n _)) = _
  rw [pderiv_headRestriction, ← map_sub, eval_zero_headRestriction]
  rfl

/-- The determinant pencil with an arbitrary base matrix and one covariance per variable. -/
noncomputable def affinePencil {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (B : Matrix ι ι R) (A : Fin n → Matrix ι ι R) :
    MvPolynomial (Fin n) R :=
  (B.map MvPolynomial.C + ∑ i, (MvPolynomial.X i : MvPolynomial (Fin n) R) •
    (A i).map MvPolynomial.C).det

/-- The flat mixed determinant is exactly the product of the `1 - ∂ᵢ` operators
applied to the affine determinant pencil, followed by evaluation at zero. -/
noncomputable def flatMixedDet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (B : Matrix ι ι R) (A : Fin n → Matrix ι ι R) : R :=
  MvPolynomial.eval (fun _ ↦ (0 : R))
    (mixedDifference (List.finRange n) (affinePencil n B A))

/-- Splitting the first variable splits the affine determinant pencil with no change
to the matrix dimension. -/
theorem splitHead_affinePencil {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (B : Matrix ι ι R) (A : Fin (n + 1) → Matrix ι ι R) :
    splitHead n (affinePencil (n + 1) B A) =
      affinePencil n
        (B.map MvPolynomial.C + (MvPolynomial.X () : MvPolynomial Unit R) •
          (A 0).map MvPolynomial.C)
        (fun i ↦ (A i.succ).map MvPolynomial.C) := by
  unfold affinePencil
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, map_add, map_sum, map_mul]
  rw [Fin.sum_univ_succ]
  simp only [splitHead_C, splitHead_X_zero, splitHead_X_succ]
  ring

/-- A recursion theorem for the flat operator, proved through the differentiation
and specialization identities above. -/
theorem flatMixedDet_succ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (B : Matrix ι ι R) (A : Fin (n + 1) → Matrix ι ι R) :
    flatMixedDet (n + 1) B A =
      differenceAtZero R (flatMixedDet n
        (B.map MvPolynomial.C + (MvPolynomial.X () : MvPolynomial Unit R) •
          (A 0).map MvPolynomial.C)
        (fun i ↦ (A i.succ).map MvPolynomial.C)) := by
  unfold flatMixedDet
  rw [← splitHead_affinePencil, differenceAtZero_splitHead, List.finRange_succ]

/-- Nested fresh variables and a single multivariate pencil give the same mixed determinant. -/
theorem flatMixedDet_eq_nestedMixedDet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (R : Type*) [CommRing R] (B : Matrix ι ι R)
    (A : Fin n → Matrix ι ι R) :
    flatMixedDet n B A = nestedMixedDet n R B A := by
  induction n generalizing R with
  | zero =>
    simp only [flatMixedDet, List.finRange_zero, mixedDifference, List.foldr_nil,
      affinePencil, Finset.univ_eq_empty, Finset.sum_empty, add_zero, nestedMixedDet]
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.map_apply]
  | succ n ih =>
    rw [flatMixedDet_succ, ih]
    rfl

/-- The full finite mixed-characteristic formula in one multivariate polynomial.
This is the usual MSS identity, with arbitrary normalized finite independent laws. -/
theorem expected_determinant_eq_flatMixedDet {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (n : ℕ) (B : Matrix ι ι R) (u v : Fin n → Ω → ι → R)
    (p : Fin n → Ω → R) (hp : ∀ i, ∑ ω, p i ω = 1) :
    (∑ q : Fin n → Ω, (∏ i, p i (q i)) *
      (B - ∑ i, Matrix.vecMulVec (u i (q i)) (v i (q i))).det) =
      flatMixedDet n B (fun i ↦ ∑ ω, p i ω • Matrix.vecMulVec (u i ω) (v i ω)) := by
  rw [flatMixedDet_eq_nestedMixedDet]
  exact expected_determinant_eq_nestedMixedDet n R B u v p hp

end NoEpsilon.MSSExpectation
