import CommutatorTheorem.Epsilon.BTRSExactMDPHarness
import CommutatorTheorem.Epsilon.BTHermitianDetPDeriv

/-!
# Boundary audit for the exact-MDP base expansion

The base-expansion harness must assume that the color set is nonempty.  With
zero colors and one coordinate, its determinant product is the empty product
`1`, while the exact MDP is the average of an empty coloring space and hence
is `0`.  The theorem below records the obstruction inside Lean.
-/

namespace CommutatorTheorem.BTRSBaseExpansion

open scoped BigOperators Polynomial
open Polynomial Finset
open CommutatorTheorem
open CommutatorTheorem.BTMixedDet
open CommutatorTheorem.BTMDPSelection
open CommutatorTheorem.BTDeterminantStability
open CommutatorTheorem.BTRealStabilityClosure
open CommutatorTheorem.BTRSStabilityBridge
open CommutatorTheorem.BTRSExactMDPHarness
open CommutatorTheorem.BTHermitianDetPDeriv
open CommutatorTheorem.BTMDPDeletionIdentity

/-- Dimension-uniform real coordinate-deletion formula, phrased using the
ordered embedding used by the exact-MDP deletion API. -/
theorem pderiv_realHermitianDetPoly_fin_delete
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.IsHermitian) (i : Fin N) :
    MvPolynomial.pderiv i (realHermitianDetPoly A) =
      MvPolynomial.rename (finDeleteOrderEmb i)
        (realHermitianDetPoly
          (A.submatrix (finDeleteOrderEmb i) (finDeleteOrderEmb i))) := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
      simpa [finDeleteOrderEmb_eq_succAbove] using
        pderiv_realHermitianDetPoly_fin_succ A hA i

/-- Renaming variables does not change the all-equal-variable
specialization. -/
theorem diagonalizeReal_rename {σ τ : Type*} (f : σ → τ)
    (p : MvPolynomial σ ℝ) :
    diagonalizeReal (MvPolynomial.rename f p) = diagonalizeReal p := by
  unfold diagonalizeReal
  rw [MvPolynomial.eval₂_rename]
  rfl

private theorem repeatedCoordinateList_zero
    (sigma : Type*) [Fintype sigma] [DecidableEq sigma] :
    repeatedCoordinateList sigma 0 = [] := by
  unfold repeatedCoordinateList
  rw [List.flatMap_eq_nil_iff]
  simp

/-! ## Repeated differentiation of a product of multiaffine factors -/

noncomputable def repeatedPDeriv {sigma : Type*} (x : sigma) (r : ℕ)
    (p : MvPolynomial sigma ℂ) : MvPolynomial sigma ℂ :=
  iteratedPDeriv (List.replicate r x) p

@[simp] theorem repeatedPDeriv_zero {sigma : Type*} (x : sigma)
    (p : MvPolynomial sigma ℂ) : repeatedPDeriv x 0 p = p := rfl

theorem repeatedPDeriv_succ {sigma : Type*} (x : sigma) (r : ℕ)
    (p : MvPolynomial sigma ℂ) :
    repeatedPDeriv x (r + 1) p =
      repeatedPDeriv x r (MvPolynomial.pderiv x p) := by
  rfl

theorem repeatedPDeriv_succ_right {sigma : Type*} (x : sigma) (r : ℕ)
    (p : MvPolynomial sigma ℂ) :
    repeatedPDeriv x (r + 1) p =
      MvPolynomial.pderiv x (repeatedPDeriv x r p) := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
      rw [show r + 1 + 1 = (r + 1) + 1 by omega,
        repeatedPDeriv_succ, ih, repeatedPDeriv_succ]

theorem repeatedPDeriv_add {sigma : Type*} (x : sigma) (r : ℕ)
    (p q : MvPolynomial sigma ℂ) :
    repeatedPDeriv x r (p + q) =
      repeatedPDeriv x r p + repeatedPDeriv x r q := by
  induction r generalizing p q with
  | zero => rfl
  | succ r ih =>
      rw [repeatedPDeriv_succ, map_add, ih,
        ← repeatedPDeriv_succ, ← repeatedPDeriv_succ]

theorem repeatedPDeriv_const_mul {sigma : Type*} (x : sigma) (r : ℕ)
    (a : ℂ) (p : MvPolynomial sigma ℂ) :
    repeatedPDeriv x r (MvPolynomial.C a * p) =
      MvPolynomial.C a * repeatedPDeriv x r p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
      rw [repeatedPDeriv_succ, MvPolynomial.pderiv_C_mul, ih,
        ← repeatedPDeriv_succ]

theorem repeatedPDeriv_mul_of_left_derivative_zero
    {sigma : Type*} (x : sigma) (r : ℕ)
    (p q : MvPolynomial sigma ℂ)
    (hp : MvPolynomial.pderiv x p = 0) :
    repeatedPDeriv x r (p * q) = p * repeatedPDeriv x r q := by
  induction r generalizing q with
  | zero => rfl
  | succ r ih =>
      rw [repeatedPDeriv_succ, MvPolynomial.pderiv_mul, hp,
        zero_mul, zero_add, ih, ← repeatedPDeriv_succ]

/-- Higher Leibniz rule when the left factor is affine in `x`. -/
theorem repeatedPDeriv_succ_mul_of_left_multiaffine
    {sigma : Type*} (x : sigma) (r : ℕ)
    (p q : MvPolynomial sigma ℂ)
    (hp : MvPolynomial.pderiv x (MvPolynomial.pderiv x p) = 0) :
    repeatedPDeriv x (r + 1) (p * q) =
      p * repeatedPDeriv x (r + 1) q +
        (r + 1 : ℂ) •
          (MvPolynomial.pderiv x p * repeatedPDeriv x r q) := by
  induction r generalizing q with
  | zero =>
      rw [repeatedPDeriv_succ, repeatedPDeriv_zero,
        MvPolynomial.pderiv_mul, repeatedPDeriv_succ,
        repeatedPDeriv_zero]
      simp [add_comm]
  | succ r ih =>
      rw [show r + 1 + 1 = (r + 1) + 1 by omega,
        repeatedPDeriv_succ, MvPolynomial.pderiv_mul,
        repeatedPDeriv_add]
      rw [repeatedPDeriv_mul_of_left_derivative_zero x (r + 1) _ _ hp]
      rw [ih]
      rw [← repeatedPDeriv_succ x (r + 1) q,
        ← repeatedPDeriv_succ x r q]
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      module

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
private theorem pderiv_prod_eq_zero_of_derivatives_zero
    {sigma iota : Type*} [Fintype iota] [DecidableEq iota]
    (x : sigma) (f : iota → MvPolynomial sigma ℂ)
    (hf : ∀ i, MvPolynomial.pderiv x (f i) = 0) :
    MvPolynomial.pderiv x (∏ i : iota, f i) = 0 := by
  rw [show (∏ i : iota, f i) = ∏ i ∈ (Finset.univ : Finset iota), f i by rfl]
  rw [pderiv_prod_finset]
  apply Finset.sum_eq_zero
  intro i _
  simp [hf i]

/-- Differentiating once for every multiaffine factor forces every factor to
be differentiated, with the expected factorial multiplicity. -/
theorem repeatedPDeriv_prod_fin_full
    {sigma : Type*} (x : sigma) (k : ℕ)
    (f : Fin k → MvPolynomial sigma ℂ)
    (hf : ∀ a, MvPolynomial.pderiv x (MvPolynomial.pderiv x (f a)) = 0) :
    repeatedPDeriv x k (∏ a : Fin k, f a) =
      MvPolynomial.C (k.factorial : ℂ) *
        ∏ a : Fin k, MvPolynomial.pderiv x (f a) := by
  induction k with
  | zero => simp [repeatedPDeriv]
  | succ k ih =>
      let g : Fin k → MvPolynomial sigma ℂ := fun a ↦ f a.succ
      have hg : ∀ a, MvPolynomial.pderiv x
          (MvPolynomial.pderiv x (g a)) = 0 := fun a ↦ hf a.succ
      have hfull := ih g hg
      have hmore : repeatedPDeriv x (k + 1) (∏ a : Fin k, g a) = 0 := by
        rw [repeatedPDeriv_succ_right, hfull]
        rw [MvPolynomial.pderiv_C_mul]
        rw [pderiv_prod_eq_zero_of_derivatives_zero]
        · simp
        · exact hg
      rw [Fin.prod_univ_succ]
      rw [repeatedPDeriv_succ_mul_of_left_multiaffine x k]
      · rw [hmore, mul_zero, zero_add, hfull]
        rw [Fin.prod_univ_succ, Nat.factorial_succ]
        push_cast
        rw [Algebra.smul_def]
        dsimp [g]
        simp only [map_add, map_mul, map_one]
        ring
      · exact hf 0

/-- The full `k`-fold derivative in one coordinate of a product of `k`
Hermitian determinant polynomials deletes that coordinate from every factor.
The multiplicity is exactly `k!`. -/
theorem repeatedPDeriv_hermitianDetProduct_full_coordinate
    {n k : ℕ}
    (A : Fin k → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) :
    repeatedPDeriv i k (∏ a : Fin k, hermitianDetPoly (A a)) =
      MvPolynomial.C (k.factorial : ℂ) *
        MvPolynomial.rename i.succAbove
          (∏ a : Fin k,
            hermitianDetPoly ((A a).submatrix i.succAbove i.succAbove)) := by
  rw [repeatedPDeriv_prod_fin_full]
  · simp_rw [pderiv_hermitianDetPoly_fin_succ]
    rw [map_prod]
  · exact fun a ↦ pderiv_self_hermitianDetPoly_fin_succ (A a) i

theorem count_repeatedCoordinateList
    (sigma : Type*) [Fintype sigma] [DecidableEq sigma]
    (x : sigma) (r : ℕ) :
    List.count x (repeatedCoordinateList sigma r) = r := by
  unfold repeatedCoordinateList
  rw [List.count_flatMap]
  simp [Function.comp_def, List.count_replicate]

theorem coordinateList_deletion_perm {n k : ℕ} (hk : 0 < k)
    (i : Fin (n + 1)) :
    (i :: repeatedCoordinateList (Fin (n + 1)) (k - 1)).Perm
      (List.replicate k i ++
        List.map i.succAbove (repeatedCoordinateList (Fin n) (k - 1))) := by
  classical
  rw [List.perm_iff_count]
  intro x
  rw [List.count_cons, List.count_append]
  by_cases hxi : x = i
  · subst x
    rw [count_repeatedCoordinateList]
    have hmap : List.count i
        (List.map i.succAbove
          (repeatedCoordinateList (Fin n) (k - 1))) = 0 := by
      apply List.count_eq_zero.mpr
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨y, _, hy⟩ := hmem
      exact Fin.succAbove_ne i y hy
    rw [hmap, add_zero]
    simp
    omega
  · obtain ⟨y, hy⟩ : ∃ y : Fin n, i.succAbove y = x := by
      exact Fin.exists_succAbove_eq_iff.mpr hxi
    rw [← hy]
    rw [List.count_map_of_injective _ i.succAbove
      Fin.succAbove_right_injective]
    rw [count_repeatedCoordinateList]
    have hne : i ≠ i.succAbove y := Fin.ne_succAbove i y
    simpa [List.count_replicate, hne] using
      (count_repeatedCoordinateList (Fin n) y (k - 1)).symm

theorem iteratedPDeriv_perm {sigma R : Type*} [CommSemiring R]
    {is js : List sigma} (h : is.Perm js) (p : MvPolynomial sigma R) :
    iteratedPDeriv is p = iteratedPDeriv js p := by
  induction h generalizing p with
  | nil => rfl
  | cons x _ ih => exact ih (MvPolynomial.pderiv x p)
  | swap x y l =>
      simp only [iteratedPDeriv_cons]
      rw [pderiv_comm]
  | trans _ _ ih₁ ih₂ => exact (ih₁ p).trans (ih₂ p)

theorem iteratedPDeriv_append {sigma R : Type*} [CommSemiring R]
    (is js : List sigma) (p : MvPolynomial sigma R) :
    iteratedPDeriv (is ++ js) p =
      iteratedPDeriv js (iteratedPDeriv is p) := by
  induction is generalizing p with
  | nil => rfl
  | cons i is ih => exact ih (MvPolynomial.pderiv i p)

theorem pderiv_iteratedPDeriv {sigma R : Type*} [CommSemiring R]
    (i : sigma) (is : List sigma) (p : MvPolynomial sigma R) :
    MvPolynomial.pderiv i (iteratedPDeriv is p) =
      iteratedPDeriv (i :: is) p := by
  change iteratedPDeriv [i] (iteratedPDeriv is p) = _
  rw [← iteratedPDeriv_append]
  apply iteratedPDeriv_perm
  have hmove : ∀ l : List sigma, (l ++ [i]).Perm (i :: l) := by
    intro l
    induction l with
    | nil => rfl
    | cons j js ih =>
        exact (List.Perm.cons j ih).trans (List.Perm.swap i j js)
  exact hmove is

theorem iteratedPDeriv_rename
    {sigma tau R : Type*} [CommSemiring R]
    (f : sigma → tau) (hf : Function.Injective f)
    (is : List sigma) (p : MvPolynomial sigma R) :
    iteratedPDeriv (List.map f is) (MvPolynomial.rename f p) =
      MvPolynomial.rename f (iteratedPDeriv is p) := by
  induction is generalizing p with
  | nil => rfl
  | cons i is ih =>
      simp only [List.map_cons, iteratedPDeriv_cons]
      rw [MvPolynomial.pderiv_rename hf, ih]

theorem iteratedPDeriv_C_mul {sigma : Type*}
    (is : List sigma) (a : ℂ) (p : MvPolynomial sigma ℂ) :
    iteratedPDeriv is (MvPolynomial.C a * p) =
      MvPolynomial.C a * iteratedPDeriv is p := by
  induction is generalizing p with
  | nil => rfl
  | cons i is ih =>
      simp only [iteratedPDeriv_cons]
      rw [MvPolynomial.pderiv_C_mul, ih]

/-- Coordinate deletion for the fully differentiated complex determinant
product underlying `rsExactMDPBase`. -/
theorem pderiv_iteratedDetProduct_eq_factorial_rename_delete
    {n k : ℕ}
    (hk : 0 < k)
    (A : Fin k → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) :
    MvPolynomial.pderiv i
        (iteratedPDeriv
          (repeatedCoordinateList (Fin (n + 1)) (k - 1))
          (∏ a : Fin k, hermitianDetPoly (A a))) =
      MvPolynomial.C (k.factorial : ℂ) *
        MvPolynomial.rename i.succAbove
          (iteratedPDeriv
            (repeatedCoordinateList (Fin n) (k - 1))
            (∏ a : Fin k,
              hermitianDetPoly
                ((A a).submatrix i.succAbove i.succAbove))) := by
  rw [pderiv_iteratedPDeriv]
  rw [iteratedPDeriv_perm (coordinateList_deletion_perm hk i)]
  rw [iteratedPDeriv_append]
  change iteratedPDeriv
      (List.map i.succAbove
        (repeatedCoordinateList (Fin n) (k - 1)))
      (repeatedPDeriv i k (∏ a : Fin k, hermitianDetPoly (A a))) = _
  rw [repeatedPDeriv_hermitianDetProduct_full_coordinate]
  rw [iteratedPDeriv_C_mul]
  rw [iteratedPDeriv_rename _ Fin.succAbove_right_injective]

/-- Real form of the coordinate-deletion identity for the exact-MDP base.
This is the explicit factorial identity needed for the deletion half of the
harness. -/
theorem pderiv_rsExactMDPBase_eq_factorial_rename_deleteFamilyAt
    {n k : ℕ}
    (hk : 0 < k)
    (A : Fin k → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (i : Fin (n + 1)) :
    MvPolynomial.pderiv i (rsExactMDPBase A) =
      MvPolynomial.C (k.factorial : ℝ) *
        MvPolynomial.rename i.succAbove
          (rsExactMDPBase
            (CommutatorTheorem.BTMDPDeletionIdentity.deleteFamilyAt A i)) := by
  let D := CommutatorTheorem.BTMDPDeletionIdentity.deleteFamilyAt A i
  have hD : ∀ a, (D a).IsHermitian :=
    CommutatorTheorem.BTMDPDeletionIdentity.deleteFamilyAt_isHermitian hA i
  unfold rsExactMDPBase
  apply MvPolynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  rw [← MvPolynomial.pderiv_map]
  rw [← iteratedPDeriv_map]
  rw [map_realHermitianDetProduct A hA]
  rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_rename]
  rw [← iteratedPDeriv_map]
  rw [map_realHermitianDetProduct D hD]
  simpa [D] using
    pderiv_iteratedDetProduct_eq_factorial_rename_delete hk A i

/-- Dimension-uniform ordered-coordinate version of the preceding identity. -/
theorem pderiv_rsExactMDPBase_eq_factorial_rename_deleteFamilyAtFin
    {N k : ℕ}
    (hk : 0 < k)
    (A : Fin k → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (i : Fin N) :
    MvPolynomial.pderiv i (rsExactMDPBase A) =
      MvPolynomial.C (k.factorial : ℝ) *
        MvPolynomial.rename
          (CommutatorTheorem.BTMDPDeletionIdentity.finDeleteOrderEmb i)
          (rsExactMDPBase
            (CommutatorTheorem.BTMDPDeletionIdentity.deleteFamilyAtFin A i)) := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
      have hemb :
          CommutatorTheorem.BTMDPDeletionIdentity.finDeleteOrderEmb i =
            Fin.succAboveOrderEmb i :=
        CommutatorTheorem.BTMDPDeletionIdentity.finDeleteOrderEmb_eq_succAbove i
      have hfamily :
          CommutatorTheorem.BTMDPDeletionIdentity.deleteFamilyAtFin A i =
            CommutatorTheorem.BTMDPDeletionIdentity.deleteFamilyAt A i := by
        funext a
        ext x y
        change A a
          (CommutatorTheorem.BTMDPDeletionIdentity.finDeleteOrderEmb i x)
          (CommutatorTheorem.BTMDPDeletionIdentity.finDeleteOrderEmb i y) =
          A a (i.succAbove x) (i.succAbove y)
        rw [hemb]
        rfl
      simpa [hemb, hfamily] using
        pderiv_rsExactMDPBase_eq_factorial_rename_deleteFamilyAt hk A hA i

theorem diagonalizeReal_C_mul {sigma : Type*}
    (a : ℝ) (p : MvPolynomial sigma ℝ) :
    diagonalizeReal (MvPolynomial.C a * p) = a • diagonalizeReal p := by
  simp [diagonalizeReal, Polynomial.smul_eq_C_mul]

/-! ## Reduction of the local harness to the single base coloring expansion -/

/-- The remaining finite determinant-coloring identity, with its explicit
factorial normalization.  All coordinate-deletion identities follow from it
and the proved multiaffine product calculus above. -/
def RSExactMDPFactorialBaseIdentity : Prop :=
  ∀ (n k : ℕ), 0 < k →
    ∀ (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
      (hA : ∀ a, (A a).IsHermitian),
      diagonalizeReal (rsExactMDPBase A) =
        ((k.factorial : ℝ) ^ n) •
          realMixedDeterminantalPolynomial A hA

private theorem prod_erase_zero_fin_succ
    {M : Type*} [CommMonoid M] {n : ℕ}
    (f : Fin (n + 1) → M) :
    (∏ b ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0, f b) =
      ∏ i : Fin n, f i.succ := by
  rw [Finset.prod_subtype
    (p := fun x : Fin (n + 1) ↦ x ≠ 0)
    ((Finset.univ : Finset (Fin (n + 1))).erase 0) (by simp) f]
  · symm
    apply Fintype.prod_equiv
      (CommutatorTheorem.BTMDPDeletionIdentity.finSuccAboveEquiv 0)
    intro x
    rfl

private def optionEraseSuccEquiv {n : ℕ} (a : Fin n) :
    Option {y : Fin n // y ≠ a} ≃ {x : Fin (n + 1) // x ≠ a.succ} where
  toFun
    | none => ⟨0, (Fin.succ_ne_zero a).symm⟩
    | some y => ⟨y.1.succ, fun h ↦ y.2 (Fin.succ_inj.mp h)⟩
  invFun x :=
    Fin.cases (motive := fun z ↦ z ≠ a.succ → Option {y : Fin n // y ≠ a})
      (fun _ ↦ none)
      (fun y hy ↦ some ⟨y, fun h ↦ hy (Fin.succ_inj.mpr h)⟩)
      x.1 x.2
  left_inv x := by
    cases x with
    | none => rfl
    | some y => rfl
  right_inv x := by
    rcases x with ⟨x, hx⟩
    apply Subtype.ext
    cases x using Fin.cases with
    | zero => rfl
    | succ y => rfl

@[simp] private theorem optionEraseSuccEquiv_none {n : ℕ} (a : Fin n) :
    (optionEraseSuccEquiv a none).1 = 0 := rfl

@[simp] private theorem optionEraseSuccEquiv_some {n : ℕ}
    (a : Fin n) (y : {y : Fin n // y ≠ a}) :
    (optionEraseSuccEquiv a (some y)).1 = y.1.succ := rfl

private theorem prod_erase_succ_fin_succ
    {M : Type*} [CommMonoid M] {n : ℕ}
    (f : Fin (n + 1) → M) (a : Fin n) :
    (∏ b ∈ (Finset.univ : Finset (Fin (n + 1))).erase a.succ, f b) =
      f 0 * ∏ i ∈ (Finset.univ : Finset (Fin n)).erase a, f i.succ := by
  rw [Finset.prod_subtype
    (p := fun x : Fin (n + 1) ↦ x ≠ a.succ)
    ((Finset.univ : Finset (Fin (n + 1))).erase a.succ) (by simp) f]
  rw [← Fintype.prod_equiv (optionEraseSuccEquiv a)
    (fun o : Option {y : Fin n // y ≠ a} ↦
      match o with
      | none => f 0
      | some y => f y.1.succ)
    (fun x ↦ f x.1) (by intro x; cases x <;> rfl)]
  rw [Fintype.prod_option]
  congr 1
  rw [Finset.prod_subtype
    (p := fun x : Fin n ↦ x ≠ a)
    ((Finset.univ : Finset (Fin n)).erase a) (by simp)
    (fun i ↦ f i.succ)]

/-- The leave-one-factor form of the higher Leibniz rule.  After `k-1`
derivatives of a product of `k` multiaffine factors, exactly one factor is
left undifferentiated. -/
theorem repeatedPDeriv_prod_fin_leave_one
    {sigma : Type*} (x : sigma) (n : ℕ)
    (f : Fin (n + 1) → MvPolynomial sigma ℂ)
    (hf : ∀ a, MvPolynomial.pderiv x (MvPolynomial.pderiv x (f a)) = 0) :
    repeatedPDeriv x n (∏ a : Fin (n + 1), f a) =
      MvPolynomial.C (n.factorial : ℂ) *
        ∑ a : Fin (n + 1),
          f a * ∏ b ∈ (Finset.univ : Finset (Fin (n + 1))).erase a,
            MvPolynomial.pderiv x (f b) := by
  induction n with
  | zero =>
      rw [repeatedPDeriv_zero]
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
      rw [prod_erase_zero_fin_succ]
      simp
  | succ n ih =>
      let g : Fin (n + 1) → MvPolynomial sigma ℂ := fun a ↦ f a.succ
      have hg : ∀ a, MvPolynomial.pderiv x
          (MvPolynomial.pderiv x (g a)) = 0 := fun a ↦ hf a.succ
      have hfull := repeatedPDeriv_prod_fin_full x (n + 1) g hg
      have hone := ih g hg
      rw [Fin.prod_univ_succ]
      rw [repeatedPDeriv_succ_mul_of_left_multiaffine x n]
      · rw [hfull, hone]
        conv_rhs => rw [Fin.sum_univ_succ]
        rw [prod_erase_zero_fin_succ]
        simp_rw [prod_erase_succ_fin_succ]
        rw [Nat.factorial_succ]
        push_cast
        rw [Algebra.smul_def]
        simp only [map_mul]
        dsimp [g]
        rw [mul_add, Finset.mul_sum]
        apply congrArg₂ (fun u v ↦ u + v)
        · ring
        · simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
      · exact hf 0

/-! ## Iterating the leave-one expansion over all coordinates -/

noncomputable def coloringExpansion {sigma : Type*} {m : ℕ} :
    List sigma → (Fin (m + 1) → MvPolynomial sigma ℂ) →
      MvPolynomial sigma ℂ
  | [], f => ∏ a, f a
  | x :: xs, f =>
      ∑ a : Fin (m + 1), coloringExpansion xs
        (fun b ↦ if b = a then f b else MvPolynomial.pderiv x (f b))

noncomputable def coordinateDerivativeBlocks {sigma : Type*}
    (r : ℕ) (xs : List sigma) : List sigma :=
  xs.flatMap (List.replicate r)

private theorem prod_leaveOneFamily
    {sigma : Type*} {m : ℕ} (x : sigma)
    (f : Fin (m + 1) → MvPolynomial sigma ℂ) (a : Fin (m + 1)) :
    (∏ b : Fin (m + 1),
        if b = a then f b else MvPolynomial.pderiv x (f b)) =
      f a * ∏ b ∈ (Finset.univ : Finset (Fin (m + 1))).erase a,
        MvPolynomial.pderiv x (f b) := by
  classical
  rw [Finset.prod_eq_mul_prod_diff_singleton a]
  · simp only [ite_true]
    congr 1
    rw [Finset.sdiff_singleton_eq_erase]
    apply Finset.prod_congr rfl
    intro b hb
    simp [Finset.ne_of_mem_erase hb]
  · simp

theorem iteratedPDeriv_sum {sigma : Type*}
    (is : List sigma) {iota : Type*} [Fintype iota]
    (f : iota → MvPolynomial sigma ℂ) :
    iteratedPDeriv is (∑ a, f a) = ∑ a, iteratedPDeriv is (f a) := by
  classical
  induction is generalizing f with
  | nil => rfl
  | cons x xs ih =>
      simp only [iteratedPDeriv_cons, map_sum, ih]

/-- Repeated leave-one expansion over a duplicate-free coordinate list. -/
theorem iteratedPDeriv_prod_eq_coloringExpansion
    {sigma : Type*} {m : ℕ} (xs : List sigma)
    (hxs : xs.Nodup)
    (f : Fin (m + 1) → MvPolynomial sigma ℂ)
    (hf : ∀ a x, x ∈ xs →
      MvPolynomial.pderiv x (MvPolynomial.pderiv x (f a)) = 0) :
    iteratedPDeriv (coordinateDerivativeBlocks m xs) (∏ a, f a) =
      MvPolynomial.C (((m.factorial : ℂ) ^ xs.length)) *
        coloringExpansion xs f := by
  induction xs generalizing f with
  | nil => simp [coordinateDerivativeBlocks, coloringExpansion]
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.mp hxs).1
      have hxs' : xs.Nodup := (List.nodup_cons.mp hxs).2
      have hupdated (chosen : Fin (m + 1)) :
          ∀ a y, y ∈ xs →
            MvPolynomial.pderiv y (MvPolynomial.pderiv y
              (if a = chosen then f a else MvPolynomial.pderiv x (f a))) = 0 := by
        intro a y hy
        split_ifs
        · exact hf a y (by simp [hy])
        · rw [pderiv_comm y x, pderiv_comm y x]
          rw [hf a y (by simp [hy])]
          simp
      rw [coordinateDerivativeBlocks]
      simp only [List.flatMap_cons]
      rw [iteratedPDeriv_append]
      change iteratedPDeriv (coordinateDerivativeBlocks m xs)
        (repeatedPDeriv x m (∏ a, f a)) = _
      rw [repeatedPDeriv_prod_fin_leave_one]
      · rw [iteratedPDeriv_C_mul, iteratedPDeriv_sum]
        simp_rw [← prod_leaveOneFamily x f]
        have hih (a : Fin (m + 1)) := ih hxs'
          (fun b ↦ if b = a then f b else MvPolynomial.pderiv x (f b))
          (hupdated a)
        simp_rw [hih]
        rw [coloringExpansion]
        simp only [List.length_cons, pow_succ, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [← mul_assoc, ← map_mul]
        ring
      · exact fun a ↦ hf a x (by simp)

noncomputable def coloringDerivativeTerm
    {sigma : Type*} {n m : ℕ} (e : Fin n → sigma)
    (c : Coloring n (m + 1))
    (f : Fin (m + 1) → MvPolynomial sigma ℂ) :
    MvPolynomial sigma ℂ :=
  ∏ a : Fin (m + 1),
    iteratedPDeriv
      (List.map e <| (List.finRange n).filter fun i ↦ c i != a)
      (f a)

/-- The recursive coloring expansion is the ordinary finite sum over all
colorings of the coordinate list. -/
theorem coloringExpansion_finRange
    {sigma : Type*} {n m : ℕ} (e : Fin n → sigma)
    (f : Fin (m + 1) → MvPolynomial sigma ℂ) :
    coloringExpansion (List.map e (List.finRange n)) f =
      ∑ c : Coloring n (m + 1), coloringDerivativeTerm e c f := by
  induction n generalizing f with
  | zero =>
      simp [coloringExpansion, coloringDerivativeTerm]
  | succ n ih =>
      rw [List.finRange_succ, List.map_cons, coloringExpansion]
      simp only [List.map_map]
      simp_rw [ih]
      rw [← Fintype.sum_prod_type (fun z :
        Fin (m + 1) × Coloring n (m + 1) ↦
          coloringDerivativeTerm (e ∘ Fin.succ) z.2
            (fun b ↦ if b = z.1 then f b else
              MvPolynomial.pderiv (e 0) (f b)))]
      apply Fintype.sum_equiv
        (CommutatorTheorem.BTMDPDeletionIdentity.coloringExtensionEquiv 0)
      rintro ⟨a, d⟩
      unfold coloringDerivativeTerm
      apply Finset.prod_congr rfl
      intro b _
      by_cases hba : b = a
      · subst a
        simp only [CommutatorTheorem.BTMDPDeletionIdentity.coloringExtensionEquiv_apply]
        simp only [↓reduceIte, CommutatorTheorem.BTMDPDeletionIdentity.extendColoring,
          Fin.insertNth_zero', List.finRange_succ, Fin.cons_zero, bne_self_eq_false,
          Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
        rw [List.filter_map, List.map_map]
        have hfilter :
            ((fun i : Fin (n + 1) ↦
                (Fin.cons b d : Fin (n + 1) → Fin (m + 1)) i != b) ∘
              Fin.succ) =
              (fun i ↦ d i != b) := by
          funext i
          rfl
        rw [hfilter]
      · simp only [CommutatorTheorem.BTMDPDeletionIdentity.coloringExtensionEquiv_apply]
        have hab : a ≠ b := Ne.symm hba
        simp only [hba, ↓reduceIte, CommutatorTheorem.BTMDPDeletionIdentity.extendColoring,
          Fin.insertNth_zero', List.finRange_succ, Fin.cons_zero, bne_iff_ne, ne_eq, hab,
          not_false_eq_true, List.filter_cons_of_pos, List.filter_map, List.map_cons, List.map_map,
          iteratedPDeriv_cons]
        have hfilter :
            ((fun i : Fin (n + 1) ↦
                (Fin.cons a d : Fin (n + 1) → Fin (m + 1)) i != b) ∘
              Fin.succ) =
              (fun i ↦ d i != b) := by
          funext i
          rfl
        rw [hfilter]

theorem coordinateDerivativeBlocks_finRange_perm_repeated
    (n r : ℕ) :
    (coordinateDerivativeBlocks r (List.finRange n)).Perm
      (repeatedCoordinateList (Fin n) r) := by
  classical
  rw [List.perm_iff_count]
  intro x
  rw [count_repeatedCoordinateList]
  unfold coordinateDerivativeBlocks
  rw [List.count_flatMap]
  have hsum : ∀ (N R : ℕ) (i : Fin N),
      (List.map (fun j : Fin N ↦ if j = i then R else 0)
        (List.finRange N)).sum = R := by
    intro N
    induction N with
    | zero =>
        intro R i
        exact Fin.elim0 i
    | succ N ih =>
        intro R i
        rw [List.finRange_succ]
        cases i using Fin.cases with
        | zero => simp [Function.comp_def]
        | succ i =>
            have hzero : (0 : Fin (N + 1)) ≠ i.succ :=
              Ne.symm (Fin.succ_ne_zero i)
            simp only [List.map_cons, List.sum_cons, if_neg hzero,
              zero_add, List.map_map]
            have hfun :
                ((fun j : Fin (N + 1) ↦ if j = i.succ then R else 0) ∘
                  Fin.succ) =
                (fun j : Fin N ↦ if j = i then R else 0) := by
              funext j
              simp
            rw [hfun]
            exact ih R i
  change (List.map
      (fun j : Fin n ↦ List.count x (List.replicate r j))
      (List.finRange n)).sum = r
  have hcount :
      (fun j : Fin n ↦ List.count x (List.replicate r j)) =
        (fun j : Fin n ↦ if j = x then r else 0) := by
    funext j
    by_cases hj : j = x
    · subst j
      simp
    · simp [List.count_replicate, hj]
  rw [hcount]
  exact hsum n r x

private theorem pderiv_self_hermitianDetPoly_fin
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    MvPolynomial.pderiv i
      (MvPolynomial.pderiv i (hermitianDetPoly A)) = 0 := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n => exact pderiv_self_hermitianDetPoly_fin_succ A i

/-- Expansion of the differentiated complex determinant product into one
term for every coordinate coloring, before interpreting each term as a
product of principal-compression characteristic polynomials. -/
theorem iteratedDetProduct_eq_sum_coloringDerivativeTerm
    {n m : ℕ}
    (A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℂ) :
    iteratedPDeriv (repeatedCoordinateList (Fin n) m)
        (∏ a : Fin (m + 1), hermitianDetPoly (A a)) =
      MvPolynomial.C (((m.factorial : ℂ) ^ n)) *
        ∑ c : Coloring n (m + 1),
          coloringDerivativeTerm (fun i : Fin n ↦ i) c
            (fun a ↦ hermitianDetPoly (A a)) := by
  have hblock := iteratedPDeriv_prod_eq_coloringExpansion
    (List.finRange n) (List.nodup_finRange n)
    (fun a ↦ hermitianDetPoly (A a))
    (fun a x _ ↦ pderiv_self_hermitianDetPoly_fin (A a) x)
  rw [show (List.finRange n).length = n by simp] at hblock
  calc
    iteratedPDeriv (repeatedCoordinateList (Fin n) m)
        (∏ a : Fin (m + 1), hermitianDetPoly (A a)) =
      iteratedPDeriv (coordinateDerivativeBlocks m (List.finRange n))
        (∏ a : Fin (m + 1), hermitianDetPoly (A a)) :=
      iteratedPDeriv_perm
        (coordinateDerivativeBlocks_finRange_perm_repeated n m).symm _
    _ = MvPolynomial.C (((m.factorial : ℂ) ^ n)) *
        coloringExpansion (List.finRange n)
          (fun a ↦ hermitianDetPoly (A a)) := hblock
    _ = _ := by
      congr 1
      simpa using coloringExpansion_finRange
        (fun i : Fin n ↦ i) (fun a ↦ hermitianDetPoly (A a))

/-- Once the base coloring expansion is known, the entire corrected
base-and-deletion harness follows, with no further determinant algebra. -/
theorem rsExactMDPBaseDeletionExpansion_of_factorialBase
    (F : RSExactMDPFactorialBaseIdentity) :
    RSExactMDPBaseDeletionExpansion := by
  intro n k hk A hA s
  let q : ℝ := k.factorial
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.factorial_pos k
  let B := restrictFamilyToFinset A s
  have hB : ∀ a, (B a).IsHermitian :=
    restrictFamilyToFinset_isHermitian hA s
  constructor
  · refine ⟨q ^ s.card, pow_pos hq _, ?_⟩
    simpa [q, B, restrictedMDP] using F s.card k hk B hB
  · intro hs
    refine ⟨q * q ^ (s.card - 1), mul_pos hq (pow_pos hq _), ?_⟩
    intro i
    let j : Fin s.card := finIndexOfMem s i
    let D := CommutatorTheorem.BTMDPDeletionIdentity.deleteFamilyAtFin B j
    have hD : ∀ a, (D a).IsHermitian :=
      CommutatorTheorem.BTMDPDeletionIdentity.deleteFamilyAtFin_isHermitian hB j
    have hcoord :=
      pderiv_rsExactMDPBase_eq_factorial_rename_deleteFamilyAtFin hk B hB j
    have hbaseD := F (s.card - 1) k hk D hD
    have hj : s.orderEmbOfFin rfl j = i.1 := by
      change ((s.orderIsoOfFin rfl)
        ((s.orderIsoOfFin rfl).symm i)).1 = i.1
      exact congrArg Subtype.val
        ((s.orderIsoOfFin rfl).apply_symm_apply i)
    have hmdp :=
      restrictedMDP_erase_orderEmb_eq_deleteFamilyAtFin A hA s j
    calc
      diagonalizeReal
          (MvPolynomial.pderiv j (rsExactMDPBase B)) =
          q • diagonalizeReal (rsExactMDPBase D) := by
            rw [hcoord, diagonalizeReal_C_mul, diagonalizeReal_rename]
      _ = q • ((q ^ (s.card - 1)) •
          realMixedDeterminantalPolynomial D hD) := by rw [hbaseD]
      _ = (q * q ^ (s.card - 1)) •
          restrictedMDP A hA (s.erase i.1) := by
            rw [smul_smul, ← hmdp, hj]


/-- Diagonal specialization of one real Hermitian determinant is its real
characteristic polynomial.  This is the determinant atom in the finite
exact-MDP expansion. -/
theorem diagonalizeReal_realHermitianDetPoly
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (A : Matrix sigma sigma ℂ) (hA : A.IsHermitian) :
    diagonalizeReal (realHermitianDetPoly A) = realCharpoly A hA := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  rw [map_diagonalizeReal, map_realHermitianDetPoly A hA,
    realCharpoly_map_complex]
  unfold diagonalize hermitianDetPoly Matrix.charpoly Matrix.charmatrix
  change MvPolynomial.eval₂Hom Polynomial.C (fun _ : sigma ↦ Polynomial.X)
      ((Matrix.diagonal (fun i ↦ MvPolynomial.X i) -
        A.map MvPolynomial.C).det) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

private def oneColoring (n : ℕ) : Coloring n 1 := fun _ ↦ 0

private def oneColorFiberEquiv (n : ℕ) :
    Fin n ≃ ColorFiber (oneColoring n) 0 where
  toFun i := ⟨i, rfl⟩
  invFun i := i.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- With one color, the exact MDP is just the real characteristic polynomial
of the sole matrix. -/
theorem realMixedDeterminantalPolynomial_fin_one
    {n : ℕ} (A : Fin 1 → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    realMixedDeterminantalPolynomial A hA = realCharpoly (A 0) (hA 0) := by
  let c : Coloring n 1 := oneColoring n
  have hc : ∀ d : Coloring n 1, d = c := by
    intro d
    funext i
    exact Subsingleton.elim _ _
  have hcomp :
      realCharpoly
          (BTMixedDet.principalCompression (A 0) c 0)
          (BTMixedDet.principalCompression_isHermitian (hA 0) c 0) =
        realCharpoly (A 0) (hA 0) := by
    apply CommutatorTheorem.BTMDPDeletionIdentity.realCharpoly_eq_of_reindex_eq
      (oneColorFiberEquiv n)
    ext i j
    rfl
  rw [realMixedDeterminantalPolynomial]
  have hcard : Fintype.card (Coloring n 1) = 1 := by simp [Coloring]
  rw [hcard]
  simp only [Nat.cast_one, inv_one, one_smul]
  rw [Fintype.sum_unique]
  rw [hc default]
  rw [realColoringPolynomial, Fintype.prod_unique]
  exact hcomp

/-- The base (non-deletion) half of the exact expansion is completely
formal for one color. -/
theorem diagonalizeReal_rsExactMDPBase_fin_one
    {n : ℕ} (A : Fin 1 → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (s : Finset (Fin n)) :
    diagonalizeReal
        (rsExactMDPBase (restrictFamilyToFinset A s)) =
      restrictedMDP A hA s := by
  let B := restrictFamilyToFinset A s
  have hB : ∀ a, (B a).IsHermitian :=
    restrictFamilyToFinset_isHermitian hA s
  rw [rsExactMDPBase]
  have hrep : repeatedCoordinateList (Fin s.card) (1 - 1) = [] := by
    simpa using repeatedCoordinateList_zero (Fin s.card)
  rw [hrep]
  simp only [iteratedPDeriv_nil]
  rw [realHermitianDetProduct, Fintype.prod_unique]
  rw [diagonalizeReal_realHermitianDetPoly (B default) (hB default)]
  rw [restrictedMDP, realMixedDeterminantalPolynomial_fin_one B hB]
  congr 2

/-- The currently stated base-deletion expansion is false at `k = 0`.
Consequently its quantifier list needs a hypothesis `0 < k`. -/
theorem not_RSExactMDPBaseDeletionExpansionUnrestricted :
    ¬ RSExactMDPBaseDeletionExpansionUnrestricted := by
  intro H
  let A : Fin 0 → Matrix (Fin 1) (Fin 1) ℂ := Fin.elim0
  have hA : ∀ a, (A a).IsHermitian := by
    intro a
    exact Fin.elim0 a
  obtain ⟨b, hb, heq⟩ := (H 1 0 A hA Finset.univ).1
  have hbase :
      diagonalizeReal
          (rsExactMDPBase (restrictFamilyToFinset A Finset.univ)) = 1 := by
    rw [rsExactMDPBase, repeatedCoordinateList_zero]
    simp only [iteratedPDeriv_nil]
    rw [realHermitianDetProduct]
    unfold diagonalizeReal
    exact MvPolynomial.eval₂_one _ _
  have hmdp : restrictedMDP A hA Finset.univ = 0 := by
    simp [restrictedMDP, realMixedDeterminantalPolynomial,
      realColoringPolynomial]
  rw [hbase, hmdp, smul_zero] at heq
  exact one_ne_zero heq

end CommutatorTheorem.BTRSBaseExpansion
