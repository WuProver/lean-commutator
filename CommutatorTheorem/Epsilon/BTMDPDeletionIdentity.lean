import CommutatorTheorem.Epsilon.BTMDPStability

/-!
# Finite reindexing for the exact-MDP deletion identity

This file isolates the finite combinatorics in the proof that differentiating
the exact mixed determinantal polynomial is the sum of the exact MDPs obtained
by deleting one coordinate.  A coloring together with a coordinate is
canonically equivalent to

* the coordinate to delete;
* its color; and
* the coloring restricted to the remaining coordinates.

The equivalence is implemented with `Fin.insertNth`/`Fin.removeNth`.  The last
theorem below is the precise three-sum reindexing needed after applying the
product rule and Jacobi's formula to every leaf.  There are no axioms or
placeholders in this file.
-/

open scoped BigOperators Polynomial

namespace CommutatorTheorem.BTMDPDeletionIdentity

open CommutatorTheorem.BTMixedDet
open CommutatorTheorem.BTMixedDeterminantal
open CommutatorTheorem.BTMDPSelection
open CommutatorTheorem.BTMDPStability

/-! ## The canonical equivalence with a deleted `Fin` coordinate -/

/-- `Fin n` is the complement of one fixed point in `Fin (n + 1)`, via
`succAbove`. -/
noncomputable def finSuccAboveEquiv {n : ℕ} (i : Fin (n + 1)) :
    Fin n ≃ {j : Fin (n + 1) // j ≠ i} :=
  (Equiv.ofInjective i.succAbove Fin.succAbove_right_injective).trans
    (Equiv.setCongr (by
      ext j
      simp only [Set.mem_range]
      exact Fin.exists_succAbove_eq_iff))

@[simp] theorem finSuccAboveEquiv_apply_val {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) :
    (finSuccAboveEquiv i j).1 = i.succAbove j := rfl

/-- Transporting `succAbove` through an arbitrary equivalence gives the
complement of the corresponding coordinate. -/
noncomputable def complementEquivOfFinSucc {n : ℕ} {ι : Type*}
    (e : Fin (n + 1) ≃ ι) (j : Fin (n + 1)) :
    Fin n ≃ {x : ι // x ≠ e j} :=
  (finSuccAboveEquiv j).trans
    (Equiv.subtypeEquiv e (by
      intro x
      exact e.injective.eq_iff.not.symm))

@[simp] theorem complementEquivOfFinSucc_apply_val {n : ℕ} {ι : Type*}
    (e : Fin (n + 1) ≃ ι) (j : Fin (n + 1)) (t : Fin n) :
    (complementEquivOfFinSucc e j t).1 = e (j.succAbove t) := rfl

/-! ## Jacobi after an arbitrary finite reindexing -/

/-- Coordinate-deletion Jacobi formula on any type explicitly presented as
`Fin (n + 1)`.  This is the form needed for a nonempty color fiber: the
equivalence may depend on both the coloring and the color. -/
theorem charpoly_derivative_eq_sum_principal_of_equiv
    {n : ℕ} {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (e : Fin (n + 1) ≃ ι) (M : Matrix ι ι R) :
    Polynomial.derivative M.charpoly =
      ∑ i : ι,
        (M.submatrix (fun x : {x : ι // x ≠ i} ↦ x.1)
          (fun x : {x : ι // x ≠ i} ↦ x.1)).charpoly := by
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.reindex e.symm e.symm M
  rw [← e.sum_comp]
  rw [← Matrix.charpoly_reindex e.symm M]
  rw [BTMDPStability.charpoly_derivative_eq_sum_principal_fin_succ N]
  apply Finset.sum_congr rfl
  intro j _
  let q := complementEquivOfFinSucc e j
  rw [← Matrix.charpoly_reindex q
    (N.submatrix j.succAbove j.succAbove)]
  congr 1
  ext x y
  change M (e (j.succAbove (q.symm x)))
      (e (j.succAbove (q.symm y))) = M x.1 y.1
  have hx := congrArg Subtype.val (q.apply_symm_apply x)
  have hy := congrArg Subtype.val (q.apply_symm_apply y)
  change e (j.succAbove (q.symm x)) = x.1 at hx
  change e (j.succAbove (q.symm y)) = y.1 at hy
  rw [hx, hy]

/-- Real-coefficient Hermitian version of
`charpoly_derivative_eq_sum_principal_of_equiv`. -/
theorem realCharpoly_derivative_eq_sum_principal_of_equiv
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Fin (n + 1) ≃ ι) (M : Matrix ι ι ℂ)
    (hM : M.IsHermitian) :
    Polynomial.derivative (realCharpoly M hM) =
      ∑ i : ι,
        realCharpoly
          (M.submatrix (fun x : {x : ι // x ≠ i} ↦ x.1)
            (fun x : {x : ι // x ≠ i} ↦ x.1))
          (hM.submatrix (fun x : {x : ι // x ≠ i} ↦ x.1)) := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  rw [← Polynomial.derivative_map, realCharpoly_map_complex]
  rw [charpoly_derivative_eq_sum_principal_of_equiv e M]
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (realCharpoly_map_complex _ _).symm

/-- Jacobi's coordinate-deletion formula for a real Hermitian characteristic
polynomial on an arbitrary finite index type. -/
theorem realCharpoly_derivative_eq_sum_principal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    Polynomial.derivative (realCharpoly M hM) =
      ∑ i : ι,
        realCharpoly
          (M.submatrix (fun x : {x : ι // x ≠ i} ↦ x.1)
            (fun x : {x : ι // x ≠ i} ↦ x.1))
          (hM.submatrix (fun x : {x : ι // x ≠ i} ↦ x.1)) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI := hempty
      simp [realCharpoly]
  | inr hnonempty =>
      letI := hnonempty
      let n := Fintype.card ι - 1
      have hcard : Fintype.card ι = n + 1 := by
        have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hnonempty
        dsimp [n]
        omega
      let e : Fin (n + 1) ≃ ι :=
        (Fintype.equivFinOfCardEq hcard).symm
      exact realCharpoly_derivative_eq_sum_principal_of_equiv e M hM

/-! ## Reindexing Hermitian characteristic polynomials -/

/-- The chosen real form of a Hermitian characteristic polynomial is
invariant under simultaneous reindexing. -/
theorem realCharpoly_reindex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    realCharpoly (Matrix.reindex e e M) (hM.reindex e) =
      realCharpoly M hM := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  rw [realCharpoly_map_complex, realCharpoly_map_complex]
  exact Matrix.charpoly_reindex e M

/-- Delete one ambient coordinate from every matrix in a family. -/
def deleteFamilyAt {n k : ℕ}
    (A : Fin k → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (a : Fin k) : Matrix (Fin n) (Fin n) ℂ :=
  (A a).submatrix i.succAbove i.succAbove

theorem deleteFamilyAt_isHermitian {n k : ℕ}
    {A : Fin k → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : ∀ a, (A a).IsHermitian) (i : Fin (n + 1)) (a : Fin k) :
    (deleteFamilyAt A i a).IsHermitian :=
  (hA a).submatrix i.succAbove

/-! ## Restricting and extending a coloring at one coordinate -/

/-- Delete coordinate `i` from a coloring of `n + 1` coordinates. -/
def deleteColoring {n k : ℕ} (i : Fin (n + 1))
    (c : Coloring (n + 1) k) : Coloring n k :=
  Fin.removeNth i c

/-- Extend a coloring of the complement of `i` by assigning color `a` to
`i`. -/
def extendColoring {n k : ℕ} (i : Fin (n + 1))
    (a : Fin k) (d : Coloring n k) : Coloring (n + 1) k :=
  Fin.insertNth i a d

@[simp] theorem deleteColoring_extendColoring {n k : ℕ}
    (i : Fin (n + 1)) (a : Fin k) (d : Coloring n k) :
    deleteColoring i (extendColoring i a d) = d := by
  simp [deleteColoring, extendColoring]

@[simp] theorem extendColoring_apply_deleted {n k : ℕ}
    (i : Fin (n + 1)) (a : Fin k) (d : Coloring n k) :
    extendColoring i a d i = a := by
  simp [extendColoring]

@[simp] theorem extendColoring_apply_remaining {n k : ℕ}
    (i : Fin (n + 1)) (a : Fin k) (d : Coloring n k) (j : Fin n) :
    extendColoring i a d (i.succAbove j) = d j := by
  simp [extendColoring]

@[simp] theorem extendColoring_self_deleteColoring {n k : ℕ}
    (i : Fin (n + 1)) (c : Coloring (n + 1) k) :
    extendColoring i (c i) (deleteColoring i c) = c := by
  exact Fin.insertNth_self_removeNth i c

/-! ## Reindexing color fibers after deletion -/

/-- Swap the order of two nested subtype conditions. -/
def swapNestedSubtypeEquiv {α : Type*} (p q : α → Prop) :
    {x : {x : α // p x} // q x.1} ≃
      {x : {x : α // q x} // p x.1} where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- After deleting coordinate `i`, the `b`-fiber of the restricted coloring
is the old `b`-fiber with `i` removed.  This statement is uniform in whether
`b` is the color assigned to `i`. -/
noncomputable def deletedColorFiberEquiv {n k : ℕ}
    (i : Fin (n + 1)) (a : Fin k) (d : Coloring n k) (b : Fin k) :
    ColorFiber d b ≃
      {x : ColorFiber (extendColoring i a d) b // x.1 ≠ i} :=
  (Equiv.subtypeEquiv (finSuccAboveEquiv i) (by
      intro j
      change (d j = b) ↔
        extendColoring i a d (i.succAbove j) = b
      rw [extendColoring_apply_remaining])).trans
    (swapNestedSubtypeEquiv (fun x : Fin (n + 1) ↦ x ≠ i)
      (fun x : Fin (n + 1) ↦ extendColoring i a d x = b))

@[simp] theorem deletedColorFiberEquiv_apply_val {n k : ℕ}
    (i : Fin (n + 1)) (a : Fin k) (d : Coloring n k)
    (b : Fin k) (x : ColorFiber d b) :
    ((deletedColorFiberEquiv i a d b x).1 : Fin (n + 1)) =
      i.succAbove x.1 := rfl

/-- The assigned-color specialization, with the removed point expressed as
the actual fiber element rather than only by equality of ambient values. -/
noncomputable def deletedPivotColorFiberEquiv {n k : ℕ}
    (i : Fin (n + 1)) (a : Fin k) (d : Coloring n k) :
    ColorFiber d a ≃
      {x : ColorFiber (extendColoring i a d) a //
        x ≠ ⟨i, extendColoring_apply_deleted i a d⟩} := by
  let e := deletedColorFiberEquiv i a d a
  let pivot : ColorFiber (extendColoring i a d) a :=
    ⟨i, extendColoring_apply_deleted i a d⟩
  exact
    { toFun := fun x ↦ ⟨(e x).1, by
        intro hx
        have hxval := congrArg (fun z : ColorFiber (extendColoring i a d) a ↦ z.1) hx
        exact (e x).2 hxval⟩
      invFun := fun x ↦ e.symm ⟨x.1, by
        intro hxval
        apply x.2
        exact Subtype.ext hxval⟩
      left_inv := by
        intro x
        apply e.injective
        simp only [Equiv.apply_symm_apply]
      right_inv := by
        intro x
        apply Subtype.ext
        simp only [Equiv.apply_symm_apply] }

@[simp] theorem deletedPivotColorFiberEquiv_apply_val {n k : ℕ}
    (i : Fin (n + 1)) (a : Fin k) (d : Coloring n k)
    (x : ColorFiber d a) :
    ((deletedPivotColorFiberEquiv i a d x).1 : Fin (n + 1)) =
      i.succAbove x.1 := rfl

/-- If `b` differs from the color assigned at `i`, removing `i` does not
change the `b`-fiber. -/
def colorFiberComplementEquivOf_ne {n k : ℕ}
    (i : Fin (n + 1)) (a b : Fin k) (d : Coloring n k) (hba : b ≠ a) :
    {x : ColorFiber (extendColoring i a d) b // x.1 ≠ i} ≃
      ColorFiber (extendColoring i a d) b where
  toFun x := x.1
  invFun x := ⟨x, by
    intro hxi
    have hcolor := x.2
    have hxval : x.1 = i := hxi
    rw [hxval, extendColoring_apply_deleted] at hcolor
    exact hba hcolor.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindex the unchanged `b`-fiber (`b ≠ a`) by the coordinates remaining
after deletion. -/
noncomputable def unchangedColorFiberEquiv {n k : ℕ}
    (i : Fin (n + 1)) (a b : Fin k) (d : Coloring n k) (hba : b ≠ a) :
    ColorFiber d b ≃ ColorFiber (extendColoring i a d) b :=
  (deletedColorFiberEquiv i a d b).trans
    (colorFiberComplementEquivOf_ne i a b d hba)

@[simp] theorem unchangedColorFiberEquiv_apply_val {n k : ℕ}
    (i : Fin (n + 1)) (a b : Fin k) (d : Coloring n k) (hba : b ≠ a)
    (x : ColorFiber d b) :
    (unchangedColorFiberEquiv i a b d hba x).1 = i.succAbove x.1 := rfl

/-- A convenient proof-irrelevant version of real-charpoly invariance under
reindexing. -/
theorem realCharpoly_eq_of_reindex_eq
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℂ) (N : Matrix κ κ ℂ)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hMN : Matrix.reindex e e M = N) :
    realCharpoly N hN = realCharpoly M hM := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  rw [realCharpoly_map_complex, realCharpoly_map_complex, ← hMN]
  exact Matrix.charpoly_reindex e M

/-- Family equality may be used under the proof-dependent real MDP
constructor; Hermitian witnesses are proof irrelevant. -/
theorem realMixedDeterminantalPolynomial_congr
    {n k : ℕ}
    (A B : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (hB : ∀ a, (B a).IsHermitian) (hAB : A = B) :
    realMixedDeterminantalPolynomial A hA =
      realMixedDeterminantalPolynomial B hB := by
  subst B
  rfl

/-- For a color different from the deleted coordinate's assigned color, the
old compression and the compression of the deleted family are the same up to
the explicit fiber reindexing. -/
theorem deletedCompression_realCharpoly_eq_unchanged
    {n k : ℕ}
    (A : Fin k → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : ∀ b, (A b).IsHermitian)
    (i : Fin (n + 1)) (a b : Fin k) (d : Coloring n k)
    (hba : b ≠ a) :
    realCharpoly
        (BTMixedDet.principalCompression (deleteFamilyAt A i b) d b)
        (BTMixedDet.principalCompression_isHermitian
          (deleteFamilyAt_isHermitian hA i b) d b) =
      realCharpoly
        (BTMixedDet.principalCompression (A b) (extendColoring i a d) b)
        (BTMixedDet.principalCompression_isHermitian (hA b)
          (extendColoring i a d) b) := by
  let e := unchangedColorFiberEquiv i a b d hba
  apply realCharpoly_eq_of_reindex_eq e.symm
  ext x y
  change A b (e x).1 (e y).1 =
    A b (i.succAbove x.1) (i.succAbove y.1)
  rw [unchangedColorFiberEquiv_apply_val,
    unchangedColorFiberEquiv_apply_val]

/-- The Jacobi minor in the color assigned to the deleted coordinate is the
corresponding color compression of the deleted family. -/
theorem deletedCompression_realCharpoly_eq_jacobi
    {n k : ℕ}
    (A : Fin k → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : ∀ b, (A b).IsHermitian)
    (i : Fin (n + 1)) (a : Fin k) (d : Coloring n k) :
    realCharpoly
        (BTMixedDet.principalCompression (deleteFamilyAt A i a) d a)
        (BTMixedDet.principalCompression_isHermitian
          (deleteFamilyAt_isHermitian hA i a) d a) =
      realCharpoly
        ((BTMixedDet.principalCompression (A a) (extendColoring i a d) a).submatrix
          (fun x : {x : ColorFiber (extendColoring i a d) a //
            x ≠ ⟨i, extendColoring_apply_deleted i a d⟩} ↦ x.1)
          (fun x : {x : ColorFiber (extendColoring i a d) a //
            x ≠ ⟨i, extendColoring_apply_deleted i a d⟩} ↦ x.1))
        ((BTMixedDet.principalCompression_isHermitian (hA a)
          (extendColoring i a d) a).submatrix
            (fun x : {x : ColorFiber (extendColoring i a d) a //
              x ≠ ⟨i, extendColoring_apply_deleted i a d⟩} ↦ x.1)) := by
  let e := deletedPivotColorFiberEquiv i a d
  apply realCharpoly_eq_of_reindex_eq e.symm
  ext x y
  change A a (e x).1.1 (e y).1.1 =
    A a (i.succAbove x.1) (i.succAbove y.1)
  rw [deletedPivotColorFiberEquiv_apply_val,
    deletedPivotColorFiberEquiv_apply_val]

/-- After the coloring/fiber reindexing, one product-rule/Jacobi summand is
exactly a leaf of the MDP for the coordinate-deleted family. -/
theorem reindexedJacobiTerm_eq_realColoringPolynomial
    {n k : ℕ}
    (A : Fin k → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : ∀ b, (A b).IsHermitian)
    (i : Fin (n + 1)) (a : Fin k) (d : Coloring n k) :
    (∏ b ∈ (Finset.univ : Finset (Fin k)).erase a,
        realCharpoly
          (BTMixedDet.principalCompression (A b)
            (extendColoring i a d) b)
          (BTMixedDet.principalCompression_isHermitian (hA b)
            (extendColoring i a d) b)) *
      realCharpoly
        ((BTMixedDet.principalCompression (A a)
          (extendColoring i a d) a).submatrix
          (fun x : {x : ColorFiber (extendColoring i a d) a //
            x ≠ ⟨i, extendColoring_apply_deleted i a d⟩} ↦ x.1)
          (fun x : {x : ColorFiber (extendColoring i a d) a //
            x ≠ ⟨i, extendColoring_apply_deleted i a d⟩} ↦ x.1))
        ((BTMixedDet.principalCompression_isHermitian (hA a)
          (extendColoring i a d) a).submatrix
          (fun x : {x : ColorFiber (extendColoring i a d) a //
            x ≠ ⟨i, extendColoring_apply_deleted i a d⟩} ↦ x.1)) =
      realColoringPolynomial (deleteFamilyAt A i)
        (deleteFamilyAt_isHermitian hA i) d := by
  rw [realColoringPolynomial]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun b ↦ realCharpoly
      (BTMixedDet.principalCompression (deleteFamilyAt A i b) d b)
      (BTMixedDet.principalCompression_isHermitian
        (deleteFamilyAt_isHermitian hA i b) d b)) (Finset.mem_univ a)]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro b hb
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    exact (deletedCompression_realCharpoly_eq_unchanged
      A hA i a b d hba).symm
  · exact (deletedCompression_realCharpoly_eq_jacobi A hA i a d).symm

/-- For a fixed deleted coordinate, a coloring is equivalent to the color at
that coordinate together with the coloring of the remaining coordinates. -/
def coloringExtensionEquiv {n k : ℕ} (i : Fin (n + 1)) :
    (Fin k × Coloring n k) ≃ Coloring (n + 1) k :=
  Fin.insertNthEquiv (fun _ ↦ Fin k) i

@[simp] theorem coloringExtensionEquiv_apply {n k : ℕ}
    (i : Fin (n + 1)) (x : Fin k × Coloring n k) :
    coloringExtensionEquiv i x = extendColoring i x.1 x.2 := rfl

@[simp] theorem coloringExtensionEquiv_symm_apply {n k : ℕ}
    (i : Fin (n + 1)) (c : Coloring (n + 1) k) :
    (coloringExtensionEquiv i).symm c = (c i, deleteColoring i c) := rfl

/-! ## A coloring-coordinate pair as deletion data -/

/-- A coloring together with a distinguished coordinate is canonically the
same as a deleted coordinate, its old color, and the restricted coloring. -/
def coloringCoordinateEquiv {n k : ℕ} :
    (Σ _c : Coloring (n + 1) k, Fin (n + 1)) ≃
      Fin (n + 1) × (Fin k × Coloring n k) where
  toFun x := (x.2, (x.1 x.2, deleteColoring x.2 x.1))
  invFun x := ⟨extendColoring x.1 x.2.1 x.2.2, x.1⟩
  left_inv := by
    rintro ⟨c, i⟩
    apply Sigma.ext
    · exact extendColoring_self_deleteColoring i c
    · rfl
  right_inv := by
    rintro ⟨i, a, d⟩
    simp

@[simp] theorem coloringCoordinateEquiv_apply {n k : ℕ}
    (c : Coloring (n + 1) k) (i : Fin (n + 1)) :
    coloringCoordinateEquiv ⟨c, i⟩ =
      (i, (c i, deleteColoring i c)) := rfl

@[simp] theorem coloringCoordinateEquiv_symm_apply {n k : ℕ}
    (i : Fin (n + 1)) (a : Fin k) (d : Coloring n k) :
    coloringCoordinateEquiv.symm (i, (a, d)) =
      ⟨extendColoring i a d, i⟩ := rfl

/-! ## Sum reindexing -/

/-- Sum over all colors and all points in the corresponding color fiber by
first summing over the underlying coordinate. -/
theorem sum_colorFiber_eq_sum_coordinate {n k : ℕ}
    {R : Type*} [AddCommMonoid R] (c : Coloring n k)
    (f : (a : Fin k) → ColorFiber c a → R) :
    ∑ a : Fin k, ∑ i : ColorFiber c a, f a i =
      ∑ i : Fin n, f (c i) ⟨i, rfl⟩ := by
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv (sigmaColorFiberEquiv c) (fun x ↦ f x.1 x.2)
    (fun i ↦ f (c i) ⟨i, rfl⟩) (by
      rintro ⟨a, i, hi⟩
      subst a
      rfl)

/-- Reindex a sum over a coloring and a distinguished coordinate as a sum
over the deleted coordinate, its assigned color, and a coloring of the
remaining coordinates. -/
theorem sum_coloring_coordinate_eq_sum_extensions {n k : ℕ}
    {R : Type*} [AddCommMonoid R]
    (f : Coloring (n + 1) k → Fin (n + 1) → R) :
    ∑ c : Coloring (n + 1) k, ∑ i : Fin (n + 1), f c i =
      ∑ i : Fin (n + 1), ∑ a : Fin k, ∑ d : Coloring n k,
        f (extendColoring i a d) i := by
  rw [← Fintype.sum_sigma']
  rw [Fintype.sum_equiv coloringCoordinateEquiv
    (fun x ↦ f x.1 x.2)
    (fun x ↦ f (extendColoring x.1 x.2.1 x.2.2) x.1)
    (by
      rintro ⟨c, i⟩
      change f c i = f (extendColoring i (c i) (deleteColoring i c)) i
      rw [extendColoring_self_deleteColoring])]
  calc
    ∑ x : Fin (n + 1) × (Fin k × Coloring n k),
        f (extendColoring x.1 x.2.1 x.2.2) x.1 =
        ∑ i : Fin (n + 1), ∑ x : Fin k × Coloring n k,
          f (extendColoring i x.1 x.2) i :=
      Fintype.sum_prod_type _
    _ = ∑ i : Fin (n + 1), ∑ a : Fin k, ∑ d : Coloring n k,
          f (extendColoring i a d) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact Fintype.sum_prod_type _

/-- The exact reindexing after product rule and Jacobi: a coloring, a matrix
label, and a coordinate in that label's color fiber become a deleted
coordinate, one of its `k` possible colors, and the restricted coloring.

The equality proof `c i = a` carried by the fiber disappears because the
extension assigns `a` to `i` definitionally. -/
theorem sum_coloring_colorFiber_eq_sum_deletion_extensions {n k : ℕ}
    {R : Type*} [AddCommMonoid R]
    (f : (c : Coloring (n + 1) k) →
      (a : Fin k) → ColorFiber c a → R) :
    ∑ c : Coloring (n + 1) k, ∑ a : Fin k,
        ∑ i : ColorFiber c a, f c a i =
      ∑ i : Fin (n + 1), ∑ a : Fin k, ∑ d : Coloring n k,
        f (extendColoring i a d) a ⟨i, extendColoring_apply_deleted i a d⟩ := by
  simp_rw [sum_colorFiber_eq_sum_coordinate]
  rw [sum_coloring_coordinate_eq_sum_extensions]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  let c : Coloring (n + 1) k := extendColoring i a d
  change f c (c i) ⟨i, rfl⟩ = f c a ⟨i, _⟩
  have ha : c i = a := by simp [c]
  have fiber_transport :
      ∀ (c' : Coloring (n + 1) k) (i' : Fin (n + 1))
        (a' : Fin k) (h : c' i' = a'),
        f c' (c' i') ⟨i', rfl⟩ = f c' a' ⟨i', h⟩ := by
    intro c' i' a' h
    subst a'
    rfl
  exact fiber_transport c i a ha

/-! ## The ambient exact-MDP deletion identity -/

/-- Unnormalized numerator identity: differentiating every coloring leaf and
summing is the same as choosing the deleted coordinate, its old color, and a
coloring of the remaining coordinates. -/
theorem sum_derivative_realColoringPolynomial_eq_deletions
    {n k : ℕ}
    (A : Fin k → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : ∀ b, (A b).IsHermitian) :
    ∑ c : Coloring (n + 1) k,
        Polynomial.derivative (realColoringPolynomial A hA c) =
      ∑ i : Fin (n + 1), ∑ _a : Fin k, ∑ d : Coloring n k,
        realColoringPolynomial (deleteFamilyAt A i)
          (deleteFamilyAt_isHermitian hA i) d := by
  simp_rw [BTMDPStability.derivative_realColoringPolynomial]
  simp_rw [realCharpoly_derivative_eq_sum_principal]
  simp_rw [Finset.mul_sum]
  rw [sum_coloring_colorFiber_eq_sum_deletion_extensions]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  exact reindexedJacobiTerm_eq_realColoringPolynomial A hA i a d

/-- The normalization constants in consecutive coloring dimensions differ
by exactly the sum over the deleted coordinate's `k` possible colors. -/
theorem inv_coloringCard_succ_mul_colors {n k : ℕ} (hk : 0 < k) :
    ((Fintype.card (Coloring (n + 1) k) : ℝ)⁻¹) * (k : ℝ) =
      (Fintype.card (Coloring n k) : ℝ)⁻¹ := by
  rw [BTMixedDet.coloring_card, BTMixedDet.coloring_card, pow_succ]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hpowR : ((k : ℝ) ^ n) ≠ 0 := pow_ne_zero _ hkR
  push_cast
  field_simp

/-- Exact ambient deletion identity for the normalized real MDP.  Positivity
of `k` is necessary: with no colors the dimension-zero average is exceptional. -/
theorem derivative_realMixedDeterminantalPolynomial_eq_sum_deleteFamilyAt
    {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : ∀ b, (A b).IsHermitian) :
    Polynomial.derivative (realMixedDeterminantalPolynomial A hA) =
      ∑ i : Fin (n + 1),
        realMixedDeterminantalPolynomial (deleteFamilyAt A i)
          (deleteFamilyAt_isHermitian hA i) := by
  rw [BTMDPStability.derivative_realMixedDeterminantalPolynomial_eq_average]
  rw [sum_derivative_realColoringPolynomial_eq_deletions A hA]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [realMixedDeterminantalPolynomial]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ k]
  rw [smul_smul]
  congr 1
  exact inv_coloringCard_succ_mul_colors hk

/-! ## Dimension-uniform ordered coordinate deletion -/

/-- The increasing enumeration of all coordinates except `j`. -/
noncomputable def finDeleteOrderEmb {N : ℕ} (j : Fin N) :
    Fin (N - 1) ↪o Fin N :=
  ({j}ᶜ : Finset (Fin N)).orderEmbOfFin (by simp [Finset.card_compl])

theorem finDeleteOrderEmb_eq_succAbove {n : ℕ} (j : Fin (n + 1)) :
    finDeleteOrderEmb j = Fin.succAboveOrderEmb j := by
  exact Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb j

/-- Delete position `j` from a family on `Fin N`, retaining the increasing
order of all remaining positions. -/
noncomputable def deleteFamilyAtFin {N k : ℕ}
    (A : Fin k → Matrix (Fin N) (Fin N) ℂ)
    (j : Fin N) (a : Fin k) : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ :=
  (A a).submatrix (finDeleteOrderEmb j) (finDeleteOrderEmb j)

theorem deleteFamilyAtFin_isHermitian {N k : ℕ}
    {A : Fin k → Matrix (Fin N) (Fin N) ℂ}
    (hA : ∀ a, (A a).IsHermitian) (j : Fin N) (a : Fin k) :
    (deleteFamilyAtFin A j a).IsHermitian :=
  (hA a).submatrix (finDeleteOrderEmb j)

/-- Dimension-uniform form of the ambient exact-MDP deletion identity. -/
theorem derivative_realMixedDeterminantalPolynomial_eq_sum_deleteFamilyAtFin
    {N k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ b, (A b).IsHermitian) :
    Polynomial.derivative (realMixedDeterminantalPolynomial A hA) =
      ∑ j : Fin N,
        realMixedDeterminantalPolynomial (deleteFamilyAtFin A j)
          (deleteFamilyAtFin_isHermitian hA j) := by
  cases N with
  | zero =>
      simp [realMixedDeterminantalPolynomial, realColoringPolynomial,
        realCharpoly]
  | succ n =>
      rw [derivative_realMixedDeterminantalPolynomial_eq_sum_deleteFamilyAt
        (n := n) hk A hA]
      apply Finset.sum_congr rfl
      intro j _
      have hfamily : deleteFamilyAtFin A j = deleteFamilyAt A j := by
        funext a
        ext x y
        simp only [deleteFamilyAtFin, deleteFamilyAt,
          finDeleteOrderEmb_eq_succAbove, Matrix.submatrix_apply]
        rfl
      exact (realMixedDeterminantalPolynomial_congr
        (deleteFamilyAtFin A j) (deleteFamilyAt A j)
        (deleteFamilyAtFin_isHermitian hA j)
        (deleteFamilyAt_isHermitian hA j) hfamily).symm

/-! ## Compatibility with `restrictFamilyToFinset` -/

/-- Simultaneously cast the matrix dimension of every member of a family
along an equality of natural numbers. -/
noncomputable def reindexFamilyByFinCast {r m k : ℕ} (h : r = m)
    (A : Fin k → Matrix (Fin r) (Fin r) ℂ)
    (a : Fin k) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.reindex (Fin.castOrderIso h).toEquiv
    (Fin.castOrderIso h).toEquiv (A a)

theorem reindexFamilyByFinCast_isHermitian {r m k : ℕ} (h : r = m)
    {A : Fin k → Matrix (Fin r) (Fin r) ℂ}
    (hA : ∀ a, (A a).IsHermitian) (a : Fin k) :
    (reindexFamilyByFinCast h A a).IsHermitian :=
  (hA a).reindex (Fin.castOrderIso h).toEquiv

/-- The real MDP is unchanged by a dimension cast. -/
theorem realMixedDeterminantalPolynomial_reindexFamilyByFinCast
    {r m k : ℕ} (h : r = m)
    (A : Fin k → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    realMixedDeterminantalPolynomial A hA =
      realMixedDeterminantalPolynomial (reindexFamilyByFinCast h A)
        (reindexFamilyByFinCast_isHermitian h hA) := by
  subst m
  apply realMixedDeterminantalPolynomial_congr
  funext a
  ext x y
  rfl

/-- Deleting a position in the ordered compression to `s` is exactly the
ordered compression to the finset obtained by erasing the corresponding
ambient coordinate. -/
theorem restrictedMDP_erase_orderEmb_eq_deleteFamilyAtFin
    {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian)
    (s : Finset (Fin n)) (j : Fin s.card) :
    restrictedMDP A hA
        (s.erase (s.orderEmbOfFin rfl j)) =
      realMixedDeterminantalPolynomial
        (deleteFamilyAtFin (restrictFamilyToFinset A s) j)
        (deleteFamilyAtFin_isHermitian
          (restrictFamilyToFinset_isHermitian hA s) j) := by
  let i : Fin n := s.orderEmbOfFin rfl j
  let t : Finset (Fin n) := s.erase i
  have hi : i ∈ s := Finset.orderEmbOfFin_mem s rfl j
  have htcard : t.card = s.card - 1 := by
    dsimp [t]
    exact Finset.card_erase_of_mem hi
  have hposmem : ∀ x : Fin (s.card - 1),
      finDeleteOrderEmb j x ≠ j := by
    intro x
    have hx := Finset.orderEmbOfFin_mem ({j}ᶜ : Finset (Fin s.card))
      (by simp [Finset.card_compl]) x
    have hx' := Finset.mem_compl.mp hx
    simpa only [Finset.mem_singleton] using hx'
  let compEmb : Fin (s.card - 1) ↪o Fin n :=
    (finDeleteOrderEmb j).trans (s.orderEmbOfFin rfl)
  have hcompmem : ∀ x, compEmb x ∈ t := by
    intro x
    simp only [t, Finset.mem_erase]
    constructor
    · intro hx
      apply hposmem x
      apply (s.orderEmbOfFin rfl).injective
      exact hx
    · exact Finset.orderEmbOfFin_mem s rfl (finDeleteOrderEmb j x)
  have hcomp : compEmb = t.orderEmbOfFin htcard :=
    Finset.orderEmbOfFin_unique' htcard hcompmem
  have hfamily :
      deleteFamilyAtFin (restrictFamilyToFinset A s) j =
        fun a ↦ (A a).submatrix (t.orderEmbOfFin htcard)
          (t.orderEmbOfFin htcard) := by
    funext a
    ext x y
    change A a (compEmb x) (compEmb y) =
      A a (t.orderEmbOfFin htcard x) (t.orderEmbOfFin htcard y)
    rw [hcomp]
  have hcastFamily :
      reindexFamilyByFinCast htcard (restrictFamilyToFinset A t) =
        fun a ↦ (A a).submatrix (t.orderEmbOfFin htcard)
          (t.orderEmbOfFin htcard) := by
    funext a
    ext x y
    change A a
      (t.orderEmbOfFin rfl ((Fin.castOrderIso htcard).symm x))
      (t.orderEmbOfFin rfl ((Fin.castOrderIso htcard).symm y)) =
        A a (t.orderEmbOfFin htcard x) (t.orderEmbOfFin htcard y)
    congr 1
  change restrictedMDP A hA t = _
  rw [restrictedMDP]
  calc
    realMixedDeterminantalPolynomial (restrictFamilyToFinset A t)
        (restrictFamilyToFinset_isHermitian hA t) =
      realMixedDeterminantalPolynomial
        (reindexFamilyByFinCast htcard (restrictFamilyToFinset A t))
        (reindexFamilyByFinCast_isHermitian htcard
          (restrictFamilyToFinset_isHermitian hA t)) :=
      realMixedDeterminantalPolynomial_reindexFamilyByFinCast
        htcard (restrictFamilyToFinset A t)
          (restrictFamilyToFinset_isHermitian hA t)
    _ = realMixedDeterminantalPolynomial
        (fun a ↦ (A a).submatrix (t.orderEmbOfFin htcard)
          (t.orderEmbOfFin htcard))
        (fun a ↦ (hA a).submatrix (t.orderEmbOfFin htcard)) :=
      realMixedDeterminantalPolynomial_congr _ _ _ _ hcastFamily
    _ = realMixedDeterminantalPolynomial
        (deleteFamilyAtFin (restrictFamilyToFinset A s) j)
        (deleteFamilyAtFin_isHermitian
          (restrictFamilyToFinset_isHermitian hA s) j) :=
      realMixedDeterminantalPolynomial_congr _ _ _ _ hfamily.symm

/-! ## The concrete deletion identity -/

/-- The exact deletion-derivative identity required by the concrete
conditional MDP tree.  This discharges `MDPDeletionDerivativeIdentity` for
every nonempty matrix family (`k > 0`) using only determinant algebra and
finite reindexing. -/
theorem mdpDeletionDerivativeIdentity_of_pos
    {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    MDPDeletionDerivativeIdentity A hA := by
  intro s
  rw [restrictedMDP]
  rw [derivative_realMixedDeterminantalPolynomial_eq_sum_deleteFamilyAtFin
    hk (restrictFamilyToFinset A s)
      (restrictFamilyToFinset_isHermitian hA s)]
  exact Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv
    (fun j ↦ realMixedDeterminantalPolynomial
      (deleteFamilyAtFin (restrictFamilyToFinset A s) j)
      (deleteFamilyAtFin_isHermitian
        (restrictFamilyToFinset_isHermitian hA s) j))
    (fun i ↦ restrictedMDP A hA (s.erase i.1))
    (by
      intro j
      simpa only [Finset.coe_orderIsoOfFin_apply] using
        (restrictedMDP_erase_orderEmb_eq_deleteFamilyAtFin A hA s j).symm)

end CommutatorTheorem.BTMDPDeletionIdentity
