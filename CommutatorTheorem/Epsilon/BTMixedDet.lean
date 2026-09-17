import Mathlib

/-!
# Finite coloring and averaged characteristic-polynomial harness

This file isolates the finite-dimensional algebraic layer used by mixed
determinantal-polynomial approaches to restricted invertibility.  It contains no
analytic root bound and introduces no axioms.
-/

open scoped BigOperators Polynomial

namespace CommutatorTheorem.BTMixedDet

/-- An `r`-coloring of `n` coordinates. -/
abbrev Coloring (n r : ℕ) := Fin n → Fin r

/-- The coordinates carrying a specified color. -/
abbrev ColorFiber {n r : ℕ} (c : Coloring n r) (a : Fin r) :=
  {i : Fin n // c i = a}

/-- The genuine principal compression to a color fiber. -/
def principalCompression {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) :
    Matrix (ColorFiber c a) (ColorFiber c a) ℂ :=
  A.submatrix Subtype.val Subtype.val

@[simp] lemma principalCompression_apply {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n r) (a : Fin r)
    (i j : ColorFiber c a) :
    principalCompression A c a i j = A i.1 j.1 := rfl

lemma principalCompression_isHermitian {n r : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (c : Coloring n r) (a : Fin r) :
    (principalCompression A c a).IsHermitian :=
  hA.submatrix Subtype.val

lemma trace_principalCompression {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n r) (a : Fin r) :
    (principalCompression A c a).trace =
      ∑ i : ColorFiber c a, A i.1 i.1 := by
  rfl

/-- Compress every member of a finite Hermitian family to the same color fiber. -/
def compressedFamily {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) (j : Fin k) :
    Matrix (ColorFiber c a) (ColorFiber c a) ℂ :=
  principalCompression (A j) c a

lemma compressedFamily_isHermitian {n r k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ j, (A j).IsHermitian) (c : Coloring n r) (a : Fin r) (j : Fin k) :
    (compressedFamily A c a j).IsHermitian :=
  principalCompression_isHermitian (hA j) c a

/-- Fixed-size version of a principal compression: entries outside the chosen
color are zero.  Keeping the ambient `Fin n` makes all characteristic polynomials
have the same degree. -/
def maskedCompression {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if c i = a ∧ c j = a then A i j else 0

@[simp] lemma maskedCompression_apply {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n r) (a : Fin r)
    (i j : Fin n) :
    maskedCompression A c a i j = if c i = a ∧ c j = a then A i j else 0 := rfl

lemma maskedCompression_isHermitian {n r : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (c : Coloring n r) (a : Fin r) :
    (maskedCompression A c a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hi : c i = a <;> by_cases hj : c j = a <;>
    simp [maskedCompression, hi, hj, hA.apply]

lemma trace_maskedCompression {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n r) (a : Fin r) :
    (maskedCompression A c a).trace =
      ∑ i : Fin n, if c i = a then A i i else 0 := by
  simp [Matrix.trace, maskedCompression]

/-- Sum of the masked compressions of a finite matrix family. -/
noncomputable def jointMaskedCompression {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ j, maskedCompression (A j) c a

lemma jointMaskedCompression_isHermitian {n r k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ j, (A j).IsHermitian) (c : Coloring n r) (a : Fin r) :
    (jointMaskedCompression A c a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [jointMaskedCompression, Matrix.sum_apply]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact (maskedCompression_isHermitian (hA t) c a).apply i j

lemma trace_jointMaskedCompression {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) :
    (jointMaskedCompression A c a).trace =
      ∑ i : Fin n, if c i = a then ∑ j : Fin k, A j i i else 0 := by
  rw [jointMaskedCompression, Matrix.trace_sum]
  simp_rw [trace_maskedCompression]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : c i = a <;> simp [hi]

/-- Uniform average of the fixed-size characteristic polynomials over all colorings. -/
noncomputable def averageCharpoly {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) : ℂ[X] :=
  ((Fintype.card (Coloring n r) : ℂ)⁻¹) •
    ∑ c : Coloring n r, (jointMaskedCompression A c a).charpoly

/-- Uniform average of the corresponding traces. -/
noncomputable def averageTrace {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) : ℂ :=
  ((Fintype.card (Coloring n r) : ℂ)⁻¹) *
    ∑ c : Coloring n r, (jointMaskedCompression A c a).trace

private lemma charpoly_coeff_dim {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.coeff n = 1 := by
  simpa using M.charpoly_monic.coeff_natDegree

lemma averageCharpoly_natDegree_le {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).natDegree ≤ n := by
  rw [averageCharpoly]
  apply le_trans (Polynomial.natDegree_smul_le _ _)
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro c _
  simp

lemma coloring_card (n r : ℕ) : Fintype.card (Coloring n r) = r ^ n := by
  simp [Coloring]

lemma averageCharpoly_coeff_dim {n r k : ℕ} (hr : 0 < r)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).coeff n = 1 := by
  classical
  have hcoeff :
      (∑ c : Coloring n r, (jointMaskedCompression A c a).charpoly).coeff n =
        ∑ c : Coloring n r, (jointMaskedCompression A c a).charpoly.coeff n := by
    let S : Finset (Coloring n r) := Finset.univ
    change (∑ c ∈ S, (jointMaskedCompression A c a).charpoly).coeff n =
      ∑ c ∈ S, (jointMaskedCompression A c a).charpoly.coeff n
    induction S using Finset.induction_on with
    | empty => simp
    | @insert c S hc ih => simp [Finset.sum_insert hc, ih]
  rw [averageCharpoly, Polynomial.coeff_smul]
  rw [hcoeff]
  simp_rw [charpoly_coeff_dim]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, coloring_card]
  rw [smul_eq_mul]
  have hrpow : r ^ n ≠ 0 := pow_ne_zero n (Nat.ne_of_gt hr)
  have hrpowC : ((r ^ n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hrpow
  exact inv_mul_cancel₀ hrpowC

theorem averageCharpoly_monic {n r k : ℕ} (hr : 0 < r)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
    (averageCharpoly_natDegree_le A a) (averageCharpoly_coeff_dim hr A a)

/-! ## The first lower coefficient and its coloring average -/

/-- The coefficient immediately below the leading coefficient of a matrix
characteristic polynomial is minus its trace.  In dimension zero the exponent
`n - 1` is still zero, so it selects the constant coefficient of the polynomial
`1`; the conditional records this unavoidable boundary case. -/
lemma charpoly_coeff_pred_dim {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.coeff (n - 1) = if n = 0 then 1 else -M.trace := by
  cases n with
  | zero => simp
  | succ n =>
      have h := Matrix.trace_eq_neg_charpoly_coeff M
      simpa using (congrArg Neg.neg h).symm

private lemma sum_coloring_indicator {n r : ℕ} (i : Fin n) (a : Fin r) (z : ℂ) :
    (∑ c : Coloring n r, if c i = a then z else 0) = (r ^ (n - 1) : ℕ) • z := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  congr 1
  simpa [Coloring] using
    (Fintype.card_filter_piFinset_const_eq_of_mem
      (s := (Finset.univ : Finset (Fin r))) i (x := a) (Finset.mem_univ a))

private lemma card_colorings_two_coordinates {n r : ℕ} (i l : Fin n) (hil : i ≠ l)
    (a : Fin r) :
    (Finset.univ.filter fun c : Coloring n r ↦ c i = a ∧ c l = a).card = r ^ (n - 2) := by
  classical
  let s : Fin n → Finset (Fin r) :=
    Function.update (Function.update (fun _ ↦ Finset.univ) i {a}) l {a}
  have hs : Fintype.piFinset s =
      Finset.univ.filter fun c : Coloring n r ↦ c i = a ∧ c l = a := by
    ext c
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hc
      constructor
      · simpa [s, hil] using hc i
      · simpa [s] using hc l
    · rintro ⟨hci, hcl⟩ q
      by_cases hql : q = l
      · subst q
        simp [s, hcl]
      · by_cases hqi : q = i
        · subst q
          simp [s, hil, hci]
        · simp [s, hql, hqi]
  rw [← hs, Fintype.card_piFinset]
  dsimp only [s]
  have hcardfun :
      (fun q : Fin n ↦
        (Function.update (Function.update (fun _ ↦ (Finset.univ : Finset (Fin r))) i {a})
          l {a} q).card) =
        Function.update (Function.update (fun _ : Fin n ↦ r) i 1) l 1 := by
    funext q
    by_cases hql : q = l
    · subst q
      simp
    · by_cases hqi : q = i
      · subst q
        simp [hil]
      · simp [hql, hqi]
  rw [hcardfun]
  rw [Finset.prod_update_of_mem (Finset.mem_univ l)]
  simp only [one_mul]
  have hi : i ∈ (Finset.univ : Finset (Fin n)) \ {l} := by simp [hil]
  rw [Finset.prod_update_of_mem hi]
  simp only [one_mul, Finset.prod_const]
  congr 1
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hi,
    Finset.sdiff_singleton_eq_erase,
    Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin]
  omega

/-- A fixed coordinate receives a fixed color in exactly `r^(n-1)` colorings. -/
lemma sum_coloring_indicator_one {n r : ℕ} (i : Fin n) (a : Fin r) :
    (∑ c : Coloring n r, if c i = a then (1 : ℂ) else 0) = (r ^ (n - 1) : ℕ) := by
  simpa using sum_coloring_indicator i a (1 : ℂ)

private lemma sum_coloring_indicator_two {n r : ℕ} (i l : Fin n) (hil : i ≠ l)
    (a : Fin r) (z : ℂ) :
    (∑ c : Coloring n r, if c i = a ∧ c l = a then z else 0) =
      (r ^ (n - 2) : ℕ) • z := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  congr 1
  exact card_colorings_two_coordinates i l hil a

/-- Uniformly averaged two-coordinate weight.  This is the finite probability
space needed for second-moment and second Newton-coefficient computations. -/
noncomputable def averagePairWeight {n r : ℕ} (w : Fin n → Fin n → ℂ)
    (a : Fin r) : ℂ :=
  ((Fintype.card (Coloring n r) : ℂ)⁻¹) *
    ∑ c : Coloring n r, ∑ i : Fin n, ∑ l : Fin n,
      if c i = a ∧ c l = a then w i l else 0

/-- Off-diagonal two-coordinate terms survive the color mask with probability
`1 / r²`.  The zero-diagonal assumption precisely removes the exceptional
`i = l` terms, which survive with probability `1 / r`. -/
theorem averagePairWeight_of_diagonal_eq_zero {n r : ℕ} (hn : 2 ≤ n)
    (w : Fin n → Fin n → ℂ) (hdiag : ∀ i, w i i = 0) (a : Fin r) :
    averagePairWeight w a = ((r : ℂ) ^ 2)⁻¹ * ∑ i : Fin n, ∑ l : Fin n, w i l := by
  classical
  have hr : 0 < r := Fin.pos_iff_nonempty.mpr ⟨a⟩
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hcount :
      (∑ c : Coloring n r, ∑ i : Fin n, ∑ l : Fin n,
        if c i = a ∧ c l = a then w i l else 0) =
        (r ^ (n - 2) : ℕ) • ∑ i : Fin n, ∑ l : Fin n, w i l := by
    rw [Finset.sum_comm, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hil : i = l
    · subst l
      simp [hdiag]
    · exact sum_coloring_indicator_two i l hil a (w i l)
  rw [averagePairWeight, hcount, coloring_card]
  simp only [nsmul_eq_mul]
  push_cast
  have hpow : (r : ℂ) ^ n = (r : ℂ) ^ 2 * (r : ℂ) ^ (n - 2) := by
    rw [← pow_add, Nat.add_sub_of_le hn]
  rw [hpow]
  field_simp

/-! ## The second Newton numerator -/

/-- Sum of the input family before applying a common color mask. -/
noncomputable def familySum {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ j, A j

@[simp] lemma familySum_apply {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (i l : Fin n) :
    familySum A i l = ∑ j : Fin k, A j i l := by
  simp only [familySum, Matrix.sum_apply]

lemma jointMaskedCompression_apply {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) (i l : Fin n) :
    jointMaskedCompression A c a i l =
      if c i = a ∧ c l = a then familySum A i l else 0 := by
  simp only [jointMaskedCompression, Matrix.sum_apply]
  by_cases h : c i = a ∧ c l = a <;>
    simp [maskedCompression_apply, familySum_apply, h]

/-- The numerator in the degree-two Newton identity:
`2 e₂ = trace(M)² - trace(M²)`. -/
noncomputable def secondNewtonNumerator {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  M.trace ^ 2 - (M * M).trace

private lemma secondNewtonNumerator_eq_sum {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    secondNewtonNumerator M =
      ∑ i : Fin n, ∑ l : Fin n, (M i i * M l l - M i l * M l i) := by
  simp only [secondNewtonNumerator, Matrix.trace, Matrix.mul_apply, pow_two,
    Matrix.diag_apply, Finset.mul_sum, Finset.sum_sub_distrib, mul_comm]

/-- The off-diagonal kernel whose sum is the second Newton numerator. -/
def secondNewtonKernel {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (i l : Fin n) : ℂ :=
  M i i * M l l - M i l * M l i

@[simp] lemma secondNewtonKernel_diag {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    secondNewtonKernel M i i = 0 := by
  simp [secondNewtonKernel]

lemma secondNewtonNumerator_jointMaskedCompression {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) :
    secondNewtonNumerator (jointMaskedCompression A c a) =
      ∑ i : Fin n, ∑ l : Fin n,
        if c i = a ∧ c l = a then secondNewtonKernel (familySum A) i l else 0 := by
  rw [secondNewtonNumerator_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hi : c i = a <;> by_cases hl : c l = a <;>
    simp [jointMaskedCompression_apply, secondNewtonKernel, hi, hl]

/-- Uniform average of the second Newton numerator over all common masks. -/
noncomputable def averageSecondNewtonNumerator {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) : ℂ :=
  ((Fintype.card (Coloring n r) : ℂ)⁻¹) *
    ∑ c : Coloring n r, secondNewtonNumerator (jointMaskedCompression A c a)

/-- Second-moment counting closes exactly: in dimension at least two, the
averaged second Newton numerator is `1 / r²` times that of the unmasked family
sum.  Equivalently, the same-color probability for every genuine two-index
term is `1 / r²`. -/
theorem averageSecondNewtonNumerator_eq {n r k : ℕ} (hn : 2 ≤ n)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    averageSecondNewtonNumerator A a =
      ((r : ℂ) ^ 2)⁻¹ * secondNewtonNumerator (familySum A) := by
  rw [averageSecondNewtonNumerator]
  simp_rw [secondNewtonNumerator_jointMaskedCompression]
  change averagePairWeight (secondNewtonKernel (familySum A)) a = _
  rw [averagePairWeight_of_diagonal_eq_zero hn _ (secondNewtonKernel_diag _) a]
  rw [secondNewtonNumerator_eq_sum]
  rfl

/-- Closed form for the uniform coloring average of the trace.  Each diagonal
coordinate survives with probability `1 / r`. -/
theorem averageTrace_eq_inv_mul_sum_trace {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    averageTrace A a = (r : ℂ)⁻¹ * ∑ j : Fin k, (A j).trace := by
  classical
  have hr : 0 < r := Fin.pos_iff_nonempty.mpr ⟨a⟩
  by_cases hn : n = 0
  · subst n
    simp [averageTrace]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [averageTrace]
    simp_rw [trace_jointMaskedCompression]
    rw [Finset.sum_comm]
    simp_rw [sum_coloring_indicator]
    rw [coloring_card]
    simp only [nsmul_eq_mul]
    rw [← Finset.mul_sum]
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    have hpow : (r : ℂ) ^ n = (r : ℂ) * (r : ℂ) ^ (n - 1) := by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp [pow_succ']
    push_cast
    rw [hpow]
    field_simp
    rw [Finset.sum_comm]
    rfl

/-- In positive dimension the next coefficient of the averaged characteristic
polynomial is minus the averaged trace. -/
lemma averageCharpoly_coeff_pred_dim {n r k : ℕ} (hn : 0 < n)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 1) = -averageTrace A a := by
  classical
  simp [averageCharpoly, averageTrace, charpoly_coeff_pred_dim, hn.ne']

/-- Boundary-aware form of the preceding coefficient identity.  At `n = 0`,
`n - 1 = 0` and the averaged characteristic polynomial is the constant `1`. -/
theorem averageCharpoly_coeff_pred_dim_boundary {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 1) =
      if n = 0 then 1 else -averageTrace A a := by
  by_cases hn : n = 0
  · subst n
    simpa using averageCharpoly_coeff_dim (Fin.pos_iff_nonempty.mpr ⟨a⟩) A a
  · simpa [hn] using averageCharpoly_coeff_pred_dim (Nat.pos_of_ne_zero hn) A a

/-- Combining the coefficient identity with the closed trace count gives an
explicit first lower coefficient for the averaged characteristic polynomial. -/
theorem averageCharpoly_coeff_pred_dim_eq {n r k : ℕ} (hn : 0 < n)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 1) =
      -((r : ℂ)⁻¹ * ∑ j : Fin k, (A j).trace) := by
  rw [averageCharpoly_coeff_pred_dim hn, averageTrace_eq_inv_mul_sum_trace]

/-! ## The degree-two characteristic-polynomial coefficient -/

private lemma two_mul_esymm_two (s : Multiset ℂ) :
    2 * s.esymm 2 = s.sum ^ 2 - (s.map fun z ↦ z ^ 2).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm]
  | cons z s ih =>
      have hesymm : (z ::ₘ s).esymm 2 = s.esymm 2 + z * s.sum := by
        simp only [Multiset.esymm, Multiset.powersetCard_cons, Nat.reduceAdd,
          Multiset.powersetCard_one, Multiset.map_map, Function.comp_apply, Multiset.map_add,
          Multiset.prod_cons, Multiset.prod_singleton, Multiset.sum_add, add_right_inj]
        rw [Multiset.sum_map_mul_left]
        simp
      rw [hesymm, mul_add, ih]
      simp only [Multiset.sum_cons, Multiset.map_cons]
      ring

private lemma trace_mul_self_eq_sum_eigenvalues_sq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
    (M * M).trace = ∑ i : Fin n, (hM.eigenvalues i : ℂ) ^ 2 := by
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
  let U := hM.eigenvectorUnitary
  calc
    (M * M).trace =
        ((Unitary.conjStarAlgAut ℂ _ U D) * (Unitary.conjStarAlgAut ℂ _ U D)).trace := by
          rw [hM.spectral_theorem]
    _ = (Unitary.conjStarAlgAut ℂ _ U (D * D)).trace := by
          rw [map_mul]
    _ = (D * D).trace := by
          simp only [Unitary.conjStarAlgAut_apply]
          rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
    _ = ∑ i : Fin n, (hM.eigenvalues i : ℂ) ^ 2 := by
          simp [D, Matrix.trace, pow_two]

/-- For a Hermitian matrix in dimension at least two, the `x^(n-2)`
characteristic-polynomial coefficient is the second Newton numerator divided by
two. -/
theorem charpoly_coeff_sub_two_eq_secondNewtonNumerator_div {n : ℕ} (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
    M.charpoly.coeff (n - 2) = secondNewtonNumerator M / 2 := by
  have hdeg : M.charpoly.natDegree = n := by simp
  have hle : n - 2 ≤ M.charpoly.natDegree := by rw [hdeg]; omega
  have hcoeff := Polynomial.coeff_eq_esymm_roots_of_splits
    (k := n - 2) hM.splits_charpoly hle
  have hsub : n - (n - 2) = 2 := by omega
  have hc : M.charpoly.coeff (n - 2) = M.charpoly.roots.esymm 2 := by
    simpa [hdeg, hsub, M.charpoly_monic.leadingCoeff] using hcoeff
  rw [hc]
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  rw [mul_comm, two_mul_esymm_two]
  have htrace : M.trace = M.charpoly.roots.sum :=
    Matrix.trace_eq_sum_roots_charpoly M
  have hsquares : (M.charpoly.roots.map fun z ↦ z ^ 2).sum = (M * M).trace := by
    rw [trace_mul_self_eq_sum_eigenvalues_sq M hM, hM.roots_charpoly_eq_eigenvalues]
    simp [Function.comp_def, List.sum_ofFn]
  rw [← htrace, hsquares]
  rfl

/-- Boundary-aware second-lower-coefficient formula.  At dimension zero the
truncated exponent selects the coefficient of the constant polynomial `1`; at
dimension one it selects the ordinary constant coefficient, namely minus the
trace. -/
theorem charpoly_coeff_sub_two_boundary {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
    M.charpoly.coeff (n - 2) =
      if n = 0 then 1
      else if n = 1 then -M.trace
      else secondNewtonNumerator M / 2 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · by_cases hn1 : n = 1
    · subst n
      simpa using charpoly_coeff_pred_dim M
    · have hn2 : 2 ≤ n := by omega
      simpa [hn0, hn1] using
        charpoly_coeff_sub_two_eq_secondNewtonNumerator_div hn2 M hM

lemma familySum_isHermitian {n k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ} (hA : ∀ j, (A j).IsHermitian) :
    (familySum A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i l
  simp only [familySum, Matrix.sum_apply, star_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (hA j).apply i l

/-- In dimension at least two, the averaged `x^(n-2)` coefficient has the
closed second-moment form predicted by the common-color calculation. -/
theorem averageCharpoly_coeff_sub_two_eq_secondNewtonNumerator {n r k : ℕ}
    (hn : 2 ≤ n) (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ j, (A j).IsHermitian) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 2) =
      ((r : ℂ) ^ 2)⁻¹ * secondNewtonNumerator (familySum A) / 2 := by
  classical
  calc
    (averageCharpoly A a).coeff (n - 2) =
        ((Fintype.card (Coloring n r) : ℂ)⁻¹) *
          ∑ c : Coloring n r,
            (jointMaskedCompression A c a).charpoly.coeff (n - 2) := by
              simp [averageCharpoly]
    _ = ((Fintype.card (Coloring n r) : ℂ)⁻¹) *
          ∑ c : Coloring n r,
            secondNewtonNumerator (jointMaskedCompression A c a) / 2 := by
              congr 1
              apply Finset.sum_congr rfl
              intro c _
              exact charpoly_coeff_sub_two_eq_secondNewtonNumerator_div hn _
                (jointMaskedCompression_isHermitian hA c a)
    _ = averageSecondNewtonNumerator A a / 2 := by
          rw [averageSecondNewtonNumerator]
          simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_assoc]
    _ = ((r : ℂ) ^ 2)⁻¹ * secondNewtonNumerator (familySum A) / 2 := by
          rw [averageSecondNewtonNumerator_eq hn]

/-- Equivalent coefficient-only form: common masking multiplies the second
lower characteristic-polynomial coefficient of the family sum by `1 / r²`. -/
theorem averageCharpoly_coeff_sub_two_eq_inv_sq_mul {n r k : ℕ}
    (hn : 2 ≤ n) (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ j, (A j).IsHermitian) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 2) =
      ((r : ℂ) ^ 2)⁻¹ * (familySum A).charpoly.coeff (n - 2) := by
  rw [averageCharpoly_coeff_sub_two_eq_secondNewtonNumerator hn A hA a]
  rw [charpoly_coeff_sub_two_eq_secondNewtonNumerator_div hn _ (familySum_isHermitian hA)]
  rw [mul_div_assoc]

/-- Complete boundary description for the averaged second-lower coefficient.
The degree-two Newton formula starts only at `n = 2`; dimensions zero and one
are the two explicit exceptional cases. -/
theorem averageCharpoly_coeff_sub_two_boundary {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ j, (A j).IsHermitian) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 2) =
      if n = 0 then 1
      else if n = 1 then -averageTrace A a
      else ((r : ℂ) ^ 2)⁻¹ * secondNewtonNumerator (familySum A) / 2 := by
  by_cases hn0 : n = 0
  · subst n
    simpa using averageCharpoly_coeff_dim (Fin.pos_iff_nonempty.mpr ⟨a⟩) A a
  · by_cases hn1 : n = 1
    · subst n
      simpa using averageCharpoly_coeff_pred_dim (by omega) A a
    · have hn2 : 2 ≤ n := by omega
      simpa [hn0, hn1] using
        averageCharpoly_coeff_sub_two_eq_secondNewtonNumerator hn2 A hA a

end CommutatorTheorem.BTMixedDet
