import CommutatorTheorem.Epsilon.BTFellPair
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Descartes continuity infrastructure for the Fell converse

The root-disjoint Fell step can be expressed as constancy of the number of
roots on either side of a fixed point along a real-rooted affine pencil.  The
lemmas here develop a coefficient-side route to that constancy.  The key
finite observation is that inserting additional nonzero signs into a
coefficient sign word cannot decrease its number of sign changes.
-/

open scoped Polynomial Topology

namespace CommutatorTheorem.BTFellDescartes

open Polynomial

/-- The nonzero coefficient signs, in descending degree order. -/
noncomputable def nonzeroCoeffSigns (p : ℝ[X]) : List SignType :=
  (p.coeffList.map SignType.sign).filter (· ≠ 0)

/-- Every nonzero coefficient sign of `p` occurs, in the same order, among
the nonzero coefficient signs of `q`.  This is the relation obtained by
perturbing coefficients that vanish in `p` while preserving all other
coefficient signs. -/
def CoeffSignRefines (p q : ℝ[X]) : Prop :=
  List.Sublist (nonzeroCoeffSigns p) (nonzeroCoeffSigns q)

theorem signVariations_eq_destutter_length_sub_one (p : ℝ[X]) :
    p.signVariations =
      ((nonzeroCoeffSigns p).destutter (· ≠ ·)).length - 1 := by
  rfl

/-- Inserting nonzero signs cannot decrease the number of sign changes. -/
theorem signVariations_le_of_coeffSignRefines {p q : ℝ[X]}
    (h : CoeffSignRefines p q) :
    p.signVariations ≤ q.signVariations := by
  rw [signVariations_eq_destutter_length_sub_one,
    signVariations_eq_destutter_length_sub_one]
  apply Nat.sub_le_sub_right
  apply List.IsChain.length_le_length_destutter_ne
  · exact (List.destutter_sublist _ _).trans h
  · exact List.isChain_destutter _ _

/-- The number of coefficient sign changes never exceeds the polynomial's
natural degree.  This is the elementary upper bound complementary to
Descartes' lower bound by the number of positive roots. -/
theorem signVariations_le_natDegree (p : ℝ[X]) :
    p.signVariations ≤ p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [signVariations_eq_destutter_length_sub_one]
  calc
    ((nonzeroCoeffSigns p).destutter (· ≠ ·)).length - 1 ≤
        (nonzeroCoeffSigns p).length - 1 :=
      Nat.sub_le_sub_right (List.destutter_sublist _ _).length_le 1
    _ ≤ p.coeffList.length - 1 := by
      apply Nat.sub_le_sub_right
      simpa [nonzeroCoeffSigns] using
        List.length_filter_le (fun s : SignType ↦ s ≠ 0)
          (p.coeffList.map SignType.sign)
    _ = p.natDegree := by
      simp [Polynomial.length_coeffList_eq_ite, hp]

/-- Entrywise description of the descending coefficient list. -/
theorem coeffList_getElem_eq_coeff_natDegree_sub
    {p : ℝ[X]} (hp : p ≠ 0) (i : ℕ) (hi : i < p.coeffList.length) :
    p.coeffList[i] = p.coeff (p.natDegree - i) := by
  simp [Polynomial.coeffList,
    withBotSucc_degree_eq_natDegree_add_one hp] at hi ⊢

/-- Over `ℝ`, differentiation lowers every positive natural degree by
exactly one. -/
theorem natDegree_derivative_eq_sub_one
    {p : ℝ[X]} (hpdeg : 0 < p.natDegree) :
    p.derivative.natDegree = p.natDegree - 1 := by
  have hdne : p.derivative ≠ 0 := by
    intro hzero
    have hdegzero : p.derivative.degree = ⊥ := by simp [hzero]
    rw [degree_derivative_eq p hpdeg] at hdegzero
    simp at hdegzero
  exact (degree_eq_iff_natDegree_eq hdne).mp (degree_derivative_eq p hpdeg)

/-- After discarding coefficient magnitudes, differentiation removes exactly
the constant-term entry from the descending coefficient word. -/
theorem coeffSignWord_derivative_eq_dropLast
    {p : ℝ[X]} (hpdeg : 0 < p.natDegree) :
    p.derivative.coeffList.map SignType.sign =
      (p.coeffList.map SignType.sign).dropLast := by
  have hp : p ≠ 0 := by
    intro hzero
    simp [hzero] at hpdeg
  have hdne : p.derivative ≠ 0 := by
    intro hzero
    have := natDegree_eq_zero_of_derivative_eq_zero hzero
    omega
  have hddegree := natDegree_derivative_eq_sub_one hpdeg
  apply List.ext_getElem
  · simp [Polynomial.length_coeffList_eq_ite, hp, hdne, hddegree]
    omega
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_dropLast]
    rw [coeffList_getElem_eq_coeff_natDegree_sub hdne,
      coeffList_getElem_eq_coeff_natDegree_sub hp]
    simp only [coeff_derivative, hddegree]
    have hiDle : i ≤ p.natDegree - 1 := by
      simpa [Polynomial.length_coeffList_eq_ite, hdne, hddegree] using hi
    have hiD : i < p.natDegree := by omega
    have hindex : p.natDegree - 1 - i + 1 = p.natDegree - i := by omega
    rw [hindex]
    have hfactor : (0 : ℝ) <
        ((p.natDegree - 1 - i : ℕ) : ℝ) + 1 := by positivity
    rw [sign_mul, sign_pos hfactor, mul_one]

/-- Multiplication by `X` appends a zero constant coefficient to the
descending coefficient list. -/
theorem coeffList_mul_X_eq_append_zero
    {p : ℝ[X]} (hp : p ≠ 0) :
    (p * X).coeffList = p.coeffList ++ [0] := by
  have hmul : p * X ≠ 0 := mul_ne_zero hp X_ne_zero
  have hdeg : (p * X).natDegree = p.natDegree + 1 := by
    simp [natDegree_mul hp X_ne_zero]
  apply List.ext_getElem
  · simp [Polynomial.length_coeffList_eq_ite, hp, hmul, hdeg]
  · intro i hi hi'
    by_cases hip : i < p.coeffList.length
    · rw [List.getElem_append_left hip]
      rw [coeffList_getElem_eq_coeff_natDegree_sub hmul,
        coeffList_getElem_eq_coeff_natDegree_sub hp, hdeg]
      have hiNat : i ≤ p.natDegree := by
        simpa [Polynomial.length_coeffList_eq_ite, hp] using hip
      have hindex : p.natDegree + 1 - i = p.natDegree - i + 1 := by
        omega
      rw [hindex, coeff_mul_X]
    · have hieq : i = p.coeffList.length := by
        simp only [List.length_append, List.length_cons, List.length_nil,
          Nat.add_zero] at hi'
        omega
      subst i
      simp [coeffList_getElem_eq_coeff_natDegree_sub hmul, hdeg,
        Polynomial.length_coeffList_eq_ite, hp, coeff_mul_X]

/-- Appending the zero introduced by multiplication with `X` does not alter
the nonzero coefficient sign word. -/
theorem nonzeroCoeffSigns_mul_X {p : ℝ[X]} (hp : p ≠ 0) :
    nonzeroCoeffSigns (p * X) = nonzeroCoeffSigns p := by
  unfold nonzeroCoeffSigns
  rw [coeffList_mul_X_eq_append_zero hp, List.map_append,
    List.filter_append]
  simp

/-- Multiplication by `X` preserves coefficient sign variations. -/
theorem signVariations_mul_X {p : ℝ[X]} (hp : p ≠ 0) :
    (p * X).signVariations = p.signVariations := by
  simp only [signVariations_eq_destutter_length_sub_one,
    nonzeroCoeffSigns_mul_X hp]

/-- If the constant coefficient is nonzero, filtering zero coefficient signs
commutes with the preceding removal of the constant-term entry. -/
theorem nonzeroCoeffSigns_derivative_eq_dropLast
    {p : ℝ[X]} (hpdeg : 0 < p.natDegree)
    (hconst : p.coeff 0 ≠ 0) :
    nonzeroCoeffSigns p.derivative = (nonzeroCoeffSigns p).dropLast := by
  have hp : p ≠ 0 := by
    intro hzero
    simp [hzero] at hpdeg
  have hclne : p.coeffList ≠ [] := by
    simpa using hp
  have hlast : p.coeffList.getLast hclne = p.coeff 0 := by
    rw [List.getLast_eq_getElem]
    rw [coeffList_getElem_eq_coeff_natDegree_sub hp]
    simp [Polynomial.length_coeffList_eq_ite, hp]
  have hdecomp : p.coeffList =
      p.coeffList.dropLast ++ [p.coeff 0] := by
    simpa [hlast] using (p.coeffList.dropLast_append_getLast hclne).symm
  have hsignDecomp : p.coeffList.map SignType.sign =
      (p.coeffList.map SignType.sign).dropLast ++
        [SignType.sign (p.coeff 0)] := by
    rw [hdecomp]
    simp
  unfold nonzeroCoeffSigns
  rw [coeffSignWord_derivative_eq_dropLast hpdeg, hsignDecomp,
    List.filter_append]
  have hsign0 : SignType.sign (p.coeff 0) ≠ 0 := by
    simpa [sign_ne_zero] using hconst
  simp [hsign0]

/-- Appending one entry can increase the length of a destuttered list by at
most one. -/
theorem length_destutter_append_singleton_le
    {u : List SignType} (c : SignType) :
    ((u ++ [c]).destutter (· ≠ ·)).length ≤
      (u.destutter (· ≠ ·)).length + 1 := by
  induction u with
  | nil => simp
  | cons a u ih =>
      cases u with
      | nil =>
          by_cases hac : a = c <;> simp [hac]
      | cons b u =>
          by_cases hab : a = b
          · simpa [List.destutter_cons_cons, hab] using ih
          · simpa [List.destutter_cons_cons, hab] using
              Nat.succ_le_succ ih

/-- Differentiation cannot increase the number of nonzero coefficient sign
changes when the constant coefficient is nonzero. -/
theorem signVariations_derivative_le
    {p : ℝ[X]} (hpdeg : 0 < p.natDegree)
    (hconst : p.coeff 0 ≠ 0) :
    p.derivative.signVariations ≤ p.signVariations := by
  apply signVariations_le_of_coeffSignRefines
  unfold CoeffSignRefines
  rw [nonzeroCoeffSigns_derivative_eq_dropLast hpdeg hconst]
  have hne : nonzeroCoeffSigns p ≠ [] := by
    intro h
    have hp : p ≠ 0 := fun hp ↦ hconst (by simp [hp])
    have hclne : p.coeffList ≠ [] := by simpa using hp
    have hlast : p.coeffList.getLast hclne = p.coeff 0 := by
      rw [List.getLast_eq_getElem]
      rw [coeffList_getElem_eq_coeff_natDegree_sub hp]
      simp [Polynomial.length_coeffList_eq_ite, hp]
    have hsign0 : SignType.sign (p.coeff 0) ∈ nonzeroCoeffSigns p := by
      unfold nonzeroCoeffSigns
      rw [List.mem_filter]
      constructor
      · exact List.mem_map.mpr
          ⟨p.coeffList.getLast hclne, List.getLast_mem hclne,
            congrArg SignType.sign hlast⟩
      · simpa [sign_ne_zero] using hconst
    simpa [h] using hsign0
  have hsub := List.sublist_append_left (nonzeroCoeffSigns p).dropLast
    [(nonzeroCoeffSigns p).getLast hne]
  rw [List.dropLast_append_getLast hne] at hsub
  exact hsub

/-- Differentiation removes at most one coefficient sign change when the
constant coefficient is nonzero. -/
theorem signVariations_le_derivative_add_one
    {p : ℝ[X]} (hpdeg : 0 < p.natDegree)
    (hconst : p.coeff 0 ≠ 0) :
    p.signVariations ≤ p.derivative.signVariations + 1 := by
  have hne : nonzeroCoeffSigns p ≠ [] := by
    intro h
    have hp : p ≠ 0 := fun hp ↦ hconst (by simp [hp])
    have hclne : p.coeffList ≠ [] := by simpa using hp
    have hlast : p.coeffList.getLast hclne = p.coeff 0 := by
      rw [List.getLast_eq_getElem]
      rw [coeffList_getElem_eq_coeff_natDegree_sub hp]
      simp [Polynomial.length_coeffList_eq_ite, hp]
    have hsign0 : SignType.sign (p.coeff 0) ∈ nonzeroCoeffSigns p := by
      unfold nonzeroCoeffSigns
      rw [List.mem_filter]
      constructor
      · exact List.mem_map.mpr
          ⟨p.coeffList.getLast hclne, List.getLast_mem hclne,
            congrArg SignType.sign hlast⟩
      · simpa [sign_ne_zero] using hconst
    simpa [h] using hsign0
  have hdecomp : nonzeroCoeffSigns p =
      nonzeroCoeffSigns p.derivative ++
        [(nonzeroCoeffSigns p).getLast hne] := by
    rw [nonzeroCoeffSigns_derivative_eq_dropLast hpdeg hconst]
    exact (List.dropLast_append_getLast hne).symm
  rw [signVariations_eq_destutter_length_sub_one,
    signVariations_eq_destutter_length_sub_one, hdecomp]
  have hlen := length_destutter_append_singleton_le
    (u := nonzeroCoeffSigns p.derivative)
    ((nonzeroCoeffSigns p).getLast hne)
  omega

/-- For a word of nonzero signs, the parity of its number of changes is
exactly the discrepancy between its first and last signs. -/
theorem negOne_pow_destutter_length_sub_one_mul_head_eq_getLast
    (a : SignType) (u : List SignType)
    (hnz : ∀ s ∈ a :: u, s ≠ 0) :
    (-1 : SignType) ^ ((a :: u).destutter (· ≠ ·)).length.pred * a =
      (a :: u).getLast (List.cons_ne_nil a u) := by
  induction u generalizing a with
  | nil => simp
  | cons b u ih =>
      have ha : a ≠ 0 := hnz a (by simp)
      have hb : b ≠ 0 := hnz b (by simp)
      have hnz' : ∀ s ∈ b :: u, s ≠ 0 := by
        intro s hs
        exact hnz s (by simp [hs])
      by_cases hab : a = b
      · subst b
        simpa [List.destutter_cons_cons] using ih a hnz'
      · have hba : b = -a := by
          cases a <;> cases b <;> simp_all
        subst b
        have hih := ih (-a) hnz'
        simp only [List.destutter] at hih ⊢
        rw [List.destutter'_cons_pos (l := u) hab]
        simp only [List.length_cons, Nat.pred_succ]
        have hpos : 0 <
            (u.destutter' (· ≠ ·) (-a)).length :=
          List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _)
        rw [← Nat.succ_pred_eq_of_pos hpos, pow_succ]
        simpa [mul_assoc] using hih

/-- The parity form of the elementary coefficient rule of signs: the first
and last nonzero coefficient signs differ by `(-1)^signVariations`. -/
theorem negOne_pow_signVariations_mul_leadingSign_eq_constantSign
    {p : ℝ[X]} (hp : p ≠ 0) (hconst : p.coeff 0 ≠ 0) :
    (-1 : SignType) ^ p.signVariations *
        SignType.sign p.leadingCoeff = SignType.sign (p.coeff 0) := by
  obtain ⟨cs, hcoeff⟩ := Polynomial.coeffList_eq_cons_leadingCoeff hp
  have hlc : SignType.sign p.leadingCoeff ≠ 0 := by
    simpa [sign_ne_zero] using Polynomial.leadingCoeff_ne_zero.mpr hp
  have hword : nonzeroCoeffSigns p =
      SignType.sign p.leadingCoeff ::
        ((cs.map SignType.sign).filter (· ≠ 0)) := by
    unfold nonzeroCoeffSigns
    rw [hcoeff]
    simp [hlc]
  have hclne : p.coeffList ≠ [] := by simpa using hp
  have hlastCoeff : p.coeffList.getLast hclne = p.coeff 0 := by
    rw [List.getLast_eq_getElem]
    rw [coeffList_getElem_eq_coeff_natDegree_sub hp]
    simp [Polynomial.length_coeffList_eq_ite, hp]
  have hlast : (nonzeroCoeffSigns p).getLast (by simp [hword]) =
      SignType.sign (p.coeff 0) := by
    have hdecomp : p.coeffList =
        p.coeffList.dropLast ++ [p.coeff 0] := by
      simpa [hlastCoeff] using
        (p.coeffList.dropLast_append_getLast hclne).symm
    have hfilteredDecomp : nonzeroCoeffSigns p =
        ((p.coeffList.dropLast.map SignType.sign).filter (· ≠ 0)) ++
          [SignType.sign (p.coeff 0)] := by
      unfold nonzeroCoeffSigns
      rw [hdecomp, List.map_append, List.filter_append]
      simp [hconst, sign_ne_zero]
    simp [hfilteredDecomp]
  have hnz : ∀ s ∈ nonzeroCoeffSigns p, s ≠ 0 := by
    intro s hs
    simpa using (List.mem_filter.mp hs).2
  rw [hword] at hnz
  have hlastWord :
      (SignType.sign p.leadingCoeff ::
          ((cs.map SignType.sign).filter (· ≠ 0))).getLast
            (List.cons_ne_nil _ _) = SignType.sign (p.coeff 0) := by
    simpa [hword] using hlast
  rw [signVariations_eq_destutter_length_sub_one, hword]
  rw [← hlastWord]
  exact negOne_pow_destutter_length_sub_one_mul_head_eq_getLast
    (SignType.sign p.leadingCoeff)
    ((cs.map SignType.sign).filter (· ≠ 0)) hnz

/-- For a monic polynomial with nonzero constant term, the constant term has
the sign prescribed by the parity of its coefficient variations. -/
theorem negOne_pow_signVariations_mul_constant_pos
    {p : ℝ[X]} (hmonic : p.Monic) (hconst : p.coeff 0 ≠ 0) :
    0 < (-1 : ℝ) ^ p.signVariations * p.coeff 0 := by
  have hp : p ≠ 0 := hmonic.ne_zero
  have hsign :=
    negOne_pow_signVariations_mul_leadingSign_eq_constantSign hp hconst
  rw [hmonic.leadingCoeff, sign_one, mul_one] at hsign
  have hcast := congrArg (fun s : SignType ↦ (s : ℝ)) hsign
  norm_num [SignType.coe_pow] at hcast
  rw [hcast]
  rw [sign_mul_self]
  exact abs_pos.mpr hconst

/-- A pointwise sign-preservation relation on equal-length sign words. -/
def SignWordRefines (u v : List SignType) : Prop :=
  List.Forall₂ (fun a b ↦ a = 0 ∨ a = b) u v

/-- Removing zero entries from a sign word that is pointwise refined gives
a sublist of the refined nonzero word. -/
theorem filter_ne_zero_sublist_of_signWordRefines
    {u v : List SignType} (h : SignWordRefines u v) :
    List.Sublist (u.filter (· ≠ 0)) (v.filter (· ≠ 0)) := by
  induction h with
  | nil => simp
  | cons hab huv ih =>
      rename_i a b u v
      rcases hab with rfl | hab
      · by_cases hb : b = 0
        · simpa [hb] using ih
        · simpa [hb] using (ih.cons b)
      · subst b
        by_cases ha : a = 0
        · simpa [ha] using ih
        · simpa [ha] using ih.cons_cons a

/-- Pointwise preservation of every old nonzero coefficient sign implies
coefficient-sign refinement. -/
theorem coeffSignRefines_of_forall_coeff_sign
    {p q : ℝ[X]} (hdegree : p.natDegree = q.natDegree)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (h : ∀ i : ℕ, i ≤ p.natDegree →
      SignType.sign (p.coeff i) = 0 ∨
        SignType.sign (p.coeff i) = SignType.sign (q.coeff i)) :
    CoeffSignRefines p q := by
  apply filter_ne_zero_sublist_of_signWordRefines
  unfold SignWordRefines
  rw [List.forall₂_iff_get]
  constructor
  · simp [hp0, hq0, hdegree]
  · intro i hi hi'
    simp only [List.get_eq_getElem, List.getElem_map]
    have hiNatLt : i < p.natDegree + 1 := by
      simpa [Polynomial.length_coeffList_eq_ite, hp0] using hi
    have hiNat : i ≤ p.natDegree := by omega
    have hiRange : i < (List.range p.natDegree.succ).reverse.length := by
      simp only [List.length_reverse, List.length_range]
      omega
    let j := (List.range p.natDegree.succ).reverse[i]'hiRange
    have hjmem : j ∈ List.range p.natDegree.succ := by
      rw [← List.mem_reverse]
      exact List.getElem_mem _
    have hjlt : j < p.natDegree.succ := List.mem_range.mp hjmem
    have hindex : j ≤ p.natDegree := by omega
    simpa [Polynomial.coeffList, hp0, hq0, degree_eq_natDegree,
      hdegree, j] using h j hindex

end CommutatorTheorem.BTFellDescartes
