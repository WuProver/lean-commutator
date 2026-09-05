import NoEpsilon.BlockAlgebra
import NoEpsilon.Goal
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith

/-!
# Hermitian splitting and the adaptive two-commutator reduction

Every trace-zero complex matrix splits into two trace-zero Hermitian matrices, each with
operator norm bounded by the original norm. A bounded commutator theorem for Hermitian
matrices therefore implies the adaptive two-commutator input needed by the Riccati construction.

The Hermitian commutator statement below is an explicit proposition and theorem hypothesis,
not an axiom. Its full spectral-ordering proof is given in `NoEpsilon.CyclicCommutator`.
Unlike the earlier quantum-expander route, the two first factors may depend on the input.
-/

open scoped Matrix.Norms.L2Operator

namespace NoEpsilon

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hermitian real part of a complex matrix. -/
noncomputable def hermitianRealPart (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  realPart A

/-- The Hermitian imaginary part of a complex matrix. -/
noncomputable def hermitianImaginaryPart (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  imaginaryPart A

omit [Fintype ι] [DecidableEq ι] in
theorem hermitianRealPart_isHermitian (A : Matrix ι ι ℂ) :
    (hermitianRealPart A).IsHermitian :=
  (realPart A).property.isHermitian

omit [Fintype ι] [DecidableEq ι] in
theorem hermitianImaginaryPart_isHermitian (A : Matrix ι ι ℂ) :
    (hermitianImaginaryPart A).IsHermitian :=
  (imaginaryPart A).property.isHermitian

omit [Fintype ι] [DecidableEq ι] in
theorem hermitian_split (A : Matrix ι ι ℂ) :
    hermitianRealPart A + Complex.I • hermitianImaginaryPart A = A :=
  realPart_add_I_smul_imaginaryPart A

theorem hermitianRealPart_norm_le (A : Matrix ι ι ℂ) :
    ‖hermitianRealPart A‖ ≤ ‖A‖ :=
  realPart.norm_le A

theorem hermitianImaginaryPart_norm_le (A : Matrix ι ι ℂ) :
    ‖hermitianImaginaryPart A‖ ≤ ‖A‖ :=
  imaginaryPart.norm_le A

omit [DecidableEq ι] in
theorem hermitianRealPart_trace_zero (A : Matrix ι ι ℂ) (hA : Matrix.trace A = 0) :
    Matrix.trace (hermitianRealPart A) = 0 := by
  simp [hermitianRealPart, realPart_apply_coe, Matrix.trace_smul, Matrix.trace_add,
    Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, hA]

omit [DecidableEq ι] in
theorem hermitianImaginaryPart_trace_zero (A : Matrix ι ι ℂ)
    (hA : Matrix.trace A = 0) : Matrix.trace (hermitianImaginaryPart A) = 0 := by
  simp [hermitianImaginaryPart, imaginaryPart_apply_coe, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, hA]

/-- Complete same-dimension Hermitian splitting, including trace and operator-norm bounds. -/
theorem exists_hermitian_split (A : Matrix ι ι ℂ) (hA : Matrix.trace A = 0) :
    ∃ H G : Matrix ι ι ℂ,
      H.IsHermitian ∧ G.IsHermitian ∧ Matrix.trace H = 0 ∧ Matrix.trace G = 0 ∧
      ‖H‖ ≤ ‖A‖ ∧ ‖G‖ ≤ ‖A‖ ∧ A = H + Complex.I • G := by
  exact ⟨hermitianRealPart A, hermitianImaginaryPart A,
    hermitianRealPart_isHermitian A, hermitianImaginaryPart_isHermitian A,
    hermitianRealPart_trace_zero A hA, hermitianImaginaryPart_trace_zero A hA,
    hermitianRealPart_norm_le A, hermitianImaginaryPart_norm_le A, (hermitian_split A).symm⟩

/-- The bounded Hermitian single-commutator proposition, proved in `NoEpsilon.CyclicCommutator`.
The norm of the unitary is stated as at most one to include the empty index type. -/
def HermitianUnitaryCommutatorBound : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ),
    G.IsHermitian → Matrix.trace G = 0 →
      ∃ U V : Matrix (Fin n) (Fin n) ℂ,
        U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ G = ringCommutator U V ∧
          ‖U‖ ≤ 1 ∧ ‖V‖ ≤ ‖G‖

/-- The weaker quantifier order sufficient for the Riccati construction: first factors may
depend on the target. This proposition does not assert any common fixed pair for all targets. -/
def AdaptiveTwoCommutatorBound : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), Matrix.trace A = 0 →
    ∃ U K V T : Matrix (Fin n) (Fin n) ℂ,
      U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ K ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        A = ringCommutator U V + ringCommutator K T ∧
          ‖U‖ ≤ 1 ∧ ‖K‖ ≤ 1 ∧ ‖V‖ ≤ ‖A‖ ∧ ‖T‖ ≤ ‖A‖

/-- Multiplying the second factor by a complex scalar multiplies the commutator by it. -/
theorem ringCommutator_smul_right (z : ℂ) (U V : Matrix ι ι ℂ) :
    ringCommutator U (z • V) = z • ringCommutator U V := by
  simp only [ringCommutator, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- Hermitian bounded commutators suffice for the adaptive two-commutator input with constant 1.
This theorem discharges the complex/Hermitian reduction, not the Hermitian hypothesis. -/
theorem adaptiveTwoCommutatorBound_of_hermitian
    (hHermitian : HermitianUnitaryCommutatorBound) : AdaptiveTwoCommutatorBound := by
  intro n A hA
  obtain ⟨H, G, hH, hG, htrH, htrG, hnormH, hnormG, hsplit⟩ :=
    exists_hermitian_split A hA
  obtain ⟨U, V, hU, hUV, hnormU, hnormV⟩ := hHermitian n H hH htrH
  obtain ⟨K, T, hK, hKT, hnormK, hnormT⟩ := hHermitian n G hG htrG
  refine ⟨U, K, V, Complex.I • T, hU, hK, ?_, hnormU, hnormK,
    hnormV.trans hnormH, ?_⟩
  · rw [ringCommutator_smul_right, ← hUV, ← hKT]
    exact hsplit
  · simpa only [norm_smul, Complex.norm_I, one_mul] using hnormT.trans hnormG

/-- The sign-greedy step for a real zero-sum ordering: one can choose a remaining term
without leaving the same interval that bounds the individual terms and current sum. -/
theorem exists_bounded_next_term (l : List ℝ) (s M : ℝ) (hl : l ≠ [])
    (hs : |s| ≤ M) (hbound : ∀ x ∈ l, |x| ≤ M) (htotal : s + l.sum = 0) :
    ∃ x ∈ l, |s + x| ≤ M := by
  rcases abs_le.mp hs with ⟨hslo, hshi⟩
  by_cases hsign : 0 ≤ s
  · have hsum : (l.map (fun x ↦ x)).sum ≤ (l.map (fun _ ↦ (0 : ℝ))).sum := by
      simpa using (show l.sum ≤ 0 by linarith)
    obtain ⟨x, hx, hxsign⟩ := List.exists_le_of_sum_le hl (fun x ↦ x) (fun _ ↦ (0 : ℝ)) hsum
    refine ⟨x, hx, abs_le.mpr ?_⟩
    have hxbound := abs_le.mp (hbound x hx)
    constructor <;> linarith
  · have hsum : (l.map (fun _ ↦ (0 : ℝ))).sum ≤ (l.map (fun x ↦ x)).sum := by
      simpa using (show 0 ≤ l.sum by linarith)
    obtain ⟨x, hx, hxsign⟩ := List.exists_le_of_sum_le hl (fun _ ↦ (0 : ℝ)) (fun x ↦ x) hsum
    refine ⟨x, hx, abs_le.mpr ?_⟩
    have hxbound := abs_le.mp (hbound x hx)
    constructor <;> linarith

/-- A real finite list whose sum cancels a bounded starting value can be reordered so
that every partial sum, including the starting value, stays within the same bound. -/
theorem exists_perm_bounded_partial_sums (l : List ℝ) (s M : ℝ)
    (hs : |s| ≤ M) (hbound : ∀ x ∈ l, |x| ≤ M) (htotal : s + l.sum = 0) :
    ∃ k : List ℝ, l.Perm k ∧ ∀ j : ℕ, |s + (k.take j).sum| ≤ M := by
  classical
  by_cases hl : l = []
  · subst l
    exact ⟨[], List.Perm.refl [], by simpa using fun _ : ℕ ↦ hs⟩
  · obtain ⟨x, hx, hsx⟩ := exists_bounded_next_term l s M hl hs hbound htotal
    have hperm : l.Perm (x :: l.erase x) := List.perm_cons_erase hx
    have hrest : ∀ y ∈ l.erase x, |y| ≤ M :=
      fun y hy ↦ hbound y (List.mem_of_mem_erase hy)
    have htotal' : (s + x) + (l.erase x).sum = 0 := by
      have hsum := hperm.sum_eq
      simp only [List.sum_cons] at hsum
      linarith
    obtain ⟨k, hk, hkbound⟩ :=
      exists_perm_bounded_partial_sums (l.erase x) (s + x) M hsx hrest htotal'
    refine ⟨x :: k, hperm.trans (hk.cons x), ?_⟩
    intro j
    cases j with
    | zero => simpa using hs
    | succ j => simpa [List.take_succ_cons, List.sum_cons, add_assoc] using hkbound j
termination_by l.length
decreasing_by
  classical
  have hlength := (List.perm_cons_erase hx).length_eq
  simp only [List.length_cons] at hlength
  omega

/-- In particular, real zero-sum eigenvalue lists admit a permutation with all partial
sums bounded by the maximum absolute eigenvalue. -/
theorem exists_zero_sum_real_ordering (l : List ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ l, |x| ≤ M) (htotal : l.sum = 0) :
    ∃ k : List ℝ, l.Perm k ∧ ∀ j : ℕ, |(k.take j).sum| ≤ M := by
  simpa using exists_perm_bounded_partial_sums l 0 M (by simpa using hM) hbound
    (by simpa using htotal)

/-- The sign-greedy ordering also preserves labels; repeated equal values do not lose
which spectral coordinate they came from. -/
theorem exists_perm_bounded_weighted_partial_sums {α : Type*} (l : List α)
    (a : α → ℝ) (s M : ℝ) (hs : |s| ≤ M)
    (hbound : ∀ x ∈ l, |a x| ≤ M) (htotal : s + (l.map a).sum = 0) :
    ∃ k : List α, l.Perm k ∧ ∀ j : ℕ, |s + ((k.take j).map a).sum| ≤ M := by
  classical
  by_cases hl : l = []
  · subst l
    exact ⟨[], List.Perm.refl [], by simpa using fun _ : ℕ ↦ hs⟩
  · have hmap : l.map a ≠ [] := by simpa using hl
    have hb : ∀ y ∈ l.map a, |y| ≤ M := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact hbound x hx
    obtain ⟨y, hy, hsy⟩ := exists_bounded_next_term (l.map a) s M hmap hs hb htotal
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hperm : l.Perm (x :: l.erase x) := List.perm_cons_erase hx
    have hrest : ∀ z ∈ l.erase x, |a z| ≤ M :=
      fun z hz ↦ hbound z (List.mem_of_mem_erase hz)
    have htotal' : (s + a x) + ((l.erase x).map a).sum = 0 := by
      have hsum := (hperm.map a).sum_eq
      simp only [List.map_cons, List.sum_cons] at hsum
      linarith
    obtain ⟨k, hk, hkbound⟩ :=
      exists_perm_bounded_weighted_partial_sums (l.erase x) a (s + a x) M hsy hrest htotal'
    refine ⟨x :: k, hperm.trans (hk.cons x), ?_⟩
    intro j
    cases j with
    | zero => simpa using hs
    | succ j => simpa [List.take_succ_cons, List.map_cons, List.sum_cons, add_assoc] using hkbound j
termination_by l.length
decreasing_by
  classical
  have hlength := (List.perm_cons_erase hx).length_eq
  simp only [List.length_cons] at hlength
  omega

end NoEpsilon
