import NoEpsilon.HermitianSplit
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Bounded Hermitian and adaptive two-commutator theorems

A diagonal vector of the form `w ∘ σ - w` is a single commutator whose first factor is a
permutation unitary and whose second-factor norm is at most the supremum of the weights.
The statement allows arbitrary finite index types and includes the empty-dimensional case.
The real spectral ordering, cyclic construction, unitary conjugation, and Hermitian spectral
reduction are all proved. The final adaptive two-commutator theorem has no extra assumptions.
-/

open scoped Matrix.Norms.L2Operator

namespace NoEpsilon

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem permutationMatrix_isUnitary (σ : Equiv.Perm ι) :
    σ.permMatrix ℂ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- Conjugating a diagonal matrix by a permutation matrix permutes its diagonal entries. -/
theorem permutation_conjugates_diagonal (σ : Equiv.Perm ι) (w : ι → ℂ) :
    σ.permMatrix ℂ * Matrix.diagonal w * star (σ.permMatrix ℂ) =
      Matrix.diagonal (fun i ↦ w (σ i)) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.diagonal_apply, Equiv.Perm.inv_def]

/-- Any bounded cyclic difference of weights is a bounded unitary commutator. This exact
matrix construction is independent of the greedy ordering of a real spectrum. -/
theorem diagonal_difference_is_bounded_commutator (σ : Equiv.Perm ι) (w : ι → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hw : ∀ i, ‖w i‖ ≤ M) :
    ∃ U V : Matrix ι ι ℂ,
      U ∈ Matrix.unitaryGroup ι ℂ ∧
        Matrix.diagonal (fun i ↦ w (σ i) - w i) = ringCommutator U V ∧
          ‖U‖ ≤ 1 ∧ ‖V‖ ≤ M := by
  let U := σ.permMatrix ℂ
  let V := Matrix.diagonal w * star U
  have hU := permutationMatrix_isUnitary σ
  have hUstar : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUnorm : ‖U‖ ≤ 1 := Matrix.permMatrix_l2_opNorm_le σ
  have hDnorm : ‖Matrix.diagonal w‖ ≤ M := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hM).mpr hw
  refine ⟨U, V, hU, ?_, hUnorm, ?_⟩
  · calc
      Matrix.diagonal (fun i ↦ w (σ i) - w i) =
          Matrix.diagonal (fun i ↦ w (σ i)) - Matrix.diagonal w := by
        simp only [Matrix.diagonal_sub]
      _ = U * Matrix.diagonal w * star U - Matrix.diagonal w := by
        rw [permutation_conjugates_diagonal]
      _ = ringCommutator U V := by
        dsimp [ringCommutator, V]
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hUstar, Matrix.mul_one]
  · calc
      ‖V‖ ≤ ‖Matrix.diagonal w‖ * ‖star U‖ := norm_mul_le _ _
      _ = ‖Matrix.diagonal w‖ * ‖U‖ := by rw [norm_star]
      _ ≤ M * 1 := mul_le_mul hDnorm hUnorm (norm_nonneg _) hM
      _ = M := mul_one M

/-- A labelled version of real spectral ordering, expressed as a permutation of `Fin n`. -/
theorem exists_bounded_real_permutation (n : ℕ) (a : Fin n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (ha : ∀ i, |a i| ≤ M) (hsum : ∑ i, a i = 0) :
    ∃ σ : Equiv.Perm (Fin n),
      ∀ j : ℕ, |((List.ofFn (a ∘ σ)).take j).sum| ≤ M := by
  classical
  have htotal : (0 : ℝ) + ((List.finRange n).map a).sum = 0 := by
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    simpa using hsum
  obtain ⟨k, hk, hkb⟩ := exists_perm_bounded_weighted_partial_sums
    (List.finRange n) a 0 M (by simpa using hM) (fun i _ ↦ ha i) htotal
  have hn : k.length = n := by simpa using hk.length_eq.symm
  have hbij : Function.Bijective k.get := List.get_bijective_iff.mpr (fun i ↦ by
    rw [← hk.count_eq i]
    exact List.count_finRange i)
  let σ : Equiv.Perm (Fin n) :=
    (finCongr hn.symm).trans (Equiv.ofBijective k.get hbij)
  have hlist : List.ofFn (a ∘ σ) = k.map a := by
    apply List.ext_getElem (by simp [hn])
    intro i hi hi'
    simp only [List.getElem_ofFn, List.getElem_map, Function.comp_apply]
    rfl
  refine ⟨σ, fun j ↦ ?_⟩
  rw [hlist, ← List.map_take]
  simpa using hkb j

/-- A bounded ordered zero-sum real tuple is exactly the cyclic difference of bounded
prefix sums, including the final wrap-around equality. -/
theorem real_cyclic_difference (n : ℕ) (a : Fin n → ℝ) (hsum : ∑ i, a i = 0) :
    ∀ i : Fin n,
      ((List.ofFn a).take (finRotate n i).val).sum -
        ((List.ofFn a).take i.val).sum = a i := by
  cases n with
  | zero => exact fun i ↦ Fin.elim0 i
  | succ n =>
    intro i
    have hstep := List.sum_take_succ (List.ofFn a) i.val (by simpa using i.isLt)
    simp only [List.getElem_ofFn] at hstep
    by_cases hi : i = Fin.last n
    · subst i
      rw [finRotate_last]
      simp only [Fin.val_zero, List.take_zero, List.sum_nil, Fin.val_last, zero_sub]
      have htotal : ((List.ofFn a).take (n + 1)).sum = 0 := by
        have ht : (List.ofFn a).take (n + 1) = List.ofFn a := by
          simp
        rw [ht, List.sum_ofFn]
        exact hsum
      change ((List.ofFn a).take (n + 1)).sum =
        ((List.ofFn a).take n).sum + a (Fin.last n) at hstep
      linarith
    · rw [coe_finRotate_of_ne_last hi, hstep]
      simp

/-- Unitary conjugation preserves the commutator equation and both operator-norm bounds. -/
theorem unitary_conjugation_bounded_commutator
    (W : Matrix.unitaryGroup ι ℂ) (D : Matrix ι ι ℂ) (M : ℝ)
    (hD : ∃ U V : Matrix ι ι ℂ, U ∈ Matrix.unitaryGroup ι ℂ ∧
      D = ringCommutator U V ∧ ‖U‖ ≤ 1 ∧ ‖V‖ ≤ M) :
    ∃ U V : Matrix ι ι ℂ, U ∈ Matrix.unitaryGroup ι ℂ ∧
      Unitary.conjStarAlgAut ℂ _ W D = ringCommutator U V ∧
        ‖U‖ ≤ 1 ∧ ‖V‖ ≤ M := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) W
  have hnorm (X : Matrix ι ι ℂ) : ‖φ X‖ = ‖X‖ := by
    dsimp [φ]
    change ‖(W : Matrix ι ι ℂ) * X * (star W : Matrix.unitaryGroup ι ℂ)‖ = ‖X‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  obtain ⟨U, V, hU, hUV, hUn, hVn⟩ := hD
  have hU' : φ U ∈ Matrix.unitaryGroup ι ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    rw [← map_star φ, ← map_mul φ, Matrix.mem_unitaryGroup_iff.mp hU, map_one]
  refine ⟨φ U, φ V, hU', ?_, (hnorm U).trans_le hUn, (hnorm V).trans_le hVn⟩
  simpa only [ringCommutator, map_sub, map_mul] using congrArg φ hUV

/-- Every real zero-sum diagonal is a unitary commutator with second-factor norm bounded
by the maximum absolute diagonal entry. The ordering and wrap-around are proved above. -/
theorem real_diagonal_bounded_commutator (n : ℕ) (a : Fin n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (ha : ∀ i, |a i| ≤ M) (hsum : ∑ i, a i = 0) :
    ∃ U V : Matrix (Fin n) (Fin n) ℂ,
      U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        Matrix.diagonal (fun i ↦ (a i : ℂ)) = ringCommutator U V ∧
          ‖U‖ ≤ 1 ∧ ‖V‖ ≤ M := by
  obtain ⟨σ, hσ⟩ := exists_bounded_real_permutation n a M hM ha hsum
  let d := a ∘ σ
  have hd : ∑ i, d i = 0 := (Equiv.sum_comp σ a).trans hsum
  let w : Fin n → ℂ := fun i ↦ (((List.ofFn d).take i.val).sum : ℂ)
  have hw : ∀ i, ‖w i‖ ≤ M := by
    intro i
    simpa only [w, Complex.norm_real, Real.norm_eq_abs] using hσ i.val
  have hdiff : (fun i ↦ w (finRotate n i) - w i) = fun i ↦ (d i : ℂ) := by
    funext i
    dsimp [w]
    rw [← Complex.ofReal_sub, real_cyclic_difference n d hd i]
  have hD := diagonal_difference_is_bounded_commutator (finRotate n) w M hM hw
  rw [hdiff] at hD
  let W : Matrix.unitaryGroup (Fin n) ℂ :=
    ⟨(σ⁻¹).permMatrix ℂ, permutationMatrix_isUnitary σ.symm⟩
  have hconj := unitary_conjugation_bounded_commutator W
    (Matrix.diagonal (fun i ↦ (d i : ℂ))) M hD
  have heq : Unitary.conjStarAlgAut ℂ _ W
      (Matrix.diagonal (fun i ↦ (d i : ℂ))) = Matrix.diagonal (fun i ↦ (a i : ℂ)) := by
    rw [Unitary.conjStarAlgAut_apply]
    change (σ⁻¹).permMatrix ℂ * Matrix.diagonal _ * star ((σ⁻¹).permMatrix ℂ) = _
    rw [permutation_conjugates_diagonal]
    simp only [d, Function.comp_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  rwa [heq] at hconj

/-- The entire Hermitian input is discharged using the spectral theorem, the proved greedy
ordering, and the proved cyclic shift construction. This has no additional hypothesis. -/
theorem hermitianUnitaryCommutatorBound : HermitianUnitaryCommutatorBound := by
  intro n G hG htrace
  let a := hG.eigenvalues
  have hsumC : (∑ i, (a i : ℂ)) = 0 := hG.trace_eq_sum_eigenvalues.symm.trans htrace
  have hsum : ∑ i, a i = 0 := by
    have h := congrArg Complex.re hsumC
    simpa using h
  have hdiagNorm : ‖Matrix.diagonal (fun i ↦ (a i : ℂ))‖ = ‖G‖ := by
    change ‖Matrix.diagonal (RCLike.ofReal ∘ hG.eigenvalues)‖ = ‖G‖
    rw [← hG.conjStarAlgAut_star_eigenvectorUnitary]
    rw [Unitary.conjStarAlgAut_apply]
    change ‖((star hG.eigenvectorUnitary : Matrix.unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) * G *
      (star (star hG.eigenvectorUnitary) : Matrix.unitaryGroup (Fin n) ℂ)‖ = ‖G‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  have ha : ∀ i, |a i| ≤ ‖G‖ := by
    intro i
    calc
      |a i| = ‖(a i : ℂ)‖ := by simp
      _ ≤ ‖fun j ↦ (a j : ℂ)‖ := norm_le_pi_norm (fun j : Fin n ↦ (a j : ℂ)) i
      _ = ‖Matrix.diagonal (fun j ↦ (a j : ℂ))‖ := (Matrix.l2_opNorm_diagonal _).symm
      _ = ‖G‖ := hdiagNorm
  have hD := real_diagonal_bounded_commutator n a ‖G‖ (norm_nonneg G) ha hsum
  have hconj := unitary_conjugation_bounded_commutator hG.eigenvectorUnitary
    (Matrix.diagonal (fun i ↦ (a i : ℂ))) ‖G‖ hD
  have heq : Unitary.conjStarAlgAut ℂ _ hG.eigenvectorUnitary
      (Matrix.diagonal (fun i ↦ (a i : ℂ))) = G := hG.spectral_theorem.symm
  rwa [heq] at hconj

/-- The dimension-free adaptive two-commutator input with constant one, proved with no
quantum-expander, Schatten-space, or other external analytic assumption. -/
theorem adaptiveTwoCommutatorBound : AdaptiveTwoCommutatorBound :=
  adaptiveTwoCommutatorBound_of_hermitian hermitianUnitaryCommutatorBound

end NoEpsilon
