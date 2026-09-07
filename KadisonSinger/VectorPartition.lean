import CommutatorTheorem.NoEpsilon.MSSPadding
import CommutatorTheorem.NoEpsilon.BlockCompression

/-!
# The MSS vector partition theorem

Corollary 1.5 of Marcus--Spielman--Srivastava follows by applying `finite_mss`
to independent random vectors supported in one of `r` orthogonal coordinate blocks.
-/

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace KadisonSinger

open NoEpsilon.MSSSelection NoEpsilon.MSSPadding

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

private noncomputable def blockVector {r : ℕ} (u : ι → ℂ) (j : Fin r) :
    Fin r × ι → ℂ := fun a ↦ if a.1 = j then u a.2 else 0

omit [DecidableEq ι] in
private lemma blockVector_energy {r : ℕ} (u : ι → ℂ) (j : Fin r) :
    energy (blockVector u j) = energy u := by
  classical
  simp only [energy, blockVector, Fintype.sum_prod_type]
  simp_rw [apply_ite (fun z : ℂ ↦ ‖z‖ ^ 2)]
  simp

omit [Fintype ι] [DecidableEq ι] in
private lemma blockVector_outer_sum {r : ℕ} (u : ι → ℂ) (a b : Fin r × ι) :
    (∑ j : Fin r, outer (blockVector u j) a b) =
      if a.1 = b.1 then outer u a.2 b.2 else 0 := by
  classical
  by_cases hab : a.1 = b.1
  · simp [outer, blockVector, hab]
  · simp [outer, blockVector, ite_mul, hab, eq_comm]

/-- The finite MSS vector partition theorem, for a positive energy bound. -/
theorem vector_partition (r : ℕ) (hr : 0 < r) (u : κ → ι → ℂ)
    (hsum : (∑ i, Matrix.vecMulVec (u i) (star (u i))) = 1)
    (δ : ℝ) (hδ : 0 < δ) (henergy : ∀ i, energy (u i) ≤ δ) :
    ∃ c : κ → Fin r, ∀ j,
      ‖∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (u i) (star (u i))‖ ≤
          (1 / Real.sqrt (r : ℝ) + Real.sqrt δ)^2 := by
  classical
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrR
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  let v : κ → Fin r → Fin r × ι → ℂ :=
    fun i j a ↦ (Real.sqrt (r : ℝ) : ℂ) * blockVector (u i) j a
  let p : κ → Fin r → ℝ := fun _ _ ↦ 1 / (r : ℝ)
  have hscale (i : κ) (j : Fin r) : outer (v i j) = (r : ℝ) • outer (blockVector (u i) j) := by
    dsimp [v]
    rw [outer_real_mul, Real.sq_sqrt hrR.le]
  have hcov (i : κ) (j : Fin r) :
      (p i j : ℂ) • Matrix.vecMulVec (v i j) (star (v i j)) =
        outer (blockVector (u i) j) := by
    change ((1 / (r : ℝ) : ℝ) : ℂ) • outer (v i j) = _
    rw [hscale]
    ext a b
    simp [Matrix.smul_apply, smul_eq_mul, hrC]
  have htotal : (∑ i, ∑ j, (p i j : ℂ) •
      Matrix.vecMulVec (v i j) (star (v i j))) = 1 := by
    simp_rw [hcov]
    ext a b
    simp only [Matrix.sum_apply, blockVector_outer_sum]
    by_cases hab : a.1 = b.1
    · have hentry := congrArg (fun A : Matrix ι ι ℂ ↦ A a.2 b.2) hsum
      simpa [hab, Matrix.sum_apply, Matrix.vecMulVec, outer, Matrix.one_apply,
        Prod.ext_iff] using hentry
    · simp [hab, Prod.ext_iff]
  have hmean (i : κ) : ∑ j, p i j * energy (v i j) ≤ (r : ℝ) * δ := by
    have hv (j : Fin r) : energy (v i j) = (r : ℝ) * energy (u i) := by
      dsimp [v]
      rw [energy_real_mul, Real.sq_sqrt hrR.le, blockVector_energy]
    simp_rw [hv]
    simp only [p, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    exact henergy i
  obtain ⟨c, hc⟩ := NoEpsilon.MSSFinite.finite_mss v p
    (fun _ _ ↦ by dsimp [p]; positivity)
    (fun _ ↦ by simp [p, hr0]) htotal ((r : ℝ) * δ) (mul_pos hrR hδ) hmean
  refine ⟨c, fun j ↦ ?_⟩
  let A : Matrix (Fin r × ι) (Fin r × ι) ℂ := ∑ i, outer (v i (c i))
  let B : Matrix ι ι ℂ := ∑ i ∈ Finset.univ.filter (fun i ↦ c i = j), outer (u i)
  have hcomp : A.submatrix (Prod.mk j) (Prod.mk j) = (r : ℂ) • B := by
    ext a b
    simp only [A, Matrix.submatrix_apply, Matrix.sum_apply, hscale, Matrix.smul_apply,
      B, Finset.sum_filter]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : c i = j
    · simp [outer, blockVector, hij]
    · have hji : j ≠ c i := Ne.symm hij
      simp [outer, blockVector, hij, hji]
  have hb : (r : ℝ) * ‖B‖ ≤ (1 + Real.sqrt ((r : ℝ) * δ))^2 := by
    have hh := NoEpsilon.submatrix_operator_norm_le A (Prod.mk j) (Prod.mk j)
      (fun _ _ h ↦ Prod.mk.inj h |>.2) (fun _ _ h ↦ Prod.mk.inj h |>.2)
    rw [hcomp, norm_smul] at hh
    have hn : ‖(r : ℂ)‖ = (r : ℝ) := by simp
    rw [hn] at hh
    exact hh.trans hc
  have hsqrt : Real.sqrt (r : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hrR)
  have hbound : (1 + Real.sqrt ((r : ℝ) * δ))^2 =
      (r : ℝ) * (1 / Real.sqrt (r : ℝ) + Real.sqrt δ)^2 := by
    rw [Real.sqrt_mul hrR.le]
    field_simp
    nlinarith [Real.sq_sqrt hrR.le]
  rw [hbound] at hb
  exact (mul_le_mul_iff_right₀ hrR).mp hb

/-- The vector partition theorem when the total covariance is at most the identity.
A positive covariance deficit is padded with sufficiently small deterministic vectors. -/
theorem vector_partition_le (r : ℕ) (hr : 0 < r) (u : κ → ι → ℂ)
    (hdef : (1 - ∑ i, Matrix.vecMulVec (u i) (star (u i))).PosSemidef)
    (δ : ℝ) (hδ : 0 < δ) (henergy : ∀ i, energy (u i) ≤ δ) :
    ∃ c : κ → Fin r, ∀ j,
      ‖∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (u i) (star (u i))‖ ≤
          (1 / Real.sqrt (r : ℝ) + Real.sqrt δ)^2 := by
  classical
  obtain ⟨K, _, w, hw, hwen⟩ := exists_small_energy_decomposition
    (1 - ∑ i, Matrix.vecMulVec (u i) (star (u i))) hdef δ hδ
  let u' : κ ⊕ (ι × Fin K) → ι → ℂ := Sum.elim u w
  have htotal : (∑ i, Matrix.vecMulVec (u' i) (star (u' i))) = 1 := by
    rw [Fintype.sum_sum_type]
    change (∑ i, outer (u i)) + (∑ i, outer (w i)) = 1
    rw [hw]
    change (∑ i, outer (u i)) + (1 - ∑ i, outer (u i)) = 1
    exact add_sub_cancel _ _
  have hen : ∀ i, energy (u' i) ≤ δ := by
    intro i
    cases i with
    | inl i => exact henergy i
    | inr i => exact hwen i
  obtain ⟨c, hc⟩ := vector_partition r hr u' htotal δ hδ hen
  refine ⟨fun i ↦ c (.inl i), fun j ↦ ?_⟩
  have hsplit :
      (∑ i ∈ Finset.univ.filter (fun i ↦ c i = j), outer (u' i)) =
        (∑ i ∈ Finset.univ.filter (fun i ↦ c (.inl i) = j), outer (u i)) +
        (∑ i ∈ Finset.univ.filter (fun i ↦ c (.inr i) = j), outer (w i)) := by
    simp only [Finset.sum_filter, Fintype.sum_sum_type]
    rfl
  have hj := hc j
  change ‖∑ i ∈ Finset.univ.filter (fun i ↦ c i = j), outer (u' i)‖ ≤ _ at hj
  rw [hsplit] at hj
  apply le_trans (norm_le_norm_add_of_posSemidef _ _ ?_ ?_) hj
  · exact Matrix.posSemidef_sum _ fun i _ ↦ Matrix.posSemidef_vecMulVec_self_star (u i)
  · exact Matrix.posSemidef_sum _ fun i _ ↦ Matrix.posSemidef_vecMulVec_self_star (w i)

end KadisonSinger
