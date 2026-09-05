import CommutatorTheorem.Defs

/-!
# Elementary ranges of the Bourgain--Tzafriri selection estimate

This file isolates the part of the central-submatrix estimate which does not use
the deep Bourgain--Tzafriri theorem.  When `1 / 2 <= epsilon < 1`, the desired
estimate follows by taking the initial coordinate subset and using compression
contractivity.  Thus the genuinely analytic part of the theorem is confined to
small `epsilon`.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing

namespace CommutatorTheorem

/-- The central-submatrix estimate with constant `2` in the elementary range
`1 / 2 <= epsilon < 1`.  No zero-diagonal hypothesis is needed in this range. -/
theorem central_submatrix_large_epsilon
    (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ)
    (ε : ℝ) (hε : (1 / 2 : ℝ) ≤ ε) (hε' : ε < 1) :
    ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
      Function.Injective f ∧
      ‖A.submatrix f f‖ ≤ 2 * ε * ‖A‖ := by
  have hε_nonneg : 0 ≤ ε := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hε
  have harg_nonneg : 0 ≤ ε ^ 2 * (m : ℝ) :=
    mul_nonneg (sq_nonneg ε) (Nat.cast_nonneg m)
  have hε_sq_le : ε ^ 2 ≤ 1 := by nlinarith
  have harg_le : ε ^ 2 * (m : ℝ) ≤ (m : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hε_sq_le (Nat.cast_nonneg m)
  have hsize : ⌊ε ^ 2 * (m : ℝ)⌋₊ ≤ m := by
    exact_mod_cast (Nat.floor_le harg_nonneg).trans harg_le
  let f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m := Fin.castLE hsize
  have hf : Function.Injective f := Fin.castLE_injective hsize
  refine ⟨f, hf, ?_⟩
  have hcompress := submatrix_norm_le f hf A
  have hsubmatrix :
      Matrix.of (fun i j => A (f i) (f j)) = A.submatrix f f := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.of_apply]
  rw [hsubmatrix] at hcompress
  have hone_le : (1 : ℝ) ≤ 2 * ε := by nlinarith
  calc
    ‖A.submatrix f f‖ ≤ ‖A‖ := hcompress
    _ = 1 * ‖A‖ := by ring
    _ ≤ (2 * ε) * ‖A‖ :=
      mul_le_mul_of_nonneg_right hone_le (norm_nonneg A)
    _ = 2 * ε * ‖A‖ := by ring

/-- If the requested principal submatrix has at most one coordinate, its norm is
zero for a zero-diagonal matrix.  This is the second elementary range of the
Bourgain--Tzafriri estimate. -/
theorem central_submatrix_card_le_one
    (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) (hzd : ZeroDiag A)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hcard : ⌊ε ^ 2 * (m : ℝ)⌋₊ ≤ 1) :
    ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
      Function.Injective f ∧
      ‖A.submatrix f f‖ ≤ 2 * ε * ‖A‖ := by
  have harg_nonneg : 0 ≤ ε ^ 2 * (m : ℝ) :=
    mul_nonneg (sq_nonneg ε) (Nat.cast_nonneg m)
  have hε_sq_le : ε ^ 2 ≤ 1 := by nlinarith
  have harg_le : ε ^ 2 * (m : ℝ) ≤ (m : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hε_sq_le (Nat.cast_nonneg m)
  have hsize : ⌊ε ^ 2 * (m : ℝ)⌋₊ ≤ m := by
    exact_mod_cast (Nat.floor_le harg_nonneg).trans harg_le
  let f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m := Fin.castLE hsize
  have hf : Function.Injective f := Fin.castLE_injective hsize
  refine ⟨f, hf, ?_⟩
  have hzero : A.submatrix f f = 0 := by
    ext i j
    have hij : i = j := Fin.ext (by omega)
    subst hij
    simpa [Matrix.submatrix_apply] using hzd (f i)
  rw [hzero, norm_zero]
  positivity

/-- The genuinely non-elementary core left after removing the large-`epsilon`
and cardinality-at-most-one ranges. -/
def BourgainTzafririSmallEpsilonCore (K : ℝ) : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
    ZeroDiag A →
    ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      2 ≤ ⌊ε ^ 2 * (m : ℝ)⌋₊ →
      ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
        Function.Injective f ∧
        ‖A.submatrix f f‖ ≤ K * ε * ‖A‖

/-- Once the small-`epsilon`, nontrivial-cardinality core is available with a
constant at least `2`, the full central-submatrix statement follows. -/
theorem central_submatrix_of_small_epsilon_core
    (K : ℝ) (hK : 2 ≤ K) (hcore : BourgainTzafririSmallEpsilonCore K) :
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ K * ε * ‖A‖ := by
  intro m A hzd ε hε hε'
  have hconstant : 2 * ε * ‖A‖ ≤ K * ε * ‖A‖ := by
    have h2Kε : 2 * ε ≤ K * ε := mul_le_mul_of_nonneg_right hK hε.le
    exact mul_le_mul_of_nonneg_right h2Kε (norm_nonneg A)
  by_cases hlarge : (1 / 2 : ℝ) ≤ ε
  · obtain ⟨f, hf, hbound⟩ := central_submatrix_large_epsilon m A ε hlarge hε'
    refine ⟨f, hf, hbound.trans ?_⟩
    exact hconstant
  · have hsmall : ε < (1 / 2 : ℝ) := lt_of_not_ge hlarge
    by_cases hcard : ⌊ε ^ 2 * (m : ℝ)⌋₊ ≤ 1
    · obtain ⟨f, hf, hbound⟩ :=
        central_submatrix_card_le_one m A hzd ε hε hε' hcard
      refine ⟨f, hf, hbound.trans ?_⟩
      exact hconstant
    · exact hcore m A hzd ε hε hsmall (by omega)

end CommutatorTheorem
