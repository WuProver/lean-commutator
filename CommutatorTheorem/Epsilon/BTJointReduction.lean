import CommutatorTheorem.Epsilon.BTElementary
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The joint-restricted-invertibility reduction to Bourgain--Tzafriri

This file isolates the elementary reduction from the four-matrix form of joint restricted
invertibility to the central-submatrix estimate used by the commutator proof.  It does not assume
joint restricted invertibility as an axiom: `JointRestrictedInvertibility` is an
ordinary `Prop`, and all theorems below take a proof of that proposition as an
explicit hypothesis.

The proposition is stated in the equivalent two-sided form for two Hermitian matrices.  Applying
the one-sided joint restricted-invertibility theorem to the four contractions
`H, -H, G, -G` gives exactly this formulation, with selected cardinality
`floor (t^2 * m / (6 * 4))`.  Conversely, the norm conclusions are precisely the simultaneous
upper and lower Hermitian bounds supplied by those four matrices.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedSpace
  Matrix.instL2OpNormedRing

namespace CommutatorTheorem

/-- The two-sided, four-matrix form of joint restricted invertibility.

For two zero-diagonal Hermitian contractions `H` and `G` and `0 < t < 1`, it selects
`floor (t^2 m / 24)` common coordinates on which both compressions have norm at most `t`.
This is the norm formulation of the one-sided theorem applied simultaneously to
`H, -H, G, -G`. -/
def JointRestrictedInvertibility : Prop :=
  ∀ (m : ℕ) (H G : Matrix (Fin m) (Fin m) ℂ),
    ZeroDiag H → H.IsHermitian → ‖H‖ ≤ 1 →
    ZeroDiag G → G.IsHermitian → ‖G‖ ≤ 1 →
    ∀ (t : ℝ), 0 < t → t < 1 →
      ∃ (f : Fin ⌊(t ^ 2 / 24) * (m : ℝ)⌋₊ → Fin m),
        Function.Injective f ∧
        ‖H.submatrix f f‖ ≤ t ∧
        ‖G.submatrix f f‖ ≤ t

private lemma floor_scaled_card_le (m : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ⌊s * (m : ℝ)⌋₊ ≤ m := by
  have hsm : s * (m : ℝ) ≤ (m : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hs1 (Nat.cast_nonneg m)
  exact_mod_cast (Nat.floor_le (mul_nonneg hs0 (Nat.cast_nonneg m))).trans hsm

private lemma sqrt_twenty_four_pos : 0 < Real.sqrt 24 := by positivity

private lemma sqrt_six_pos : 0 < Real.sqrt 6 := by positivity

private lemma sqrt_twenty_four_sq : (Real.sqrt 24) ^ 2 = 24 := by norm_num

private lemma four_sqrt_six_eq_two_sqrt_twenty_four :
    4 * Real.sqrt 6 = 2 * Real.sqrt 24 := by
  have h : Real.sqrt 24 = 2 * Real.sqrt 6 := by
    calc
      Real.sqrt 24 = Real.sqrt (4 * 6) := by norm_num
      _ = Real.sqrt 4 * Real.sqrt 6 := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt 6 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
  rw [h]
  ring

private noncomputable def hermitianPart {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (1 / 2 : ℂ) • (A + A.conjTranspose)

private noncomputable def imaginaryHermitianPart {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (-Complex.I / 2 : ℂ) • (A - A.conjTranspose)

private lemma hermitianPart_isHermitian {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : (hermitianPart A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [hermitianPart, Matrix.conjTranspose_apply]
  ring

private lemma imaginaryHermitianPart_isHermitian {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : (imaginaryHermitianPart A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [imaginaryHermitianPart, Matrix.conjTranspose_apply]
  ring

private lemma hermitianPart_zeroDiag {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℂ} (hA : ZeroDiag A) : ZeroDiag (hermitianPart A) := by
  intro i
  simp [hermitianPart, Matrix.conjTranspose_apply, hA i]

private lemma imaginaryHermitianPart_zeroDiag {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℂ} (hA : ZeroDiag A) :
    ZeroDiag (imaginaryHermitianPart A) := by
  intro i
  simp [imaginaryHermitianPart, Matrix.conjTranspose_apply, hA i]

private lemma hermitian_decomposition {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) :
    A = hermitianPart A + Complex.I • imaginaryHermitianPart A := by
  ext i j
  simp [hermitianPart, imaginaryHermitianPart, Matrix.conjTranspose_apply]
  ring_nf
  simp [Complex.I_sq]
  ring

private lemma hermitianPart_norm_le {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : ‖hermitianPart A‖ ≤ ‖A‖ := by
  calc
    ‖hermitianPart A‖
        = ‖(1 / 2 : ℂ)‖ * ‖A + A.conjTranspose‖ := by rw [hermitianPart, norm_smul]
    _ = (1 / 2 : ℝ) * ‖A + A.conjTranspose‖ := by norm_num [Complex.norm_def]
    _ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖A.conjTranspose‖) := by
      gcongr
      exact norm_add_le _ _
    _ = ‖A‖ := by rw [Matrix.l2_opNorm_conjTranspose]; ring

private lemma imaginaryHermitianPart_norm_le {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : ‖imaginaryHermitianPart A‖ ≤ ‖A‖ := by
  calc
    ‖imaginaryHermitianPart A‖
        = ‖(-Complex.I / 2 : ℂ)‖ * ‖A - A.conjTranspose‖ := by
          rw [imaginaryHermitianPart, norm_smul]
    _ = (1 / 2 : ℝ) * ‖A - A.conjTranspose‖ := by norm_num [Complex.norm_def]
    _ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖A.conjTranspose‖) := by
      gcongr
      exact norm_sub_le _ _
    _ = ‖A‖ := by rw [Matrix.l2_opNorm_conjTranspose]; ring

/-- Joint restricted invertibility supplies the genuinely analytic small-parameter core of the
Bourgain--Tzafriri central-submatrix theorem. -/
theorem jointRestrictedInvertibility_smallEpsilonCore
    (hJRI : JointRestrictedInvertibility) :
    BourgainTzafririSmallEpsilonCore (4 * Real.sqrt 6) := by
  intro m A hA ε hε hε_half _hcard
  let t : ℝ := Real.sqrt 24 * ε
  by_cases ht : t < 1
  · by_cases hAnorm : ‖A‖ = 0
    · have hAzero : A = 0 := norm_eq_zero.mp hAnorm
      have hε_sq_nonneg : 0 ≤ ε ^ 2 := sq_nonneg ε
      have hε_sq_le : ε ^ 2 ≤ 1 := by nlinarith
      have hsize : ⌊ε ^ 2 * (m : ℝ)⌋₊ ≤ m :=
        floor_scaled_card_le m hε_sq_nonneg hε_sq_le
      let f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m := Fin.castLE hsize
      refine ⟨f, Fin.castLE_injective hsize, ?_⟩
      simp [hAzero]
    · have hAnorm_pos : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg A) (Ne.symm hAnorm)
      let H := hermitianPart A
      let G := imaginaryHermitianPart A
      let c : ℂ := ((‖A‖ : ℂ)⁻¹)
      let Hn : Matrix (Fin m) (Fin m) ℂ := c • H
      let Gn : Matrix (Fin m) (Fin m) ℂ := c • G
      have hH_zd : ZeroDiag H := hermitianPart_zeroDiag hA
      have hG_zd : ZeroDiag G := imaginaryHermitianPart_zeroDiag hA
      have hH_herm : H.IsHermitian := hermitianPart_isHermitian A
      have hG_herm : G.IsHermitian := imaginaryHermitianPart_isHermitian A
      have hc_self : IsSelfAdjoint c := by
        rw [isSelfAdjoint_iff]
        apply Complex.ext <;> simp [c]
      have hHn_zd : ZeroDiag Hn := by
        intro i
        simp [Hn, hH_zd i]
      have hGn_zd : ZeroDiag Gn := by
        intro i
        simp [Gn, hG_zd i]
      have hHn_herm : Hn.IsHermitian := hH_herm.smul hc_self
      have hGn_herm : Gn.IsHermitian := hG_herm.smul hc_self
      have hc_norm : ‖c‖ = ‖A‖⁻¹ := by
        simp [c, Complex.norm_real]
      have hHn_norm : ‖Hn‖ ≤ 1 := by
        change ‖c • H‖ ≤ 1
        rw [norm_smul, hc_norm]
        calc
          ‖A‖⁻¹ * ‖H‖ ≤ ‖A‖⁻¹ * ‖A‖ := by
            gcongr
            exact hermitianPart_norm_le A
          _ = 1 := inv_mul_cancel₀ hAnorm
      have hGn_norm : ‖Gn‖ ≤ 1 := by
        change ‖c • G‖ ≤ 1
        rw [norm_smul, hc_norm]
        calc
          ‖A‖⁻¹ * ‖G‖ ≤ ‖A‖⁻¹ * ‖A‖ := by
            gcongr
            exact imaginaryHermitianPart_norm_le A
          _ = 1 := inv_mul_cancel₀ hAnorm
      have ht_pos : 0 < t := mul_pos sqrt_twenty_four_pos hε
      have ht_scale : t ^ 2 / 24 = ε ^ 2 := by
        dsimp [t]
        rw [mul_pow, sqrt_twenty_four_sq]
        ring
      have hsel := hJRI m Hn Gn hHn_zd hHn_herm hHn_norm
        hGn_zd hGn_herm hGn_norm t ht_pos ht
      rw [ht_scale] at hsel
      obtain ⟨f, hf, hHf, hGf⟩ := hsel
      have hHf_scaled : ‖H.submatrix f f‖ ≤ t * ‖A‖ := by
        have heq : Hn.submatrix f f = c • H.submatrix f f := by
          ext i j
          simp [Hn, Matrix.submatrix_apply]
        have hrewrite : ‖Hn.submatrix f f‖ = ‖A‖⁻¹ * ‖H.submatrix f f‖ := by
          rw [heq, norm_smul, hc_norm]
        rw [hrewrite] at hHf
        calc
          ‖H.submatrix f f‖ = ‖A‖ * (‖A‖⁻¹ * ‖H.submatrix f f‖) := by
            field_simp
          _ ≤ ‖A‖ * t := mul_le_mul_of_nonneg_left hHf (norm_nonneg A)
          _ = t * ‖A‖ := mul_comm _ _
      have hGf_scaled : ‖G.submatrix f f‖ ≤ t * ‖A‖ := by
        have heq : Gn.submatrix f f = c • G.submatrix f f := by
          ext i j
          simp [Gn, Matrix.submatrix_apply]
        have hrewrite : ‖Gn.submatrix f f‖ = ‖A‖⁻¹ * ‖G.submatrix f f‖ := by
          rw [heq, norm_smul, hc_norm]
        rw [hrewrite] at hGf
        calc
          ‖G.submatrix f f‖ = ‖A‖ * (‖A‖⁻¹ * ‖G.submatrix f f‖) := by
            field_simp
          _ ≤ ‖A‖ * t := mul_le_mul_of_nonneg_left hGf (norm_nonneg A)
          _ = t * ‖A‖ := mul_comm _ _
      refine ⟨f, hf, ?_⟩
      have hdecomp :
          A.submatrix f f = H.submatrix f f + Complex.I • G.submatrix f f := by
        ext i j
        simpa [H, G, Matrix.submatrix_apply] using
          congrFun (congrFun (hermitian_decomposition A) (f i)) (f j)
      rw [hdecomp]
      calc
        ‖H.submatrix f f + Complex.I • G.submatrix f f‖
            ≤ ‖H.submatrix f f‖ + ‖Complex.I • G.submatrix f f‖ := norm_add_le _ _
        _ = ‖H.submatrix f f‖ + ‖G.submatrix f f‖ := by rw [norm_smul]; norm_num
        _ ≤ t * ‖A‖ + t * ‖A‖ := add_le_add hHf_scaled hGf_scaled
        _ = (4 * Real.sqrt 6) * ε * ‖A‖ := by
          rw [four_sqrt_six_eq_two_sqrt_twenty_four]
          dsimp [t]
          ring
  · have ht_ge : 1 ≤ t := le_of_not_gt ht
    have hε_sq_nonneg : 0 ≤ ε ^ 2 := sq_nonneg ε
    have hε_sq_le : ε ^ 2 ≤ 1 := by nlinarith
    have hsize : ⌊ε ^ 2 * (m : ℝ)⌋₊ ≤ m :=
      floor_scaled_card_le m hε_sq_nonneg hε_sq_le
    let f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m := Fin.castLE hsize
    have hf : Function.Injective f := Fin.castLE_injective hsize
    refine ⟨f, hf, ?_⟩
    have hcompress : ‖A.submatrix f f‖ ≤ ‖A‖ := by
      simpa only [Matrix.submatrix] using submatrix_norm_le f hf A
    have hcoeff : 1 ≤ (4 * Real.sqrt 6) * ε := by
      rw [four_sqrt_six_eq_two_sqrt_twenty_four]
      dsimp [t] at ht_ge
      nlinarith [sqrt_twenty_four_pos]
    calc
      ‖A.submatrix f f‖ ≤ ‖A‖ := hcompress
      _ = 1 * ‖A‖ := by ring
      _ ≤ ((4 * Real.sqrt 6) * ε) * ‖A‖ :=
        mul_le_mul_of_nonneg_right hcoeff (norm_nonneg A)
      _ = (4 * Real.sqrt 6) * ε * ‖A‖ := by ring

private lemma two_le_four_sqrt_six : 2 ≤ 4 * Real.sqrt 6 := by
  have hs : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hs_sq : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The full central-submatrix estimate, conditional only on the explicitly stated joint
restricted-invertibility proposition. -/
theorem central_submatrix_of_jointRestrictedInvertibility
    (hJRI : JointRestrictedInvertibility) :
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ (4 * Real.sqrt 6) * ε * ‖A‖ :=
  central_submatrix_of_small_epsilon_core
    (4 * Real.sqrt 6) two_le_four_sqrt_six
    (jointRestrictedInvertibility_smallEpsilonCore hJRI)

/-- Existential packaging matching the statement shape of
`bourgain_tzafriri_central_submatrix`, without declaring that theorem as an axiom. -/
theorem bourgain_tzafriri_central_submatrix_of_jointRestrictedInvertibility
    (hJRI : JointRestrictedInvertibility) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ K * ε * ‖A‖ := by
  refine ⟨4 * Real.sqrt 6, mul_pos (by norm_num) sqrt_six_pos, ?_⟩
  exact central_submatrix_of_jointRestrictedInvertibility hJRI

end CommutatorTheorem
