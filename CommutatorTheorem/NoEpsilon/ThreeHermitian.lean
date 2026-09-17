import CommutatorTheorem.NoEpsilon.HighMassCompression
import CommutatorTheorem.NoEpsilon.BlockCompression
import Mathlib.Analysis.Polynomial.Order

/-!
# Common neutral vectors for Hermitian triples

The real three-coordinate calculation below is the constructive core of
Damm--Faßbender's simultaneous hollowization argument. All vector norms used
in the matrix interfaces are Euclidean norms.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate
open Polynomial

namespace NoEpsilon
namespace ThreeHermitian

/-- A real polynomial negative somewhere and with nonnegative leading coefficient
has a real root. -/
theorem exists_root_of_negative (P : ℝ[X]) (x : ℝ) (hx : P.eval x < 0)
    (hP : 0 ≤ P.leadingCoeff) : ∃ t : ℝ, P.eval t = 0 := by
  by_contra h
  push Not at h
  have hp := P.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (x := x) (fun y hy ↦ (h y hy).elim) hP
  linarith

/-- A quadratic with opposite signs in its constant and leading terms has a real root. -/
theorem exists_quadratic_zero (a b c : ℝ) (ha : 0 < a) (hc : c < 0) :
    ∃ t : ℝ, a * t ^ 2 + b * t + c = 0 := by
  let P : ℝ[X] := C a * X ^ 2 + C b * X + C c
  have hdeg : P.natDegree = 2 := by
    dsimp [P]
    compute_degree!
    exact ha.ne'
  have hlc : P.leadingCoeff = a := by
    rw [Polynomial.leadingCoeff, hdeg]
    dsimp [P]
    compute_degree!
  obtain ⟨t, ht⟩ := exists_root_of_negative P 0 (by simpa [P] using hc) (by
    rw [hlc]
    exact ha.le)
  exact ⟨t, by simpa [P] using ht⟩

/-- Two real quadratic forms on three coordinates have a common nonzero zero
when the first is hollow and the second has one negative and two positive diagonal
coefficients. The proof uses a polynomial curve lying entirely in the first quadric. -/
theorem exists_real_common_zero (a b c d₀ d₁ d₂ α β γ : ℝ)
    (hd₀ : d₀ < 0) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    ∃ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      a * x * y + b * x * z + c * y * z = 0 ∧
      d₀ * x ^ 2 + d₁ * y ^ 2 + d₂ * z ^ 2 +
        α * x * y + β * x * z + γ * y * z = 0 := by
  by_cases ha : a = 0
  · obtain ⟨t, ht⟩ := exists_quadratic_zero d₁ α d₀ hd₁ hd₀
    refine ⟨1, t, 0, Or.inl one_ne_zero, ?_, ?_⟩
    · simp [ha]
    · simpa [add_comm, add_left_comm, add_assoc] using ht
  by_cases hb : b = 0
  · obtain ⟨t, ht⟩ := exists_quadratic_zero d₂ β d₀ hd₂ hd₀
    refine ⟨1, 0, t, Or.inl one_ne_zero, ?_, ?_⟩
    · simp [hb]
    · simpa [add_comm, add_left_comm, add_assoc] using ht
  by_cases hc : c = 0
  · let L : ℝ := d₁ * b ^ 2 + d₂ * a ^ 2 - γ * a * b
    by_cases hL : 0 < L
    · obtain ⟨t, ht⟩ := exists_quadratic_zero L (α * b ^ 2 - β * a * b)
        (d₀ * b ^ 2) hL (mul_neg_of_neg_of_pos hd₀ (sq_pos_of_ne_zero hb))
      refine ⟨b, b * t, -a * t, Or.inl hb, ?_, ?_⟩
      · simp only [hc, zero_mul, add_zero]
        ring
      · dsimp [L] at ht
        nlinarith [ht]
    · have hL' : L ≤ 0 := le_of_not_gt hL
      let f : ℝ → ℝ := fun t ↦ d₁ * b ^ 2 + d₂ * (-a * t) ^ 2 + γ * b * (-a * t)
      have hf : Continuous f := by dsimp [f]; fun_prop
      have hf₀ : 0 ≤ f 0 := by
        simpa [f] using mul_nonneg hd₁.le (sq_nonneg b)
      have hf₁ : f 1 ≤ 0 := by dsimp [f, L] at *; nlinarith
      obtain ⟨t, ht⟩ := intermediate_value_univ 1 0 hf ⟨hf₁, hf₀⟩
      refine ⟨0, b, -a * t, Or.inr (Or.inl hb), ?_, ?_⟩
      · simp [hc]
      · simpa [f] using ht
  let P : ℝ[X] :=
    C d₀ * (C b + C c * X) ^ 2 +
    C d₁ * (X * (C b + C c * X)) ^ 2 + C d₂ * (-C a * X) ^ 2 +
    C α * (C b + C c * X) * (X * (C b + C c * X)) +
    C β * (C b + C c * X) * (-C a * X) +
    C γ * (X * (C b + C c * X)) * (-C a * X)
  have hdeg : P.natDegree = 4 := by
    dsimp [P]
    compute_degree!
    exact ⟨hd₁.ne', hc⟩
  have hlc : P.leadingCoeff = d₁ * c ^ 2 := by
    rw [Polynomial.leadingCoeff, hdeg]
    dsimp [P]
    compute_degree!
  have hP₀ : P.eval 0 < 0 := by
    simpa [P] using mul_neg_of_neg_of_pos hd₀ (sq_pos_of_ne_zero hb)
  obtain ⟨t, ht⟩ := exists_root_of_negative P 0 hP₀ (by rw [hlc]; positivity)
  refine ⟨b + c * t, t * (b + c * t), -a * t, ?_, ?_, ?_⟩
  · by_cases ht₀ : t = 0
    · exact Or.inl (by simpa [ht₀] using hb)
    · exact Or.inr (Or.inr (mul_ne_zero (neg_ne_zero.mpr ha) ht₀))
  · ring
  · simpa [P] using ht

/-- Multiplying by a suitable nonzero complex scalar makes any complex number
purely imaginary. Normalization is unnecessary for the neutral-vector construction. -/
theorem exists_nonzero_imaginary_multiple (z : ℂ) :
    ∃ u : ℂ, u ≠ 0 ∧ (z * u).re = 0 := by
  by_cases hz : z = 0
  · exact ⟨1, one_ne_zero, by simp [hz]⟩
  refine ⟨Complex.I * star z, mul_ne_zero Complex.I_ne_zero (star_ne_zero.mpr hz), ?_⟩
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- A singular hollow Hermitian three-coordinate form admits a nonsingular diagonal
change of variables whose restriction to real vectors is identically zero. This is
the off-diagonal calculation; singularity is the real triangle-product condition. -/
theorem exists_imaginary_edge_scaling (a b c : ℂ)
    (h : (a * c * star b).re = 0) :
    ∃ u v : ℂ, u ≠ 0 ∧ v ≠ 0 ∧ (a * u).re = 0 ∧ (b * v).re = 0 ∧
      (star u * c * v).re = 0 := by
  by_cases ha : a = 0
  · obtain ⟨v, hv, hbv⟩ := exists_nonzero_imaginary_multiple b
    obtain ⟨w, hw, hcw⟩ := exists_nonzero_imaginary_multiple (c * v)
    refine ⟨star w, v, star_ne_zero.mpr hw, hv, by simp [ha], hbv, ?_⟩
    simpa only [star_star, mul_comm, mul_left_comm, mul_assoc] using hcw
  by_cases hb : b = 0
  · obtain ⟨u, hu, hau⟩ := exists_nonzero_imaginary_multiple a
    obtain ⟨v, hv, hcv⟩ := exists_nonzero_imaginary_multiple (star u * c)
    exact ⟨u, v, hu, hv, hau, by simp [hb], hcv⟩
  refine ⟨Complex.I * star a, Complex.I * star b,
    mul_ne_zero Complex.I_ne_zero (star_ne_zero.mpr ha),
    mul_ne_zero Complex.I_ne_zero (star_ne_zero.mpr hb), ?_, ?_, ?_⟩
  · simp [Complex.mul_re, Complex.mul_im]
    ring
  · simp [Complex.mul_re, Complex.mul_im]
    ring
  · convert h using 1
    simp [Complex.mul_re, Complex.mul_im]
    ring

/-- An odd cubic on a real two-dimensional pencil vanishes in a nonzero direction.
The half-circle argument avoids division by a polynomial coefficient. -/
theorem exists_singular_hollow_pencil (a b c a' b' c' : ℂ) :
    ∃ p q : ℝ, p ^ 2 + q ^ 2 = 1 ∧
      (((p : ℂ) * a + q * a') * ((p : ℂ) * c + q * c') *
        star ((p : ℂ) * b + q * b')).re = 0 := by
  let f : ℝ → ℝ := fun t ↦
    (((Real.cos t : ℂ) * a + Real.sin t * a') *
      ((Real.cos t : ℂ) * c + Real.sin t * c') *
      star ((Real.cos t : ℂ) * b + Real.sin t * b')).re
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hπ : f Real.pi = -f 0 := by simp [f]; ring
  have hz : ∃ t : ℝ, f t = 0 := by
    rcases le_total (f 0) 0 with h | h
    · exact intermediate_value_univ 0 Real.pi hf ⟨h, by rw [hπ]; linarith⟩
    · exact intermediate_value_univ Real.pi 0 hf ⟨by rw [hπ]; linarith, h⟩
  obtain ⟨t, ht⟩ := hz
  exact ⟨Real.cos t, Real.sin t, by nlinarith [Real.sin_sq_add_cos_sq t], ht⟩

/-- The real quadratic form of a hollow Hermitian matrix, written using its three
upper-triangular entries. -/
def edgeForm (a b c x y z : ℂ) : ℝ :=
  2 * (star x * a * y + star x * b * z + star y * c * z).re

theorem edgeForm_real_scaled (a b c u v : ℂ) (x y z : ℝ) :
    edgeForm a b c x (u * y) (v * z) =
      2 * ((a * u).re * x * y + (b * v).re * x * z +
        (star u * c * v).re * y * z) := by
  simp [edgeForm, Complex.mul_re, Complex.mul_im]
  ring

theorem edgeForm_pencil (a b c a' b' c' x y z : ℂ) (p q : ℝ) :
    edgeForm (p * a + q * a') (p * b + q * b') (p * c + q * c') x y z =
      p * edgeForm a b c x y z + q * edgeForm a' b' c' x y z := by
  simp [edgeForm, Complex.mul_re, Complex.mul_im]
  ring

/-- Two hollow Hermitian forms and a third Hermitian form with diagonal signs
`(-,+,+)` have a common nonzero zero over the complex numbers. This is a genuine
three-form result, proved by reducing an odd pencil to the real three-coordinate lemma. -/
theorem exists_hollow_triple_zero (a b c a' b' c' e f g : ℂ) (d₀ d₁ d₂ : ℝ)
    (hd₀ : d₀ < 0) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    ∃ x y z : ℂ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      edgeForm a b c x y z = 0 ∧ edgeForm a' b' c' x y z = 0 ∧
      d₀ * Complex.normSq x + d₁ * Complex.normSq y + d₂ * Complex.normSq z +
        edgeForm e f g x y z = 0 := by
  obtain ⟨p, q, hpq, hzero⟩ := exists_singular_hollow_pencil a b c a' b' c'
  obtain ⟨u, v, hu, hv, hau, hbv, hcuv⟩ := exists_imaginary_edge_scaling
    (p * a + q * a') (p * b + q * b') (p * c + q * c') hzero
  let A : ℂ := (-q : ℂ) * a + p * a'
  let B : ℂ := (-q : ℂ) * b + p * b'
  let C : ℂ := (-q : ℂ) * c + p * c'
  obtain ⟨x, y, z, hxyz, hK, hE⟩ := exists_real_common_zero
    (A * u).re (B * v).re (star u * C * v).re
    d₀ (d₁ * Complex.normSq u) (d₂ * Complex.normSq v)
    (2 * (e * u).re) (2 * (f * v).re) (2 * (star u * g * v).re)
    hd₀ (mul_pos hd₁ (Complex.normSq_pos.mpr hu))
    (mul_pos hd₂ (Complex.normSq_pos.mpr hv))
  have hL : p * edgeForm a b c x (u * y) (v * z) +
      q * edgeForm a' b' c' x (u * y) (v * z) = 0 := by
    rw [← edgeForm_pencil, edgeForm_real_scaled, hau, hbv, hcuv]
    ring
  have hK' : -q * edgeForm a b c x (u * y) (v * z) +
      p * edgeForm a' b' c' x (u * y) (v * z) = 0 := by
    rw [← edgeForm_pencil]
    have h : edgeForm A B C x (u * y) (v * z) = 0 := by
      rw [edgeForm_real_scaled, hK, mul_zero]
    simpa only [A, B, C, Complex.ofReal_neg] using h
  have hFirst : edgeForm a b c x (u * y) (v * z) = 0 := by
    have h : (p ^ 2 + q ^ 2) * edgeForm a b c x (u * y) (v * z) = 0 := by
      linear_combination p * hL - q * hK'
    simpa only [hpq, one_mul] using h
  have hSecond : edgeForm a' b' c' x (u * y) (v * z) = 0 := by
    have h : (p ^ 2 + q ^ 2) * edgeForm a' b' c' x (u * y) (v * z) = 0 := by
      linear_combination q * hL + p * hK'
    simpa only [hpq, one_mul] using h
  refine ⟨x, u * y, v * z, ?_, hFirst, hSecond, ?_⟩
  · rcases hxyz with hx | hy | hz
    · exact Or.inl (Complex.ofReal_ne_zero.mpr hx)
    · exact Or.inr (Or.inl (mul_ne_zero hu (Complex.ofReal_ne_zero.mpr hy)))
    · exact Or.inr (Or.inr (mul_ne_zero hv (Complex.ofReal_ne_zero.mpr hz)))
  · rw [edgeForm_real_scaled]
    simp only [Complex.normSq_mul, Complex.normSq_ofReal]
    nlinarith [hE]

theorem rayleighValue_hermitian_im {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (v : ι → ℂ) :
    (rayleighValue H v).im = 0 := by
  classical
  have h := congrArg Complex.im (rayleighValue_adjoint H v)
  rw [hH.eq] at h
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

theorem rayleighValue_eq_zero_of_re_eq_zero {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (v : ι → ℂ)
    (hv : (rayleighValue H v).re = 0) : rayleighValue H v = 0 := by
  apply Complex.ext
  · exact hv
  · exact rayleighValue_hermitian_im H hH v

/-- The three-coordinate matrix quadratic form, with all conjugates accounted for. -/
theorem rayleighValue_three_re (H : Matrix (Fin 3) (Fin 3) ℂ) (hH : H.IsHermitian)
    (x y z : ℂ) :
    (rayleighValue H ![x, y, z]).re =
      (H 0 0).re * Complex.normSq x + (H 1 1).re * Complex.normSq y +
      (H 2 2).re * Complex.normSq z + edgeForm (H 0 1) (H 0 2) (H 1 2) x y z := by
  simp [rayleighValue, Matrix.mulVec, dotProduct, Fin.sum_univ_three, edgeForm,
    ← hH.apply 1 0, ← hH.apply 2 0, ← hH.apply 2 1,
    Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- A concrete three-by-three common-neutral-vector theorem. The two first matrices
are hollow and the third has diagonal signs `(-,+,+)`. No convexity axiom for triple
numerical ranges is used. -/
theorem exists_common_neutral_three_of_signs (H G E : Matrix (Fin 3) (Fin 3) ℂ)
    (hH : H.IsHermitian) (hG : G.IsHermitian) (hE : E.IsHermitian)
    (hHd : ∀ i, H i i = 0) (hGd : ∀ i, G i i = 0)
    (hE₀ : (E 0 0).re < 0) (hE₁ : 0 < (E 1 1).re) (hE₂ : 0 < (E 2 2).re) :
    ∃ v : Fin 3 → ℂ, v ≠ 0 ∧ rayleighValue H v = 0 ∧ rayleighValue G v = 0 ∧
      rayleighValue E v = 0 := by
  obtain ⟨x, y, z, hxyz, hFirst, hSecond, hThird⟩ := exists_hollow_triple_zero
    (H 0 1) (H 0 2) (H 1 2) (G 0 1) (G 0 2) (G 1 2)
    (E 0 1) (E 0 2) (E 1 2) (E 0 0).re (E 1 1).re (E 2 2).re hE₀ hE₁ hE₂
  refine ⟨![x, y, z], ?_, ?_, ?_, ?_⟩
  · intro hv
    have hx := congrFun hv 0
    have hy := congrFun hv 1
    have hz := congrFun hv 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at hx hy hz
    exact hxyz.elim (fun h ↦ h hx) (fun h ↦ h.elim (fun h ↦ h hy) (fun h ↦ h hz))
  · apply rayleighValue_eq_zero_of_re_eq_zero H hH
    simpa only [rayleighValue_three_re H hH, hHd, Complex.zero_re, zero_mul,
      zero_add] using hFirst
  · apply rayleighValue_eq_zero_of_re_eq_zero G hG
    simpa only [rayleighValue_three_re G hG, hGd, Complex.zero_re, zero_mul,
      zero_add] using hSecond
  · apply rayleighValue_eq_zero_of_re_eq_zero E hE
    rw [rayleighValue_three_re E hE]
    exact hThird

/-- A nonzero zero-sum real family with at least three indices contains three
distinct entries with one sign opposite to the other two. -/
theorem exists_three_signs {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hcard : 3 ≤ Fintype.card ι) (hsum : ∑ i, f i = 0) (hzero : ∀ i, f i ≠ 0) :
    ∃ i j k : ι, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ((f i < 0 ∧ 0 < f j ∧ 0 < f k) ∨ (0 < f i ∧ f j < 0 ∧ f k < 0)) := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hneg : ∃ i, f i < 0 := by
    by_contra h
    push Not at h
    have hpos : 0 < ∑ i, f i := Finset.sum_pos
      (fun i _ ↦ lt_of_le_of_ne (h i) (Ne.symm (hzero i))) Finset.univ_nonempty
    linarith
  have hpos : ∃ i, 0 < f i := by
    by_contra h
    push Not at h
    have hneg' : (∑ i, f i) < 0 := Finset.sum_neg
      (fun i _ ↦ lt_of_le_of_ne (h i) (hzero i)) Finset.univ_nonempty
    linarith
  obtain ⟨i, hi⟩ := hneg
  obtain ⟨j, hj⟩ := hpos
  have hij : i ≠ j := by intro h; subst j; linarith
  have hsmall : ({i, j} : Finset ι).card < (Finset.univ : Finset ι).card := by
    simp only [Finset.card_pair hij, Finset.card_univ]
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  rcases lt_or_gt_of_ne (hzero k) with hkn | hkp
  · exact ⟨j, i, k, hij.symm, Ne.symm hk.2, Ne.symm hk.1, Or.inr ⟨hj, hi, hkn⟩⟩
  · exact ⟨i, j, k, hij, Ne.symm hk.1, Ne.symm hk.2, Or.inl ⟨hi, hj, hkp⟩⟩

/-- A three-coordinate common neutral vector remains nonzero when included in
the full coordinate space. -/
theorem exists_common_neutral_of_three_signs {ι : Type*} [Fintype ι]
    (H G E : Matrix ι ι ℂ) (hH : H.IsHermitian) (hG : G.IsHermitian)
    (hE : E.IsHermitian) (hHd : ∀ i, H i i = 0) (hGd : ∀ i, G i i = 0)
    (f : Fin 3 → ι) (hf : Function.Injective f)
    (hE₀ : (E (f 0) (f 0)).re < 0) (hE₁ : 0 < (E (f 1) (f 1)).re)
    (hE₂ : 0 < (E (f 2) (f 2)).re) :
    ∃ v : ι → ℂ, v ≠ 0 ∧ rayleighValue H v = 0 ∧ rayleighValue G v = 0 ∧
      rayleighValue E v = 0 := by
  classical
  obtain ⟨v, hv, hHv, hGv, hEv⟩ := exists_common_neutral_three_of_signs
    (H.submatrix f f) (G.submatrix f f) (E.submatrix f f)
    (hH.submatrix f) (hG.submatrix f) (hE.submatrix f)
    (fun i ↦ hHd (f i)) (fun i ↦ hGd (f i)) hE₀ hE₁ hE₂
  let C := coordinateInclusion f
  have hC : Cᴴ * C = 1 := coordinateInclusion_isometry f hf
  have hcomp (A : Matrix ι ι ℂ) :
      rayleighValue (A.submatrix f f) v = rayleighValue A (C *ᵥ v) := by
    rw [submatrix_eq_coordinate_compression, rayleighValue_compression]
  refine ⟨C *ᵥ v, ?_, (hcomp H).symm.trans hHv, (hcomp G).symm.trans hGv,
    (hcomp E).symm.trans hEv⟩
  intro hw
  apply hv
  apply (vectorEnergy_eq_zero v).mp
  rw [← vectorEnergy_isometry_mulVec C hC v, hw]
  simp [vectorEnergy]

theorem rayleighValue_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i : ι) : rayleighValue A (Pi.single i 1) = A i i := by
  simp [rayleighValue, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem rayleighValue_neg {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (v : ι → ℂ) : rayleighValue (-A) v = -rayleighValue A v := by
  simp only [rayleighValue, Matrix.neg_mulVec, dotProduct_neg]

/-- The full-dimensional common-neutral-vector theorem once the first two
Hermitian matrices have been made hollow. -/
theorem exists_common_neutral_of_hollow {ι : Type*} [Fintype ι]
    (H G E : Matrix ι ι ℂ) (hH : H.IsHermitian) (hG : G.IsHermitian)
    (hE : E.IsHermitian) (hHd : ∀ i, H i i = 0) (hGd : ∀ i, G i i = 0)
    (htrace : Matrix.trace E = 0) (hcard : 3 ≤ Fintype.card ι) :
    ∃ v : ι → ℂ, v ≠ 0 ∧ rayleighValue H v = 0 ∧ rayleighValue G v = 0 ∧
      rayleighValue E v = 0 := by
  classical
  by_cases hzero : ∃ i, (E i i).re = 0
  · obtain ⟨i, hi⟩ := hzero
    refine ⟨Pi.single i 1, ?_, ?_, ?_, ?_⟩
    · intro h
      have := congrFun h i
      simp at this
    · rw [rayleighValue_single, hHd]
    · rw [rayleighValue_single, hGd]
    · apply rayleighValue_eq_zero_of_re_eq_zero E hE
      rwa [rayleighValue_single]
  push Not at hzero
  have hsum : ∑ i, (E i i).re = 0 := by
    simpa only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.zero_re] using
      congrArg Complex.re htrace
  obtain ⟨i, j, k, hij, hik, hjk, hsigns⟩ :=
    exists_three_signs (fun i ↦ (E i i).re) hcard hsum hzero
  let f : Fin 3 → ι := ![i, j, k]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  rcases hsigns with ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩
  · exact exists_common_neutral_of_three_signs H G E hH hG hE hHd hGd f hf hi hj hk
  · obtain ⟨v, hv, hHv, hGv, hEv⟩ := exists_common_neutral_of_three_signs
      H G (-E) hH hG hE.neg hHd hGd f hf
      (by simpa [f] using neg_neg_of_pos hi)
      (by simpa [f] using neg_pos.mpr hj) (by simpa [f] using neg_pos.mpr hk)
    exact ⟨v, hv, hHv, hGv, neg_eq_zero.mp ((rayleighValue_neg E v).symm.trans hEv)⟩

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedFintypeInType false in
theorem isHermitian_compression {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (U : Matrix ι κ ℂ) :
    (Uᴴ * H * U).IsHermitian := by
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]

/-- Fillmore's theorem for `H + i G` simultaneously hollows two Hermitian matrices. -/
theorem exists_simultaneously_hollow {n : ℕ} (H G : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hG : G.IsHermitian)
    (htrH : Matrix.trace H = 0) (htrG : Matrix.trace G = 0) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, CommutatorTheorem.IsUnitaryMatrix U ∧
      (∀ j, (Uᴴ * H * U) j j = 0) ∧ (∀ j, (Uᴴ * G * U) j j = 0) := by
  let A := H + Complex.I • G
  have htrA : Matrix.trace A = 0 := by simp [A, htrH, htrG]
  obtain ⟨U, B, hU, hB, hA⟩ := CommutatorTheorem.fillmore A htrA
  have hcomp : Uᴴ * A * U = B := by
    rw [hA]
    calc
      Uᴴ * (U * B * Uᴴ) * U = (Uᴴ * U) * B * (Uᴴ * U) := by noncomm_ring
      _ = B := by rw [hU.2]; simp
  have hsplit (v : Fin n → ℂ) :
      rayleighValue A v = rayleighValue H v + Complex.I * rayleighValue G v := by
    simp only [A, rayleighValue, Matrix.add_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hzeros (j : Fin n) : (Uᴴ * H * U) j j = 0 ∧ (Uᴴ * G * U) j j = 0 := by
    let v : Fin n → ℂ := fun i ↦ U i j
    have hzero : rayleighValue A v = 0 := by
      rw [← gram_diagonal, hcomp]
      exact hB j
    rw [hsplit] at hzero
    have hr := congrArg Complex.re hzero
    have hi := congrArg Complex.im hzero
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, rayleighValue_hermitian_im G hG, sub_zero, add_zero,
      Complex.zero_re] at hr
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, rayleighValue_hermitian_im H hH, zero_add,
      Complex.zero_im] at hi
    exact ⟨(gram_diagonal H U j).trans (rayleighValue_eq_zero_of_re_eq_zero H hH v hr),
      (gram_diagonal G U j).trans (rayleighValue_eq_zero_of_re_eq_zero G hG v hi)⟩
  exact ⟨U, hU, fun j ↦ (hzeros j).1, fun j ↦ (hzeros j).2⟩

/-- Three trace-zero Hermitian forms in complex dimension at least three have
a common nonzero neutral vector. This proves the three-form step directly,
without importing joint-numerical-range convexity. -/
theorem exists_common_neutral {n : ℕ} (H G E : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hG : G.IsHermitian) (hE : E.IsHermitian)
    (htrH : Matrix.trace H = 0) (htrG : Matrix.trace G = 0)
    (htrE : Matrix.trace E = 0) (hn : 3 ≤ n) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧ rayleighValue H v = 0 ∧ rayleighValue G v = 0 ∧
      rayleighValue E v = 0 := by
  obtain ⟨U, hU, hHd, hGd⟩ := exists_simultaneously_hollow H G hH hG htrH htrG
  have htrace : Matrix.trace (Uᴴ * E * U) = 0 := by
    rw [Matrix.trace_mul_cycle, hU.1, Matrix.one_mul, htrE]
  obtain ⟨v, hv, hHv, hGv, hEv⟩ := exists_common_neutral_of_hollow
    (Uᴴ * H * U) (Uᴴ * G * U) (Uᴴ * E * U)
    (isHermitian_compression H hH U) (isHermitian_compression G hG U)
    (isHermitian_compression E hE U) hHd hGd htrace (by simpa using hn)
  refine ⟨U *ᵥ v, ?_, ?_, ?_, ?_⟩
  · intro hzero
    apply hv
    have h := congrArg (fun w ↦ Uᴴ *ᵥ w) hzero
    simpa only [Matrix.mulVec_mulVec, hU.2, Matrix.one_mulVec, Matrix.mulVec_zero] using h
  · rwa [← rayleighValue_compression]
  · rwa [← rayleighValue_compression]
  · rwa [← rayleighValue_compression]

/-- The normalized common-neutral-vector theorem, with Euclidean squared norm one. -/
theorem exists_unit_common_neutral {n : ℕ} (H G E : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hG : G.IsHermitian) (hE : E.IsHermitian)
    (htrH : Matrix.trace H = 0) (htrG : Matrix.trace G = 0)
    (htrE : Matrix.trace E = 0) (hn : 3 ≤ n) :
    ∃ v : Fin n → ℂ, vectorEnergy v = 1 ∧ rayleighValue H v = 0 ∧
      rayleighValue G v = 0 ∧ rayleighValue E v = 0 := by
  obtain ⟨v, hv, hHv, hGv, hEv⟩ := exists_common_neutral H G E hH hG hE htrH htrG htrE hn
  let r : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖
  have hr : r ≠ 0 := by
    intro hr
    apply hv
    apply (vectorEnergy_eq_zero v).mp
    rw [vectorEnergy_eq_norm_sq]
    change r ^ 2 = 0
    rw [hr, zero_pow (by decide : 2 ≠ 0)]
  refine ⟨((r⁻¹ : ℝ) : ℂ) • v, ?_, ?_, ?_, ?_⟩
  · rw [vectorEnergy_smul, Complex.normSq_ofReal, vectorEnergy_eq_norm_sq]
    change (r⁻¹ * r⁻¹) * r ^ 2 = 1
    field_simp
  · rw [rayleighValue_smul, hHv, mul_zero]
  · rw [rayleighValue_smul, hGv, mul_zero]
  · rw [rayleighValue_smul, hEv, mul_zero]

end ThreeHermitian
end NoEpsilon
