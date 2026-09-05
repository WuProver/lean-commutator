import CommutatorTheorem.Epsilon.BTJointReduction
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# A library-facing quantitative paving route to Bourgain--Tzafriri

This file records the strongest route available from the current Mathlib library to the
central-submatrix theorem.  Mathlib supplies the finite-dimensional matrix/operator-norm,
spectral, singular-value, polynomial and pigeonhole infrastructure, but it does not currently
contain a quantitative paving, Kadison--Singer, Weaver, restricted-invertibility, or
matrix-concentration theorem with the dimension-free constants needed here.

Accordingly, the genuinely analytic input below is an ordinary `Prop`, not an axiom.  It is the
standard quantitative coordinate-paving formulation: a zero-diagonal matrix can be colored with
at most `C / t^2` colors so that every monochromatic principal compression has norm at most
`t * ‖A‖`.  The main theorem of this file proves, with no additional assumptions, that this single
input implies the exact Bourgain--Tzafriri statement used by the commutator development, with
constant `sqrt C`.

The proof makes the often implicit cardinality step fully explicit using Mathlib's finite
pigeonhole theorem, and then shrinks the largest color class to exactly `floor (ε^2 m)` indices.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing

namespace CommutatorTheorem

/-! ## Exact one-sided input used by the four-matrix reduction -/

/-- The continuous operator represented by a square complex matrix. -/
private noncomputable def matrixCLM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A

/-- The one-sided `k`-matrix restricted-invertibility statement.

This is the exact interface of Theorem 3 in Ravichandran--Srivastava's quantitative multi-paving
argument: `k` zero-diagonal Hermitian contractions have a common coordinate restriction of size
`floor (t^2 m / (6k))` on which every largest Rayleigh quotient is below `t`.  We state the
largest-eigenvalue conclusion by its equivalent Rayleigh-quotient bound because this is the form
directly consumed by Mathlib's self-adjoint operator-norm theorem.

It is an ordinary proposition.  In particular, introducing this interface does not hide a new
Lean axiom. -/
def OneSidedJointRestrictedInvertibility : Prop :=
  ∀ (m k : ℕ), 0 < k →
    ∀ M : Fin k → Matrix (Fin m) (Fin m) ℂ,
      (∀ i, ZeroDiag (M i)) →
      (∀ i, (M i).IsHermitian) →
      (∀ i, ‖M i‖ ≤ 1) →
      ∀ (t : ℝ), 0 < t → t < 1 →
        ∃ f : Fin ⌊(t ^ 2 / ((6 * k : ℕ) : ℝ)) * (m : ℝ)⌋₊ → Fin m,
          Function.Injective f ∧
          ∀ i x,
            (matrixCLM ((M i).submatrix f f)).rayleighQuotient x < t

private lemma hermitian_norm_le_of_two_sided_rayleigh {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian) {t : ℝ}
    (hupper : ∀ x, (matrixCLM B).rayleighQuotient x ≤ t)
    (hlower : ∀ x, (matrixCLM (-B)).rayleighQuotient x ≤ t) :
    ‖B‖ ≤ t := by
  have hsym : (matrixCLM B).IsSymmetric := by
    unfold matrixCLM
    change (Matrix.toEuclideanLin B).IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  rw [matOpNorm_eq_clm_norm]
  change ‖matrixCLM B‖ ≤ t
  rw [(matrixCLM B).norm_eq_iSup_rayleighQuotient hsym]
  apply ciSup_le
  intro x
  have hclm_neg : matrixCLM (-B) = -(matrixCLM B) := by
    unfold matrixCLM
    exact map_neg (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) B
  have hneg : (matrixCLM (-B)).rayleighQuotient x =
      -(matrixCLM B).rayleighQuotient x := by
    rw [hclm_neg]
    exact ContinuousLinearMap.rayleighQuotient_neg_apply _ _
  have hl := hlower x
  rw [hneg] at hl
  exact abs_le.mpr ⟨by linarith, hupper x⟩

/-- The paper's one-sided theorem, applied to `H, -H, G, -G`, gives precisely the
two-sided four-matrix proposition used in `BTJointReduction.lean`. -/
theorem jointRestrictedInvertibility_of_oneSided
    (hOne : OneSidedJointRestrictedInvertibility) :
    JointRestrictedInvertibility := by
  intro m H G hHzd hHherm hHnorm hGzd hGherm hGnorm t ht ht1
  let M : Fin 4 → Matrix (Fin m) (Fin m) ℂ :=
    Fin.cases H (Fin.cases (-H) (Fin.cases G (fun _ ↦ -G)))
  have hMzd : ∀ i, ZeroDiag (M i) := by
    intro i
    fin_cases i
    · exact hHzd
    · intro j
      change -H j j = 0
      rw [hHzd j, neg_zero]
    · exact hGzd
    · intro j
      change -G j j = 0
      rw [hGzd j, neg_zero]
  have hMherm : ∀ i, (M i).IsHermitian := by
    intro i
    fin_cases i
    · exact hHherm
    · exact hHherm.neg
    · exact hGherm
    · exact hGherm.neg
  have hMnorm : ∀ i, ‖M i‖ ≤ 1 := by
    intro i
    fin_cases i
    · exact hHnorm
    · change ‖-H‖ ≤ 1
      rw [norm_neg]
      exact hHnorm
    · exact hGnorm
    · change ‖-G‖ ≤ 1
      rw [norm_neg]
      exact hGnorm
  have hsel := hOne m 4 (by omega) M hMzd hMherm hMnorm t ht ht1
  obtain ⟨f, hf, hray⟩ := hsel
  refine ⟨f, hf, ?_, ?_⟩
  · apply hermitian_norm_le_of_two_sided_rayleigh
      (H.submatrix f f) (hHherm.submatrix f)
    · intro x
      have h := hray (0 : Fin 4) x
      change (matrixCLM (H.submatrix f f)).rayleighQuotient x < t at h
      exact h.le
    · intro x
      have h := hray (1 : Fin 4) x
      change (matrixCLM (-(H.submatrix f f))).rayleighQuotient x < t at h
      exact h.le
  · apply hermitian_norm_le_of_two_sided_rayleigh
      (G.submatrix f f) (hGherm.submatrix f)
    · intro x
      have h := hray (2 : Fin 4) x
      change (matrixCLM (G.submatrix f f)).rayleighQuotient x < t at h
      exact h.le
    · intro x
      have h := hray (3 : Fin 4) x
      change (matrixCLM (-(G.submatrix f f))).rayleighQuotient x < t at h
      exact h.le

/-- Direct packaging of the exact one-sided literature input as the Bourgain--Tzafriri theorem
already used by this repository. -/
theorem bourgain_tzafriri_central_submatrix_of_oneSided
    (hOne : OneSidedJointRestrictedInvertibility) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ K * ε * ‖A‖ :=
  bourgain_tzafriri_central_submatrix_of_jointRestrictedInvertibility
    (jointRestrictedInvertibility_of_oneSided hOne)

section FiberEnumeration

/-- The canonical enumeration of a color fiber by a finite ordinal. -/
noncomputable def colorFiberEmbedding {m r : ℕ} (c : Fin m → Fin r) (a : Fin r) :
    Fin (Fintype.card {i : Fin m // c i = a}) → Fin m :=
  fun j ↦ ((Fintype.equivFin {i : Fin m // c i = a}).symm j).1

lemma colorFiberEmbedding_injective {m r : ℕ} (c : Fin m → Fin r) (a : Fin r) :
    Function.Injective (colorFiberEmbedding c a) := by
  intro i j hij
  apply (Fintype.equivFin {i : Fin m // c i = a}).symm.injective
  exact Subtype.ext hij

lemma colorFiberEmbedding_mem {m r : ℕ} (c : Fin m → Fin r) (a : Fin r)
    (j : Fin (Fintype.card {i : Fin m // c i = a})) :
    c (colorFiberEmbedding c a j) = a :=
  ((Fintype.equivFin {i : Fin m // c i = a}).symm j).2

lemma colorFiberEmbedding_surjective_on_fiber {m r : ℕ} (c : Fin m → Fin r)
    (a : Fin r) {i : Fin m} (hi : c i = a) :
    ∃ j, colorFiberEmbedding c a j = i := by
  let x : {i : Fin m // c i = a} := ⟨i, hi⟩
  refine ⟨Fintype.equivFin {i : Fin m // c i = a} x, ?_⟩
  simp [colorFiberEmbedding, x]

end FiberEnumeration

/-- A quantitative coordinate-paving statement in a form directly supported by Mathlib's
finite matrix API.

The inequality `r * t^2 ≤ C` is the division-free version of the usual color bound
`r ≤ C / t^2`.  Every color fiber is enumerated by `colorFiberEmbedding`, so its principal
compression is a square matrix indexed by a `Fin` type and carries the repository's operator norm
instance without further transport. -/
def QuantitativeZeroDiagonalPaving (C : ℝ) : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
    ZeroDiag A →
    ∀ (t : ℝ), 0 < t → t < 1 →
      ∃ (r : ℕ), 0 < r ∧
        ∃ c : Fin m → Fin r,
          (r : ℝ) * t ^ 2 ≤ C ∧
          ∀ a : Fin r,
            ‖A.submatrix (colorFiberEmbedding c a) (colorFiberEmbedding c a)‖ ≤
              t * ‖A‖

private lemma floor_epsilon_card_le (m : ℕ) {eps : ℝ}
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    ⌊eps ^ 2 * (m : ℝ)⌋₊ ≤ m := by
  have hsq0 : 0 ≤ eps ^ 2 := sq_nonneg eps
  have hsqm : eps ^ 2 * (m : ℝ) ≤ (m : ℝ) := by
    have hsq1 : eps ^ 2 ≤ 1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_right hsq1 (Nat.cast_nonneg m)
  exact_mod_cast (Nat.floor_le (mul_nonneg hsq0 (Nat.cast_nonneg m))).trans hsqm

/-- Quantitative paving gives a central submatrix of the exact Bourgain--Tzafriri cardinality.

This is the library-facing bridge: all spectral/analytic difficulty is isolated in
`QuantitativeZeroDiagonalPaving C`; the rest is finite pigeonhole, exact-cardinality selection,
and operator-norm monotonicity for principal submatrices. -/
theorem central_submatrix_of_quantitativePaving {C : ℝ} (hC : 0 < C)
    (hpave : QuantitativeZeroDiagonalPaving C) :
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ Real.sqrt C * ε * ‖A‖ := by
  intro m A hA ε hε hε1
  let q : ℕ := ⌊ε ^ 2 * (m : ℝ)⌋₊
  let t : ℝ := Real.sqrt C * ε
  have hC0 : 0 ≤ C := hC.le
  have hsqrtC : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have ht0 : 0 < t := mul_pos hsqrtC hε
  by_cases ht1 : t < 1
  · obtain ⟨r, hr0, c, hrt, hblocks⟩ := hpave m A hA t ht0 ht1
    have hroot_sq : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC0
    have hreps : (r : ℝ) * ε ^ 2 ≤ 1 := by
      have hscaled : C * ((r : ℝ) * ε ^ 2) ≤ C * 1 := by
        calc
          C * ((r : ℝ) * ε ^ 2) = (r : ℝ) * t ^ 2 := by
            dsimp [t]
            rw [mul_pow, hroot_sq]
            ring
          _ ≤ C := hrt
          _ = C * 1 := by ring
      exact le_of_mul_le_mul_left hscaled hC
    have hq_real : (q : ℝ) ≤ ε ^ 2 * (m : ℝ) := by
      dsimp [q]
      exact Nat.floor_le (mul_nonneg (sq_nonneg ε) (Nat.cast_nonneg m))
    have hrq_real : ((r * q : ℕ) : ℝ) ≤ (m : ℝ) := by
      rw [Nat.cast_mul]
      calc
        (r : ℝ) * (q : ℝ) ≤ (r : ℝ) * (ε ^ 2 * (m : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hq_real (Nat.cast_nonneg r)
        _ = ((r : ℝ) * ε ^ 2) * (m : ℝ) := by ring
        _ ≤ 1 * (m : ℝ) :=
          mul_le_mul_of_nonneg_right hreps (Nat.cast_nonneg m)
        _ = (m : ℝ) := one_mul _
    have hrq : r * q ≤ m := by exact_mod_cast hrq_real
    letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr0
    have hrq' : Fintype.card (Fin r) * q ≤ Fintype.card (Fin m) := by simpa using hrq
    obtain ⟨a, ha⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
      (f := c) (n := q) hrq'
    have ha' : q ≤ Fintype.card {i : Fin m // c i = a} := by
      rw [Fintype.card_subtype]
      exact ha
    let g : Fin q → Fin (Fintype.card {i : Fin m // c i = a}) := Fin.castLE ha'
    have hg : Function.Injective g := Fin.castLE_injective ha'
    let e := colorFiberEmbedding c a
    let f : Fin q → Fin m := e ∘ g
    have he : Function.Injective e := colorFiberEmbedding_injective c a
    have hf : Function.Injective f := he.comp hg
    refine ⟨f, hf, ?_⟩
    have hshrink :
        ‖A.submatrix f f‖ ≤ ‖A.submatrix e e‖ := by
      have h := submatrix_norm_le g hg (A.submatrix e e)
      simpa [f, e, Function.comp_def, Matrix.submatrix_apply] using h
    calc
      ‖A.submatrix f f‖ ≤ ‖A.submatrix e e‖ := hshrink
      _ ≤ t * ‖A‖ := hblocks a
      _ = Real.sqrt C * ε * ‖A‖ := by rfl
  · have htge : 1 ≤ t := le_of_not_gt ht1
    have hqle : q ≤ m := floor_epsilon_card_le m hε.le hε1.le
    let f : Fin q → Fin m := Fin.castLE hqle
    have hf : Function.Injective f := Fin.castLE_injective hqle
    refine ⟨f, hf, ?_⟩
    have hsub : ‖A.submatrix f f‖ ≤ ‖A‖ := by
      simpa only [Matrix.submatrix] using submatrix_norm_le f hf A
    calc
      ‖A.submatrix f f‖ ≤ ‖A‖ := hsub
      _ = 1 * ‖A‖ := by ring
      _ ≤ t * ‖A‖ := mul_le_mul_of_nonneg_right htge (norm_nonneg A)
      _ = Real.sqrt C * ε * ‖A‖ := by rfl

/-- Existential packaging in exactly the shape of `bourgain_tzafriri_central_submatrix`.
No axiom is introduced: a proof of quantitative paving is an explicit theorem parameter. -/
theorem bourgain_tzafriri_central_submatrix_of_quantitativePaving
    {C : ℝ} (hC : 0 < C) (hpave : QuantitativeZeroDiagonalPaving C) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
          Function.Injective f ∧
          ‖A.submatrix f f‖ ≤ K * ε * ‖A‖ := by
  refine ⟨Real.sqrt C, Real.sqrt_pos.2 hC, ?_⟩
  exact central_submatrix_of_quantitativePaving hC hpave

end CommutatorTheorem
