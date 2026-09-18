import CommutatorTheorem.Shared.THConvexity
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-!
# Shared unitary zero-diagonalization

Fillmore's theorem is used by both commutator proofs. Its original public names in
`CommutatorTheorem` are preserved so importing either branch remains compatible.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instCStarRing
attribute [local instance] Matrix.instL2OpNormedSpace

open CommutatorTheorem

namespace CommutatorTheorem

/-! ## Fillmore's Lemma -/

/-- A matrix is unitary if U * Uᴴ = 1 and Uᴴ * U = 1. -/
def IsUnitaryMatrix {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1

/-- Extract the (n+1)×(n+1) lower-right subblock of an (n+2)×(n+2) matrix. -/
private noncomputable def lowerRight' {n : ℕ}
    (C : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j => C i.succ j.succ

private lemma lowerRight'_trace {n : ℕ}
    (C : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    (lowerRight' C).trace = ∑ i : Fin (n + 1), C i.succ i.succ := by
  simp [lowerRight', Matrix.trace, Matrix.diag, Matrix.of_apply]

/-- Helper: Re of a Fintype sum. -/
private lemma re_fintype_sum {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    (∑ i, f i).re = ∑ i, (f i).re :=
  map_sum Complex.reAddGroupHom f Finset.univ

/-- Given a trace-zero matrix with all nonzero diagonal entries, there exists an
    index j ≠ 0 whose diagonal entry projects negatively onto A₀₀. This is the
    pigeonhole step: since ∑ Re(Aᵢᵢ·conj(A₀₀)) = 0 and the i=0 term is |A₀₀|² > 0,
    some other term must be negative. -/
private lemma exists_neg_proj (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hTrace : A.trace = 0)
    (hDiag : ∀ i, A i i ≠ 0) :
    ∃ j : Fin (n + 2), j ≠ 0 ∧ (A j j * starRingEnd ℂ (A 0 0)).re < 0 := by
  by_contra h
  push Not at h
  have hA00 : A 0 0 ≠ 0 := hDiag 0
  have hTotalSum : ∑ i : Fin (n + 2), (A i i * starRingEnd ℂ (A 0 0)).re = 0 := by
    rw [← re_fintype_sum, ← Finset.sum_mul]
    have : ∑ i : Fin (n + 2), A i i = 0 := by
      have := hTrace; simp only [Matrix.trace, Matrix.diag] at this; exact this
    rw [this, zero_mul]; rfl
  have h00 : 0 < (A 0 0 * starRingEnd ℂ (A 0 0)).re := by
    rw [starRingEnd_apply]; simp [Complex.mul_conj, Complex.normSq_pos, hA00]
  have hTail : 0 ≤ ∑ i ∈ Finset.univ.erase 0, (A i i * starRingEnd ℂ (A 0 0)).re := by
    apply Finset.sum_nonneg
    intro i hi; apply h; exact Finset.ne_of_mem_erase hi
  linarith [Finset.add_sum_erase Finset.univ
    (fun i => (A i i * starRingEnd ℂ (A 0 0)).re) (Finset.mem_univ (0 : Fin (n+2)))]

/-- If A.mulVec v = 0, the Rayleigh quotient ∑ᵢⱼ conj(vᵢ)·Aᵢⱼ·vⱼ = 0. -/
private lemma rayleigh_zero_of_mulVec_zero {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ)
    (v : Fin m → ℂ)
    (hv : A.mulVec v = 0) :
    ∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j = 0 := by
  have hmv : ∀ i, ∑ j, A i j * v j = 0 := by
    intro i
    have h1 := congr_fun hv i
    simp only [Pi.zero_apply] at h1
    rw [show A.mulVec v i = ∑ j, A i j * v j from by simp [Matrix.mulVec, dotProduct]] at h1
    exact h1
  simp_rw [show ∀ i j, starRingEnd ℂ (v i) * A i j * v j =
    starRingEnd ℂ (v i) * (A i j * v j) from fun i j => by ring]
  simp_rw [← Finset.mul_sum, hmv, mul_zero, Finset.sum_const_zero]

/-- ∑ᵢ |vᵢ|² > 0 for a nonzero vector v. -/
private lemma normSq_sum_pos {m : ℕ} (v : Fin m → ℂ) (hv : v ≠ 0) :
    0 < ∑ i, Complex.normSq (v i) := by
  apply Finset.sum_pos'
  · intro i _; exact Complex.normSq_nonneg _
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact ⟨i, Finset.mem_univ _, by rwa [Complex.normSq_pos]⟩

/-- If det A = 0, there exists a unit vector with zero Rayleigh quotient.
    This is the eigenvalue-0 case: A has a nontrivial kernel element v,
    so Av = 0 implies v†Av = 0. Normalizing v gives a unit vector. -/
private lemma zero_mem_nr_of_det_zero {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ)
    (hdet : A.det = 0) :
    ∃ v : Fin m → ℂ,
      (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j = 0) ∧
      (∑ i, Complex.normSq (v i) = 1) := by
  rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet
  obtain ⟨v, hv_ne, hv_mul⟩ := hdet
  set s := ∑ i, Complex.normSq (v i)
  have hs_pos : 0 < s := normSq_sum_pos v hv_ne
  have hs_sqrt_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs_pos
  set c : ℂ := ↑((Real.sqrt s)⁻¹)
  set w := fun i => c * v i
  refine ⟨w, ?_, ?_⟩
  · have hmulvec_w : A.mulVec w = 0 := by
      ext i
      simp only [Pi.zero_apply]
      rw [show A.mulVec w i = ∑ j, A i j * (c * v j) from by simp [Matrix.mulVec, dotProduct, w]]
      simp_rw [show ∀ j, A i j * (c * v j) = c * (A i j * v j) from fun j => by ring]
      rw [← Finset.mul_sum]
      have h1 := congr_fun hv_mul i
      simp only [Pi.zero_apply] at h1
      rw [show A.mulVec v i = ∑ j, A i j * v j from by simp [Matrix.mulVec, dotProduct]] at h1
      rw [h1, mul_zero]
    exact rayleigh_zero_of_mulVec_zero A w hmulvec_w
  · simp_rw [w, Complex.normSq_mul, ← Finset.mul_sum]
    simp only [c, Complex.normSq_ofReal]
    rw [show (Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹ = ((Real.sqrt s) * (Real.sqrt s))⁻¹ from by
      rw [mul_inv_rev]]
    rw [Real.mul_self_sqrt (le_of_lt hs_pos)]
    exact inv_mul_cancel₀ (ne_of_gt hs_pos)

-- Normalization: if there exists a nonzero v with R(v) = 0,
-- then there exists a unit vector with R(v) = 0.
private lemma rayleigh_zero_normalize {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ)
    (u : Fin m → ℂ) (hu_ne : u ≠ 0)
    (hR : ∑ i, ∑ j, starRingEnd ℂ (u i) * A i j * u j = 0) :
    ∃ v : Fin m → ℂ,
      (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j = 0) ∧
      (∑ i, Complex.normSq (v i) = 1) := by
  set s := ∑ i, Complex.normSq (u i)
  have hs_pos : 0 < s := by
    apply Finset.sum_pos'
    · intro i _; exact Complex.normSq_nonneg _
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hu_ne
      exact ⟨i, Finset.mem_univ _, by rwa [Complex.normSq_pos]⟩
  set c : ℂ := ↑((Real.sqrt s)⁻¹)
  set v := fun i => c * u i
  refine ⟨v, ?_, ?_⟩
  · have : ∀ i j, starRingEnd ℂ (v i) * A i j * v j =
        starRingEnd ℂ c * c * (starRingEnd ℂ (u i) * A i j * u j) := by
      intro i j; simp only [v, starRingEnd_apply, star_mul]; ring
    simp_rw [this]
    simp_rw [← Finset.mul_sum]
    rw [hR, mul_zero]
  · simp_rw [v, Complex.normSq_mul, ← Finset.mul_sum]
    simp only [c, Complex.normSq_ofReal]
    rw [show (Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹ = ((Real.sqrt s) * (Real.sqrt s))⁻¹ from by
      rw [mul_inv_rev]]
    rw [Real.mul_self_sqrt (le_of_lt hs_pos)]
    exact inv_mul_cancel₀ (ne_of_gt hs_pos)

-- 2×2 trace-zero invertible case: 0 is in the numerical range.
-- Strategy: The Rayleigh quotient constraint a*p + b*w + c*conj(w) = 0
-- is ℝ-linear in (p, Re w, Im w). By rank-nullity (3 vars, 2 real equations),
-- the kernel has dim ≥ 1. A nonzero kernel element, scaled to the ellipsoid
-- p²+4|w|²=1, gives the desired unit vector.
set_option maxHeartbeats 1600000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
private lemma zero_mem_nr_2x2
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hTrace : A.trace = 0)
    (hDiag : ∀ i, A i i ≠ 0)
    (hdet : ¬A.det = 0) :
    ∃ v : Fin 2 → ℂ,
      (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j = 0) ∧
      (∑ i, Complex.normSq (v i) = 1) := by
  set a := A 0 0
  set b := A 0 1
  set c := A 1 0
  have ha : a ≠ 0 := hDiag 0
  have hA11 : A 1 1 = -a := by
    have ht := hTrace; simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at ht
    linear_combination ht
  let L : (Fin 3 → ℝ) →ₗ[ℝ] ℂ :=
    { toFun := fun v => a * ↑(v 0) + (b + c) * ↑(v 1) + Complex.I * (b - c) * ↑(v 2)
      map_add' := by intro x y; simp only [Pi.add_apply, Complex.ofReal_add]; ring
      map_smul' := by
        intro r x
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply]
        change a * (↑r * ↑(x 0)) + (b + c) * (↑r * ↑(x 1)) + Complex.I * (b - c) * (↑r * ↑(x 2)) =
          ↑r * (a * ↑(x 0) + (b + c) * ↑(x 1) + Complex.I * (b - c) * ↑(x 2))
        ring }
  have hL_ker : L.ker ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have h2 : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
    omega
  obtain ⟨v0, hv0_mem, hv0_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL_ker
  rw [LinearMap.mem_ker] at hv0_mem
  set p0 := v0 0; set x0 := v0 1; set y0 := v0 2
  set w0 : ℂ := ↑x0 + Complex.I * ↑y0
  have hL_eq : a * ↑p0 + (b + c) * ↑x0 + Complex.I * (b - c) * ↑y0 = 0 := hv0_mem
  have hconj_w0 : starRingEnd ℂ w0 = ↑x0 - Complex.I * ↑y0 := by
    rw [show w0 = ↑x0 + Complex.I * ↑y0 from rfl, starRingEnd_apply]
    rw [star_add, star_mul]
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hw0_eq : a * ↑p0 + b * w0 + c * starRingEnd ℂ w0 = 0 := by
    rw [hconj_w0, show w0 = ↑x0 + Complex.I * ↑y0 from rfl]
    linear_combination hL_eq
  have hv0_ne' : p0 ≠ 0 ∨ x0 ≠ 0 ∨ y0 ≠ 0 := by
    by_contra h; push Not at h; obtain ⟨hp, hx, hy⟩ := h; apply hv0_ne
    ext i; fin_cases i
    · exact hp
    · exact hx
    · exact hy
  set q := p0 ^ 2 + 4 * (x0 ^ 2 + y0 ^ 2)
  have hq_pos : 0 < q := by rcases hv0_ne' with h | h | h <;> positivity
  set sq := Real.sqrt q
  have hsq_pos : 0 < sq := Real.sqrt_pos.mpr hq_pos
  have hsq_ne : sq ≠ 0 := ne_of_gt hsq_pos
  have hsq_c_ne : (↑sq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq_ne
  set p := p0 / sq; set w := w0 / ↑sq
  have hw_eq : a * ↑p + b * w + c * starRingEnd ℂ w = 0 := by
    have hconj_w : starRingEnd ℂ w = starRingEnd ℂ w0 / ↑sq := by
      rw [show w = w0 / ↑sq from rfl, starRingEnd_apply, star_div₀]
      rw [show star (↑sq : ℂ) = ↑sq from Complex.conj_ofReal sq]; rfl
    rw [show p = p0 / sq from rfl, show w = w0 / ↑sq from rfl, hconj_w, Complex.ofReal_div]
    rw [show a * (↑p0 / ↑sq) + b * (w0 / ↑sq) + c * (starRingEnd ℂ w0 / ↑sq) =
        (a * ↑p0 + b * w0 + c * starRingEnd ℂ w0) / ↑sq from by ring]
    rw [hw0_eq, zero_div]
  have hnorm_w0 : Complex.normSq w0 = x0 ^ 2 + y0 ^ 2 := by
    rw [show w0 = ↑x0 + Complex.I * ↑y0 from rfl]
    simp [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq_sq : sq ^ 2 = q := Real.sq_sqrt (le_of_lt hq_pos)
  have hell : p ^ 2 + 4 * Complex.normSq w = 1 := by
    rw [show Complex.normSq w = (x0 ^ 2 + y0 ^ 2) / q from by
      rw [show w = w0 / ↑sq from rfl, Complex.normSq_div, Complex.normSq_ofReal, hnorm_w0]
      rw [Real.mul_self_sqrt (le_of_lt hq_pos)]]
    rw [show p = p0 / sq from rfl, div_pow, hsq_sq]
    field_simp; ring
  have hp_bound : -1 < p := by
    by_contra h; push Not at h
    have hnw0 : Complex.normSq w = 0 := by nlinarith [hell, Complex.normSq_nonneg w]
    have hw0' : w = 0 := by rwa [Complex.normSq_eq_zero] at hnw0
    have hp_eq : p = -1 := by nlinarith [Complex.normSq_nonneg w, hell]
    apply ha
    have := hw_eq
    rw [hp_eq, hw0'] at this
    simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one, mul_zero, add_zero,
      map_zero, neg_eq_zero] at this
    exact this
  set α := ((1 + p) / 2 : ℝ)
  have hα_pos : 0 < α := by change 0 < (1 + p) / 2; linarith
  set u : Fin 2 → ℂ := ![↑α, w]
  have hu_ne : u ≠ 0 := by
    intro h; have := congr_fun h 0
    simp [u, Matrix.cons_val_zero] at this; linarith
  apply rayleigh_zero_normalize A u hu_ne
  simp only [u, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hA11]
  simp only [Complex.conj_ofReal]
  have hbwcw : b * w + c * starRingEnd ℂ w = -(a * ↑p) := by linear_combination hw_eq
  have hcww : starRingEnd ℂ w * w = ↑(Complex.normSq w) := by
    rw [show starRingEnd ℂ w * w = w * starRingEnd ℂ w from by ring]
    exact Complex.mul_conj w
  have hnw : Complex.normSq w = (1 - p ^ 2) / 4 := by linarith [hell]
  rw [show ↑α * a * ↑α + ↑α * b * w + (starRingEnd ℂ w * c * ↑α + starRingEnd ℂ w * -a * w) =
      ↑α * (a * ↑α + (b * w + c * starRingEnd ℂ w)) - a * (starRingEnd ℂ w * w) from by ring]
  rw [hbwcw, hcww, hnw]
  have : ↑α = (↑p + 1) / 2 := by ring
  rw [this]
  push_cast
  ring

/-- Sum of a function supported on two points {i₀, j₀} equals f(i₀) + f(j₀). -/
private lemma finset_sum_support_pair {n : ℕ}
    (i₀ j₀ : Fin (n + 1 + 2)) (hij : i₀ ≠ j₀)
    (f : Fin (n + 1 + 2) → ℂ)
    (hf : ∀ k, k ≠ i₀ → k ≠ j₀ → f k = 0) :
    ∑ k, f k = f i₀ + f j₀ := by
  have h1 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i₀)
  rw [← h1]; congr 1
  have hj_mem : j₀ ∈ Finset.univ.erase i₀ :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
  have h2 := Finset.add_sum_erase (Finset.univ.erase i₀) f hj_mem
  rw [← h2]
  have htail : ∑ x ∈ (Finset.univ.erase i₀).erase j₀, f x = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_erase] at hk
    exact hf k (Finset.mem_erase.mp hk.2).1 hk.1
  rw [htail, add_zero]

-- Quadratic a·t² + b·t + c with a < 0, c > 0 has a nonneg root (by discriminant).
set_option maxHeartbeats 800000 in
-- Needed for the IVT Rayleigh quotient argument: real quadratic with sign change.
private lemma quadratic_has_nonneg_root {a b c : ℝ} (ha : a < 0) (hc : 0 < c) :
    ∃ t : ℝ, 0 ≤ t ∧ a * t ^ 2 + b * t + c = 0 := by
  have ha_ne : a ≠ 0 := ne_of_lt ha
  have hdisc : 0 < b ^ 2 - 4 * a * c := by nlinarith
  set D := Real.sqrt (b ^ 2 - 4 * a * c)
  have hD_sq : D ^ 2 = b ^ 2 - 4 * a * c := Real.sq_sqrt hdisc.le
  set t₀ := (-b - D) / (2 * a)
  refine ⟨t₀, ?_, ?_⟩
  · apply div_nonneg_of_nonpos
    · linarith [neg_le_abs b, show D ≥ |b| from by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)]
    · linarith
  · have key : 2 * a * t₀ = -b - D := by simp only [t₀]; field_simp [ha_ne]
    have hsq : (2 * a * t₀ + b) ^ 2 = D ^ 2 := by rw [key]; ring
    have hfour : 4 * a * (a * t₀ ^ 2 + b * t₀ + c) = 0 := by nlinarith [hsq, hD_sq]
    rcases mul_eq_zero.mp hfour with h | h
    · exact absurd h (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) ha_ne)
    · exact h

-- Segment embedding: for distinct indices i₀, j₀ in Fin m (m ≥ 3),
-- any point on [A_{i₀,i₀}, A_{j₀,j₀}] is in NR(A).
-- Proof: embed the 2×2 segment result into the full matrix via zero-extension.
private lemma segment_diag_in_nr {n : ℕ}
    (A : Matrix (Fin (n + 1 + 2)) (Fin (n + 1 + 2)) ℂ)
    (i₀ j₀ : Fin (n + 1 + 2)) (hij : i₀ ≠ j₀)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ v : Fin (n + 1 + 2) → ℂ,
      (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j =
        ↑t * A i₀ i₀ + ↑(1 - t) * A j₀ j₀) ∧
      (∑ i, Complex.normSq (v i) = 1) := by
  -- Build the 2×2 compression
  set M : Matrix (Fin 2) (Fin 2) ℂ := fun a b =>
    A (if a = 0 then i₀ else j₀) (if b = 0 then i₀ else j₀)
  have hM00 : M 0 0 = A i₀ i₀ := by simp [M]
  have hM11 : M 1 1 = A j₀ j₀ := by simp [M]
  obtain ⟨w, hR, hN⟩ := CommutatorTheorem.THConvexity.segment_diag_in_nr_2x2 M t ht0 ht1
  rw [hM00, hM11] at hR
  -- Embed w into full space
  set v : Fin (n + 1 + 2) → ℂ := fun k =>
    if k = i₀ then w 0 else if k = j₀ then w 1 else 0
  have hvi0 : v i₀ = w 0 := by simp [v]
  have hvj0 : v j₀ = w 1 := by simp [v, hij.symm]
  have hvk : ∀ k, k ≠ i₀ → k ≠ j₀ → v k = 0 := by
    intro k hk0 hkj; simp [v, hk0, hkj]
  refine ⟨v, ?_, ?_⟩
  · -- Rayleigh quotient
    simp_rw [show ∀ i j, starRingEnd ℂ (v i) * A i j * v j =
      starRingEnd ℂ (v i) * (A i j * v j) from fun i j => by ring]
    simp_rw [← Finset.mul_sum]
    have houter : ∀ i, i ≠ i₀ → i ≠ j₀ →
        starRingEnd ℂ (v i) * ∑ k, A i k * v k = 0 := by
      intro i hi0 hij'; rw [show v i = 0 from hvk i hi0 hij', map_zero, zero_mul]
    rw [finset_sum_support_pair i₀ j₀ hij _ houter]
    have hinner : ∀ i, ∑ k, A i k * v k = A i i₀ * w 0 + A i j₀ * w 1 := by
      intro i
      have h1 := finset_sum_support_pair i₀ j₀ hij (fun k => A i k * v k)
        (fun k hk0 hkj => show A i k * v k = 0 by rw [hvk k hk0 hkj, mul_zero])
      simp only at h1; rw [h1, hvi0, hvj0]
    simp only [hinner, hvi0, hvj0]
    rw [← hR]
    simp only [Fin.sum_univ_two, M]
    simp only [show (1 : Fin 2) ≠ 0 from by omega,
      ite_true, ite_false]
    ring
  · -- Norm
    have h1 : ∀ k, Complex.normSq (v k) =
        if k = i₀ then Complex.normSq (w 0)
        else if k = j₀ then Complex.normSq (w 1) else 0 := by
      intro k; by_cases hk0 : k = i₀
      · subst hk0; rw [hvi0, if_pos rfl]
      · by_cases hkj : k = j₀
        · subst hkj; rw [hvj0, if_neg hk0, if_pos rfl]
        · rw [hvk k hk0 hkj, Complex.normSq_zero, if_neg hk0, if_neg hkj]
    simp_rw [h1]
    -- Each term is 0 except at i₀ and j₀
    have : ∀ x, (if x = i₀ then Complex.normSq (w 0)
        else if x = j₀ then Complex.normSq (w 1) else 0) =
        (if x = i₀ then Complex.normSq (w 0) else 0) +
        (if x = j₀ then Complex.normSq (w 1) else 0) := by
      intro x; by_cases hx : x = i₀ <;> by_cases hxj : x = j₀ <;> simp_all
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [Fin.sum_univ_two] at hN; linarith

-- Orthogonal compression: given a unit vector v₁ with v₁(k₀) = 0,
-- for any t ∈ [0,1], produce a unit vector v with
-- R_A(v) = t * R_A(v₁) + (1-t) * A(k₀,k₀)
-- and v(i) = 0 whenever v₁(i) = 0 and i ≠ k₀.
set_option maxHeartbeats 1600000 in
-- orthogonal compression via 2x2 embedding
open Complex Finset in
private lemma ortho_compress {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ)
    (v₁ : Fin m → ℂ) (k₀ : Fin m)
    (hv₁_unit : ∑ i, Complex.normSq (v₁ i) = 1)
    (hv₁_zero : v₁ k₀ = 0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let R₁ := ∑ i, ∑ j, starRingEnd ℂ (v₁ i) * A i j * v₁ j
    ∃ v : Fin m → ℂ,
      (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j =
        ↑t * R₁ + ↑(1 - t) * A k₀ k₀) ∧
      (∑ i, Complex.normSq (v i) = 1) ∧
      (∀ i, v₁ i = 0 ∧ i ≠ k₀ → v i = 0) := by
  intro R₁
  set M : Matrix (Fin 2) (Fin 2) ℂ := fun a b =>
    if a = 0 then
      (if b = 0 then R₁
       else ∑ i, starRingEnd ℂ (v₁ i) * A i k₀)
    else
      (if b = 0 then ∑ j, A k₀ j * v₁ j else A k₀ k₀)
  have hM00 : M 0 0 = R₁ := by simp [M]
  have hM11 : M 1 1 = A k₀ k₀ := by simp [M]
  obtain ⟨w, hR, hN⟩ :=
    THConvexity.segment_diag_in_nr_2x2 M t ht0 ht1
  rw [hM00, hM11] at hR
  set v : Fin m → ℂ := fun i =>
    w 0 * v₁ i + w 1 * (if i = k₀ then 1 else 0)
  refine ⟨v, ?_, ?_, ?_⟩
  · -- Rayleigh quotient
    set col := fun i => ∑ j, A i j * v₁ j
    have hinner : ∀ i, ∑ x, A i x * v x =
        w 0 * col i + w 1 * A i k₀ := by
      intro i; simp only [v, col]
      have : ∀ x,
          A i x * (w 0 * v₁ x +
            w 1 * (if x = k₀ then (1 : ℂ) else 0)) =
          w 0 * (A i x * v₁ x) +
          w 1 * (if x = k₀ then A i k₀ else 0) := by
        intro x
        by_cases hx : x = k₀
        · subst hx; simp; ring
        · simp [hx]; ring
      simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [Finset.sum_ite_eq']
    simp_rw [show ∀ i j, starRingEnd ℂ (v i) * A i j * v j =
      starRingEnd ℂ (v i) * (A i j * v j) from fun i j => by ring]
    simp_rw [← Finset.mul_sum, hinner]
    simp only [v]
    simp_rw [map_add, map_mul, add_mul, mul_add,
      Finset.sum_add_distrib]
    simp_rw [show ∀ i,
      starRingEnd ℂ (w 0) * starRingEnd ℂ (v₁ i) *
        (w 0 * col i) =
      starRingEnd ℂ (w 0) * w 0 *
        (starRingEnd ℂ (v₁ i) * col i)
      from fun i => by ring]
    simp_rw [show ∀ i,
      starRingEnd ℂ (w 0) * starRingEnd ℂ (v₁ i) *
        (w 1 * A i k₀) =
      starRingEnd ℂ (w 0) * w 1 *
        (starRingEnd ℂ (v₁ i) * A i k₀)
      from fun i => by ring]
    simp_rw [show ∀ i,
      starRingEnd ℂ (w 1) *
      starRingEnd ℂ ((if i = k₀ then (1 : ℂ) else 0)) *
      (w 0 * col i) = starRingEnd ℂ (w 1) * w 0 *
      (starRingEnd ℂ (if i = k₀ then (1 : ℂ) else 0) *
        col i)
      from fun i => by ring]
    simp_rw [show ∀ i,
      starRingEnd ℂ (w 1) *
      starRingEnd ℂ ((if i = k₀ then (1 : ℂ) else 0)) *
      (w 1 * A i k₀) = starRingEnd ℂ (w 1) * w 1 *
      (starRingEnd ℂ (if i = k₀ then (1 : ℂ) else 0) *
        A i k₀)
      from fun i => by ring]
    simp_rw [← Finset.mul_sum]
    have hs1 : ∑ i, starRingEnd ℂ (v₁ i) * col i = R₁ := by
      simp only [col, R₁]; simp_rw [Finset.mul_sum]
      congr 1; ext i; congr 1; ext j; ring
    have hs3 :
        ∑ i, starRingEnd ℂ
          (if i = k₀ then (1 : ℂ) else 0) * col i =
        col k₀ := by
      have : ∀ i,
          starRingEnd ℂ
            (if i = k₀ then (1 : ℂ) else 0) * col i =
          if i = k₀ then col k₀ else 0 := by
        intro i; by_cases hi : i = k₀ <;> simp [hi]
      simp_rw [this]; simp [Finset.sum_ite_eq']
    have hs4 :
        ∑ i, starRingEnd ℂ
          (if i = k₀ then (1 : ℂ) else 0) * A i k₀ =
        A k₀ k₀ := by
      have : ∀ i,
          starRingEnd ℂ
            (if i = k₀ then (1 : ℂ) else 0) * A i k₀ =
          if i = k₀ then A k₀ k₀ else 0 := by
        intro i; by_cases hi : i = k₀ <;> simp [hi]
      simp_rw [this]; simp [Finset.sum_ite_eq']
    rw [hs1, hs3, hs4, ← hR]
    simp only [Fin.sum_univ_two, M]
    simp only [show (1 : Fin 2) ≠ 0 from by omega,
      ite_true, ite_false]
    ring
  · -- Norm
    simp only [v]
    simp_rw [Complex.normSq_add, Complex.normSq_mul,
      Finset.sum_add_distrib]
    have h1 : ∑ i, Complex.normSq (w 0) * Complex.normSq (v₁ i) =
        Complex.normSq (w 0) := by
      rw [← Finset.mul_sum, hv₁_unit, mul_one]
    have h2 : ∑ i : Fin m, Complex.normSq (w 1) *
        Complex.normSq (if i = k₀ then (1 : ℂ) else 0) =
        Complex.normSq (w 1) := by
      have : ∀ i : Fin m,
          Complex.normSq (if i = k₀ then (1 : ℂ) else 0) =
          if i = k₀ then 1 else 0 := by
        intro i
        by_cases hi : i = k₀ <;>
          simp [hi, Complex.normSq_one, Complex.normSq_zero]
      simp_rw [this]; rw [← Finset.mul_sum]
      rw [show ∑ i : Fin m,
          (if i = k₀ then (1 : ℝ) else 0) = 1
        from by simp [Finset.sum_ite_eq']]
      ring
    have h3 : ∑ i : Fin m, 2 * (w 0 * v₁ i *
        (starRingEnd ℂ)
          (w 1 * if i = k₀ then 1 else 0)).re = 0 := by
      have key : ∀ i : Fin m,
          v₁ i * starRingEnd ℂ
            (if i = k₀ then (1 : ℂ) else 0) = 0 := by
        intro i
        by_cases hi : i = k₀ <;> simp [hi, hv₁_zero]
      have : ∀ i : Fin m, (w 0 * v₁ i *
          (starRingEnd ℂ)
            (w 1 * if i = k₀ then 1 else 0)).re = 0 := by
        intro i; rw [map_mul]
        rw [show w 0 * v₁ i *
          (starRingEnd ℂ (w 1) *
           starRingEnd ℂ
             (if i = k₀ then (1 : ℂ) else 0)) =
          w 0 * starRingEnd ℂ (w 1) *
          (v₁ i * starRingEnd ℂ
             (if i = k₀ then (1 : ℂ) else 0))
          from by ring, key i, mul_zero, zero_re]
      simp_rw [this, mul_zero, Finset.sum_const_zero]
    rw [h1, h2, h3, add_zero]
    simp only [Fin.sum_univ_two] at hN; linarith
  · -- Support preservation
    intro i ⟨hvi, hik⟩
    simp only [v, hvi, mul_zero, hik, ite_false, add_zero]

-- Iterative averaging of diagonal entries via orthogonal compression.
set_option maxHeartbeats 6400000 in
-- iterative diagonal averaging via orthogonal compression
open Complex Finset in
private lemma iter_diag_avg {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) :
    ∀ p : ℕ, p < m →
    ∃ v : Fin m → ℂ,
      (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j =
        (↑(p + 1 : ℕ) : ℂ)⁻¹ *
          ∑ i : Fin m,
            if (i : ℕ) ≤ p then A i i else 0) ∧
      (∑ i, Complex.normSq (v i) = 1) ∧
      (∀ i : Fin m, p < (i : ℕ) → v i = 0) := by
  intro p
  induction p with
  | zero =>
    intro _
    have hm0 : 0 < m := by omega
    set e₀ : Fin m → ℂ := fun i =>
      if i = ⟨0, hm0⟩ then 1 else 0
    refine ⟨e₀, ?_, ?_, ?_⟩
    · -- Rayleigh = A₀₀
      simp only [Nat.zero_add, Nat.cast_one, inv_one, one_mul]
      have h1 : ∀ k j,
          starRingEnd ℂ (e₀ k) * A k j * e₀ j =
          if k = ⟨0, hm0⟩ ∧ j = ⟨0, hm0⟩
          then A ⟨0, hm0⟩ ⟨0, hm0⟩ else 0 := by
        intro k j; simp only [e₀]
        by_cases hk : k = ⟨0, hm0⟩ <;>
          by_cases hj : j = ⟨0, hm0⟩ <;> simp [hk, hj]
      simp_rw [h1]
      have hLHS : ∑ i : Fin m, ∑ j : Fin m,
          (if i = ⟨0, hm0⟩ ∧ j = ⟨0, hm0⟩
           then A ⟨0, hm0⟩ ⟨0, hm0⟩ else 0) =
          A ⟨0, hm0⟩ ⟨0, hm0⟩ := by
        have hsplit : ∀ i : Fin m, ∑ j : Fin m,
            (if i = ⟨0, hm0⟩ ∧ j = ⟨0, hm0⟩
             then A ⟨0, hm0⟩ ⟨0, hm0⟩ else 0) =
            if i = ⟨0, hm0⟩
            then A ⟨0, hm0⟩ ⟨0, hm0⟩ else 0 := by
          intro i
          by_cases hi : i = ⟨0, hm0⟩
          · subst hi; simp [Finset.sum_ite_eq']
          · simp [hi]
        simp_rw [hsplit, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
      rw [hLHS]
      have hRHS : ∑ i : Fin m,
          (if (i : ℕ) ≤ 0 then A i i else 0) =
          A ⟨0, hm0⟩ ⟨0, hm0⟩ := by
        have : ∀ i : Fin m,
            (if (i : ℕ) ≤ 0 then A i i else 0) =
            if i = ⟨0, hm0⟩
            then A ⟨0, hm0⟩ ⟨0, hm0⟩ else 0 := by
          intro i
          by_cases hi : i = ⟨0, hm0⟩
          · subst hi; simp
          · have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
            simp [show ¬(i : ℕ) ≤ 0 from by omega, hi]
        simp_rw [this, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
      rw [hRHS]
    · -- Norm
      simp only [e₀]
      have : ∀ k : Fin m,
          Complex.normSq
            (if k = ⟨0, hm0⟩ then (1 : ℂ) else 0) =
          if k = ⟨0, hm0⟩ then 1 else 0 := by
        intro k
        by_cases hk : k = ⟨0, hm0⟩ <;>
          simp [hk, Complex.normSq_one,
            Complex.normSq_zero]
      simp_rw [this, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    · -- Support
      intro i hi
      simp only [e₀]
      have : i ≠ ⟨0, hm0⟩ :=
        fun h => by subst h; simp at hi
      simp [this]
  | succ p ih =>
    intro hp
    obtain ⟨v₁, hR₁, hN₁, hS₁⟩ := ih (by omega)
    have hv₁_zero : v₁ ⟨p + 1, hp⟩ = 0 :=
      hS₁ ⟨p + 1, hp⟩ (by simp)
    have ht0 :
        (0 : ℝ) ≤ (↑(p + 1) : ℝ) / (↑(p + 2) : ℝ) :=
      by positivity
    have ht1 :
        (↑(p + 1) : ℝ) / (↑(p + 2) : ℝ) ≤ 1 := by
      rw [div_le_one
        (by positivity : (0 : ℝ) < ↑(p + 2))]
      exact_mod_cast Nat.le_succ (p + 1)
    set t := (↑(p + 1) : ℝ) / (↑(p + 2) : ℝ)
    obtain ⟨v, hR, hN, hSupp⟩ :=
      ortho_compress A v₁ ⟨p + 1, hp⟩
        hN₁ hv₁_zero t ht0 ht1
    refine ⟨v, ?_, hN, ?_⟩
    · -- Rayleigh quotient
      rw [hR, hR₁]
      set Sp := ∑ i : Fin m,
        if (i : ℕ) ≤ p then A i i else 0
      have hSdecomp :
          (∑ i : Fin m,
            if (i : ℕ) ≤ p + 1 then A i i else 0) =
          Sp + A ⟨p + 1, hp⟩ ⟨p + 1, hp⟩ := by
        simp only [Sp]
        have hsplit : ∀ i : Fin m,
            (if (i : ℕ) ≤ p + 1 then A i i else 0) =
            (if (i : ℕ) ≤ p then A i i else 0) +
            (if i = ⟨p + 1, hp⟩
             then A i i else 0) := by
          intro i
          by_cases h1 : (i : ℕ) ≤ p
          · simp [h1,
              show (i : ℕ) ≤ p + 1 from by omega,
              show i ≠ ⟨p + 1, hp⟩ from by
                intro h
                have := congr_arg Fin.val h
                simp at this; omega]
          · by_cases h2 : i = ⟨p + 1, hp⟩
            · subst h2; simp [h1]
            · have : ¬(i : ℕ) ≤ p + 1 := by
                intro hle
                exact h2 (Fin.ext
                  (show i.val = p + 1 from by omega))
              simp [h1, h2, this]
        simp_rw [hsplit, Finset.sum_add_distrib]
        congr 1
        simp [Finset.sum_ite_eq']
      rw [hSdecomp]
      have hp1c : (↑(p + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero p
      have hp2c : (↑(p + 2 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero (p + 1)
      have h1 : (1 : ℝ) - t = 1 / ↑(p + 2) := by
        simp only [t]; field_simp; push_cast; ring
      rw [h1]
      simp only [Complex.ofReal_div,
        Complex.ofReal_natCast, Complex.ofReal_one, t]
      field_simp
    · -- Support
      intro i hi
      apply hSupp i
      constructor
      · exact hS₁ i (by omega)
      · intro h; subst h; simp at hi

private lemma claim2_bt_to_strengthened_constants {ε : ℝ}
    (hε : 0 < ε) (hε_half : ε ≤ 1 / 2) :
    ∃ δ ε' : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ε' ∧ ε' < 1 ∧
      (2 / (1 - δ)) * (6 * ε') ≤ 1 + ε ∧
      (2 / (1 - δ)) + 6 / δ ≤ 6 / ε ^ 2 + 1 := by
  refine ⟨ε / (1 + ε), ε / 12, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · rw [div_lt_one (by linarith : (0 : ℝ) < 1 + ε)]; linarith
  · positivity
  · linarith
  · have h1pe : (0 : ℝ) < 1 + ε := by linarith
    rw [← sub_nonneg]
    have hgoal :
        1 + ε - 2 / (1 - ε / (1 + ε)) * (6 * (ε / 12)) =
          ((1 + ε) - (1 + ε) * ε) := by field_simp; ring
    rw [hgoal]
    nlinarith [hε_half, hε.le]
  · have h1pe : (0 : ℝ) < 1 + ε := by linarith
    have hε_pos : (0 : ℝ) < ε := hε
    have hε2_pos : (0 : ℝ) < ε ^ 2 := by positivity
    rw [← sub_nonneg]
    have hgoal :
        6 / ε ^ 2 + 1 - (2 / (1 - ε / (1 + ε)) + 6 / (ε / (1 + ε))) =
          (6 + ε ^ 2 - 2 * (1 + ε) * ε ^ 2 - 6 * (1 + ε) * ε) / ε ^ 2 := by
      field_simp; ring
    rw [hgoal]
    apply div_nonneg _ (le_of_lt hε2_pos)
    nlinarith [sq_nonneg ε, sq_nonneg (1 - 2 * ε), sq_nonneg (1 - ε),
      hε_half, hε.le]

-- T-H: 0 ∈ NR for trace-zero matrix (Toeplitz-Hausdorff convexity).
-- NR is convex, diagonal entries ∈ NR, average of diag = 0 by trace = 0.
-- Key: 2×2 NR = affine image of B³ (convex); general via compressions.
private lemma zero_in_nr_of_trace_zero (m : ℕ) (hm : 2 ≤ m)
    (A : Matrix (Fin m) (Fin m) ℂ)
    (hTrace : A.trace = 0) :
    ∃ v : Fin m → ℂ,
      (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j = 0) ∧
      (∑ i, Complex.normSq (v i) = 1) := by
  -- Easy case: if some diagonal entry is zero, use the standard basis vector
  by_cases hdiag_zero : ∃ i, A i i = 0
  · obtain ⟨i, hi⟩ := hdiag_zero
    refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
    · have h1 : ∀ k j, starRingEnd ℂ ((fun l => if l = i then (1:ℂ) else 0) k) *
          A k j * ((fun l => if l = i then (1:ℂ) else 0) j) =
          if k = i then (if j = i then A i i else 0) else 0 := by
        intro k j; by_cases hk : k = i <;> by_cases hj : j = i <;> simp [hk, hj]
      simp_rw [h1]; simp [hi]
    · have h2 : ∀ k, Complex.normSq ((fun l => if l = i then (1:ℂ) else 0) k) =
          if k = i then 1 else 0 := by
        intro k; by_cases hk : k = i <;> simp [hk, Complex.normSq_one]
      simp_rw [h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · push Not at hdiag_zero
    -- All diagonal entries nonzero. Case split on det.
    by_cases hdet : A.det = 0
    · exact zero_mem_nr_of_det_zero A hdet
    · -- All diag ≠ 0, det ≠ 0, trace = 0.
      -- Write m = n + 2
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
      cases n with
      | zero =>
        -- m = 2: use zero_mem_nr_2x2
        exact zero_mem_nr_2x2 A hTrace hdiag_zero hdet
      | succ n =>
        -- m = n + 3 ≥ 3: replicate zero_mem_nr_toeplitz_hausdorff inline
        -- (can't call it since it's defined later and calls us for Im ≠ 0)
        obtain ⟨j, hj, _hproj⟩ := exists_neg_proj (n + 1) A hTrace hdiag_zero
        -- Case: 2×2 det at {0,j} = 0 → kernel vector
        by_cases hdet2 : A 0 0 * A j j = A 0 j * A j 0
        · set u : Fin (n + 1 + 2) → ℂ := fun k =>
            if k = (0 : Fin (n+1+2)) then -A 0 j else if k = j then A 0 0 else 0
          have hu_ne : u ≠ 0 := by
            intro h
            have h1 := congr_fun h j
            change (if j = (0 : Fin (n+1+2)) then -A 0 j else if j = j then A 0 0 else 0) = 0 at h1
            rw [if_neg hj, if_pos rfl] at h1
            exact hdiag_zero 0 h1
          apply rayleigh_zero_normalize A u hu_ne
          have hu0 : u 0 = -A 0 j := if_pos rfl
          have huj : u j = A 0 0 := by
            change (if j = 0 then _ else if j = j then _ else _) = _
            rw [if_neg hj, if_pos rfl]
          have huk : ∀ k, k ≠ 0 → k ≠ j → u k = 0 := by
            intro k hk0 hkj
            change (if k = 0 then _ else if k = j then _ else _) = _
            rw [if_neg hk0, if_neg hkj]
          have hinner : ∀ i, ∑ k, A i k * u k = A i 0 * u 0 + A i j * u j := by
            intro i
            apply finset_sum_support_pair 0 j hj.symm
            intro k hk0 hkj; rw [huk k hk0 hkj, mul_zero]
          have hrow0 : ∑ k, A 0 k * u k = 0 := by
            rw [hinner 0, hu0, huj]; ring
          have hrowj : ∑ k, A j k * u k = 0 := by
            rw [hinner j, hu0, huj]; linear_combination hdet2
          simp_rw [show ∀ i j', starRingEnd ℂ (u i) * A i j' * u j' =
            starRingEnd ℂ (u i) * (A i j' * u j') from fun i j' => by ring]
          simp_rw [← Finset.mul_sum]
          have houter : ∀ i, i ≠ 0 → i ≠ j →
              starRingEnd ℂ (u i) * ∑ k, A i k * u k = 0 := by
            intro i hi0 hij'; rw [show u i = 0 from huk i hi0 hij', map_zero, zero_mul]
          rw [finset_sum_support_pair 0 j hj.symm _ houter]
          rw [hrow0, hrowj, mul_zero, mul_zero, add_zero]
        · -- 2×2 det at {0,j} ≠ 0. Find third index k (exists since m ≥ 3).
          have hk_exists : ∃ k : Fin (n + 1 + 2), k ≠ 0 ∧ k ≠ j := by
            by_contra h
            push Not at h
            have huniv : Finset.univ ⊆ ({0, j} : Finset (Fin (n + 1 + 2))) := by
              intro x _
              simp only [Finset.mem_insert, Finset.mem_singleton]
              by_cases hx : x = 0
              · left; exact hx
              · right; exact h x hx
            have h1 := Finset.card_le_card huniv
            have h2 : ({0, j} : Finset (Fin (n + 1 + 2))).card ≤ 2 := Finset.card_le_two
            have h3 : Finset.card (Finset.univ : Finset (Fin (n + 1 + 2))) = n + 1 + 2 := by
              simp [Fintype.card_fin]
            linarith
          obtain ⟨k, hk0, hkj⟩ := hk_exists
          -- Case: 2×2 det at {0,k} = 0 → kernel vector
          by_cases hdet3 : A 0 0 * A k k = A 0 k * A k 0
          · set u : Fin (n + 1 + 2) → ℂ := fun i =>
              if i = (0 : Fin (n+1+2)) then -A 0 k else if i = k then A 0 0 else 0
            have hu_ne : u ≠ 0 := by
              intro h
              have h1 := congr_fun h k
              change (if k = (0 : Fin (n+1+2)) then -A 0 k else if k = k then A 0 0 else 0) = 0
                at h1
              rw [if_neg hk0, if_pos rfl] at h1
              exact hdiag_zero 0 h1
            apply rayleigh_zero_normalize A u hu_ne
            have hu0 : u 0 = -A 0 k := if_pos rfl
            have huk' : u k = A 0 0 := by
              change (if k = 0 then _ else if k = k then _ else _) = _
              rw [if_neg hk0, if_pos rfl]
            have hum : ∀ m, m ≠ 0 → m ≠ k → u m = 0 := by
              intro m hm0 hmk
              change (if m = 0 then _ else if m = k then _ else _) = _
              rw [if_neg hm0, if_neg hmk]
            have hinner : ∀ i, ∑ m, A i m * u m = A i 0 * u 0 + A i k * u k := by
              intro i
              apply finset_sum_support_pair 0 k hk0.symm
              intro m hm0 hmk; rw [hum m hm0 hmk, mul_zero]
            have hrow0 : ∑ m, A 0 m * u m = 0 := by
              rw [hinner 0, hu0, huk']; ring
            have hrowk : ∑ m, A k m * u m = 0 := by
              rw [hinner k, hu0, huk']; linear_combination hdet3
            simp_rw [show ∀ i m, starRingEnd ℂ (u i) * A i m * u m =
              starRingEnd ℂ (u i) * (A i m * u m) from fun i m => by ring]
            simp_rw [← Finset.mul_sum]
            have houter : ∀ i, i ≠ 0 → i ≠ k →
                starRingEnd ℂ (u i) * ∑ m, A i m * u m = 0 := by
              intro i hi0 hik; rw [show u i = 0 from hum i hi0 hik, map_zero, zero_mul]
            rw [finset_sum_support_pair 0 k hk0.symm _ houter]
            rw [hrow0, hrowk, mul_zero, mul_zero, add_zero]
          · -- Case: 2×2 det at {j,k} = 0 → kernel vector
            by_cases hdet4 : A j j * A k k = A j k * A k j
            · set u : Fin (n + 1 + 2) → ℂ := fun i =>
                if i = j then -A j k else if i = k then A j j else 0
              have hu_ne : u ≠ 0 := by
                intro h
                have h1 := congr_fun h k
                change (if k = j then -A j k else if k = k then A j j else 0) = 0 at h1
                rw [if_neg hkj, if_pos rfl] at h1
                exact hdiag_zero j h1
              apply rayleigh_zero_normalize A u hu_ne
              have huj : u j = -A j k := if_pos rfl
              have huk' : u k = A j j := by
                change (if k = j then _ else if k = k then _ else _) = _
                rw [if_neg hkj, if_pos rfl]
              have hum : ∀ m, m ≠ j → m ≠ k → u m = 0 := by
                intro m hmj hmk
                change (if m = j then _ else if m = k then _ else _) = _
                rw [if_neg hmj, if_neg hmk]
              have hinner : ∀ i, ∑ m, A i m * u m = A i j * u j + A i k * u k := by
                intro i
                apply finset_sum_support_pair j k hkj.symm
                intro m hmj hmk; rw [hum m hmj hmk, mul_zero]
              have hrowj : ∑ m, A j m * u m = 0 := by
                rw [hinner j, huj, huk']; ring
              have hrowk : ∑ m, A k m * u m = 0 := by
                rw [hinner k, huj, huk']; linear_combination hdet4
              simp_rw [show ∀ i m, starRingEnd ℂ (u i) * A i m * u m =
                starRingEnd ℂ (u i) * (A i m * u m) from fun i m => by ring]
              simp_rw [← Finset.mul_sum]
              have houter : ∀ i, i ≠ j → i ≠ k →
                  starRingEnd ℂ (u i) * ∑ m, A i m * u m = 0 := by
                intro i hij hik; rw [show u i = 0 from hum i hij hik, map_zero, zero_mul]
              rw [finset_sum_support_pair j k hkj.symm _ houter]
              rw [hrowj, hrowk, mul_zero, mul_zero, add_zero]
            · -- All three 2×2 dets nonzero. Use quadratic/phase method.
              by_cases him : (A j j * starRingEnd ℂ (A 0 0)).im = 0
              · -- Im = 0: Aⱼⱼ·conj(A₀₀) is real (and < 0). Quadratic method.
                set w₁ := A 0 j * starRingEnd ℂ (A 0 0)
                set w₂ := A j 0 * starRingEnd ℂ (A 0 0)
                set Pv := w₁.im + w₂.im
                set Qv := w₁.re - w₂.re
                set z₀ : ℂ := if Pv = 0 ∧ Qv = 0 then 1 else ⟨Qv, -Pv⟩
                have hnz_pos : (0 : ℝ) < Complex.normSq z₀ := by
                  simp only [z₀]
                  split_ifs with h
                  · exact Complex.normSq_pos.mpr one_ne_zero
                  · push Not at h
                    rw [Complex.normSq_apply]
                    by_cases hPv : Pv = 0
                    · have hQv : Qv ≠ 0 := h hPv
                      have hQv2 : 0 < Qv * Qv := mul_self_pos.mpr hQv
                      simp only [mul_neg, neg_mul, neg_neg, gt_iff_lt]
                      nlinarith [sq_nonneg Pv, hQv2]
                    · have : Pv ^ 2 > 0 := by positivity
                      nlinarith [sq_nonneg Qv]
                have him_cross : (z₀ * w₁ + starRingEnd ℂ z₀ * w₂).im = 0 := by
                  simp only [z₀]
                  split_ifs with h
                  · obtain ⟨hPv0, hQv0⟩ := h
                    change w₁.im + w₂.im = 0 at hPv0
                    change w₁.re - w₂.re = 0 at hQv0
                    have hw1 : w₁ = ⟨w₁.re, w₁.im⟩ := (Complex.eta w₁).symm
                    have hw2 : w₂ = ⟨w₂.re, w₂.im⟩ := (Complex.eta w₂).symm
                    rw [hw1, hw2]
                    change (1 * ⟨w₁.re, w₁.im⟩ + starRingEnd ℂ 1 * ⟨w₂.re, w₂.im⟩).im = 0
                    simp only [one_mul, map_one]
                    change w₁.im + w₂.im = 0
                    exact hPv0
                  · have hw1 : w₁ = ⟨w₁.re, w₁.im⟩ := (Complex.eta w₁).symm
                    have hw2 : w₂ = ⟨w₂.re, w₂.im⟩ := (Complex.eta w₂).symm
                    rw [hw1, hw2]
                    have hstar : star (⟨Qv, -Pv⟩ : ℂ) =
                      (⟨Qv, Pv⟩ : ℂ) := by apply Complex.ext <;> simp
                    change (⟨Qv, -Pv⟩ * ⟨w₁.re, w₁.im⟩ +
                         star (⟨Qv, -Pv⟩ : ℂ) * ⟨w₂.re, w₂.im⟩).im = 0
                    rw [hstar]
                    change Qv * w₁.im + (-Pv) * w₁.re +
                           (Qv * w₂.im + Pv * w₂.re) = 0
                    change (w₁.re - w₂.re) * w₁.im + -(w₁.im + w₂.im) * w₁.re +
                           ((w₁.re - w₂.re) * w₂.im + (w₁.im + w₂.im) * w₂.re) = 0
                    ring
                set nz := Complex.normSq z₀
                set acoeff := nz * (A j j * starRingEnd ℂ (A 0 0)).re
                set bcoeff := (z₀ * w₁ + starRingEnd ℂ z₀ * w₂).re
                set ccoeff := Complex.normSq (A 0 0)
                have ha_neg : acoeff < 0 := by
                  simp only [acoeff]; exact mul_neg_of_pos_of_neg hnz_pos _hproj
                have hc_pos : (0 : ℝ) < ccoeff := Complex.normSq_pos.mpr (hdiag_zero 0)
                obtain ⟨t₀, _, hroot⟩ :=
                  quadratic_has_nonneg_root (b := bcoeff) ha_neg hc_pos
                set w : ℂ := ↑t₀ * z₀
                set u : Fin (n + 1 + 2) → ℂ := fun i =>
                  if i = (0 : Fin (n + 1 + 2)) then 1 else if i = j then w else 0
                have hu_ne : u ≠ 0 := by
                  intro h; have h0 := congr_fun h 0
                  simp only [u, ite_true, Pi.zero_apply] at h0
                  exact one_ne_zero h0
                apply rayleigh_zero_normalize A u hu_ne
                have hu0 : u 0 = 1 := if_pos rfl
                have huj : u j = w := by
                  change (if j = (0 : Fin (n+1+2)) then 1 else if j = j then w else 0) = w
                  rw [if_neg hj, if_pos rfl]
                have hum : ∀ m, m ≠ 0 → m ≠ j → u m = 0 := by
                  intro m hm0 hmj
                  change (if m = (0 : Fin (n+1+2)) then 1 else if m = j then w else 0) = 0
                  rw [if_neg hm0, if_neg hmj]
                have hinner : ∀ i, ∑ m, A i m * u m = A i 0 + A i j * w := by
                  intro i
                  have hsup := finset_sum_support_pair (0 : Fin (n+1+2)) j hj.symm
                    (fun m => A i m * u m)
                    (fun m hm0 hmj => by simp only [hum m hm0 hmj, mul_zero])
                  rw [hsup]; simp only [hu0, mul_one, huj]
                simp_rw [show ∀ i m, starRingEnd ℂ (u i) * A i m * u m =
                  starRingEnd ℂ (u i) * (A i m * u m) from fun i m => by ring]
                simp_rw [← Finset.mul_sum]
                have houter : ∀ i, i ≠ 0 → i ≠ j →
                    starRingEnd ℂ (u i) * ∑ m, A i m * u m = 0 := by
                  intro i hi0 hij'
                  rw [show u i = 0 from hum i hi0 hij', map_zero, zero_mul]
                rw [finset_sum_support_pair (0 : Fin (n+1+2)) j hj.symm _ houter]
                rw [hu0, map_one, one_mul, huj, hinner 0, hinner j]
                suffices h : (A 0 0 + A 0 j * w + starRingEnd ℂ w * (A j 0 + A j j * w)) *
                    starRingEnd ℂ (A 0 0) = 0 by
                  rcases mul_eq_zero.mp h with hr | hc
                  · exact hr
                  · exfalso; exact hdiag_zero 0 (by rwa [starRingEnd_apply, star_eq_zero] at hc)
                have hw_eq : w = (↑t₀ : ℂ) * z₀ := rfl
                have hcw : starRingEnd ℂ w = (↑t₀ : ℂ) * starRingEnd ℂ z₀ := by
                  rw [hw_eq, map_mul, Complex.conj_ofReal]
                have hcww : starRingEnd ℂ w * w = ↑(t₀ ^ 2 * Complex.normSq z₀) := by
                  rw [hcw, hw_eq]
                  rw [show (↑t₀ : ℂ) * starRingEnd ℂ z₀ * ((↑t₀ : ℂ) * z₀) =
                    (↑t₀ : ℂ) * (↑t₀ : ℂ) * (z₀ * starRingEnd ℂ z₀) from by ring]
                  rw [Complex.mul_conj]
                  push_cast; ring
                have step1 : A 0 0 + A 0 j * w +
                    starRingEnd ℂ w * (A j 0 + A j j * w) =
                    A 0 0 + (↑t₀ : ℂ) * (z₀ * A 0 j + starRingEnd ℂ z₀ * A j 0) +
                    ↑(t₀ ^ 2 * Complex.normSq z₀) * A j j := by
                  rw [hw_eq, hcw]; rw [← hcww, hcw, hw_eq]; ring
                have step2 : (A 0 0 + (↑t₀ : ℂ) *
                    (z₀ * A 0 j + starRingEnd ℂ z₀ * A j 0) +
                    ↑(t₀ ^ 2 * Complex.normSq z₀) * A j j) *
                    starRingEnd ℂ (A 0 0) =
                    A 0 0 * starRingEnd ℂ (A 0 0) +
                    (↑t₀ : ℂ) * (z₀ * w₁ + starRingEnd ℂ z₀ * w₂) +
                    ↑(t₀ ^ 2 * Complex.normSq z₀) *
                    (A j j * starRingEnd ℂ (A 0 0)) := by ring
                have hre_add3 : ∀ (a b c : ℂ),
                    (a + b + c).re = a.re + b.re + c.re := by
                  intro a b c; simp [Complex.add_re]
                have him_add3 : ∀ (a b c : ℂ),
                    (a + b + c).im = a.im + b.im + c.im := by
                  intro a b c; simp [Complex.add_im]
                have hre_real_mul : ∀ (r : ℝ) (z : ℂ),
                    ((↑r : ℂ) * z).re = r * z.re := by
                  intro r z; rw [Complex.mul_re, Complex.ofReal_re,
                    Complex.ofReal_im]; ring
                have him_real_mul : ∀ (r : ℝ) (z : ℂ),
                    ((↑r : ℂ) * z).im = r * z.im := by
                  intro r z; rw [Complex.mul_im, Complex.ofReal_re,
                    Complex.ofReal_im]; ring
                apply Complex.ext
                · simp only [Complex.zero_re]
                  rw [step1, step2, Complex.mul_conj, hre_add3,
                    Complex.ofReal_re, hre_real_mul, hre_real_mul]
                  linarith [hroot]
                · simp only [Complex.zero_im]
                  rw [step1, step2, Complex.mul_conj, him_add3,
                    Complex.ofReal_im, him_real_mul, him_real_mul,
                    him_cross, him, mul_zero, mul_zero, add_zero, add_zero]
              · -- Im(Aⱼⱼ·conj(A₀₀)) ≠ 0: use segment_diag_in_nr twice.
                -- Step 1: Find t₁ s.t. z := t₁·A₀₀ + (1-t₁)·Aⱼⱼ lies on
                -- the line from Aₖₖ through 0 (convex hull argument).
                -- Step 2: Get unit v₁ supported on {0,j} with R(v₁)=z.
                -- Step 3: v₁ ⊥ eₖ, so apply segment_diag_in_nr_2x2 to
                -- the 2×2 compression {v₁, eₖ} to find unit v₂ with R(v₂)=0.
                -- Solved by iterative diagonal averaging.
                obtain ⟨v, hRv, hNv, _⟩ :=
                  iter_diag_avg A (n + 1 + 2 - 1) (by omega)
                refine ⟨v, ?_, hNv⟩
                rw [hRv]
                have hfull : ∑ i : Fin (n + 1 + 2),
                    (if (i : ℕ) ≤ n + 1 + 2 - 1 then A i i
                     else 0) =
                    ∑ i, A i i := by
                  congr 1; ext i
                  rw [if_pos (show (i : ℕ) ≤ n + 1 + 2 - 1
                    from by omega)]
                rw [hfull]
                have : ∑ i, A i i = A.trace := by
                  simp [Matrix.trace, Matrix.diag]
                rw [this, hTrace, mul_zero]

-- Toeplitz-Hausdorff consequence: for an invertible (n+3)x(n+3) trace-zero
-- matrix with all nonzero diagonal entries, 0 is in the numerical range.
-- Strategy: find j with opposite diagonal direction via exists_neg_proj,
-- then handle the 2x2 submatrix at (0,j). If its det is 0, construct a
-- kernel vector. If not, use zero_in_nr_of_trace_zero for the Im ≠ 0 case.
set_option maxHeartbeats 1600000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
private lemma zero_mem_nr_toeplitz_hausdorff (n : ℕ)
    (A : Matrix (Fin (n + 1 + 2)) (Fin (n + 1 + 2)) ℂ)
    (hTrace : A.trace = 0)
    (hDiag : ∀ i, A i i ≠ 0)
    (hdet : ¬A.det = 0) :
    ∃ v : Fin (n + 1 + 2) → ℂ,
      (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j = 0) ∧
      (∑ i, Complex.normSq (v i) = 1) := by
  -- Step 1: find j ≠ 0 with "opposite" diagonal direction
  obtain ⟨j, hj, _hproj⟩ := exists_neg_proj (n + 1) A hTrace hDiag
  -- Step 2: case split on the 2×2 submatrix determinant
  by_cases hdet2 : A 0 0 * A j j = A 0 j * A j 0
  · -- Case: 2×2 submatrix has det = 0.
    -- Construct u with u 0 = -A 0 j, u j = A 0 0, u k = 0 otherwise.
    -- Then u†Au = 0 because the relevant 2×2 block annihilates u.
    set u : Fin (n + 1 + 2) → ℂ := fun k =>
      if k = (0 : Fin (n+1+2)) then -A 0 j else if k = j then A 0 0 else 0
    have hu_ne : u ≠ 0 := by
      intro h
      have h1 := congr_fun h j
      change (if j = (0 : Fin (n+1+2)) then -A 0 j else if j = j then A 0 0 else 0) = 0 at h1
      rw [if_neg hj, if_pos rfl] at h1
      exact hDiag 0 h1
    apply rayleigh_zero_normalize A u hu_ne
    -- Prove: ∑ i, ∑ j', conj(u i) * A i j' * u j' = 0
    have hu0 : u 0 = -A 0 j := if_pos rfl
    have huj : u j = A 0 0 := by
      change (if j = 0 then _ else if j = j then _ else _) = _
      rw [if_neg hj, if_pos rfl]
    have huk : ∀ k, k ≠ 0 → k ≠ j → u k = 0 := by
      intro k hk0 hkj
      change (if k = 0 then _ else if k = j then _ else _) = _
      rw [if_neg hk0, if_neg hkj]
    -- Inner sum: for each row i, ∑ k A i k * u k = A i 0 * u 0 + A i j * u j
    have hinner : ∀ i, ∑ k, A i k * u k = A i 0 * u 0 + A i j * u j := by
      intro i
      apply finset_sum_support_pair 0 j hj.symm
      intro k hk0 hkj; rw [huk k hk0 hkj, mul_zero]
    -- Row 0: A 0 0 * (-A 0 j) + A 0 j * A 0 0 = 0
    have hrow0 : ∑ k, A 0 k * u k = 0 := by
      rw [hinner 0, hu0, huj]; ring
    -- Row j: uses det condition A 0 0 * A j j = A 0 j * A j 0
    have hrowj : ∑ k, A j k * u k = 0 := by
      rw [hinner j, hu0, huj]; linear_combination hdet2
    -- Assemble: rewrite as ∑ i conj(u i) * (∑ k A i k * u k), then collapse
    simp_rw [show ∀ i j', starRingEnd ℂ (u i) * A i j' * u j' =
      starRingEnd ℂ (u i) * (A i j' * u j') from fun i j' => by ring]
    simp_rw [← Finset.mul_sum]
    have houter : ∀ i, i ≠ 0 → i ≠ j →
        starRingEnd ℂ (u i) * ∑ k, A i k * u k = 0 := by
      intro i hi0 hij'; rw [show u i = 0 from huk i hi0 hij', map_zero, zero_mul]
    rw [finset_sum_support_pair 0 j hj.symm _ houter]
    rw [hrow0, hrowj, mul_zero, mul_zero, add_zero]
  · -- Case: 2×2 submatrix at {0,j} has nonzero det.
    -- Strategy: find a third index k and try other 2×2 submatrices.
    -- If any 2×2 det is 0, use kernel vector. Otherwise, use the
    -- trace-zero + IVT approach with appropriate phase rotation.
    -- Step 1: Find k ≠ 0, k ≠ j (exists since matrix size ≥ 3).
    have hk_exists : ∃ k : Fin (n + 1 + 2), k ≠ 0 ∧ k ≠ j := by
      by_contra h
      push Not at h
      have huniv : Finset.univ ⊆ ({0, j} : Finset (Fin (n + 1 + 2))) := by
        intro x _
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hx : x = 0
        · left; exact hx
        · right; exact h x hx
      have h1 := Finset.card_le_card huniv
      have h2 : ({0, j} : Finset (Fin (n + 1 + 2))).card ≤ 2 := Finset.card_le_two
      have h3 : Finset.card (Finset.univ : Finset (Fin (n + 1 + 2))) = n + 1 + 2 := by
        simp [Fintype.card_fin]
      linarith
    obtain ⟨k, hk0, hkj⟩ := hk_exists
    -- Step 2: Case split on the 2×2 det at {0, k}.
    by_cases hdet3 : A 0 0 * A k k = A 0 k * A k 0
    · -- det at {0,k} = 0: kernel vector at {0,k}
      set u : Fin (n + 1 + 2) → ℂ := fun i =>
        if i = (0 : Fin (n+1+2)) then -A 0 k else if i = k then A 0 0 else 0
      have hu_ne : u ≠ 0 := by
        intro h
        have h1 := congr_fun h k
        change (if k = (0 : Fin (n+1+2)) then -A 0 k else if k = k then A 0 0 else 0) = 0 at h1
        rw [if_neg hk0, if_pos rfl] at h1
        exact hDiag 0 h1
      apply rayleigh_zero_normalize A u hu_ne
      have hu0 : u 0 = -A 0 k := if_pos rfl
      have huk : u k = A 0 0 := by
        change (if k = 0 then _ else if k = k then _ else _) = _
        rw [if_neg hk0, if_pos rfl]
      have hum : ∀ m, m ≠ 0 → m ≠ k → u m = 0 := by
        intro m hm0 hmk
        change (if m = 0 then _ else if m = k then _ else _) = _
        rw [if_neg hm0, if_neg hmk]
      have hinner : ∀ i, ∑ m, A i m * u m = A i 0 * u 0 + A i k * u k := by
        intro i
        apply finset_sum_support_pair 0 k hk0.symm
        intro m hm0 hmk; rw [hum m hm0 hmk, mul_zero]
      have hrow0 : ∑ m, A 0 m * u m = 0 := by
        rw [hinner 0, hu0, huk]; ring
      have hrowk : ∑ m, A k m * u m = 0 := by
        rw [hinner k, hu0, huk]; linear_combination hdet3
      simp_rw [show ∀ i m, starRingEnd ℂ (u i) * A i m * u m =
        starRingEnd ℂ (u i) * (A i m * u m) from fun i m => by ring]
      simp_rw [← Finset.mul_sum]
      have houter : ∀ i, i ≠ 0 → i ≠ k →
          starRingEnd ℂ (u i) * ∑ m, A i m * u m = 0 := by
        intro i hi0 hik; rw [show u i = 0 from hum i hi0 hik, map_zero, zero_mul]
      rw [finset_sum_support_pair 0 k hk0.symm _ houter]
      rw [hrow0, hrowk, mul_zero, mul_zero, add_zero]
    · -- det at {0,k} ≠ 0. Try det at {j,k}.
      by_cases hdet4 : A j j * A k k = A j k * A k j
      · -- det at {j,k} = 0: kernel vector at {j,k}
        set u : Fin (n + 1 + 2) → ℂ := fun i =>
          if i = j then -A j k else if i = k then A j j else 0
        have hu_ne : u ≠ 0 := by
          intro h
          have h1 := congr_fun h k
          change (if k = j then -A j k else if k = k then A j j else 0) = 0 at h1
          split_ifs at h1 with h2 h3
          · exact absurd h2 hkj
          · exact hDiag j h1
          · exact absurd rfl h3
        apply rayleigh_zero_normalize A u hu_ne
        have huj : u j = -A j k := if_pos rfl
        have huk : u k = A j j := by
          change (if k = j then _ else if k = k then _ else _) = _
          split_ifs with h1 h2
          · exact absurd h1 hkj
          · rfl
          · exact absurd rfl h2
        have hum : ∀ m, m ≠ j → m ≠ k → u m = 0 := by
          intro m hmj hmk
          change (if m = j then _ else if m = k then _ else _) = _
          rw [if_neg hmj, if_neg hmk]
        have hinner : ∀ i, ∑ m, A i m * u m = A i j * u j + A i k * u k := by
          intro i
          apply finset_sum_support_pair j k hkj.symm
          intro m hmj hmk; rw [hum m hmj hmk, mul_zero]
        have hrowj : ∑ m, A j m * u m = 0 := by
          rw [hinner j, huj, huk]; ring
        have hrowk : ∑ m, A k m * u m = 0 := by
          rw [hinner k, huj, huk]; linear_combination hdet4
        simp_rw [show ∀ i m, starRingEnd ℂ (u i) * A i m * u m =
          starRingEnd ℂ (u i) * (A i m * u m) from fun i m => by ring]
        simp_rw [← Finset.mul_sum]
        have houter : ∀ i, i ≠ j → i ≠ k →
            starRingEnd ℂ (u i) * ∑ m, A i m * u m = 0 := by
          intro i hij hik; rw [show u i = 0 from hum i hij hik, map_zero, zero_mul]
        rw [finset_sum_support_pair j k hkj.symm _ houter]
        rw [hrowj, hrowk, mul_zero, mul_zero, add_zero]
      · -- All three 2×2 dets nonzero. Use IVT/quadratic approach.
        -- Strategy: construct v = e₀ + w·eⱼ with w = t·z₀, where z₀ is a
        -- phase chosen to make Im(Rayleigh · conj(A₀₀)) = 0, and t is a
        -- nonneg real root of a quadratic (exists by quadratic_has_nonneg_root).
        --
        -- Case split: if Im(Aⱼⱼ·conj(A₀₀)) = 0, the full argument works.
        -- If Im(Aⱼⱼ·conj(A₀₀)) ≠ 0, a more subtle 2D winding argument is
        -- needed; the corresponding case is handled below.
        by_cases him : (A j j * starRingEnd ℂ (A 0 0)).im = 0
        · -- Case: Aⱼⱼ·conj(A₀₀) is real (and negative by _hproj).
          -- Choose z₀ to kill Im of cross-term · conj(A₀₀).
          -- Let w₁ = A₀ⱼ·conj(A₀₀), w₂ = Aⱼ₀·conj(A₀₀).
          -- Set z₀ = ⟨w₁.re - w₂.re, -(w₁.im + w₂.im)⟩.
          -- Then Im(z₀·w₁ + conj(z₀)·w₂) = 0 by algebraic identity.
          -- If z₀ = 0 (i.e., w₁.re = w₂.re and w₁.im = -w₂.im), use z₀ = 1.
          set w₁ := A 0 j * starRingEnd ℂ (A 0 0)
          set w₂ := A j 0 * starRingEnd ℂ (A 0 0)
          set Pv := w₁.im + w₂.im
          set Qv := w₁.re - w₂.re
          set z₀ : ℂ := if Pv = 0 ∧ Qv = 0 then 1 else ⟨Qv, -Pv⟩
          -- normSq z₀ > 0
          have hnz_pos : (0 : ℝ) < Complex.normSq z₀ := by
            simp only [z₀]
            split_ifs with h
            · exact Complex.normSq_pos.mpr one_ne_zero
            · push Not at h
              rw [Complex.normSq_apply]
              by_cases hPv : Pv = 0
              · have hQv : Qv ≠ 0 := h hPv
                simp only [hPv, neg_zero, mul_zero, add_zero, mul_self_pos, ne_eq]; positivity
              · have : Pv ^ 2 > 0 := by positivity
                nlinarith [sq_nonneg Qv]
          -- Im of cross-term · conj(A₀₀) = 0 by choice of z₀
          have him_cross : (z₀ * w₁ + starRingEnd ℂ z₀ * w₂).im = 0 := by
            simp only [z₀]
            split_ifs with h
            · -- z₀ = 1: then w₁.im + w₂.im = 0 and w₁.re = w₂.re
              obtain ⟨hPv0, hQv0⟩ := h
              change w₁.im + w₂.im = 0 at hPv0
              change w₁.re - w₂.re = 0 at hQv0
              have hw1 : w₁ = ⟨w₁.re, w₁.im⟩ := (Complex.eta w₁).symm
              have hw2 : w₂ = ⟨w₂.re, w₂.im⟩ := (Complex.eta w₂).symm
              rw [hw1, hw2]
              change (1 * ⟨w₁.re, w₁.im⟩ + starRingEnd ℂ 1 * ⟨w₂.re, w₂.im⟩).im = 0
              simp only [one_mul, map_one]
              change w₁.im + w₂.im = 0
              exact hPv0
            · -- z₀ = ⟨Qv, -Pv⟩: algebraic identity
              have hw1 : w₁ = ⟨w₁.re, w₁.im⟩ := (Complex.eta w₁).symm
              have hw2 : w₂ = ⟨w₂.re, w₂.im⟩ := (Complex.eta w₂).symm
              rw [hw1, hw2]
              have hstar : star (⟨Qv, -Pv⟩ : ℂ) =
                (⟨Qv, Pv⟩ : ℂ) := by apply Complex.ext <;> simp
              change (⟨Qv, -Pv⟩ * ⟨w₁.re, w₁.im⟩ +
                   star (⟨Qv, -Pv⟩ : ℂ) * ⟨w₂.re, w₂.im⟩).im = 0
              rw [hstar]
              change Qv * w₁.im + (-Pv) * w₁.re +
                     (Qv * w₂.im + Pv * w₂.re) = 0
              change (w₁.re - w₂.re) * w₁.im + -(w₁.im + w₂.im) * w₁.re +
                     ((w₁.re - w₂.re) * w₂.im + (w₁.im + w₂.im) * w₂.re) = 0
              ring
          -- Get t₀ from quadratic root lemma
          set nz := Complex.normSq z₀
          set acoeff := nz * (A j j * starRingEnd ℂ (A 0 0)).re
          set bcoeff := (z₀ * w₁ + starRingEnd ℂ z₀ * w₂).re
          set ccoeff := Complex.normSq (A 0 0)
          have ha_neg : acoeff < 0 := by
            simp only [acoeff]; exact mul_neg_of_pos_of_neg hnz_pos _hproj
          have hc_pos : (0 : ℝ) < ccoeff := Complex.normSq_pos.mpr (hDiag 0)
          obtain ⟨t₀, _, hroot⟩ :=
            quadratic_has_nonneg_root (b := bcoeff) ha_neg hc_pos
          -- Construct the vector v
          set w : ℂ := ↑t₀ * z₀
          set u : Fin (n + 1 + 2) → ℂ := fun i =>
            if i = (0 : Fin (n + 1 + 2)) then 1 else if i = j then w else 0
          -- u ≠ 0 since u 0 = 1
          have hu_ne : u ≠ 0 := by
            intro h; have h0 := congr_fun h 0
            simp only [u, ite_true, Pi.zero_apply] at h0
            exact one_ne_zero h0
          apply rayleigh_zero_normalize A u hu_ne
          -- Reduce Rayleigh quotient to 4 terms
          have hu0 : u 0 = 1 := if_pos rfl
          have huj : u j = w := by
            change (if j = (0 : Fin (n+1+2)) then 1 else if j = j then w else 0) = w
            rw [if_neg hj, if_pos rfl]
          have hum : ∀ m, m ≠ 0 → m ≠ j → u m = 0 := by
            intro m hm0 hmj
            change (if m = (0 : Fin (n+1+2)) then 1 else if m = j then w else 0) = 0
            rw [if_neg hm0, if_neg hmj]
          -- Inner sums: ∑ m, A i m * u m = A i 0 + A i j * w
          have hinner : ∀ i, ∑ m, A i m * u m = A i 0 + A i j * w := by
            intro i
            have hsup := finset_sum_support_pair (0 : Fin (n+1+2)) j hj.symm
              (fun m => A i m * u m)
              (fun m hm0 hmj => by simp only [hum m hm0 hmj, mul_zero])
            rw [hsup]; simp only [hu0, mul_one, huj]
          -- Rayleigh = ∑ i, conj(u i) * (∑ m, A i m * u m)
          simp_rw [show ∀ i m, starRingEnd ℂ (u i) * A i m * u m =
            starRingEnd ℂ (u i) * (A i m * u m) from fun i m => by ring]
          simp_rw [← Finset.mul_sum]
          -- Outer sum: only i=0 and i=j contribute
          have houter : ∀ i, i ≠ 0 → i ≠ j →
              starRingEnd ℂ (u i) * ∑ m, A i m * u m = 0 := by
            intro i hi0 hij'
            rw [show u i = 0 from hum i hi0 hij', map_zero, zero_mul]
          rw [finset_sum_support_pair (0 : Fin (n+1+2)) j hj.symm _ houter]
          -- Now: conj(u 0) * row0_sum + conj(u j) * rowj_sum
          rw [hu0, map_one, one_mul, huj, hinner 0, hinner j]
          -- Goal: (A 0 0 + A 0 j * w) + conj(w) * (A j 0 + A j j * w) = 0
          -- = A 0 0 + w * A 0 j + conj(w) * A j 0 + conj(w) * w * A j j
          -- = A 0 0 + w * A 0 j + conj(w) * A j 0 + normSq(w) * A j j
          -- Multiply both sides by conj(A 0 0) and show = 0.
          -- The Re part = ccoeff + t₀ * bcoeff + t₀² * nz * Re(Aⱼⱼ·conj(A₀₀)) = 0
          -- The Im part = t₀ * Im(cross) + t₀² * nz * Im(Aⱼⱼ·conj(A₀₀)) = 0
          suffices h : (A 0 0 + A 0 j * w + starRingEnd ℂ w * (A j 0 + A j j * w)) *
              starRingEnd ℂ (A 0 0) = 0 by
            rcases mul_eq_zero.mp h with hr | hc
            · exact hr
            · exfalso; exact hDiag 0 (by rwa [starRingEnd_apply, star_eq_zero] at hc)
          -- Show the product is 0 by showing Re=0 and Im=0.
          -- Common setup: express everything in terms of t₀, z₀, w₁, w₂.
          have hw_eq : w = (↑t₀ : ℂ) * z₀ := rfl
          have hcw : starRingEnd ℂ w = (↑t₀ : ℂ) * starRingEnd ℂ z₀ := by
            rw [hw_eq, map_mul, Complex.conj_ofReal]
          have hcww : starRingEnd ℂ w * w = ↑(t₀ ^ 2 * Complex.normSq z₀) := by
            rw [hcw, hw_eq]
            rw [show (↑t₀ : ℂ) * starRingEnd ℂ z₀ * ((↑t₀ : ℂ) * z₀) =
              (↑t₀ : ℂ) * (↑t₀ : ℂ) * (z₀ * starRingEnd ℂ z₀) from by ring]
            rw [Complex.mul_conj]
            push_cast; ring
          have step1 : A 0 0 + A 0 j * w +
              starRingEnd ℂ w * (A j 0 + A j j * w) =
              A 0 0 + (↑t₀ : ℂ) * (z₀ * A 0 j + starRingEnd ℂ z₀ * A j 0) +
              ↑(t₀ ^ 2 * Complex.normSq z₀) * A j j := by
            rw [hw_eq, hcw]; rw [← hcww, hcw, hw_eq]; ring
          have step2 : (A 0 0 + (↑t₀ : ℂ) *
              (z₀ * A 0 j + starRingEnd ℂ z₀ * A j 0) +
              ↑(t₀ ^ 2 * Complex.normSq z₀) * A j j) *
              starRingEnd ℂ (A 0 0) =
              A 0 0 * starRingEnd ℂ (A 0 0) +
              (↑t₀ : ℂ) * (z₀ * w₁ + starRingEnd ℂ z₀ * w₂) +
              ↑(t₀ ^ 2 * Complex.normSq z₀) *
              (A j j * starRingEnd ℂ (A 0 0)) := by ring
          have hre_add3 : ∀ (a b c : ℂ),
              (a + b + c).re = a.re + b.re + c.re := by
            intro a b c; simp [Complex.add_re]
          have him_add3 : ∀ (a b c : ℂ),
              (a + b + c).im = a.im + b.im + c.im := by
            intro a b c; simp [Complex.add_im]
          have hre_real_mul : ∀ (r : ℝ) (z : ℂ),
              ((↑r : ℂ) * z).re = r * z.re := by
            intro r z; rw [Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im]; ring
          have him_real_mul : ∀ (r : ℝ) (z : ℂ),
              ((↑r : ℂ) * z).im = r * z.im := by
            intro r z; rw [Complex.mul_im, Complex.ofReal_re,
              Complex.ofReal_im]; ring
          apply Complex.ext
          · -- Re = 0: reduces to acoeff*t₀² + bcoeff*t₀ + ccoeff = 0
            simp only [Complex.zero_re]
            rw [step1, step2, Complex.mul_conj, hre_add3,
              Complex.ofReal_re, hre_real_mul, hre_real_mul]
            linarith [hroot]
          · -- Im = 0: reduces to t₀ * 0 + (t₀²*nz) * 0 = 0
            simp only [Complex.zero_im]
            rw [step1, step2, Complex.mul_conj, him_add3,
              Complex.ofReal_im, him_real_mul, him_real_mul,
              him_cross, him, mul_zero, mul_zero, add_zero, add_zero]
        · -- Case: Im(Aⱼⱼ·conj(A₀₀)) ≠ 0.
          -- Use T-H: 0 ∈ NR for any trace-zero matrix of size ≥ 2.
          exact zero_in_nr_of_trace_zero (n + 1 + 2) (by omega) A hTrace

/-- 0 is in the numerical range of a trace-zero matrix with all nonzero diagonal entries.

    **Proof strategy:**
    Case 1 (det A = 0): A has eigenvalue 0, so there exists v ≠ 0 with Av = 0.
    Then v†Av = 0, and normalizing v gives a unit vector with zero Rayleigh quotient.

    Case 2 (det A ≠ 0, 2×2): Rank-nullity argument on a real-linear map encoding
    the Rayleigh quotient, using trace = 0 to linearize.

    Case 3 (det A ≠ 0, ≥ 3×3): Toeplitz-Hausdorff theorem. See
    `zero_mem_nr_toeplitz_hausdorff`. -/
private lemma zero_mem_numerical_range (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hTrace : A.trace = 0)
    (hDiag : ∀ i, A i i ≠ 0) :
    ∃ v : Fin (n + 2) → ℂ,
      (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j = 0) ∧
      (∑ i, Complex.normSq (v i) = 1) := by
  by_cases hdet : A.det = 0
  · exact zero_mem_nr_of_det_zero A hdet
  · -- A is invertible. 0 ∈ W(A) by Toeplitz-Hausdorff + trace zero.
    cases n with
    | zero =>
      -- 2×2 trace-zero invertible case
      exact zero_mem_nr_2x2 A hTrace hDiag hdet
    | succ n =>
      exact zero_mem_nr_toeplitz_hausdorff n A hTrace hDiag hdet

set_option maxHeartbeats 800000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
/-- ONB extension: given a unit vector v in ℂⁿ, there exists a unitary matrix
    whose first column is v. Standard result via Gram-Schmidt or Householder. -/
private lemma onb_extension (n : ℕ)
    (v : Fin (n + 2) → ℂ)
    (hv : ∑ i, Complex.normSq (v i) = 1) :
    ∃ U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ,
      IsUnitaryMatrix U ∧
      (∀ i, U i 0 = v i) := by
  -- Lift v to EuclideanSpace and show it has norm 1
  set ve := (WithLp.equiv 2 (Fin (n + 2) → ℂ)).symm v
  have hnorm : ‖ve‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [show ∀ i, ve.ofLp i = v i from fun _ => rfl]
    simp_rw [← Complex.normSq_eq_norm_sq]; rw [hv, Real.sqrt_one]
  -- The singleton {ve} is orthonormal (unit vector)
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 2))) =
      Fintype.card (Fin (n + 2)) := by
    simp [finrank_euclideanSpace]
  set w : Fin (n + 2) → EuclideanSpace ℂ (Fin (n + 2)) := fun i =>
    if i = 0 then ve else 0
  have horth : Orthonormal ℂ
      (({(0 : Fin (n + 2))} : Set (Fin (n + 2))).restrict w) := by
    rw [orthonormal_iff_ite]
    intro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp only [Set.restrict_apply, ite_true, w]
    rw [inner_self_eq_norm_sq_to_K, hnorm]; simp
  -- Extend to a full ONB b with b 0 = ve
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard horth
  have hb0 : b 0 = ve := by
    have := hb 0 (Set.mem_singleton 0)
    simp only [↓reduceIte, w] at this; exact this
  -- Form the change-of-basis matrix (unitary) and verify first column
  let e := EuclideanSpace.basisFun (Fin (n + 2)) ℂ
  let M := e.toBasis.toMatrix (fun i => b i)
  have hMu : M ∈ Matrix.unitaryGroup (Fin (n + 2)) ℂ :=
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary e b
  refine ⟨M, ?_, ?_⟩
  · rw [Matrix.unitaryGroup, Unitary.mem_iff] at hMu
    simp only [Matrix.star_eq_conjTranspose] at hMu
    exact ⟨hMu.2, hMu.1⟩
  · intro i
    simp only [M, Module.Basis.toMatrix_apply]
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, hb0]; rfl

/-- The Rayleigh quotient v†Av equals (U†AU)₀₀ when U has first column v. -/
private lemma rayleigh_eq_conj_entry (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (v : Fin (n + 2) → ℂ)
    (hcol : ∀ i, U i 0 = v i) :
    (U.conjTranspose * A * U) 0 0 =
    ∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_mul, hcol, starRingEnd_apply]
  rw [Finset.sum_comm]

-- Toeplitz-Hausdorff: 0 ∈ W(A) when all diagonal entries are nonzero and tr A = 0.
-- Combines zero_mem_numerical_range (∃ unit v with v†Av = 0),
-- onb_extension (extend v to unitary U), and rayleigh_eq_conj_entry.
private lemma numerical_range_zero_of_trace_zero (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hTrace : A.trace = 0)
    (hDiag : ∀ i, A i i ≠ 0) :
    ∃ (U₁ : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      IsUnitaryMatrix U₁ ∧
      (U₁.conjTranspose * A * U₁) 0 0 = 0 := by
  obtain ⟨v, hray, hnorm⟩ := zero_mem_numerical_range n A hTrace hDiag
  obtain ⟨U, hU, hcol⟩ := onb_extension n v hnorm
  exact ⟨U, hU, by rw [rayleigh_eq_conj_entry n A U v hcol]; exact hray⟩

/-- Numerical range fact: for a trace-zero matrix, there exists a unitary U
    such that (UᴴAU)₀₀ = 0. Packages Toeplitz-Hausdorff (0 ∈ W(A) when tr A = 0)
    together with ONB extension. -/
private lemma exists_unitary_zero_entry (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hTrace : A.trace = 0) :
    ∃ (U₁ : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      IsUnitaryMatrix U₁ ∧
      (U₁.conjTranspose * A * U₁) 0 0 = 0 := by
  by_cases h : ∃ i, A i i = 0
  · -- Case 1: some diagonal entry is zero → use swap matrix
    obtain ⟨i, hi⟩ := h
    refine ⟨Matrix.swap ℂ 0 i, ?_, ?_⟩
    · exact ⟨by rw [Matrix.conjTranspose_swap, Matrix.swap_mul_self],
             by rw [Matrix.conjTranspose_swap, Matrix.swap_mul_self]⟩
    · rw [Matrix.conjTranspose_swap]
      simp [Matrix.swap_mul_apply_left, Matrix.mul_swap_apply_left, hi]
  · -- Case 2: all diagonal entries nonzero → Toeplitz-Hausdorff
    push Not at h
    exact numerical_range_zero_of_trace_zero n A hTrace h

private lemma trace_conj_eq {n : ℕ}
    (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitaryMatrix U) :
    (U.conjTranspose * A * U).trace = A.trace := by
  rw [Matrix.trace_mul_cycle]
  simp [hU.1]

/-- Key step: given a trace-zero (n+2)×(n+2) matrix, there exists a unitary U₁
    such that U₁ᴴAU₁ has zero (0,0) entry and the lower-right subblock has trace 0.
    Uses `exists_unitary_zero_entry` (Toeplitz-Hausdorff + ONB extension) and
    the fact that trace is preserved under unitary conjugation. -/
private lemma exists_unitary_zero_corner (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hTrace : A.trace = 0) :
    ∃ (U₁ : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
      (C : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      IsUnitaryMatrix U₁ ∧
      C 0 0 = 0 ∧
      A = U₁ * C * U₁.conjTranspose ∧
      (∑ i : Fin (n + 1), C i.succ i.succ) = 0 := by
  obtain ⟨U₁, hU₁, hC00⟩ := exists_unitary_zero_entry n A hTrace
  let C := U₁.conjTranspose * A * U₁
  refine ⟨U₁, C, hU₁, hC00, ?_, ?_⟩
  · simp only [C, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U₁ U₁.conjTranspose, hU₁.1, Matrix.one_mul, Matrix.mul_one]
  · have hTraceC : C.trace = 0 := by
      rw [trace_conj_eq A U₁ hU₁, hTrace]
    have hExpand : C.trace = C 0 0 + ∑ i : Fin (n + 1), C i.succ i.succ := by
      simp only [Matrix.trace, Matrix.diag_apply]
      rw [Fin.sum_univ_succ]
    have h1 : C 0 0 + ∑ i : Fin (n + 1), C i.succ i.succ = 0 := by
      rw [← hExpand, hTraceC]
    simp only [show C 0 0 = 0 from hC00, zero_add] at h1
    exact h1

private lemma fromBlocks_unitary {n : ℕ}
    (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hV : IsUnitaryMatrix V) :
    let W := Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 V
    W * W.conjTranspose = 1 ∧ W.conjTranspose * W = 1 := by
  constructor
  · rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp [hV.1]
  · rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp [hV.2]

/-- Given C with zero (0,0) entry and lower-right block unitarily equivalent to a
    zero-diagonal matrix, the whole C is unitarily equivalent to a zero-diagonal matrix. -/
private lemma block_conjugation_zero_diag (n : ℕ)
    (C : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hC00 : C 0 0 = 0)
    (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B'' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hV : IsUnitaryMatrix V)
    (hB : ZeroDiag B'')
    (hLR : lowerRight' C = V * B'' * V.conjTranspose) :
    ∃ (W : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
      (D : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      IsUnitaryMatrix W ∧ ZeroDiag D ∧
      C = W * D * W.conjTranspose := by
  have h12 : 1 + (n + 1) = n + 2 := by omega
  let e : Fin 1 ⊕ Fin (n + 1) ≃ Fin (n + 2) :=
    finSumFinEquiv.trans (finCongr h12)
  let W_sum := Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 V
  let W := (Matrix.reindex e e) W_sum
  let D := W.conjTranspose * C * W
  refine ⟨W, D, ?_, ?_, ?_⟩
  · -- W is unitary
    have hWs := fromBlocks_unitary V hV
    constructor
    · show W * W.conjTranspose = 1
      simp only [W, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
      rw [Matrix.submatrix_mul_equiv, hWs.1, Matrix.submatrix_one_equiv]
    · show W.conjTranspose * W = 1
      simp only [W, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
      rw [Matrix.submatrix_mul_equiv, hWs.2, Matrix.submatrix_one_equiv]
  · -- D is zero-diagonal
    let C_sum : Matrix (Fin 1 ⊕ Fin (n + 1)) (Fin 1 ⊕ Fin (n + 1)) ℂ :=
      C.submatrix e e
    let D_sum := W_sum.conjTranspose * C_sum * W_sum
    suffices hD : D = (Matrix.reindex e e) D_sum by
      intro i
      rw [hD, Matrix.reindex_apply, Matrix.submatrix_apply]
      obtain (⟨j, hj⟩ | ⟨j, hj'⟩) := e.symm i
      · simp only [D_sum, W_sum, C_sum, Matrix.mul_apply, Matrix.conjTranspose_apply,
                   Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
                   Fintype.sum_sum_type, Matrix.one_apply, Matrix.zero_apply,
                   Matrix.submatrix_apply]
        simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, RCLike.star_def,
          MonoidWithZeroHom.map_ite_one_zero, finSumFinEquiv, finCongr, Equiv.trans_apply,
          Equiv.coe_fn_mk, Sum.elim_inl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_singleton, Fin.mk_eq_zero, Fin.castAdd_mk, Fin.cast_mk, star_zero,
          Sum.elim_inr, Fin.cast_natAdd, Fin.addNat_one, Finset.sum_const_zero, add_zero,
          mul_ite, mul_one, mul_zero, ite_eq_right_iff, forall_self_imp, e]
        intro hj0
        subst hj0
        convert hC00 using 2
      · simp only [D_sum, W_sum, C_sum, Matrix.mul_apply, Matrix.conjTranspose_apply,
                   Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
                   Fintype.sum_sum_type, Matrix.zero_apply, Matrix.submatrix_apply]
        simp only [star_zero, zero_mul, Finset.sum_const_zero, zero_add, mul_zero]
        have hCe : ∀ (a b : Fin (n + 1)),
            C (e (Sum.inr a)) (e (Sum.inr b)) = lowerRight' C a b := by
          intro a b
          simp only [lowerRight', Matrix.of_apply]
          congr 1 <;> · ext; simp [e, Fin.succ, Fin.natAdd, Equiv.trans_apply,
            finSumFinEquiv_apply_right, finCongr_apply]; omega
        simp_rw [hCe]
        have key : (V.conjTranspose * lowerRight' C * V) ⟨j, hj'⟩ ⟨j, hj'⟩ = 0 := by
          rw [hLR, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc V.conjTranspose V, hV.2, Matrix.one_mul]
          rw [Matrix.mul_one]
          exact hB ⟨j, hj'⟩
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at key
        convert key using 1
    change W.conjTranspose * C * W = (Matrix.reindex e e) D_sum
    have hC_eq : C = (Matrix.reindex e e) C_sum := by
      simp only [C_sum, Matrix.reindex_apply, Matrix.submatrix_submatrix]
      rw [Equiv.self_comp_symm, Matrix.submatrix_id_id]
    conv_lhs => rw [hC_eq]
    simp only [W, D_sum, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  · -- C = W * D * Wᴴ
    have hWu : W * W.conjTranspose = 1 := by
      simp only [W, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
      rw [Matrix.submatrix_mul_equiv, (fromBlocks_unitary V hV).1, Matrix.submatrix_one_equiv]
    change C = W * D * W.conjTranspose
    simp only [D, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W W.conjTranspose, hWu, Matrix.one_mul]
    rw [Matrix.mul_one]

/-- Fillmore's induction: every trace-zero (m+2)×(m+2) matrix is unitarily
    equivalent to a zero-diagonal matrix. -/
private lemma fillmore_induction (m : ℕ) :
    ∀ (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ),
    A.trace = 0 →
    ∃ (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
      (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ),
      IsUnitaryMatrix U ∧ ZeroDiag B ∧
      A = U * B * U.conjTranspose := by
  induction m with
  | zero =>
    intro A hTrace
    obtain ⟨U₁, C, hU₁, hC00, hAC, hSubTrace⟩ := exists_unitary_zero_corner 0 A hTrace
    have hC11 : C (1 : Fin 2) (1 : Fin 2) = 0 := by
      rw [Fin.sum_univ_one] at hSubTrace; exact hSubTrace
    exact ⟨U₁, C, hU₁, fun i => by fin_cases i <;> [exact hC00; exact hC11], hAC⟩
  | succ k ih =>
    intro A hTrace
    obtain ⟨U₁, C, hU₁, hC00, hAC, hSubTrace⟩ :=
      exists_unitary_zero_corner (k + 1) A hTrace
    have hLRTrace : (lowerRight' C).trace = 0 := by
      rw [lowerRight'_trace]; exact hSubTrace
    obtain ⟨V, B'', hV, hB''zd, hLReq⟩ := ih (lowerRight' C) hLRTrace
    obtain ⟨W, D, hW, hDzd, hCD⟩ :=
      block_conjugation_zero_diag (k + 1) C hC00 V B'' hV hB''zd hLReq
    refine ⟨U₁ * W, D, ?_, hDzd, ?_⟩
    · constructor
      · rw [Matrix.conjTranspose_mul]
        have : U₁ * W * (W.conjTranspose * U₁.conjTranspose) =
            U₁ * (W * W.conjTranspose) * U₁.conjTranspose := by
          simp only [Matrix.mul_assoc]
        rw [this, hW.1, Matrix.mul_one, hU₁.1]
      · rw [Matrix.conjTranspose_mul]
        have : W.conjTranspose * U₁.conjTranspose * (U₁ * W) =
            W.conjTranspose * (U₁.conjTranspose * U₁) * W := by
          simp only [Matrix.mul_assoc]
        rw [this, hU₁.2, Matrix.mul_one, hW.2]
    · rw [hAC, hCD, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]

/-- Fillmore 1969 for n ≥ 2: every trace-zero complex matrix is unitarily
    equivalent to a zero-diagonal matrix. -/
theorem fillmore_ge_two (m : ℕ)
    (A : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ)
    (hTrace : A.trace = 0) :
    ∃ (U : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ)
      (B : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ),
      IsUnitaryMatrix U ∧ ZeroDiag B ∧
      A = U * B * U.conjTranspose := by
  exact fillmore_induction m A hTrace

/-- Fillmore 1969: every trace-zero complex matrix is unitarily
    equivalent to a zero-diagonal matrix.
    Proof: induction on n. Base n=1: trace=0 ⟹ A=0.
    Step: ∃ unit v₀ with ⟨v₀,Av₀⟩=0 (sphere integral = tr(A)/n = 0);
    extend to ONB, get A=[[0,*];[*,A']] with tr(A')=0; apply IH. -/
theorem fillmore {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hTrace : A.trace = 0) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ),
      IsUnitaryMatrix U ∧
      ZeroDiag B ∧
      A = U * B * U.conjTranspose := by
  cases n with
  | zero =>
    -- Fin 0 is empty; any matrix trivially satisfies everything
    exact ⟨1, A, ⟨by simp [Matrix.conjTranspose_one], by simp [Matrix.conjTranspose_one]⟩,
      fun i => i.elim0, by simp [Matrix.conjTranspose_one]⟩
  | succ m =>
    cases m with
    | zero =>
      -- 1×1 case: trace = 0 means A 0 0 = 0, so A is zero-diagonal
      refine ⟨1, A, ⟨by simp [Matrix.conjTranspose_one], by simp [Matrix.conjTranspose_one]⟩,
        ?_, by simp [Matrix.conjTranspose_one]⟩
      intro i
      have hi : i = 0 := Fin.eq_zero i
      rw [hi]
      -- hTrace says the trace (= A 0 0 for 1×1) is zero
      rw [show A.trace = A 0 0 from Fin.sum_univ_one _] at hTrace; exact hTrace
    | succ m =>
      -- For n = m + 2 ≥ 2: Fillmore's 1969 induction argument.
      -- Step 1: The map v ↦ ⟨v, Av⟩ on the unit sphere S^{2(m+2)-1} has zero integral
      --         (= trace(A)/(m+2) = 0). By connectedness of S^{2(m+2)-1}, there exists
      --         a unit vector v₀ with ⟨v₀, Av₀⟩ = 0.
      -- Step 2: Extend v₀ to an ONB {v₀, v₁, ..., v_{m+1}}. In this basis,
      --         A = [[0, *]; [*, A']] with trace(A') = trace(A) - 0 = 0.
      -- Step 3: By induction, A' is unitarily equivalent to a zero-diagonal matrix.
      exact fillmore_ge_two m A hTrace

end CommutatorTheorem
