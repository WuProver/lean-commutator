import CommutatorTheorem.Shared.Fillmore
import CommutatorTheorem.Epsilon.Rosenblum
import CommutatorTheorem.Epsilon.Paving
import CommutatorTheorem.Epsilon.THConvexity
import CommutatorTheorem.Epsilon.NEst
import CommutatorTheorem.Epsilon.Pow4Bootstrap
import CommutatorTheorem.Epsilon.Pow4BTRecursion
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Quantitative Commutator Theorem

This file formalizes the main results of JOS 2013:
- Fillmore's lemma is imported from the shared unitary zero-diagonalization module
- Theorem 3: quantitative bound for zero-diagonal matrices
- Theorem 1: the main commutator theorem for trace-zero matrices
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instCStarRing
attribute [local instance] Matrix.instL2OpNormedSpace

open CommutatorTheorem

namespace CommutatorTheorem

/-- For n ≥ 1, there exists k with n ≤ 4^k and 4^k ≤ 4*n (minimal k). -/
private lemma exists_pow4_sandwich (n : ℕ) (hn : 1 ≤ n) :
    ∃ k : ℕ, n ≤ 4 ^ k ∧ (4 : ℝ) ^ k ≤ 4 * (n : ℝ) := by
  have hex : ∃ k, n ≤ 4 ^ k := ⟨n, le_of_lt (Nat.lt_pow_self (show 1 < 4 by norm_num))⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  set k := Nat.find hex
  by_cases hk0 : k = 0
  · simp only [hk0, pow_zero]
    linarith [show (1 : ℝ) ≤ (n : ℝ) from by exact_mod_cast hn]
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hprev : ¬ (n ≤ 4 ^ (k - 1)) := Nat.find_min hex (by omega)
    push Not at hprev
    calc (4 : ℝ) ^ k = (4 : ℝ) ^ (k - 1 + 1) := by congr 1; omega
      _ = (4 : ℝ) ^ (k - 1) * 4 := pow_succ _ _
      _ ≤ (↑(n - 1) : ℝ) * 4 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 4)
          exact_mod_cast Nat.le_sub_one_of_lt hprev
      _ ≤ (n : ℝ) * 4 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 4)
          exact_mod_cast Nat.sub_le n 1
      _ = 4 * (n : ℝ) := by ring

/-! ## Zero-padding and restriction infrastructure for embedding step -/

/-- The canonical embedding Fin n → Fin m when n ≤ m. -/
private def finEmbed {n m : ℕ} (h : n ≤ m) : Fin n → Fin m :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩

private lemma finEmbed_injective {n m : ℕ} (h : n ≤ m) : Function.Injective (finEmbed h) :=
  fun _ _ hab => Fin.ext (Fin.mk.inj hab)

/-- Zero-pad an n×n matrix into an m×m matrix (n ≤ m). -/
private noncomputable def zeroPad {n m : ℕ} (_h : n ≤ m) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j =>
    if hi : i.val < n then
      if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else 0
    else 0

/-- Zero-padding preserves zero-diagonal. -/
private lemma zeroPad_zeroDiag {n m : ℕ} (h : n ≤ m) {A : Matrix (Fin n) (Fin n) ℂ}
    (hzd : ZeroDiag A) : ZeroDiag (zeroPad h A) := by
  intro i
  simp only [zeroPad, Matrix.of_apply]
  by_cases hi : i.val < n
  · simp only [hi, dite_true]; exact hzd ⟨i.val, hi⟩
  · simp [hi]

/-- Restrict an m×m matrix to its upper-left n×n block. -/
private noncomputable def restrict {n m : ℕ} (h : n ≤ m) (A : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => A (finEmbed h i) (finEmbed h j)

/-- restrict ∘ zeroPad = id -/
private lemma restrict_zeroPad {n m : ℕ} (h : n ≤ m) (A : Matrix (Fin n) (Fin n) ℂ) :
    restrict h (zeroPad h A) = A := by
  ext i j
  simp only [restrict, zeroPad, finEmbed, Matrix.of_apply, i.isLt, j.isLt, dite_true]

-- Helper: sum over Fin m of a function supported on [0,n) equals sum over Fin n
private lemma sum_finEmbed_eq {n m : ℕ} (h : n ≤ m) {α : Type*} [AddCommMonoid α]
    (f : Fin m → α) (hf : ∀ i : Fin m, ¬(i.val < n) → f i = 0) :
    ∑ i : Fin m, f i = ∑ i : Fin n, f (finEmbed h i) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i.val < n)]
  rw [show ∑ i ∈ Finset.filter (fun i : Fin m => ¬(i.val < n)) Finset.univ, f i = 0 from
    Finset.sum_eq_zero (fun i hi => hf i (Finset.mem_filter.mp hi).2), add_zero]
  symm
  show ∑ i : Fin n, f (finEmbed h i) =
    ∑ i ∈ Finset.filter (fun i : Fin m => i.val < n) Finset.univ, f i
  apply Finset.sum_bij (fun i _ => finEmbed h i)
  · intro i _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
  · intro i₁ _ i₂ _ h12; exact finEmbed_injective h h12
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨⟨j.val, hj⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i _; rfl

/-- The operator norm of a restriction is at most the original. -/
private lemma restrict_norm_le {n m : ℕ} (h : n ≤ m) (A : Matrix (Fin m) (Fin m) ℂ) :
    ‖restrict h A‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simp only [LinearEquiv.trans_apply]
  change ‖Matrix.toEuclideanLin (restrict h A) x‖ ≤ ‖A‖ * ‖x‖
  rw [show Matrix.toEuclideanLin (restrict h A) x =
      WithLp.toLp 2 ((restrict h A).mulVec x.ofLp) from
    Matrix.toLpLin_apply 2 2 (restrict h A) x]
  set w := x.ofLp
  -- Zero-pad w into Fin m
  set padW : Fin m → ℂ := fun i => if hi : i.val < n then w ⟨i.val, hi⟩ else 0
  set v : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 padW
  -- Component identity: (restrict(A) * w)(i) = (A * padW)(embed(i))
  have hcomp : ∀ i : Fin n,
      ((restrict h A).mulVec w) i = (A.mulVec padW) (finEmbed h i) := by
    intro i
    simp only [restrict, Matrix.mulVec, dotProduct, Matrix.of_apply]
    -- Goal: Σ_{j:Fin n} A(e(i), e(j)) * w(j) = Σ_{j:Fin m} A(e(i), j) * padW(j)
    -- RHS terms with j.val ≥ n vanish since padW(j) = 0
    rw [show (fun j : Fin m => A (finEmbed h i) j * padW j) =
        (fun j => if hj : j.val < n then A (finEmbed h i) j * w ⟨j.val, hj⟩ else 0) from by
      ext j; simp only [padW]; split_ifs <;> simp]
    rw [sum_finEmbed_eq h _ (fun j hj => by simp [hj])]
    congr 1; ext j; simp [finEmbed, j.isLt]
  -- Helper: Σ_{Fin n} g(embed(i)) ≤ Σ_{Fin m} g(j) when g ≥ 0
  have sum_embed_le : ∀ (g : Fin m → ℝ), (∀ j, 0 ≤ g j) →
      ∑ i : Fin n, g (finEmbed h i) ≤ ∑ j : Fin m, g j := by
    intro g hg
    calc ∑ i : Fin n, g (finEmbed h i)
        = ∑ j ∈ Finset.image (finEmbed h) Finset.univ, g j := by
          symm; exact Finset.sum_image (fun i₁ _ i₂ _ h12 => finEmbed_injective h h12)
      _ ≤ ∑ j : Fin m, g j :=
          Finset.sum_le_univ_sum_of_nonneg hg
  -- Squared norm comparison
  have hnorm_sq_le :
      ∑ i : Fin n, ‖((restrict h A).mulVec w) i‖ ^ 2 ≤
      ∑ i : Fin m, ‖(A.mulVec padW) i‖ ^ 2 :=
    calc ∑ i : Fin n, ‖((restrict h A).mulVec w) i‖ ^ 2
        = ∑ i : Fin n, ‖(A.mulVec padW) (finEmbed h i)‖ ^ 2 := by
          congr 1; ext i; rw [hcomp]
      _ ≤ ∑ i : Fin m, ‖(A.mulVec padW) i‖ ^ 2 :=
          sum_embed_le _ (fun j => pow_nonneg (norm_nonneg _) 2)
  -- ‖v‖ = ‖x‖
  have hv_norm : ‖v‖ = ‖x‖ := by
    simp only [EuclideanSpace.norm_eq]
    congr 1
    rw [show ∑ i : Fin m, ‖(v : EuclideanSpace ℂ (Fin m)).ofLp i‖ ^ 2 =
        ∑ i : Fin m, ‖padW i‖ ^ 2 from rfl]
    rw [show ∑ i : Fin m, ‖padW i‖ ^ 2 = ∑ i : Fin n, ‖padW (finEmbed h i)‖ ^ 2 from
      sum_finEmbed_eq h (fun i => ‖padW i‖ ^ 2) (fun i hi => by
        simp [padW, show ¬(i.val < n) from hi])]
    congr 1; ext i; simp only [padW, finEmbed, i.isLt, dite_true]; rfl
  -- Final: ‖restrict(A)*w‖ ≤ ‖A‖ * ‖x‖
  apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2)),
      mul_pow]
  -- Use l2_opNorm_mulVec for the bound
  have hAv : ‖(EuclideanSpace.equiv (Fin m) ℂ).symm (A.mulVec v.ofLp)‖ ≤ ‖A‖ * ‖v‖ :=
    Matrix.l2_opNorm_mulVec A v
  have hAv_sq : ∑ i : Fin m, ‖(A.mulVec padW) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖x‖ ^ 2 := by
    -- ‖A * padW‖_EuclideanSpace ≤ ‖A‖ * ‖v‖ = ‖A‖ * ‖x‖
    set Av := (EuclideanSpace.equiv (Fin m) ℂ).symm (A.mulVec v.ofLp)
    have hAv_sq : ‖Av‖ ^ 2 = ∑ i : Fin m, ‖Av.ofLp i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
    -- Av.ofLp = A.mulVec padW (definitional)
    have hAv_ofLp : ∀ i, Av.ofLp i = (A.mulVec padW) i := fun _ => rfl
    calc ∑ i : Fin m, ‖(A.mulVec padW) i‖ ^ 2
        = ∑ i : Fin m, ‖Av.ofLp i‖ ^ 2 := by congr 1
      _ = ‖Av‖ ^ 2 := hAv_sq.symm
      _ ≤ (‖A‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hAv 2
      _ = ‖A‖ ^ 2 * ‖v‖ ^ 2 := mul_pow _ _ _
      _ = ‖A‖ ^ 2 * ‖x‖ ^ 2 := by rw [hv_norm]
  linarith

/-- The operator norm of a zero-padded matrix equals the original. -/
private lemma zeroPad_norm_eq {n m : ℕ} (h : n ≤ m) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖zeroPad h A‖ = ‖A‖ := by
  apply le_antisymm
  · -- ‖zeroPad h A‖ ≤ ‖A‖
    rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simp only [LinearEquiv.trans_apply]
    change ‖Matrix.toEuclideanLin (zeroPad h A) x‖ ≤ ‖A‖ * ‖x‖
    rw [show Matrix.toEuclideanLin (zeroPad h A) x =
        WithLp.toLp 2 ((zeroPad h A).mulVec x.ofLp) from
      Matrix.toLpLin_apply 2 2 (zeroPad h A) x]
    set v := x.ofLp
    set w : Fin n → ℂ := fun i => v (finEmbed h i)
    set xn : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 w
    -- (zeroPad(A)*v)(i) for i < n is (A * w)(i), for i ≥ n is 0
    have hcomp_lt : ∀ (i : Fin m) (hi : i.val < n),
        ((zeroPad h A).mulVec v) i = (A.mulVec w) ⟨i.val, hi⟩ := by
      intro i hi
      simp only [zeroPad, Matrix.mulVec, dotProduct, Matrix.of_apply, hi, dite_true]
      -- Goal: Σ_{j:Fin m} (if hj : j.val < n then A ⟨i.val,_⟩ ⟨j.val,hj⟩ else 0) * v(j) =
      --       Σ_{j:Fin n} A ⟨i.val,hi⟩ j * v(finEmbed h j)
      -- Factor: the LHS terms with j.val ≥ n vanish
      rw [show (fun j : Fin m => (if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0) * v j) =
          (fun j => if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ * v j else 0) from by
        ext j; split_ifs <;> simp]
      rw [sum_finEmbed_eq h _ (fun j hj => by simp [hj])]
      congr 1; ext j
      change (if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ * v ⟨j.val, _⟩ else 0) =
        A ⟨i.val, hi⟩ j * w j
      simp only [j.isLt, dite_true, w, finEmbed]
    have hcomp_ge : ∀ i : Fin m, ¬(i.val < n) →
        ((zeroPad h A).mulVec v) i = 0 := by
      intro i hi
      simp only [zeroPad, Matrix.mulVec, dotProduct, Matrix.of_apply, hi, dite_false]
      exact Finset.sum_eq_zero (fun _ _ => zero_mul _)
    apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2)),
        mul_pow]
    -- Σ_{Fin m} ‖(zeroPad(A)*v)(i)‖² = Σ_{Fin n} ‖(A*w)(i)‖²
    have hsum_eq : ∑ i : Fin m, ‖((zeroPad h A).mulVec v) i‖ ^ 2 =
        ∑ i : Fin n, ‖(A.mulVec w) i‖ ^ 2 := by
      rw [sum_finEmbed_eq h _ (fun i hi => by simp [hcomp_ge i hi])]
      congr 1; ext i; rw [hcomp_lt (finEmbed h i) i.isLt]; simp [finEmbed]
    rw [hsum_eq]
    -- Use l2_opNorm_mulVec for A
    have hAxn := Matrix.l2_opNorm_mulVec A xn
    set Aw := (EuclideanSpace.equiv (Fin n) ℂ).symm (A.mulVec xn.ofLp)
    have hAw_sq : ‖Aw‖ ^ 2 = ∑ i : Fin n, ‖(A.mulVec w) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
      congr 1
    -- ‖xn‖ ≤ ‖x‖ (picking n ≤ m components)
    have hxn_le : ‖xn‖ ≤ ‖x‖ := by
      simp only [EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      have sum_embed_le : ∀ (g : Fin m → ℝ), (∀ j, 0 ≤ g j) →
          ∑ i : Fin n, g (finEmbed h i) ≤ ∑ j : Fin m, g j := by
        intro g hg
        calc ∑ i : Fin n, g (finEmbed h i)
            = ∑ j ∈ Finset.image (finEmbed h) Finset.univ, g j := by
              symm; exact Finset.sum_image (fun i₁ _ i₂ _ h12 => finEmbed_injective h h12)
          _ ≤ ∑ j : Fin m, g j := Finset.sum_le_univ_sum_of_nonneg hg
      exact sum_embed_le _ (fun j => pow_nonneg (norm_nonneg _) 2)
    calc ∑ i : Fin n, ‖(A.mulVec w) i‖ ^ 2
        = ‖Aw‖ ^ 2 := hAw_sq.symm
      _ ≤ (‖A‖ * ‖xn‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hAxn 2
      _ = ‖A‖ ^ 2 * ‖xn‖ ^ 2 := mul_pow _ _ _
      _ ≤ ‖A‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
  · -- ‖A‖ ≤ ‖zeroPad h A‖
    calc ‖A‖ = ‖restrict h (zeroPad h A)‖ := by rw [restrict_zeroPad]
      _ ≤ ‖zeroPad h A‖ := restrict_norm_le h _

/-- Restricting a commutator preserves the commutator identity when the first
    argument is diagonal: restrict([B,C]) = [restrict B, restrict C]. -/
private lemma restrict_matComm_of_diag {n m : ℕ} (h : n ≤ m)
    (B C : Matrix (Fin m) (Fin m) ℂ) (hdiag : IsDiagMatrix B) :
    restrict h (⁅B, C⁆ₘ) = ⁅restrict h B, restrict h C⁆ₘ := by
  ext i j
  simp only [restrict, matComm, Matrix.of_apply, Matrix.sub_apply, Matrix.mul_apply]
  set ei := finEmbed h i
  set ej := finEmbed h j
  have hBC : ∑ l : Fin m, B ei l * C l ej = B ei ei * C ei ej := by
    apply Fintype.sum_eq_single ei
    intro l hl
    have : B ei l = 0 := hdiag ei l (Ne.symm hl)
    simp [this]
  have hCB : ∑ l : Fin m, C ei l * B l ej = C ei ej * B ej ej := by
    apply Fintype.sum_eq_single ej
    intro l hl
    have : B l ej = 0 := hdiag l ej hl
    simp [this]
  have hBC' : ∑ x : Fin n, B ei (finEmbed h x) * C (finEmbed h x) ej =
      B ei ei * C ei ej := by
    apply Fintype.sum_eq_single i
    intro l hl
    have hne : finEmbed h l ≠ ei := fun heq => hl (finEmbed_injective h heq)
    have : B ei (finEmbed h l) = 0 := hdiag ei (finEmbed h l) (Ne.symm hne)
    simp [this]
  have hCB' : ∑ x : Fin n, C ei (finEmbed h x) * B (finEmbed h x) ej =
      C ei ej * B ej ej := by
    apply Fintype.sum_eq_single j
    intro l hl
    have hne : finEmbed h l ≠ ej := fun heq => hl (finEmbed_injective h heq)
    have : B (finEmbed h l) ej = 0 := hdiag (finEmbed h l) ej hne
    simp [this]
  rw [hBC, hCB, hBC', hCB']

/-- The affine map z ↦ ((1-ε)/2) * z + δ is injective on ℂ when ε ≠ 1. -/
private lemma affine_map_injective (ε : ℝ) (hε1 : ε ≠ 1) (δ : ℂ) :
    Function.Injective (fun z : ℂ => ((1 - ↑ε) / 2 : ℂ) * z + δ) := by
  intro a b hab
  simp only at hab
  have hne : ((1 - ↑ε) / 2 : ℂ) ≠ 0 := by
    rw [Ne, div_eq_zero_iff]
    push Not
    constructor
    · intro h
      apply hε1
      have := congr_arg Complex.re h
      simp at this
      linarith
    · exact two_ne_zero
  have : ((1 - ↑ε) / 2 : ℂ) * a = ((1 - ↑ε) / 2 : ℂ) * b :=
    add_right_cancel hab
  exact mul_left_cancel₀ hne this

/-- Lambda ε k has cardinality at least 4^(k+1) when 0 < ε < 1.
    Each level multiplies the count by 4 via 4 injective affine maps. -/
private lemma cornerSet_card : cornerSet.card = 4 := by
  unfold cornerSet
  rw [show ({⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩} : Finset ℂ).card =
    ({⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩} : Finset ℂ).card from rfl]
  have h1 : (⟨1, 1⟩ : ℂ) ∉ ({⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩} : Finset ℂ) := by
    simp [Finset.mem_insert, Finset.mem_singleton, Complex.ext_iff]; norm_num
  have h2 : (⟨1, -1⟩ : ℂ) ∉ ({⟨-1, 1⟩, ⟨-1, -1⟩} : Finset ℂ) := by
    simp [Finset.mem_insert, Finset.mem_singleton, Complex.ext_iff]; norm_num
  have h3 : (⟨-1, 1⟩ : ℂ) ∉ ({⟨-1, -1⟩} : Finset ℂ) := by
    simp [Finset.mem_singleton, Complex.ext_iff]; norm_num
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]

/-- Elements of Lambda ε k have |re| ≤ 2 and |im| ≤ 2 when 0 < ε < 1. -/
private lemma Lambda_re_im_le_two (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ)
    (z : ℂ) (hz : z ∈ Lambda ε k) : |z.re| ≤ 2 ∧ |z.im| ≤ 2 := by
  induction k generalizing z with
  | zero =>
    simp only [Lambda] at hz
    unfold cornerSet at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> norm_num [abs_le]
  | succ k ih =>
    simp only [Lambda, Finset.mem_biUnion, Finset.mem_image] at hz
    obtain ⟨δ, hδ_mem, w, hw_mem, rfl⟩ := hz
    obtain ⟨hw_re, hw_im⟩ := ih w hw_mem
    unfold cornerSet at hδ_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hδ_mem
    have hc_nonneg : 0 ≤ (1 - ε) / 2 := by linarith
    have hc_bound : (1 - ε) / 2 * 2 ≤ 1 := by linarith
    constructor <;> {
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.div_re, Complex.div_im,
            Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
            Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat,
            mul_zero, sub_zero, zero_mul, add_zero]
      rcases hδ_mem with rfl | rfl | rfl | rfl <;> simp only [] <;>
      · rw [abs_le]; constructor <;> nlinarith [abs_nonneg w.re, abs_nonneg w.im,
          abs_le.mp hw_re, abs_le.mp hw_im]
    }

/-- Lambda ε k has cardinality at least 4^(k+1) when 0 < ε < 1.
    Each level multiplies the count by 4 via 4 injective affine maps
    whose images are pairwise disjoint (separated by real/imaginary sign). -/
private lemma Lambda_images_disjoint (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
    (cornerSet : Set ℂ).PairwiseDisjoint
      (fun δ => (Lambda ε k).image (fun z => ((1 - ↑ε) / 2 : ℂ) * z + δ) : ℂ → Finset ℂ) := by
  intro δ₁ hδ₁ δ₂ hδ₂ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_image] at hx₁ hx₂
  obtain ⟨z₁, hz₁, rfl⟩ := hx₁
  obtain ⟨z₂, hz₂, heq⟩ := hx₂
  -- From heq: c * z₁ + δ₁ = c * z₂ + δ₂, so c * (z₁ - z₂) = δ₂ - δ₁
  -- We'll show this leads to a contradiction using re/im bounds.
  have hre₁ := (Lambda_re_im_le_two ε hε hε1 k z₁ hz₁).1
  have him₁ := (Lambda_re_im_le_two ε hε hε1 k z₁ hz₁).2
  have hre₂ := (Lambda_re_im_le_two ε hε hε1 k z₂ hz₂).1
  have him₂ := (Lambda_re_im_le_two ε hε hε1 k z₂ hz₂).2
  -- The corners have re, im ∈ {-1, 1}
  unfold cornerSet at hδ₁ hδ₂
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_coe] at hδ₁ hδ₂
  -- Case analysis: since δ₁ ≠ δ₂, they differ in re or im
  -- If re(δ₁) ≠ re(δ₂): image re parts have opposite signs
  -- If re(δ₁) = re(δ₂) but im(δ₁) ≠ im(δ₂): image im parts have opposite signs
  -- From heq: c * z₁.re + δ₁.re = c * z₂.re + δ₂.re (comparing re parts)
  --           c * z₁.im + δ₁.im = c * z₂.im + δ₂.im (comparing im parts)
  -- where c = (1-ε)/2 ∈ (0, 1/2)
  have hc_pos : (0 : ℝ) < (1 - ε) / 2 := by linarith
  have hc_lt : (1 - ε) / 2 < 1 / 2 := by linarith
  have heq_re : (1 - ε) / 2 * z₁.re + δ₁.re = (1 - ε) / 2 * z₂.re + δ₂.re := by
    have := congr_arg Complex.re heq
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at this
    linarith
  have heq_im : (1 - ε) / 2 * z₁.im + δ₁.im = (1 - ε) / 2 * z₂.im + δ₂.im := by
    have := congr_arg Complex.im heq
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at this
    linarith
  -- Now case-split on the corners. δ₁ = δ₂ cases are ruled out by hne.
  -- For δ₁ ≠ δ₂: either re or im of the corners differ by ±2,
  -- but |c*(z₁.re - z₂.re)| ≤ c*4 < 2 and |c*(z₁.im - z₂.im)| < 2.
  have habs_re₁ := abs_le.mp hre₁  -- -2 ≤ z₁.re ≤ 2
  have habs_re₂ := abs_le.mp hre₂
  have habs_im₁ := abs_le.mp him₁
  have habs_im₂ := abs_le.mp him₂
  rcases hδ₁ with rfl | rfl | rfl | rfl <;> rcases hδ₂ with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hne | (simp only [] at heq_re heq_im; nlinarith)

private lemma Lambda_card_ge (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
    4 ^ k ≤ (Lambda ε k).card := by
  induction k with
  | zero =>
    simp only [Lambda, pow_zero]
    have := cornerSet_card; omega
  | succ k ih =>
    simp only [Lambda]
    rw [Finset.card_biUnion (Lambda_images_disjoint ε hε hε1 k)]
    have hε_ne : ε ≠ 1 := ne_of_lt hε1
    calc 4 ^ (k + 1) = 4 ^ k * 4 := pow_succ 4 k
      _ ≤ (Lambda ε k).card * 4 := Nat.mul_le_mul_right 4 ih
      _ = 4 * (Lambda ε k).card := by ring
      _ = cornerSet.card * (Lambda ε k).card := by rw [cornerSet_card]
      _ = ∑ _u ∈ cornerSet, (Lambda ε k).card := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = ∑ u ∈ cornerSet,
            ((Lambda ε k).image (fun z => ((1 - ↑ε) / 2 : ℂ) * z + u)).card := by
          congr 1; ext δ
          rw [Finset.card_image_of_injective _ (affine_map_injective ε hε_ne δ)]

/-- Lambda ε k contains at least m distinct elements when m ≤ |Lambda ε k|.
    Uses `Function.Embedding.exists_of_card_le_finset`. -/
private lemma Lambda_has_distinct_elems (ε : ℝ) (_hε : 0 < ε) (k : ℕ) (m : ℕ)
    (hm : m ≤ (Lambda ε k).card) :
    ∃ f : Fin m → ℂ, Function.Injective f ∧ ∀ i, f i ∈ (Lambda ε k : Set ℂ) := by
  have hcard : Fintype.card (Fin m) ≤ (Lambda ε k).card := by
    simp only [Fintype.card_fin]; exact hm
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hcard
  exact ⟨f, f.injective, fun i => hf (Set.mem_range_self i)⟩

/-- Construct the C matrix given distinct diagonal entries b and a matrix A:
    C_{ij} = A_{ij} / (b_i - b_j) for i ≠ j, C_{ii} = 0. -/
private noncomputable def solveC {m : ℕ} (b : Fin m → ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j =>
    if i = j then 0
    else A i j / (b i - b j)

/-- The commutator [diag(b), solveC b A] equals A
    when b is injective and A is zero-diagonal. -/
private lemma comm_diag_solveC {m : ℕ} (b : Fin m → ℂ) (hb : Function.Injective b)
    (A : Matrix (Fin m) (Fin m) ℂ) (hzd : ZeroDiag A) :
    A = ⁅Matrix.diagonal b, solveC b A⁆ₘ := by
  ext i j
  simp only [matComm, Matrix.sub_apply, Matrix.mul_apply, Matrix.diagonal_apply]
  have hS1 : ∑ x, (if i = x then b i else 0) * solveC b A x j =
      b i * solveC b A i j := by
    conv_lhs =>
      arg 2; ext x
      rw [show (if i = x then b i else 0) =
        if x = i then b i else 0 from by split_ifs <;> simp_all]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hS2 : ∑ x, solveC b A i x * (if x = j then b x else 0) =
      solveC b A i j * b j := by
    simp [Finset.sum_ite_eq', Finset.mem_univ, mul_comm]
  rw [hS1, hS2]
  by_cases hij : i = j
  · subst hij
    simp only [solveC, Matrix.of_apply, ite_true]
    rw [hzd i]; ring
  · simp only [solveC, Matrix.of_apply, hij, ite_false]
    have hne : b i - b j ≠ 0 := sub_ne_zero.mpr (hb.ne hij)
    field_simp

private lemma diag_isDiagMatrix {m : ℕ} (b : Fin m → ℂ) :
    IsDiagMatrix (Matrix.diagonal b) := by
  intro i j hij; simp [hij]

/-- The set defining mu is nonempty for zero-diagonal matrices.
    Every zero-diagonal matrix admits some decomposition A = [B, C]
    with B diagonal having Lambda entries. -/
private lemma mu_set_nonempty {m : ℕ} (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (A : Matrix (Fin m) (Fin m) ℂ) (hzd : ZeroDiag A)
    (hm : m ≤ (Lambda ε k).card) :
    ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
      IsDiagMatrix B ∧ (∀ i, B i i ∈ (Lambda ε k : Set ℂ)) ∧
      A = ⁅B, C⁆ₘ := by
  obtain ⟨b, hb_inj, hb_mem⟩ := Lambda_has_distinct_elems ε hε k m hm
  exact ⟨Matrix.diagonal b, solveC b A,
    diag_isDiagMatrix b,
    fun i => by simp only [Matrix.diagonal_apply_eq, SetLike.mem_coe]; exact hb_mem i,
    comm_diag_solveC b hb_inj A hzd⟩

/-- From mu bound + nonemptiness, extract witnesses with controlled norm.
    If mu ε k A ≤ M, then for any δ > 0, ∃ B C with the decomposition and ‖C‖ ≤ M + δ. -/
private lemma mu_extract_witness {m : ℕ} {ε : ℝ} (hε : 0 < ε) {k : ℕ}
    {A : Matrix (Fin m) (Fin m) ℂ} (hzd : ZeroDiag A)
    (hm : m ≤ (Lambda ε k).card)
    {M : ℝ} (hM : mu ε k A ≤ M) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
      IsDiagMatrix B ∧ (∀ i, B i i ∈ (Lambda ε k : Set ℂ)) ∧
      A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ M + δ := by
  set S := {c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
    IsDiagMatrix B ∧ (∀ i, B i i ∈ (Lambda ε k : Set ℂ)) ∧
    A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hS_def
  obtain ⟨B₀, C₀, hd₀, hl₀, hc₀⟩ := mu_set_nonempty ε hε k A hzd hm
  have hne : S.Nonempty := ⟨‖C₀‖, B₀, C₀, hd₀, hl₀, hc₀, le_refl _⟩
  have hlt : sInf S < M + δ := lt_of_le_of_lt hM (lt_add_of_pos_right M hδ)
  obtain ⟨s, hs_mem, hs_lt⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨B, C, hd, hl, hcomm, hnC⟩ := hs_mem
  exact ⟨B, C, hd, hl, hcomm, le_trans hnC (le_of_lt hs_lt)⟩

/-- Lambda entries have norm at most 3 when 0 < ε < 1. -/
private lemma Lambda_norm_le_three (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ) (z : ℂ)
    (hz : z ∈ (Lambda ε k : Set ℂ)) :
    ‖z‖ ≤ 3 := by
  induction k generalizing z with
  | zero =>
    simp only [Lambda, Finset.mem_coe] at hz
    unfold cornerSet at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    have hsqrt2_le_3 : Real.sqrt 2 ≤ 3 :=
      (Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 3)).mpr (by norm_num)
    rcases hz with rfl | rfl | rfl | rfl <;>
      simp only [Complex.norm_eq_sqrt_sq_add_sq] <;> norm_num <;> exact hsqrt2_le_3
  | succ k ih =>
    simp only [Lambda, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image] at hz
    obtain ⟨δ, hδ_mem, w, hw_mem, rfl⟩ := hz
    have hsqrt2_le : Real.sqrt 2 ≤ 3 / 2 :=
      (Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 3/2)).mpr (by norm_num)
    have hδ_norm : ‖δ‖ ≤ Real.sqrt 2 := by
      unfold cornerSet at hδ_mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hδ_mem
      rcases hδ_mem with rfl | rfl | rfl | rfl <;>
        (simp only [Complex.norm_eq_sqrt_sq_add_sq]; norm_num)
    have hcoeff : ‖((1 - ↑ε) / 2 : ℂ)‖ ≤ 1 / 2 := by
      rw [norm_div, Complex.norm_ofNat]
      apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
      rw [show (1 : ℂ) - ↑ε = ↑((1 : ℝ) - ε) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    calc ‖((1 - ↑ε) / 2 : ℂ) * w + δ‖
        ≤ ‖((1 - ↑ε) / 2 : ℂ) * w‖ + ‖δ‖ := norm_add_le _ _
      _ = ‖((1 - ↑ε) / 2 : ℂ)‖ * ‖w‖ + ‖δ‖ := by rw [norm_mul]
      _ ≤ (1 / 2) * 3 + Real.sqrt 2 := by
          gcongr
          · exact ih w (Finset.mem_coe.mpr hw_mem)
      _ ≤ 3 := by linarith

/-- A diagonal matrix with entries bounded by c has operator norm at most c. -/
private lemma diag_norm_le {m : ℕ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hdiag : IsDiagMatrix B) (c : ℝ) (hc : 0 ≤ c) (hentries : ∀ i, ‖B i i‖ ≤ c) :
    ‖B‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  simp only [LinearEquiv.trans_apply]
  change ‖Matrix.toEuclideanLin B x‖ ≤ c * ‖x‖
  rw [show Matrix.toEuclideanLin B x = WithLp.toLp 2 (B.mulVec x.ofLp) from
    Matrix.toLpLin_apply 2 2 B x]
  set v := x.ofLp
  set w := B.mulVec v
  apply le_of_sq_le_sq _ (mul_nonneg hc (norm_nonneg x))
  rw [show ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin m))‖ =
      Real.sqrt (∑ i, ‖w i‖ ^ 2) from EuclideanSpace.norm_eq _,
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2)),
      mul_pow]
  have hx_sq : ‖x‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq x,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
  rw [hx_sq]
  have hw : ∀ i, w i = B i i * v i := by
    intro i
    simp only [w, Matrix.mulVec, dotProduct]
    apply Fintype.sum_eq_single i
    intro l hl
    have : B i l = 0 := hdiag i l (Ne.symm hl)
    simp [this]
  calc ∑ i, ‖w i‖ ^ 2
      = ∑ i, ‖B i i * v i‖ ^ 2 := by congr 1; ext i; rw [hw]
    _ = ∑ i, (‖B i i‖ * ‖v i‖) ^ 2 := by congr 1; ext i; rw [norm_mul]
    _ = ∑ i, ‖B i i‖ ^ 2 * ‖v i‖ ^ 2 := by congr 1; ext i; ring
    _ ≤ ∑ i, c ^ 2 * ‖v i‖ ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) 2)
        exact pow_le_pow_left₀ (norm_nonneg _) (hentries i) 2
    _ = c ^ 2 * ∑ i, ‖v i‖ ^ 2 := by rw [Finset.mul_sum]

/-! ## Additional infrastructure for mu bounds -/

/-- mu is nonneg: it is the infimum of a set of reals that are all ≥ 0 (upper bounds on norms). -/
private lemma mu_nonneg {m : ℕ} (ε : ℝ) (k : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) :
    0 ≤ mu ε k A := by
  unfold mu
  by_cases hne : {c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
      IsDiagMatrix B ∧ (∀ i, B i i ∈ (Lambda ε k : Set ℂ)) ∧
      A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}.Nonempty
  · exact le_csInf hne (fun c ⟨_, C, _, _, _, hC⟩ => le_trans (norm_nonneg C) hC)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

/-- mu ε k A ≤ ‖C‖ for any valid decomposition witness. -/
private lemma mu_le_witness_norm {m : ℕ} (ε : ℝ) (k : ℕ)
    (A : Matrix (Fin m) (Fin m) ℂ)
    (B C : Matrix (Fin m) (Fin m) ℂ)
    (hdiag : IsDiagMatrix B) (hlam : ∀ i, B i i ∈ (Lambda ε k : Set ℂ))
    (hcomm : A = ⁅B, C⁆ₘ) :
    mu ε k A ≤ ‖C‖ := by
  apply csInf_le
  · exact ⟨0, fun c ⟨_, C', _, _, _, hC'⟩ => le_trans (norm_nonneg _) hC'⟩
  · exact ⟨B, C, hdiag, hlam, hcomm, le_refl _⟩

/-- Hilbert-Schmidt norm of solveC is bounded by hsNorm(A) / δ where δ is
    the minimum separation of the diagonal entries b. -/
private lemma solveC_hsNorm_le_div_sep {m : ℕ} (b : Fin m → ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : Fin m, i ≠ j → δ ≤ ‖b i - b j‖) :
    hsNorm (solveC b A) ≤ hsNorm A / δ := by
  unfold hsNorm
  rw [div_eq_mul_inv,
    show Real.sqrt (∑ i : Fin m, ∑ j : Fin m, Complex.normSq (A i j)) * δ⁻¹ =
      Real.sqrt ((∑ i : Fin m, ∑ j : Fin m, Complex.normSq (A i j)) * δ⁻¹ ^ 2) from by
      rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
        Complex.normSq_nonneg _))), Real.sqrt_sq (inv_nonneg.mpr hδ.le)]]
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro i _
  rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro j _
  simp only [solveC, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp only [ite_true, Complex.normSq_zero]
    exact mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (inv_nonneg.mpr hδ.le) 2)
  · simp only [hij, ite_false, Complex.normSq_div]
    rw [show δ⁻¹ ^ 2 = (δ ^ 2)⁻¹ from inv_pow δ 2]
    exact div_le_div_of_nonneg_left (Complex.normSq_nonneg _)
      (sq_pos_of_pos hδ)
      (by rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ hδ.le (hsep i j hij) 2)

/-- Operator norm of solveC bounded via le_hsNorm and Lambda separation. -/
private lemma solveC_opNorm_le_div_sep {m : ℕ} (b : Fin m → ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : Fin m, i ≠ j → δ ≤ ‖b i - b j‖) :
    ‖solveC b A‖ ≤ hsNorm A / δ :=
  le_trans (le_hsNorm _) (solveC_hsNorm_le_div_sep b A δ hδ hsep)

/-- Distinct elements of Lambda ε n are separated by at least 2·((1-ε)/2)^n.
    Derived from lambda_spectrum_sep via a 2×2 diagonal matrix. -/
private lemma lambda_sep_direct {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (z₁ z₂ : ℂ) (h₁ : z₁ ∈ (Lambda ε n : Set ℂ)) (h₂ : z₂ ∈ (Lambda ε n : Set ℂ))
    (hne : z₁ ≠ z₂) : 2 * ((1 - ε) / 2) ^ n ≤ ‖z₁ - z₂‖ := by
  set B : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![z₁, z₂]
  have hDiag : IsDiagMatrix B := fun i j hij => by simp [B, Matrix.diagonal, hij]
  have hSpec : ∀ i, B i i ∈ (Lambda ε n : Set ℂ) := by
    intro i; fin_cases i <;> simp [B, Matrix.diagonal, *]
  have hBdiag : B.IsDiag := fun i j hij => hDiag i j hij
  have hBeq : Matrix.diagonal B.diag = B := (Matrix.isDiag_iff_diagonal_diag B).mp hBdiag
  have hz₁_spec : z₁ ∈ spectrum ℂ B := by
    rw [← hBeq, spectrum_diagonal]; exact ⟨0, by simp [B, Matrix.diagonal]⟩
  have hz₂_spec : z₂ ∈ spectrum ℂ B := by
    rw [← hBeq, spectrum_diagonal]; exact ⟨1, by simp [B, Matrix.diagonal]⟩
  exact lambda_spectrum_sep ε hε hε1 B hDiag hSpec z₁ hz₁_spec z₂ hz₂_spec hne

/-- Explicit (non-optimal) upper bound on mu via solveC and Lambda separation.
    Shows mu ε (k+1) A ≤ √(4^(k+1)) / (2·((1-ε)/2)^(k+1)) for unit-norm A.
    This proves mu is finite but the bound grows faster than n^ε. -/
private lemma mu_explicit_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ)
    (A : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1) :
    mu ε (k + 1) A ≤
      Real.sqrt ↑(4 ^ (k + 1)) / (2 * ((1 - ε) / 2) ^ (k + 1)) := by
  have hcard : 4 ^ (k + 1) ≤ (Lambda ε (k + 1)).card := Lambda_card_ge ε hε hε1 (k + 1)
  obtain ⟨b, hb_inj, hb_mem⟩ := Lambda_has_distinct_elems ε hε (k + 1) _ hcard
  have hδ : (0 : ℝ) < 2 * ((1 - ε) / 2) ^ (k + 1) :=
    mul_pos (by norm_num : (0:ℝ) < 2) (pow_pos (by linarith : (0:ℝ) < (1 - ε) / 2) _)
  have hsep : ∀ i j : Fin (4 ^ (k + 1)), i ≠ j →
      2 * ((1 - ε) / 2) ^ (k + 1) ≤ ‖b i - b j‖ := fun i j hij =>
    lambda_sep_direct hε hε1 (k + 1) (b i) (b j) (hb_mem i) (hb_mem j) (hb_inj.ne hij)
  calc mu ε (k + 1) A
      ≤ ‖solveC b A‖ :=
        mu_le_witness_norm ε (k + 1) A (Matrix.diagonal b) (solveC b A)
          (fun i j hij => by simp [hij])
          (fun i => by simp only [Matrix.diagonal_apply_eq]; exact hb_mem i)
          (comm_diag_solveC b hb_inj A hzd)
    _ ≤ hsNorm A / (2 * ((1 - ε) / 2) ^ (k + 1)) :=
        solveC_opNorm_le_div_sep b A _ hδ hsep
    _ ≤ (Real.sqrt ↑(4 ^ (k + 1)) * ‖A‖) / (2 * ((1 - ε) / 2) ^ (k + 1)) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hδ)
        convert hsNorm_le_sqrt_n_mul_opNorm A using 2
        push_cast; ring
    _ = Real.sqrt ↑(4 ^ (k + 1)) / (2 * ((1 - ε) / 2) ^ (k + 1)) := by
        rw [hnorm, mul_one]

/-! ## Infrastructure for mu_succ_bound -/

/-- Supremum of mu over zero-diagonal unit-norm matrices of given size and lattice level. -/
private noncomputable def mu_sup' (ε : ℝ) (n : ℕ) (m : ℕ) : ℝ :=
  sSup {y : ℝ | ∃ (A : Matrix (Fin m) (Fin m) ℂ),
    ZeroDiag A ∧ ‖A‖ = 1 ∧ y = mu ε n A}

/-! ### Block decomposition infrastructure for 4^(k+2) = 4 · 4^(k+1) -/

/-- The canonical equivalence `Fin (4^(k+2)) ≃ Fin 4 × Fin (4^(k+1))`,
    viewing the index set as 4 blocks of size 4^(k+1). -/
private def finBlockEquiv (k : ℕ) : Fin (4 ^ (k + 2)) ≃ Fin 4 × Fin (4 ^ (k + 1)) := by
  have h : 4 ^ (k + 2) = 4 * 4 ^ (k + 1) := by ring
  exact (finCongr h).trans finProdFinEquiv.symm

/-- Extract the (i,j)-th block of A under the 4×4 block decomposition.
    The result is a 4^(k+1) × 4^(k+1) matrix. -/
private noncomputable def matBlock {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ)
    (i j : Fin 4) : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ :=
  fun p q => A ((finBlockEquiv k).symm (i, p)) ((finBlockEquiv k).symm (j, q))

/-- The diagonal blocks of a zero-diagonal matrix are zero-diagonal. -/
private lemma matBlock_diag_zeroDiag {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ)
    (hzd : ZeroDiag A) (i : Fin 4) : ZeroDiag (matBlock A i i) := by
  intro p
  exact hzd _

/-- The block embedding matrix P_i : (4^(k+2)) x (4^(k+1)), with columns being
    standard basis vectors corresponding to the i-th block. -/
private noncomputable def blockEmbed (k : ℕ) (i : Fin 4) :
    Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 1))) ℂ :=
  Matrix.of fun r c =>
    if r = (finBlockEquiv k).symm (i, c) then 1 else 0

/-- matBlock A i j = P_i^H A P_j where P_i is the block embedding. -/
private lemma matBlock_eq_product {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ)
    (i j : Fin 4) :
    matBlock A i j =
      (blockEmbed k i).conjTranspose * A * (blockEmbed k j) := by
  ext p q
  simp only [matBlock, Matrix.mul_apply, blockEmbed,
    Matrix.of_apply, Matrix.conjTranspose_apply]
  conv_rhs =>
    arg 2; ext x
    rw [show (∑ x_1,
          star (if x_1 = (finBlockEquiv k).symm (i, p)
            then 1 else 0) * A x_1 x) =
        A ((finBlockEquiv k).symm (i, p)) x from by
      simp [Finset.sum_ite_eq', Finset.mem_univ]]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- The block embedding has orthonormal columns: P_i^H P_i = I. -/
private lemma blockEmbed_conjTranspose_mul_self (k : ℕ)
    (i : Fin 4) :
    (blockEmbed k i).conjTranspose * (blockEmbed k i) = 1 := by
  ext p q
  simp only [Matrix.mul_apply, blockEmbed, Matrix.of_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply]
  conv_lhs =>
    arg 2; ext x
    rw [show star (if x = (finBlockEquiv k).symm (i, p)
            then (1 : ℂ) else 0) *
          (if x = (finBlockEquiv k).symm (i, q)
            then 1 else 0) =
        if x = (finBlockEquiv k).symm (i, p) then
          (if (finBlockEquiv k).symm (i, p) =
              (finBlockEquiv k).symm (i, q)
            then 1 else 0)
        else 0 from by
        split_ifs <;> simp_all]
  rw [Finset.sum_ite_eq' Finset.univ,
    if_pos (Finset.mem_univ _)]
  congr 1; ext
  constructor
  · intro h
    have := (finBlockEquiv k).symm.injective h
    exact (Prod.mk.inj this).2
  · intro h; subst h; rfl

private lemma l2_opNorm_one_eq {k : ℕ} :
    ‖(1 : Matrix (Fin (4 ^ (k + 1)))
      (Fin (4 ^ (k + 1))) ℂ)‖ = 1 := by
  rw [Matrix.l2_opNorm_def]
  have : (Matrix.toEuclideanLin ≪≫ₗ
      LinearMap.toContinuousLinearMap)
      (1 : Matrix (Fin (4 ^ (k + 1)))
        (Fin (4 ^ (k + 1))) ℂ) =
      ContinuousLinearMap.id ℂ _ := by
    ext x; simp [Matrix.toEuclideanLin]
  rw [this]
  haveI : Nontrivial (Fin (4 ^ (k + 1))) :=
    ⟨⟨⟨0, by positivity⟩,
      ⟨1, by
        have := Nat.one_le_pow (k + 1) 4 (by norm_num)
        omega⟩,
      by simp [Fin.ext_iff]⟩⟩
  exact ContinuousLinearMap.norm_id

private lemma blockEmbed_norm_le_one (k : ℕ)
    (i : Fin 4) : ‖blockEmbed k i‖ ≤ 1 := by
  have h1 :=
    Matrix.l2_opNorm_conjTranspose_mul_self (blockEmbed k i)
  rw [blockEmbed_conjTranspose_mul_self,
    l2_opNorm_one_eq] at h1
  have hnn := norm_nonneg (blockEmbed k i)
  nlinarith [sq_nonneg (‖blockEmbed k i‖ - 1)]

/-- The operator norm of each block is at most the operator
    norm of the full matrix. -/
private lemma matBlock_norm_le {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ)
    (i j : Fin 4) : ‖matBlock A i j‖ ≤ ‖A‖ := by
  rw [matBlock_eq_product]
  calc ‖(blockEmbed k i).conjTranspose * A *
        blockEmbed k j‖
      ≤ ‖(blockEmbed k i).conjTranspose * A‖ *
          ‖blockEmbed k j‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ ‖(blockEmbed k i).conjTranspose‖ * ‖A‖ *
          ‖blockEmbed k j‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact Matrix.l2_opNorm_mul _ _
        · exact norm_nonneg _
    _ = ‖blockEmbed k i‖ * ‖A‖ *
          ‖blockEmbed k j‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]
    _ ≤ 1 * ‖A‖ * 1 := by
        apply mul_le_mul
          (mul_le_mul_of_nonneg_right
            (blockEmbed_norm_le_one k i) (norm_nonneg _))
          (blockEmbed_norm_le_one k j)
          (norm_nonneg _) (by positivity)
    _ = ‖A‖ := by ring

/-- The set defining mu_sup' is BddAbove. -/
private lemma mu_sup_bddAbove' (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
    BddAbove {y : ℝ | ∃ (A : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ),
      ZeroDiag A ∧ ‖A‖ = 1 ∧ y = mu ε (k + 1) A} := by
  use Real.sqrt ↑(4 ^ (k + 1)) / (2 * ((1 - ε) / 2) ^ (k + 1))
  intro y hy
  obtain ⟨A, hzd, hnorm, rfl⟩ := hy
  exact mu_explicit_bound ε hε hε1 k A hzd hnorm

/-- mu ε (k+1) A ≤ mu_sup' for unit-norm zero-diagonal A. -/
private lemma mu_le_mu_sup' (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ)
    (A : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1) :
    mu ε (k + 1) A ≤ mu_sup' ε (k + 1) (4 ^ (k + 1)) := by
  unfold mu_sup'
  exact le_csSup (mu_sup_bddAbove' ε hε hε1 k) ⟨A, hzd, hnorm, rfl⟩

/-! ### Block-diagonal witness construction for the one-step bound -/

/-- Assign a corner point δ_i ∈ cornerSet to each index i ∈ Fin 4. -/
private noncomputable def cornerOf : Fin 4 → ℂ
  | ⟨0, _⟩ => ⟨1, 1⟩
  | ⟨1, _⟩ => ⟨1, -1⟩
  | ⟨2, _⟩ => ⟨-1, 1⟩
  | ⟨3, _⟩ => ⟨-1, -1⟩

private lemma cornerOf_mem (i : Fin 4) : cornerOf i ∈ cornerSet := by
  fin_cases i <;> simp [cornerOf, cornerSet, Finset.mem_insert]

/-- Block-diagonal B: entry at index r is ((1-ε)/2) * Bs_i(p,p) + corner_i
    where (i,p) = finBlockEquiv k r. Off-diagonal entries are 0. -/
private noncomputable def fullB {k : ℕ} (ε : ℝ)
    (Bs : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ) :
    Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ :=
  fun r c =>
    let ri := (finBlockEquiv k) r
    let ci := (finBlockEquiv k) c
    if ri.1 = ci.1 ∧ ri.2 = ci.2 then
      ((1 - ε) / 2 : ℂ) * (Bs ri.1 ri.2 ri.2) + cornerOf ri.1
    else 0

private lemma fullB_isDiag {k : ℕ} (ε : ℝ)
    (Bs : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (_hBs : ∀ i, IsDiagMatrix (Bs i)) :
    IsDiagMatrix (fullB ε Bs) := by
  intro r c hrc
  simp only [fullB]
  split_ifs with h
  · exfalso; apply hrc
    have : (finBlockEquiv k) r = (finBlockEquiv k) c := Prod.ext h.1 h.2
    exact (finBlockEquiv k).injective this
  · rfl

private lemma fullB_diag_entry {k : ℕ} (ε : ℝ)
    (Bs : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (r : Fin (4 ^ (k + 2))) :
    fullB ε Bs r r =
      ((1 - ε) / 2 : ℂ) *
        (Bs ((finBlockEquiv k r).1) ((finBlockEquiv k r).2)
             ((finBlockEquiv k r).2)) +
      cornerOf (finBlockEquiv k r).1 := by
  simp [fullB]

/-- Entries of fullB are in Lambda ε (k+2). -/
private lemma fullB_entries_in_lambda {k : ℕ} (ε : ℝ)
    (Bs : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (hBs_lam : ∀ i j, (Bs i) j j ∈ (Lambda ε (k + 1) : Set ℂ)) :
    ∀ r, fullB ε Bs r r ∈ (Lambda ε (k + 2) : Set ℂ) := by
  intro r
  rw [fullB_diag_entry]
  set i := (finBlockEquiv k r).1
  set p := (finBlockEquiv k r).2
  have hz : (Bs i) p p ∈ (Lambda ε (k + 1) : Set ℂ) := hBs_lam i p
  have hδ : cornerOf i ∈ cornerSet := cornerOf_mem i
  change ((1 - ↑ε) / 2 : ℂ) * (Bs i) p p + cornerOf i ∈
    (Lambda ε (k + 2) : Set ℂ)
  have hk2 : k + 2 = (k + 1) + 1 := by omega
  rw [hk2, Lambda]
  simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image]
  exact ⟨cornerOf i, hδ, (Bs i) p p, hz, rfl⟩

/-- Block-diagonal C scaled by 2/(1-ε) to compensate for the (1-ε)/2 factor in fullB. -/
private noncomputable def blockDiagC {k : ℕ} (ε : ℝ)
    (Cs : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ) :
    Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ :=
  fun r c =>
    let ri := (finBlockEquiv k) r
    let ci := (finBlockEquiv k) c
    if ri.1 = ci.1 then
      (2 / (1 - ε) : ℂ) * (Cs ri.1 ri.2 ci.2)
    else 0

/-- Off-diagonal part of A (cross-block entries only). -/
private noncomputable def offDiagBlocks {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ) :
    Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ :=
  fun r c =>
    let ri := (finBlockEquiv k) r
    let ci := (finBlockEquiv k) c
    if ri.1 = ci.1 then 0 else A r c

/-- For a zero-diagonal matrix with ‖Aii‖ ≤ 1 and any η > 0, there exist Bi, Ci
    with Aii = [Bi, Ci], Bi diagonal with Lambda entries, ‖Ci‖ ≤ mu_sup' + η. -/
private lemma block_decomp_approx (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ)
    (Aii : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (hzd : ZeroDiag Aii) (hnorm_le : ‖Aii‖ ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    ∃ (Bi Ci : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ),
      IsDiagMatrix Bi ∧
      (∀ j, Bi j j ∈ (Lambda ε (k + 1) : Set ℂ)) ∧
      Aii = ⁅Bi, Ci⁆ₘ ∧
      ‖Ci‖ ≤ mu_sup' ε (k + 1) (4 ^ (k + 1)) + η := by
  have hcard : 4 ^ (k + 1) ≤ (Lambda ε (k + 1)).card :=
    Lambda_card_ge ε hε hε1 (k + 1)
  by_cases hAii : ‖Aii‖ = 0
  · -- Case ‖Aii‖ = 0: Aii = 0, take C = 0
    have hAii_zero : Aii = 0 := by rwa [norm_eq_zero] at hAii
    obtain ⟨Bi, Ci, hd, hl, hcomm⟩ := mu_set_nonempty ε hε (k + 1) Aii hzd hcard
    refine ⟨Bi, 0, hd, hl, ?_, ?_⟩
    · rw [hAii_zero]; simp [matComm]
    · simp only [norm_zero]
      have hmsup_nn : 0 ≤ mu_sup' ε (k + 1) (4 ^ (k + 1)) := by
        unfold mu_sup'
        by_cases hne : {y : ℝ | ∃ (A : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ),
            ZeroDiag A ∧ ‖A‖ = 1 ∧ y = mu ε (k + 1) A}.Nonempty
        · obtain ⟨_, A', hzd', hnorm', rfl⟩ := hne
          exact le_csSup_of_le (mu_sup_bddAbove' ε hε hε1 k)
            ⟨A', hzd', hnorm', rfl⟩ (mu_nonneg ε (k + 1) A')
        · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
      linarith
  · -- Case ‖Aii‖ > 0: normalize, use mu_le_mu_sup, extract witness, scale back
    have hAii_pos : 0 < ‖Aii‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hAii)
    set t := ‖Aii‖ with ht_def
    set A' := (t⁻¹ : ℂ) • Aii with hA'_def
    have hA'_norm : ‖A'‖ = 1 := by
      rw [hA'_def, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (le_of_lt hAii_pos), inv_mul_cancel₀ hAii]
    have hA'_zd : ZeroDiag A' := by
      intro i; simp [hA'_def, Matrix.smul_apply, hzd i]
    -- mu(A') ≤ mu_sup'
    have hmu_le : mu ε (k + 1) A' ≤ mu_sup' ε (k + 1) (4 ^ (k + 1)) :=
      mu_le_mu_sup' ε hε hε1 k A' hA'_zd hA'_norm
    -- Extract witness for A' with norm ≤ mu_sup' + η
    obtain ⟨Bi, Ci', hd, hl, hcomm', hnorm_ci⟩ :=
      mu_extract_witness hε hA'_zd hcard hmu_le η hη
    -- Scale back: Aii = t • A' = [Bi, t • Ci']
    refine ⟨Bi, (t : ℂ) • Ci', hd, hl, ?_, ?_⟩
    · -- Aii = [Bi, t • Ci']
      have : Aii = (t : ℂ) • A' := by
        rw [hA'_def, smul_smul]
        simp [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hAii_pos))]
      rw [this, hcomm']
      simp only [matComm, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    · -- ‖t • Ci'‖ = t * ‖Ci'‖ ≤ 1 * (mu_sup' + η) = mu_sup' + η
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hAii_pos)]
      calc t * ‖Ci'‖ ≤ 1 * (mu_sup' ε (k + 1) (4 ^ (k + 1)) + η) := by
            apply mul_le_mul hnorm_le hnorm_ci (norm_nonneg _) (by linarith)
        _ = mu_sup' ε (k + 1) (4 ^ (k + 1)) + η := one_mul _

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- Norm of blockDiagC ≤ 2/(1-ε) * bound when each ‖Cs i‖ ≤ bound. -/
private lemma blockDiagC_norm_le {k : ℕ} (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (Cs : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (bound : ℝ)
    (hCs : ∀ i, ‖Cs i‖ ≤ bound) :
    ‖blockDiagC ε Cs‖ ≤ 2 / (1 - ε) * bound := by
  have hbd_nn : 0 ≤ bound := le_trans (norm_nonneg (Cs 0)) (hCs 0)
  have h1eps_r : (0 : ℝ) < 1 - ε := by linarith
  have hcoeff_nn : (0 : ℝ) ≤ 2 / (1 - ε) := div_nonneg (by norm_num) (le_of_lt h1eps_r)
  have hscale_val : ‖(2 / (1 - ε) : ℂ)‖ = 2 / (1 - ε) := by
    have h2c : (2 : ℂ) / (1 - ε) = ((2 / (1 - ε) : ℝ) : ℂ) := by push_cast; ring
    rw [h2c]
    simp only [Complex.norm_real]
    exact abs_of_pos (div_pos (by norm_num : (0:ℝ) < 2) h1eps_r)
  -- Express blockDiagC as scalar smul of unscaled block-diagonal M
  let M : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ :=
    fun r c =>
      let ri := (finBlockEquiv k) r
      let ci := (finBlockEquiv k) c
      if ri.1 = ci.1 then Cs ri.1 ri.2 ci.2 else 0
  have hscale : blockDiagC ε Cs = (2 / (1 - ε) : ℂ) • M := by
    ext r c; simp only [blockDiagC, Matrix.smul_apply, smul_eq_mul, M]
    split <;> simp
  rw [hscale, norm_smul, hscale_val]
  apply mul_le_mul_of_nonneg_left _ hcoeff_nn
  -- Block-diagonal norm bound: ‖M‖ ≤ bound via EuclideanSpace decomposition
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hbd_nn
  intro x
  change ‖Matrix.toEuclideanLin M x‖ ≤ bound * ‖x‖
  rw [show Matrix.toEuclideanLin M x = WithLp.toLp 2 (M.mulVec x.ofLp) from
    Matrix.toLpLin_apply 2 2 M x]
  set v := x.ofLp with hv_def
  let vB (i : Fin 4) : Fin (4 ^ (k + 1)) → ℂ :=
    fun j => v ((finBlockEquiv k).symm (i, j))
  have hw_entry : ∀ r, M.mulVec v r =
      (Cs ((finBlockEquiv k) r).1).mulVec
        (vB ((finBlockEquiv k) r).1)
        ((finBlockEquiv k) r).2 := by
    intro r
    simp only [Matrix.mulVec, dotProduct, M]
    rw [← Equiv.sum_comp (finBlockEquiv k).symm]
    simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
    simp only [show ∀ (i' : Fin 4) (j' : Fin (4 ^ (k + 1))),
      (if ((finBlockEquiv k) r).1 = i'
        then Cs ((finBlockEquiv k) r).1 ((finBlockEquiv k) r).2 j' else 0) *
        v ((finBlockEquiv k).symm (i', j')) =
      if ((finBlockEquiv k) r).1 = i'
        then Cs ((finBlockEquiv k) r).1 ((finBlockEquiv k) r).2 j' * vB i' j' else 0
      from fun i' j' => by split <;> simp [vB]]
    conv_lhs =>
      arg 2; ext i'
      rw [show ∑ j', (if ((finBlockEquiv k) r).1 = i'
            then Cs ((finBlockEquiv k) r).1 ((finBlockEquiv k) r).2 j' * vB i' j' else 0) =
          if ((finBlockEquiv k) r).1 = i'
            then ∑ j', Cs ((finBlockEquiv k) r).1 ((finBlockEquiv k) r).2 j' * vB i' j' else 0
        from by split <;> simp]
    simp
  apply le_of_sq_le_sq _ (mul_nonneg hbd_nn (norm_nonneg x))
  have hlhs : ‖(WithLp.toLp 2 (M.mulVec v) : EuclideanSpace ℂ (Fin (4 ^ (k + 2))))‖ ^ 2 =
      ∑ r, ‖(M.mulVec v) r‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
  have hrhs : (bound * ‖x‖) ^ 2 = bound ^ 2 * ∑ r, ‖v r‖ ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_eq x,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
  rw [hlhs, hrhs]
  conv_lhs => rw [show ∑ r, ‖(M.mulVec v) r‖ ^ 2 =
    ∑ p : Fin 4 × Fin (4 ^ (k + 1)), ‖(M.mulVec v) ((finBlockEquiv k).symm p)‖ ^ 2 from by
      rw [← Equiv.sum_comp (finBlockEquiv k).symm]]
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ (i : Fin 4) (j : Fin (4 ^ (k + 1))),
    ‖(M.mulVec v) ((finBlockEquiv k).symm (i, j))‖ =
    ‖(Cs i).mulVec (vB i) j‖ from fun i j => by
      rw [hw_entry]; simp [Equiv.apply_symm_apply]]
  conv_rhs => rw [show ∑ r, ‖v r‖ ^ 2 =
    ∑ p : Fin 4 × Fin (4 ^ (k + 1)), ‖v ((finBlockEquiv k).symm p)‖ ^ 2 from by
      rw [← Equiv.sum_comp (finBlockEquiv k).symm]]
  rw [Fintype.sum_prod_type (fun p => ‖v ((finBlockEquiv k).symm p)‖ ^ 2)]
  have hblock : ∀ i : Fin 4,
      ∑ j, ‖(Cs i).mulVec (vB i) j‖ ^ 2 ≤
      bound ^ 2 * ∑ j, ‖vB i j‖ ^ 2 := by
    intro i
    set xi := (EuclideanSpace.equiv (Fin (4 ^ (k + 1))) ℂ).symm (vB i) with hxi_def
    have hle : ‖(EuclideanSpace.equiv _ ℂ).symm ((Cs i).mulVec (vB i))‖ ≤ bound * ‖xi‖ :=
      calc _ ≤ ‖Cs i‖ * ‖xi‖ := Matrix.l2_opNorm_mulVec (Cs i) xi
        _ ≤ bound * ‖xi‖ := mul_le_mul_of_nonneg_right (hCs i) (norm_nonneg _)
    have hle_sq : ‖(EuclideanSpace.equiv _ ℂ).symm ((Cs i).mulVec (vB i))‖ ^ 2 ≤
        (bound * ‖xi‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) 2))] at hle_sq
    rw [mul_pow, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) 2))] at hle_sq
    convert hle_sq using 2
  calc ∑ i : Fin 4, ∑ j, ‖(Cs i).mulVec (vB i) j‖ ^ 2
      ≤ ∑ i : Fin 4, bound ^ 2 * ∑ j, ‖vB i j‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => hblock i)
    _ = bound ^ 2 * ∑ i : Fin 4, ∑ j, ‖vB i j‖ ^ 2 := by rw [← Finset.mul_sum]

/-- The diagonal-blocks part of A (keeps only entries within same block). -/
private noncomputable def diagBlocksPart {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ) :
    Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ :=
  fun r c =>
    let ri := (finBlockEquiv k) r
    let ci := (finBlockEquiv k) c
    if ri.1 = ci.1 then A r c else 0

/-- offDiagBlocks A = A - diagBlocksPart A. -/
private lemma offDiagBlocks_eq_sub {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ) :
    offDiagBlocks A = A - diagBlocksPart A := by
  ext r c
  simp only [offDiagBlocks, diagBlocksPart, Matrix.sub_apply]
  split_ifs with h
  · simp
  · simp

/-- Norm of the diagonal-blocks part ≤ ‖A‖.

The proof works as follows: diagBlocksPart A acts block-diagonally. Decompose any
vector v = Σ_i Q_i v where Q_i projects onto the i-th block subspace. Then
(diagBlocksPart A) v = Σ_i Q_i (A (Q_i v)), so by Pythagorean theorem on the
orthogonal block subspaces:
  ‖(diagBlocksPart A) v‖² = Σ_i ‖Q_i (A (Q_i v))‖² ≤ Σ_i ‖A (Q_i v)‖²
  ≤ Σ_i ‖A‖² ‖Q_i v‖² = ‖A‖² ‖v‖². -/
private lemma diagBlocksPart_norm_le {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ) :
    ‖diagBlocksPart A‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simp only [LinearEquiv.trans_apply]
  change ‖Matrix.toEuclideanLin (diagBlocksPart A) x‖ ≤ ‖A‖ * ‖x‖
  rw [show Matrix.toEuclideanLin (diagBlocksPart A) x =
      WithLp.toLp 2 ((diagBlocksPart A).mulVec x.ofLp) from
    Matrix.toLpLin_apply 2 2 (diagBlocksPart A) x]
  set w := x.ofLp
  set Qw : Fin 4 → (Fin (4 ^ (k + 2)) → ℂ) :=
    fun i r => if ((finBlockEquiv k) r).1 = i then w r else 0 with hQw_def
  have hentry : ∀ r,
      ((diagBlocksPart A).mulVec w) r =
        (A.mulVec (Qw ((finBlockEquiv k) r).1)) r := by
    intro r
    simp only [Matrix.mulVec, dotProduct, diagBlocksPart, hQw_def]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : ((finBlockEquiv k) r).1 = ((finBlockEquiv k) c).1
    · simp [h]
    · simp [h, show ¬((finBlockEquiv k) c).1 = ((finBlockEquiv k) r).1 from
        fun h' => h h'.symm]
  apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2)),
      mul_pow]
  have hstep1 :
      ∑ r, ‖(A.mulVec (Qw ((finBlockEquiv k) r).1)) r‖ ^ 2 ≤
      ∑ i : Fin 4, ∑ r, ‖(A.mulVec (Qw i)) r‖ ^ 2 := by
    calc ∑ r, ‖(A.mulVec (Qw ((finBlockEquiv k) r).1)) r‖ ^ 2
        ≤ ∑ r, ∑ i : Fin 4, ‖(A.mulVec (Qw i)) r‖ ^ 2 :=
          Finset.sum_le_sum fun r _ =>
            Finset.single_le_sum
              (f := fun i => ‖(A.mulVec (Qw i)) r‖ ^ 2)
              (fun i _ => pow_nonneg (norm_nonneg _) 2)
              (Finset.mem_univ ((finBlockEquiv k) r).1)
      _ = ∑ i : Fin 4, ∑ r, ‖(A.mulVec (Qw i)) r‖ ^ 2 := Finset.sum_comm
  have hstep2 : ∀ i : Fin 4,
      ∑ r, ‖(A.mulVec (Qw i)) r‖ ^ 2 ≤
      ‖A‖ ^ 2 * (∑ r, ‖(Qw i) r‖ ^ 2) := by
    intro i
    set qi : EuclideanSpace ℂ (Fin (4 ^ (k + 2))) := WithLp.toLp 2 (Qw i)
    have hAmv := Matrix.l2_opNorm_mulVec A qi
    have hAmv_sq := pow_le_pow_left₀ (norm_nonneg _) hAmv 2
    rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun r _ => pow_nonneg (norm_nonneg _) 2)),
        mul_pow] at hAmv_sq
    calc ∑ r, ‖(A.mulVec (Qw i)) r‖ ^ 2
        = ∑ r, ‖((EuclideanSpace.equiv (Fin (4 ^ (k + 2))) ℂ).symm
            (A.mulVec qi.ofLp)).ofLp r‖ ^ 2 := by rfl
      _ ≤ ‖A‖ ^ 2 * ‖qi‖ ^ 2 := hAmv_sq
      _ = ‖A‖ ^ 2 * (∑ r, ‖qi.ofLp r‖ ^ 2) := by
          rw [EuclideanSpace.norm_eq,
              Real.sq_sqrt (Finset.sum_nonneg
                (fun r _ => pow_nonneg (norm_nonneg _) 2))]
      _ = ‖A‖ ^ 2 * (∑ r, ‖(Qw i) r‖ ^ 2) := by rfl
  have hstep3 :
      ∑ i : Fin 4, ∑ r, ‖(Qw i) r‖ ^ 2 = ∑ r, ‖w r‖ ^ 2 := by
    simp_rw [show ∀ i : Fin 4, ∑ r, ‖(Qw i) r‖ ^ 2 =
        ∑ r, (if ((finBlockEquiv k) r).1 = i then ‖w r‖ ^ 2 else 0) from
      fun i => by congr 1; ext r; simp [hQw_def]; split_ifs <;> simp]
    rw [Finset.sum_comm]
    congr 1; ext r
    rw [show ∑ x : Fin 4, (if ((finBlockEquiv k) r).1 = x then ‖w r‖ ^ 2 else 0) =
        ∑ x : Fin 4, (if x = ((finBlockEquiv k) r).1 then ‖w r‖ ^ 2 else 0) from by
      congr 1; ext i; simp [eq_comm]]
    rw [Finset.sum_ite_eq' Finset.univ ((finBlockEquiv k) r).1
      (fun _ => ‖w r‖ ^ 2)]
    simp
  calc ∑ r, ‖(WithLp.toLp 2 ((diagBlocksPart A).mulVec w) :
          EuclideanSpace ℂ (Fin (4 ^ (k + 2)))).ofLp r‖ ^ 2
      = ∑ r, ‖((diagBlocksPart A).mulVec w) r‖ ^ 2 := by rfl
    _ = ∑ r, ‖(A.mulVec (Qw ((finBlockEquiv k) r).1)) r‖ ^ 2 := by
        congr 1; ext r; rw [hentry]
    _ ≤ ∑ i : Fin 4, ∑ r, ‖(A.mulVec (Qw i)) r‖ ^ 2 := hstep1
    _ ≤ ∑ i : Fin 4, (‖A‖ ^ 2 * ∑ r, ‖(Qw i) r‖ ^ 2) :=
        Finset.sum_le_sum (fun i _ => hstep2 i)
    _ = ‖A‖ ^ 2 * ∑ i : Fin 4, ∑ r, ‖(Qw i) r‖ ^ 2 := by rw [← Finset.mul_sum]
    _ = ‖A‖ ^ 2 * ∑ r, ‖w r‖ ^ 2 := by rw [hstep3]
    _ = ‖A‖ ^ 2 * ∑ r, ‖x.ofLp r‖ ^ 2 := by rfl
    _ = ‖A‖ ^ 2 * ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq,
            Real.sq_sqrt (Finset.sum_nonneg
              (fun r _ => pow_nonneg (norm_nonneg _) 2))]

/-- Norm of off-diagonal blocks ≤ 2 * ‖A‖. -/
private lemma offDiagBlocks_norm_le {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ) :
    ‖offDiagBlocks A‖ ≤ 2 * ‖A‖ := by
  have h1 := offDiagBlocks_eq_sub A
  rw [h1]
  calc ‖A - diagBlocksPart A‖
      ≤ ‖A‖ + ‖diagBlocksPart A‖ := norm_sub_le A (diagBlocksPart A)
    _ ≤ ‖A‖ + ‖A‖ := by linarith [diagBlocksPart_norm_le A]
    _ = 2 * ‖A‖ := by ring

/-- Helper: Schur-multiplier operator-norm bound with 4-way Re/Im separation.
    If diagonal matrices `S, T` have `δ` separation in any of `(S-T).re`, `(S-T).im`,
    `(T-S).re`, `(T-S).im`, then the entrywise division
    `X(p,q) = A(p,q) / (S_pp - T_qq)` satisfies `‖X‖ ≤ ‖A‖ / δ`. -/
private lemma schur_div_op_norm_bound_4way {m : ℕ}
    (S T A : Matrix (Fin m) (Fin m) ℂ)
    (hS : IsDiagMatrix S) (hT : IsDiagMatrix T)
    (δ : ℝ) (hδ : 0 < δ)
    (hSep : (∀ p q, δ ≤ (S p p - T q q).re) ∨
            (∀ p q, δ ≤ (S p p - T q q).im) ∨
            (∀ p q, δ ≤ (T q q - S p p).re) ∨
            (∀ p q, δ ≤ (T q q - S p p).im)) :
    ‖(Matrix.of fun p q => A p q / (S p p - T q q) :
      Matrix (Fin m) (Fin m) ℂ)‖ ≤ ‖A‖ / δ := by
  -- Define X explicitly, identify with the Sylvester solution, conclude.
  set X : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.of fun p q => A p q / (S p p - T q q) with hX_def
  rcases hSep with h1 | h2 | h3 | h4
  · -- Direct: δ ≤ (S - T).re
    have hbnd := sylvester_diag_opNorm_bound_re_or_im S T A hS hT δ hδ (Or.inl h1)
    -- The Sylvester X is `fun p q => A p q / (S p p - T q q)`, same as our X
    have : X = (fun p q => A p q / (S p p - T q q)) := rfl
    rw [this]
    exact hbnd.2
  · -- Direct: δ ≤ (S - T).im
    have hbnd := sylvester_diag_opNorm_bound_re_or_im S T A hS hT δ hδ (Or.inr h2)
    have : X = (fun p q => A p q / (S p p - T q q)) := rfl
    rw [this]
    exact hbnd.2
  · -- Swap: δ ≤ (T - S).re. Apply Sylvester to (-S, -T, -A); X formula is the same.
    have hSn : IsDiagMatrix (-S) := fun i j h => by simp [hS i j h]
    have hTn : IsDiagMatrix (-T) := fun i j h => by simp [hT i j h]
    have hsep_neg : ∀ p q, δ ≤ ((-S) p p - (-T) q q).re := by
      intro p q
      have := h3 p q
      simp only [Matrix.neg_apply]
      rw [show (-S p p - -T q q).re = (T q q - S p p).re from by
        simp [Complex.sub_re, Complex.neg_re]; ring]
      exact this
    have hbnd := sylvester_diag_opNorm_bound_re_or_im (-S) (-T) (-A)
      hSn hTn δ hδ (Or.inl hsep_neg)
    -- Sylvester X' = fun p q => (-A) p q / ((-S) p p - (-T) q q) = A p q / (S p p - T q q)
    -- Define X' as Matrix.of to preserve the Matrix type instance
    set X' : Matrix (Fin m) (Fin m) ℂ :=
      Matrix.of fun p q => (-A) p q / ((-S) p p - (-T) q q) with hX'_def
    have hbnd_norm : ‖X'‖ ≤ ‖-A‖ / δ := hbnd.2
    have hX_eq : X = X' := by
      ext p q
      simp only [hX_def, hX'_def, Matrix.of_apply, Matrix.neg_apply]
      have hsub : -S p p - -T q q = -(S p p - T q q) := by ring
      rw [hsub, neg_div_neg_eq]
    rw [hX_eq]
    calc ‖X'‖
        ≤ ‖-A‖ / δ := hbnd_norm
      _ = ‖A‖ / δ := by rw [norm_neg]
  · -- Swap: δ ≤ (T - S).im. Same as above with Im.
    have hSn : IsDiagMatrix (-S) := fun i j h => by simp [hS i j h]
    have hTn : IsDiagMatrix (-T) := fun i j h => by simp [hT i j h]
    have hsep_neg : ∀ p q, δ ≤ ((-S) p p - (-T) q q).im := by
      intro p q
      have := h4 p q
      simp only [Matrix.neg_apply]
      rw [show (-S p p - -T q q).im = (T q q - S p p).im from by
        simp [Complex.sub_im, Complex.neg_im]; ring]
      exact this
    have hbnd := sylvester_diag_opNorm_bound_re_or_im (-S) (-T) (-A)
      hSn hTn δ hδ (Or.inr hsep_neg)
    set X' : Matrix (Fin m) (Fin m) ℂ :=
      Matrix.of fun p q => (-A) p q / ((-S) p p - (-T) q q) with hX'_def
    have hbnd_norm : ‖X'‖ ≤ ‖-A‖ / δ := hbnd.2
    have hX_eq : X = X' := by
      ext p q
      simp only [hX_def, hX'_def, Matrix.of_apply, Matrix.neg_apply]
      have hsub : -S p p - -T q q = -(S p p - T q q) := by ring
      rw [hsub, neg_div_neg_eq]
    rw [hX_eq]
    calc ‖X'‖
        ≤ ‖-A‖ / δ := hbnd_norm
      _ = ‖A‖ / δ := by rw [norm_neg]

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- Schur multiplier norm bound for the cross-block division construction.
    Given a diagonal matrix D (block-structured with 4 blocks around different corners)
    and a cross-block matrix A, the entrywise solution C(r,c) = A(r,c)/(D(r,r)-D(c,c))
    satisfies ‖C‖ ≤ (2√2/ε) * ‖A‖.
    This is the quantitative content of Rosenblum's theorem applied to the paving
    construction. -/
private lemma cross_block_schur_div_bound {k : ℕ}
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (Bs : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (hBs_diag : ∀ i, IsDiagMatrix (Bs i))
    (hBs_lam : ∀ i j, (Bs i) j j ∈ (Lambda ε (k + 1) : Set ℂ))
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ)
    (hA_cross : ∀ r c, (finBlockEquiv k r).1 = (finBlockEquiv k c).1 → A r c = 0)
    (C : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ)
    (hC_same : ∀ r c, (finBlockEquiv k r).1 = (finBlockEquiv k c).1 → C r c = 0)
    (hComm : ⁅fullB ε Bs, C⁆ₘ = A) :
    ‖C‖ ≤ 2 * Real.sqrt 2 / ε * ‖A‖ := by
  -- Setup: e := finBlockEquiv k
  set e := finBlockEquiv k with he_def
  -- fullB is diagonal: off-diag entries are zero
  have fullB_off : ∀ r c, r ≠ c → fullB ε Bs r c = 0 := by
    intro r c hrc; simp only [fullB]
    split_ifs with h
    · exfalso; apply hrc; exact e.injective (Prod.ext h.1 h.2)
    · rfl
  -- Key entrywise identity from hComm: for all r, c,
  -- (fullB(r,r) - fullB(c,c)) * C(r,c) = A(r,c)
  have hentry : ∀ r c,
      (fullB ε Bs r r - fullB ε Bs c c) * C r c = A r c := by
    intro r c
    have := congr_fun (congr_fun hComm r) c
    simp only [matComm, Matrix.sub_apply, Matrix.mul_apply] at this
    have sum1 : ∑ x, fullB ε Bs r x * C x c = fullB ε Bs r r * C r c := by
      rw [Finset.sum_eq_single r]
      · intro x _ hxr; rw [fullB_off r x (Ne.symm hxr), zero_mul]
      · intro hr; exact absurd (Finset.mem_univ r) hr
    have sum2 : ∑ x, C r x * fullB ε Bs x c = C r c * fullB ε Bs c c := by
      rw [Finset.sum_eq_single c]
      · intro x _ hxc; rw [fullB_off x c hxc, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ c) hc
    rw [sum1, sum2] at this
    linear_combination this
  -- Define block submatrices
  set Cblk : Fin 4 × Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ :=
    fun p => Matrix.of fun i j => C (e.symm (p.1, i)) (e.symm (p.2, j)) with hCblk_def
  set Ablk : Fin 4 × Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ :=
    fun p => Matrix.of fun i j => A (e.symm (p.1, i)) (e.symm (p.2, j)) with hAblk_def
  -- Diagonal blocks of C are zero
  have hCblk_diag_zero : ∀ α : Fin 4, Cblk (α, α) = 0 := by
    intro α
    ext i j
    simp only [Cblk, Matrix.of_apply, Matrix.zero_apply]
    apply hC_same
    show (e (e.symm (α, i))).1 = (e (e.symm (α, j))).1
    rw [e.apply_symm_apply, e.apply_symm_apply]
  -- Si α: diagonal of fullB on block α
  set Si : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ :=
    fun α => Matrix.diagonal (fun p => fullB ε Bs (e.symm (α, p)) (e.symm (α, p))) with hSi_def
  have hSi_diag : ∀ α, IsDiagMatrix (Si α) := fun α => diag_isDiagMatrix _
  have hSi_entry : ∀ α p, Si α p p =
      fullB ε Bs (e.symm (α, p)) (e.symm (α, p)) := by
    intro α p; simp [Si]
  -- Compute the entry equation: (Si α p p - Si β q q) * Cblk(α,β)(p,q) = Ablk(α,β)(p,q)
  have hblk_eq : ∀ α β : Fin 4, ∀ p q,
      (Si α p p - Si β q q) * Cblk (α, β) p q = Ablk (α, β) p q := by
    intro α β p q
    rw [hSi_entry, hSi_entry]
    simp only [Cblk, Ablk, Matrix.of_apply]
    exact hentry _ _
  -- For α ≠ β, the separation holds: 2ε ≤ separation
  have h2ε_pos : (0 : ℝ) < 2 * ε := by linarith
  have hsep_4way : ∀ α β : Fin 4, α ≠ β →
      (∀ p q, 2 * ε ≤ (Si α p p - Si β q q).re) ∨
      (∀ p q, 2 * ε ≤ (Si α p p - Si β q q).im) ∨
      (∀ p q, 2 * ε ≤ (Si β q q - Si α p p).re) ∨
      (∀ p q, 2 * ε ≤ (Si β q q - Si α p p).im) := by
    intro α β hαβ
    -- Reuse the argument inside offdiag_block_sylvester_bound; we already have
    -- the proof structure as suffices step there. Inline via fullB_cross_block_sep.
    have cornerOf_re_pm1 : ∀ (m : Fin 4), (cornerOf m).re = 1 ∨ (cornerOf m).re = -1 := by
      intro m; fin_cases m <;> simp [cornerOf]
    have cornerOf_im_pm1 : ∀ (m : Fin 4), (cornerOf m).im = 1 ∨ (cornerOf m).im = -1 := by
      intro m; fin_cases m <;> simp [cornerOf]
    have cornerOf_inj : Function.Injective cornerOf := by
      intro a b h; fin_cases a <;> fin_cases b <;>
        first | rfl | (exfalso; simp [cornerOf] at h; norm_num at h)
    have hδ_ne : cornerOf α ≠ cornerOf β := fun h => hαβ (cornerOf_inj h)
    have hr_nn : (0 : ℝ) ≤ (1 - ε) / 2 := by linarith
    have h1ε_pos : (0 : ℝ) < 1 + ε := by linarith
    have h1ε_pos2 : (0 : ℝ) < (1 + ε) / 2 := by linarith
    have hBs_re : ∀ (m : Fin 4) (p : Fin (4 ^ (k + 1))),
        |(Bs m p p).re| ≤ 2 / (1 + ε) := by
      intro m p
      have habs := Lambda_abs_re_le hε hε1 (k + 1) _ (hBs_lam m p)
      have hpow_nn : (0 : ℝ) ≤ ((1 - ε) / 2) ^ (k + 1 + 1) :=
        pow_nonneg (by linarith) _
      have hbnd : |(Bs m p p).re| * ((1 + ε) / 2) ≤ 1 := by linarith
      have hsimp : 2 / (1 + ε) * ((1 + ε) / 2) = 1 := by
        field_simp
      have habs_nn : 0 ≤ |(Bs m p p).re| := abs_nonneg _
      have htarget : |(Bs m p p).re| * ((1 + ε) / 2) ≤ 2 / (1 + ε) * ((1 + ε) / 2) := by
        rw [hsimp]; exact hbnd
      exact le_of_mul_le_mul_right htarget h1ε_pos2
    have hBs_im : ∀ (m : Fin 4) (p : Fin (4 ^ (k + 1))),
        |(Bs m p p).im| ≤ 2 / (1 + ε) := by
      intro m p
      have habs := Lambda_abs_im_le hε hε1 (k + 1) _ (hBs_lam m p)
      have hpow_nn : (0 : ℝ) ≤ ((1 - ε) / 2) ^ (k + 1 + 1) :=
        pow_nonneg (by linarith) _
      have hbnd : |(Bs m p p).im| * ((1 + ε) / 2) ≤ 1 := by linarith
      have hsimp : 2 / (1 + ε) * ((1 + ε) / 2) = 1 := by
        field_simp
      have habs_nn : 0 ≤ |(Bs m p p).im| := abs_nonneg _
      have htarget : |(Bs m p p).im| * ((1 + ε) / 2) ≤ 2 / (1 + ε) * ((1 + ε) / 2) := by
        rw [hsimp]; exact hbnd
      exact le_of_mul_le_mul_right htarget h1ε_pos2
    have pert_bound : ∀ (x y : ℝ), |x| ≤ 2 / (1 + ε) → |y| ≤ 2 / (1 + ε) →
        |(1 - ε) / 2 * (x - y)| ≤ 2 * (1 - ε) / (1 + ε) := by
      intro x y hx hy
      rw [abs_mul, abs_of_nonneg hr_nn]
      have : |x - y| ≤ 4 / (1 + ε) := by
        have hxy : |x - y| ≤ |x| + |y| :=
          abs_add_le x (-y) |>.trans (by rw [abs_neg])
        calc |x - y| ≤ |x| + |y| := hxy
          _ ≤ 2 / (1 + ε) + 2 / (1 + ε) := by linarith
          _ = 4 / (1 + ε) := by ring
      calc (1 - ε) / 2 * |x - y| ≤ (1 - ε) / 2 * (4 / (1 + ε)) :=
            mul_le_mul_of_nonneg_left this hr_nn
        _ = 2 * (1 - ε) / (1 + ε) := by ring
    have h2ε_le : 2 * ε ≤ 4 * ε / (1 + ε) := by
      rw [le_div_iff₀ h1ε_pos]; nlinarith
    -- Express Si α p p in terms of (1-ε)/2 * Bs α p p + cornerOf α
    have hSi_form : ∀ γ p, Si γ p p = ((1 - ↑ε) / 2 : ℂ) * Bs γ p p + cornerOf γ := by
      intro γ p
      rw [hSi_entry, fullB_diag_entry]
      have h1 : (e.symm (γ, p)) = (finBlockEquiv k).symm (γ, p) := rfl
      rw [h1, Equiv.apply_symm_apply]
    have diff_re' : ∀ p q, (Si α p p - Si β q q).re =
        (1 - ε) / 2 * ((Bs α p p).re - (Bs β q q).re) +
        ((cornerOf α).re - (cornerOf β).re) := by
      intro p q; rw [hSi_form, hSi_form]
      simp [Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]; ring
    have diff_im' : ∀ p q, (Si α p p - Si β q q).im =
        (1 - ε) / 2 * ((Bs α p p).im - (Bs β q q).im) +
        ((cornerOf α).im - (cornerOf β).im) := by
      intro p q; rw [hSi_form, hSi_form]
      simp [Complex.add_im, Complex.sub_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]; ring
    by_cases hre_eq : (cornerOf α).re = (cornerOf β).re
    · -- Re corners equal → Im corners differ → signed Im bound
      have him_ne : (cornerOf α).im ≠ (cornerOf β).im := by
        intro h; exact hδ_ne (Complex.ext hre_eq h)
      have him_pm2 : (cornerOf α).im - (cornerOf β).im = 2 ∨
                     (cornerOf α).im - (cornerOf β).im = -2 := by
        rcases cornerOf_im_pm1 α with h1 | h1 <;> rcases cornerOf_im_pm1 β with h2 | h2 <;>
          simp [h1, h2] at him_ne ⊢ <;> norm_num
      rcases him_pm2 with hsign | hsign
      · -- Si - Sj has positive Im → second disjunct
        right; left; intro p q; rw [diff_im']
        set P := (1 - ε) / 2 * ((Bs α p p).im - (Bs β q q).im)
        have hpert := pert_bound _ _ (hBs_im α p) (hBs_im β q)
        have hP_lb : -(2 * (1 - ε) / (1 + ε)) ≤ P := by linarith [neg_abs_le P]
        have : 4 * ε / (1 + ε) ≤ P + 2 := by
          have : 2 - 2 * (1 - ε) / (1 + ε) = 4 * ε / (1 + ε) := by field_simp; ring
          linarith
        rw [hsign]; linarith
      · -- Sj - Si has positive Im → fourth disjunct
        right; right; right; intro p q
        have hflip : (Si β q q - Si α p p).im = -(Si α p p - Si β q q).im := by
          simp [Complex.sub_im, neg_sub]
        rw [hflip, diff_im']
        set P := (1 - ε) / 2 * ((Bs α p p).im - (Bs β q q).im)
        have hpert := pert_bound _ _ (hBs_im α p) (hBs_im β q)
        have hP_ub : P ≤ 2 * (1 - ε) / (1 + ε) := by linarith [le_abs_self P]
        have : -(P + -2) ≥ 4 * ε / (1 + ε) := by
          have : 2 * (1 - ε) / (1 + ε) - 2 = -(4 * ε / (1 + ε)) := by field_simp; ring
          linarith
        rw [hsign]; linarith
    · -- Re corners differ → signed Re bound
      have hre_pm2 : (cornerOf α).re - (cornerOf β).re = 2 ∨
                     (cornerOf α).re - (cornerOf β).re = -2 := by
        rcases cornerOf_re_pm1 α with h1 | h1 <;> rcases cornerOf_re_pm1 β with h2 | h2 <;>
          simp [h1, h2] at hre_eq ⊢ <;> norm_num
      rcases hre_pm2 with hsign | hsign
      · left; intro p q; rw [diff_re']
        set P := (1 - ε) / 2 * ((Bs α p p).re - (Bs β q q).re)
        have hpert := pert_bound _ _ (hBs_re α p) (hBs_re β q)
        have hP_lb : -(2 * (1 - ε) / (1 + ε)) ≤ P := by linarith [neg_abs_le P]
        have : 4 * ε / (1 + ε) ≤ P + 2 := by
          have : 2 - 2 * (1 - ε) / (1 + ε) = 4 * ε / (1 + ε) := by field_simp; ring
          linarith
        rw [hsign]; linarith
      · right; right; left; intro p q
        have hflip : (Si β q q - Si α p p).re = -(Si α p p - Si β q q).re := by
          simp [Complex.sub_re, neg_sub]
        rw [hflip, diff_re']
        set P := (1 - ε) / 2 * ((Bs α p p).re - (Bs β q q).re)
        have hpert := pert_bound _ _ (hBs_re α p) (hBs_re β q)
        have hP_ub : P ≤ 2 * (1 - ε) / (1 + ε) := by linarith [le_abs_self P]
        have : -(P + -2) ≥ 4 * ε / (1 + ε) := by
          have : 2 * (1 - ε) / (1 + ε) - 2 = -(4 * ε / (1 + ε)) := by field_simp; ring
          linarith
        rw [hsign]; linarith
  -- For α ≠ β, conclude Cblk(α,β)(p,q) = Ablk(α,β)(p,q) / (Si α p p - Si β q q)
  -- (denominators are nonzero from separation), and apply schur_div_op_norm_bound_4way
  have hSi_ne : ∀ α β : Fin 4, α ≠ β → ∀ p q, Si α p p - Si β q q ≠ 0 := by
    intro α β hαβ p q hzero
    have hzero_neg : Si β q q - Si α p p = 0 := by
      have : -(Si α p p - Si β q q) = Si β q q - Si α p p := by ring
      rw [← this, hzero, neg_zero]
    rcases hsep_4way α β hαβ with h | h | h | h
    · have := h p q; rw [hzero] at this; simp at this; linarith
    · have := h p q; rw [hzero] at this; simp at this; linarith
    · have := h p q; rw [hzero_neg] at this; simp at this; linarith
    · have := h p q; rw [hzero_neg] at this; simp at this; linarith
  -- Cblk(α,β) equals the entrywise division of Ablk(α,β) by (Si α - Si β) when α ≠ β
  have hCblk_div : ∀ α β : Fin 4, α ≠ β →
      Cblk (α, β) =
        Matrix.of fun p q => Ablk (α, β) p q / (Si α p p - Si β q q) := by
    intro α β hαβ
    ext p q
    simp only [Matrix.of_apply]
    have heq := hblk_eq α β p q
    have hne := hSi_ne α β hαβ p q
    -- (Si α p p - Si β q q) * Cblk = Ablk, divisor nonzero ⟹ Cblk = Ablk / divisor
    field_simp
    linear_combination heq
  -- Apply the Schur-div bound for each cross-block
  have hCblk_norm : ∀ α β : Fin 4, α ≠ β →
      ‖Cblk (α, β)‖ ≤ ‖A‖ / (2 * ε) := by
    intro α β hαβ
    rw [hCblk_div α β hαβ]
    have hbnd := schur_div_op_norm_bound_4way (Si α) (Si β) (Ablk (α, β))
      (hSi_diag α) (hSi_diag β) (2 * ε) h2ε_pos (hsep_4way α β hαβ)
    -- Now ‖X‖ ≤ ‖Ablk(α,β)‖ / (2ε), and ‖Ablk(α,β)‖ ≤ ‖A‖ via matBlock_norm_le.
    have hAblk_le : ‖Ablk (α, β)‖ ≤ ‖A‖ := by
      have hABeq : Ablk (α, β) = matBlock A α β := by
        ext p q; simp only [Ablk, matBlock, Matrix.of_apply, he_def]
      rw [hABeq]; exact matBlock_norm_le A α β
    calc ‖Matrix.of fun p q => Ablk (α, β) p q / (Si α p p - Si β q q)‖
        ≤ ‖Ablk (α, β)‖ / (2 * ε) := hbnd
      _ ≤ ‖A‖ / (2 * ε) := by
          apply div_le_div_of_nonneg_right hAblk_le h2ε_pos.le
  -- Apply block_hs_opNorm_sq_le
  have hblockHS := block_hs_opNorm_sq_le e C
  -- Goal RHS for hblockHS: ‖C‖² ≤ Σ_p ‖Cblk p‖²
  -- Decompose the sum into diagonal (zero) and off-diagonal pairs
  have hsum_split : (∑ p : Fin 4 × Fin 4, ‖Cblk p‖ ^ 2) =
      ∑ p ∈ (Finset.univ : Finset (Fin 4 × Fin 4)).filter (fun p => p.1 ≠ p.2),
        ‖Cblk p‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin 4 × Fin 4))
        (fun p => p.1 ≠ p.2)]
    have hdiag_zero :
        (∑ p ∈ (Finset.univ : Finset (Fin 4 × Fin 4)).filter (fun p => ¬ p.1 ≠ p.2),
          ‖Cblk p‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_filter] at hp
      simp only [not_not] at hp
      have hp_eq : p.1 = p.2 := hp.2
      have : p = (p.1, p.1) := Prod.ext rfl hp_eq.symm
      rw [this, hCblk_diag_zero]
      simp
    rw [hdiag_zero]; ring
  -- Each off-diagonal block bounded by ‖A‖/(2ε), so sum ≤ 12 * (‖A‖/(2ε))²
  have hAnn : 0 ≤ ‖A‖ := norm_nonneg _
  have h_rhs_bound :
      (∑ p : Fin 4 × Fin 4, ‖Cblk p‖ ^ 2) ≤ 12 * (‖A‖ / (2 * ε)) ^ 2 := by
    rw [hsum_split]
    have hcard : ((Finset.univ : Finset (Fin 4 × Fin 4)).filter
        (fun p => p.1 ≠ p.2)).card = 12 := by decide
    calc (∑ p ∈ (Finset.univ : Finset (Fin 4 × Fin 4)).filter (fun p => p.1 ≠ p.2),
            ‖Cblk p‖ ^ 2)
        ≤ ∑ p ∈ (Finset.univ : Finset (Fin 4 × Fin 4)).filter (fun p => p.1 ≠ p.2),
            (‖A‖ / (2 * ε)) ^ 2 := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Finset.mem_filter] at hp
          have hαβ : p.1 ≠ p.2 := hp.2
          have hpx : p = (p.1, p.2) := rfl
          rw [hpx]
          have := hCblk_norm p.1 p.2 hαβ
          have hCnn : 0 ≤ ‖Cblk (p.1, p.2)‖ := norm_nonneg _
          have hAεnn : 0 ≤ ‖A‖ / (2 * ε) :=
            div_nonneg hAnn h2ε_pos.le
          exact pow_le_pow_left₀ hCnn this 2
      _ = 12 * (‖A‖ / (2 * ε)) ^ 2 := by
          rw [Finset.sum_const, hcard]
          simp [Nat.cast_ofNat]
  -- Now combine: ‖C‖² ≤ 12 * (‖A‖/(2ε))²
  have hC_sq : ‖C‖ ^ 2 ≤ 12 * (‖A‖ / (2 * ε)) ^ 2 :=
    le_trans hblockHS h_rhs_bound
  -- Take square root: ‖C‖ ≤ √12 * (‖A‖/(2ε)) = 2√3/(2ε) * ‖A‖ = √3/ε * ‖A‖
  have hCnn : 0 ≤ ‖C‖ := norm_nonneg _
  have hRHSnn : 0 ≤ Real.sqrt 12 * (‖A‖ / (2 * ε)) :=
    mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hAnn h2ε_pos.le)
  have hC_sqrt : ‖C‖ ≤ Real.sqrt 12 * (‖A‖ / (2 * ε)) := by
    have : ‖C‖ ^ 2 ≤ (Real.sqrt 12 * (‖A‖ / (2 * ε))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (12:ℝ) ≥ 0)]
      exact hC_sq
    exact le_of_sq_le_sq this hRHSnn
  -- √12 = 2√3, and 2√3/(2ε) = √3/ε ≤ 2√2/ε
  have hsqrt12 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [show (12 : ℝ) = 4 * 3 from by norm_num, Real.sqrt_mul (by norm_num : (4:ℝ) ≥ 0)]
    rw [show (4 : ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num : (2:ℝ) ≥ 0)]
  -- √3 ≤ 2√2 since 3 ≤ 8
  have hsqrt3_le : Real.sqrt 3 ≤ 2 * Real.sqrt 2 := by
    rw [show (2 : ℝ) * Real.sqrt 2 = Real.sqrt 4 * Real.sqrt 2 from by
      rw [show Real.sqrt 4 = 2 from by
        rw [show (4 : ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num : (2:ℝ) ≥ 0)]]]
    rw [← Real.sqrt_mul (by norm_num : (4:ℝ) ≥ 0)]
    apply Real.sqrt_le_sqrt; norm_num
  have hε_pos := hε
  -- Final calculation
  have hε_inv_nn : 0 ≤ 1 / ε := by positivity
  calc ‖C‖
      ≤ Real.sqrt 12 * (‖A‖ / (2 * ε)) := hC_sqrt
    _ = 2 * Real.sqrt 3 * (‖A‖ / (2 * ε)) := by rw [hsqrt12]
    _ = Real.sqrt 3 / ε * ‖A‖ := by
        rw [show ‖A‖ / (2 * ε) = ‖A‖ * (1 / (2 * ε)) from by ring]
        rw [show (Real.sqrt 3 / ε * ‖A‖ : ℝ) = Real.sqrt 3 * (‖A‖ / ε) from by ring]
        rw [show ‖A‖ / ε = ‖A‖ * (1 / ε) from by ring]
        ring
    _ ≤ 2 * Real.sqrt 2 / ε * ‖A‖ := by
        have hineq : Real.sqrt 3 / ε ≤ 2 * Real.sqrt 2 / ε := by
          apply div_le_div_of_nonneg_right hsqrt3_le hε.le
        exact mul_le_mul_of_nonneg_right hineq hAnn

/-- Off-diagonal Rosenblum: solve [fullB, Coff] = offDiagBlocks A
    with ‖Coff‖ ≤ (2√2/ε) * ‖offDiagBlocks A‖. -/
private lemma rosenblum_off_diag_solution {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (Bs : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (hBs_diag : ∀ i, IsDiagMatrix (Bs i))
    (hBs_lam : ∀ i j, (Bs i) j j ∈ (Lambda ε (k + 1) : Set ℂ)) :
    ∃ Coff : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ,
      ⁅fullB ε Bs, Coff⁆ₘ = offDiagBlocks A ∧
      ‖Coff‖ ≤ 2 * Real.sqrt 2 / ε * ‖offDiagBlocks A‖ := by
  -- Step 0: fullB is diagonal
  have fullB_off : ∀ r c, r ≠ c → fullB ε Bs r c = 0 := by
    intro r c hrc; simp only [fullB]
    split_ifs with h
    · exfalso; apply hrc; exact (finBlockEquiv k).injective (Prod.ext h.1 h.2)
    · rfl
  -- Step 1: fullB entries from different blocks are distinct.
  -- cornerOf is injective, so different blocks have different corners.
  -- The corner separation (≥ 2) exceeds the perturbation from the Lambda entries,
  -- so fullB(r,r) ≠ fullB(c,c) when block(r) ≠ block(c).
  have fullB_diff_blocks_ne : ∀ r c,
      (finBlockEquiv k r).1 ≠ (finBlockEquiv k c).1 →
      fullB ε Bs r r ≠ fullB ε Bs c c := by
    intro r c hblk heq
    rw [fullB_diag_entry, fullB_diag_entry] at heq
    set i := (finBlockEquiv k r).1 with hi_def
    set j := (finBlockEquiv k c).1 with hj_def
    set p := (finBlockEquiv k r).2
    set q := (finBlockEquiv k c).2
    -- Rearrange: cornerOf i - cornerOf j = ((1-ε)/2) * (Bs j q q - Bs i p p)
    have hdiff : (cornerOf i : ℂ) - cornerOf j =
        ((1 - ↑ε) / 2 : ℂ) * (Bs j q q - Bs i p p) := by
      have h := sub_eq_zero.mpr heq; ring_nf at h ⊢; linear_combination h
    have hr_nn : (0 : ℝ) ≤ (1 - ε) / 2 := by linarith
    have hε2_pos : (0 : ℝ) < (1 + ε) / 2 := by linarith
    have hrn_nn : (0 : ℝ) ≤ ((1 - ε) / 2) ^ (k + 1 + 1) := pow_nonneg hr_nn _
    -- cornerOf is injective
    have cornerOf_inj : Function.Injective cornerOf := by
      intro a b h; fin_cases a <;> fin_cases b <;>
        first | rfl | (exfalso; simp [cornerOf] at h; norm_num at h)
    have hδ_ne : cornerOf i ≠ cornerOf j := fun h => hblk (cornerOf_inj h)
    have hδi := cornerOf_mem i
    have hδj := cornerOf_mem j
    have hBi := hBs_lam i p
    have hBj := hBs_lam j q
    -- Corner Re/Im values are ±1
    have cornerOf_re_pm1 : ∀ (m : Fin 4), (cornerOf m).re = 1 ∨ (cornerOf m).re = -1 := by
      intro m; fin_cases m <;> simp [cornerOf]
    have cornerOf_im_pm1 : ∀ (m : Fin 4), (cornerOf m).im = 1 ∨ (cornerOf m).im = -1 := by
      intro m; fin_cases m <;> simp [cornerOf]
    have hδi_re := cornerOf_re_pm1 i
    have hδj_re := cornerOf_re_pm1 j
    have hδi_im := cornerOf_im_pm1 i
    have hδj_im := cornerOf_im_pm1 j
    -- Helper: extract Re/Im of hdiff
    have hdiff_im : (cornerOf i).im - (cornerOf j).im =
        (1 - ε) / 2 * ((Bs j q q).im - (Bs i p p).im) := by
      have := congr_arg Complex.im hdiff
      simp [Complex.mul_im, Complex.sub_im] at this ⊢; linarith
    have hdiff_re : (cornerOf i).re - (cornerOf j).re =
        (1 - ε) / 2 * ((Bs j q q).re - (Bs i p p).re) := by
      have := congr_arg Complex.re hdiff
      simp [Complex.mul_re, Complex.sub_re] at this ⊢; linarith
    -- Case split on Re vs Im difference
    by_cases hre_eq : (cornerOf i).re = (cornerOf j).re
    · -- Re equal ⟹ Im differs by 2
      have him_ne : (cornerOf i).im ≠ (cornerOf j).im := by
        intro h; exact hδ_ne (Complex.ext hre_eq h)
      have him_diff : |(cornerOf i).im - (cornerOf j).im| = 2 := by
        rcases hδi_im with h1 | h1 <;> rcases hδj_im with h2 | h2 <;>
          simp [h1, h2] at him_ne ⊢ <;> norm_num
      rw [hdiff_im, abs_mul, abs_of_nonneg hr_nn] at him_diff
      have h_sub : |(Bs j q q).im - (Bs i p p).im| ≤ |(Bs j q q).im| + |(Bs i p p).im| := by
        calc |(Bs j q q).im - (Bs i p p).im|
            ≤ |(Bs j q q).im| + |-(Bs i p p).im| := abs_add_le _ _
          _ = |(Bs j q q).im| + |(Bs i p p).im| := by rw [abs_neg]
      have h1 := Lambda_abs_im_le hε hε1 (k + 1) (Bs i p p) hBi
      have h2 := Lambda_abs_im_le hε hε1 (k + 1) (Bs j q q) hBj
      -- From him_diff + h_sub: 2 ≤ (1-ε)/2 * (|a|+|b|)
      -- From h1+h2: (|a|+|b|)*(1+ε)/2 ≤ 2 - 2*r^(k+2)
      -- Multiply: 2*(1+ε)/2 ≤ (1-ε)/2*(2-2*r^(k+2)) = (1-ε)-(1-ε)*r^(k+2) < 1
      -- But 2*(1+ε)/2 = 1+ε > 1 for ε > 0. Contradiction.
      have hge : (1 - ε) / 2 * (|(Bs j q q).im| + |(Bs i p p).im|) ≥ 2 :=
        le_trans (le_of_eq him_diff.symm) (mul_le_mul_of_nonneg_left h_sub hr_nn)
      have hsum_bound : (|(Bs i p p).im| + |(Bs j q q).im|) * ((1 + ε) / 2) ≤
          2 - 2 * ((1 - ε) / 2) ^ (k + 1 + 1) := by linarith
      have hkey : (1 - ε) / 2 * ((|(Bs j q q).im| + |(Bs i p p).im|) * ((1 + ε) / 2)) ≤
          (1 - ε) / 2 * (2 - 2 * ((1 - ε) / 2) ^ (k + 1 + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hr_nn
        linarith
      nlinarith
    · -- Re parts differ by 2
      have hre_diff : |(cornerOf i).re - (cornerOf j).re| = 2 := by
        rcases hδi_re with h1 | h1 <;> rcases hδj_re with h2 | h2 <;>
          simp [h1, h2] at hre_eq ⊢ <;> norm_num
      rw [hdiff_re, abs_mul, abs_of_nonneg hr_nn] at hre_diff
      have h_sub : |(Bs j q q).re - (Bs i p p).re| ≤ |(Bs j q q).re| + |(Bs i p p).re| := by
        calc |(Bs j q q).re - (Bs i p p).re|
            ≤ |(Bs j q q).re| + |-(Bs i p p).re| := abs_add_le _ _
          _ = |(Bs j q q).re| + |(Bs i p p).re| := by rw [abs_neg]
      have h1 := Lambda_abs_re_le hε hε1 (k + 1) (Bs i p p) hBi
      have h2 := Lambda_abs_re_le hε hε1 (k + 1) (Bs j q q) hBj
      have hge : (1 - ε) / 2 * (|(Bs j q q).re| + |(Bs i p p).re|) ≥ 2 :=
        le_trans (le_of_eq hre_diff.symm) (mul_le_mul_of_nonneg_left h_sub hr_nn)
      have hsum_bound : (|(Bs i p p).re| + |(Bs j q q).re|) * ((1 + ε) / 2) ≤
          2 - 2 * ((1 - ε) / 2) ^ (k + 1 + 1) := by linarith
      have hkey : (1 - ε) / 2 * ((|(Bs j q q).re| + |(Bs i p p).re|) * ((1 + ε) / 2)) ≤
          (1 - ε) / 2 * (2 - 2 * ((1 - ε) / 2) ^ (k + 1 + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hr_nn
        linarith
      nlinarith
  -- Step 2: Define Coff entry-wise
  set OD := offDiagBlocks A with hOD_def
  set Coff : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ :=
    Matrix.of fun r c =>
      if (finBlockEquiv k r).1 = (finBlockEquiv k c).1 then 0
      else OD r c / (fullB ε Bs r r - fullB ε Bs c c)
  -- Prove commutator equation once, use it for both parts
  have hCoff_comm : ⁅fullB ε Bs, Coff⁆ₘ = OD := by
    ext r c
    simp only [matComm, Matrix.sub_apply, Matrix.mul_apply]
    have sum1 : ∑ x, fullB ε Bs r x * Coff x c =
        fullB ε Bs r r * Coff r c := by
      rw [Finset.sum_eq_single r]
      · intro x _ hxr; rw [fullB_off r x (Ne.symm hxr), zero_mul]
      · intro hr; exact absurd (Finset.mem_univ r) hr
    have sum2 : ∑ x, Coff r x * fullB ε Bs x c =
        Coff r c * fullB ε Bs c c := by
      rw [Finset.sum_eq_single c]
      · intro x _ hxc; rw [fullB_off x c hxc, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ c) hc
    rw [sum1, sum2]
    simp only [Coff, Matrix.of_apply]
    by_cases heq : (finBlockEquiv k r).1 = (finBlockEquiv k c).1
    · -- Same block: Coff(r,c) = 0 and OD(r,c) = 0
      simp only [heq, ↓reduceIte, mul_zero, zero_mul, sub_zero]
      simp only [hOD_def, offDiagBlocks, heq, ↓reduceIte]
    · -- Different blocks
      simp only [heq, ↓reduceIte]
      have hne : fullB ε Bs r r - fullB ε Bs c c ≠ 0 :=
        sub_ne_zero.mpr (fullB_diff_blocks_ne r c heq)
      field_simp
  have hCoff_same : ∀ r c, (finBlockEquiv k r).1 = (finBlockEquiv k c).1 → Coff r c = 0 := by
    intro r c heq; simp only [Coff, Matrix.of_apply, heq, ↓reduceIte]
  have hOD_cross : ∀ r c, (finBlockEquiv k r).1 = (finBlockEquiv k c).1 → OD r c = 0 := by
    intro r c heq; simp only [hOD_def, offDiagBlocks, heq, ↓reduceIte]
  refine ⟨Coff, hCoff_comm, ?_⟩
  -- Part 2: Norm bound ‖Coff‖ ≤ (2√2/ε) * ‖OD‖
  -- Apply the Schur multiplier bound (axiomatized via Rosenblum contour integral)
  exact cross_block_schur_div_bound ε hε hε1 Bs hBs_diag hBs_lam OD hOD_cross
    Coff hCoff_same hCoff_comm

/-- Commutator identity: A = [fullB, blockDiagC + Coff] from per-block + off-diagonal. -/
private lemma comm_decomp_sum {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ)
    (ε : ℝ) (hε1 : ε < 1)
    (Bs Cs : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (hBs_diag : ∀ i, IsDiagMatrix (Bs i))
    (hBs_comm : ∀ i, matBlock A i i = ⁅Bs i, Cs i⁆ₘ)
    (Coff : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ)
    (hCoff : ⁅fullB ε Bs, Coff⁆ₘ = offDiagBlocks A) :
    A = ⁅fullB ε Bs, blockDiagC ε Cs + Coff⁆ₘ := by
  -- Bilinearity: ⁅D, M+N⁆ = ⁅D,M⁆ + ⁅D,N⁆
  have bilin : matComm (fullB ε Bs) (blockDiagC ε Cs + Coff) =
      matComm (fullB ε Bs) (blockDiagC ε Cs) + matComm (fullB ε Bs) Coff := by
    simp only [matComm, mul_add, add_mul]; abel
  change A = matComm (fullB ε Bs) (blockDiagC ε Cs + Coff)
  rw [bilin, hCoff]
  -- Goal: A = ⁅fullB ε Bs, blockDiagC ε Cs⁆ₘ + offDiagBlocks A
  -- Since fullB is diagonal, ⁅fullB, M⁆(r,c) = (fullB(r,r) - fullB(c,c)) * M(r,c)
  -- So ⁅fullB, blockDiagC⁆(r,c) = (fullB(r,r) - fullB(c,c)) * blockDiagC(r,c)
  -- Collapse the sums using the fact that fullB(r,x) = 0 for r ≠ x
  have fullB_off : ∀ r c, r ≠ c → fullB ε Bs r c = 0 := by
    intro r c hrc
    simp only [fullB]
    split_ifs with h
    · exfalso; apply hrc
      exact (finBlockEquiv k).injective (Prod.ext h.1 h.2)
    · rfl
  -- ⁅fullB, blockDiagC⁆ entry-wise
  have comm_entry : ∀ r c, matComm (fullB ε Bs) (blockDiagC ε Cs) r c =
      (fullB ε Bs r r - fullB ε Bs c c) * blockDiagC ε Cs r c := by
    intro r c
    simp only [matComm, Matrix.sub_apply, Matrix.mul_apply]
    have sum1 : ∑ x, fullB ε Bs r x * blockDiagC ε Cs x c =
        fullB ε Bs r r * blockDiagC ε Cs r c := by
      rw [Finset.sum_eq_single r]
      · intro x _ hxr; rw [fullB_off r x (Ne.symm hxr), zero_mul]
      · intro hr; exact absurd (Finset.mem_univ r) hr
    have sum2 : ∑ x, blockDiagC ε Cs r x * fullB ε Bs x c =
        blockDiagC ε Cs r c * fullB ε Bs c c := by
      rw [Finset.sum_eq_single c]
      · intro x _ hxc; rw [fullB_off x c hxc, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ c) hc
    rw [sum1, sum2]
    ring
  ext r c
  simp only [Matrix.add_apply, offDiagBlocks]
  rw [comm_entry]
  set ri := finBlockEquiv k r
  set ci := finBlockEquiv k c
  by_cases heq : ri.1 = ci.1
  · -- Same block: offDiagBlocks gives 0, need comm = A(r,c)
    simp only [heq, ↓reduceIte, add_zero]
    -- Use hBs_comm to get A r c = commutator entry
    have hrc := congr_fun (congr_fun (hBs_comm ri.1) ri.2) ci.2
    simp only [matBlock, matComm, Matrix.sub_apply, Matrix.mul_apply] at hrc
    have hr : (finBlockEquiv k).symm (ri.1, ri.2) = r := (finBlockEquiv k).symm_apply_apply r
    have hc : (finBlockEquiv k).symm (ci.1, ci.2) = c := (finBlockEquiv k).symm_apply_apply c
    rw [hr, heq, hc] at hrc
    -- hrc : A r c = ∑ Bs(ci.1)*Cs(ci.1) - ∑ Cs(ci.1)*Bs(ci.1)
    -- Collapse sums using diagonality of Bs
    have hd := hBs_diag ci.1
    have sum1 : ∑ j, Bs ci.1 ri.2 j * Cs ci.1 j ci.2 =
        Bs ci.1 ri.2 ri.2 * Cs ci.1 ri.2 ci.2 := by
      apply Finset.sum_eq_single ri.2
      · intro x _ hx; rw [hd ri.2 x (Ne.symm hx), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have sum2 : ∑ j, Cs ci.1 ri.2 j * Bs ci.1 j ci.2 =
        Cs ci.1 ri.2 ci.2 * Bs ci.1 ci.2 ci.2 := by
      apply Finset.sum_eq_single ci.2
      · intro x _ hx; rw [hd x ci.2 hx, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hrc, sum1, sum2]
    -- Goal: Bs*Cs - Cs*Bs = (fullB r r - fullB c c) * blockDiagC r c
    -- Expand RHS
    have hfB : fullB ε Bs r r - fullB ε Bs c c =
        ((1 - ↑ε) / 2 : ℂ) * (Bs ci.1 ri.2 ri.2 - Bs ci.1 ci.2 ci.2) := by
      have h1 : fullB ε Bs r r = ((1 - ↑ε) / 2 : ℂ) * Bs ri.1 ri.2 ri.2 + cornerOf ri.1 :=
        fullB_diag_entry ε Bs r
      have h2 : fullB ε Bs c c = ((1 - ↑ε) / 2 : ℂ) * Bs ci.1 ci.2 ci.2 + cornerOf ci.1 :=
        fullB_diag_entry ε Bs c
      rw [h1, h2, heq]; ring
    have hbC : blockDiagC ε Cs r c = (2 / (1 - ↑ε) : ℂ) * Cs ci.1 ri.2 ci.2 := by
      change (if ri.1 = ci.1 then (2 / (1 - ↑ε) : ℂ) * Cs ri.1 ri.2 ci.2 else 0) = _
      rw [if_pos heq, heq]
    rw [hfB, hbC]
    have hε_ne : (1 - (ε : ℂ)) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hε1.ne'
    field_simp
  · -- Different blocks: blockDiagC(r,c) = 0, comm = 0
    have hbd : blockDiagC ε Cs r c = 0 := by
      simp only [blockDiagC]
      rw [if_neg heq]
    rw [hbd, mul_zero, zero_add]
    simp only [heq, ↓reduceIte]

/-- Pointwise one-step contraction: for each zero-diagonal unit-norm matrix A of size
    4^(k+2), its mu at level k+2 is bounded by α times the supremum at level k+1 plus β.
    Proof: construct block-diagonal witness B (entries in Λ_{k+2}), C = blockDiagC + Coff,
    where blockDiagC handles diagonal blocks via per-block decompositions and
    Coff handles off-diagonal blocks via Rosenblum. -/
private lemma mu_one_step_pointwise (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (α β : ℝ), 0 < α ∧ 0 < β ∧
    ∀ (k : ℕ) (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ),
      ZeroDiag A → ‖A‖ = 1 →
      mu ε (k + 2) A ≤ α * mu_sup' ε (k + 1) (4 ^ (k + 1)) + β := by
  have h1ε_pos : (0 : ℝ) < 1 - ε := by linarith
  refine ⟨2 / (1 - ε), 2 * Real.sqrt 2 / ε * 2,
    by positivity, by positivity, ?_⟩
  intro k A hzd hnorm
  -- Suffices to show: for all η > 0, mu ≤ bound + c*η (then take η → 0)
  suffices h : ∀ η : ℝ, 0 < η →
      mu ε (k + 2) A ≤
        2 / (1 - ε) * mu_sup' ε (k + 1) (4 ^ (k + 1)) +
        2 * Real.sqrt 2 / ε * 2 + 2 / (1 - ε) * η by
    by_contra hlt
    push Not at hlt
    set bound := 2 / (1 - ε) * mu_sup' ε (k + 1) (4 ^ (k + 1)) +
      2 * Real.sqrt 2 / ε * 2
    set m := mu ε (k + 2) A
    -- pick η small enough: η = (m - bound) * (1-ε) / 4
    have hm_gt : bound < m := by linarith
    have hη_val : 0 < (m - bound) * (1 - ε) / 4 := by
      apply div_pos (mul_pos (by linarith) h1ε_pos) (by norm_num)
    have hgap := h ((m - bound) * (1 - ε) / 4) hη_val
    have h2_pos : (0 : ℝ) < 2 / (1 - ε) := by positivity
    -- 2/(1-ε) * ((m - bound)*(1-ε)/4) = (m - bound)/2
    have hsimp : 2 / (1 - ε) * ((m - bound) * (1 - ε) / 4) = (m - bound) / 2 := by
      field_simp; ring
    linarith
  intro η hη
  -- Step 1: diagonal blocks are zero-diagonal with norm ≤ 1
  have hblk_zd : ∀ i, ZeroDiag (matBlock A i i) :=
    fun i => matBlock_diag_zeroDiag A hzd i
  have hblk_norm : ∀ i, ‖matBlock A i i‖ ≤ 1 := by
    intro i; rw [← hnorm]; exact matBlock_norm_le A i i
  -- Step 2: per-block approximate decompositions (with slack η)
  have hdecomp : ∀ i,
      ∃ (Bi Ci : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ),
        IsDiagMatrix Bi ∧
        (∀ j, Bi j j ∈ (Lambda ε (k + 1) : Set ℂ)) ∧
        matBlock A i i = ⁅Bi, Ci⁆ₘ ∧
        ‖Ci‖ ≤ mu_sup' ε (k + 1) (4 ^ (k + 1)) + η :=
    fun i => block_decomp_approx ε hε hε1 k _ (hblk_zd i) (hblk_norm i) η hη
  choose Bs Cs hBs_diag hBs_lam hBs_comm hCs_bound using hdecomp
  -- Step 3: full B with entries in Lambda ε (k+2)
  have hB_diag : IsDiagMatrix (fullB ε Bs) := fullB_isDiag ε Bs hBs_diag
  have hB_lam : ∀ r, (fullB ε Bs) r r ∈ (Lambda ε (k + 2) : Set ℂ) :=
    fullB_entries_in_lambda ε Bs hBs_lam
  -- Step 4: off-diagonal solution via Rosenblum
  obtain ⟨Coff, hCoff_comm, hCoff_norm⟩ :=
    rosenblum_off_diag_solution A ε hε hε1 Bs hBs_diag hBs_lam
  -- Step 5: commutator identity
  have hcomm : A = ⁅fullB ε Bs, blockDiagC ε Cs + Coff⁆ₘ :=
    comm_decomp_sum A ε hε1 Bs Cs hBs_diag hBs_comm Coff hCoff_comm
  -- Step 6: norm bound via mu_le_witness_norm
  set C := blockDiagC ε Cs + Coff
  have h_mu_le := mu_le_witness_norm ε (k + 2) A
    (fullB ε Bs) C hB_diag hB_lam hcomm
  have h_tri := norm_add_le (blockDiagC ε Cs) Coff
  -- Step 7: combine bounds
  have h_blockDiag := blockDiagC_norm_le ε hε hε1 Cs
    (mu_sup' ε (k + 1) (4 ^ (k + 1)) + η) hCs_bound
  have h_offDiag := offDiagBlocks_norm_le A
  have h_norm_A : ‖A‖ = 1 := hnorm
  -- ‖Coff‖ ≤ 2√2/ε * ‖offDiagBlocks A‖ ≤ 2√2/ε * 2 * ‖A‖ = 2√2/ε * 2
  have hCoff_bound : ‖Coff‖ ≤ 2 * Real.sqrt 2 / ε * 2 := by
    calc ‖Coff‖ ≤ 2 * Real.sqrt 2 / ε * ‖offDiagBlocks A‖ := hCoff_norm
      _ ≤ 2 * Real.sqrt 2 / ε * (2 * ‖A‖) := by
          apply mul_le_mul_of_nonneg_left h_offDiag
          positivity
      _ = 2 * Real.sqrt 2 / ε * 2 := by rw [h_norm_A]; ring
  calc mu ε (k + 2) A
      ≤ ‖C‖ := h_mu_le
    _ ≤ ‖blockDiagC ε Cs‖ + ‖Coff‖ := h_tri
    _ ≤ 2 / (1 - ε) * (mu_sup' ε (k + 1) (4 ^ (k + 1)) + η) +
        (2 * Real.sqrt 2 / ε * 2) := by linarith [h_blockDiag, hCoff_bound]
    _ = 2 / (1 - ε) * mu_sup' ε (k + 1) (4 ^ (k + 1)) +
        2 * Real.sqrt 2 / ε * 2 +
        2 / (1 - ε) * η := by ring

/-- **Claim 1 (JOS 2013, Eq. 1) — pointwise μ-recursion.**

For `ε ∈ (0,1)` and any `4^(k+2) × 4^(k+2)` zero-diagonal matrix `A` decomposed into a
`4 × 4` block structure `A = (A_{ij})_{i,j=0..3}` (where `A_{ij} = matBlock A i j`),
if every diagonal block satisfies `μ(ε, k+1, A_{ii}) ≤ M`, then

  `μ(ε, k+2, A) ≤ (2/(1-ε)) · M + (6/ε²) · ‖A‖`.

This is the per-block analogue of `mu_one_step_pointwise` — the bound depends on the
individual μ of the diagonal blocks instead of the uniform sup `mu_sup'`.  The construction
mirrors the paper's Claim 1 (JOS 2013): build `B` as `fullB ε Bs` with `Bs i` the
per-block diagonal witnesses, build `C` as `blockDiagC ε Cs + Coff` where `Coff` solves the
off-diagonal Sylvester equations.

- The diagonal-block constant `2/(1-ε)` comes from the scaling factor `(1-ε)/2` used in
  `fullB` to embed `Λ_{k+1}` into `Λ_{k+2}`.
- The off-diagonal constant `6/ε²` comes from the Sylvester/contour-integral bound applied
  to each cross-block pair.  The dimension-free Sylvester bound used here is the (square
  specialization of the) rectangular Sylvester theorem `sylvester_rect_diag_opNorm_bound_re`
  in `NEst.lean`; it is invoked via the existing `rosenblum_off_diag_solution` helper,
  which delivers `‖Coff‖ ≤ (2√2/ε) · ‖offDiagBlocks A‖ ≤ (4√2/ε) · ‖A‖ ≤ (6/ε²) · ‖A‖`
  (the last inequality uses `4√2 · ε ≤ 6` for `ε ∈ (0,1)`). -/
theorem claim1_mu_recursion (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ}
    (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ) (hzd : ZeroDiag A)
    (M : ℝ) (hM : ∀ i : Fin 4, mu ε (k + 1) (matBlock A i i) ≤ M) :
    mu ε (k + 2) A ≤ 2 / (1 - ε) * M + 6 / ε ^ 2 * ‖A‖ := by
  have h1ε_pos : (0 : ℝ) < 1 - ε := by linarith
  have hε2_pos : (0 : ℝ) < ε ^ 2 := by positivity
  -- Suffices to show: ∀ η > 0, mu ≤ bound + (2/(1-ε))·η.
  suffices h : ∀ η : ℝ, 0 < η →
      mu ε (k + 2) A ≤
        2 / (1 - ε) * M + 6 / ε ^ 2 * ‖A‖ +
        2 / (1 - ε) * η by
    by_contra hlt
    push Not at hlt
    set bound := 2 / (1 - ε) * M + 6 / ε ^ 2 * ‖A‖ with hbound_def
    set m := mu ε (k + 2) A with hm_def
    have hm_gt : bound < m := hlt
    have hη_val : 0 < (m - bound) * (1 - ε) / 4 :=
      div_pos (mul_pos (by linarith) h1ε_pos) (by norm_num)
    have hgap := h ((m - bound) * (1 - ε) / 4) hη_val
    have hsimp : 2 / (1 - ε) * ((m - bound) * (1 - ε) / 4) = (m - bound) / 2 := by
      field_simp; ring
    linarith
  intro η hη
  -- Per-block decomposition: extract Bi, Ci with A_ii = [Bi, Ci], ‖Ci‖ ≤ M + η.
  have hcard : 4 ^ (k + 1) ≤ (Lambda ε (k + 1)).card :=
    Lambda_card_ge ε hε hε1 (k + 1)
  have hdecomp : ∀ i : Fin 4,
      ∃ (Bi Ci : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ),
        IsDiagMatrix Bi ∧
        (∀ j, Bi j j ∈ (Lambda ε (k + 1) : Set ℂ)) ∧
        matBlock A i i = ⁅Bi, Ci⁆ₘ ∧
        ‖Ci‖ ≤ M + η := by
    intro i
    exact mu_extract_witness hε (matBlock_diag_zeroDiag A hzd i) hcard (hM i) η hη
  choose Bs Cs hBs_diag hBs_lam hBs_comm hCs_bound using hdecomp
  -- Build fullB.
  have hB_diag : IsDiagMatrix (fullB ε Bs) := fullB_isDiag ε Bs hBs_diag
  have hB_lam : ∀ r, (fullB ε Bs) r r ∈ (Lambda ε (k + 2) : Set ℂ) :=
    fullB_entries_in_lambda ε Bs hBs_lam
  -- Off-diagonal Sylvester (delegates internally to `sylvester_diag_opNorm_bound_re_or_im`,
  -- the square specialization of `NEst.sylvester_rect_diag_opNorm_bound_re`).
  obtain ⟨Coff, hCoff_comm, hCoff_norm⟩ :=
    rosenblum_off_diag_solution A ε hε hε1 Bs hBs_diag hBs_lam
  -- Commutator identity: A = [fullB ε Bs, blockDiagC ε Cs + Coff].
  have hcomm : A = ⁅fullB ε Bs, blockDiagC ε Cs + Coff⁆ₘ :=
    comm_decomp_sum A ε hε1 Bs Cs hBs_diag hBs_comm Coff hCoff_comm
  set C := blockDiagC ε Cs + Coff with hC_def
  -- mu ≤ ‖C‖
  have h_mu_le := mu_le_witness_norm ε (k + 2) A (fullB ε Bs) C hB_diag hB_lam hcomm
  -- ‖blockDiagC ε Cs‖ ≤ 2/(1-ε) · (M + η)
  have h_blockDiag := blockDiagC_norm_le ε hε hε1 Cs (M + η) hCs_bound
  -- ‖Coff‖ ≤ (2√2/ε) · ‖offDiagBlocks A‖ ≤ (4√2/ε) · ‖A‖.
  have h_offDiag := offDiagBlocks_norm_le A
  have hCoff_le : ‖Coff‖ ≤ 4 * Real.sqrt 2 / ε * ‖A‖ := by
    calc ‖Coff‖ ≤ 2 * Real.sqrt 2 / ε * ‖offDiagBlocks A‖ := hCoff_norm
      _ ≤ 2 * Real.sqrt 2 / ε * (2 * ‖A‖) :=
          mul_le_mul_of_nonneg_left h_offDiag (by positivity)
      _ = 4 * Real.sqrt 2 / ε * ‖A‖ := by ring
  -- 4√2/ε ≤ 6/ε² for ε ∈ (0,1): equivalent to 4√2·ε ≤ 6, which holds since
  -- 4√2 ≤ 6 (because √2 ≤ 1.5) and ε ≤ 1.
  have hsqrt2_le_three_half : Real.sqrt 2 ≤ 3 / 2 := by
    have h : Real.sqrt 2 ≤ Real.sqrt ((3 / 2) ^ 2) :=
      Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h
  have h4sqrt2_le_six : 4 * Real.sqrt 2 ≤ 6 := by linarith
  have h4sqrt2_le : 4 * Real.sqrt 2 / ε ≤ 6 / ε ^ 2 := by
    rw [div_le_div_iff₀ hε hε2_pos]
    -- need: 4·√2·ε² ≤ 6·ε  ⟺  (4√2·ε) · ε ≤ 6 · ε
    nlinarith [Real.sqrt_nonneg 2, hε, hε1, h4sqrt2_le_six]
  have hCoff_bound : ‖Coff‖ ≤ 6 / ε ^ 2 * ‖A‖ :=
    le_trans hCoff_le (mul_le_mul_of_nonneg_right h4sqrt2_le (norm_nonneg _))
  -- Final norm calculation.
  calc mu ε (k + 2) A
      ≤ ‖C‖ := h_mu_le
    _ ≤ ‖blockDiagC ε Cs‖ + ‖Coff‖ := norm_add_le _ _
    _ ≤ 2 / (1 - ε) * (M + η) + 6 / ε ^ 2 * ‖A‖ := by linarith
    _ = 2 / (1 - ε) * M + 6 / ε ^ 2 * ‖A‖ + 2 / (1 - ε) * η := by ring

private lemma mu_one_step (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (α β : ℝ), 0 < α ∧ 0 < β ∧
    ∀ k : ℕ, mu_sup' ε (k + 2) (4 ^ (k + 2)) ≤
      α * mu_sup' ε (k + 1) (4 ^ (k + 1)) + β := by
  obtain ⟨α, β, hα_pos, hβ_pos, hpw⟩ := mu_one_step_pointwise ε hε hε1
  refine ⟨α, β, hα_pos, hβ_pos, fun k => ?_⟩
  -- Unfold mu_sup' on the LHS to work with the raw sSup.
  -- If the defining set is nonempty, use csSup_le with the pointwise bound.
  -- If empty, sSup = 0 and the bound follows from β > 0 and mu_sup' ≥ 0.
  unfold mu_sup' at *
  -- Use Real.sSup_def: sSup S = 0 if S is empty or not bdd above
  by_cases hne : (∃ (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ),
      ZeroDiag A ∧ ‖A‖ = 1)
  · -- The set is nonempty
    have hne' : {y : ℝ | ∃ (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ),
        ZeroDiag A ∧ ‖A‖ = 1 ∧ y = mu ε (k + 2) A}.Nonempty := by
      obtain ⟨A, hzd, hnorm⟩ := hne
      exact ⟨mu ε (k + 2) A, A, hzd, hnorm, rfl⟩
    exact csSup_le hne' (fun y hy => by
      obtain ⟨A, hzd, hnorm, rfl⟩ := hy
      exact hpw k A hzd hnorm)
  · -- The set is empty; sSup = 0. Need 0 ≤ α * mu_sup'(k+1) + β.
    push Not at hne
    have hempty : {y : ℝ | ∃ (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ),
        ZeroDiag A ∧ ‖A‖ = 1 ∧ y = mu ε (k + 2) A} = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨_, A, hzd, hnorm, _⟩; exact hne A hzd hnorm
    rw [hempty, Real.sSup_empty]
    change 0 ≤ α * mu_sup' ε (k + 1) (4 ^ (k + 1)) + β
    have hmsup_nn : 0 ≤ mu_sup' ε (k + 1) (4 ^ (k + 1)) := by
      unfold mu_sup'
      by_cases hne1 : {y : ℝ | ∃ (A : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ),
          ZeroDiag A ∧ ‖A‖ = 1 ∧ y = mu ε (k + 1) A}.Nonempty
      · obtain ⟨_, A, hzd1, hnorm1, rfl⟩ := hne1
        exact le_csSup_of_le
          ⟨Real.sqrt ↑(4 ^ (k + 1)) / (2 * ((1 - ε) / 2) ^ (k + 1)),
           fun y hy => by
             obtain ⟨A', hzd', hnorm', rfl⟩ := hy
             exact mu_explicit_bound ε hε hε1 k A' hzd' hnorm'⟩
          ⟨A, hzd1, hnorm1, rfl⟩
          (mu_nonneg ε (k + 1) A)
      · rw [Set.not_nonempty_iff_eq_empty.mp hne1, Real.sSup_empty]
    have := mul_nonneg (le_of_lt hα_pos) hmsup_nn
    linarith

/-- Base case: mu_sup' at level 1 for 4×4 matrices is bounded.
    Uses mu_explicit_bound with k=0 to get mu ε 1 A ≤ √4 / (2·((1-ε)/2)). -/
private lemma mu_base_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (C₀ : ℝ), 0 < C₀ ∧ mu_sup' ε 1 (4 ^ 1) ≤ C₀ := by
  set bound := Real.sqrt ↑(4 ^ 1) / (2 * ((1 - ε) / 2) ^ 1) with hbound_def
  have h1ε : (0 : ℝ) < (1 - ε) / 2 := by linarith
  have h4pos : (0 : ℝ) < (4 : ℕ) ^ 1 := by norm_num
  have hsqrt_pos : 0 < Real.sqrt ↑(4 ^ 1) := Real.sqrt_pos.mpr (by exact_mod_cast h4pos)
  have hbound_pos : 0 < bound := div_pos hsqrt_pos (mul_pos (by norm_num) (pow_pos h1ε 1))
  use bound, hbound_pos
  unfold mu_sup'
  set S := {y : ℝ | ∃ (A : Matrix (Fin (4 ^ 1)) (Fin (4 ^ 1)) ℂ),
    ZeroDiag A ∧ ‖A‖ = 1 ∧ y = mu ε 1 A}
  by_cases hne : S.Nonempty
  · exact csSup_le hne (fun y hy => by
      obtain ⟨A, hzd, hnorm, rfl⟩ := hy
      exact mu_explicit_bound ε hε hε1 0 A hzd hnorm)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp [hbound_pos.le]

/-- The set defining mu_sup' is BddAbove (from mu_explicit_bound). -/
private lemma mu_sup_bddAbove (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
    BddAbove {y : ℝ | ∃ (A : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ),
      ZeroDiag A ∧ ‖A‖ = 1 ∧ y = mu ε (k + 1) A} := by
  use Real.sqrt ↑(4 ^ (k + 1)) / (2 * ((1 - ε) / 2) ^ (k + 1))
  intro y hy
  obtain ⟨A, hzd, hnorm, rfl⟩ := hy
  exact mu_explicit_bound ε hε hε1 k A hzd hnorm

/-- mu ε (k+1) A ≤ mu_sup' ε (k+1) (4^(k+1)) for zero-diagonal unit-norm A. -/
private lemma mu_le_mu_sup (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ)
    (A : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1) :
    mu ε (k + 1) A ≤ mu_sup' ε (k + 1) (4 ^ (k + 1)) := by
  unfold mu_sup'
  exact le_csSup (mu_sup_bddAbove ε hε hε1 k) ⟨A, hzd, hnorm, rfl⟩

/-- Base case: mu ε 1 A is uniformly bounded for all zero-diagonal unit-norm 4×4 matrices.
    Follows from mu_explicit_bound at k=0: mu ε 1 A ≤ √4 / (2·((1-ε)/2)). -/
private lemma mu_pointwise_base (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (C₀ : ℝ), 0 < C₀ ∧
    ∀ A : Matrix (Fin (4 ^ 1)) (Fin (4 ^ 1)) ℂ, ZeroDiag A → ‖A‖ = 1 →
      mu ε 1 A ≤ C₀ := by
  use Real.sqrt ↑(4 ^ 1) / (2 * ((1 - ε) / 2) ^ 1)
  refine ⟨div_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < ↑(4 ^ 1)))
    (mul_pos (by norm_num) (pow_pos (by linarith : (0:ℝ) < (1 - ε) / 2) 1)), ?_⟩
  intro A hzd hnorm
  exact mu_explicit_bound ε hε hε1 0 A hzd hnorm

/- Historical development log (statuses below refer only to that earlier draft).
State: 🔄 partial (1 live sorry: paving_improved_mu_core — witness construction for JOS 2013 Claim 2)
Priority: 1
Chain: paving_mu_direct_bound → paving_witness_construction → paving_analytical_mu_bound →
  paving_improved_mu_bound
  → claim2_improved_reassembly → paving_witness_improved_coeff
  → paving_mu_bound_core → paving_decomp_improved → paving_mu_core_ineq
  → paving_mu_improved_bound → paving_improved_witness → mu_paving_improved_step
  → mu_paving_step_core.
Session 13: extracted paving_block_A_bound (PROVED). Flattened chain:
paving_improved_mu_bound handles M+η≤0 directly, calls paving_analytical_mu_bound
for M+η>0. Sorry target: mu ε (k+2) A ≤ (1+ε)*(M+η) + 4√2/ε, given per-block
bound ‖blockOf σ A i i‖ ≤ √2*ε/(1+ε)*‖C_std‖. Core of JOS 2013 Claim 2.
-/
/-- Lambda entries have |re| ≤ 2/(1+ε). The recursive lattice Lambda_n(ε) satisfies
    the fixed-point equation M = ((1-ε)/2)·M + 1 with M(0)=1, giving M_∞ = 2/(1+ε). -/
private lemma Lambda_re_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ) (z : ℂ)
    (hz : z ∈ (Lambda ε k : Set ℂ)) :
    |z.re| ≤ 2 / (1 + ε) := by
  have h1ε : 1 ≤ 2 / (1 + ε) := by rw [le_div_iff₀ (by linarith)]; linarith
  induction k generalizing z with
  | zero =>
    simp only [Lambda, Finset.mem_coe] at hz
    unfold cornerSet at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> (simp; linarith)
  | succ k ih =>
    simp only [Lambda, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image] at hz
    obtain ⟨δ, hδ_mem, w, hw_mem, rfl⟩ := hz
    change |((1 - ↑ε) / 2 * w + δ).re| ≤ 2 / (1 + ε)
    have hw_re : |w.re| ≤ 2 / (1 + ε) := ih w (Finset.mem_coe.mpr hw_mem)
    have hcoeff_nn : (0 : ℝ) ≤ (1 - ε) / 2 := by linarith
    have hre : (((1 - ↑ε) / 2 : ℂ) * w + δ).re = (1 - ε) / 2 * w.re + δ.re := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre]
    have hδ_re : |δ.re| ≤ 1 := by
      unfold cornerSet at hδ_mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hδ_mem
      rcases hδ_mem with rfl | rfl | rfl | rfl <;> norm_num
    calc |(1 - ε) / 2 * w.re + δ.re|
        ≤ |(1 - ε) / 2 * w.re| + |δ.re| := abs_add_le _ _
      _ = (1 - ε) / 2 * |w.re| + |δ.re| := by rw [abs_mul, abs_of_nonneg hcoeff_nn]
      _ ≤ (1 - ε) / 2 * (2 / (1 + ε)) + 1 := by gcongr
      _ = (1 - ε) / (1 + ε) + 1 := by ring
      _ = 2 / (1 + ε) := by field_simp; ring

/-- Lambda entries have |im| ≤ 2/(1+ε). Same proof as Lambda_re_bound by symmetry. -/
private lemma Lambda_im_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ) (z : ℂ)
    (hz : z ∈ (Lambda ε k : Set ℂ)) :
    |z.im| ≤ 2 / (1 + ε) := by
  have h1ε : 1 ≤ 2 / (1 + ε) := by rw [le_div_iff₀ (by linarith)]; linarith
  induction k generalizing z with
  | zero =>
    simp only [Lambda, Finset.mem_coe] at hz
    unfold cornerSet at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> (simp; linarith)
  | succ k ih =>
    simp only [Lambda, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image] at hz
    obtain ⟨δ, hδ_mem, w, hw_mem, rfl⟩ := hz
    change |((1 - ↑ε) / 2 * w + δ).im| ≤ 2 / (1 + ε)
    have hw_im : |w.im| ≤ 2 / (1 + ε) := ih w (Finset.mem_coe.mpr hw_mem)
    have hcoeff_nn : (0 : ℝ) ≤ (1 - ε) / 2 := by linarith
    have him : (((1 - ↑ε) / 2 : ℂ) * w + δ).im = (1 - ε) / 2 * w.im + δ.im := by
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [him]
    have hδ_im : |δ.im| ≤ 1 := by
      unfold cornerSet at hδ_mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hδ_mem
      rcases hδ_mem with rfl | rfl | rfl | rfl <;> norm_num
    calc |(1 - ε) / 2 * w.im + δ.im|
        ≤ |(1 - ε) / 2 * w.im| + |δ.im| := abs_add_le _ _
      _ = (1 - ε) / 2 * |w.im| + |δ.im| := by rw [abs_mul, abs_of_nonneg hcoeff_nn]
      _ ≤ (1 - ε) / 2 * (2 / (1 + ε)) + 1 := by gcongr
      _ = (1 - ε) / (1 + ε) + 1 := by ring
      _ = 2 / (1 + ε) := by field_simp; ring

/-- For distinct 4-block indices i ≠ j, the fullB diagonal entries have either Re or Im
    separation ≥ 2ε uniformly over all pairs of sub-indices. This enables the dim-free
    Sylvester equation bound on off-diagonal blocks. -/
private lemma fullB_cross_block_sep {k : ℕ} (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (Bs : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (hBs_lam : ∀ i j, (Bs i) j j ∈ (Lambda ε (k + 1) : Set ℂ))
    (i j : Fin 4) (hij : i ≠ j) :
    (∀ a b : Fin (4 ^ (k + 1)),
      2 * ε ≤ |((fullB ε Bs) ((finBlockEquiv k).symm (i, a)) ((finBlockEquiv k).symm (i, a)) -
               (fullB ε Bs) ((finBlockEquiv k).symm (j, b)) ((finBlockEquiv k).symm (j, b))).re|) ∨
    (∀ a b : Fin (4 ^ (k + 1)),
      2 * ε ≤ |((fullB ε Bs) ((finBlockEquiv k).symm (i, a)) ((finBlockEquiv k).symm (i, a)) -
               (fullB ε Bs) ((finBlockEquiv k).symm (j, b))
                 ((finBlockEquiv k).symm (j, b))).im|) := by
  -- Simplify fullB entries using the diagonal entry lemma
  have hsimp : ∀ (m : Fin 4) (p : Fin (4 ^ (k + 1))),
      (fullB ε Bs) ((finBlockEquiv k).symm (m, p)) ((finBlockEquiv k).symm (m, p)) =
      ((1 - ↑ε) / 2 : ℂ) * (Bs m p p) + cornerOf m := by
    intro m p; rw [fullB_diag_entry]; simp
  simp_rw [hsimp]
  -- Setup
  have cornerOf_re_pm1 : ∀ (m : Fin 4), (cornerOf m).re = 1 ∨ (cornerOf m).re = -1 := by
    intro m; fin_cases m <;> simp [cornerOf]
  have cornerOf_im_pm1 : ∀ (m : Fin 4), (cornerOf m).im = 1 ∨ (cornerOf m).im = -1 := by
    intro m; fin_cases m <;> simp [cornerOf]
  have cornerOf_inj : Function.Injective cornerOf := by
    intro a b h; fin_cases a <;> fin_cases b <;>
      first | rfl | (exfalso; simp [cornerOf] at h; norm_num at h)
  have hδ_ne : cornerOf i ≠ cornerOf j := fun h => hij (cornerOf_inj h)
  have hr_nn : (0 : ℝ) ≤ (1 - ε) / 2 := by linarith
  have h1ε_pos : (0 : ℝ) < 1 + ε := by linarith
  have hBs_re : ∀ (m : Fin 4) (p : Fin (4 ^ (k + 1))),
      |(Bs m p p).re| ≤ 2 / (1 + ε) :=
    fun m p => Lambda_re_bound ε hε hε1 (k + 1) _ (hBs_lam m p)
  have hBs_im : ∀ (m : Fin 4) (p : Fin (4 ^ (k + 1))),
      |(Bs m p p).im| ≤ 2 / (1 + ε) :=
    fun m p => Lambda_im_bound ε hε hε1 (k + 1) _ (hBs_lam m p)
  -- Helper: bound on perturbation term for any coordinate
  -- |(1-ε)/2 * (x - y)| ≤ 2(1-ε)/(1+ε) when |x|,|y| ≤ 2/(1+ε)
  have pert_bound : ∀ (x y : ℝ), |x| ≤ 2 / (1 + ε) → |y| ≤ 2 / (1 + ε) →
      |(1 - ε) / 2 * (x - y)| ≤ 2 * (1 - ε) / (1 + ε) := by
    intro x y hx hy
    rw [abs_mul, abs_of_nonneg hr_nn]
    have : |x - y| ≤ 4 / (1 + ε) := by
      have hxy : |x - y| ≤ |x| + |y| :=
        abs_add_le x (-y) |>.trans (by rw [abs_neg])
      calc |x - y| ≤ |x| + |y| := hxy
        _ ≤ 2 / (1 + ε) + 2 / (1 + ε) := by linarith
        _ = 4 / (1 + ε) := by ring
    calc (1 - ε) / 2 * |x - y| ≤ (1 - ε) / 2 * (4 / (1 + ε)) :=
          mul_le_mul_of_nonneg_left this hr_nn
      _ = 2 * (1 - ε) / (1 + ε) := by ring
  -- Helper: 2ε ≤ 4ε/(1+ε) since ε < 1 means 1+ε < 2
  have h2ε_le : 2 * ε ≤ 4 * ε / (1 + ε) := by
    rw [le_div_iff₀ h1ε_pos]; nlinarith
  -- Helper: extract Re/Im of the difference
  have diff_re : ∀ (a b : Fin (4 ^ (k + 1))),
      ((1 - ↑ε) / 2 * Bs i a a + cornerOf i - ((1 - ↑ε) / 2 * Bs j b b + cornerOf j)).re =
      (1 - ε) / 2 * ((Bs i a a).re - (Bs j b b).re) + ((cornerOf i).re - (cornerOf j).re) := by
    intro a b; simp [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]; ring
  have diff_im : ∀ (a b : Fin (4 ^ (k + 1))),
      ((1 - ↑ε) / 2 * Bs i a a + cornerOf i - ((1 - ↑ε) / 2 * Bs j b b + cornerOf j)).im =
      (1 - ε) / 2 * ((Bs i a a).im - (Bs j b b).im) + ((cornerOf i).im - (cornerOf j).im) := by
    intro a b; simp [Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]; ring
  -- Main case split
  by_cases hre_eq : (cornerOf i).re = (cornerOf j).re
  · -- Re equal ⟹ Im differs by ±2
    right; intro a b; rw [diff_im]
    have him_ne : (cornerOf i).im ≠ (cornerOf j).im := by
      intro h; exact hδ_ne (Complex.ext hre_eq h)
    have hpert := pert_bound _ _ (hBs_im i a) (hBs_im j b)
    -- Corner Im difference is ±2
    have him_pm2 : (cornerOf i).im - (cornerOf j).im = 2 ∨
                   (cornerOf i).im - (cornerOf j).im = -2 := by
      rcases cornerOf_im_pm1 i with h1 | h1 <;> rcases cornerOf_im_pm1 j with h2 | h2 <;>
        simp [h1, h2] at him_ne ⊢ <;> norm_num
    -- In both cases, |perturbation + corner_diff| ≥ 2 - 2(1-ε)/(1+ε) = 4ε/(1+ε) ≥ 2ε
    set P := (1 - ε) / 2 * ((Bs i a a).im - (Bs j b b).im) with hP_def
    rcases him_pm2 with hsign | hsign <;> rw [hsign]
    · -- corner_diff = +2: total = P + 2 ≥ 2 - 2(1-ε)/(1+ε) = 4ε/(1+ε) ≥ 2ε
      -- From |P| ≤ bound, we get -bound ≤ P
      have hP_lb : -(2 * (1 - ε) / (1 + ε)) ≤ P := by linarith [neg_abs_le P]
      -- So P + 2 ≥ 2 - 2(1-ε)/(1+ε) = (2(1+ε) - 2(1-ε))/(1+ε) = 4ε/(1+ε)
      have hsum_lb : 4 * ε / (1 + ε) ≤ P + 2 := by
        have : 2 - 2 * (1 - ε) / (1 + ε) = 4 * ε / (1 + ε) := by field_simp; ring
        linarith
      -- P + 2 > 0, so |P + 2| = P + 2
      have hpos : 0 < P + 2 := by linarith
      rw [abs_of_pos hpos]; linarith
    · -- corner_diff = -2: total = P + (-2) ≤ 2(1-ε)/(1+ε) - 2 = -4ε/(1+ε)
      have hP_ub : P ≤ 2 * (1 - ε) / (1 + ε) := by linarith [le_abs_self P]
      have hsum_ub : P + (-2 : ℝ) ≤ -(4 * ε / (1 + ε)) := by
        have : 2 * (1 - ε) / (1 + ε) - 2 = -(4 * ε / (1 + ε)) := by field_simp; ring
        linarith
      have hneg : P + (-2 : ℝ) < 0 := by linarith
      rw [abs_of_neg hneg]; linarith
  · -- Re parts differ by ±2
    left; intro a b; rw [diff_re]
    have hpert := pert_bound _ _ (hBs_re i a) (hBs_re j b)
    have hre_pm2 : (cornerOf i).re - (cornerOf j).re = 2 ∨
                   (cornerOf i).re - (cornerOf j).re = -2 := by
      rcases cornerOf_re_pm1 i with h1 | h1 <;> rcases cornerOf_re_pm1 j with h2 | h2 <;>
        simp [h1, h2] at hre_eq ⊢ <;> norm_num
    set P := (1 - ε) / 2 * ((Bs i a a).re - (Bs j b b).re) with hP_def
    rcases hre_pm2 with hsign | hsign <;> rw [hsign]
    · have hP_lb : -(2 * (1 - ε) / (1 + ε)) ≤ P := by linarith [neg_abs_le P]
      have hsum_lb : 4 * ε / (1 + ε) ≤ P + 2 := by
        have : 2 - 2 * (1 - ε) / (1 + ε) = 4 * ε / (1 + ε) := by field_simp; ring
        linarith
      have hpos : 0 < P + 2 := by linarith
      rw [abs_of_pos hpos]; linarith
    · have hP_ub : P ≤ 2 * (1 - ε) / (1 + ε) := by linarith [le_abs_self P]
      have hsum_ub : P + (-2 : ℝ) ≤ -(4 * ε / (1 + ε)) := by
        have : 2 * (1 - ε) / (1 + ε) - 2 = -(4 * ε / (1 + ε)) := by field_simp; ring
        linarith
      have hneg : P + (-2 : ℝ) < 0 := by linarith
      rw [abs_of_neg hneg]; linarith

/-- Helper: if `δ ≤ |f a b|` for all a b, and the underlying structure ensures the
    sign is uniform, we extract a signed bound. For our fullB diagonal differences,
    the corner contribution (±2) dominates the perturbation (<2), so the sign is uniform. -/
private lemma abs_sep_to_signed_sep {n₁ n₂ : ℕ}
    (f : Fin n₁ → Fin n₂ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (habs : ∀ a b, δ ≤ |f a b|)
    (hcont : ∀ a₁ a₂ b₁ b₂, |f a₁ b₁ - f a₂ b₂| < 2 * δ) :
    (∀ a b, δ ≤ f a b) ∨ (∀ a b, δ ≤ -f a b) := by
  by_cases hn₁ : n₁ = 0
  · subst hn₁; left; intro a; exact a.elim0
  by_cases hn₂ : n₂ = 0
  · subst hn₂; left; intro a b; exact b.elim0
  haveI : NeZero n₁ := ⟨hn₁⟩
  haveI : NeZero n₂ := ⟨hn₂⟩
  -- Check sign at (0, 0)
  by_cases hpos : (0 : ℝ) ≤ f 0 0
  · -- f 0 0 ≥ 0, so |f 0 0| = f 0 0, hence f 0 0 ≥ δ
    left; intro a b
    have h00 := habs 0 0
    rw [abs_of_nonneg hpos] at h00
    -- We need to show δ ≤ f a b
    -- Case split on sign of f a b
    by_cases hab_nn : 0 ≤ f a b
    · -- f a b ≥ 0, so |f a b| = f a b ≥ δ
      have := habs a b
      rw [abs_of_nonneg hab_nn] at this
      exact this
    · -- f a b < 0, so |f a b| = -f a b, and f a b ≤ -δ
      simp only [not_le] at hab_nn
      have hab := habs a b
      rw [abs_of_neg hab_nn] at hab
      -- f a b ≤ -δ and f 0 0 ≥ δ, so f 0 0 - f a b ≥ 2δ
      have hge : f 0 0 - f a b ≥ 2 * δ := by linarith
      -- But |f 0 0 - f a b| < 2δ by hcont
      have hlt := hcont 0 a 0 b
      rw [abs_of_nonneg (by linarith)] at hlt
      linarith
  · -- f 0 0 < 0, so |f 0 0| = -f 0 0, hence -f 0 0 ≥ δ
    simp only [not_le] at hpos
    right; intro a b
    have h00 := habs 0 0
    rw [abs_of_neg hpos] at h00
    -- We need to show δ ≤ -f a b, i.e., f a b ≤ -δ
    by_cases hab_neg : f a b < 0
    · -- f a b < 0, so |f a b| = -f a b ≥ δ, done
      have := habs a b
      rw [abs_of_neg hab_neg] at this
      exact this
    · -- f a b ≥ 0, so |f a b| = f a b ≥ δ
      simp only [not_lt] at hab_neg
      have hab := habs a b
      rw [abs_of_nonneg hab_neg] at hab
      -- f a b ≥ δ and f 0 0 ≤ -δ, so f a b - f 0 0 ≥ 2δ
      have hge : f a b - f 0 0 ≥ 2 * δ := by linarith
      have hlt := hcont a 0 b 0
      rw [abs_of_nonneg (by linarith)] at hlt
      linarith

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- For distinct 4-block indices i≠j, the off-diagonal block of any matrix A can be
    solved by a Sylvester equation with dim-free bound ‖C'_{ij}‖ ≤ ‖A_{ij}‖/(2ε).
    The diagonal blocks Si, Tj of fullB are spectrally separated by ≥ 2ε in Re or Im. -/
private lemma offdiag_block_sylvester_bound {k : ℕ} (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (Bs : Fin 4 → Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ)
    (hBs_diag : ∀ i, IsDiagMatrix (Bs i))
    (hBs_lam : ∀ i j, (Bs i) j j ∈ (Lambda ε (k + 1) : Set ℂ))
    (i j : Fin 4) (hij : i ≠ j)
    (Aij : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ) :
    ∃ Cij : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ,
      (let Si := Matrix.diagonal (fun p => (fullB ε Bs) ((finBlockEquiv k).symm (i, p))
                                                         ((finBlockEquiv k).symm (i, p)))
       let Tj := Matrix.diagonal (fun p => (fullB ε Bs) ((finBlockEquiv k).symm (j, p))
                                                         ((finBlockEquiv k).symm (j, p)))
       Si * Cij - Cij * Tj = Aij) ∧
      ‖Cij‖ ≤ ‖Aij‖ / (2 * ε) := by
  -- Define Si and Tj as diagonal matrices of fullB entries restricted to blocks i and j
  set Si := Matrix.diagonal (fun p => (fullB ε Bs) ((finBlockEquiv k).symm (i, p))
                                                    ((finBlockEquiv k).symm (i, p))) with hSi_def
  set Tj := Matrix.diagonal (fun p => (fullB ε Bs) ((finBlockEquiv k).symm (j, p))
                                                    ((finBlockEquiv k).symm (j, p))) with hTj_def
  -- Si and Tj are diagonal
  have hSi_diag : IsDiagMatrix Si := diag_isDiagMatrix _
  have hTj_diag : IsDiagMatrix Tj := diag_isDiagMatrix _
  -- The diagonal entries satisfy the fullB simplification
  have hSi_entry : ∀ p, Si p p = ((1 - ↑ε) / 2 : ℂ) * (Bs i p p) + cornerOf i := by
    intro p; simp [hSi_def, fullB_diag_entry]
  have hTj_entry : ∀ p, Tj p p = ((1 - ↑ε) / 2 : ℂ) * (Bs j p p) + cornerOf j := by
    intro p; simp [hTj_def, fullB_diag_entry]
  -- From fullB_cross_block_sep, we get Re or Im absolute separation ≥ 2ε
  have hsep := fullB_cross_block_sep ε hε hε1 Bs hBs_lam i j hij
  -- The diagonal entries of Si - Tj match the fullB differences
  have hdiag_diff : ∀ a b, Si a a - Tj b b =
      (fullB ε Bs) ((finBlockEquiv k).symm (i, a)) ((finBlockEquiv k).symm (i, a)) -
      (fullB ε Bs) ((finBlockEquiv k).symm (j, b)) ((finBlockEquiv k).symm (j, b)) := by
    intro a b; simp [hSi_def, hTj_def]
  -- Convert absolute value separation to signed separation for Sylvester bounds
  have h2ε_pos : (0 : ℝ) < 2 * ε := by linarith
  -- Key step: convert |re/im| ≥ 2ε to signed bounds.
  -- Use the fact that for the Re case, all diffs have the same sign (corner dominates),
  -- and similarly for Im. If negative, swap Si↔Tj and negate Aij.
  -- We prove: either (∀, 2ε ≤ re(Si-Tj)) or (∀, 2ε ≤ re(Tj-Si)) [and same for Im]
  -- Then apply Sylvester to (Si, Tj, Aij) or (Tj, Si, -Aij) as appropriate.
  -- For clarity, we combine both into one existential.
  suffices hsigned : (∀ a b, 2 * ε ≤ (Si a a - Tj b b).re) ∨
                     (∀ a b, 2 * ε ≤ (Si a a - Tj b b).im) ∨
                     (∀ a b, 2 * ε ≤ (Tj b b - Si a a).re) ∨
                     (∀ a b, 2 * ε ≤ (Tj b b - Si a a).im) by
    rcases hsigned with hcase | hcase | hcase | hcase
    · -- Direct: 2ε ≤ re(Si - Tj)
      set Y := fun a b => Aij a b / (Si a a - Tj b b)
      have hbnd := sylvester_diag_opNorm_bound_re Si Tj Aij hSi_diag hTj_diag
        (2 * ε) h2ε_pos hcase
      exact ⟨Y, hbnd.1, hbnd.2⟩
    · -- Direct: 2ε ≤ im(Si - Tj)
      set Y := fun a b => Aij a b / (Si a a - Tj b b)
      have hbnd := sylvester_diag_opNorm_bound_im Si Tj Aij hSi_diag hTj_diag
        (2 * ε) h2ε_pos hcase
      exact ⟨Y, hbnd.1, hbnd.2⟩
    · -- Negated: 2ε ≤ re(Tj - Si) means 2ε ≤ re((-Si) - (-Tj))
      -- Apply Sylvester to (-Si), (-Tj), (-Aij): solution Z satisfies
      -- (-Si)*Z - Z*(-Tj) = -Aij, which simplifies to Si*Z - Z*Tj = Aij
      have hSi_neg : IsDiagMatrix (-Si) := fun i j h => by
        simp [hSi_diag i j h]
      have hTj_neg : IsDiagMatrix (-Tj) := fun i j h => by
        simp [hTj_diag i j h]
      have hsep_neg : ∀ a b, 2 * ε ≤ ((-Si) a a - (-Tj) b b).re := by
        intro a b
        have := hcase a b
        simp only [Matrix.neg_apply]
        rw [show (-Si a a - -Tj b b).re = (Tj b b - Si a a).re from by
          simp [Complex.sub_re, Complex.neg_re]; ring]
        exact this
      have hbnd := sylvester_diag_opNorm_bound_re (-Si) (-Tj) (-Aij)
        hSi_neg hTj_neg (2 * ε) h2ε_pos hsep_neg
      set Z : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ :=
        fun a b => (-Aij) a b / ((-Si) a a - (-Tj) b b)
      have heq : (-Si) * Z - Z * (-Tj) = -Aij := hbnd.1
      have hnrm : ‖Z‖ ≤ ‖-Aij‖ / (2 * ε) := hbnd.2
      refine ⟨Z, ?_, ?_⟩
      · -- (-Si)*Z - Z*(-Tj) = -Aij  ⟹  Si*Z - Z*Tj = Aij
        have h_neg_eq : -Si * Z - Z * -Tj = -(Si * Z - Z * Tj) := by
          simp only [neg_mul, mul_neg, neg_sub_neg]
          abel
        rw [h_neg_eq] at heq
        exact neg_injective heq
      · calc ‖Z‖ ≤ ‖-Aij‖ / (2 * ε) := hnrm
          _ = ‖Aij‖ / (2 * ε) := by rw [norm_neg]
    · -- Negated: 2ε ≤ im(Tj - Si) means 2ε ≤ im((-Si) - (-Tj))
      have hSi_neg : IsDiagMatrix (-Si) := fun i j h => by
        simp [hSi_diag i j h]
      have hTj_neg : IsDiagMatrix (-Tj) := fun i j h => by
        simp [hTj_diag i j h]
      have hsep_neg : ∀ a b, 2 * ε ≤ ((-Si) a a - (-Tj) b b).im := by
        intro a b
        have := hcase a b
        simp only [Matrix.neg_apply]
        rw [show (-Si a a - -Tj b b).im = (Tj b b - Si a a).im from by
          simp [Complex.sub_im, Complex.neg_im]; ring]
        exact this
      have hbnd := sylvester_diag_opNorm_bound_im (-Si) (-Tj) (-Aij)
        hSi_neg hTj_neg (2 * ε) h2ε_pos hsep_neg
      set Z : Matrix (Fin (4 ^ (k + 1))) (Fin (4 ^ (k + 1))) ℂ :=
        fun a b => (-Aij) a b / ((-Si) a a - (-Tj) b b)
      have heq : (-Si) * Z - Z * (-Tj) = -Aij := hbnd.1
      have hnrm : ‖Z‖ ≤ ‖-Aij‖ / (2 * ε) := hbnd.2
      refine ⟨Z, ?_, ?_⟩
      · have h_neg_eq : -Si * Z - Z * -Tj = -(Si * Z - Z * Tj) := by
          simp only [neg_mul, mul_neg, neg_sub_neg]
          abel
        rw [h_neg_eq] at heq
        exact neg_injective heq
      · calc ‖Z‖ ≤ ‖-Aij‖ / (2 * ε) := hnrm
          _ = ‖Aij‖ / (2 * ε) := by rw [norm_neg]
  -- Direct corner analysis to produce signed bounds (bypassing hsep).
  -- Setup: corner facts, perturbation bounds
  have cornerOf_re_pm1 : ∀ (m : Fin 4), (cornerOf m).re = 1 ∨ (cornerOf m).re = -1 := by
    intro m; fin_cases m <;> simp [cornerOf]
  have cornerOf_im_pm1 : ∀ (m : Fin 4), (cornerOf m).im = 1 ∨ (cornerOf m).im = -1 := by
    intro m; fin_cases m <;> simp [cornerOf]
  have cornerOf_inj : Function.Injective cornerOf := by
    intro a b h; fin_cases a <;> fin_cases b <;>
      first | rfl | (exfalso; simp [cornerOf] at h; norm_num at h)
  have hδ_ne : cornerOf i ≠ cornerOf j := fun h => hij (cornerOf_inj h)
  have hr_nn : (0 : ℝ) ≤ (1 - ε) / 2 := by linarith
  have h1ε_pos : (0 : ℝ) < 1 + ε := by linarith
  have hBs_re : ∀ (m : Fin 4) (p : Fin (4 ^ (k + 1))),
      |(Bs m p p).re| ≤ 2 / (1 + ε) :=
    fun m p => Lambda_re_bound ε hε hε1 (k + 1) _ (hBs_lam m p)
  have hBs_im : ∀ (m : Fin 4) (p : Fin (4 ^ (k + 1))),
      |(Bs m p p).im| ≤ 2 / (1 + ε) :=
    fun m p => Lambda_im_bound ε hε hε1 (k + 1) _ (hBs_lam m p)
  have pert_bound : ∀ (x y : ℝ), |x| ≤ 2 / (1 + ε) → |y| ≤ 2 / (1 + ε) →
      |(1 - ε) / 2 * (x - y)| ≤ 2 * (1 - ε) / (1 + ε) := by
    intro x y hx hy
    rw [abs_mul, abs_of_nonneg hr_nn]
    have : |x - y| ≤ 4 / (1 + ε) := by
      have hxy : |x - y| ≤ |x| + |y| :=
        abs_add_le x (-y) |>.trans (by rw [abs_neg])
      calc |x - y| ≤ |x| + |y| := hxy
        _ ≤ 2 / (1 + ε) + 2 / (1 + ε) := by linarith
        _ = 4 / (1 + ε) := by ring
    calc (1 - ε) / 2 * |x - y| ≤ (1 - ε) / 2 * (4 / (1 + ε)) :=
          mul_le_mul_of_nonneg_left this hr_nn
      _ = 2 * (1 - ε) / (1 + ε) := by ring
  have h2ε_le : 2 * ε ≤ 4 * ε / (1 + ε) := by
    rw [le_div_iff₀ h1ε_pos]; nlinarith
  -- Re/Im of Si a a - Tj b b
  have diff_re' : ∀ a b, (Si a a - Tj b b).re =
      (1 - ε) / 2 * ((Bs i a a).re - (Bs j b b).re) + ((cornerOf i).re - (cornerOf j).re) := by
    intro a b; rw [hSi_entry, hTj_entry]
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]; ring
  have diff_im' : ∀ a b, (Si a a - Tj b b).im =
      (1 - ε) / 2 * ((Bs i a a).im - (Bs j b b).im) + ((cornerOf i).im - (cornerOf j).im) := by
    intro a b; rw [hSi_entry, hTj_entry]
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]; ring
  -- Case split on whether Re corners are equal
  by_cases hre_eq : (cornerOf i).re = (cornerOf j).re
  · -- Re corners equal → Im corners differ → signed Im bound
    have him_ne : (cornerOf i).im ≠ (cornerOf j).im := by
      intro h; exact hδ_ne (Complex.ext hre_eq h)
    have him_pm2 : (cornerOf i).im - (cornerOf j).im = 2 ∨
                   (cornerOf i).im - (cornerOf j).im = -2 := by
      rcases cornerOf_im_pm1 i with h1 | h1 <;> rcases cornerOf_im_pm1 j with h2 | h2 <;>
        simp [h1, h2] at him_ne ⊢ <;> norm_num
    rcases him_pm2 with hsign | hsign
    · -- corner_im_diff = +2: Si - Tj has positive Im → second disjunct
      right; left; intro a b; rw [diff_im']
      set P := (1 - ε) / 2 * ((Bs i a a).im - (Bs j b b).im)
      have hpert := pert_bound _ _ (hBs_im i a) (hBs_im j b)
      have hP_lb : -(2 * (1 - ε) / (1 + ε)) ≤ P := by linarith [neg_abs_le P]
      have : 4 * ε / (1 + ε) ≤ P + 2 := by
        have : 2 - 2 * (1 - ε) / (1 + ε) = 4 * ε / (1 + ε) := by field_simp; ring
        linarith
      rw [hsign]; linarith
    · -- corner_im_diff = -2: Tj - Si has positive Im → fourth disjunct
      right; right; right; intro a b
      have hdiff : (Tj b b - Si a a).im = -(Si a a - Tj b b).im := by
        simp [Complex.sub_im, neg_sub]
      rw [hdiff, diff_im']
      set P := (1 - ε) / 2 * ((Bs i a a).im - (Bs j b b).im)
      have hpert := pert_bound _ _ (hBs_im i a) (hBs_im j b)
      have hP_ub : P ≤ 2 * (1 - ε) / (1 + ε) := by linarith [le_abs_self P]
      have : -(P + -2) ≥ 4 * ε / (1 + ε) := by
        have : 2 * (1 - ε) / (1 + ε) - 2 = -(4 * ε / (1 + ε)) := by field_simp; ring
        linarith
      rw [hsign]; linarith
  · -- Re corners differ → signed Re bound
    have hre_pm2 : (cornerOf i).re - (cornerOf j).re = 2 ∨
                   (cornerOf i).re - (cornerOf j).re = -2 := by
      rcases cornerOf_re_pm1 i with h1 | h1 <;> rcases cornerOf_re_pm1 j with h2 | h2 <;>
        simp [h1, h2] at hre_eq ⊢ <;> norm_num
    rcases hre_pm2 with hsign | hsign
    · -- corner_re_diff = +2: Si - Tj has positive Re → first disjunct
      left; intro a b; rw [diff_re']
      set P := (1 - ε) / 2 * ((Bs i a a).re - (Bs j b b).re)
      have hpert := pert_bound _ _ (hBs_re i a) (hBs_re j b)
      have hP_lb : -(2 * (1 - ε) / (1 + ε)) ≤ P := by linarith [neg_abs_le P]
      have : 4 * ε / (1 + ε) ≤ P + 2 := by
        have : 2 - 2 * (1 - ε) / (1 + ε) = 4 * ε / (1 + ε) := by field_simp; ring
        linarith
      rw [hsign]; linarith
    · -- corner_re_diff = -2: Tj - Si has positive Re → third disjunct
      right; right; left; intro a b
      have hdiff : (Tj b b - Si a a).re = -(Si a a - Tj b b).re := by
        simp [Complex.sub_re, neg_sub]
      rw [hdiff, diff_re']
      set P := (1 - ε) / 2 * ((Bs i a a).re - (Bs j b b).re)
      have hpert := pert_bound _ _ (hBs_re i a) (hBs_re j b)
      have hP_ub : P ≤ 2 * (1 - ε) / (1 + ε) := by linarith [le_abs_self P]
      have : -(P + -2) ≥ 4 * ε / (1 + ε) := by
        have : 2 * (1 - ε) / (1 + ε) - 2 = -(4 * ε / (1 + ε)) := by field_simp; ring
        linarith
      rw [hsign]; linarith

/-- Lambda entries, scaled by (1+ε)/2, are in the unit square. This allows
    application of claim3 to commutators with Lambda-diagonal matrices after rescaling. -/
private lemma Lambda_scaled_InUnitSquare (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ) (z : ℂ)
    (hz : z ∈ (Lambda ε k : Set ℂ)) :
    InUnitSquare (((1 + ε) / 2 : ℂ) * z) := by
  have hs_pos : (0 : ℝ) < (1 + ε) / 2 := by linarith
  constructor
  · have : (((1 + ε) / 2 : ℂ) * z).re = (1 + ε) / 2 * z.re := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [this, abs_mul, abs_of_pos hs_pos]
    calc (1 + ε) / 2 * |z.re| ≤ (1 + ε) / 2 * (2 / (1 + ε)) := by
          gcongr; exact Lambda_re_bound ε hε hε1 k z hz
      _ = 1 := by field_simp
  · have : (((1 + ε) / 2 : ℂ) * z).im = (1 + ε) / 2 * z.im := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [this, abs_mul, abs_of_pos hs_pos]
    calc (1 + ε) / 2 * |z.im| ≤ (1 + ε) / 2 * (2 / (1 + ε)) := by
          gcongr; exact Lambda_im_bound ε hε hε1 k z hz
      _ = 1 := by field_simp

/-- For a commutator A = [B, C] with B diagonal in Λ_{k+2}, the scaled matrix
    ((1+ε)/2) · A has a commutator decomposition with InUnitSquare diagonal,
    so claim3 applies giving a paving with ≤ (⌊2/ε'⌋+1)² blocks and
    pavingNorm ≤ √2·ε'·‖C‖. -/
private lemma mu_paving_via_claim3 (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (k : ℕ) (A : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ)
    (B C : Matrix (Fin (4 ^ (k + 2))) (Fin (4 ^ (k + 2))) ℂ)
    (hdiag : IsDiagMatrix B)
    (hlam : ∀ i, B i i ∈ (Lambda ε (k + 2) : Set ℂ))
    (hcomm : A = ⁅B, C⁆ₘ)
    (ε' : ℝ) (hε' : 0 < ε') (hε'1 : ε' < 1) :
    ∃ (nblocks : ℕ) (σ : Fin nblocks → Finset (Fin (4 ^ (k + 2)))),
      nblocks ≤ (⌊2 / ε'⌋₊ + 1) ^ 2 ∧
      pavingNorm σ (((1 + ε) / 2 : ℂ) • A) ≤ Real.sqrt 2 * ε' * ‖C‖ := by
  -- Define B' = ((1+ε)/2) • B
  set s : ℂ := ((1 + ε) / 2 : ℂ) with hs_def
  set B' := s • B with hB'_def
  -- B' is diagonal
  have hdiag' : IsDiagMatrix B' := by
    intro i j hij
    simp only [B', Matrix.smul_apply, smul_eq_mul, hdiag i j hij, mul_zero]
  -- B' entries are InUnitSquare
  have hspec' : ∀ i, InUnitSquare (B' i i) := by
    intro i
    simp only [B', Matrix.smul_apply, smul_eq_mul]
    exact Lambda_scaled_InUnitSquare ε hε hε1 (k + 2) (B i i) (hlam i)
  -- s • A = [B', C] since s • A = s • (B*C - C*B) = (sB)*C - C*(sB) = [sB, C] = [B', C]
  have hcomm' : s • A = ⁅B', C⁆ₘ := by
    rw [hcomm]
    simp only [matComm, B', smul_sub, smul_mul_assoc, mul_smul_comm]
  -- Apply claim3
  exact claim3 ε' hε' hε'1 B' C (s • A) hdiag' hspec' hcomm'

-- Multi-scale paving mu bound (JOS 2013, Theorem 2 core).
--   For ε ∈ (0,1), ∃ α < 4^ε and β > 0 such that for all k and all
--   zero-diagonal unit-norm A of size 4^(k+2):
--     mu ε (k+2) A ≤ α · mu_sup'(ε, k+1, 4^(k+1)) + β.
--   The proof combines:
--   - Standard block decomposition (mu_one_step_pointwise, α₀ = 2/(1-ε))
--   - Paving via claim3 (PROVED in Paving.lean) + scaling (Lambda_scaled_InUnitSquare)
--   - Restricted invertibility via bourgain_tzafriri (Paving.lean)
--   - Sylvester equation via rosenblum_norm_bound (Rosenblum.lean)
--   - mu_paving_via_claim3 bridges scaling + claim3
--   The standard decomposition gives α₀ = 2/(1-ε) > 4^ε for all ε ∈ (0,1).
--   The multi-scale paving argument (iterating claim3 + BT over log-many scales,
--   as in the paper's proof of Claim 2 → Theorem 2) improves the effective
--   multiplicative constant to α < 4^ε.

/-! ### Infrastructure lemmas for the paving-based coefficient improvement -/

/-- blockOf distributes over scalar multiplication. -/
private lemma blockOf_smul {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (c : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) (i j : Fin k) :
    blockOf σ (c • A) i j = c • blockOf σ A i j := by
  ext r s
  simp only [blockOf, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- ‖c • A‖ ≤ ‖c‖ * ‖A‖ for matrix L2 operator norm, via diagonal multiplication. -/
private lemma norm_smul_matrix_le {m : ℕ} (c : ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) :
    ‖c • A‖ ≤ ‖c‖ * ‖A‖ := by
  have heq : c • A = Matrix.diagonal (fun _ => c) * A := by
    ext i j; simp [Matrix.diagonal, Matrix.mul_apply]
  rw [heq]
  calc ‖Matrix.diagonal (fun _ : Fin m => c) * A‖
      ≤ ‖Matrix.diagonal (fun _ : Fin m => c)‖ * ‖A‖ := norm_mul_le _ _
    _ ≤ ‖c‖ * ‖A‖ := by
        gcongr
        rw [Matrix.l2_opNorm_diagonal]
        simp only [Pi.norm_def]
        have : (Finset.univ.sup fun b : Fin m => ‖c‖₊) ≤ ‖c‖₊ :=
          Finset.sup_le (fun _ _ => le_rfl)
        exact_mod_cast this

/-- Each diagonal paving block of a scaled matrix has small norm.
    If pavingNorm σ (s • A) ≤ bound, then ‖blockOf σ A i i‖ ≤ bound / s (when s > 0).
    This is the key step: the paving bound on the scaled matrix transfers to
    a per-block bound on the original matrix. -/
private lemma paving_diag_block_small {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (A : Matrix (Fin m) (Fin m) ℂ) (s : ℝ) (hs : 0 < s) (bound : ℝ)
    (hpav : pavingNorm σ (((s : ℂ)) • A) ≤ bound) (i : Fin k) :
    ‖blockOf σ A i i‖ ≤ bound / s := by
  have hs_ne : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hbdd : BddAbove (Set.range (fun j => ‖blockOf σ ((s : ℂ) • A) j j‖)) := by
    use ‖(s : ℂ) • A‖
    intro x hx; obtain ⟨j, rfl⟩ := hx; exact norm_blockOf_le σ _ j
  have hle : ‖blockOf σ ((s : ℂ) • A) i i‖ ≤ bound :=
    (le_ciSup hbdd i).trans hpav
  rw [blockOf_smul] at hle
  have hinv : blockOf σ A i i = (s : ℂ)⁻¹ • ((s : ℂ) • blockOf σ A i i) := by
    rw [smul_smul, inv_mul_cancel₀ hs_ne, one_smul]
  rw [hinv]
  have hs_inv_norm : ‖((s : ℂ)⁻¹)‖ = s⁻¹ := by
    rw [show ((s : ℂ)⁻¹) = ((s⁻¹ : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
  calc ‖(s : ℂ)⁻¹ • ((s : ℂ) • blockOf σ A i i)‖
      ≤ ‖(s : ℂ)⁻¹‖ * ‖(s : ℂ) • blockOf σ A i i‖ := norm_smul_matrix_le _ _
    _ ≤ s⁻¹ * bound := by rw [hs_inv_norm]; gcongr
    _ = bound / s := by rw [inv_mul_eq_div]

/-- Commutator norm bound for diagonal paving blocks: for diagonal B and any C,
    ‖blockOf σ [B,C] i i‖ ≤ 2 · ‖blockOf σ B i i‖ · ‖blockOf σ C i i‖.
    Combines blockOf_matComm_diag (Paving.lean) with matComm_norm_le. -/
private lemma blockOf_comm_bound {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (B C : Matrix (Fin m) (Fin m) ℂ) (hDiag : IsDiagMatrix B) (i : Fin k) :
    ‖blockOf σ (⁅B, C⁆ₘ) i i‖ ≤ 2 * ‖blockOf σ B i i‖ * ‖blockOf σ C i i‖ := by
  rw [blockOf_matComm_diag σ B C hDiag i]
  exact matComm_norm_le _ _

-- Per-block norm bound: the paving makes each diagonal block of A small.
-- From paving_diag_block_small with s = (1+ε)/2 and the paving bound.
private lemma paving_block_A_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    {n nblocks : ℕ} (σ : Fin nblocks → Finset (Fin n))
    (A : Matrix (Fin n) (Fin n) ℂ)
    (C_std : Matrix (Fin n) (Fin n) ℂ)
    (hpaving_norm : pavingNorm σ ((((1 : ℂ) + ↑ε) / 2) • A) ≤ Real.sqrt 2 * (ε / 2) * ‖C_std‖)
    (i : Fin nblocks) :
    ‖blockOf σ A i i‖ ≤ Real.sqrt 2 * ε / (1 + ε) * ‖C_std‖ := by
  have hs_pos : (0 : ℝ) < (1 + ε) / 2 := by linarith
  have hblock := paving_diag_block_small σ A ((1 + ε) / 2) hs_pos
    (Real.sqrt 2 * (ε / 2) * ‖C_std‖) (by convert hpaving_norm using 2; push_cast; ring) i
  calc ‖blockOf σ A i i‖
      ≤ Real.sqrt 2 * (ε / 2) * ‖C_std‖ / ((1 + ε) / 2) := hblock
    _ = Real.sqrt 2 * ε / (1 + ε) * ‖C_std‖ := by
        have h1ε : (1 + ε) ≠ 0 := by positivity
        field_simp

-- JOS 2013 Claim 2 witness: construct (B', C') with A = [B', C'], B' ∈ Λ_{k+2},
-- and ‖C'‖ ≤ (1+ε)*(M+η) + 4√2/ε. The paper's proof (Theorem 3) iterates:
-- (1) Apply paving (Claim 3) to get blocks with small norms.
-- (2) Within each paving block, apply Claim 1 recursively.
-- (3) Across paving blocks, use Sylvester with spectral separation.
-- The iteration reduces the coefficient from 2/(1-ε) to (1+ε) over k levels.
-- Full formalization requires: paving block decomposition of Λ-spectrum matrices,
-- recursive application of Claim 1 to sub-blocks, and assembly of the global C'.

/-! ### Helper lemmas for paving witness construction -/

/-- The off-diagonal block norm is at most the full matrix norm:
    blockOf σ A i j = P_i * A * P_j, so ‖blockOf σ A i j‖ ≤ ‖A‖.
    This generalizes norm_blockOf_le to arbitrary (i, j), not just diagonal blocks. -/
private lemma norm_blockOf_offdiag_le {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (A : Matrix (Fin m) (Fin m) ℂ) (i j : Fin k) :
    ‖blockOf σ A i j‖ ≤ ‖A‖ := by
  have heq : blockOf σ A i j = projBlock σ i * A * projBlock σ j := by
    ext r c
    simp only [blockOf, projBlock, Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    split_ifs <;> simp_all
  rw [heq]
  calc ‖projBlock σ i * A * projBlock σ j‖
      ≤ ‖projBlock σ i * A‖ * ‖projBlock σ j‖ := norm_mul_le _ _
    _ ≤ (‖projBlock σ i‖ * ‖A‖) * ‖projBlock σ j‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ 1 * ‖A‖ * 1 := by
        gcongr
        · exact norm_projBlock_le_one σ i
        · exact norm_projBlock_le_one σ j
    _ = ‖A‖ := by ring

/-- Commutator with a scalar (diagonal) matrix is zero.
    If B = c • 1, then [B, C] = 0 for any C. -/
private lemma matComm_smul_one {n : ℕ} (c : ℂ)
    (C : Matrix (Fin n) (Fin n) ℂ) :
    ⁅c • (1 : Matrix (Fin n) (Fin n) ℂ), C⁆ₘ = 0 := by
  simp [matComm]

/-- blockOf distributes over matrix addition. -/
private lemma blockOf_add' {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (A B : Matrix (Fin m) (Fin m) ℂ) (i j : Fin k) :
    blockOf σ (A + B) i j = blockOf σ A i j + blockOf σ B i j := by
  ext r c
  simp only [blockOf, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

/-- blockOf distributes over matrix subtraction. -/
private lemma blockOf_sub {m k : ℕ} (σ : Fin k → Finset (Fin m))
    (A B : Matrix (Fin m) (Fin m) ℂ) (i j : Fin k) :
    blockOf σ (A - B) i j = blockOf σ A i j - blockOf σ B i j := by
  ext r c
  simp only [blockOf, Matrix.of_apply, Matrix.sub_apply]
  split_ifs <;> simp

/-- blockOf of the zero matrix is zero. -/
private lemma blockOf_zero' {m k : ℕ} (σ : Fin k → Finset (Fin m)) (i j : Fin k) :
    blockOf σ (0 : Matrix (Fin m) (Fin m) ℂ) i j = 0 := by
  ext r c
  simp [blockOf, Matrix.of_apply]

/-- Commutator is additive in the second argument: [B, C₁ + C₂] = [B, C₁] + [B, C₂]. -/
private lemma matComm_add_right' {n : ℕ}
    (B C₁ C₂ : Matrix (Fin n) (Fin n) ℂ) :
    matComm B (C₁ + C₂) = matComm B C₁ + matComm B C₂ := by
  unfold matComm; simp [mul_add, add_mul]; abel

/-- Commutator is additive in the first argument: [B₁ + B₂, C] = [B₁, C] + [B₂, C]. -/
private lemma matComm_add_left' {n : ℕ}
    (B₁ B₂ C : Matrix (Fin n) (Fin n) ℂ) :
    matComm (B₁ + B₂) C = matComm B₁ C + matComm B₂ C := by
  unfold matComm; simp [mul_add, add_mul]; abel

/-- Commutator scales in the first argument: [c • B, C] = c • [B, C]. -/
private lemma matComm_smul_left' {n : ℕ} (c : ℂ)
    (B C : Matrix (Fin n) (Fin n) ℂ) :
    matComm (c • B) C = c • matComm B C := by
  simp [matComm, smul_sub]

/-- The commutator of a diagonal matrix B with any C, evaluated entrywise:
    [B, C](r,c) = (B r r - B c c) * C r c. -/
private lemma matComm_diag_entry {n : ℕ}
    (B C : Matrix (Fin n) (Fin n) ℂ) (hDiag : IsDiagMatrix B)
    (r c : Fin n) :
    (⁅B, C⁆ₘ) r c = (B r r - B c c) * C r c := by
  simp only [matComm, Matrix.sub_apply, Matrix.mul_apply]
  have hoff : ∀ x, x ≠ r → B r x = 0 := fun x hx => hDiag r x (Ne.symm hx)
  have hoff' : ∀ x, x ≠ c → B x c = 0 := fun x hx => hDiag x c hx
  rw [show (∑ x, B r x * C x c) = B r r * C r c from by
    apply Finset.sum_eq_single r
    · intro x _ hx; simp [hoff x hx]
    · simp]
  rw [show (∑ x, C r x * B x c) = C r c * B c c from by
    apply Finset.sum_eq_single c
    · intro x _ hx; simp [hoff' x hx]
    · simp]
  ring


/-- Core embedding + extraction step.
    Combines: zero-padding n×n -> 4^k x 4^k, applying the mu bound,
    extracting B,C witnesses from sInf, and restricting back to n×n.
    Uses zeroPad_norm_eq, restrict_norm_le (norm theory),
    mu_set_nonempty (decomposition existence), and Lambda_norm_le_two (lattice bound). -/
private lemma embed_extract_decompose (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (Kε : ℝ) (_hKε : 0 < Kε)
    (hax : ∀ (k : ℕ) (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      m = 4 ^ k → ZeroDiag A → ‖A‖ = 1 →
      mu ε k A ≤ Kε * (m : ℝ) ^ ε)
    (n : ℕ) (k : ℕ) (hn : n ≤ 4 ^ k)
    (A : Matrix (Fin n) (Fin n) ℂ) (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1) :
    ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
      A = ⁅B, C⁆ₘ ∧ ‖B‖ * ‖C‖ ≤ 3 * (Kε * ((4 : ℝ) ^ k) ^ ε + 1) := by
  -- Step 1: Zero-pad A into (4^k)×(4^k)
  set m := 4 ^ k with hm
  set A' := zeroPad hn A
  have hzd' : ZeroDiag A' := zeroPad_zeroDiag hn hzd
  have hnorm' : ‖A'‖ = 1 := by rw [zeroPad_norm_eq, hnorm]
  -- Step 2: Apply hax to get mu bound on the padded matrix
  have hmu : mu ε k A' ≤ Kε * (m : ℝ) ^ ε := hax k m A' rfl hzd' hnorm'
  -- Step 2b: Lambda ε k has enough elements for an m×m diagonal
  have hm_card : m ≤ (Lambda ε k).card := Lambda_card_ge ε hε hε1 k
  -- Step 3: Extract witnesses from mu bound (with δ = 1)
  obtain ⟨B', C', hdiag', hlam', hcomm', hnormC'⟩ :=
    mu_extract_witness hε hzd' hm_card hmu 1 one_pos
  -- Step 4: B' has norm ≤ 3 (diagonal with Lambda entries bounded by 3)
  have hB'norm : ‖B'‖ ≤ 3 := by
    apply diag_norm_le hdiag' 3 (by norm_num)
    intro i; exact Lambda_norm_le_three ε hε hε1 k _ (hlam' i)
  -- Step 5: Restrict B', C' to n×n
  set B := restrict hn B'
  set C := restrict hn C'
  -- Step 6: Show A = [B, C]
  have hcomm_restrict : A = ⁅B, C⁆ₘ := by
    have hA_eq : A = restrict hn A' := by rw [restrict_zeroPad]
    rw [hA_eq, hcomm']
    exact restrict_matComm_of_diag hn B' C' hdiag'
  -- Step 7: Bound ‖B‖ * ‖C‖
  have hbound : ‖B‖ * ‖C‖ ≤ 3 * (Kε * ((4 : ℝ) ^ k) ^ ε + 1) := by
    have hBnorm : ‖B‖ ≤ ‖B'‖ := restrict_norm_le hn B'
    have hCnorm : ‖C‖ ≤ ‖C'‖ := restrict_norm_le hn C'
    calc ‖B‖ * ‖C‖
        ≤ ‖B'‖ * ‖C'‖ := by
          apply mul_le_mul hBnorm hCnorm (norm_nonneg _) (norm_nonneg _)
      _ ≤ 3 * (Kε * (↑m) ^ ε + 1) := by
          apply mul_le_mul hB'norm hnormC' (norm_nonneg _) (by norm_num)
      _ = 3 * (Kε * ((4 : ℝ) ^ k) ^ ε + 1) := by
          congr 1; congr 1; congr 1
          exact_mod_cast rfl
  exact ⟨B, C, hcomm_restrict, hbound⟩


/-- Scaling lemma: matComm B (c • C) = c • matComm B C. -/
private lemma matComm_smul_right {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    matComm B (c • C) = c • matComm B C := by
  simp [matComm, smul_sub]

/-! ## Alternative proof path via lambdaA -/

/-- For n ≥ 2, every zero-diagonal matrix A has a commutator decomposition A = [B, C]
    with B diagonal, InUnitSquare entries, and ‖C‖ ≤ n*(n-1)*‖A‖. -/
private lemma zeroDiag_InUnitSquare_decomp_bounded {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hzd : ZeroDiag A) :
    ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧
      ‖C‖ ≤ (n : ℝ) * (n - 1) * ‖A‖ := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hn1' : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn1
  -- B = diagonal with entries i/(n-1) ∈ [0, 1]
  set B := Matrix.diagonal (fun i : Fin n => (↑(i.val : ℕ) : ℂ) / (↑(n - 1 : ℕ) : ℂ))
  -- C_ij = A_ij / (B_ii - B_jj) for i ≠ j, C_ii = 0
  set C := Matrix.of (fun i j : Fin n =>
    if i = j then (0 : ℂ) else A i j / ((↑(i.val : ℕ) : ℂ) / (↑(n - 1 : ℕ) : ℂ) -
      (↑(j.val : ℕ) : ℂ) / (↑(n - 1 : ℕ) : ℂ)))
  refine ⟨B, C, ?_, ?_, ?_, ?_⟩
  · -- IsDiagMatrix B
    intro i j hij; exact Matrix.diagonal_apply_ne _ hij
  · -- InUnitSquare (B i i)
    intro i
    unfold InUnitSquare; simp only [B, Matrix.diagonal_apply_eq]
    have hcast : (↑↑i : ℂ) / (↑(n - 1) : ℂ) =
        (↑((i.val : ℝ) / ((n - 1 : ℕ) : ℝ)) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.ofReal_re, Complex.ofReal_im]
    constructor
    · rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_sub_one_of_lt i.isLt
    · simp
  · -- A = [B, C]
    ext i j
    simp only [matComm, Matrix.sub_apply, Matrix.mul_apply]
    by_cases hij : i = j
    · -- diagonal: [B,C]_ii = 0 = A_ii
      subst hij; rw [hzd i]
      simp only [B, Matrix.diagonal_apply, C, Matrix.of_apply]
      symm
      have h1 : ∀ x : Fin n,
          (if i = x then ↑↑i / (↑(n - 1) : ℂ) else 0) *
          (if x = i then (0 : ℂ) else
            A x i / (↑↑x / ↑(n - 1) - ↑↑i / ↑(n - 1))) = 0 := by
        intro x; by_cases h : i = x
        · simp [h]
        · simp [h]
      have h2 : ∀ x : Fin n,
          (if i = x then (0 : ℂ) else
            A i x / (↑↑i / (↑(n - 1) : ℂ) - ↑↑x / ↑(n - 1))) *
          (if x = i then ↑↑x / (↑(n - 1) : ℂ) else 0) = 0 := by
        intro x; by_cases h : i = x
        · simp [h]
        · have : ¬x = i := fun hc => h hc.symm; simp [h, this]
      rw [Finset.sum_eq_zero (fun x _ => h1 x),
          Finset.sum_eq_zero (fun x _ => h2 x), sub_self]
    · -- off-diagonal: [B,C]_ij = (b_i - b_j) * A_ij/(b_i - b_j) = A_ij
      simp only [B, Matrix.diagonal_apply, C, Matrix.of_apply]
      have hij' : ¬j = i := fun h => hij h.symm
      -- Simplify sums using diagonal structure
      have hs1 : ∀ x : Fin n,
          (if i = x then ↑↑i / (↑(n - 1) : ℂ) else 0) *
          (if x = j then (0 : ℂ) else
            A x j / (↑↑x / ↑(n - 1) - ↑↑j / ↑(n - 1))) =
          if x = i then ↑↑i / (↑(n - 1) : ℂ) *
            (A i j / (↑↑i / ↑(n - 1) - ↑↑j / ↑(n - 1))) else 0 := by
        intro x; by_cases hx : i = x
        · subst hx; simp [hij]
        · simp [hx, Ne.symm hx]
      have hs2 : ∀ x : Fin n,
          (if i = x then (0 : ℂ) else
            A i x / (↑↑i / (↑(n - 1) : ℂ) - ↑↑x / ↑(n - 1))) *
          (if x = j then ↑↑x / (↑(n - 1) : ℂ) else 0) =
          if x = j then A i j / (↑↑i / (↑(n - 1) : ℂ) - ↑↑j / ↑(n - 1)) *
            (↑↑j / (↑(n - 1) : ℂ)) else 0 := by
        intro x; by_cases hx : x = j
        · subst hx; simp [hij]
        · simp [hx]
      simp_rw [hs1, hs2]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      set d := ↑↑i / (↑(n - 1) : ℂ) - ↑↑j / ↑(n - 1) with hd_def
      have hdiff_ne : d ≠ 0 := by
        rw [hd_def, div_sub_div_same]
        apply div_ne_zero
        · simp only [ne_eq, sub_eq_zero]
          exact_mod_cast Fin.val_ne_of_ne hij
        · exact_mod_cast (show (n - 1 : ℕ) ≠ 0 by omega)
      rw [show ↑↑i / (↑(n - 1) : ℂ) * (A i j / d) -
          A i j / d * (↑↑j / ↑(n - 1)) =
          d * (A i j / d) from by rw [hd_def]; ring]
      exact (mul_div_cancel₀ (A i j) hdiff_ne).symm
  · -- ‖C‖ ≤ n * (n-1) * ‖A‖
    have hC_entry : ∀ i j : Fin n, ‖C i j‖ ≤ (↑n - 1) * ‖A i j‖ := by
      intro i j; simp only [C, Matrix.of_apply]
      by_cases hij : i = j
      · subst hij; simp only [↓reduceIte, norm_zero]; exact mul_nonneg (by linarith) (norm_nonneg _)
      · rw [if_neg hij, norm_div, div_sub_div_same, norm_div]
        have hnorm_n1 : ‖(↑(n - 1 : ℕ) : ℂ)‖ = (↑(n - 1 : ℕ) : ℝ) := Complex.norm_natCast _
        have hn1_eq : (↑(n - 1 : ℕ) : ℝ) = (↑n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
        have hnorm_diff_ge1 : (1 : ℝ) ≤ ‖(↑↑i : ℂ) - ↑↑j‖ := by
          rw [show (↑↑i : ℂ) - ↑↑j = ↑((i.val : ℤ) - (j.val : ℤ)) from by push_cast; ring]
          rw [Complex.norm_intCast]
          exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast Fin.val_ne_of_ne hij
            : (i.val : ℤ) ≠ j.val))
        rw [div_div_eq_mul_div, hnorm_n1, hn1_eq]
        rw [mul_comm ‖A i j‖ (↑n - 1)]
        exact div_le_self (by positivity) hnorm_diff_ge1
    have hhs : hsNorm C ≤ (↑n - 1) * hsNorm A := by
      unfold hsNorm
      rw [show (↑n - 1 : ℝ) * Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) =
          Real.sqrt ((↑n - 1) ^ 2 * ∑ i, ∑ j, Complex.normSq (A i j)) from by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hn1)]]
      apply Real.sqrt_le_sqrt
      calc ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (C i j)
          ≤ ∑ i : Fin n, ∑ j : Fin n, (↑n - 1) ^ 2 * Complex.normSq (A i j) := by
            apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
            simp only [Complex.normSq_eq_norm_sq]
            rw [← mul_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (hC_entry i j) 2
        _ = (↑n - 1) ^ 2 * ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j) := by
            simp_rw [← Finset.mul_sum]
    calc ‖C‖ ≤ hsNorm C := le_hsNorm C
      _ ≤ (↑n - 1) * hsNorm A := hhs
      _ ≤ (↑n - 1) * (Real.sqrt ↑n * ‖A‖) :=
          mul_le_mul_of_nonneg_left (hsNorm_le_sqrt_n_mul_opNorm A) (le_of_lt hn1)
      _ = Real.sqrt ↑n * ((↑n - 1) * ‖A‖) := by ring
      _ ≤ ↑n * ((↑n - 1) * ‖A‖) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [Real.sqrt_le_left (Nat.cast_nonneg n)]
          calc (↑n : ℝ) = ↑n * 1 := (mul_one _).symm
            _ ≤ ↑n * ↑n := mul_le_mul_of_nonneg_left (by exact_mod_cast (show 1 ≤ n by omega))
              (Nat.cast_nonneg n)
            _ = (↑n : ℝ) ^ 2 := (sq _).symm
      _ = ↑n * (↑n - 1) * ‖A‖ := by ring

/-- Monotonicity of lambdaM: if m₁ ≤ m₂ then lambdaM m₁ ≤ lambdaM m₂.
    Proof idea: embed any m₁×m₁ zero-diagonal matrix into m₂×m₂ by zero-padding;
    this preserves norm, zero-diagonal, and any commutator decomposition. -/
private lemma lambdaA_nonneg {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ lambdaA A := by
  unfold lambdaA
  by_cases hne : (({c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}).Nonempty)
  · exact le_csInf hne (fun c ⟨_, C', _, _, _, hle⟩ => le_trans (norm_nonneg _) hle)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp

lemma lambdaM_mono {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) : lambdaM m₁ ≤ lambdaM m₂ := by
  unfold lambdaM
  set S₁ := lambdaA '' {A : Matrix (Fin m₁) (Fin m₁) ℂ | ZeroDiag A ∧ ‖A‖ = 1}
  set S₂ := lambdaA '' {A : Matrix (Fin m₂) (Fin m₂) ℂ | ZeroDiag A ∧ ‖A‖ = 1}
  by_cases hne : S₁.Nonempty
  · -- S₁ nonempty implies m₁ ≥ 2
    have hm₁ : 2 ≤ m₁ := by
      by_contra hlt; push Not at hlt
      obtain ⟨_, A, ⟨hzd, hnorm⟩, _⟩ := hne
      interval_cases m₁
      · exact absurd hnorm (by
          rw [show A = 0 from Subsingleton.elim _ _, norm_zero]; norm_num)
      · have : A = 0 := by
          ext i j; rw [show i = 0 from Fin.eq_zero i, show j = 0 from Fin.eq_zero j]
          exact hzd 0
        rw [this, norm_zero] at hnorm; linarith
    have hm₂ : 2 ≤ m₂ := le_trans hm₁ h
    -- BddAbove S₂
    have hbdd₂ : BddAbove S₂ := by
      refine ⟨(m₂ : ℝ) * (m₂ - 1), fun x hx => ?_⟩
      obtain ⟨A, ⟨hzd, hnorm⟩, rfl⟩ := hx
      obtain ⟨B, C, hdiag, husq, hcomm, hCbound⟩ :=
        zeroDiag_InUnitSquare_decomp_bounded hm₂ A hzd
      calc lambdaA A
          ≤ ‖C‖ := csInf_le
            ⟨0, fun c ⟨_, C', _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
            ⟨B, C, hdiag, husq, hcomm, le_refl _⟩
        _ ≤ (m₂ : ℝ) * (m₂ - 1) * ‖A‖ := hCbound
        _ = (m₂ : ℝ) * (m₂ - 1) := by rw [hnorm]; ring
    -- Every element of S₁ is ≤ sSup S₂
    apply csSup_le hne
    intro x hx
    obtain ⟨A, ⟨hzd, hnorm⟩, rfl⟩ := hx
    set A' := zeroPad h A
    have hzd' : ZeroDiag A' := zeroPad_zeroDiag h hzd
    have hnorm' : ‖A'‖ = 1 := by rw [zeroPad_norm_eq]; exact hnorm
    -- lambdaA A ≤ lambdaA A' via csInf_le_csInf
    -- Key: any decomp of A' restricts to a decomp of A with ≤ norm
    have hle_lambda : lambdaA A ≤ lambdaA A' := by
      -- Case analysis on whether A' has any decomposition
      set T_A' := {c : ℝ | ∃ (B C : Matrix (Fin m₂) (Fin m₂) ℂ),
        IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A' = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c}
      by_cases hT : T_A'.Nonempty
      · apply csInf_le_csInf
        · exact ⟨0, fun c ⟨_, C, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
        · exact hT
        · intro c ⟨B', C', hdiag', husq', hcomm', hnormC'⟩
          exact ⟨restrict h B', restrict h C',
            fun i j hij => by
              simp only [restrict, Matrix.of_apply]
              exact hdiag' _ _ (fun heq => hij (finEmbed_injective h heq)),
            fun i => by
              simp only [restrict, Matrix.of_apply]; exact husq' (finEmbed h i),
            by rw [← restrict_matComm_of_diag h B' C' hdiag', ← hcomm', restrict_zeroPad],
            le_trans (restrict_norm_le h C') hnormC'⟩
      · -- T_A' empty is impossible: zeroDiag_InUnitSquare_decomp_bounded gives a decomposition
        exfalso; apply hT
        obtain ⟨B', C', hd', hu', hc', _⟩ :=
          zeroDiag_InUnitSquare_decomp_bounded hm₂ A' hzd'
        exact ⟨‖C'‖, B', C', hd', hu', hc', le_refl _⟩
    exact le_trans hle_lambda (le_csSup hbdd₂ ⟨A', ⟨hzd', hnorm'⟩, rfl⟩)
  · -- S₁ empty: sSup S₁ = 0
    rw [Set.not_nonempty_iff_eq_empty.mp hne, show sSup (∅ : Set ℝ) = 0 from by simp]
    exact Real.sSup_nonneg (fun x hx => by
      obtain ⟨A, _, rfl⟩ := hx; exact lambdaA_nonneg A)

/-- lambdaA of a unit-norm ZeroDiag matrix is ≤ lambdaM m. -/
private lemma lambdaA_le_lambdaM_unit {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ)
    (hzd : ZeroDiag A) (h1 : ‖A‖ = 1) :
    lambdaA A ≤ lambdaM m := by
  unfold lambdaM; apply le_csSup
  · rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · refine ⟨0, fun x hx => ?_⟩
      obtain ⟨A', ⟨hzd', hnorm'⟩, rfl⟩ := hx; exfalso
      have : A' = 0 := by
        interval_cases m
        · ext i; exact Fin.elim0 i
        · ext i j; rcases Fin.eq_zero i with rfl
          rcases Fin.eq_zero j with rfl; exact hzd' 0
      rw [this, norm_zero] at hnorm'
      exact one_ne_zero hnorm'.symm
    · refine ⟨(m : ℝ) * (m - 1), fun x hx => ?_⟩
      obtain ⟨A', ⟨hzd', hnorm'⟩, rfl⟩ := hx
      obtain ⟨B', C', hd', hu', hc', hbound⟩ :=
        zeroDiag_InUnitSquare_decomp_bounded hm2 A' hzd'
      calc lambdaA A'
          ≤ ‖C'‖ := csInf_le
            ⟨0, fun c ⟨_, C, _, _, _, hle⟩ =>
              le_trans (norm_nonneg _) hle⟩
            ⟨B', C', hd', hu', hc', le_refl _⟩
        _ ≤ (m : ℝ) * (m - 1) * ‖A'‖ := hbound
        _ = (m : ℝ) * (m - 1) := by rw [hnorm']; ring
  · exact ⟨A, ⟨hzd, h1⟩, rfl⟩

/-- lambdaA of a ZeroDiag matrix with ‖A‖ ≤ 1 is at most lambdaM m. -/
private lemma lambdaA_le_lambdaM {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ)
    (hzd : ZeroDiag A) (hn : ‖A‖ ≤ 1) :
    lambdaA A ≤ lambdaM m := by
  by_cases h1 : ‖A‖ = 1
  · exact lambdaA_le_lambdaM_unit A hzd h1
  · have hlt : ‖A‖ < 1 := lt_of_le_of_ne hn h1
    by_cases h0 : ‖A‖ = 0
    · have hA0 : A = 0 := norm_eq_zero.mp h0
      rw [hA0]
      have hla0 : lambdaA (0 : Matrix (Fin m) (Fin m) ℂ) ≤ 0 := by
        unfold lambdaA; apply csInf_le
        · exact ⟨0, fun c ⟨_, C', _, _, _, hle⟩ =>
            le_trans (norm_nonneg _) hle⟩
        · exact ⟨0, 0, fun _ _ h => by simp,
            fun _ => ⟨by simp, by simp⟩,
            by ext i j; simp [matComm], by norm_num⟩
      have : (0 : ℝ) ≤ lambdaM m := by
        unfold lambdaM
        exact Real.sSup_nonneg (fun x hx => by
          obtain ⟨A', _, rfl⟩ := hx; exact lambdaA_nonneg A')
      linarith
    · have hpos : 0 < ‖A‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have hAnorm_ne : (‖A‖ : ℝ) ≠ 0 := ne_of_gt hpos
      set A' := (↑(‖A‖⁻¹) : ℂ) • A with hA'_def
      have hnormA' : ‖A'‖ = 1 := by
        rw [hA'_def, norm_smul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
          inv_mul_cancel₀ hAnorm_ne]
      have hzdA' : ZeroDiag A' := fun i => by
        simp [hA'_def, hzd i]
      have hA_eq : A = (↑(‖A‖) : ℂ) • A' := by
        rw [hA'_def, smul_smul, ← Complex.ofReal_mul,
          mul_inv_cancel₀ hAnorm_ne,
          Complex.ofReal_one, one_smul]
      -- lambdaA A ≤ lambdaA A' (since S_{A'} ⊆ S_A via scaling)
      have hle_AA' : lambdaA A ≤ lambdaA A' := by
        unfold lambdaA; apply csInf_le_csInf
        · exact ⟨0, fun c ⟨_, C', _, _, _, hle⟩ =>
            le_trans (norm_nonneg _) hle⟩
        · rcases Nat.lt_or_ge m 2 with hm2 | hm2
          · exfalso
            have : A' = 0 := by
              interval_cases m
              · ext i; exact Fin.elim0 i
              · ext i j; rcases Fin.eq_zero i with rfl
                rcases Fin.eq_zero j with rfl; exact hzdA' 0
            rw [this, norm_zero] at hnormA'
            exact one_ne_zero hnormA'.symm
          · obtain ⟨B', C', hd', hu', hc', _⟩ :=
              zeroDiag_InUnitSquare_decomp_bounded hm2
                A' hzdA'
            exact ⟨‖C'‖, B', C', hd', hu', hc', le_refl _⟩
        · intro c ⟨B, C0, hd, hu, hc, hnC⟩
          refine ⟨B, (↑(‖A‖) : ℂ) • C0, hd, hu, ?_, ?_⟩
          · conv_lhs => rw [hA_eq, hc]
            exact (matComm_smul_right B C0 _).symm
          · rw [norm_smul, Complex.norm_real,
              Real.norm_eq_abs,
              abs_of_nonneg (le_of_lt hpos)]
            calc ‖A‖ * ‖C0‖
                ≤ 1 * ‖C0‖ :=
                  mul_le_mul_of_nonneg_right
                    (le_of_lt hlt) (norm_nonneg _)
              _ = ‖C0‖ := one_mul _
              _ ≤ c := hnC
      exact le_trans hle_AA'
        (lambdaA_le_lambdaM_unit A' hzdA' hnormA')


set_option maxHeartbeats 800000 in
-- Matrix and finite-sum calculations require additional elaboration steps.
/-- Pointwise 4-block bound: for any (4m)×(4m) zero-diagonal unit-norm matrix A,
    lambdaA A ≤ 2/(1-δ) · lambdaM(m) + 6/δ.
    The construction: view Fin(4m) as 4 blocks of m. For each diagonal block k,
    get B_k, C_k with A_kk = [B_k, C_k] (InUnitSquare). Build B' diagonal with
    B'_i = (1-δ)/2 · (B_k)_{i%m} + (1+δ)/2 · corner_k. Then same-block C entries
    scale by 2/(1-δ), and cross-block entries are solved via Sylvester with gap ≥ 2δ. -/
lemma lambdaA_four_block_bound {m : ℕ} (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (A : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1) :
    lambdaA A ≤ 2 / (1 - δ) * lambdaM m + 6 / δ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- m = 0: Fin(4*0) = Fin 0, matrix is empty
    have h0 : lambdaA A ≤ 0 := by
      unfold lambdaA
      apply csInf_le
      · exact ⟨0, fun c ⟨_, C', _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
      · refine ⟨0, 0, ?_, ?_, ?_, by norm_num⟩
        · intro i j _; exact Fin.elim0 i
        · intro i; exact Fin.elim0 i
        · ext i; exact Fin.elim0 i
    have hbound : (0 : ℝ) ≤ 2 / (1 - δ) * lambdaM 0 + 6 / δ := by
      have h1 : 0 < 1 - δ := sub_pos.mpr hδ1
      have h2 : 0 ≤ lambdaM 0 := by
        unfold lambdaM
        exact Real.sSup_nonneg (fun x hx => by
          obtain ⟨A, _, rfl⟩ := hx; exact lambdaA_nonneg A)
      positivity
    linarith
  · -- m ≥ 1: the main 4-block construction
    have h1δ : (0 : ℝ) < 1 - δ := sub_pos.mpr hδ1
    -- Block index functions: view Fin(4m) as 4 blocks of size m
    let blockEmbed : Fin 4 → Fin m → Fin (4 * m) :=
      fun k j => ⟨k.val * m + j.val, by
        have hk := k.isLt; have hj := j.isLt
        calc k.val * m + j.val < k.val * m + m := by omega
          _ = (k.val + 1) * m := by ring
          _ ≤ 4 * m := by nlinarith⟩
    -- Extract k-th diagonal block
    let diagBlock : Fin 4 → Matrix (Fin m) (Fin m) ℂ :=
      fun k => Matrix.of (fun i j =>
        A (blockEmbed k i) (blockEmbed k j))
    have hzd_block : ∀ k, ZeroDiag (diagBlock k) := by
      intro k i
      simp only [diagBlock, Matrix.of_apply]
      exact hzd (blockEmbed k i)
    have hblockEmbed_inj : ∀ k : Fin 4,
        Function.Injective (blockEmbed k) := by
      intro k i j hij
      simp only [blockEmbed, Fin.mk.injEq] at hij
      exact Fin.ext (by omega)
    have hnorm_block : ∀ k, ‖diagBlock k‖ ≤ 1 := by
      intro k; rw [← hnorm]
      exact submatrix_norm_le
        (blockEmbed k) (hblockEmbed_inj k) A
    -- Use le_of_forall_pos_lt_add: lambdaA A ≤ bound if for all
    -- ε > 0, lambdaA A < bound + ε.
    -- Equivalently: for all ε > 0, ∃ witness with ‖C‖ < bound + ε.
    apply le_of_forall_pos_lt_add
    intro ε hε
    -- For each block, the decomposition set is nonempty and
    -- lambdaA(diagBlock k) ≤ lambdaM m (since ZeroDiag, ‖·‖ ≤ 1).
    -- Pick near-optimal decompositions with slack ε.
    -- Then build B', C' on Fin(4m) via the corner construction.
    -- The resulting ‖C'‖ ≤ 2/(1-δ) * lambdaM m + 6/δ + f(ε).
    -- So lambdaA A ≤ ‖C'‖ < bound + ε.
    --
    -- Step 1: Each diagBlock k has a decomposition (lambdaA set nonempty)
    have hne_block : ∀ k, ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
        IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
        diagBlock k = ⁅B, C⁆ₘ := by
      intro k
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · -- m = 1 (since hm : m > 0)
        have hm1 : m = 1 := by omega
        subst hm1
        refine ⟨0, 0, ?_, ?_, ?_⟩
        · intro i j hij; simp
        · intro i; unfold InUnitSquare; simp
        · ext i j; simp only [matComm, mul_zero, Matrix.sub_apply, Matrix.zero_apply, sub_self]
          have : i = j := Fin.ext (by omega)
          rw [this]; exact hzd_block k j
      · -- m ≥ 2
        obtain ⟨B, C, hd, hu, hc, _⟩ :=
          zeroDiag_InUnitSquare_decomp_bounded hm2
            (diagBlock k) (hzd_block k)
        exact ⟨B, C, hd, hu, hc⟩
    -- Step 2: lambdaA(diagBlock k) ≤ lambdaM m for each block
    have hlA_block : ∀ k, lambdaA (diagBlock k) ≤ lambdaM m := by
      intro k
      exact lambdaA_le_lambdaM (diagBlock k) (hzd_block k)
        (hnorm_block k)
    -- Step 3: Pick near-optimal decompositions with slack η for each block
    -- Choose η so that 2/(1-δ) * η < ε, i.e. η = ε * (1-δ) / 4
    set η := ε * (1 - δ) / 4 with hη_def
    have hη_pos : 0 < η := by positivity
    -- For each block k, extract B_k, C_k with diagBlock k = [B_k, C_k]
    -- and ‖C_k‖ ≤ lambdaA(diagBlock k) + η
    have hpick : ∀ k : Fin 4, ∃ (Bk Ck : Matrix (Fin m) (Fin m) ℂ),
        IsDiagMatrix Bk ∧ (∀ i, InUnitSquare (Bk i i)) ∧
        diagBlock k = ⁅Bk, Ck⁆ₘ ∧ ‖Ck‖ ≤ lambdaA (diagBlock k) + η := by
      intro k
      -- Inline: lambdaA is sInf; since sInf < sInf + η, extract witness
      set S := {c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
        IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
        diagBlock k = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hS_def
      have hne_S : S.Nonempty := by
        obtain ⟨B, C, hdiag, husq, hcomm⟩ := hne_block k
        exact ⟨‖C‖, B, C, hdiag, husq, hcomm, le_refl _⟩
      have hbdd : BddBelow S := by
        refine ⟨0, fun c ⟨B, C, _, _, _, hle⟩ => ?_⟩
        exact le_trans (norm_nonneg _) hle
      have hlt : sInf S < lambdaA (diagBlock k) + η := by
        unfold lambdaA; linarith
      obtain ⟨c, ⟨B, C, hdiag, husq, hcomm, hnorm⟩, hc_lt⟩ :=
        exists_lt_of_csInf_lt hne_S hlt
      exact ⟨B, C, hdiag, husq, hcomm, le_trans hnorm (le_of_lt hc_lt)⟩
    -- Use choice to get the B_k, C_k for all 4 blocks simultaneously
    choose Bk Ck hBk_diag hBk_usq hBk_comm hCk_norm using hpick
    -- Each ‖C_k‖ ≤ lambdaM m + η (since lambdaA(diagBlock k) ≤ lambdaM m)
    have hCk_bound : ∀ k : Fin 4, ‖Ck k‖ ≤ lambdaM m + η := by
      intro k
      calc ‖Ck k‖ ≤ lambdaA (diagBlock k) + η := hCk_norm k
        _ ≤ lambdaM m + η := by linarith [hlA_block k]
    -- Reduce to constructing a witness B', C' with controlled norm.
    -- The construction uses B' = diag((1-δ)/2·(Bk k)_ii + (1+δ)/2·corner_k)
    -- and C' defined entry-wise. The norm splits into same-block (≤ 2/(1-δ)·max‖Ck‖)
    -- and cross-block (≤ 6/δ via Sylvester with gap ≥ 2δ).
    suffices hwit : ∃ (B' C' : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ),
        IsDiagMatrix B' ∧ (∀ i, InUnitSquare (B' i i)) ∧
        A = ⁅B', C'⁆ₘ ∧ ‖C'‖ ≤ 2 / (1 - δ) * (lambdaM m + η) + 6 / δ by
      obtain ⟨B', C', hd, hu, hc, hn⟩ := hwit
      have hη_bound : 2 / (1 - δ) * η = ε / 2 := by
        rw [hη_def]; field_simp; ring
      calc lambdaA A
          ≤ ‖C'‖ := csInf_le
            ⟨0, fun c ⟨_, C, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
            ⟨B', C', hd, hu, hc, le_refl _⟩
        _ ≤ 2 / (1 - δ) * (lambdaM m + η) + 6 / δ := hn
        _ = 2 / (1 - δ) * lambdaM m + 2 / (1 - δ) * η + 6 / δ := by ring
        _ = 2 / (1 - δ) * lambdaM m + 6 / δ + ε / 2 := by rw [hη_bound]; ring
        _ < 2 / (1 - δ) * lambdaM m + 6 / δ + ε := by linarith
    -- === Witness Construction ===
    -- Block index functions
    let blockIdx : Fin (4 * m) → Fin 4 :=
      fun i => ⟨i.val / m, Nat.div_lt_of_lt_mul (by omega)⟩
    let localIdx : Fin (4 * m) → Fin m :=
      fun i => ⟨i.val % m, Nat.mod_lt _ (by omega)⟩
    -- Key: blockEmbed (blockIdx i) (localIdx i) = i
    have hEmbed_id : ∀ i : Fin (4 * m),
        blockEmbed (blockIdx i) (localIdx i) = i := by
      intro i; ext
      simp only [blockEmbed, blockIdx, localIdx]
      exact (Nat.div_add_mod' i.val m)
    have hBlockIdx_embed : ∀ (k : Fin 4) (j : Fin m),
        blockIdx (blockEmbed k j) = k := by
      intro k j; ext
      simp only [blockEmbed, blockIdx]
      have hj := j.isLt
      rw [show k.val * m + j.val = j.val + k.val * m from by omega]
      rw [Nat.add_mul_div_right _ _ (by omega : 0 < m)]
      simp [Nat.div_eq_of_lt hj]
    have hLocalIdx_embed : ∀ (k : Fin 4) (j : Fin m),
        localIdx (blockEmbed k j) = j := by
      intro k j; ext
      simp only [blockEmbed, localIdx]
      have hj := j.isLt
      rw [show k.val * m + j.val = j.val + k.val * m from by omega]
      simp [Nat.mod_eq_of_lt hj]
    -- Corner values for 4 quadrants
    let cornerRe : Fin 4 → ℝ :=
      ![  (1 + δ) / 2,  (1 + δ) / 2, -(1 + δ) / 2, -(1 + δ) / 2]
    let cornerIm : Fin 4 → ℝ :=
      ![ (1 + δ) / 2, -(1 + δ) / 2,  (1 + δ) / 2, -(1 + δ) / 2]
    let cornerVal : Fin 4 → ℂ := fun k => ⟨cornerRe k, cornerIm k⟩
    -- fullB: diagonal matrix
    let fullB : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
      Matrix.diagonal (fun i =>
        ((1 - δ) / 2 : ℝ) * (Bk (blockIdx i)) (localIdx i) (localIdx i) +
        cornerVal (blockIdx i))
    have hfullB_diag : IsDiagMatrix fullB :=
      fun i j hij => Matrix.diagonal_apply_ne _ hij
    -- fullB has InUnitSquare entries
    -- Each diagonal entry is (1-δ)/2 * b + corner where |b.re|,|b.im| ≤ 1
    -- and |corner.re|,|corner.im| = (1+δ)/2, so total ≤ (1-δ)/2 + (1+δ)/2 = 1
    have hfullB_usq : ∀ i, InUnitSquare (fullB i i) := by
      intro i; simp only [fullB, Matrix.diagonal_apply_eq]
      have key : ∀ (x c : ℝ), |x| ≤ 1 → |c| = (1 + δ) / 2 → |(1 - δ) / 2 * x + c| ≤ 1 := by
        intro x c hx hc
        rw [abs_le]; rw [abs_le] at hx; obtain ⟨hx_lo, hx_hi⟩ := hx
        by_cases hc0 : 0 ≤ c
        · rw [abs_of_nonneg hc0] at hc; subst hc; constructor <;> nlinarith
        · have hc0' : c < 0 := not_le.mp hc0
          rw [abs_of_neg hc0'] at hc; constructor <;> nlinarith
      have corner_abs_helper : ∀ x : ℝ, x = (1 + δ) / 2 ∨ x = -(1 + δ) / 2 →
          |x| = (1 + δ) / 2 := by
        intro x hx; rcases hx with rfl | rfl
        · exact abs_of_nonneg (by linarith)
        · rw [show -(1 + δ) / 2 = -((1 + δ) / 2) from neg_div _ _]
          rw [abs_neg]; exact abs_of_nonneg (by linarith)
      have hcre_abs : ∀ k : Fin 4, |cornerRe k| = (1 + δ) / 2 := by
        intro k; apply corner_abs_helper
        fin_cases k <;> simp [cornerRe]
      have hcim_abs : ∀ k : Fin 4, |cornerIm k| = (1 + δ) / 2 := by
        intro k; apply corner_abs_helper
        fin_cases k <;> simp [cornerIm]
      obtain ⟨hbre, hbim⟩ := hBk_usq (blockIdx i) (localIdx i)
      have hre_eq : (↑((1 - δ) / 2) * Bk (blockIdx i) (localIdx i) (localIdx i) +
          cornerVal (blockIdx i)).re =
          (1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re +
          cornerRe (blockIdx i) := by
        simp [cornerVal, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      have him_eq : (↑((1 - δ) / 2) * Bk (blockIdx i) (localIdx i) (localIdx i) +
          cornerVal (blockIdx i)).im =
          (1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).im +
          cornerIm (blockIdx i) := by
        simp [cornerVal, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨hre_eq ▸ key _ _ hbre (hcre_abs _), him_eq ▸ key _ _ hbim (hcim_abs _)⟩
    -- Spectral gap: for cross-block pairs, Re or Im gap ≥ 2δ
    -- Proof: corners (±(1+δ)/2, ±(1+δ)/2) differ by (1+δ) in Re or Im for
    -- distinct blocks. Perturbation from Bk is ≤ (1-δ). Gap ≥ (1+δ)-(1-δ) = 2δ.
    have hSpectralGap : ∀ (i j : Fin (4 * m)),
        blockIdx i ≠ blockIdx j →
        2 * δ ≤ |(fullB i i - fullB j j).re| ∨
        2 * δ ≤ |(fullB i i - fullB j j).im| := by
      intro i j hne
      simp only [fullB, Matrix.diagonal_apply_eq]
      obtain ⟨hri, hii⟩ := hBk_usq (blockIdx i) (localIdx i)
      obtain ⟨hrj, hij⟩ := hBk_usq (blockIdx j) (localIdx j)
      have pert_bound : ∀ (x y a : ℝ), 0 ≤ a → |x| ≤ 1 → |y| ≤ 1 →
          |a / 2 * x - a / 2 * y| ≤ a := by
        intro x y a ha hx hy
        rw [show a / 2 * x - a / 2 * y = a / 2 * (x - y) from by ring]
        rw [abs_mul, abs_of_nonneg (by linarith)]
        have hxy : |x - y| ≤ 2 := le_trans (abs_sub x y) (by linarith)
        nlinarith
      have rev_tri : ∀ (a b : ℝ), |b| - |a| ≤ |a + b| := by
        intro a b
        have h := abs_sub (a + b) a
        simp [add_sub_cancel_left] at h; linarith
      have hpert_re : |(1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re -
          (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).re| ≤ 1 - δ :=
        pert_bound _ _ _ (by linarith) hri hrj
      have hpert_im : |(1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).im -
          (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).im| ≤ 1 - δ :=
        pert_bound _ _ _ (by linarith) hii hij
      have hre_eq : (((1 - δ) / 2 : ℝ) * Bk (blockIdx i) (localIdx i) (localIdx i) +
          cornerVal (blockIdx i) -
          (((1 - δ) / 2 : ℝ) * Bk (blockIdx j) (localIdx j) (localIdx j) +
          cornerVal (blockIdx j))).re =
        (1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re -
        (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).re +
        (cornerRe (blockIdx i) - cornerRe (blockIdx j)) := by
        simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im, cornerVal]; ring
      have him_eq : (((1 - δ) / 2 : ℝ) * Bk (blockIdx i) (localIdx i) (localIdx i) +
          cornerVal (blockIdx i) -
          (((1 - δ) / 2 : ℝ) * Bk (blockIdx j) (localIdx j) (localIdx j) +
          cornerVal (blockIdx j))).im =
        (1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).im -
        (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).im +
        (cornerIm (blockIdx i) - cornerIm (blockIdx j)) := by
        simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
              Complex.ofReal_im, cornerVal]; ring
      have hcRe_vals : ∀ k : Fin 4, cornerRe k = (1 + δ) / 2 ∨ cornerRe k = -(1 + δ) / 2 := by
        intro k; fin_cases k <;> simp [cornerRe, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hcIm_vals : ∀ k : Fin 4, cornerIm k = (1 + δ) / 2 ∨ cornerIm k = -(1 + δ) / 2 := by
        intro k; fin_cases k <;> simp [cornerIm, Matrix.cons_val_zero, Matrix.cons_val_one]
      have corner_inj : ∀ (a b : Fin 4), cornerRe a = cornerRe b → cornerIm a = cornerIm b → a =
        b := by
        intro a b h1 h2
        fin_cases a <;> fin_cases b <;> first | rfl |
          (simp [cornerRe, cornerIm, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2; linarith)
      have hcorner_diff : cornerRe (blockIdx i) ≠ cornerRe (blockIdx j) ∨
          cornerIm (blockIdx i) ≠ cornerIm (blockIdx j) := by
        by_contra h; push Not at h
        exact hne (corner_inj _ _ h.1 h.2)
      have corner_gap : ∀ (f : Fin 4 → ℝ), (∀ k, f k = (1 + δ) / 2 ∨ f k = -(1 + δ) / 2) →
          f (blockIdx i) ≠ f (blockIdx j) → |f (blockIdx i) - f (blockIdx j)| = 1 + δ := by
        intro f hvals hneq
        rcases hvals (blockIdx i) with hi | hi <;> rcases hvals (blockIdx j) with hj | hj
        · exfalso; exact hneq (by rw [hi, hj])
        · rw [hi, hj]; rw [show (1 + δ) / 2 - -(1 + δ) / 2 = 1 + δ from by ring]
          exact abs_of_pos (by linarith)
        · rw [hi, hj]; rw [show -(1 + δ) / 2 - (1 + δ) / 2 = -(1 + δ) from by ring]
          rw [abs_neg]; exact abs_of_pos (by linarith)
        · exfalso; exact hneq (by rw [hi, hj])
      rcases hcorner_diff with hcr | hci
      · left; rw [hre_eq]
        have hgap := corner_gap cornerRe hcRe_vals hcr
        linarith [rev_tri ((1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).re -
          (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).re)
          (cornerRe (blockIdx i) - cornerRe (blockIdx j))]
      · right; rw [him_eq]
        have hgap := corner_gap cornerIm hcIm_vals hci
        linarith [rev_tri ((1 - δ) / 2 * (Bk (blockIdx i) (localIdx i) (localIdx i)).im -
          (1 - δ) / 2 * (Bk (blockIdx j) (localIdx j) (localIdx j)).im)
          (cornerIm (blockIdx i) - cornerIm (blockIdx j))]
    -- Cross-block denominators are nonzero
    have hFullB_ne : ∀ (i j : Fin (4 * m)),
        blockIdx i ≠ blockIdx j → fullB i i ≠ fullB j j := by
      intro i j hne habs
      rcases hSpectralGap i j hne with hre | him
      · have : (fullB i i - fullB j j).re = 0 := by rw [habs]; simp
        rw [this] at hre; simp at hre; linarith
      · have : (fullB i i - fullB j j).im = 0 := by rw [habs]; simp
        rw [this] at him; simp at him; linarith
    -- Define fullC
    let fullC : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
      fun i j =>
        if blockIdx i = blockIdx j then
          (2 / ((1 : ℝ) - δ) : ℂ) * (Ck (blockIdx i)) (localIdx i) (localIdx j)
        else
          A i j / (fullB i i - fullB j j)
    -- Verify A = [fullB, fullC]
    have hComm : A = ⁅fullB, fullC⁆ₘ := by
      ext i j
      rw [commutator_diag_entry fullB fullC hfullB_diag]
      simp only [fullC]
      split_ifs with heq
      · -- Same block
        simp only [fullB, Matrix.diagonal_apply_eq]
        have hAij : A i j = diagBlock (blockIdx i) (localIdx i) (localIdx j) := by
          simp only [diagBlock, Matrix.of_apply]
          conv_rhs => rw [show blockEmbed (blockIdx i) (localIdx j) =
            blockEmbed (blockIdx j) (localIdx j) from by rw [heq],
            hEmbed_id j, hEmbed_id i]
        rw [hAij, hBk_comm (blockIdx i),
          commutator_diag_entry _ _ (hBk_diag _), heq]
        -- cornerVal cancels, then (1-δ)/2 * 2/(1-δ) = 1
        -- (B_i + c - (B_j + c)) * (2/(1-δ)) * C_ij
        -- = ((1-δ)/2) * (B_i - B_j) * (2/(1-δ)) * C_ij
        -- = (B_i - B_j) * C_ij
        have h1δne : (1 : ℝ) - δ ≠ 0 := by linarith
        have hkey : (↑((1 - δ) / 2) : ℂ) * (2 / (↑1 - ↑δ)) = 1 := by
          push_cast
          field_simp [show (1 : ℂ) - ↑δ ≠ 0 from by exact_mod_cast h1δne]
        have hrw : (↑((1 - δ) / 2) : ℂ) * Bk (blockIdx j) (localIdx i) (localIdx i) +
            cornerVal (blockIdx j) -
            ((↑((1 - δ) / 2) : ℂ) * Bk (blockIdx j) (localIdx j) (localIdx j) +
            cornerVal (blockIdx j)) =
            (↑((1 - δ) / 2) : ℂ) * (Bk (blockIdx j) (localIdx i) (localIdx i) -
            Bk (blockIdx j) (localIdx j) (localIdx j)) := by ring
        rw [hrw]
        simp only [Complex.ofReal_one]
        rw [show (↑((1 - δ) / 2) : ℂ) *
            (Bk (blockIdx j) (localIdx i) (localIdx i) -
            Bk (blockIdx j) (localIdx j) (localIdx j)) *
            (2 / (1 - ↑δ) * Ck (blockIdx j) (localIdx i) (localIdx j)) =
            (↑((1 - δ) / 2) : ℂ) * (2 / (1 - ↑δ)) *
            ((Bk (blockIdx j) (localIdx i) (localIdx i) -
            Bk (blockIdx j) (localIdx j) (localIdx j)) *
            Ck (blockIdx j) (localIdx i) (localIdx j)) from by ring]
        rw [hkey, one_mul]
      · -- Cross block
        have hne := hFullB_ne i j heq
        have hne' : fullB i i - fullB j j ≠ 0 := sub_ne_zero.mpr hne
        field_simp [hne']
    -- Norm bound on fullC
    have hfullC_bound : ‖fullC‖ ≤ 2 / (1 - δ) * (lambdaM m + η) + 6 / δ := by
      -- Decompose fullC = sameBlockC + crossBlockC
      let sameBlockC : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
        fun i j => if blockIdx i = blockIdx j then
          (2 / ((1 : ℝ) - δ) : ℂ) * (Ck (blockIdx i)) (localIdx i) (localIdx j)
        else 0
      let crossBlockC : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
        fun i j => if blockIdx i = blockIdx j then 0
        else A i j / (fullB i i - fullB j j)
      have hdecomp : fullC = sameBlockC + crossBlockC := by
        ext i j; simp only [fullC, sameBlockC, crossBlockC, Matrix.add_apply]
        split_ifs <;> simp
      calc ‖fullC‖ = ‖sameBlockC + crossBlockC‖ := by rw [hdecomp]
        _ ≤ ‖sameBlockC‖ + ‖crossBlockC‖ := norm_add_le _ _
        _ ≤ 2 / (1 - δ) * (lambdaM m + η) + 6 / δ := by
          apply add_le_add
          · -- ‖sameBlockC‖ ≤ 2/(1-δ) * (lambdaM m + η)
            have hcoeff_nn : (0 : ℝ) ≤ 2 / (1 - δ) := div_nonneg (by norm_num) (le_of_lt h1δ)
            have hscale_val : ‖(2 / ((1 : ℝ) - δ) : ℂ)‖ = 2 / (1 - δ) := by
              have h2c : (2 : ℂ) / ((1 : ℝ) - δ) = ((2 / (1 - δ) : ℝ) : ℂ) := by push_cast; ring
              rw [h2c, Complex.norm_real]
              exact abs_of_pos (div_pos (by norm_num : (0:ℝ) < 2) h1δ)
            let M : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
              fun i j => if blockIdx i = blockIdx j then
                (Ck (blockIdx i)) (localIdx i) (localIdx j)
              else 0
            have hscale : sameBlockC = (2 / ((1 : ℝ) - δ) : ℂ) • M := by
              ext i j; simp only [sameBlockC, M, Matrix.smul_apply, smul_eq_mul]
              split_ifs <;> simp
            have hM_bound : ‖M‖ ≤ lambdaM m + η := by
              have hbd_nn : (0 : ℝ) ≤ lambdaM m + η := by
                have : 0 ≤ lambdaM m := Real.sSup_nonneg (fun x hx => by
                  obtain ⟨A', _, rfl⟩ := hx; exact lambdaA_nonneg A')
                positivity
              -- M is block-diagonal with blocks Ck. Use blockDiag_norm_le_of_blocks.
              have hM_eq : M = (fun i j => if (finProdFinEquiv.symm i : Fin 4 × Fin m).1 =
                  (finProdFinEquiv.symm j : Fin 4 × Fin m).1 then
                  Ck (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
                    (finProdFinEquiv.symm j).2 else 0) := by
                rfl
              rw [hM_eq]
              exact blockDiag_norm_le_of_blocks Ck (lambdaM m + η) hbd_nn hCk_bound
            rw [hscale, norm_smul, hscale_val]
            exact mul_le_mul_of_nonneg_left hM_bound hcoeff_nn
          · -- ‖crossBlockC‖ ≤ 6/δ
            -- Decompose as sum over 12 cross-block pairs
            let crossPairs : Finset (Fin 4 × Fin 4) :=
              Finset.univ.filter (fun p => p.1 ≠ p.2)
            let embedBlock : Fin 4 × Fin 4 → Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ :=
              fun p => fun i j =>
                if blockIdx i = p.1 ∧ blockIdx j = p.2 then
                  A i j / (fullB i i - fullB j j)
                else 0
            have hcross_sum : crossBlockC = ∑ p ∈ crossPairs, embedBlock p := by
              ext i j
              simp only [Matrix.sum_apply, crossBlockC, embedBlock]
              by_cases heq : blockIdx i = blockIdx j
              · simp only [heq, ite_true]
                symm; apply Finset.sum_eq_zero
                intro p hp
                simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
                split_ifs with h
                · have : p.1 = p.2 := by rw [← h.1, ← h.2]
                  exact absurd this hp
                · rfl
              · simp only [heq, ite_false]
                have hmem : (blockIdx i, blockIdx j) ∈ crossPairs := by
                  simp only [crossPairs, Finset.mem_filter, Finset.mem_univ,
                    true_and]; exact heq
                rw [← Finset.add_sum_erase _ _ hmem]
                simp only [true_and, ite_true]
                suffices hsuff : ∑ x ∈ crossPairs.erase (blockIdx i, blockIdx j),
                    (if blockIdx i = x.1 ∧ blockIdx j = x.2
                      then A i j / (fullB i i - fullB j j) else 0) = 0 by
                  rw [hsuff, add_zero]
                apply Finset.sum_eq_zero; intro p hp
                simp only [Finset.mem_erase] at hp
                split_ifs with h
                · exfalso; exact hp.1 (Prod.ext h.1.symm h.2.symm)
                · rfl
            have hcard : crossPairs.card = 12 := by decide
            -- Bound each embedded block via Sylvester
            have hblock_bound : ∀ p ∈ crossPairs, ‖embedBlock p‖ ≤ 1 / (2 * δ) := by
              intro ⟨k, l⟩ hp
              simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
              -- The m×m Sylvester problem for block pair (k,l)
              let Skl : Matrix (Fin m) (Fin m) ℂ :=
                Matrix.diagonal (fun i => fullB (blockEmbed k i) (blockEmbed k i))
              let Tkl : Matrix (Fin m) (Fin m) ℂ :=
                Matrix.diagonal (fun j => fullB (blockEmbed l j) (blockEmbed l j))
              let Akl : Matrix (Fin m) (Fin m) ℂ :=
                Matrix.of (fun i j => A (blockEmbed k i) (blockEmbed l j))
              let Xkl : Matrix (Fin m) (Fin m) ℂ :=
                fun i j => Akl i j / (Skl i i - Tkl j j)
              have hSkl_diag : IsDiagMatrix Skl := diag_isDiagMatrix _
              have hTkl_diag : IsDiagMatrix Tkl := diag_isDiagMatrix _
              -- Signed separation: the corner difference (1+δ) dominates perturbation (1-δ)
              -- For each (k,l) pair, either Re or Im has a definite-sign gap ≥ 2δ.
              -- We handle all 4 sign cases via negation trick.
              have hSep_abs : ∀ i j, 2 * δ ≤ |(Skl i i - Tkl j j).re| ∨
                  2 * δ ≤ |(Skl i i - Tkl j j).im| := by
                intro i j
                have := hSpectralGap (blockEmbed k i) (blockEmbed l j)
                  (by rw [hBlockIdx_embed, hBlockIdx_embed]; exact hp)
                simp only [Skl, Tkl, Matrix.diagonal_apply_eq] at this ⊢
                exact this
              -- Convert abs separation to signed separation for Sylvester bound
              -- For a fixed (k,l) pair, the corner difference has uniform sign across all (i,j)
              have hSigned : (∀ i j, 2 * δ ≤ (Skl i i - Tkl j j).re) ∨
                  (∀ i j, (Skl i i - Tkl j j).re ≤ -(2 * δ)) ∨
                  (∀ i j, 2 * δ ≤ (Skl i i - Tkl j j).im) ∨
                  (∀ i j, (Skl i i - Tkl j j).im ≤ -(2 * δ)) := by
                -- Perturbation bound: |(1-δ)/2 * x - (1-δ)/2 * y| ≤ 1 - δ when |x|,|y| ≤ 1.
                have hpert : ∀ (x y : ℝ), |x| ≤ 1 → |y| ≤ 1 →
                    -(1 - δ) ≤ (1 - δ) / 2 * x - (1 - δ) / 2 * y ∧
                    (1 - δ) / 2 * x - (1 - δ) / 2 * y ≤ 1 - δ := by
                  intro x y hx hy
                  rw [abs_le] at hx hy
                  constructor <;> nlinarith
                -- Expand Skl i i - Tkl j j into perturbation + corner difference.
                have hDiff_re : ∀ i j, (Skl i i - Tkl j j).re =
                    (1 - δ) / 2 * (Bk k i i).re - (1 - δ) / 2 * (Bk l j j).re +
                    (cornerRe k - cornerRe l) := by
                  intro i j
                  simp only [Skl, Tkl, Matrix.diagonal_apply_eq, fullB,
                    hBlockIdx_embed, hLocalIdx_embed, cornerVal,
                    Complex.sub_re, Complex.add_re, Complex.mul_re,
                    Complex.ofReal_re, Complex.ofReal_im]
                  ring
                have hDiff_im : ∀ i j, (Skl i i - Tkl j j).im =
                    (1 - δ) / 2 * (Bk k i i).im - (1 - δ) / 2 * (Bk l j j).im +
                    (cornerIm k - cornerIm l) := by
                  intro i j
                  simp only [Skl, Tkl, Matrix.diagonal_apply_eq, fullB,
                    hBlockIdx_embed, hLocalIdx_embed, cornerVal,
                    Complex.sub_im, Complex.add_im, Complex.mul_im,
                    Complex.ofReal_re, Complex.ofReal_im]
                  ring
                -- Corner values.
                have hcRe_vals : ∀ a : Fin 4,
                    cornerRe a = (1 + δ) / 2 ∨ cornerRe a = -(1 + δ) / 2 := by
                  intro a; fin_cases a <;> simp [cornerRe]
                have hcIm_vals : ∀ a : Fin 4,
                    cornerIm a = (1 + δ) / 2 ∨ cornerIm a = -(1 + δ) / 2 := by
                  intro a; fin_cases a <;> simp [cornerIm]
                have corner_inj : ∀ (a b : Fin 4),
                    cornerRe a = cornerRe b → cornerIm a = cornerIm b → a = b := by
                  intro a b h1 h2
                  fin_cases a <;> fin_cases b <;> first | rfl |
                    (simp [cornerRe, cornerIm] at h1 h2; linarith)
                -- Since k ≠ l, either cornerRe or cornerIm differs.
                have hcorner_diff : cornerRe k ≠ cornerRe l ∨ cornerIm k ≠ cornerIm l := by
                  by_contra h; push Not at h
                  exact hp (corner_inj _ _ h.1 h.2)
                rcases hcorner_diff with hre_ne | him_ne
                · -- cornerRe k ≠ cornerRe l: real part separates with definite sign
                  rcases hcRe_vals k with hk | hk <;> rcases hcRe_vals l with hl | hl
                  · exact absurd (hk.trans hl.symm) hre_ne
                  · -- cornerRe k - cornerRe l = (1+δ): left disjunct
                    left; intro i j
                    rw [hDiff_re i j]
                    have hxi := (hBk_usq k i).1
                    have hyj := (hBk_usq l j).1
                    have hp1 := (hpert _ _ hxi hyj).1
                    rw [hk, hl]; linarith
                  · -- cornerRe k - cornerRe l = -(1+δ): second disjunct
                    right; left; intro i j
                    rw [hDiff_re i j]
                    have hxi := (hBk_usq k i).1
                    have hyj := (hBk_usq l j).1
                    have hp2 := (hpert _ _ hxi hyj).2
                    rw [hk, hl]; linarith
                  · exact absurd (hk.trans hl.symm) hre_ne
                · -- cornerIm k ≠ cornerIm l: imaginary part separates with definite sign
                  rcases hcIm_vals k with hk | hk <;> rcases hcIm_vals l with hl | hl
                  · exact absurd (hk.trans hl.symm) him_ne
                  · right; right; left; intro i j
                    rw [hDiff_im i j]
                    have hxi := (hBk_usq k i).2
                    have hyj := (hBk_usq l j).2
                    have hp1 := (hpert _ _ hxi hyj).1
                    rw [hk, hl]; linarith
                  · right; right; right; intro i j
                    rw [hDiff_im i j]
                    have hxi := (hBk_usq k i).2
                    have hyj := (hBk_usq l j).2
                    have hp2 := (hpert _ _ hxi hyj).2
                    rw [hk, hl]; linarith
                  · exact absurd (hk.trans hl.symm) him_ne
              have hSylv : ‖Xkl‖ ≤ ‖Akl‖ / (2 * δ) := by
                -- In each of the 4 sign cases, apply sylvester_diag_opNorm_bound_re_or_im
                -- (possibly after negating S, T, or multiplying by -i)
                rcases hSigned with hpos_re | hneg_re | hpos_im | hneg_im
                · -- All Re gaps are ≥ 2δ: direct application
                  exact (sylvester_diag_opNorm_bound_re Skl Tkl Akl
                    hSkl_diag hTkl_diag (2 * δ) (by positivity) hpos_re).2
                · -- All Re gaps are ≤ -2δ: negate S,T,A to get positive separation
                  -- Xkl i j = Akl/(S-T) = (-Akl)/(-S-(-T)) and (-S)-(-T) has Re ≥ 2δ
                  let S' : Matrix (Fin m) (Fin m) ℂ := -Skl
                  let T' : Matrix (Fin m) (Fin m) ℂ := -Tkl
                  let A' : Matrix (Fin m) (Fin m) ℂ := -Akl
                  have hS'_diag : IsDiagMatrix S' := by
                    intro i j hij; simp [S', Skl, Matrix.diagonal, hij]
                  have hT'_diag : IsDiagMatrix T' := by
                    intro i j hij; simp [T', Tkl, Matrix.diagonal, hij]
                  have hSep' : ∀ i j, 2 * δ ≤ (S' i i - T' j j).re := by
                    intro i j
                    simp only [S', T', Matrix.neg_apply, Complex.sub_re, Complex.neg_re]
                    have := hneg_re i j
                    simp only [Complex.sub_re] at this; linarith
                  have hXeq : (fun i j => A' i j / (S' i i - T' j j)) = Xkl := by
                    ext i j
                    simp only [S', T', A', Xkl, Akl, Skl, Tkl, Matrix.neg_apply,
                      Matrix.of_apply, Matrix.diagonal_apply_eq]
                    set a := A (blockEmbed k i) (blockEmbed l j)
                    set b := fullB (blockEmbed k i) (blockEmbed k i)
                    set c := fullB (blockEmbed l j) (blockEmbed l j)
                    show -a / (-b - -c) = a / (b - c)
                    rw [show -b - -c = -(b - c) from by ring, neg_div_neg_eq]
                  have key := (sylvester_diag_opNorm_bound_re S' T' A'
                    hS'_diag hT'_diag (2 * δ) (by positivity) hSep').2
                  rw [hXeq] at key
                  rw [show ‖A'‖ = ‖Akl‖ from by simp [A', norm_neg]] at key
                  exact key
                · exact (sylvester_diag_opNorm_bound_im Skl Tkl Akl
                    hSkl_diag hTkl_diag (2 * δ) (by positivity) hpos_im).2
                · -- All Im gaps are ≤ -2δ: negate to get positive Im separation
                  let S' : Matrix (Fin m) (Fin m) ℂ := -Skl
                  let T' : Matrix (Fin m) (Fin m) ℂ := -Tkl
                  let A' : Matrix (Fin m) (Fin m) ℂ := -Akl
                  have hS'_diag : IsDiagMatrix S' := by
                    intro i j hij; simp [S', Skl, Matrix.diagonal, hij]
                  have hT'_diag : IsDiagMatrix T' := by
                    intro i j hij; simp [T', Tkl, Matrix.diagonal, hij]
                  have hSep' : ∀ i j, 2 * δ ≤ (S' i i - T' j j).im := by
                    intro i j
                    simp only [S', T', Matrix.neg_apply, Complex.sub_im, Complex.neg_im]
                    have := hneg_im i j
                    simp only [Complex.sub_im] at this; linarith
                  have hXeq : (fun i j => A' i j / (S' i i - T' j j)) = Xkl := by
                    ext i j
                    simp only [S', T', A', Xkl, Akl, Skl, Tkl, Matrix.neg_apply,
                      Matrix.of_apply, Matrix.diagonal_apply_eq]
                    set a := A (blockEmbed k i) (blockEmbed l j)
                    set b := fullB (blockEmbed k i) (blockEmbed k i)
                    set c := fullB (blockEmbed l j) (blockEmbed l j)
                    show -a / (-b - -c) = a / (b - c)
                    rw [show -b - -c = -(b - c) from by ring, neg_div_neg_eq]
                  have key := (sylvester_diag_opNorm_bound_im S' T' A'
                    hS'_diag hT'_diag (2 * δ) (by positivity) hSep').2
                  rw [hXeq] at key
                  rw [show ‖A'‖ = ‖Akl‖ from by simp [A', norm_neg]] at key
                  exact key
              -- ‖Akl‖ ≤ ‖A‖ = 1 (cross-submatrix bound)
              have hAkl_norm : ‖Akl‖ ≤ 1 := by
                rw [← hnorm]
                exact cross_submatrix_norm_le (blockEmbed k) (blockEmbed l)
                  (hblockEmbed_inj k) (hblockEmbed_inj l) A
              -- ‖embedBlock (k,l)‖ ≤ ‖Xkl‖ (embedding into larger matrix)
              -- ‖embedBlock (k,l)‖ ≤ ‖Xkl‖: embedding into larger matrix
              -- Proof sketch: embedBlock acts on l-th block of v, outputs to k-th block.
              -- ‖embedBlock v‖ = ‖Xkl * v_l‖ ≤ ‖Xkl‖ * ‖v_l‖ ≤ ‖Xkl‖ * ‖v‖.
              have hembed_norm : ‖embedBlock (k, l)‖ ≤ ‖Xkl‖ := by
                apply embedBlock_norm_le (blockEmbed k) (blockEmbed l)
                  (hblockEmbed_inj k) (hblockEmbed_inj l)
                  (embedBlock (k, l)) Xkl
                · -- hM_row_zero: if no i' with blockEmbed k i' = i, then M i j = 0
                  intro i j hrow
                  simp only [embedBlock]
                  have hbi : blockIdx i ≠ k := by
                    intro hbi
                    exact hrow (localIdx i) (by rw [← hbi]; exact hEmbed_id i)
                  rw [if_neg (fun h => hbi h.1)]
                · -- hM_col_zero
                  intro i j hcol
                  simp only [embedBlock]
                  have hbj : blockIdx j ≠ l := by
                    intro hbj
                    exact hcol (localIdx j) (by rw [← hbj]; exact hEmbed_id j)
                  rw [if_neg (fun h => hbj h.2)]
                · -- hM_eq: M (blockEmbed k i) (blockEmbed l j) = Xkl i j
                  intro i j
                  simp only [embedBlock, Xkl, Akl, Skl, Tkl,
                    Matrix.of_apply, Matrix.diagonal_apply_eq,
                    hBlockIdx_embed, and_self, if_true]
              calc ‖embedBlock (k, l)‖ ≤ ‖Xkl‖ := hembed_norm
                _ ≤ ‖Akl‖ / (2 * δ) := hSylv
                _ ≤ 1 / (2 * δ) := by
                    apply div_le_div_of_nonneg_right hAkl_norm (by positivity)
            rw [hcross_sum]
            calc ‖∑ p ∈ crossPairs, embedBlock p‖
                ≤ ∑ p ∈ crossPairs, ‖embedBlock p‖ := norm_sum_le crossPairs embedBlock
              _ ≤ ∑ _p ∈ crossPairs, (1 / (2 * δ)) :=
                  Finset.sum_le_sum hblock_bound
              _ = crossPairs.card • (1 / (2 * δ)) := by rw [Finset.sum_const]
              _ = 12 * (1 / (2 * δ)) := by rw [hcard]; simp
              _ = 6 / δ := by ring
    exact ⟨fullB, fullC, hfullB_diag, hfullB_usq, hComm, hfullC_bound⟩

/-- ε ≤ 1/2 case of the 4-block bound: weaker than `lambdaA_four_block_bound`
    (since `6/ε ≤ 6/ε²` when `0 < ε ≤ 1/2 < 1`). Direct corollary, no BT needed
    for THIS signature (the strengthened `(1+ε)·lambdaM m + 6/ε² + 1` shape that
    the consumer site needs is genuinely stronger and would require BT). -/
lemma lambdaA_bt_improved_bound {m : ℕ} (ε : ℝ) (hε : 0 < ε) (hε_half : ε ≤ 1 / 2)
    (A : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ)
    (hzd : ZeroDiag A) (hnorm : ‖A‖ = 1) :
    lambdaA A ≤ (2 / (1 - ε)) * lambdaM m + 6 / ε ^ 2 := by
  have hε1 : ε < 1 := by linarith
  have hbase := lambdaA_four_block_bound ε hε hε1 A hzd hnorm
  have hε2_le_ε : ε ^ 2 ≤ ε := by nlinarith
  have hε2_pos : 0 < ε ^ 2 := by positivity
  have hstep : 6 / ε ≤ 6 / ε ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) hε2_pos hε2_le_ε
  linarith

/-- Core 4-block recursion (JOS 2013, Claim 1 variant):
    For any construction parameter δ ∈ (0,1), λ(4m) ≤ (2/(1-δ))·λ(m) + 6/δ.
    Proof: view the (4m)×(4m) matrix A as 4 blocks of m×m. Scale each diagonal
    block's InUnitSquare decomposition by (1-δ)/2 and shift by (1+δ)/2 × corner.
    The diagonal blocks contribute 2/(1-δ) · lambdaM(m). The cross-block entries
    are solved via the Sylvester equation with spectral gap ≥ 2δ, giving
    operator norm ≤ 1/(2δ) per block pair × 12 pairs = 6/δ. -/
lemma lambdaM_four_block_recursion (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ (m : ℕ), lambdaM (4 * m) ≤ 2 / (1 - δ) * lambdaM m + 6 / δ := by
  intro m
  unfold lambdaM
  set S := lambdaA '' {A : Matrix (Fin (4 * m)) (Fin (4 * m)) ℂ | ZeroDiag A ∧ ‖A‖ = 1}
  set bound := 2 / (1 - δ) * lambdaM m + 6 / δ
  by_cases hne : S.Nonempty
  · -- S nonempty: show every element ≤ bound
    apply csSup_le hne
    intro x hx
    obtain ⟨A, ⟨hzd, hnorm⟩, rfl⟩ := hx
    exact lambdaA_four_block_bound δ hδ hδ1 A hzd hnorm
  · -- S empty: sSup ∅ = 0 ≤ bound
    rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp only [Real.sSup_empty]
    have h1 : (0 : ℝ) < 1 - δ := by linarith
    have h2 : (0 : ℝ) ≤ lambdaM m := by
      unfold lambdaM
      exact Real.sSup_nonneg (fun x hx => by
        obtain ⟨A, _, rfl⟩ := hx; exact lambdaA_nonneg A)
    positivity

/-- Base case bound: lambdaM at small values is bounded by some constant.
    For 1×1 matrices, the only zero-diagonal matrix is 0, which has norm 0 ≠ 1,
    so the defining set is empty and lambdaM 1 = 0. -/
private lemma lambdaM_base_bound : ∃ (B : ℝ), 0 < B ∧ lambdaM 1 ≤ B := ⟨1, one_pos, by
  unfold lambdaM
  by_cases hne : (lambdaA '' {A : Matrix (Fin 1) (Fin 1) ℂ | ZeroDiag A ∧ ‖A‖ = 1}).Nonempty
  · exfalso
    obtain ⟨_, A, ⟨hzd, hnorm⟩, rfl⟩ := hne
    have : A = 0 := by
      ext i j; fin_cases i; fin_cases j; exact hzd 0
    rw [this, norm_zero] at hnorm; linarith
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp⟩


/-! ### Helper lemmas for `lambdaM_pow4_paper_bound`

The paper's Eq. [4] is derived (JOS 2013, PNAS pp.19253–19254) by an outer
induction on `k` with an inner `l`-fold inductive iteration of Claim 1
(`lambdaA_four_block_bound`) combined with `bourgain_tzafriri_iterated`.

We package the two layers as helper lemmas:

* `lambdaM_pow4_paper_base` — the base case `k = 1` (paper Eq. [3]):
  `λ(4ⁿ) ≤ K · n^3 · 2^{n/2}`.  Obtained from `l = n/2` iterations of Claim 1
  against `bourgain_tzafriri_iterated` with `ε = 1/l`.

* `lambdaM_pow4_paper_step` — the bootstrap `k → k+1` (paper Eqs. [2]/[3]
  re-iterated): given the bound for `k`, derive the bound for `k+1` by another
  inner iteration of Claim 1 + BT with `ε = 1/l`, `l ≈ n/(2(k+1))`.

Historical development note: early drafts left the inner iteration arguments
as placeholders and treated the BT inputs as axioms. This describes the earlier
implementation, not the current proof status; use `AxiomAudit.lean` to inspect
the current declarations' axiom dependencies. -/

/-- Auxiliary "harmonic-δ" iteration of `lambdaM_four_block_recursion`.

The supremum-level recursion `λ(4m) ≤ (2/(1-δ))·λ(m) + 6/δ` with `δ = 1/(n+2)` at the
`n`-th step gives a multiplicative factor `2·(n+2)/(n+1)`.  Telescoping over `n` steps
yields a product `2^n · ∏_{i<n} (i+2)/(i+1) = 2^n · (n+1)`.  Hence one obtains a bound

  `λ(4ⁿ) ≤ K · (n+1) · 2ⁿ`

with an *explicit* constant `K` that absorbs both `lambdaM(1)` and the geometric error
series.  This is the **non-BT route** to the `2ⁿ` rate appearing in the paper's
Eq. [3] base-case shape; it is strictly weaker than the paper's full Eq. [3] (which
gives `2^{n/2}`) but it suffices for the `k = 1` instance of Eq. [4] required here.

The numerical constant `K = 18` below has no special significance — any constant
`≥ 6 · sup_n (n+1)(n+2)/2ⁿ ≈ 9` plus the base bound `lambdaM 1 ≤ 1` works. -/
lemma lambdaM_pow4_linear_2n_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      lambdaM (4 ^ n) ≤ K * ((n : ℝ) + 1) * (2 : ℝ) ^ n := by
  -- The IH carries an additive `M · 2^n` slack: `λ(4ⁿ) ≤ K · n · 2ⁿ + M · 2ⁿ`.
  -- Strategy: induction on `n`.  Base `n = 0`: `lambdaM(1) = 0` (the defining set
  -- is empty), so any `K, M ≥ 0` works.  Step `n → n+1`: apply
  -- `lambdaM_four_block_recursion` with `δ = 1/(n+2)`, giving factor
  -- `2(n+2)/(n+1)` and additive `6(n+2)`.  Telescoping with the harmonic δ
  -- precisely yields `K(n+1)·2^{n+1} + M·2^{n+1}` provided `K - M ≥ 9`.
  -- We package it as a single bound `K · (n+1) · 2^n` with `K = 18`.
  refine ⟨18, by norm_num, fun n => ?_⟩
  -- Strengthened IH: `lambdaM(4^n) ≤ 17·n·2^n + 2^n = (17n + 1)·2^n`.
  -- Note `(17n + 1) ≤ 18(n+1)` since `1 ≤ 18` and `17n ≤ 18n`.
  -- We prove `lambdaM(4^n) ≤ 17·n·2^n + 2^n` by induction.
  suffices h : ∀ m : ℕ, lambdaM (4 ^ m) ≤ 17 * (m : ℝ) * (2 : ℝ) ^ m + (2 : ℝ) ^ m by
    have hbd := h n
    have h2n_nn : (0 : ℝ) ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc lambdaM (4 ^ n)
        ≤ 17 * (n : ℝ) * (2 : ℝ) ^ n + (2 : ℝ) ^ n := hbd
      _ = (17 * (n : ℝ) + 1) * (2 : ℝ) ^ n := by ring
      _ ≤ 18 * ((n : ℝ) + 1) * (2 : ℝ) ^ n := by
          have : 17 * (n : ℝ) + 1 ≤ 18 * ((n : ℝ) + 1) := by nlinarith
          exact mul_le_mul_of_nonneg_right this h2n_nn
  intro m
  induction m with
  | zero =>
      -- `lambdaM(4^0) = lambdaM(1) ≤ 1 ≤ 0 + 1` (using `lambdaM_base_bound`).
      have hlm1 : lambdaM 1 ≤ 1 := by
        unfold lambdaM
        by_cases hne :
            (lambdaA '' {A : Matrix (Fin 1) (Fin 1) ℂ | ZeroDiag A ∧ ‖A‖ = 1}).Nonempty
        · exfalso
          obtain ⟨_, A, ⟨hzd, hnorm⟩, rfl⟩ := hne
          have : A = 0 := by
            ext i j; fin_cases i; fin_cases j; exact hzd 0
          rw [this, norm_zero] at hnorm; linarith
        · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
      change lambdaM (4 ^ 0) ≤ 17 * ((0 : ℕ) : ℝ) * (2 : ℝ) ^ 0 + (2 : ℝ) ^ 0
      simp only [pow_zero, Nat.cast_zero, mul_zero, zero_mul, zero_add]
      exact hlm1
  | succ n ih =>
      -- Apply `lambdaM_four_block_recursion` with `δ := 1/(n+2)`.
      set δ : ℝ := 1 / ((n : ℝ) + 2) with hδ_def
      have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
      have hδ_lt_one : δ < 1 := by
        rw [hδ_def, div_lt_one hn2_pos]; linarith
      have hrec :
          lambdaM (4 * 4 ^ n) ≤ 2 / (1 - δ) * lambdaM (4 ^ n) + 6 / δ :=
        lambdaM_four_block_recursion δ hδ_pos hδ_lt_one (4 ^ n)
      -- `4^(n+1) = 4 · 4^n` (in ℕ).
      have hpow : (4 : ℕ) ^ (n + 1) = 4 * 4 ^ n := by
        rw [pow_succ]; ring
      rw [hpow]
      -- Compute `2/(1-δ) = 2(n+2)/(n+1)` and `6/δ = 6(n+2)`.
      have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hn2_ne : ((n : ℝ) + 2) ≠ 0 := ne_of_gt hn2_pos
      have hn1_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn1_pos
      have h1mδ : 1 - δ = ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
        rw [hδ_def]
        field_simp
        ring
      have h2_div : 2 / (1 - δ) = 2 * ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
        rw [h1mδ, div_div_eq_mul_div]
      have h6_div : 6 / δ = 6 * ((n : ℝ) + 2) := by
        rw [hδ_def]; field_simp
      -- IH: `lambdaM(4^n) ≤ 17·n·2^n + 2^n`.
      -- Bound: `lambdaM(4·4^n) ≤ 2(n+2)/(n+1) · (17·n·2^n + 2^n) + 6(n+2)`.
      have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
      have h2n_nn : (0 : ℝ) ≤ (2 : ℝ) ^ n := le_of_lt h2n_pos
      have hfactor_pos : (0 : ℝ) < 2 * ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
        positivity
      have hfactor_nn : (0 : ℝ) ≤ 2 * ((n : ℝ) + 2) / ((n : ℝ) + 1) :=
        le_of_lt hfactor_pos
      have hih_scaled :
          2 * ((n : ℝ) + 2) / ((n : ℝ) + 1) * lambdaM (4 ^ n) ≤
            2 * ((n : ℝ) + 2) / ((n : ℝ) + 1) *
              (17 * (n : ℝ) * (2 : ℝ) ^ n + (2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left ih hfactor_nn
      have hrec' :
          lambdaM (4 * 4 ^ n) ≤
            2 * ((n : ℝ) + 2) / ((n : ℝ) + 1) *
              (17 * (n : ℝ) * (2 : ℝ) ^ n + (2 : ℝ) ^ n) +
            6 * ((n : ℝ) + 2) := by
        have := hrec
        rw [h2_div, h6_div] at this
        linarith
      -- Show RHS ≤ `17(n+1)·2^{n+1} + 2^{n+1}`.
      have htarget :
          2 * ((n : ℝ) + 2) / ((n : ℝ) + 1) *
            (17 * (n : ℝ) * (2 : ℝ) ^ n + (2 : ℝ) ^ n) +
          6 * ((n : ℝ) + 2) ≤
          17 * ((n : ℝ) + 1) * (2 : ℝ) ^ (n + 1) + (2 : ℝ) ^ (n + 1) := by
        -- Compute `2·(n+2)/(n+1) · (17n+1)·2^n + 6(n+2) ≤ (17(n+1)+1)·2^{n+1}`
        -- ⇔ `(n+2)(17n+1)·2^{n+1}/(n+1) + 6(n+2) ≤ (17n+18)·2^{n+1}`.
        -- Multiply both sides by (n+1) (positive):
        -- ⇔ `(n+2)(17n+1)·2^{n+1} + 6(n+2)(n+1) ≤ (17n+18)(n+1)·2^{n+1}`
        -- ⇔ `6(n+2)(n+1) ≤ [(17n+18)(n+1) - (n+2)(17n+1)] · 2^{n+1}`
        -- `(17n+18)(n+1) - (n+2)(17n+1) = 17n²+35n+18 - (17n²+35n+2) = 16`
        -- So need `6(n+2)(n+1) ≤ 16 · 2^{n+1} = 32·2^n`.
        -- i.e. `3(n+1)(n+2) ≤ 16 · 2^n`. Check n=0: 3·1·2 = 6 ≤ 16 ✓.
        -- n=1: 18 ≤ 32 ✓; n=2: 36 ≤ 64 ✓; n=3: 60 ≤ 128 ✓.
        -- General: `(n+1)(n+2) ≤ 6·2^n` by simple induction.
        have hkey : 3 * ((n : ℝ) + 1) * ((n : ℝ) + 2) ≤ 16 * (2 : ℝ) ^ n := by
          -- Prove `(n+1)(n+2) ≤ 6·2^n` ⇒ `3(n+1)(n+2) ≤ 18·2^n ≤ ...`
          -- Easier: directly induction.
          have h_aux : ∀ m : ℕ, 3 * ((m : ℝ) + 1) * ((m : ℝ) + 2) ≤ 16 * (2 : ℝ) ^ m := by
            intro m
            induction m with
            | zero => norm_num
            | succ k ihk =>
                have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
                have h2k_nn : (0 : ℝ) ≤ (2 : ℝ) ^ k := le_of_lt h2k_pos
                have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
                -- Goal: `3 · (k+2) · (k+3) ≤ 16 · 2^{k+1} = 32·2^k`.
                -- ihk: `3 · (k+1) · (k+2) ≤ 16 · 2^k`.
                -- (k+2)(k+3) = (k+1)(k+2) + 2(k+2).
                -- So 3(k+2)(k+3) = 3(k+1)(k+2) + 6(k+2).
                -- We need 3(k+1)(k+2) + 6(k+2) ≤ 32·2^k.
                -- From ihk: 3(k+1)(k+2) ≤ 16·2^k. Need 6(k+2) ≤ 16·2^k.
                -- For k=0: 12 ≤ 16 ✓. For k≥1: 6(k+2) ≤ 18k ≤ k·16·2^k/(k+1)... easier:
                -- 6(k+2) ≤ 16·2^k? k=0: 12≤16. k=1: 18≤32. k=2: 24≤64.
                -- Induct: f(k) = 6(k+2), g(k) = 16·2^k. f(k+1)-f(k) = 6, g(k+1)-g(k) = 16·2^k ≥ 16.
                have h6k2_le : 6 * ((k : ℝ) + 2) ≤ 16 * (2 : ℝ) ^ k := by
                  have hsub : ∀ j : ℕ, 6 * ((j : ℝ) + 2) ≤ 16 * (2 : ℝ) ^ j := by
                    intro j
                    induction j with
                    | zero => norm_num
                    | succ i ih2 =>
                        have h2i_pos : (0 : ℝ) < (2 : ℝ) ^ i := pow_pos (by norm_num) i
                        have h2i_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
                        have hpow_i : (2 : ℝ) ^ (i + 1) = 2 * (2 : ℝ) ^ i := by ring
                        rw [hpow_i]
                        push_cast
                        nlinarith [ih2, h2i_ge1]
                  exact hsub k
                have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
                rw [hpow]
                push_cast
                nlinarith [ihk, h6k2_le, h2k_nn, hk_nn]
          exact h_aux n
        -- Now combine into the polynomial inequality.
        have hpow_succ : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by ring
        rw [hpow_succ]
        -- Need: `2·(n+2)/(n+1) · ((17n+1)·2^n) + 6(n+2) ≤ (17n+18)·2·2^n`
        -- Multiply both sides by (n+1):
        -- (n+2)(17n+1)·2·2^n + 6(n+2)(n+1) ≤ (17n+18)·2·2^n·(n+1)
        -- 2·2^n·[(17n+18)(n+1) - (n+2)(17n+1)] ≥ 6(n+2)(n+1)
        -- LHS factor = 16. So 32·2^n ≥ 6(n+2)(n+1), i.e., 16·2^n ≥ 3(n+1)(n+2). ✓
        have hLHS : 2 * ((n : ℝ) + 2) / ((n : ℝ) + 1) *
                      (17 * (n : ℝ) * (2 : ℝ) ^ n + (2 : ℝ) ^ n) =
                    (((n : ℝ) + 2) * (17 * (n : ℝ) + 1) / ((n : ℝ) + 1)) * (2 * (2 : ℝ) ^ n) := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
          congr 1
          ring
        rw [hLHS]
        have hRHS : 17 * ((n : ℝ) + 1) * (2 * (2 : ℝ) ^ n) + 2 * (2 : ℝ) ^ n =
                    (17 * ((n : ℝ) + 1) + 1) * (2 * (2 : ℝ) ^ n) := by ring
        rw [hRHS]
        -- Now: `((n+2)(17n+1)/(n+1)) · X + 6(n+2) ≤ (17n+18) · X`
        -- where X = 2·2^n. ⇔ `(17n+18)X - ((n+2)(17n+1)/(n+1))·X ≥ 6(n+2)`
        -- ⇔ `X · [(17n+18)(n+1) - (n+2)(17n+1)]/(n+1) ≥ 6(n+2)`
        -- LHS num = `17n²+35n+18 - 17n²-35n-2 = 16`. So `X · 16/(n+1) ≥ 6(n+2)`,
        -- i.e., `16X ≥ 6(n+1)(n+2)`, i.e., `32·2^n ≥ 6(n+1)(n+2)`, i.e., `16·2^n ≥ 3(n+1)(n+2)`.
        have hineq : (((n : ℝ) + 2) * (17 * (n : ℝ) + 1) / ((n : ℝ) + 1)) * (2 * (2 : ℝ) ^ n) +
                     6 * ((n : ℝ) + 2) ≤
                     (17 * ((n : ℝ) + 1) + 1) * (2 * (2 : ℝ) ^ n) := by
          -- Rewrite LHS division: `(a/b)·c = a·c/b`.
          rw [div_mul_eq_mul_div]
          -- Goal: `(n+2)(17n+1)·(2·2^n) / (n+1) + 6(n+2) ≤ (17(n+1)+1)·(2·2^n)`
          -- Subtract: equivalent to multiplying both sides by (n+1):
          --   `(n+2)(17n+1)·2·2^n + 6(n+2)(n+1) ≤ (17(n+1)+1)·2·2^n·(n+1)`
          have hgoal : ((n : ℝ) + 2) * (17 * (n : ℝ) + 1) * (2 * (2 : ℝ) ^ n) +
                       6 * ((n : ℝ) + 2) * ((n : ℝ) + 1) ≤
                       (17 * ((n : ℝ) + 1) + 1) * (2 * (2 : ℝ) ^ n) * ((n : ℝ) + 1) := by
            nlinarith [hkey, h2n_nn, hn1_pos, hn2_pos]
          -- Convert back.
          have hsub :
              ((n : ℝ) + 2) * (17 * (n : ℝ) + 1) * (2 * (2 : ℝ) ^ n) / ((n : ℝ) + 1) +
                6 * ((n : ℝ) + 2) ≤
              (17 * ((n : ℝ) + 1) + 1) * (2 * (2 : ℝ) ^ n) := by
            rw [div_add' _ _ _ hn1_ne, div_le_iff₀ hn1_pos]
            linarith
          exact hsub
        linarith
      push_cast
      linarith


/-! The former `k`-by-`k` paper bootstrap is retained below as historical
source commentary only.  The active proof now uses the stronger direct
geometric consequence of the genuine Claim 2 recurrence. -/
/-
/-- Base case (paper Eq. [3]) of `lambdaM_pow4_paper_bound`: `λ(4ⁿ) ≤ K · n^3 · 2^{n/2}`,
i.e. the `k = 1` instance with `(log 4ⁿ)^{4·1−1} · (4ⁿ)^{1/(2·1)}` shape.

The bound is derived from `lambdaM_pow4_linear_2n_bound` (which gives the weaker
`K·(n+1)·2ⁿ` bound from the supremum-level recursion alone) combined with the
elementary inequality `(n+1) ≤ K' · n^3 · (log 4)^3` for `n ≥ 1`; the `n = 0`
case is handled trivially since `lambdaM(1) = 0` and `log 1 = 0`. -/
private lemma lambdaM_pow4_paper_base :
    ∃ K : ℝ, 0 < K ∧
    ∀ n : ℕ, lambdaM (4 ^ n) ≤
      K * (Real.log ((4 : ℝ) ^ n)) ^ (4 * 1 - 1) *
        ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * ((1 : ℕ) : ℝ))) := by
  -- We use the harmonic-δ-iterated bound `λ(4ⁿ) ≤ K₀·(n+1)·2ⁿ`.
  obtain ⟨K₀, hK₀_pos, hK₀_bd⟩ := lambdaM_pow4_linear_2n_bound
  -- The target RHS is `K · (n·L)^3 · 2ⁿ` where `L = log 4`.  Compare with `K₀(n+1)·2ⁿ`:
  -- need `K₀·(n+1) ≤ K · (n·L)^3`.  For `n ≥ 1`: `(n+1) ≤ 2n` and `n ≤ n^3`, so
  -- `K₀(n+1) ≤ 2K₀·n ≤ 2K₀·n^3 = (2K₀/L^3) · (nL)^3`.  For `n = 0`: both sides are 0.
  set L : ℝ := Real.log 4 with hL_def
  have hL_pos : 0 < L := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hL3_pos : 0 < L ^ 3 := pow_pos hL_pos 3
  -- The target's `(log 4^n)` simplifies to `n·L`.
  set K : ℝ := 2 * K₀ / L ^ 3 + 1 with hK_def
  have hK_pos : 0 < K := by
    have : 0 < 2 * K₀ / L ^ 3 := by positivity
    linarith
  refine ⟨K, hK_pos, fun n => ?_⟩
  -- Simplify `(4^n)^(1/(2·1)) = (4^n)^(1/2)`.
  -- Note that `((1:ℕ):ℝ) = 1` so the exponent becomes `1/2`.
  have h4_pos : (0 : ℝ) < (4 : ℝ) ^ n := pow_pos (by norm_num) n
  have h4_nn : (0 : ℝ) ≤ (4 : ℝ) ^ n := le_of_lt h4_pos
  -- `(4^n)^(1/2) = 2^n`.
  have h4n_half : ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * ((1 : ℕ) : ℝ))) = (2 : ℝ) ^ n := by
    have h1cast : ((1 : ℕ) : ℝ) = 1 := by norm_cast
    rw [h1cast]
    have hexp : (1 : ℝ) / (2 * 1) = 1 / 2 := by norm_num
    rw [hexp]
    -- Use `(4^n)^(1/2) = (4^(1/2))^n` via rpow gymnastics, but easier:
    -- `(4^n)^(1/2) = ((2^2)^n)^(1/2) = (2^(2n))^(1/2) = 2^(2n·(1/2)) = 2^n`.
    have h4eq : ((4 : ℝ) ^ n) = (2 : ℝ) ^ (2 * n) := by
      have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [this, ← pow_mul]
    rw [h4eq]
    rw [show ((2 : ℝ) ^ (2 * n) : ℝ) = ((2 : ℝ) ^ ((2 * n : ℕ) : ℝ)) from
          (Real.rpow_natCast _ (2 * n)).symm,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hexpval : ((2 * n : ℕ) : ℝ) * (1 / 2) = (n : ℝ) := by push_cast; ring
    rw [hexpval, Real.rpow_natCast]
  -- `log (4^n) = n·L`.
  have h_log : Real.log ((4 : ℝ) ^ n) = (n : ℝ) * L := by
    rw [hL_def, Real.log_pow]
  -- The target exponent on `log` is `4 * 1 - 1 = 3`.
  rw [h4n_half, h_log]
  -- Goal: `lambdaM (4 ^ n) ≤ K * ((n : ℝ) * L) ^ (4 * 1 - 1) * 2 ^ n`.
  simp only [Nat.reduceMul, Nat.sub_self, Nat.add_zero]
  -- `4 * 1 - 1 = 3`.
  have hpow_eq : (4 * 1 - 1 : ℕ) = 3 := by norm_num
  rw [hpow_eq]
  have h_factor : ((n : ℝ) * L) ^ 3 = (n : ℝ) ^ 3 * L ^ 3 := mul_pow _ _ _
  rw [h_factor]
  -- Goal: `lambdaM(4^n) ≤ K · (n^3 · L^3) · 2^n`.
  have hbd_n := hK₀_bd n
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have h2n_nn : (0 : ℝ) ≤ (2 : ℝ) ^ n := le_of_lt h2n_pos
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- Case split on n = 0 vs n ≥ 1.
  by_cases hn0 : n = 0
  · subst hn0
    -- `lambdaM(4^0) = lambdaM(1) ≤ 1` (`lambdaM_base_bound`).
    -- RHS: `K · (0^3 · L^3) · 2^0 = K · 0 = 0`.  But LHS could be `> 0`!
    -- Fortunately `lambdaM(1) = 0` (the set is empty), so LHS = 0.
    have hlm1_eq : lambdaM 1 = 0 := by
      unfold lambdaM
      by_cases hne :
          (lambdaA '' {A : Matrix (Fin 1) (Fin 1) ℂ | ZeroDiag A ∧ ‖A‖ = 1}).Nonempty
      · exfalso
        obtain ⟨_, A, ⟨hzd, hnorm⟩, rfl⟩ := hne
        have : A = 0 := by
          ext i j; fin_cases i; fin_cases j; exact hzd 0
        rw [this, norm_zero] at hnorm; linarith
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact Real.sSup_empty
    simp only [pow_zero, Nat.cast_zero, ne_eq, zero_pow, mul_zero, zero_mul]
    rw [hlm1_eq]
    simp
  · -- n ≥ 1.
    push_neg at hn0
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    -- `K₀·(n+1)·2^n ≤ K · n³ · L³ · 2^n`.
    -- Suffices: `K₀·(n+1) ≤ K · n³ · L³`.  Use `(n+1) ≤ 2n` for `n ≥ 1`,
    -- and `n ≤ n³`, so `K₀·(n+1) ≤ 2K₀·n ≤ 2K₀·n³ ≤ K · n³ · L³` since
    -- `K · L³ = (2K₀/L³ + 1) · L³ = 2K₀ + L³ ≥ 2K₀`.
    have hcoef : K₀ * ((n : ℝ) + 1) ≤ K * ((n : ℝ) ^ 3 * L ^ 3) := by
      have h_n1 : ((n : ℝ) + 1) ≤ 2 * (n : ℝ) := by linarith
      have h_n_le_n3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
        have : (n : ℝ) ^ 3 = (n : ℝ) * (n : ℝ) * (n : ℝ) := by ring
        rw [this]
        have : (n : ℝ) * (n : ℝ) * (n : ℝ) = (n : ℝ) * ((n : ℝ) * (n : ℝ)) := by ring
        rw [this]
        have h_n_sq_ge_one : (1 : ℝ) ≤ (n : ℝ) * (n : ℝ) := by nlinarith
        have hnn : (0 : ℝ) ≤ (n : ℝ) := hn_nn
        nlinarith
      have hK₀_nn : 0 ≤ K₀ := le_of_lt hK₀_pos
      have h_step1 : K₀ * ((n : ℝ) + 1) ≤ K₀ * (2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left h_n1 hK₀_nn
      have h_step2 : K₀ * (2 * (n : ℝ)) ≤ K₀ * (2 * (n : ℝ) ^ 3) := by
        have : 2 * (n : ℝ) ≤ 2 * (n : ℝ) ^ 3 := by linarith
        exact mul_le_mul_of_nonneg_left this hK₀_nn
      have h_step3 : K₀ * (2 * (n : ℝ) ^ 3) ≤ K * ((n : ℝ) ^ 3 * L ^ 3) := by
        -- `K · L^3 = 2K₀ + L^3 ≥ 2K₀`.
        have hKL3 : K * L ^ 3 = 2 * K₀ + L ^ 3 := by
          rw [hK_def]; field_simp
        have hKL3_ge : 2 * K₀ ≤ K * L ^ 3 := by
          rw [hKL3]; linarith [pow_pos hL_pos 3]
        have hn3_nn : (0 : ℝ) ≤ (n : ℝ) ^ 3 := pow_nonneg hn_nn 3
        calc K₀ * (2 * (n : ℝ) ^ 3)
            = 2 * K₀ * (n : ℝ) ^ 3 := by ring
          _ ≤ K * L ^ 3 * (n : ℝ) ^ 3 :=
              mul_le_mul_of_nonneg_right hKL3_ge hn3_nn
          _ = K * ((n : ℝ) ^ 3 * L ^ 3) := by ring
      linarith
    -- Multiply through by `2^n`.
    calc lambdaM (4 ^ n)
        ≤ K₀ * ((n : ℝ) + 1) * (2 : ℝ) ^ n := hbd_n
      _ ≤ K * ((n : ℝ) ^ 3 * L ^ 3) * (2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right hcoef h2n_nn

set_option maxHeartbeats 1600000 in
/-- Inductive step (paper bootstrap, Eq. [2] re-iterated): given Eq. [4] at level `k`,
derive it at level `k + 1`.

Discharged using `lambdaM_pow4_BT_iterated_recursion` (a packaged form of paper
Eq. [2] + Claim 2 lift, axiomatised in `BourgainTzafriri.lean`) plus the IH at
level `k`, with the BT depth choice `l = ⌈n/(k+1)⌉`. Small `n` is absorbed via
the harmonic-δ `lambdaM_pow4_linear_2n_bound`. -/
private lemma lambdaM_pow4_paper_step (k : ℕ) (_hk : 1 ≤ k)
    (_IH : ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, lambdaM (4 ^ n) ≤
        K * (Real.log ((4 : ℝ) ^ n)) ^ (4 * k - 1) *
          ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * ((k : ℕ) : ℝ)))) :
    ∃ K : ℝ, 0 < K ∧
    ∀ n : ℕ, lambdaM (4 ^ n) ≤
      K * (Real.log ((4 : ℝ) ^ n)) ^ (4 * (k + 1) - 1) *
        ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (((k + 1) : ℕ) : ℝ))) := by
  -- Plug IH into the BT-iterated supremum recursion
  -- (`lambdaM_pow4_BT_iterated_recursion`, paper Eq. [2]+Claim 2) and pick
  -- `l = ⌈n/(k+1)⌉ = (n + k) / (k + 1)`.  Small n is absorbed via
  -- `lambdaM_pow4_linear_2n_bound`.
  obtain ⟨K_IH, hK_IH_pos, hIH⟩ := _IH
  obtain ⟨K_BT, hK_BT_pos, hBT⟩ := lambdaM_pow4_BT_iterated_recursion
  obtain ⟨K_lin, hK_lin_pos, hK_lin⟩ := lambdaM_pow4_linear_2n_bound
  set L : ℝ := Real.log 4 with hL_def
  have hL_pos : 0 < L := Real.log_pos (by norm_num)
  have hL_nn : 0 ≤ L := le_of_lt hL_pos
  have hL_ge_one : (1 : ℝ) ≤ L := by
    rw [hL_def]
    have h_exp_le : Real.exp 1 ≤ 4 := by
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_le_log (Real.exp_pos 1) h_exp_le
    rw [Real.log_exp] at this; exact this
  have hLp_pos : 0 < L ^ (4 * k + 3) := pow_pos hL_pos _
  -- Final constant `K_main` covers all three cases.
  set K_main : ℝ :=
      K_BT * K_IH + 16 * K_BT / L ^ (4 * k + 3) +
      K_lin * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1) / L ^ (4 * k + 3) + 1
    with hK_main_def
  have hK_main_pos : 0 < K_main := by
    rw [hK_main_def]
    have h1 : 0 < K_BT * K_IH := mul_pos hK_BT_pos hK_IH_pos
    have h2 : 0 < 16 * K_BT / L ^ (4 * k + 3) := by positivity
    have h3 : 0 < K_lin * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1) / L ^ (4 * k + 3) := by positivity
    linarith
  refine ⟨K_main, hK_main_pos, fun n => ?_⟩
  have hexp_eq : 4 * (k + 1) - 1 = 4 * k + 3 := by omega
  have hk1_R_eq : (((k + 1) : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hexp_eq, hk1_R_eq]
  set t : ℝ := (1 : ℝ) / (2 * ((k : ℝ) + 1)) with ht_def
  have hk_R_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast _hk
  have hk1_R_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have ht_pos : 0 < t := by rw [ht_def]; positivity
  have h_log : Real.log ((4 : ℝ) ^ n) = (n : ℝ) * L := by rw [hL_def, Real.log_pow]
  rw [h_log]
  have hlm1_eq : lambdaM 1 = 0 := by
    unfold lambdaM
    by_cases hne :
        (lambdaA '' {A : Matrix (Fin 1) (Fin 1) ℂ | ZeroDiag A ∧ ‖A‖ = 1}).Nonempty
    · exfalso
      obtain ⟨_, A, ⟨hzd, hnorm⟩, rfl⟩ := hne
      have : A = 0 := by ext i j; fin_cases i; fin_cases j; exact hzd 0
      rw [this, norm_zero] at hnorm; linarith
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact Real.sSup_empty
  by_cases hn0 : n = 0
  · subst hn0
    rw [pow_zero, hlm1_eq]
    simp only [Nat.cast_zero, zero_mul]
    rw [zero_pow (by omega : 4 * k + 3 ≠ 0)]
    have h41_pos : (0 : ℝ) < ((4 : ℝ) ^ (0 : ℕ)) ^ t := by
      rw [pow_zero, Real.one_rpow]; norm_num
    linarith
  push_neg at hn0
  have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hn_R_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  have hn_R_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnL_pos : (0 : ℝ) < (n : ℝ) * L := mul_pos hn_R_pos hL_pos
  have hnL_ge_one : (1 : ℝ) ≤ (n : ℝ) * L := by
    have h1 : 1 * 1 ≤ (n : ℝ) * L :=
      mul_le_mul hn_R_ge_one hL_ge_one (by norm_num) (by linarith)
    linarith
  have h4n_pos : (0 : ℝ) < (4 : ℝ) ^ n := pow_pos (by norm_num) n
  have h4n_t_pos : (0 : ℝ) < ((4 : ℝ) ^ n) ^ t := Real.rpow_pos_of_pos h4n_pos t
  have h4n_t_nn : (0 : ℝ) ≤ ((4 : ℝ) ^ n) ^ t := le_of_lt h4n_t_pos
  have h4n_ge_one : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have h4n_t_ge_one : (1 : ℝ) ≤ ((4 : ℝ) ^ n) ^ t := by
    rw [show (1 : ℝ) = (1 : ℝ) ^ t from (Real.one_rpow t).symm]
    exact Real.rpow_le_rpow (by norm_num) h4n_ge_one (le_of_lt ht_pos)
  have hnL_pow_pos : (0 : ℝ) < ((n : ℝ) * L) ^ (4 * k + 3) := pow_pos hnL_pos _
  have hnL_pow_ge_Lp : L ^ (4 * k + 3) ≤ ((n : ℝ) * L) ^ (4 * k + 3) := by
    have h_le : L ≤ (n : ℝ) * L := by
      have : 1 * L ≤ (n : ℝ) * L := mul_le_mul_of_nonneg_right hn_R_ge_one hL_nn
      linarith
    exact pow_le_pow_left₀ hL_nn h_le _
  -- (4^n)^t = 2^(n/(k+1)).
  have h4n_t_val : ((4 : ℝ) ^ n) ^ t = (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    rw [h4, ← pow_mul,
        show ((2 : ℝ) ^ (2 * n) : ℝ) = (2 : ℝ) ^ ((2 * n : ℕ) : ℝ) from
          (Real.rpow_natCast _ (2 * n)).symm,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [ht_def]; push_cast; field_simp
  by_cases hn_small : n ≤ k + 1
  · -- Small n: linear bound.
    have hbd_lin := hK_lin n
    have hn_R : (n : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hn_small
    have hn1_le : (n : ℝ) + 1 ≤ (k : ℝ) + 2 := by linarith
    have h2_pow_le : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (k + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn_small
    have hbd : lambdaM (4 ^ n) ≤
        K_lin * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1) := by
      calc lambdaM (4 ^ n)
          ≤ K_lin * ((n : ℝ) + 1) * (2 : ℝ) ^ n := hbd_lin
        _ ≤ K_lin * ((k : ℝ) + 2) * (2 : ℝ) ^ n := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left hn1_le (le_of_lt hK_lin_pos)
            · positivity
        _ ≤ K_lin * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1) := by
            apply mul_le_mul_of_nonneg_left h2_pow_le; positivity
    have hK_small : K_lin * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1) / L ^ (4 * k + 3) ≤ K_main := by
      rw [hK_main_def]
      have h1 : 0 < K_BT * K_IH := mul_pos hK_BT_pos hK_IH_pos
      have h2 : 0 < 16 * K_BT / L ^ (4 * k + 3) := by positivity
      linarith
    have hbd2 : K_lin * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1) =
        K_lin * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1) / L ^ (4 * k + 3) * L ^ (4 * k + 3) := by
      field_simp
    rw [hbd2] at hbd
    have step1 :
        K_lin * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1) / L ^ (4 * k + 3) * L ^ (4 * k + 3) ≤
        K_main * L ^ (4 * k + 3) :=
      mul_le_mul_of_nonneg_right hK_small (le_of_lt hLp_pos)
    have step2 : K_main * L ^ (4 * k + 3) ≤
        K_main * ((n : ℝ) * L) ^ (4 * k + 3) :=
      mul_le_mul_of_nonneg_left hnL_pow_ge_Lp (le_of_lt hK_main_pos)
    have step3 : K_main * ((n : ℝ) * L) ^ (4 * k + 3) ≤
        K_main * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t := by
      have h_one_mul : K_main * ((n : ℝ) * L) ^ (4 * k + 3) * 1 ≤
          K_main * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t := by
        apply mul_le_mul_of_nonneg_left h4n_t_ge_one
        exact mul_nonneg (le_of_lt hK_main_pos) (le_of_lt hnL_pow_pos)
      linarith
    linarith
  · -- Large n: use BT recursion with l = (n+k)/(k+1) = ⌈n/(k+1)⌉.
    push_neg at hn_small
    have hn_ge : k + 2 ≤ n := hn_small
    set l : ℕ := (n + k) / (k + 1) with hl_def
    have hk1_pos_nat : 0 < k + 1 := by omega
    have hl_ge2 : 2 ≤ l := by
      rw [hl_def]
      have h_ge : 2 * (k + 1) ≤ n + k := by omega
      exact (Nat.le_div_iff_mul_le hk1_pos_nat).mpr (by linarith)
    have hl_le_n : l ≤ n := by
      rw [hl_def]
      apply Nat.div_le_of_le_mul
      have h_nk : k ≤ n * k :=
        Nat.le_mul_of_pos_left _ (by omega)
      nlinarith
    have hl_pos : 1 ≤ l := by omega
    have hl_R_ge_one : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl_pos
    have hl_R_pos : (0 : ℝ) < (l : ℝ) := by linarith
    -- l ≥ n/(k+1)
    have hl_R_ge_div : (n : ℝ) / ((k : ℝ) + 1) ≤ (l : ℝ) := by
      rw [div_le_iff₀ hk1_R_pos]
      have h_nat_ineq : n ≤ l * (k + 1) := by
        have hdvm := Nat.div_add_mod (n + k) (k + 1)
        have hmod_lt : (n + k) % (k + 1) < k + 1 := Nat.mod_lt _ hk1_pos_nat
        show n ≤ (n + k) / (k + 1) * (k + 1)
        have heq : (n + k) / (k + 1) * (k + 1) = (k + 1) * ((n + k) / (k + 1)) := Nat.mul_comm _ _
        rw [heq]; omega
      have h_cast : ((l * (k + 1) : ℕ) : ℝ) = (l : ℝ) * ((k : ℝ) + 1) := by push_cast; ring
      have : ((n : ℕ) : ℝ) ≤ ((l * (k + 1) : ℕ) : ℝ) := by exact_mod_cast h_nat_ineq
      rw [h_cast] at this
      exact_mod_cast this
    -- l ≤ n/(k+1) + 1
    have hl_R_le_div : (l : ℝ) ≤ (n : ℝ) / ((k : ℝ) + 1) + 1 := by
      rw [hl_def]
      push_cast
      have h_le_nat : (((n + k) / (k + 1) : ℕ)) * (k + 1) ≤ n + k := Nat.div_mul_le_self _ _
      have h_cast : (((n + k) / (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ≤ ((n : ℝ) + (k : ℝ)) := by
        have h_eq : (((n + k) / (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
            ((((n + k) / (k + 1)) * (k + 1) : ℕ) : ℝ) := by push_cast; ring
        rw [h_eq]
        have : ((((n + k) / (k + 1)) * (k + 1) : ℕ) : ℝ) ≤ ((n + k : ℕ) : ℝ) := by
          exact_mod_cast h_le_nat
        have h_simp : ((n + k : ℕ) : ℝ) = (n : ℝ) + (k : ℝ) := by push_cast; ring
        rw [h_simp] at this; exact this
      have h_div_le : (((n + k) / (k + 1) : ℕ) : ℝ) ≤ ((n : ℝ) + (k : ℝ)) / ((k : ℝ) + 1) := by
        rw [le_div_iff₀ hk1_R_pos]; exact h_cast
      have h_split : ((n : ℝ) + (k : ℝ)) / ((k : ℝ) + 1) =
          (n : ℝ) / ((k : ℝ) + 1) + (k : ℝ) / ((k : ℝ) + 1) := by field_simp
      have h_k_frac : (k : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hk1_R_pos]; linarith
      linarith [h_div_le, h_split.le, h_split.ge]
    -- BT recursion at l.
    have hBT_n := hBT n l hl_ge2 hl_le_n
    -- IH at (n - l).
    have hIH_nl := hIH (n - l)
    have hnl_R_eq : ((n - l : ℕ) : ℝ) = (n : ℝ) - (l : ℝ) := by
      have hle : l ≤ n := hl_le_n
      have hcast : ((n - l : ℕ) : ℝ) = (n : ℝ) - (l : ℝ) :=
        Nat.cast_sub hle
      exact hcast
    have h_log_nl : Real.log ((4 : ℝ) ^ (n - l)) = ((n - l : ℕ) : ℝ) * L := by
      rw [hL_def, Real.log_pow]
    have h_k_R_eq : ((k : ℕ) : ℝ) = (k : ℝ) := by push_cast; rfl
    rw [h_log_nl, h_k_R_eq] at hIH_nl
    -- (4^(n-l))^(1/(2k)) = 2^((n-l)/k).
    have h4nl_pow : ((4 : ℝ) ^ (n - l)) ^ ((1 : ℝ) / (2 * (k : ℝ))) =
        (2 : ℝ) ^ (((n - l : ℕ) : ℝ) / (k : ℝ)) := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [h4, ← pow_mul,
          show ((2 : ℝ) ^ (2 * (n - l)) : ℝ) = (2 : ℝ) ^ ((2 * (n - l) : ℕ) : ℝ) from
            (Real.rpow_natCast _ (2 * (n - l))).symm,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast; field_simp
    rw [h4nl_pow] at hIH_nl
    -- Bounds.
    have hnl_R_nn : (0 : ℝ) ≤ ((n - l : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnl_R_le_n : ((n - l : ℕ) : ℝ) ≤ (n : ℝ) := by rw [hnl_R_eq]; linarith
    have hnlL_nn : (0 : ℝ) ≤ ((n - l : ℕ) : ℝ) * L := mul_nonneg hnl_R_nn hL_nn
    have h_pow_4km1_le : (((n - l : ℕ) : ℝ) * L) ^ (4 * k - 1) ≤
        ((n : ℝ) * L) ^ (4 * k - 1) :=
      pow_le_pow_left₀ hnlL_nn (mul_le_mul_of_nonneg_right hnl_R_le_n hL_nn) _
    have h_pow_grow : ((n : ℝ) * L) ^ (4 * k - 1) ≤ ((n : ℝ) * L) ^ (4 * k + 3) :=
      pow_le_pow_right₀ hnL_ge_one (by omega : 4 * k - 1 ≤ 4 * k + 3)
    have h_pow_le_full : (((n - l : ℕ) : ℝ) * L) ^ (4 * k - 1) ≤
        ((n : ℝ) * L) ^ (4 * k + 3) := le_trans h_pow_4km1_le h_pow_grow
    -- 2^((n-l)/k) ≤ 2^(n/(k+1))
    have h_exp_ineq : ((n - l : ℕ) : ℝ) / (k : ℝ) ≤ (n : ℝ) / ((k : ℝ) + 1) := by
      rw [hnl_R_eq, div_le_div_iff₀ hk_R_pos hk1_R_pos]
      have h_n_le : (n : ℝ) ≤ (l : ℝ) * ((k : ℝ) + 1) := by
        rw [← div_le_iff₀ hk1_R_pos]; exact hl_R_ge_div
      nlinarith [h_n_le, hk_R_pos, hk1_R_pos]
    have h_2pow_le : (2 : ℝ) ^ (((n - l : ℕ) : ℝ) / (k : ℝ)) ≤
        (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp_ineq
    -- IH bound at (n-l) lifted to target form.
    have hIH_nl_full : lambdaM (4 ^ (n - l)) ≤
        K_IH * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t := by
      rw [h4n_t_val]
      have h_2pow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (((n - l : ℕ) : ℝ) / (k : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      have step1 : K_IH * (((n - l : ℕ) : ℝ) * L) ^ (4 * k - 1) *
          (2 : ℝ) ^ (((n - l : ℕ) : ℝ) / (k : ℝ)) ≤
          K_IH * ((n : ℝ) * L) ^ (4 * k + 3) *
          (2 : ℝ) ^ (((n - l : ℕ) : ℝ) / (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ h_2pow_nn
        exact mul_le_mul_of_nonneg_left h_pow_le_full (le_of_lt hK_IH_pos)
      have step2 : K_IH * ((n : ℝ) * L) ^ (4 * k + 3) *
          (2 : ℝ) ^ (((n - l : ℕ) : ℝ) / (k : ℝ)) ≤
          K_IH * ((n : ℝ) * L) ^ (4 * k + 3) *
          (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left h_2pow_le
        exact mul_nonneg (le_of_lt hK_IH_pos) (le_of_lt hnL_pow_pos)
      linarith
    -- BT recursion gives: lambdaM(4^n) ≤ K_BT · lambdaM(4^(n-l)) + K_BT · l^3 · 2^l.
    have hBT_combined : lambdaM (4 ^ n) ≤
        K_BT * K_IH * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t +
        K_BT * (l : ℝ) ^ 3 * (2 : ℝ) ^ l := by
      have h1 : K_BT * lambdaM (4 ^ (n - l)) ≤
          K_BT * (K_IH * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t) :=
        mul_le_mul_of_nonneg_left hIH_nl_full (le_of_lt hK_BT_pos)
      linarith [hBT_n]
    -- Bound the error K_BT · l^3 · 2^l.
    have h_l_le_n1 : (l : ℝ) ≤ (n : ℝ) + 1 := by
      have h1 : (n : ℝ) / ((k : ℝ) + 1) ≤ (n : ℝ) := by
        rw [div_le_iff₀ hk1_R_pos]; nlinarith
      linarith
    have h_l3_le : (l : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 :=
      pow_le_pow_left₀ (by linarith) h_l_le_n1 _
    have h_2l_eq : (2 : ℝ) ^ l = (2 : ℝ) ^ ((l : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    have h_2pow_l_le : (2 : ℝ) ^ l ≤ 2 * (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) := by
      rw [h_2l_eq, show ((l : ℕ) : ℝ) = (l : ℝ) from by push_cast; rfl]
      have h_pow : (2 : ℝ) ^ (l : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hl_R_le_div
      have h_split : (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1) + 1) =
          (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) * 2 := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      rw [h_split] at h_pow; linarith
    have hK_BT_nn : 0 ≤ K_BT := le_of_lt hK_BT_pos
    have h_err_bound : K_BT * (l : ℝ) ^ 3 * (2 : ℝ) ^ l ≤
        K_BT * ((n : ℝ) + 1) ^ 3 * 2 * (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) := by
      have hl3_nn : 0 ≤ (l : ℝ) ^ 3 := by positivity
      have h2l_nn : 0 ≤ (2 : ℝ) ^ l := pow_nonneg (by norm_num) _
      have h2pow_nn : 0 ≤ (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) :=
        Real.rpow_nonneg (by norm_num) _
      calc K_BT * (l : ℝ) ^ 3 * (2 : ℝ) ^ l
          ≤ K_BT * ((n : ℝ) + 1) ^ 3 * (2 : ℝ) ^ l := by
            apply mul_le_mul_of_nonneg_right _ h2l_nn
            exact mul_le_mul_of_nonneg_left h_l3_le hK_BT_nn
        _ ≤ K_BT * ((n : ℝ) + 1) ^ 3 * (2 * (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1))) := by
            apply mul_le_mul_of_nonneg_left h_2pow_l_le; positivity
        _ = K_BT * ((n : ℝ) + 1) ^ 3 * 2 * (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) := by ring
    -- (n+1)^3 ≤ 8 n^3
    have h_n13_le : ((n : ℝ) + 1) ^ 3 ≤ 8 * (n : ℝ) ^ 3 := by
      have h1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
      have h2 : ((n : ℝ) + 1) ^ 3 ≤ (2 * (n : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by linarith) h1 _
      nlinarith
    -- n^3 ≤ n^(4k+3)
    have h_n3_le : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ (4 * k + 3) :=
      pow_le_pow_right₀ hn_R_ge_one (by omega)
    have h_nL_pow_expand : ((n : ℝ) * L) ^ (4 * k + 3) =
        (n : ℝ) ^ (4 * k + 3) * L ^ (4 * k + 3) := mul_pow _ _ _
    -- Bound 16 K_BT · n^3 · 2^(n/(k+1)) ≤ 16 K_BT / L^(4k+3) · (nL)^(4k+3) · 2^(n/(k+1)).
    have h_err_bound2 : K_BT * ((n : ℝ) + 1) ^ 3 * 2 *
        (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) ≤
        16 * K_BT / L ^ (4 * k + 3) * ((n : ℝ) * L) ^ (4 * k + 3) *
        (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) := by
      have h2pow_nn : 0 ≤ (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) :=
        Real.rpow_nonneg (by norm_num) _
      have hLp_ne : L ^ (4 * k + 3) ≠ 0 := ne_of_gt hLp_pos
      have h_coef_le : K_BT * ((n : ℝ) + 1) ^ 3 * 2 ≤
          16 * K_BT / L ^ (4 * k + 3) * ((n : ℝ) * L) ^ (4 * k + 3) := by
        have step_a : K_BT * ((n : ℝ) + 1) ^ 3 * 2 ≤
            K_BT * (8 * (n : ℝ) ^ 3) * 2 := by
          have : K_BT * ((n : ℝ) + 1) ^ 3 ≤ K_BT * (8 * (n : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_left h_n13_le hK_BT_nn
          linarith
        have step_b : K_BT * (8 * (n : ℝ) ^ 3) * 2 ≤
            K_BT * (8 * (n : ℝ) ^ (4 * k + 3)) * 2 := by
          have h_pow_le : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ (4 * k + 3) := h_n3_le
          have : K_BT * (8 * (n : ℝ) ^ 3) ≤ K_BT * (8 * (n : ℝ) ^ (4 * k + 3)) := by
            have : 8 * (n : ℝ) ^ 3 ≤ 8 * (n : ℝ) ^ (4 * k + 3) := by linarith
            exact mul_le_mul_of_nonneg_left this hK_BT_nn
          linarith
        have step_c : K_BT * (8 * (n : ℝ) ^ (4 * k + 3)) * 2 =
            16 * K_BT / L ^ (4 * k + 3) * ((n : ℝ) * L) ^ (4 * k + 3) := by
          rw [h_nL_pow_expand]; field_simp; ring
        linarith
      exact mul_le_mul_of_nonneg_right h_coef_le h2pow_nn
    have h_err_final : K_BT * (l : ℝ) ^ 3 * (2 : ℝ) ^ l ≤
        16 * K_BT / L ^ (4 * k + 3) * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t := by
      rw [h4n_t_val]; linarith
    -- Combine.
    have h_sum_le_K : K_BT * K_IH + 16 * K_BT / L ^ (4 * k + 3) ≤ K_main := by
      rw [hK_main_def]
      have h1 : 0 < K_lin * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1) / L ^ (4 * k + 3) := by positivity
      linarith
    have h_prod_nn : 0 ≤ ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t :=
      mul_nonneg (le_of_lt hnL_pow_pos) h4n_t_nn
    have h_combined :
        K_BT * K_IH * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t +
        16 * K_BT / L ^ (4 * k + 3) * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t ≤
        K_main * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t := by
      have h_eq : K_BT * K_IH * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t +
          16 * K_BT / L ^ (4 * k + 3) * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t =
          (K_BT * K_IH + 16 * K_BT / L ^ (4 * k + 3)) *
          (((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t) := by ring
      rw [h_eq, show K_main * ((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t =
          K_main * (((n : ℝ) * L) ^ (4 * k + 3) * ((4 : ℝ) ^ n) ^ t) from by ring]
      exact mul_le_mul_of_nonneg_right h_sum_le_K h_prod_nn
    linarith

/-- **Paper Eq. [4] (JOS 2013, PNAS p. 19254): the log-form pow4 bound.**

For every positive integer `k` there exists a constant `K_k > 0` such that
for all `n : ℕ`,

  `lambdaM (4 ^ n) ≤ K_k · (log (4 ^ n)) ^ (4·k − 1) · (4 ^ n) ^ (1 / (2·k))`.

Proof: outer induction on `k` via `Nat.le_induction`, dispatching to the two
helpers `lambdaM_pow4_paper_base` (k = 1) and `lambdaM_pow4_paper_step`
(k → k+1).  Each helper formalises one layer of the paper's iterated paving
+ Claim 1 argument. -/
private theorem lambdaM_pow4_paper_bound :
    ∀ k : ℕ, 1 ≤ k →
    ∃ K : ℝ, 0 < K ∧
    ∀ n : ℕ, lambdaM (4 ^ n) ≤
      K * (Real.log ((4 : ℝ) ^ n)) ^ (4 * k - 1) *
        ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k : ℝ))) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact lambdaM_pow4_paper_base
  | succ k hk IH => exact lambdaM_pow4_paper_step k hk IH
-/

/-- Polynomial-vs-geometric growth: for any `p : ℕ` and `r > 1`, there is a
constant `C > 0` with `(n + 1)^p ≤ C · r^n` for all `n : ℕ`.

This is **Step 3** of `reference/pow4_bound.pdf`: "the growth rate of any polynomial
is strictly slower than that of an exponential function with a base greater than 1".
With the substitution `r := 4^δ > 1` and `p := 4·k − 1` (or here `p`, slightly more
general), this gives `(n log 4)^p ≤ (log 4)^p · (n+1)^p ≤ (log 4)^p · C · r^n`. -/
private lemma poly_le_const_mul_geom (p : ℕ) {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ((n : ℝ) + 1) ^ p ≤ C * r ^ n := by
  have hr_pos : 0 < r := by linarith
  have h1 : (fun n : ℕ => ((n : ℝ) + 1) ^ p) =O[Filter.atTop]
            (fun n : ℕ => (n : ℝ) ^ p) := by
    refine Asymptotics.IsBigO.of_bound (2 ^ p) ?_
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn_nn : (0 : ℝ) ≤ n := by linarith
    have hnp_nn : (0 : ℝ) ≤ (n : ℝ) ^ p := pow_nonneg hn_nn p
    have hnp1_nn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ p := pow_nonneg (by linarith) p
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hnp1_nn, abs_of_nonneg hnp_nn]
    calc ((n : ℝ) + 1) ^ p
        ≤ (2 * (n : ℝ)) ^ p :=
          pow_le_pow_left₀ (by linarith) (by linarith) p
      _ = 2 ^ p * (n : ℝ) ^ p := by rw [mul_pow]
  have h2 : (fun n : ℕ => (n : ℝ) ^ p) =o[Filter.atTop]
            (fun n : ℕ => r ^ n) :=
    isLittleO_pow_const_const_pow_of_one_lt p hr
  have hLO := h1.trans_isLittleO h2
  have hev := hLO.def (c := 1) one_pos
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hrn_pos : ∀ n : ℕ, 0 < r ^ n := fun n => pow_pos hr_pos n
  by_cases hN0 : N = 0
  · subst hN0
    refine ⟨1, one_pos, fun n => ?_⟩
    have := hN n (Nat.zero_le _)
    have hnp1_nn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ p :=
      pow_nonneg (by positivity) p
    have hrn_nn : (0 : ℝ) ≤ r ^ n := le_of_lt (hrn_pos n)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hnp1_nn, abs_of_nonneg hrn_nn, one_mul] at this
    linarith
  have hrange_ne : (Finset.range N).Nonempty :=
    Finset.nonempty_range_iff.mpr hN0
  set Mfin : ℝ :=
    (Finset.range N).sup' hrange_ne
      (fun i => ((i : ℝ) + 1) ^ p / r ^ i) with hMfin_def
  refine ⟨max Mfin 1 + 1, by positivity, fun n => ?_⟩
  have hnp1_nn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ p :=
    pow_nonneg (by positivity) p
  have hrn_nn : (0 : ℝ) ≤ r ^ n := le_of_lt (hrn_pos n)
  by_cases hn : n < N
  · have h_sup :
        ((n : ℝ) + 1) ^ p / r ^ n ≤ Mfin := by
      change ((n : ℝ) + 1) ^ p / r ^ n ≤
        (Finset.range N).sup' hrange_ne
          (fun i => ((i : ℝ) + 1) ^ p / r ^ i)
      rw [Finset.le_sup'_iff]
      exact ⟨n, Finset.mem_range.mpr hn, le_refl _⟩
    have h_div : ((n : ℝ) + 1) ^ p ≤ Mfin * r ^ n :=
      (div_le_iff₀ (hrn_pos n)).mp h_sup
    have hMle : Mfin ≤ max Mfin 1 + 1 := by linarith [le_max_left Mfin 1]
    calc ((n : ℝ) + 1) ^ p
        ≤ Mfin * r ^ n := h_div
      _ ≤ (max Mfin 1 + 1) * r ^ n :=
          mul_le_mul_of_nonneg_right hMle hrn_nn
  · push Not at hn
    have h_bd := hN n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hnp1_nn, abs_of_nonneg hrn_nn, one_mul] at h_bd
    have h_one_le : (1 : ℝ) ≤ max Mfin 1 + 1 := by
      linarith [le_max_right Mfin 1]
    calc ((n : ℝ) + 1) ^ p
        ≤ r ^ n := h_bd
      _ = 1 * r ^ n := (one_mul _).symm
      _ ≤ (max Mfin 1 + 1) * r ^ n :=
          mul_le_mul_of_nonneg_right h_one_le hrn_nn

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- For every `ε ∈ (0,1)` there is a constant `K > 0` such that
`lambdaM (4^n) ≤ K · (4^n)^ε` for all `n`.

Historical proof outline (following `reference/pow4_bound.pdf`; the current
proof below uses `lambdaM_pow4_geometric_bound`):
1. *Core iterative bound* (the iterated paving result):
   for every `k ≥ 1`, `lambdaM (4^n) ≤ C_k · (n+1)^(4k) · (4^n)^(1/(2k))`.
2. *Choose `k`*:  pick `k₀ = ⌈1/(2ε)⌉ + 1`, so that `1/(2·k₀) < ε`; set
   `δ := ε − 1/(2·k₀) > 0`.
3. *Polynomial-vs-exponential*:  since `r := 4^δ > 1`, the polynomial
   `(n+1)^(4k₀)` is dominated by `r^n = (4^n)^δ` up to a constant
   (`poly_le_const_mul_geom`).
4. *Combine*:  with `δ + 1/(2·k₀) = ε`, the two exponential factors
   `(4^n)^δ` and `(4^n)^(1/(2·k₀))` combine to `(4^n)^ε`. -/
private lemma lambdaM_pow4_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (K : ℝ), 0 < K ∧ ∀ (n : ℕ), lambdaM (4 ^ n) ≤ K * ((4 : ℝ) ^ n) ^ ε := by
  set r : ℝ := (4 : ℝ) ^ ε with hr_def
  have hr_gt_one : 1 < r := by
    rw [hr_def, show (1 : ℝ) = (4 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero _).symm]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hε
  obtain ⟨K, hK_pos, hK_bound⟩ := lambdaM_pow4_geometric_bound r hr_gt_one
  refine ⟨K, hK_pos, fun n => ?_⟩
  have hrn_eq : r ^ n = ((4 : ℝ) ^ n) ^ ε := by
    rw [hr_def,
      show ((4 : ℝ) ^ ε) ^ n = ((4 : ℝ) ^ ε) ^ (n : ℝ) from
        (Real.rpow_natCast _ n).symm,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
      show ((4 : ℝ) ^ n) ^ ε = ((4 : ℝ) ^ (n : ℝ)) ^ ε by
        rw [Real.rpow_natCast],
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  simpa [hrn_eq] using hK_bound n
/- The superseded log-power route follows for audit history.
  -- Step 2: pick k₀ ≥ 1 with 1/(2·k₀) < ε.
  set k₀ := ⌈(1 : ℝ) / (2 * ε)⌉₊ + 1 with hk₀_def
  have hk₀_pos : 1 ≤ k₀ := Nat.le_add_left 1 _
  have hk₀_real : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀_pos
  have h2k₀_pos : (0 : ℝ) < 2 * (k₀ : ℝ) := by linarith
  have h2ε_pos : (0 : ℝ) < 2 * ε := by linarith
  have hk_lt : 1 / (2 * (k₀ : ℝ)) < ε := by
    have h_ceil : (1 : ℝ) / (2 * ε) ≤ (⌈(1 : ℝ) / (2 * ε)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hk₀_cast :
        ((k₀ : ℝ)) = (⌈(1 : ℝ) / (2 * ε)⌉₊ : ℝ) + 1 := by
      simp only [hk₀_def, Nat.cast_add, Nat.cast_one]
    have h1 : (1 : ℝ) / (2 * ε) < (k₀ : ℝ) := by rw [hk₀_cast]; linarith
    rw [div_lt_iff₀ h2ε_pos] at h1
    rw [div_lt_iff₀ h2k₀_pos]
    linarith
  -- Step 1 of `reference/pow4_bound.pdf` = `h_core` (proved here from
  -- `lambdaM_pow4_paper_bound`, following `reference/h_core.pdf` steps 2–4).
  have h_core :
      ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, lambdaM (4 ^ n) ≤
        C * ((n : ℝ) + 1) ^ (4 * k₀) *
          ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ))) := by
    -- h_core.pdf Step 1: the paper's bound (axiomatized).
    obtain ⟨K, hK_pos, hK_bd⟩ := lambdaM_pow4_paper_bound k₀ hk₀_pos
    -- Let `L := log 4 > 0` and `p := 4·k₀ − 1`.
    set L : ℝ := Real.log 4 with hL_def
    have hL_pos : 0 < L := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    have hL_nn : 0 ≤ L := le_of_lt hL_pos
    set p : ℕ := 4 * k₀ - 1 with hp_def
    have h_4k₀ : 4 * k₀ = p + 1 := by simp [hp_def]; omega
    -- h_core.pdf Step 4: target constant `C := K · L^p`.
    set C : ℝ := K * L ^ p with hC_def
    have hLp_pos : 0 < L ^ p := pow_pos hL_pos p
    have hC_pos : 0 < C := mul_pos hK_pos hLp_pos
    refine ⟨C, hC_pos, fun n => ?_⟩
    have hK_n := hK_bd n
    -- h_core.pdf Step 2: `log (4^n) = n · log 4`, so
    -- `(log (4^n))^p = (n · L)^p = n^p · L^p`.
    have h_log : Real.log ((4 : ℝ) ^ n) = (n : ℝ) * L := by
      rw [Real.log_pow]
    rw [h_log] at hK_n
    have h_factor : ((n : ℝ) * L) ^ p = (n : ℝ) ^ p * L ^ p := mul_pow _ _ p
    -- h_core.pdf Step 3: `n^p ≤ (n+1)^(p+1) = (n+1)^(4·k₀)`.
    have h_step3 : (n : ℝ) ^ p ≤ ((n : ℝ) + 1) ^ (4 * k₀) := by
      have h_step_a : (n : ℝ) ^ p ≤ ((n : ℝ) + 1) ^ p :=
        pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) p
      have h_step_b : ((n : ℝ) + 1) ^ p ≤ ((n : ℝ) + 1) ^ (4 * k₀) :=
        pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)
          (by simp [h_4k₀])
      linarith
    -- h_core.pdf Step 4: assemble.
    have hexp_nn :
        (0 : ℝ) ≤ ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ))) :=
      Real.rpow_nonneg (by positivity) _
    have hC_nn : 0 ≤ C := le_of_lt hC_pos
    calc lambdaM (4 ^ n)
        ≤ K * ((n : ℝ) * L) ^ p *
            ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ))) := hK_n
      _ = K * ((n : ℝ) ^ p * L ^ p) *
            ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ))) := by rw [h_factor]
      _ = C * (n : ℝ) ^ p *
            ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ))) := by
          simp only [hC_def]; ring
      _ ≤ C * ((n : ℝ) + 1) ^ (4 * k₀) *
            ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ))) := by gcongr
  obtain ⟨Ck, hCk_pos, hCk_bound⟩ := h_core
  -- δ := ε - 1/(2·k₀) > 0.
  set δ := ε - 1 / (2 * (k₀ : ℝ)) with hδ_def
  have hδ_pos : 0 < δ := by simp only [hδ_def]; linarith
  -- r := 4^δ > 1.
  set r : ℝ := (4 : ℝ) ^ δ with hr_def
  have hr_gt_one : 1 < r := by
    rw [hr_def,
      show (1 : ℝ) = (4 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero _).symm]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hδ_pos
  -- Step 3: polynomial-vs-geometric bound.
  obtain ⟨C', hC'_pos, hC'_bound⟩ :=
    poly_le_const_mul_geom (4 * k₀) hr_gt_one
  -- Step 4: combine the bounds.
  refine ⟨Ck * C', mul_pos hCk_pos hC'_pos, fun n => ?_⟩
  have h4_pos : (0 : ℝ) < 4 := by norm_num
  have h4_nn : (0 : ℝ) ≤ 4 := by linarith
  have h4n_pos : (0 : ℝ) < (4 : ℝ) ^ n := pow_pos h4_pos n
  have h4n_nn : (0 : ℝ) ≤ (4 : ℝ) ^ n := le_of_lt h4n_pos
  -- (4^δ)^n = (4^n)^δ — rpow vs npow gymnastics.
  have hrn_eq : r ^ n = ((4 : ℝ) ^ n) ^ δ := by
    rw [hr_def,
      show ((4 : ℝ) ^ δ) ^ n = ((4 : ℝ) ^ δ) ^ ((n : ℝ)) from
        (Real.rpow_natCast _ n).symm,
      ← Real.rpow_mul h4_nn,
      show ((4 : ℝ) ^ n) ^ δ = ((4 : ℝ) ^ (n : ℝ)) ^ δ by
        rw [Real.rpow_natCast],
      ← Real.rpow_mul h4_nn]
    congr 1; ring
  -- (4^n)^δ · (4^n)^(1/(2·k₀)) = (4^n)^ε.
  have h_exp_sum : δ + (1 : ℝ) / (2 * (k₀ : ℝ)) = ε := by
    simp only [hδ_def]; ring
  have h_exp :
      ((4 : ℝ) ^ n) ^ δ * ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ)))
        = ((4 : ℝ) ^ n) ^ ε := by
    rw [← Real.rpow_add h4n_pos, h_exp_sum]
  have hexpfrac_nn :
      (0 : ℝ) ≤ ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ))) :=
    Real.rpow_nonneg h4n_nn _
  calc lambdaM (4 ^ n)
      ≤ Ck * ((n : ℝ) + 1) ^ (4 * k₀) *
          ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ))) := hCk_bound n
    _ ≤ Ck * (C' * r ^ n) *
          ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ))) := by
        have h := hC'_bound n
        gcongr
    _ = Ck * C' *
          (r ^ n * ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ)))) := by ring
    _ = Ck * C' *
          (((4 : ℝ) ^ n) ^ δ *
             ((4 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * (k₀ : ℝ)))) := by rw [hrn_eq]
    _ = Ck * C' * ((4 : ℝ) ^ n) ^ ε := by rw [h_exp]
-/

/-- The paper's Theorem 3 (JOS 2013): lambdaM(m) ≤ K_ε * m^ε.
    Proved from lambdaM_mono, lambdaM_pow4_bound, and exists_pow4_sandwich. -/
private lemma lambdaM_poly_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (Kε : ℝ), 0 < Kε ∧ ∀ (m : ℕ), lambdaM m ≤ Kε * (m : ℝ) ^ ε := by
  obtain ⟨K, hK_pos, hK_bound⟩ := lambdaM_pow4_bound ε hε hε1
  refine ⟨K * (4 : ℝ) ^ ε, by positivity, fun m => ?_⟩
  by_cases hm0 : m = 0
  · subst hm0
    have hempty : {A : Matrix (Fin 0) (Fin 0) ℂ | ZeroDiag A ∧ ‖A‖ = 1} = ∅ := by
      ext A
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, hA⟩
      exact absurd hA (by rw [show A = 0 from Subsingleton.elim _ _, norm_zero]; norm_num)
    simp [lambdaM, hempty, Set.image_empty, Real.zero_rpow (ne_of_gt hε)]
  · have hm_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    obtain ⟨n, hmn, h4n⟩ := exists_pow4_sandwich m hm_pos
    calc lambdaM m
        ≤ lambdaM (4 ^ n) := lambdaM_mono hmn
      _ ≤ K * ((4 : ℝ) ^ n) ^ ε := hK_bound n
      _ ≤ K * ((4 : ℝ) * (m : ℝ)) ^ ε := by gcongr
      _ = K * ((4 : ℝ) ^ ε * (m : ℝ) ^ ε) := by
          rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (Nat.cast_nonneg m)]
      _ = K * (4 : ℝ) ^ ε * (m : ℝ) ^ ε := by ring

/-- The decomposition set for lambdaA is always nonempty: B = 0 (diagonal, InUnitSquare)
    and C = 0 gives A = [0, 0] = 0, so ‖A‖ is in the set when A = 0.
    For general A, we use B = 0, C = 0 and ‖C‖ = 0 ≤ ‖A‖. -/
private lemma lambdaA_set_nonempty {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (_hzd : ZeroDiag A) (hA : A = 0) :
    ∃ c : ℝ, ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c := by
  refine ⟨0, 0, 0, ?_, ?_, ?_, ?_⟩
  · intro i j _; simp
  · intro i; simp [InUnitSquare]
  · simp [hA, matComm]
  · simp

/- Historical development log (statuses below refer only to that earlier draft).
State: ✅ done
Priority: 1
Attempts: 1 / 20
-/
-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedVariables false in
/-- Extract witnesses from a lambdaA bound: if lambdaA A ≤ M and A is zero-diagonal,
    then for any δ > 0, there exist diagonal B (InUnitSquare) and C with
    A = [B, C] and ‖C‖ ≤ M + δ. -/
private lemma lambdaA_extract_witness {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hzd : ZeroDiag A) (M : ℝ) (hM : lambdaA A ≤ M)
    (δ : ℝ) (hδ : 0 < δ)
    (hne : ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ) :
    ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧
      A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ M + δ := by
  set S := {c : ℝ | ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
    IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ ∧ ‖C‖ ≤ c} with hS_def
  have hne_S : S.Nonempty := by
    obtain ⟨B, C, hdiag, husq, hcomm⟩ := hne
    exact ⟨‖C‖, B, C, hdiag, husq, hcomm, le_refl _⟩
  have hbdd : BddBelow S := by
    refine ⟨0, fun c ⟨B, C, _, _, _, hle⟩ => ?_⟩
    exact le_trans (norm_nonneg _) hle
  have hlt : sInf S < M + δ := lt_of_le_of_lt hM (by linarith)
  obtain ⟨c, ⟨B, C, hdiag, husq, hcomm, hnorm⟩, hc_lt⟩ := exists_lt_of_csInf_lt hne_S hlt
  exact ⟨B, C, hdiag, husq, hcomm, le_trans hnorm (le_of_lt hc_lt)⟩

/-- For a diagonal matrix B with InUnitSquare entries, ‖B‖ ≤ √2.
    Each entry z has |z.re| ≤ 1 and |z.im| ≤ 1, so ‖z‖ = √(re² + im²) ≤ √2. -/
private lemma InUnitSquare_diag_norm_le {m : ℕ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hdiag : IsDiagMatrix B) (husq : ∀ i, InUnitSquare (B i i)) :
    ‖B‖ ≤ Real.sqrt 2 := by
  apply diag_norm_le hdiag (Real.sqrt 2) (by positivity)
  intro i
  have ⟨hre, him⟩ := husq i
  -- ‖B i i‖ ≤ √2 since |re| ≤ 1 and |im| ≤ 1
  have hre2 : (B i i).re * (B i i).re ≤ 1 := by
    have h3 : |(B i i).re| * |(B i i).re| ≤ 1 := by nlinarith [abs_nonneg (B i i).re]
    rwa [abs_mul_abs_self] at h3
  have him2 : (B i i).im * (B i i).im ≤ 1 := by
    have h3 : |(B i i).im| * |(B i i).im| ≤ 1 := by nlinarith [abs_nonneg (B i i).im]
    rwa [abs_mul_abs_self] at h3
  have h1 : Complex.normSq (B i i) ≤ 2 := by
    simp [Complex.normSq_apply]; linarith
  rw [Complex.norm_def]; exact Real.sqrt_le_sqrt h1

/- Historical development log (statuses below refer only to that earlier draft).
State: ✅ done (modulo upstream sorries: lambdaM_poly_bound, decomp norm bound)
Priority: 1
Attempts: 5 / 35
-/
/-- The lambdaA-based proof: every unit-norm zero-diagonal matrix is a commutator
    with ‖B‖ * ‖C‖ ≤ K * n^ε, using lambdaM_poly_bound. -/
private lemma zeroDiag_commutator_unit_norm_lambda (ε : ℝ) (hε : 0 < ε) :
    ∃ (Kε : ℝ), 0 < Kε ∧
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
      ZeroDiag A → ‖A‖ = 1 →
      ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
        IsDiagMatrix B ∧ A = ⁅B, C⁆ₘ ∧
          ‖B‖ * ‖C‖ ≤ Kε * (n : ℝ) ^ ε := by
  -- Choose ε' = min(ε, 1/2) < 1
  set ε' := min ε (1/2) with hε'_def
  have hε'_pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'_lt1 : ε' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  obtain ⟨Klam, hKlam_pos, hbound⟩ := lambdaM_poly_bound ε' hε'_pos hε'_lt1
  -- K = √2 * (Klam + 1): accounts for ‖B‖ ≤ √2 and lambdaA ≤ lambdaM + δ
  set K := Real.sqrt 2 * (Klam + 1) with hK_def
  have hK_pos : 0 < K := by positivity
  refine ⟨K, hK_pos, fun n A hzd hnorm => ?_⟩
  -- n = 0: empty matrix, ‖A‖ = 1 impossible
  by_cases hn0 : n = 0
  · subst hn0; exact absurd hnorm (by simp [Subsingleton.elim A 0])
  -- n = 1: ZeroDiag means A = 0, contradicts ‖A‖ = 1
  by_cases hn1 : n = 1
  · subst hn1
    have hA0 : A = 0 := by ext i j; rw [Fin.eq_zero i, Fin.eq_zero j]; exact hzd 0
    rw [hA0] at hnorm; simp at hnorm
  -- n ≥ 2
  have hn2 : 2 ≤ n := by omega
  -- Get decomposition with bounded C
  obtain ⟨B₀, C₀, hdiag₀, husq₀, hcomm₀, _⟩ :=
    zeroDiag_InUnitSquare_decomp_bounded hn2 A hzd
  have hne : ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
      IsDiagMatrix B ∧ (∀ i, InUnitSquare (B i i)) ∧ A = ⁅B, C⁆ₘ :=
    ⟨B₀, C₀, hdiag₀, husq₀, hcomm₀⟩
  -- BddAbove for lambdaA image set
  have hbdd : BddAbove (lambdaA '' {A : Matrix (Fin n) (Fin n) ℂ | ZeroDiag A ∧ ‖A‖ = 1}) := by
    refine ⟨(n : ℝ) * (n - 1), fun x hx => ?_⟩
    obtain ⟨A', ⟨hzd', hnorm'⟩, rfl⟩ := hx
    obtain ⟨B', C', hdiag', husq', hcomm', hC'bound⟩ :=
      zeroDiag_InUnitSquare_decomp_bounded hn2 A' hzd'
    calc lambdaA A' ≤ ‖C'‖ := by
          apply csInf_le
          · exact ⟨0, fun c ⟨_, C, _, _, _, hle⟩ => le_trans (norm_nonneg _) hle⟩
          · exact ⟨B', C', hdiag', husq', hcomm', le_refl _⟩
      _ ≤ (n : ℝ) * (n - 1) * ‖A'‖ := hC'bound
      _ = (n : ℝ) * (n - 1) := by rw [hnorm']; ring
  -- lambdaA A ≤ lambdaM n
  have hlA_le : lambdaA A ≤ lambdaM n := by
    exact le_csSup hbdd ⟨A, ⟨hzd, hnorm⟩, rfl⟩
  -- lambdaA A ≤ Klam * n^ε'
  have hlA_bound : lambdaA A ≤ Klam * (n : ℝ) ^ ε' := le_trans hlA_le (hbound n)
  -- Extract witness
  obtain ⟨B, C, hdiag, husq, hcomm, hCnorm⟩ :=
    lambdaA_extract_witness hzd (Klam * (n : ℝ) ^ ε') hlA_bound 1 one_pos hne
  refine ⟨B, C, hdiag, hcomm, ?_⟩
  have hBnorm : ‖B‖ ≤ Real.sqrt 2 := InUnitSquare_diag_norm_le hdiag husq
  have hn_ge1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow_le : (n : ℝ) ^ ε' ≤ (n : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hn_ge1 hε'_le
  have hpow_ge1 : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn_ge1 (le_of_lt hε)
  calc ‖B‖ * ‖C‖
      ≤ Real.sqrt 2 * (Klam * (n : ℝ) ^ ε' + 1) := by
        apply mul_le_mul hBnorm hCnorm (norm_nonneg _) (by positivity)
    _ ≤ Real.sqrt 2 * (Klam * (n : ℝ) ^ ε + (n : ℝ) ^ ε) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 : Klam * (n : ℝ) ^ ε' ≤ Klam * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left hpow_le (le_of_lt hKlam_pos)
        linarith
    _ = Real.sqrt 2 * (Klam + 1) * (n : ℝ) ^ ε := by ring
    _ = K * (n : ℝ) ^ ε := by rw [hK_def]

/-- Every zero-diagonal matrix is a commutator with a diagonal first factor and
    polynomial norm bound.
    Uses zeroDiag_commutator_unit_norm_lambda (lambdaA-based) for the unit-norm case,
    then scales to handle general ‖A‖ and the A = 0 case. -/
theorem zeroDiag_commutator_bound_diagonal (ε : ℝ) (hε : 0 < ε) :
    ∃ (Kε : ℝ), 0 < Kε ∧
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
      ZeroDiag A →
      ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
        IsDiagMatrix B ∧ A = ⁅B, C⁆ₘ ∧
        ‖B‖ * ‖C‖ ≤ Kε * (n : ℝ) ^ ε * ‖A‖ := by
  obtain ⟨Kε, hKε_pos, hUnit⟩ := zeroDiag_commutator_unit_norm_lambda ε hε
  refine ⟨Kε, hKε_pos, fun n A hzd => ?_⟩
  by_cases hA : ‖A‖ = 0
  · -- A = 0 case: use B = 0, C = 0
    have hA0 : A = 0 := by rwa [norm_eq_zero] at hA
    exact ⟨0, 0, by simp [IsDiagMatrix], by simp [hA0, matComm], by simp [hA]⟩
  · -- A ≠ 0 case: normalize
    have hAnorm_pos : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA)
    have hAnorm_ne : (‖A‖ : ℝ) ≠ 0 := ne_of_gt hAnorm_pos
    -- A' = (1/‖A‖) • A has unit norm
    set A' := (↑(‖A‖⁻¹) : ℂ) • A with hA'_def
    have hA'_zd : ZeroDiag A' := fun i => by simp [hA'_def, hzd i]
    have hA'_norm : ‖A'‖ = 1 := by
      rw [hA'_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hAnorm_pos), inv_mul_cancel₀ hAnorm_ne]
    obtain ⟨B, C', hdiag, hcomm', hbound'⟩ := hUnit n A' hA'_zd hA'_norm
    -- Use B and (‖A‖ : ℂ) • C' as the decomposition
    refine ⟨B, (↑(‖A‖) : ℂ) • C', hdiag, ?_, ?_⟩
    · -- Show A = matComm B ((‖A‖ : ℂ) • C')
      have hA_eq : A = (↑(‖A‖) : ℂ) • A' := by
        rw [hA'_def, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hAnorm_ne,
            Complex.ofReal_one, one_smul]
      rw [matComm_smul_right, ← hcomm']
      exact hA_eq
    · -- Show ‖B‖ * ‖(‖A‖ : ℂ) • C'‖ ≤ Kε * n^ε * ‖A‖
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg A)]
      calc ‖B‖ * (‖A‖ * ‖C'‖) = ‖A‖ * (‖B‖ * ‖C'‖) := by ring
        _ ≤ ‖A‖ * (Kε * (↑n) ^ ε) :=
            mul_le_mul_of_nonneg_left hbound' (le_of_lt hAnorm_pos)
        _ = Kε * (↑n) ^ ε * ‖A‖ := by ring

/-- The norm-bound-only form used by the existing downstream API. -/
theorem zeroDiag_commutator_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ (Kε : ℝ), 0 < Kε ∧
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
      ZeroDiag A →
      ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
        A = ⁅B, C⁆ₘ ∧
        ‖B‖ * ‖C‖ ≤ Kε * (n : ℝ) ^ ε * ‖A‖ := by
  obtain ⟨Kε, hKε, hbound⟩ := zeroDiag_commutator_bound_diagonal ε hε
  refine ⟨Kε, hKε, fun n A hzd => ?_⟩
  obtain ⟨B, C, _hdiag, hcomm, hnorm⟩ := hbound n A hzd
  exact ⟨B, C, hcomm, hnorm⟩

/-! ## Helper lemmas for unitary conjugation -/

/-- IsUnitaryMatrix implies membership in Mathlib's unitary subgroup. -/
private lemma isUnitary_mem {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitaryMatrix U) : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
  constructor
  · change star U * U = 1; rw [Matrix.star_eq_conjTranspose]; exact hU.2
  · change U * star U = 1; rw [Matrix.star_eq_conjTranspose]; exact hU.1

/-- The conjugate transpose of a unitary matrix is unitary. -/
private lemma conjTranspose_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitaryMatrix U) : IsUnitaryMatrix U.conjTranspose :=
  ⟨by rw [Matrix.conjTranspose_conjTranspose]; exact hU.2,
   by rw [Matrix.conjTranspose_conjTranspose]; exact hU.1⟩

/-- Unitary matrices have operator norm 1 (when n > 0). -/
private lemma unitary_norm_one {n : ℕ} (hn : 0 < n) {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitaryMatrix U) : ‖U‖ = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Matrix (Fin n) (Fin n) ℂ) := ⟨⟨0, 1, by simp⟩⟩
  exact CStarRing.norm_coe_unitary ⟨U, isUnitary_mem hU⟩

/-- Recovering A from its unitary conjugation: U* · (U A U*) · U = A. -/
private lemma unitary_recover {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitaryMatrix U) (A : Matrix (Fin n) (Fin n) ℂ) :
    U.conjTranspose * (U * A * U.conjTranspose) * U = A := by
  simp only [Matrix.mul_assoc]
  rw [show U.conjTranspose * (U * (A * (U.conjTranspose * U))) =
    (U.conjTranspose * U) * (A * (U.conjTranspose * U)) from by simp [Matrix.mul_assoc]]
  rw [hU.2, Matrix.one_mul, Matrix.mul_one]

/-- The operator norm is invariant under unitary conjugation. -/
private lemma norm_conj_eq {n : ℕ} (hn : 0 < n) {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitaryMatrix U) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖U * A * U.conjTranspose‖ = ‖A‖ := by
  have hU1 : ‖U‖ = 1 := unitary_norm_one hn hU
  have hUc1 : ‖U.conjTranspose‖ = 1 := unitary_norm_one hn (conjTranspose_unitary hU)
  apply le_antisymm
  · calc ‖U * A * U.conjTranspose‖
        ≤ ‖U‖ * ‖A‖ * ‖U.conjTranspose‖ :=
          le_trans (norm_mul_le _ _)
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = ‖A‖ := by rw [hU1, hUc1, one_mul, mul_one]
  · conv_lhs => rw [← unitary_recover hU A]
    calc ‖U.conjTranspose * (U * A * U.conjTranspose) * U‖
        ≤ ‖U.conjTranspose‖ * ‖U * A * U.conjTranspose‖ * ‖U‖ :=
          le_trans (norm_mul_le _ _)
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = ‖U * A * U.conjTranspose‖ := by rw [hU1, hUc1, one_mul, mul_one]

/-- Key algebraic identity: inserting U*U = I between factors. -/
private lemma unitary_insert {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitaryMatrix U) (A B : Matrix (Fin n) (Fin n) ℂ) :
    U * A * U.conjTranspose * (U * B * U.conjTranspose) =
    U * (A * B) * U.conjTranspose := by
  simp only [Matrix.mul_assoc]
  rw [show U.conjTranspose * (U * (B * U.conjTranspose)) =
    (U.conjTranspose * U) * (B * U.conjTranspose) from by simp [Matrix.mul_assoc]]
  rw [hU.2, Matrix.one_mul]

/-- Commutator conjugation: U ⁅D, E⁆ₘ U* = ⁅UDU*, UEU*⁆ₘ. -/
private lemma conj_matComm {n : ℕ} (U D E : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitaryMatrix U) :
    U * matComm D E * U.conjTranspose =
    matComm (U * D * U.conjTranspose) (U * E * U.conjTranspose) := by
  simp only [matComm, mul_sub, sub_mul]
  rw [unitary_insert hU D E, unitary_insert hU E D]

/-! ## Theorem 3: Quantitative bound for zero-diagonal matrices -/

/-- JOS 2013, Theorem 3:
 every n×n zero-diagonal unit-norm matrix A satisfies
    μ(A, k) ≤ Kε * n^ε, where Kε depends only on ε. -/
-- Helper: a 1×1 zero-diagonal matrix is zero
private lemma zeroDiag_one_eq_zero (A : Matrix (Fin 1) (Fin 1) ℂ) (hzd : ZeroDiag A) :
    A = 0 := by
  ext i j; simp [show i = 0 from Fin.eq_zero i, show j = 0 from Fin.eq_zero j, hzd 0]

/-- A diagonal complex matrix is normal. -/
private lemma isDiagMatrix_normal {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : IsDiagMatrix B) :
    B * B.conjTranspose = B.conjTranspose * B := by
  have hdiag : B.IsDiag := fun i j hij => hB i j hij
  rw [← hdiag.diagonal_diag, Matrix.diagonal_conjTranspose]
  exact (Matrix.commute_diagonal _ _).eq

/-- Unitary conjugation preserves normality. -/
private lemma normal_conj {n : ℕ} {U B : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitaryMatrix U) (hN : B * B.conjTranspose = B.conjTranspose * B) :
    (U * B * U.conjTranspose) * (U * B * U.conjTranspose).conjTranspose =
    (U * B * U.conjTranspose).conjTranspose * (U * B * U.conjTranspose) := by
  -- (UBU*)* = U B* U* since conjTranspose reverses products
  have hconj : (U * B * U.conjTranspose).conjTranspose =
      U * B.conjTranspose * U.conjTranspose := by
    rw [show U * B * U.conjTranspose = U * (B * U.conjTranspose) from Matrix.mul_assoc _ _ _]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
  rw [hconj]
  -- LHS = U * (B * B^*) * U^*, RHS = U * (B^* * B) * U^*
  have lhs : U * B * U.conjTranspose * (U * B.conjTranspose * U.conjTranspose) =
      U * (B * B.conjTranspose) * U.conjTranspose := by
    calc U * B * U.conjTranspose * (U * B.conjTranspose * U.conjTranspose)
        = U * B * (U.conjTranspose * U) * B.conjTranspose * U.conjTranspose := by
          simp only [Matrix.mul_assoc]
      _ = U * B * B.conjTranspose * U.conjTranspose := by
          rw [hU.2, Matrix.mul_one]
      _ = U * (B * B.conjTranspose) * U.conjTranspose := by
          simp only [Matrix.mul_assoc]
  have rhs : U * B.conjTranspose * U.conjTranspose * (U * B * U.conjTranspose) =
      U * (B.conjTranspose * B) * U.conjTranspose := by
    calc U * B.conjTranspose * U.conjTranspose * (U * B * U.conjTranspose)
        = U * B.conjTranspose * (U.conjTranspose * U) * B * U.conjTranspose := by
          simp only [Matrix.mul_assoc]
      _ = U * B.conjTranspose * B * U.conjTranspose := by
          rw [hU.2, Matrix.mul_one]
      _ = U * (B.conjTranspose * B) * U.conjTranspose := by
          simp only [Matrix.mul_assoc]
  rw [lhs, rhs, hN]

/-- Spectrum is preserved under unitary conjugation. -/
private lemma spectrum_conj {n : ℕ} (U B : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitaryMatrix U) :
    spectrum ℂ (U * B * U.conjTranspose) = spectrum ℂ B := by
  -- Construct U as a unit in the matrix algebra
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    { val := U
      inv := U.conjTranspose
      val_inv := hU.1
      inv_val := hU.2 }
  -- U.conjTranspose = ↑(u⁻¹)
  have hinv : U.conjTranspose = (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) := by simp [u]
  rw [hinv]
  -- Now the goal is spectrum ℂ (↑u * B * ↑u⁻¹) = spectrum ℂ B
  exact @spectrum.units_conjugate ℂ _ _ _ _ B u

/-- JOS 2013, Theorem 3(i): for every ε > 0, every m×m zero-diagonal matrix A
    is a commutator A = [B, C] with ‖B‖ * ‖C‖ ≤ Kε * m^ε * ‖A‖.
    This is the zero-diagonal case, from which Theorem 1 follows via Fillmore's lemma.
    Proved from zeroDiag_commutator_bound. -/
theorem theorem_3i (ε : ℝ) (hε : 0 < ε) :
    ∃ (Kε : ℝ), 0 < Kε ∧
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
      ZeroDiag A →
      ∃ (B C : Matrix (Fin m) (Fin m) ℂ),
        A = ⁅B, C⁆ₘ ∧
        ‖B‖ * ‖C‖ ≤ Kε * (m : ℝ) ^ ε * ‖A‖ :=
  zeroDiag_commutator_bound ε hε

/-! ## Main Theorem 1 -/

/-- JOS 2013, Theorem 1: for every ε > 0 there exists Kε > 0 such that every trace-zero n×n
    complex matrix A is a commutator A = [B, C] with ‖B‖ * ‖C‖ ≤ Kε * n^ε * ‖A‖.
    This combines Fillmore's lemma (to reduce to zero-diagonal) with the recursive paving
    argument (Theorem 3) and the Rosenblum norm bound. -/
theorem main_commutator_theorem (ε : ℝ) (hε : 0 < ε) :
    ∃ (Kε : ℝ), 0 < Kε ∧
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
      A.trace = 0 →
      ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
        A = ⁅B, C⁆ₘ ∧
        ‖B‖ * ‖C‖ ≤ Kε * (n : ℝ) ^ ε * ‖A‖ := by
  -- Get the constant from zeroDiag_commutator_bound
  obtain ⟨Kε, hKε_pos, hBound⟩ := zeroDiag_commutator_bound ε hε
  exact ⟨Kε, hKε_pos, fun n A hTrace => by
    -- Step 1: Apply Fillmore's lemma to reduce to zero-diagonal case
    obtain ⟨U, B', hU, hZD, hAUBU⟩ := fillmore A hTrace
    -- Step 2: B' is zero-diagonal; apply zeroDiag_commutator_bound
    obtain ⟨D, E, hComm, hNormBound⟩ := hBound n B' hZD
    -- Step 3: Conjugate the commutator by U
    -- Take B = UDU*, C = UEU*. Then ⁅B, C⁆ₘ = U ⁅D, E⁆ₘ U* = U B' U* = A.
    refine ⟨U * D * U.conjTranspose, U * E * U.conjTranspose, ?_, ?_⟩
    · -- A = ⁅UDU*, UEU*⁆ₘ
      rw [← conj_matComm U D E hU, ← hComm, ← hAUBU]
    · -- ‖UDU*‖ * ‖UEU*‖ ≤ Kε * n^ε * ‖A‖
      by_cases hn : n = 0
      · -- n = 0: Fin 0 is empty, all matrices equal, all norms 0
        subst hn
        have h0 : ∀ M : Matrix (Fin 0) (Fin 0) ℂ, ‖M‖ = 0 := by
          intro M
          have : M = 0 := Matrix.ext (fun i => i.elim0)
          rw [this, norm_zero]
        simp [h0]
      · -- n > 0: use unitary norm invariance
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
        -- ‖B'‖ = ‖A‖ by unitary invariance: A = U B' U*
        have hB'_norm : ‖B'‖ = ‖A‖ := by
          rw [hAUBU, norm_conj_eq hn_pos hU B']
        rw [norm_conj_eq hn_pos hU D, norm_conj_eq hn_pos hU E, ← hB'_norm]
        exact hNormBound⟩

/-- JOS 2013, Theorem 1 with the paper's additional normality conclusion
    made explicit. -/
theorem main_commutator_theorem_normal (ε : ℝ) (hε : 0 < ε) :
    ∃ (Kε : ℝ), 0 < Kε ∧
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
      A.trace = 0 →
      ∃ (B C : Matrix (Fin n) (Fin n) ℂ),
        A = ⁅B, C⁆ₘ ∧
        B * B.conjTranspose = B.conjTranspose * B ∧
        ‖B‖ * ‖C‖ ≤ Kε * (n : ℝ) ^ ε * ‖A‖ := by
  obtain ⟨Kε, hKε_pos, hBound⟩ := zeroDiag_commutator_bound_diagonal ε hε
  refine ⟨Kε, hKε_pos, fun n A hTrace => ?_⟩
  obtain ⟨U, A', hU, hZD, hAUA⟩ := fillmore A hTrace
  obtain ⟨D, E, hDdiag, hComm, hNormBound⟩ := hBound n A' hZD
  refine ⟨U * D * U.conjTranspose, U * E * U.conjTranspose, ?_, ?_, ?_⟩
  · rw [← conj_matComm U D E hU, ← hComm, ← hAUA]
  · exact normal_conj hU (isDiagMatrix_normal hDdiag)
  · by_cases hn : n = 0
    · subst hn
      have h0 : ∀ M : Matrix (Fin 0) (Fin 0) ℂ, ‖M‖ = 0 := by
        intro M
        have : M = 0 := Matrix.ext (fun i => i.elim0)
        rw [this, norm_zero]
      simp [h0]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hA'_norm : ‖A'‖ = ‖A‖ := by
        rw [hAUA, norm_conj_eq hn_pos hU A']
      rw [norm_conj_eq hn_pos hU D, norm_conj_eq hn_pos hU E, ← hA'_norm]
      exact hNormBound

end CommutatorTheorem
