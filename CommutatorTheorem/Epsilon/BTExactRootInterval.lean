import CommutatorTheorem.Epsilon.BTLeafSpectral

/-!
# Root interval of the exact mixed determinantal polynomial

Hermitian contractions have spectrum in `[-1,1]`.  This file transports that
fact first to every exact-MDP leaf and then, by positivity to the right of the
leaf roots, to the uniform exact-MDP average.
-/

namespace CommutatorTheorem.BTExactRootInterval

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
  Matrix.instL2OpNormedSpace Matrix.instL2OpNormedRing Matrix.instCStarRing

open scoped BigOperators Polynomial
open Polynomial Finset
open CommutatorTheorem
open CommutatorTheorem.BTMixedDet
open CommutatorTheorem.BTMixedDeterminantal
open CommutatorTheorem.BTMDPSelection

/-- A root of a product leaf is a root of one of its real characteristic
polynomial factors. -/
theorem exists_realCharpoly_root_of_realColoringPolynomial_isRoot
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (c : Coloring n k)
    {r : ℝ} (hr : (realColoringPolynomial A hA c).IsRoot r) :
    ∃ a : Fin k,
      (realCharpoly (BTMixedDet.principalCompression (A a) c a)
        (BTMixedDet.principalCompression_isHermitian (hA a) c a)).IsRoot r := by
  rw [Polynomial.IsRoot, realColoringPolynomial, Polynomial.eval_prod] at hr
  obtain ⟨a, _ha, haroot⟩ := Finset.prod_eq_zero_iff.mp hr
  exact ⟨a, haroot⟩

private theorem norm_root_charpoly_hermitian_le_one {m : ℕ}
    (B : Matrix (Fin m) (Fin m) ℂ) (hB : B.IsHermitian)
    (hBnorm : ‖B‖ ≤ 1) {z : ℂ} (hz : B.charpoly.IsRoot z) :
    ‖z‖ ≤ 1 := by
  have hzroots : z ∈ B.charpoly.roots :=
    (Polynomial.mem_roots B.charpoly_monic.ne_zero).2 hz
  rw [hB.roots_charpoly_eq_eigenvalues] at hzroots
  obtain ⟨i, _hi, hiz⟩ := Multiset.mem_map.mp hzroots
  have hdiagNorm : ‖fun j : Fin m ↦ (hB.eigenvalues j : ℂ)‖ ≤ 1 := by
    have hBnorm' := hBnorm
    rw [hB.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal] at hBnorm'
    exact hBnorm'
  rw [← hiz]
  exact (norm_le_pi_norm (fun j : Fin m ↦ (hB.eigenvalues j : ℂ)) i).trans
    hdiagNorm

/-- Every root of an exact-MDP leaf lies in `[-1,1]` when all input matrices
are Hermitian contractions. -/
theorem abs_root_realColoringPolynomial_le_one
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hAnorm : ∀ a, ‖A a‖ ≤ 1)
    (c : Coloring n k) {r : ℝ}
    (hr : (realColoringPolynomial A hA c).IsRoot r) :
    |r| ≤ 1 := by
  obtain ⟨a, hra⟩ :=
    exists_realCharpoly_root_of_realColoringPolynomial_isRoot A hA c hr
  let M := BTMixedDet.principalCompression (A a) c a
  let hM : M.IsHermitian :=
    BTMixedDet.principalCompression_isHermitian (hA a) c a
  let e : ColorFiber c a ≃ Fin (Fintype.card (ColorFiber c a)) :=
    Fintype.equivFin (ColorFiber c a)
  let B : Matrix (Fin (Fintype.card (ColorFiber c a)))
      (Fin (Fintype.card (ColorFiber c a))) ℂ := Matrix.reindex e e M
  have hrmap := hra.map (f := Complex.ofRealHom)
  have hrM : M.charpoly.IsRoot (r : ℂ) := by
    rw [realCharpoly_map_complex M hM] at hrmap
    exact hrmap
  have hrB : B.charpoly.IsRoot (r : ℂ) := by
    dsimp only [B]
    rw [Matrix.charpoly_reindex]
    exact hrM
  have hB : B.IsHermitian := by
    dsimp only [B]
    exact hM.reindex e
  have hemb : Function.Injective
      (fun i : Fin (Fintype.card (ColorFiber c a)) ↦ (e.symm i).1) := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  have hBnorm : ‖B‖ ≤ ‖A a‖ := by
    have hsub := CommutatorTheorem.submatrix_norm_le
      (fun i : Fin (Fintype.card (ColorFiber c a)) ↦ (e.symm i).1)
      hemb (A a)
    simpa [B, M, BTMixedDet.principalCompression, Matrix.reindex_apply,
      Matrix.submatrix_submatrix, Function.comp_def] using hsub
  have hrnorm : ‖(r : ℂ)‖ ≤ 1 :=
    norm_root_charpoly_hermitian_le_one B hB
      (hBnorm.trans (hAnorm a)) hrB
  simpa [Real.norm_eq_abs] using hrnorm

/-- In particular, `1` is an upper bound for all roots of every leaf. -/
theorem realColoringPolynomial_rootUpperBound_one
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hAnorm : ∀ a, ‖A a‖ ≤ 1)
    (c : Coloring n k) :
    IsRootUpperBound (realColoringPolynomial A hA c) 1 := by
  intro r hr
  exact (abs_le.mp (abs_root_realColoringPolynomial_le_one A hA hAnorm c hr)).2

/-- Every leaf evaluates positively to the right of `1`. -/
theorem realColoringPolynomial_eval_pos_of_one_lt
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hAnorm : ∀ a, ‖A a‖ ≤ 1)
    (c : Coloring n k) {x : ℝ} (hx : 1 < x) :
    0 < (realColoringPolynomial A hA c).eval x := by
  apply (realColoringPolynomial_realRooted A hA c).eval_pos_of_strictRootUpperBound
    (realColoringPolynomial_monic A hA c)
  intro r hr
  exact lt_of_le_of_lt (realColoringPolynomial_rootUpperBound_one A hA hAnorm c r hr) hx

/-- The uniform exact-MDP average evaluates positively at every `x > 1`. -/
theorem realMixedDeterminantalPolynomial_eval_pos_of_one_lt
    {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hAnorm : ∀ a, ‖A a‖ ≤ 1)
    {x : ℝ} (hx : 1 < x) :
    0 < (realMixedDeterminantalPolynomial A hA).eval x := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hcard : 0 < (Fintype.card (Coloring n k) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Coloring n k))
  have hsum : 0 < ∑ c : Coloring n k,
      (realColoringPolynomial A hA c).eval x := by
    exact Finset.sum_pos
      (fun c _ ↦ realColoringPolynomial_eval_pos_of_one_lt A hA hAnorm c hx)
      Finset.univ_nonempty
  rw [realMixedDeterminantalPolynomial, Polynomial.eval_smul,
    Polynomial.eval_finset_sum]
  simpa only [smul_eq_mul] using mul_pos (inv_pos.mpr hcard) hsum

/-- The exact MDP itself has no root to the right of `1`.  This conclusion is
independent of the real-stability input; real-rootedness is needed later only
to apply univariate root shrinking. -/
theorem realMixedDeterminantalPolynomial_rootUpperBound_one
    {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hAnorm : ∀ a, ‖A a‖ ≤ 1) :
    IsRootUpperBound (realMixedDeterminantalPolynomial A hA) 1 := by
  intro r hr
  by_contra hnot
  have hpos := realMixedDeterminantalPolynomial_eval_pos_of_one_lt
    hk A hA hAnorm (lt_of_not_ge hnot)
  exact hpos.ne' hr

private lemma signed_prod_sub_pos (s : Multiset ℝ) {x : ℝ}
    (hx : ∀ r ∈ s, x < r) :
    0 < (-1 : ℝ) ^ s.card * (s.map fun r ↦ x - r).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
      have hr : x < r := hx r (by simp)
      have hs : 0 < (-1 : ℝ) ^ s.card * (s.map fun z ↦ x - z).prod := by
        apply ih
        intro z hz
        exact hx z (by simp [hz])
      calc
        0 < (r - x) *
            ((-1 : ℝ) ^ s.card * (s.map fun z ↦ x - z).prod) :=
          mul_pos (sub_pos.mpr hr) hs
        _ = (-1 : ℝ) ^ (r ::ₘ s).card *
            ((r ::ₘ s).map fun z ↦ x - z).prod := by
          simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ]
          ring

/-- To the left of `-1`, a degree-`n` leaf has the strict sign `(-1)^n`. -/
theorem realColoringPolynomial_signed_eval_pos_of_lt_neg_one
    {n k : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hAnorm : ∀ a, ‖A a‖ ≤ 1)
    (c : Coloring n k) {x : ℝ} (hx : x < -1) :
    0 < (-1 : ℝ) ^ n * (realColoringPolynomial A hA c).eval x := by
  let p := realColoringPolynomial A hA c
  have hp : RealRooted p := realColoringPolynomial_realRooted A hA c
  have hmonic : p.Monic := realColoringPolynomial_monic A hA c
  rw [hp.eval_eq_prod_roots_of_monic hmonic]
  have hright : ∀ r ∈ p.roots, x < r := by
    intro r hr
    have hrroot : p.IsRoot r :=
      (Polynomial.mem_roots hmonic.ne_zero).mp hr
    have hminus : -1 ≤ r :=
      (abs_le.mp (abs_root_realColoringPolynomial_le_one A hA hAnorm c hrroot)).1
    exact hx.trans_le hminus
  have hsigned := signed_prod_sub_pos p.roots hright
  have hcard : p.roots.card = n := by
    rw [← hp.natDegree_eq_card_roots]
    exact realColoringPolynomial_natDegree A hA c
  rwa [hcard] at hsigned

/-- The uniform exact-MDP average has the same strict signed evaluation to
the left of `-1`. -/
theorem realMixedDeterminantalPolynomial_signed_eval_pos_of_lt_neg_one
    {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hAnorm : ∀ a, ‖A a‖ ≤ 1)
    {x : ℝ} (hx : x < -1) :
    0 < (-1 : ℝ) ^ n *
      (realMixedDeterminantalPolynomial A hA).eval x := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hcard : 0 < (Fintype.card (Coloring n k) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Coloring n k))
  have hsum : 0 < ∑ c : Coloring n k,
      (-1 : ℝ) ^ n * (realColoringPolynomial A hA c).eval x := by
    exact Finset.sum_pos
      (fun c _ ↦ realColoringPolynomial_signed_eval_pos_of_lt_neg_one
        A hA hAnorm c hx)
      Finset.univ_nonempty
  rw [realMixedDeterminantalPolynomial, Polynomial.eval_smul,
    Polynomial.eval_finset_sum]
  simp only [smul_eq_mul]
  calc
    0 < (Fintype.card (Coloring n k) : ℝ)⁻¹ *
        ∑ c : Coloring n k,
          (-1 : ℝ) ^ n * (realColoringPolynomial A hA c).eval x :=
      mul_pos (inv_pos.mpr hcard) hsum
    _ = (-1 : ℝ) ^ n *
        ((Fintype.card (Coloring n k) : ℝ)⁻¹ *
          ∑ c : Coloring n k, (realColoringPolynomial A hA c).eval x) := by
      rw [← Finset.mul_sum]
      ring

/-- The exact MDP has no root to the left of `-1`. -/
theorem realMixedDeterminantalPolynomial_rootLowerBound_neg_one
    {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hAnorm : ∀ a, ‖A a‖ ≤ 1) :
    ∀ r : ℝ, (realMixedDeterminantalPolynomial A hA).IsRoot r → -1 ≤ r := by
  intro r hr
  by_contra hnot
  have hsign := realMixedDeterminantalPolynomial_signed_eval_pos_of_lt_neg_one
    hk A hA hAnorm (lt_of_not_ge hnot)
  rw [hr] at hsign
  simp at hsign

/-- Every real root of the exact MDP lies in the full contraction interval
`[-1,1]`. -/
theorem realMixedDeterminantalPolynomial_root_mem_unitInterval
    {n k : ℕ} (hk : 0 < k)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hAnorm : ∀ a, ‖A a‖ ≤ 1)
    {r : ℝ} (hr : (realMixedDeterminantalPolynomial A hA).IsRoot r) :
    r ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨realMixedDeterminantalPolynomial_rootLowerBound_neg_one hk A hA hAnorm r hr,
    realMixedDeterminantalPolynomial_rootUpperBound_one hk A hA hAnorm r hr⟩

end CommutatorTheorem.BTExactRootInterval
