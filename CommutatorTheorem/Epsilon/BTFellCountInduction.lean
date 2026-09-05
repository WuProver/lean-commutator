import CommutatorTheorem.Epsilon.BTFellSignWordCrossing
import Mathlib.Data.Finset.DenselyOrdered

/-!
# Degree induction for Fell half-line root counts

Rolle sandwiches reduce the endpoint count comparison to normalized
derivatives.  A putative gap of two has even parity, hence equal endpoint
evaluation signs; local constancy then rules it out.
-/

open scoped Polynomial Topology

namespace CommutatorTheorem.BTFellCountInduction

open Polynomial Set Filter
open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTFellCrossGap
open CommutatorTheorem.BTFellRolleCount
open CommutatorTheorem.BTFellThreshold
open CommutatorTheorem.BTFellCountLocal

private noncomputable def pencil (p q : ℝ[X]) (t : ℝ) : ℝ[X] :=
  t • p + (1 - t) • q

/-- Degree-indexed form of the half-line count assertion, without a
root-disjointness hypothesis. -/
def PencilCountBalancedAtDegree (d : ℕ) : Prop :=
  ∀ (p q : ℝ[X]), p.Monic → q.Monic → RealRooted p → RealRooted q →
    p.natDegree = d → q.natDegree = d →
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → RealRooted (pencil p q t)) →
    RootsGTCountBalanced p q

private theorem rootsGTCount_eq_of_threshold_gap
    {p : ℝ[X]} {x y : ℝ} (hxy : x < y)
    (hy : ∀ r ∈ p.roots, x < r → y < r) :
    rootsGTCount p x = rootsGTCount p y := by
  unfold rootsGTCount
  congr 1
  apply Multiset.filter_congr
  intro r hr
  constructor
  · intro hxr
    exact hy r hr hxr
  · intro hyr
    exact hxy.trans hyr

set_option maxHeartbeats 800000 in
-- The nested degree induction and its two symmetric endpoint arguments need
-- a larger elaboration budget than Lean's default.
theorem pencilCountBalancedAtDegree_all :
    ∀ d : ℕ, PencilCountBalancedAtDegree d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro p q hp hq hpreal hqreal hpdegree hqdegree hall x
      by_cases hd : d = 0
      · have hpcard : p.roots.card = 0 := by
          rw [← hpreal.natDegree_eq_card_roots, hpdegree, hd]
        have hqcard : q.roots.card = 0 := by
          rw [← hqreal.natDegree_eq_card_roots, hqdegree, hd]
        have hpzero : rootsGTCount p x = 0 := by
          unfold rootsGTCount
          exact Nat.eq_zero_of_le_zero
            ((Multiset.card_le_card (Multiset.filter_le _ _)).trans_eq hpcard)
        have hqzero : rootsGTCount q x = 0 := by
          unfold rootsGTCount
          exact Nat.eq_zero_of_le_zero
            ((Multiset.card_le_card (Multiset.filter_le _ _)).trans_eq hqcard)
        simp [hpzero, hqzero]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
        let high : Finset ℝ :=
          (p.roots.toFinset ∪ q.roots.toFinset).filter (x < ·)
        obtain ⟨y, hxyAll, hyHigh⟩ :=
          ({x} : Finset ℝ).exists_between' high (by
            intro a ha r hr
            simp only [Finset.mem_singleton] at ha
            subst a
            exact (Finset.mem_filter.mp hr).2)
        have hxy : x < y := hxyAll x (by simp)
        have hyp : ∀ r ∈ p.roots, x < r → y < r := by
          intro r hr hxr
          apply hyHigh r
          exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _
            (Multiset.mem_toFinset.mpr hr), hxr⟩
        have hyq : ∀ r ∈ q.roots, x < r → y < r := by
          intro r hr hxr
          apply hyHigh r
          exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _
            (Multiset.mem_toFinset.mpr hr), hxr⟩
        have hpCount : rootsGTCount p x = rootsGTCount p y :=
          rootsGTCount_eq_of_threshold_gap hxy hyp
        have hqCount : rootsGTCount q x = rootsGTCount q y :=
          rootsGTCount_eq_of_threshold_gap hxy hyq
        have hpnot : ¬p.IsRoot y := by
          intro hyr
          have hyrMem := (mem_roots hp.ne_zero).mpr hyr
          exact (hyHigh y (Finset.mem_filter.mpr ⟨
            Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hyrMem), hxy⟩)).false
        have hqnot : ¬q.IsRoot y := by
          intro hyr
          have hyrMem := (mem_roots hq.ne_zero).mpr hyr
          exact (hyHigh y (Finset.mem_filter.mpr ⟨
            Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hyrMem), hxy⟩)).false
        let p' := normalizedDerivative d p
        let q' := normalizedDerivative d q
        have hp'monic : p'.Monic :=
          (normalizedDerivative_isMonicOfDegree hdpos hp hpdegree).monic
        have hq'monic : q'.Monic :=
          (normalizedDerivative_isMonicOfDegree hdpos hq hqdegree).monic
        have hp'degree : p'.natDegree = d - 1 :=
          (normalizedDerivative_isMonicOfDegree hdpos hp hpdegree).natDegree_eq
        have hq'degree : q'.natDegree = d - 1 :=
          (normalizedDerivative_isMonicOfDegree hdpos hq hqdegree).natDegree_eq
        have hp'real : RealRooted p' :=
          realRooted_normalizedDerivative hdpos hpreal hpdegree
        have hq'real : RealRooted q' :=
          realRooted_normalizedDerivative hdpos hqreal hqdegree
        have hderivHall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
            RealRooted (pencil p' q' t) := by
          intro t ht0 ht1
          rw [pencil, ← normalizedDerivative_convex]
          exact realRooted_normalizedDerivative hdpos (hall t ht0 ht1)
            (by
              apply natDegree_eq_of_le_of_coeff_ne_zero
              · exact (natDegree_add_le _ _).trans
                  (max_le ((natDegree_smul_le t p).trans hpdegree.le)
                    ((natDegree_smul_le (1 - t) q).trans hqdegree.le))
              · have hpc : p.coeff d = 1 := by
                  rw [← hpdegree]
                  exact hp.coeff_natDegree
                have hqc : q.coeff d = 1 := by
                  rw [← hqdegree]
                  exact hq.coeff_natDegree
                simp [coeff_add, coeff_smul, hpc, hqc])
        have hprev := ih (d - 1) (by omega) p' q' hp'monic hq'monic
          hp'real hq'real hp'degree hq'degree hderivHall y
        have hdcast : (d : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hd)
        have hp'roots : p'.roots = p.derivative.roots := by
          dsimp [p', normalizedDerivative]
          exact roots_smul_nonzero p.derivative hdcast
        have hq'roots : q'.roots = q.derivative.roots := by
          dsimp [q', normalizedDerivative]
          exact roots_smul_nonzero q.derivative hdcast
        have hprev' :
            rootsGTCount p.derivative y ≤ rootsGTCount q.derivative y + 1 ∧
              rootsGTCount q.derivative y ≤ rootsGTCount p.derivative y + 1 := by
          simpa [rootsGTCount, hp'roots, hq'roots] using hprev
        let Np := rootsGTCount p y
        let Nq := rootsGTCount q y
        let Mp := rootsGTCount p.derivative y
        let Mq := rootsGTCount q.derivative y
        have hpUpper : Np ≤ Mp + 1 := rootsGTCount_le_derivative_succ p y
        have hqUpper : Nq ≤ Mq + 1 := rootsGTCount_le_derivative_succ q y
        have hpLower : Mp ≤ Np :=
          derivative_rootsGTCount_le_unconditional hdpos hp hpreal hpdegree y
        have hqLower : Mq ≤ Nq :=
          derivative_rootsGTCount_le_unconditional hdpos hq hqreal hqdegree y
        have hroughP : Np ≤ Nq + 2 := by
          dsimp [Np, Nq, Mp, Mq] at *
          omega
        have hroughQ : Nq ≤ Np + 2 := by
          dsimp [Np, Nq, Mp, Mq] at *
          omega
        have hsharpP : Np ≤ Nq + 1 := by
          by_contra hbad
          have heq : Np = Nq + 2 := by omega
          have hsp : 0 < (-1 : ℝ) ^ Np * p.eval y := by
            simpa [Np, rootsGTCount, Multiset.countP_eq_card_filter] using
              signed_eval_pos_by_roots_gt_count hp hpreal hpnot
          have hsq : 0 < (-1 : ℝ) ^ Nq * q.eval y := by
            simpa [Nq, rootsGTCount, Multiset.countP_eq_card_filter] using
              signed_eval_pos_by_roots_gt_count hq hqreal hqnot
          rw [heq, pow_add] at hsp
          norm_num at hsp
          have hprod : 0 < p.eval y * q.eval y := by
            rcases neg_one_pow_eq_or ℝ Nq with hpow | hpow <;>
              rw [hpow] at hsp hsq <;> norm_num at hsp hsq <;> nlinarith
          have hno : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
              ¬(pencil p q t).IsRoot y := by
            intro t ht0 ht1 hroot
            rw [IsRoot, pencil, eval_convex_eq] at hroot
            rcases mul_pos_iff.mp hprod with hpos | hneg
            · by_cases ht : t = 0
              · subst t
                norm_num at hroot
                linarith
              · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
                have htp : 0 < t * p.eval y := mul_pos htpos hpos.1
                have htq : 0 ≤ (1 - t) * q.eval y :=
                  mul_nonneg (sub_nonneg.mpr ht1) hpos.2.le
                have hsum : t * p.eval y + (1 - t) * q.eval y = 0 := by
                  calc
                    _ = t * (p.eval y - q.eval y) + q.eval y := by ring
                    _ = 0 := hroot
                exact (ne_of_gt (add_pos_of_pos_of_nonneg htp htq)) hsum
            · by_cases ht : t = 0
              · subst t
                norm_num at hroot
                linarith
              · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
                have htp : t * p.eval y < 0 := mul_neg_of_pos_of_neg htpos hneg.1
                have htq : (1 - t) * q.eval y ≤ 0 :=
                  mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hneg.2.le
                have hsum : t * p.eval y + (1 - t) * q.eval y = 0 := by
                  calc
                    _ = t * (p.eval y - q.eval y) + q.eval y := by ring
                    _ = 0 := hroot
                exact (ne_of_lt (add_neg_of_neg_of_nonpos htp htq)) hsum
          let F : Set.Icc (0 : ℝ) 1 → ℕ := fun t =>
            rootsGTCount (pencil p q t) y
          have hFlocal : IsLocallyConstant F :=
            (IsLocallyConstant.iff_eventually_eq F).2 fun z => by
              have hev := eventually_rootsGTCount_eq hp hq hpdegree hqdegree
                hall z.property (hno z z.property.1 z.property.2)
              rw [nhdsWithin_eq_map_subtype_coe z.property] at hev
              simpa [F] using hev
          letI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
            Subtype.preconnectedSpace isPreconnected_Icc
          have hends := hFlocal.apply_eq_of_preconnectedSpace
            (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1)
            (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1)
          have : Np = Nq := by simpa [F, pencil, Np, Nq] using hends
          omega
        have hsharpQ : Nq ≤ Np + 1 := by
          by_contra hbad
          have heq : Nq = Np + 2 := by omega
          have hsp : 0 < (-1 : ℝ) ^ Np * p.eval y := by
            simpa [Np, rootsGTCount, Multiset.countP_eq_card_filter] using
              signed_eval_pos_by_roots_gt_count hp hpreal hpnot
          have hsq : 0 < (-1 : ℝ) ^ Nq * q.eval y := by
            simpa [Nq, rootsGTCount, Multiset.countP_eq_card_filter] using
              signed_eval_pos_by_roots_gt_count hq hqreal hqnot
          rw [heq, pow_add] at hsq
          norm_num at hsq
          have hprod : 0 < p.eval y * q.eval y := by
            rcases neg_one_pow_eq_or ℝ Np with hpow | hpow <;>
              rw [hpow] at hsp hsq <;> norm_num at hsp hsq <;> nlinarith
          have hno : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
              ¬(pencil p q t).IsRoot y := by
            intro t ht0 ht1 hroot
            rw [IsRoot, pencil, eval_convex_eq] at hroot
            rcases mul_pos_iff.mp hprod with hpos | hneg
            · by_cases ht : t = 0
              · subst t
                norm_num at hroot
                linarith
              · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
                have htp : 0 < t * p.eval y := mul_pos htpos hpos.1
                have htq : 0 ≤ (1 - t) * q.eval y :=
                  mul_nonneg (sub_nonneg.mpr ht1) hpos.2.le
                have hsum : t * p.eval y + (1 - t) * q.eval y = 0 := by
                  calc
                    _ = t * (p.eval y - q.eval y) + q.eval y := by ring
                    _ = 0 := hroot
                exact (ne_of_gt (add_pos_of_pos_of_nonneg htp htq)) hsum
            · by_cases ht : t = 0
              · subst t
                norm_num at hroot
                linarith
              · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
                have htp : t * p.eval y < 0 := mul_neg_of_pos_of_neg htpos hneg.1
                have htq : (1 - t) * q.eval y ≤ 0 :=
                  mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hneg.2.le
                have hsum : t * p.eval y + (1 - t) * q.eval y = 0 := by
                  calc
                    _ = t * (p.eval y - q.eval y) + q.eval y := by ring
                    _ = 0 := hroot
                exact (ne_of_lt (add_neg_of_neg_of_nonpos htp htq)) hsum
          let F : Set.Icc (0 : ℝ) 1 → ℕ := fun t =>
            rootsGTCount (pencil p q t) y
          have hFlocal : IsLocallyConstant F :=
            (IsLocallyConstant.iff_eventually_eq F).2 fun z => by
              have hev := eventually_rootsGTCount_eq hp hq hpdegree hqdegree
                hall z.property (hno z z.property.1 z.property.2)
              rw [nhdsWithin_eq_map_subtype_coe z.property] at hev
              simpa [F] using hev
          letI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
            Subtype.preconnectedSpace isPreconnected_Icc
          have hends := hFlocal.apply_eq_of_preconnectedSpace
            (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1)
            (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1)
          have : Np = Nq := by simpa [F, pencil, Np, Nq] using hends
          omega
        rw [hpCount, hqCount]
        exact ⟨hsharpP, hsharpQ⟩

/-- The root-count balance required by the cross-gap reduction. -/
theorem rootsGTCountBalanced_of_convex_realRooted
    {p q : ℝ[X]} {d : ℕ}
    (hp : p.Monic) (hq : q.Monic)
    (hpreal : RealRooted p) (hqreal : RealRooted q)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      RealRooted (t • p + (1 - t) • q)) :
    RootsGTCountBalanced p q :=
  pencilCountBalancedAtDegree_all d p q hp hq hpreal hqreal
    hpdegree hqdegree hall

/-- The arbitrary-degree root-disjoint Fell converse. -/
theorem rootDisjointPairFellConverseAtDegree_all
    (d : ℕ) (hd : 2 ≤ d) : RootDisjointPairFellConverseAtDegree d := by
  apply rootDisjointPairFellConverseAtDegree_of_rootsGTCountBalanced d hd
  intro p q hp hq hpreal hqreal hpdegree hqdegree _hdisjoint hall
  exact rootsGTCountBalanced_of_convex_realRooted hp hq hpreal hqreal
    hpdegree hqdegree hall

end CommutatorTheorem.BTFellCountInduction
