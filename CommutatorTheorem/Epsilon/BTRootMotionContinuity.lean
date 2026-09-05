import CommutatorTheorem.Epsilon.BTMDPJointControl
import Mathlib.Analysis.Normed.Field.Approximation

/-!
# Largest-root continuity infrastructure for affine pencils

This module packages the canonical largest real root and the algebraic
no-return property of a nonconstant affine polynomial pencil.  These are the
interfaces needed to turn the moment-divergence estimate into root motion.
-/

open scoped Polynomial Topology

namespace CommutatorTheorem.BTRootMotionContinuity

open Polynomial
open CommutatorTheorem

/-- A chosen largest root of a nonconstant real-rooted polynomial. -/
noncomputable def largestRealRoot (p : ℝ[X]) (hp : RealRooted p)
    (hd : 0 < p.natDegree) : ℝ :=
  Classical.choose (hp.exists_largestRoot hd)

theorem largestRealRoot_isLargest (p : ℝ[X]) (hp : RealRooted p)
    (hd : 0 < p.natDegree) :
    IsLargestRoot p (largestRealRoot p hp hd) :=
  Classical.choose_spec (hp.exists_largestRoot hd)

theorem largestRealRoot_isRoot (p : ℝ[X]) (hp : RealRooted p)
    (hd : 0 < p.natDegree) :
    p.IsRoot (largestRealRoot p hp hd) :=
  (largestRealRoot_isLargest p hp hd).isRoot

theorem root_le_largestRealRoot (p : ℝ[X]) (hp : RealRooted p)
    (hd : 0 < p.natDegree) {x : ℝ} (hx : p.IsRoot x) :
    x ≤ largestRealRoot p hp hd :=
  (largestRealRoot_isLargest p hp hd).upperBound x hx

theorem isRootUpperBound_iff_largestRealRoot_le
    (p : ℝ[X]) (hp : RealRooted p) (hd : 0 < p.natDegree)
    (x : ℝ) :
    IsRootUpperBound p x ↔ largestRealRoot p hp hd ≤ x := by
  constructor
  · intro hx
    exact hx _ (largestRealRoot_isRoot p hp hd)
  · intro hx y hy
    exact (root_le_largestRealRoot p hp hd hy).trans hx

/-- A convenient fixed positive bound for the norms of all roots of `p`. -/
noncomputable def rootNormBound (p : ℝ[X]) : ℝ :=
  max (p.roots.map norm).sum 1

theorem rootNormBound_pos (p : ℝ[X]) : 0 < rootNormBound p := by
  exact zero_lt_one.trans_le (le_max_right _ _)

theorem norm_root_le_rootNormBound {p : ℝ[X]} {a : ℝ}
    (ha : a ∈ p.roots) : ‖a‖ ≤ rootNormBound p := by
  apply (Multiset.single_le_sum (s := p.roots.map norm)
    (fun x hx ↦ ?_) ‖a‖ (Multiset.mem_map.mpr ⟨a, ha, rfl⟩)).trans
    (le_max_left _ _)
  obtain ⟨y, _hy, rfl⟩ := Multiset.mem_map.mp hx
  exact norm_nonneg y

/-- Quantitative continuity estimate for the largest root.  The coefficient
error is converted to the root-error scale `k` used by mathlib's root
approximation theorem.  The denominator comes from controlling the theorem's
apparently circular `max ‖a‖ 1` factor in the reverse direction. -/
theorem norm_largestRealRoot_sub_lt_of_norm_coeff_sub_lt
    {p q : ℝ[X]} (hpmonic : p.Monic) (hqmonic : q.Monic)
    (hpreal : RealRooted p) (hqreal : RealRooted q)
    (hdegree : q.natDegree = p.natDegree)
    (hpdeg : 0 < p.natDegree) {eta : ℝ} (heta : 0 < eta)
    (hcoeff : ∀ i : ℕ, ‖q.coeff i - p.coeff i‖ < eta) :
    let k := (((p.natDegree + 1 : ℕ) : ℝ) * eta) ^
      (p.natDegree : ℝ)⁻¹
    0 < k → k < 1 →
      ‖largestRealRoot p hpreal hpdeg -
          largestRealRoot q hqreal (hdegree.symm ▸ hpdeg)‖ <
        k * rootNormBound p / (1 - k) := by
  dsimp only
  intro hk0 hk1
  let ap := largestRealRoot p hpreal hpdeg
  let aq := largestRealRoot q hqreal (hdegree.symm ▸ hpdeg)
  let k : ℝ := (((p.natDegree + 1 : ℕ) : ℝ) * eta) ^
    (p.natDegree : ℝ)⁻¹
  let M := rootNormBound p
  have hMpos : 0 < M := rootNormBound_pos p
  have hMone : 1 ≤ M := le_max_right _ _
  have hkap : max ‖ap‖ 1 ≤ M := by
    apply max_le
    · exact norm_root_le_rootNormBound
        ((mem_roots hpmonic.ne_zero).mpr
          (largestRealRoot_isRoot p hpreal hpdeg))
    · exact hMone
  have hapEval : p.eval ap = 0 := largestRealRoot_isRoot p hpreal hpdeg
  obtain ⟨bq, hbqroot, hbqclose⟩ :=
    exists_roots_norm_sub_lt_of_norm_coeff_sub_lt heta hapEval
      hpmonic hqmonic hdegree hcoeff hqreal
  have hbqclose' : ‖ap - bq‖ < k * max ‖ap‖ 1 := by
    simpa [k, Nat.cast_add, Nat.cast_one] using hbqclose
  have hbqle : bq ≤ aq := root_le_largestRealRoot q hqreal
    (hdegree.symm ▸ hpdeg) ((mem_roots hqmonic.ne_zero).mp hbqroot)
  have hlower : ap - aq < k * M := by
    calc
      ap - aq ≤ ap - bq := sub_le_sub_left hbqle ap
      _ ≤ ‖ap - bq‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ < k * max ‖ap‖ 1 := hbqclose'
      _ ≤ k * M := mul_le_mul_of_nonneg_left hkap hk0.le
  have haqEval : q.eval aq = 0 :=
    largestRealRoot_isRoot q hqreal (hdegree.symm ▸ hpdeg)
  have hcoeffRev : ∀ i : ℕ, ‖p.coeff i - q.coeff i‖ < eta := by
    intro i
    simpa [norm_sub_rev] using hcoeff i
  obtain ⟨bp, hbproot, hbpclose⟩ :=
    exists_roots_norm_sub_lt_of_norm_coeff_sub_lt heta haqEval
      hqmonic hpmonic hdegree.symm hcoeffRev hpreal
  have hbpclose' : ‖aq - bp‖ < k * max ‖aq‖ 1 := by
    simpa [k, hdegree, Nat.cast_add, Nat.cast_one] using hbpclose
  have hbpNorm : ‖bp‖ ≤ M := norm_root_le_rootNormBound hbproot
  have hden : 0 < 1 - k := sub_pos.mpr hk1
  have haqNorm : ‖aq‖ < M / (1 - k) := by
    by_cases haq1 : ‖aq‖ ≤ 1
    · calc
        ‖aq‖ ≤ 1 := haq1
        _ ≤ M := hMone
        _ < M / (1 - k) := by
          rw [lt_div_iff₀ hden]
          nlinarith
    · have hmax : max ‖aq‖ 1 = ‖aq‖ :=
        max_eq_left (le_of_not_ge haq1)
      have htri : ‖aq‖ ≤ ‖aq - bp‖ + ‖bp‖ := by
        calc
          ‖aq‖ = ‖(aq - bp) + bp‖ := by ring_nf
          _ ≤ ‖aq - bp‖ + ‖bp‖ := norm_add_le _ _
      rw [hmax] at hbpclose'
      rw [lt_div_iff₀ hden]
      nlinarith
  have hmaxAq : max ‖aq‖ 1 < M / (1 - k) := by
    rw [max_lt_iff]
    refine ⟨haqNorm, ?_⟩
    rw [lt_div_iff₀ hden]
    nlinarith
  have hbpLe : bp ≤ ap := root_le_largestRealRoot p hpreal hpdeg
    ((mem_roots hpmonic.ne_zero).mp hbproot)
  have hupper : aq - ap < k * M / (1 - k) := by
    calc
      aq - ap ≤ aq - bp := sub_le_sub_left hbpLe aq
      _ ≤ ‖aq - bp‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ < k * max ‖aq‖ 1 := hbpclose'
      _ < k * (M / (1 - k)) :=
        mul_lt_mul_of_pos_left hmaxAq hk0
      _ = k * M / (1 - k) := by ring
  rw [Real.norm_eq_abs, abs_lt]
  constructor
  · simpa [ap, aq, k, M] using (show
      -(k * M / (1 - k)) < ap - aq by linarith [hupper])
  · have hid : (k * M / (1 - k)) * (1 - k) = k * M := by
      field_simp
    have htarget : k * M < k * M / (1 - k) := by
      nlinarith [mul_pos hk0 hMpos]
    simpa [ap, aq, k, M] using
      (show ap - aq < k * M / (1 - k) by linarith)

/-- A positive finite bound for all direction coefficients through degree
`d`; coefficients above `d` vanish when the direction degree is at most `d`. -/
noncomputable def directionCoeffNormBound (d : ℕ) (s : ℝ[X]) : ℝ :=
  max (∑ i ∈ Finset.range (d + 1), ‖s.coeff i‖) 1

theorem directionCoeffNormBound_pos (d : ℕ) (s : ℝ[X]) :
    0 < directionCoeffNormBound d s :=
  zero_lt_one.trans_le (le_max_right _ _)

theorem norm_coeff_le_directionCoeffNormBound
    {d : ℕ} {s : ℝ[X]} (hsdegree : s.natDegree ≤ d) (i : ℕ) :
    ‖s.coeff i‖ ≤ directionCoeffNormBound d s := by
  by_cases hi : i ≤ d
  · apply (Finset.single_le_sum
      (fun j _ ↦ norm_nonneg (s.coeff j))
      (Finset.mem_range.mpr (by omega : i < d + 1))).trans
      (le_max_left _ _)
  · have hzero : s.coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hzero, (directionCoeffNormBound_pos d s).le]

/-- Coefficients of an affine polynomial pencil are uniformly Lipschitz in
the parameter. -/
theorem norm_affine_pencil_coeff_sub_le
    {d : ℕ} {r s : ℝ[X]} (hsdegree : s.natDegree ≤ d)
    (u v : ℝ) (i : ℕ) :
    ‖(r + u • s).coeff i - (r + v • s).coeff i‖ ≤
      ‖u - v‖ * directionCoeffNormBound d s := by
  rw [coeff_add, coeff_add, coeff_smul, coeff_smul]
  simp only [smul_eq_mul]
  have heq : r.coeff i + u * s.coeff i -
      (r.coeff i + v * s.coeff i) = (u - v) * s.coeff i := by ring
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_coeff_le_directionCoeffNormBound hsdegree i) (norm_nonneg _)

/-- A fixed-degree affine pencil has direction degree no larger than the
common degree. -/
theorem direction_natDegree_le_of_affine_natDegree
    {d : ℕ} {r s : ℝ[X]}
    (hdegree : ∀ t : ℝ, 0 ≤ t → (r + t • s).natDegree = d) :
    s.natDegree ≤ d := by
  have hr : r.natDegree = d := by simpa using hdegree 0 le_rfl
  have hrs : (r + s).natDegree = d := by simpa using hdegree 1 zero_le_one
  have hsrepr : s = (r + s) - r := by module
  rw [hsrepr]
  exact (natDegree_sub_le _ _).trans (by simp [hr, hrs])

/-- Epsilon--delta continuity of the largest root along a fixed-degree monic
real-rooted affine pencil on the nonnegative parameter half-line. -/
theorem exists_delta_largestRealRoot_affine
    (d : ℕ) (r s : ℝ[X]) (hd : 0 < d)
    (hmonic : ∀ t : ℝ, 0 ≤ t → (r + t • s).Monic)
    (hdegree : ∀ t : ℝ, 0 ≤ t → (r + t • s).natDegree = d)
    (hreal : ∀ t : ℝ, 0 ≤ t → RealRooted (r + t • s))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (t : ℝ) (ht : 0 ≤ t),
      ‖t - t₀‖ < delta →
      ‖largestRealRoot (r + t • s) (hreal t ht)
          (by rw [hdegree t ht]; exact hd) -
        largestRealRoot (r + t₀ • s) (hreal t₀ ht₀)
          (by rw [hdegree t₀ ht₀]; exact hd)‖ < eps := by
  let p₀ := r + t₀ • s
  let M := rootNormBound p₀
  let C := directionCoeffNormBound d s
  let kappa : ℝ := min (1 / 2) (eps / (2 * M))
  let eta : ℝ := kappa ^ (d : ℝ) / (d + 1 : ℝ)
  let delta : ℝ := eta / C
  have hM : 0 < M := rootNormBound_pos p₀
  have hC : 0 < C := directionCoeffNormBound_pos d s
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact lt_min (by norm_num) (div_pos heps (by positivity))
  have hkappaHalf : kappa ≤ 1 / 2 := min_le_left _ _
  have hkappaEps : kappa ≤ eps / (2 * M) := min_le_right _ _
  have heta : 0 < eta := by
    dsimp [eta]
    exact div_pos (Real.rpow_pos_of_pos hkappa _) (by positivity)
  have hdelta : 0 < delta := div_pos heta hC
  refine ⟨delta, hdelta, ?_⟩
  intro t ht htdelta
  have hsdegree : s.natDegree ≤ d :=
    direction_natDegree_le_of_affine_natDegree hdegree
  have hcoeff : ∀ i : ℕ,
      ‖(r + t • s).coeff i - p₀.coeff i‖ < eta := by
    intro i
    have hle := norm_affine_pencil_coeff_sub_le (r := r) hsdegree t t₀ i
    dsimp [p₀] at hle
    have hdeltaC : delta * C = eta := by
      dsimp [delta]
      field_simp
    exact hle.trans_lt (by
      calc
        ‖t - t₀‖ * C < delta * C :=
          mul_lt_mul_of_pos_right htdelta hC
        _ = eta := hdeltaC)
  have hp₀monic : p₀.Monic := hmonic t₀ ht₀
  have hp₀real : RealRooted p₀ := hreal t₀ ht₀
  have hp₀deg : 0 < p₀.natDegree := by
    rw [hdegree t₀ ht₀]
    exact hd
  have htmonic : (r + t • s).Monic := hmonic t ht
  have htreal : RealRooted (r + t • s) := hreal t ht
  have htdegree : (r + t • s).natDegree = p₀.natDegree := by
    rw [hdegree t ht, hdegree t₀ ht₀]
  have hkformula :
      ((((p₀.natDegree + 1 : ℕ) : ℝ) * eta) ^
          (p₀.natDegree : ℝ)⁻¹) = kappa := by
    have hdcast : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hbase : (((p₀.natDegree + 1 : ℕ) : ℝ) * eta) =
        kappa ^ (d : ℝ) := by
      rw [show p₀.natDegree = d by exact hdegree t₀ ht₀]
      dsimp [eta]
      rw [Nat.cast_add, Nat.cast_one]
      field_simp
    rw [hbase, show p₀.natDegree = d by exact hdegree t₀ ht₀,
      ← Real.rpow_mul hkappa.le, mul_inv_cancel₀ hdcast, Real.rpow_one]
  have hk0 : 0 <
      ((((p₀.natDegree + 1 : ℕ) : ℝ) * eta) ^
        (p₀.natDegree : ℝ)⁻¹) := by rw [hkformula]; exact hkappa
  have hk1 :
      ((((p₀.natDegree + 1 : ℕ) : ℝ) * eta) ^
        (p₀.natDegree : ℝ)⁻¹) < 1 := by
    rw [hkformula]
    linarith
  have hroot := norm_largestRealRoot_sub_lt_of_norm_coeff_sub_lt
    hp₀monic htmonic hp₀real htreal htdegree hp₀deg heta hcoeff hk0 hk1
  rw [hkformula] at hroot
  have hden : 1 / 2 ≤ 1 - kappa := by linarith
  have htarget : kappa * M / (1 - kappa) ≤ eps := by
    have hkm : kappa * M ≤ eps / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * M)] at hkappaEps
      nlinarith
    rw [div_le_iff₀ (by linarith : 0 < 1 - kappa)]
    nlinarith
  simpa [p₀, norm_sub_rev] using hroot.trans_le htarget

/-- The largest-root function of the pencil, defined on the nonnegative
parameter subtype. -/
noncomputable def affineLargestRoot
    (d : ℕ) (r s : ℝ[X]) (hd : 0 < d)
    (hdegree : ∀ t : ℝ, 0 ≤ t → (r + t • s).natDegree = d)
    (hreal : ∀ t : ℝ, 0 ≤ t → RealRooted (r + t • s))
    (t : Set.Ici (0 : ℝ)) : ℝ :=
  largestRealRoot (r + (t : ℝ) • s) (hreal t t.property)
    (by rw [hdegree t t.property]; exact hd)

/-- Bundled continuity of the largest root on the nonnegative half-line. -/
theorem continuous_affineLargestRoot
    (d : ℕ) (r s : ℝ[X]) (hd : 0 < d)
    (hmonic : ∀ t : ℝ, 0 ≤ t → (r + t • s).Monic)
    (hdegree : ∀ t : ℝ, 0 ≤ t → (r + t • s).natDegree = d)
    (hreal : ∀ t : ℝ, 0 ≤ t → RealRooted (r + t • s)) :
    Continuous (affineLargestRoot d r s hd hdegree hreal) := by
  rw [Metric.continuous_iff]
  intro t₀ eps heps
  obtain ⟨delta, hdelta, hclose⟩ :=
    exists_delta_largestRealRoot_affine d r s hd hmonic hdegree hreal
      t₀.property heps
  refine ⟨delta, hdelta, ?_⟩
  intro t ht
  have ht' : ‖(t : ℝ) - (t₀ : ℝ)‖ < delta := by
    simpa [Real.dist_eq] using ht
  have := hclose t t.property ht'
  simpa [affineLargestRoot, Real.dist_eq] using this

/-- Two distinct members of an affine pencil can share a root only when
that point is a root of both the base and direction polynomials. -/
theorem common_root_of_affine_pencil
    {r s : ℝ[X]} {u v a : ℝ} (huv : u ≠ v)
    (hu : (r + u • s).IsRoot a) (hv : (r + v • s).IsRoot a) :
    r.IsRoot a ∧ s.IsRoot a := by
  rw [IsRoot] at hu hv ⊢
  simp only [eval_add, eval_smul, smul_eq_mul] at hu hv
  have hs : s.eval a = 0 := by
    have huv' : u - v ≠ 0 := sub_ne_zero.mpr huv
    apply (mul_eq_zero.mp ?_).resolve_left huv'
    calc
      (u - v) * s.eval a =
          (r.eval a + u * s.eval a) -
            (r.eval a + v * s.eval a) := by ring
      _ = 0 := by rw [hu, hv, sub_self]
  exact ⟨by simpa [hs] using hu, hs⟩

/-- If a root occurs at two distinct parameters, it is fixed throughout the
entire affine pencil. -/
theorem root_all_parameters_of_root_two_parameters
    {r s : ℝ[X]} {u v a : ℝ} (huv : u ≠ v)
    (hu : (r + u • s).IsRoot a) (hv : (r + v • s).IsRoot a) :
    ∀ t : ℝ, (r + t • s).IsRoot a := by
  obtain ⟨hr, hs⟩ := common_root_of_affine_pencil huv hu hv
  intro t
  rw [IsRoot] at hr hs ⊢
  simp [hr, hs]

/-- The general affine-pencil root-motion theorem.  Moment escape supplies a
later parameter whose largest root is above the initial largest root.
Continuity then gives a repeated largest-root value; affine algebra makes
that root fixed throughout the pencil, contradicting a decrease at `t = 1`. -/
theorem affineRealRootedPencilLargestRootMonotoneFromMoment :
    CommutatorTheorem.BTMDPJointControl.AffineRealRootedPencilLargestRootMonotoneFromMoment := by
  intro d r s hd hmonic hdegree hreal hnext hslope x hx
  have hdpos : 0 < d := by omega
  have hrreal : RealRooted r := by simpa using hreal 0 le_rfl
  have hrdegree : r.natDegree = d := by simpa using hdegree 0 le_rfl
  have hrdegpos : 0 < r.natDegree := by omega
  let a₀ := largestRealRoot r hrreal hrdegpos
  have ha₀root : r.IsRoot a₀ := largestRealRoot_isRoot r hrreal hrdegpos
  by_contra hgoal
  have hxa₀ : x < a₀ := by
    rw [IsRootUpperBound] at hgoal
    push Not at hgoal
    obtain ⟨a, haroot, hxa⟩ := hgoal
    exact hxa.trans_le (root_le_largestRealRoot r hrreal hrdegpos haroot)
  let p₁ := r + (1 : ℝ) • s
  have hp₁real : RealRooted p₁ := hreal 1 zero_le_one
  have hp₁deg : 0 < p₁.natDegree := by
    rw [hdegree 1 zero_le_one]
    exact hdpos
  let a₁ := largestRealRoot p₁ hp₁real hp₁deg
  have ha₁x : a₁ ≤ x := by
    apply hx
    dsimp [a₁]
    simpa [p₁] using largestRealRoot_isRoot p₁ hp₁real hp₁deg
  have ha₁a₀ : a₁ < a₀ := ha₁x.trans_lt hxa₀
  obtain ⟨T, hT1, hTnot⟩ :=
    CommutatorTheorem.BTMDPJointControl.exists_parameter_not_rootUpperBound_of_coeff_sub_two_neg
        d r s hd hmonic hdegree hreal hnext hslope a₀
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  have hpTreal : RealRooted (r + T • s) := hreal T hT0
  have hpTdeg : 0 < (r + T • s).natDegree := by
    rw [hdegree T hT0]
    exact hdpos
  let aT := largestRealRoot (r + T • s) hpTreal hpTdeg
  have ha₀aT : a₀ < aT := by
    rw [isRootUpperBound_iff_largestRealRoot_le
      (r + T • s) hpTreal hpTdeg a₀] at hTnot
    exact lt_of_not_ge hTnot
  let L := affineLargestRoot d r s hdpos hdegree hreal
  have hLcont : Continuous L :=
    continuous_affineLargestRoot d r s hdpos hmonic hdegree hreal
  let F : ℝ → ℝ := fun t ↦ L ⟨max 0 t, le_max_left 0 t⟩
  have hFcont : Continuous F := by
    apply hLcont.comp
    exact (continuous_const.max continuous_id).subtype_mk _
  have hF₁ : F 1 = a₁ := by
    simp [F, L, a₁, p₁, affineLargestRoot]
  have hFT : F T = aT := by
    simp [F, L, aT, affineLargestRoot, hT0]
  have ha₀mem : a₀ ∈ Set.Icc (F 1) (F T) := by
    rw [hF₁, hFT]
    exact ⟨ha₁a₀.le, ha₀aT.le⟩
  have hiv := intermediate_value_Icc hT1 hFcont.continuousOn ha₀mem
  obtain ⟨u, hu, hFu⟩ := hiv
  have hu1 : 1 ≤ u := hu.1
  have hu0 : 0 ≤ u := zero_le_one.trans hu1
  have huNe : u ≠ 0 := ne_of_gt (zero_lt_one.trans_le hu1)
  have huroot : (r + u • s).IsRoot a₀ := by
    have hlarge := largestRealRoot_isRoot (r + u • s)
      (hreal u hu0) (by rw [hdegree u hu0]; exact hdpos)
    have heq : largestRealRoot (r + u • s) (hreal u hu0)
        (by rw [hdegree u hu0]; exact hdpos) = a₀ := by
      simpa [F, L, affineLargestRoot, hu0] using hFu
    rwa [heq] at hlarge
  have hfixed := root_all_parameters_of_root_two_parameters
    huNe.symm (by simpa using ha₀root) huroot
  have ha₀rootOne : p₁.IsRoot a₀ := by
    simpa [p₁] using hfixed 1
  have ha₀le : a₀ ≤ a₁ :=
    root_le_largestRealRoot p₁ hp₁real hp₁deg ha₀rootOne
  exact (not_le_of_gt ha₁a₀) ha₀le

end CommutatorTheorem.BTRootMotionContinuity
