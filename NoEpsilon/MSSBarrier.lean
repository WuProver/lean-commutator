import NoEpsilon.MSSStability
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Analytic ingredients of the MSS multivariate barrier argument

The upper-half-plane signs below are derived from stability. In particular, they
are not supplied as barrier monotonicity assumptions. The final quantitative
shift theorem will use the mixed derivative signs proved in this file.
-/

namespace NoEpsilon.MSSBarrier

open NoEpsilon.MSSStability Polynomial Filter
open scoped BigOperators Topology

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def coordinateShift {R : Type*} [Add R] [Zero R]
    (z : σ → R) (j : σ) (t : R) : σ → R :=
  fun i ↦ z i + if i = j then t else 0

omit [Fintype σ] in
@[simp] theorem coordinateShift_zero {R : Type*} [AddZeroClass R]
    (z : σ → R) (j : σ) : coordinateShift z j 0 = z := by
  funext i
  simp [coordinateShift]

/-- The coordinate logarithmic derivative at a point of the open upper orthant
has nonpositive imaginary part. -/
theorem logDerivative_im_nonpos {p : MvPolynomial σ ℂ} (hp : UpperStable p)
    (z : σ → ℂ) (hz : ∀ i, InUpperHalfPlane (z i)) (j : σ) :
    (MvPolynomial.eval z (MvPolynomial.pderiv j p) / MvPolynomial.eval z p).im ≤ 0 := by
  let w : σ → ℝ := fun i ↦ if i = j then 1 else 0
  let f := stableLinePolynomial z w p
  have hf0 : f.eval 0 ≠ 0 := by
    rw [eval_stableLinePolynomial]
    simpa using hp z hz
  have hfne : f ≠ 0 := fun h ↦ hf0 (by rw [h]; simp)
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; split_ifs <;> norm_num
  have hsum : (f.derivative.eval 0 / f.eval 0).im ≤ 0 := by
    rw [(IsAlgClosed.splits f).eval_derivative_div_eval_of_ne_zero hf0]
    have him : ∀ s : Multiset ℂ, s.sum.im = (s.map Complex.im).sum := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a s ih => simp [ih, Complex.add_im]
    rw [him, Multiset.map_map]
    apply (Multiset.sum_le_card_nsmul _ 0 ?_).trans (by simp)
    intro y hy
    obtain ⟨a, ha, heq⟩ := Multiset.mem_map.mp hy
    rw [← heq]
    exact (one_div_neg_im_neg
      (root_im_neg_of_stableLinePolynomial hp z w hz hw
        ((Polynomial.mem_roots hfne).mp ha))).le
  simpa [f, derivative_stableLinePolynomial_eval_zero, eval_stableLinePolynomial,
    nonnegativeDirectionalDerivative, w, apply_ite] using hsum

/-- The same sign extends to boundary points, provided the denominator does
not vanish. This only uses continuity, not an assumed specialization theorem. -/
theorem logDerivative_im_nonpos_closed {p : MvPolynomial σ ℂ} (hp : UpperStable p)
    (z : σ → ℂ) (hz : ∀ i, 0 ≤ (z i).im) (hzero : MvPolynomial.eval z p ≠ 0)
    (j : σ) :
    (MvPolynomial.eval z (MvPolynomial.pderiv j p) / MvPolynomial.eval z p).im ≤ 0 := by
  let zt : ℝ → σ → ℂ := fun t i ↦ z i + Complex.I * (t : ℂ)
  have hzt : Continuous zt := by unfold zt; fun_prop
  have hlim : Tendsto (fun t : ℝ ↦
      (MvPolynomial.eval (zt t) (MvPolynomial.pderiv j p) /
        MvPolynomial.eval (zt t) p).im) (𝓝[>] 0)
      (𝓝 (MvPolynomial.eval z (MvPolynomial.pderiv j p) /
        MvPolynomial.eval z p).im) := by
    have hz0 : zt 0 = z := by ext i; simp [zt]
    have hc : ContinuousAt (fun t : ℝ ↦
        MvPolynomial.eval (zt t) (MvPolynomial.pderiv j p) /
          MvPolynomial.eval (zt t) p) 0 :=
      ((MvPolynomial.pderiv j p).continuous_eval.comp hzt).continuousAt.div
        (p.continuous_eval.comp hzt).continuousAt (by rw [hz0]; exact hzero)
    have hi := Complex.continuous_im.continuousAt.comp hc
    simpa [hz0] using hi.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply logDerivative_im_nonpos hp (zt t) _ j
  intro i
  simpa [zt, InUpperHalfPlane] using add_pos_of_nonneg_of_pos (hz i) ht

/-- Differentiating a coordinate restriction at its base point evaluates the
corresponding polynomial partial derivative. -/
theorem hasDerivAt_coordinateEval_zero (p : MvPolynomial σ ℂ) (z : σ → ℂ) (j : σ) :
    HasDerivAt (fun t ↦ MvPolynomial.eval (coordinateShift z j t) p)
      (MvPolynomial.eval z (MvPolynomial.pderiv j p)) 0 := by
  let w : σ → ℝ := fun i ↦ if i = j then 1 else 0
  have h := (stableLinePolynomial z w p).hasDerivAt 0
  have heq : (fun t ↦ (stableLinePolynomial z w p).eval t) =
      (fun t ↦ MvPolynomial.eval (coordinateShift z j t) p) := by
    funext t
    rw [eval_stableLinePolynomial]
    apply congrArg (fun zz ↦ MvPolynomial.eval zz p)
    funext i
    by_cases hi : i = j <;> simp [w, coordinateShift, hi]
  rw [heq] at h
  simpa [derivative_stableLinePolynomial_eval_zero, nonnegativeDirectionalDerivative,
    w, apply_ite] using h

/-- A holomorphic function with nonpositive imaginary part immediately above
a real boundary value has nonpositive real derivative there. -/
theorem boundary_derivative_re_nonpos {f : ℂ → ℂ} {f' : ℂ}
    (hf : HasDerivAt f f' 0) (hreal : (f 0).im = 0)
    (hsign : ∀ᶠ t : ℝ in 𝓝[>] 0, (f (Complex.I * (t : ℂ))).im ≤ 0) :
    f'.re ≤ 0 := by
  have hcomp : HasDerivAt (fun z : ℂ ↦ -Complex.I * f (Complex.I * z)) f' 0 := by
    have hin : HasDerivAt (fun z : ℂ ↦ Complex.I * z) Complex.I 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul Complex.I
    have hf₁ : HasDerivAt f f' (Complex.I * (0 : ℂ)) := by simpa using hf
    convert (hf₁.comp 0 hin).const_mul (-Complex.I) using 1
    calc
      f' = -(f' * (Complex.I * Complex.I)) := by simp
      _ = -Complex.I * (f' * Complex.I) := by ring
  have hder : HasDerivAt (fun t : ℝ ↦ (f (Complex.I * (t : ℂ))).im) f'.re 0 := by
    simpa [Complex.mul_re] using hcomp.real_of_complex
  apply le_of_tendsto hder.tendsto_slope_zero_right
  filter_upwards [hsign, self_mem_nhdsWithin] with t ht htpos
  simpa [hreal] using mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr htpos.le) ht

/-- Real stability is the semantic stability of the polynomial after the real
coefficient inclusion. -/
def RealStable (p : MvPolynomial σ ℝ) : Prop :=
  UpperStable (p.map Complex.ofRealHom)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem eval₂_ofReal (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun i ↦ (z i : ℂ)) p =
      (MvPolynomial.eval z p : ℂ) :=
  (MvPolynomial.eval₂_comp Complex.ofRealHom z p).symm

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem eval_complexification (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    MvPolynomial.eval (fun i ↦ (z i : ℂ)) (p.map Complex.ofRealHom) =
      (MvPolynomial.eval z p : ℂ) := by
  rw [MvPolynomial.eval_map, eval₂_ofReal]

noncomputable def barrier (p : MvPolynomial σ ℝ) (i : σ) (z : σ → ℝ) : ℝ :=
  MvPolynomial.eval z (MvPolynomial.pderiv i p) / MvPolynomial.eval z p

noncomputable def mixedBarrierDerivative (p : MvPolynomial σ ℝ)
    (i j : σ) (z : σ → ℝ) : ℝ :=
  (MvPolynomial.eval z (MvPolynomial.pderiv j (MvPolynomial.pderiv i p)) *
      MvPolynomial.eval z p - MvPolynomial.eval z (MvPolynomial.pderiv i p) *
      MvPolynomial.eval z (MvPolynomial.pderiv j p)) / (MvPolynomial.eval z p)^2

/-- The mixed logarithmic derivative of a real stable polynomial is nonpositive
at every real point where the polynomial is nonzero. This is the Rayleigh
inequality, proved here from upper-half-plane stability and a boundary limit. -/
theorem mixedBarrierDerivative_nonpos {p : MvPolynomial σ ℝ} (hp : RealStable p)
    (z : σ → ℝ) (hzero : MvPolynomial.eval z p ≠ 0) (i j : σ) :
    mixedBarrierDerivative p i j z ≤ 0 := by
  let q := p.map Complex.ofRealHom
  let zz : σ → ℂ := fun k ↦ (z k : ℂ)
  let f : ℂ → ℂ := fun t ↦
    MvPolynomial.eval (coordinateShift zz j t) (MvPolynomial.pderiv i q) /
      MvPolynomial.eval (coordinateShift zz j t) q
  have hqzero : MvPolynomial.eval zz q ≠ 0 := by
    simpa [zz, q] using (Complex.ofReal_ne_zero.mpr hzero)
  have hf : HasDerivAt f (mixedBarrierDerivative p i j z : ℂ) 0 := by
    have hh := (hasDerivAt_coordinateEval_zero (MvPolynomial.pderiv i q) zz j).div
      (hasDerivAt_coordinateEval_zero q zz j) (by simpa using hqzero)
    simpa [f, mixedBarrierDerivative, q, zz, MvPolynomial.pderiv_map] using hh
  have hreal : (f 0).im = 0 := by
    simp [f, q, zz, MvPolynomial.pderiv_map]
  have hnz : ∀ᶠ t : ℝ in 𝓝[>] 0,
      MvPolynomial.eval (coordinateShift zz j (Complex.I * (t : ℂ))) q ≠ 0 := by
    have hc : Continuous (fun t : ℝ ↦
        MvPolynomial.eval (coordinateShift zz j (Complex.I * (t : ℂ))) q) := by
      apply q.continuous_eval.comp
      apply continuous_pi
      intro k
      by_cases hk : k = j <;> simp [coordinateShift, hk] <;> fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa using hqzero)).filter_mono
      nhdsWithin_le_nhds
  have hsign : ∀ᶠ t : ℝ in 𝓝[>] 0, (f (Complex.I * (t : ℂ))).im ≤ 0 := by
    filter_upwards [hnz, self_mem_nhdsWithin] with t ht htpos
    apply logDerivative_im_nonpos_closed hp _ _ ht i
    intro k
    change 0 < t at htpos
    by_cases hk : k = j <;> simp [coordinateShift, zz, hk, htpos.le]
  simpa using boundary_derivative_re_nonpos hf hreal hsign

omit [Fintype σ] in
@[simp] theorem coordinateShift_twice {R : Type*} [AddMonoid R]
    (z : σ → R) (j : σ) (a b : R) :
    coordinateShift (coordinateShift z j a) j b = coordinateShift z j (a + b) := by
  funext i
  by_cases hi : i = j <;> simp [coordinateShift, hi, add_assoc]

/-- The algebraic mixed derivative is the actual derivative of the real
coordinate barrier restriction. -/
theorem hasDerivAt_barrier_coordinate (p : MvPolynomial σ ℝ) (z : σ → ℝ)
    (i j : σ) (t : ℝ) (ht : MvPolynomial.eval (coordinateShift z j t) p ≠ 0) :
    HasDerivAt (fun s ↦ barrier p i (coordinateShift z j s))
      (mixedBarrierDerivative p i j (coordinateShift z j t)) t := by
  let q := p.map Complex.ofRealHom
  let zz : σ → ℂ := fun k ↦ (z k : ℂ)
  have hzc : coordinateShift zz j (t : ℂ) =
      (fun k ↦ (coordinateShift (R := ℝ) z j t k : ℂ)) := by
    funext k
    by_cases hk : k = j <;> simp [coordinateShift, zz, hk]
  have hzero : MvPolynomial.eval (coordinateShift zz j (t : ℂ)) q ≠ 0 := by
    rw [hzc]
    simpa [q] using Complex.ofReal_ne_zero.mpr ht
  have hh := (hasDerivAt_coordinateEval_zero (MvPolynomial.pderiv i q)
    (coordinateShift zz j (t : ℂ)) j).div
    (hasDerivAt_coordinateEval_zero q (coordinateShift zz j (t : ℂ)) j)
    (by simpa using hzero)
  have hin : HasDerivAt (fun s : ℂ ↦ s - (t : ℂ)) 1 (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).sub_const (t : ℂ)
  have hout : HasDerivAt
      (fun s : ℂ ↦ MvPolynomial.eval (coordinateShift zz j s) (MvPolynomial.pderiv i q) /
        MvPolynomial.eval (coordinateShift zz j s) q)
      (mixedBarrierDerivative p i j (coordinateShift z j t) : ℂ) (t : ℂ) := by
    have hh' := hh.comp_of_eq (t : ℂ) hin (by simp)
    simp only [Function.comp_def, Pi.div_apply, coordinateShift_twice] at hh'
    have hc : ∀ s : ℂ, (t : ℂ) + (s - (t : ℂ)) = s := fun s ↦ by ring
    simp only [hc] at hh'
    simpa [hzc, q, MvPolynomial.pderiv_map, mixedBarrierDerivative] using hh'
  have heq : (fun s : ℝ ↦
      (MvPolynomial.eval (coordinateShift zz j (s : ℂ)) (MvPolynomial.pderiv i q) /
        MvPolynomial.eval (coordinateShift zz j (s : ℂ)) q).re) =
      (fun s ↦ barrier p i (coordinateShift z j s)) := by
    funext s
    have hzs : coordinateShift zz j (s : ℂ) =
        (fun k ↦ (coordinateShift (R := ℝ) z j s k : ℂ)) := by
      funext k
      by_cases hk : k = j <;> simp [coordinateShift, zz, hk]
    simp [hzs, q, MvPolynomial.pderiv_map, barrier]
  simpa only [heq, Complex.ofReal_re] using hout.real_of_complex

/-- Positivity throughout the upper orthant, the MSS definition of being above
all roots. Using a pointwise order makes its upward closure explicit. -/
def AboveRoots (p : MvPolynomial σ ℝ) (z : σ → ℝ) : Prop :=
  ∀ y, z ≤ y → 0 < MvPolynomial.eval y p

omit [Fintype σ] [DecidableEq σ] in
theorem AboveRoots.eval_pos {p : MvPolynomial σ ℝ} {z : σ → ℝ}
    (hz : AboveRoots p z) : 0 < MvPolynomial.eval z p := hz z le_rfl

omit [Fintype σ] [DecidableEq σ] in
theorem AboveRoots.mono {p : MvPolynomial σ ℝ} {z y : σ → ℝ}
    (hz : AboveRoots p z) (hy : z ≤ y) : AboveRoots p y :=
  fun w hw ↦ hz w (hy.trans hw)

omit [Fintype σ] in
theorem le_coordinateShift (z : σ → ℝ) (j : σ) {t : ℝ} (ht : 0 ≤ t) :
    z ≤ coordinateShift z j t := by
  intro k
  by_cases hk : k = j <;> simp [coordinateShift, hk, ht]

/-- Coordinate monotonicity in MSS Lemma 5.7, proved from real stability. -/
theorem barrier_coordinate_antitone {p : MvPolynomial σ ℝ} (hp : RealStable p)
    {z : σ → ℝ} (hz : AboveRoots p z) (i j : σ) :
    AntitoneOn (fun t ↦ barrier p i (coordinateShift z j t)) (Set.Ici 0) := by
  have hd : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun s ↦ barrier p i (coordinateShift z j s))
        (mixedBarrierDerivative p i j (coordinateShift z j t)) t := by
    intro t ht
    exact hasDerivAt_barrier_coordinate p z i j t
      (hz _ (le_coordinateShift z j ht)).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  · exact fun t ht ↦ (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact mixedBarrierDerivative_nonpos hp _
      (hz _ (le_coordinateShift z j (interior_subset ht))).ne' i j

/-- The coordinate monotonicity extends to arbitrary increases of all variables. -/
theorem barrier_antitone_aboveRoots {p : MvPolynomial σ ℝ} (hp : RealStable p)
    {z y : σ → ℝ} (hz : AboveRoots p z) (hy : z ≤ y) (i : σ) :
    barrier p i y ≤ barrier p i z := by
  classical
  have hfin : ∀ s : Finset σ,
      barrier p i (fun k ↦ if k ∈ s then y k else z k) ≤ barrier p i z := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      let a : σ → ℝ := fun k ↦ if k ∈ s then y k else z k
      have hza : z ≤ a := by
        intro k
        dsimp [a]
        split_ifs <;> first | exact hy k | exact le_rfl
      have hs : coordinateShift a j (y j - z j) =
          (fun k ↦ if k ∈ insert j s then y k else z k) := by
        funext k
        by_cases hkj : k = j
        · subst k; simp [coordinateShift, a, hj]
        · simp [coordinateShift, a, hkj]
      have hm := barrier_coordinate_antitone hp (hz.mono hza) i j
        (show (0 : ℝ) ∈ Set.Ici 0 by simp)
        (show y j - z j ∈ Set.Ici 0 from sub_nonneg.mpr (hy j))
        (sub_nonneg.mpr (hy j))
      dsimp only at hm
      rw [coordinateShift_zero, hs] at hm
      exact hm.trans ih
  simpa using hfin Finset.univ

/-- MSS Lemma 5.9: a barrier below one keeps the entire upper orthant positive
under the operator `1 - ∂ᵢ`. -/
theorem aboveRoots_sub_pderiv {p : MvPolynomial σ ℝ} (hp : RealStable p)
    {z : σ → ℝ} (hz : AboveRoots p z) (i : σ) (hi : barrier p i z < 1) :
    AboveRoots (p - MvPolynomial.pderiv i p) z := by
  intro y hy
  have hpz := hz y hy
  have hb := (barrier_antitone_aboveRoots hp hz hy i).trans_lt hi
  rw [barrier, div_lt_one hpz] at hb
  simpa only [map_sub] using sub_pos.mpr hb

end NoEpsilon.MSSBarrier
