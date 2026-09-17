import CommutatorTheorem.NoEpsilon.MSSBarrierStep

/-!
# Finite iteration of the quantitative MSS barrier step
-/

namespace NoEpsilon.MSSBarrierIteration

open NoEpsilon.MSSStability NoEpsilon.MSSBarrier NoEpsilon.MSSBarrierStep
open scoped BigOperators

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedFintypeInType false in
theorem realStable_sub_pderiv {p : MvPolynomial σ ℝ} (hp : RealStable p) (i : σ) :
    RealStable (p - MvPolynomial.pderiv i p) := by
  change UpperStable ((p - MvPolynomial.pderiv i p).map Complex.ofRealHom)
  simpa only [map_sub, MvPolynomial.pderiv_map] using hp.sub_pderiv i

noncomputable def advance (z : σ → ℝ) (δ : ℝ) (xs : List σ) : σ → ℝ :=
  xs.foldl (fun w i ↦ coordinateShift w i δ) z

omit [Fintype σ] in
/-- When a coordinate list has no repetitions, its successive shifts are exactly
one shift at each listed coordinate. -/
theorem advance_eq_of_nodup (z : σ → ℝ) (δ : ℝ) (xs : List σ) (hxs : xs.Nodup) :
    advance z δ xs = fun k ↦ z k + if k ∈ xs then δ else 0 := by
  induction xs generalizing z with
  | nil => simp [advance]
  | cons j xs ih =>
    have hj : j ∉ xs := (List.nodup_cons.mp hxs).1
    have hs : xs.Nodup := (List.nodup_cons.mp hxs).2
    change advance (coordinateShift z j δ) δ xs = _
    rw [ih _ hs]
    funext k
    by_cases hkj : k = j
    · subst k
      simp [coordinateShift, hj]
    · simp [coordinateShift, hkj]

omit [Fintype σ] in
/-- No coordinate moves by more than `δ` in a list with no repetitions. -/
theorem advance_le_uniform (t δ : ℝ) (hδ : 0 ≤ δ) (xs : List σ) (hxs : xs.Nodup) :
    advance (fun _ : σ ↦ t) δ xs ≤ fun _ ↦ t + δ := by
  rw [advance_eq_of_nodup _ _ _ hxs]
  intro k
  by_cases hk : k ∈ xs <;> simp [hk, hδ]

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedFintypeInType false in
/-- Finite iteration preserves all barrier bounds, with the point shifted in
the same order as the polynomial difference operators. -/
theorem iterate_quantitative_barrier {p : MvPolynomial σ ℝ} (hp : RealStable p)
    {z : σ → ℝ} (hz : AboveRoots p z) (δ φ : ℝ) (hδ : 0 < δ)
    (hφ : φ ≤ 1 - 1 / δ) (hb : ∀ i : σ, barrier p i z ≤ φ) (xs : List σ) :
    RealStable (xs.foldl (fun q i ↦ q - MvPolynomial.pderiv i q) p) ∧
      AboveRoots (xs.foldl (fun q i ↦ q - MvPolynomial.pderiv i q) p) (advance z δ xs) ∧
      ∀ i : σ, barrier (xs.foldl (fun q j ↦ q - MvPolynomial.pderiv j q) p)
        i (advance z δ xs) ≤ φ := by
  induction xs generalizing p z with
  | nil => exact ⟨hp, hz, hb⟩
  | cons j xs ih =>
    have hstep := quantitative_barrier_step hp hz j δ hδ ((hb j).trans hφ)
    have hp' := realStable_sub_pderiv hp j
    have hb' : ∀ i : σ,
        barrier (p - MvPolynomial.pderiv j p) i (coordinateShift z j δ) ≤ φ :=
      fun i ↦ (hstep.2 i).trans (hb i)
    simpa only [List.foldl_cons, advance] using ih hp' hstep.1 hb'

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- Applying any list of distinct MSS operators moves a uniform upper-root
barrier by at most one coordinate shift, independently of the list length. -/
theorem aboveRoots_fold_uniform {p : MvPolynomial σ ℝ} (hp : RealStable p)
    (t δ φ : ℝ) (hz : AboveRoots p (fun _ : σ ↦ t)) (hδ : 0 < δ)
    (hφ : φ ≤ 1 - 1 / δ) (hb : ∀ i : σ, barrier p i (fun _ : σ ↦ t) ≤ φ)
    (xs : List σ) (hxs : xs.Nodup) :
    AboveRoots (xs.foldl (fun q i ↦ q - MvPolynomial.pderiv i q) p)
      (fun _ : σ ↦ t + δ) := by
  have hi := iterate_quantitative_barrier hp hz δ φ hδ hφ hb xs
  exact hi.2.1.mono (advance_le_uniform t δ hδ.le xs hxs)

/-- The MSS optimized parameters satisfy the quantitative step condition. -/
theorem optimized_parameters {ε : ℝ} (hε : 0 < ε) :
    0 < ε + Real.sqrt ε ∧ 0 < 1 + Real.sqrt ε ∧
      ε / (ε + Real.sqrt ε) = 1 - 1 / (1 + Real.sqrt ε) ∧
      ε + Real.sqrt ε + (1 + Real.sqrt ε) = (1 + Real.sqrt ε)^2 := by
  have hs := Real.sqrt_nonneg ε
  have hs2 := Real.sq_sqrt hε.le
  have ht : 0 < ε + Real.sqrt ε := by positivity
  have hd : 0 < 1 + Real.sqrt ε := by positivity
  refine ⟨ht, hd, ?_, ?_⟩
  · field_simp
    nlinarith
  · nlinarith

-- Preserve the existing parameter list for downstream callers.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- The optimized MSS bound for any real stable polynomial satisfying the
explicit initial above-roots and trace-sized barrier estimates. -/
theorem aboveRoots_fold_optimized {p : MvPolynomial σ ℝ} (hp : RealStable p)
    (ε : ℝ) (hε : 0 < ε)
    (hz : AboveRoots p (fun _ : σ ↦ ε + Real.sqrt ε))
    (hb : ∀ i : σ, barrier p i (fun _ : σ ↦ ε + Real.sqrt ε) ≤
      ε / (ε + Real.sqrt ε))
    (xs : List σ) (hxs : xs.Nodup) :
    AboveRoots (xs.foldl (fun q i ↦ q - MvPolynomial.pderiv i q) p)
      (fun _ : σ ↦ (1 + Real.sqrt ε)^2) := by
  have hopt := optimized_parameters hε
  have hi := aboveRoots_fold_uniform hp (ε + Real.sqrt ε) (1 + Real.sqrt ε)
    (ε / (ε + Real.sqrt ε)) hz hopt.2.1 hopt.2.2.1.le hb xs hxs
  simpa only [hopt.2.2.2] using hi

end NoEpsilon.MSSBarrierIteration
