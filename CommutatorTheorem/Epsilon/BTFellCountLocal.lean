import CommutatorTheorem.Epsilon.BTFellSignLocal

/-!
# Local constancy of half-line root counts in a Fell pencil
-/

open scoped Polynomial Topology

namespace CommutatorTheorem.BTFellCountLocal

open Polynomial Set Filter
open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTFellCrossGap
open CommutatorTheorem.BTFellExactDescartes
open CommutatorTheorem.BTFellCountParity
open CommutatorTheorem.BTFellSignLocal

private noncomputable def pencil (p q : ℝ[X]) (t : ℝ) : ℝ[X] :=
  t • p + (1 - t) • q

/-- Near a parameter where `x` is not a root, the exact number of roots to
the right of `x` is constant within the real-rooted pencil interval. -/
theorem eventually_rootsGTCount_eq
    {p q : ℝ[X]} {d : ℕ}
    (hp : p.Monic) (hq : q.Monic)
    (hpdegree : p.natDegree = d) (hqdegree : q.natDegree = d)
    (hall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → RealRooted (pencil p q t))
    {t₀ x : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hroot : ¬(pencil p q t₀).IsRoot x) :
    ∀ᶠ t in 𝓝[Icc (0 : ℝ) 1] t₀,
      rootsGTCount (pencil p q t) x = rootsGTCount (pencil p q t₀) x := by
  let P : ℝ → ℝ[X] := fun t => (pencil p q t).taylor x
  have hP : ∀ t : ℝ, P t =
      t • p.taylor x + (1 - t) • q.taylor x := by
    intro t
    exact taylor_convex p q t x
  have hsignNhds : ∀ᶠ t in 𝓝 t₀, ∀ i ∈ Finset.range (d + 1),
      SignType.sign ((P t₀).coeff i) = 0 ∨
        SignType.sign ((P t₀).coeff i) = SignType.sign ((P t).coeff i) := by
    rw [Filter.eventually_all_finset]
    intro i hi
    by_cases hzero : (P t₀).coeff i = 0
    · exact Filter.Eventually.of_forall fun t => Or.inl (by simp [hzero])
    · have hcont : ContinuousAt (fun t => (P t).coeff i) t₀ := by
        simp only [hP, coeff_add, coeff_smul]
        fun_prop
      rcases lt_or_gt_of_ne hzero with hneg | hpos
      · have hev : ∀ᶠ t in 𝓝 t₀, (P t).coeff i < 0 :=
          hcont (isOpen_Iio.mem_nhds hneg)
        filter_upwards [hev] with t ht
        right
        simp [sign_apply, hneg, ht]
      · have hev : ∀ᶠ t in 𝓝 t₀, 0 < (P t).coeff i :=
          hcont (isOpen_Ioi.mem_nhds hpos)
        filter_upwards [hev] with t ht
        right
        simp [sign_apply, hpos, ht]
  filter_upwards [hsignNhds.filter_mono inf_le_left,
    self_mem_nhdsWithin] with t hsign ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hmonic₀ : (pencil p q t₀).Monic :=
    monic_convex_combination_of_same_natDegree hp hq hpdegree hqdegree t₀
  have hmonic : (pencil p q t).Monic :=
    monic_convex_combination_of_same_natDegree hp hq hpdegree hqdegree t
  have hreal₀ := hall t₀ ht₀.1 ht₀.2
  have hreal := hall t ht0 ht1
  have hdegreePencil : ∀ u : ℝ, (pencil p q u).natDegree = d := by
    intro u
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact (natDegree_add_le _ _).trans
        (max_le ((natDegree_smul_le u p).trans hpdegree.le)
          ((natDegree_smul_le (1 - u) q).trans hqdegree.le))
    · have hpc : p.coeff d = 1 := by
        rw [← hpdegree]
        exact hp.coeff_natDegree
      have hqc : q.coeff d = 1 := by
        rw [← hqdegree]
        exact hq.coeff_natDegree
      simp [pencil, coeff_add, coeff_smul, hpc, hqc]
  have hdegree₀ : (P t₀).natDegree = d := by
    dsimp [P]
    rw [natDegree_taylor]
    exact hdegreePencil t₀
  have hdegree : (P t).natDegree = d := by
    dsimp [P]
    rw [natDegree_taylor]
    exact hdegreePencil t
  have hPmonic₀ : (P t₀).Monic := by
    dsimp [P]
    rw [Monic, leadingCoeff_taylor]
    exact hmonic₀
  have hPmonic : (P t).Monic := by
    dsimp [P]
    rw [Monic, leadingCoeff_taylor]
    exact hmonic
  have hPreal₀ : RealRooted (P t₀) := by
    dsimp [P]
    simpa [taylor_apply] using hreal₀.comp_X_add_C x
  have hPreal : RealRooted (P t) := by
    dsimp [P]
    simpa [taylor_apply] using hreal.comp_X_add_C x
  have hPzero₀ : ¬(P t₀).IsRoot 0 := by
    intro hz
    apply hroot
    rw [IsRoot] at hz ⊢
    have hzcoeff : (P t₀).coeff 0 = 0 := by
      simpa only [eval, eval₂_at_zero, RingHom.id_apply] using hz
    dsimp [P] at hzcoeff
    simpa only [taylor_coeff_zero] using hzcoeff
  have hsign' : ∀ i : ℕ, i ≤ (P t₀).natDegree →
      SignType.sign ((P t₀).coeff i) = 0 ∨
        SignType.sign ((P t₀).coeff i) = SignType.sign ((P t).coeff i) := by
    intro i hi
    apply hsign i
    simp only [Finset.mem_range]
    omega
  have hPzero : ¬(P t).IsRoot 0 := by
    intro hz
    have hzcoeff : (P t).coeff 0 = 0 := by
      simpa only [IsRoot, eval, eval₂_at_zero, RingHom.id_apply] using hz
    have hbase := hsign' 0 (by omega)
    rcases hbase with hbase | hbase
    · apply hPzero₀
      rw [IsRoot]
      have hc : (P t₀).coeff 0 = 0 := by simpa using hbase
      simpa only [eval, eval₂_at_zero, RingHom.id_apply] using hc
    · have : SignType.sign ((P t₀).coeff 0) = 0 := by simpa [hzcoeff] using hbase
      apply hPzero₀
      rw [IsRoot]
      have hc : (P t₀).coeff 0 = 0 := by simpa using this
      simpa only [eval, eval₂_at_zero, RingHom.id_apply] using hc
  have hvar := signVariations_eq_of_coeff_sign_preserved
    hPmonic₀ hPmonic hPreal₀ hPreal (hdegree₀.trans hdegree.symm)
    hPzero₀ hPzero hsign'
  rw [rootsGTCount_eq_signVariations_taylor hmonic hreal x,
    rootsGTCount_eq_signVariations_taylor hmonic₀ hreal₀ x]
  simpa [P] using hvar.symm

end CommutatorTheorem.BTFellCountLocal
