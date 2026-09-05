import CommutatorTheorem.Epsilon.BTCardTwo

/-!
# The cardinality-three elementary Bourgain--Tzafriri range

We average the Hilbert--Schmidt energy of the `3 × 3` zero-diagonal
compression over ordered triples of distinct coordinates.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing

namespace CommutatorTheorem

private abbrev TripleIndex (m : ℕ) := Σ _p : Fin m × Fin m, Fin m

private noncomputable def orderedTriples (m : ℕ) : Finset (TripleIndex m) :=
  (Finset.univ : Finset (Fin m)).offDiag.sigma fun p =>
    ((Finset.univ.erase p.1).erase p.2)

private noncomputable def tripleEnergy {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (q : TripleIndex m) : ℝ :=
  Complex.normSq (A q.1.1 q.1.2) + Complex.normSq (A q.1.2 q.1.1) +
  Complex.normSq (A q.1.1 q.2) + Complex.normSq (A q.2 q.1.1) +
  Complex.normSq (A q.1.2 q.2) + Complex.normSq (A q.2 q.1.2)

private lemma tripleEnergy_nonneg {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (q : TripleIndex m) :
    0 ≤ tripleEnergy A q := by
  have h₁ := Complex.normSq_nonneg (A q.1.1 q.1.2)
  have h₂ := Complex.normSq_nonneg (A q.1.2 q.1.1)
  have h₃ := Complex.normSq_nonneg (A q.1.1 q.2)
  have h₄ := Complex.normSq_nonneg (A q.2 q.1.1)
  have h₅ := Complex.normSq_nonneg (A q.1.2 q.2)
  have h₆ := Complex.normSq_nonneg (A q.2 q.1.2)
  change 0 ≤ Complex.normSq (A q.1.1 q.1.2) + Complex.normSq (A q.1.2 q.1.1) +
    Complex.normSq (A q.1.1 q.2) + Complex.normSq (A q.2 q.1.1) +
    Complex.normSq (A q.1.2 q.2) + Complex.normSq (A q.2 q.1.2)
  linarith

private lemma mem_orderedTriples {m : ℕ} {q : TripleIndex m} :
    q ∈ orderedTriples m ↔
      q.1.1 ≠ q.1.2 ∧ q.2 ≠ q.1.2 ∧ q.2 ≠ q.1.1 := by
  simp [orderedTriples]

private lemma orderedTriples_card (m : ℕ) :
    (orderedTriples m).card = (m * m - m) * (m - 2) := by
  rw [orderedTriples, Finset.card_sigma]
  have hleaf : ∀ p ∈ (Finset.univ : Finset (Fin m)).offDiag,
      (((Finset.univ.erase p.1).erase p.2).card) = m - 2 := by
    intro p hp
    have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    have hp2mem : p.2 ∈ (Finset.univ : Finset (Fin m)).erase p.1 := by
      simp [hpne.symm]
    rw [Finset.card_erase_of_mem hp2mem]
    simp
    omega
  calc
    (∑ p ∈ (Finset.univ : Finset (Fin m)).offDiag,
        ((Finset.univ.erase p.1).erase p.2).card)
        = ∑ _p ∈ (Finset.univ : Finset (Fin m)).offDiag, (m - 2) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hleaf p hp
    _ = (m * m - m) * (m - 2) := by simp [Finset.offDiag_card]

private lemma total_normSq_le_three {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    (∑ i : Fin m, ∑ j : Fin m, Complex.normSq (A i j)) ≤
      (m : ℝ) * ‖A‖ ^ 2 := by
  have hhs := hsNorm_le_sqrt_n_mul_opNorm A
  have hsq := pow_le_pow_left₀ (hsNorm_nonneg A) hhs 2
  have hsum_nonneg :
      0 ≤ ∑ i : Fin m, ∑ j : Fin m, Complex.normSq (A i j) := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hhs_sq :
      hsNorm A ^ 2 = ∑ i : Fin m, ∑ j : Fin m, Complex.normSq (A i j) := by
    unfold hsNorm
    rw [Real.sq_sqrt hsum_nonneg]
  rw [hhs_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at hsq
  simpa [mul_assoc] using hsq

private noncomputable def allTriples (m : ℕ) : Finset (TripleIndex m) :=
  ((Finset.univ : Finset (Fin m)) ×ˢ Finset.univ).sigma fun _ => Finset.univ

private lemma orderedTriples_subset_all (m : ℕ) :
    orderedTriples m ⊆ allTriples m := by
  intro q hq
  simp [allTriples, orderedTriples] at hq ⊢

private lemma allTriples_energy_sum {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) :
    (∑ q ∈ allTriples m, tripleEnergy A q) =
      6 * (m : ℝ) *
        (∑ i : Fin m, ∑ j : Fin m, Complex.normSq (A i j)) := by
  rw [allTriples, Finset.sum_sigma]
  rw [Finset.sum_product]
  simp only [tripleEnergy]
  simp_rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j : Fin m => Complex.normSq (A j i))]
  ring

private lemma orderedTriples_energy_sum_le {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) :
    (∑ q ∈ orderedTriples m, tripleEnergy A q) ≤
      6 * (m : ℝ) ^ 2 * ‖A‖ ^ 2 := by
  have hsubset := orderedTriples_subset_all m
  have hsubsum :
      (∑ q ∈ orderedTriples m, tripleEnergy A q) ≤
        ∑ q ∈ allTriples m, tripleEnergy A q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun q _ _ => tripleEnergy_nonneg A q)
  calc
    (∑ q ∈ orderedTriples m, tripleEnergy A q)
        ≤ ∑ q ∈ allTriples m, tripleEnergy A q := hsubsum
    _ = 6 * (m : ℝ) *
        (∑ i : Fin m, ∑ j : Fin m, Complex.normSq (A i j)) :=
          allTriples_energy_sum A
    _ ≤ 6 * (m : ℝ) * ((m : ℝ) * ‖A‖ ^ 2) := by
      gcongr
      exact total_normSq_le_three A
    _ = 6 * (m : ℝ) ^ 2 * ‖A‖ ^ 2 := by ring

private lemma exists_good_ordered_triple
    (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hfloor : ⌊ε ^ 2 * (m : ℝ)⌋₊ = 3) :
    ∃ q ∈ orderedTriples m, tripleEnergy A q ≤ (4 * ε * ‖A‖) ^ 2 := by
  have harg_nonneg : 0 ≤ ε ^ 2 * (m : ℝ) := by positivity
  have hthree_le_arg : (3 : ℝ) ≤ ε ^ 2 * (m : ℝ) := by
    have h := Nat.floor_le (R := ℝ) harg_nonneg
    rw [hfloor] at h
    exact_mod_cast h
  have hm4 : 4 ≤ m := by
    by_contra hm
    have hm_le : m ≤ 3 := by omega
    have hmR : (m : ℝ) ≤ 3 := by exact_mod_cast hm_le
    have hεsq : ε ^ 2 < 1 := by nlinarith
    nlinarith
  let S : Finset (TripleIndex m) := orderedTriples m
  have hSnonempty : S.Nonempty := by
    let q : TripleIndex m := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ⟨2, by omega⟩⟩
    refine ⟨q, ?_⟩
    rw [mem_orderedTriples]
    simp [q]
  have hcardS : S.card = (m * m - m) * (m - 2) := by
    simpa [S] using orderedTriples_card m
  have hcard_cast :
      ((S.card : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) := by
    rw [hcardS]
    have hm_le_mm : m ≤ m * m := by nlinarith
    have h2m : 2 ≤ m := by omega
    rw [Nat.cast_mul, Nat.cast_sub hm_le_mm, Nat.cast_mul, Nat.cast_sub h2m]
    ring
  have hcoef :
      6 * (m : ℝ) ^ 2 ≤ (S.card : ℝ) * (16 * ε ^ 2) := by
    rw [hcard_cast]
    have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm4
    nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : (1 : ℝ) ≤ m))
      (sub_nonneg.mpr (by linarith : (2 : ℝ) ≤ m))]
  have hsum_bound :
      (∑ q ∈ S, tripleEnergy A q) ≤
        ∑ _q ∈ S, (4 * ε * ‖A‖) ^ 2 := by
    calc
      (∑ q ∈ S, tripleEnergy A q)
          ≤ 6 * (m : ℝ) ^ 2 * ‖A‖ ^ 2 := by
            simpa [S] using orderedTriples_energy_sum_le A
      _ ≤ ((S.card : ℝ) * (16 * ε ^ 2)) * ‖A‖ ^ 2 := by
            gcongr
      _ = ∑ _q ∈ S, (4 * ε * ‖A‖) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
  obtain ⟨q, hqS, hq⟩ := Finset.exists_le_of_sum_le hSnonempty hsum_bound
  exact ⟨q, by simpa [S] using hqS, hq⟩

private def tripleEmbedding {m : ℕ} (q : TripleIndex m) : Fin 3 → Fin m :=
  fun i => if i = 0 then q.1.1 else if i = 1 then q.1.2 else q.2

@[simp] private lemma tripleEmbedding_zero {m : ℕ} (q : TripleIndex m) :
    tripleEmbedding q 0 = q.1.1 := by simp [tripleEmbedding]

@[simp] private lemma tripleEmbedding_one {m : ℕ} (q : TripleIndex m) :
    tripleEmbedding q 1 = q.1.2 := by simp [tripleEmbedding]

@[simp] private lemma tripleEmbedding_two {m : ℕ} (q : TripleIndex m) :
    tripleEmbedding q 2 = q.2 := by simp [tripleEmbedding]

private lemma tripleEmbedding_injective {m : ℕ} {q : TripleIndex m}
    (hq : q ∈ orderedTriples m) : Function.Injective (tripleEmbedding q) := by
  rw [mem_orderedTriples] at hq
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- The central-submatrix estimate with constant `4` when the requested
cardinality is exactly three. -/
theorem central_submatrix_card_eq_three
    (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) (hzd : ZeroDiag A)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hcard : ⌊ε ^ 2 * (m : ℝ)⌋₊ = 3) :
    ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
      Function.Injective f ∧
      ‖A.submatrix f f‖ ≤ 4 * ε * ‖A‖ := by
  obtain ⟨q, hq, hqEnergy⟩ := exists_good_ordered_triple m A ε hε hε' hcard
  rw [hcard]
  let f : Fin 3 → Fin m := tripleEmbedding q
  have hf : Function.Injective f := tripleEmbedding_injective hq
  refine ⟨f, hf, ?_⟩
  set B : Matrix (Fin 3) (Fin 3) ℂ := A.submatrix f f with hB
  have hsum :
      (∑ i : Fin 3, ∑ j : Fin 3, Complex.normSq (B i j)) = tripleEnergy A q := by
    rw [hB]
    simp [Fin.sum_univ_succ, f, tripleEnergy,
      hzd q.1.1, hzd q.1.2, hzd q.2]
    ring
  have hsum_nonneg :
      0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, Complex.normSq (B i j) := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hhs_sq : hsNorm B ^ 2 = tripleEnergy A q := by
    unfold hsNorm
    rw [Real.sq_sqrt hsum_nonneg, hsum]
  have hhs_bound : hsNorm B ≤ 4 * ε * ‖A‖ := by
    apply le_of_sq_le_sq
    · rw [hhs_sq]
      exact hqEnergy
    · positivity
  calc
    ‖A.submatrix f f‖ = ‖B‖ := by rw [hB]
    _ ≤ hsNorm B := le_hsNorm B
    _ ≤ 4 * ε * ‖A‖ := hhs_bound

/-- The cardinality-at-most-three range, with the uniform explicit constant `4`. -/
theorem central_submatrix_card_le_three
    (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) (hzd : ZeroDiag A)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hcard : ⌊ε ^ 2 * (m : ℝ)⌋₊ ≤ 3) :
    ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
      Function.Injective f ∧
      ‖A.submatrix f f‖ ≤ 4 * ε * ‖A‖ := by
  by_cases htwo : ⌊ε ^ 2 * (m : ℝ)⌋₊ ≤ 2
  · obtain ⟨f, hf, hb⟩ := central_submatrix_card_le_two m A hzd ε hε hε' htwo
    refine ⟨f, hf, hb.trans ?_⟩
    have : 2 * ε ≤ 4 * ε := by nlinarith
    exact mul_le_mul_of_nonneg_right this (norm_nonneg A)
  · apply central_submatrix_card_eq_three m A hzd ε hε hε'
    omega

end CommutatorTheorem
