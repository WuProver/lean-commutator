import CommutatorTheorem.Epsilon.BTElementary

/-!
# The cardinality-two elementary Bourgain--Tzafriri range

For a zero-diagonal matrix, a two-coordinate compression has Hilbert--Schmidt
norm squared `|aᵢⱼ|² + |aⱼᵢ|²`.  Averaging this energy over ordered off-diagonal
pairs gives a pair with the required bound when `⌊ε²m⌋ = 2`.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing

namespace CommutatorTheorem

private noncomputable def pairEnergy {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (p : Fin m × Fin m) : ℝ :=
  Complex.normSq (A p.1 p.2) + Complex.normSq (A p.2 p.1)

private lemma pairEnergy_nonneg {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (p : Fin m × Fin m) :
    0 ≤ pairEnergy A p := by
  unfold pairEnergy
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

private lemma total_normSq_le {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
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

private lemma offDiag_pairEnergy_sum_le {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) :
    (∑ p ∈ (Finset.univ : Finset (Fin m)).offDiag, pairEnergy A p) ≤
      2 * (m : ℝ) * ‖A‖ ^ 2 := by
  let U : Finset (Fin m) := Finset.univ
  have hsubset : U.offDiag ⊆ U ×ˢ U := by
    intro p hp
    simp only [Finset.mem_offDiag] at hp
    exact Finset.mem_product.mpr ⟨hp.1, hp.2.1⟩
  have hsubsum :
      (∑ p ∈ U.offDiag, pairEnergy A p) ≤
        ∑ p ∈ U ×ˢ U, pairEnergy A p := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun p _ _ => pairEnergy_nonneg A p)
  have hfull :
      (∑ p ∈ U ×ˢ U, pairEnergy A p) =
        2 * ∑ i : Fin m, ∑ j : Fin m, Complex.normSq (A i j) := by
    rw [Finset.sum_product]
    simp only [pairEnergy]
    simp_rw [Finset.sum_add_distrib]
    have htranspose :
        (∑ x ∈ U, ∑ y ∈ U, Complex.normSq (A y x)) =
          ∑ x ∈ U, ∑ y ∈ U, Complex.normSq (A x y) := by
      exact Finset.sum_comm
    rw [htranspose]
    simp only [U]
    ring
  calc
    (∑ p ∈ (Finset.univ : Finset (Fin m)).offDiag, pairEnergy A p)
        ≤ ∑ p ∈ U ×ˢ U, pairEnergy A p := by simpa [U] using hsubsum
    _ = 2 * ∑ i : Fin m, ∑ j : Fin m, Complex.normSq (A i j) := hfull
    _ ≤ 2 * ((m : ℝ) * ‖A‖ ^ 2) := by
      gcongr
      exact total_normSq_le A
    _ = 2 * (m : ℝ) * ‖A‖ ^ 2 := by ring

private lemma exists_good_offDiag_pair
    (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hfloor : ⌊ε ^ 2 * (m : ℝ)⌋₊ = 2) :
    ∃ p ∈ (Finset.univ : Finset (Fin m)).offDiag,
      pairEnergy A p ≤ (2 * ε * ‖A‖) ^ 2 := by
  have harg_nonneg : 0 ≤ ε ^ 2 * (m : ℝ) := by positivity
  have htwo_le_arg : (2 : ℝ) ≤ ε ^ 2 * (m : ℝ) := by
    have := Nat.floor_le (R := ℝ) harg_nonneg
    rw [hfloor] at this
    exact_mod_cast this
  have hm2 : 2 ≤ m := by
    by_contra hm
    have hm_le : m ≤ 1 := by omega
    have hmR : (m : ℝ) ≤ 1 := by exact_mod_cast hm_le
    have hεlt : ε ^ 2 < 1 := by nlinarith
    nlinarith
  let S : Finset (Fin m × Fin m) := (Finset.univ : Finset (Fin m)).offDiag
  have hSnonempty : S.Nonempty := by
    refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
    simp [S]
  have hcardS : S.card = m * m - m := by simp [S]
  have hcoef :
      2 * (m : ℝ) ≤ ((m * m - m : ℕ) : ℝ) * (4 * ε ^ 2) := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hcast : ((m * m - m : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
      have hmm : m ≤ m * m := by nlinarith
      rw [Nat.cast_sub hmm]
      rw [Nat.cast_mul]
      ring
    rw [hcast]
    nlinarith
  have hsum_bound :
      (∑ p ∈ S, pairEnergy A p) ≤
        ∑ _p ∈ S, (2 * ε * ‖A‖) ^ 2 := by
    calc
      (∑ p ∈ S, pairEnergy A p)
          ≤ 2 * (m : ℝ) * ‖A‖ ^ 2 := by
            simpa [S] using offDiag_pairEnergy_sum_le A
      _ ≤ (((m * m - m : ℕ) : ℝ) * (4 * ε ^ 2)) * ‖A‖ ^ 2 := by
            gcongr
      _ = ∑ _p ∈ S, (2 * ε * ‖A‖) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, hcardS]
            ring
  obtain ⟨p, hpS, hp⟩ := Finset.exists_le_of_sum_le hSnonempty hsum_bound
  exact ⟨p, by simpa [S] using hpS, hp⟩

private def pairEmbedding {m : ℕ} (p : Fin m × Fin m) : Fin 2 → Fin m :=
  fun i => if i = 0 then p.1 else p.2

@[simp] private lemma pairEmbedding_zero {m : ℕ} (p : Fin m × Fin m) :
    pairEmbedding p 0 = p.1 := by simp [pairEmbedding]

@[simp] private lemma pairEmbedding_one {m : ℕ} (p : Fin m × Fin m) :
    pairEmbedding p 1 = p.2 := by simp [pairEmbedding]

private lemma pairEmbedding_injective {m : ℕ} {p : Fin m × Fin m}
    (hp : p.1 ≠ p.2) : Function.Injective (pairEmbedding p) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- The central-submatrix estimate with constant `2` when the requested
cardinality is exactly two. -/
theorem central_submatrix_card_eq_two
    (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) (hzd : ZeroDiag A)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hcard : ⌊ε ^ 2 * (m : ℝ)⌋₊ = 2) :
    ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
      Function.Injective f ∧
      ‖A.submatrix f f‖ ≤ 2 * ε * ‖A‖ := by
  obtain ⟨p, hp, hpEnergy⟩ := exists_good_offDiag_pair m A ε hε hε' hcard
  have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
  rw [hcard]
  let f : Fin 2 → Fin m := pairEmbedding p
  have hf : Function.Injective f := pairEmbedding_injective hpne
  refine ⟨f, hf, ?_⟩
  set B : Matrix (Fin 2) (Fin 2) ℂ := A.submatrix f f with hB
  have hsum :
      (∑ i : Fin 2, ∑ j : Fin 2, Complex.normSq (B i j)) = pairEnergy A p := by
    simp only [Fin.sum_univ_two]
    rw [hB]
    simp only [Matrix.submatrix_apply]
    simp [f, pairEnergy, hzd p.1, hzd p.2]
  have hsum_nonneg :
      0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, Complex.normSq (B i j) := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hhs_sq : hsNorm B ^ 2 = pairEnergy A p := by
    unfold hsNorm
    rw [Real.sq_sqrt hsum_nonneg, hsum]
  have hhs_bound : hsNorm B ≤ 2 * ε * ‖A‖ := by
    apply le_of_sq_le_sq
    · rw [hhs_sq]
      exact hpEnergy
    · positivity
  calc
    ‖A.submatrix f f‖ = ‖B‖ := by rw [hB]
    _ ≤ hsNorm B := le_hsNorm B
    _ ≤ 2 * ε * ‖A‖ := hhs_bound

/-- The cardinality-at-most-two elementary range. -/
theorem central_submatrix_card_le_two
    (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) (hzd : ZeroDiag A)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hcard : ⌊ε ^ 2 * (m : ℝ)⌋₊ ≤ 2) :
    ∃ (f : Fin ⌊ε ^ 2 * (m : ℝ)⌋₊ → Fin m),
      Function.Injective f ∧
      ‖A.submatrix f f‖ ≤ 2 * ε * ‖A‖ := by
  by_cases hone : ⌊ε ^ 2 * (m : ℝ)⌋₊ ≤ 1
  · exact central_submatrix_card_le_one m A hzd ε hε hε' hone
  · apply central_submatrix_card_eq_two m A hzd ε hε hε'
    omega

end CommutatorTheorem
