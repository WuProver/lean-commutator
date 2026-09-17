import CommutatorTheorem.Epsilon.BTRSBaseExpansion

/-!
# Recursive coloring expansion for repeated coordinate derivatives

This file packages the purely Leibniz-theoretic part of the exact mixed
determinantal expansion.  It is independent of determinant reindexing: a
coordinate is recursively assigned to the unique factor left
undifferentiated in that coordinate.
-/

namespace CommutatorTheorem.BTRSColoringExpansion

open scoped BigOperators
open Finset
open CommutatorTheorem.BTRSStabilityBridge
open CommutatorTheorem.BTRSBaseExpansion
open CommutatorTheorem.BTHermitianDetPDeriv

noncomputable def chooseUndifferentiated
    {σ : Type*} {k : ℕ} (x : σ) (a : Fin k)
    (f : Fin k → MvPolynomial σ ℂ) (b : Fin k) : MvPolynomial σ ℂ :=
  if b = a then f b else MvPolynomial.pderiv x (f b)

noncomputable def recursiveColoringExpansion
    {σ : Type*} {k : ℕ} :
    List σ → (Fin k → MvPolynomial σ ℂ) → MvPolynomial σ ℂ
  | [], f => ∏ a, f a
  | x :: xs, f =>
      ∑ a, recursiveColoringExpansion xs (chooseUndifferentiated x a f)

theorem prod_chooseUndifferentiated
    {σ : Type*} {k : ℕ} (x : σ) (a : Fin k)
    (f : Fin k → MvPolynomial σ ℂ) :
    (∏ b, chooseUndifferentiated x a f b) =
      f a * ∏ b ∈ (Finset.univ : Finset (Fin k)).erase a,
        MvPolynomial.pderiv x (f b) := by
  classical
  rw [← Finset.prod_erase_mul Finset.univ
    (chooseUndifferentiated x a f) (Finset.mem_univ a)]
  rw [mul_comm (f a)]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro b hb
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    simp [chooseUndifferentiated, hba]
  · simp [chooseUndifferentiated]

theorem iteratedPDeriv_sum_fin
    {σ : Type*} {k : ℕ} (is : List σ)
    (f : Fin k → MvPolynomial σ ℂ) :
    iteratedPDeriv is (∑ a, f a) = ∑ a, iteratedPDeriv is (f a) := by
  induction is generalizing f with
  | nil => rfl
  | cons x xs ih =>
      simp only [iteratedPDeriv_cons, map_sum]
      exact ih (fun a => MvPolynomial.pderiv x (f a))

private theorem chooseUndifferentiated_multiaffine
    {σ : Type*} {k : ℕ} (x y : σ) (a : Fin k)
    (f : Fin k → MvPolynomial σ ℂ)
    (hf : ∀ b, MvPolynomial.pderiv y
      (MvPolynomial.pderiv y (f b)) = 0) :
    ∀ b, MvPolynomial.pderiv y
      (MvPolynomial.pderiv y (chooseUndifferentiated x a f b)) = 0 := by
  intro b
  classical
  by_cases hba : b = a
  · simpa only [chooseUndifferentiated, if_pos hba] using hf b
  · simp only [chooseUndifferentiated, hba, ↓reduceIte]
    calc
      MvPolynomial.pderiv y
          (MvPolynomial.pderiv y (MvPolynomial.pderiv x (f b))) =
          MvPolynomial.pderiv y
            (MvPolynomial.pderiv x (MvPolynomial.pderiv y (f b))) :=
        congrArg (MvPolynomial.pderiv y) (pderiv_comm y x (f b))
      _ = MvPolynomial.pderiv x
          (MvPolynomial.pderiv y (MvPolynomial.pderiv y (f b))) :=
        pderiv_comm y x (MvPolynomial.pderiv y (f b))
      _ = 0 := by rw [hf b]; simp

/-- Repeating `m` derivatives in every coordinate of `xs` assigns each
coordinate to one of `m+1` factors.  The multiplicity is `(m!)^|xs|`. -/
theorem iteratedPDeriv_blocks_eq_recursiveColoringExpansion
    {σ : Type*} (m : ℕ) (xs : List σ)
    (f : Fin (m + 1) → MvPolynomial σ ℂ)
    (hf : ∀ x ∈ xs, ∀ a, MvPolynomial.pderiv x
      (MvPolynomial.pderiv x (f a)) = 0) :
    iteratedPDeriv
        (xs.flatMap (List.replicate m)) (∏ a, f a) =
      MvPolynomial.C ((m.factorial : ℂ) ^ xs.length) *
        recursiveColoringExpansion xs f := by
  induction xs generalizing f with
  | nil => simp [recursiveColoringExpansion]
  | cons x xs ih =>
      rw [List.flatMap_cons, iteratedPDeriv_append]
      change iteratedPDeriv (xs.flatMap (List.replicate m))
        (repeatedPDeriv x m (∏ a, f a)) = _
      rw [repeatedPDeriv_prod_fin_leave_one x m f (hf x (by simp))]
      have hsum :
          (∑ a : Fin (m + 1),
              f a * ∏ b ∈ (Finset.univ : Finset (Fin (m + 1))).erase a,
                MvPolynomial.pderiv x (f b)) =
            ∑ a : Fin (m + 1), ∏ b, chooseUndifferentiated x a f b := by
        apply Finset.sum_congr rfl
        intro a _
        exact (prod_chooseUndifferentiated x a f).symm
      rw [hsum, iteratedPDeriv_C_mul, iteratedPDeriv_sum_fin]
      have htail : ∀ y ∈ xs, ∀ a,
          MvPolynomial.pderiv y (MvPolynomial.pderiv y (f a)) = 0 := by
        intro y hy
        exact hf y (by simp [hy])
      simp_rw [ih _ (fun y hy ↦
        chooseUndifferentiated_multiaffine x y _ f (htail y hy))]
      simp only [recursiveColoringExpansion, List.length_cons]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [pow_succ]
      simp only [map_mul]
      ring

end CommutatorTheorem.BTRSColoringExpansion
