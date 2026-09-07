import CommutatorTheorem.NoEpsilon.Budget
import Mathlib.Tactic

/-!
# Abstract induction and constant closure for the no-epsilon proof

This module proves only the dimension induction and its scalar budget. The local splitting
and assembly hypotheses are explicit theorem parameters. This is not a proof that complex
matrices satisfy those hypotheses, and is not the final commutator theorem.
-/

namespace CommutatorTheorem.NoEpsilon

/-- A local finite splitting into strictly smaller dimensions, together with a common-budget
assembly rule, propagates a uniform bound to every dimension. The shrinking estimate is used
to put every child solution under the same budget before assembly. -/
theorem uniform_bound_of_shrinking_split
    {X : ℕ → Type*} (size : {n : ℕ} → X n → ℝ)
    (Solution : {n : ℕ} → X n → ℝ → Prop)
    (size_nonneg : ∀ {n} (x : X n), 0 ≤ size x)
    (solution_mono : ∀ {n} (x : X n) {p q : ℝ}, p ≤ q → Solution x p → Solution x q)
    (c q b H K : ℝ) (hq : 0 ≤ q) (hK : 0 ≤ K)
    (hHK : H ≤ K) (hclose : c * q * K + b ≤ K)
    (split : ∀ {n} (x : X n),
      Solution x (H * size x) ∨
        ∃ (l : ℕ) (d : Fin l → ℕ) (child : (i : Fin l) → X (d i)),
          (∀ i, d i < n) ∧ (∀ i, size (child i) ≤ q * size x) ∧
          (∀ p : ℝ, 0 ≤ p → (∀ i, Solution (child i) p) →
            Solution x (c * p + b * size x))) :
    ∀ {n} (x : X n), Solution x (K * size x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x
    rcases split x with hdirect | ⟨l, d, child, hd, hsize, hassemble⟩
    · exact solution_mono x (mul_le_mul_of_nonneg_right hHK (size_nonneg x)) hdirect
    · have hp : 0 ≤ K * q * size x :=
        mul_nonneg (mul_nonneg hK hq) (size_nonneg x)
      have hchildren : ∀ i, Solution (child i) (K * q * size x) := by
        intro i
        apply solution_mono (child i) _ (ih (d i) (hd i) (child i))
        calc
          K * size (child i) ≤ K * (q * size x) :=
            mul_le_mul_of_nonneg_left (hsize i) hK
          _ = K * q * size x := by ring
      have hparent := hassemble (K * q * size x) hp hchildren
      apply solution_mono x _ hparent
      calc
        c * (K * q * size x) + b * size x = (c * q * K + b) * size x := by ring
        _ ≤ K * size x := mul_le_mul_of_nonneg_right hclose (size_nonneg x)

/-- The proposed global constant dominates both the high-mass branch and the additive
cost needed by the shrinking branch. This is scalar arithmetic, not either branch theorem. -/
theorem candidate_global_constant (KH : ℝ) :
    let K := max ((8 * 8192 : ℝ) * KH + (2 : ℝ) ^ 42) ((2 : ℝ) ^ 43)
    (8 * 8192 : ℝ) * KH + (2 : ℝ) ^ 42 ≤ K ∧
      (8 * 8192 : ℝ) * (319 / (2 : ℝ) ^ 26) * K + (2 : ℝ) ^ 42 ≤ K := by
  dsimp
  exact ⟨le_max_left _ _, candidate_budget_closes _ (le_max_right _ _)⟩

end CommutatorTheorem.NoEpsilon
