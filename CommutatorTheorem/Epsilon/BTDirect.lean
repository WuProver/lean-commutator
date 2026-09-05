import CommutatorTheorem.Defs

/-!
# The elementary part of the iterated paving interface

The coordinate bookkeeping in `bourgain_tzafriri_iterated` is elementary: one can
choose `4^l` disjoint coordinate blocks of cardinality `4^(n-l)`, and compression to
each block does not increase operator norm.  The genuinely deep input is precisely
the dimension-free decay from `1` to `K * 2^(-l)`.

This file proves the elementary interface without using the Bourgain--Tzafriri axiom.
-/

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing

namespace CommutatorTheorem

/-- Consecutive coordinate blocks inside the first `4^n` of `2 * 4^n` coordinates. -/
def canonicalPavingBlock (n l : ℕ) (hl : l ≤ n)
    (i : Fin (4 ^ l)) (j : Fin (4 ^ (n - l))) : Fin (2 * 4 ^ n) := by
  refine ⟨i.1 * 4 ^ (n - l) + j.1, ?_⟩
  have hsplit : 4 ^ l * 4 ^ (n - l) = 4 ^ n := by
    rw [← pow_add]
    congr 1
    omega
  have hqpos : 0 < 4 ^ (n - l) := pow_pos (by omega) _
  have hlt : i.1 * 4 ^ (n - l) + j.1 < 4 ^ l * 4 ^ (n - l) := by
    nlinarith [i.2, j.2]
  rw [hsplit] at hlt
  omega

lemma canonicalPavingBlock_injective (n l : ℕ) (hl : l ≤ n) (i : Fin (4 ^ l)) :
    Function.Injective (canonicalPavingBlock n l hl i) := by
  intro a b hab
  apply Fin.ext
  have habv := congrArg Fin.val hab
  change i.1 * 4 ^ (n - l) + a.1 = i.1 * 4 ^ (n - l) + b.1 at habv
  omega

lemma canonicalPavingBlock_disjoint (n l : ℕ) (hl : l ≤ n)
    (i k : Fin (4 ^ l)) (hik : i ≠ k) :
    Disjoint (Set.range (canonicalPavingBlock n l hl i))
      (Set.range (canonicalPavingBlock n l hl k)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a, rfl⟩ ⟨b, hEq⟩
  apply hik
  apply Fin.ext
  have hEqv := congrArg Fin.val hEq
  change k.1 * 4 ^ (n - l) + b.1 = i.1 * 4 ^ (n - l) + a.1 at hEqv
  have ha : a.1 < 4 ^ (n - l) := a.2
  have hb : b.1 < 4 ^ (n - l) := b.2
  have hqpos : 0 < 4 ^ (n - l) := pow_pos (by omega) _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hiklt | hkilt
  · have hsucc : i.1 + 1 ≤ k.1 := by omega
    have hsep : (i.1 + 1) * 4 ^ (n - l) ≤ k.1 * 4 ^ (n - l) :=
      Nat.mul_le_mul_right _ hsucc
    have hwithin : i.1 * 4 ^ (n - l) + a.1 < (i.1 + 1) * 4 ^ (n - l) := by
      nlinarith
    omega
  · have hsucc : k.1 + 1 ≤ i.1 := by omega
    have hsep : (k.1 + 1) * 4 ^ (n - l) ≤ i.1 * 4 ^ (n - l) :=
      Nat.mul_le_mul_right _ hsucc
    have hwithin : k.1 * 4 ^ (n - l) + b.1 < (k.1 + 1) * 4 ^ (n - l) := by
      nlinarith
    omega

/-- The no-decay paving available from coordinate bookkeeping and norm compression alone. -/
theorem canonical_trivial_paving :
    ∀ (n l : ℕ), l ≤ n →
    ∀ A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ,
      ∃ σ : Fin (4 ^ l) → Fin (4 ^ (n - l)) → Fin (2 * 4 ^ n),
        (∀ i, Function.Injective (σ i)) ∧
        (∀ i j, i ≠ j → Disjoint (Set.range (σ i)) (Set.range (σ j))) ∧
        (∀ i, ‖A.submatrix (σ i) (σ i)‖ ≤ ‖A‖) := by
  intro n l hl A
  refine ⟨canonicalPavingBlock n l hl, canonicalPavingBlock_injective n l hl,
    canonicalPavingBlock_disjoint n l hl, ?_⟩
  intro i
  simpa only [Matrix.submatrix] using
    submatrix_norm_le (canonicalPavingBlock n l hl i)
      (canonicalPavingBlock_injective n l hl i) A

/-- At the terminal depth `l = n`, all canonical leaves are singletons and hence
their compressions are zero for a zero-diagonal matrix.  Thus the two endpoints
(`l = 0` and `l = n`) are elementary; uniform decay at intermediate depths is the
analytic Bourgain--Tzafriri content. -/
theorem canonical_terminal_paving_zero (n : ℕ)
    (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ) (hzd : ZeroDiag A) :
    ∀ i : Fin (4 ^ n),
      A.submatrix (canonicalPavingBlock n n le_rfl i)
        (canonicalPavingBlock n n le_rfl i) = 0 := by
  intro i
  ext a b
  have hab : a = b := by
    apply Fin.ext
    have ha := a.2
    have hb := b.2
    simp only [Nat.sub_self, pow_zero] at ha hb
    omega
  subst b
  exact hzd _

/-- The weakest interface consumed by the final Claim-2 recurrence: it asks only
for one controlled half and its complement, rather than the full family of paving
leaves.  Proving this predicate with a uniform constant would be enough for the
rest of the current main-theorem pipeline. -/
def SelectedHalfLambdaDescent : Prop :=
  ∃ K : ℝ, 48 ≤ K ∧
    ∀ (n l : ℕ), 2 ≤ l → l ≤ n →
    ∀ (A : Matrix (Fin (2 * 4 ^ n)) (Fin (2 * 4 ^ n)) ℂ),
      ZeroDiag A → ‖A‖ ≤ 1 →
      ∃ (H H' : Fin (4 ^ n) → Fin (2 * 4 ^ n)),
        Function.Injective H ∧ Function.Injective H' ∧
        Disjoint (Set.range H) (Set.range H') ∧
        (Set.range H ∪ Set.range H') = Set.univ ∧
        lambdaA (A.submatrix H H) ≤
          K * lambdaM (4 ^ (n - l)) +
            K * (l : ℝ) ^ 3 * (2 : ℝ) ^ l

end CommutatorTheorem
