import CommutatorTheorem.Epsilon.BTFellCountParity

/-!
# Two-sided sign refinement for real-rooted polynomials

Exact Descartes makes the positive-root count lower semicontinuous when all
old nonzero coefficient signs are preserved.  Reflection gives the same
inequality for negative roots.  Away from zero their sum is the fixed degree,
so both inequalities are equalities.
-/

open scoped Polynomial

namespace CommutatorTheorem.BTFellSignLocal

open Polynomial
open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTFellDescartes
open CommutatorTheorem.BTFellExactDescartes

/-- The monic normalization of `p(-X)`. -/
noncomputable def reflectPolynomial (p : ℝ[X]) : ℝ[X] :=
  C ((-1 : ℝ) ^ p.natDegree) * p.comp (-X)

theorem coeff_comp_neg_X (p : ℝ[X]) (i : ℕ) :
    (p.comp (-X)).coeff i = (-1 : ℝ) ^ i * p.coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, coeff_add, hp, hq]; ring
  | monomial n a =>
      have hpow : (-X : ℝ[X]) ^ n = C ((-1 : ℝ) ^ n) * X ^ n := by
        rw [neg_pow]
        simp
      by_cases hni : n = i
      · subst n
        rw [monomial_comp, hpow, ← mul_assoc, ← C_mul,
          C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
        simp
        ring
      · rw [monomial_comp, hpow, ← mul_assoc, ← C_mul,
          C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
        simp [hni]

theorem coeff_reflectPolynomial (p : ℝ[X]) (i : ℕ) :
    (reflectPolynomial p).coeff i =
      ((-1 : ℝ) ^ p.natDegree * (-1 : ℝ) ^ i) * p.coeff i := by
  rw [reflectPolynomial, coeff_C_mul, coeff_comp_neg_X]
  ring

theorem reflectPolynomial_monic {p : ℝ[X]} (hp : p.Monic) :
    (reflectPolynomial p).Monic := by
  simpa [reflectPolynomial] using hp.neg_one_pow_natDegree_mul_comp_neg_X

/-- Reflection negates every root, with multiplicity. -/
theorem roots_reflectPolynomial {p : ℝ[X]} (hp : p.Monic)
    (hreal : RealRooted p) :
    (reflectPolynomial p).roots = p.roots.map (- ·) := by
  have hpProd := hreal.eq_prod_roots_of_monic hp
  have hdegree : p.natDegree = p.roots.card := hreal.natDegree_eq_card_roots
  have hprod : ∀ s : Multiset ℝ,
      C ((-1 : ℝ) ^ s.card) *
          (s.map (fun r : ℝ => X - C r)).prod.comp (-X) =
        (s.map (fun r : ℝ => X - C (-r))).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons r s ih =>
        simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons,
          mul_comp_neg_X, pow_succ]
        calc
          C ((-1 : ℝ) ^ s.card * -1) *
                ((X - C r).comp (-X) *
                  (s.map (fun r : ℝ => X - C r)).prod.comp (-X)) =
              (X - C (-r)) *
                (C ((-1 : ℝ) ^ s.card) *
                  (s.map (fun r : ℝ => X - C r)).prod.comp (-X)) := by
                    simp
                    ring
          _ = (X - C (-r)) *
                (s.map (fun r : ℝ => X - C (-r))).prod := by rw [ih]
  have heq : reflectPolynomial p =
      (p.roots.map (fun r : ℝ => X - C (-r))).prod := by
    unfold reflectPolynomial
    calc
      C ((-1 : ℝ) ^ p.natDegree) * p.comp (-X) =
          C ((-1 : ℝ) ^ p.roots.card) *
            (p.roots.map (fun r : ℝ => X - C r)).prod.comp (-X) := by
              rw [hdegree, ← hpProd]
      _ = _ := hprod p.roots
  rw [heq]
  convert roots_multiset_prod_X_sub_C (p.roots.map fun x => -x) using 1 <;>
    simp [Multiset.map_map]

theorem reflectPolynomial_realRooted {p : ℝ[X]} (hp : p.Monic)
    (hreal : RealRooted p) : RealRooted (reflectPolynomial p) := by
  unfold reflectPolynomial
  exact (hreal.comp_neg_X).C_mul _

theorem natDegree_reflectPolynomial {p : ℝ[X]} (hp : p.Monic)
    (hreal : RealRooted p) :
    (reflectPolynomial p).natDegree = p.natDegree := by
  rw [(reflectPolynomial_realRooted hp hreal).natDegree_eq_card_roots,
    roots_reflectPolynomial hp hreal, Multiset.card_map,
    ← hreal.natDegree_eq_card_roots]

theorem negativeRootsCount_eq_reflect_signVariations
    {p : ℝ[X]} (hp : p.Monic) (hreal : RealRooted p) :
    p.roots.countP (· < 0) = (reflectPolynomial p).signVariations := by
  rw [← roots_countP_pos_eq_signVariations
    (reflectPolynomial_monic hp) (reflectPolynomial_realRooted hp hreal)]
  rw [roots_reflectPolynomial hp hreal, Multiset.countP_map]
  rw [← Multiset.countP_eq_card_filter]
  apply Multiset.countP_congr rfl
  intro r hr
  simp

/-- The positive and negative root counts exhaust the degree when zero is
not a root. -/
theorem positive_add_negativeRootsCount_eq_natDegree
    {p : ℝ[X]} (hp : p.Monic) (hreal : RealRooted p)
    (hzero : ¬p.IsRoot 0) :
    p.roots.countP (0 < ·) + p.roots.countP (· < 0) = p.natDegree := by
  have hpartition := Multiset.card_eq_countP_add_countP (0 < ·) p.roots
  have hnonpos : p.roots.countP (fun r : ℝ => ¬ 0 < r) =
      p.roots.countP (· < 0) := by
    apply Multiset.countP_congr rfl
    intro r hr
    have hrne : r ≠ 0 := by
      intro hre
      subst r
      exact hzero ((mem_roots hp.ne_zero).mp hr)
    apply propext
    constructor <;> intro h
    · exact lt_of_le_of_ne (le_of_not_gt h) hrne
    · exact not_lt_of_ge h.le
  rw [hnonpos] at hpartition
  exact hpartition.symm.trans hreal.natDegree_eq_card_roots.symm

/-- Within the real-rooted locus and away from zero, preservation of every
old nonzero coefficient sign actually preserves the exact sign variation. -/
theorem signVariations_eq_of_coeff_sign_preserved
    {p q : ℝ[X]} (hp : p.Monic) (hq : q.Monic)
    (hpreal : RealRooted p) (hqreal : RealRooted q)
    (hdegree : p.natDegree = q.natDegree)
    (hpzero : ¬p.IsRoot 0) (hqzero : ¬q.IsRoot 0)
    (hsign : ∀ i : ℕ, i ≤ p.natDegree →
      SignType.sign (p.coeff i) = 0 ∨
        SignType.sign (p.coeff i) = SignType.sign (q.coeff i)) :
    p.signVariations = q.signVariations := by
  have hpos : p.signVariations ≤ q.signVariations :=
    signVariations_le_of_coeffSignRefines
      (coeffSignRefines_of_forall_coeff_sign hdegree hp.ne_zero hq.ne_zero hsign)
  have hreflectDegree : (reflectPolynomial p).natDegree =
      (reflectPolynomial q).natDegree := by
    rw [natDegree_reflectPolynomial hp hpreal,
      natDegree_reflectPolynomial hq hqreal]
    exact hdegree
  have hreflectSign : ∀ i : ℕ, i ≤ (reflectPolynomial p).natDegree →
      SignType.sign ((reflectPolynomial p).coeff i) = 0 ∨
        SignType.sign ((reflectPolynomial p).coeff i) =
          SignType.sign ((reflectPolynomial q).coeff i) := by
    intro i hi
    have hip : i ≤ p.natDegree := by
      simpa [natDegree_reflectPolynomial hp hpreal] using hi
    rcases hsign i hip with hzero | heq
    · left
      have hpcoeff : p.coeff i = 0 := by simpa using hzero
      simp [coeff_reflectPolynomial, hpcoeff]
    · right
      rw [coeff_reflectPolynomial, coeff_reflectPolynomial, hdegree]
      simp only [sign_mul]
      rw [heq]
  have hneg : (reflectPolynomial p).signVariations ≤
      (reflectPolynomial q).signVariations :=
    signVariations_le_of_coeffSignRefines
      (coeffSignRefines_of_forall_coeff_sign hreflectDegree
        (reflectPolynomial_monic hp).ne_zero
        (reflectPolynomial_monic hq).ne_zero hreflectSign)
  have hpSum := positive_add_negativeRootsCount_eq_natDegree
    hp hpreal hpzero
  have hqSum := positive_add_negativeRootsCount_eq_natDegree
    hq hqreal hqzero
  rw [roots_countP_pos_eq_signVariations hp hpreal,
    negativeRootsCount_eq_reflect_signVariations hp hpreal] at hpSum
  rw [roots_countP_pos_eq_signVariations hq hqreal,
    negativeRootsCount_eq_reflect_signVariations hq hqreal] at hqSum
  omega

end CommutatorTheorem.BTFellSignLocal
