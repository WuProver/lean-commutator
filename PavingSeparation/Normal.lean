import PavingSeparation.Family

/-!
# Normal commutator factors

An explicit self-adjoint involution anticommutes with the recursive family. This gives
normal factors of optimal cost `1 / 2`, without a change of coordinate basis.
-/

open Matrix
open scoped ComplexConjugate

attribute [local instance] Matrix.instL2OpNormedAddCommGroup Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedSpace Matrix.instCStarRing

namespace PavingSeparation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unnormalized anticommuting involution. -/
def rawFlip : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := fromBlocks 1 (-1) (-1) (-1)

omit [Fintype ι] in
theorem rawFlip_isHermitian : (rawFlip (ι := ι)).IsHermitian := by
  change (rawFlip (ι := ι))ᴴ = rawFlip
  simp [rawFlip, fromBlocks_conjTranspose]

theorem rawFlip_mul_self :
    rawFlip (ι := ι) * rawFlip = (2 : ℂ) • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  rw [rawFlip, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  apply fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> module

theorem rawFlip_anticommutes (S : Matrix ι ι ℂ) :
    rawFlip * fromBlocks S (S + 1) (S - 1) (-S) =
      -(fromBlocks S (S + 1) (S - 1) (-S) * rawFlip) := by
  rw [rawFlip, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg]
  apply fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

/-- A self-adjoint unitary of the same size as `pavingMatrix (m+1)`. -/
noncomputable def flip (m : ℕ) : Matrix (Cube (m + 1)) (Cube (m + 1)) ℂ :=
  ((Real.sqrt 2 : ℂ) / 2) • rawFlip

theorem flip_isHermitian (m : ℕ) : (flip m).IsHermitian := by
  change (flip m)ᴴ = flip m
  rw [flip, conjTranspose_smul, rawFlip_isHermitian.eq]
  simp

theorem flip_mul_self (m : ℕ) : flip m * flip m = 1 := by
  rw [flip, smul_mul_smul, rawFlip_mul_self, smul_smul]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hc : ((Real.sqrt 2 : ℂ) / 2 * ((Real.sqrt 2 : ℂ) / 2)) * 2 = 1 := by
    calc
      _ = (Real.sqrt 2 : ℂ) ^ 2 / 2 := by ring
      _ = 1 := by rw [hs]; norm_num
  rw [hc, one_smul]

theorem flip_anticommutes (m : ℕ) :
    flip m * pavingMatrix (m + 1) = -(pavingMatrix (m + 1) * flip m) := by
  rw [flip, pavingMatrix, smul_mul_smul, smul_mul_smul, skew_succ,
    rawFlip_anticommutes, smul_neg]
  congr 2
  ring

theorem flip_norm (m : ℕ) : ‖flip m‖ = 1 := by
  apply CStarRing.norm_of_mem_unitary
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, (flip_isHermitian m).eq]
  exact ⟨flip_mul_self m, flip_mul_self m⟩

/-- The second factor is skew-adjoint, hence normal. -/
noncomputable def normalSecond (m : ℕ) :
    Matrix (Cube (m + 1)) (Cube (m + 1)) ℂ :=
  (1 / 2 : ℂ) • (flip m * pavingMatrix (m + 1))

theorem normalSecond_conjTranspose (m : ℕ) :
    (normalSecond m)ᴴ = -normalSecond m := by
  rw [normalSecond, conjTranspose_smul, conjTranspose_mul,
    (flip_isHermitian m).eq, (family_isHermitian (m + 1)).eq]
  rw [flip_anticommutes]
  simp
  module

theorem normalSecond_isStarNormal (m : ℕ) : IsStarNormal (normalSecond m) := by
  constructor
  change (normalSecond m)ᴴ * normalSecond m = normalSecond m * (normalSecond m)ᴴ
  rw [normalSecond_conjTranspose]
  simp

theorem normal_factors_commutator (m : ℕ) :
    flip m * normalSecond m - normalSecond m * flip m = pavingMatrix (m + 1) := by
  rw [normalSecond, mul_smul_comm, smul_mul_assoc]
  have h₁ : flip m * (flip m * pavingMatrix (m + 1)) = pavingMatrix (m + 1) := by
    rw [← mul_assoc, flip_mul_self, one_mul]
  have h₂ : flip m * pavingMatrix (m + 1) * flip m = -pavingMatrix (m + 1) := by
    rw [flip_anticommutes, neg_mul, mul_assoc, flip_mul_self, mul_one]
  rw [h₁, h₂]
  module

theorem normalSecond_norm (m : ℕ) : ‖normalSecond m‖ = 1 / 2 := by
  have hu : flip m * pavingMatrix (m + 1) ∈
      unitary (Matrix (Cube (m + 1)) (Cube (m + 1)) ℂ) := by
    apply mul_mem
    · rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, (flip_isHermitian m).eq]
      exact ⟨flip_mul_self m, flip_mul_self m⟩
    · rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, (family_isHermitian (m + 1)).eq]
      exact ⟨family_mul_self (by omega), family_mul_self (by omega)⟩
  rw [normalSecond, norm_smul, CStarRing.norm_of_mem_unitary hu]
  norm_num

/-- Every commutator representation of a norm-one matrix has cost at least `1/2`. -/
theorem commutator_cost_lower {A B C : Matrix ι ι ℂ} (hA : ‖A‖ = 1)
    (hcomm : A = B * C - C * B) : 1 / 2 ≤ ‖B‖ * ‖C‖ := by
  have h := (norm_sub_le (B * C) (C * B)).trans
    (add_le_add (norm_mul_le B C) (norm_mul_le C B))
  rw [← hcomm, hA] at h
  nlinarith

/-- Infimum of the product of operator norms over commutator representations. -/
noncomputable def unrestrictedCost (A : Matrix ι ι ℂ) : ℝ :=
  sInf {t : ℝ | ∃ B C : Matrix ι ι ℂ, A = B * C - C * B ∧ t = ‖B‖ * ‖C‖}

/-- Both factors must be normal, as in the PDF's definition of `κ_normal`. -/
noncomputable def normalCost (A : Matrix ι ι ℂ) : ℝ :=
  sInf {t : ℝ | ∃ B C : Matrix ι ι ℂ,
    IsStarNormal B ∧ IsStarNormal C ∧ A = B * C - C * B ∧ t = ‖B‖ * ‖C‖}

theorem family_normalCost (m : ℕ) : normalCost (pavingMatrix (m + 1)) = 1 / 2 := by
  have hw : (1 / 2 : ℝ) ∈ {t : ℝ | ∃ B C : Matrix (Cube (m + 1)) (Cube (m + 1)) ℂ,
      IsStarNormal B ∧ IsStarNormal C ∧ pavingMatrix (m + 1) = B * C - C * B ∧
        t = ‖B‖ * ‖C‖} := by
    refine ⟨flip m, normalSecond m, (flip_isHermitian m).isSelfAdjoint.isStarNormal,
      normalSecond_isStarNormal m, (normal_factors_commutator m).symm, ?_⟩
    rw [flip_norm, normalSecond_norm, one_mul]
  apply le_antisymm
  · exact csInf_le ⟨0, by rintro t ⟨B, C, _, _, _, rfl⟩; positivity⟩ hw
  · apply le_csInf ⟨_, hw⟩
    rintro t ⟨B, C, _, _, hc, rfl⟩
    exact commutator_cost_lower (family_norm (by omega)) hc

theorem family_unrestrictedCost (m : ℕ) : unrestrictedCost (pavingMatrix (m + 1)) = 1 / 2 := by
  have hw : (1 / 2 : ℝ) ∈ {t : ℝ | ∃ B C : Matrix (Cube (m + 1)) (Cube (m + 1)) ℂ,
      pavingMatrix (m + 1) = B * C - C * B ∧ t = ‖B‖ * ‖C‖} := by
    refine ⟨flip m, normalSecond m, (normal_factors_commutator m).symm, ?_⟩
    rw [flip_norm, normalSecond_norm, one_mul]
  apply le_antisymm
  · exact csInf_le ⟨0, by rintro t ⟨B, C, _, rfl⟩; positivity⟩ hw
  · apply le_csInf ⟨_, hw⟩
    rintro t ⟨B, C, hc, rfl⟩
    exact commutator_cost_lower (family_norm (by omega)) hc

end PavingSeparation
