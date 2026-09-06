import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Rectangular block shears

The first two blocks have index type `ι`; the block to be eliminated has the possibly
different index type `κ`. The identities hold over every ring. The two-step elimination
uses only a rectangular matrix `J` with a left inverse, so an isometric embedding is a
special case. No analytic norm bound or existence of an embedding is assumed implicitly.
-/

namespace NoEpsilon.Shear

section Ring

variable {R : Type*} [Ring R]

/-- The expanded conjugation formula, valid even without square-zero hypotheses. -/
theorem conjugate_expand (A N : R) :
    (1 - N) * A * (1 + N) = A + A * N - N * A - N * A * N := by
  noncomm_ring

/-- A square-zero perturbation of the identity has this explicit right inverse. -/
theorem one_add_mul_one_sub (N : R) (hN : N * N = 0) :
    (1 + N) * (1 - N) = 1 := by
  calc
    (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
    _ = 1 := by rw [hN, sub_zero]

/-- The same explicit inverse is also a left inverse. -/
theorem one_sub_mul_one_add (N : R) (hN : N * N = 0) :
    (1 - N) * (1 + N) = 1 := by
  calc
    (1 - N) * (1 + N) = 1 - N * N := by noncomm_ring
    _ = 1 := by rw [hN, sub_zero]

end Ring

section ThreeBlocks

variable {ι κ R : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ] [Ring R]

/-- The actual coordinate type of the three blocks; no equal-size padding is used. -/
abbrev Index (ι κ : Type*) := ι ⊕ (ι ⊕ κ)

/-- Assemble nine rectangular blocks into one matrix. -/
def blocks (A₁₁ A₁₂ : Matrix ι ι R) (A₁₃ : Matrix ι κ R)
    (A₂₁ A₂₂ : Matrix ι ι R) (A₂₃ : Matrix ι κ R)
    (A₃₁ A₃₂ : Matrix κ ι R) (A₃₃ : Matrix κ κ R) :
    Matrix (Index ι κ) (Index ι κ) R :=
  fun i j ↦ match i, j with
    | .inl i, .inl j => A₁₁ i j
    | .inl i, .inr (.inl j) => A₁₂ i j
    | .inl i, .inr (.inr j) => A₁₃ i j
    | .inr (.inl i), .inl j => A₂₁ i j
    | .inr (.inl i), .inr (.inl j) => A₂₂ i j
    | .inr (.inl i), .inr (.inr j) => A₂₃ i j
    | .inr (.inr i), .inl j => A₃₁ i j
    | .inr (.inr i), .inr (.inl j) => A₃₂ i j
    | .inr (.inr i), .inr (.inr j) => A₃₃ i j

def block₁₁ (A : Matrix (Index ι κ) (Index ι κ) R) : Matrix ι ι R :=
  fun i j ↦ A (.inl i) (.inl j)

def block₁₂ (A : Matrix (Index ι κ) (Index ι κ) R) : Matrix ι ι R :=
  fun i j ↦ A (.inl i) (.inr (.inl j))

def block₁₃ (A : Matrix (Index ι κ) (Index ι κ) R) : Matrix ι κ R :=
  fun i j ↦ A (.inl i) (.inr (.inr j))

def block₂₁ (A : Matrix (Index ι κ) (Index ι κ) R) : Matrix ι ι R :=
  fun i j ↦ A (.inr (.inl i)) (.inl j)

def block₂₂ (A : Matrix (Index ι κ) (Index ι κ) R) : Matrix ι ι R :=
  fun i j ↦ A (.inr (.inl i)) (.inr (.inl j))

def block₂₃ (A : Matrix (Index ι κ) (Index ι κ) R) : Matrix ι κ R :=
  fun i j ↦ A (.inr (.inl i)) (.inr (.inr j))

def block₃₁ (A : Matrix (Index ι κ) (Index ι κ) R) : Matrix κ ι R :=
  fun i j ↦ A (.inr (.inr i)) (.inl j)

def block₃₂ (A : Matrix (Index ι κ) (Index ι κ) R) : Matrix κ ι R :=
  fun i j ↦ A (.inr (.inr i)) (.inr (.inl j))

def block₃₃ (A : Matrix (Index ι κ) (Index ι κ) R) : Matrix κ κ R :=
  fun i j ↦ A (.inr (.inr i)) (.inr (.inr j))

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Ring R] in
theorem blocks_reconstruct (A : Matrix (Index ι κ) (Index ι κ) R) :
    blocks (block₁₁ A) (block₁₂ A) (block₁₃ A)
      (block₂₁ A) (block₂₂ A) (block₂₃ A)
      (block₃₁ A) (block₃₂ A) (block₃₃ A) = A := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;> rfl

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem blocks_zero :
    blocks (0 : Matrix ι ι R) 0 (0 : Matrix ι κ R) 0 0 0 0 0 0 = 0 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;> rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem blocks_mul
    (A₁₁ A₁₂ : Matrix ι ι R) (A₁₃ : Matrix ι κ R)
    (A₂₁ A₂₂ : Matrix ι ι R) (A₂₃ : Matrix ι κ R)
    (A₃₁ A₃₂ : Matrix κ ι R) (A₃₃ : Matrix κ κ R)
    (B₁₁ B₁₂ : Matrix ι ι R) (B₁₃ : Matrix ι κ R)
    (B₂₁ B₂₂ : Matrix ι ι R) (B₂₃ : Matrix ι κ R)
    (B₃₁ B₃₂ : Matrix κ ι R) (B₃₃ : Matrix κ κ R) :
    blocks A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃ *
        blocks B₁₁ B₁₂ B₁₃ B₂₁ B₂₂ B₂₃ B₃₁ B₃₂ B₃₃ =
      blocks
        (A₁₁ * B₁₁ + A₁₂ * B₂₁ + A₁₃ * B₃₁)
        (A₁₁ * B₁₂ + A₁₂ * B₂₂ + A₁₃ * B₃₂)
        (A₁₁ * B₁₃ + A₁₂ * B₂₃ + A₁₃ * B₃₃)
        (A₂₁ * B₁₁ + A₂₂ * B₂₁ + A₂₃ * B₃₁)
        (A₂₁ * B₁₂ + A₂₂ * B₂₂ + A₂₃ * B₃₂)
        (A₂₁ * B₁₃ + A₂₂ * B₂₃ + A₂₃ * B₃₃)
        (A₃₁ * B₁₁ + A₃₂ * B₂₁ + A₃₃ * B₃₁)
        (A₃₁ * B₁₂ + A₃₂ * B₂₂ + A₃₃ * B₃₂)
        (A₃₁ * B₁₃ + A₃₂ * B₂₃ + A₃₃ * B₃₃) := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [blocks, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

/-- A rectangular matrix supported in block `(2,3)`. -/
def insert₂₃ (X : Matrix ι κ R) : Matrix (Index ι κ) (Index ι κ) R :=
  blocks 0 0 0 0 0 X 0 0 0

/-- A rectangular matrix supported in block `(3,1)`. -/
def insert₃₁ (Y : Matrix κ ι R) : Matrix (Index ι κ) (Index ι κ) R :=
  blocks 0 0 0 0 0 0 Y 0 0

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem insert₂₃_square (X : Matrix ι κ R) : insert₂₃ X * insert₂₃ X = 0 := by
  simp [insert₂₃, blocks_mul]

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem insert₃₁_square (Y : Matrix κ ι R) : insert₃₁ Y * insert₃₁ Y = 0 := by
  simp [insert₃₁, blocks_mul]

/-- Conjugation by an elementary shear, using its explicit inverse. -/
def conjugate (A N : Matrix (Index ι κ) (Index ι κ) R) :
    Matrix (Index ι κ) (Index ι κ) R :=
  (1 - N) * A * (1 + N)

omit [Fintype ι] [Fintype κ] in
private theorem one_add_insert₂₃ (X : Matrix ι κ R) :
    1 + insert₂₃ X = blocks 1 0 0 0 1 X 0 0 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [insert₂₃, blocks, Matrix.one_apply]

omit [Fintype ι] [Fintype κ] in
private theorem one_sub_insert₂₃ (X : Matrix ι κ R) :
    1 - insert₂₃ X = blocks 1 0 0 0 1 (-X) 0 0 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [insert₂₃, blocks, Matrix.one_apply]

omit [Fintype ι] [Fintype κ] in
private theorem one_add_insert₃₁ (Y : Matrix κ ι R) :
    1 + insert₃₁ Y = blocks 1 0 0 0 1 0 Y 0 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [insert₃₁, blocks, Matrix.one_apply]

omit [Fintype ι] [Fintype κ] in
private theorem one_sub_insert₃₁ (Y : Matrix κ ι R) :
    1 - insert₃₁ Y = blocks 1 0 0 0 1 0 (-Y) 0 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [insert₃₁, blocks, Matrix.one_apply]

/-- Every block after the first rectangular shear. -/
theorem conjugate_insert₂₃_blocks
    (A₁₁ A₁₂ : Matrix ι ι R) (A₁₃ : Matrix ι κ R)
    (A₂₁ A₂₂ : Matrix ι ι R) (A₂₃ : Matrix ι κ R)
    (A₃₁ A₃₂ : Matrix κ ι R) (A₃₃ : Matrix κ κ R) (X : Matrix ι κ R) :
    conjugate (blocks A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃) (insert₂₃ X) =
      blocks A₁₁ A₁₂ (A₁₃ + A₁₂ * X)
        (A₂₁ - X * A₃₁) (A₂₂ - X * A₃₂)
        (A₂₃ + A₂₂ * X - X * A₃₃ - X * A₃₂ * X)
        A₃₁ A₃₂ (A₃₃ + A₃₂ * X) := by
  simp only [conjugate, one_sub_insert₂₃, one_add_insert₂₃, blocks_mul]
  congr 1 <;>
    simp [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_assoc] <;> abel

/-- Every block after the second rectangular shear. -/
theorem conjugate_insert₃₁_blocks
    (A₁₁ A₁₂ : Matrix ι ι R) (A₁₃ : Matrix ι κ R)
    (A₂₁ A₂₂ : Matrix ι ι R) (A₂₃ : Matrix ι κ R)
    (A₃₁ A₃₂ : Matrix κ ι R) (A₃₃ : Matrix κ κ R) (Y : Matrix κ ι R) :
    conjugate (blocks A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃) (insert₃₁ Y) =
      blocks (A₁₁ + A₁₃ * Y) A₁₂ A₁₃
        (A₂₁ + A₂₃ * Y) A₂₂ A₂₃
        (A₃₁ + A₃₃ * Y - Y * A₁₁ - Y * A₁₃ * Y)
        (A₃₂ - Y * A₁₂) (A₃₃ - Y * A₁₃) := by
  simp only [conjugate, one_sub_insert₃₁, one_add_insert₃₁, blocks_mul]
  congr 1 <;>
    simp [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_assoc] <;> abel

theorem conjugate_insert₂₃_block₁₂ (A : Matrix (Index ι κ) (Index ι κ) R)
    (X : Matrix ι κ R) : block₁₂ (conjugate A (insert₂₃ X)) = block₁₂ A := by
  rw [← blocks_reconstruct A, conjugate_insert₂₃_blocks]
  rfl

theorem conjugate_insert₂₃_block₁₃ (A : Matrix (Index ι κ) (Index ι κ) R)
    (X : Matrix ι κ R) :
    block₁₃ (conjugate A (insert₂₃ X)) = block₁₃ A + block₁₂ A * X := by
  rw [← blocks_reconstruct A, conjugate_insert₂₃_blocks]
  rfl

theorem conjugate_insert₂₃_block₃₃ (A : Matrix (Index ι κ) (Index ι κ) R)
    (X : Matrix ι κ R) :
    block₃₃ (conjugate A (insert₂₃ X)) = block₃₃ A + block₃₂ A * X := by
  rw [← blocks_reconstruct A, conjugate_insert₂₃_blocks]
  rfl

theorem conjugate_insert₃₁_block₁₂ (A : Matrix (Index ι κ) (Index ι κ) R)
    (Y : Matrix κ ι R) : block₁₂ (conjugate A (insert₃₁ Y)) = block₁₂ A := by
  rw [← blocks_reconstruct A, conjugate_insert₃₁_blocks]
  rfl

theorem conjugate_insert₃₁_block₃₃ (A : Matrix (Index ι κ) (Index ι κ) R)
    (Y : Matrix κ ι R) :
    block₃₃ (conjugate A (insert₃₁ Y)) = block₃₃ A - Y * block₁₃ A := by
  rw [← blocks_reconstruct A, conjugate_insert₃₁_blocks]
  rfl

/-- Two explicit rectangular shears preserve the identity bridge and kill the external block. -/
theorem two_step_elimination (A : Matrix (Index ι κ) (Index ι κ) R)
    (hA : block₁₂ A = 1) (J : Matrix ι κ R) (L : Matrix κ ι R) (hJ : L * J = 1) :
    let X := J - block₁₃ A
    let A' := conjugate A (insert₂₃ X)
    let Y := block₃₃ A' * L
    let A'' := conjugate A' (insert₃₁ Y)
    block₁₂ A'' = 1 ∧ block₃₃ A'' = 0 := by
  have hbridge : block₁₃ (conjugate A (insert₂₃ (J - block₁₃ A))) = J := by
    rw [conjugate_insert₂₃_block₁₃, hA, Matrix.one_mul]
    abel
  dsimp only
  constructor
  · rw [conjugate_insert₃₁_block₁₂, conjugate_insert₂₃_block₁₂, hA]
  · rw [conjugate_insert₃₁_block₃₃, hbridge, Matrix.mul_assoc, hJ,
      Matrix.mul_one, sub_self]

end ThreeBlocks

section RemainingSpace

variable {μ ν R : Type*} [Fintype μ] [Fintype ν]
variable [DecidableEq μ] [DecidableEq ν] [Ring R]

/-- Embed a shear into a larger matrix, leaving the remaining coordinates fixed. -/
def liftShear (N : Matrix μ μ R) : Matrix (μ ⊕ ν) (μ ⊕ ν) R :=
  Matrix.fromBlocks N 0 0 0

omit [DecidableEq μ] [DecidableEq ν] in
theorem liftShear_square (N : Matrix μ μ R) (hN : N * N = 0) :
    (liftShear N : Matrix (μ ⊕ ν) (μ ⊕ ν) R) * liftShear N = 0 := by
  simp [liftShear, Matrix.fromBlocks_multiply, hN]

omit [Fintype μ] [Fintype ν] in
private theorem one_add_liftShear (N : Matrix μ μ R) :
    (1 + liftShear N : Matrix (μ ⊕ ν) (μ ⊕ ν) R) =
      Matrix.fromBlocks (1 + N) 0 0 1 := by
  ext i j
  cases i <;> cases j <;> simp [liftShear, Matrix.fromBlocks, Matrix.one_apply]

omit [Fintype μ] [Fintype ν] in
private theorem one_sub_liftShear (N : Matrix μ μ R) :
    (1 - liftShear N : Matrix (μ ⊕ ν) (μ ⊕ ν) R) =
      Matrix.fromBlocks (1 - N) 0 0 1 := by
  ext i j
  cases i <;> cases j <;> simp [liftShear, Matrix.fromBlocks, Matrix.one_apply]

/-- Conjugate the whole matrix by a shear supported in its first major block. -/
def liftConjugate (A : Matrix (μ ⊕ ν) (μ ⊕ ν) R) (N : Matrix μ μ R) :
    Matrix (μ ⊕ ν) (μ ⊕ ν) R :=
  (1 - liftShear N) * A * (1 + liftShear N)

theorem liftConjugate_block₁₁ (A : Matrix (μ ⊕ ν) (μ ⊕ ν) R) (N : Matrix μ μ R) :
    (liftConjugate A N).toBlocks₁₁ = (1 - N) * A.toBlocks₁₁ * (1 + N) := by
  rw [← Matrix.fromBlocks_toBlocks A]
  simp [liftConjugate, one_sub_liftShear, one_add_liftShear,
    Matrix.fromBlocks_multiply]

/-- The whole remaining diagonal compression is unchanged, including all earlier zero blocks. -/
theorem liftConjugate_block₂₂ (A : Matrix (μ ⊕ ν) (μ ⊕ ν) R) (N : Matrix μ μ R) :
    (liftConjugate A N).toBlocks₂₂ = A.toBlocks₂₂ := by
  rw [← Matrix.fromBlocks_toBlocks A]
  simp [liftConjugate, one_sub_liftShear, one_add_liftShear,
    Matrix.fromBlocks_multiply]

end RemainingSpace

section FullElimination

variable {ι κ ν R : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ν] [Ring R]

/-- Full-matrix elimination with an arbitrary remaining space and arbitrary cross couplings. -/
theorem two_step_elimination_with_remainder
    (A : Matrix (Index ι κ ⊕ ν) (Index ι κ ⊕ ν) R)
    (hA : block₁₂ A.toBlocks₁₁ = 1)
    (J : Matrix ι κ R) (L : Matrix κ ι R) (hJ : L * J = 1) :
    let X := J - block₁₃ A.toBlocks₁₁
    let A' := liftConjugate A (insert₂₃ X)
    let Y := block₃₃ A'.toBlocks₁₁ * L
    let A'' := liftConjugate A' (insert₃₁ Y)
    (block₁₂ A''.toBlocks₁₁ = 1 ∧ block₃₃ A''.toBlocks₁₁ = 0) ∧
      A''.toBlocks₂₂ = A.toBlocks₂₂ := by
  dsimp only
  constructor
  · simpa only [liftConjugate_block₁₁, conjugate] using
      two_step_elimination A.toBlocks₁₁ hA J L hJ
  · simp only [liftConjugate_block₂₂]

end FullElimination

section EntryPreservation

variable {ν R : Type*} [Fintype ν] [DecidableEq ν] [Ring R]

/-- Entries away from both the supported row and supported column survive the shear unchanged. -/
theorem conjugate_entry_of_zero_row_column (A N : Matrix ν ν R) (i j : ν)
    (hrow : ∀ k, N i k = 0) (hcol : ∀ k, N k j = 0) :
    ((1 - N) * A * (1 + N)) i j = A i j := by
  rw [conjugate_expand]
  simp [Matrix.mul_apply, hrow, hcol]

end EntryPreservation

end NoEpsilon.Shear
