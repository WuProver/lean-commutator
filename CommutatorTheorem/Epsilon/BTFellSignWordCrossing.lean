import CommutatorTheorem.Epsilon.BTFellCountLocal

/-!
# Sign-word control across a threshold crossing

Negating a whole suffix preserves every internal sign change.  Only its
boundary with the unchanged prefix can change, hence the total variation
changes by at most one.
-/

namespace CommutatorTheorem.BTFellSignWordCrossing

/-- Adjacent changes after a fixed preceding sign. -/
def changesFrom (a : SignType) : List SignType → ℕ
  | [] => 0
  | b :: l => (if a ≠ b then 1 else 0) + changesFrom b l

/-- The number of adjacent changes in a sign word. -/
def signChanges : List SignType → ℕ
  | [] => 0
  | a :: l => changesFrom a l

theorem changesFrom_eq_destutter_length_sub_one
    (a : SignType) (l : List SignType) :
    changesFrom a l = (l.destutter' Ne a).length - 1 := by
  induction l generalizing a with
  | nil => simp [changesFrom]
  | cons b l ih =>
      by_cases hab : a ≠ b
      · rw [changesFrom, if_pos hab,
          List.destutter'_cons_pos (l := l) hab, List.length_cons]
        have ihb := ih b
        have hne : l.destutter' Ne b ≠ [] := by
          intro h
          have := List.mem_destutter' l Ne b
          simpa [h] using this
        have hpos : 0 < (l.destutter' Ne b).length :=
          List.length_pos_of_ne_nil hne
        omega
      · have hab' : a = b := not_ne_iff.mp hab
        subst b
        rw [changesFrom, if_neg (by simp), zero_add,
          List.destutter'_cons_neg (l := l) (by simp)]
        exact ih a

theorem signChanges_eq_destutter_length_sub_one (l : List SignType) :
    signChanges l = (l.destutter Ne).length - 1 := by
  cases l with
  | nil => simp [signChanges]
  | cons a l =>
      change changesFrom a l = _
      simpa [List.destutter] using changesFrom_eq_destutter_length_sub_one a l

theorem changesFrom_neg (a : SignType) (l : List SignType) :
    changesFrom (-a) (l.map (- ·)) = changesFrom a l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
      simp only [List.map_cons, changesFrom]
      rw [ih b]
      by_cases hab : a = b <;> simp [hab]

theorem signChanges_neg (l : List SignType) :
    signChanges (l.map (- ·)) = signChanges l := by
  cases l with
  | nil => rfl
  | cons a l =>
      simp [signChanges, changesFrom_neg]

theorem changesFrom_append_neg_suffix_balanced
    (a : SignType) (u v : List SignType) :
    changesFrom a (u ++ v) ≤
        changesFrom a (u ++ v.map (- ·)) + 1 ∧
      changesFrom a (u ++ v.map (- ·)) ≤
        changesFrom a (u ++ v) + 1 := by
  induction u generalizing a with
  | nil =>
      cases v with
      | nil => simp
      | cons b v =>
          simp only [List.nil_append, List.map_cons, changesFrom]
          rw [changesFrom_neg b v]
          split_ifs <;> omega
  | cons b u ih =>
      simp only [List.cons_append, changesFrom]
      obtain ⟨h₁, h₂⟩ := ih b
      omega

/-- Negating an arbitrary suffix changes the adjacent-variation count by at
most one. -/
theorem signChanges_append_neg_suffix_balanced (u v : List SignType) :
    signChanges (u ++ v) ≤ signChanges (u ++ v.map (- ·)) + 1 ∧
      signChanges (u ++ v.map (- ·)) ≤ signChanges (u ++ v) + 1 := by
  cases u with
  | nil =>
      rw [List.nil_append, List.nil_append, signChanges_neg]
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  | cons a u =>
      simpa [signChanges] using changesFrom_append_neg_suffix_balanced a u v

end CommutatorTheorem.BTFellSignWordCrossing
