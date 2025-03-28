import Mathlib

namespace Homework_02

variable (α : Type) (p q : α → Prop)

theorem exercise_1 : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  sorry

theorem exercise_2 : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  sorry

theorem exercise_3 : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  sorry

variable (r : Prop)

theorem exercise_4 : α → ((∀ x : α, r) ↔ r) :=
  sorry

/-
  NOTE: The forward direction requires Classical.em!
-/
#check (Classical.em r : r ∨ ¬r)

theorem exercise_5 : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  sorry

theorem exercise_6 : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  sorry


theorem exercise_7 : (∃ x : α, r) → r :=
  sorry

theorem exercise_8 (a : α) : r → (∃ x : α, r) :=
  sorry

theorem exercise_9 : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  sorry

theorem exercise_10 : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  sorry

theorem exercise_11 : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  sorry

end Homework_02
