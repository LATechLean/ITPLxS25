import Mathlib

namespace Lecture_08

section Generalize

/-
  The generalize tactic can be used to introduce names for terms.
-/
example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl
/-
  WARNING: generalize is not safe.  You can transform the goal into one that
  cannot be proven.
-/
example : 2 + 3 = 5 := by
  generalize 3 = x
  revert x
  sorry

end Generalize

section Cases
/-
  The cases tactic can be used on disjunctions to do a proof by cases.

-/

--Structured cases
example (p q : Prop) : p ∨ q → q ∨ p := by
intro h
cases h with
| inl hp => apply Or.inr; exact hp
| inr hq => apply Or.inl; exact hq

-- Alternative structure
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inl hp => exact Or.inr hp
  case inr hq => exact Or.inl hq

-- Unstructured cases
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

/-
  Unstructured cases are especially nice when combined with repeat.
-/

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  /- assumption
  assumption -/
  repeat assumption

/-
  NOTE: Cases can also be used to destruct a conjunction into its two
        components.
-/

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  |intro hp hq => exact ⟨hq, hp⟩
end Cases

section Sequencing

/-
  The combinator tac₁ <;> tac₂ is used to apply tac₂ to all subgoals
  that are created by tac₁.
-/

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
end Sequencing

section Constructor
/-
  The constructor tactic is the tactic version of ⟨_,_⟩.  It is effective for
  constructing terms with a single introduction rule.
    · Conjunction,
    · If and only If,
    · Existential statements,
-/

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h
  constructor <;> assumption

end Constructor

section Contradiction
/-
  The contradiction tactic is like assumption, but for proving False.
-/

example (p q : Prop) : p ∧ ¬p → q := by
  intro h
  cases h
  contradiction

end Contradiction

section Calculation
/-
  Calculation
-/

/-
  Many of the proofs we write will eventually boil down to some sort
  of mundane computation.  As a simple example,
    (a + b)^2 = a^2 + 2ab + b^2.
  The simplest sort of proof would be to chain together a string of
  equalities:
    (a + b)^2 = (a + b)*(a + b)
              = (a + b)*a + (a + b)*b
              = a*a + b*a + a*b + b*b
              = a^2 + a*b + a*b + b^2
              = a^2 + 2*a*b + b^2
  We move from one step to the other using simple equalities.  Lean
  offers a similar way to do this using the calc keyword.

  Lean has *many* different equalities.  Here are a few of the ones
  that are useful for proving basic things.
-/

variable (a b c: ℕ)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : 2 * a = a + a := Nat.two_mul a
example : a * 2 = a + a := Nat.mul_two a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
example : a^2 = a*a := Nat.pow_two a

example : (a + b)^2 = a^2 + 2*a*b + b^2 :=
  calc (a + b)^2 = (a + b) * (a + b) := Nat.pow_two (a + b)
  _= (a + b) * a + (a + b) * b := Nat.mul_add (a + b) a b
  _= a*a + b*a + (a + b) * b := by rw[Nat.add_mul a b a]
  _= a*a + b*a + a*b + b*b := by linarith[Nat.add_mul a b b]
  _= a*a + a*b + a*b + b*b := by linarith[Nat.add_comm b a]
  _= a*a + 2*a*b + b*b := by linarith[Nat.two_mul]
  _= a^2 + 2*a*b + b^2 := by simp[Nat.pow_two]

end Calculation

section Match
/-
  The match construction that we have seen in the past is also
  available for use in tactic blocks.
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  case mp =>
    intro h
    match h with
    | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  case mpr =>
    intro h
    match h with
    | Or.inl ⟨_,_⟩ => constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨_,_⟩ => constructor; assumption; apply Or.inr; assumption

/-
  Of course, we have already seen that intro provides this structure
  without the extra call to match.
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  -- Split on the cases p, q and p, r
  case mp =>
    intro
    | ⟨_,Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_,Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  case mpr =>
    intro
    | Or.inl ⟨_,_⟩ => constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨_,_⟩ => constructor; assumption; apply Or.inr; assumption
end Match

section Exists
/-
  The exists tactic can be used to prove an existential statement.
-/

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro
  | ⟨x, h⟩ => exists x; apply Or.inl; assumption
end Exists


section Combinators
/-
  In addition to the combinators we have already seen (by, <;>, repeat),
  the combinator
    first | t₁ | t₂ | … | tₙ
  applies each of t₁, t₂, …, tₙ until one of them succeeds, or the whole
  attempt fails.
-/
example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

/-
  The combinator try will apply a tactic and always report success.
  This can be useful when attempting to automate similar steps, such as
  proving iterated conjunctions.

  In the example below, constructor opens subgoals of p and p ∧ q.
  We can use the sequencing combinator with
    try constructor
  to apply constructor in the both cases and to fail silently on the first.
  This results in the subgoals p, q, and r, each of which are proven by
    assumption.
-/

example (p q r : Prop) (hp :p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

/-
  The all_goals combinator applies a tactic to all open goals in parallel.
-/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)  -- try constructor is needed because one of the goals is just p.
  all_goals assumption

/-
  The any_goals combinator attempts to apply a tactic to all of the open goals
  and succeeds if at least one application is successful.
-/

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  all_goals assumption

/-
  This is useful when we need to prove silly equalities involving parentheses.
-/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

end Combinators

end Lecture_08
