namespace Lecture_09

section InductiveTypes

/-
  Inductive types in Lean provide a way to define objects inductively
  by providing a list of constructors.
-/

section EnumeratedTypes
/-
  The simplest kind is an Enumerated Type, which is basically just a
  finite set.
-/
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
 deriving Repr

namespace Weekday

/-
  We can define functions on enumerated types by exhaustion.
  The match … with construction is useful here.
-/
def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday => 1
  | monday => 2
  | tuesday => 3
  | wednesday => 4
  | thursday => 5
  | friday => 6
  | saturday => 7

def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

/-
  If we want to prove things about functions defined on enumerated
  types, we frequently prove things by exhaustion.
-/

example : next (previous Weekday.friday) = friday := rfl

def next_previous₀ (d : Weekday) : next (previous d) = d :=
match d with
  | sunday => rfl
  | monday => rfl
  | tuesday => rfl
  | wednesday => rfl
  | thursday => rfl
  | friday => rfl
  | saturday => rfl

/-
  When the type is explicitly enumerated, this is tedious.  Fortunately,
  the sequencing combinator makes short work of this sort of thing.
-/

def next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

def previous_next (d : Weekday) : previous (next d) = d := by
  cases d <;> rfl
end Weekday

namespace hidden
namespace MyBool

/-
  A less trivial example is the Boolean type. It has two elements:
  `true` and `false`.
-/

inductive Bool where
  | false : Bool
  | true : Bool

namespace Bool

/-
  The logical operators ∧, ∨, ¬, →, ↔ can all be defined exhaustively.
  Essentially, this is just recording the truth value.
-/

def not (a : Bool) :=
  match a with
  | true => false
  | false => true

#eval not true
#eval not false

def and (a b : Bool) :=
  match a with
  | true => b
  | false => false

#eval and true true
#eval and true false
#eval and false true
#eval and false false

def or (a b : Bool) :=
  match a with
  | true => true
  | false => b

#eval or true true
#eval or true false
#eval or false true
#eval or false false

def implies (a b : Bool) :=
  match a with
  | true => b
  | false => true

#eval implies true true
#eval implies true false
#eval implies false true
#eval implies false false

def if_and_only_if (a b : Bool) :=
  match a with
  | true => b
  | false => not b

#eval if_and_only_if true true
#eval if_and_only_if true false
#eval if_and_only_if false true
#eval if_and_only_if false false

end Bool
end MyBool
end hidden

end EnumeratedTypes

section Constructors

/-
  We can make more elaborate inductive types by allow arguments in
  our constructors.
-/

namespace hidden

/-
  The type Prod α β represents the type-theoretic analogue of the
  Cartesian product of two sets.  We can construct elements of
  type Prod α β from
    · a term a : α, and
    · a term b : β

-/
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

section
variable (α : Type u) (β : Type v) (a : α) (b : β)
#check (Prod.mk a b : Prod α β)
end

/-
  We can define functions on the product such as projections.
  Again, the match … with construction is useful.
-/

namespace Prod

def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a _ => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk _ b => b

end Prod

/-
  The type Sum α β represents the type-theoretic analogue of the
  disjoint union two sets. We can construct elements of type Sum α β
  from
    · terms a : α using introduction on the left, or
    · terms b : β using introduction on the right
-/

inductive Sum (α : Type u) (β : Type v)
  | inl : α → Sum α β
  | inr : β → Sum α β

section
variable (α : Type u) (β : Type v) (a : α) (b : β)
#check (Sum.inl a : Sum α β)
#check (Sum.inr b : Sum α β)
end

/-
  Propositions are also defined inductively.
-/

/-- The `False` proposition cannot be proven. -/
inductive False : Prop

/-- The `True` proposition is always true.-/
inductive True : Prop where
  | intro : True

/-- The conjunction of two propositions.-/
inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

/-- The disjunction of two propositions. -/
inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

/- Disjunctive elimination can be achieved using match … with -/
example (a b : Prop) : Or a b → Or b a :=
  λ h ↦ match h with
  | Or.inl ha => Or.inr ha
  | Or.inr hb => Or.inl hb

/- Or we can use either match or cases in a tactics proof. -/
example (a b : Prop) : Or a b → Or b a := by
  intro h
  /- match h with
  | Or.inl ha => exact Or.inr ha
  | Or.inr hb => exact Or.inl hb -/
  cases h with
  | inl ha => exact Or.inr ha
  | inr hb => exact Or.inl hb

/-
  A simple inductive version of Iff should have one introduction rule that
  requires a proof of each direction.
-/
inductive Iff (a b : Prop) : Prop where
  | intro : (a → b) → (b → a) → Iff a b

example (a b : Prop) (hab : a → b) (hba : b → a) : Iff a b :=
  Iff.intro hab hba

/-
  Elimination for the Iff construct can also be achieved by match or cases.
-/
example (a b: Prop) (ha : a) (haa : Iff a b) : b :=
  match haa with
  | Iff.intro mp _ => mp ha

example (a b: Prop) (hb : b) (haa : Iff a b) : a := by
  cases haa with
  | intro _ mpr => exact mpr hb

end hidden

end Constructors

end InductiveTypes

end Lecture_09
