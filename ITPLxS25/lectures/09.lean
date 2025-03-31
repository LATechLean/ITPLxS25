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

/-
  Note that the motive is not always required.  In this example, our return
  type is not a dependent type, so Lean doesn't need the motive.
-/
def prod_example (p : Bool × Nat) : Nat :=
  --Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))
  Prod.casesOn p (fun b n => cond b (2 * n) (2 * n + 1))
#eval prod_example (true, 3)
#eval prod_example (false, 3)

end Constructors

section Constructing_Nat
/-
  The inductive types above serve merely to package data.  In those examples,
  the constructors depend only on types that have already been defined.
  However, Lean allows us to define inductive types with constructors that
  depend on the type being defined.

  A simple example is the construction of the natural numbers.  Set theoretically,
  the number zero is defined to be the empty set, and all other numbers are
  defined recursively via the successor function, which states that
    n + 1 = n ∪ {n}
  In practice, this means
    0 = ∅
    1 = {0} = {∅}
    2 = {0,1} = {∅, {∅}}
    3 = {0,1,2} = {∅, {∅}, {∅, {∅}}}
    ⋮
    n = {1,2,3,…,n-1}
    ⋮
  In lean, this recursion is simple
-/

namespace hidden

inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr -- Constructs objects into text.

/-
  The following chunk of code is just used to pretty print our numbers.
-/
def toNat : hidden.Nat → _root_.Nat
  | hidden.Nat.zero => 0
  | hidden.Nat.succ n => toNat n + 1

instance : Repr hidden.Nat where
  reprPrec n _ := (toString (toNat n))

#eval Nat.zero                                    -- 0
#eval Nat.succ Nat.zero                           -- 1
#eval Nat.succ (Nat.succ Nat.zero)                -- 2
#eval Nat.succ (Nat.succ (Nat.succ Nat.zero))     -- 3


/-
  Similar to the previous constructs, we have two elimination rules for
  our natural numbers depending on the form
    · n is zero
    · n is the successor of something non-zero (i.e. n-1).
  The same match … with construct can be used to define basic functions
  on our type recursively.
-/
namespace Nat
/-
  For a binary operation on Nat, such as addition, we will need to
  make a choice as to which slot we want to use for our recursion.
  We arbitrarily make the choice to the take the left.

  In practice, this means we start by defining
    0 + n = n.
  Then we can define
    · 1 + n as the successor of 0 + n = n,
    · 2 + n as the successor of 1 + n,
    · 3 + n as the successor of 2 + n,
    ⋮
    · m + n as the successor of (m-1) + n
-/
def add (m n : Nat) : Nat :=
match m with
| zero => n
| succ m => Nat.succ (add m n)

/-
  We can register the usual addition symbol using infixl to
  indicate that our + is left associative.
-/
infixl:65 "+" => add

#eval Nat.zero + (succ Nat.zero)                   -- 0 + 1 = 1
#eval add Nat.zero (succ Nat.zero)                 -- 0 + 1 = 1

#eval  (succ Nat.zero) + (succ (succ Nat.zero))    -- 1 + 2 = 3
#eval add (succ Nat.zero) (succ (succ Nat.zero))   -- 1 + 2 = 3

/-
  Lean is able to infer facts about addition automatically, so long as
  they are stated relative to the left slot.
-/

/-- For all `n : Nat`, `0 + n = n`-/
theorem zero_add (n : Nat) : add Nat.zero n = n := rfl
/-- For all `m n : Nat`, `(m + 1) + n = (m + n) + 1`-/
theorem succ_add (m n : Nat) : add (succ m) n = succ (add m n) := rfl

/-
  However, it cannot infer that m + 0 = m automatically.  In order to accomplish
  this task, we will need to use the principle of induction.
-/

/-- For all `m : Nat`, `m + 0 = m`.-/
theorem add_zero (m : Nat) : add m Nat.zero = m := by
  induction m with
  | zero => rfl       -- Base case m = 0: 0 + 0 = 0 := rfl
  | succ m ih =>      -- Assume m + 0 = m.  Prove (m + 1) + 0 = m + 1.
    rw [add,ih]

/-
  This proof is essentially the observation that,
    (m + 1) + 0 := add (succ m) + Nat.zero
                 = succ (add m Nat.zero)      (by definition of add)
                 = succ m                     (by the induction hypothesis)
-/

/-
  Exercise: Complete the following proofs using induction (on m).
-/

/-- For all `m n : Nat`, `m + (n + 1) = (m + n) + 1`-/
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := sorry

/--For all `m, n : Nat`, `(m + n) + k = m + (n + k)` -/
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := sorry
/-- For all `m,n : Nat`, `m + n = n + m` -/
theorem add_comm (m n : Nat) : add m n = add n m := sorry

end Nat
end hidden
end Constructing_Nat

section Lists
/-
  In Lean, a list is also implemented as an inductive type.  A nonempty
  list of elements of type α : Type u consists of two pieces of information:
    · an element α, commonly referred to as the head of the list
    · a list (List α), commonly referred to as the tail of the list.
-/

namespace hidden
  inductive List (α : Type u) where
  | nil : List α
  | cons : α → List α → List α
  deriving Repr
namespace List

/- The following code is used to print the lists in human readable format. -/
open Std -- if you need standard string functions

/-- Helper that produces the inner part of the list (after the first element),
    producing a string of the form ", a, b, c". -/
def reprCommaAux {α : Type u} [Repr α] : List α → String
  | nil       => ""
  | cons a as => ", " ++ Format.pretty (repr a) ++ reprCommaAux as

/-- Convert the entire list to a string in the format "[a, b, c]". -/
def reprComma {α : Type u} [Repr α] (l : List α) : String :=
  match l with
  | nil       => "[]"
  | cons a as => "[" ++ Format.pretty (repr a) ++ reprCommaAux as ++ "]"

/-- Override the default Repr instance for hidden.List to use our comma‐separated format. -/
instance {α : Type u} [Repr α] : Repr (List α) where
  reprPrec l _ := reprComma l

#eval @List.nil Nat
#eval List.cons 1 List.nil
#eval List.cons 1 (List.cons 2 List.nil)
/-
  Similar to the natural numbers, we can define common operations on a list.
-/
/-- Append the list `a₁ a₂ … aₘ` to the list `b₁ b₂ … bₙ` to obtain the list
    `a₁ a₂ … aₘ b₁ b₂ … bₙ`-/
def append {α} (as bs : List α) : List α :=
  match as with
  | nil => bs
  | cons a as => cons a (append as bs)

#eval append (List.cons 1 List.nil) (List.cons 2 List.nil) -- append [1] [2] = [1,2]

/-
  Of course, we might like to know our append function actually does what we think it does.
  Some of the functionality is definitionally true.
-/
/-- If `as = []`, then `append as bs = bs`. -/
theorem nil_append (bs : List α) : append List.nil bs = bs := rfl


theorem append_nil {α} (as : List α) : append as List.nil = as := by
  induction as with
  | nil => rfl              -- Base case: append [] [] = [].
  | cons a as ih =>
    rw [append,ih]

theorem cons_append (a : α) (as bs : List α) : append (cons a as) bs = cons a (append as bs) := by
  induction as with
  | nil => rfl
  | cons x xs ih =>
    calc
    append (cons a (cons x xs)) bs = cons a (append (cons x xs) bs) := by rw[append]
    _= cons a (cons x (append xs bs)) := by sorry
    _= cons a (append (cons x xs) bs) := by sorry
    _= append (cons a (cons x xs)) bs := by sorry

end List
end hidden
end Lists
