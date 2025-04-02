import Mathlib.Order.Defs.LinearOrder

namespace hidden

  inductive List (α : Type u) where
  | nil : List α
  | cons : α → List α → List α
  deriving Repr
namespace List

section Ignore_Me
/- The following code is used to print the lists in human readable format. -/
open Std -- standard string functions

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
  end Ignore_Me

/-- Accesses the head of a given list -/
def head {α : Type u} (as : List α) : Option α :=
  match as with
  | nil => none
  | cons a _ => some a

/-- Append the list `a₁ a₂ … aₘ` to the list `b₁ b₂ … bₙ` to obtain the list
    `a₁ a₂ … aₘ b₁ b₂ … bₙ`-/
def append {α} (as bs : List α) : List α :=
  match as with
  | nil => bs
  | cons a as => cons a (append as bs)

/-- Appending `nil` on the left has no effect -/
theorem nil_append (bs : List α) : append List.nil bs = bs := rfl

/-- Appending `nil` on the right has no effect.-/
theorem append_nil {α} (as : List α) : append as List.nil = as := by
  induction as with
  | nil => rfl              -- Base case: append [] [] = [].
  | cons a as ih => rw [append,ih]

/-- `cons` commutes with `append` in the sense that `append (cons a as) bs = cons a (append as bs)`-/
theorem cons_append {α} (a : α) (as bs : List α) : append (cons a as) bs = cons a (append as bs) := rfl

/-- `append` is an asociative operator on lists -/
theorem append_assoc {α} (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := by
  induction as with
  | nil => repeat rw[nil_append]
  | cons a as ih =>
    calc append (append (cons a as) bs) cs = append (cons a (append as bs)) cs := by rw[cons_append]
    _= cons a (append (append as bs) cs) := by rw[cons_append]
    _= cons a (append as (append bs cs)) := by rw[ih]
    _= append (cons a as) (append bs cs) := by rw[← cons_append]

/-- Counts the number of elements in a list -/
def length {α} (as : List α) : Nat :=
  match as with
  | nil => 0
  | cons _ as => 1 + length as

/-- The `length` is additive -/
theorem length_append {α} (as bs : List α) : length (append as bs) = (length as) + (length bs) := by
  induction as with
  | nil => rw[nil_append,length,Nat.zero_add]
  | cons a as ih =>
    calc length (append (cons a as) bs) = length (cons a (append as bs)) := by rw[append]
    _= 1 + length (append as bs) := by rw[length]
    _= 1 + (length as + length bs) := by rw[ih]
    _= (1 + length as) + length bs := by rw[Nat.add_assoc]
    _= length (cons a as) + length bs := by rw[← length]


section LinearOrders
/-
  We will soon say more about notation like `[LinearOrder α]` below.  For now, all you need to know
  is this enforces certain rules on terms of type `α`.  A LinearOrder behaves like the real numbers,
  meaning the following trichotomy always holds:
-/

variable (α : Type u) [LinearOrder α] (a b : α)
#check (lt_trichotomy a b : a < b ∨ a = b ∨ b < a)

/-
  In particular, in sorting, it is useful to have the following fact:
-/
variable (a_nle_b : ¬(a ≤ b))
#check (le_of_not_le : ¬(a ≤ b) → b ≤ a)
#check (le_of_not_le a_nle_b : b ≤ a)

end LinearOrders

/-
  One way to define what it means to be sorted is to make the definition inductive.
  If you pursue this route, there should be three cases.
    · The `nil` list is trivially sorted.
    · The singleton list `[a]` is trivially sorted.
    · Given a ≤ a' and sorted (cons a' as), (cons a (cons a' as)) is also sorted.
-/
/-- A list is sorted if each element is less than or equal to the next -/
inductive sorted {α : Type u} [LinearOrder α] : List α → Prop
  | nil : sorted nil
  | singleton (a : α) : sorted (cons a nil)
  | cons (a b : α) (as : List α) (a_le_b : a ≤ b) (h_sorted : sorted (cons b as)) :
     sorted (cons a (cons b as))

/-- Inserts a value into a sorted list, preserving order -/
def insert {α : Type u} [LinearOrder α] (x : α) (as : List α): List α := sorry

/-
  Prove the following simple lemmas about the interaction between insert and cons.
  You may find them helpful in the proof that `insertionSort` sorts.
-/
lemma insert_cons_le {α : Type u} [LinearOrder α] (x a : α) (as : List α) (h : x ≤ a) :
  insert x (cons a as) = cons x (cons a as) := sorry

lemma insert_cons_nle {α : Type u} [LinearOrder α] (x a : α) (as : List α) (h : ¬ (x ≤ a)) :
  insert x (cons a as) = cons a (insert x as) := sorry

/-- Sorts a list using insertion sort -/
def insertionSort {α : Type u} [LinearOrder α] (as : List α) : List α := sorry

/-
  When working with `if … then … else …`, you might find it helpful to use the `split` tactic:
    split
    case isTrue h => …
    case isFalse h => …
  You may also find the following theorem helpful.
-/

/-
  The fundamental result is to prove that a list built using `insert` is `sorted`.
  Effectively, this means we need only to show that `insert` preserves `sorted`.
  Prove this result using `induction h with`.
-/
/-- Given a `sorted` list `as`, `insert a as` is also `sorted` -/
theorem insert_preserves_sorted {α : Type u} [LinearOrder α] (a : α) (as : List α) (h : sorted as) :
  sorted (insert a as) := sorry

theorem sort_sorts {α : Type u} [LinearOrder α] (as : List α) : sorted (insertionSort as) := sorry

end List
end hidden
