namespace Lecture_11

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
theorem nil_append (bs : List α) : append List.nil bs = bs := sorry

/-- Appending `nil` has no effect.-/
theorem append_nil {α} (as : List α) : append as List.nil = as := sorry

/-- `cons` commutes with `append` in the sense that `append (cons a as) bs = cons a (append as bs)`-/
theorem cons_append {α} (a : α) (as bs : List α) : append (cons a as) bs = cons a (append as bs) := sorry

theorem append_assoc {α} (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := sorry

def length {α} (as : List α) : Nat := sorry

theorem length_append {α} (as bs : List α) : length (append as bs) = (length as) + (length bs) := sorry

end List
end hidden
end Lists

end Lecture_11
