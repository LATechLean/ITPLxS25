import Mathlib

namespace Homework00

/-
  Suppose we ONLY know how to add two natural numbers.
  Define a function
    double : ℕ → ℕ
  that doubles the input.
-/

def double (x : ℕ) : ℕ :=
  sorry

/-
  Define a function
    add : ℕ → ℕ
  that adds two numbers.
-/

def add (x y : ℕ) : ℕ :=
  sorry

/-
  Suppose that α : Type.
  Write a function
    doTwice : (α → α) → α → α
  that applies a function f : α → α to a : α two times.
-/
def doTwice (α : Type) (f : α → α) (a : α) : α :=
  sorry

/-
  Suppose that α : Type.
  Write a function
    doThrice : (α → α) → α → α
  that applies a function f : α → α to a : α three times.
-/
def doThrice (α : Type) (f : α → α) (a : α) : α :=
  sorry

/-
  Write a function
    compose (α β γ : Type) → (β → γ) → (α → β) → α → γ
  that applies the composition of f : α → β an g : β → γ to x : α.
-/
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  sorry

/-
  Suppose we know how to multiply two natural numbers.
  Write a function
    square : ℕ → ℕ
  that squares the input.
-/
def square (x : ℕ) : ℕ :=
  sorry

end Homework00
