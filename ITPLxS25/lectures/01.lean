import Mathlib.tactic
namespace Lecture_01
/-
  Simple Type Theory
-/

/- Define some constants. -/
namespace Simple_Type_Theory

def m : ℕ := 1       -- m is a ℕural number
def n : ℕ := 0       -- Lean considers 0 a natural number...
def b₁ : Bool := true  -- Boolean type.  Use, e.g., "\1" to typeset subscripts
def b₂ : Bool := false

/- Check their types. -/

#check 1
#check (m : ℕ)
#check (n : ℕ)
#check (n + 0 : ℕ)
#check (m * (n + 0): ℕ)
#check (b₁ : Bool)
#check (b₁ && b₂ : Bool)   -- "&&" is the Boolean and
#check (b₁ || b₂ : Bool)   -- Boolean or
#check (true : Bool)       -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b₁ && b₂      -- false
#eval b₁ || b₂      -- true

#check ℕ → ℕ      -- type the arrow as "\to" or "\r"
#check ℕ -> ℕ     -- alternative ASCII notation

#check ℕ × ℕ      -- type the product as "\times"
#check Prod ℕ ℕ   -- alternative notation

#check ℕ → ℕ → ℕ
#check ℕ → (ℕ → ℕ)  --  same type as above

#check ℕ × ℕ → ℕ
#check (ℕ → ℕ) → ℕ -- a "functional"

#check (Nat.succ : ℕ → ℕ)
#check ((0, 1) : ℕ × ℕ)
#check (Nat.add : ℕ → ℕ → ℕ)

#check (Nat.succ 2 : ℕ)
#check (Nat.add 3 : ℕ → ℕ)
#check (Nat.add 5 2 : ℕ)

/-

-/
#check (((5, 9).1 : ℕ) : ℕ)
#check ((5, 9).2 : ℕ)    -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9

end Simple_Type_Theory


/-
  Types as objects
-/
namespace Types_as_Objects
#check Nat               -- The natural numbers together with 0.
#check ℕ                 -- Also the natural numbers with 0.
                         -- Use "\N" to typeset the math blackboard bold N.
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check (α : Type)
#check (F α : Type)
#check (F ℕ : Type)
#check (G α : Type → Type)
#check (G α β : Type)
#check (G α ℕ  : Type)

#check (Prod α β : Type)
#check (α × β : Type)

#check (Prod ℕ ℕ : Type)
#check (ℕ × ℕ : Type)

#check (Prop : Type)
#check Type      -- Type 1

#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5

#check Type
#check Type 0

#check List    -- List.{u} (α : Type u) : Type u

universe u

def H (α : Type u) : Type u := Prod α α

#check (H : Type u → Type u)

end Types_as_Objects

/-
  Function Abstraction and Evaluation
-/
namespace Function_Abstraction_and_Evaluation
#check (fun (x : ℕ) => x + 5 : ℕ → ℕ)
#check (λ (x : ℕ) => x + 5 : ℕ → ℕ)       -- λ and fun mean the same thing
#check (fun x => x + 5 : ℕ → ℕ)           -- ℕ inferred
#check (λ x => x + 5 : ℕ → ℕ)             -- ℕ inferred

#eval (λ x : ℕ => x + 5) 10               -- 15

#check (fun x : ℕ => fun y : Bool => if not y then x + 1 else x + 2 : ℕ → Bool → ℕ)
#check (fun (x : ℕ) (y : Bool) => if not y then x + 1 else x + 2 : ℕ → Bool → ℕ)
#check (fun x y => if not y then x + 1 else x + 2 : ℕ → Bool → ℕ)

def f (n : ℕ) : String := toString n
def g (s : String) : Bool := s.length > 0

#check (fun x : ℕ => x : ℕ → ℕ)
#check (fun x : ℕ => true : ℕ → Bool)
#check (fun x : ℕ => g (f x) : ℕ → Bool)
#check (fun x => g (f x) : ℕ → Bool)

#check (fun (g : String → Bool) (f : ℕ → String) (x : ℕ) => g (f x) : (String → Bool) → (ℕ → String) → ℕ → Bool)

#check (fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x) : (α β γ : Type) → (β → γ) → (α → β) → α → γ)

#check ((fun x : ℕ => x) 1 : ℕ)
#check ((fun x : ℕ => true) 1 : Bool)

#check
  ((fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) ℕ String Bool g f 0 : Bool)

#eval (fun x : ℕ => x) 1     -- 1
#eval (fun x : ℕ => true) 1  -- true

end Function_Abstraction_and_Evaluation

/-
  Definitions
-/
namespace Definitions

/-
  Suppose we ONLY know how to add two natural numbers.
  Define a function double : ℕ → ℕ that doubles the input.
  Check that double 3 = 6
-/
def double (x : ℕ) : ℕ := sorry

/-
  Define a function double₂ : ℕ → ℕ that doubles the input using either λ or fun.
-/
def double₂ := sorry

-- Make sure it type checks!
#check (double₂ : ℕ → ℕ)

def pi := 3.141592654

/-
  Define a function add : ℕ → ℕ that adds two numbers.
  Check that add 3 2 = 5
-/
def add (x y : ℕ) := sorry

/-
  Use these functions to double 3 and then add, then add 9.
-/

/-
  The function greater : ℕ → N → ℕ returns the larger of the two inputs.
-/
def greater (x y : ℕ) :=
  if x > y then x
  else y

/-
  Write a function
    doTwice : (ℕ → ℕ) → ℕ → N
  that applies a a function f : ℕ → ℕ to x : ℕ twice.
-/
def doTwice (f : ℕ → ℕ) (x : ℕ) : ℕ := sorry

-- Make sure it type checks!
#check (doTwice : (ℕ → ℕ) → ℕ → ℕ)

/-
  Evaluate doTwice double 2.
    What is the result?
    Is it what you expected?
-/

/-
  Write a function
    compose (α β γ : Type) → (β → γ) → (α → β) → α → γ
  that applies the composition of f : α → β an g : β → γ to x : α.
-/
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := sorry

/-
  Suppose we know how to multiply two natural numbers.
  Write a function
    square : ℕ → ℕ
  that squares the input.
-/
def square (x : ℕ) : ℕ := sorry

/-
  Evaluate the expression (2*x)^2 at x = 3 using the functions
    · compose,
    · double, and
    · square
  defined above.
-/

end Definitions

/-
  Local Definitions
-/
namespace Local_Definitions

#check let y := 2 + 2; y * y   -- ℕ
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : ℕ) : ℕ :=
  let y := x + x; y * y
  /-
    This is equivalent to
      (x + x) * (x + x) = (x + x)^2
                        = x^2 + 2*x^2 + x^2
                        = 4*x^2
  -/

#eval twice_double 2   -- 16

#check (let y := 2 + 2; let z := y + y; z * z : ℕ)
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64
/-
  This is equivalent to
    ((2 + 2) + (2 + 2))*((2 + 2) + (2 + 2)) = 8 * 8 = 64
-/

/-
  Can omit semi-colon by using a newline
-/
def t (x : ℕ) : ℕ :=
  let y := x + x
  y * y


#eval t 2

def foo := let a := ℕ; fun x : a => x + 2
#check (foo : ℕ → ℕ)
/-
  def bar := (fun a => fun x : a => x + 2) ℕ
-/

end Local_Definitions
/-
  Variables and Sections
-/

namespace Variables_and_Sections

section

/-
  We can define functions by explicitly
  listing all the components in the declaration:
-/
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
end

section

/-
  We can make these more compact using variables
  for the types.
-/
variable (α β γ : Type)

def compose₂ (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice₂ (h : α → α) (x : α) : α :=
  h (h x)

def doThrice₂ (h : α → α) (x : α) : α :=
  h (h (h x))

/-
  We could even go so far as to use variables for the functions.
-/

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose₃ := g (f x)
def doTwice₃ := h (h x)
def doThrice₃ := h (h (h x))

/-
  We can see these are definitionally equal using #print.
-/

#print compose
#print compose₂
#print compose₃
#print doTwice
#print doThrice
end

/-
  We can provide a lexical scope for variables using sections.
-/
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose₄ := g (f x)
  def doTwice₄ := h (h x)
  def doThrice₄ := h (h (h x))
end useful

#check α -- The variable disappears outside the section
#check compose₄ -- The function remains.
#print compose₄ -- It remains the same, even though the variable is out of scope.

end Variables_and_Sections

/-
  Namespaces
-/

namespace Namespaces

namespace Foo
  def a : ℕ := 5
  def f (x : ℕ) : ℕ := x + 7

  def fa : ℕ := f a

  /-
    Inside a namespace, we can use short names.
  -/
  #check a
  #check f
  #check fa
  #check ffa
  /-
    We can also use the fully qualified name
  -/
  #check Foo.fa
end Foo

/-
  Outside the namespace, we must use the fully qualified name.
-/
#check a
#check f
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

/-
  We can use the short names if we open the namespace.
-/
open Foo

#check a
#check f
#check fa
#check Foo.fa

#check List.nil
#check List.cons
#check List.map

open List

#check nil
#check cons
#check map

/-
  We can reopen namespaces later.
-/
namespace Foo
  #check a

  /-
    We can also nest namespaces.
  -/
  namespace Bar
    def ffa : ℕ := f (f a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : ℕ := f (f a)
  #check ffa
  #check Bar.ffa
end Foo

end Namespaces
