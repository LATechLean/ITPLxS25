import Mathlib

namespace Lecture_02
section Definitions

/-
  Having to write out these expressions over and over again is also quite cumbersome.
  We can assign the name t to a term of type T with value v in Lean using the def keyword
    def (t : T) := v
-/

def m : ℕ := 1
def n := 0                -- Lean can often infer the type.
def b₁ : Bool := true            -- use "\1" to typeset the subscript.
def b₂ := false
def s := "Hello, world!"

/-
  When the term we want to define is a function, we can omit the lambda notation.
    · Arguments to our function appear after the name and before a colon.
    · The type of the output appears after the colon.
    · The output term appears after the := symbol.
-/
def first (x y : ℕ) : ℕ := x
def second (x y : ℕ) : ℕ := y

#check (first : ℕ → ℕ → ℕ)
#eval first 1 2

#check (second : ℕ → ℕ → ℕ)
#eval second 1 2

def add_one (x : ℕ) := x + 1
#check (add_one : ℕ → ℕ)

def ev_1 (f : ℕ → ℕ) := f 1
#check (ev_1 : (ℕ → ℕ) → ℕ)

#check (ev_1 add_one : ℕ)
#eval ev_1 add_one

/-
  Suppose we ONLY know how to add two natural numbers.
  Define a function
    double : ℕ → ℕ
  that doubles the input.
  Use #eval to check that the result of double 3 is 6.
-/
def double (x : ℕ) : ℕ := sorry


/-
  Define a function
    add : ℕ → ℕ
  that adds two numbers.
  Check that add 3 2 = 5
-/
def add (x y : ℕ) : ℕ := sorry

/-
  Use these functions to double 3 and then add, then add 9.
-/

/-
  Write a function
    greater : ℕ → ℕ → ℕ
  that returns the larger of the two inputs.
-/
def greater (x y : ℕ) : ℕ := sorry

/-
  Suppose that α : Type.
  Write a function
    doTwice : (α → α) → α → α
  that applies a function f : α → α to a : α two times.
-/
def doTwice (α : Type) (f : α → α) (a : α) : α := sorry

#check (doTwice : (α : Type) → (α → α) → α → α)

/-
  Suppose that α : Type.
  Write a function
    doThrice : (α → α) → α → α
  that applies a function f : α → α to a : α three times.
-/
def doThrice (α : Type) (f : α → α) (a : α) : α := sorry

/-
  Use #eval to evaluate
    · doTwice double 2.
    · doThrice double 2.
  Make sure the result is what you expect!
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
  Use #eval to evaluate the expression (2*x)^2 at x = 3 using the functions
    · compose,
    · double, and
    · square
  defined above.
-/
end Definitions

section Local_Definitions

/-
  The let keyword in Lean allows us to simplify expressions using a local definition.
  The idea behind its usage in Lean is the same as when you're writing proof: to reduce
  clutter and improve readability. The construct
    let a := t₁; t₂
  or
    let a := t₁
    t₂
  is definitionally equivalent to replacing every occurence of a in the term t₂ by the term t₁.

  For example, suppose we wanted to add a value to itself, then multiply it by itself.
  We could write this expression out.
-/

#eval (2 + 2)*(2 + 2)

/-
  The let construct allows us to reduce this
-/

#eval let y := 2 + 2; y*y

/-
  We could of course nest this to make it a little clearer what's happening.
-/

#eval let x := 2; let y := x + x; y*y

/-
  Note that unlike the def keyword, the definition is out of scope immediately.
-/

#check x
#check y
/-
  We can use this in definitions.
-/

def twice_double (x : ℕ) : ℕ :=
  let y := x + x; y * y

/-
  We can omit the semicolon(s) if we use a newline.
-/

def twice_double₂ (x : ℕ) : ℕ :=
  let s := x + x
  s * s


#eval twice_double 2   -- 16
#eval twice_double₂ 2  -- Also 16.
end Local_Definitions

section Variables_and_Sections

/-
  Recall the function definitions above:
  domain and codomain of each of our functions in the definition:
    def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ
    def doTwice (α : Type) (h : α → α) (x : α) : α
    def doThrice (α : Type) (h : α → α) (x : α) : α := sorry
  The types α, β, and γ appear in each of these.  It is cumbersome to
  have to keep writing these explicitly in every one of our definitions.

  We can use the variable keyword to reduce some of the clutter here.
  The exact same definitions above will work for these new functions.
-/

variable (α β γ : Type)

def compose₂ (g : β → γ) (f : α → β) (x : α) : γ := sorry
def doTwice₂ (h : α → α) (x : α) : α  := sorry
def doThrice₂ (h : α → α) (x : α) : α := sorry

/-
  We could even go so far as to use variables for the functions.
  Again, pasing the same definition will provide a definitionally
  equal function in each case.
-/

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose₃  := sorry
def doTwice₃  := sorry
def doThrice₃ := sorry

/-
  We can actually see these are definitionally equal using #print.
-/

#print compose
#print compose₂
-- #print compose₃

#print doTwice
#print doTwice₂
#print doTwice₃

#print doThrice
#print doThrice₂
#print doThrice₃

/-
  Sometimes, we don't want these variables to persist beyond the definitions.
  Sections are useful for limiting the scope of variables.
  The can either be named or anonymous.
-/

section -- Anonymous section
  variable (T : Type)
  #check T
end

#check T -- This fails because the name T is destroyed at the end of the section.

section useful
  variable (S T U : Type)

  def compose₄ (g : T → U) (f : S → T) (x : S) : U := sorry
  def doTwice₄ (h : S → S) (x : S) : S := sorry
  def doThrice₄ (h : S → S) (x : S) : S := sorry
end useful

/-
  Note that while the names from variable do not persist beyond the section, the names
  from def do persist!  Moreover, the same names persist internal to the functions.
-/
#check S
#check T
#check U
#check compose₄
#print compose₄
end Variables_and_Sections

section Namespaces

/-
  Namespaces are similar to sections.  Unlike a section, all definitions are internal to the
  namespace.  However, we can access elements of a namespace using fully qualified names.
-/
namespace Namespaces

namespace Foo
  def a : ℕ := 5
  def add_seven (x : ℕ) : ℕ := x + 7

  def add_seven_a : ℕ := add_seven a

  /-
    Inside a namespace, we can use short names.
  -/
  #check a
  #check add_seven
  #check add_seven_a
  /-
    We can also use the fully qualified name
  -/
  #check Foo.add_seven
end Foo

/-
  Outside the namespace, we must use the fully qualified name.
-/
#check a          -- Fails; outside namespace.
#check add_seven  -- Fails; outside namespace.

#check Foo.a
#check Foo.add_seven


/-
  If we don't want to use the fully qualified names, we can open the namespace.
-/
open Foo

#check a
#check add_seven


/-
  We can re-enter namespaces later.
-/
namespace Foo
  #check a
  #check add_seven

  /-
    We can also nest namespaces.
  -/
  namespace Bar
    def add_fourteen_a : ℕ := add_seven (add_seven a)

    #check add_seven_a
    #check add_fourteen_a
  end Bar

  #check add_seven_a
  #check Bar.add_fourteen_a
end Foo

#check Foo.add_seven_a
#check Foo.Bar.add_fourteen_a

open Foo

#check add_seven_a
#check Bar.add_fourteen_a

#check Foo.a
#check Foo.add_seven

namespace Foo
  def add_fourteen_a : ℕ := add_seven (add_seven a)
  #check add_fourteen_a       -- Note these are not the same.
  #check Bar.add_fourteen_a
end Foo
end Namespaces
end Lecture_02
