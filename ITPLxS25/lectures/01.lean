import Mathlib.tactic

namespace Lecture_01
/-
  Simple Type Theory
-/

/-
  Lean's foundation is known as the Calculus of Inductive Constructions.
  For our puroses, we restrict ourselves to a piece of this foundation called
  Simple Type Theory.  It might be simplest to understand type theory by analogy.

  A set theory is a system to describe sets, which are (loosely) collections of objects.
    - The set theory with which you are familiar is the Zermelo-Fraenkel Set theory with
      the axiom of choice (ZFC).
  In ZFC, the basic set operation from which all other set operations are formed is the
  membership operator: x ∈ S (x is an element of S).

  By analogy, a type theory is a system to describe types which are (loosely) characterizations
  or classifications of terms (objects).  The analogous operation to membership is judgement
    x : S is the judgement that the term x has type S.

  We can use #check to ask Lean to provide the type of a given term.  If we have a term, t,
  the syntax
    #check t
  will print the type of t in the Lean Infoview window under Messages when the cursor is
  on the same line as the statement #check.
-/


#check 1
#check 2
#check true
#check false
#check "Hello, world!"

/-
  If we think we know the term t has type S, we can use #check to ask Lean whether or not
  our guess is correct using the judgement operator:
    #check t : S
-/

#check (1 : ℕ)
#check (2 : ℕ)
#check (3 : ℕ)
#check (3 + 0 : ℕ)
#check (4 * (5 + 0): ℕ)
#check (true : Bool)
#check (false : Bool)
#check (true && false : Bool)   -- "&&" is the Boolean and
#check (true || false : Bool)   -- Boolean or
#check (true : Bool)       -- Boolean "true"

/-
  Unlike set theory, judgement is NOT a proposition, but a statement of fact.

  Example: In set theory we can use set membership and negation to
  express logical statements symbolically
    · 3 is an element of the natural numbers is represented as 3 ∈ ℕ
    · -7 is not an element of the natural numbers is represented as ¬(7 ∈ ℕ) or 7 ∉ ℕ.

  In type theory, we make the judgement 3 : ℕ because 3 is in fact a natural number.
  However, we CANNOT negate types (what is the type of "not a natural number?") and
  so we also cannot negate judgements.

  We should also note that judgements like -7 : ℕ simply do not make sense because -7
  is definitionally NOT a natural number.  These types of statements result in errors.
-/

#check ¬ℕ
#check -7 : ℕ
#check ¬(-7 : ℕ)


/-
  We can also use Lean to evaluate expressions.  For example,
-/

#eval 5 * 4              -- 20
#eval 1 + 2              -- 3
#eval true && false      -- false
#eval true || false      -- true
#eval ¬true              -- false

/-
  A powerful feature of type theory is the ability to construct new types from existing
  types.  The simplest ways to do this involve Function Types and Product Types.
  Each of these are constructed from two types, α and β.

  A function type α → β represents a function that transforms a term of type α into a
  term of type β. A term α → β will have type "Type".
-/

#check ℕ → ℕ      -- type the arrow as "\to" or "\r"
#check ℕ -> ℕ     -- alternative ASCII notation

/-
  A product type α × β represents a pair of terms of type α and β.
  A term α × β will also have type "Type".
-/
#check ℕ × ℕ      -- type the product as "\times"
#check Prod ℕ ℕ   -- alternative notation

/-
  We can iterate these constructions to create longer chains of functions
  or longer chains of products.  Note that in lean, these expressions naturally
  associate to the RIGHT.
-/

#check ℕ → ℕ → ℕ
#check ℕ → (ℕ → ℕ)  --  same type as above
#check (ℕ → ℕ) → ℕ  -- not the same as the two above.

/-
  We can also think about triples (or more generally n-tuples)
-/
#check ℕ × ℕ × ℕ
#check ℕ × (ℕ × ℕ)  -- same type as above
#check (ℕ × ℕ) × ℕ  -- not the same as the two above.

/-
  We can also mix and match these constructions.
-/

#check ℕ × ℕ → ℕ
#check ℕ → ℕ × ℕ

/-
  In Lean, types are organized in a (countable) infinite hierarchy of universes.
    · Type 0 (or, simply, Type) contains all "ordinary" types such as ℕ, Bool, String,
      and any types that are constructed from them.
    · Type 1 contains types that treat types of Type 0 as elements and types constructed
      those.  For example, Type has Type 1 because, e.g., ℕ is a term of type Type.
      Simialrly, functions Type → Type have Type 1 because it is constructed using
      Type (which has type Type 1).
      ·
      ·
      ·
    · Type n is constructed inductively.  If we have constructed Type (n-1), then we
      have already constructed a term of type Type n, namely Type (n-1).  This is
      because Type (n-1) contains terms of type Type (n-1).  Any types constructed from
      terms of Type n, e.g. Type (n-1) → Type (n-1), is also of Type n.
-/
#check (Type : Type 1)
#check (Type → Type : Type 1)
#check (Type 1 → Type 1 : Type 2)
/-
  When we wish to consider a type in an unspecified level of the heirarchy in Lean, we
  usually specify the universe itself, rather than Type n:
    universe u
    Type u
-/
universe u
#check (Type u : Type (u + 1))
#check (Type u → Type u : Type (u +1 ))

/-
  We can define functions of the types above using lambda abstraction.
  This can be achieved using the fun and λ keywords.
-/

#check (fun (x : ℕ) => x + 5 : ℕ → ℕ)
#check (λ (x : ℕ) ↦ x + 5 : ℕ → ℕ)        -- These are equivalent.

/-
  Lean can often infer the type of the input and output from context.
-/

#check (fun x => x + 5 : ℕ → ℕ)
#check (λ x ↦ x + 5 : ℕ → ℕ)


/-
  We evaluate functions by passing a term of the appropriate type.
-/

#eval (λ x ↦ x + 5) 10

/-
  We can create functions of multiple variables using either nested λs.
  For example, a function of two natural numbers has type
    ℕ → ℕ → ℕ
-/

#check (λ (x : ℕ) ↦ (λ (y: ℕ) ↦ x) : ℕ → ℕ → ℕ)
#check (λ (x : ℕ) ↦ (λ (y : ℕ) ↦ y) : ℕ → ℕ → ℕ)

/-
  This notation is cumbersome.  Lean allows us to reduce to a single λ as follows:
-/

#check (λ (x : ℕ) (y : ℕ) ↦ x : ℕ → ℕ → ℕ)
#check (λ (x : ℕ) (y : ℕ) ↦ y : ℕ → ℕ → ℕ)

#eval (λ (x : ℕ) (y : ℕ) ↦ x : ℕ → ℕ → ℕ) 1 2               -- Evaluates to 1
#eval (λ (x : ℕ) (y : ℕ) ↦ y : ℕ → ℕ → ℕ) 1 2               -- Evaluates to 2

/-
  Lean allows us to reduce even further by grouping terms of the same type
-/
#check (λ (x y : ℕ) ↦ x : ℕ → ℕ → ℕ)
#check (λ (x y : ℕ) ↦ y : ℕ → ℕ → ℕ)

#eval (λ (x y : ℕ) ↦ x : ℕ → ℕ → ℕ) 1 2               -- Evaluates to 1
#eval (λ (x y : ℕ) ↦ y : ℕ → ℕ → ℕ) 1 2               -- Evaluates to 2


/-
  NOTE: We can think of the ℕ → ℕ → ℕ as being a function that accepts as input a
  natural number and outputs a function ℕ → ℕ.  That is to say, for every n : ℕ,
    (λ (x y : ℕ) ↦ x) n
  is the constant function ℕ → ℕ, m ↦ n.
  Similarly, the for every n : ℕ,
    (λ (x y : ℕ) ↦ y) n
  is the identity function ℕ → ℕ, m ↦ m.  This is an operation known as Currying
  (for the mathematician Haskell Curry).
-/

#check ((λ (x y : ℕ) ↦ x) 1 : ℕ → ℕ)
#check ((λ (x y : ℕ) ↦ y) 1 : ℕ → ℕ)

/-
  NOTE: Association is very important here!  Remember that Lean naturally associates to
  the RIGHT, so that ℕ → ℕ → ℕ means the same thing as ℕ → (ℕ → ℕ).  If we force
  association on the LEFT, (ℕ → ℕ) → ℕ, then we obtain a function that accepts as
  input a function ℕ → ℕ and outputs a number.

  For example, for every n : ℕ, we can define an evaluation at n function.  Below, we define
  the evaluation at 1 function:
-/

--#check (λ (f : ℕ → ℕ) ↦ f 1 : ℕ → ℕ → ℕ)    -- This fails because our function is
                                              -- NOT a function of 2 natural numbers!
#check (λ (f : ℕ → ℕ) ↦ f 1 : (ℕ → ℕ) → ℕ)

/-
  Evaluating the "evaluate at 1" function at the function x ↦ x + 1 reduces to
    (λ (f : ℕ → ℕ) ↦ f 1) (λ (x : ℕ) ↦ x + 1) = (λ (x : ℕ) x + 1) 1
                                              = 1 + 1
                                              = 2.
-/
#eval (λ (f : ℕ → ℕ) ↦ f 1) (λ (x : ℕ) ↦ x + 1) -- Confirm this evaluates to 2.

/-
  Of course, we don't have to restrict ourselves to functions defined on ℕ.
-/

#check (λ (x : ℕ) (y : Bool) ↦ if not y then x + 1 else x + 2 : ℕ → Bool → ℕ)
#check (λ x y ↦ if not y then x + 1 else x + 2 : ℕ → Bool → ℕ)

/-
  Definitions
-/

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
    · Arguments to our function appear after the name and before a semicolon.
    · The type of the output appears after the semicolon.
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

/- Local Definitions-/

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


/-
  Variables and Sections
-/

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


/-
  Namespaces
-/

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
