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
  Terms of type α × β come equipped with two projections.
  If (a,b) : α × β, then (a,b).1 = a and (a,b).2 = b.
-/

#check ((1,false) : ℕ × Bool)
#eval (1,true).1          -- evaluates to 1
#eval (1,true).2          -- evaluates to true

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

#check (λ ((x,y) : ℕ × ℕ) ↦ x + y : ℕ × ℕ → ℕ)
#eval (λ ((x,y) : ℕ × ℕ) ↦ x + y) (1,2)

/-
  We can create functions of multiple variables using either nested λs.
  For example, a function of two natural numbers has type
    ℕ → ℕ → ℕ
-/

#check (λ (x : ℕ) ↦ (λ (y: ℕ) ↦ x + y) : ℕ → ℕ → ℕ)

/-
  This notation is cumbersome.  Lean allows us to reduce to a single λ as follows:
-/

#check (λ (x : ℕ) (y : ℕ) ↦ x + y: ℕ → ℕ → ℕ)

#eval (λ (x : ℕ) (y : ℕ) ↦ x + y) 1 2               -- Evaluates to 3

/-
  Lean allows us to reduce even further by grouping terms of the same type
-/
#check (λ (x y : ℕ) ↦ x + y: ℕ → ℕ → ℕ)
#eval (λ (x y : ℕ) ↦ x + y ) 1 2               -- Evaluates to 3

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

end Lecture_01
