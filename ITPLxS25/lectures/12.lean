import Mathlib

namespace Lecture_12

namespace hidden

section Structures
/-
  A structure is a mechanism to bundle pieces of data together, which takes the form
    structure name parameters parent-structures where
      constructor :: fields
  Declaring a structure automatically declares a namespace of the same name.
-/

structure Point2 (α : Type u) where
  mk :: (x : α) (y : α)

/-
  The constructor name is optional and defaults to `mk`.
-/

structure Point2' (α : Type u) where
  (x : α) (y : α)

/-
  Parentheses may be avoided using newlines.
-/

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α


/-
  Lean provides projections for each of the fields specified.
-/

#eval Point2.x (Point2.mk 1 2)
#eval (Point2.mk 1 2).y

def p := Point2'.mk "First" "Second"
#eval p.x
#eval p.y

def q := Point3.mk 'x' 'y' 'z'
#eval q.x
#eval q.y
#eval Point3.z q

/-
  We can define functions on our structures.
-/

namespace Point3
/-
  We might want to define addition on points with coordinates from ℕ.
-/
def add (p q : Point3 Nat) :=
  mk (p.x + q.x) (p.y + q.y) (p.z + q.z)

def p := Point3.mk 1 2 3
def q := Point3.mk 4 5 6

#eval add p q
#eval p.add q
#eval q.add p

def smul (n : Nat) (p : Point3 Nat) :=
  mk (n * p.x) (n * p.y) (n*p.z)

#eval smul 3 p
#eval p.smul 3

/-
  Utilizing the constructor on a structure requires that we remember
  the order in which the fields appear.  Lean provides an alternate
  form for creating an instance of a structure:
    { (field-name := expr)* : structure-type }
  or
    { (field-name := expr)* }
  Here, the * indicates that the pattern can be repeated as necessary.
-/
#check {x := 1, y := 2, z := 3 : Point3 _}
def r := {z := 3, x := 1, y := 2 : Point3 Nat}
def s : Point3 Nat := {y := 2, z := 3, x := 1}

/-
  Lean is pretty smart: if you miss something, it can tell you what you missed.
-/
#check {x := 1, y := 2 ,z := 7: Point3 _}

end Point3

end Structures

section Inheritance

/-
  Inheritance is a mechanism by which one structure extends another.
-/

structure Point4 (α : Type u) extends Point3 α where
 w : α

def myPoint : Point4 Nat := {x := 1, y := 2, z := 3, w := 4}
end Inheritance

section Type_Classes
/-
  When we defined Point3, we defined an addition on points with coordinates
  from ℕ.  This provides a nice way to add these types of points, but there are
  many other structures that would permit the same kind of addition.  Some examples
  are
    · Point3 ℤ
    · Point3 ℝ
    · Point3 ℂ
  We do not want to have to keep defining addition functions for each coordinate
  type that permits the construction.  Instead, we rely on what's known as Type Class.
  This is a way to implement ad-hoc polymorphism -- essentially, a mechanism to write
  code that works over a wide range of types, provided they satisfy some required
  interface.

  For mathematicians, this means we can write code that generalize notions like adding
  triples pointwise -- so long as the coordinates support an addition -- in the way we
  expect.

  To take the pointwise addition example, we simply observe that addition is a binary
  operation on a type, a, which we encode in Lean as a function
    a → a → a
  This observation allows us to define what it means to implement *some* sort of addition
  on a type using just a bare structure.
-/

structure Add₀ (a : Type) where
  add : a → a → a

/-
  Note that all of the additions above work the way we would want them to
-/

#check (Nat.add : ℕ → ℕ → ℕ)
#check (Int.add : ℤ → ℤ → ℤ)
#check (Rat.add : ℚ → ℚ → ℚ)
/-
  In fact, Lean uses it's own `Add` to define addition on ℝ and ℂ
-/
#check (inferInstance : _root_.Add ℝ).add
#check (inferInstance : _root_.Add ℂ).add


def double₀ {a : Type} (s : Add₀ a) (x : a) : a :=
  s.add x x

#eval double₀ {add := Nat.add} (54543 : Nat)
#eval double₀ {add := Int.add} (-27656534542 : Int)
#eval double₀ {add := Rat.add} (3/2 : Rat)
/-
  The reals are defined as the completion of the rationals, so the output i
  a bit weird in the real case.
-/
#eval double₀ {add := (inferInstance : _root_.Add ℝ).add} (2 : ℝ)
-- Same for ℂ, just twice as weird.
#eval double₀ {add := (inferInstance : _root_.Add ℂ).add} {re := 2, im := 3}

/-
  While more convenient than defining multiple additions, this is still
  cumbersome.  By using a class instead of a structure, we can make
  Lean do this work for us.
-/

class Add (a : Type) where
 add : a → a → a

/-
  Now, we can define our double function so that it requires the object
  being passed to double to implement an addition.
-/
def double {a : Type} [Add a] (x : a) : a :=
  Add.add x x

/-
  This his doesn't magically allow us to start applying double to things
  with addition.
-/
#check double 2

/-
  Instead, we have to register a type as an instance of Add by providing the
  addition.
-/

instance : Add Nat where
  add := Nat.add

#eval double (2 : Nat)

/-
  Of course, in doing this, we don't have to use the standard addition.
  For example, we could define some weird operation like
    Add x y = 2x + xy - 3y
-/

instance : Add Int where
  add := λ x y : Int ↦ 2*x + x*y - 3*y

/-
  Now that we've registered Int as an instance of Add using this weird
  operation, the function double evaluates to
    2x + x*x - 3x = x^2 - x = x(x - 1)
-/
#eval double (3 : Int)
#eval double (1 : Int)
#eval double (0 : Int)

/-
  Another useful application is the Inhabited type class.
-/

class Inhabited (a : Type u) where
  default : a

/-
  This simply asserts that a type is non-empty.
-/

instance : Inhabited Nat where
  default := 0

instance : Inhabited Bool where
  default := false


end Type_Classes

section Example

inductive Animal
| cat
| dog
| cow
| horse
| peacock

/-
  The `Repr` class is used to tell Lean how to print. In its
  simplest form, you just need to supply a string.  Here is
  the actual definition from Repr.lean:

  class Repr (α : Type u) where
    reprPrec : α → Nat → Format

  If our animal speaks, it seems reasonable that it should
  have a pretty-print interface.
-/

class Speaks (α : Type) extends Repr α where
  Says : α → String

class HasTail (α : Type) where
  action : α → String

namespace Animal

instance : Repr Animal where
reprPrec a _ := match a with
    | cat => "cat"
    | dog => "dog"
    | cow => "cow"
    | horse => "horse"
    | peacock => "peacock"

instance : Speaks Animal where
  Says
  | cat => "The " ++ reprStr cat ++ " says meow"
  | dog => "The " ++ reprStr dog ++ " says woof"
  | cow => "The " ++ reprStr cow ++ " says moo"
  | horse => "The " ++ reprStr horse ++ " says neigh"
  | peacock => "The " ++ reprStr peacock ++ " says honk"

#eval Speaks.Says Animal.cat
#eval Speaks.Says Animal.dog
#eval Speaks.Says Animal.cow
#eval Speaks.Says Animal.horse
#eval Speaks.Says Animal.peacock

instance : HasTail Animal where
action
| cat => "flicks"
| dog => "wags"
| cow => "swishes"
| horse => "swishes"
| peacock => "fans"
end Animal

def fullBehaviorExplicit {α : Type} (s : Speaks α) (t : HasTail α) (x : α) : String :=
  s.Says x ++ ", and its tail " ++ t.action x

#eval fullBehaviorExplicit Animal.instSpeaks Animal.instHasTail Animal.cat
#eval fullBehaviorExplicit Animal.instSpeaks Animal.instHasTail Animal.dog
#eval fullBehaviorExplicit Animal.instSpeaks Animal.instHasTail Animal.cow
#eval fullBehaviorExplicit Animal.instSpeaks Animal.instHasTail Animal.horse
#eval fullBehaviorExplicit Animal.instSpeaks Animal.instHasTail Animal.peacock

def fullBehavior {α : Type} [Repr α] [HasTail α] [Speaks α] (x : α) : String :=
  Speaks.Says x ++ ", and its tail " ++ HasTail.action x

#eval fullBehavior Animal.cat
#eval fullBehavior Animal.dog
#eval fullBehavior Animal.cow
#eval fullBehavior Animal.horse
#eval fullBehavior Animal.peacock

end Example
end hidden

end Lecture_12
