import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Notation.Defs
namespace Lecture_17

/-
  Algebraic structures in Lean are implemented through the typeclass
  interface. Moreover, these structures are stratified by the inclusions
    Semigroup ⊆ Monoid ⊆ Group ⊆ Ring.
-/

section Operations

/-
  In algebra, one often encounters two 'types' of operations:
    · Operations that behave like multiplication, such as
        - Multiplication
        - Concatenation
        - Function composition
    · Operations that are basically addition.

  Lean implements a generic multiplication-like operation as a type class
  called `Mul`.  We can think about the type `α` functioning like the
  underlying set of an algebraic structure.
-/

section Multiplicative_Operations
/-
  class Mul (α : Type u) where
  mul : α → α → α
-/

/-
  We prove that various sets can be equipped with a multiplication
  by proving `α` has a well-defined multiplication
    `α × α → α`
-/

/-
  For number systems, the actual functions are already available in lean:
-/

/- instance : Mul ℕ where
  mul := Nat.mul

instance : Mul ℤ where
  mul := Int.mul

instance : Mul ℚ where
  mul := Rat.mul -/

/-
  The construction of the real numbers in Lean as equivalence
  classes of Cauchy sequences means the proof that ℝ implements Mul
  is housed inside Mathlib.Data.Real.Basic.  The situation is
  similar for ℂ, which is housed in Mathlib.Data.Complex.Basic.
-/

/-
  Of course, we can define operations on all sorts of types that are not
  actually multiplication, but behave like it.  For example, function composition.
-/

/-- The composition of g with f, `g ∘ f`-/
def comp {α β γ : Type u} (g : β → γ) (f : α → β) : α → γ :=
  λ a : α ↦ g (f a)

/-
  Registering composition as an instance of `HMul` (heterogeneous multiplication)
  provides notation:
    If `g : β → γ` and `f : α → β`, then `g * f := comp g f`.
-/
instance {α β γ : Type u} : HMul (β → γ) (α → β) (α → γ) where
hMul:= comp

/-
  Composition of functions is associative.
-/
theorem comp_assoc {α β γ δ : Type u} (h : γ → δ) (g : β → γ) (f : α → β) :
  h * (g * f) = (h*g)*f := rfl

/-
  Note that composition requires the codomain of `f` and the domain of `g` to
  be the same type, so composition isn't a well-defined binary operation for
  functions in general.
  However, if we restrict to just functions `α → α`, we can prove that composition
  is a well-defined binary operation on this type.
-/
instance {α : Type u} : Mul (α → α) where
  mul := comp

/-
  Registering as an instance of `Mul` also provides access to the infix operator `*`
  as a shorthand for composition.
-/

#eval (λ n : ℕ ↦ 2 + n) 3 -- 2 + 3 = 5
#eval (λ n : ℕ ↦ 2*n) 5 -- 2*5 = 10
#eval ((λ n : ℕ ↦ 2*n)*(λ n : ℕ ↦ 2 + n)) 3 -- 2*(2 + 3) = 2*5 = 10

/-
  The function `λ a : α ↦ a` is the called the identity function because
  it serves as the identity element for composition.  We can tell Lean what the
  identity element is using the type class `One`:

  class One (α : Type u) where
  one : α
-/

instance {α : Type u} : One (α → α) where
one := λ a : α ↦ a

/-
  The class `MulOneClass` allows us to identify a type as having an operation
  (`Mul`) and a unit, `One`.

  class MulOneClass (M : Type u) extends One M, Mul M where
  protected one_mul : ∀ a : M, 1 * a = a
  protected mul_one : ∀ a : M, a * 1 = a
-/

theorem id_comp {α : Type u} (f : α → α) :  1 * f = f := rfl
theorem comp_id {α : Type u} (f : α → α) : f * 1 = f := rfl

instance {α : Type u} : MulOneClass (α → α) where
  mul_one := id_comp
  one_mul := comp_id

/-
  This allows us to use `1` as a standin for the function identity function
  `λ a : α ↦ a`.
-/
#eval ((λ s : String ↦ s ++ " bar") * 1) "foo"
#eval (1 * (λ s : String ↦ s ++ " bar")) "foo"

/-
  Since we're thinking of our operation as multiplication, we want a shorthand
  for repeated multiplication:
    . `f^0 = 1`
    · `f^1 = f`
    · `f^2 = f * f`
    · `f^3 = f * f * f`
    ⋮

  For reasons that will be clear when we get to Monoids, we define exponents
  recursively as a function named `npow_comp`
-/

/-- The `n`-fold composition of `f : α → α` with itself.-/
def npow_comp {α : Type u} : ℕ → (α → α) → (α → α) :=
  λ (n : ℕ) (f : α → α) ↦ match n with
  | Nat.zero => 1
  | Nat.succ n => λ a : α ↦ ((npow_comp n f) * f) a

#eval (npow_comp 0 λ n ↦ 2*n) 3 -- 3
#eval (npow_comp 1 λ n ↦ 2*n) 3 -- 2*3 = 6
#eval (npow_comp 2 λ n ↦ 2*n) 3 -- 2*(2*3) = 2*6 = 12

/-
  We can register this as an instance of HPow

  class HPow (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hPow : α → β → γ
-/

@[default_instance]
instance {α : Type u} [Mul (α → α)] : HPow (α → α) ℕ (α → α) where
  hPow f n := npow_comp n f

/-
  This provides the exponent notation:
-/

#eval ((λ n : ℕ ↦ 2*n) ^ 0) 3 -- 3
#eval ((λ n : ℕ ↦ 2*n) ^ 1) 3 -- 2*3 = 6
#eval ((λ n : ℕ ↦ 2*n) ^ 2) 3 -- 2*(2*3) = 2*6 = 12

/-
  It's often convenient to prove some basic facts about how exponents work.
  Fortunately, our definitions were basically rigged to make these trivial.
-/

theorem npow_zero_comp {α : Type u} (f : α → α) : f ^ 0 = 1 := rfl
theorem npow_succ_comp {α : Type u} (n : ℕ) (f : α → α): f ^ (n+1) = f^n * f := rfl


end Multiplicative_Operations

section Additive_Operations
/-
  Lean also provides a type class specifically for operations that are
  basically the same thing as addition.
-/

/-
  class Add (α : Type u) where
  add : α → α → α
-/

/-
  Consider the following enumerated type, which we regard as a set with 4 elements.
-/
inductive X where | e | a | b | c

namespace X
instance : Repr X where
reprPrec x _ := match x with
  | e => "0"
  | a => "a"
  | b => "b"
  | c => "c"
/-
  We can define an addition operation by defining every possible addition.
  This is most easily represented as a table:

   + | e | a | b | c |
  -----------------------
  e || e | a | b | c |
  a || a | b | c | e |
  b || b | c | e | a |
  c || c | e | a | b |
-/

def add : X → X → X
| e, e => e
| e, a => a
| e, b => b
| e, c => c
| a, e => a
| a, a => b
| a, b => c
| a, c => e
| b, e => b
| b, a => c
| b, b => e
| b, c => a
| c, e => c
| c, a => e
| c, b => a
| c, c => b

#eval add e e
#eval add a b
#eval add b a

instance : Add X where
  add := add

/-
  Note that we can now use `+` instead of `add`.
-/
#eval e + a
#eval a + b


/-
  Checking that this operation is associative requires checking all of the cases.
  To avoid doing this by hand, we use the `cases` tactic and the sequence
  combinator `<;>` to produce all 64 cases and close each one with `rfl`.
-/
theorem add_assoc (x y z : X) : (x + y) + z = x + (y + z):= by
  sorry

/-
  We can also prove this addition is commutative.  Again, we would need to
  check every single case (of which there are 16), so we use `cases` and `<;>`
  to get each of the possible cases, then close them all with `rfl`.
-/

theorem add_comm (x y : X) : x + y = y + x := by
  sorry

/-
  We can also register that this operation has an identity.  Since the operation
  we have defined is addition, it is customary to call the identity element `0`.

  class Zero (α : Type u) where
  zero : α

  class AddZeroClass (M : Type u) extends Zero M, Add M where
  protected zero_add : ∀ a : M, 0 + a = a
  protected add_zero : ∀ a : M, a + 0 = a
-/

instance : Zero X where
  zero := e

/-
  We can prove that `e = 0` by expanding the cases and then applying `rfl`.
-/
theorem zero_add (x : X) : e + x = x := by
  sorry

theorem add_zero (x : X) : x + e = x := by
  sorry

instance : AddZeroClass X where
zero_add := zero_add
add_zero := add_zero

/-
  Now we can standardize the notation and use `0` instead of `e`.
-/

#eval 0 + a
#eval a + 0
#eval 0 + b
#eval b + 0
#eval 0 + c
#eval c + 0

/-
  We can also see that every element of X has an additive inverse since `e`
  appears in every row of the table.  We can register this with Lean using the
  type class `Neg`

  class Neg (α : Type u) where
  neg : α → α

  NOTE: This is specific to ADDITIVE operations.  It is customary to use the
  type class `Inv` for MULTIPLICATIVE operations.

  class Inv (α : Type u) where
  inv : α → α
-/

instance : Neg X where
neg x := match x with
| e => e
| a => c
| b => b
| c => a

/-
  The class `Neg` provides access to the notation -x for the inverse.
  The class `Inv` provides access to the notation x⁻¹ for the inverse.
-/

#eval -a -- The additive inverse of `a` is `c`.

/-
  It's often convenient to prove that the negation behaves as expected.
-/
theorem add_neg_cancel (x : X) : x + -x = 0 := by
  sorry

theorem neg_add_cancel (x : X) : -x + x = 0 := by
  sorry

/-
  Of course, it seems silly to write x + -x.  It would be much more
  natural to write x - x or -x + x.  We can achieve this using `Sub`

  class Sub (α : Type u) where
  sub : α → α → α
-/

instance : Sub X where
  sub x₁ x₂ := x₁ + (-x₂)

#eval a - a
#eval b - b
#eval c - c

#eval -b -- b is its own inverse: b + b = 0.
#eval a + b -- a + b := c
#eval a - b -- a - b := a + (-b) := a + b = c.

/-
  Frequently, when we have an addition operation, we like to use the shorthand
  `nx` to mean "add `x` to itself `n` times", where `n : ℕ`.  In Lean, this is
  often called `nsmul` to indicate scalar multiplication with ℕ.
  This is easy to define inductively:
-/
def nsmul (n : ℕ) (x : X): X := by
  match n with
  | 0 => exact 0
  | n+1 => exact (nsmul n x) + x

/-
  We can register this as a heterogeneous scalar multiplication

  class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSMul : α → β → γ
-/

instance : HSMul ℕ X X where
hSMul := nsmul

/-
  This provides the shorthand for scalar multiplication, n • x:
-/
#eval a + a -- b
#eval 2 • a -- also b.


/-
  We can also prove that this behaves as expected:
-/
theorem nsmul_succ (n : ℕ) (x : X) : (n + 1) • x = (n • x) + x := rfl

#eval 1•a

#eval nsmul 1 a
#eval nsmul (1 + 1) a
--#eval a +  nsmul

/-
  Since X is an instance of both `Neg` and `HSMul ℕ X X`, we can extend
  this scalar multiplication to all integers.
-/

def zsmul : ℤ → X → X
| Int.ofNat n, x => n • x         -- Non-negative case
| Int.negSucc n, x => -((n+1) • x)  -- Negative case.

instance : HSMul ℤ X X where
hSMul := zsmul

#eval 3 • a         -- c
#eval a + a + a     -- also c
#eval -a + -a + -a  -- a
#eval (-3) • a      -- also a
#eval -c            -- a

/-
  We can prove scalar multiplication by ℤ behaves as expected:
-/

theorem zsmul_zero (x : X) : 0 • x = 0 :=
  sorry
theorem zsmul_succ (n : ℕ) (x : X) : (n+1) • x =  (n • x) + x :=
  sorry
theorem zsmul_neg (n : ℕ) (x : X) :  (Int.negSucc n) • x = - ((n+1) • x) :=
  sorry

end X

end Additive_Operations

end Operations

section Semigroups
/-
  The notion of a Semigroup is merely a set with an associative operation
  that we call mul by default.  The existence of this operation is asserted by
  the requirement that `Semigroup` extends `Mul`.

  class Semigroup (G : Type u) extends Mul G where
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
-/

/-
  Functions of type `α → α` form a semigroup under composition:
-/
instance {α : Type u} : Semigroup (α → α) where
  mul_assoc := comp_assoc

/-
  Note that if our operation behaves like addition, then our carrier
  type (e.g. X above) is an instance of Add, not of Mul.  This makes it
  impossible to prove X is a semigroup under the addition we've defined.
  Fortunately, Lean provides the `AddSemigroup` with extends `Add`, rather
  than the more general `Mul`.

  class AddSemigroup (G : Type u) extends Add G where
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
-/

namespace X
instance : AddSemigroup X where
  add_assoc := add_assoc
end X

end Semigroups

section Monoids
/-
  A monoid is a semigroup that also has an identity element.

  class Monoid (M : Type u) extends Semigroup M, MulOneClass M

  Since we've already proven that maps `α → α` are a semigroup and a MulOneClass,
  we have already done all the legwork for proving that it is a monoid.
-/

instance {α : Type u} : Monoid (α → α) where
  mul_one := mul_one
  one_mul := one_mul

/-
  Similar to Semigroup, Lean provides an additive monoid

  class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M
-/

namespace X

instance : AddMonoid X where
zero_add := zero_add
add_zero := add_zero
nsmul := nsmul
nsmul_succ := nsmul_succ

/-
  Note that when we proved the result `add_comm`, we actually established more: `X`
  is not just an `AddMonoid`, it's actually an `AddCommMonoid`

  class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M
-/

instance : AddCommMonoid X where
add_comm := add_comm

/-
  Lean also provides further stratification within Monoids.
  For an additive monoid, such as a our finite example `({0,a,b,c}, +)`,
  there exists a class called `SubNegMonoid`


  class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  protected sub := SubNegMonoid.sub'
  protected sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  protected zsmul : ℤ → G → G
  protected zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  protected zsmul_succ' (n : ℕ) (a : G) :
      zsmul n.succ a = zsmul n a + a := by
    intros; rfl
  protected zsmul_neg' (n : ℕ) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by
    intros; rfl
-/

instance : SubNegMonoid X where
zsmul := zsmul


/-
  For multiplicative monoids, Lean has the analogous DivInvMonoid.
-/

/-
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  protected div := DivInvMonoid.div'
  protected div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  protected zpow : ℤ → G → G := zpowRec npowRec
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  protected zpow_succ' (n : ℕ) (a : G) : zpow n.succ a = zpow n a * a := by
    intros; rfl
  protected zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl
-/
end X
end Monoids
end Lecture_17
