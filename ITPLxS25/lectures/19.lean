import ITPLxS25.lectures.«17»
import ITPLxS25.lectures.«18»
namespace Lecture_17

section Rings
/-
  A ring consists of a set, `A`, with two structures
    · (A, +) is an additive abelian group, and
    · (A, *) is a monoid.
  that are compatbile in the sense that
    · x * (y + z) = x * y + x * z, and
    · (x + y) * z = x * z + y * z.
-/

/-
  We show that our toy example, `X`, forms a ring. Since we've already proven that
  `(X,+)` is an abelian group, the next step is to equip `X` with a multiplication.
  Just as for addition, it's easiest to present the rules as a table:
   * | e | a | b | c |
  -----------------------
  e || e | e | e | e |
  a || e | a | b | c |
  b || e | b | e | b |
  c || e | c | b | a |
-/
namespace X

def mul : X → X → X
| e, e => e
| e, a => e
| e, b => e
| e, c => e
| a, e => e
| a, a => a
| a, b => b
| a, c => c
| b, e => e
| b, a => b
| b, b => e
| b, c => b
| c, e => e
| c, a => c
| c, b => b
| c, c => a

instance : Mul X where
mul := mul

theorem mul_assoc (x y z : X) : (x * y) * z = x * (y * z) := by
  sorry

instance : One X where
one := a

theorem one_mul (x : X) : 1 * x = x := by
  sorry

theorem mul_one (x : X) : x * 1 = x := by
  sorry

instance : Monoid X where
mul := mul
mul_assoc := mul_assoc
one_mul := one_mul
mul_one := mul_one

/-
  We can easily prove that the multiplication we have defined is commutative.
  This makes X a CommMonoid under *.
-/
theorem mul_comm (x y : X) : x * y = y * x := by
  sorry

instance : CommMonoid X where
mul_comm := mul_comm

/-
  We would like to know that `0` behaves as we expect: `0 * x = 0 = x * 0`.
-/
theorem zero_mul (x : X) : 0 * x = 0 := by
  sorry

theorem mul_zero (x : X) : x * 0 = 0 := by
  sorry

/-
  Finally we prove the compatibility.
-/
theorem left_distrib (x y z : X) : x * (y + z) = x*y + x*z := by
  sorry

theorem right_distrib (x y z : X) : (x + y) * z = x*z + y*z := by
  sorry

/-
  This is everything we need to establish that `(X, +, *)` is a ring.
-/
instance : Ring X where
left_distrib := left_distrib
right_distrib := right_distrib
zero_mul := zero_mul
mul_zero := mul_zero
mul_assoc := mul_assoc
one_mul := one_mul
mul_one := mul_one
zsmul := zsmul
neg_add_cancel := neg_add_cancel

/-
  In fact, since `(X,*)` is a commutative monoid, `(X,+,*)` is a commutative ring.

  class CommRing (α : Type u) extends Ring α, CommMonoid α
-/

instance : CommRing X where
mul_comm := mul_comm

end X
end Rings

section Fields
/-
  A field is a specific type of non-trivial, commutative ring, which means it MUST have
  at least two distinct elements, `0 ≠ 1`. The easiest way to understand the distinction
  between a field and a ring is to understand the elements called `Units`.

  A unit in a ring is an element that has a multiplicative inverse.  For a given ring,
  there is always at least one unit, `1` because `1 * 1 = 1`.  However, the number of
  units will vary dramatically depending on the particular ring.  For example, ℤ has
  exactly two units: `1` and `-1` (because `-1 * -1 = 1`.) However, the rational numbers,
  `ℚ` have countably many units and `ℝ` and `ℂ` both have uncountably many units.
-/

/-
  While we really only care about units in rings, the definition depends only on
  the monoid structure `(R,*)`, so mathlib implements units at the monoid level.

  structure Units (α : Type u) [Monoid α] where
  /-- The underlying value in the base `Monoid`. -/
  val : α
  /-- The inverse value of `val` in the base `Monoid`. -/
  inv : α
  /-- `inv` is the right inverse of `val` in the base `Monoid`. -/
  val_inv : val * inv = 1
  /-- `inv` is the left inverse of `val` in the base `Monoid`. -/
  inv_val : inv * val = 1
-/

/-
  As an example, we can construct the the only two units in our ring X as follows.
-/

namespace X
def unit_a : Units X := {val := a, inv := a, val_inv := rfl, inv_val := rfl}
def unit_c : Units X := sorry

/-
  The shorthand for the units in a Monoid, `M`, is `Mˣ`.
-/

#check Xˣ
end X

/-
  Mathlib provides a predicate to determine whether or not an element is a ring.

  def IsUnit [Monoid M] (a : M) : Prop :=
  ∃ u : Mˣ, (u : M) = a
-/

/-
  We can use this to prove that there are always fewer units than elements of a
  non-trivial ring. This is `0` is not a unit whenever `0 ≠ 1`.
-/
example {R : Type u} [Ring R] (h : (1:R) ≠ (0:R)) : ¬IsUnit (0 : R) := by
  intro ⟨u,h_u⟩
  have inv_0 : 0*u.inv = (1 : R) := by
    rw[← h_u]
    exact u.val_inv
  apply h
  calc
      1 = 0*u.inv := by rw[inv_0]
      _= 0 := by rw[zero_mul]

namespace X
/-
  For the ring X, this tells us that we have 2 units: `a` and `c`.
-/
example : IsUnit a := by
  use unit_a
  -- NOTE: At this stage, we are being asked to prove that unit_a.val = a.
  -- This is definitionally true, so we just use rfl.
  rfl

example : IsUnit c := ⟨unit_c,rfl⟩

/-
  The element `b` is not a unit because `b*b = 0`.
-/

example : ¬IsUnit b := by
  rintro ⟨u, h_u⟩
  have b_inv : b*u.inv = 1 := by
    sorry
  have absurd : b = 0 := by
    sorry
  contradiction
end X

/-
  For an arbitrary ring, `R`, the units will always form a group.
-/

instance {R : Type u} [Ring R] : Group Rˣ where
inv_mul_cancel := λ u ↦ inv_mul_cancel u

/-
  If our ring is commutative, then `Rˣ` is abelian.
-/

instance {R : Type u} [CommRing R] : CommGroup Rˣ where
mul_comm := mul_comm
inv_mul_cancel := λ u ↦ inv_mul_cancel u

/-
  With this in mind, we define a Field to be a ring, F, that satisfies
    `Fˣ = F \ {0}`.
-/

/-
  The simplest field has exactly two elements.
-/

inductive 𝔽₂ where | zero | one

namespace 𝔽₂

instance : Repr 𝔽₂ where
reprPrec x _ := match x with
  | zero => "0"
  | one => "1"

def add : 𝔽₂ → 𝔽₂ → 𝔽₂
| zero, zero => zero
| zero, one => one
| one, zero => one
| one,one => zero

-- Provides notation : x + y
instance : Add 𝔽₂ where
add := add

def neg : 𝔽₂ → 𝔽₂
| zero => zero
| one => one

-- Provides notation: - x
instance : Neg 𝔽₂ where
neg := neg

-- Provides notation: 0 for zero.
instance : Zero 𝔽₂ where
zero := zero

theorem neg_add_cancel (x : 𝔽₂) : -x + x = 0 := by
  sorry

theorem add_neg_cancel (x : 𝔽₂) : x + -x = 0 := by
  sorry

-- Provides notation : x - y
instance : Sub 𝔽₂ where
sub x y := x + -y

/-
  A particularly strange property of the field with two elements is that
  addition an subtraction are the same.  This is a consequence of
-/

theorem neg_is_trivial (x : 𝔽₂) : x = -x := by
  sorry

theorem sub_eq_add_neg (x y : 𝔽₂) : x - y = x + -y :=
  sorry

theorem add_is_sub (x y : 𝔽₂) : x + y = x - y := by
  sorry

def zero_add (x : 𝔽₂) : 0 + x = x := by
  sorry

def add_zero (x : 𝔽₂) : x + 0 = x := by
  sorry

theorem add_assoc (x y z : 𝔽₂) : (x + y) + z = x + (y + z) := by
  sorry

def add_comm (x y : 𝔽₂) : x + y = y + x := by
  sorry

def nsmul : ℕ → 𝔽₂ → 𝔽₂
| 0, _ => 0
| n+1, x => (nsmul n x) + x

-- Provides notation: n • x
instance : HSMul ℕ 𝔽₂ 𝔽₂ where
hSMul := nsmul

def zsmul : ℤ → 𝔽₂ → 𝔽₂
| Int.ofNat n, x =>  n • x                 -- Non-negative case
| Int.negSucc n, x => -((Nat.succ n) • x)  -- Negative case.

-- Provides notation : z • x
instance : HSMul ℤ 𝔽₂ 𝔽₂ where
hSMul := zsmul

instance : AddCommGroup 𝔽₂ where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmul
  neg := neg
  zsmul := zsmul
  neg_add_cancel := neg_add_cancel
  add_comm := add_comm

def mul : 𝔽₂ → 𝔽₂ → 𝔽₂
| zero, zero => zero
| zero, one => zero
| one, zero => zero
| one, one => one

-- Provides notation : x * y
instance : Mul 𝔽₂ where
mul := mul

-- Provides notation : 1
instance : One 𝔽₂ where
one := one

theorem mul_one (x : 𝔽₂) : x * 1 = x := by
  sorry

theorem one_mul (x : 𝔽₂) : 1 * x = x := by
  sorry

instance : MulOneClass 𝔽₂ where
one_mul := one_mul
mul_one := mul_one

theorem mul_zero (x : 𝔽₂) : x * 0 = 0 := by
  sorry

theorem zero_mul (x : 𝔽₂) : 0 * x = 0 := by
  sorry

theorem mul_assoc (x y z : 𝔽₂) : (x * y) * z = x * (y * z) := by
  sorry

theorem mul_comm (x y : 𝔽₂) : x * y = y * x := by
  sorry

theorem left_distrib (x y z : 𝔽₂) : x * (y + z) = x*y + x*z := by
  sorry

theorem right_distrib (x y z : 𝔽₂) : (x + y) * z = x*z + y*z := by
  sorry

instance : CommRing 𝔽₂ where
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul := one_mul
  mul_comm := mul_comm
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  zsmul := zsmul
  neg_add_cancel := neg_add_cancel

def inv : 𝔽₂ → 𝔽₂
| zero => zero
| one => one

-- Provides notation:  x⁻¹
instance : Inv 𝔽₂ where
inv := inv

theorem mul_inv_cancel (x : 𝔽₂) (h : x ≠ 0): x * x⁻¹ = 1 := by
  sorry

theorem exists_pair_ne : ∃ x y : 𝔽₂, x ≠ y := by
  sorry

instance : Field 𝔽₂ where
  inv := inv
  inv_zero := rfl
  exists_pair_ne := exists_pair_ne
  mul_inv_cancel := mul_inv_cancel
  nnqsmul := _
  qsmul := _

end 𝔽₂

--instance Field :
end Fields
