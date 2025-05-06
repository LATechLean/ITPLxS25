import ITPLxS25.lectures.Lecture17

namespace Lecture_17

section Groups

/-
  In Lean, a general group (which is assumed to be multiplicative) is an extension of
  `DivInvMonoid`

  class Group (G : Type u) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

  If our operation is additive, then we use the `AdditiveGroup` class instead.

  class AddGroup (A : Type u) extends SubNegMonoid A where
  protected neg_add_cancel : ∀ a : A, -a + a = 0
-/

namespace X
instance : AddGroup X where
neg_add_cancel := sorry

/-
  In fact, more is true: we've already proven that `X` is actually an abelian group
  via the theorem `add_comm`. In lean, we have the type class

  class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G
-/

instance : AddCommGroup X where
add_comm := sorry

end X

/-
  As an example of a multiplicative group, let's define the Fourth Roots of Unity.
  This group has 4 elements consisting of 1, i and their negatives,
  subject to the usual relations
    · i^2 = -1
    · (-1)^2 = 1
-/
inductive U where | one | i | neg_one | neg_i

namespace U

instance : Repr U where
reprPrec x _ := match x with
  | one => "1"
  | i => "i"
  | neg_one => "-1"
  | neg_i => "-i"

def mul : U → U → U
| one, one => one
| one, i => i
| one, neg_one => neg_one
| one, neg_i => neg_i
| i, one => i
| i, i => neg_one
| i, neg_one => neg_i
| i, neg_i => one
| neg_one, one => neg_one
| neg_one, i => neg_i
| neg_one, neg_one => one
| neg_one, neg_i => i
| neg_i, one => neg_i
| neg_i, i => one
| neg_i, neg_one => i
| neg_i, neg_i => neg_one

instance : Mul U where
  mul := mul

theorem mul_assoc (x y z : U) : (x * y) * z = x * (y * z) := by
  sorry

instance : One U where
one := one

theorem one_mul (x : U) : 1 * x = x := by
  sorry

theorem mul_one (x : U) : x * 1 = x := by
  sorry

instance : Inv U where
  inv
  | one => one
  | i => neg_i
  | neg_one => neg_one
  | neg_i => i

theorem inv_mul_cancel (x : U) : x⁻¹ * x = 1 := by
  sorry

theorem mul_inv_cancel (x : U) : x * x⁻¹ = 1 := by
  sorry

instance : Group U where
mul := mul
mul_assoc := mul_assoc
one_mul := one_mul
mul_one := mul_one
inv_mul_cancel := inv_mul_cancel

instance : CommGroup U where
  mul_comm := sorry

end U

end Groups

end Lecture_17
