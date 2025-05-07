import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Equiv.Defs

namespace Lecture_20


section Morphisms_of_Monoids

/-
  Assume `M` and `N` are monoids. A morphism of monoids is defined to be a function
  `f : M → N` that satisfies two properties
    · For all `m₁, m₂ : M`, `f (m₁ * m₂) = (f m₁) * (f m₂)`, and
    · `f 1 = 1`, where the first `1` is the identity for `M` and the second `1`
      is the identity for `N`.

  Lean encodes this as a hierarchy of structures:

  structure OneHom (M : Type*) (N : Type*) [One M] [One N] where
    protected toFun : M → N
    protected map_one' : toFun 1 = 1

  structure MonoidHom (M : Type*) (N : Type*) [MulOneClass M] [MulOneClass N] extends
  OneHom M N, M →ₙ* N

  This provides a type `M →* N` that connotes a morphism of monoids.

  We can construct a MonoidHom using the constructor `MonoidHom.mk`, which requires proof that
  a function `f : M → N` satisfies the two conditions
    · `map_mul : ∀ (a b : M), f (a * b) = f a * f b`
    · `map_one : f 1 = 1`

  As expected, there are additive versions:

  structure AddMonoidHom (M : Type*) (N : Type*) [AddZeroClass M] [AddZeroClass N] extends
    ZeroHom M N, AddHom M N

  structure ZeroHom (M : Type*) (N : Type*) [Zero M] [Zero N] where
    protected toFun : M → N
    protected map_zero' : toFun 0 = 0

  structure AddHom (M : Type*) (N : Type*) [Add M] [Add N] where
    protected toFun : M → N
    protected map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

-/

#check ZeroHom
#check AddHom
#check MonoidHom.mk
#check AddMonoidHom

instance : AddZeroClass ℕ where
add_zero := Nat.add_zero
zero_add := Nat.zero_add

example : ℕ →+ ℕ := by
  let f : ℕ → ℕ := λ n ↦ 2*n
  have map_add : ∀ (a b : ℕ), f (a + b) = f a + f b := by
    intro a b
    unfold f
    rw[Nat.mul_add]
  have map_zero : f 0 = 0 := by
    unfold f
    rw[Nat.mul_zero]
  exact {toFun := f, map_add' := map_add, map_zero' := map_zero}

end Morphisms_of_Monoids

section Morphisms_of_Groups

/-
  Morphisms for groups in lean are also just morphisms for monoids.
  However, this doesn't quite fit the literature. If you happen to pick
  up a text on abstract algebra, you'll almost certainly see that a
  morphism of groups is usually called a Homomorphism of Groups and
  is defined as follows:

  Assume `(G,*₁)` and `(H,*₂)` are groups with identity elements
  `e₁ ∈ G` and `e₂ ∈ H`. A function `f : G → H` is a Homomorphism
  of Groups if for all `x₁, x₂ ∈ G`,
    `f (x₁ *₁ x₂) = f x₁ *₂ f x₂.`

  This means a morphism of monoids imposes an additional condition on
  top of being a morphism of groups.  However, every morphism of groups
  satisfies `f(e₁) = e₂`.

  To prove this fact, we'll need a couple of basic results.
-/

variable {G H : Type u} [Group G] [Group H] (a b c: G)

/-
  By virtue of being a group, we obtain the following axioms.
-/
#check (inv_mul_cancel a : a⁻¹ * a = 1)
#check (one_mul a : 1 * a = a)
#check (mul_one a : a * 1 = a)

/-
  From these, we can prove that `a*a⁻¹ = 1`.  The trick is to use
    `1 = (a*a⁻¹)⁻¹ *(a*a⁻¹)`.
-/

theorem mul_inv_cancel : a*a⁻¹ = 1 :=
  sorry

/-
  We'll need this to prove the following theorems about cancellation.
-/
theorem mul_left_cancel {a b c : G} (h : a * b = a * c) : b = c := sorry

theorem mul_right_cancel {a b c : G} (h : a*b = c*b) : a = c := sorry

/-
  Now, we can use cancellation to prove that f 1 = 1.
  This result proves that nothing is lost by the stronger form of
  morphism of groups.
-/
example (f : G →* H) : f 1 = 1 := sorry


/-
  With a little induction, this result allows us to conclude that
  for all `n : ℕ`, `f (a^n) = (f a)^n`.  We use the two theorems
  `pow_zero` and `pow_succ` we discussed in the section on Monoids
  in combination with `map_one` and `map_mul`.
-/

example (a : G) : a^0 = 1 := pow_zero a
example (n : ℕ) (a : G) : a^(n+1) = a^n*a := pow_succ a n
example (f : G →*H) : f 1 = 1 := map_one f
example (f : G →* H) (a b : G) : f (a*b) = (f a) * (f b) := map_mul f a b


theorem map_npow (n : ℕ) (f : G →* H) (a : G) : f (a^n) = (f a)^n := by
  induction n with
  | zero =>
    sorry
  | succ n ih =>
    sorry

/-
  We can extend this to the full set of integers by proving that `f`
  preserves inverses.  First, it's helpful to prove a couple lemmas
  about the properties that define the inverse.
-/

theorem eq_inv_of_mul_eq_one_left {a b : G} (h : a * b = 1) : a = b⁻¹ := sorry

theorem eq_inv_of_mul_eq_one_right {a b : G} (h : a * b = 1) : b = a⁻¹ := sorry

/-
  This means to prove f a⁻¹ = (f a)⁻¹, it suffices to prove either
    `f (a⁻¹) * (f a) = 1` or `(f a) * f (a⁻¹)`.
-/

theorem map_inv (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ := by
  have h : f (a⁻¹) * f a = 1 := calc
    f (a⁻¹) * f a = f (a⁻¹ * a) := by rw[map_mul]
    _= f 1 := by rw[inv_mul_cancel]
    _= 1 := by rw[map_one]

  have h' : f a * f (a⁻¹) = 1 := calc
    f a * f (a⁻¹) = f (a * a⁻¹) := by rw[map_mul]
    _= f 1 := by rw[mul_inv_cancel]
    _= 1 := by rw[map_one]

  exact eq_inv_of_mul_eq_one_left h
  --exact eq_inv_of_mul_eq_one_right h'

/-
  Now we're ready to extend to the integers.  We'll use the
  `zpow_neg` function we've encountered with DivisionMonoids.
-/

example (n : ℤ) (a : G) : a^(-n) = (a^n)⁻¹ := zpow_neg a n
example (n : ℕ) (f : G →* H) (a : G) : f (a^n) = (f a)^n := map_npow n f a
example (a : G) : a^(0:ℤ) = a^(0:ℤ) := by exact rfl

#check zpow_ofNat
example (f : G →* H) (a : G) : f (a^0) = (f a)^0 := map_npow 0 f a
theorem map_zpow (n : ℤ) (f : G →* H) (a : G) : f (a^n) = (f a)^n := by
  match n with
  | (n : ℕ) =>
  /-
    The symbol `↑n` represents the coercion of `n : ℕ` to `↑n : ℤ`.  Since
    `n : ℕ`, `n` and `↑n` should be the same.  The tactic `norm_cast`
    is used to rewrite the goal as `f (a^n) = (f a)^n`.
  -/
    norm_cast
    exact map_npow n f a
  | Int.negSucc n =>
    have : Int.negSucc n = -(n+1) := rfl
    rw[this,zpow_neg,zpow_neg,map_inv]
    norm_cast
    have : (f (a^(n+1)))⁻¹ * (f a)^(n+1) = 1 := by
      rw[← map_npow (n+1) f a,inv_mul_cancel]
    exact eq_inv_of_mul_eq_one_left this

/-
  Just as with normal functions, we can compose morphisms.  However, because
  morphisms are "bundled" maps, we need to use the `comp` function.
-/

variable {K : Type u} [Group K]

example (f : G →* H) (g : H →* K) : G →* K := by
  exact MonoidHom.comp g f
  --Equivalently, `exact g.comp f`

/-
  Importantly, Lean also provides a notion of isomorphism via `MulEquiv`.
  Depending on your perspective, you might find one of the following definitions for an isomorphism.

  1. A morphism `f : G → H` is an isomorphism if `f` is bijective.
  2. A morphism `f : G → H` is an isomorphism if there exists a morphism `g : H → G` such that
     `g ∘ f = id_G` and ` f ∘ g = id_H`.  That is to say, for every `x : G` and `y : H`,
     `g (f x) = x` and `f (g y) = y`.

  Mathematically, these definitions are equivalent.  It's not hard to prove a function
    · has a left inverse if and only if it is injective, and
    · has a right inverse if and only if it is surjective.
  From this, it follows that (2) is equivalent to (1).

  However, in Lean, there is a major difference between these.  The proof that a function is
  bijective if and only if it has an inverse requires the Axiom of Choice.  In terms of Lean,
  this means only *one* of these definitions is actually computable.  Hence Lean opts for the second
  definition over the first, but provides for the non-computable option.
-/

example (f : G ≃* H) : H ≃* G := f.symm

noncomputable example (f : G →* H) (h : Function.Bijective f) : G ≃* H := MulEquiv.ofBijective f h


end Morphisms_of_Groups

end Lecture_20
