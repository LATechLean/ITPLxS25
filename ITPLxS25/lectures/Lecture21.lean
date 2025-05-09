import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.Ring
import Init.Data.Int.Basic

namespace Lecture_21

/-
  A ring is a set, `R`, equipped with two compatible structures:
    · An abelian group structure `(R,+)` with additive identity 0, and
    · A monoid structure `(R,*)` with additive identity 1.
  Naturally, a morphism of rings is a function `f : R → S` that
  preserves these two structures:
    1. `f` is a morphism of additive abelian groups in the sense that
       `f(r₁ + r₂) = f(r₁) + f(r₂)`, and
    2. `f` is a morphism of multiplicative monoids in the sense that
          · `f(r₁r₂) = f(r₁)f(r₂)`, and
          · `f(1) = 1`.
  Lean implements this behavior through the `RingHom` class which defines
  the type `R →+* S` and (as expected) extends both `R →+ S` and `R →* S`.

    `structure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β] extends`
    `α →* β, α →+ β, α →ₙ+* β, α →*₀ β`
-/

variable {R S : Type u} [Ring R] [Ring S]

example (a b : R) (f : R →+* S) : f (a*b) = f a * f b := f.map_mul a b
example (a b : R) (f : R →+* S) : f (a+b) = f a + f b := f.map_add a b
example (f : R →+* S) : f 0 = 0 := f.map_zero
example (f : R →+* S) : f 1 = 1 := f.map_one

/-
  As with groups, an isomorphism of rings is defined to be an invertible
  morphism of rings.  That is, `f : R →+* S` is an isomorphism of rings
  if there exists a morphism of rings `g : S →+* R` such that
    `g ∘ f = id_R` and `f ∘ g = id_S`.
  This is implemented by the `RingEquiv` class
-/

example (f : R ≃+* S) : S ≃+* R := RingEquiv.symm f -- Equivalently, f.symm
noncomputable example (f : R →+* S) (h : Function.Bijective f) : R ≃* S :=
  RingEquiv.ofBijective f h

variable {R : Type u} [AddCommGroup R] [Mul R] [One R]
example (a : R) : a + -a = 0 := by exact add_neg_cancel a

end Lecture_21
