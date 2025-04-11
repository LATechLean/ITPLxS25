import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Lecture_14

section Functions
open Function
open Set
/-
    Recall that sets in Lean are predicates.  Namely, constructing
    `s : Set α` is equivalent to providing a predicate `p : α → Prop`.
    One way to interpret this set-theoretically is to think about `α`
    as being the "Universe of Discourse", so that in some sense
    `s ⊆ α`.

    When we talk about set functions in Lean, we always assume
    our mappings come from mappings between these "universes of discourse"
    (e.g. `f : α → β`), so that we can always talk about the image of `s`
    as some "subset" of `β` and the preimage of `t` as some "subset" of `α`.
-/

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

/-
    Lean provides the notions of `preimage f u`, which is defined to be the
    set
        {a : α | f a ∈ t}
    and `image f s`, which is defined to be the set
        {b : β | ∃ a : α, a ∈ s ∧ f a = b}
    It also provides shorthand for each:
        · `f ⁻¹' u` for the preimage of `u` under `f`, and
        · `f '' s` for the image of `s` under `f`.
-/

#check preimage f u
#check image f s

namespace hidden
inductive myFiniteType₁ where | a | b | c
inductive myFiniteType₂ where | d | e

open myFiniteType₁
open myFiniteType₂

def finiteFunction : myFiniteType₁ → myFiniteType₂
| a => d
| b => d
| c => d

#check ({a,b,c} : Set myFiniteType₁)
#check ({d} : Set myFiniteType₂)

example : preimage finiteFunction {e} = ∅ := by
    ext x
    constructor
    · intro
      cases x <;> contradiction
    · intro
      simp
      contradiction

example : preimage finiteFunction {d} = {a,b,c} := by
    ext x
    constructor
    · intro hx
      cases x <;> simp
    · intro hx
      simp
      cases x <;> trivial

example : finiteFunction '' {a,b,c} = {d} := by
    ext y
    constructor
    /-
        Being in the image bundles three pieces of data
            · An element x,
            · An assertion that x ∈ {a,b,c}
            · An assertion that f x = y.
    -/
    · rintro ⟨x, hx ,hfx⟩
      rw[← hfx]
      cases x <;> trivial
    · rintro hy
      rw[mem_singleton_iff] at hy
      rw[hy]
      use a
      constructor
      · simp
      · trivial

end hidden

/-
  Most of these exercises can be done using ext and rewrites of
    · image
    · preimage,
    · mem_setOf,
-/

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  sorry

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  sorry

example : s ⊆ f ⁻¹' (f '' s) := by
  sorry

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry
end Functions

section Injective_and_Surjective
/-
  Lean also provides notions of injectivity and surjectivity.
  Recall that f : s → t is injective if
    ∀ s₁, s₂ ∈ s , f s₁ = f s₂ → s₁ = s₂
  and surjective if
    ∀ t ∈ t, ∃ s ∈ s, t = f s.
  In lean these are
    · def Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
    · def Surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b

  Most of these exercises can be done using rewrites of
    · image
    · preimage,
    · mem_setOf,
    · injective,
    · surjective.
-/
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry

example : f '' (f ⁻¹' u) ⊆ u := by
  sorry

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by

  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  sorry

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry
end Injective_and_Surjective

section InjOn

/-
  Lean also provides a predicate called InjOn to indicate that f is
  injective on a specific set.
    InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂
-/

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry
end InjOn

section Choice

/-
  Lean provides a mechanism for the usual mathematical operation of
  "Let x be a … ".  This is very much not constructive, so Lean requires
  the line `noncomputatble section` to mark this behavior.
-/
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

/-
  When dealing with `if … then … else`, the identity `dif_pos` can be used to obtain the
  `then` statement, provided a proof of the `if` clause.
-/
theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry
end

end Choice

end Lecture_14
