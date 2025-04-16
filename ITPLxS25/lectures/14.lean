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


end Lecture_14
