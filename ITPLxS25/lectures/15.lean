import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Lecture_15

section Injective_and_Surjective
open Function
open Set

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)
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
open Set
open Function

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
  intro x₁ x₁_nonneg x₂ x₂_nonneg h
  rw[mem_setOf] at x₁_nonneg
  rw [mem_setOf] at x₂_nonneg
  calc
    x₁ = √x₁ * √x₁ := by exact Eq.symm (mul_self_sqrt x₁_nonneg)
    _ = √x₂ * √x₂ := by rw[h]
    _= x₂ := by exact mul_self_sqrt x₂_nonneg

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x₁ x₁_nonneg x₂ x₂_nonneg h
  dsimp at h
  calc
    x₁ = |x₁| := Eq.symm (abs_of_nonneg x₁_nonneg)
    _ = √(x₁^2) := Eq.symm (sqrt_sq_eq_abs x₁)
    _ = √(x₂^2) := by rw [h]
    _ = |x₂| := (sqrt_sq_eq_abs x₂)
    _ = x₂ := abs_of_nonneg x₂_nonneg

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  apply Subset.antisymm
  case h₁ =>
    intro y ⟨x,x_nonneg,fx_eq_y⟩
    simp
    rw [← fx_eq_y]
    exact sqrt_nonneg x
  case h₂ =>
    intro x
    dsimp
    intro x_nonneg
    -- Since 0 ≤ x, x = √(x^2).
    exact ⟨x^2, sq_nonneg x, sqrt_sq x_nonneg⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  apply Subset.antisymm
  case h₁ =>
    intro y
    simp
    intro x fx_eq_y
    rw [← fx_eq_y]
    exact sq_nonneg x
  case h₂ =>
    intro y
    simp
    intro y_nonneg
    exact ⟨√y, sq_sqrt y_nonneg⟩
end InjOn

section Choice
open Classical
/-
  Lean provides a mechanism for the usual mathematical operation of
  "Let x be a … ".  This is very much not constructive, so Lean requires
  the line `noncomputatble section` to mark this behavior.
-/
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

/-
  Classical.choose is used to produce an element from an existential
  statement like `∃ x, P x`.
-/
#check choose h

/-
  Classical.choose_spec is proves that the chosen element meets the specification.
  In this particular case, the term `choose h` satisfies the predicate `P`.
-/

example : P (choose h) := choose_spec h

noncomputable section

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

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro injf
    intro a
    have h : ∃ x, f x = f a := ⟨a,rfl⟩
    rw[inverse,dif_pos h]
    apply injf
    exact choose_spec h
  · intro h
    intro x₁ x₂ fx₁_eq_fx₂
    calc
      x₁ = inverse f (f x₁) := by rw [h x₁]
        _ = inverse f (f x₂) := by rw[fx₁_eq_fx₂]
        _ = x₂ := by rw[h x₂]

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry
end

end Choice

end Lecture_15
