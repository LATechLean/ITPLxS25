import Mathlib
namespace Lecture_13
open Set

variable {α : Type*} (s t u : Set α) (x : α)

/-
  Sets in lean are simply predicates
    def Set (α : Type u) := α → Prop

  Lean provides all the usual set operators that you already
  know:
    · ⊆
    · ∈
    · ∩
    · ∪
    · \
-/

section Set_Builder_Notation

/-
  Lean supports set-builder notation.  It requires a predicate, just as
  normal set-builder notation would.
-/

variable (p : α → Prop) (a : α)

#check {a | p a}
def evens : Set ℕ := {n | Even n}
def odds : Set ℕ := {n | ¬Even n}

/-
  We can prove the union of these two sets is the universe (ℕ).
-/

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

end Set_Builder_Notation

section Subsets
/-
  Subset works the way you would expect. There is a handy theorem that will
  allow you to rewrite it in this form:
    theorem subset_def : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t

  This allows us to prove obvious things like the following.
-/

example (h_xs : x ∈ s) (h_st : s ⊆ t) : x ∈ t := by
  rw [subset_def] at h_st
  apply h_st
  exact h_xs

/-
  There are a bunch of useful theorems in Basic.lean.  You can browse them by
  right-clicking subset_def and selecting Go To Definition.  Here are a few
  that might be valuable.
    · theorem union_def {s₁ s₂ : Set α} : s₁ ∪ s₂ = { a | a ∈ s₁ ∨ a ∈ s₂ }
    · theorem inter_def {s₁ s₂ : Set α} : s₁ ∩ s₂ = { a | a ∈ s₁ ∧ a ∈ s₂ }
    · theorem mem_def {a : α} {s : Set α} : a ∈ s ↔ s a
    · theorem mem_setOf {a : α} {p : α → Prop} : a ∈ { x | p x } ↔ p a
    · theorem mem_inter_iff (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b
-/

end Subsets

section Intersections_and_Unions
/-
  Here's a slightly more interesting example.
-/
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf] -- `only` restricts the tools available to simp.
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  /-
    The rintro tactic is nice for destructuring.  In this case, we break
      ∀ x, x ∈ s ∧ x ∈ u
    into the hypotheses x, xs : x ∈ s, xu : x ∈ u
  -/
  rintro x ⟨xs, xu⟩
  /-
    We've encountered wildcards before.  They can be used in application
    to ask Lean to infer an argument from context.  Technically, the full
    call here is
      h x xs
    but the wildcard forces Lean to infer x for us.
  -/
  #check (h _ xs : x ∈ t)

  /-
    Remember, Lean is quite clever.  The same tricks for And work for ∩:
  -/
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  #check (h xsu.1 : x ∈ t)
  #check (xsu.2 : x ∈ u)
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  λ _ ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  /-
    The `rcases` tactic splits the or into two cases
      · xt : x ∈ t
      · xu : x ∈ u
  -/
  rcases xtu with xt | xu
  · left -- The `left` tactic tells Lean we want to prove x ∈ s ∩ t.
    show x ∈ s ∩ t
    constructor <;> assumption
  · right -- Similarly, the `right` tactic tells Lean we want to prove x ∈ s ∩ u.
    show x ∈ s ∩ u
    constructor <;> assumption

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; constructor <;> assumption
  · right; constructor <;> assumption

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry

end Intersections_and_Unions

section Set_Difference
/-
  Set difference is defined in the usual way:
    theorem mem_diff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t
  This means that set differences have projections `.left` or `.1` and `.right` or `.2`.
  They can also be constructed like an And statement.
-/

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  case left => exact xs
  case right =>
    intro xtu
    -- x ∈ t ∨ x ∈ u
    /-
      The rcases tactic allows us to split xtu into the two cases
        · xt : x ∈ t,
        · xu : x ∈ u.
      Both lead to contradictions.
    -/
    rcases xtu with xt | xu
    · contradiction
    · contradiction


/-
  A slightly slicker version that uses rintro to split the x ∉ t ∪ u
  version into two cases and the sequence combinator to finish it off.
-/
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  sorry

end Set_Difference

section Equality_of_Sets
/-
  There are a couple different ways to prove equalities involving sets.
  One is the `ext` (extensionality) tactic.  In this context, `ext` reduces
  proving equality to proving every element of one is an element of the other.

  The following example shows how `ext` reduces this to the familiar proof of
    p ∧ q ↔ q ∧ p.
-/
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

/-
  A term version of this proof.
-/
example : s ∩ t = t ∩ s :=
  Set.ext λ _ ↦ ⟨λ ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, λ ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

/-
  If we're not concerned with mechanics, this is handled easily by simp using
   theorem and_comm : a ∧ b ↔ b ∧ a
-/
example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

/-
  Another way to handle equality is to use antisymmetry.  This is the idea that
  two sets are equal if and only if each is a subset of the other.
    theorem Subset.antisymm {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b
-/
example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm sorry sorry

example : s ∩ (s ∪ t) = s := by
  sorry

example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  sorry

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry
end Equality_of_Sets


section Indexed_Sets

variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

/-
  Type-theoretically, we a sequence of sets
    A₀, A₁, A₂, …
  as a function A : ℕ → Set α. The indexed intersection/union is then
    ∪ i, A i
    ∩ i, A i
  There's nothing special about ℕ: we can use any type I to index, analogous
  to allowing any set to index a collection of sets.
-/

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end Indexed_Sets
end Lecture_13
