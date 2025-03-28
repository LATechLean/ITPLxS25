import ITPLxS25.lectures.«06»
open Lecture_05
open Lecture_06

namespace Lecture_07

section Equality

/-
  In Lean, equality is defined via the type Eq.  It is the canonical
  equivalence relation, meaning equality is
    · Reflexive: ∀ a, a = a,
    · Symmetric: ∀ a b, a = b → b = a, and
    · Transitive: ∀ a b c, a = b ∧ b = c → a = c.
  The first, Eq.refl, is actually the constructor for the Eq type.
  The other two properties are the theorems Eq.symm, and Eq.trans.
-/


variable (α β γ : Type) (h₁ : α = β) (h₂ : β = γ)
#check (Eq.refl α : α = α)

#check (Eq.symm : α = β → β = α)
#check (Eq.symm h₁ : β = α)
#check (Eq.symm (Eq.symm h₁) : α = β)
#check (h₁.symm : β = α)                            -- Projection notation

#check (Eq.trans : α = β → β = γ → α = γ)
#check (Eq.trans h₁ h₂ : α = γ)
#check (h₁.trans h₂ : α = γ)                        -- Projection notation


/-
  By virtue of the type system, reflexivity is often more powerful in Lean
  than one might expect.  At face value, it's used to prove two things are
  definitionally equal, but it can frequently reduce seemingly non-trivial
  tasks to definitional equality by construction.  This is often very handy.
-/

example : 2 + 3 = 5 := Eq.refl 5
example : 2 + 3 = 5 := Eq.refl (2 + 3)
example : 2 + 3 = 5 := Eq.refl _

/-
  In the third example, we use the wildcard to let Lean infer which term
  it will use as the argument to Eq.refl. Lean provides a built-in notation
  for exactly this sort of thing, rfl.
-/

example : 2 + 3 = 5 := rfl

/-
  Lean can also infer more complicated objects are definitionally equal.
-/

example (α : Type) (a : α) : (λ _ ↦ 0) a = 0 := rfl
example (α β : Type) (a : α) (b : β) : (a,b).1 = a := rfl

theorem foo (p q : Prop) (h_p : p) (h_q : q) : p ∨ q := Or.inl h_p
theorem bar (p q : Prop) (h_p : p) (h_q : q) : p ∨ q := Or.inr h_q
example : foo = bar := rfl

/-
  Unsurprisingly, we can substitute one value for another, provided they
  are actually equal.
-/

example (α : Type) (a b : α) (p : α → Prop)  (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

/-
  Lean provides a shorthand, ▸, for this which can be typeset using \t.
-/

example (α : Type) (a b : α) (p : α → Prop)  (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

/-
  Lean extends this to applications (i.e. function calls) using
    · congrArg
    · congrFun
    · congr
-/

variable (α : Type) (a b : α) (f g : α → Nat) (h₁ : a = b) (h₂ : f = g)

example : f a = f b := congrArg f h₁  -- replace a with b
example : f a = g a := congrFun h₂ a  -- replace f with g
example : f a = g b := congr h₂ h₁    -- replace f with g, a with b.

end Equality

section Tactics

/-
  Up until now, we have been proving results by constructing terms explicitly.
  Lean provides a second mechanism for proving results called Tactic Mode.
  A tactic is a command that tells Lean to construct proof terms for you.
-/

section Tactic_Mode
/-
  Whenever we write an example, lemma, theorem, or have statement, we can enter tactic
  mode using the keyword by to create a tactic block.

  Inside a tactic block, we see the exact same information we would normally see when
  writing a term proof.
-/

/-
  As we have seen, constructing proof terms usually requires us to think in the forward
  direction, unless we explicitly utilize the
    suffices ... from ...
  construction.  By contrast, reasoning in Tactic Mode naturally runs backward more often
  than not.  This is because one of the main tools is the apply tactic, which applies a
  result to the goal.

  For example, consider the following term proof.
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  ⟨hp,hq,hp⟩

/-
  As a tactic proof, we progress in our goal using apply.
-/
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  -- Our goal is to prove a conjuction, so we start by applying And.intro
  apply And.intro
  /-
    This breaks the p ∧ q ∧ p = p ∧ (q ∧ p) into two subgoals: p, p ∧ q.
    Note that Lean even tags these two subgoals with the names left and right.
    The subgoal left p, which we close using the exact tactic.
      - exact functions similarly to apply, but matches the goal exactly.
  -/

  exact hp

  /-
    The second subgoal is p ∧ q.  We could close this goal immediately with either of
    the commands
      exact ⟨hq,hp⟩ or exact And.intro hq hp
    In the spirit of Tactic Mode, we opt for apply And.intro.  This splits the goal
      p ∧ q
    into the two subgoals p, q.
  -/

  apply And.intro
  exact hq
  exact hp

/-
  We can peer into the proof that Lean creates using #print.  We can see Lean generated
  precisely the proof term
    λ (p q : Prop) (h_p : p) (h_q : q) ↦ ⟨hp,⟨hq,hp⟩⟩
-/
#print test


/-
  NOTE: The tags we observed in the subgoals provides us a way to improve readability
        in our Tactic Mode proofs using the case keyword.
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

/-
  Additionally, lean provides bullet notation as a visual cue to indicate cases.
  Typeset the bullet using \.
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · exact ⟨hq,hp⟩

end Tactic_Mode

section Intro

/-
  The tactic intro allows us to introduce hypotheses from statements.  The intro tactic
  is generally used when you would start a proof with a function, such with goals of the
  form
    · t ↦ ...
    · ∀ t, ...
  When writing term proofs we usually move a term into our context using
    λ h ↦ ... or λ x ↦ ...
  In tactic mode,
    intro h or intro x
  has the same effect.

  NOTE: Just like with λ-abstractions, you can move multiple hypotheses into your context
  using a space separated list of names.  That is, if you would have used
    λ t₁ t₂ t₃ ↦ ...
  in a term proof, then you can use
    intro t₁ t₂ t₃
  in a tactic proof.
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  case mp =>
    intro h
    sorry
  case mpr =>
    intro h
    sorry

example(α : Type) : α → α := by
  intro a
  exact a

example (α β γ : Type) (h_γ : γ ) : α → β → γ  := by
  intro h_α h_β
  exact h_γ

/-
  Intro also allows for alternatives, akin to the match construct.  For example, we could handle
  the proof that disjunction is commutative as follows.
-/

example (p q : Prop) : (p ∨ q) → (q ∨ p) := by
  intro h
  apply Or.elim h
  case left =>
    intro h_p
    exact Or.inr h_p
  case right =>
    intro h_q
    exact Or.inl h_q

/-
  Matching allows us to split on the two cases
    1. p
    2. q
  directly using Or.inl and Or.inr.
-/
example (p q : Prop) : (p ∨ q) → (q ∨ p) := by
  intro
  | Or.inl h_px => exact Or.inr h_px
  | Or.inr h_qx => exact Or.inl h_qx

/-
  This construct can also be used with existential statements.
-/
variable (f : ℝ → ℝ) (a : ℝ)
#check Lecture_06.FnHasUb f
example : FnHasUb f → ∃ a : ℝ, FnUb f a := by
  intro
  | ⟨a, hfa⟩ => exact ⟨a, hfa⟩

/-
  Moreover, we can even use this with more elaborate nested constructs.
-/
example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨x, Or.inl h_px⟩ => exact ⟨x, Or.inr h_px⟩
  | ⟨x, Or.inr h_qx⟩ => exact ⟨x, Or.inl h_qx⟩

end Intro

section Rewrite
/-
  The rewrite (or rw) tactic allows us to make substitutions in goals and
  other hypotheses.
-/

example (f : ℕ → ℕ) (k : ℕ) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw[h₂,h₁]

/-
  Rewrite always reads from left-to-right by default.
  If we want it to go in the other direction, we can use a left arrow
  before the name of the term we're using to rewrite.
-/

example (f : ℕ → ℕ) (k : ℕ) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw[←h₁,h₂]

/-
  To rewrite a portion of a hypothesis, we can use the at keyword.
-/

example (a b : ℕ) (p : ℕ → Prop) (hab : a = b) (hpa : p a) : p b := by
  rw [hab] at hpa
  assumption

end Rewrite

section Simp
/-
  The simplifier, simp, is a handy tool for automation.  It essentially
  pushes otherwise mundane tasks onto Lean to save us time.
-/

example (x y z : ℕ) : (x + 0) * (0 + y*1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y)) : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp       -- reduces to p(x*y)
  assumption -- Apply h the lazy way.

/-
  We can also provide simp with extra pieces of information to improve automation.
-/
example (x y z : Nat) (p : Nat → Prop) (h : p (x * y)) : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp[h]

/-
  Just like rw, simp can be applied to hypotheses with the at keyword.
-/
example (x y z : Nat) (p : Nat → Prop) (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
        simp at h; assumption

/-
  The wildcard * can be used to point simp at ALL of the hypotheses.
-/

example (a b c: ℕ) (hab : a = b + 0) (hac : b = c + 0) : a = c := by
  simp at *
  apply Eq.trans <;> assumption

/-
  We can use the wildcard * to feed all of the hypotheses we have to simp.
-/

example (u w x x' y y' z : Nat) (p : Nat → Prop) (h₁ : x + 0 = x') (h₂ : y + 0 = y') : x + y + 0 = x' + y' := by
  simp at *
  simp [*]

end Simp

section Linarith
/-
  The tactic linarith automatically solves linear arithmetic goals using known linear inequalities or equalities.
-/

example (a b : ℤ) (h₁ : a ≤ b) (h₂ : b ≤ 5) : a ≤ 5 := by
  linarith

end Linarith

section Ring
  /-
    The ring tactic automatically proves equalities in commutative rings.  It handles
      · Addition
      · Multiplication
      · Associativity
      · Commutativity
      · Distributivity
      · Integer constants
      · Variables
      · Parentheses
    There is some overlap between proofs that can be automated by ring and by linarith.
  -/

example (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  ring

end Ring

section Assumption
/-
  The assumption tactic can be used to create a proof from the context in the Infoview window.
-/

/-
  Consider the proof that if x = y, y = z, and z = w, then x = w.  A traditional informal proof
  would look something like
    x = y
      = z
      = w.
  QED.
  This is transitivity of equality in action.
-/

/-
  If we were slightly less lazy in our proof writing, we might note this as two applications of transitivity:
    x = y and y = z implies x = z.
    x = z and z = w implies x = w.
  We can create a proof by nesting Eq.trans calls.
-/

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  exact Eq.trans (Eq.trans h₁ h₂) h₃

/-
  Alternatively, we can do the lazy thing with Lean.
-/
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by

  --We're going to use transitivity, so we might as well start by applying Eq.trans.
  apply Eq.trans
  -- Lean knows to start with x.  We ask Lean to unify this application with *something*
  -- in the context using the assumption keyword.
  assumption

  --We need transitivity again, so we apply Eq.trans again
  apply Eq.trans

  -- Now we let Lean sort out the pieces.
  assumption
  assumption

end Assumption

section Intros
/-
  We note that this proof doesn't actually use the names h₁, h₂, and h₃.  This tells us that if
  instead we had encountered the same statement in the following form, we can use the intros tactic
  to grab everything at once with randomly assigned names.

  NOTE: The intros names are inaccessible by default.
-/
example : ∀ a b c d: Nat, a = b → b = c → c = d → a = d := by
  intros
  apply Eq.trans
  assumption
  apply Eq.trans
  assumption
  assumption

end Intros

section Rename
/-
  If necessary, we can rename using rename_i
-/
  example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
    intros
    rename_i h_1 h_2 h_3
    apply Eq.trans
    apply Eq.symm
    assumption
    assumption

/-

-/
example (y : Nat) : (fun x : Nat => 0) y = 0 := Eq.refl _

end Rename

section Repeat
/-
  Repeat is a combinator -- it combines smaller tactic blocks -- that can be
  used to automate repetetive tasks.
-/

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  /- assumption
  assumption -/
  repeat assumption

end Repeat

section Revert
/-
  The revert tactic can be used to push a hypothesis back into the goal.
  It acts essentially like an inverse to intro.
-/

example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

example (x y : Nat) (h : x = y) : y = x := by
  revert h
  intro h₁
  apply Eq.symm
  assumption

/-
  NOTE: The revert tactic is clever.
    · You can revert more than one term at a time.
    · If you revert a term, it also reverts other terms that depend on it.
-/

example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  intros
  apply Eq.symm
  assumption
end Revert

end Tactics

end Lecture_07
