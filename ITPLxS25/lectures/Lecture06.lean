import Mathlib
import ITPLxS25.lectures.Lecture05

namespace Lecture_06
open Lecture_05


section  Existential_Quantifiers

/-
  While the assertion f is bounded above by a is a universally quantified statement, asserting
  that a function is bounded above/below is an existential statement.  More precisely, when we say
  f : ℝ → ℝ is bounded above (resp. below), what we mean is
    ∃ a : ℝ, FnUb f a (resp. ∃ a : ℝ, FnLb f a).
-/

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a : ℝ, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a : ℝ, FnLb f a

/-
  The existential quantifier, ∃, comes equipped with an introduction and elimination rule.
  Say we have a predicate, p : α → Prop.  The introduction rule, Exists.intro, is used to
  create a term of type
    ∃ x : α, p x.
  That is, to prove a statement "There exists x such that p x is true."

  NOTE: The anonymous constructor works for Exists just as for conjunction and Iff.
-/


section
  variable (α : Type) (a : α) (p : α → Prop) (h_a : p a)
  #check (Exists.intro a h_a : ∃ x, p x)

  #check (⟨a, h_a⟩ : ∃ x, p x)
end

section
/-
  The elimination rule is used to produce from an existential statement a particular term
  that satisfies the quantified statement.

  As a concrete example, we prove that if f : ℝ → ℝ has an upper bound and g : ℝ → ℝ
  has an upper bound, then so does f + g : ℝ → ℝ.  In spirit, this proof is very similar
  to the first example using FnUb:
-/
variable (f g: ℝ → ℝ) (a b : ℝ)
example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) :=
    λ x : ℝ ↦ add_le_add (hfa x) (hgb x)
/-
  The difference here is that the first example provides us with the bounds (a and b)
  as hypotheses, while this example merely asserts they exist.

  This means we will first need to use the elimnation rule to produce the actual upper bounds
  for f and g.  Once we have the upper bounds, a and b, we can prove
    f x + g x ≤ a + b
  using add_le_add.  Finally, we use Exists.intro with the terms of type a + b and
  f x + g x ≤ a + b to introduce the existential statement
    ∃ c : ℝ, FnUb f c.
-/
end

section
variable (f g : ℝ → ℝ)
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  Exists.elim ubf
    λ (a : ℝ) (h_a : FnUb f a) ↦ Exists.elim ubg
      λ (b : ℝ) (h_b : FnUb g b) ↦
        have h_ab : ∀ x, f x + g x ≤ a + b :=
          λ x : ℝ ↦ add_le_add (h_a x) (h_b x)
        ⟨a + b, h_ab⟩ -- Equivalent to Exists.intro (a + b) h_ab

/-
  While usable, the notation
    Exists.elim h λ (w, h_w) ↦ ...
  is somewhat clunky.  Lean also provides a useful construct called match
  that can make this operation a little nicer:
    match h with
    | ⟨ w , h_w ⟩ => ...
-/

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf with
  | ⟨a, h_a⟩ => match ubg with
    | ⟨b, h_b⟩ =>
      have h_ab : ∀ x, f x + g x ≤ a + b :=
        λ x : ℝ ↦ add_le_add (h_a x) (h_b x)
      ⟨a + b, h_ab⟩

/-
  The match construct really shines when our predicate also works with the
  anonymous constructor, such as existential statements about conjunction.
-/
end

section
variable (α : Type) (p q : α → Prop)

/-
  Consider the following example, where we explicitly use the introduction and
  elimination rules by name.  The argument is simple, but the proof is rather verbose.
-/
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h λ (x : α) (h_x : p x ∧ q x) ↦
    Exists.intro x (And.intro h_x.right h_x.left)

/-
  We could down our verbosity a bit by using anonymous constructors for Exists.intro
  and And.intro.

  NOTE: If we want to construct an element of type ∃ x, q x ∧ p x from the terms x,
  h_x.left, and h_x.right, the naive use of the anonymous constructor is
    ⟨x, ⟨h_x.right, h_x.left⟩⟩
  where the inner langle/rangle constructs the term q x ∧ p x.  However, the anonymous
  constructor is smart enough to understand from context that
    ⟨x, h_x.right, h_x.left⟩
  indicates it should construct an element of type ∃ x, q x ∧ p x.  This saves us a
  some nasty nested langle/rangles
-/

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h λ (x : α) (h_x : p x ∧ q x) ↦
    ⟨x,h_x.right,h_x.left⟩

/-
  Similarly, the match construction is clever enough to destruct the term
    ∃ x, p x ∧ q x
  into three terms of type x, p x, and q x, which makes our proof even more concise
  than before.
-/

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨x, h_px,h_qx⟩ => ⟨x, h_qx,h_px⟩

/-
  We should also point out that the let construct is equally capable of this type of
  pattern matching.  If we're code golfing, this is likely the winner.
-/

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := let ⟨x, h_px, h_qx⟩ := h; ⟨x, h_qx, h_px⟩

end

end Existential_Quantifiers

section Negating_Quantifiers

/-
  On a first pass, negating quantifiers is frequently a difficult task.  In general, it requires
  that one judiciously exchanges ∀ and ∃ and negate the statement.
-/

section
variable (α : Type) (p : α → Prop)

/-
  First, we prove how to negate a universally quantified predicate.

  We start with the proof that ∀ x, p x → ∃ x, ¬p x.

  Proof:  Assume ¬(∀ x, p x).  We proceed by contradiction.  Suppose ¬∃ x, ¬p x.
          Let x be given. Suppose for contradiction that ¬p x. Hence
            ∃ x, ¬p x
          contrary to the supposition that ¬∃ x, ¬p x.  Therefore ∃ x, ¬p x.  QED.
-/

example : ¬(∀ x, p x) → (∃ x, ¬p x) :=
  λ h : ¬(∀ x, p x) ↦
    show ∃ x, ¬p x from Classical.byContradiction
      λ h' : ¬∃ x, ¬p x ↦
        show False from h
          λ x ↦ show p x from Classical.byContradiction
        λ h_npx : ¬p x ↦ h' ⟨x, h_npx⟩

/-
  Next, we prove the converse.

  Proof:  Assume ∃ x, ¬p x.  Suppose to the contrary ∀ x, p x.
          By assumption, there exists x such that ¬p x.  Contradiction.
          Therefore ¬(∀ x, p x).
-/

example : (∃ x, ¬p x) → ¬(∀ x, p x) :=
  λ (h_ex : ∃ x, ¬p x) (h_un : ∀ x, p x) ↦
    let ⟨x, h_npx⟩ := h_ex
    have h_px : p x := h_un x
    h_npx h_px

/-
  Similarly, we can prove the negation of ∃ x, p x is ∀ x, ¬p x.
-/

/-
  Proof:  Assume ¬(∃ x, p x).  Let x be given.  Suppose for contradiction p x.
          Hence ∃ x, p x.  This contradicts the assumption ¬∃ x, p x and thus ¬p x.
          Therefore ∀ x, ¬p x because x was arbitrary.
-/
example : ¬(∃ x, p x) → (∀ x, ¬p x) :=
  λ (h : ¬∃ x, p x) (x : α) (h_px : p x) ↦
    h ⟨x, h_px⟩

/-
  Now we prove the converse.

  Proof:  Assume ∀ x, ¬p x.  Suppose for contradiction ∃ x, p x.
          This clearly contradicts the assumption ∀ x, ¬p x.
          Therefore ¬∃ x, p x.
-/
example : (∀ x, ¬p x) → ¬(∃ x, p x) :=
  λ (h : ∀ x, ¬p x) (h_absurd : ∃ x, p x) ↦
    let ⟨x,h_px⟩ := h_absurd
    have h_npx : ¬p x := (h x)
    show False from h_npx h_px
end

/-
  Now that we know the formalism, let's put it into practice with a concrete exercise.
  We prove that f : ℝ → ℝ is unbounded if for all a : ℝ, there exists x : ℝ such that
  f x > a.  Let's start with the informal proof first.
-/

/-
  Proof:  Assume for all a ∈ R, ∃ x ∈ R such that a < f(x).
          Suppose for contradiction that f has an upper bound, ub.
          Hence for all x ∈ ℝ, f(x) ≤ ub.
          By assumption, there exists x ∈ ℝ such that ub < f(x).
          Contradiction.  Therefore f does not have an upper bound.
-/

/-
  In order to derive the contradiction, we rely on Lean to prove
    ub < fx ≤ ub
  implies ub < ub and that this is absurd.  The tools we need are
    · lt_of_lt_of_le
        - This naming convention seems completely absurd at first.  The first lt means the
          result is a strict inequality. The of_lt_of_le means this strict inequality is
          obtained by combining a strict inequality with a non-strict inequality.
          That is to say, if a < b and b ≤ c, then a < c.
    · lt_irrefl
        - This asserts that the binary relation < is Irreflexive.  Recall that to be reflexiv,
          a relation, R, must satisfy the condition ∀ a, a R a.  To be irreflexive asserts the
          negation: ∀ a : ℝ, ¬(a < a).
-/

section
variable (a b c : ℝ) (hab : a < b) (hac : b ≤ c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_of_lt_of_le hab hac : a < c)

#check (lt_irrefl a : ¬a < a)

example (h : a < a) : False :=
  lt_irrefl a h
end

section
variable (f : ℝ → ℝ)
example (h : ∀ a : ℝ, ∃ x : ℝ, f x > a) : ¬FnHasUb f :=
  λ h_fbndd : FnHasUb f ↦
    let ⟨ub,h_ub⟩ := h_fbndd
    have h_contra : ∃ x : ℝ, ub < f x := h ub
    let ⟨x, h_x⟩ := h_contra
    have h_ub_lt_self : ub < ub :=
      lt_of_lt_of_le h_x (h_ub x)
    lt_irrefl ub h_ub_lt_self
end

end Negating_Quantifiers

end Lecture_06
