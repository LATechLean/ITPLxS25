import Mathlib
namespace Lecture_05
/-
Dependent Types
-/

/-
  So far, we have seen only simple types such as String, Bool, Prop, ℕ, etc.
  Lean also supports a notion of Dependent Type, which allows the type to depend
  on some input.  As we focus on quantifiers, our primary focus will be on
  dependent types of the form α → Prop.  In logic, we refer to these as Predicates.
  A predicate is a logical statement whose truth value depends on some parameter.
-/

/-
  For example, a simple predicate could be "The integer n is nonnegative."
  The truth value of this statement depends on the integer, n, involved.  For example,
    · The integer 7 is nonnegative.
        - This statement is true.
    · The integer -5 is nonnegative.
        - This statement is false.

  We can therefore view this predicate as a function that accepts an integer as input
  and outputs a proposition.  In Lean, this is the dependent type ℤ → Prop, where
  ℤ stands for the type of the integers (e.g. 0, ±1, ±2, ±3, ...).
-/

def is_nonneg (n : ℤ) : Prop := 0 ≤ n
#check (is_nonneg : ℤ → Prop)

/-
  Universal Quantifiers
-/

/-
  We normally encounter predicates in quantified statements.  As a simple example,
  we might wish to describe a real-valued function of a single real variable as
  being bounded above or bounded below by a real number a.  This means the output
  of the function is guaranteed to be less than or equal to a (bounded above) or
  greater than or equal to a (bounded below).

  This is an example of a Universally Quantified statement because it expresses that
  for every value x in the domain of f, f x ≤ a.  In mathematics, we frequently
  translate such statements into symbols, such as
    ∀ x ∈ ℝ, f(x) ≤ a.
  The syntax in lean is similar
-/

section
variable (x : ℝ)

#check ∀ x : ℝ, 0 ≤ x^2

/-
  One proves such a statement by taking an abitrary element -- in this case a real number --
  and proving the predicate holds for this arbitrary element.  In Lean, this means the proof
  term should be of the form (λ x : ℝ ↦ ... ).  Fortunately, Mathlib provides a proof that
  0 ≤ x^2, so we can prove this proposition quite easily.
-/

#check sq_nonneg x
example : ∀ x : ℝ, 0 ≤ x^2 :=
  λ x : ℝ ↦ sq_nonneg x
end

/-
  We can define the property that a function f : ℝ → ℝ is bounded above/below by
  a real number a as follows.
-/

/-
  f : ℝ → ℝ is bounded above by a : ℝ if for every x : ℝ, f x ≤ a.
-/
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

/-
  f : ℝ → ℝ is bounded below by a : ℝ if for every x : ℝ, a ≤ f x.
-/
def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section

/-
  As an example of how to use this property, let's prove the following:
    If f is bounded above by a and g is bounded above by b, then f + g is
    bounded above by a + b.
-/

/-
  The informal proof is quite simple.

  Proof:  Assume f and g are functions, f is bounded above by a, and g is bounded above by b.
          Let x ∈ ℝ be given.  By assumption, f(x) ≤ a and g(x) ≤ b.  Hence
            (f + g)(x) = f(x) + g(x) ≤ a + b.
          Therefore f + g is bounded above by a + b.
-/

/-
  To formalize this proof from scratch in Lean, we would need to first prove a lemma
    ∀ a b c d : ℝ, a ≤ b → c ≤ d → a + c ≤ b + d
  which states for all real numbers a,b,c, and d, if a ≤ b and c ≤ d, then a + c ≤ b + d.
  Fortunately, Mathlib already contains a proof of this fact.
-/
end

section
variable (a b c d : ℝ) (h_ab : a ≤ b) (h_cd : c ≤ d)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add h_ab h_cd : a + c ≤ b + d)
end

variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) :=
  λ x : ℝ ↦ add_le_add (hfa x) (hgb x)


section variable (h_fa : FnLb f a) (h_gb : FnLb g b)
#check (λ x : ℝ ↦ add_le_add  (h_fa x) (h_gb x))

/-
  Exercise: Formalize the analogous statement for lower bounds.
-/
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

/-
  Use the following to prove that if f and g are nonnegative
  (i.e. bounded below by 0), then so is f*g.
-/
end

section
variable (a b : ℝ)
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a*b)
end

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  λ x : ℝ ↦ mul_nonneg (nnf x) (nng x)

/-
  Prove that if
    · f is bounded above by a,
    · g is bounded above by b,
    · g is nonnegative, and
    · a is nonnegative,
  then f*g is bounded above by a*b.
-/

/-
  You will need the theorem mul_le_mul_right
-/

section
variable (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (nnb : 0 ≤ b) (nnc : 0 ≤ c) (hbc : b ≤ c)
/-
  If a ≤ b, c ≤ d, and 0 ≤ b,c, then a * c ≤ b * d.
-/
#check (mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d)
#check (mul_le_mul hab hcd nnc nnb : a * c ≤ b * d)

/-
  Alternatively, you could use the following three theorems in conjunction.
-/

/- Multiply both sides of an inequality by a non-negative number on the right-/
#check (mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c)
#check (mul_le_mul_of_nonneg_right hab nnc : a * c ≤ b * c)

/- Multiply both sides of an inequality by a non-negative number on the left-/
#check (mul_le_mul_of_nonneg_left : a ≤ b → 0 ≤ c → c * a ≤ c * b)
#check (mul_le_mul_of_nonneg_left hab nnc : c * a ≤ c * b)

/- Inequality is a transitive relation: if a ≤ b and b ≤ c, then a ≤ c.-/
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans hab hbc : a ≤ c)
end

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
      sorry

/-
  Existential Quantifiers
-/

/-
  While the assertion f is bounded above by a is a universally quantified statement, asserting
  that a function is bounded above/below is an existential statement.  More precisely, when we say
  f : ℝ → ℝ is bounded above (resp. below), what we mean is
    ∃ a : ℝ, FnUb f a (resp. ∃ a : ℝ, FnLb f a).
-/

section

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

/-
  The elimination rule is used to produce from an existential statement a particular term
  that satisfies the quantified statement.

  As a concrete example, we prove that if f : ℝ → ℝ has an upper bound and g : ℝ → ℝ
  has an upper bound, then so does f + g : ℝ → ℝ.  In spirit, this proof is very similar
  to the first example using FnUb:
-/
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

/-
  Negating quantifiers
-/

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

section
end Lecture_05
