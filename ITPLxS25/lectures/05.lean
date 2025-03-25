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

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (λ x ↦ f x + g x) (a + b) :=
  λ x : ℝ ↦ add_le_add (hfa x) (hgb x)


section variable (h_fa : FnLb f a) (h_gb : FnLb g b)
#check (λ x : ℝ ↦ add_le_add  (h_fa x) (h_gb x))

/-
  Exercise: Formalize the analogous statement for lower bounds.
-/
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (λ x ↦ f x + g x) (a + b) :=
  λ x : ℝ ↦ add_le_add (hfa x) (hgb x)

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
#check (mul_le_mul : (a ≤ b) → (c ≤ d) → (0 ≤ c) → (0 ≤ b) → (a * c ≤ b * d))
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
    FnUb (fun x ↦ f x * g x) (a * b) := sorry
end Lecture_05
