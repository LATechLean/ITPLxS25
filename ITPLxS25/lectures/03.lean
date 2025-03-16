import Mathlib

namespace Lecture_03
/-
  Propositions as Types

  In Lean, propositions are their own type, Prop. Two built-in terms of type Prop are
    · True - the proposition that is always true.
    · False - the proposition that is always false
-/

#check (True : Prop)
#check (False : Prop)

/-
  Lean has all of the familiar constructions for p q : Prop.
    · Negation: ¬p
    · Implication: p → q.
    · Conjunction: And p q or p ∧ q
    · Disjunction: Or p q or p ∨ q
    . Biconditional: p ↔ q.
-/

section
  variable (p q : Prop) (h_p : p) (h_np : ¬p)

  #check ¬p        -- A proposition named p
  #check h_p       -- A proof of p
  #check p ∧ q     -- The conjunction of p and q.
  #check p ∨ q     -- The disjunction of p and q.
  #check p → q     -- The conditional If p, then q.
  #check p ↔ q     -- The bicondition p if and only if q.
end

/-
  The case of negation is likely the strangest of the lot.  The type ¬p is
  actually shorthand for p → False.  We will see how this is useful in the future.
-/

section
  #check False
  variable (p : Prop) (h_np : ¬ p)
  #check (h_np : p → False)
end

/-
  In order to work with propositions and proof, we need a way to declare them.
  We have three keywords for doing so:
    · theorem
    · lemma
    · example
  A theorem and a lemma both have names, while an example does not.
  The keywords theorem and lemma behave the same, but provide information to the
  reader.  Generally, a lemma is a small result that is abstracted from the proof
  of a theorem.
-/

namespace hidden

-- If p : Prop is true, then p is true.
lemma myLemma : (p : Prop) → (h_p : p) → p  := sorry

/-
  If p and its negation are both true, we arrive at a contradiciton.
  This is to say, the assumption that p and its negation are both true implies the
  proposition (False) that is always false.
-/
theorem myTheorem : (p : Prop) → (h_p : p) → (h_np : ¬p) → False := sorry

/-
  Just as for functions, we can replace the → construction by placing arguments
  (hypotheses) to the left of the colon and the resulting type (conclusion) to the right.
-/


theorem myEquivalentTheorem (p : Prop) (h_p : p) (h_np : ¬p): False  := sorry

/-
  We can also move hypotheses outside the declaration using variables.
-/

section
variable (p : Prop)
theorem yetAnotherEquivalentTheorem (h_p : p) (h_np: ¬p) : False := sorry
end

/-
  We'll see soon that myTheorem and myEquivalentTheorem are definitionally equal.
  This means that Lean sees no difference between the two theorems.
-/
example : myTheorem = myEquivalentTheorem := sorry

/-
  We note the lemma and the theorem have function types, while the example has
  Prop as its type. Providing a proof of any of these statements is equivalent
  to constructing a term of the correct type.
-/

#check (myLemma : (p : Prop) → p → p)
#check (myTheorem : (p : Prop) → p → ¬p → False)
#check (myTheorem = myEquivalentTheorem : Prop)
end hidden

/-
  The first is trivial: if we assume p is true, then p is true.
  That is to say, our function has two input values
    · p : Prop
    · h_p : p,
  where h_p represents a proof that p is a true proposition, and so the output
  of our function is simply that same proof, h_p.
-/
example: (p : Prop) → (h_p : p) → p  :=
  λ (p : Prop) (h_p : p) ↦ h_p

/-
  For the second, we need to remember that h_np : ¬p is actually a function h_np : p → False.
  This means the composition
    h_np h_p : (p → False) p = False
  is precisely the False term we need to construct.
-/

example (p : Prop) (h_p : p) (h_np : ¬p) : False := h_np h_p

/-
  We should note that implication, p → q, behaves exactly as we expect from logic:
    · If p : Prop is true and q : Prop is true, then p → q : Prop is true.
    · If p : Prop is true and q : Prop is false, then p → q : Prop is false.
    · If p : Prop is false and q : Prop is true, then p → q : Prop is true.
    · If p : Prop is false and q : Prop is false, then p → q : Prop is true.
-/

/-
  The first and third are easy to prove.  We have assumed h_q : q, so we just need to
  construct functions of type p → q.  Essentially, a function that accepts a term of
  type p as input and outputs h_q.
-/
example (p q : Prop) (h_p : p) (h_q : q) : p → q :=
  (λ h : p ↦ h_q)

example (p q : Prop) (h_np : ¬p) (h_q : q) : p → q :=
  λ (h : p) ↦ h_q

/-
  Note: VS Code underlines the assumptions h_p and h_np in our example statements.
        This alerts us to the fact that these assumptions are not being used, so we could
        refactor each to the simpler example:
-/

example (p q : Prop) (h_q : q) : p → q :=
  λ (h_p : p) ↦ h_q

/-
  Note also that h_p : p is an unused assumption in the actual proof term.  We can omit it
  using the wildcard _ (underscore).
-/

example (p q : Prop) (h_q : q) : p → q :=
  λ _ ↦ h_q

/-
  The second is slightly trickier.  We recall that ¬(p → q) is actually a function of
  type (p → q) → False.  This allows us to think of this case as proving False using
  the following assumptions:
    · h_p : p
    · h_nq : q → False
    · h_pq : p → q
  We can produce a term of type q by applying h_pq to h_p, h_pq h_p : q.  We can apply
  h_nq to this term to obtain False, h_nq (h_pq h_p) : False.

  We can effectively think of this as a proof by contradiction.

  Proof: Assume p is true and q is false.  Suppose to the contrary that p → q is true.
         Since p is true and p → q, q is true by Modus Ponens.  This contradicts the
         assmption that q is false.  Therefore p → q is false.  QED.
-/

example (p q : Prop) (h_p : p) (h_q : ¬q) : ¬(p → q) :=
  λ (h_pq : p → q) ↦ h_q (h_pq h_p)

/-
  The final case, unfortunately, is not constructable.  That means there is no way
  in which we can use hypotheses
    · h_np : p → False
    · h_nq : q → False
  to construct p → q.

  However, as in classical logic, we can prove anything from a contradiction.
  This is known as the Principle of Explosion (ex falso quodlibet).  The proposition
  False comes equipped with an Elimination Rule, False.elim that we can use.
-/
section
variable (p : Prop) (h_p : p) (h_np : ¬p)
#check (h_np h_p : False)
#check False.elim (h_np h_p)
end

example (p q : Prop) (h_np : ¬p) (h_nq : ¬ q) : p → q :=
  λ (h_p : p) ↦ False.elim (h_np h_p)

/-
  Note: As before, we can see that h_nq is not relevant to this example, so we could
        refactor to the following simpler example.
-/

example (p q : Prop) (h_np : ¬p) : p → q :=
  λ (h_p : p) ↦ False.elim (h_np h_p)

/-
  Working with the the other logical structures (∧, ∨, ↔) require two rules
    · Introduction
      - Constructs a compound proposition from its components.
    · Elimination
      - Extracts information from a compound proposition.
-/

/-
  The disjunction comes equipped with two introduction rules -- one for the left
  and one for the right.
    · Or.inl constructs a proof term of type p ∨ q from a proof term of type p.
    · Or.inl constructs a proof term of type p ∨ q from a proof term of type q.
-/

/-
  The disjunction also comes with an elimination rule, Or.elim, which allows us to use
  a proof term h_pq : p ∨ q to complete a proof. It is essentially a proof by cases, so it
  takes two arguments
    · A proof of the result assuming the proof term  h_p : p, and
    . A proof of the result assuming the proof term h_q : q.
-/

/-
  To demonstrate their use, we show that p ∨ q behaves exactly as defined in a standard
  logic text:
    · If p and q are both true, then so is p ∨ q.
    · If p is true and q is false, then p ∨ q is true.
    · If p is false and q is true, then p ∨ q is true.
    · If p and q are both false, then so is p ∨ q.
-/

/-
  The first three require only the introduction rule.  In the first case, we can choose
  to use the left or the right introduction rule.  Both provide a proof of p ∨ q.
-/

example (p q : Prop) (h_p : p) (h_q : q): p ∨ q :=
  Or.inl h_p
example (p q : Prop) (h_p : p) (h_q : q): p ∨ q :=
  Or.inr h_q
example (p q : Prop) (h_p : p) (h_nq : ¬q) : p ∨ q :=
  Or.inl h_p
example (p q : Prop) (h_np : ¬p) (h_q : q) : p ∨ q :=
  Or.inr h_q

/-
  As above, there is no need to carry the extra hypotheses.
-/

example (p q : Prop) (h_p : p) : p ∨ q :=
  Or.inl h_p
example (p q : Prop) (h_q : q): p ∨ q :=
  Or.inr h_q
example (p q : Prop) (h_p : p) : p ∨ q :=
  Or.inl h_p
example (p q : Prop) (h_q : q) : p ∨ q :=
  Or.inr h_q


/-
  The final result is ¬(p ∨ q), which we recall is equivalent to p ∨ q → False.
  This says it is sufficient to derive a contradiction from
    · h_np : ¬p
    · h_nq : ¬q
    · h_pq : p ∨ q.
  The argument proceeds in cases.

  Proof: Assume p and q are both false. Suppose for contradiction that p ∨ q is true.
         There are two cases to handle.

         Case 1: Suppose p is true. This contradicts the assumption that p is false.
         Case 2: Suppose q is true. This contradicts the assumption that q is false.

         Therefore ¬(p ∨ q). QED.

  To formalize this proof, we first translate the pieces into the relevant commands.

    1. The assumption that p ∨ q is true is a proof term of the form
      λ (h_pq : p ∨ q) ↦ ...
    2. We split the assumption p ∨ q into two cases using the elimination rule
      Or.elim h_pq (Case 1) (Case 2)
        - Case 1 assumes p is true and arrives at a contradiction using the assumption that p is false.
          Hence this case corresponds to a proof term of the form
            λ (h_p : p) ↦ h_np p
        - Case 2 assumes q is true and arrives at a contradiction using the assumption that q is false.
          Hence this case corresponds to a proof term of the form
            λ (h_q : q) ↦ h_nq h_q
    3. Assemble the pieces into a single function.
-/

example (p q : Prop) (h_np: ¬p) (h_nq: ¬q) : ¬(p ∨ q) :=
  (λ (h_pq : p ∨ q) ↦                                   -- Assume p ∨ q.
    Or.elim h_pq                                        -- Break into cases
      (λ (h_p : p) ↦ h_np h_p)                          -- Case 1
      (λ (h_q : q) ↦ h_nq h_q))                         -- Case 2

/-
  Conjunction has similar rules for introduction and elimination.

  Conjunction is equipped with a single introduction rule, And.intro, that is used to
  construct a proof term of type p ∧ q from a proof term of type p and a proof term of type q.

  Conjunction is equipped with two elimination rules,
    · And.left that constructs a proof term of type p from a proof term of p ∧ q,
    · And.right that constructs a proof term of type q from a proof term of p ∧ q.

  To demonstrate their use, we show that conjunction behaves as expected:
    · If p and q are true, then p ∧ q is true.
    · If p is true and q is false, then p ∧ q is false.
    · If p is false and q is true, then p ∧ q is false.
    · if p is false and q is false, then p and q is false.
-/

/-
  The first is a simple application of the introduction rule:
-/
example (p q : Prop) (h_p : p) (h_q : q) : p ∧ q := And.intro h_p h_q

/-
  Note: Lean also provides an "anonymous constructor" that works in situations like this.
  Instead of writing And.intro h_p h_q, we could simply write ⟨h_p, h_q⟩ and Lean will (as if by magic...)
  infer from context that it should construct a proof term of type p ∧ q from h_p and h_q.
-/

example (p q : Prop) (h_p : p) (h_q : q) : p ∧ q := ⟨h_p,h_q⟩

/-
  The remaining facts must be proven by contradiction. In each case, we begin by assuming p ∧ q.
  For the first,

  Proof: Assume p ∧ q.  Then q must be true, but this contradics the assumption that q is false.
         Therefore ¬(p ∧ q). QED.
-/
example (p q : Prop) (h_p : p) (h_nq : ¬q) : ¬(p ∧ q) :=
  λ (h_pq : p ∧ q) ↦ h_nq h_pq.right

/-
  Proof: Assume p ∧ q. Then p must be true, but this contradicts the assumption that p is false.
         Therefore ¬(p ∧ q).  QED.
-/
example (p q : Prop) (h_np : ¬p) (h_q : q) : ¬(p ∧ q) :=
  λ (h_pq : p ∧ q) ↦ h_np h_pq.left

/-
  In the final case, we can prove ¬(p ∧ q) from either ¬p or ¬q. This means we could copy/pase paste
  the proof from the second or third example here.
-/
example (p q : Prop) (h_np : ¬p) (h_nq : ¬q) : ¬(p ∧ q) :=
  λ (h_pq : p ∧ q) ↦ h_nq h_pq.right

example (p q : Prop) (h_np : ¬p) (h_nq : ¬q) : ¬(p ∧ q) :=
  λ (h_pq : p ∧ q) ↦ h_np h_pq.left

/-
  Similar to conjunction, the biconditional comes equipped with a single introduction rule and two
  elimination rules.

  The introduction rule is Iff.intro, which constructs a proof term of type p ↔ q from a proof term of type
  p → q and a proof term of type q → p.  As such, the introduction rule generally has the form
    Iff.intro (Proof of p → q) (Proof of q → p).

  The two elimination rules are
    · Modus Ponens (MP): Iff.mp constructs a proof term of type p → q from a proof term of type p ↔ q.
    · Modus Ponens Reverse (MPR): Iff.mpr constructs a proof term of type q → p from a proof term of type p ↔ q.

  Recall that in traditional logic the biconditional plays the role of equality.  Namely, it expresses that
  two propositions have the same truth values.  As an example, we show that the biconditional behaves as we expect.
    · If p and q are both true, then p ↔ q is true.
    · If p is true and q is false, then p ↔ q is false.
    · If p is false and q is true, then p ↔ q is false.
    · If p and q are both false, then p ↔ q is true.
-/

/-
  These proofs are all a bit silly, so it helps to write the pieces explicitly.

  Proof: Assume p is true and q is true.

         1. If p is true, then q is true by assumption. (This is the MP)
         2. If q is true, then p is true by assumption. (This is MPR)

         Therefore p ↔ q. QED.

  Recall the If ..., then ... construct is a function, so this tells us the two arguments to Iff.intro.
    1. λ (h_mp : p) ↦ h_q
    2. λ (h_mpr : q) ↦ h_p
-/
example (p q : Prop) (h_p : p) (h_q : q) : p ↔ q :=
  Iff.intro
  (λ _ ↦ h_q) -- The hypothesis p is replace with the wildcard _ because it is not used.
  (λ _ ↦ h_p) -- Same for q.

/-
  Like conjunction, we can use the anonymous constructor to introduce Iff statements.
-/

example (p q : Prop) (h_p : p) (h_q : q) : p ↔ q :=
  ⟨(λ _ ↦ h_q), (λ _ ↦ h_p)⟩

/-
  Since we want to prove ¬(p ↔ q), the next two proofs are by contradiction, so this is where we'll need
  the elimination rules.  In both cases, we have h_pq : p ↔ q.

  For the first, the only way to derive a contradiction is to use h_nq : q → False. Since we have h_p : p, we
  obtain a proof term h_pq.mp h_p : q and then we obtain False from h_nq (h_pq.mp h_p).
-/
example (p q : Prop) (h_p : p) (h_nq : ¬q) : ¬(p ↔ q) :=
  λ (h_pq : p ↔ q) ↦ h_nq (h_pq.mp h_p)

/-
  The second is nearly identical; just use h_pq.mpr and swap the roles of p and q.
-/

example (p q : Prop) (h_np : ¬p) (h_q : q) : ¬(p ↔ q) :=
  λ (h_pq : p ↔ q) ↦ h_np (h_pq.mpr h_q)

/-
  For the final statement, note we are proving the two assertions
    · ¬p → (p → q), and
    · ¬q → (q → p).
  Each one of these is precisely the final case of implication we tackled.
  We use the exact same proof with appropriate adjustments.
-/

example (p q : Prop) (h_np : ¬p) (h_nq : ¬q) : p ↔ q :=
   Iff.intro
   (λ (h_p : p) ↦ False.elim (h_np h_p))
   (λ (h_q : q) ↦ False.elim (h_nq h_q))

/-
  As we build up to more elaborate proofs, we will start to see the λ constructions
  will quickly become unwieldy.  For example, let us consider the term proof for
  one of De Morgan's laws:

  Theorem: ¬(p ∨ q) is logically equivalent to ¬p ∧ ¬q.

  Proof: Assume ¬(p ∨ q).  To prove ¬p, suppose p for contradiction.  Then p ∨ q,
         contrary to the assumption ¬(p ∨ q).  Hence ¬p.
         Similarly, if we suppose q, then p ∨ q contradicts the assumption ¬(p ∨ q).
         Therefore ¬p ∧ ¬q.

         Conversely, assume ¬p ∧ ¬q.  Suppose for contradiction p ∨ q.
         This contradicts the assumption ¬p and ¬q.  Therefore ¬(p ∨ q).  QED.

  As above, we can judicioiusly translate this into a term proof by building it in stages.
  Since the proof term must be an If and Only If, we must use Iff.intro or ⟨_,_⟩ and build the two
  arguments MP and MPR.
    1.  The MP begins with the assumption ¬(p ∨ q), so we start from λ h_mp : ¬(p ∨ q) ↦ ... .
        To construct ¬p ∧ ¬q, we introduce a conjunction using And.intro or ⟨_,_⟩. The two sides
        have the form λ (h_p : p) ↦ ... and λ (h_q : q) ↦ ... .  In each case, we intend to arrive
        at a contradiction, so we must use introduce p ∨ q and then apply h_mp : p ∨ q → False.
        We introduce p ∨ q using Or.inl and the hypothesis (p or q), so the final branches will be:
          · λ (h_p : p) ↦ h_mp (Or.inl h_p)
          · λ (h_q : q) ↦ h_mp (Or.inl h_q)
    2.  The MPR begins with the assumption ¬p ∧ ¬q, so the initial proof term is
        λ (h_mpr : ¬p ∧ ¬q) ↦ ... . Next, we suppose p ∨ q and derive a contradiction by cases.
        The next term will have the form λ (h_pq : p ∨ q) ↦ ... .  We split the two cases using
        the elimination rule Or.elim.
          · Case p: We derive the contradiction by applying h_mpr.left : p → False to the
            assumption h_p : p.
          · Case q: We derive the contradiction by applying h_mpr.right : q → False to the
            assumption h_q : q.
    Putting all of this together results in the following seemingly inscrutible term proof.
-/

theorem not_or (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨(λ (h_mp : ¬(p ∨ q)) ↦
      ⟨λ (h_p : p) ↦ h_mp (Or.inl h_p),
      λ (h_q : q) ↦ h_mp (Or.inr h_q)⟩),
    (λ  (h_mpr : ¬p ∧ ¬q) (h_pq : p ∨ q) ↦
      Or.elim (h_pq)
        (λ (h_p : p) ↦ h_mpr.left h_p)
        (λ (h_q : q) ↦ h_mpr.right h_q))⟩

/-
  Using the names of the introduction rules may or may not make this marginally better:
-/
theorem not_or₂ (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (λ (h_mp : ¬(p ∨ q)) ↦
      And.intro
        (λ (h_p : p) ↦ h_mp (Or.inl h_p))
        (λ (h_q : q) ↦ h_mp (Or.inr h_q)))
    (λ (h_mpr : ¬p ∧ ¬ q) (h_pq : p ∨ q) ↦
      Or.elim (h_pq)
      (λ (h_p : p) ↦ h_mpr.left h_p)
      (λ (h_q : q) ↦ h_mpr.right h_q))

/-
  Fortunately, Lean provides some tools for us to improve readability.

  One such tool is the show ... from ... construct.  This helps the reader to better
  parse the goal that is being proven.
-/

theorem not_or₃ (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (λ (h_mp : ¬(p ∨ q)) ↦
        show ¬p ∧ ¬q from And.intro
          (λ (h_p : p) ↦ show False from h_mp (Or.inl h_p))
          (λ (h_q : q) ↦ show False from h_mp (Or.inr h_q)))
    (λ (h_mpr : ¬p ∧ ¬ q) (h_pq : p ∨ q) ↦
      show False from Or.elim (h_pq)
        (λ (h_p : p) ↦ show False from h_mpr.left h_p)
        (λ (h_q : q) ↦ show False from h_mpr.right h_q))


/-
  Another tool that can help improve readability is to define and prove subgoals.
  In longer proofs, this is common to help focus the reader's attention on a particular
  task.
-/

theorem not_or₄ (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (λ (h_mp : ¬(p ∨ q)) ↦
      have h_np : ¬p := λ (h_p : p) ↦ h_mp (Or.inl h_p)
      have h_nq : ¬q := λ (h_q : q) ↦ h_mp (Or.inr h_q)
      show ¬p ∧ ¬q from And.intro h_np h_nq)
    (λ (h_mpr : ¬p ∧ ¬q) (h_pq : p ∨ q) ↦
      have h_np : ¬p := h_mpr.left
      have h_nq : ¬q := h_mpr.right
      show False from Or.elim (h_pq)
        (λ (h_p : p) ↦ show False from h_np h_p)
        (λ (h_q : q) ↦ show False from h_nq h_q))

/-
  In longer proofs, it is quite common to reduce the proof to a particular statement.
  This frequently occurs as a courtesy to the reader, such as when the next
  step is seemingly unintuitive or unmotivated.

-/

-- associativity of ∧ and ∨
example (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (λ h_mp : (p ∧ q) ∧ r ↦
      have h_p : p := h_mp.left.left
      have h_q : q := h_mp.left.right
      have h_r : r := h_mp.right
      suffices h_qr : q ∧ r from ⟨h_p, h_qr⟩
      ⟨h_q,h_r⟩)
    (λ h_mpr : p ∧ q ∧ r ↦
      have h_p : p := h_mpr.left
      have h_q : q := h_mpr.right.left
      have h_r : r := h_mpr.right.right
      suffices h_pq : p ∧ q from ⟨h_pq,h_r⟩
      ⟨h_p,h_q⟩)

/-
  Classical Logic

  So far, the logic we have used does not assume that our propositions must be either
  true or false.  In order to utilize this type of reasoning, we need the Classical library.
  The assertion that p : Prop must be either true or false is an axiom called the
  Law of Excluded Middle.
-/

#check (Classical.em : (p : Prop) → p ∨ ¬p)

/-
  We can use the law of excluded middle to prove ¬¬p is logically equivalent to p.
  Note that ¬¬p : ¬p → False.
-/

theorem dne (p : Prop) : (¬¬p ↔ p) :=
  ⟨
    λ h_nnp : ¬¬p ↦ Or.elim (Classical.em p)
      (λ h_p : p ↦ h_p)
      (λ h_np : ¬p ↦
        False.elim (h_nnp h_np)),
    λ (h_p : p) (h_np : ¬p) ↦ h_np h_p
  ⟩

/-
  In fact, we can also show that dne implies em.  This tells us that double negation elimination
  is equivalent to the law of excluded middle.

  The proof isn't difficult, but does require some mental gymnastics.  We first observe that
  we can easily prove ¬¬(p ∨ ¬p).

  Proof: Assume ¬(p ∨ ¬p).

        For we prove ¬p.  Suppose p for contradiction.  Then p ∨ ¬p.  Contradiction.
        Hence ¬p and also p ∨ ¬p.  This is a contradiction.
        Therefore ¬¬(p ∨ ¬p).
-/

lemma em_lemma (p : Prop) : ¬¬(p ∨ ¬p) :=
  λ h : ¬(p ∨ ¬p) ↦
    have h_np : ¬p := λ h_p ↦ h (Or.inl h_p)
    h (Or.inr h_np)

/-
  Now we push everything through DNE.
-/
theorem em (p : Prop) : p ∨ ¬p := (dne (p ∨ ¬p)).mp (em_lemma p)

end Lecture_03
