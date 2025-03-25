import Mathlib
namespace Lecture_04

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

/-
  Another tool that can help improve readability is to define and prove subgoals.
  In longer proofs, this is common to help focus the reader's attention on a particular
  task.

  If you have a subgoal of type t, you can introduce the subgoal and its proof using the
  have keyword.
    have name : t :=
      <your proof goes here>
  The name you specify will appear in the Infoview.
-/

/-
  In longer proofs, it is quite common to reduce the proof to a particular statement.
  This frequently occurs as a courtesy to the reader, such as when the next
  step is seemingly unintuitive or unmotivated.

  This is achieved using the suffices keyword.  It has the form
    suffices <your sufficient condition goes here> from <your proof the condition is sufficient>
    <your proof of the sufficient condition>
-/

theorem not_or₃ (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    ( λ h_mp : ¬(p ∨ q) ↦ ⟨λ h_p : p ↦
      show False from
      suffices h_pq : p ∨ q from h_mp h_pq
      Or.inl h_p,
      λ h_q : q ↦
        show False from
        suffices h_pq : p ∨ q from h_mp h_pq
        Or.inr h_q⟩)
    (λ (h_mpr : ¬p ∧ ¬ q) (h_pq : p ∨ q) ↦
      show False from Or.elim (h_pq)
        (λ (h_p : p) ↦ show False from h_mpr.left h_p)
        (λ (h_q : q) ↦ show False from h_mpr.right h_q))

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
end Lecture_04
