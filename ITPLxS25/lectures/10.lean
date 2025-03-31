namespace Lecture_10

section Constructing_Nat
/-
  The inductive types above serve merely to package data.  In those examples,
  the constructors depend only on types that have already been defined.
  However, Lean allows us to define inductive types with constructors that
  depend on the type being defined.

  A simple example is the construction of the natural numbers.  Set theoretically,
  the number zero is defined to be the empty set, and all other numbers are
  defined recursively via the successor function, which states that
    n + 1 = n ∪ {n}
  In practice, this means
    0 = ∅
    1 = {0} = {∅}
    2 = {0,1} = {∅, {∅}}
    3 = {0,1,2} = {∅, {∅}, {∅, {∅}}}
    ⋮
    n = {1,2,3,…,n-1}
    ⋮
  In lean, this recursion is simple
-/

namespace hidden

inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr -- Constructs objects into text.

/-
  The following chunk of code is just used to pretty print our numbers.
-/
def toNat : hidden.Nat → _root_.Nat
  | hidden.Nat.zero => 0
  | hidden.Nat.succ n => toNat n + 1

instance : Repr hidden.Nat where
  reprPrec n _ := (toString (toNat n))

#eval Nat.zero                                    -- 0
#eval Nat.succ Nat.zero                           -- 1
#eval Nat.succ (Nat.succ Nat.zero)                -- 2
#eval Nat.succ (Nat.succ (Nat.succ Nat.zero))     -- 3


/-
  Similar to the previous constructs, we have two elimination rules for
  our natural numbers depending on the form
    · n is zero
    · n is the successor of something non-zero (i.e. n-1).
  The same match … with construct can be used to define basic functions
  on our type recursively.
-/
namespace Nat
/-
  For a binary operation on Nat, such as addition, we will need to
  make a choice as to which slot we want to use for our recursion.
  We arbitrarily make the choice to the take the left.

  In practice, this means we start by defining
    0 + n = n.
  Then we can define
    · 1 + n as the successor of 0 + n = n,
    · 2 + n as the successor of 1 + n,
    · 3 + n as the successor of 2 + n,
    ⋮
    · m + n as the successor of (m-1) + n
-/
def add (m n : Nat) : Nat :=
match m with
| zero => n
| succ m => Nat.succ (add m n)

/-
  We can register the usual addition symbol using infixl to
  indicate that our + is left associative.
-/
infixl:65 "+" => add

#eval Nat.zero + (succ Nat.zero)                   -- 0 + 1 = 1
#eval add Nat.zero (succ Nat.zero)                 -- 0 + 1 = 1

#eval  (succ Nat.zero) + (succ (succ Nat.zero))    -- 1 + 2 = 3
#eval add (succ Nat.zero) (succ (succ Nat.zero))   -- 1 + 2 = 3

/-
  Lean is able to infer facts about addition automatically, so long as
  they are stated relative to the left slot.
-/

/-- For all `n : Nat`, `0 + n = n`-/
theorem zero_add (n : Nat) : add Nat.zero n = n := rfl
/-- For all `m n : Nat`, `(m + 1) + n = (m + n) + 1`-/
theorem succ_add (m n : Nat) : add (succ m) n = succ (add m n) := rfl

/-
  However, it cannot infer that m + 0 = m automatically.  In order to accomplish
  this task, we will need to use the principle of induction.
-/

/-- For all `m : Nat`, `m + 0 = m`.-/
theorem add_zero (m : Nat) : add m Nat.zero = m := by
  induction m with
  | zero => rfl       -- Base case m = 0: 0 + 0 = 0 := rfl
  | succ m ih =>      -- Assume m + 0 = m.  Prove (m + 1) + 0 = m + 1.
    rw [add,ih]

/-
  This proof is essentially the observation that,
    (m + 1) + 0 := add (succ m) + Nat.zero
                 = succ (add m Nat.zero)      (by definition of add)
                 = succ m                     (by the induction hypothesis)
-/

/-
  Exercise: Complete the following proofs using induction (on m).
-/

/-- For all `m n : Nat`, `m + (n + 1) = (m + n) + 1`-/
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := sorry

/--For all `m, n : Nat`, `(m + n) + k = m + (n + k)` -/
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := sorry

/-- For all `m,n : Nat`, `m + n = n + m` -/
theorem add_comm (m n : Nat) : add m n = add n m := sorry

end Nat
end hidden
end Constructing_Nat



end Lecture_10
