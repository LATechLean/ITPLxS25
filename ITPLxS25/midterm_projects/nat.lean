namespace hidden

inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr -- Constructs objects into text.

section IgnoreMe
/-
  The following chunk of code is just used to pretty print our numbers.
-/
def toNat : hidden.Nat → _root_.Nat
  | hidden.Nat.zero => 0
  | hidden.Nat.succ n => toNat n + 1

instance : Repr hidden.Nat where
  reprPrec n _ := (toString (toNat n))

end IgnoreMe

namespace Nat

/-- Addition of natural numbers. -/
def add (m n : Nat) : Nat :=
match m with
| zero => n
| succ m => Nat.succ (add m n)

section IgnoreMe
infixl:65 "+" => add
end IgnoreMe


/-- For all `n : Nat`, `0 + n = n`-/
theorem zero_add (n : Nat) : Nat.zero + n = n := rfl
/-- For all `m n : Nat`, `(m + 1) + n = (m + n) + 1`-/
theorem succ_add (m n : Nat) : (succ m) + n = succ (m + n) := rfl

/-- For all `m : Nat`, `m + 0 = m`.-/
theorem add_zero (m : Nat) : m + Nat.zero = m := by
  induction m with
  | zero => rfl       -- Base case m = 0: 0 + 0 = 0 := rfl
  | succ m ih =>      -- Assume m + 0 = m.  Prove (m + 1) + 0 = m + 1.
    rw [add,ih]

/-- For all `m n : Nat`, `m + (n + 1) = (m + n) + 1`-/
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc (succ m) + (succ n) = succ (m + succ n) := by rw[add]
    _= succ ((succ (m + n))) := by rw[ih]
    _= succ ((succ m) + n) := by rw[add]


/--For all `m, n : Nat`, `(m + n) + k = m + (n + k)` -/
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction m with
  | zero => repeat rw[zero_add]
  | succ m ih =>
    calc (succ m) + n + k = (succ (m + n)) + k := by rw[add]
    _= succ ((m + n) + k) := by rw[add]
    _= succ (m + (n + k)) := by rw[ih]
    _= (succ m) + (n + k) := by rw[add]

/-- For all `m,n : Nat`, `m + n = n + m` -/
theorem add_comm (m n : Nat) : m + n = n + m := by
  induction m with
  | zero => rw[add_zero,zero_add]
  | succ m ih =>
    calc (succ m) + n = succ (m + n) := by rw[add]
    _= succ (n + m) := by rw[ih]
    _= n + (succ m) := by rw[add_succ]

def one := succ zero
def two := succ one

/-- Multiplication of natural numbers.-/
def mul (m n : Nat) : Nat := sorry

section IgnoreMe
infixl:70 "*" => mul
end IgnoreMe

/-- For all `n : Nat`, `zero * n = zero`-/
theorem zero_mul (n: Nat) : zero * n = zero := sorry

/-- For all `m : Nat`, `m * zero = zero`-/
theorem mul_zero (m : Nat) : m * zero = zero := sorry

/-- For all `n : Nat`, `one * n = n` -/
theorem one_mul (n : Nat) : one * n = n := sorry

/-- For all `m : Nat`, `m*one = m` -/
theorem mul_one (m : Nat) : m * one = m := sorry

/-- For all `n : Nat`, `two*n = n + n`-/
theorem two_mul (n : Nat) : two * n = n + n := sorry

/-- For all `m : Nat`, `m*two = m + m`-/
theorem mul_two (m : Nat) : m * two = m + m := sorry

/-- For all `m n : ℕ`, `(m+1) * n = n + m * n`-/
theorem succ_mul (m n : Nat) : (succ m) * n = n + (m * n) := sorry

/-- For all `m n : ℕ`, `m*(n+1) = m + m*n`-/
theorem mul_succ (m n : Nat) : m * (succ n) = m + m*n := sorry

/-- For all `m n : ℕ`, `m*n = n*m`-/
theorem mul_comm (m n : Nat) : m * n = n * m := sorry

/-- For all `m n k : Nat`, `(m + n) * k = m * k + n * k`-/
theorem distrib_right (m n k : Nat) : (m + n) * k = m*k + n*k := sorry

/-- For all `m n k : ℕ`, `m*(n+k) = m*n + m*k`-/
theorem distrib_left (m n k : Nat) : m * (n + k) = m * n + m * k := sorry

/-- For all `m n k : ℕ`, `(m*n) *k = m * (n * k)`-/
theorem mul_assoc (m n k : Nat) : (m * n) * k = m * (n * k) := sorry

end Nat
end hidden
