-- Here I import the maths library
import Mathlib

-- Here I make accessible the nice syntax for Σ-summation, etc.
open BigOperators Finset

set_option linter.unusedTactic false

section Programming

def sum_of_first_n_odd_nat : ℕ → ℕ
 | n => ∑ k ∈ range n, (2 * k + 1)

#eval sum_of_first_n_odd_nat 1

#eval sum_of_first_n_odd_nat 2

#eval sum_of_first_n_odd_nat 3

#eval sum_of_first_n_odd_nat 4

#eval sum_of_first_n_odd_nat 10

#eval sum_of_first_n_odd_nat 20

#eval sum_of_first_n_odd_nat 33



end Programming

section Proof

section AIHelp

-- #leansearch "binomial expansion of a square of a sum."

-- The first option seems promising! Looks a bit strange though
#check add_pow_two

-- Is the set of Natural numbers a commutative semiring?
#synth CommSemiring ℕ
-- Ah it seems it is :)

#check Nat.instCommSemiring

end AIHelp

theorem sum_of_odd_eq_sq' : ∀ n, sum_of_first_n_odd_nat n = n^2 := by sorry

theorem sum_of_odd_eq_sq : ∀ n, ∑ k ∈ range n, (2 * k + 1) = n^2 := by
  intro n
  induction n
  -- Prove the base case.
  case zero =>
    rewrite [range_zero, sum_empty, sq, mul_zero]
    rfl
  -- Prove the induction step.
  case succ m induction_hypothesis =>
    #check induction_hypothesis
    calc
    ∑ k ∈ range (m + 1), (2 * k + 1) = ∑ k ∈ range m, (2 * k + 1) + (2 * m + 1) := by
      rewrite [sum_range_add, range_one, sum_singleton, add_zero]
      rfl
    _ = m^2 + (2 * m + 1) := by
      -- Apply the induction hypothesis.
      rewrite [induction_hypothesis]
      rfl
    _ = (m + 1)^2 := by
      -- rw [add_pow_two, mul_one, one_pow, add_assoc]
      -- -- Natural numbers are a commutative semi-ring,
      -- Lean please find the (semi-ring) normal form for the LHS and the RHS.
      ring

#check sum_of_odd_eq_sq

end Proof
