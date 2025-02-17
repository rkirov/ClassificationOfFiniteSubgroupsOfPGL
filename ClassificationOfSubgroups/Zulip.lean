import Mathlib

def sum_of_first_n_odd_nat : ℕ → ℕ
| 0 => 0
| n + 1 => sum_of_first_n_odd_nat n + (2*n+1)


-- Ask AI if it can find the useful theorem
#leansearch "multiply out the square of sum?"

-- The following seems sensible
#check add_mul_self_eq

-- We check naturals are a commutative semiring
#synth CommSemiring ℕ

-- Naturals are indeed a commutative semiring

-- If you don't want to use AI then use loogle, a glorified maths search engine + regex(ish)
#loogle

theorem closed_eq_sum_of_first_n_odd_nat'' (n : ℕ) :
  sum_of_first_n_odd_nat n = n * n := by
    induction n
    case zero =>
      rw [sum_of_first_n_odd_nat]
    case succ k hk =>
      calc sum_of_first_n_odd_nat (k + 1) = k * k + (2*k +1) := by rw [sum_of_first_n_odd_nat, hk]
      _ = (k + 1) * (k + 1) := by sorry


theorem closed_eq_sum_of_first_n_odd_nat (n : ℕ) :
  sum_of_first_n_odd_nat n = n * n := by
  induction n
  -- Prove the base case.
  case zero =>
    rw [mul_zero, sum_of_first_n_odd_nat]
  -- Prove the induction step.
  case succ d hd =>
    calc sum_of_first_n_odd_nat (d + 1) = sum_of_first_n_odd_nat d + (2 * d + 1) := by rw [sum_of_first_n_odd_nat]
    _ = d * d + (2 * d + 1) := by rw [hd]
    _ = (d + 1) * (d + 1) := by sorry
    _ = (d + 1) * (d + 1) := by sorry

    -- rw [sum_of_first_n_odd_nat]
    -- -- Apply the induction hypothesis
    -- rw [hd]
    -- -- Multiply out the square of sum
    -- rw [add_mul_self_eq]
    -- -- We finish it off by hand
    -- rw [mul_one, mul_one, add_assoc]

theorem closed_eq_sum_of_first_n_odd_nat' (n : ℕ) : (sum_of_first_n_odd_nat n) = n * n := by
  induction n
  -- Prove the base case.
  case zero =>
    rw [Nat.mul_zero, sum_of_first_n_odd_nat]
  -- Prove the induction step.
  case succ d hd =>
    rw [sum_of_first_n_odd_nat]
    -- Apply the induction hypothesis
    rw [hd]
    -- Multiply out the square of sum
    rw [add_mul_self_eq]
    -- Now we ask lean to find the (semi)ring normal form of LHS and RHS  and compare them
    ring


#eval sum_of_first_n_odd_nat 0

#eval sum_of_first_n_odd_nat 1

#eval sum_of_first_n_odd_nat 2

#eval sum_of_first_n_odd_nat 3

#eval sum_of_first_n_odd_nat 4
