import Mathlib.Data.Nat.Digits
import Mathlib.Tactic.NormNum

example : 7 ∣ 63 := by norm_num
example : 7 ∣ 693 := by norm_num

-- Let's also compute the quotients to see the pattern
#eval 63 / 7  -- Should be 9
#eval 693 / 7 -- Should be 99
#eval 6993 / 7 -- Should be 999

-- Helper function to check if a number ends in 3
def ends_in_3 (n : ℕ) : Prop := n % 10 = 3

example : ends_in_3 63 := by
  unfold ends_in_3
  norm_num

-- Helper function to insert 9 before the last digit of a number
def insert_9 (n: ℕ): ℕ :=
  let units := n % 10
  let tens_and_above := n / 10
  tens_and_above * 100 + 90 + units

#eval insert_9 1234 -- Should be 12394

example: insert_9 1234 = 12394 := by
  unfold insert_9
  norm_num

-- Main theorem: If a number in the 7 times table ends no a 3, then
-- inserting a 9 before the last digit gives another number in the 7 times table
theorem insert_9_preserves_7_times_table (n : ℕ)
  (h1 : 7 ∣ n)              -- n is in the 7 times table
  (h2 : ends_in_3 n) :      -- n ends in 3
  7 ∣ insert_9 n := by

  -- Proof outline: First we multiply by 10 to get a number that ends in 30
  -- then we add 63 to get a number that ends in 93.
  -- Both of these operations preserve the divisibility by 7, and the resulting
  -- number is exactly what insert_9 produces.

  let ten_n := n * 10

  have h_10 : 7 ∣ ten_n := by
    exact dvd_mul_of_dvd_left h1 10

  have h_63 : (7 : ℕ) ∣ (63 : ℕ) := by
    norm_num

  let ten_n_plus_63 := ten_n + 63

  have h_ten_n_plus_63 : 7 ∣ ten_n_plus_63 := by
    unfold ten_n_plus_63  -- this line is optional, but it helps clarify the proof step
    exact dvd_add h_10 h_63

  have h_insert_9 : insert_9 n = ten_n_plus_63 := by
    unfold insert_9
    simp
    rw [h2]
    unfold ten_n_plus_63
    unfold ten_n
    simp

    have div_mod : n = n / 10 + 3 := by
      rw [←Nat.div_add_mod n 10]
      sorry

    sorry

  rw [h_insert_9]
  exact h_ten_n_plus_63
