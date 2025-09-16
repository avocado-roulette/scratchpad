import Mathlib.Data.Nat.Digits
import Mathlib.Tactic.NormNum
import Mathlib

example : 7 ∣ 63 := by norm_num
example : 7 ∣ 693 := by norm_num

-- Let's also compute the quotients to see the pattern
#eval 63 / 7  -- Should be 9
#eval 693 / 7 -- Should be 99
#eval 6993 / 7 -- Should be 999

-- Helper function to check if a number ends in 3
def ends_in_3 (n : ℕ) : Prop := n % 10 = 3

lemma ends_in_3_eq (n : ℕ) (h : ends_in_3 n) : n = (n / 10) * 10 + 3 := by
  unfold ends_in_3 at h
  grind

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

-- Main theorem: If a number in the 7 times table ends in a 3, then
-- inserting a 9 before the last digit gives another number in the 7 times table
theorem insert_9_preserves_7_times_table (n : ℕ)
  (h1 : 7 ∣ n)              -- n is in the 7 times table
  (h2 : ends_in_3 n) :      -- n ends in 3
  7 ∣ insert_9 n := by

  -- Proof outline: First we multiply by 10 to get a number that ends in 30
  -- then we add 63 to get a number that ends in 93.
  -- Both of these operations preserve the divisibility by 7, and the resulting
  -- number is exactly what insert_9 produces.

  let f (n: ℕ): ℕ := (n * 10) + 63

  -- now prove that insert_9 n = f n
  have h_insert_9_eq_f : insert_9 n = f n := by
    unfold insert_9
    unfold f
    simp
    rw [h2]
    simp_all only [Nat.add_left_inj, Nat.reduceEqDiff]
    rw [ends_in_3_eq n h2]
    grind

  have h_f_preserves_multiplicity_of_7 : ∀ m : ℕ, 7 ∣ m → 7 ∣ f m := by
    intro m h_m
    unfold f
    have h_10 : 7 ∣ (m * 10) := by
      exact dvd_mul_of_dvd_left h_m 10
    have h_63 : 7 ∣ 63 := by norm_num
    exact dvd_add h_10 h_63

  rw [h_insert_9_eq_f]
  exact h_f_preserves_multiplicity_of_7 n h1
