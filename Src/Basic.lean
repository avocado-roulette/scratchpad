import Mathlib.Tactic
import Mathlib.Util.Delaborators

set_option warningAsError false

example (a b c : ℝ) : a * b * c = b * (a * c) := by
 rw [mul_comm a b]
 rw [mul_assoc b a c]
