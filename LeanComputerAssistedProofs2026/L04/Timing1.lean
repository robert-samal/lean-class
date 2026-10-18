import Mathlib.Util.CountHeartbeats
/-!
# Measurement of simp vs. guided simp.
-/

example (a b : Nat) : (0 + a) + (b + 0) = a + b := by
  #count_heartbeats! 20 in simp

example (a b : Nat) : (0 + a) + (b + 0) = a + b := by
  #count_heartbeats! 20 in simp only [Nat.zero_add, Nat.add_zero]
