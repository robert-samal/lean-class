set_option trace.profiler true
set_option trace.profiler.threshold 0

example (a b : Nat) : (0 + a) + (b + 0) = a + b := by
  simp

example (a b : Nat) : (0 + a) + (b + 0) = a + b := by
  simp only [Nat.zero_add, Nat.add_zero]
