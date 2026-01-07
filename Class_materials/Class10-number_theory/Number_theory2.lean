/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib


-- added to make Bhavik's proof work
-- added to make Bhavik's proof work
namespace Section15sheet2

/-

# Find all integers x ≠ 3 such that x - 3 divides x³ - 3

This is the second question in Sierpinski's book "250 elementary problems
in number theory".

My solution: x - 3 divides x^3-27, and hence if it divides x^3-3
then it also divides the difference, which is 24. Conversely,
if x-3 divides 24 then because it divides x^3-27 it also divides x^3-3.
But getting Lean to find all the integers divisors of 24 is a bit harder!
-/

-- This isn't so hard
theorem lemma1 (x : ℤ) : x - 3 ∣ x ^ 3 - 3 ↔ x - 3 ∣ 24 := sorry

theorem int_dvd_iff (x : ℤ) (n : ℤ) (hn : n ≠ 0) : x ∣ n ↔ x.natAbs ∈ n.natAbs.divisors := by
  simp [hn]

#eval Nat.divisors 24
#check Nat.divisors 24

def divisors24 : Set ℤ := {-24, -12, -8, -6, -4, -3, -2, -1, 1, 2, 3, 4, 6, 8, 12, 24}

-- theorem dvd_24_iff (x : ℤ) : x ∣ 24 ↔ x ∈ divisors24 := by sorry

theorem dvd_24_iff (x : ℤ) : x ∣ 24 ↔ x ∈ divisors24 := by
  constructor
  · -- Forward: x ∣ 24 → x ∈ divisors24
    intro h
    rcases Int.eq_one_or_self_of_prime_of_dvd ... -- or use Int.divisors approach
  · -- Backward: x ∈ divisors24 → x ∣ 24
    intro h
    fin_cases h <;> decide  -- if divisors24 is a finite set

-- This seems much harder :-) (it's really a computer science question, not a maths question,
-- feel free to skip)
example (x : ℤ) :
    x - 3 ∣ x ^ 3 - 3 ↔
    x ∈ ({-21, -9, -5, -3, -1, 0, 1, 2, 4, 5, 6, 7, 9, 11, 15, 27} : Set ℤ) :=
  sorry


end Section15sheet2
