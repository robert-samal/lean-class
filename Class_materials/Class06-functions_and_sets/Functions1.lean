
/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib

open Real

/- ## Last time:
Expressions and types, every expression has a type
A proof has type given by what it's proved!
-/

-- ## Dependently typed
-- Lean is *dependently typed* (unlike C, Java, Haskell), which means that types can depend on
-- terms. Not every theorem proving language is dependently typed, but it's sometimes useful in
-- practice when formalising maths.
-- Take a look at the types of these two things:
-- `Fin` takes in a value, an element of the natural numbers, and *produces* a type.
-- (`Fin n` is the type whose elements are natural numbers less than `n`)
#check Fin 10
#check Fin

-- and here's a simple proof about the size of this (finite) type
example (n : ℕ) : Fintype.card (Fin n) = n := by simp

-- ## Simp -- what it does and when to avoid it
-- The `simp` tactic is Lean's simplifier. A bunch of lemmas throughout mathlib are tagged
-- `@[simp]`, meaning they're simplification lemmas, and so `simp` will try to use them to prove the
-- goal.
--> **about 30K of them in MathLib!!!**

-- But this means that running `simp` can sometimes be quite slow, or more concerningly,
-- if a new lemma gets added to mathlib and tagged `simp`, it could break an old `simp` proof.
-- As a consequence, for maintainability of Lean proofs, a *non-terminal* use of the `simp` tactic
-- is strongly discouraged. Non-terminal here means that it's a tactic call which isn't the one
-- closing the goal. A terminal simp is usually fine, since new simp lemmas usually can't break
-- these, but non-terminal `simp`s are frowned upon.
-- Fortunately, however, there's a nice way to fix them: changing `simp` to `simp?` gives a code
-- action telling you which lemmas `simp` actually used, and produces a call to `simp only` instead.
-- This is a restricted version of `simp` which simplifies in the same way, but *only* uses the
-- lemmas listed.
-- Here's an example:
example (n : ℕ) : Fintype.card (Fin n) = n := by simp?
-- Changing `simp` to `simp?` is sometimes called "squeezing" it, and it has a secondary use of
-- helping you figure out what `simp` actually did, or finding lemmas which are useful in your
-- situation.

-- ## Practicing with the `rw` tactic
-- Let's get some practice with the `rw` tactic for equalities now.

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these using rw.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

-- Don't forget you can use ← to rewrite in the reverse direction!
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

#check  sub_self

-- The lemma `sub_self` could be helpful
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section
-- Instead of having to declare my six real numbers each time, I can say `variables` which will
-- include them everywhere _below_ the declaration. And to avoid them going too far, I can constrain
-- that to a section.

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

-- The calc keyword allows writing more structured proofs which are easier to read, and sometimes
-- easier to write as well, despite being longer.
theorem Square : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

-- To appreciate, what the tactics `by`, `calc` and `rw` are doing for us, here is an
-- reduced form of the proof Square

#check Square
#print Square

-- For instance, you can start your proof by sketching the structure as follows, with the sorry
-- keyword in place of some subproofs.
-- (You don't need to fill these in, it's as above!)
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_add a b c
#check sub_self a
#check sub_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

-- The ring tactic can sometimes help a lot!
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  sorry

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  sorry

end

-- The nth_rw tactic allows you to be more precise about which occurrence of a subterm you want to
-- rewrite.
-- Usually this isn't necessary, but it's occasionally very helpful.
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
