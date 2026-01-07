/-
Copyright (c) 2025 Robert Šámal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Šámal
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-
# Three ways to compute Fibonacci numbers

## 1. First, by the definition.
As you know, this straighforward recursion blows.
(time complexity to compute $F_n$ is $Ω(F_n) ≐ 1.6^n$)
-/

def fib1 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib1 n  + fib1 (n+1)

-- NOT  | n => fib1 (n - 1) + fib1 (n-2)

#eval fib1 0   -- 0
#eval fib1 1   -- 1
#eval fib1 10  -- 55

local notation:100 "F_" n:1000 => Nat.fib n

#eval F_ 5


/-

## 2. Second, a Tail-recursive helper with an accumulator
Basically, we always remember two consecutive values.
It's only a bit tricky to do it in a functional programming language.
Anyway, time complexity is $O(n)$.

-/

def fibAux : Nat → Nat → Nat → Nat
  | 0, a, b => a
  | n+1, a, b => fibAux n b (a + b)

def fib2 (n : Nat) : Nat :=
  fibAux n 0 1

#eval fib2 0   -- 0
#eval fib2 1   -- 1
#eval fib2 10  -- 55
-- #eval fib2 50-- 12586269025

/-
## Library implementation
Same thing is implemented in the library in a more cool/cryptic way:

-/

#print Nat.fib
#eval Nat.fib 10

-- To understand it, let's look at function interation in Lean:

def f : ℕ → ℕ := fun n => n + 1

#eval f 5
#eval f^[3] 5

/- Btw, this is eachieved by
`notation f "^[ " n " ]" => Function.iterate f n`
in the library
-/

def f2 : ℕ → ℕ := fun n => f^[n] n

#eval f2 5

-- How do we continue this pattern to define power of 2
-- (in a different way then 2^n)
-- secretly, 2^n is defined in this way (?)
-- you may want to continue to much larger functions ([Ackermann function](https://en.wikipedia.org/wiki/Ackermann_function) )

def f3 : ℕ → ℕ := sorry
-- #eval f3 5 should give 32

example (n : ℕ) : f3 n = 2^n := sorry


/-
  In mathlib there are results showing that Nat.fib does what it should:
  The cool thing about Lean, is that we can implement functions AND
  prove their properties in the same language.
-/

example {n : ℕ}: Nat.fib (n+2) = Nat.fib (n) + Nat.fib (n+1) := by
  exact Nat.fib_add_two

example {n : ℕ}: F_ 0 = 0 := by
  rfl

example {n : ℕ}: F_ 1 = 1 := by
  simp

/-
  In the next proof, observe
   - use of `refine` tactics -- it create new goals for the "holes"
   - The "twoStepInduction" is a special theorem, the general "pattern matching"
     fails here (unlike the definition of `fib1`)
-/
theorem fib_is_ok : ∀ n : ℕ, Nat.fib n = fib1 n := by
  refine Nat.twoStepInduction ?h0 ?h1 ?hs
  . -- goal ?h0
    rfl
  . -- goal ?h1
    simp [fib1]
  . -- goal ?hs
    intro n hn hn1
    unfold fib1
    rw [← hn]
    rw [← hn1]
    exact Nat.fib_add_two

/-
## 3. Finally, a version using math property of Fib.numbers
$F_{2k} ​= F_k​^2(F_{k+1}​−F_k​)$
$F_{2k+1} ​=F_{k+1}^2​+F_k^2​$

Time complexity $O(\log n)$

It also exists in mathlib, as `Nat.fastFib`
-/

def fib3 (n : Nat) : Nat :=
  let rec aux (k : Nat) : Nat × Nat :=
    if k = 0 then (0, 1)
    else
      let (a, b) := aux (k / 2) -- a = F_m, b = F_{m+1} where m = k/2
      let c := a * (2 * b - a)
      let d := a * a + b * b
      if k % 2 = 0 then (c, d) else (d, c + d)
  (aux n).1

#check Nat.binaryRec
#eval fib3 2
#eval fib3 10

#print Nat.fastFib
#print Nat.fastFibAux

-- #eval Nat.fib  450000
-- #eval Nat.fastFib 900000
