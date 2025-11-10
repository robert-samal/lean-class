/-
Copyright (c) 2025 Robert Šámal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Šámal.
Based on work by Bhavik Mehta.
-/

-- In this sheet we avoid Mathlib
-- Thus we have to write Nat instead of ℕ
-- also, you may get a weird error about "unknown configuration option 'linter.style.longLine'"
-- in such case, make sure you have update the file lakefile.toml


/-!  # Several ways to define a function
  We can use Lean as a normal functional language.
  The following are equivalent ways to define a square function from Nat to Nat:
  (Internally, Lean translate all to the form "square2", as you may see using
  the #print command)
-/

def square1 (x : Nat) : Nat := x*x
def square2 : Nat → Nat := fun x => x*x
def square3 : Nat → Nat := λ x ↦ x*x
def square4 := fun x : Nat => x*x

#check square1
#check square2
#check square3
#check square4

#print square1
#print square2
#print square3
#print square4

/-!  # Currying
  We can define higher-order functions (that is, functions with several
  arguments).  Internally, they are represented as functions of one parameter,
  that return another function of one parameter
-/

def my_add (x y : Nat) : Nat := x + y
def my_add1 (x : Nat) (y : Nat) : Nat := x + y
def my_add2 : Nat → (Nat → Nat) := fun x : Nat => (fun y : Nat => x+y)
def my_add2a : Nat → Nat → Nat := fun x => (fun y => x+y)
def my_add2b := fun x : Nat => (fun y : Nat => x+y)

def my_add_one := my_add 1

-- not that "the arrows associate to the right"

#check my_add
#check my_add
#check my_add2a
#check my_add2b
#check my_add_one

#print my_add
#print my_add2
#print my_add_one

#eval my_add 1 3
-- function application "associates to the left", so the above and below are the same:
#eval (my_add 1) 3
-- and they are the same as the following, due to def of my_add_one, "partial evaluation"
#eval my_add_one 3

/-! # More syntactic sugar to define functions on Nat
  Here we use the definition of Nat (that we haven't seen yet):
  Every number in Nat is either 0 or n+1 for some n in Nat.
-/
def myFactorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * myFactorial n

-- another, more explicit, syntax for the same
def myFactorial1b (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * myFactorial n


-- Here is a more "normal looking" definition.
def myFactorial2 (n : Nat) : Nat :=
  if n = 0 then 1 else n*myFactorial2 (n-1)

#print myFactorial

#check myFactorial
#check myFactorial2

-- Lean can compute too!
#eval myFactorial 10
#eval myFactorial1b 10
#eval myFactorial2 10
-- This is useful for sanity-checking definitions.
-- Lean can compile (via C++), so it can be fast.

/--
Next, we will prove that both definitions do the same.
Again, using that every n in Nat is either 0 or something plus 1.
  ## The first proof
  uses the "syntactic sugar": `by induction` tactics
-/

theorem same_factorials (n : Nat) : myFactorial n = myFactorial2 n := by
  induction n
  case zero =>
    rw [ myFactorial, myFactorial2]
    rfl
  case succ n ih =>
    rw [myFactorial, myFactorial2]
    simp
    rw [← ih]


/- ## Second and third proofs of the factorial equality
  They differ only in the syntax that exactly mimics the syntax of the recursive definition
  of the factorials themselves. To reinforce the idea, that theorems are
  special kinds of functions, that produce proofs (in this case they are recursive functions).
-/

theorem same_factorials2 : ∀ n : Nat, myFactorial n = myFactorial2 n
  | 0 => by rw [myFactorial, myFactorial2]; rfl
  | n + 1 => by rw [myFactorial, myFactorial2]; simp; rw [same_factorials2 n]

theorem same_factorials3 (n : Nat) : myFactorial n = myFactorial2 n :=
  match n with
  | 0 => by rw [myFactorial, myFactorial2]; rfl
  | n + 1 => by rw [myFactorial, myFactorial2]; simp; rw [same_factorials3 n]

-- Cool thing is we use the same language to define the function
-- that computes factorial and to prove stuff about the implementation.


def isEven : Nat -> Bool
  | 0   => true
  | n+1 => not (isEven n)

#eval isEven 4
#eval isEven 5

example  (n : Nat) : isEven (n*(n+1)) := sorry

-- Try inductive definition for Fibonacci numbers
-- (defined as $F_0 = 0, F_1 = 1, F_{n+2} = F_n + F_{n+1}$ )
-- (there are several ways, don't worry about efficiency for now)
def Fibonacci : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => Fibonacci n + Fibonacci (n+1)

#eval Fibonacci 6

/-! # Function composition
-/

#check Fibonacci
#check Fibonacci (myFactorial 2)
#check Fibonacci ∘ myFactorial

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (x : X) : Z := g (f x)
-- here the paranthesis is important!
-- `g f x` means `(g f) x`

/-!
  Later we will return to functions to prove things about
  injective/bijective functions, etc.
  But first, we will proceed with learning about connection
  between functions and proofs.
-/
