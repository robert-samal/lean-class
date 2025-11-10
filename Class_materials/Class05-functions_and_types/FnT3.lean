/- -/

import Mathlib.Tactic


/-!
# Why bother with types
-/
#check 1+2
#check Nat
#check Type
#check Type 1
#check Prop
#check Sort 0

/-!
So every expression has a type. Even types have a type.
But **No type has itself as a type**.
This will not affect us, but prevents variants of Russell's (Girard's) paradox
(set of all sets that do not contain itself).


So what is a type in Lean?
Just like a group is a set defining the group axioms, the type theory of Lean is a collection
which satisfies the axioms of LeanTT. But these are pretty complex and abstract to write down
so we'll just stick with our model of, a type is just a set, but they're all disjoint.
But now we have the deeper fact that while this is fair in Lean, it's not quite right in MLTT.

Let's now talk about the types of Lean
function types, subtypes, Pi types, inductive types, (maybe quotient types?)

## Function types

--/

universe u

variable {α β : Type u}

#check α → β

-- Construction:
#check fun a : α => (sorry : β)
-- Destruction:
example (f : α → β) (x : α) : β := f x

-- Computation:
example (f : α → β) (x : α) : (fun y ↦ f y) x = f x := rfl

-- ## Subtypes

#check { i : Nat // i < 10 }

lemma zero_is_small : 0 < 10 := by norm_num

def small_num : { i : Nat // i < 10 } := ⟨ 0, zero_is_small ⟩

-- ## Dependent types

#check Nat → Nat
#check (n : Nat) → {i : Nat // i ≤ n}

def pick (n : Nat) : {i : Nat // i ≤ n} :=
  ⟨ 0, by norm_num ⟩
-- equivalently:
-- Subtype.mk 0 (by norm_num)

example : Type := Π n : ℕ, {i : ℕ // i ≤ n}
#check  pick 10

-- ## Pi (product) types
variable (Y : ℕ → Set ℕ)
-- Y 0 : Set ℕ
-- Y 1 : Set ℕ
-- Y 2 : Set ℕ
-- ...
-- We can then make a new type, whose elements are functions from the natural numbers to
-- ⋃ i : ℕ, Y i
-- i : ℕ, output of the function should be in Y i
-- A generalised function which takes in `i : I`, and returns a term of type `Y i`.
example : Type := Π i : ℕ, Y i
example : Type := (i : ℕ) → Y i

-- Try to define a function, that has the above type!
-- (Why it may not be possible?)


example : ∀ n : ℕ, n + n = 2 * n := by
  intro n
  ring

theorem trivi : (n : ℕ) → n + n = 2 * n := by
  sorry

-- We will see such proves later, for now just observe:
-- trivi 0 has type `0+0 = 2*0`
-- trivi 1 has type `1+1 = 2*1`

/-! ## Inductive types
Not only function definitions, but the types themselves can be inductive.
The following mimics definitions of `Nat`, `True`, `False`, `And`, `Or`
-/


inductive Nat' : Type where
  | zero : Nat'
  | succ (n : Nat') : Nat'

#print Nat
#print Nat'

inductive True' : Prop where
  | intro : True'

#print True'

inductive False' : Prop where

#print False'
-- this is not a typo: the definition end by the first line
-- so there is not object of type False'
-- On the other hand, we can define an object of type True':

def trivial' : True' := True'.intro

--- False implies anything
example (q : Prop) : False' → q := by
  intro h
  cases h

#print And
#print Prod

inductive And' (P Q : Prop) : Prop where
  | intro (hp : P) (hq : Q) : And' P Q

structure And'' (P Q : Prop) : Prop where
  left : P
  right : Q

#print Prod

#check And
#print And
#print And''
#print And'

example : And'' (1=1) (2=2) := ⟨ rfl, rfl ⟩


inductive Or' (P Q : Prop) : Prop where
  | inl (hp : P) : Or' P Q
  | inr (hq : Q) : Or' P Q


#print Or'

#check Sort 0
#check Type 0
