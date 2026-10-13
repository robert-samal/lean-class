/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `True` and `False`

-/

variable (P Q R S : Prop)


/- New tactic `exfalso` -/
example : False → P := by
  intro h
  exfalso -- instead of showing `P`, we will show a contradiction
  exact h

example : P ∧ Q → P := by
  intro h
  rcases h with ⟨left, right⟩
  exact left
/--
The pattern `intro h` then `rcases h with ...` is so common that it has an abbreviation as
`rintro ...`, so you could also do
-/
example : P ∧ Q → P := by
  rintro ⟨left, right⟩
  exact left

-- or you can get the relevant part out directly using `.left`
example : P ∧ Q → P := by
  intro h
  exact h.left

-- or by using `.1` (the first part)
example : P ∧ Q → P := by
  intro h
  exact h.1

-- this will make more sense later, when we see that `And` is actually a defined concept

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  -- After the `constructor` tactic, we have *2 goals*
  -- We can solve them one by one:
  · assumption -- cheating ... we don't need `exact hP`
  · assumption

-- If the exact same tactic works to finish both goals, these can be combined:
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  all_goals assumption

-- or even more succintly:
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor <;> assumption


/-!

# Logic in Lean: "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`
* `change`

-/


example : P ↔ P := by
  sorry


example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  constructor -- We can construct a proof of `↔` by `constructor`, similar to `∧`
  · exact h.mpr  -- "modus ponens reverse"
  · exact h.mp   -- "modus ponens"

-- Note, that `rw` tries a weak version of `rfl` when it’s finished.
-- If you insist to know what this means, see at the end of this file
example : (P ↔ Q) → (Q ↔ P) := by
  sorry



-- We may use it twice in a row
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  all_goals (intro h; rw[h])

-- But, this is a well-known property of equivalence `↔`
-- so, there are many ways to solve it, starting from "cheating" by automatic prover
example : (P ↔ Q) ↔ (Q ↔ P) := by
  tauto

-- another form of cheating, how do we know the library name?
example : (P ↔ Q) ↔ (Q ↔ P) := by
  exact iff_comm

example : (P ↔ Q) ↔ (Q ↔ P) := by
  exact?


-- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`
-- try it here
-- you may also want to use `rw[h1,h2]` -- it applies these in order
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  sorry

/-!

# Logic in Lean: "and" (`∧`)

We learn about how to manipulate a conjuction `P ∧ Q` in Lean.

-/




example : P ∧ Q ↔ Q ∧ P := by
  exact And.comm

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  all_goals (intro h; exact ⟨h.2, h.1⟩ )


example : P ∧ Q ↔ Q ∧ P := by
  constructor
  all_goals
  rintro ⟨ hP, hQ ⟩
  constructor <;> assumption

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · rintro ⟨ ⟨ hP, hQ⟩, hR ⟩
    exact ⟨ hP, ⟨ hQ, hR ⟩ ⟩
  · rintro ⟨ hP, ⟨ hQ, hR ⟩ ⟩
    exact ⟨ ⟨ hP, hQ⟩, hR ⟩


example : P ↔ P ∧ True := by
  constructor
  · intro h
    constructor
    · exact h
    · trivial
  · intro h
    exact h.1

example : False ↔ P ∧ False := by
  constructor
  · intro h; exfalso; exact h
  · intro h; exact h.2

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2
  rw [h1,h2]

example : ¬(P ↔ ¬P) := by
  intro h
  by_cases hP : P
  · have hnP : ¬P := h.mp hP
    contradiction
  · have h2 : P := h.mpr hP
    contradiction

/-!

# Logic in Lean: "or" (`∨`)

We learn about how to manipulate a disjunction `P ∨ Q` in Lean.


* `left`, `right`

-/



example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  sorry

-- Here are a few ways to break down a disjunction
-- we saw this already:
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  rcases hPoQ with h | h
  · intro h1 h2; apply h1; exact h
  · intro h1 h2; apply h2; exact h

-- another syntax for the same
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  obtain h | h := hPoQ
  · sorry
  · sorry

-- shortcut for the first one
example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (h | h)
  · sorry
  · sorry

-- this one will not make much sense now ...
-- it is a preparation of visual memory for handling recursive definitions
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  cases hPoQ with
  | inl h => sorry
  | inr h => sorry

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  sorry

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  sorry

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  sorry

example : (P → Q) → P ∨ R → Q ∨ R := by
  sorry

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  sorry

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry



/-
# rw works up to syntactic equality!

TODO: explain various equalities
-/


/-

# BONUS (ignore if you are scared ;-)  )
`rw` tries a weak version of `rfl` when it’s finished.

Explicitly: it tests "definitional equality" -- equivalence/equality up to definitions,
BUT only definitions marked by `@[reducible]`.

-/

def my_one : Nat := 1

-- Here we need both of the lines in the proof (try commenting out one or the other)
example (x : Nat) (h : x = 1) : x = my_one := by
  rw [h]
  rfl


@[reducible]
def my_oneB : Nat := 1

-- This proof works
example (x : Nat) (h : x = 1) : x = my_oneB := by
  rw [h]
