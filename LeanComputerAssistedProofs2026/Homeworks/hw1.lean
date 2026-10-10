/-
Homework 1, Lean -- Computer-assisted proofs, class 2026
Author: Robert Šámal
-/
module
public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
/-!
# HW1

Do not use `tauto`, `grind` nor any other automatic means.
The goal here is to understand the basics.

-/

variable (P Q R S T : Prop)

/-- 1. Easy: don't be afraid of the double negation ...
    just recall `¬Q` means `Q → False`
-/
example : P → ¬¬P := by
  sorry

/-- 2. Easy: Construct a conjunction using `constructor`. -/
example : P → Q → P ∧ Q := by
  sorry

/-- 3. Looks more complicated than it is.
Combine `intro` and `rcases`. -/
example : (P → Q ∨ R) → (Q → S) → (R → T) → P → S ∨ T := by
  sorry

/-- 4. Peirce's law -- only true in classical logic.
In other words, you have to uses `by_cases` -/
example : ((P → Q) → P) → P := by
  sorry

/-- 5. Distributivity of conjunction over disjunction.
  Needs rcases twice. -/
example : (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R) := by
  sorry
