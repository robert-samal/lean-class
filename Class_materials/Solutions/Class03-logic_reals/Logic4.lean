/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro h
  cases h with
  | intro left right => exact left
  done

-- alternative syntax 1
example : P ∧ Q → P := by
  intro h
  cases h
  case intro left right => exact left
  done

-- alternative syntax 2
example : P ∧ Q → P := by
  intro h
  cases' h with left right
  exact left
  done



example : P ∧ Q → Q := by
  intro h
  cases' h with left right
  exact right
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro hPQR hPQ
  cases' hPQ with hP hQ
  apply hPQR
  . exact hP
  . exact hQ
  done

-- or shorter (and less easy to understand?)
example : (P → Q → R) → P ∧ Q → R := by
  rintro hPQR ⟨hP, hQ⟩
  exact hPQR hP hQ
  done


example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor <;> assumption
  -- · assumption
  -- · assumption
  done


/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  sorry -- homework
  done

example : P → P ∧ True := by
  intro h
  constructor
  . exact h
  . trivial
  done

example : False → P ∧ False := by
  intro h
  contradiction
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  cases' h1 with hP hQ
  cases' h2 with _ hR
  trivial
  done

example : (P ∧ Q → R) → P → Q → R := by
  sorry -- homework
  done
