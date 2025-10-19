/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  constructor
  . intro h
    exact h
  . intro h
    exact h
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;>
  . intro h
    rw [h]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rwa [h1]
  done

example : P ∧ Q ↔ Q ∧ P := by
  sorry -- homework
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  sorry
  done

example : P ↔ P ∧ True := by
  constructor
  . intro hP
    constructor
    . exact hP
    . trivial
  . rintro ⟨hP, _⟩
    assumption
  done

example : False ↔ P ∧ False := by
  sorry
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry -- homework
  done

example : ¬(P ↔ ¬P) := by
  by_contra h
  by_cases hP : P
  . have hN : ¬P := by
      apply h.mp
      assumption
    contradiction
  . have hN : P := by
      apply h.mpr
      assumption
    contradiction
  done

-- or the same, more succintly (using theorem `em` that we did not cover yet)
example : ¬(P ↔ ¬P) := by
  intro h
  cases em P with
  | inl p => exact h.mp p p
  | inr np => exact np (h.mpr np)
