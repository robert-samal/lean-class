/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP
  done

example : Q → P ∨ Q := by
  sorry
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ hPR hQR
  cases hPoQ with
  | inl h => exact hPR h
  | inr h =>
      apply hQR
      assumption

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl h =>
     right
     assumption
  | inr h =>
     left
     assumption
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  . rintro ((hP|hQ) | hR)
    left; assumption
    right; left; assumption
    right; right; assumption
  . sorry -- try it yourself as above!
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1 h2
  rintro (hR | hS)
  . left; apply h1; assumption
  . right; apply h2; assumption
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h
  rintro (hP | hR)
  . left; apply h; assumption
  . right; assumption
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  rw [h1,h2]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  . intro h
    change (P ∨ Q → False) at h -- not needed, but easier to read (?)
    constructor
    . intro hP
      apply h
      left
      exact hP
    . intro hQ
      apply h
      right
      exact hQ
  intro h
  cases' h with hnP hnQ
  rintro (hP|hQ) <;>
  . contradiction
  done

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro p; exact h (Or.inl p) -- same as above, but shorter
    · intro q; exact h (Or.inr q)
  · intro ⟨np, nq⟩ pq
    cases pq with
    | inl p => exact np p
    | inr q => exact nq q



example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  . intro h
    by_cases hP : P
    . right; by_contra hQ; apply h
      constructor <;> assumption
    . left; assumption
  . rintro (hnP|hnQ) <;>
    . intro h
      cases' h with hP hQ
      contradiction
  done

-- or the same, but shorter, using more general API to `rintro`
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  . intro h
    by_cases hP : P
    . right; by_contra hQ; apply h
      constructor <;> assumption
    . left; assumption
  . rintro (hnP|hnQ) ⟨hP,hQ⟩ <;> contradiction
  done
