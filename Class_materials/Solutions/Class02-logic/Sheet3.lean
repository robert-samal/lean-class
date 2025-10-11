/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics
set_option linter.unusedTactic false

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
--  "exact h" does not work here
--  "trivial" does
  change True → False at h -- for clarity we change h to its definitional equivalence
  apply h
  trivial
  done

example : False → ¬True := by
  intro h
  exfalso
  exact h
  done

example : ¬False → True := by
  intro h
  trivial
  done

example : True → ¬False := by
  intro h
  intro h2
  exact h2
  done

-- all of the above could also be solved by "trivial"

example : False → ¬P := by
  intro h
  exfalso
  exact h
  done

-- perhaps more simply:
example : False → ¬P := by
  intro h
  contradiction
  done

example : P → ¬P → False := by
  intro h1 h2
  contradiction
--  "trivial"  also works, but perhaps too easy/vague
  done

example : P → ¬P → False := by
  intro h1 h2
  contradiction
  done

example : P → ¬¬P := by
  intro h1
  change ¬P → False -- not really needed, because intro tactics works "up to definitional equality"
  intro h2
  contradiction
  done

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ
  intro h
  intro hP
  apply hPQ at hP
  contradiction
  done

example : ¬¬False → False := by
  intro h
  apply h
  intro h2
  exact h2
  done

example : ¬¬P → P := by
  intro h
  by_contra h2
  contradiction
  done

example : (¬Q → ¬P) → P → Q := by
  intro h hP
  by_cases hQ : Q
  . exact hQ
  . apply h at hQ
    contradiction
    done
