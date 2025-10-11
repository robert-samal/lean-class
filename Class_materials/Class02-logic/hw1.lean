import Mathlib.Tactic -- imports all the Lean tactics
set_option linter.unusedTactic false

/-
You'll need to know about the tactics we have used (`intro`, `exact`, `apply`, `trivial`, `exfalso`)
and also probably

* `by_contra` -- start a proof by contradiction
* `contradiction` -- use when you already get two contradicting assumptions
* `change` -- use for rewriting assumptions or goal to an equivalent form
* `by_cases` -- use to distinguish, whether a proposition is true or not

See also https://b-mehta.github.io/formalising-mathematics-notes/Part_2/Part_2.html

DO NOT USE TACTICS `tauto` (it can solve all of these problems for you).
Also, I suggest to switch off copilot if you are using it.

-/

variable (P Q R S : Prop)

example : P → Q → R → R := by
  sorry
  done

example : False → True := by
  sorry
  done

example : P → ¬¬P := by
  sorry
  done

example : ¬¬P → P := by
  sorry
  done

example : (P → ¬Q) → Q → ¬P := by
  sorry
  done
