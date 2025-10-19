import Mathlib.Tactic

/-!

# Second homework -- more logic

## Tactics

You will need the following tactics:

* `cases` (or `cases'`)
* `constructor`
* `left/right`
* `rw`
* `rfl`
* `ring`
* `norm_num`

It may be helpful to also use
* `assumption`
* `<;>`

For details on these, you may see https://b-mehta.github.io/formalising-mathematics-notes/Part_2/tactics/tactics.html
or https://leanprover-community.github.io/mathlib-manual/html-multi/Tactics/All-tactics/ .

As before, do NOT use tactics `tauto` or `simp` -- in this exercise the purpose
is to learn how to derive these things "hands-on".

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P ∧ Q ↔ Q ∧ P := by
  sorry
  done

example : (P ∧ Q → R) → P → Q → R := by
  sorry
  done

example : P ∨ False ↔ P := by
  sorry
  done

example : (P ↔ Q) → (R ↔ S) → (P ∨ R ↔ Q ∨ S) := by
  sorry
  done

example : ∀ x y : ℝ, (x+y)*(x-y) = x^2 - y^2 := by
  sorry
  done

example : ∃ x : ℝ, 0 < x ∧ x < 1 / 1000 := by
  sorry
  done
