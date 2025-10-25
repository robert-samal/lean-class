import Mathlib.Tactic

import Class_materials.Solutions.Class04.Reals5
-- import the definition of `TendsTo` and the theorems we proved from previous sheets
-- if it does not work for you, pull from the repo
-- Alternately, uncomment the definition below for the definition
-- And perhaps copy-paste the theorems `tendsTo_neg`, `tendsTo_add `

/-
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε
-/

open Section2sheet3solutions
open Section2sheet5solutions

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)` tends to `t - u`. -/
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
  -- this one follows without too much trouble from earlier results (two lines at most)
  -- Or you can do it in a similar way.
  sorry


/-- A sequence has at most one limit. First perhaps recall how it is done using pen and paper.
   This one is a bit longer. You will need all of the tactics we have learned
   (`by_contra`, `specialize`, `obtain`, `have`, etc.) and also `exact?` to search for the
   names of basic theorems. Or you may guess which of the following suits you:
   `half_pos`, `abs_pos`, `le_max_left`, `abs_add_le`,
   `abs_sub_com`, `add_lt_add`, `lt_self_iff_false`
 -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  sorry
