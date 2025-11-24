/-
Copyright (c) 2025 Robert Šámal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Šámal, Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/

open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by
  intro h
--  exact h
  intro h2
  contradiction

example : x ∈ A → x ∉ A → False := by
  intro h1 h2
  contradiction
-- OR: exact h2 h1


-- hw
example : A ⊆ B → x ∉ B → x ∉ A := by sorry

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
  by_contra h
  cases h

example : x ∈ Aᶜ ↔ x ∉ A := by
  rfl

-- this simple statement is also a theorem in the library
example : x ∈ Aᶜ ↔ x ∉ A := mem_compl_iff A x
-- the reason for this is that we can then use it by `rw` et al.
-- (see below)

-- perhaps surprisingly, the next one is different
-- `rfl` does not solve it, as it is not equal by definition
-- we may solve it explicitly
example : x ∉ Aᶜ ↔ x ∈ A := by
  constructor
  . intro h
    change x ∈ Aᶜ → False at h -- added for the programmer/reader, Lean does not need it
    by_contra h2
    apply h
    exact h2
  . intro h1 h2
    contradiction

-- or we can first rewrite the definitino of `Aᶜ`, then get rid of double negation
-- and only then use `rfl`
example : x ∉ Aᶜ ↔ x ∈ A := by
  rw [mem_compl_iff]
  push_neg
  rfl

-- or use `simp` to search through the library
example : x ∉ Aᶜ ↔ x ∈ A := by
   simp

-- or, better yet, find the right theorem in the library by use of `exact?`
example : x ∉ Aᶜ ↔ x ∈ A := by
  exact notMem_compl_iff

-- the next one is easy
example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
-- `rw [mem_compl_iff]` does not work -- it does not work inside quantifiers
-- ``simp_rw [mem_compl_iff]`` this one does work
-- or we may use `simp only` -- the `only` part is important for performance
-- (avoids the library search)
  simp only  [mem_compl_iff]
  rw [not_exists_not]

-- or we can do it explicitly
example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  · intro h ⟨x, hx⟩
    exact hx (h x)
  · intro h x
    by_contra hx
    exact h ⟨x, hx⟩

-- hw
example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  simp only  [mem_compl_iff]
  rw [not_forall_not]
