/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

#check f '' S
#check f ⁻¹' T

-- We can use library theorems:
example : S ⊆ f ⁻¹' (f '' S) := by
   intro x hx
   simp_rw [Set.mem_preimage] -- this can be omitted, it is applied automatically
   exact Set.mem_image_of_mem f hx
-- alternately:
--   simp_rw [Set.mem_image]
--   use x

-- but it can be done much simpler:
example : S ⊆ f ⁻¹' (f '' S) := by
   intro x hx
-- to show `x ∈ f ⁻¹' T` is (by definition) the same as to show `f x ∈ T`
-- so, we need to show `f x ∈ f '' S`
-- by definition of `f '' S` this means
-- `∃ x : X, x ∈ S ∧ f x = f x`
-- so, we can say just:
   use x

-- `exact?` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by sorry

example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
   constructor
   . intro h x hS
     -- we need to show `f x ∈ T`
     have h2 : f x ∈ f '' S := by use x
     exact h h2
   . intro h y hy
     obtain ⟨x, hx⟩ := hy
     have h3 : x ∈ f ⁻¹' T := h hx.left
     change f x ∈ T at h3
     rw [hx.right] at h3
     exact h3


-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by
  rfl

-- pushforward is a little trickier. You might have to `ext x`, `constructor`.
example : id '' S = S := by
  ext x
  constructor
  . intro hx
    obtain ⟨y, hy⟩ := hx
    have h4 : y = x := hy.right
    rw [← h4]
    exact hy.left
  . intro hx
    use x
    constructor
    . exact hx
    . rfl

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by sorry

-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by sorry
