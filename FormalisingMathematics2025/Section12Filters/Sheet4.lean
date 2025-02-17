/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Filters and limits

The motivation for filters was to unify different ways of talking about limits, so to finish this
story we need to know how to use this filter language to talk about limits!

The key ingredients we'll need for this story are:
* the order relation on filters
* our two special filters `atTop` and `nhds`
* the pushforward of a filter: `Filter.map`

We've seen the first two of these, so let's talk about the third.

Given a filter `f : Filter α` and a map `m : α → β`, there's a reasonably natural way of making
a `Filter β`: a set `s : Set β` will be in our filter if its preimage under `m` (which
is `m ⁻¹' s : Set α`) is in `f`. Let's make this and check it's a filter.
-/

namespace Filter

variable {α β : Type*}

def map' (f : Filter α) (m : α → β) : Filter β where
  sets := {s | m ⁻¹' s ∈ f}
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry

/-
Now I can write down what it means for a function `f` to tend to a filter `l₂` under a filter `l₁`.
Then if `f : ℕ → ℝ`, `l₁ = atTop`, and `l₂ = nhds 0`, I claim `Tendsto f l₁ l₂` means the same as
what we'd informally write as $lim_{x → ∞} f(x) = 0$.

Similarly, if `l₁ = nhds a` and `l₂ = nhds b`, then `Tendsto f l₁ l₂` will be that `f(x) → b` as
`x → a`.
-/

def Tendsto' (f : α → β) (l₁ : Filter α) (l₂ : Filter β) : Prop :=
  l₁.map f ≤ l₂

-- That felt too easy.
-- Let's make sure it does actually work.

#check Metric.tendsto_nhds_nhds
#check Metric.tendsto_atTop

lemma tendsto_atTop_atTop_iff {α β : Type*} [LinearOrder α] [LinearOrder β] (f : α → β) :
    Tendsto f atTop atTop ↔ ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → b ≤ f a := by
  sorry

end Filter
