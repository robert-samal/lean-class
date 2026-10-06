import Mathlib.Logic.Function.Basic

/-!
# An opening demonstration: the diagonal set

The argument below proves that an arbitrary proposed
list of subsets of ℕ misses at least one subset.
The first proof spells out the mathematical
argument; the last proof reuses the result
already available in Mathlib.
-/

namespace FirstClassDemo

def ℕ := Nat

-- `f n` is the nth subset on a proposed list.
-- Keep n precisely when the nth subset leaves n out.
def diagonal (f : ℕ → Set ℕ) : Set ℕ :=
  { n | n ∉ f n }

theorem cantor_thm (f : ℕ → Set ℕ) : ¬ Function.Surjective f := by
  intro hf -- for contradiction, assume f is surjective
  let D : Set ℕ := diagonal f -- define a set that differs from every f k
  obtain ⟨k, hk⟩ := hf D   -- hk : f k = D
  classical -- we do classical logic: a statement or its negation is true
  -- this allows shorter proof than what I showed in class
  by_cases h : k ∈ f k
  · have hD : k ∈ D := by
      rw [← hk]
      exact h
    exact hD h                 -- k ∈ D means k ∉ f k
  · have hD : k ∈ D := h      -- again, by the definition of D
    have hfk : k ∈ f k := by
      rw [hk]
      exact hD
    exact h hfk

#print Function.Surjective

-- The same result using Mathlib. Here α can be *any* type, not only ℕ.
#print Function.cantor_surjective

example {α : Type} (f : α → Set α) :
    ¬ Function.Surjective f := by
  exact Function.cantor_surjective f


theorem no_list_of_all_subsets2 (f : ℕ → Set ℕ) :
    ¬ Function.Surjective f := by
  exact Function.cantor_surjective f

end FirstClassDemo
