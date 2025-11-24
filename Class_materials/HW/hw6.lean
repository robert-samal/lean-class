import Mathlib.Tactic -- imports all the Lean tactics

variable (X Y : Type) (f : X → Y)
  (A B C D S T : Set X)
  (T : Set Y)

-- avoid using library lemmas, work from first principles
-- however, you may want to check that `exact?` solves this
example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D := by sorry

-- Here it is a good idea to use `Set.mem_compl_iff` and `not_forall_not`
-- Experiment with `rw` vs `simp_rw` vs `simp only`
-- Or, possibly, use `push_neg` after getting rid of `Aᶜ`
-- Don't just use one library lemma though.
example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by sorry

-- Again, avoid using `exact?` to find the library lemma (eventhough it works again).
-- Instead, use this as an opportunity to recall basic handling of conjuction
-- and disjunction, as well as tactic `rintro` that allows a short proof (8 lines).
-- Or, use interactive infoview to put together any proof :-)
example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by sorry

-- Recall the definitions of `f '' S` and `f ⁻¹' T`
-- avoid using a library lemma, do the proof from first principles
-- (as an exercise in working with sets defined by a property).
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by sorry


-- Recall how to do proofs by induction.
-- Also check the class materials for the proof of similar formula for the sum of squares.
-- You will probably need `Nat.cast_add` and `Nat.cast_one`.
example (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℚ) ^ 3 = (n : ℚ) ^ 2 * (n - 1) ^ 2 / 4 := by sorry
