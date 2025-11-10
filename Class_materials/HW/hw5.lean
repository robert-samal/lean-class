import Mathlib

section First
open Real
variable (a b c d : ℝ)

-- In the first problem, you verify the elementary distributivity law.
-- The goal is to learn the "step-by-step" procedure, using `calc` and `rw`.
-- Do not use `ring` tactic here.
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry
end First

section Second
open Function
variable (X Y Z : Type)

-- You will probably need (some of) these theorems from the last class.
theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) : (g ∘ f) x = g (f x) := by
  rfl
theorem id_eval (x : X) : id x = x := by
  rfl
theorem injective_def (f : X → Y) : Injective f ↔ ∀ a b : X, f a = f b → a = b := by
  rfl
theorem surjective_def (f : X → Y) : Surjective f ↔ ∀ b : Y, ∃ a : X, f a = b := by
  rfl


-- tactic `funext` comes in handy in this one
example (f : X → X) : id ∘ f = f := by
  sorry

-- `rw [Injective]` and `rw [injective_def]` are not exactly the same!
example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f := by
  sorry

example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  sorry

end Second

section Third
-- Next, we saw how to use a specific example -- particular finite types.
-- These are the same as we had in class.

open Function
-- Let X be {a}
inductive X : Type
  | a : X

-- Let Y be {b,c}
inductive Y : Type
  | b : Y
  | c : Y

-- Let Z be {d}
inductive Z : Type
  | d : Z

-- Define f by f(X.a)=Y.b
def f : X → Y
  | X.a => Y.b

-- define g by g(Y.b)=g(Y.c)=Z.d
def g : Y → Z
  | Y.b => Z.d
  | Y.c => Z.d

-- We have seen the following easy
theorem Yb_ne_Yc : Y.b ≠ Y.c := by
  intro h
  -- x ≠ y is definitionally equal to (x = y) → False
  cases h

-- next, prove this:
theorem gf_injective : Injective (g ∘ f) := by
  sorry

-- and finally, we have the following (very easy) proposition about injective functions
-- we saw in class that this is true and the types defined above should be a counterexample.
-- Now, convince Lean that it is so.
example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Injective (ψ ∘ φ) → Injective ψ := by
  sorry

end Third

section Fourth
open Function
-- Next, do the same thing for surjective functions:
-- Prove one of the following two theorems (the other one is false, so don't prove that)
-- You may use results above, if needed.
theorem Inner_surj :  ∀ X Y : Type, ∀ f : X → Y, ∀ g : Y → Z,
  Surjective (g ∘ f) → Surjective f := by
  sorry

theorem notInner_surj :  ¬ ∀ X Y : Type, ∀ f : X → Y, ∀ g : Y → Z,
  Surjective (g ∘ f) → Surjective f := by
  sorry

end Fourth
