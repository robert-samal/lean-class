import Mathlib

/-
# PAT principle = Propositions-as-types, proofs-as-terms

1. Propositions (such as 0=0) are also types (as any other expression is a type).
2. A term of type P = proof of P
3. So to prove a proposition P, we need to show, that there **exists some term of type P**
4. Other than that, proofs serve no purpose: we don't store a sequence of formulas that consists
   proof, we just verify, that there is such a sequence -- that proof exists.
   In type theory parlance, we check if **the type is inhabited**.

-/


#check Eq.refl 0

-- we can prove the (trivial) statement 0 = 0 by directly refering to some theorem

example : 0 = 0 := Eq.refl 0

-- or by using tactics that do some work for us

example : 0 = 0 := by norm_num

/-
##  Revisiting Propositional logic
-/

variable (P Q R : Prop)

-- function application
theorem modus_ponens (hp : P) (hpq : P → Q) : Q := hpq hp

-- or using tactic to figure it for us
theorem modus_ponens_tactical (hp : P) (hpq : P → Q) : Q := by
  apply hpq
  exact hp

/- try for yourself based on
https://en.wikipedia.org/wiki/Rule_of_inference#Classical
-/

-- theorem hypothetical_syllogism := sorry

-- Modus tollens


/-
## Logical and
-/

#print And

theorem And_swap_raw (a b : Prop) :
    a ∧ b → b ∧ a :=
  fun hab : a ∧ b ↦ And.intro (And.right hab) (And.left hab)

theorem And_swap_tactical (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab
