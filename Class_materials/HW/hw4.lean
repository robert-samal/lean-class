/-!
## Prod type

### Construction
Objects of this type can be defined in two ways as shown below.
`#print Prod` will suggest one, the ⟨ ⟩ notation is just syntactic sugar for the
"real" defintion using the constuctor `Prod.mk`. Also `A x B` is nice syntax for
`Prod A B`
-/

def tuple1 := Prod.mk 0 1
def tuple2 : Nat × Nat := ⟨0, 1⟩

#print Prod

#check Prod
#check Prod Nat Nat

#check tuple1
#check tuple2
#print tuple1
#print tuple2

-- check that both ways define the same object
example : tuple1 = tuple2 := rfl
example : (Nat × Nat) = (Prod Nat Nat) := rfl

/- ### Deconstruction
The `#print Prod` tells us the names of the fields: `.fst`, `.snd`. The other syntax is equivalent.
-/

#eval tuple1.1
#eval tuple1.2
#eval tuple1.fst
#eval tuple1.snd


/- ## Function types
We know these already. Just to revisit two possible ways to write them.
We consider them equal (by what is called eta-conversion).

## Construction
-/
def f1 : Nat → Nat := fun x => x
def f2 := fun x : Nat => x
def f3 (x : Nat) : Nat := x

#check f1
#check f2
#check f3

example : f1 = f2 := rfl

/- ## Deconstruction
-/

#eval f1 5

/-!
## TASK FOR YOU:
-/

#check (Nat → Nat) → (Nat × Nat) → Nat
#check (Nat × Nat → Nat) × (Nat → Nat → Nat × Nat)

/-
Define (arbitrary) objects of the above types
Do it in two ways (as `f1` and `f2` above).
Use `#check` to check the types and `example ... rfl` to verify that both definitions do the same.
-/

def a1 : (Nat → Nat) → (Nat × Nat) → Nat := sorry
-- def a2 := sorry

-- #check a1
-- #check a2
-- example : a1 = a2 := rfl

def b1 : (Nat × Nat → Nat) × (Nat → Nat → Nat × Nat) := sorry
-- etc.

/-
# Logical connectives & PAT principle

Let us now try to understand how the basics of logic is implemented in Lean.
Keep in mind the PAT principle:
if type P is a logical formula (`P : Prop`) then
**type P is _inhabited_ (there is a term of type P) iff P is provable.**
-/

-- ## Type False

#print False
-- type False is defined so, that we cannot create any term of this type (there is no constructor)

-- Proof by contradiction is based on the truth of `False → P` for any `P`
-- This is kind of strange -- but works here, as an empty mapping is defined on an empty type `False`.
-- This kind of empty mapping is actually useful, so it has a name: False.elim
-- but it can be also implemented as below, using `nomatch` keyword.

variable (P : Prop) (hp : P)
example : False → P := False.elim
example : False → P := fun h => nomatch h

#print False.elim
#print False.rec

-- ## Type True

#print True
-- otoh, True has a constructor, so we have terms of this type
#check True.intro
-- we can give it fancy names, if we want
def basic_truth := True.intro
-- the usual name for this is `trivial`
example : basic_truth = trivial := rfl
-- these two terms have been defined in the same way -- in fact, there is no other way to create
-- terms of type True (there is only one constructor)
-- In fact, for any `P : Prop`  there is **at most one** object of type `P`
-- (so-called proof-irrelevance, all proofs are considered the same)

-- ## And
#print And

/- ### Construction
Based on the definition of structure type (see the output of `#print And` above),
a way (the only way) to create proof term of type (And P Q) is to use constructor And.intro
with the proofs of P and of Q (objects of types P and Q).
There is a shorter way to typeset this using the angle brackets.
Btw, don't worry for now about how `And P Q` is translated to `P ∧ Q`.
This corresponds to the usual meaning of the logical connective -- and also
to how we have used this before.
Note also the similarity with `Prod`.
-/
variable (P Q : Prop)
namespace and_section
variable (hp : P) (hq : Q)
/- by assuming existence of these variables, we are saying that
- P, Q are propositions
- and both of them have a proof (this we do only in this namespace)
Now to get a proof of the conjunction:
-/

def hpq1 : And P Q := And.intro hp hq
def hpq2 : P ∧ Q := ⟨ hp, hq ⟩

#check hpq1
#check hpq2
example : hpq1 = hpq2 := rfl

/- ### Deconstruction
An object (proof term) of type (And P Q) has two fields `.left` and `.right` (again, see the definition).
Which means, when we have a proof of type `P ∧ Q`, we can obtain proof of `P` and also a proof of `Q`.
-/

def first_deduction (hpq : P ∧ Q) : P := sorry
def second_deduction (hpq : P ∧ Q) : Q := sorry

end and_section

-- ## Or
#print Or

/- ### Construction
Now, do the same for Or: read carefully the definition above.
Construct an object of type `P ∨ Q` -- do it twice, once using a proof of P, second using a proof of Q.
Check it has the right type -- and think that these are the only ways to obtain a term of this type.
-/

def or_first_proof (hp : P) : P ∨ Q := sorry
def or_second_proof (hq : Q) : P ∨ Q := sorry

#check or_first_proof

/- ### Deconstruction
Show "Disjunctive syllogism": if we have objects of types `P ∨ Q` and `¬ P` then
we can create an object of type `Q`.
You will need `match hpq with` to learn which constructor was used to create term hpq.
Also `False.elim` will be helpful.
-/

example (hpq : P ∨ Q) (hnp : ¬ P) : Q :=
  sorry

/- ## Not
As we said before, `Not P` is definitionally equal to `P → False`.
Check the definition using `#print Not` below and explain, why
it does what it should -- not using logic truth tables as we did before,
but in terms of inhabited types.
-/

#print Not


/- ## For all
Formula with a general quantifier ∀ is a dependent function type.
The word dependent means, that type of `f x` may depend on `x`.

The interpretation in view of PAT principle: to get a proof of (say)
`∀ x : Nat, P x` we need to provide a function that maps any `x : Nat` to
a proof of `P x` -- that is, to an object of type `P x`.
It can be denoted as `(x : Nat)→P x` but more usual is `(x : Nat) : P x`.
This corresponds to the normal meaning of the syntax: we just need to prove
the formula for every x.

### Deconstruction
A basic rule of deduction is that if something is true for every x, then
it is also true for any chosen object of the right type.
Observe, how this is just function application.
-/

#check Eq.refl

def equal_is_reflexive : ∀ x : Nat, x = x := Eq.refl

-- Note the difference here:
#check Eq.refl
#check equal_is_reflexive

def simple3 : 3 = 3 := sorry

/-
### Construction
Other than using a result from the library (as `Eq.refl` above) we may construct
proofs by induction. Here is a simple example on basic properties of addition.
This is defined by recursion using the formula `0 + (k + 1) = Nat.succ (0 + k)`
(We will talk about this more, later.)
 -/

#print Nat.add

-- The usual way to prove this would be by using tactics, like this:
theorem add_zero_left_tactic (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    -- Inductive step
    -- k : Nat
    -- ih : 0 + k = k
    -- Goal: 0 + (k + 1) = k + 1
    -- We use `Nat.add_succ` which is the definition: 0 + (k + 1) = Nat.succ (0 + k)
    rw [Nat.add_succ, ih]

-- Rewrite this as a recursive proof of an appropriate object (using `match`)
-- to make it clear, that we are building a function from Nat.
-- You may still use "by rw" though (not to distruct us from the main topic here)
-- you need to find out how to get the induction hypothesis though
theorem add_zero_left_term (n : Nat) : 0 + n = n :=
  sorry


/- ## Exists
To finish the FO logic syntax, we need to deal with the existence quantifier ∃.
As seen from the definition, to create a formula of type Exists, we need to
give it an object and a proof that it has the right property.

Also note again the ⟨ ⟩ notation -- it works generally for types with only one
constructor, and passes the arguments to the constructor. (We have already seen this
for Prod and And.)
-/
-- ### Construction
#print Exists

def exists_one : ∃ x : Nat, x=1 := Exists.intro 1 (Eq.refl 1)
example : ∃ x : Nat, x=1 := ⟨ 1, Eq.refl 1⟩

-- ### Deconstruction
-- we can use `match ... with | ` as in other inductive types

def even (n : Nat) := ∃ k : Nat, n = 2*k

def four_is_even : even 4 := sorry

-- here you may again use tactics `by rw` in the final step
theorem plus_two_even (n : Nat) : even n → even (n+2) := sorry

/- ## Iff -- bonus
Observe that Iff (↔) is defined as it should be and that the fields `.mp` and `.mpr` correspond to what we have
used in proofs before.
-/

#print Iff
