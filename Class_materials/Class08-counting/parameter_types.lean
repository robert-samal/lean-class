/-
# Function parameters in Lean: explicit, implicit, strict implicit (and instances)

Lean has several kinds of function parameters / binders:

* `(x : α)`   — explicit
* `{x : α}`   — implicit
* `⦃x : α⦄`   — strict implicit  (ASCII: `{{x : α}}`)
* `[inst : C α]` — instance implicit (typeclasses)
(or just `[C α]`)

The **kind of binder** tells Lean *who* is responsible for supplying the
argument and *when* it should be determined.
-/

namespace ParamKinds

/-!
## 1. Explicit parameters `(x : α)`

* You (the caller) must always supply them.
* Lean never tries to guess them.
* Use them for "real data" the function operates on, *not* for types or indices.
-/

def addOne (n : Nat) : Nat :=
  n + 1

-- You must pass the argument:
#eval addOne 5      -- ok
-- #eval addOne 5.      -- error: wrong type
-- #eval addOne     -- error: missing explicit argument

/-
Semantics:
- The function's type is `Nat → Nat`.
- The caller *always* decides `n`.
- There is no inference or typeclass search here.
-/

/-!
## 2. Ordinary implicit parameters `{x : α}`

Syntax: `{x : α}`

* Lean *tries to infer* them automatically from:
  - later explicit arguments,
  - and/or the expected result type.
* If Lean can uniquely infer the value, you *don't* write it.
* You can still pass them manually if needed (e.g. with `@` or named args).

Typical uses:
* Type parameters: `{α : Type}`
* “Indices” determined by another argument, e.g. `{n : Nat}` for `Fin n`
* Data that is "contained" in some explicit proof.
-/

def myId {α : Type} (x : α) : α := x

#check myId "hello"
#check myId 7

#eval myId "hello"
#eval myId 7

#eval myId (α := Nat) 7
#eval @myId Nat 7


-- Why is the following an error?
-- def myadd {α : Type} (x : α) (y : α) : α := x + y


-- A polymorphic identity function with an implicit type parameter.
def addTwo {α : Type} [Add α] [OfNat α 2] (x : α) : α :=
  x + 2

-- `α` is inferred from the type of `x`:
#check addTwo (42 : Nat )       -- : Nat
#eval addTwo 42

#check addTwo (42 : Float )       -- : Nat
#eval addTwo 42.


/-
Semantics (ordinary implicit):
* At each call site, Lean solves `{α}` by unification:
  it looks at the types involved and tries to find the unique `α` that
  makes the application well-typed.
* If it can't infer `{α}`, you'll get an error and Lean will tell you
  to specify the implicit argument.
-/

-- Example where an index is inferred from a proof:
variable {α : Type} (x y : α) (h : x = y)

def useEq {α : Type} {x y : α} (h : x = y) : α :=
  x

-- `α`, `x`, `y` are all inferred from `h`:
#check useEq h        -- : α

/-
Reason to use `{}`:
* “This parameter is logically part of the function,
  but in practice, it should be recoverable from other arguments
  so callers shouldn’t have to write it.”
* Reduces clutter, especially for type parameters and indices that are
  almost always determinable from context.
-/

/-!
## 3. Strict implicit parameters `⦃x : α⦄` (double curly)

Syntax: `⦃x : α⦄`   (ASCII: `{{x : α}}`)

* Also filled by unification, like `{x : α}`…
* **but** Lean only tries to infer them when there are
  **explicit arguments following them**.
* If you use the function *without* explicit arguments, the strict implicit
  stays *unapplied* — the function remains polymorphic.

This matters when you want to *keep* something as a polymorphic function,
without Lean eagerly instantiating all implicits.
-/

-- Compare these two:

def idOrdinary {α : Type} : α → α :=
  fun x => x

def idStrict ⦃α : Type⦄ : α → α :=
  fun x => x

-- def f := onlyOrdinary  -- this is an error!
def g := onlyStrict

/-!
## 4. Instance implicits `[inst : C α]` (typeclass parameters)

Syntax: `[inst : C α]` or just `[C α]`

* These are also implicit, but **filled by typeclass search**,
  not by unification from later arguments.
* Typical examples: `[Group G]`, `[DecidableEq α]`, `[Monad m]`, …

Idea:
* Think of them as "dictionaries" of operations/laws that Lean
  looks up for you automatically.
-/

-- Example: a generic "size" for types with a `SizeOf` instance.
def sizeTwice {α : Type} [SizeOf α] (x : α) : Nat :=
  sizeOf x + sizeOf x

-- We can use it on any type with a `[SizeOf]` instance:
#eval sizeTwice (10 : Nat)
#eval sizeTwice (some 10)    -- Option has a SizeOf instance too

/-
Semantics (instance implicits):
* Lean runs typeclass resolution to build a value of type `C α` whenever
  a `[C α]` parameter is needed and not supplied explicitly. :contentReference[oaicite:4]{index=4}
* You can still give them explicitly with named args:
    sizeTwice (x := 10) (inst := inferInstance)
  but you almost never need to.

Why we want `[ ]`:
* Encodes shared structure (algebraic structures, order, monad, etc.)
  without passing huge “records of operations” manually everywhere.
* Keeps code close to standard mathematical notation.
-/

/-!
## 5. Quick comparison & rules of thumb

Binder kinds:

1. `(x : α)` — explicit
   * Caller must supply.
   * Use for “real” arguments: numbers, lists, graphs, etc.

2. `{x : α}` — ordinary implicit
   * Inferred from explicit arguments / expected type by unification.
   * Good for type parameters and indices logically determined by others.

3. `⦃x : α⦄` — strict implicit
   * Like `{x}` but not inferred unless explicit arguments follow.
   * Keeps functions/lemmas polymorphic when referred to as bare names.
   * Use when eager instantiation of `{x}` would be annoying or fragile.

4. `[inst : C α]` — instance implicit (typeclasses)
   * Filled by typeclass search, using instances in the environment.
   * Use for structures: groups, rings, orders, `Decidable` assumptions,
     monads, etc.

Some practical tips:

* Start with:
    def f {α : Type} (x : α) : α := ...
  and only reach for `⦃α⦄` when you hit problems with Lean instantiating `α`
  too early.

* Use `[C α]` not `{inst : C α}` for typeclasses: you want typeclass search.

* When debugging what Lean infers:
  - Use `#check` and sometimes `#check @f` to see all arguments explicitly.
  - If inference fails, temporarily make a parameter explicit and see what
    value you *wish* Lean had inferred.

-/

end ParamKinds
