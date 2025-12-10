/-
Graph101.lean
==============

Very first steps with `SimpleGraph` and trees in Lean 4 / mathlib.

Focus:
* basic use of `SimpleGraph`
* path graphs on `Fin n`
* definitions of tree
* “tree = connected + acyclic”
* “tree = unique simple path between any two vertices”

All nontrivial proofs are left as `sorry` for students.

You’ll likely want to compile this with a recent mathlib. If some names
move, update the imports and hints (search with `#find`, Loogle, etc.).
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
-- import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic

open scoped BigOperators
open SimpleGraph

namespace Graph101

/-!
## 1. A very small graph by hand

We start with a tiny vertex type and a simple graph on it, just
to see how `SimpleGraph` is structured.
-/

inductive V3
  | a | b | c
deriving DecidableEq, Repr

open V3

/-- A toy graph on 3 vertices: `a`–`b`–`c` is a path. -/
def G3 : SimpleGraph V3 where
  Adj
    | a, b => True
    | b, a => True
    | b, c => True
    | c, b => True
    | _, _ => False
  symm := by
    intro v w
    cases v <;> cases w <;> simp [Adj]
  loopless := by
    intro v
    cases v <;> simp [Adj]

/-!
**Exercise 1.1.** (Warmup)

Prove that `a` is adjacent to `b` but not adjacent to `c` in `G3`.
-/

example : G3.Adj a b := by
  -- unfold the definition and simplify
  simp [G3]

example : ¬ G3.Adj a c := by
  -- again, unfold + simp
  simp [G3]

/-!
**Exercise 1.2.**

Show that `G3` has no loops: this is already encoded in the definition
of `SimpleGraph` and enforced by the `loopless` field, but prove
a concrete instance by hand: `¬ G3.Adj a a`.
-/

example : ¬ G3.Adj a a := by
  -- try: `simp [G3]`
  sorry


/-!
## 2. Path graphs on `Fin n`

For serious work we don’t build graphs by hand — we reuse mathlib’s
constructions. The basic “model” graph is the path `0–1–2–…–(n-1)` on
vertices `Fin n`.

Mathlib calls this `SimpleGraph.pathGraph n : SimpleGraph (Fin n)`.
-/

/-- Path graph on `Fin n`. We give it a short alias `Pn`. -/
def Pn (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.pathGraph n

namespace Pn

/-- A handy abbreviation for degree in `Pn n`. -/
def degree {n : ℕ} [DecidableEq (Fin n)] [Fintype (Fin n)]
    (v : Fin n) : ℕ :=
  (Pn n).degree v

/-!
There is a lemma in mathlib (search for it!) that characterizes adjacency
in the path graph:

`(SimpleGraph.pathGraph n).Adj i j ↔ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i)`.

We’ll *use* that, but we won’t hard-code its name here.
Students should find it via `#find _ (SimpleGraph.pathGraph _)` or Loogle.
-/

/-!
**Exercise 2.1.**

Assume `n ≥ 2`. Show that every vertex in `Pn n` has degree at most 2.
(Do not try to prove the sharp bound yet.)

Hint: split into cases:
* `v = 0`
* `v = last` (the vertex with value `n-1`)
* middle vertices.
-/
example {n : ℕ} (hn : 2 ≤ n) [DecidableEq (Fin n)] [Fintype (Fin n)]
    (v : Fin n) :
    degree v ≤ 2 := by
  -- outline:
  -- * unfold `degree`
  -- * use the adjacency characterization for `pathGraph`
  -- * classify neighbors of `v`
  sorry

/-!
**Exercise 2.2.**

For `n ≥ 2`, show that the endpoints (0 and `n-1`) in `Pn n`
have degree exactly 1.
-/
example {n : ℕ} (hn : 2 ≤ n) [DecidableEq (Fin n)] [Fintype (Fin n)] :
    degree (0 : Fin n) = 1 := by
  sorry

example {n : ℕ} (hn : 2 ≤ n) [DecidableEq (Fin n)] [Fintype (Fin n)] :
    degree ⟨n-1, by
      have := Nat.sub_lt (by exact hn) (by decide : 0 < 1)
      simpa [Nat.sub_eq, Nat.lt_of_lt_of_le this hn]⟩ = 1 := by
  -- Feel free to simplify this endpoint; or replace ⟨...⟩ by `Fin.last n`.
  -- (There is a `Fin.last` in mathlib.)
  sorry

/-!
**Exercise 2.3.** (Connectivity)

Show that `Pn (n+1)` is connected.

Hint:
* Either use the existing lemma `SimpleGraph.pathGraph_connected`,
  or reprove the statement using `Walk`s and induction on `|i - j|`.
-/
example (n : ℕ) :
    (Pn (n+1)).Connected := by
  -- try `exact SimpleGraph.pathGraph_connected (n := n+1)` or similar
  sorry

end Pn


/-!
## 3. Trees: connected + acyclic

Mathlib has a notion `G.IsTree` for trees, and `G.IsAcyclic` for being
acyclic. There is also a lemma `SimpleGraph.isTree_iff` which says
roughly: “a finite graph is a tree iff it is connected and acyclic”.

Here we first define our own “`IsTree'`” and then prove the equivalence,
*pretending* we don’t know the library lemma. Afterwards one can
compare to the mathlib version.
-/

section Trees_basic

variable {V : Type*} (G : SimpleGraph V)

/-- A naive tree predicate: connected and acyclic. -/
def IsTree' : Prop :=
  G.Connected ∧ G.IsAcyclic

/-!
**Exercise 3.1.**

Show that `G.IsTree` implies `IsTree' G`.

(Hint: there are lemmas in the `Acyclic`/`Connectivity` files that unpack
`IsTree` into connected + acyclic. Search for them; or, as a first pass,
you can assume a lemma of the form
`G.IsTree → G.Connected` and another `G.IsTree → G.IsAcyclic`
and use them.)
-/
lemma IsTree.to_IsTree' :
    G.IsTree → IsTree' G := by
  intro h
  -- Strategy:
  -- * obtain `h_conn : G.Connected` from `h`
  -- * obtain `h_acyc : G.IsAcyclic` from `h`
  -- * return ⟨h_conn, h_acyc⟩
  sorry

/-!
**Exercise 3.2.**

Assume `V` is finite. Show that `IsTree' G` implies `G.IsTree`.

Now you’re going the other way: from “connected + acyclic” to “tree”.

Again, there is a mathlib lemma `SimpleGraph.isTree_iff` that does this.
Here we want a hand-rolled proof (maybe only in a special case, and then
later show how to call the library lemma instead).
-/
lemma IsTree'.to_IsTree [Fintype V] :
    IsTree' G → G.IsTree := by
  intro h
  -- Strategy:
  -- * write `h` as ⟨h_conn, h_acyc⟩
  -- * use an appropriate characterization of `IsTree` in mathlib
  --   (or prove it ad hoc for finite graphs, if you feel ambitious).
  sorry

/-- Optional: combine the two directions into an equivalence. -/
lemma isTree_iff_IsTree' [Fintype V] :
    G.IsTree ↔ IsTree' G := by
  constructor
  · intro h
    exact IsTree.to_IsTree' (G := G) h
  · intro h
    exact IsTree'.to_IsTree (G := G) h

end Trees_basic


/-!
## 4. Trees and unique simple paths

Another standard characterization of trees:

> A graph is a tree iff between any two vertices there is a unique
> simple path.

In Lean, “paths” are certain `Walk`s with no repeated vertices, and
“unique” is expressed via `∃! p : G.Walk v w, p.IsPath`.

Mathlib has a lemma `SimpleGraph.isTree_iff_existsUnique_path` that formalizes
exactly this. Here we use the direction “tree ⇒ unique path”.
-/

section UniquePaths

variable {V : Type*} (G : SimpleGraph V)

variable [DecidableEq V]  -- needed for path-ness / finiteness in some lemmas

/-!
**Exercise 4.1.**

Assume `G.IsTree`. Show that for any vertices `v w` there exists a unique
simple path between them.

In Lean-speak: prove that there exists a unique walk from `v` to `w`
which is a path.

There is a mathlib lemma of the form

`G.IsTree → ∀ v w, ∃! p : G.Walk v w, p.IsPath`.

Use that as the engine, but still write the statement and the proof
yourself.
-/
example (hT : G.IsTree) (v w : V) :
    ∃! p : G.Walk v w, p.IsPath := by
  -- Hint: search for `existsUnique_path` in `SimpleGraph`.
  sorry

end UniquePaths


/-!
## 5. Specializing to path graphs: `Pn n` is a tree

Now we put things together for a concrete family:

* show `Pn n` is connected (from above),
* show `Pn n` is acyclic,
* deduce `Pn n` is a tree,
* conclude there is a unique simple path between any two vertices.
-/

section Path_is_tree

/-- Reuse the earlier definition. -/
def Pn (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.pathGraph n

variable (n : ℕ)

instance instDecidableEqFin : DecidableEq (Fin n) := inferInstance
instance instFintypeFin : Fintype (Fin n) := inferInstance

/-!
**Exercise 5.1.**

Show that `Pn (n+1)` is connected and acyclic.

Connectivity was earlier (Exercise 2.3). For acyclicity, use that a path
graph has no cycles by combinatorial reasoning (no way to return to the
start without repeating a vertex).
-/
lemma Pn_connected :
    (Pn (n+1)).Connected := by
  -- you can reuse Exercise 2.3 or a mathlib lemma
  sorry

lemma Pn_acyclic :
    (Pn (n+1)).IsAcyclic := by
  -- prove directly, or search for a ready-made lemma
  sorry

/-!
**Exercise 5.2.**

Conclude that `Pn (n+1)` is a tree (using your `IsTree'` or directly
`SimpleGraph.IsTree`).
-/
lemma Pn_isTree :
    (Pn (n+1)).IsTree := by
  -- One option:
  --   have h := (Pn_connected (n := n))
  --   have h' := (Pn_acyclic (n := n))
  --   use `IsTree'.to_IsTree` with `G := Pn (n+1)`
  sorry

/-!
**Exercise 5.3.**

Show that between any two vertices of `Pn (n+1)` there is a unique
simple path.

This is just an instance of Exercise 4.1 applied to a concrete `G`.
-/
example (v w : Fin (n+1)) :
    ∃! p : (Pn (n+1)).Walk v w, p.IsPath := by
  -- apply the “tree ⇒ unique path” lemma with `G := Pn (n+1)`
  sorry

end Path_is_tree

end Graph101
