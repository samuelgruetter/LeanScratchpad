


/-
The different tactic monads:


GrindM <- GrindTacticM
  |
  V
SymM
  |
  V
MetaM <-- TacticM
  |
  V
CoreM

If I write `sym =>` or `grind =>` I get GrindTacticM in both cases.
by `grind =>` eagerly applies "by contradiction" so less useful than `sym =>`
`sym =>` preprocess all hypotheses by default

`sym =>` runs all grind homomorphism preprocessing and maintains the egraph


TacticM: processing the "by"

MetaM keeps track of the context of each metavar so that it can check
that instantiations only use in-scope vars.
Lots of operations become quadratic because linear metavar context traversal.

SymM: only keeps track of highest variable in scope per metavariable.
Puts restrictions on how you can use/create metavariables.
Software verification applications.

GrindM: adds egraph

Also elaration monads such TermElabM
-/


/-
View
sym =>
grind =>
as an enviroment to debug tactics written in SymM and GrindTacticM

grind?
-> sugggests proofs so that we don't need to rerun full grind
can use scripts output by grind? to avoid doing search again

To write tactics in GrindTacticM:
by grind =>
instantiate
have
simp
But not all tactics are available there, only those that put all terms
into the e-graph and don't delete vars


The `tests/elab` directory contains interesting examples such as
https://github.com/leanprover/lean4/blob/master/tests/elab/grind_interactive.lean
https://github.com/leanprover/lean4/blob/master/tests/elab/sym_simp_grind_discharger.lean
https://github.com/leanprover/lean4/blob/master/tests/elab/sym_simp_variant_discharger.lean
https://github.com/leanprover/lean4/blob/master/tests/elab/sym_simp_interactive1.lean

-/
example (a b : Nat) : a + b - a = b := by simp

/-

simp inside "grind =>" is different
permanent cache:
transient cache: "this thing is unprovable", may become invalid later
source term and result term and equality proof

sym simp procs
cbv
ground simproc
cbv_opaque

-/

/-
simp does not use any heuristics to decide whether to unfold a definition.
That leads to more stable proofs, but it might be harder to simplify
goals into a "nice" shape.

preprocessing is only hypotheses, not on goals
But eg "intro" will automatically preprocess intro'd hyps
-/


set_option trace.grind.hom true
example (x : UInt16) : (h : x < 100) →  x + y = 0 := by sym =>
  intro h
  --by_contra
  done



def getAt (l : List Nat) (i : Nat) : Nat := l[i]?.getD 0
def getAt' (l : List Nat) (i : Nat) : Nat := l[i]?.getD 0

theorem getAt_append_left {xs ys : List Nat} {i : Nat} (h : i < xs.length) :
    getAt (xs ++ ys) i = getAt xs i := by
  simp [getAt, List.getElem?_append_left h]

/-
--> register register_sym_simp variants

-/
--example xs

inductive Color where | red | green | blue

-- @[simp]
def index (c : Color) : Nat :=
  match c with
  | .red => 0
  | .green => 1
  | .blue => 2

example c : index c = index .red -> c = .red := by
  simp [index]
  cases c <;> simp

-- can add own simproc with own heuristics
/-
Lean.Meat.Sym.Simp.ControlFlow eg simpCond to simplify a ite
Have is an example of a simproc

There are simprocs for meta simp and sym simp.

-/


-- minimal representative of terms from E-graph

/-
GoalState in Lean.Meta.Tactic.Grind.Types
eg forEachNode
fold over
foldEqc
circular list in equivalence classes

how to add equations to egraph

2) heuristic unfolding exercise for simproc
3) simproc reads egraph, may create new terms not in egraph, but read egraph
4) to update egraph: understand invariants. simpifier goes under binders.

-/
