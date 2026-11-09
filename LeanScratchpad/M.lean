


/-
The different tactic monads:

GrindM
  |
  V
SymM
  |
  V
MetaM <-- TacticM
  |
  V
CoreM

MetaM keeps track of the context of each metavar so that it can check
that instantiations only use in-scope vars.
Lots of operations become quadratic because linear metavar context traversal.

SymM: only keeps track of highest variable in scope per metavariable.

GrindM: adds egraph
-/


/-
To write tactics in GrindM:
by grind =>
instantiate
have
simp
But not all tactics are available there, only those that put all terms
into the e-graph and don't delete vars
-/



/-
simp does not use any heuristics to decide whether to unfold a definition.
That leads to more stable proofs, but it might be harder to simplify
goals into a "nice" shape.
-/

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
