import LeanScratchpad.CatNotation

/-!
One instruction per line, as in Kraken's `x64_prog`, with the item `lineEq` of
`notation ... in c` (issue 4 of Kraken's `X64/Parser/design.md`).

Kraken wraps every instruction rule in `withPosition(...)` and puts `lineEq` before each operand.
Here a rule with a `lineEq` item gets the `withPosition` from `notation ... in c`, so `lineEq`
refers to the rule's first item (the mnemonic).

Tested first: `lineEq` without that `withPosition`, relying on the one of the hand-written
directive rule. It broke in two ways. `[instruction| pushq %rax]` on the line after
`example : Instr :=` was rejected: `lineEq` used a position saved by Lean's parser for the
declaration. And `pushq` and `%rax;` on two lines were read by the `;` rule, which has no
`withPosition`.
-/

set_option autoImplicit false

inductive Reg | rax | rbx
inductive Instr | push (r : Reg) | pop (r : Reg) | ret

declare_syntax_cat register
entry_notation "[register| " r:register "]" => r
notation "%rax" in register => Reg.rax
notation "%rbx" in register => Reg.rbx

declare_syntax_cat instruction (behavior := both)
entry_notation "[instruction| " i:instruction "]" => i
notation "pushq " lineEq r:register in instruction => Instr.push r
-- No `lineEq`, for comparison.
notation "popq " r:register in instruction => Instr.pop r
notation &"retq" in instruction => Instr.ret

/-! The fixed part: directives and programs, written with `syntax` as in Kraken
(`notFollowedBy`, `*`). -/

declare_syntax_cat directive
syntax withPosition(instruction notFollowedBy(lineEq (register <|> ","))) : directive
syntax instruction ";" : directive
syntax "[program| " directive* "]" : term
macro_rules
  | `([program| $ds*]) => do
    let is ← ds.mapM fun
      | `(directive| $i:instruction) | `(directive| $i:instruction ;) => `([instruction| $i])
      | _ => Lean.Macro.throwUnsupported
    `([$is,*])

/-! ### Parsing -/

example : [program|
    pushq %rax
    popq %rbx
    retq] = [.push .rax, .pop .rbx, .ret] := rfl
example : [program| pushq %rax; popq %rbx; retq] = [.push .rax, .pop .rbx, .ret] := rfl

/-! The operand of `pushq` must be on its line; that of `popq` (no `lineEq`) need not. GAS
rejects both (a line break ends a statement). -/

/-- error: <input>:2:0: expected checkLineEq -/
#guard_msgs in #eval show Lean.Elab.Command.CommandElabM Unit from do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `directive "pushq\n%rax" with
  | .ok _ => pure ()
  | .error e => throwError e

example : [program|
    popq
    %rbx] = [.pop .rbx] := rfl

/-- error: <input>:2:0: expected checkLineEq -/
#guard_msgs in #eval show Lean.Elab.Command.CommandElabM Unit from do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `directive "pushq\n%rax;" with
  | .ok _ => pure ()
  | .error e => throwError e

/-! Inside a Lean term, the position is that of the mnemonic too, wherever the entry is. -/

example : Instr :=
  [instruction| pushq %rax]
example : List Instr :=
  [[instruction| pushq %rax],
   [instruction| pushq %rbx]]
-- `[instruction| pushq` and `%rax]` on two lines: "expected checkLineEq" (tested; a parse
-- error, which `#guard_msgs` can't catch).

/-! `notFollowedBy`: one directive per line, unless separated by `;`. -/

/-- error: <input>:1:5: unexpected element; expected ';' -/
#guard_msgs in #eval show Lean.Elab.Command.CommandElabM Unit from do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `directive "retq %rax" with
  | .ok _ => pure ()
  | .error e => throwError e


/-! ### Printing: `lineEq` leaves no node, so the printer is unchanged -/

/-- info: [instruction| pushq %rax] : Instr -/
#guard_msgs in #check Instr.push .rax
