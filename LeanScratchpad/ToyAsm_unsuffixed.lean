import LeanScratchpad.CatNotation

/-!
Unsuffixed mnemonics (`inc %eax`, `inc (%rax)`), done the straightforward way: one more rule per
width, in the operation category of that width, as in Kraken's AST (`Operation w`).
-/

set_option autoImplicit false

inductive Width | W8 | W32 | W64
inductive Reg : Width → Type | al : Reg .W8 | eax : Reg .W32 | rax : Reg .W64
structure AddrExpr where
  base : Reg .W64
inductive RegOrMem (w : Width) | reg (r : Reg w) | mem (a : AddrExpr)
inductive Operation (w : Width)
  | inc (dst : RegOrMem w)
inductive Instr | regular (operation_size : Width) (operation : Operation operation_size)

declare_syntax_cat register8
entry_notation "[register8| " r:register8 "]" => r
notation "%al" in register8 => Reg.al
declare_syntax_cat register32
entry_notation "[register32| " r:register32 "]" => r
notation "%eax" in register32 => Reg.eax
declare_syntax_cat register64
entry_notation "[register64| " r:register64 "]" => r
notation "%rax" in register64 => Reg.rax

declare_syntax_cat memoryOperand
entry_notation "[memoryOperand| " m:memoryOperand "]" => m
notation "(" b:register64 ")" in memoryOperand => AddrExpr.mk b

-- One `registerOrMemory` category per width (issue 8). `RegOrMem.mem m` has no width of its own,
-- so the rule states it, and only prints memory operands of that width.
declare_syntax_cat registerOrMemory8
entry_notation "[registerOrMemory8| " x:registerOrMemory8 "]" => x
notation r:register8 in registerOrMemory8 => RegOrMem.reg r
notation m:memoryOperand in registerOrMemory8 => @RegOrMem.mem Width.W8 m
declare_syntax_cat registerOrMemory32
entry_notation "[registerOrMemory32| " x:registerOrMemory32 "]" => x
notation r:register32 in registerOrMemory32 => RegOrMem.reg r
notation m:memoryOperand in registerOrMemory32 => @RegOrMem.mem Width.W32 m
declare_syntax_cat registerOrMemory64
entry_notation "[registerOrMemory64| " x:registerOrMemory64 "]" => x
notation r:register64 in registerOrMemory64 => RegOrMem.reg r
notation m:memoryOperand in registerOrMemory64 => @RegOrMem.mem Width.W64 m

/-! Each operation category has the unsuffixed rule (the suffixed line without the suffix),
marked `(print := false)`: it only parses, so the suffixed rule prints, although the unsuffixed
one is declared last. Without the marker, the printer tries the rule declared last first, and
`incq (%rax)` printed as `inc (%rax)`, which doesn't read back, and which GAS would read as
`incl` (tested). -/

declare_syntax_cat operation8 (behavior := both)
entry_notation "[operation8| " o:operation8 "]" => o
notation "incb " x:registerOrMemory8 in operation8 => Operation.inc x
notation (print := false) "inc " x:registerOrMemory8 in operation8 => Operation.inc x
declare_syntax_cat operation32 (behavior := both)
entry_notation "[operation32| " o:operation32 "]" => o
notation "incl " x:registerOrMemory32 in operation32 => Operation.inc x
notation (print := false) "inc " x:registerOrMemory32 in operation32 => Operation.inc x
declare_syntax_cat operation64 (behavior := both)
entry_notation "[operation64| " o:operation64 "]" => o
notation "incq " x:registerOrMemory64 in operation64 => Operation.inc x
notation (print := false) "inc " x:registerOrMemory64 in operation64 => Operation.inc x


declare_syntax_cat instruction (behavior := both)
entry_notation "[instruction| " i:instruction "]" => i
notation o:operation8 in instruction => Instr.regular Width.W8 o
notation o:operation32 in instruction => Instr.regular Width.W32 o
notation o:operation64 in instruction => Instr.regular Width.W64 o

/-! ### Parsing

The register decides the width: `inc %al` parses as `operation8`, `operation32` and `operation64`, and only the `operation8`
reading type-checks. With a lone address, all three type-check, and Lean rejects the input. -/
example : [instruction| inc %al] = .regular .W8 (.inc (.reg .al)) := rfl
example : [instruction| inc %rax] = .regular .W64 (.inc (.reg .rax)) := rfl

/--
error: Ambiguous term
  inc (%rax)
Possible interpretations:
  [instruction| incq (%rax)] : Instr
  ⏎
  [instruction| incl (%rax)] : Instr
  ⏎
  [instruction| incb (%rax)] : Instr
-/
#guard_msgs in example := [instruction| inc (%rax)]

/-! A higher priority on one wrapper only (`(priority := high) o:operation64 in instruction`) makes Lean drop
the other parses: `inc (%rax)` then silently reads as 64 bits, and `inc %al` fails to type-check
(tested). So all wrappers of the operation categories must have the same priority. -/

/-! ### Printing

Each operand prints in the category of its width (see the `registerOrMemory` rules), so each
suffixed rule only matches operations of its width. With one `registerOrMemory` category for all
widths, `Operation.inc` hides the width (an implicit argument), and `[instruction| incb %al]`
printed as a Lean term (tested). See Kraken's `X64/Parser/design.md`, issue 8. -/
/-- info: [instruction| incq (%rax)] : Instr -/
#guard_msgs in #check [instruction| incq (%rax)]
/-- info: [instruction| incl %eax] : Instr -/
#guard_msgs in #check [instruction| incl %eax]
/-- info: [instruction| incb %al] : Instr -/
#guard_msgs in #check [instruction| incb %al]
/-- info: [instruction| incb (%rax)] : Instr -/
#guard_msgs in #check [instruction| incb (%rax)]
