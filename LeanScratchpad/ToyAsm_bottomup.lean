import LeanScratchpad.CatNotation

/-! Issue 8 without typed categories: plain bottom-up printing, one operand category per width,
suffixed rules only (unsuffixed ones would be parse-only).

A register shows its width in the term (`Reg.al`). `RegOrMem.mem` and `Operand.imm` don't: their
width is an implicit argument. Their rules therefore write it with `@` (`@RegOrMem.mem Width.W8 m`).
For such a rule, `notation ... in c` prints the application with its implicit arguments and
matches the width too, so each of these operands prints in the category of its own width. That is
all: the instruction rules are plain, and each finds its operands in the categories of its width.
The `@` also fixes parsing of `movzbl (%rax), %eax`: the source width of `movzx` is implicit, and
without `@` nothing would set it for a memory source. -/

set_option autoImplicit false

inductive Width | W8 | W16 | W32 | W64
inductive Reg : Width → Type | al : Reg .W8 | ax : Reg .W16 | eax : Reg .W32 | rax : Reg .W64
structure AddrExpr where
  base : Reg .W64
inductive RegOrMem (w : Width) | reg (r : Reg w) | mem (a : AddrExpr)
inductive Operand (w : Width) | regOrMem (x : RegOrMem w) | imm (v : Nat)
inductive Operation (w : Width)
  | inc (dst : RegOrMem w)
  | add (dst : RegOrMem w) (src : Operand w)
  | movzx {w'} (dst : Reg w) (src : RegOrMem w')
inductive Instr | regular (operation_size : Width) (op : Operation operation_size)

declare_syntax_cat register8
entry_notation "[register8| " r:register8 "]" => r
notation "%al" in register8 => Reg.al
declare_syntax_cat register16
entry_notation "[register16| " r:register16 "]" => r
notation "%ax" in register16 => Reg.ax
declare_syntax_cat register32
entry_notation "[register32| " r:register32 "]" => r
notation "%eax" in register32 => Reg.eax
declare_syntax_cat register64
entry_notation "[register64| " r:register64 "]" => r
notation "%rax" in register64 => Reg.rax

declare_syntax_cat memoryOperand
entry_notation "[memoryOperand| " m:memoryOperand "]" => m
notation "(" b:register64 ")" in memoryOperand => AddrExpr.mk b

declare_syntax_cat registerOrMemory8
entry_notation "[registerOrMemory8| " x:registerOrMemory8 "]" => x
notation r:register8 in registerOrMemory8 => RegOrMem.reg r
notation m:memoryOperand in registerOrMemory8 => @RegOrMem.mem Width.W8 m
declare_syntax_cat registerOrMemory16
entry_notation "[registerOrMemory16| " x:registerOrMemory16 "]" => x
notation r:register16 in registerOrMemory16 => RegOrMem.reg r
notation m:memoryOperand in registerOrMemory16 => @RegOrMem.mem Width.W16 m
declare_syntax_cat registerOrMemory32
entry_notation "[registerOrMemory32| " x:registerOrMemory32 "]" => x
notation r:register32 in registerOrMemory32 => RegOrMem.reg r
notation m:memoryOperand in registerOrMemory32 => @RegOrMem.mem Width.W32 m
declare_syntax_cat registerOrMemory64
entry_notation "[registerOrMemory64| " x:registerOrMemory64 "]" => x
notation r:register64 in registerOrMemory64 => RegOrMem.reg r
notation m:memoryOperand in registerOrMemory64 => @RegOrMem.mem Width.W64 m

declare_syntax_cat operand8
entry_notation "[operand8| " x:operand8 "]" => x
notation x:registerOrMemory8 in operand8 => Operand.regOrMem x
notation "$" n:num in operand8 => @Operand.imm Width.W8 n
declare_syntax_cat operand64
entry_notation "[operand64| " x:operand64 "]" => x
notation x:registerOrMemory64 in operand64 => Operand.regOrMem x
notation "$" n:num in operand64 => @Operand.imm Width.W64 n

declare_syntax_cat operation8 (behavior := both)
entry_notation "[operation8| " o:operation8 "]" => o
notation "incb " x:registerOrMemory8 in operation8 => Operation.inc x
notation "addb " s:operand8 ", " d:registerOrMemory8 in operation8 => Operation.add d s
declare_syntax_cat operation32 (behavior := both)
entry_notation "[operation32| " o:operation32 "]" => o
notation "movzbl " s:registerOrMemory8 ", " d:register32 in operation32 =>
  Operation.movzx d s
notation "movzwl " s:registerOrMemory16 ", " d:register32 in operation32 =>
  Operation.movzx d s
declare_syntax_cat operation64 (behavior := both)
entry_notation "[operation64| " o:operation64 "]" => o
notation "incq " x:registerOrMemory64 in operation64 => Operation.inc x
notation "addq " s:operand64 ", " d:registerOrMemory64 in operation64 => Operation.add d s

declare_syntax_cat instruction (behavior := both)
entry_notation "[instruction| " i:instruction "]" => i
notation o:operation8 in instruction => Instr.regular Width.W8 o
notation o:operation32 in instruction => Instr.regular Width.W32 o
notation o:operation64 in instruction => Instr.regular Width.W64 o

/-! ### Printing -/
/-- info: [instruction| incb %al] : Instr -/
#guard_msgs in #check [instruction| incb %al]
/-- info: [instruction| incq %rax] : Instr -/
#guard_msgs in #check [instruction| incq %rax]
/-- info: [instruction| movzbl %al, %eax] : Instr -/
#guard_msgs in #check [instruction| movzbl %al, %eax]
/-- info: [instruction| movzwl %ax, %eax] : Instr -/
#guard_msgs in #check [instruction| movzwl %ax, %eax]
-- Operands without a width in the term:
/-- info: [instruction| addb $1, %al] : Instr -/
#guard_msgs in #check [instruction| addb $1, %al]
/-- info: [instruction| incb (%rax)] : Instr -/
#guard_msgs in #check [instruction| incb (%rax)]
/-- info: [instruction| incq (%rax)] : Instr -/
#guard_msgs in #check [instruction| incq (%rax)]
/-- info: [instruction| addb $1, (%rax)] : Instr -/
#guard_msgs in #check [instruction| addb $1, (%rax)]
/-- info: [instruction| addq $1, (%rax)] : Instr -/
#guard_msgs in #check [instruction| addq $1, (%rax)]
/-- info: [instruction| movzbl (%rax), %eax] : Instr -/
#guard_msgs in #check [instruction| movzbl (%rax), %eax]
/-- info: [instruction| movzwl (%rax), %eax] : Instr -/
#guard_msgs in #check [instruction| movzwl (%rax), %eax]

/-! ### Parsing sets the source width of `movzx` -/
def b : Instr := [instruction| movzbl (%rax), %eax]

/--
info: def b : Instr :=
Instr.regular Width.W32 (@Operation.movzx Width.W32 Width.W8 Reg.eax (@RegOrMem.mem Width.W8 { base := Reg.rax }))
-/
#guard_msgs in
set_option pp.explicit true in
set_option pp.notation false in
#print b

/-! Without the `@` (`notation m:memoryOperand in registerOrMemory8 => RegOrMem.mem m`, tested):
`def b` fails with "don't know how to synthesize implicit argument `w'`"; `addb $1, %al`,
`incb (%rax)`, `addb $1, (%rax)` and `movzbl (%rax), %eax` print as Lean terms, because each
width-less operand printed with the rule declared last (64 bits). -/

/-! ### Like `notation`: constants are matched by name, and named arguments get no printer -/
namespace Ns
inductive W | b | q
inductive Imm (w : W) | imm (n : Nat)
declare_syntax_cat immByte
entry_notation "[immByte| " x:immByte "]" => x
notation "$" n:num "b" in immByte => @Imm.imm W.b n
declare_syntax_cat immQuad
entry_notation "[immQuad| " x:immQuad "]" => x
notation "$" n:num "q" in immQuad => Imm.imm (w := W.q) n

/-- info: [immByte| $1b] : Imm W.b -/
#guard_msgs in #check (Imm.imm 1 : Imm .b)
-- Parses, but has no printer.
example : Imm .q := [immQuad| $1q]
/-- info: Imm.imm 1 : Imm W.q -/
#guard_msgs in #check (Imm.imm 1 : Imm .q)
end Ns

-- Outside the namespace, `W.b` prints as `Ns.W.b` and the rule doesn't match.
/-- info: Ns.Imm.imm 1 : Ns.Imm Ns.W.b -/
#guard_msgs in #check (Ns.Imm.imm 1 : Ns.Imm .b)
open Ns in
/-- info: [immByte| $1b] : Imm W.b -/
#guard_msgs in #check (Imm.imm 1 : Imm .b)
