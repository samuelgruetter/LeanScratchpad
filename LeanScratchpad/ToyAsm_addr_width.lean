import LeanScratchpad.CatNotation

/-!
Address widths with Kraken's AST shape, declared with the generic `notation ... in c` machinery
of `CatNotation.lean` and nothing else.

As in Kraken, an address expression holds width-less 64-bit registers (`Reg64`), and the address
width is a field of the instruction (`Instr.regular address_size operation`). `0(%eax)` and `0(%rax)` are
the same `AddrExpr`; only the instruction tells them apart.

The syntax has two categories of address expressions, `memoryOperandAddr32` (registers `%eax`, `%ebx`) and
`memoryOperand` (registers `%rax`, `%rbx`). Each instruction form with a memory operand has one rule per
category, and the rule writes the address width into the instruction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

inductive Width | W32 | W64

inductive Reg64 | rax | rbx

structure AddrExpr where
  base : Reg64
  disp : Nat

inductive RegOrMem where
  | reg (r : Reg64)
  | mem (a : AddrExpr)

inductive Operation where
  | inc (dst : RegOrMem)
  | lea (dst : Reg64) (src : AddrExpr)

inductive Instr where
  | regular (address_size : Width) (operation : Operation)

/-! ## Registers

`register32` is declared first and `register64` last, so that `Reg64.rax` prints as `%rax` (of two rules with
the same right-hand side, the printer uses the one declared last). -/

declare_syntax_cat register32
entry_notation "[register32| " r:register32 "]" => r
notation "%eax" in register32 => Reg64.rax
notation "%ebx" in register32 => Reg64.rbx

declare_syntax_cat register64
entry_notation "[register64| " r:register64 "]" => r
notation "%rax" in register64 => Reg64.rax
notation "%rbx" in register64 => Reg64.rbx

/-! ## Address expressions -/

declare_syntax_cat memoryOperandAddr32
entry_notation "[memoryOperandAddr32| " m:memoryOperandAddr32 "]" => m
notation d:num "(" b:register32 ")" in memoryOperandAddr32 => AddrExpr.mk b d
notation "(" b:register32 ")" in memoryOperandAddr32 => AddrExpr.mk b 0

declare_syntax_cat memoryOperand
entry_notation "[memoryOperand| " m:memoryOperand "]" => m
notation d:num "(" b:register64 ")" in memoryOperand => AddrExpr.mk b d
notation "(" b:register64 ")" in memoryOperand => AddrExpr.mk b 0

/-! ## Instructions -/

declare_syntax_cat instruction (behavior := both)
entry_notation "[instruction| " i:instruction "]" => i

notation "incq " r:register64 in instruction => Instr.regular Width.W64 (Operation.inc (RegOrMem.reg r))
notation "incq " m:memoryOperandAddr32 in instruction => Instr.regular Width.W32 (Operation.inc (RegOrMem.mem m))
notation "incq " m:memoryOperand in instruction => Instr.regular Width.W64 (Operation.inc (RegOrMem.mem m))
notation "leaq " m:memoryOperandAddr32 ", " d:register64 in instruction => Instr.regular Width.W32 (Operation.lea d m)
notation "leaq " m:memoryOperand ", " d:register64 in instruction => Instr.regular Width.W64 (Operation.lea d m)

/-! ## Parsing works

The register names decide the category, and the category decides the address width. -/

example : [instruction| incq (%eax)] = .regular .W32 (.inc (.mem ⟨.rax, 0⟩)) := rfl
example : [instruction| incq (%rax)] = .regular .W64 (.inc (.mem ⟨.rax, 0⟩)) := rfl
example : [instruction| leaq 8(%ebx), %rax] = .regular .W32 (.lea .rax ⟨.rbx, 8⟩) := rfl
example : [instruction| incq %rbx] = .regular .W64 (.inc (.reg .rbx)) := rfl

-- Base registers of the wrong category are rejected.
/-- error: <input>:1:1: expected register64 -/
#guard_msgs in #eval show Lean.Elab.Command.CommandElabM Unit from do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `memoryOperand "(%eax)" with
  | .ok _ => pure ()
  | .error e => throwError e

/-! ## Printing works for 64-bit addresses only -/

/-- info: [instruction| incq (%rax)] : Instr -/
#guard_msgs in #check [instruction| incq (%rax)]

/-- info: [instruction| leaq 8(%rbx), %rax] : Instr -/
#guard_msgs in #check [instruction| leaq 8(%rbx), %rax]

/-- info: [instruction| incq %rbx] : Instr -/
#guard_msgs in #check [instruction| incq %rbx]

/-! A 32-bit address can't be printed. Printing works bottom-up: the arguments of `Instr.regular`
are printed before its own rules are tried. By then the `AddrExpr` has been printed without the
instruction's context, as `[memoryOperand| (%rax)]` (the only spelling of `Reg64.rax` is `%rax`, see
above). The `memoryOperandAddr32` rule of `incq` needs a `memoryOperandAddr32` at that position, so no rule matches, and the
instruction is printed as a Lean term. -/

/-- info: Instr.regular Width.W32 (Operation.inc (RegOrMem.mem [memoryOperand| (%rax)])) : Instr -/
#guard_msgs in #check [instruction| incq (%eax)]

/-- info: Instr.regular Width.W32 (Operation.lea [register64| %rax] ([memoryOperand| 8(%rbx)])) : Instr -/
#guard_msgs in #check [instruction| leaq 8(%ebx), %rax]

-- Out of context, an address prints as a 64-bit address, whichever syntax it was written in.
/-- info: [memoryOperand| (%rax)] : AddrExpr -/
#guard_msgs in #check [memoryOperandAddr32| (%eax)]
