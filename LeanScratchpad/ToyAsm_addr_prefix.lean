import LeanScratchpad.CatNotation

/-!
Address widths with Kraken's AST unchanged, printed with an address-size prefix.

As in Kraken (and `ToyAsm_addr_width.lean`), `AddrExpr` holds width-less registers and the address
width is a field of the instruction. Two levels of rules:
* one rule per instruction form in category `operation`, which produces an `Operation`. Address
  expressions are written with 64-bit register names only.
* two wrapper rules in `instruction`, one per address width. The 32-bit one adds a prefix.

The prefix `.byte 0x67;` uses the items `noWs`, `&"..."` and a fixed numeral of
`notation ... in c`. Assemblers emit the same bytes for it as for `(%eax)`.

The last part adds parse-only input with 32-bit register names (`incq (%eax)`), with one more
line per instruction form.
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
  | add (dst src : RegOrMem)
  | lea (dst : Reg64) (src : AddrExpr)

inductive Instr where
  | regular (address_size : Width) (operation : Operation)

declare_syntax_cat register64
entry_notation "[register64| " r:register64 "]" => r
notation "%rax" in register64 => Reg64.rax
notation "%rbx" in register64 => Reg64.rbx

declare_syntax_cat memoryOperand
entry_notation "[memoryOperand| " m:memoryOperand "]" => m
notation d:num "(" b:register64 ")" in memoryOperand => AddrExpr.mk b d
notation "(" b:register64 ")" in memoryOperand => AddrExpr.mk b 0

declare_syntax_cat registerOrMemory
entry_notation "[registerOrMemory| " x:registerOrMemory "]" => x
notation r:register64 in registerOrMemory => RegOrMem.reg r
notation m:memoryOperand in registerOrMemory => RegOrMem.mem m

/-! ## One rule per form, whatever the number of operands that can be memory -/

declare_syntax_cat operation (behavior := both)
entry_notation "[operation| " o:operation "]" => o
notation "incq " x:registerOrMemory in operation => Operation.inc x
notation "addq " s:registerOrMemory ", " d:registerOrMemory in operation => Operation.add d s
notation "leaq " m:memoryOperand ", " d:register64 in operation => Operation.lea d m

/-! ## Two wrappers per operation category -/

declare_syntax_cat instruction (behavior := both)
entry_notation "[instruction| " i:instruction "]" => i
notation (priority := high) o:operation in instruction => Instr.regular Width.W64 o
-- TODO (to discuss with the other developers): this also accepts the prefix on an operation
-- without a memory operand (`.byte 0x67; incq %rax`). The SDM reportedly calls that use of `67h`
-- reserved (Vol. 2, §2.1, to be checked); see Kraken's `X64/Parser/design.md`, issue 1.
notation "." noWs &"byte " 0x67 "; " o:operation in instruction => Instr.regular Width.W32 o

/-! ## Parsing -/

example : [instruction| incq (%rax)] = .regular .W64 (.inc (.mem ⟨.rax, 0⟩)) := rfl
example : [instruction| .byte 0x67; incq (%rax)] = .regular .W32 (.inc (.mem ⟨.rax, 0⟩)) := rfl
example : [instruction| .byte 0x67; leaq 8(%rbx), %rax] = .regular .W32 (.lea .rax ⟨.rbx, 8⟩) := rfl
-- Two memory operands parse (an assembler rejects them; see Kraken's README).
example : [instruction| addq (%rax), 8(%rbx)] =
    .regular .W64 (.add (.mem ⟨.rbx, 8⟩) (.mem ⟨.rax, 0⟩)) := rfl

/-! ## Printing works for both address widths -/

/-- info: [instruction| incq (%rax)] : Instr -/
#guard_msgs in #check [instruction| incq (%rax)]

/-- info: [instruction| .byte 0x67; incq (%rax)] : Instr -/
#guard_msgs in #check [instruction| .byte 0x67; incq (%rax)]

/-- info: [instruction| .byte 0x67; leaq 8(%rbx), %rax] : Instr -/
#guard_msgs in #check [instruction| .byte 0x67; leaq 8(%rbx), %rax]

/-- info: [instruction| .byte 0x67; addq %rax, 8(%rbx)] : Instr -/
#guard_msgs in #check [instruction| .byte 0x67; addq %rax, 8(%rbx)]

/-- info: [instruction| addq (%rax), 8(%rbx)] : Instr -/
#guard_msgs in #check [instruction| addq (%rax), 8(%rbx)]

-- The prefix also prints on an instruction without a memory operand.
/-- info: [instruction| .byte 0x67; incq %rax] : Instr -/
#guard_msgs in #check Instr.regular .W32 (.inc (.reg .rax))

/-! ## Parse-only: 32-bit register names in addresses, one more line per instruction form

The categories below have no `entry_notation`, so `notation ... in c` makes no printer for them
(see `CatNotation.lean`): they are only read. `operationAddr32` repeats each form of `operation` with `registerOrMemoryAddr32` and
`memoryOperandAddr32` (addresses with 32-bit register names) instead of `registerOrMemory` and `memoryOperand`. Its wrapper writes
the 32-bit address size into the instruction, and the instruction prints back with the prefix.

An instruction without addresses (`incq %rax`) reads as both `operation` and `operationAddr32`. The `operation`
wrapper's priority is higher, so it wins and the address size is 64 bits. Without the priority,
Lean reports the input as ambiguous. An instruction mixing 32- and 64-bit names
(`addq (%eax), 8(%rbx)`) reads as neither. -/

declare_syntax_cat register32
notation "%eax" in register32 => Reg64.rax
notation "%ebx" in register32 => Reg64.rbx

declare_syntax_cat memoryOperandAddr32
notation d:num "(" b:register32 ")" in memoryOperandAddr32 => AddrExpr.mk b d
notation "(" b:register32 ")" in memoryOperandAddr32 => AddrExpr.mk b 0

declare_syntax_cat registerOrMemoryAddr32
notation r:register64 in registerOrMemoryAddr32 => RegOrMem.reg r
notation m:memoryOperandAddr32 in registerOrMemoryAddr32 => RegOrMem.mem m

declare_syntax_cat operationAddr32 (behavior := both)
notation "incq " x:registerOrMemoryAddr32 in operationAddr32 => Operation.inc x
notation "addq " s:registerOrMemoryAddr32 ", " d:registerOrMemoryAddr32 in operationAddr32 => Operation.add d s
notation "leaq " m:memoryOperandAddr32 ", " d:register64 in operationAddr32 => Operation.lea d m

notation o:operationAddr32 in instruction => Instr.regular Width.W32 o

example : [instruction| incq (%eax)] = .regular .W32 (.inc (.mem ⟨.rax, 0⟩)) := rfl
example : [instruction| leaq 8(%ebx), %rax] = .regular .W32 (.lea .rax ⟨.rbx, 8⟩) := rfl
example : [instruction| addq %rax, 8(%ebx)] = .regular .W32 (.add (.mem ⟨.rbx, 8⟩) (.reg .rax)) := rfl
example : [instruction| incq %rax] = .regular .W64 (.inc (.reg .rax)) := rfl
example : [instruction| incq (%rax)] = .regular .W64 (.inc (.mem ⟨.rax, 0⟩)) := rfl

-- Printed back with the prefix.
/-- info: [instruction| .byte 0x67; incq (%rax)] : Instr -/
#guard_msgs in #check [instruction| incq (%eax)]

/-- error: <input>:1:15: expected register32 -/
#guard_msgs in #eval show Lean.Elab.Command.CommandElabM Unit from do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `instruction "addq (%eax), 8(%rbx)" with
  | .ok _ => pure ()
  | .error e => throwError e

-- The prefix with 32-bit names doesn't parse: the prefixed wrapper takes an `operation`.
/-- error: <input>:1:18: expected register64 -/
#guard_msgs in #eval show Lean.Elab.Command.CommandElabM Unit from do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `instruction ".byte 0x67; incq (%eax)" with
  | .ok _ => pure ()
  | .error e => throwError e

-- Still accepted: the prefix without a memory operand.
example : [instruction| .byte 0x67; incq %rax] = .regular .W32 (.inc (.reg .rax)) := rfl

/-! ## The items of the prefix

`"." noWs &"byte"`: `.` is already a token and `byte` is read as an identifier, so `.byte` is
not a token, and Lean's own `.byteArray` and `.byte` still work. -/

inductive D | byteArray (n : Nat) | byte
example : D := .byteArray 3
example : D := .byte

-- Only the spelling `0x67` is accepted; other numerals parse but fail with Lean's generic error.
example : [instruction| .byte 0x67; incq (%rax)] = .regular .W32 (.inc (.mem ⟨.rax, 0⟩)) := rfl

/--
error: elaboration function for `«instruction._Byte_;_»` has not been implemented
  .byte 103; incq (%rax)
-/
#guard_msgs in example := [instruction| .byte 103; incq (%rax)]

/--
error: elaboration function for `«instruction._Byte_;_»` has not been implemented
  .byte 0x66; incq (%rax)
-/
#guard_msgs in example := [instruction| .byte 0x66; incq (%rax)]

/-- error: <input>:1:2: expected no space before -/
#guard_msgs in #eval show Lean.Elab.Command.CommandElabM Unit from do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `instruction ". byte 0x67; incq (%rax)" with
  | .ok _ => pure ()
  | .error e => throwError e

-- `byte` is not reserved.
def byte : Nat := 1
