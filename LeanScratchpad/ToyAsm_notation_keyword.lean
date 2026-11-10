/-!
A toy assembly language embedded in Lean. Each instruction is a `notation`, which gives both
parsing and printing from one declaration. Only the `asm{ ... }` block needs more machinery,
because `notation` cannot express repetition.

Argument positions are ordinary Lean terms at `max` precedence: literals, identifiers, or any
Lean expression in parentheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

structure Reg where
  idx : Nat

inductive Instr where
  | label (name : String)
  | mov (dst : Reg) (imm : Nat)
  | add (dst src : Reg)
  | dec (dst : Reg)
  | jnz (cond : Reg) (target : String)
  | halt

structure Program where
  instrs : List Instr

namespace Asm

/-! The notations are `scoped`, so their keywords (`mov`, `add`, ...) are only reserved after
`open Asm`. Instructions have precedence 10 so that one instruction is never parsed as a function
applied to the next. -/

scoped notation:max "%" n:max => Reg.mk n

scoped notation:10 "label " l:max => Instr.label l
scoped notation:10 "mov " r:max ", " n:max => Instr.mov r n
scoped notation:10 "add " d:max ", " s:max => Instr.add d s
scoped notation:10 "dec " r:max => Instr.dec r
scoped notation:10 "jnz " r:max ", " l:max => Instr.jnz r l
scoped notation:10 "halt" => Instr.halt

/-! A block of instructions, each printed on its own line. Without the outer `ppDedent`, the
body including `}` would be indented by two more columns. -/

scoped syntax "asm{" ppDedent(ppIndent((ppLine term)*) ppLine) "}" : term

scoped macro_rules
  | `(asm{ $[$is]* }) => `(Program.mk [$is,*])

@[scoped app_unexpander Program.mk] def unexpandProgram : Lean.PrettyPrinter.Unexpander
  | `($_ [$is,*]) => `(asm{ $[$is]* })
  | _ => throw ()

end Asm

open Asm

/-! ## Examples -/

/--
info: asm{
  mov %0, 0
  mov %1, 6
  mov %2, 7
  label "loop"
  add %0, %2
  dec %1
  jnz %1, "loop"
  halt
} : Program
-/
#guard_msgs in
#check asm{
  mov %0, 0
  mov %1, 6
  mov %2, 7
  label "loop"
  add %0, %2
  dec %1
  jnz %1, "loop"
  halt
}

-- Lean terms in argument positions.
def answer : Nat := 42
def scratch : Reg := ⟨3⟩
def exitLabel : String := "exit"

/--
info: asm{
  mov scratch, answer
  mov %1, (answer + 1)
  jnz %(answer - 40), exitLabel
  halt
} : Program
-/
#guard_msgs in
#check asm{
  mov scratch, answer
  mov %1, (answer + 1)
  jnz %(answer - 40), exitLabel
  halt
}

-- A Lean-defined instruction in the block. The printer conservatively parenthesizes an
-- instruction that is followed by a bare identifier; the result still parses the same way.
def stop : Instr := .halt

/--
info: asm{
  (mov %0, 1)
  stop
  halt
} : Program
-/
#guard_msgs in
#check asm{
  mov %0, 1
  stop
  halt
}

-- Values built without the notation are printed with it too.
/--
info: asm{
  label "start"
  mov %answer, 1
  halt
} : Program
-/
#guard_msgs in
#check Program.mk [.label "start", .mov ⟨answer⟩ 1, .halt]

/-- info: dec %2 : Instr -/
#guard_msgs in
#check Instr.dec ⟨2⟩

/--
info: asm{
} : Program
-/
#guard_msgs in
#check asm{}

-- Ordinary Lean syntax still works with the notations open, e.g. `%` as modulo.
/-- info: 7 % 2 : Nat -/
#guard_msgs in
#check (7 % 2 : Nat)
