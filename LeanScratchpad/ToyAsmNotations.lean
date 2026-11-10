/-!
A toy assembly language embedded in Lean.

Assembly lives in its own syntax categories, so it does not mix with Lean's term syntax:
`[asm| ... ]` enters assembly for a whole program, `[instr| ... ]` for a single instruction, and
inside assembly `❰e❱` escapes back to a Lean term `e`. These follow the conventions of Kraken's
`[x64| ... ]`; `$` and `( )` are avoided because real assembly uses them (AT&T immediates and
memory operands), and `$` is also Lean's own antiquotation.

`notation` cannot be used here: it only defines `term` syntax, and labels such as `loop:` need a
category of their own. The language is therefore given by three parallel tables of pattern rules:
the grammar (`syntax`), the translation into `Instr` (`macro_rules`), and the printing back
(`app_unexpander`).
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

/-! ## Grammar -/

declare_syntax_cat asm_reg
declare_syntax_cat asm_imm
declare_syntax_cat asm_label
-- `behavior := both`: an instruction starting with an identifier may also start with a keyword
-- such as `mov`, so the keyword rules are tried as well, not only the label rule.
declare_syntax_cat asm_instr (behavior := both)

syntax "%" num : asm_reg
syntax num : asm_imm
syntax ident : asm_label

-- `&"mov"` etc. are non-reserved keywords, so `mov`, `add`, ... stay usable as Lean identifiers.
syntax ident ":" : asm_instr
syntax &"mov " asm_reg ", " asm_imm : asm_instr
syntax &"add " asm_reg ", " asm_reg : asm_instr
syntax &"dec " asm_reg : asm_instr
syntax &"jnz " asm_reg ", " asm_label : asm_instr
syntax &"halt" : asm_instr

-- escapes back to Lean
syntax "❰" term "❱" : asm_reg
syntax "❰" term "❱" : asm_imm
syntax "❰" term "❱" : asm_label
syntax "❰" term "❱" : asm_instr

-- entering assembly; in a program each instruction is printed on its own line
syntax "[asm|" ppDedent(ppIndent((ppLine asm_instr)*) ppLine) "]" : term
syntax "[instr| " asm_instr "]" : term
syntax "[reg| " asm_reg "]" : term
syntax "[imm| " asm_imm "]" : term
syntax "[label| " asm_label "]" : term

/-! ## Translation into `Instr` -/

macro_rules
  | `([reg| % $n:num]) => `(Reg.mk $n)
  | `([imm| $n:num]) => `(($n : Nat))
  -- labels are strings in the AST, not Lean binders, so macro scopes are dropped
  | `([label| $l:ident]) => `($(Lean.quote (l.getId.eraseMacroScopes.toString (escape := false))))
  | `([reg| ❰$e❱]) => `(($e : Reg))
  | `([imm| ❰$e❱]) => `(($e : Nat))
  | `([label| ❰$e❱]) => `(($e : String))

macro_rules
  | `([instr| $l:ident :]) => `(Instr.label [label| $l:ident])
  | `([instr| mov $r, $i]) => `(Instr.mov [reg| $r] [imm| $i])
  | `([instr| add $d, $s]) => `(Instr.add [reg| $d] [reg| $s])
  | `([instr| dec $r]) => `(Instr.dec [reg| $r])
  | `([instr| jnz $r, $l]) => `(Instr.jnz [reg| $r] [label| $l])
  | `([instr| halt]) => `(Instr.halt)
  | `([instr| ❰$e❱]) => `(($e : Instr))

macro_rules
  | `([asm| $is*]) => `(Program.mk [$[[instr| $is]],*])

/-! ## Printing

An unexpander sees its arguments already printed as Lean terms. These helpers turn such a term
back into an operand: the assembly form if it is a literal, the `❰e❱` escape otherwise. -/

namespace Asm
open Lean PrettyPrinter

def reg : Term → UnexpandM (TSyntax `asm_reg)
  | `([reg| $r]) => pure r
  | e => `(asm_reg| ❰$e❱)

def imm : Term → UnexpandM (TSyntax `asm_imm)
  | `($n:num) => `(asm_imm| $n:num)
  | e => `(asm_imm| ❰$e❱)

def labelIdent (s : StrLit) : Ident := mkIdent (Name.mkSimple s.getString)

def label : Term → UnexpandM (TSyntax `asm_label)
  | `($s:str) => `(asm_label| $(labelIdent s):ident)
  | e => `(asm_label| ❰$e❱)

def instr : Term → UnexpandM (TSyntax `asm_instr)
  | `([instr| $i]) => pure i
  | e => `(asm_instr| ❰$e❱)

end Asm

@[app_unexpander Reg.mk] def unexpandReg : Lean.PrettyPrinter.Unexpander
  | `($_ $n:num) => `([reg| % $n])
  | _ => throw ()

@[app_unexpander Instr.label] def unexpandLabel : Lean.PrettyPrinter.Unexpander
  | `($_ $s:str) => `([instr| $(Asm.labelIdent s):ident :])
  | _ => throw ()

@[app_unexpander Instr.mov] def unexpandMov : Lean.PrettyPrinter.Unexpander
  | `($_ $r $i) => do `([instr| mov $(← Asm.reg r), $(← Asm.imm i)])
  | _ => throw ()

@[app_unexpander Instr.add] def unexpandAdd : Lean.PrettyPrinter.Unexpander
  | `($_ $d $s) => do `([instr| add $(← Asm.reg d), $(← Asm.reg s)])
  | _ => throw ()

@[app_unexpander Instr.dec] def unexpandDec : Lean.PrettyPrinter.Unexpander
  | `($_ $r) => do `([instr| dec $(← Asm.reg r)])
  | _ => throw ()

@[app_unexpander Instr.jnz] def unexpandJnz : Lean.PrettyPrinter.Unexpander
  | `($_ $r $l) => do `([instr| jnz $(← Asm.reg r), $(← Asm.label l)])
  | _ => throw ()

-- `Instr.halt` has no arguments, so the pattern is just the head constant.
@[app_unexpander Instr.halt] def unexpandHalt : Lean.PrettyPrinter.Unexpander
  | `($_) => `([instr| halt])

@[app_unexpander Program.mk] def unexpandProgram : Lean.PrettyPrinter.Unexpander
  | `($_ [$is,*]) => do `([asm| $(← is.getElems.mapM Asm.instr)*])
  | _ => throw ()

/-! ## Single instructions -/

/-- info: [instr| loop:] : Instr -/
#guard_msgs in #check [instr| loop:]

/-- info: [instr| mov %0, 1] : Instr -/
#guard_msgs in #check [instr| mov %0, 1]

/-- info: [instr| add %0, %2] : Instr -/
#guard_msgs in #check [instr| add %0, %2]

/-- info: [instr| dec %1] : Instr -/
#guard_msgs in #check [instr| dec %1]

/-- info: [instr| jnz %1, loop] : Instr -/
#guard_msgs in #check [instr| jnz %1, loop]

/-- info: [instr| halt] : Instr -/
#guard_msgs in #check [instr| halt]

-- Escapes back to Lean in every operand position, and for a whole instruction.
def scratch : Reg := ⟨3⟩
def answer : Nat := 42
def exitLabel : String := "exit"
def stop : Instr := .halt

/-- info: [instr| mov ❰scratch❱, ❰answer + 1❱] : Instr -/
#guard_msgs in #check [instr| mov ❰scratch❱, ❰answer + 1❱]

/-- info: [instr| jnz ❰scratch❱, ❰exitLabel❱] : Instr -/
#guard_msgs in #check [instr| jnz ❰scratch❱, ❰exitLabel❱]

/-- info: stop : Instr -/
#guard_msgs in #check [instr| ❰stop❱]

-- Instructions built without the syntax are printed in it too.
/-- info: [instr| mov %0, 1] : Instr -/
#guard_msgs in #check Instr.mov ⟨0⟩ 1

/-- info: [instr| jnz ❰Reg.mk answer❱, done] : Instr -/
#guard_msgs in #check Instr.jnz ⟨answer⟩ "done"

/-! ## Programs -/

/--
info: [asm|
  mov %0, 0
  mov %1, 6
  mov %2, 7
  loop:
  add %0, %2
  dec %1
  jnz %1, loop
  halt
] : Program
-/
#guard_msgs in
#check [asm|
  mov %0, 0
  mov %1, 6
  mov %2, 7
  loop:
  add %0, %2
  dec %1
  jnz %1, loop
  halt
]

/--
info: [asm|
  mov ❰scratch❱, ❰answer❱
  ❰stop❱
] : Program
-/
#guard_msgs in
#check [asm|
  mov ❰scratch❱, ❰answer❱
  ❰stop❱
]

/--
info: [asm|
  start:
  jnz %0, start
] : Program
-/
#guard_msgs in
#check Program.mk [.label "start", .jnz ⟨0⟩ "start"]

/--
info: [asm|
] : Program
-/
#guard_msgs in
#check [asm|]

-- Lean's own syntax is unaffected.
def mov (add : Nat) : Nat := add + 1

/-- info: mov (3 % 2) : Nat -/
#guard_msgs in #check mov ((3 : Nat) % 2)
