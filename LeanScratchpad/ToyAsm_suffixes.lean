import LeanScratchpad.CatNotation

/-!
The toy assembly language of `ToyAsm_custom_notation.lean`, with operand-width suffixes on the
mnemonics (`movb`, `movw`, `movl`, `movq`), declared with the generic `notation ... in c` machinery
of `CatNotation.lean` and nothing else.

A suffixed mnemonic is a single identifier token (`movq`): Lean tokenizes the input before any rule
runs, taking the longest token, so `"mov" noWs w:width` can never see a `mov` followed by a `q`.
Each width of a mnemonic is therefore its own rule, with the width written out in the right-hand
side. This costs a few lines per mnemonic but needs no extra machinery, and each line can be
checked on its own.
-/

/-! ## The assembly language -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

structure Reg where
  idx : Nat

inductive Width | W8 | W16 | W32 | W64

inductive Instr where
  | label (name : String)
  | mov (w : Width) (dst : Reg) (imm : Nat)
  | add (w : Width) (dst src : Reg)
  | dec (w : Width) (dst : Reg)
  | bswap (w : Width) (dst : Reg)
  | jnz (cond : Reg) (target : String)
  | halt

declare_syntax_cat register
entry_notation "[register| " r:register "]" => r
escape_notation "❰" e:term "❱" in register => e
notation "%" n:num in register => Reg.mk n

declare_syntax_cat immediate
escape_notation "❰" e:term "❱" in immediate => e
notation n:num in immediate => n

declare_syntax_cat label
escape_notation "❰" e:term "❱" in label => e
notation l:ident in label => ident_str% l

-- `behavior := both` makes the first token of each rule a non-reserved keyword: `movq`, `add`, ...
-- stay usable as Lean identifiers, and an instruction starting with an identifier is tried both
-- as a label and as a keyword rule.
declare_syntax_cat instruction (behavior := both)
entry_notation "[instruction| " i:instruction "]" => i
escape_notation "❰" e:term "❱" in instruction => e

notation l:label ":" in instruction => Instr.label l
notation "movb " r:register ", " i:immediate in instruction => Instr.mov Width.W8 r i
notation "movw " r:register ", " i:immediate in instruction => Instr.mov Width.W16 r i
notation "movl " r:register ", " i:immediate in instruction => Instr.mov Width.W32 r i
notation "movq " r:register ", " i:immediate in instruction => Instr.mov Width.W64 r i
notation "addb " d:register ", " s:register in instruction => Instr.add Width.W8 d s
notation "addw " d:register ", " s:register in instruction => Instr.add Width.W16 d s
notation "addl " d:register ", " s:register in instruction => Instr.add Width.W32 d s
notation "addq " d:register ", " s:register in instruction => Instr.add Width.W64 d s
notation "decb " r:register in instruction => Instr.dec Width.W8 r
notation "decw " r:register in instruction => Instr.dec Width.W16 r
notation "decl " r:register in instruction => Instr.dec Width.W32 r
notation "decq " r:register in instruction => Instr.dec Width.W64 r
-- Byte swaps only exist for 32 and 64 bits.
notation "bswapl " r:register in instruction => Instr.bswap Width.W32 r
notation "bswapq " r:register in instruction => Instr.bswap Width.W64 r
notation "jnz " r:register ", " l:label in instruction => Instr.jnz r l
notation "halt" in instruction => Instr.halt

/-! A program is a non-empty `List Instr`, written `[asm| ... ]` with one instruction per line,
defined directly as in `ToyAsm_custom_notation.lean`. -/

syntax "[asm|" ppDedent(ppIndent((ppLine instruction)+) ppLine) "]" : term

macro_rules
  | `([asm| $is*]) => `(([$[[instruction| $is]],*] : List Instr))

open Lean PrettyPrinter Delaborator SubExpr in
/-- The elements of a list literal `[a, ..., z]`, each shown as an instruction. -/
partial def delabInstrs : DelabM (Array (TSyntax `instruction)) := do
  let e ← getExpr
  if e.isAppOfArity ``List.nil 1 then return #[]
  guard (e.isAppOfArity ``List.cons 3)
  let some i := CatNotation.toCat `instruction none none (some instruction.escape.mk)
      (← withNaryArg 1 delab) | failure
  return #[⟨i⟩] ++ (← withNaryArg 2 delabInstrs)

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.List.cons] def delabAsm : Delab := do
  let e ← getExpr
  guard (e.isAppOfArity ``List.cons 3 && e.appFn!.appFn!.appArg!.isConstOf ``Instr)
  let is ← delabInstrs
  `([asm| $[$is]*])

/-! ## Single instructions -/

/-- info: [instruction| loop:] : Instr -/
#guard_msgs in #check [instruction| loop:]

/-- info: [instruction| movq %0, 1] : Instr -/
#guard_msgs in #check [instruction| movq %0, 1]

/-- info: [instruction| movb %0, 1] : Instr -/
#guard_msgs in #check [instruction| movb %0, 1]

/-- info: [instruction| addl %0, %2] : Instr -/
#guard_msgs in #check [instruction| addl %0, %2]

/-- info: [instruction| decw %1] : Instr -/
#guard_msgs in #check [instruction| decw %1]

/-- info: [instruction| bswapq %1] : Instr -/
#guard_msgs in #check [instruction| bswapq %1]

/-- info: [instruction| jnz %1, loop] : Instr -/
#guard_msgs in #check [instruction| jnz %1, loop]

/-- info: [instruction| halt] : Instr -/
#guard_msgs in #check [instruction| halt]

-- The suffix denotes the width.
example : [instruction| movw %0, 1] = Instr.mov .W16 ⟨0⟩ 1 := rfl
example : [instruction| bswapl %3] = Instr.bswap .W32 ⟨3⟩ := rfl

-- Unsuffixed mnemonics, and widths a mnemonic does not have, are not instructions.
/-- error: <input>:1:4: expected ':' -/
#guard_msgs in #eval show Lean.Elab.Command.CommandElabM Unit from do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `instruction "mov %0, 1" with
  | .ok _ => pure ()
  | .error e => throwError e

/-- error: <input>:1:7: expected ':' -/
#guard_msgs in #eval show Lean.Elab.Command.CommandElabM Unit from do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `instruction "bswapb %1" with
  | .ok _ => pure ()
  | .error e => throwError e

-- Escapes back to Lean in every operand position, and for a whole instruction.
def scratch : Reg := ⟨3⟩
def answer : Nat := 42
def exitLabel : String := "exit"
def stop : Instr := .halt

/-- info: [instruction| movq ❰scratch❱, ❰answer + 1❱] : Instr -/
#guard_msgs in #check [instruction| movq ❰scratch❱, ❰answer + 1❱]

/-- info: [instruction| jnz ❰scratch❱, ❰exitLabel❱] : Instr -/
#guard_msgs in #check [instruction| jnz ❰scratch❱, ❰exitLabel❱]

/-- info: stop : Instr -/
#guard_msgs in #check [instruction| ❰stop❱]

-- Instructions built without the syntax are printed in it too.
/-- info: [instruction| movq %0, 1] : Instr -/
#guard_msgs in #check Instr.mov .W64 ⟨0⟩ 1

/-- info: [instruction| jnz ❰{ idx := answer }❱, done] : Instr -/
#guard_msgs in #check Instr.jnz ⟨answer⟩ "done"

-- A width that is not a value has no rule, so the instruction is printed as a Lean term (its
-- operands are still printed in their categories).
/-- info: fun w => Instr.dec w ([register| %1]) : Width → Instr -/
#guard_msgs in #check fun w => Instr.dec w ⟨1⟩

-- `bswap` has no 8-bit form, so a byte swap of width 8 is printed as a Lean term.
/-- info: Instr.bswap Width.W8 ([register| %1]) : Instr -/
#guard_msgs in #check Instr.bswap .W8 ⟨1⟩

/-! ## Programs (non-empty `List Instr`) -/

/--
info: [asm|
  movq %0, 0
  movq %1, 6
  movq %2, 7
  loop:
  addq %0, %2
  decq %1
  jnz %1, loop
  halt
] : List Instr
-/
#guard_msgs in
#check [asm|
  movq %0, 0
  movq %1, 6
  movq %2, 7
  loop:
  addq %0, %2
  decq %1
  jnz %1, loop
  halt
]

/--
info: [asm|
  movl ❰scratch❱, ❰answer❱
  ❰stop❱
] : List Instr
-/
#guard_msgs in
#check [asm|
  movl ❰scratch❱, ❰answer❱
  ❰stop❱
]

-- Lists built without the syntax are printed with it too.
/--
info: [asm|
  start:
  jnz %0, start
] : List Instr
-/
#guard_msgs in
#check ([.label "start", .jnz ⟨0⟩ "start"] : List Instr)

/--
info: [asm|
  halt
] : List Instr
-/
#guard_msgs in
#check [Instr.halt]

-- The empty list, lists of other types, and lists with an unknown tail are printed as usual.
/-- info: [] : List Instr -/
#guard_msgs in #check ([] : List Instr)

/-- info: [1, 2] : List Nat -/
#guard_msgs in #check [1, 2]

/-- info: fun rest => [instruction| halt] :: rest : List Instr → List Instr -/
#guard_msgs in #check fun (rest : List Instr) => Instr.halt :: rest

-- `[asm| ]` is not a way to write the empty list.
/-- error: <input>:1:6: expected label -/
#guard_msgs in #eval show Lean.Elab.Command.CommandElabM Unit from do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `term "[asm| ]" with
  | .ok _ => pure ()
  | .error e => throwError e

/-! ## Other concrete syntax for switching categories

Nothing about `[c| ... ]` or `❰e❱` is built in: conditions are entered with `⟦cond| ... ⟧`, and
have no escape back to Lean. -/

inductive Cond where
  | zero
  | nonzero (r : Reg)
  | not (c : Cond)

declare_syntax_cat cond
entry_notation "⟦cond| " c:cond "⟧" => c
notation "=0" in cond => Cond.zero
notation "≠0 " r:register in cond => Cond.nonzero r
notation "¬ " c:cond in cond => Cond.not c

def always : Cond := .not .zero

/-- info: ⟦cond| ¬ ≠0 %2⟧ : Cond -/
#guard_msgs in #check ⟦cond| ¬ ≠0 %2⟧

-- `always` would need an escape, which `cond` does not have.
/-- info: always.not : Cond -/
#guard_msgs in #check Cond.not always

/-- info: ⟦cond| ≠0 ❰scratch❱⟧ : Cond -/
#guard_msgs in #check ⟦cond| ≠0 ❰scratch❱⟧

/-! ## Printers for other right-hand sides

As with `notation`, a rule gets a printer if its right-hand side applies a constant to arguments
that contain each variable at most once. -/

notation "clrl " r:register in instruction => Instr.mov Width.W32 r 0
notation "dblb " r:register in instruction => Instr.add Width.W8 r r

/-- info: [instruction| clrl %1] : Instr -/
#guard_msgs in #check Instr.mov .W32 ⟨1⟩ 0

/-- info: [instruction| movl %1, 2] : Instr -/
#guard_msgs in #check Instr.mov .W32 ⟨1⟩ 2

-- `dbl` uses its variable twice, so it has no printer and `add` is used instead.
/-- info: [instruction| addb %1, %1] : Instr -/
#guard_msgs in #check [instruction| dblb %1]

/-! ## Rejected rules -/

/-- error: variable `r` does not occur on the right-hand side -/
#guard_msgs in notation "nop " r:register in instruction => Instr.halt

/--
error: a notation that switches categories must be an `entry_notation` or an `escape_notation`
-/
#guard_msgs in notation "(" r:register ")" in instruction => r

/-- error: an `entry_notation` must switch into a custom category -/
#guard_msgs in entry_notation "<<" e:term ">>" => e

/-- error: an `escape_notation` must switch to `term` -/
#guard_msgs in escape_notation "<<" r:register ">>" in instruction => r

/-- error: the right-hand side of an `escape_notation` must be a variable -/
#guard_msgs in escape_notation "<<" e:term ">>" in register => Reg.mk e

-- A second `entry_notation` or `escape_notation` would make printing ambiguous.
/-- error: there already is an `escape_notation` for `register` -/
#guard_msgs in escape_notation "<<" e:term ">>" in register => e

/-- error: there already is an `entry_notation` for `cond` -/
#guard_msgs in entry_notation "⦃" c:cond "⦄" => c

/-! ## Lean's `notation` is unaffected -/

def pairUp (a b : Nat) : Nat × Nat := (a, b)
def double (n : Nat) : Nat := 2 * n

notation "⟪pair " a ", " b "⟫" => pairUp a b
local notation:max "dbl " n:max => double n

/-- info: ⟪pair 1, 2⟫ : Nat × Nat -/
#guard_msgs in #check pairUp 1 2

/-- info: dbl 3 : Nat -/
#guard_msgs in #check double 3

-- Lean's own syntax is unaffected; mnemonics with suffixes and suffixes alone stay identifiers.
def movq (addb : Nat) : Nat := addb + 1
def q (b : Nat) : Nat := b

/-- info: movq (3 % 2) : Nat -/
#guard_msgs in #check movq ((3 : Nat) % 2)

/-- info: q 1 : Nat -/
#guard_msgs in #check q 1

-- `entry` and `escape` are not keywords.
def entry (escape : Nat) : Nat := escape

/-- info: entry 1 : Nat -/
#guard_msgs in #check entry 1

/-! ## A category without an escape back to Lean

`aexp` has a rule to switch from `term` into it, but none to switch back. Expressions that
consist only of `aexp` notations are still printed with them; an expression that contains a
foreign Lean term is printed as an ordinary Lean term. -/

inductive AExp where
  | lit (n : Nat)
  | neg (a : AExp)
  | plus (a b : AExp)

declare_syntax_cat aexp
entry_notation "⟦aexp| " e:aexp "⟧" => e
notation n:num in aexp => AExp.lit n
notation "-" a:aexp in aexp => AExp.neg a
notation "(" a:aexp " + " b:aexp ")" in aexp => AExp.plus a b

/-- info: ⟦aexp| (1 + -(2 + 3))⟧ : AExp -/
#guard_msgs in #check ⟦aexp| (1 + -(2 + 3))⟧

/-- info: ⟦aexp| (1 + -2)⟧ : AExp -/
#guard_msgs in #check AExp.plus (.lit 1) (.neg (.lit 2))

/-- info: fun x => ⟦aexp| 1⟧.plus x : AExp → AExp -/
#guard_msgs in #check fun x => AExp.plus (.lit 1) x

/-- info: AExp.lit answer : AExp -/
#guard_msgs in #check AExp.lit answer
