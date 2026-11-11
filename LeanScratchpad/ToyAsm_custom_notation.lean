import Lean

/-!
A toy assembly language embedded in Lean, defined with `notation ... in c`, a variant of Lean's
`notation` for custom syntax categories. `notation items in c => rhs` adds one rule to category
`c`, and like `notation` it derives parsing (a `syntax` rule plus `macro_rules`) and printing (an
`app_unexpander`) from the single declaration. An item `x:d` is a variable of category `d`.

Every variable must occur on the right-hand side. Two kinds of rules switch between Lean and a
custom category `c`: `entry_notation items => x` with `x:c` is a term that contains a `c` (named
`c.entry`), and `escape_notation items in c => e` with `e:term` is a `c` that contains a Lean term
(named `c.escape`). A rule `n:num in c => ...` or `x:ident in c => ...` shows numerals or strings
in `c`. For these rules, the printer uses builders `c.entry.mk`, `c.escape.mk`, `c.ofNum` and
`c.ofIdent`, which apply the rule to a syntax tree; all other rules are named by `syntax`.

The printer of a rule uses the switches and literal rules declared before it. The entry of a
rule's category is required; values that need a missing escape or literal rule are printed as
ordinary Lean terms.
-/

/-! ## `notation ... in c` (generic) -/
namespace CatNotation
open Lean Elab Command PrettyPrinter

/-- `ident_str% x` is the identifier `x` as a string literal. -/
macro "ident_str% " x:ident : term =>
  pure (Syntax.mkStrLit (x.getId.eraseMacroScopes.toString false))

/-! ### Printing helpers, used by the generated unexpanders -/

/-- Shows an argument, already printed as a term, in category `cat`: an entry `[cat| s]` is
unwrapped, numerals, strings (as identifiers) and other terms are switched into `cat` with the
given builders. Fails if the needed builder is missing. -/
def toCat (cat : Name) (num? str? esc? : Option (Syntax → Syntax)) (e : Syntax) : Option Syntax :=
  if e.isOfKind (cat ++ `entry) then e.getArgs.find? (!·.isAtom)
  else if let (some f, true) := (num?, e.isOfKind numLitKind) then some (f e)
  else if let (some f, some s) := (str?, e.isStrLit?) then some (f (mkIdent (.mkSimple s)))
  else esc?.map (· e)

def numeral (e : Syntax) : Option Syntax := if e.isOfKind numLitKind then some e else none

def get? : Option Syntax → UnexpandM Syntax
  | some s => pure s
  | none => throw ()

/-! ### The commands -/

/-- Items: a token or a variable `x:cat`. -/
syntax item := str <|> (ident ":" ident)
syntax "notation " item* " in " ident " => " term : command
syntax "entry_notation " item* " => " term : command
syntax "escape_notation " item* " in " ident " => " term : command

inductive Item where
  | tok (s : StrLit)
  | var (x : Ident) (cat : Name)

def Item.ofSyntax (stx : Syntax) : Item :=
  let a := stx[0]
  if a.isOfKind strLitKind then .tok ⟨a⟩
  else .var ⟨a[0]⟩ a[2].getId.eraseMacroScopes

/-- What the printer may use a rule for. -/
inductive Role where
  | plain
  /-- `entry_notation`: a term that contains category `c` -/
  | entry (c : Name)
  /-- `escape_notation`: the rule's category contains a term -/
  | escape
  /-- `n:num in c` or `x:ident in c`: shows numerals or strings in the rule's category -/
  | literal (lit : Name)

/-- A rule `items in cat => rhs`. -/
structure Rule where
  cat : Name
  items : Array Item
  rhs : Term
  role : Role

/-- Entries and escapes have fixed names; other rules are named by `syntax`. -/
def Rule.kind? (r : Rule) : Option Name := match r.role with
  | .entry c => some (c ++ `entry)
  | .escape => some (r.cat ++ `escape)
  | _ => none

/-- The function that applies the rule to a syntax tree, for rules the printer uses. -/
def Rule.builder? (r : Rule) : Option Name := match r.role with
  | .entry c => some (c ++ `entry ++ `mk)
  | .escape => some (r.cat ++ `escape ++ `mk)
  | .literal `num => some (r.cat ++ `ofNum)
  | .literal _ => some (r.cat ++ `ofIdent)
  | .plain => none

def Rule.varCat? (r : Rule) (x : Syntax) : Option Name := r.items.findSome? fun
  | .var y d => if y.getId == x.getId then some d else none
  | _ => none

/-- Checks the rule and determines its role. `switch` is `entry`, `escape`, or `anonymous`. -/
def Rule.mk? (switch cat : Name) (items : Array Item) (rhs : Term) : CommandElabM Rule := do
  for item in items do
    if let .var x _ := item then
      unless (rhs.raw.find? (·.getId == x.getId)).isSome do
        throwErrorAt x "variable `{x}` does not occur on the right-hand side"
  let r : Rule := { cat, items, rhs, role := .plain }
  let d? := r.varCat? rhs
  let role : Role ←
    if switch == `entry then
      match d? with
      | some d =>
        if [`term, `num, `ident, `str].contains d then
          throwErrorAt rhs "an `entry_notation` must switch into a custom category"
        pure (.entry d)
      | none => throwErrorAt rhs "the right-hand side of an `entry_notation` must be a variable"
    else if switch == `escape then
      match d? with
      | some `term => pure .escape
      | some _ => throwErrorAt rhs "an `escape_notation` must switch to `term`"
      | none => throwErrorAt rhs "the right-hand side of an `escape_notation` must be a variable"
    else if let #[.var _ l] := items then
      pure (if [`num, `ident].contains l then .literal l else .plain)
    else pure .plain
  if role matches .plain && d?.isSome then
    throwErrorAt rhs "a notation that switches categories must be an `entry_notation` or an \
      `escape_notation`"
  let r := { r with role }
  if let some b := r.builder? then
    if (← getEnv).contains b then
      throwError match role with
        | .entry c => m!"there already is an `entry_notation` for `{c}`"
        | .escape => m!"there already is an `escape_notation` for `{cat}`"
        | _ => m!"there already is a notation for these literals in `{cat}`"
  return r

def antiquot (x : Syntax) : Syntax := Syntax.mkAntiquotNode `term x (isPseudoKind := true)

/-- Parsing: the `syntax` rule; returns its syntax node kind. -/
def Rule.addSyntax (r : Rule) : CommandElabM Name := do
  let items : Array (TSyntax `stx) ← r.items.mapM fun
    | .tok s => `(stx| $s:str)
    | .var _ d => `(stx| $(mkIdent d):ident)
  let name? := r.kind?.map mkIdent
  Command.elabSyntax (← `(syntax $[(name := $name?)]? $[$items]* : $(mkIdent r.cat)))

/-- Translation: a macro that substitutes the variables into `rhs`. -/
def Rule.addMacro (r : Rule) (kind : Name) : CommandElabM Unit := do
  let pat : Term := ⟨mkNode kind (r.items.map fun
    | .tok s => mkAtom s.getString.trimAscii.toString
    | .var x _ => antiquot x)⟩
  let rhs : Term := ⟨Id.run <| r.rhs.raw.replaceM fun s =>
    pure (if (r.varCat? s).isSome then some (antiquot s) else none)⟩
  elabCommand (← `(macro_rules | `($pat) => ``($rhs)))

/-- For rules the printer uses: the builder, which applies the rule to a syntax tree. -/
def Rule.addBuilder (r : Rule) (kind : Name) : CommandElabM Unit := do
  let some b := r.builder? | return
  let x := mkIdent `x
  let args : Array Term ← r.items.mapM fun
    | .tok s => `(Lean.mkAtom $(quote s.getString.trimAscii.toString))
    | .var .. => pure x
  elabCommand (← `(def $(mkIdent b) ($x : Lean.Syntax) : Lean.Syntax :=
    Lean.mkNode $(quote kind) #[$args,*]))

/-- Printing: an unexpander, derived from `rhs` like `notation` does (`mkUnexpander`), that also
switches each variable into its category and the result into `term`. -/
def Rule.addUnexpander (r : Rule) (kind : Name) : CommandElabM Unit := do
  if r.role matches .entry _ | .escape then return
  let env ← getEnv
  let builder? (n : Name) : CommandElabM Term :=
    if env.contains n then `(some $(mkIdent n)) else `(none)
  unless env.contains (r.cat ++ `entry ++ `mk) do return
  let qrhs : Term := ⟨Id.run <| r.rhs.raw.replaceM fun s =>
    pure (if (r.varCat? s).isSome then some (antiquot s) else none)⟩
  let (c, args) ← match qrhs with
    | `($c:ident $args*) => pure (c, args)
    | `($c:ident) => pure (c, #[])
    | _ => return
  let [(c, [])] ← liftMacroM <| Macro.resolveGlobalName c.getId | return
  let args ← liftMacroM <| args.mapM removeParentheses
  if hasDuplicateAntiquot args then return
  let outs : Array Term ← r.items.mapM fun
    | .tok s => `(Lean.mkAtom $(quote s.getString.trimAscii.toString))
    | .var x `num => `((← CatNotation.get? (CatNotation.numeral ($x).raw)))
    | .var x d => do
      if [`ident, `str, `term].contains d then `(($x).raw) else
      `((← CatNotation.get? (CatNotation.toCat $(quote d) $(← builder? (d ++ `ofNum))
        $(← builder? (d ++ `ofIdent)) $(← builder? (d ++ `escape ++ `mk)) ($x).raw)))
  let lhs := Syntax.mkApp (← `($$f:ident)) (args.map (⟨·⟩))
  let enter := mkIdent (r.cat ++ `entry ++ `mk)
  elabCommand (← `(@[app_unexpander $(mkIdent c)] def $(mkIdent (kind ++ `unexpand)) :
      Lean.PrettyPrinter.Unexpander
    | `($lhs) => do pure (⟨$enter (Lean.mkNode $(quote kind) #[$outs,*])⟩ : Lean.Term)
    | _ => throw ()))

def elabRule (switch : Name) (items : TSyntaxArray ``item) (cat : Ident) (rhs : Term) :
    CommandElabM Unit := do
  let r ← Rule.mk? switch cat.getId.eraseMacroScopes (items.map (Item.ofSyntax ·.raw)) rhs
  let kind ← r.addSyntax
  r.addMacro kind
  r.addBuilder kind
  r.addUnexpander kind

elab_rules : command
  | `(notation $items* in $cat => $rhs) => elabRule .anonymous items cat rhs
  | `(entry_notation $items* => $rhs) => elabRule `entry items (mkIdent `term) rhs
  | `(escape_notation $items* in $cat => $rhs) => elabRule `escape items cat rhs

end CatNotation

/-! ## The assembly language -/

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

declare_syntax_cat reg
entry_notation "[reg| " r:reg "]" => r
escape_notation "❰" e:term "❱" in reg => e
notation "%" n:num in reg => Reg.mk n

declare_syntax_cat imm
escape_notation "❰" e:term "❱" in imm => e
notation n:num in imm => n

declare_syntax_cat label
escape_notation "❰" e:term "❱" in label => e
notation l:ident in label => ident_str% l

-- `behavior := both` makes the first token of each rule a non-reserved keyword: `mov`, `add`, ...
-- stay usable as Lean identifiers, and an instruction starting with an identifier is tried both
-- as a label and as a keyword rule.
declare_syntax_cat instr (behavior := both)
entry_notation "[instr| " i:instr "]" => i
escape_notation "❰" e:term "❱" in instr => e

notation l:label ":" in instr => Instr.label l
notation "mov " r:reg ", " i:imm in instr => Instr.mov r i
notation "add " d:reg ", " s:reg in instr => Instr.add d s
notation "dec " r:reg in instr => Instr.dec r
notation "jnz " r:reg ", " l:label in instr => Instr.jnz r l
notation "halt" in instr => Instr.halt

/-! A program is a non-empty `List Instr`, written `[asm| ... ]` with one instruction per line.
This is defined directly, because `notation ... in c` (like `notation`) cannot express
repetition. The printer only handles lists of instructions that end in `[]`; the empty list is
not affected and is still written `[]`. -/

syntax "[asm|" ppDedent(ppIndent((ppLine instr)+) ppLine) "]" : term

macro_rules
  | `([asm| $is*]) => `(([$[[instr| $is]],*] : List Instr))

open Lean PrettyPrinter Delaborator SubExpr in
/-- The elements of a list literal `[a, ..., z]`, each shown as an instruction. -/
partial def delabInstrs : DelabM (Array (TSyntax `instr)) := do
  let e ← getExpr
  if e.isAppOfArity ``List.nil 1 then return #[]
  guard (e.isAppOfArity ``List.cons 3)
  let some i := CatNotation.toCat `instr none none (some instr.escape.mk)
      (← withNaryArg 1 delab) | failure
  return #[⟨i⟩] ++ (← withNaryArg 2 delabInstrs)

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.List.cons] def delabAsm : Delab := do
  let e ← getExpr
  guard (e.isAppOfArity ``List.cons 3 && e.appFn!.appFn!.appArg!.isConstOf ``Instr)
  let is ← delabInstrs
  `([asm| $[$is]*])

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

/-! ## Programs (non-empty `List Instr`) -/

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
] : List Instr
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
] : List Instr
-/
#guard_msgs in
#check [asm|
  mov ❰scratch❱, ❰answer❱
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

/-- info: fun rest => [instr| halt] :: rest : List Instr → List Instr -/
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
notation "≠0 " r:reg in cond => Cond.nonzero r
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

notation "clr " r:reg in instr => Instr.mov r 0
notation "dbl " r:reg in instr => Instr.add r r

/-- info: [instr| clr %1] : Instr -/
#guard_msgs in #check Instr.mov ⟨1⟩ 0

/-- info: [instr| mov %1, 2] : Instr -/
#guard_msgs in #check Instr.mov ⟨1⟩ 2

-- `dbl` uses its variable twice, so it has no printer and `add` is used instead.
/-- info: [instr| add %1, %1] : Instr -/
#guard_msgs in #check [instr| dbl %1]

/-! ## Rejected rules -/

/-- error: variable `r` does not occur on the right-hand side -/
#guard_msgs in notation "nop " r:reg in instr => Instr.halt

/--
error: a notation that switches categories must be an `entry_notation` or an `escape_notation`
-/
#guard_msgs in notation "(" r:reg ")" in instr => r

/-- error: an `entry_notation` must switch into a custom category -/
#guard_msgs in entry_notation "<<" e:term ">>" => e

/-- error: an `escape_notation` must switch to `term` -/
#guard_msgs in escape_notation "<<" r:reg ">>" in instr => r

/-- error: the right-hand side of an `escape_notation` must be a variable -/
#guard_msgs in escape_notation "<<" e:term ">>" in reg => Reg.mk e

-- A second `entry_notation` or `escape_notation` would make printing ambiguous.
/-- error: there already is an `escape_notation` for `reg` -/
#guard_msgs in escape_notation "<<" e:term ">>" in reg => e

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

-- Lean's own syntax is unaffected.
def mov (add : Nat) : Nat := add + 1

/-- info: mov (3 % 2) : Nat -/
#guard_msgs in #check mov ((3 : Nat) % 2)

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

-- Foreign terms: a variable, and a non-numeral argument of `AExp.lit`. Only the expressions that
-- contain them are printed as Lean terms; `AExp.lit 1` still uses the notation.
/-- info: fun x => ⟦aexp| 1⟧.plus x : AExp → AExp -/
#guard_msgs in #check fun x => AExp.plus (.lit 1) x

/-- info: AExp.lit answer : AExp -/
#guard_msgs in #check AExp.lit answer
