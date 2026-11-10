import Lean

/-!
A toy assembly language embedded in Lean, defined with `notation ... in c`, a variant of Lean's
`notation` for custom syntax categories. `notation items in c => rhs` adds one rule to category
`c`, and like `notation` it derives parsing (a `syntax` rule plus `macro_rules`) and printing (a
delaborator) from the single declaration. An item `x:d` is a variable of category `d`.

Every variable must occur on the right-hand side. A rule whose right-hand side is just a variable
`x:d` is an *identity rule*: it switches from `c` into `d` (so `d` must differ from `c`) and is
named `c.enter_d`; it also defines `c.enter_d.mk`, which applies the rule to a syntax tree. The
printer of a rule uses the identity rules declared before it to switch categories: `term.enter_c`
to show a value of category `c` as a term (required), `c.enter_term` to escape a Lean term inside
`c`, and `c.enter_num` to show a numeral in `c`. A string is shown in `c` with the rule
`x:ident in c`. Values that need a missing switch are printed as ordinary Lean terms.
-/

/-! ## `notation ... in c` (generic) -/
namespace CatNotation
open Lean Elab Command PrettyPrinter Delaborator SubExpr

/-- `ident_str% x` is the identifier `x` as a string literal. -/
macro "ident_str% " x:ident : term =>
  pure (Syntax.mkStrLit (x.getId.eraseMacroScopes.toString (escape := false)))

/-- The syntax node kind of an identity rule in category `c` with a variable of category `d`. -/
def enterKind (c d : Name) : Name := c ++ .mkSimple s!"enter_{d}"

/-- The syntax node kind of any other rule `items in cat`, e.g. `reg.«% num»`. -/
def kindOf (cat : Name) (items : List String) : Name := cat ++ .mkSimple (" ".intercalate items)

/-! ### Printing (generic delaborator) -/

/-- Shows an argument, already printed as a term, in category `cat`: `term.enter_cat` nodes are
unwrapped, numerals, strings (as identifiers) and other terms are switched into `cat` with the
given rules. Fails if the needed rule is missing. -/
def toCat (cat : Name) (num? str? esc? : Option (Syntax → Syntax)) (e : Syntax) : Option Syntax :=
  if e.isOfKind (enterKind `term cat) then e.getArgs.find? (!·.isAtom)
  else if let (some f, true) := (num?, e.isOfKind numLitKind) then some (f e)
  else if let (some f, some s) := (str?, e.isStrLit?) then some (f (mkIdent (.mkSimple s)))
  else esc?.map (· e)

def numeral (e : Syntax) : Option Syntax := if e.isOfKind numLitKind then some e else none

/-- An item of a printed rule: a token, or the argument with the given index, converted. -/
inductive Out where
  | tok (s : String)
  | arg (i : Nat) (conv : Syntax → Option Syntax)

/-- Prints an application of a rule's head constant to `arity` arguments as rule `kind`, and
switches the result into `term` with `enter`. -/
def delabRule (arity : Nat) (kind : Name) (enter : Syntax → Syntax) (items : Array Out) :
    Delab := do
  guard ((← getExpr).getAppNumArgs == arity)
  let args ← items.mapM fun
    | .tok s => pure (mkAtom s)
    | .arg i conv => do
      let some s := conv (← withNaryArg i delab) | failure
      pure s
  return ⟨enter (mkNode kind args)⟩

/-! ### The command -/

/-- Items: a token or a variable `x:cat`. -/
syntax item := str <|> (ident ":" ident)
syntax "notation " item* " in " ident " => " term : command

inductive Item where
  | tok (s : StrLit)
  | var (x : Ident) (cat : Name)

def Item.ofSyntax (stx : Syntax) : Item :=
  let a := stx[0]
  if a.isOfKind strLitKind then .tok ⟨a⟩
  else .var ⟨a[0]⟩ a[2].getId.eraseMacroScopes

def Item.token? : Item → Option String
  | .tok s => some s.getString.trimAscii.toString
  | .var .. => none

/-- A rule `items in cat => rhs` whose syntax node kind is `kind`. -/
structure Rule where
  cat : Name
  items : Array Item
  rhs : Term
  kind : Name
  isIdentity : Bool := false

def Rule.varCat? (r : Rule) (x : Syntax) : Option Name := r.items.findSome? fun
  | .var y d => if y.getId == x.getId then some d else none
  | _ => none

/-- Checks the rule and determines its kind. -/
def Rule.mk? (cat : Name) (items : Array Item) (rhs : Term) : CommandElabM Rule := do
  for item in items do
    if let .var x _ := item then
      unless (rhs.raw.find? (·.getId == x.getId)).isSome do
        throwErrorAt x "variable `{x}` does not occur on the right-hand side"
  let r : Rule := { cat, items, rhs, kind := .anonymous }
  if let some d := r.varCat? rhs then
    if d == cat then throwErrorAt rhs "an identity rule must switch to another category"
    if (← getEnv).contains (enterKind cat d) then
      throwError "there already is a notation that switches from `{cat}` to `{d}`"
    return { r with kind := enterKind cat d, isIdentity := true }
  return { r with kind := kindOf cat (items.toList.map fun i => i.token?.getD (match i with
    | .var _ d => d.toString | _ => "")) }

def antiquot (x : Syntax) : Syntax := Syntax.mkAntiquotNode `term x (isPseudoKind := true)

/-- Parsing: the `syntax` rule. -/
def Rule.elabSyntax (r : Rule) : CommandElabM Unit := do
  let items : Array (TSyntax `stx) ← r.items.mapM fun
    | .tok s => `(stx| $s:str)
    | .var _ d => `(stx| $(mkIdent d):ident)
  elabCommand (← `(syntax (name := $(mkIdent r.kind)) $[$items]* : $(mkIdent r.cat)))

/-- Translation: a macro that substitutes the variables into `rhs`. -/
def Rule.elabMacro (r : Rule) : CommandElabM Unit := do
  let pat : Term := ⟨mkNode r.kind (r.items.map fun i => (i.token?.map mkAtom).getD (match i with
    | .var x _ => antiquot x | _ => .missing))⟩
  let rhs : Term := ⟨Id.run <| r.rhs.raw.replaceM fun s =>
    pure (if (r.varCat? s).isSome then some (antiquot s) else none)⟩
  elabCommand (← `(macro_rules | `($pat) => ``($rhs)))

/-- Printing an identity rule: `kind.mk`, which applies the rule to a syntax tree. -/
def Rule.elabBuilder (r : Rule) : CommandElabM Unit := do
  unless r.isIdentity do return
  let x := mkIdent `x
  let args : Array Term ← r.items.mapM fun i => match i.token? with
    | some s => `(Lean.mkAtom $(quote s))
    | none => pure x
  elabCommand (← `(def $(mkIdent (r.kind ++ `mk)) ($x : Lean.Syntax) : Lean.Syntax :=
    Lean.mkNode $(quote r.kind) #[$args,*]))

/-- Printing any other rule: a delaborator, if `rhs` is a constant applied to distinct variables
and the switch `term.enter_cat` exists. -/
def Rule.elabDelab (r : Rule) : CommandElabM Unit := do
  let (c, args) ← match r.rhs with
    | `($c:ident $args*) => pure (c, args)
    | `($c:ident) => pure (c, #[])
    | _ => return
  if (r.varCat? c).isSome || args.any fun a => (r.varCat? a).isNone then return
  let env ← getEnv
  let builder? (k : Name) : Option Ident :=
    if env.contains (k ++ `mk) then mkIdent (k ++ `mk) else none
  let some enter := builder? (enterKind `term r.cat) | return
  let optTerm (t? : Option Term) : CommandElabM Term := match t? with
    | some t => `(some $t)
    | none => `(none)
  let outs : Array Term ← r.items.mapM fun
    | .tok s => `(CatNotation.Out.tok $(quote s.getString.trimAscii.toString))
    | .var x d => do
      let i := (args.findIdx? fun a : Term => a.raw.getId == x.getId).getD 0
      let str? : Option Term ← if env.contains (kindOf d ["ident"]) then
        some <$> `(fun i => Lean.mkNode $(quote (kindOf d ["ident"])) #[i]) else pure none
      let conv ← if d == `num then `(CatNotation.numeral)
        else if [`ident, `str, `term].contains d then `(some)
        else `(CatNotation.toCat $(quote d) $(← optTerm (builder? (enterKind d `num)))
          $(← optTerm str?) $(← optTerm (builder? (enterKind d `term))))
      `(CatNotation.Out.arg $(quote i) $conv)
  let const ← liftTermElabM <| realizeGlobalConstNoOverload c
  elabCommand (← `(@[delab $(mkIdent (`app ++ const))] def $(mkIdent (r.kind ++ `delab)) :
      Lean.PrettyPrinter.Delaborator.Delab :=
    CatNotation.delabRule $(quote args.size) $(quote r.kind) $enter #[$outs,*]))

elab_rules : command
  | `(notation $items* in $cat => $rhs) => do
    let r ← Rule.mk? cat.getId.eraseMacroScopes (items.map (Item.ofSyntax ·.raw)) rhs
    r.elabSyntax
    r.elabMacro
    r.elabBuilder
    r.elabDelab

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
notation "[reg| " r:reg "]" in term => r
notation "❰" e:term "❱" in reg => e
notation "%" n:num in reg => Reg.mk n

declare_syntax_cat imm
notation "❰" e:term "❱" in imm => e
notation n:num in imm => n

declare_syntax_cat label
notation "❰" e:term "❱" in label => e
notation l:ident in label => ident_str% l

-- `behavior := both` makes the first token of each rule a non-reserved keyword: `mov`, `add`, ...
-- stay usable as Lean identifiers, and an instruction starting with an identifier is tried both
-- as a label and as a keyword rule.
declare_syntax_cat instr (behavior := both)
notation "[instr| " i:instr "]" in term => i
notation "❰" e:term "❱" in instr => e

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
  let some i := CatNotation.toCat `instr none none (some instr.enter_term.mk)
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

/-- info: [instr| jnz ❰{ idx := answer }❱, done] : Instr -/
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
notation "⟦cond| " c:cond "⟧" in term => c
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

/-! ## Rejected rules -/

/-- error: variable `r` does not occur on the right-hand side -/
#guard_msgs in notation "nop " r:reg in instr => Instr.halt

/-- error: an identity rule must switch to another category -/
#guard_msgs in notation "(" r:reg ")" in reg => r

-- A second notation for the same category switch would make printing ambiguous.
/-- error: there already is a notation that switches from `reg` to `term` -/
#guard_msgs in notation "<<" e:term ">>" in reg => e

/-- error: there already is a notation that switches from `term` to `cond` -/
#guard_msgs in notation "⦃" c:cond "⦄" in term => c

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

/-! ## A category without an escape back to Lean

`aexp` has a rule to switch from `term` into it, but none to switch back. Expressions that
consist only of `aexp` notations are still printed with them; an expression that contains a
foreign Lean term is printed as an ordinary Lean term. -/

inductive AExp where
  | lit (n : Nat)
  | neg (a : AExp)
  | plus (a b : AExp)

declare_syntax_cat aexp
notation "⟦aexp| " e:aexp "⟧" in term => e
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
