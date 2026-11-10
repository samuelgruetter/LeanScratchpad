import Lean

/-!
A toy assembly language embedded in Lean, defined with `cat_notation`, a variant of `notation`
for custom syntax categories.

`cat_notation items : c => rhs` adds one rule to the syntax category `c`. Like `notation`, it
derives parsing (a `syntax` rule plus `macro_rules`) and printing (an `app_unexpander`) from the
single declaration. An item `x:d` is a variable of category `d`.

Two kinds of rules are recognized by their shape, because the printer needs them: an entry
`"[c| " x:c "]" : term => x` (needed if `c` has rules with printers) and an escape
`"❰" e:term "❱" : c => e` (needed if arguments of category `c` may have to be escaped).
-/

/-! ## `cat_notation` (generic) -/
namespace CatNotation
open Lean Elab Command

/-- `ident_str% x` is the identifier `x` as a string literal. -/
macro "ident_str% " x:ident : term =>
  pure (Syntax.mkStrLit (x.getId.eraseMacroScopes.toString (escape := false)))
/-- Printing: turns an already printed argument into syntax of category `cat`. `[cat| s]` becomes
`s`, literals of a pass-through rule of `cat` (`lits`) are kept, anything else is escaped. -/
def toCat (cat : Name) (lits : Array Name) (esc : String × String) (e : Syntax) : Syntax :=
  if e.isOfKind (cat ++ `entry) then e[1]
  else if lits.contains `num && e.isOfKind numLitKind then mkNode (cat ++ `pass ++ `num) #[e]
  else if let (true, some s) := (lits.contains `ident_str, e.isStrLit?) then
    mkNode (cat ++ `pass ++ `ident_str) #[mkIdent (.mkSimple s)]
  else mkNode (cat ++ `escape) #[mkAtom esc.1, e, mkAtom esc.2]
-- printing a `num` variable fails unless the argument is a numeral
def num? (e : Syntax) : PrettyPrinter.UnexpandM Syntax :=
  if e.isOfKind numLitKind then pure e else throw ()
def entry (cat : Name) (tks : String × String) (s : Syntax) : Syntax :=
  mkNode (cat ++ `entry) #[mkAtom tks.1, s, mkAtom tks.2]

/-- `cat_notation` items: a token, a non-reserved keyword (`&"mov"`), or a variable `x:cat`. -/
syntax item := str <|> ("&" str) <|> (ident ":" ident)
syntax "cat_notation " item* " : " ident " => " term : command

inductive Item where
  | tok (s : String) (nonReserved : Bool)
  | var (x : Ident) (cat : Name)
def Item.ofSyntax (stx : Syntax) : Item :=
  let a := stx[0]
  if let some s := a.isStrLit? then .tok s false
  else if a[0].isAtom then .tok (a[1].isStrLit?.getD "") true
  else .var ⟨a[0]⟩ a[2].getId.eraseMacroScopes

elab_rules : command
  | `(cat_notation $items* : $catId => $rhs) => do
    let cat := catId.getId.eraseMacroScopes
    let items := items.map (Item.ofSyntax ·.raw)
    let varCat? (x : Syntax) : Option Name := items.findSome? fun
      | .var y d => if y.getId == x.getId then some d else none
      | _ => none
    -- entries, escapes and pass-through rules (`n:num : c => n`) get names that the printer knows
    let kind? : Option Name := match rhs with
      | `($x:ident) => (varCat? x).map fun d =>
        if cat == `term then d ++ `entry
        else if d == `term then cat ++ `escape else cat ++ `pass ++ d
      | `(ident_str% $_) => some (cat ++ `pass ++ `ident_str)
      | _ => none
    let kind := kind?.getD (cat ++ .mkSimple s!"r{(← getRef).getPos?.map (·.byteIdx) |>.getD 0}")
    -- the printer builds entry and escape nodes, so it needs their delimiters
    if let (some (Item.tok o _), some (Item.tok c _)) := (items[0]?, items.back?) then
      if ["entry", "escape"].contains kind.getString! then
        elabCommand (← `(def $(mkIdent (kind ++ `tokens)) : String × String :=
          ($(quote o.trimAscii.toString), $(quote c.trimAscii.toString))))
    -- parsing: a `syntax` rule and a macro that substitutes the variables into `rhs`
    let stxItems : Array (TSyntax `stx) ← items.mapM fun
      | .tok s false => `(stx| $(Syntax.mkStrLit s):str)
      | .tok s true => pure ⟨mkNode ``Parser.Syntax.nonReserved #[mkAtom "&", .mkStrLit s]⟩
      | .var _ d => `(stx| $(mkIdent d):ident)
    elabCommand (← `(syntax (name := $(mkIdent kind)) $[$stxItems]* : $(mkIdent cat)))
    let antiquot (x : Syntax) := Syntax.mkAntiquotNode `term x (isPseudoKind := true)
    let pat : Term := ⟨mkNode kind (items.map fun
      | .tok s _ => mkAtom s.trimAscii.toString
      | .var x _ => antiquot x)⟩
    let qrhs : Term := ⟨Id.run <| rhs.raw.replaceM fun s =>
      pure (if (varCat? s).isSome then some (antiquot s) else none)⟩
    elabCommand (← `(macro_rules | `($pat) => ``($qrhs)))
    -- printing: an unexpander for `rhs = c x₁ ... xₙ` where the `xᵢ` are variables
    let (c, args) ← match rhs with
      | `($c:ident $args*) => pure (c, args)
      | `($c:ident) => pure (c, #[])
      | _ => return
    let some lhsArgs := args.mapM fun a => (varCat? a).map fun _ => (⟨antiquot a⟩ : Term)
      | return
    if (varCat? c).isSome then return
    let env ← getEnv
    let lits (d : Name) : Array Name := match Parser.getParserCategory? env d with
      | some pc => pc.kinds.foldl (init := #[]) fun acc k _ =>
        if k.getPrefix == d ++ `pass then acc.push (.mkSimple k.getString!) else acc
      | none => #[]
    let outs : Array Term ← items.mapM fun
      | .tok s _ => `(mkAtom $(quote s.trimAscii.toString))
      | .var x `num => `((← CatNotation.num? ($x).raw))
      | .var x d => if [`ident, `str, `term].contains d then `(($x).raw)
        else `(CatNotation.toCat $(quote d) $(quote (lits d)) $(mkIdent (d ++ `escape ++ `tokens))
          ($x).raw)
    let lhs := Syntax.mkApp (← `($$f:ident)) lhsArgs
    let out ← `(CatNotation.entry $(quote cat) $(mkIdent (cat ++ `entry ++ `tokens))
      (mkNode $(quote kind) #[$outs,*]))
    elabCommand (← `(@[app_unexpander $c] def $(mkIdent (kind ++ `unexpand)) :
        Lean.PrettyPrinter.Unexpander
      | `($lhs) => do pure (⟨$out⟩ : Lean.Term)
      | _ => throw ()))

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

structure Program where
  instrs : List Instr

declare_syntax_cat reg
cat_notation "[reg| " r:reg "]" : term => r
cat_notation "❰" e:term "❱" : reg => e
cat_notation "%" n:num : reg => Reg.mk n

declare_syntax_cat imm
cat_notation "❰" e:term "❱" : imm => e
cat_notation n:num : imm => n

declare_syntax_cat label
cat_notation "❰" e:term "❱" : label => e
cat_notation l:ident : label => ident_str% l

-- `behavior := both`: an instruction starting with an identifier may also start with a keyword
-- such as `mov`, so the keyword rules are tried as well, not only the label rule.
declare_syntax_cat instr (behavior := both)
cat_notation "[instr| " i:instr "]" : term => i
cat_notation "❰" e:term "❱" : instr => e

-- `&"mov"` etc. are non-reserved keywords, so `mov`, `add`, ... stay usable as Lean identifiers.
cat_notation l:label ":" : instr => Instr.label l
cat_notation &"mov " r:reg ", " i:imm : instr => Instr.mov r i
cat_notation &"add " d:reg ", " s:reg : instr => Instr.add d s
cat_notation &"dec " r:reg : instr => Instr.dec r
cat_notation &"jnz " r:reg ", " l:label : instr => Instr.jnz r l
cat_notation &"halt" : instr => Instr.halt

/-! A program is a sequence of instructions, which `cat_notation` cannot express (just like
`notation`), so it is defined directly. Each instruction is printed on its own line. -/

syntax "[asm|" ppDedent(ppIndent((ppLine instr)*) ppLine) "]" : term

macro_rules
  | `([asm| $is*]) => `(Program.mk [$[[instr| $is]],*])

@[app_unexpander Program.mk] def unexpandProgram : Lean.PrettyPrinter.Unexpander
  | `($_ [$is,*]) => do
    let is : Array (Lean.TSyntax `instr) := is.getElems.map
      (⟨CatNotation.toCat `instr #[] instr.escape.tokens ·⟩)
    `([asm| $[$is]*])
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
