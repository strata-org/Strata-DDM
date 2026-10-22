/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.AST
public import StrataDDM.Render
import all StrataDDM.Util.Format
import all StrataDDM.Util.Nat
import all StrataDDM.Util.String

open Std (Format format)

public section
namespace StrataDDM

/--
Check if a character is valid for starting a regular identifier.
Regular identifiers must start with a letter or underscore.

NOTE: When updating this function, you will want to consider updating Strata/DDM/Parser.lean as well.
-/
@[expose] def isIdBegin (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '$'

/--
Check if a character is valid for continuing a regular identifier.
Includes @ and $ which are valid in SMT-LIB 2.6 simple symbols and
used by the encoder for disambiguated names (e.g. x@1) and generated
names (e.g. $__bv0).
Note: `'` (apostrophe) is intentionally excluded. Although SMT-LIB 2.6 allows
it in simple symbols, both cvc5 and Z3 reject it as an unquoted character.
Names containing `'` (e.g. Lean's `v'`) will be pipe-quoted instead.
-/
@[expose] def isIdContinue (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '?' || c == '!' || c == '@' || c == '$'

/--
Check if a string needs pipe delimiters when formatted as an identifier.
Returns true if the string contains special characters, spaces, or starts with a digit.
-/
private def needsPipeDelimiters (s : String) : Bool :=
  if h : s.isEmpty then
    true
  else
    let firstChar := s.startPos.get (by simp_all)
    !isIdBegin firstChar || s.any (fun c => !isIdContinue c)

/--
Escape a string for use in pipe-delimited identifiers (SMT-LIB 2.6).
Escapes \ as \\ and | as \|
-/
private def escapePipeIdent (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c == '\\' then acc ++ "\\\\"
    else if c == '|' then acc ++ "\\|"
    else acc.push c

/-- The identifiers that the dialects' tokens make unreadable (see `tokenWords`): each one of
`names`, and each identifier that starts with one of `prefixes`. -/
private structure Keywords where
  names : Std.HashSet String := {}
  prefixes : Array String := #[]

/-- Whether the parser would read the identifier `s`, printed bare, as a token or as part of one. -/
private def Keywords.unreadable (ks : Keywords) (s : String) : Bool :=
  (!ks.names.isEmpty && ks.names.contains s) || ks.prefixes.any fun p => s.startsWith p

/--
Format a string as an identifier, using pipe delimiters if needed: when it has a character an
identifier cannot have, or when `keywords` makes it unreadable, because the parser would read it
as a token or as part of one.
Strips Lean's «» notation if present.
Follows SMT-LIB 2.6 specification for quoted symbols.
-/
private def formatIdent (s : String) (keywords : Keywords := {}) : Format :=
  if needsPipeDelimiters s || keywords.unreadable s then
    Format.text ("|" ++ escapePipeIdent s ++ "|")
  else
    Format.text s

/-- Whether `c` is a letter, a digit, `_` or `$`. -/
private def isWordChar (c : Char) : Bool := isIdBegin c || c.isDigit

/-- Whether `c` can be part of a number: a hexadecimal digit, or `x` or `o`, which mark a base. -/
private def isNumberChar (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') || c == 'x' || c == 'X' || c == 'o' ||
    c == 'O'

/-- Whether a name printed right after the text `rb`, given in reverse, can read as a word of its
own.  It can after a space or a punctuation character.  After a letter, a digit, `_` or `$`, it can
only when the text ends with a number, or with one of `ends`: the tokens, reversed, of the literals
that a name can follow and that end with such a character, as `#a` does.  After a name or a
keyword, the name reads as part of it; this assumes that no syntax prints a name there. -/
private def nameCanFollow (ends : Array (List Char)) (rb : List Char) : Bool :=
  match rb with
  | [] => false
  | c :: _ =>
    !isWordChar c || (rb.takeWhile isNumberChar).any Char.isDigit || ends.any (·.isPrefixOf rb)

/-- The runs of identifier characters in `cs` that begin like an identifier where `canFollow`
holds for the text before them, each with whether it ends `cs`.  `rb` is the text before `cs`,
in reverse. -/
private def innerRuns (canFollow : List Char → Bool) (rb : List Char) :
    List Char → List (String × Bool)
  | [] => []
  | c :: cs =>
    let runs := innerRuns canFollow (c :: rb) cs
    if isIdBegin c && canFollow rb then
      let run := (c :: cs).takeWhile isIdContinue
      (String.ofList run, run.length == cs.length + 1) :: runs
    else runs

/-- The identifiers that a token `t` makes unreadable, each with whether every longer identifier
that starts with it is unreadable too:
* `t` itself;
* when `t` starts like an identifier and goes on with other characters, as `old(` does, its
  identifier part `old`, which the parser would read as the start of `t`;
* each run of identifier characters inside `t` where a name can follow the part of `t` before it
  (`canFollow`), as `const` in `= const`.  After `=`, the parser reads the longest token without
  checking where a name ends, so the name `const`, printed after `= `, reads as part of `t`.  When
  the run ends `t`, every longer identifier that starts with it is unreadable too: `= constFoo`
  reads as `t`, then `Foo`.
-/
private def tokenWords (canFollow : List Char → Bool) (t : String) : Array (String × Bool) :=
  let cs := t.toList
  let pre := cs.takeWhile isIdContinue
  let (words, rb, rest) :=
    if isIdBegin t.front then
      (if pre.length == cs.length then #[t] else #[t, String.ofList pre], pre.reverse,
        cs.drop pre.length)
    else (#[t], [], cs)
  words.map (·, false) ++ (innerRuns canFollow rb rest).toArray

/-- The atoms of a syntax definition's atom, with the atoms of an indented block in line. -/
private def SyntaxDefAtom.flatten : SyntaxDefAtom → Array SyntaxDefAtom
  | .indent _ as => as.attach.flatMap fun ⟨a, _⟩ => a.flatten
  | a => #[a]

/-- The atoms of a syntax definition, with the atoms of its indented blocks in line: an indented
block prints no text of its own. -/
private def SyntaxDef.flatAtoms : SyntaxDef → Array SyntaxDefAtom
  | .std atoms _ => atoms.flatMap (·.flatten)
  | .passthrough => #[]

/-- The first atom after position `j` of `atoms` that prints text, if there is one. -/
private def nextAtom? (atoms : Array SyntaxDefAtom) (j : Nat) : Option SyntaxDefAtom :=
  (atoms.extract (j + 1) atoms.size).find? fun | .str l => !l.isEmpty | _ => true

/-- The categories whose printed operations a name can follow directly, as one level of the
syntax definitions shows.  `occurs` holds the categories of the arguments, and `byName` those of
the arguments that a name may follow: the next atom is an argument, or there is none. -/
private structure Follows where
  occurs : Std.HashSet QualifiedIdent := {}
  byName : Std.HashSet QualifiedIdent := {}

/-- Whether a name may follow an operation of category `cat` directly.  It may after a command,
since commands follow one another; after an operation whose category no argument has, which this
check does not cover; and after an argument of category `cat` that a name may follow. -/
private def Follows.nameMayFollow (fs : Follows) (cat : QualifiedIdent) : Bool :=
  cat == q`Init.Command || !fs.occurs.contains cat || fs.byName.contains cat

/-- Record an argument of category `c`, which a name may follow when `byName` holds.  An option,
and the last element of a list, are followed by what follows the argument.  The other elements are
followed by the list's separator, except in a `Seq`, whose elements follow one another. -/
private def Follows.mark (fs : Follows) (byName : Bool) (c : SyntaxCat) : Follows :=
  let fs := { occurs := fs.occurs.insert c.name
              byName := if byName then fs.byName.insert c.name else fs.byName }
  let inner := byName || c.name == q`Init.Seq
  c.args.attach.foldl (init := fs) fun fs ⟨a, _⟩ => fs.mark inner a
termination_by c
decreasing_by
  have hlt := Array.sizeOf_lt_of_mem ‹a ∈ c.args›
  cases c; simp_all; omega

/-- Record the arguments of a syntax definition with arguments `args` (see `Follows`).  An
operation that prints as its argument passes on what follows it, so a name may follow that
argument. -/
private def Follows.markDef (fs : Follows) (args : ArgDecls) (stx : SyntaxDef) : Follows :=
  match stx with
  | .passthrough => args.toArray.foldl (init := fs) fun fs a =>
    match a.kind with
    | .cat c => fs.mark true c
    | .type _ => fs
  | .std .. =>
    let atoms := stx.flatAtoms
    atoms.zipIdx.foldl (init := fs) fun fs (a, j) =>
      match a with
      | .ident i _ =>
        match args.toArray[i]? with
        | some { kind := .cat c, .. } =>
          fs.mark (match nextAtom? atoms j with | some (.str _) => false | _ => true) c
        | _ => fs
      | _ => fs

/-- The tokens, reversed, of the literals of a syntax definition that end with a letter, a digit,
`_` or `$`, and that a printed name can follow directly: the next atom that prints text is an
argument, or there is none and a name can follow the operation.  `cat` is the operation's
category, or `none` for a function, which a name may follow. -/
private def SyntaxDef.wordEnds (fs : Follows) (cat : Option QualifiedIdent) (stx : SyntaxDef) :
    Array (List Char) :=
  let atoms := stx.flatAtoms
  atoms.zipIdx.filterMap fun (a, j) => match a with
    | .str l =>
      let nameFollows := match nextAtom? atoms j with
        | some (.str _) => false
        | some _ => true
        | none => cat.all fs.nameMayFollow
      if !l.isEmpty && isWordChar l.back && nameFollows then
        (SyntaxDefAtom.tokenOf? l).map (·.toList.reverse)
      else none
    | _ => none

/-- Add the identifiers `ws` that a token makes unreadable (see `tokenWords`). -/
private def Keywords.insertMany (ks : Keywords) (ws : Array (String × Bool)) : Keywords :=
  ws.foldl (init := ks) fun ks (w, isPrefix) =>
    { names := ks.names.insert w
      prefixes := if isPrefix && !ks.prefixes.contains w then ks.prefixes.push w else ks.prefixes }

/-- The identifiers the tokens of the dialects' operations and functions make unreadable. -/
private def DialectMap.keywords (dialects : DialectMap) : Keywords :=
  let decls : Array (Option QualifiedIdent × ArgDecls × SyntaxDef) :=
    dialects.toList.foldl (init := #[]) fun ds d => d.declarations.foldl (init := ds) fun ds decl =>
      match decl with
      | .op o => ds.push (some o.category, o.argDecls, o.syntaxDef)
      | .function f => ds.push (none, f.argDecls, f.syntaxDef)
      | _ => ds
  let fs := decls.foldl (init := {}) fun fs (_, args, stx) => fs.markDef args stx
  let ends := decls.flatMap fun (cat, _, stx) => stx.wordEnds fs cat
  decls.foldl (init := {}) fun ks (_, _, stx) => stx.flatAtoms.foldl (init := ks) fun ks a =>
    match a with
    | .str l => match SyntaxDefAtom.tokenOf? l with
      | some t => ks.insertMany (tokenWords (nameCanFollow ends) t)
      | none => ks
    | _ => ks

/-- Quote an identifier string for SMT-LIB, adding pipe delimiters if needed. -/
def quoteIdent (s : String) : String :=
  if needsPipeDelimiters s then "|" ++ escapePipeIdent s ++ "|" else s

structure PrecFormat where
  format : Format
  prec : Nat
deriving Inhabited

namespace PrecFormat

private def atom (format : Format) : PrecFormat := { format, prec := maxPrec + 1 }

private def ofFormat {α} [Std.ToFormat α] (x : α) (prec : Nat := maxPrec) : PrecFormat := { format := Std.format x, prec }

end PrecFormat

/--
Options to control parenthesis
-/
structure FormatOptions where
  /-- Always add parenthesis when feasible. -/
  alwaysParen : Bool := false
  /-- Override string-literal rendering for a consumer-specific concrete syntax. -/
  customStringEscaper : Option (String → String) := none
  /-- Force a format mode per literal kind (e.g. `"decimal"`), overriding any
      dialect-declared spec. An absent entry means "use each type's default". -/
  formatModes : Std.HashMap String FormatMode := {}
  /-- Pipe-delimit every name that the dialects' tokens make unreadable (see
      `tokenWords`), so that the printed text parses again.  Off by default, because it changes
      what a dialect prints when a token is printed through an identifier, e.g. SMT-LIB's `as`.
      With it, a type variable prints as other names do: pipe-delimited when its characters need
      it.  It applies to programs only: it does not change how a dialect definition prints. -/
  quoteKeywords : Bool := false

/--
A format context provides callbacks and information needed to
properly pretty-print Strata AST types.
-/
structure FormatContext where
  private opts : FormatOptions
  private getFnDecl : QualifiedIdent → Option FunctionDecl
  private getOpDecl : QualifiedIdent → Option OpDecl
  private globalContext : GlobalContext
  /-- The identifiers that the dialects' tokens make unreadable (see `tokenWords`).  It is empty
      unless `FormatOptions.quoteKeywords` is set. -/
  private keywords : Keywords := {}
  /-- Format mode declared on the argument currently being rendered (via
      `@[<mode>]` on its `ArgDecl`), if any. Lower precedence than an explicit
      `opts.formatModes` entry. -/
  private argFormatMode : Option FormatMode := none

namespace FormatContext

/-- A format context that uses no syntactic sugar. -/
private def explicit : FormatContext where
  opts := {}
  getFnDecl _ := none
  getOpDecl _ := none
  globalContext := {}

/-- Set the format mode carried from the current argument's declaration. -/
def withArgFormatMode (ctx : FormatContext) (mode : Option FormatMode) : FormatContext :=
  { ctx with argFormatMode := mode }

private def fvarName (ctx : FormatContext) (idx : FreeVarIndex) : String :=
  if let some name := ctx.globalContext.nameOf? idx then
    name
  else
    s!"fvar!{idx}"

protected def ofDialects (dialects : DialectMap) (globalContext : GlobalContext := {}) (opts : FormatOptions := {}) : FormatContext where
  opts := opts
  getFnDecl sym := Id.run do
    let .function f := dialects.decl! sym
      | return panic! s!"Unknown function {sym}"
    some f
  getOpDecl i := Id.run do
    let .op op := dialects.decl! i
      | panic! s!"Unknown op {i}"; return default
    some op
  globalContext := globalContext
  keywords := if opts.quoteKeywords then dialects.keywords else {}

end FormatContext

/-- Format state  -/
structure FormatState where
  openDialects : Std.HashSet String
  bindings : Array String := #[]

namespace FormatState

/-- A format context that uses no syntactic sugar. -/
def empty : FormatState where
  openDialects := {}

instance : Inhabited FormatState where
  default := .empty

def pushBinding (s : FormatState) (ident : String) : FormatState :=
  { s with bindings := s.bindings.push ident }

private def lvlVarName (s : FormatState) (lvl : Nat) : String :=
  let b := s.bindings
  if h : lvl < b.size then
    b[lvl]
  else
    s!"bvar!{s.bindings.size - (lvl + 1)}"

private def bvarName (s : FormatState) (idx : Nat) : String :=
  let b := s.bindings
  if h : idx < b.size then
    b[b.size - (idx + 1)]
  else
    s!"bvar!{idx}"

end FormatState

/--
A StrataFormat is a closure which given contextual information
produces a format operation as well as a precedence.  This
is used for auto-inserting parenthesis when needed.

Formats should return `maxPrec` when parenthesis are not
required.
-/
@[expose] def StrataFormat := FormatContext → FormatState → PrecFormat

class ToStrataFormat (α : Type u) where
  mformat : α → StrataFormat

export ToStrataFormat (mformat)

private def cformat [ToStrataFormat α] (a : α) (c : FormatContext) (s : FormatState) : Format := mformat a c s |>.format

def eformat [ToStrataFormat α] (a : α) : Format := mformat a .explicit .empty |>.format

instance : ToStrataFormat String where
  mformat s _ _ := private .ofFormat s

instance : ToStrataFormat Format where
  mformat s _ _ := private .atom s

instance : ToStrataFormat StrataFormat where
  mformat := id

instance : ToStrataFormat Nat where
  mformat n _ _ := private .ofFormat n (maxPrec + 1)

instance : ToStrataFormat Decimal where
  mformat n _ _ := private .ofFormat n (maxPrec + 1)

namespace StrataFormat

private protected def nil : StrataFormat := fun _ _ => .atom .nil

/-- Pretty print a free variable with the given index. Names with special
    characters (e.g. `#` in monomorphized names) are pipe-quoted so the
    output re-parses correctly. -/
private protected def fvar (fvarIdx : Nat) : StrataFormat := fun c _ =>
  .atom (formatIdent (c.fvarName fvarIdx) c.keywords)

/-- Pretty print a bound variable with the given deBruijn index -/
private protected def lvlVar (lvl : Nat) : StrataFormat := fun _ s => .atom (formatIdent (s.lvlVarName lvl))

/-- Pretty print a bound variable with the given deBruijn index -/
private protected def bvar (idx : Nat) : StrataFormat := fun c s =>
  .atom (formatIdent (s.bvarName idx) c.keywords)

/--
Join together elements in list with no separator between adjacent elements.
-/
private def join [ToStrataFormat α] (a : List α) : StrataFormat :=
  match a with
  | [] => .nil
  | [x] => mformat x
  | _ => fun c s => .atom (Format.join (a.map (fun e => mformat e c s |>.format)))

/--
Join together elements in list with a separator between adjacent elements.
-/
private def sepBy [ToStrataFormat α] (a : Array α) (sep : String) : StrataFormat :=
  match p : a.size with
  | 0 => .nil
  | 1 =>
    mformat a[0]
  | n + 2 => fun c s =>
    let sep := format sep
    let append f e := f ++ sep ++ (mformat e c s).format
    .atom (a.foldl (start := 1) append (mformat a[0] c s).format)

instance : Append StrataFormat where
  append x y ctx s := private
    let xf := x ctx s |>.format
    let yf := y ctx s |>.format
    .atom (xf ++ yf)

/-- Set the precedence of the `fmt` to `prec` without changing format. -/
private def setPrec (fmt : StrataFormat) (prec : Nat) : StrataFormat := fun c s =>
  { format := fmt c s |>.format, prec := prec }

/-- Add parenthesis as needed to `fmt` to ensure precedence at least `p` -/
private def ensurePrec (fmt : StrataFormat) (prec : Nat) : StrataFormat := fun c s =>
  let r := fmt c s
  if r.prec < prec then
    .atom f!"({r.format})"
  else
    r

def withState (f : FormatState → FormatState) (fmt : StrataFormat) : StrataFormat := fun c s =>
  fmt c (f s)

private def nest (n : Nat) (fmt : StrataFormat) : StrataFormat := fun c s =>
  let ⟨r, p⟩ := fmt c s
  ⟨.nest n r, p⟩

end StrataFormat

syntax:max "mf!" interpolatedStr(term) : term

macro_rules
  | `(mf! $interpStr) => do interpStr.expandInterpolatedStr (← `(StrataFormat)) (← `(mformat))

instance : ToStrataFormat QualifiedIdent where
  mformat (ident : QualifiedIdent) c s := private
    if ident.dialect ∈ s.openDialects then
      -- The parser reads `Init.Type` through the token `Type`, so it is not pipe-delimited.
      .atom (formatIdent ident.name (if ident == q`Init.Type then {} else c.keywords))
    else
      .atom f!"{ident.dialect}.{formatIdent ident.name}"

namespace TypeExprF

private protected def mformat : TypeExprF α → StrataFormat
| .ident _ tp a => a.attach.foldl (init := mformat tp) fun m ⟨e, _⟩ =>
  mf!"{m} {e.mformat.ensurePrec (appPrec + 1)}".setPrec appPrec
| .bvar _ idx => .bvar idx
| .tvar _ name => fun c s =>
  if c.opts.quoteKeywords then .atom (formatIdent name c.keywords) else mf!"{name}" c s
| .fvar _ idx a => a.attach.foldl (init := .fvar idx) fun m ⟨e, _⟩ =>
  mf!"{m} {e.mformat.ensurePrec (appPrec + 1)}".setPrec appPrec
| .arrow _ a r =>
  mf!"{a.mformat.ensurePrec (arrowPrec+1)} -> {r.mformat.ensurePrec arrowPrec}".setPrec arrowPrec

instance {α} : ToStrataFormat (TypeExprF α) where
  mformat e := private e.mformat

end TypeExprF

namespace PreType

private protected def mformat : PreType → StrataFormat
| .ident _ tp a => a.attach.foldl (init := mformat tp) (fun m ⟨e, _⟩ => mf!"{m} {e.mformat}")
| .bvar _ idx => .bvar idx
| .tvar _ name => mf!"{name}"
| .arrow _ a r => mf!"{a.mformat} -> {r.mformat}"
| .funMacro _ idx r => mf!"fnOf({StrataFormat.bvar idx}, {r.mformat})"

instance : ToStrataFormat PreType where
  mformat := private PreType.mformat

end PreType

namespace SyntaxCatF

private protected def mformat {α} (cat : SyntaxCatF α) : StrataFormat :=
  let init := mformat cat.name
  cat.args.foldl (init := init) (fun f a => mf!"{f} {a.mformat.ensurePrec (appPrec+1)}")
  decreasing_by
    rw [SyntaxCatF.sizeOf_spec cat]
    decreasing_tactic

instance {α} : ToStrataFormat (SyntaxCatF α)  where
  mformat := private SyntaxCatF.mformat

end SyntaxCatF

/--
This pretty prints the argument an op atom has.
-/
private def SyntaxDefAtom.formatArgs (opts : FormatOptions) (args : Array PrecFormat) (stx : SyntaxDefAtom) : Format :=
  match stx with
  | .ident lvl prec =>
    if h : lvl ≥ args.size then
      panic! s!"ident level {lvl} out of bounds"
    else
      let ⟨r, innerPrec⟩ := args[lvl]
      if prec > 0 ∧ (innerPrec ≤ prec ∨ opts.alwaysParen) then
        f!"({r})"
      else
        r
  | .str s => format s
  | .indent n f =>
    let r := Format.join (f.attach.map (fun ⟨a, _⟩ => a.formatArgs opts args) |>.toList)
    .nest n r

private def ppOp (opts : FormatOptions) (stx : SyntaxDef) (args : Array PrecFormat) : PrecFormat :=
  match stx with
  | .passthrough =>
    if h : args.size = 1 then
      args[0]
    else
      panic! "passthrough requires one argument"
  | .std atoms prec => ⟨Format.join ((·.formatArgs opts args) <$> atoms).toList, prec⟩

private abbrev FormatM := ReaderT FormatContext (StateM FormatState)

private def pformat {α} [ToStrataFormat α] (a : α) : FormatM PrecFormat :=
  fun c s => (mformat a c s, s)

/-- Wrap a finished literal string as a max-precedence `PrecFormat` (literals
    never need parentheses), matching the precedence `ofFormat` assigns to
    numeric/decimal literals. -/
private def pformatStr (s : String) : PrecFormat :=
  { format := Format.text s, prec := maxPrec + 1 }

/-- Resolve the format mode for a literal of the given kind. A caller's explicit
    render-context override (`FormatOptions.formatModes`) wins; otherwise the mode
    declared on the current argument (`@[<mode>]`) applies; absent both, the
    type's default mode. -/
private def resolveMode (ctx : FormatContext) (kind : String) : FormatMode :=
  match ctx.opts.formatModes[kind]? with
  | some m => m
  | none   => ctx.argFormatMode.getD .default

mutual

/- Renders expression to format and precedence of outmost operator. -/
private partial def ExprF.mformatM (e : ExprF α) (rargs : Array (ArgF α)  := #[]) : FormatM PrecFormat :=
  let ppArgs (f : Format) : FormatM PrecFormat :=
        if rargs.isEmpty then
          pure <| .atom f
        else do
          let args := (←rargs.reverse.mapM (·.mformatM)) |>.map (·.format)
          let args := Format.joinSep args.toList f!", "
          pure <| .mk f!"{f}({args})" callPrec
  match e with
  | .bvar _ idx => do
    ppArgs (← pformat (StrataFormat.bvar idx)).format
  | .fvar _ idx => do
    ppArgs (← pformat (StrataFormat.fvar idx)).format
  | .fn _ f => do
      match (←read).getFnDecl f with
      | some op =>
        let args := rargs.reverse
        let bindings := op.argDecls
        let .isTrue bsize := decEq args.size bindings.size
              | do
                -- When a function is applied to more arguments than it declares
                -- (e.g. a function returning a function type via funMacro),
                -- format it with its declared args, then apply the remaining
                -- args with call syntax.
                let declArgCount := bindings.size
                if rargs.size > declArgCount then
                  let fnArgs := args.take declArgCount
                  let extraArgs := args.drop declArgCount
                  let .isTrue bsize' := decEq fnArgs.size bindings.size
                        | return panic! "Mismatch betweeen binding and arg size" -- nopanic:ok
                  let argResults ← do
                        match formatArguments (← read) (← get) bindings ⟨fnArgs, bsize'⟩ with
                        | .ok r => pure r
                        | .error e => return panic! e -- nopanic:ok
                  let fnFmt := ppOp (← read).opts op.syntaxDef (Prod.fst <$> argResults)
                  let extraFmts := (← extraArgs.mapM (·.mformatM)) |>.map (·.format)
                  let extraFmts := Format.joinSep extraFmts.toList f!", "
                  return .mk f!"({fnFmt.format})({extraFmts})" callPrec
                else
                  -- Fewer args than expected: format as name(args)
                  ppArgs f.fullName
        let argResults ← do
              match formatArguments (← read) (← get) bindings ⟨args, bsize⟩ with
              | .ok r => pure r
              | .error e => return panic! e
        pure <| ppOp (← read).opts op.syntaxDef (Prod.fst <$> argResults)
      | none => ppArgs f.fullName
  | .app _ f a => f.mformatM (rargs.push a)

private partial def ArgF.mformatM {α} : ArgF α → FormatM PrecFormat
| .op o => o.mformatM
| .expr e => e.mformatM
| .type e => pformat e
| .cat e => pformat e
| .ident _ x => return .atom (formatIdent x (← read).keywords)
| .num _ x => pformat x
| .decimal _ v => do
    let ctx ← read
    pure <| pformatStr (StrataRender.render (resolveMode ctx "decimal") v)
| .strlit _ s => do
    let ctx ← read
    let escape := ctx.opts.customStringEscaper.getD escapeStringLit
    return .atom (.text (escape s))
| .bytes _ v => return .atom <| .text <| ByteArray.escapeBytes v
| .option _ ma =>
  match ma with
  | none => pure (.atom .nil)
  | some a => a.mformatM
| .seq _ sep entries => do
  match sep with
  | .none =>
    .atom <$> entries.foldlM (init := .nil) fun p a =>
      return (p ++ (← a.mformatM).format)
  | .comma =>
    if z : entries.size = 0 then
      pure (.atom .nil)
    else do
      let f i q s := return s ++ ", " ++ (← entries[i].mformatM).format
      let a := (← entries[0].mformatM).format
      .atom <$> entries.size.foldlM f (start := 1) a
  | .space =>
    if z : entries.size = 0 then
      pure (.atom .nil)
    else do
      let f i q s := return s ++ " " ++ (← entries[i].mformatM).format
      let a := (← entries[0].mformatM).format
      .atom <$> entries.size.foldlM f (start := 1) a
  | .spacePrefix =>
    .atom <$> entries.foldlM (init := .nil) fun p a =>
      return (p ++ " " ++ (← a.mformatM).format)
  | .newline =>
    if z : entries.size = 0 then
      pure (.atom .nil)
    else do
      let f i q s := return s ++ "\n" ++ (← entries[i].mformatM).format
      let a := (← entries[0].mformatM).format
      .atom <$> entries.size.foldlM f (start := 1) a
  | .semicolonNewline =>
    if z : entries.size = 0 then
      pure (.atom .nil)
    else do
      let f i q s := return s ++ ";\n" ++ (← entries[i].mformatM).format
      let a := (← entries[0].mformatM).format
      .atom <$> entries.size.foldlM f (start := 1) a

private partial def ppArgs (f : StrataFormat) (rargs : Array Arg) : FormatM PrecFormat :=
  if rargs.isEmpty then
    pformat f
  else do
    let f := (← pformat f).format
    let pf := (← rargs.back!.mformatM).format
    let init := f!"{f}({pf}"
    let rargs := rargs.pop
    let r ← rargs.foldrM (init := init) (fun a r => return f!"{r},{(←a.mformatM).format})")
    pure <| .atom f!"{r})"

private partial def formatArguments (c : FormatContext) (initState : FormatState) (argDecls : ArgDecls) (args : Vector (ArgF α) argDecls.size) : Except String (Array (PrecFormat × FormatState)) :=
  let rec aux (a : Array (PrecFormat × FormatState)) :=
        let lvl := a.size
        if h : lvl < argDecls.size then do
          let s ← do
                match ← argDecls.argScopeLevel ⟨lvl, h⟩ with
                | none =>
                  pure initState
                | some ⟨alvl, aisLt⟩  =>
                  have _ : alvl < a.size := by simp at aisLt; omega
                  pure a[alvl].snd
          -- An `@[<mode>]` on the argument declaration supplies a default render
          -- mode for its literal, without a render-context override. A caller's
          -- explicit `formatModes` entry still wins (applied in `resolveMode`),
          -- so this only fills in when the caller left the kind unset. An
          -- unrecognized marker name is a hard error, not a silent default.
          let argMode ← (argDecls[lvl].metadata.formatModeName?).mapM FormatMode.ofString
          let c := c.withArgFormatMode argMode
          aux (a.push (args[lvl].mformatM c s))
        else
          .ok a
  aux (.mkEmpty argDecls.size)

private partial def OperationF.mformatM (op : OperationF α) : FormatM PrecFormat := do
  match (← read).getOpDecl op.name with
  | some decl =>
    let bindings := decl.argDecls
    let .isTrue bsize := decEq op.args.size bindings.size
          | return panic! "Mismatch betweeen binding and arg size"
    let args : Vector _ bindings.size := ⟨op.args, bsize⟩
    let argResults ← do
          match formatArguments (← read) (← get) bindings args with
          | .ok r => pure r
          | .error e => return panic! e
    let fmt := ppOp (← read).opts decl.syntaxDef (Prod.fst <$> argResults)
    match decl.metadata.resultLevel bindings.size with
    | .ok (some idx) =>
      if h : idx.val < argResults.size then
        set argResults[idx.val].snd
      else
        panic! "result scope index out of bounds"
    | .ok none => pure ()
    | .error e => return panic! e
    for b in decl.newBindings do
      match args[b.nameIndex.toLevel] with
      | .ident _ e =>
        modify (·.pushBinding e)
      | _ =>
        return panic! s!"Expected ident at {b.nameIndex.toLevel}."
    return fmt
  | none =>
    -- FIXME: Consider reporting error here.
    let initCtx ← read
    let initState ← get
    let args := op.args |>.map (ArgF.mformatM · initCtx initState |>.fst |>.format) |>.toList
    return .atom f!"{op.name.fullName}({Format.joinSep args ", "});"

end

instance ExprF.instToStrataFormat {α} : ToStrataFormat (ExprF α) where
  mformat e c s := private e.mformatM #[] c s |>.fst

instance ArgF.instToStrataFormat {α} : ToStrataFormat (ArgF α) where
  mformat a c s := private a.mformatM c s |>.fst


namespace OperationF

instance {α} : ToStrataFormat (OperationF α) where
  mformat o c s := private o.mformatM c s |>.fst

/--
This renders an operation returning its string representation and new state.
-/
def render {α} (op : OperationF α) (ctx : FormatContext) (s : FormatState) : String × FormatState :=
  let (f, s) := op.mformatM ctx s
  (f.format.render, s)

end OperationF

namespace MetadataArg

private protected def mformat : MetadataArg → StrataFormat
| .bool b => if b then mf!"true" else mf!"false"
| .num n => mformat n
| .catbvar idx => StrataFormat.bvar idx
| .option ma =>
  match ma with
  | none => mf!"none"
  | some a => a.mformat
| .functionTemplate t => mf!"functionTemplate({repr t})"

instance : ToStrataFormat MetadataArg where
  mformat := private MetadataArg.mformat

end MetadataArg

namespace MetadataAttr

instance : ToStrataFormat MetadataAttr where
  mformat a := private
    if a.args.isEmpty then
      mformat a.ident
    else
      mf!"{a.ident}({StrataFormat.sepBy a.args ","})"

end MetadataAttr

instance Metadata.instToStrataFormat : ToStrataFormat Metadata where
  mformat m := private
    if m.toArray.isEmpty then
      .nil
    else
      mf!"@[{StrataFormat.sepBy m.toArray ", "}]"

namespace ArgDeclKind

instance : ToStrataFormat ArgDeclKind where
  mformat private
  | .cat c => mformat c
  | .type tp => mformat tp

end ArgDeclKind

namespace ArgDecl

instance : ToStrataFormat ArgDecl where
  mformat b := private
    let r := mf!"{b.ident} : {b.kind}"
    if b.metadata.isEmpty then
      r
    else
      mf!"{b.metadata} {r}"

end ArgDecl

namespace ArgDecls

private def mformatAux (f : Format) (c : FormatContext) (s : FormatState) (a : ArgDecls) (idx : Nat) : Format × FormatState :=
  if h : idx < a.size then
    let b := a[idx]
    mformatAux (f ++ ", " ++ cformat b c s) c (s.pushBinding b.ident) a (idx + 1)
  else
    (f ++ ")", s)

private protected def mformat (c : FormatContext) (s : FormatState) (l : ArgDecls) : Format × FormatState :=
  if h : 0 < l.size then
    let b := l[0]
    mformatAux ("(" ++ cformat b c s) c (s.pushBinding b.ident) l 1
  else
    ("()", s)

instance : ToStrataFormat ArgDecls where
  mformat l c s := private .atom (l.mformat c s |>.fst)

/- Format `fmt` in a context with additional bindings `b`. -/
private protected def formatIn [ToStrataFormat α] (b : ArgDecls) (fmt : α) : StrataFormat := fun c s =>
  StrataDDM.mformat fmt c (b.toArray.foldl (init := s) (·.pushBinding ·.ident))

end ArgDecls

namespace SyntaxDefAtom

private protected def mformat : SyntaxDefAtom → StrataFormat
| .ident lvl prec => mf!"{StrataFormat.lvlVar lvl}:{prec}" -- FIXME.  This may be wrong.
| .str lit => mformat (escapeStringLit lit)
| .indent n f =>
  let r := f.attach.map fun ⟨a, _⟩ => a.mformat
  let f := StrataFormat.sepBy r " "
  mf!"indent({n}, {f})"

instance : ToStrataFormat SyntaxDefAtom where
  mformat := private SyntaxDefAtom.mformat

end SyntaxDefAtom

namespace SyntaxDef

instance : ToStrataFormat SyntaxDef where
  mformat := private fun
    | .std atoms _ => .sepBy atoms " "
    | .passthrough => mf!"{StrataFormat.lvlVar 0}:{0}"

end SyntaxDef

instance SynCatDecl.instToStrataFormat : ToStrataFormat SynCatDecl where
  mformat d := private
    let args : StrataFormat := .join <| d.argNames.map (mf!" {·}") |>.toList
    mf!"category {d.name}{args};\n"

namespace OpDecl

instance : ToStrataFormat OpDecl where
  mformat d := private
    let argDecls := d.argDecls
    let mdf := if d.metadata.isEmpty then .nil else mf!"{argDecls.formatIn d.metadata} "
    let argDeclsF := if argDecls.isEmpty then mf!"" else mf!" {argDecls}"
    mf!"{mdf}op {d.name}{argDeclsF} : {d.category} => {argDecls.formatIn d.syntaxDef};\n"

end OpDecl

instance TypeDecl.instToStrataFormat : ToStrataFormat TypeDecl where
  mformat d := private
    let params := d.argNames
    let params := if params.isEmpty then
                    mf!""
                  else
                    let p := d.argNames.map fun anm => mf!"{anm.val} : Type"
                    mf! " " ++ StrataFormat.sepBy p ", "
    mf!"type {d.name}{params};\n"

instance FunctionDecl.instToStrataFormat : ToStrataFormat FunctionDecl where
  mformat d := private
    let argDecls := d.argDecls
    let mdf := if d.metadata.isEmpty then .nil else mf!"{argDecls.formatIn d.metadata} "
    let argDeclsF := if argDecls.isEmpty then mf!"" else mf!" {argDecls}"
    let result := argDecls.formatIn d.result
    mf!"{mdf}fn {d.name}{argDeclsF} : {result} => {d.argDecls.formatIn d.syntaxDef};\n"

namespace MetadataArgType

private protected def mformat : MetadataArgType → StrataFormat
| .num => mf!"Num"
| .ident => mf!"Ident"
| .bool => mf!"Bool"
| .opt tp => mf!"Option {tp.mformat |>.ensurePrec (appPrec + 1)}" |>.setPrec appPrec
| .functionTemplate => mf!"FunctionTemplate"

instance : ToStrataFormat MetadataArgType where
  mformat := private MetadataArgType.mformat

end MetadataArgType

instance MetadataDecl.instToStrataFormat : ToStrataFormat MetadataDecl where
  mformat d := private
    if d.args.isEmpty then
      mf!"metadata {d.name};\n"
    else
      let ppArg a := mf! "{a.ident} : {a.type}"
      mf!"metadata {d.name}({StrataFormat.sepBy (d.args |>.map ppArg) ", "});\n"

instance Decl.instToStrataFormat : ToStrataFormat Decl where
  mformat private
  | .syncat d => mformat d
  | .op d => mformat d
  | .type d => mformat d
  | .function d => mformat d
  | .metadata d => mformat d

namespace DialectMap

/--
Pretty print the dialect with the given name in the map.
-/
protected def format (dialects : DialectMap) (name : DialectName) (mem : name ∈ dialects) (opts : FormatOptions := {}) : Format :=
  let d := dialects[name]
  -- `quoteKeywords` quotes the names that the tokens of `dialects` make unreadable, but a dialect
  -- definition is read with StrataDDL's tokens, so the option is off here.
  let c := FormatContext.ofDialects dialects {} { opts with quoteKeywords := false }
  let imports := dialects.importedDialects name mem
  let s : FormatState := { openDialects := imports.toList.foldl (init := {}) fun s d => s.insert d.name }
  let f := f!"dialect {name};\n"
  let f := d.imports.foldl (init := f) fun f i =>
    if i = "Init" then
      f
    else
      f!"{f}import {i}\n"
  d.declarations.foldl (init := f) fun f d => f ++ (mformat d c s).format

end DialectMap

namespace Program

protected def formatContext (p : Program) (opts : FormatOptions) : FormatContext :=
  .ofDialects p.dialects p.globalContext opts

protected def formatState (p : Program) : FormatState where
  openDialects := p.dialects.toList.foldl (init := {}) fun a d => a.insert d.name

protected def format (p : Program) (opts : FormatOptions := {}) : Format :=
  let c := p.formatContext opts
  let s := p.formatState
  p.commands.foldl (init := f!"program {p.dialect};\n") fun f cmd =>
    f ++ (mformat cmd c s).format

protected def toString (p : Program) (opts : FormatOptions := {}) : String :=
  p.format opts |>.render

instance : ToString Program where
  toString p := p.toString
protected def ppDialect! (p : Program) (name : DialectName := p.dialect) (opts : FormatOptions := {}) : Format :=
  if mem : name ∈ p.dialects then
    p.dialects.format name mem opts
  else
    panic! s!"Unknown dialect {name}"

end Program

end StrataDDM
end
