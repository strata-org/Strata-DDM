/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module


public import StrataDDM.Elab.LoadedDialects
import all StrataDDM.Util.Lean
import all StrataDDM.Util.PrattParsingTables

set_option autoImplicit false

open Lean (Syntax Message)

open StrataDDM.Parser (DeclParser InputContext Parser ParsingContext)

public section
namespace StrataDDM

namespace PrattParsingTableMap

private def addSynCat! (tables : PrattParsingTableMap) (dialect : String) (decl : SynCatDecl) : PrattParsingTableMap :=
  let cat : QualifiedIdent := { dialect, name := decl.name }
  if cat ∈ tables then
    panic! s!"{cat} already declared."
  else
    tables.insert cat {}

private def addParserToCat! (tables : PrattParsingTableMap) (dp : DeclParser) : PrattParsingTableMap :=
  tables.alter dp.category fun mtables =>
    match mtables with
    | none => panic s!"Category {dp.category.fullName} not declared."
    | some tables =>
      let r := tables |>.addParser dp.isLeading dp.parser dp.outerPrec
      some r

private def addDialect! (tables : PrattParsingTableMap) (dialect : Dialect) (parsers : Array DeclParser) : PrattParsingTableMap :=
  dialect.syncats.fold (init := tables) (·.addSynCat! dialect.name ·)
  |> parsers.foldl PrattParsingTableMap.addParserToCat!

end PrattParsingTableMap

namespace Elab

-- Metadata syntax

syntax "md{" withoutPosition(sepBy(term, ", ")) "}" : term

macro_rules
  | `(md{ $elems,* }) => `(Metadata.ofArray (List.toArray [ $elems,* ]))

-- ElabClass

class ElabClass (m : Type → Type) extends Monad m where
  getInputContext : m InputContext
  getDialects : m DialectMap
  getOpenDialects : m (Std.HashSet DialectName)
  getGlobalContext : m GlobalContext
  getErrorCount : m Nat
  logErrorMessage : Message → m Unit

export ElabClass (logErrorMessage)

/--
Runs action and returns result along with Bool that is true if
action ran without producing errors.
-/
def runChecked {m α} [ElabClass m] (action : m α) : m (α × Bool) := do
  let errorCount ← ElabClass.getErrorCount
  let r ← action
  return (r, errorCount = (← ElabClass.getErrorCount))

def mkErrorMessage (inputCtx : InputContext) (loc : SourceRange) (msg : String) (isSilent : Bool := false) : Message :=
  let m := Lean.mkStringMessage inputCtx loc.start msg (isSilent := isSilent)
  if loc.isNone then m else { m with endPos := inputCtx.fileMap.toPosition loc.stop }

def logError {m} [ElabClass m] (loc : SourceRange) (msg : String) (isSilent : Bool := false) : m Unit := do
  let inputCtx ← ElabClass.getInputContext
  logErrorMessage (mkErrorMessage inputCtx loc msg isSilent)

def logErrorMF {m} [ElabClass m] (loc : SourceRange) (msg : StrataFormat) (isSilent : Bool := false) (globalContext? : Option GlobalContext := none) : m Unit := do
  let inputCtx ← ElabClass.getInputContext
  let gctx ← match globalContext? with
    | some gctx => pure gctx
    | none => ElabClass.getGlobalContext
  let c : FormatContext := .ofDialects (← ElabClass.getDialects) gctx {}
  let s : FormatState := { openDialects := ← ElabClass.getOpenDialects }
  let msg := msg c s |>.format |>.pretty
  logErrorMessage (mkErrorMessage inputCtx loc msg isSilent)

-- DeclM

structure DeclContext where
  inputContext : InputContext
  stopPos : String.Pos.Raw
  -- Map from dialect names to the dialect definition
  loader : LoadedDialects
  /-- Flag indicating imports are missing (silences some errors). -/
  missingImport : Bool
  /-- When false, type inference and unification are skipped during elaboration. -/
  typecheck : Bool := true

namespace DeclContext

def empty : DeclContext where
  inputContext := default
  loader := .empty
  stopPos := 0
  missingImport := false

end DeclContext

/-- Represents an entity with some form of unique string name. -/
class NamedValue (α : Type) where
  name : α → String

abbrev ValueWithName (α : Type) [NamedValue α] (name : String) :=
  { d : α // NamedValue.name d = name }

/--
  Map metadata attribute names to any declarations with that name that
  are in the current scope.
-/
structure NamedValueMap (α : Type) [NamedValue α] where
  map : Std.DHashMap String (λname => Array (DialectName × ValueWithName α name)) := {}
deriving Inhabited

/--
  Map metadata attribute names to any declarations with that name that
  are in the current scope.
-/
structure MetadataDeclMap where
  map : Std.DHashMap String fun name =>
          Array (DialectName × { d : MetadataDecl // d.name = name }) :=
    {}
deriving Inhabited

namespace MetadataDeclMap

def add (m : MetadataDeclMap) (dialect : DialectName) (decl : MetadataDecl) : MetadataDeclMap where
  map := m.map.alter decl.name fun ma => some <| ma.getD #[] |>.push (dialect, ⟨decl, rfl⟩)

def addDialect (m : MetadataDeclMap) (dialect : Dialect) :=
  dialect.metadata.fold (init := m) (·.add dialect.name ·)

def get (m : MetadataDeclMap) (name : String) : Array (DialectName × { d : MetadataDecl // d.name = name }) :=
  m.map.getD name #[]

end MetadataDeclMap

inductive TypeOrCatDecl where
| syncat (d : SynCatDecl)
| type (d : TypeDecl)
deriving Inhabited

def TypeOrCatDecl.name : TypeOrCatDecl → String
| .syncat d => d.name
| .type d => d.name

def TypeOrCatDecl.decl : TypeOrCatDecl → Decl
| .syncat d => .syncat d
| .type d => .type d

/--
  Map metadata attribute names to any declarations with that name that
  are in the current scope.
-/
structure TypeOrCatDeclMap where
  map : Std.DHashMap String fun name =>
          Array (DialectName × { d : TypeOrCatDecl // d.name = name }) :=
    {}
deriving Inhabited

namespace TypeOrCatDeclMap

def add (m : TypeOrCatDeclMap) (dialect : DialectName) (decl : TypeOrCatDecl) : TypeOrCatDeclMap where
  map := m.map.alter decl.name fun ma => some <| ma.getD #[] |>.push (dialect, ⟨decl, rfl⟩)

def addSynCat (m : TypeOrCatDeclMap) (dialect : DialectName) (d : SynCatDecl) :=
  m.add dialect (.syncat d)

def addType (m : TypeOrCatDeclMap) (dialect : DialectName) (d : TypeDecl) :=
  m.add dialect (.type d)

def addDialect (m : TypeOrCatDeclMap) (dialect : Dialect) :=
  let m := dialect.syncats.fold (init := m) (·.addSynCat dialect.name ·)
  dialect.types.fold (init := m) (·.addType dialect.name ·)

def get (m : TypeOrCatDeclMap) (name : String) : Array (DialectName × { d : TypeOrCatDecl // d.name = name }) :=
  m.map.getD name #[]

end TypeOrCatDeclMap

private def initTokenTable : Lean.Parser.TokenTable :=
  initParsers.fixedParsers.fold (init := {}) fun tt _ p => Parser.TokenTable.addParser tt p

structure DeclState where
  -- Fixed parser map
  fixedParsers : ParsingContext := {}
  -- Dialects considered open for pretty-printing purposes.
  openDialects : Array DialectName := #["Init"]
  -- List of dialects considered open.
  openDialectSet : Std.HashSet DialectName := .ofArray openDialects
  /-- Map for looking up types and categories by name. -/
  typeOrCatDeclMap : TypeOrCatDeclMap := {}
  /-- Map for looking up metadata by name. -/
  metadataDeclMap : MetadataDeclMap := {}
  -- Dynamic parser categories
  parserMap : PrattParsingTableMap := {}
  -- Token table for parsing
  tokenTable : Lean.Parser.TokenTable := {}
  -- Operations at the global level
  globalContext : GlobalContext := {}
  -- String position in file.
  pos : String.Pos.Raw := 0
  -- Errors found in elaboration.
  errors : Array Message := #[]
deriving Inhabited

namespace DeclState

def addParserToCat! (s : DeclState) (dp : DeclParser) : DeclState :=
  assert! dp.category ∈ s.parserMap
  { s with
      tokenTable := Parser.TokenTable.addParser s.tokenTable dp.parser
      parserMap := s.parserMap.addParserToCat! dp
  }

def addSynCat! (s : DeclState) (dialect : String) (decl : SynCatDecl) : DeclState :=
  { s with parserMap := s.parserMap.addSynCat! dialect decl }

/--
Opens the dialect definition dialect in the parser so it is visible to parser, but not
part of environment.  This is used for dialect definitions.
-/
def openParserDialect! (s : DeclState) (loader : LoadedDialects) (dialect : Dialect) : DeclState :=
  let name := dialect.name
  let parsers := loader.dialectParsers.getD name #[]
  { s with
    metadataDeclMap := s.metadataDeclMap.addDialect dialect
    parserMap := s.parserMap.addDialect! dialect parsers
    tokenTable := parsers.foldl (init := s.tokenTable) (Parser.TokenTable.addParser · ·.parser)
  }

mutual

partial def ensureLoaded! (s : DeclState) (loaded : LoadedDialects) (dialect : DialectName) : DeclState :=
  if dialect ∈ s.openDialectSet then
    s
  else
    match loaded.dialects[dialect]? with
    | none => panic! s!"Unknown dialect {dialect}"
    | some d => addDialect! s loaded d

/--
Opens the dialect (not must not already be open)
-/
partial def addDialect! (s : DeclState) (loaded : LoadedDialects) (dialect : Dialect) : DeclState :=
  assert! dialect.name ∉ s.openDialectSet
  let s := dialect.imports.foldl (init := s) fun s d =>
      assert! d ≠ dialect.name
      ensureLoaded! s loaded d
  let s := { s with
    openDialects := s.openDialects.push dialect.name
    openDialectSet := s.openDialectSet.insert dialect.name
    typeOrCatDeclMap := s.typeOrCatDeclMap.addDialect dialect
  }
  s.openParserDialect! loaded dialect

end

/--
Opens the dialect (not must not already be open)
-/
partial def openLoadedDialect! (s : DeclState) (loaded : LoadedDialects) (dialect : Dialect) : DeclState :=
  if dialect.name ∈ s.openDialectSet then
    panic s!"Dialect {dialect.name} already open"
  else
    s.addDialect! loaded dialect

def ofDialects (ds : LoadedDialects) : DeclState :=
  let s : DeclState := {
    openDialects := #[]
    openDialectSet := {}
    tokenTable := initTokenTable
  }
  ds.dialects.toList.foldl (init := s) fun s d => s.ensureLoaded! ds d.name

end DeclState

/--
Returns the number of errors together with the state. Not inlined, so the count
is computed before a following action consumes the state. Otherwise the
compiler may move the `size` after the action, keeping `errors` shared while the
action logs to it, so each logged error copies the array.
-/
@[noinline] def DeclState.errorCount (s : DeclState) : Nat × DeclState :=
  (s.errors.size, s)

@[reducible, expose]
def DeclM := ReaderT DeclContext (StateM DeclState)

namespace DeclM

instance : ElabClass DeclM where
  getInputContext := return (←read).inputContext
  getDialects := return (←read).loader.dialects
  getOpenDialects := return (←get).openDialectSet
  getGlobalContext := return (←get).globalContext
  getErrorCount := fun _ s => s.errorCount
  logErrorMessage msg :=
    modify fun s => { s with errors := s.errors.push msg }

end DeclM

def addTypeOrCatDecl (dialect : DialectName) (tpcd : TypeOrCatDecl) : DeclM Unit := do
  modify fun s => {
    s with typeOrCatDeclMap := s.typeOrCatDeclMap.add dialect tpcd
  }

end StrataDDM.Elab
end
