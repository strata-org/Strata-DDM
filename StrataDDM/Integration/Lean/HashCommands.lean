/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Lean.Elab.Command
public meta import StrataDDM.Elab
public import StrataDDM.SourcedProgram
public meta import StrataDDM.Integration.Lean.Env
public meta import StrataDDM.Integration.Lean.ToExpr
public meta import StrataDDM.TaggedRegions
import StrataDDM.Elab.DeclM
import StrataDDM.Integration.Lean.Env
import StrataDDM.Integration.Lean.ToExpr
import StrataDDM.TaggedRegions

open Lean
open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Command (CommandElab CommandElabM liftCoreM)
open Lean.Elab.Term (TermElab)
open Lean.Parser (InputContext)
open System (FilePath)
open StrataDDM.Lean (arrayToExpr listToExpr)

namespace StrataDDM

public class HasInputContext (m : Type → Type _) [Functor m] where
  getInputContext : m InputContext
  getFileName : m FilePath :=
    (fun ctx => FilePath.mk ctx.fileName) <$> getInputContext

meta section

deriving instance Lean.ToExpr for SourcedProgram

public instance : HasInputContext CommandElabM where
  getInputContext := do
    let ctx ← read
    pure {
      inputString := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap := ctx.fileMap
    }
  getFileName := return (← read).fileName

public instance : HasInputContext CoreM where
  getInputContext := do
    let ctx ← read
    pure {
      inputString := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap := ctx.fileMap
    }
  getFileName := return (← read).fileName

def mkScopedName {m} [Monad m] [MonadError m] [MonadEnv m] [MonadResolveName m] (name : Name) : m Name := do
  let scope ← getCurrNamespace
  let fullName := scope ++ name
  let env ← getEnv
  if env.contains fullName then
    throwError s!"Cannot define {name}: {fullName} already exists."
  return fullName

def offsetPos (base : String.Pos.Raw) (pos : String.Pos.Raw) : String.Pos.Raw :=
  ⟨base.byteIdx + pos.byteIdx⟩

def offsetSourceRange (base : String.Pos.Raw) (sr : SourceRange) : SourceRange :=
  { start := offsetPos base sr.start, stop := offsetPos base sr.stop }

def offsetMessage
    (fullCtx snippetCtx : InputContext)
    (base : String.Pos.Raw)
    (msg : Lean.Message) : Lean.Message :=
  let pos := fullCtx.fileMap.toPosition (offsetPos base (snippetCtx.fileMap.ofPosition msg.pos))
  let endPos := msg.endPos.map fun endPos =>
    fullCtx.fileMap.toPosition (offsetPos base (snippetCtx.fileMap.ofPosition endPos))
  { msg with fileName := fullCtx.fileName, pos := pos, endPos := endPos }

/--
Add a definition to environment and compile it.
-/
public def addDefn (name : Lean.Name)
            (type : Lean.Expr)
            (value : Lean.Expr)
            (levelParams : List Name := [])
            (hints : ReducibilityHints := .abbrev)
            (safety : DefinitionSafety := .safe)
            (all : List Lean.Name := [name])
            (isMeta : Bool := false) : CoreM Unit := do
  addAndCompile (markMeta := isMeta) <| .defnDecl {
    name := name
    levelParams := levelParams
    type := type
    value := value
    hints := hints
    safety := safety
    all := all
  }

public section

/--
Declare dialect and add to environment.
-/
def declareDialect (d : Dialect) : CommandElabM Unit := do
  -- Identifier for dialect
  let dialectName := Name.anonymous |>.str d.name
  let scope := (← get).scopes.head!
  let env ← getEnv
  -- A file not using the module system has no `public section`, so treat it as
  -- public; `Gen.lean`'s `resolveScopedName` does the same.
  let isPublic := !env.header.isModule || scope.isPublic
  let isMeta := scope.isMeta

  let mut dialectAbsName ← mkScopedName dialectName
  -- Identifier for dialect map
  let mut mapAbsName ← mkScopedName (Name.anonymous |>.str s!"{d.name}_map")
  if isPublic = false then
    dialectAbsName := mkPrivateName env dialectAbsName
    mapAbsName := mkPrivateName env mapAbsName

  let dialectTypeExpr := mkConst ``Dialect
  liftCoreM <| addDefn dialectAbsName dialectTypeExpr (toExpr d) (isMeta := isMeta)
  -- Add dialect to environment
  modifyEnv fun env =>
    dialectExt.modifyState env (·.addDialect! d dialectAbsName (isExported := isPublic))
  -- Create term to represent minimal DialectMap with dialect.
  let s := (dialectExt.getState (←Lean.getEnv))
  let .isTrue mem := (inferInstance : Decidable (d.name ∈ s.loaded.dialects))
    | throwError "Internal error with unknown dialect"
  let openDialects := s.loaded.dialects.importedDialects d.name mem |>.toList
  let exprD (d : Dialect) : CommandElabM Lean.Expr := do
      let some name := s.nameMap[d.name]?
        | throwError s!"Unknown dialect {d.name}"
      return mkConst name
  let de ← openDialects.mapM exprD
  let mapValue := mkApp (mkConst ``DialectMap.ofList!)
                        (listToExpr .zero dialectTypeExpr de)
  liftCoreM <| addDefn mapAbsName (mkConst ``DialectMap) mapValue (isMeta := isMeta)

declare_tagged_region command strataDialectCommand "#dialect" "#end"

@[command_elab strataDialectCommand]
def strataDialectImpl: CommandElab := fun (stx : Syntax) => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← HasInputContext.getInputContext
  let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
  let fm ← DialectFileMap.new loaded
  let (d, s) ← Elab.elabDialect fm inputCtx p e
  if !s.errors.isEmpty then
    for e in s.errors do
      logMessage e
    return
  -- Add dialect to command environment
  declareDialect d

declare_tagged_region term strataProgram "#strata" "#end"

@[term_elab strataProgram]
meta def strataProgramImpl : TermElab := fun stx tp => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let fullInputCtx ← (HasInputContext.getInputContext : CoreM _)
  let snippet := String.Pos.Raw.extract fullInputCtx.inputString p e
  let inputCtx : InputContext := {
    inputString := snippet
    fileName := fullInputCtx.fileName
    fileMap := FileMap.ofString snippet
  }
  let s := (dialectExt.getState (←Lean.getEnv))
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let baseLine : Nat := (fullInputCtx.fileMap.toPosition p).line
  match Elab.elabProgram s.loaded leanEnv inputCtx 0 inputCtx.endPos with
  | .ok pgm =>
    let commands := pgm.commands.map (fun cmd => cmd.mapAnn (offsetSourceRange p))
    let pgm := Program.create pgm.dialects pgm.dialect commands
    -- Get Lean name for dialect
    let some (.str name root) := s.nameMap[pgm.dialect]?
      | throwError s!"Unknown dialect {pgm.dialect}"
    let commandType := mkConst ``Operation
    -- Decide whether the generated `command✝` definitions should be `meta`, so a
    -- `meta` consumer can reference them (and, symmetrically, a non-`meta` consumer
    -- keeps them regular). We are in a `meta` context when any of:
    --   * we are inside a `meta section`;
    --   * the enclosing declaration is already tagged `meta` (e.g. a user `meta def`);
    --   * the enclosing declaration is the `_eval` aux def that `#eval`/`#guard_msgs`
    --     synthesize. `#eval` declares it with `computeKind := .meta` but elaborates
    --     it under `withoutModifyingEnv`, so the `meta` tag is not visible on our
    --     environment branch while this `#strata` body is elaborated. Its name is a
    --     fixed `_eval` literal placed directly on the private prefix
    --     (`_private.<module>.0._eval`, see Lean's `BuiltinEvalCommand`); match that
    --     shape precisely so we don't also treat a user's own `_eval` declaration as
    --     an eval aux def.
    let declName? := (← read).declName?
    let enclosingIsEval := declName?.any fun
      | .str p "_eval" => Lean.isPrivatePrefix p
      | _ => false
    let isMeta := (← read).isMetaSection ||
      declName?.any (Lean.isMarkedMeta (← getEnv)) ||
      enclosingIsEval
    let cmdToExpr (cmd : Operation) : CoreM Lean.Expr := do
          -- Private, hygienic name: these are internal aux defs, never public API.
          -- Being private also avoids the stricter "public `meta` def" visibility rule,
          -- which would otherwise force every referenced AST decl to be `public meta`.
          let n := mkPrivateName (← getEnv) (← mkFreshUserName `command)
          addDefn n commandType (toExpr cmd) (isMeta := isMeta)
          pure <| mkConst n
    let commandExprs ← monadLift <| pgm.commands.mapM cmdToExpr
    let pgmExpr : Lean.Expr :=
      astExpr! Program.create
        (mkConst (name |>.str s!"{root}_map"))
        (toExpr pgm.dialect)
        (arrayToExpr .zero commandType commandExprs)
    return mkApp5 (mkConst ``SourcedProgram.mk)
      pgmExpr
      (toExpr snippet)
      (toExpr (p.byteIdx : Nat))
      (toExpr baseLine)
      (toExpr fullInputCtx.fileName)
  | .error errors =>
    for e in errors do
      logMessage (offsetMessage fullInputCtx inputCtx p e)
    return mkApp2 (mkConst ``sorryAx [1]) (toTypeExpr SourcedProgram) (toExpr true)

syntax (name := loadDialectCommand) "#load_dialect" str : command

/-- Derive the package source root from a module's file path and name by
stripping one directory component per name part. For example, given
`/repo/Strata/Languages/Foo.lean` and module name `Strata.Languages.Foo`,
returns `/repo`. -/
def getModuleRoot (path : FilePath) (modName : Name) : Except String FilePath := do
  let depth := modName.getNumParts
  let some dir := path.parent
    | throw s!"cannot get parent of file path '{path}'"
  let mut dir := dir
  for _ in List.range (depth - 1) do
    let some parent := dir.parent
      | throw s!"cannot resolve package root from '{path}' \
          with module '{modName}' (ran out of parent directories)"
    dir := parent
  pure dir

/-- Resolve a relative path against the current package's source root.
Absolute paths are returned unchanged. -/
private def resolveLeanRelPath (path : FilePath) : CommandElabM FilePath := do
  if path.isAbsolute then
    return path
  let mut currentFileName : FilePath := (← read).fileName
  if currentFileName.isRelative then
    currentFileName := (← IO.currentDir) / currentFileName
  let modName := (← getEnv).mainModule
  match getModuleRoot currentFileName modName with
  | .ok dir => pure <| dir / path
  | .error msg => throwError msg

@[command_elab loadDialectCommand]
def loadDialectImpl : CommandElab := fun (stx : Syntax) => do
  match stx with
  | `(command|#load_dialect $pathStx) =>
    let dialectPath : FilePath := pathStx.getString
    let absPath ← resolveLeanRelPath dialectPath
    if ! (← absPath.pathExists) then
      throwErrorAt pathStx "Could not find file {dialectPath}"
    let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
    let fm ← DialectFileMap.new loaded
    let r ← Elab.loadDialectFromFile fm (path := dialectPath) (actualPath := absPath)
    -- Add dialect to command environment
    match r with
    | .ok d =>
      declareDialect d
    | .error errorMessages =>
      assert! errorMessages.size > 0
      throwError (← Elab.mkErrorReport errorMessages)
  | _ =>
    throwUnsupportedSyntax

end
end

end StrataDDM
