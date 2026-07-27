/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDDM.Elab.LoadedDialects
import StrataDDM.BuiltinDialects

namespace StrataDDM

open Lean Parser

public structure PersistentDialect where
  leanName : Lean.Name
  name : DialectName
  -- Names of dialects that are imported into this dialect
  imports : Array DialectName
  declarations : Array Decl
  -- Whether type inference/unification runs during elaboration for this
  -- dialect (set via `dialect_option typecheck off;`). Serialized here so the
  -- flag survives the export/import round-trip; otherwise a dialect defined in
  -- one module reverts to the `typecheck := true` default when imported into
  -- another.
  typecheck : Bool := true

namespace PersistentDialect

public def ofDialect (leanName : Name) (d : Dialect) : PersistentDialect where
  leanName := leanName
  name := d.name
  imports := d.imports
  declarations := d.declarations
  typecheck := d.typecheck

public def dialect (pd : PersistentDialect) : Dialect :=
  { Dialect.ofArray pd.name pd.imports pd.declarations with typecheck := pd.typecheck }

end PersistentDialect

public structure DialectState where
  loaded : Elab.LoadedDialects
  nameMap : Std.HashMap DialectName Name
  exportedDialects : Array (Name × Dialect)
deriving Inhabited

namespace DialectState

instance : EmptyCollection DialectState where
  emptyCollection := {
    loaded := .builtin,
    nameMap := .ofList [
      (initDialect.name, ``initDialect),
      (headerDialect.name, ``headerDialect),
      (StrataDDL.name, ``StrataDDL),
    ],
    exportedDialects := #[]
  }

public def addDialect! (s : DialectState) (d : Dialect) (name : Name) (isExported : Bool) : DialectState where
  loaded :=
    assert! d.name ∉ s.loaded.dialects
    s.loaded.addDialect! d
  nameMap :=
    assert! d.name ∉ s.nameMap
    s.nameMap.insert d.name name
  exportedDialects :=
    if isExported then
      s.exportedDialects.push (name, d)
    else
      s.exportedDialects

end DialectState

def mkImported (e : Array (Array PersistentDialect)) : ImportM DialectState :=
  return e.foldl (init := {}) fun s a => a.foldl (init := s) fun s d =>
    if d.name ∈ s.loaded.dialects then
      @panic _ ⟨s⟩ s!"Multiple dialects named {d.name} found in imports."
    else
      s.addDialect! d.dialect d.leanName (isExported := false)

def exportEntries (s : DialectState) : Array PersistentDialect :=
  s.exportedDialects.map fun (n, d) => .ofDialect n d

public initialize dialectExt : PersistentEnvExtension PersistentDialect (Name × Dialect) DialectState ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := mkImported
    addEntryFn    := fun s (leanName, d) =>
      assert! d.name ∉ s.loaded.dialects
      DialectState.addDialect! s d leanName (isExported := !leanName.isInternal)
    exportEntriesFn := exportEntries
  }

end StrataDDM
