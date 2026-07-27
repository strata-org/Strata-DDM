/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Util.Ion.AST
meta import Lean.Elab.Command -- shake: keep
meta import StrataDDM.Util.Ion.SymbolTable --shake: keep

-- Use metaprogramming to declare `{sym}SymbolId : SymbolId` for each system symbol.
open Lean.Elab.Command (elabCommand)

-- Declare all system symbol ids as constants
run_cmd do
  for sym in Ion.SymbolTable.ionSharedSymbolTableEntries do
    -- To simplify name, strip out non-alphanumeric characters.
    let simplifiedName : String := .ofList <| sym.toList.filter (·.isAlphanum)
    let leanName := Lean.mkIdentFrom (canonical := true) default <| ``Ion.SymbolId |>.str simplifiedName
    let idx := Ion.SymbolTable.system.symbolId sym
    if idx = .zero then
      throwError s!"Unbound symbol {sym}"
    elabCommand $ ← `(command|
      public def $(leanName) : Ion.SymbolId := ⟨$(Lean.Syntax.mkNatLit idx.value)⟩
    )
