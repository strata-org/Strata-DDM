/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
--Runtime dependendencies for Strata.Integration.Lean

public import StrataDDM.BuiltinDialects.Init --shake: keep
public import StrataDDM.SourcedProgram --shake: keep
public import StrataDDM.Integration.Lean.OfAstM --shake: keep
