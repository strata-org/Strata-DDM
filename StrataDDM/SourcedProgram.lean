/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDDM.AST
public import StrataDDM.Format

namespace StrataDDM

/--
Bundle returned by the `#strata` term region. Carries:

- `program`: the parsed `Strata.Program` with **file-global** AST byte offsets,
  so Boole-style consumers (and any code that uses byte offsets in obligation
  labels or diagnostic ranges) keep their existing behavior.
- `source`: the raw snippet text between `#strata` and `#end`. Test helpers
  use this to build a snippet-local `FileMap`.
- `basePos`: byte offset in the Lean file where the snippet starts, so
  helpers can convert file-global pipeline diagnostics back to snippet-local
  positions when matching against inline annotations.
- `baseLine` / `fileName`: enough info for helpers to render
  `<lean_file>:<line>:<col>` in error messages so editors / quickfix lists
  can jump straight to the offending source.
-/
public structure SourcedProgram where
  program  : Program
  source   : String
  basePos  : Nat
  baseLine : Nat
  fileName : String
  deriving Inhabited

-- Forwarders so existing call sites can keep using `.commands`, `.dialect`,
-- etc. on the result of `#strata` as if it were a `Program`.
namespace SourcedProgram

public protected def toString (p : SourcedProgram) : String := toString p.program

/-- Forward `ToString` to the underlying `Program` so `#eval` printing keeps
    working at existing call sites. -/
public instance : ToString SourcedProgram where
  toString s := s.toString

/-- Allow `SourcedProgram` to be used wherever a `Program` is expected;
    the source/positions are dropped. -/
public instance : Coe SourcedProgram Program where
  coe s := s.program

public abbrev commands (s : SourcedProgram) : Array Operation :=
  s.program.commands
public abbrev dialect (s : SourcedProgram) : DialectName :=
  s.program.dialect
public abbrev dialects (s : SourcedProgram) : DialectMap :=
  s.program.dialects
public abbrev globalContext (s : SourcedProgram) : GlobalContext :=
  s.program.globalContext
public abbrev format (s : SourcedProgram) (opts : FormatOptions := {}) : Std.Format :=
  s.program.format opts

end SourcedProgram

end StrataDDM
