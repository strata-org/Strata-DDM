/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Integration.Lean

public section

namespace StrataDDM.RenderContext.Tests

open StrataDDM

#dialect
dialect RC;
op decimal (v : Decimal) : Command => "decimal " v ";";
op str (v : Str) : Command => "str " v ";";
#end

def prog := #strata program RC; decimal 6283185307179586e-15; #end
def stringProg := #strata program RC; str "value"; #end

-- Default render context: the compact scientific form (exponent out of window).
#guard Program.toString prog = "program RC;\ndecimal 6283185307179586e-15;"

-- Forcing the `decimal` literal kind to `noExponent` yields the plain,
-- SMT-LIB-valid expansion from the same AST (the SMT-consumer use case).
#guard Program.toString prog { formatModes := Std.HashMap.ofList [("decimal", .noExponent)] }
        = "program RC;\ndecimal 6.283185307179586;"

-- Consumers can replace string-literal syntax without adding their policy to StrataDDM.
#guard Program.toString stringProg {
          customStringEscaper := some fun s => "[" ++ s ++ "]"
        } = "program RC;\nstr [value];"

/-! The parser-side callback is equally consumer-owned. This deliberately uses
syntax unrelated to SMT-LIB: the callback rewrites one wire spelling before the
generic DDM parser constructs the `Init.Str` argument. -/

private def advance (input : String) : Nat → String.Pos.Raw → String.Pos.Raw
  | 0, pos => pos
  | n + 1, pos => advance input n (pos.next input)

private def testStringDecoder : Parser.StringLiteralDecoder := fun input startPos =>
  let stopPos := advance input "\"wire\"".utf8ByteSize startPos
  if String.Pos.Raw.extract input startPos stopPos = "\"wire\"" then
    .ok ("decoded", stopPos)
  else
    .error "expected the test wire spelling"

/-- info: decoded -/
#guard_msgs in
#eval do
  let pctx : Parser.ParsingContext := {
    Elab.initParsers with stringLiteralDecoder := some testStringDecoder
  }
  let loaded := Elab.LoadedDialects.ofDialectsWith! pctx #[initDialect, RC]
  let input := Parser.stringInputContext "<decoder-test>" "str \"wire\";"
  let command ← Elab.parseCategoryFromDialect loaded q`Init.Command input
  match command with
  | { args := #[.strlit _ value], .. } => IO.println value
  | _ => throw (IO.userError "unexpected parsed program")

end StrataDDM.RenderContext.Tests
