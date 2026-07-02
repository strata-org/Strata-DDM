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
#end

def prog := #strata program RC; decimal 6283185307179586e-15; #end

-- Default render context: the plain literal.
#guard Program.toString prog = "program RC;\ndecimal 6.283185307179586;"

-- Forcing the `decimal` literal kind to `scientific` yields a different string
-- from the same AST.
#guard Program.toString prog { formatModes := Std.HashMap.ofList [("decimal", "scientific")] }
        = "program RC;\ndecimal 6283185307179586e-15;"

end StrataDDM.RenderContext.Tests
