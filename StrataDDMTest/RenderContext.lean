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

-- Default render context: the compact scientific form (exponent out of window).
#guard Program.toString prog = "program RC;\ndecimal 6283185307179586e-15;"

-- Forcing the `decimal` literal kind to `noExponent` yields the plain,
-- SMT-LIB-valid expansion from the same AST (the SMT-consumer use case).
#guard Program.toString prog { formatModes := Std.HashMap.ofList [("decimal", "noExponent")] }
        = "program RC;\ndecimal 6.283185307179586;"

end StrataDDM.RenderContext.Tests
