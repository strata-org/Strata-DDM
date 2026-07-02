/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Integration.Lean

public section

namespace StrataDDM.ArgFormatMode.Tests

open StrataDDM

#dialect
dialect AFM;
op plain (@[noExponent] d : Decimal) : Command => "plain " d ";";
op raw (d : Decimal) : Command => "raw " d ";";
#end

def progPlain := #strata program AFM; plain 6283185307179586e-15; #end
def progRaw   := #strata program AFM; raw 6283185307179586e-15; #end

-- The `@[noExponent]` argument annotation renders the plain, SMT-LIB-valid
-- literal with no render-context override set.
#guard Program.toString progPlain = "program AFM;\nplain 6.283185307179586;"

-- An unannotated argument uses the default rendering (compact scientific for an
-- out-of-window exponent) — the annotation is opt-in and backward-compatible.
#guard Program.toString progRaw = "program AFM;\nraw 6283185307179586e-15;"

-- A caller's explicit `formatModes` override wins over the arg annotation:
-- forcing `scientific` overrides the `@[noExponent]` on `plain`.
#guard Program.toString progPlain { formatModes := Std.HashMap.ofList [("decimal", "scientific")] }
        = "program AFM;\nplain 6283185307179586e-15;"

end StrataDDM.ArgFormatMode.Tests
