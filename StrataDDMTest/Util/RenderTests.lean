/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDDM.Render

namespace StrataDDM.Render.Tests

open StrataDDM

-- `.default` mode is `Decimal.toString`: compact scientific for out-of-window
-- exponents, plain otherwise.
#guard StrataRender.render .default (Decimal.mk 6283185307179586 (-15)) = "6283185307179586e-15"
#guard StrataRender.render .default (Decimal.mk 15 (-1)) = "1.5"
-- `.noExponent` always expands in full (the SMT-LIB-safe form).
#guard StrataRender.render .noExponent (Decimal.mk 271828 8) = "27182800000000.0"
#guard StrataRender.render .noExponent (Decimal.mk 6283185307179586 (-15)) = "6.283185307179586"
-- `.scientific` always renders the raw exponent form.
#guard StrataRender.render .scientific (Decimal.mk 271828 8) = "271828e8"

-- `FormatMode.ofString` parses declared marker names. The empty string and
-- "default" both denote the default; an unrecognized name is a hard error
-- rather than a silent fallback, so a typo in a dialect marker fails loudly.
#guard match FormatMode.ofString "" with | .ok .default => true | _ => false
#guard match FormatMode.ofString "default" with | .ok .default => true | _ => false
#guard match FormatMode.ofString "noExponent" with | .ok .noExponent => true | _ => false
#guard match FormatMode.ofString "scientific" with | .ok .scientific => true | _ => false
#guard match FormatMode.ofString "bogus" with
       | .error e => e = "unknown format mode 'bogus'"
       | .ok _ => false

end StrataDDM.Render.Tests
