/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDDM.Render

namespace StrataDDM.Render.Tests

open StrataDDM

-- Default mode (empty string or "default") is `Decimal.toString`: compact
-- scientific for out-of-window exponents, plain otherwise.
#guard StrataRender.render "" (Decimal.mk 6283185307179586 (-15)) = "6283185307179586e-15"
#guard StrataRender.render "default" (Decimal.mk 6283185307179586 (-15)) = "6283185307179586e-15"
#guard StrataRender.render "" (Decimal.mk 15 (-1)) = "1.5"
-- `noExponent` always expands in full (the SMT-LIB-safe form).
#guard StrataRender.render "noExponent" (Decimal.mk 271828 8) = "27182800000000.0"
#guard StrataRender.render "noExponent" (Decimal.mk 6283185307179586 (-15)) = "6.283185307179586"
-- `scientific` always renders the raw exponent form.
#guard StrataRender.render "scientific" (Decimal.mk 271828 8) = "271828e8"
-- Unknown mode falls back to the default rather than crashing.
#guard StrataRender.render "bogus" (Decimal.mk 15 (-1)) = "1.5"

end StrataDDM.Render.Tests
