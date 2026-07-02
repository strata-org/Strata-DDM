/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDDM.Render

namespace StrataDDM.Render.Tests

open StrataDDM

-- Default (mode = none) is the plain literal (the landed plain-decimal behavior).
#guard StrataRender.render none (Decimal.mk 6283185307179586 (-15)) = "6.283185307179586"
#guard StrataRender.render (some "noExponent") (Decimal.mk 271828 8) = "27182800000000.0"
-- Scientific mode selects the raw exponent form.
#guard StrataRender.render (some "scientific") (Decimal.mk 6283185307179586 (-15)) = "6283185307179586e-15"
-- Unknown mode falls back to the default rather than crashing.
#guard StrataRender.render (some "bogus") (Decimal.mk 15 (-1)) = "1.5"

end StrataDDM.Render.Tests
