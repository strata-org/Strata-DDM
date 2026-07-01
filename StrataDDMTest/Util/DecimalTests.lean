/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDDM.Util.Decimal

namespace StrataDDM.Decimal.Tests

open StrataDDM

#guard s!"{Decimal.mk 0 0}" = "0.0"
#guard s!"{Decimal.mk 1 0}" = "1.0"
#guard s!"{Decimal.mk (-3) 0}" = "-3.0"
#guard s!"{Decimal.mk 4 2}" = "400.0"
#guard s!"{Decimal.mk (-4) 2}" = "-400.0"
#guard s!"{Decimal.mk (42) (-2)}" = "0.42"
#guard s!"{Decimal.mk (-42) (-2)}" = "-0.42"
#guard s!"{Decimal.mk (-134) (-2)}" = "-1.34"
-- Exponents outside the old pretty-print window must still expand to a plain
-- decimal literal (SMT-LIB has no scientific-notation literal).
#guard s!"{Decimal.mk (-142) 10}" = "-1420000000000.0"
#guard s!"{Decimal.mk 271828 8}" = "27182800000000.0"
#guard s!"{Decimal.mk 6283185307179586 (-15)}" = "6.283185307179586"
-- in-window control values are unchanged
#guard s!"{Decimal.mk 15 (-1)}" = "1.5"
-- leading zeros in fractional part
#guard s!"{Decimal.mk 2 (-2)}"  = "0.02"
#guard s!"{Decimal.mk 1 (-2)}"  = "0.01"
#guard s!"{Decimal.mk 5 (-3)}"  = "0.005"
#guard s!"{Decimal.mk 1 (-3)}"  = "0.001"
#guard s!"{Decimal.mk (-2) (-2)}" = "-0.02"

end StrataDDM.Decimal.Tests
