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
-- Default: exponents outside the pretty-print window `[-5, 5]` render compact
-- scientific.
#guard s!"{Decimal.mk (-142) 10}" = "-142e10"
#guard s!"{Decimal.mk 271828 8}" = "271828e8"
#guard s!"{Decimal.mk 6283185307179586 (-15)}" = "6283185307179586e-15"
-- in-window control values are unchanged
#guard s!"{Decimal.mk 15 (-1)}" = "1.5"
-- leading zeros in fractional part
#guard s!"{Decimal.mk 2 (-2)}"  = "0.02"
#guard s!"{Decimal.mk 1 (-2)}"  = "0.01"
#guard s!"{Decimal.mk 5 (-3)}"  = "0.005"
#guard s!"{Decimal.mk 1 (-3)}"  = "0.001"
#guard s!"{Decimal.mk (-2) (-2)}" = "-0.02"

-- `toPlainString` always expands in full (no scientific notation) — the
-- representation the `noExponent` format mode selects for SMT-LIB.
-- Boundary cases for the `m = 0` and `e == 0` branches.
#guard StrataDDM.Decimal.toPlainString (Decimal.mk 0 0) = "0.0"
#guard StrataDDM.Decimal.toPlainString (Decimal.mk 0 (-3)) = "0.0"
#guard StrataDDM.Decimal.toPlainString (Decimal.mk 7 0) = "7.0"
#guard StrataDDM.Decimal.toPlainString (Decimal.mk (-7) 0) = "-7.0"
#guard StrataDDM.Decimal.toPlainString (Decimal.mk (-142) 10) = "-1420000000000.0"
#guard StrataDDM.Decimal.toPlainString (Decimal.mk 271828 8) = "27182800000000.0"
#guard StrataDDM.Decimal.toPlainString (Decimal.mk 6283185307179586 (-15)) = "6.283185307179586"
#guard StrataDDM.Decimal.toPlainString (Decimal.mk 15 (-1)) = "1.5"
-- Fewer mantissa digits than `|e|`: the fractional part is left-padded with
-- zeros. And a negative mantissa in the `e < 0` arm carries its sign through.
#guard StrataDDM.Decimal.toPlainString (Decimal.mk 5 (-3)) = "0.005"
#guard StrataDDM.Decimal.toPlainString (Decimal.mk (-42) (-2)) = "-0.42"

-- The invariant the function exists to guarantee: no `e` in the output, so the
-- literal is never lexed as scientific notation (a free symbol) by SMT-LIB.
#guard !(StrataDDM.Decimal.toPlainString (Decimal.mk 6283185307179586 (-15))).any (· == 'e')
#guard !(StrataDDM.Decimal.toPlainString (Decimal.mk (-142) 10)).any (· == 'e')

-- `toSciString` always renders raw scientific form.
#guard StrataDDM.Decimal.toSciString (Decimal.mk 6283185307179586 (-15)) = "6283185307179586e-15"
#guard StrataDDM.Decimal.toSciString (Decimal.mk 271828 8) = "271828e8"
#guard StrataDDM.Decimal.toSciString (Decimal.mk 0 0) = "0e0"
-- A negative mantissa carries its sign into the scientific form too.
#guard StrataDDM.Decimal.toSciString (Decimal.mk (-142) 10) = "-142e10"

end StrataDDM.Decimal.Tests
