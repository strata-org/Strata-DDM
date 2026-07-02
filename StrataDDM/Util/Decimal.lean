/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.ToExpr

import all StrataDDM.Util.Lean
import all StrataDDM.Util.String

public section
namespace StrataDDM

structure Decimal where
  mantissa : Int
  exponent : Int
deriving DecidableEq, Inhabited, Repr

namespace Decimal

def zero : Decimal := { mantissa := 0, exponent := 0 }

protected def ofInt (x : Int) : Decimal := { mantissa := x, exponent := 0 }

private opaque maxPrettyExponent : Int := 5

private opaque minPrettyExponent : Int := -5

/-- Always expand to a plain decimal literal, with no scientific notation.
    SMT-LIB has no scientific-notation numeric literal (a form like `142e10`
    parses as the free symbol `e10` applied to a number), so consumers that
    emit SMT select this via the `noExponent` format mode. -/
def toPlainString (d : Decimal) : String :=
  let m := d.mantissa
  let e := d.exponent
  if m = 0 then
    s!"0.0"
  else if e == 0 then
    s!"{m}.0"
  else if e > 0 then
    -- Positive exponent: append `e` trailing zeros and a `.0` fractional part.
    s!"{m}{String.replicate e.natAbs '0'}.0"
  else
    -- Negative exponent: shift the decimal point left by `|e|` digits,
    -- padding with leading zeros in the fractional part as needed.
    let ms := if m < 0 then "-" else ""
    let ma := m.natAbs
    let width := (-e).natAbs
    let ne := 10^width
    let md := ma % ne
    let fracStr := s!"{md}"
    let padded := String.replicate (width - fracStr.length) '0' ++ fracStr
    s!"{ms}{ma / ne}.{padded}"

/-- The default rendering: a plain literal within the pretty-print exponent
    window `[-5, 5]`, and compact scientific notation outside it. -/
def toString (d : Decimal) : String :=
  let m := d.mantissa
  let e := d.exponent
  if m = 0 then
    s!"0.0"
  else if e == 0 then
    s!"{m}.0"
  else if e > 0 ∧ e ≤ maxPrettyExponent then
    s!"{m}{String.replicate e.natAbs '0'}.0"
  else if e < 0 ∧ e ≥ minPrettyExponent then
    let ms := if m < 0 then "-" else ""
    let ma := m.natAbs
    let width := (-e).natAbs
    let ne := 10^width
    let md := ma % ne
    let fracStr := s!"{md}"
    let padded := String.replicate (width - fracStr.length) '0' ++ fracStr
    s!"{ms}{ma / ne}.{padded}"
  else
    s!"{m}e{e}"

/-- Always render in scientific form: raw `mantissa`e`exponent`. -/
def toSciString (d : Decimal) : String := s!"{d.mantissa}e{d.exponent}"

instance : ToString Decimal where
  toString := private Decimal.toString

section

open _root_.Lean

instance : ToExpr Decimal where
  toTypeExpr := mkConst ``Decimal
  toExpr d :=
    mkApp2 (mkConst ``Decimal.mk) (toExpr d.mantissa) (toExpr d.exponent)

private instance : Quote Decimal where
  quote d := Syntax.mkCApp ``Decimal.mk #[quote d.mantissa, quote d.exponent]

end

end Decimal

end StrataDDM
