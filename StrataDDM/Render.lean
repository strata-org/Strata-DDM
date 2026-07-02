/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Util.Decimal

public section
namespace StrataDDM

/-- A format "mode" is a name selecting one of a type's textual representations
    (e.g. `noExponent`, `scientific`). The empty string and `"default"` both
    denote the type's default representation. -/
abbrev FormatMode := String

/-- Types whose literal rendering can be selected by a named mode.
    `render "" x` (equivalently `render "default" x`) is the type's default. -/
class StrataRender (α : Type) where
  render : FormatMode → α → String

instance : StrataRender Decimal where
  render
    | "noExponent",  d => Decimal.toPlainString d
    | "scientific",  d => Decimal.toSciString d
    | _,             d => Decimal.toString d

end StrataDDM
