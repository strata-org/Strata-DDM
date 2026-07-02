/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Util.Decimal

public section
namespace StrataDDM

/-- A format "mode" is a name selecting one of a type's textual representations
    (e.g. `noExponent`, `scientific`). `none` means the type's default. -/
abbrev FormatMode := String

/-- Types whose literal rendering can be selected by a named mode.
    `render none x` is the type's default representation. -/
class StrataRender (α : Type) where
  render : Option FormatMode → α → String

instance : StrataRender Decimal where
  render
    | none,               d => Decimal.toString d
    | some "scientific",  d => Decimal.toSciString d
    | some "noExponent",  d => Decimal.toString d
    | some _,             d => Decimal.toString d

end StrataDDM
