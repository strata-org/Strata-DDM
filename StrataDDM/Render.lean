/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Util.Decimal

public section
namespace StrataDDM

/-- A format mode selects one of a type's textual representations. `default` is
    the type's default representation; the others name alternatives (e.g. a
    decimal's plain or scientific form). Parsed from a declared marker name by
    `FormatMode.ofString`. -/
inductive FormatMode where
  | default
  | noExponent
  | scientific
deriving DecidableEq, Repr, Inhabited

namespace FormatMode

/-- Parse a declared mode name. The empty string and `"default"` both denote the
    default representation; an unrecognized name is an error rather than a silent
    fallback, so a typo in a dialect's `@[<mode>]` marker fails loudly. -/
def ofString : String → Except String FormatMode
  | "" | "default" => .ok .default
  | "noExponent"   => .ok .noExponent
  | "scientific"   => .ok .scientific
  | s              => .error s!"unknown format mode '{s}'"

end FormatMode

/-- Types whose literal rendering can be selected by a `FormatMode`.
    `render .default x` is the type's default representation. -/
class StrataRender (α : Type) where
  render : FormatMode → α → String

instance : StrataRender Decimal where
  render
    | .noExponent, d => Decimal.toPlainString d
    | .scientific, d => Decimal.toSciString d
    | .default,    d => Decimal.toString d

end StrataDDM
