/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
import StrataDDM.Format

open StrataDDM

#dialect
dialect TestPrec;

type bool;
type Box (a : Type);
fn trueExpr : bool => "t";
fn falseExpr : bool => "f";
fn and (a : bool, b : bool) : bool => @[prec(10), leftassoc] a " && " b;
fn or (a : bool, b : bool) : bool => @[prec(8), leftassoc] a " || " b;
fn imp (a : bool, b : bool) : bool => @[prec(7), rightassoc] a " => " b;
fn xor (a : bool, b : bool) : bool => @[prec(12)] a " ^^ " b;

op assert (b : bool) : Command => "assert " b ";\n";
op declType (t : Type) : Command => "val : " t ";\n";
#end

def ppParen (pgm : Program) :=
  IO.println <| toString <| pgm |>.format {alwaysParen := true }

/-- Pretty-print with the default formatter (parenthesize only where the
    grammar requires it). `alwaysParen` would parenthesize everything and so
    couldn't show whether the arrow itself is parenthesized when it needs to be. -/
def pp (pgm : Program) :=
  IO.println <| toString <| pgm |>.format {}

/--
info: program TestPrec;
assert ((t) && (t)) && (t);
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t && t && t;
#end

/--
info: program TestPrec;
assert (t) => ((t) => (t));
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t => t => t;
#end

/--
info: program TestPrec;
assert (f) ^^ (f);
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert f ^^ f;
#end

-- Check without associativity annotations, we get error.
/--
error: unexpected token '^^'; expected ';'
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert f ^^ f ^^ f;
#end

/--
info: program TestPrec;
assert ((t) && (t)) || (t);
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t && t || t;
#end

/--
info: program TestPrec;
assert (t) || ((t) && (t));
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t || t && t;
#end

/--
info: program TestPrec;
assert ((t) || (f)) => (t);
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t || f => t;
#end

-- Arrow types: `->` right-associates, so a right-nested arrow needs no parens,
-- but a left-nested arrow must be parenthesized or it reparses as right-nested.

/--
info: program TestPrec;
val : bool -> bool -> bool;
-/
#guard_msgs in
#eval pp #strata
program TestPrec;
val : bool -> bool -> bool;
#end

/--
info: program TestPrec;
val : (bool -> bool) -> bool;
-/
#guard_msgs in
#eval pp #strata
program TestPrec;
val : (bool -> bool) -> bool;
#end

-- An arrow as an argument to a type constructor must be parenthesized, or it
-- reparses as `(Box bool) -> bool` (type application binds tighter than `->`).

/--
info: program TestPrec;
val : Box (bool -> bool);
-/
#guard_msgs in
#eval pp #strata
program TestPrec;
val : Box (bool -> bool);
#end
