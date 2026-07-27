/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDDM.Integration.Lean

open StrataDDM

/-!
# Deep left-nested parse regression

A deeply left-nested parenthesized operand chain made the dynamic
(Pratt / longest-match) category parser re-parse each inner subexpression once
per competing longest-match alternative per nesting level, so parse time grew
exponentially in nesting depth (empirically ~3.7x per two levels). Past a
moderate depth the parser did not terminate within any practical bound; with
position-keyed category memoization it parses in well under a second.

The signal is termination-with-correct-structure: a left-associative operator
means the fully-parenthesized input below round-trips to the flat form, so the
`#guard_msgs` assertion checks both that parsing completes AND that it nests
left. Before the memoization change this evaluation would not terminate.
-/

meta section

#dialect
dialect DeepNest;

type bool;
fn t : bool => "t";
fn and (a : bool, b : bool) : bool => @[prec(10), leftassoc] a " && " b;

op assert (b : bool) : Command => "assert " b ";\n";
#end

/- A left-associative `&&` re-associates the explicitly-parenthesized,
left-nested input back to the flat surface form on print. Reaching this output
at all is the regression signal (pre-fix: non-terminating parse at this depth). -/
/--
info: program DeepNest;
assert t && t && t && t && t && t && t && t && t && t && t && t && t && t && t && t && t && t && t && t;
-/
#guard_msgs in
#eval IO.println #strata
program DeepNest;
assert (((((((((((((((((((t && t) && t) && t) && t) && t) && t) && t) && t) && t) && t) && t) && t) && t) && t) && t) && t) && t) && t) && t);
#end
