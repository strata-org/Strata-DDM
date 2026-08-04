/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Integration.Lean

/-!
# `sourceLocEnd` skips trailing zero-width children (parser regression)

A trailing element with no concrete syntax parses to a *zero-width* node sitting
past the last real token (its preceding token consumes the trailing whitespace, so
the node lands beyond the real content, typically on the next line). Two shapes
produce this, both stamped with a zero-width `emptySourceInfo` range in the parser:
an **absent trailing optional** (`optionalFn`), and an **empty-template op** — one
with no concrete syntax, `op else0 () : Else => ;`, the `Core.else0`/`Dyn.no_else`/
`Core.nilInvariants` shape. `sourceLocEnd` skips such children when computing a
node's end, and `mkSourceRange?` — `⟨sourceLocPos, sourceLocEnd⟩` — inherits the skip.

These tests drive the real parser on the shapes that produce a trailing zero-width
node. The optional case is the analogue of Laurel `if c then new Left else new Right`,
where `new` ends in a trailing `Option NewTypeArgs`: `newExpr` (trailing `Option
Targs`) is nested as the last child of `outer`, so `outer`'s end descends through
`newExpr` into its absent optional — and must resolve to the end of `new Foo`, not the
later zero-width position. The empty-template case is the analogue of an else-less
`if`: `wrap`'s last child is a `Tail` whose absent alternative is the empty-template
`tailEmpty`, so `wrap`'s end must resolve to the end of `wrap foo`. Both stamp their
own zero-width range. The third case is a RANGELESS op that is a zero-width subtree
(`wrapOptOnly`): it carries no own range, so its emptiness is only visible by computing
its range — the `none`-branch skip in `lastSpanningEnd`.

Each case asserts the parsed range two ways: `markSpan` renders it *in the source
text* (`⟦…⟧` around the covered characters, or a caret `‸` for a zero-width point)
so the golden shows what the range covers at a glance, and `spanLen` gives a compact
numeric cross-check. A correct range's `⟧` sits at the end of the real content, never
overshooting onto the next line.
-/

public section

#dialect
dialect TrailingOpt;
category TExpr;
category Targs;
category Tail;
op targs (arg : Ident) : Targs => "<" arg ">";
// Trailing `Option`: with no `<arg>`, `ta` is an absent zero-width node and is
// the op's final syntactic element — exactly the `new`/`Option NewTypeArgs` shape.
op newExpr (name : Ident, ta : Option Targs) : TExpr => "new " name ta;
// `e` (the `newExpr`) is `outer`'s final syntactic element, so `outer`'s range
// descends into it — and thus into `newExpr`'s absent trailing optional.
op outer (e : TExpr) : TExpr => "outer " e;
// A second zero-width shape: an *empty-template* op (`=> ;`, no concrete syntax) —
// the `Core.else0`/`Dyn.no_else`/`Core.nilInvariants` shape. `mkNode` stamps such an
// op's node `SourceInfo.none`; the parser then restamps it with its own zero-width
// range (as it does an absent optional), so the end scan's own-range check can skip
// it. `tailEmpty` is the absent alternative of `Tail`.
op tailEmpty (         ) : Tail  => ;
op tailFull  (x : Ident) : Tail  => "tail " x;
// `t` (a `Tail`) is `wrap`'s final syntactic element, so `wrap`'s end comes from it:
// the end of `tail x` when present, and — skipping `tailEmpty`'s zero-width node — the
// end of the real content when the `Tail` is absent.
op wrap (a : Ident, t : Tail) : TExpr => "wrap " a t;
// A RANGELESS zero-width subtree: an op whose only surface element is an absent
// optional. Not an empty-template op (`.isLeading []`), so the parser does not restamp
// it — its node stays `SourceInfo.none` (rangeless) with a zero-width child. As a
// parent's last child it is reached through `lastSpanningEnd`'s `none` branch, whose
// computed-range zero-width check must skip it (the own-range check cannot: no own range).
category JOpt;
op optOnly (ta : Option Targs) : JOpt => ta;
op wrapOptOnly (a : Ident, j : JOpt) : TExpr => "wrapj " a j;
// A rangeless op with REAL content before its absent optional: computed end > start, so
// it must NOT be skipped. Guards the `none`-branch check against over-skipping.
op identThenOpt (x : Ident, ta : Option Targs) : JOpt => x ta;
op wrapIdentOpt (a : Ident, j : JOpt) : TExpr => "wrapk " a j;
// A LEADING absent optional: `ta` is the op's FIRST template element, before the real
// content. Its absent node sits at the next real token (the parser makes whitespace the
// preceding token's trailing trivia), so the op's START — `sourceLocPos`, which does NOT
// skip leading zero-width — is still correct. This pins the one-sidedness of the skip.
op optThenIdent (ta : Option Targs, name : Ident) : TExpr => ta "pre " name;
// `stmt` places a NEWLINE immediately after its expression `e`, with no separator
// token between them. So `e`'s last real token consumes that newline as trailing
// trivia, and the absent optional's zero-width node lands past the real content on
// the NEXT line — the position the end computation must skip. (A separator like
// `;` right after `e` leaves no whitespace to consume, keeping the optional on the
// same line.) A well-formed program has a following line per `stmt`.
op stmt (e : TExpr) : Command => "stmt " e "\n";
#end

open StrataDDM

/-- The first `stmt` command's sole argument op (an `outer` or `wrap`). -/
private def stmtArgOp (pgm : Program) : Option Operation :=
  match pgm.commands[0]? with
  | some stmt => match stmt.args[0]! with | ArgF.op o => some o | _ => none
  | _ => none

/-- Render `op`'s parsed range marked within `sp`'s snippet text, so the golden
shows exactly which characters it covers — a correct range brackets the op's real
text; a range that failed to skip a trailing zero-width child overshoots, its
closing marker landing past the content (typically the next line).

`#strata` returns a `SourcedProgram` carrying the raw snippet `source` and its
`basePos` (the snippet's byte offset in the Lean file); AST ranges are file-global,
so the range is sliced from `source` at `byteIdx - basePos`. A zero-width range
renders as a single caret `‸` (a located point), a nonempty one as `⟦…⟧`. -/
private def markSpan (sp : SourcedProgram) (op : Operation) : String :=
  let b := sp.source.toRawSubstring
  let lo := op.ann.start.byteIdx - sp.basePos
  let hi := op.ann.stop.byteIdx  - sp.basePos
  let before := (b.extract ⟨0⟩ ⟨lo⟩).toString
  let after  := (b.extract ⟨hi⟩ ⟨sp.source.utf8ByteSize⟩).toString
  if lo == hi then before ++ "‸" ++ after
  else before ++ "⟦" ++ (b.extract ⟨lo⟩ ⟨hi⟩).toString ++ "⟧" ++ after

/-- Byte-length of an op's range: `stop - start`. Offset-stable (unlike absolute
positions, which shift with surrounding text). Asserted alongside `markSpan` as a
compact numeric cross-check — it equals the op's source-text width when the range
is correct, and exceeds it if a trailing zero-width child was not skipped. -/
private def spanLen (op : Operation) : Nat := op.ann.stop.byteIdx - op.ann.start.byteIdx

/-- Render the first stmt-arg op's range marked in its source (empty if absent). -/
private def markFirst (sp : SourcedProgram) : String :=
  (stmtArgOp sp.program).map (markSpan sp) |>.getD "<no op>"

-- The programs below are MULTI-LINE on purpose: the trailing-optional op must end
-- a line (its last real token consumes the newline as trailing trivia) so the
-- absent optional lands past the real content on the NEXT line — the case the skip
-- handles. A following `stmt` line supplies that newline; a single-line input
-- leaves the optional on the same line and exercises nothing.
private def twoStmts : SourcedProgram :=
  #strata
  program TrailingOpt;
  stmt outer new Foo
  stmt outer new Bar
  #end

-- The first stmt's `outer` op ends at `Foo` on line 1, not at the absent optional's
-- zero-width node on line 2. The marked source shows the range covering exactly
-- `outer new Foo` (span 13); the `⟧` must not overshoot onto line 2.
/-- info: program TrailingOpt;
  stmt ⟦outer new Foo⟧
  stmt outer new Bar -/
#guard_msgs in
#eval IO.println (markFirst twoStmts)
/-- info: some 13 -/
#guard_msgs in
#eval (stmtArgOp twoStmts.program).map spanLen

-- With the type args PRESENT the range legitimately runs through `>`, confirming
-- the skip drops only ABSENT optionals, not present ones.
private def withTargs : SourcedProgram :=
  #strata
  program TrailingOpt;
  stmt outer new Foo<Bar>
  stmt outer new Bar
  #end
/-- info: program TrailingOpt;
  stmt ⟦outer new Foo<Bar>⟧
  stmt outer new Bar -/
#guard_msgs in
#eval IO.println (markFirst withTargs)
/-- info: some 18 -/
#guard_msgs in
#eval (stmtArgOp withTargs.program).map spanLen

-- Deeper nesting `outer outer new Foo`: the corrected end must propagate up
-- through every level — outer←outer←newExpr, each taking its last child's end,
-- with newExpr's skip of the absent optional.
private def deepNest : SourcedProgram :=
  #strata
  program TrailingOpt;
  stmt outer outer new Foo
  stmt outer new Bar
  #end
/-- info: program TrailingOpt;
  stmt ⟦outer outer new Foo⟧
  stmt outer new Bar -/
#guard_msgs in
#eval IO.println (markFirst deepNest)
/-- info: some 19 -/
#guard_msgs in
#eval (stmtArgOp deepNest.program).map spanLen

-- The boundary cases below reach `lastSpanningEnd` arms no dialect op can parse to (a
-- parseable op has at least one real token), so they build `Syntax` directly. Helpers:
-- The boundary cases below reach `lastSpanningEnd` arms no dialect op can parse to (a
-- parseable op has at least one real token), so they build `Syntax` directly. Node
-- builders (`sourceLocEnd` is `meta`, so the query stays inline in each `#eval`):
open Lean (Syntax SourceInfo) in
/-- A node with an own range `[a, b)`. -/
private def spanning (a b : Nat) : Syntax :=
  .node (SourceInfo.original "".toRawSubstring ⟨a⟩ "".toRawSubstring ⟨b⟩) `tok #[]
open Lean (Syntax) in
/-- A rangeless node (`SourceInfo.none`) with the given children. -/
private def rangeless (children : Array Syntax) : Syntax := .node .none `op children

-- `some r` branch, `i == 0` fallback: a lone child with an own (zero-width) range keeps
-- that child's end, so a wholly-empty node still yields a position.
/-- info: some 7 -/
#guard_msgs in
#eval (StrataDDM.sourceLocEnd (rangeless #[spanning 7 7])).map (·.byteIdx)

-- `none` branch, `sourceLocEnd`-is-`none` arms (a rangeless child with no spanning
-- descendant — an empty `rangeless #[]`):
-- (a) sole such child at `i == 0`: nothing to fall back to, so the node yields `none`.
/-- info: none -/
#guard_msgs in
#eval (StrataDDM.sourceLocEnd (rangeless #[rangeless #[]])).map (·.byteIdx)
-- (b) such a child after a spanning sibling: skip left to the sibling's end.
/-- info: some 5 -/
#guard_msgs in
#eval (StrataDDM.sourceLocEnd (rangeless #[spanning 0 5, rangeless #[]])).map (·.byteIdx)

-- Empty-template op (`tailEmpty`, the `else0`/`no_else`/`nilInvariants` shape) nested
-- as `wrap`'s last child, with the `Tail` alternative absent. The `tailEmpty` node sits
-- (zero-width) past the consumed newline on line 2; the end scan skips it via its
-- parser-stamped own zero-width range, so `wrap`'s range covers exactly `wrap foo`
-- (span 8), not the line-2 position.
private def wrapEmpty : SourcedProgram :=
  #strata
  program TrailingOpt;
  stmt wrap foo
  stmt outer new Bar
  #end
/-- info: program TrailingOpt;
  stmt ⟦wrap foo⟧
  stmt outer new Bar -/
#guard_msgs in
#eval IO.println (markFirst wrapEmpty)
/-- info: some 8 -/
#guard_msgs in
#eval (stmtArgOp wrapEmpty.program).map spanLen

-- The empty-template op's *own* range is a zero-width point, rendered as a caret
-- `‸`. Its position IS the "past the content, on the next line" spot (the caret
-- lands at the start of line 2, after `wrap foo`'s consumed newline) — exactly the
-- position `wrap`'s end scan must SKIP. Here we mark the point itself, showing where
-- it sits; the `wrap`-span test above shows the skip working.
/-- The `Tail` argument of a `wrap` op (its second argument). -/
private def wrapTail (op : Operation) : Option Operation :=
  match op.args[1]! with | ArgF.op o => some o | _ => none
/-- info: program TrailingOpt;
  stmt wrap foo
  ‸stmt outer new Bar -/
#guard_msgs in
#eval IO.println ((stmtArgOp wrapEmpty.program).bind wrapTail |>.map (markSpan wrapEmpty) |>.getD "<no op>")
-- The point is a real location, not `SourceRange.none` — so it can anchor the op's
-- own diagnostics. (`markSpan`'s caret cannot distinguish a point from "no range";
-- this pins the distinguishing property directly.)
/-- info: some (0, false) -/
#guard_msgs in
#eval (stmtArgOp wrapEmpty.program).bind wrapTail |>.map (fun t => (spanLen t, t.ann.isNone))

-- A rangeless op that is a zero-width subtree, as `wrapOptOnly`'s last child. Its end
-- is computed (no own range), so `lastSpanningEnd`'s `none` branch must recognize the
-- computed range as zero-width and skip it — `wrapOptOnly`'s range covers `wrapj foo`,
-- not the absent optional's position on the next line. (Skipping only stamped
-- zero-width children would miss this; the `none`-branch computed-range check is required.)
private def wrapRangeless : SourcedProgram :=
  #strata
  program TrailingOpt;
  stmt wrapj foo
  stmt outer new Bar
  #end
/-- info: program TrailingOpt;
  stmt ⟦wrapj foo⟧
  stmt outer new Bar -/
#guard_msgs in
#eval IO.println (markFirst wrapRangeless)
/-- info: some 9 -/
#guard_msgs in
#eval (stmtArgOp wrapRangeless.program).map spanLen

-- The over-skip guard: `identThenOpt x` (real content, then an absent optional) is
-- rangeless but NOT zero-width — computed end > start — so the `none`-branch check must
-- keep it. `wrapIdentOpt`'s range covers `wrapk foo x`, confirming the skip drops only
-- genuinely empty subtrees.
private def wrapIdentThenOpt : SourcedProgram :=
  #strata
  program TrailingOpt;
  stmt wrapk foo x
  stmt outer new Bar
  #end
/-- info: program TrailingOpt;
  stmt ⟦wrapk foo x⟧
  stmt outer new Bar -/
#guard_msgs in
#eval IO.println (markFirst wrapIdentThenOpt)
/-- info: some 11 -/
#guard_msgs in
#eval (stmtArgOp wrapIdentThenOpt.program).map spanLen

-- Leading-side one-sidedness: `optThenIdent` opens with an absent `ta`, nested under
-- `outer`. `outer`'s start descends to `optThenIdent`'s start, which must be `pre` (the
-- next real token) — `sourceLocPos` does NOT skip the leading absent optional, and must
-- not need to. The `⟦` marks the start; a wrong leading skip would misplace it.
private def leadingOpt : SourcedProgram :=
  #strata
  program TrailingOpt;
  stmt outer pre Foo
  stmt outer new Bar
  #end
/-- info: program TrailingOpt;
  stmt ⟦outer pre Foo⟧
  stmt outer new Bar -/
#guard_msgs in
#eval IO.println (markFirst leadingOpt)
/-- info: some 13 -/
#guard_msgs in
#eval (stmtArgOp leadingOpt.program).map spanLen
