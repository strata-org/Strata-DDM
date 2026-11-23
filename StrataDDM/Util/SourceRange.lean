/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.Data.Position

public section
namespace StrataDDM

/--
Source location information in the DDM is defined
by a range of bytes in a UTF-8 string with the input
Line/column information can be constructed from a
`Lean.FileMap`

As an example, in the string `"123abc\ndef"`, the string
`"abc"` has the position `{start := 3, stop := 6 }` while
`"def"` has the position `{start := 7, stop := 10 }`.
-/
structure SourceRange where
  /-- The starting offset of the source range. -/
  start : String.Pos.Raw
  /-- One past the end of the range. -/
  stop : String.Pos.Raw
deriving DecidableEq, Inhabited, Repr, Hashable

namespace SourceRange

def none : SourceRange := { start := 0, stop := 0 }

def isNone (loc : SourceRange) : Bool := loc.start = 0 ∧ loc.stop = 0

instance : Std.ToFormat SourceRange where
 format fr := f!"{fr.start}-{fr.stop}"

/-- Format a SourceRange as a string using a FileMap for line:column conversion.
    Renders location information in a format VSCode understands.
    Returns "path:line:col-col" if on same line, otherwise "path:line:col". -/
def format (loc : SourceRange) (path : System.FilePath) (fm : Lean.FileMap) : String :=
  if loc.isNone then
    s!"{path}:unknown"
  else
    let spos := fm.toPosition loc.start
    let epos := fm.toPosition loc.stop
    if spos.line == epos.line then
      s!"{path}:{spos.line}:{spos.column+1}-{epos.column+1}"
    else
      s!"{path}:{spos.line}:{spos.column+1}"

end SourceRange

open Lean (Syntax)

def infoSourceRange (info : Lean.SourceInfo) : Option SourceRange :=
  match info with
  | .original (pos := pos) (endPos := endPos) ..
  | .synthetic (pos := pos) (endPos := endPos) .. =>
    some { start := pos, stop := endPos }
  | .none  => none

/-- A node's *own* source range (from its head info), without descending into
children. `none` for a `.node` that carries no range of its own. -/
private def ownRange (stx : Syntax) : Option SourceRange :=
  match stx with
  | .atom info .. | .ident info .. | .node info .. => infoSourceRange info
  | .missing => none

def sourceLocPos (stx:Syntax) : Option String.Pos.Raw :=
  match stx with
  | .atom info .. | .ident info .. =>
    infoSourceRange info |>.map (·.start)
  | .node info _kind args  =>
    match infoSourceRange info with
    | some loc =>
      some loc.start
    | .none  =>
      -- First child's start, with no leading zero-width skip (unlike `sourceLocEnd`).
      -- The parser makes whitespace the *preceding* token's trailing trivia, so a
      -- leading absent optional sits at the next real token — a correct start. Only
      -- a trailing absent optional lands past consumed whitespace (`sourceLocEnd`
      -- skips those).
      if h : args.size > 0 then
        sourceLocPos args[0]
      else
        none
  | .missing => none

/-- End position of a syntax tree, skipping trailing zero-width children.

For a node with no range of its own, the end is that of its last child that covers
source text, found by scanning right-to-left and skipping zero-width children. A
trailing element with no concrete syntax — an absent trailing optional, or an
empty-template op (`op else0 () => ;`) — parses to a zero-width node past the real
content (on the preceding token's consumed trailing whitespace), so it must be
skipped, not taken as the end. The common case is an O(1) own-info check: these nodes
carry their own zero-width range (stamped by the parser). A rangeless nested node (a
non-empty list, a present optional, a literal, a `choice`, or an op without a stamp: one
whose template is only whitespace, or one in a tree that the parser did not build) is the
exception — it needs a descent to tell whether its subtree is zero-width (see
`lastSpanningEnd`'s `none` case).

The skip lives here, in the descending function, so a parent reaching a nested
child's end gets the corrected position at every level, e.g. `if … else new C` →
`else` → `new` → its absent trailing type-args. `mkSourceRange?` is then just
`⟨sourceLocPos, sourceLocEnd⟩`. The `i == 0` case keeps the first child's end even
if empty, so a wholly-empty node still yields a position. The skip is one-sided —
`sourceLocPos` needs no *leading* skip (see its comment). -/
def sourceLocEnd (stx:Syntax) : Option String.Pos.Raw :=
  match stx with
  | .atom info ..  | .ident info .. =>
    infoSourceRange info |>.map (·.stop)
  | .node info _kind args  =>
    match infoSourceRange info with
    | some loc =>
      some loc.stop
    | .none  =>
      if h : 0 < args.size then lastSpanningEnd args ⟨args.size - 1, by omega⟩ else none
  | .missing => none
where
  /-- `stop` of the rightmost child in `args[0…i]` that covers source text, skipping
  trailing zero-width children (classified below). Falls back to `args[0]`'s end, so a
  node all of whose children are zero-width still yields a position. -/
  lastSpanningEnd (args : Array Syntax) (i : Fin args.size) : Option String.Pos.Raw :=
    -- Classify the child from its *own* info first (O(1), no descent):
    --   spanning own range   → its end is `r.stop`; keep it (no `sourceLocEnd` walk).
    --   zero-width own range → no concrete syntax: an absent optional or an empty list
    --                          (`emptySourceInfo`), or an op whose children are all
    --                          zero-width, such as an empty-template op over its empty
    --                          atom (stamped by `stampFn`); skip it, scanning left.
    --   no own range         → a non-empty list, a present optional, a literal, a
    --                          `choice`, or an op without a stamp (one whose template is
    --                          only whitespace, which has no children, or one in a tree
    --                          that the parser did not build); recurse for its end, and
    --                          skip it too if that subtree is zero-width (see below).
    -- Only the no-own-range case descends (plus a conditional start probe; see below).
    match ownRange args[i] with
    | some r =>
      if r.start != r.stop then some r.stop
      else if h : 0 < i.val then lastSpanningEnd args ⟨i.val - 1, by omega⟩
      else some r.stop      -- all children zero-width: fall back to the first
    | none =>
      -- A child without a range of its own can itself be a zero-width subtree: a present
      -- optional around a zero-width op, say, or, in a tree that the parser did not
      -- build, an op without a stamp whose descendants are all absent. Its computed end
      -- then equals its start. The `some r` branch skips a zero-width range that the
      -- child carries; this one has none, so detect it by comparing
      -- `sourceLocEnd args[i]` with `sourceLocPos args[i]`. The `sourceLocPos` probe
      -- fires only for a spanning child with a skip still possible (`i > 0`), so a real
      -- last child pays nothing; cost is linear in spine depth.
      match sourceLocEnd args[i], h : i.val with
      | none,   0     => none
      | none,   _ + 1 => lastSpanningEnd args ⟨i.val - 1, by omega⟩
      | some e, 0     => some e
      | some e, _ + 1 => if sourceLocPos args[i] == some e     -- zero-width subtree: skip
                         then lastSpanningEnd args ⟨i.val - 1, by omega⟩
                         else some e

/-- Source range of a syntax tree: its start position paired with its end.

Both bounds come from `sourceLocPos` / `sourceLocEnd`, so the trailing
zero-width skip that `sourceLocEnd` performs is honored here for free — this is
just the two positional queries combined. -/
def mkSourceRange? (stx:Syntax) : Option SourceRange :=
  match sourceLocPos stx, sourceLocEnd stx with
  | some start, some stop => some { start, stop }
  | _, _ => none

/-- The info for a node `n` that has none, once `n`'s children have theirs: the range that
`mkSourceRange?` finds for `n`, with the leading whitespace of `n`'s first token and the
trailing whitespace of its last (`getHeadInfo`, `getTailInfo`). `none` if there is no
range, or if either token's info is not `.original`; the node then keeps no info, and its
range is found by walking down it, as without a stamp. So do the nodes above it whose first
or last token is that token, since `getHeadInfo` and `getTailInfo` descend through it: on
a spine, one such token brings back the walk down the whole spine.

With the children stamped, `mkSourceRange? n` reads their own info, so this is constant
work per node, except that a child with no info of its own (a non-empty list, say) is read
through its first and last children, and that `sourceLocEnd` skips zero-width children at
the end of `n` (at most as many as `n`'s template has arguments, or one after a list's
last separator).

The stamp's trailing whitespace need not start at its end: when `n` ends with zero-width
children (an absent optional, say), the range stops at the last child that spans text,
while the trailing whitespace is that of the zero-width child, empty and after the
whitespace that follows the range.

**The ranges do not change.** Write `pos`, `end` for `sourceLocPos`, `sourceLocEnd`, and
let `n'` be `n` with this info. If `pos` and `end` agree on each child stamped and
unstamped, they agree on `n'` and `n`: `n'` reads its own info, which is
`⟨pos n, end n⟩`. They also agree on the parent, whose `end` walks its children right to
left and skips a zero-width child unless it is the first: on `n` it takes `end n` and
skips `n` when `pos n = end n`; on `n'` it takes the stop of `n'`'s range and skips `n'`
when that range is empty. These are the same test.

**The whitespace does not change.** `getHeadInfo` and `getTailInfo` return a node's own
info when it has one, so on `n'` and on every node above it they read this info instead of
descending to `n`'s first and last tokens; it holds those tokens' leading and trailing
whitespace. -/
def rangeInfo? (n : Syntax) : Option Lean.SourceInfo :=
  match mkSourceRange? n, n.getHeadInfo, n.getTailInfo with
  | some r, .original leading .., .original _ _ trailing _ =>
    some (.original leading r.start trailing r.stop)
  | _, _, _ => none

end StrataDDM
end
