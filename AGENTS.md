# AGENTS.md - StrataDDM

Guide for AI agents working with the StrataDDM package.

For purpose, file structure, and build/test commands, see
[`README.md`](./README.md). The notes below cover only the conventions and
workflows that aren't obvious from reading the code.

## What the DDM produces

A *dialect definition* (written in the DDM's own surface syntax) is the input;
from it the DDM derives an AST type, a parser, a pretty printer, and a
preliminary type checker. The first result of parsing dialect text is always
the **generic** AST in `StrataDDM/AST.lean` (`Operation`, `Expr`, `Arg`,
`TypeExpr`, `Program`, ... — all `*F` functors specialized at `SourceRange`).
This representation is flexible but awkward to traverse, so a dialect may also
have a generated or hand-written specialized Lean AST plus a transform from the
generic form. When adding constructs, decide first whether you are touching the
generic AST (affects every dialect) or a per-dialect specialization.

## The two integration paths

`StrataDDM/Integration/` is where a dialect crosses from generic AST into
something usable:

1. **Lean** (`Integration/Lean/`) — the `#strata_gen <Dialect>` command
   (`Gen.lean`) generates a specialized Lean AST for a loaded dialect, *plus*
   `ofAst`/`toAst` conversions to and from the generic AST (`OfAstM.lean`).
   `#load_dialect "<path>"` loads a dialect from a `.dialect.st` file at compile
   time. These are the macros test files and downstream packages use.
2. **Java** (`Integration/Java/`) — `generateDialect d package` returns
   `GeneratedFiles`; `writeJavaFiles baseDir package files` writes them. Output
   is assembled from the hand-maintained templates in
   `Integration/Java/templates/` (`Node.java`, `IonSerializer.java`,
   `SourceRange.java`) — edit those templates for cross-cutting Java changes,
   not the generated strings.

## Embedding dialect text in Lean

Hash commands (defined in `Integration/Lean/`): `#dialect ... #end` defines a
dialect inline, and `#strata <Dialect>; ... #end` parses a program in that
dialect. Most tests combine these with `#guard_msgs` to pin the pretty-printed
or elaborated output — see `StrataDDMTest/Bool.lean` for the canonical shape.

## Ion serialization

`StrataDDM/Ion.lean` + `Util/Ion/` implement (de)serialization to
[Ion](https://amazon-ion.github.io/ion-docs/) binary. Dialects are exchanged
with other tools (including the generated Java library) in this format, so any
change to the generic AST or a dialect's wire shape must keep the Ion
serializer, the Ion deserializer, and the Java `IonSerializer.java` template in
agreement. Roundtrip tests live in `StrataDDMTest/Util/Ion/`.

## Lean module-system conventions

This package uses Lean 4's module system. Every file starts with the
SPDX-licensed copyright block, then `module`, then imports. Use `public import`
for a dependency whose names appear in this file's public signatures and plain
`import` otherwise; mark exported declarations with `public` / `public section`.
Match the surrounding file — `Util/Ion/Serialize.lean` is a representative
example. New `.lean` files must carry the standard header:

```lean
/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
```

## Namespaces

Library code lives under the `StrataDDM` namespace (the package was renamed from
`Strata.*` to `StrataDDM.*`; do not reintroduce `Strata.*` namespaces here).
Note that `Util/Ion/` declarations sit in a top-level `Ion` namespace, not
`StrataDDM.Ion`.

## Testing

`lake test` builds the `StrataDDMTest` library; the tests are `#eval` /
`#guard_msgs` checks that run during elaboration, so a clean build of that
library *is* a passing test run. Add new tests as files under `StrataDDMTest/`
(the lakefile globs `StrataDDMTest.+`, so no manifest edit is needed). Example
dialects used by tests live in `StrataDDMTest/dialects/`.
