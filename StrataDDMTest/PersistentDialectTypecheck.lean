/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean

/-! ## Regression: `PersistentDialect` round-trips the `typecheck` flag

`dialect_option typecheck off;` sets `Dialect.typecheck := false`. When a dialect
crosses a module boundary it is serialized through `PersistentDialect` (the
`dialectExt` env extension's export/import path). `PersistentDialect` previously
did not carry `typecheck`, so on import the reconstructed dialect reverted to the
`typecheck := true` default — silently re-enabling type inference for a dialect
whose author turned it off. This affected any dialect defined in one module and
used in another (e.g. a language dialect declared in its grammar module and used
by `#strata` programs elsewhere); the same-module `#dialect` path was unaffected
because it stores the full `Dialect` via the extension's `addEntryFn`.

These guards pin the flag surviving the `ofDialect ∘ dialect` round-trip. -/

open StrataDDM

-- `typecheck := false` survives the PersistentDialect round-trip.
#guard
  (PersistentDialect.ofDialect `TCOffProbe
      { name := "TCOffProbe", imports := #[], declarations := #[], typecheck := false }).dialect.typecheck
    == false

-- Positive control: the default `typecheck := true` is preserved as well.
#guard
  (PersistentDialect.ofDialect `TCOnProbe
      { name := "TCOnProbe", imports := #[], declarations := #[] }).dialect.typecheck
    == true
