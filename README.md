# StrataDDM

StrataDDM is a standalone Lean 4 package implementing the **Dialect Definition Mechanism (DDM)** for [Strata](https://github.com/strata-org/Strata).

## Overview

The DDM is an embedded DSL within Lean for defining the syntax and typing rules of a *dialect*. From a single dialect definition it produces:

- an AST type,
- a parser (for both snippets embedded in Lean source and text read from external files),
- a pretty printer, and
- a preliminary type checker.

The immediate result of processing text written in a dialect is a generic, flexible AST that captures all constructs expressible in Strata. Dialects can import one another, reusing the syntactic categories of imported dialects.

The DDM also supports serialization to and from the [Ion](https://amazon-ion.github.io/ion-docs/) binary format, and can generate a corresponding Java AST library directly from a dialect definition, making it convenient for any dialect that needs to be exchanged with other programs.

## Package Structure

```
StrataDDM/
├── lakefile.toml         # Lake build config
├── lean-toolchain        # Lean version selection
├── StrataDDM.lean        # Root module — file I/O and public API
├── StrataDDM/
│   ├── AST/              # Generic Strata AST
│   ├── Parser.lean       # Pratt parser
│   ├── Elab/             # Elaboration / dialect loading
│   ├── Format.lean       # Pretty printing
│   ├── BuiltinDialects/  # init, header, StrataDDL
│   ├── Integration/      # Lean and Java code generation
│   ├── Ion.lean          # Ion (de)serialization
│   └── Util/             # Supporting utilities (Ion, Graph, ...)
├── StrataDDMTest.lean    # Test root module
└── StrataDDMTest/        # Tests and example dialects
```

## Building

From the `StrataDDM/` directory:

```bash
lake build
```

To run the tests (the test library uses `#eval` and `#guard_msgs` checks):

```bash
lake test
```

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
