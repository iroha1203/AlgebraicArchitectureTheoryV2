# Algebraic Architecture Theory V2

This repository contains the V2 formalization of Algebraic Architecture Theory.

The goal is to classify software design principles by the architecture
invariants they preserve or improve, and to evaluate architecture quality as a
multi-axis risk signature of invariant violations.

## Structure

- `Formal.lean`: root Lean module.
- `Formal/Arch`: Lean definitions and theorems for graphs, reachability,
  layering, projection, observation, LSP, counterexamples, and signatures.
- `docs`: research overview, design-principle classification, and proof
  obligations.
- `Main.lean`: minimal executable entry point.

## Build

```bash
lake build
lake build Formal
lake exe aatv2
```

## Current Scope

The initial formalization includes:

- dependency graphs and walks;
- reachability and the thin component category;
- strict layering, decomposability, acyclicity, and finite propagation;
- projection soundness/completeness/exactness and strong operational DIP;
- observation, observation factorization, and LSP compatibility;
- local-contract and abstract-layer-cycle counterexamples;
- architecture signatures with componentwise risk order and executable v0
  finite-list metrics.
