# Handoff for Next Codex Session

## Context

This directory is the new standalone repository for **Algebraic Architecture Theory V2**.

It was split out from the older repository:

```text
Algebraic_Theory_of_Software_Architecture
```

The goal of V2 is to keep only the new research direction and Lean formalization:

> Design principles are operations that preserve or improve architecture invariants.  
> Architecture quality can be evaluated as a multi-axis risk signature of invariant violations.

## Current State

The repository is not initialized as a Git repository yet.

Important files:

- `Formal.lean`: Lean library root.
- `Formal/Arch/Core/Category.lean`: local minimal `SmallCategory`.
- `Formal/Arch/Core/Graph.lean`: `ArchGraph`, `Walk`, `Walk.length`.
- `Formal/Arch/Core/Reachability.lean`: `Reachable`, transitivity, walk-to-reachability.
- `Formal/Arch/Core/ThinCategory.lean`: `ComponentCategory`, thinness.
- `Formal/Arch/Core/Layering.lean`: `StrictLayered`, `Acyclic`, `WalkAcyclic`, `FinitePropagation`.
- `Formal/Arch/Core/Decomposable.lean`: initial definition `Decomposable G := StrictLayered G`, four-layer example.
- `Formal/Arch/Law/Projection.lean`: `InterfaceProjection`, `ProjectionSound`, `ProjectionComplete`, `ProjectionExact`, `RepresentativeStable`, `DIPCompatible`, `StrongDIPCompatible`.
- `Formal/Arch/Law/Observation.lean`: `Observation`, `ObservationallyEquivalent`, equivalence-style lemmas.
- `Formal/Arch/Law/LSP.lean`: `LSPCompatible`, `ObservationFactorsThrough`, and factorization-implies-LSP.
- `Formal/Arch/SolidCounterexample.lean`: cycle counterexamples, including `StrongAbstractCycleComponent`.
- `Formal/Arch/Signature/Signature.lean`: `ArchitectureSignature` and componentwise risk order.
- `docs/research_goal.md`: research goal and overview entry point.
- `docs/design_principle_classification.md`: design-principle classification.
- `docs/proof_obligations.md`: Lean proof obligations vs empirical hypotheses.
- `README.md`: standalone project README.
- `AGENTS.md`: repo-specific agent instructions.
- `.gitignore`: ignores `.lake/` and generated artifacts.

## Verification Already Run

From this directory:

```bash
lake build
lake exe aatv2
```

Both succeeded.

`lake exe aatv2` output:

```text
Algebraic Architecture Theory V2
```

Searches also confirmed:

- No references to `ArchTheory`.
- No references to the old repository name.
- No `sorry/admit/axiom/unsafe` in Lean source files.

The words `sorry`, `axiom`, etc. appear only in docs/AGENTS as policy text.

## Important Design Decisions

### Thin Category vs Walk Counting

`ComponentCategory` uses:

```lean
Reachable G : C -> C -> Prop
```

as Hom, so it intentionally forgets path counts, path lengths, and walk multiplicity.

Quantitative metrics should use:

- `Walk`
- future `Path`
- future adjacency matrices
- possibly future `FreeCategoryOfGraph`

### Edge Direction

Convention:

```text
edge c -> d means component c depends on component d.
```

Strict layering means:

```text
for every edge c -> d, layer d < layer c
```

### Decomposable

Initial definition:

```lean
def Decomposable G := StrictLayered G
```

Do not mix acyclicity, finite propagation, nilpotence, or spectral conditions into the definition. Grow those as theorems.

Already proved:

- `StrictLayered -> Acyclic`
- `StrictLayered -> FinitePropagation`
- `Acyclic <-> WalkAcyclic`
- four-layer example is `Decomposable`
- cycle examples are `¬ Decomposable`

### DIP

Current `DIPCompatible` is a strong operational formalization:

```lean
ProjectionSound G π GA ∧ RepresentativeStable G π
```

`QuotientWellDefined` is currently the same as `RepresentativeStable`, i.e. a strong representative-stability condition.

`StrongDIPCompatible` additionally requires exact projection:

```lean
ProjectionExact G π GA ∧ RepresentativeStable G π
```

### LSP

`ObservationFactorsThrough π O` was added:

```lean
∃ OAbs : Abs -> Obs, ∀ x, O.observe x = OAbs (π.expose x)
```

Already proved:

```lean
ObservationFactorsThrough π O -> LSPCompatible π O
```

### Counterexamples

`AbstractCycleComponent` is only a `DIP-direction-only counterexample`.

The stronger example is `StrongAbstractCycleComponent`, which proves:

- `ProjectionSound`
- `ProjectionComplete`
- `ProjectionExact`
- `RepresentativeStable`
- `DIPCompatible`
- `StrongDIPCompatible`
- `LSPCompatible`
- `¬ Decomposable`

This shows that even strong projection/LSP compatibility does not imply global decomposability when the abstract layer itself cycles.

## Likely Next Steps

1. Initialize Git:

```bash
git init
git add .
git commit -m "Initialize Algebraic Architecture Theory V2"
```

2. Create a public GitHub repository and push.

3. Ask ChatGPT/Chappy to review the PR or repository URL.

4. Next research/Lean task options:

- PR4: ArchitectureSignature v0 metric definitions.
- Add finite graph representation:
  - `[Fintype C]`
  - `[DecidableEq C]`
  - `DecidableRel G.edge`
  - or a dedicated `FiniteArchGraph`
- Prove `Acyclic + finite vertices -> StrictLayered`.
- Add `Path` distinct from `Walk`.
- Start adjacency matrix / nilpotence bridge.

## Caution

This directory has `.lake/` generated by `lake build`, but `.gitignore` excludes it.

Do not copy old `ArchTheory/Part1` through `Part7` into this repository unless explicitly requested. V2 is intended to be standalone and focused.
