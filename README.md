# Algebraic Architecture Theory & Software Field Theory

[日本語版はこちら](README.jp.md)

This repository brings together the mathematical theory, Lean 4 formalization,
tooling, and publications for **Algebraic Architecture Theory (AAT)** and
**Software Field Theory (SFT)**.

Software architecture is not only a static shape; it changes continuously through
implementation, review, CI, operations, and AI-assisted development. This project
treats software semantics as a geometric space: **AAT** constructs that geometry
from architectural facts and laws, **SFT** models software evolution as dynamics
within it, and the **tooling** connects the theory to real codebases.

For the overarching vision, see [Overall Research Goal](docs/research_goal.md) (Japanese).

## Why AAT?

Buildings have both architectural design and structural engineering — loads,
stresses, and safety factors are calculated mathematically. Software
architecture, by contrast, has rich design principles (MVC, Clean Architecture,
DDD, design patterns) that help humans read code, while the **structural
calculation of meaning** — checking whether local changes actually hold together
as a whole — was carried in people's heads during code review. As AI agents
generate code far faster than humans can review, human comprehension alone can
no longer carry that load.

Existing approaches leave a gap. Unit tests and CI verify local slices, yet
systems still fail globally where parts overlap — through implicit interface
assumptions, shared state, or unintended ripple effects. Traditional formal
methods verify a separate specification written before implementation, making it
costly to keep the model aligned with evolving code. Meanwhile, AI agents read
large codebases from scratch every session without a shared, verifiable
**semantic layer** that preserves what a system's parts mean in context.

AAT approaches this from the opposite direction:

- **Source code as the single source of truth**: Abstract facts from existing
  code into **Atoms** and express design rules as **Laws**, capturing design
  roles and preservation conditions beyond syntax, types, and call graphs —
  independently of any programming language or framework.
- **Architecture as a system of equations**: When Laws act as algebraic
  equations on realizations and changes, their solutions form a **geometric
  space**. Algebraic geometry is the mathematics built for such spaces — turning
  local-versus-global failures into computable **obstructions**, scoped fixes
  into **repairs**, and minimal reading into **observation sufficiency**.

## AAT (Algebraic Architecture Theory)

Formally, AAT is a pure mathematical theory that starts from typed declarations
of states, operations, relations, quantities, and Laws, defining **models** that
satisfy those Laws and structure-preserving **morphisms** between them. Realizing
models over commutative rings lifts realizations, changes, and repairs into
algebraic geometry, where the theory investigates four core questions:

- what realizations and semantics-preserving changes are possible under given constraints;
- whether inconsistencies can be repaired within a permitted scope, what obstructions
  block repair, and what degrees of freedom remain;
- what observations are sufficient to decide repairability, select a solution, or
  integrate revisions and multiple sources;
- how global objects, morphisms, and repairs can be reconstructed from local records,
  and when finite information determines them.

- [Mathematical Text (Table of Contents)](docs/aat/algebraic_geometric_theory/README.md) (Japanese)
- [Introduction](docs/aat/algebraic_geometric_theory/introduction.md) (Japanese)

## SFT (Software Field Theory)

SFT models software evolution as dynamics on the architecture geometry provided
by AAT. Its central object is a **Development System**:

```text
𝔇 = (𝒯, 𝔛, 𝔖, Π, 𝔐)

𝒯 : development trace site and time
𝔛 : evolution family, space, and transport data
𝔖 : source and organization structure
Π : policy and laws of motion
𝔐 : measurement profiles and observation
```

Requirements, specifications, issues, PRs, reviews, CI, organizational structure,
AI proposals, and lifecycle decisions are modeled as sources, policies,
observations, and transitions in order to analyze which future architectures
become reachable.

- [Software Field Theory](docs/sft/software_field_theory.md) (Japanese)

## Tooling

The repository includes a set of tools that connect AAT and SFT to real codebases
and development artifacts:

- **ArchSig**: A deterministic Rust engine that computes structures, Law checks,
  diagnostics, repair candidates, and required observations from Atom definitions,
  Laws, and ArchMap evidence.
- **ArchView**: Visualizes ArchMap Atom geometry and overlays ArchSig analysis
  results, linking findings back to source locations.
- **FieldSig**: Combines ArchSig measurement outputs with development workflow
  evidence for SFT-oriented evolution measurement.

See [Tooling Documentation](docs/tool/README.md) for specifications, build steps,
and usage.

## Lean Formalization

Formal definitions and machine-checked proofs of the AAT mathematical text live
under `Formal/SHIGURE/` ([Formal/SHIGURE.lean](Formal/SHIGURE.lean)) using Lean 4
and mathlib.

Full Lean builds and kernel axiom audits run in CI. Locally, check a single file
or a targeted module:

```bash
lake env lean Formal/SHIGURE/Part1/Reading.lean
lake build +Formal.SHIGURE
```

## Repository Structure

| Path | Description | Entry point |
| --- | --- | --- |
| `docs/aat/` | AAT mathematical text and guidelines | [AAT Mathematical Text](docs/aat/algebraic_geometric_theory/README.md) |
| `docs/sft/` | SFT theory text and AAT/SFT interface | [Software Field Theory](docs/sft/software_field_theory.md) |
| `docs/tool/` | Tool concepts, specifications, and usage | [Tooling Documentation](docs/tool/README.md) |
| `docs/reports/` | Fixed experiment reports and evidence | [Reports](docs/reports/README.md) |
| `Formal/` | Lean 4 formalization (`Formal/SHIGURE/`) | [Formal/SHIGURE.lean](Formal/SHIGURE.lean) |
| `tools/` | Implementations of ArchSig, ArchView, and FieldSig | [Tooling Documentation](docs/tool/README.md) |
| `website/` | Public site built with Eleventy (Cloudflare Pages) | [website/src/index.html](website/src/index.html) |
| `outreach/` | Articles, papers, and monograph PDF pipeline | [outreach/README.md](outreach/README.md) |
| `research/` | Research goals, explorations, and `research/lean/` | [research/README.md](research/README.md) |

## License

This repository is licensed under the MIT License. See [LICENSE](LICENSE).
