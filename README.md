# Algebraic Architecture Theory & Software Field Theory

[日本語版はこちら](README.jp.md)

This repository contains the Lean formalization, research notes, and tooling
design for **Algebraic Architecture Theory** (AAT) and **Software Field Theory**
(SFT).

The long-term goal is to treat software architecture not only as a static
shape, but as an object that keeps changing through implementation, review, CI,
operations, and AI-agent proposals. The project aims to build a theory and
toolchain for diagnosing what is preserved, what breaks, and which futures a
software system becomes more likely to reach.

```text
AAT makes architecture locally algebraic.
ArchSig makes architecture observable.
SFT makes software evolution computable.
```

The main entry point for the overall research program is
[Research Goal](docs/research_goal.md).

## Research Question

This project tries to move architecture review from subjective impression
toward explicit diagnosis. Its central questions are:

```text
Does this change preserve the selected architecture invariant?
If not, which obstruction witness shows the break?
Which ArchitectureSignature axis exposes the break?
Which future architecture does this PRD / Issue / PR make easier to reach?
Which review / CI / policy / governance narrows dangerous trajectories?
```

To answer these questions, the project keeps the following layers separate:

- structural claims proved in Lean;
- claims observed or inferred from artifacts by tooling;
- hypotheses to be tested empirically;
- non-conclusions outside explicit theorem and forecast boundaries.

## Layers

| Layer | Role | Source of truth |
| --- | --- | --- |
| AAT | A local algebra for architecture objects, operations, invariants, obstruction witnesses, signatures, and theorem boundaries. | [AAT mathematical theory](docs/aat/mathematical_theory.md) |
| AAT / SFT Interface | The boundary explaining how local AAT claims are read through SFT projections, observable coordinates, and governance. | [AAT / SFT Interface](docs/sft/aat_interface.md) |
| ArchSig / FieldSig Tooling | ArchSig reads supplied ArchMap evidence into AAT structural review artifacts; Lean / Python scans are optional bounded adapters. FieldSig measures SFT software evolution evidence from ArchSig refs plus workflow evidence. | [AAT Tooling Documentation](docs/tool/README.md) |
| SFT | A computational theory of how PRDs, specs, issues, PRs, reviews, CI, organizations, AI, and feedback change reachable futures. | [Software Field Theory](docs/sft/software_field_theory.md) |
| Lean formalization | Structural propositions, finite universes, lawfulness bridges, and bounded theorem packages with explicit assumptions. | [Lean definitions and theorem index](docs/aat/lean_theorem_index.md) |
| Proof / empirical ledger | Theorem boundaries, open proof obligations, empirical hypotheses, and their GitHub Issue links. | [Proof obligations and empirical hypotheses](docs/aat/proof_obligations.md) |
| Website | The public reading surface for AAT, SFT, and ArchSig, published as a no-build Cloudflare Pages site. | [Website operating notes](docs/website/README.md) and [website source](website/index.html) |

The README does not duplicate detailed theorem lists or progress ledgers.
Current Lean status, non-conclusion boundaries, and open proof obligations are
tracked in [Proof obligations and empirical hypotheses](docs/aat/proof_obligations.md)
and [Lean definitions and theorem index](docs/aat/lean_theorem_index.md).

Most detailed research notes are currently written in Japanese; English
summaries will be added as the theory and Lean formalization stabilize.

## Reading Order

1. [Research Goal](docs/research_goal.md)
2. [AAT Mathematical Theory](docs/aat/mathematical_theory.md)
3. [AAT / SFT Interface](docs/sft/aat_interface.md)
4. [Software Field Theory](docs/sft/software_field_theory.md)
5. [Proof Obligations and Empirical Hypotheses](docs/aat/proof_obligations.md)
6. [Lean Definitions and Theorem Index](docs/aat/lean_theorem_index.md)
7. [AAT Tooling Documentation](docs/tool/README.md)
8. As needed:
   [docs guide](docs/README.md),
   [AAT directory guide](docs/aat/README.md),
   [SFT directory guide](docs/sft/README.md),
   [website operating notes](docs/website/README.md)

## AAT

AAT treats a bounded piece of software architecture as an `ArchitectureObject`.
It studies which invariants are preserved by operations on that object, which
obstruction witnesses are produced when preservation fails, and which signature
axes expose the break.

```text
software architecture
  = ArchitectureObject
  + ArchitectureOperation
  + InvariantFamily
  + ObstructionWitness
  + ArchitectureSignature
  + theorem boundary / non-conclusions
```

AAT reads design principles as operations rather than slogans. SOLID,
Layered / Clean Architecture, Event Sourcing, Saga, Circuit Breaker, Replicated
Log, and related patterns are not treated as universal maxims. Instead, the
theory asks which invariants, operations, observations, and theorem boundaries
each principle is connected to.

## SFT

SFT treats software evolution as a computable object. A codebase is not a static
structure that merely receives changes. PRDs, specs, issues, PRs, reviews, CI,
organizations, AI, and lifecycle decisions all shape which future changes
become likely, which breaks are easy to miss, which constraints accumulate, and
which shortcuts are dampened.

SFT uses the local algebra of AAT through architecture projections, observable
coordinates, local transition laws, and governance inputs in the field model.
However, AAT theorems do not automatically become empirical forecasts.
`ForecastCone`, `ConsequenceEnvelope`, `FieldUpdate`, and AI proposal
governance are handled under explicit computable cores and claim boundaries.

## Tooling

The tooling goal is to connect the vocabulary of AAT and SFT to real development
artifacts. ArchSig extracts observable evidence from codebases, PRs, reports,
and policies, then turns it into signature axes, obstruction witnesses, theorem
boundary status, and forecast boundaries that review and CI can handle.

The tooling is not the theory itself. It does not confuse measured zero with
unmeasured, and a tool pass is not read as a Lean theorem.

## Website

The public website in `website/` is a Cloudflare Pages reading surface for AAT, SFT,
and ArchSig. It is not the research ledger or the source of theorem status.
Instead, it presents the theory as web-native preprint / monograph pages and
presents ArchSig as a public manual while preserving the claim boundaries kept
in `docs/`.

Website planning and editorial rules live in [docs/website](docs/website/README.md).
The current stack is intentionally no-build: static HTML, CSS, small JavaScript,
MathJax, and local assets under `website/assets`.

## Lean Formalization

See [Lean definitions and theorem index](docs/aat/lean_theorem_index.md) for the
main definitions and theorems currently present on the Lean side. Theorem names,
bounded readings, and non-conclusion boundaries are tracked in
[Proof obligations and empirical hypotheses](docs/aat/proof_obligations.md) and
[Lean definitions and theorem index](docs/aat/lean_theorem_index.md).

The static structural core of the architecture zero-curvature theorem is proved
in Lean. Runtime metrics, empirical hypotheses, general numerical curvature, and
completeness of real-code extractors are not included in that QED.

## Repository Layout

- `Formal.lean`
  - Public entry point of the Lean library.
- `Formal/Arch`
  - Lean formalization split into `Core`, `Law`, `Signature`, `Extension`,
    `Operation`, `Patterns`, `Repair`, `Evolution`, and `Examples`.
  - See [Lean definitions and theorem index](docs/aat/lean_theorem_index.md)
    for main definitions, theorem names, and module paths.
- `docs`
  - First-class theory documents, Lean status, proof obligations, tool docs,
    and empirical protocol.
- `docs/aat`
  - AAT mathematical theory, proof obligations, and Lean theorem index.
- `docs/sft`
  - AAT / SFT interface and the SFT body.
- `docs/tool`
  - AIR, extractor, report, claim boundary, workflow, and schema compatibility.
- `docs/website`
  - Internal operating notes for the public website, including sitemap, design,
    tone, and publication rules.
- `website`
  - No-build static Cloudflare Pages site for the public AAT / SFT / ArchSig reading
    surface.
- `Main.lean`
  - Minimal entry point for the executable target `aatv2`.
- `lakefile.toml`
  - Lake build configuration.
- `lean-toolchain`
  - Pinned Lean version.

## Build

```bash
lake build
lake build Formal
lake exe aatv2
```

The output of `lake exe aatv2` is:

```text
Algebraic Architecture Theory V2
```

## Proof And Documentation Policy

- Do not introduce `axiom`, `admit`, `sorry`, or `unsafe` into Lean sources.
- Record unproved claims in `docs/aat/proof_obligations.md` or GitHub Issues.
- Keep Lean-proved claims, definition-only concepts, future proof obligations,
  and empirical hypotheses distinct.
- Do not identify AAT theorems, tooling output, SFT forecasts, and empirical
  hypotheses with each other.
- `docs/aat/proof_obligations.md` also serves as an index to GitHub Issues.

## Task Management

Open work is tracked in GitHub Issues. Issues are organized according to the
research dependency structure with milestones and `type:*`, `area:*`,
`priority:*`, and `status:*` labels. The README does not duplicate the issue
list.

## License

This repository is licensed under the MIT License. See [LICENSE](LICENSE).


## FieldSig

FieldSig is the SFT-based software evolution measurement crate under `tools/fieldsig`. Run `cargo test --manifest-path tools/fieldsig/Cargo.toml` for FieldSig changes. ArchSig remains the AAT structural telemetry generator under `tools/archsig`.
