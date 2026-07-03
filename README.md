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
AAT makes architecture algebraic-geometric.
ArchSig makes selected architecture evidence measurable.
SFT makes software evolution computable.
```

The project's core philosophy and guiding question are stated in [PHILOSOPHY](PHILOSOPHY.md).
The main entry point for the overall research program is
[Research Goal](docs/research_goal.md).

## Research Question

This project tries to move architecture review from subjective impression
toward explicit diagnosis. Its central questions are:

```text
Does this change preserve the selected architecture invariant?
If not, which obstruction witness shows the break?
Which selected measurement coordinate or law-evaluation profile exposes the break?
Which future architecture does this PRD / Issue / PR make easier to reach?
Which review / CI / policy / governance narrows dangerous trajectories?
```

To answer these questions, the project keeps the following layers separate:

- structural claims proved in Lean;
- claims observed or inferred from artifacts by tooling;
- hypotheses to be tested empirically;
- non-conclusions outside explicit theorem assumptions and forecast scopes.

## Layers

| Layer | Role | Source of truth |
| --- | --- | --- |
| AAT | A pure algebraic-geometric theory that starts from architectural atoms and builds architecture objects, AAT sites, sheaves, law algebras, obstruction ideal sheaves, lawful loci, architecture schemes, Čech descent, derived law geometry, measurement, and evolution geometry. | [AAT algebraic-geometric mathematical text](docs/aat/algebraic_geometric_theory/README.md) |
| AAT / SFT Interface | The interface explaining how local AAT claims are read through SFT projections, observable coordinates, and governance. | [AAT / SFT Interface](docs/sft/aat_interface.md) |
| ArchSig / FieldSig Tooling | ArchSig reads supplied ArchMap evidence, LawPolicy, and MeasurementProfile artifacts into bounded diagnostic / measurement packets. FieldSig measures SFT software evolution evidence from ArchSig refs plus workflow evidence. | [AAT Tooling Documentation](docs/tool/README.md) |
| SFT | A computational theory of how PRDs, specs, issues, PRs, reviews, CI, organizations, AI, and feedback change reachable futures. | [Software Field Theory](docs/sft/software_field_theory.md) |
| Lean formalization | Structural propositions, finite universes, lawfulness bridges, and bounded theorem packages with explicit assumptions. | [Lean definitions and theorem index](docs/aat/lean_theorem_index.md), split into classical / AG / research indexes. |
| Proof / empirical ledger | Theorem assumptions, open proof obligations, empirical hypotheses, and their GitHub Issue links. | [Proof obligations and empirical hypotheses](docs/aat/proof_obligations.md), split into classical / AG / research ledgers. |
| Website | The public reading surface for AAT, SFT, and ArchSig, published as a no-build Cloudflare Pages site. | [Website operating notes](docs/website/README.md) and [website source](website/index.html) |

The README does not duplicate detailed theorem lists or progress ledgers.
Current Lean status, non-conclusions, and open proof obligations are tracked
through [Proof obligations and empirical hypotheses](docs/aat/proof_obligations.md)
and [Lean definitions and theorem index](docs/aat/lean_theorem_index.md). Those
entrypoints route to separate classical AAT, algebraic-geometric AAT, and
research-loop ledgers.

Most detailed research notes are currently written in Japanese; English
summaries will be added as the theory and Lean formalization stabilize.

## Reading Order

1. [PHILOSOPHY](PHILOSOPHY.md)
2. [Research Goal](docs/research_goal.md)
3. [AAT Algebraic-Geometric Mathematical Text](docs/aat/algebraic_geometric_theory/README.md)
4. [AAT / SFT Interface](docs/sft/aat_interface.md)
5. [Software Field Theory](docs/sft/software_field_theory.md)
6. [Proof Obligations and Empirical Hypotheses](docs/aat/proof_obligations.md)
7. [Lean Definitions and Theorem Index](docs/aat/lean_theorem_index.md)
8. [AAT Tooling Documentation](docs/tool/README.md)
9. As needed:
   [docs guide](docs/README.md),
   [AAT directory guide](docs/aat/README.md),
   [SFT directory guide](docs/sft/README.md),
   [website operating notes](docs/website/README.md)

## AAT

AAT begins from primitive architectural facts called atoms. An atom axiom system
and atom families generate configurations and architecture objects; after a law
universe, coverage topology, and coefficient data are fixed, those objects are
lifted to architecture geometry: AAT sites, sheaves, law algebras, obstruction
ideal sheaves, lawful loci, architecture schemes, Čech obstruction classes, and
derived law geometry.

```text
AAT
  = atom vocabulary
  + atom axiom system
  + atom family / configuration
  + architecture object
  + law universe
  + coverage topology
  + coefficient sheaf
  + AAT site
  + sheaves
  + law algebra
  + obstruction ideal sheaf
  + lawful locus
  + architecture scheme
  + Čech descent
  + derived law geometry
```

External design vocabulary such as SOLID or Layered Architecture is not an AAT
primitive. When useful, it is read as a concrete law presentation, cover,
restriction-compatibility condition, obstruction ideal, or lawful-locus example
inside a selected algebraic-geometric regime.

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
governance are handled under explicit computable cores and stated claim scopes.

## Tooling

The tooling goal is to connect the vocabulary of AAT and SFT to real development
artifacts. ArchSig reads supplied ArchMap evidence, LawPolicy, and
MeasurementProfile artifacts, then emits bounded diagnostic / measurement
packets that review and CI can handle.

The tooling is not the theory itself. It does not confuse measured zero with
unmeasured, and a tool pass is not read as a Lean theorem.

## Website

The public website in `website/` is a Cloudflare Pages reading surface for AAT, SFT,
and ArchSig. It is not the research ledger or the source of theorem status.
Instead, it presents the theory as web-native preprint / monograph pages and
presents ArchSig as a public manual while preserving the claim discipline kept
in `docs/`.

Website planning and editorial rules live in [docs/website](docs/website/README.md).
The current stack is intentionally no-build: static HTML, CSS, small JavaScript,
MathJax, and local assets under `website/assets`.

## Lean Formalization

See [Lean definitions and theorem index](docs/aat/lean_theorem_index.md) for the
main definitions and theorems currently present on the Lean side. Theorem names,
assumption-relative readings, and non-conclusions are tracked through the
split proof / theorem ledgers linked from
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
  - Canonical algebraic-geometric AAT text, proof obligations, and Lean theorem index.
- `docs/sft`
  - AAT / SFT interface and the SFT body.
- `docs/tool`
  - LLM Atom ArchMap, LawPolicy, ArchSig analysis packet, FieldSig handoff, and tooling claim boundaries.
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
- Record unproved claims in the appropriate split ledger linked from
  `docs/aat/proof_obligations.md`, or in GitHub Issues.
- Keep Lean-proved claims, definition-only concepts, future proof obligations,
  and empirical hypotheses distinct.
- Do not identify AAT theorems, tooling output, SFT forecasts, and empirical
  hypotheses with each other.
- `docs/aat/proof_obligations.md` is an entrypoint to split ledgers that also
  index the relevant GitHub Issues.

## Task Management

Open work is tracked in GitHub Issues. Issues are organized according to the
research dependency structure with milestones and `type:*`, `area:*`,
`priority:*`, and `status:*` labels. The README does not duplicate the issue
list.

## License

This repository is licensed under the MIT License. See [LICENSE](LICENSE).


## FieldSig

FieldSig is the SFT-based software evolution measurement crate under `tools/fieldsig`. Run `cargo test --manifest-path tools/fieldsig/Cargo.toml` for FieldSig changes. ArchSig remains the selected architecture-evidence measurement and bounded diagnostic crate under `tools/archsig`.
