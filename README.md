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
The research-loop operating entry is [research/README.md](research/README.md), with
GOAL definitions under [research/goals](research/goals/README.md).

## Research Question

This project treats a codebase as an algebraic-geometric architecture object and
asks how its local-to-global structure can be described. Its central questions are:

```text
Can the local structure, laws, obstructions, repairs, and evolution of a codebase
be described as algebraic-geometric architecture?
How does that geometry change through implementation, review, CI, operations,
and AI proposals?
Which future architectures become reachable through those changes?
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
| AAT / SFT Interface | The interface between the pure AAT theory and SFT's development-system model. The current SFT v2 reading is in the SFT body; the separate interface note still contains v1 material. | [Software Field Theory](docs/sft/software_field_theory.md) and [AAT / SFT interface note](docs/sft/aat_interface.md) |
| ArchSig / ArchView / FieldSig Tooling | ArchSig reads supplied ArchMap evidence, LawPolicy, and MeasurementProfile artifacts into bounded diagnostic / measurement packets. ArchView reads ArchMap Atom geometry directly and overlays supplied ArchSig analysis without creating a new verdict. FieldSig consumes serialized ArchSig measurement packets together with workflow evidence for SFT-oriented evolution measurement. | [AAT Tooling Documentation](docs/tool/README.md) |
| SFT | SFT v2 models software evolution through a Development System containing development time, evolution space and transport, sources, policy, and measurement profiles. | [Software Field Theory](docs/sft/software_field_theory.md) |
| Lean formalization | Structural propositions, finite universes, lawfulness bridges, and bounded theorem packages with explicit assumptions. | Lean source under `Formal/`. |
| Website | The public reading surface for AAT, SFT, and ArchSig. It is authored and built with Eleventy, then published as a static Cloudflare Pages site. | [Website source](website/src/index.html) |

Most detailed research notes are currently written in Japanese; English
summaries will be added as the theory and Lean formalization stabilize.

## Reading Order

1. [PHILOSOPHY](PHILOSOPHY.md)
2. [AAT Algebraic-Geometric Mathematical Text](docs/aat/algebraic_geometric_theory/README.md)
3. [Software Field Theory](docs/sft/software_field_theory.md)
4. [AAT Tooling Documentation](docs/tool/README.md)
5. [Research-loop operating guide](research/README.md)
6. As needed:
   [docs guide](docs/README.md),
   [AAT directory guide](docs/aat/README.md),
   [SFT directory guide](docs/sft/README.md),
   [AAT / SFT interface note](docs/sft/aat_interface.md)

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

SFT v2 treats software evolution as a computable development system rather than
as a static codebase that merely receives changes. Its central object is
represented by

```text
𝔇 = (𝒯, 𝔛, 𝔖, Π, 𝔐)

𝒯 : development trace site and time
𝔛 : evolution family, space, and transport data
𝔖 : source and organization structure
Π : policy and laws of motion
𝔐 : measurement profiles and observation
```

PRDs, specs, issues, PRs, reviews, CI, organizations, AI, and lifecycle
decisions become selected sources, policies, observations, and transitions in
this model. SFT uses AAT through architecture projections and selected local
algebra, but AAT theorems do not automatically become empirical forecasts.
Older v1 names such as `ForecastCone` and `ConsequenceEnvelope` remain only in
legacy or compatibility surfaces and should not be read as the current SFT v2
center.

## Tooling

The tooling goal is to connect the vocabulary of AAT and SFT to real development
artifacts. ArchSig reads supplied ArchMap evidence, LawPolicy, and
MeasurementProfile artifacts, then emits bounded diagnostic / measurement
packets that review and CI can handle. The current handoff is the serialized
`archsig-measurement-packet/v0.5.0`; FieldSig consumes that packet together with
workflow and operational evidence for SFT-oriented measurement.

The tooling is not the theory itself. It does not confuse measured zero with
unmeasured, and a tool pass is not read as a Lean theorem.

## Website

The public website in `website/` is a Cloudflare Pages reading surface for AAT, SFT,
and ArchSig. It is authored with Eleventy from `website/src/` and published as
static output.

## Repository Layout

- `Formal`
  - Lean formalization and theorem packages.
- `docs`
  - First-class theory documents, tool docs, and empirical protocol.
  - `docs/aat`
  - Canonical algebraic-geometric AAT text and supporting notes.
- `docs/sft`
  - AAT / SFT interface and the SFT body.
- `docs/tool`
  - LLM Atom ArchMap, LawPolicy, ArchSig analysis packet, FieldSig handoff, and tooling claim boundaries.
- `docs/website`
  - Internal operating notes for the public website, including sitemap, design,
    tone, and publication rules.
- `research`
  - Research-loop operating guide, GOAL definitions, candidate ideas, and reports.
- `tools`
  - ArchSig, ArchView, and FieldSig tooling, schemas, fixtures, and skills.
- `website`
  - Eleventy source under `src/` and static Cloudflare Pages output for the public
    AAT / SFT / ArchSig reading surface.
- `outreach`
  - External article drafts, English and Japanese translations, and publication assets
    for AAT, SFT, and ArchSig.
- `lakefile.toml`
  - Lake build configuration.
- `lean-toolchain`
  - Pinned Lean version.

## Build

The root-wide full Lean build for the main package is run by CI after a pull request is opened. Choose a local check that matches the change scope; for example, a single target file or a targeted module build:

```bash
lake env lean Formal/AG/Atom/Atom.lean
lake build +Formal.AG
```

## License

This repository is licensed under the MIT License. See [LICENSE](LICENSE).
