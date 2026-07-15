---
name: archmap-creater
description: Create bounded ArchMap evidence artifacts from repository evidence. Use when Codex is asked to draft, update, or validate an ArchMap JSON file, prepare a source inventory or prompt pack, or turn code/docs/tests/runtime hints into LLM-authored Atom evidence.
---

# ArchMap Creater

## Purpose

Create an ArchMap evidence artifact as bounded LLM-authored Atom evidence. Treat ArchMap as a source-grounded map of sources, atoms, contexts, and covers for later ArchSig analysis. It is not ground truth, certified atom truth, obstruction analysis, Lean proof, forecast correctness, or causal diagnosis.

## Inputs

Collect only evidence the user allows and record the boundary explicitly:

- source inventory paths, included refs, excluded refs, private refs, unavailable refs, known blind spots
- code, docs, tests, PR context, runtime hints, framework adapters, or policy files
- the requested architecture scope and target representation
- any prompt pack or model provenance needed for reproducibility

This skill must work with only the skill bundle and a built `archsig` executable. Do not require
the ArchSig source repository, legacy `docs/tool` documents, or test fixtures to be present.

Use this command form by default:

```bash
${ARCHSIG_BIN:-archsig} <command> ...
```

When working inside the ArchSig source repository, these optional source references may help:

- `tools/archsig/docs/commands.md`
- `tools/archsig/docs/artifacts-and-boundaries.md`
- `tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json`
- `tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json`

## Workflow

1. Identify the source universe.
   - Write down included, excluded, private, and unavailable references.
   - Preserve blind spots instead of filling them with guesses.
   - Do not infer evidence from files that were not read or supplied.
   - For a new repository or unfamiliar area, read `references/repository-survey.md` first.
   - For non-trivial authoring, read `references/mapping-guide.md` before drafting observations.
   - When unsure about field values, read `references/schema-cheatsheet.md`.
   - When checking output quality, compare against `references/examples.md`.

2. Generate or update the protocol artifact when useful.

The protocol artifact is maintained by the external authoring workflow; do not invoke a retired ArchSig subcommand.

3. Draft the ArchMap observation artifact.
   - Use the current `archmap/v0.5.0` fields: `sources`, `atoms`, `contexts`, and `covers`.
   - Give each atom a source-grounded `id`, `kind`, `subject`, `axis`, and optional `predicate`, `object`, `refs`, or `label`.
   - Bind context and cover membership through `contexts[].atoms`, `contexts[].restrictsTo`, and `covers[].contexts`; use `refs` for declared source keys.
   - Keep source details in the top-level `sources` map and use the fixed `extractionDoctrineRef`; do not invent observation, gap, projection, or concern fields.
   - Preserve uncertainty and unavailable evidence in the source selection or review notes; never round missing evidence to an atom or verdict.

4. Validate the result.

```bash
${ARCHSIG_BIN:-archsig} archmap \
  --input <archmap.json> \
  --out .archsig/archmap/validation.json

```

5. Build downstream analysis through `archsig analyze` when a LawPolicy is available.

```bash
${ARCHSIG_BIN:-archsig} law-policy \
  --law-policy <law-policy.json> \
  --measurement-profile <measurement-profile.json> \
  --out .archsig/law-policy/validation.json

${ARCHSIG_BIN:-archsig} analyze \
  --archmap <archmap.json> \
  --law-policy <law-policy.json> \
  --measurement-profile <measurement-profile.json> \
  --out-dir .archsig/analyze
```

6. Read the validation report before handing the artifact downstream.
   - Treat failures as schema or boundary problems to fix.
   - Treat warnings as review cues, not automatic rejection.
   - Check the report `checks`, `summary`, and `nonConclusions`; fix failures before handing the artifact downstream.

## Writing Rules

- Preserve uncertainty in fields; do not erase it in prose.
- Never claim that an ArchMap evidence artifact validates architecture lawfulness.
- Never claim that authored ArchMap evidence certifies universal `ArchitectureAtom` truth.
- Never put obstruction circuits in ArchMap; let ArchSig + LawPolicy construct law-relative obstruction readings.
- Never claim that validation produces a Lean proof term.
- Never put ForecastCone, ConsequenceEnvelope, attractor, basin, incident causality, or quality ranking into ArchMap as computed results.
- Do not write implementation progress into PRDs. Use issues, theorem indexes, proof obligations, roadmaps, or PRs for status.

## Handoff

Use `$arch-pr-analyzer` after this skill when the user asks what an ArchMap or PR / CI artifact implies for PR quality or current architecture state.

Use FieldSig planning skills after ArchSig has produced `archsig-measurement-packet/v0.5.3` with all three component fingerprints and the user asks for planning forecast.
