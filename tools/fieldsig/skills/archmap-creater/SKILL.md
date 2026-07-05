---
name: archmap-creater
description: Create bounded ArchMap observation artifacts from repository evidence. Use when Codex is asked to draft, generate, update, or validate an ArchMap JSON file, prepare an ArchMap source inventory or prompt pack, run the archmap-generate protocol, or turn code/docs/tests/runtime hints into LLM-authored Atom observation evidence.
---

# ArchMap Creater

## Purpose

Create an ArchMap observation artifact as bounded LLM-authored Atom observation evidence. Treat ArchMap as a source-grounded observation map that records observed atoms, molecules, semantic observations, gaps, projection notes, and concern hints for later ArchSig analysis. It is not ground truth, certified atom truth, obstruction analysis, Lean proof, forecast correctness, or causal diagnosis.

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
- `tools/fieldsig/tests/fixtures/minimal/archmap.json`
- `tools/fieldsig/tests/fixtures/minimal/archmap_source_inventory.json`

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

```bash
${ARCHSIG_BIN:-archsig} archmap-generate \
  --source-inventory <source-inventory.json> \
  --prompt-pack <prompt-pack.md> \
  --provider external-agent \
  --model-id <model-or-agent-id> \
  --out .archsig/archmap/generation-protocol.json
```

3. Draft the ArchMap observation artifact.
   - Use `atomObservations[]` for source-grounded primitive observations.
   - Use `moleculeObservations[]` for composed roles such as responsibility over atom observation refs.
   - Use `semanticObservations[]` for selected behavioral, contract, workflow, or diagram readings supported by sources.
   - Use `observationGaps[]` for unknown/private/unavailable/out-of-scope evidence; never round gaps to absence.
   - Use `projectionInfo[]` only as downstream reading hints, not as proof or lawfulness claims.
   - Use `concernHints[]` only as review cues. A concern hint is not an obstruction circuit; ArchSig constructs law-relative obstruction readings only after combining ArchMap with LawPolicy.
   - Keep `sourceRefs`, `observationStatus`, `evidenceBoundary`, `confidence`, `uncertainty`, `projectionRefs`, and `nonConclusions` explicit.
   - Separate AAT-facing observations from SFT-facing projection hints. Shared source refs are allowed; proof claims and forecast inputs must not be conflated.
   - Include semantic structure only when evidence supports it.

4. Validate the result.

```bash
${ARCHSIG_BIN:-archsig} archmap \
  --input <archmap.json> \
  --out .archsig/archmap/validation.json

```

5. Build downstream analysis through `archsig analyze` when a LawPolicy is available.

```bash
${ARCHSIG_BIN:-archsig} law-policy \
  --input <law-policy.json> \
  --out .archsig/law-policy/validation.json

${ARCHSIG_BIN:-archsig} analyze \
  --archmap <archmap.json> \
  --law-policy <law-policy.json> \
  --out-dir .archsig/analyze
```

6. Read the validation report before handing the artifact downstream.
   - Treat failures as schema or boundary problems to fix.
   - Treat warnings as review cues, not automatic rejection.
   - Check `formalPromotionGuardrailChecks`, `leanPreservationPreconditionChecklist`, `sourceInventoryChecks`, `atomicObservationChecks`, `atomicObservationSummary`, conflicts, missing evidence, and non-conclusions.

## Writing Rules

- Preserve uncertainty in fields; do not erase it in prose.
- Never claim that an ArchMap observation artifact validates architecture lawfulness.
- Never claim that `atomObservations[]` certifies universal `ArchitectureAtom` truth.
- Never put obstruction circuits in ArchMap. Use `concernHints[]` for source-grounded review cues and let ArchSig + LawPolicy construct law-relative obstruction readings.
- Never treat responsibility as a primitive atom; use `moleculeObservations[]`.
- Never claim that validation produces a Lean proof term.
- Never put ForecastCone, ConsequenceEnvelope, attractor, basin, incident causality, or quality ranking into ArchMap as computed results.
- Do not write implementation progress into PRDs. Use issues, theorem indexes, proof obligations, roadmaps, or PRs for status.

## Handoff

Use `$arch-pr-analyzer` after this skill when the user asks what an ArchMap or PR / CI artifact implies for PR quality or current architecture state.

Use FieldSig planning skills after ArchSig has produced `archsig-analysis-packet/v0.5.0` and the user asks for planning forecast.
