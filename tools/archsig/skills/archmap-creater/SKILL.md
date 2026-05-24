---
name: archmap-creater
description: Create bounded ArchMap and IntentMap artifacts. Use when Codex is asked to draft, generate, update, or validate an archmap-v0 or intentmap-v0 JSON file, prepare an ArchMap source inventory or prompt pack, run the archmap-generate protocol, align PRD / Epic / Spec intent to architecture evidence, or turn code/docs/tests/runtime hints into LLM-authored mapping evidence.
---

# ArchMap Creater

## Purpose

Create `archmap-v0` and `intentmap-v0` as bounded LLM-authored evidence. Treat ArchMap as a source-to-architecture mapping artifact and IntentMap as a source-to-intent mapping artifact. Either may feed AIR or SFT projections, but neither is ground truth, Lean proof, forecast correctness, implementation plan completeness, or causal diagnosis.

## Inputs

Collect only evidence the user allows and record the boundary explicitly:

- source inventory paths, included refs, excluded refs, private refs, unavailable refs, known blind spots
- code, docs, tests, PR context, runtime hints, framework adapters, or policy files
- PRD / Epic / Spec / Issue / proposal text when creating IntentMap
- the requested architecture scope and target representation
- any prompt pack or model provenance needed for reproducibility

This skill must work with only the skill bundle and a built `archsig` executable. Do not require
the ArchSig source repository, `docs/tool`, or test fixtures to be present.

Use this command form by default:

```bash
${ARCHSIG_BIN:-archsig} <command> ...
```

When working inside the ArchSig source repository, these optional source references may help:

- `docs/tool/archsig_archmap_prd_v2.md`
- `docs/tool/archmap_prd.md`
- `tools/archsig/docs/commands.md`
- `tools/archsig/tests/fixtures/minimal/archmap.json`
- `tools/archsig/tests/fixtures/minimal/archmap_source_inventory.json`
- `tools/archsig/tests/fixtures/expressiveness/archmap_expressiveness_suite_v0.json`

## Workflow

1. Identify the source universe.
   - Write down included, excluded, private, and unavailable references.
   - Preserve blind spots instead of filling them with guesses.
   - Do not infer evidence from files that were not read or supplied.
   - For a new repository or unfamiliar area, read `references/repository-survey.md` first.
   - For non-trivial authoring, read `references/mapping-guide.md` before drafting map items.
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

3. Draft `archmap-v0`.
   - Use `mapItems[]` as the unit of mapping.
   - Keep `sourceRefs`, `targetRef`, `preserves`, `forgets`, `claimClassification`, `measurementBoundary`, `confidence`, `missingEvidence`, and `nonConclusions` explicit.
   - Separate AAT-facing items from SFT-facing items. Shared source refs are allowed; proof claims and forecast inputs must not be conflated.
   - Include semantic structure only when evidence supports it.

4. Draft `intentmap-v0` when the task is planning or PRD forecast.
   - Use `items[]` as the unit of requirement / operation / workflow / state transition / invariant / acceptance / non-goal / ambiguity.
   - Keep `intentItemId`, `intentKind`, `sourceRefs`, `targetIntentRef`, `preserves`, `forgets`, `claimClassification`, `confidence`, `requiredAssumptions`, `missingDecisions`, `missingEvidence`, and `nonConclusions` explicit.
   - Put unresolved product choices in `missingDecisions[]`; do not fill them with guesses.
   - Put ambiguous wording in `ambiguousIntents[]`; do not convert it to measured support.
   - Keep confidence as review priority, not probability.

5. Validate the result.

```bash
${ARCHSIG_BIN:-archsig} archmap \
  --input <archmap.json> \
  --out .archsig/archmap/validation.json

${ARCHSIG_BIN:-archsig} intent-map \
  --input <intentmap.json> \
  --out .archsig/intent/intentmap-validation.json
```

6. For planning forecast, create or validate `intent-archmap-alignment-v0`.
   - Link IntentMap item ids to ArchMap map item ids.
   - Use `intentUnaligned`, unsupported intent, ambiguous alignment, and missing evidence boundaries when the current ArchMap does not support the intent.
   - Validate with both artifacts when available.

```bash
${ARCHSIG_BIN:-archsig} intent-archmap-alignment \
  --input <alignment.json> \
  --intent-map <intentmap.json> \
  --archmap <archmap.json> \
  --out .archsig/intent/alignment-validation.json
```

7. Read the validation report before handing the artifact downstream.
   - Treat failures as schema or boundary problems to fix.
   - Treat warnings as review cues, not automatic rejection.
   - Check `formalPromotionGuardrailChecks`, `leanPreservationPreconditionChecklist`, `sourceInventoryChecks`, conflicts, missing evidence, and non-conclusions.

## Writing Rules

- Preserve uncertainty in fields; do not erase it in prose.
- Never claim that `archmap-v0` validates architecture lawfulness.
- Never claim that validation produces a Lean proof term.
- Never put ForecastCone, ConsequenceEnvelope, attractor, basin, incident causality, or quality ranking into ArchMap as computed results.
- Never put implementation plan completeness, forecast correctness, effort estimate, future probability, or resolved product decisions into IntentMap.
- Preserve `missingDecision`, `ambiguousIntent`, `intentUnaligned`, `unsupportedIntent`, and `missingEvidence` as first-class boundaries.
- Do not write implementation progress into PRDs. Use issues, theorem indexes, proof obligations, roadmaps, or PRs for status.

## Handoff

Use `$archsig-executer` after this skill when the user asks to project ArchMap into AIR, SFT input, forecast cone, consequence envelope, or calibration artifacts.

Use `$arch-doctor` after this skill when the user asks what the validated artifacts imply about current architecture state or likely evolution.
