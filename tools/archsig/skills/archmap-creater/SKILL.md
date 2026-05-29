---
name: archmap-creater
description: Create bounded ArchMap observation artifacts from repository evidence. Use when Codex is asked to draft, generate, update, or validate an archmap-observation-map-v0 JSON file, prepare an ArchMap source inventory or prompt pack, run the archmap-generate protocol, or turn code/docs/tests/runtime hints into LLM-authored Atom observation evidence.
---

# ArchMap Creater

## Purpose

Create `archmap-observation-map-v0` as bounded LLM-authored Atom observation evidence.

ArchMap is an observation map, not an extractor result and not architecture truth. The LLM reads selected source evidence, records observed primitive architectural facts as Atom observations, records composed roles as Molecule observations, records selected semantic readings, and preserves gaps. ArchSig later combines this ArchMap with LawPolicy to produce law-relative analysis.

ArchMap does not prove Atom truth, architecture lawfulness, zero curvature, obstruction circuits, Lean theorem discharge, forecast correctness, or causal diagnosis.

## Inputs

Collect only evidence the user allows and record the boundary explicitly:

- source inventory paths, included refs, excluded refs, private refs, unavailable refs, known blind spots
- code, docs, tests, PR context, runtime hints, framework convention notes, generated artifacts, or policy files
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
- `tools/archsig/tests/fixtures/minimal/archmap.json`
- `tools/archsig/tests/fixtures/minimal/archmap_source_inventory.json`

## Atom Reading Rules

Use these rules before writing any observation.

- An Atom is a primitive architectural fact: a small typed fact such as component existence, relation, capability, state, effect, authority, trust, contract, semantic fact, or runtime interaction.
- An Atom observation is the LLM's bounded observation of such a fact from selected sources. It is not the certified canonical Atom itself.
- An Atom observation has no coarse/fine scale. If the reading needs to be split into smaller architectural facts, it is not yet an atom observation.
- A Molecule observation composes Atom observations into a higher role such as responsibility. Do not model responsibility as a primitive atom.
- A Semantic observation records a source-supported meaning, contract reading, workflow reading, or commutation cue. It is not global semantic correctness.
- A Concern hint records a review cue over observations. It is not an obstruction circuit or law violation.
- A Projection info entry is a downstream handoff hint, especially toward AAT or SFT surfaces. It is not proof or forecast output.
- An Observation gap records unavailable, private, unmeasured, or out-of-scope evidence. Never rewrite missing evidence as measured absence.
- Static structure, ASTs, symbol indexes, route lists, and framework conventions may guide navigation, but they do not by themselves create an atom. The source text still has to support the architectural fact being recorded.

Before writing an atom observation, ask:

1. What exact architectural fact is observed?
2. Which selected source refs directly support it?
3. Is it primitive, or is it a responsibility, workflow, policy reading, concern, or gap?
4. What evidence boundary prevents overclaiming?

If any answer is unclear, do not write an atom yet. Read more source evidence, lower the confidence, or record an observation gap.

Common Atom families:

| atomFamily | Record when the selected source directly shows | Do not record when |
| --- | --- | --- |
| `existence` | component, module, service, class, package, process, table, queue, or public surface exists | the only evidence is a guessed layer or inferred runtime instance |
| `relation` | import, call, read, write, publish, subscribe, ownership, implementation, or explicit dependency edge | the edge is only a naming similarity, directory proximity, or framework convention not inspected |
| `capability` | command, query, handler, port, interface, storage access, serializer, processor, or tool surface | the statement is really an end-to-end workflow or responsibility |
| `state` | field, table column, cache entry, config value, event projection, lifecycle status, durable job marker | the fact is a transient runtime value with no supplied source or trace |
| `effect` | database write, message send, email, payment, event publish, remote call, file/object storage mutation, provider call | the effect is only possible from a library name and no effecting code was read |
| `authority` | permission check, owner scope, role gate, visibility boundary, access path, policy scope, admin bypass | the source only names a user or role without an observed guard or authority state |
| `trust` | trusted source, delegated authority, token verification, webhook boundary, integration trust, provider output boundary | the source merely calls an external library without a trust decision or boundary |
| `contractSpecification` | precondition, postcondition, return shape, error behavior, invariant, validation rule, retry or idempotency contract | a test or doc is being generalized to all executions |
| `semantic` | source-supported domain meaning, identity meaning, ownership meaning, unit meaning, workflow term meaning | the statement is a large workflow reading better represented as `semanticObservations[]` |
| `runtimeInteraction` | trace/log-supported runtime call, edge, message, or effect | runtime evidence was unavailable or only expected |

If a source can support both a primitive fact and a larger interpretation, write the primitive fact in `atomObservations[]` first. Put the larger interpretation in `moleculeObservations[]`, `semanticObservations[]`, `projectionInfo[]`, or `concernHints[]`.

See `references/mapping-guide.md` for atomFamily-specific yes/no examples and `references/schema-cheatsheet.md` for required evidence metadata.

## Observation Surface Decision Rules

Choose the output surface by the role of the reading, not by how important it feels:

| Candidate reading | Use | Do not use |
| --- | --- | --- |
| One primitive source-grounded architectural fact | `atomObservations[]` | `moleculeObservations[]` just because the fact is important |
| A responsibility, role, or pattern composed from several atom refs | `moleculeObservations[]` | `atomObservations[]` with `atomFamily: "responsibility"` |
| A workflow, operation meaning, contract behavior reading, policy reading, or commutation cue over atoms/molecules | `semanticObservations[]` | A coarse `semantic` atom that hides multiple facts |
| Missing, private, unavailable, unmeasured, or out-of-scope evidence | `observationGaps[]` | An observed atom claiming absence |
| A downstream AAT/SFT handoff hint | `projectionInfo[]` | A proof, forecast, lawfulness, or quality claim |
| A source-grounded review cue | `concernHints[]` | An obstruction circuit or law violation |

Workflow-first exploration is allowed: you may read a workflow to discover atoms. The ArchMap output must still put primitive facts in atoms and the workflow reading in `semanticObservations[]` after the atoms exist.

## Workflow

1. Identify the bounded source universe.
   - Write down included, excluded, private, and unavailable references.
   - Preserve blind spots instead of filling them with guesses.
   - Do not infer evidence from files that were not read or supplied.
   - For a new repository or unfamiliar area, read `references/repository-survey.md` first.
   - For non-trivial authoring, read `references/mapping-guide.md` before drafting observations.
   - When unsure about field values, read `references/schema-cheatsheet.md`.
   - When checking output quality, compare against `references/examples.md`.

2. Create a source inventory file.

Use `.archsig/archmap/source-inventory.json` by default. Minimal shape:

```json
{
  "schemaVersion": "archmap-source-inventory-v0",
  "inventoryId": "source-inventory-<scope>",
  "root": ".",
  "includedRefs": [
    {"artifactId": "src-main", "kind": "file", "path": "src/main.ts"}
  ],
  "excludedRefs": [],
  "unavailableRefs": [],
  "privateRefs": [],
  "hashes": [],
  "knownBlindSpots": [],
  "selectionBoundary": "bounded source slice used for this ArchMap",
  "nonConclusions": [
    "source inventory is not complete repository discovery"
  ]
}
```

3. Generate or update the protocol artifact when useful.

```bash
${ARCHSIG_BIN:-archsig} archmap-generate \
  --source-inventory .archsig/archmap/source-inventory.json \
  --prompt-pack tools/archsig/skills/archmap-creater/references/prompt-pack.md \
  --provider external-agent \
  --model-id <model-or-agent-id> \
  --out .archsig/archmap/generation-protocol.json
```

If this skill bundle is copied outside the ArchSig repository, use the local path to `references/prompt-pack.md` inside the copied skill bundle.

4. Draft `.archsig/archmap/archmap.json`.
   - Use `atomObservations[]` for source-grounded primitive observations.
   - For every observed atom, make `sourceRefs[].artifactId` resolve to `sourceUniverse.includedRefs[]` and keep `evidenceBoundary` consistent with what was actually inspected.
   - Put inferred, private, unavailable, framework-expanded, or runtime-only evidence into `observationGaps[]` unless it was directly supplied and read.
   - Use `moleculeObservations[]` for composed roles such as responsibility over atom observation refs.
   - Use `semanticObservations[]` for selected behavioral, contract, workflow, or diagram readings supported by sources.
   - Use `observationGaps[]` for unknown/private/unavailable/out-of-scope evidence; never round gaps to absence.
   - Use `projectionInfo[]` only as downstream reading hints, not as proof or lawfulness claims.
   - Use `concernHints[]` only as review cues. A concern hint is not an obstruction circuit; ArchSig constructs law-relative obstruction readings only after combining ArchMap with LawPolicy.
   - Keep `sourceRefs`, `observationStatus`, `evidenceBoundary`, `confidence`, `uncertainty`, `projectionRefs`, and `nonConclusions` explicit.
   - Separate AAT-facing observations from SFT-facing projection hints. Shared source refs are allowed; proof claims and forecast inputs must not be conflated.
   - Include semantic structure only when evidence supports it.

5. Validate the result.
   - `archsig archmap` reads `sourceInventoryRef.path` from the ArchMap JSON when present.
   - Do not pass repository paths or scan flags; ArchSig does not auto-scan code.

```bash
${ARCHSIG_BIN:-archsig} archmap \
  --input .archsig/archmap/archmap.json \
  --out .archsig/archmap/validation.json

```

6. Build downstream analysis only through the LLM-native path when a LawPolicy is available.

```bash
${ARCHSIG_BIN:-archsig} law-policy \
  --input <law-policy.json> \
  --out .archsig/law-policy/validation.json

${ARCHSIG_BIN:-archsig} archsig-analysis \
  --archmap .archsig/archmap/archmap.json \
  --law-policy <law-policy.json> \
  --out .archsig/analysis/packet.json \
  --validation-out .archsig/analysis/validation.json

${ARCHSIG_BIN:-archsig} llm-native-workflow \
  --archmap .archsig/archmap/archmap.json \
  --law-policy <law-policy.json> \
  --out-dir .archsig/llm-native
```

7. Read the validation report before handing the artifact downstream.
   - Treat failures as schema or boundary problems to fix.
   - Treat warnings as review cues, not automatic rejection.
   - Check `summary`, `sourceInventoryChecks`, `sourceRefChecks`, `claimBoundaryChecks`, `semanticCoverageChecks`, `formalPromotionGuardrailChecks`, `leanPreservationPreconditionChecklist`, `atomicObservationChecks`, `atomicObservationSummary`, `responsibilityChecks`, and `nonConclusions`.

## Minimal ArchMap Skeleton

Use this only as a starting shape. Replace every placeholder with source-grounded content or remove it.

```json
{
  "schemaVersion": "archmap-observation-map-v0",
  "mapId": "archmap-<scope>",
  "architectureId": "<architecture-id>",
  "generatedAt": "<iso-8601-time>",
  "generator": {
    "kind": "llm-authored",
    "tool": "archsig",
    "provider": "codex",
    "modelId": "<model-or-agent-id>"
  },
  "promptRefs": [
    {"artifactId": "prompt-pack", "kind": "prompt", "path": "tools/archsig/skills/archmap-creater/references/prompt-pack.md"}
  ],
  "sourceInventoryRef": {
    "artifactId": "source-inventory-<scope>",
    "kind": "source_inventory",
    "path": ".archsig/archmap/source-inventory.json"
  },
  "generationBoundary": {
    "tokenBudget": "<budget-or-unknown>",
    "scope": ["<selected-scope>"],
    "excludedRefs": [],
    "privateRefs": [],
    "unavailableRefs": [],
    "nonConclusions": ["generation boundary does not imply complete repository discovery"]
  },
  "sourceUniverse": {
    "root": ".",
    "includedRefs": [],
    "excludedRefs": [],
    "unavailableRefs": [],
    "privateRefs": [],
    "hashes": [],
    "knownBlindSpots": [],
    "selectionBoundary": "<bounded source slice>"
  },
  "provenance": {
    "observer": "codex",
    "observationMethod": "LLM-authored source reading",
    "sourceRoot": ".",
    "observationBoundary": "source-grounded observations only; no law-relative obstruction analysis",
    "reviewedRefs": [],
    "excludedReadings": ["architecture lawfulness", "obstruction circuit", "zero curvature", "forecast correctness"],
    "nonConclusions": ["ArchMap validation is not Lean theorem discharge"]
  },
  "atomObservations": [],
  "moleculeObservations": [],
  "semanticObservations": [],
  "observationGaps": [],
  "projectionInfo": [],
  "concernHints": [],
  "nonConclusions": [
    "ArchMap is bounded observation evidence, not architecture ground truth"
  ]
}
```

## Common Validation Fixes

- Missing source inventory: add `sourceUniverse.includedRefs[]` and `sourceUniverse.selectionBoundary`, or supply a readable `sourceInventoryRef.path`.
- Unresolved source refs: make every observed `sourceRefs[].artifactId` match an entry in `sourceUniverse.includedRefs[]`, unless it is intentionally a boundary ref in gaps or unavailable/private refs.
- Measured-zero mistake: move absent runtime/framework/private evidence into `observationGaps[]` instead of claiming an observed negative fact.
- Responsibility atom mistake: move responsibility from `atomObservations[]` to `moleculeObservations[]`.
- Obstruction mistake: move law violation or obstruction wording out of ArchMap. Keep only source-grounded primitive facts and optional `concernHints[]`.
- Forecast mistake: move ForecastCone, ConsequenceEnvelope, attractor, basin, probability, quality ranking, and incident causality out of ArchMap.

## Writing Rules

- Preserve uncertainty in fields; do not erase it in prose.
- Never claim that `archmap-observation-map-v0` validates architecture lawfulness.
- Never claim that `atomObservations[]` certifies universal `ArchitectureAtom` truth.
- Never put obstruction circuits in ArchMap. Use `concernHints[]` for source-grounded review cues and let ArchSig + LawPolicy construct law-relative obstruction readings.
- Never treat responsibility as a primitive atom; use `moleculeObservations[]`.
- Never claim that validation produces a Lean proof term.
- Never put ForecastCone, ConsequenceEnvelope, attractor, basin, incident causality, or quality ranking into ArchMap as computed results.
- Do not write implementation progress into PRDs. Use issues, theorem indexes, proof obligations, roadmaps, or PRs for status.

## Handoff

Use ArchSig analysis only after a valid ArchMap and a selected LawPolicy exist. Report ArchMap findings as bounded observation evidence until then.

Use FieldSig planning skills after ArchSig has produced `archsig-analysis-packet-v0` and the user asks for planning forecast.
