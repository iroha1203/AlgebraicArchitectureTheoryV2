---
name: archmap-creater
description: Create and validate ArchMap v1 Atom artifacts from repository evidence. Use when Codex is asked to draft, generate, update, or validate an archmap/v1 JSON file, prepare source-grounded atoms and molecules, or run ArchSig v1 analyze from code/docs/tests/traces.
---

# ArchMap Creater

## Purpose

Create `archmap/v1` as source-grounded Atom input for ArchSig.

ArchMap v1 has three primary surfaces:

- `sources`: source ledger for files, symbols, docs, tests, traces, and policy refs that were actually read.
- `atoms`: primitive source-grounded Atom facts from those sources.
- `molecules`: explicit local configurations that group existing atom ids.

ArchMap does not contain obstruction circuits, law violations, signature axes,
distance results, risk findings, projection hints, concern hints, observation
gap ledgers, Lean proof objects, or global architecture truth. ArchSig computes
bounded diagnostics later from `ArchMap + LawPolicy + evaluator registry`.

## Inputs

Collect only evidence the user allows:

- repository root and requested scope
- files, symbols, docs, tests, traces, generated artifacts, or policy docs to read
- source refs that are private, unavailable, or out of scope, kept as authoring notes rather than ArchMap primary fields
- optional LawPolicy path when the user wants an immediate ArchSig run

Before publishing public artifacts, scrub private repository names, private
paths, customer names, internal service names, local smoke paths, and private
artifact ids.

This skill must work with only this skill bundle and a built `archsig`
executable. Do not require the ArchSig source checkout.

## Atom Rules

Write atoms directly. In the ArchSig context these are the atoms.

Allowed atom `kind` values:

- `component`
- `relation`
- `capability`
- `dataState`
- `effect`
- `authority`
- `contract`
- `semantic`
- `runtime`

Each atom must have:

- `id`
- `kind`
- the constructor-specific fields required by the v1 schema
- `refs` resolving to `sources` ids
- optional `label` for human display only

Do not use natural-language-only atoms. `predicate`, `effect`, `authority`,
`contract`, `meaning`, and `interaction` are controlled predicate tokens for
ArchSig normalization, not prose paragraphs. Use `label` for prose display.

Do not write removed v0 fields:

- `atomObservations`
- `moleculeObservations`
- `semanticObservations`
- `projectionInfo`
- `operationSquareEvidence`
- `concernHints`
- `observationGaps`
- `nonConclusions` as a defensive prose ledger

Missing evidence is handled by ArchSig as `blocked`, `unknown`, or
`unmeasured` when a selected evaluator needs support that is not present. Do
not encode missing evidence as measured absence.

## Authoring Workflow

1. Define the source scope.
   - Record read files, symbols, docs, tests, and traces in `sources`.
   - Keep unread/private/unavailable inventory in notes, not ArchMap primary JSON.

2. Extract primitive atoms.
   - Split workflows, responsibilities, and policies into primitive facts.
   - Prefer small atoms with direct source refs.
   - Use `semantic` only for a primitive source-supported meaning, not a whole workflow.

3. Add molecule membership.
   - A molecule is a local configuration of existing atom ids.
   - Do not invent molecule kind enums.
   - Do not create reverse paths, squares, fillers, or risks in ArchMap.

4. Validate.
   - Run `archsig archmap --input <archmap.json> --out <archmap-validation.json>`.
   - Unknown kind, unknown predicate, unresolved source refs, removed v0 fields, and legacy aliases must fail.

5. Run ArchSig when LawPolicy is available.
   - Run `archsig analyze --archmap <archmap.json> --law-policy <law_policy.json> --out-dir <out>`.
   - Use `--strict-distance` when blocked / unknown / unmeasured distance must fail the run.
   - Use `--emit-raw-artifacts` when packet / detail-index / LLM handoff artifacts are needed.

## Commands

Use this command form:

```bash
${ARCHSIG_BIN:-archsig} archmap \
  --input <archmap.json> \
  --out <archmap-validation.json>

${ARCHSIG_BIN:-archsig} analyze \
  --archmap <archmap.json> \
  --law-policy <law_policy.json> \
  --out-dir <out-dir>
```

If no binary exists, report that validation was not performed. Do not replace
ArchSig validation with an ad hoc checker.

## Output Shape

When delivering an ArchMap, include:

1. ArchMap path
2. source scope summary
3. atoms grouped by kind
4. molecule membership summary
5. explicit notes for private / unavailable / out-of-scope evidence outside the primary JSON
6. validation result
7. optional analyze output directory and verdict

Use concise Japanese when working in this repository.

## References

- `references/schema-cheatsheet.md`: v1 schema shape
- `references/mapping-guide.md`: source cue to atom mapping
- `references/examples.md`: v1 examples
- `references/repository-survey.md`: survey protocol
- `references/prompt-pack.md`: prompt template
