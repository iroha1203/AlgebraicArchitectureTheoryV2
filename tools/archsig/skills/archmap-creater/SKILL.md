---
name: archmap-creater
description: Create and validate ArchMap artifacts from repository evidence, especially AG measurement archmap/v0.5.0 finite-poset-site JSON. Use when Codex is asked to draft, generate, update, or validate an ArchMap, prepare source-grounded atoms, contexts, covers, or run ArchSig analyze from code/docs/tests/traces.
---

# ArchMap Creater

## Purpose

Create `archmap/v0.5.0` as the source-grounded finite-poset-site input for
ArchSig AG measurement.

ArchMap v2 has five primary surfaces:

- `schema`: exactly `archmap/v0.5.0`.
- `sources`: source ledger for files, symbols, docs, tests, traces, and policy
  refs that were actually read.
- `atoms`: subject / axis-decorated primitive source-grounded Atom facts.
- `contexts`: finite poset contexts, each with explicit atom membership and
  optional `restrictsTo` edges.
- `covers`: finite context families selected as cover candidates.

The extraction doctrine is fixed by ArchSig as `doctrine:aat-canonical@1`.
ArchMap authors do not choose, fingerprint, or extend a doctrine in the v2
artifact.

ArchMap does not contain obstruction circuits, law violations, signature axes,
distance results, risk findings, projection hints, concern hints, observation
gap ledgers, Lean proof objects, or global architecture truth. ArchSig computes
bounded diagnostics later from `ArchMap + LawPolicy + MeasurementProfile +
evaluator registry`.

Use `archmap/v0.5.0` only when the user explicitly targets the bounded legacy
structural-analysis path. Do not migrate v2 contexts back into v1 molecules for
AG measurement work.

## Non-Negotiable Authoring Discipline

Author ArchMap by reading and interpreting source evidence, not by generating a
static-analysis dump.

- Do not create final atoms with a repository-wide script, AST walker, import
  graph dump, filename template, or "minimal JSON" boilerplate. Scripts may help
  list candidate files or run validation, but the accepted atoms / contexts /
  covers must come from manual source reading and semantic integration.
- Do not stop at a minimal component/relation inventory when the requested scope
  exposes capabilities, states, effects, authority, contracts, runtime traces,
  or domain semantics. A component-only ArchMap is a draft unless the source
  scope truly contains only component existence evidence.
- Do not use ArchMap to smuggle evaluator outcomes. Diagnostic-shaped tokens
  such as `mismatch`, `obstruction`, `violation`, `risk`, `debt`, `unsafe`,
  `lawful`, `nonzero`, or `failure` are forbidden in authored atom ids and
  predicates. Record neutral observed source relations and let ArchSig derive
  diagnostic readings later.
- Before delivery, run the self-review gate in `references/prompt-pack.md`.
  If any gate fails, revise the ArchMap instead of explaining the failure away.

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
- `state`
- `effect`
- `authority`
- `contract`
- `semantic`
- `runtime`

Each v2 atom must have:

- `id`
- `kind`
- `subject`
- `axis`
- `refs` resolving to `sources` ids
- optional `predicate`
- optional `object`
- optional `label` for human display only

Do not use natural-language-only atoms. `predicate`, `effect`, `authority`,
`contract`, `meaning`, and `interaction` are controlled predicate tokens for
ArchSig normalization, not prose paragraphs. Use `label` for prose display.

Semantic atoms require use-evidence. A `semantic` atom is valid only when it
captures how a symbol / value / boundary is used in the repository: name the
subject, choose a predicate token from observed usage, and cite the files,
tests, docs, or traces where that use is enacted. Do not write dictionary
glosses, vibes, design praise, or policy conclusions as `semantic`.

Do not write removed v0 fields:

- `atomObservations`
- `moleculeObservations`
- `semanticObservations`
- `projectionInfo`
- `operationSquareEvidence`
- `concernHints`
- `observationGaps`
- `nonConclusions` as a defensive prose ledger
- `molecules` for AG measurement v2 primary input

Missing evidence is handled by ArchSig as `blocked`, `unknown`, or
`unmeasured` when a selected evaluator needs support that is not present. Do
not encode missing evidence as measured absence.

## Context And Cover Rules

Contexts and covers are source-grounded observation structure.

- A `context` has `id`, non-empty `atoms`, optional `restrictsTo`, `refs`, and
  optional `label`.
- `restrictsTo` edges must resolve to context ids, be irreflexive, and form an
  acyclic finite poset.
- A `cover` has `id`, non-empty `contexts`, `refs`, and optional `label`.
- Contexts / covers do not declare coefficients, witness variables, verdict
  predicates, U-adequacy, exactness, Leray assumptions, or repair semantics.
  Those belong to `MeasurementProfile` and the assumption ledger.

## Authoring Workflow

1. Define the source scope.
   - Record read files, symbols, docs, tests, and traces in `sources`.
   - Keep unread/private/unavailable inventory in notes, not ArchMap primary JSON.

2. Extract primitive atoms.
   - Split workflows, responsibilities, and policies into primitive facts.
   - Prefer small atoms with direct source refs.
   - Cover all observed atom kinds relevant to the scope; do not collapse
     capability, state, effect, authority, contract, runtime, and semantic
     evidence into coarse component / relation atoms.
   - Use `semantic` only for a primitive source-supported meaning, not a whole
     workflow. Extract it from use: how the term participates in commands,
     tests, invariants, docs, status transitions, permissions, or runtime
     traces.

3. Add contexts and covers.
   - Contexts are finite atom subfamilies with source refs.
   - Use `restrictsTo` only for observed restriction direction.
   - Covers are selected finite context families grounded in source refs.
   - Do not create squares, fillers, obstruction classes, repairs, or risks in
     ArchMap.

4. Validate.
   - Run `archsig archmap --input <archmap.json> --out <archmap-validation.json>`.
   - Unknown kind, unresolved source refs, invalid context / cover refs,
     removed v0 fields, and legacy aliases must fail.
   - Predicate tokens are still an authoring discipline: prefer evaluator-known
     tokens from fixtures or policy docs, but do not claim validation rejects
     every unknown predicate unless the current tool report says so.

5. Run ArchSig when LawPolicy is available.
   - Run `archsig analyze --archmap <archmap.json> --law-policy <law_policy.json> --out-dir <out>`.
   - For AG evaluators, LawPolicy must include `measurementProfileRef` and a
     matching `measurementProfiles[]` entry.
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
4. contexts and cover summary
5. explicit notes for private / unavailable / out-of-scope evidence outside the primary JSON
6. validation result
7. optional analyze output directory and verdict

Use concise Japanese when working in this repository.

## References

- `references/schema-cheatsheet.md`: v2 schema shape
- `references/mapping-guide.md`: source cue to atom mapping
- `references/examples.md`: v2 examples
- `references/repository-survey.md`: survey protocol
- `references/prompt-pack.md`: prompt template
