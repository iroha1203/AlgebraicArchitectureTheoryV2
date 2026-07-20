# ArchMap Reading-Pass Instructions (train-ticket fullbuild, Issue #3545)

You are one independent reading pass over an assigned chunk of a scope-manifest
worklist. You emit ONE `archmap-candidate-packet/v0.5.4` JSON file. You are not
producing the final ArchMap. Every candidate must be source-grounded: written
from your own reading of the assigned files, never generated from an index,
script, or file-name pattern.

## Fixed paths

- Repo root (target codebase):
  `<WORKDIR>/train-ticket`
- Chunk assignments (`chunks.json`, your chunkId is given in your task prompt):
  `(file list is inline in your task prompt)`
- Reference docs you MUST read before reading sources:
  - `<REPO>/tools/archsig/skills/archmap-creater/references/schema-cheatsheet.md`
  - `<REPO>/tools/archsig/skills/archmap-creater/references/vocabulary-catalog.md`
  - `<REPO>/tools/archsig/skills/archmap-creater/references/mapping-guide.md`

Do not read any other pass's candidate packets. Do not read files under
`fullbuild/candidates/`.

## Output

Write exactly one JSON file at the output path given in your task prompt, shaped:

```json
{
  "schema": "archmap-candidate-packet/v0.5.4",
  "id": "candidates:<passId>:<chunkId>",
  "scopeManifestRef": "scope:train-ticket-supply-bench@1",
  "passId": "<passId>",
  "chunk": { "worklistOrderFrom": <N>, "worklistOrderTo": <M> },
  "reviewedSources": ["src:<repo-relative-path>", ...],
  "candidateSources": { "src:<repo-relative-path>": { "kind": "file", "path": "<repo-relative-path>" }, ... },
  "candidateAtoms": [ ... ],
  "candidateContexts": [ ... ],
  "candidateCovers": [ ... ],
  "surveyRows": [ ... one entry per assigned worklist row, same order ... ],
  "privateUnavailableNotes": [],
  "selfReview": {
    "notScriptGenerated": true|false,
    "notCoarseWhenEvidenceWasRicher": true|false,
    "semanticAtomsHaveUseEvidence": true|false,
    "noDiagnosticShortcutAtoms": true|false,
    "worklistChunkFullyRead": true|false,
    "aliasPreservingSemantics": true|false
  }
}
```

Set a selfReview field to true only when actually satisfied.

## Survey surface (check every file for all of these)

components and public entrypoints; relations and dependency boundaries;
capabilities (commands/queries/endpoints); state, persistence, lifecycle,
cache; effects (jobs, queues, providers called over HTTP/RPC, file mutations);
authority (access control, permitAll, CORS, ownership, header forwarding);
contracts (preconditions, postconditions, DTO shape, invariants, retry rules);
semantic use evidence (what an observed value/flag/code MEANS in use at this
site); context boundaries and restriction directions; finite cover candidates.

Known repeated gaps — do not repeat them: per-file semantic survey skipped;
authority/permission evidence not read (SecurityConfig files carry authority
atoms: permitsAll / permitsWithoutAuthentication / allowsCrossOrigin are valid
catalog predicates); response-envelope semantics skipped.

## Atom rules

- Atom shape: `{id, kind, subject, axis, predicate?, object?, refs[]}`.
  ids lowercase kebab, `atom:<kind>:<subject-slug>[:<predicate-slug>]`.
- Default axis by kind (use unless a specific evidence axis applies):
  component→static, relation→relation, capability→capability, effect→effect,
  authority→authority, semantic→semantic, contract→specification, state→state.
  Use `restriction` only for context restriction direction evidence, not for
  ordinary calls/dependsOn/writesTo.
- Semantic atoms REQUIRE `object` carrying the observed meaning, and use
  evidence in refs. Different observed uses of the same subject stay separate
  atoms (alias-preserving); carry the difference in `object`.
- refs are repo-relative `src:<path>` and may carry `:<line>` samples.
- NEUTRAL PHRASING: ids, predicates, objects must not contain the tokens
  `failure`, `violation`, `obstruction`, or `mismatch`. For status/result
  flags describe what each value SELECTS (branch-descriptive), e.g.
  `status-1-on-result-carrying-branch-status-0-on-not-found-or-rejected-branch`.
  Same rule for notes: name the branch condition, not a verdict word.
- No diagnostic-shaped ids/predicates (nothing that pre-authors a conclusion).

## Shared-convention observations (cech sectionValue candidates)

This build measures cross-service drift of shared conventions. While reading,
record as ordinary semantic atoms every concrete observation of these shared
quantities (with file:line refs and branch-descriptive objects):

- money/amount representation: Java type (String / BigDecimal / double), where
  parsing/arithmetic happens, rounding or scaling conventions
- order-status code vocabulary: numeric literals or enum names used to gate or
  set order state (e.g. hardcoded 0/1/4/5/6/7), which codes appear at this site
- response envelope: what status codes select which branches
- id/lookup contract: how orders/accounts are looked up (by id, by field), and
  date/time formats crossing service boundaries

ADDITIONALLY, when your chunk's files let you observe how one of your
candidateContexts represents such a shared quantity, emit a candidate cech atom:

```json
{
  "id": "atom:semantic:<ctx-slug>:cech-section-<quantity>",
  "kind": "semantic",
  "subject": "<one of YOUR candidateContexts ids>",
  "axis": "cech",
  "predicate": "sectionValue",
  "object": "section=<quantity>:<short-neutral-value-label>",
  "refs": ["src:<path>:<line>", ...]
}
```

`<quantity>` is one of: `money-amount`, `order-status-code` (use these exact
names when applicable so passes converge). The value label describes the
convention as observed (e.g. `string-price-parsed-to-double-at-use-site`,
`int-codes-0-not-paid-1-paid-4-cancel-hardcoded`). Only emit sectionValue when
you actually observed the convention in the assigned sources.

## candidateContexts / candidateCovers

Propose contexts for coherent behavioral surfaces you actually observed
(flows, boundaries, lifecycles) with `{id, label, atoms, refs, restrictsTo}`;
propose covers `{id, label, contexts, refs}` when your chunk shows a
measurement surface spanning several contexts. It is fine if your contexts are
local to your chunk; the integrator merges across chunks. Use
`ctx:<service-or-boundary>-<surface>` naming.

## surveyRows

One entry per assigned worklist row, same order:
`{sourceId, status, surveyedKinds, candidateAtomIds, notes}`.
status `read` normally; `partial`/`skipped` only with procedural reasons
(`private`, `binary`, `unreadable`, `tooling-error`). NEVER use out-of-scope as
a skip reason — if a file looks out of scope, note it for the integrator in
`privateUnavailableNotes` and still survey what is readable.
Notes must be sanitized: no absolute paths, no personal names, no secrets.

## Reporting back

Your final reply must be SHORT (no atom listings): output file path, counts
(atoms by kind, contexts, covers, sectionValue atoms), rows read/partial/skipped,
and at most 3 one-line observations useful to the integrator.

## v2 convergence rules (MANDATORY, added after the fullbuild run)

Also read, BEFORE reading sources:
`<REPO>/tools/archsig/skills/archmap-creater/references/prompt-pack.md`
and apply its Subject Normal Form (`<source-dir>.<ClassName>`), Default
Granularity table, Structured Object Notation templates, and Default Axis
Selection exactly. These are convergence defaults: a reading that genuinely
differs may still be emitted.
