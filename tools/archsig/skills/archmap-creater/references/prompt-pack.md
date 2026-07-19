# Prompt Pack

Use this prompt shape for each reading-pass chunk.

## System Task

Read the assigned worklist rows and emit one
`archmap-candidate-packet/v0.5.4`. You are not producing the final ArchMap. You are
not allowed to use generated inventories as final atoms. Every candidate must
be source-grounded.

## Inputs To The Reader

- `scopeManifestRef`
- pass id: `pass-a` or `pass-b`
- deterministic chunk range
- assigned worklist rows
- `schema-cheatsheet.md`
- `mapping-guide.md`
- `vocabulary-catalog.md`

Do not read the other pass's candidate packets.

## Required Output Shape

```json
{
  "schema": "archmap-candidate-packet/v0.5.4",
  "id": "candidates:pass-a:chunk-01",
  "scopeManifestRef": "scope:orders-service",
  "passId": "pass-a",
  "chunk": { "worklistOrderFrom": 1, "worklistOrderTo": 20 },
  "reviewedSources": [],
  "candidateSources": {},
  "candidateAtoms": [],
  "candidateContexts": [],
  "candidateCovers": [],
  "surveyRows": [
    {
      "sourceId": "src:path/from-worklist",
      "status": "skipped",
      "reason": "unreadable",
      "surveyedKinds": [],
      "candidateAtomIds": [],
      "notes": []
    }
  ],
  "privateUnavailableNotes": [],
  "selfReview": {
    "notScriptGenerated": false,
    "notCoarseWhenEvidenceWasRicher": false,
    "semanticAtomsHaveUseEvidence": false,
    "noDiagnosticShortcutAtoms": false,
    "worklistChunkFullyRead": false,
    "aliasPreservingSemantics": false
  }
}
```

Set a self-review field to `true` only when it is actually satisfied.
The candidate-packet validator treats any false self-review field as not ready.

## Candidate Rules

- Add one `surveyRows` entry for every assigned worklist row.
- Use `status: "read"` when the source was read enough for the surveyed kinds.
- Use `status: "partial"` or `status: "skipped"` only with procedural reasons:
  `private`, `binary`, `unreadable`, or `tooling-error`.
- Do not use `out-of-scope` as a pass-time reason. Report scope mismatch to the
  integrator for a round trip.
- Survey every file for semantic use evidence, even when no semantic atom is
  emitted.
- Semantic candidate atoms must include `object`.
- Do not emit diagnostic-shaped ids or predicates.
- Do not merge different semantic uses of the same subject.
- Keep notes sanitized. Do not include local absolute paths, personal names,
  nonpublic labels, secrets, or machine-specific identifiers.

## Self Review Gate

- `notScriptGenerated`: candidate atoms were written from source reading, not
  generated from an index or script.
- `notCoarseWhenEvidenceWasRicher`: source evidence was not collapsed to a
  coarse component or relation when capabilities, state, effects, authority,
  contracts, runtime, or semantic use were present.
- `semanticAtomsHaveUseEvidence`: every semantic atom cites observed use.
- `noDiagnosticShortcutAtoms`: ids and predicates do not pre-author diagnostic
  conclusions.
- `worklistChunkFullyRead`: every assigned worklist row has a survey row.
- `aliasPreservingSemantics`: different observed semantic uses remain separate.

## Neutral Phrasing For Outcome Semantics

Ids, predicates, and objects must not contain the diagnostic conclusion tokens
`failure`, `violation`, `obstruction`, or `mismatch`. This bites most often on
response-envelope observations (a status/result flag whose values select
branches). Describe what each observed value *selects*, not a verdict word.

Bad (rejected by the candidate-packet validator):

```json
{
  "id": "atom:semantic:common.Response.status:meansInUse:one-success-zero-failure",
  "object": "status-1-success-status-0-failure"
}
```

Good (same observation, branch-descriptive):

```json
{
  "id": "atom:semantic:common.Response.status:meansInUse:one-data-branch-zero-message-branch",
  "object": "status-1-on-result-carrying-branch-status-0-on-not-found-or-rejected-branch"
}
```

The same rule applies to survey-row notes: name the branch condition the code
takes ("the branch taken when a payment already exists"), not "the failure
branch".

## Subject Normal Form

Independent passes drift most heavily on subject spelling (FQCN vs shortened
package vs service-dir form), which alone can account for ~90% of mechanical
mismatches. Write every atom subject as:

```
<source-dir>.<ClassName>
```

where `<source-dir>` is the first path component of the source file
(e.g. `ts-cancel-service.CancelServiceImpl`, `ts-common.OrderStatus`).
Configuration files use `<source-dir>.application-yml`. Do not put Java
package segments into the subject.

Bad: `cancel.service.CancelServiceImpl`, `edu.fudan.common.entity.OrderStatus`
Good: `ts-cancel-service.CancelServiceImpl`, `ts-common.OrderStatus`

The mechanical differ additionally normalizes identifier subjects to this form
(atom-match-key@2), but write the normal form directly so ids, contexts, and
human review converge too.

## Default Granularity

The same evidence read at different granularities produces unmatched
candidates that adjudication must reconcile. Use these defaults (they are
convergence points, not prohibitions — a reading that genuinely differs may
still be emitted and will be adjudicated):

- HTTP endpoint capability: **one atom per endpoint (verb + path)**. Do not
  bundle multiple verbs or endpoints into one atom.
- Cross-service call effect: **one atom per provider**. Do not bundle
  alternative providers ("A or B") into one atom; a branch-selected provider
  pair is two atoms (plus the branch condition as its own observation).
- Capability subject: the **implementing class** (behavioral evidence). The
  declaring interface is a separate `contract` observation, not the capability
  subject.
- Repository persistence: **one aggregate `state`/`persistsIn` atom per
  repository** by default; add per-method atoms only when a method carries
  behavior of its own worth citing.
- Two-valued response envelope semantics (status 0/1 and similar): **one
  semantic atom whose object describes both branches**, not one atom per value.
- One atom per evidence site: do not combine facts observed in **different
  methods** into one atom, and do not split a **single construct** (one
  try/catch, one if/else, one computation) into several atoms unless the parts
  genuinely carry different predicates.
- Relation predicate lens: use `calls` when an **invocation site** is observed;
  use `dependsOn` only for declaration-only dependencies (import, injected
  field, extends/implements) with no observed invocation in the read scope.
- Capability predicate lens for service methods: `servesQuery` when the
  observed body only reads, `handlesCommand` when it mutates state or triggers
  a mutating downstream call — decide from the observed body, not the name.
  Emit one capability atom per public service method whose body you read
  (do not skip the capability layer for a class you surveyed).

## Structured Object Notation

For recurring observation shapes, use these object forms so identical facts
produce identical keys (free prose stays allowed for genuinely novel
observations — the narration is free, the key converges):

- endpoint route: `GET /api/v1/cancelservice/cancel/{orderId}/{loginId}`
- response envelope: `status-1-on-<selected-branch>-status-0-on-<selected-branch>`
- code vocabulary: `int-codes-0-notpaid-1-paid-2-collected-...` (list every
  observed code in ascending order)
- money/amount representation, one label per convention:
  `string-passthrough-unparsed`, `string-parsed-to-double-arithmetic-decimalformat`,
  `string-parsed-to-bigdecimal-at-use-site`, `string-parsed-to-float-at-use-site`,
  `double-primitive-fields`, `double-arithmetic-then-string-concatenation`,
  `double-parsed-from-text-at-init-seed`, `price-from-string-keyed-map-lookup-unparsed`
- authority path rule: `<verb-or-all> <path-pattern> <rule>` (e.g.
  `POST /api/v1/seatservice/seats requiresRole-ADMIN`,
  `ALL /api/v1/basicservice/** permitsUnauthenticated`)
- service-method capability (`handlesCommand` / `servesQuery`): object is the
  **verbatim method name plus `/` plus parameter count**, nothing else (e.g.
  `cancelOrder/2`, `queryForStationId/2`). No prose, no route, no description —
  the route belongs to the endpoint atom, the behavior to semantic atoms.
- cross-service call effect (`callsProvider`): object is
  `<verb> <target-service> <route>` (e.g.
  `GET ts-order-service /api/v1/orderservice/order/{id}`).
- repository persistence (`persistsIn`): object is the verbatim entity class
  name (e.g. `Order`).

## Default Axis Selection

Independent passes drift most on `axis`, which breaks `atom-match-key@1`
matching for otherwise identical observations. Unless a specific evidence axis
(`cech`, `runtime`, and the other AG-consumed axes) applies, default to:

| kind | default axis |
| --- | --- |
| `component` | `static` |
| `relation` | `relation` |
| `capability` | `capability` |
| `effect` | `effect` |
| `authority` | `authority` |
| `semantic` | `semantic` |
| `contract` | `specification` |
| `state` | `state` |

Use `restriction` only for evidence of a context restriction direction, not for
ordinary `calls` / `dependsOn` / `writesTo` edges. These defaults are a
convergence point for new authoring passes; they do not retroactively rewrite
existing ArchMap artifacts.

## Reader Notes

Unmatched candidates are useful. The integrator will compare passes and reread
sources. Do not adjust your output to match another pass.
