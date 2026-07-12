# Coverage And Consistency

This reference defines the two authoring artifacts that make survey coverage
and pass differences auditable without turning them into semantic verdicts.

## Extraction Consistency

`archmap-extraction-consistency/v0.5.1` is produced by `archsig extraction-diff`.
The command compares candidate packets by atom-match-key and leaves semantic
adjudication to the integrator. The integrator completes adjudication by
rereading sources.

Required shape:

```json
{
  "schema": "archmap-extraction-consistency/v0.5.1",
  "id": "consistency:orders-service",
  "scopeManifestRef": "scope:orders-service",
  "passARefs": ["candidates:pass-a:chunk-01"],
  "passBRefs": ["candidates:pass-b:chunk-01"],
  "atomMatchKeySpec": "kind | NFC(trim(subject)) | axis | predicate? | object?",
  "matched": {
    "count": 12,
    "rows": [
      {
        "key": "semantic|orders.Handler|semantic|uses|cancel path",
        "passAAtomIds": ["atom:pass-a:cancel-path"],
        "passBAtomIds": ["atom:pass-b:cancel-path"],
        "refs": ["src:src/orders/handler.rs", "src:src/orders/handler.rs:42"]
      }
    ]
  },
  "onlyInPassA": [],
  "onlyInPassB": [],
  "matchRate": 1.0,
  "contextDiff": { "matched": 2, "onlyInPassA": [], "onlyInPassB": [] },
  "adjudications": []
}
```

`adjudications` is empty in the mechanical output. The integrator appends
entries after source rereading:

```json
{
  "key": "capability|orders.Handler|static|handlesCommand|CancelOrder",
  "decision": "adopted",
  "basis": "re-read src:src/orders/handler.rs; cancel path is present"
}
```

Allowed decisions are:

- `adopted`
- `merged`
- `not-adopted`

Do not add a generated adoption decision during `extraction-diff`.

## Match Rate

`matchRate = matched / (matched + |onlyInPassA| + |onlyInPassB|)`.

The value is a record, not a pass/fail verdict. There is no configured cutoff
and no branch in the authoring workflow may use a cutoff to skip adjudication.

## Context Difference

Context match keys are built from sorted member atom keys and sorted
`restrictsTo` target keys. A context-only difference records a different local
cut of the same source evidence. The integrator rereads the relevant source and
decides whether to adopt, merge, or reject the cut.

## Coverage Ledger

`archmap-coverage-ledger/v0.5.1` records the selected-scope survey. Rows must be
one-to-one with the scope manifest worklist.

Required shape:

```json
{
  "schema": "archmap-coverage-ledger/v0.5.1",
  "id": "coverage:orders-service",
  "scopeManifestRef": "scope:orders-service",
  "archmapRef": "archmap:orders-service",
  "passRefs": ["pass-a", "pass-b"],
  "rows": [
    {
      "sourceId": "src:src/orders/handler.rs",
      "surveyStatus": "surveyed",
      "passes": ["pass-a", "pass-b"],
      "surveyedKinds": ["component", "capability", "authority", "semantic"],
      "adoptedAtomIds": ["atom:capability:orders.Handler:handlesCommand:PlaceOrder"]
    }
  ],
  "claimBoundary": "Rows record the authoring survey of the selected scope at the recorded revision. They do not assert extraction completeness."
}
```

Allowed `surveyStatus` values:

- `surveyed`
- `partially_surveyed`
- `not_surveyed`

Allowed procedural reasons for `partially_surveyed` and `not_surveyed`:

- `private`
- `binary`
- `unreadable`
- `tooling-error`

`out-of-scope` is not a ledger reason because ledger rows span only the approved
worklist. Scope exclusions stay in the scope manifest.

## Authoring Checks

When authoring artifact flags are implemented and passed to `archsig archmap`,
the validation layer checks:

- `authoring-sources-resolve`
- `authoring-provenance-closure`
- `authoring-ledger-spans-worklist`
- `authoring-read-before-cite`
- `authoring-revision-recorded`

All passing checks produce the leading conclusion
`AUTHORING_SURVEY_TRACEABLE_WITHIN_SCOPE`.

When a check fails, fix the authoring artifact or its scope evidence and rerun
the CLI; do not report the traceability conclusion until the required checks
pass.
