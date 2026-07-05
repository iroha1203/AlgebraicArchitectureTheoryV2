# Examples

Use `tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json` as the current
minimal executable example for ArchMap v2 validation.

## Alias Preservation

Good: the same subject has two observed meanings and therefore two semantic
atoms.

```json
[
  {
    "id": "atom:semantic:orders.Status:statusGates:cancelable",
    "kind": "semantic",
    "subject": "orders.Status",
    "axis": "semantic",
    "predicate": "statusGates",
    "object": "cancelable-transition",
    "refs": ["src:src/orders/domain.rs"]
  },
  {
    "id": "atom:semantic:orders.Status:statusGates:billable",
    "kind": "semantic",
    "subject": "orders.Status",
    "axis": "semantic",
    "predicate": "statusGates",
    "object": "billable-invoice-transition",
    "refs": ["src:src/billing/policy.rs"]
  }
]
```

Bad: merging both observations into one generic semantic atom for
`orders.Status`. This erases the alias evidence that PRD-4 `aliasWitnesses`
measure on the ArchSig side.

## Coverage Ledger

Good: one row for each worklist source.

```json
{
  "sourceId": "src:src/orders/handler.rs",
  "surveyStatus": "surveyed",
  "passes": ["pass-a", "pass-b"],
  "surveyedKinds": ["component", "capability", "authority", "semantic"],
  "adoptedAtomIds": [
    "atom:capability:orders.Handler:handlesCommand:PlaceOrder"
  ]
}
```

Bad: adding a ledger row for a source that is not in the manifest worklist, or
using `out-of-scope` as a ledger reason. Scope exclusions belong to the scope
manifest.

## Chunk Boundary

Good: Pass A reads `handler.rs` in chunk 01 and `repository.rs` in chunk 02. The
integrator sees that both describe the same local operation and creates one
context after rereading the boundary.

Bad: each chunk emits a separate final context and the integrator keeps both
without checking the shared transaction or adapter boundary. That duplicates
the measurement surface and can produce a poor cover.

## Cover Cut

Good: a Cech cover contains two local contexts and a shared boundary context,
with `restrictsTo` edges from each local context into the shared context.

Bad: a cover contains unrelated contexts with no shared atom, shared boundary,
or restriction convergence. That cut usually degenerates for Cech-style
measurement.
