# Vocabulary Catalog

This catalog is a recommended token table inside
`doctrine:aat-canonical@1`. It is not a closed enum for predicates. Its purpose
is to keep repeated observations written with stable tokens while preserving
author judgment about whether a token applies.

The machine-readable AG binding pairs used by the law-equation-surface validator
are fixed in `aat-law-surface-binding-vocabulary.json` in this directory. The
ArchMap vocabulary reader and validator use that same `aat-atom-vocabulary`
binding manifest; update the manifest and authoring guidance in one change when
an accepted AG axis/predicate pair changes.

The manifest is the accepted Stage 2 law-surface subset. The broader AG table
below also records evaluator-specific and later-stage vocabulary for authoring
reference; those entries are not accepted as law-surface/v0.5.1 bindings.

New axis names are not introduced inside an authoring run. If the current axis
table is insufficient, escalate to doctrine or registry work.

## Kind Table

ArchMap v2 atom kinds:

| kind | Use |
| --- | --- |
| `component` | file, module, service, package, class, process |
| `relation` | call, import, dependency, ownership, implementation edge |
| `capability` | command, query, handler, adapter surface, endpoint |
| `state` | table, field, cache, lifecycle state, persistence |
| `effect` | write, publish, enqueue, provider call, file mutation |
| `authority` | role gate, permission check, owner scope, visibility rule |
| `contract` | precondition, postcondition, invariant, DTO shape, retry rule |
| `semantic` | observed use meaning of a term, status, value, or boundary |
| `runtime` | supplied trace, log, latency, runtime edge |

## Axis Table

| axis | Role | AG consumed |
| --- | --- | --- |
| `cech` | Cech section evidence | yes |
| `square-free` | square-free repair raw support | yes |
| `section-factorization` | selected section factorization | yes |
| `tor` | Taylor Tor proxy evidence | yes |
| `transfer` | support transfer model evidence | yes |
| `period` | period integral evidence | yes |
| `laplacian` | cellular Laplacian evidence | yes |
| `witness` | descriptive witness note | no |
| `boundary-residue` | boundary residue repair evidence | yes |
| `restriction-compatibility` | finite support restriction evidence | yes |
| `coherence` | coherence evaluator evidence | yes |
| `refactor` | refactor evaluator evidence | yes |
| `static` | descriptive source structure | no |
| `restriction` | descriptive restriction relation | no |
| `relation` | descriptive relation mirror | no |
| `capability` | descriptive capability mirror | no |
| `effect` | descriptive effect mirror | no |
| `authority` | descriptive authority mirror | no |
| `semantic` | descriptive semantic mirror | no |
| `specification` | descriptive specification evidence | no |
| `existence` | descriptive existence evidence | no |
| `boundary` | descriptive boundary evidence | no |

`support` is not an axis. It is a raw predicate used with AG-consumed axes such
as `square-free` and `section-factorization`.

## Predicate Table

| kind | Recommended predicates |
| --- | --- |
| `relation` | `dependsOn`, `calls`, `implements`, `publishesTo`, `readsFrom`, `writesTo` |
| `capability` | `handlesCommand`, `servesQuery`, `exposesEndpoint` |
| `authority` | `requiresRole`, `checksPermission`, `scopesToOwner` |
| `state` | `persistsIn`, `transitionsTo`, `cachedIn` |
| `effect` | `enqueues`, `publishes`, `mutatesFile`, `callsProvider` |
| `contract` | `requires`, `ensures`, `shapedAs`, `retriesWith` |
| `semantic` | `meansInUse`, `identifiedBy`, `statusGates` |
| `runtime` | `observedCall`, `observedLatency` |

Catalog-external predicate use is an integrator adjudication: record why no
listed predicate fit the observed source use. This is not an axis extension.

## AG Axis Predicate Pairs

| axis | predicates consumed by AG paths |
| --- | --- |
| `cech` | `sectionValue`, `cocycleValue` |
| `square-free` | `support`, `cooccurrence` |
| `section-factorization` | `support`, `cooccurrence`, `witnessAssignment` |
| `laplacian` | `cellularCochain`, `cellularBoundary` |
| `period` | `periodIntegral` |
| `transfer` | `transferPairing`, `repairPath`, `groundCost` |
| `tor` | `commonAmbient`, `lawIdealGenerator` |
| `boundary-residue` | `restrictionColumn`, `boundarySection`, `patchRole`, `patchClassification` |
| `restriction-compatibility` | `restrictionIdealGenerator` |
| `coherence` | evaluator-specific coherence predicates |
| `refactor` | evaluator-specific refactor predicates |

## Semantic Object Rule

Semantic atoms must carry `object`. The `object` value identifies the observed
use meaning. This keeps different aliases for the same subject visible to
`atom-match-key@1`.

Good:

```json
{
  "id": "atom:semantic:orders.Status:statusGates:cancelable",
  "kind": "semantic",
  "subject": "orders.Status",
  "axis": "semantic",
  "predicate": "statusGates",
  "object": "cancelable-order-transition",
  "refs": ["src:src/orders/domain.rs"]
}
```

Bad: a semantic atom with no `object`.

## Naming

- Subject: `<domain-or-module>.<Symbol>`.
- Atom id: `atom:<kind>:<slug(subject)>[:<slug(predicate-or-object)>]`.
- Source id: file evidence uses `src:<repo-relative-path>`.

## Atom Match Key

`atom-match-key@1 = kind | NFC(trim(subject)) | axis | predicate? | object?`.

The key excludes `id` and `refs`. Refs may vary between passes and are unioned
only after integrator confirmation. For semantic atoms, `object` is required so
meaning differences are key-bearing.
