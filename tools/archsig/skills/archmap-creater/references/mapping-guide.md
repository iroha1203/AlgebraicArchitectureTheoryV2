# ArchMap v1 Mapping Guide

ArchMap v1 records source-grounded atoms and explicit molecule membership.
ArchSig computes normalized predicates, evaluator results, distance diagnosis,
and bounded conclusions later.

## Source Cue To Atom

| Source cue | Atom kind | Payload |
| --- | --- | --- |
| file, module, class, service, package exists | `component` | `subject` |
| call/import/dependency/ownership edge | `relation` | `subject`, `predicate`, `object` |
| command, query, handler, port, adapter surface | `capability` | `subject`, `predicate` |
| persisted state, table, field, cache, lifecycle state | `dataState` | `diagram`, `state` |
| write, publish, enqueue, provider call, file mutation | `effect` | `diagram`, `effect` |
| role gate, permission check, owner scope, visibility rule | `authority` | `subject`, `authority` |
| precondition, postcondition, DTO shape, invariant, retry rule | `contract` | `diagram`, `contract` |
| domain meaning, identity meaning, unit/status meaning | `semantic` | `diagram`, `meaning` |
| supplied trace/log/runtime edge | `runtime` | `edge`, `interaction` |

## Boundary Rules

- Static indexes and search results are navigation aids, not atoms.
- Framework conventions become atoms only when the expanded source or generated artifact was inspected.
- Workflows are discovered by reading source, then split into primitive atoms.
- Responsibilities are molecules over atoms, not primitive atoms.
- Policy/lawfulness is not written into ArchMap.
- Missing evidence is not written as measured absence.

## Molecule Rules

Create a molecule when the source shows a local configuration:

- service method local flow
- route / handler / service / repository interaction
- provider mediation sequence
- transaction boundary sequence
- authority + state + effect local operation

The molecule contains atom ids only. It does not assert a square, filler,
obstruction, homotopy, distance, risk, or repair.
