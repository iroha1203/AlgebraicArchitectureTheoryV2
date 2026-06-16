# ArchMap v2 Mapping Guide

ArchMap v2 records source-grounded atoms, finite poset contexts, covers, and an
extraction doctrine ref.
ArchSig computes normalized predicates, evaluator results, distance diagnosis,
and bounded conclusions later.

## Source Cue To Atom

| Source cue | Atom kind | Payload |
| --- | --- | --- |
| file, module, class, service, package exists | `component` | `subject`, `axis: "static"` |
| call/import/dependency/ownership edge | `relation` | `subject`, `object`, `predicate`, axis such as `restriction` |
| command, query, handler, port, adapter surface | `capability` | `subject`, `predicate`, axis such as `static` |
| persisted state, table, field, cache, lifecycle state | `state` | `subject`, `predicate`, axis such as `support` |
| write, publish, enqueue, provider call, file mutation | `effect` | `subject`, `predicate`, optional `object` |
| role gate, permission check, owner scope, visibility rule | `authority` | `subject`, `predicate` |
| precondition, postcondition, DTO shape, invariant, retry rule | `contract` | `subject`, `predicate`, optional `object` |
| domain meaning, identity meaning, unit/status meaning | `semantic` | `subject`, `predicate` |
| supplied trace/log/runtime edge | `runtime` | `subject`, `predicate`, optional `object` |

## Boundary Rules

- Static indexes and search results are navigation aids, not atoms.
- Framework conventions become atoms only when the expanded source or generated artifact was inspected.
- Workflows are discovered by reading source, then split into primitive atoms.
- Responsibilities are contexts over atoms, not primitive atoms.
- Policy/lawfulness is not written into ArchMap.
- Missing evidence is not written as measured absence.
- Generated import graphs, AST dumps, route lists, and symbol indexes are survey
  aids only. They cannot be promoted wholesale into final atoms.
- "Minimal" does not mean "coarse". If a source shows a command, state change,
  authority check, contract, or domain meaning, preserve that primitive fact
  instead of replacing it with a generic component or dependency atom.

## Semantic Rules

Semantic atoms are late-Wittgensteinian use observations: record what a term,
status, boundary, or value does in the repository's practice.

Use a `semantic` atom when the evidence shows one of these:

- a term's role in commands, tests, docs, or review rules
- a status/value meaning through transitions, guards, or invariants
- a domain identity that changes how code paths treat an object
- a boundary vocabulary that controls allowed operations

Do not use `semantic` for:

- dictionary definitions detached from use
- broad workflow summaries
- "this is good/bad/lawful/unsafe" judgements
- labels that merely restate file names or class names

Every semantic atom should answer: "Which observed use makes this meaning true?"
If that cannot be answered with refs, omit the semantic atom.

## Diagnostic Token Rules

Avoid diagnostic-shaped ids and predicates in authored atoms:

- `*_mismatch`
- `*_obstruction`
- `*_violation`
- `*_risk`
- `*_debt`
- `*_unsafe`
- `*_lawful`
- `*_nonzero`
- `*_failure`

Exception: use such a token only when the current extraction doctrine or an AG
fixture vocabulary explicitly models it as an observed source relation, and the
refs directly support that observation. Otherwise let ArchSig evaluators derive
diagnostic readings from neutral atoms, contexts, covers, and LawPolicy.

## Context Rules

Create a context when the source shows a local finite observation region:

- service method local flow
- route / handler / service / repository interaction
- provider mediation sequence
- transaction boundary sequence
- authority + state + effect local operation
- shared boundary, adapter seam, policy surface, or selected cover patch

The context contains atom ids and source refs. `restrictsTo` records observed
restriction direction between contexts. It does not assert a square, filler,
obstruction, homotopy, distance, U-adequacy, risk, or repair.

## Cover Rules

Create a cover when a finite family of contexts is the source-grounded
measurement surface for an AG profile. Covers name context ids only; they do
not choose coefficients, witness variables, or verdict predicates.
