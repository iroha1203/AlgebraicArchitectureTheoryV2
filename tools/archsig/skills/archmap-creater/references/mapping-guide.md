# ArchMap v2 Mapping Guide

ArchMap v2 records source-grounded atoms, finite poset contexts, and covers
under the fixed ArchMap v2 extraction doctrine. ArchSig computes diagnostics and
bounded conclusions later.

## Source Cue To Atom

| Source cue | Atom kind | Payload |
| --- | --- | --- |
| file, module, class, service, package exists | `component` | `subject`, `axis: "static"` |
| call/import/dependency/ownership edge | `relation` | `subject`, `object`, `predicate`, axis such as `restriction` |
| command, query, handler, port, adapter surface | `capability` | `subject`, `predicate`, optional `object` |
| persisted state, table, field, cache, lifecycle state | `state` | `subject`, `predicate`, optional `object` |
| write, publish, enqueue, provider call, file mutation | `effect` | `subject`, `predicate`, optional `object` |
| role gate, permission check, owner scope, visibility rule | `authority` | `subject`, `predicate`, optional `object` |
| precondition, postcondition, DTO shape, invariant, retry rule | `contract` | `subject`, `predicate`, optional `object` |
| domain meaning, identity meaning, unit/status meaning | `semantic` | `subject`, `predicate`, required `object` |
| supplied trace/log/runtime edge | `runtime` | `subject`, `predicate`, optional `object` |

## Boundary Rules

- Static indexes and search results are navigation aids, not atoms.
- Framework conventions become atoms only when expanded source or generated
  artifacts were inspected.
- Workflows are discovered by reading source, then split into primitive atoms.
- Responsibilities are contexts over atoms, not primitive atoms.
- Policy and lawfulness are not written into ArchMap.
- Missing evidence is not written as measured absence.
- Generated import graphs, AST dumps, route lists, and symbol indexes are survey
  aids only. They cannot be promoted wholesale into final atoms.
- If a source shows a command, state change, authority check, contract, or domain
  meaning, preserve that primitive fact instead of replacing it with a generic
  component or dependency atom.

## Semantic Rules

Semantic atoms are use observations: record what a term, status, boundary, or
value does in repository practice.

Use a `semantic` atom when evidence shows:

- a term's role in commands, tests, docs, or review rules
- a status or value meaning through transitions, guards, or invariants
- a domain identity that changes how code paths treat an object
- a boundary vocabulary that controls allowed operations

Every semantic atom must answer: which observed use makes this meaning true?
Store the answer's meaning identifier in `object` and cite source refs.

Do not use `semantic` for:

- dictionary definitions detached from use
- broad workflow summaries
- good/bad/lawful/unsafe judgments
- labels that merely restate file names or class names

## Alias Preservation

If the same subject has different observed use evidence, keep separate semantic
atoms. Do not merge them merely because they point to the same component.

This is the observation-side counterpart to PRD-4 `aliasWitnesses`: ArchSig may
detect alias collapse later, but ArchMap authoring must not collapse the input
aliases first.

Required practice:

- put the meaning difference in `object`
- keep different use evidence as different semantic atoms
- when two semantic candidates have the same atom-match key but different refs,
  the integrator must reread the sources before unioning refs

## Diagnostic Token Rules

Do not use diagnostic-shaped ids or predicates in authored atoms:

- `*_mismatch`
- `*_obstruction`
- `*_violation`
- `*_risk`
- `*_debt`
- `*_unsafe`
- `*_lawful`
- `*_nonzero`
- `*_failure`

Source-supported observations must still be written as neutral atoms. Let
evaluators derive diagnostic readings from neutral atoms, contexts, covers, and
LawPolicy.

## Context Rules

Create a context when the source shows a local finite observation region:

- service method local flow
- route / handler / service / repository interaction
- provider mediation sequence
- transaction boundary sequence
- authority + state + effect local operation
- shared boundary, adapter boundary, policy surface, or selected cover patch

The context contains atom ids and source refs. `restrictsTo` records observed
restriction direction between contexts. It does not assert obstruction,
homotopy, distance, risk, or repair.

Operational cue for `C1 restrictsTo C2`: source evidence shows that the
observation region of `C1` enters or shares the region of `C2`, such as a shared
adapter, common boundary, downstream convergence point, or fixture pattern
where an including patch maps to an overlap patch.

## Cover Rules

Create a cover when a finite family of contexts is the source-grounded
measurement surface for one LawPolicy / MeasurementProfile.

- One cover corresponds to one measurement surface.
- The cover label or authoring note should name what is being measured.
- Covers with no overlap, no shared atom, and no restriction convergence are
  poor inputs for Cech-style measurements; document or avoid that cut.
- Covers do not choose coefficients, witness variables, or verdict predicates.
