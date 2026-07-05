# Repository Survey For ArchMap v2

Use parallel survey only to collect candidate evidence. The final ArchMap is a
single integrated `archmap/v0.5.0` artifact.

Do not delegate ArchMap creation to a script. Mechanical inventories may guide
the survey, but final atoms require source reading and author judgement about
primitive observed facts.

## Recommended Surfaces

- components and public entrypoints
- relations and dependency boundaries
- capabilities and commands/queries
- state and persistence
- effects, jobs, queues, providers
- authority and access control
- contracts, tests, docs, and domain semantics
- runtime traces when supplied
- source-grounded context boundaries and restriction directions
- finite cover candidates for AG measurement

## Sub-Agent Output

Each sub-agent returns:

- reviewed source refs
- candidate `sources` entries
- candidate atoms with direct refs
- candidate semantic atoms only when they include use-evidence
- candidate contexts with atom membership and restriction direction
- candidate covers with context membership
- notes for private, unavailable, generated, framework-expanded, or out-of-scope evidence

Sub-agents must not output obstruction, signature axes, distance, risk,
projection hints, concern hints, observation gaps, or diagnostic-shaped shortcut
atoms as final ArchMap fields.

## Integration Rules

- Deduplicate atoms by kind, subject, axis, predicate/object payload, and refs.
- Resolve every accepted atom `refs[]` entry into `sources`.
- Resolve every context atom id into `atoms`.
- Resolve every cover context id into `contexts`.
- Split coarse workflow or responsibility claims into primitive atoms plus context membership.
- Reject component-only / relation-only output when reviewed sources contain
  capabilities, states, effects, authority, contracts, runtime traces, or
  semantic use evidence.
- Reject semantic atoms that do not explain the observed use that makes the
  meaning true.
- Reject diagnostic-shaped ids / predicates unconditionally; source-supported
  observations must still be written as neutral atom ids and predicates.
- Keep unavailable inventory in notes; do not encode it as measured absence.
- Validate with `archsig archmap`.
