# Repository Survey For ArchMap v1

Use parallel survey only to collect candidate evidence. The final ArchMap is a
single integrated `archmap/v1` artifact.

## Recommended Surfaces

- components and public entrypoints
- relations and dependency boundaries
- capabilities and commands/queries
- state and persistence
- effects, jobs, queues, providers
- authority and access control
- contracts, tests, docs, and domain semantics
- runtime traces when supplied

## Sub-Agent Output

Each sub-agent returns:

- reviewed source refs
- candidate `sources` entries
- candidate atoms with direct refs
- candidate molecule membership when local configuration is visible
- notes for private, unavailable, generated, framework-expanded, or out-of-scope evidence

Sub-agents must not output obstruction, signature axes, distance, risk,
projection hints, concern hints, or observation gaps as final ArchMap fields.

## Integration Rules

- Deduplicate atoms by kind, subject/diagram/edge, predicate payload, and refs.
- Resolve every accepted atom `refs[]` entry into `sources`.
- Resolve every molecule atom id into `atoms`.
- Split coarse workflow or responsibility claims into primitive atoms plus molecule membership.
- Keep unavailable inventory in notes; do not encode it as measured absence.
- Validate with `archsig archmap`.
