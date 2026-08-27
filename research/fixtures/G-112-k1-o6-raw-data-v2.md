# G-112 K1 O6 raw data, second selection

This checkpoint supersedes the first K1 raw-data attempt.  That attempt is
invalid for O6 provenance because its Lean proof existed at commit `7f6b6317`
before the raw-data-only commit `779bd010`.  None of the carrier, predicate,
endpoint, arrow, candidate-assignment, or positive-family data selected below
occurs in that earlier proof.

This file fixes authored data only.  It supplies no candidate firing result,
noncoverage result, finite/cofinite result, isomorphism obstruction,
noninvertibility result, strict-image result, or qualification certificate.  A
later proof commit must derive every such proposition without changing this
checkpoint.  If any derivation fails, the failure must be recorded before a
third selection is made.

## Carrier and distinguished predicate

For every universe `u`, use an `AtomCarrier.{u}` whose five descriptive
coordinate types are one-point types and whose Atom type is
`ULift.{u} (Nat × Bool)`.  All coordinate projections are constant.

The distinguished predicate `left(atom)` holds exactly when the Boolean
coordinate `atom.down.2` is `false`.

## Endpoint doctrines

Fix identity-normalized doctrines on that carrier as follows.

1. `left-one`: one source cell; its unique extraction is `left`.
2. `all-one`: one source cell; its unique extraction contains every Atom.
3. `all-grid`: source type `ULift.{u} (Nat × Fin 2)`; every source cell extracts
   every Atom.  Its selected point is `ULift.up (0, 1)`.
4. `mixed-three`: source type `ULift.{u} (Fin 3)`; cell `0` extracts every Atom,
   while cells `1` and `2` extract exactly `left`.  Its selected point is
   `ULift.up 0`.

All vocabulary, semantic-reading, and resolution types are one-point types.
Their admission relations and source semantics are constantly true except for
the extraction distinctions stated above.

## Semantic arrows and candidate assignment

Fix these five semantic inputs.  Every Atom equivalence is the identity.

| ID | Source | Target | Source map |
| --- | --- | --- | --- |
| `left-id` | `left-one` | `left-one` | identity |
| `finite-to-grid` | `all-one` | `all-grid` | constant at `ULift.up (0, 1)` |
| `grid-to-finite` | `all-grid` | `all-one` | constant |
| `grid-id` | `all-grid` | `all-grid` | identity |
| `finite-to-mixed-three` | `all-one` | `mixed-three` | constant at `ULift.up 0` |

The final characterized-branch counterexample is `grid-id`.  Assign the
pre-registered candidate indices to the raw inputs as follows:

| Candidate indices | Raw input |
| --- | --- |
| `0` | `left-id` |
| `1`, `4`, `6` | `finite-to-grid` |
| `2`, `5`, `7` | `grid-to-finite` |
| `3`, `8`, `9` | `grid-id` |
| `10` | `finite-to-mixed-three` |

## Qualification positive-family data

Fix a three-member raw family on `FiniteModel.carrier`, with parameter type
`Fin 3` and distinguished parameter `0`.

- member `0` is the existing realized three-source-to-one-source selective
  arrow `finiteSelectiveThreeInput.semantic.hom`;
- members `1` and `2` are identities of one-source, all-extracting doctrines
  whose `Vocabulary` type is `Fin 3`, selected vocabulary is respectively `1`
  and `2`, and whose remaining reading coordinate types are one-point types.

The later proof must generate candidate firing for every member, a strict
realization-image outsider, a nonisomorphic pair, and a noninvertible member
from this raw family.  Those conclusions are not fields of the fixed data.
