# G-112 K1 O6 coverage counterexample raw data

This file fixes the authored raw data for the K1 O6 coverage refutations before
their Lean proofs are committed.  It records data only: no coverage result,
candidate firing proof, finite/cofinite proof, isomorphism obstruction, or
qualification certificate is supplied here.

## Carrier

For every universe `u`, use one `AtomCarrier.{u}` whose five descriptive
coordinate types are one-point types and whose `Atom` type is `ULift.{u} Nat`.
All coordinate projections are constant.  Define the distinguished predicate
`even(atom)` by the existence of `n : Nat` with `atom.down = 2 * n`.

## Endpoint doctrines

Fix the following identity-normalized doctrines on that carrier.

1. `bad-one`: one source cell; its unique extraction is `even`.
2. `all-one`: one source cell; its unique extraction contains every Atom.
3. `all-nat`: source type `ULift.{u} Nat`; every source cell extracts every Atom.
4. `mixed`: source type `ULift.{u} Bool`; the `false` cell extracts every Atom
   and the `true` cell extracts exactly `even`.  The selected point is `false`.

All vocabulary, semantic-reading, and resolution types are one-point types.
Their admission relations and source semantics are constantly true except for
the extraction distinctions stated above.

## Semantic arrows

Fix these five semantic inputs.

| ID | Source | Target | Source map | Atom equivalence |
| --- | --- | --- | --- | --- |
| `bad-id` | `bad-one` | `bad-one` | identity | identity |
| `finite-to-infinite` | `all-one` | `all-nat` | constant at `0` | identity |
| `infinite-to-finite` | `all-nat` | `all-one` | constant | identity |
| `infinite-id` | `all-nat` | `all-nat` | identity | identity |
| `finite-to-mixed` | `all-one` | `mixed` | constant at `false` | identity |

The final characterized-branch counterexample is `infinite-id`.

## Fixed candidate assignment

The pre-registered candidate list itself remains the F0 artifact.  For the K1
attempt following this checkpoint, fix the refutation inputs as follows:

| Candidate indices | Raw input |
| --- | --- |
| `0` | `bad-id` |
| `1`, `4`, `6` | `finite-to-infinite` |
| `2`, `5`, `7` | `infinite-to-finite` |
| `3`, `8`, `9` | `infinite-id` |
| `10` | `finite-to-mixed` |

The subsequent proof must establish both that each assigned candidate fires
and that its assigned input has no anchored coverage witness.  If either proof
fails, this data is not to be altered inside that proof commit; the failed
attempt must be recorded before a new raw-data checkpoint is selected.

## Qualification positive-family data

Fix a two-member raw family on `FiniteModel.carrier`:

- `false`: the existing realized two-source-to-one-source selective arrow
  `finiteSelectiveTwoInput.semantic.hom`;
- `true`: the identity of a one-source, all-extracting doctrine whose
  `Vocabulary` is `Bool`, selected vocabulary is `false`, and other reading
  coordinate types are one-point types.

The subsequent proof must generate candidate firing, a strict-realization-image
outsider, a nonisomorphic pair, and a noninvertible member from this raw family;
none of those conclusions is part of the fixed data.
