# G-112 K1 O6 raw data, third selection

This checkpoint begins K1 Cycle 4.  The first selection lacked a proof-before-
data record.  The second selection was rejected because it preserved the first
selection's candidate assignment and recoded its countable partition and
positive family without changing the proof route.

The data below changes both routes.  Earlier candidates are now refuted by a
different assignment that uses finite bad endpoints wherever their firing
conditions permit, rather than using infinite endpoints uniformly.  The
positive family uses two newly authored nonidentity arrows and does not reuse
`finiteSelectiveTwoInput` or `finiteSelectiveThreeInput`.

This file fixes authored data only.  It supplies no candidate firing result,
noncoverage result, finiteness result, strict-image result, isomorphism
obstruction, noninvertibility result, or qualification certificate.  A later
proof commit must derive every proposition without changing this checkpoint.

## Carrier and distinguished predicate

For every universe `u`, use an `AtomCarrier.{u}` whose five descriptive
coordinate types are one-point types and whose Atom type is

`ULift.{u} (Nat ⊕ (Nat ⊕ (Nat → Bool)))`.

All coordinate projections are constant.  The distinguished predicate
`first-summand(atom)` holds exactly when `atom.down` is in the outer `Nat`
summand.  Thus the authored bad extraction is a summand predicate, not the
even/odd or Boolean-slice partition used in the rejected cycles.

## Endpoint doctrines

Fix identity-normalized doctrines on that carrier as follows.

1. `summand-one`: one source cell; its unique extraction is `first-summand`.
2. `all-one`: one source cell; its unique extraction contains every Atom.
3. `all-plane`: source type `ULift.{u} (Nat × Nat)`; every source cell
   extracts every Atom.  Its selected point is `ULift.up (0, 1)`.
4. `mixed-four`: source type `ULift.{u} (Fin 4)`; cell `0` extracts every Atom,
   while cells `1`, `2`, and `3` extract exactly `first-summand`.  Its selected
   point is `ULift.up 0`.

All vocabulary, semantic-reading, and resolution types are one-point types.
Their admission relations and source semantics are constantly true except for
the extraction distinctions stated above.

## Semantic arrows and changed candidate assignment

Fix these five semantic inputs.  Every Atom equivalence is the identity.

| ID | Source | Target | Source map |
| --- | --- | --- | --- |
| `summand-id` | `summand-one` | `summand-one` | identity |
| `finite-to-plane` | `all-one` | `all-plane` | constant at `ULift.up (0, 1)` |
| `plane-to-finite` | `all-plane` | `all-one` | constant |
| `plane-id` | `all-plane` | `all-plane` | identity |
| `finite-to-mixed-four` | `all-one` | `mixed-four` | constant at `ULift.up 0` |

The final characterized-branch counterexample is `plane-id`.  Assign the
pre-registered candidate indices to raw inputs as follows:

| Candidate indices | Raw input | Intended raw obstruction location |
| --- | --- | --- |
| `0`, `6`, `7` | `summand-id` | finite bad endpoint |
| `1`, `5`, `8`, `10` | `finite-to-mixed-four` | finite target's unused bad cells |
| `2` | `plane-to-finite` | infinite source |
| `3`, `9` | `plane-id` | infinite source and target |
| `4` | `finite-to-plane` | infinite target |

The table is part of the fixed raw selection.  The later proof must establish
both candidate firing and noncoverage for every assigned index.

## Qualification positive-family data

Fix a two-member raw family on `FiniteModel.carrier`, with parameter type
`Fin 2` and distinguished parameter `0`.  Both members are newly authored exact
arrows whose extraction, admission, resolution, and source-semantics relations
are constantly true and whose normalizations are identities.

### Member 0

- source endpoint: `Source := Fin 2`, selected source `0`,
  `Vocabulary := Fin 5`, selected vocabulary `0`;
- target endpoint: `Source := PUnit`, selected source `unit`,
  `Vocabulary := Fin 5`, selected vocabulary `0`;
- semantic arrow: constant source map to `unit`, identity Atom equivalence.

### Member 1

- source endpoint: `Source := Fin 3`, selected source `0`,
  `Vocabulary := Fin 7`, selected vocabulary `0`;
- target endpoint: `Source := PUnit`, selected source `unit`,
  `Vocabulary := Fin 7`, selected vocabulary `0`;
- semantic arrow: constant source map to `unit`, identity Atom equivalence.

The later proof must generate candidate firing for both members, a strict
realization-image outsider, a nonisomorphic pair, and a noninvertible member.
None of those conclusions is a field of the fixed family.
