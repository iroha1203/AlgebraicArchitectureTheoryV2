# Adjudication Rubric (integrator delegation, train-ticket cancel/refund trial)

You adjudicate unmatched atom candidates from a dual-pass ArchMap survey.
Inputs:
- Consistency artifact: `extraction-consistency.json` (same directory as this file).
  Process EVERY entry in `onlyInPassA` and `onlyInPassB` whose FIRST ref path
  starts with your assigned service prefix(es). Ignore other entries.
- Candidate packets: `candidates/pass-{a,b}-chunk-0{1..4}.json` (look up atom
  bodies by `candidateAtomId`).
- Source repository root: `../../train-ticket` relative to this directory
  (refs are `src:<repo-relative-path>[:line]`).
- Vocabulary catalog (allowed kinds/axes/predicates):
  <REPO>/tools/archsig/skills/archmap-creater/references/vocabulary-catalog.md

## Decisions

For every assigned entry, REREAD the cited source location first, then record
exactly one decision:

- `merged`: the same observed fact appears in the other pass under a different
  key (search both `onlyInPassA` and `onlyInPassB` for the counterpart, and
  also check `matched` rows to avoid duplicating an already-matched fact).
  Record `merged` for BOTH keys of the pair. Choose ONE side's atom verbatim
  as the canonical atom (prefer the clearer, service-qualified subject and a
  catalog predicate); you may union the refs of both sides. The basis must
  cite the reread source (`file:line`) and name the kept atom id.
- `adopted`: only one pass saw it and the reread confirms the evidence.
  The candidate atom is kept verbatim (id unchanged). Basis cites the reread.
- `not-adopted`: the reread does not support the atom (misreading, invented
  value, no evidence at the cited location), or the fact is already fully
  covered by a matched/merged atom (then name that atom in the basis), or the
  predicate is catalog-external and no truthful catalog predicate exists.

## Hard rules

- No majority voting, no similarity scores, no adoption without rereading.
- Canonical atoms MUST use only catalog kinds/axes/predicates. When merging a
  catalog-external predicate with a catalog counterpart, keep the catalog one.
  If you must normalize (canonical atom's kind|subject|axis|predicate|object
  differs from both source keys), add ONE extra adjudication row whose `key`
  is the canonical atom's exact match key (`kind|subject|axis|predicate|object`,
  omitting absent predicate/object segments) with the same decision and a
  basis explaining the normalization.
- Never introduce diagnostic tokens (failure / violation / obstruction /
  mismatch) into ids, predicates, or objects.
- Bases must be short (one sentence), sanitized (no absolute paths), and cite
  repo-relative `file:line`.
- Semantic atoms must keep `object` and alias separation (do not merge two
  genuinely different uses of one subject; if both passes observed different
  real uses, adopt both).

## Output

Write ONE JSON file (path given in your task) with exactly this shape:

```json
{
  "service": "<your prefix(es)>",
  "adjudications": [
    {"key": "...", "decision": "merged|adopted|not-adopted", "basis": "..."}
  ],
  "canonicalAtoms": [
    {"id": "...", "kind": "...", "subject": "...", "axis": "...",
     "predicate": "...", "object": "...", "refs": ["src:..."]}
  ],
  "coverage": {"assignedEntryCount": 0, "adjudicatedEntryCount": 0}
}
```

- `adjudications` must cover every assigned entry key (plus any extra
  normalization keys). `canonicalAtoms` holds one atom per merged pair and one
  per adopted entry (verbatim from a candidate packet apart from ref unions /
  catalog normalization).
- Verify the JSON parses and `assignedEntryCount == adjudicatedEntryCount`
  (counting one per assigned entry, extras not counted) before replying.
