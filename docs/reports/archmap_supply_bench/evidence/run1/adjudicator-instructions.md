# Adjudication Instructions (supply-bench, group-structured record)

You adjudicate the unmatched candidates of ONE extraction-consistency artifact
by rereading the cited sources. You never invent atoms and never use majority
or similarity; every decision cites source evidence.

## Inputs (paths given in your task prompt)

- consistency artifact (matched / onlyInPassA / onlyInPassB)
- the two candidate packets of YOUR pair (for atom content lookup by id)
- train-ticket checkout (refs `src:<path>` are relative to it)

Do not read any other run's packets, any other pair's adjudication, or
anything under reference_v1/ or alignment/.

## Task

For EVERY atom row in onlyInPassA and onlyInPassB (no omission, no surplus),
reread the cited source and record exactly one adjudication row:

- `merged`: the two passes observed the SAME fact with different keys.
  Merged rows carry a `mergeGroup` (unique id `group-1`, `group-2`, ... within
  this artifact) joining ALL rows that describe that same fact. A group must
  contain at least one pass-a and one pass-b atom. All rows of a group carry
  the same `canonicalAtomId`: the pass-a member's atom id (if several pass-a
  members, the lexicographically smallest).
- `adopted`: a real observation that only this pass made (complementary).
  No mergeGroup.
- `not-adopted`: not supported by the source on reread (wrong fact,
  double-count, or out of assigned evidence). No mergeGroup. Basis must cite
  the source line that refutes it.

Row shape:
```json
{"key": "<key from the onlyIn row>", "decision": "merged|adopted|not-adopted",
 "basis": "reread: <short evidence, file and line>",
 "candidateAtomId": "<the onlyIn row's candidateAtomId>",
 "mergeGroup": "group-N", "canonicalAtomId": "atom:..."}
```
(mergeGroup / canonicalAtomId only on merged rows.)

Rules:
- key and candidateAtomId must be copied verbatim from the onlyIn row.
- A pass-a atom and a pass-b atom that both match a MATCHED key are already
  settled; do not adjudicate matched atoms.
- Neutral phrasing in basis: never use the tokens failure, violation,
  obstruction, mismatch.
- basis must be sanitized: no absolute paths, no personal names.

## Output

Write ONE JSON file at the output path given in your prompt:
```json
{"consistencyRef": "<consistency id>", "adjudicator": "sonnet-reread",
 "adjudications": [ ...all rows... ]}
```
Final reply: counts only (merged rows, groups, adopted, not-adopted) plus at
most 3 one-line notes. No atom listings.
