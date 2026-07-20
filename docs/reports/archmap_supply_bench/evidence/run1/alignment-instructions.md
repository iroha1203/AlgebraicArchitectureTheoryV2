# Reference-Alignment Adjudication Instructions

You complete the alignment between ONE pair's candidate union and its frozen
reference slice. A mechanical prefill has already aligned every candidate whose
atom-match-key@2 equals a reference key. Your job is the semantic remainder,
by rereading sources. Never use similarity scores or majority; every decision
cites source evidence or the atom contents themselves.

## Inputs (paths in your task prompt)

- prefill file: prefilled reference-matched rows + remaining lists
- reference slice (atomId + matchKey; the key encodes kind|subject|axis|predicate|object)
- the two candidate packets of YOUR pair (atom content lookup by id)
- train-ticket checkout

Do not read other pairs' packets or alignments.

## Task

1. For each remaining REFERENCE atom: decide
   - `reference-matched`: one or more remaining candidates describe the SAME
     fact under a different key (cite the source you reread).
   - `unrecovered`: no candidate of this pair describes it. Empty
     candidateAtomIds. basis says what the reference records and that no
     candidate covers it.
2. For each remaining CANDIDATE atom (after step 1 assignments): decide
   - `novel-correct`: source-verified fact that the reference does not carry
     (reference revision candidate). Group candidates of the same fact into
     ONE row.
   - `not-adopted`: not supported by source on reread. basis cites the
     refuting line.
3. Every reference atom and every candidate atom appears in EXACTLY ONE row
   (prefilled rows included). No candidate id may be reused.

Row shape (same as prefill rows):
```json
{"referenceAtomId": "...?", "candidateAtomIds": [...], "decision": "...",
 "basis": "reread: ..."}
```
`unrecovered` rows: referenceAtomId + empty candidateAtomIds.
`novel-correct` / `not-adopted` rows: NO referenceAtomId.

Neutral phrasing in basis (never: failure, violation, obstruction, mismatch).
Sanitized basis (no absolute paths, no personal names).

## Output

ONE JSON file at the given output path:
```json
{"schema": "archmap-reference-alignment/v1", "id": "alignment:<pair>-<chunk>",
 "referenceRef": "<reference slice id>", "referenceVersion": "1",
 "pairRef": "<pair id>", "adjudicator": "sonnet-reread",
 "rows": [ ...prefilled rows verbatim + your rows... ]}
```
Final reply: counts only (reference-matched mech/adjudicated, unrecovered,
novel-correct, not-adopted) + at most 3 one-line notes.
