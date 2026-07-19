# Adjudication Instructions (train-ticket fullbuild, Issue #3545)

You are an adjudication delegate for one chunk of an ArchMap dual-pass
extraction. Two independent reading passes produced candidate atoms; the
mechanical diff left unmatched candidates. Unmatched candidates are rereading
queues, NOT proof of error. Your job: for EVERY row in your work order, reread
the cited source and record an adjudication. Never decide by similarity or
majority — only by what the source actually shows.

## Fixed paths

- Repo root: `<SCRATCHPAD>/train-ticket`
- Your work order: `fullbuild/adjudication/work-<chunkId>.json` (path given in task prompt) — contains `onlyInPassA` and `onlyInPassB` rows `{key, candidateAtomId, refs}`.
- Both candidate packets for your chunk: `fullbuild/candidates/pass-a-<chunkId>.json` and `fullbuild/candidates/pass-b-<chunkId>.json` (read both fully — you need each pass's atom list to detect cross-pass same-observation pairs).

## Decisions

For each unmatched row, reread the cited source lines, then record exactly one:

- `merged`: the same source-grounded observation exists in the OTHER pass under
  a different match key (naming/axis/object phrasing drift). Confirm semantic
  identity by the reread, then emit ONE canonical atom for the pair.
- `adopted`: a genuine observation only one pass made; the reread confirms the
  cited evidence supports it. Emit the canonical atom.
- `not-adopted`: the reread does NOT support it (wrong file, invented, class
  mislabeled), OR it duplicates another atom in the SAME pass, OR it is
  diagnostic-shaped and cannot be restated neutrally, OR its predicate is not
  in the vocabulary catalog and no catalog predicate states the same fact
  truthfully. State why in `basis`.

Alias preservation: different observed semantic uses of the same subject are
NOT the same observation — keep them as separate `adopted` atoms. When in
doubt whether two candidates state the same fact or two different facts, reread
and decide from the source, never from wording similarity.

A pair (one row from each side describing the same observation) needs the
merged decision recorded on BOTH rows, pointing to the same canonical atom.

## Canonical atom form

For merged/adopted rows, output the full canonical atom JSON, normalized:

- `subject`: `<service-dir>.<ClassName>` (e.g. `ts-cancel-service.CancelServiceImpl`,
  `ts-common.OrderStatus`). For yml/config subjects: `<service-dir>.application-yml`.
- `id`: `atom:<kind>:<subject-slug>[:<predicate-slug>[-<object-hint>]]`, lowercase kebab.
- `axis` per default table (component→static, relation→relation,
  capability→capability, effect→effect, authority→authority, semantic→semantic,
  contract→specification, state→state) unless cech/runtime/restriction evidence applies.
- `refs`: union of both passes' refs for merged atoms, repo-relative, `:line` allowed.
- NEUTRAL PHRASING everywhere: no `failure` / `violation` / `obstruction` /
  `mismatch` tokens in id/predicate/object. If a candidate carries one,
  restate branch-descriptively (what each value selects), do not carry the token.
- Semantic atoms must keep an `object` carrying the observed meaning.
- cech `sectionValue` atoms: keep `subject` as the candidate context id proposed
  by the pass, object `section=<quantity>:<value-label>`; these are adjudicated
  like any other atom (the integrator remaps context ids later).

## Output

Write ONE JSON file at the output path given in your task prompt:

```json
{
  "chunkId": "<chunkId>",
  "adjudications": [
    {
      "key": "<row key verbatim>",
      "candidateAtomId": "<row candidateAtomId>",
      "pass": "pass-a" | "pass-b",
      "decision": "merged" | "adopted" | "not-adopted",
      "basis": "Reread <repo-relative-path>:<line> — <one sentence of what the source shows>. <kept/dropped rationale>.",
      "canonicalAtom": { ...full atom JSON... }   // merged/adopted only
    }
  ]
}
```

Every row in your work order gets exactly one adjudication entry. `basis` must
cite at least one concrete file:line you actually reread. Keep basis to 1-2
sentences, sanitized (no absolute paths).

## Reporting back

Short reply only: output path, counts (merged/adopted/not-adopted), and at most
2 one-line notes on systematic drift patterns you saw (useful for the tooling
feedback report).
