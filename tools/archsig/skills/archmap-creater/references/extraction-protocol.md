# Extraction Protocol

This protocol fixes the authoring procedure around deterministic worklists and
independent reading passes. It does not automate atom generation.

## Mechanical Layer

The mechanical layer may perform only four operations:

- enumerate selected files and author-supplied evidence files
- hash source bytes with sha256
- compare normalized literal keys
- check that references resolve

Arithmetic aggregation of key-comparison results (counting matched and
unmatched keys, computing ratios such as matchRate or bench metrics) is a
consequence of these four operations and stays inside the mechanical layer.

It must not interpret source meaning, choose atoms, adopt candidates, merge by
similarity, vote between passes, or assign verdicts from match numbers.

## Scope Manifest

Create a run-specific directory first, normally under `.tmp/archmap-authoring/`.
Use a fresh directory per run and do not overwrite an earlier run unless the
user explicitly asks.

When available, create `<run-dir>/scope-manifest.json` with:

```bash
archsig scope-manifest \
  --repo-root . \
  --include 'src/**/*.rs' \
  --exclude '**/target/**' \
  --add-evidence 'trace:orders-happy-path=authoring/evidence/orders.trace.json' \
  --out <run-dir>/scope-manifest.json
```

The worklist is sorted by byte-wise path order. Author-added evidence is a file
registered by `--add-evidence <kind>:<name>=<repo-relative-path>` and appended
after file worklist entries by source id order. `--baseline <old-manifest>` is
used for incremental manifests.

Use the CLI to create the manifest. It records repo-relative paths, byte-wise
sorting, sha256 content hashes, and an explicit scope approval record.

Exclusion reasons at scope approval time are:

- `user-excluded`
- `private`
- `generated`
- `binary`
- `out-of-scope`

`out-of-scope` is not a pass-time skip reason. It is only a scope approval
decision recorded in the manifest.

## Chunking

Split the manifest worklist into deterministic contiguous chunks. The default
chunk size is 20 worklist rows. Every pass must use the same chunk boundaries.

Readers may inspect neighboring files when needed for understanding, but the
candidate packet must still contain a `surveyRows` entry for each assigned row.

## Survey Surface

Survey the selected scope for:

- components and public entrypoints
- relations and dependency boundaries
- capabilities and commands or queries
- state, persistence, lifecycle, and cache facts
- effects, jobs, queues, providers, and file mutations
- authority, access control, ownership, and visibility checks
- contracts, preconditions, postconditions, DTO shape, invariants, retry rules
- semantic use evidence in source, tests, docs, and review rules
- supplied runtime traces
- source-grounded context boundaries and restriction directions
- finite cover candidates for AG measurement

Known repeated gap types:

- per-file semantic survey was skipped
- supplied runtime traces were not read as evidence
- supplied permission or authority evidence was not read

## Pass A And Pass B

Pass A and Pass B read the same approved manifest and chunking independently.
Candidate atoms from one pass are not given to the other pass. Both passes emit
`archmap-candidate-packet/v0.5.4`.

Allowed `surveyRows[].status` values are:

- `read`
- `partial`
- `skipped`

Allowed `partial` / `skipped` reasons are procedural only:

- `private`
- `binary`
- `unreadable`
- `tooling-error`

## Round Trip Rule

If a reader concludes that a source is outside the requested scope, the reader
must not mark it skipped. The reader reports the source to the integrator. The
integrator updates scope-manifest exclusions, asks for reapproval, regenerates
the manifest, and restarts affected chunks. Scope decisions stay at the approval
gate.

## Candidate Packet Requirements

Each packet includes:

- `reviewedSources`
- `candidateSources`
- `candidateAtoms`
- `candidateContexts`
- `candidateCovers`
- `surveyRows`
- `privateUnavailableNotes`
- `selfReview`

Candidate semantic atoms require direct use evidence and an `object` value. The
object carries the observed meaning so that alias differences appear in
`atom-match-key@1`.

Notes and `privateUnavailableNotes` must be sanitized summaries. Do not include
local absolute paths, personal names, nonpublic labels, secrets, or
machine-specific identifiers. Source paths in artifacts are repo-relative.

## Integration

Run `archsig extraction-diff` after both passes. The integrator rereads the
cited source for every unmatched key and records `adjudications`. Integration is
complete only after those rereads, not after mechanical matching.
