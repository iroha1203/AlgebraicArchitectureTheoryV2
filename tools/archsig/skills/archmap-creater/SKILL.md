---
name: archmap-creater
description: Create bounded archmap/v0.5.0 finite-poset-site artifacts from repository evidence.
---

# ArchMap Creater

Use this skill to create `archmap/v0.5.0` documents and their authoring
artifacts from source-grounded repository evidence.

The core discipline is to keep the mechanical layer and the reading layer
separate. The mechanical layer may only enumerate files, hash content, compare
literal normalized keys, and check reference consistency. It must not generate
atoms, choose semantic meaning, adopt candidates, vote between passes, merge by
similarity, or convert a numeric match value into a verdict.

ArchMap authoring claims are bounded to the recorded revision and the selected
scope. Do not claim that all possible repository evidence was extracted.

## Inputs

- A repository checkout and a user-approved scope: include globs, exclude globs,
  requested scope text, and any author-supplied evidence files.
- An ArchSig binary. Resolve it in this order: `$ARCHSIG_BIN`, `archsig` on
  `PATH`, a bundled binary near the skill, then the local checkout build.
- A run-specific authoring directory, normally under `.tmp/archmap-authoring/`.
  Do not overwrite a previous run directory unless the user explicitly asks.
- Optional: a LawPolicy and MeasurementProfile for a post-authoring
  `archsig analyze` run.
- Optional: a baseline scope manifest for `incremental-dual` mode.

## Operating Modes

- `full-dual`: default for initial authoring and major revisions. Survey the
  full worklist twice with independent reading passes.
- `incremental-dual`: use `scope-manifest --baseline` and survey changed or new
  worklist entries twice before integrating them into an existing ArchMap.
- `single-pass`: allowed only when the user explicitly selects it. Record the
  consistency artifact as a degenerate single-pass run; do not present it as a
  dual-pass result.

## Workflow

1. **Preflight**
   - Resolve the ArchSig binary. If no binary is available, stop and report that
     validation was not run. Do not replace it with an ad hoc checker.
   - Record git revision and dirty status when available.
   - Confirm the requested scope, include/exclude globs, and added evidence
     files before reading source files.
   - Choose a fresh run directory. Keep authoring artifacts there until the
     user asks to publish or commit them.

2. **Scope Manifest**
   - If `archsig scope-manifest` is available, run it to produce
     `<run-dir>/scope-manifest.json`.
   - Until that CLI exists, create the same `archmap-scope-manifest/v0.5.0` shape by
     hand from a deterministic file list, repo-relative paths, sha256 hashes, and
     the approved scope spec.
   - Present exclusions to the user or author for approval. Do not start the
     reading passes before the scope manifest is approved.
   - `out-of-scope` is valid only in scope-manifest exclusions after approval or
     reapproval. It is not a pass-time skip reason.

3. **Pass A Survey**
   - Split the worklist into deterministic contiguous chunks, default size 20.
   - Each sub-agent reads every source in its chunk and emits one
     `archmap-candidate-packet/v0.5.0` with a `surveyRows` entry for every worklist
     row in the chunk.
   - Survey for components, relations, capabilities, state, effects, authority,
     contracts, semantic use, runtime traces, context boundaries, restriction
     directions, and finite cover candidates.
   - Known gap types must be checked explicitly: per-file semantic survey,
     supplied runtime trace evidence, and supplied permission or authority
     evidence.
   - Scope round-trip rule: if a source appears out of scope during reading, do
     not skip it as out of scope. Report it to the integrator, update
     exclusions, regenerate the scope manifest, and obtain reapproval before
     continuing.

4. **Pass B Survey**
   - Run an independent reading pass over the same approved worklist and the same
     deterministic chunking.
   - Do not share Pass A candidate atoms with Pass B readers. The worklist and
     protocol are shared; the reading is independent.
   - Apply the same round-trip rule as Pass A.

5. **Consistency**
   - If `archsig extraction-diff` is available, run it over Pass A and Pass B
     candidate packets.
   - Until that CLI exists, build `archmap-extraction-consistency/v0.5.0` by applying
     `atom-match-key@1` and the context key rules from the references. Mark this
     as hand-authored consistency in the run notes.
   - For every `onlyInPassA` or `onlyInPassB` entry, the integrator rereads the
     cited source and records an adjudication: `adopted`, `merged`, or
     `not-adopted`.
   - Do not use majority, similarity, or automatic adoption to decide unmatched
     candidates. Unmatched candidates are rereading queues, not proof of error.

6. **Integrate**
   - Build the final `archmap.json` after adjudication.
   - Use `atom-match-key@1` for candidate deduplication and union refs only after
     the integrator confirms semantic identity.
   - Preserve semantic aliases: if the same subject has different observed
     uses, keep separate semantic atoms and carry the difference in key-bearing
     fields, especially `object`.
   - Choose contexts, `restrictsTo`, and covers using `mapping-guide.md`.

7. **Coverage Ledger**
   - Generate `archmap-coverage-ledger/v0.5.0` from candidate packet survey rows.
   - Ledger rows must span the worklist one-to-one. Extra rows and missing rows
     are errors.
   - Use only procedural survey reasons in ledger rows: `private`, `binary`,
     `unreadable`, or `tooling-error`.

8. **Validate**
   - Run the existing `archsig archmap --input archmap.json` validation.
   - When authoring flags are implemented in ArchSig, also run:

     ```bash
     archsig archmap \
       --input archmap.json \
       --scope-manifest <run-dir>/scope-manifest.json \
       --candidate-packets '<run-dir>/candidates/*.json' \
       --coverage-ledger <run-dir>/coverage-ledger.json \
       --out <run-dir>/archmap-validation.json
     ```

   - Before those flags exist, perform the same authoring checks manually from
     `coverage-and-consistency.md` and record that authoring validation was
     hand-checked rather than binary-checked.
   - Repair any failed checks and rerun applicable validation.
   - If LawPolicy and MeasurementProfile are supplied, run `archsig analyze`.
     If the user asks for analyze without LawPolicy, stop and ask for LawPolicy
     creation rather than inventing one.

9. **Deliver**
   - Report in this order:
     1. ArchMap path and the validation conclusion, such as
        `AUTHORING_SURVEY_TRACEABLE_WITHIN_SCOPE`.
     2. Scope summary: revision, dirty status, worklist row count, exclusions.
     3. Atom counts by kind and a few representative atoms.
     4. Contexts, covers, and restriction directions.
     5. Consistency summary: matchRate and adjudication counts. State that
        matchRate is a record, not a pass/fail verdict. In Japanese reports,
        use the fixed phrase: `記録であり合否ではない`.
     6. Coverage ledger `not_surveyed` or `partially_surveyed` rows with reasons.
     7. Authoring artifact paths.
     8. Optional analyze result.
   - Before publishing or committing artifacts, scrub local absolute paths,
     personal names, nonpublic labels, secrets, and machine-specific
     identifiers. Keep source paths repo-relative.

## Stop Conditions

- No ArchSig binary: stop and report missing validation.
- Scope manifest not approved: stop before source reading.
- Authoring CLI surface not yet implemented: continue only with the hand-written
  artifact procedure in the references, and report that authoring checks were
  not binary-enforced.
- Unreadable worklist source: record a procedural reason; do not infer content.
- Source appears out of scope during reading: round-trip to scope-manifest
  exclusions and reapproval.
- Analyze requested without LawPolicy: stop and request LawPolicy creation.
- Candidate packet contains diagnostic shortcut atoms or semantic atoms without
  `object`: fail before integration.

## References

- `references/extraction-protocol.md`
- `references/coverage-and-consistency.md`
- `references/vocabulary-catalog.md`
- `references/schema-cheatsheet.md`
- `references/mapping-guide.md`
- `references/examples.md`
- `references/prompt-pack.md`

Respond to the user in Japanese. Keep Issue, PR, and commit text in Japanese.
