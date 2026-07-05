# Release Runtime

Use this reference when the ArchSig source repository is not available.

The released skill environment may contain only:

- an `archsig` binary
- the `skills/` directory
- the user's repository, PR context, and ArchSig artifacts

Do not assume these exist:

- `tools/archsig/`
- Cargo project files
- test fixtures
- `docs/tool`
- AAT mathematical documents
- prior Git history beyond what the user repository exposes

## Binary Resolution

Try binary locations in this order:

1. `ARCHSIG_BIN` environment variable
2. `archsig` on `PATH`
3. `bin/archsig` beside the release root
4. `../bin/archsig` or `../../bin/archsig` relative to the skill directory
5. a user-supplied path

If none exists, stop and ask for the binary path.

Use this command shape:

```bash
"$ARCHSIG_BIN" pr-review \
  --base-archmap <archmap.json> \
  --after-archmap <after_archmap.json> \
  --path-archmap <intermediate_archmap.json> \
  --delta-archmap <archmap_delta.json> \
  --law-policy <law_policy.json> \
  --out <archsig-pr-review.json>
```

Omit `--after-archmap` only when the review intentionally does not need PR
drift / safe-change budget readings. Omit `--path-archmap` when no intermediate
ArchMap snapshots are available; the report will keep hidden-excursion absence
blocked instead of inferring it.

Do not ask the user to install Rust or build from source in a release-only
workflow unless they explicitly want to develop ArchSig itself.

## Required Artifacts

For `pr-review`, the release-only required artifacts are:

| Artifact | Required schema | How to obtain |
| --- | --- | --- |
| base ArchMap | `archmap/v0.5.0` | Existing project ArchMap. If absent, stop and use `archmap-creater`. |
| PR-local delta | `archmap-delta/v0.5.0` | Create from the current PR's base branch diff. |
| LawPolicy | `law-policy/v0.5.0` | Existing selected project policy. If absent, stop and use `law-policy-creater`. |
| PR review report | `archsig-pr-review-report/v0.5.0` | Output from `archsig pr-review`. |

No bundled default LawPolicy is valid for PR review. A generic LawPolicy would
change the review meaning and should not be substituted silently.

## Local Checks Without Repository Fixtures

Before running `archsig pr-review`, inspect the input JSON directly:

- `schema`
- ids such as `mapId`, `deltaId`, `lawPolicyId`
- `changedObservationRefs[]`
- `reviewIntent.sourceFirstTargets[]`
- `nonConclusions[]`

After running, inspect the report:

- `schema` is `archsig-pr-review-report/v0.5.0`
- `canonicalInputs` point to the intended files
- `policyBoundary.lawPolicyRequired` is true
- there is no raw diff input field

If JSON parsing tools are unavailable, read the files as text and check these
fields manually. The ArchSig binary remains the authoritative validator for the
PR-review command surface.

## Failure Handling

Stop instead of guessing when:

- the base ArchMap path is unknown or missing
- the LawPolicy path is unknown or missing
- the base branch diff cannot be determined or supplied
- the ArchSig binary cannot be found
- a JSON file has the wrong `schema`
- changed observations cannot be mapped to the base ArchMap and the user asked
  for a confident architecture review

Report the missing prerequisite and name the next skill or user input needed.
