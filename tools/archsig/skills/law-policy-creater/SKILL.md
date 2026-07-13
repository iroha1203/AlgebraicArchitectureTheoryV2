---
name: law-policy-creater
description: Create law-policy/v0.5.1 files for current ArchSig measurement runs.
---

# LawPolicy Creater

Use this skill to create a `law-policy/v0.5.1` file, a separate
`measurement-profile/v0.5.1` file, and a `law-equation-surface/v0.5.1` /
`archsig-policy-bundle/v0.5.1` input set for an AG run.

## Workflow

1. Select evaluator manifests and laws from the current registry.
2. Select one external MeasurementProfile artifact and one law-equation-surface artifact for the run.
3. Record `basisLedger` entries and policy basis refs.
4. Validate with `archsig measurement-profile --measurement-profile <profile> --out <report>`.
5. Validate with `archsig law-policy --law-policy <policy> --measurement-profile <profile> --law-surface <law-surface> --out <report>`.
6. Create and validate a bundle with `archsig policy-bundle --law-policy <policy> --law-surface <law-surface> --measurement-profile <profile> --out <bundle>`.
7. Run `archsig analyze --archmap <archmap> --policy-bundle <bundle> --out-dir <run-dir>`.

For the executable fixture workflow, use
`references/schema-guide.md` and `references/law-surface-examples.md`.
For `ag.law-conflict-tor`, use an explicit `policies[].lawPair` with exactly two
distinct law ids; law-id naming conventions are not selectors.
The bundle is the reproducibility record: its three component references and
canonical fingerprints must be preserved with the run.

Gate decisions belong in `archsig gate` policy, not in `analyze` flags.
