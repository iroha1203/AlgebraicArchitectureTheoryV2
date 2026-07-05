---
name: law-policy-creater
description: Create law-policy/v0.5.0 files for current ArchSig measurement runs.
---

# LawPolicy Creater

Use this skill to create a `law-policy/v0.5.0` file and, for AG evaluator
runs, a separate `measurement-profile/v0.5.0` file.

## Workflow

1. Select evaluator manifests and laws from the current registry.
2. Select one external MeasurementProfile artifact for the run.
3. Record `basisLedger` entries and policy basis refs.
4. Validate with `archsig measurement-profile --measurement-profile <profile> --out <report>`.
5. Validate with `archsig law-policy --law-policy <policy> --measurement-profile <profile> --out <report>`.
6. Run `archsig analyze --archmap <archmap> --law-policy <policy> --measurement-profile <profile> --out-dir <run-dir>`.

Gate decisions belong in `archsig gate` policy, not in `analyze` flags.
