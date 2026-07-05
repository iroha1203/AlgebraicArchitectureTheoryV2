---
name: law-policy-creater
description: Create law-policy/v0.5.0 files for current ArchSig measurement runs.
---

# LawPolicy Creater

Use this skill to create a `law-policy/v0.5.0` file.

## Workflow

1. Select evaluator manifests and laws from the current registry.
2. Select measurement profiles and policies needed by the run.
3. Record basis refs and non-conclusions.
4. Validate with `archsig law-policy --input <policy> --out <report>`.
5. Run `archsig analyze --archmap <archmap> --law-policy <policy> --out-dir <run-dir>`.

Gate decisions belong in `archsig gate` policy, not in `analyze` flags.
