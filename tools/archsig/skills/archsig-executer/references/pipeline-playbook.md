# ArchSig Pipeline Playbook

Use this playbook to select the right pipeline for the user's request.

## Decision Table

| User asks for | Run |
| --- | --- |
| "scan this repo", "create Sig0", "architecture signature" | Core signature pipeline |
| "validate this Sig0" | Sig0 validation only |
| "compare revisions", "PR signature diff" | Snapshot and diff pipeline |
| "validate this ArchMap" | ArchMap validation |
| "turn ArchMap into AIR" | ArchMap review pipeline |
| "theorem preconditions" | ArchMap review pipeline through `theorem-check` |
| "feature report from ArchMap" | ArchMap review pipeline through `feature-report` |
| "ForecastCone from ArchMap" | ArchMap to SFT pipeline through `forecast-cone-skeleton` |
| "ConsequenceEnvelope from ArchMap" | ArchMap to SFT pipeline through `consequence-envelope` |
| "calibration hook" | `forecast-calibration-hook` after forecast artifacts exist, or skeleton if explicitly requested |
| "diagnose the result" | Generate missing artifacts, then hand off to `$arch-doctor` |

## Core Signature Pipeline

Run when the user wants repository telemetry:

```text
scan
  -> validate
```

Minimum outputs:

- `.archsig/signature/sig0.json`
- `.archsig/signature/sig0-validation.json`

Do not interpret placeholder numeric zero as low risk. Read metric status fields.

## Snapshot And Diff Pipeline

Run when before/after artifacts exist or can be generated:

```text
previous scan + validation + snapshot
current scan + validation + snapshot
  -> signature-diff
```

Required inputs:

- before Sig0
- after Sig0
- before snapshot
- after snapshot
- PR metadata when available

If previous artifacts are missing, ask whether to generate them from another checkout/ref or skip diff.

## ArchMap Review Pipeline

Run after an ArchMap JSON exists:

```text
archmap
  -> air-from-archmap
  -> validate-air
  -> theorem-check
  -> feature-report
```

Read outputs as review artifacts:

- validation success is not semantic preservation
- AIR projection is not Lean proof
- theorem-check is precondition status, not proof discharge
- feature report is a review summary, not an automatic merge decision

## ArchMap To SFT Pipeline

Run when the user wants future evolution artifacts:

```text
archmap-sft-input
  -> forecast-cone-skeleton
  -> consequence-envelope
```

Read outputs as bounded forecast surfaces:

- operation support estimate is candidate support, not forecast result
- forecast cone skeleton is not a point prediction or probability distribution
- consequence envelope is a report projection, not causal proof

## Calibration Hook Pipeline

Run when forecast items need later comparison against observed outcomes:

```text
forecast-calibration-hook
```

If observed artifact refs are not available, create only a skeleton when explicitly requested. Otherwise ask for observed refs.

## Execution Discipline

- Run commands in order.
- Stop after the first failed command unless the user asks for best-effort collection.
- Do not create downstream artifacts from stale or missing upstream artifacts.
- Summarize generated paths and any validation failures.
- Hand off to `$arch-doctor` for interpretation, recommendation, or forecast analysis.
