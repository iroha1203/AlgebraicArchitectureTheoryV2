# ArchSig Command Guide

この文書は `archsig` の主要 command と最小例をまとめる。研究上の解釈や非主張境界は
[Artifacts And Boundaries](artifacts-and-boundaries.md) を参照する。

## Scan

Lean repository を scan する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- \
  --root . \
  --policy signature-policy.json \
  --runtime-edges runtime-edges.json \
  --out .lake/sig0.json
```

`--policy` と `--runtime-edges` は任意である。省略した metric は placeholder 0 を出す場合があるが、
`metricStatus.<axis>.measured = false` として未評価を保持する。

Python repository を scan する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- \
  --language python \
  --root path/to/repository \
  --source-root src \
  --package-root src \
  --out .lake/python-sig0.json
```

Python scan は `componentKind = "python-module"` を出し、標準 `ast` parser で
`import` / `from ... import ...` を抽出する。dynamic import、plugin loading、
framework convention は未評価 boundary として残す。

## Validate

既存 Sig0 JSON を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- validate \
  --input .lake/sig0.json \
  --out .lake/sig0-validation.json \
  --universe-mode local-only
```

`validate` は source file を再 scan しない。入力 JSON の component、edge、metric status から
duplicate-free component list、local edge closure、external target、policy metric status を検査する。

## Snapshot / Diff

revision snapshot を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- snapshot \
  --input .lake/signature-current/sig0.json \
  --validation-report .lake/signature-current/validation.json \
  --repo-owner example \
  --repo-name service \
  --revision-sha "$(git rev-parse HEAD)" \
  --revision-ref "$(git rev-parse --abbrev-ref HEAD)" \
  --revision-branch main \
  --scanned-at "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --policy-path signature-policy.json \
  --extractor-output-path .lake/signature-current/sig0.json \
  --tag ci \
  --out .lake/signature-current/snapshot.json
```

before / after の snapshot から diff report を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- signature-diff \
  --before-snapshot .lake/signature-previous/snapshot.json \
  --after-snapshot .lake/signature-current/snapshot.json \
  --before-sig0 .lake/signature-previous/sig0.json \
  --after-sig0 .lake/signature-current/sig0.json \
  --pr-metadata .lake/pr-metadata-123.json \
  --out .lake/signature-current/diff-report.json
```

`signature-diff` は `diff` alias でも呼び出せる。

## AIR / Report

AIR v0 を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- air \
  --sig0 .lake/signature-current/sig0.json \
  --validation .lake/signature-current/validation.json \
  --diff .lake/signature-current/diff-report.json \
  --pr-metadata .lake/pr-metadata-123.json \
  --law-policy signature-policy.json \
  --framework-adapter framework-adapter.json \
  --out .lake/signature-current/air.json
```

AIR の参照整合性を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- validate-air \
  --input .lake/signature-current/air.json \
  --out .lake/signature-current/air-validation.json
```

`--strict-measured-evidence` を付けると、evidence refs を持たない measured claim を
warning ではなく failure として扱う。

Theorem precondition check を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- theorem-check \
  --air .lake/signature-current/air.json \
  --out .lake/signature-current/theorem-check.json
```

Feature Extension Report を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- feature-report \
  --air .lake/signature-current/air.json \
  --out .lake/signature-current/feature-report.json
```

PR comment summary を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- pr-comment \
  --feature-report .lake/signature-current/feature-report.json \
  --policy-decision .lake/signature-current/policy-decision.json \
  --out .lake/signature-current/pr-comment-summary.md
```

## Policy / Registry / Schema

organization policy と policy decision を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- organization-policy \
  --out .lake/signature-current/organization-policy-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- policy-decision \
  --feature-report .lake/signature-current/feature-report.json \
  --policy organization-policy.json \
  --out .lake/signature-current/policy-decision.json
```

B7 report artifact retention manifest を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- report-artifacts \
  --input report-artifacts.json \
  --out .lake/signature-current/report-artifacts-validation.json
```

B8 extension registry を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- law-policy-templates \
  --out .lake/signature-current/law-policy-templates-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- custom-rule-plugins \
  --out .lake/signature-current/custom-rule-plugins-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- measurement-units \
  --out .lake/signature-current/measurement-units-validation.json
```

Architecture Dynamics 共通 measurement contract を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- dynamics-measurements \
  --input tools/archsig/tests/fixtures/minimal/dynamics_measurement_contract.json \
  --out .lake/signature-current/dynamics-measurements-validation.json
```

PR force report の canonical fixture を出力し、既存 artifact を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- pr-force-report \
  --fixture \
  --out .lake/signature-current/pr-force-report.json

cargo run --manifest-path tools/archsig/Cargo.toml -- pr-force-report \
  --input tools/archsig/tests/fixtures/minimal/pr_force_report.json \
  --out .lake/signature-current/pr-force-report-validation.json
```

Architecture Dynamics metrics report の canonical fixture を出力し、既存 artifact を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- architecture-dynamics-metrics \
  --fixture \
  --out .lake/signature-current/architecture-dynamics-metrics-report.json

cargo run --manifest-path tools/archsig/Cargo.toml -- architecture-dynamics-metrics \
  --input tools/archsig/tests/fixtures/minimal/architecture_dynamics_metrics_report.json \
  --out .lake/signature-current/architecture-dynamics-metrics-validation.json
```

B5 repair / synthesis artifact を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- repair-registry \
  --input repair-rule-registry.json \
  --out .lake/signature-current/repair-registry-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- synthesis-constraints \
  --input tools/archsig/tests/fixtures/minimal/synthesis_constraints_candidate.json \
  --out .lake/signature-current/synthesis-constraints.json

cargo run --manifest-path tools/archsig/Cargo.toml -- no-solution-certificate \
  --input tools/archsig/tests/fixtures/minimal/no_solution_certificate_valid.json \
  --out .lake/signature-current/no-solution-certificate-validation.json
```

B9 schema compatibility を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- reported-axes-catalog \
  --out .lake/signature-current/reported-axes-catalog.json

cargo run --manifest-path tools/archsig/Cargo.toml -- schema-compatibility \
  --before .lake/signature-previous/feature-report.json \
  --after .lake/signature-current/feature-report.json \
  --out .lake/signature-current/schema-compatibility.json
```

## Baseline / Suppression

baseline/current の Feature Extension Report と policy decision report を比較する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- baseline-suppression \
  --baseline-feature-report .lake/signature-baseline/feature-report.json \
  --current-feature-report .lake/signature-current/feature-report.json \
  --baseline-policy-decision .lake/signature-baseline/policy-decision.json \
  --current-policy-decision .lake/signature-current/policy-decision.json \
  --retention-manifest .lake/signature-current/report-artifacts.json \
  --suppression .lake/signature-current/suppression.json \
  --out .lake/signature-current/baseline-suppression.json
```

## Dataset

GitHub API の PR detail / files / reviews JSON から PR metadata を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- pr-metadata \
  --pull-request github-pr.json \
  --files github-pr-files.json \
  --reviews github-pr-reviews.json \
  --review-threads github-review-threads.json \
  --out pr-metadata.json
```

before / after の Sig0 output と PR metadata から empirical dataset record を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- dataset \
  --before .lake/sig0-base.json \
  --after .lake/sig0-head.json \
  --pr-metadata pr-metadata.json \
  --after-role head \
  --out .lake/empirical-dataset-v0.json
```

PR history、Feature Extension Report、outcome observation を join する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- pr-history-dataset \
  --pull-request github-pr.json \
  --files github-pr-files.json \
  --reviews github-pr-reviews.json \
  --review-threads github-review-threads.json \
  --signature-artifact base=.lake/sig0-base.json \
  --signature-artifact head=.lake/sig0-head.json \
  --feature-report-artifact head=.lake/signature-current/feature-report.json \
  --out .lake/pr-history-dataset.json

cargo run --manifest-path tools/archsig/Cargo.toml -- feature-extension-dataset \
  --pr-history .lake/pr-history-dataset.json \
  --feature-report .lake/signature-current/feature-report.json \
  --theorem-check-report .lake/signature-current/theorem-check.json \
  --out .lake/feature-extension-dataset.json

cargo run --manifest-path tools/archsig/Cargo.toml -- outcome-linkage-dataset \
  --feature-dataset .lake/feature-extension-dataset.json \
  --outcome outcome-observation.json \
  --out .lake/outcome-linkage-dataset.json
```

## Operational Feedback

B10 daily ledger を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- report-outcome-daily-ledger \
  --outcome-linkage .lake/outcome-linkage-dataset.json \
  --drift-ledger .lake/architecture-drift-ledger.json \
  --generated-at 2026-05-05T00:00:00Z \
  --window-start 2026-05-04T00:00:00Z \
  --window-end 2026-05-05T00:00:00Z \
  --out .lake/report-outcome-daily-ledger.json
```

Canonical B10 artifact を出力する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- calibration-review-record \
  --out .lake/calibration-review-record.json

cargo run --manifest-path tools/archsig/Cargo.toml -- team-threshold-policy \
  --out .lake/team-threshold-policy.json

cargo run --manifest-path tools/archsig/Cargo.toml -- ownership-boundary-monitor \
  --out .lake/ownership-boundary-monitor.json

cargo run --manifest-path tools/archsig/Cargo.toml -- repair-adoption-record \
  --out .lake/repair-adoption-record.json

cargo run --manifest-path tools/archsig/Cargo.toml -- incident-correlation-monitor \
  --out .lake/incident-correlation-monitor.json

cargo run --manifest-path tools/archsig/Cargo.toml -- hypothesis-refresh-cycle \
  --out .lake/hypothesis-refresh-cycle.json
```

これらは empirical / operational feedback artifact であり、因果証明、formal claim
promotion、theorem precondition discharge、extractor completeness、architecture
lawfulness を結論しない。詳しい読み方は
[Operational Feedback](operational-feedback.md) を参照する。

## Other Artifacts

Workflow 単位の relation complexity observation を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- relation-complexity \
  --input relation-complexity-candidates.json \
  --out relation-complexity-observation.json
```
