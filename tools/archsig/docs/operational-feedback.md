# ArchSig Operational Feedback

B10 operational feedback artifact は、実運用 outcome を継続的に review するための
schema / fixture / guardrail である。現状の command は canonical artifact 出力と bounded
join を提供し、scheduler や外部 incident system からの自動収集までは行わない。

Lean status: `empirical hypothesis` / tooling output.

## Commands

Daily ledger を作る。

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

## Artifacts

| artifact | schemaVersion | 役割 |
| --- | --- | --- |
| Report outcome daily ledger | `report-outcome-daily-ledger-v0` | `outcome-linkage-dataset-v0` と `architecture-drift-ledger-v0` を aggregation window で join する。 |
| Calibration review record | `calibration-review-record-v0` | false positive / false negative review と metric calibration の入力を保持する。 |
| Team threshold policy | `team-threshold-policy-v0` | team-specific threshold tuning policy を保持する。 |
| Ownership boundary monitor | `ownership-boundary-monitor-v0` | ownership / boundary erosion monitoring を保持する。 |
| Repair adoption record | `repair-adoption-record-v0` | repair suggestion adoption tracking を保持する。 |
| Incident correlation monitor | `incident-correlation-monitor-v0` | incident / rollback / MTTR correlation monitoring を保持する。 |
| Hypothesis refresh cycle | `hypothesis-refresh-cycle-v0` | empirical hypothesis refresh cycle を保持する。 |

## Reading Rules

B10 artifact は operational outcome、calibration、threshold、ownership、repair adoption、
incident correlation、hypothesis refresh を empirical artifact として保存する。

- unavailable / private / missing / unmeasured outcome data を measured-zero evidence に丸めない。
- reviewer decision は threshold / CI policy の empirical calibration input として読む。
- team threshold は formal theorem precondition discharge ではない。
- ownership / boundary erosion signal は repair correctness を証明しない。
- repair adoption decision は global flatness preservation や cost improvement を証明しない。
- incident / rollback / MTTR correlation は causality proof ではない。
- retained hypothesis は Lean theorem claim ではない。

## Non-Conclusions

B10 artifact は次を結論しない。

- report warning と incident / rollback / MTTR の因果関係。
- formal claim promotion。
- theorem precondition discharge。
- extractor completeness。
- architecture lawfulness。
- semantic preservation。
