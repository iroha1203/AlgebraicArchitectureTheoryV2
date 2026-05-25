# FieldSig Operational Feedback Handoff

Operational feedback artifacts moved to FieldSig. ArchSig no longer owns CLI commands, fixtures, schema catalog entries, or public exports for daily ledgers, calibration records, team thresholds, ownership monitoring, repair adoption, incident correlation, hypothesis refresh, field snapshots, dynamics metrics, or governance artifacts.

Use FieldSig instead:

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- calibration-review-record \
  --out .fieldsig/operational/calibration-review-record.json

cargo run --manifest-path tools/fieldsig/Cargo.toml -- report-outcome-daily-ledger \
  --outcome-linkage .fieldsig/operational/outcome-linkage-dataset.json \
  --drift-ledger .fieldsig/operational/architecture-drift-ledger.json \
  --generated-at 2026-05-05T00:00:00Z \
  --out .fieldsig/operational/report-outcome-daily-ledger.json
```

Operational correlation remains empirical evidence. It is not causal proof, forecast correctness, or a Lean theorem witness.
