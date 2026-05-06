# Schema Compatibility

Schema compatibility は、artifact evolution で claim boundary、coverage、exactness、
non-conclusions を落とさないための policy である。

## Version policy

```text
schema-compatibility-policy-v0 :=
  artifactId
  + schemaVersion
  + fieldMappings
  + deprecatedFields
  + requiredAssumptions
  + coverageExactnessBoundaries
  + nonConclusions
```

schema version の更新は、field shape だけでなく claim boundary の migration として扱う。

## Required checks

```text
required checks:
  schemaVersion exists in catalog
  field mappings are explicit
  deprecated fields have replacement / reader behavior
  new required assumptions are not silently discharged
  non-conclusions are preserved or strengthened
  coverage / exactness metadata is preserved
```

## Compatibility outcomes

```text
compatible
requiresMigration
notComparable
blockedFormalClaimPromotion
```

`notComparable` は失敗ではなく、比較境界である。schema、unit、projection、coverage が
揃わない場合は、delta を作らない。

## Catalog

Schema catalog は次の artifact family を含む。

```text
archsig-sig0-v0
aat-air-v0
feature-extension-report-v0
obstruction-witness-v0
architecture-drift-ledger-v0
detectable-values-reported-axes-catalog-v0
report-outcome-daily-ledger-v0
calibration-review-record-v0
team-threshold-policy-v0
ownership-boundary-monitor-v0
repair-adoption-record-v0
incident-correlation-monitor-v0
hypothesis-refresh-cycle-v0
pr-force-report-v0
signature-trajectory-report-v0
architecture-dynamics-metrics-report-v0
```

現行の `static_schema_version_catalog` に含まれる Architecture Dynamics artifact は
`pr-force-report-v0`、`signature-trajectory-report-v0`、
`architecture-dynamics-metrics-report-v0` である。
`architecture-field-snapshot-v0` と `operation-proposal-log-v0` は CLI / fixture / validator が
あるが、static schema catalog の catalog family にはまだ載せない。

詳細な catalog と実装 status は `docs/design/schema_version_catalog.md` と
`tools/archsig/src/schema_catalog.rs` で管理する。

## Migration rule

schema migration では、古い artifact の non-conclusion が消えた場合、migration は
safe ではない。弱い boundary を強い claim に変える migration は blocked とする。
