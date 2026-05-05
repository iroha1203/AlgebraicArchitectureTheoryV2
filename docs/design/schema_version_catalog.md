# B9/B10 schema version catalog

Lean status: `empirical hypothesis` / `tooling validation`.

Issue: [#613](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/613)

この文書は、Phase B9 の schema version 名、互換性 policy、B10 operational feedback
artifact、後続 checker が参照する最小 skeleton を固定する。canonical fixture は
`tools/archsig/tests/fixtures/minimal/schema_version_catalog.json` であり、Rust 側の
`static_schema_version_catalog` と一致することを test で確認する。

## Catalog

| artifact | schema version | role | status | 後続 Issue |
| --- | --- | --- | --- | --- |
| Architecture Signature artifact | `archsig-sig0-v0` | extractor output | implemented | なし |
| AIR | `aat-air-v0` | intermediate representation | implemented | [#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608), [#609](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/609) |
| Feature Extension Report | `feature-extension-report-v0` | review output | implemented | [#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608), [#609](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/609) |
| Obstruction Witness | `obstruction-witness-v0` | embedded witness | implemented | [#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608), [#610](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/610) |
| Architecture Drift Ledger | `architecture-drift-ledger-v0` | batch history output | implemented | [#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608), [#610](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/610) |
| Detectable values / reported axes catalog | `detectable-values-reported-axes-catalog-v0` | axis catalog | implemented | [#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608) |
| Report outcome daily ledger | `report-outcome-daily-ledger-v0` | operational feedback output | implemented | [#620](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/620) |

## Compatibility Policy

Compatibility policy の schema version は `schema-compatibility-policy-v0` である。
この policy は次を区別して扱う。

- `field_mapping`: renamed / removed / split / merged field を explicit mapping として扱う。
- `deprecated_fields`: replacement、removal phase、reader behavior を保持する。
- `new_required_assumptions`: theorem、coverage、projection、exactness、review assumption を missing / undischarged として表面化する。
- `non_conclusions`: migration 後も削除せず、同等またはより強い boundary として保持する。
- `coverage_exactness_boundary`: layer / axis ごとの measurement boundary、coverage assumptions、exactness assumptions を保持する。

後続 checker の最小 required checks は次である。

- `schemaVersion` が catalog に存在する。
- renamed / removed field の field mapping が explicit である。
- deprecated field が replacement または removal behavior を持つ。
- new required assumptions が evidence なしに discharge されない。
- non-conclusions が保存または強化される。
- coverage / exactness metadata が migration で落ちない。

## AIR / Feature Extension Report metadata

Issue: [#609](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/609)

`aat-air-v0` と `feature-extension-report-v0` は B9 compatibility policy への artifact-local
trace として `schemaCompatibility` を持つ。

AIR metadata は次を固定する。

- `coverage.layers[].extractionScope`
- `coverage.layers[].exactnessAssumptions`
- `coverage.layers[].unsupportedConstructs`
- `claims[].missingPreconditions`
- `claims[].nonConclusions`

Feature Extension Report metadata は次を固定する。

- `coverageGaps[].nonConclusions`
- `theoremPreconditionChecks[].missingPreconditions`
- `unsupportedConstructs`
- `nonConclusions`

AIR validation は `schemaCompatibility` がある場合に、coverage / exactness boundaries、
new required assumptions、theorem bridge preconditions、formal claim promotion を禁止する
non-conclusions が落ちていないことを検査する。metadata がない legacy AIR v0 fixture は
backward-compatible input として読むが、新しく生成する AIR / Feature Extension Report は
metadata を出力する。

## Migration / compatibility checker

Issue: [#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608)

`archsig schema-compatibility --before <artifact.json> --after <artifact.json>` は
`schema-compatibility-check-report-v0` を出力する。catalog の `schemaVersion` 照合に加え、
artifact-local `schemaCompatibility` metadata がある場合は次を別軸で検査する。

- field mappings が explicit に保持されていること。
- deprecated fields が replacement または reader behavior と removal phase を持つこと。
- new required assumptions が missing / undischarged として表面化し、formal claim を暗黙に
  discharge しないこと。
- non-conclusions が保存または強化され、semantic preservation、extractor completeness、
  Lean theorem / formal claim promotion の boundary が落ちないこと。
- coverage / exactness boundary が migration で落ちないこと。

同一 `schemaVersion` で `schemaCompatibility` metadata を持たない B0-B8 artifact は、
backward-compatible input として warning 付きで受け入れる。schemaVersion 変更や metadata
欠落を伴う migration は `requiresMigration` として報告し、formal claim promotion を
防ぐ guardrail 欠落は `blockedFormalClaimPromotion` として報告する。

## Obstruction Witness / Architecture Drift Ledger metadata

Issue: [#610](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/610)

`obstruction-witness-v0` は、Feature Extension Report の
`introducedObstructionWitnesses` と同じ witness field set を standalone artifact として
versioning する。target field は `witnessId`, `layer`, `kind`, `extensionRole`,
`extensionClassification`, `evidence`, `theoremReference`, `claimLevel`,
`claimClassification`, `measurementBoundary`, `nonConclusions`, `repairCandidates` である。
`schemaCompatibility` は evidence refs、claim classification、measurement boundary、
non-conclusions を別 boundary として保持し、private / missing / unmeasured evidence を
`measuredZero` に丸めない。

`architecture-drift-ledger-v0` は、daily batch や scheduled scan の drift entry を
versioning する。stable grouping key (`subjectRef`, `witnessFingerprint`, `policyRef`),
`aggregationWindow`, `measurementBoundary`, `evidenceRefs`, `status`, `suppression`,
`retentionManifestRef`, `baselineRef`, `suppressionWorkflowRefs`, `nonConclusions` が
compatibility boundary である。retention / baseline / suppression metadata は ledger
schema version と結びつく operational metadata であり、formal proof state ではない。

Canonical fixtures:

```text
tools/archsig/tests/fixtures/minimal/obstruction_witness.json
tools/archsig/tests/fixtures/minimal/architecture_drift_ledger.json
```

`archsig schema-compatibility` の fixture test は、private / missing / unmeasured evidence
boundary が `measuredZero` へ変更された場合に `requiresMigration` として報告することを
固定する。

## Detectable values / reported axes catalog

Issue: [#612](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/612)

`detectable-values-reported-axes-catalog-v0` は、report に出す axis と benchmark suite の
freeze boundary を同じ artifact として versioning する。canonical fixture は
`tools/archsig/tests/fixtures/minimal/detectable_values_reported_axes_catalog.json` であり、
`ReportedAxesCatalogEntryV0` と `BenchmarkSuiteFixtureV0` を Rust 側の static builder と
一致させる。

Catalog entry は次を保持する。

- `axisId`, `layer`, `valueType`
- `reportedIn`
- `allowedMeasurementBoundaries`
- `defaultMeasurementBoundary`
- evidence requirements
- theorem refs
- compatibility notes
- non-conclusions

Benchmark suite freeze は `benchmarkSuiteVersion = archsig-benchmark-suite-v0` として、
canonical AIR fixtures の expected measurement boundary を固定する。対象には static split、
runtime measured zero / measured nonzero / unmeasured、semantic unmeasured、
generated-change metadata gap を含める。

Axis の追加・改名・削除・measurement boundary 変更は backward-compatible な変更として
黙って受け入れない。`archsig schema-compatibility` は
`detectable-values-reported-axes-catalog-v0` 同士の比較で、追加、削除、改名候補、
`allowedMeasurementBoundaries` または `defaultMeasurementBoundary` の変更を
`requiresMigration` として報告する。特に `measuredZero`, `measuredNonzero`,
`unmeasured`, `outOfScope` の区別は migration で失われてはならない。

## Report outcome daily ledger metadata

Issue: [#620](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/620)

`report-outcome-daily-ledger-v0` は、B6 の `outcome-linkage-dataset-v0` と B9 の
`architecture-drift-ledger-v0` を B10 の daily batch operational artifact として
蓄積する。schema は `aggregationWindow`, `sourceReportRefs`, `retention`,
`batches[].outcomeMetricSummaries`, `batches[].missingPrivateUnmeasuredBoundaries`,
`analysisMetadata`, `nonConclusions` を保持する。

Daily batch は source report refs と retention manifest ref を明示し、review outcome、
follow-up fix、rollback、incident affected component count、MTTR、drift ledger metric の
boundary count を保存する。`unavailable`, `private`, `missingOrPrivate`, `unmeasured`
は measured-zero evidence に丸めず、operational monitoring の exactness boundary として
残す。

Canonical fixture:

```text
tools/archsig/tests/fixtures/minimal/report_outcome_daily_ledger.json
```

CLI は次の形で outcome linkage dataset と Architecture Drift Ledger を join する。

```bash
archsig report-outcome-daily-ledger \
  --outcome-linkage outcome-linkage-dataset.json \
  --drift-ledger architecture-drift-ledger.json \
  --generated-at 2026-05-05T00:00:00Z \
  --window-start 2026-05-04T00:00:00Z \
  --window-end 2026-05-05T00:00:00Z \
  --out report-outcome-daily-ledger.json
```

この artifact は empirical / operational signal であり、report warning と incident /
rollback / MTTR の因果関係、schema migration の意味保存、Lean theorem claim、
extractor completeness、architecture lawfulness を結論しない。

## Non-Conclusions

Schema migration は意味保存を主張しない。field mapping が通ることは、
artifact の数学的意味、Architecture lawfulness、Lean theorem claim、extractor completeness を
結論しない。

Compatibility pass は tooling validation であり、測定境界や exactness assumption を
明示的に運ぶための operational guardrail である。未測定の axis、coverage gap、
private / missing evidence は measured zero evidence ではない。
