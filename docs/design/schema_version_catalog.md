# B9 schema version catalog

Lean status: `empirical hypothesis` / `tooling validation`.

Issue: [#613](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/613)

この文書は、Phase B9 の schema version 名、互換性 policy、後続 checker が参照する
最小 skeleton を固定する。canonical fixture は
`tools/archsig/tests/fixtures/minimal/schema_version_catalog.json` であり、Rust 側の
`static_schema_version_catalog` と一致することを test で確認する。

## Catalog

| artifact | schema version | role | status | 後続 Issue |
| --- | --- | --- | --- | --- |
| Architecture Signature artifact | `archsig-sig0-v0` | extractor output | implemented | なし |
| AIR | `aat-air-v0` | intermediate representation | implemented | [#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608), [#609](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/609) |
| Feature Extension Report | `feature-extension-report-v0` | review output | implemented | [#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608), [#609](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/609) |
| Obstruction Witness | `obstruction-witness-v0` | embedded witness | schema skeleton | [#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608), [#610](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/610) |
| Architecture Drift Ledger | `architecture-drift-ledger-v0` | batch history output | schema skeleton | [#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608), [#610](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/610) |
| Detectable values / reported axes catalog | `detectable-values-reported-axes-catalog-v0` | axis catalog | schema skeleton | [#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608), [#612](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/612) |

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

## Non-Conclusions

Schema migration は意味保存を主張しない。field mapping が通ることは、
artifact の数学的意味、Architecture lawfulness、Lean theorem claim、extractor completeness を
結論しない。

Compatibility pass は tooling validation であり、測定境界や exactness assumption を
明示的に運ぶための operational guardrail である。未測定の axis、coverage gap、
private / missing evidence は measured zero evidence ではない。
