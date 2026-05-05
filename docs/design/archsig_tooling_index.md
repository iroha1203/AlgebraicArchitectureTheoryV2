# ArchSig tooling index

Lean status: `empirical hypothesis` / `tooling validation`.

この文書は、ArchSig tooling の schema、CLI、fixture、non-conclusion boundary を追跡する
tooling-side index である。数学的な定義・定理候補・非目標は
[`aat_v2_mathematical_design.md`](../aat_v2_mathematical_design.md) に置き、Lean status と
Issue 対応は [`proof_obligations.md`](../proof_obligations.md) に置く。

ここに記載する tooling artifact は、CI / PR review / empirical validation の入力または
出力であり、artifact の存在だけで architecture lawfulness、Lean theorem claim、設計判断の
自動承認を結論しない。

## B7 CI / PR review integration

Parent Issue: [#571](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/571)

B7 は Feature Extension Report を日常の PR review に接続する運用 layer である。tool は
設計判断を自動承認しない。CI fail は policy が明示した required axis と missing
precondition に基づく運用判断であり、theorem の自動結論ではない。

### Organization policy

Issue: [#576](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/576)

`organization-policy-v0` は CI decision support schema である。次を保持する。

- `policy_id`
- `policy_version`
- `scope`
- required axes
- allowed unmeasured gaps
- required theorem preconditions
- non-conclusions

validation は unknown axis、unknown claim level、missing scope、invalid unmeasured
allowance、precondition refs、CI / lawfulness / unmeasured / missing-precondition の
non-conclusion boundary を検査する。

CLI:

```bash
archsig organization-policy
```

出力 schema:

```text
organization-policy-validation-report-v0
```

Canonical fixture は `cargo test --manifest-path tools/archsig/Cargo.toml` で固定する。

Non-conclusions:

- policy pass は architecture lawfulness を結論しない。
- policy pass は Lean theorem claim を結論しない。
- allowed unmeasured gap は measured-zero evidence ではない。
- missing precondition は policy 設定だけでは discharge されない。

### Report artifact retention

Issue: [#575](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/575)

`report-artifact-retention-manifest-v0` は、B7 の report artifact retention schema である。
Feature Extension Report、theorem precondition check report、policy decision report、
PR comment summary の artifact ref または missing/private gap を保持する。

各 artifact ref は次を保持する。

- repository
- PR number
- commit sha
- schema version
- policy version
- generated_at
- retention scope
- visibility

retention metadata は baseline comparison、suppression workflow、Architecture Drift Ledger、
reviewer output refs から参照できる。

CLI:

```bash
archsig report-artifacts
```

出力 schema:

```text
report-artifact-retention-validation-report-v0
```

Canonical fixture は `cargo test --manifest-path tools/archsig/Cargo.toml` で固定する。

Non-conclusions:

- retention pass は architecture lawfulness を結論しない。
- retention pass は Lean theorem claim を結論しない。
- private / missing artifact は measured-zero evidence ではない。
- PR comment summary は proof certificate ではない。

### Warn / fail / advisory policy decision

Issue: [#573](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/573)

`policy-decision-report-v0` は、Feature Extension Report と `organization-policy-v0` から
CI / PR review 向けの warn / fail / advisory decision を生成する schema である。

入力:

- Feature Extension Report
- organization policy

decision boundary:

- `fail` は required axis の未測定・測定境界違反・閾値違反、または required theorem
  precondition の欠落に限定する。
- `warn` は coverage gap、allowed unmeasured gap、非 required な測定不足を reviewer に残す。
- `advisory` は measured nonzero witness や obstruction witness を review signal として示す。

CLI:

```bash
archsig policy-decision --feature-report feature-report.json --policy organization-policy.json
```

出力 schema:

```text
policy-decision-report-v0
```

Canonical fixture は `cargo test --manifest-path tools/archsig/Cargo.toml` で固定する。

Non-conclusions:

- policy decision は Lean theorem ではない。
- policy decision は architecture lawfulness を承認しない。
- advisory signal は repair success evidence ではない。
- unmeasured axis は measured-zero risk として扱わない。

### GitHub Checks / PR comment output

Issue: [#574](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/574)

`pr-comment-summary-v0` は、Feature Extension Report と任意の
`policy-decision-report-v0` を GitHub Checks / PR comment 向け Markdown に写す
reviewer-facing summary artifact である。CI 判定そのものは `policy-decision-report-v0`
に残し、PR comment は Level 1 / Level 2 / Level 3 の読み分けを固定する。

表示境界:

- Level 1 は split status、claim classification、top witnesses、required action、
  warn / fail / advisory status を出す。
- Level 2 は changed components、witness evidence、runtime summary、coverage gaps を出す。
- Level 3 は theorem package refs、discharged / missing assumptions、exactness assumptions、
  non-conclusions を出す。

CLI:

```bash
archsig pr-comment --feature-report feature-report.json --policy-decision policy-decision.json
```

出力 artifact:

```text
pr-comment-summary-v0 Markdown
```

Canonical fixture は `cargo test --manifest-path tools/archsig/Cargo.toml` で固定する。

Non-conclusions:

- PR comment summary は architecture lawfulness を承認しない。
- PR comment summary は Lean theorem proof ではない。
- unmeasured axis は measured-zero evidence ではない。
- advisory signal は repair success evidence ではない。

### Baseline comparison and suppression workflow

Issue: [#572](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/572)

`baseline-suppression-report-v0` は、baseline/current の Feature Extension Report と
policy decision report を比較し、PR review で必要な差分と risk disposition を保持する
tooling artifact である。

比較対象:

- newly introduced / eliminated obstruction witnesses
- coverage gap delta
- required axis status / measurement boundary / value delta
- policy decision fail / warn / advisory delta

suppression / accepted risk metadata は次を保持する。

- reason
- approved_by
- approved_at
- expires_at
- scope
- policy_ref
- witness_ref

CLI:

```bash
archsig baseline-suppression \
  --baseline-feature-report baseline-feature-report.json \
  --current-feature-report current-feature-report.json \
  --baseline-policy-decision baseline-policy-decision.json \
  --current-policy-decision current-policy-decision.json \
  --retention-manifest report-artifacts.json \
  --suppression suppression.json
```

出力 schema:

```text
baseline-suppression-report-v0
```

Canonical fixture は `cargo test --manifest-path tools/archsig/Cargo.toml` で固定する。

Non-conclusions:

- baseline comparison は Lean theorem ではない。
- suppressed / accepted-risk witness は resolved witness ではない。
- private / missing baseline artifact は measured-zero evidence ではない。
- policy decision delta は architecture lawfulness を承認しない。

## B8 Extractor / policy ecosystem

Parent Issues:

- [#577](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/577)
- [#593](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/593)

B8 は non-Lean extractor と policy ecosystem を AIR / Feature Extension Report へ接続する
layer である。extractor は言語ごとの bounded subset、unsupported constructs、coverage
assumptions、projection rule を evidence として出し、Lean の `ComponentUniverse` 完全性とは
分離する。

### Adapter registry

Issue: [#598](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/598)

`adapter-registry-v0` は、language extractor、framework adapter、runtime / semantic
evidence adapter、policy adapter の evidence boundary を固定する tooling registry である。
registry entry は adapter id、adapter kind、source language / framework、
component / relation / evidence kind、projection rule、measured layer / axis、
coverage assumptions、exactness assumptions、unsupported constructs、
required inputs、output artifacts、theorem bridge preconditions、non-conclusions を持つ。

Python pilot の `python-import-graph-v0` は `language-extractor` entry として読む。
将来の framework-specific adapter、runtime / semantic evidence adapter、law policy template、
custom rule plugin は同じ registry boundary の下で AIR coverage と Feature Extension Report
へ trace する。registry entry の存在だけで Lean theorem claim、extractor completeness、
architecture lawfulness、runtime / semantic flatness は結論しない。

詳細 schema は [Adapter registry v0 schema](adapter_registry_schema.md) で管理する。

### Framework adapter fixture

Issue: [#599](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/599)

`framework-adapter-evidence-v0` は、特定 framework convention を bounded adapter evidence
として AIR へ渡す fixture schema である。初期 fixture は FastAPI の `APIRouter` route
decorator を `framework_route` evidence と `layer = "framework"` の relation に写す。
`archsig air --framework-adapter framework_adapter.json` は adapter artifact、route evidence、
framework coverage layer を AIR に追加し、Feature Extension Report は同じ layer の
coverage gap と unsupported constructs を表示する。

Canonical fixture は
`tools/archsig/tests/fixtures/python_imports/framework_adapter.json` で固定する。CLI test は
measured route relation と、dependency injection / middleware など adapter が扱わない
FastAPI convention を measured-zero にしない境界を検査する。

Non-conclusions:

- framework adapter output は framework runtime semantics の完全性を結論しない。
- route relation が測定されても未対応 convention は measured-zero evidence ではない。
- adapter confidence は Lean theorem claim や `ComponentUniverse` completeness の代替ではない。
- framework fixture は architecture lawfulness を結論しない。

### Law policy template registry

Issue: [#594](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/594)

`law-policy-template-registry-v0` は、boundary / abstraction / runtime protection などの
law policy template を selector assumptions と required evidence boundary 付きで固定する
tooling registry である。template は template id、対象 component kind、law / policy
family、selector semantics、selector assumptions、required evidence kinds、default
required axes、policy output artifacts、theorem bridge preconditions、non-conclusions を持つ。

CLI:

```bash
archsig law-policy-templates --input law_policy_templates.json
```

出力 schema:

```text
law-policy-template-registry-validation-report-v0
```

Canonical fixture は `tools/archsig/tests/fixtures/minimal/law_policy_templates.json` で固定する。
validation は template id の一意性、component kind / policy family / selector semantics、
selector assumptions、required evidence、output artifact、theorem bridge precondition、
non-conclusion boundary を検査する。

Non-conclusions:

- template application は architecture lawfulness を結論しない。
- template pass は Lean theorem claim を結論しない。
- unmeasured gap は measured-zero evidence ではない。
- selector match は extractor completeness を証明しない。

### Custom rule plugin registry

Issue: [#596](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/596)

`custom-rule-plugin-registry-v0` は、organization-specific rule や extractor extension を
AIR evidence / Feature Extension Report metadata に接続する trust boundary である。plugin は
plugin id、rule id、plugin kind、evidence kind、confidence、input / output contract、
coverage assumptions、permitted claim levels、formal claim promotion mode、theorem
precondition refs、required theorem preconditions、output artifacts、non-conclusions を持つ。

CLI:

```bash
archsig custom-rule-plugins --input custom_rule_plugins.json
```

出力 schema:

```text
custom-rule-plugin-registry-validation-report-v0
```

Canonical fixture は `tools/archsig/tests/fixtures/minimal/custom_rule_plugins.json` で固定する。
validation は plugin id / rule id の一意性、plugin kind / evidence kind / confidence /
claim level / promotion mode、input / output contract、coverage assumptions、output artifact、
non-conclusion boundary を検査する。`permittedClaimLevels` に `formal` を含める plugin は
`theoremPreconditionRefs` と `requiredTheoremPreconditions` を持つ必要があり、validation test は
これを欠いた overclaiming plugin を fail にする。

Non-conclusions:

- plugin output は architecture lawfulness を結論しない。
- plugin output は Lean theorem claim を結論しない。
- plugin evidence は unsupported gap を measured-zero evidence に変えない。
- formal claim promotion は theorem precondition checker の explicit preconditions を必要とする。

### Measurement unit registry

Issue: [#600](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/600)

`measurement-unit-registry-v0` は、monorepo / multi-service 環境で runtime / semantic
evidence を読む前に、repository root、service root、deployment unit、runtime evidence
source、semantic workflow source の境界を固定する tooling registry である。unit は unit id、
unit kind、repository root、任意の service root / deployment unit、component id kind、
selected component refs、runtime / semantic evidence sources、coverage assumptions、
unsupported constructs、output artifacts、non-conclusions を持つ。

runtime / semantic evidence adapter boundary は adapter id、adapter kind、
measurement unit refs、measured layer、evidence kind、projection rule、coverage /
exactness assumptions、unsupported constructs、theorem bridge preconditions、
non-conclusions を持つ。これにより、runtime trace、service mesh、log、manual workflow、
contract test、semantic diagram の source boundary を AIR coverage / Feature Extension
Report の coverage gap へ trace する。

CLI:

```bash
archsig measurement-units --input measurement_units.json
```

出力 schema:

```text
measurement-unit-registry-validation-report-v0
```

Canonical fixture は `tools/archsig/tests/fixtures/minimal/measurement_units.json` で固定する。
validation は repository root / service root / deployment unit を collapse せず、adapter の
`measurementUnitRefs` が selected unit へ解決すること、coverage / exactness assumptions と
unsupported constructs が report へ trace 可能な形で残ることを検査する。

Non-conclusions:

- selected measurement unit は global architecture completeness を結論しない。
- selected measurement unit は Lean `ComponentUniverse` completeness を結論しない。
- runtime / semantic adapter coverage gap は measured-zero evidence ではない。
- private / missing evidence source は明示的に供給されるまで unmeasured のままである。

### Python component policy

Issues:

- [#581](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/581)
- [#582](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/582)
- [#579](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/579)
- [#578](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/578)

Python extractor の最小 component kind は `python-module` である。component id は
package root から見た importable module 名とし、policy selector は
`componentIdKind = "python-module"` でこの id を参照する。

Root policy:

- repository root: checkout と artifact path の基準。
- source root: scan 対象 file を制限する file system 境界。
- package root: module id 正規化と local import 解決の境界。

Edge policy:

- package root 内で解決できる `import` / `from ... import ...` は local module edge。
- package root 外、標準 library、installed dependency、unresolved target は external dependency edge。
- namespace package は明示された package root 群に属する file だけを local component として測る。
- `tests/` や `test_*.py` は既定で `python-module` に含め、production / test の区別は policy group で扱う。

AIR normalization:

- Python Sig0 artifact は `archsig air` で `aat-air-v0` に正規化できる。
- local module は `kind = "python-module"`、外部 dependency target は `kind = "external-dependency"` component として AIR relation refs を解決する。
- static relation の `extractionRule` は `python-import-graph-v0`、対応する evidence kind は `python_import` として保持する。
- static coverage は Python `ast` import/from scan と package-root normalization の exactness assumption を記録する。
- `unsupportedConstructs` は Sig0 data model で `kind`、`path`、任意の `line` / `evidence`、`reason` を持つ boundary record として保持し、AIR static coverage と Feature Extension Report の coverage gap へ写す。
- theorem precondition checker は Python import graph を tooling evidence として扱い、Python AIR に formal claim を追加しても Lean `ComponentUniverse` bridge precondition なしでは `FORMAL_PROVED` に昇格しない。

Unsupported construct taxonomy:

- `dynamic-import`: `__import__` / `importlib.import_module` による import target は静的 import edge として測定しない。
- `plugin-loading`: entry point / plugin metadata による relation は runtime/package metadata evidence を別途必要とする。
- `framework-convention`: Django / FastAPI / Celery / SQLAlchemy などの convention は framework-specific adapter の対象である。
- `generated-code`: 生成物は generator trace として扱い、通常 source evidence と同一視しない。
- `notebook`: notebook は execution order / hidden state を持つため notebook-specific extraction の対象である。

Canonical fixture / CLI validation:

- `tools/archsig/tests/fixtures/python_imports` は small Python package、relative import、external dependency、dynamic import、plugin loading、framework convention、generated code、notebook boundary を 1 つの canonical fixture として固定する。
- `tools/archsig/tests/cli.rs` は Python Sig0 output、AIR normalization、AIR validation、Feature Extension Report、Theorem Precondition Checker の CLI 経路を `cargo test --manifest-path tools/archsig/Cargo.toml` で検証する。
- fixture は measured static import graph と unmeasured / unsupported boundary の区別を固定するための tooling validation であり、Python runtime semantics や Lean `ComponentUniverse` bridge の完全性を結論しない。

関連 schema / docs:

- [AAT v2 tooling design](../aat_v2_tooling_design.md#phase-b8-extractor--policy-ecosystem)
- [ArchSig v0 design](archsig_design.md)
- [Adapter registry v0 schema](adapter_registry_schema.md)
- [boundary / abstraction policy v0 schema](boundary_abstraction_policy_schema.md#python-module-id-policy)
- [ComponentUniverse validation report v0](component_universe_validation_report.md)

Non-conclusions:

- Python component policy は extractor evidence であり、Lean theorem ではない。
- `python-module` scan は dynamic import、plugin loading、framework convention、generated code、notebook を完全捕捉しない。
- external dependency edge は local `ComponentUniverse` closure witness ではない。
- policy selector の一致は architecture lawfulness や実コード extractor completeness を結論しない。

## B9 Schema Standardization And Compatibility

Parent Issue: [#607](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/607)

Issues: [#613](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/613),
[#609](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/609),
[#608](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/608)

B9 は AIR、Feature Extension Report、Obstruction Witness、Architecture Drift Ledger、
detectable values / reported axes catalog など、複数 tooling artifact の schema version と
compatibility boundary を固定する段階である。catalog と policy の詳細は
[B9 schema version catalog](schema_version_catalog.md) で管理する。

Canonical fixture:

```text
tools/archsig/tests/fixtures/minimal/schema_version_catalog.json
```

Rust schema skeleton:

```text
SchemaVersionCatalogV0
SchemaCompatibilityPolicyV0
SchemaCompatibilityBoundaryV0
SchemaArtifactCompatibilityV0
```

Compatibility policy は field mapping、deprecated fields、new required assumptions、
non-conclusions、coverage / exactness boundary を別項目として扱う。

AIR と Feature Extension Report は `schemaCompatibility` metadata を出力する。
AIR metadata は `coverage.layers[].extractionScope`、
`coverage.layers[].exactnessAssumptions`、`coverage.layers[].unsupportedConstructs`、
`claims[].missingPreconditions`、`claims[].nonConclusions` を migration boundary として
保持する。Feature Extension Report metadata は `coverageGaps[].nonConclusions`、
`theoremPreconditionChecks[].missingPreconditions`、`unsupportedConstructs`、
`nonConclusions` を保持する。

`archsig validate-air` は metadata が存在する AIR について、coverage / exactness
boundary、theorem bridge preconditions、formal claim promotion を禁止する
non-conclusions が metadata から落ちていないことを検査する。legacy AIR v0 fixture は
metadata 欠落を backward-compatible input として読む。

`archsig schema-compatibility --before <path> --after <path>` は B9 catalog を参照し、
schema migration / compatibility check report を出力する。report は field mappings、
deprecated fields、new required assumptions、non-conclusions、coverage / exactness
boundaries を別軸で保持し、schemaVersion 未登録、metadata 欠落、non-conclusion 欠落、
formal claim promotion boundary の欠落を `pass` / `requiresMigration` /
`blockedFormalClaimPromotion` / `fail` に分類する。metadata がない同一 schemaVersion の
B0-B8 artifact は backward-compatible input として warning 付きで受け入れる。

Non-conclusions:

- schema migration は意味保存を主張しない。
- compatibility pass は architecture lawfulness を結論しない。
- compatibility pass は Lean theorem claim を結論しない。
- catalog entry の存在は extractor completeness を結論しない。
