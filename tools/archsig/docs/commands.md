# ArchSig Command Guide

この文書は `archsig` の主要 command と最小例をまとめる。研究上の解釈や非主張境界は
[Artifacts And Boundaries](artifacts-and-boundaries.md) を参照する。

## Surface map

Command は次の product surface に分けて読む。

| Surface | Commands | 読み方 |
| --- | --- | --- |
| ArchSig Core | default scan、`validate`、`snapshot`、`signature-diff` | repository observation と revision diff。未評価軸は `metricStatus` と `metricDeltaStatus` で読む。 |
| ArchSig Review | `air`、`archmap`、`archmap-generate`、`air-from-archmap`、`validate-air`、`theorem-check`、`feature-report`、`policy-decision`、`pr-comment`、`baseline-suppression` | PR / CI review 補助。tool output を formal theorem claim に昇格しない。 |
| ArchSig SFT | `artifact-descriptor`、`archmap-sft-input`、`operation-support-estimate`、`forecast-cone-skeleton`、`consequence-envelope`、`forecast-calibration-hook`、`ai-proposal-governance`、`sft-forecast` | bounded forecast artifact と governance / report projection。point prediction、causal proof、global safety は non-conclusions。 |
| ArchSig Operational | `dataset`、`pr-history-dataset`、`feature-extension-dataset`、`outcome-linkage-dataset`、B10 feedback commands | calibration、threshold、ownership、repair adoption、incident correlation、hypothesis refresh 用 artifact。correlation は因果 theorem ではない。 |

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

supplied JSON の ArchMap v0 を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/minimal/archmap.json \
  --out .lake/archmap-validation.json
```

`archmap` は `archmap-validation-report-v0` を出す。source inventory / source refs、
claim boundary、semantic coverage、conflict category、formal promotion guardrail を検査する。
出力には `leanPreservationVocabulary` と `leanPreservationPreconditionChecklist` も含まれる。
これは `archmap-v0` の map item を `ArchMapPreservationPackage` の候補 field
(`ObjectPreservation`, `RelationPreservation`, `SemanticDiagramPreservation`,
`SemanticCommutationPreservation`, `NonfillabilityWitnessPreservation`,
`LawPolicyPreservation`, `FlatnessPreconditionPreservation`, `CoverageExactnessBoundary`)
へ対応づけ、missing evidence、unmeasured coverage、formal promotion guardrail、
supplied assumption、out-of-scope を区別する report surface である。
canonical fixture では `sourceInventoryRef.path` が
`tools/archsig/tests/fixtures/minimal/archmap_source_inventory.json` を指し、validation は
その独立 artifact の存在、included / excluded / unavailable / private boundary、hash、
selection boundary が `archmap.json` 内の `sourceUniverse` と整合するかを
`sourceInventoryChecks` に記録する。
warning は conflict や dangling boundary を review cue として残すために使い、semantic correctness や
architecture lawfulness は結論しない。
`formalPromotionGuardrailChecks` には `archmap-aat-sft-projection-separation` も含まれる。
これは AAT-facing projection と SFT-facing projection の有無を検査し、shared source refs は許しつつ、
SFT-facing item を Lean proof や forecast correctness へ昇格しない guardrail として読む。

外部 agent / LLM による ArchMap 生成 workflow を固定する protocol artifact を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-generate \
  --source-inventory tools/archsig/tests/fixtures/minimal/archmap_source_inventory.json \
  --prompt-pack .lake/archmap-prompt.md \
  --provider external-agent \
  --model-id model-name \
  --out .lake/archmap-generation-protocol.json
```

`archmap-generate` は model を実行しない。`archmap-generation-protocol-v0` として
source inventory、prompt pack、model provenance、required workflow、private / unavailable boundary を
再現可能に残す。生成された ArchMap JSON は別途 `archmap` で validation する。

表現力回帰用には
`tools/archsig/tests/fixtures/expressiveness/archmap_expressiveness_suite_v0.json` を使う。
この fixture は layered policy、SRP responsibility、contract preservation、semantic commutation /
non-commutation、event sourcing projection、saga compensation、runtime/static disagreement、
framework convention、dynamic plugin blind spot を一つの suite artifact として固定する。
`cli_locks_archmap_expressiveness_suite_v0_boundaries` は `archmap`、`air-from-archmap`、
`validate-air`、`theorem-check`、`feature-report` の期待 boundary を検査する。

ArchMap から AIR v0 を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- air-from-archmap \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --validation .lake/archmap-validation.json \
  --out .lake/archmap-air.json
```

`air-from-archmap` は source artifact refs を AIR `artifacts[]` / `evidence[]` に、object /
relation / semantic diagram / nonfillability witness / claim boundary を対応する AIR field に投影する。
missing evidence、coverage gap、nonConclusions、conflict は measured zero や resolved claim に丸めない。
Lean preservation field との対応は AIR `claims[].requiredAssumptions` に candidate として残し、
後段 `theorem-check` が ArchMap preservation checklist を再構成できるようにする。

ArchMap から SFT input artifact を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-sft-input \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --out .lake/archmap-operation-support-estimate.json
```

`archmap-sft-input` は `operation-support-estimate-v0` を出す。ArchMap の SFT-facing item を
operation / workflow / event / state / transition / test oracle / runtime observation /
proposal force candidate として読むための候補 family に投影し、`source:archmap:*` refs、
missing evidence、private / unavailable / unsupported boundary を保持する。ここで出る confidence は
review priority であり probability ではない。後段では既存の
`forecast-cone-skeleton --operation-support` と `consequence-envelope --forecast-cone` に接続する。

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

ArchMap-derived AIR の場合、`theorem-check` は
`archmapPreservationPreconditionChecklist` を出力する。これは validation / AIR projection の成功を
Lean theorem proof に昇格せず、candidate / blocked / supplied-assumption の状態を保持する。

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

Signature trajectory report の canonical fixture を出力し、既存 artifact を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- signature-trajectory-report \
  --fixture \
  --out .lake/signature-current/signature-trajectory-report.json

cargo run --manifest-path tools/archsig/Cargo.toml -- signature-trajectory-report \
  --input tools/archsig/tests/fixtures/minimal/signature_trajectory_report.json \
  --out .lake/signature-current/signature-trajectory-report-validation.json
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

B12 ArtifactDescriptor の canonical fixture を出力し、既存 descriptor を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- artifact-descriptor \
  --fixture \
  --out .lake/signature-current/artifact-descriptor.json

cargo run --manifest-path tools/archsig/Cargo.toml -- artifact-descriptor \
  --input tools/archsig/tests/fixtures/minimal/artifact_descriptor.json \
  --out .lake/signature-current/artifact-descriptor-validation.json
```

`artifact-descriptor-v0` は PRD / Spec / Issue / AI proposal を source refs、
action class candidates、scope、missing evidence、measurement boundary、
forecast non-conclusions に正規化する。operation support、ForecastCone、probability、
causal forecast はこの command では生成しない。

Markdown PRD / Spec を実入力として descriptor を生成する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- artifact-descriptor \
  --from-markdown docs/prd/coupon.md \
  --artifact-kind prd \
  --out .lake/signature-current/artifact-descriptor.json
```

`--from-markdown` は Markdown の title、scope 系 heading、inline file refs、
request body から source refs、scope、action class candidates、missing evidence を
組み立てる。生成 descriptor は通常の `artifact-descriptor --input` validator に渡せる。

GitHub Issue JSON または AI proposal JSON を実入力として descriptor を生成する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- artifact-descriptor \
  --from-github-issue-json issue-878.json \
  --out .lake/signature-current/artifact-descriptor.json

cargo run --manifest-path tools/archsig/Cargo.toml -- artifact-descriptor \
  --from-ai-proposal-json ai-proposal.json \
  --out .lake/signature-current/artifact-descriptor.json
```

JSON adapter は与えられた artifact を正規化するだけで、GitHub API 取得、
authenticated connector、AI model evaluation、runtime extraction は行わない。
GitHub Issue JSON では private / unavailable API context、AI proposal JSON では
human review と model evaluation を missing evidence boundary として保持する。

B12 OperationSupportEstimate の canonical fixture を出力し、既存 estimate を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- operation-support-estimate \
  --fixture \
  --out .lake/signature-current/operation-support-estimate.json

cargo run --manifest-path tools/archsig/Cargo.toml -- operation-support-estimate \
  --input tools/archsig/tests/fixtures/minimal/operation_support_estimate.json \
  --out .lake/signature-current/operation-support-estimate-validation.json
```

生成済み `artifact-descriptor-v0` から operation support estimate を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- operation-support-estimate \
  --descriptor .lake/signature-current/artifact-descriptor.json \
  --out .lake/signature-current/operation-support-estimate.json
```

`operation-support-estimate-v0` は `artifact-descriptor-v0` の source refs と
action class candidate refs を保持したまま、candidate operation families、
policy constraints、known forbidden support、unknown remainder、confidence /
evidence boundary を分離する。accepted PR history、actual future support、global
policy safety、future trajectory safety はこの command では主張しない。

B12 ForecastCone / ConsequenceEnvelope / CalibrationHook の canonical fixture を出力し、
既存 artifact を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- forecast-cone-skeleton \
  --fixture \
  --out .lake/signature-current/forecast-cone-skeleton.json

cargo run --manifest-path tools/archsig/Cargo.toml -- forecast-cone-skeleton \
  --input tools/archsig/tests/fixtures/minimal/forecast_cone_skeleton.json \
  --out .lake/signature-current/forecast-cone-skeleton-validation.json
```

生成済み `operation-support-estimate-v0` から bounded horizon 付きの
`forecast-cone-skeleton-v0` を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- forecast-cone-skeleton \
  --operation-support .lake/signature-current/operation-support-estimate.json \
  --horizon-steps 4 \
  --horizon-window "selected bounded forecast horizon" \
  --out .lake/signature-current/forecast-cone-skeleton.json
```

`forecast-cone-skeleton` の generator は operation support refs、finite support refs、
bounded horizon、path class candidates、forecast boundary、unknown remainder を保持する。
probability、global risk reduction、trajectory-level safety、empirical prediction theorem は
non-conclusions として残す。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- consequence-envelope \
  --fixture \
  --out .lake/signature-current/consequence-envelope-report.json

cargo run --manifest-path tools/archsig/Cargo.toml -- consequence-envelope \
  --input tools/archsig/tests/fixtures/minimal/consequence_envelope_report.json \
  --out .lake/signature-current/consequence-envelope-validation.json
```

生成済み `forecast-cone-skeleton-v0` から reviewer / CI / issue decomposition が読める
`consequence-envelope-report-v0` を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- consequence-envelope \
  --forecast-cone .lake/signature-current/forecast-cone-skeleton.json \
  --out .lake/signature-current/consequence-envelope-report.json

cargo run --manifest-path tools/archsig/Cargo.toml -- forecast-calibration-hook \
  --fixture \
  --out .lake/signature-current/forecast-calibration-hook.json

cargo run --manifest-path tools/archsig/Cargo.toml -- forecast-calibration-hook \
  --input tools/archsig/tests/fixtures/minimal/forecast_calibration_hook.json \
  --out .lake/signature-current/forecast-calibration-hook-validation.json
```

`forecast-cone-skeleton-v0` は finite support refs、bounded horizon、
path class candidates、operation support refs、source refs、forecast boundary、
unknown remainder を保持する。`consequence-envelope-report-v0` は affected
architecture regions、comparable signature axes、expected axis delta ranges、
selected obstruction witness candidates、missing boundary items、theorem boundary
items、review / CI / issue recommendation を保持する。`forecast-calibration-hook-v0`
は forecast item refs と observed PR / review / CI / outcome refs、B10 / B11 artifact
boundary を対応付ける。これらは probability、global risk reduction、trajectory-level
safety、forecast correctness、causal proof、Lean theorem claim を主張しない。
Calibration / benchmark の読み方は `docs/tool/sft_calibration_benchmark.md` に置き、
review mediation と AI shortcut detection を分けて扱う。

AI proposal governance の canonical fixture を出力し、既存 governance artifact を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- ai-proposal-governance \
  --fixture \
  --out .lake/signature-current/ai-proposal-governance.json

cargo run --manifest-path tools/archsig/Cargo.toml -- ai-proposal-governance \
  --input tools/archsig/tests/fixtures/minimal/ai_proposal_governance.json \
  --out .lake/signature-current/ai-proposal-governance-validation.json
```

生成済み `artifact-descriptor-v0` から governance projection を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- ai-proposal-governance \
  --descriptor .lake/signature-current/artifact-descriptor.json \
  --operation-support-id fixture-operation-support-estimate-v0 \
  --consequence-envelope-id fixture-consequence-envelope-report-v0 \
  --out .lake/signature-current/ai-proposal-governance.json
```

`ai-proposal-governance-v0` は prompt / policy boundary、allowed /
conditionallyAllowed / forbidden / unknown / outOfScope support、shortcut witness、
review / CI mediation、posterior field update を保持する。AI safety、forecast
correctness、architecture lawfulness、review pass / CI pass の theorem 化は
non-conclusions として残す。

Markdown PRD / Spec / Issue / AI proposal から B13 pipeline を end-to-end で実行し、
中間 artifact と validation report、final `ConsequenceEnvelope` を出力する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- sft-forecast \
  --artifact docs/prd/coupon.md \
  --artifact-kind prd \
  --horizon-steps 4 \
  --horizon-window "Coupon PRD bounded forecast horizon" \
  --out-dir .lake/signature-current/sft-forecast
```

GitHub Issue JSON または AI proposal JSON から同じ pipeline を実行する場合は
`--artifact-format` を指定する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- sft-forecast \
  --artifact issue-878.json \
  --artifact-format github-issue-json \
  --horizon-steps 3 \
  --horizon-window "GitHub Issue bounded forecast horizon" \
  --out-dir .lake/signature-current/sft-forecast
```

`sft-forecast` は次のファイルを `--out-dir` に書く。

- `artifact-descriptor.json`
- `artifact-descriptor-validation.json`
- `operation-support-estimate.json`
- `operation-support-estimate-validation.json`
- `forecast-cone-skeleton.json`
- `forecast-cone-skeleton-validation.json`
- `consequence-envelope-report.json`
- `consequence-envelope-validation.json`

この command の成功は、source refs、measurement boundary、forecast boundary、
unknown remainder、non-conclusions が B13 pipeline 内で保持されたことを検査する。
probability、causal prediction、global safety、Lean theorem claim、extractor
completeness、forecast correctness は結論しない。

Closed-loop SFT workbench の最小設計では、この `sft-forecast` 出力を
AI proposal governance、lifecycle decision surface、`forecast-calibration-hook-v0`、
B10 operational feedback artifact と束ねて読む。現時点では workbench 専用 CLI はなく、
workbench run manifest、review intervention record、calibration join report は将来の
schema / fixture / validator 候補である。`sft-forecast` の成功や B10 artifact との接続は、
deployed governance correctness、forecast quality、global risk reduction、または incident
causality を意味しない。

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

cargo run --manifest-path tools/archsig/Cargo.toml -- schema-catalog \
  --out .lake/signature-current/schema-version-catalog.json

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
