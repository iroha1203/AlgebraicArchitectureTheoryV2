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

Parent Issue: [#577](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/577)

B8 は non-Lean extractor と policy ecosystem を AIR / Feature Extension Report へ接続する
layer である。extractor は言語ごとの bounded subset、unsupported constructs、coverage
assumptions、projection rule を evidence として出し、Lean の `ComponentUniverse` 完全性とは
分離する。

### Python component policy

Issue: [#581](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/581)

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

関連 schema / docs:

- [AAT v2 tooling design](../aat_v2_tooling_design.md#phase-b8-extractor--policy-ecosystem)
- [ArchSig v0 design](archsig_design.md)
- [boundary / abstraction policy v0 schema](boundary_abstraction_policy_schema.md#python-module-id-policy)
- [ComponentUniverse validation report v0](component_universe_validation_report.md)

Non-conclusions:

- Python component policy は extractor evidence であり、Lean theorem ではない。
- `python-module` scan は dynamic import、plugin loading、framework convention、generated code、notebook を完全捕捉しない。
- external dependency edge は local `ComponentUniverse` closure witness ではない。
- policy selector の一致は architecture lawfulness や実コード extractor completeness を結論しない。
