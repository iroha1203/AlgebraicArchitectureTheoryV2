# Custom rule plugin registry v0 schema

Lean status: empirical hypothesis / tooling validation.

`custom-rule-plugin-registry-v0` は、organization-specific な rule や extractor extension を
ArchSig tooling evidence として扱うための trust boundary を固定する。plugin は AIR evidence
や Feature Extension Report metadata を追加できるが、plugin validation pass だけで
architecture lawfulness、Lean theorem claim、extractor completeness、unsupported gap の
measured-zero 化は結論しない。

この registry は `adapter-registry-v0` の policy / runtime / semantic adapter boundary と
接続して読む。formal claim promotion を許す plugin は、theorem precondition checker が参照
する theorem package refs と required preconditions を明示しなければならない。

## Schema

```text
CustomRulePluginRegistryV0
  schemaVersion: "custom-rule-plugin-registry-v0"
  registryId: String
  scope: String
  plugins: List CustomRulePluginV0
  explicitAssumptions: List String
  nonConclusions: List String
```

```text
CustomRulePluginV0
  pluginId: String
  ruleId: String
  pluginKind: "policy-rule" | "extractor-extension" | "runtime-evidence" | "semantic-evidence"
  evidenceKind: String
  confidence: "low" | "medium" | "high"
  inputContract: List String
  outputContract: List String
  coverageAssumptions: List String
  permittedClaimLevels: List ("tooling" | "empirical" | "formal")
  formalClaimPromotion: "not-permitted" | "requires-theorem-precondition-check"
  theoremPreconditionRefs: List String
  requiredTheoremPreconditions: List String
  outputArtifacts: List String
  nonConclusions: List String
```

`pluginId` は executable plugin または registry entry の stable id である。`ruleId` は plugin
が発火させる organization-specific rule の stable id であり、AIR evidence、Feature Extension
Report、policy decision report から trace できる必要がある。

## Trust boundary

`inputContract` は plugin が読む universe、artifact、selector、adapter output の前提を記録する。
`outputContract` は plugin が生成してよい evidence / report metadata の境界を記録する。contract
に含まれない relation、component、workflow、runtime trace は unsupported / unmeasured gap として
残す。

`evidenceKind` と `confidence` は plugin output の証拠種別と信頼度であり、formal proof status では
ない。`coverageAssumptions` は plugin が測定できる範囲を示し、欠落部分を violation count 0 や
measured zero として埋めない。

`permittedClaimLevels` に `formal` を含める場合、`formalClaimPromotion` は
`requires-theorem-precondition-check` でなければならない。この場合
`theoremPreconditionRefs` と `requiredTheoremPreconditions` を空にできない。validation はこの境界を
確認するだけで、theorem precondition を discharge しない。

## CLI validation

ArchSig CLI は registry を validation report に写す。

```bash
archsig custom-rule-plugins --input custom_rule_plugins.json
```

input を省略すると static B8 registry を検証する。

出力 schema:

```text
custom-rule-plugin-registry-validation-report-v0
```

validation は少なくとも次を検査する。

- schema version が `custom-rule-plugin-registry-v0` である。
- registry id、scope、explicit assumptions が空ではない。
- `pluginId` と `ruleId` が空でなく一意である。
- plugin kind、evidence kind、confidence、claim level、formal promotion mode が v0 の予約値である。
- input / output contract、coverage assumptions、permitted claim levels、output artifacts が空ではない。
- formal claim promotion は theorem refs と required preconditions なしに許されない。
- registry と各 plugin が non-conclusion boundary を保持する。

Canonical fixture は `tools/archsig/tests/fixtures/minimal/custom_rule_plugins.json` であり、
`cargo test --manifest-path tools/archsig/Cargo.toml` で固定する。

## Non-conclusions

- custom rule plugin registry は Lean theorem ではない。
- plugin output は architecture lawfulness を結論しない。
- plugin output は Lean theorem claim を結論しない。
- plugin evidence は unsupported gap を measured-zero evidence に変えない。
- formal claim promotion には explicit theorem precondition check が必要である。
