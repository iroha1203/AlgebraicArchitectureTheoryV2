# Law policy template registry v0 schema

Lean status: empirical hypothesis / tooling validation.

`law-policy-template-registry-v0` は、boundary / abstraction / runtime protection などの
law policy template を tooling registry として固定する。template は policy selector と
required evidence の初期値を与えるが、template 適用や validation pass だけで
architecture lawfulness、Lean theorem claim、extractor completeness、未測定 gap の
measured-zero 化は結論しない。

この registry は `adapter-registry-v0` の `policy-adapter` boundary と接続して読む。
template が出力する policy artifact は AIR / Feature Extension Report / organization
policy decision の入力になりうるが、formal claim promotion には明示的な theorem bridge
precondition が別に必要である。

## Schema

```text
LawPolicyTemplateRegistryV0
  schemaVersion: "law-policy-template-registry-v0"
  registryId: String
  scope: String
  templates: List LawPolicyTemplateV0
  explicitAssumptions: List String
  nonConclusions: List String
```

```text
LawPolicyTemplateV0
  templateId: String
  targetComponentKind: String
  lawPolicyFamily: "boundary" | "abstraction" | "local-contract" | "state-transition" | "runtime-protection" | "distributed-convergence"
  selectorSemantics: "exact-or-prefix-star" | "tag-match" | "adapter-provided"
  selectorAssumptions: List String
  requiredEvidenceKinds: List String
  defaultRequiredAxes: List String
  policyOutputArtifacts: List String
  theoremBridgePreconditions: List String
  nonConclusions: List String
```

`templateId` は stable id として扱う。Feature Extension Report、organization policy、
adapter registry の `policy-adapter` entry は、この id を trace できる必要がある。

## Template boundary

`targetComponentKind` は selector が参照する component id の kind を表す。v0 tooling が
予約する値は `lean-module`、`python-module`、`path`、`package`、`service`、`workflow`
である。

`selectorAssumptions` は、selector がどの測定 universe 上で解釈されるかを記録する。
selector が component を 0 個または曖昧に解決する場合、その axis は未測定または
validation failure として扱い、違反数 0 とは読まない。

`requiredEvidenceKinds` は policy template の適用に必要な evidence kind を表す。
例えば Python boundary template は `python_import` と `policy_selector` を必要とする。
runtime protection template は `runtime_trace` のような runtime adapter evidence を必要とする。

`defaultRequiredAxes` は organization policy の初期候補であり、CI fail 条件を自動決定しない。
どの axis を required にするかは organization policy 側で明示する。

`theoremBridgePreconditions` は formal claim へ接続する場合に不足してはならない前提である。
template validation はこの list の存在を確認するだけで、前提を discharge しない。

## CLI validation

ArchSig CLI は registry を validation report に写す。

```bash
archsig law-policy-templates --input law_policy_templates.json
```

input を省略すると static B8 registry を検証する。

出力 schema:

```text
law-policy-template-registry-validation-report-v0
```

validation は少なくとも次を検査する。

- schema version が `law-policy-template-registry-v0` である。
- registry id、scope、explicit assumptions が空ではない。
- `templateId` が空でなく一意である。
- target component kind、law / policy family、selector semantics が v0 の予約値である。
- selector assumptions、required evidence kinds、default required axes、output artifacts、theorem bridge preconditions が空ではない。
- registry と各 template が non-conclusion boundary を保持する。

Canonical fixture は `tools/archsig/tests/fixtures/minimal/law_policy_templates.json` であり、
`cargo test --manifest-path tools/archsig/Cargo.toml` で固定する。

## Non-conclusions

- law policy template registry は Lean theorem ではない。
- template application は architecture lawfulness を結論しない。
- template pass は Lean theorem claim を結論しない。
- unmeasured gap は measured-zero evidence ではない。
- selector match は extractor completeness を証明しない。
