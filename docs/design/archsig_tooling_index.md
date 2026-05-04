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
