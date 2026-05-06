# AAT Tooling 総合入口

この文書は、旧 `AAT v2 ツール設計書` への参照を受けるための互換入口である。
tool 側の本文は [docs/tooling/](tooling/README.md) に分割して管理する。

数学理論の第一級本文は [AAT 総合理論](aat/README.md) に置く。
tool 側文書は理論を参照してよいが、理論本文は tool artifact、schema version、CI、PR workflow に
依存しない。

## 0. ツールの中心問い

Tooling の中心問いは、feature addition、operation、invariant、obstruction witness、
proof obligation、certificate、signature trajectory を、測定可能な artifact と review flow に
変換することである。

詳細は [Tooling principles](tooling/principles.md) と [Workflows](tooling/workflows.md) を参照する。

### 0.1 ユーザーストーリー

初回導入、PR review、generated-change provenance は [Workflows](tooling/workflows.md) を参照する。

#### Story 1: 初回導入

[Workflows: First adoption](tooling/workflows.md#first-adoption) を参照する。

#### Story 2: PR review

[Workflows: PR review](tooling/workflows.md#pr-review) を参照する。

#### Story 3: Generated-change provenance

[Workflows: Generated-change provenance](tooling/workflows.md#generated-change-provenance) を参照する。

#### CLI sketch

CLI の実装上の詳細は [ArchSig command guide](../tools/archsig/docs/commands.md) を参照する。

### 0.2 Architecture Dynamics tooling

Architecture Dynamics tooling は [Workflows](tooling/workflows.md#architecture-dynamics-workflow) と
[Roadmap: Phase B11](tooling/roadmap.md#phase-b11-architecture-dynamics-tooling) を参照する。

## 1. 数学設計書 / ツール設計書の境界

境界は [Tooling principles](tooling/principles.md) を参照する。

```text
math theory
  -> Lean theorem / proof obligation
  -> tooling artifact
  -> empirical workflow
```

## 2. Claim Taxonomy

Claim taxonomy は [Claim boundary](tooling/claim_boundary.md) を参照する。

## 3. AIR: Architecture Intermediate Representation

AIR は [AIR](tooling/air.md) を参照する。

### 3.1 AIR v0 schema

`aat-air-v0` は [AIR: Schema role](tooling/air.md#schema-role) を参照する。

### 3.2 Semantic path / homotopy layer

Semantic path / homotopy layer は [AIR: Semantic path and homotopy layer](tooling/air.md#semantic-path-and-homotopy-layer)
を参照する。

### 3.3 Law policy input

Law policy input は [Extraction: Policy extraction](tooling/extraction.md#policy-extraction) を参照する。

### 3.4 Feature extension fields

Feature extension fields は [AIR: Extension fields](tooling/air.md#extension-fields) を参照する。

### 3.5 Static split evidence

Static split evidence は [Feature Extension Report](tooling/reports.md#feature-extension-report) と
[Examples](tooling/examples.md) を参照する。

### 3.6 Algebraic annotations

Algebraic annotations は [Claim boundary](tooling/claim_boundary.md) と
[Theorem precondition checks](tooling/theorem_preconditions.md) を参照する。

### 3.7 Gradual adoption path

Gradual adoption path は [Roadmap](tooling/roadmap.md) を参照する。

## 4. Architecture Signature Artifact Layer

Architecture Signature artifact は [Signature artifacts](tooling/signature_artifacts.md) を参照する。

## 4. Signature Artifact Layer

旧見出し互換用の heading である。内容は
[Signature artifacts](tooling/signature_artifacts.md) を参照する。

### 4.1 Detectable values / reported axes

Detectable values / reported axes は
[Signature artifacts: Detectable values / reported axes](tooling/signature_artifacts.md#detectable-values--reported-axes)
を参照する。

## 5. Feature Extension Report

Feature Extension Report は [Reports](tooling/reports.md#feature-extension-report) を参照する。

### 5.1 Architecture Drift Ledger

Architecture Drift Ledger は [Reports: Architecture Drift Ledger](tooling/reports.md#architecture-drift-ledger)
を参照する。

## 6. Obstruction Witness Schema

Obstruction Witness Schema は [Reports: Obstruction Witness](tooling/reports.md#obstruction-witness)
を参照する。

### 6.1 Witness YAML example

Witness example は [Examples: Hidden interaction witness](tooling/examples.md#hidden-interaction-witness)
を参照する。

### 6.2 Semantic witness YAML example

Semantic witness example は [Examples: Semantic witness](tooling/examples.md#semantic-witness)
を参照する。

## 7. Theorem Precondition Checker

Theorem Precondition Checker は [Theorem precondition checks](tooling/theorem_preconditions.md) を参照する。

### 7.1 Report Soundness

Report soundness は [Theorem precondition checks: Report soundness](tooling/theorem_preconditions.md#report-soundness)
を参照する。

### 7.2 Witness Traceability

Witness traceability は [Theorem precondition checks: Witness traceability](tooling/theorem_preconditions.md#witness-traceability)
を参照する。

### 7.3 Coverage / Exactness Checker

Coverage / Exactness Checker は
[Theorem precondition checks: Coverage / exactness checker](tooling/theorem_preconditions.md#coverage--exactness-checker)
を参照する。

## 8. Extractor 方針

Extractor 方針は [Extraction](tooling/extraction.md) を参照する。

## 9. CI での扱い

CI / PR review flow は [Workflows](tooling/workflows.md#pr-review) を参照する。

## 10. Repair Suggestion

Repair Suggestion は [Repair suggestion](tooling/repair_suggestion.md) を参照する。

## 11. Empirical Validation

Empirical validation は [Roadmap: Phase B6](tooling/roadmap.md#phase-b6-empirical-validation) と
`docs/empirical/` を参照する。

## 12. Canonical Examples

Canonical examples は [Examples](tooling/examples.md) を参照する。

### 12.1 良い機能追加

[Examples: Good extension](tooling/examples.md#good-extension) を参照する。

### 12.2 悪い機能追加

[Examples: Hidden interaction witness](tooling/examples.md#hidden-interaction-witness) を参照する。

### 12.3 Semantic obstruction example

[Examples: Semantic witness](tooling/examples.md#semantic-witness) を参照する。

### 12.4 Benchmark suite

Benchmark suite は [Roadmap](tooling/roadmap.md) と `docs/empirical/` を参照する。

### 12.5 Standardization targets

Standardization targets は [Roadmap: Standardization targets](tooling/roadmap.md#standardization-targets)
を参照する。

## 13. Roadmap

Roadmap は [Roadmap](tooling/roadmap.md) を参照する。

### Phase B0: AIR and boundary

[Roadmap: Phase B0](tooling/roadmap.md#phase-b0-air-and-boundary) を参照する。

### Phase B1: Static Feature Extension Report

[Roadmap: Phase B1](tooling/roadmap.md#phase-b1-static-feature-extension-report) を参照する。

### Phase B2: Runtime integration

[Roadmap: Phase B2](tooling/roadmap.md#phase-b2-runtime-integration) を参照する。

### Phase B3: Semantic integration

[Roadmap: Phase B3](tooling/roadmap.md#phase-b3-semantic-integration) を参照する。

### Phase B4: Generated-change provenance and review workflow

[Roadmap: Phase B4](tooling/roadmap.md#phase-b4-generated-change-provenance) を参照する。

### Phase B5: Repair and synthesis prototype

[Roadmap: Phase B5](tooling/roadmap.md#phase-b5-repair-and-synthesis-prototype) を参照する。

### Phase B6: Empirical validation

[Roadmap: Phase B6](tooling/roadmap.md#phase-b6-empirical-validation) を参照する。

### Phase B7: CI / PR review integration

[Roadmap: Phase B7](tooling/roadmap.md#phase-b7-pr-review-integration) を参照する。

### Phase B8: Extractor / policy ecosystem

[Roadmap: Phase B8](tooling/roadmap.md#phase-b8-extractor--policy-ecosystem) を参照する。

### Phase B9: Schema standardization and compatibility

[Roadmap: Phase B9](tooling/roadmap.md#phase-b9-schema-standardization-and-compatibility) を参照する。

### Phase B10: Operational feedback loop

[Roadmap: Phase B10](tooling/roadmap.md#phase-b10-operational-feedback-loop) を参照する。

### Phase B11: Architecture Dynamics tooling

[Roadmap: Phase B11](tooling/roadmap.md#phase-b11-architecture-dynamics-tooling) を参照する。

## 14. 成功基準

成功基準は、tool output が claim boundary、measurement boundary、coverage、exactness、
non-conclusions を落とさず、人間と automation が同じ artifact を読めることである。

## 15. 非目標

Tooling docs は次を目標としない。

```text
完全な architecture model の自動抽出
Lean theorem の自動証明
未測定軸の zero 扱い
empirical correlation の formal theorem 化
人間の設計判断の置き換え
```
