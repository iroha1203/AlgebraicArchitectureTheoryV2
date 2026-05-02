# Lean module 階層整理方針

Lean status: `defined only` / module organization / docs and API design.

この文書は Issue [#138](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/138)
の責務分類を引き継ぎ、Issue [#423](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/423)
以降で `Formal/Arch` を段階的にサブディレクトリ化するための facade / import 方針を固定する。
数学的定義、theorem statement、Lean status の読みは変更しない。

## 方針

`Formal/Arch` 直下は public facade / compatibility layer として残す。

- 新しい実体 module は責務別のサブディレクトリへ移す。
- 既存の `Formal.Arch.<Module>` は、当面は同名 facade module として残し、移動先を import する。
- `Formal.lean` は public entry point として、既存 facade を import し続ける。
- 新規コードと docs の主参照先は、移動後の canonical path を使う。
- 互換 facade の削除は、この段階移行とは別 Issue として、下流 import の確認後に扱う。

この方針により、既存利用者は `Formal.Arch.<Module>` import をすぐ変更しなくてもよい。
一方で、移動後の責務構造は canonical path として docs / theorem index に反映する。

## サブディレクトリ構成

| canonical path | 対象 module | 役割 |
| --- | --- | --- |
| `Formal/Arch/Core` | `Graph`, `Reachability`, `Layering`, `Decomposable`, `Finite`, `Category`, `ThinCategory`, `Matrix` | graph、walk / reachability、strict layering、finite universe、thin category、finite matrix bridge の基盤。 |
| `Formal/Arch/Law` | `Projection`, `Observation`, `LSP`, `LocalReplacement`, `Lawfulness`, `StateEffect` | projection / observation / LSP / local replacement と、lawfulness・state effect の bounded law schema。 |
| `Formal/Arch/Signature` | `Signature`, `SignatureLawfulness`, `Obstruction`, `DependencyObstruction`, `Curvature`, `AnalyticRepresentation`, `ComplexityTransfer` | Architecture Signature、obstruction witness、curvature、analytic representation、complexity-transfer witness の診断軸。 |
| `Formal/Arch/Extension` | `FeatureExtension`, `FeatureExtensionExamples`, `SplitExtensionLifting`, `Flatness`, `ArchitectureExtensionFormula`, `CertifiedArchitecture` | feature extension、split lifting、flatness、extension formula、proof-carrying architecture core。 |
| `Formal/Arch/Operation` | `Operation`, `OperationKernel`, `OperationLaws`, `OperationInvariant` | operation schema、finite operation kernel、bounded calculus laws、operation / invariant bridge。 |
| `Formal/Arch/Patterns` | `LocalContractDesignPattern`, `SRPDesignPattern`, `ISPDesignPattern`, `StructuralDesignPattern`, `RuntimeProtectionDesignPattern`, `StateTransitionDesignPattern`, `EventSourcingSagaDesignPattern`, `ReplicatedLogDesignPattern` | design pattern を selected operation / invariant family として読む bounded theorem package。 |
| `Formal/Arch/Repair` | `Repair`, `RepairSynthesis`, `RepairTransferCounterexample` | repair step、synthesis / no-solution certificate、repair transfer の境界例。 |
| `Formal/Arch/Evolution` | `ArchitecturePath`, `ArchitectureEvolution`, `DiagramFiller`, `Chapter7TheoremPackages` | path / evolution / diagram filler と、Chapter 7 の docs-facing theorem package entrypoint。 |
| `Formal/Arch/Examples` | `SolidCounterexample`, `StaticSemanticCounterexample` | reader-facing counterexample / example。 |

この表は現在の canonical path を表す。互換性のため、`Formal/Arch` 直下には import-only
facade module を残す。ただし、数学的主張や theorem 名の変更を file move と混ぜない。

## 移行順

移行は leaf module から core module へ進める。

1. Issue [#425](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/425):
   `Patterns`, `Repair`, `Evolution`, `Examples` へ leaf module を移す。
2. Issue [#426](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/426):
   `Core`, `Law`, `Signature`, `Extension`, `Operation` を依存グラフに沿って小さく移す。
3. Issue [#427](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/427):
   `docs/lean_theorem_index.md` と `docs/proof_obligations.md` の path / status を実配置へ同期する。

依存中心に近い module は broad import の影響が大きい。`Graph`, `Reachability`, `Finite`,
`Signature`, `Flatness`, `Operation*` は、leaf 移動後に単独または小さい束で移す。

## facade module の作り方

既存 module `Formal/Arch/Foo.lean` を `Formal/Arch/<Group>/Foo.lean` へ移す場合は、
原則として次の形にする。

```lean
import Formal.Arch.<Group>.Foo
```

facade module には定義や theorem を追加しない。移動先 module に namespace と実装を置き、
facade は旧 import path の互換性だけを担う。

移動後の import ルールは次の通り。

- moved implementation 同士は canonical path を import する。
- 既存 facade は互換性のために canonical path だけを import する。
- `Formal.lean` は public facade を import し、全体 import の互換性を保つ。
- docs では、移行 PR の時点で canonical path と facade path の関係を明記する。

## docs 更新ルール

file move を含む PR では、少なくとも次を確認する。

- `Formal.lean`: public import entry point と import 順序。
- moved Lean files: `import Formal.Arch.<Module>` から canonical path への更新。
- facade Lean files: 旧 path 互換の import-only module になっていること。
- `docs/lean_theorem_index.md`: `File:` / `Files:` の path と section name。
- `docs/proof_obligations.md`: status ledger / proof obligation index に影響する path。
- `docs/README.md` と `docs/design/*.md`: Lean module path を参照する箇所。

`docs/aat_v2_mathematical_design.md` は数学面の第一級設計書であり、作業状態や移行 status を
混ぜない。module path の進捗管理はこの文書、`docs/proof_obligations.md`、
`docs/lean_theorem_index.md` で扱う。

## PR 前チェック

Lean module を移動する PR では、必ず次を実行する。

- `lake build Formal`
- `git diff --check`
- hidden / bidirectional Unicode scan
- Lean ソースに対する `axiom` / `admit` / `sorry` / `unsafe` scan

docs-only の方針更新 PR でも、`git diff --check` と hidden / bidirectional Unicode scan は実行する。
Lean import に影響しないことを確認したうえで、`lake build Formal` は必要に応じて実行する。

## 当面の命名・配置ルール

- `Decomposable G := StrictLayered G` は維持し、acyclicity, finite propagation,
  nilpotence, spectral conditions を `Decomposable` の定義へ混ぜない。
- `ComponentCategory` は thin category として path count / walk length を忘れる。
- 定量指標は `Walk`, `Path`, finite metrics, adjacency matrix, または将来の
  free-category construction 側で扱う。
- executable metrics は有限な測定 universe 上の計算として定義し、graph-level facts との
  接続は別 theorem として証明する。
- `ComponentUniverse` は proof-carrying measurement universe として扱い、実コード抽出器の
  完全性を直接主張しない。
- Architecture Signature は単一スコアではなく、多軸診断として扱う。

## #424 の結論

Issue #424 では、`Formal/Arch` 直下に互換 facade を残す方針を採用する。
実体 module は leaf から core へ段階的に canonical subdirectory へ移し、各段階で
docs path と `lake build Formal` を確認する。完全移動や facade 削除は、この段階移行の
完了後に別 Issue として判断する。
