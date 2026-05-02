# Lean module 階層整理方針

Lean status: `defined only` / module organization / docs and API design.

この文書は Issue [#138](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/138)
の責務分類を引き継ぎ、Issue [#423](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/423)
以降で `Formal/Arch` を段階的にサブディレクトリ化し、最終的に canonical path へ一本化する
ための import 方針を固定する。
数学的定義、theorem statement、Lean status の読みは変更しない。

## 方針

`Formal/Arch` 直下の import-only facade は削除し、実体 module の canonical path へ一本化する。

- 新しい実体 module は責務別のサブディレクトリへ移す。
- 旧 `Formal.Arch.<Module>` import path は互換 API として維持しない。
- `Formal.lean` は public entry point として残し、canonical path を import する。
- 新規コードと docs の主参照先は、移動後の canonical path を使う。

この方針により、`Formal/Arch` 直下のファイル数を削減し、責務構造を file system 上でも
直接読めるようにする。既存利用者が全体を import する場合は `import Formal` を使い、
個別 module を import する場合は canonical path を使う。

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

この表は現在の canonical path を表す。`Formal/Arch` 直下の import-only facade は残さない。
ただし、数学的主張や theorem 名の変更を file move と混ぜない。

## 移行状況

移行は leaf module から core module へ進めた。

1. Issue [#425](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/425):
   `Patterns`, `Repair`, `Evolution`, `Examples` へ leaf module を移した。
2. Issue [#426](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/426):
   `Core`, `Law`, `Signature`, `Extension`, `Operation` を依存グラフに沿って小さく移した。
3. Issue [#427](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/427):
   `docs/lean_theorem_index.md` と `docs/proof_obligations.md` の path / status を実配置へ同期した。
4. Issue [#444](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/444):
   `Formal/Arch` 直下の import-only facade を削除し、canonical path へ一本化する。

依存中心に近い module は broad import の影響が大きいため、`Graph`, `Reachability`,
`Finite`, `Signature`, `Flatness`, `Operation*` は段階的に canonical path へ移した。

## import ルール

移動後の import ルールは次の通りである。

- moved implementation 同士は canonical path を import する。
- `Formal.lean` は canonical path を import し、全体 import の入口を保つ。
- docs では canonical path を主参照先にする。
- `Formal/Arch` 直下に旧 path 互換の import-only facade は置かない。

## docs 更新ルール

file move を含む PR では、少なくとも次を確認する。

- `Formal.lean`: public import entry point と import 順序。
- moved Lean files: `import Formal.Arch.<Module>` から canonical path への更新。
- `Formal/Arch` 直下に不要な import-only facade が残っていないこと。
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

## #423 系 Issue の結論

Issue #424 では、段階移行中の互換性のため `Formal/Arch` 直下に facade を残す方針を採用した。
Issue #425 と Issue #426 では、実体 module を leaf から core へ段階的に canonical
subdirectory へ移した。Issue #427 では docs / theorem index を canonical path へ同期した。
Issue #444 では、整理の最終段階として `Formal/Arch` 直下の import-only facade を削除し、
`Formal.lean` と内部 import を canonical path に一本化する。以後、旧 `Formal.Arch.<Module>`
import path は互換 API として維持しない。
