# Lean module 階層整理方針

Lean status: `defined only` / module organization / docs and API design.

この文書は Issue [#138](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/138)
の設計決定である。現時点では `Formal/Arch` 以下のファイル移動は行わず、責務分類と
当面の配置ルールを明文化する。実際の import path 変更は、必要になった時点で単独の
follow-up Issue / PR に分割し、`lake build` を通して進める。

## 現行 module の責務分類

| 責務層 | 現行 module | 役割 |
| --- | --- | --- |
| Core graph theory | `Graph`, `Reachability` | `ArchGraph`, `Walk`, `SimpleWalk` / `Path`, `Reachable` を定義する最小基盤。 |
| Structural invariants | `Layering`, `Decomposable`, `Finite` | `StrictLayered`, `Acyclic`, `FinitePropagation`, finite `ComponentUniverse`, finite graph bridge theorem を扱う。 |
| Category / projection | `Category`, `ThinCategory`, `Projection` | thin category と抽象射影、DIP / projection soundness / exactness を扱う。 |
| Behavior | `Observation`, `LSP`, `LocalReplacement` | 観測同値、LSP、projection bridge と observation bridge を束ねる局所置換契約を扱う。 |
| Architecture operations | `FeatureExtension`, `Flatness` | feature addition を first-class operation として扱う最小 schema、静的 split extension 条件、coverage-aware three-layer flatness predicate を扱う。 |
| Metrics / matrix / obstruction bridge | `Signature`, `Matrix`, `DependencyObstruction` | Architecture Signature v0/v1、finite executable metrics、adjacency matrix / nilpotence / spectral bridge、closed-walk obstruction exactness を扱う。 |
| Examples / counterexamples | `SolidCounterexample` | SOLID-style local contract だけでは `Decomposable` が従わない反例を保持する。 |

この分類は reader-facing な責務整理であり、現時点の Lean import path は
`Formal.Arch.<Module>` の flat layout のまま維持する。

## 変更しない判断

短期的には `Formal/Arch` 直下の flat layout を維持する。理由は次の通り。

- module 数はまだ少なく、`Formal.lean` と `docs/formal/lean_theorem_index.md` で入口を把握できる。
- file move は import path を変え、下流 import、docs link、theorem index の同時更新を要求する。
- 現在の主要課題は theorem / docs / empirical tooling の安定化であり、階層移動そのものは新しい theorem を増やさない。
- `Formal.Arch.Signature` と `Formal.Arch.Matrix` は多くの前提 module を参照するため、移動 PR の blast radius が相対的に大きい。

したがって Issue #138 では、移動を実施せず、責務分類・移動判断基準・配置ルールを固定する。

## 将来移動する判断基準

次のいずれかが起きた場合に、subdirectory 化を follow-up Issue として検討する。

- `Formal/Arch` 直下の module が増え、theorem index の reader-facing section と import path の対応が分かりにくくなった。
- core graph theory と metric / empirical bridge の依存方向を import path でも明示する必要が出た。
- paper-ready research note で、Lean API の提示順と module path の対応が読者の理解を妨げる。
- downstream code が `Formal.Arch` 全体 import ではなく特定責務層だけを import する需要を持つ。

移動する場合の候補は次である。

| 将来 path 候補 | 対象 module |
| --- | --- |
| `Formal/Arch/Core` | `Graph`, `Reachability`, `Layering`, `Decomposable`, `Finite` |
| `Formal/Arch/Category` | `Category`, `ThinCategory`, `Projection` |
| `Formal/Arch/Behavior` | `Observation`, `LSP`, `LocalReplacement` |
| `Formal/Arch/Operations` | `FeatureExtension`, `Flatness` |
| `Formal/Arch/Metrics` | `Signature`, `Matrix` |
| `Formal/Arch/Examples` | `SolidCounterexample` |

ただし `Projection` は category / behavior / metrics の境界にある。移動時は、
projection soundness を category-side abstraction bridge として置くか、
behavior と同じ local-contract 層へ置くかをその PR で明示する。

## import path 変更の影響範囲

実際に file move する PR では、少なくとも次を同時に更新する。

- `Formal.lean`: public import entry point の順序と path。
- moved Lean files: `import Formal.Arch.<Module>` 参照。
- `docs/formal/lean_theorem_index.md`: `File:` / `Files:` の path と section name。
- `docs/proof_obligations.md`: theorem 名や file path を含む説明。
- `docs/aat_v2_overview.md` と `docs/design/*.md`: Lean module path を参照する箇所。
- downstream imports: repository 内の `Formal.Arch.<Module>` import と、必要なら README の例。

file move PR は docs-only PR と混ぜない。移動 PR では Lean の定義や theorem statement を
原則として変更せず、path 更新と `lake build` に焦点を絞る。

## 当面の命名・配置ルール

- graph の基礎構造は `Graph` / `Reachability` に置く。
- `Decomposable G := StrictLayered G` は `Decomposable` に置き、acyclicity,
  finite propagation, nilpotence, spectral conditions を定義へ混ぜない。
- finite universe と graph-level bridge theorem は `Finite` に置く。
- Signature の executable metric 定義は `Signature` に置き、graph-level correctness theorem は
  必要に応じて `Finite` または該当 bridge module に置く。
- adjacency matrix / nilpotence / spectral radius の bridge は `Matrix` に置く。
- projection / DIP の定義と theorem は `Projection` に置く。
- observation / LSP / local replacement は `Observation`, `LSP`, `LocalReplacement` に分ける。
- feature addition / split extension の operation schema は `FeatureExtension` に置く。
- coverage-aware three-layer flatness predicate と extension coverage package は `Flatness` に置く。
- counterexample は theorem の補助例であっても、reader-facing example として
  `SolidCounterexample` に隔離する。
- 新規 module を追加する場合は、`Formal.lean`、`docs/formal/lean_theorem_index.md`、
  必要なら `docs/proof_obligations.md` を同じ PR で更新する。

## #138 の結論

Issue #138 では、現行 layout を維持する。subdirectory 化は今すぐ行わない。
ただし、この文書の責務分類を当面の reader-facing module map とし、将来の file move は
単独 Issue / PR で扱う。
