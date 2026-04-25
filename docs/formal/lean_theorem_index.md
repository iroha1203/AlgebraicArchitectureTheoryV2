# Lean 定義・定理索引

この文書は、現在 Lean 側に存在する主要な定義・定理の索引である。

`proof_obligations.md` は未解決課題と実証仮説の台帳として扱い、この文書は実装済みの Lean API を確認する入口として扱う。

この索引は手動管理である。Lean 定義・定理を追加、削除、rename する PR では、研究上参照する主要 API に影響がある場合にこの文書も更新する。

## Graph / Walk

File: `Formal/Arch/Graph.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchGraph` | `structure` | component 間の依存辺 `edge : C -> C -> Prop` を持つ基本グラフ。 | `defined only` |
| `StaticDependencyGraph` | `abbrev` | 静的依存を表す graph role。 | `defined only` |
| `RuntimeDependencyGraph` | `abbrev` | 実行時依存を表す graph role。 | `defined only` |
| `ArchitectureDependencyGraphs` | `structure` | 静的依存と実行時依存を同時に保持する薄い構造。 | `defined only` |
| `Walk` | `inductive` | 長さを保持する依存 walk。 | `defined only` |
| `Walk.length` | `def` | walk の長さ。 | `defined only` |
| `Walk.vertices` | `def` | walk が通る頂点列。 | `defined only` |
| `Walk.vertices_length` | `theorem` | `vertices` と `length` の基本関係。 | `proved` |
| `SimpleWalk` | `structure` | 頂点重複のない walk。 | `defined only` |
| `SimpleWalk.vertices_length` | `theorem` | simple walk の頂点列と長さの基本関係。 | `proved` |

## Reachability

File: `Formal/Arch/Reachability.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Reachable` | `inductive` | 反射推移閉包としての到達可能性。 | `defined only` |
| `Reachable.refl'` | `theorem` | 任意 component は自身へ到達可能。 | `proved` |
| `Reachable.of_edge` | `theorem` | 依存辺から到達可能性を得る。 | `proved` |
| `Reachable.trans` | `def` | 到達可能性の推移性。 | `proved` |
| `Reachable.of_walk` | `def` | `Walk` から `Reachable` を得る。 | `proved` |
| `Reachable.of_simpleWalk` | `def` | `SimpleWalk` から `Reachable` を得る。 | `proved` |
| `Reachable.exists_path` | `theorem` | 到達可能なら simple path が存在する。 | `proved` |

## Layering / Acyclicity

File: `Formal/Arch/Layering.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Layering` | `abbrev` | component から `Nat` layer への関数。 | `defined only` |
| `StrictLayering` | `def` | 依存辺に沿って layer が厳密に下がること。 | `defined only` |
| `StrictLayered` | `def` | strict layering が存在すること。 | `defined only` |
| `Acyclic` | `def` | 依存辺 `c -> d` と `Reachable d c` が同時に成り立たないこと。 | `defined only` |
| `HasClosedWalk` | `def` | 閉 walk を持つこと。 | `defined only` |
| `WalkAcyclic` | `def` | 非自明な閉 walk が存在しないこと。 | `defined only` |
| `FinitePropagation` | `def` | 任意 component からの walk 長に上界があること。 | `defined only` |
| `layer_le_of_reachable` | `theorem` | strict layering 下で reachable な依存先の layer は増えない。 | `proved` |
| `acyclic_of_strictLayering` | `theorem` | strict layering は acyclicity を与える。 | `proved` |
| `strictLayered_acyclic` | `theorem` | `StrictLayered -> Acyclic`。 | `proved` |
| `walkAcyclic_of_acyclic` | `theorem` | `Acyclic -> WalkAcyclic`。 | `proved` |
| `acyclic_of_walkAcyclic` | `theorem` | `WalkAcyclic -> Acyclic`。 | `proved` |
| `acyclic_iff_walkAcyclic` | `theorem` | acyclicity と walk acyclicity の同値。 | `proved` |
| `finitePropagation_of_strictLayered` | `theorem` | `StrictLayered -> FinitePropagation`。 | `proved` |

## Decomposable

File: `Formal/Arch/Decomposable.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Decomposable` | `def` | 現在は `StrictLayered` として定義する。 | `defined only` |
| `decomposable_iff_strictLayered` | `theorem` | `Decomposable G <-> StrictLayered G`。 | `proved` |
| `decomposable_acyclic` | `theorem` | `Decomposable -> Acyclic`。 | `proved` |
| `decomposable_finitePropagation` | `theorem` | `Decomposable -> FinitePropagation`。 | `proved` |
| `FourLayerExample.decomposable` | `theorem` | 4層例が decomposable であること。 | `proved` |

## Thin Category

Files: `Formal/Arch/Category.lean`, `Formal/Arch/ThinCategory.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `SmallCategory` | `structure` | 最小限の category 構造。 | `defined only` |
| `SmallCategory.discrete` | `def` | 離散 category。 | `defined only` |
| `ComponentCategory` | `def` | `Reachable` を Hom にする component category。 | `defined only` |
| `componentCategory_thin` | `theorem` | `ComponentCategory` が thin category であること。 | `proved` |

`ComponentCategory` は path count や walk length を忘れる。定量指標は `Walk`, `SimpleWalk`, finite metrics, adjacency matrix 側で扱う。

## Projection / DIP

File: `Formal/Arch/Projection.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `InterfaceProjection` | `structure` | 具象 component から抽象 component への射影。 | `defined only` |
| `ProjectedDeps` | `def` | 具象依存を抽象依存へ写した関係。 | `defined only` |
| `ProjectionSound` | `abbrev` | 具象依存が抽象依存へ sound に写ること。 | `defined only` |
| `projectionSoundnessViolationEdges` | `def` | 有限な測定 universe 上で、abstract edge に写らない concrete edge のリスト。 | `defined only` |
| `mem_projectionSoundnessViolationEdges_iff` | `theorem` | projection soundness violation edge の membership が、測定対象 concrete edge かつ projected abstract edge 不在であることと一致する。 | `proved` |
| `projectionSoundnessViolation` | `def` | projection soundness に反する測定 concrete edge 数。 | `defined only` |
| `projectionSoundnessViolation_eq_zero_of_projectionSound` | `theorem` | `ProjectionSound` なら finite violation count は 0。 | `proved` |
| `projectionSound_of_projectionSoundnessViolation_eq_zero` | `theorem` | 測定 universe が concrete edge を閉じていれば、violation 0 から `ProjectionSound` を得る。 | `proved` |
| `ProjectionComplete` | `def` | 抽象依存が具象依存で代表されること。 | `defined only` |
| `ProjectionExact` | `def` | soundness と completeness の両方。 | `defined only` |
| `QuotientWellDefined` | `def` | 同じ抽象へ写る代表の依存が安定すること。 | `defined only` |
| `RepresentativeStable` | `abbrev` | 代表選択に対する安定性。 | `defined only` |
| `DIPCompatible` | `def` | `ProjectionSound` と `RepresentativeStable` を含む DIP 互換性。 | `defined only` |
| `StrongDIPCompatible` | `def` | `DIPCompatible` に `ProjectionComplete` を加えた強い互換性。 | `defined only` |
| `projectionSound_of_projectionExact` | `theorem` | exact projection から soundness を得る。 | `proved` |
| `projectionComplete_of_projectionExact` | `theorem` | exact projection から completeness を得る。 | `proved` |
| `dipCompatible_of_strongDIPCompatible` | `theorem` | strong DIP compatible なら DIP compatible。 | `proved` |
| `dipCompatible_id` | `theorem` | identity projection は DIP compatible。 | `proved` |
| `strongDIPCompatible_id` | `theorem` | identity projection は strong DIP compatible。 | `proved` |

## Observation / LSP

Files: `Formal/Arch/Observation.lean`, `Formal/Arch/LSP.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Observation` | `structure` | 実装を観測値へ写す観測関手風の構造。 | `defined only` |
| `ObservationallyEquivalent` | `def` | 観測値が一致すること。 | `defined only` |
| `ObservationallyEquivalent.refl` | `theorem` | 観測同値の反射性。 | `proved` |
| `ObservationallyEquivalent.symm` | `theorem` | 観測同値の対称性。 | `proved` |
| `ObservationallyEquivalent.trans` | `theorem` | 観測同値の推移性。 | `proved` |
| `LSPCompatibleAt` | `def` | 抽象と具象の一点ごとの LSP 互換性。 | `defined only` |
| `LSPCompatible` | `def` | 全体の LSP 互換性。 | `defined only` |
| `ObservationFactorsThrough` | `def` | 観測が抽象射影を通って factor すること。 | `defined only` |
| `ObservationallyDivergent` | `def` | 観測値が一致しない measured pair。 | `defined only` |
| `observationalDivergence` | `def` | measured pair ごとの観測差分を 0/1 で数える behavioral metric。 | `defined only` |
| `lspViolationPairs` | `def` | 有限な測定 universe 上で、同じ抽象に写るが観測が異なる ordered pair のリスト。 | `defined only` |
| `mem_lspViolationPairs_iff` | `theorem` | LSP violation pair の membership が、測定対象 pair・同一抽象・観測差分と一致する。 | `proved` |
| `lspViolationCount` | `def` | 有限な測定 universe 上の measured LSP violation 数。 | `defined only` |
| `observationalDivergence_eq_zero_of_equivalent` | `theorem` | 観測同値なら pair-level divergence は 0。 | `proved` |
| `observationallyEquivalent_of_observationalDivergence_eq_zero` | `theorem` | pair-level divergence 0 から観測同値を得る。 | `proved` |
| `lspAt_of_lsp` | `theorem` | 全体 LSP 互換性から一点ごとの互換性を得る。 | `proved` |
| `lspCompatibleAt_refl` | `theorem` | 同じ実装の LSP 互換性。 | `proved` |
| `lspObservation_symm` | `theorem` | 一点ごとの LSP 互換性から得た観測同値を反転する。 | `proved` |
| `lspCompatible_of_observationFactorsThrough` | `theorem` | 観測が射影を通って factor すれば LSP compatible。 | `proved` |
| `lspViolationCount_eq_zero_of_lspCompatible` | `theorem` | `LSPCompatible` なら finite LSP violation count は 0。 | `proved` |
| `lspViolationCount_eq_zero_of_observationFactorsThrough` | `theorem` | `ObservationFactorsThrough` なら finite LSP violation count は 0。 | `proved` |
| `lspCompatible_of_lspViolationCount_eq_zero` | `theorem` | 測定 universe が同一抽象 pair を閉じていれば、violation 0 から `LSPCompatible` を得る。 | `proved` |

## Signature v0

File: `Formal/Arch/Signature.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureSignature` | `structure` | v0 の多軸リスク signature。 | `defined only` |
| `ArchitectureSignature.RiskLE` | `def` | componentwise risk order。 | `defined only` |
| `ArchitectureSignature.riskLE_refl` | `theorem` | risk order の反射性。 | `proved` |
| `ArchitectureSignature.riskLE_trans` | `theorem` | risk order の推移性。 | `proved` |
| `ArchitectureSignature.riskLE_antisymm` | `theorem` | risk order の反対称性。 | `proved` |
| `ArchitectureSignature.reachesWithin` | `def` | fuel-bounded reachability。 | `defined only` |
| `ArchitectureSignature.hasCycleBool` | `def` | executable cycle indicator。 | `defined only` |
| `ArchitectureSignature.sccSizeAt` | `def` | component 周辺の相互到達 class size。 | `defined only` |
| `ArchitectureSignature.sccMaxSizeOfFinite` | `def` | finite universe 上の最大 SCC サイズ。 | `defined only` |
| `ArchitectureSignature.totalFanout` | `def` | finite universe 上の総 fanout。 | `defined only` |
| `ArchitectureSignature.measuredDependencyEdgesFromSource` | `def` | source component 固定で測定される依存辺ペア。 | `defined only` |
| `ArchitectureSignature.mem_measuredDependencyEdgesFromSource_iff` | `theorem` | source 固定の測定依存辺 membership が selected source からの graph edge と一致すること。 | `proved` |
| `ArchitectureSignature.fanout_eq_measuredDependencyEdgesFromSource_length` | `theorem` | component ごとの `fanout` が source 固定の測定依存辺数と一致すること。 | `proved` |
| `ArchitectureSignature.measuredDependencyEdges` | `def` | finite component list 上で測定される依存辺ペア。 | `defined only` |
| `ArchitectureSignature.mem_measuredDependencyEdges_iff` | `theorem` | 測定依存辺リストの membership が list 内の graph edge と一致すること。 | `proved` |
| `ArchitectureSignature.totalFanout_eq_measuredDependencyEdges_length` | `theorem` | `totalFanout` が測定依存辺数と一致すること。 | `proved` |
| `ArchitectureSignature.fanoutRiskOfFinite` | `def` | v0 の fanout risk。現在は `totalFanout`。 | `defined only` |
| `ArchitectureSignature.fanoutRiskOfFinite_eq_measuredDependencyEdges_length` | `theorem` | v0 `fanoutRisk` が測定依存辺数と一致すること。 | `proved` |
| `ArchitectureSignature.sccExcessSizeOfFinite` | `def` | v1 core の SCC excess metric。`sccMaxSizeOfFinite - 1`。 | `defined only` |
| `ArchitectureSignature.sccExcessAt` | `def` | component ごとの SCC excess metric。`sccSizeAt - 1`。 | `defined only` |
| `ArchitectureSignature.weightedSccContributionAt` | `def` | component ごとの `weight * sccExcessAt`。 | `defined only` |
| `ArchitectureSignature.weightedSccRiskOfFinite` | `def` | finite universe 上で重み付き SCC excess contribution を合計する v1 metric。 | `defined only` |
| `ArchitectureSignature.weightedSccRiskOfFinite_zero_weight` | `theorem` | すべての component weight が 0 なら weighted SCC risk も 0。 | `proved` |
| `ArchitectureSignature.weightedSccRiskOfFinite_unit_weight` | `theorem` | unit weight では weighted SCC risk が component ごとの SCC excess の和になること。 | `proved` |
| `ArchitectureSignature.maxFanoutOfFinite` | `def` | v1 core の局所 fanout 最大値 metric。 | `defined only` |
| `ArchitectureSignature.maxFanoutOfFinite_eq_max_measuredDependencyEdgesFromSource_length` | `theorem` | `maxFanoutOfFinite` が source ごとの測定依存辺数の最大値であること。 | `proved` |
| `ArchitectureSignature.reachableConeSizeAt` | `def` | v1 core の component ごとの strict bounded reachable cone size。 | `defined only` |
| `ArchitectureSignature.reachableConeSizeOfFinite` | `def` | v1 core の最大 strict bounded reachable cone size。 | `defined only` |
| `ArchitectureSignature.maxDepthOfFinite` | `def` | finite universe 上の bounded max depth。 | `defined only` |
| `ArchitectureSignature.v0OfFinite` | `def` | finite universe から v0 signature を計算する。 | `defined only` |
| `ArchitectureSignature.ArchitectureSignatureV1Core` | `structure` | v0 signature と Lean-measured v1 core axis を束ねる schema。 | `defined only` |
| `ArchitectureSignature.ArchitectureSignatureV1` | `structure` | v1 core と optional extension axis を束ねる output schema。 | `defined only` |
| `ArchitectureSignature.v1CoreOfFinite` | `def` | finite universe から v1 core signature を計算する。 | `defined only` |
| `ArchitectureSignature.v1OfFinite` | `def` | finite universe から v1 schema を作り、未評価 extension axis を `none` にする。 | `defined only` |
| `ArchitectureSignature.v1OfFiniteWithWeightedSccRisk` | `def` | 明示的な component weight から `weightedSccRisk` を埋めた v1 schema を作る。 | `defined only` |
| `ArchitectureSignature.runtimePropagationOfFinite` | `def` | 0/1 runtime graph 上の reachable cone size を `runtimePropagation` の最小 metric として計算する。 | `defined only` |
| `ArchitectureSignature.v1OfFiniteWithRuntimePropagation` | `def` | 静的 graph から v1 core を計算し、runtime graph から `runtimePropagation` axis を埋める。 | `defined only` |
| `ArchitectureSignature.v0_unitNoEdge` | `theorem` | 辺なし unit graph の v0 計算例。 | `proved` |
| `ArchitectureSignature.v0_unitSelfLoop` | `theorem` | self-loop unit graph の v0 計算例。 | `proved` |
| `ArchitectureSignature.v0_boolForward` | `theorem` | bool forward graph の v0 計算例。 | `proved` |
| `ArchitectureSignature.v1Core_unitNoEdge` | `theorem` | 辺なし unit graph の v1 core 計算例。 | `proved` |
| `ArchitectureSignature.v1CoreSchema_unitNoEdge` | `theorem` | 辺なし unit graph の v1 core schema 計算例。 | `proved` |
| `ArchitectureSignature.v1Schema_unitNoEdge_unmeasured` | `theorem` | 未評価 v1 extension axis が `none` に残る計算例。 | `proved` |
| `ArchitectureSignature.v1Core_boolForward` | `theorem` | bool forward graph の v1 core 計算例。 | `proved` |
| `ArchitectureSignature.weightedSccRisk_boolForward` | `theorem` | 非循環 bool forward graph では weighted SCC risk が 0 になる計算例。 | `proved` |
| `ArchitectureSignature.weightedSccRisk_boolCycle` | `theorem` | 2 component cycle では各 component の重みが 1 回ずつ寄与する計算例。 | `proved` |
| `ArchitectureSignature.v1Schema_boolCycle_weightedScc` | `theorem` | weighted SCC entry point が `weightedSccRisk` extension axis を埋める計算例。 | `proved` |
| `ArchitectureSignature.v1Schema_boolForward_runtimePropagation` | `theorem` | runtime propagation entry point が `runtimePropagation` extension axis を埋める計算例。 | `proved` |

## Finite Universe / Bridge Theorems

File: `Formal/Arch/Finite.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ComponentUniverse` | `structure` | finite measurement universe with proofs。 | `defined only` |
| `ComponentUniverse.full` | `def` | full coverage universe を作る。 | `defined only` |
| `ComponentUniverse.v0` | `def` | universe から v0 signature を計算する。 | `defined only` |
| `FiniteArchGraph` | `structure` | `ArchGraph` と `ComponentUniverse` を束ねる構造。 | `defined only` |
| `FiniteArchGraph.v0` | `def` | finite graph から v0 signature を計算する。 | `defined only` |
| `ComponentUniverse.reachable_exists_bounded_path` | `theorem` | finite universe 上で reachable なら bounded simple path がある。 | `proved` |
| `reachableBool_eq_true_iff` | `theorem` | executable reachable boolean と propositional reachable の接続。 | `proved` |
| `mutualReachableBool_eq_true_iff` | `theorem` | executable mutual reachability と proposition の接続。 | `proved` |
| `MutuallyReachable` | `def` | 相互到達可能性。 | `defined only` |
| `mutuallyReachable_refl` | `theorem` | 相互到達可能性の反射性。 | `proved` |
| `mutuallyReachable_symm` | `theorem` | 相互到達可能性の対称性。 | `proved` |
| `mutuallyReachable_trans` | `theorem` | 相互到達可能性の推移性。 | `proved` |
| `reachableCone` | `def` | finite list 内で、source 自身を除く graph-level reachable cone。 | `defined only` |
| `reachableConeSize` | `def` | graph-level strict reachable cone のサイズ。 | `defined only` |
| `mem_reachableCone_iff` | `theorem` | strict reachable cone の membership が list 内到達可能性と一致すること。 | `proved` |
| `reachesWithin_sound` | `theorem` | bounded reachability boolean の soundness。 | `proved` |
| `reachesWithin_complete_of_walk` | `theorem` | 明示的な walk と fuel bound から bounded reachability を得る。 | `proved` |
| `reachesWithin_complete_of_reachable_under_universe` | `theorem` | finite universe 下で reachable から bounded reachability を得る。 | `proved` |
| `reachesWithin_eq_reachableBool_under_universe` | `theorem` | bounded reachability と executable reachability の一致。 | `proved` |
| `sccSizeAt_eq_mutualReachableClassSize_under_universe` | `theorem` | SCC size executable metric と相互到達 class size の接続。 | `proved` |
| `sccMaxSizeOfFinite_eq_max_mutualReachableClassSize_under_universe` | `theorem` | max SCC metric と相互到達 class size 最大値の接続。 | `proved` |
| `sccExcessSizeOfFinite_eq_max_mutualReachableClassSize_sub_one_under_universe` | `theorem` | v1 core SCC excess metric と相互到達 class size 最大値から 1 を引いた値の接続。 | `proved` |
| `sccExcessSizeOfFinite_eq_zero_iff_sccMaxSizeOfFinite_le_one` | `theorem` | SCC excess metric が 0 になる境界条件を `sccMaxSizeOfFinite <= 1` として特徴づける。 | `proved` |
| `sccExcessSizeOfFinite_eq_zero_of_max_mutualReachableClassSize_le_one_under_universe` | `theorem` | finite universe 下で graph-level mutual-reachability class size 最大値が 1 以下なら SCC excess が 0 になること。 | `proved` |
| `reachableConeSizeAt_eq_reachableConeSize_under_universe` | `theorem` | executable bounded reachable cone size と graph-level strict reachable cone size の接続。 | `proved` |
| `reachableConeSizeOfFinite_eq_max_reachableConeSize_under_universe` | `theorem` | reachable cone metric が component ごとの graph-level strict reachable cone size 最大値であること。 | `proved` |
| `fanoutRiskOfFinite_eq_measuredDependencyEdges_length_under_universe` | `theorem` | finite universe 下で v0 `fanoutRisk` が測定依存辺数と一致すること。 | `proved` |
| `maxFanoutOfFinite_eq_max_measuredDependencyEdgesFromSource_length_under_universe` | `theorem` | finite universe 下で v1 core `maxFanout` が source ごとの測定依存辺数の最大値であること。 | `proved` |
| `hasClosedWalk_of_hasCycleBool` | `theorem` | executable cycle indicator から closed walk を得る。 | `proved` |
| `hasCycleBool_complete_of_hasClosedWalk` | `theorem` | closed walk から executable cycle indicator を得る。 | `proved` |
| `hasCycleBool_correct_under_finite_universe` | `theorem` | finite universe 下の cycle indicator correctness。 | `proved` |
| `maxDepthOfFinite_correct_of_acyclic` | `theorem` | acyclic finite graph 上の max depth correctness。 | `proved` |
| `ComponentUniverse.strictLayered_of_acyclic` | `theorem` | finite acyclic graph から strict layering を構成する。 | `proved` |
| `FiniteArchGraph.strictLayered_of_acyclic` | `theorem` | `FiniteArchGraph` 入口で finite acyclic graph から strict layering を得る。 | `proved` |

## Matrix Bridge

File: `Formal/Arch/Matrix.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `NatMatrix` | `abbrev` | finite universe の list-sum で冪を計算する自然数 entry の行列表現。 | `defined only` |
| `NatMatrix.id` | `def` | 単位行列。 | `defined only` |
| `NatMatrix.mul` | `def` | `ComponentUniverse.components` 上で和を取る行列積。 | `defined only` |
| `NatMatrix.pow` | `def` | finite universe 上の行列冪。 | `defined only` |
| `adjacencyMatrix` | `def` | `ArchGraph` の 0/1 adjacency matrix。 | `defined only` |
| `adjacencyPowerEntry` | `def` | adjacency matrix の `A^k` entry。 | `defined only` |
| `AdjacencyNilpotent` | `def` | 十分大きい adjacency matrix 冪がすべて 0 になること。 | `defined only` |
| `SpectralIndex` | `abbrev` | mathlib-backed spectral bridge 用の `Fin U.components.length` 添字。 | `defined only` |
| `SpectralIndex.component` | `def` | spectral matrix index が指す component を読む。 | `defined only` |
| `indexedAdjacencyMatrix` | `def` | `SpectralIndex U` 添字の自然数値 mathlib adjacency matrix。 | `defined only` |
| `spectralAdjacencyMatrix` | `def` | `Complex` 係数へ持ち上げた finite adjacency matrix。 | `defined only` |
| `spectralRadiusOfAdjacency` | `def` | finite complex adjacency matrix の spectral radius。 | `defined only` |
| `adjacencyPowerZeroOnComponentsBool` | `def` | finite measurement universe 上で `A^k` が 0 行列かを判定する executable test。 | `defined only` |
| `adjacencyPowerZeroOnComponentsBool_eq_true_iff` | `theorem` | executable zero test が measured entries の全 0 条件と一致する。 | `proved` |
| `adjacencyPowerZeroOnComponentsBool_iff_zero` | `theorem` | `ComponentUniverse.covers` の下で executable zero test が graph-level 全 0 条件と一致する。 | `proved` |
| `firstZeroPowerIndex` | `def` | 候補 power list から最初の zero adjacency power を返す。 | `defined only` |
| `nilpotencyIndexSearchBound` | `def` | executable `nilpotencyIndex` が探索する finite DAG-complete bound。 | `defined only` |
| `nilpotencyIndexOfFinite` | `def` | finite `ComponentUniverse` 上の executable nilpotency index candidate。 | `defined only` |
| `ArchitectureSignature.v1OfComponentUniverseWithNilpotencyIndex` | `def` | `ArchitectureSignatureV1.nilpotencyIndex` を matrix bridge から埋める entry point。 | `defined only` |
| `Walk.append` | `def` | walk の連結。 | `defined only` |
| `Walk.length_append` | `theorem` | walk 連結で長さが加法的になる。 | `proved` |
| `Walk.repeatClosed` | `def` | 閉 walk の繰り返し。 | `defined only` |
| `Walk.length_repeatClosed` | `theorem` | 閉 walk の繰り返しで長さが乗法的になる。 | `proved` |
| `adjacencyMatrix_pos_iff` | `theorem` | adjacency entry が正であることと辺の存在が一致する。 | `proved` |
| `indexedAdjacencyMatrix_pow_apply` | `theorem` | mathlib-indexed matrix powers が既存の `adjacencyPowerEntry` と一致する。 | `proved` |
| `spectralAdjacencyMatrix_pow_apply` | `theorem` | complex spectral adjacency matrix powers が `adjacencyPowerEntry` の coercion と一致する。 | `proved` |
| `adjacencyPowerEntry_pos_iff_walk_length` | `theorem` | `A^k` entry が正であることと長さ `k` の walk の存在が一致する。 | `proved` |
| `adjacencyNilpotent_of_acyclic` | `theorem` | finite acyclic graph では adjacency matrix が冪零になる。 | `proved` |
| `adjacencyPowerEntry_zero_at_acyclic_cutoff` | `theorem` | finite acyclic graph では `A^(components.length + 1)` の全 entry が 0 になる。 | `proved` |
| `indexedAdjacencyMatrix_pow_zero_at_acyclic_cutoff` | `theorem` | finite acyclic graph では mathlib-indexed natural adjacency matrix の cutoff power が 0 になる。 | `proved` |
| `spectralAdjacencyMatrix_pow_zero_at_acyclic_cutoff` | `theorem` | finite acyclic graph では complex adjacency matrix の cutoff power が 0 になる。 | `proved` |
| `spectralAdjacencyMatrix_isNilpotent_of_acyclic` | `theorem` | finite acyclic graph では complex adjacency matrix が冪零になる。 | `proved` |
| `spectralRadius_eq_zero_of_matrix_pow_eq_zero` | `theorem` | positive zero power を持つ complex matrix の spectral radius が 0 になる。 | `proved` |
| `matrix_isNilpotent_of_spectralRadius_eq_zero` | `theorem` | finite complex matrix で spectral radius が 0 なら冪零になる。 | `proved` |
| `spectralRadius_pos_of_matrix_not_isNilpotent` | `theorem` | finite complex matrix が非冪零なら spectral radius が正になる。 | `proved` |
| `spectralRadiusOfAdjacency_eq_zero_of_acyclic` | `theorem` | finite acyclic graph では complex adjacency matrix の spectral radius が 0 になる。 | `proved` |
| `spectralAdjacencyMatrix_not_isNilpotent_of_hasClosedWalk` | `theorem` | 非空閉 walk を持つ finite graph では complex adjacency matrix が冪零でない。 | `proved` |
| `spectralRadiusOfAdjacency_pos_of_hasClosedWalk` | `theorem` | 非空閉 walk を持つ finite graph では complex adjacency matrix の spectral radius が正になる。 | `proved` |
| `nilpotencyIndexOfFinite_isSome_of_acyclic` | `theorem` | finite acyclic graph では executable `nilpotencyIndex` が `some` になる。 | `proved` |
| `walkAcyclic_of_adjacencyNilpotent` | `theorem` | adjacency nilpotence から非空閉 walk が存在しないことを得る。 | `proved` |
| `acyclic_of_adjacencyNilpotent` | `theorem` | adjacency nilpotence から graph-level acyclicity を得る。 | `proved` |
| `adjacencyNilpotent_iff_walkAcyclic` | `theorem` | finite universe 上で adjacency nilpotence と `WalkAcyclic` が一致する。 | `proved` |
| `adjacencyNilpotent_iff_acyclic` | `theorem` | finite universe 上で adjacency nilpotence と `Acyclic` が一致する。 | `proved` |
| `ArchitectureSignature.Examples.nilpotencyIndex_boolForward` | `theorem` | one-way Boolean graph の executable nilpotency index が `some 2` になる計算例。 | `proved` |
| `ArchitectureSignature.Examples.nilpotencyIndex_boolCycle` | `theorem` | two-component cycle graph の executable nilpotency index が `none` になる計算例。 | `proved` |
| `ArchitectureSignature.Examples.v1Schema_boolForward_nilpotencyIndex` | `theorem` | matrix-bridge v1 entry point が `nilpotencyIndex` を埋める計算例。 | `proved` |
| `FiniteArchGraph.adjacencyNilpotent_of_acyclic` | `theorem` | `FiniteArchGraph` 入口で acyclicity から adjacency nilpotence を得る。 | `proved` |
| `FiniteArchGraph.acyclic_of_adjacencyNilpotent` | `theorem` | `FiniteArchGraph` 入口で adjacency nilpotence から acyclicity を得る。 | `proved` |

## SOLID Counterexamples

File: `Formal/Arch/SolidCounterexample.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `TwoCycleComponent.not_decomposable` | `theorem` | 2点循環グラフが decomposable でないこと。 | `proved` |
| `PaymentComponent.not_decomposable` | `theorem` | 局所契約風データを持つ循環例が decomposable でないこと。 | `proved` |
| `AbstractCycleComponent.not_decomposable` | `theorem` | 抽象層循環例が decomposable でないこと。 | `proved` |
| `StrongAbstractCycleComponent.observation_factors` | `theorem` | 強い抽象層循環例の observation factorization。 | `proved` |
| `StrongAbstractCycleComponent.lspCompatible` | `theorem` | 強い抽象層循環例が LSP compatible であること。 | `proved` |
| `StrongAbstractCycleComponent.abstractGraph_not_decomposable` | `theorem` | 抽象 port-level cycle graph が decomposable でないこと。 | `proved` |
| `StrongAbstractCycleComponent.projectionSound` | `theorem` | 強い抽象層循環例の projection soundness。 | `proved` |
| `StrongAbstractCycleComponent.projectionComplete` | `theorem` | 強い抽象層循環例の projection completeness。 | `proved` |
| `StrongAbstractCycleComponent.projectionExact` | `theorem` | 強い抽象層循環例の exact projection。 | `proved` |
| `StrongAbstractCycleComponent.representativeStable` | `theorem` | 強い抽象層循環例の representative stability。 | `proved` |
| `StrongAbstractCycleComponent.dipCompatible` | `theorem` | 強い抽象層循環例が DIP compatible であること。 | `proved` |
| `StrongAbstractCycleComponent.strongDIPCompatible` | `theorem` | 強い抽象層循環例が strong DIP compatible であること。 | `proved` |
| `StrongAbstractCycleComponent.not_decomposable` | `theorem` | strong DIP / LSP 互換でも decomposable は従わないこと。 | `proved` |
| `StrongAbstractCycleComponent.dipCompatible_and_not_decomposable` | `theorem` | DIP compatible と `¬ Decomposable` が同時に成立すること。 | `proved` |
| `StrongAbstractCycleComponent.strongDIPCompatible_and_not_decomposable` | `theorem` | strong DIP compatible と `¬ Decomposable` が同時に成立すること。 | `proved` |

## 現在 Lean に入れていないもの

次は意図的に Lean core へ混ぜていない。

- `Decomposable` の定義への acyclicity, finite propagation, nilpotence, spectral conditions の混入。
- `relationComplexity`, `runtimePropagation`, `empiricalChangeCost` の実証相関。
- extractor output が `ComponentUniverse` の完全な witness であるという主張。
- `rho(A)` と変更波及・障害伝播コストの相関。

これらは [証明義務と実証仮説](../proof_obligations.md) または [個別設計メモ](../design/README.md) で扱う。
