# Lean 定義・定理索引

この文書は、現在 Lean 側に存在する主要な定義・定理の索引である。

`proof_obligations.md` は未解決課題と実証仮説の台帳として扱い、この文書は実装済みの Lean API を確認する入口として扱う。

この索引は手動管理である。Lean 定義・定理を追加、削除、rename する PR では、研究上参照する主要 API に影響がある場合にこの文書も更新する。

`Formal/Arch` 以下の責務分類、file move の判断基準、当面の配置ルールは
[Lean module 階層整理方針](formal/lean_module_organization.md) に分離する。

## 索引の読み方

この索引は、数学設計書の theorem 候補をそのまま現在の Lean proved claim に
昇格するための文書ではない。Lean 実装済み API の入口であり、Lean status と
未解決 proof obligation の境界は
[証明義務と実証仮説](proof_obligations.md) で管理する。

各表の `Status` は declaration 単位の状態である。`proved` には、主定理だけでなく、
schema field を取り出す accessor theorem、定義間の bridge theorem、有限例の
example theorem、bounded completeness theorem が含まれる。研究上の主張として読む場合は、
各節の Non-conclusions と `proof_obligations.md` の coverage / exactness assumptions を
併せて確認する。

特に `defined only` / `proved` が同じ領域に並ぶ場合、carrier schema は
`defined only`、その schema に相対化された一部の theorem package が `proved` である。
この区別により、数学設計書を純粋な設計書として保ちつつ、Lean source 側の作業状態を
この索引と `proof_obligations.md` に分離する。

## Graph / Walk

File: `Formal/Arch/Graph.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchGraph` | `structure` | component 間の依存辺 `edge : C -> C -> Prop` を持つ基本グラフ。 | `defined only` |
| `EdgeSubset` | `def` | 依存削除・部分グラフ化を、片方の graph の全 edge がもう片方に含まれる関係として表す。 | `defined only` |
| `EdgeSubset.refl` | `theorem` | 任意 graph は自身の edge subset である。 | `proved` |
| `EdgeSubset.trans` | `theorem` | edge subset 関係は推移的である。 | `proved` |
| `StaticDependencyGraph` | `abbrev` | 静的依存を表す graph role。 | `defined only` |
| `RuntimeDependencyGraph` | `abbrev` | 実行時依存を表す graph role。 | `defined only` |
| `ArchitectureDependencyGraphs` | `structure` | 静的依存と実行時依存を同時に保持する薄い構造。 | `defined only` |
| `Walk` | `inductive` | 長さを保持する依存 walk。 | `defined only` |
| `Walk.length` | `def` | walk の長さ。 | `defined only` |
| `Walk.map_edgeSubset` | `def` | edge subset に沿って小さい graph の walk を大きい graph の walk へ写す。 | `proved` |
| `Walk.length_map_edgeSubset` | `theorem` | edge subset に沿って写した walk の長さは保存される。 | `proved` |
| `Walk.vertices` | `def` | walk が通る頂点列。 | `defined only` |
| `Walk.vertices_length` | `theorem` | `vertices` と `length` の基本関係。 | `proved` |
| `SimpleWalk` | `structure` | 頂点重複のない walk。 | `defined only` |
| `Path` | `abbrev` | 現時点では `SimpleWalk` の別名。bounded reachability で使う path representative。 | `defined only` |
| `SimpleWalk.vertices_length` | `theorem` | simple walk の頂点列と長さの基本関係。 | `proved` |

## Reachability

File: `Formal/Arch/Reachability.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Reachable` | `inductive` | 反射推移閉包としての到達可能性。 | `defined only` |
| `Reachable.refl'` | `theorem` | 任意 component は自身へ到達可能。 | `proved` |
| `Reachable.of_edge` | `theorem` | 依存辺から到達可能性を得る。 | `proved` |
| `Reachable.trans` | `def` | 到達可能性の推移性。 | `proved` |
| `Reachable.map_edgeSubset` | `def` | edge subset に沿って小さい graph の reachability を大きい graph の reachability へ写す。 | `proved` |
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
| `strictLayering_of_edgeSubset` | `theorem` | edge subset restriction は特定の strict layer assignment を保存する。 | `proved` |
| `strictLayered_of_edgeSubset` | `theorem` | edge subset restriction は `StrictLayered` を保存する。 | `proved` |
| `layer_le_of_reachable` | `theorem` | strict layering 下で reachable な依存先の layer は増えない。 | `proved` |
| `acyclic_of_strictLayering` | `theorem` | strict layering は acyclicity を与える。 | `proved` |
| `strictLayered_acyclic` | `theorem` | `StrictLayered -> Acyclic`。 | `proved` |
| `acyclic_of_edgeSubset` | `theorem` | edge subset restriction は `Acyclic` を保存する。 | `proved` |
| `walkAcyclic_of_acyclic` | `theorem` | `Acyclic -> WalkAcyclic`。 | `proved` |
| `acyclic_of_walkAcyclic` | `theorem` | `WalkAcyclic -> Acyclic`。 | `proved` |
| `acyclic_iff_walkAcyclic` | `theorem` | acyclicity と walk acyclicity の同値。 | `proved` |
| `finitePropagation_of_strictLayered` | `theorem` | `StrictLayered -> FinitePropagation`。 | `proved` |

有限 universe と decidable edge relation を明示した逆向き bridge は
`Formal/Arch/Finite.lean` の `ComponentUniverse.strictLayered_of_acyclic` と
`FiniteArchGraph.strictLayered_of_acyclic` として索引する。これは static graph
layering の theorem であり、semantic contract や runtime protocol の一般的な
decomposability を結論しない。

## Decomposable

File: `Formal/Arch/Decomposable.lean`

現在の Lean core における `Decomposable` は、`StrictLayered` と同義の
static / strict-layer decomposability である。semantic contract、runtime protocol、
event bus、pub-sub、局所化された相互再帰などを含む一般の分解可能性を主張しない。
有限 acyclic graph からこの static decomposability に戻る方向は、
`ComponentUniverse.strictLayered_of_acyclic` / `FiniteArchGraph.strictLayered_of_acyclic`
により、finite universe と decidable edge relation の前提に相対化して扱う。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Decomposable` | `def` | 現在は `StrictLayered` として定義する。 | `defined only` |
| `decomposable_iff_strictLayered` | `theorem` | `Decomposable G <-> StrictLayered G`。 | `proved` |
| `decomposable_acyclic` | `theorem` | `Decomposable -> Acyclic`。 | `proved` |
| `decomposable_finitePropagation` | `theorem` | `Decomposable -> FinitePropagation`。 | `proved` |
| `decomposable_of_edgeSubset` | `theorem` | edge subset restriction は `Decomposable` を保存する。 | `proved` |
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
| `AbstractGraph` | `abbrev` | 射影先の抽象依存グラフ。 | `defined only` |
| `ProjectedDeps` | `def` | 具象依存を抽象依存へ写した関係。 | `defined only` |
| `RespectsProjection` | `def` | すべての具象依存 edge が抽象 edge として表現されること。 | `defined only` |
| `ProjectionSound` | `abbrev` | 具象依存が抽象依存へ sound に写ること。 | `defined only` |
| `projectionSoundnessCandidateEdges` | `def` | finite measurement universe から projection obstruction candidate edge を列挙する。 | `defined only` |
| `ProjectionObstruction` | `def` | 抽象 edge に写らない具象 edge を projection obstruction witness として表す。 | `defined only` |
| `NoProjectionObstruction` | `def` | graph-level に projection obstruction witness が存在しないこと。 | `defined only` |
| `projectionSoundnessViolationEdges` | `def` | 有限な測定 universe 上で、abstract edge に写らない concrete edge のリスト。 | `defined only` |
| `mem_projectionSoundnessViolationEdges_iff` | `theorem` | projection soundness violation edge の membership が、測定対象 concrete edge かつ projected abstract edge 不在であることと一致する。 | `proved` |
| `mem_projectionSoundnessCandidateEdges_iff` | `theorem` | projection candidate edge の membership が、両端点が finite measurement universe に含まれることと一致する。 | `proved` |
| `mem_projectionSoundnessViolationEdges_iff_mem_violatingWitnesses` | `theorem` | 既存 projection violation list の membership が generic `violatingWitnesses` の特殊例であることを示す。 | `proved` |
| `projectionSoundnessViolation` | `def` | projection soundness に反する測定 concrete edge 数。 | `defined only` |
| `projectionSound_iff_noProjectionObstruction` | `theorem` | `ProjectionSound` と projection obstruction witness 不在が同値。 | `proved` |
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
| `projectedConcreteEdge_of_projectionComplete` | `theorem` | completeness から抽象 edge の具体 edge witness を得る。 | `proved` |
| `abstractEdge_iff_projectedConcreteEdge_of_projectionExact` | `theorem` | exact projection の下で抽象 edge と投影された具体 edge witness が同値。 | `proved` |
| `strongDIPCompatible_of_projectionExact_representativeStable` | `theorem` | `ProjectionExact` と `RepresentativeStable` を bundled `StrongDIPCompatible` へまとめる。 | `proved` |
| `projectionExact_of_strongDIPCompatible` | `theorem` | `StrongDIPCompatible` から exact projection を取り出す。 | `proved` |
| `representativeStable_of_strongDIPCompatible` | `theorem` | `StrongDIPCompatible` から representative stability を取り出す。 | `proved` |
| `quotientWellDefined_of_projectionExact_representativeStable` | `theorem` | exact projection と representative stability から quotient well-definedness を得る。 | `proved` |
| `quotientWellDefined_of_strongDIPCompatible` | `theorem` | strong DIP compatibility から quotient well-definedness を得る。 | `proved` |
| `projectedDeps_iff_abstractEdge_of_projectionExact_representativeStable` | `theorem` | exact projection と representative stability の下で、選択代表の `ProjectedDeps` と abstract edge が同値になる。 | `proved` |
| `projectedDeps_iff_abstractEdge_of_strongDIPCompatible` | `theorem` | strong DIP compatibility の下で、選択代表の projected dependency を abstract edge として読む。 | `proved` |
| `dipCompatible_of_strongDIPCompatible` | `theorem` | strong DIP compatible なら DIP compatible。 | `proved` |
| `respectsProjection_id` | `theorem` | identity projection は元の graph を respect する。 | `proved` |
| `quotientWellDefined_id` | `theorem` | identity projection は quotient well-defined。 | `proved` |
| `dipCompatible_id` | `theorem` | identity projection は DIP compatible。 | `proved` |
| `projectionComplete_id` | `theorem` | identity projection は complete。 | `proved` |
| `projectionExact_id` | `theorem` | identity projection は exact。 | `proved` |
| `strongDIPCompatible_id` | `theorem` | identity projection は strong DIP compatible。 | `proved` |
| `mapReachable` | `def` | projection soundness の下で具象到達可能性を抽象到達可能性へ写す。 | `proved` |

## Observation / LSP

Files: `Formal/Arch/Observation.lean`, `Formal/Arch/LSP.lean`, `Formal/Arch/LocalReplacement.lean`

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
| `lspCandidatePairs` | `def` | finite measurement universe から LSP obstruction candidate pair を列挙する。 | `defined only` |
| `LSPObstruction` | `def` | 同じ抽象 fiber 内で観測が異なる ordered pair を LSP obstruction witness として表す。 | `defined only` |
| `NoLSPObstruction` | `def` | implementation-pair level に LSP obstruction witness が存在しないこと。 | `defined only` |
| `observationalDivergence` | `def` | measured pair ごとの観測差分を 0/1 で数える behavioral metric。 | `defined only` |
| `lspViolationPairs` | `def` | 有限な測定 universe 上で、同じ抽象に写るが観測が異なる ordered pair のリスト。 | `defined only` |
| `mem_lspViolationPairs_iff` | `theorem` | LSP violation pair の membership が、測定対象 pair・同一抽象・観測差分と一致する。 | `proved` |
| `mem_lspCandidatePairs_iff` | `theorem` | LSP candidate pair の membership が、両要素が finite measurement universe に含まれることと一致する。 | `proved` |
| `mem_lspViolationPairs_iff_mem_violatingWitnesses` | `theorem` | 既存 LSP violation list の membership が generic `violatingWitnesses` の特殊例であることを示す。 | `proved` |
| `lspViolationCount` | `def` | 有限な測定 universe 上の measured LSP violation 数。 | `defined only` |
| `observationalDivergence_eq_zero_of_equivalent` | `theorem` | 観測同値なら pair-level divergence は 0。 | `proved` |
| `observationallyEquivalent_of_observationalDivergence_eq_zero` | `theorem` | pair-level divergence 0 から観測同値を得る。 | `proved` |
| `lspAt_of_lsp` | `theorem` | 全体 LSP 互換性から一点ごとの互換性を得る。 | `proved` |
| `lspCompatibleAt_refl` | `theorem` | 同じ実装の LSP 互換性。 | `proved` |
| `lspObservation_symm` | `theorem` | 一点ごとの LSP 互換性から得た観測同値を反転する。 | `proved` |
| `lspCompatible_of_observationFactorsThrough` | `theorem` | 観測が射影を通って factor すれば LSP compatible。 | `proved` |
| `lspCompatible_iff_noLSPObstruction` | `theorem` | `LSPCompatible` と LSP obstruction witness 不在が同値。 | `proved` |
| `lspViolationCount_eq_zero_of_lspCompatible` | `theorem` | `LSPCompatible` なら finite LSP violation count は 0。 | `proved` |
| `lspViolationCount_eq_zero_of_observationFactorsThrough` | `theorem` | `ObservationFactorsThrough` なら finite LSP violation count は 0。 | `proved` |
| `lspCompatible_of_lspViolationCount_eq_zero` | `theorem` | 測定 universe が同一抽象 pair を閉じていれば、violation 0 から `LSPCompatible` を得る。 | `proved` |
| `LocalReplacementContract` | `def` | `DIPCompatible` と `ObservationFactorsThrough` を同じ `InterfaceProjection` 上で束ねる局所置換契約。 | `defined only` |
| `projectionSound_of_localReplacementContract` | `theorem` | 局所置換契約から projection soundness を得る。 | `proved` |
| `observationFactorsThrough_of_localReplacementContract` | `theorem` | 局所置換契約から observation factorization を得る。 | `proved` |
| `lspCompatible_of_localReplacementContract` | `theorem` | 局所置換契約から同一 interface fiber 上の observation preservation を得る。 | `proved` |
| `observationallyEquivalent_of_localReplacementContract` | `theorem` | 同じ interface に expose される2実装が局所置換契約の下で observationally equivalent であることを得る。 | `proved` |
| `localReplacementContract_iff_noProjectionObstruction_and_representativeStable_and_observationFactorsThrough` | `theorem` | 局所置換契約を projection obstruction 不在、representative stability、observation factorization に分解する。 | `proved` |
| `noProjectionObstruction_and_noLSPObstruction_of_localReplacementContract` | `theorem` | 局所置換契約から projection obstruction と LSP obstruction の同時消滅を得る。 | `proved` |
| `violationCounts_eq_zero_of_localReplacementContract` | `theorem` | 局所置換契約から projection soundness violation count と LSP violation count が同時に 0 になることを得る。 | `proved` |

## Feature Extension

Issue [#243](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/243)
の feature extension 最小コアは、`FeatureExtension`、`Flatness`,
`ArchitecturePath`, `DiagramFiller` の四つの module に分かれる。この節以降は、
first-class feature addition schema、coverage-aware flatness、有限 path calculus、
semantic diagram filler の順に、Lean 上で参照できる主要 API を索引する。

FeatureExtension 周辺の公開 API は、責務ごとに次の module へ分離している。
`FeatureExtension.lean` は first-class feature addition と静的 split predicate、
`SplitExtensionLifting.lean` は observation-relative な featureView / section law、
`Flatness.lean` は extension coverage witness と bounded flatness preservation package
を担当する。この分離により、static split、feature observation、coverage failure、
runtime / semantic split evidence を混同しない。

| 設計語彙 | Lean 入口 | Status | 境界 |
| --- | --- | --- | --- |
| Static split feature extension | `StaticSplitFeatureExtension`, `SelectedStaticSplitExtension`, `StaticExtensionWitness` | `defined only` / `proved` | selected static split law とその witness に限る。runtime / semantic flatness、extractor completeness は主張しない。 |
| featureView observation law | `FeatureViewSound`, `FeatureObservationCoverage`, `FeatureViewSectionPackage` | `defined only` / `proved` | selected observation model に相対化する。strict equality、全 component の一意分解、global split completeness は主張しない。 |
| Extension coverage failure | `ExtensionCoverageWitness`, `ExtensionCoverageFailureCoverage` | `defined only` / `proved` | supplied `ComponentUniverse` 上の coverage-only 診断であり、static split law failure とは別に扱う。 |
| SplitFeatureExtensionWithin preservation package | `SplitFeatureExtensionWithin`, `architectureFlatWithin_of_splitFeatureExtensionWithin` | `defined only` / `proved` | extension coverage、static side conditions、runtime / semantic split evidence を明示前提にした bounded `ArchitectureFlatWithin` への入口であり、global `ArchitectureFlat` へは昇格しない。 |

File: `Formal/Arch/FeatureExtension.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `FeatureExtension` | `structure` | 既存 core、feature、拡大後 architecture、core embedding、feature embedding、observation model 相対の `featureView`、保存条件・相互作用条件・coverage・proof obligation を束ねる feature extension schema。 | `defined only` |
| `FeatureExtension.CoreEmbedded` | `def` | 拡大後 component が既存 core から埋め込まれたことを表す。 | `defined only` |
| `FeatureExtension.FeatureOwned` | `def` | 拡大後 component が追加 feature に所有されることを表す。 | `defined only` |
| `FeatureExtension.featureOwned_featureEmbedding` | `theorem` | `featureEmbedding` された component は feature-owned component である。 | `proved` |
| `FeatureExtension.coreEmbedded_coreEmbedding` | `theorem` | `coreEmbedding` された component は core-embedded component である。 | `proved` |
| `CoreEdgesPreserved` | `def` | 既存 core の静的 edge が拡大後 graph 上で保存されること。 | `defined only` |
| `EdgeFactorsThroughDeclaredInterface` | `def` | 依存 edge が宣言済み interface component を経由して factor すること。 | `defined only` |
| `CrossesFeatureCoreBoundary` | `def` | edge が feature-owned component と core-embedded component の境界を跨ぐこと。 | `defined only` |
| `DeclaredInterfaceFactorization` | `def` | feature/core 間の静的 interaction が宣言済み interface component を経由すること。 | `defined only` |
| `NoNewForbiddenStaticEdge` | `def` | 拡大後の静的 edge が supplied policy を満たすこと。 | `defined only` |
| `EmbeddingPolicyPreserved` | `def` | core 側 policy が embedding 後の extended policy として保存されること。 | `defined only` |
| `StaticSplitFeatureExtension` | `structure` | core edge preservation、declared interface factorization、forbidden static edge absence、policy preservation を束ねる静的 split extension schema。 | `defined only` |
| `StaticSplitExtension` | `abbrev` | `StaticSplitFeatureExtension` の短縮名。 | `defined only` |
| `SelectedStaticSplitExtension` | `structure` | 固定された feature extension と policy parameters に対し、静的 split の4条件を unbundled predicate として束ねる。runtime / semantic / extractor completeness は含めない。 | `defined only` |
| `selectedStaticSplitExtension_of_staticSplitFeatureExtension` | `theorem` | 既存の bundled `StaticSplitFeatureExtension` から selected static split predicate を得る。 | `proved` |
| `staticSplitFeatureExtension_of_selectedStaticSplitExtension` | `def` | selected static split predicate を既存の bundled schema に戻す。 | `defined only` |
| `identityFeatureExtension` | `def` | no-feature の identity extension。extended graph は元の core graph と同一で、feature component を追加しない。 | `defined only` |
| `identityFeatureExtension_coreEdgesPreserved` | `theorem` | identity extension では core edge preservation が反射的に成立する。 | `proved` |
| `identityFeatureExtension_not_crossesFeatureCoreBoundary` | `theorem` | no-feature identity extension では feature/core boundary crossing が存在しない。 | `proved` |
| `identityStaticSplitFeatureExtension` | `def` | 既存 graph が selected static policy を満たす前提から identity static split package を構成する。 | `defined only` |
| `selectedStaticSplitExtension_identity` | `theorem` | identity static split package から selected static split predicate を得る。 | `proved` |
| `composeFeatureExtension` | `def` | 二段の feature extension を、第一段の extended component を第二段の core として読む合成 schema。 | `defined only` |
| `StaticSplitCompositionAssumptions` | `structure` | static split composition に必要な graph compatibility、interface factorization、policy transport 前提を束ねる。 | `defined only` |
| `staticSplitFeatureExtension_compose` | `def` | 明示された compatibility 前提の下で、二段の static split extension から合成 static split package を構成する。 | `defined only` |
| `selectedStaticSplitExtension_compose` | `theorem` | 明示された compatibility 前提の下で、合成 extension が selected static split predicate を満たす。 | `proved` |
| `StaticExtensionWitness` | `inductive` | core edge preservation、declared interface factorization、no-new-forbidden-edge、embedding policy preservation の失敗を表す selected static diagnostic witness family。 | `defined only` |
| `StaticExtensionWitnessExists` | `def` | selected static diagnostic witness が存在すること。 | `defined only` |
| `StaticSplitFailureCoverage` | `def` | selected static split 失敗が selected witness family で cover されるという bounded coverage / exactness 前提。global completeness は主張しない。 | `defined only` |
| `not_selectedStaticSplitExtension_of_staticExtensionWitness` | `theorem` | selected static witness が対応する selected static split predicate を反証する soundness theorem。 | `proved` |
| `not_selectedStaticSplitExtension_of_staticExtensionWitnessExists` | `theorem` | selected static witness の存在から selected static split predicate の不成立を得る。 | `proved` |
| `staticExtensionWitnessExists_of_not_selectedStaticSplitExtension` | `theorem` | `StaticSplitFailureCoverage` 前提の下で、selected static split predicate の失敗から selected witness の存在を得る bounded completeness theorem。 | `proved` |
| `staticExtensionWitnessExists_iff_not_selectedStaticSplitExtension` | `theorem` | selected coverage / exactness 前提に相対化された、selected witness 存在と selected static split 失敗の同値。 | `proved` |

Non-conclusions: `staticSplitFeatureExtension_compose` は graph compatibility、
interface factorization、policy transport を明示前提とする bounded な composition law である。
runtime flatness、semantic flatness、global `ArchitectureFlat`、extractor completeness、
無条件の global composition law は主張しない。

File: `Formal/Arch/FeatureExtensionExamples.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `CouponStaticDependencyExample.CoreComponent` | `inductive` | coupon feature extension 例の core 側有限 component skeleton。 | `defined only` |
| `CouponStaticDependencyExample.FeatureComponent` | `inductive` | coupon feature extension 例の feature 側有限 component skeleton。 | `defined only` |
| `CouponStaticDependencyExample.ExtendedComponent` | `inductive` | `CouponService`、`PaymentAdapter.internalCache` 相当、declared payment port を含む extended component skeleton。 | `defined only` |
| `CouponStaticDependencyExample.goodExtension` | `def` | declared payment port 経由の good static extension。 | `defined only` |
| `CouponStaticDependencyExample.badExtension` | `def` | `CouponService -> internalCache` の hidden dependency を含む bad static extension。 | `defined only` |
| `CouponStaticDependencyExample.repairedExtension` | `def` | hidden direct edge を declared payment port 経由へ戻した repaired static extension。 | `defined only` |
| `CouponStaticDependencyExample.goodStaticSplitFeatureExtension` | `def` | good extension が `StaticSplitFeatureExtension` を満たす bundled package。 | `defined only` |
| `CouponStaticDependencyExample.good_selectedStaticSplitFeatureExtension` | `theorem` | good extension から selected static split predicate を得る。 | `proved` |
| `CouponStaticDependencyExample.featureObservation` | `def` | coupon feature の selected feature observation。 | `defined only` |
| `CouponStaticDependencyExample.extensionOf_featureViewSound` | `theorem` | coupon extension family の declared feature embedding が selected feature observation と一致して観測されることを示す。 | `proved` |
| `CouponStaticDependencyExample.good_featureObservationCoverage` | `theorem` | good coupon extension が feature-owned representative による selected feature observation coverage を持つことを示す。 | `proved` |
| `CouponStaticDependencyExample.hiddenDependencyWitness` | `def` | bad extension の `CouponService -> PaymentAdapter.internalCache` 相当の unfactored boundary edge witness。 | `defined only` |
| `CouponStaticDependencyExample.hiddenDependencyWitnessExists` | `theorem` | bad extension に selected static witness が存在することを示す。 | `proved` |
| `CouponStaticDependencyExample.bad_not_selectedStaticSplitFeatureExtension` | `theorem` | hidden dependency witness から selected static split failure を得る。 | `proved` |
| `CouponStaticDependencyExample.repairedStaticSplitFeatureExtension` | `def` | repair 後 extension が `StaticSplitFeatureExtension` を満たす bundled package。 | `defined only` |
| `CouponStaticDependencyExample.repaired_selectedStaticSplitFeatureExtension` | `theorem` | repair 後 extension で selected static split が回復することを示す。 | `proved` |

Non-conclusions: coupon static canonical example は静的 split と selected hidden dependency
witness に限る。runtime flatness、semantic flatness、extractor completeness は主張しない。

## Split Extension Lifting

File: `Formal/Arch/SplitExtensionLifting.lean`

Issue [#264](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/264)
と Issue [#372](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/372)
の対象範囲は、strict fibration ではなく observation model に相対化された
feature section / core retraction、featureView law package、selected feature step の bounded lifting である。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `FeatureSectionLaw` | `def` | `q ∘ s ≈ id` を、extended 側 `featureView` と feature 側 selected observation の一致として表す observation-relative section law。 | `defined only` |
| `FeatureViewSound` | `def` | declared `featureEmbedding` 後の component が selected feature observation と一致して観測されることを表す observation-relative soundness。 | `defined only` |
| `FeatureObservationCoverage` | `def` | 各 feature observation が feature-owned extended representative を持つことを表す selected coverage。global split completeness は主張しない。 | `defined only` |
| `FeatureViewSectionPackage` | `structure` | selected `featureView` section と `FeatureSectionLaw` を公開語彙として束ねる package。 | `defined only` |
| `FeatureViewSectionPackage.featureSection_observes` | `theorem` | `FeatureViewSectionPackage` から selected feature observation law を accessor theorem として取り出す。 | `proved` |
| `featureObservationCoverage_of_featureViewSound` | `theorem` | `FeatureViewSound` から feature-owned representative による selected coverage を得る。 | `proved` |
| `featureViewSectionPackage_of_featureViewSound` | `def` | sound な declared `featureEmbedding` を `FeatureViewSectionPackage` として束ねる。 | `defined only` |
| `ObservationalCoreRetraction` | `def` | `r ∘ i ≈ id` を、embedded core に対する selected core observation の一致として表す retraction law。 | `defined only` |
| `SplitExtensionLiftingData` | `structure` | `FeatureExtension`、feature observation、core observation、feature section、core retraction、section / retraction law、interface factorization、required invariant preservation を束ねる selected split-extension lifting schema。 | `defined only` |
| `SplitExtensionLiftingData.featureSection_observes` | `theorem` | feature section law を accessor theorem として取り出す。 | `proved` |
| `SplitExtensionLiftingData.coreRetraction_observes_coreEmbedding` | `theorem` | embedded core 上の observational core retraction law を accessor theorem として取り出す。 | `proved` |
| `SplitExtensionLiftingData.featureViewSectionPackage` | `def` | lifting data の feature-section 部分を公開 `FeatureViewSectionPackage` として取り出す。 | `defined only` |
| `SplitExtensionLiftingData.featureViewSectionPackage_observes` | `theorem` | lifting data 由来の公開 section package が selected feature observation law を満たすことを示す。 | `proved` |
| `SelectedFeatureStep` | `structure` | selected feature state 間の feature step。 | `defined only` |
| `LiftedExtensionStep` | `structure` | extended architecture 内の lifted endpoint pair。 | `defined only` |
| `LawfulFeatureStep` | `def` | selected feature invariant を feature step が保存すること。 | `defined only` |
| `CanonicalLiftedFeatureStep` | `def` | feature section によって feature step の endpoint を extended endpoint へ持ち上げる canonical lift。 | `defined only` |
| `LiftsFeatureStep` | `def` | lifted step が section-induced endpoints を持ち、extended static edge として存在すること。 | `defined only` |
| `PreservesCoreInvariants` | `def` | core retraction 後の selected core invariant を lifted step が保存すること。 | `defined only` |
| `CompatibleWithInterface` | `structure` | selected step ごとの extended edge、interface factorization、coverage、core invariant preservation を束ねる compatibility package。 | `defined only` |
| `SplitExtensionLifting` | `theorem` | selected split-extension lifting data、lawful feature step、interface compatibility から、lifting と core invariant preservation を満たす extended step の存在を得る。 | `proved` |

Non-conclusions: `SplitExtensionLifting` は strict equality の section/retraction、全 component の一意分解、
runtime flatness、semantic flatness、または all feature steps の自動 lifting を主張しない。

## Architecture Operation

File: `Formal/Arch/Operation.lean`

Issues [#322](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/322)
and [#327](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/327)
audit this schema as the entry point for generated operation proof obligations.
The useful accessors are the generated-obligation kind theorem, the combined
precondition predicate, and the one-way witness mapping theorem; this package
does not by itself assert any unconditional operation law or global flatness
preservation.
Issue [#359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/359)
records where each Chapter 3 operation lives after the public tag / proof
obligation schema: [Architecture Calculus catalog placement](design/architecture_calculus_catalog_placement.md).
Only `compose`, `replace`, `protect`, and `reverse` currently have concrete
finite graph kernels. `refine`, `abstract`, `split`, `merge`, `isolate`,
`migrate`, `contract`, and `synthesize` are routed to contract / observation,
runtime / semantic, repair, or synthesis theorem packages instead of a uniform
graph transform.

この節の status 分類は次の通りである。

| API 群 | 読み方 | ここで `proved` と読める範囲 | 読まない範囲 |
| --- | --- | --- | --- |
| operation / role tag | schema / carrier | tag constructor と label が theorem package から参照できる。 | tag だけから preservation、improvement、localization、operation law は出ない。 |
| `OperationProofObligation` constructor | schema / carrier | operation ごとの obligation package を explicit precondition と non-conclusion つきで構成できる。 | constructor が存在するだけでは obligation discharge ではない。 |
| `ArchitectureOperation.*` theorem | accessor theorem / witness bridge | generated-obligation kind の一致と、post-to-pre witness mapping の片方向 soundness。 | global flatness preservation、semantic completeness、逆向き witness completeness。 |
| `OperationRoleSchema.*` theorem | accessor theorem / bounded discharge wrapper / role bridge | role package kind の一致、明示的に与えた bounded conclusion からの discharge、preserve / non-preserve role を selected invariant / witness / relation / assumption 境界として読む bridge。 | role tag だけから preservation、reflection、improvement、localization、translation、transfer、assumption discharge は推論しない。 |

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureOperationKind` | `inductive` | 第3章 catalog の `compose`, `refine`, `abstract`, `replace`, `split`, `merge`, `isolate`, `protect`, `migrate`, `reverse`, `contract`, `repair`, `synthesize` を表す operation family tag。 | `defined only` |
| `ArchitectureOperationKind.label` | `def` | theorem package や docs から参照するための operation tag label。 | `defined only` |
| `ArchitectureOperationRole` | `inductive` | 第3章の Preserve / Reflect / Improve / Localize / Translate / Transfer / Assume に対応する operation role tag。 | `defined only` |
| `ArchitectureOperationRole.label` | `def` | theorem package や docs から参照するための operation role label。 | `defined only` |
| `ProofObligation` | `structure` | formal universe、required laws、invariant family、witness universe、coverage / exactness、operation precondition、conclusion、non-conclusions を束ねる最小 schema。 | `defined only` |
| `ProofObligation.AssumptionsHold` | `def` | proof obligation の visible assumptions をまとめる。 | `defined only` |
| `ProofObligation.Discharged` | `def` | visible assumptions から conclusion が得られること。 | `defined only` |
| `ProofObligation.RecordsNonConclusions` | `def` | theorem package が明示的な non-conclusions を持つこと。 | `defined only` |
| `ProofObligation.discharged_of_conclusion` | `theorem` | conclusion が直接与えられれば obligation は discharge できる。 | `proved` |
| `OperationProofObligation` | `structure` | operation kind ごとに生成される proof obligation、precondition、non-conclusion を束ねる。 | `defined only` |
| `OperationProofObligation.compose` | `def` | `compose` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.refine` | `def` | `refine` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.abstract` | `def` | `abstract` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.replace` | `def` | `replace` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.split` | `def` | `split` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.merge` | `def` | `merge` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.isolate` | `def` | `isolate` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.protect` | `def` | `protect` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.migrate` | `def` | `migrate` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.reverse` | `def` | `reverse` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.contract` | `def` | `contract` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.repair` | `def` | `repair` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.synthesize` | `def` | `synthesize` operation 用 proof-obligation package constructor。 | `defined only` |
| `ArchitectureOperation` | `structure` | operation kind、source / target state、precondition、生成 proof obligation、operation tag 一致、前後 witness family、後段 witness から前段 witness への mapping と soundness field を束ねる。 | `defined only` |
| `ArchitectureOperation.GeneratedObligation` | `def` | operation に紐づく generated proof obligation を取り出す。 | `defined only` |
| `ArchitectureOperation.generatedObligation_kind` | `theorem` | operation と generated proof obligation の operation tag が一致することを取り出す。 | `proved` |
| `ArchitectureOperation.PreconditionsHold` | `def` | operation と generated obligation の visible precondition をまとめる。 | `defined only` |
| `ArchitectureOperation.witnessMapping_sound` | `theorem` | post-operation witness から pre-operation witness への片方向 mapping soundness を取り出す。 | `proved` |
| `ArchitectureOperation.exists_sourceWitness_of_targetWitness` | `theorem` | post-operation witness があれば、対応する pre-operation witness が存在する。 | `proved` |
| `OperationRoleSchema` | `structure` | selected `ArchitectureOperation` に role tag、selected invariant、role-specific assumptions、bounded conclusion、non-conclusion を付与する schema。 | `defined only` |
| `OperationRoleSchema.operationKind` | `def` | role package が参照する operation kind を取り出す。 | `defined only` |
| `OperationRoleSchema.HasRole` | `def` | role package が特定 role tag を持つことを predicate として表す。 | `defined only` |
| `OperationRoleSchema.AssumptionsHold` | `def` | operation precondition と role-specific assumptions をまとめる。 | `defined only` |
| `OperationRoleSchema.Discharged` | `def` | visible assumptions から bounded role conclusion が得られること。 | `defined only` |
| `OperationRoleSchema.RecordsNonConclusions` | `def` | role package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `OperationRoleSchema.preserve` | `def` | Preserve role package constructor。 | `defined only` |
| `OperationRoleSchema.reflect` | `def` | Reflect role package constructor。 | `defined only` |
| `OperationRoleSchema.improve` | `def` | Improve role package constructor。 | `defined only` |
| `OperationRoleSchema.localize` | `def` | Localize role package constructor。 | `defined only` |
| `OperationRoleSchema.translate` | `def` | Translate role package constructor。 | `defined only` |
| `OperationRoleSchema.transfer` | `def` | Transfer role package constructor。 | `defined only` |
| `OperationRoleSchema.assume` | `def` | Assume role package constructor。 | `defined only` |
| `OperationRoleSchema.discharged_of_conclusion` | `theorem` | bounded role conclusion が直接与えられれば role package は discharge できる。 | `proved` |
| `OperationRoleSchema.generatedObligation_kind` | `theorem` | role package が参照する operation と generated proof obligation の operation tag が一致する。 | `proved` |

## Concrete Graph Operation Kernel

File: `Formal/Arch/OperationKernel.lean`

Issue [#298](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/298)
の対象範囲は、finite `ArchGraph` 上で扱える concrete graph transformation kernel を
定義し、既存の `ArchitectureOperation` schema と接続することである。Issue
[#339](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/339)
では、同一 component 型上の edge union としての `compose` と、edge equivalence
precondition に相対化した bounded `replace` を追加した。Issue
[#412](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/412)
では、`reverse` graph 上の reachable cone を source graph の incoming reachability として読む
bounded diagnostic bridge を追加した。無条件の全 operation laws、
global flatness preservation、runtime / semantic preservation の完全性、
incident prediction、telemetry / extractor completeness は主張しない。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ConcreteGraphOperation` | `structure` | finite `ArchGraph` 上の concrete operation kernel。operation kind、source / target、precondition、non-conclusion を束ねる。 | `defined only` |
| `ConcreteGraphOperation.generatedProofObligation` | `def` | concrete operation から既存 `OperationProofObligation` schema へ接続する。 | `defined only` |
| `ConcreteGraphOperation.toArchitectureOperation` | `def` | concrete operation を既存 `ArchitectureOperation` schema へ埋め込む。 | `defined only` |
| `ConcreteGraphOperation.toArchitectureOperation_kind` | `theorem` | schema 埋め込みが operation tag を保存する。 | `proved` |
| `ConcreteGraphOperation.toArchitectureOperation_source` | `theorem` | schema 埋め込みが source graph を保存する。 | `proved` |
| `ConcreteGraphOperation.toArchitectureOperation_target` | `theorem` | schema 埋め込みが target graph を保存する。 | `proved` |
| `EdgeEquivalent` | `def` | 2つの architecture graph が同じ edge relation を持つこと。bounded replacement の明示 precondition として使う。 | `defined only` |
| `EdgeEquivalent.refl` | `theorem` | edge equivalence の反射性。 | `proved` |
| `EdgeEquivalent.symm` | `theorem` | edge equivalence の対称性。 | `proved` |
| `EdgeEquivalent.trans` | `theorem` | edge equivalence の推移性。 | `proved` |
| `ArchGraph.reverse` | `def` | dependency edge の向きを反転した graph を定義する。 | `defined only` |
| `ArchGraph.reverse_edge_iff` | `theorem` | reversed graph の edge は元 graph の逆向き edge と同値である。 | `proved` |
| `ArchGraph.reverse_reverse_edge_iff` | `theorem` | `reverse` を二回適用すると edge relation が元に戻る。 | `proved` |
| `ArchGraph.reachable_reverse_iff` | `theorem` | reversed graph の reachability が source graph の逆向き reachability と同値であること。 | `proved` |
| `ArchGraph.reverseReachableCone` | `def` | finite list 内で、selected component へ source graph 上で到達できる strict reverse-reachability cone。upstream impact / blast radius の graph-level bridge として使う。 | `defined only` |
| `ArchGraph.reverseReachableConeSize` | `def` | graph-level strict reverse-reachability cone のサイズ。 | `defined only` |
| `ArchGraph.mem_reverseReachableCone_iff` | `theorem` | reverse-reachability cone の membership が source graph の incoming reachability と一致すること。 | `proved` |
| `ArchGraph.compose` | `def` | 同一 component 型上の2つの graph を edge union で合成する。 | `defined only` |
| `ArchGraph.compose_edge_iff` | `theorem` | composed graph の edge はどちらかの入力 graph の edge と同値である。 | `proved` |
| `ArchGraph.left_edgeSubset_compose` | `theorem` | compose の左入力 graph は composed graph の edge subset である。 | `proved` |
| `ArchGraph.right_edgeSubset_compose` | `theorem` | compose の右入力 graph は composed graph の edge subset である。 | `proved` |
| `ArchGraph.compose_assoc_edgeEquivalent` | `theorem` | edge-union composition が edge equivalence まで結合的である。 | `proved` |
| `ArchGraph.replace` | `def` | graph-level replacement として置換先 graph を選ぶ。保存性は別 theorem に分離する。 | `defined only` |
| `ArchGraph.replace_edge_iff` | `theorem` | replacement graph の edge は置換先 graph の edge と同値である。 | `proved` |
| `ArchGraph.replace_preserves_edges_of_edgeEquivalent` | `theorem` | edge equivalence 前提の下で replacement が source edge relation を保存する。 | `proved` |
| `FiniteArchGraph.reverse` | `def` | finite component universe を保ったまま dependency edge を反転する。 | `defined only` |
| `FiniteArchGraph.reverse_edge_iff` | `theorem` | finite reversed graph の edge は元 graph の逆向き edge と同値である。 | `proved` |
| `FiniteArchGraph.reverse_reverse_edge_iff` | `theorem` | finite graph の `reverse` 二回適用が edge relation を復元する。 | `proved` |
| `FiniteArchGraph.reverse_reachableConeSizeAt_eq_reverseReachableConeSize_under_universe` | `theorem` | finite graph の reversed graph 上の executable bounded reachable-cone size が graph-level reverse cone size と一致すること。 | `proved` |
| `FiniteArchGraph.protect` | `def` | graph-level protect kernel を static graph の identity transform として定義する。 | `defined only` |
| `FiniteArchGraph.protect_edge_iff` | `theorem` | graph-level protect kernel が edge relation を保存する。 | `proved` |
| `FiniteArchGraph.compose` | `def` | source 側の finite measurement universe を保ったまま edge union graph を作る。 | `defined only` |
| `FiniteArchGraph.compose_edge_iff` | `theorem` | finite composed graph の edge はどちらかの入力 graph の edge と同値である。 | `proved` |
| `FiniteArchGraph.left_edgeSubset_compose` | `theorem` | compose の左入力 finite graph は composed graph の edge subset である。 | `proved` |
| `FiniteArchGraph.right_edgeSubset_compose` | `theorem` | compose の右入力 finite graph は composed graph の edge subset である。 | `proved` |
| `FiniteArchGraph.compose_assoc_edgeEquivalent` | `theorem` | finite edge-union composition が edge equivalence まで結合的である。 | `proved` |
| `FiniteArchGraph.replace` | `def` | finite graph replacement として置換先 finite graph を選ぶ。 | `defined only` |
| `FiniteArchGraph.replace_edge_iff` | `theorem` | finite replacement graph の edge は置換先 graph の edge と同値である。 | `proved` |
| `FiniteArchGraph.replace_preserves_edges_of_edgeEquivalent` | `theorem` | edge equivalence 前提の下で finite replacement が source edge relation を保存する。 | `proved` |
| `ConcreteGraphOperation.reverse` | `def` | finite graph の concrete `reverse` operation。 | `defined only` |
| `ConcreteGraphOperation.protect` | `def` | finite graph の concrete `protect` operation。 | `defined only` |
| `ConcreteGraphOperation.compose` | `def` | finite edge union を target にする concrete `compose` operation。 | `defined only` |
| `ConcreteGraphOperation.replace` | `def` | `EdgeEquivalent` を precondition に持つ concrete `replace` operation。 | `defined only` |
| `ConcreteGraphOperation.reverse_kind` | `theorem` | concrete reverse operation が `reverse` tag を持つ。 | `proved` |
| `ConcreteGraphOperation.protect_kind` | `theorem` | concrete protect operation が `protect` tag を持つ。 | `proved` |
| `ConcreteGraphOperation.compose_kind` | `theorem` | concrete compose operation が `compose` tag を持つ。 | `proved` |
| `ConcreteGraphOperation.replace_kind` | `theorem` | concrete replace operation が `replace` tag を持つ。 | `proved` |
| `ConcreteGraphOperation.reverse_schema_kind` | `theorem` | concrete reverse の schema 埋め込みが `reverse` tag を持つ。 | `proved` |
| `ConcreteGraphOperation.protect_schema_kind` | `theorem` | concrete protect の schema 埋め込みが `protect` tag を持つ。 | `proved` |
| `ConcreteGraphOperation.compose_schema_kind` | `theorem` | concrete compose の schema 埋め込みが `compose` tag を持つ。 | `proved` |
| `ConcreteGraphOperation.replace_schema_kind` | `theorem` | concrete replace の schema 埋め込みが `replace` tag を持つ。 | `proved` |

## Architecture Calculus Laws

File: `Formal/Arch/OperationLaws.lean`

Issue [#279](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/279)
の対象範囲は、Architecture Calculus law を無条件の algebraic law としてではなく、
bounded universe、compatibility、coverage、exactness、observation equivalence を明示する
theorem package として扱うことである。global associativity、全 operation の冪等性、
global flatness preservation は主張しない。
Issues [#322](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/322)
and [#327](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/327)
reuse this section as the bounded law audit surface for compose / replace /
protect / reverse / repair.
Issue [#360](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/360)
continues from the placement decision in
[Architecture Calculus catalog placement](design/architecture_calculus_catalog_placement.md)
by adding concrete graph / repair / synthesis entrypoints for selected bounded
law packages.
Issue [#381](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/381)
adds the declared-interface-mediated compose associativity package, with
compatibility, coverage, exactness, and observation equivalence kept explicit.
Issue [#378](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/378)
adds separate `refine` / `abstract` observation-equivalence packages so they do
not reuse the `replace` law wrapper.
Issue [#410](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/410)
adds a bounded `migrate` package for staged migration paths, compatibility
windows, and old/new observation equivalence.

この節の status 分類は次の通りである。

| API 群 | 読み方 | ここで `proved` と読める範囲 | 読まない範囲 |
| --- | --- | --- | --- |
| `ArchitectureCalculusLawKind`, `ArchitectureCalculusLaw` | schema / carrier | bounded law package が law kind、operation kind、explicit assumptions、conclusion、non-conclusions を名前づける。 | law tag は無条件の algebraic law ではない。 |
| generic constructor accessor | accessor theorem | constructor が意図した law kind / operation kind を保持する。 | それだけで concrete graph equality、observation preservation、flatness は証明しない。 |
| concrete finite graph entrypoint | schema bridge / substantive theorem | selected finite graph kernel が、明示前提の下で edge-union、edge-equivalence、protect-idempotence、reverse-involution の結論を discharge する。 | uniform operation law と global flatness preservation。 |
| observation / runtime / migration entrypoint | schema bridge / substantive theorem | selected projection、observation、runtime、compatibility window、migration assumptions から下表の bounded conclusion を得る。 | runtime telemetry completeness、semantic completeness、extractor completeness、empirical cost claim。 |
| repair / synthesis entrypoint | schema bridge / substantive theorem | selected obstruction universe、admissible rule、produced candidate、valid certificate 前提から bounded repair / synthesis conclusion を得る。 | solver completeness と all obstruction removal。 |

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureCalculusLawKind` | `inductive` | `identity`, `associativity`, `edgeUnion`, `refinementAbstraction`, `edgeEquivalence`, `externalContractPreservation`, `explicitContractSoundness`, `protectionIdempotence`, `runtimeLocalization`, `migrationCompatibility`, `reverseInvolution`, `witnessMappingFunctoriality`, `synthesisSoundness`, `noSolutionSoundness` の bounded law tag。 | `defined only` |
| `ArchitectureCalculusLawKind.label` | `def` | documentation-facing な law tag label。 | `defined only` |
| `ArchitectureCalculusLaw` | `structure` | law kind、operation kind、bounded universe、compatibility / coverage / exactness / observation equivalence、結論、soundness、non-conclusions を束ねる schema。 | `defined only` |
| `ArchitectureCalculusLaw.AssumptionsHold` | `def` | bounded law package の visible assumptions をまとめる。 | `defined only` |
| `ArchitectureCalculusLaw.RecordsNonConclusions` | `def` | law package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `ArchitectureCalculusLaw.conclusion_of_assumptions` | `theorem` | bounded assumptions から law conclusion を得る。 | `proved` |
| `ArchitectureCalculusLaw.identityLaw` | `def` | selected operation kind に対する bounded identity law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.composeAssociativity` | `def` | `compose` operation 用 bounded associativity law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.composeEdgeUnion` | `def` | `compose` operation 用 bounded concrete edge-union law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.replaceRefinementAbstraction` | `def` | `replace` operation 用 bounded refinement / abstraction law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.refineObservationEquivalence` | `def` | `refine` operation 用 bounded observation-equivalence law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.abstractObservationEquivalence` | `def` | `abstract` operation 用 bounded observation-equivalence law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.replaceEdgeEquivalence` | `def` | `replace` operation 用 bounded concrete edge-equivalence law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.mergeExternalContractPreservation` | `def` | `merge` operation 用 bounded external-contract preservation law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.contractExplicitizationSoundness` | `def` | `contract` operation 用 bounded explicitization-soundness law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.protectIdempotence` | `def` | `protect` operation 用 bounded idempotence law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.runtimeLocalization` | `def` | `isolate` / policy-aware `protect` など、selected runtime region に相対化した bounded runtime-localization law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.migrationCompatibility` | `def` | `migrate` operation 用 bounded migration compatibility law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.reverseInvolution` | `def` | selected operation kind に対する bounded reverse-involution law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.repairMonotonicity` | `def` | `repair` operation 用 bounded witness-mapping / monotonicity law package constructor。 | `defined only` |
| `ArchitectureCalculusLaw.identityLaw_kind` | `theorem` | identity law constructor が identity tag を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.composeAssociativity_operationKind` | `theorem` | compose associativity constructor が `compose` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.composeEdgeUnion_operationKind` | `theorem` | compose edge-union constructor が `compose` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.replaceRefinementAbstraction_operationKind` | `theorem` | replace refinement / abstraction constructor が `replace` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.refineObservationEquivalence_operationKind` | `theorem` | refine observation-equivalence constructor が `refine` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.abstractObservationEquivalence_operationKind` | `theorem` | abstract observation-equivalence constructor が `abstract` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.replaceEdgeEquivalence_operationKind` | `theorem` | replace edge-equivalence constructor が `replace` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.mergeExternalContractPreservation_operationKind` | `theorem` | merge external-contract preservation constructor が `merge` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.contractExplicitizationSoundness_operationKind` | `theorem` | contract explicitization-soundness constructor が `contract` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.protectIdempotence_operationKind` | `theorem` | protect idempotence constructor が `protect` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.runtimeLocalization_operationKind` | `theorem` | runtime-localization constructor が指定された operation kind を保持すること。 | `proved` |
| `ArchitectureCalculusLaw.migrationCompatibility_operationKind` | `theorem` | migration-compatibility constructor が `migrate` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.reverseInvolution_kind` | `theorem` | reverse-involution constructor が reverse-involution tag を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.repairMonotonicity_operationKind` | `theorem` | repair monotonicity constructor が `repair` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.finiteComposeEdgeUnionLaw` | `def` | finite `compose` graph kernel の edge-union theorem を bounded law package として包む entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.finiteComposeEdgeUnionLaw_operationKind` | `theorem` | finite compose edge-union law package が `compose` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.finiteComposeEdgeUnionLaw_conclusion` | `theorem` | bounded assumptions から finite compose の edge-union theorem を得る。 | `proved` |
| `ArchitectureCalculusLaw.InterfaceMediatedComposeCompatibility` | `structure` | interface-mediated finite composition の selected compatibility 前提として、入力 graph の projection soundness と interface graph の declared boundary closure を束ねる。 | `defined only` |
| `ArchitectureCalculusLaw.InterfaceMediatedComposeCoverage` | `def` | projection がすべての component を declared interface boundary に露出する coverage 前提。 | `defined only` |
| `ArchitectureCalculusLaw.InterfaceMediatedComposeExact` | `structure` | 左結合 / 右結合の finite composition が選択 interface graph に exact projection される前提。 | `defined only` |
| `ArchitectureCalculusLaw.InterfaceMediatedComposeObserved` | `def` | 左結合 / 右結合の finite composition が選択 observation で外部同値である前提。 | `defined only` |
| `ArchitectureCalculusLaw.interfaceMediatedComposeAssociativityLaw` | `def` | declared interface、coverage、exactness、observation equivalence に相対化した bounded `compose` associativity law package。 | `defined only` |
| `ArchitectureCalculusLaw.interfaceMediatedComposeAssociativityLaw_operationKind` | `theorem` | interface-mediated compose associativity package が `compose` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.interfaceMediatedComposeAssociativityLaw_conclusion` | `theorem` | bounded assumptions から finite compose の edge associativity と選択 observation equivalence を得る。 | `proved` |
| `ArchitectureCalculusLaw.finiteReplaceEdgeEquivalenceLaw` | `def` | `EdgeEquivalent` precondition に相対化した finite `replace` edge preservation を bounded law package として包む entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.finiteReplaceEdgeEquivalenceLaw_operationKind` | `theorem` | finite replace edge-equivalence law package が `replace` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.finiteReplaceEdgeEquivalenceLaw_conclusion` | `theorem` | bounded assumptions から edge-equivalent finite replacement の source-edge preservation を得る。 | `proved` |
| `ArchitectureCalculusLaw.localReplacementPreservationLaw` | `def` | `LocalReplacementContract` を bounded `replace` law package として包み、projection soundness と observation preservation を結論する entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.localReplacementPreservationLaw_operationKind` | `theorem` | local replacement preservation law package が `replace` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.localReplacementPreservationLaw_conclusion` | `theorem` | bounded assumptions から projection soundness と `LSPCompatible` を得る。 | `proved` |
| `ArchitectureCalculusLaw.localReplacementViolationZeroLaw` | `def` | `LocalReplacementContract` を bounded `replace` law package として包み、finite measurement universe 上の projection / LSP violation count が 0 になることを結論する entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.localReplacementViolationZeroLaw_operationKind` | `theorem` | local replacement zero-violation law package が `replace` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.localReplacementViolationZeroLaw_conclusion` | `theorem` | bounded assumptions から projection soundness violation count と LSP violation count が 0 であることを得る。 | `proved` |
| `ArchitectureCalculusLaw.RefinementProjectionContract` | `def` | refinement 側の selected projection contract として `DIPCompatible` を置く。projection completeness は含めない。 | `defined only` |
| `ArchitectureCalculusLaw.RefinementObservationContract` | `def` | refinement 側の selected observation contract として `ObservationFactorsThrough` を置く。 | `defined only` |
| `ArchitectureCalculusLaw.AbstractionProjectionContract` | `def` | abstraction 側の selected projection contract として `StrongDIPCompatible` を置く。 | `defined only` |
| `ArchitectureCalculusLaw.AbstractionObservationContract` | `def` | abstraction 側の selected observation contract として `ObservationFactorsThrough` を置く。 | `defined only` |
| `ArchitectureCalculusLaw.RefinementAbstractionObserved` | `def` | `abstract` 後の architecture が元 architecture と selected external observation で同値であること。 | `defined only` |
| `ArchitectureCalculusLaw.projectionSound_of_refinementProjectionContract` | `theorem` | refinement projection contract から projection soundness を得る。 | `proved` |
| `ArchitectureCalculusLaw.lspCompatible_of_refinementObservationContract` | `theorem` | refinement observation contract から `LSPCompatible` を得る。 | `proved` |
| `ArchitectureCalculusLaw.projectionExact_of_abstractionProjectionContract` | `theorem` | abstraction projection contract から `ProjectionExact` を得る。 | `proved` |
| `ArchitectureCalculusLaw.lspCompatible_of_abstractionObservationContract` | `theorem` | abstraction observation contract から `LSPCompatible` を得る。 | `proved` |
| `ArchitectureCalculusLaw.refinementObservationEquivalenceLaw` | `def` | `refine` を projection soundness と selected observation preservation に接続する bounded entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.refinementObservationEquivalenceLaw_operationKind` | `theorem` | refinement observation-equivalence package が `refine` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.refinementObservationEquivalenceLaw_conclusion` | `theorem` | bounded assumptions から projection soundness と `LSPCompatible` を得る。 | `proved` |
| `ArchitectureCalculusLaw.abstractionObservationEquivalenceLaw` | `def` | `abstract` を exact projection、selected observation preservation、external observation equivalence に接続する bounded entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.abstractionObservationEquivalenceLaw_operationKind` | `theorem` | abstraction observation-equivalence package が `abstract` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.abstractionObservationEquivalenceLaw_conclusion` | `theorem` | bounded assumptions から exact projection、`LSPCompatible`、external observation equivalence を得る。 | `proved` |
| `ArchitectureCalculusLaw.MergedBoundaryContract` | `def` | merged boundary の selected external contract として `StrongDIPCompatible` と `ObservationFactorsThrough` を束ねる。 | `defined only` |
| `ArchitectureCalculusLaw.projectionExact_of_mergedBoundaryContract` | `theorem` | merged-boundary contract から exact projection を得る。 | `proved` |
| `ArchitectureCalculusLaw.representativeStable_of_mergedBoundaryContract` | `theorem` | merged-boundary contract から representative stability を得る。 | `proved` |
| `ArchitectureCalculusLaw.observationFactorsThrough_of_mergedBoundaryContract` | `theorem` | merged-boundary contract から observation factorization を得る。 | `proved` |
| `ArchitectureCalculusLaw.lspCompatible_of_mergedBoundaryContract` | `theorem` | merged-boundary contract から selected external observation preservation を得る。 | `proved` |
| `ArchitectureCalculusLaw.ExplicitContractSound` | `def` | concrete implicit expectation が interface-level explicit contract の pullback と一致することを表す soundness predicate。 | `defined only` |
| `ArchitectureCalculusLaw.observationFactorsThrough_of_explicitContractSound` | `theorem` | explicit contract soundness から observation factorization を得る。 | `proved` |
| `ArchitectureCalculusLaw.lspCompatible_of_explicitContractSound` | `theorem` | explicit contract soundness から selected observation preservation を得る。 | `proved` |
| `ArchitectureCalculusLaw.mergeExternalContractPreservationLaw` | `def` | `merge` を exact projection、representative stability、selected external observation preservation に接続する bounded entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.mergeExternalContractPreservationLaw_operationKind` | `theorem` | merge external-contract package が `merge` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.mergeExternalContractPreservationLaw_conclusion` | `theorem` | bounded assumptions から exact projection、representative stability、`LSPCompatible` を得る。 | `proved` |
| `ArchitectureCalculusLaw.contractExplicitizationLaw` | `def` | `contract` を exact projection、representative stability、observation factorization、selected observation preservation に接続する bounded entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.contractExplicitizationLaw_operationKind` | `theorem` | contract explicitization package が `contract` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.contractExplicitizationLaw_conclusion` | `theorem` | bounded assumptions から exact projection、representative stability、observation factorization、`LSPCompatible` を得る。 | `proved` |
| `ArchitectureCalculusLaw.RuntimePathLocalizedWithin` | `def` | selected component universe と selected region に相対化して、runtime path endpoint が region 内に局所化されること。telemetry completeness は含めない。 | `defined only` |
| `ArchitectureCalculusLaw.RuntimeProtectionContract` | `def` | runtime path localization と `RuntimeInteractionProtected` を束ねる policy-aware runtime protection contract。 | `defined only` |
| `ArchitectureCalculusLaw.runtimePathLocalized_of_runtimeProtectionContract` | `theorem` | runtime protection contract から selected path localization を取り出す。 | `proved` |
| `ArchitectureCalculusLaw.runtimeInteractionProtected_of_runtimeProtectionContract` | `theorem` | runtime protection contract から `RuntimeInteractionProtected` を取り出す。 | `proved` |
| `ArchitectureCalculusLaw.runtimeFlatWithin_of_runtimeProtectionContract` | `theorem` | runtime coverage 前提の下で policy-aware runtime protection から `RuntimeFlatWithin` を得る。 | `proved` |
| `ArchitectureCalculusLaw.isolateRuntimeLocalizationLaw` | `def` | `isolate` を selected runtime path localization と bounded runtime flatness に接続する bounded entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.isolateRuntimeLocalizationLaw_operationKind` | `theorem` | isolate runtime-localization package が `isolate` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.isolateRuntimeLocalizationLaw_conclusion` | `theorem` | bounded assumptions から selected path localization と `RuntimeFlatWithin` を得る。 | `proved` |
| `ArchitectureCalculusLaw.protectRuntimeProtectionLaw` | `def` | policy-aware `protect` を selected path localization、`RuntimeInteractionProtected`、bounded runtime flatness に接続する bounded entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.protectRuntimeProtectionLaw_operationKind` | `theorem` | protect runtime-protection package が `protect` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.protectRuntimeProtectionLaw_conclusion` | `theorem` | bounded assumptions から selected path localization、runtime interaction protection、`RuntimeFlatWithin` を得る。 | `proved` |
| `ArchitectureCalculusLaw.StagedMigrationPath` | `def` | selected evolution plan の全 step が migration tag を持ち、各 step の local lawfulness field を満たす staged migration premise。 | `defined only` |
| `ArchitectureCalculusLaw.MigrationCompatibilityWindow` | `def` | selected compatibility predicate が migration plan の endpoints と各 primitive step boundary で成り立つこと。telemetry / semantic / extractor completeness は含めない。 | `defined only` |
| `ArchitectureCalculusLaw.MigrationObserved` | `def` | old architecture と new architecture が selected observation で同値であること。 | `defined only` |
| `ArchitectureCalculusLaw.MigrationNonConclusions` | `def` | bounded migration package が runtime telemetry completeness、semantic completeness、global flatness preservation を主張しないことを記録する marker。 | `defined only` |
| `ArchitectureCalculusLaw.migrationSequence_of_stagedMigrationPath` | `theorem` | staged migration premise から `MigrationSequence` を取り出す。 | `proved` |
| `ArchitectureCalculusLaw.everyStepLawful_of_stagedMigrationPath` | `theorem` | staged migration premise から `EveryStepLawful` を取り出す。 | `proved` |
| `ArchitectureCalculusLaw.migrateObservationEquivalenceLaw` | `def` | staged migration path、compatibility window、old / new observation equivalence を explicit assumptions として束ねる bounded `migrate` entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.migrateObservationEquivalenceLaw_operationKind` | `theorem` | migration observation-equivalence package が `migrate` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.migrateObservationEquivalenceLaw_conclusion` | `theorem` | bounded assumptions から staged migration path、compatibility window、selected old/new observation equivalence を得る。 | `proved` |
| `ArchitectureCalculusLaw.migrateObservationEquivalenceLaw_recordsNonConclusions` | `theorem` | bounded migration package が migration non-conclusions を記録していること。 | `proved` |
| `ArchitectureCalculusLaw.finiteProtectIdempotenceLaw` | `def` | graph-level identity としての finite `protect` を bounded idempotence law package として包む entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.finiteProtectIdempotenceLaw_operationKind` | `theorem` | finite protect idempotence law package が `protect` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.finiteProtectIdempotenceLaw_conclusion` | `theorem` | bounded assumptions から finite protect idempotence を得る。 | `proved` |
| `ArchitectureCalculusLaw.finiteReverseInvolutionLaw` | `def` | finite `reverse` double-application theorem を bounded reverse-involution law package として包む entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.finiteReverseInvolutionLaw_operationKind` | `theorem` | finite reverse involution law package が `reverse` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.finiteReverseInvolutionLaw_conclusion` | `theorem` | bounded assumptions から finite double-reverse edge restoration を得る。 | `proved` |
| `ArchitectureCalculusLaw.repairStepDecreasesLaw` | `def` | selected obstruction universe、selected witness、admissible rule、repair step に相対化した repair monotonicity を bounded law package として包む entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.repairStepDecreasesLaw_operationKind` | `theorem` | repair monotonicity law package が `repair` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.repairStepDecreasesLaw_conclusion` | `theorem` | bounded assumptions から selected obstruction measure decrease を得る。 | `proved` |
| `ArchitectureCalculusLaw.synthesisCandidateSoundnessLaw` | `def` | produced candidate の `SynthesisSoundnessPackage` を bounded `synthesize` law package として包む entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.synthesisCandidateSoundnessLaw_operationKind` | `theorem` | synthesis candidate soundness law package が `synthesize` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.synthesisCandidateSoundnessLaw_conclusion` | `theorem` | bounded assumptions から produced candidate が required constraints を満たすことを得る。 | `proved` |
| `ArchitectureCalculusLaw.noSolutionCertificateSoundnessLaw` | `def` | valid no-solution certificate の soundness を bounded `synthesize` law package として包む entrypoint。 | `defined only` |
| `ArchitectureCalculusLaw.noSolutionCertificateSoundnessLaw_operationKind` | `theorem` | no-solution certificate soundness law package が `synthesize` operation kind を持つこと。 | `proved` |
| `ArchitectureCalculusLaw.noSolutionCertificateSoundnessLaw_conclusion` | `theorem` | valid certificate と bounded assumptions から satisfying architecture の非存在を得る。 | `proved` |

Non-conclusions: concrete entrypoint は selected finite graph kernel、selected obstruction universe、または explicit synthesis package に相対化された theorem を包むだけであり、無条件の associativity、全 operation の冪等性、global flatness preservation、solver completeness、all obstruction removal は主張しない。

## Operation / Invariant Galois

Files: `Formal/Arch/OperationInvariant.lean`, `Formal/Arch/LocalContractDesignPattern.lean`, `Formal/Arch/SRPDesignPattern.lean`, `Formal/Arch/ISPDesignPattern.lean`, `Formal/Arch/StructuralDesignPattern.lean`, `Formal/Arch/RuntimeProtectionDesignPattern.lean`, `Formal/Arch/StateTransitionDesignPattern.lean`, `Formal/Arch/EventSourcingSagaDesignPattern.lean`, `Formal/Arch/ReplicatedLogDesignPattern.lean`

Issue [#276](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/276)
の対象範囲は、operation family と invariant family の保存関係から誘導される弱い
Galois 対応である。Issue [#383](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/383)
では、この対応から使う `Ops` / `Inv` の反単調性と closure operator API も
証明済み API として追加した。Issue [#384](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/384)
では、`OperationRoleSchema` の preserve role package を selected invariant に相対化して
`PreservesInvariant` / `Ops` へ接続する bridge を追加した。Issue
[#411](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/411)
では、非 preserve role package を explicit witness reflection、source-to-target
relation、または assumption boundary に相対化して読む bounded bridge を追加した。ここでは
`T ⊆ Ops(S) ↔ S ⊆ Inv(T)` と、それから誘導される selected preservation relation 上の閉包性のみを
証明し、束同型、完全分類、または選択 universe 外の保存性は主張しない。Issue
[#385](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/385)
では、局所契約層の代表例として `LocalReplacementContract` を
`DesignPattern` schema に接続した。ここでは projection soundness、LSP compatibility、
DIP compatibility を selected invariant family とし、`LocalReplacementContract`
から得られる既存 theorem により closure law を構成する。局所契約層から
`Decomposable` / `StrictLayered` を結論しないことは non-conclusion として記録する。
Issue [#417](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/417)
では、SRP を selected responsibility boundary と edge-local cohesion の bounded
package として `DesignPattern` schema に接続した。ここでは responsibility boundary
の totality、functional assignment、edge-local cohesion を invariant family とし、
自然言語としての SRP 全体、責務の意味的発見、組織 ownership 評価は
non-conclusion として記録する。
Issue [#414](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/414)
では、ISP を projection refinement / split の bounded package として
`DesignPattern` schema に接続した。ここでは target 側の projection soundness、
selected observation boundary factorization、そこから得る LSP compatibility を
invariant family として扱い、自然言語としての ISP 全体、API usability、interface
粒度最適性は non-conclusion として記録する。
Issue [#403](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/403)
では、大域構造層の代表例として Layered / Clean Architecture を
`DesignPattern` schema に接続した。ここでは edge-subset restriction を
operation family とし、`StrictLayered`、`Decomposable`、boundary policy soundness、
abstraction policy soundness を selected invariant family として扱う。層名 convention
の完全分類、runtime / semantic decomposability、global flatness preservation は
non-conclusion として記録する。
Issue [#404](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/404)
では、実行時依存層の代表例として `protect` / `isolate` の bounded runtime
protection package を `DesignPattern` schema に接続した。ここでは selected path
localization、`RuntimeInteractionProtected`、bounded `RuntimeFlatWithin` を
selected invariant family とし、`isolateRuntimeLocalizationLaw` /
`protectRuntimeProtectionLaw` の bounded assumptions から closure law を構成する。
incident reduction、障害修正コスト低下、runtime telemetry completeness、
policy-aware coverage completeness は non-conclusion として記録する。
Issue [#418](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/418)
では、状態遷移代数層の入口として `StateTransitionCarrier` と
`stateTransitionDesignPattern` を追加した。ここでは replay / roundtrip /
compensation の selected finite law cases を invariant family として扱う。
CRUD の一般 theorem 化、extractor completeness、実コード event log completeness、
運用コスト改善は non-conclusion として記録する。
Issue [#416](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/416)
では、Event Sourcing と Saga を状態遷移代数層の固有 `DesignPattern` package として
追加した。Event Sourcing は event sequence monoid、selected replay law、selected
projection law に相対化し、Saga は compensation を一般逆射ではなく selected weak
recovery law として扱う。
Issue [#415](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/415)
では、Replicated Log を分散収束層の bounded `DesignPattern` package として追加した。
ここでは failure model、quorum、ordering、convergence predicate、selected entries に
相対化した conditional convergence のみを扱い、無条件の可用性、分断耐性、収束性、
特定実装 protocol correctness、実コード log completeness は non-conclusion として
記録する。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `PreservesInvariant` | `def` | operation の source で invariant が成り立つなら target でも成り立つ、という保存関係。 | `defined only` |
| `Ops` | `def` | invariant family `S` のすべてを保存する operation family。 | `defined only` |
| `Inv` | `def` | operation family `T` のすべてによって保存される invariant family。 | `defined only` |
| `PredicateSubset` | `def` | predicate family 間の包含関係。 | `defined only` |
| `ClosedInvariantSet` | `def` | `S = Inv(Ops(S))` としての保存閉包。 | `defined only` |
| `ClosedOperationSet` | `def` | `T = Ops(Inv(T))` としての保存閉包。 | `defined only` |
| `operationInvariant_galois` | `theorem` | 保存関係から `T ⊆ Ops(S) ↔ S ⊆ Inv(T)` を得る弱い Galois 対応。 | `proved` |
| `Ops_antitone` | `theorem` | selected invariant family の包含を反転して `Ops` の包含を得る。 | `proved` |
| `Inv_antitone` | `theorem` | selected operation family の包含を反転して `Inv` の包含を得る。 | `proved` |
| `inv_ops_extensive` | `theorem` | `S ⊆ Inv(Ops(S))` として invariant closure の extensive law を得る。 | `proved` |
| `ops_inv_extensive` | `theorem` | `T ⊆ Ops(Inv(T))` として operation closure の extensive law を得る。 | `proved` |
| `inv_ops_monotone` | `theorem` | invariant closure `Inv ∘ Ops` が monotone であることを得る。 | `proved` |
| `ops_inv_monotone` | `theorem` | operation closure `Ops ∘ Inv` が monotone であることを得る。 | `proved` |
| `inv_ops_idempotent` | `theorem` | invariant closure `Inv ∘ Ops` が predicate extensionality 上 idempotent であることを得る。 | `proved` |
| `ops_inv_idempotent` | `theorem` | operation closure `Ops ∘ Inv` が predicate extensionality 上 idempotent であることを得る。 | `proved` |
| `OperationRoleSchema.operationInvariantSource` | `def` | role package を operation/invariant Galois 側の operation として読むため、underlying `ArchitectureOperation.source` を source map として取り出す。 | `defined only` |
| `OperationRoleSchema.operationInvariantTarget` | `def` | role package を operation/invariant Galois 側の operation として読むため、underlying `ArchitectureOperation.target` を target map として取り出す。 | `defined only` |
| `OperationRoleSchema.stateInvariantHolds` | `def` | bridge で使う invariant を、同じ state universe 上の predicate として評価する。 | `defined only` |
| `OperationRoleSchema.operationInvariantSource_eq` | `theorem` | Galois bridge の source map が underlying `ArchitectureOperation.source` と一致することを示す。 | `proved` |
| `OperationRoleSchema.operationInvariantTarget_eq` | `theorem` | Galois bridge の target map が underlying `ArchitectureOperation.target` と一致することを示す。 | `proved` |
| `OperationRoleSchema.RoleConclusionIsSelectedPreservation` | `def` | preserve role の bounded conclusion が selected invariant の source-to-target preservation である、という明示的な bridge 前提。 | `defined only` |
| `OperationRoleSchema.preservesInvariant_of_discharged_preserve` | `theorem` | preserve role package が discharge 済みで、bounded conclusion が selected preservation なら `PreservesInvariant` を得る。 | `proved` |
| `OperationRoleSchema.ops_mem_selectedInvariant_of_discharged_preserve` | `theorem` | discharge 済み preserve role package を、その selected invariant singleton family に対する `Ops` member として読む。 | `proved` |
| `OperationRoleSchema.RoleConclusionIsSelectedReflection` | `def` | reflect role の bounded conclusion が post-operation witness から pre-operation witness の存在を返す witness reflection である、という明示的な bridge 前提。 | `defined only` |
| `OperationRoleSchema.sourceWitness_exists_of_discharged_reflect` | `theorem` | reflect role package が discharge 済みで、bounded conclusion が selected witness reflection なら target witness から source witness の存在を得る。 | `proved` |
| `OperationRoleSchema.RoleConclusionIsSelectedImprovement` | `def` | improve role の bounded conclusion が selected source-to-target relation である、という明示的な bridge 前提。 | `defined only` |
| `OperationRoleSchema.selectedImprovement_of_discharged_improve` | `theorem` | improve role package が discharge 済みで、bounded conclusion が selected relation ならその relation を得る。 | `proved` |
| `OperationRoleSchema.RoleConclusionIsSelectedLocalization` | `def` | localize role の bounded conclusion が selected source-to-target localization relation である、という明示的な bridge 前提。 | `defined only` |
| `OperationRoleSchema.selectedLocalization_of_discharged_localize` | `theorem` | localize role package が discharge 済みで、bounded conclusion が selected localization relation ならその relation を得る。 | `proved` |
| `OperationRoleSchema.RoleConclusionIsSelectedTranslation` | `def` | translate role の bounded conclusion が selected source-to-target translation relation である、という明示的な bridge 前提。 | `defined only` |
| `OperationRoleSchema.selectedTranslation_of_discharged_translate` | `theorem` | translate role package が discharge 済みで、bounded conclusion が selected translation relation ならその relation を得る。 | `proved` |
| `OperationRoleSchema.RoleConclusionIsSelectedTransfer` | `def` | transfer role の bounded conclusion が selected source-to-target transfer relation である、という明示的な bridge 前提。 | `defined only` |
| `OperationRoleSchema.selectedTransfer_of_discharged_transfer` | `theorem` | transfer role package が discharge 済みで、bounded conclusion が selected transfer relation ならその relation を得る。 | `proved` |
| `OperationRoleSchema.RoleConclusionIsSelectedAssumption` | `def` | assume role の bounded conclusion が selected explicit assumption boundary である、という明示的な bridge 前提。 | `defined only` |
| `OperationRoleSchema.selectedAssumption_of_discharged_assume` | `theorem` | assume role package が discharge 済みで、bounded conclusion が selected assumption ならその assumption を得る。 | `proved` |
| `OperationRoleSchema.operationFamily_subset_ops_of_preserves_selected` | `theorem` | selected operation family の各 role package が selected invariant family を保存するなら、その operation family は `Ops(S)` に含まれる。 | `proved` |
| `DesignPattern` | `structure` | operation family、invariant family、両方向の closure law、non-conclusion clause を束ねる schema。 | `defined only` |
| `DesignPattern.operations_subset_ops` | `theorem` | design pattern から operation-to-invariant closure law を取り出す。 | `proved` |
| `DesignPattern.invariants_subset_inv` | `theorem` | design pattern から invariant-to-operation closure law を取り出す。 | `proved` |
| `DesignPattern.closure_law` | `theorem` | design pattern が保持する二つの closure law を pair として取り出す。 | `proved` |
| `DesignPattern.RecordsNonConclusions` | `def` | design pattern schema の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `DesignPattern.records_nonConclusions_iff` | `theorem` | recorded non-conclusion clause と schema field が一致すること。 | `proved` |
| `LocalContractState` | `structure` | concrete graph、interface projection、abstract graph、observation を同じ局所契約 state として束ねる。 | `defined only` |
| `LocalReplacementOperation` | `structure` | source / target state と target 側の `LocalReplacementContract` を持つ proof-carrying operation。 | `defined only` |
| `localReplacementOperationSource` | `def` | 局所置換 operation の source state を取り出す。 | `defined only` |
| `localReplacementOperationTarget` | `def` | 局所置換 operation の target state を取り出す。 | `defined only` |
| `LocalContractInvariant` | `inductive` | 局所契約層の selected invariant axis として projection soundness、LSP compatibility、DIP compatibility を列挙する。 | `defined only` |
| `localContractInvariantHolds` | `def` | `LocalContractInvariant` を `LocalContractState` 上の predicate として評価する。 | `defined only` |
| `localContractInvariantFamily` | `def` | 局所契約層で選択する invariant family。 | `defined only` |
| `localReplacementOperationFamily` | `def` | proof-carrying local replacement operation family。 | `defined only` |
| `localReplacementOperation_preserves_projectionSound` | `theorem` | `LocalReplacementContract` から target state の projection soundness を得る。 | `proved` |
| `localReplacementOperation_preserves_lspCompatible` | `theorem` | `LocalReplacementContract` から target state の `LSPCompatible` を得る。 | `proved` |
| `localReplacementOperation_preserves_dipCompatible` | `theorem` | `LocalReplacementContract` から target state の `DIPCompatible` を得る。 | `proved` |
| `localReplacementOperation_preserves_localContractInvariant` | `theorem` | proof-carrying local replacement operation が selected local contract invariants を保存する。 | `proved` |
| `localReplacementOperationFamily_subset_ops` | `theorem` | local replacement operation family が selected invariant family の `Ops` に含まれる。 | `proved` |
| `localContractInvariantFamily_subset_inv` | `theorem` | selected local contract invariants が local replacement operation family により保存される `Inv` に含まれる。 | `proved` |
| `LocalContractLayerNonConclusion` | `def` | local contract layer から無条件の `Decomposable` / `StrictLayered` theorem を結論しないことを記録する predicate。 | `defined only` |
| `localContractLayer_nonConclusion` | `theorem` | strong abstract-cycle counterexample により、local contract layer の global layering non-conclusion を証明する。 | `proved` |
| `localContractDesignPattern` | `def` | `LocalReplacementContract` を局所契約層の representative `DesignPattern` schema として束ねる。 | `defined only` |
| `localContractDesignPattern_closure_law` | `theorem` | 局所契約層 `DesignPattern` から operation-to-invariant / invariant-to-operation closure law を取り出す。 | `proved` |
| `localContractDesignPattern_records_nonConclusion` | `theorem` | 局所契約層 `DesignPattern` が global layering non-conclusion を記録する。 | `proved` |
| `ResponsibilityBoundary` | `structure` | SRP theorem package 用の selected responsibility boundary witness。 | `defined only` |
| `ResponsibilityBoundary.Total` | `def` | 各 component が少なくとも一つの selected responsibility を持つこと。 | `defined only` |
| `ResponsibilityBoundary.Functional` | `def` | 各 component が高々一つの selected responsibility を持つこと。 | `defined only` |
| `ResponsibilityBoundary.EdgeCohesive` | `def` | selected dependency edge が同じ responsibility boundary 内に留まる edge-local cohesion predicate。 | `defined only` |
| `ResponsibilityCohesionState` | `structure` | dependency graph と selected responsibility boundary を SRP state として束ねる。 | `defined only` |
| `ResponsibilityCohesionOperation` | `structure` | source / target state、target responsibility を source responsibility へ戻す collapse map、target 側の responsibility / cohesion witnesses を持つ proof-carrying operation。 | `defined only` |
| `responsibilityCohesionOperationSource` | `def` | SRP operation の source state を取り出す。 | `defined only` |
| `responsibilityCohesionOperationTarget` | `def` | SRP operation の target state を取り出す。 | `defined only` |
| `ResponsibilityCohesionInvariant` | `inductive` | SRP の selected invariant axis として boundary totality、functional assignment、local cohesion を列挙する。 | `defined only` |
| `responsibilityCohesionInvariantHolds` | `def` | `ResponsibilityCohesionInvariant` を responsibility-cohesion state 上の predicate として評価する。 | `defined only` |
| `responsibilityCohesionInvariantFamily` | `def` | SRP theorem package で選択する invariant family。 | `defined only` |
| `responsibilityCohesionOperationFamily` | `def` | proof-carrying responsibility refinement operation family。 | `defined only` |
| `responsibilityCohesionOperation_preserves_boundaryTotal` | `theorem` | proof-carrying SRP operation から target state の boundary totality を得る。 | `proved` |
| `responsibilityCohesionOperation_preserves_boundaryFunctional` | `theorem` | proof-carrying SRP operation から target state の functional assignment を得る。 | `proved` |
| `responsibilityCohesionOperation_preserves_localCohesion` | `theorem` | proof-carrying SRP operation から target state の selected edge-local cohesion を得る。 | `proved` |
| `responsibilityCohesionOperation_refinesBoundary` | `theorem` | target responsibility label が collapse map を通じて source responsibility boundary に読めることを取り出す。 | `proved` |
| `responsibilityCohesionOperation_preserves_invariant` | `theorem` | proof-carrying SRP operation が selected responsibility / local cohesion invariants を保存する。 | `proved` |
| `responsibilityCohesionOperationFamily_subset_ops` | `theorem` | SRP operation family が selected invariant family の `Ops` に含まれる。 | `proved` |
| `responsibilityCohesionInvariantFamily_subset_inv` | `theorem` | selected SRP invariants が SRP operation family により保存される `Inv` に含まれる。 | `proved` |
| `ResponsibilityCohesionNonConclusionClause` | `inductive` | SRP の non-conclusion clause として自然言語 SRP 全体、責務の意味的発見、組織 ownership 評価を列挙する。 | `defined only` |
| `ResponsibilityCohesionNonConclusion` | `def` | SRP の non-conclusion clause を記録する predicate。 | `defined only` |
| `responsibilityCohesion_nonConclusion` | `theorem` | SRP の non-conclusion clause が記録されることを示す。 | `proved` |
| `responsibilityCohesionDesignPattern` | `def` | SRP を selected responsibility boundary と edge-local cohesion に相対化した representative `DesignPattern` schema として束ねる。 | `defined only` |
| `responsibilityCohesionDesignPattern_closure_law` | `theorem` | SRP `DesignPattern` から operation-to-invariant / invariant-to-operation closure law を取り出す。 | `proved` |
| `responsibilityCohesionDesignPattern_records_nonConclusion` | `theorem` | SRP `DesignPattern` が自然言語 SRP 全体、責務の意味的発見、組織 ownership 評価を non-conclusion として記録する。 | `proved` |
| `InterfaceProjectionRefinementState` | `structure` | concrete graph、interface projection、abstract graph、selected observation を ISP 用の projection-refinement state として束ねる。 | `defined only` |
| `InterfaceProjectionRefinementOperation` | `structure` | source / target state、target projection を source projection へ戻す collapse map、target 側 projection soundness と observation factorization を持つ proof-carrying operation。 | `defined only` |
| `interfaceProjectionRefinementOperationSource` | `def` | ISP refinement operation の source state を取り出す。 | `defined only` |
| `interfaceProjectionRefinementOperationTarget` | `def` | ISP refinement operation の target state を取り出す。 | `defined only` |
| `InterfaceProjectionRefinementInvariant` | `inductive` | ISP の selected invariant axis として projection soundness、observation boundary factorization、LSP compatibility を列挙する。 | `defined only` |
| `interfaceProjectionRefinementInvariantHolds` | `def` | `InterfaceProjectionRefinementInvariant` を projection-refinement state 上の predicate として評価する。 | `defined only` |
| `interfaceProjectionRefinementOperation_preserves_projectionSound` | `theorem` | proof-carrying ISP operation から target state の projection soundness を得る。 | `proved` |
| `interfaceProjectionRefinementOperation_preserves_observationBoundaryFactors` | `theorem` | proof-carrying ISP operation から target state の observation factorization を得る。 | `proved` |
| `interfaceProjectionRefinementOperation_preserves_lspCompatible` | `theorem` | target observation factorization から target state の `LSPCompatible` を得る。 | `proved` |
| `interfaceProjectionRefinementOperation_refinesProjection` | `theorem` | target projection が collapse map を通じて source projection へ戻ることを取り出す。 | `proved` |
| `interfaceProjectionRefinementOperation_preserves_invariant` | `theorem` | proof-carrying ISP refinement operation が selected projection / observation invariants を保存する。 | `proved` |
| `interfaceProjectionRefinementOperationFamily_subset_ops` | `theorem` | ISP refinement operation family が selected invariant family の `Ops` に含まれる。 | `proved` |
| `interfaceProjectionRefinementInvariantFamily_subset_inv` | `theorem` | selected ISP invariants が ISP refinement operation family により保存される `Inv` に含まれる。 | `proved` |
| `InterfaceProjectionRefinementNonConclusionClause` | `inductive` | ISP の non-conclusion clause として自然言語 ISP 全体、API usability、interface 粒度最適性を列挙する。 | `defined only` |
| `InterfaceProjectionRefinementNonConclusion` | `def` | ISP の non-conclusion clause を記録する predicate。 | `defined only` |
| `interfaceProjectionRefinement_nonConclusion` | `theorem` | ISP の non-conclusion clause が記録されることを示す。 | `proved` |
| `interfaceProjectionRefinementDesignPattern` | `def` | ISP を projection refinement / split と selected observation boundary に相対化した representative `DesignPattern` schema として束ねる。 | `defined only` |
| `interfaceProjectionRefinementDesignPattern_closure_law` | `theorem` | ISP `DesignPattern` から operation-to-invariant / invariant-to-operation closure law を取り出す。 | `proved` |
| `interfaceProjectionRefinementDesignPattern_records_nonConclusion` | `theorem` | ISP `DesignPattern` が自然言語 ISP 全体、API usability、interface 粒度最適性を non-conclusion として記録する。 | `proved` |
| `StructuralLayerState` | `structure` | 大域構造層の state として dependency graph を束ねる。 | `defined only` |
| `StructuralRestrictionOperation` | `structure` | source / target state と `EdgeSubset target.G source.G` を持つ proof-carrying structural operation。 | `defined only` |
| `structuralRestrictionOperationSource` | `def` | structural restriction operation の source state を取り出す。 | `defined only` |
| `structuralRestrictionOperationTarget` | `def` | structural restriction operation の target state を取り出す。 | `defined only` |
| `StructuralLayerInvariant` | `inductive` | 大域構造層の selected invariant axis として strict layered、decomposable、boundary policy soundness、abstraction policy soundness を列挙する。 | `defined only` |
| `structuralLayerInvariantHolds` | `def` | `StructuralLayerInvariant` を fixed boundary / abstraction policy に相対化して `StructuralLayerState` 上の predicate として評価する。 | `defined only` |
| `structuralLayerInvariantFamily` | `def` | 大域構造層で選択する invariant family。 | `defined only` |
| `structuralRestrictionOperationFamily` | `def` | proof-carrying structural restriction operation family。 | `defined only` |
| `structuralRestrictionOperation_preserves_strictLayered` | `theorem` | edge-subset restriction が `StrictLayered` を保存する。 | `proved` |
| `structuralRestrictionOperation_preserves_decomposable` | `theorem` | edge-subset restriction が `Decomposable` を保存する。 | `proved` |
| `structuralRestrictionOperation_preserves_boundaryPolicySound` | `theorem` | edge-subset restriction が boundary policy soundness を保存する。 | `proved` |
| `structuralRestrictionOperation_preserves_abstractionPolicySound` | `theorem` | edge-subset restriction が abstraction policy soundness を保存する。 | `proved` |
| `structuralRestrictionOperation_preserves_structuralLayerInvariant` | `theorem` | proof-carrying structural restriction operation が selected global structural invariants を保存する。 | `proved` |
| `structuralRestrictionOperationFamily_subset_ops` | `theorem` | structural restriction operation family が selected invariant family の `Ops` に含まれる。 | `proved` |
| `structuralLayerInvariantFamily_subset_inv` | `theorem` | selected structural invariants が structural operation family により保存される `Inv` に含まれる。 | `proved` |
| `StructuralLayerNonConclusionClause` | `inductive` | 大域構造層の non-conclusion clause として layer convention classification、runtime / semantic decomposability、global flatness preservation を列挙する。 | `defined only` |
| `StructuralLayerNonConclusion` | `def` | 大域構造層の non-conclusion clause を記録する predicate。 | `defined only` |
| `structuralLayer_nonConclusion` | `theorem` | 大域構造層の non-conclusion clause が記録されることを示す。 | `proved` |
| `structuralLayerDesignPattern` | `def` | Layered / Clean Architecture を大域構造層の representative `DesignPattern` schema として束ねる。 | `defined only` |
| `structuralLayerDesignPattern_closure_law` | `theorem` | 大域構造層 `DesignPattern` から operation-to-invariant / invariant-to-operation closure law を取り出す。 | `proved` |
| `structuralLayerDesignPattern_records_nonConclusion` | `theorem` | 大域構造層 `DesignPattern` が structural non-conclusion clauses を記録する。 | `proved` |
| `RuntimeProtectionState` | `structure` | runtime flatness model、selected `ComponentUniverse`、selected region を実行時依存層 state として束ねる。 | `defined only` |
| `RuntimeProtectionOperation` | `inductive` | `isolateRuntimeLocalizationLaw` または `protectRuntimeProtectionLaw` の bounded assumptions を持つ proof-carrying runtime operation。 | `defined only` |
| `runtimeProtectionOperationSource` | `def` | runtime protection operation の source state を取り出す。 | `defined only` |
| `runtimeProtectionOperationTarget` | `def` | runtime protection operation の target state を取り出す。 | `defined only` |
| `RuntimeProtectionInvariant` | `inductive` | 実行時依存層の selected invariant axis として path localization、runtime interaction protection、bounded runtime flatness を列挙する。 | `defined only` |
| `runtimeProtectionInvariantHolds` | `def` | `RuntimeProtectionInvariant` を `RuntimeProtectionState` 上の predicate として評価する。 | `defined only` |
| `runtimeProtectionInvariantFamily` | `def` | 実行時依存層で選択する invariant family。 | `defined only` |
| `runtimeProtectionOperationFamily` | `def` | proof-carrying `isolate` / `protect` runtime operation family。 | `defined only` |
| `runtimeProtectionOperation_isolate_preserves_pathLocalized` | `theorem` | `isolateRuntimeLocalizationLaw` から target state の selected path localization を得る。 | `proved` |
| `runtimeProtectionOperation_isolate_preserves_interactionProtected` | `theorem` | `isolateRuntimeLocalizationLaw` の bounded assumptions から target state の `RuntimeInteractionProtected` を得る。 | `proved` |
| `runtimeProtectionOperation_isolate_preserves_runtimeFlat` | `theorem` | `isolateRuntimeLocalizationLaw` から target state の bounded `RuntimeFlatWithin` を得る。 | `proved` |
| `runtimeProtectionOperation_protect_preserves_pathLocalized` | `theorem` | `protectRuntimeProtectionLaw` から target state の selected path localization を得る。 | `proved` |
| `runtimeProtectionOperation_protect_preserves_interactionProtected` | `theorem` | `protectRuntimeProtectionLaw` から target state の `RuntimeInteractionProtected` を得る。 | `proved` |
| `runtimeProtectionOperation_protect_preserves_runtimeFlat` | `theorem` | `protectRuntimeProtectionLaw` から target state の bounded `RuntimeFlatWithin` を得る。 | `proved` |
| `runtimeProtectionOperation_preserves_runtimeProtectionInvariant` | `theorem` | proof-carrying runtime protection operation が selected runtime protection invariants を保存する。 | `proved` |
| `runtimeProtectionOperationFamily_subset_ops` | `theorem` | runtime protection operation family が selected invariant family の `Ops` に含まれる。 | `proved` |
| `runtimeProtectionInvariantFamily_subset_inv` | `theorem` | selected runtime protection invariants が runtime operation family により保存される `Inv` に含まれる。 | `proved` |
| `RuntimeProtectionNonConclusionClause` | `inductive` | 実行時依存層の non-conclusion clause として incident reduction、repair cost reduction、runtime telemetry completeness、policy-aware coverage completeness を列挙する。 | `defined only` |
| `RuntimeProtectionNonConclusion` | `def` | 実行時依存層の non-conclusion clause を記録する predicate。 | `defined only` |
| `runtimeProtection_nonConclusion` | `theorem` | 実行時依存層の non-conclusion clause が記録されることを示す。 | `proved` |
| `runtimeProtectionDesignPattern` | `def` | `protect` / `isolate` を実行時依存層の representative `DesignPattern` schema として束ねる。 | `defined only` |
| `runtimeProtectionDesignPattern_closure_law` | `theorem` | 実行時依存層 `DesignPattern` から operation-to-invariant / invariant-to-operation closure law を取り出す。 | `proved` |
| `runtimeProtectionDesignPattern_records_nonConclusion` | `theorem` | 実行時依存層 `DesignPattern` が runtime protection non-conclusion clauses を記録する。 | `proved` |
| `ReplicatedLogState` | `structure` | failure model、quorum、ordering、replica-local log presence、convergence predicate、selected entries を分散収束層 state として束ねる。 | `defined only` |
| `ReplicatedLogOperation` | `structure` | source / target state と target 側の aggregate `ReplicatedLogLawFamilyLawful` を持つ proof-carrying operation。 | `defined only` |
| `replicatedLogOperationSource` | `def` | replicated-log operation の source state を取り出す。 | `defined only` |
| `replicatedLogOperationTarget` | `def` | replicated-log operation の target state を取り出す。 | `defined only` |
| `ReplicatedLogInvariant` | `inductive` | quorum condition、ordering condition、conditional convergence、aggregate lawfulness を selected invariant axis として列挙する。 | `defined only` |
| `replicatedLogInvariantHolds` | `def` | `ReplicatedLogInvariant` を `ReplicatedLogState` 上の predicate として評価する。 | `defined only` |
| `replicatedLogInvariantFamily` | `def` | 分散収束層で選択する invariant family。 | `defined only` |
| `replicatedLogOperationFamily` | `def` | proof-carrying replicated-log operation family。 | `defined only` |
| `replicatedLogOperation_preserves_replicatedLogInvariant` | `theorem` | proof-carrying replicated-log operation が selected replicated-log invariants を保存する。 | `proved` |
| `replicatedLogOperationFamily_subset_ops` | `theorem` | replicated-log operation family が selected invariant family の `Ops` に含まれる。 | `proved` |
| `replicatedLogInvariantFamily_subset_inv` | `theorem` | selected replicated-log invariants が replicated-log operation family により保存される `Inv` に含まれる。 | `proved` |
| `ReplicatedLogNonConclusionClause` | `inductive` | Replicated Log の non-conclusion clause として無条件の可用性、分断耐性、収束性、protocol correctness completeness、concrete implementation correctness を列挙する。 | `defined only` |
| `ReplicatedLogNonConclusion` | `def` | Replicated Log の non-conclusion clause を記録する predicate。 | `defined only` |
| `replicatedLog_nonConclusion` | `theorem` | Replicated Log の non-conclusion clause が記録されることを示す。 | `proved` |
| `replicatedLogDesignPattern` | `def` | Replicated Log を分散収束層の representative `DesignPattern` schema として束ねる。 | `defined only` |
| `replicatedLogDesignPattern_closure_law` | `theorem` | 分散収束層 `DesignPattern` から operation-to-invariant / invariant-to-operation closure law を取り出す。 | `proved` |
| `replicatedLogDesignPattern_records_nonConclusion` | `theorem` | 分散収束層 `DesignPattern` が replicated-log non-conclusion clauses を記録する。 | `proved` |
| `StateTransitionCarrier` | `structure` | 状態、遷移、観測、replay / projection、compensation、`StateTransitionExpr` semantics を束ねる状態遷移代数層の最小 carrier。 | `defined only` |
| `StateTransitionPatternState` | `structure` | carrier と selected finite replay / roundtrip / compensation law cases を同じ state として束ねる。 | `defined only` |
| `StateTransitionOperation` | `structure` | source / target state と target 側の aggregate `StateTransitionLawFamilyLawful` を持つ proof-carrying operation。 | `defined only` |
| `stateTransitionOperationSource` | `def` | 状態遷移 operation の source state を取り出す。 | `defined only` |
| `stateTransitionOperationTarget` | `def` | 状態遷移 operation の target state を取り出す。 | `defined only` |
| `StateTransitionInvariant` | `inductive` | 状態遷移代数層の selected invariant axis として replay、roundtrip、compensation、aggregate lawfulness を列挙する。 | `defined only` |
| `stateTransitionInvariantHolds` | `def` | `StateTransitionInvariant` を `StateTransitionPatternState` 上の predicate として評価する。 | `defined only` |
| `stateTransitionInvariantFamily` | `def` | 状態遷移代数層で選択する invariant family。 | `defined only` |
| `stateTransitionOperationFamily` | `def` | proof-carrying state-transition operation family。 | `defined only` |
| `stateTransitionOperation_preserves_stateTransitionInvariant` | `theorem` | proof-carrying state-transition operation が selected state-transition invariants を保存する。 | `proved` |
| `stateTransitionOperationFamily_subset_ops` | `theorem` | state-transition operation family が selected invariant family の `Ops` に含まれる。 | `proved` |
| `stateTransitionInvariantFamily_subset_inv` | `theorem` | selected state-transition invariants が state-transition operation family により保存される `Inv` に含まれる。 | `proved` |
| `StateTransitionNonConclusionClause` | `inductive` | 状態遷移代数層の non-conclusion clause として extractor completeness、event log completeness、operational cost improvement、CRUD の一般 theorem 化を列挙する。 | `defined only` |
| `StateTransitionNonConclusion` | `def` | 状態遷移代数層の non-conclusion clause を記録する predicate。 | `defined only` |
| `stateTransition_nonConclusion` | `theorem` | 状態遷移代数層の non-conclusion clause が記録されることを示す。 | `proved` |
| `stateTransitionDesignPattern` | `def` | 状態遷移代数層を representative `DesignPattern` schema として束ねる。 | `defined only` |
| `stateTransitionDesignPattern_closure_law` | `theorem` | 状態遷移代数層 `DesignPattern` から operation-to-invariant / invariant-to-operation closure law を取り出す。 | `proved` |
| `stateTransitionDesignPattern_records_nonConclusion` | `theorem` | 状態遷移代数層 `DesignPattern` が state-transition non-conclusion clauses を記録する。 | `proved` |

Non-conclusions: この theorem package は operation / invariant の束同型、設計パターンの完全分類、
selected preservation relation の外側にある runtime / semantic / empirical 性質の保存、
局所契約層からの無条件の `Decomposable` / `StrictLayered`、自然言語としての SRP 全体、
責務の意味的発見、組織 ownership 評価、自然言語としての ISP 全体、interface 粒度最適性、
API usability、層名 convention の完全分類、
runtime / semantic decomposability、global flatness preservation、incident reduction、
障害修正コスト低下、runtime telemetry completeness、policy-aware coverage completeness、
無条件の可用性、分断耐性、収束性、特定実装 protocol correctness、
実コード log completeness、extractor completeness、実コード event log completeness、
運用コスト改善、または CRUD の一般 theorem 化
を主張しない。

## Chapter 7 Theorem Package Entrypoints

File: `Formal/Arch/Chapter7TheoremPackages.lean`

Issue [#420](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/420)
は、第7章 7.1〜7.6 の中心 theorem 候補に対応する既存 bounded theorem package を、
一箇所から import / 追跡できる入口として整理する作業である。

`Chapter7TheoremPackages.Candidate` は docs-facing な候補名、設計書の節番号、
代表 Lean declaration 名、non-conclusion boundary を束ねる軽量 API である。
この module は既存 theorem package を再利用する統合入口であり、無条件の global theorem、
extractor completeness、runtime / semantic completeness、solver completeness を新たに
主張しない。

Issue [#421](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/421)
は、数学設計書の schematic name と Lean API 名の対応を
`Chapter7TheoremPackages.SchematicCorrespondence` と
`Chapter7TheoremPackages.Candidate.schematicCorrespondences` で安定化する。
この対応表は docs-facing metadata であり、既存 bounded package の薄い読み替えに留める。

| 設計書 | 候補 | 代表 Lean entrypoint | Status |
| --- | --- | --- | --- |
| 7.1 | Split Extension Preservation | `SplitFeatureExtensionWithin`, `architectureFlatWithin_of_splitFeatureExtensionWithin`, `LawfulExtensionPreservesFlatness`, `LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation` | `defined only` / `proved` |
| 7.2 | Non-split Extension Witness | `NonSplitExtensionWitnessPackage`, `NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitness`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension` | `defined only` / `proved` |
| 7.3 | Repair as Re-splitting | `SelectedObstructionUniverse`, `AdmissibleRepairRule`, `repairStepDecreases_of_admissible`, `extensionObstructionMeasure_decreases_of_admissible` | `defined only` / `proved` |
| 7.4 | Complexity Transfer | `BoundedComplexityTransferPackage`, `BoundedComplexityTransferPackage.complexityTransfer_selectedAlternative`, `BoundedComplexityTransferPackage.no_free_elimination_bounded` | `defined only` / `proved` |
| 7.5 | No-solution Certificate | `NoSolutionCertificate`, `ValidNoSolutionCertificate`, `NoSolutionCertificate.sound_of_valid` | `defined only` / `proved` |
| 7.6 | Architecture Evolution | `ArchitectureTransition`, `ArchitectureEvolution`, `ArchitectureTransition.flatness_of_transitionPreservesFlatness`, `ArchitectureTransition.reportedObstruction_of_drift`, `eventuallyFlat_of_targetFlat`, `evolutionPathPreservesFlatness` | `defined only` / `proved` |

### Chapter 7 schematic name correspondence

| 設計書の schematic name | 対応する Lean API | 読み替え |
| --- | --- | --- |
| `SplitFeatureExtensionWithin U X F X'` | `SplitFeatureExtensionWithin`, `splitFeatureExtensionWithin_of_runtimeSemanticSplitPreservation` | explicit `ComponentUniverse` 上の bounded split feature extension package。 |
| `InteractionLawfulWithin U X F X'` | `RuntimeSemanticSplitPreservation`, `RuntimeInteractionProtected`, `FeatureDiagramsCommute`, `LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation` | runtime interaction protection と selected semantic diagram commutation を束ねた証拠として読む。 |
| `ArchitectureFlatWithin U X'` | `ArchitectureFlatWithin`, `architectureFlatWithin_of_splitFeatureExtensionWithin`, `LawfulExtensionPreservesFlatness` | coverage と measured semantic diagram に相対化された bounded flatness。global `ArchitectureFlat` ではない。 |
| `ExtensionObstructionWitness X F X' w` | `ExtensionObstructionWitness`, `SelectedExtensionObstructionWitness`, `NonSplitExtensionWitnessPackage.WitnessPredicate` | selected witness universe 内の obstruction witness。 |
| `ExtensionWitnessComplete X F X'` | `NonSplitExtensionWitnessPackage.coverageAssumptions`, `NonSplitExtensionWitnessPackage.exactnessAssumptions`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension` | non-split から selected witness 存在を得る逆向きは coverage / exactness assumptions に相対化する。 |
| `NonSplitExtensionWitness X F X' w` | `SelectedObstructionUniverse`, `NonSplitExtensionWitness` | repair 側では選択された obstruction universe の witness として読む。 |
| `AdmissibleRepairRule r w` | `AdmissibleRepairRule`, `repairStepDecreases_of_admissible`, `extensionObstructionMeasure_decreases_of_admissible` | selected rule / witness pair に対する selected measure decrease。 |
| `ComplexityTransferredTo Runtime/Semantic/Policy t` | `ComplexityTransferredTo`, `ComplexityTransferTarget.runtime`, `ComplexityTransferTarget.semantic`, `ComplexityTransferTarget.policy`, `ComplexityTransferredWithinSelectedTargets` | selected runtime / semantic / policy target axis への bounded transfer witness。 |
| Complexity Transfer theorem candidate | `BoundedComplexityTransferPackage`, `BoundedComplexityTransferPackage.complexityTransfer_selectedAlternative`, `BoundedComplexityTransferPackage.no_free_elimination_bounded` | proof elimination がない場合の selected target transfer を返す bounded alternative。 |
| `ProducesNoSolutionCertificate C cert` | `NoSolutionCertificate` | solver failure ではなく proof-carrying certificate package。 |
| `ValidNoSolutionCertificate cert C` | `ValidNoSolutionCertificate`, `NoSolutionCertificate.sound_of_valid` | valid certificate から selected constraint system の no-solution soundness を得る。 |
| `TransitionPreservesFlatness t` | `ArchitectureTransition.TransitionPreservesFlatness`, `ArchitectureTransition.flatness_of_transitionPreservesFlatness` | selected flatness predicate に対する single-step preservation。 |
| `ReportedObstruction (ApplyTransition X t) w` | `ArchitectureTransition.ReportedObstruction`, `ArchitectureTransition.reportedObstruction_of_drift` | selected drift evidence に相対化された obstruction reporting。 |
| `EventuallyFlat plan` | `EventuallyFlat`, `eventuallyFlat_of_targetFlat`, `evolutionPathPreservesFlatness` | selected migration path または preserving path に対する bounded eventual flatness。 |

Non-conclusions: この統合入口は、既存 package の bounded / coverage-aware な読みを
横断的に索引するだけである。global `ArchitectureFlat`、全 obstruction coverage、
extractor completeness、runtime telemetry completeness、semantic universe completeness、
solver completeness、empirical cost 改善、global complexity conservation は結論しない。

## Repair

File: `Formal/Arch/Repair.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `SelectedObstructionUniverse` | `structure` | repair theorem package が追跡する selected witness family と selected obstruction measure を束ねる。 | `defined only` |
| `NonSplitExtensionWitness` | `def` | selected obstruction universe 内で、state に witness が存在することを表す。 | `defined only` |
| `ExtensionObstructionMeasure` | `def` | selected obstruction universe が state に割り当てる measure を取り出す。 | `defined only` |
| `RepairStep` | `structure` | selected rule を source state から target state へ適用する repair step skeleton。 | `defined only` |
| `RepairStepDecreases` | `def` | target の selected obstruction measure が source より小さいこと。 | `defined only` |
| `AdmissibleRepairRule` | `structure` | selected witness に対し、repair step が selected measure を減少させることと non-conclusions を束ねる。 | `defined only` |
| `AdmissibleRepairRule.selected` | `theorem` | admissible repair rule が対象 witness を selected universe 内の witness として記録していることを取り出す。 | `proved` |
| `AdmissibleRepairRule.RecordsNonConclusions` | `def` | admissible repair rule の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `AdmissibleRepairRule.records_nonConclusions_iff` | `theorem` | recorded non-conclusion clause と rule field が一致すること。 | `proved` |
| `repairStepDecreases_of_admissible` | `theorem` | selected witness、admissible repair rule、repair step から selected obstruction measure の減少を得る。 | `proved` |
| `extensionObstructionMeasure_decreases_of_admissible` | `theorem` | named measure 形式で selected obstruction measure の減少を得る。 | `proved` |

Non-conclusions: repair theorem package は runtime flatness、semantic flatness、all obstruction removal、
repair termination、finite repair、synthesis soundness、no-solution certificate soundness を主張しない。

## Repair Synthesis

File: `Formal/Arch/RepairSynthesis.lean`

Issue [#277](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/277)
の対象範囲は、既存の local `RepairStepDecreases` から分離して、bounded finite repair、
synthesis soundness、valid no-solution certificate soundness を schema として整理することである。
solver が `none` を返すだけでは非存在を主張しない。
Issues [#322](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/322)
and [#327](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/327)
audit the package-level entry points here: finite repair clears only the selected
obstruction universe under explicit plan assumptions, synthesis soundness only
reads back produced candidate soundness, and no-solution soundness requires a
valid certificate.

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `SelectedObstructionsCleared` | `def` | selected obstruction universe 内の witness が target state に存在しないこと。 | `defined only` |
| `BoundedRepairPlan` | `structure` | finite bound、step bound、target measure zero、zero measure から selected witness absence への coverage bridge、non-conclusions を束ねる bounded repair plan schema。 | `defined only` |
| `BoundedRepairPlan.finite_steps_within_initial_measure` | `theorem` | finite repair plan の step 数が initial selected measure bound 内にあることを取り出す。 | `proved` |
| `BoundedRepairPlan.selectedObstructionsCleared` | `theorem` | bounded repair plan から selected obstruction universe の target clearing を得る。 | `proved` |
| `BoundedRepairPlan.RecordsNonConclusions` | `def` | bounded repair plan の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `FiniteRepairPackage` | `structure` | bounded repair plan、coverage / exactness assumptions、non-conclusions を束ねる finite repair theorem package。 | `defined only` |
| `FiniteRepairPackage.selectedObstructionsCleared` | `theorem` | finite repair package から selected obstruction universe の target clearing を得る。 | `proved` |
| `FiniteRepairPackage.RecordsNonConclusions` | `def` | finite repair package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `SynthesisConstraintSystem` | `structure` | required constraint predicate と state satisfaction predicate を束ねる synthesis problem schema。 | `defined only` |
| `ArchitectureSatisfies` | `def` | state が required constraints をすべて満たすこと。 | `defined only` |
| `NoArchitectureSatisfies` | `def` | required constraints をすべて満たす architecture state が存在しないこと。 | `defined only` |
| `SynthesisSoundnessPackage` | `structure` | produced candidate、candidate soundness、coverage / exactness assumptions、non-conclusions を束ねる synthesis soundness package。 | `defined only` |
| `SynthesisSoundnessPackage.candidate_satisfies` | `theorem` | produced candidate が required constraints を満たすことを取り出す。 | `proved` |
| `SynthesisSoundnessPackage.RecordsNonConclusions` | `def` | synthesis package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `NoSolutionCertificate` | `structure` | certificate value、valid predicate、valid certificate から no-solution conclusion への soundness、coverage / exactness assumptions、non-conclusions を束ねる。 | `defined only` |
| `ValidNoSolutionCertificate` | `def` | no-solution certificate package の valid field を公開 predicate として読む。 | `defined only` |
| `NoSolutionCertificate.sound_of_valid` | `theorem` | `ValidNoSolutionCertificate` から `NoArchitectureSatisfies` を得る。 | `proved` |
| `NoSolutionCertificate.RecordsNonConclusions` | `def` | certificate package の non-conclusion clause を predicate として取り出す。 | `defined only` |

## Architecture Extension Formula

File: `Formal/Arch/ArchitectureExtensionFormula.lean`

Issues [#321](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/321)
and [#326](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/326)
audit this package as the Lean entry point for mathematical design sections 7.2,
9, and 10.  The package separates the soundness direction, the bounded
completeness direction under explicit coverage / exactness assumptions, and the
coverage-style structural classification theorem.

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ExtensionCoverage` | `abbrev` | `Flatness.lean` の `ExtensionCoverageComplete` に、Architecture Extension Formula 用の公開名を与える。 | `defined only` |
| `ExtensionObstructionClass` | `inductive` | inherited core / feature local / interaction / lifting failure / filling failure / complexity transfer / residual coverage gap の bounded classification class。 | `defined only` |
| `ExtensionObstructionWitness` | `structure` | 抽象 witness payload と選択された `ExtensionObstructionClass` を束ねる。具体的な static / runtime / semantic / analytic witness family は後続 bridge で接続する。 | `defined only` |
| `MultiLabelExtensionObstructionWitness` | `structure` | 抽象 witness payload と、複数の `ExtensionObstructionClass` を許す label predicate、少なくとも一つの selected label による coverage 証拠を束ねる。 | `defined only` |
| `ExtensionObstructionWitness.toMultiLabel` | `def` | 既存 single-label witness を payload 不変のまま multi-label witness へ埋め込む。 | `defined only` |
| `ExtensionObstructionWitness.toMultiLabel_witness` | `theorem` | single-label から multi-label への bridge が payload を保つことを示す。 | `proved` |
| `ExtensionObstructionWitness.toMultiLabel_label_iff` | `theorem` | bridge 後の label predicate が元の `classifiesAs` と一致することを示す。 | `proved` |
| `ExtensionObstructionWitness.toMultiLabel_classifiesAs` | `theorem` | bridge 後の multi-label witness が元の classification label を持つことを示す。 | `proved` |
| `FillingFailureWitnessPayload` | `structure` | `NonFillabilityWitnessFor` を required diagram の filling failure payload として包む bridge witness。payload 単独では selected split failure を主張しない。 | `defined only` |
| `fillingFailureExtensionObstructionWitness` | `def` | selected diagram non-fillability payload から `.fillingFailure` に分類された `ExtensionObstructionWitness` を構成する。 | `defined only` |
| `SelectedSplitExtension` | `def` | feature extension と selected split predicate を結び、global split completeness を固定しないための selected split predicate。 | `defined only` |
| `SelectedExtensionObstructionWitness` | `def` | selected obstruction universe 内の `ExtensionObstructionWitness` であることを表す predicate。 | `defined only` |
| `SelectedExtensionObstructionWitnessExists` | `def` | selected obstruction universe 内に witness が存在すること。 | `defined only` |
| `SelectedExtensionWitnessSound` | `def` | selected witness が selected split predicate を反証する soundness 関係。 | `defined only` |
| `SelectedExtensionWitnessComplete` | `def` | selected split 失敗から selected witness 存在を得る bounded completeness 関係。 | `defined only` |
| `NonSplitExtensionWitnessPackage` | `structure` | selected split predicate、selected obstruction witness predicate、coverage / exactness assumptions、soundness、bounded completeness、non-conclusions を束ねる theorem package。 | `defined only` |
| `NonSplitExtensionWitnessPackage.SplitPredicate` | `def` | package が対象にする selected split predicate を取り出す。 | `defined only` |
| `NonSplitExtensionWitnessPackage.WitnessPredicate` | `def` | package が対象にする selected witness predicate を取り出す。 | `defined only` |
| `NonSplitExtensionWitnessPackage.WitnessExists` | `def` | package の selected witness universe 内に witness が存在すること。 | `defined only` |
| `NonSplitExtensionWitnessPackage.RecordsNonConclusions` | `def` | theorem package が明示的な non-conclusions を持つこと。 | `defined only` |
| `NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitness` | `theorem` | selected obstruction witness から selected split predicate の不成立を得る soundness theorem。 | `proved` |
| `NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitnessExists` | `theorem` | selected witness 存在から selected split predicate の不成立を得る soundness-only theorem。 | `proved` |
| `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension` | `theorem` | coverage / exactness assumptions の下で selected split 失敗から selected witness 存在を得る bounded completeness theorem。 | `proved` |
| `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension` | `theorem` | coverage / exactness assumptions に相対化された selected witness 存在と selected split 失敗の同値。 | `proved` |
| `NonSplitExtensionWitnessPackage.records_nonConclusions_iff` | `theorem` | recorded non-conclusion clause と package field が一致すること。 | `proved` |
| `ClassifiedAsInheritedCore` | `def` | witness が embedded core 由来として分類されること。 | `defined only` |
| `ClassifiedAsFeatureLocal` | `def` | witness が追加 feature 内部由来として分類されること。 | `defined only` |
| `ClassifiedAsInteraction` | `def` | witness が feature/core interaction 境界由来として分類されること。 | `defined only` |
| `ClassifiedAsLiftingFailure` | `def` | witness が selected feature step の lifting failure として分類されること。 | `defined only` |
| `ClassifiedAsFillingFailure` | `def` | witness が required diagram の filling failure として分類されること。 | `defined only` |
| `fillingFailureExtensionObstructionWitness_classified` | `theorem` | bridge constructor で作った witness が `ClassifiedAsFillingFailure` を満たすことを示す。 | `proved` |
| `FillingFailureRefutesSplit` | `def` | selected filling-failure payload が selected split predicate を反駁するための明示 premise。`NonFillabilityWitnessFor` 単独では split failure を結論しない。 | `defined only` |
| `not_selectedSplitExtension_of_fillingFailurePayload` | `theorem` | `FillingFailureRefutesSplit` 前提の下で selected payload から selected split failure を得る bounded soundness theorem。 | `proved` |
| `FillingFailureBridgePackage` | `structure` | selected filling-failure payload universe、coverage / exactness assumptions、split refutation premise、bounded completeness、non-conclusions を束ねる bridge package。 | `defined only` |
| `FillingFailureBridgePackage.SelectedWitness` | `def` | bridge package が誘導する `.fillingFailure` 分類済み selected extension witness predicate。 | `defined only` |
| `FillingFailureBridgePackage.toNonSplitExtensionWitnessPackage` | `def` | filling-failure bridge package を generic `NonSplitExtensionWitnessPackage` へ埋め込む。 | `defined only` |
| `FillingFailureBridgePackage.selectedExtensionObstructionWitnessExists_of_selectedPayloadExists` | `theorem` | selected payload の存在から generic package 側の selected obstruction witness 存在を構成する。 | `proved` |
| `ClassifiedAsComplexityTransfer` | `def` | witness が complexity / analytic diagnostic axis への transfer として分類されること。 | `defined only` |
| `ClassifiedAsResidualCoverageGap` | `def` | witness が residual evidence または bounded coverage gap として分類されること。 | `defined only` |
| `ArchitectureExtensionFormula_structural` | `theorem` | bounded extension coverage の下で、任意の selected extension obstruction witness が 7 分類 predicate の少なくとも一つで cover されること。 | `proved` |
| `MultiLabelClassifiedAsInheritedCore` | `def` | multi-label witness が embedded core 由来 label を持つこと。 | `defined only` |
| `MultiLabelClassifiedAsFeatureLocal` | `def` | multi-label witness が追加 feature 内部由来 label を持つこと。 | `defined only` |
| `MultiLabelClassifiedAsInteraction` | `def` | multi-label witness が feature/core interaction label を持つこと。 | `defined only` |
| `MultiLabelClassifiedAsLiftingFailure` | `def` | multi-label witness が lifting failure label を持つこと。 | `defined only` |
| `MultiLabelClassifiedAsFillingFailure` | `def` | multi-label witness が filling failure label を持つこと。 | `defined only` |
| `fillingFailureExtensionObstructionWitness_multilabel_classified` | `theorem` | filling-failure bridge witness を multi-label layer に埋め込んでも `.fillingFailure` label が得られることを示す。 | `proved` |
| `MultiLabelClassifiedAsComplexityTransfer` | `def` | multi-label witness が complexity / analytic transfer label を持つこと。 | `defined only` |
| `MultiLabelClassifiedAsResidualCoverageGap` | `def` | multi-label witness が residual evidence / coverage gap label を持つこと。 | `defined only` |
| `ArchitectureExtensionFormula_multilabel_structural` | `theorem` | bounded extension coverage の下で、任意の multi-label extension obstruction witness が 7 分類 predicate の少なくとも一つで cover されること。 | `proved` |

Non-conclusions: 最初の theorem package は disjoint decomposition、global extractor
completeness、runtime / semantic universe completeness、または universe 外の obstruction
分類を主張しない。`NonSplitExtensionWitnessPackage` の同値版も package の
coverage / exactness assumptions に相対化され、global witness completeness は主張しない。
diagram filling failure から split failure への接続は `FillingFailureRefutesSplit` または
`FillingFailureBridgePackage` の明示 premise に相対化され、`NonFillabilityWitnessFor`
単独から `¬ SplitExtension` は結論しない。
bounded flatness preservation は runtime / semantic flatness と coverage assumptions を明示する
`LawfulExtensionPreservesFlatness` として `Formal/Arch/Flatness.lean` で証明済みである。
このため `ArchitectureExtensionFormula_structural` と
`ArchitectureExtensionFormula_multilabel_structural` は 7 分類の少なくとも一つに入ることを
述べる coverage theorem であり、分類が互いに素であることや全 obstruction universe の
完全分類は結論しない。multi-label layer は同一 witness が複数 label を持つことを許し、
single-label layer との bridge は payload preservation と元 label の保存だけを主張する。

## Complexity Transfer

File: `Formal/Arch/ComplexityTransfer.lean`

Issue [#288](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/288)
の対象範囲は、static complexity の削減が proof elimination なのか、runtime /
semantic / policy axis への selected transfer witness なのかを返す bounded theorem
package として整理することである。empirical cost 改善、global complexity
conservation、selected witness universe 外の completeness は non-conclusions として
扱う。
Issues [#323](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/323)
and [#328](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/328)
audit this section as the bounded complexity-transfer entry point.  The
representative theorem is
`BoundedComplexityTransferPackage.no_free_elimination_bounded`: when selected
static reduction and requirement preservation hold, non-elimination by proof
forces a selected runtime / semantic / policy transfer witness, not a global
conservation or empirical cost theorem.

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ComplexityTransferTarget` | `inductive` | runtime / semantic / policy の selected transfer target axis。 | `defined only` |
| `ComplexityTransferTarget.label` | `def` | documentation-facing な target label。 | `defined only` |
| `ArchitectureTransform` | `structure` | selected transform の source / target と bounded-universe assumption、non-conclusions を束ねる schema。 | `defined only` |
| `ArchitectureTransform.RecordsNonConclusions` | `def` | transform schema の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `SelectedComplexityMeasure` | `structure` | bounded measurement universe に相対化された natural-valued complexity measure。 | `defined only` |
| `ReducesStaticComplexity` | `def` | selected static measure が transform target で source より小さいこと。 | `defined only` |
| `RequirementSchema` | `structure` | selected requirement universe と satisfaction predicate を束ねる schema。 | `defined only` |
| `PreservesRequirements` | `def` | selected requirements の satisfaction truth が source / target で一致すること。 | `defined only` |
| `ComplexityTransferSchema` | `structure` | proof elimination predicate、target-indexed transfer witness、selected witness predicate、assumptions、non-conclusions を束ねる schema。 | `defined only` |
| `ComplexityEliminatedByProof` | `def` | selected transform の complexity が proof により消去されたこと。 | `defined only` |
| `ComplexityTransferredTo` | `def` | selected witness によって target axis への transfer を示すこと。 | `defined only` |
| `ComplexityTransferredWithinSelectedTargets` | `def` | selected witness が runtime / semantic / policy のいずれかの bounded target axis へ移転すること。 | `defined only` |
| `ComplexityTransferAlternative` | `def` | selected transform について proof elimination または selected target transfer の bounded alternative。 | `defined only` |
| `ComplexityTransferResidualGap` | `def` | coverage / exactness が閉じていない residual gap を bounded diagnostic predicate として記録する。 | `defined only` |
| `ComplexityTransferredTo.has_selectedWitness` | `theorem` | transfer conclusion から selected witness の存在を取り出す。 | `proved` |
| `BoundedComplexityTransferPackage` | `structure` | selected static reduction と requirement preservation から proof elimination または selected transfer witness を返す bounded theorem package。 | `defined only` |
| `BoundedComplexityTransferPackage.complexityTransfer_alternative` | `theorem` | bounded theorem package から proof elimination / runtime transfer / semantic transfer / policy transfer の alternative を得る。 | `proved` |
| `BoundedComplexityTransferPackage.complexityTransfer_selectedAlternative` | `theorem` | bounded theorem package から named selected-target predicate を使った `ComplexityTransferAlternative` を得る。 | `proved` |
| `BoundedComplexityTransferPackage.no_free_elimination_bounded` | `theorem` | selected static reduction と requirement preservation の下で proof elimination がなければ、runtime / semantic / policy の selected transfer witness がある。 | `proved` |
| `BoundedComplexityTransferPackage.RecordsNonConclusions` | `def` | complexity-transfer package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `BoundedComplexityTransferPackage.records_nonConclusions_iff` | `theorem` | recorded non-conclusion predicate が schema field と一致すること。 | `proved` |

## Repair Transfer Counterexample

File: `Formal/Arch/RepairTransferCounterexample.lean`

Issue [#353](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/353)
の対象範囲は、repair step が selected obstruction measure を減少させても、
別の diagnostic axis で obstruction / transferred complexity が増える可能性を
最小 skeleton として固定することである。これは repair theorem が selected measure に
相対化されており、全 axis の単調改善や global flatness preservation を主張しないことを
Lean 側の counterexample package として記録する。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `RepairTransferCounterexample.RepairState` | `inductive` | static witness を持つ `entangled` と、static repair 後の `repaired` の 2 状態 skeleton。 | `defined only` |
| `RepairTransferCounterexample.RepairWitness` | `inductive` | selected static witness `staticLeak` と別軸 witness `runtimeBackpressure`。 | `defined only` |
| `RepairTransferCounterexample.selectedStaticUniverse` | `def` | selected static obstruction universe。measure は `entangled = 1`, `repaired = 0`。 | `defined only` |
| `RepairTransferCounterexample.runtimeAxisUniverse` | `def` | runtime diagnostic axis。measure は `entangled = 0`, `repaired = 1`。 | `defined only` |
| `RepairTransferCounterexample.staticRepairStep` | `def` | selected static repair step skeleton。 | `defined only` |
| `RepairTransferCounterexample.selectedRepairStep_decreases` | `theorem` | concrete repair step で selected static measure が減少する。 | `proved` |
| `RepairTransferCounterexample.selectedRepairStep_decreases_of_admissible` | `theorem` | 既存 `AdmissibleRepairRule` API から同じ selected-measure decrease を得る bridge。 | `proved` |
| `RepairTransferCounterexample.runtimeAxisMeasure_increases` | `theorem` | 同じ endpoint で runtime-axis measure が `0 -> 1` に増える。 | `proved` |
| `RepairTransferCounterexample.runtimeAxis_noMeasuredViolation_before` | `theorem` | repair 前の runtime measured witness universe には violation がない。 | `proved` |
| `RepairTransferCounterexample.runtimeAxis_measuredViolation_after` | `theorem` | repair 後には runtime measured violation witness が存在する。 | `proved` |
| `RepairTransferCounterexample.runtimeAxisViolationCount_before` | `theorem` | repair 前の runtime measured violation count は 0。 | `proved` |
| `RepairTransferCounterexample.runtimeAxisViolationCount_after` | `theorem` | repair 後の runtime measured violation count は 1。 | `proved` |
| `RepairTransferCounterexample.selectedRepairStep_not_all_axes_nonincreasing` | `theorem` | selected static repair endpoint は selected+runtime 全軸の nonincreasing step ではない。 | `proved` |
| `RepairTransferCounterexample.staticSplitRepair_reducesStaticComplexity` | `theorem` | 同じ step を `ReducesStaticComplexity` として complexity-transfer schema に接続する。 | `proved` |
| `RepairTransferCounterexample.staticSplitRepair_not_eliminated_by_proof` | `theorem` | この skeleton では proof elimination ではないことを selected schema 上で記録する。 | `proved` |
| `RepairTransferCounterexample.staticSplitRepair_transfers_runtime` | `theorem` | runtime target への selected transfer witness が存在する。 | `proved` |
| `RepairTransferCounterexample.repairComplexityTransfer_records_nonConclusion` | `theorem` | repair が全 axis 単調改善ではない non-conclusion を schema field として記録する。 | `proved` |
| `RepairTransferCounterexample.RepairTransferCounterexamplePackage` | `structure` | selected decrease、runtime increase、violation count、runtime transfer、non-conclusion を束ねる package。 | `defined only` |
| `RepairTransferCounterexample.counterexamplePackage` | `def` | Issue #353 の concrete counterexample package。 | `defined only` |

## Architecture Path

File: `Formal/Arch/ArchitecturePath.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitecturePath` | `inductive` | `Step : State -> State -> Type` に相対化された有限 architecture evolution path。型 index が start / target state を保持する。 | `defined only` |
| `ArchitecturePath.ApplyPath` | `def` | path を start state に適用した target state を返す endpoint projection。 | `defined only` |
| `ArchitecturePath.length` | `def` | path に含まれる primitive architecture step 数。 | `defined only` |
| `ArchitecturePath.append` | `def` | endpoint が一致する二つの architecture path を連結する。 | `defined only` |
| `ArchitecturePath.InvariantHolds` | `def` | state predicate としての architecture invariant が特定 state で成り立つこと。 | `defined only` |
| `ArchitecturePath.StepPreservesInvariant` | `def` | primitive step が invariant を source から target へ保存すること。 | `defined only` |
| `ArchitecturePath.EveryStepPreserves` | `def` | path 上のすべての primitive step が invariant を保存すること。 | `defined only` |
| `ArchitecturePath.pathPreservesInvariant` | `theorem` | すべての step が invariant を保存するなら、path 全体も start から target へ invariant を保存する。 | `proved` |
| `ArchitecturePath.PathHomotopy` | `inductive` | refl / symm / trans と、independent square swap、same external contract replacement、repair fill で生成される有限 path homotopy relation。 | `defined only` |
| `ArchitecturePath.HomotopyInvariant` | `def` | generated path homotopy の下で安定な invariant。endpoint と state universe は `ArchitecturePath` の index によって明示される。 | `defined only` |
| `ArchitecturePath.architectureHomotopyInvariance` | `theorem` | `HomotopyInvariant` を homotopic path pair に適用する bridge theorem。 | `proved` |

## Architecture Evolution

File: `Formal/Arch/ArchitectureEvolution.lean`

Issue [#278](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/278) の対象範囲は、既存
`ArchitecturePath` の endpoint-indexed path を再利用し、その上に evolution-specific な
transition tag、bounded flatness preservation、drift-obstruction reporting、migration plan
schema を置くことである。global extractor completeness、全 obstruction coverage、任意の
flatness predicate の自動保存は主張しない。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureTransitionKind` | `inductive` | `featureExtension`, `drift`, `repair`, `migration`, `policyUpdate`, `runtimeTopologyChange`, `semanticContractChange` の evolution transition tag。 | `defined only` |
| `ArchitectureTransitionKind.label` | `def` | documentation-facing な transition tag label。 | `defined only` |
| `ArchitectureTransition` | `structure` | source / target を型 index に持つ primitive transition。kind、lawful、coverage / exactness assumptions、non-conclusions を明示する。 | `defined only` |
| `ArchitectureTransition.ApplyTransition` | `def` | transition を source state に適用した target state を返す endpoint projection。 | `defined only` |
| `ArchitectureTransition.TransitionPreservesFlatness` | `def` | selected bounded flatness predicate が transition の source から target へ保存されること。 | `defined only` |
| `ArchitectureTransition.RecordsNonConclusions` | `def` | transition package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `ArchitectureTransition.flatness_of_transitionPreservesFlatness` | `theorem` | `ArchitectureFlat X` と `TransitionPreservesFlatness t` から `ArchitectureFlat (ApplyTransition X t)` を得る single-step preservation theorem。 | `proved` |
| `ArchitectureTransition.FeatureExtensionStep` | `def` | transition が feature-extension step tag を持つこと。 | `defined only` |
| `ArchitectureTransition.DriftEvent` | `def` | transition が drift event tag を持つこと。 | `defined only` |
| `ArchitectureTransition.RepairTransition` | `def` | transition が repair tag を持つこと。 | `defined only` |
| `ArchitectureTransition.MigrationStep` | `def` | transition が migration tag を持つこと。 | `defined only` |
| `ArchitectureTransition.PolicyUpdate` | `def` | transition が policy update tag を持つこと。 | `defined only` |
| `ArchitectureTransition.RuntimeTopologyChange` | `def` | transition が runtime topology change tag を持つこと。 | `defined only` |
| `ArchitectureTransition.SemanticContractChange` | `def` | transition が semantic contract change tag を持つこと。 | `defined only` |
| `ArchitectureTransition.DriftObstructionSchema` | `structure` | selected introduced obstruction witness、reported witness predicate、drift reporting soundness、coverage / exactness / non-conclusions を束ねる bounded schema。 | `defined only` |
| `ArchitectureTransition.IntroducesObstruction` | `def` | selected schema に相対化された introduced obstruction witness predicate。 | `defined only` |
| `ArchitectureTransition.ReportedObstruction` | `def` | selected schema に相対化された reported obstruction witness predicate。 | `defined only` |
| `ArchitectureTransition.reportedObstruction_of_drift` | `theorem` | `DriftEvent t` と `IntroducesObstruction t w` から `ReportedObstruction (ApplyTransition X t) w` を得る selected reporting soundness theorem。 | `proved` |
| `ArchitectureEvolution` | `abbrev` | `ArchitectureTransition` を primitive step とする finite architecture evolution path。 | `defined only` |
| `EveryTransition` | `def` | evolution sequence 上のすべての transition が selected predicate を満たすこと。 | `defined only` |
| `MigrationSequence` | `def` | すべての selected transition が migration tag を持つ bounded migration plan。 | `defined only` |
| `EveryStepLawful` | `def` | plan 上のすべての transition が local `lawful` field を満たすこと。 | `defined only` |
| `TargetFlat` | `def` | selected bounded flatness predicate が plan の target で成り立つこと。 | `defined only` |
| `EventuallyFlat` | `def` | plan が selected bounded flatness predicate を満たす target に到達すること。 | `defined only` |
| `eventuallyFlat_of_targetFlat` | `theorem` | `MigrationSequence plan`, `EveryStepLawful plan`, `TargetFlat plan` から `EventuallyFlat plan` を得る bounded theorem package。 | `proved` |
| `evolutionPathPreservesFlatness` | `theorem` | 既存 `ArchitecturePath.pathPreservesInvariant` を evolution-specific な `EventuallyFlat` 名へ bridge する theorem。 | `proved` |

## Diagram Filler

File: `Formal/Arch/DiagramFiller.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureDiagram` | `structure` | 同じ start / target state を持つ二つの有限 architecture path を semantic diagram skeleton として束ねる。 | `defined only` |
| `DiagramFiller` | `def` | `ArchitecturePath.PathHomotopy` により、diagram の左右 path が finite path calculus 上で fillable であることを表す。 | `defined only` |
| `NonFillabilityWitness` | `structure` | domain-specific witness value と、任意の `DiagramFiller` を反駁する soundness 証拠を束ねる。 | `defined only` |
| `NonFillabilityWitnessFor` | `def` | `NonFillabilityWitness` が特定の witness value `w` についての証人であること。 | `defined only` |
| `obstructionAsNonFillability_sound` | `theorem` | `NonFillabilityWitnessFor D w` から `¬ DiagramFiller D` を得る片方向 soundness theorem。 | `proved` |
| `WitnessUniverseComplete` | `def` | bounded completeness theorem 用の有限 witness universe 完全性前提。 | `defined only` |
| `obstructionAsNonFillability_complete_bounded` | `theorem` | `WitnessUniverseComplete` と `¬ DiagramFiller D` から、有限 universe 内の `NonFillabilityWitnessFor D w` を得る bounded completeness theorem。 | `proved` |
| `CouponDiscountExample.CouponState` | `inductive` | coupon / discount 順序依存例の有限状態 skeleton。 | `defined only` |
| `CouponDiscountExample.CouponDiscountStep` | `inductive` | coupon-first / discount-first の二つの operation path を表す有限 step family。 | `defined only` |
| `CouponDiscountExample.couponThenDiscount` | `def` | coupon を先に適用する selected operation path。 | `defined only` |
| `CouponDiscountExample.discountThenCoupon` | `def` | discount を先に適用する selected operation path。 | `defined only` |
| `CouponDiscountExample.couponDiscountDiagram` | `def` | coupon と discount の順序依存例を、二つの operation order を持つ diagram skeleton として表す。 | `defined only` |
| `CouponDiscountExample.CouponDiscountWitness` | `inductive` | selected rounding-order obstruction witness。 | `defined only` |
| `CouponDiscountExample.CouponDiscountStep.roundingCode` | `def` | coupon / discount step を selected rounding observation code へ写す。 | `defined only` |
| `CouponDiscountExample.roundingTrace` | `def` | coupon / discount path の selected rounding-order observation を `Nat` trace として与える。 | `defined only` |
| `CouponDiscountExample.RoundingIndependentSquare` | `def` | selected filler generator のうち rounding observation を保存する independent-square contract。 | `defined only` |
| `CouponDiscountExample.RoundingSameExternalContract` | `def` | rounding observation を保存する same-contract replacement contract。 | `defined only` |
| `CouponDiscountExample.RoundingRepairFill` | `def` | rounding observation を保存する selected repair fill contract。 | `defined only` |
| `CouponDiscountExample.pathHomotopy_preserves_roundingTrace` | `theorem` | selected filler generator から生成される path homotopy が `roundingTrace` を保存することを示す。 | `proved` |
| `CouponDiscountExample.couponThenDiscount_roundingTrace` | `theorem` | coupon-first path の selected rounding trace が `21` であることを計算する。 | `proved` |
| `CouponDiscountExample.discountThenCoupon_roundingTrace` | `theorem` | discount-first path の selected rounding trace が `43` であることを計算する。 | `proved` |
| `CouponDiscountExample.roundingOrder_refutes_selectedDiagramFiller` | `theorem` | `roundingOrder` witness が selected coupon / discount diagram filler を反駁する。 | `proved` |
| `CouponDiscountExample.roundingOrderNonFillabilityWitness` | `def` | selected coupon / discount diagram 用の concrete `NonFillabilityWitness`。 | `defined only` |
| `CouponDiscountExample.roundingOrder_nonFillabilityWitnessFor` | `theorem` | `CouponDiscountWitness.roundingOrder` が selected diagram の `NonFillabilityWitnessFor` であることを示す。 | `proved` |
| `CouponDiscountExample.roundingOrderResidual` | `def` | selected coupon / discount diagram の semantic residual を `0/1` valuation として定義する。 | `defined only` |
| `CouponDiscountExample.RoundingSemanticObstruction` | `def` | selected rounding-order residual が検出する semantic obstruction predicate。 | `defined only` |
| `CouponDiscountExample.roundingOrderValuation` | `def` | selected rounding-order residual に相対化された `ObstructionValuation` package。 | `defined only` |
| `CouponDiscountExample.couponDiscount_roundingOrderResidual_positive` | `theorem` | canonical coupon / discount diagram の selected residual が正であることを示す。 | `proved` |
| `CouponDiscountExample.roundingOrderValuation_obstruction` | `theorem` | canonical coupon / discount diagram が selected rounding-order obstruction を持つことを示す。 | `proved` |
| `CouponDiscountExample.roundingOrderValuation_positive` | `theorem` | canonical coupon / discount diagram で selected rounding-order valuation が positive になることを示す。 | `proved` |
| `CouponDiscountExample.roundingOrderValuation_recordsNonConclusions` | `theorem` | selected valuation package が non-conclusion clause を記録していることを示す。 | `proved` |

Non-conclusions: bounded completeness は `WitnessUniverseComplete` に相対化される。
coupon / discount valuation は selected rounding-order residual に相対化される。
global semantic completeness、finite universe 外の witness coverage、未測定 semantic axis の
zero 性、実コード extractor completeness は主張しない。

## Static / Semantic Counterexample

File: `Formal/Arch/StaticSemanticCounterexample.lean`

Issue [#348](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/348)
の canonical counterexample は、repaired coupon static skeleton で selected static split
と bounded static flatness が成立しても、coupon / discount の selected semantic
diagram obstruction が残り、`SemanticFlatWithin` や global `ArchitectureFlat` は
結論できないことを Lean theorem として固定する。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `StaticSemanticCounterexample.SelectedCouponOrder` | `inductive` | coupon-first / discount-first の selected semantic order expression。 | `defined only` |
| `StaticSemanticCounterexample.selectedCouponOrderSemantics` | `def` | 既存 `CouponDiscountExample.roundingTrace` を selected semantic expression の観測値として使う。 | `defined only` |
| `StaticSemanticCounterexample.selectedCouponDiscountDiagram` | `def` | coupon-first と discount-first を比較する selected required semantic diagram。 | `defined only` |
| `StaticSemanticCounterexample.selectedCouponDiscount_semanticCoverage` | `theorem` | selected diagram が measured semantic universe に cover されていることを示す。 | `proved` |
| `StaticSemanticCounterexample.selectedCouponDiscount_not_commutes` | `theorem` | selected coupon / discount diagram が commute しないことを、`21 ≠ 43` の trace 計算から示す。 | `proved` |
| `StaticSemanticCounterexample.repairedUniverse` | `def` | repaired coupon static graph 用の finite `ComponentUniverse`。 | `defined only` |
| `StaticSemanticCounterexample.repaired_strictLayering` | `theorem` | repaired coupon static graph が strict layer assignment を持つことを示す。 | `proved` |
| `StaticSemanticCounterexample.repaired_walkAcyclic` | `theorem` | strict layering から repaired coupon static graph の `WalkAcyclic` を得る。 | `proved` |
| `StaticSemanticCounterexample.canonicalFlatnessModel` | `def` | repaired static graph と selected coupon / discount semantic diagram を束ねた flatness model。 | `defined only` |
| `StaticSemanticCounterexample.repaired_staticSplit` | `theorem` | repaired coupon extension が selected static split を満たすことを再公開する。 | `proved` |
| `StaticSemanticCounterexample.canonical_staticFlatWithin` | `theorem` | canonical model が finite universe 相対で `StaticFlatWithin` を満たすことを示す。 | `proved` |
| `StaticSemanticCounterexample.canonical_not_semanticFlatWithin` | `theorem` | selected semantic obstruction により `SemanticFlatWithin` が成り立たないことを示す。 | `proved` |
| `StaticSemanticCounterexample.canonical_not_architectureFlatWithin` | `theorem` | repaired universe 相対の `ArchitectureFlatWithin` が成り立たないことを示す。 | `proved` |
| `StaticSemanticCounterexample.canonical_not_architectureFlat` | `theorem` | global completion predicate `ArchitectureFlat` が成り立たないことを示す。 | `proved` |
| `StaticSemanticCounterexample.staticFlat_with_semanticObstruction` | `theorem` | `StaticFlatWithin` と `¬ SemanticFlatWithin` を同時に持つ counterexample package。 | `proved` |
| `StaticSemanticCounterexample.staticFlat_not_architectureFlat` | `theorem` | `StaticFlatWithin` と `¬ ArchitectureFlat` を同時に持つ counterexample package。 | `proved` |

Non-conclusions: この counterexample は selected repaired static skeleton と selected
rounding-order semantic diagram に相対化される。static split / static flatness から
runtime flatness、semantic flatness、global `ArchitectureFlat`、または extractor
completeness は結論しない。

## Flatness

File: `Formal/Arch/Flatness.lean`

#320 の Flatness / Feature Extension 統合 theorem package では、
#325 の API 監査結果を踏まえ、中心入口を次のように読む。

- `ArchitectureFlatWithin` が primary な bounded / coverage-aware flatness predicate である。
- `LawfulExtensionPreservesFlatness` は static split extension だけからではなく、extension coverage、static side conditions、runtime coverage / flatness、semantic coverage / flatness を明示前提として `ArchitectureFlatWithin` を構成する。
- `LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation` は `RuntimeSemanticSplitPreservation` により runtime / semantic flatness 前提を discharge する接続 corollary であり、runtime telemetry completeness、semantic universe completeness、extractor completeness は主張しない。
- `ArchitectureFlat` は `GlobalFlatCertificate` による completion predicate であり、`globalFlat_of_within_exhaustive` の exhaustive coverage / exact observation / recorded non-conclusions 前提なしに bounded theorem package から昇格しない。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureFlatnessModel` | `structure` | static / runtime / semantic の三層 flatness を一つの architecture model として束ねる。runtime policy と semantic required / measured diagram universe を明示し、未測定軸を zero と見なさない境界を置く。 | `defined only` |
| `ArchitectureFlatnessModel.staticLawModel` | `def` | flatness model の static layer を既存の `ArchitectureLawModel` に写す。 | `defined only` |
| `StaticCoverageComplete` | `def` | supplied `ComponentUniverse` が static dependency evidence を cover すること。 | `defined only` |
| `staticCoverageComplete_of_componentUniverse` | `theorem` | `ComponentUniverse.edgeClosed` から static coverage complete を得る。 | `proved` |
| `StaticFlatWithin` | `def` | finite universe 相対の static flatness。既存の `ArchitectureLawful` package を使う。 | `defined only` |
| `RuntimeCoverageComplete` | `def` | runtime dependency evidence が supplied component universe に含まれること。 | `defined only` |
| `RuntimeFlatWithin` | `def` | measured runtime universe 内の runtime edge が runtime policy を満たすこと。 | `defined only` |
| `SemanticCoverageComplete` | `def` | measured semantic diagram list が required semantic diagrams を cover すること。 | `defined only` |
| `SemanticFlatWithin` | `def` | measured semantic diagram universe 内の diagram lawfulness。 | `defined only` |
| `RuntimeInteractionProtected` | `def` | selected universe 内の runtime interaction が target runtime policy を満たす bounded runtime split premise。 | `defined only` |
| `runtimeFlatWithin_of_runtimeInteractionProtected` | `theorem` | runtime coverage 前提の下で selected runtime protection から `RuntimeFlatWithin` を得る。 | `proved` |
| `runtimeInteractionProtected_of_runtimeFlatWithin` | `theorem` | `RuntimeFlatWithin` を selected runtime protection として読み替える。 | `proved` |
| `runtimeInteractionProtected_iff_runtimeFlatWithin` | `theorem` | runtime coverage 前提に相対化して selected runtime protection と `RuntimeFlatWithin` を同値にする。 | `proved` |
| `FeatureDiagramsCommute` | `def` | selected measured semantic diagrams がすべて commute すること。global semantic completeness は含めない。 | `defined only` |
| `semanticFlatWithin_of_featureDiagramsCommute` | `theorem` | semantic coverage 前提の下で selected diagram commutation から `SemanticFlatWithin` を得る。 | `proved` |
| `featureDiagramsCommute_of_semanticFlatWithin` | `theorem` | `SemanticFlatWithin` を selected diagram commutation として読み替える。 | `proved` |
| `featureDiagramsCommute_iff_semanticFlatWithin` | `theorem` | semantic coverage 前提に相対化して selected diagram commutation と `SemanticFlatWithin` を同値にする。 | `proved` |
| `RuntimeSemanticSplitPreservation` | `structure` | runtime interaction protection と selected semantic diagram commutation を束ねる bounded runtime / semantic split preservation package。 | `defined only` |
| `NoUnmeasuredRequiredAxis` | `def` | static / runtime / semantic の required evidence が bounded universes で測定済みであること。 | `defined only` |
| `ArchitectureFlatWithin` | `def` | coverage-aware な bounded architecture flatness。coverage と三層 flatness を束ね、global extractor / telemetry / semantic universe completeness は主張しない。 | `defined only` |
| `staticFlatWithin_of_architectureFlatWithin` | `theorem` | bounded architecture flatness から static flatness を取り出す。 | `proved` |
| `runtimeFlatWithin_of_architectureFlatWithin` | `theorem` | bounded architecture flatness から runtime flatness を取り出す。 | `proved` |
| `semanticFlatWithin_of_architectureFlatWithin` | `theorem` | bounded architecture flatness から semantic flatness を取り出す。 | `proved` |
| `noUnmeasuredRequiredAxis_of_architectureFlatWithin` | `theorem` | bounded architecture flatness から coverage package を取り出す。 | `proved` |
| `ExhaustiveFlatnessCoverage` | `def` | bounded flatness を global completion として読むための exhaustive coverage premise。`NoUnmeasuredRequiredAxis` を明示名で公開する。 | `defined only` |
| `ExactFlatnessObservation` | `def` | selected static / runtime / semantic flatness evidence を bounded `ArchitectureFlatWithin` へまとめる exact observation bridge。extractor / telemetry completeness は主張しない。 | `defined only` |
| `exactFlatnessObservation_of_exhaustiveCoverage` | `theorem` | exhaustive coverage から既存三層 flatness の exact-observation bridge を構成する。 | `proved` |
| `GlobalFlatCertificate` | `structure` | `ArchitectureFlatWithin`、exhaustive coverage、exact observation、non-conclusions を束ね、global flatness を completion corollary として読むための certificate。 | `defined only` |
| `ArchitectureFlat` | `def` | `GlobalFlatCertificate` の存在として定義される global completion predicate。primary theorem package ではない。 | `defined only` |
| `GlobalFlatCertificate.architectureFlatWithin` | `theorem` | certificate から underlying bounded flatness を取り出す。 | `proved` |
| `GlobalFlatCertificate.exhaustiveFlatnessCoverage` | `theorem` | certificate から exhaustive coverage premise を取り出す。 | `proved` |
| `GlobalFlatCertificate.exactFlatnessObservation` | `theorem` | certificate から exact observation premise を取り出す。 | `proved` |
| `GlobalFlatCertificate.nonConclusions_recorded` | `theorem` | certificate が記録する non-conclusions を取り出す。 | `proved` |
| `globalFlat_of_within_exhaustive` | `theorem` | `ArchitectureFlatWithin` を、exhaustive coverage / exact observation / recorded non-conclusions 前提つきで `ArchitectureFlat` へ上げる completion corollary。 | `proved` |
| `ExtensionCoverageComplete` | `def` | feature extension の core embedding、feature embedding、extended static edges、declared coverage assumptions が supplied extended universe で cover されること。 | `defined only` |
| `ExtensionCoverageWitness` | `inductive` | `ExtensionCoverageComplete` の失敗を、core embedding 未測定、feature embedding 未測定、extended edge endpoint 未測定、declared coverage assumption failure として表す selected coverage diagnostic witness family。`StaticExtensionWitness` とは別の coverage-only 診断である。 | `defined only` |
| `ExtensionCoverageWitnessExists` | `def` | selected extension-coverage witness が存在すること。 | `defined only` |
| `ExtensionCoverageFailureCoverage` | `def` | `ExtensionCoverageComplete` 失敗が selected coverage witness family で cover されるという bounded coverage / exactness 前提。extractor completeness や runtime / semantic flatness は主張しない。 | `defined only` |
| `not_extensionCoverageComplete_of_extensionCoverageWitness` | `theorem` | selected coverage witness が対応する `ExtensionCoverageComplete` を反証する soundness theorem。 | `proved` |
| `not_extensionCoverageComplete_of_extensionCoverageWitnessExists` | `theorem` | selected coverage witness の存在から `ExtensionCoverageComplete` の不成立を得る。 | `proved` |
| `extensionCoverageWitnessExists_of_not_extensionCoverageComplete` | `theorem` | `ExtensionCoverageFailureCoverage` 前提の下で、`ExtensionCoverageComplete` の失敗から selected coverage witness の存在を得る bounded completeness theorem。 | `proved` |
| `extensionCoverageWitnessExists_iff_not_extensionCoverageComplete` | `theorem` | selected coverage / exactness 前提に相対化された、selected coverage witness 存在と `ExtensionCoverageComplete` 失敗の同値。 | `proved` |
| `StaticSplitExtensionCoverageComplete` | `def` | `StaticSplitExtension` 用の coverage package。 | `defined only` |
| `coreEmbedding_mem_of_extensionCoverageComplete` | `theorem` | complete extension coverage から core embedding の universe membership を得る。 | `proved` |
| `featureEmbedding_mem_of_extensionCoverageComplete` | `theorem` | complete extension coverage から feature embedding の universe membership を得る。 | `proved` |
| `extended_edge_mem_of_extensionCoverageComplete` | `theorem` | complete extension coverage から extended static edge endpoints の universe membership を得る。 | `proved` |
| `policySound_of_staticSplitExtension` | `theorem` | compatible な static graph に対して、`StaticSplitExtension` の no-new-forbidden-edge 条件から policy soundness を得る。 | `proved` |
| `boundaryPolicySound_of_staticSplitExtension` | `theorem` | compatible な static graph に対して、`StaticSplitExtension` 由来の boundary policy soundness を取り出す。acyclicity、projection、LSP、runtime / semantic flatness は結論しない。 | `proved` |
| `abstractionPolicySound_of_staticSplitExtension` | `theorem` | compatible な static graph に対して、`StaticSplitExtension` 由来の abstraction policy soundness を取り出す。projection soundness 自体は別前提として残す。 | `proved` |
| `lspCompatible_of_staticSplitObservationFactorsThrough` | `theorem` | static split 文脈で、明示的な `ObservationFactorsThrough` 前提から `LSPCompatible` を得る接続補題。 | `proved` |
| `projectionSound_of_staticSplitProjectionExact` | `theorem` | static split の extended graph に対し、明示的な `ProjectionExact` 前提から `ProjectionSound` を得る bounded 補題。 | `proved` |
| `projectionSound_of_staticSplitEdgeDecomposition` | `theorem` | compatible static graph の edge が static split の extended graph に分解され、その extended graph が projection sound なら、compatible graph の `ProjectionSound` を得る。 | `proved` |
| `staticFlatWithin_of_staticSplitExtension` | `theorem` | coverage-aware な静的範囲で、static split extension と残りの静的 law 前提から `StaticFlatWithin` を得る。runtime / semantic flatness は結論しない。 | `proved` |
| `LawfulExtensionFlatnessModel` | `def` | static graph を `StaticSplitExtension` の extended graph に固定し、runtime / semantic evidence を明示引数として持つ bounded flatness model。 | `defined only` |
| `SplitFeatureExtensionWithinNonConclusions` | `def` | bounded split feature extension package が global `ArchitectureFlat`、extractor completeness、runtime / semantic completeness を自動導出しないことを記録する marker。 | `defined only` |
| `SplitFeatureExtensionWithin` | `structure` | `StaticSplitExtension`、extension coverage、static side conditions、runtime / semantic split evidence、non-conclusions を束ねる bounded public package。 | `defined only` |
| `splitFeatureExtensionWithin_of_runtimeSemanticSplitPreservation` | `def` | 既存の runtime / semantic split preservation evidence から `SplitFeatureExtensionWithin` を構成する入口。 | `defined only` |
| `splitFeatureExtensionWithin_recordsNonConclusions` | `theorem` | `SplitFeatureExtensionWithin` から記録済み non-conclusions を取り出す。 | `proved` |
| `LawfulExtensionPreservesFlatness` | `theorem` | extension coverage、runtime coverage / flatness、semantic coverage / flatness を明示前提として、lawful static split extension から bounded `ArchitectureFlatWithin` を構成する。 | `proved` |
| `LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation` | `theorem` | runtime / semantic split preservation package で `LawfulExtensionPreservesFlatness` の runtime / semantic flatness 前提を discharge する。 | `proved` |
| `architectureFlatWithin_of_splitFeatureExtensionWithin` | `theorem` | `SplitFeatureExtensionWithin` から induced flatness model の bounded `ArchitectureFlatWithin` を得る public preservation theorem。 | `proved` |

## Architecture Core / Certified Architecture

File: `Formal/Arch/CertifiedArchitecture.lean`

Issue [#287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/287)
の対象範囲は、数学設計書 9 の `ArchitectureCore` / `CertifiedArchitecture`
を既存の bounded flatness、finite `ComponentUniverse`、`ProofObligation`
API に接続する proof-carrying schema として固定することである。
実コード extractor の完全性、runtime telemetry の完全性、global semantic universe
completeness は主張しない。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `RuntimeDependencyRole` | `inductive` | runtime dependency を raw / protected / forbidden / unprotected の selected role metadata として区別する。telemetry completeness は主張しない。 | `defined only` |
| `ArchitectureCore` | `structure` | `ArchitectureFlatnessModel`、static `ComponentUniverse`、component equality / static edge / runtime edge / boundary policy / abstraction policy の decidability、runtime role、semantic required diagram decidability を束ねる最小 core。 | `defined only` |
| `ArchitectureCore.toFlatnessModel` | `def` | proof-carrying wrapper から既存の flatness model を取り出す。 | `defined only` |
| `ArchitectureCore.staticLawModel` | `def` | core の finite component universe から既存の `ArchitectureLawModel` を構成する。 | `defined only` |
| `ArchitectureCore.measuredSemanticUniverse` | `def` | core が保持する measured semantic diagram universe を取り出す。 | `defined only` |
| `ArchitectureCore.runtimeDependencyRole` | `def` | component pair に対する selected runtime dependency role を取り出す。 | `defined only` |
| `ArchitectureCore.component_mem_staticUniverse` | `theorem` | core の `ComponentUniverse.covers` から component membership を取り出す。 | `proved` |
| `ArchitectureCore.staticCoverageComplete` | `theorem` | core の static dependency evidence が `ComponentUniverse` で cover されることを取り出す。 | `proved` |
| `ArchitectureLawRole` | `inductive` | law universe の required / optional / derived role tag。 | `defined only` |
| `ArchitectureLawUniverse` | `structure` | finite law list と role assignment を束ねる。 | `defined only` |
| `ArchitectureLawUniverse.Required` | `def` | law が finite universe に含まれ、required role を持つこと。 | `defined only` |
| `ArchitectureLawUniverse.Optional` | `def` | law が finite universe に含まれ、optional role を持つこと。 | `defined only` |
| `ArchitectureLawUniverse.Derived` | `def` | law が finite universe に含まれ、derived role を持つこと。 | `defined only` |
| `ObstructionWitnessUniverse` | `structure` | bounded theorem package input としての finite obstruction witness universe。global obstruction enumeration は主張しない。 | `defined only` |
| `ArchitectureTheoremPackage` | `structure` | 名前付き theorem package、対応する `ProofObligation`、明示的な non-conclusion record を束ねる。 | `defined only` |
| `ClaimLevel` | `inductive` | architecture report claim を `formal` / `tooling` / `empirical` / `hypothesis` に分類する claim level。 | `defined only` |
| `ClaimLevel.IsFormal` | `def` | claim level が Lean theorem-package claim であること。 | `defined only` |
| `ClaimLevel.IsTooling` | `def` | claim level が tooling-side evidence claim であること。 | `defined only` |
| `ClaimLevel.IsEmpirical` | `def` | claim level が empirical validation claim であること。 | `defined only` |
| `ClaimLevel.IsHypothesis` | `def` | claim level が research hypothesis であること。 | `defined only` |
| `MeasurementBoundary` | `inductive` | report claim の測定境界を measured zero / measured nonzero / unmeasured / out of scope に分ける。 | `defined only` |
| `MeasurementBoundary.IsMeasuredZero` | `def` | boundary が明示的な measured zero であること。 | `defined only` |
| `MeasurementBoundary.IsUnmeasured` | `def` | boundary が unmeasured であること。 | `defined only` |
| `MeasurementBoundary.unmeasured_not_measuredZero` | `theorem` | unmeasured boundary は measured zero ではないこと。 | `proved` |
| `ArchitectureClaim` | `structure` | theorem package reference、tooling / empirical / hypothesis evidence、measurement boundary、non-conclusions を持つ claim schema。 | `defined only` |
| `ArchitectureClaim.RecordsNonConclusions` | `def` | architecture claim の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `ArchitectureClaim.IsFormal` | `def` | architecture claim が formal level であること。 | `defined only` |
| `ArchitectureClaim.HasFormalPackage` | `def` | architecture claim が theorem package reference を持つこと。 | `defined only` |
| `ArchitectureClaim.ToolingOnly` | `def` | architecture claim が tooling-only で theorem package を持たないこと。 | `defined only` |
| `ArchitectureClaim.IsMeasuredZero` | `def` | architecture claim の measurement boundary が measured zero であること。 | `defined only` |
| `ArchitectureClaim.IsUnmeasured` | `def` | architecture claim の measurement boundary が unmeasured であること。 | `defined only` |
| `ArchitectureClaim.records_nonConclusions_iff` | `theorem` | recorded non-conclusion predicate と claim field が一致すること。 | `proved` |
| `ArchitectureClaim.toolingOnly_no_formalPackage` | `theorem` | tooling-only claim は formal theorem package reference を持たないこと。 | `proved` |
| `ArchitectureClaim.unmeasured_not_measuredZero` | `theorem` | unmeasured claim boundary は measured-zero evidence ではないこと。 | `proved` |
| `CertifiedArchitecture` | `structure` | core、law universe、invariant family、witness universe、theorem package list、listed package の discharge proof を束ねる certified architecture object。 | `defined only` |
| `CertifiedArchitecture.theoremPackageObligations` | `def` | certified architecture が持つ theorem package から proof obligation list を取り出す。 | `defined only` |
| `CertifiedArchitecture.ProofObligationDischargeSet` | `def` | listed theorem package がすべて discharged であること。 | `defined only` |
| `CertifiedArchitecture.theoremPackage_discharged` | `theorem` | listed theorem package の discharge proof を取り出す accessor theorem。 | `proved` |
| `CertifiedArchitecture.proofObligationDischargeSet` | `theorem` | certified architecture が proof-obligation discharge set を持つことを示す。 | `proved` |
| `CertifiedArchitecture.theoremPackage_recordsNonConclusions` | `theorem` | listed theorem package が non-conclusions を記録していることを取り出す。 | `proved` |
| `CertifiedArchitecture.theoremPackage_obligation_mem` | `theorem` | listed theorem package の obligation が induced obligation list に含まれること。 | `proved` |

## Obstruction Kernel

File: `Formal/Arch/Obstruction.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `violatingWitnesses` | `def` | 有限な測定 witness list から、`bad` predicate を満たす阻害証人を取り出す。 | `defined only` |
| `violationCount` | `def` | `violatingWitnesses` の長さとして measured obstruction count を数える。 | `defined only` |
| `WitnessUniverseIncluded` | `def` | 一方の有限 measured witness universe が他方に含まれる set-like inclusion 条件。重複を同一視しないため count 単調性は別前提を要する。 | `defined only` |
| `MeasuredViolationExists` | `def` | 測定 universe 内に `bad` witness が存在すること。 | `defined only` |
| `NoMeasuredViolation` | `def` | 測定 universe 内に `bad` witness が存在しないこと。 | `defined only` |
| `mem_violatingWitnesses_iff` | `theorem` | `violatingWitnesses` の membership が、測定対象であり `bad` を満たすことと一致する。 | `proved` |
| `violationCount_eq_zero_iff_forall_not_bad` | `theorem` | `violationCount bad xs = 0` と、すべての測定 witness が `bad` でないことの同値。 | `proved` |
| `mem_violatingWitnesses_of_witnessUniverseIncluded` | `theorem` | measured universe inclusion 下で、small 側の violating witness membership が large 側へ保存される。 | `proved` |
| `measuredViolationExists_of_witnessUniverseIncluded` | `theorem` | measured universe inclusion 下で、witness existence が small から large へ保存される。 | `proved` |
| `noMeasuredViolation_of_witnessUniverseIncluded` | `theorem` | large 側に measured violation がなければ、included な small 側にも measured violation がない。 | `proved` |
| `violationCount_eq_zero_of_witnessUniverseIncluded` | `theorem` | large 側の measured violation count 0 が、included な small 側の count 0 を含意する。 | `proved` |
| `CoversWitnesses` | `def` | required witness がすべて measured list に含まれる一方向 coverage 条件。 | `defined only` |
| `RequiredByList` | `def` | 有限 list を、その list が列挙する required witness predicate として使う。 | `defined only` |
| `coversWitnesses_of_requiredByList_subset` | `theorem` | required list が measured list に含まれるなら、finite required universe の coverage が得られる。 | `proved` |
| `coversWitnesses_requiredByList_self` | `theorem` | finite required witness list は自分自身を cover する。 | `proved` |
| `RequiredDiagram` | `structure` | 左辺・右辺を持つ required equality diagram。 | `defined only` |
| `Semantics` | `structure` | diagram expression を観測値へ解釈する意味論。 | `defined only` |
| `DiagramCommutes` | `def` | required diagram の両辺の意味論が等しいこと。 | `defined only` |
| `DiagramBad` | `def` | required diagram が可換でないことを表す diagram obstruction witness。 | `defined only` |
| `diagramViolatingWitnesses` | `def` | 測定 diagram list から非可換な diagram obstruction witness を取り出す。 | `defined only` |
| `diagramViolationCount` | `def` | 測定 diagram obstruction witness 数。 | `defined only` |
| `CoversRequired` | `def` | required diagram がすべて measured list に含まれる complete coverage 条件。 | `defined only` |
| `RequiredDiagramsByList` | `def` | 有限 diagram list を、その list が列挙する required diagram predicate として使う。 | `defined only` |
| `coversRequired_of_requiredDiagramsByList_subset` | `theorem` | finite required diagram universe が measured list に含まれるなら `CoversRequired` が得られる。 | `proved` |
| `coversRequired_requiredDiagramsByList_self` | `theorem` | finite required diagram universe は自分自身を cover する。 | `proved` |
| `no_measured_DiagramBad_of_diagramViolationCount_eq_zero` | `theorem` | diagram violation count 0 から、測定 diagram obstruction witness が存在しないことを得る。 | `proved` |
| `diagramViolationCount_eq_zero_of_forall_measured_DiagramCommutes` | `theorem` | 測定 diagram がすべて可換なら diagram violation count は 0。 | `proved` |
| `diagramViolationCount_eq_zero_iff_forall_measured_DiagramCommutes` | `theorem` | `[DecidableEq Obs]` の下で、diagram violation count 0 と測定 diagram の可換性が同値。 | `proved` |
| `no_required_DiagramBad_of_coversRequired_and_diagramViolationCount_eq_zero` | `theorem` | complete coverage と diagram violation count 0 から、required diagram obstruction witness が存在しないことを得る。 | `proved` |
| `requiredDiagramCommutes_of_coversRequired_and_diagramViolationCount_eq_zero` | `theorem` | `[DecidableEq Obs]` の下で、complete coverage と diagram violation count 0 から required diagram の可換性を得る。 | `proved` |

## Numerical Curvature

File: `Formal/Arch/Curvature.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ZeroSeparatingDistance` | `structure` | 観測値上の `Nat` 値距離と、`distance x y = 0 ↔ x = y` の zero-separation law を束ねる。 | `defined only` |
| `numericalCurvature` | `def` | required diagram の両辺の観測意味論間の距離として数値 curvature を定義する。 | `defined only` |
| `NumericalCurvatureObstruction` | `def` | diagram の数値 curvature が非零であることを obstruction witness として表す。 | `defined only` |
| `NoNumericalCurvatureObstruction` | `def` | required diagram family に数値 curvature obstruction が存在しないこと。 | `defined only` |
| `totalCurvature` | `def` | 有限な測定済み diagram list 上で、各 diagram の数値 curvature を `Nat` 和として集約する。 | `defined only` |
| `NoMeasuredNumericalCurvatureObstruction` | `def` | 測定済み diagram list 内に数値 curvature obstruction が存在しないこと。未測定 diagram には主張しない。 | `defined only` |
| `PositiveCurvatureWeightOn` | `def` | 測定済み diagram list 上で各 diagram の重みが正であること。重み付き aggregate から各局所 curvature zero へ戻す bounded exactness 前提。 | `defined only` |
| `totalWeightedCurvature` | `def` | 有限な測定済み diagram list 上で、`weight d * numericalCurvature d` を合計する。calibration や empirical cost model は外部に残す。 | `defined only` |
| `numericalCurvature_eq_zero_iff_DiagramCommutes` | `theorem` | zero-separating distance の下で、数値 curvature 0 と diagram commutativity が一致する。 | `proved` |
| `numericalCurvature_eq_zero_of_DiagramCommutes` | `theorem` | 可換な diagram は数値 curvature が 0 である。 | `proved` |
| `DiagramCommutes_of_numericalCurvature_eq_zero` | `theorem` | 数値 curvature 0 から diagram commutativity を得る。 | `proved` |
| `numericalCurvatureObstruction_iff_DiagramBad` | `theorem` | 数値 curvature obstruction と既存の `DiagramBad` predicate が一致する。 | `proved` |
| `not_numericalCurvatureObstruction_iff_DiagramCommutes` | `theorem` | 個別 diagram で、数値 curvature obstruction 不在と可換性が一致する。 | `proved` |
| `diagramLawful_iff_noNumericalCurvatureObstruction` | `theorem` | required diagram family の lawfulness と数値 curvature obstruction 不在を接続する。 | `proved` |
| `totalCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero` | `theorem` | 有限測定 universe 上で、合計 curvature 0 と各 measured diagram の curvature 0 が一致する。 | `proved` |
| `totalCurvature_eq_zero_iff_forall_measured_DiagramCommutes` | `theorem` | 有限測定 universe 上で、合計 curvature 0 と各 measured diagram の可換性が一致する。 | `proved` |
| `totalCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction` | `theorem` | 有限測定 universe 上で、合計 curvature 0 と measured numerical curvature obstruction 不在が一致する。 | `proved` |
| `totalWeightedCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero` | `theorem` | 測定済み diagram が正の重みを持つ場合、重み付き合計 curvature 0 と各 measured diagram の curvature 0 が一致する。 | `proved` |
| `totalWeightedCurvature_eq_zero_iff_forall_measured_DiagramCommutes` | `theorem` | 正の重み付き有限測定 universe 上で、重み付き合計 curvature 0 と各 measured diagram の可換性が一致する。 | `proved` |
| `totalWeightedCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction` | `theorem` | 正の重み付き有限測定 universe 上で、重み付き合計 curvature 0 と measured numerical curvature obstruction 不在が一致する。未測定 diagram や empirical cost correlation は主張しない。 | `proved` |

## Lawfulness Bridge

File: `Formal/Arch/Lawfulness.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `LawFamily` | `structure` | 独立した `lawful` predicate、測定 witness list、required witness predicate、bad witness predicate、required axis predicate を束ねる抽象法則族。 | `defined only` |
| `AxisSignature` | `abbrev` | 抽象 axis から `Option Nat` metric への signature valuation。 | `defined only` |
| `MeasuredZero` | `def` | `Option Nat` metric に測定済み非零値がないこと。`none` を許す弱い零性。 | `defined only` |
| `AvailableAndZero` | `def` | `Option Nat` metric が `some 0` として測定済みであること。`none` は許さない強い零性。 | `defined only` |
| `AxisMeasuredZero` | `def` | signature valuation の指定 axis が weak measured-zero であること。 | `defined only` |
| `AxisAvailableAndZero` | `def` | signature valuation の指定 axis が available-and-zero であること。 | `defined only` |
| `measuredZero_none` | `theorem` | 未測定 `none` は weak measured-zero を満たす。 | `proved` |
| `not_availableAndZero_none` | `theorem` | 未測定 `none` は available-and-zero を満たさない。 | `proved` |
| `measuredZero_of_availableAndZero` | `theorem` | available-and-zero なら weak measured-zero。 | `proved` |
| `measuredZero_some_iff` | `theorem` | `some n` の weak measured-zero は `n = 0` と同値。 | `proved` |
| `availableAndZero_some_iff` | `theorem` | `some n` の available-and-zero は `n = 0` と同値。 | `proved` |
| `Lawful` | `def` | 法則族側で与えられた独立 predicate としての lawfulness。 | `defined only` |
| `NoRequiredObstruction` | `def` | required witness 全体に bad witness が存在しないこと。 | `defined only` |
| `NoMeasuredObstruction` | `def` | measured witness list に bad witness が存在しないこと。 | `defined only` |
| `RequiredWitnessCoverage` | `def` | 法則族の measured witness list がすべての required witness を含むこと。 | `defined only` |
| `CompleteWitnessCoverage` | `def` | measured witness list が required witness universe と一致する完全被覆条件。 | `defined only` |
| `lawViolationCount` | `def` | generic `violationCount` を使う law-family obstruction count。 | `defined only` |
| `lawful_iff_noMeasuredObstruction` | `theorem` | 法則族が持つ bridge により、独立 lawfulness と measured obstruction 不在を接続する。 | `proved` |
| `lawViolationCount_eq_zero_iff_lawful` | `theorem` | measured violation count 0 と独立 lawfulness の同値。 | `proved` |
| `requiredWitnessCoverage_of_completeWitnessCoverage` | `theorem` | 完全被覆から required-witness coverage を得る。 | `proved` |
| `noRequiredObstruction_of_completeCoverage_and_noMeasuredObstruction` | `theorem` | 完全被覆下で measured obstruction 不在から required obstruction 不在を得る。 | `proved` |
| `noRequiredObstruction_of_requiredWitnessCoverage_and_noMeasuredObstruction` | `theorem` | required-witness coverage 下で measured obstruction 不在から required obstruction 不在を得る。 | `proved` |
| `noRequiredObstruction_of_requiredWitnessCoverage_and_lawViolationCount_eq_zero` | `theorem` | required-witness coverage 下で measured violation count 0 から required obstruction 不在を得る。 | `proved` |
| `noMeasuredObstruction_of_completeCoverage_and_noRequiredObstruction` | `theorem` | 完全被覆下で required obstruction 不在から measured obstruction 不在を得る。 | `proved` |
| `lawful_iff_noRequiredObstruction_of_completeCoverage` | `theorem` | 完全被覆下で独立 lawfulness と required obstruction 不在を接続する中心 bridge。 | `proved` |
| `lawViolationCount_eq_zero_iff_noRequiredObstruction_of_completeCoverage` | `theorem` | 完全被覆下で measured violation count 0 と required obstruction 不在を接続する。 | `proved` |
| `RequiredAxesAvailableAndZero` | `def` | 法則族の required axis がすべて available and zero であること。 | `defined only` |
| `AxisExact` | `def` | 1 つの axis の available-and-zero と、その axis が表す witness subfamily の bad witness 不在が同値であること。 | `defined only` |
| `AxisCoversOnlyRequired` | `def` | axis が表す witness subfamily が required witness だけを含むこと。 | `defined only` |
| `RequiredWitnessCoveredByAxis` | `def` | required witness が少なくとも 1 つの required axis によって表されること。 | `defined only` |
| `RequiredAxisFamilyExact` | `def` | required axis ごとの `AxisExact` がそろっていること。 | `defined only` |
| `RequiredAxisExact` | `def` | required axis の available-and-zero と required obstruction 不在が同値であること。 | `defined only` |
| `requiredAxesAvailableAndZero_iff_noRequiredObstruction_of_requiredAxisExact` | `theorem` | required axis exactness から signature axis と obstruction 不在の bridge を取り出す。 | `proved` |
| `requiredAxesAvailableAndZero_iff_noRequiredObstruction_of_axisExactFamily` | `theorem` | axis ごとの exactness と required witness cover から、required axis 全体の available-and-zero と required obstruction 不在を接続する。 | `proved` |
| `requiredAxisExact_of_axisExactFamily` | `theorem` | axis ごとの exactness を既存の whole-family exactness predicate にパッケージする。 | `proved` |
| `lawful_iff_requiredAxesAvailableAndZero_of_completeCoverage_and_requiredAxisExact` | `theorem` | 完全被覆と required axis exactness の下で、lawfulness と required axis zero を接続する零曲率定理の structural core。 | `proved` |

## Signature-Integrated Lawfulness

File: `Formal/Arch/SignatureLawfulness.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureSignature.PolicyViolation` | `def` | boundary / abstraction policy に反する依存 pair。 | `defined only` |
| `ArchitectureSignature.PolicySound` | `def` | graph edge が指定 policy をすべて満たすこと。 | `defined only` |
| `ArchitectureSignature.BoundaryPolicySound` | `def` | boundary policy が graph edge をすべて許可すること。 | `defined only` |
| `ArchitectureSignature.AbstractionPolicySound` | `def` | abstraction policy が graph edge をすべて許可すること。 | `defined only` |
| `ArchitectureSignature.BoundaryPolicyObstruction` | `def` | boundary policy に反する dependency pair witness。 | `defined only` |
| `ArchitectureSignature.AbstractionPolicyObstruction` | `def` | abstraction policy に反する dependency pair witness。 | `defined only` |
| `ArchitectureSignature.boundaryPolicySound_iff_no_boundaryPolicyObstruction` | `theorem` | boundary policy soundness と boundary obstruction witness 不在を接続する。 | `proved` |
| `ArchitectureSignature.abstractionPolicySound_iff_no_abstractionPolicyObstruction` | `theorem` | abstraction policy soundness と abstraction obstruction witness 不在を接続する。 | `proved` |
| `ArchitectureSignature.ArchitectureRequiredLawWitness` | `inductive` | selected required Signature axes に対応する concrete witness family。 | `defined only` |
| `ArchitectureSignature.ArchitectureWitness` | `abbrev` | selected required Signature axes に対応する concrete witness family の短い公開名。 | `defined only` |
| `ArchitectureSignature.ArchitectureLawModel` | `structure` | graph, projection, observation, finite universe, policy, LSP pair coverage を束ねる Signature-integrated law model。 | `defined only` |
| `ArchitectureSignature.ArchitectureLawModel.signatureOf` | `def` | selected required law axes を concrete count で埋めた `ArchitectureSignatureV1`。 | `defined only` |
| `ArchitectureSignature.architectureBad` | `def` | concrete architecture witness が阻害 witness であること。 | `defined only` |
| `ArchitectureSignature.architectureMeasuredWitnesses` | `def` | concrete law family で測定する selected witness universe。 | `defined only` |
| `ArchitectureSignature.architectureRequiredWitness` | `def` | current concrete law family で required とみなす witness predicate。 | `defined only` |
| `ArchitectureSignature.architectureRequiredAxis` | `def` | current concrete law family で required とみなす Signature axis predicate。 | `defined only` |
| `ArchitectureSignature.ArchitectureLawCandidateRole` | `inductive` | full law universe 候補を required law / derived corollary / diagnostic axis / empirical axis に分類する role。 | `defined only` |
| `ArchitectureSignature.ArchitectureLawUniverseCandidate` | `inductive` | current required laws、LocalReplacement、state-effect laws、matrix / runtime diagnostics、empirical axes を含む候補 universe。 | `defined only` |
| `ArchitectureSignature.architectureFullLawUniverseCandidates` | `def` | #222 で固定した full law universe 候補の有限 list。 | `defined only` |
| `ArchitectureSignature.architectureLawCandidateRole` | `def` | full law universe 候補ごとの required / corollary / diagnostic / empirical 分類。 | `defined only` |
| `ArchitectureSignature.architectureLawCandidateRole_requiredLaw_iff` | `theorem` | required law 候補が current final theorem の 5 条件に限られることを展開する。 | `proved` |
| `ArchitectureSignature.architectureLawCandidateRole_nonrequired_examples` | `theorem` | LocalReplacement / state-effect / nilpotency / spectral / runtime / empirical 候補が required law ではないことを確認する分類補題。 | `proved` |
| `ArchitectureSignature.ArchitectureLawful` | `def` | `WalkAcyclic`, `ProjectionSound`, `LSPCompatible`, boundary policy soundness, abstraction policy soundness の統合 lawfulness。 | `defined only` |
| `ArchitectureSignature.RequiredSignatureAxesAvailableAndZero` | `def` | selected required Signature axes がすべて `some 0` であること。 | `defined only` |
| `ArchitectureSignature.RequiredSignatureAxesZero` | `def` | selected required Signature axes がすべて available-and-zero であることの短い公開名。 | `defined only` |
| `ArchitectureSignature.hasCycle_axisExact` | `theorem` | `v1OfFiniteWithRequiredLawAxes` の hasCycle axis available-and-zero と `WalkAcyclic` を、finite universe coverage の下で接続する。 | `proved` |
| `ArchitectureSignature.hasCycle_axisExact_no_closedWalkObstruction` | `theorem` | hasCycle axis available-and-zero と closed-walk obstruction witness 不在を接続する。 | `proved` |
| `ArchitectureSignature.projectionSoundnessViolation_axisExact` | `theorem` | `v1OfFiniteWithRequiredLawAxes` の projection axis available-and-zero と `NoProjectionObstruction` を、finite edge coverage の下で接続する。 | `proved` |
| `ArchitectureSignature.lspViolationCount_axisExact` | `theorem` | `v1OfFiniteWithRequiredLawAxes` の LSP axis available-and-zero と `NoLSPObstruction` を、same-abstraction pair coverage の下で接続する。 | `proved` |
| `ArchitectureSignature.boundaryViolationCountOfFinite_eq_zero_iff_no_boundaryPolicyObstruction` | `theorem` | boundary violation count が 0 であることと boundary obstruction witness 不在を接続する。 | `proved` |
| `ArchitectureSignature.abstractionViolationCountOfFinite_eq_zero_iff_no_abstractionPolicyObstruction` | `theorem` | abstraction violation count が 0 であることと abstraction obstruction witness 不在を接続する。 | `proved` |
| `ArchitectureSignature.boundaryViolation_axisExact` | `theorem` | `v1OfFiniteWithRequiredLawAxes` の boundary axis available-and-zero と `BoundaryPolicySound` を、finite edge coverage の下で接続する。 | `proved` |
| `ArchitectureSignature.abstractionViolation_axisExact` | `theorem` | `v1OfFiniteWithRequiredLawAxes` の abstraction axis available-and-zero と `AbstractionPolicySound` を、finite edge coverage の下で接続する。 | `proved` |
| `ArchitectureSignature.witnessForAxis` | `def` | each required Signature axis が表す concrete witness subfamily。 | `defined only` |
| `ArchitectureSignature.architectureLawful_iff_no_measured_bad` | `theorem` | `ArchitectureLawful X` と measured concrete bad witness 不在を接続する。 | `proved` |
| `ArchitectureSignature.architectureLawFamily` | `def` | selected required Signature axes 用の concrete `LawFamily`。 | `defined only` |
| `ArchitectureSignature.architectureLawFamily_completeCoverage` | `theorem` | concrete law family の measured witness list が required witness universe と一致する。 | `proved` |
| `ArchitectureSignature.architecture_requiredAxisFamilyExact` | `theorem` | selected required axes ごとに concrete `axisValue` と obstruction witness 不在が同値であること。 | `proved` |
| `ArchitectureSignature.architecture_requiredAxisExact` | `theorem` | concrete law family で required axis 全体の available-and-zero と required obstruction 不在を接続する。 | `proved` |
| `ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesAvailableAndZero` | `theorem` | selected required Signature axes について、`ArchitectureLawful X` と `RequiredSignatureAxesAvailableAndZero (signatureOf X)` を接続する static structural core の QED の中核 theorem。 | `proved` |
| `ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero` | `theorem` | selected required Signature axes について、`ArchitectureLawful X` と `RequiredSignatureAxesZero (signatureOf X)` を接続する static structural core の QED の中核 theorem。 | `proved` |
| `ArchitectureSignature.MatrixDiagnosticCorollaries` | `def` | selected required laws から導かれる matrix diagnostics を束ねる derived corollary package。adjacency nilpotence、`nilpotencyIndexOfFinite = some k`、`spectralRadiusOfAdjacency = 0` を含む。 | `defined only` |
| `ArchitectureSignature.matrixDiagnosticCorollaries_of_architectureLawful` | `theorem` | `ArchitectureLawful X` から matrix diagnostic corollaries を得る。`nilpotencyIndex` と `spectralRadius` を required zero-axis にはしない。 | `proved` |
| `ArchitectureSignature.matrixDiagnosticCorollaries_of_requiredSignatureAxesZero` | `theorem` | `RequiredSignatureAxesZero (signatureOf X)` から matrix diagnostic corollaries を得る #224 bridge。 | `proved` |
| `ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage` | `def` | current law-universe policy で static structural core の QED と読む theorem package。selected required axes zero と matrix diagnostic corollaries を束ね、runtime / empirical / numerical curvature は含めない。 | `defined only` |
| `ArchitectureSignature.architectureZeroCurvatureTheoremPackage_of_architectureLawful` | `theorem` | `ArchitectureLawful X` から static structural core の QED package を得る。 | `proved` |
| `ArchitectureSignature.architectureLawful_of_architectureZeroCurvatureTheoremPackage` | `theorem` | theorem package から selected required `ArchitectureLawful X` を戻す。 | `proved` |
| `ArchitectureSignature.architectureLawful_iff_architectureZeroCurvatureTheoremPackage` | `theorem` | current law-universe policy で、`ArchitectureLawful X` と static structural core の QED package が同値であることを示す #226 packaging theorem。 | `proved` |
| `ArchitectureSignature.localReplacementContract_requiredSignatureProjectionLSPAxes` | `theorem` | `LocalReplacementContract` から selected required Signature axes の projection / LSP が available-and-zero であることを得る derived corollary bridge。 | `proved` |
| `ArchitectureSignature.architectureLawful_of_localReplacementContract` | `theorem` | closed-walk acyclicity、`LocalReplacementContract`、boundary / abstraction policy soundness から `ArchitectureLawful X` を得る。 | `proved` |
| `ArchitectureSignature.requiredSignatureAxesZero_of_localReplacementContract` | `theorem` | closed-walk acyclicity、`LocalReplacementContract`、boundary / abstraction policy soundness から `RequiredSignatureAxesZero (signatureOf X)` を得る derived zero-curvature bridge。 | `proved` |
| `ArchitectureSignature.architectureZeroCurvatureTheoremPackage_of_localReplacementContract` | `theorem` | LocalReplacement と残りの static laws から static structural core の QED package を得る derived bridge。 | `proved` |

### 零曲率 theorem package の読み順

1. `architectureLawCandidateRole_requiredLaw_iff` で required law が 5 条件に限られることを確認する。
2. `architectureLawful_iff_requiredSignatureAxesZero` を static structural core の QED の主 theorem として読む。
3. LocalReplacement / state-effect laws は `localReplacementContract_requiredSignatureProjectionLSPAxes`, `requiredSignatureAxesZero_of_localReplacementContract`, `stateTransitionLawFamilyLawful_iff_noStateTransitionLawFamilyObstruction`, `effectBoundaryLawFamilyLawful_iff_noEffectBoundaryLawFamilyObstruction` で derived corollary として読む。
4. nilpotency / spectral diagnostics は `MatrixDiagnosticCorollaries` と `matrixDiagnosticCorollaries_of_requiredSignatureAxesZero` で読む。
5. package は `architectureLawful_iff_architectureZeroCurvatureTheoremPackage` を入口にし、static structural core の QED として読む。runtime / empirical axis はこの package に含めず、numerical curvature は別の bounded diagram bridge として読む。

## State Transition / Effect Boundary Laws

Files: `Formal/Arch/StateEffect.lean`, `Formal/Arch/StateTransitionDesignPattern.lean`, `Formal/Arch/EventSourcingSagaDesignPattern.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `StateTransitionExpr` | `inductive` | 状態、履歴、replay、roundtrip、compensation を区別する状態遷移 diagram 用 expression。 | `defined only` |
| `EffectBoundaryExpr` | `inductive` | effect、boundary 通過、trace、replay、roundtrip、compensation を区別する effect-boundary diagram 用 expression。 | `defined only` |
| `DiagramLawful` | `def` | required diagram predicate のすべてが可換であること。 | `defined only` |
| `NoDiagramObstruction` | `def` | required diagram predicate に diagram obstruction witness が存在しないこと。 | `defined only` |
| `diagramLawful_iff_noDiagramObstruction` | `theorem` | diagram lawfulness と required diagram obstruction witness 不在を接続する。 | `proved` |
| `DiagramLawfulByList` | `def` | finite required diagram list に対する diagram lawfulness。 | `defined only` |
| `NoDiagramObstructionByList` | `def` | finite required diagram list に対する obstruction witness 不在。 | `defined only` |
| `diagramLawfulByList_iff_noDiagramObstructionByList` | `theorem` | finite required diagram list で lawfulness と obstruction witness 不在を接続する。 | `proved` |
| `StateReplayCase` | `structure` | 状態遷移 replay law の finite case。 | `defined only` |
| `StateRoundtripCase` | `structure` | 状態遷移 roundtrip law の finite case。 | `defined only` |
| `StateCompensationCase` | `structure` | 状態遷移 compensation law の finite case。 | `defined only` |
| `stateReplayDiagram` | `def` | 状態遷移 replay case を required diagram に写す。 | `defined only` |
| `stateRoundtripDiagram` | `def` | 状態遷移 roundtrip case を required diagram に写す。 | `defined only` |
| `stateCompensationDiagram` | `def` | 状態遷移 compensation case を required diagram に写す。 | `defined only` |
| `stateReplayLawful_iff_noStateReplayObstruction` | `theorem` | 状態遷移 replay lawfulness と obstruction witness 不在の同値。 | `proved` |
| `stateRoundtripLawful_iff_noStateRoundtripObstruction` | `theorem` | 状態遷移 roundtrip lawfulness と obstruction witness 不在の同値。 | `proved` |
| `stateCompensationLawful_iff_noStateCompensationObstruction` | `theorem` | 状態遷移 compensation lawfulness と obstruction witness 不在の同値。 | `proved` |
| `EffectReplayCase` | `structure` | effect-boundary replay law の finite case。 | `defined only` |
| `EffectRoundtripCase` | `structure` | effect-boundary roundtrip law の finite case。 | `defined only` |
| `EffectCompensationCase` | `structure` | effect-boundary compensation law の finite case。 | `defined only` |
| `effectReplayDiagram` | `def` | effect-boundary replay case を required diagram に写す。 | `defined only` |
| `effectRoundtripDiagram` | `def` | effect-boundary roundtrip case を required diagram に写す。 | `defined only` |
| `effectCompensationDiagram` | `def` | effect-boundary compensation case を required diagram に写す。 | `defined only` |
| `effectReplayLawful_iff_noEffectReplayObstruction` | `theorem` | effect-boundary replay lawfulness と obstruction witness 不在の同値。 | `proved` |
| `effectRoundtripLawful_iff_noEffectRoundtripObstruction` | `theorem` | effect-boundary roundtrip lawfulness と obstruction witness 不在の同値。 | `proved` |
| `effectCompensationLawful_iff_noEffectCompensationObstruction` | `theorem` | effect-boundary compensation lawfulness と obstruction witness 不在の同値。 | `proved` |
| `StateTransitionLawFamilyLawful` | `def` | 状態遷移 replay / roundtrip / compensation law family の aggregate lawfulness。 | `defined only` |
| `NoStateTransitionLawFamilyObstruction` | `def` | 状態遷移 replay / roundtrip / compensation law family の aggregate obstruction absence。 | `defined only` |
| `stateTransitionLawFamilyLawful_iff_noStateTransitionLawFamilyObstruction` | `theorem` | 状態遷移 law family package の lawfulness と obstruction absence を接続する。 | `proved` |
| `StateTransitionCarrier` | `structure` | 状態、遷移、観測、replay / projection、compensation、`StateTransitionExpr` semantics を束ねる状態遷移代数層の最小 carrier。 | `defined only` |
| `StateTransitionPatternState` | `structure` | carrier と selected finite replay / roundtrip / compensation law cases を同じ state として束ねる。 | `defined only` |
| `StateTransitionOperation` | `structure` | source / target state と target 側の aggregate lawfulness を持つ proof-carrying operation。 | `defined only` |
| `StateTransitionInvariant` | `inductive` | replay、roundtrip、compensation、aggregate lawfulness を selected invariant axis として列挙する。 | `defined only` |
| `stateTransitionDesignPattern` | `def` | 状態遷移代数層を `DesignPattern` schema に接続する入口。 | `defined only` |
| `stateTransitionDesignPattern_closure_law` | `theorem` | 状態遷移代数層 `DesignPattern` から operation-to-invariant / invariant-to-operation closure law を取り出す。 | `proved` |
| `stateTransitionDesignPattern_records_nonConclusion` | `theorem` | extractor completeness、event log completeness、運用コスト改善、CRUD 一般 theorem 化を non-conclusion として記録する。 | `proved` |
| `EventSequenceMonoidLawful` | `def` | Event Sourcing の event sequence を finite list monoid として読む selected law predicate。 | `defined only` |
| `eventSequenceMonoidLawful` | `theorem` | finite event sequence の empty / append / associativity law を証明する。 | `proved` |
| `StateProjectionCase` | `structure` | Event Sourcing projection law の finite selected case。 | `defined only` |
| `StateProjectionLawful` | `def` | carrier の projection が同じ event sequence の replay observation と一致する selected law。 | `defined only` |
| `EventSourcingPatternState` | `structure` | carrier、selected replay cases、selected projection cases を束ねる Event Sourcing state。 | `defined only` |
| `EventSourcingOperation` | `structure` | source / target state と target 側 replay / projection lawfulness を持つ proof-carrying operation。 | `defined only` |
| `eventSourcingOperation_toStateTransitionOperation` | `def` | Event Sourcing operation を汎用 `StateTransitionOperation` として読む bridge。 | `defined only` |
| `eventSourcingOperation_stateTransitionClosure` | `theorem` | Event Sourcing operation を汎用状態遷移 closure law に接続する。 | `proved` |
| `EventSourcingInvariant` | `inductive` | event sequence monoid、replay law、projection law、aggregate lawfulness を selected invariant axis として列挙する。 | `defined only` |
| `eventSourcingDesignPattern` | `def` | Event Sourcing を `DesignPattern` schema に接続する theorem package。 | `defined only` |
| `eventSourcingDesignPattern_closure_law` | `theorem` | Event Sourcing `DesignPattern` から operation-to-invariant / invariant-to-operation closure law を取り出す。 | `proved` |
| `eventSourcingDesignPattern_records_nonConclusion` | `theorem` | extractor completeness、event log completeness、projection completeness、運用コスト改善を non-conclusion として記録する。 | `proved` |
| `SagaPatternState` | `structure` | carrier と selected compensation cases を束ねる Saga state。 | `defined only` |
| `SagaWeakRecoveryLawful` | `def` | Saga compensation を selected weak recovery law として読む predicate。 | `defined only` |
| `SagaOperation` | `structure` | source / target state と target 側 weak recovery lawfulness を持つ proof-carrying operation。 | `defined only` |
| `sagaOperation_toStateTransitionOperation` | `def` | Saga operation を汎用 `StateTransitionOperation` として読む bridge。 | `defined only` |
| `sagaOperation_stateTransitionClosure` | `theorem` | Saga operation を汎用状態遷移 closure law に接続する。 | `proved` |
| `SagaInvariant` | `inductive` | compensation weak recovery と aggregate lawfulness を selected invariant axis として列挙する。 | `defined only` |
| `sagaDesignPattern` | `def` | Saga を `DesignPattern` schema に接続する theorem package。 | `defined only` |
| `sagaDesignPattern_closure_law` | `theorem` | Saga `DesignPattern` から operation-to-invariant / invariant-to-operation closure law を取り出す。 | `proved` |
| `sagaDesignPattern_records_nonConclusion` | `theorem` | 補償の一般逆射性、全 failure mode coverage、運用回復コスト改善、extractor completeness を non-conclusion として記録する。 | `proved` |
| `EffectBoundaryLawFamilyLawful` | `def` | effect-boundary replay / roundtrip / compensation law family の aggregate lawfulness。 | `defined only` |
| `NoEffectBoundaryLawFamilyObstruction` | `def` | effect-boundary replay / roundtrip / compensation law family の aggregate obstruction absence。 | `defined only` |
| `effectBoundaryLawFamilyLawful_iff_noEffectBoundaryLawFamilyObstruction` | `theorem` | effect-boundary law family package の lawfulness と obstruction absence を接続する。 | `proved` |

## Signature v0

File: `Formal/Arch/Signature.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureSignature` | `structure` | v0 の多軸リスク signature。 | `defined only` |
| `ArchitectureSignature.RiskLE` | `def` | componentwise risk order。 | `defined only` |
| `ArchitectureSignature.riskLE_refl` | `theorem` | risk order の反射性。 | `proved` |
| `ArchitectureSignature.riskLE_trans` | `theorem` | risk order の推移性。 | `proved` |
| `ArchitectureSignature.riskLE_antisymm` | `theorem` | risk order の反対称性。 | `proved` |
| `ArchitectureSignature.boolRisk` | `def` | `Bool` を 0/1 risk convention へ写す補助関数。 | `defined only` |
| `ArchitectureSignature.boolRisk_eq_zero_iff` | `theorem` | `boolRisk b = 0` と `b = false` が同値であること。 | `proved` |
| `ArchitectureSignature.maxNatList` | `def` | finite metric list の最大値を取る補助関数。 | `defined only` |
| `ArchitectureSignature.countWhere` | `def` | Boolean predicate を満たす list 要素数を数える補助関数。 | `defined only` |
| `ArchitectureSignature.componentPairs` | `def` | finite component list 上の ordered pair 測定 universe。 | `defined only` |
| `ArchitectureSignature.mem_componentPairs_iff` | `theorem` | `componentPairs` の membership が両 endpoint の finite list membership と一致する。 | `proved` |
| `ArchitectureSignature.reachesWithin` | `def` | fuel-bounded reachability。 | `defined only` |
| `ArchitectureSignature.hasCycleBool` | `def` | executable cycle indicator。 | `defined only` |
| `ArchitectureSignature.sccSizeAt` | `def` | component 周辺の相互到達 class size。 | `defined only` |
| `ArchitectureSignature.sccMaxSizeOfFinite` | `def` | finite universe 上の最大 SCC サイズ。 | `defined only` |
| `ArchitectureSignature.fanout` | `def` | component ごとの outgoing dependency count。 | `defined only` |
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
| `ArchitectureSignature.averageFanoutOfFinite` | `def` | legacy coarse Nat-valued average fanout。Signature v0 では使わない派生 metric。 | `defined only` |
| `ArchitectureSignature.boundedDepthFrom` | `def` | component ごとの fuel-bounded dependency-chain depth。 | `defined only` |
| `ArchitectureSignature.maxDepthOfFinite` | `def` | finite universe 上の bounded max depth。 | `defined only` |
| `ArchitectureSignature.boundaryViolationCountOfFinite` | `def` | supplied boundary policy に反する測定依存辺数。 | `defined only` |
| `ArchitectureSignature.abstractionViolationCountOfFinite` | `def` | supplied abstraction policy に反する測定依存辺数。 | `defined only` |
| `ArchitectureSignature.v0OfFinite` | `def` | finite universe から v0 signature を計算する。 | `defined only` |
| `ArchitectureSignature.ArchitectureSignatureV1Core` | `structure` | v0 signature と Lean-measured v1 core axis を束ねる schema。 | `defined only` |
| `ArchitectureSignature.ArchitectureSignatureV1` | `structure` | v1 core と optional extension axis を束ねる output schema。 | `defined only` |
| `ArchitectureSignature.AxisMeasurementClass` | `inductive` | Signature v1 axis を `proved witness axis` / `defined executable axis` / `empirical axis` / `unmeasured required law` に分類する。 | `defined only` |
| `ArchitectureSignature.ArchitectureSignatureV1Axis` | `inductive` | Signature v1 schema が公開する named axis。 | `defined only` |
| `ArchitectureSignature.selectedRequiredLawAxes` | `def` | Signature-integrated lawfulness bridge の初期 required zero law axes を列挙する。 | `defined only` |
| `ArchitectureSignature.IsSelectedRequiredLawAxis` | `def` | `selectedRequiredLawAxes` の predicate 版。 | `defined only` |
| `ArchitectureSignature.mem_selectedRequiredLawAxes_iff` | `theorem` | selected required axis が `hasCycle`, projection, LSP, boundary, abstraction のいずれかであることを展開する。 | `proved` |
| `ArchitectureSignature.ArchitectureSignatureV1.axisValue` | `def` | Signature v1 の任意 axis を `Option Nat` metric として読む。 | `defined only` |
| `ArchitectureSignature.ArchitectureSignatureV1.axisMeasurementClass` | `def` | Signature v1 axis の現在の Lean/proof/empirical status 分類。 | `defined only` |
| `ArchitectureSignature.ArchitectureSignatureV1.axisMeasuredZero` | `def` | Signature v1 axis value の weak measured-zero predicate。 | `defined only` |
| `ArchitectureSignature.ArchitectureSignatureV1.axisAvailableAndZero` | `def` | Signature v1 axis value の strong available-and-zero predicate。 | `defined only` |
| `ArchitectureSignature.ArchitectureSignatureV1.axisMeasuredZero_of_axisValue_none` | `theorem` | `axisValue = none` の axis は weak measured-zero。 | `proved` |
| `ArchitectureSignature.ArchitectureSignatureV1.not_axisAvailableAndZero_of_axisValue_none` | `theorem` | `axisValue = none` の axis は available-and-zero ではない。 | `proved` |
| `ArchitectureSignature.ArchitectureSignatureV1.axisAvailableAndZero_some_iff` | `theorem` | `axisValue = some n` の axis available-and-zero は `n = 0` と同値。 | `proved` |
| `ArchitectureSignature.v1CoreOfFinite` | `def` | finite universe から v1 core signature を計算する。 | `defined only` |
| `ArchitectureSignature.v1OfFinite` | `def` | finite universe から v1 schema を作り、未評価 extension axis を `none` にする。 | `defined only` |
| `ArchitectureSignature.v1OfFiniteWithRequiredLawAxes` | `def` | selected required law axes のうち projection / LSP / policy count を `some count` として埋める v1 entry point。 | `defined only` |
| `ArchitectureSignature.axisValue_v1OfFiniteWithRequiredLawAxes_hasCycle` | `theorem` | required-axis entry point の `hasCycle` axis 計算補題。 | `proved` |
| `ArchitectureSignature.axisValue_v1OfFiniteWithRequiredLawAxes_projectionSoundnessViolation` | `theorem` | required-axis entry point の projection soundness axis 計算補題。 | `proved` |
| `ArchitectureSignature.axisValue_v1OfFiniteWithRequiredLawAxes_lspViolationCount` | `theorem` | required-axis entry point の LSP violation axis 計算補題。 | `proved` |
| `ArchitectureSignature.axisValue_v1OfFiniteWithRequiredLawAxes_boundaryViolationCount` | `theorem` | required-axis entry point の boundary policy axis 計算補題。 | `proved` |
| `ArchitectureSignature.axisValue_v1OfFiniteWithRequiredLawAxes_abstractionViolationCount` | `theorem` | required-axis entry point の abstraction policy axis 計算補題。 | `proved` |
| `ArchitectureSignature.v1OfFiniteWithWeightedSccRisk` | `def` | 明示的な component weight から `weightedSccRisk` を埋めた v1 schema を作る。 | `defined only` |
| `ArchitectureSignature.runtimePropagationOfFinite` | `def` | 0/1 runtime graph 上の reachable cone size を exposure 側の `runtimePropagation` 最小 metric として計算する。 | `defined only` |
| `ArchitectureSignature.NoRuntimeExposureObstruction` | `def` | `reachesWithin runtime components components.length` ベースで、測定 universe 内の distinct runtime reachable cone が空であることを表す。 | `defined only` |
| `ArchitectureSignature.NoSemanticRuntimeExposureObstruction` | `def` | `Reachable runtime source target` ベースで、測定 universe 内の distinct runtime reachable cone が空であることを表す。 | `defined only` |
| `ArchitectureSignature.runtimePropagationOfFinite_eq_zero_iff_noRuntimeExposureObstruction` | `theorem` | runtime exposure radius が 0 であることと measured / bounded runtime exposure obstruction がないことの同値。 | `proved` |
| `ArchitectureSignature.v1OfFiniteWithRuntimePropagation` | `def` | 静的 graph から v1 core を計算し、runtime graph から exposure 側の `runtimePropagation` axis を埋める。 | `defined only` |
| `ArchitectureSignature.v1OfFiniteWithRuntimePropagation_runtimePropagation_eq_some_zero_iff` | `theorem` | runtime extension constructor の `runtimePropagation = some 0` が `NoRuntimeExposureObstruction` と同値であることを示す。 | `proved` |
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
| `ComponentUniverse.edgeClosed_of_covers` | `theorem` | full coverage universe では edge-closedness が coverage から従う。 | `proved` |
| `ComponentUniverse.full` | `def` | full coverage universe を作る。 | `defined only` |
| `ComponentUniverse.componentPairWitnesses` | `def` | finite component universe から ordered component-pair witness list を作る。 | `defined only` |
| `ComponentUniverse.ComponentPairRequired` | `def` | finite universe 内の component pair を required witness predicate として表す。 | `defined only` |
| `ComponentUniverse.mem_componentPairWitnesses_iff` | `theorem` | component-pair witness list の membership が両 endpoint の universe membership と一致する。 | `proved` |
| `ComponentUniverse.coversWitnesses_componentPairWitnesses` | `theorem` | finite component universe が生成する component-pair witness list は required pair universe を cover する。 | `proved` |
| `ComponentUniverse.v0` | `def` | universe から v0 signature を計算する。 | `defined only` |
| `FiniteArchGraph` | `structure` | `ArchGraph` と `ComponentUniverse` を束ねる構造。 | `defined only` |
| `FiniteArchGraph.ofComponentUniverse` | `def` | 既存の graph と component universe を `FiniteArchGraph` として束ねる。 | `defined only` |
| `FiniteArchGraph.components` | `def` | bundled component universe の測定 component list を読む。 | `defined only` |
| `FiniteArchGraph.nodup_components` | `theorem` | `FiniteArchGraph.components` が duplicate-free であること。 | `proved` |
| `FiniteArchGraph.covers_components` | `theorem` | `FiniteArchGraph.components` が全 component を cover すること。 | `proved` |
| `FiniteArchGraph.edgeClosed_components` | `theorem` | `FiniteArchGraph` の edge が component universe 内に閉じていること。 | `proved` |
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
| `noRuntimeExposureObstruction_iff_noSemanticRuntimeExposureObstruction_under_universe` | `theorem` | finite runtime universe 下で measured / bounded runtime obstruction absence と semantic `Reachable` 版 obstruction absence が同値であること。 | `proved` |
| `runtimePropagationOfFinite_eq_zero_iff_noSemanticRuntimeExposureObstruction_under_universe` | `theorem` | finite runtime universe 下で runtime exposure radius 0 と semantic runtime obstruction absence が同値であること。 | `proved` |
| `v1OfFiniteWithRuntimePropagation_runtimePropagation_eq_some_zero_iff_noSemanticRuntimeExposureObstruction_under_universe` | `theorem` | runtime extension constructor の `runtimePropagation = some 0` が finite runtime universe 下で semantic runtime obstruction absence と同値であること。 | `proved` |
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
| `nilpotencyIndexOfFinite` | `def` | finite `ComponentUniverse` 上の executable nilpotency index candidate。`some k` は最初の zero adjacency power であり、required zero-axis ではない。 | `defined only` |
| `ArchitectureSignature.v1OfComponentUniverseWithNilpotencyIndex` | `def` | `ArchitectureSignatureV1.nilpotencyIndex` を matrix bridge から埋める entry point。`RequiredAxesAvailableAndZero` へ接続するには別途 axis interpretation が必要。 | `defined only` |
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

## Dependency Obstruction

File: `Formal/Arch/DependencyObstruction.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ClosedWalkWitness` | `structure` | 非空閉 walk を dependency obstruction witness として束ねる。 | `defined only` |
| `ClosedWalkBad` | `def` | `ClosedWalkWitness` 自体を forbidden obstruction として扱う predicate。 | `defined only` |
| `closedWalkViolatingWitnesses` | `def` | measured closed-walk witness list を generic `violatingWitnesses` へ載せる。 | `defined only` |
| `closedWalkViolationCount` | `def` | measured closed-walk obstruction witness の個数。 | `defined only` |
| `mem_closedWalkViolatingWitnesses_iff` | `theorem` | closed-walk violation list の membership が measured witness membership と一致する。 | `proved` |
| `closedWalkViolationCount_eq_zero_iff_forall_not_bad` | `theorem` | measured closed-walk violation count が 0 であることと measured witness に bad がないことが一致する。 | `proved` |
| `hasClosedWalk_of_closedWalkWitness` | `theorem` | `ClosedWalkWitness` から既存 `HasClosedWalk` を得る。 | `proved` |
| `exists_closedWalkWitness_of_hasClosedWalk` | `theorem` | 既存 `HasClosedWalk` を `ClosedWalkWitness` として包装する。 | `proved` |
| `hasClosedWalk_iff_exists_closedWalkWitness` | `theorem` | `HasClosedWalk` と closed-walk obstruction witness の存在が一致する。 | `proved` |
| `walkAcyclic_iff_no_closedWalkObstruction` | `theorem` | `WalkAcyclic` と closed-walk obstruction witness 不在が一致する。 | `proved` |
| `acyclic_iff_no_closedWalkObstruction` | `theorem` | graph-level `Acyclic` と closed-walk obstruction witness 不在が一致する。 | `proved` |
| `adjacencyNilpotent_iff_no_closedWalkObstruction` | `theorem` | finite universe 上で adjacency nilpotence と closed-walk obstruction witness 不在が一致する。 | `proved` |
| `no_closedWalkObstruction_of_adjacencyNilpotent` | `theorem` | adjacency nilpotence から closed-walk obstruction witness 不在を得る。 | `proved` |
| `adjacencyNilpotent_of_no_closedWalkObstruction` | `theorem` | closed-walk obstruction witness 不在から finite universe 上の adjacency nilpotence を得る。 | `proved` |

## Analytic Representation

File: `Formal/Arch/AnalyticRepresentation.lean`

Issue [#280](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/280)
の対象範囲は、Architecture Calculus / structural theorem から analytic layer への representation
map と、その strength predicate を分離して定義することである。zero-reflecting /
obstruction-reflecting は coverage、witness completeness、semantic contract coverage に相対化し、
witness absence だけから flatness を主張しない。
Issues [#323](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/323)
and [#328](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/328)
audit this section as the representation bridge entry point.  The preserving
directions move structural zero / obstruction facts into the analytic domain,
while the reflecting directions require the recorded coverage and completeness
assumptions before returning to structural facts.

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `AnalyticRepresentation` | `structure` | architecture state から analytic domain への representation map、structural / analytic zero predicate、structural / analytic obstruction predicate、coverage / witness completeness / semantic contract coverage、non-conclusions を束ねる schema。 | `defined only` |
| `AnalyticRepresentation.ZeroPreserving` | `def` | structural zero が analytic zero へ写ること。 | `defined only` |
| `AnalyticRepresentation.ZeroReflecting` | `def` | coverage / completeness 前提の下で analytic zero から structural zero を得ること。 | `defined only` |
| `AnalyticRepresentation.ObstructionPreserving` | `def` | structural obstruction witness が analytic obstruction witness へ写ること。 | `defined only` |
| `AnalyticRepresentation.ObstructionReflecting` | `def` | coverage / completeness 前提の下で analytic obstruction witness から structural obstruction witness を得ること。 | `defined only` |
| `AnalyticRepresentation.RecordsNonConclusions` | `def` | representation package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `AnalyticRepresentation.analyticZero_of_structuralZero` | `theorem` | `ZeroPreserving` から structural zero を analytic zero へ送る。 | `proved` |
| `AnalyticRepresentation.structuralZero_of_analyticZero` | `theorem` | `ZeroReflecting` と coverage / completeness 前提から analytic zero を structural zero へ戻す。 | `proved` |
| `AnalyticRepresentation.analyticObstruction_of_structuralObstruction` | `theorem` | `ObstructionPreserving` から structural obstruction witness を analytic obstruction witness へ送る。 | `proved` |
| `AnalyticRepresentation.structuralObstruction_of_analyticObstruction` | `theorem` | `ObstructionReflecting` と coverage / completeness 前提から analytic obstruction witness を structural obstruction witness へ戻す。 | `proved` |
| `ObstructionValuation` | `structure` | selected witness に対する `Nat` valuation、zero が witness absence を反映する条件、obstruction が positive valuation を与える条件、coverage assumptions、non-conclusions を束ねる。 | `defined only` |
| `ObstructionValuation.NoSelectedObstruction` | `def` | selected valuation universe に obstruction witness が存在しないこと。 | `defined only` |
| `ObstructionValuation.ZeroReflectingSum` | `def` | aggregate value 0 から selected obstruction witness absence を得る aggregate-level reflection predicate。 | `defined only` |
| `ObstructionValuation.no_obstruction_of_value_zero` | `theorem` | individual witness value が 0 なら、その selected obstruction witness は存在しない。 | `proved` |
| `ObstructionValuation.noSelectedObstruction_of_zeroReflectingSum` | `theorem` | zero-reflecting aggregate value から selected obstruction witness absence を得る。 | `proved` |
| `ObstructionValuation.RecordsNonConclusions` | `def` | valuation package の non-conclusion clause を predicate として取り出す。 | `defined only` |

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
- より一般の `Sem_A(p) - Sem_A(q)` 型の数値 curvature metric。
  `Formal/Arch/Curvature.lean` は、zero-separating distance の個別 diagram bridge、
  有限測定 list 上の `Nat` total bridge、正の重みに相対化された weighted total bridge
  までを含む。Signature axis 化、重み calibration、empirical cost model はまだ導入しない。
- `relationComplexity`, `runtimePropagation`, `empiricalChangeCost` の実証相関。
- extractor output が `ComponentUniverse` の完全な witness であるという主張。
- `rho(A)` と変更波及・障害伝播コストの相関。

これらは [証明義務と実証仮説](proof_obligations.md) または [個別設計メモ](design/README.md) で扱う。
