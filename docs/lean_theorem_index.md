# Lean 定義・定理索引

この文書は、現在 Lean 側に存在する主要な定義・定理の索引である。

`proof_obligations.md` は未解決課題と実証仮説の台帳として扱い、この文書は実装済みの Lean API を確認する入口として扱う。

この索引は手動管理である。Lean 定義・定理を追加、削除、rename する PR では、研究上参照する主要 API に影響がある場合にこの文書も更新する。

`Formal/Arch` 以下の責務分類、file move の判断基準、当面の配置ルールは
[Lean module 階層整理方針](formal/lean_module_organization.md) に分離する。

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

## Decomposable

File: `Formal/Arch/Decomposable.lean`

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
| `localReplacementContract_iff_noProjectionObstruction_and_representativeStable_and_observationFactorsThrough` | `theorem` | 局所置換契約を projection obstruction 不在、representative stability、observation factorization に分解する。 | `proved` |
| `noProjectionObstruction_and_noLSPObstruction_of_localReplacementContract` | `theorem` | 局所置換契約から projection obstruction と LSP obstruction の同時消滅を得る。 | `proved` |
| `violationCounts_eq_zero_of_localReplacementContract` | `theorem` | 局所置換契約から projection soundness violation count と LSP violation count が同時に 0 になることを得る。 | `proved` |

## Feature Extension

Issue [#243](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/243)
の feature extension 最小コアは、`FeatureExtension`、`Flatness`,
`ArchitecturePath`, `DiagramFiller` の四つの module に分かれる。この節以降は、
first-class feature addition schema、coverage-aware flatness、有限 path calculus、
semantic diagram filler の順に、Lean 上で参照できる主要 API を索引する。

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

## Split Extension Lifting

File: `Formal/Arch/SplitExtensionLifting.lean`

Issue [#264](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/264)
の対象範囲は、strict fibration ではなく observation model に相対化された
feature section / core retraction と、selected feature step の bounded lifting である。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `FeatureSectionLaw` | `def` | `q ∘ s ≈ id` を、extended 側 `featureView` と feature 側 selected observation の一致として表す observation-relative section law。 | `defined only` |
| `ObservationalCoreRetraction` | `def` | `r ∘ i ≈ id` を、embedded core に対する selected core observation の一致として表す retraction law。 | `defined only` |
| `SplitExtensionLiftingData` | `structure` | `FeatureExtension`、feature observation、core observation、feature section、core retraction、section / retraction law、interface factorization、required invariant preservation を束ねる selected split-extension lifting schema。 | `defined only` |
| `SplitExtensionLiftingData.featureSection_observes` | `theorem` | feature section law を accessor theorem として取り出す。 | `proved` |
| `SplitExtensionLiftingData.coreRetraction_observes_coreEmbedding` | `theorem` | embedded core 上の observational core retraction law を accessor theorem として取り出す。 | `proved` |
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

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureOperationKind` | `inductive` | Phase A3 の最初の対象である `compose`, `replace`, `protect`, `repair` の operation family tag。 | `defined only` |
| `ArchitectureOperationKind.label` | `def` | theorem package や docs から参照するための operation tag label。 | `defined only` |
| `ProofObligation` | `structure` | formal universe、required laws、invariant family、witness universe、coverage / exactness、operation precondition、conclusion、non-conclusions を束ねる最小 schema。 | `defined only` |
| `ProofObligation.AssumptionsHold` | `def` | proof obligation の visible assumptions をまとめる。 | `defined only` |
| `ProofObligation.Discharged` | `def` | visible assumptions から conclusion が得られること。 | `defined only` |
| `ProofObligation.RecordsNonConclusions` | `def` | theorem package が明示的な non-conclusions を持つこと。 | `defined only` |
| `ProofObligation.discharged_of_conclusion` | `theorem` | conclusion が直接与えられれば obligation は discharge できる。 | `proved` |
| `OperationProofObligation` | `structure` | operation kind ごとに生成される proof obligation、precondition、non-conclusion を束ねる。 | `defined only` |
| `OperationProofObligation.compose` | `def` | `compose` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.replace` | `def` | `replace` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.protect` | `def` | `protect` operation 用 proof-obligation package constructor。 | `defined only` |
| `OperationProofObligation.repair` | `def` | `repair` operation 用 proof-obligation package constructor。 | `defined only` |
| `ArchitectureOperation` | `structure` | operation kind、source / target state、precondition、生成 proof obligation、operation tag 一致、前後 witness family、後段 witness から前段 witness への mapping と soundness field を束ねる。 | `defined only` |
| `ArchitectureOperation.GeneratedObligation` | `def` | operation に紐づく generated proof obligation を取り出す。 | `defined only` |
| `ArchitectureOperation.generatedObligation_kind` | `theorem` | operation と generated proof obligation の operation tag が一致することを取り出す。 | `proved` |
| `ArchitectureOperation.PreconditionsHold` | `def` | operation と generated obligation の visible precondition をまとめる。 | `defined only` |
| `ArchitectureOperation.witnessMapping_sound` | `theorem` | post-operation witness から pre-operation witness への片方向 mapping soundness を取り出す。 | `proved` |
| `ArchitectureOperation.exists_sourceWitness_of_targetWitness` | `theorem` | post-operation witness があれば、対応する pre-operation witness が存在する。 | `proved` |

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

## Architecture Extension Formula

Issue [#262](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/262)
の `ArchitectureExtensionFormula_structural` は、現時点では `future proof obligation`
であり、対応する Lean module / theorem はまだ存在しない。

予定されている Lean 対象範囲は、`ExtensionCoverage`, `ExtensionObstructionWitness`,
inherited core / feature local / interaction / lifting failure / filling failure /
complexity transfer / residual coverage gap の classification predicate 群、および
bounded classification theorem である。実装時にはこの節を File と API table へ更新する。

Non-conclusions: 最初の theorem package は disjoint decomposition、global extractor
completeness、runtime / semantic universe completeness、または universe 外の obstruction
分類を主張しない。

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

## Diagram Filler

File: `Formal/Arch/DiagramFiller.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureDiagram` | `structure` | 同じ start / target state を持つ二つの有限 architecture path を semantic diagram skeleton として束ねる。 | `defined only` |
| `DiagramFiller` | `def` | `ArchitecturePath.PathHomotopy` により、diagram の左右 path が finite path calculus 上で fillable であることを表す。 | `defined only` |
| `NonFillabilityWitness` | `structure` | domain-specific witness value と、任意の `DiagramFiller` を反駁する soundness 証拠を束ねる。 | `defined only` |
| `NonFillabilityWitnessFor` | `def` | `NonFillabilityWitness` が特定の witness value `w` についての証人であること。 | `defined only` |
| `obstructionAsNonFillability_sound` | `theorem` | `NonFillabilityWitnessFor D w` から `¬ DiagramFiller D` を得る片方向 soundness theorem。 | `proved` |
| `WitnessUniverseComplete` | `def` | bounded completeness theorem 用の有限 witness universe 完全性前提。逆向き theorem 自体は未主張。 | `defined only` |
| `CouponDiscountExample.couponDiscountDiagram` | `def` | coupon と discount の順序依存例を、二つの operation order を持つ diagram skeleton として表す。 | `defined only` |

## Flatness

File: `Formal/Arch/Flatness.lean`

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
| `NoUnmeasuredRequiredAxis` | `def` | static / runtime / semantic の required evidence が bounded universes で測定済みであること。 | `defined only` |
| `ArchitectureFlatWithin` | `def` | coverage-aware な bounded architecture flatness。coverage と三層 flatness を束ね、global extractor / telemetry / semantic universe completeness は主張しない。 | `defined only` |
| `staticFlatWithin_of_architectureFlatWithin` | `theorem` | bounded architecture flatness から static flatness を取り出す。 | `proved` |
| `runtimeFlatWithin_of_architectureFlatWithin` | `theorem` | bounded architecture flatness から runtime flatness を取り出す。 | `proved` |
| `semanticFlatWithin_of_architectureFlatWithin` | `theorem` | bounded architecture flatness から semantic flatness を取り出す。 | `proved` |
| `noUnmeasuredRequiredAxis_of_architectureFlatWithin` | `theorem` | bounded architecture flatness から coverage package を取り出す。 | `proved` |
| `ExtensionCoverageComplete` | `def` | feature extension の core embedding、feature embedding、extended static edges、declared coverage assumptions が supplied extended universe で cover されること。 | `defined only` |
| `StaticSplitExtensionCoverageComplete` | `def` | `StaticSplitExtension` 用の coverage package。 | `defined only` |
| `coreEmbedding_mem_of_extensionCoverageComplete` | `theorem` | complete extension coverage から core embedding の universe membership を得る。 | `proved` |
| `featureEmbedding_mem_of_extensionCoverageComplete` | `theorem` | complete extension coverage から feature embedding の universe membership を得る。 | `proved` |
| `extended_edge_mem_of_extensionCoverageComplete` | `theorem` | complete extension coverage から extended static edge endpoints の universe membership を得る。 | `proved` |
| `policySound_of_staticSplitExtension` | `theorem` | compatible な static graph に対して、`StaticSplitExtension` の no-new-forbidden-edge 条件から policy soundness を得る。 | `proved` |
| `staticFlatWithin_of_staticSplitExtension` | `theorem` | coverage-aware な静的範囲で、static split extension と残りの静的 law 前提から `StaticFlatWithin` を得る。runtime / semantic flatness は結論しない。 | `proved` |

## Obstruction Kernel

File: `Formal/Arch/Obstruction.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `violatingWitnesses` | `def` | 有限な測定 witness list から、`bad` predicate を満たす阻害証人を取り出す。 | `defined only` |
| `violationCount` | `def` | `violatingWitnesses` の長さとして measured obstruction count を数える。 | `defined only` |
| `mem_violatingWitnesses_iff` | `theorem` | `violatingWitnesses` の membership が、測定対象であり `bad` を満たすことと一致する。 | `proved` |
| `violationCount_eq_zero_iff_forall_not_bad` | `theorem` | `violationCount bad xs = 0` と、すべての測定 witness が `bad` でないことの同値。 | `proved` |
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
| `numericalCurvature_eq_zero_iff_DiagramCommutes` | `theorem` | zero-separating distance の下で、数値 curvature 0 と diagram commutativity が一致する。 | `proved` |
| `numericalCurvature_eq_zero_of_DiagramCommutes` | `theorem` | 可換な diagram は数値 curvature が 0 である。 | `proved` |
| `DiagramCommutes_of_numericalCurvature_eq_zero` | `theorem` | 数値 curvature 0 から diagram commutativity を得る。 | `proved` |
| `numericalCurvatureObstruction_iff_DiagramBad` | `theorem` | 数値 curvature obstruction と既存の `DiagramBad` predicate が一致する。 | `proved` |
| `not_numericalCurvatureObstruction_iff_DiagramCommutes` | `theorem` | 個別 diagram で、数値 curvature obstruction 不在と可換性が一致する。 | `proved` |
| `diagramLawful_iff_noNumericalCurvatureObstruction` | `theorem` | required diagram family の lawfulness と数値 curvature obstruction 不在を接続する。 | `proved` |
| `totalCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero` | `theorem` | 有限測定 universe 上で、合計 curvature 0 と各 measured diagram の curvature 0 が一致する。 | `proved` |
| `totalCurvature_eq_zero_iff_forall_measured_DiagramCommutes` | `theorem` | 有限測定 universe 上で、合計 curvature 0 と各 measured diagram の可換性が一致する。 | `proved` |
| `totalCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction` | `theorem` | 有限測定 universe 上で、合計 curvature 0 と measured numerical curvature obstruction 不在が一致する。 | `proved` |

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
5. package は `architectureLawful_iff_architectureZeroCurvatureTheoremPackage` を入口にし、static structural core の QED として読む。runtime / empirical / numerical curvature は「現在 Lean に入れていないもの」の境界として読む。

## State Transition / Effect Boundary Laws

File: `Formal/Arch/StateEffect.lean`

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
- 重み付き・より一般の `Sem_A(p) - Sem_A(q)` 型の数値 curvature metric。
  `Formal/Arch/Curvature.lean` は、zero-separating distance の個別 diagram bridge と
  有限測定 list 上の `Nat` total bridge までを含み、重み・Signature axis 化・
  empirical cost model はまだ導入しない。
- `relationComplexity`, `runtimePropagation`, `empiricalChangeCost` の実証相関。
- extractor output が `ComponentUniverse` の完全な witness であるという主張。
- `rho(A)` と変更波及・障害伝播コストの相関。

これらは [証明義務と実証仮説](proof_obligations.md) または [個別設計メモ](design/README.md) で扱う。
