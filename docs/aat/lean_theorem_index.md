# Lean 定義・定理索引

この文書は、現在 Lean 側に存在する主要な定義・定理の索引である。

`proof_obligations.md` は未解決課題と実証仮説の台帳として扱い、この文書は実装済みの Lean API を確認する入口として扱う。

この索引は手動管理である。Lean 定義・定理を追加、削除、rename する PR では、研究上参照する主要 API に影響がある場合にこの文書も更新する。

`Formal/Arch` 以下の現在の主要 API と canonical path は、この索引で確認する。
過去の file move 方針メモは archive に退避しており、現行入口としては使わない。
Atom 起点の AAT 数学本文は
[AAT 数学理論](mathematical_theory/README.md) を入口とする。

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

File: `Formal/Arch/Core/Graph.lean`

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

## Selected Presentation / Complete Extraction Boundary

File: `Formal/Arch/Core/Presentation.lean`

この節は Foundations の `selected universe` / `presentation-indexed claim` /
`complete extraction` 境界を Lean 側に置く。`SelectedPresentation` は
ambient system から選ばれた bounded component type への読み方を固定するが、
ambient repository 全体の component / edge / telemetry / semantic observation が
すべて選択されたとは主張しない。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `SelectedPresentation` | `structure` | selected component type を ambient universe 内で読むための embedding を持つ presentation。 | `defined only` |
| `SelectedPresentation.identity` | `def` | selected universe と ambient universe が同じ場合の identity presentation。 | `defined only` |
| `SelectedPresentation.Covers` | `def` | ambient component が selected presentation の image に入ること。 | `defined only` |
| `SelectedPresentation.covers_identity` | `theorem` | identity presentation は自身の universe 全体を cover する。 | `proved` |
| `PresentationClaim` | `abbrev` | selected presentation に index された claim。 | `defined only` |
| `AATJudgement` | `def` | `P` の下で claim を読む Foundations judgement form。 | `defined only` |
| `aatJudgement_iff` | `theorem` | `AATJudgement P claim` は `claim P` の評価である。 | `proved` |
| `aatJudgement_intro` | `theorem` | `claim P` から `AATJudgement P claim` を導入する。 | `proved` |
| `aatJudgement_elim` | `theorem` | `AATJudgement P claim` から `claim P` を取り出す。 | `proved` |
| `aatJudgement_congr` | `theorem` | selected presentation 上で同値な claim は judgement として同値。 | `proved` |
| `EdgeRestriction` | `def` | ambient edge relation を selected presentation 上へ制限する。 | `defined only` |
| `GraphRestriction` | `def` | ambient `ArchGraph` を selected presentation 上の `ArchGraph` へ制限する。 | `defined only` |
| `SameEdgeRestriction` | `def` | 二つの ambient relation が selected presentation からは同じに見えること。 | `defined only` |
| `sameEdgeRestriction_refl` | `theorem` | selected edge restriction の反射性。 | `proved` |
| `sameEdgeRestriction_symm` | `theorem` | selected edge restriction の対称性。 | `proved` |
| `sameEdgeRestriction_trans` | `theorem` | selected edge restriction の推移性。 | `proved` |
| `sameEdgeRestriction_of_edgeRestriction_eq` | `theorem` | selected edge restriction の関数等式から `SameEdgeRestriction` を得る。 | `proved` |
| `edgeRestriction_eq_of_sameEdgeRestriction` | `theorem` | `SameEdgeRestriction` から selected edge restriction の関数等式を得る。 | `proved` |
| `sameEdgeRestriction_iff_edgeRestriction_eq` | `theorem` | `SameEdgeRestriction` と selected edge restriction equality の同値。 | `proved` |
| `CompleteForRelation` | `def` | ambient relation のすべての edge endpoint が selected presentation に表現されること。 | `defined only` |
| `CompleteForGraph` | `def` | `CompleteForRelation` の graph-level spelling。 | `defined only` |
| `completeForGraph_iff_completeForRelation` | `theorem` | graph-level completeness と relation-level completeness の定義的同値。 | `proved` |
| `completeForGraph_of_completeForRelation` | `theorem` | relation-level completeness から graph-level completeness を得る。 | `proved` |
| `completeForRelation_of_completeForGraph` | `theorem` | graph-level completeness から relation-level completeness を得る。 | `proved` |
| `completeForRelation_left_covered` | `theorem` | complete relation から edge の左 endpoint coverage を取り出す。 | `proved` |
| `completeForRelation_right_covered` | `theorem` | complete relation から edge の右 endpoint coverage を取り出す。 | `proved` |
| `completeForRelation_of_covers_all` | `theorem` | 全 ambient component coverage があれば任意 relation に対する complete representation を得る。 | `proved` |
| `completeForRelation_identity` | `theorem` | identity presentation は自身の universe 上の任意 relation に complete。 | `proved` |
| `edgeRestriction_identity` | `theorem` | identity presentation を通した edge restriction は元の relation と一致する。 | `proved` |
| `graphRestriction_identity` | `theorem` | identity presentation を通した graph restriction は元の graph と一致する。 | `proved` |
| `completeForGraph_identity` | `theorem` | identity presentation は自身の universe 上の任意 graph に complete。 | `proved` |
| `sameEdgeRestriction_of_graphRestriction_eq` | `theorem` | restricted graph equality から selected edge restriction equivalence を得る。 | `proved` |
| `graphRestriction_eq_of_sameEdgeRestriction` | `theorem` | selected edge restriction equivalence から restricted graph equality を得る。 | `proved` |
| `sameEdgeRestriction_iff_graphRestriction_eq` | `theorem` | graph-level で `SameEdgeRestriction` と restricted graph equality が同値。 | `proved` |
| `CompleteExtractionCounterexample.same_selectedRestriction` | `theorem` | empty ambient relation と out-of-scope edge を追加した relation は selected restriction が一致する。 | `proved` |
| `CompleteExtractionCounterexample.complete_base` | `theorem` | empty ambient relation は selected presentation に complete。 | `proved` |
| `CompleteExtractionCounterexample.not_complete_withOutOfScopeEdge` | `theorem` | out-of-scope source を持つ ambient edge は selected presentation に complete ではない。 | `proved` |
| `CompleteExtractionCounterexample.selectedRestriction_same_but_completeExtraction_differs` | `theorem` | 同じ selected restriction でも complete extraction status は一致しない concrete counterexample package。 | `proved` |
| `CompleteExtractionCounterexample.exists_sameSelectedRestriction_completeExtraction_differs` | `theorem` | 上記 counterexample の existential form。 | `proved` |

Non-conclusions: `CompleteForRelation` は明示前提であり、
`ComponentUniverse` や `ArchitectureCore` から任意の ambient repository に対して
自動的に導かれない。counterexample は selected presentation-level reading と
ambient completeness を分離するための formal anchor であり、実コード観測
completeness、runtime telemetry completeness、semantic universe completeness は結論しない。

## Reachability

File: `Formal/Arch/Core/Reachability.lean`

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

File: `Formal/Arch/Core/Layering.lean`

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
`Formal/Arch/Core/Finite.lean` の `ComponentUniverse.strictLayered_of_acyclic` と
`FiniteArchGraph.strictLayered_of_acyclic` として索引する。これは static graph
layering の theorem であり、semantic contract や runtime protocol の一般的な
decomposability を結論しない。

## Decomposable

File: `Formal/Arch/Core/Decomposable.lean`

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

Files: `Formal/Arch/Core/Category.lean`, `Formal/Arch/Core/ThinCategory.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `SmallCategory` | `structure` | 最小限の category 構造。 | `defined only` |
| `SmallCategory.discrete` | `def` | 離散 category。 | `defined only` |
| `ComponentCategory` | `def` | `Reachable` を Hom にする component category。 | `defined only` |
| `componentCategory_thin` | `theorem` | `ComponentCategory` が thin category であること。 | `proved` |

`ComponentCategory` は path count や walk length を忘れる。定量指標は `Walk`, `SimpleWalk`, finite metrics, adjacency matrix 側で扱う。

## Projection / DIP

File: `Formal/Arch/Law/Projection.lean`

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

Files: `Formal/Arch/Law/Observation.lean`, `Formal/Arch/Law/LSP.lean`, `Formal/Arch/Law/LocalReplacement.lean`

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
| Static split feature extension | `StaticSplitFeatureExtension`, `SelectedStaticSplitExtension`, `StaticExtensionWitness` | `defined only` / `proved` | selected static split law とその witness に限る。runtime / semantic flatness は主張しない。 |
| featureView observation law | `FeatureViewSound`, `FeatureObservationCoverage`, `FeatureViewSectionPackage` | `defined only` / `proved` | selected observation model に相対化する。strict equality、全 component の一意分解、global split completeness は主張しない。 |
| Extension coverage failure | `ExtensionCoverageWitness`, `ExtensionCoverageFailureCoverage` | `defined only` / `proved` | supplied `ComponentUniverse` 上の coverage-only 診断であり、static split law failure とは別に扱う。 |
| SplitFeatureExtensionWithin preservation package | `SplitFeatureExtensionWithin`, `architectureFlatWithin_of_splitFeatureExtensionWithin` | `defined only` / `proved` | extension coverage、static side conditions、runtime / semantic split evidence を明示前提にした bounded `ArchitectureFlatWithin` への入口であり、global `ArchitectureFlat` へは昇格しない。 |

File: `Formal/Arch/Extension/FeatureExtension.lean`

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
| `SelectedStaticSplitExtension` | `structure` | 固定された feature extension と policy parameters に対し、静的 split の4条件を unbundled predicate として束ねる。runtime / semantic / source-observation layer は含めない。 | `defined only` |
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
runtime flatness、semantic flatness、global `ArchitectureFlat`、
無条件の global composition law は主張しない。

File: `Formal/Arch/Extension/FeatureExtensionExamples.lean`

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
| `SelectedSplitExtensionLiftingExample.extension` | `def` | two-state coupon feature の selected lifting positive example 用 `FeatureExtension`。 | `defined only` |
| `SelectedSplitExtensionLiftingExample.featureViewSectionPackage` | `def` | declared feature embedding を selected `FeatureViewSectionPackage` として束ねる具体例。 | `defined only` |
| `SelectedSplitExtensionLiftingExample.featureViewSectionPackage_observes` | `theorem` | 具体例の selected feature section が selected feature observation と一致することを示す。 | `proved` |
| `SelectedSplitExtensionLiftingExample.liftingData` | `def` | section law、observational core retraction、interface factorization、required invariant preservation を束ねる具体的 `SplitExtensionLiftingData`。 | `defined only` |
| `SelectedSplitExtensionLiftingExample.compatibleWithInterface` | `theorem` | selected `couponDraft -> couponApplied` step の `CompatibleWithInterface` を構成する。 | `proved` |
| `SelectedSplitExtensionLiftingExample.selectedStepLifts` | `theorem` | `SplitExtensionLifting` から selected feature step の lifted step と core preservation を得る。 | `proved` |
| `SelectedSplitExtensionLiftingExample.selectedStepPreservationPackage` | `theorem` | `SplitExtensionLifting_preservationPackage` から selected feature/core preservation package を得る。 | `proved` |
| `SelectedSplitExtensionLiftingExample.selectedStep_coreInvariant_target_of_source` | `theorem` | preservation package accessor から selected core invariant preservation を取り出す。 | `proved` |
| `SelectedSplitExtensionLiftingExample.selectedStep_liftedSource_observes` | `theorem` | preservation package accessor から lifted source の selected feature observation law を取り出す。 | `proved` |
| `SelectedSplitExtensionLiftingExample.selectedStep_liftedTarget_observes` | `theorem` | preservation package accessor から lifted target の selected feature observation law を取り出す。 | `proved` |
| `ThreeLayerFlatnessPositiveExample.staticSplit` | `def` | repaired coupon extension を bounded three-layer flatness example の static split package として再利用する。 | `defined only` |
| `ThreeLayerFlatnessPositiveExample.selectedStaticSplit` | `theorem` | concrete static evidence として selected static split predicate を取り出す。 | `proved` |
| `ThreeLayerFlatnessPositiveExample.canonicalUniverse` | `def` | repaired coupon extended graph の finite `ComponentUniverse`。 | `defined only` |
| `ThreeLayerFlatnessPositiveExample.extensionCoverage` | `theorem` | static split extension の core / feature embeddings と extended static edges が selected universe で cover されることを示す。 | `proved` |
| `ThreeLayerFlatnessPositiveExample.runtimeGraph` | `def` | coupon service から declared port、declared port から payment API への selected runtime interaction graph。 | `defined only` |
| `ThreeLayerFlatnessPositiveExample.runtimeInteractionProtected` | `theorem` | selected runtime interactions が selected runtime policy を満たすことを示す。 | `proved` |
| `ThreeLayerFlatnessPositiveExample.selectedSemanticDiagram` | `def` | direct checkout と port-mediated checkout を比較する selected semantic diagram。 | `defined only` |
| `ThreeLayerFlatnessPositiveExample.semanticCoverage` | `theorem` | selected semantic diagram universe が required semantic diagrams を cover することを示す。 | `proved` |
| `ThreeLayerFlatnessPositiveExample.featureDiagramsCommute` | `theorem` | measured semantic diagram が commute することを示す。 | `proved` |
| `ThreeLayerFlatnessPositiveExample.runtimeSemanticPreservation` | `def` | runtime interaction protection と selected semantic commutation を `RuntimeSemanticSplitPreservation` として束ねる。 | `defined only` |
| `ThreeLayerFlatnessPositiveExample.splitFeatureExtensionWithin` | `def` | static split、coverage、static side conditions、runtime / semantic preservation、non-conclusions を `SplitFeatureExtensionWithin` として束ねる。 | `defined only` |
| `ThreeLayerFlatnessPositiveExample.architectureFlatWithin` | `theorem` | `architectureFlatWithin_of_splitFeatureExtensionWithin` から bounded `ArchitectureFlatWithin` を得る positive canonical theorem。 | `proved` |
| `ThreeLayerFlatnessPositiveExample.noUnmeasuredRequiredAxis` | `theorem` | bounded theorem package から selected coverage package を取り出す。 | `proved` |
| `ThreeLayerFlatnessPositiveExample.exactObservationBridge` | `theorem` | selected coverage に相対化した exact observation bridge を得る。extractor / telemetry completeness は含めない。 | `proved` |
| `ThreeLayerFlatnessPositiveExample.recordsNonConclusions` | `theorem` | bounded split package が global `ArchitectureFlat`、runtime / semantic completeness を自動導出しない marker を保持することを示す。 | `proved` |

Non-conclusions: coupon static canonical example は静的 split と selected hidden dependency
witness に限る。runtime flatness、semantic flatness は主張しない。
selected split-extension lifting positive example は一つの selected feature step と local
compatibility package に限る。strict section/retraction equality、全 component の一意分解、
all feature steps の automatic lifting、ambient semantic coverage は主張しない。
three-layer flatness positive example は selected finite component universe、selected runtime
interaction graph、selected measured semantic diagram に相対化された bounded
`ArchitectureFlatWithin` に限る。global `ArchitectureFlat`、
telemetry completeness、ambient semantic coverage は主張しない。

## Split Extension Lifting

File: `Formal/Arch/Extension/SplitExtensionLifting.lean`

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
| `SplitExtensionLiftingData.interfaceFactorization_holds` | `theorem` | lifting data から declared-interface factorization assumption を accessor theorem として取り出す。 | `proved` |
| `SplitExtensionLiftingData.preservesRequiredInvariants_holds` | `theorem` | lifting data から required invariant preservation assumption を accessor theorem として取り出す。 | `proved` |
| `SplitExtensionLiftingData.featureViewSectionPackage` | `def` | lifting data の feature-section 部分を公開 `FeatureViewSectionPackage` として取り出す。 | `defined only` |
| `SplitExtensionLiftingData.featureViewSectionPackage_observes` | `theorem` | lifting data 由来の公開 section package が selected feature observation law を満たすことを示す。 | `proved` |
| `SelectedFeatureStep` | `structure` | selected feature state 間の feature step。 | `defined only` |
| `LiftedExtensionStep` | `structure` | extended architecture 内の lifted endpoint pair。 | `defined only` |
| `LawfulFeatureStep` | `def` | selected feature invariant を feature step が保存すること。 | `defined only` |
| `CanonicalLiftedFeatureStep` | `def` | feature section によって feature step の endpoint を extended endpoint へ持ち上げる canonical lift。 | `defined only` |
| `LiftsFeatureStep` | `def` | lifted step が section-induced endpoints を持ち、extended static edge として存在すること。 | `defined only` |
| `PreservesCoreInvariants` | `def` | core retraction 後の selected core invariant を lifted step が保存すること。 | `defined only` |
| `liftedFeatureStep_source_observes` | `theorem` | `LiftsFeatureStep` から lifted source endpoint の selected feature observation を feature step source の observation として読み替える。 | `proved` |
| `liftedFeatureStep_target_observes` | `theorem` | `LiftsFeatureStep` から lifted target endpoint の selected feature observation を feature step target の observation として読み替える。 | `proved` |
| `CompatibleWithInterface` | `structure` | selected step ごとの extended edge、interface factorization、coverage、core invariant preservation を束ねる compatibility package。 | `defined only` |
| `CompatibleWithInterface.liftedEdge_holds` | `theorem` | compatibility package から selected step の lifted extended edge を accessor theorem として取り出す。 | `proved` |
| `CompatibleWithInterface.interfaceFactorization_holds` | `theorem` | compatibility package から declared-interface factorization assumption を selected step 単位で取り出す。 | `proved` |
| `CompatibleWithInterface.coverageAssumptions_holds` | `theorem` | compatibility package から selected coverage assumptions を accessor theorem として取り出す。 | `proved` |
| `CompatibleWithInterface.coreInvariantPreserved_holds` | `theorem` | compatibility package から selected core invariant preservation assumption を accessor theorem として取り出す。 | `proved` |
| `SplitExtensionLifting` | `theorem` | selected split-extension lifting data、lawful feature step、interface compatibility から、lifting と core invariant preservation を満たす extended step の存在を得る。 | `proved` |
| `SplitExtensionLiftingPreservationPackage` | `structure` | lifted-step fact、feature-side invariant preservation、core-side invariant preservation を後続 theorem package 用に束ねる conclusion package。 | `defined only` |
| `SplitExtensionLiftingPreservationPackage.liftsFeatureStep_holds` | `theorem` | conclusion package から lifted-step fact を取り出す。 | `proved` |
| `SplitExtensionLiftingPreservationPackage.liftedFeatureSource_observes` | `theorem` | conclusion package から lifted source endpoint の selected feature observation law を取り出す。 | `proved` |
| `SplitExtensionLiftingPreservationPackage.liftedFeatureTarget_observes` | `theorem` | conclusion package から lifted target endpoint の selected feature observation law を取り出す。 | `proved` |
| `SplitExtensionLiftingPreservationPackage.featureInvariantPreserved_holds` | `theorem` | conclusion package から feature-side invariant preservation を取り出す。 | `proved` |
| `SplitExtensionLiftingPreservationPackage.featureInvariant_target_of_source` | `theorem` | source feature invariant から target feature invariant を得る package accessor。 | `proved` |
| `SplitExtensionLiftingPreservationPackage.coreInvariantPreserved_holds` | `theorem` | conclusion package から core-side invariant preservation を取り出す。 | `proved` |
| `SplitExtensionLiftingPreservationPackage.coreInvariant_target_of_source` | `theorem` | lifted source の core invariant から lifted target の core invariant を得る package accessor。 | `proved` |
| `SplitExtensionLifting_preservationPackage` | `theorem` | selected split-extension lifting data、lawful feature step、interface compatibility から、feature/core preservation を束ねた conclusion package の存在を得る。 | `proved` |

Non-conclusions: `SplitExtensionLifting` は strict equality の section/retraction、全 component の一意分解、
runtime flatness、semantic flatness、または all feature steps の自動 lifting を主張しない。

## Architecture Operation

File: `Formal/Arch/Operation/Operation.lean`

Issues [#322](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/322)
and [#327](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/327)
audit this schema as the entry point for generated operation proof obligations.
The useful accessors are the generated-obligation kind theorem, the combined
precondition predicate, and the one-way witness mapping theorem; this package
does not by itself assert any unconditional operation law or global flatness
preservation.
Issue [#359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/359)
records where each Chapter 3 operation lives after the public tag / proof
obligation schema: [Architecture Calculus catalog placement](../archive/2026-05-09-first-class-docs/design/architecture_calculus_catalog_placement.md).
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

File: `Formal/Arch/Operation/OperationKernel.lean`

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
incident prediction、telemetry / source-observation layer は AAT theorem package の外で扱う。

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

File: `Formal/Arch/Operation/OperationLaws.lean`

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
[Architecture Calculus catalog placement](../archive/2026-05-09-first-class-docs/design/architecture_calculus_catalog_placement.md)
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
| observation / runtime / migration entrypoint | schema bridge / substantive theorem | selected projection、observation、runtime、compatibility window、migration assumptions から下表の bounded conclusion を得る。 | runtime telemetry completeness、semantic completeness、empirical cost claim。 |
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
| `ArchitectureCalculusLaw.MigrationCompatibilityWindow` | `def` | selected compatibility predicate が migration plan の endpoints と各 primitive step boundary で成り立つこと。telemetry / semantic / source-observation layer は含めない。 | `defined only` |
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

Files: `Formal/Arch/Operation/OperationInvariant.lean`, `Formal/Arch/Patterns/LocalContractDesignPattern.lean`, `Formal/Arch/Patterns/SRPDesignPattern.lean`, `Formal/Arch/Patterns/ISPDesignPattern.lean`, `Formal/Arch/Patterns/StructuralDesignPattern.lean`, `Formal/Arch/Patterns/RuntimeProtectionDesignPattern.lean`, `Formal/Arch/Patterns/StateTransitionDesignPattern.lean`, `Formal/Arch/Patterns/EventSourcingSagaDesignPattern.lean`, `Formal/Arch/Patterns/ReplicatedLogDesignPattern.lean`

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
CRUD の一般 theorem 化、実コード event log completeness、
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
| `StateTransitionNonConclusionClause` | `inductive` | 状態遷移代数層の non-conclusion clause として event log completeness、operational cost improvement、CRUD の一般 theorem 化を列挙する。 | `defined only` |
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
実コード log completeness、実コード event log completeness、
運用コスト改善、または CRUD の一般 theorem 化
を主張しない。

## Chapter 7 Theorem Package Entrypoints

File: `Formal/Arch/Evolution/Chapter7TheoremPackages.lean`

Issue [#420](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/420)
は、第7章 7.1〜7.6 の中心 theorem 候補に対応する既存 bounded theorem package を、
一箇所から import / 追跡できる入口として整理する作業である。

`Chapter7TheoremPackages.Candidate` は docs-facing な候補名、設計書の節番号、
代表 Lean declaration 名、non-conclusion boundary を束ねる軽量 API である。
この module は既存 theorem package を再利用する統合入口であり、無条件の global theorem、
runtime / semantic completeness、solver completeness を新たに
主張しない。Atom-generated feature extension、operation transport、repair、synthesis
soundness の wrapper は generated input から既存 bounded package を発火させる入口として
公開する。

Issue [#421](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/421)
は、数学設計書の schematic name と Lean API 名の対応を
`Chapter7TheoremPackages.SchematicCorrespondence` と
`Chapter7TheoremPackages.Candidate.schematicCorrespondences` で安定化する。
この対応表は docs-facing metadata であり、既存 bounded package の薄い読み替えに留める。

Issue [#422](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/422)
は、この節と `proof_obligations.md` 側の対応を、第7章の統合・命名・索引 status
として閉じる作業である。以下の表は `Chapter7TheoremPackages.Candidate`
の代表 entrypoint と non-conclusion boundary を docs index 側へ展開したものである。

| 設計書 | 候補 | 代表 Lean entrypoint | Status | Bounded reading / non-conclusion boundary |
| --- | --- | --- | --- | --- |
| 7.1 | Split Extension Preservation | `SplitFeatureExtensionWithin`, `architectureFlatWithin_of_splitFeatureExtensionWithin`, `LawfulExtensionPreservesFlatness`, `LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation`, `Chapter7TheoremPackages.generatedSplitFeatureExtension_flatWithin`, `generatedSplitFeatureExtension_recordsNonConclusions` | `defined only` / `proved` | coverage-aware `ArchitectureFlatWithin` への入口。Atom-generated identity feature extension 上でも発火する。global flatness や source-observation layer は AAT theorem package の外で扱う。 |
| 7.2 | Non-split Extension Witness | `NonSplitExtensionWitnessPackage`, `Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage`, `NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitness`, `Chapter9DiagramFilling.generatedFillingFailureBridge_not_selectedSplitExtension_of_generatedWitness`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension`, `Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists` | `defined only` / `proved` | soundness と、明示的な coverage / exactness assumptions 下の bounded completeness に限る。Atom-generated diagram filling failure は generated identity feature extension 上の non-split witness package へ接続する。 |
| 7.3 | Repair as Re-splitting | `SelectedObstructionUniverse`, `AdmissibleRepairRule`, `repairStepDecreases_of_admissible`, `extensionObstructionMeasure_decreases_of_admissible`, `Chapter7TheoremPackages.generatedRepair_target_shapeLevel`, `generatedRepair_clears_selected_target`, `generatedRepair_toRepairClearingPackage`, `generatedRepairProblemOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount`, `generatedRepairProblemOperation_unmapped_target_atom_primitive`, `generatedRepairFromProblem_shapeLevel`, `generatedRepairFromProblem_clears_selected_problem`, `generatedRepairFromProblem_toRepairClearingPackage` | `defined only` / `proved` | selected obstruction measure の decrease と、generated shape-level repair target / pre-molecule repair problem operation の AtomShape distance / unmapped target primitive evidence から generated target object の repair-clearing package への入口。全 obstruction removal や termination は結論しない。 |
| 7.4 | Complexity Transfer | `BoundedComplexityTransferPackage`, `BoundedComplexityTransferPackage.complexityTransfer_selectedAlternative`, `BoundedComplexityTransferPackage.no_free_elimination_bounded`, `Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitnessExists_of_no_free_elimination`, `generatedComplexityTransferExtensionObstructionWitness_multilabel_classified` | `defined only` / `proved` | selected runtime / semantic / policy target への transfer witness。Atom-generated identity feature extension 上の `.complexityTransfer` classification に接続する。global conservation や empirical cost theorem は主張しない。 |
| 7.5 | No-solution Certificate | `NoSolutionCertificate`, `ValidNoSolutionCertificate`, `NoSolutionCertificate.sound_of_valid`, `Chapter7TheoremPackages.generatedSynthesisCandidate_flatWithin`, `generatedSynthesisCandidate_toSynthesisSoundnessPackage` | `defined only` / `proved` | valid certificate soundness。generated synthesis candidate は positive candidate soundness として既存 AAT synthesis package へ接続する。solver failure だけでは no-solution proof にならない。 |
| 7.6 | Architecture Evolution | `ArchitectureTransition`, `ArchitectureEvolution`, `ArchitectureTransition.flatness_of_transitionPreservesFlatness`, `ArchitectureTransition.reportedObstruction_of_drift`, `eventuallyFlat_of_targetFlat`, `evolutionPathPreservesFlatness`, `Chapter7TheoremPackages.generatedOperation_atomShape_transformed`, `generatedOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount`, `generatedOperation_unmapped_target_atom_primitive`, `generatedOperation_toOperationTransportPackage` | `defined only` / `proved` | selected transition / migration path に相対化する。generated operation は AtomShape transport、mapped carrier shape distance、unmapped target primitive evidence、generated AATCore 間の operation transport package へ接続する。全 transition の自動 preservation は主張しない。 |

### Chapter 7 schematic name correspondence

| 設計書の schematic name | 対応する Lean API | 読み替え |
| --- | --- | --- |
| `SplitFeatureExtensionWithin U X F X'` | `SplitFeatureExtensionWithin`, `splitFeatureExtensionWithin_of_runtimeSemanticSplitPreservation` | explicit `ComponentUniverse` 上の bounded split feature extension package。 |
| `InteractionLawfulWithin U X F X'` | `RuntimeSemanticSplitPreservation`, `RuntimeInteractionProtected`, `FeatureDiagramsCommute`, `LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation` | runtime interaction protection と selected semantic diagram commutation を束ねた証拠として読む。 |
| `ArchitectureFlatWithin U X'` | `ArchitectureFlatWithin`, `architectureFlatWithin_of_splitFeatureExtensionWithin`, `LawfulExtensionPreservesFlatness`, `Chapter7TheoremPackages.generatedSplitFeatureExtension_flatWithin`, `Chapter7TheoremPackages.generatedSplitFeatureExtension_recordsNonConclusions` | coverage と measured semantic diagram に相対化された bounded flatness。generated identity feature extension でも発火するが、global `ArchitectureFlat` ではない。 |
| `ExtensionObstructionWitness X F X' w` | `ExtensionObstructionWitness`, `SelectedExtensionObstructionWitness`, `NonSplitExtensionWitnessPackage.WitnessPredicate` | selected witness universe 内の obstruction witness。 |
| `ExtensionWitnessComplete X F X'` | `NonSplitExtensionWitnessPackage.coverageAssumptions`, `NonSplitExtensionWitnessPackage.exactnessAssumptions`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension`, `Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists`, `Chapter9DiagramFilling.generatedFillingFailureBridge_not_selectedSplitExtension_of_generatedWitness` | non-split から selected witness 存在を得る逆向きは coverage / exactness assumptions に相対化する。generated diagram filling failure は generated identity feature extension 上の selected witness と split-refutation に接続する。 |
| `NonSplitExtensionWitness X F X' w` | `SelectedObstructionUniverse`, `NonSplitExtensionWitness` | repair 側では選択された obstruction universe の witness として読む。 |
| `AdmissibleRepairRule r w` | `AdmissibleRepairRule`, `repairStepDecreases_of_admissible`, `extensionObstructionMeasure_decreases_of_admissible` | selected rule / witness pair に対する selected measure decrease。 |
| generated repair clears shape-level target | `Chapter7TheoremPackages.generatedRepair_target_shapeLevel`, `Chapter7TheoremPackages.generatedRepair_clears_selected_target`, `Chapter7TheoremPackages.generatedRepair_toRepairClearingPackage`, `Chapter7TheoremPackages.generatedRepairProblemOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount`, `Chapter7TheoremPackages.generatedRepairProblemOperation_unmapped_target_atom_primitive`, `Chapter7TheoremPackages.generatedRepairFromProblem_shapeLevel`, `Chapter7TheoremPackages.generatedRepairFromProblem_clears_selected_problem`, `Chapter7TheoremPackages.generatedRepairFromProblem_toRepairClearingPackage` | generated repair target は port / slot / valence-level target として読み、repair problem operation の mapped carrier 変化量を AtomShape distance として公開し、source map 外の target carrier も primitive atom として保持した上で、generated target object 上の AAT repair-clearing package へ接続する。 |
| `ComplexityTransferredTo Runtime/Semantic/Policy t` | `ComplexityTransferredTo`, `ComplexityTransferTarget.runtime`, `ComplexityTransferTarget.semantic`, `ComplexityTransferTarget.policy`, `ComplexityTransferredWithinSelectedTargets` | selected runtime / semantic / policy target axis への bounded transfer witness。 |
| Complexity Transfer theorem candidate | `BoundedComplexityTransferPackage`, `BoundedComplexityTransferPackage.complexityTransfer_selectedAlternative`, `BoundedComplexityTransferPackage.no_free_elimination_bounded`, `Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_classified`, `Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitnessExists_of_no_free_elimination`, `Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_multilabel_classified` | proof elimination がない場合の selected target transfer を返す bounded alternative を、generated identity feature extension の `.complexityTransfer` classification に接続する。 |
| `ProducesNoSolutionCertificate C cert` | `NoSolutionCertificate` | solver failure ではなく proof-carrying certificate package。 |
| `ValidNoSolutionCertificate cert C` | `ValidNoSolutionCertificate`, `NoSolutionCertificate.sound_of_valid` | valid certificate から selected constraint system の no-solution soundness を得る。 |
| generated synthesis candidate soundness | `Chapter7TheoremPackages.generatedSynthesisCandidate_flatWithin`, `Chapter7TheoremPackages.generatedSynthesisCandidate_toSynthesisSoundnessPackage` | generated target law model から positive synthesis candidate soundness を読む。これは no-solution certificate ではない。 |
| `TransitionPreservesFlatness t` | `ArchitectureTransition.TransitionPreservesFlatness`, `ArchitectureTransition.flatness_of_transitionPreservesFlatness` | selected flatness predicate に対する single-step preservation。 |
| `ReportedObstruction (ApplyTransition X t) w` | `ArchitectureTransition.ReportedObstruction`, `ArchitectureTransition.reportedObstruction_of_drift` | selected drift evidence に相対化された obstruction reporting。 |
| `EventuallyFlat plan` | `EventuallyFlat`, `eventuallyFlat_of_targetFlat`, `evolutionPathPreservesFlatness`, `Chapter7TheoremPackages.generatedOperation_atomShape_transformed`, `Chapter7TheoremPackages.generatedOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount`, `Chapter7TheoremPackages.generatedOperation_unmapped_target_atom_primitive`, `Chapter7TheoremPackages.generatedOperation_toOperationTransportPackage` | selected migration path または preserving path に対する bounded eventual flatness。generated operation は AtomShape transformation、mapped shape distance、unmapped target primitive evidence、generated AATCore transport package として読む。 |

Non-conclusions: この統合入口は、既存 package の bounded / coverage-aware な読みを
横断的に索引するだけである。global `ArchitectureFlat`、全 obstruction coverage、
runtime telemetry completeness、semantic universe completeness、
solver completeness、empirical cost 改善、global complexity conservation は結論しない。

## Repair

File: `Formal/Arch/Repair/Repair.lean`,

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
Atom repair bridge も selected atom obstruction circuit / target exactness / selected repair universe
に相対化され、全 repair synthesis、全 semantic repair correctness は主張しない。

## Repair Synthesis

File: `Formal/Arch/Repair/RepairSynthesis.lean`,

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

File: `Formal/Arch/Repair/RepairSynthesisExamples.lean`

Issue [#477](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/477)
は、上記 schema を小さい finite state / witness universe で読むための concrete example を追加する。
example は selected universe に相対化され、全 obstruction removal、solver completeness、
global flatness preservation、empirical cost 改善は主張しない。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `RepairSynthesisExamples.smallRepairStates` / `smallRepairWitnesses` | `def` | repair example の小さい state / witness universe を列挙する。 | `defined only` |
| `RepairSynthesisExamples.smallRepairStates_complete` / `smallRepairWitnesses_complete` | `theorem` | 小さい repair state / witness universe の列挙が各型を覆うこと。 | `proved` |
| `RepairSynthesisExamples.selectedLeakUniverse` | `def` | selected leak witness だけを測る二状態 repair universe。 | `defined only` |
| `RepairSynthesisExamples.splitFeatureStep_decreases` | `theorem` | concrete repair step で selected obstruction measure が減少すること。 | `proved` |
| `RepairSynthesisExamples.smallFiniteRepairPackage` | `def` | bounded plan と non-conclusions を束ねた concrete `FiniteRepairPackage`。 | `defined only` |
| `RepairSynthesisExamples.smallFiniteRepair_selectedObstructionsCleared` | `theorem` | `FiniteRepairPackage.selectedObstructionsCleared` を concrete package に適用する例。 | `proved` |
| `RepairSynthesisExamples.smallSynthesisSoundnessPackage` | `def` | 小さい candidate synthesis system の soundness package。 | `defined only` |
| `RepairSynthesisExamples.smallSynthesis_candidate_satisfies` | `theorem` | `SynthesisSoundnessPackage.candidate_satisfies` を concrete candidate に適用する例。 | `proved` |
| `RepairSynthesisExamples.conflictingRequirementsCertificatePackage` | `def` | conflicting requirements に対する小さい no-solution certificate package。 | `defined only` |
| `RepairSynthesisExamples.smallNoSolution_from_valid_certificate` | `theorem` | `NoSolutionCertificate.sound_of_valid` を valid certificate に適用する例。 | `proved` |

## Architecture Extension Formula

File: `Formal/Arch/Extension/ArchitectureExtensionFormula.lean`

Issues [#321](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/321),
[#326](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/326),
[#458](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/458),
[#459](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/459),
and [#460](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/460)
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
| `LiftingFailureWitnessPayload` | `structure` | selected feature step について、lawful feature step でありながら `SplitExtensionLiftingPreservationPackage` が得られないことを、第10章の `.liftingFailure` bridge payload として包む。 | `defined only` |
| `liftingFailureExtensionObstructionWitness` | `def` | selected split-extension lifting failure payload から `.liftingFailure` に分類された `ExtensionObstructionWitness` を構成する。 | `defined only` |
| `liftingFailureExtensionObstructionWitness_classified` | `theorem` | bridge constructor で作った witness が `ClassifiedAsLiftingFailure` を満たすことを示す。 | `proved` |
| `not_compatibleWithInterface_of_liftingFailurePayload` | `theorem` | selected lifting failure payload から、その selected step の `CompatibleWithInterface` 不成立を得る local contrapositive bridge。 | `proved` |
| `liftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage` | `theorem` | selected lifting preservation package の不在から、分類済み lifting-failure witness の存在を得る代表 bridge。 | `proved` |
| `ClassifiedAsFillingFailure` | `def` | witness が required diagram の filling failure として分類されること。 | `defined only` |
| `fillingFailureExtensionObstructionWitness_classified` | `theorem` | bridge constructor で作った witness が `ClassifiedAsFillingFailure` を満たすことを示す。 | `proved` |
| `FillingFailureRefutesSplit` | `def` | selected filling-failure payload が selected split predicate を反駁するための明示 premise。`NonFillabilityWitnessFor` 単独では split failure を結論しない。 | `defined only` |
| `not_selectedSplitExtension_of_fillingFailurePayload` | `theorem` | `FillingFailureRefutesSplit` 前提の下で selected payload から selected split failure を得る bounded soundness theorem。 | `proved` |
| `FillingFailureBridgePackage` | `structure` | selected filling-failure payload universe、coverage / exactness assumptions、split refutation premise、bounded completeness、non-conclusions を束ねる bridge package。 | `defined only` |
| `FillingFailureBridgePackage.SelectedWitness` | `def` | bridge package が誘導する `.fillingFailure` 分類済み selected extension witness predicate。 | `defined only` |
| `FillingFailureBridgePackage.toNonSplitExtensionWitnessPackage` | `def` | filling-failure bridge package を generic `NonSplitExtensionWitnessPackage` へ埋め込む。 | `defined only` |
| `FillingFailureBridgePackage.selectedExtensionObstructionWitnessExists_of_selectedPayloadExists` | `theorem` | selected payload の存在から generic package 側の selected obstruction witness 存在を構成する。 | `proved` |
| `ClassifiedAsComplexityTransfer` | `def` | witness が complexity / analytic diagnostic axis への transfer として分類されること。 | `defined only` |
| `ComplexityTransferWitnessPayload` | `structure` | `ComplexityTransferredTo` の selected target axis と selected transfer witness を、第10章の `.complexityTransfer` bridge payload として包む。 | `defined only` |
| `complexityTransferExtensionObstructionWitness` | `def` | selected complexity-transfer payload から `.complexityTransfer` に分類された `ExtensionObstructionWitness` を構成する。 | `defined only` |
| `complexityTransferExtensionObstructionWitness_classified` | `theorem` | bridge constructor で作った witness が `ClassifiedAsComplexityTransfer` を満たすことを示す。 | `proved` |
| `complexityTransferExtensionObstructionWitnessExists_of_transferredTo` | `theorem` | target-specific な `ComplexityTransferredTo` conclusion から、分類済み complexity-transfer witness の存在を得る。 | `proved` |
| `complexityTransferExtensionObstructionWitnessExists_of_no_free_elimination` | `theorem` | `BoundedComplexityTransferPackage.no_free_elimination_bounded` の conclusion を、第10章の `.complexityTransfer` 分類 witness 存在へ接続する代表 bridge。 | `proved` |
| `ResidualCoverageGapWitnessPayload` | `structure` | selected `ExtensionCoverageWitness` を、第10章の `.residualCoverageGap` bridge payload として包む。coverage-only 診断であり、static split law failure や runtime / semantic flatness failure は主張しない。 | `defined only` |
| `residualCoverageGapExtensionObstructionWitness` | `def` | selected extension-coverage diagnostic payload から `.residualCoverageGap` に分類された `ExtensionObstructionWitness` を構成する。 | `defined only` |
| `ClassifiedAsResidualCoverageGap` | `def` | witness が residual evidence または bounded coverage gap として分類されること。 | `defined only` |
| `residualCoverageGapExtensionObstructionWitness_classified` | `theorem` | bridge constructor で作った witness が `ClassifiedAsResidualCoverageGap` を満たすことを示す。 | `proved` |
| `not_extensionCoverage_of_residualCoverageGapPayload` | `theorem` | residual-coverage payload から、その bounded `ExtensionCoverage` premise の不成立を得る。 | `proved` |
| `residualCoverageGapExtensionObstructionWitnessExists_of_extensionCoverageWitnessExists` | `theorem` | selected coverage witness 存在から、分類済み residual-coverage-gap witness の存在を得る。 | `proved` |
| `residualCoverageGapExtensionObstructionWitnessExists_of_not_extensionCoverage` | `theorem` | `ExtensionCoverageFailureCoverage` 前提の下で、`ExtensionCoverage` 失敗を `.residualCoverageGap` 分類 witness 存在へ接続する代表 bridge。 | `proved` |
| `ArchitectureExtensionFormula_structural` | `theorem` | bounded extension coverage の下で、任意の selected extension obstruction witness が 7 分類 predicate の少なくとも一つで cover されること。 | `proved` |
| `MultiLabelClassifiedAsInheritedCore` | `def` | multi-label witness が embedded core 由来 label を持つこと。 | `defined only` |
| `MultiLabelClassifiedAsFeatureLocal` | `def` | multi-label witness が追加 feature 内部由来 label を持つこと。 | `defined only` |
| `MultiLabelClassifiedAsInteraction` | `def` | multi-label witness が feature/core interaction label を持つこと。 | `defined only` |
| `MultiLabelClassifiedAsLiftingFailure` | `def` | multi-label witness が lifting failure label を持つこと。 | `defined only` |
| `liftingFailureExtensionObstructionWitness_multilabel_classified` | `theorem` | lifting-failure bridge witness を multi-label layer に埋め込んでも `.liftingFailure` label が得られることを示す。 | `proved` |
| `MultiLabelClassifiedAsFillingFailure` | `def` | multi-label witness が filling failure label を持つこと。 | `defined only` |
| `fillingFailureExtensionObstructionWitness_multilabel_classified` | `theorem` | filling-failure bridge witness を multi-label layer に埋め込んでも `.fillingFailure` label が得られることを示す。 | `proved` |
| `MultiLabelClassifiedAsComplexityTransfer` | `def` | multi-label witness が complexity / analytic transfer label を持つこと。 | `defined only` |
| `complexityTransferExtensionObstructionWitness_multilabel_classified` | `theorem` | complexity-transfer bridge witness を multi-label layer に埋め込んでも `.complexityTransfer` label が得られることを示す。 | `proved` |
| `MultiLabelClassifiedAsResidualCoverageGap` | `def` | multi-label witness が residual evidence / coverage gap label を持つこと。 | `defined only` |
| `residualCoverageGapExtensionObstructionWitness_multilabel_classified` | `theorem` | residual-coverage bridge witness を multi-label layer に埋め込んでも `.residualCoverageGap` label が得られることを示す。 | `proved` |
| `ArchitectureExtensionFormula_multilabel_structural` | `theorem` | bounded extension coverage の下で、任意の multi-label extension obstruction witness が 7 分類 predicate の少なくとも一つで cover されること。 | `proved` |

Non-conclusions: 最初の theorem package は disjoint decomposition、ambient source observation
completeness、runtime / semantic universe completeness、または universe 外の obstruction
分類を主張しない。`NonSplitExtensionWitnessPackage` の同値版も package の
coverage / exactness assumptions に相対化され、global witness completeness は主張しない。
diagram filling failure から split failure への接続は `FillingFailureRefutesSplit` または
`FillingFailureBridgePackage` の明示 premise に相対化され、`NonFillabilityWitnessFor`
単独から `¬ SplitExtension` は結論しない。
bounded flatness preservation は runtime / semantic flatness と coverage assumptions を明示する
`LawfulExtensionPreservesFlatness` として `Formal/Arch/Extension/Flatness.lean` で証明済みである。
このため `ArchitectureExtensionFormula_structural` と
`ArchitectureExtensionFormula_multilabel_structural` は 7 分類の少なくとも一つに入ることを
述べる coverage theorem であり、分類が互いに素であることや全 obstruction universe の
完全分類は結論しない。multi-label layer は同一 witness が複数 label を持つことを許し、
single-label layer との bridge は payload preservation と元 label の保存だけを主張する。
complexity-transfer bridge は `ComplexityTransferredTo` または
`BoundedComplexityTransferPackage.no_free_elimination_bounded` の selected witness を
`.complexityTransfer` に分類するだけであり、global complexity conservation や empirical
cost 改善は追加しない。
residual-coverage bridge は selected `ExtensionCoverageWitness` を `.residualCoverageGap`
に分類するだけであり、static split law failure、runtime / semantic flatness failure、
または coverage witness universe 外の completeness は追加しない。
lifting-failure bridge は selected feature step ごとの
`SplitExtensionLiftingPreservationPackage` 不在を `.liftingFailure` に分類するだけであり、
strict section/retraction equality、global split completeness、または all feature steps の
automatic lifting failure は追加しない。

## Complexity Transfer

File: `Formal/Arch/Signature/ComplexityTransfer.lean`

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

File: `Formal/Arch/Repair/RepairTransferCounterexample.lean`

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

## Chapter 8 Homotopy Skeleton Entrypoint

File: `Formal/Arch/Evolution/Chapter8HomotopySkeleton.lean`

Issue [#451](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/451)
は、第8章 Homotopy Skeleton の有限 path calculus、generated path homotopy、
selected observation invariance、diagram filler / non-fillability witness API を
docs-facing な公開入口として整理する作業である。

`Chapter8HomotopySkeleton.Candidate` は docs-facing な候補名、設計書の節番号、
代表 Lean declaration 名、schematic name correspondence、non-conclusion boundary
を束ねる軽量 API である。この module は既存 API を横断 import し、Atom-generated
path / diagram theorem を docs-facing entrypoint として公開する。ただし
ambient semantic coverage、HoTT / 高次圏論の completeness、
全 observation axis の保存を新たに主張しない。

| 設計書 | 候補 | 代表 Lean entrypoint | Status | Bounded reading / non-conclusion boundary |
| --- | --- | --- | --- | --- |
| 8.1 | Architecture paths | `ArchitecturePath`, `ArchitecturePath.append`, `ArchitecturePath.append_assoc`, `ArchitecturePath.length_append`, `ArchitecturePath.everyStepPreserves_append`, `ArchitecturePath.pathPreservesInvariant`, `AAT.GeneratedArchitecturePath.preservesInvariant`, `Chapter8HomotopySkeleton.generatedPath_preservesInvariant` | `defined only` / `proved` | endpoint-indexed な有限 path calculus。generated relation-backed step/path 上でも invariant preservation theorem が発火する。path count や walk-length metric semantics はこの API の範囲外。 |
| 8.1 | Generated path homotopy | `ArchitecturePath.PathHomotopy`, `AAT.GeneratedPathHomotopy`, `Chapter8HomotopySkeleton.generatedSignatureTrajectory_refutesGeneratedPathHomotopy`, `ArchitecturePath.PathHomotopy.cons_congr`, `ArchitecturePath.PathHomotopy.append_left`, `ArchitecturePath.PathHomotopy.append_right`, `ArchitecturePath.HomotopyInvariant`, `ArchitecturePath.architectureHomotopyInvariance` | `defined only` / `proved` | supplied contracts 上の generated relation と文脈閉包。Atom-generated path homotopy への trajectory refutation entrypoint を持つ。HoTT / 高次圏論の completeness は主張しない。 |
| 8 | Selected observation invariance | `ArchitecturePath.PathHomotopy.observation_eq_append`, `ArchitecturePath.PathHomotopy.observation_eq`, `Chapter8HomotopySkeleton.generatedPathHomotopy_observation_eq_append`, `Chapter8HomotopySkeleton.generatedPathHomotopy_observation_eq`, `CouponDiscountExample.pathHomotopy_preserves_roundingTrace_append`, `CouponDiscountExample.pathHomotopy_preserves_roundingTrace` | `proved` | generator preservation と context congruence の明示前提下での selected observation 保存。Atom-generated path homotopy でも同じ theorem が発火する。全 observation axis の保存ではない。 |
| 8 | Diagram filler | `ArchitectureDiagram`, `DiagramFiller`, `diagramFiller_observation_eq`, `observationDifference_refutesDiagramFiller`, `AAT.GeneratedDiagramFiller`, `Chapter8HomotopySkeleton.generatedDiagramFiller_observation_eq`, `Chapter8HomotopySkeleton.generatedObservationDifference_refutesDiagramFiller`, `CouponDiscountExample.couponDiscountDiagram`, `CouponDiscountExample.roundingOrder_refutes_selectedDiagramFiller` | `defined only` / `proved` | finite path calculus 上の diagram fillability。Atom-generated diagram filler でも selected observation 差分による refutation は generator preservation 前提に相対化される。ambient semantic coverage は主張しない。 |
| 8 | Obstruction as non-fillability | `NonFillabilityWitness`, `NonFillabilityWitnessFor`, `obstructionAsNonFillability_sound`, `observationDifference_nonFillabilityWitnessFor`, `AAT.GeneratedNonFillabilityWitnessFor`, `Chapter8HomotopySkeleton.generated_obstructionAsNonFillability_sound`, `Chapter8HomotopySkeleton.generatedObservationDifference_nonFillabilityWitnessFor`, `WitnessUniverseComplete`, `obstructionAsNonFillability_complete_bounded`, `CouponDiscountExample.roundingOrder_nonFillabilityWitnessFor`, `CouponDiscountExample.roundingOrderValuation_positive` | `defined only` / `proved` | soundness と、`WitnessUniverseComplete` に相対化された bounded completeness に限る。Atom-generated diagram では selected generated observation difference から generated non-fillability witness を構成する。source-observation layer や full witness coverage は主張しない。 |

### Chapter 8 schematic name correspondence

| 設計書の schematic name | 対応する Lean API | 読み替え |
| --- | --- | --- |
| `ArchitecturePath Step X Y` | `ArchitecturePath`, `ArchitecturePath.append`, `ArchitecturePath.length`, `ArchitecturePath.length_append`, `AAT.GeneratedArchitecturePath.preservesInvariant`, `Chapter8HomotopySkeleton.generatedPath_preservesInvariant` | explicit primitive step family 上の finite endpoint-indexed path calculus。generated relation-backed path 上でも invariant theorem package が発火する。 |
| `PathHomotopy p q` | `ArchitecturePath.PathHomotopy`, `AAT.GeneratedPathHomotopy`, `Chapter8HomotopySkeleton.generatedSignatureTrajectory_refutesGeneratedPathHomotopy`, `ArchitecturePath.PathHomotopy.cons_congr`, `ArchitecturePath.PathHomotopy.append_left`, `ArchitecturePath.PathHomotopy.append_right` | supplied generator contracts で生成され、selected finite path context で閉じる relation。Atom-generated object 上では selected trajectory difference が generated homotopy を refute する。 |
| `Obs p = Obs q for homotopic paths` | `ArchitecturePath.PathHomotopy.observation_eq_append`, `ArchitecturePath.PathHomotopy.observation_eq`, `Chapter8HomotopySkeleton.generatedPathHomotopy_observation_eq_append`, `Chapter8HomotopySkeleton.generatedPathHomotopy_observation_eq` | generator-preservation と context-congruence assumptions に相対化した selected observation preservation。Atom-generated path homotopy に直接特殊化する。 |
| coupon / discount selected observation preservation | `CouponDiscountExample.pathHomotopy_preserves_roundingTrace_append`, `CouponDiscountExample.pathHomotopy_preserves_roundingTrace` | 一般 selected observation theorem の coupon / discount 特殊化。 |
| `DiagramFiller D` | `ArchitectureDiagram`, `DiagramFiller`, `AAT.GeneratedArchitectureDiagram`, `AAT.GeneratedDiagramFiller` | generated path homotopy による finite semantic diagram fillability。 |
| `Obs D.lhs ≠ Obs D.rhs` refutes `DiagramFiller D` | `diagramFiller_observation_eq`, `observationDifference_refutesDiagramFiller`, `Chapter8HomotopySkeleton.generatedDiagramFiller_observation_eq`, `Chapter8HomotopySkeleton.generatedObservationDifference_refutesDiagramFiller` | selected observation を各 generator が保存する明示前提の下で、generated diagram filler の不在を示す。 |
| `NonFillabilityWitness D w` | `NonFillabilityWitness`, `NonFillabilityWitnessFor`, `AAT.GeneratedNonFillabilityWitnessFor`, `obstructionAsNonFillability_sound`, `observationDifference_nonFillabilityWitnessFor`, `Chapter8HomotopySkeleton.generated_obstructionAsNonFillability_sound`, `Chapter8HomotopySkeleton.generatedObservationDifference_nonFillabilityWitnessFor` | selected generated diagram と witness value に対する sound non-fillability witness。 |
| bounded completeness for non-fillability witnesses | `WitnessUniverseComplete`, `obstructionAsNonFillability_complete_bounded` | finite witness-universe completeness premise を明示した場合だけ成立する逆向き。 |

Non-conclusions: この統合入口は、既存の finite path calculus と bounded diagram witness API
を Atom-generated path / diagram entrypoint として公開する。ambient semantic coverage、HoTT / 高次圏論の完全性、
全 observation axis の保存、finite universe 外の witness coverage、
source-observation layer は AAT theorem package の外で扱う。

## Chapter 9 Diagram Filling / Split Extension Entrypoint

File: `Formal/Arch/Evolution/Chapter9DiagramFilling.lean`

親 Issue [#452](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/452)
と Issue [#454](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/454)
は、第9章 Diagram Filling and Split Extension の bounded Lean API を docs-facing な
公開入口として整理する作業である。

`Chapter9DiagramFilling.Candidate` は docs-facing な候補名、設計書の節番号、
代表 Lean declaration 名、schematic name correspondence、non-conclusion boundary
を束ねる軽量 API である。この module は既存 API を横断 import し、Atom-generated
diagram filler / non-fillability witness theorem を docs-facing entrypoint として公開する。
ただし ambient semantic coverage、strict section / retraction equality、
all feature steps の automatic lifting を新たに主張しない。

| 設計書 | 候補 | 代表 Lean entrypoint | Status | Bounded reading / non-conclusion boundary |
| --- | --- | --- | --- | --- |
| 9.1 | Diagram filling and obstruction | `ArchitectureDiagram`, `AAT.GeneratedArchitectureDiagram`, `DiagramFiller`, `AAT.GeneratedDiagramFiller`, `Chapter9DiagramFilling.generatedDiagramFiller_refl`, `diagramFiller_observation_eq`, `Chapter9DiagramFilling.generatedObservationDifference_refutesDiagramFiller`, `NonFillabilityWitnessFor`, `AAT.GeneratedNonFillabilityWitnessFor`, `Chapter9DiagramFilling.generatedObservationDifference_nonFillabilityWitnessFor`, `obstructionAsNonFillability_sound`, `WitnessUniverseComplete`, `obstructionAsNonFillability_complete_bounded` | `defined only` / `proved` | selected finite diagram と finite witness universe に相対化された filling refutation / bounded completeness。Atom-generated diagram に対する filler / refutation / witness entrypoint を持つ。ambient semantic coverage や source-observation layer は AAT theorem package の外で扱う。 |
| 9.2 | Split extension as lifting and section | `FeatureSectionLaw`, `FeatureViewSectionPackage`, `ObservationalCoreRetraction`, `SplitExtensionLiftingData`, `Chapter9DiagramFilling.generatedSelfFeatureExtension`, `Chapter9DiagramFilling.generatedSelfFeatureExtension_preservesRequiredInvariants`, `Chapter9DiagramFilling.generatedSelfFeatureExtension_interactionFactorsThroughDeclaredInterfaces`, `Chapter9DiagramFilling.generatedSelfFeatureExtension_coverageAssumptions`, `Chapter9DiagramFilling.generatedSelfFeatureExtension_proofObligations`, `Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData`, `LiftsFeatureStep`, `PreservesCoreInvariants`, `SplitExtensionLifting`, `SplitExtensionLiftingPreservationPackage`, `SplitExtensionLifting_preservationPackage`, `Chapter9DiagramFilling.generatedSelfSplitExtensionLifting_preservationPackage`, `Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitness_classified`, `Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage` | `defined only` / `proved` | observation-relative section / retraction と selected generated feature step の bounded lifting。generated self-view feature extension の field は `True` marker ではなく generated carrier primitive、generated relation-atom edge witness、generated carrier-list coverage から discharge し、preservation package と lifting-failure classification に接続する。strict equality、一意分解、all feature steps の automatic lifting は主張しない。 |
| 9.1 / 9.2 | Filling failure bridge | `FillingFailureWitnessPayload`, `Chapter9DiagramFilling.generatedFillingFailureWitnessPayload`, `fillingFailureExtensionObstructionWitness`, `Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness`, `fillingFailureExtensionObstructionWitness_classified`, `Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness_classified`, `FillingFailureRefutesSplit`, `not_selectedSplitExtension_of_fillingFailurePayload`, `FillingFailureBridgePackage.toNonSplitExtensionWitnessPackage`, `Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage`, `Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists`, `Chapter9DiagramFilling.generatedFillingFailureBridge_not_selectedSplitExtension_of_generatedWitness` | `defined only` / `proved` | generated diagram non-fillability payload を generated identity feature extension の obstruction へ分類し、non-split witness package へ接続する bridge。`GeneratedNonFillabilityWitnessFor` 単独から任意の selected split failure は結論しない。 |

### Chapter 9 schematic name correspondence

| 設計書の schematic name | 対応する Lean API | 読み替え |
| --- | --- | --- |
| `DiagramFiller D` | `ArchitectureDiagram`, `AAT.GeneratedArchitectureDiagram`, `DiagramFiller`, `AAT.GeneratedDiagramFiller`, `Chapter9DiagramFilling.generatedDiagramFiller_refl` | generated path homotopy による finite semantic diagram fillability。Atom-generated reflexive diagram は entrypoint theorem から filler を得る。 |
| `Obs D.lhs ≠ Obs D.rhs` refutes `DiagramFiller D` | `diagramFiller_observation_eq`, `observationDifference_refutesDiagramFiller`, `Chapter9DiagramFilling.generatedObservationDifference_refutesDiagramFiller` | selected observation を各 generator が保存する明示前提の下で、Atom-generated diagram filler の不在を示す。 |
| `NonFillabilityWitnessFor D w` | `NonFillabilityWitness`, `AAT.GeneratedNonFillabilityWitnessFor`, `NonFillabilityWitnessFor`, `obstructionAsNonFillability_sound`, `observationDifference_nonFillabilityWitnessFor`, `Chapter9DiagramFilling.generatedObservationDifference_nonFillabilityWitnessFor` | selected Atom-generated diagram と witness value に対する sound non-fillability witness。 |
| `WitnessUniverseComplete U D` | `WitnessUniverseComplete`, `obstructionAsNonFillability_complete_bounded` | finite witness-universe completeness premise を明示した場合だけ成立する bounded converse。 |
| `q ∘ s ≈[O_F] id_F` | `FeatureSectionLaw`, `FeatureViewSectionPackage.featureSection_observes`, `SplitExtensionLiftingData.featureSection_observes` | strict equality ではなく、selected feature observation に相対化された section law。 |
| `r ∘ i ≈[O_X] id_X` | `ObservationalCoreRetraction`, `SplitExtensionLiftingData.coreRetraction_observes_coreEmbedding` | embedded core 上の selected core observation に相対化された retraction law。 |
| selected feature operations lift to `X'` | `SelectedFeatureStep`, `LiftedExtensionStep`, `LiftsFeatureStep`, `PreservesCoreInvariants`, `SplitExtensionLifting`, `SplitExtensionLiftingPreservationPackage`, `SplitExtensionLifting_preservationPackage`, `Chapter9DiagramFilling.generatedSelfFeatureExtension`, `Chapter9DiagramFilling.generatedSelfFeatureExtension_preservesRequiredInvariants`, `Chapter9DiagramFilling.generatedSelfFeatureExtension_interactionFactorsThroughDeclaredInterfaces`, `Chapter9DiagramFilling.generatedSelfFeatureExtension_coverageAssumptions`, `Chapter9DiagramFilling.generatedSelfFeatureExtension_proofObligations`, `Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData`, `Chapter9DiagramFilling.generatedSelfSplitExtensionLifting_preservationPackage`, `Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitness_classified`, `Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage` | selected generated feature step と local compatibility package に相対化した generated self-view lifting / feature-core preservation。self-view feature-extension field は generated object carrier facts から discharge する。 |
| filling failure as extension obstruction | `FillingFailureWitnessPayload`, `Chapter9DiagramFilling.generatedFillingFailureWitnessPayload`, `fillingFailureExtensionObstructionWitness`, `Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness`, `ClassifiedAsFillingFailure`, `fillingFailureExtensionObstructionWitness_classified`, `Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness_classified` | selected generated diagram non-fillability payload を generated identity feature extension の `.fillingFailure` label の extension obstruction witness として包む。 |
| filling failure refutes selected split | `FillingFailureRefutesSplit`, `not_selectedSplitExtension_of_fillingFailurePayload`, `FillingFailureBridgePackage.toNonSplitExtensionWitnessPackage`, `Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage`, `Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists`, `Chapter9DiagramFilling.generatedFillingFailureBridge_not_selectedSplitExtension_of_generatedWitness` | split failure への接続は explicit bridge premise と selected payload coverage / exactness assumptions に相対化する。generated diagram witness は generated identity feature extension 上の non-split witness package へ渡される。 |

Non-conclusions: この統合入口は、第9章で使う bounded theorem package と bridge API を
索引するだけである。cohomological obstruction、ambient semantic coverage、
strict section / retraction equality、全 feature step の automatic lifting、
全 split failure が filling failure であるという completeness は
結論しない。

## Chapter 10 Architecture Extension Formula Entrypoint

File: `Formal/Arch/Evolution/Chapter10ArchitectureExtensionFormula.lean`

親 Issue [#457](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/457)
と Issue [#461](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/461)
は、第10章 Structural Architecture Extension Formula の中核 theorem と、
filling / lifting / complexity-transfer / residual-coverage bridge API を
docs-facing な公開入口として整理する作業である。

`Chapter10ArchitectureExtensionFormula.Candidate` は docs-facing な候補名、
設計書の節番号、代表 Lean declaration 名、schematic name correspondence、
non-conclusion boundary を束ねる軽量 API である。この module は既存 API を
横断 import し、Atom-generated identity feature extension 上の structural
formula theorem を docs-facing entrypoint として公開する。ただし disjoint decomposition、
global witness completeness、universe-wide obstruction coverage、
source-observation layer は AAT theorem package の外で扱う。

| 設計書 | 候補 | 代表 Lean entrypoint | Status | Bounded reading / non-conclusion boundary |
| --- | --- | --- | --- | --- |
| 10 | Extension obstruction universe | `ExtensionCoverage`, `ExtensionObstructionClass`, `ExtensionObstructionWitness`, `MultiLabelExtensionObstructionWitness`, `ExtensionObstructionWitness.toMultiLabel`, `ExtensionObstructionWitness.toMultiLabel_label_iff`, `ExtensionObstructionWitness.toMultiLabel_classifiesAs`, `Chapter10ArchitectureExtensionFormula.GeneratedExtensionObstructionWitness`, `GeneratedMultiLabelExtensionObstructionWitness`, `generatedExtensionObstructionWitness_toMultiLabel`, `generatedExtensionObstructionWitness_toMultiLabel_label_iff`, `generatedExtensionObstructionWitness_toMultiLabel_classifiesAs` | `defined only` / `proved` | selected witness carrier と single-label から multi-label への payload-preserving bridge。Atom-generated identity feature extension 上の witness carrier と bridge も持つ。universe-wide obstruction coverage や source-observation layer は AAT theorem package の外で扱う。 |
| 10 | Non-split witness package | `SelectedSplitExtension`, `SelectedExtensionObstructionWitness`, `SelectedExtensionObstructionWitnessExists`, `NonSplitExtensionWitnessPackage`, `Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage`, `NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitness`, `Chapter9DiagramFilling.generatedFillingFailureBridge_not_selectedSplitExtension_of_generatedWitness`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension`, `Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists` | `defined only` / `proved` | soundness と、明示的な coverage / exactness assumptions 下の bounded completeness に限る。generated diagram filling failure は generated identity feature extension 上の non-split witness package へ接続する。 |
| 10 | Single-label structural classification | `ClassifiedAsInheritedCore`, `ClassifiedAsFeatureLocal`, `ClassifiedAsInteraction`, `ClassifiedAsLiftingFailure`, `ClassifiedAsFillingFailure`, `ClassifiedAsComplexityTransfer`, `ClassifiedAsResidualCoverageGap`, `ArchitectureExtensionFormula_structural`, `Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_structural` | `defined only` / `proved` | selected single-label witness が 7 分類 predicate の少なくとも一つに入る coverage theorem。Atom-generated identity feature extension 上でも発火する。分類の互いに素性や global completeness は主張しない。 |
| 10 | Multi-label structural classification | `MultiLabelClassifiedAsInheritedCore`, `MultiLabelClassifiedAsFeatureLocal`, `MultiLabelClassifiedAsInteraction`, `MultiLabelClassifiedAsLiftingFailure`, `MultiLabelClassifiedAsFillingFailure`, `MultiLabelClassifiedAsComplexityTransfer`, `MultiLabelClassifiedAsResidualCoverageGap`, `ArchitectureExtensionFormula_multilabel_structural`, `Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_multilabel_structural` | `defined only` / `proved` | 同一 witness の複数 label を許す coverage layer。Atom-generated identity feature extension 上でも発火する。single-label 化や disjointness は主張しない。 |
| 10 / 9 | Filling failure bridge | `FillingFailureWitnessPayload`, `Chapter9DiagramFilling.generatedFillingFailureWitnessPayload`, `fillingFailureExtensionObstructionWitness`, `Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness`, `fillingFailureExtensionObstructionWitness_classified`, `Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness_classified`, `FillingFailureRefutesSplit`, `not_selectedSplitExtension_of_fillingFailurePayload`, `FillingFailureBridgePackage.toNonSplitExtensionWitnessPackage`, `Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage`, `Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists`, `fillingFailureExtensionObstructionWitness_multilabel_classified`, `Chapter10ArchitectureExtensionFormula.generatedFillingFailureExtensionObstructionWitness_multilabel_classified` | `defined only` / `proved` | selected generated diagram non-fillability payload を generated identity feature extension の `.fillingFailure` へ分類し、single-label / multi-label formula と non-split witness package へ接続する bridge。任意の split failure は結論しない。 |
| 10 / 9.2 | Lifting failure bridge | `LiftingFailureWitnessPayload`, `Chapter9DiagramFilling.generatedSelfFeatureExtension`, `Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData`, `liftingFailureExtensionObstructionWitness`, `Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitness_classified`, `liftingFailureExtensionObstructionWitness_classified`, `not_compatibleWithInterface_of_liftingFailurePayload`, `liftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage`, `Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage`, `liftingFailureExtensionObstructionWitness_multilabel_classified`, `Chapter10ArchitectureExtensionFormula.generatedSelfLiftingFailureExtensionObstructionWitness_multilabel_classified` | `defined only` / `proved` | selected generated self-view feature step ごとの lifting preservation package 不在を `.liftingFailure` へ分類する bridge。strict equality、global split completeness、all-step lifting は主張しない。 |
| 10 / 7.4 | Complexity transfer bridge | `ComplexityTransferWitnessPayload`, `complexityTransferExtensionObstructionWitness`, `complexityTransferExtensionObstructionWitness_classified`, `complexityTransferExtensionObstructionWitnessExists_of_transferredTo`, `complexityTransferExtensionObstructionWitnessExists_of_no_free_elimination`, `complexityTransferExtensionObstructionWitness_multilabel_classified`, `Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_classified`, `generatedComplexityTransferExtensionObstructionWitnessExists_of_transferredTo`, `generatedComplexityTransferExtensionObstructionWitnessExists_of_no_free_elimination`, `generatedComplexityTransferExtensionObstructionWitness_multilabel_classified` | `defined only` / `proved` | selected runtime / semantic / policy transfer witness を generated identity feature extension の `.complexityTransfer` へ分類する bridge。global conservation や empirical cost theorem は主張しない。 |
| 10 / FeatureExtension coverage | Residual coverage gap bridge | `ResidualCoverageGapWitnessPayload`, `residualCoverageGapExtensionObstructionWitness`, `residualCoverageGapExtensionObstructionWitness_classified`, `not_extensionCoverage_of_residualCoverageGapPayload`, `residualCoverageGapExtensionObstructionWitnessExists_of_extensionCoverageWitnessExists`, `residualCoverageGapExtensionObstructionWitnessExists_of_not_extensionCoverage`, `residualCoverageGapExtensionObstructionWitness_multilabel_classified`, `Chapter10ArchitectureExtensionFormula.generatedResidualCoverageGapExtensionObstructionWitness_classified`, `generatedResidualCoverageGapExtensionObstructionWitness_multilabel_classified`, `generatedIdentityExtension_noResidualCoverageGapPayload` | `defined only` / `proved` | selected extension-coverage diagnostic を generated identity feature extension の `.residualCoverageGap` へ分類する bridge。generated identity coverage は residual-gap payload 自体を排除する。static split law failure、runtime / semantic flatness failure は主張しない。 |

### Chapter 10 schematic name correspondence

| 設計書の schematic name | 対応する Lean API | 読み替え |
| --- | --- | --- |
| `ExtensionObstructionClass` | `ExtensionObstructionClass`, `ExtensionObstructionWitness`, `MultiLabelExtensionObstructionWitness`, `Chapter10ArchitectureExtensionFormula.GeneratedExtensionObstructionWitness`, `Chapter10ArchitectureExtensionFormula.GeneratedMultiLabelExtensionObstructionWitness` | selected extension-obstruction witness の bounded classification carrier。generated entrypoint では `GeneratedArchitectureObject` から構成した identity feature extension 上の carrier として読む。 |
| single-label witness embedded into multi-label layer | `ExtensionObstructionWitness.toMultiLabel`, `ExtensionObstructionWitness.toMultiLabel_label_iff`, `ExtensionObstructionWitness.toMultiLabel_classifiesAs`, `Chapter10ArchitectureExtensionFormula.generatedExtensionObstructionWitness_toMultiLabel`, `generatedExtensionObstructionWitness_toMultiLabel_label_iff`, `generatedExtensionObstructionWitness_toMultiLabel_classifiesAs` | payload を保存し、元の single label を generated multi-label witness の label predicate として読む bridge。 |
| selected non-split witness package | `NonSplitExtensionWitnessPackage`, `Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage`, `NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitness`, `Chapter9DiagramFilling.generatedFillingFailureBridge_not_selectedSplitExtension_of_generatedWitness`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension`, `NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension`, `Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists` | soundness と bounded completeness は selected witness coverage / exactness assumptions に相対化する。generated diagram filling failure は generated identity extension の selected non-split witness package に特殊化される。 |
| `ArchitectureExtensionFormula_structural` | `ArchitectureExtensionFormula_structural`, `Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_structural` | selected single-label witness が 7 分類 predicate の少なくとも一つに入ること。generated entrypoint では `GeneratedArchitectureObject` から構成した identity feature extension と coverage premise を使う。 |
| `ArchitectureExtensionFormula_multilabel_structural` | `ArchitectureExtensionFormula_multilabel_structural`, `Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_multilabel_structural` | selected multi-label witness が 7 multi-label predicate の少なくとも一つに入ること。generated entrypoint では `GeneratedArchitectureObject` から構成した identity feature extension と coverage premise を使う。 |
| filling failure classified as extension obstruction | `FillingFailureWitnessPayload`, `Chapter9DiagramFilling.generatedFillingFailureWitnessPayload`, `fillingFailureExtensionObstructionWitness`, `Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness`, `fillingFailureExtensionObstructionWitness_classified`, `Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness_classified`, `fillingFailureExtensionObstructionWitness_multilabel_classified`, `Chapter10ArchitectureExtensionFormula.generatedFillingFailureExtensionObstructionWitness_multilabel_classified` | selected generated diagram non-fillability payload を generated identity feature extension の `.fillingFailure` classification layer に埋め込む。 |
| lifting failure classified as extension obstruction | `LiftingFailureWitnessPayload`, `Chapter9DiagramFilling.generatedSelfFeatureExtension`, `Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData`, `liftingFailureExtensionObstructionWitness`, `Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitness_classified`, `liftingFailureExtensionObstructionWitness_classified`, `liftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage`, `Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage`, `liftingFailureExtensionObstructionWitness_multilabel_classified`, `Chapter10ArchitectureExtensionFormula.generatedSelfLiftingFailureExtensionObstructionWitness_multilabel_classified` | selected generated self-view lifting preservation package の不在を `.liftingFailure` classification layer に埋め込む。 |
| complexity transfer classified as extension obstruction | `ComplexityTransferWitnessPayload`, `complexityTransferExtensionObstructionWitness`, `complexityTransferExtensionObstructionWitness_classified`, `complexityTransferExtensionObstructionWitnessExists_of_no_free_elimination`, `complexityTransferExtensionObstructionWitness_multilabel_classified`, `Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_classified`, `Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitnessExists_of_no_free_elimination`, `Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_multilabel_classified` | selected runtime / semantic / policy transfer witness を generated identity feature extension の `.complexityTransfer` classification layer に埋め込む。 |
| residual coverage gap classified as extension obstruction | `ResidualCoverageGapWitnessPayload`, `residualCoverageGapExtensionObstructionWitness`, `residualCoverageGapExtensionObstructionWitness_classified`, `residualCoverageGapExtensionObstructionWitnessExists_of_not_extensionCoverage`, `residualCoverageGapExtensionObstructionWitness_multilabel_classified`, `Chapter10ArchitectureExtensionFormula.generatedResidualCoverageGapExtensionObstructionWitness_classified`, `Chapter10ArchitectureExtensionFormula.generatedResidualCoverageGapExtensionObstructionWitness_multilabel_classified`, `Chapter10ArchitectureExtensionFormula.generatedIdentityExtension_noResidualCoverageGapPayload` | selected extension-coverage diagnostic を generated identity feature extension の `.residualCoverageGap` classification layer に埋め込む。generated identity feature extension では coverage complete により residual-gap payload は存在しない。 |

Non-conclusions: この統合入口は、第10章の既存 structural classification theorem と
bridge API を索引するだけである。分類の互いに素性、global witness completeness、
global obstruction completeness、universe-wide obstruction coverage、
runtime / semantic universe completeness、
global complexity conservation、empirical cost 改善は結論しない。

## Chapter 11 Analytic Representation Entrypoint

File: `Formal/Arch/Evolution/Chapter11AnalyticRepresentation.lean`

Issue [#481](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/481)
は、第11章 Analytic Representation と tooling report 接続を仕上げる親 Issue である。
Issue [#482](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/482)
は、第11章 Analytic Representation / Canonical Example を docs-facing な
公開入口として整理する作業である。
Issue [#483](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/483)
は、tooling report の `measurement_boundary` と Lean 側の `Option Nat`
axis を接続する第11章向け wrapper を追加する作業である。
Issue [#484](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/484)
は、coupon canonical example を report-facing な analytic snapshot として
`static_hidden_interaction` / `runtime_exposure` / `semantic_curvature` の
3 軸に束ねる作業である。
Issue [#486](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/486)
は、`ArchitectureLawModel.signatureOf` を concrete
`ArchitectureSignatureV1` analytic representation として読む bridge を追加する作業である。
Issue [#488](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/488)
は、coupon の `CouponService -> PaymentAdapter.internalCache` hidden
interaction を、同じ canonical story の selected lifting failure witness として
接続する作業である。
Issue [#485](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/485)
は、AIR / Feature Extension Report / theorem precondition checker が参照する
Lean declaration 名と metadata 境界を整理する作業である。
Issue [#487](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/487)
は、第11章の analytic extension formula を明示前提つき theorem package として
定義する作業である。

`Chapter11AnalyticRepresentation.Candidate` は docs-facing な候補名、
設計書の節番号、代表 Lean declaration 名、schematic name correspondence、
non-conclusion boundary を束ねる軽量 API である。この module は既存 API を
横断 import し、Atom-generated law model を state space とする generated
analytic representation theorem を Chapter 11 entrypoint として公開する。
ただし global flatness、
universe-wide witness completeness、実証的な cost 改善、実コード観測
completeness を新たに主張しない。

| 設計書 | 候補 | 代表 Lean entrypoint | Status | Bounded reading / non-conclusion boundary |
| --- | --- | --- | --- | --- |
| 11 | Analytic Representation | `AnalyticRepresentation`, `AnalyticRepresentation.ZeroPreserving`, `AnalyticRepresentation.ZeroReflecting`, `AnalyticRepresentation.ObstructionPreserving`, `AnalyticRepresentation.ObstructionReflecting`, `AnalyticRepresentation.RecordsNonConclusions`, `AnalyticRepresentation.analyticZero_of_structuralZero`, `AnalyticRepresentation.structuralZero_of_analyticZero`, `AnalyticRepresentation.analyticObstruction_of_structuralObstruction`, `AnalyticRepresentation.structuralObstruction_of_analyticObstruction` | `defined only` / `proved` | preserving direction と reflecting direction を分離する。reflecting direction は coverage / witness completeness / semantic contract coverage に相対化され、analytic value だけから flatness は結論しない。 |
| 11.1 / tooling report metadata | AIR / Feature Extension Report theorem metadata | `ClaimClassification`, `ClaimClassification.IsProved`, `ClaimClassification.IsMeasured`, `ClaimClassification.measured_not_proved`, `ToolingTheoremPackageMetadata`, `ToolingTheoremPackageMetadata.IsMeasuredWitness`, `ToolingTheoremPackageMetadata.IsFormalProvedClaim`, `ToolingTheoremPackageMetadata.measuredWitness_not_formalProvedClaim`, `ToolingTheoremPackageMetadata.not_formalProvedClaim_of_missingPreconditions`, `ToolingTheoremPackageMetadata.RecordsNonConclusions`, `generatedToolingTheoremPackageMetadata`, `generatedToolingTheoremPackageMetadata_formalProvedClaim`, `generatedToolingTheoremPackageMetadata_recordsNonConclusions` | `defined only` / `proved` / Atom-generated acceptance | `claim_level`, `claim_classification`, `measurement_boundary`, required assumptions, coverage / exactness assumptions, missing preconditions, non-conclusions を Lean 側の report metadata schema として束ねる。`MEASURED` witness は `PROVED` formal claim ではなく、missing preconditions がある claim は formal proved claim として読まない。generated law model では generated analytic representation への theorem reference と generated lawfulness / coverage / exactness assumptions から formal proved metadata package を構成する。 |
| 11.1 / 11.2 | ArchitectureSignatureV1 concrete analytic representation | `ArchitectureSignatureAggregateWitness`, `ArchitectureSignatureAnalyticNonConclusions`, `architectureSignatureAnalyticRepresentation`, `architectureSignatureAnalyticRepresentation_nonConclusions`, `architectureSignatureAnalyticRepresentation_zeroPreserving`, `architectureSignatureAnalyticRepresentation_zeroReflecting`, `architectureSignatureAnalyticRepresentation_obstructionPreserving`, `architectureSignatureAnalyticRepresentation_obstructionReflecting`, `AAT.GeneratedArchitectureLawModel.generatedAnalyticRepresentation`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_represent_eq_signatureOfGenerated`, `generatedAnalyticRepresentation_coverageAssumptions`, `generatedAnalyticRepresentation_witnessCompleteness`, `generatedAnalyticRepresentation_semanticContractCoverage`, `generatedAnalyticRepresentation_zeroPreserving`, `generatedAnalyticRepresentation_zeroReflecting`, `generatedAnalyticRepresentation_obstructionPreserving`, `generatedAnalyticRepresentation_obstructionReflecting`, `generatedAnalyticRepresentation_nonConclusions`, `ArchitectureSignature.ArchitectureLawModel.signatureOf`, `ArchitectureSignature.RequiredSignatureAxesZero`, `ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero` | `defined only` / `proved` | `ArchitectureLawModel` から `ArchitectureSignatureV1` への concrete representation に加え、Atom-generated law model 自体を representation state として `signatureOfGenerated` へ写す generated entrypoint を公開する。generated coverage / witness / semantic-contract fields は `True` marker ではなく generated lawfulness equivalence、single selected Signature witness、generated required Signature axes coverage から discharge する。analytic zero は selected required axes の available zero に限り、optional `none`、runtime / empirical axes は zero certificate として扱わない。 |
| 11 | Obstruction Valuation | `ObstructionValuation`, `ObstructionValuation.NoSelectedObstruction`, `ObstructionValuation.ZeroReflectingSum`, `ObstructionValuation.no_obstruction_of_value_zero`, `ObstructionValuation.noSelectedObstruction_of_zeroReflectingSum`, `ObstructionValuation.RecordsNonConclusions`, `AAT.GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation`, `generatedRequiredSignatureObstructionValuation_coverageAssumptions`, `generatedRequiredSignatureObstructionValuation_value_zero`, `generatedRequiredSignatureObstructionValuation_noSelectedObstruction`, `generatedRequiredSignatureObstructionValuation_recordsNonConclusions` | `defined only` / `proved` | selected witness valuation に限る。zero valuation は selected witness absence を与えるが、global `ArchitectureFlat` は結論しない。generated law model では selected generated Signature-axis valuation coverage が generated required Signature axes coverage から discharge され、generated required Signature axes zero から valuation が 0 になる。 |
| 11.1 / analytic extension formula | Analytic Extension Formula theorem package | `AnalyticExtensionFormulaPackage`, `AnalyticExtensionFormulaPackage.FormulaEquation`, `AnalyticExtensionFormulaPackage.RequiredAssumptions`, `AnalyticExtensionFormulaPackage.RecordsNonConclusions`, `AnalyticExtensionFormulaPackage.formula_holds`, `AnalyticExtensionFormulaPackage.requiredAssumptions_of_fields`, `AnalyticExtensionFormulaPackage.records_nonConclusions_iff`, `generatedIdentityAnalyticExtensionFormulaPackage`, `generatedIdentityAnalyticExtensionFormula_representationMapAssumptions`, `generatedIdentityAnalyticExtensionFormula_valuationStructureAssumptions`, `generatedIdentityAnalyticExtensionFormula_decompositionCertificate`, `generatedIdentityAnalyticExtensionFormula_coverageAssumptions`, `generatedIdentityAnalyticExtensionFormula_complexityTransferBoundary`, `generatedIdentityAnalyticExtensionFormula_formula_holds`, `generatedIdentityAnalyticExtensionFormula_requiredAssumptions`, `generatedIdentityAnalyticExtensionFormula_recordsNonConclusions`, `generatedIdentityAnalyticExtensionFormula_obstructionValue_zero`, `ObstructionValuation`, `BoundedComplexityTransferPackage.no_free_elimination_bounded` | `defined only` / `proved` | analytic formula は `formulaHolds` field として package に明示し、representation map、before / after state、feature contribution、interaction / transfer / repair / residual terms、valuation、decomposition certificate、coverage assumptions に相対化する。generated identity specialization は generated law model / generated analytic representation / generated selected obstruction valuation を使い、package assumptions は `True` marker ではなく generated representation coverage、generated valuation coverage、identity decomposition、generated required Signature axes coverage、zero-transfer boundary から discharge する。global conservation law、empirical cost 改善 は結論しない。 |
| 11.3 | Coupon canonical analytic snapshot | `CouponAnalyticSnapshot`, `CouponAnalyticSnapshot.bad`, `CouponAnalyticSnapshot.repaired`, `CouponAnalyticSnapshot.repairedWithMeasuredSemanticCurvature`, `CouponAnalyticSnapshot.bad_staticHiddenInteraction_bridge`, `CouponAnalyticSnapshot.repaired_staticHiddenInteraction_bridge`, `CouponAnalyticSnapshot.runtimeExposure_not_zeroReflectingClaim`, `CouponAnalyticSnapshot.semanticCurvature_unmeasured_not_zeroReflectingClaim`, `CouponAnalyticSnapshot.repairedWithMeasuredSemanticCurvature_roundingOrderValuation_positive`, `CouponAnalyticSnapshot.recordsNonConclusions`, `generatedCouponAnalyticSnapshot_bad_staticHiddenInteraction_bridge` | `defined only` / `proved` / Atom-generated acceptance | coupon report-facing snapshot を 3 軸で束ねる。bad static axis は `some 1`、repaired static axis は `some 0`、runtime exposure は `none`、semantic curvature は `none` または selected measured nonzero として読む。generated law model の semantic flatness と selected static hidden-interaction obstruction は同時に読まれ、runtime / semantic flatness は主張しない。 |
| 11.3 / coupon lifting bridge | Coupon hidden interaction as lifting failure | `CouponHiddenInteractionLiftingBridge.selectedFeatureStep`, `CouponHiddenInteractionLiftingBridge.selectedFeatureStep_liftedEdge_is_hiddenDependency`, `CouponHiddenInteractionLiftingBridge.selectedFeatureStep_not_declaredInterfaceFactor`, `CouponHiddenInteractionLiftingBridge.not_compatibleWithInterface`, `CouponHiddenInteractionLiftingBridge.liftingFailurePayload`, `CouponHiddenInteractionLiftingBridge.liftingFailureWitness`, `CouponHiddenInteractionLiftingBridge.liftingFailureWitness_classified`, `CouponHiddenInteractionLiftingBridge.liftingFailurePayload_refutesCompatibility`, `CouponHiddenInteractionLiftingBridge.hiddenDependency_liftingFailure_bridge`, `generatedCouponHiddenInteraction_liftingFailure_bridge` | `defined only` / `proved` / Atom-generated acceptance | `CouponService -> PaymentAdapter.internalCache` の selected hidden edge を local `.liftingFailure` obstruction witness としても読む。generated law model の semantic flatness は selected lifting failure を消さない。strict section/retraction equality、all feature steps の automatic lifting failure、runtime / semantic flatness は主張しない。 |
| 11 / coupon static axis | Coupon static hidden dependency example | `CouponStaticDependencyExample.goodStaticSplitFeatureExtension`, `CouponStaticDependencyExample.hiddenDependencyWitness`, `CouponStaticDependencyExample.hiddenDependencyWitnessExists`, `CouponStaticDependencyExample.bad_not_selectedStaticSplitFeatureExtension`, `CouponStaticDependencyExample.repairedStaticSplitFeatureExtension`, `CouponStaticDependencyExample.repaired_selectedStaticSplitFeatureExtension`, `generatedCouponStaticExample_bad_not_split`, `generatedCouponStaticExample_repaired_split` | `defined only` / `proved` / Atom-generated acceptance | coupon の selected static hidden dependency witness と repaired static split package。generated boundary acceptance は bad non-split と repaired split を generated semantic flatness と並べて読む。runtime flatness、semantic flatness は主張しない。 |
| 11 / coupon semantic axis | Coupon semantic rounding-order valuation | `CouponDiscountExample.couponDiscountDiagram`, `CouponDiscountExample.roundingOrderResidual`, `CouponDiscountExample.roundingOrderValuation`, `CouponDiscountExample.couponDiscount_roundingOrderResidual_positive`, `CouponDiscountExample.roundingOrderValuation_obstruction`, `CouponDiscountExample.roundingOrderValuation_positive`, `CouponDiscountExample.roundingOrderValuation_recordsNonConclusions`, `generatedCouponSemanticValuation_roundingOrder_positive`, `generatedCouponSemanticValuation_recordsNonConclusions` | `defined only` / `proved` / Atom-generated acceptance | selected coupon / discount rounding-order residual が正であることを示す。generated boundary acceptance は positive valuation と non-conclusions を generated semantic flatness と並べて保持する。未測定 semantic axis の zero 性や ambient semantic coverage は主張しない。 |
| 11 / canonical counterexample | Static-flat semantic-obstruction example | `StaticSemanticCounterexample.canonical_staticFlatWithin`, `StaticSemanticCounterexample.canonical_not_semanticFlatWithin`, `StaticSemanticCounterexample.canonical_not_architectureFlat`, `StaticSemanticCounterexample.staticFlat_with_semanticObstruction`, `StaticSemanticCounterexample.staticFlat_not_architectureFlat`, `generatedStaticSemanticCounterexample_boundary` | `proved` / Atom-generated acceptance | repaired static skeleton が selected-static-flat でも、selected semantic diagram obstruction が残る例。generated boundary acceptance は generated semantic flatness と外部 static-flat semantic obstruction を分離して保持する。実証頻度や source-observation layer は AAT theorem package の外で扱う。 |
| 11 / generated semantic boundary | Generated semantic flatness external-obstruction boundary | `Chapter11AnalyticRepresentation.GeneratedExternalSemanticObstructionBoundary`, `Chapter11AnalyticRepresentation.GeneratedExternalSemanticObstructionBoundary.generated_semanticFlatWithin`, `Chapter11AnalyticRepresentation.GeneratedExternalSemanticObstructionBoundary.external_semantic_obstruction_remains`, `Chapter11AnalyticRepresentation.GeneratedExternalSemanticObstructionBoundary.external_not_architectureFlatWithin`, `Chapter11AnalyticRepresentation.GeneratedExternalSemanticObstructionBoundary.generated_semantic_flatness_does_not_discharge_external`, `Chapter11AnalyticRepresentation.couponGeneratedExternalSemanticObstructionBoundary`, `Chapter11AnalyticRepresentation.coupon_generated_semantic_flatness_does_not_discharge_static_semantic_counterexample`, `Chapter11AnalyticRepresentation.coupon_generated_boundary_staticFlat_with_semanticObstruction` | `defined only` / `proved` | Atom-generated law model の reflexive semantic flatness は generated diagrams に相対化され、外部 selected coupon semantic obstruction を discharge しない。generated obstruction witness が構成されない限り、外部 counterexample は外部 boundary として残る。 |
| 11 / tooling boundary | Measurement boundary for unmeasured axes | `MeasurementBoundary`, `MeasurementBoundary.measuredZero`, `MeasurementBoundary.measuredNonzero`, `MeasurementBoundary.unmeasured`, `MeasurementBoundary.outOfScope`, `AnalyticAxisBoundary`, `AnalyticAxisBoundary.boundaryOfOption`, `AnalyticAxisBoundary.ofSignatureAxis`, `AnalyticAxisBoundary.IsMeasuredZero`, `AnalyticAxisBoundary.IsMeasuredNonzero`, `AnalyticAxisBoundary.IsUnmeasured`, `AnalyticAxisBoundary.SupportsSelectedAnalyticObstruction`, `AnalyticAxisBoundary.CanDischargeZeroReflectingClaim`, `AnalyticAxisBoundary.some_zero_ne_unmeasured`, `AnalyticAxisBoundary.unmeasured_not_availableAndZero`, `AnalyticAxisBoundary.supportsSelectedAnalyticObstruction_of_measuredNonzero`, `AnalyticAxisBoundary.not_canDischargeZeroReflectingClaim_of_unmeasured`, `AnalyticAxisBoundary.signatureAxisMeasuredZero_of_unmeasured`, `AnalyticAxisBoundary.not_signatureAxisAvailableAndZero_of_unmeasured`, `generatedAnalyticAxisBoundary`, `generatedAnalyticAxisBoundary_value_eq_generatedValuation`, `generatedAnalyticAxisBoundary_measuredZero`, `generatedAnalyticAxisBoundary_canDischargeZeroReflectingClaim`, `generatedMeasurementBoundary_unmeasured_remains_not_measuredZero`, `MeasurementBoundary.unmeasured_not_measuredZero`, `ArchitectureClaim.unmeasured_not_measuredZero`, `ArchitectureSignature.v1Schema_unitNoEdge_unmeasured` | `defined only` / `proved` / Atom-generated acceptance | tooling report の `measuredZero`, `measuredNonzero`, `unmeasured`, `outOfScope` と Lean 側の `none` / coverage assumptions の境界を区別する。generated selected axis は generated obstruction valuation zero と coverage assumptions から zero-reflecting claim を discharge できるが、`none` は `some 0` ではない。 |

### Chapter 11 schematic name correspondence

| 設計書の schematic name | 対応する Lean API | 読み替え |
| --- | --- | --- |
| `AnalyticRepresentation State Analytic Witness` | `AnalyticRepresentation`, `AnalyticRepresentation.ZeroPreserving`, `AnalyticRepresentation.ZeroReflecting`, `AnalyticRepresentation.ObstructionPreserving`, `AnalyticRepresentation.ObstructionReflecting` | representation map の preserving direction と reflecting direction を、明示的な coverage / completeness assumptions に相対化して読む。 |
| coverage / witness completeness / semantic contract coverage | `AnalyticRepresentation.coverageAssumptions`, `AnalyticRepresentation.witnessCompleteness`, `AnalyticRepresentation.semanticContractCoverage`, `AnalyticRepresentation.RecordsNonConclusions` | analytic zero / obstruction を structural fact へ戻す前提。tooling output 単独では discharge されない。 |
| `claim_level` / `claim_classification` / `measurement_boundary` | `ClaimLevel`, `ClaimClassification`, `MeasurementBoundary`, `ToolingTheoremPackageMetadata` | tooling report metadata は formal theorem claim、tooling evidence、empirical evidence、hypothesis、measured / unmeasured / out-of-scope boundary を分ける。 |
| `MEASURED` witness is not a `PROVED` claim | `ToolingTheoremPackageMetadata.IsMeasuredWitness`, `ToolingTheoremPackageMetadata.IsFormalProvedClaim`, `ToolingTheoremPackageMetadata.measuredWitness_not_formalProvedClaim`, `ClaimClassification.measured_not_proved` | measured witness は obstruction report の evidence であり、theorem package discharge なしに formal proved claim へ昇格しない。 |
| required assumptions / missing preconditions / non-conclusions | `ToolingTheoremPackageMetadata.requiredAssumptions`, `ToolingTheoremPackageMetadata.coverageAssumptions`, `ToolingTheoremPackageMetadata.exactnessAssumptions`, `ToolingTheoremPackageMetadata.missingPreconditions`, `ToolingTheoremPackageMetadata.not_formalProvedClaim_of_missingPreconditions`, `ToolingTheoremPackageMetadata.RecordsNonConclusions` | theorem precondition checker が registry 化する最小項目。missing preconditions が残る場合、formal proved claim として表示しない。 |
| `ArchitectureLawModel -> ArchitectureSignatureV1` | `architectureSignatureAnalyticRepresentation`, `ArchitectureSignature.ArchitectureLawModel.signatureOf` | Signature v1 を concrete analytic domain とする representation map。 |
| selected required axes zero | `ArchitectureSignature.RequiredSignatureAxesZero`, `architectureSignatureAnalyticRepresentation_zeroPreserving`, `architectureSignatureAnalyticRepresentation_zeroReflecting`, `ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero` | structural zero と analytic zero を既存の selected required-axis theorem package で接続する。 |
| selected required-law obstruction package | `ArchitectureSignatureAggregateWitness`, `architectureSignatureAnalyticRepresentation_obstructionPreserving`, `architectureSignatureAnalyticRepresentation_obstructionReflecting` | selected required-law theorem package の aggregate failure を preserving / reflecting direction で扱う。 |
| optional axis `none` is not analytic zero evidence | `ArchitectureSignatureAnalyticNonConclusions`, `architectureSignatureAnalyticRepresentation_nonConclusions`, `ArchitectureSignature.ArchitectureSignatureV1.not_axisAvailableAndZero_of_axisValue_none` | `none` は unavailable metric であり、selected required-axis の available zero certificate ではない。 |
| `GeneratedArchitectureLawModel -> ArchitectureSignatureV1` | `AAT.GeneratedArchitectureLawModel.generatedAnalyticRepresentation`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_represent_eq_signatureOfGenerated`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_coverageAssumptions`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_witnessCompleteness`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_semanticContractCoverage`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_zeroPreserving`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_zeroReflecting`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_obstructionPreserving`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_obstructionReflecting`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_nonConclusions` | Atom-generated law model を representation state とし、analytic value を `signatureOfGenerated` とする。coverage / witness / semantic-contract fields は generated lawfulness equivalence、single selected Signature witness、generated required Signature axes coverage として導出し、preserving / reflecting direction は generated lawfulness theorem package から得る。 |
| `ObstructionValuation State Witness` | `ObstructionValuation`, `ObstructionValuation.ZeroReflectingSum`, `ObstructionValuation.no_obstruction_of_value_zero`, `ObstructionValuation.noSelectedObstruction_of_zeroReflectingSum`, `AAT.GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation`, `Chapter11AnalyticRepresentation.generatedRequiredSignatureObstructionValuation_coverageAssumptions`, `generatedRequiredSignatureObstructionValuation_value_zero`, `generatedRequiredSignatureObstructionValuation_noSelectedObstruction` | selected witness valuation の zero は selected witness absence に限って読む。generated law model では selected generated Signature-axis valuation coverage が generated required Signature axes coverage から導出され、valuation が generated required axes zero から計算される。 |
| `AnalyticExtensionFormulaPackage` | `AnalyticExtensionFormulaPackage`, `AnalyticExtensionFormulaPackage.FormulaEquation`, `AnalyticExtensionFormulaPackage.formula_holds`, `generatedIdentityAnalyticExtensionFormulaPackage`, `generatedIdentityAnalyticExtensionFormula_formula_holds`, `generatedIdentityAnalyticExtensionFormula_obstructionValue_zero` | 第11章の analytic formula は package field であり、無条件の保存則ではない。generated identity specialization は generated law model state と generated analytic valuation で package を構成する。 |
| representation / valuation / decomposition / coverage assumptions | `AnalyticExtensionFormulaPackage.RequiredAssumptions`, `AnalyticExtensionFormulaPackage.requiredAssumptions_of_fields`, `AnalyticExtensionFormulaPackage.RecordsNonConclusions`, `ObstructionValuation`, `BoundedComplexityTransferPackage.no_free_elimination_bounded` | formula の theorem package 読みは representation map、valuation structure、decomposition certificate、coverage、complexity-transfer boundary に相対化される。 |
| coupon canonical analytic snapshot | `CouponAnalyticSnapshot`, `CouponAnalyticSnapshot.bad`, `CouponAnalyticSnapshot.repaired`, `CouponAnalyticSnapshot.repairedWithMeasuredSemanticCurvature` | `static_hidden_interaction` / `runtime_exposure` / `semantic_curvature` を explicit measurement boundary つきの report-facing axis として読む。 |
| coupon bad `static_hidden_interaction = some 1` | `CouponAnalyticSnapshot.bad_staticHiddenInteraction_bridge`, `CouponStaticDependencyExample.hiddenDependencyWitnessExists`, `CouponStaticDependencyExample.bad_not_selectedStaticSplitFeatureExtension` | bad coupon extension の selected static hidden dependency witness と measured nonzero static axis を接続する。 |
| coupon hidden interaction as selected lifting failure | `CouponHiddenInteractionLiftingBridge.selectedFeatureStep_liftedEdge_is_hiddenDependency`, `CouponHiddenInteractionLiftingBridge.selectedFeatureStep_not_declaredInterfaceFactor`, `CouponHiddenInteractionLiftingBridge.not_compatibleWithInterface`, `CouponHiddenInteractionLiftingBridge.liftingFailurePayload`, `CouponHiddenInteractionLiftingBridge.liftingFailureWitness_classified`, `CouponHiddenInteractionLiftingBridge.hiddenDependency_liftingFailure_bridge` | bad coupon extension の selected hidden edge を、declared interface を通らない local lifting failure payload と `.liftingFailure` 分類 witness へ接続する。 |
| coupon repaired `static_hidden_interaction = some 0` | `CouponAnalyticSnapshot.repaired_staticHiddenInteraction_bridge`, `CouponStaticDependencyExample.repaired_selectedStaticSplitFeatureExtension` | repaired coupon extension では selected static split が回復し、selected static witness absence を measured zero static axis と接続する。 |
| coupon `runtime_exposure = none` / `semantic_curvature = none or measured δ` | `CouponAnalyticSnapshot.runtimeExposure_not_zeroReflectingClaim`, `CouponAnalyticSnapshot.semanticCurvature_unmeasured_not_zeroReflectingClaim`, `CouponAnalyticSnapshot.repairedWithMeasuredSemanticCurvature_roundingOrderValuation_positive` | unmeasured runtime / semantic axis は zero-reflecting claim を discharge しない。semantic curvature は selected rounding-order residual の measured nonzero としても読める。 |
| coupon `static_hidden_interaction = some 1` | `CouponStaticDependencyExample.hiddenDependencyWitness`, `CouponStaticDependencyExample.hiddenDependencyWitnessExists`, `CouponStaticDependencyExample.bad_not_selectedStaticSplitFeatureExtension` | bad coupon extension の selected static hidden dependency witness として読む。 |
| coupon `semantic_curvature = measured nonzero delta` | `CouponDiscountExample.roundingOrderResidual`, `CouponDiscountExample.roundingOrderValuation`, `CouponDiscountExample.couponDiscount_roundingOrderResidual_positive`, `CouponDiscountExample.roundingOrderValuation_positive` | coupon / discount ordering diagram の selected semantic residual が positive であることとして読む。 |
| generated reflexive semantic flatness does not discharge external selected semantic obstruction | `Chapter11AnalyticRepresentation.GeneratedExternalSemanticObstructionBoundary`, `Chapter11AnalyticRepresentation.GeneratedExternalSemanticObstructionBoundary.generated_semanticFlatWithin`, `Chapter11AnalyticRepresentation.GeneratedExternalSemanticObstructionBoundary.external_semantic_obstruction_remains`, `Chapter11AnalyticRepresentation.GeneratedExternalSemanticObstructionBoundary.generated_semantic_flatness_does_not_discharge_external`, `Chapter11AnalyticRepresentation.couponGeneratedExternalSemanticObstructionBoundary`, `Chapter11AnalyticRepresentation.coupon_generated_semantic_flatness_does_not_discharge_static_semantic_counterexample` | Atom-generated law model の semantic flatness は generated reflexive diagram family に相対化される。外部 selected semantic counterexample は別 boundary として残り、generated flatness だけでは discharge されない。 |
| `measuredZero` / `measuredNonzero` / `unmeasured` / `outOfScope` | `MeasurementBoundary`, `AnalyticAxisBoundary`, `AnalyticAxisBoundary.boundaryOfOption`, `MeasurementBoundary.unmeasured_not_measuredZero`, `ArchitectureClaim.unmeasured_not_measuredZero` | report axis の未測定状態は measured zero ではなく、Lean theorem precondition を満たす証拠にもならない。 |
| `Option Nat` axis: `some 0` versus `none` | `AnalyticAxisBoundary.IsMeasuredZero`, `AnalyticAxisBoundary.IsUnmeasured`, `AnalyticAxisBoundary.some_zero_ne_unmeasured`, `AnalyticAxisBoundary.unmeasured_not_availableAndZero`, `AnalyticAxisBoundary.not_canDischargeZeroReflectingClaim_of_unmeasured` | `some 0` は available measured zero、`none` は unmeasured として読む。coverage / witness completeness / semantic contract coverage なしに zero-reflecting claim は出さない。 |
| measured nonzero selected analytic obstruction support | `AnalyticAxisBoundary.IsMeasuredNonzero`, `AnalyticAxisBoundary.SupportsSelectedAnalyticObstruction`, `AnalyticAxisBoundary.supportsSelectedAnalyticObstruction_of_measuredNonzero` | measured nonzero axis は selected analytic obstruction support として読む。global flatness theorem や universe-wide obstruction completeness は主張しない。 |
| `runtime_exposure = none` | `AnalyticAxisBoundary.ofSignatureAxis`, `AnalyticAxisBoundary.ofSignatureAxis_isUnmeasured_of_axisValue_none`, `AnalyticAxisBoundary.signatureAxisMeasuredZero_of_unmeasured`, `AnalyticAxisBoundary.not_signatureAxisAvailableAndZero_of_unmeasured`, `ArchitectureSignature.v1Schema_unitNoEdge_unmeasured` | Signature v1 extension axis の欠落は `none` として残り、weak measured-zero ではあっても available-and-zero ではない。 |

### Chapter 11 tooling theorem metadata API

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Chapter11AnalyticRepresentation.ClaimClassification` | `inductive` | Feature Extension Report の `PROVED` / `MEASURED` / `ASSUMED` / `EMPIRICAL` / `UNMEASURED` / `OUT_OF_SCOPE` 分類を Lean 側で保持する report metadata。 | `defined only` |
| `Chapter11AnalyticRepresentation.ClaimClassification.measured_not_proved` | `theorem` | `MEASURED` は `PROVED` ではない。 | `proved` |
| `Chapter11AnalyticRepresentation.ClaimClassification.unmeasured_not_proved` | `theorem` | `UNMEASURED` は `PROVED` ではない。 | `proved` |
| `Chapter11AnalyticRepresentation.ToolingTheoremPackageMetadata` | `structure` | theorem references、claim level、claim classification、measurement boundary、required assumptions、coverage / exactness assumptions、missing preconditions、non-conclusions を束ねる registry metadata schema。 | `defined only` |
| `Chapter11AnalyticRepresentation.ToolingTheoremPackageMetadata.IsMeasuredWitness` | `def` | tooling-level measured nonzero witness として読める metadata。 | `defined only` |
| `Chapter11AnalyticRepresentation.ToolingTheoremPackageMetadata.IsFormalProvedClaim` | `def` | theorem reference と required / coverage / exactness assumptions があり、missing preconditions がない formal proved claim。 | `defined only` |
| `Chapter11AnalyticRepresentation.ToolingTheoremPackageMetadata.measuredWitness_not_formalProvedClaim` | `theorem` | measured tooling witness は formal proved claim ではない。 | `proved` |
| `Chapter11AnalyticRepresentation.ToolingTheoremPackageMetadata.not_formalProvedClaim_of_missingPreconditions` | `theorem` | missing preconditions がある metadata は formal proved claim ではない。 | `proved` |
| `Chapter11AnalyticRepresentation.ToolingTheoremPackageMetadata.records_nonConclusions_iff` | `theorem` | metadata の non-conclusion field を取り出す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedToolingTheoremPackageMetadata` | `def` | generated analytic representation を formal theorem claim として参照する generated metadata package。 | `defined only` |
| `Chapter11AnalyticRepresentation.generatedToolingTheoremPackageMetadata_formalProvedClaim` | `theorem` | generated metadata package が formal proved claim の preconditions を満たすことを示す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedToolingTheoremPackageMetadata_recordsNonConclusions` | `theorem` | generated metadata package が generated analytic representation の non-conclusion boundary を保持する。 | `proved` |

### Chapter 11 analytic extension formula package API

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Chapter11AnalyticRepresentation.AnalyticExtensionFormulaPackage` | `structure` | representation、obstruction valuation、before / after state、feature、signature value、feature contribution、interaction / transfer / repair / obstruction residual terms、assumptions、`formulaHolds`、non-conclusions を束ねる第11章 formula package。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticExtensionFormulaPackage.FormulaEquation` | `def` | package が主張する analytic formula equation。`after + repair = before + feature + interaction + transfer + residual` の形で repair term を明示する。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticExtensionFormulaPackage.RequiredAssumptions` | `def` | representation map、valuation structure、decomposition certificate、coverage、complexity-transfer boundary assumptions を束ねる前提。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticExtensionFormulaPackage.RecordsNonConclusions` | `def` | formula package が主張しない範囲を記録する predicate。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticExtensionFormulaPackage.formula_holds` | `theorem` | package field の `formulaHolds` から `FormulaEquation` を取り出す。 | `proved` |
| `Chapter11AnalyticRepresentation.AnalyticExtensionFormulaPackage.requiredAssumptions_of_fields` | `theorem` | 各 assumption field から `RequiredAssumptions` を構成する。 | `proved` |
| `Chapter11AnalyticRepresentation.AnalyticExtensionFormulaPackage.records_nonConclusions_iff` | `theorem` | formula package の non-conclusion field を取り出す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormulaPackage` | `def` | generated law model の before / after state、generated analytic representation、generated required-Signature obstruction valuation から identity analytic extension formula package を構成する。 | `defined only` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_representationMapAssumptions` | `theorem` | generated identity formula package の representation assumption が generated analytic coverage と `signatureOfGenerated` representation から discharge されること。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_valuationStructureAssumptions` | `theorem` | generated identity formula package の valuation assumption が generated selected obstruction valuation coverage と all-witness zero valuation から discharge されること。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_decompositionCertificate` | `theorem` | generated identity formula package の decomposition certificate が before = after の identity generated law model から discharge されること。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_coverageAssumptions` | `theorem` | generated identity formula package の coverage assumption が generated required Signature axes coverage から discharge されること。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_complexityTransferBoundary` | `theorem` | generated identity formula package の complexity-transfer boundary が identity state と unit feature の zero-transfer boundary から discharge されること。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_formula_holds` | `theorem` | generated identity formula package が持つ formula equation を取り出す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_requiredAssumptions` | `theorem` | generated identity formula package の明示 assumptions を discharge する。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_recordsNonConclusions` | `theorem` | generated identity formula package の non-conclusion boundary を取り出す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_obstructionValue_zero` | `theorem` | formula package 内の generated selected obstruction valuation が generated law model で 0 になることを示す。 | `proved` |

### Chapter 11 analytic axis boundary API

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary` | `structure` | 1 つの `Option Nat` axis value、report-side `MeasurementBoundary`、coverage / completeness assumptions、non-conclusions を束ねる第11章 wrapper。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.MeasuredNonzeroValue` | `def` | `some (n + 1)` として測定済み非零 axis value であること。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.UnmeasuredValue` | `def` | axis value が `none`、つまり未測定であること。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.boundaryOfOption` | `def` | `none` / `some 0` / `some (n + 1)` を `unmeasured` / `measuredZero` / `measuredNonzero` に読む標準分類。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.ofOption` | `def` | optional metric と coverage assumptions から analytic axis boundary wrapper を作る。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.ofSignatureAxis` | `def` | `ArchitectureSignatureV1.axisValue` を第11章 analytic axis boundary として読む。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.IsMeasuredZero` | `def` | report boundary が measured zero で、値が `AvailableAndZero` であること。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.IsMeasuredNonzero` | `def` | report boundary が measured nonzero で、値が `some (n + 1)` であること。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.IsUnmeasured` | `def` | report boundary が unmeasured で、値が `none` であること。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.SupportsSelectedAnalyticObstruction` | `def` | measured nonzero value を selected analytic obstruction support として読む predicate。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.CanDischargeZeroReflectingClaim` | `def` | available-and-zero と coverage / witness completeness / semantic contract coverage がそろった zero-reflecting claim の前提。 | `defined only` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.some_zero_ne_unmeasured` | `theorem` | `some 0` と `none` は別の report input である。 | `proved` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.unmeasured_ne_some_zero` | `theorem` | `none` と `some 0` は別の report input である。 | `proved` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.unmeasured_not_availableAndZero` | `theorem` | 未測定 `none` は available-and-zero ではない。 | `proved` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.measuredNonzero_not_measuredZero` | `theorem` | measured nonzero value は weak measured-zero ではない。 | `proved` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.supportsSelectedAnalyticObstruction_of_measuredNonzero` | `theorem` | measured nonzero axis から selected analytic obstruction support を得る。 | `proved` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.not_canDischargeZeroReflectingClaim_of_unmeasured` | `theorem` | unmeasured axis は zero-reflecting claim package を discharge できない。 | `proved` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.signatureAxisMeasuredZero_of_unmeasured` | `theorem` | `ArchitectureSignatureV1.axisValue = none` は weak measured-zero に限って成り立つ。 | `proved` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.not_signatureAxisAvailableAndZero_of_unmeasured` | `theorem` | `ArchitectureSignatureV1.axisValue = none` は available-and-zero ではない。 | `proved` |
| `Chapter11AnalyticRepresentation.AnalyticAxisBoundary.ofSignatureAxis_isUnmeasured_of_axisValue_none` | `theorem` | `axisValue = none` の Signature v1 axis は第11章 wrapper 上で unmeasured になる。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticAxisBoundary` | `def` | generated selected obstruction valuation zero を measured-zero analytic axis boundary として読む generated wrapper。 | `defined only` |
| `Chapter11AnalyticRepresentation.generatedAnalyticAxisBoundary_value_eq_generatedValuation` | `theorem` | generated axis boundary の値が generated selected obstruction valuation の値と一致することを示す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticAxisBoundary_measuredZero` | `theorem` | generated axis boundary が measured zero であることを示す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticAxisBoundary_canDischargeZeroReflectingClaim` | `theorem` | generated axis boundary が generated coverage / completeness / semantic contract coverage により zero-reflecting claim preconditions を満たすことを示す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedMeasurementBoundary_unmeasured_remains_not_measuredZero` | `theorem` | generated measurement acceptance でも unmeasured は measured zero ではない境界を保持する。 | `proved` |

### Chapter 11 coupon analytic snapshot API

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Chapter11AnalyticRepresentation.CouponAnalyticSnapshot` | `structure` | coupon canonical example の `staticHiddenInteraction`, `runtimeExposure`, `semanticCurvature` axis と non-conclusions を束ねる report-facing snapshot。 | `defined only` |
| `Chapter11AnalyticRepresentation.CouponAnalyticSnapshot.bad` | `def` | bad coupon extension を、static hidden interaction `some 1`、runtime / semantic unmeasured として読む canonical snapshot。 | `defined only` |
| `Chapter11AnalyticRepresentation.CouponAnalyticSnapshot.repaired` | `def` | repaired coupon extension を、selected static hidden interaction `some 0`、runtime / semantic unmeasured として読む canonical snapshot。 | `defined only` |
| `Chapter11AnalyticRepresentation.CouponAnalyticSnapshot.repairedWithMeasuredSemanticCurvature` | `def` | repaired static skeleton に selected rounding-order semantic residual を measured nonzero として加えた snapshot。 | `defined only` |
| `Chapter11AnalyticRepresentation.CouponAnalyticSnapshot.bad_staticHiddenInteraction_bridge` | `theorem` | bad snapshot の measured nonzero static axis と `CouponStaticDependencyExample.hiddenDependencyWitnessExists` を接続する。 | `proved` |
| `Chapter11AnalyticRepresentation.CouponAnalyticSnapshot.repaired_staticHiddenInteraction_bridge` | `theorem` | repaired snapshot の measured-zero static axis と selected static witness absence を接続する。 | `proved` |
| `Chapter11AnalyticRepresentation.CouponAnalyticSnapshot.runtimeExposure_not_zeroReflectingClaim` | `theorem` | `runtime_exposure = none` は zero-reflecting claim package を discharge しない。 | `proved` |
| `Chapter11AnalyticRepresentation.CouponAnalyticSnapshot.semanticCurvature_unmeasured_not_zeroReflectingClaim` | `theorem` | `semantic_curvature = none` は semantic commuting / zero-reflecting claim として扱えない。 | `proved` |
| `Chapter11AnalyticRepresentation.CouponAnalyticSnapshot.repairedWithMeasuredSemanticCurvature_roundingOrderValuation_positive` | `theorem` | measured semantic curvature snapshot が selected `CouponDiscountExample.roundingOrderValuation_positive` と接続する。 | `proved` |
| `Chapter11AnalyticRepresentation.CouponAnalyticSnapshot.recordsNonConclusions` | `theorem` | snapshot の non-conclusion clause を取り出す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedCouponAnalyticSnapshot_bad_staticHiddenInteraction_bridge` | `theorem` | generated semantic flatness と bad coupon static hidden-interaction obstruction support を同時に保持する。 | `proved` |

### Chapter 11 coupon hidden interaction lifting bridge API

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Chapter11AnalyticRepresentation.CouponHiddenInteractionLiftingBridge.HiddenInteractionEndpoint` | `inductive` | bad coupon hidden interaction を selected operation endpoint view として読むための局所 endpoint 型。 | `defined only` |
| `Chapter11AnalyticRepresentation.CouponHiddenInteractionLiftingBridge.operationExtension` | `def` | `CouponStaticDependencyExample.badGraph` を共有する selected lifting view。static ownership model の置換ではない。 | `defined only` |
| `Chapter11AnalyticRepresentation.CouponHiddenInteractionLiftingBridge.selectedFeatureStep` | `def` | coupon calculation から payment cache read への selected feature step。 | `defined only` |
| `Chapter11AnalyticRepresentation.CouponHiddenInteractionLiftingBridge.selectedFeatureStep_liftedEdge_is_hiddenDependency` | `theorem` | selected step の lifted edge が `BadStaticEdge.hiddenCouponToInternalCache` であることを示す。 | `proved` |
| `Chapter11AnalyticRepresentation.CouponHiddenInteractionLiftingBridge.selectedFeatureStep_not_declaredInterfaceFactor` | `theorem` | selected hidden edge が declared payment interface を通って factor しないことを示す。 | `proved` |
| `Chapter11AnalyticRepresentation.CouponHiddenInteractionLiftingBridge.not_compatibleWithInterface` | `theorem` | selected cache-read step が chosen core invariant に対して `CompatibleWithInterface` を満たさないことを示す。 | `proved` |
| `Chapter11AnalyticRepresentation.CouponHiddenInteractionLiftingBridge.liftingFailurePayload` | `def` | selected hidden interaction を `LiftingFailureWitnessPayload` として包む。 | `defined only` |
| `Chapter11AnalyticRepresentation.CouponHiddenInteractionLiftingBridge.liftingFailureWitness` | `def` | payload を `.liftingFailure` の `ExtensionObstructionWitness` として包む。 | `defined only` |
| `Chapter11AnalyticRepresentation.CouponHiddenInteractionLiftingBridge.liftingFailureWitness_classified` | `theorem` | concrete witness が `ClassifiedAsLiftingFailure` を満たすことを示す。 | `proved` |
| `Chapter11AnalyticRepresentation.CouponHiddenInteractionLiftingBridge.liftingFailurePayload_refutesCompatibility` | `theorem` | payload から selected local compatibility failure を取り出す。 | `proved` |
| `Chapter11AnalyticRepresentation.CouponHiddenInteractionLiftingBridge.hiddenDependency_liftingFailure_bridge` | `theorem` | static hidden dependency witness の存在と classified lifting-failure witness の存在を同じ canonical bridge として束ねる。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedCouponHiddenInteraction_liftingFailure_bridge` | `theorem` | generated semantic flatness と selected hidden-interaction lifting failure を同時に保持する。 | `proved` |

Non-conclusions: この bridge は、一つの selected coupon interaction に限る。
strict section / retraction equality、all feature steps の automatic lifting
failure、runtime flatness、semantic flatness は結論しない。

Non-conclusions: この統合入口は、第11章の representation schema、coupon static /
semantic examples、measurement boundary を索引するだけである。analytic value
単独からの flatness、global witness completeness、runtime / semantic universe
completeness、実証的な cost 改善 は結論しない。

## AAT Part IV Distance / Measure Geometry Entrypoint

Files: `Formal/Arch/Signature/DistanceGeometry.lean`,
`Formal/Arch/Evolution/Part4DistanceMeasureGeometry.lean`,
`Formal/Arch/AAT/GeneratedDistance.lean`,
`Formal/Arch/AAT/GeneratedOperation.lean`,
`Formal/Arch/AAT/GeneratedRepair.lean`,
`Formal/Arch/Signature/Curvature.lean`,
`Formal/Arch/AAT/TheoremClassification.lean`,
`Formal/Arch/Examples/AATPart4DistanceExamples.lean`.

この節は [AAT Part IV: Distance, Measure, and Architecture Geometry](mathematical_theory/part_4_distance_measure_geometry.md)
と [AAT Distance Extension Design](AAT_Distance_Extension_Design.md) に対応する
bounded Lean theorem package の入口である。Part IV 本文は数学理論の source text として保ち、
Lean 実装 status はこの索引と `proof_obligations.md` に分離する。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `DistanceValue`, `DistanceValue.IsMeasuredZero`, `DistanceValue.HasMeasuredDistance`, `DistanceValue.IsUnmeasured`, `DistanceValue.measuredNat?` | `inductive` / `def` | 測定ゼロ、測定値、未測定、利用不可、比較不能、無限を分ける診断距離値。 | `defined only` |
| `DistanceValue.unmeasured_not_zero`, `DistanceValue.unmeasured_not_measuredZero`, `DistanceValue.unmeasured_not_hasMeasuredDistance`, `DistanceValue.unavailable_not_measuredZero`, `DistanceValue.incomparable_not_measuredZero`, `DistanceValue.infinite_not_measuredZero` | `theorem` | 未測定や利用不可などを measured zero と読まない境界を固定する。 | `proved` |
| `DistanceValue.measuredContribution`, `DistanceValue.measuredNat?_zero`, `DistanceValue.measuredNat?_measured`, `DistanceValue.measuredNat?_unmeasured`, `DistanceValue.measuredNat?_unavailable`, `DistanceValue.measuredNat?_incomparable`, `DistanceValue.measuredNat?_infinite`, `DistanceValue.unmeasured_not_measuredNat`, `DistanceValue.unavailable_not_measuredNat`, `DistanceValue.incomparable_not_measuredNat`, `DistanceValue.infinite_not_measuredNat` | `def` / `theorem` | measured payload を `Option Nat` として読み、未測定・利用不可・比較不能・無限が measured payload evidence へ昇格しないことを固定する。 | `defined only` / `proved` |
| `DistanceProfile`, `SelectedDistanceScope`, `BoundedDiagnosticConclusion` | `structure` | 距離 profile、selected measured / unmeasured axes、bounded diagnostic conclusion と non-conclusion boundary を束ねる。 | `defined only` |
| `BoundedDiagnosticConclusion.records_nonConclusions` | `theorem` | diagnostic conclusion が global lawfulness / flatness / unmeasured-zero 非結論を保持することを取り出す。 | `proved` |
| `DetailedBoundedDiagnosticConclusion`, `DetailedBoundedDiagnosticConclusion.MeasuredAxis`, `DetailedBoundedDiagnosticConclusion.UnmeasuredAxis`, `DetailedBoundedDiagnosticConclusion.records_nonConclusions`, `DetailedBoundedDiagnosticConclusion.records_recommendation_boundary` | `structure` / `def` / `theorem` | supporting distance refs、recommended operation refs、recommendation boundary を持つ詳細 diagnostic conclusion。recommended operation は empirical repair correctness theorem ではない。 | `defined only` / `proved` |
| `AxisDistanceReading`, `AxisDistanceReading.MeasuredPayload?`, `AxisDistanceReading.RecordsMeasurementBoundary`, `SignatureDistanceBundle`, `SignatureDistanceBundle.valueAt`, `SignatureDistanceBundle.measuredPayload?`, `SignatureDistanceBundle.measuredSubtotalOf`, `SignatureDistanceBundle.measuredSubtotal`, `SignatureDistanceBundle.RecordsMeasurementBoundary`, `SignatureDistanceBundle.RecordsNonConclusions` | `structure` / `def` | Part IV §4.2 / §9 の axis-wise signature distance bundle。`DistanceValue` の測定状態、selected axes、measured / unmeasured / unavailable / incomparable axes、coverage、aggregation policy、confidence boundary を保持する。 | `defined only` |
| `SignatureDistanceBundle.measuredPayload?_measured`, `SignatureDistanceBundle.unmeasuredAxis_not_measuredPayload`, `SignatureDistanceBundle.unavailableAxis_not_measuredPayload`, `SignatureDistanceBundle.incomparableAxis_not_measuredPayload`, `SignatureDistanceBundle.infiniteAxis_not_measuredPayload`, `SignatureDistanceBundle.nonMeasuredValue_not_measuredPayload`, `SignatureDistanceBundle.measuredSubtotalOf_append`, `SignatureDistanceBundle.unmeasuredAxis_not_measuredZero`, `SignatureDistanceBundle.records_measurementBoundary`, `SignatureDistanceBundle.records_coverage_confidence_boundary`, `SignatureDistanceBundle.records_nonConclusions` | `theorem` | measured subtotal は measured payload だけから読まれ、未測定・利用不可・比較不能・無限 axis を measured zero や measured payload evidence として扱わないことを固定する。append decomposition と coverage / aggregation / confidence / unmeasured policy boundary は bundle-level theorem として読む。 | `proved` |
| `AtomRootDistanceBundle`, `AtomRootDistanceBundle.layoutDistance`, `AtomRootDistanceBundle.layoutDistance_eq_weighted_components`, `GeneratedAtomShapeDistanceBridge`, `GeneratedAtomShapeDistanceBridge.generatedDistance_eq_coordinateMismatch`, `AAT.GeneratedAtomFullShapeCoordinate`, `GeneratedAtomFullShapeCoordinate.fullMismatchCount` | `structure` / `def` / `theorem` | fiber / carrier / valence / semantic-anchor component を選択された root Atom geometry として束ね、generated shape distance と full-shape coordinate mismatch との bridge を与える。semantic ontology calibration は結論しない。 | `defined only` / `proved` |
| `Part4DistanceMeasureGeometry.generatedCarrierShapeDistanceBridge`, `generatedCarrierAtomRootDistanceBundle`, `GeneratedAtomRootGeometryPackage`, `generatedCarrierFullRootDistanceBundle`, `generatedCarrierFullRootGeometryPackage`, `generatedCarrierShapeDistanceBridge_unfolds`, `generatedCarrierShapeDistanceBridge_recordsRootBoundary`, `generatedCarrierRootDistance_layout_eq_generatedCarrierShapeDistance`, `generatedCarrierFullRootGeometryPackage_recordsBoundaries`, `generatedCarrierFullRootGeometryPackage_fullDistance_eq_coordinateMismatch` | `def` / `structure` / `theorem` | `GeneratedArchitectureObject` / `GeneratedCarrier` から root Atom distance bridge、selected layout-distance bundle、full-shape root geometry package を構成し、AtomShape coordinate と selected slot / valence / semantic-anchor coordinate を Part IV root geometry へ接続する。 | `defined only` / `proved` |
| `Part4DistanceMeasureGeometry.GeneratedMappedDistanceEvidence`, `GeneratedMappedDistanceEvidence.records_generated_boundaries`, `generatedOperation_mappedDistanceEvidence`, `generatedOperation_mappedDistanceEvidence_unfolds`, `generatedOperation_mappedDistanceEvidence_targetPrimitive`, `generatedOperation_mappedDistanceEvidence_doesNotCreateAtoms`, `generatedOperation_mappedDistanceEvidence_recordsGeneratedBoundaries`, `generatedOperation_unmapped_target_atom_primitive`, `generatedRepairProblemOperation_mappedDistanceEvidence`, `generatedRepairProblemOperation_mappedDistanceEvidence_unfolds`, `generatedRepairProblemOperation_mappedDistanceEvidence_targetPrimitive`, `generatedRepairProblemOperation_mappedDistanceEvidence_doesNotCreateAtoms`, `generatedRepairProblemOperation_mappedDistanceEvidence_recordsGeneratedBoundaries`, `generatedRepairProblemOperation_unmapped_target_atom_primitive` | `structure` / `def` / `theorem` | `GeneratedOperation` と `GeneratedRepairProblemOperation` の mapped carrier distance を AtomShape coordinate mismatch、target primitive evidence、root AtomAxiomSystem 由来の non-creation boundary、solver completeness / empirical repair quality 非結論境界と一緒に Part IV operation distance evidence として束ねる。 | `defined only` / `proved` |
| `Part4DistanceMeasureGeometry.AtomGeneratedDistanceDiagnosticConclusion`, `AtomGeneratedDistanceDiagnosticConclusion.records_generated_boundaries`, `atomGeneratedDistanceDiagnosticConclusion`, `atomGeneratedDiagnostic_supportingDistances_eq`, `atomGeneratedDiagnostic_recommendedOperations_eq` | `structure` / `def` / `theorem` | Atom-generated distance refs を detailed diagnostic の `supportingDistances` に、generated operation refs を `recommendedOperations` に接続し、recommendation が repair-correctness theorem へ昇格しない境界を保持する。 | `defined only` / `proved` |
| `Part4DistanceMeasureGeometry.GeneratedOperationRepairDiagnosticBridge`, `generatedOperationRepairDiagnosticBridge_recordsGeneratedDiagnosticBoundaries` | `structure` / `theorem` | generated operation distance evidence と generated repair-problem distance evidence を bounded diagnostic recommendation に同時接続する。supporting evidence と recommendation boundary を記録するだけで、repair correctness や solver completeness は結論しない。 | `defined only` / `proved` |
| `AAT.GeneratedArchitectureObject.generatedContext`, `generatedContextCarriers`, `GeneratedContextProjection`, `carrier_in_generatedContext`, `carrier_mem_generatedContextCarriers`, `generatedContext_atom_primitive`, `carrier_compatible_pairs`, `generatedContextProjection_from_object`, `Part4DistanceMeasureGeometry.GeneratedConfigurationContextEvidence`, `generatedConfigurationContextEvidence`, `generatedConfigurationContextEvidence_recordsBoundaries`, `generatedConfigurationContextEvidence_pairCompatible`, `generatedConfigurationDistanceSchema`, `generatedConfigurationDistanceWitness`, `generatedConfigurationDistanceWitness_recordsScope`, `generatedConfigurationDistanceWitness_distance_le`, `generatedConfigurationDistance_samePairDiffers_of_witness`, `generatedContextDistanceSchema`, `generatedContextDistanceSchema_in_selectedContext`, `generatedContextDistanceSchema_recordsFiniteContext` | `def` / `structure` / `theorem` | `GeneratedMolecule` / `GeneratedArchitectureObject` の membership、finite carrier projection、compatible pair evidence から Part IV configuration/context distance bridge を構成し、両 generated context 内の selected pair、selected finite context、supplied path witness に相対化して読む。global shortest-path / context completeness は主張しない。 | `defined only` / `proved` |
| `ConfigurationDistanceSchema`, `ConfigurationDistanceSchema.distance_le_suppliedPathCost`, `ConfigurationDistanceSchema.samePairDistanceDiffers_of_witness`, `ContextDistanceSchema`, `ContextDistanceSchema.records_finiteContext` | `structure` / `def` / `theorem` | configuration-indexed distance と context distance を supplied finite witness / selected finite context に相対化する。global shortest-path / context completeness は主張しない。 | `defined only` / `proved` |
| `SignatureDistanceSchema`, `SignatureDistanceSchema.pathLength`, `SignatureDistanceSchema.endpointDistance`, `SignatureDistanceSchema.hiddenExcursion`, `SignatureDistanceSchema.PathLengthWithinMargin` | `structure` / `def` | selected signature observation 上の自然数距離、有限 path length、endpoint distance、hidden excursion、margin predicate。 | `defined only` |
| `SignatureDistanceSchema.endpointDistance_le_pathLength`, `SignatureDistanceSchema.pathLength_nil`, `SignatureDistanceSchema.pathLength_append`, `SignatureDistanceSchema.margin_stability` | `theorem` | triangle law つき selected schema で endpoint distance が path length 以下であること、path length が nil / append で再利用できること、明示された stepwise preservation と margin 前提の下で trajectory が selected safe region に残ることを示す。 | `proved` |
| `SignatureDistanceSchema.hiddenExcursion_eq_pathLength_sub_endpointDistance`, `endpointDistance_add_hiddenExcursion_eq_pathLength`, `hiddenExcursion_positive_of_endpointDistance_lt_pathLength`, `hiddenExcursion_zero_of_endpointDistance_eq_pathLength` | `theorem` | finite path length と endpoint distance の差として hidden excursion を読み、endpoint-only comparison と total movement を分離する。endpoint と path length が一致する場合は hidden excursion が 0 である。 | `proved` |
| `FiniteRouteCost`, `FiniteFillerCost`, `FiniteHomotopyCost`, `LowerBoundForSelectedCandidates`, `NoRouteBelow`, `NoFillerBelow`, `NoHomotopyBelow`, `SelectedFiniteOptimum`, `SelectedFiniteOptimum.lowerBound_for_selected_candidates`, `SelectedFiniteOptimum.noCandidateBelow_lowerBound` | `structure` / `def` / `theorem` | supplied finite route / filler / homotopy sequence、selected finite candidate universe、lower-bound / selected optimum / named no-below predicate を記録する。global `inf` や all-route completeness は主張しない。 | `defined only` / `proved` |
| `AbstractInfimumInterface`, `AbstractInfimumInterface.lowerBound`, `AbstractInfimumInterface.exists_approximatingWitness`, `AbstractInfimumInterface.NoAbstractCandidateBelow`, `AbstractInfimumInterface.noAbstractCandidateBelow_infimum`, `AbstractInfimumInterface.ofSelectedFiniteOptimum` | `structure` / `def` / `theorem` | finite witness / lower-bound layer の上に、candidate predicate、cost、lower bound、近似 witness、abstract no-below predicate を束ねる abstract infimum interface。computable global optimizer ではない。 | `defined only` / `proved` |
| `DistanceBundle`, `DistanceBundle.RecordsSelectedOverlay`, `DistanceBundle.records_selectedOverlay`, `DistanceAAT`, `DistanceAAT.RecordsOverlayBoundary`, `DistanceAAT.distance_does_not_generate_atoms`, `DistanceAAT.distance_does_not_replace_aatCore` | `structure` / `def` / `theorem` | Part IV の距離束を selected overlay としてまとめ、AAT core を生成・置換しない境界を明示する。 | `defined only` / `proved` |
| `SelectedDistanceToRegion`, `SelectedDistanceToRegion.region_of_distance_zero`, `SelectedDistanceToRegion.distance_zero_of_region` | `structure` / `theorem` | selected lawfulness / flatness region への距離 0 bridge。逆向きは explicit exactness assumptions に相対化される。 | `defined only` / `proved` |
| `MetricOperationAction`, `MetricOperationAction.PreservesDistance`, `NonExpansive`, `Lipschitz`, `MetricOperationAction.SelectedMetricGaloisPackage`, `MetricOperationAction.SelectedMetricGaloisPackage.operation_nonExpansive`, `invariant_stable` | `structure` / `def` / `theorem` | selected finite operation universe で距離保存、非拡大、Lipschitz、invariant stability を読む metric Galois correspondence surface。 | `defined only` / `proved` |
| `OperationCostModel`, `OperationPathCost`, `DistanceToFlatRegion`, `BoundedSideEffectRepair` | `structure` / `abbrev` | selected operation cost、distance-to-flat wrapper、target distance decrease と protected side-effect bound を持つ repair package。 | `defined only` |
| `DistanceToFlatRegion.flat_of_distance_zero`, `BoundedSideEffectRepair.targetDistance_decreases`, `BoundedSideEffectRepair.protectedMovement_within_bound` | `theorem` | 明示された zero reflection / decrease / side-effect bound field を取り出す。 | `proved` |
| `FiniteRepairSequence`, `FiniteRepairSequence.AllStepsDecrease`, `FiniteRepairSequence.allStepsDecrease`, `ContractiveRepairStep`, `ContractiveRepairStep.target_contracts`, `ratio_lt_one` | `structure` / `def` / `theorem` | finite repair sequence と selected contractive repair step を cross-multiplied Nat inequality で記録する。solver completeness や global convergence は主張しない。 | `defined only` / `proved` |
| `FillingCostLowerBound`, `FillingCostLowerBound.observationGap_le_lipschitz_mul_fillingCost`, `Part4DistanceMeasureGeometry.GeneratedFillingCostPackage`, `generatedFillingCostPackage_recordsGeneratedFillingBoundaries`, `generatedFillingCostPackage_observationGap_le`, `generatedFillingCostPackage_no_candidate_filler_within_scale`, `GeneratedCurvatureFillingBridge`, `generatedCurvatureFillingBridge_recordsGeneratedCurvatureFillingBoundaries`, `generatedCurvatureFillingBridge_target_curvature_decreases`, `generatedCurvatureFillingBridge_observationGap_le` | `structure` / `theorem` | `observationGap ≤ L * fillingCost` 形式の bounded lower-bound package、generated diagram / finite filler universe / persistent non-fillability、selected curvature transport を束ねる generated bridge。 | `defined only` / `proved` |
| `QuantitativeHomotopyBound`, `QuantitativeHomotopyBound.observationDistance_le`, `FiniteDehnBound`, `FiniteDehnBound.fillingArea_le_dehnValue`, `PersistentNonFillability`, `PersistentNonFillability.no_candidate_filler_within_scale`, `Part4DistanceMeasureGeometry.GeneratedFiniteHomotopyCost`, `generatedFiniteHomotopyCost_recordsFiniteWitnessUniverse`, `generatedFiniteHomotopyCost_observationDistance_le`, `GeneratedFiniteDehnBound`, `generatedFiniteDehnBound_recordsFiniteUniverse`, `generatedFiniteDehnBound_fillingArea_le_dehnValue` | `structure` / `theorem` | quantitative homotopy bound、finite Dehn-style bound、scale-restricted persistent non-fillability を selected finite candidate universe 上で記録し、generated finite witness universe として読む bridge を持つ。 | `defined only` / `proved` |
| `SelectedCurvatureReading`, `CurvatureTransport`, `CurvatureTransport.target_curvature_decreases`, `CurvatureTransport.transported_curvature_increases` | `structure` / `theorem` | selected measured axes で target curvature decrease と transported-axis increase を分けて読む curvature transport package。 | `defined only` / `proved` |
| `LipschitzRepresentation`, `BiLipschitzRepresentation`, `Part4DistanceMeasureGeometry.GeneratedRepresentationMetricPackage` | `structure` | selected comparability / coverage / witness completeness 前提つきの representation metric と、generated representation / selected obstruction valuation boundary を束ねる metric bridge。 | `defined only` |
| `LipschitzRepresentation.analyticDistance_le_lipschitz`, `BiLipschitzRepresentation.structuralDistance_le_analyticDistance`, `BiLipschitzRepresentation.analyticDistance_le_lipschitz` | `theorem` | comparable な selected state pair で upper / lower Lipschitz 境界を取り出す。 | `proved` |
| `LipschitzRepresentation.analyticDistance_le_of_structuralDistance_le`, `SpectralStabilityPackage`, `SpectralStabilityPackage.spectralDistance_le`, `Part4DistanceMeasureGeometry.generatedRepresentationMetricPackage_recordsGeneratedMetricBoundaries`, `generatedRepresentationMetricPackage_analyticDistance_le`, `generatedRepresentationMetricPackage_spectralDistance_le` | `structure` / `theorem` | structural distance が `ε` 以下なら analytic / spectral distance が `L * ε` 以下になる selected-scope stability surface。generated metric bridge は representation evidence、selected obstruction valuation、zero-preservation / zero-reflection boundary を分けて記録する。 | `defined only` / `proved` |
| `GeneratedDistanceMeasureGeometryFields`, `AATTheoremFamily.generatedDistanceMeasureGeometry`, `AtomGeneratedAATWorld.generated_distance_measure_geometry_fields`, `AATTheoremSuite.generatedDistanceMeasureGeometry`, `AATCompleteFormalizationExamples.generatedComponentTheoremSuite_has_distance_measure_geometry_fields` | `structure` / `def` / `theorem` | Part IV を `AATTheoremSuite` の一級 field として読み、unmeasured-zero 分離、full root geometry、signature measurement boundary、generated operation / repair distance boundary、diagnostic recommendation boundary、curvature / filling bridge、finite homotopy / Dehn witness universe、representation metric bridge を generated world から取り出す。 | `defined only` / `proved` |
| `Part4DistanceMeasureGeometry.Candidate`, `Part4DistanceMeasureGeometry.Candidate.schematicCorrespondences`, `Part4DistanceMeasureGeometry.Candidate.nonConclusionBoundary` | `inductive` / `def` | Part IV の distance foundation、atom/configuration geometry、Atom-generated root / operation / diagnostic / configuration-context connection、signature path geometry、DistanceValue-aware signature aggregation、finite witness / infimum core、distance-to-region、metric Galois、operation/contractive repair、curvature/filling/transport、quantitative homotopy、representation/spectral、docs/classification boundary を横断する docs-facing entrypoint。 | `defined only` |
| `Part4DistanceMeasureGeometry.generatedCarrierShapeDistance_eq_coordinate_mismatchCount`, `Part4DistanceMeasureGeometry.generatedOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount`, `generatedCarrierShapeDistanceBridge_unfolds`, `generatedOperation_mappedDistanceEvidence_unfolds`, `generatedRepairProblemOperation_mappedDistanceEvidence_unfolds` | `theorem` | generated carrier / operation / repair-problem operation distance が AtomShape coordinate mismatch count に展開されることを Part IV 入口から参照する wrapper。 | `proved` |
| `Part4DistanceMeasureGeometry.signatureEndpointDistance_le_pathLength`, `signaturePathLength_nil`, `signaturePathLength_append`, `signatureEndpointDistance_add_hiddenExcursion_eq_pathLength`, `signatureHiddenExcursion_zero_of_endpointDistance_eq_pathLength`, `selectedFiniteOptimum_lowerBound_for_selected_candidates`, `selectedDistanceToRegion_region_of_distance_zero`, `metricGalois_operation_nonExpansive`, `boundedSideEffectRepair_targetDistance_decreases`, `finiteRepairSequence_allStepsDecrease`, `contractiveRepairStep_target_contracts`, `fillingCostLowerBound_observationGap_le`, `generatedFillingCostPackage_observationGap_le`, `generatedCurvatureFillingBridge_target_curvature_decreases`, `quantitativeHomotopyBound_observationDistance_le`, `generatedFiniteHomotopyCost_observationDistance_le`, `finiteDehnBound_fillingArea_le`, `generatedFiniteDehnBound_fillingArea_le_dehnValue`, `curvatureTransport_target_curvature_decreases`, `lipschitzRepresentation_analyticDistance_le`, `generatedRepresentationMetricPackage_analyticDistance_le`, `generatedRepresentationMetricPackage_spectralDistance_le`, `abstractInfimumInterface_lowerBound` | `theorem` | Part IV entrypoint から各 bounded theorem package の代表 accessor / bridge を参照する wrapper。 | `proved` |
| `Part4DistanceMeasureGeometry.signatureDistanceBundle_measuredSubtotal_eq_selectedAxes`, `signatureDistanceBundle_measuredSubtotalOf_append`, `signatureDistanceBundle_measuredPayload_measured`, `signatureDistanceBundle_unmeasuredAxis_not_measuredPayload`, `signatureDistanceBundle_nonMeasuredValue_not_measuredPayload`, `signatureDistanceBundle_unmeasuredAxis_not_measuredZero`, `signatureDistanceBundle_records_measurementBoundary`, `signatureDistanceBundle_records_coverage_confidence_boundary`, `signatureDistanceBundle_records_nonConclusions` | `theorem` | DistanceValue-aware signature aggregation layer を Part IV entrypoint から参照する wrapper。measured subtotal と non-measured axis boundary を finite path geometry から分離して読む。 | `proved` |
| `Part4DistanceMeasureGeometry.distanceBundle_records_selectedOverlay`, `distanceAAT_does_not_generate_atoms`, `distanceAAT_does_not_replace_aatCore`, `atomRootDistance_layoutDistance_eq_weighted_components`, `configurationDistance_le_suppliedPathCost`, `configurationDistance_samePairDiffers_of_witness`, `contextDistance_records_finiteContext`, `selectedFiniteOptimum_noCandidateBelow_lowerBound`, `noRouteBelow_of_selected_lowerBound`, `noFillerBelow_of_selected_lowerBound`, `noHomotopyBelow_of_selected_lowerBound`, `abstractInfimumInterface_noAbstractCandidateBelow_infimum`, `detailedDiagnostic_records_nonConclusions`, `detailedDiagnostic_records_recommendation_boundary` | `theorem` | #1727 系の完全形式化拡張から追加された DistanceAAT overlay、root Atom geometry、configuration/context distance、named lower-bound、詳細 diagnostic conclusion の wrapper。 | `proved` |
| `AATPart4DistanceExamples.*` | `def` / `theorem` | `DistanceValue`、DistanceValue-aware signature aggregation、detailed diagnostic boundary、signature path calculus、bounded repair、selected finite optimum / `NoRouteBelow`、Lipschitz / spectral stability、Atom-generated full root distance bridge、generated operation / repair problem diagnostic bridge、generated filling / homotopy / Dehn package、generated representation metric package、generated configuration/context distance bridge を小さな selected scope で実例化する。 | `defined only` / `proved` |
| `classifyPart4`, `part4Classifications`, `part4_candidates_are_registered` | `def` / `theorem` | theorem-package classification registry に Part IV row を追加し、distance foundation / signature aggregation / path / repair / filling / representation は downstream representation-level、generated root distance / operation distance / diagnostic conclusion / configuration-context membership and projection bridge は Atom-generated source row として分離する。 | `defined only` / `proved` |

Non-conclusions: Part IV distance package は selected scope、finite path、
generated AtomShape coordinate mismatch、root Atom geometry bundle、configuration/context finite witness、
明示 coverage / witness assumptions に相対化される。Atom-generated 接続は
`GeneratedArchitectureObject` / `GeneratedCarrier` / `GeneratedOperation` /
`GeneratedRepairProblemOperation` から Part IV root / operation / diagnostic / configuration-context package への入口であり、
distance が Atom を生成する向きの claim ではない。
距離値だけから lawfulness / flatness を証明せず、未測定 axis を measured zero と読まず、
semantic ontology distance の empirical calibration、solver completeness、global repair
termination、global optimization / route completeness、universal Dehn function completeness、
global witness completeness は結論しない。`inf` 的な数学語彙は finite witness、selected
candidate lower-bound、abstract infimum interface に分解して扱い、computable global optimizer
や all-path / all-filler enumeration は主張しない。

## Architecture Path

File: `Formal/Arch/Evolution/ArchitecturePath.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitecturePath` | `inductive` | `Step : State -> State -> Type` に相対化された有限 architecture evolution path。型 index が start / target state を保持する。 | `defined only` |
| `ArchitecturePath.ApplyPath` | `def` | path を start state に適用した target state を返す endpoint projection。 | `defined only` |
| `ArchitecturePath.length` | `def` | path に含まれる primitive architecture step 数。 | `defined only` |
| `ArchitecturePath.append` | `def` | endpoint が一致する二つの architecture path を連結する。 | `defined only` |
| `ArchitecturePath.append_nil` | `theorem` | 右側に empty path を append しても path は変わらない。 | `proved` |
| `ArchitecturePath.nil_append` | `theorem` | 左側の empty path に path を append すると元の path になる。 | `proved` |
| `ArchitecturePath.append_assoc` | `theorem` | endpoint-indexed architecture path の append が結合的である。 | `proved` |
| `ArchitecturePath.length_append` | `theorem` | append した path の長さは左右 path の長さの和になる。 | `proved` |
| `ArchitecturePath.InvariantHolds` | `def` | state predicate としての architecture invariant が特定 state で成り立つこと。 | `defined only` |
| `ArchitecturePath.StepPreservesInvariant` | `def` | primitive step が invariant を source から target へ保存すること。 | `defined only` |
| `ArchitecturePath.EveryStepPreserves` | `def` | path 上のすべての primitive step が invariant を保存すること。 | `defined only` |
| `ArchitecturePath.everyStepPreserves_append` | `theorem` | append した path 上の stepwise preservation は、左右 segment の preservation に分解できる。 | `proved` |
| `ArchitecturePath.pathPreservesInvariant` | `theorem` | すべての step が invariant を保存するなら、path 全体も start から target へ invariant を保存する。 | `proved` |
| `ArchitecturePath.PathHomotopy` | `inductive` | refl / symm / trans、independent square swap、same external contract replacement、repair fill、cons / right-append context closure で生成される有限 path homotopy relation。 | `defined only` |
| `ArchitecturePath.PathHomotopy.cons_congr` | `theorem` | homotopic な tail path の前に同じ primitive step を付けても homotopy が保たれる。 | `proved` |
| `ArchitecturePath.PathHomotopy.append_left` | `theorem` | homotopic な path pair の左側に同じ prefix path を append しても homotopy が保たれる。 | `proved` |
| `ArchitecturePath.PathHomotopy.append_right` | `theorem` | homotopic な path pair の右側に同じ suffix path を append しても homotopy が保たれる。 | `proved` |
| `ArchitecturePath.PathHomotopy.observation_eq_append` | `theorem` | independent-square / same-contract / repair-fill generator と shared head context が selected path observation を保存する前提から、homotopic path pair の任意 suffix context で observation が一致することを示す。 | `proved` |
| `ArchitecturePath.PathHomotopy.observation_eq` | `theorem` | explicit generator-preservation 前提に相対化して、`PathHomotopy p q` から selected path observation `Obs p = Obs q` を得る。 | `proved` |
| `ArchitecturePath.HomotopyInvariant` | `def` | generated path homotopy の下で安定な invariant。endpoint と state universe は `ArchitecturePath` の index によって明示される。 | `defined only` |
| `ArchitecturePath.architectureHomotopyInvariance` | `theorem` | `HomotopyInvariant` を homotopic path pair に適用する bridge theorem。 | `proved` |

## Architecture Evolution

File: `Formal/Arch/Evolution/ArchitectureEvolution.lean`

Issue [#278](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/278) の対象範囲は、既存
`ArchitecturePath` の endpoint-indexed path を再利用し、その上に evolution-specific な
transition tag、bounded flatness preservation、drift-obstruction reporting、migration plan
schema を置くことである。global 全 obstruction coverage、任意の
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

## SFT SoftwareField / Architecture Projection Boundary

File: `Formal/Arch/Evolution/SFTField.lean`

Issue [#919](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/919) では、
SFT の field state / estimate / architecture projection boundary を最小 Lean record として
追加した。`SoftwareField` は selected field carrier と AAT `ArchitectureObject` への
projection を束ねる wrapper であり、field 自体を architecture object と同一視しない。
coverage、observation、reconstruction、missing evidence、non-conclusion は caller-supplied
boundary accessor として保持し、development field 全体の完全モデル化、trace-grounded
reconstruction completeness、global future trajectory safety は
結論しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `SoftwareField` | `structure` | selected field carrier、architecture projection、observed signature、history / support / policy / constraint / observation / governance / artifact input boundaries、non-conclusions を束ねる SFT field wrapper。 | `defined only` |
| `SoftwareField.arch` | `def` | field から AAT `ArchitectureObject` への selected projection を取り出す。 | `defined only` |
| `SoftwareField.RecordsObservedSignature` | `def` | selected field が observable signature evidence を記録する boundary accessor。 | `defined only` |
| `SoftwareField.RecordsHistoryBoundary` | `def` | history boundary を取り出す。 | `defined only` |
| `SoftwareField.RecordsOperationSupportBoundary` | `def` | operation support boundary を取り出す。 | `defined only` |
| `SoftwareField.RecordsOperationPolicyBoundary` | `def` | operation policy boundary を取り出す。 | `defined only` |
| `SoftwareField.RecordsConstraintEnvironmentBoundary` | `def` | constraint environment boundary を取り出す。 | `defined only` |
| `SoftwareField.RecordsObservationModelBoundary` | `def` | observation model boundary を取り出す。 | `defined only` |
| `SoftwareField.RecordsGovernanceInterventionBoundary` | `def` | governance intervention boundary を取り出す。 | `defined only` |
| `SoftwareField.RecordsExogenousArtifactInputBoundary` | `def` | exogenous artifact input boundary を取り出す。 | `defined only` |
| `SoftwareField.RecordsFieldNotArchitectureObjectBoundary` | `def` | `SoftwareField` を直接 `ArchitectureObject` として読まない boundary を取り出す。 | `defined only` |
| `SoftwareField.RecordsNonConclusions` | `def` | field-level non-conclusions を取り出す。 | `defined only` |
| `SoftwareField.arch_eq_architectureProjection` | `theorem` | `arch` accessor が stored architecture projection と一致すること。 | `proved` |
| `SoftwareFieldEstimate` | `structure` | selected `SoftwareField` と coverage / observation / reconstruction / estimator / missing evidence / non-conclusion boundaries を束ねる partial estimate。 | `defined only` |
| `SoftwareFieldEstimate.selectedField` | `def` | estimate が保持する selected field を取り出す。 | `defined only` |
| `SoftwareFieldEstimate.arch` | `def` | estimate から selected field の architecture projection を取り出す。 | `defined only` |
| `SoftwareFieldEstimate.RecordsCoverageAssumptions` | `def` | coverage assumptions を取り出す。 | `defined only` |
| `SoftwareFieldEstimate.RecordsObservationBoundary` | `def` | observation boundary を取り出す。 | `defined only` |
| `SoftwareFieldEstimate.RecordsReconstructionBoundary` | `def` | reconstruction boundary を取り出す。 | `defined only` |
| `SoftwareFieldEstimate.RecordsEstimatorBoundary` | `def` | estimator/model boundary を取り出す。 | `defined only` |
| `SoftwareFieldEstimate.RecordsMissingEvidence` | `def` | missing evidence を取り出す。 | `defined only` |
| `SoftwareFieldEstimate.RecordsNonConclusions` | `def` | estimate と selected field の non-conclusions を組み合わせて取り出す。 | `defined only` |
| `SoftwareFieldEstimate.arch_eq_field_arch` | `theorem` | estimate の `arch` accessor が selected field の `arch` と一致すること。 | `proved` |
| `ArchitectureProjectionBoundary` | `structure` | `SoftwareFieldEstimate` から selected `ArchitectureObject` への片方向 projection boundary と保存 obligations を束ねる predicate record。 | `defined only` |
| `ArchitectureProjectionBoundary.projection_eq_selected_arch` | `theorem` | projected architecture object が estimate の selected projection と一致することを取り出す。 | `proved` |
| `ArchitectureProjectionBoundary.projection_preserves_coverageAssumptions` | `theorem` | projection boundary が coverage assumptions を保持すること。 | `proved` |
| `ArchitectureProjectionBoundary.projection_preserves_observationBoundary` | `theorem` | projection boundary が observation boundary を保持すること。 | `proved` |
| `ArchitectureProjectionBoundary.projection_preserves_reconstructionBoundary` | `theorem` | projection boundary が reconstruction boundary を保持すること。 | `proved` |
| `ArchitectureProjectionBoundary.projection_preserves_missingEvidence` | `theorem` | projection boundary が missing evidence を保持すること。 | `proved` |
| `ArchitectureProjectionBoundary.projection_records_fieldNotArchitectureObjectBoundary` | `theorem` | field を projected `ArchitectureObject` と同一視しない boundary を保持すること。 | `proved` |
| `ArchitectureProjectionBoundary.projection_records_nonConclusions` | `theorem` | projection-boundary non-conclusions を保持すること。 | `proved` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareField`, `atomGeneratedSignature_generatedSoftwareFieldEstimate`, `atomGeneratedSignature_generatedArchitectureProjectionBoundary`, `atomGeneratedSignature_generatedSoftwareField_projects_to_generated`, `atomGeneratedSignature_generatedSoftwareField_records_nonConclusions` | `def` / `theorem` | Atom-generated component object の generated carrier を SFT field state とし、selected estimate が generated flatness model へ projection することと non-conclusion boundary を保持することを固定する acceptance。 | `defined only` / `proved` |

## SFT ForecastCone Core

File: `Formal/Arch/Evolution/SFTForecastCone.lean`

Issue [#909](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/909) と
Issue [#918](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/918) では、
SFT の `ForecastCone` 最小 core として、set-valued support、selected step relation、
support-witnessed finite `FieldPath`、bounded `ReachableFieldPath`、`ForecastCone`
membership predicate を追加した。`ForecastCone` は finite path-length horizon に相対化した
到達可能 path predicate であり、point prediction、probability、calibration、causal proof、
global safety は結論しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `OperationSupport` | `structure` | field state ごとの selected operation support family と coverage / support boundary / non-conclusions を束ねる schema。 | `defined only` |
| `OperationSupport.Supports` | `def` | selected operation が selected field state の support に含まれること。 | `defined only` |
| `OperationSupport.RecordsCoverageAssumptions` | `def` | support package の coverage assumptions を predicate として取り出す。 | `defined only` |
| `OperationSupport.RecordsSupportBoundary` | `def` | finite sampling、proposal completeness、weights、extractor coverage の boundary を predicate として取り出す。 | `defined only` |
| `OperationSupport.RecordsNonConclusions` | `def` | support package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `StepRelation` | `structure` | selected operation が field transition を realize する relation と coverage / theorem boundary / non-conclusions を束ねる schema。 | `defined only` |
| `StepRelation.Realizes` | `def` | selected operation が source field から target field への selected step を realize すること。 | `defined only` |
| `StepRelation.RecordsCoverageAssumptions` | `def` | step relation の coverage assumptions を predicate として取り出す。 | `defined only` |
| `StepRelation.RecordsTheoremBoundary` | `def` | step relation が相対化される theorem / modeling boundary を predicate として取り出す。 | `defined only` |
| `StepRelation.RecordsNonConclusions` | `def` | step relation の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `SupportedFieldStep` | `structure` | operation witness、support membership、step realization を保持する primitive SFT field step。 | `defined only` |
| `FieldPath` | `abbrev` | `SupportedFieldStep` を primitive step とする finite field path。 | `defined only` |
| `ReachableFieldPath` | `def` | endpoint-indexed `FieldPath` の length が selected horizon 以下であること。 | `defined only` |
| `ForecastCone` | `def` | selected support / step relation / source / horizon に相対化された bounded reachable field path membership predicate。 | `defined only` |
| `ForecastCone.length_le_horizon` | `theorem` | cone membership から finite path-length horizon bound を取り出す accessor theorem。 | `proved` |
| `ForecastCone.nil_mem` | `theorem` | source の zero-length path が zero-horizon cone に属すること。 | `proved` |
| `ForecastCone.monotone_horizon` | `theorem` | horizon を大きくすると cone membership が保存されること。 | `proved` |
| `ForecastCone.of_length_le` | `theorem` | finite path length が horizon 以下であることから cone membership を構成する helper theorem。 | `proved` |
| `ForecastCone.of_length_eq_le` | `theorem` | 明示された path-length equality と horizon bound から cone membership を構成する helper theorem。 | `proved` |
| `ForecastCone.RecordsSupportCoverageAssumptions` | `def` | ForecastCone core が support coverage assumptions を明示 accessor として保持すること。 | `defined only` |
| `ForecastCone.RecordsStepCoverageAssumptions` | `def` | ForecastCone core が step coverage assumptions を明示 accessor として保持すること。 | `defined only` |
| `ForecastCone.RecordsSupportBoundary` | `def` | ForecastCone core が support/model boundary を明示 accessor として保持すること。 | `defined only` |
| `ForecastCone.RecordsStepTheoremBoundary` | `def` | ForecastCone core が step relation の theorem boundary を明示 accessor として保持すること。 | `defined only` |
| `ForecastCone.RecordsHorizonBoundary` | `def` | horizon が finite path-length bound に限られる boundary を predicate として取り出す。 | `defined only` |
| `ForecastCone.RecordsNonConclusions` | `def` | support と step relation の non-conclusions を組み合わせて ForecastCone の non-conclusion boundary を取り出す。 | `defined only` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_sftSupportSafetyPackage`, `atomGeneratedSignature_generatedForecastCone_mem`, `atomGeneratedSignature_generatedForecastCone_length_le_horizon`, `atomGeneratedSignature_generatedForecastCone_monotone_succ` | `def` / `theorem` | Atom-generated support-safety package から generated carrier 上の concrete `FieldPath` と `ForecastCone` witness を構成し、length bound と horizon monotonicity を固定する acceptance。 | `defined only` / `proved` |

## SFT Cone Projection

File: `Formal/Arch/Evolution/SFTConeProjection.lean`

Issue [#910](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/910) と
Issue [#918](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/918) では、
same `Field` / `Operation` 上の set-valued support semantics に限定し、
pointwise support inclusion と step simulation から `ForecastCone` membership が
同じ horizon で射影されることを証明した。これは identity-field projection の Lean core であり、
probability、transition kernel、calibration、global risk reduction、causal correctness、
global safety は結論しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `PointwiseSupportInclusion` | `def` | 各 selected field state で narrower support の operation membership が wider support に含まれること。 | `defined only` |
| `StepSimulation` | `def` | narrower support で supported な primitive transition が、同じ source / operation / target で wider step relation により realize されること。 | `defined only` |
| `SameRelationStepSimulation` | `def` | 同一 `StepRelation` が任意の narrower support に対して自分自身を simulate する helper。 | `defined only` |
| `ForecastConeProjection.projectSupportedFieldStep` | `def` | support inclusion と step simulation に沿って `SupportedFieldStep` を wider model へ写す。 | `defined only` |
| `ForecastConeProjection.projectFieldPath` | `def` | support-witnessed `FieldPath` を構造再帰で wider model へ写す。 | `defined only` |
| `ForecastConeProjection.ProjectedFieldPath` | `def` | wider model の path が narrower path の structural projection であることを表す predicate。 | `defined only` |
| `ForecastConeProjection.projectFieldPath_nil` | `theorem` | zero-length path の projection が zero-length path であること。 | `proved` |
| `ForecastConeProjection.projectFieldPath_cons` | `theorem` | successor path の projection が head step projection と tail path projection に分解されること。 | `proved` |
| `ForecastConeProjection.projectFieldPath_length` | `theorem` | path projection が finite path length を保存すること。 | `proved` |
| `ForecastConeProjection.forecastCone_project_zero` | `theorem` | zero-horizon cone membership が projected zero-length path で保存されること。 | `proved` |
| `ForecastConeProjection.projectedFieldPath_cons` | `theorem` | tail の projected-path relation が successor path へ持ち上がること。 | `proved` |
| `ForecastConeProjection.forecastCone_projects_of_supportInclusion_and_stepSimulation` | `theorem` | pointwise support inclusion と step simulation の下で、narrower cone membership が同じ horizon の wider cone membership へ射影されること。 | `proved` |
| `ForecastConeProjection.exists_projected_forecastCone` | `theorem` | projected path witness と wider cone membership を存在形で取り出す wrapper。 | `proved` |
| `ForecastConeProjection.forecastCone_projects_of_supportInclusion` | `theorem` | 同一 `StepRelation` 上で support inclusion だけから narrower cone membership を wider cone membership へ射影すること。 | `proved` |
| `ForecastConeProjection.exists_projected_forecastCone_of_supportInclusion` | `theorem` | shared step relation の support monotonicity を projected path witness の存在形で取り出す wrapper。 | `proved` |
| `ForecastConeProjection.forecastCone_projects_of_supportInclusion_and_horizon_le` | `theorem` | support inclusion と horizon extension を組み合わせても projected cone membership が保存されること。 | `proved` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_supportSelfInclusion`, `atomGeneratedSignature_generatedForecastCone_projects_self`, `atomGeneratedSignature_exists_projected_generatedForecastCone`, `atomGeneratedSignature_generatedForecastCone_projects_horizon_succ` | `def` / `theorem` | generated support self-inclusion により、generated carrier `ForecastCone` witness が projected path witness と horizon-extension projection を持つことを固定する acceptance。 | `defined only` / `proved` |

## SFT ArtifactAction / Candidate Update

File: `Formal/Arch/Evolution/SFTArtifactAction.lean`

Issue [#917](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/917) では、
artifact-mediated change を、candidate update relation と、それを source とする
action-after-cone family member に分解した。`ArtifactAction` は PRD / Spec / Issue /
AI proposal が複数の candidate update と複数の future cone を生みうることを表す。
`DeterministicArtifactAction` は candidate と applied target が一意な特殊ケースとして
分離している。これは unique future、probability、causal proof、candidate completeness、
market success、human intention を結論しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `CandidateUpdateRelation` | `structure` | source field ごとの candidate update membership と candidate application relation、interpretation / update / non-conclusion boundary を束ねる schema。 | `defined only` |
| `CandidateUpdateRelation.Candidate` | `def` | selected update が selected source field の candidate であること。 | `defined only` |
| `CandidateUpdateRelation.AppliesTo` | `def` | selected update が selected source field から selected target field へ適用されること。 | `defined only` |
| `CandidateUpdateRelation.RecordsInterpretationBoundary` | `def` | interpretation boundary を predicate として取り出す。 | `defined only` |
| `CandidateUpdateRelation.RecordsUpdateBoundary` | `def` | candidate update boundary を predicate として取り出す。 | `defined only` |
| `CandidateUpdateRelation.RecordsNonConclusions` | `def` | candidate update relation の non-conclusion clause を取り出す。 | `defined only` |
| `ArtifactAction` | `structure` | source artifact、candidate update relation、target field component、action / composition / observable / non-conclusion boundary を束ねる schema。 | `defined only` |
| `ArtifactAction.CandidateUpdate` | `def` | artifact action が誘導する candidate update membership。 | `defined only` |
| `ArtifactAction.AppliesTo` | `def` | artifact action が誘導する candidate update application relation。 | `defined only` |
| `ArtifactAction.RecordsTargetFieldComponents` | `def` | target field component assumptions を predicate として取り出す。 | `defined only` |
| `ArtifactAction.RecordsInterpretationBoundary` | `def` | candidate update relation 側の interpretation boundary を取り出す。 | `defined only` |
| `ArtifactAction.RecordsActionBoundary` | `def` | action-level boundary を predicate として取り出す。 | `defined only` |
| `ArtifactAction.RecordsCompositionBoundary` | `def` | composition boundary を predicate として取り出す。 | `defined only` |
| `ArtifactAction.RecordsObservableBoundary` | `def` | observable boundary を predicate として取り出す。 | `defined only` |
| `ArtifactAction.RecordsNonConclusions` | `def` | action-level と candidate-relation の non-conclusions を組み合わせて取り出す。 | `defined only` |
| `DeterministicArtifactAction` | `structure` | candidate update と applied target が source field ごとに一意な artifact action の特殊ケース。 | `defined only` |
| `DeterministicArtifactAction.selected_candidate` | `theorem` | deterministic action の selected update が candidate であることを取り出す accessor theorem。 | `proved` |
| `DeterministicArtifactAction.candidate_eq_selected` | `theorem` | 任意の candidate update が selected deterministic update と一致すること。 | `proved` |
| `DeterministicArtifactAction.target_eq_selected` | `theorem` | 任意の applied candidate target が selected deterministic target と一致すること。 | `proved` |
| `DeterministicArtifactAction.RecordsNonConclusions` | `def` | deterministic special case でも artifact-action non-conclusion boundary を保持すること。 | `defined only` |
| `ForecastConeFamilyAfterAction` | `structure` | candidate update 適用後の selected field を source とする `ForecastCone` family member と family / non-conclusion boundary を束ねる schema。 | `defined only` |
| `ForecastConeFamilyAfterAction.candidate_member` | `theorem` | stored family member から candidate update membership を取り出す accessor theorem。 | `proved` |
| `ForecastConeFamilyAfterAction.applies_to_updatedField` | `theorem` | stored family member から candidate update application witness を取り出す accessor theorem。 | `proved` |
| `ForecastConeFamilyAfterAction.length_le_horizon` | `theorem` | stored cone member から finite horizon bound を取り出す accessor theorem。 | `proved` |
| `ForecastConeFamilyAfterAction.RecordsFamilyBoundary` | `def` | action-after-cone family boundary を predicate として取り出す。 | `defined only` |
| `ForecastConeFamilyAfterAction.RecordsNonConclusions` | `def` | family、artifact action、underlying forecast cone の non-conclusions を組み合わせて取り出す。 | `defined only` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_artifactAction`, `atomGeneratedSignature_deterministicArtifactAction`, `atomGeneratedSignature_forecastConeAfterArtifact`, `atomGeneratedSignature_forecastConeAfterArtifact_candidate_member`, `atomGeneratedSignature_forecastConeAfterArtifact_length_le_horizon` | `def` / `theorem` | Atom-generated SFT input を artifact とし、generated carrier を保つ deterministic update と after-action `ForecastCone` family member を構成する acceptance。 | `defined only` / `proved` |

## SFT OperationPolicy / GovernanceIntervention

File: `Formal/Arch/Evolution/SFTPolicy.lean`

Issue [#921](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/921) では、
operation support に相対化された `OperationPolicy` と、before/after support・policy を束ねる
`GovernanceIntervention` を追加した。restrictive intervention は after-support が
before-support に pointwise inclusion される条件として扱い、既存の same-relation
`ForecastCone` projection theorem に接続する。redirective / instrumenting は policy boundary
と observation enrichment の accessor に留める。これは review、CI、type checking、
architecture rules、AI policy、runtime guard が architecture lawfulness、future trajectory
safety、empirical risk reduction を結論することを意味しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `OperationPolicy` | `structure` | selected support に相対化された operation selection、preorder-like preference、cost / selection / policy / non-conclusion boundary の record。 | `defined only` |
| `OperationPolicy.Selected` | `def` | selected operation が field state で policy により選択されること。 | `defined only` |
| `OperationPolicy.NoHarderThan` | `def` | operation 間の no-harder / no-less-natural / no-less-preferred vocabulary。 | `defined only` |
| `OperationPolicy.RecordsCostBoundary` | `def` | cost-order assumptions を boundary predicate として取り出す。 | `defined only` |
| `OperationPolicy.RecordsSelectionBoundary` | `def` | selection assumptions を boundary predicate として取り出す。 | `defined only` |
| `OperationPolicy.RecordsPolicyBoundary` | `def` | policy/modeling boundary を取り出す。 | `defined only` |
| `OperationPolicy.RecordsNonConclusions` | `def` | policy と underlying support の non-conclusion boundary を組み合わせる。 | `defined only` |
| `SupportTransformation` | `structure` | before/after support と support / policy / non-conclusion boundary を束ねる governance support transformation。 | `defined only` |
| `SupportTransformation.Restricts` | `def` | after-support が before-support に pointwise inclusion される restrictive condition。 | `defined only` |
| `SupportTransformation.RecordsSupportTransformation` | `def` | selected support transformation を boundary predicate として取り出す。 | `defined only` |
| `SupportTransformation.RecordsSupportBoundary` | `def` | support-transformation assumptions を取り出す。 | `defined only` |
| `SupportTransformation.RecordsPolicyBoundary` | `def` | policy-shaping assumptions を取り出す。 | `defined only` |
| `SupportTransformation.RecordsNonConclusions` | `def` | support transformation と before/after support の non-conclusions を組み合わせる。 | `defined only` |
| `GovernanceIntervention` | `structure` | before/after support、before/after policy、support transformation、observation / feedback / escalation / intervention / non-conclusion boundary を束ねる record。 | `defined only` |
| `GovernanceIntervention.RecordsSupportTransformation` | `def` | intervention の selected support transformation を取り出す。 | `defined only` |
| `GovernanceIntervention.RecordsPolicyBeforeBoundary` | `def` | before-policy boundary を取り出す。 | `defined only` |
| `GovernanceIntervention.RecordsPolicyAfterBoundary` | `def` | after-policy boundary を取り出す。 | `defined only` |
| `GovernanceIntervention.RecordsObservationEnrichment` | `def` | observation enrichment boundary を取り出す。 | `defined only` |
| `GovernanceIntervention.RecordsFeedbackUpdate` | `def` | feedback-update assumptions を取り出す。 | `defined only` |
| `GovernanceIntervention.RecordsEscalationBoundary` | `def` | escalation / deferral boundary を取り出す。 | `defined only` |
| `GovernanceIntervention.RecordsInterventionBoundary` | `def` | intervention-level modeling boundary を取り出す。 | `defined only` |
| `GovernanceIntervention.RecordsNonConclusions` | `def` | intervention、support transformation、before/after policy の non-conclusions を組み合わせる。 | `defined only` |
| `GovernanceIntervention.Restrictive` | `def` | after-support を before-support に制限する intervention predicate。 | `defined only` |
| `GovernanceIntervention.Redirective` | `def` | before/after policy と policy-shaping boundary を記録する intervention predicate。 | `defined only` |
| `GovernanceIntervention.Instrumenting` | `def` | observation enrichment を記録する intervention predicate。 | `defined only` |
| `GovernanceIntervention.restrictive_supportInclusion` | `theorem` | restrictive intervention から `PointwiseSupportInclusion supportAfter supportBefore` を取り出す。 | `proved` |
| `GovernanceIntervention.restrictive_forecastCone_projects` | `theorem` | restrictive intervention により after-support cone path が before-support cone へ同じ horizon で射影される。 | `proved` |
| `GovernanceIntervention.redirective_records_policyBoundaries` | `theorem` | redirective intervention から before/after policy boundaries を取り出す。 | `proved` |
| `GovernanceIntervention.instrumenting_records_observationEnrichment` | `theorem` | instrumenting intervention から observation enrichment boundary を取り出す。 | `proved` |
| `GovernanceIntervention.policy_pass_does_not_discharge_lawfulness` | `theorem` | policy pass / governance non-conclusion boundary を accessor として公開する。 | `proved` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedOperationPolicy`, `atomGeneratedSignature_generatedGovernanceIntervention`, `atomGeneratedSignature_generatedGovernance_restrictive`, `atomGeneratedSignature_generatedGovernance_projects_forecastCone`, `atomGeneratedSignature_generatedGovernance_keeps_nonConclusion` | `def` / `theorem` | Atom-generated support package の before/after policy と restrictive governance self-transformation を構成し、generated `ForecastCone` projection と policy-pass non-conclusion を固定する acceptance。 | `defined only` / `proved` |

## SFT Reachability / Stable Region

File: `Formal/Arch/Evolution/SFTReachability.lean`

Issue [#914](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/914) では、
SFT Part IV の set-valued reachability vocabulary として `MayReach`、`MustReach`、
`StableRegion`、`ReachablePreimage` を `ForecastCone` core に接続した。
`MayReach` / `MustReach` は selected support、selected step relation、finite horizon、
selected region に相対化される。`StableRegion` は one-step closure predicate として扱い、
finite `FieldPath` と `ForecastCone` endpoint への accessor theorem を持つ。これは strong
attractor、global basin、probability、transition kernel、recurrence、convergence、
calibrated future prediction、global safety を結論しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `FieldRegion` | `abbrev` | selected field state region を表す predicate alias。 | `defined only` |
| `MayReach` | `def` | selected `ForecastCone` endpoint が target region に入る existential reachability predicate。 | `defined only` |
| `MustReach` | `def` | selected `ForecastCone` のすべての endpoint が target region に入る universal reachability predicate。 | `defined only` |
| `StableRegion` | `def` | selected support と selected step relation に対する one-step closure predicate。 | `defined only` |
| `ReachablePreimage` | `def` | target region への finite-horizon `MayReach` を source 側 predicate として読む vocabulary。 | `defined only` |
| `SFTReachabilityBoundary` | `structure` | probability / attractor / basin / recurrence / non-conclusion boundary を reachability vocabulary と分離して保持する record。 | `defined only` |
| `SFTReachabilityBoundary.RecordsProbabilityBoundary` | `def` | probability / transition-kernel boundary を predicate として取り出す。 | `defined only` |
| `SFTReachabilityBoundary.RecordsAttractorBoundary` | `def` | strong attractor boundary を predicate として取り出す。 | `defined only` |
| `SFTReachabilityBoundary.RecordsBasinBoundary` | `def` | strong basin boundary を predicate として取り出す。 | `defined only` |
| `SFTReachabilityBoundary.RecordsRecurrenceBoundary` | `def` | recurrence assumptions boundary を predicate として取り出す。 | `defined only` |
| `SFTReachabilityBoundary.RecordsNonConclusions` | `def` | reachability boundary と underlying support / relation の non-conclusions を組み合わせる。 | `defined only` |
| `MayReach.of_forecastCone` | `theorem` | 明示的な `ForecastCone` witness と target-region membership から `MayReach` を構成する。 | `proved` |
| `MayReach.nil` | `theorem` | source が target region に入るなら nil path により任意 horizon で `MayReach` する。 | `proved` |
| `MayReach.witness` | `theorem` | `MayReach` から endpoint、field path、cone membership、target-region witness を取り出す。 | `proved` |
| `MustReach.target` | `theorem` | `MustReach` を明示的な cone endpoint に適用して target-region membership を得る。 | `proved` |
| `MustReach.source_mem` | `theorem` | nil path により `MustReach` region が source を含むことを取り出す。 | `proved` |
| `MustReach.mayReach` | `theorem` | `MustReach` から nil witness による `MayReach` を得る。 | `proved` |
| `StableRegion.supportedStep` | `theorem` | stable-region closure を `SupportedFieldStep` に適用する accessor theorem。 | `proved` |
| `StableRegion.fieldPath_target` | `theorem` | stable region が support-witnessed finite `FieldPath` の endpoint まで保存されること。 | `proved` |
| `StableRegion.forecastCone_target` | `theorem` | source が stable region に入るなら selected `ForecastCone` endpoint もその region に入ること。 | `proved` |
| `StableRegion.mustReach` | `theorem` | stable-region closure と source membership から任意 finite horizon の `MustReach` を得る。 | `proved` |
| `ReachablePreimage.iff_mayReach` | `theorem` | `ReachablePreimage` が source 側の `MayReach` predicate と同値であること。 | `proved` |
| `ReachablePreimage.of_mem` | `theorem` | target region membership から reachable preimage membership を nil path で構成する。 | `proved` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFieldRegion`, `atomGeneratedSignature_generatedStableRegion`, `atomGeneratedSignature_generatedMayReach`, `atomGeneratedSignature_generatedMustReach`, `atomGeneratedSignature_generatedReachablePreimage` | `def` / `theorem` | Atom-generated carrier 上の selected region と generated `ForecastCone` witness から `MayReach` / `MustReach` / `StableRegion` / `ReachablePreimage` を構成する acceptance。 | `defined only` / `proved` |

## SFT Support Safety

File: `Formal/Arch/Evolution/SFTSupportSafety.lean`

Issue [#912](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/912) では、
既存の `AttractorEngineeringSupportPackage` / `FiniteOperationKernel` safe-region theorem を
SFT-native support safety package として公開した。finite kernel を `OperationSupport`、
operation semantics を existential transition witness 付き `StepRelation` として読み、
realized supported script から `ForecastCone` witness と bounded safe observed trajectory を
同時に取り出す。accepted-step evidence は record に保持するが、support preservation の導出には
使わない。これは unmeasured axis、empirical review / CI capacity、forecast correctness、
calibration、global safety を結論しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `SFTSupportSafetyPackage` | `structure` | checked support-preservation package と observation / accepted-step / forecast / non-conclusion boundary を束ねる SFT support safety wrapper。 | `defined only` |
| `SFTSupportSafetyPackage.observation` | `def` | underlying package の selected observation を取り出す。 | `defined only` |
| `SFTSupportSafetyPackage.kernel` | `def` | selected finite operation support kernel を取り出す。 | `defined only` |
| `SFTSupportSafetyPackage.semantics` | `def` | selected operation transition semantics を取り出す。 | `defined only` |
| `SFTSupportSafetyPackage.targetRegion` | `def` | theorem-bearing な selected safe region を取り出す。 | `defined only` |
| `SFTSupportSafetyPackage.ForecastTrajectory` | `def` | package observation で finite architecture evolution を読んだ observed forecast trajectory。 | `defined only` |
| `SFTSupportSafetyPackage.RecordsObservationBoundary` | `def` | observation boundary を predicate として取り出す。 | `defined only` |
| `SFTSupportSafetyPackage.RecordsAcceptedStepBoundary` | `def` | accepted-step evidence が support preservation の代替ではない boundary を取り出す。 | `defined only` |
| `SFTSupportSafetyPackage.RecordsForecastBoundary` | `def` | support safety が forecast correctness / calibration ではない boundary を取り出す。 | `defined only` |
| `SFTSupportSafetyPackage.RecordsNonConclusions` | `def` | package と underlying Attractor Engineering package の non-conclusions / measurement boundary を組み合わせて取り出す。 | `defined only` |
| `SFTSupportSafetyPackage.operationSupport` | `def` | finite kernel を SFT `OperationSupport` として読む vocabulary bridge。 | `defined only` |
| `SFTSupportSafetyPackage.stepRelation` | `def` | operation semantics を primitive transition witness 付き SFT `StepRelation` として読む vocabulary bridge。 | `defined only` |
| `SFTSupportSafetyPackage.supportedArchitectureStep` | `def` | supported operation が realize する primitive architecture transition を `SupportedFieldStep` へ変換する。 | `defined only` |
| `SFTSupportSafetyPackage.fieldPathOfSupportedScript` | `def` | realized script が finite support だけを使う証拠から SFT `FieldPath` を構成する。 | `defined only` |
| `SFTSupportSafetyPackage.fieldPathOfSupportedScript_length` | `theorem` | script-to-field-path conversion が operation count を保存すること。 | `proved` |
| `SFTSupportSafetyPackage.AcceptedSupportedTrajectory` | `structure` | script / plan / start-safe / realization / support-use / accepted evidence を束ねる selected trajectory record。 | `defined only` |
| `SFTSupportSafetyPackage.AcceptedSupportedTrajectory.fieldPath` | `def` | selected trajectory から induced SFT field path を取り出す。 | `defined only` |
| `SFTSupportSafetyPackage.AcceptedSupportedTrajectory.fieldPath_length` | `theorem` | induced field path の length が script operation count と一致すること。 | `proved` |
| `SFTSupportSafetyPackage.AcceptedSupportedTrajectory.mem_forecastCone` | `theorem` | accepted supported trajectory が script-length horizon の `ForecastCone` に入ること。 | `proved` |
| `SFTSupportSafetyPackage.AcceptedSupportedTrajectory.supportSafety_preserves_forecastTrajectory` | `theorem` | stored support-preservation premise により selected forecast trajectory が target safe region 内に留まること。 | `proved` |
| `SFTSupportSafetyPackage.AcceptedSupportedTrajectory.forecastCone_and_supportSafety` | `theorem` | ForecastCone witness と support safety conclusion を同時に返す wrapper。 | `proved` |
| `SFTSupportSafetyPackage.AcceptedSupportedTrajectory.acceptedEvidence` | `theorem` | accepted evidence を accessor として公開し、support-preservation premise と分離する。 | `proved` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_sftSupportSafetyPackage`, `atomGeneratedSignature_acceptedSupportedTrajectory`, `atomGeneratedSignature_supportSafety_forecastCone_and_safety` | `def` / `theorem` | Atom-generated component object の generated carrier を SFT state とし、generated identity support operation / finite supported script / accepted trajectory から `SFTSupportSafetyPackage.AcceptedSupportedTrajectory.forecastCone_and_supportSafety` を発火させる acceptance。 | `defined only` / `proved` |

## SFT FieldUpdate

File: `Formal/Arch/Evolution/SFTFieldUpdate.lean`

Issue [#908](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/908) では、
SFT の closed-loop feedback を、`ForecastCone` witness を含む prior forecast record、
observed outcome、posterior field record、selected update soundness predicate に分解した。
`UpdateSound` は observed feedback classes が posterior record に保存されることだけを述べる。
これは forecast accuracy improvement、empirical calibration、governance effectiveness、
operational feedback artifact の source-observation layer は AAT theorem package の外で扱う。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `ForecastRecord` | `structure` | selected `ForecastCone` witness と forecast / non-conclusion boundary を束ねる prior forecast record。 | `defined only` |
| `ForecastRecord.length_le_horizon` | `theorem` | stored cone witness から finite horizon bound を取り出す accessor theorem。 | `proved` |
| `ForecastRecord.RecordsForecastBoundary` | `def` | forecast/model boundary を predicate として取り出す。 | `defined only` |
| `ForecastRecord.RecordsNonConclusions` | `def` | forecast record の non-conclusion boundary を取り出す。 | `defined only` |
| `ObservedOutcome` | `structure` | observed field と forecast error / missing evidence / unexpected witness / policy drift / observation boundary / non-conclusions を保持する feedback record。 | `defined only` |
| `ObservedOutcome.RecordsObservationBoundary` | `def` | observed outcome の observation boundary を取り出す。 | `defined only` |
| `ObservedOutcome.RecordsNonConclusions` | `def` | observed outcome の non-conclusion boundary を取り出す。 | `defined only` |
| `PosteriorFieldRecord` | `structure` | posterior field と保存された feedback classes、update boundary、calibration boundary、non-conclusions を保持する record。 | `defined only` |
| `PosteriorFieldRecord.RecordsUpdateBoundary` | `def` | posterior record の update boundary を取り出す。 | `defined only` |
| `PosteriorFieldRecord.RecordsCalibrationBoundary` | `def` | preserved feedback が accuracy-improvement theorem ではない calibration boundary を取り出す。 | `defined only` |
| `PosteriorFieldRecord.RecordsNonConclusions` | `def` | posterior record の non-conclusion boundary を取り出す。 | `defined only` |
| `FieldUpdate` | `structure` | forecast record、observed outcome、posterior record、update-level boundary を束ねる selected closed-loop update。 | `defined only` |
| `FieldUpdate.RecordsUpdateBoundary` | `def` | update-level boundary を predicate として取り出す。 | `defined only` |
| `FieldUpdate.RecordsNonConclusions` | `def` | forecast / observation / posterior / update の non-conclusion boundaries を組み合わせて取り出す。 | `defined only` |
| `FieldUpdate.UpdateSound` | `structure` | observed feedback classes が posterior record に保存され、update / calibration / non-conclusion boundaries が記録されていることを表す predicate。 | `defined only` |
| `FieldUpdate.UpdateSound.fieldUpdate_preserves_forecastError_and_missingEvidence` | `theorem` | sound update rule から forecast error と missing evidence の posterior preservation を取り出す。 | `proved` |
| `FieldUpdate.UpdateSound.fieldUpdate_preserves_unexpectedWitness_and_policyDrift` | `theorem` | sound update rule から unexpected witness と policy drift の posterior preservation を取り出す。 | `proved` |
| `FieldUpdate.UpdateSound.fieldUpdate_preserves_nonConclusions` | `theorem` | observed non-conclusion boundary が posterior record に保存されることを取り出す。 | `proved` |
| `FieldUpdate.UpdateSound.fieldUpdate_records_calibrationBoundary` | `theorem` | update package が calibration boundary を保持し、accuracy improvement を結論しないことを accessor として公開する。 | `proved` |
| `FieldUpdate.UpdateSound.fieldUpdate_records_nonConclusions` | `theorem` | update package 全体の non-conclusion boundary を取り出す。 | `proved` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastRecord`, `atomGeneratedSignature_generatedFieldUpdate`, `atomGeneratedSignature_generatedFieldUpdate_sound`, `atomGeneratedSignature_generatedFieldUpdate_records_calibration`, `atomGeneratedSignature_generatedFieldUpdate_records_nonConclusions` | `def` / `theorem` | Atom-generated `ForecastCone` witness を prior forecast record とし、generated carrier 上の observed / posterior record から `FieldUpdate.UpdateSound`、calibration boundary、non-conclusions を固定する acceptance。 | `defined only` / `proved` |

## SFT ConsequenceEnvelope

File: `Formal/Arch/Evolution/SFTEnvelope.lean`

Issue [#911](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/911) では、
selected `ForecastRecord` family から reviewer-facing `ConsequenceEnvelope` への
loss-aware report projection を record-level boundary theorem package として追加した。
これは envelope が selected cone family、missing / theorem boundary、unknown remainder、
forecast non-conclusions を保存して読めることに限られ、cone family の一意復元、
probability、causal proof、point prediction、calibrated forecast correctness、tooling artifact
の Lean theorem witness 化は結論しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `ConeFamily` | `structure` | nonempty selected `ForecastRecord` list と family boundary / unknown remainder / non-conclusions を束ねる cone family record。 | `defined only` |
| `ConeFamily.RecordsForecastListNonConclusions` | `def` | selected forecast record list の各要素が non-conclusion boundary を保持すること。 | `defined only` |
| `ConeFamily.RecordsNonempty` | `def` | selected cone family が空でないことを predicate として取り出す。 | `defined only` |
| `ConeFamily.RecordsForecastNonConclusions` | `def` | selected cone family 内の forecast non-conclusions を取り出す。 | `defined only` |
| `ConeFamily.RecordsFamilyBoundary` | `def` | selected cone-family modeling boundary を取り出す。 | `defined only` |
| `ConeFamily.RecordsUnknownRemainder` | `def` | unknown / unmodeled remainder を取り出す。 | `defined only` |
| `ConeFamily.RecordsNonConclusions` | `def` | family と per-forecast non-conclusion boundaries を組み合わせて取り出す。 | `defined only` |
| `ConeFamily.records_nonempty` | `theorem` | family record から nonempty witness を取り出す accessor theorem。 | `proved` |
| `ObservationBoundary` | `structure` | path classes、affected regions、comparable axes、missing / theorem boundary、unknown remainder、non-conclusions を束ねる observation boundary。 | `defined only` |
| `ObservationBoundary.RecordsPathClassesVisible` | `def` | projection で visible な path classes を取り出す。 | `defined only` |
| `ObservationBoundary.RecordsAffectedRegionsVisible` | `def` | projection で visible な affected regions を取り出す。 | `defined only` |
| `ObservationBoundary.RecordsComparableAxes` | `def` | selected measurement universe で comparable な axes を取り出す。 | `defined only` |
| `ObservationBoundary.RecordsMissingBoundary` | `def` | missing boundary items を取り出す。 | `defined only` |
| `ObservationBoundary.RecordsTheoremBoundary` | `def` | theorem / modeling boundary items を取り出す。 | `defined only` |
| `ObservationBoundary.RecordsUnknownRemainder` | `def` | unknown / unmodeled remainder を取り出す。 | `defined only` |
| `ObservationBoundary.RecordsNonConclusions` | `def` | observation-boundary non-conclusions を取り出す。 | `defined only` |
| `ConsequenceEnvelope` | `structure` | reviewer-facing envelope report と projection / forecast / non-conclusion boundaries を束ねる projection target。 | `defined only` |
| `ConsequenceEnvelope.RecordsPathClasses` | `def` | envelope の path classes を取り出す。 | `defined only` |
| `ConsequenceEnvelope.RecordsAffectedRegions` | `def` | envelope の affected regions を取り出す。 | `defined only` |
| `ConsequenceEnvelope.RecordsComparableAxes` | `def` | envelope の comparable axes を取り出す。 | `defined only` |
| `ConsequenceEnvelope.RecordsMissingBoundary` | `def` | envelope の missing boundary items を取り出す。 | `defined only` |
| `ConsequenceEnvelope.RecordsTheoremBoundary` | `def` | envelope の theorem / modeling boundary items を取り出す。 | `defined only` |
| `ConsequenceEnvelope.RecordsUnknownRemainder` | `def` | envelope の unknown / unmodeled remainder を取り出す。 | `defined only` |
| `ConsequenceEnvelope.RecordsForecastBoundary` | `def` | envelope の forecast/model boundary を取り出す。 | `defined only` |
| `ConsequenceEnvelope.RecordsProjectionBoundary` | `def` | envelope の report projection boundary を取り出す。 | `defined only` |
| `ConsequenceEnvelope.RecordsNonConclusions` | `def` | envelope-level non-conclusions を取り出す。 | `defined only` |
| `EnvelopeProjection` | `structure` | selected cone family と observation boundary から envelope への loss-aware projection relation。 | `defined only` |
| `EnvelopeProjection.envelope_records_selectedConeCount` | `theorem` | envelope が projected cone count を family record length として保持すること。 | `proved` |
| `EnvelopeProjection.envelope_preserves_missingBoundary` | `theorem` | observation boundary の missing boundary items が envelope に保存されること。 | `proved` |
| `EnvelopeProjection.envelope_preserves_theoremBoundary` | `theorem` | theorem / modeling boundary items が envelope に保存されること。 | `proved` |
| `EnvelopeProjection.envelope_preserves_unknownRemainder` | `theorem` | selected cone family の unknown remainder が envelope に保存されること。 | `proved` |
| `EnvelopeProjection.envelope_preserves_nonConclusions` | `theorem` | selected cone family の forecast non-conclusions が envelope に保存されること。 | `proved` |
| `EnvelopeProjection.envelope_does_not_strengthen_forecast_claim` | `theorem` | envelope が forecast / projection / non-conclusion boundaries を保持し、forecast claim を強めないことを accessor として公開する。 | `proved` |
| `AATCorePremisedConsequenceEnvelope` | `structure` | `AATCore` local algebra、`AATCoreTransition`、selected cone family、observation boundary、reviewer-facing envelope を束ねる Atom 公理系 root の SFT consequence package。 | `defined only` |
| `AATCorePremisedConsequenceEnvelope.forecast_cone`, `reads_aatcore_local_algebra`, `records_transition_boundaries`, `transition_does_not_create_atoms`, `aatcore_premise_does_not_prove_forecast_correctness`, `records_envelope_boundaries` | `theorem` | `AATCore` transition と envelope boundary を取り出し、transition / delta が atom existence を生成せず、AATCore premise が forecast correctness を結論しないことを読む。 | `proved` |
| `GeneratedAATConsequenceEnvelope` | `structure` | `GeneratedSFTInput` から作った local algebra と `GeneratedArchSigAATCoreTransition` の transition を使い、generic `AATCorePremisedConsequenceEnvelope` を Atom-generated input に特殊化する consequence envelope。 | `defined only` |
| `GeneratedAATConsequenceEnvelope.to_premisedEnvelope`, `theorem_status_from_generated`, `reads_generated_aat`, `records_transition_boundaries`, `forecast_correctness_remains_boundary`, `records_envelope_boundaries` | `theorem` | generated theorem status、generated AAT reading、transition / FieldSig boundary、forecast boundary、envelope boundary を accessor として取り出す。forecast correctness は結論しない。 | `proved` |

## SFT / AAT Theorem Status Interface Boundary

File: `Formal/Arch/Evolution/SFTInterfaceBoundary.lean`

Issue [#922](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/922) では、
AAT theorem status を SFT forecast status の local premise として読む境界を
record-level theorem package として追加した。これは AAT theorem evidence、measured-zero
evidence、unmeasured-axis boundary、tool/report boundary、forecast boundary を分離し、
AAT theorem status が trajectory safety、unmeasured-axis safety、empirical forecast status、
calibrated forecast correctness、global future safety へ自動昇格しないことを accessor として
公開する。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `AATTheoremStatus` | `structure` | theorem package、measured-zero evidence、theorem boundary、unmeasured-axis boundary、tooling boundary、non-conclusions を束ねる AAT 側 status record。 | `defined only` |
| `AATTheoremStatus.RecordsTheoremPackage` | `def` | selected AAT theorem package evidence を取り出す。 | `defined only` |
| `AATTheoremStatus.RecordsMeasuredZeroEvidence` | `def` | selected measured-zero evidence を取り出す。 | `defined only` |
| `AATTheoremStatus.RecordsTheoremBoundary` | `def` | AAT theorem boundary を取り出す。 | `defined only` |
| `AATTheoremStatus.RecordsUnmeasuredAxisBoundary` | `def` | unmeasured axis boundary を取り出す。 | `defined only` |
| `AATTheoremStatus.RecordsToolingBoundary` | `def` | tooling/report boundary を取り出す。 | `defined only` |
| `AATTheoremStatus.RecordsNonConclusions` | `def` | AAT-level non-conclusions を取り出す。 | `defined only` |
| `AATTheoremStatus.ofArchitectureZeroCurvatureTheoremPackage` | `def` | 既存の `ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage` を SFT interface 用の AAT theorem-status record として包む。 | `defined only` |
| `AATTheoremStatus.records_theoremPackage_of_architectureZeroCurvatureTheoremPackage` | `theorem` | zero-curvature theorem package constructor から stored theorem package を取り出す。 | `proved` |
| `SFTForecastStatus` | `structure` | local premise、support boundary、trajectory safety boundary、measured / unmeasured axis boundary、theorem / tooling / forecast boundary、non-conclusions を束ねる SFT 側 status record。 | `defined only` |
| `SFTForecastStatus.RecordsLocalPremise` | `def` | SFT forecast status に local premise が残ることを取り出す。 | `defined only` |
| `SFTForecastStatus.RecordsSupportBoundary` | `def` | support/model boundary を取り出す。 | `defined only` |
| `SFTForecastStatus.RecordsTrajectorySafetyBoundary` | `def` | trajectory safety boundary を取り出す。 | `defined only` |
| `SFTForecastStatus.RecordsMeasuredAxisBoundary` | `def` | measured-axis boundary を取り出す。 | `defined only` |
| `SFTForecastStatus.RecordsUnmeasuredAxisBoundary` | `def` | unmeasured-axis safety boundary を取り出す。 | `defined only` |
| `SFTForecastStatus.RecordsTheoremBoundary` | `def` | theorem/modeling boundary を取り出す。 | `defined only` |
| `SFTForecastStatus.RecordsToolingBoundary` | `def` | tooling/report boundary を取り出す。 | `defined only` |
| `SFTForecastStatus.RecordsForecastBoundary` | `def` | forecast correctness / calibration boundary を取り出す。 | `defined only` |
| `SFTForecastStatus.RecordsNonConclusions` | `def` | SFT forecast non-conclusions を取り出す。 | `defined only` |
| `AATToSFTInterfaceBoundary` | `structure` | AAT theorem status から SFT forecast status への one-way local-premise reading と boundary preservation を束ねる relation。 | `defined only` |
| `AATToSFTInterfaceBoundary.aat_theorem_status_as_local_premise` | `theorem` | AAT theorem package evidence を SFT local premise として読む。 | `proved` |
| `AATToSFTInterfaceBoundary.aat_lawfulness_alone_does_not_discharge_trajectory_safety_boundary` | `theorem` | AAT theorem status だけでは SFT trajectory safety boundary が消えないことを accessor として公開する。 | `proved` |
| `AATToSFTInterfaceBoundary.measured_zero_does_not_discharge_unmeasured_axis_safety_boundary` | `theorem` | measured-zero evidence が unmeasured-axis safety を discharge しない boundary を保存する。 | `proved` |
| `AATToSFTInterfaceBoundary.tool_report_output_does_not_strengthen_aat_theorem_status` | `theorem` | tool/report output が AAT theorem status を強めず、SFT tooling boundary として残ること。 | `proved` |
| `AATToSFTInterfaceBoundary.preserves_theorem_boundary` | `theorem` | AAT theorem boundary が SFT theorem boundary に保存されること。 | `proved` |
| `AATToSFTInterfaceBoundary.preserves_measured_axis_boundary` | `theorem` | measured-axis evidence が measured-axis boundary として保存されること。 | `proved` |
| `AATToSFTInterfaceBoundary.forecast_status_records_forecast_boundary` | `theorem` | forecast correctness / calibration boundary が SFT forecast status に残ること。 | `proved` |
| `AATToSFTInterfaceBoundary.interface_preserves_nonConclusions` | `theorem` | AAT non-conclusions が SFT forecast non-conclusions として保存されること。 | `proved` |

Atom-generated SFT handoff は `Formal/Arch/AAT/GeneratedSFT.lean` に置く。
`GeneratedSFTInput.theoremStatus` は caller-supplied な任意 status ではなく、
`GeneratedArchitectureLawModel.generatedAATTheoremStatusForSFT` から計算される。
`GeneratedSFTInput.reads_generated_aat_as_sft_local_premise` は、その generated theorem
status を `AATToSFTInterfaceBoundary` 経由で SFT local premise として読む。

## ArchSig-SFT Analysis / Report Boundary

File: `Formal/Arch/Evolution/SFTArchSigBoundary.lean`

Issue [#915](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/915) では、
ArchSig analysis / report state を SFT estimate / forecast status へ読む片方向境界を Lean 側に追加した。
`ArchSigSFTReport` は selected `SoftwareFieldEstimate`、action class candidates、
target regions、candidate operation families、comparable signature axes、missing invariants、
unmeasured axes、theorem boundary、forecast boundary、report boundary、non-conclusions を
保持する。LLM-native tooling 側では FieldSig handoff は `archsig-analysis-packet-v0` を
bounded local AAT state として受け取り、raw ArchMap observation を forecast truth へ
昇格しない。Lean 側ではまだ analysis / report boundary data として読む段階であり、
`ArchSigSFTReportEstimateBoundary` は、report output が estimate boundary と
SFT forecast boundary に保存されることを accessor theorem として公開する。

Non-conclusions: ArchSig report は ground-truth architecture object、AAT theorem package、
calibrated forecast correctness、global future safety、certified
universal atom truth を結論しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `ArchSigSFTReport` | `structure` | selected `SoftwareFieldEstimate` と ArchSig-SFT report の candidate / boundary / non-conclusion fields を束ねる record。 | `defined only` |
| `ArchSigSFTReport.estimate` | `def` | report が保持する selected SFT estimate を取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsActionClassCandidates` | `def` | action-class candidates を report-side candidate data として取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsTargetRegions` | `def` | target regions を report-side candidate data として取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsCandidateOperationFamilies` | `def` | candidate operation families を report-side candidate data として取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsComparableSignatureAxes` | `def` | comparable signature axes が selected boundary data として残ることを取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsCoverageAssumptions` | `def` | report の coverage assumptions を取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsObservationBoundary` | `def` | report の observation boundary を取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsReconstructionBoundary` | `def` | report の reconstruction boundary を取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsMissingInvariants` | `def` | missing invariants を missing-evidence boundary data として取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsUnmeasuredAxes` | `def` | unmeasured axes を measured-zero ではない explicit boundary として取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsTheoremBoundary` | `def` | theorem/modeling boundary items を取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsForecastBoundary` | `def` | forecast correctness / calibration boundary items を取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsReportBoundary` | `def` | report/tooling boundary items を取り出す。 | `defined only` |
| `ArchSigSFTReport.RecordsNonConclusions` | `def` | report-level non-conclusions を取り出す。 | `defined only` |
| `ArchSigSFTReport.estimate_eq_selectedEstimate` | `theorem` | report estimate accessor が stored selected estimate を返すこと。 | `proved` |
| `ArchSigSFTReportEstimateBoundary` | `structure` | ArchSig report から selected SFT estimate と `SFTForecastStatus` への boundary-preserving relation。 | `defined only` |
| `ArchSigSFTReportEstimateBoundary.estimate_eq_report_estimate` | `theorem` | boundary relation が selected estimate を report accessor と同一視すること。 | `proved` |
| `ArchSigSFTReportEstimateBoundary.report_preserves_coverageAssumptions` | `theorem` | report coverage assumptions が SFT estimate 側へ保存されること。 | `proved` |
| `ArchSigSFTReportEstimateBoundary.report_preserves_observationBoundary` | `theorem` | report observation boundary が SFT estimate 側へ保存されること。 | `proved` |
| `ArchSigSFTReportEstimateBoundary.report_preserves_reconstructionBoundary` | `theorem` | report reconstruction boundary が SFT estimate 側へ保存されること。 | `proved` |
| `ArchSigSFTReportEstimateBoundary.report_missing_invariants_remain_missingEvidence` | `theorem` | missing invariants が estimate missing-evidence boundary として残ること。 | `proved` |
| `ArchSigSFTReportEstimateBoundary.report_unmeasured_axes_remain_forecast_boundary` | `theorem` | unmeasured axes が SFT unmeasured-axis forecast boundary として残ること。 | `proved` |
| `ArchSigSFTReportEstimateBoundary.report_preserves_theoremBoundary` | `theorem` | report theorem boundary が SFT theorem boundary として保存されること。 | `proved` |
| `ArchSigSFTReportEstimateBoundary.report_preserves_forecastBoundary` | `theorem` | report forecast boundary が SFT forecast boundary として保存されること。 | `proved` |
| `ArchSigSFTReportEstimateBoundary.report_existence_does_not_promote_aat_theorem_status` | `theorem` | report output が AAT theorem status を強めず theorem boundary を残すこと。 | `proved` |
| `ArchSigSFTReportEstimateBoundary.report_existence_does_not_promote_calibrated_forecast` | `theorem` | report output が calibrated forecast correctness に昇格せず forecast boundary を残すこと。 | `proved` |
| `ArchSigSFTReportEstimateBoundary.report_boundary_remains_toolingBoundary` | `theorem` | report/tooling boundary が SFT tooling boundary として保存されること。 | `proved` |
| `ArchSigSFTReportEstimateBoundary.report_preserves_nonConclusions` | `theorem` | report non-conclusions が estimate と forecast status の双方に保存されること。 | `proved` |
| `ArchSigAATCoreTransition`, `FieldSigAATCoreTransitionAnalysis`, `GeneratedArchSigAATCoreTransition`, `GeneratedArchSigAATCoreTransition.ofTransition`, `GeneratedFieldSigAATCoreTransitionAnalysis`, `GeneratedArchSigAATCoreTransportTransition`, `GeneratedArchSigAATCoreTransportTransition.ofTransportTransition`, `GeneratedFieldSigAATCoreTransportTransitionAnalysis` | `structure` | ArchSig が観測した `AATCoreTransition` / `AATCoreTransportTransition` を FieldSig / SFT analysis input として読む boundary package。generated 版は source / target の generated law model から Signature bridge を計算し、transport 版は source / target law・molecule を preservation に潰さない。caller-supplied `architectureLawfulFromAAT` field は受け取らない。ArchSig / FieldSig は AAT を定義しない。 | `defined only` |
| `ArchSigAATCoreTransition.records_transition_boundary`, `archsig_transition_does_not_define_aat`, `records_fieldsig_analysis_boundary`, `transition_does_not_create_atoms`, `FieldSigAATCoreTransitionAnalysis.fieldsig_reads_archsig_transition_as_sft_analysis`, `fieldsig_does_not_define_aat`, `transition_does_not_create_atoms`, `forecast_correctness_remains_boundary`, `theorem_and_nonConclusions_remain_boundaries`, `GeneratedArchSigAATCoreTransition.ofTransition`, `GeneratedArchSigAATCoreTransition.generatedArchSigDoesNotDefineAAT_recorded`, `GeneratedArchSigAATCoreTransition.generatedFieldSigAnalysisBoundary_recorded`, `GeneratedArchSigAATCoreTransition.generatedUnknownRejectedUnmeasuredSeparated_recorded`, `GeneratedArchSigAATCoreTransition.sourceBridge`, `targetBridge`, `source_bridge_architectureLawful`, `target_bridge_architectureLawful`, `GeneratedFieldSigAATCoreTransitionAnalysis.fieldsig_reads_generated_archsig_transition_as_sft_analysis`, `GeneratedArchSigAATCoreTransportTransition.ofTransportTransition`, `GeneratedArchSigAATCoreTransportTransition.generatedArchSigDoesNotDefineAAT_recorded`, `GeneratedArchSigAATCoreTransportTransition.generatedFieldSigAnalysisBoundary_recorded`, `GeneratedArchSigAATCoreTransportTransition.generatedUnknownRejectedUnmeasuredSeparated_recorded`, `GeneratedArchSigAATCoreTransportTransition.sourceBridge`, `targetBridge`, `source_bridge_architectureLawful`, `target_bridge_architectureLawful`, `GeneratedFieldSigAATCoreTransportTransitionAnalysis.fieldsig_reads_generated_archsig_transport_transition_as_sft_analysis`, `forecast_correctness_remains_boundary` | `def` / `theorem` | ArchSig transition / FieldSig analysis が AATCore preservation / transport transition を SFT analysis として読むだけで、generated transition では source / target bridge と handoff boundary fields が generated law model / transition non-creation 由来であること、transport transition では source / target law・molecule が別々に保持されること、AAT 定義、atom creation、forecast correctness へ昇格しないことを取り出す。 | `proved` |

## SFT-native Counterexample Package

File: `Formal/Arch/Evolution/SFTCounterexamples.lean`

Issue [#920](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/920) では、
既存の有限 counterexample を SFT の non-conclusion 境界から参照できる entrypoint として
束ねた。新しい反例を作るのではなく、`SignatureDynamics.lean` と
`AttractorEngineering.lean` の proved theorem を wrapper / registry として公開する。
これは endpoint-only metric、accepted-step evidence、same current observation、coarse safety
から、path safety、support preservation、same future support / trajectory、refined hidden-axis
safety、empirical degradation、incident risk、global forecast safety を結論しないための
SFT-native 索引である。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `SFTCounterexampleKind` | `inductive` | SFT-facing counterexample family の分類。endpoint safe + zero delta、accepted/support preservation 分離、same observation future 分離、coarse/refined hidden-axis 分離を列挙する。 | `defined only` |
| `SFTCounterexamples.Package` | `structure` | 既存 counterexample theorem の proof と non-conclusion list を束ねる SFT-native registry。 | `defined only` |
| `SFTCounterexamples.canonicalPackage` | `def` | 既存 proved theorem に基づく canonical SFT counterexample registry。 | `defined only` |
| `SFTCounterexamples.endpoint_safe_zero_delta_not_path_safe` | `theorem` | endpoint delta zero と safe endpoints から path safety を結論しない counterexample accessor。 | `proved` |
| `SFTCounterexamples.accepted_preservation_not_support_preservation` | `theorem` | accepted-step invariant preservation から support preservation は従わない counterexample accessor。 | `proved` |
| `SFTCounterexamples.same_observed_signature_different_future_support` | `theorem` | same current observation から same future operation support は従わない counterexample accessor。 | `proved` |
| `SFTCounterexamples.same_observed_signature_different_future_trajectory` | `theorem` | same current observation から same future signature trajectory は従わない counterexample accessor。 | `proved` |
| `SFTCounterexamples.coarse_safe_not_refined_hidden_axis_safe` | `theorem` | coarse safety から refined hidden-axis safety は従わない counterexample accessor。 | `proved` |
| `SFTCounterexamples.nonConclusionList` | `def` | package が公開する selected non-conclusion kind list。 | `defined only` |
| `SFTCounterexamples.records_nonConclusions` | `theorem` | package の non-conclusion clause を accessor theorem として取り出す。 | `proved` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_sftCounterexamplePackage`, `atomGeneratedSignature_sftCounterexamples_record_nonConclusions`, `atomGeneratedSignature_supportSafety_does_not_discharge_counterexamples` | `def` / `theorem` | Atom-generated support-safety package と canonical counterexample registry を接続し、generated support safety が forbidden reading を discharge せず non-conclusion として保持することを固定する acceptance。 | `defined only` / `proved` |

## SFT Clocked Cone

File: `Formal/Arch/Evolution/SFTClockedCone.lean`

`ClockedForecastCone` は `ForecastCone` に idle / stutter tick を足した exact shared-clock
path model である。core membership は `length = horizon` とし、`<= horizon` の読みは
`BoundedClockedForecastCone` へ分離する。通常の `ForecastCone` からは target-side idle tick
で padding した exact clock witness への bridge を証明する。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `ClockedFieldStep` | `inductive` | active supported step または idle / stutter step からなる clock tick。 | `defined only` |
| `ClockedFieldPath` | `abbrev` | `ClockedFieldStep` を primitive step とする finite path。 | `defined only` |
| `ClockedForecastCone` | `def` | `length = horizon` を要求する exact shared-clock cone membership predicate。 | `defined only` |
| `BoundedClockedForecastCone` | `def` | `length <= horizon` の bounded clocked cone membership predicate。exact clock とは分離する。 | `defined only` |
| `ClockedForecastCone.length_eq_horizon` | `theorem` | exact clocked cone membership から path length と horizon の一致を取り出す。 | `proved` |
| `ClockedForecastCone.length_le_horizon` | `theorem` | exact clocked cone membership から bounded reading を得る。 | `proved` |
| `ClockedForecastCone.nil_mem` | `theorem` | zero-length clocked path が zero-horizon cone に属すること。 | `proved` |
| `ClockedForecastCone.idle_mem_one` | `theorem` | single idle tick が exact one-tick clocked cone に属すること。 | `proved` |
| `BoundedClockedForecastCone.of_clockedForecastCone` | `theorem` | exact shared-clock cone membership を bounded membership へ読む。 | `proved` |
| `BoundedClockedForecastCone.monotone_horizon` | `theorem` | bounded clocked cone では horizon extension が membership を保存すること。 | `proved` |
| `clockedFieldPathOfFieldPath` | `def` | 通常の supported `FieldPath` を active tick だけの clocked path へ持ち上げる。 | `defined only` |
| `boundedClockedForecastCone_of_forecastCone` | `theorem` | 通常の bounded `ForecastCone` witness を同じ horizon の bounded clocked cone witness へ読む。 | `proved` |
| `clockedForecastCone_of_forecastCone` | `theorem` | 通常の bounded `ForecastCone` witness に idle tick を padding し、同じ horizon の exact `ClockedForecastCone` witness へ読む。 | `proved` |
| `ClockedConePoint` | `structure` | target、clocked path、exact cone membership を束ねる sigma-like cone point。 | `defined only` |
| `ClockedConePoint.ofForecastCone` | `def` | 通常の `ForecastCone` witness から exact clocked cone point を作る。 | `defined only` |

## SFT Binary Field Cover

File: `Formal/Arch/Evolution/SFTFieldCover.lean`

`BinaryFieldCover` は global field を left / right local field と shared interface へ制限する
最初の concrete cover API である。`global_ext` は descent 側で使う theorem-bearing uniqueness
principle として cover に保持する。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `BinaryFieldCover` | `structure` | global restriction、interface compatibility、glue、restriction laws、`global_ext`、boundary predicates を束ねる binary cover。 | `defined only` |
| `BinaryFieldCover.compatible_iff_interface_eq` | `theorem` | local compatibility が interface equality と同値であることを取り出す。 | `proved accessor` |
| `BinaryFieldCover.restricts_compatible` | `theorem` | 任意の global state の left / right restrictions が compatible であることを取り出す。 | `proved accessor` |
| `BinaryFieldCover.restrictLeft_glue` | `theorem` | compatible local pair を glue した global state の left restriction を回収する。 | `proved accessor` |
| `BinaryFieldCover.restrictRight_glue` | `theorem` | compatible local pair を glue した global state の right restriction を回収する。 | `proved accessor` |
| `BinaryFieldCover.glue_restricts_eq` | `theorem` | global state の selected restrictions を glue すると元の global state に戻る。 | `proved` |
| `BinaryFieldCover.glue_compatible_proof_irrel` | `theorem` | 同じ compatible local pair の glue は compatibility proof の選び方に依存しない。 | `proved` |

## SFT Binary Descent

File: `Formal/Arch/Evolution/SFTDescent.lean`

Exact `ClockedForecastCone` 上の最初の substantive binary descent surface を定義する。global
cone point は compatible local cone family へ射影でき、compatible local path は
`BinaryClockedStepGluingData` から global clocked path へ glue できる。さらに selected
inverse laws は `BinaryProjectionGluingLaws` の endpoint projection/glue laws から
endpoint-based equivalence として構成できる。加えて
`BinaryProjectionGluingPathLaws` から、explicit selected path-level equivalence data に
相対化された path-level inverse-law constructor も構成できる。これは dependent path の
definitional equality ではなく、selected relatedness であり、その relatedness には
reflexive / symmetric / transitive laws と endpoint consequence を要求する。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `ConeEquivalence` | `structure` | selected forward / inverse maps、両側の inverse-up-to-relatedness laws、relatedness の reflexive / symmetric / transitive laws を持つ equivalence witness。 | `defined only` |
| `BinarySFTModel` | `structure` | binary cover、global/local/interface support、step relation、projection/gluing premises、boundary predicates を束ねる model。 | `defined only` |
| `BinarySFTModel.projectClockedForecastCone_left` | `theorem` | global exact clocked cone membership を left local exact clocked cone membership へ射影する。 | `proved` |
| `BinarySFTModel.projectClockedForecastCone_right` | `theorem` | global exact clocked cone membership を right local exact clocked cone membership へ射影する。 | `proved` |
| `CompatibleLocalClockedStep` | `structure` | left/right の 1 tick と source/target compatibility、interface-step boundary を束ねる local tick pair。 | `defined only` |
| `CompatibleLocalClockedPath` | `inductive` | left/right local clocked paths を tickwise に zip する compatibility witness。 | `defined only` |
| `CompatibleLocalClockedPath.left_length_eq_right_length` | `theorem` | tickwise-compatible local paths の left/right clock length が一致する。 | `proved` |
| `BinarySFTModel.projectClockedStepPairCompatible` | `def` | global clock tick の left/right projections から compatible local tick pair を構成する。 | `defined only` |
| `BinarySFTModel.projectedClockedPaths_tickwiseCompatible` | `def` | global clocked path の left/right projections が tickwise compatible であることを構成する。 | `defined only` |
| `BinaryClockedStepGluingData` | `structure` | compatible local tick pair から global clock tick を構成する step-level gluing data と boundary predicates。 | `defined only` |
| `BinaryClockedStepGluingData.glueCompatibleLocalClockedPath` | `def` | tickwise-compatible local paths を global clocked path へ glue する。 | `defined only` |
| `BinaryClockedStepGluingData.glueCompatibleLocalClockedPath_length` | `theorem` | glued global path の clock length が left local path の length と一致する。 | `proved` |
| `CompatibleBinaryClockedConeFamily` | `structure` | left/right exact clocked cone points、endpoint compatibility、tickwise local path witness を束ねる local cone family。 | `defined only` |
| `projectGlobalConePointToBinaryFamily` | `def` | global cone point を compatible binary local family へ射影する。 | `defined only` |
| `glueCompatibleBinaryClockedConeFamily` | `def` | `BinaryClockedStepGluingData` から compatible local cone family を global exact clocked cone point へ glue する。 | `defined only` |
| `GlobalConePointTargetEquivalent` | `def` | global cone points を target equality で関連づける endpoint-based equivalence。 | `defined only` |
| `LocalFamilyTargetEquivalent` | `def` | compatible local families を left/right target equality で関連づける endpoint-based equivalence。 | `defined only` |
| `GlobalConePointPathEquivalenceData` | `structure` | global cone points の selected path-level relatedness、equivalence-relation laws、endpoint consequence を束ねる。 | `defined only` |
| `LocalFamilyPathEquivalenceData` | `structure` | compatible local families の selected path-level relatedness、equivalence-relation laws、left/right endpoint consequence を束ねる。 | `defined only` |
| `globalConePointTargetEquivalent_refl` / `symm` / `trans` | `theorem` | global endpoint equivalence の equivalence-relation laws。 | `proved` |
| `localFamilyTargetEquivalent_refl` / `symm` / `trans` | `theorem` | local-family endpoint equivalence の equivalence-relation laws。 | `proved` |
| `BinaryProjectionGluingLaws` | `structure` | step-level projection law boundaries と endpoint projection/glue laws を束ねる。 | `defined only` |
| `BinaryProjectionGluingPathLaws` | `structure` | endpoint projection/glue laws の上に、global/local の selected path-level inverse laws と strict path law boundary を束ねる。 | `defined only` |
| `BinaryProjectionGluingPathLaws.toEndpointLaws` | `def` | selected path-level law package から endpoint-law component を忘却する。 | `defined only` |
| `BinaryProjectionGluingPathLaws.glue_project_after_projection_endpoint` | `theorem` | selected global path inverse law から glue-after-projection の target equality を取り出す。 | `proved accessor` |
| `BinaryProjectionGluingPathLaws.project_after_glue_endpoint` | `theorem` | selected local-family path inverse law から projection-after-glue の left/right target equality を取り出す。 | `proved accessor` |
| `projected_glued_target_related` | `theorem` | projection after glue が original local family と endpoint-equivalent であること。 | `proved` |
| `glued_projected_target_related` | `theorem` | glue after projection が original global cone point と endpoint-equivalent であること。 | `proved` |
| `BinaryProjectionGluingEquivalenceLaws` | `structure` | concrete step-glued map に対する selected inverse laws と equivalence-relation laws を束ねる。 | `defined only` |
| `BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws` | `def` | endpoint projection/glue laws から selected equivalence laws を構成する。 | `defined only` |
| `BinaryDescentAssumptions.ofStepGluing` | `def` | step-level gluing data と selected inverse laws から `BinaryDescentAssumptions` を構成する。 | `defined only` |
| `BinaryDescentAssumptions.ofEndpointLaws` | `def` | step-level gluing data と endpoint projection/glue laws から `BinaryDescentAssumptions` を構成する。 | `defined only` |
| `BinaryDescentAssumptions` | `structure` | compatible local family の gluing、selected inverse laws、global/local relatedness の equivalence-relation laws を束ねる descent assumptions。 | `defined only` |
| `BinaryDescentAssumptions.glueClockedPoint` | `def` | compatible local family から global exact clocked cone point を構成する。 | `defined only` |
| `forecastCone_descent_binary` | `def` | `BinaryDescentAssumptions` から global cone point と compatible local family の selected `ConeEquivalence` を構成する。 | `defined only` |
| `forecastCone_descent_binary_of_endpoint_laws` | `def` | step gluing data と endpoint projection/glue laws から binary selected descent equivalence を構成する。 | `defined only` |
| `forecastCone_descent_binary_of_path_laws` | `def` | step gluing data、endpoint laws、selected path-level inverse laws から binary selected descent equivalence を構成する。 | `defined only` |
| `BinarySelectedForecastConeDescentPackage.ofAssumptions` | `def` | binary descent assumptions を selected descent package へ束ねる。 | `defined only` |
| `BinarySelectedForecastConeDescentPackage.ofEndpointLaws` | `def` | endpoint projection/glue laws から selected binary descent package を構成する。 | `defined only` |
| `BinarySelectedForecastConeDescentPackage.ofPathLaws` | `def` | selected path-level inverse laws から selected binary descent package を構成し、endpoint / step / strict path law boundary を保持する。 | `defined only` |
| `binaryForecastConeDescentPackage_of_assumptions` | `theorem` | assumptions から selected binary descent package の存在を取り出す。 | `proved accessor` |
| `binaryForecastConeDescentPackage_of_endpoint_laws` | `theorem` | endpoint projection/glue laws から selected binary descent package の存在を取り出す。 | `proved accessor` |
| `binaryForecastConeDescentPackage_of_path_laws` | `theorem` | selected path-level inverse laws から selected binary descent package の存在を取り出す。 | `proved accessor` |
| `SFTModuleBoundary` | `def` | すべての source / horizon で selected descent equivalence があることを module boundary として定義する。 | `defined only` |
| `moduleBoundary_iff_forecastConeDescent` | `theorem` | `SFTModuleBoundary` と source/horizon indexed descent の同値を取り出す。 | `proved` |
| `LocalFamilyDoesNotLift` | `def` | compatible local family が global cone point に lift しない failure predicate。 | `defined only` |
| `GlobalPathsLocallyIdentified` | `def` | distinct global cone points が local projection で同一視される failure predicate。 | `defined only` |

## SFT Finite-Cover Descent Skeleton

File: `Formal/Arch/Evolution/SFTFiniteCover.lean`

Binary cover descent の上に、uniform finite cover と Cech-style simplex を concrete API として置く。
この surface は full Cech cohomology ではなく、finite index、selected local family、explicit finite
gluing、selected compatibility laws に相対化された ForecastCone descent skeleton である。すべての
finite cover が descent を満たすこと、Cech cohomology theorem、Fundamental Modularity theorem は
主張しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `UniformFiniteFieldCover` | `structure` | concrete `indices : List Index`、global-to-local restriction、coverage / finite / non-conclusion boundary を束ねる uniform finite cover skeleton。 | `defined only` |
| `UniformFiniteFieldCover.RecordsCoverage` | `def` | selected cover の coverage boundary を取り出す。 | `defined only` |
| `UniformFiniteFieldCover.RecordsFiniteBoundary` | `def` | selected finite-witness boundary を取り出す。 | `defined only` |
| `Cech0Simplex` | `structure` | finite cover の selected 0-simplex / index membership witness。 | `defined only` |
| `Cech1Simplex` | `structure` | selected pair overlap と overlap boundary を持つ Cech-style 1-simplex。 | `defined only` |
| `Cech2Simplex` | `structure` | selected triple overlap と triple-overlap boundary を持つ Cech-style 2-simplex。 | `defined only` |
| `FiniteSFTModel` | `structure` | finite cover 上の global/local support、step relation、operation projection、support / step projection laws を束ねる。 | `defined only` |
| `FiniteSFTModel.projectClockedStepLocal` | `def` | selected finite index で global clock tick を local clock tick へ射影する。 | `defined only` |
| `FiniteSFTModel.projectClockedPathLocal` | `def` | selected finite index で global clocked path を local clocked path へ射影する。 | `defined only` |
| `FiniteSFTModel.projectClockedPathLocal_length` | `theorem` | finite local projection が clock length を保存する。 | `proved` |
| `FiniteSFTModel.projectClockedForecastCone_local` | `theorem` | exact global clocked cone membership を selected local exact cone membership へ射影する。 | `proved` |
| `FiniteLocalConeDatum` | `structure` | selected index の local target/path/cone membership を束ねる datum。 | `defined only` |
| `FiniteLocalClockedConeFamily` | `structure` | 各 selected finite index の local target/path/cone membership と Cech compatibility boundary を束ねる compatible local cone family。 | `defined only` |
| `FiniteLocalClockedConeFamily.local_length_eq_horizon` | `theorem` | finite local family の各 selected local path が exact shared-clock horizon を持つ。 | `proved` |
| `projectGlobalConePointToFiniteFamily` | `def` | global cone point を finite local cone family へ射影する。 | `defined only` |
| `FiniteClockedGluingData` | `structure` | finite local family から global cone point を作る selected gluing data と projection / compatibility / finite-cover boundary。 | `defined only` |
| `FiniteGlobalConeEquivalenceData` | `structure` | finite descent の global cone point relatedness と equivalence-relation laws を束ねる。 | `defined only` |
| `FiniteLocalFamilyEquivalenceData` | `structure` | finite local family relatedness と equivalence-relation laws を束ねる。 | `defined only` |
| `FiniteProjectionGluingLaws` | `structure` | finite projection/glue inverse laws、global/local selected equivalence、Cech compatibility / finite descent boundary を束ねる。 | `defined only` |
| `FiniteTransportNormalizedPathEquality` | `structure` | finite projection/gluing 後の path equality を selected equivalence と normalized inverse laws として束ねる。definitional path equality は主張しない。 | `defined only` |
| `FiniteTransportNormalizedPathEquality.global_inverse_law` | `theorem` | transport-normalized package から global cone point 側の selected inverse law を取り出す。 | `proved accessor` |
| `FiniteTransportNormalizedPathEquality.local_inverse_law` | `theorem` | transport-normalized package から finite local-family 側の selected inverse law を取り出す。 | `proved accessor` |
| `forecastCone_descent_finite_of_laws` | `def` | explicit finite gluing と Cech-style compatibility laws から global cone point と finite local family の selected `ConeEquivalence` を構成する。 | `defined only` |
| `FiniteSelectedForecastConeDescentPackage` | `structure` | finite-cover selected descent equivalence、package boundary、non-conclusions を束ねる。 | `defined only` |
| `FiniteSelectedForecastConeDescentPackage.ofLaws` | `def` | explicit finite projection/gluing laws から finite selected descent package を構成する。 | `defined only` |
| `FiniteSelectedForecastConeDescentPackage.ofTransportNormalizedPathEquality` | `def` | transport-normalized path equality から finite selected descent package を構成する。 | `defined only` |
| `FiniteSelectedForecastConeDescentPackage.normalized_global_inverse_law` | `theorem` | constructed finite selected package が normalized global inverse law を保持することを取り出す。 | `proved accessor` |
| `FiniteSelectedForecastConeDescentPackage.normalized_local_inverse_law` | `theorem` | constructed finite selected package が normalized local-family inverse law を保持することを取り出す。 | `proved accessor` |
| `GoodFiniteCoverDescentCondition` | `structure` | exact gluing、support-stable boundary、transport-normalized inverse laws を good finite cover の十分条件として束ねる。 | `defined only` |
| `GoodFiniteCoverDescentCondition.descentPackage` | `def` | good finite cover 条件から selected finite descent package を構成する。 | `defined only` |
| `forecastCone_descent_of_goodFiniteCover` | `theorem` | good-cover sufficient condition から selected finite ForecastCone descent package の存在を取り出す。all finite covers theorem ではない。 | `proved accessor` |
| `finiteForecastConeDescentPackage_of_laws` | `theorem` | explicit laws から finite selected descent package の存在を取り出す。 | `proved accessor` |
| `finiteCoverOfBinaryCover` | `def` | binary cover を `Bool` index / `Sum Left Right` local carrier の finite cover skeleton として読む cover-level bridge。 | `defined only` |
| `BinaryAsFiniteCoverPackage` | `structure` | binary-as-finite cover bridge の package boundary を束ねる。 | `defined only` |
| `FiniteCechDescentCohomologyBridge` | `structure` | selected `H1Vanishes` と finite descent glue predicate の iff bridge を保持する cohomology-facing skeleton。 | `defined only` |
| `FiniteCechDescentCohomologyBridge.finiteDescent_of_h1_vanishes` | `theorem` | selected bridge から H1 vanishing implies finite descent reading を取り出す。 | `proved accessor` |
| `FiniteCechDescentCohomologyBridge.h1_vanishes_of_finiteDescent` | `theorem` | selected bridge から finite descent implies H1 vanishing reading を取り出す。 | `proved accessor` |

## SFT Finite Exact Model

File: `Formal/Arch/Evolution/SFTFiniteExactModel.lean`

Fundamental Modularity assumption discharge のため、selected finite proof universe、
exact cover、operation support / relation、observation boundary、governance basis を
同じ package として束ねる。これは後続 theorem が参照する public entrypoint であり、
empirical correctness、すべての finite cover の descent、
full Fundamental Modularity theorem は主張しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `FiniteExactSFTModel` | `structure` | selected global / index / local / operation / governance carriers、`UniformFiniteFieldCover`、`FiniteSFTModel`、`ObservationBoundary`、exact cover / operation / observation / governance / extractor / empirical boundary を束ねる。 | `defined only` |
| `FiniteExactSFTModel.exactCover` | `def` | selected exact finite cover を後続 theorem 向け entrypoint として取り出す。 | `defined only` |
| `FiniteExactSFTModel.descentModel` | `def` | theorem-bearing `FiniteSFTModel` を後続 descent / obstruction theorem 向け entrypoint として取り出す。 | `defined only` |
| `FiniteExactSFTModel.exactCover_indices_eq_selected` | `theorem` | exact cover の index list が selected index carrier と一致することを取り出す。 | `proved accessor` |
| `FiniteExactSFTModel.RecordsSelectedUniverseBoundary` | `def` | selected finite universe boundary を取り出す。 | `defined only` |
| `FiniteExactSFTModel.RecordsExactCoverBoundary` | `def` | exact cover / coverage / finite witness boundary を取り出す。 | `defined only` |
| `FiniteExactSFTModel.RecordsOperationBoundary` | `def` | operation support と step relation の boundary を取り出す。 | `defined only` |
| `FiniteExactSFTModel.RecordsFiniteModelBoundary` | `def` | finite model package 自体の boundary を取り出す。 | `defined only` |
| `FiniteExactSFTModel.RecordsObservationBoundary` | `def` | selected observation boundary と theorem / non-conclusion boundary を取り出す。 | `defined only` |
| `FiniteExactSFTModel.RecordsGovernanceBasisBoundary` | `def` | selected governance basis boundary を取り出す。 | `defined only` |
| `FiniteExactSFTModel.RecordsExtractorEmpiricalBoundary` | `def` | extractor / empirical boundary を completeness や correctness に昇格せず保持する。 | `defined only` |
| `FiniteExactSFTModel.RecordsNonConclusions` | `def` | cover、finite model、observation、extractor、empirical non-conclusions をまとめて保持する。 | `defined only` |
| `FiniteExactDescentAssumptions` | `structure` | `FiniteExactSFTModel` 上の explicit finite gluing data、projection/gluing laws、exact cover / operation / observation / governance boundary を束ねる descent assumption package。 | `defined only` |
| `FiniteExactDescentAssumptions.descentPackage` | `def` | explicit assumptions から selected finite ForecastCone descent package を構成する。 | `defined only` |
| `FiniteExactDescentAssumptions.records_exactCoverBoundary` | `theorem` | finite exact descent assumptions が exact cover boundary を保持することを取り出す。 | `proved accessor` |
| `FiniteExactDescentAssumptions.records_operationBoundary` | `theorem` | operation support / relation boundary を取り出す。 | `proved accessor` |
| `FiniteExactDescentAssumptions.records_observationBoundary` | `theorem` | observation boundary を取り出す。 | `proved accessor` |
| `FiniteExactDescentAssumptions.records_governanceBoundary` | `theorem` | governance basis boundary を取り出す。 | `proved accessor` |
| `FiniteExactDescentAssumptions.RecordsNonConclusions` | `def` | finite exact descent assumptions の non-conclusion boundary を保持する。 | `defined only` |
| `FiniteExactDescentAssumptions.DescentPackageBoundary` | `def` | 構成された descent package の boundary proposition を取り出す。 | `defined only` |
| `FiniteExactDescentAssumptions.DescentPackageNonConclusions` | `def` | 構成された descent package の non-conclusion proposition を取り出す。 | `defined only` |
| `finiteExactForecastConeDescentPackage_of_assumptions` | `theorem` | 明示された finite exact descent assumptions の下で、各 selected source / horizon の `FiniteSelectedForecastConeDescentPackage` の存在を証明する。 | `proved accessor` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFiniteExactModel`, `atomGeneratedSignature_generatedFiniteExactModel_indices_selected`, `atomGeneratedSignature_generatedFiniteExactModel_records_exactCover`, `atomGeneratedSignature_generatedFiniteExactModel_records_operation`, `atomGeneratedSignature_generatedFiniteExactModel_records_nonConclusions` | `def` / `theorem` | Atom-generated carrier を global/local carrier とする singleton-index finite exact SFT model を構成し、selected index、exact-cover boundary、operation boundary、non-conclusions を固定する acceptance。 | `defined only` / `proved` |

## SFT Cech Cone Cohomology Vocabulary

File: `Formal/Arch/Evolution/SFTCechCohomology.lean`

Finite cover の 0/1-simplex skeleton と selected exact cone family を接続する
concrete Cech cochain vocabulary を定義する。ここでは cocycle / coboundary
predicate と bridge を置くが、`H1 = 0 -> finite descent` や full Cech
cohomology theorem は証明しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `CechCone0` | `structure` | 各 `Cech0Simplex` に local target / exact local path / cone membership を割り当てる concrete cone-valued 0-cochain。 | `defined only` |
| `CechCone0.ofFiniteLocalFamily` | `def` | `FiniteLocalClockedConeFamily` を 0-simplex indexed 0-cochain として読む。 | `defined only` |
| `CechCone0.ofGlobalConePoint` | `def` | global cone point を各 0-simplex へ射影して 0-cochain を作る。 | `defined only` |
| `CechCone0.local_length_eq_horizon` | `theorem` | 0-cochain の各 local path が selected horizon と同じ exact length を持つ。 | `proved` |
| `CechCone1` | `structure` | 各 `Cech1Simplex` に overlap compatibility predicate と boundary を割り当てる concrete 1-cochain surface。 | `defined only` |
| `CechCone1.ofFiniteLocalFamily` | `def` | `FiniteLocalClockedConeFamily` の pairwise compatibility を 1-simplex indexed 1-cochain として読む。 | `defined only` |
| `IsCechConeCocycle` | `def` | すべての selected 1-simplex で overlap compatibility が成り立つことを cocycle predicate として定義する。 | `defined only` |
| `CechConeCoboundary` | `structure` | global cone point の selected local projections が 0-cochain target と一致する coboundary witness。 | `defined only` |
| `IsCechConeCoboundary` | `def` | `CechConeCoboundary` の存在を predicate として読む。 | `defined only` |
| `CechConeCoboundary.ofGlobalConePoint` | `def` | global cone point の projection から coboundary witness を作る。 | `defined only` |
| `CechConeCoboundary.isCoboundary_of_globalConePoint` | `theorem` | global cone point の projection が coboundary predicate を満たすことを取り出す。 | `proved accessor` |
| `cechConeCocycle_of_finiteLocalFamily` | `theorem` | existing finite local family の pairwise compatibility / Cech boundary から concrete cocycle predicate を得る。 | `proved accessor` |
| `CechConeH1Vanishes` | `structure` | concrete selected `H1 = 0` vocabulary として、すべての selected cocycle が coboundary であること、H1 / finite boundary、non-conclusions を束ねる。 | `defined only` |
| `CechConeH1Vanishes.cocycle_is_coboundary` | `theorem` | selected H1 vanishing から concrete cocycle が coboundary であることを取り出す。 | `proved accessor` |
| `CechH1FiniteDescentAssumptions` | `structure` | concrete H1 vanishing と `FiniteExactDescentAssumptions` を同じ selected source / horizon slice で束ねる bridge package。 | `defined only` |
| `CechH1FiniteDescentAssumptions.RecordsH1Vanishes` | `def` | H1 / selected finite boundary を取り出す。 | `defined only` |
| `CechH1FiniteDescentAssumptions.RecordsNonConclusions` | `def` | H1 と finite descent assumptions の non-conclusion boundary を保持する。 | `defined only` |
| `h1_vanishes_implies_finite_descent` | `theorem` | concrete selected `H1 = 0` と finite exact descent assumptions の下で selected finite ForecastCone descent package の存在を証明する。 | `proved accessor` |
| `h1_vanishes_selected_finite_descent_bridge` | `theorem` | selected finite descent package、H1 vanishing record、non-conclusion boundary を同時に取り出す bridge。full Cech cohomology theorem ではない。 | `proved accessor` |
| `h1_vanishes_implies_finite_descent_with_normalized_paths` | `theorem` | concrete selected `H1 = 0` bridge を transport-normalized path equality の boundary と合わせて読む。full Cech cohomology theorem ではない。 | `proved accessor` |

## SFT Finite Descent Obstruction / Governance Cutting

File: `Formal/Arch/Evolution/SFTDescentObstruction.lean`

Finite-cover selected descent skeleton の failure を typed obstruction witness、Cech-facing bridge、
review projection、governance cutting package へ接続する checked surface を定義する。これは selected
classifier と selected governance law に相対化され、すべての descent failure の完全分類、full
Cech cohomology、operational governance effectiveness、Fundamental Modularity theorem は主張しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `FiniteDescentFailureKind` | `inductive` | finite descent failure を no global lift、local identification、Cech incompatibility、governance blocked に分類する selected kind。 | `defined only` |
| `FiniteDescentFailure` | `structure` | failure kind、optional local/global evidence payload、evidence boundary、non-conclusions を束ねる failure package。 | `defined only` |
| `FiniteObstructionClass` | `inductive` | missing glue、overlap mismatch、hidden coupling、support mismatch、governance conflict の typed obstruction class。 | `defined only` |
| `FiniteDescentObstructionPayload` | `structure` | failure kind、obstruction class、affected indices、classifier boundary、non-conclusions を束ねる witness payload。 | `defined only` |
| `FiniteTypedObstructionWitness` / `FiniteDescentObstructionWitness` | `structure` / `abbrev` | finite descent failure に対する typed obstruction witness。outer failure kind と payload failure kind の equality witness を保持する。 | `defined only` |
| `FiniteDescentObstructionClassifier` | `structure` | selected failure を optional typed witness へ写す classifier、outer / payload failure kind soundness law、completeness boundary を束ねる。 | `defined only` |
| `FiniteDescentObstructionClassifier.classified_failureKind_eq` | `theorem` | classified witness の outer failure kind が selected failure kind と一致することを取り出す。 | `proved accessor` |
| `FiniteDescentObstructionClassifier.classified_payload_failureKind_eq` | `theorem` | classified witness の payload failure kind が selected failure kind と一致することを取り出す。 | `proved accessor` |
| `FiniteDescentObstructionClassifier.classified_payload_matches_witness_kind` | `theorem` | classified witness 内の outer failure kind と payload failure kind の一致を取り出す。 | `proved accessor` |
| `finite_descent_obstruction_of_classified_failure` | `theorem` | classifier が selected failure を分類しているなら obstruction witness を取り出す。 | `proved accessor` |
| `finite_descent_obstruction_of_classified_failure_sound` | `theorem` | classified witness とともに outer / payload failure kind equality を取り出す。 | `proved accessor` |
| `finite_descent_obstruction_of_classified_failure_sound_complete` | `theorem` | classified witness とともに outer tag、payload tag、witness-internal payload tag の一致をすべて取り出す。 | `proved accessor` |
| `FiniteDescentObstructionPackage` | `structure` | classifier と every-selected-failure-classified assumption、obstruction boundary を束ねる。 | `defined only` |
| `finite_descent_obstruction_of_failure` | `theorem` | package assumption の下で selected finite descent failure から typed obstruction witness を得る。 | `proved accessor` |
| `finite_descent_obstruction_of_failure_sound` | `theorem` | package assumption の下で obstruction witness と outer / payload failure kind equality を同時に得る。 | `proved accessor` |
| `FiniteExactFailureClassifierCompleteness` | `structure` | `FiniteExactSFTModel` に相対化された classifier completeness package。selected failure boundary、classifier completeness / soundness boundary、non-conclusions を保持する。 | `defined only` |
| `FiniteExactFailureClassifierCompleteness.classifier` | `def` | finite exact completeness package から selected classifier を取り出す。 | `defined only` |
| `FiniteExactFailureClassifierCompleteness.RecordsClassifierCompletenessBoundary` | `def` | selected classifier completeness boundary を取り出す。 | `defined only` |
| `FiniteExactFailureClassifierCompleteness.RecordsNonConclusions` | `def` | finite exact model、obstruction package、classifier の non-conclusion boundary を保持する。 | `defined only` |
| `FiniteExactFailureClassifierCompleteness.records_exactCoverBoundary` | `theorem` | finite exact classifier completeness package が exact cover boundary を保持することを取り出す。 | `proved accessor` |
| `FiniteExactFailureClassifierCompleteness.records_finiteModelBoundary` | `theorem` | finite model boundary を保持することを取り出す。 | `proved accessor` |
| `FiniteFailureKindClassifierCoverage` | `def` | selected classifier coverage を failure kind 単位で表す predicate。global classifier completeness ではない。 | `defined only` |
| `FiniteFailureKindClassifierCoverageMatrix` | `def` | selected finite failure kind ごとの coverage predicate を束ねる matrix。 | `defined only` |
| `finiteExact_failure_classifier_complete` | `theorem` | selected finite exact descent failure が classifier package により typed obstruction witness へ分類され、outer / payload failure-kind soundness が保たれることを証明する。 | `proved accessor` |
| `finiteExact_failureKind_classifier_complete` | `theorem` | finite exact classifier completeness package を selected failure kind ごとの witness availability として読む。 | `proved accessor` |
| `finiteExact_failureKind_classifier_matrix` | `theorem` | finite exact classifier completeness package から failure-kind coverage matrix を取り出す。 | `proved accessor` |
| `CechCocycleObstruction` | `structure` | concrete Cech cocycle と selected non-coboundary / obstruction boundary を束ねる Cech-side obstruction witness。 | `defined only` |
| `FiniteCechTypedObstructionBridge` | `structure` | selected finite exact model 上で typed obstruction witness と Cech cocycle obstruction を対応付ける bridge package。 | `defined only` |
| `FiniteCechTypedObstructionBridge.RecordsSelectedFiniteBoundary` | `def` | Cech obstruction bridge の selected finite / classifier completeness boundary を取り出す。 | `defined only` |
| `FiniteCechTypedObstructionBridge.RecordsNonConclusions` | `def` | Cech obstruction bridge と classifier completeness の non-conclusion boundary を保持する。 | `defined only` |
| `cech_obstruction_of_typed_witness` | `def` | typed finite obstruction witness を selected Cech cocycle obstruction として読む。 | `defined only` |
| `typed_obstruction_of_cech_cocycle_obstruction` | `theorem` | selected Cech cocycle obstruction から classifier completeness bridge 経由で typed finite obstruction witness を得る。 | `proved accessor` |
| `typed_obstruction_of_cech_cocycle_preserves_failure_kind` | `theorem` | Cech cocycle obstruction 由来の typed witness が selected failure kind と payload kind の一致を保持することを取り出す。 | `proved accessor` |
| `FiniteCechObstructionBridge` | `structure` | finite Cech descent bridge、obstruction package、H1 nonzero / obstruction reflection boundary を束ねる。 | `defined only` |
| `FiniteCechObstructionBridge.finite_descent_of_h1_vanishes` | `theorem` | obstruction bridge 経由で selected H1 vanishing から finite descent reading を取り出す。 | `proved accessor` |
| `FiniteObstructionReviewProjection` | `structure` | obstruction witness を selected review decision へ写す projection と sound/minimal-envelope boundary を束ねる。 | `defined only` |
| `finite_obstruction_review_records_sound_boundary` | `theorem` | review projection の sound boundary を assumption-preserving accessor として公開する。 | `proved accessor` |
| `FiniteGovernanceCutTarget` | `structure` | selected bad obstruction predicate と desired local-family preservation predicate を束ねる governance target。 | `defined only` |
| `FiniteGovernanceCuttingPackage` | `structure` | selected intervention、bad cutting law、desired preservation law、governance boundary を束ねる。 | `defined only` |
| `finite_governance_cuts_bad_obstruction` | `theorem` | selected bad obstruction witness が selected intervention で cut されることを取り出す。 | `proved accessor` |
| `finite_governance_preserves_desired_family` | `theorem` | selected desired local family が selected intervention で preserved されることを取り出す。 | `proved accessor` |
| `FiniteObstructionGovernancePackage` | `structure` | obstruction package と governance cutting package の bridge boundary を束ねる。 | `defined only` |
| `governance_cuts_obstruction_of_finite_failure` | `theorem` | selected finite failure が bad obstruction として分類されるなら selected governance intervention がその witness を cut する。 | `proved accessor` |
| `FiniteExactGovernanceCuttingSoundness` | `structure` | `FiniteExactSFTModel` に相対化された governance cutting soundness package。bad exclusion / desired preservation / operational boundary と non-conclusions を保持する。 | `defined only` |
| `FiniteExactGovernanceCuttingSoundness.governancePackage` | `def` | finite exact soundness package から selected governance cutting package を取り出す。 | `defined only` |
| `FiniteExactGovernanceCuttingSoundness.RecordsSoundnessBoundary` | `def` | bad exclusion、desired preservation、operational boundary を取り出す。 | `defined only` |
| `FiniteExactGovernanceCuttingSoundness.RecordsNonConclusions` | `def` | exact model、obstruction-governance package、governance package の non-conclusion boundary を保持する。 | `defined only` |
| `FiniteExactGovernanceCuttingSoundness.records_exactCoverBoundary` | `theorem` | exact cover boundary を保持することを取り出す。 | `proved accessor` |
| `FiniteExactGovernanceCuttingSoundness.records_finiteModelBoundary` | `theorem` | finite model boundary を保持することを取り出す。 | `proved accessor` |
| `finiteExact_governance_cuts_bad_failure` | `theorem` | selected finite exact model 上で、bad と分類された finite failure が selected intervention により cut されることを取り出す。 | `proved accessor` |
| `finiteExact_governance_preserves_desired_family` | `theorem` | selected finite exact model 上で、selected desired local family が selected intervention により preserved されることを取り出す。 | `proved accessor` |
| `finiteExact_governance_cutting_sound` | `theorem` | selected bad obstruction cutting と selected desired-family preservation を同時に取り出す soundness accessor。 | `proved accessor` |

## SFT Theorem Roadmap

File: `Formal/Arch/Evolution/SFTTheoremRoadmap.lean`

`docs/sft/sft_theorem_roadmap_and_research_vision.md` の ForecastCone Descent から
Fundamental Modularity Theorem までの theorem family を、Lean 側の checked entrypoint
として束ねた。ロードマップの大定理は無条件の global theorem として主張せず、descent、
cover compatibility、cohomology、governance、calibration、fixed point などの仮定を明示した
theorem package surface と accessor theorem として実装する。

Non-conclusions: この entrypoint は global descent、module boundary の完全性、
cohomology vanishing、governance effectiveness、calibrated forecast correctness、
AI agent safety、lifecycle decision correctness を無条件には結論しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `SFTTheoremRoadmap.ClockedForecastConeDescentPackage` | `structure` | compatible local family との bidirectional equivalence と descent boundary を束ねる ForecastCone Descent package。 | `defined only` |
| `SFTTheoremRoadmap.ClockedForecastConeDescentPackage.forecastCone_descent` | `theorem` | package assumption から global clocked cone と compatible local family の equivalence witness の存在を取り出す descent witness accessor。 | `proved accessor` |
| `SFTTheoremRoadmap.BinaryForecastConeDescentPackage.forecastCone_binary_descent` | `theorem` | binary cover の pullback 形式の descent witness existence を取り出す。 | `proved accessor` |
| `SFTTheoremRoadmap.binaryForecastConeDescent_of_endpoint_laws` | `theorem` | step gluing data と endpoint projection/glue laws から selected binary descent package の存在を取り出す roadmap-facing accessor。 | `proved accessor` |
| `SFTTheoremRoadmap.binaryForecastConeDescent_of_path_laws` | `theorem` | step gluing data と selected path-level inverse laws から selected binary descent package の存在を取り出す roadmap-facing accessor。finite-cover descent や full Fundamental Modularity theorem は主張しない。 | `proved accessor` |
| `SFTTheoremRoadmap.finiteForecastConeDescent_of_laws` | `theorem` | explicit finite gluing と Cech-style compatibility laws から finite selected descent package の存在を取り出す roadmap-facing accessor。すべての finite cover の descent や full Cech cohomology は主張しない。 | `proved accessor` |
| `SFTTheoremRoadmap.finite_governance_cuts_obstruction_of_failure` | `theorem` | selected finite descent failure が selected bad obstruction として分類されるなら selected governance cutting package がその obstruction を cut する roadmap-facing accessor。operational governance effectiveness や full Fundamental Modularity theorem は主張しない。 | `proved accessor` |
| `SFTTheoremRoadmap.ModularityRepresentationPackage.modularity_representation` | `theorem` | module boundary、ForecastCone descent、unique compatible representation の同値 package を展開する。 | `proved accessor` |
| `SFTTheoremRoadmap.DescentObstructionPackage.obstruction_of_no_lift` | `theorem` | actual no-lift predicate から typed surjectivity obstruction witness を得る。 | `proved accessor` |
| `SFTTheoremRoadmap.DescentObstructionPackage.obstruction_of_local_identification` | `theorem` | local identification failure から typed injectivity obstruction witness を得る。 | `proved accessor` |
| `SFTTheoremRoadmap.PathIndistinguishableFor` | `def` | sound decision projection が区別しない path 同士の relation。 | `defined only` |
| `SFTTheoremRoadmap.ReviewSetoid` | `def` | decision projection relative な quotient 用 setoid。 | `defined only` |
| `SFTTheoremRoadmap.MinimalEnvelope` | `def` | `ReviewSetoid` の quotient として定義される minimal decision envelope。 | `defined only` |
| `SFTTheoremRoadmap.MinimalEnvelope.minimalEnvelope_sound` | `theorem` | quotient equality から任意の sound decision projection の equality を得る。 | `proved` |
| `SFTTheoremRoadmap.MinimalEnvelope.minimalEnvelope_exact` | `theorem` | sound projection が同じなら minimal envelope でも同一視される。 | `proved` |
| `SFTTheoremRoadmap.MinimalEnvelope.minimalEnvelope_factors` | `theorem` | sound decision projection が minimal envelope を factor する。 | `proved` |
| `SFTTheoremRoadmap.minimalConsequenceEnvelopePackageOfDecisionEquivalence` | `def` | decision-preserving equivalence と factorization / uniqueness-on-image witness から minimal consequence-envelope package を構成する。 | `defined only` |
| `SFTTheoremRoadmap.MinimalConsequenceEnvelopePackage.minimal_consequenceEnvelope_factor_unique_on_image` | `theorem` | minimal consequence-envelope package の factor map が selected image 上で一意であることを取り出す。 | `proved accessor` |
| `SFTTheoremRoadmap.ObstructionAwareReviewEquivalence` | `def` | selected review equivalence が obstruction-aware decision projection を尊重することを表す boundary predicate。 | `defined only` |
| `SFTTheoremRoadmap.decisionSoundProjection_of_obstructionAware` | `theorem` | obstruction-aware review equivalence を `DecisionSoundProjection` として読む。 | `proved accessor` |
| `SFTTheoremRoadmap.GovernanceSynthesisPackage.governance_synthesis` | `theorem` | desired-preserving / bad-excluding intervention と hit/miss guard family の同値を取り出す。 | `proved accessor` |
| `SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge` | `structure` | abstract guard/intervention synthesis を finite obstruction witness / desired cone-family surface に接続する bridge。 | `defined only` |
| `SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.synthesized_intervention_of_guard_family` | `theorem` | selected sound guard family から abstract synthesized intervention の存在を取り出す。 | `proved accessor` |
| `SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.guard_family_hits_and_misses` | `theorem` | selected guard family が hit/miss completeness を保持することを取り出す。 | `proved accessor` |
| `SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.selected_bad_matches_synthesis_bad` | `theorem` | selected finite bad witness を synthesis package 側の abstract bad path として読む。 | `proved accessor` |
| `SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.selected_desired_matches_synthesis_desired` | `theorem` | selected desired finite family を synthesis package 側の abstract desired path として読む。 | `proved accessor` |
| `SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.guard_family_hits_selected_bad` | `theorem` | selected bad finite obstruction witness が selected guard family に hit されることを取り出す。 | `proved accessor` |
| `SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.governanceCuttingPackage` | `def` | synthesized intervention を finite governance cutting package として読む。 | `defined only` |
| `SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.obstructionGovernancePackage` | `def` | synthesized cutting package と obstruction package を finite obstruction-governance package として束ねる。 | `defined only` |
| `SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.governanceCuttingPackage_cuts_bad` | `theorem` | synthesized finite package が selected bad obstruction witness を cut することを取り出す。 | `proved accessor` |
| `SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.governanceCuttingPackage_preserves_desired` | `theorem` | synthesized finite package が selected desired cone family を preserve することを取り出す。 | `proved accessor` |
| `SFTTheoremRoadmap.governance_synthesis_of_guard_basis_complete` | `theorem` | complete guard basis と support restriction premise から bad exclusion / desired preservation を得る。 | `proved` |
| `SFTTheoremRoadmap.FiniteRefinementHeight.closedLoopCalibration_fixedPoint_or_boundary_of_finiteHeight` | `theorem` | finite rank descent の下で closed-loop update が fixed point または boundary に到達する。 | `proved` |
| `SFTTheoremRoadmap.FiniteHeightClosedLoopCalibrationBridge` | `structure` | concrete `Nat`-ranked finite refinement height を closed-loop calibration package へ接続する bridge。 | `defined only` |
| `SFTTheoremRoadmap.FiniteHeightClosedLoopCalibrationBridge.closedLoopPackage` | `def` | finite-height bridge を `ClosedLoopCalibrationPackage` として読む。 | `defined only` |
| `SFTTheoremRoadmap.FiniteHeightClosedLoopCalibrationBridge.finiteHeight_closedLoopCalibration_fixedPoint_or_boundary` | `theorem` | finite-height bridge から selected fixed point または boundary expansion への到達を取り出す。 | `proved` |
| `SFTTheoremRoadmap.FiniteHeightClosedLoopCalibrationBridge.RecordsCalibrationBoundary` | `def` | finite-height bridge の selected calibration / evidence boundary を取り出す。 | `defined only` |
| `SFTTheoremRoadmap.FiniteHeightClosedLoopCalibrationBridge.RecordsNonConclusions` | `def` | finite-height bridge と rank-descent skeleton の non-conclusions を保持する。 | `defined only` |
| `SFTTheoremRoadmap.artifact_yoneda_of_separating_probes` | `theorem` | separating probes の下で artifact response equivalence から SFT equivalence を得る。 | `proved` |
| `SFTTheoremRoadmap.agentic_confluence_of_local_normal_forms_and_descent` | `theorem` | descent と unique normal form から fair interleaving convergence を得る。 | `proved` |
| `SFTTheoremRoadmap.FundamentalModularityTheoremPackage.ofTheoremFamily` | `def` | selected theorem family から grand theorem package を構成する。`computablyGoverned` と `typedBoundaryFailureWitness` は別命題として保持し、disjunction witness を package conclusion へ渡す。 | `defined only` |
| `SFTTheoremRoadmap.fundamental_modularity_of_theorem_family` | `theorem` | selected theorem family から governed / failure の二分岐を含む `FundamentalModularityConclusion` を得る。 | `proved` |
| `SFTTheoremRoadmap.FundamentalModularityTheoremPackage.fundamental_modularity` | `theorem` | grand theorem package から modularity と ForecastCone descent の同値を取り出す。 | `proved accessor` |
| `SFTTheoremRoadmap.FundamentalModularityTheoremPackage.bounded_evolution_governed_or_typed_witness` | `theorem` | bounded evolution は governed または typed boundary failure witness を持つ、という package conclusion を取り出す。 | `proved accessor` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_clockedConeDescentPackage`, `atomGeneratedSignature_clockedConeDescent_forecastCone_descent`, `atomGeneratedSignature_modularityRepresentationPackage`, `atomGeneratedSignature_modularity_representation`, `atomGeneratedSignature_fundamentalModularityTheoremPackage`, `atomGeneratedSignature_fundamental_modularity`, `atomGeneratedSignature_fundamental_modularity_nonConclusions` | `def` / `theorem` | Atom-generated carrier 上で clocked descent、modularity representation、fundamental modularity theorem package を instantiate し、non-conclusion boundary を保持する roadmap acceptance。 | `defined only` / `proved` |

## SFT Fundamental Modularity Final Assembly

File: `Formal/Arch/Evolution/SFTFundamentalModularity.lean`

SFT theorem roadmap の各 package surface を、final conservative assembly layer として束ねる。
これは assumption-free full theorem ではなく、descent、typed obstruction、minimal review
envelope、obstruction-cutting governance、closed-loop calibration、agentic confluence などの
explicit package assumptions の下で、bounded selected evolution が governed であるか typed
boundary failure を露出する、という checked assembly を提供する。

Non-conclusions: all software evolution is governed、complete descent failure classification、
all finite covers satisfying descent、full Cech cohomology theorem、operational governance effectiveness、
empirical calibration correctness、global agentic safety、assumption-free Fundamental Modularity theorem
は結論しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `SFTFundamentalModularity.FundamentalEvolutionOutcome` | `inductive` | final assembly の docs-facing outcome vocabulary。 | `defined only` |
| `SFTFundamentalModularity.FundamentalBoundaryFailureKind` | `inductive` | descent failure、unclassified obstruction、uncut governance、review/calibration/agentic/theorem-family boundary などの typed failure kind。 | `defined only` |
| `SFTFundamentalModularity.TypedComputationBoundaryFailure` | `structure` | typed boundary failure kind、broken-boundary explanation、evidence boundary、non-conclusions を束ねる。 | `defined only` |
| `SFTFundamentalModularity.TypedComputationBoundaryFailure.ofKind` | `def` | explicit kind / explanation / evidence boundary / non-conclusions から typed boundary failure witness を作る generic constructor。 | `defined only` |
| `SFTFundamentalModularity.TypedComputationBoundaryFailure.ofKind_records_kind` | `theorem` | generic constructor が requested failure kind を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.ComputablyGoverned` | `structure` | descent、obstruction handling、minimal envelope、governance cutting、closed-loop settling、agentic confluence を読める governed-side package。 | `defined only` |
| `SFTFundamentalModularity.FundamentalDescentComponent` | `structure` | modularity-as-descent と ForecastCone descent の selected equivalence boundary を保持する。 | `defined only` |
| `SFTFundamentalModularity.FundamentalObstructionComponent` | `structure` | technical debt as obstruction と typed failure witness availability を保持する。 | `defined only` |
| `SFTFundamentalModularity.FundamentalReviewComponent` | `structure` | minimal decision-preserving envelope component。 | `defined only` |
| `SFTFundamentalModularity.FundamentalGovernanceComponent` | `structure` | obstruction cutting と desired-family preservation component。 | `defined only` |
| `SFTFundamentalModularity.FundamentalCalibrationComponent` | `structure` | boundary-explicit fixed point と fixed-point-or-boundary expansion component。 | `defined only` |
| `SFTFundamentalModularity.FundamentalAgenticComponent` | `structure` | agentic confluence と fair interleaving convergence component。 | `defined only` |
| `SFTFundamentalModularity.FundamentalModularityHypotheses` | `structure` | final assembly に必要な component packages と explicit proof assumptions を束ねる。agentic confluence assumption と governed-side availability bridge も保持する。 | `defined only` |
| `SFTFundamentalModularity.FundamentalModularityHypotheses.ofDischargedComponents` | `def` | discharged selected component propositions と governed-or-failure branch から final hypotheses を組み立てる staged constructor。 | `defined only` |
| `SFTFundamentalModularity.roadmapConclusion_of_hypotheses` | `def` | final hypotheses から既存 `SFTTheoremRoadmap.FundamentalModularityConclusion` を構成する。 | `defined only` |
| `SFTFundamentalModularity.roadmapPackage_of_hypotheses` | `def` | final hypotheses から既存 `SFTTheoremRoadmap.FundamentalModularityTheoremPackage` を構成する。 | `defined only` |
| `SFTFundamentalModularity.fundamental_modularity_final_assembly` | `theorem` | explicit hypotheses の下で theorem-family components、agentic confluence、governed-or-typed-failure conclusion を組み上げる。 | `proved accessor / assembly theorem` |
| `SFTFundamentalModularity.final_bounded_evolution_governed_or_typed_failure` | `theorem` | final hypotheses から governed または typed boundary failure の disjunction を取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.final_agentic_confluence` | `theorem` | final hypotheses から selected agentic confluence assumption を取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.final_governed_agenticConfluenceAvailable` | `theorem` | final hypotheses の bridge から governed-side agentic confluence availability を取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.final_modularity_iff_forecastConeDescent` | `theorem` | assembled roadmap package が modularity と ForecastCone descent の同値を記録することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.final_assembly_preserves_component_nonConclusions` | `theorem` | final assembly が component non-conclusions を保持し、assumption-free / empirical / operational / AI-safety claim へ昇格しないことを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.hypotheses_ofDischargedComponents_records_finalAssembly` | `theorem` | staged constructor で作った hypotheses から final selected assembly を即座に回収する。 | `proved accessor` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem` | `structure` | `FiniteExactSFTModel`、selected source / horizon、final hypotheses、exact-model boundary、non-conclusions を束ねる finite selected final theorem package。 | `defined only` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.roadmapConclusion` | `def` | finite selected package から assembled roadmap conclusion を取り出す。 | `defined only` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.roadmapPackage` | `def` | finite selected package から assembled roadmap theorem package を取り出す。 | `defined only` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.RecordsExactModelBoundary` | `def` | exact cover / finite model / observation / governance / theorem boundary を保持する。 | `defined only` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.RecordsNonConclusions` | `def` | finite exact model と final package の non-conclusions を保持する。 | `defined only` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.records_nonConclusions_preserved` | `theorem` | finite selected final package の exact-model / component non-conclusion records を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.records_exactCoverBoundary` | `theorem` | finite selected final package が exact cover boundary を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.records_finiteModelBoundary` | `theorem` | finite selected final package が finite model boundary を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.finiteSelected_fundamental_modularity` | `theorem` | finite exact model / selected source / horizon に相対化された final assembly theorem。 | `proved accessor / assembly theorem` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.governed_or_typed_failure` | `theorem` | finite selected bounded evolution が governed または typed boundary failure を持つことを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.modularity_iff_forecastConeDescent` | `theorem` | finite selected package が modularity と ForecastCone descent の同値を記録することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.FiniteExactQuantifiedFundamentalModularityTheorem` | `structure` | finite exact model 上で selected source / horizon ごとの finite selected theorem と quantified boundary / non-conclusions を束ねる wrapper。 | `defined only` |
| `SFTFundamentalModularity.FiniteExactQuantifiedFundamentalModularityTheorem.selectedPackage` | `def` | quantified wrapper から指定 source / horizon の finite selected theorem package を取り出す。 | `defined only` |
| `SFTFundamentalModularity.FiniteExactQuantifiedFundamentalModularityTheorem.selected_fundamental_modularity` | `theorem` | quantified wrapper の各 selected source / horizon で finite selected final assembly theorem を取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.FiniteExactQuantifiedFundamentalModularityTheorem.RecordsQuantifiedBoundary` | `def` | quantified theorem が finite exact model / selected source / horizon に相対化される boundary を保持する。 | `defined only` |
| `SFTFundamentalModularity.FiniteExactQuantifiedFundamentalModularityTheorem.RecordsNonConclusions` | `def` | quantified wrapper が assumption-free / all-covers / empirical / AI-safety claim に昇格しない boundary を保持する。 | `defined only` |
| `SFTFundamentalModularity.descentComponent_of_finiteSelectedDescentPackage` | `def` | selected finite ForecastCone descent package を final descent component として読む。 | `defined only` |
| `SFTFundamentalModularity.descentComponent_of_finiteExactDescentAssumptions` | `def` | finite exact descent assumptions から final descent component を構成する。 | `defined only` |
| `SFTFundamentalModularity.descentComponent_of_h1FiniteDescentAssumptions` | `def` | H1 finite descent assumptions から final descent component を構成する。 | `defined only` |
| `SFTFundamentalModularity.descentComponent_records_h1FiniteDescent` | `theorem` | H1 finite-descent assumptions 由来の final descent component が selected finite descent package と H1 / non-conclusion boundary を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.descentComponent_of_goodFiniteCover` | `def` | good finite cover sufficient condition を final descent component として読む。 | `defined only` |
| `SFTFundamentalModularity.descentComponent_records_goodFiniteCover` | `theorem` | good finite cover sufficient condition 由来の final descent component が selected finite descent を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.descentComponent_records_goodFiniteCover_nonConclusions` | `theorem` | good finite cover 由来の final descent component が non-conclusion boundary を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.obstructionComponent_of_finiteDescentObstructionPackage` | `def` | finite classifier package を final obstruction component として読む。 | `defined only` |
| `SFTFundamentalModularity.obstructionComponent_records_finite_witness` | `theorem` | final obstruction component が selected finite failure の typed witness availability を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.obstructionComponent_of_finiteExactFailureClassifierCompleteness` | `def` | finite exact classifier completeness package を final obstruction component として読む。 | `defined only` |
| `SFTFundamentalModularity.obstructionComponent_records_finiteExact_failureKind_matrix` | `theorem` | final obstruction component 側から finite exact classifier の failure-kind coverage matrix を取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.ofFiniteExactComponents` | `def` | finite exact model boundary と final hypotheses から finite selected final theorem package を構成する。 | `defined only` |
| `SFTFundamentalModularity.finiteSelected_ofFiniteExactComponents_records_finalAssembly` | `theorem` | constructor-built finite selected package から final assembly theorem を取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.governanceComponent_of_finiteObstructionGovernance` | `def` | finite obstruction governance package を final governance component として読む bridge。 | `defined only` |
| `SFTFundamentalModularity.governanceComponent_of_finiteExactGovernanceSoundness` | `def` | finite exact governance-cutting soundness package を final governance component として読む bridge。 | `defined only` |
| `SFTFundamentalModularity.governanceComponent_records_finiteExact_cut` | `theorem` | finite exact governance component が selected bad-witness cutting を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.governanceComponent_records_finiteExact_desired_preservation` | `theorem` | finite exact governance component が desired-family preservation を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.governanceComponent_of_finiteGovernanceSynthesisBridge` | `def` | finite governance synthesis bridge を final governance component として読む。 | `defined only` |
| `SFTFundamentalModularity.governanceComponent_records_synthesis_cut` | `theorem` | synthesis bridge 由来の final governance component が selected bad-witness cutting を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.governanceComponent_records_synthesis_desired_preservation` | `theorem` | synthesis bridge 由来の final governance component が desired-family preservation を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.governanceComponent_records_synthesis_guard_family` | `theorem` | synthesis bridge 由来の final governance component が selected guard family の hit/miss witness を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.reviewComponent_of_minimalEnvelopePackage` | `def` | minimal consequence-envelope package を final review component として読む bridge。 | `defined only` |
| `SFTFundamentalModularity.reviewComponent_records_minimalEnvelope` | `theorem` | minimal envelope package 由来の final review component から `minimalDecisionPreservingEnvelope` を取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.reviewComponent_records_minimalEnvelope_boundary` | `theorem` | minimal envelope package 由来の final review component が review boundary を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.reviewComponent_records_minimalEnvelope_nonConclusions` | `theorem` | minimal envelope package 由来の final review component が non-conclusions を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.FiniteObstructionAwareReviewEnvelopeBridge` | `structure` | finite selected obstruction review projection と minimal consequence-envelope universal property を接続する bridge。 | `defined only` |
| `SFTFundamentalModularity.FiniteObstructionAwareReviewEnvelopeBridge.obstructionDecision_factors` | `theorem` | selected obstruction decision projection が minimal envelope を通じて factor することを示す。 | `proved accessor` |
| `SFTFundamentalModularity.reviewComponent_of_obstructionAwareEnvelopeBridge` | `def` | obstruction-aware minimal envelope bridge を final review component として読む。 | `defined only` |
| `SFTFundamentalModularity.reviewComponent_records_obstructionAware_minimalEnvelope` | `theorem` | final review component が obstruction-aware factorization を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.reviewComponent_records_obstructionAware_boundary` | `theorem` | obstruction-aware bridge 由来の final review component が bridge / envelope / decision boundary を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.reviewComponent_records_obstructionAware_nonConclusions` | `theorem` | obstruction-aware bridge 由来の final review component が non-conclusions を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.FiniteReviewGovernanceCuttingBridge` | `structure` | obstruction-aware review envelope と governance synthesis が同じ selected obstruction family を参照することを記録する bridge。 | `defined only` |
| `SFTFundamentalModularity.FiniteReviewGovernanceCuttingBridge.records_sameSelectedObstructionFamily` | `theorem` | review / governance bridge の same-selected-obstruction-family boundary を取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.FiniteReviewGovernanceCuttingBridge.RecordsNonConclusions` | `def` | review / governance bridge、review side、governance side の non-conclusion boundary を束ねる。 | `defined only` |
| `SFTFundamentalModularity.reviewComponent_of_reviewGovernanceCuttingBridge` | `def` | review-governance bridge の review side を final review component として読む。 | `defined only` |
| `SFTFundamentalModularity.governanceComponent_of_reviewGovernanceCuttingBridge` | `def` | review-governance bridge の governance side を final governance component として読む。 | `defined only` |
| `SFTFundamentalModularity.reviewGovernanceCuttingBridge_records_components` | `theorem` | selected review-governance bridge から final review component と final governance cutting component を同時に取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.calibrationComponent_of_closedLoopPackage` | `def` | closed-loop calibration package を final calibration component として読む bridge。 | `defined only` |
| `SFTFundamentalModularity.calibrationComponent_records_boundaryExplicit` | `theorem` | closed-loop package 由来の final calibration component が `boundaryExplicitFixedPoint` を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.calibrationComponent_records_fixedPointOrBoundary` | `theorem` | closed-loop package 由来の final calibration component が fixed point または boundary expansion を記録する。 | `proved accessor` |
| `SFTFundamentalModularity.calibrationComponent_records_closedLoop_nonConclusions` | `theorem` | closed-loop package 由来の final calibration component が non-conclusions を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.calibrationComponent_of_finiteHeightClosedLoopBridge` | `def` | finite-height closed-loop calibration bridge を final calibration component として読む bridge。 | `defined only` |
| `SFTFundamentalModularity.calibrationComponent_records_finiteHeight_fixedPointOrBoundary` | `theorem` | finite-height bridge 由来の final calibration component が fixed point または boundary expansion を記録することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.calibrationComponent_records_finiteHeight_boundary` | `theorem` | finite-height bridge 由来の final calibration component が calibration boundary を明示的に保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.calibrationComponent_records_finiteHeight_boundaryExplicit` | `theorem` | finite-height bridge 由来の final calibration component が `boundaryExplicitFixedPoint` を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.calibrationComponent_records_finiteHeight_nonConclusions` | `theorem` | finite-height bridge 由来の final calibration component が non-conclusions を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.agenticComponent_of_agenticConfluencePackage` | `def` | agentic confluence package の conclusion `FairInterleavingsConverge package.landing` を final agentic component の `agenticConfluence` / `fairInterleavingsConverge` として読む bridge。 | `defined only` |
| `SFTFundamentalModularity.agenticComponent_records_agenticConfluence` | `theorem` | package assumptions から final agentic component の `agenticConfluence` conclusion を取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.agenticComponent_records_confluence` | `theorem` | package assumptions から final agentic component の `fairInterleavingsConverge` conclusion を取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.agenticComponent_records_agentBoundary` | `theorem` | agentic package 由来の final agentic component が agent boundary を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.agenticComponent_records_nonConclusions` | `theorem` | agentic package 由来の final agentic component が non-conclusions を保持する。 | `proved accessor` |
| `SFTFundamentalModularity.agenticComponent_governedAvailability` | `theorem` | selected agentic confluence と明示 bridge から governed-side `agenticConfluenceAvailable` を取り出す。 | `proved accessor` |
| `SFTAgenticConfluence.ReductionReaches` | `inductive` | selected interleaving reduction の reflexive-transitive closure。 | `defined only` |
| `SFTAgenticConfluence.IsNormal` | `def` | selected reduction step を持たない normal state predicate。 | `defined only` |
| `SFTAgenticConfluence.PairwiseJoinableLanding` | `def` | two selected interleavings が landing を保存する common reduct で join すること。 | `defined only` |
| `SFTAgenticConfluence.NewmanStyleConfluenceKernel` | `structure` | selected reduction relation、normal-form witness、termination/local confluence から pairwise joinability を得る Newman-style kernel。 | `defined only` |
| `SFTAgenticConfluence.NewmanStyleConfluenceKernel.fairInterleavingsConverge_of_pairwiseJoinable` | `theorem` | pairwise joinability から fair interleaving convergence を得る。 | `proved` |
| `SFTAgenticConfluence.NewmanStyleConfluenceKernel.newmanStyle_fairInterleavingsConverge` | `theorem` | selected termination と local confluence から fair interleaving convergence を得る。 | `proved accessor` |
| `SFTAgenticConfluence.NewmanStyleConfluenceKernel.agenticPackage` | `def` | Newman-style kernel を既存 `AgenticConfluencePackage` として読む。 | `defined only` |
| `SFTAgenticConfluence.NewmanStyleConfluenceKernel.agenticPackage_records_newmanStyle_confluence` | `theorem` | kernel 由来 package が Newman-style convergence theorem を保持することを取り出す。 | `proved accessor` |
| `SFTAgenticConfluence.NewmanStyleConfluenceKernel.RecordsAgentBoundary` | `def` | selected agentic proof boundary を取り出す。 | `defined only` |
| `SFTAgenticConfluence.NewmanStyleConfluenceKernel.RecordsNonConclusions` | `def` | selected agentic confluence の non-conclusions を保持する。 | `defined only` |
| `SFTAgenticConfluence.FiniteAgentTeamSemantics` | `structure` | finite agent list、accepted schedule、schedule step、finite-team / schedule boundary を束ねる selected finite agent-team semantics。 | `defined only` |
| `SFTAgenticConfluence.FiniteAgentTeamConfluenceBridge` | `structure` | finite agent-team schedule semantics を Newman-style confluence kernel へ接続する bridge。 | `defined only` |
| `SFTAgenticConfluence.FiniteAgentTeamConfluenceBridge.fairInterleavingsConverge` | `theorem` | finite agent-team bridge から selected fair interleaving convergence を取り出す。unbounded agent-team safety ではない。 | `proved accessor` |
| `SFTAgenticConfluence.FiniteAgentTeamConfluenceBridge.RecordsFiniteAgentBoundary` | `def` | finite team / schedule / accepted-boundary / agent-boundary を保持する。 | `defined only` |
| `SFTFundamentalModularity.agenticComponent_of_newmanStyleConfluenceKernel` | `def` | Newman-style confluence kernel を final agentic component として読む。 | `defined only` |
| `SFTFundamentalModularity.agenticComponent_records_newmanStyle_confluence` | `theorem` | Newman-style final agentic component が fair interleaving convergence を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.agenticComponent_records_newmanStyle_nonConclusions` | `theorem` | Newman-style final agentic component が non-conclusions を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.agenticComponent_of_finiteAgentTeamConfluenceBridge` | `def` | finite agent-team bridge と termination/local-confluence assumptions を final agentic component として読む。 | `defined only` |
| `SFTFundamentalModularity.agenticComponent_records_finiteTeam_confluence` | `theorem` | finite team bridge 由来の final agentic component が selected fair interleaving convergence を保持することを取り出す。 | `proved accessor` |
| `SFTFundamentalModularity.agenticComponent_records_finiteTeam_boundary` | `theorem` | finite team bridge 由来の final agentic component が finite team / schedule / agent boundary を保持することを取り出す。 | `proved accessor` |

## SFT AAT-Supported Fundamental Modularity

File: `Formal/Arch/Evolution/SFTAATFundamentalModularity.lean`
Canonical example file: `Formal/Arch/Evolution/SFTAATFundamentalModularityExamples.lean`

Issue [#1046](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1046) と子 Issue
[#1047](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1047)-
[#1051](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1051)、および follow-up
Issue [#1054](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1054) と
Issue [#1057](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1057)-
[#1062](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1062) では、
AAT の selected architecture slice、AAT theorem status、projection / observation /
reconstruction / missing-evidence boundary、finite selected SFT model、selected source /
horizon を、既存の `FiniteSelectedFundamentalModularityTheorem` へ接続する
AAT-supported theorem package と、AAT/SFT boundary failure kind を final typed conclusion
まで保存する accessor を追加した。さらに review / calibration / agentic component の
discharge helper accessor と、singleton canonical finite AAT-supported example 上の
end-to-end package instantiation を追加した。
Issue [#1064](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1064)
では、この canonical example の descent / obstruction / governance component を
既存 finite selected descent package、finite descent obstruction package、finite
obstruction-governance package 経由の helper construction に寄せた。
Issue [#1066](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1066)
と子 Issue [#1071](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1071),
[#1067](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1067),
[#1068](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1068),
[#1070](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1070),
[#1069](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1069)
では、ArchMap / FieldSig artifact boundary を theorem precondition / boundary evidence として
`AATSupportedSFTBoundary` へ接続する helper と selected finite example を追加した。
Issue [#1072](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1072) と子
Issue [#1073](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1073),
[#1074](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1074),
[#1076](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1076),
[#1077](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1077),
[#1075](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1075)
では、explicit assumption ledger、final failure taxonomy accessors、non-singleton selected
finite example、lifecycle sidecar、evolutionary conclusion-preservation sidecar を追加した。

Non-conclusions: AAT-supported package は assumption-free Grand Theorem、all software
systems / all covers / all runtime schedules、empirical calibration correctness、
operational governance effectiveness、runtime failure prediction、empirical incident risk、
arbitrary refactoring correctness、runtime behavior equivalence、global AI safety、
source-observation layer は AAT theorem package の外で扱う。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `SFTAATFundamentalModularity.AATSelectedArchitectureSlice` | `structure` | selected architecture slice と projection / observation / reconstruction / missing-evidence / theorem-status / non-conclusion boundary を束ねる。 | `defined only` |
| `SFTAATFundamentalModularity.AATSelectedArchitectureSlice.archMap_records_selectedArchitecture` | `theorem` | ArchMap preservation package から selected architecture slice evidence を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSelectedArchitectureSlice.archMap_records_projectionBoundary` | `theorem` | ArchMap-derived slice が object / relation preservation と forgetting / unsupported-relation boundary を保持することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSelectedArchitectureSlice.archMap_records_observationBoundary` | `theorem` | ArchMap-derived slice が coverage / exactness boundary を保持することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSelectedArchitectureSlice.archMap_records_reconstructionBoundary` | `theorem` | ArchMap-derived slice が semantic diagram / commutation / nonfillability witness preservation を保持することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSelectedArchitectureSlice.archMap_records_missingEvidence` | `theorem` | ArchMap-derived slice が semantic coverage gap boundary を missing-evidence boundary として保持することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSelectedArchitectureSlice.archMap_records_theoremStatusBoundary` | `theorem` | ArchMap-derived slice が formal promotion guardrail を theorem-status boundary として保持することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSelectedArchitectureSlice.archMap_preserves_nonConclusions` | `theorem` | ArchMap-derived slice が non-conclusions を保存することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSelectedArchitectureSlice.ArchMapAATHomomorphicReading` | `def` | ArchMap-derived selected slice の architecture / projection / observation / reconstruction / missing-evidence / theorem-status / non-conclusion boundary を AAT homomorphic reading として束ねる。 | `defined only` |
| `SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary` | `structure` | `ArchSigSFTReportEstimateBoundary` と report-side facts を束ねる SFT report / forecast boundary package。 | `defined only` |
| `SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary.report_preserves_observationBoundary` | `theorem` | ArchSig-derived report boundary が selected estimate の observation boundary を保持する。 | `proved accessor` |
| `SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary.report_preserves_reconstructionBoundary` | `theorem` | ArchSig-derived report boundary が selected estimate の reconstruction boundary を保持する。 | `proved accessor` |
| `SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary.report_missing_invariants_remain_missingEvidence` | `theorem` | missing invariants を selected estimate の missing-evidence boundary として保持する。 | `proved accessor` |
| `SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary.report_preserves_theoremBoundary` | `theorem` | ArchSig report の theorem boundary が SFT forecast status 側に残ることを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary.report_boundary_remains_toolingBoundary` | `theorem` | ArchSig report boundary が SFT tooling boundary として残ることを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary.report_boundary_does_not_strengthen_theorem_status` | `theorem` | ArchSig-derived report boundary が theorem status を強めないことを theorem-boundary accessor として示す。 | `proved accessor` |
| `SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary.report_boundary_does_not_calibrate_forecast` | `theorem` | ArchSig-derived report boundary が calibrated forecast correctness を結論せず forecast boundary を残す。 | `proved accessor` |
| `SFTAATFundamentalModularity.ArchMapAATSFTHomomorphicBoundary` | `def` | ArchMap-derived AAT homomorphic reading と ArchSig-derived SFT estimate / forecast boundary reading を合わせた AAT/SFT homomorphic boundary。 | `defined only` |
| `SFTAATFundamentalModularity.archMap_archSig_aatSftHomomorphicBoundary` | `theorem` | ArchMap preservation package と ArchSig-derived report boundary から combined AAT/SFT homomorphic boundary を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary` | `structure` | selected AAT slice、`AATTheoremStatus`、`SFTForecastStatus`、`AATToSFTInterfaceBoundary`、`FiniteExactSFTModel`、selected source / horizon を束ねる AAT-supported SFT boundary package。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofSelectedSliceAndFiniteExactModel` | `def` | selected slice、interface boundary、finite exact model boundary records から `AATSupportedSFTBoundary` を構成する constructor helper。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInput` | `def` | selected slice / finite exact model boundary records は明示したまま、AAT theorem status を `GeneratedSFTInput.theoremStatus` から埋める constructor helper。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInput_aatStatus_eq_generated` | `theorem` | generated constructor が stored `aatStatus` として generated SFT input の theorem status を保持すること。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInput_reads_generated_status_as_local_premise` | `theorem` | generated constructor 経由でも generated AAT theorem status が SFT local premise として読まれること。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition` | `def` | `GeneratedSFTInput` と `GeneratedArchSigAATCoreTransition` から AAT status、ArchSig report boundary、theorem boundary、typed-failure boundary、non-conclusion boundary を構成する generated handoff constructor。selected slice / finite exact model boundary records は引き続き明示前提として残す。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition_aatStatus_eq_generated`, `ofGeneratedSFTInputAndArchSigTransition_records_archsig_boundary`, `ofGeneratedSFTInputAndArchSigTransition_records_theorem_boundary`, `ofGeneratedSFTInputAndArchSigTransition_records_typed_failure_boundary`, `ofGeneratedSFTInputAndArchSigTransition_records_nonConclusions` | `theorem` | generated handoff constructor が generated theorem status、generated ArchSig transition boundary、generated theorem/status boundary、ArchSig non-definition typed-failure boundary、generated non-conclusion boundary を保持することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofArchMapAndArchSigBoundaries` | `def` | ArchMap-derived selected slice と ArchSig-derived SFT report boundary から `AATSupportedSFTBoundary` を構成する higher-level constructor。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.RecordsSelectedFiniteBoundary` | `def` | selected architecture slice、finite selected model、selected source、selected horizon の相対化 boundary を保持する。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.RecordsAATSliceBoundaries` | `def` | projection / observation / reconstruction / missing-evidence boundary を保持する。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.RecordsTheoremAndModelBoundaries` | `def` | exact cover / observation / theorem / ArchSig report / typed failure boundary を保持する。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.RecordsNonConclusions` | `def` | AAT slice、AAT theorem status、SFT forecast status、finite exact model の non-conclusions を保持する。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.aat_status_as_sft_local_premise` | `theorem` | AAT theorem status を SFT local premise として読む accessor。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_projection_observation_reconstruction_missingEvidence` | `theorem` | AAT projection / observation / reconstruction / missing-evidence boundary を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_selected_finite_source_horizon` | `theorem` | AAT-supported package が selected / finite / source-horizon-relative であることを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_selected_source_boundary` | `theorem` | selected source boundary を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_selected_horizon_boundary` | `theorem` | selected horizon boundary を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_aat_projection_boundary` | `theorem` | AAT projection boundary を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_aat_observation_boundary` | `theorem` | AAT observation boundary を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_aat_reconstruction_boundary` | `theorem` | AAT reconstruction boundary を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_aat_missingEvidence_boundary` | `theorem` | AAT missing-evidence boundary を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.preserves_nonConclusions` | `theorem` | AAT / SFT / finite exact model の non-conclusions を保存する。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_report_and_theorem_status_boundaries` | `theorem` | ArchSig report boundary と AAT/SFT theorem-status boundary を混同せずに theorem/model boundary record として取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.constructor_preserves_nonConclusions` | `theorem` | constructor helper 経由でも AAT/SFT/finite exact model の non-conclusions が保存されることを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.artifact_constructor_records_archMap_boundaries` | `theorem` | artifact constructor 経由で作った boundary から ArchMap-derived projection / observation / reconstruction / missing-evidence boundary を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.artifact_constructor_reads_aat_status_as_sft_local_premise` | `theorem` | artifact constructor 経由で作った boundary でも AAT theorem status を SFT local premise として読む accessor。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedSFTBoundary.artifact_constructor_preserves_nonConclusions` | `theorem` | artifact constructor 経由でも ArchMap / AAT / SFT / finite exact model の non-conclusions が保存されることを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailureKind` | `inductive` | expression / projection / observation / reconstruction / missing evidence / theorem status / ArchSig report の AAT/SFT boundary failure vocabulary。 | `defined only` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailure` | `structure` | AAT/SFT boundary failure witness と evidence boundary / non-conclusions を束ねる。 | `defined only` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailure.ofKind` | `def` | explicit AAT/SFT failure kind と evidence payload から kind-preserving boundary failure witness を構成する generic constructor。 | `defined only` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailure.ofKind_records_kind` | `theorem` | generic constructor が requested AAT/SFT failure kind を保持することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailure.toTypedComputationBoundaryFailure` | `def` | AAT/SFT boundary failure を `TypedComputationBoundaryFailure` として読む bridge。 | `defined only` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailure.AATTypedComputationBoundaryFailure` | `structure` | typed SFT failure と、その由来である AAT/SFT boundary failure kind を一緒に保持する refined wrapper。 | `defined only` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailure.toAATTypedComputationBoundaryFailure` | `def` | AAT/SFT boundary failure を kind-preserving refined typed failure として読む bridge。 | `defined only` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailure.toTypedComputationBoundaryFailure_explains` | `theorem` | typed failure bridge が broken-boundary witness を保存する。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailure.toTypedComputationBoundaryFailure_preserves_nonConclusions` | `theorem` | typed failure bridge が non-conclusions を保存する。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailure.toAATTypedComputationBoundaryFailure_records_kind` | `theorem` | refined typed failure が AAT/SFT boundary failure kind を潰さず保持することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailure.toAATTypedComputationBoundaryFailure_preserves_explanation` | `theorem` | refined typed failure が broken-boundary witness を保存する。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSFTBoundaryFailure.toAATTypedComputationBoundaryFailure_preserves_nonConclusions` | `theorem` | refined typed failure が non-conclusions を保存する。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage` | `structure` | AAT-supported boundary と `FiniteSelectedFundamentalModularityTheorem` を束ねる final package。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.ofBoundaryAndFiniteSelectedHypotheses` | `def` | AAT-supported boundary と explicit final hypotheses から AAT-supported final package を構成する。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.ExplicitAssumptionLedger` | `structure` | selected finite boundary、selected source / horizon、AAT slice boundaries、theorem/model boundaries、final component hypotheses、final typed conclusion、non-conclusion boundary を束ねる Grand Theorem assumption ledger。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.explicitAssumptionLedger` | `def` | package と selected source / horizon evidence から explicit assumption ledger を構成する。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.explicitAssumptionLedger_supports_final_typed_conclusion` | `theorem` | ledger から final component hypotheses と final typed conclusion の対応を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.explicitAssumptionLedger_supports_nonConclusion_boundary` | `theorem` | ledger から selected/AAT/theorem/model boundaries と non-conclusion preservation の対応を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.finiteSelected_fundamental_modularity` | `theorem` | AAT-supported package から finite selected final assembly conclusion を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.governed_or_typed_boundary_failure` | `theorem` | governed-or-typed-boundary-failure conclusion を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.AATSupportedFinalTypedConclusion` | `def` | governed / existing finite typed failure / AAT-SFT boundary failure の三分岐 final typed conclusion。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.finite_failure_enters_final_typed_conclusion` | `theorem` | existing finite SFT typed failure が三分岐 final typed conclusion の finite failure branch に入ることを示す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.final_typed_conclusion_records_finite_or_aat_failure_taxonomy` | `theorem` | final typed conclusion が governed / finite SFT typed failure / AAT-SFT boundary failure の taxonomy を保持することを読む accessor。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.governed_or_finite_failure_or_aat_boundary_failure` | `theorem` | AAT-supported package から governed または existing finite typed failure の branch を三分岐 conclusion として取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.aat_boundary_failure_enters_final_typed_conclusion` | `theorem` | 明示された AAT/SFT boundary failure witness が三分岐 final typed conclusion の AAT/SFT branch に入ることを示す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.aat_boundary_failure_kind_preserved_in_final_typed_conclusion` | `theorem` | final typed conclusion に入る AAT/SFT boundary failure branch が failure kind を保持することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.aat_boundary_failure_nonConclusions_preserved_in_final_typed_conclusion` | `theorem` | final typed conclusion に入る AAT/SFT boundary failure branch が non-conclusions を保持することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.final_failure_taxonomy_preserves_nonConclusions` | `theorem` | finite/AAT failure taxonomy reading と boundary/final non-conclusion preservation を同時に保持する。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.modularity_iff_forecastConeDescent` | `theorem` | modularity-as-ForecastCone-descent conclusion を取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.does_not_promote_to_unconditional_claim` | `theorem` | AAT-supported package が non-conclusions を保持し、無条件 theorem / empirical / operational / AI-safety claim へ昇格しない boundary theorem。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.LifecycleTypedFailureSidecar` | `structure` | lifecycle bifurcation を final typed conclusion の sidecar として読む record。runtime / empirical claim には昇格しない。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.lifecycleTypedFailureSidecar_of_threshold` | `def` | lifecycle threshold 以上の evidence から lifecycle sidecar を構成し、pressure regime と non-conclusions を保持する。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.lifecycleTypedFailureSidecar_records_final_typed_conclusion` | `theorem` | lifecycle sidecar が final typed conclusion を保持することを取り出す。runtime prediction ではない。 | `proved accessor` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.AllowedGrandTheoremTransformation` | `structure` | AAT-supported package 間の allowed transformation が final typed conclusion と non-conclusion boundary を保存することを明示前提として束ねる。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.EvolutionaryConclusionPreservation` | `structure` | evolutionary invariance package と allowed transformation の下で、target package の final conclusion / non-conclusion preservation を読む sidecar。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.evolutionaryConclusionPreservation_of_allowedTransformation` | `def` | ForecastCone equivalence と allowed transformation から evolutionary conclusion-preservation sidecar を構成する。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.FieldShapingConclusionSidecar` | `structure` | field-shaping conclusion と AAT-supported final typed conclusion を sidecar として同時に保持する record。empirical outcome preservation には昇格しない。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.fieldShapingConclusionSidecar_of_fixedPointPackage` | `def` | fixed-point field-shaping package と minimality premise から final typed conclusion sidecar を構成する。 | `defined only` |
| `SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.fieldShapingConclusionSidecar_records_final_typed_conclusion` | `theorem` | field-shaping sidecar が AAT-supported final typed conclusion を保持することを取り出す。 | `proved accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalAATSupportedBoundary` | `def` | singleton finite exact model、selected source、horizon 1、AAT selected slice から構成した canonical AAT-supported boundary。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalAATSupportedBoundary_reads_aat_status_as_local_premise` | `theorem` | canonical AAT-supported boundary が AAT theorem status を SFT local premise として読むことを取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary` | `def` | Atom-generated Signature acceptance の `GeneratedSFTInput` と generated ArchSig transition evidence を singleton finite exact model 上の AAT-supported SFT boundary へ渡す example。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary_aatStatus_eq_generated` | `theorem` | canonical generated AAT-supported boundary が generated theorem status を保持すること。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary_reads_generated_status_as_local_premise` | `theorem` | canonical generated AAT-supported boundary が generated theorem status を SFT local premise として読むこと。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary_records_archsig_transition_boundary`, `canonicalGeneratedAATSupportedBoundary_records_generated_theorem_boundary`, `canonicalGeneratedAATSupportedBoundary_records_typed_failure_boundary`, `canonicalGeneratedAATSupportedBoundary_records_nonConclusions_from_generated_transition` | `theorem` | canonical generated boundary が ArchSig / FieldSig handoff の report / theorem / typed-failure / non-conclusion boundary を generated ArchSig transition evidence から読んでいることを取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedFundamentalModularityPackage`, `canonicalGeneratedAATSupported_final_typed_conclusion`, `canonicalGeneratedAATSupported_preserves_nonConclusions` | `def` / `theorem` | generated SFT input と generated ArchSig transition evidence 由来の AAT-supported boundary から、明示的 final hypotheses の下で selected final package / final typed conclusion / non-conclusions preservation を取り出す。 | `defined only` / `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.artifactSoftwareFieldEstimate` | `def` | ArchSig-like selected report example が保持する singleton `SoftwareFieldEstimate`。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.artifactArchSigReport` | `def` | selected estimate と report / theorem / forecast / non-conclusion boundary を持つ small ArchSig-like report example。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.artifactDerivedReportBoundary` | `def` | small ArchSig-like report を SFT report / forecast boundary として読む derived boundary package。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalArtifactSupportedBoundary` | `def` | ArchMap preservation package と ArchSig-derived report boundary から canonical finite `AATSupportedSFTBoundary` を構成する artifact-boundary example。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalArtifactSupportedBoundary_records_artifact_slice` | `theorem` | artifact-boundary example から ArchMap-derived AAT slice boundary を取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalArtifactSupportedBoundary_records_report_boundary` | `theorem` | artifact-boundary example から ArchSig report boundary を取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalArtifactSupportedBoundary_preserves_nonConclusions` | `theorem` | artifact-boundary example の boundary non-conclusions preservation を取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalFiniteSelectedDescentPackage` | `def` | singleton model 上の finite selected ForecastCone descent package。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalDescentComponent` | `def` | `descentComponent_of_finiteSelectedDescentPackage` 経由で構成した canonical descent component。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalDescentComponent_records_finiteSelectedDescent` | `theorem` | canonical descent component が selected finite descent を保持することを取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalObstructionPackage` | `def` | singleton model 上の finite descent obstruction classifier package。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalObstructionComponent` | `def` | `obstructionComponent_of_finiteDescentObstructionPackage` 経由で構成した canonical obstruction component。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalObstructionComponent_records_finite_witness` | `theorem` | canonical obstruction component が typed finite witness availability を保持することを取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalObstructionGovernancePackage` | `def` | singleton model 上の finite obstruction-governance package。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalGovernanceComponent` | `def` | `governanceComponent_of_finiteObstructionGovernance` 経由で構成した canonical governance component。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalGovernanceComponent_records_finite_cut` | `theorem` | canonical governance component が selected bad-witness cutting を保持することを取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalAATSupportedFundamentalModularityPackage` | `def` | canonical finite AAT-supported boundary と component discharge helper 由来 hypotheses から構成した end-to-end package。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalArtifactSupportedFundamentalModularityPackage` | `def` | artifact boundary から canonical finite AAT-supported Grand Theorem package へ到達する end-to-end package。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.canonicalAATSupported_fundamental_modularity` | `theorem` | canonical package から finite selected final assembly conclusion を取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalAATSupported_governed_or_typed_boundary_failure` | `theorem` | canonical package から governed-or-typed-boundary-failure conclusion を取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalAATSupported_final_typed_conclusion` | `theorem` | canonical package から AAT-supported final typed conclusion を取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalAATSupported_preserves_nonConclusions` | `theorem` | canonical package が boundary / final package non-conclusions を保存することを取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalArtifactSupported_final_typed_conclusion` | `theorem` | artifact-boundary package から AAT-supported final typed conclusion を取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.canonicalArtifactSupported_preserves_nonConclusions` | `theorem` | artifact-boundary package が boundary / final package non-conclusions を保存することを取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.nonSingletonCover_has_two_indices` | `theorem` | non-singleton selected finite example の cover index carrier が長さ 2 であることを確認する。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.nonSingletonExactModel` | `def` | `Bool` carriers 上の non-singleton selected finite exact model。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.nonSingletonExactModel_has_two_global_points` | `theorem` | non-singleton selected finite exact model の selected global carrier が長さ 2 であることを確認する。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.nonSingletonAATSupportedFundamentalModularityPackage` | `def` | non-singleton selected finite exact model 上で AAT-supported package を end-to-end instantiate する example。 | `defined only` |
| `SFTAATFundamentalModularity.Examples.nonSingletonAATSupported_fundamental_modularity` | `theorem` | non-singleton package から finite selected final assembly conclusion を取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.nonSingletonAATSupported_final_typed_conclusion` | `theorem` | non-singleton package から AAT-supported final typed conclusion を取り出す。 | `proved example accessor` |
| `SFTAATFundamentalModularity.Examples.nonSingletonAATSupported_preserves_nonConclusions` | `theorem` | non-singleton package が boundary / final package non-conclusions を保存することを取り出す。 | `proved example accessor` |

## SFT Theorem Package Entrypoint

File: `Formal/Arch/Evolution/SFTTheoremPackages.lean`

Issue [#916](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/916) では、
#907 / #913 配下で分割実装された SFT Lean core を、docs-facing theorem package entrypoint
として束ねた。`SFTTheoremPackages` は横断 import surface と metadata を提供するだけで、
未実装 theorem を `proved` に昇格しない。Part III / IV の schematic statement と既存
bounded Lean API の対応、代表 declaration、non-conclusion boundary を追跡する。AAT interface
candidate は `GeneratedSFTInput.theoremStatus`、
`GeneratedSFTInput.theoremStatusFromGenerated`、
`GeneratedSFTInput.measured_zero_from_generated`、
`GeneratedSFTInput.reads_generated_aat_as_sft_local_premise` も代表 declaration として含め、
SFT handoff が hand-authored `AATTheoremStatus` だけに見えないようにする。

Non-conclusions: この entrypoint は empirical calibration、tooling extraction completeness、
global future trajectory safety、market / human-intention prediction、ArchSig report の
Lean theorem witness 化を結論しない。

| Name | Kind | Description | Status |
| --- | --- | --- | --- |
| `SFTTheoremPackages.SchematicCorrespondence` | `structure` | SFT schematic statement と対応する Lean declaration、bounded reading、status を保持する docs-facing metadata row。 | `defined only` |
| `SFTTheoremPackages.Candidate` | `inductive` | SFT theorem-package group。`SoftwareField`, `ForecastCone`, cone projection, artifact action, policy / governance, reachability, support safety, `FieldUpdate`, `ConsequenceEnvelope`, AAT interface boundary, ArchSig report boundary, counterexample package, theorem roadmap を列挙する。 | `defined only` |
| `SFTTheoremPackages.Candidate.sftSection` | `def` | candidate が主に対応する SFT source section を返す。 | `defined only` |
| `SFTTheoremPackages.Candidate.schematicName` | `def` | docs / website status で使う stable schematic name を返す。 | `defined only` |
| `SFTTheoremPackages.Candidate.representativeDeclarations` | `def` | candidate ごとの代表 Lean declaration 名を返す public entrypoint metadata。 | `defined only` |
| `SFTTheoremPackages.Candidate.schematicCorrespondences` | `def` | Part III / IV statement と既存 bounded Lean API の読み替えを列挙する。 | `defined only` |
| `SFTTheoremPackages.Candidate.nonConclusionBoundary` | `def` | candidate ごとの non-conclusion boundary summary を返す。 | `defined only` |
| `SFTTheoremPackages.Candidate.representativeDeclarations SFTTheoremPackages.Candidate.aatInterfaceBoundary` | `def` | AAT interface boundary の代表 declaration に Atom-generated SFT handoff wrapper 群を含める。 | `defined only` |

## Signature Dynamics

File: `Formal/Arch/Evolution/SignatureDynamics.lean`

Issue [#638](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/638) の対象範囲は、
Architecture Signature Dynamics の最小 Lean core として、AI patch distribution、GitHub PR、
dataset schema に依存しない observation / trajectory / delta schema を切ることである。
Issue [#640](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/640) では、
selected additive delta law に相対化して net delta の telescoping theorem を追加した。
Issue [#641](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/641) では、
selected safe region と stepwise preservation assumption に相対化して、
observed trajectory が safe region 内に留まる theorem を追加した。
Issue [#639](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/639) では、
two-step の観測可換性と bounded merge-order sensitivity を定義し、可換なら sensitivity が
0 になる theorem と、小さい非可換 counterexample を追加した。
Issue [#637](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/637) では、
finite observed trajectory と selected region に相対化した attractor candidate、
finite initial-state list と bounded operation script に相対化した basin candidate、
および deterministic self-map の eventually periodic future proof obligation を追加した。
Issue [#657](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/657) では、
explicit finite state universe と mathlib の finite pigeonhole principle に接続し、
deterministic self-map の eventually periodic theorem を証明した。
Issue [#658](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/658) では、
finite observed suffix に相対化した bounded recurrence predicate、safe / bad attractor
predicate、basin から selected safe suffix への accessor theorem を追加した。
Issue [#642](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/642) では、
accepted / rejected transition boundary と selected damping assumption に相対化して、
accepted evolution の invariant preservation と bad-axis nonincrease theorem を追加した。
Issue [#656](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/656) では、
`SignatureTrajectory` / `SignatureDeltaSequence` の endpoint、length、append 分解補題を
追加し、後続 theorem package 用の有限 path API を固めた。
Issue [#659](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/659) では、
bounded operation script、operation family、operation-to-transition semantics を追加し、
script family preservation と accepted script を既存 safe-region / bad-axis theorem に
接続した。
Issue [#660](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/660) では、
finite support operation kernel を追加し、support 内 operation が selected safe region を
保存するという明示前提から、support から選ばれた任意 step と bounded sampled script の
safe-region preservation を証明した。
Issue [#661](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/661) では、
`ArchitectureSignatureV1` の selected measured axis に限定した signed delta bridge を追加し、
`Option Nat` axis の `some n` evidence を持つ trajectory 上で net delta が endpoint delta に
telescope することを証明した。`none` / unavailable axis は measured-axis trajectory domain に
入らず、available zero evidence としても扱わない。
Issue [#662](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/662) では、
accepted transition sequence に相対化した abstract force reading schema を追加し、
selected additive delta law の下で net force が endpoint force と一致する theorem を、
selected invariant preservation / bad-axis nonincrease theorem と bounded に接続した。
Issue [#684](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/684) では、
`ZeroNetForceNonZeroExcursion` の小さな finite counterexample を追加し、
endpoint delta が 0 で start / target が selected safe region に入っていても、
observed trajectory 全体の safe-region preservation は従わない境界を証明した。
Issue [#687](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/687) では、
`AxisWiseSafeNotGlobalSafe` の小さな finite pair-signature counterexample を追加し、
projection-wise safety から cross-axis relation を含む global safety は従わない境界を証明した。
Issue [#688](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/688) では、
`SameSignatureDifferentFuture` の小さな finite kernel counterexample を追加し、
same observed signature から same future operation support は従わない境界を証明した。
Issue [#685](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/685) では、
`ObservabilityExpansionShock` の小さな finite observation counterexample を追加し、
coarse observation で safe に見えることから、refined observation の hidden axis が
measured zero であることや refined safety が従わない境界を証明した。
Issue [#686](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/686) では、
`OperationCommutatorCurvature` と `DistanceMergeOrderSensitivity` を追加し、
selected distance function に相対化して two-step operation order の final signature 差を読む
API へ一般化した。`EqualityDistance` では既存 0/1 `MergeOrderSensitivity` と一致し、
既存 counterexample は距離付き curvature でも nonzero になる。
Issue [#697](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/697) では、
`AttractorEngineeringSupportPackage` と target trajectory wrapper を追加し、
`FiniteOperationKernel.boundedSampledScript_preserves_safeRegion` を Attractor Engineering
語彙で読む入口を `Formal/Arch/Evolution/AttractorEngineering.lean` に分離した。
bad region の補集合を selected safe region として扱う wrapper も追加し、coverage /
measurement boundary / non-conclusions を package accessor として記録する。
Issue [#699](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/699) では、
`ConstructiveDampingFiniteReturn.StrictFairBlockDampingAssumption` を追加し、
Nat 値の selected bad-axis trace が explicit nonincrease と strict fair-block hypothesis を
満たすとき、`exists n <= blockLength * B, bad sigma_n = 0` となる finite return theorem を
証明した。accepted nonincrease だけから finite return は結論せず、strict damping support の
tooling / empirical claim は boundary accessor 側に残す。
Issue [#643](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/643) は
stochastic / empirical bridge の設計境界であり、新しい Lean API は追加しない。
finite weighted operation distribution、simulation protocol、PR force / trajectory /
dynamics metrics report、AI patch sensitivity、Vibe coding success hypothesis は
tooling validation / empirical hypothesis として扱い、下表の Lean theorem claim とは分ける。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `SignatureObservation` | `structure` | architecture state から抽象 signature domain `Sig` への観測写像と、coverage assumptions / non-conclusions を束ねる schema。 | `defined only` |
| `SignatureObservation.Observes` | `def` | selected state の観測値が指定 signature と一致すること。 | `defined only` |
| `SignatureObservation.RecordsNonConclusions` | `def` | observation package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `SignatureDelta` | `structure` | 抽象 signature 間の delta operation と non-conclusions を束ねる schema。加法・符号・telescoping law は仮定しない。 | `defined only` |
| `SignatureDelta.between` | `def` | selected abstract delta operation を二つの signature に適用する。 | `defined only` |
| `SignatureDelta.RecordsNonConclusions` | `def` | delta package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `SignatureTrajectory` | `def` | `ArchitectureEvolution` の visited state を `SignatureObservation.observe` で写した signature sequence。 | `defined only` |
| `SignatureDeltaSequence` | `def` | `ArchitectureEvolution` の各 primitive transition に沿った per-step abstract delta sequence。 | `defined only` |
| `signatureTrajectory_endsWith_target` | `theorem` | observed trajectory が target observation を末尾に持つことを、prefix decomposition として示す。 | `proved` |
| `signatureTrajectory_length` | `theorem` | observed trajectory の長さが `ArchitecturePath.length plan + 1` であることを示す。 | `proved` |
| `signatureDeltaSequence_length` | `theorem` | per-step delta sequence の長さが `ArchitecturePath.length plan` と一致することを示す。 | `proved` |
| `signatureTrajectory_head_cons_tail` | `theorem` | observed trajectory が非空であり、head observation と tail から再構成できることを示す補助補題。 | `proved` |
| `signatureTrajectory_append` | `theorem` | appended path の observed trajectory が、左 trajectory と右 trajectory の tail の連結に分解できることを示す。 | `proved` |
| `signatureDeltaSequence_append` | `theorem` | appended path の per-step delta sequence が左右 segment の delta sequence の連結に分解できることを示す。 | `proved` |
| `SafeRegion` | `abbrev` | 観測 signature domain 上の selected safe region predicate。review / CI / policy capacity は結論しない。 | `defined only` |
| `StateInSafeRegion` | `def` | state の selected observation が safe region に属すること。 | `defined only` |
| `StepPreservesSafeRegion` | `def` | primitive transition が selected observed safe region を source から target へ保存すること。 | `defined only` |
| `EveryStepPreservesSafeRegion` | `def` | path 上のすべての primitive transition が selected safe region を保存すること。 | `defined only` |
| `SignatureTrajectoryInSafeRegion` | `def` | trajectory 内のすべての observed signature が selected safe region に属すること。 | `defined only` |
| `SignatureTrajectoryHasBoundedReturn` | `def` | finite observed trajectory 内で、selected signature が非空 repeated block に含まれることを表す bounded recurrence witness predicate。 | `defined only` |
| `RecurrentSignatureRegion` | `def` | selected region 内の各 signature が supplied finite trajectory 内の bounded return witness を持つこと。global recurrent class は結論しない。 | `defined only` |
| `NetSignatureDelta` | `def` | selected per-step signature deltas を `Delta` の `0` / `+` で集計する fold API。unmeasured axis や empirical PR outcome は結論しない。 | `defined only` |
| `EndpointSignatureDelta` | `def` | evolution path の start / target observation の間の selected endpoint delta。 | `defined only` |
| `AdditiveSignatureDeltaLaw` | `structure` | `self_zero` と `step_telescope` を明示前提として持つ selected additive delta law package。coverage 外の軸、cost、incident risk、PR outcome は non-conclusions に残す。 | `defined only` |
| `AdditiveSignatureDeltaLaw.RecordsNonConclusions` | `def` | additive delta law package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `netSignatureDelta_telescopes` | `theorem` | `AdditiveSignatureDeltaLaw` の下で、path 上の per-step delta の net sum が endpoint delta と一致することを示す。 | `proved` |
| `ArchitectureSignatureV1MeasuredAxisDelta.Schema` | `structure` | `ArchitectureSignatureV1` の signed delta 読み取り対象になる selected measured axis list、coverage assumptions、non-conclusions を束ねる concrete bridge schema。 | `defined only` |
| `ArchitectureSignatureV1MeasuredAxisDelta.Schema.AxisSelected` | `def` | concrete bridge schema で axis が selected であること。 | `defined only` |
| `ArchitectureSignatureV1MeasuredAxisDelta.Schema.RecordsNonConclusions` | `def` | concrete bridge schema の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `ArchitectureSignatureV1MeasuredAxisDelta.Schema.RecordsUnmeasuredNonConclusion` | `def` | selected axis の `none` を available zero evidence と読まない boundary を schema から読む predicate。 | `defined only` |
| `ArchitectureSignatureV1MeasuredAxisDelta.Schema.unmeasured_not_axisAvailableAndZero` | `theorem` | selected axis が `none` の場合、`ArchitectureSignatureV1.axisAvailableAndZero` ではないことを示す。 | `proved` |
| `ArchitectureSignatureV1MeasuredAxisDelta.MeasuredAxisSignature` | `structure` | fixed axis について `ArchitectureSignatureV1.axisValue = some value` の evidence を持つ measured sample。 | `defined only` |
| `ArchitectureSignatureV1MeasuredAxisDelta.not_measuredAxisSignature_of_axisValue_none` | `theorem` | `axisValue = none` の V1 signature は同じ axis の measured sample として表現できない。 | `proved` |
| `ArchitectureSignatureV1MeasuredAxisDelta.measuredAxisObservation` | `def` | measured sample から fixed axis の `Nat` value を観測する concrete observation schema。 | `defined only` |
| `ArchitectureSignatureV1MeasuredAxisDelta.signedNatAxisDelta` | `def` | measured `Nat` axis value の signed target-source delta。 | `defined only` |
| `ArchitectureSignatureV1MeasuredAxisDelta.signedNatAxisDelta_additiveLaw` | `def` | signed natural axis delta が selected additive law を満たす package。 | `defined only` |
| `ArchitectureSignatureV1MeasuredAxisDelta.selectedMeasuredAxis_netDelta_telescopes` | `theorem` | selected measured V1 axis の trajectory 上で per-step signed delta の net sum が endpoint delta と一致することを示す。 | `proved` |
| `ArchitectureSignatureV1MeasuredAxisDelta.measuredAxis_endpointDelta_eq` | `theorem` | measured V1 axis の endpoint delta が signed target-source value であることを示す。 | `proved` |
| `trajectory_preserves_safeRegion` | `theorem` | initial observation が safe region にあり、各 selected transition が safe region を保存するなら、observed trajectory 全体が safe region に属することを示す。 | `proved` |
| `DampingControlSchema` | `structure` | selected observation / safe region、accepted / rejected transition predicate、accepted step が selected invariant を保存する explicit assumption、coverage / non-conclusions を束ねる control schema。 | `defined only` |
| `DampingControlSchema.AcceptedStep` | `def` | selected controller が primitive transition を accepted と分類すること。 | `defined only` |
| `DampingControlSchema.RejectedStep` | `def` | selected controller が primitive transition を rejected と分類すること。target-state guarantee は結論しない。 | `defined only` |
| `DampingControlSchema.RecordsNonConclusions` | `def` | control package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `DampingControlSchema.AcceptedEvolution` | `def` | finite evolution path 上のすべての primitive transition が accepted であること。 | `defined only` |
| `DampingControlSchema.acceptedStep_preserves_selectedInvariant` | `theorem` | accepted step が selected invariant を保存することを explicit controller assumption から取り出す。 | `proved` |
| `DampingControlSchema.everyStepPreservesSafeRegion_of_acceptedEvolution` | `theorem` | accepted evolution から path 上の各 step の selected safe-region preservation を得る。 | `proved` |
| `DampingControlSchema.acceptedEvolution_preserves_selectedInvariant` | `theorem` | initial observation が selected invariant 内にあり、evolution が accepted なら observed trajectory 全体が selected invariant 内に留まる。 | `proved` |
| `DampingControlSchema.BadAxisDampingAssumption` | `structure` | selected bad-axis measure、order reflexivity / transitivity、accepted step nonincrease、non-conclusions を束ねる explicit damping assumption。 | `defined only` |
| `DampingControlSchema.BadAxisDampingAssumption.RecordsNonConclusions` | `def` | bad-axis damping assumption package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `DampingControlSchema.badAxis_nonincrease_of_acceptedStep` | `theorem` | explicit damping assumption の下で、accepted step が selected bad-axis measure を非増加にすることを示す。 | `proved` |
| `DampingControlSchema.badAxis_nonincrease_of_acceptedEvolution` | `theorem` | explicit damping assumption の下で、accepted finite evolution が source から target へ selected bad-axis measure を非増加にすることを示す。 | `proved` |
| `AcceptedTransitionForceSchema` | `structure` | selected control schema、signature delta、additive law、accepted-transition / PR outcome / incident / review cost / GitHub metadata / report calibration boundary を束ねる abstract accepted-transition force reading schema。 | `defined only` |
| `AcceptedTransitionForceSchema.AcceptedSequence` | `def` | selected finite evolution が supplied controller に accepted されていること。 | `defined only` |
| `AcceptedTransitionForceSchema.ObservedForceSequence` | `def` | accepted-transition reading の per-step selected force sequence を `SignatureDeltaSequence` として読む。 | `defined only` |
| `AcceptedTransitionForceSchema.NetForce` | `def` | selected per-step force sequence を `NetSignatureDelta` で集計した net force。 | `defined only` |
| `AcceptedTransitionForceSchema.EndpointForce` | `def` | source / target observation の selected endpoint delta として読む endpoint force。 | `defined only` |
| `AcceptedTransitionForceSchema.RecordsAcceptedTransitionBoundary` | `def` | accepted-transition boundary を predicate として取り出す。 | `defined only` |
| `AcceptedTransitionForceSchema.RecordsPROutcomeBoundary` | `def` | PR outcome が theorem claim 外である boundary を predicate として取り出す。 | `defined only` |
| `AcceptedTransitionForceSchema.RecordsIncidentBoundary` | `def` | incident が theorem claim 外である boundary を predicate として取り出す。 | `defined only` |
| `AcceptedTransitionForceSchema.RecordsReviewCostBoundary` | `def` | review cost が theorem claim 外である boundary を predicate として取り出す。 | `defined only` |
| `AcceptedTransitionForceSchema.RecordsGitHubMetadataBoundary` | `def` | GitHub metadata が theorem claim 外である boundary を predicate として取り出す。 | `defined only` |
| `AcceptedTransitionForceSchema.RecordsReportCalibrationBoundary` | `def` | report calibration が theorem claim 外である boundary を predicate として取り出す。 | `defined only` |
| `AcceptedTransitionForceSchema.RecordsNonConclusions` | `def` | accepted-transition force schema の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `AcceptedTransitionForceSchema.netForce_eq_endpointForce` | `theorem` | accepted sequence に相対化された force reading で、selected additive delta law の下で net force が endpoint force と一致することを示す。 | `proved` |
| `AcceptedTransitionForceSchema.preservesInvariant_and_netForce_eq_endpointForce` | `theorem` | accepted sequence について selected invariant preservation と net force endpoint equality を同時に得る bounded theorem。 | `proved` |
| `AcceptedTransitionForceSchema.badAxisNonincrease_and_netForce_eq_endpointForce` | `theorem` | explicit bad-axis damping assumption の下で、accepted sequence の bad-axis nonincrease と net force endpoint equality を同時に得る bounded theorem。 | `proved` |
| `ZeroNetForceNonZeroExcursion.observation` | `def` | `Nat` state をそのまま observed signature として読む小さな counterexample 用 observation schema。 | `defined only` |
| `ZeroNetForceNonZeroExcursion.signedNatDelta` | `def` | selected endpoint / per-step 差分を signed target-source delta として読む小例用 delta schema。 | `defined only` |
| `ZeroNetForceNonZeroExcursion.safeRegion` | `def` | selected safe region を signature `0` に限定する小例用 predicate。 | `defined only` |
| `ZeroNetForceNonZeroExcursion.excursionPlan` | `def` | `0 -> 2 -> 0` の finite architecture evolution witness。 | `defined only` |
| `ZeroNetForceNonZeroExcursion.endpointSignatureDelta_eq_zero` | `theorem` | 小例の endpoint-only selected signature delta が `0` であることを示す。 | `proved` |
| `ZeroNetForceNonZeroExcursion.netSignatureDelta_eq_zero` | `theorem` | 小例の per-step selected delta の net sum も `0` に評価されることを示す。 | `proved` |
| `ZeroNetForceNonZeroExcursion.source_in_safeRegion` | `theorem` | source state が selected safe region に入ることを示す。 | `proved` |
| `ZeroNetForceNonZeroExcursion.target_in_safeRegion` | `theorem` | target state が selected safe region に入ることを示す。 | `proved` |
| `ZeroNetForceNonZeroExcursion.excursion_signature_mem` | `theorem` | observed trajectory が unsafe excursion signature `2` を含むことを示す。 | `proved` |
| `ZeroNetForceNonZeroExcursion.not_signatureTrajectoryInSafeRegion` | `theorem` | 小例の observed trajectory 全体は selected safe region 内に留まらないことを示す。 | `proved` |
| `ZeroNetForceNonZeroExcursion.endpointSafe_and_zeroDelta_but_not_pathSafe` | `theorem` | endpoint delta zero と safe endpoints から path safety を結論しない bounded counterexample を束ねる。 | `proved` |
| `AxisWiseSafeNotGlobalSafe.AxisValue` | `abbrev` | `Fin 2` を使う小さな finite axis value domain。 | `defined only` |
| `AxisWiseSafeNotGlobalSafe.ExampleSig` | `abbrev` | 二つの measured axis を持つ finite pair signature domain。 | `defined only` |
| `AxisWiseSafeNotGlobalSafe.projectionSafe` | `def` | selected per-axis safety predicate。membership in `Fin 2` に相対化された局所 predicate として扱う。 | `defined only` |
| `AxisWiseSafeNotGlobalSafe.AxisWiseSafe` | `def` | pair signature の各 projection が selected per-axis predicate を満たすこと。 | `defined only` |
| `AxisWiseSafeNotGlobalSafe.CrossAxisInvariant` | `def` | pair signature の二つの axis が一致するという selected cross-axis relation。 | `defined only` |
| `AxisWiseSafeNotGlobalSafe.GlobalSafe` | `def` | axis-wise safety と selected cross-axis invariant を同時に要求する bounded global safety predicate。 | `defined only` |
| `AxisWiseSafeNotGlobalSafe.witness` | `def` | axis-wise safe だが cross-axis invariant を破る finite witness `(0, 1)`。 | `defined only` |
| `AxisWiseSafeNotGlobalSafe.firstProjection_safe` | `theorem` | witness の第一 projection が selected per-axis predicate を満たすことを示す。 | `proved` |
| `AxisWiseSafeNotGlobalSafe.secondProjection_safe` | `theorem` | witness の第二 projection が selected per-axis predicate を満たすことを示す。 | `proved` |
| `AxisWiseSafeNotGlobalSafe.axisWiseSafe_witness` | `theorem` | witness が axis-wise safe であることを示す。 | `proved` |
| `AxisWiseSafeNotGlobalSafe.not_crossAxisInvariant_witness` | `theorem` | witness が selected cross-axis invariant を破ることを示す。 | `proved` |
| `AxisWiseSafeNotGlobalSafe.not_globalSafe_witness` | `theorem` | witness が selected global safety predicate を満たさないことを示す。 | `proved` |
| `AxisWiseSafeNotGlobalSafe.axisWiseSafe_but_not_globalSafe` | `theorem` | axis-wise safe だが global safe ではない bounded counterexample を束ねる。 | `proved` |
| `AxisWiseSafeNotGlobalSafe.not_axisWiseSafe_implies_globalSafe` | `theorem` | axis-wise safety だけから selected global safety を結論する一般命題が成り立たないことを示す。 | `proved` |
| `OperationTransitionSemantics` | `structure` | operation ID と primitive `ArchitectureTransition` の bounded realization relation、coverage / non-conclusions を束ねる schema。operation tag だけから preservation / acceptance は結論しない。 | `defined only` |
| `OperationTransitionSemantics.Realizes` | `def` | selected operation ID が primitive transition を realize すること。 | `defined only` |
| `OperationTransitionSemantics.RecordsNonConclusions` | `def` | operation semantics package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `OperationTransitionSemantics.OperationPreservesSafeRegion` | `def` | operation ID が realize する任意 transition で selected safe region を保存すること。 | `defined only` |
| `OperationTransitionSemantics.OperationFamilyPreservesSafeRegion` | `def` | selected operation family の全 operation ID が selected safe region を保存すること。 | `defined only` |
| `BoundedOperationScript` | `structure` | finite operation ID list、selected operation family、script entries が family に属する proof、coverage / non-conclusions を束ねる bounded script schema。 | `defined only` |
| `BoundedOperationScript.RecordsNonConclusions` | `def` | bounded script package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `BoundedOperationScript.ScriptRealizesEvolution` | `def` | operation ID list が endpoint-indexed `ArchitectureEvolution` の各 transition を 1 対 1 に realize すること。length mismatch は false。 | `defined only` |
| `BoundedOperationScript.RealizesEvolution` | `def` | bounded script が selected architecture evolution を realize すること。 | `defined only` |
| `BoundedOperationScript.EveryScriptStepAccepted` | `def` | realized script の各 primitive transition が selected controller に accepted されること。 | `defined only` |
| `BoundedOperationScript.AcceptedEvolution` | `def` | bounded script が accepted steps として selected plan を realize すること。 | `defined only` |
| `BoundedOperationScript.everyStepPreservesSafeRegion_of_scriptRealizes` | `theorem` | realized script の各 operation に explicit preservation assumption があれば、plan の各 transition が safe region を保存する。 | `proved` |
| `BoundedOperationScript.everyStepPreservesSafeRegion_of_scriptFamily` | `theorem` | selected operation family が safe region を保存し、script が family members のみからなるなら、realized plan の各 transition が safe region を保存する。 | `proved` |
| `BoundedOperationScript.script_preserves_safeRegion` | `theorem` | initial state が safe で、script family preservation と realization があれば、observed signature trajectory 全体が safe region 内に留まる。 | `proved` |
| `BoundedOperationScript.acceptedEvolution_of_scriptAccepted` | `theorem` | accepted operation script から既存 `DampingControlSchema.AcceptedEvolution` を得る。 | `proved` |
| `BoundedOperationScript.badAxis_nonincrease_of_acceptedScript` | `theorem` | explicit damping assumption の下で、accepted bounded operation script が selected bad-axis measure を endpoint で非増加にする。 | `proved` |
| `FiniteOperationKernel` | `structure` | state ごとの finite support operation list と、coverage / weight source / normalization / non-conclusion boundary を束ねる operation selection kernel。確率分布そのものは主張しない。 | `defined only` |
| `FiniteOperationKernel.Supports` | `def` | selected operation ID が source state の finite support に含まれること。 | `defined only` |
| `FiniteOperationKernel.RecordsWeightSourceBoundary` | `def` | finite support kernel の weight-source boundary を predicate として取り出す。 | `defined only` |
| `FiniteOperationKernel.RecordsNormalizationBoundary` | `def` | finite support kernel の normalization boundary を predicate として取り出す。 | `defined only` |
| `FiniteOperationKernel.RecordsNonConclusions` | `def` | finite support kernel の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `FiniteOperationKernel.SupportOperationsPreserveSafeRegion` | `def` | finite support 内の各 operation が、realize する任意 transition で selected safe region を保存すること。 | `defined only` |
| `FiniteOperationKernel.SupportStep` | `def` | source state の finite support から選ばれた operation が primitive transition を realize すること。 | `defined only` |
| `FiniteOperationKernel.supportStep_preserves_safeRegion` | `theorem` | support 内 operation が safe region を保存するなら、support から選ばれて realize された任意 step も safe region を保存する。 | `proved` |
| `FiniteOperationKernel.ScriptUsesSupport` | `def` | operation list が endpoint-indexed evolution の各 source state で finite support 内 operation だけを使うこと。length mismatch は false。 | `defined only` |
| `FiniteOperationKernel.everyStepPreservesSafeRegion_of_scriptUsesSupport` | `theorem` | realized operation list が各 source state の finite support 内 operation だけを使い、support operation が safe region を保存するなら、plan の各 transition が safe region を保存する。 | `proved` |
| `FiniteOperationKernel.boundedSampledScript_preserves_safeRegion` | `theorem` | bounded sampled script が plan を realize し、各 source state の finite support 内 operation だけを使うなら、support preservation 前提の下で observed signature trajectory 全体が safe region 内に留まる。 | `proved` |
| `AvoidsBadRegion` | `abbrev` | selected bad region の補集合を selected safe region として読む Attractor Engineering wrapper。bad-region discovery や empirical guardrail capacity は結論しない。 | `defined only` |
| `AttractorEngineeringSupportPackage` | `structure` | selected observation、finite operation support、bounded transition semantics、target region、explicit support preservation、coverage / measurement boundary / non-conclusions を束ねる薄い package。 | `defined only` |
| `AttractorEngineeringSupportPackage.RecordsCoverageAssumptions` | `def` | support package の selected coverage assumptions を predicate として取り出す。 | `defined only` |
| `AttractorEngineeringSupportPackage.RecordsMeasurementBoundary` | `def` | unmeasured axes、tooling coverage、calibration、empirical completeness が theorem claim 外である measurement boundary を取り出す。 | `defined only` |
| `AttractorEngineeringSupportPackage.RecordsNonConclusions` | `def` | support package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `AttractorEngineeringSupportPackage.TargetTrajectory` | `def` | package の selected observation で `ArchitectureEvolution` の visited states を読む target trajectory wrapper。 | `defined only` |
| `AttractorEngineeringSupportPackage.supportPreserves_targetRegion` | `theorem` | package に格納された support preservation 前提を accessor theorem として取り出す。 | `proved` |
| `AttractorEngineeringSupportPackage.supportPackage_preserves_targetTrajectory` | `theorem` | realized bounded script が finite support だけを使い、start が target region 内なら、package の target trajectory が target region 内に留まる。 | `proved` |
| `AttractorEngineeringSupportPackage.supportPackage_avoids_badRegion` | `theorem` | package の target region が bad region の補集合なら、bounded target trajectory がその bad region を避けることを示す。 | `proved` |
| `AttractorEngineeringSupportPackage.supportShaping_avoids_badRegion` | `theorem` | bad region の補集合を safe region として、support operation preservation から bounded trajectory が bad region を避けることを直接得る wrapper。 | `proved` |
| `ConstructiveDampingFiniteReturn.StrictFairBlockDampingAssumption` | `structure` | selected bad-axis `Sig -> Nat`、finite block length、accepted nonincrease / empirical support / non-conclusion boundary を束ねる strict fair-block damping package。 | `defined only` |
| `StrictFairBlockDampingAssumption.scoreAt` | `def` | selected signature trajectory の index `n` における bad-axis score を読む。 | `defined only` |
| `StrictFairBlockDampingAssumption.TraceNonincreasing` | `def` | selected score trace が隣接 step ごとに非増加であること。finite return はこれだけからは結論しない。 | `defined only` |
| `StrictFairBlockDampingAssumption.TraceHasStrictFairBlocks` | `def` | positive-score block ごとに、selected finite block length 内で strict decrease が現れること。 | `defined only` |
| `StrictFairBlockDampingAssumption.RecordsAcceptedNonincreaseBoundary` | `def` | accepted nonincrease だけでは finite return を結論しない boundary を predicate として取り出す。 | `defined only` |
| `StrictFairBlockDampingAssumption.RecordsEmpiricalSupportBoundary` | `def` | tooling / empirical layer が strict fair-block hypothesis を support するかは theorem claim 外である boundary を取り出す。 | `defined only` |
| `StrictFairBlockDampingAssumption.RecordsNonConclusions` | `def` | strict fair-block damping package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `StrictFairBlockDampingAssumption.strictFairBlockDamping_finiteReturn` | `theorem` | score が `B` から始まり、非増加かつ positive block ごとに strict decrease を持つなら、`exists n <= blockLength * B, score n = 0` を示す。 | `proved` |
| `StrictFairBlockDampingAssumption.strictFairBlockDamping_finiteReturn_with_boundaries` | `theorem` | finite return conclusion と、明示的に与えられた accepted nonincrease / empirical support / non-conclusion boundary records を束ねる。 | `proved` |
| `AcceptedPreservationNotSupportPreservation.observation` | `def` | `Bool` state をそのまま observed signature として読む小さな Attractor Engineering counterexample 用 observation schema。 | `defined only` |
| `AcceptedPreservationNotSupportPreservation.control` | `def` | safe self-step のみを accepted とし、accepted step が selected invariant を保存する小例用 control schema。 | `defined only` |
| `AcceptedPreservationNotSupportPreservation.semantics` | `def` | accepted noop と unsafe drift operation の bounded realization relation を持つ小例用 semantics。 | `defined only` |
| `AcceptedPreservationNotSupportPreservation.kernel` | `def` | safe state の finite support に unsafe drift operation も含める小例用 kernel。 | `defined only` |
| `AcceptedPreservationNotSupportPreservation.acceptedTransition_accepted` | `theorem` | 小例の safe self-step が selected controller に accepted されることを示す。 | `proved` |
| `AcceptedPreservationNotSupportPreservation.acceptedTransition_preserves_selectedInvariant` | `theorem` | 小例の accepted safe self-step が selected invariant を保存することを示す。 | `proved` |
| `AcceptedPreservationNotSupportPreservation.source_supports_unsafeOperation` | `theorem` | safe source state の finite support が unsafe drift operation を含むことを示す。 | `proved` |
| `AcceptedPreservationNotSupportPreservation.unsafeOperation_not_preserves_safeRegion` | `theorem` | unsafe drift operation が selected safe region を保存しないことを示す。 | `proved` |
| `AcceptedPreservationNotSupportPreservation.acceptedPreservation_not_supportPreservation_counterexample` | `theorem` | accepted-step invariant preservation と、support 内 unsafe operation の存在が同時に成り立つ finite counterexample を束ねる。 | `proved` |
| `SameObservedSignatureDifferentFutureSupport` | `def` | same selected observed signature と different finite future operation support を束ねる bounded witness predicate。future distribution / empirical weights / unmeasured axes は結論しない。 | `defined only` |
| `SameObservedSignatureDifferentFutureTrajectory` | `def` | same selected observed signature と realized finite scripts / support use から異なる future signature trajectory が生じる bounded witness predicate。global distribution / empirical proposal probability / AI behavior theorem は結論しない。 | `defined only` |
| `SameSignatureDifferentFuture.observation` | `def` | `Nat` state を `Bool` signature へ潰して読み、source / target の current signature を同一にする小さな counterexample 用 observation schema。 | `defined only` |
| `SameSignatureDifferentFuture.kernel` | `def` | source state と target state に異なる singleton operation support を割り当てる finite kernel witness。 | `defined only` |
| `SameSignatureDifferentFuture.semantics` | `def` | selected left / right operation をそれぞれ source / target から別の future state へ進める bounded transition semantics。 | `defined only` |
| `SameSignatureDifferentFuture.leftPlan` | `def` | source から left future state へ進む 1-step finite evolution。 | `defined only` |
| `SameSignatureDifferentFuture.rightPlan` | `def` | target から right future state へ進む 1-step finite evolution。 | `defined only` |
| `SameSignatureDifferentFuture.leftScript` | `def` | left operation だけを含む bounded operation script。 | `defined only` |
| `SameSignatureDifferentFuture.rightScript` | `def` | right operation だけを含む bounded operation script。 | `defined only` |
| `SameSignatureDifferentFuture.source_ne_target` | `theorem` | 小例の source と target が distinct state pair であることを示す。 | `proved` |
| `SameSignatureDifferentFuture.same_observed_signature` | `theorem` | distinct state pair が same selected observed signature を持つことを示す。 | `proved` |
| `SameSignatureDifferentFuture.source_supports_leftOperation` | `theorem` | source state の finite support が selected left operation を含むことを示す。 | `proved` |
| `SameSignatureDifferentFuture.target_not_supports_leftOperation` | `theorem` | target state の finite support が selected left operation を含まないことを示す。 | `proved` |
| `SameSignatureDifferentFuture.leftScript_uses_sourceSupport` | `theorem` | left script が left plan 上で source state の finite support operation だけを使うことを示す。 | `proved` |
| `SameSignatureDifferentFuture.rightScript_uses_targetSupport` | `theorem` | right script が right plan 上で target state の finite support operation だけを使うことを示す。 | `proved` |
| `SameSignatureDifferentFuture.leftScript_realizes_leftPlan` | `theorem` | selected semantics の下で left script が left plan を realize することを示す。 | `proved` |
| `SameSignatureDifferentFuture.rightScript_realizes_rightPlan` | `theorem` | selected semantics の下で right script が right plan を realize することを示す。 | `proved` |
| `SameSignatureDifferentFuture.future_support_differs` | `theorem` | same observed signature を持つ selected state pair の finite support list が異なることを示す。 | `proved` |
| `SameSignatureDifferentFuture.future_trajectory_differs` | `theorem` | same current observed signature から始まる selected realized scripts の future signature trajectory が異なることを示す。 | `proved` |
| `SameSignatureDifferentFuture.sameObservedSignature_differentFutureSupport` | `theorem` | same observed signature と different future operation support を束ねる bounded counterexample。 | `proved` |
| `SameSignatureDifferentFuture.sameObservedSignature_differentFutureTrajectory` | `theorem` | same observed signature、finite support use、selected script realization、different future signature trajectory を束ねる bounded counterexample。 | `proved` |
| `SameSignatureDifferentFuture.not_sameObservation_implies_sameFutureSupport` | `theorem` | same selected observation だけから same future operation support を結論する一般命題が成り立たないことを示す。 | `proved` |
| `SameSignatureDifferentFuture.not_sameObservation_implies_sameFutureTrajectory` | `theorem` | same selected observation だけから same future signature trajectory を結論する一般命題が成り立たないことを示す。 | `proved` |
| `ObservabilityExpansionShock.coarseObservation` | `def` | `Unit` signature だけを観測する coarse observation schema。hidden refined axis は測定しない。 | `defined only` |
| `ObservabilityExpansionShock.refinedObservation` | `def` | visible axis と hidden axis を持つ refined observation schema。小例では hidden axis が `1` として測定される。 | `defined only` |
| `ObservabilityExpansionShock.hiddenAxis` | `def` | refined signature から newly measured hidden axis を取り出す。 | `defined only` |
| `ObservabilityExpansionShock.coarseSafe` | `def` | selected coarse observation 上の safe predicate。 | `defined only` |
| `ObservabilityExpansionShock.refinedSafe` | `def` | hidden axis が `0` であることを要求する selected refined safety predicate。 | `defined only` |
| `ObservabilityExpansionShock.HiddenAxisMeasuredNonzero` | `def` | refined observation の hidden axis が measured nonzero であること。 | `defined only` |
| `ObservabilityExpansionShock.UnmeasuredAxisIsNotMeasuredZeroBoundary` | `def` | coarse safe observation が hidden axis の measured-zero evidence を供給しないことを表す boundary predicate。 | `defined only` |
| `ObservabilityExpansionShock.ObservabilityExpansionBoundary` | `def` | coarse safety、newly measured hidden-axis nonzero、observation non-conclusions を束ねる bounded boundary predicate。 | `defined only` |
| `ObservabilityExpansionShock.coarse_witness_safe` | `theorem` | witness が selected coarse safe predicate を満たすことを示す。 | `proved` |
| `ObservabilityExpansionShock.refined_hiddenAxis_eq_one` | `theorem` | refined observation が hidden axis を `1` として測定することを示す。 | `proved` |
| `ObservabilityExpansionShock.refined_hiddenAxis_nonzero` | `theorem` | newly measured hidden axis が nonzero であることを示す。 | `proved` |
| `ObservabilityExpansionShock.not_refined_witness_safe` | `theorem` | 同じ witness が selected refined safety predicate を満たさないことを示す。 | `proved` |
| `ObservabilityExpansionShock.coarseSafe_but_refinedHiddenAxis_nonzero` | `theorem` | coarse safe だが refined hidden axis は measured nonzero である bounded counterexample を束ねる。 | `proved` |
| `ObservabilityExpansionShock.coarseSafe_but_not_refinedSafe` | `theorem` | coarse safe から refined safe は従わない bounded counterexample を束ねる。 | `proved` |
| `ObservabilityExpansionShock.unmeasuredAxis_is_not_measuredZeroBoundary` | `theorem` | coarse observation の未測定 hidden axis を measured zero と読めない non-conclusion boundary を示す。 | `proved` |
| `ObservabilityExpansionShock.not_coarseSafe_implies_refinedSafe` | `theorem` | coarse safety だけから selected refined safety を結論する一般命題が成り立たないことを示す。 | `proved` |
| `ObservabilityExpansionShock.records_observabilityExpansionBoundary` | `theorem` | observability expansion は coarse safety と hidden-axis nonzero evidence と non-conclusion clauses を同時に記録する boundary event として扱う。 | `proved` |
| `AttractorCandidate` | `structure` | finite observed trajectory と selected region に相対化し、selected entry index 以降の observed suffix が region 内に留まることを記録する schema。 | `defined only` |
| `AttractorCandidate.observedSuffix` | `def` | attractor candidate の selected entry index 以降の finite observed suffix を取り出す。 | `defined only` |
| `AttractorCandidate.RecurrentRegion` | `def` | candidate の selected observed suffix と selected region に相対化した recurrent signature region predicate。 | `defined only` |
| `AttractorCandidate.IsSafeAttractor` | `def` | candidate suffix が caller-supplied safe region 内に留まることを表す selected safe attractor predicate。 | `defined only` |
| `AttractorCandidate.IsBadAttractor` | `def` | caller-supplied bad-axis measurement と bad-score predicate により、candidate suffix に bad signature が含まれることを表す selected bad attractor predicate。 | `defined only` |
| `AttractorCandidate.RecordsNonConclusions` | `def` | attractor candidate package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `AttractorCandidate.observedSuffix_in_region` | `theorem` | selected observed suffix が candidate region 内に留まることを schema field から取り出す accessor theorem。 | `proved` |
| `AttractorCandidate.isSafeAttractor_region` | `theorem` | candidate suffix が candidate 自身の selected region に対して safe attractor であることを示す accessor theorem。 | `proved` |
| `AttractorCandidate.isSafeAttractor_of_region_subset` | `theorem` | candidate region が別の selected safe region に含まれるなら、その region に対しても candidate suffix が safe attractor であることを示す。 | `proved` |
| `BasinCandidate` | `structure` | selected observation、finite initial-state list、attractor candidate、bounded operation script、caller-supplied reachability predicate を束ねる basin candidate schema。 | `defined only` |
| `BasinCandidate.RecordsNonConclusions` | `def` | basin candidate package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `BasinCandidate.CoversSelectedInitialStates` | `def` | finite initial-state list の各 state が caller-supplied reachability predicate を満たすこと。 | `defined only` |
| `BasinCandidate.SelectedInitialStatesReachSafeSuffix` | `def` | candidate suffix が selected safe region にあり、selected initial-state list が reachability predicate で cover されることを束ねる bounded basin predicate。 | `defined only` |
| `BasinCandidate.coversSelectedInitialStates` | `theorem` | basin candidate が selected initial-state list を cover することを schema field から取り出す accessor theorem。 | `proved` |
| `BasinCandidate.selectedInitialStates_reach_safeSuffix_of_safeAttractor` | `theorem` | safe attractor predicate と basin coverage から、selected initial states が selected safe suffix へ到達する bounded predicate を得る。 | `proved` |
| `BasinCandidate.selectedInitialStates_reach_attractorRegionSuffix` | `theorem` | selected initial states が candidate 自身の region-safe suffix へ到達することを schema field から取り出す accessor theorem。 | `proved` |
| `FiniteStateUniverse` | `structure` | deterministic signature dynamics 用の duplicate-free finite state list と coverage を束ねる explicit finite universe。 | `defined only` |
| `FiniteStateUniverse.StepClosed` | `def` | selected self-map が explicit finite universe の state list 内に閉じていることを表す closure predicate。 | `defined only` |
| `FiniteStateUniverse.stepClosed_of_covers` | `theorem` | full finite state universe では selected self-map closure が coverage から従うことを示す。 | `proved` |
| `FiniteStateUniverse.full` | `def` | duplicate-free covering list から full finite state universe を構成する。 | `defined only` |
| `FiniteStateUniverse.fintype` | `def` | explicit finite state universe から `Fintype State` instance を構成する bridge。 | `defined only` |
| `IterateSelfMap` | `def` | deterministic self-map の `n` 回反復を表す finite dynamics substrate。 | `defined only` |
| `iterateSelfMap_add` | `theorem` | self-map 反復が加法的 horizon に沿って合成されることを示す補助補題。 | `proved` |
| `DeterministicSelfMapEventuallyPeriodic` | `def` | deterministic finite dynamics の eventually periodic property を表す predicate。 | `defined only` |
| `deterministicSelfMap_periodic_from_repetition` | `theorem` | self-map orbit が以前の state を再訪した場合、その suffix が正の周期で periodic になることを示す。 | `proved` |
| `deterministicSelfMapEventuallyPeriodic_of_finite` | `theorem` | `[Finite State]` の下で deterministic self-map orbit が eventually periodic になることを示す。global attractor や empirical convergence は結論しない。 | `proved` |
| `deterministicSelfMapEventuallyPeriodic_of_finiteUniverse` | `theorem` | explicit `FiniteStateUniverse` と selected self-map closure 前提から `DeterministicSelfMapEventuallyPeriodic` を得る。 | `proved` |
| `TwoStepObservationCommutative` | `def` | 同じ start state からの二つの two-step transition order が selected final observation 上で一致すること。 | `defined only` |
| `MergeOrderSensitive` | `def` | 二つの two-step transition order の selected final observation が異なること。実 PR risk や incident との相関は結論しない。 | `defined only` |
| `MergeOrderSensitivity` | `def` | selected final observation が一致すれば `0`、異なれば `1` を返す bounded 0/1 sensitivity metric。 | `defined only` |
| `OperationCommutatorCurvatureSchema` | `structure` | selected signature distance、coverage assumptions、empirical PR risk / incident risk / review cost / unmeasured axes / non-conclusion boundary を束ねる距離付き curvature schema。 | `defined only` |
| `OperationCommutatorCurvatureSchema.RecordsEmpiricalPRRiskBoundary` | `def` | distance-valued curvature schema が empirical PR-risk boundary を記録すること。 | `defined only` |
| `OperationCommutatorCurvatureSchema.RecordsIncidentRiskBoundary` | `def` | distance-valued curvature schema が incident-risk boundary を記録すること。 | `defined only` |
| `OperationCommutatorCurvatureSchema.RecordsReviewCostBoundary` | `def` | distance-valued curvature schema が review-cost boundary を記録すること。 | `defined only` |
| `OperationCommutatorCurvatureSchema.RecordsUnmeasuredAxesBoundary` | `def` | distance-valued curvature schema が unmeasured axes boundary を記録すること。 | `defined only` |
| `OperationCommutatorCurvatureSchema.RecordsNonConclusions` | `def` | distance-valued curvature schema の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `OperationCommutatorCurvature` | `def` | supplied distance function で二つの selected final observations の差を読む距離付き commutator curvature。 | `defined only` |
| `DistanceMergeOrderSensitivity` | `def` | `OperationCommutatorCurvature` と同じ bounded quantity を merge-order sensitivity 側の名前で読む API。 | `defined only` |
| `OperationCommutatorCurvatureOfSchema` | `def` | boundary-recording schema の `distance` から距離付き commutator curvature を読む。 | `defined only` |
| `EqualityDistance` | `def` | equality / disequality を `0` / `1` に読む selected distance。 | `defined only` |
| `operationCommutatorCurvature_eq_mergeOrderSensitivity_of_equalityDistance` | `theorem` | `EqualityDistance` を選ぶと距離付き curvature が既存 0/1 `MergeOrderSensitivity` と一致することを示す。 | `proved` |
| `distanceMergeOrderSensitivity_eq_zero_of_twoStepObservationCommutative` | `theorem` | selected distance が self-zero を満たすなら、観測可換性から距離付き sensitivity が `0` になることを示す。 | `proved` |
| `mergeOrderSensitivity_eq_zero_of_twoStepObservationCommutative` | `theorem` | two-step order が観測上可換なら bounded merge-order sensitivity が `0` になることを示す。 | `proved` |
| `not_mergeOrderSensitive_of_twoStepObservationCommutative` | `theorem` | two-step order の観測可換性から selected merge-order sensitivity がないことを示す。 | `proved` |
| `MergeOrderCounterexample.steps_lawful` | `theorem` | counterexample の各 primitive transition が locally lawful であることを示す。 | `proved` |
| `MergeOrderCounterexample.not_twoStepObservationCommutative` | `theorem` | locally lawful な二つの two-step order が観測上可換でない小例を示す。 | `proved` |
| `MergeOrderCounterexample.mergeOrderSensitive` | `theorem` | 同じ小例が selected merge-order sensitive であることを示す。 | `proved` |
| `MergeOrderCounterexample.mergeOrderSensitivity_eq_one` | `theorem` | 同じ小例の bounded sensitivity metric が `1` に評価されることを示す。 | `proved` |
| `MergeOrderCounterexample.selectedDistance` | `def` | counterexample の final observation 差を equality distance で読む selected distance。 | `defined only` |
| `MergeOrderCounterexample.curvatureSchema` | `def` | counterexample 用 distance と empirical / measurement non-conclusion boundary を束ねる schema。 | `defined only` |
| `MergeOrderCounterexample.operationCommutatorCurvature_eq_one` | `theorem` | 同じ counterexample の距離付き commutator curvature が `1` に評価されることを示す。 | `proved` |
| `MergeOrderCounterexample.operationCommutatorCurvature_ne_zero` | `theorem` | 同じ counterexample の距離付き commutator curvature が nonzero であることを示す。 | `proved` |
| `MergeOrderCounterexample.curvatureSchema_records_boundaries` | `theorem` | curvature schema が empirical PR risk、incident risk、review cost、unmeasured axes、non-conclusions の境界を記録することを示す。 | `proved` |

## Diagram Filler

File: `Formal/Arch/Evolution/DiagramFiller.lean`

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureDiagram` | `structure` | 同じ start / target state を持つ二つの有限 architecture path を semantic diagram skeleton として束ねる。 | `defined only` |
| `DiagramFiller` | `def` | `ArchitecturePath.PathHomotopy` により、diagram の左右 path が finite path calculus 上で fillable であることを表す。 | `defined only` |
| `NonFillabilityWitness` | `structure` | domain-specific witness value と、任意の `DiagramFiller` を反駁する soundness 証拠を束ねる。 | `defined only` |
| `NonFillabilityWitnessFor` | `def` | `NonFillabilityWitness` が特定の witness value `w` についての証人であること。 | `defined only` |
| `obstructionAsNonFillability_sound` | `theorem` | `NonFillabilityWitnessFor D w` から `¬ DiagramFiller D` を得る片方向 soundness theorem。 | `proved` |
| `diagramFiller_observation_eq` | `theorem` | observation-preserving generator 前提の下で、`DiagramFiller D` から `Obs D.lhs = Obs D.rhs` を得る。 | `proved` |
| `observationDifference_refutesDiagramFiller` | `theorem` | `Obs D.lhs ≠ Obs D.rhs` から、selected observation を保存する generator で作る `DiagramFiller D` が存在しないことを示す。 | `proved` |
| `observationDifference_nonFillabilityWitnessFor` | `theorem` | selected observation 差分を、caller-selected witness value の `NonFillabilityWitnessFor` として package する。 | `proved` |
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
| `CouponDiscountExample.RoundingRepairFill` | `def` | rounding observation を任意の suffix context で保存する selected repair fill contract。 | `defined only` |
| `CouponDiscountExample.pathHomotopy_preserves_roundingTrace_append` | `theorem` | `ArchitecturePath.PathHomotopy.observation_eq_append` の特殊化として、selected filler generator から生成される path homotopy が任意 suffix context で `roundingTrace` を保存することを示す。 | `proved` |
| `CouponDiscountExample.pathHomotopy_preserves_roundingTrace` | `theorem` | `ArchitecturePath.PathHomotopy.observation_eq` の特殊化として、selected filler generator から生成される path homotopy が `roundingTrace` を保存することを示す。 | `proved` |
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
ambient semantic coverage、finite universe 外の witness coverage、未測定 semantic axis の
zero 性 は主張しない。

## Monodromy Measurement Minimal Guardrail

File: `Formal/Arch/Signature/MonodromyMeasurement.lean`

この節は ArchSig の monodromy / boundary-holonomy reading を Lean 側で読むための
minimal guardrail である。完全な monodromy 理論ではなく、finite family、selected axis、
axis-local defect、nonnegative weighted aggregate に相対化した bounded theorem package を置く。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `MonodromyMeasurement.MeasuredSquare` | `structure` | 一つの reading が比較する selected path / operation pair。 | `defined only` |
| `MonodromyMeasurement.SelectedAxis` | `structure` | bounded measurement policy が選んだ observation axis。 | `defined only` |
| `MonodromyMeasurement.AxisDefect` | `structure` | selected square / axis 上の `Nat` defect と、zero / nonzero の sound reading boundary。 | `defined only` |
| `MonodromyMeasurement.AxisDefect.observationDiff_of_nonzero` | `theorem` | defect nonzero から selected observation difference を得る。 | `proved` |
| `MonodromyMeasurement.AxisDefect.observationEq_of_zero` | `theorem` | defect zero から selected observation equality を得る。 | `proved` |
| `MonodromyMeasurement.WeightedAxisDefect` | `structure` | finite aggregate に入れる selected defect と nonnegative natural weight。 | `defined only` |
| `MonodromyMeasurement.FiniteMeasuredSquareFamily` | `abbrev` | weighted selected defects の finite list。 | `defined only` |
| `MonodromyMeasurement.WeightedAxisDefect.contribution` | `def` | `weight * defect.value` としての nonnegative contribution。 | `defined only` |
| `MonodromyMeasurement.weightedAggregate` | `def` | finite family の nonnegative weighted aggregate。 | `defined only` |
| `MonodromyMeasurement.localZero_of_weightedAggregate_zero` | `theorem` | aggregate zero から positive-weight entry の local defect zero を得る。 | `proved` |
| `MonodromyMeasurement.observationEq_of_weightedAggregate_zero` | `theorem` | aggregate zero と positive weight から local selected observation equality を得る。 | `proved` |
| `MonodromyMeasurement.localSelectedAxis` | `def` | endpoint-indexed `ArchitecturePath` observation を local selected axis として読む wrapper。 | `defined only` |
| `MonodromyMeasurement.nonzero_refutes_selectedPathHomotopy` | `theorem` | nonzero defect から、既存 `PathHomotopy.observation_eq` API に相対化された selected homotopy refutation を得る。 | `proved` |
| `MonodromyMeasurement.nonzero_nonFillabilityWitnessFor` | `theorem` | nonzero defect から、既存 `observationDifference_nonFillabilityWitnessFor` API に相対化された non-fillability witness package を得る。 | `proved` |
| `MonodromyMeasurement.GuardrailBoundary` | `structure` | bounded finite family / selected axis / non-completeness 境界を明示する boundary record。 | `defined only` |

Non-conclusions: all-path homotopy completeness、all-axis semantic completeness、
ArchSig measurement correctness in the wild、global safety は
主張しない。aggregate zero は positive-weight selected entries にだけ local zero を与え、
zero-weight entry や unmeasured square の zero には読まない。

## ACTS Minimal Theorem Guardrail

File: `Formal/Arch/Signature/CurvatureTransferSpectrum.lean`

この節は Architecture Curvature Transfer Spectrum (ACTS) を Lean 側で読むための
minimal guardrail である。ArchSig implementation correctness ではなく、finite
curvature-support family、positive weight、nonempty witness support、finite
nonnegative transfer relation、positive closed transfer edge に相対化した bounded
theorem package を置く。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `CurvatureTransferSpectrum.MeasuredCurvatureSupport` | `structure` | selected axis、witness support、nonempty support 証拠、curvature、weight を持つ finite support row。 | `defined only` |
| `CurvatureTransferSpectrum.MeasuredCurvatureSupport.contribution` | `def` | `weight * curvature` としての nonnegative weighted contribution。 | `defined only` |
| `CurvatureTransferSpectrum.FiniteCurvatureSupportFamily` | `abbrev` | measured curvature support row の finite list。 | `defined only` |
| `CurvatureTransferSpectrum.weightedCurvatureSupportAggregate` | `def` | finite support family の weighted aggregate。 | `defined only` |
| `CurvatureTransferSpectrum.SelectedMeasuredCurvatureZero` | `def` | supplied finite support family のすべての selected measured curvature が zero である predicate。 | `defined only` |
| `CurvatureTransferSpectrum.localCurvature_zero_of_weightedCurvatureSupportAggregate_zero` | `theorem` | aggregate zero から positive-weight measured support row の local curvature zero を得る。 | `proved` |
| `CurvatureTransferSpectrum.weightedCurvatureSupportAggregate_zero_of_selectedMeasuredCurvatureZero` | `theorem` | selected measured curvature all zero から aggregate zero を得る。 | `proved` |
| `CurvatureTransferSpectrum.weightedCurvatureSupportAggregate_zero_iff_selectedMeasuredCurvatureZero` | `theorem` | all rows positive-weight の下で aggregate zero と selected measured curvature all zero が同値。 | `proved` |
| `CurvatureTransferSpectrum.NonnegativeTransferEdge` | `structure` | finite transfer relation の source / target / nonnegative Nat weight edge。 | `defined only` |
| `CurvatureTransferSpectrum.FiniteNonnegativeTransferRelation` | `abbrev` | nonnegative transfer edge の finite list。 | `defined only` |
| `CurvatureTransferSpectrum.PositiveClosedTransferEdge` | `def` | source = target かつ positive weight の transfer edge。 | `defined only` |
| `CurvatureTransferSpectrum.HasPositiveClosedTransferEdge` | `def` | finite relation が positive closed transfer edge を含む predicate。 | `defined only` |
| `CurvatureTransferSpectrum.BoundedRecurrentObstructionReading` | `structure` | positive closed transfer edge を current-state recurrent obstruction support として包む bounded reading。 | `defined only` |
| `CurvatureTransferSpectrum.hasPositiveClosedTransferEdge_of_recurrentReading` | `theorem` | recurrent reading から finite relation 内の positive closed edge 存在を得る。 | `proved` |
| `CurvatureTransferSpectrum.recurrentReading_of_positiveClosedTransferEdge` | `def` | finite relation 内の positive closed edge を recurrent reading として包む constructor。 | `defined only` |
| `CurvatureTransferSpectrum.ACTSNonConclusionClause` | `inductive` | ACTS theorem package の non-conclusion clause。 | `defined only` |
| `CurvatureTransferSpectrum.requiredNonConclusions` | `def` | required non-conclusion clause の finite list。 | `defined only` |
| `CurvatureTransferSpectrum.ACTSMinimalTheoremGuardrail` | `structure` | support family、transfer relation、non-conclusions を束ねる minimal theorem guardrail package。 | `defined only` |
| `CurvatureTransferSpectrum.ACTSMinimalTheoremGuardrail.RecordsRequiredNonConclusions` | `def` | package が required non-conclusion clauses を保持する predicate。 | `defined only` |
| `CurvatureTransferSpectrum.ACTSMinimalTheoremGuardrail.recordsRequiredNonConclusions_of_eq_required` | `theorem` | package の nonConclusions が required list と一致すれば boundary を保持する。 | `proved` |

Non-conclusions: この theorem package は finite supplied support / transfer relation に
相対化された guardrail であり、ArchSig implementation correctness、global semantic
flatness、future safety、empirical incident/cost calibration は
主張しない。positive closed transfer edge は current-state recurrent obstruction
support として読むだけで、future incident prediction や repair safety evidence ではない。

## Homotopy-Holonomy Stokes Minimal Guardrail

File: `Formal/Arch/Signature/HomotopyHolonomyStokes.lean`

この節は Homotopy / Holonomy / Stokes readings を Lean 側で読むための minimal
guardrail である。ArchSig implementation correctness や一般 homology 理論ではなく、
finite measured path pair、selected continuation、measured loop、finite measured
2-cell filling、bounded Stokes-style inequality、unfilled loop non-conclusion に
相対化した theorem package を置く。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `HomotopyHolonomyStokes.MeasuredPathPair` | `structure` | bounded homotopy reading が比較する path pair。 | `defined only` |
| `HomotopyHolonomyStokes.SelectedContinuation` | `structure` | LawPolicy profile が選ぶ `Nat` 値 continuation。 | `defined only` |
| `HomotopyHolonomyStokes.selectedHolonomy` | `def` | selected continuation 上で path pair の holonomy を `0/1` として読む。 | `defined only` |
| `HomotopyHolonomyStokes.MeasuredLoop` | `structure` | path pair と selected boundary holonomy を束ねる measured loop。 | `defined only` |
| `HomotopyHolonomyStokes.MeasuredTwoCell` | `structure` | measured boundary path pair、local curvature、weight を持つ finite 2-cell row。 | `defined only` |
| `HomotopyHolonomyStokes.MeasuredTwoCell.contribution` | `def` | `weight * localCurvature` としての nonnegative contribution。 | `defined only` |
| `HomotopyHolonomyStokes.FiniteMeasuredTwoCellFamily` | `abbrev` | measured 2-cell row の finite list。 | `defined only` |
| `HomotopyHolonomyStokes.localCurvatureAggregate` | `def` | finite filling の weighted local curvature aggregate。 | `defined only` |
| `HomotopyHolonomyStokes.MeasuredFilling` | `structure` | measured loop、finite 2-cell family、bounded Stokes assumption を束ねる filling。 | `defined only` |
| `HomotopyHolonomyStokes.boundedStokesInequality_of_measuredFilling` | `theorem` | measured filling から boundary holonomy ≤ local curvature aggregate を取り出す。 | `proved` |
| `HomotopyHolonomyStokes.exists_nonzero_localCurvature_of_aggregate_nonzero` | `theorem` | aggregate nonzero から positive-weight nonzero local curvature cell の存在を得る。 | `proved` |
| `HomotopyHolonomyStokes.localCurvatureAggregate_nonzero_of_boundaryHolonomy_nonzero` | `theorem` | bounded filling の boundary holonomy nonzero から local curvature aggregate nonzero を得る。 | `proved` |
| `HomotopyHolonomyStokes.exists_nonzero_localCurvature_of_boundaryHolonomy_nonzero` | `theorem` | measured filling の boundary holonomy nonzero から positive-weight nonzero measured local curvature cell の存在を得る。 | `proved` |
| `HomotopyHolonomyStokes.UnfilledLoopReading` | `structure` | missing filler evidence と violation conclusion refusal を持つ unfilled loop reading。 | `defined only` |
| `HomotopyHolonomyStokes.unfilledLoop_not_violationConclusion` | `theorem` | unfilled loop reading は violation conclusion を結論しない。 | `proved` |
| `HomotopyHolonomyStokes.HomotopyStokesNonConclusionClause` | `inductive` | Homotopy / Holonomy / Stokes theorem package の non-conclusion clause。 | `defined only` |
| `HomotopyHolonomyStokes.requiredNonConclusions` | `def` | required non-conclusion clause の finite list。 | `defined only` |
| `HomotopyHolonomyStokes.HomotopyHolonomyStokesGuardrail` | `structure` | measured fillings、unfilled loops、non-conclusions を束ねる minimal theorem guardrail package。 | `defined only` |
| `HomotopyHolonomyStokes.HomotopyHolonomyStokesGuardrail.RecordsRequiredNonConclusions` | `def` | package が required non-conclusion clauses を保持する predicate。 | `defined only` |
| `HomotopyHolonomyStokes.HomotopyHolonomyStokesGuardrail.recordsRequiredNonConclusions_of_eq_required` | `theorem` | package の nonConclusions が required list と一致すれば boundary を保持する。 | `proved` |

Non-conclusions: この theorem package は finite measured filling に相対化された
guardrail であり、ArchSig implementation correctness、global homotopy completeness、
global homology computation、future safety、empirical calibration、extractor
completeness は主張しない。unfilled loop は architectural hole / missing filler
evidence として読むだけで、automatic violation conclusion ではない。

## Static / Semantic Counterexample

File: `Formal/Arch/Examples/StaticSemanticCounterexample.lean`

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

File: `Formal/Arch/Extension/Flatness.lean`

#320 の Flatness / Feature Extension 統合 theorem package では、
#325 の API 監査結果を踏まえ、中心入口を次のように読む。

- `ArchitectureFlatWithin` が primary な bounded / coverage-aware flatness predicate である。
- `LawfulExtensionPreservesFlatness` は static split extension だけからではなく、extension coverage、static side conditions、runtime coverage / flatness、semantic coverage / flatness を明示前提として `ArchitectureFlatWithin` を構成する。
- `LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation` は `RuntimeSemanticSplitPreservation` により runtime / semantic flatness 前提を discharge する接続 corollary であり、runtime telemetry completeness、semantic universe completeness は主張しない。
- `ArchitectureFlat` は `GlobalFlatCertificate` による completion predicate であり、`globalFlat_of_within_exhaustive` の exhaustive coverage / exact observation / recorded non-conclusions 前提なしに bounded theorem package から昇格しない。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ArchitectureFlatnessModel` | `structure` | static / runtime / semantic の三層 flatness を一つの architecture model として束ねる。runtime policy と semantic required / measured diagram universe を明示し、未測定軸を zero と見なさない境界を置く。 | `defined only` |
| `ArchitectureObject` | `abbrev` | Foundations-level bounded architecture object。現在は `ArchitectureFlatnessModel` として、selected carrier / policy / observation / measured semantic universe に相対化して読む。 | `defined only` |
| `ArchitectureFlatnessModel.selectedPresentation` | `def` | bounded model 自身の component carrier 上の selected presentation。ambient repository completeness は主張しない。 | `defined only` |
| `ArchitectureFlatnessModel.staticRestriction_eq_staticEdge` | `theorem` | bounded selected presentation を通した static restriction が selected static edge と一致する。 | `proved` |
| `ArchitectureFlatnessModel.runtimeRestriction_eq_runtimeEdge` | `theorem` | bounded selected presentation を通した runtime restriction が selected runtime edge と一致する。 | `proved` |
| `ArchitectureFlatnessModel.staticCompleteForSelectedPresentation` | `theorem` | model 自身の selected static relation は identity presentation に complete。ambient source-observation layer ではない。 | `proved` |
| `ArchitectureFlatnessModel.runtimeCompleteForSelectedPresentation` | `theorem` | model 自身の selected runtime relation は identity presentation に complete。runtime telemetry completeness ではない。 | `proved` |
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
| `FeatureDiagramsCommute` | `def` | selected measured semantic diagrams がすべて commute すること。ambient semantic coverage は含めない。 | `defined only` |
| `semanticFlatWithin_of_featureDiagramsCommute` | `theorem` | semantic coverage 前提の下で selected diagram commutation から `SemanticFlatWithin` を得る。 | `proved` |
| `featureDiagramsCommute_of_semanticFlatWithin` | `theorem` | `SemanticFlatWithin` を selected diagram commutation として読み替える。 | `proved` |
| `featureDiagramsCommute_iff_semanticFlatWithin` | `theorem` | semantic coverage 前提に相対化して selected diagram commutation と `SemanticFlatWithin` を同値にする。 | `proved` |
| `RuntimeSemanticSplitPreservation` | `structure` | runtime interaction protection と selected semantic diagram commutation を束ねる bounded runtime / semantic split preservation package。 | `defined only` |
| `NoUnmeasuredRequiredAxis` | `def` | static / runtime / semantic の required evidence が bounded universes で測定済みであること。 | `defined only` |
| `ArchitectureFlatWithin` | `def` | coverage-aware な bounded architecture flatness。coverage と三層 flatness を束ね、ambient source observation / telemetry / semantic universe completeness は主張しない。 | `defined only` |
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
| `ExtensionCoverageFailureCoverage` | `def` | `ExtensionCoverageComplete` 失敗が selected coverage witness family で cover されるという bounded coverage / exactness 前提。source-observation layer や runtime / semantic flatness は主張しない。 | `defined only` |
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
| `SplitFeatureExtensionWithinNonConclusions` | `def` | bounded split feature extension package が global `ArchitectureFlat`、runtime / semantic completeness を自動導出しないことを記録する marker。 | `defined only` |
| `SplitFeatureExtensionWithin` | `structure` | `StaticSplitExtension`、extension coverage、static side conditions、runtime / semantic split evidence、non-conclusions を束ねる bounded public package。 | `defined only` |
| `splitFeatureExtensionWithin_of_runtimeSemanticSplitPreservation` | `def` | 既存の runtime / semantic split preservation evidence から `SplitFeatureExtensionWithin` を構成する入口。 | `defined only` |
| `splitFeatureExtensionWithin_recordsNonConclusions` | `theorem` | `SplitFeatureExtensionWithin` から記録済み non-conclusions を取り出す。 | `proved` |
| `LawfulExtensionPreservesFlatness` | `theorem` | extension coverage、runtime coverage / flatness、semantic coverage / flatness を明示前提として、lawful static split extension から bounded `ArchitectureFlatWithin` を構成する。 | `proved` |
| `LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation` | `theorem` | runtime / semantic split preservation package で `LawfulExtensionPreservesFlatness` の runtime / semantic flatness 前提を discharge する。 | `proved` |
| `architectureFlatWithin_of_splitFeatureExtensionWithin` | `theorem` | `SplitFeatureExtensionWithin` から induced flatness model の bounded `ArchitectureFlatWithin` を得る public preservation theorem。 | `proved` |

## ArchMap Observation Layer

Files:

- `Formal/Arch/Observation/ArchMap.lean`
- `Formal/Arch/Observation/ArchMapGeneratedHandoff.lean`

この節は ArchMap を pure AAT core の外側にある observation layer として索引する。
ArchMap は Atom を観測するが、Atom existence / AAT を生成・定義しない。一方で、観測済み
Atom と `AtomShapePresentation`、composition / required-port evidence がそろう場合は、
観測済み Atom selection を `GeneratedMolecule` / `GeneratedArchitectureObject` へ渡す
positive handoff を持つ。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Observation.ArchMapObservationLayer` | `structure` | `AtomAxiomSystem` と `AtomPresentation` に相対化された ArchMap observation layer。selected source、raw candidate boundary、validation / coverage / exactness boundary、non-conclusions を持つ。 | `defined only` |
| `Observation.ArchMapObservationLayer.observes_atoms` | `theorem` | ArchMap が atom を観測する boundary evidence を取り出す。 | `proved` |
| `Observation.ArchMapObservationLayer.archmap_does_not_create_atoms` | `theorem` | ArchMap observation が Atom 公理系の atom existence を生成しないことを取り出す。 | `proved` |
| `Observation.ArchMapObservationLayer.archmap_does_not_define_aat` | `theorem` | ArchMap が AAT を定義しないことを取り出す。 | `proved` |
| `Observation.ArchMapObservationLayer.raw_candidate_is_not_atom_truth` | `theorem` | raw candidate は atom truth ではないことを presentation boundary から取り出す。 | `proved` |
| `Observation.ArchMapObservationLayer.missing_is_not_measured_zero` | `theorem` | missing observation は measured-zero atom ではないことを presentation boundary から取り出す。 | `proved` |
| `Observation.ArchMapObservationLayer.missing_is_not_atom_absence` | `theorem` | missing observation は atom absence ではないことを presentation boundary から取り出す。 | `proved` |
| `Observation.ArchMapObservedAtomSelection` | `structure` | ArchMap の observed atom predicate と `AtomShapePresentation`、composition graph、required-port matching を束ね、観測済み atom selection を generated algebra へ渡す入力を表す。 | `defined only` |
| `ArchMapObservedAtomSelection.selected_atoms_observed`, `selected_atoms_primitive`, `toGeneratedMolecule`, `toGeneratedMolecule_atom_observed`, `toGeneratedMolecule_observation_does_not_create_atoms` | `theorem` / `def` | selected atom が ArchMap observed-atom evidence を持つことを保持し、その selection から `GeneratedMolecule` を構成する。handoff 後も observation は atom を生成しない boundary を保つ。 | `proved` / `defined only` |
| `Observation.ArchMapGeneratedArchitectureObjectInput`, `toGeneratedArchitectureObject`, `toGeneratedArchitectureObject_carrier_observed`, `toGeneratedArchitectureObject_observation_does_not_create_atoms` | `structure` / `def` / `theorem` | observed atom selection から finite carrier evidence を添えて `GeneratedArchitectureObject` を構成し、各 carrier が observed atom evidence に戻れることを固定する。 | `defined only` / `proved` |

Non-conclusions: ArchMap validation pass、AIR projection success、ambient semantic coverage、certified atom truth、zero-curvature theorem discharge は結論しない。

## Architecture Core / Certified Architecture

File: `Formal/Arch/Extension/CertifiedArchitecture.lean`

Issue [#287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/287)
の対象範囲は、数学設計書 9 の `ArchitectureCore` / `CertifiedArchitecture`
を既存の bounded flatness、finite `ComponentUniverse`、`ProofObligation`
API に接続する proof-carrying schema として固定することである。
Issue [#838](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/838)
では、`ArchitectureCore` が Foundations で引用する selected-presentation claim
boundary を theorem package として束ねる。
runtime telemetry の完全性、global semantic universe
completeness は主張しない。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `RuntimeDependencyRole` | `inductive` | runtime dependency を raw / protected / forbidden / unprotected の selected role metadata として区別する。telemetry completeness は主張しない。 | `defined only` |
| `ArchitectureCore` | `structure` | `ArchitectureFlatnessModel`、static `ComponentUniverse`、component equality / static edge / runtime edge / boundary policy / abstraction policy の decidability、runtime role、semantic required diagram decidability を束ねる最小 core。 | `defined only` |
| `ArchitectureCore.selectedPresentation` | `def` | core 自身の component carrier 上の selected presentation。ambient repository extraction とは別前提。 | `defined only` |
| `ArchitectureCore.selectedPresentationJudgement_iff` | `theorem` | core の selected presentation 上の `AATJudgement` が、その presentation での claim evaluation と一致する。 | `proved` |
| `ArchitectureCore.toFlatnessModel` | `def` | proof-carrying wrapper から既存の flatness model を取り出す。 | `defined only` |
| `ArchitectureCore.staticLawModel` | `def` | core の finite component universe から既存の `ArchitectureLawModel` を構成する。 | `defined only` |
| `ArchitectureCore.measuredSemanticUniverse` | `def` | core が保持する measured semantic diagram universe を取り出す。 | `defined only` |
| `ArchitectureCore.runtimeDependencyRole` | `def` | component pair に対する selected runtime dependency role を取り出す。 | `defined only` |
| `ArchitectureCore.staticRestriction_eq_staticEdge` | `theorem` | core の selected presentation を通した static restriction が core の selected static edge と一致する。 | `proved` |
| `ArchitectureCore.runtimeRestriction_eq_runtimeEdge` | `theorem` | core の selected presentation を通した runtime restriction が core の selected runtime edge と一致する。 | `proved` |
| `ArchitectureCore.staticGraphRestriction_eq_staticGraph` | `theorem` | core の selected presentation を通した static graph restriction が core の selected static graph と一致する。 | `proved` |
| `ArchitectureCore.runtimeGraphRestriction_eq_runtimeGraph` | `theorem` | core の selected presentation を通した runtime graph restriction が core の selected runtime graph と一致する。 | `proved` |
| `ArchitectureCore.staticCompleteForSelectedPresentation` | `theorem` | core 自身の selected static relation は selected presentation に complete。ambient source-observation layer は AAT theorem package の外で扱う。 | `proved` |
| `ArchitectureCore.runtimeCompleteForSelectedPresentation` | `theorem` | core 自身の selected runtime relation は selected presentation に complete。runtime telemetry completeness は結論しない。 | `proved` |
| `ArchitectureCore.staticCompleteGraphForSelectedPresentation` | `theorem` | #837 の `CompleteForGraph` bridge を使い、core 自身の selected static graph が selected presentation に complete であることを graph-level に読む。 | `proved` |
| `ArchitectureCore.runtimeCompleteGraphForSelectedPresentation` | `theorem` | #837 の `CompleteForGraph` bridge を使い、core 自身の selected runtime graph が selected presentation に complete であることを graph-level に読む。 | `proved` |
| `ArchitectureCore.component_mem_staticUniverse` | `theorem` | core の `ComponentUniverse.covers` から component membership を取り出す。 | `proved` |
| `ArchitectureCore.staticCoverageComplete` | `theorem` | core の static dependency evidence が `ComponentUniverse` で cover されることを取り出す。 | `proved` |
| `ArchitectureCore.SelectedClaimBoundary` | `structure` | Foundations 向け claim boundary package。`judgementBridge`、static / runtime restriction、graph restriction、relation / graph completeness、static coverage を selected presentation 相対で束ねる。 | `defined only` |
| `ArchitectureCore.selectedClaimBoundary` | `theorem` | 任意の `ArchitectureCore` から `SelectedClaimBoundary` を構成する。ambient repository completeness、runtime telemetry completeness、global semantic universe completeness は結論しない。 | `proved` |
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

File: `Formal/Arch/Signature/Obstruction.lean`

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

File: `Formal/Arch/Signature/Curvature.lean`

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

File: `Formal/Arch/Law/Lawfulness.lean`

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

## Finite Static Structural Core Formal Anchor

Files: `Formal/Arch/Signature/SignatureLawfulness.lean`,
`Formal/Arch/Signature/Signature.lean`, `Formal/Arch/Core/Finite.lean`,
`Formal/Arch/AAT/GeneratedSignature.lean`

Issue [#787](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/787)
の投稿版向け formal anchor は、AAT 全体を static structural theorem へ縮約するものではない。
`ArchitectureLawModel` 上で finite static universe、required law family、required witness family、
selected Signature axes、coverage / exactness assumptions、non-conclusions を明示し、
査読者が Lean source で検査できる proved theorem package として提示する。

この anchor の theorem boundary は次である。

| 境界 | Lean 名 | 読み |
| --- | --- | --- |
| universe | `ArchitectureSignature.ArchitectureLawModel` | `ArchGraph`, `InterfaceProjection`, `AbstractGraph`, `Observation`, finite `ComponentUniverse`, boundary / abstraction policy, `lspPairClosed` を束ねる。 |
| law family | `ArchitectureSignature.ArchitectureLawful` | `WalkAcyclic`, `ProjectionSound`, `LSPCompatible`, boundary policy soundness, abstraction policy soundness。 |
| witness family | `ArchitectureSignature.ArchitectureRequiredLawWitness`, `ArchitectureSignature.architectureMeasuredWitnesses`, `ArchitectureSignature.architectureBad` | cycle, projection, LSP, boundary policy, abstraction policy の selected required obstruction witness family。 |
| signature axes | `selectedRequiredLawAxes`, `ArchitectureSignature.RequiredSignatureAxesZero`, `ArchitectureSignature.ArchitectureLawModel.signatureOf` | `.hasCycle`, `.projectionSoundnessViolation`, `.lspViolationCount`, `.boundaryViolationCount`, `.abstractionViolationCount` の available zero。 |
| coverage | `ComponentUniverse`, `ArchitectureLawModel.lspPairClosed`, `ArchitectureSignature.architectureLawFamily_completeCoverage` | finite universe coverage、edge closure、same-abstraction pair coverage、required witness coverage。 |
| exactness | `ArchitectureSignature.hasCycle_axisExact`, `ArchitectureSignature.projectionSoundnessViolation_axisExact`, `ArchitectureSignature.lspViolationCount_axisExact`, `ArchitectureSignature.boundaryViolation_axisExact`, `ArchitectureSignature.abstractionViolation_axisExact`, `ArchitectureSignature.architecture_requiredAxisExact` | 各 selected axis の available zero と対応 obstruction witness 不在を接続する。 |
| anchor theorem | `ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero` | selected required `ArchitectureLawful X` と `RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X)` を同値にする。 |
| package theorem | `ArchitectureSignature.architectureLawful_iff_architectureZeroCurvatureTheoremPackage` | selected required lawfulness と `ArchitectureZeroCurvatureTheoremPackage X` を同値にする。 |
| generated source theorem | `AAT.GeneratedArchitectureLawModel.generatedArchitectureZeroCurvatureTheoremPackage_holds`, `AAT.GeneratedArchitectureLawModel.generatedArchitectureLawful_iff_generatedArchitectureZeroCurvatureTheoremPackage` | static structural core package を `GeneratedArchitectureLawModel` 入力から発火させ、hand-authored `ArchitectureLawModel` row を AAT source-of-truth として扱わない。 |
| derived diagnostics | `ArchitectureSignature.MatrixDiagnosticCorollaries`, `ArchitectureSignature.matrixDiagnosticCorollaries_of_requiredSignatureAxesZero` | adjacency nilpotence、populated `nilpotencyIndexOfFinite`、zero structural spectral radius は derived diagnostic corollary として読む。 |

`zero-curvature` はここでは differential-geometric curvature ではなく、selected law universe に
対する required obstruction valuation が zero であるという terminology である。
`Formal/Arch/Signature/Curvature.lean` の numerical curvature theorem package は別の
bounded diagram bridge であり、この formal anchor の required Signature axes には含めない。

Non-conclusions: この anchor は runtime / semantic completeness、global semantic flatness、
relation complexity や empirical cost correlation、実コードからの
完全な `ComponentUniverse` 生成、全 operation の preservation、全 observation axis の保存を
主張しない。

## Signature-Integrated Lawfulness

File: `Formal/Arch/Signature/SignatureLawfulness.lean`

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
| `AAT.GeneratedArchitectureLawModel.generatedArchitectureZeroCurvatureTheoremPackage` | `def` | generated relation predicate から projected law model の decidable relation instances を回収し、static structural core package を generated law model 上の Prop として読む。 | `defined only` |
| `AAT.GeneratedArchitectureLawModel.generatedArchitectureZeroCurvatureTheoremPackage_holds` | `theorem` | generated lawfulness から static structural core package を generated law model 上で得る。hand-authored `ArchitectureLawModel` package を caller が与えない。 | `proved` |
| `AAT.GeneratedArchitectureLawModel.generatedArchitectureLawful_iff_generatedArchitectureZeroCurvatureTheoremPackage` | `theorem` | generated lawfulness と generated static structural core package が同値であることを示す。 | `proved` |
| `AtomGeneratedSignatureExamples.atomGeneratedSignature_zeroCurvatureTheoremPackage`, `AtomGeneratedSignatureExamples.atomGeneratedSignature_lawful_iff_zeroCurvatureTheoremPackage` | `theorem` | concrete generated component example で static structural core package が Atom-generated law model から発火することを固定する。 | `proved` |
| `ArchitectureSignature.localReplacementContract_requiredSignatureProjectionLSPAxes` | `theorem` | `LocalReplacementContract` から selected required Signature axes の projection / LSP が available-and-zero であることを得る derived corollary bridge。 | `proved` |
| `ArchitectureSignature.architectureLawful_of_localReplacementContract` | `theorem` | closed-walk acyclicity、`LocalReplacementContract`、boundary / abstraction policy soundness から `ArchitectureLawful X` を得る。 | `proved` |
| `ArchitectureSignature.requiredSignatureAxesZero_of_localReplacementContract` | `theorem` | closed-walk acyclicity、`LocalReplacementContract`、boundary / abstraction policy soundness から `RequiredSignatureAxesZero (signatureOf X)` を得る derived zero-curvature bridge。 | `proved` |
| `ArchitectureSignature.architectureZeroCurvatureTheoremPackage_of_localReplacementContract` | `theorem` | LocalReplacement と残りの static laws から static structural core の QED package を得る derived bridge。 | `proved` |
| `AtomSurfacePresented`, `AtomDeltaPreservesSurface`, `AtomPresentationOperation` | `def` / `structure` | pure AAT surface 上の selected atoms が presentation で測定付きに観測され、atom delta で保存されることを束ねる Signature-free operation-level bridge。 | `defined only` |
| `AtomPresentationOperation.target_presented_of_source`, `preservesSurfaceInvariant`, `ops_mem_surfaceInvariant` | `theorem` | surface を保存する atom presentation operation から、target presentation の surface coverage、通常の `PreservesInvariant`、singleton invariant family 上の `Ops` membership を導く。 | `proved` |

### 零曲率 theorem package の読み順

1. `architectureLawCandidateRole_requiredLaw_iff` で required law が 5 条件に限られることを確認する。
2. `architectureLawful_iff_requiredSignatureAxesZero` を static structural core の QED の主 theorem として読む。
3. LocalReplacement / state-effect laws は `localReplacementContract_requiredSignatureProjectionLSPAxes`, `requiredSignatureAxesZero_of_localReplacementContract`, `stateTransitionLawFamilyLawful_iff_noStateTransitionLawFamilyObstruction`, `effectBoundaryLawFamilyLawful_iff_noEffectBoundaryLawFamilyObstruction` で derived corollary として読む。
4. nilpotency / spectral diagnostics は `MatrixDiagnosticCorollaries` と `matrixDiagnosticCorollaries_of_requiredSignatureAxesZero` で読む。
5. package は `architectureLawful_iff_architectureZeroCurvatureTheoremPackage` を入口にし、static structural core の QED として読む。runtime / empirical axis はこの package に含めず、numerical curvature は別の bounded diagram bridge として読む。

## State Transition / Effect Boundary Laws

Files: `Formal/Arch/Law/StateEffect.lean`, `Formal/Arch/Patterns/StateTransitionDesignPattern.lean`, `Formal/Arch/Patterns/EventSourcingSagaDesignPattern.lean`

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
| `stateTransitionDesignPattern_records_nonConclusion` | `theorem` | event log completeness、運用コスト改善、CRUD 一般 theorem 化を non-conclusion として記録する。 | `proved` |
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
| `eventSourcingDesignPattern_records_nonConclusion` | `theorem` | event log completeness、projection completeness、運用コスト改善を non-conclusion として記録する。 | `proved` |
| `SagaPatternState` | `structure` | carrier と selected compensation cases を束ねる Saga state。 | `defined only` |
| `SagaWeakRecoveryLawful` | `def` | Saga compensation を selected weak recovery law として読む predicate。 | `defined only` |
| `SagaOperation` | `structure` | source / target state と target 側 weak recovery lawfulness を持つ proof-carrying operation。 | `defined only` |
| `sagaOperation_toStateTransitionOperation` | `def` | Saga operation を汎用 `StateTransitionOperation` として読む bridge。 | `defined only` |
| `sagaOperation_stateTransitionClosure` | `theorem` | Saga operation を汎用状態遷移 closure law に接続する。 | `proved` |
| `SagaInvariant` | `inductive` | compensation weak recovery と aggregate lawfulness を selected invariant axis として列挙する。 | `defined only` |
| `sagaDesignPattern` | `def` | Saga を `DesignPattern` schema に接続する theorem package。 | `defined only` |
| `sagaDesignPattern_closure_law` | `theorem` | Saga `DesignPattern` から operation-to-invariant / invariant-to-operation closure law を取り出す。 | `proved` |
| `sagaDesignPattern_records_nonConclusion` | `theorem` | 補償の一般逆射性、全 failure mode coverage、運用回復コスト改善 を non-conclusion として記録する。 | `proved` |
| `EffectBoundaryLawFamilyLawful` | `def` | effect-boundary replay / roundtrip / compensation law family の aggregate lawfulness。 | `defined only` |
| `NoEffectBoundaryLawFamilyObstruction` | `def` | effect-boundary replay / roundtrip / compensation law family の aggregate obstruction absence。 | `defined only` |
| `effectBoundaryLawFamilyLawful_iff_noEffectBoundaryLawFamilyObstruction` | `theorem` | effect-boundary law family package の lawfulness と obstruction absence を接続する。 | `proved` |

## Signature v0

File: `Formal/Arch/Signature/Signature.lean`

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

File: `Formal/Arch/Core/Finite.lean`

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

File: `Formal/Arch/Core/Matrix.lean`

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

File: `Formal/Arch/Signature/DependencyObstruction.lean`

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

File: `Formal/Arch/Signature/AnalyticRepresentation.lean`

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
| `Chapter11AnalyticRepresentation.ArchitectureSignatureAggregateWitness` | `inductive` | Signature v1 concrete representation で使う selected required-law theorem package failure の aggregate witness。 | `defined only` |
| `Chapter11AnalyticRepresentation.ArchitectureSignatureAnalyticNonConclusions` | `def` | optional axis `none` が `axisAvailableAndZero` ではないことを non-conclusion boundary として記録する。 | `defined only` |
| `Chapter11AnalyticRepresentation.architectureSignatureAnalyticRepresentation` | `def` | `ArchitectureLawModel.signatureOf` を `ArchitectureSignatureV1` analytic domain へ送る concrete `AnalyticRepresentation`。 | `defined only` |
| `Chapter11AnalyticRepresentation.architectureSignatureAnalyticRepresentation_nonConclusions` | `theorem` | concrete representation が optional `none` を available zero と混同しない non-conclusion を記録する。 | `proved` |
| `Chapter11AnalyticRepresentation.architectureSignatureAnalyticRepresentation_zeroPreserving` | `theorem` | `ArchitectureLawful X` から `RequiredSignatureAxesZero (signatureOf X)` を得る preserving direction。 | `proved` |
| `Chapter11AnalyticRepresentation.architectureSignatureAnalyticRepresentation_zeroReflecting` | `theorem` | coverage / completeness 前提つきで `RequiredSignatureAxesZero (signatureOf X)` から `ArchitectureLawful X` を得る reflecting direction。 | `proved` |
| `Chapter11AnalyticRepresentation.architectureSignatureAnalyticRepresentation_obstructionPreserving` | `theorem` | selected required-law aggregate obstruction failure を Signature v1 analytic obstruction failure へ送る。 | `proved` |
| `Chapter11AnalyticRepresentation.architectureSignatureAnalyticRepresentation_obstructionReflecting` | `theorem` | coverage / completeness 前提つきで Signature v1 analytic obstruction failure を selected required-law aggregate obstruction failure へ戻す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_represent_eq_signatureOfGenerated` | `theorem` | Atom-generated law model の generated analytic representation が `signatureOfGenerated` を analytic value とすること。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_coverageAssumptions` | `theorem` | generated analytic representation の coverage assumption が generated lawfulness equivalence から discharge されること。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_witnessCompleteness` | `theorem` | generated analytic representation の witness universe が selected generated Signature witness だけを持つこと。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_semanticContractCoverage` | `theorem` | generated analytic representation の semantic-contract coverage が generated required Signature axes coverage から discharge されること。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_zeroPreserving` | `theorem` | generated lawfulness から generated analytic zero を得る preserving direction。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_zeroReflecting` | `theorem` | generated representation の coverage fields の下で generated analytic zero から generated lawfulness を戻す reflecting direction。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_obstructionPreserving` | `theorem` | generated structural obstruction を generated analytic obstruction へ送る。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_obstructionReflecting` | `theorem` | generated analytic obstruction を generated structural obstruction へ戻す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_nonConclusions` | `theorem` | generated analytic representation が non-conclusion boundary を記録する。 | `proved` |
| `ObstructionValuation` | `structure` | selected witness に対する `Nat` valuation、zero が witness absence を反映する条件、obstruction が positive valuation を与える条件、coverage assumptions、non-conclusions を束ねる。 | `defined only` |
| `ObstructionValuation.NoSelectedObstruction` | `def` | selected valuation universe に obstruction witness が存在しないこと。 | `defined only` |
| `ObstructionValuation.ZeroReflectingSum` | `def` | aggregate value 0 から selected obstruction witness absence を得る aggregate-level reflection predicate。 | `defined only` |
| `ObstructionValuation.no_obstruction_of_value_zero` | `theorem` | individual witness value が 0 なら、その selected obstruction witness は存在しない。 | `proved` |
| `ObstructionValuation.noSelectedObstruction_of_zeroReflectingSum` | `theorem` | zero-reflecting aggregate value から selected obstruction witness absence を得る。 | `proved` |
| `ObstructionValuation.RecordsNonConclusions` | `def` | valuation package の non-conclusion clause を predicate として取り出す。 | `defined only` |
| `AAT.GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation` | `def` | generated law model の `signatureOfGenerated` に対し、required Signature axes zero なら value 0、そうでなければ selected generated analytic obstruction value 1 と読む valuation。 | `defined only` |
| `Chapter11AnalyticRepresentation.generatedRequiredSignatureObstructionValuation_coverageAssumptions` | `theorem` | generated selected obstruction valuation の coverage assumption が generated required Signature axes coverage から discharge されること。 | `proved` |
| `AAT.GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation_value_zero` | `theorem` | generated law model では generated required Signature axes zero から selected generated analytic obstruction valuation が 0 になる。 | `proved` |
| `AAT.GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation_noSelectedObstruction` | `theorem` | generated law model には selected generated analytic obstruction witness がない。 | `proved` |
| `AAT.GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation_recordsNonConclusions` | `theorem` | generated obstruction valuation が non-conclusion boundary を記録する。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormulaPackage` | `def` | generated law model を before / after state とし、generated analytic representation と generated selected obstruction valuation で Chapter 11 analytic extension formula package を構成する。 | `defined only` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_representationMapAssumptions` | `theorem` | generated identity formula package の representation-map assumption を generated representation coverage と `signatureOfGenerated` equation で discharge する。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_valuationStructureAssumptions` | `theorem` | generated identity formula package の valuation-structure assumption を generated valuation coverage と all-witness zero valuation で discharge する。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_decompositionCertificate` | `theorem` | generated identity formula package の decomposition certificate を before = after で discharge する。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_coverageAssumptions` | `theorem` | generated identity formula package の coverage assumption を generated required Signature axes coverage で discharge する。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_complexityTransferBoundary` | `theorem` | generated identity formula package の complexity-transfer boundary を identity state と unit feature で discharge する。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_formula_holds` | `theorem` | generated identity analytic extension formula package が保持する formula equation を取り出す。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_requiredAssumptions` | `theorem` | generated identity formula package の representation / valuation / decomposition / coverage assumptions を discharge する。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_recordsNonConclusions` | `theorem` | generated identity formula package が non-conclusion boundary を記録する。 | `proved` |
| `Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_obstructionValue_zero` | `theorem` | generated identity formula package が使う generated selected obstruction valuation の value が 0 であることを取り出す。 | `proved` |

## SOLID Counterexamples

File: `Formal/Arch/Examples/SolidCounterexample.lean`

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

## Atom Axiom System / AATCore Refoundation

Files: `Formal/Arch/Atom/Foundation.lean`,
`Formal/Arch/AAT/Molecule.lean`, `Formal/Arch/AAT/Law.lean`,
`Formal/Arch/AAT/Circuit.lean`, `Formal/Arch/AAT/Core.lean`,
`Formal/Arch/AAT/ZeroCurvature.lean`, `Formal/Arch/AAT/Operation.lean`,
`Formal/Arch/AAT/Repair.lean`, `Formal/Arch/AAT/Synthesis.lean`,
`Formal/Arch/Observation/AtomPresentation.lean`,
`Formal/Arch/Observation/ArchMap.lean`,
`Formal/Arch/Signature/AATCoreBridge.lean`,
`Formal/Arch/Evolution/SFTInterfaceBoundary.lean`,
`Formal/Arch/Evolution/SFTEnvelope.lean`,
`Formal/Arch/Evolution/SFTArchSigBoundary.lean`, and current examples under
`Formal/Arch/Examples/AtomFoundationExamples.lean`,
`Formal/Arch/Examples/AATMoleculeLawExamples.lean`,
`Formal/Arch/Examples/AATZeroCurvatureExamples.lean`,
`Formal/Arch/Examples/AATOperationRepairSynthesisExamples.lean`,
`Formal/Arch/Examples/ArchMapObservationExamples.lean`,
`Formal/Arch/Examples/AtomSFTInterfaceExamples.lean`,
`Formal/Arch/Examples/AATCoreSmokeExamples.lean`.

Issue [#1293](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1293)
の refoundation では、Atom を境界や law に依存しない公理 root として置き、
AAT を `AtomAxiomSystem` から直接立ち上げる。旧 compatibility layer は #1307 で
archive せず削除し、Lean index は現行の AATCore surface のみを source of truth とする。

LLM-native tooling epic [#1328](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1328)
以後の ArchMap / ArchSig 読みでは、ArchMap は law-independent な source-grounded
Atom observation map、LawPolicy は selected LawUniverse / witness rule / signature axis
policy artifact、ArchSig は `ArchMap + LawPolicy` から law-relative obstruction /
signature / flatness reading を出す analysis layer である。LawPolicy は Lean の
`AAT.DesignLaw` や `AAT.PureTheory` そのものではなく、ArchSig が AAT 語彙で観測を読むための
tooling policy である。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `Axis`, `AtomKind`, `AtomPredicate`, `AtomAxiomSystem`, `AATFromAtomAxioms` | `inductive` / `structure` / `abbrev` | Atom 公理 root。atom は typed predicate、kind / axis alignment、single fact、boundary / law independence、observation / law / tool output / SFT event が atom を生成しない boundary を持つ。 | `defined only` |
| `AtomAxiomSystem.primitive`, `predicate_kind`, `predicate_axis`, `single_fact`, `predicate_preserving`, `boundary_independent`, `law_independent`, `observation_boundary_does_not_create_atoms`, `law_does_not_create_atoms`, `tool_output_does_not_create_atoms`, `sft_event_does_not_create_atoms`, `AATFromAtomAxioms.begins_from_atom_axioms`, `independent_of_observation_boundary`, `independent_of_law` | `theorem` | root atom が primitive typed fact であり、境界 / law / tooling / SFT event から生成されないことを accessor theorem として取り出す。 | `proved` |
| `AAT.Molecule`, `AAT.MoleculeSubset`, `AAT.ProperSubmolecule`, `AAT.RoleInterpretation`, `AAT.PatternInterpretation` | `structure` / `def` | `AtomAxiomSystem` 上の finite atom configuration と inclusion / proper inclusion、role / pattern を primitive atom ではなく molecule interpretation として読む pure AAT surface。 | `defined only` |
| `AAT.DesignLaw`, `AAT.ObstructionCircuit`, `AAT.FiniteMoleculeUniverse`, `AAT.LawfulWithinMoleculeConfiguration`, `AAT.NoRequiredObstructionCircuit`, `AAT.LawfulnessBridge` | `structure` / `def` | molecule を評価する law、law-relative minimal bad molecule、selected finite molecule universe、lawfulness / no required circuit bridge。 | `defined only` |
| `AAT.PureTheory`, `AAT.AATCore`, `AAT.LawfulWithinAATCore`, `AAT.ZeroCurvature`, `AAT.ZeroCurvaturePackage` | `structure` / `abbrev` / `def` | Atom 公理系から直接立ち上がる pure AAT core と、その core 上の selected law / required molecule / no required obstruction circuit package。 | `defined only` |
| `AAT.OperationPreservationPackage`, `AAT.OperationTransportPackage`, `AAT.RepairClearingPackage`, `AAT.SynthesisSoundnessPackage` | `structure` | operation / repair / synthesis を AATCore と zero-curvature package の後段 theorem package として読む。`OperationTransportPackage` は generated operation が source molecule / law から target molecule / law へ移る場合を扱う。 | `defined only` |
| `ArchitectureSignature.AATCoreSignatureLawfulnessBridge`, `AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel`, `ofGeneratedLawModel_zeroCurvaturePackage_eq_generated`, `ofGeneratedLawModel_architectureLawful` | `structure` / `def` / `theorem` | `AAT.ZeroCurvaturePackage` を消費し、`ArchitectureLawModel` の Signature lawfulness / required axes zero へ渡す後段 analysis bridge。generated law model からは `architectureLawfulFromAAT` field を caller が渡さず、generated zero-curvature package / generated lawfulness で bridge を構成できる。ArchSig / LawPolicy tooling artifact はこの bridge の入力候補を記録できるが、AAT core を定義しない。 | `defined only` / `proved` |
| `Observation.AtomObservationStatus`, `Observation.RawAtomCandidate`, `ObservedAtom`, `AtomObservationGap`, `AtomPresentation`, `ArchMapObservationLayer`, `ArchMapObservedAtomSelection`, `ArchMapGeneratedArchitectureObjectInput` | `inductive` / `structure` | raw candidate、observed / validated / rejected / uncertain / missing、presentation、ArchMap observation layer を pure AAT core の外で分離し、observed atom selection から generated molecule / object へ渡す handoff input も表す observation namespace。 | `defined only` |
| `Observation.RawAtomCandidate.does_not_create_atoms`, `ObservedAtom.observation_does_not_create_atoms`, `ObservedAtom.atom_primitive`, `AtomObservationGap.gap_does_not_imply_atom_absence`, `AtomPresentation.raw_candidate_is_not_atom_truth`, `rejected_is_not_measured_zero`, `uncertain_is_not_measured_zero`, `missing_is_not_measured_zero`, `missing_is_not_atom_absence`, `ArchMapObservationLayer.observes_atoms`, `archmap_does_not_create_atoms`, `archmap_does_not_define_aat`, `ArchMapObservedAtomSelection.selected_atoms_observed`, `selected_atoms_primitive`, `toGeneratedMolecule_atom_observed`, `toGeneratedMolecule_observation_does_not_create_atoms`, `ArchMapGeneratedArchitectureObjectInput.toGeneratedArchitectureObject_carrier_observed` | `theorem` | raw candidate は atom truth ではなく、observation は atom を生成せず、missing observation は measured zero / atom absence ではない。観測済み atom は primitive atom として generated molecule/object handoff に渡せるが、ArchMap は Atom existence / AAT を定義しない。 | `proved` |
| `AATCoreLocalAlgebraForSFT`, `AATCoreAtomDelta`, `AATCoreSemanticDelta`, `AATCoreCircuitDelta`, `AATCoreTransportCircuitDelta`, `AATCoreTransition`, `AATCoreTransportTransition`, `AATCorePremisedConsequenceEnvelope`, `GeneratedAATConsequenceEnvelope`, `ArchSigAATCoreTransition`, `FieldSigAATCoreTransitionAnalysis`, `GeneratedArchSigAATCoreTransition`, `GeneratedFieldSigAATCoreTransitionAnalysis`, `GeneratedArchSigAATCoreTransportTransition`, `GeneratedFieldSigAATCoreTransportTransitionAnalysis` | `structure` | SFT / FieldSig が `AATCore` preservation / transport transition または ArchSig analysis state を input として読む bridge。transport circuit delta は source / target law・molecule を別々に保持し、generated transition は generated law model から source / target Signature bridge を構成する。`GeneratedAATConsequenceEnvelope` は `GeneratedSFTInput` と generated ArchSig transition から consequence envelope premise を構成する。SFT / FieldSig は Atom / AAT を再定義せず、ArchSig handoff から forecast correctness を結論しない。 | `defined only` |
| `AtomFoundationExamples.*`, `AtomShapeKindCoverageExamples.*`, `AATMoleculeLawExamples.*`, `AATZeroCurvatureExamples.*`, `AATOperationRepairSynthesisExamples.*`, `ArchMapObservationExamples.*`, `AtomSFTInterfaceExamples.*`, `AATCoreSmokeExamples.*` | `theorem` | Atom 公理 root、全 `AtomKind` constructor の AtomShape coverage、molecule / law / circuit、zero curvature、operation / repair / synthesis、observation separation、SFT / FieldSig transition bridge、非identity generated transport handoff を検査する current smoke tests。 | `proved` |

Non-conclusions: `AtomAxiomSystem` は taxonomy completeness、tool validation correctness、forecast correctness、global future safety を結論しない。ArchMap / ArchSig / FieldSig は Atom を観測・分析・受け渡しする後段 layer であり、Atom や AAT を生成しない。

### Atom-Generated Algebra Kernel

Files: `Formal/Arch/Atom/Valence.lean`,
`Formal/Arch/Atom/Shape.lean`,
`Formal/Arch/Atom/Composition.lean`,
`Formal/Arch/AAT/AtomComposition.lean`,
`Formal/Arch/AAT/GeneratedMolecule.lean`,
`Formal/Arch/AAT/GeneratedObject.lean`,
`Formal/Arch/AAT/GeneratedGraph.lean`,
`Formal/Arch/AAT/GeneratedLawModel.lean`,
`Formal/Arch/AAT/GeneratedSignature.lean`,
`Formal/Arch/AAT/GeneratedFlatness.lean`,
`Formal/Arch/AAT/GeneratedFeatureExtension.lean`,
`Formal/Arch/AAT/GeneratedCurvature.lean`,
`Formal/Arch/AAT/GeneratedPath.lean`,
`Formal/Arch/AAT/GeneratedDiagram.lean`,
`Formal/Arch/AAT/GeneratedAnalyticRepresentation.lean`,
`Formal/Arch/AAT/GeneratedOperation.lean`,
`Formal/Arch/AAT/GeneratedRepair.lean`,
`Formal/Arch/AAT/GeneratedSynthesis.lean`,
`Formal/Arch/AAT/GeneratedSFT.lean`,
`Formal/Arch/AAT/TheoremClassification.lean`,
`Formal/Arch/AAT/CompleteFormalization.lean`, and acceptance examples
`Formal/Arch/Examples/AtomShapeKindCoverageExamples.lean`,
`Formal/Arch/Examples/AtomGeneratedSignatureExamples.lean`,
`Formal/Arch/Examples/AtomGeneratedRepairExamples.lean`,
`Formal/Arch/Examples/AtomGeneratedClassificationExamples.lean`,
`Formal/Arch/Examples/AATCompleteFormalizationExamples.lean`,
`Formal/Arch/Examples/IncompatibleAtomCompositionExamples.lean`.

この節は [AAT Atom-Based Reconstruction Plan](atom_based_aat_reconstruction_plan.md)
の acceptance kernel を索引する。Atom は無構造な点ではなく `AtomShape` /
`AtomValence` を持つ primitive typed fact として読み、compatible composition から
generated molecule、generated object、generated graph / law model、generated signature、
SFT handoff へ接続する。これは計画全体の完了宣言ではなく、既存 theorem package 全体の
Atom-generated 移行を監査するための initial generated kernel である。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `AtomPortKind`, `AtomPort`, `AtomValence`, `AtomSubject`, `AtomObjectSlot`, `AtomPayloadSlot`, `AtomDirection`, `AtomShape`, `AtomShapePresentation`, `AtomShapeOf` | `inductive` / `structure` / `def` | Atom の port / valence、subject、object / payload slot、direction、arity、shape presentation を持つ形状層。 | `defined only` |
| `required_port_has_port`, `PortCompatible.symm`, `shape_kind_aligned`, `shape_axis_aligned`, `shape_single_fact` | `theorem` | required port が valence 内に存在すること、port compatibility の対称性、shape が atom kind / axis / single fact と整合することを取り出す。 | `proved` |
| `AtomShapeKindCoverageExamples.coverage_shape_exists_for_every_atom_kind`, `coverage_shape_kind_matches_predicate`, `coverage_shape_axis_matches_predicate`, `coverage_shape_has_valence_port`, `coverage_shape_single_fact` | `theorem` | current AtomKind grammar の existence / relation / capability / data state / effect / authority / contract / semantic / runtime 各 constructor が、typed predicate から intrinsic `AtomShape` family と valence port を持つ shaped atom として現れることを固定する。 | `proved` |
| `SlotCompatible`, `PayloadSlotCompatible`, `PredicateSlotCompatible`, `CompatibleComposition`, `CompositionGraph` | `def` / `structure` | AtomShape 間の slot / payload / predicate / port compatibility と composition graph。 | `defined only` |
| `CompatibleComposition.has_port_pair`, `no_compatible_port_not_compatible`, `incompatible_slots_not_compatible` | `theorem` | compatible composition は port pair を持ち、port 不一致や slot 不一致から compatible composition が出ないことを示す。 | `proved` |
| `RequiredPortsMatched`, `GeneratedMolecule`, `GeneratedMolecule.toMolecule`, `GeneratedMolecule.compatible_pairs`, `GeneratedMolecule.notArbitrarySet` | `def` / `structure` | Molecule を任意 atom 集合ではなく、required ports と compatible pairs を満たす generated finite configuration として読む。`notArbitrarySet` は field ではなく composition graph / required-port evidence から計算される predicate。 | `defined only` |
| `GeneratedMolecule.atoms_primitive`, `GeneratedMolecule.not_arbitrary_set`, `GeneratedMolecule.incompatible_slots_not_generatedMolecule`, `GeneratedMolecule.missing_required_port_not_generatedMolecule` | `theorem` | generated molecule が primitive atom に支えられ、任意集合ではなく、slot / required port 不整合からは生成されないことを、caller-supplied marker ではなく構造由来で固定する。 | `proved` |
| `GeneratedArchitectureObject`, `GeneratedCarrier`, `GeneratedObservationCoordinate`, `GeneratedAuthority`, `GeneratedEffect`, `GeneratedCapability`, `GeneratedDataState`, `GeneratedContract`, `GeneratedSemanticInterpretation`, `GeneratedSemanticContractCoverage`, `GeneratedCapabilityDataStateSupport`, `GeneratedAuthorityPolicy`, `GeneratedEffectLawInput`, `GeneratedAuthorityEffectLawSatisfied` | `structure` / `abbrev` / `def` | generated molecule から architecture carrier、observation coordinate、authority / effect / capability / data-state / contract / semantic interpretation、semantic-contract coverage、capability/data-state support、authority-effect law input を読む object 層。 | `defined only` |
| `GeneratedArchitectureObject.carrier_atom_primitive`, `generated_observation_from_semantic_atoms`, `generated_authority_policy_from_authority_atoms`, `generated_effect_law_input_from_effect_atoms`, `generated_capability_from_capability_atoms`, `generated_data_state_from_data_state_atoms`, `generated_capability_data_state_support_from_data_state_atoms`, `generated_contract_from_contract_atoms`, `generated_semantic_interpretation_from_semantic_atoms`, `generated_semantic_contract_coverage_from_contract_atoms`, `generated_authority_effect_law_satisfied_from_authority_policy`, `no_authority_policy_not_generated_authority_effect_law_satisfied` | `theorem` | generated object の carrier atom が primitive であり、semantic / authority / effect / capability / data-state / contract atom から対応 surface が出ること、capability atom と generated data-state が同じ generated object 内にあると capability/data-state support が構成されること、semantic atom と generated contract が同じ generated object 内にあると semantic-contract coverage が構成されること、effect atom と generated authority policy が同じ generated object 内にあると authority-effect law satisfied が構成されること、authority がない effect-only input から law satisfied は出ないことを示す。 | `proved` |
| `GeneratedRelationAtom`, `GeneratedRelation`, `GeneratedArchGraph`, `GeneratedRuntimeRelationAtom`, `GeneratedRuntimeRelation`, `GeneratedRuntimeGraph`, `GeneratedRelationEdgeWitness`, `GeneratedRuntimeEdgeWitness` | `def` / `structure` | relation / runtime interaction atom から generated static / runtime graph edge を作る graph 層。relation atom は distinct endpoints を要求し、static relation edge は source 側を `relationSource` port、target 側を `relationTarget` port で接続する。runtime interaction edge も source 側を `runtimeSource` port、target 側を `runtimeTarget` port で接続する。 | `defined only` |
| `generated_graph_edges_from_relation_atoms`, `generated_graph_edge_requires_distinct_endpoints`, `generated_runtime_edges_from_interaction_atoms`, `generated_runtime_edge_requires_distinct_endpoints`, `directedRelationGeneratedGraph_api_to_database_edge`, `directedRelationGeneratedGraph_edge_uses_source_target_ports`, `directedRelationGeneratedGraph_no_database_to_api_edge`, `directedRelationGeneratedGraph_edge_only_api_to_database`, `directedRelationGraphRank_walkAcyclic`, `directedRuntimeGeneratedGraph_api_to_database_edge`, `directedRuntimeGeneratedGraph_edge_uses_source_target_ports`, `directedRuntimeGeneratedGraph_no_database_to_api_edge`, `directedRuntimeGeneratedGraph_edge_only_api_to_database`, `directedRuntimeGraphRank_walkAcyclic` | `theorem` | generated relation / runtime atom から graph edge witness を得る方向と、generated edge が distinct endpoints を要求することを固定する。directed relation acceptance は API -> database relation atom が `relationSource` / `relationTarget` ports で向き付き edge を生成し、逆向き edge を生成せず、generated edge が API -> database に限られるため generated graph rank から acyclicity を得ることを固定する。directed runtime acceptance は API -> database runtime interaction atom が `runtimeSource` / `runtimeTarget` ports で向き付き runtime edge を生成し、逆向き runtime edge を生成せず、runtime edge が API -> database に限られるため generated runtime graph rank から runtime acyclicity を得ることを固定する。 | `proved` |
| `GeneratedGraphRank`, `GeneratedGraphRank.strictLayering`, `GeneratedGraphRank.walkAcyclic`, `GeneratedRuntimeGraphRank`, `GeneratedRuntimeGraphRank.strictLayering`, `GeneratedRuntimeGraphRank.walkAcyclic`, `GeneratedArchitectureLawModel`, `GeneratedArchitectureLawModel.graphRank`, `GeneratedArchitectureLawModel.ofGraphRank`, `GeneratedArchitectureLawModel.generatedWalkAcyclic`, `GeneratedArchitectureLawModel.toArchitectureLawModel`, `GeneratedArchitectureLawModel.generatedSignatureOf`, `signatureOfGenerated`, `GeneratedArchitectureLawModel.generatedDesignLaw`, `GeneratedArchitectureLawModel.generatedAATCoreNoObservationDependency`, `GeneratedArchitectureLawModel.generatedAATCoreCircuitBoundary`, `GeneratedArchitectureLawModel.generatedAATCore`, `GeneratedArchitectureLawModel.generatedZeroCurvaturePackage` | `structure` / `def` | generated object / graph / observation から `ArchitectureLawModel` と signature reading を構成し、その generated lawfulness から pure AAT `DesignLaw` / `AATCore` / `ZeroCurvaturePackage` を構成する law / signature 層。`GeneratedGraphRank` は generated carrier rank が every generated relation edge で減少することを証明し、`GeneratedArchitectureLawModel` は raw `WalkAcyclic` field ではなくこの generated graph-rank certificate を state として持つ。generated AAT core の observation boundary は root `AtomAxiomSystem.noObservationBoundaryCreatesAtoms`、circuit boundary は generated lawfulness による obstruction-circuit exclusion として持つ。`GeneratedRuntimeGraphRank` は generated runtime-interaction edge に同じ rank certificate を与え、runtime surface の acyclicity も generated structure として扱う。 | `defined only` |
| `GeneratedArchitectureLawModel.generatedWalkAcyclic_eq_graphRank_walkAcyclic`, `GeneratedArchitectureLawModel.generated_projection_sound`, `generated_lsp_compatible`, `generated_boundary_policy_sound`, `generated_abstraction_policy_sound`, `generatedArchitectureLawful`, `generated_law_model_from_generated_object`, `generated_law_model_from_generated_graph_rank`, `directedRelation_law_model_from_graph_rank`, `generated_requiredSignatureAxesZero`, `generatedArchitectureLawful_iff_requiredSignatureAxesZero`, `generatedArchitectureLawful_of_requiredSignatureAxesZero`, `generatedArchitectureZeroCurvatureTheoremPackage`, `generatedArchitectureZeroCurvatureTheoremPackage_holds`, `generatedArchitectureLawful_iff_generatedArchitectureZeroCurvatureTheoremPackage`, `AtomGeneratedSignatureExamples.atomGeneratedSignature_zeroCurvatureTheoremPackage`, `AtomGeneratedSignatureExamples.atomGeneratedSignature_lawful_iff_zeroCurvatureTheoremPackage` | `def` / `theorem` | generated law model から selected lawfulness、required signature axes zero、static structural core theorem package を得る。`generated_law_model_from_generated_object` と `generated_law_model_from_generated_graph_rank` は generated object と generated graph rank certificate から law model / lawfulness を構成し、directed relation acceptance では実際の API -> database generated edge に対して rank が下がることから law model を作る。`generatedWalkAcyclic` は `GeneratedArchitectureLawModel.graphRank` から導出され、raw `WalkAcyclic` premise を law-model state として保持しない。generated static structural core package は projected law model の decidable relation instances を generated relation predicate から回収し、hand-authored graph / law model や `architectureLawfulFromAAT` field を入力にしない。 | `defined only` / `proved` |
| `AATTheoremFamily`, `AATFieldImplementationStatus`, `AATImplementationFrontier`, `AtomGeneratedAATWorld`, `ArchMapGeneratedObjectHandoff`, `GeneratedMoleculeObjectFields`, `GeneratedGraphRankFields`, `GeneratedFlatnessCurvatureFields`, `GeneratedPathDiagramFields`, `GeneratedFeatureExtensionFields`, `GeneratedOperationRepairSynthesisFields`, `GeneratedDistanceMeasureGeometryFields`, `GeneratedAnalyticRepresentationFields`, `GeneratedSFTArchSigFieldSigFields`, `AATTheoremSuite`, `AATCompleteFormalization`, `allAATTheoremFamilies`, `currentImplementationFrontier`, `initialTheoremSuite`, `initialCompleteFormalization` | `inductive` / `structure` / `def` | AAT 完全形式化を並列で進めるための coordination skeleton。`AtomGeneratedAATWorld` は Atom root、shape presentation、generated object、generated law model、generated runtime graph rank、generated Signature 用 decidability evidence を共有 world として束ねる。`AATTheoremSuite` は source-of-truth field として generated molecule non-arbitrariness、generated object carrier / ArchMap handoff、generated relation/runtime graph-rank certificate、generated lawfulness、generated required Signature axes zero、generated static structural core、generated AATCore no-observation / circuit-boundary bridge fields、generated flatness / curvature、generated path / diagram / selected non-fillability package fields、generated feature extension / lifting / obstruction / extension formula fields、generated operation / repair / synthesis package fields、Part IV distance / measure geometry field、generated analytic representation、generated SFT / ArchSig / FieldSig handoff fields / selected obstruction valuation / identity analytic extension formula package、classification registry の source/downstream 分離を持つ。`AATImplementationFrontier` は suite field、既存 entrypoint、次 work package、parallel / coordination flag、docs target を concrete row として列挙し、generated molecule object row、generated graph rank row、generated law / Signature row、generated flatness / curvature row、generated path / diagram row、generated feature extension row、generated operation / repair / synthesis row、generated distance / measure geometry row、generated analytic representation row、generated SFT / ArchSig / FieldSig row は connected として扱う。 | `defined only` |
| `AtomGeneratedAATWorld.molecule_not_arbitrary_set`, `generated_object_carriers_atom_primitive`, `archMap_generated_object_handoff`, `generated_molecule_object_fields`, `generated_lawful`, `required_signature_axes_zero`, `static_structural_core`, `generated_graph_rank_walkAcyclic`, `generated_runtime_graph_rank_walkAcyclic`, `generated_architecture_flat`, `generated_shapeCoordinateTotalCurvature_eq_zero`, `generated_flatness_curvature_fields`, `generated_path_preservesInvariant`, `generated_nonFillabilityWitness`, `generated_path_diagram_fields`, `generated_analyticRepresentation`, `generated_requiredSignatureObstructionValuation`, `generated_identityAnalyticExtensionFormulaPackage`, `generated_distance_measure_geometry_fields`, `generated_aat_core_noObservationDependency`, `generated_aat_core_circuitBoundary`, `currentImplementationFrontier_covers_all_families`, `connected_frontier_rows_have_existing_entrypoints`, `parallel_frontier_rows_are_not_core_coordination`, `initialCompleteFormalization_frontier_covers_all_families`, `AATCompleteFormalizationExamples.generatedComponentTheoremSuite_has_required_axes_zero`, `generatedComponentTheoremSuite_has_static_structural_core`, `generatedComponentTheoremSuite_has_generated_object_fields`, `generatedComponentTheoremSuite_has_graph_rank_fields`, `generatedComponentTheoremSuite_has_flatness_curvature_fields`, `generatedComponentTheoremSuite_has_path_diagram_fields`, `generatedComponentTheoremSuite_has_distance_measure_geometry_fields`, `generatedComponentTheoremSuite_has_analytic_representation_fields`, `generatedComponentTheoremSuite_has_generated_aat_core_bridge_fields`, `generatedComponentTheoremSuite_registry_has_no_bridge_assumed_rows`, `generatedComponentTheoremSuite_registry_has_no_rewrite_targets`, `generatedComponentTheoremSuite_registry_source_rows_are_atom_generated`, `generatedComponentTheoremSuite_registry_representation_rows_are_downstream`, `generatedComponentCompleteFormalization_frontier_covers_all_families`, `generatedComponentCompleteFormalization_parallel_rows_are_safe`, `generated_featureExtension_architectureFlatWithin`, `generated_featureExtension_recordsNonConclusions`, `generated_selfSplitExtensionLifting_preservationPackage`, `generated_selfLiftingFailureExtensionObstructionWitnessExists`, `generated_identityArchitectureExtensionFormula_structural`, `generated_feature_extension_fields`, `generatedComponentTheoremSuite_has_feature_extension_fields`, `generated_operation_does_not_create_atoms`, `generated_repair_toRepairClearingPackage`, `generated_synthesis_toSynthesisSoundnessPackage`, `generated_operation_repair_synthesis_fields`, `generatedComponentTheoremSuite_has_operation_repair_synthesis_fields`, `generated_sft_input_toAATCoreLocalAlgebraForSFT`, `generated_archsig_transition_sourceBridge`, `generated_fieldsig_reads_archsig_transition_as_sft_analysis`, `generated_fieldsig_forecast_correctness_remains_boundary`, `generated_sft_archsig_fieldsig_fields`, `generatedComponentTheoremSuite_has_sft_archsig_fieldsig_fields` | `theorem` / `def` | 既存 generated component model で complete-formalization skeleton が inhabited になり、generated object carrier が primitive atom であること、ArchMap observed-atom input が `GeneratedArchitectureObject` へ handoff できること、generated relation/runtime graph-rank certificate とその acyclicity、generated law / Signature static core から generated AATCore no-observation / circuit-boundary bridge fields、generated architecture flatness / shape-coordinate curvature zero、generated path / diagram / selected non-fillability package fields、generated feature extension / lifting / obstruction / extension formula fields、generated operation non-creation / repair clearing / synthesis soundness fields、Part IV distance / measure geometry field、generated analytic representation、generated SFT local-algebra / ArchSig transition / FieldSig analysis-boundary fields / selected obstruction valuation / identity analytic extension formula package まで suite field として読めること、current frontier が全 theorem family を覆うこと、generated operation / repair / synthesis suite field、generated distance / measure geometry suite field、generated SFT / ArchSig / FieldSig suite field、connected row は existing entrypoint を持つこと、parallel row が core coordination row ではないことを固定する。これは AAT 完全形式化の完了宣言ではなく、suite field 単位でサブエージェントを投入するための共有 contract である。 | `proved` |
| `AATImplementationFrontier.IsConnected`, `AATCompleteFormalization.IsComplete`, `currentImplementationFrontier_has_no_parallelReady_rows`, `currentImplementationFrontier_all_rows_connected`, `initialCompleteFormalization_is_complete`, `AATCompleteFormalizationExamples.generatedComponentCompleteFormalization_is_complete` | `def` / `theorem` | `AATCompleteFormalization` の final closure boundary。`currentImplementationFrontier` を削除せず completion ledger として残し、全 row が `connected` であり `parallelReady` row が残っていないことを Lean 上で固定する。これは suite field と theorem-package audit がすべて接続済みであることの完了判定であり、ambient semantic coverage、FieldSig forecast calibration、未知の ambient semantic universe までの完全性は結論しない。 | `proved completion boundary` |
| `GeneratedFlatnessCurvatureFields`, `AATTheoremSuite.generatedFlatnessCurvature` | `structure` / suite field | generated flatness / curvature を generated world と generated measurement universe に相対化した suite field。`ArchitectureFlatWithin`、既存の generated `ArchitectureFlat` certificate、shape-coordinate total curvature zero を束ねるが、ambient semantic coverage、unmeasured axis safety は結論しない。`currentImplementationFrontier` の `generatedFlatnessCurvature` row は connected。 | `defined only` |
| `AtomGeneratedAATWorld.generated_architecture_flat`, `generated_shapeCoordinateTotalCurvature_eq_zero`, `generated_flatness_curvature_fields`, `AATCompleteFormalizationExamples.generatedComponentTheoremSuite_has_flatness_curvature_fields` | `theorem` / `def` | 既存 `GeneratedArchitectureLawModel.generatedArchitectureFlatWithin` / `generatedArchitectureFlat` と `GeneratedArchitectureObject.generated_shapeCoordinateTotalCurvature_eq_zero` から suite field を埋め、example theorem が `AATTheoremSuite.generatedFlatnessCurvature` から generated architecture flatness と shape-coordinate curvature zero を読むことを固定する。 | `proved` |
| `GeneratedPathDiagramFields`, `AATTheoremSuite.generatedPathDiagram` | `structure` / suite field | generated path invariant preservation、reflexive generated diagram filler、selected observation difference からの non-fillability witness construction を generated world に相対化した suite field。arbitrary diagram filling、global non-fillability、ambient semantic coverage は結論しない。`currentImplementationFrontier` の `generatedPathDiagram` row は connected。 | `defined only` |
| `AtomGeneratedAATWorld.generated_path_preservesInvariant`, `generated_nonFillabilityWitness`, `generated_path_diagram_fields`, `AATCompleteFormalizationExamples.generatedComponentTheoremSuite_has_path_diagram_fields` | `theorem` / `def` | 既存 `Chapter8HomotopySkeleton.generatedPath_preservesInvariant`、`generatedDiagramFiller_refl`、`Chapter8HomotopySkeleton.generatedObservationDifference_nonFillabilityWitnessFor` から suite field を埋め、example theorem が `AATTheoremSuite.generatedPathDiagram` から generated reflexive diagram filler を読むことを固定する。non-fillability は selected observation difference evidence に相対化される。 | `proved` |
| `GeneratedFeatureExtensionFields`, `AATTheoremSuite.generatedFeatureExtension` | `structure` / suite field | generated identity feature extension、selected lifting、lifting-failure obstruction bridge、identity extension formula structural field を generated world に相対化して束ねる suite field。lifting は selected feature step と interface compatibility に相対化し、lifting-failure obstruction は no-preservation-package premise に相対化する。external semantic obstruction を generated flatness だけで discharge する主張は含めない。`currentImplementationFrontier` の `generatedFeatureExtension` row は connected。 | `defined only` |
| `AtomGeneratedAATWorld.generated_featureExtension_architectureFlatWithin`, `generated_featureExtension_recordsNonConclusions`, `generated_selfSplitExtensionLifting_preservationPackage`, `generated_selfLiftingFailureExtensionObstructionWitnessExists`, `generated_identityArchitectureExtensionFormula_structural`, `generated_feature_extension_fields`, `AATCompleteFormalizationExamples.generatedComponentTheoremSuite_has_feature_extension_fields` | `theorem` / `def` | 既存 generated feature-extension / Chapter 9 / Chapter 10 entrypoints から suite field を埋め、example theorem が `AATTheoremSuite.generatedFeatureExtension` から generated feature-extension package を読むことを固定する。 | `proved` |
| `GeneratedOperationRepairSynthesisFields`, `AATTheoremSuite.generatedOperationRepairSynthesis` | `structure` / suite field | generated operation / repair / synthesis を `AATTheoremSuite` の suite field として接続する。operation は root `AtomAxiomSystem` 由来の atom non-creation を読み、repair は pre-molecule problem から generated target object の `RepairClearingPackage` へ接続し、synthesis は candidate law model 由来の `SynthesisSoundnessPackage` へ接続する。repair target を free-form recommendation として扱わず、synthesis candidate が Atom を新規生成することも許さない。 | `defined only` |
| `AtomGeneratedAATWorld.generated_operation_does_not_create_atoms`, `generated_repair_toRepairClearingPackage`, `generated_synthesis_toSynthesisSoundnessPackage`, `generated_operation_repair_synthesis_fields`, `AATCompleteFormalizationExamples.generatedComponentTheoremSuite_has_operation_repair_synthesis_fields` | `theorem` / `def` | `GeneratedOperation.operation_does_not_create_atoms`、`GeneratedRepairFromProblem.toRepairClearingPackage`、`GeneratedSynthesisCandidate.toSynthesisSoundnessPackage` から `initialTheoremSuite` の generated operation / repair / synthesis field を埋め、example theorem が suite field から non-creation evidence、repair-clearing package、synthesis-soundness package を読むことを固定する。 | `proved` |
| `GeneratedSFTArchSigFieldSigFields`, `AATTheoremSuite.generatedSFTArchSigFieldSig` | `structure` / suite field | generated SFT / ArchSig / FieldSig handoff を generated world に相対化した suite field。`GeneratedSFTInput.toAATCoreLocalAlgebraForSFT`、`GeneratedArchSigAATCoreTransition.sourceBridge`、`GeneratedFieldSigAATCoreTransitionAnalysis.fieldsig_reads_generated_archsig_transition_as_sft_analysis` を束ねるが、FieldSig forecast calibration、empirical calibration、future safety は結論しない。`currentImplementationFrontier` の `generatedSFTArchSigFieldSig` row は connected。 | `defined only` |
| `AtomGeneratedAATWorld.generated_sft_input_toAATCoreLocalAlgebraForSFT`, `generated_archsig_transition_sourceBridge`, `generated_fieldsig_reads_archsig_transition_as_sft_analysis`, `generated_fieldsig_forecast_correctness_remains_boundary`, `generated_sft_archsig_fieldsig_fields`, `AATCompleteFormalizationExamples.generatedComponentTheoremSuite_has_sft_archsig_fieldsig_fields` | `theorem` / `def` | 既存 generated SFT / ArchSig / FieldSig handoff theorem から suite field を埋め、example theorem が `AATTheoremSuite.generatedSFTArchSigFieldSig` から SFT local algebra premise、generated ArchSig source bridge、FieldSig analysis boundary、forecast boundary を読むことを固定する。 | `proved` |
| `GeneratedArchitectureLawModel.generatedAATCoreNoObservationDependency_recorded`, `GeneratedArchitectureLawModel.generatedAATCoreCircuit_impossible`, `GeneratedArchitectureLawModel.generatedAATCoreCircuitBoundary_recorded`, `GeneratedArchitectureLawModel.generated_noRequiredObstructionCircuit`, `generatedLawfulnessBridge`, `generated_lawfulWithinMoleculeConfiguration`, `ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel`, `AtomGeneratedMoleculeExamples.generatedComponentAATCore_noObservationDependency`, `AtomGeneratedMoleculeExamples.generatedComponentAATCore_circuitBoundary`, `AtomGeneratedMoleculeExamples.generatedComponentAATCore_obstructionCircuit_impossible`, `AtomGeneratedSignatureExamples.atomGeneratedSignature_coreSignatureBridge`, `atomGeneratedSignature_coreSignatureBridge_architectureLawful` | `theorem` / `def` | generated law model から pure AAT lawfulness / no required obstruction circuit bridge を構成し、既存 `ZeroCurvaturePackage` と AATCore-to-Signature bridge へ接続する。generated AAT core は obstruction circuits を `True` surface として選択せず、generated lawfulness によって selected pure AAT obstruction circuit が不可能であることを core circuit evidence として使う。AATCore-to-Signature bridge は generated constructor 経由なら `architectureLawfulFromAAT` field を caller が手入力しない。 | `proved` |
| `GeneratedAtomShapeCoordinate`, `GeneratedAtomShapeCoordinate.ofShape`, `mismatchBit_eq_zero_iff`, `mismatchCount`, `mismatchCount_eq_zero_iff`, `componentLabels`, `GeneratedArchitectureObject.generatedAtomShapeCoordinate`, `GeneratedArchitectureObject.generatedCarrierShapeDistance`, `GeneratedArchitectureObject.generatedCarrierShapeDistance_self`, `generatedComponentObject_api_database_shapeDistance_eq_one` | `structure` / `def` / `theorem` | AtomShape の family / axis / subject / predicate / direction / arity から generated carrier distance を計算する。API と database の generated carrier は subject だけが違うため mismatch-count distance が 1 になる acceptance を持つ。source refs / confidence / observation boundary は距離 coordinate に入らない。 | `defined only` / `proved` |
| `generatedSemanticDiagram`, `generatedFlatnessModel`, `generatedArchitectureFlatWithin`, `generatedExhaustiveFlatnessCoverage`, `generatedExactFlatnessObservation`, `generatedArchitectureFlatCompletionBoundary`, `generatedArchitectureFlatCompletionBoundary_recorded`, `generatedArchitectureFlat`, `generatedObservationDistance`, `generatedAtomShapeCoordinateDistance`, `generatedAtomShapeCoordinateSemantics`, `generated_totalCurvature_eq_zero`, `generated_noMeasuredNumericalCurvatureObstruction`, `generated_shapeCoordinateTotalCurvature_eq_zero`, `generated_noMeasuredShapeCoordinateCurvatureObstruction`, `generatedComponent_exhaustiveFlatnessCoverage`, `generatedComponent_exactFlatnessObservation`, `generatedComponent_architectureFlatCompletionBoundary`, `generatedComponent_shapeCoordinateTotalCurvature_eq_zero`, `generatedComponent_noMeasuredShapeCoordinateCurvatureObstruction` | `def` / `theorem` | generated semantic diagram / flatness model / curvature input を既存 bounded flatness / curvature API に接続する。global flatness completion は anonymous `True` marker ではなく、generated lawfulness、generated bounded flatness、generated exhaustive coverage、generated exact-observation bridge を記録する certificate boundary から読む。shape-coordinate curvature は full AtomShape mismatch-count distance を zero-separating metric として使い、generated reflexive semantic diagrams が shape-coordinate curvature obstruction を持たないことを固定する。 | `defined only` / `proved` |
| `generatedIdentityFeatureExtension`, `generatedIdentityStaticSplitFeatureExtension`, `generated_selectedStaticSplitFeatureExtension`, `generatedIdentityExtensionComponentUniverse`, `generatedIdentityExtensionCoverageComplete`, `generatedIdentityExtensionFlatnessModel`, `generatedIdentityRuntimeSemanticSplitPreservation`, `generatedSplitFeatureExtensionWithin`, `generatedFeatureExtension_architectureFlatWithin`, `generatedSplitFeatureExtension_recordsNonConclusions`, `Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_structural`, `generatedIdentityArchitectureExtensionFormula_multilabel_structural` | `def` / `theorem` | generated object から identity `FeatureExtension` / `StaticSplitFeatureExtension` を構成し、既存 `SplitFeatureExtensionWithin` / `architectureFlatWithin_of_splitFeatureExtensionWithin` theorem と Chapter 10 structural extension formula を generated input に接続する。 | `defined only` / `proved` |
| `GeneratedArchitectureStep`, `GeneratedArchitecturePath`, `GeneratedArchitecturePath.preservesInvariant`, `GeneratedPathHomotopy`, `Chapter8HomotopySkeleton.generatedPath_preservesInvariant`, `Chapter8HomotopySkeleton.generatedPathHomotopy_observation_eq_append`, `Chapter8HomotopySkeleton.generatedPathHomotopy_observation_eq`, `Chapter8HomotopySkeleton.generatedSignatureTrajectory_refutesGeneratedPathHomotopy` | `structure` / `abbrev` / `theorem` | generated relation-backed step / finite path / homotopy を既存 finite path calculus に制限して読み、Chapter 8 path / observation theorem package へ接続する。 | `defined only` / `proved` |
| `GeneratedArchitectureDiagram`, `GeneratedDiagramFamily`, `GeneratedDiagramFiller`, `GeneratedNonFillabilityWitness`, `GeneratedNonFillabilityWitnessFor`, `generatedDiagramFiller_refl`, `generated_obstructionAsNonFillability_sound`, `generatedDiagramFiller_observation_eq`, `generatedObservationDifference_refutesDiagramFiller`, `generatedObservationDifference_nonFillabilityWitnessFor`, `Chapter8HomotopySkeleton.generatedDiagramFiller_observation_eq`, `Chapter8HomotopySkeleton.generatedObservationDifference_refutesDiagramFiller`, `Chapter8HomotopySkeleton.generated_obstructionAsNonFillability_sound`, `Chapter8HomotopySkeleton.generatedObservationDifference_nonFillabilityWitnessFor`, `Chapter9DiagramFilling.generatedSelfFeatureExtension`, `generatedSelfFeatureExtension_preservesRequiredInvariants`, `generatedSelfFeatureExtension_interactionFactorsThroughDeclaredInterfaces`, `generatedSelfFeatureExtension_coverageAssumptions`, `generatedSelfFeatureExtension_proofObligations`, `generatedSelfSplitExtensionLiftingData`, `generatedSelfSplitExtensionLifting_preservationPackage`, `generatedSelfLiftingFailureExtensionObstructionWitness_classified`, `generatedSelfLiftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage`, `generatedFillingFailureWitnessPayload`, `generatedFillingFailureExtensionObstructionWitness`, `generatedFillingFailureExtensionObstructionWitness_classified`, `generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage`, `generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists`, `generatedFillingFailureBridge_not_selectedSplitExtension_of_generatedWitness`, `Chapter10ArchitectureExtensionFormula.generatedFillingFailureExtensionObstructionWitness_multilabel_classified`, `generatedSelfLiftingFailureExtensionObstructionWitness_multilabel_classified` | `abbrev` / `structure` / `def` / `theorem` | generated step/path に制限された diagram family、filler、non-fillability witness surface。Chapter 8 / 9 entrypoint から selected generated observation difference、generated diagram filler refutation、generated non-fillability witness package を構成し、generated self-view feature extension の field を generated carrier primitive / generated relation edge witness / generated carrier coverage から discharge して lifting / lifting-failure bridge に接続し、generated identity feature extension の filling-failure obstruction / non-split witness package / multi-label classification へ接続する。 | `defined only` / `proved` |
| `GeneratedAnalyticWitness`, `GeneratedArchitectureLawModel.generatedAnalyticRepresentation`, `generatedAnalyticCoverageAssumptions`, `generatedAnalyticWitnessCompleteness`, `generatedAnalyticSemanticContractCoverage`, `generatedAnalyticRepresentation_coverageAssumptions`, `generatedAnalyticRepresentation_witnessCompleteness`, `generatedAnalyticRepresentation_semanticContractCoverage`, `generatedAnalyticRepresentation_zeroPreserving`, `generatedAnalyticRepresentation_zeroReflecting`, `generatedAnalyticRepresentation_obstructionPreserving`, `generatedAnalyticRepresentation_obstructionReflecting`, `generatedAnalyticRepresentation_nonConclusions`, `generatedRequiredSignatureObstructionValuation`, `generatedRequiredSignatureObstructionValuation_coverageAssumptions`, `generatedRequiredSignatureObstructionValuation_value_zero`, `generatedRequiredSignatureObstructionValuation_noSelectedObstruction`, `generatedRequiredSignatureObstructionValuation_recordsNonConclusions`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_represent_eq_signatureOfGenerated`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_coverageAssumptions`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_witnessCompleteness`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_semanticContractCoverage`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_zeroPreserving`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_zeroReflecting`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_obstructionPreserving`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_obstructionReflecting`, `Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_nonConclusions`, `generatedIdentityAnalyticExtensionFormulaPackage`, `generatedIdentityAnalyticExtensionFormula_representationMapAssumptions`, `generatedIdentityAnalyticExtensionFormula_valuationStructureAssumptions`, `generatedIdentityAnalyticExtensionFormula_decompositionCertificate`, `generatedIdentityAnalyticExtensionFormula_coverageAssumptions`, `generatedIdentityAnalyticExtensionFormula_complexityTransferBoundary`, `generatedIdentityAnalyticExtensionFormula_formula_holds`, `generatedIdentityAnalyticExtensionFormula_requiredAssumptions`, `generatedIdentityAnalyticExtensionFormula_recordsNonConclusions`, `generatedIdentityAnalyticExtensionFormula_obstructionValue_zero` | `inductive` / `def` / `theorem` | generated law model を state space とし、`signatureOfGenerated` を analytic value とする generated analytic representation。coverage / witness completeness / semantic-contract coverage は `True` marker ではなく generated lawfulness equivalence、selected Signature witness universe、generated required Signature axes coverage として discharge する。Chapter 11 entrypoint からも generated preserving / reflecting theorem を公開し、generated selected obstruction valuation と generated identity analytic extension formula package に接続する。identity formula package の assumptions も `True` marker ではなく generated representation coverage、generated valuation coverage、identity decomposition、generated required Signature axes coverage、zero-transfer boundary から discharge する。hand-authored `ArchitectureLawModel` を representation 入力として受け取らない。 | `defined only` / `proved` |
| `Chapter11AnalyticRepresentation.GeneratedExternalSemanticObstructionBoundary`, `GeneratedExternalSemanticObstructionBoundary.generated_semanticFlatWithin`, `GeneratedExternalSemanticObstructionBoundary.external_semantic_obstruction_remains`, `GeneratedExternalSemanticObstructionBoundary.external_not_architectureFlatWithin`, `GeneratedExternalSemanticObstructionBoundary.generated_semantic_flatness_does_not_discharge_external`, `Chapter11AnalyticRepresentation.couponGeneratedExternalSemanticObstructionBoundary`, `coupon_generated_semantic_flatness_does_not_discharge_static_semantic_counterexample`, `coupon_generated_boundary_staticFlat_with_semanticObstruction` | `structure` / `def` / `theorem` | generated law model の reflexive semantic flatness と、外部 selected semantic obstruction を同一視しない境界 package。generated semantic flatness は generated diagram family に相対化され、canonical coupon static/semantic counterexample の semantic obstruction は外部 boundary として残る。 | `defined only` / `proved` |
| `GeneratedOperation`, `GeneratedOperation.atomShape_transformed`, `GeneratedOperation.mappedCarrierShapeDistance`, `GeneratedOperation.mappedCarrierShapeDistance_eq_coordinate_mismatchCount`, `GeneratedOperation.mappedCarrierShapeDistance_eq_zero_iff_coordinate_eq`, `GeneratedOperation.TargetCarrierUnmapped`, `GeneratedOperation.target_atom_primitive`, `GeneratedOperation.unmapped_target_atom_primitive`, `GeneratedOperation.operation_does_not_create_atoms`, `GeneratedOperation.toOperationTransportPackage`, `Chapter7TheoremPackages.generatedOperation_atomShape_transformed`, `generatedOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount`, `generatedOperation_unmapped_target_atom_primitive`, `generatedOperation_toOperationTransportPackage`, `AtomGeneratedMoleculeExamples.generatedApiExpansionOperation`, `generatedApiExpansionOperation_mapped_api_shapeDistance_eq_zero`, `generatedApiExpansionOperation_database_unmapped`, `generatedApiExpansionOperation_unmapped_database_primitive`, `generatedApiExpansionOperation_target_atom_primitive`, `generatedApiExpansionOperation_does_not_create_atoms`, `generatedApiExpansionOperationTransportPackage`, `generatedApiExpansionOperation_target_molecule_is_distinct` | `structure` / `def` / `theorem` | generated object 間の AtomShape transformation を、atom existence を生成しない operation として読み、source/target の generated AATCore 間の `OperationTransportPackage` へ接続する。operation mapped carrier の変化量は AtomShape coordinate mismatch count として計算され、API-only source から API+database target への acceptance では mapped API の distance が 0 で、database は source map 外の target carrier だが target generated object の primitive atom として残る。operation target primitive は caller-supplied field ではなく target generated object の carrier primitive theorem から導出される。operation non-creation も generated operation field ではなく root `AtomAxiomSystem.tool_output_does_not_create_atoms` から導出される。API-only source object から API+database target object への非identity transport acceptance により、source molecule と target molecule が別物でも transport package が通ることを固定する。Chapter 7 entrypoint からも generated operation distance / unmapped target / transport を公開する。 | `defined only` / `proved` |
| `GeneratedRepairTarget`, `GeneratedRepairTarget.ShapeLevel`, `GeneratedRepairTarget.shapeLevel`, `GeneratedRepair`, `GeneratedRepair.clears_selected_target`, `GeneratedRepair.repair_does_not_create_atoms`, `GeneratedRepair.toRepairClearingPackage`, `GeneratedRepairProblemConfiguration`, `GeneratedRepairProblem`, `GeneratedRepairProblem.ShapeLevel`, `GeneratedRepairProblemOperation`, `GeneratedRepairProblemOperation.mappedCarrierShapeDistance`, `GeneratedRepairProblemOperation.mappedCarrierShapeDistance_eq_coordinate_mismatchCount`, `GeneratedRepairProblemOperation.mappedCarrierShapeDistance_eq_zero_iff_coordinate_eq`, `GeneratedRepairProblemOperation.TargetCarrierUnmapped`, `GeneratedRepairProblemOperation.target_atom_primitive`, `GeneratedRepairProblemOperation.unmapped_target_atom_primitive`, `GeneratedRepairProblemOperation.operation_does_not_create_atoms`, `GeneratedRepairProblemCleared`, `GeneratedRepairFromProblem`, `GeneratedRepairFromProblem.clears_selected_problem`, `GeneratedRepairFromProblem.target_generated_molecule`, `GeneratedRepairFromProblem.repair_problem_does_not_create_atoms`, `GeneratedRepairFromProblem.toRepairClearingPackage`, `AtomGeneratedRepairExamples.repairedGeneratedGraphRank`, `AtomGeneratedRepairExamples.repaired_law_model_from_graph_rank`, `AtomGeneratedRepairExamples.generatedMissingPortRepair_target_atom_primitive`, `AtomGeneratedRepairExamples.generatedMissingPortRepair_mapped_api_shapeDistance_eq_zero`, `AtomGeneratedRepairExamples.generatedMissingPortRepair_database_unmapped`, `AtomGeneratedRepairExamples.generatedMissingPortRepair_unmapped_database_primitive`, `GeneratedSynthesisCandidate`, `GeneratedSynthesisCandidate.candidate_flatWithin`, `GeneratedSynthesisCandidate.candidate_flatWithin_eq_lawModel_generated`, `GeneratedSynthesisCandidate.candidate_totalCurvature_eq_zero`, `GeneratedSynthesisCandidate.synthesis_does_not_create_atoms`, `GeneratedSynthesisCandidate.toSynthesisSoundnessPackage`, `Chapter7TheoremPackages.generatedRepair_target_shapeLevel`, `Chapter7TheoremPackages.generatedRepair_clears_selected_target`, `Chapter7TheoremPackages.generatedRepair_toRepairClearingPackage`, `Chapter7TheoremPackages.generatedRepairProblemOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount`, `Chapter7TheoremPackages.generatedRepairProblemOperation_unmapped_target_atom_primitive`, `Chapter7TheoremPackages.generatedRepairFromProblem_shapeLevel`, `Chapter7TheoremPackages.generatedRepairFromProblem_clears_selected_problem`, `Chapter7TheoremPackages.generatedRepairFromProblem_toRepairClearingPackage`, `Chapter7TheoremPackages.generatedSynthesisCandidate_flatWithin`, `Chapter7TheoremPackages.generatedSynthesisCandidate_toSynthesisSoundnessPackage` | `inductive` / `structure` / `def` / `theorem` | valid generated object 内だけで repair target を仮定せず、`GeneratedMolecule` 前の failed atom configuration から port / slot / valence level repair problem を読み、shape-level evidence は `True` marker ではなく constructor-specific `ShapeLevel` witness として保持し、generated repair operation によって valid generated target object / molecule へ到達する。repair problem operation mapped carrier の変化量は AtomShape coordinate mismatch count として読み、missing-port acceptance では mapped API の distance が 0、database は source map 外の target carrier だが target generated object の primitive atom として残る。repair problem operation target primitive は caller-supplied field ではなく target generated object から導出される。repair problem operation / repair / synthesis の non-creation は per-operation / per-candidate field ではなく root `AtomAxiomSystem.tool_output_does_not_create_atoms` から導出される。repair / synthesis candidate は generated graph rank から構成された generated target law model から既存 AAT repair-clearing / synthesis-soundness package に接続し、synthesis flatness は candidate field ではなく target law model の `generatedArchitectureFlatWithin` から導出し、Chapter 7 entrypoint からも公開する。 | `defined only` / `proved` |
| `GeneratedArchitectureLawModel.generatedAATTheoremStatusForSFT`, `GeneratedSFTInput`, `GeneratedSFTInput.theoremStatus`, `GeneratedSFTInput.theoremStatusFromGenerated`, `GeneratedSFTInput.measured_zero_from_generated`, `GeneratedSFTInput.reads_generated_aat`, `GeneratedSFTInput.reads_generated_aat_as_sft_local_premise`, `GeneratedSFTInput.toAATCoreLocalAlgebraForSFT`, `localAlgebra_reads_generated_aat`, `localAlgebra_forecast_correctness_remains_boundary`, `sft_does_not_redefine_atoms`, `sft_does_not_redefine_aat`, `forecast_correctness_remains_boundary`, `sft_event_does_not_create_atoms`, `GeneratedArchitectureLawModel.generatedIdentityCircuitDeltaBoundary`, `GeneratedArchitectureLawModel.generatedIdentityCircuitDeltaBoundary_recorded`, `GeneratedArchitectureLawModel.generatedIdentityAATCoreCircuitDelta`, `GeneratedArchitectureLawModel.generatedIdentityAATCoreCircuitDelta_circuitBoundary`, `GeneratedArchitectureLawModel.generatedIdentityAATCoreCircuitDelta_doesNotCreateAtoms`, `AtomGeneratedSignatureExamples.atomGeneratedSignature_circuitDelta_boundary`, `AtomGeneratedSignatureExamples.atomGeneratedSignature_circuitDelta_does_not_create_atoms` | `def` / `structure` / `theorem` | generated law model の AAT theorem status を任意 field ではなく generated law model から計算し、その status が generated theorem package / measured-zero evidence を記録し、SFT local premise としてだけ渡されることを固定する。`toAATCoreLocalAlgebraForSFT` は generated SFT input から existing SFT local algebra boundary を構成する。SFT event non-creation は `GeneratedSFTInput` field ではなく root `AtomAxiomSystem.sft_event_does_not_create_atoms` から導出する。identity SFT circuit delta は generated law model の selected law/molecule と generated lawfulness 由来の impossible circuit boundary から構成する。SFT / FieldSig は Atom / AAT を再定義せず forecast correctness を結論しない。 | `defined only` / `proved` |
| `GeneratedArchSigAATCoreTransition.sourceBridge`, `targetBridge`, `source_bridge_architectureLawful`, `target_bridge_architectureLawful`, `GeneratedFieldSigAATCoreTransitionAnalysis.fieldsig_reads_generated_archsig_transition_as_sft_analysis`, `forecast_correctness_remains_boundary`, `GeneratedArchSigAATCoreTransportTransition.sourceBridge`, `targetBridge`, `source_bridge_architectureLawful`, `target_bridge_architectureLawful`, `GeneratedFieldSigAATCoreTransportTransitionAnalysis.fieldsig_reads_generated_archsig_transport_transition_as_sft_analysis`, `forecast_correctness_remains_boundary`, `AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedArchSigTransition`, `atomGeneratedSignature_generatedFieldSigAnalysis`, `atomGeneratedSignature_generatedArchSigTransportTransition`, `atomGeneratedSignature_generatedFieldSigTransportAnalysis`, `atomGeneratedSignature_fieldsig_reads_generated_transport_transition`, `atomGeneratedSignature_transport_target_molecule_is_distinct` | `def` / `theorem` | generated law model から AATCore preservation / non-identity transport transition、source / target Signature bridge、FieldSig analysis boundary までを構成し、`architectureLawfulFromAAT` field を手入力しない ArchSig / FieldSig handoff acceptance を固定する。transport transition は source / target law・molecule を transport 専用 delta で分け、preservation に潰さない。 | `defined only` / `proved` |
| `TheoremPackageClass`, `ReconstructionAction`, `ClassificationEvidence`, `ActionAllowed`, `TheoremPackageClassification`, `ClassificationFootprint`, `LegacyBridgeSurface`, `genericSignatureBridgeLegacySurface`, `generatedWalkAcyclicLawModelLegacySurface`, `legacyBridgeSurfaces`, `AATCandidate`, `classifyAATCandidate`, `classifyChapter7`, `classifyChapter8`, `classifyChapter9`, `classifyChapter10`, `classifyChapter11`, `classifySFT`, `allClassifications`, `allPackageIds`, `allClassificationClasses`, `allClassificationActions`, `allClassificationClassActions`, `allClassificationFootprints` | `inductive` / `structure` / `def` | 再構成計画 8.2 の theorem package 分類 registry。各 row は `atomGenerated` / `bridgeAssumed` / `representationLevel` のいずれかで、分類ごとに generated entrypoint、bridge assumption、representation surface の evidence list を要求する。`unclassified` constructor は存在しない。generic Signature bridge や旧 `GeneratedArchitectureLawModel.generatedWalkAcyclic` raw premise surface のような compatibility / obsolete API は `LegacyBridgeSurface` に分離し、theorem package source row には数えない。`allClassificationClassActions` と `allClassificationFootprints` は source-of-truth / downstream library / bridge-assumption 混入境界を finite decidable check に落とす。 | `defined only` |
| `aat_candidates_are_registered`, `chapter7_candidates_are_registered`, `chapter8_candidates_are_registered`, `chapter9_candidates_are_registered`, `chapter10_candidates_are_registered`, `chapter11_candidates_are_registered`, `sft_candidates_are_registered`, `registry_rows_have_classification_evidence`, `registry_rows_have_allowed_actions`, `theorem_package_registry_has_unique_package_ids`, `theorem_package_registry_has_no_bridge_assumed_rows`, `theorem_package_registry_has_no_bridge_assumption_footprints`, `theorem_package_registry_has_no_temporary_bridge_actions`, `theorem_package_registry_has_no_rewrite_targets`, `theorem_package_registry_source_rows_are_atom_generated`, `theorem_package_registry_source_footprints_are_generated_only`, `theorem_package_registry_representation_rows_are_downstream_libraries`, `theorem_package_registry_representation_footprints_are_downstream_only`, `AATCompleteFormalizationExamples.generatedComponentTheoremSuite_registry_has_no_rewrite_targets`, `AATCompleteFormalizationExamples.generatedComponentTheoremSuite_registry_source_rows_are_atom_generated`, `AATCompleteFormalizationExamples.generatedComponentTheoremSuite_registry_representation_rows_are_downstream`, `generic_signature_bridge_is_not_theorem_package_registry_row`, `generic_signature_bridge_is_legacy_replaced_surface`, `generated_walk_acyclic_law_model_is_not_theorem_package_registry_row`, `generated_walk_acyclic_law_model_is_legacy_replaced_surface`, `generated_signature_bridge_is_atom_generated`, `finite_static_core_is_atom_generated`, `archmap_observation_handoff_is_atom_generated`, `nonidentity_transport_handoff_is_atom_generated`, `generated_chapter8_path_diagram_is_atom_generated`, `generated_extension_obstruction_universe_is_atom_generated`, `generated_filling_failure_bridge_is_atom_generated`, `generated_split_lifting_bridge_is_atom_generated`, `generated_complexity_residual_bridge_is_atom_generated`, `generated_consequence_envelope_is_atom_generated`, `generated_support_safety_is_atom_generated`, `generated_sft_projection_cone_is_atom_generated`, `generated_sft_action_policy_reachability_is_atom_generated`, `generated_sft_field_update_is_atom_generated`, `generated_sft_finite_exact_model_is_atom_generated`, `generated_sft_counterexample_roadmap_is_atom_generated`, `generated_analytic_representation_is_atom_generated`, `generated_analytic_extension_formula_is_atom_generated`, `generated_external_semantic_boundary_is_atom_generated`, `generated_chapter11_fixture_boundary_is_atom_generated` | `theorem` | 各 theorem-package candidate が対応する registry slice に載ること、registry row が分類 evidence と許可された migration action を持つこと、package id が重複しないこと、current theorem package registry に bridge-assumed row / bridge-assumption footprint / temporary bridge action / rewrite-target row が残らないこと、source-of-truth action を持つ row は Atom-generated であり、generated entrypoint だけを source evidence として持つこと、representation-level row は downstream library action と representation entrypoint だけを持つこと、generic Signature bridge と旧 raw `WalkAcyclic` law-model state surface は legacy surface として generated graph-rank replacement を持つが registry row ではないこと、finite static structural core / generated Signature bridge / ArchMap observed-atom handoff / 非identity transport handoff / Chapter 8 path-diagram package / generated extension obstruction universe / generated filling-failure bridge / generated split-lifting bridge / generated complexity-residual bridge / generated consequence envelope / generated SFT support safety / generated SFT projection-cone package / generated SFT action-policy-reachability package / generated SFT field update / generated SFT finite exact model / generated SFT counterexample-roadmap package / generic analytic representation と ArchitectureSignature representation / generated analytic extension formula / generated external semantic boundary / Chapter 11 metadata・coupon fixture・static-semantic counterexample・measurement boundary は Atom-generated であることを固定する。 | `proved` |
| `AtomShapeKindCoverageExamples.*`, `AtomGeneratedSignatureExamples.*`, `AtomGeneratedMoleculeExamples.generatedComponentObject_api_database_shapeDistance_eq_one`, `AtomGeneratedMoleculeExamples.generatedComponent_shapeCoordinateTotalCurvature_eq_zero`, `AtomGeneratedMoleculeExamples.generatedComponent_noMeasuredShapeCoordinateCurvatureObstruction`, `AtomGeneratedMoleculeExamples.generatedComponentLawModel_carries_generated_graph_rank`, `AtomGeneratedMoleculeExamples.generatedComponentLawModel_walkAcyclic_derived_from_graph_rank`, `AtomGeneratedMoleculeExamples.generatedAuthorityEffectMolecule_not_arbitrary_set`, `AtomGeneratedMoleculeExamples.generatedAuthorityPolicy_from_authority_atom`, `AtomGeneratedMoleculeExamples.generatedEffectLawInput_from_effect_atom`, `AtomGeneratedMoleculeExamples.generatedAuthorityEffectLaw_locally_satisfied`, `AtomGeneratedMoleculeExamples.generatedContractSemanticMolecule_not_arbitrary_set`, `AtomGeneratedMoleculeExamples.generatedContract_from_contract_atom`, `AtomGeneratedMoleculeExamples.generatedSemanticInterpretation_from_semantic_atom`, `AtomGeneratedMoleculeExamples.generatedSemanticContractCoverage_from_contract_atom`, `AtomGeneratedMoleculeExamples.generatedApiExpansionOperation_target_atom_primitive`, `AtomGeneratedMoleculeExamples.generatedApiExpansionOperation_does_not_create_atoms`, `AtomGeneratedMoleculeExamples.generatedComponentIdentityOperation_does_not_create_atoms`, `AtomGeneratedMoleculeExamples.generatedComponentSynthesisCandidate_flatWithin_from_law_model`, `AtomGeneratedMoleculeExamples.generatedComponentSynthesisCandidate_does_not_create_atoms`, `AtomGeneratedMoleculeExamples.directedRelationGeneratedGraph_api_to_database_edge`, `AtomGeneratedMoleculeExamples.directedRelationGeneratedGraph_edge_uses_source_target_ports`, `AtomGeneratedMoleculeExamples.directedRelationGeneratedGraph_no_database_to_api_edge`, `AtomGeneratedMoleculeExamples.directedRelationGraphRank`, `AtomGeneratedMoleculeExamples.directedRelation_law_model_from_graph_rank`, `AtomGeneratedMoleculeExamples.directedRuntimeGeneratedGraph_api_to_database_edge`, `AtomGeneratedMoleculeExamples.directedRuntimeGeneratedGraph_edge_uses_source_target_ports`, `AtomGeneratedMoleculeExamples.directedRuntimeGeneratedGraph_no_database_to_api_edge`, `AtomGeneratedMoleculeExamples.directedRuntimeGraphRank`, `AtomGeneratedMoleculeExamples.directedRuntimeGraphRank_walkAcyclic`, `AtomGeneratedRepairExamples.repairedGeneratedGraphRank`, `AtomGeneratedRepairExamples.repaired_law_model_from_graph_rank`, `AtomGeneratedRepairExamples.generatedMissingPortRepair_target_atom_primitive`, `AtomGeneratedRepairExamples.generatedMissingPortRepair_mapped_api_shapeDistance_eq_zero`, `AtomGeneratedRepairExamples.generatedMissingPortRepair_database_unmapped`, `AtomGeneratedRepairExamples.generatedMissingPortRepair_unmapped_database_primitive`, `AtomGeneratedRepairExamples.generatedMissingPortRepair_does_not_create_atoms`, `AtomGeneratedRepairExamples.*`, `ArchMapObservationExamples.*`, `AtomGeneratedClassificationExamples.*`, `IncompatibleAtomCompositionExamples.effect_atom_without_authority_not_generated_molecule`, `IncompatibleAtomCompositionExamples.capability_atom_without_data_state_not_generated_molecule`, `IncompatibleAtomCompositionExamples.semantic_atom_without_contract_not_generated_molecule`, `IncompatibleAtomCompositionExamples.*` | `def` / `theorem` | positive acceptance は current AtomKind grammar の shaped atom coverage と source-like AtomShape から generated law model / signature / generated AATCore / generated AtomShape distance / shape-coordinate curvature / authority-effect local law satisfaction / semantic-contract coverage / capability-data-state support / oriented relation edge / generated graph rank / law model state 上の generated graph rank / generated operation target primitive / generated repair problem operation distance / root AtomAxiomSystem 由来の generated operation / repair / synthesis / SFT event non-creation / law model 由来 synthesis flatness / oriented runtime edge / generated runtime graph rank / operation transport / synthesis soundness / SFT handoff / generated ArchSig-FieldSig preservation and transport transition analysis / generated SFT projection / ForecastCone / support-safety package / generated analytic representation package / generated analytic extension formula package までを通す。authority-effect acceptance は effect atom の required authority port が同じ generated molecule 内の authority atom によって満たされ、generated authority policy と generated effect law input から local satisfaction が構成され、authority が欠ける effect-only required-port configuration は generated molecule にならないことを固定する。semantic-contract acceptance は semantic atom の required contract port が同じ generated molecule 内の contract atom によって満たされ、generated contract surface と generated semantic interpretation から semantic-contract coverage が構成され、contract が欠ける semantic-only configuration は generated molecule にならないことを固定する。capability/data-state acceptance は capability atom の required data-state payload port が同じ generated molecule 内の data-state atom によって満たされ、data-state が欠ける capability-only configuration は generated molecule にならないことを固定する。ArchMap observation acceptance は observed atom selection から generated molecule / object へ handoff し、carrier が observed evidence に戻れることを固定する。classification acceptance は theorem package registry が各 candidate を全列挙し、row が分類 evidence と allowed action を持ち、package id が重複せず、bridge-assumed / bridge-assumption footprint / temporary bridge / rewrite-target row が残っていないこと、source-of-truth row は Atom-generated だけで generated source evidence のみを持つこと、representation-level row は downstream library だけで generated source evidence や bridge assumptions を持たないこと、generic Signature bridge と旧 raw `WalkAcyclic` law-model surface が legacy replacement surface であり registry source row ではないこと、ArchMap observed-atom handoff、Chapter 8 path / observation / diagram / non-fillability、generated extension obstruction universe、generated filling-failure bridge、generated self-view split-lifting bridge、generated complexity / residual coverage bridge が Atom-generated として分類され、Chapter 11 generic analytic representation / ArchitectureSignature representation / obstruction valuation / analytic extension formula / generated external semantic boundary も Atom-generated として分類することを固定する。generated repair acceptance は missing required port configuration が直接 generated molecule にならず、repair problem operation が mapped API distance 0 と unmapped database primitive evidence を持ち、repair 後に generated graph rank 由来の target law model / generated target molecule / object / repair-clearing package へ到達することを固定する。negative acceptance は incompatible slot、missing required port、relation endpoint 欠落、authority 欠落、semantic contract 欠落、capability data-state 欠落、concern hint、observation gap、hand-authored graph 非含意を固定する。 | `proved` |

| `AtomGeneratedMoleculeExamples.generatedCapabilityDataStateMolecule_not_arbitrary_set`, `generatedCapability_from_capability_atom`, `generatedDataState_from_data_state_atom`, `generatedCapabilityDataStateSupport_from_data_state_atom`, `IncompatibleAtomCompositionExamples.capability_atom_without_data_state_not_generated_molecule` | `def` / `theorem` | capability atom の required data-state payload port が同じ generated molecule 内の data-state atom で満たされ、generated capability / generated data-state から capability/data-state support が構成されることを固定する。data-state payload がない capability-only configuration は `GeneratedMolecule.missing_required_port_not_generatedMolecule` により generated molecule にならない。global capability completeness、runtime permission correctness は結論しない。 | `proved` |
| `AtomGeneratedMoleculeExamples.generatedContractSemanticMolecule_not_arbitrary_set`, `generatedContract_from_contract_atom`, `generatedSemanticInterpretation_from_semantic_atom`, `generatedSemanticContractCoverage_from_contract_atom`, `IncompatibleAtomCompositionExamples.semantic_atom_without_contract_not_generated_molecule` | `def` / `theorem` | semantic atom の required contract port が同じ generated molecule 内の contract atom で満たされ、generated contract / generated semantic interpretation から semantic-contract coverage が構成されることを固定する。contract がない semantic-only configuration は `GeneratedMolecule.missing_required_port_not_generatedMolecule` により generated molecule にならない。ambient semantic coverage、all-contract compliance は結論しない。 | `proved` |

Non-conclusions: この kernel は `AtomShape` / `Generated*` surface の存在と代表 acceptance
theorem と分類 registry を固定するが、全 theorem package の Atom-generated 移行完了、実コード観測
completeness、ArchMap observation completeness、global semantic flatness、all-path homotopy
completeness、FieldSig forecast calibration は結論しない。

## AG版AAT Lean形式化 PRD-1 bootstrap

File: `Formal/AG.lean`, `Formal/AG/Atom/Atom.lean`, `Formal/AG/Atom/Axioms.lean`,
`Formal/AG/Atom/Observation.lean`, `Formal/AG/Atom/Family.lean`,
`Formal/AG/Atom/Configuration.lean`, `Formal/AG/Atom/ArchitectureObject.lean`,
`Formal/AG/Atom/Invariant.lean`, `Formal/AG/Atom/Law.lean`,
`Formal/AG/Atom/Obstruction.lean`, `Formal/AG/Atom/LawfulnessZero.lean`,
`Formal/AG/Atom/ThreeReading.lean`, `Formal/AG/Atom/ObjectAlgebra.lean`,
`Formal/AG/Atom/AATCore.lean`, `Formal/AG/Examples/FiniteModel.lean`.

PRD-1 [第I部 Atom・対象・法則](lean_ag_part_1_atoms_objects_laws_prd.md) の
AC1/R0、AC2/R1、AC3/R1、AC4/R2、AC5/R3、AC6/R4、AC7/R5、AC8/R6、AC9/R7、AC10/R8、AC11/R8、AC12/R9、AC13/R9、AC14/R10、AC15-AC17/R11 に対応する初期 Atom entrypoint である。`Formal/Arch` は import せず、
AG 版 AAT の namespace を `AAT.AG` として分離する。

R11 coverage note: Issue [#1959](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1959)
で `Formal/AG` の宣言 inventory を本文ラベル行に対応づけ直し、
helper 宣言は該当する本文ラベル行の Lean 名欄に束ねる。`rg -n "\b(axiom|admit|sorry|unsafe)\b" Formal/AG Formal/AG.lean`
と `rg -n "Formal\.Arch|import Formal\.Arch" Formal/AG Formal/AG.lean` は no matches である。

| 本文ラベル | Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- | --- |
| `I.定義1.1` | `AAT.AG.AtomRecord` | `structure` | kind / axis / subject / predicate / payload を持つ五成分 Atom record。 | `defined only` |
| `I.定義1.1` | `AAT.AG.AtomCarrier` | `structure` | Atom 型と五つの coordinate projection を束ねる carrier。 | `defined only` |
| `I.定義1.1` | `AAT.AG.AtomCarrier.record` | `def` | carrier 内の Atom を `AtomRecord` として読む projection。 | `defined only` |
| `I.公理A0-A8` | `AAT.AG.AtomAxiomSystem`, `AtomAxiomSystem.primitive_exists`, `AtomAxiomSystem.typing_total`, `AtomAxiomSystem.configurationOf`, `AtomAxiomSystem.operateFamily` | `structure` / `def` / `theorem` | AG Atom carrier 上で A0-A8 を structure field として束ねる package と、primitive existence / typing totality / configuration composition / operation の accessor。 | `defined only` / `proved` |
| `I.公理A3` | `AAT.AG.SameCoordinates`, `AAT.AG.AtomAxiomSystem.eq_iff_sameCoordinates`, `AAT.AG.AtomAxiomSystem.ext` | `def` / `theorem` | 五成分一致と Atom 同一性の同値、ならびに ext 補題。 | `proved` |
| `I.公理A8` | `AAT.AG.ExtractionDoctrine`, `AAT.AG.ExtractionDoctrine.atomize_unique`, `AAT.AG.CoarseProjection`, `AAT.AG.AtomAxiomSystem.doctrine_family_unique` | `structure` / `theorem` | extraction doctrine と、`atomize` が関数であることから得る canonical Atom family の一意性。 | `defined only` / `proved` |
| `I.命題A9` | `AAT.AG.ObservationModel`, `ObservationModel.NonInjective`, `ObservationProjection`, `ReconstructionAttempt`, `no_exact_reconstruction_of_nonInjective`, `A9Example.Atom`, `A9Example.Family`, `A9Example.Source`, `A9Example.Observation`, `A9Example.carrier`, `A9Example.observeAtom`, `A9Example.observedAtom?`, `A9Example.AppearsInObservation`, `A9Example.familyObservation`, `A9Example.doctrine`, `A9Example.projection`, `A9Example.reconstruction`, `A9Example.noninjective_atom_observation`, `A9Example.unobserved_atom_exists`, `A9Example.noninjective_family_observation`, `A9Example.reconstruction_not_exact`, `A9Example.canonical_family_unique`, `A9Example.observation_incompleteness_coexists_with_a8` | `inductive` / `structure` / `def` / `theorem` | 観測写像、projection、reconstruction、非単射観測、未観測 Atom、A8 一意性との分離を有限例で示す。 | `defined only` / `proved` |
| `I.定義3.1-3.5` | `AAT.AG.AtomFamily`, `AtomFamily.Subset`, `AtomFamily.support`, `AtomFamily.restrictAxis`, `AtomFamily.Compatible`, `AtomFamily.EqCompatible`, `AtomFamily.AtomOrigin`, `AtomFamily.OriginMarked`, `AtomFamily.InferenceSystem`, `AtomFamily.IsClosed`, `AtomFamily.closure`, `AtomFamily.support_of_mem`, `AtomFamily.restrictAxis_subset`, `AtomFamily.restrictAxis_axis`, `AtomFamily.subset_closure`, `AtomFamily.closure_isClosed`, `AtomFamily.closure_minimal` | `structure` / `def` / `inductive` / `theorem` | Atom family、subset、support、axis restriction、選択された payload compatibility relation に相対化された compatibility、origin marker、monotone 推論規則族 closure と support/restriction 補題および closure 3補題。 | `defined only` / `proved` |
| `I.定義4.1 / 4.2 / 4.4` | `AAT.AG.AtomConfiguration`, `AtomConfiguration.Subconfiguration`, `AtomConfiguration.FamilySupported`, `AtomConfiguration.Molecule`, `AtomConfiguration.Subconfiguration.refl`, `AtomConfiguration.Subconfiguration.trans`, `AtomConfiguration.Subconfiguration.preorder`, `AtomConfiguration.Molecule.family_subset_parent`, `AtomConfiguration.Molecule.finite_marker` | `structure` / `def` / `theorem` | Atom configuration `C = (F, R, E)`、R/E の family-supported predicate、finite marker 付き molecule、subconfiguration と、その反射・推移・preorder 補題。 | `defined only` / `proved` |
| `I.定義5.1 / 5.2 / 命題5.3 / 定義5.4` | `AAT.AG.ArchitectureObject`, `ArchitectureObject.GeneratedObject`, `ArchitectureObject.ObjectEquivalence`, `ArchitectureObject.atom_origin`, `ArchitectureObject.generated_family_eq`, `ArchitectureObject.generated_family_subset`, `ArchitectureObject.ObjectEquivalence.configuration_equivalent`, `ArchitectureObject.ObjectEquivalence.structure_maps_preserved`, `ArchitectureObject.ObjectEquivalence.selected_quantities_preserved` | `structure` / `def` / `theorem` | Architecture object `A = (C, S, Q)`、抽象 structure maps / selected quantities、Atom family からの generated object relation、Atom-Origin theorem、object equivalence の保存 predicate。 | `defined only` / `proved` |
| `I.定義6.1-6.3` | `AAT.AG.FunctionInvariant`, `AAT.AG.PredicateInvariant`, `AAT.AG.Invariant`, `AAT.AG.InvariantFamily`, `Invariant.EqualityPreserved`, `Invariant.OrderPreserved`, `Invariant.PredicatePreserved`, `Invariant.equalityPreserved_apply`, `Invariant.orderPreserved_apply`, `Invariant.predicatePreserved_apply`, `InvariantFamily.get`, `InvariantFamily.get_eq` | `structure` / `inductive` / `def` / `theorem` | ArchitectureObject 上の関数形 invariant、述語形 invariant、mixed invariant family、等式形 preservation `I(A)=I(B)`、順序形 preservation `I(B) <= I(A)`、predicate preservation と accessor 補題。 | `defined only` / `proved` |
| `I.定義7.1-7.3` | `AAT.AG.Law`, `AAT.AG.LawRole`, `AAT.AG.LawWitnessFamily`, `AAT.AG.SignatureAxes`, `AAT.AG.LawUniverse`, `LawUniverse.Required`, `LawUniverse.Optional`, `LawUniverse.Derived`, `AAT.AG.Lawfulness`, `AAT.AG.SemanticLawful`, `AAT.AG.NoRequiredObstruction`, `AAT.AG.RequiredSignatureAxesZero`, `AAT.AG.lawfulness_required_holds`, `AAT.AG.semanticLawful_iff_lawfulness`, `AAT.AG.noRequiredObstruction_no_bad_witness`, `AAT.AG.requiredSignatureAxesZero_axis` | `structure` / `inductive` / `def` / `theorem` | ArchitectureObject 上の law predicate、required / optional / derived role を持つ law universe、witness family、selected reading、coverage / exactness assumption、required lawfulness、三述語と accessor 補題。三述語の同値は主張しない。 | `defined only` / `proved` |
| `I.定義8.1 / 8.2 / 8.5` | `AAT.AG.Obstruction`, `AAT.AG.ObstructionCircuit`, `AAT.AG.ObstructionValueDomain`, `AAT.AG.ObstructionValuation`, `AAT.AG.ZeroReflectingAggregation`, `AAT.AG.ZeroReflectingListAggregation`, `LawUniverse.RequiredIndex`, `AAT.AG.FiniteIndexEnumeration`, `ZeroReflectingListAggregation.toIndexed`, `AAT.AG.omegaU`, `AAT.AG.omegaU_zero_iff_required`, `ObstructionCircuit.relation_supported_holds`, `ObstructionCircuit.finite_marker`, `ObstructionCircuit.law_failure_holds`, `ObstructionValueDomain.nat`, `ObstructionValueDomain.bool`, `ObstructionValueDomain.NonnegativeWeight`, `ObstructionValueDomain.NonnegativeWeight.zero`, `ObstructionValueDomain.NonnegativeWeight.sup`, `ObstructionValueDomain.nonnegativeWeight`, `ObstructionAggregation.natSum`, `ObstructionAggregation.boolOr`, `ObstructionAggregation.weightSup`, `ObstructionAggregation.natSum_eq_zero_iff`, `ObstructionAggregation.boolOr_eq_false_iff`, `ObstructionAggregation.weightSup_eq_zero_iff`, `ObstructionAggregation.natSumListAggregation`, `ObstructionAggregation.boolOrListAggregation`, `ObstructionAggregation.weightSupListAggregation` | `structure` / `def` / `theorem` | Obstruction witness、finite marker 付き obstruction circuit、zero / positive / dichotomy / no-cancellation を持つ値域、law-indexed valuation、required law index に相対化した aggregate valuation、finite-list aggregation から selected finite index aggregation への bridge、count sum / boolean disjunction / nonnegative-weight sup の finite-list zero-reflecting theorem。定理9.3 は主張しない。 | `defined only` / `proved` |
| `I.命題9.1 / 9.2 / 定理9.3` | `AAT.AG.ObstructionSound`, `AAT.AG.ObstructionComplete`, `AAT.AG.law_holds_iff_omega_zero`, `AAT.AG.lawfulness_iff_omegaU_zero` | `def` / `theorem` | selected law valuation の soundness / completeness predicate、per-law `L(A) ↔ omega_L(A)=0`、required law universe と zero-reflecting aggregation に相対化した `Lawfulness A LU ↔ omegaU ... A = 0`。三述語一致は主張しない。 | `defined only` / `proved` |
| `I.定理9.3 後段` | `AAT.AG.ThreeReadingAgreementAssumptions`, `ThreeReadingAgreementAssumptions.semanticLawful_iff_noRequiredObstruction`, `ThreeReadingAgreementAssumptions.noRequiredObstruction_iff_requiredSignatureAxesZero`, `ThreeReadingAgreementAssumptions.semanticLawful_iff_requiredSignatureAxesZero`, `ThreeReadingAgreementAssumptions.threeReadingAgreement` | `structure` / `theorem` | witness completeness、axis exactness、coverage、selected reading exactness を明示 field として持つ package から、`SemanticLawful(A,U)` / `NoRequiredObstruction(A,W)` / `RequiredSignatureAxesZero(A,S)` の三読み一致を取り出す。 | `defined only` / `proved` |
| `I.定義10.1-10.3 / 命題10.4` | `AAT.AG.Operation`, `AAT.AG.ArchitectureSignature`, `AAT.AG.ObjectAlgebra`, `AAT.AG.OperationRole`, `Operation.objectMap_apply`, `Operation.configurationMap_apply`, `Operation.PreservesFunctionInvariant`, `Operation.PreservesPredicateInvariant`, `Operation.ReflectsObstruction`, `Operation.RepairsObstruction`, `Operation.ExtendsAtomFamily`, `Operation.SynthesizesLawfulObject`, `Operation.TranslatesRepresentation`, `Operation.preservesFunctionInvariant_apply`, `Operation.preservesPredicateInvariant_apply`, `Operation.reflectsObstruction_witness`, `Operation.repairsObstruction_apply`, `Operation.extendsAtomFamily_apply`, `Operation.synthesizesLawfulObject_apply`, `Operation.translatesRepresentation_witness`, `ArchitectureSignature.read`, `ArchitectureSignature.selected_axis`, `ArchitectureSignature.read_eq_coordinate`, `ObjectAlgebra.getObject`, `ObjectAlgebra.getOperation`, `ObjectAlgebra.getOperationSource`, `ObjectAlgebra.getOperationTarget`, `ObjectAlgebra.getObstructionCircuit`, `ObjectAlgebra.getObject_eq`, `ObjectAlgebra.getOperation_eq`, `ObjectAlgebra.operation_source_object`, `ObjectAlgebra.operation_target_object`, `ObjectAlgebra.getObstructionCircuit_eq` | `structure` / `inductive` / `def` / `theorem` | Object Algebra の Obj / Op / Inv / Law / Ob / Sig、source / target と configuration map を持つ operation、Op の source / target が Obj 内にあること、多軸 signature、operation の preservation / reflection / repair / extension / synthesis / translation の六役割 predicate と accessor 補題。定理10.5 は主張しない。 | `defined only` / `proved` |
| `I.定理10.5` | `AAT.AG.AATCorePackage`, `AATCorePackage.identityOperation`, `AATCorePackage.objectAlgebraOfComponents`, `AATCorePackage.ofComponents`, `AATCorePackage.exists_ofComponents`, `AATCorePackage.axioms_eq`, `AATCorePackage.family_eq`, `AATCorePackage.configuration_eq`, `AATCorePackage.object_eq`, `AATCorePackage.configuration_family`, `AATCorePackage.object_configuration`, `AATCorePackage.lawUniverse_eq`, `AATCorePackage.obstructionLaw_eq`, `AATCorePackage.obstructionCircuit_eq`, `AATCorePackage.signature_eq`, `AATCorePackage.algebra_eq`, `AATCorePackage.algebra_object`, `AATCorePackage.algebra_lawUniverse`, `AATCorePackage.algebra_signature`, `AATCorePackage.algebra_operation_source`, `AATCorePackage.algebra_operation_target` | `structure` / `def` / `theorem` | AtomAxiomSystem と R1-R7 / AC12 の component を受け取り、configuration-family / object-configuration 整合性付きで singleton ObjectAlgebra に束ねた AAT Core theorem package を構成する。`exists_ofComponents` は obstruction circuit component を heterogeneous equality として含む。`#print axioms` で `exists_ofComponents` / `ofComponents` / `algebra_object` が追加公理に依存しないことを確認済み。 | `defined only` / `proved` |
| `I.R10 finite model / 例8.3 / 例8.4 / 定理9.3 example` | `FiniteModel.FiniteAtom`, `FiniteModel.FiniteAtom.all`, `FiniteModel.FiniteAtom.mem_all`, `FiniteModel.carrier`, `FiniteModel.allFamily`, `FiniteModel.cycleRelation`, `FiniteModel.substitutionRelation`, `FiniteModel.configuration`, `FiniteModel.configuration_familySupported`, `FiniteModel.object`, `FiniteModel.objectOfConfiguration`, `FiniteModel.noCycleLaw`, `FiniteModel.substitutionLaw`, `FiniteModel.invariantFamily`, `FiniteModel.lawUniverse`, `FiniteModel.lawUniverse_required`, `FiniteModel.signature`, `FiniteModel.axiomSystem`, `FiniteModel.finite_atom_exists`, `FiniteModel.cycle_dependsAB_BC`, `FiniteModel.cycle_dependsBC_CA`, `FiniteModel.cycle_dependsCA_AB`, `FiniteModel.cycleObstructionCircuit`, `FiniteModel.cycle_obstruction_law_failure`, `FiniteModel.substitution_impl_base`, `FiniteModel.substitution_contract_impl_base`, `FiniteModel.substitutionObstructionCircuit`, `FiniteModel.hasCycleWitness`, `FiniteModel.object_hasCycleWitness`, `FiniteModel.substitution_obstruction_law_failure`, `FiniteModel.noCycleOmega`, `FiniteModel.noCycleValuation`, `FiniteModel.singletonRequiredAggregation`, `FiniteModel.noCycleSound`, `FiniteModel.noCycleComplete`, `FiniteModel.finite_lawfulness_iff_omega_zero`, `FiniteModel.corePackage`, `FiniteModel.corePackage_object` | `inductive` / `def` / `theorem` | component / depends / contract / substitution atoms を持つ finite example universe、A0-A8 package、relation witness に基づく NoCycle と substitution obstruction circuit、定理9.3 の singleton required law universe 上の finite example、AAT Core package への handoff。 | `defined only` / `proved` |

Non-conclusions: この bootstrap は `Formal/AG` の Atom carrier、A0-A8 package、A9、
AtomFamily / closure、Configuration / Molecule、ArchitectureObject / Atom-Origin、
Invariant / preservation、Law / Lawfulness、Obstruction / Valuation、定理9.3 本体と後段三読み一致、
Object Algebra / operation / signature / operation role predicate、定理10.5 AAT Core theorem package の入口であり、
finite model example theorem package までを含む。第II部以降の concrete graph / category / algebra / diagram / state transition instance は後続 Issue の対象である。

## AG版AAT Lean形式化 PRD-2 / 第II部 Architecture Geometry・Site・Sheaf

File: `Formal/AG/Site.lean`, `Formal/AG/Site/Basic.lean`,
`Formal/AG/Site/Context.lean`, `Formal/AG/Site/ContextCategory.lean`,
`Formal/AG/Site/Coverage.lean`, `Formal/AG/Site/Topology.lean`,
`Formal/AG/Site/Adequate.lean`, `Formal/AG/Site/Geometry.lean`,
`Formal/AG/Site/Sheaf.lean`, `Formal/AG/Site/Descent.lean`,
`Formal/AG/Site/FinitePoset.lean`, `Formal/AG/Site/SheafCategory.lean`,
`Formal/AG/Examples/FiniteModel.lean`.

PRD-2 [第II部 Architecture Geometry・Site・Sheaf](lean_ag_part_2_sites_sheaves_prd.md) の
AC1/R0、AC2/R1、AC3-AC4/R2、AC5/R3、AC6-AC7/R4、AC8-AC9/R5、AC10/R6、AC11/R7、AC12/R8、AC13-AC14/R9、AC15/R10、AC16/R11、AC17-AC19/R12 に対応する site/context entrypoint と台帳である。現時点では
PRD-1 の `AATCorePackage` に依存する入口、Architecture Context の最小モデル、
§5 の射 role predicate、命題4.2 の finite-meet preorder / quotient-poset package、
仮定4.3 の pullback lifting package、coverage family、admissible cover の5条件までを Lean 上に置き、
admissible cover から生成される `J_U` と Mathlib `Coverage.toGrothendieck` bridge までを Lean 上に置く。
U-adequate cover、補題7.2A、AAT Site、Architecture Geometry、presheaf、sheaf condition bridge、名前付き sheaf family、gluing / descent、sheafification comparison / gap、finite poset Čech regime と高次消滅、AAT sheaf category entrypoint、PRD-1 finite model 上の singleton site example も Lean 上に置く。

| 本文ラベル | Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- | --- |
| `II.R0` | `AAT.AG.Site.PartIPrerequisites`, `PartIPrerequisites.architectureObject`, `PartIPrerequisites.lawUniverse`, `PartIPrerequisites.signature`, `PartIPrerequisites.architectureObject_configuration` | `structure` / `def` / `theorem` | 第II部 site tower が PRD-1 の `AATCorePackage` から architecture object / law universe / signature を読むための prerequisite package と accessor。 | `defined only` / `proved` |
| `II.定義3.1 / §5.1-5.4` | `AAT.AG.Site.MinimalContext`, `AAT.AG.Site.ArchitectureContext`, `ArchitectureContext.Support`, `ArchitectureContext.Axis`, `ArchitectureContext.Observable`, `AAT.AG.Site.ContextMorphism`, `ContextMorphism.IsRestriction`, `ContextMorphism.IsProjection`, `ContextMorphism.IsRefinement`, `ContextMorphism.IsBaseChange`, `ContextMorphism.supportReadable_of_restriction`, `ContextMorphism.axisReadable_of_restriction`, `ContextMorphism.observableFunctorial_of_restriction`, `ContextMorphism.nonGenerating_of_restriction`, `ContextMorphism.axisForgetting_of_projection`, `ContextMorphism.supportRefinement_of_refinement`, `ContextMorphism.axisRefinement_of_refinement`, `ContextMorphism.baseChangeCompatible_of_baseChange` | `structure` / `def` / `theorem` | 最小 context model `(Supp, Ax, Obs)`、最小読みを含む一般 context、local context から target context への readable morphism、および restriction / projection / refinement / base change の role predicate と accessor。 | `defined only` / `proved` |
| `II.定義4.1 / 命題4.2 / 仮定4.3` | `AAT.AG.Site.ArchCtx`, `ContextPreorderCategory`, `ContextPreorderCategory.Hom`, `ContextPreorderCategory.hom_subsingleton`, `ContextPreorderCategory.id`, `ContextPreorderCategory.comp`, `ContextPreorderCategory.morphism`, `ContextPreorderCategory.morphism_isRestriction`, `ContextFiniteMeet`, `ReadableEquivalent`, `ReadableEquivalent.refl`, `ReadableEquivalent.symm`, `ReadableEquivalent.trans`, `readableSetoid`, `QuotientArchCtx`, `ContextFiniteMeetPreorderCategory`, `ContextFiniteMeetPosetCategory`, `QuotientFiniteMeetPosetCategory`, `finiteMeetPreorderCategoryOf`, `finiteMeetPosetCategoryOf`, `minimalContextFiniteMeetPreorderCategory`, `minimalContextFiniteMeetPosetCategory`, `minimalContextQuotientFiniteMeetPosetCategory`, `ContextOverlapPullback`, `ContextOverlapPullback.left`, `ContextOverlapPullback.right`, `ContextOverlapPullback.base`, `ContextOverlapPullback.lift`, `meetOverlapPullback`, `minimalMeetPullback` | `abbrev` / `structure` / `def` / `theorem` | `ArchCtx(A)` の readable morphism 付き preorder-category reading、finite meet、readable equivalence quotient、quotient object 上の finite-meet poset package、pullback / overlap 仮定 package と lifting property、および meet が overlap を実現する補題。 | `defined only` / `proved` |
| `II.定義6.1 / 定義7.1前半` | `AAT.AG.Site.CoverageFamily`, `CoverageFamily.inclusionMorphism`, `CoverageFamily.inclusion_isRestriction`, `CoverageFamily.inclusion_nonGenerating`, `AAT.AG.Site.CoverageRequirements`, `AAT.AG.Site.AdmissibleCover`, `AdmissibleCover.support`, `AdmissibleCover.witness`, `AdmissibleCover.axis`, `AdmissibleCover.boundary`, `AdmissibleCover.nonGenerating`, `AdmissibleCover.nonGenerating_from_inclusions` | `structure` / `def` / `theorem` | coverage family `{ W_i -> W }`、law universe と selected reading を実引数に取る required support / witness / axis、overlap package に相対化した witness / boundary visibility、および admissible cover の5条件と accessor。 | `defined only` / `proved` |
| `II.定義7.1後半 / R4` | `AAT.AG.Site.ContextCategoryObject`, `ContextCategoryObject.of`, `AAT.AG.Site.AATCoverageFamily`, `AATCoverageFamily.toCoverageFamily`, `AATCoverageFamily.presieve`, `AATCoverageFamily.admissibleCover`, `AAT.AG.Site.admissiblePrecoverage`, `AAT.AG.Site.AATGrothendieckTopology`, `AATGrothendieckTopology.top_mem`, `AATGrothendieckTopology.pullback_stable`, `AATGrothendieckTopology.transitive`, `AATGrothendieckTopology.generate_mem`, `AATGrothendieckTopology.eq_coverage_toGrothendieck` | `structure` / `def` / `theorem` | context preorder を Mathlib の thin preorder category に包み、admissible cover family を presieve として生成 precoverage に入れ、その `toGrothendieck` を `J_U` として定義する。Mathlib `Coverage.toGrothendieck` との一致は、admissible precoverage が pullback と base-change stability を持つことを明示前提にした bridge theorem。 | `defined only` / `proved` |
| `II.定義7.2 / 補題7.2A` | `AAT.AG.Site.UAdequacyRequirements`, `AAT.AG.Site.UAdequateCover`, `UAdequateCover.isCover`, `UAdequateCover.support`, `UAdequateCover.witness`, `UAdequateCover.axis`, `UAdequateCover.boundary`, `UAdequateCover.witnessIdeal`, `AAT.AG.Site.RequiredWitnessSubtype`, `AAT.AG.Site.WitnessClosureIndex`, `WitnessClosureIndex.patch`, `AAT.AG.Site.WitnessClosureCover`, `WitnessClosureCover.ClosedIndex`, `WitnessClosureCover.patch`, `WitnessClosureCover.inclusion`, `WitnessClosureCover.toAATCoverageFamily`, `AAT.AG.Site.witnessClosureCover_uAdequate` | `abbrev` / `structure` / `def` / `theorem` | `J_U` cover に required support / witness / axis / boundary visibility と selected reading 上の witness ideal predicate の restriction 保存を追加した `U`-adequate cover。補題7.2A は seed patch、局所有限な required witness subtype、required witness support、seed-boundary overlap branch から生成される closed index を持つ witness-closure cover construction package を明示引数に取り、その package から admissible family を構成する。admissibility と adequacy の boundary 条件は明示された boundary visibility field から得る。 | `defined only` / `proved under explicit WitnessClosureCover package assumptions` |
| `II.定義8.1 / 定義2.1` | `AAT.AG.Site.AATSite`, `AATSite.architectureObject`, `AATSite.category`, `AATSite.topology`, `AATSite.topology_eq`, `AATSite.top_mem`, `AAT.AG.Site.ArchitectureGeometry`, `ArchitectureGeometry.generatedObject`, `ArchitectureGeometry.generatedObject_eq_core`, `ArchitectureGeometry.contextPreorder`, `ArchitectureGeometry.category`, `ArchitectureGeometry.topology`, `ArchitectureGeometry.topology_eq_site` | `structure` / `abbrev` / `def` / `theorem` | `ArchCtx(A)` と `J_U` を束ねる AAT Site package、および PRD-1 の `PartIPrerequisites` / `AATCorePackage` 由来 object に site を載せる Architecture Geometry package。第III部以降の sheaf 群の置き場はコメントに留める。 | `defined only` / `proved` |
| `II.定義9.1 / 定義10.1 / 定義10.2` | `AAT.AG.Site.AATPresheaf`, `AAT.AG.Site.AtRaw`, `AAT.AG.Site.LawRaw`, `AAT.AG.Site.SigRaw`, `AAT.AG.Site.AATSheafConditionFor`, `AAT.AG.Site.AATSheafCondition`, `AATSheafCondition.cover`, `AATSheafCondition.iff_presieve_isSheaf`, `AAT.AG.Site.AATSheaf`, `AATSheaf.toPresheaf`, `AATSheaf.presieve_isSheaf`, `AAT.AG.Site.ArchitectureSheafFamily`, `ArchitectureSheafFamily.At_isSheaf`, `ArchitectureSheafFamily.Law_isSheaf`, `ArchitectureSheafFamily.Sig_isSheaf`, `ArchitectureSheafFamily.State_isSheaf`, `ArchitectureSheafFamily.Eff_isSheaf`, `ArchitectureSheafFamily.Auth_isSheaf`, `ArchitectureSheafFamily.Sem_isSheaf`, `ArchitectureSheafFamily.Trace_isSheaf` | `abbrev` / `structure` / `def` / `theorem` | `ArchCtx(A)^op` 上の Type-valued presheaf、代表的 raw presheaf signature、compatible local sections が一意の global section へ貼り合う sheaf condition、Mathlib `Presieve.IsSheaf` bridge、および `At / Law / Sig / State / Eff / Auth / Sem / Trace` の名前付き sheaf family carrier package。 | `defined only` / `proved` |
| `II.定義11.1 / 定義11.2 / 定義12.1` | `AAT.AG.Site.AATLocalSectionFamily`, `AAT.AG.Site.AATOverlapAgreement`, `AAT.AG.Site.AATCocycleCondition`, `AAT.AG.Site.AATGluingData`, `AATGluingData.cocycle`, `AAT.AG.Site.AATGlobalSectionRealizes`, `AAT.AG.Site.AATDescent`, `AATDescent.exists_global`, `AATSheafConditionFor.descent`, `AATSheafCondition.descent`, `AATSheaf.descent`, `AAT.AG.Site.AATSheafificationComparison`, `AATSheafificationComparison.plus_isSheaf`, `AAT.AG.Site.AATSheafificationGap` | `abbrev` / `structure` / `def` / `theorem` | cover 上の局所 section family、overlap agreement / cocycle condition、gluing data、compatible gluing data が一意の global section から来る descent、sheaf condition から descent を読む補題、および canonical map `F_raw -> F_raw^+` に相対化した sheafification comparison / gap。 | `defined only` / `proved` |
| `II.定義7.2B / 命題7.2C` | `AAT.AG.Site.FinitePosetAATSiteRegime`, `FinitePosetAATSiteRegime.context_index_finite`, `FinitePosetAATSiteRegime.selected_context_le_sound`, `FinitePosetAATSiteRegime.selected_context_le_antisymm`, `FinitePosetAATSiteRegime.cover_index_finite`, `FinitePosetAATSiteRegime.cover_is_uAdequate`, `AAT.AG.Site.FinitePosetCechSimplex`, `FinitePosetCechSimplex.indices`, `FinitePosetCechSimplex.overlap`, `FinitePosetCechSimplex.overlap_le_patch`, `FinitePosetCechSimplex.finite`, `AAT.AG.Site.FinitePosetCechOverlapObject`, `AAT.AG.Site.FinitePosetCechSection`, `AAT.AG.Site.FinitePosetCechCochain`, `AAT.AG.Site.FinitePosetCechFaceData`, `AAT.AG.Site.FinitePosetCechFaceRestriction`, `AAT.AG.Site.FinitePosetCechAdditiveData`, `AAT.AG.Site.FinitePosetCechZeroCochain`, `AAT.AG.Site.FinitePosetCechComplex`, `FinitePosetCechComplex.differential_from_restrictions`, `FinitePosetCechComplex.differential_comp`, `AAT.AG.Site.FinitePosetCechCocycle`, `AAT.AG.Site.FinitePosetCechZeroCocycle`, `AAT.AG.Site.FinitePosetCechBoundaryCocycle`, `AAT.AG.Site.FinitePosetCechBoundaryImage`, `AAT.AG.Site.FinitePosetCechBoundaryCocycle_mem_image`, `AAT.AG.Site.FinitePosetCechCoboundaryRelation`, `FinitePosetCechCoboundaryRelation.kills_differential_image`, `FinitePosetCechCoboundaryRelation.kills_boundary_cocycle`, `AAT.AG.Site.FinitePosetCechCoboundarySetoid`, `AAT.AG.Site.FinitePosetCechCohomology`, `AAT.AG.Site.FinitePosetCechCochainsVanish`, `AAT.AG.Site.FinitePosetCechCohomologyVanishes`, `AAT.AG.Site.FinitePosetNerveDimension`, `AAT.AG.Site.finitePosetCechComplex_finite`, `AAT.AG.Site.finitePosetCechCochains_vanish_above_nerveDimension`, `AAT.AG.Site.finitePosetCechCocycles_vanish_above_nerveDimension`, `AAT.AG.Site.finitePosetCechCohomology_vanishes_above_nerveDimension` | `structure` / `abbrev` / `def` / `theorem` | selected finite context poset、finite witness-closure adequate cover、coefficient presheaf、selected finite nerve simplex と overlap データを束ねる finite poset AAT site regime。Čech cochain は各 nonempty `(n+1)`-fold overlap 上の coefficient section product として定義し、face restriction map、selected alternating-combination surface、`d ∘ d = 0` 付き complex、cocycle kernel、previous differential image としての boundary predicate、その image を zero と同一視する selected kernel/image quotient cohomology、nerve dimension `d` より上の cochain / cocycle / cohomology vanishing を定義・証明する。 | `defined only` / `proved` |
| `II.§13 / R10` | `AAT.AG.Site.AATSh`, `AATSh.toPresheafFunctor`, `AATSh.underlyingPresheaf`, `AATSh.presieve_isSheaf`, `AATSh.aatSheafCondition`, `AATSh.toAATSheaf` | `abbrev` / `def` / `theorem` | `AATSh(A,U,J) = Sh(ArchCtx(A), J_U)` を Mathlib `Sheaf S.topology (Type u)` として定義し、presheaf forgetful functor、Mathlib presieve sheaf condition、AAT sheaf condition、既存 `AATSheaf` carrier package への bridge を公開する。 | `defined only` / `proved` |
| `II.R11 finite model examples` | `AAT.AG.FiniteModel.siteContext`, `FiniteModel.siteContextIdentityMorphism`, `FiniteModel.siteContextPreorder`, `FiniteModel.siteOverlap`, `FiniteModel.siteCoverageRequirements`, `FiniteModel.site`, `FiniteModel.siteBase`, `FiniteModel.siteSingletonCover`, `FiniteModel.siteAdequacyRequirements`, `FiniteModel.siteSingletonCover_uAdequate`, `FiniteModel.site_requiredWitnessSubtype_finite`, `FiniteModel.siteWitnessClosureCover`, `FiniteModel.siteWitnessClosureCover_uAdequate`, `FiniteModel.siteCoefficient`, `FiniteModel.siteNerveSimplex`, `FiniteModel.finitePosetRegime`, `FiniteModel.finitePosetRegime_context_finite`, `FiniteModel.finitePosetRegime_context_meet_left`, `FiniteModel.finitePosetRegime_context_meet_right`, `FiniteModel.finitePosetRegime_context_le_meet`, `FiniteModel.finitePosetRegime_context_antisymm`, `FiniteModel.site_top_mem`, `FiniteModel.finitePosetRegime_nerveDimension_zero`, `FiniteModel.finitePosetCechAdditiveData`, `FiniteModel.finitePosetCechFaceData`, `FiniteModel.finitePosetCechComplex`, `FiniteModel.finitePosetCechCoboundaryRelation`, `FiniteModel.finitePosetRegime_cechComplex_finite`, `FiniteModel.finitePosetRegime_cech_vanishes_above_dimension` | `def` / `theorem` | PRD-1 finite model 上の singleton context/site example。singleton admissible cover、witness-closure adequate cover、selected finite poset regime、top cover membership、degree 0 nerve dimension、selected face restriction / zero-combination data、`d ∘ d = 0` 付き Čech complex、differential image を殺す quotient relation、および positive degree Čech cohomology vanishing theorem を持つ。 | `defined only` / `proved` |

Non-conclusions: この entrypoint は `Formal/AG/Site` が build 対象に入ったことと
PRD-1 依存の入口、定義3.1 Architecture Context、§5 の射 role predicate、
命題4.2 と仮定4.3 の明示仮定 package と pullback lifting property、
coverage family と admissible cover の5条件、admissible cover から生成される `J_U`、
明示された pullback / base-change 前提下の Mathlib coverage bridge、U-adequate cover、
補題7.2A の十分条件、AAT Site、Architecture Geometry、presheaf、sheaf condition bridge、
名前付き sheaf family carrier package、gluing / descent、sheafification comparison / gap、
finite poset cover-relative Čech section product / face restriction differential / differential image quotient cohomology、nerve dimension 上の高次消滅、AAT sheaf category entrypoint、
PRD-1 finite model 上の singleton site example だけを示す。
一般 site の Čech complex、sheaf cohomology 計算、law algebra sheaf の具体構成、非 singleton の finite poset site example はまだ形式化しない。

## AG版AAT Lean形式化 PRD-3 / 第III部 Law Algebra・Obstruction Ideal・Lawful Locus

File: `Formal/AG/LawAlgebra.lean`, `Formal/AG/LawAlgebra/Coordinate.lean`,
`Formal/AG/LawAlgebra/AmbientAlgebra.lean`,
`Formal/AG/LawAlgebra/StructuralRelation.lean`,
`Formal/AG/LawAlgebra/StructureSheaf.lean`,
`Formal/AG/LawAlgebra/WitnessIdeal.lean`,
`Formal/AG/LawAlgebra/IdempotentCollapse.lean`,
`Formal/AG/LawAlgebra/StanleyReisner.lean`,
`Formal/AG/LawAlgebra/ObstructionIdeal.lean`,
`Formal/AG/LawAlgebra/LawfulLocus.lean`,
`Formal/AG/LawAlgebra/Nullstellensatz.lean`,
`Formal/AG/LawAlgebra/AffineChart.lean`,
`Formal/AG/LawAlgebra/Scheme.lean`,
`Formal/AG/LawAlgebra/Correspondence.lean`,
`Formal/AG/LawAlgebra/FiniteExamples.lean`.

PRD-3 [第III部 Law Algebra・Obstruction Ideal・Lawful Locus](lean_ag_part_3_law_algebra_lawful_locus_prd.md) の
R0-R14、AC1-AC22 に対応する entrypoint である。現時点では
`Formal/AG/LawAlgebra` を build 対象へ追加し、context に相対化された coordinate
family と、`FreeCommAlg_k(Coord_X(W))` を Mathlib `MvPolynomial` として読む
definitional bridge、structural relation family、`J_struct`、raw ambient quotient、
restriction-stability 下の quotient 降下補題、明示法則付き raw ambient presheaf
bridge、universe-lifted commutative `k`-algebra-valued presheaf /
sheafification bridge、presentation-stability assumption package、law-indexed violation
witness family、law witness ideal、ideal / point / canonical section pullback に沿った
primary ideal-vanishing encoding、no-cancellation 付き defect representative reading、
finite idempotent coordinate algebra の Boolean 点直積への collapse と flat / Tor /
ideal square / Kähler 消滅 surface、square-free witness regime と
Stanley-Reisner obstruction theorem / invariants surface、local obstruction ideal
sum と restriction / sheaf-image surface、lawful locus と section factorization
surface、Architecture Nullstellensatz statement と NSdepth monotonicity surface
、Affine AAT chart と raw/sheafified representability surface、ringed AAT topos /
architecture scheme / scheme gluing surface、Lawfulness-Ideal Correspondence theorem
package、finite example theorem 群までを Lean 上に置く。

| 本文ラベル | Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- | --- |
| `III.R0` | `Formal.AG.LawAlgebra` entrypoint | `import` | 第III部 LawAlgebra module を `Formal/AG.lean` から import し、PRD-1 `Formal/AG/Atom` と PRD-2 `Formal/AG/Site` の成果物上に立ち上げる。 | `defined only` |
| `III.定義3.1` | `AAT.AG.LawAlgebra.CoordinateLabel`, `AAT.AG.LawAlgebra.ArchitectureCoordinate`, `ArchitectureCoordinate.eval`, `ArchitectureCoordinate.eval_eq_read`, `AAT.AG.LawAlgebra.CoordinateFamily`, `CoordinateFamily.CoordX`, `CoordinateFamily.namespaceLabel`, `CoordinateFamily.localData`, `AAT.AG.LawAlgebra.CoordinateReading`, `CoordinateReading.eval`, `CoordinateReading.eval_eq_read` | `inductive` / `structure` / `abbrev` / `def` / `theorem` | context `W` に相対化された coordinate label、単一 coordinate、coordinate family、係数値 reading。coordinate は局所データから係数 carrier への読みとして扱い、structural relation や law equation はまだ課さない。 | `defined only` / `proved` |
| `III.定義4.1` | `AAT.AG.LawAlgebra.FreeCommAlg`, `AAT.AG.LawAlgebra.FreeTypedCommAlg`, `FreeTypedCommAlg.eq_mvPolynomial`, `FreeTypedCommAlg.coordVar`, `FreeTypedCommAlg.coordVar_eq_X` | `abbrev` / `def` / `theorem` | `FreeCommAlg_k(Coord_X(W))` を `MvPolynomial F.CoordX k` として読む bridge。law witness equation は ambient stage では quotient しない。 | `defined only` / `proved` |
| `III.定義4.2 / 定義4.3 / 条件4.4 / 定義10.1` | `AAT.AG.LawAlgebra.StructuralRelationFamily`, `StructuralRelationFamily.RelStruct`, `StructuralRelationFamily.JStruct`, `StructuralRelationFamily.polynomial_mem_JStruct`, `StructuralRelationFamily.RawAmbientLawAlgebra`, `StructuralRelationFamily.quotientMap`, `StructuralRelationFamily.quotientMap_polynomial_eq_zero`, `AAT.AG.LawAlgebra.TypedCoordinateRestriction`, `TypedCoordinateRestriction.polynomialMap`, `TypedCoordinateRestriction.polynomialMap_X`, `AAT.AG.LawAlgebra.RestrictionStableStructuralRelations`, `RestrictionStableStructuralRelations.quotientDesc`, `RestrictionStableStructuralRelations.quotientDesc_mk`, `AAT.AG.LawAlgebra.RawAmbientPresheafBridge`, `RawAmbientPresheafBridge.rawAlgebra`, `RawAmbientPresheafBridge.res`, `RawAmbientPresheafBridge.identityLaw`, `RawAmbientPresheafBridge.compositionLaw` | `structure` / `def` / `abbrev` / `theorem` | structural relation family `Rel_struct(W)` と生成 ideal `J_struct(W)` を分離し、`O_raw^U(W)` を `FreeTypedCommAlg / J_struct` として定義する。typed coordinate restriction が `J_struct` を保存する仮定の下で quotient に降りることを証明し、定義10.1 の ring restriction surface と identity / composition law を明示フィールドとして持つ raw ambient presheaf bridge を公開する。 | `defined only` / `proved under explicit restriction-stability and presheaf-law assumptions` |
| `III.定義2.1 / 条件4.5` | `AAT.AG.LawAlgebra.AATCommAlgCat`, `AAT.AG.LawAlgebra.AlgebraValuedAATPresheaf`, `AAT.AG.LawAlgebra.LawAlgebraSheaf`, `AAT.AG.LawAlgebra.RawAmbientAlgebraPresheafBridge`, `RawAmbientAlgebraPresheafBridge.toPresheaf`, `RawAmbientAlgebraPresheafBridge.objectIso`, `RawAmbientAlgebraPresheafBridge.restriction_naturality_apply`, `AAT.AG.LawAlgebra.LawAlgebraSheafificationBridge`, `LawAlgebraSheafificationBridge.OX`, `LawAlgebraSheafificationBridge.OXPresheaf`, `LawAlgebraSheafificationBridge.canonicalAt`, `LawAlgebraSheafificationBridge.plus_isSheaf`, `LawAlgebraSheafificationBridge.OX_eq_plus`, `LawAlgebraSheafificationBridge.sheafification_lift_unique`, `AAT.AG.LawAlgebra.SelectedLawAlgebraPresentation`, `AAT.AG.LawAlgebra.PresentationStableAt`, `AAT.AG.LawAlgebra.PresentationStableAATSite`, `PresentationStableAATSite.presentsRaw`, `PresentationStableAATSite.canonicalPreservesGenerators`, `PresentationStableAATSite.canonicalPreservesRelations`, `PresentationStableAATSite.presentsSheafified`, `AAT.AG.LawAlgebra.LawAlgebraSheafPackage`, `LawAlgebraSheafPackage.OX`, `LawAlgebraSheafPackage.raw_eq_rawAmbient`, `LawAlgebraSheafPackage.presentationStableAt` | `abbrev` / `structure` / `def` / `theorem` | `O_X^U = (O_raw^U)^+` を、universe-lifted commutative `k`-algebra-valued presheaf、Mathlib `Sheaf` object、canonical map、sheafification universal property からなる selected sheafification bridge として定義する。raw ambient restriction と presheaf map の自然性を明示し、条件4.5 は selected generator / relation が canonical bridge で保たれる型付き仮定 package として持つ。 | `defined only` / `proved under explicit sheafification-bridge and presentation-stability assumptions` |
| `III.定義5.1 / 定義5.2 / 定義5.3` | `AAT.AG.LawAlgebra.ViolationWitnessFamily`, `ViolationWitnessFamily.LawIndex`, `ViolationWitnessFamily.law`, `ViolationWitnessFamily.coordinateSet`, `AAT.AG.LawAlgebra.LawWitnessIdeal`, `LawWitnessIdeal.coordinate_mem`, `AAT.AG.LawAlgebra.LawWitnessPoint`, `AAT.AG.LawAlgebra.LawWitnessIdealVanishesAtIdeal`, `AAT.AG.LawAlgebra.LawWitnessIdealVanishesAtPoint`, `AAT.AG.LawAlgebra.LawWitnessSectionPullback`, `LawWitnessSectionPullback.pullback`, `LawWitnessSectionPullback.pulledIdeal`, `LawWitnessSectionPullback.Vanishes`, `AAT.AG.LawAlgebra.DefectRepresentativeReading`, `DefectRepresentativeReading.Vanishes`, `DefectRepresentativeReading.noCancellation_of_vanishes` | `structure` / `def` / `theorem` | law-indexed violation witness family `Viol_L(W)`、対応する coordinate set、生成 ideal `I_L(W)`、ideal support に沿った `I_L(W) ⊆ p`、point condition を持つ point support、canonical `O_raw^U(W) -> O_X^U(W)` bridge 経由の section pullback に沿った `s^* I_L = 0` を primary encoding として定義する。代表元 `δ_L` による `s^*(δ_L)=0` の読みは no-cancellation 条件を持つ別 surface として分離する。 | `defined only` / `proved for accessor lemma` |
| `III.補題5.6A` | `AAT.AG.LawAlgebra.BoolPoint`, `AAT.AG.LawAlgebra.IdempotentCollapse.boolValue`, `IdempotentCollapse.booleanEval`, `IdempotentCollapse.booleanRelation`, `IdempotentCollapse.booleanIdeal`, `IdempotentCollapse.IdempotentAlgebra`, `IdempotentCollapse.booleanIdeal_eq_ker`, `IdempotentCollapse.booleanEval_surjective`, `IdempotentCollapse.quotientAlgEquivPi`, `IdempotentCollapse.quotientRingEquivPi`, `IdempotentCollapse.module_projective`, `IdempotentCollapse.module_flat`, `IdempotentCollapse.isZero_Tor_succ`, `IdempotentCollapse.ideal_mul_self`, `IdempotentCollapse.ideal_square_comap_eq_top`, `IdempotentCollapse.kaehler_subsingleton` | `abbrev` / `def` / `theorem` / `instance` | finite coordinate set `E` と field `k` に対し、`k[x_e]/<x_e^2-x_e>` を Boolean points `E -> Bool` 上の finite product `BoolPoint E -> k` へ `AlgEquiv` で collapse する。semisimple ring 経由で全 module projective / flat、Mathlib `Tor` の projective 消滅 API で higher Tor zero、ideal idempotence により `I/I²=0` の top 条件、`FormallyUnramified` 経由で `Ω_{A/k}=0` を与える。 | `proved` |
| `III.定義5.6B / 定理5.6C / 系5.6D` | `AAT.AG.LawAlgebra.StanleyReisner.squareFreeMonomial`, `StanleyReisner.SquareFreeWitnessRegime`, `SquareFreeWitnessRegime.obstructionIdeal`, `SquareFreeWitnessRegime.AdmissibleSupport`, `SquareFreeWitnessRegime.AbstractSimplicialComplex`, `SquareFreeWitnessRegime.delta`, `SquareFreeWitnessRegime.stanleyReisnerIdeal`, `SquareFreeWitnessRegime.coordinateSubspaceArrangement`, `SquareFreeWitnessRegime.flatChart`, `SquareFreeWitnessRegime.obstructionIdeal_eq_stanleyReisnerIdeal`, `SquareFreeWitnessRegime.obstructionIdeal_eq_stanleyReisnerIdeal_of_minimal`, `SquareFreeWitnessRegime.minimalReduction_obstructionIdeal_eq`, `SquareFreeWitnessRegime.radical_minimalReduction_obstructionIdeal_eq`, `SquareFreeWitnessRegime.face_iff_admissibleSupport`, `SquareFreeWitnessRegime.minimalGeneratorSupport_iff_minimalForbidden` | `structure` / `def` / `theorem` | square-free witness regime `Forb` と monomial obstruction ideal、`Finset` ベースの abstract simplicial complex `Delta_U(W)`、Stanley-Reisner ideal、coordinate subspace arrangement `V(I_Delta)` を定義する。非 face monomial が forbidden monomial の倍元になることから `I_Ob = I_Delta` を証明し、minimal family wrapper、finite witness 型での minimal reduction exact ideal equality / radical equality、minimal generator support と minimal forbidden support の一致、face と admissible support の一致を与える。 | `defined only` / `proved` |
| `III.定義6.1 / 定義6.2 / 定義10.2` | `AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily`, `SelectedLawWitnessIdealFamily.selectedElementSet`, `SelectedLawWitnessIdealFamily.localObstructionIdeal`, `SelectedLawWitnessIdealFamily.witnessIdeal_le_localObstructionIdeal`, `SelectedLawWitnessIdealFamily.localObstructionIdeal_le_iff`, `SelectedLawWitnessIdealFamily.RestrictionCompatible`, `SelectedLawWitnessIdealFamily.map_localObstructionIdeal_le`, `SelectedLawWitnessIdealFamily.SheafImageConstruction`, `SheafImageConstruction.imageIdeal_eq_localObstructionIdeal`, `SheafImageConstruction.localObstructionIdeal_eq_imageIdeal` | `structure` / `def` / `theorem` | selected law witness ideal family の和として local obstruction ideal `I_Ob^U(W)` を定義する。選択された各 `I_L(W)` が local sum に入ること、local sum の最小性、restriction map が selected ideals を target selected ideals へ送る仮定の下で `I_Ob` が restriction-compatible になること、sheaf-image construction が local sum 表示と一致する範囲を明示する。 | `defined only` / `proved under explicit restriction-compatibility and sheaf-image agreement assumptions` |
| `III.定義7.1 / 定義7.2` | `AAT.AG.LawAlgebra.LawfulLocus.lawfulLocus`, `LawfulLocus.localLawfulLocus`, `LawfulLocus.LawfulSectionData`, `LawfulSectionData.pulledObstructionIdeal`, `LawfulSectionData.Lawful`, `LawfulSectionData.FactorsThroughLawfulLocus`, `LawfulSectionData.lawful_iff_pulledObstructionIdeal_eq_bot`, `LawfulSectionData.factorsThroughLawfulLocus_of_lawful`, `LawfulSectionData.lawful_of_factorsThroughLawfulLocus`, `LawfulSectionData.lawful_iff_factorsThroughLawfulLocus`, `LawfulLocus.LocalLawfulSectionData` | `structure` / `def` / `theorem` | lawful locus `Flat_U(X) = V(I_Ob^U)` を `PrimeSpectrum.zeroLocus` として定義し、section pullback に沿った `s^* I_Ob^U = 0` を lawfulness とする。factorization through lawful locus は同じ vanishing condition を保持する package として置き、lawful section と factorization の同値を証明する。 | `defined only` / `proved` |
| `III.定理候補7.2A / 定義7.2B / 命題7.2C` | `AAT.AG.LawAlgebra.Nullstellensatz.booleanLawIdeal`, `Nullstellensatz.VanishesAtIdeal`, `Nullstellensatz.BooleanLawZeroSetEmpty`, `Nullstellensatz.ArchitectureNullstellensatzCandidate`, `Nullstellensatz.RadicalUnitCertificate`, `Nullstellensatz.UnlawfulnessCertificate`, `Nullstellensatz.HasCertificateAt`, `Nullstellensatz.NSdepthProfile`, `NSdepthProfile.NSdepth`, `NSdepthProfile.GeneratorExtension`, `NSdepthProfile.NSdepth_mono_of_generatorExtension` | `def` / `structure` / `theorem` | Boolean law ideal `I_U(W)+B_W`、Boolean law zero set empty、radical unit certificate を用いて Architecture Nullstellensatz candidate を statement-only `Prop` として定義する。NSdepth は certificate availability profile の最小次数として package 化し、generator extension が certificate を同次数で保存する仮定から `NSdepth_new ≤ NSdepth_old` を証明する。 | `statement only` / `defined only` / `proved` |
| `III.定義8.1 / 定義8.2 / 定義8.5 / 定理8.3 / 仮定8.4` | `AAT.AG.LawAlgebra.AffineChart.SpecAAT`, `SpecAAT.pointSpace`, `SpecAAT.localLawfulChart`, `AffineChart.AffineAATChart`, `AffineAATChart.hWU`, `AffineAATChart.rawAffineChartRepresentability`, `AffineAATChart.RawAffinePresentation`, `RawAffinePresentation.CoordinateAssignment`, `RawAffinePresentation.assignmentAlgHom`, `RawAffinePresentation.assignmentAlgHom_X`, `RawAffinePresentation.SatisfiesStructuralRelations`, `RawAffinePresentation.hWUConfiguration`, `RawAffinePresentation.assignmentAlgHom_eq_zero_of_mem_JStruct`, `RawAffinePresentation.quotientAlgHomOfConfiguration`, `RawAffinePresentation.quotientAlgHomOfConfiguration_mk`, `RawAffinePresentation.configurationOfQuotientAlgHom`, `RawAffinePresentation.rawQuotientRepresentability`, `RawAffinePresentation.hWUConfigurationRepresentability`, `AffineChart.AffineAATChart.SheafifiedChartPresentation`, `AffineAATChart.sheafifiedChartRepresentability` | `structure` / `abbrev` / `def` / `theorem` | `Spec_AAT(A,D)` を ordinary `PrimeSpectrum A` と decoration / obstruction ideal の package として定義する。既存 `hWU` は chosen coordinate algebra からの selected `k`-Alg Hom surface として残し、`RawAffinePresentation` が typed coordinate assignment、structural relation satisfaction、`MvPolynomial.aeval`、`Ideal.Quotient.liftₐ` による raw quotient algebra hom の同値を公開する。仮定8.4 は sheafified chart presentation package と、その下での selected representability surface として扱う。 | `defined only` / `proved for raw quotient representability and under selected presentation assumptions` |
| `III.定義9.1 / 定義9.2 / 定義9.3 / 定義10.3` | `AAT.AG.LawAlgebra.Scheme.RingedAATTopos`, `RingedAATTopos.OX`, `RingedAATTopos.forgetfulLocallyRingedSpace`, `RingedAATTopos.forgetfulLocallyRingedSpace_eq`, `AAT.AG.LawAlgebra.Scheme.ChartCompatibility`, `ChartCompatibility.allConditions`, `AAT.AG.LawAlgebra.Scheme.ArchitectureScheme`, `ArchitectureScheme.forgetfulLocallyRingedSpace`, `ArchitectureScheme.forgetful_reading_locallyRingedSpace`, `ArchitectureScheme.ringedTopos_forgetful_eq_underlying`, `AAT.AG.LawAlgebra.Scheme.SchemeGluingData`, `AAT.AG.LawAlgebra.Scheme.AffineReturnConditions`, `AffineReturnConditions.affineReturnAssumptions` | `structure` / `def` / `theorem` | ringed AAT topos を既存 `Site.AATSh S` object / `LawAlgebraSheafPackage S k` の `O_X^U` / Mathlib `LocallyRingedSpace` の package として定義する。chart compatibility は 7条件の Prop package とし、architecture scheme は chart-compatible atlas と decorated locally ringed geometry の selected package とする。forgetful reading は Mathlib `LocallyRingedSpace` へ戻る bridge theorem として固定する。scheme gluing は chart gluing data、underlying Mathlib gluing bridge predicate、単一 affine chart へ戻るための glued affine / canonical ring comparison / `O_X^U(W)` と glued global sections の comparison / decoration 同定の明示仮定までに限定する。 | `defined only` / `proved for forgetful bridge` |
| `III.定理11.1` | `AAT.AG.LawAlgebra.Correspondence.LawfulnessIdealCorrespondenceAssumptions`, `LawfulnessIdealCorrespondenceAssumptions.lawful_iff_semanticLawfulness`, `LawfulnessIdealCorrespondenceAssumptions.lawful_iff_omegaU_zero`, `LawfulnessIdealCorrespondenceAssumptions.lawful_iff_requiredSignatureAxesZero`, `AAT.AG.LawAlgebra.Correspondence.LawfulnessIdealCorrespondencePackage`, `Correspondence.lawful_iff_pulledObstructionIdeal_eq_bot`, `Correspondence.pulledObstructionIdeal_eq_bot_iff_factorsThroughLawfulLocus`, `Correspondence.factorsThroughLawfulLocus_iff_omegaU_zero`, `Correspondence.omegaU_zero_iff_requiredSignatureAxesZero`, `Correspondence.lawfulnessIdealCorrespondence` | `structure` / `theorem` / `def` | obstruction soundness / completeness、axis exactness、witness coverage、U-adequate cover、`Ob_U` sheaf descent、ring restriction compatibility を明示仮定として持ち、`Lawful_U(s)`、`s^* I_Ob^U = 0`、`s` factors through `Flat_U(X)`、PRD-1 `omegaU = 0`、PRD-1 `RequiredSignatureAxesZero` の5項同値を edge theorem と theorem package として公開する。 | `proved under explicit correspondence assumptions` |
| `III.例5.6E / 例7.2D / R13 finite examples` | `AAT.AG.LawAlgebra.FiniteExamples.StanleyReisnerChart.regime`, `StanleyReisnerChart.xy_forbidden`, `StanleyReisnerChart.obstructionIdeal_eq_span_xy`, `StanleyReisnerChart.obstructionIdeal_eq_stanleyReisnerIdeal`, `StanleyReisnerChart.z_face`, `StanleyReisnerChart.xy_not_face`, `AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.one_eq_x_sub_x_minus_one`, `NSdepthExample.one_mem_x_sup_xMinusOne`, `NSdepthExample.UnitCertificate`, `NSdepthExample.unitCertificate`, `NSdepthExample.hasUnitCertificateAt_one`, `NSdepthExample.nsdepthOneProfile`, `NSdepthExample.nsdepth_eq_one`, `AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cycleCoordinate`, `CycleCorrespondenceExample.cycleIdeal`, `CycleCorrespondenceExample.cycleCoordinate_mem_cycleIdeal`, `CycleCorrespondenceExample.cycleWitnessIdealFamily`, `CycleCorrespondenceExample.localObstructionIdeal_eq_cycleIdeal`, `CycleCorrespondenceExample.acyclicSectionData`, `CycleCorrespondenceExample.cyclicSectionData`, `CycleCorrespondenceExample.acyclic_pulledObstructionIdeal_eq_bot`, `CycleCorrespondenceExample.cyclic_pulledObstructionIdeal_eq_top`, `CycleCorrespondenceExample.acyclic_pulled_lawful_locus_has_point`, `CycleCorrespondenceExample.cyclic_pulled_lawful_locus_no_point`, `CycleCorrespondenceExample.acyclicObject`, `CycleCorrespondenceExample.cyclicObject`, `CycleCorrespondenceExample.acyclicCorrespondencePackage`, `CycleCorrespondenceExample.cyclicCorrespondencePackage` | `def` / `theorem` | `E_W = {x,y,z}`、`Forb = {{x,y}}` の Stanley-Reisner chart、`I_Ob = <xy>`、faces/nonfaces、`I=<x>` と `B=<x-1>` の `1 = x - (x-1)` concrete certificate から生成される `NSdepth = 1` profile、cycle witness coordinate `c_ABC` と `I_cycle = <c_ABC>`、acyclic / cyclic pullback による lawful locus の点あり/なし、定理11.1 の acyclic / cyclic finite package を example theorem として公開する。 | `proved examples` |

Non-conclusions: この entrypoint は coordinate と free typed commutative algebra の
bridge、structural quotient、restriction descent bridge、law algebra sheafification
bridge、law witness ideal、defect representative reading、idempotent coordinate collapse、
square-free local obstruction ideal と Stanley-Reisner chart reading、selected law
ideal sum と sheaf-image 表示、lawful locus / lawful section factorization、ringed
AAT topos / architecture scheme / scheme gluing surface、明示仮定下の
Lawfulness-Ideal Correspondence theorem package、selected finite examples だけを示す。
Nullstellensatz candidate は statement-only であり、証明昇格はしない。

## AG版AAT Lean形式化 PRD-4 / 第IV部 Obstruction Cohomology

File: `Formal/AG/Cohomology.lean`, `Formal/AG/Cohomology/Basic.lean`,
`Formal/AG/Cohomology/ObstructionSheaf.lean`,
`Formal/AG/Cohomology/CechComplex.lean`,
`Formal/AG/Cohomology/Cohomology.lean`,
`Formal/AG/Cohomology/FinitePosetComparison.lean`,
`Formal/AG/Cohomology/GluingMismatch.lean`,
`Formal/AG/Cohomology/LocalFlatnessGap.lean`,
`Formal/AG/Cohomology/BoundaryHolonomy.lean`,
`Formal/AG/Cohomology/BoundaryResidue.lean`,
`Formal/AG/Cohomology/HigherOverlap.lean`,
`Formal/AG/Cohomology/FlatnessCriterion.lean`,
`Formal/AG/Cohomology/CoverNerve.lean`,
`Formal/AG/Cohomology/FiniteExamples.lean`,
`Formal/AG/Cohomology/PeriodStokes.lean`,
`Formal/AG/Cohomology/Aggregation.lean`.

PRD-4 [第IV部 Obstruction Cohomology](lean_ag_part_4_obstruction_cohomology_prd.md)
の AC1/R0 から AC16/R12 までに対応する entrypoint である。現時点では
`Formal/AG/Cohomology` を build 対象へ追加し、PRD-2 `Site` と PRD-3
`LawAlgebra` への prerequisite package、obstruction coefficient sheaf carrier、
`O_X^U`-module valued coefficient surface、`Def_U = I_U`、`ConDef_U = I_U/I_U^2`
の Mathlib `Ideal.Cotangent` bridge、`i_* ConDef_U` の selected pushforward
carrier boundary、`DerOb_U` の type-signature-only placeholder、一般 AAT site 上の
cover-relative Cech complex package、`d ∘ d = 0` witness、positive degree
`ker d / im d` quotient、条件付き `H^n(X, Ob_U)` notation package、PRD-2
finite-poset surface を明示 comparison data の下で PRD-4 comparison target として
読む package、local lawful section data、parameterized gluing mismatch、
pseudo-torsor 正規化による cocycle 自動成立補題、descent obstruction class
`[g] in H^1(𝒰, Ob_U)`、hidden coupling class、compatible global lawful
section から coboundary / zero class を得る step、および Local Flatness Gap
の対偶 theorem、2-chart feature-extension cover、boundary mismatch section、
selected Čech-level connecting homomorphism、boundary holonomy class、および
明示仮定ブロック下の Boundary Residue theorem、triple-overlap coherence
failure `H^2` class、低次五項完全列形の theorem-candidate statement、
effective abelian torsor surface、Cohomological Flatness Criterion と
Local-to-Global Flatness corollary、cover nerve と明示的な有限次元 accounting data 下の
rank-nullity lower bound / constant coefficient nerve reading / forest vanishing /
Euler invariance、擬円周 golden example の H0/H1 分離と local-flatness-gap 型の
global section 不存在 theorem、Boundary Residue 両方向例と forest / cycle nerve
finite examples、period Stokes theorem と extension holonomy accounting convention
、aggregation / scale-stable debt statement surface までを Lean 上に置く。

| 本文ラベル | Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- | --- |
| `IV.R0` | `AAT.AG.Cohomology.PartIVPrerequisites`, `PartIVPrerequisites.sitePrerequisites`, `PartIVPrerequisites.selectedAffineChart`, `PartIVPrerequisites.site_architectureObject_eq` | `structure` / `def` / `theorem` | 第IV部 obstruction-cohomology tower が PRD-2 site surface と PRD-3 law-algebra surface の上に立つことを記録する bootstrap package。obstruction sheaf、Cech complex、cohomology group はまだ定義しない。 | `defined only` / `proved accessor` |
| `IV.定義2.1 / 定義2.2` | `AAT.AG.Cohomology.ObstructionSheaf`, `AAT.AG.Cohomology.Ob_U`, `AAT.AG.Cohomology.ModuleObstructionSheaf`, `AAT.AG.Cohomology.OXModuleOb_U` | `structure` / `abbrev` | PRD-2 Type-valued AAT sheaf carrier に abelian group structure を添えた obstruction coefficient sheaf と、PRD-3 `O_X^U(W)` section ring 上の module-valued coefficient surface。 | `defined only` |
| `IV.定義2.4` | `AAT.AG.Cohomology.StandardObstruction.Def_U`, `StandardObstruction.LawfulLocusAlgebra`, `StandardObstruction.ConDef_U`, `StandardObstruction.conDefModule`, `StandardObstruction.toConDef`, `StandardObstruction.PushforwardConDef`, `StandardObstruction.CanonicalPackage`, `CanonicalPackage.defU`, `CanonicalPackage.conDefU`, `CanonicalPackage.defU_eq_localObstructionIdeal`, `CanonicalPackage.pushforwardCarrier`, `StandardObstruction.DerOb_U` | `def` / `abbrev` / `instance` / `structure` / `theorem` / `opaque` | PRD-3 `SelectedLawWitnessIdealFamily.localObstructionIdeal` を `Def_U := I_U` として読み、`ConDef_U := I_U/I_U^2` を Mathlib `Ideal.Cotangent` で公開する。`ConDef_U` は lawful-locus quotient `O_X^U/I_U` 上の module として扱い、`i_* ConDef_U` は別 carrier として区別する。`DerOb_U` は型シグネチャのみで、第V部へ委譲する。 | `defined only` / `proved accessor` |
| `IV.定義3.1-3.3` | `AAT.AG.Cohomology.CoverRelativeCechCover`, `CoverRelativeCechCochain`, `CoverRelativeCechComplex`, `CoverRelativeCechComplex.Cn`, `CoverRelativeCechComplex.d`, `CoverRelativeCechComplex.faceRestrictionTerm`, `CoverRelativeCechComplex.d_eq_alternatingFaceCombination`, `CoverRelativeCechComplex.d_comp_d_eq_zero`, `CoverRelativeCechComplex.FinitePosetComparisonTarget` | `structure` / `def` / `abbrev` / `theorem` | 一般 AAT site 上の cover-relative Cech cover、n-simplex overlap section product としての cochain、face restriction term、選択された alternating face-combination に一致する differential package、`d ∘ d = 0` witness、および PRD-2 finite-poset comparison theorem の typed target。 | `defined only` / `proved accessor` |
| `IV.定義4.1` | `AAT.AG.Cohomology.CoverRelativeCechComplex.CechCocycle`, `CechCoboundarySetoidSucc`, `CechCohomologySucc`, `CechCohomologyZero`, `CoverRelativeHn`, `cohomologyClassSucc`, `CechToSheafComparisonHypothesis`, `RefinementSystemHypothesis`, `SpaceCohomologyNotationJustification`, `ConditionalSpaceCohomology`, `ConditionalSpaceCohomology.HnX`, `ConditionalSpaceCohomology.HnX_eq_coverRelative` | `def` / `abbrev` / `structure` / `inductive` / `theorem` | cover-relative `H^n(𝒰, Ob_U)` を一次対象として置き、positive degree は cocycle kernel を previous differential image で割る quotient として読む。`H^n(X, Ob_U)` は Cech-to-sheaf comparison または refinement system を明示する条件付き notation package に限る。 | `defined only` / `proved accessor` |
| `IV.R2 finite-poset comparison` | `AAT.AG.Cohomology.finitePosetCoverRelativeCover`, `FinitePosetCechComparisonData`, `FinitePosetCechComparisonData.generalComplex`, `FinitePosetCechComparisonData.comparisonTarget`, `FinitePosetCechComparisonData.cochain_to_from`, `FinitePosetCechComparisonData.differential_compatible`, `FinitePosetCechComparisonData.cohomology_target_eq`, `FinitePosetCechComparisonData.cohomology_to_from`, `FinitePosetCechComparisonData.cohomology_from_to` | `def` / `structure` / `theorem` | PRD-2 finite poset Cech complex から PRD-4 cover-relative cover を作り、明示された coefficient / additive / cochain equivalence / quotient relation data の下で PRD-4 `FinitePosetComparisonTarget` として読む。differential compatibility、finite-poset cohomology target、selected cohomology maps の round-trip laws を accessor theorem として公開する。 | `proved under explicit comparison data` |
| `IV.定義5.1-5.3 / 原則5.2A` | `AAT.AG.Cohomology.LocalFlatnessData`, `LocalFlatnessData.factorsThroughFlat_U`, `LocalFlatnessData.pulledObstructionIdeal_eq_bot`, `RestrictedLocalLawfulSection`, `RestrictedLocalLawfulSection.factorsThroughFlat_U`, `GluingMismatchData`, `GluingMismatchData.value`, `GluingMismatchData.gluingMismatchCochain`, `GluingMismatchData.gluingMismatchCochain_apply`, `GluingMismatchData.leftRestriction_holds`, `GluingMismatchData.rightRestriction_holds`, `PseudoTorsorNormalizedMismatch`, `PseudoTorsorNormalizedMismatch.readMismatch_gluingMismatch`, `PseudoTorsorNormalizedMismatch.triple_mismatch_sum_zero`, `PseudoTorsorNormalizedMismatch.gluingMismatch_cocycle`, `descentCocycle`, `descentObstructionClass`, `descentObstructionClassOfPseudoTorsor` | `structure` / `def` / `theorem` | PRD-3 lawful section surface に基づく local flatness data、overlap 上の selected restricted lawful section、選択された比較写像による gluing mismatch cochain、abelian pseudo-torsor 正規化で mismatch cochain が `g_ij = s_j - s_i` 型の差分 carrier へ読まれ、triple-overlap sum が消えること、および既存 cover-relative `H^1(𝒰, Ob_U)` に入る descent obstruction class を定義する。Čech differential が triple sum zero を cocycle に読む方向は selected package の明示 field に相対化する。 | `defined only` / `proved accessor` |
| `IV.定義6.1 / 6.2 / 定理7.1` | `AAT.AG.Cohomology.h1ZeroCocycle`, `h1ZeroClass`, `HiddenCouplingData`, `HiddenCouplingData.hiddenCouplingCocycle`, `HiddenCouplingData.hiddenCouplingClass`, `CompatibleGlobalLawfulSection`, `CompatibleGlobalLawfulSection.globalFactorsThroughFlat_U`, `GlobalSectionCoboundarySoundness`, `GlobalSectionCoboundarySoundness.hiddenCouplingClass_eq_zero`, `LocalFlatnessGapHypotheses`, `localFlatnessGap_no_globalLawfulSection` | `def` / `structure` / `theorem` | R4 の descent obstruction class を hidden coupling cocycle / class として読む。U-adequate cover・global lawful section・local restriction compatibility を持つ compatible global lawful section を statement-level object とし、global section から coboundary witness を得る soundness は明示 hypothesis として分離する。定理7.1 は hidden coupling class 非零なら compatible global lawful section は存在しない、という対偶 theorem として証明する。 | `proved under explicit compatibility data` |
| `IV.定義8.1-8.3 / 9.1` | `AAT.AG.Cohomology.TwoChartFeatureExtensionCover`, `TwoChartFeatureExtensionCover.boundaryObject`, `TwoChartFeatureExtensionCover.extensionObject`, `BoundaryCoefficient`, `CoreCoefficient`, `FeatureCoefficient`, `BoundaryMismatchSection`, `BoundaryMismatchSection.b_U`, `TwoChartCechBoundaryComplex`, `TwoChartCechBoundaryComplex.C0`, `TwoChartCechBoundaryComplex.C1`, `TwoChartCechBoundaryComplex.d0`, `TwoChartCechBoundaryComplex.d0_apply`, `TwoChartConnectingHomomorphism`, `TwoChartConnectingHomomorphism.delta`, `TwoChartConnectingHomomorphism.delta_eq_boundaryRestrictionSource`, `TwoChartConnectingHomomorphism.deltaCocycle`, `TwoChartConnectingHomomorphism.deltaClass`, `TwoChartConnectingHomomorphism.deltaH1`, `TwoChartConnectingHomomorphism.deltaH1_eq_deltaClass`, `TwoChartConnectingHomomorphism.boundaryHolonomy`, `TwoChartConnectingHomomorphism.boundaryHolonomy_eq_delta` | `structure` / `abbrev` / `def` / `theorem` | 2-chart feature-extension cover `C' = C_core ∪ F` と boundary `B = C_core ∩ F` を selected cover data として記録し、`C^0 = Ob(C_core) × Ob(F)`、`C^1 = Ob(B)`、boundary differential `s_F|_B - s_core|_B`、boundary mismatch section `b_U ∈ H^0(B, Ob_B)`、selected Čech-level cochain map と selected class-level connecting homomorphism `δ : H^0(B, Ob_B) -> H^1(C', Ob_C')`、boundary holonomy `Hol_U = δ(b_U)` を既存 cover-relative Čech complex 上に置く。この AC8 surface 自体は derived Mayer-Vietoris triangle や定理9.2 を主張しない。 | `defined only` / `proved accessor` |
| `IV.定理9.2` | `AAT.AG.Cohomology.BoundaryHolonomyVanishes`, `BoundaryResidueHypotheses`, `BoundaryResidueHypotheses.boundaryResidueSoundness`, `BoundaryResidueHypotheses.boundaryResidueCompleteness`, `BoundaryResidueHypotheses.globallyUFlat`, `BoundaryResidueHypotheses.boundaryWitnessCoverage_holds`, `BoundaryResidueHypotheses.boundaryResidueTheorem`, `BoundaryResidueHypotheses.globallyUFlat_of_boundaryHolonomy_zero`, `BoundaryResidueHypotheses.boundaryHolonomy_zero_of_globallyUFlat` | `def` / `structure` / `theorem` | `C_core / F` の U-flatness、boundary witness coverage、axis exactness、boundary-exact 係数、ring restriction compatibility、effective torsor/module descent、holonomy completeness、NoHigherBoundaryObstruction を明示 field として持つ hypothesis block の下で、soundness / completeness data から selected global U-flatness と `Hol_U = 0` の同値を証明する。仮定なしの global criterion ではない。 | `proved under explicit Boundary Residue hypotheses` |
| `IV.定義10.1 / 定理候補10.4` | `AAT.AG.Cohomology.TripleOverlapCoherenceFailure`, `TripleOverlapCoherenceFailure.hCocycle`, `TripleOverlapCoherenceFailure.hClass`, `LowDegreeFiveTermData`, `LowDegreeFiveTermData.FiveTermExact`, `LowDegreeFiveTermData.FiveTermStatement`, `LowDegreeFiveTermData.fiveTermExact_of_statement` | `structure` / `def` / `theorem` | triple-overlap coherence failure を degree-two Čech cocycle `h` と class `[h] in H^2(𝒰, Ob_U)` として定義し、定理候補10.4 は既存 cover-relative Čech complex に相対化された finite-cover Čech filtration provenance 付きの低次五項完全列 statement shape として `Prop` に記録する。一般スペクトル系列機構や statement の証明は構成しない。 | `statement only` / `defined only` / `proved accessor` |
| `IV.定理11.1 / 系11.2` | `AAT.AG.Cohomology.H1ClassVanishes`, `GluingObstructionClass`, `GluingObstructionClass.h1Class`, `GluingObstructionClass.h1Class_eq`, `EffectiveAbelianObstructionTorsor`, `CohomologicalFlatnessCriterionHypotheses`, `CohomologicalFlatnessCriterionHypotheses.cohomologicalFlatnessCriterion`, `CohomologicalFlatnessCriterionHypotheses.adjustedGlobalLawfulSection_of_h1Class_zero`, `CohomologicalFlatnessCriterionHypotheses.noAdjustedGlobalLawfulSection_of_h1Class_nonzero`, `CohomologicalFlatnessCriterionHypotheses.localToGlobalFlatness` | `def` / `structure` / `theorem` | gluing obstruction を concrete cocycle `g` の class `[g] in H^1(𝒰, Ob_U)` として読み、effective abelian torsor、local flatness、abelian coefficients、U-adequate cover、soundness / completeness、axis exactness、witness coverage、descent、effective adjustment を明示 field とする仮定ブロックの下で、torsor triviality を経由して `[g]=0` と調整後の大域 lawful section の同値を証明し、`[g]≠0` なら調整後の大域 lawful section が存在しないこと、および local-to-global flatness を証明する。abelianization が non-abelian torsor の自明性を復元するとは主張しない。 | `proved under explicit Cohomological Flatness hypotheses` |
| `IV.定義12.1 / 定理12.2 / 系12.3 / 定理12.4 / 系12.5` | `AAT.AG.Cohomology.CoverNerve`, `CoverNerve.ParallelEdgeComponents`, `CoverNerve.ParallelFaceComponents`, `CoverNerve.edge_component_selected`, `CoverNerve.face_component_selected`, `FiniteDimensionalNerveCohomologyData`, `FiniteDimensionalNerveCohomologyData.topologicalDebtCapacity`, `ConstantCoefficientNerveReading`, `ConstantCoefficientNerveReading.h1_equiv`, `ConstantCoefficientNerveReading.dimSpace_eq_dimNerve`, `ConstantCoefficientNerveReading.dimH1_eq_b1`, `ForestCoverGluingData`, `ForestCoverGluingData.localGluingSufficiency`, `ForestCoverGluingData.localGluingSufficiency_subsingleton`, `EulerCochainAccounting`, `EulerCochainAccounting.eulerAccounting`, `EulerCochainAccounting.ShapeStalkPreservingRefactor`, `EulerCochainAccounting.chi_invariant_under_refactor` | `structure` / `def` / `theorem` | cover nerve を chart 頂点、pairwise-overlap component 辺、triple-overlap component 面として定義し、多重 edge / face component を許す。有限 poset regime と有限次元 `k`-linear coefficient accounting data の下で `dim C^1 <= dim H^1 + dim C^0 + dim C^2` を証明し、定数係数の `k`-linear comparison data から `H^1(U,k) ≃ₗ[k] H^1(N(U),k)` と `dim H^1(U,k) = b_1(N(U))` を読む。forest / no triple faces / surjective restrictions から tree-induction absorption data を通じて selected `H^1` の全 class が `0` になること、shape/stalk-preserving refactor が Euler characteristic を保つことを証明する。 | `proved under explicit finite-dimensional accounting data` |
| `IV.R10(a) / AC13` | `AAT.AG.Cohomology.FiniteExamples.PseudoCircleGolden.Chart`, `BoundaryEdge`, `edgeLeft`, `edgeRight`, `coverNerve`, `LocallyLawful`, `each_chart_lawful`, `witnessCountingObstruction`, `h0_witness_counting_sees_no_obstruction`, `BoundaryMismatchValue`, `boundaryCocycle`, `boundaryCocycle_AB_nonzero`, `CoverRelativeH1NonzeroWitness`, `CoverRelativeH1NonzeroWitness.concreteClass_nonzero`, `no_global_lawful_section_by_localFlatnessGap`, `pseudoCircle_h0_invisible_h1_obstructed` | `inductive` / `def` / `structure` / `theorem` | ArchSig v0.4.0 R14 golden fixture に対応する selected 擬円周 boundary model。各 chart は locally lawful、H0 的 witness count は zero、finite boundary cocycle は visibly nonzero。`CoverRelativeH1NonzeroWitness` が concrete `K.CechCocycle 1` と既存 `HiddenCouplingData.hiddenCouplingClass : K.CoverRelativeHn 1` を接続し、その actual cover-relative H1 class 非零から既存 `localFlatnessGap_no_globalLawfulSection` を呼んで compatible global lawful section 不在を証明する。 | `proved finite example under explicit cover-relative H1 witness` |
| `IV.R10(b)(c) / AC14` | `AAT.AG.Cohomology.FiniteExamples.BoundaryResidueGolden.zero_boundaryResidue_glues`, `BoundaryResidueGolden.nonzero_boundaryResidue_blocks_gluing`, `BoundaryResidueGolden.boundaryResidue_two_direction_example`, `NerveGolden.forestCoverNerve`, `NerveGolden.forestCoverGluingData`, `NerveGolden.forestCover_H1_zero`, `NerveGolden.cycleCoverNerve`, `NerveGolden.cycleConstantCoefficientReading`, `NerveGolden.cycleNerve_dimH1_eq_b1` | `def` / `theorem` | Boundary Residue finite example は既存 `BoundaryResidueHypotheses` に相対化し、`delta(b)=0` から global U-flat、`delta(b)≠0` から global U-flat 不在を証明する。forest cover example は `ForestCoverGluingData` を instantiate して selected `H^1 = 0` を証明し、cycle nerve example は `ConstantCoefficientNerveReading` を instantiate して `dim H^1 = b_1` を読む。 | `proved finite examples under explicit packages` |
| `IV.定義13.1 / 定理13.2 / 定義13.4` | `AAT.AG.Cohomology.FiniteCechChainComplex`, `FiniteCechChainComplex.boundaryOp`, `FiniteCechChainComplex.boundary_comp_zero`, `CechCochainChainPairing`, `CechCochainChainPairing.pair`, `StokesCompatiblePairing`, `StokesCompatiblePairing.cechStokes`, `ConnectingBoundaryRepresentative`, `ConnectingBoundaryRepresentative.connectingStokes`, `ExtensionHolonomyAccounting`, `ExtensionHolonomyAccounting.kappa_U_additive`, `ExtensionHolonomyAccounting.kappa_U_zero` | `structure` / `def` / `theorem` | finite Čech chain complex、boundary、cochain-chain pairing、Stokes-compatible condition を定義し、`<d omega, gamma> = <omega, boundary gamma>` を証明する。connecting homomorphism が selected coboundary representative で構成される場合の `<delta(b), gamma> = <b, boundary gamma>` も明示 compatibility data から証明する。定義13.4 は `kappa_U` の加法性を defining property とする extension holonomy accounting convention として定義し、Stokes theorem の自動系とは主張しない。 | `proved under explicit pairing/accounting data` |
| `IV.定義14.1 / 定理候補14.2 / 定義14.3` | `AAT.AG.Cohomology.FiniteSiteMorphism`, `PushforwardObstructionSheaf`, `HigherDirectImageCech`, `AggregationComparisonMap`, `AggregationComparisonMap.InComparisonImage`, `AggregationFiveTermStatement`, `ScaleStableDebt`, `ScaleStableDebt.in_comparison_image` | `structure` / `def` / `theorem` | selected finite site morphism `pi : X_fine -> X_coarse`、pushforward `pi_* Ob`、Čech-style `R^q pi_* Ob` statement surface、`H^1(X_coarse, pi_* Ob) -> H^1(X_fine, Ob)` comparison map、定理候補14.2 の五項完全列 statement package、selected aggregation family 全体で comparison image に入る scale-stable debt を定義する。 | `statement only` / `defined only` / `proved accessor` |

Non-conclusions: この entrypoint は obstruction coefficient sheaf carrier、module-valued
coefficient surface、`Def_U` / `ConDef_U` / `DerOb_U` placeholder の R1 package、
一般 site の cover-relative Cech complex package、`d ∘ d = 0` witness、
cover-relative cohomology notation、条件付き space-level notation、明示 comparison
data 下の finite-poset target、R4 の local flatness / gluing mismatch / pseudo-torsor
normalized cocycle / descent class surface、R5 の explicit compatibility data 下の
Local Flatness Gap theorem、R6 first half の 2-chart connecting homomorphism /
boundary holonomy、R6 の explicit Boundary Residue hypotheses 下の theorem、
R7 の `H^2` class と低次五項 statement、R8 の explicit Cohomological
Flatness hypotheses 下の criterion theorem、R9 の explicit finite-dimensional
accounting data 下の cover nerve theorem package、R10(a) の selected pseudo-circle
finite golden example、R10(b)(c) の Boundary Residue / forest / cycle selected examples だけを示す。任意の finite-poset regime が
自動的に obstruction sheaf comparison data を持つこと、descent class の非零性や
非零 hidden coupling class の具体例、一般 descent theorem、仮定なしの Boundary Residue theorem、
仮定なしの Cohomological Flatness Criterion、任意 cover の無条件 nerve cohomology 計算、
ArchSig fixture JSON の検証、Boundary Residue 仮定ブロックの無条件構成、任意 cover の forest / cycle 分類、
Stokes-compatible pairing の無条件存在、`kappa_U` accounting が Stokes theorem から自動的に従うこと、
aggregation five-term statement の証明、spectral sequence 構成、任意 aggregation family の scale stability、
non-abelian torsor triviality、スペクトル系列一般論、derived category、cotangent complex、
`Ext^1` はまだ形式化しない。

## AG版AAT Lean形式化 PRD-5 / 第V部 Derived Law Geometry と Repair

File: `Formal/AG/Derived.lean`, `Formal/AG/Derived/LawfulLoci.lean`,
`Formal/AG/Derived/Koszul.lean`, `Formal/AG/Derived/Intersection.lean`,
`Formal/AG/Derived/FreeResolution.lean`, `Formal/AG/Derived/TaylorResolution.lean`,
`Formal/AG/Derived/Transversality.lean`, `Formal/AG/Derived/RepairProfile.lean`.

PRD-5 [第V部 Derived Law Geometry と Repair](lean_ag_part_5_derived_law_geometry_repair_prd.md)
の AC1/R0 と AC2/R1 に対応する entrypoint である。現時点では
`Formal/AG/Derived` を build 対象へ追加し、PRD-3 の lawful locus / obstruction
ideal surface を再利用して、law universe pair、`I_U` / `I_V` 記法、
`Flat_U(X)`、`Flat_V(X)`、および classical joint lawful locus
`V(I_U + I_V)` を Lean 上に置く。R2 として、selected finite generators に
相対化した chart-level Koszul surface、derived lawful locus、`H_0` truncation
が classical quotient / lawful locus に戻る accessor も追加している。
R3 として、selected derived tensor complex を持つ chart-level derived intersection と
Mathlib `Tor` object への selected bridge に相対化した `LawConflict_i` /
`LawConflict_0` surface、および selected global / hypercohomology notation carrier
も追加している。
R4 として、selected finite free resolution、selected tensor-complex Tor computation、
Taylor complex surface、monomial law conflict regime、命題5.5 calculation package の
carrier / accessor surface も追加している。さらに Mathlib
`ProjectiveResolution.isoLeftDerivedObj` による `Tor_i(A/I_U,A/I_V)` 計算 theorem、
Mathlib projective resolution と Taylor complex surface を結ぶ
`TaylorMathlibResolution`、および命題5.5 theorem package を追加している。
R5 として、selected law-conflict / Mathlib Tor vanishing predicate、定理6.1 の
derived non-transversality theorem、および定理7.3 の selected transversality
criterion package も追加している。
R6 として、repair comparison profile、pullback / probe repair profile、
conflict comparison profile、repair path、および代表 profile を追加している。

| 本文ラベル | Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- | --- |
| `V.R0` | `Formal.AG.Derived`, `Formal.AG.Derived.LawfulLoci`, `Formal.AG.Derived.Koszul`, `Formal.AG.Derived.Intersection`, `Formal.AG.Derived.FreeResolution`, `Formal.AG.Derived.TaylorResolution`, `Formal.AG.Derived.Transversality`, `Formal.AG.Derived.RepairProfile` | `import` | 第V部 derived-law-geometry tower の entrypoint。`Formal/AG.lean` から import され、`lake build` 対象に入る。 | `defined only` |
| `V.定義2.1 / 定義3.1` | `AAT.AG.Derived.LawfulLoci.LawUniverseReading`, `LawUniversePair`, `LawUniversePair.I_U`, `LawUniversePair.I_V`, `LawUniversePair.flatU`, `LawUniversePair.flatV`, `LawUniversePair.classicalJointIdeal`, `LawUniversePair.classicalJointLawfulLocus`, `LawUniversePair.flatU_eq_lawfulLocus`, `LawUniversePair.flatV_eq_lawfulLocus`, `LawUniversePair.classicalJointLawfulLocus_eq_zeroLocus`, `LawUniversePair.classicalJointLawfulLocus_eq_flatU_inter_flatV` | `abbrev` / `structure` / `def` / `theorem` | 同じ chart algebra 上の二つの selected law-universe reading から、PRD-3 の `localObstructionIdeal` を `I_U` / `I_V` として読み、classical joint lawful locus を `V(I_U + I_V)` および `Flat_U(X) ∩ Flat_V(X)` として公開する。 | `defined only` / `proved accessor` |
| `V.定義2.3 / 原則2.4` | `AAT.AG.Derived.Koszul.SelectedGeneratorFamily`, `SelectedGeneratorFamily.generatedIdeal`, `SelectedGeneratorFamily.firstTerm`, `SelectedGeneratorFamily.d1`, `SelectedGeneratorFamily.d1_mem_generatedIdeal`, `KoszulComplex`, `KoszulComplex.C0`, `KoszulComplex.C1`, `KoszulComplex.d1`, `KoszulComplex.zeroHomologyIdeal`, `KoszulComplex.zeroHomology`, `KoszulComplex.zeroHomologyIdeal_eq`, `KoszulComplex.zeroHomology_eq_classicalQuotient`, `KoszulComplex.zeroHomologyAlgEquivClassicalQuotient`, `KoszulComplex.zeroHomologyRingEquivClassicalQuotient`, `DerivedLawfulLocus`, `DerivedLawfulLocus.structureSheafComplex`, `DerivedLawfulLocus.truncation`, `DerivedLawfulLocus.truncation_eq_classicalQuotient`, `DerivedLawfulLocus.truncationAlgEquivClassicalQuotient`, `DerivedLawfulLocus.truncationRingEquivClassicalQuotient`, `DerivedLawfulLocus.truncationIdeal_eq`, `DerivedLawfulLocus.truncation_locus_eq_classical` | `structure` / `abbrev` / `def` / `theorem` | selected finite defect generators から chart-level Koszul surface を作り、zero-th truncation quotient が classical quotient `O_X/I` に戻り、その locus が classical lawful locus と一致することを accessor theorem として公開する。quotient truncation は type equality に加えて algebra/ring equivalence でも参照できる。 | `defined only` / `proved accessor` |
| `V.定義4.1 / 5.1 / 5.2` | `AAT.AG.Derived.Intersection.classicalJointQuotient`, `AAT.AG.Derived.Intersection.mathlibTor`, `SelectedDerivedTensorComplex`, `SelectedDerivedTensorComplex.C0`, `SelectedDerivedTensorComplex.homology0`, `SelectedDerivedTensorComplex.homology0LinearEquivClassicalJoint`, `ChartDerivedIntersection`, `ChartDerivedIntersection.classicalQuotient`, `ChartDerivedIntersection.structureSheafComplex`, `ChartDerivedIntersection.homology0LinearEquivClassicalJoint`, `SelectedTorBridge`, `SelectedTorBridge.torLinearEquivMathlib`, `SelectedTorBridge.LawConflict`, `SelectedTorBridge.LawConflict₁`, `SelectedTorBridge.lawConflict_eq_tor`, `SelectedTorBridge.lawConflictLinearEquivMathlibTor`, `SelectedTorBridge.lawConflict0AlgEquivClassicalJoint`, `SelectedTorBridge.lawConflict0RingEquivClassicalJoint`, `LawConflictPackage`, `LawConflictPackage.LawConflict`, `LawConflictPackage.LawConflict₁`, `LawConflictPackage.lawConflict_eq_tor`, `LawConflictPackage.lawConflictLinearEquivMathlibTor`, `LawConflictPackage.lawConflict0AlgEquivClassicalJoint`, `LawConflictPackage.lawConflict0RingEquivClassicalJoint`, `SelectedGlobalLawConflictReading`, `SelectedGlobalLawConflictReading.H0`, `SelectedGlobalLawConflictReading.H0LawConflict₁`, `SelectedGlobalLawConflictReading.h0LinearEquivSelectedLawConflict`, `SelectedGlobalLawConflictReading.hypercohomology`, `LawfulLoci.LawUniversePair.DerivedIntersectionFor`, `LawfulLoci.LawUniversePair.derivedIntersection` | `abbrev` / `structure` / `def` / `theorem` | chart-level derived intersectionを selected Koszul presentations と selected derived tensor complex として持ち、`LawConflict_i` を Mathlib `Tor_i(O_X/I_U,O_X/I_V)` への selected linear equivalence として公開する。degree zero は `O_X/(I_U+I_V)` への algebra/ring equivalence として固定し、`H^0(X, LawConflict_i)` と hypercohomology は selected notation carrier として置く。 | `defined only` / `proved accessor` |
| `V.R4 / 定義5.4 / 命題5.5` | `AAT.AG.Derived.FreeResolution.SelectedFiniteFreeResolution`, `SelectedFiniteFreeResolution.termLinearEquivFree_certificate`, `SelectedFiniteFreeResolution.exact_certificate`, `SelectedTensorComplex`, `SelectedTensorComplex.homology`, `SelectedTensorComplex.tensorOfResolution_certificate`, `FiniteFreeResolutionTorComputation`, `FiniteFreeResolutionTorComputation.mathlibTorLinearEquivTensorHomology`, `FiniteFreeResolutionTorComputation.tensorHomologyLinearEquivMathlibTor`, `FreeResolution.MathlibResolution.quotientModule`, `FreeResolution.MathlibResolution.tensorAppliedComplex`, `FreeResolution.MathlibResolution.torIsoProjectiveResolutionHomology`, `FreeResolution.MathlibResolution.FiniteFreeMathlibResolution`, `FiniteFreeMathlibResolution.termIsoFree_certificate`, `FiniteFreeMathlibResolution.torIsoTensorHomology`, `FiniteFreeMathlibResolution.tensorHomologyIsoTor`, `AAT.AG.Derived.TaylorResolution.SquareFreeMonomialIdealPresentation`, `SquareFreeMonomialIdealPresentation.generatedIdeal_eq`, `SquareFreeMonomialIdealPresentation.squareFree_certificate`, `MonomialLawConflictRegime`, `MonomialLawConflictRegime.lcmSupport`, `MonomialLawConflictRegime.lcmSupport_eq_union`, `TaylorComplex`, `TaylorComplex.resolvesQuotient_certificate`, `TaylorComplex.multidegree_union_eq`, `TaylorMathlibResolution`, `TaylorMathlibResolution.identifiesTaylorTerms_certificate`, `TaylorMathlibResolution.identifiesTaylorDifferentials_certificate`, `TaylorMathlibResolution.taylorResolution_certificate`, `TaylorMathlibResolution.mathlibResolutionTorIsoTensorHomology`, `MonomialConflictCalculation`, `MonomialConflictCalculation.computesLawConflict_certificate`, `MonomialConflictCalculation.lawConflictLinearEquivTensorHomology`, `MonomialConflictCalculation.lcm_multidegree_eq_union`, `Proposition55TheoremPackage`, `Proposition55TheoremPackage.computesLawConflict_certificate`, `Proposition55TheoremPackage.taylorResolution_certificates`, `Proposition55TheoremPackage.lawConflictIsoRightMathlibResolutionTensorHomology`, `Proposition55TheoremPackage.rightMathlibResolutionTensorHomologyIsoLawConflict`, `Proposition55TheoremPackage.lcm_multidegree_eq_union` | `structure` / `abbrev` / `def` / `theorem` | monomial law conflict regime を square-free monomial ideal pair として読み、selected finite free resolution / tensor complex surface を保持する。Mathlib projective resolution theorem により有限自由 Mathlib resolution の tensor complex homology が `Tor_i(A/I_U,A/I_V)` を計算し、Taylor complex surface は `TaylorMathlibResolution` の selected Taylor certificate と projective-resolution identification data により quotient resolution として読む。命題5.5 package は selected right Taylor package に付随する Mathlib resolution から law conflict Tor を計算し、lcm multidegree が forbidden support union であることを返す。 | `proved under explicit Mathlib projective-resolution / Taylor identification data` |
| `V.定理6.1 / 定義7.1-7.4 / 定理7.3` | `AAT.AG.Derived.Transversality.LawConflictVanishes`, `PositiveLawConflictVanishing`, `LawConflictNonzero`, `FirstLawConflictNonzero`, `DerivedNonTransverse`, `MathlibTorVanishes`, `PositiveMathlibTorVanishing`, `Transversality.LawConflictPackage.derivedNonTransverse_of_firstLawConflictNonzero`, `Transversality.LawConflictPackage.lawConflictVanishes_iff_mathlibTorVanishes`, `Transversality.LawConflictPackage.positiveLawConflictVanishing_iff_mathlibTorVanishing`, `DerivedTransversalityCriterion`, `DerivedTransversalityCriterion.criterion_positiveTorVanishing_iff_classicalAgreement`, `DerivedTransversalityCriterion.positiveLawConflictVanishing_iff_classicalAgreement` | `def` / `abbrev` / `structure` / `theorem` | selected law-conflict vanishing / nonvanishing と Mathlib Tor vanishing を定義し、`LawConflict_1` 非零から selected derived non-transversality を読む定理6.1 surface を証明する。定理7.3 は、正次数 Mathlib Tor 消滅と selected derived tensor の classical agreement statement の明示 equivalence data として package 化し、selected law-conflict vanishing との同値も返す。 | `proved under explicit selected transversality criterion data` |
| `V.定義8.1-8.4` | `AAT.AG.Derived.RepairProfile.RepairComparisonLevel`, `RepairComparisonProfile`, `RepairComparisonProfile.sectionLe`, `RepairComparisonProfile.geometryLe`, `RepairComparisonProfile.sectionComparison_of_improves`, `RepairComparisonProfile.geometryComparison_of_improves`, `RepairComparisonProfile.idealOrderRepairProfile`, `RepairComparisonProfile.valuationRepairProfile`, `RepairComparisonProfile.rankRepairProfile`, `RepairComparisonProfile.supportRepairProfile`, `RepairKind`, `PullbackRepairProfile`, `PullbackRepairProfile.IsInternal`, `PullbackRepairProfile.IsGeometric`, `PullbackRepairProfile.pullbackObstructionComparison_certificate`, `PullbackRepairProfile.probeComparison_certificate`, `PullbackRepairProfile.geometryImproves_certificate`, `ConflictComparisonProfile`, `ConflictComparisonProfile.selectedDegree_positive`, `ConflictComparisonProfile.comparisonMap_ordered_certificate`, `ConflictComparisonProfile.doesNotIncreaseSelectedConflict_certificate`, `RepairPathKind`, `UAxisObstructionDecreases`, `RepairPath`, `RepairPath.decreasesUAxis_certificate`, `RepairPath.uAxisDecrease_certificate`, `RepairPath.sectionComparison_of_uAxisDecrease` | `inductive` / `structure` / `def` / `theorem` | repair comparison profile `P_U` を section / geometry 比較と改善 predicate の明示データとして固定し、ideal-order / valuation / rank / support の代表 profile を与える。pullback repair profile は internal / geometric repair を分け、`r^{-1} I'_U · O_X <= I_U` と probe-level comparison を profile data として保持する。conflict comparison profile `Q_{U,V}` は selected positive degree、comparison map、order / vanishing predicate、selected conflict が増えない certificate を持つ。repair path は geometry morphism / section deformation と `U`-axis decrease を profile 相対で記録する。 | `defined only` / `proved accessor` |

Non-conclusions: この entrypoint は derived category 一般論、
repair transfer、Hilbert series、well-founded repair、cotangent complex、
`Ext^1` をまだ形式化しない。Koszul surface は selected finite generators に
相対化され、generator choice independence や higher Koszul homology は主張しない。
LawConflict は selected complex / bridge / global notation data に相対化され、Tor の計算や
finite free resolution から bridge を構成する補題は Mathlib projective-resolution data
および selected package の明示 certificate に相対化する。raw monomial presentation だけから
Taylor resolution exactness を自動構成する一般定理、Scarf complex、lcm-lattice resolution、
minimality、concrete Tor nonzero examples、Cech-to-sheaf comparison、global cohomology
計算はまだ主張しない。Transversality criterion は selected `classicalAgreement`
statement と明示 equivalence data に相対化する。Repair profile は比較 profile /
probe profile / conflict profile の選択データだけを固定し、repair monotonicity、
global improvement、または profile-independent repair theorem は主張しない。
PRD-4 の `DerOb_U` は type-signature-only placeholder のまま維持する。

## Reverse-Import Theorem Packages

File: `Formal/Arch/Evolution/ReverseImportTheorems.lean`.

ArchSig の structural reading から見える projection / trajectory / bridge-transfer の
パターンを、private source に依存しない AAT theorem package として戻した索引である。
各 theorem は assumption-relative であり、tooling measurement を global truth や
automatic repair safety に昇格しない。

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `ReverseImportTheorems.AxisForgettingProjectionBoundary` | `structure` | coarse reading preservation と、selected axis preservation / witness completeness に相対化された zero / obstruction reflection boundary を分離する。 | `defined only` |
| `ReverseImportTheorems.AxisForgettingProjectionBoundary.HasReflectionWitnesses` | `def` | projection reflection に必要な selected axis preservation と witness completeness の組。 | `defined only` |
| `ReverseImportTheorems.AxisForgettingProjectionBoundary.not_zeroReflecting_of_missingAxisWitness` | `theorem` | axis preservation / witness completeness が欠ける場合、structural zero reflection を結論できない。 | `proved` |
| `ReverseImportTheorems.AxisForgettingProjectionBoundary.not_obstructionReflecting_of_missingAxisWitness` | `theorem` | axis preservation / witness completeness が欠ける場合、obstruction absence reflection を結論できない。 | `proved` |
| `ReverseImportTheorems.AxisForgettingProjectionBoundary.records_nonConclusions` | `theorem` | projection boundary が non-conclusion clause を保持する。 | `proved` |
| `ReverseImportTheorems.selectedSignatureTrajectory_refutesPathHomotopy` | `theorem` | selected trajectory observation を保存する generated homotopy に対し、trajectory disagreement から selected homotopy 不在を得る。 | `proved` |
| `ReverseImportTheorems.BridgeEdgeSplitObstructionBoundary` | `structure` | bridge edge shared Atom support、selected obstruction support、filler / lifting / boundary-operation evidence、split readiness を束ねる。 | `defined only` |
| `ReverseImportTheorems.BridgeEdgeSplitObstructionBoundary.HasBoundaryEvidence` | `def` | split transfer を防ぐ filler / lifting / boundary-operation evidence の和。 | `defined only` |
| `ReverseImportTheorems.BridgeEdgeSplitObstructionBoundary.not_splitReadyWithoutTransfer_of_missingBoundaryEvidence` | `theorem` | selected bridge support と obstruction support の下で boundary evidence が欠ける場合、transfer-free split readiness は結論できない。 | `proved` |
| `ReverseImportTheorems.BridgeEdgeSplitObstructionBoundary.RecordsTransferRisk` | `def` | bridge support、obstruction support、missing boundary evidence、non-conclusion を transfer-risk report として束ねる。 | `defined only` |
| `ReverseImportTheorems.BridgeEdgeSplitObstructionBoundary.recordsTransferRisk_of_missingBoundaryEvidence` | `theorem` | 明示前提から transfer-risk report package を構成する。 | `proved` |

Non-conclusions: private repository 名、source path、internal id、global architecture truth、operation commutativity、automatic repair safety、FieldSig forecast calibration は結論しない。

## 現在 Lean に入れていないもの

次は意図的に Lean core へ混ぜていない。

- `Decomposable` の定義への acyclicity, finite propagation, nilpotence, spectral conditions の混入。
- より一般の `Sem_A(p) - Sem_A(q)` 型の数値 curvature metric。
  `Formal/Arch/Signature/Curvature.lean` は、zero-separating distance の個別 diagram bridge、
  有限測定 list 上の `Nat` total bridge、正の重みに相対化された weighted total bridge
  までを含む。Signature axis 化、重み calibration、empirical cost model はまだ導入しない。
- `relationComplexity`, `runtimePropagation`, `empiricalChangeCost` の実証相関。
- source-observation output が `ComponentUniverse` の完全な witness であるという主張。
- `rho(A)` と変更波及・障害伝播コストの相関。

これらは [証明義務と実証仮説](proof_obligations.md)、tooling boundary、または empirical protocol 側で扱う。
