# G-127：既存宣言と新規構成の対応

[実装設計](README.md)の再利用箇所を、既存の入力型・結論と新規の接続に分ける。
Research pathは `research/lean/ResearchLean/AG/` からの相対、mathlib pathは
リポジトリが指定するmathlibの `Mathlib/` からの相対とする。
参照版はGOALのactive化時にtracking Issueへ記録する。

## 1. グラフ、道、群

| 既存path・宣言 | 既存の内容 | G-127で構成する接続 |
| --- | --- | --- |
| `RealizationReconstruction/FixedFSourceClassification.lean`：`FixedFDirectedMultigraph`、`FixedFGraphAutomorphism` | 名前付き多重グラフと、頂点・辺の全単射による自己同型 | グラフの型はそのまま使い、各頂点の可変fiberと可逆な辺作用を付ける |
| `RealizationReconstruction/FixedFAllAutomorphismGroup.lean`：`Group (FixedFGraphAutomorphism Q)` | グラフ自己同型の合成・逆 | `H` の周囲の群に使う。同ファイルの状態変更群は恒等操作専用なので新しい `ChangeGroup` を構成する |
| `RealizationReconstruction/FixedFComponentClassification.lean`：`FixedFComponent`、`fixedFComponentMk_eq_iff`、`fixedFComponent_source_eq_target` | 辺の両端の関係の同値閉包と商 | 逆向きを含む道の存在、および有限全域森の成分との同値を示す |
| mathlib `Combinatorics/Quiver/Symmetric.lean`：`Quiver.Symmetrify`、`Quiver.Path.reverse`、`reverse_comp`、`reverse_reverse` | 形式的な逆向き辺と道の反転 | 正向き辺を `T_e`、逆向きを `T_e⁻¹` で評価し、輸送の合成・反転を証明する |
| mathlib `Algebra/Group/Subgroup/Lattice.lean`：`Subgroup.closure`、`closure_le`、`closure_induction` | 部分群の生成と生成元からの帰納法 | 閉路 `γ_e` の置換を生成元にし、全閉路の輸送との一致を証明する |
| mathlib `GroupTheory/Subgroup/Centralizer.lean`：`Subgroup.centralizer`、`mem_centralizer_iff`、`centralizer_closure` | 群の部分集合との可換性。生成部分群の中心化は生成元の中心化に一致 | 根での評価・復元から `verticalGroup` との群同型を構成し、有限判定を各辺の等式へ帰着する |
| `ComparisonInformationLoss/GroupHomRestriction.lean`：`IsGroupShortExact`、`restrictedSubgroupHom_shortExact_iff_map_eq` | 単射・完全性・全射による短完全列。制限射影の像との同値 | 値域を `H_lift=projection.range` とし、元の `Aut_Q(F)` を実際の核へ群同型で対応させる |
| 同ファイル：`RestrictedFiber`、`restrictedFiber_existsUnique_smul_eq` | 制限準同型のfiberは、実際の核の右作用について自由かつ推移的 | `Lift F u` との全単射と核の群同型を作り、右作用の各頂点での値が `φ_v∘α_v` になることを示す |

右作用は既存APIと同じく反対群の左作用として使う。
群の完全性だけを得て終わらず、可視射影と根での持ち上げ条件を同じ入力上で同定する。

## 2. プロトコル意味論

| 既存path・宣言 | 既存の内容 | G-127で構成する接続 |
| --- | --- | --- |
| `RealizationReconstruction/ProtocolSchema.lean`：`ProtocolSchema`、`ExecutionCategory`、`pathFunctorOfEdgeAction`、`evaluatePath_comp` | 有限な型付きグラフと有限経路等式から商実行圏を作り、生成辺から全経路を評価 | `Q,Π` のスキーマを作り、可逆な辺作用の評価と符号付き輸送の正向き部分を一致させる |
| `RealizationReconstruction/FixedFProtocolConnection.lean`：`TypedEdge`、`renameTypedEdge`、`renamePath` | 元の辺名・端点を保つ型付き辺と付け替え | 型付き辺の表現と付け替えを再利用し、任意の `Π` への降下を新たに証明する |
| 同ファイル：`schema`、`renameExecutionFunctor`、`realization` | 関係族が空、辺作用が恒等の場合の実現と実行の付け替え | 一般構成の入力にはせず、`Π=∅,T_e=id` の特殊化で既存対象との同型を示す |
| `RealizationReconstruction/ProtocolSemantics.lean`：`ProtocolRealization` | 有限状態を持つ実行圏上の関手と観測。射は観測を保つ自然変換 | 原始辺作用から実現を構成し、`u` で再添字づけた実現との自然同型を持ち上げへ対応させる |
| `RealizationReconstruction/ProtocolReconstruction.lean`：`GeneratorMap`、`ext`、`res`、`res_ext`、`ext_res`、`homEquivGeneratorMap`（`ProtocolRealization` 内） | 同じスキーマ・観測上の実現間で、辺の可換式と観測条件から自然変換を延長 | 固定した `u` の再添字後の実現を行き先に取り、全単射成分とその逆を延長する。異なる `u` 間の合成の対応は別に証明する |
| `RealizationReconstruction/ProtocolFinitePresentation.lean`：`ProtocolPresentation.decoder`、`decoderObject_edgeAction`、`decoderObject_observe` | `Fin (card v)` 上の表から独立な実現を構成。状態は `ULift` される | Eの表をこの表示へ送り、上げ下げ・座標化の全単射を通して元の辺と全頂点の持ち上げを読み戻す |

`H` の経路合同保存は、再添字づけ関手を商へ降ろすための入力条件として使う。
既存の `renameExecutionFunctor` の空の関係族による証明を、一般の `Π` の証明として使わない。

## 3. 恒等操作系との照合

| 既存path・宣言 | 適用条件と対応 |
| --- | --- |
| `RealizationReconstruction/FixedFComponentClassification.lean`：`FixedFEdgeConstantPermutationFamily.equivComponentPermutationFamilies` | `F(v)=K,T_e=id` で辺の条件を両端の置換の一致へ簡約し、Bの根での評価・復元と同じ全頂点の族を返すことを示す |
| `RealizationReconstruction/FixedFSplitExactSequenceAndTorsor.lean`：`isGroupShortExact`、`canonicalSection_rightInverse`、`projectionFiber_existsUnique_smul_eq` | 恒等操作系の分裂短完全列とfiber。新しい群の特殊化との群同型を通して、射影・section・核作用を対応させる |
| `RealizationReconstruction/FixedFProtocolGroupConnection.lean`：`ProtocolChangeGroup`、`mulEquivFollowingGroup`、`projection_compatibility`、`section_compatibility`、`kernelMulEquiv`、`projectionFiberEquiv` | 有限 `Q,K`、空の経路関係、恒等操作。各頂点の置換と名前付き辺の等式を保つ群同型を作り、既存の接続へ合成する |
| `LocalSemanticReconstruction/CSFixedFDetermining.lean`：`protocolRepresentativeSet`、`protocol_representatives_determining` | 後者には `Nontrivial K` がある。その適用下で、既存の代表を根に選び、読み取り・延長をB・Cの特殊化と照合する |

可逆な非恒等操作での中心化群表示、根の同時対応条件、根・木の変更、全域森と有限探索、
GOALの二つの固定例は、[実装設計](README.md)に沿って新しく構成する。
一般分類へ恒等操作系のsectionを持ち込まず、sectionの構成はGOAL Dの特殊化で行う。
