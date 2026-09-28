# G-128：既存宣言と新規構成の対応

[実装設計](README.md)で使う既存宣言を、既存の結論と新しい証明義務に分ける。
Research pathは `research/lean/ResearchLean/AG/`、mathlib pathは `Mathlib/` からの相対とする。
mathlibは[Research packageのmanifest](../../lean/lake-manifest.json)が指定する版を使う。
具体的な参照版と検証結果はtracking Issueへ記録する。

## 1. 群作用・観測・最小数

| 既存path・宣言 | 既存の入力と結論 | 再利用と新しい証明義務 |
| --- | --- | --- |
| mathlib `GroupTheory/GroupAction/Defs.lean`：`MulAction.stabilizer`、`mem_stabilizer_iff` | 任意の群作用の一点安定化群と所属条件 | 有限集合の各点で共通部分を取り、`O_B(g)=O_B(h)` と `h⁻¹*g` の所属を新しく証明する |
| mathlib `Algebra/Group/Subgroup/Lattice.lean`、`Map.lean` | 部分群の格子・引き戻し | 点安定化群と適合部分群をnativeな `Subgroup` で扱う。判定述語の因子化と最小性はG-128の証明義務 |
| [ComparisonInformationLoss/ObservationKernel.lean](../../lean/ResearchLean/AG/ComparisonInformationLoss/ObservationKernel.lean)：`exists_observation_predicate_iff_ker_le` | 任意の群準同型 `O : G →* L` と部分群について、所属判定の因子化と `O.ker ≤ Gamma` が同値。有限性・正規性・全射性は不要 | 一般の点観測に対するA1を新しく証明する。`X=L, g • x=O(g)*x, B={1}` で同じ観測・核・述語となることを証明し、既存定理へ接続する |
| mathlib `Algebra/Group/Action/Hom.lean`：`MulAction.compHom` | 準同型に沿う作用の引き戻し | G-120への特殊化と、積群の各射影を通じたDの作用を構成する |
| mathlib `Data/ENat/Lattice.lean`：`ENat.iInf_coe_eq_top`、`ENat.exists_eq_iInf` | 自然数を埋め込んだ下限の∞判定、非空な族での最小値の達成 | 十分な有限集合の族に適用して `b_Gamma` のAPIを作る。同じ型をBの最悪回数の最小値にも使う |
| mathlib `Algebra/Group/Action/Sum.lean`：`Sum.smul_inl`、`Sum.smul_inr` と `MulAction` instance | 同じ群が作用する二つの型の非交和への作用 | Dでは積の各射影、Eでは頂点・辺・状態の作用を組み合わせる。Eの全観測の忠実性は三成分の評価から新しく証明する |
| mathlib `Data/Finset/Sum.lean`：`disjSum`、`toLeft`、`toRight`、`card_disjSum`、`card_toLeft_add_card_toRight` | 有限な非交和の分解と濃度の加法性 | Dの点安定化群の積表示と十分性の同値を証明し、Aの最小値APIを使って∞を含む最小数の加法性を得る |

`ObservationKernel.lean` の剰余類・飽和の定理は、一般の `O_B` の証明として流用しない。
G-128 Aの安定化群は正規部分群であるとは限らず、作用の忠実性も入力条件ではない。

## 2. 有限列挙・問い合わせ・greedy

| 既存path・宣言 | 既存の入力と結論 | 再利用と新しい証明義務 |
| --- | --- | --- |
| [ProtocolHolonomy/FiniteDirectDecision.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/FiniteDirectDecision.lean)：`ExplicitEnumeration` | `values : List α` と `complete : ∀ a, a ∈ values`。重複の排除は要求しない | Cの入力型としてそのまま使う。集合の濃度は `toFinset`、greedyの同数時の順序は元の `values` で扱う |
| 同ファイル：`ExplicitEnumeration.toFintype` | 入力されたリストと `DecidableEq` から有限量化を作る | 実行用 `Fintype` の生成に使い、`Finite` だけから選択した列挙を実行入力にしない |
| 同ファイル：`ExplicitEnumeration.pi`、`product` | 完全な入力列挙から依存関数・組の完全な列挙を作る | Eの候補表生成を再利用する。Cの一般群・作用の表は既知入力として受け取る |
| mathlib `Data/Finset/Powerset.lean`：`Finset.powerset` | 全ての部分集合の有限列挙 | 最小観測集合の走査と、全候補に対する最小性を新しく証明する |
| mathlib `Algebra/BigOperators/Group/Finset/Basic.lean`：`Finset.card_biUnion_le` | 和集合の濃度は濃度の和以下 | 被覆集合と最大新規被覆数を比較する |
| mathlib `Algebra/Order/BigOperators/Group/Finset.lean`：`Finset.card_biUnion_le_card_mul` | 各集合の濃度が `k` 以下なら、和集合の濃度は集合数と `k` の積以下 | 任意の被覆集合 `B*` に対して `|R| ≤ |B*| * k` を証明する |
| mathlib `NumberTheory/Harmonic/Defs.lean`：`harmonic`、`harmonic_zero`、`harmonic_succ` | 有理数値の調和数と再帰式 | 新しい差分評価 `k/n ≤ H_n-H_(n-k)` と選択回数の帰納法に使う |

質問・回答履歴、`Run`、最悪問い合わせ回数、恒等元の実行による下限、
観測点への集合被覆の対応、最大新規被覆を選ぶ関数、調和数の近似保証を新規に構成する。
既存の有限列挙や `harmonic` の存在だけで、これらの結論が証明済みであるとは扱わない。
具体的な補題と依存関係は[アルゴリズム設計](query-and-greedy.md)に従う。

## 3. G-127の原始入力と群の接続

以下の `ReversibleData` 内の宣言は `D : ReversibleData Q` に対するものとする。

| 既存path・宣言 | 既存の入力と結論 | 再利用と新しい証明義務 |
| --- | --- | --- |
| [RealizationReconstruction/FixedFSourceClassification.lean](../../lean/ResearchLean/AG/RealizationReconstruction/FixedFSourceClassification.lean)：`FixedFDirectedMultigraph`、`FixedFGraphAutomorphism` | 名前付き辺を保った多重グラフ、頂点・辺の全単射と端点の保存 | 同じ `Q` と可視群を使う。辺名の作用を頂点の作用に縮約しない |
| [ProtocolHolonomy/PathEquations.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/PathEquations.lean)：`FiniteProtocolInput` | `data`、頂点・辺・fiberの有限性、経路等式の充足、`H` による生成等式の保存 | Eの原始入力としてそのまま受け取る。新しい周囲の群は `data,H` から構成し、同じ入力の意味論への対応を保つ |
| [ProtocolHolonomy/Basic.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/Basic.lean)：`ReversibleData`、`renamedEdgeEquiv`、`Lift`、`Lift.stateEquiv` | 任意のfiberと辺の全単射、型付きの名前変更、元の可換式を満たすfiber全単射族と全状態置換 | 新しい周囲の群には可換式を課さず、適合群の元を同じ `Lift` へ対応させる。全状態の作用が `Lift.stateEquiv` と一致することを示す |
| [ProtocolHolonomy/ChangeGroup.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/ChangeGroup.lean)：`NamedExecution`、`StateChange`、`ChangeGroup`、`ChangeGroup.projection` | 名前付き操作の関係、その関係を保つ可視・状態変更の群、`H` への射影 | 適合群との群同型と射影の可換性に使う。新しい周囲の群は `H × Equiv.Perm S` の部分群として別に構成する |
| [ProtocolHolonomy/LiftBridge.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/LiftBridge.lean)：`Lift.preserves_namedExecution`、`Lift.toStateChange`、`StateChange.toLift`、`liftEquivStateChangeOver` | 元のfiberの可換式と全状態での操作保存の対応 | 新しい適合条件を(E1)と同値にし、可視fiberを同じ `Lift` に対応させる。周囲の群からfiberへの制限は新しく作る |
| 同ファイル：`liftPairMulEquivChangeGroup`、`liftPair_mul_fiber_apply` | `Σ u:H, D.Lift u.1` と元の変更群の群同型、各頂点でのA2の合成式 | 新しい適合群からの写像が同じ積を保つことを確認する。`LiftPair` は既に適合条件を含むので、周囲の群の代用にしない |
| [ProtocolHolonomy/LiftRootReconstruction.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/LiftRootReconstruction.lean)：`liftEquivRootSolutions`、`RootSolutions.toLift` | 任意の `RootedPaths` と可視変更について、元の `Lift` と根での同時解の全単射・復元 | 適合群の可視fiberから合成し、各頂点での元の写像を保つ。解の存在だけを返す接続にしない |
| [ProtocolHolonomy/VerticalCentralizer.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/VerticalCentralizer.lean)：`RootCentralizers`、`verticalRootMulEquiv` | `D.Lift 1` と、成分の各根におけるholonomy中心化群の積との群同型 | 新しい適合群の可視射影の核を `D.Lift 1` に群同型で移し、同じ根での評価へ接続する |

一般の可変fiberを持つ周囲の群、適合部分群、頂点・辺・状態への作用、
全観測の忠実性は新規構成である。既存の恒等操作・共通fiber専用の
`FixedFFollowingStateChange` を一般の周囲の群として使わない。
G-127のholonomy生成、森の選択、根からの復元そのものは既存宣言へ接続する。

## 4. 操作系の有限表

| 既存path・宣言 | 既存の入力と結論 | 再利用と新しい証明義務 |
| --- | --- | --- |
| [ProtocolHolonomy/FiniteDirectDecision.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/FiniteDirectDecision.lean)：`CandidateMaps`、`allCandidateMaps` | 固定した可視変更、頂点・fiberの列挙から、全ての前向き・逆向きfiber関数表を列挙する | 候補列挙をそのまま使い、二つの逆写像条件だけの検査で周囲の群の元を作る。その完全性を証明する |
| 同ファイル：`ValidCandidate`、`liftOfValidCandidate` | 二つの逆写像条件と元の辺の可換式を検査し、元の `Lift` を作る | 適合する候補の読み戻しに使う。周囲の群の列挙に使うと不適合な元が消えるため、検査の役割を分ける |
| [ProtocolHolonomy/FiniteSelectedAllLifts.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/FiniteSelectedAllLifts.lean)：`finiteSelectedAllLifts`、`mem_finiteSelectedAllLifts`、`finiteSelectedAllLifts_eq_nil_iff` | 原始表から生成した同じ森、C1の一つの解、B2の垂直変更、C3の作用によって、固定した可視変更上の全ての `Lift` を列挙する | 全 `u : H` について列挙して周囲の群へ埋め込む。その集合が新しい適合部分群の(E1)判定と一致することを示す |
| [ProtocolHolonomy/FiniteAllLifts.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/FiniteAllLifts.lean)：`composeVertical`、`composeVertical_eq_rightAction` | 各fiber上の実行可能な合成と、G-127の実際の右作用との一致 | `finiteSelectedAllLifts` の内部で再利用する。同じ列挙を別のtorsor実装で作り直さない |

`findSelectedRootLift` の一つの成功出力だけでは、適合群の全要素を列挙したことにならない。
G-128 Cの候補を尽くすには、上表の `finiteSelectedAllLifts` とその完全性を使う。
入力された `visible : ExplicitEnumeration H` は、持ち上げ可能な可視変更だけに狭めない。

既存の `FiniteProtocolInput` は `Finite` を、新しい実行用関数は明示的列挙を受け取る。
数学的な群同型の `noncomputable` 宣言と、有限表から返す関数の計算依存を分ける。
実行する変換は列挙・前向き写像・逆写像から作り、同型との一致を後で証明する。

## 5. G-124の代表・置換表・延長

| 既存path・宣言 | 既存の入力と結論 | 再利用と新しい証明義務 |
| --- | --- | --- |
| [LocalSemanticReconstruction/FiniteReadingCore.lean](../../lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteReadingCore.lean)：`FiniteReading.restrict`、`Separates`、`Extends`、`Determining` | 読取り関数の有限表への制限、単射性、別に定義した整合述語を満たす表の延長、両者の連言 | G-124の「区別」とG-128の「適合性判定」を区別して対応を記述する。延長は実際の変更の存在を結論にする |
| [LocalSemanticReconstruction/FinitePermutationReadingCriteria.lean](../../lean/ResearchLean/AG/LocalSemanticReconstruction/FinitePermutationReadingCriteria.lean)：`readAt`、`EdgeCoherent` | 固定した可視変更上の適合する変更から、各頂点の置換全体を読み取る。整合性は保持した辺の条件 | `H={1}` の同じ可視変更、同じ置換表を全点評価の表へ移す。点観測との等式はG-128で証明する |
| [LocalSemanticReconstruction/CSFixedFDetermining.lean](../../lean/ResearchLean/AG/LocalSemanticReconstruction/CSFixedFDetermining.lean)：`protocolRepresentativeSet`、`protocol_representatives_determining` | 前者は有限な頂点から成分ごとの代表集合を非計算的に選ぶ。後者は `Nontrivial K` の下で、その集合における区別と `EdgeCoherent` 表の延長を証明する | 同じ代表集合 `R` とGOALの有限・非自明な `K` に適用する。`B=R×K` の全点評価へ移し、Cの適合する延長探索と一致させる |
| [ProtocolHolonomy/IdentityG124Bridge.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/IdentityG124Bridge.lean)：`identityLiftEquivG124Preserving`、`identityG124_readAt` | 恒等操作の元の `Lift` とG-124の変更の全単射、同じ頂点で `readAt = fiber` | 適合群からこの全単射へ接続し、`O_B(a)(r,x)` が同じ置換を `x` に評価した状態であることを示す |
| [ProtocolHolonomy/IdentityG124Representatives.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/IdentityG124Representatives.lean)：`g124RepresentativeRootedPaths`、`identityG124_B2_representative_reading` | G-124と同じ代表を根とし、B2の根での値とG-124の読取りを一致させる | 同じ代表のまま接続する。有限表生成で別に選ばれた根と同一視しない |
| [ProtocolHolonomy/IdentityG124Determining.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/IdentityG124Determining.lean)：`identityLift_representatives_determining` | 有限な頂点、非自明な `K`、任意の可視自己同型について、元の `Lift` のfiber読取りが同じ `R,EdgeCoherent` で区別・延長を満たす | 単射性と延長の両方を使い、Cの探索が返した適合変更を一意な既存延長と一致させる |
| [ProtocolHolonomy/IdentityG124Extension.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/IdentityG124Extension.lean)：`identityComponentRootSolutions`、`identity_G124_C2_extension_agree` | 成分の置換族からC1の解を作り、C2とG-124の延長が全頂点で同じ置換を返す | 代表の表から同じ成分族を取り、Cの出力の各頂点・各状態での値をこの等式へ接続する |

全点評価に直す写像と、その逆の置換の外延性が新しい接続の中心になる。
`Nontrivial K` はGOAL Eの特殊化で使用し、一般の群作用や任意の可変fiberへ持ち込まない。
既存の `IdentityG124*` は共通universeの型配置で述べられているため、一般のEからの
特殊化で必要な型移送も、可視写像・状態評価を保つ対応として扱う。

## 6. 固定例

| 既存path・宣言 | 再利用する内容 | G-128で新しく示す内容 |
| --- | --- | --- |
| [ProtocolHolonomy/OneVertexTwoLoopsInput.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/OneVertexTwoLoopsInput.lean)：`oneLoopInput` | 一頂点・二辺名、空の経路等式、`H=⊤` の原始入力 | 同じ入力からEの周囲の群・作用表を生成する |
| [ProtocolHolonomy/OneVertexTwoLoops.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/OneVertexTwoLoops.lean)：`oneLoopData`、`oneLoopSwap`、`oneLoopSwap_noLift`、`oneLoopVertices`、`oneLoopEdges`、`oneLoopFibers` | 恒等・交換の二つの操作、辺名交換の持ち上げ不能、明示的な入力列挙 | 辺名だけを交換する周囲の群の元が不適合で、全状態を固定することを示す |
| [ProtocolHolonomy/OneVertexTwoLoopsVisibleGroup.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/OneVertexTwoLoopsVisibleGroup.lean)：`oneLoopHEquivPermBool`、`oneLoop_H_card_two` | 元の可視群と二点置換群の群同型、濃度2 | 周囲の群の二因子を辺名・状態へ対応させる |
| [ProtocolHolonomy/OneVertexTwoLoopsLiftable.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/OneVertexTwoLoopsLiftable.lean)：`oneLoop_H_lift_eq_bot` | 持ち上げ可能な可視変更は恒等元だけ | 適合部分群の第一因子が自明であることを示す |
| [ProtocolHolonomy/OneVertexTwoLoopsCentralizer.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/OneVertexTwoLoopsCentralizer.lean)：`oneLoop_holonomy_centralizer_top_every`、`oneLoopB2` | 全ての根の中心化群が二点置換群全体、実際のB2の群同型 | 適合部分群の第二因子が全体であることを示す |

最小観測数の `∞,1,2`、最適問い合わせ回数、greedyの選択、Cの実行出力との対応は
G-128で証明する。既存の持ち上げ不能の定理と、新しい観測による判定不能の定理は、
同じ辺名交換の元を使って結び付ける。
