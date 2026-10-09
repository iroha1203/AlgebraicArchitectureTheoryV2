# 数学との対応と証明義務

この文書は、I/O が保持すべき数学的データ、利用できる既存結果、処理系に残る
証明義務を区別する。調査対象は main の `ed16acc02` である。
数学本文・Lean 宣言・研究 report を照合した文献調査であり、Lean の再検証や
新しい target theorem loop の開始は行っていない。

## 1. I/O に必要な区別

| 区別する値 | 数学的な意味と I/O への帰結 |
| --- | --- |
| Law の十分性 / 診断保存 | `q(s)=q(t)` から各 Law 評価の一致が従うことは、評価の降下を与える。診断保存には被覆、係数、実際の cochain map の比較が別に必要である。十分性の成立を診断保存の成立へ読み替えない |
| 係数空間 / 指定障害類 | `H¹` の表示・次元と、特定の cocycle の商類・零性を別々に保持する。同じ `H¹` 上でも入力の変更で指定類は変わる |
| 判定可能性 / 修復値の取得 | 可解性が全補完で一定でも、同じ数値の補正が全補完に通用するとは限らない。G-131 はこの二つの十分性を区別する |
| 方程式の解 / actual repair | 方程式への代入確認、意味状態への復元、制限との可換性、貼り合わせを分ける。actual repair は実際の意味状態と元の操作への対応を保持する |
| 名前付き辺 / 端点の組 | 同じ始域・終域を持つ別操作を別の生成元にする。経路は辺名の順序付き列であり、合成後も原始辺へ戻れる |
| 面の各出現 / 辺の集合 | 面には同じ辺が繰り返し現れうる。位置・向き・整数係数を保持し、微分では出現ごとの符号付き和を取る |
| Law 値の逆像 / chart 写像の逆像 | G-135 の `labelValueFiber` による target 部分集合と、セル比較から生じる chart fiber は異なる型にする |
| 一次診断の保存 / 全複体の保存 | `H¹` 同型は錐全体の非輪状性を意味しない。G-134/G-135 の面複製は `H¹` を保存しつつ非零の `H²` 余核を生じる |
| 局所解の同型 / 共有値の一致 | G-130 の厳密な貼り合わせでは、元の共有辺・頂点の値、内部自由度、再同定の射を保持する。局所可否と同型類だけでは復元できない |
| 有限提示 / 有限な意味対象 | 生成元と関係が有限でも、全操作語は有限とは限らない。特定の有限語の評価、生成元上の保存検査、商での一般的な語の等値判定を別の問いにする |
| 係数の変更 / 表示の変更 | `ℤ`、有限体、`ℚ` は異なる係数である。有理化は torsion を失いうる。係数変更を無記録の最適化にせず、比較写像と適用条件を持つ別計算にする |

## 2. 既存結果を使う箇所

以下の表は新規の定理要求ではない。表中の Research 成果を Formal へ移す場合は
`unported (Research-proved)` の蒸留作業であり、既存結果の再証明を新しい研究目標に
数えない。処理系がこれらの入力条件を構成・検査したことも、宣言名の存在だけからは従わない。

| 既存構成 | 一次資料と宣言 | I/O に必要な原始データと条件 |
| --- | --- | --- |
| Atlas の標準解像度 | [Rising Sea 第3章 §§3.1–3.4](../../../outreach/paper/rising-sea/ja/06-resolution-invariance.md)。補題3.2、定理3.4、構成3.6、命題3.14 | source の対象族、Law 評価、reading。有限計算では対象の全列挙と値の等号判定。診断比較には各セルの台と実際のセル写像を追加構成する |
| SAGA の係数比較 | [Exactness.lean](../../../Formal/AG/SemanticRepair/Saga/Exactness.lean): `relationSound_of_stateCorrespondence`, `phi_injective`, `phi_surjective`, `phiEquiv`, `phi_natural` | 独立に生成した意味側の生成元・関係と方程式側の係数、生成元上の対応と作用。関係の健全性・完全性、生成元の全射性を確かめる |
| SAGA の複体と障害比較 | [KappaComparison.lean](../../../Formal/AG/SemanticRepair/Saga/KappaComparison.lean): `kappa1_delta0`, `kappa2_delta1`, `kappaH1AddEquiv`, `residual_correspondence_class`, `sagaComparison_zero_iff` | 同じ cover 上の係数比較、制限の自然性、局所状態の対応。商上の比較だけでなく、その生成元上の写像を保存する |
| SAGA の actual global repair | [TrueSheafDescent.lean](../../../Formal/AG/SemanticRepair/Saga/TrueSheafDescent.lean): `exists_unique_glue`, `globalRepair_nonempty_iff`, `sagaGroundedGluing`, `sagaEquationGlobalLift` | 局所非空性、torsor 作用、選択 topology に対する層条件、cover の所属、空交差の正規化。大域状態とその制限を返す。固定した整合族の貼り合わせの一意性と、大域修復全体の一意性を区別する |
| G-127 の可逆操作と持ち上げ | [report の宣言対応](../../../research/reports/G-127-aat-reversible-protocol-holonomy.md)、[FiniteSelectedAllLifts.lean](../../../research/lean/ResearchLean/AG/ProtocolHolonomy/FiniteSelectedAllLifts.lean): `mem_finiteSelectedAllLifts`, `finiteSelectedAllLifts_eq_nil_iff` | 頂点 fiber、名前付き辺、実作用、経路等式、可視変更。有限手続きは完全な有限表と等号判定を要する。木、holonomy、中心化群、lift は生成結果 |
| G-128 の最小観測 | [FiniteMinimum.lean](../../../research/lean/ResearchLean/AG/MinimalCompatibilityObservations/FiniteMinimum.lean): `minimumOrWitness_correct`、[QueryOptimum.lean](../../../research/lean/ResearchLean/AG/MinimalCompatibilityObservations/QueryOptimum.lean): `optimalQueries_eq_minObservations` | 候補変更群、実作用、操作保存から求める適合部分群、選択可能な観測。最小性の対象族・費用・有限列挙を固定する。不能時には区別できない不適合変更を返せる |
| G-129 の可換核と持ち上げ障害 | [Defect.lean](../../../research/lean/ResearchLean/AG/AbelianLiftingObstruction/Defect.lean): `defect_cocycle`、[Solutions.lean](../../../research/lean/ResearchLean/AG/AbelianLiftingObstruction/Solutions.lean): `obstructionClass_eq_zero_iff_solution` | 原始辺作用、射影、その可換核、核輸送、名前付き面と3-cell。cocycle 条件には固定 target の syzygy 条件等を要する。微分や defect を完成した入力にしない |
| G-130 の相対修復と厳密な復元 | [StrictCoverRestoration.lean](../../../research/lean/ResearchLean/AG/RelativeRepairComposition/StrictCoverRestoration.lean): `glueObjects`, `objectEquiv`, `equivalence`、[NativeEquationBridge.lean](../../../research/lean/ResearchLean/AG/RelativeRepairComposition/NativeEquationBridge.lean): `originalRepairEquationEquivalence` | 元の固定部分、補正候補、共有辺・頂点、内部 kernel、元の操作と再同定。対象の復元だけでなく全射の復元を保持する |
| G-131 の修復・観測双対性 | [FiberSufficiency.lean](../../../research/lean/ResearchLean/AG/RepairObservationDuality/FiberSufficiency.lean): `decision_sufficient_iff`, `numerical_sufficient_iff`, `decision_numerical_differ`、[FiniteMinimumPlan.lean](../../../research/lean/ResearchLean/AG/RepairObservationDuality/FiniteMinimumPlan.lean): `plan_spec`, `plan_none_iff`, `plan_card` | 同じ原始入力族から作る方程式と query。可解性だけを決める観測と、具体的補正値を返すための観測を分ける。線形の核条件の適用には定理に明示された成功基準点等を必要とする |
| G-132 の零性反映 | [IntegralVisibleReflection.lean](../../../research/lean/ResearchLean/AG/VisibleCycleReflection/IntegralVisibleReflection.lean): `exists_full_potential`, `exists_integral_correction` | 原始 graph、可視辺、係数座標と比較。可視性の条件から整数補正へ戻す定理であり、任意の有理診断から任意の整数障害への零性反映ではない |
| G-133 の欠損・合成 | [LawDefectDecomposition.lean](../../../research/lean/ResearchLean/AG/AtlasDefectComposition/LawDefectDecomposition.lean): `lawH1KernelFamilyEquiv`, `lawH1CokernelFamilyEquiv`, `lawH1Defect_sum`、[ConeExactSequence.lean](../../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeExactSequence.lean): `cone_short_exact` | 実 cochain 比較、Law の各発生ラベル、kernel/cokernel、標準錐の射。欠損を単一の次元だけへ圧縮せず元・写像・分解を保持する |
| G-134 の診断保存細分化 | [IncidenceComparison.lean](../../../research/lean/ResearchLean/AG/FaceRelationSubdivision/IncidenceComparison.lean): `IncidenceSupportedComparison`、[OperationPathFunctor.lean](../../../research/lean/ResearchLean/AG/FaceRelationSubdivision/OperationPathFunctor.lean): `lawR_append`, `lawS_append` | セル名、平行辺、loop、面内の重複、部分セル比較と退化の符号付き和。原始操作列から比較と homotopy を作る |
| G-135 の係数・fiber と有限判定 | [NativeDiagnosticMatrices.lean](../../../research/lean/ResearchLean/AG/AtlasCoefficientFiber/NativeDiagnosticMatrices.lean): `nativeTMatrix_represents`, `nativeTauMatrix_connectingTau`、[FinitePreservationDecision.lean](../../../research/lean/ResearchLean/AG/AtlasCoefficientFiber/FinitePreservationDecision.lean): `primitiveDiagnostic_eq_blockDefect`, `allAPreservationDecision_eq_true_iff`, `lawPreservationDecision_eq_true_iff` | 同じ原始部分セル比較と台から順像・fiber 適合・transgression を生成する。有理行列と rank は出力。一般の混在面では fiber 項は適合部分 `R_A` であり、全 fiber の `H¹` の直和へ無条件に置き換えない |

G-133 と G-134 の report には全 target の完了認定がある。G-135 も、[最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5318#issuecomment-6078269788)と[完了記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6078348119)により、
Research の固定 T0・A–E・W 全体を `target-theorem-proved` と認定され、基準版 `ed16acc02` にマージ済みである。
Formal への移植は `unported (Research-proved)`。Research 全体 build と Formal local build・移植は未実施であり、
Research での証明完了と区別する。CI の Formal build 等6 step も `SKIPPED` と記録されている。

## 3. 有限提示から使える保証

[ProtocolFinitePresentation.lean](../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolFinitePresentation.lean)
は、頂点ごとの有限状態数、名前付き操作の表、観測値、生成関係の充足から、
経路全体の作用と射を構成する。完成した関手や全経路の作用を入力しない。
この数学的 record の充足証拠は、I/O では原始表から検査して作る。

有限個の生成関係が与えられた任意の商で、すべての語の等値を決定できるという
結論は、この構成からは得られない。I/O は次を区別する。

1. 有限に記述された経路を、既知の原始操作で評価する。
2. 有限表・正確なアフィン式等の対応済み意味領域で、評価された操作を比較する。
3. 候補写像の生成元上の保存を検査し、合成の意味論から全有限経路の保存を得る。
4. 関係で生成される商の語の等値そのものを問う。

第4項は、選んだ意味領域の決定手続きがある場合に判定する。
打切りまで反例が見つからないことを、商での等値や非等値の証明にしない。

## 4. 新仕様に残る証明義務

今回の調査では、I/O を決定するために新しい Rising Sea の一般定理を必要とする
不足は特定されなかった。以下は新しい DSL・処理系についての未証明義務である。
既存の数学の不足、新しい研究ループ、既に証明済みの処理系保証として扱わない。
仕様の確定を進め、実装時には各義務に対する検証方法と証拠を対応させる。

### P1. 型付き DSL と導出の健全性

- **原始入力:** 型検査された ArchMap、import を含め固定した Law、固定した組込み意味論。
- **必要な仮定:** 組込み演算が公表された意味論を実装すること。有限列挙の完全性は
  対応済み有限型の構成から、商写像の整合性は生成関係の検査から得る。
- **結論:** 評価された値は宣言された型の意味を持つ。確定判定と反例は参照意味論で
  正しい。生成物の導出の葉は二入力と固定演算に到達する。コンパイルと再利用検査は
  その意味を保存する。
- **既存との差:** [エンジン自身の Law](../archsig_atom_law_engine/engine_laws.md) は
  L01–L13 と有限検算を与えるが、新しい具体 DSL 全体の処理系保存定理ではない。
  G-123 等の有限 decoder は、対象となる数学的表示についての構成である。
- **必要な I/O 保証:** 型付き結果の接続、検査済みの射、導出元、版をまたぐ再利用の判定。
- **分類:** 製品固有の意味論・実装正確性の義務。Rising Sea の理論上の不足ではない。

### P2. 不完全な観測からの確定判定

- **原始入力:** 未観測値を区別する部分的 ArchMap と Law。仕様で許容する補完の集合を
  `Comp(A,L)` と書く。対象の存在・有限領域・既知の値・既存の関係を保存する補完だけを取る。
- **必要な仮定:** `Comp(A,L)` が空でないこと、未観測を既知値へ置換すると補完集合が
  狭まること。空である場合は観測・型・提示条件の不整合として扱い、空虚な全称で成功しない。
- **結論:** 確定した真偽はすべての許容補完で同じである。具体的反例の成立に必要な値が
  すべて既知なら、その反例は追加観測で失われない。反対の判定になる二補完は
  現観測の不足を証明する。数値の修復値を返すときは、その値の妥当性も別途示す。
- **既存との差:** G-128 の識別と G-131 の情報 fiber は、この原則の数学的特殊化と
  判定／数値出力の違いを既に与える。新 DSL の関係演算、必須フィールド、適用条件、
  欠落の伝播に対する一般的な健全性は別途必要である。
- **必要な I/O 保証:** 不足理由、欠落しても保持される対象と Law instance、確定反例の再利用、
  追加観測要求と未確認候補の区別。
- **分類:** 製品固有の部分情報意味論の義務。任意の補完集合で停止する完全判定は要求しない。

### P3. 原始 support から局所状態・大域状態を生成する接続

- **原始入力:** 有限の値座標と原始操作、Law の局所化規則、各方程式の全 operand と
  support。線形の場合は原始式の正確な係数を用いる。
- **必要な仮定:** context の制限で式の評価が可換すること。cover が値座標を覆い、
  各方程式の全 support を少なくとも一つの patch で読めること。重なりは実際の制限先
  であること。torsor を使う場合は局所解の存在を生成し、差と作用の条件を確かめる。
- **結論:** 各 context の状態をその上の方程式を満たす値割当として独立に構成したとき、
  整合する局所割当は一意に貼り合い、全方程式を満たす。アフィンな場合は同次解係数、
  局所解の差、cocycle、補正、具体的大域解へ接続する。SAGA 比較を称する場合は、
  さらに独立に構成した意味側・方程式側の生成元対応から係数比較を作る。
- **既存との差:** [三操作の局所・大域計算](../archsig_atom_law_engine/local_global_example.md)
  は一つの具体的生成例、Formal の SAGA は適用条件を備えた一般定理である。
  G-130 の厳密な復元も別の原始表示について既にある。新 DSL の任意の対応済み
  局所化規則からこれらの対象・仮定を生成する一般接続は、その DSL 固有の義務となる。
- **必要な I/O 保証:** cover の導出、層条件の成立根拠、障害零から実際の修復状態への接続。
- **分類:** 選択した有限 realization の証明義務。一般の局所化規則で無条件に層条件を
  保証する命題は要求しない。条件が確かめられない instance は、その条件を保持して返す。

## 5. 証明課題にしてはいけない主張

- Law の十分性だけから、任意の被覆・係数の診断保存を導くこと。
- `dim H¹=0` または指定類の零性だけから、局所解・状態対応・層条件を伴わない
  actual repair を導くこと。
- 同じ source が多く現れることを、同じ Law 値の係数座標の重複と見なすこと。
  Law 添字が異なる発生ラベルの重複度は、これと別に保持する。
- 全操作語を有限深さまで調べた結果から、無制限の商の語の等値を判定すること。
- G-135 の混在入力の `R_A` を、条件なしに全 chart fiber の `H¹` の直和とすること。
- 有理係数で得た零性を、係数比較と反映条件なしに整数係数の零性へ戻すこと。

これらは証明すべき不足ではなく、必要な仮定または対象の違いを欠いた主張である。
I/O は対象、係数、比較写像、適用条件を保持することで、それぞれの成立済み結果を
正確に次の計算へ渡す。
