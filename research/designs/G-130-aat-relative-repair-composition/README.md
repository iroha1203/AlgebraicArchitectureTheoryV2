# G-130：全変更範囲の相対修復を合成・分類するための構成

[固定target A–FとW1–W5](../../goals/G-130-aat-relative-repair-composition.md)の証明方針を定める。
入力・結論・完了条件はGOALに従う。以下の分割は証明依存による設計であり、
各段階の実行・査読・PRの記録はtracking Issueへ置く。

## 1. 一次仕様との対応

| GOAL | [n1017](../../../docs/note/n1017_aat_relative_boundary_repair_and_observation.md) | 構成の要点 |
| --- | --- | --- |
| A | §2.1–2.2・2.5、§3.1の系 | 実操作の固定とcochainの零、許された再同定と次数0の制限 |
| B | §2.3–2.5 | 次数ごとの完全列、再同定の延長、局所差と実defectの接続 |
| C | §2.6・3.1 | 候補を残した内部変数消去、対象・射の相互逆、共有セルの厳密一致 |
| D | §3.4 | 同じ面座標の商、双対分離、証拠支持の極小横断集合 |
| E | §3.2・3.5–3.6 | 一点環境、記号的右辺、実分解からの縮約・復元・自然同型 |
| F | §5.1 | 全アフィン写像の全核、実輸送、実修復と作用の往復 |
| W1–W5 | §5.8、§2.5、§5.6、§5.7、§5.2 | GOALの指定データを同じ一般定理へ適用 |

## 2. 既存宣言の再利用と新しい対応

Research pathは `research/lean/ResearchLean/AG/` からの相対である。
各行では宣言の入力型に対する部品の再利用と、固定targetへ接続する証明義務を分ける。
宣言の参照版はactive化時にtracking Issueへ固定する。

### 2.1 実核・実補正・経路・解の分類

| 既存path・宣言 | 再利用する部分と入力条件 | 新しく構成・証明する部分 |
| --- | --- | --- |
| `TransportCoherence/FinitePresentation.lean` の `FiniteTransportPresentation`、`RewritePasting` | 頂点・型付き辺・面・3-cell、前後の文脈を持つ書き換え | A・B・E：閉じた部分表示、包含、制限、有限被覆、分割時の全辺出現の置換 |
| `AbelianLiftingObstruction/OriginalTowerPresentation.lean` の `OriginalTowerPresentation`、`toTower` | 元辺・core・基準持ち上げを保持した塔 | A・F：各部分表示への入力の制限、任意の元アフィン辺による入力 |
| `AbelianLiftingObstruction/KernelTransport.lean` の `kernelTransportHom`、`kernelTransportHom_fac`、`kernelTransportHom_unique` | 同じ圏の塔と強い実辺から、全核の輸送を実因子分解と一意性で構成 | A：制限先でも同じ輸送を得ること、補正零と固定実辺の一致 |
| `AbelianLiftingObstruction/LocalCoefficients.lean` の `pathTransport_append`、`PathKernelTransport.lean` の `kernelTransportHom_comp` | 経路の連結と実射の合成に沿う同じ核輸送 | A・E：部分表示・辺置換との交換、実分解からの $`\rho_e=\rho_2\rho_1`$ |
| `AbelianLiftingObstruction/Cochains.lean` の `C0`–`C3`、`d0Hom`–`d2Hom`、`d1_d0`、`d2_d1` | 同じ経路・輸送による微分 | A・C：制限との交換、相対複体、範囲ごとの部分複体、線形座標 |
| `AbelianLiftingObstruction/Defect.lean` の `defect_cocycle` | 元の実3-cell整合から得る $`d^2\delta=0`$ | A・B：相対部分への所属、制限と実defectの交換 |
| `AbelianLiftingObstruction/Correction.lean` の `correctedEdge_core`、`correctedPath_fac`、`correctedPath_core`、`correctedDefect_eq` | 実辺・実経路の補正、core保持、同じ実defectの変化 | A・C・E：固定部分・禁止候補の条件、制限・分割・復元との交換 |
| 同ファイルの `authoredSyzygy_correction_invariant`、`correctedPathKernelTransport_eq` | 核補正後も保持される実3-cell整合と経路輸送 | A・E：相対条件と分割後の型付き書き換えへの適用 |
| `AbelianLiftingObstruction/Cohomology.lean` の `cochainComplex`、`firstShortComplex`、`secondShortComplex` | 加法群のnativeな複体とコホモロジーの計算表示 | A・B・E：相対・範囲付き複体の計算商、接続写像・分割比較との対応 |
| `AbelianLiftingObstruction/Solutions.lean` の `Solution`、`solutionCorrection`、`solutionOfCorrection`、`solution_nonempty_iff_correction` | 独立した実解と核補正の往復 | A：固定部分・禁止候補を保つ相互逆、groupoidの対象と射 |
| `AbelianLiftingObstruction/SolutionTorsor.lean` の `solutionAction`、`solutionDifference`、`solutionAddTorsor` | 実解上の $`Z^1`$ 作用と差、非空な実解のnative torsor | A：相対・範囲付き作用への制限、同じ実辺の対応 |
| `AbelianLiftingObstruction/VertexGauge.lean` の `vertexGauge_correction`、`vertexGauge_edge_arrow`、`H1Classification.lean` の `vertexAddAction`、`solutionOrbitEquivH1` | 元の実射への頂点作用、軌道と $`H^1`$ | A–C：全作用元を射として保持した相対groupoid、自己同型、制限・descent |
| `AbelianLiftingObstruction/ReferenceLiftInvariant.lean` の `solutionChangeReference`、`defect_changeReference`、`obstructionClass_changeReference` | 同じ実解を保つ参照持ち上げの変更 | A・C・E：候補のアフィン固定条件の同時輸送、局所生成との交換 |
| `AbelianLiftingObstruction/GroupExtension.lean` の `kernelEquiv`、`kernel_comm`、`selectedStrong`、`selectedLowerStrong`、`transport_kernelEquiv`、`transport_bijective` | 任意の群射影 $`\pi:E\to H`$ と任意の実辺 $`e\in E`$ に対する全核・強さ・共役輸送 | F：アフィン射影の全核と平行移動の同定、共役と線形成分の評価一致、元辺・指定比較・3-cellの入力構成 |

`GroupExtension.original` と高水準の `input` は元辺を恒等に取る経路である。
Fでは上表の任意射用APIを使い、`OriginalTowerPresentation` に元のアフィン辺を渡す。
`GeometryKernelTransport.lean` の `actualKernelCommGroup`、`identityTransport_eq_id`、
`authored_centralizes` は指定された有限geometryの全核の例であり、Fの全アフィン核の
同定・任意輸送はFの同じ射影から証明する。

### 2.2 Mathlibと有限入力の構成

Mathlibのpathは `Mathlib/` からの相対であり、版はrepositoryの依存設定に従う。

| 既存path・宣言 | 適用先と残る接続 |
| --- | --- |
| `CategoryTheory/Action.lean` の `ActionCategory`、`hom_as_subtype`、`stabilizerIsoEnd`、群作用からの `Groupoid` instance | A–C：$`\operatorname{Multiplicative}(C_S^0)`$ の実修復への作用を構成する。射の作用元を保ち、安定化群と $`\ker d^0`$、実再同定、厳密貼り合わせを対応させる |
| `Algebra/Homology/HomologySequence.lean` の `ShortComplex.ShortExact.δ`、`homology_exact₁`–`homology_exact₃`、`δ_eq` | B：相対複体の次数ごとの短完全列を先に構成する。計算商との同型を通し、$`(-h_U,-h_V)`$ の持ち上げから接続像の符号と実defectを対応させる |
| `LinearAlgebra/Dual/Lemmas.lean` の `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`、`Submodule.dualQuotEquivDualAnnihilator` | D：同じ面座標の商で双対分離を使う。名前付き候補の像と証拠支持、極小横断集合への対応を構成する |
| `LinearAlgebra/AffineSpace/AffineEquiv.lean` の `AffineEquiv.linearHom`、`constVAddHom`、群構造 | F：nativeな全アフィン自己同型と実射影を使う。射影の全核が平行移動全体であること、実共役、元の写像評価との一致を証明する |
| `LinearAlgebra/Matrix/ToLin.lean` の `Matrix.mulVecLin`、`LinearAlgebra/Isomorphisms.lean` の商同型API | C・D：実微分を座標行列へ対応させる。像・kernel・商の数学的仕様と、有限入力から生成したデータの正確性を結ぶ |
| Research `ProtocolHolonomy/FiniteDirectDecision.lean` の `ExplicitEnumeration.toFintype`、`pi`、`product`、`MinimalCompatibilityObservations/FiniteAmbientTable.lean` の `ExplicitEnumeration.sigma`、`sum` | C・F：完全性付きの有限入力リストから関数表・直積・直和を生成する。`toFintype` は要素の、`pi` は添字の等値判定を要求する。有限体と基底から入力リストを構成し、線形消去・section・復元を別途証明する |
| `Formal/AG/Measurement/FiniteRegime.lean` の `FiniteLinearSystemSolver.ofFiniteSemiring/ofFiniteField`、`FiniteLinearCosetNormalizer.finiteRepresentativeCertified/ofFiniteField` | C・D：有限添字・有限体・等値判定から行列方程式の有限探索と商の代表を構成する既存部品。`solve_isSome_iff` は可解性の判定契約なので、返却値の正確性を具体的な `find?` 定義から追加証明する。商代表のcanonical性から線形sectionは得られない |
| Research `TwoPhase/CoefficientComplex.lean` の `coordinateSupport`、`coordinateSupport_eq_span` | C・D：禁止候補の零条件を基底添字上の支持部分空間へ移した後に使う。部分表示の制限や実全核との座標対応は2.1で構成する |

有限列挙や抽象的な線形同型だけで、Cの生成器の停止・正確性が得られるわけではない。
行列の消去、核・像の基底、線形sectionを入力データから計算し、上表の数学的対象との
一致を示す。sectionを選択公理で得ただけの構成は、この有限生成の出力に使わない。
`FiniteRegime.lean` は `noncomputable section` 内にあるため、定義と可解性の定理を参照する
ことと、今回の明示入力で実行可能な生成器を得ることを分け、後者はfocused checkで検証する。

### 2.3 対象を比較して使う関連資産

| 既存資産 | 入力・結論の相違と用途 |
| --- | --- |
| Research `CrossStageCoherence/RelativeObstruction.lean` | 固定coreを持つedge sectionに相対的な非可換障害を扱う。Aの $`\ker(C(K)\to C(P))`$ は新しく構成する |
| `Formal/AG/Cohomology/CochainComparison.lean` の `AdditiveThreeTermComplex.Equivalence.toH1AddEquiv` | 三次数で相互逆なcochain写像を与えた後の $`H^1`$ の移送に使える。次数ごとの空間が増える辺分割には、そのままの同型を仮定せずEの可縮部分の分解を構成する |
| `Formal/AG/Site/Descent.lean`、`Formal/AG/SemanticRepair/Saga/TrueSheafDescent.lean` | sheaf条件を入力に取る集合値の貼り合わせ。B・Cは同じ実再同定を射として持つgroupoidの貼り合わせを証明する |
| `Formal/AG/Cohomology/BoundaryHolonomy.lean` の `TwoChartConnectingHomomorphism`、`BoundaryResidue.lean` の `BoundaryResidueHypotheses` | 接続cochain・cocycle性やsoundness/completenessをfieldとして受け取る。Bの $`H^1\to H^2`$ の接続は短完全列から構成する。特定siteの `ReadingFunctoriality/TopologyChangeFiring.lean` のprivateなMayer–Vietoris例はその証明構成の参考になる |
| `Formal/AG/SemanticRepair/AdditiveH1.lean` の `additiveFiberTranslation_unique` | 対象間の並進射が一意な場合のAPI。A・W3で保持する非自明な自己同型は作用groupoid側で扱う |
| Research `ObstructionDiagnosticBridge/SpecifiedAffineObstruction.lean`、`ResolutionInvariance/LawValueBlockComparisonFiberPrimitive.lean` | 前者は指定Čech入力の $`H^1`$、後者は $`\mathbb Q`$ 値incidenceの双対論。実全核・相対面微分への同一視には別の対応が要るため、F・Dの直接の定理入力にはしない |
| Research `UniformInvariance/ExecutableRationalRank.lean` の `columnGram_det_ne_zero_iff`、`rationalMatrixRank_eq_rank` | $`\mathbb Q`$ 上のGram行列式による計算。有限体では非零列のGram行列が零になるため、Cの有限体上の消去へ直接流用できない。有限探索と数学的仕様を結ぶ構成を参考にする |
| Research `OperationRepair/FiniteTables.lean` の `FiniteTable`、`ofFn`、`get_ofFn` | 有限データの配列表現として利用可能。operationを保つ同値関係の修復を扱うG-126の分類定理は、核補正・頂点作用を扱う今回の分類とは対象が異なる |
| Research `ProtocolHolonomy` の経路・holonomy構成 | `FixedFDirectedMultigraph` の `SignedPath` と、今回の型付き表示・書き換えは入力が異なる。Eの分割は2.1の実経路APIで構成し、既存holonomy定理を使う場合は経路・評価・作用の対応を追加する |

## 3. 相対化から全修復groupoidへ

閉じた部分表示のセルは元のセルの部分型として表し、経路と書き換えの所属を追う。
制限の合成・恒等・微分との交換を先に揃える。零延長は各次数の全射性の証明に使い、
複体の写像として必要なのは制限と差写像である。

相対補正を独立した実修復に往復させた後、元の0-cochainを射として持つ作用groupoidを
構成する。射の合成は和であり、異なる作用元の同一視を行う前に自己同型を計算する。
禁止候補については $`d^0b`$ の該当成分も零となる部分群を使う。

Bの二領域descentでは、共有部分の0-cochainを一方へ延長して対象を厳密一致させる。
射の全忠実性は共有頂点上で一致する0-cochainの一意な貼り合わせから得る。
局所差の符号は差写像 $`r_U-r_V`$ と合わせ、持ち上げ $`(-h_U,-h_V)`$ の微分が
$`(\delta|_U,\delta|_V)`$ になることから接続像を求める。

## 4. 局所線形消去と厳密合成

有限生成の入力には明示した有限体演算・有限添字・実核の基底と実座標の対応を使う。
相対辺空間を $`X_i\oplus Z_i`$ に分け、$`X_i`$ に含めるのは非共有の常時許容辺だけとする。
行簡約から像の基底、商写像、線形section $`s_i:\operatorname{im}D_i\to X_i`$ を生成する。

局所の座標化と復元にはn1017の次の式を使う。

```math
\operatorname{rec}_i(z,k)=(s_i(r_i-F_iz)+k,z),\qquad
\operatorname{coord}_i(x,z)=(z,x-s_i(r_i-F_iz)).
```

作用の内部成分は $`\gamma_i b=a_i b-s_iD_i a_i b`$ と構成する。
$`D_ia_i+F_ic_i=0`$ から $`(z,k)\mapsto(z+c_ib,k+\gamma_ib)`$ が対象条件を保ち、
復元が元の $`d^0b`$ と交換することを示す。共有辺の値は $`z_i`$ に全て残っているため、
共有部分への制限は内部の $`k_i`$ に依存しない。

Glueの対象には共有辺の一致、射には共有頂点の一致を課し、セルごとの一意な
貼り合わせで大域の補正と再同定を得る。局所式の相互逆性とこの一意性により、
大域でも両合成が対象・射で恒等になる。
公開関係の解から内部成分を零として一つの実修復を作り、内部成分全体を動かして全解を戻す。
各 $`S`$ の解を先に列挙する代わりに、生成済みの候補座標へ零条件を課す経路を用いる。

被覆・sectionなどの表示変更は $`\operatorname{coord}'\operatorname{rec}`$ で比較する。
中間消去では未組立ての領域との共有辺と全候補を残し、比較の合成則を同じ復元から導く。

## 5. 双対分類と再利用

大域の常時許容列の像を商に取り、局所合成後の消去と同じ可解性・復元を与えることを示す。
候補列は名前付きで残し、有限次元の双対分離を $`o\notin\mathsf R_S`$ へ適用する。
得た評価の支持集合から横断集合条件を作り、包含極小性を移す。
有限体上では双対評価も有限データで扱え、空の支持・空の証拠族も同じ定義で計算する。

記号的右辺では $`r_i`$ の項だけをアフィンに変える。
kernel・section・作用の線形部分が $`r_i`$ に依存しないことを用いて更新則を示す。
G-131へ渡すのは、生成された同じ行列・候補名・実defectへの対応・復元写像である。

文脈同値の逆向きでは共有修復値 $`t`$ の各辺に平行な禁止候補を追加し、
基準実操作を $`\tau_{t_e}\widetilde L_e`$ とする。元の辺との恒等比較の面から
$`h_e=t_e`$ を導き、二領域の共有関係の差を検出する。

## 6. 内部辺分割

まず有限表示の全ての辺出現を置換し、面と3-cellの終点・書き換え順序を保つ。
実分解の輸送平方から $`\rho_e=\rho_2\rho_1`$ と縮約式を得る。
逆関手の補正を $`(0,h_e)`$、新頂点の再同定を $`\rho_1b_s`$ とし、
自然同型の新頂点成分を元の $`h_1`$ とする。

複体の新自由度は $`b_w-\rho_1b_s`$ と $`h_1`$ を座標に取ると恒等微分の二項複体になる。
この分解からコホモロジーと障害の比較を作り、常時許容列の像が一致することから
公開関係・候補列・双対証拠支持も対応させる。
新頂点での自由度を持つ実修復の対象集合と、再同定後の分類をそれぞれ計算する。

## 7. 証明の依存順と検証

| 数学的な段階 | 依存 | 終了時に対応させるもの |
| --- | --- | --- |
| 部分表示・相対修復、アフィン実現 | G-129 | A・Fの実辺、微分、固定条件、対象・射 |
| 全補正のdescent・相対障害 | A | B・W5、範囲付きの反例W2 |
| 全範囲の有限生成と合成 | A・F | Cの相互逆とW1・W3、表示比較 |
| 双対分類・記号的更新・文脈同値 | C | D、Eの該当項、G-131へ渡す同じ行列 |
| 内部辺分割と全体の指定例 | A・C・D | Eの比較、W1–W5の一般定理への接続 |

Leanの検証は[AAT guideline](../../../docs/aat/guideline.md#lean-build-運用hard-rule)に従う。
親が指定する単一の非aggregate fileのfocused checkを基本とし、必要な依存moduleだけを
親がtargeted checkする。Research package全体のbuildは実行しない。
完了時にはGOALの全条項と宣言、実操作への往復、前提の生成・使用、指定例をreportで対応させる。
