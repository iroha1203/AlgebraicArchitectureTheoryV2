# G-133：生成比較・欠損対象・台署名の構成

[GOAL T0・A–F・W](../../goals/G-133-aat-atlas-defect-composition.md)を実装ループで進めるための設計。
固定targetはカードとそこから指定した節にあり、宣言対応は[再利用対応表](reuse-map.md)、
台の構成は[台署名](support-signatures.md)、原始入力と評価値は[指定例](witnesses.md)に置く。
ここで計画する新しい接続・定理は証明義務である。

参照するrepository版は `aa544f1755484cb05894f7fb54631be8dd7203a7`。
Leanは `v4.28.0`、mathlibは `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。
active化の際はGOAL・共通基準・既存宣言の参照版をtracking Issueに固定する。

## 1. 候補07全体との対応

| 原文の要求 | GOAL | 構成の中心 |
| --- | --- | --- |
| 同じLaw・台・セルからの三段比較、直接比較との一致 | T0・A | 部分incidence射の合成と生成手続きの可換性 |
| 六項完全列、相殺写像、二つの欠損公式 | B | 中間H¹の実類を前段の余核へ送る写像 |
| 写像錐、他次数の寄与 | C | 三項複体とmathlib複体の同定、次数−1を含む錐 |
| Lawごとの直和、指示Lawによる実現 | D | G-104/G-107の既存分解を錐・相殺へ延長 |
| 台によるセル選択の商と普遍性 | E | 全セルの復元を持つ商の圏、Law族の重複度 |
| R14(iv)の台制限・欠損加群 | E | 比較自然変換と点ごとの核・余核 |
| R14(v)(vi)の錐の合成・有限多段filtration | F | 標準triangleと累積比較のtower |
| 同じ実入力での非零相殺 | W1 | 真に異なる三readingと二つの閉路の生成比較 |
| 弱い同一視・次数省略の検出 | W2・W3 | 同一診断値と異なるセル、錐の追加項 |

六項完全列、Galois接続、自由可換モノイド、錐のtriangleは標準数学を使う。
新規の仕事は入力からの生成・既存APIとの同定・同じ例での発火・保持する構造の特定にある。
R14の構成部分も受入条件に含め、相殺公式だけでGOALを閉じない。

## 2. 許容比較の合成を先に閉じる

### 2.1 入力幾何の圏

Sourceを固定した対象を $`(q,N)`$ とし、粗→細の射に既存の
`TargetSupportedNerveMorphism` を使う。比較因子・cochain写像を独立のfieldとして足さない。
任意の二つの隣接射から次を構成する。

| 成分 | 合成の式 | 放電する条件 |
| --- | --- | --- |
| reading因子 | $`\pi_{01}\circ\pi_{12}`$ | Source上で可換であることを示し `comparisonFactor_unique` へ渡す |
| chart | $`c\mapsto M_{01}.\mathrm{chartMap}(M_{12}.\mathrm{chartMap}(c))`$ | chart台の包含を二回適用 |
| edge | $`e\mapsto M_{12}.\mathrm{edgeMap}(e).\mathrm{bind}(M_{01}.\mathrm{edgeMap})`$ | `none` の二経路それぞれで端点が同じchartへ写る |
| face | edgeと同じ `Option.bind` | 前段・後段どちらで退化しても三つの合成辺が `none` |

最後の行は既存のhereditary条件を使う。部分的に辺を残す面の縮約は、候補08の別の
許容比較に属する。G-133ではT0の型を任意に量化し、その全体で合成を閉じる。
全射chart写像やC0–C6を後から課すとW1の後段を除外するので、合成の入力に加えない。

恒等には既存 `identityMorphism` を利用できる。型が持つ証明引数の相違を処理する
extensionalityとidentity・associativityを整えた後、生成Homの等式へ進む。

### 2.2 既存の生成式との一致

`generatedPullback0` は座標写像との合成、次数1・2は `Option.elim 0` による引き戻しである。
辺・面では「両方mapped」「後段でnone」「前段でnone」を評価式から照合する。
Law・値は `lawDescend_comparisonFactor` で同定する。

部分集合比較では $`\pi_{02}^{-1}A=\pi_{12}^{-1}(\pi_{01}^{-1}A)`$ に沿う
subtype同定が必要になる。cochain写像だけでなく、セル同定・微分・代表元の商写像を
同じ図式へ置く。既存 `h1Map_mk` を使い、H¹合成を全類について証明する。

新しい `ThreeCochainComplex.Hom` の恒等・合成APIが必要なら、Research内で実装し、
既存の全三成分と商の評価則へ接続する。cochainの合成を直接比較の定義にする実装はAを満たさない。

## 3. 完全列と写像錐の接続

### 3.1 相殺の代表元

Bの $`\chi`$ は、線形包含 $`\ker g\hookrightarrow V`$ と商射
$`V\to V/\operatorname{im}f`$ の合成である。
中間cocycle $`z`$ に対し、後段で零になる条件は
$`u_{12}^1z=d_2^0b`$ というprimitiveの存在、前段の像にある条件は
$`z-u_{01}^1a=d_1^0c`$ という粗側cocycle $`a`$ と中間primitiveの存在である。
ここで $`d_i^0`$ の下付きは段階を表す。
二つの条件を既存H¹商の代表元判定へ接続し、相殺する類の意味を得る。

線形代数の一般補題と、生成した三比較への適用を分ける。
`ShortComplex.SnakeInput.snake_lemma`を使う場合も各項・各射をBへ同定する。
直接 `LinearMap.ker`、`range`、`Submodule.mapQ` で証明する場合も、
`Function.Exact` / `LinearMap.exact_iff` などの標準完全性へ接続する。
完全性やrank値をcertificateとして受け取らない。

零欠損の2-out-of-3は、同じ三つのH¹空間で述べる。
`M12.UniformInvariance` は全 $`q_1`$ 部分集合を量化するため、
$`q_0`$ からの逆像族だけの結論と区別する。合成と前後の量化域を混ぜない。

### 3.2 三項複体の埋め込みと次数

`ThreeCochainComplex` は有限次元の次数0・1・2を持つ独自のrecordである。
そのまま `CochainComplex.mappingCone` の入力型にはならない。
零延長した `CochainComplex (ModuleCat ℚ) ℤ`、全Homの移送、恒等・合成との整合、
既存 `H1` とmathlib homologyの線形同型を新たに構成する。
単に錐の名前を付けた別recordを閉じたまま使わない。

カードCの順序 $`(y,x)`$ では各次数は次のとおりになる。

| 次数 | 錐の空間 | 次への微分 |
| --- | --- | --- |
| −1 | $`C^0`$ | $`x\mapsto(u^0x,-d^0x)`$ |
| 0 | $`C'^0\oplus C^1`$ | $`(y,x)\mapsto(d'^0y+u^1x,-d^1x)`$ |
| 1 | $`C'^1\oplus C^2`$ | $`(y,x)\mapsto d'^1y+u^2x`$ |
| 2 | $`C'^2`$ | 零 |

mathlibのbiproduct順序はsourceのshift・targetなので、成分交換を含む明示的な同型を使う。
長完全列の各射、短完全列の包含・商、代表元の符号を追う。
$`H^0D\to\ker H^1u`$ が同型になる条件は $`H^0u`$ の全射性、
$`\operatorname{coker}H^1u\to H^1D`$ が同型になる条件は $`H^2u`$ の単射性である。
一般の短完全列にcanonicalな分裂は要求しない。W3は両条件を一般入力へ紛れ込ませることを検出する。

### 3.3 錐の合成と多段

$`u:C_0\to C_1`$、$`v:C_1\to C_2`$ とすると、最初の二射は
$`(y,x)\mapsto(vy,x)`$ と $`(z,x)\mapsto(z,ux)`$ である。
三射目は標準shiftの符号と合わせ、mathlib
`mappingConeCompTriangle` / `mappingConeCompTriangleh_distinguished` へ同定する。
二射の合成がchain mapとして零とは限らず、標準homotopyを保持する。
H¹の六項列を錐の長完全列とそのまま同一視せず、Cの追加寄与も追う。

多段では累積錐 $`E_i=D(u_{0i})`$ を使い、
$`E_{i-1}\to E_i\to D(u_{i-1,i})\to E_{i-1}[1]`$ を組み立てる。
$`E_0=D(1)`$ はcontractibleなので、零から始まるtowerへ同定できる。
実filtrationには累積錐の射をmapping cylinderで次数別の単射へ置き換え、
逐次商が隣接錐へhomotopy同値となることを帰納的に示す。
一般の比較は単射でないため、元の $`E_i`$ をそのまま部分複体の列と宣言しない。
ここで要求するのは有限filtrationまでであり、n1006 R16のスペクトル系列は後続の課題である。

## 4. Law分解と台署名を合成へ戻す

既存 `lawGeneratedH1BlockEquiv` と `generatedComparisonH1Map_block_naturality` はH¹水準まである。
cochain水準にも三つのblock同値、微分のintertwining、生成比較のcomponent式がある。
これらを零延長へ移し、有限直和とbiproduct・shiftが交換することから錐の分解を構成する。
核・余核・相殺の各射も同じblock分解へ移す。次元等式だけではDの受入条件を満たさない。

台署名はLawを固定する前の全target部分集合から構成する。
同署名は比較複体を名付きセルごとに同定し、複数Lawが同じ署名へ写る場合は直和の
複数成分として残す。[台署名 §4](support-signatures.md#4-lawの再添字づけと加法的な普遍性)
の対象・射を使い、診断値だけの同一視と混同しない。
三段の共通署名により、A・B・C・D・Fがすべて同じ包含方向の制限と可換になる。

## 5. 到達点と依存関係

到達点は同じG-133のproof obligation群である。実装ループの各cycleは、次の終了条件を
満たす単位で選び、実際の宣言・結果・未完項目をreportとtracking Issueに記録する。
内部ファイル名や補題の分割は設計候補であり、固定targetの変更を伴わず調整できる。

| 到達点 | 依存 | 同じcycleで閉じる数学的内容・終了条件 |
| --- | --- | --- |
| M1：実生成比較の合成 | 既存G-104/G-107 | Aの入力比較の合成、全次数・H¹の直接比較等式。W1の全原始データと二射を構成し、直接生成HomがLaw座標の標準同定下で恒等になることを確認 |
| M2：実相殺と欠損 | M1 | Bの全射と完全性、次元公式、代表元の意味、W1の非零相殺とLaw全体の値。一般線形補題だけを終了点にしない |
| M3：標準錐との接続 | M1 | 三項複体の零延長、既存H¹との自然同型、Cの全次数、W3a・W3bの追加寄与 |
| M4：Law別の対象分解 | M2・M3 | Dの錐・核・余核・六項列・相殺の直和同定。指示Lawのselected blockと重複度を確認 |
| M5：台による構造の分類 | M1（錐への適用にはM3・M4） | EのGalois接続、二つの普遍性、Law族の復元、台制限の関手、W2。診断値の一致だけで終了しない |
| M6：有限多段と統合 | M2–M5 | Fの実triangle・filtration、共通署名上の自然性、全条項とWの証拠対応。ここで全targetの完了候補を作る |

M1→M2とM1→M3は依存上別々に進められる。実行時にはrootが一つの到達点を選び、
単一のGOALの下で必要な接続を閉じる。M3を省いてH¹の数値だけへ進む経路や、
M5を後続GOALへ分離してG-133を完了にする経路は固定targetと一致しない。

## 6. 検証と独立レビューへの論点

設計段階では、参照宣言の存在・型・仮定・使用先、式の向きと次数、指定例の有理行列計算、
相対リンク、語彙、`git diff --check`、hidden/BiDi Unicodeを確認する。
Lean宣言を追加する実装段階では、各到達点の非aggregate fileに対するfocused check、
対象宣言の公理・placeholder・import方向検査と固定targetの照合を行う。
Research全体buildの運用は[AAT guideline](../../../docs/aat/guideline.md#lean-build-運用hard-rule)に従う。

独立レビューでは特に次の設計判断を確認する。

- T0は既存のhereditary部分incidence射を全量化する。候補08の別の面退化を導入せず合成が閉じること。
- Eの最粗商は名付きセルと比較を復元する商の圏で述べる。抽象的な複体の同型だけを保存する商とは対象・射が異なること。
- 加法的普遍性はselected blockを扱い、Law全体の数値だけからblock評価を一意復元するという過大な主張をしないこと。
- Fのfiltrationにはモデル変更を含める。錐の単純な部分空間列と誤認しないこと。

これらの量化・要求はカードで特定済みである。変更が必要になった場合はGOALの改訂として扱う。
mathlibと既存H¹商の同型をどの内部補題で構成するか、filtrationの具体的なAPI配置は
実装時に選べる未確定事項であり、要求の削減理由にはしない。

## 7. 理論とArchSigの保証範囲

G-133が証明するのは、T0の有限入力から作る有理複体・実比較・錐・台署名の関係である。
既存 `computedASubnerveDefect_eq_aSubnerveDefect` はLean内の有限表計算と
G-107の実H¹欠損を接続する。新しい三段表・相殺計算との接続は追加の構成義務になる。

ArchSigの結論は[Tool guideline](../../../docs/tool/guideline.md#責務範囲入力トライアドの正本)の
ArchMapとLawからの導出について保証する。
現行 [saga.rs](../../../tools/archsig/src/saga.rs) の `derive_residual` は
`profile.coefficient != "F2"` を検査する。G-133の係数はℚであり、
係数・入力表・セル選択・比較式を揃える実装対応と検証を経て採用する。
G-133のResearch証明、Formalへの蒸留、Rustの実装と検証はそれぞれ別の成果として記録する。

現段階のdeliverableはdraftカードと本設計であり、Leanの新規証明statusや
ArchSigの機能・schema・公開面のstatusを更新しない。
