# G-132：可視閉路から零性反映を判定する構成

[GOALの固定target T0・A–C・W](../../goals/G-132-aat-visible-cycle-reflection.md)の構成・証明方針を定める。
既存宣言の入力・型・適用条件は[再利用対応表](reuse-map.md)、実被覆と有限例の全データは
[指定例](witnesses.md)に置く。以下の新しい定理・接続はすべて証明義務である。

## 1. 既存実装から進む部分

参照版はmain commit `7547b0d1dc9d523e63c0e8596180dd61e6119529`。
[G-125 report](../../reports/G-125-aat-obstruction-diagnostic-bridge.md)が記録する受理実装と、
[Rising Sea 構成3.36–定理3.40](../../../outreach/paper/rising-sea/ja/06-resolution-invariance.md)を照合した。
G-125の共通代表条件は `SpecifiedClassReflection.lean` の
`CommonLabelChartSupport` にあり、係数の `ReflectionCondition` とは別の仮定である。

| 区分 | 内容 | 今回の接続 |
| --- | --- | --- |
| 再利用 | 原始関係による係数商、blockとラベルの同値、係数比較 | $`R_q`$ の下で整数ラベル座標と基底を得る |
| 再利用 | 実Čech正規化、実比較、独立の診断生成式、既存障害類への接続 | 新しい実被覆で同じ宣言を具体化する |
| 再利用 | law-valueごとのcochain分解、微分の可換性、H¹分解 | 分解自体を作り直さず、各blockを $`N_\lambda`$ の複体へ同定する |
| 新しい接続 | 完全な実nerve、部分的なtarget台、point/generator Atom site | supplied face型の空性から残る幾何の証明義務を放電する |
| 新規結果 | 可視部分の包含・閉路・非橋辺の同値と三条件同値 | 全局所データの零性反映を特徴づける |
| 新しい接続・新規構成 | 全グラフのpotential、整数補正、遷移で貼る状態層 | G-125のfloor補題を実切断の補正と大域状態へ接続する |
| 新規構成 | 有限表の判定と失敗証拠、W1–W3 | 真偽だけでなく元の実入力を返す |

## 2. 同じ入力から実被覆と診断台を作る

### 2.1 幾何台と診断台

T0の二種類の台は、既存実装でも `ContextOpenSupport.support : S.category ⥤ Opens X` と
`TargetSupportedNerve.chartSupport : Chart → Set q.Target` という異なる型である。
$`U_i\cap U_j`$ の非空性がnerve辺を決め、その辺の診断にはK1の $`T_i\cap T_j`$ を使う。
target台の三重交差が非空でも、幾何的三重交差が空なら面は存在しない。
両者を同一視すると、G-125の全target台の有限例さえ誤ったnerveになる。

辺型は $`\{(i,j):i<j\ \land\ (U_i\cap U_j).\mathrm{Nonempty}\}`$ とし、
存在証明をproof dataとして保持する。辺の向き、実交差context、左右restrictionを
この同じ組から作る。任意の非空二重交差がこの型に対応し、同じ組に辺が一つであることを示す。
三つの異なるchartとその実交差点を保持する完全なface型を一旦定め、T0の三重交差条件から
空性を証明する。`FaceEmptyAATCechCover` はその後に組み立てる。

`N_λ`は一般には頂点集合から作る誘導部分グラフではない。
辺ごとに $`\exists t\in T_i\cap T_j,\bar v_\ell(t)=v`$ を確認して生成する。
この証人から両端の可視性が従うので部分グラフ包含を構成できる。

### 2.2 AAT siteと層の生成経路

G-125の `PointGeneratorAtomInput`、`CombinedAtomContextSupport`、
`CombinedAtomContextContinuity` は特定の八点空間と四生成子に特殊化されている。
その固定値をW1–W3へ流用せず、次の構成をT0の入力に対して一般化する。

1. Atom carrierを幾何点と $`\mathrm{Law}\times\mathrm{Source}`$ の直和とする。
   生成子のsubject・Law・値を保持し、生成子間のarchitecture relationは原始 $`R`$ とする。
2. 開集合 $`W`$ のcontextはその点Atomと全生成子Atomを読む。
   任意contextの幾何台は読める点集合のinteriorから作り、context間のrestrictionで単調になる
   support functorを構成する。product contextの台は実開集合の交差であることを示す。
3. point/generatorのcoverageを持つ既存形式のAAT siteを構成する。
   原始被覆の点被覆とchart族の非空性から、選定coverのadmissibilityを証明する。
   生成topologyの被覆を開被覆へ送り、productのpullback保存を用いて
   `Functor.IsContinuous` を証明する。これを `ContextOpenSupport` へ格納する。
4. 既存の局所定数層と `aatLocallyConstantObstructionSheaf` を適用し、実chart・重なりcontextの
   restrictionを持つČech複体へ接続する。

このAAT構成で全生成子Atomを読むことと、診断で読むtarget台 $`T_i`$ の選択は異なる。
構成3.36と同じく $`T_i`$ は原始入力として先に固定する。全生成子を持つことから
$`T_i=Q`$ や共通代表を推論しない。診断の各セルの支持証人は、同じ実セルに付いた
$`T_i`$ とK1交差から生成し、欲しい零性判定に合わせて選び直さない。

`ContextOpenSupport.continuous` を外から受け取り、それをsheaf構成の完了とする経路は
Aの構成義務を満たさない。既存の特殊化されたcontinuity証明は一般化の参照実装であり、
新しい入力に対する証明は未接続である。

## 3. A：実比較をラベル別の制限へ同定する

$`\theta:M_R\simeq\mathbb Z^\Lambda`$ は、`presentationGroupEquivBlocks`、
`blockLabelEquiv`、有限集合上の自由アーベル群の座標表示を合成して作る。
`coefficientComparison` の各値が $`\theta(m)_\lambda`$ の有理数への埋め込みであることを、
既存の基底評価・block係数回収から示す。

診断側は `chartCochainBlockEquiv`、`edgeCochainBlockEquiv` と
`lawGeneratedH1BlockEquiv` を使う。各block座標を
$`\{i:i\in V_\lambda\}`$、$`\{e:e\in E_\lambda\}`$ へ送る同値はcell射影から作る。
逆は同じLaw・値と支持証人から作り、証人の違いが座標を重複させないことには
`CellCoordinate.ext` を使う。

次数0・1の座標同値で `lawValueBlockD0` が通常の $`b_j-b_i`$ に一致し、次数2が空で
微分が零になることを示す。cochainの空間だけの同値では不十分であり、微分とcoboundaryの
像の一致を証明してから既存のH¹商へ降ろす。

実Čech側では `faceEmptyCechCochain0Equiv/1Equiv` と
`faceEmptyCech_d0_normalizes` を使う。この同定の下で

```math
(\phi^n c)_{\sigma,\lambda}
  =\bigl(\theta(c_\sigma)_\lambda:\mathbb Q\bigr),\qquad
  \sigma\in N_\lambda,\quad n=0,1
```

を実 `actualCechCoefficientCochain0/1` の評価式として証明する。
この式と微分の可換性により、GOAL Aの係数変更と制限の合成を得る。
`existingDescentAdditiveClass_eq_actualClass` と
`h1_map_actual_class_eq_diagnostic_class` を適用する対象は、同じ $`P,C,x`$ とする。
legacyの `CoverRelativeHn 1` と加法群 `AdditiveCechH1` は型が異なるため、既存の同値を明示する。

## 4. B：閉路条件、整数補正、必要性

### 4.1 chainとcochainの対応

有限単純グラフ $`N`$ にT0の向きを使い、$`\partial[e]=[t(e)]-[s(e)]`$ とする。
次数2がないので $`H_1(N;\mathbb Q)=\ker\partial`$ であり、
$`H^1(N;\mathbb Q)`$ は辺cochainを頂点差で割った商である。
部分グラフのchain包含は零延長、cochain写像は制限とし、評価pairingの可換性を示す。
通常の有限次元の完全pairing、または全域森によるperiod座標から、
H¹制限の単射性とH₁包含の全射性を対応させる。

H₁包含は既に単射である。全射性から非橋辺包含を得るには、ある非橋辺を含む単純閉路の
chainを取る。欠けた辺での係数は $`\pm1`$ なので、部分グラフからの像には入らない。
逆に橋で閉路chainの係数が零になることを、辺削除後の片側の頂点係数の総和から示す。
全非橋辺が見えれば任意の閉路chainが可視部分に支持され、全射になる。
孤立頂点や非連結なグラフにも同じ証明を適用する。

Mathlibの `SimpleGraph.IsBridge` と辺削除後の到達可能性・閉路による特徴づけを使う。
連結成分数によるGOALの定義との一致を有限グラフで証明する。
一般のloop・平行辺を持つグラフの補題へ広げることは内部選択として許すが、
実被覆のnerveの実現範囲はT0の単純グラフのまま保持する。

### 4.2 可視閉路から大域potentialを作る

診断類が零なら各 $`\lambda`$ の可視辺上で $`z_\lambda`$ は有理頂点差である。
よって可視閉路のperiodは零で、(B2)から全閉路のperiodが零になる。
成分ごとに根と全域木を取り、根からの向き付き辺和で全頂点のpotentialを構成する。
木以外の辺では閉路periodの零を使って辺差の一致を証明する。

ここで得るのは **全N上の** 有理potential $`b`$ と
$`b_{t(e),\lambda}-b_{s(e),\lambda}=(z_{e,\lambda}:\mathbb Q)`$ である。
診断の証人は不可視頂点に値を持たないので、そこを零で埋めてfloorするだけでは足りない。
全辺差を導出してから `IntegralReflection.exists_integral_correction` を適用し、
$`\theta^{-1}`$ とČech次数0同値の逆で実切断の整数補正へ戻す。
floorはこの辺差を保つ証人構成であり、加法準同型・有理数から整数への線形射ではない。

### 4.3 アフィン状態の層と実際の貼り合わせ

遷移の向きは $`\xi_{ij}+p_j-p_i`$ に合わせる。$`i<j`$ の遷移から
$`\xi_{ji}=-\xi_{ij},\xi_{ii}=0`$ を定め、平行移動を局所状態の同型とする。
空の二重交差では唯一の切断を使う。
相異なる三重交差が空で、反復indexでは加法の逆元律があるので、遷移の整合を証明できる。

開集合 $`W`$ 上の $`\mathcal T_\xi`$ を、$`F_R(W\cap U_i)`$ の局所状態を
この遷移で貼った層として構成する。各chartで $`F_R`$ への局所自明化とその逆を与え、
元のrestrictionとの可換性、各chartで自由かつ推移的な $`F_R`$ の作用を証明する。
大域切断の非空性は構造のfieldにせず、障害の零性から導く結論とする。
層条件は局所定数係数層の貼り合わせから導き、AAT siteにも同じsupport functorで引き戻す。
`p-n`の重なり条件から大域状態を得て、逆に大域状態の局所表示 $`r`$ から
$`n=p-r`$ と $`d^0n=\xi+d^0p`$ を回収する。

既存 `ExistingObstructionBridge.lean` は障害類のprovenanceを与えるが、
このアフィン状態層の構成・局所自明化・大域切断の定理までは供給していない。
通常の $`F_R`$ のrestrictionで $`p-n`$ がそのまま一致すると主張せず、同じ $`\xi`$ の
平行移動を通した一致を証明する。

### 4.4 不可視非橋辺から実入力を作る

非橋辺 $`e`$ を除いて両端を結ぶ単純道を取り、$`e`$ を一度通る閉路 $`\gamma`$ を作る。
$`u_\lambda=\theta^{-1}(\delta_\lambda)`$ を定め、
`faceEmptyCechCochain1Equiv` の逆から単一辺の定数切断を作る。chart切断は零とする。
これは任意の固定T0構造で作れる。W2専用の実現仮定に置き換えない。

係数比較の基底評価から、可視座標の全てで診断cochainが零になる。
$`\lambda`$ の $`e`$ 座標自体は存在せず、他ラベルではdeltaが零だからである。
同じ実遷移のperiodは $`\pm u_\lambda`$、任意のcoboundaryのperiodは望遠和で零。
したがって実Čech類が非零であり、既存descent障害の加法的表示へ戻して必要性を得る。
`actual_class_adjust_local_state` は、$`p`$ だけの変更で必要性を証明できないことを
確認する既存APIとして再利用する。

## 5. C：有限入力と出力

一般定理Bは任意のT0空間を扱い、Cは有限表で提示した同じ構造を扱う。
有限幾何は有限preorderの順序表とchart集合で表示できる。上集合のAlexandrov位相を使い、
chartの開性・被覆・非空性、各非空二重交差の連結性、三重交差の空性を有限に確認する。
連結性は誘導された有限comparability graphでの到達可能性と対応させる。
一般の被覆表を入口にする場合も、実交差・連結性をこの構造へ対応させる証拠が必要である。

| 段階 | 表から作るデータ | 証明すること |
| --- | --- | --- |
| 前処理 | SourceのLaw評価像 $`\Lambda`$、readingのfiber、原始関係の連結成分 | adequate・ラベル保存・$`R_q`$ を有限判定できる。無効入力と(B1)の失敗を区別する |
| 実nerve | chart対を全列挙し、非空交差の対だけを辺にする | T0の辺集合と向きに一致し、収載漏れ・重複がない |
| 可視部分 | $`T_i`$ と $`T_i\cap T_j`$ 上のLaw値を列挙・重複除去 | `CellCoordinate`のラベルfiberと一致する |
| 橋 | 各辺を削除し両端間の有限到達可能性を判定 | `IsBridge`とGOALの橋の定義に一致する |
| 成功 | 全ラベルで全非橋辺が含まれることを検査 | 成功 $`\leftrightarrow`$ (B3) $`\leftrightarrow`$ (B1) |
| 失敗 | 最初の欠落対 $`(\lambda,e)`$ と、削除後の両端間の単純道を探索 | 閉路・単一辺遷移・零状態を生成し、Bの証拠へ戻す |

有限な頂点列の長さを頂点数で制限した道の列挙でもよい。
探索は新しい頂点を追加するか有限な候補リストを消費するため停止する。
閉路を存在証明からchoiceで選ぶだけでなく、この探索が返す道を使用する。
Rの有限経路も同様に得る。Cの出力 $`x`$ は有限表の整数係数から実切断へ戻すconstructorで作り、
存在量化された任意の局所入力を返すだけにしない。

## 6. 証明の依存と自己点検

| 段階 | 前に必要なもの | 終了時に得る証拠 |
| --- | --- | --- |
| 実被覆・AAT構成 | T0、G-125のsite構成方法 | 完全nerve、continuous support、実係数層とrestriction |
| 座標と実比較 | 上段、既存presentation・law-value分解 | Aのcochain・微分・指定類・制限の対応 |
| 閉路と整数補正 | A、有限グラフのchain計算 | (B2)⇔(B3)、十分性、整数補正 |
| 実入力と状態層 | A、単一辺基底、実係数層 | 必要性、零障害と大域状態の往復 |
| 有限手続きと指定例 | A–B、有限表のdecode | Cの停止・成功同値・失敗証拠、W1–W3の実評価 |

検証時は、特に次を照合する。

- 全体のH₁・H¹とラベル別部分のH₁・H¹を取り違えず、写像の向きを明示しているか。
- 全非橋辺条件を十分性だけで終えず、全 $`(\xi,p)`$ の必要性まで実入力で閉じたか。
- 共通代表なしの入力で整数補正が全辺差を満たし、アフィン状態層の大域切断へ進んだか。
- W1の非零coboundary、W2の非零period、W3の森がそれぞれ同じA–Cへ接続しているか。
- 2-cellを追加していないか。面があれば閉路がhomologyで消えるため、非橋辺条件は
  この形の必要条件ではなくなる。

一般化したsiteのcontinuity、可視blockからgraph complexへの同定、状態層の局所自明化、
有限表のdecodeと探索の正確性が主要な未証明事項である。今回の設計PRでは新規Lean宣言を
追加しない。設計の確認は既存signature・本文の直接照合、有限例の計算、参照・差分scanで行う。
後続実装のfocused checkとbuild制約は[AAT guideline](../../../docs/aat/guideline.md#lean-build-運用hard-rule)、
完了判定と停止はGOALの共通基準への参照に従う。
