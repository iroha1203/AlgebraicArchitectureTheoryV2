# G-129-aat-abelian-lifting-obstruction — 可換核による整合持ち上げの障害と解の分類

- `id`: `G-129-aat-abelian-lifting-obstruction`
- `status`: `completed`
- `research mode`: `target-theorem`
- `tracking issue`: [#5082](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5082)
- `source note`: [n1016 §2.4・候補04](../../docs/note/n1016_rising_sea_v2_paper_plan.md)
- `design`: [構成・証明方針と再利用対応](../designs/G-129-aat-abelian-lifting-obstruction/README.md)

## 研究目的

coreで整合するように固定した辺の選択を、幾何でもすべての指定比較と整合するように
持ち上げられる条件と、その全選択肢を求める。実際の射影の可換核と辺の輸送から
局所係数を構成し、面に残るdefectを二次の障害類へ、解の差を一次のコホモロジーへ移す。

[Rising Sea 第4章](../../outreach/paper/rising-sea/ja/07-transport-coherence.md)の
定理4.23・4.33・4.34による、再選択の存在と核のdefect消滅との対応を、
コチェインの補正方程式と解の分類へ進める。
[G-127](G-127-aat-reversible-protocol-holonomy.md)の同じ変更群・可視射影から得る
非分裂拡大を、この障害の具体例へ接続する。

## 固定target

A–Dを一つの障害・分類定理の構成部分とする。
量化順は有限表示と射影・輸送データ、固定したcoreの選択、その辺ごとの持ち上げ、
最後に核の補正とする。係数となる核の有限性は要求しない。
コホモロジーは、Aで構成する同じ有限表示の局所係数複体に対して定める。

### A. 原始入力からの局所係数と複体

**有限表示。** `FiniteTransportPresentation` の頂点・辺・面・3-cellを持つ表示を
$`K`$ とする。
各面 $`f`$ は共通の始点・終点を持つ二つの有限な辺の列
$`\ell_f,r_f`$、各3-cell $`\sigma`$ は同じ道から同じ道へ至る二つの
型付き書き換え列 $`P_\sigma,Q_\sigma`$ を指定する。
書き換えの各段は、面の向きと前後の道を保持する。空の道と辺の繰り返しを許す。

**射影・辺・比較。** 圏の塔 $`\mathcal E\xrightarrow{p}\mathcal B\xrightarrow{q}\mathcal D`$、
各頂点の対象 $`X_v\in\mathcal E`$、各辺 $`e:v\to w`$ の射 $`L_e:X_v\to X_w`$ を
入力とする。$`L_e`$ は $`qp`$ に関して、$`p(L_e)`$ は $`q`$ に関して強い
opcartesian射とする。各面の二つの道は $`\mathcal D`$ で同じ射を与える。
終点の指定比較 $`u_f\in\operatorname{Aut}_{qp}(X_{t(f)})`$ も入力に含める。
道の射は元の辺の合成で、面の標準比較は強いopcartesian射の一意性から構成する。
式では $`yx=y\circ x`$ の順で合成する。

各頂点について、実際の射影から

```math
C_v=\operatorname{Aut}_{qp}(X_v),\qquad
B_v=\operatorname{Aut}_{q}(pX_v),\qquad
\pi_v:C_v\longrightarrow B_v,\qquad
A_v=\ker\pi_v
\tag{A1}
```

を作る。coreの辺の再選択 $`a_e\in B_{t(e)}`$ と、辺ごとの持ち上げ
$`\widetilde a_e\in C_{t(e)}`$、$`\pi_{t(e)}(\widetilde a_e)=a_e`$ を入力とする。
$`\widetilde L_e=\widetilde a_eL_e`$ とし、coreでの整合を

```math
p(u_f)\,p(\widetilde L_{\ell_f})=p(\widetilde L_{r_f})
\qquad\text{for every }f
\tag{A2}
```

で指定する。次を一般定理の仮定とする。

1. 各 $`A_v`$ は可換である。以下では $`A_v`$ を加法で書き、
   実際の自己同型への包含を $`\iota_v`$ と書く。
2. $`\widetilde L_e`$ に沿う強いopcartesian射の輸送は、実際の核 $`A_{s(e)}`$ を
   $`A_{t(e)}`$ へ同型に運ぶ。輸送写像は
   $`\iota_{t(e)}(\rho_e(b))\widetilde L_e=\widetilde L_e\iota_{s(e)}(b)`$
   を満たす一意の自己同型として構成し、核への所属と準同型性を証明する。
   その核上の写像の全単射性を仮定として保持する。
3. 各指定比較 $`u_f`$ は終点の核 $`\iota_{t(f)}(A_{t(f)})`$ の各元と可換である。
   この条件は、面に沿う係数輸送の一致と、指定比較を保つ頂点での再同定に使う。
4. 各3-cellについて、元の指定比較を前後の道に沿って輸送・合成した二つの写像が、
   $`\widetilde L`$ において等しい。これは第4章の指定比較のsyzygy条件である。

**仮定の意味と適用範囲。** 条件1は核の補正を加法で扱う条件、条件2は辺の輸送が
その自由度を同型に保つ条件である。強いopcartesian性から輸送の準同型を構成し、
核上の全単射性を別の条件として確かめる。

(A2)と条件1・2の下で、Bの標準比較 $`m_f`$ を用いて

```math
\rho_{r_f}=\operatorname{Ad}(u_f)|_{A_{t(f)}}\circ\rho_{\ell_f}
```

を導く。ここで $`\operatorname{Ad}(u_f)`$ は $`u_f`$ による共役である。
条件3と $`\rho_{r_f}=\rho_{\ell_f}`$ の同値を証明し、条件3を、核の輸送が
指定した面の関係を尊重する条件として位置づける。
例えば $`p(u_f)=1`$ の場合は $`u_f\in A_{t(f)}`$ と条件1から条件3を導ける。
条件4は指定比較同士の関係であり、その貼り合わせからBのdefectのコサイクル条件を導く。

この入力から、$`\rho_e`$ が同じcoreを持ち上げる辺の選択によらないことを証明する。
核の族とその輸送を局所係数 $`A_\rho`$ として、同じ辺・面から生成される道の関係へ
降下させる。辺の輸送 $`\rho_e`$ は非自明な作用も含む。

次の可換群と準同型を構成する。

```math
C^0=\prod_v A_v,\quad C^1=\prod_e A_{t(e)},\quad
C^2=\prod_f A_{t(f)},\quad C^3=\prod_\sigma A_{t(\sigma)},
\qquad C^0\xrightarrow{d^0}C^1\xrightarrow{d^1}C^2\xrightarrow{d^2}C^3.
\tag{A3}
```

辺の補正 $`h\in C^1`$ と道 $`w=e_1\cdots e_m`$ に対し、その終点での総補正を

```math
T_w(h)=\sum_{j=1}^{m}\rho_{e_{j+1}\cdots e_m}(h_{e_j})
```

と定める。空の道では零とし、辺の各出現をそれぞれ数える。
$`(d^0b)_e=b_{t(e)}-\rho_e(b_{s(e)})`$、
$`(d^1h)_f=T_{\ell_f}(h)-T_{r_f}(h)`$ とする。
書き換え列上の2次のコチェインの評価は、各面の値を後続の道で終点へ輸送し、
面の順向きには正、逆向きには負の符号を付けた和とする。
$`(d^2c)_\sigma`$ は $`P_\sigma`$ 上の評価から $`Q_\sigma`$ 上の評価を引いたものとする。

同じ道の輸送・面・型付き貼り合わせから $`d^1d^0=0`$、$`d^2d^1=0`$ を証明し、
$`Z^1=\ker d^1`$、$`H^1=\ker d^1/\operatorname{im}d^0`$、
$`H^2=\ker d^2/\operatorname{im}d^1`$ を構成する。
これらの微分、複体の等式、以下のdefect変換則とコサイクル条件は構成・証明義務とする。

### B. 選択によらない障害と持ち上げの存在

標準比較 $`m_f`$ を $`m_f\widetilde L_{\ell_f}=\widetilde L_{r_f}`$ から構成する。
(A2)から $`p(m_f)=p(u_f)`$ を導き、同じ射の差を

```math
\iota_{t(f)}(\delta_f)=u_fm_f^{-1}
\tag{B1}
```

で $`A_{t(f)}`$ に戻す。Aの3-cell条件から $`d^2\delta=0`$ を証明する。
任意の核補正 $`h\in C^1`$ により
$`\widetilde L_e^h=\iota_{t(e)}(h_e)\widetilde L_e`$ と選び直すとき、
実際に構成し直したdefectについて

```math
\delta^h=\delta+d^1h
\tag{B2}
```

を証明する。係数輸送と3-cell条件も同じものを使えることを示す。
障害類 $`o(a)=[\delta]\in H^2(K;A_\rho)`$ は、固定したcoreの選択を持ち上げる
$`\widetilde a`$ の選び方によらないことを証明する。

解集合 $`\operatorname{Sol}(a)`$ は、$`\pi_{t(e)}(c_e)=a_e`$ を満たす辺の族
$`c_e\in C_{t(e)}`$ のうち、$`L_e^c=c_eL_e`$ が
$`u_fL_{\ell_f}^c=L_{r_f}^c`$ をすべての面で満たすものとして独立に定める。

```math
o(a)=0\quad\Longleftrightarrow\quad\operatorname{Sol}(a)\ne\varnothing
\tag{B3}
```

を証明し、$`d^1h=-\delta`$ の解と実際の整合する持ち上げを相互に構成する。
この対応は元の各辺の射を保つものとする。

### C. 解全体と頂点での再同定による分類

$`\operatorname{Sol}(a)\ne\varnothing`$ のとき、各辺への核の補正により
$`Z^1(K;A_\rho)`$ が $`\operatorname{Sol}(a)`$ に自由かつ推移的に作用することを
証明する。任意の二つの解の差を同じ辺の核の元として取り出し、唯一の1次のコサイクルへ
対応させる。基準解を選ぶときには、この作用から $`Z^1`$ との全単射を与える。

頂点の再同定は、任意の $`b\in C^0`$ による元の辺の射の変更

```math
L_e^c\longmapsto
\iota_{t(e)}(b_{t(e)})\,L_e^c\,\iota_{s(e)}(b_{s(e)})^{-1}
\tag{C1}
```

として定める。同じcoreと指定比較を保ち、辺の補正では $`d^0b`$ の加算に一致することを
証明する。(C1)による同値類の集合が $`H^1(K;A_\rho)`$ のtorsorとなることを示す。
辺の持ち上げの基準選択を変えたときも、Bの障害類とCの作用・同値類を、同じ実際の
持ち上げと頂点での再同定を通じて対応させる。

### D. 第4章の実際のdefectと、G-127の群拡大への接続

**幾何からcoreへの射影。** Aの圏の塔を、同じAtom carrier上の
幾何のpackageからcoreのpackage、さらに抽出対象への塔に特殊化する。
`TwoLayerTransportData`、`EdgeSectionFamily`、`CoreAlignmentAt` の同じ入力について、
(A1)を `compositeFiberPushforward` とその実際の核 `InnerFiberAut` に対応させる。
Aの可換性・核上の全単射性・面比較の可換性・3-cell条件を満たす全入力を対象とする。

(B1)の包含が `sectionInnerObstruction` と同じ元の自己同型であること、
任意の補正について(B2)が `relativeInnerDefectCochain` の値を与えることを示す。
(B3)を `SectionRelativeCoherentizable` の同じ辺の選択へ、Cの作用を同じ
`StrictEdgeReselection` と実際の頂点自己同型へ対応させる。
核の所属・輸送・貼り合わせはこの原始入力から構成し、Aの仮定は各対応箇所で使用する。
完了条件4では具体的な幾何packageの入力を構成し、同じ実際の核についてAの各仮定を
証明した上で、この対応を適用する。

**指定された群拡大。** 任意の可換核を持つ群拡大
$`1\to A\xrightarrow{i}E\xrightarrow{\pi}H\to1`$ を一対象圏の塔
$`BE\to BH\to\mathbf1`$ としてA–Cへ適用する。
各辺の元 $`a_e\in H`$ は指定したすべての面の関係を満たすものとし、
元の辺 $`L_e`$ と指定比較 $`u_f`$ は恒等元とする。
核の輸送は持ち上げの共役から降下する $`H`$ 作用と一致させる。
このとき(B3)は同じ $`H`$ 値の辺データを関係を保つ $`E`$ 値データへ持ち上げる条件、
Cはその全持ち上げと核による頂点共役の分類を与えることを証明する。

G-127の原始入力から得る `ChangeGroup`、`projectionToLiftable`、
`verticalLiftInclusion` にこの構成を接続する。実際の垂直核が可換である入力に対し、
同じ $`A_F\to H_{\mathrm{lift}}`$、同じ元の可視変更・fiber写像でB・Cを読み戻す。
完了条件2では、G-127の指定例に同じ一般定理を適用する。

## 既存宣言の参照

Research pathは `research/lean/ResearchLean/AG/` からの相対とする。
宣言の参照版はactive化時にtracking Issueへ記録する。

| 用途 | path・宣言 |
| --- | --- |
| Aの有限表示・型付き貼り合わせ | `TransportCoherence/FinitePresentation.lean` の `FiniteTransportPresentation`、`RewritePasting` |
| A・Bの任意の関手上の持ち上げ・比較 | `TransportCoherence/ArbitraryFinitePresentation.lean` の `LiftData`、`TransportData`、`TransportCoherence/ArbitraryObstruction.lean` の `whiskerFiberAutHom`、`AuthoredSyzygy`、`rawDefect_cocycle_of_authoredSyzygy` |
| Dの核と整列した選択 | `CrossStageCoherence/ObstructionGroups.lean` の `compositeFiberPushforward`、`InnerFiberAut`、`CrossStageCoherence/SectionDecomposition.lean` の `EdgeSectionFamily`、`CoreAlignmentAt`、`sectionInnerObstruction` |
| Dの同じ核の補正・解 | `CrossStageCoherence/RelativeObstruction.lean` の `relativeInnerDefectCochain`、`SectionRelativeCoherentizable`、`innerVanishesAt_iff_sectionRelativeCoherentizable` |
| 完了条件4の幾何入力に使える既存構成 | `CrossStageCoherence/FiniteWitnesses.lean` の `FiniteCrossStageWitness.symmetricRaw`、`FiniteCrossStageWitness.package`、`FiniteCrossStageWitness.innerSwap`、`FiniteCrossStageWitness.innerSwap_ne_one`。核全体の可換性は完了条件4の証明義務 |
| DのG-127短完全列 | `ProtocolHolonomy/LiftableVisible.lean` の `verticalLiftInclusion`、`projectionToLiftable`、`liftable_shortExact` |
| 完了条件2の同じ群・射影・非分裂 | `ProtocolHolonomy/TwoVertexTotalGroup.lean` の `twoVertexC4`、`ProtocolHolonomy/TwoVertexQuotient.lean` の `twoVertex_projection_is_mod_two`、`ProtocolHolonomy/TwoVertexNoSection.lean` の `twoVertex_no_group_section` |

## 前提・構成台帳

| 対象・対応条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 有限表示、圏の塔、辺、指定比較(A) | 原始入力として保持 | Aの道・面・3-cell、強いopcartesian性、底の道の一致 | 実際の比較・核・係数複体へ |
| 固定coreと辺ごとの持ち上げ(A・B) | 入力として保持 | (A2)と辺ごとの射影等式 | 核へのdefectの所属と、同じcore上の解集合へ |
| 可換核・核輸送の全単射性・面比較の可換性(A) | 一般定理の仮定 | Aの条件1–3。具体例では証明義務 | 選択によらない局所係数、面の輸送の一致、(C1)の作用へ |
| 指定比較の3-cell条件(A・B) | 一般定理の仮定、具体例では証明義務 | Aの条件4。元の貼り合わせの等式 | 実際のdefectのコサイクル条件へ。面のdefect消滅は要求しない |
| 微分・局所係数・障害類(A・B) | 構成・証明義務 | (A3)、複体の等式、(B1)–(B3) | 同じ原始入力から存在条件へ |
| 解・核補正・頂点での再同定(C) | 構成・証明義務 | 二つのtorsorと(C1)、基準選択との整合 | 実際の辺の選択とその差から全解の分類へ |
| 第4章・群拡大への特殊化(D) | 既存宣言を再利用、同じ対象との対応は証明義務 | Dの原始入力・元の写像・defect・作用の一致 | 抽象的な障害判定を同じAATの持ち上げへ戻す |
| 完了条件2・3の群拡大の例 | 全入力条件と結論の証明義務 | 同じ拡大・3-cell付き有限表示・作用・解集合 | Bの非零障害・コサイクル条件、Cの非空なtorsorと再同定へ |
| 完了条件4の幾何packageの例 | 原始入力の構成とAの条件1–4の証明義務 | 実際の `InnerFiberAut`、辺の輸送、指定比較とその貼り合わせ | Dを同じ幾何のdefectと整合する持ち上げへ適用する |

## 完了条件

1. A–Dを同じ入力・核・defect・解集合についてLeanで証明し、
   `target-theorem-proved` とする。
2. **G-127の非分裂拡大。** G-127完了条件3の二頂点、二辺
   $`a:0\to1,b:1\to0`$、Bool fiber、$`T_a=\mathrm{id},T_b=(01)`$、
   空の経路関係、頂点と辺を交換する可視群 $`C_2`$ を固定する。
   その実際の短完全列 $`1\to C_2\to C_4\to C_2\to1`$ をDへ適用する。
   持ち上げを問う有限表示は、一頂点・一ループ $`e`$、一つの面
   $`f:e^2\Rightarrow\varnothing`$ と、$`e^3\Rightarrow e`$ の二つの書き換えを比べる
   一つの3-cell $`\sigma`$ とする。$`P_\sigma`$ は先頭の $`e^2`$ を消す書き換え、
   $`Q_\sigma`$ は末尾の $`e^2`$ を消す書き換えとし、coreでは $`a_e`$ を非自明元とする。
   これは元の二頂点の操作グラフとは別の、可視変更の関係の表示である。
   同じ可視変更の二つの持ち上げに対し、$`A=C_2`$、$`\rho_e=1`$、
   $`d^1=2=0`$、$`d^2=\rho_e-1=0`$、$`H^2(K;C_2)\cong C_2`$、$`\delta=1`$ を計算する。
   同じ $`\sigma`$ について条件4の貼り合わせ等式と $`d^2\delta=0`$ を評価する。
   その非零障害を(B3)へ適用し、同じ射影に群準同型のsectionが存在しないという
   `twoVertex_no_group_section` の結論へ対応させる。
3. **非自明な係数輸送と非空の解。** 符号準同型による拡大
   $`1\to C_3\to S_3\to C_2\to1`$ にDを適用する。
   $`S_3=\operatorname{Sym}(\{0,1,2\})`$ とし、$`C_3`$ の生成元を $`(012)`$ へ送る。
   有限表示とcoreの値は完了条件2と同じものを使い、基準の持ち上げは互換 $`(01)`$ とする。
   $`\rho_e=-1`$、$`\delta=0`$、$`d^0=2`$、$`d^1=1+\rho_e=0`$ を計算する。
   $`\sigma`$ による $`d^2=\rho_e-1=-2=\mathrm{id}_{C_3}`$ と条件4を確かめ、
   $`d^2\delta=0`$、$`H^2(K;C_3)=0`$ を計算する。
   実際の解は三つの互換であり、$`Z^1\cong C_3`$ が自由かつ推移的に作用する一方、
   $`H^1=0`$ で、核による頂点での再同定の後には一つの同値類になることを証明する。
4. **第4章の幾何入力での仮定の証明。** 有限Atom carrier上の幾何packageからcore、
   抽出対象への実際の塔に対し、完了条件2の3-cell付き有限表示を使った入力を一つ構成する。
   packageのsiteは非空とし、少なくとも一つの被覆と非零のraw関係式を持つものとする。
   実際の核 `InnerFiberAut` の非自明性・可換性を証明し、辺、coreの再選択、
   辺ごとの持ち上げ、指定比較を原始入力から与える。指定比較は非恒等な元とする。
   この入力について強いopcartesian性、(A2)、核輸送の全単射性、指定比較と核全体との可換性、
   $`\sigma`$ 上の貼り合わせ等式を証明する。同じ入力にDを適用し、実際の
   `sectionInnerObstruction`、障害類、整合する持ち上げの存在判定を計算する。
5. Lean成果を `research/lean/ResearchLean/AG/` に置き、
   `research/reports/G-129-aat-abelian-lifting-obstruction.md` にA–Dと宣言、
   前提の出所・使用先、第4章とG-127の元の写像への対応、指定例の証拠を対応させる。
6. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従って完了を判定する。適用版、検証、査読、実行状態はIssue・reportへ置く。
