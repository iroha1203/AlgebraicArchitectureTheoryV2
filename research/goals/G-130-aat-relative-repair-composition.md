# G-130-aat-relative-repair-composition — 全変更範囲を保つ相対修復の合成と分類

- `id`: `G-130-aat-relative-repair-composition`
- `status`: `active`
- `research mode`: `target-theorem`
- `tracking issue`: [#5132](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5132)
- `source note`: [n1017 §2–3・§5](../../docs/note/n1017_aat_relative_boundary_repair_and_observation.md)
- `design`: [構成・証明方針と再利用対応](../designs/G-130-aat-relative-repair-composition/README.md)

## 研究目的

保持する実操作と追加変更を許す辺を固定し、各部分で一度生成した表現から、全ての
変更範囲の修復可否、全修復、再同定、包含極小の修復可能範囲を求める。
同じ表現から不能証拠を取り出し、得た補正を元の名前付き操作へ戻す。

[G-129](G-129-aat-abelian-lifting-obstruction.md)の実核・輸送・補正方程式・解の分類を、
固定部分に相対化し、変更範囲を保つ局所合成へ進める。内部の補正自由度と再同定を保持し、
入力値の更新と内部辺の分割に沿って同じ修復構成を再利用できることを示す。
[G-131](G-131-aat-repair-observation-duality.md)は、この同じ実方程式に対する観測を扱う。

## 固定target

A–Fを一つの修復合成・分類定理の構成部分とする。
量化順は、原始表示・実射・固定条件、有限被覆、そこから生成する局所表現、
最後に全ての変更範囲 $`S`$ とその修復・再同定とする。
A・BとEの内部辺分割は可換群で述べる。C・D、Eの有限生成・文脈同値、Fでは
同一の有限体上の有限次元実全核と線形な核輸送を用いる。

### A. 固定部分と変更範囲を保つ実修復

**原始入力。** G-129 Aの `FiniteTransportPresentation` $`K`$ と一般の圏の塔
$`\mathcal E\xrightarrow p\mathcal B\xrightarrow q\mathcal D`$ を用いる。
元辺 $`L_e^{\mathrm{orig}}`$、固定core再選択 $`\kappa_e`$、その持ち上げ
$`\widetilde c_e`$、基準実辺 $`\widetilde L_e=\widetilde c_eL_e^{\mathrm{orig}}`$、
面の指定比較 $`u_f`$ を保持する。合成は $`yx=y\circ x`$ の順とする。
元辺の $`qp`$ に関する強いopcartesian性、その像の $`q`$ に関する強いopcartesian性、
底での面の経路一致、core整合、G-129 Aの条件1–4を同じ意味で課す。
係数 $`A_v`$ は実射影 $`\operatorname{Aut}_{qp}(X_v)\to\operatorname{Aut}_q(pX_v)`$ の
全核とし、実輸送平方から $`\rho_e`$ を構成する。

部分表示は、所属辺の端点、所属面の両経路、所属3-cellの両書き換え列に現れる面と
前後の経路を全て含むものとする。対象・射・比較・係数を同じものの制限で与え、
制限が微分・実defect・補正・再同定と交換することを証明する。
固定部分 $`P\subseteq K`$ はこの意味で閉じ、そこで基準実辺が指定面に整合するとする。
$`P`$ 外の辺を、常時補正可能な辺 $`E_0`$ と候補辺 $`\mathsf E`$ に分割する。

**実修復と射。** 各 $`S\subseteq\mathsf E`$ について、実修復を
$`p(c_e)=\kappa_e`$ を満たす $`c_e\in\operatorname{Aut}_{qp}(X_{t(e)})`$ の族で、
$`L_e=c_eL_e^{\mathrm{orig}}`$ が全ての面で $`u_fL_{\ell_f}=L_{r_f}`$ を満たし、
$`P`$ および $`\mathsf E\setminus S`$ 上で基準実辺に一致するものと独立に定める。
射は $`P`$ 上で恒等な頂点の核自己同型による再同定であり、辺には
$`L_e\mapsto\iota(b_{t(e)})L_e\iota(b_{s(e)})^{-1}`$ と作用する。
両端が同じ固定条件を満たす全ての再同定を保持するgroupoidを $`\mathscr R_{P,S}(K)`$ とする。

G-129の同じ微分から相対複体 $`C_P^\bullet=\ker(C^\bullet(K)\to C^\bullet(P))`$ を作り、
$`\delta|_P=0`$ と $`d^2\delta=0`$ を導く。次の複体を構成する。

```math
C_S^1=\{h\in C_P^1:h_e=0\ (e\in\mathsf E\setminus S)\},\qquad
C_S^0=(d^0)^{-1}(C_S^1),\qquad C_S^j=C_P^j\ (j=2,3).
```

実修復と $`\{h\in C_S^1:d^1h=-\delta\}`$ の間に、元の各実辺を保つ相互逆を構成する。
再同定を $`b:h\to h+d^0b`$ と対応させ、異なる再同定を異なる射として保つ。
強いopcartesian性による一意性から、補正零と基準実辺の一致も双方向に示す。
この同じ対応から、$`H_S^j=H^j(C_S^\bullet)`$ に対し

```math
\mathscr R_{P,S}(K)\ne\varnothing\ \Longleftrightarrow\ [\delta]=0\in H_S^2,\qquad
\pi_0\mathscr R_{P,S}(K)\text{ は非空なら }H_S^1\text{ のtorsor},\qquad
\operatorname{Aut}(h)\cong H_S^0=H^0(K,P;A_\rho)
```

を証明し、$`S\subseteq T`$ の包含と対応させる。
同じ物理的な基準操作の参照座標を $`h'=h-a`$ へ変える場合は、固定条件も
$`h'_e=-a_e`$ へ運び、同じ実修復と障害を対応させる。

### B. 全核補正を許すdescentと統合障害

$`\mathscr R_P=\mathscr R_{P,\mathsf E}`$ とする。
閉じた部分表示による被覆 $`K=U\cup V`$、$`W=U\cap V`$ に対し、制限から

```math
0\longrightarrow C^\bullet(K,P)\longrightarrow
C^\bullet(U,P_U)\oplus C^\bullet(V,P_V)
\xrightarrow{r_U-r_V}C^\bullet(W,P_W)\longrightarrow0,
\qquad P_X=P\cap X
```

という次数ごとに短完全な複体の列と、同じ実修復の制限関手による
$`\mathscr R_P(K)\simeq\mathscr R_{P_U}(U)\times^h_{\mathscr R_{P_W}(W)}\mathscr R_{P_V}(V)`$
を構成する。有限被覆では三重交差の再同定のコサイクル条件を保持し、細分化・組立ての
比較を大域実修復への復元と整合させる。

局所修復 $`h_U,h_V`$ が存在するとき、$`z=h_V|_W-h_U|_W`$ とする。
指定した二案が再同定だけで接続する条件は $`[z]=0\in H^1(W,P_W)`$、局所案を
選び直してよい場合の統合条件は、次の商における $`[z]`$ の像 $`\omega`$ の零性とする。

```math
\Omega=H^1(W,P_W)/(\operatorname{im}H^1(U,P_U)+\operatorname{im}H^1(V,P_V)).
```

$`\omega`$ の局所案からの独立性、$`\omega=0\iff\mathscr R_P(K)\ne\varnothing`$、
接続写像について $`\partial[z]=[\delta]`$、および
$`\Omega\cong\ker(H^2(K,P)\to H^2(U,P_U)\oplus H^2(V,P_V))`$ を証明する。
範囲制限後の通常のhomotopy pullbackが実修復と一致しないことを完了条件W2で示す。

### C. 全変更範囲に共通する有限生成と全修復の合成

各実全核に同一有限体 $`k`$ 上の有限次元構造を与え、核輸送を線形とする。
実核の演算・基底・包含・実輸送・実defectの座標を扱う有限データと、0〜3-cellを全て覆う
閉じた部分表示の有限被覆 $`(U_i)`$ を入力とする。
各領域では、常時補正可能で他領域と共有しない辺だけを内部変数 $`x_i`$ とし、
共有辺と全候補辺の補正値を $`z_i`$ に残す。同じ実微分とdefectから

```math
D_ix_i+F_iz_i=r_i,\qquad d_i^0b=(a_ib,c_ib),\qquad r_i=-\delta|_{U_i}
```

を生成する。有限線形消去により、公開アフィン関係
$`R_i=\{z_i:q_iF_iz_i=q_ir_i\}`$、$`q_i:V_i\to\operatorname{coker}D_i`$、
内部自由度 $`N_i=\ker D_i`$、復元section、元の0-cochainによる作用、共有部分への制限を
持つ局所groupoid $`\mathcal I_i`$ を一度生成する。生成手続きの停止と出力の正確性を証明する。

全 $`S\subseteq\mathsf E`$ について、候補の零条件を課し、共有辺の補正値と共有頂点の
再同定をそれぞれ厳密に一致させて $`\operatorname{Glue}_S(\mathcal I_i)`$ を定める。
独立に定義した実修復との間に相互逆な関手

```math
\operatorname{coord}_{\mathcal U,S}:\mathscr R_{P,S}(K)
\rightleftarrows\operatorname{Glue}_S(\mathcal I_i):\operatorname{rec}_{\mathcal U,S}
```

を構成する。候補名と値、元の実辺、全ての再同定を保持し、$`S\subseteq T`$ と交換させる。
存在判定は $`z_i\in R_i`$、共有値の一致、禁止候補の零条件だけと同値にし、
その解から局所に保持した復元データと任意の内部自由度によって全実修復・全ての射を戻す。
非空の $`R_i`$ は高々 $`\dim Z_i`$ 本の独立なアフィン方程式で表示する。
有限被覆の細分化、組立て順序・括弧づけ、基底・section・参照持ち上げの変更に対する
比較を構成し、比較の合成と同じ実復元の可換性を証明する。

### D. 不能証拠と全変更範囲の完全分類

同じ大域微分を $`Dx+\sum_{e\in\mathsf E}E_ey_e=-\delta`$ と分け、
$`\mathsf O=\operatorname{coker}D`$、$`o=q(-\delta)`$、$`B_e=qE_e`$、
$`\mathsf R_S=\sum_{e\in S}\operatorname{im}B_e`$ を構成する。
Cの局所関係を合成・消去して得る条件と同じ写像で対応させ、全 $`S`$ について

```math
\mathscr R_{P,S}(K)\ne\varnothing\ \Longleftrightarrow\ o\in\mathsf R_S
\ \Longleftrightarrow\
\forall\lambda\in\mathsf O^*,\quad
\lambda(o)\ne0\ \Longrightarrow\ S\cap E_\lambda\ne\varnothing,
\qquad E_\lambda=\{e:\lambda\circ B_e\ne0\}
```

を証明する。包含極小の修復可能範囲を、証拠支持族
$`\mathcal H_o=\{E_\lambda:\lambda(o)\ne0\}`$ の極小横断集合として分類する。
$`o=0`$ では空集合が唯一の極小範囲、全候補でも不能な場合は空の証拠支持により
横断集合が存在しないことを含める。失敗した範囲にはそれを排除する双対証拠を、成功した
範囲には同じ実辺への全補正と再同定を構成する。
$`\mathsf O/\mathsf R_{\mathsf E}\cong C_P^2/\operatorname{im}d^1`$ と誘導 $`d^2`$ を介し、
同じ $`o`$ の像を相対障害 $`[-\delta]`$ へ対応させる。

### E. 値更新、文脈同値、内部辺分割

**記号的生成と値更新。** 構造・核輸送・基底を固定した実入力族で、原始操作から
$`r_i(v)=r_{i,0}+B_iv`$ を生成できる場合、値の取得前にCの関係と復元を記号的に生成する。
defectだけの更新では消去・kernel・section・再同定作用を共用し、右辺と復元の
アフィン項の更新が全 $`S`$ の判定・復元と交換することを証明する。

**文脈同値。** Fの有限アフィン族で、共有部分表示 $`W`$ の対象・基準実操作・core・
比較・固定部分と候補名を共有する二領域 $`U,U'`$ を取る。
$`C_U(S)`$ を、Cの公開関係に候補零条件を課してから内部候補を消去した共有座標の関係とする。
環境は $`W`$ で厳密に貼り合わせ、共有候補に同じ許可条件を課す。
環境族はn1017 §3.2の平行な禁止候補辺と恒等比較の面の追加に閉じるものとする。
実操作から共有修復値 $`t`$ を指定する一点試験環境を構成し、
$`\forall S,\ C_U(S)=C_{U'}(S)`$ と、全ての許容外部環境・整合する候補許可条件に対する
修復の存在一致との同値を証明する。

**内部辺分割。** Aの可換群の入力で、$`e\in E_0`$ が $`W`$ に属さないとする。
同じ塔で $`\widetilde L_e=L_2L_1`$ を与え、両因子にAの強さ・核輸送の同型性を課す。
新頂点 $`w`$ は $`P,W`$ に含めず、両因子を常時補正可能とし、候補名を保つ。
全ての経路・面・3-cellの書き換え文脈で $`e`$ を $`e_2e_1`$ へ置換して $`K'`$ を構成する。
実合成から $`\rho_e=\rho_2\rho_1`$ を導き、補正の縮約
$`h_e=h_2+\rho_2h_1`$ による同値 $`\mathscr R_{P,S}(K')\simeq\mathscr R_{P,S}(K)`$ を
全 $`S`$ に同じ式で構成する。逆関手・自然同型、$`W`$ 上の厳密な一致、範囲包含・外部との
合成との可換性、旧修復への全ての分割補正の復元を証明する。
複体の分解 $`C^\bullet(K',P)\cong C^\bullet(K,P)\oplus[A_w\xrightarrow{1}A_w]_{0,1}`$、
障害・相対コホモロジー・旧閉路holonomyの保存も同じ写像で示す。
有限体の場合はCの公開関係とDの $`\mathsf O,o,B_e,\mathcal H_o`$、極小修復範囲を保存する。

### F. 実アフィン操作による実現

任意の有限体 $`k`$ と $`A=k^d`$ について、全ての可逆アフィン写像を実操作とする。
線形成分射影による塔 $`B\operatorname{Aff}(A)\to B\operatorname{GL}_k(A)\to\mathbf1`$ を作り、
実射影の全核が平行移動 $`A`$、実核輸送が各辺の線形成分 $`M_e`$ であることを示す。
元の辺と基準辺を保ってAのcore再選択を構成し、平行移動の指定比較と実3-cell整合から
一般入力の各条件を証明する。全核を中央化する比較がちょうど平行移動であることも示す。
経路の実合成からdefect・微分を計算し、独立に定義した実アフィン修復とA–Eの対象・射を
相互に対応させる。各対応は固定条件・候補名・部分表示への制限を保持する。
この実現では、有限な実写像の評価と合成からCの座標データを得る手順も構成する。

## 前提・構成台帳

| 対象・条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 塔、有限表示、元辺、core、持ち上げ、比較(A) | 原始入力として保持 | Aの実射・core・指定比較 | G-129の一般塔から相対修復へ |
| 強さ、全核の可換性、核輸送の全単射性、比較の中央化・3-cell整合(A) | 一般定理の仮定。F・W1–W5では証明義務 | G-129 Aの同じ条件と実射からの検査 | 輸送・微分・実defect・再同定へ |
| 閉じた部分表示、固定部分、辺の分割、被覆(A–C) | 入力条件 | セルの閉包、固定実辺の整合、被覆 | 制限・相対複体・範囲付きの合成へ |
| 修復、複体、descent、障害対応(A・B) | 構成・証明義務 | A・Bの往復、射、完全性、接続写像 | 元の実操作から存在・分類へ |
| 有限体・有限次元・実座標(C–F) | 有限生成の入力条件。Fで実現 | Cの有限表現と実射への包含 | 消去・双対分離・有限構成へ |
| 局所関係、復元、作用、全範囲分類(C・D) | 構成・証明義務 | Cの相互逆、Dの同じ商と証拠支持 | 局所データから全実修復と極小範囲へ |
| アフィンに変わる実入力、試験環境族、実辺の分解(E) | 各経路の入力条件 | Eの実現・閉包・強さ | 記号的更新、文脈同値、内部辺分割へ |
| 更新則・一点試験・分割比較(E) | 構成・証明義務 | 同じ復元との可換性、自然同型、複体分解 | 外部との合成と全範囲の再利用へ |
| 全アフィン写像と指定例(F・W1–W5) | 原始入力からの構成・証明義務 | 全核、輸送、仮定、実修復への往復 | 一般定理の適用と反例の検査へ |

## 完了条件

1. A–Fを同じ実操作・全核・輸送・defect・候補名についてLeanで構成・証明し、
   `target-theorem-proved` とする。
2. 次のW1–W5をFの実操作として構成し、一般定理への接続を証明する。

| witness | 固定データ | 必須の決定・対応 |
| --- | --- | --- |
| W1：一貫した有限変換網 | n1017 §5.8の $`\mathbb F_3`$、固定 $`p,r_x,r_y`$、$`E_0=\{e,a\}`$、候補 $`\{b,c\}`$、二つの指定Law。全 $`(x,y)`$ | 実合成から $`u+z=x,u-z+v=y`$、局所生成、全4範囲の全修復・同型類数、$`o=y-x`$、極小範囲と証拠、値更新と内部分割の全復元。$`a`$ の線形成分を $`1`$ にした同じ許可条件で極小範囲が空になる比較 |
| W2：範囲付きdescentの反例 | §2.5の二辺経路、$`A=\mathbb F_3`$、固定両端点、全辺候補、$`S=\varnothing`$ | 大域修復と両局所が一点、重なりが $`BA`$、通常のhomotopy pullbackが離散 $`A`$。Cの厳密合成は大域の対象・射を回復 |
| W3：射を保持する必要性 | §5.6の二辺閉路、$`A=\mathbb F_3^2`$、$`P=\varnothing`$、面・3-cellなし、両辺候補。$`T(x,y)=(x+y,y)`$ と $`T=I`$ | 同じ解spanに対して同型類数・自己同型群がそれぞれ $`3,\mathbb F_3`$ と $`9,A`$。局所の $`\pi_0`$ だけの貼り合わせと、候補禁止時の通常descentの不一致 |
| W4：分割の固定条件 | §5.7の $`\mathbb F_3`$、$`c=1`$、$`E_0=\{a\}`$、候補 $`\{b\}`$、指定実分解 | 候補許可時の実修復数 $`3\to9`$、同型類数3と自明自己同型の保存、全分割補正。新頂点も固定した別入力では同型類数9となること |
| W5：相対障害と局所案 | §5.2の $`\mathbb F_2`$、三平行辺、固定両端点と $`a,b`$、共有辺 $`e`$、全 $`(b_1,b_2)`$ | 局所は常に可解、相対障害とBの商障害が $`b_2-b_1`$、大域可解性が $`b_1=b_2`$ と一致。絶対 $`H^2=0`$ との比較 |

3. Lean成果を `research/lean/ResearchLean/AG/RelativeRepairComposition/` に置き、
   `research/reports/G-130-aat-relative-repair-composition.md` にA–F、W1–W5と宣言、
   前提の出所・使用先、同じ実操作への対応、有限構成の停止・正確性を対応させる。
4. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従って完了を判定する。適用版、検証、査読、実行状態はIssue・reportへ置く。
