# G-128-aat-minimal-compatibility-observations — 適合性を決定する最小観測集合

- `id`: `G-128-aat-minimal-compatibility-observations`
- `status`: `active`
- `research mode`: `target-theorem`
- `tracking issue`: [#5075](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5075)
- `source note`: [n1016 §5.2・候補05](../../docs/note/n1016_rising_sea_v2_paper_plan.md)
- `design`: [構成・証明方針と再利用対応](../designs/G-128-aat-minimal-compatibility-observations/README.md)

## 研究目的

許された点観測から、未知の変更が操作・比較を保つかどうかを判定するために必要な
最小観測数を明らかにする。点を固定する部分群から、判定可能性、最小観測集合、
適応的な問い合わせの最悪時下限、有限表からの構成と判定不能の証拠を導く。
研究対象となる費用は、未知の変更への正確な点評価の問い合わせ回数とする。

[G-120](G-120-aat-comparison-information-loss.md)と
[Rising Sea 定理7.9](../../outreach/paper/rising-sea/ja/10-comparison-and-information.md)の
観測核による適合性判定を、群作用の点観測へ広げる。
[G-127](G-127-aat-reversible-protocol-holonomy.md)の名前付き操作から、判定対象となる
周囲の変更群、その適合部分群、観測対象への作用を構成する。
[G-124 D・E](G-124-aat-local-semantic-reconstruction.md)の変更の区別・観測表の延長と
対応させ、適合性だけの判定に必要な情報を特定する。

## 固定target

A–Eを一つの最小観測・構成定理の構成部分とする。A・Dは任意の群作用について述べ、
B・CとEの計算部分では有限表を入力とする。量化順は、群作用と適合部分群、観測集合
または問い合わせ手続き、その後に未知の変更 $`g\in G`$ とする。
適合性の判定は周囲の群の全要素を対象とする。観測点集合には空集合を許す。

### A. 点観測による判定と最小観測数

群 $`G`$、集合 $`X`$、左作用 $`G\curvearrowright X`$、部分群 $`\Gamma\le G`$ を
入力とする。$`\Gamma`$ の正規性と作用の忠実性は仮定しない。
任意の有限集合 $`B\subseteq X`$ について

```math
O_B(g)=(g\cdot x)_{x\in B},\qquad
G_{(B)}=\{g\in G\mid\forall x\in B,\ g\cdot x=x\}
```

を構成する。観測による適合性判定を

```math
\exists P:(B\to X)\to\mathrm{Prop},\quad
\forall g\in G,\quad P(O_B(g))\ \Longleftrightarrow\ g\in\Gamma
\tag{A1}
```

と定め、(A1)と $`G_{(B)}\subseteq\Gamma`$ の同値を証明する。
同じ観測を持つことを $`O_B(g)=O_B(h)\iff h^{-1}g\in G_{(B)}`$ で特徴づける。
この条件を満たす有限集合の最小濃度を

```math
b_\Gamma(G\curvearrowright X)
=\min\{|B|\mid B\subseteq X\text{ は有限},\ G_{(B)}\subseteq\Gamma\}
\in\mathbb N\cup\{\infty\}
\tag{A2}
```

とし、該当する有限集合がない場合を $`\infty`$ とする。
$`b_\Gamma=0\iff\Gamma=G`$ を示し、$`\Gamma=\{1\}`$ の場合には(A1)の条件が
$`O_B`$ の単射性と同値であることを示す。

任意の群準同型 $`O:G\to L`$ に対し、$`X=L`$、$`g\cdot x=O(g)x`$、
$`B=\{1_L\}`$ と置くと、点安定化群が $`\ker O`$ となり、(A1)がG-120の
観測核による判定と同じ観測・適合述語を与えることを証明する。

### B. 適応的な問い合わせの最適最悪時回数

$`G,X,\Gamma`$ と作用を既知の有限表で与える。未知の $`g\in G`$ への問い合わせは、
選んだ $`x\in X`$ に対する正確な値 $`g\cdot x`$ の取得とする。
決定的な手続きは過去の質問と答えだけから次の点または判定結果を選ぶ。
すべての $`g\in G`$ について停止し、$`g\in\Gamma`$ かどうかを常に正しく返すことを
要求する。問い合わせ間の計算は自由とし、同じ点への再問い合わせも一回と数える。

各手続きの最悪時問い合わせ回数を全 $`g\in G`$ にわたる最大値とする。
正答する手続きの中での最小値を $`D_\Gamma`$ とし、そのような手続きがなければ
$`D_\Gamma=\infty`$ と定め、

```math
D_\Gamma(G\curvearrowright X)=b_\Gamma(G\curvearrowright X)
\tag{B1}
```

を証明する。有限値の場合には、その値を達成する固定観測集合と判定手続きを構成する。

### C. 有限表からの構成、集合被覆、観測表の延長

有限集合 $`G,X`$ の列挙・等号判定、群の積・単位元・逆元、作用と部分群 $`\Gamma`$ の
所属を表で与え、Aの群・作用・部分群の公理を入力条件とする。
同じ表から次の停止する手続きを構成し、それぞれの出力の正確性を証明する。

**最小集合と判定不能の証拠。** 有限な十分集合がある場合には、(A2)の値、最小集合
$`B_{\min}`$、その観測からの正確な適合性判定を返す。
ない場合には $`k\in G\setminus\Gamma`$ で $`\forall x\in X,\ k\cdot x=x`$ を満たす
元を返す。$`1`$ と $`k`$ は全点で観測が一致し適合性が異なること、これが
$`b_\Gamma=D_\Gamma=\infty`$ と同値であることを示す。

**集合被覆とgreedy法。** 入力から

```math
U=G\setminus\Gamma,\qquad
S_x=\{g\in U\mid g\cdot x\ne x\}
```

を構成し、$`B`$ が十分であることと $`\bigcup_{x\in B}S_x=U`$ の同値を示す。
未被覆の元を最も多く覆う点を毎回選ぶgreedy法を構成する。同数の場合は入力の
列挙順で選ぶ。被覆可能で $`U\ne\varnothing`$ の場合、返した集合 $`B_{\mathrm{gr}}`$ は
十分であり、

```math
|B_{\mathrm{gr}}|\le H_{|U|}\,b_\Gamma,
\qquad H_m=\sum_{i=1}^{m}\frac1i
\tag{C1}
```

を満たすことを証明する。$`U=\varnothing`$ の場合は空集合を返す。
被覆不能の場合は上記の $`k`$ を返す。

**指定された観測表の延長。** 任意の $`B\subseteq X`$ と表 $`t:B\to X`$ に対し、
$`O_B(g)=t`$ を満たす $`g\in G`$ の存在と、同じ条件を満たす $`g\in\Gamma`$ の存在を
それぞれ判定する。存在する場合には実際の変更を返し、存在しない場合には全候補の
不存在を証明する。前者は観測表の実現可能性、後者は適合する変更への延長である。

計算に関する定量的結論はBの問い合わせ回数と(C1)の観測点数とする。
有限構成の停止・正確性および費用の扱いは
[n1016 §9.1](../../docs/note/n1016_rising_sea_v2_paper_plan.md#91-一枚のカードで何を定めるか)に従う。

### D. 独立な系の合成と適合条件の変更

任意の二つの入力 $`G_i\curvearrowright X_i,\Gamma_i\le G_i`$ に対し、
$`G_1\times G_2`$ が非交和 $`X_1\sqcup X_2`$ の各成分へ対応する因子で作用し、
適合部分群が $`\Gamma_1\times\Gamma_2`$ である場合に

```math
b_{\Gamma_1\times\Gamma_2}
((G_1\times G_2)\curvearrowright(X_1\sqcup X_2))
=b_{\Gamma_1}(G_1\curvearrowright X_1)
+b_{\Gamma_2}(G_2\curvearrowright X_2)
\tag{D1}
```

を $`\mathbb N\cup\{\infty\}`$ の等式として証明する。有限値の場合には各因子の
最小集合の非交和が最小集合となることを示す。
同じ作用に対する任意の $`\Gamma_1\le\Gamma_2`$ について
$`b_{\Gamma_2}\le b_{\Gamma_1}`$ を証明する。

### E. 名前付き操作からの構成と既存の読取り・延長への対応

G-127 Aの任意の原始入力 $`Q=(V,E,s,t),\Pi,F(v),T_e,H`$ を取る。
有限な頂点・辺・fiberには空集合も許す。可視変更とfiberの全単射の対から

```math
G_{F,H}=\{(u,\varphi)\mid u\in H,\quad
\varphi_v:F(v)\simeq F(u_V(v))\text{ for every }v\in V\}
```

を構成し、G-127 (A2)と同じ合成によって群にする。この群の中で

```math
\Gamma_{F,H}=\{(u,\varphi)\in G_{F,H}\mid
\forall e\in E,\quad
\varphi_{t(e)}T_e=T_{u_E(e)}\varphi_{s(e)}\}
\tag{E1}
```

が部分群となることを証明する。G-127の実際の変更群 $`A_F`$ との群同型を、
同じ可視変更・頂点ごとの写像・可視射影を保って構成する。
適合群の各可視fiberと底を固定する部分群を、G-127 (C1)・(C2)の解と(B2)の
中心化群表示へ、それぞれ元の変更を保って対応させる。

全状態 $`S=\coprod_{v\in V}F(v)`$ に $`(u,\varphi)\cdot(v,x)=(u_V(v),\varphi_v(x))`$、
頂点に $`u_V`$、辺名に $`u_E`$ を作用させる。
観測対象 $`X_{\mathrm{st}}=S`$ と $`X_{\mathrm{all}}=V\sqcup E\sqcup S`$ への作用を
同じ原始入力から構成し、A–Dをそれぞれに適用する。
$`X_{\mathrm{all}}`$ の作用の忠実性と最小観測数の有限性を証明する。
G-127 Eの有限表から周囲の群・適合部分群・作用の表を作り、Cの各手続きの出力が
元の(E1)の判定と観測表の延長を与えることを示す。

恒等操作 $`F(v)=K,T_e=\mathrm{id}`$、$`\Pi=\varnothing,H=\{1\}`$、有限な非自明集合
$`K`$ に特殊化する。G-124の同じ成分代表集合 $`R`$ に対し、
$`B=\{(r,x)\mid r\in R,\ x\in K\}\subseteq S`$ とする。
既存の各頂点の置換の読取りを、適合群上の $`O_B`$ の点ごとの評価と対応させる。
頂点ごとの置換表から作った観測表について、同じ $`\mathrm{EdgeCoherent}`$ 条件の下で、
G-124の区別・延長とCの適合する変更への延長が一致することを示す。
延長した各頂点の写像を、G-127 (C2)の恒等操作への特殊化と一致させる。

## 既存宣言の参照

Research pathは `research/lean/ResearchLean/AG/` からの相対とする。
宣言の参照版はactive化時にtracking Issueへ記録する。

| 用途 | path・宣言 |
| --- | --- |
| Aの観測核との対応 | `ComparisonInformationLoss/ObservationKernel.lean` の `exists_observation_predicate_iff_ker_le` |
| Eの元の持ち上げ・変更群 | `ProtocolHolonomy/Basic.lean` の `ReversibleData.Lift`、`ProtocolHolonomy/ChangeGroup.lean` の `ReversibleData.ChangeGroup` |
| EのG-127 B–Eへの接続 | [G-127 reportのA–E対応](../reports/G-127-aat-reversible-protocol-holonomy.md)が指す原始入力・根条件・中心化群・有限表の各宣言 |
| Eの同じ成分代表と読取り・延長 | `LocalSemanticReconstruction/CSFixedFDetermining.lean` の `protocolRepresentativeSet`、`protocol_representatives_determining`、`ProtocolHolonomy/IdentityG124Determining.lean` の `identityLift_representatives_determining`、`ProtocolHolonomy/IdentityG124Extension.lean` の `identity_G124_C2_extension_agree` |

## 前提・構成台帳

| 対象・対応条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 群・作用・部分群(A・D) | 入力として保持 | Aの入力条件 | 点安定化群から判定・最小数・合成則へ |
| 観測・安定化群・最小数(A) | 構成・証明義務 | (A1)・(A2)、G-120への対応 | 元の作用からB–Dへ |
| 問い合わせモデル(B) | モデルとして保持 | Bの情報取得・停止・正答・回数の定義 | 全未知変更に対する(B1)へ |
| 有限表(C) | 実行可能な入力として保持 | Cの表と公理 | 最小集合、判定不能の元、greedy法、延長の停止・正確性へ |
| 被覆族と近似保証(C) | 構成・証明義務 | (C1)と十分性 | 元の作用表から観測点の選択へ |
| 操作系の周囲の群・適合群・作用(E) | 原始入力は保持、群・作用・対応は構成義務 | (E1)とEの対応 | G-127 Aの入力からA–Dの適用と元の変更への読み戻しへ |
| 恒等操作系の読取り・延長(E) | 既存宣言を再利用、同じ評価との対応は証明義務 | Eの特殊化 | G-124の代表・置換表からC・G-127 (C2)との一致へ |
| 完了条件2の有限例 | 全入力条件と結論の証明義務 | 指定した作用・適合群・観測対象 | 同じ例をA–C・Eへ適用 |

## 完了条件

1. A–Eを同じ群作用・観測・適合述語についてLeanで証明し、
   `target-theorem-proved` とする。指定した判定不能は、その不存在命題の証明として扱う。
2. **判定・識別・判定不能を分ける例。** G-127完了条件2の一頂点・二ループ
   $`a,b`$、fiber $`\{0,1\}`$、$`T_a=\mathrm{id},T_b=(01)`$、$`\Pi=\varnothing`$、
   辺名を交換する $`H=C_2`$ を使う。Eの実際の群と作用について、第一因子が辺名、
   第二因子が状態の交換に対応する群同型 $`G_{F,H}\cong C_2\times C_2`$ を構成する。
   この同型が適合部分群 $`\Gamma_{F,H}`$ を $`\{1\}\times C_2`$ に対応させることと、
   次を同じ入力で証明する。

   - $`X_{\mathrm{st}}`$ では $`b_{\Gamma_{F,H}}=\infty`$。Cは辺名だけを交換する
     不適合な元を、恒等元と全状態観測が一致する証拠として返す。
   - $`X_{\mathrm{all}}`$ では $`b_{\Gamma_{F,H}}=1`$。一点 $`a`$ の観測で判定できる。
   - 同じ $`X_{\mathrm{all}}`$ で全変更を識別する場合は $`b_{\{1\}}=2`$。
     辺名 $`a`$ と状態 $`0`$ の二点が最小集合となる。

   各場合をAの条件、Bの最適問い合わせ回数、Cの最小集合または判定不能の出力へ接続する。
3. Lean成果を `research/lean/ResearchLean/AG/` に置き、
   `research/reports/G-128-aat-minimal-compatibility-observations.md` にA–Eと宣言、
   前提の出所・使用先、有限例、手続きの停止・正確性の証拠を対応させる。
4. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従って完了を判定する。適用版、検証、査読、実行状態はIssue・reportへ置く。
