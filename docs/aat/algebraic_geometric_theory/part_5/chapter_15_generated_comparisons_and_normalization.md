# 第15章 生成比較と正規化

輸送してから制限する経路と、制限してから輸送する経路は、同じ始域・終域を持っても
比較の構成を必要とする。さらに正規化を加えると、比較が保つのは冪等射の像となる。
本章ではこの二段階を区別し、変更の保存・反映・全持ち上げを調べる。
意味圏の全ての射を保持し、群による分類はその可逆部分に適用する。

## 15.1 二経路と標準比較

**設定15.1（随伴を持つ可換平方）.**
[第14章](chapter_14_transport_along_readings_and_coefficients.md)で構成したexact readingの底、
または多重線形等式理論と係数の底 $`(\mathbb T,R)`$ について平方

```math
\begin{array}{ccc}
b_{12}&\xrightarrow{p_2}&b_2\\
{\scriptstyle p_1}\downarrow&&\downarrow{\scriptstyle s_2}\\
b_1&\xrightarrow{s_1}&b_0
\end{array}
\qquad s_1p_1=s_2p_2
```

を取る。各辺 $`u`$ の順方向関手を $`L_u`$、逆方向関手を $`R_u`$ とする。
使う随伴 $`L_u\dashv R_u`$ は、定理14.5の名前を戻すHom対応、
補題14.6aのbalanced写像のHom対応、構成14.6bの生成元と関係から得るHom対応、
および命題14.6cの混合した合成から構成する。
係数辺を含む後者の底では、全sortが可変加群sortであることを含め、補題14.6aの理論の範囲を用いる。
一般の正の存在式の理論には構成14.6bの反例があり、随伴を同じ方法では供給できない。
単位を $`\eta^u:1\to R_uL_u`$、余単位を $`\varepsilon^u:L_uR_u\to1`$ と書く。
輸送の合成比較から

```math
\Sigma:L_{s_2}L_{p_2}\xrightarrow{\sim}L_{s_1}L_{p_1},\qquad
D=L_{p_2}R_{p_1},\quad V=R_{s_2}L_{s_1}:
\mathcal A_{b_1}\longrightarrow\mathcal A_{b_2}
```

を作る。$`\Sigma=c_{s_1,p_1}^{-1}c_{s_2,p_2}`$ であり、平方の等号で直接輸送の終域を同定する。
ここで $`c`$ はexact readingには命題14.6、解釈・係数の混合には命題14.6cの比較である。

**定理15.2（生成されたBeck–Chevalley比較）.**
次の合成は自然変換 $`\alpha:D\Rightarrow V`$ を与える。

```math
DX\xrightarrow{\eta^{s_2}_{DX}}R_{s_2}L_{s_2}DX
\xrightarrow{R_{s_2}\Sigma_{R_{p_1}X}}
R_{s_2}L_{s_1}L_{p_1}R_{p_1}X
\xrightarrow{R_{s_2}L_{s_1}\varepsilon^{p_1}_X}VX.
```

このmateは $`\Sigma`$ と二つの随伴から一意に決まり、随伴と輸送の選択を
それらの標準同型で変更しても対応する。各辺がexact輸送の場合は自然同型である。

**証明.**
各矢印は自然変換またはその関手による像であるから、合成も自然である。
随伴のHom全単射を $`L_{s_2}`$ と $`L_{p_1}`$ について順に適用する。
自然変換 $`L_{s_2}L_{p_2}\to L_{s_1}L_{p_1}`$ の成分を、右側の
$`L_{p_1}R_{p_1}X`$ で余単位と合成し、左側の随伴で戻すと上式を得る。
逆操作は単位を挿入して左側の余単位を用いる。二往復は三角恒等式で恒等になる。
従って自然変換どうしのこの対応は全単射であり、mateの一意性を得る。
Hom対応と整合する同型で各随伴を替えれば、同じ全単射の同じ元になる。
exactの場合は定理14.5の単位・余単位と $`\Sigma`$ がすべて可逆であり、
上の三矢印を逆順に逆にして $`\alpha^{-1}`$ を得る。□

**合成する平方。** 二平方を貼り合わせた直接のmateと、各mateを合成した比較は一致する。
実際、双方を上のHom全単射で順方向の自然変換へ戻すと、途中の単位・余単位が
三角恒等式で消え、命題14.6または14.6cの同じ合成比較になる。この計算は恒等平方にも適用できる。
これにより対象だけでなく、任意の意味射 $`h:X\to X'`$ に対して
$`V(h)\alpha_X=\alpha_{X'}D(h)`$ を伴う二経路比較を得る。

**例15.2a（非可逆な解釈と係数を混ぜた平方）.**
操作を持たない加群理論から、単位付き結合的代数の理論への解釈 $`u`$ を取る。
構成14.6bの左随伴はtensor代数
$`L_u^R(M)=T_R(M)=\bigoplus_{n\ge0}M^{\otimes_Rn}`$ である。
実際、線形写像 $`M\to A`$ は純tensorをその像の積へ送る唯一の単位的代数準同型に延びる。
底の平方は上辺と下辺を $`u`$、左右の辺を環射 $`b:R\to R'`$ とする。
すなわち $`b_{12}=(\mathbb T_{\mathrm{mod}},R)`$、$`b_2=(\mathbb T_{\mathrm{alg}},R)`$、
$`b_1=(\mathbb T_{\mathrm{mod}},R')`$、$`b_0=(\mathbb T_{\mathrm{alg}},R')`$ である。
$`\Sigma`$ はtensorの係数を掛ける命題14.6cの比較となる。

$`R'`$-加群 $`X`$ に対するmateは

```math
\alpha_X:T_R(U_bX)\longrightarrow U_bT_{R'}(X),\qquad
x_1\otimes_R\cdots\otimes_Rx_n\longmapsto
x_1\otimes_{R'}\cdots\otimes_{R'}x_n.
```

次数0では $`b:R\to R'`$ である。
定理15.2の単位は $`z\mapsto z\otimes1`$、余単位は係数による作用なので、生成元に適用するとこの式になる。
同じ式は純tensorの連接と単位を保ち、構成した代数準同型に一致する。
$`R=\mathbb Z,R'=\mathbb Q,X=0`$ ではmateは $`\mathbb Z\to\mathbb Q`$ となり、同型でない。
従って混合比較 $`\Sigma`$ は可逆でも、そこから生成するmateの可逆性は別の条件である。

## 15.2 冪等正規化と像

**定義15.3（冪等射とKaroubi圏）.**
任意の圏 $`\mathcal E`$ において $`d:Y\to Y`$、$`d^2=d`$ を冪等射と呼ぶ。
分裂は $`Y\xrightarrow{q}Q\xrightarrow{s}Y`$、$`qs=1_Q`$、$`sq=d`$ である。
$`\mathrm{Kar}(\mathcal E)`$ の対象は $`(Y,d)`$、射
$`h:(X,e)\to(Y,d)`$ は $`h=dhe`$ を満たす元の圏の射とする。
合成は元の合成、恒等は $`1_{(Y,d)}=d`$ である。
$`h=dhe`$ は $`dh=h=he`$ と同値であり、これらの式から圏の公理が従う。

分裂があれば $`q:(Y,d)\to(Q,1)`$ と $`s`$ は互いに逆である。
さらにKaroubi圏内の冪等射 $`a:(Y,d)\to(Y,d)`$ は対象 $`(Y,a)`$ と
両方向の射 $`a`$ によって分裂する。したがってこの圏では像を対象として扱える。

**定理15.4（正規化分解と像の同型）.**
同型 $`\alpha:X\to Y`$ と冪等射 $`d:Y\to Y`$ に対し

```math
\beta=d\alpha,\qquad e=\alpha^{-1}d\alpha,\qquad
\gamma=\alpha^{-1}d
```

と置く。このとき $`e^2=e`$ であり、$`\beta`$ が元の圏で可逆であることと $`d=1_Y`$ は同値である。
同じ射はKaroubi圏で同型 $`\beta:(X,e)\xrightarrow{\sim}(Y,d)`$ を与え、逆は $`\gamma`$ である。

**証明.**
共役の式から $`e^2=\alpha^{-1}d^2\alpha=e`$ を得る。
$`\beta`$ が可逆なら $`d=\beta\alpha^{-1}`$ も可逆であり、$`d^2=d`$ から $`d=1`$ が従う。
逆は $`\beta=\alpha`$ から明らかである。
次に $`d\beta e=\beta`$、$`e\gamma d=\gamma`$ を計算すると

```math
\gamma\beta=e=1_{(X,e)},\qquad \beta\gamma=d=1_{(Y,d)}.
```

したがって両射はKaroubi圏で逆である。□

AATでの具体的な供給源は
[定理9.8](../part_3/chapter_9_quotients_symmetry_and_lifts.md#93-保存section冪等射分裂)である。
同章の操作系で商 $`q:Y\to Q`$ と操作・観測保存section $`s`$ があると、$`d=sq`$ は意味圏の冪等射になる。
像は全操作で閉じ、量と観測は制限される。
Lawはこの分裂の対象 $`Q`$ に課されたものを用いる。
一般の理論で像に新しい構造を与えるときは、domain・関係・Lawがその構造へ降りることを確認する。
元の圏に分裂を構成していない場合も、定理15.4のKaroubi圏での結論は成立する。

**例15.5（四点と二点）.**
操作を恒等、観測を定数とし、次の四点の間の同型を取る。

| $`x`$ | $`\alpha(x)`$ | $`d\alpha(x)`$ | $`e(x)`$ |
| --- | --- | --- | --- |
| $`x_0`$ | $`1`$ | $`0`$ | $`x_2`$ |
| $`x_1`$ | $`3`$ | $`2`$ | $`x_3`$ |
| $`x_2`$ | $`0`$ | $`0`$ | $`x_2`$ |
| $`x_3`$ | $`2`$ | $`2`$ | $`x_3`$ |

ここで $`d(0)=d(1)=0`$、$`d(2)=d(3)=2`$ とした。
表から冪等性と $`e=\alpha^{-1}d\alpha`$ を確認できる。
$`\beta`$ は四点では非単射だが、像 $`\{x_2,x_3\}\to\{0,2\}`$ では全単射である。

**台帳への適用。** 例14.8の $`q(x,y)=x+y`$ と $`s(z)=(z,0)`$ は $`qs=1`$ を満たす。
readとapplyを持つ操作系では両者が構造保存射で、$`d(x,y)=(x+y,0)`$ の像は単一台帳と同型である。
同じ名前のcompactも保存するsectionを要求すると、$`s(z)\mapsto(z-t,t)`$ は像を出る。
その場合はcompactを空語へ翻訳した変更問題を使う必要がある。

## 15.3 変更との自然性

**構成15.6（比較を保つ変更の圏）.**
対象を $`(X,Y,c:X\to Y)`$、射を対 $`(a,b)`$ で
$`bc=c'a`$ を満たすものとする。二射の合成は $`(a'a,b'b)`$ であり、
可換式を合成すれば再び射となる。これが比較の圏である。

さらに冪等射 $`e:X\to X`$、$`d:Y\to Y`$ を持ち $`dc=ce`$ を満たす対象を考える。
射には $`ae=e'a`$、$`bd=d'b`$ も課す。
正規化した比較を $`\bar c=dce=dc=ce`$ とすると、関手

```math
\mathcal N:(X,Y,c,e,d)\longmapsto
\bigl((X,e),(Y,d),\bar c\bigr),\qquad
(a,b)\longmapsto(e'ae,d'bd)
```

を得る。たとえば
$`(d'bd)\bar c=d'bc e=d'c'a e=\bar c'(e'ae)`$ である。
合成は中間の冪等射を交換させて消せ、恒等対は $`(e,d)`$ へ移る。

自然同型 $`\alpha:D\Rightarrow V`$ と自然な冪等射 $`d:V\Rightarrow V`$ に対しては、
$`e=\alpha^{-1}d\alpha`$ が $`D`$ の自然な冪等射となり、$`d\alpha`$ は
Karoubi圏値の関手の自然同型になる。自然性は
$`V(h)d_X=d_{X'}V(h)`$ と $`V(h)\alpha_X=\alpha_{X'}D(h)`$ を合成した式である。
各対象で任意に選んだsectionを自然なsectionとして扱うには、前者の可換式を別に確かめる。

第8章の固定図式の各辺にこの比較を配置すれば、可換な変更対と固定trivializationを
同時に保持できる。評価条件を運ぶ場合には定理14.10を用い、正規化後の条件だけから
元の許容条件を復元できるかは次節の反映の問題とする。

## 15.4 保存・反映・持ち上げ

**定義15.7（実比較から作る群）.**
構成15.6の一対象を固定し、

```math
G=C_{\mathrm{Aut}(X)}(e)\times C_{\mathrm{Aut}(Y)}(d),\qquad
\Gamma=\{(a,b)\in G\mid bc=ca\}
```

とする。中心化とは $`ae=ea`$、$`bd=db`$ をいう。
$`\Gamma`$ は可換式の合成と逆で閉じるので部分群である。
像側の端点自己同型群を
$`Q=\mathrm{Aut}_{\mathrm{Kar}}(X,e)\times\mathrm{Aut}_{\mathrm{Kar}}(Y,d)`$、
その中で $`\bar c`$ を保つ部分群を $`\Delta`$ とする。

```math
r:G\longrightarrow Q,\qquad r(a,b)=(eae,dbd)
```

は準同型である。$`a^{-1},b^{-1}`$ も冪等射と交換し、像の逆を与える。
構成15.6から $`r(\Gamma)\subseteq\Delta`$ が従う。
このように群と適合部分群は、端点の実変更と比較式から作られる。

**定理15.8（反映と全持ち上げ）.**
任意の群準同型 $`r:G\to Q`$ と部分群 $`\Gamma\le G`$、$`\Delta\le Q`$ に
$`r(\Gamma)\subseteq\Delta`$ を仮定すると

```math
r^{-1}(\Delta)=\Gamma
\quad\Longleftrightarrow\quad
\ker r\subseteq\Gamma\quad\text{かつ}\quad
r(\Gamma)=\Delta\cap\mathop{\mathrm{im}}r.
```

また、指定 $`\delta\in\Delta`$ の適合するliftは $`\delta\in r(\Gamma)`$ のとき存在する。
一つのliftを $`\gamma_0`$ とし、$`L=\ker(r|_\Gamma)`$ と置けば、その全体は右 $`L`$-torsor
$`(r|_\Gamma)^{-1}(\delta)=\gamma_0L`$ である。

**証明.**
左辺を仮定すると単位の原像は $`\Gamma`$ に入る。
$`\delta\in\Delta\cap\mathop{\mathrm{im}}r`$ を持ち上げた $`g`$ も $`\Gamma`$ に入るので像の等号を得る。
逆に右辺を仮定し $`r(g)\in\Delta`$ とする。
像の等号により $`r(\gamma)=r(g)`$ となる $`\gamma\in\Gamma`$ があり、
$`\gamma^{-1}g\in\ker r\subseteq\Gamma`$ だから $`g\in\Gamma`$ となる。
持ち上げの存在条件は像の定義である。
二つのlift $`\gamma_0,\gamma`$ の差 $`\gamma_0^{-1}\gamma`$ は $`L`$ に入り、
逆に右から $`L`$ を掛けても同じ像になる。この差は一意なので作用は自由かつ推移的である。□

**例15.9（観測では見えない不適合変更）.**
$`X=Y=\{0,1,2\}`$、$`c=1`$、$`e=d`$ を0への定値写像とする。
操作は恒等、観測は定数である。置換 $`\tau=(12)`$ は $`d`$ と交換する。
$`(\tau,1)\in\ker r`$ だが $`1c\ne c\tau`$ なので $`\Gamma`$ に入らない。
像は一点で比較を保つため、反映が失敗する。
その一つの像の変更には $`(1,1)`$ と $`(\tau,\tau)`$ という二つの適合liftがある。

同じ三点集合で $`e(0)=0,e(1)=e(2)=1`$ とすると、像の恒等比較は0と1の同時交換を許す。
しかし $`e`$ と交換する全単射は、各fiberを対応するfiberへ全単射に送る。
fiberの大きさは1と2なので、その交換は持ち上がらない。
第二例の中心化群は自明なので $`G=\Gamma=1`$、$`\Delta\cong\mathbb Z/2`$ である。
従って反映の核条件と $`r(\Gamma)=\Delta\cap\mathop{\mathrm{im}}r`$ は両方成立するが、
$`r|_\Gamma`$ は全射でない。第一例の適合性の反映失敗と、第二例の指定変更のlift不能は異なる現象である。

## 15.5 持ち上げの全体と残る自由

$`r|_\Gamma`$ が全射なら短完全列

```math
1\longrightarrow L\longrightarrow\Gamma\longrightarrow\Delta\longrightarrow1
```

を得る。各 $`\delta`$ のliftを一つずつ選ぶことと、合成を保つ群sectionを選ぶことは異なる。
選択 $`s(1)=1`$ に対して
$`a(\delta_2,\delta_1)=s(\delta_2)s(\delta_1)s(\delta_2\delta_1)^{-1}\in L`$ がその差を測る。
これが全対で1となることと、選択が群準同型であることは同値である。
たとえば $`\mathbb Z/4\to\mathbb Z/2`$ は全射だが、非零元のliftは奇数なので位数4であり、
位数2の元を持つ群sectionは存在しない。

非可逆な変更を対象として保持するため、構成15.6の正規化関手を
$`\mathcal N:\mathcal K\to\mathcal K'`$ と書き、矢印圏 $`\mathrm{Ar}(\mathcal K)`$ を作る。
その対象は任意の射 $`h:X\to Y`$、射 $`h\to h'`$ は $`b h=h'a`$ を満たす対 $`(a,b)`$ である。
可逆な比較だけを残したcore $`\mathrm{Ar}(\mathcal K)^\simeq`$ でも、対象 $`h`$ 自体の可逆性は要求しない。
正規化は $`h\mapsto\mathcal N(h)`$、$`(a,b)\mapsto(\mathcal N(a),\mathcal N(b))`$ により
関手 $`\mathcal N^\to:\mathrm{Ar}(\mathcal K)^\simeq\to\mathrm{Ar}(\mathcal K')^\simeq`$ を定める。
可換平方とその合成を関手で送るので、この式は対象・全比較・恒等・合成を保つ。

観測側の指定射 $`\delta`$ の全liftは、この関手の2-fiberとする。
対象は $`(h,\theta:\mathcal N^\to(h)\cong\delta)`$、比較は
$`\zeta:h\cong h'`$ で $`\theta'\mathcal N^\to(\zeta)=\theta`$ を満たすものとなる。
$`\theta`$ は端点の二つの同型からなる可換平方であり、この式はその両成分の等号である。
これは第7章の全変更groupoidと同じ「矢印圏のcore」の構成を、比較と正規化の圏へ適用したものである。
第8章の $`\mathcal F^{\partial}_{a,H,V}`$ と同じ2-fiber・部分関手の構成で、
さらに固定条件と評価を加えられる。対象の集合だけに落とす前に比較射を保持する。
たとえば二点の一方への冪等写像には逆射がなく、群 $`G`$ の元にはならないが、
この全変更fiberの対象として扱える。

第9章のholonomyから作った全liftにも、定理15.8をその実群準同型へ適用できる。
本章はその分類を一般の比較と正規化へ置き、第16章では線形な複体比較の核・余核へ接続する。
第17章の観測十分性には、例15.9のような観測で区別されない変更を渡す。
第19章の再構成には、元の圏での比較、Karoubi圏での像の比較、全変更fiberを区別して渡す。

**問題15.10.**
指定された意味圏と許容規則 $`H`$ について、構成15.6の非可逆変更のfiberを
原始操作の式から表示せよ。像側の変更の存在と、その間の全比較射のliftをそれぞれ判定すること。

**問題15.11.**
構成14.6bの非exactな等式理論解釈に対し、定理15.2で構成したmateの可逆性を
Law表示と操作の翻訳から判定せよ。部分操作domainを含める拡張では、まず該当する圏で左随伴を構成すること。
さらに、条件付き解族に制限したmateの可逆性と、意味圏全体での可逆性の関係を求めよ。
