# 第2章 意味の対象と射

Lawを満たす一つの意味をモデルとして与え、その間の変更を実際の写像で表す。
射に課す条件は、状態の写像が操作・関係・domainをどう運ぶかである。
この章では、その条件から圏を作り、理論解釈による引戻しと全操作語の保存を証明する。
最後に、独立に定義したlensとprotocolの対象・全ての射を、この共通言語から回復する。

## 2.1 状態・操作・関係を持つ構造

**定義2.1（構造保存射）.**
署名 $`\Sigma`$ の構造は、[定義1.2](chapter_1_atoms_laws_theories.md#12-型操作関係部分操作量の宣言)の解釈データである。
二構造 $`A,B`$ の間の構造保存射 $`h:A\to B`$ は、sortごとの写像
$`h_s:X_s(A)\to X_s(B)`$ で、次を満たすものとする。

```math
\begin{aligned}
h_t(f_A(\boldsymbol a))&=f_B(h_{\boldsymbol s}(\boldsymbol a)),\\
\boldsymbol a\in r_A&\ \Longrightarrow\
  h_{\boldsymbol s}(\boldsymbol a)\in r_B,\\
\boldsymbol a\in D_p^A&\ \Longrightarrow\
  h_{\boldsymbol s}(\boldsymbol a)\in D_p^B,\\
h_t(p_A(\boldsymbol a))&=p_B(h_{\boldsymbol s}(\boldsymbol a))
  \quad(\boldsymbol a\in D_p^A).
\end{aligned}
\tag{2.1}
```

量にも第一式を課す。domain sortの包含を使うときは、
そのsortの写像と包含操作の可換性も第一式に含まれる。
射の等号は全成分の写像の等号とする。

恒等射は各sortの恒等写像、合成は $`(k\circ h)_s=k_s\circ h_s`$ である。
たとえば部分操作について、$`h`$ がdomain内へ送り、次に $`k`$ がdomain内へ送る。
その入力で

```math
k_t h_t p_A
  =k_t p_B h_{\boldsymbol s}
  =p_C k_{\boldsymbol s}h_{\boldsymbol s}
```

となる。他の条件も同じように合成される。単位律と結合律は成分写像で成り立つので、
構造の圏 $`\operatorname{Str}_\Sigma`$ を得る。

射は単射性・全射性を要求されない。
同型とは、逆向きにも式(2.1)を満たす逆射を持つ射である。
一般の関係を含む署名では、成分が全単射であることに加え、
逆写像も関係とdomainを保存することが同型に必要になる。

## 2.2 Lawを満たすモデルと観測

**定義2.2（意味圏）.**
$`\mathbb T`$ のモデルは、その署名の構造で全必須Lawを満たすものである。
$`\operatorname{Str}_\Sigma`$ のうち、これらの対象と、その間の全構造保存射からなる
充満部分圏を $`\mathcal A_{\mathbb T}`$ と書く。
Lawの成立は対象の条件であり、射の条件は式(2.1)である。

指定sort $`s`$ と集合 $`O`$ を固定した観測付きモデルは、
対 $`(A,o_A:X_s(A)\to O)`$ である。その射には

```math
o_B\circ h_s=o_A
\tag{2.2}
```

を加える。複数の観測では各成分に同じ条件を課す。
これらの条件も恒等と合成で保たれる。
観測を署名に含めるには、値sortを $`O`$ に固定して観測操作を宣言し、
射の $`O`$ 成分を恒等にすればよい。

状態 $`a=a'`$ という等号、射 $`h:A\to B`$ が存在すること、
観測値 $`o_A(a)=o_A(a')`$ という等号は、異なる条件である。
たとえば定数観測を持つ二点集合では観測値は常に一致するが、二状態は区別される。

**命題2.3（追加Lawによる忘却）.**
同じ署名について、$`\mathbb T'`$ が $`\mathbb T`$ の必須LawにLawを追加して得られるとする。
このとき、構造をそのまま読む忘却関手

```math
\mathcal A_{\mathbb T'}\longrightarrow\mathcal A_{\mathbb T}
\tag{2.3}
```

は充満忠実である。

**証明.**
$`\mathbb T'`$ のモデルは $`\mathbb T`$ の全必須Lawを満たす。
二つの対象の間の射は、どちらも同じ署名について式(2.1)を満たす成分写像なので、
Hom集合は同じである。恒等と合成も同じである。□

たとえば一つの単項操作 $`f`$ にLawを課さない理論から、
$`f(f(x))=f(x)`$ を追加した理論への恒等翻訳を考える。
忘却は冪等操作を持つモデルから任意の操作を持つモデルへ向く。
二点を交換する操作は後者のモデルだが、$`f^2=\operatorname{id}\ne f`$ なので前者のモデルではない。

## 2.3 構造保存射と理論の解釈

**定理2.4（理論解釈による充足保存と引戻し）.**
[定義1.9](chapter_1_atoms_laws_theories.md#14-表示代入理論の射)の理論解釈
$`u:\mathbb T\to\mathbb T'`$ から、関手

```math
u^*:\mathcal A_{\mathbb T'}\longrightarrow\mathcal A_{\mathbb T}
\tag{2.4}
```

が構成される。任意の $`\mathbb T'`$ モデル $`B`$ に対し、その担体は
$`X_s(u^*B)=X_{u(s)}(B)`$ である。
任意のterm $`t`$、正の式 $`\varphi`$ と型の合う割当て $`\gamma`$ について、
termの翻訳前後の定義可能性・値が一致し、

```math
u^*B\models\varphi(\gamma)
\quad\Longleftrightarrow\quad
B\models u\varphi(\gamma)
\tag{2.5}
```

となる。恒等と合成について
$`\operatorname{id}^*=\operatorname{Id}`$、
$`(v\circ u)^*=u^*\circ v^*`$ が成り立つ。

**構成と証明.**
$`u^*B`$ の全域操作 $`f`$ を $`\tau_f`$ の評価で定める。
その全域性の導出と[命題A.1](../appendix_a_positive_logic.md#a2-健全性)により、
全入力で一意の値がある。
関係 $`r`$ は $`\{\boldsymbol b\mid B\models\varphi_r(\boldsymbol b)\}`$ とする。
部分操作 $`p`$ のdomainを
$`\{\boldsymbol b\mid B\models\delta_p(\boldsymbol b)\}`$ とし、
そこで $`\tau_p`$ を評価する。
$`\delta_p\dashv\vdash\operatorname{Def}_{\tau_p}`$ の導出の健全性により、
これはちょうど評価可能な入力全体である。

変数の場合から始め、termの構文木について帰納する。
各原始操作の解釈は、その翻訳termの評価として定めた。
引数に帰納法を適用し、[定理1.8](chapter_1_atoms_laws_theories.md#14-表示代入理論の射)の
代入と評価の一致を使うと、複合termの定義可能性と値も一致する。
原子式にこの結果と関係・domainの定義を適用し、
連言・選言・存在量化では同じ成分・同じwitnessを用いると式(2.5)を得る。

$`\mathbb T`$ の必須Law $`\iota_\ell\vdash\chi_\ell`$ を取る。
解釈が持つ翻訳Lawの導出は $`B`$ で真である。
式(2.5)の両向きを入力と結論に適用すれば、$`u^*B`$ はこのLawを満たす。
これで全必須Lawの成立を得る。

次に $`k:B\to C`$ に対し、$`(u^*k)_s=k_{u(s)}`$ と定める。
全域操作の可換性は、$`\tau_f`$ に対する定理1.8から従う。
部分操作のdomainは正の式 $`\delta_p`$ なので同定理により保存され、
その入力で $`\tau_p`$ の値も運ばれる。翻訳関係 $`\varphi_r`$ も正の式の保存で運ばれる。
よって $`u^*k`$ は構造保存射である。
ここでは、翻訳Lawの導出による**対象の充足**と、
正の式の保存による**射の保存条件**をそれぞれ証明した。

恒等射と合成は同じ成分写像から定めたので保たれる。
理論解釈の恒等と合成についても、担体は同じsortの担体となる。
操作は代入評価の一致から同じ写像、関係は式(2.5)から同じ部分集合となる。
射の成分も同じである。外延的な集合・写像で構造を記述した本章では、
これらの比較は上記の等号で与えられる。
別の同型な担体表示を選ぶ場合には、同じ比較を成分が恒等の自然同型として読む。
三つの翻訳の比較は、同じ式への代入と同じ成分写像になるため整合する。

最後に、同値な翻訳は、健全性により同じ値graphと関係を定める。
したがって $`u^*`$ は解釈の代表によらず定まる。□

**系（逆解釈からの同値）.**
$`u:\mathbb T\to\mathbb T'`$ と $`v:\mathbb T'\to\mathbb T`$ が
Lawの下で互いに逆の解釈なら、$`u^*,v^*`$ は互いに逆の関手である。
より一般に、合成解釈と恒等解釈の間にsortごとの全域termがあり、
逆termとの合成が恒等であること、および各操作・関係・domainの保存を
Lawから導出できるとする。このとき、それらのtermの評価がモデルごとの同型を与える。
定理1.8によりその評価は全構造保存射と可換するので自然同型となり、
$`\mathcal A_{\mathbb T}\simeq\mathcal A_{\mathbb T'}`$ を得る。

**構成2.5（理論変更を伴う全体圏）.**
$`\mathcal A_{\mathrm{tot}}`$ の対象を $`(\mathbb T,A)`$、
射を

```math
(u,h):(\mathbb T,A)\longrightarrow(\mathbb T',B),
\qquad
u:\mathbb T\to\mathbb T',\quad h:A\to u^*B
\tag{2.6}
```

とする。恒等は $`(\operatorname{id},\operatorname{id})`$、合成は

```math
(v,k)\circ(u,h)=(v\circ u,\ u^*k\circ h)
\tag{2.7}
```

である。右辺の終域は $`u^*v^*C=(v\circ u)^*C`$ である。
三つの射の状態成分は、どちらの括弧付けでも
$`u^*v^*\ell\circ u^*k\circ h`$ となる。
単位律も定理2.4と成分写像の単位律から従う。
これで圏構造を得る。

射影 $`\pi:\mathcal A_{\mathrm{tot}}\to\mathbf{Th}`$ は $`(u,h)`$ を $`u`$ へ送る。
$`\mathbb T`$ 上のfiber、すなわち対象を $`(\mathbb T,A)`$、
射の理論成分を $`\operatorname{id}_{\mathbb T}`$ に固定した圏は $`\mathcal A_{\mathbb T}`$ である。
同型だけを残した最大部分groupoidを $`\mathcal A_{\mathbb T}^{\simeq}`$ と書く。
対象のモジュライを扱う際にはこのgroupoidを用い、変更と合成には元の意味圏を用いる。

## 2.4 全操作語への保存の延長

有限操作語 $`w=e_m\cdots e_1:s\rightsquigarrow t`$ は、
型の合う名前付き単項操作の列とする。操作には部分操作も許す。
空語は恒等写像である。語 $`we`$ の定義域は、最初の操作が定義され、
その結果で残りの語が定義される状態からなる。
多引数操作の有限合成には、第1章のtermをそのまま用いる。

**定理2.6（全操作語の保存）.**
同じ署名の構造保存射 $`h:A\to B`$ と、各終点sortで式(2.2)を満たす観測を与える。
任意の有限操作語 $`w:s\rightsquigarrow t`$ について

```math
\begin{aligned}
h_s(\operatorname{Dom}_A(w))&\subseteq\operatorname{Dom}_B(w),\\
h_t(w_A(a))&=w_B(h_s(a)),\\
o_{B,t}(w_B(h_s(a)))&=o_{A,t}(w_A(a))
\quad(a\in\operatorname{Dom}_A(w))
\end{aligned}
\tag{2.8}
```

が成り立つ。さらに $`h`$ が各原始部分操作のdomainを反射する、すなわち

```math
\boldsymbol a\in D_p^A
\quad\Longleftrightarrow\quad
h_{\boldsymbol s}(\boldsymbol a)\in D_p^B
\tag{2.9}
```

なら、$`\operatorname{Dom}_A(w)=h_s^{-1}(\operatorname{Dom}_B(w))`$ である。

理論解釈 $`u:\mathbb T\to\mathbb T'`$ と射 $`h:A\to u^*B`$ については、
右辺の操作語を翻訳term $`u(w)`$ として同じ結論を得る。
domain反射を仮定する場合は、$`A`$ と $`u^*B`$ の間で式(2.9)を課す。

**証明.**
空語ではdomainは全状態、値の式は $`h_s(a)=h_s(a)`$、
観測の式は式(2.2)である。
$`w`$ の後に原始操作 $`e`$ を行う場合を考える。
$`a`$ が合成のdomainに入れば、帰納法により $`w_B(h_s(a))`$ が定義され、
$`h(w_A(a))`$ に等しい。$`e`$ が部分操作なら式(2.1)がこの値を $`D_e^B`$ へ送り、
全域操作ならそのまま適用できる。操作の可換性により合成の値も一致する。
最後の観測を式(2.2)で読み取ると第三式を得る。

domain反射の下で、逆に $`e_B(w_B(h_s(a)))`$ が定義されるとする。
帰納法の逆向きで $`w_A(a)`$ が定義される。
値の一致と原始domainの反射から、その値が $`D_e^A`$ に入る。
これで合成のdomainも反射される。
翻訳版では、まず $`h:A\to u^*B`$ に今の証明を適用し、
定理2.4のterm評価の一致で $`w_{u^*B}`$ を $`u(w)_B`$ へ置き換える。□

**例2.7（非可逆な射とdomainの拡大）.**
二点集合 $`A=\{0,1\}`$ と一点集合 $`B=\{*\}`$ に恒等操作と定数観測を与える。
一意の写像 $`A\to B`$ は全操作語の観測を保つ非単射の射である。
逆に一点集合から二点集合への包含も、同じ操作と観測について非全射の射になる。

部分操作では、同じ一点担体を持つ $`A,B`$ に対し、
$`D_p^A=\varnothing`$、$`D_p^B=\{*\}`$、$`p_B(*)=*`$ とする。
恒等担体写像は構造保存射だが、$`B`$ で定義される $`p`$ は $`A`$ では定義されない。
式(2.8)のdomain包含は成り立ち、逆包含のための式(2.9)は成り立たない。

## 2.5 独立な意味論からの構成と回復

### lens

**定義2.8（全域lensの圏）.**
全域lens $`L`$ を、集合 $`S_L,V_L`$ と写像
$`g_L:S_L\to V_L`$、$`p_L:S_L\times V_L\to S_L`$ で、
式(1.7)の三法則を満たすものとする。
射 $`L\to M`$ は、二つの写像 $`h:S_L\to S_M`$、$`k:V_L\to V_M`$ で

```math
g_Mh=kg_L,\qquad
h(p_L(a,v))=p_M(h(a),k(v))
\tag{2.10}
```

を満たすものとする。恒等と合成は二成分で与える。
二つの可換式は合成で保たれるので、圏 $`\mathbf{Lens}`$ を得る。

**定理2.9（lensの対象と全Homの回復）.**
第1章の二sort、get・put、三法則の理論を $`\mathbb T_{\mathrm{lens}}`$ とする。
各lensをその担体と二操作で解釈する対応は圏の同型

```math
\mathbf{Lens}\ \cong\ \mathcal A_{\mathbb T_{\mathrm{lens}}}
\tag{2.11}
```

を与える。view $`V`$ を固定し、view成分を恒等とした場合にも同じ対応が成り立つ。

**証明.**
lensから、state sortに $`S_L`$、view sortに $`V_L`$、
get・putに $`g_L,p_L`$ を割り当てる。
三つのLawの全入力での評価は、順に三つのlens法則そのものである。
逆にモデルから二担体と二操作を取り出すと、そのLawの成立から全域lensを得る。
この二構成は各担体・写像で互いに逆である。

射 $`(h,k)`$ に対するget・putの構造保存条件は式(2.10)である。
したがって全てのlens射が構造保存射を与え、
任意の構造保存射の二sort成分から唯一のlens射を回復する。
追加の成分はなく、全Homが対応する。
恒等と合成は両側で成分写像から定まるので一致する。□

**命題2.10（基準viewによる積表示と射の標準形）.**
lens $`L`$ に基準view $`v_0\in V_L`$ を選び、
$`C_L=g_L^{-1}(v_0)`$ とする。このとき

```math
\begin{aligned}
\theta_L:S_L&\longrightarrow V_L\times C_L,
&a&\longmapsto(g_L(a),p_L(a,v_0)),\\
\theta_L^{-1}:V_L\times C_L&\longrightarrow S_L,
&(v,c)&\longmapsto p_L(c,v)
\end{aligned}
\tag{2.12}
```

は互いに逆で、getは第一射影、putは $`(v,c)\mapsto(w,c)`$ となる。
別のlens $`M`$ に独立に $`w_0\in V_M`$ を選ぶと、全ての射の集合には全単射

```math
\operatorname{Hom}_{\mathbf{Lens}}(L,M)
\ \cong\
\operatorname{Map}(V_L,V_M)\times\operatorname{Map}(C_L,C_M)
\tag{2.13}
```

があり、対応する状態写像の標準形は
$`\theta_Mh\theta_L^{-1}(v,c)=(k(v),r(c))`$ である。

**証明.**
$`g_L(p_L(a,v_0))=v_0`$ なので $`\theta_L`$ は定義される。
三法則から

```math
\begin{aligned}
p_L(p_L(a,v_0),g_L(a))&=p_L(a,g_L(a))=a,\\
g_L(p_L(c,v))&=v,\\
p_L(p_L(c,v),v_0)&=p_L(c,v_0)=c
\quad(c\in C_L)
\end{aligned}
```

となり、二写像が逆であることが分かる。
同じ計算で $`\theta_L(p_L(a,w))=(w,\theta_L(a)_2)`$ となる。

射 $`(h,k)`$ から $`r(c)=p_M(h(c),w_0)`$ と定める。
get-put法則により $`r(c)\in C_M`$ である。
$`a=p_L(c,v)`$ に対し、getの可換性とputの可換性から

```math
\begin{aligned}
g_M(h(a))&=k(v),\\
p_M(h(a),w_0)&=p_M(p_M(h(c),k(v)),w_0)\\
&=p_M(h(c),w_0)=r(c).
\end{aligned}
```

を得る。これが標準形である。
逆に任意の $`(k,r)`$ から、積表示の間の写像 $`(v,c)\mapsto(k(v),r(c))`$ を戻すと、
第一射影と第一成分の更新の両方を保つためlens射となる。
二構成は互いに逆である。
恒等は二つの恒等写像、合成は $`(k',r')\circ(k,r)=(k'k,r'r)`$ に対応する。
基準viewは各対象で独立に選べ、$`k(v_0)=w_0`$ は必要ない。□

この命題は基準viewを選んだlensについて述べている。
空viewの場合はgetの存在からstateも空となり、定理2.9でそのまま扱える。

読取りだけを保つ写像の例として、$`V=C=\{0,1\}`$ 上の積lensを取り、
$`h(v,c)=(v,v)`$、$`k=\operatorname{id}`$ とする。
$`gh=g`$ だが、
$`h(p((0,0),1))=(1,1)`$、
$`p(h(0,0),1)=(1,0)`$ である。よってputの保存は読取りの保存からは従わない。

### protocol

**定義2.11（実行圏上のprotocol）.**
小さい圏 $`\mathcal E`$ と観測関手 $`O:\mathcal E\to\mathbf{Set}`$ を固定する。
protocolは関手 $`X:\mathcal E\to\mathbf{Set}`$ と自然変換 $`o:X\Rightarrow O`$ の対である。
対象 $`s`$ の集合 $`X(s)`$ はその段階の状態、射 $`e:s\to t`$ の写像 $`X(e)`$ は実行を表す。
射 $`(X,o)\to(Y,o')`$ は自然変換 $`h:X\Rightarrow Y`$ で $`o'h=o`$ を満たすものとする。
これを $`\mathbf{Prot}(\mathcal E,O)`$ と書く。

署名には、各 $`s`$ のstate sort、各 $`e:s\to t`$ の操作 $`T_e`$、
固定された観測sort $`O(s)`$ と操作 $`O(e)`$、観測操作 $`o_s`$ を置く。
観測sortと $`O(e)`$ の解釈を固定し、射では観測sortの成分を恒等にする。
state操作と観測に次のLawを課す。

```math
T_{\operatorname{id}_s}(a)=a,\qquad
T_{f\circ e}(a)=T_f(T_e(a)),\qquad
o_t(T_e(a))=O(e)(o_s(a)).
\tag{2.14}
```

この固定データの下のモデル圏を $`\mathcal A_{\mathrm{prot}(\mathcal E,O)}`$ と書く。

**定理2.12（protocolの対象・全Hom・生成経路の回復）.**
上の宣言への解釈と読戻しは圏の同型

```math
\mathbf{Prot}(\mathcal E,O)
\ \cong\
\mathcal A_{\mathrm{prot}(\mathcal E,O)}
\tag{2.15}
```

を与える。
$`\mathcal E`$ が有向グラフの経路圏を指定された経路等式で割った圏の場合には、
生成辺の操作、経路等式のLaw、生成辺での観測の可換性だけから同じ圏を回復できる。

**証明.**
protocolから担体 $`X(s)`$、操作 $`X(e)`$、観測 $`o_s`$ を割り当てる。
式(2.14)の初めの二式は関手の単位律・合成律、
第三式は $`o`$ の自然性である。逆にモデルから担体と $`T_e`$ を取ると、
これらのLawにより関手と自然な観測を得る。

構造保存射のstate成分 $`h_s`$ は
$`h_tT_e=T'_eh_s`$ と $`o'_sh_s=o_s`$ を満たす。
これはちょうど観測上の自然変換である。
固定観測sortの成分は恒等なので追加の選択はない。
したがって対象と全Homの読戻しは互いに逆であり、恒等と合成も一致する。

生成辺による表示では、各経路を辺の操作の合成、空経路を恒等で評価する。
指定経路等式はLawで等しい写像となる。
等しい写像の前後に同じ写像を合成しても等しいので、
それらが生成する経路の合同関係について評価は一定である。
よって商圏 $`\mathcal E`$ 上の関手が一意に定まる。
観測の自然性と射の可換性は、空経路から始めて辺を一つずつ付ける帰納法で全経路へ延長される。
全経路の作用を生成辺へ制限すれば出発時のデータに戻るため、この表示でも相互回復を得る。□

環と加群についても、例1.6の演算を読み戻せば環と加群が得られる。
全構造保存射は環準同型と、それに関して半線形な加群写像であり、
環を固定した場合には $`R`$ 線形写像である。
量や観測を付け加えた場合は、対応する可換式がこのHom集合への追加条件になる。

以上で、次章へ制限する対象と射が揃った。
後続で実現の族を幾何的に表示するときにも、
この独立な対象・全Homとの比較を通じて意味を回復する。

[前章](chapter_1_atoms_laws_theories.md) · [第I部](../README.md#第i部-lawと意味の基礎) ·
[次章：文脈と局所モデル](chapter_3_contexts_and_local_models.md)
