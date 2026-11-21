# 第1章 Atom・Law・理論の指定

何を区別し、どの操作と量を読み、何を満たすべき条件とするのか。
この章では、その指定を署名とLawで与える。共通の語彙、各対象が持つ構造、
その構造を評価して得る事実を分け、モデルと射を定義するための言語を構成する。

## 1.1 共通のAtom語彙と個々のAtom

操作名を宣言すること、その名に写像を割り当てること、その写像を特定の入力で評価することは、
それぞれ異なるデータである。たとえば、読取りを表す名前 $`get`$ には入出力の型があり、
モデルごとに実際の写像 $`get_A`$ があり、状態 $`a`$ ごとに値 $`get_A(a)`$ がある。

**定義1.1（型付きAtom語彙）.**
Atom語彙は、事実の種類と、種類ごとの名前・参照先・値の型を定めるデータである。
本章では、次の種類を区別する語彙を用いる。

| 種類 | 宣言に保持するデータ | 構造を解釈した後の事実 |
| --- | --- | --- |
| sort | 型名 $`s`$ | $`a\in X_s(A)`$ |
| 操作 | 名前 $`f`$、入力型列、出力型 | $`f_A(\boldsymbol a)=b`$ |
| 関係 | 名前 $`r`$、引数の型列 | $`\boldsymbol a\in r_A`$ |
| 部分操作 | 名前 $`p`$、入力型列、出力型、domainとgraphの名前 | $`\boldsymbol a\in D_p^A`$、$`p_A(\boldsymbol a)=b`$ |
| 量 | 名前 $`q`$、入力型列、値の型 | $`q_A(\boldsymbol a)=c`$ |
| Law | 名前、役割、入力の式、充足条件の式 | 指定された入力での式の評価 |
| 式の出現 | 式を持つ宣言の名前、有限構文木内の位置 | その部分式の評価 |

各種類はタグ付きで区別し、名前も型付きで比較する。
[定義1.7](#14-表示代入理論の射)で定める原始表示 $`\mathcal P`$ の宣言と式の出現からなる集合を
$`\mathrm{At}_{\mathrm{dec}}(\mathcal P)`$ と書く。
構造 $`A`$ を与えたときの状態・操作graph・関係・domain・量の事実の直和を
$`\mathrm{At}_{\mathrm{val}}(A)`$ と書く。
たとえば操作事実の成分は

```math
\{(f,\boldsymbol a,b)\mid b=f_A(\boldsymbol a)\}
```

である。入力 $`\boldsymbol a`$ もタグの一部として保持するので、
異なる二つの入力で出力が等しくても、その事実は区別される。
部分操作では $`\boldsymbol a\in D_p^A`$ を満たす入力だけがgraphに現れる。

宣言から構造を得るには、担体・写像・関係の解釈を与える。
構造から値の事実を得るには、実際に評価する。
観測は、この構造や事実から何を読むかを選ぶ写像として[1.5節](#15-観測とreading)で定める。

## 1.2 型・操作・関係・部分操作・量の宣言

**定義1.2（署名とその解釈データ）.**
署名 $`\Sigma`$ は、小さいsort集合 $`S`$ と、次の小さい名前の族からなる。

1. 全域操作 $`f:(s_1,\ldots,s_n)\to t`$。
2. 関係 $`r\subseteq(s_1,\ldots,s_n)`$。
3. 部分操作 $`p:(s_1,\ldots,s_n)\rightharpoonup t`$。
4. 量 $`q:(s_1,\ldots,s_n)\to v`$。$`v`$ は値を表すsortであり、量は印を付けた全域操作である。

arity $`n`$ は有限で、$`n=0`$ も許す。部分的な量は部分操作として宣言する。
値sortに環構造を要求する場合には、その演算とLawも宣言する。

構造 $`A`$ の解釈データは、各sortの小さい集合 $`X_s(A)`$、全域写像 $`f_A,q_A`$、
部分集合 $`r_A\subseteq\prod_iX_{s_i}(A)`$、および

```math
D_p^A\subseteq\prod_iX_{s_i}(A),\qquad
p_A:D_p^A\longrightarrow X_t(A)
```

である。空積は一元集合とする。全域の定数を宣言すると、その値sortの担体には元が必要になる。

部分操作に付随する原子関係を $`D_p(\boldsymbol x)`$ と $`G_p(\boldsymbol x,y)`$ とする。
解釈はそれぞれ定義域とgraphであり、
$`G_p^A=\{(\boldsymbol a,p_A(\boldsymbol a))\mid\boldsymbol a\in D_p^A\}`$ である。
全域操作と量にもgraph記号 $`G_f,G_q`$ を付ける。
これらは別々に選ぶ関係ではなく、選んだ写像から定まる。

graphによる記述では、次の式が全ての構造で成り立つ。
$`\vdash_{\boldsymbol x,y,z}`$ などの添字は、表示した全自由変数の型付き文脈を表す。

**式(1.1)**

```math
\begin{aligned}
G_f(\boldsymbol x,y)\wedge G_f(\boldsymbol x,z)
  &\ \vdash_{\boldsymbol x,y,z}\ y=z,
&
\top&\ \vdash_{\boldsymbol x}\ \exists y\,G_f(\boldsymbol x,y),\\
G_p(\boldsymbol x,y)\wedge G_p(\boldsymbol x,z)
  &\ \vdash_{\boldsymbol x,y,z}\ y=z,
&
G_p(\boldsymbol x,y)&\ \vdash_{\boldsymbol x,y}\ D_p(\boldsymbol x),\\
D_p(\boldsymbol x)&\ \vdash_{\boldsymbol x}\ \exists y\,G_p(\boldsymbol x,y).
\end{aligned}
```

量にも全域操作の二式を用いる。逆に、これらを満たすgraphから、一意の値を取ることで
全域写像・部分写像が回復する。式(1.1)を**graphの構造公理**と呼ぶ。
個別の理論のLawを課す前に、写像をgraphとして書く際に使う公理である。

domainを別sort $`d`$ の包含で表したい場合には、各 $`j_i:d\to s_i`$ を全域操作として宣言する。
この表示と部分操作のdomainとの整合は、次のLawで指定できる。

**式(1.2)**

```math
\begin{aligned}
\bigwedge_i j_i(z)=j_i(z')&\ \vdash_{z,z':d}\ z=z',\\
D_p(\boldsymbol x)&\ \dashv\vdash_{\boldsymbol x}\
  \exists z:d\,\bigwedge_i j_i(z)=x_i.
\end{aligned}
```

ここで $`\dashv\vdash`$ は二方向の含意を表す。第一式は $`(j_i)_i`$ の単射性、
第二式はその像がdomainに一致することを表す。
具体的な部分集合は構造側で選ばれ、宣言間で必要な整合はLawとして課される。

## 1.3 Lawの入力、式、評価、充足

**定義1.3（termと部分評価）.**
有限変数文脈を $`\Gamma=(x_1:s_1,\ldots,x_n:s_n)`$ と書き、
$`X_\Gamma(A)=\prod_iX_{s_i}(A)`$ とする。
型付きtermは、変数、全域操作・部分操作・量の有限回の適用、
および有限の束縛式 $`\mathrm{let}\,z=t\mathrm{\,in\,}s`$ で生成する。
termは構文木であり、その値は構造と入力を与えた後に定まる。

評価 $`\mathrm{ev}_A(t,\gamma)`$ は部分的に定める。
変数は対応成分を返す。操作への適用では全ての引数termを先に評価し、
部分操作なら、その値の組が $`D_p^A`$ に入るときにだけ $`p_A`$ を適用する。
term $`t`$ が定義される入力の集合を $`\mathrm{Dom}_A(t)`$ と書く。
一つの未定義の引数を持つ操作termも未定義とする。
束縛式では $`t`$ を先に評価し、その値を $`z`$ へ割り当てて $`s`$ を評価する。
$`s`$ が $`z`$ を使わない場合も $`t`$ の評価を行う。

この評価を有限式で表すため、値のgraph $`E_t(\boldsymbol x,y)`$ を帰納的に作る。
変数では $`E_{x_i}(\boldsymbol x,y)`$ を $`x_i=y`$ とし、
$`t=e(t_1,\ldots,t_m)`$ では

**式(1.3)**

```math
E_t(\boldsymbol x,y):=
\exists z_1\cdots z_m
\left(\bigwedge_{j=1}^m E_{t_j}(\boldsymbol x,z_j)
 \wedge G_e(z_1,\ldots,z_m,y)\right).
```

とする。$`e`$ には部分操作も含める。
束縛式の値graphは
$`E_{\mathrm{let}\,z=t\mathrm{\,in\,}s}(\boldsymbol x,y) :=\exists z\,(E_t(\boldsymbol x,z)\wedge E_s(\boldsymbol x,z,y))`$ である。
$`z`$ は他の自由変数と衝突しないように選ぶ。
$`\mathrm{Def}_t(\boldsymbol x):=\exists y\,E_t(\boldsymbol x,y)`$ と置く。
構文木の帰納法とgraphの一価性から、
$`A\models E_t(\gamma,b)`$ であることは
「$`t`$ が $`\gamma`$ で定義され、その値が $`b`$」と同値になる。
したがって $`E_t`$ は常に一価であり、その存在量化が $`\mathrm{Dom}_A(t)`$ を表す。

**定義1.4（正の式）.**
基本の原子式は、同じsortの変数間の等式、宣言された関係、
および操作のgraph・domain関係を変数に適用した式である。
これらから $`\top,\bot`$、有限連言、有限選言、存在量化で作る式を正の式と呼ぶ。
空連言は $`\top`$、空選言は $`\bot`$ とする。
充足は、等式と部分集合への所属、論理演算、量化されるsortの担体内のwitnessによって定める。

termを引数に持つ原子式は、式(1.3)を用いた略記である。たとえば

**式(1.4)**

```math
\begin{aligned}
r(t_1,\ldots,t_m)
&:=\exists z_1\cdots z_m
  \left(\bigwedge_j E_{t_j}(\boldsymbol x,z_j)\wedge r(\boldsymbol z)\right),\\
t=t'&:=\exists y\,(E_t(\boldsymbol x,y)\wedge E_{t'}(\boldsymbol x,y)).
\end{aligned}
```

domain式 $`D_p(t_1,\ldots,t_m)`$ とgraph式 $`G_e(t_1,\ldots,t_m,t')`$ も、
関係の場合と同じく全引数の値graphを連言し、その値を表す新しい変数を存在量化して読む。
したがって、部分termについて $`t=t`$ はその定義可能性を表す。
等式論理の反射律を無条件に使う対象は変数の等式であり、
部分termへの代入には定義可能性を伴わせる。

**定義1.5（Lawと役割）.**
Law $`\ell`$ は、有限変数文脈 $`\Gamma_\ell`$、
入力を指定する正の式 $`\iota_\ell`$、充足条件を表す正の式 $`\chi_\ell`$ を持つ。
構造 $`A`$ での入力集合と充足を

**式(1.5)**

```math
\begin{aligned}
I_\ell^A&=\{\gamma\in X_{\Gamma_\ell}(A)\mid A\models\iota_\ell(\gamma)\},\\
A\models\ell
&\quad\Longleftrightarrow\quad
  \forall\gamma\in I_\ell^A,\ A\models\chi_\ell(\gamma)
\end{aligned}
```

で定める。Lawはsequent $`\iota_\ell\vdash_{\Gamma_\ell}\chi_\ell`$ とも書く。
型・Law名・入力の式を保持するので、同じ結論でも異なる入力範囲を指定できる。
全域での等式Lawでは $`\iota_\ell=\top`$ とする。
部分操作の等式では、必要な定義可能性を入力または結論のどちらに要求するかも指定する。

理論 $`\mathbb T`$ は署名と必須Lawの小さい族からなる。
さらに、同じ言語で調べるLawに次の役割を付けられる。

- **必須Law**：モデルの条件として課す。
- **追加Law**：そのLawも満たすモデルの族を調べるための条件。
- **導出Law**：必須Lawとgraphの構造公理からの導出を伴うLaw。

導出に使う規則と健全性は[付録A](../appendix_a_positive_logic.md)に与える。
役割を指定することと、そのLawが成り立つ証明を持つことを区別する。

値sortが可換環 $`R_A`$ である等式Law $`\ell=(\iota_\ell\vdash_{\Gamma_\ell}t=t')`$ に対し、
$`J_\ell^A:=I_\ell^A\cap\mathrm{Dom}_A(t)\cap\mathrm{Dom}_A(t')`$ を定める。
残差 $`\rho_{\ell,A}:J_\ell^A\to R_A`$ は

**式(1.6)**

```math
\rho_{\ell,A}(\gamma)
  =\mathrm{ev}_A(t,\gamma)-\mathrm{ev}_A(t',\gamma)
```

とする。$`J_\ell^A`$ 上で等式の充足は残差の零性と同値である。
Law全体の成立 $`A\models\ell`$ は、$`J_\ell^A=I_\ell^A`$ であり、
全 $`\gamma\in J_\ell^A`$ で $`\rho_{\ell,A}(\gamma)=0`$ となることと同値である。
環演算と有限termから多項式を得る構成は、[第5章](../part_2/chapter_5_quantities_and_law_geometry.md)に接続する。

**例1.6（同じ言語で書かれるLaw）.**

**lens.** sort $`S,V`$ と全域操作
$`g:S\to V`$、$`p:S\times V\to S`$ を宣言し、全入力で

**式(1.7)**

```math
p(a,g(a))=a,\qquad
g(p(a,v))=v,\qquad
p(p(a,v),w)=p(a,w)
```

を課す。各式の変数文脈は順に $`(a:S)`$、$`(a:S,v:V)`$、$`(a:S,v:V,w:V)`$ である。
$`S=V\times C`$、$`g(v,c)=v`$、$`p((v,c),w)=(w,c)`$ は三式を満たす。
実際、三式の両辺は順に $`(v,c)`$、$`w`$、$`(w,c)`$ になる。

**経路.** 有向グラフの頂点をsort、辺を単項全域操作とする。
同じ始点・終点を持つ二経路の操作term $`t_\alpha,t_\beta`$ に対して、
$`\top\vdash_{x:s}t_\alpha(x)=t_\beta(x)`$ を課す。
たとえば $`f:s\to t`$、$`g:t\to s`$ と $`g(f(x))=x`$ は、往復操作が状態を戻す条件である。

**環と加群.** sort $`R`$ に $`0,1,+,-,\cdot`$ を宣言し、可換環の等式を課す。
さらにsort $`M`$、加法・零・逆元と作用 $`R\times M\to M`$ を加え、
加法群の等式、作用の結合・単位・両変数の分配を課すと、環とその加群を得る。
この場合も各Lawは有限の入力と式を持つ。係数を固定する場合には、
$`R`$ の担体と環構造を固定し、射の $`R`$ 成分を恒等とする。
この固定データを持つモデル圏は[定義2.2](chapter_2_models_and_morphisms.md#22-lawを満たすモデルと観測)で定める。

## 1.4 表示・代入・理論の射

**定義1.7（原始表示と代入）.**
原始表示 $`\mathcal P`$ は、署名の名前付き宣言、Lawの名前と役割、
各Lawの有限式、導出Lawについての導出を列挙したデータである。
その必須Lawで指定される理論を $`\mathbb T_{\mathcal P}`$ と書く。
表示には式の書き方と名前が残り、理論に関する等しさはLawからの導出で判断する。

変数文脈 $`\Gamma=(x_i:s_i)_{i=1}^n`$ への代入 $`\theta`$ は、
別の変数文脈 $`\Delta`$ 上の同じsortのterm $`\theta_i`$ の族である。
構文的代入 $`t[\theta]`$ は自由な変数出現を置き換える。
正の式 $`\varphi[\theta]`$ は原子式の各引数へ代入し、式(1.4)の規則で展開した後、
論理構文子に沿って定める。$`\exists`$ と $`\mathrm{let}`$ の束縛変数は、
代入termの自由変数を捕獲しないよう先に改名する。
$`\mathrm{Def}_\theta:=\bigwedge_i\mathrm{Def}_{\theta_i}`$ と置くと、
その成立する入力は $`D_{\theta,A}:=\bigcap_i\mathrm{Dom}_A(\theta_i)`$ であり、この上で

**式(1.8)**

```math
\theta_A:D_{\theta,A}\longrightarrow X_\Gamma(A),\qquad
\delta\longmapsto
  \bigl(\mathrm{ev}_A(\theta_i,\delta)\bigr)_i
```

が定まる。Law $`\ell=(\iota_\ell\vdash_\Gamma\chi_\ell)`$ への代入は

```math
\ell[\theta]:=
\bigl(\mathrm{Def}_\theta\wedge\iota_\ell[\theta]
  \ \vdash_\Delta\ \chi_\ell[\theta]\bigr)
```

とする。式に出現しない変数への代入も、$`\mathrm{Def}_\theta`$ に含める。
入力条件 $`\eta`$ の下で使う場合には、
$`\eta\vdash_\Delta\mathrm{Def}_\theta`$ を証明する。
このとき $`\eta`$ を前提に加えたLawでは、定義可能性の連言を省略できる。

**定理1.8（代入・評価・構造射による保存）.**
任意の署名、構造 $`A,B`$、有限の型付きtermと正の式について、次が成り立つ。

**(1)** $`\delta\in D_{\theta,A}`$ なら、
$`t[\theta]`$ が $`\delta`$ で定義されることと、$`t`$ が $`\theta_A(\delta)`$ で定義されることは同値であり、
定義されるとき
$`\mathrm{ev}_A(t[\theta],\delta)=\mathrm{ev}_A(t,\theta_A(\delta))`$ である。
同じ条件で、正の式 $`\varphi`$ について
$`A\models\varphi[\theta](\delta)\Longleftrightarrow A\models\varphi(\theta_A(\delta))`$ が成り立つ。

**(2)** sortごとの写像 $`h_s:X_s(A)\to X_s(B)`$ が、全域操作・量と可換し、
関係を保存し、部分操作について

**式(1.9)**

```math
\begin{aligned}
h_{\boldsymbol s}(D_p^A)&\subseteq D_p^B,\\
h_t(p_A(\boldsymbol a))&=p_B(h_{\boldsymbol s}(\boldsymbol a))
\quad(\boldsymbol a\in D_p^A)
\end{aligned}
```

を満たすとする。ここで $`h_{\boldsymbol s}`$ は入力sortの写像の積である。
このとき $`\gamma\in\mathrm{Dom}_A(t)`$ なら
$`h_\Gamma\gamma\in\mathrm{Dom}_B(t)`$ であり、

**式(1.10)**

```math
h_s(\mathrm{ev}_A(t,\gamma))
  =\mathrm{ev}_B(t,h_\Gamma\gamma).
```

また、$`A\models\varphi(\gamma)`$ なら $`B\models\varphi(h_\Gamma\gamma)`$ である。
特に $`h_{\Gamma_\ell}(I_\ell^A)\subseteq I_\ell^B`$ となる。

**(3)** (2)の仮定の下で、値sortの写像 $`h_R:R_A\to R_B`$ が環準同型であるとする。
等式Law $`\ell`$ と $`\gamma\in J_\ell^A`$ に対して
$`h_{\Gamma_\ell}\gamma\in J_\ell^B`$ であり、

**式(1.11)**

```math
h_R(\rho_{\ell,A}(\gamma))=\rho_{\ell,B}(h_{\Gamma_\ell}\gamma)
```

が成り立つ。代入については

```math
J_{\ell[\theta]}^A
 =\{\delta\in D_{\theta,A}\mid\theta_A(\delta)\in J_\ell^A\}
```

であり、この集合上で
$`\rho_{\ell[\theta],A}(\delta)=\rho_{\ell,A}(\theta_A\delta)`$ となる。

**証明.**
1のtermに関する主張を構文木で帰納する。変数の場合は式(1.8)である。
$`e(t_1,\ldots,t_m)`$ では、帰納法により各引数の定義可能性と値が一致する。
全域操作はその同じ値の組に作用する。部分操作でも、domainを検査する組が同じなので
定義可能性が一致し、そのとき同じ写像 $`p_A`$ を適用する。これでtermの場合を得る。
束縛式でも、先に評価するtermに帰納法を適用し、
得られた同じ値を束縛変数へ割り当てて本体に帰納法を適用する。
正の式では原子式を式(1.4)に展開し、同じ引数の評価を用いる。
連言・選言では各成分に帰納法を適用する。
存在量化では捕獲を避けた束縛変数に同じwitnessを割り当てる。
代入termの値はその束縛変数に依存しないので、両向きが成り立つ。

2のtermも構文木で帰納する。変数の場合は成分写像である。
全域操作の場合は引数に帰納法を適用して、操作との可換性を使う。
部分操作の場合は、得られた引数の像が式(1.9)の第一条件でdomainに入り、
第二条件によって出力が一致する。
束縛式では、最初の値を対応するsortの写像で送り、
その値を追加した割当てについて本体の帰納法を適用する。
正の式については別に構文帰納法を行う。
原子等式は写像が等号を保存すること、原子関係は仮定、
graphとdomainは操作の可換性と式(1.9)による。
連言は各成立成分を、選言は成立している一つの枝を運ぶ。
$`\top`$ は成立し、$`\bot`$ からの含意は空虚に成り立つ。
$`\exists y:t\,\psi(\gamma,y)`$ のwitness $`b`$ があれば、
帰納法から $`\psi(h_\Gamma\gamma,h_t(b))`$ を得る。
入力集合への主張は $`\varphi=\iota_\ell`$ への適用である。

3では、(2)の入力の保存と二つのtermの定義可能性の保存から
$`h_{\Gamma_\ell}(J_\ell^A)\subseteq J_\ell^B`$ を得る。二つのtermへの式(1.10)と、
$`h_R(x-y)=h_R(x)-h_R(y)`$ を合わせる。
代入の場合は、Law代入の入力に $`\mathrm{Def}_\theta`$ が含まれるため、
1を入力の式と二つのtermへ適用して定義域の等号を得る。
その定義域上で二つの値の差を取れば残差の等号となる。□

**定義1.9（理論の解釈）.**
$`u:\mathbb T\to\mathbb T'`$ は、次の翻訳と導出からなる。

- sortの写像 $`s\mapsto u(s)`$。
- 全域操作・量 $`f`$ に、その翻訳された入力型・出力型のterm $`\tau_f`$。
  $`\mathbb T'`$ で $`\top\vdash\mathrm{Def}_{\tau_f}`$ を導出する。
- 関係 $`r`$ に、翻訳された引数型の正の式 $`\varphi_r`$。
- 部分操作 $`p`$ に、同じ翻訳型のterm $`\tau_p`$ と正のdomain式 $`\delta_p`$。
  $`\mathbb T'`$ で $`\delta_p\dashv\vdash\mathrm{Def}_{\tau_p}`$ を導出する。
- 各必須Law $`\iota_\ell\vdash\chi_\ell`$ に、
  $`\mathbb T'`$ の必須Lawと構造公理からの翻訳 $`u\iota_\ell\vdash u\chi_\ell`$ の導出。

graph記号 $`G_f,G_p`$ はそれぞれ $`E_{\tau_f},E_{\tau_p}`$ に、
domain記号 $`D_p`$ は $`\delta_p`$ に送る。
式の翻訳は、原子式をこの規則で置き換え、
連言・選言・存在量化に関して延長する。等号と変数は対応するsortの等号と変数に送る。
非変数termを含む式は式(1.3)–(1.4)で展開してから翻訳する。
term自体の翻訳では、操作適用 $`e(t_1,\ldots,t_m)`$ を
「翻訳された $`t_1,\ldots,t_m`$ の値を順に新しい変数 $`z_1,\ldots,z_m`$ へ束縛し、
$`\tau_e(\boldsymbol z)`$ を評価する」termへ送る。
この有限の束縛式により、$`\tau_e`$ が一部の変数を使わない場合も、
元の全引数の定義可能性を保持する。既存の束縛式は、その二つの部分termを翻訳する。

射の等号は、sort写像が同じで、各操作の値graphと各関係・domainの翻訳が
$`\mathbb T'`$ で相互に導出可能であることとする。導出木の選び方は射の等号に含めない。
値graphを比較するため、操作の定義可能性も等号に含まれる。
恒等翻訳はsortと原始記号を保ち、操作 $`e`$ を $`e(\boldsymbol x)`$、
関係 $`r`$ を $`r(\boldsymbol x)`$、domainを $`D_p(\boldsymbol x)`$ へ送る。
$`u:\mathbb T\to\mathbb T'`$ と $`v:\mathbb T'\to\mathbb T''`$ の合成候補では、
sort写像を合成し、$`u`$ の操作term・関係式・domain式に $`v`$ の翻訳を施す。
[付録Aの補題A.3・命題A.4](../appendix_a_positive_logic.md#a3-翻訳と導出)で、
値graphと式の相互導出から、合成が解釈となること、代表によらないこと、単位律と結合律を証明する。
この等号で割った解釈を射とする圏を、理論の圏 $`\mathbf{Th}`$ と呼ぶ。

**例1.10（domainと入力を運ぶ必要）.**
一つのsort $`S=\{0,1\}`$、定数 $`c=1`$、部分単項操作 $`p`$ を考える。
構造 $`A`$ では $`D_p^A=\{0,1\}`$、$`p_A(a)=a`$ とし、
$`B`$ では $`D_p^B=\{0\}`$、$`p_B(0)=0`$ とする。
同じ名前を対応させても、恒等状態写像は $`1`$ を $`B`$ のdomainへ送らない。
$`A`$ で成り立つ $`p(c)=c`$ は、$`B`$ では左辺が未定義なので成り立たない。

また、$`B`$ は $`D_p(x)\vdash_x p(x)=x`$ を満たすが、
$`\top\vdash_x p(x)=x`$ を満たさない。
後者を必須Lawとする理論から、前者を必須Lawとする理論への翻訳候補として、
sortと全原始記号を同じ名前へ送るものを取る。
翻訳先のモデル $`B`$ が翻訳Lawを満たさないので、健全性によりその導出は存在せず、
この候補は定義1.9の解釈にならない。
Lawの入力と、その入力上で必要な定義可能性が翻訳の一部になる理由がここにある。

本章の正の式は、非単射・非全射を含む構造保存射に沿う一方向の保存を持つ。
否定を含む言語を選ぶ場合には、許す射とその保存証明も選ぶ必要がある。
たとえば二点を一点へ送る写像は $`x\ne y`$ を保存しない。
全sortで全単射であり、全原子関係を保存・反射する射なら、
式の真偽は否定・連言・選言・存在量化・全称量化について帰納的に一致する。
否定は真偽の同値から、量化は全単射によるwitnessまたは任意の元の対応から従う。
このように、別の構文を使うときの保存則はその構文子ごとに証明する。

## 1.5 観測とreading

**定義1.11（観測とreadingの指定）.**
構造 $`A`$ の指定sort $`s`$ に対する観測は、値集合 $`O`$ と写像
$`o_A:X_s(A)\to O`$ である。複数のsortや入力の組を観測する場合には、
その積を始域とする写像を用いる。構造の族 $`\mathcal U`$ に対する観測は、
別に $`q:\mathcal U\to B`$ という写像で与える。
一つの状態を読むことと、実現の族を区別することでは始域が異なる。

readingは、どの署名・Law、観測、宣言文脈と被覆、値の構造を用いて読むかの選択である。
文脈と被覆は[第3章](chapter_3_contexts_and_local_models.md)で定義する。
係数を用いるreadingでは、その係数と係数的実現方式も保持する。

二つのreadingを比較するときは、理論解釈 $`u`$ と、
[定理2.4](chapter_2_models_and_morphisms.md#23-構造保存射と理論の解釈)で構成する引戻しモデル $`u^*B`$ を用いる。
状態写像 $`h:A\to u^*B`$、観測値の写像 $`\alpha:O\to O'`$ を指定し、
必要な観測の可換性

**式(1.12)**

```math
o_B\circ h_s=\alpha\circ o_A
```

を課す。文脈や係数も変えるときには、その写像と制限・評価との可換性を併せて与える。
観測値が等しい二状態を同一状態として扱うには、さらにその同一視が操作を運ぶことを調べる。

構造保存射 $`h`$ は、状態Atomとgraph Atomを成分写像で送り、
関係・domain Atomを定理1.8で送る。
この写像は、具体的なAtom事実と、宣言された言語による評価を結びつける。
次章では同じ保存条件からモデルの圏と理論解釈の関手を構成する。

[第I部](../README.md#第i部-lawと意味の基礎) · [共通記号](../notation.md) ·
[次章：意味の対象と射](chapter_2_models_and_morphisms.md)
