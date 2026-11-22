# 第16章 診断の族と障害の比較

診断は、指定したLawの値と支持から複体を作り、その類を読む。
実修復の障害は、実操作と局所状態の不一致から独立に作る。
両者を結ぶ写像を構成して初めて、診断類の零性が修復に何を意味するかを問える。
本章では比較の欠損、局所fiber、値の合流、指定障害の零性反映を同じ生成規則で扱う。
基礎環 $`k`$ と実現の係数環 $`R`$ に加え、診断係数 $`\Lambda`$ を別に指定する。

## 16.1 指定修復問題とLaw評価からの診断複体

**定義16.1（有限支持とLaw値複体）.**
有限Source $`S`$ と有限添字集合 $`L`$ を取る。
各 $`\ell\in L`$ について、原始操作・量・Lawの式から評価した写像
$`\lambda_\ell:S\to W_\ell`$ を指定する。
これは必須Lawの残差を読む場合も、指定したLaw入力に付随する操作値を読む場合も含む。
どの式の値かを各 $`\lambda_\ell`$ の指定に含める。
reading $`q:S\twoheadrightarrow T`$ がこの評価に十分であるとは
$`q(s)=q(s')\Longrightarrow\lambda_\ell(s)=\lambda_\ell(s')`$ が全 $`\ell`$ で成立することとする。
このとき一意に $`\bar\lambda_\ell:T\to W_\ell`$ が定まる。

有限セル系 $`K`$ は頂点 $`K_0`$、向き付き辺 $`K_1`$、三角形の面 $`K_2`$ を持つ。
辺の始点・終点を $`s,t`$、面の三辺を $`e_{01},e_{02},e_{12}`$ とし、
対応する三頂点が一致する条件を課す。loopや名前の異なる平行辺、同じ辺の異なる出現も許す。
自由chainの微分を

```math
\partial_1[e]=[t(e)]-[s(e)],\qquad
\partial_2[f]=[e_{01}(f)]-[e_{02}(f)]+[e_{12}(f)]
```

とする。三頂点の相殺から $`\partial_1\partial_2=0`$ である。
各頂点に支持 $`T_v\subseteq T`$ を指定し、辺と面の支持は端点・三辺の支持の交差で作る。
より一般に支持 $`T_\sigma`$ が各faceの支持に含まれる指定でも、以下の複体を作れる。
16.3節のセル比較では交差で生成する指定を用いる。

labelは、実際に生じた対 $`a=(\ell,w)`$、$`w\in\lambda_\ell(S)`$ とする。
同じ値でも $`\ell`$ が違えば異なるlabelである。
可視部分セル系を

```math
K_a=\{\sigma\in K\mid
\exists t\in T_\sigma,\ \bar\lambda_\ell(t)=w\},\qquad
D_q^n=\bigoplus_a\Lambda^{(K_a)_n},\quad n=0,1,2
```

と定め、他次数は0とする。ここで $`\Lambda^E`$ は有限集合 $`E`$ 上の関数加群である。
支持包含から $`K_a`$ はfaceで閉じ、微分は $`d=\partial^\vee`$、すなわち端点差と三辺の交代和になる。
同じlabelを与える支持の証人が複数あっても、そのセル座標は一つである。
これをLaw値診断複体と呼び、$`H^n(D_q)=\ker d^n/\mathop{\mathrm{im}}d^{n-1}`$ とする。

宣言文脈との接続は、[第3章](../part_1/chapter_3_contexts_and_local_models.md)の有限被覆
$`(U_i)`$ と交差に名前を付けて作れる。頂点は被覆元、辺は選んだ二重交差の出現、面は三重交差の出現である。
同じ交差でも出現位置を保持し、各SourceのLaw入力・readout・witnessが交差で読めることを支持条件にする。
全参照を含む宣言に制限すると、両端と三辺は同じ制限写像になる。
この対応から上の端点・face・支持条件を確認して診断複体を作る。
任意の実被覆を扱うときは、その交差成分と制限に対応するセルを指定する。

**命題16.2（原始比較からのcochain写像）.**
同じ $`S,L,\lambda`$ に対して十分な二readingを取り、$`q_c=\rho q_f`$ とする。
細側から粗側へのセル対応 $`m`$ は、頂点写像 $`m_0`$、辺・面の像または退化記号 $`\bot`$ を指定する。
写る辺は両端を保ち、退化辺の両端は同じ頂点へ移る。
写る面は三辺を保ち、退化面では

```math
[m_1e_{01}]-[m_1e_{02}]+[m_1e_{12}]=0,
\qquad[\bot]=0
```

を粗側の自由整数加群で課す。
支持は、各頂点および像を持つ各辺・面 $`\sigma`$ について

```math
\rho(T_\sigma^f)\subseteq T_{m(\sigma)}^c
```

を満たすものとする。両側の支持を頂点支持の交差で生成する場合には、
この全セルの条件は頂点の条件 $`\rho(T_v^f)\subseteq T_{m_0v}^c`$ から従う。
このデータから、全labelについて自然なcochain写像
$`F_m:D_{q_c}\to D_{q_f}`$ を生成できる。
恒等と二比較の合成を保ち、共通のlabel・支持部分集合への制限とも可換する。

**証明.**
交差生成の場合、細辺の支持の元は両端の支持に属する。その像は対応する粗辺の
両端支持に属するので、粗辺の支持にも属する。面についても三辺の交差に同じ議論を使う。
一般の支持では、上に課した全セルの包含を使う。
label $`a`$ を見える細セルの証人 $`t`$ を $`\rho(t)`$ へ送る。
$`\bar\lambda^c_\ell\rho=\bar\lambda^f_\ell`$ と支持条件により、写るセルの粗像も同じlabelを持つ。
chain上で写るセルの基底を像の基底へ、退化セルを0へ送る。
辺では端点条件、面では写る面の三辺条件または上の零和から、$`m\partial=\partial m`$ を得る。
双対を取れば、写るセルで元のcochainを評価し、退化セルで0とする $`F_m`$ が得られる。
二段の比較で最終的に像を持つセルは両段で像を持ち、支持包含を合成できる。
途中で退化するセルは合成でも退化させる。基底の像を合成すれば境界条件も保たれ、
$`F_{mn}=F_nF_m`$ となる。恒等比較の支持条件は各支持の恒等包含である。
支持部分集合 $`A\subseteq T_c`$ を使う場合は細側を $`\rho^{-1}A`$ とする。
写るセルでは $`\rho(T_\sigma^f\cap\rho^{-1}A)\subseteq T_{m(\sigma)}^c\cap A`$ なので、
同じ証人の輸送により制限後も同じ式になり、比較が可換する。□

この命題は、[第14章](chapter_14_transport_along_readings_and_coefficients.md)の観測と支持の比較を
セルに適用したものである。第15章の二経路の標準比較がセルとlabelを同定すれば、
同じ基底上の計算により診断の比較も一致する。
一方、値域の変更が異なるlabelを一つにする場合は、ここでの固定labelの比較と区別し、16.4節で扱う。

必須残差は[第5章](../part_2/chapter_5_quantities_and_law_geometry.md)のLawful locusを定める。
診断は選んだreadoutと支持を使うので、全必須残差が零であっても $`H^1(D_q)`$ は非零になりうる。
例えば面のない三角形の全辺を一つのlabelが支えると、$`d^0`$ の階数は2、$`D^1=\Lambda^3`$ であり、
体係数で $`H^1(D_q)\cong\Lambda`$ となる。
この空間の存在と、ある修復問題がそこに指定する類の非零性は別の情報である。

## 16.2 核・余核・写像錐と合成

cochain写像 $`F:D\to D'`$ の写像錐を

```math
\mathrm{Cone}(F)^n=D'^n\oplus D^{n+1},\qquad
d(y,x)=(d'y+Fx,-dx)
```

とする。$`F`$ の微分可換性から $`d^2=0`$ を得る。
包含 $`y\mapsto(y,0)`$ と射影 $`(y,x)\mapsto x`$ により
$`0\to D'\to\mathrm{Cone}(F)\to D[1]\to0`$ を作る。
閉元を持ち上げ、その微分をkernelへ戻す操作から長完全列が得られる。
この操作は、liftを変えれば微分の像だけ変わるため類として一意であり、
各箇所のkernelはliftを閉元へ補正できる条件と一致する。
特に

```math
0\to\mathop{\mathrm{coker}}H^0(F)\to H^0(\mathrm{Cone}(F))
 \to\ker H^1(F)\to0,
\qquad
0\to\mathop{\mathrm{coker}}H^1(F)\to H^1(\mathrm{Cone}(F))
 \to\ker H^2(F)\to0.
```

写像錐は比較全体を扱い、次数1の核・余核はその特定の帰結である。
以下では有限次元の体係数を使い、$`J(f)=(\dim\ker f,\dim\mathop{\mathrm{coker}}f)`$ と書く。

**定理16.3（欠損の合成）.**
有限Source、有限Law値族、十分な三readingと命題16.2の二つの実比較から、
有理係数の写像 $`f:H^1(D_0)\to H^1(D_1)`$、$`g:H^1(D_1)\to H^1(D_2)`$ を生成する。
このとき直接比較は $`gf`$ であり、自然な完全列

```math
0\to\ker f\to\ker(gf)\xrightarrow{f}\ker g
 \xrightarrow{\delta}\mathop{\mathrm{coker}}f
 \xrightarrow{g}\mathop{\mathrm{coker}}(gf)
 \longrightarrow\mathop{\mathrm{coker}}g\to0
```

がある。$`\delta(v)=[v]`$ を相殺写像と呼ぶ。
$`r=\mathop{\mathrm{rank}}\delta`$ と置くと

```math
\dim\ker(gf)+r=\dim\ker f+\dim\ker g,\qquad
\dim\mathop{\mathrm{coker}}(gf)+r
 =\dim\mathop{\mathrm{coker}}f+\dim\mathop{\mathrm{coker}}g.
```

同じ列はLaw別の各labelと、粗支持部分集合の標準逆像族にも成立する。

**証明.**
最初の矢印は包含、次は $`x\mapsto f(x)`$、余核間の矢印は
$`[v]\mapsto[g(v)]`$ と $`[w]_{\mathrm{im}(gf)}\mapsto[w]_{\mathrm{im}g}`$ である。
代表を変えた差は対応する像に入るので全写像が定まる。
$`\ker(gf)`$ で次の像が0となる条件は $`f(x)=0`$ である。
$`v\in\ker g`$ について $`\delta(v)=0`$ となる条件は $`v=f(x)`$ であり、この $`x`$ は $`\ker(gf)`$ に入る。
$`[v]`$ が次で消えるなら $`g(v)=gf(x)`$ と書けるため
$`v-f(x)\in\ker g`$ が同じ余核類の原像になる。
最後のkernelは $`[g(v)]`$ の形の類であり、最後の射は全射である。
これで完全性を全箇所で示した。次元式は完全列を像とkernelの短完全列に分けて足せば得られる。
実比較の合成と支持制限は命題16.2の基底計算で同じ写像になる。
labelの有限直和は核・余核と可換するので各blockにも適用できる。□

cocycle $`z\in D_1^1`$ に対して $`g[z]=0`$ は
$`Gz=d_2c`$ となる実際の0-cochain $`c`$ の存在を意味する。
その $`[z]`$ が $`\mathop{\mathrm{im}}f`$ に入ることは
$`z-Fx=d_1b`$ となる粗側cocycle $`x`$ と中間の0-cochain $`b`$ の存在である。
従って相殺写像は、後段で消えた類のうち前段からすでに来ていたものを取り除いている。

**例16.4（相殺と二段の比較）.**
$`0\xrightarrow f\mathbb Q\xrightarrow g0`$ では
$`J(f)=(0,1)`$、$`J(g)=(1,0)`$、$`J(gf)=(0,0)`$ である。
$`\delta:\mathbb Q\to\mathbb Q`$ は恒等で、二つの差が相殺する。
一般に二つの比較が同型なら合成も同型であり、前段と合成、または後段と合成が同型なら残る一射も同型である。
合成だけの零欠損から両段の零欠損を結論することは、この例で否定される。

## 16.3 係数・fiber・局所貼り合わせによる分解

この節では一つのlabel、または支持部分集合を固定し、命題16.2の粗・細セル系を
$`K_c,K_f`$ と書く。係数は $`\mathbb Q`$ とし、各次数の全細セルを原始添字に用いる。
退化辺を $`E_v`$、写る辺を $`E_h`$、全辺が退化する面を $`F_v`$、
一部の辺が写る退化面を $`F_m`$、写る面を $`F_h`$ とする。
退化面の零和を自由基底の係数で比べると、その三辺像は
$`(\bot,\bot,\bot)`$、$`(\bot,e,e)`$、$`(e,e,\bot)`$ のいずれかとなる。

**構成16.5（順像係数と局所fiber）.**
粗頂点 $`c`$ 上の $`\Phi_c`$ は、$`m_0(v)=c`$ の頂点、退化辺、
その上の全辺退化面から作るセル系とする。
粗辺 $`e`$ 上の $`\Gamma_e`$ は、$`m_1(a)=e`$ の細辺を頂点、
粗辺 $`e`$ に属する混在面を辺とするグラフである。
その辺は三辺中の $`e_{02}`$ と、残る非退化辺 $`e_{01}`$ または $`e_{12}`$ を結ぶ。
粗面 $`F`$ について $`\Psi_F=\{f\mid m_2(f)=F\}`$ とする。

粗セル上の係数を

```math
G(c)=\mathbb Q^{\pi_0\Phi_c},\qquad
G(e)=\mathbb Q^{\pi_0\Gamma_e},\qquad
G(F)=\mathbb Q^{\Psi_F}
```

と定める。辺liftの両端を取ると $`\pi_0\Gamma_e\to\pi_0\Phi_{s(e)},\pi_0\Phi_{t(e)}`$ が得られる。
混在面の対応する端点は同じ頂点か退化辺で結ばれるので、成分上で定義できる。
面liftの三辺も対応する $`\Gamma`$ の成分を定める。
関数の引戻しを係数射とすれば、三頂点を経由する二通りの係数射は一致する。
これはincidenceの出現位置を保ったセル係数系である。各係数射の可逆性は要求しない。

順像係数複体を

```math
P^0=\prod_cG(c),\quad P^1=\prod_eG(e),\quad P^2=\prod_FG(F)
```

とし、係数射による端点差と三辺の交代和を微分にする。
三頂点の相殺により複体となる。
粗側複体 $`C=C^\bullet(K_c;\mathbb Q)`$ からの $`\eta:C\to P`$ は
各セル値をそのlift成分上の定数関数にする。
$`\varepsilon:P\to C'=C^\bullet(K_f;\mathbb Q)`$ は、細頂点・写る辺・写る面の成分で評価し、
退化辺・退化面では0とする。混在面の二辺値は同じ $`\Gamma`$ 成分で一致するため相殺し、
$`\varepsilon`$ もcochain写像となる。全成分には評価する細セルがあるので各次数で単射である。
原始比較 $`u:C\to C'`$ について、セルごとに
$`u=\varepsilon\eta`$ を得る。

この係数は、各粗セルのliftをincidenceの関係で貼り合わせた局所定数値から作られている。
たとえば粗辺上では混在面が辺liftの値を同一視する。
文脈の被覆から作ったセル系では、これらはそれぞれ被覆元、二重交差、三重交差のliftの条件となる。
宣言の制限が同じセル・支持・退化対応を保つなら、これらの係数射も成分を制限する式で運ばれる。

**定理16.6（係数差と局所fiberの分解）.**
構成16.5から、原始行列で計算できる空間 $`\mathscr R`$ と写像
$`\tau:\mathscr R\to H^2(P)`$ を構成でき、次が完全となる。

```math
0\to H^1(P)\xrightarrow{b}H^1(C')\to\mathscr R
 \xrightarrow{\tau}H^2(P)\to H^2(C').
```

$`a=H^1(\eta)`$、$`b=H^1(\varepsilon)`$、$`T=H^1(u)=ba`$ と置くと

```math
\ker T=\ker a,\qquad
0\to\mathop{\mathrm{coker}}a\to\mathop{\mathrm{coker}}T
 \to\ker\tau\to0.
```

従って $`T`$ が同型であることと、$`a`$ が同型かつ $`\tau`$ が単射であることは同値である。

**構成と証明.**
細chain内に次の部分複体 $`L_\bullet`$ を作る。

```math
L_0=\partial\mathbb Q[E_v],\quad
L_1=\mathbb Q[E_v]+\partial\mathbb Q[F_m],\quad
L_2=\mathbb Q[F_v]\oplus\mathbb Q[F_m].
```

退化面の分類から $`\partial L_2\subseteq L_1`$、$`\partial L_1=L_0`$ となり、$`H_0(L)=0`$ である。
$`Q=L^\vee`$ とし、細cochainの制限 $`C'\to Q`$ を取る。
体上の部分空間の基底を全体の基底へ延長すれば、この制限は各次数で全射である。
そのkernelを次数ごとに計算する。

- 次数0では退化辺の両端の値が等しく、値が $`\Phi_c`$ の成分へ降りる。
- 次数1では退化辺の値が0で、混在面の二つの非退化辺の値が等しい。
  従って値が $`\Gamma_e`$ の成分へ降りる。
- 次数2では退化面の値が0で、残る値は $`\Psi_F`$ 上の関数になる。

これはちょうど $`\mathop{\mathrm{im}}\varepsilon`$ であり、
$`0\to P\to C'\to Q\to0`$ が短完全になる。
$`H^0(Q)=\mathrm{Hom}(L_0/\partial L_1,\mathbb Q)=0`$ なので、長完全列の次数1の始まりに0を置ける。

残る $`H^1(Q)`$ をfiberから計算する。原始微分を、行 $`E_v,E_h`$、列 $`F_v,F_m,F_h`$ で分ける。

```math
\partial_1=(A\ B_0),\qquad
\partial_2=\begin{pmatrix}V&D&0\\0&B&H\end{pmatrix},\qquad
AV=0,\quad AD+B_0B=0,\quad B_0H=0.
```

垂直chainは $`\Phi_c`$ の直和なので
$`\ker A/\mathop{\mathrm{im}}V=\bigoplus_cH_1(\Phi_c)`$ である。
混在面の組 $`y\in\ker B`$ について $`ADy=0`$ となるため

```math
\kappa:\ker B\longrightarrow\bigoplus_cH_1(\Phi_c),\qquad
y\longmapsto[Dy]
```

を作れる。$`L_1`$ の閉元から混在面の微分を引くと垂直閉元が残る。
垂直閉元が $`L`$ で微分の像になる条件は $`v=Vx+Dy`$、$`By=0`$ である。
従って $`H_1(L)=\mathop{\mathrm{coker}}\kappa`$ となる。
有限次元の双対を取ると

```math
H^1(Q)\cong\mathscr R:=
\ker\left(\kappa^\vee:\bigoplus_cH^1(\Phi_c)\to(\ker B)^\vee\right).
```

この同定は同じ閉元への評価で与えられる。
双対とコホモロジーの同定は16.6節の線形代数の証明でも確認できる。
これで $`\mathscr R`$ と、短完全列の連結射を通じた $`\tau`$ を構成した。

具体的には $`r\in\mathscr R`$ を垂直cochain $`z`$、$`zV=0`$ で表す。
適合条件は $`zD|_{\ker B}=0`$ だから、$`\mathop{\mathrm{im}}B`$ 上の汎関数を延長して
$`\lambda B=-zD`$ となる水平cochain $`\lambda`$ を選べる。
細cochain $`(z,\lambda)`$ の微分は退化面で0、写る面で $`\lambda H`$ であり

```math
\tau(r)=[\lambda H]\in H^2(P).
```

$`\lambda`$ の選択差は $`B`$ を消すので $`P^1`$ の元となり、その $`H`$ への値は微分の像である。
$`z`$ を $`z+\gamma A`$ に替えたときは $`\lambda+\gamma B_0`$ を取ればよく、
$`B_0H=0`$ から同じ類になる。したがって代表にもよらない。
短完全列のliftと微分による連結射の定義と同じ式なので、上の五項列は完全である。
例えば $`\tau(r)=0`$ なら、liftしたcochainの微分を $`P^1`$ の元で消して細側cocycleを得る。

五項列から $`b`$ は単射、$`\mathop{\mathrm{coker}}b\cong\ker\tau`$ である。
定理16.3を $`a,b`$ に適用すると相殺写像の始域 $`\ker b`$ は0となり、主張の核と余核の列を得る。
次元を取ると

```math
\dim\ker T=\dim\ker a,\qquad
\dim\mathop{\mathrm{coker}}T
 =\dim\mathop{\mathrm{coker}}a+\dim\ker\tau.
```

非負整数の和が0となる条件から、最後の必要十分条件が従う。□

この分解は自然な短完全列であり、直和への分裂の選択を含まない。
六項列の相殺写像と、局所fiberの連結射 $`\tau`$ は別の写像である。
十分条件として、全 $`\Phi_c,\Gamma_e`$ が非空連結、全 $`\Psi_F`$ が一点なら $`\eta`$ は複体同型であり、
さらに全 $`H^1(\Phi_c)=0`$ なら $`\mathscr R=0`$ なので $`T`$ は同型になる。
一般には $`\tau`$ を含めた上の条件で判定する。

**例16.7（局所fiberだけが増える場合）.**
粗側を一点、細側を面のない三角形とし、全辺を退化させる。
全セルに同じSource一つを支持させ、Law値を0とする。
$`\Phi_c`$ は三角形、$`P=(\mathbb Q\to0\to0)`$、$`\mathscr R=\mathbb Q`$、$`\tau=0`$ である。
粗側 $`H^1=0`$ から細側 $`H^1=\mathbb Q`$ への余核は、このfiber項そのものになる。
Law別・支持別の診断には、構成16.5を各labelの可視セルへ適用して有限直和を取る。
すべてのblockで同じ原始対応を使うので、直接比較との同一性も保持される。

## 16.4 実現族と値の合流

固定したlabel集合に沿う係数変更 $`\Lambda\to\Lambda'`$ は、有限自由複体のtensorである。
$`\Lambda'`$ が $`\Lambda`$ 上平坦なら、cycleと微分像の短完全列をtensorして
$`H^n(D)\otimes_\Lambda\Lambda'\cong H^n(D\otimes_\Lambda\Lambda')`$ を得る。
これとは別に、実現を動かすとreadout値の等号そのものが変わり、labelの再分類が生じる。

**構成16.8（原始regular readoutとroot scheme）.**
[第6章](../part_2/chapter_6_families_and_moduli.md)の実現族 $`\mathcal M`$ のchartを
$`B=\mathrm{Spec}\,A`$ とし、有限Source $`S`$、有限readout $`L`$、固定した有限支持 $`S_\sigma\subseteq S`$ を取る。
face $`\tau\subset\sigma`$ について $`S_\sigma\subseteq S_\tau`$ を課す。
各 $`f_{\ell,s}\in A`$ は原始操作の有限式から生成するregular scalar readoutとする。
多項式chartの係数、固定した名前付き基底での成分、有限局所自由な自己準同型のtraceが例である。
traceは基底変更の $`\mathrm{tr}(P^{-1}MP)=\mathrm{tr}(M)`$ で不変であり、成分を読む場合はそのchartを保持する。

各セル・readoutについて

```math
Z_{\sigma,\ell}
 =\mathrm{Spec}\,A[z]\Big/\left(\prod_{s\in S_\sigma}(z-f_{\ell,s})\right),
\qquad p_{\sigma,\ell}:Z_{\sigma,\ell}\to B
```

を作る。空支持では積を1とし、空schemeを得る。
monic多項式による商なので $`p`$ は有限射である。
支持包含では多項式が割り切れるため閉埋込み $`Z_{\sigma,\ell}\hookrightarrow Z_{\tau,\ell}`$ が得られる。
診断係数環 $`\Lambda`$ の定数étale層の制限を順像して

```math
\mathscr D_B^n=\bigoplus_{\dim\sigma=n,\ell}(p_{\sigma,\ell})_*\underline\Lambda
```

を作り、faceへの制限の交代和を微分とする。
定数étale層とは、étale試験scheme上で局所定数な $`\Lambda`$ 値関数を読む層である。
微分の二乗では同じ二段の制限が逆符号で現れるので0になる。

**定理16.9（実現族上の診断とstalk）.**
構成16.8の任意の幾何点 $`\bar b:\mathrm{Spec}\,\Omega\to B`$ について
$`(\mathscr D_B)_{\bar b}`$ は、値 $`f_{\ell,s}(\bar b)`$ と同じ支持から
定義16.1で再生成したLaw値複体と自然に同型である。
任意の $`g:B'\to B`$ について $`g^{-1}\mathscr D_B\cong\mathscr D_{B'}`$ であり、微分・比較と整合する。
ここで使うのはétale層の逆像であり、$`\mathcal O_B`$-加群のtensorとは別の操作である。

**証明.**
[補題D.1](../appendix_d_finite_roots_and_stalks.md#d1-有限root-schemeの切断)により

```math
((p_{\sigma,\ell})_*\underline\Lambda)_{\bar b}
 \cong\Lambda^{\{f_{\ell,s}(\bar b)\mid s\in S_\sigma\}}.
```

重複した根や冪零厚みは幾何fiberの点を増やさないので、右辺は相異なる値を一回ずつ読む。
支持包含の制限は値集合の包含への関数の制限である。
有限直和をlabel別に並べ替えると、次数 $`n`$ の座標は
「値 $`w`$ を支持に持つ $`n`$-cell」とちょうど一致する。
微分も同じ端点差・三辺の交代和になるため、複体の同型を得る。
基底変更では多項式の全係数を引き戻した同じroot schemeが得られ、
補題D.1の基底変更同型が各成分と全制限を保つ。
従って複体と生成比較に対して同じ同型が成立する。□

有限個のreadout変数 $`x_{\ell,s}`$ を持つaffine空間上で先にこの構成を行い、
$`x_{\ell,s}\mapsto f_{\ell,s}`$ で引き戻しても同じ複体になる。
同値partitionを固定し、同じblockの差を0、異なるblockの差を単元にしたlocally closed部分上では、
root多項式は相異なる根ごとの互いに素な因子に分かれる。
各因子は基底の一つのsectionの冪零厚みであり、複体は同じ整数incidence行列を $`\Lambda`$ 係数で読んだものになる。
有限次元の体係数では、各partition上のコホモロジー次元も一定になる。

**命題16.10（値の合流による完全列）.**
二つの値のblockを $`K_a,K_b`$ とし、その二値だけが合流するとする。
合流後のblockは $`U=K_a\cup K_b`$、交差は $`I=K_a\cap K_b`$ である。
原始セルの制限から短完全列

```math
0\to C^\bullet(U;\Lambda)\xrightarrow{r}
C^\bullet(K_a;\Lambda)\oplus C^\bullet(K_b;\Lambda)
\xrightarrow{\rho}C^\bullet(I;\Lambda)\to0
```

を得る。$`r(x)=(x|_{K_a},x|_{K_b})`$、$`\rho(y,z)=y|_I-z|_I`$ である。
$`H^1(r)`$ が同型である必要十分条件は、$`H^0(\rho)`$ が全射かつ $`H^1(\rho)=0`$ である。

**証明.**
各次数で、一致する二つの関数は和集合上の一つの関数へ一意に貼り合わされる。
交差の任意の関数は、一方のセル集合上へ0を補えば $`\rho`$ の原像を持つ。
制限と微分は可換するので短完全列を得る。
長完全列の該当部分は

```math
H^0(K_a)\oplus H^0(K_b)\xrightarrow{H^0\rho}H^0(I)
\to H^1(U)\xrightarrow{H^1r}H^1(K_a)\oplus H^1(K_b)
\xrightarrow{H^1\rho}H^1(I).
```

完全性から、$`H^1r`$ の単射性は $`H^0\rho`$ の全射性、全射性は $`H^1\rho=0`$ と同値である。□

これは合流後のblockから合流前の二blockへの制限である。
任意の二実現の間に自動的な特殊化射を置く構成ではなく、固定支持の和と交差から得る比較である。
多数の値の合流では、各cellでそれを含むblockの有限集合を取り、その全交差の交代複体を作る。
その添字集合の一頂点を選ぶ縮約により、増大した複体は各cellで完全となる。
従って全交差を使う有限Mayer–Vietoris複体を得る。
二つの合流順序から和集合へ戻る写像はどちらも同じセルへの制限であり、比較は可換する。

**例16.11（台帳の意味保存族と診断の跳躍）.**
$`B=\mathrm{Spec}\,k[t]`$ 上で分割台帳を $`R^2`$、公開量を $`q(x,y)=x`$、
操作を $`\mathrm{apply}_t(u)(x,y)=(x+u,y+tu)`$ とする。
$`h_t(x,y)=(x,y+tx)`$ は逆 $`h_t^{-1}(x,y)=(x,y-tx)`$ を持ち、
$`h_t\mathrm{apply}_0=\mathrm{apply}_t h_t`$、$`qh_t=q`$ である。
従って全parameterで公開量を保つ意味の同型を持つ。

面のない三角形の各辺に一つずつSourceを置き、そのSourceを辺の両端で支持する。
二つのreadout値を原始定数0、第三をapplyの第二成分の係数 $`t`$ とする。
$`t\ne0`$ の幾何点では、0のblockは二辺の道、$`t`$ のblockは残る一辺で、両者の $`H^1`$ は0である。
$`t=0`$ では一つの三角形blockとなり、$`H^1\cong\Lambda`$ になる。
交差blockは道の両端の二点なので、命題16.10の $`H^0(I)`$ から新しい一類が生じる。
このreadoutは名前付き座標の係数を読むもので、公開量だけを固定した同型に対して不変ではない。
従ってchartの診断として扱う。

逆の次元変化も計算できる。三角形の各辺に値0と値 $`t`$ のSourceをそれぞれ置くと、
$`t\ne0`$ では三角形blockが二つ、$`t=0`$ では一つである。
次元は2から1へ変わり、$`H^1(r):\Lambda\to\Lambda^2`$ は対角写像となる。
非零の差を取る $`H^1(\rho)`$ が、合流前の二類を区別していた情報を表す。

## 16.5 実障害の比較と零性反映

この節では面のない有限単純グラフ $`G`$ を用いる。
実被覆としては、連結な被覆元、連結な非空二重交差、空な三重交差を持ち、
その交差グラフが $`G`$ であるものを取る。
係数の局所同定は全交差で同じ以下の可換群を読むものとする。
この条件により、局所定数係数のČech 0・1-cochainは頂点・辺の座標で一意に表される。

**構成16.12（実操作、関係、mismatch）.**
原始生成元を $`P=L\times S`$ とし、実際の再同定で同じ移動を表すと宣言した関係
$`\mathcal R\subseteq P\times P`$ を与える。
係数群を $`M=\mathbb Z^{(P)}/\langle[p]-[p']\mid p\mathcal R p'\rangle`$ とする。
これは関係の連結成分に一つずつ自由生成元を持つ。
実際、各成分の代表へ各生成元を送り、関係の道に沿って差を加えれば、
商との両方向の写像が互いに逆になる。

各局所状態空間を $`M`$ のtorsorとし、生成元はその類の加算として実際に作用する。
各有向交差辺にアフィン遷移 $`x\mapsto x+\xi_e`$ を指定し、逆向きはその逆とする。
被覆元上の定数torsorの層をこの遷移で貼り合わせる。
三重交差が空なので追加の三重整合式はなく、遷移とその逆の合成が恒等であることから層を得る。
各被覆元で局所状態 $`p_v`$ を選び、固定した原点表示で不一致を

```math
g_e=\xi_e+p_{s(e)}-p_{t(e)}\in M
```

と計算する。これは実遷移と実状態から決まり、診断複体を使わない。
三重交差がないので $`g`$ は1-cocycleであり、$`[g]\in H^1(G;M)`$ が指定実障害である。
頂点補正 $`n_v\in M`$ によって $`p_v`$ を $`p_v+n_v`$ に替えると、不一致は $`g-dn`$ になる。
従って $`[g]=0`$ と、補正して全実遷移を満たす状態を得ることは同値である。
補正後の整合局所状態はtorsorの層の貼り合わせにより大域状態になる。
[定理12.5](../part_4/chapter_12_deformations_and_obstructions.md#124-局所lift後の貼り合わせと意味比較)の
符号 $`r_{ij}=p_j-p_i`$ では、共通の表示へ運ぶと $`r=-g`$ になる。
複体の符号反転同型が両指定類を対応させ、同じ実状態の貼り合わせを判定する。

一方、Law値評価 $`\lambda:P\to\mathscr L`$、$`(\ell,s)\mapsto(\ell,\lambda_\ell(s))`$ と
同じ被覆・支持から $`D_q`$ を独立に生成する。
原始関係はlabelを保つと仮定する。各生成元をそのlabelの基底へ送ることで
$`M\to\mathbb Z^{\mathscr L}`$ を作り、可視頂点・辺に制限して有理化する。
これは微分と可換する写像 $`F:C^\bullet(G;M)\to D_q^\bullet`$ を与える。
診断類は、実mismatchの生成式にこの読みを適用したcocycleの類とする。
したがってその生成を追うと $`\mathrm{diag}(g)=H^1(F)[g]`$ になる。
原点や局所状態を替えた差は $`dF(n)`$ なので、同じ指定類を得る。

**定理16.13（可視閉路による実障害の零性反映）.**
構成16.12で、同じlabelを持つ任意の二生成元が $`\mathcal R`$ の有限zigzagで結ばれるとする。
各label $`a`$ の可視部分グラフ $`G_a`$ が $`G`$ の全非橋辺を含むなら

```math
\mathrm{diag}(g)=0\quad\Longleftrightarrow\quad[g]=0
\quad\Longleftrightarrow\quad
\exists n\in C^0(G;M),\ dn=g.
```

ここで橋とは、それを除くと連結成分数が増える辺である。
補正 $`n`$ からは、各局所torsorへの実際の整数生成操作を復元できる。

**証明.**
関係がlabelを保ち、同じlabelの全生成元を結ぶので、関係成分から発生labelへの写像は全単射である。
構成16.12の自由基底の記述から $`M\cong\mathbb Z^{\mathscr L}`$ を得る。
この同型は各原始生成元をその評価labelへ送るため、実遷移の読みとも可換する。
各labelで $`g_{e,a}\in\mathbb Z`$ を読む。
診断が0なら、可視グラフ上で $`g_{e,a}=b_{t,a}-b_{s,a}`$ となる有理数のpotentialが存在する。
任意の単純閉路の全辺は非橋辺なので可視であり、その向き付き $`g`$ の和は0になる。

各連結成分の全域木と根を選び、根で $`n_{v,a}=0`$ として、木の道に沿った整数の和で $`n_{v,a}`$ を定める。
木の辺では $`dn=g`$ が成立する。
木にない辺は木の道と一つの閉路を作り、その和が0なので同じ等式を満たす。
従って全辺で整数補正が得られる。labelが有限なのでこれを $`M`$ 値の頂点補正へ戻せる。
各係数は原始生成元の整数回の作用として実現でき、同じ $`dn=g`$ が実状態の不一致を消す。
逆に実補正があれば $`F(n)`$ が診断のprimitiveになり、診断類は0となる。□

この証明は $`H^1(D_q)`$ 全体の消滅を要求せず、一つの指定類を追っている。
全非橋辺の可視性は、すべての整数mismatchについての反映には必要でもある。
非橋辺 $`e`$ がlabel $`a`$ で見えなければ、その辺の $`a`$ 座標だけを1にしたmismatchは診断で0になる。
$`e`$ を含む閉路の和は $`\pm1`$ なので実類は非零である。
このmismatchは $`p_v=0`$、指定の $`\xi_e`$ によって実際に生成できる。

**例16.14（反映条件を原始データで調べる）.**
三角形の三辺すべてで一つのlabelが見え、$`M=\mathbb Z`$、遷移値を
$`(1,0,0)`$、局所状態を0とする。閉路の和は1なので、実障害も診断類も非零である。
$`(1,1,-2)`$ なら閉路和は0で、頂点補正 $`(0,1,2)`$ を取れば実不一致が消える。
辺を一つ見えなくすると最初の不一致をそこに置けるため、診断は反映しなくなる。

関係完全性も必要である。二生成元 $`p,p'`$ が同じlabelを持つが関係が空なら、
$`M=\mathbb Z^2`$ である。一辺の不一致を $`[p]-[p']`$ とすると、その実閉路類は非零だが
labelへの読みは0になる。この例は、labelの等号を実係数の関係と同一視できないことを示す。

定理16.13では全頂点の $`M`$ 値補正を許している。
固定部分や許可範囲を課す修復では、その許容補正の像を使う相対的な指定障害へ移る。
例えば一本の辺の両端を厳密固定すると、$`H^1`$ が0でも非零の辺不一致は修復できない。
その全解と再同定の回復には、[第11章](../part_4/chapter_11_ariadne_relative_repairs.md)の
範囲付き複体・実補正作用・全比較の対応を併せて使う。
第12章の平方零lift障害は、指定した変形問題の係数と次数で作る類であり、
本節の貼り合わせの1類へ移す際にも、その局所liftと係数比較を保持する。

## 16.6 双対評価と有限Hilbert複体による読取り

**定理16.15（完全pairingと比較）.**
体 $`\Lambda`$ 上のcochain複体 $`D`$ の各次数を有限次元とし、
双対chainを $`D^\vee_n=\mathrm{Hom}_\Lambda(D^n,\Lambda)`$、
$`\partial_n=(d^{n-1})^\vee`$ と定める。評価は完全pairing

```math
H^n(D)\times H_n(D^\vee)\longrightarrow\Lambda,
\qquad\langle[x],[z]\rangle=z(x)
```

に降りる。cochain写像 $`f:D\to D'`$ に対して

```math
\langle H^n(f)x,z'\rangle=\langle x,H_n(f^\vee)z'\rangle.
```

従って指定類 $`x`$ が0であることと、すべての双対cycleへの評価が0であることは同値である。

**証明.**
双対cycleは $`d^{n-1}`$ の像を消す汎関数であるから、cochainの代表を変えても評価は変わらない。
双対の微分像は $`\lambda d^n`$ の形であり、cocycleを消すので双対側の代表にもよらない。
$`Z^n=\ker d^n`$、$`B^n=\mathop{\mathrm{im}}d^{n-1}`$ とする。
商 $`Z^n/B^n`$ 上の任意の線形汎関数を $`Z^n`$ へ引き戻し、その基底を延長して $`D^n`$ へ延ばす。
延長は $`B^n`$ を消すので双対cycleになる。
二つの延長の差は $`Z^n`$ を消し、$`D^n/Z^n\cong\mathop{\mathrm{im}}d^n`$ を経由する。
その像上の汎関数を $`D^{n+1}`$ へ延ばせば、差は $`\lambda d^n`$ と書ける。
よって $`H_n(D^\vee)\cong\mathrm{Hom}(H^n(D),\Lambda)`$ であり、有限次元性から両側で非退化である。
比較の式は $`z'(f(x))=(z'\circ f)(x)`$ そのもので、商に降りても保たれる。
非零類を含む基底を選び、その座標汎関数を取れば非零評価が得られる。□

同じ診断複体へのこの評価をperiodと呼べる。
少数の選択したcycleだけで零性を判定するには、そのhomology類が双対空間を張ることが必要十分である。
例えば $`H^1(D)=\Lambda^2`$ で第一座標だけを読むと、$`(0,1)`$ を検出しない。
一般の評価写像が存在することだけから、非零類の分離は従わない。

**定理16.16（Hodge分解・harmonic代表・最小残差）.**
$`\Lambda=\mathbb R`$ または $`\mathbb C`$ とし、各 $`D^n`$ に正定値内積
（複素数ではHermitian内積）を選ぶ。随伴とLaplacianを

```math
\Delta_n=d^{n-1}(d^{n-1})^*+(d^n)^*d^n,\qquad
\mathcal H^n=\ker\Delta_n
```

とすると、直交分解

```math
D^n=\mathop{\mathrm{im}}d^{n-1}\ \mathbin{\perp}\
\mathcal H^n\ \mathbin{\perp}\ \mathop{\mathrm{im}}(d^n)^*
```

があり、各コホモロジー類は一意なharmonic代表を持つ。
cocycle $`g`$ のharmonic射影を $`h(g)`$ とすると

```math
\min_{c\in D^{n-1}}\|g-dc\|=\|h(g)\|.
```

**証明.**
随伴の定義から
$`\langle\Delta_nx,x\rangle=\|(d^{n-1})^*x\|^2+\|d^nx\|^2`$ であり、
$`\mathcal H^n=\ker d^n\cap\ker(d^{n-1})^*`$ となる。
$`d^nd^{n-1}=0`$ により二つの像は直交する。
その和の直交補はまさにこのkernelの交差である。
有限次元なので直交補を取れば上の直交直和が全空間になる。
cocycleでは $`\mathop{\mathrm{im}}(d^n)^*`$ 成分が0なので、一意に $`g=dc_0+h(g)`$ と書ける。
exactなharmonic元は自分自身にも直交するため0であり、harmonic空間とコホモロジーの写像は同型である。
任意の $`c`$ について

```math
\|g-dc\|^2=\|h(g)\|^2+\|d(c_0-c)\|^2
```

だから最小値は $`c=c_0`$ で達成される。□

**同じ三角形の読取り。** 例16.14の向き付き三辺と標準内積では、
$`d(c_0,c_1,c_2)=(c_1-c_0,c_2-c_1,c_0-c_2)`$ である。
双対cycle $`z=(1,1,1)`$ のperiodは $`g_1+g_2+g_3`$、harmonic射影は

```math
h(g)=\frac{g_1+g_2+g_3}{3}(1,1,1),\qquad
\|h(g)\|=\frac{|g_1+g_2+g_3|}{\sqrt3}.
```

$`g=(1,0,0)`$ ではperiodが1、最小残差は $`1/\sqrt3`$ である。
$`g=(1,1,-2)`$ では両者が0で、同じ実整数補正が復元される。
実数・複素数の最小化はその係数の補正全体に対する主張である。
本例で整数補正まで戻るのは、定理16.13の全域木による整数復元を併せて使うためである。

比較が各次数でunitaryな複体同型なら、微分の可換式の随伴を取ることで
Laplacianとharmonic射影も可換する。
一般のcochain同型ではこの結論は成立しない。
$`D^0=\mathbb R`$、$`D^1=\mathbb R^2`$、$`d(c)=(c,0)`$、標準内積とし、
$`F^0=1`$、$`F^1(x,y)=(x+y,y)`$ とすると、$`F`$ は複体同型だがharmonic元 $`(0,1)`$ を
非harmonic元 $`(1,1)`$ へ送る。類の輸送は定理16.15で、代表の輸送は内積との整合も含めて扱う。

本章から第17章へは診断写像とその核、指定類を分離する双対評価を渡す。
第18章の修復方程式へは、同じ原始mismatch、許容補正の微分像、指定障害とその読取りを渡す。
Hodge表示は選んだ実・複素内積の下でこの指定類を読む一つの方法である。

**問題16.17.**
面と非自明な係数輸送を持つ実被覆について、定理16.13に代わる零性反映条件を求めよ。
原始関係から作る係数、実mismatch、可視セルへの比較を保持し、整数係数のtorsionも扱うこと。

**問題16.18.**
固定部分・許可範囲を持つ第11章の全修復groupoidについて、診断の比較が全対象と全再同定を
回復する条件を求めよ。指定類の零性反映から追加して必要になるkernelと射の条件を明記すること。

**問題16.19.**
有限root schemeによる診断を、chart間の比較と生成元を忘れる商stack上へ降下させよ。
原始readoutの不変性を満たす族について構成し、満たさない場合は必要な表示データを特定すること。
