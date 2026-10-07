# G-135：fiber適合、transgression、診断保存

[GOAL B・C・E](../../goals/G-135-aat-atlas-coefficient-fiber.md)で要求する写像と仮定を定める。
セル分類、P、Lは[原始入力と順像](README.md)に従う。すべて同じAを固定して書く。

## 1. 混在面が課すfiberの適合

細chainの基底を $`E_v,E_h`$ と $`F_v,F_m,F_h`$ に分け、原始incidenceを

```math
\partial_1=(a\ b),\qquad
\partial_2=
\begin{pmatrix}
V&D&0\\
0&B&H
\end{pmatrix}
```

と書く。Bは $`\bigsqcup_e\Gamma_e^A`$ の有向incidence、Vは垂直面、
Dは混在面の垂直辺成分、Hはmapped面の三辺和である。
$`aV=0`$、$`aD+bB=0`$、$`bH=0`$ は全て $`\partial^2=0`$ から導く。

垂直fiber全体の一次homologyは $`\ker a/\operatorname{im}V`$。
$`y\in\ker B`$ に対し $`Dy\in\ker a`$ なので

```math
\kappa_A:\ker B\longrightarrow\bigoplus_c H_1\Phi_c^A,
\qquad y\longmapsto[Dy]
```

を作る。これは混在面の関係が一周したときに残る垂直閉路である。
Lの垂直部分からのhomology写像により

```math
H_1L_A\cong
 \ker a/(\operatorname{im}V+D(\ker B))
 \cong\operatorname{coker}\kappa_A,
\qquad
H^1Q_A\cong R_A=\ker\kappa_A^*
```

を証明する。最後の同定は有限ℚ双対と標準homologyの同定を伴う。
Lを単に $`\bigoplus_c\Phi_c^A`$ と置くと、混在面のこの商を失う。
forest仮定は、loopと平行辺を保持したΓが無向forestであることとする。
この場合 $`\ker B=0`$ を原始グラフから導き、Rを全fiber H¹の直和へ同定する。

## 2. 完全列の連結射とfiltration

標準短完全列 $`0\to P_A\to C'_A\to Q_A\to0`$ の連結射を
$`\tau_A:H^1Q_A\cong R_A\to H^2P_A`$ と読む。
$`H^0Q_A=0`$ を使ってGOAL Bの列を得る。
完全性・H¹単射性・fiber同定はいずれも構成から証明し、入力fieldにしない。

cochainの代表では、fiber cocycle $`z`$ の混在面での評価 $`zD`$ が
$`\ker B`$ をannihilateすることが $`[z]\in R_A`$ の条件である。
$`\beta B=-zD`$ を満たす水平辺cochain $`\beta`$ を選び、
$`\widetilde z=(z,\beta)`$ とする。その微分は垂直面・混在面で零であり、
mapped面では $`\beta H`$ である。従って

```math
\tau_A[z]=[\beta H]\in H^2P_A.
```

βの選択、zのcoboundary変更、基底変更に依存しないことを証明する。
この式をmathlibの短完全列の連結射の評価式へ同定する。

carrierの次元を $`p=0,1,2`$ とする。細chainの「carrier次元≤p」の部分複体の
filtrationを双対化し、cochainの減少filtrationを作る。
その $`E_1^{p,q}=H^{p+q}(\operatorname{gr}^p)`$ のq=0行はP、
$`E_1^{0,1}=\bigoplus_cH^1\Phi_c^A`$、
$`E_1^{1,1}=\operatorname{coker}B^*\cong(\ker B)^*`$ となる。
間の $`d_1`$ は $`\kappa_A^*`$、続く $`d_2`$ は上の $`\tau_A`$ と一致させる。
必要な低次数のexact couple／spectral sequenceへの接続を証明し、
任意の連結射を名前だけでtransgressionと呼ぶ構成にはしない。

## 3. 消滅条件を原始行列で判定する

$`\overline H:\mathbb Q[F_h]\to\mathbb Q[E_h]/\operatorname{im}B`$ とする。
商chainのH₂は $`\ker\overline H`$。
$`x\in\ker\overline H`$ に対し $`By=Hx`$ を解くと、chainの連結射は

```math
\partial_{\mathrm{conn}}x=[-Dy]
 \in\ker a/(\operatorname{im}V+D(\ker B)).
```

§2のτはこの写像の双対である。したがって次の原始行列の条件と必要十分にする。

```math
\tau_A=0\quad\Longleftrightarrow\quad
\forall x,y,\ By=Hx\ \Longrightarrow
 Dy\in\operatorname{im}V+D(\ker B).
```

右辺は $`\ker(B,-H)`$ の基底と有理像包含の有限検査で判定する。
全Aで検査したときの同値も証明する。消滅を入力に置かずに、許容されるセル表を判定できる形にする。
pure classでは混在面がなく、B・Dの定義域が零なのでτ=0、κ=0が従う。
forestだけではτ=0は従わない。[W3](witnesses.md)で同じ行列の条件が破れる。

## 4. 欠損と保存条件

$`a_A=H^1\eta_A`$ とし、$`T_A=H^1\varepsilon_A\circ a_A`$ とする。
§2の単射性と完全性から、GOAL Cの核同型・余核短完全列を得る。
既存 `blockDefect` の二成分を $`J_A=(j_0,j_1)`$ とすると

```math
j_0=\dim\ker a_A,\qquad
j_1+\operatorname{rank}\tau_A
 =\dim\operatorname{coker}a_A+\dim R_A,
```

さらに

```math
j_1+\operatorname{rank}\tau_A+\operatorname{rank}\kappa_A^*
 =\dim\operatorname{coker}a_A+\sum_c\dim H^1\Phi_c^A.
```

自然数ではこの加法式を用いる。減算表示は同じ等式の整数表示とする。
核は係数差の核、余核は係数差の余核と、二段の適合・transgressionを通過したfiber類からなる。
一般の保存条件は $`a_A`$ が同型かつτが単射であることと必要十分にする。

原始的な局所十分条件として、選択された各粗chartについてΦの連結成分が一つ、
各粗辺についてΓの連結成分が一つ、各粗面について持ち上げが一つであることを使う。
この条件からηの次数別同型を導く。さらに全chartで $`H^1\Phi_c^A=0`$ ならR=0、
従って零欠損となる。高次fiberの零性はこのH¹保存の仮定に含めない。
順像係数そのものを粗係数に選ぶ場合はηを恒等にでき、核は零、余核は $`\ker\tau_A`$ になる。

pure classでは

```math
J_A=0\quad\Longleftrightarrow\quad
a_A\text{ が同型かつ全 }c\text{ で }H^1\Phi_c^A=0.
```

これを全Aへ量化してC3′を得る。混在面を含む一般入力にはRとτによる条件を用いる。
`ResolutionInvarianceConditions.CoordinateFiberEdge`は端点が同じ粗chartへ写る辺を
すべて含み、粗loopへ写る辺も含む。G-107のC3非必要性例の同じ原始表について、
宣言上の退化辺で作るΦを計算し、C3の失敗とC3′の成立を同時に示す。

## 5. 三つの錐とG-133の相殺

三項複体をG-133の `zeroExtension` でℤ添字に移す。
錐は $`D(u)^n=C'^n\oplus C^{n+1}`$、
$`d(y,x)=(d'y+ux,-dx)`$ とする。Aの実因子化等号を
`compositionTriangle`へ渡し、

```math
D^{\mathrm{coeff}}_A\to D^{\mathrm{total}}_A\to
D^{\mathrm{fiber}}_A\to D^{\mathrm{coeff}}_A[1]
```

を標準homotopy圏のdistinguished triangleへ接続する。
評価 $`(y,x)\mapsto y|_{L_A}`$ が $`D^{\mathrm{fiber}}_A\to Q_A`$ の擬同型を与えることを証明する。
この同定と、錐の包含・射影・連結射の符号を§2の短完全列へ合わせる。
各錐の全整数次数で `cone_short_exact` を使い、H⁰余核・H²核などの寄与も保持する。

G-133の $`\chi:\ker H^1\varepsilon_A\to\operatorname{coker}a_A`$ は始域が零なので零である。
$`\tau_A:R_A\to H^2P_A`$ は別の始域・終域を持ち、W3では非零になる。
一般の六項相殺公式とこの五項完全列の関係は、同じ二射への特殊化として証明する。
