# 第6章 構造の族と実現のモジュライ

量を動かすだけでなく、状態の加群と原始演算そのものを動かす。
名前付き生成元があれば基底を選ぶ開集合を作れる。
生成元を忘れると自己同型が残るため、実現の族はgroupoidとして扱う。
この章では原始演算の係数からchartを構成し、係数のdescentを証明してから、
scheme、商stack、量の相対Specを得る。

## 6.1 係数実現の族と同型

**定義6.1（実現の族と多項式的な入力）.**
第4章で係数変更とその整合性を証明した方式の意味圏から、対象をそのまま、射を同型に限ったgroupoid

```math
\mathcal M_{\mathbb T,\sigma}(U,R)
 =\mathcal A_{\mathbb T,\sigma}(U,R)^{\simeq}
```

を取る。係数変更の単位・結合同型により、これは $`k`$-代数上の擬関手になる。
全意味圏も保持し、非可逆射を含む変更の族は第7章で別に作る。

本章の具体的な入力は、有限なsort集合 $`S_0`$、各sortの階数 $`n_s\ge0`$、
小さい演算族と小さいLaw族である。演算 $`e:(s_1,\ldots,s_d)\to t`$ は有限arityを持つ。
試験scheme $`T`$ 上の独立な実現は、階数 $`n_s`$ の有限局所自由
$`\mathcal O_T`$-加群 $`E_s`$ と、写像

**式(6.1)**

```math
\mu_e:\bigotimes_{i=1}^d E_{s_i}\longrightarrow E_t
```

の族である。0引数は指定切断である。
Lawは同じ入出力型の二つのtensor式の等号とする。
tensor式は恒等、置換、原始演算、tensor積、合成、有限和、$`k`$ のスカラー倍から作る。
指定生成元を含む場合は、それを0引数の構造写像として式に用いてよい。
全ての必須Lawを満たす実現と、その演算を保つ全 $`\mathcal O_T`$-線形写像を意味圏とし、
同型だけからなるgroupoidを $`\mathrm{Real}_{\boldsymbol n}(T)`$ と書く。

このtensor式のLawは[命題4.10](chapter_4_coefficient_realizations.md#44-加群のtensor実現と比較)の
係数変更に安定な場合である。
変数を反復する多項式Lawも、次の規則で扱う。
termは上の原始演算、変数、指定切断、和と $`k`$ のスカラー倍で作り、同じ変数を複数回用いてよい。
Lawの意味は、任意の試験schemeへの引戻し後の全局所入力で二辺が一致することである。
自由なchartで入力を $`v_i=\sum_a z_{ia}e_{ia}`$ と置き、残差を多項式に展開する。
このLawは全出力成分の全単項式係数が0であることと同値である。
十分性は代入、必要性は係数環の多項式拡大とその普遍入力で従う。

この規則の座標独立性も確認する。基底変更 $`e_i'=e_iC_i`$、出力の基底変更 $`C_o`$ の下で、
残差多項式は $`r'(z)=C_o^{-1}r(C_1z_1,\ldots,C_dz_d)`$ になる。
原始演算ではその保存式、複合termでは帰納法でこの等式を得る。
各新係数は元の係数の有限線形結合であり、逆の基底変更でも同じことが成り立つ。
よって係数の生成イデアルは一致する。この計算は任意の環射とも可換する。
以下ではtensor式のLawにはその成分を、多項式Lawにはこの全係数を残差として用いる。

環射 $`R\to R'`$ 上では $`E_s\mapsto E_s\otimes_RR'`$ とする。
一般schemeの射では層の引戻しを用いる。
演算・tensor式は純tensorの計算で、多項式Lawは上の係数計算で引戻しと可換し、Lawも保存される。
単位・結合の整合は構成4.8の計算による。

**補題6.2（加群・演算・射の係数descent）.**
上の実現と全構造保存射はZariski被覆およびfppf被覆に関して有効なdescentを持つ。
すなわち被覆上の実現と重なり上の同型がcocycle条件を満たせば大域実現に由来し、
同型に整合する全局所射も一意に大域射から得られる。
その最大部分groupoid $`\mathrm{Real}_{\boldsymbol n}`$ はfppf stackである。

**証明.**
[補題B.4](../appendix_b_coefficients_and_descent.md#b2-忠実平坦な係数descent)で、
忠実平坦な環射について加群と全線形写像を等化子から構成し、係数拡張後に元へ戻ることを示す。
補題B.5により有限局所自由性と階数も降下する。
各 $`E_s`$ をこの構成で降下し、そのtensor積のdescent datumを作る。
局所演算 $`\mu_e`$ は局所同型との可換性によりdatumの射であるため、一意に降下する。
tensor式の評価は引戻しと交換するので、Lawの二辺の差は被覆上で0になる。
忠実性により大域でも0である。多項式Lawの場合は自由化したchartで全残差係数に
同じ忠実性を適用し、座標独立性によって大域のLawを得る。
局所の構造保存射も加群写像として降下し、その演算保存式は同じ忠実性で降下する。
逆射を持つ局所射では逆射も降下し、合成の一意性によって大域の逆射となる。
一般schemeとfppf被覆への移行は付録B.3のaffine局所化による。
これが対象の有効性と射の層条件をともに与える。□

宣言方向の制限は、[第3章](../part_1/chapter_3_contexts_and_local_models.md)のとおり宣言を忘れる。
係数方向の制限は、今のtensorと引戻しである。
宣言の包含 $`U\subseteq W`$ に対し、残すsortでは両順序とも $`f^*E_s`$、
残す演算では両順序とも $`f^*\mu_e`$ を得る。射も残す成分の引戻しとなる。
これらの恒等比較はtensorの単位・結合同型と可換するため、二方向は自然な同型の下で交換する。
descentで構成した対象にも、補題B.4の一意性から同じ比較が得られる。

## 6.2 生成元と基底chart

**定義6.3（生成元付き実現と基底付き実現）.**
各sortに $`m_s\ge n_s`$ を固定する。
生成元付き実現には、さらに全射

```math
\pi_s:\mathcal O_T^{m_s}\twoheadrightarrow E_s
```

を与える。同型は演算と $`\pi_s`$ を保つ。
その同型類の集合を $`\mathrm{Mark}_{\boldsymbol m,\boldsymbol n}(T)`$ と書く。
これは固定した宇宙で集合となる。実際、markingから各sortの部分加群層
$`\ker\pi_s\subseteq\mathcal O_T^{m_s}`$ を選び、その商に演算を選ぶデータで記述できる。
小さいaffine開基底上の部分加群とその制限の族、および層の射の集合は、いずれも集合である。
markingを保つ自己同型 $`a_s`$ は $`a_s\pi_s=\pi_s`$ と全射性から恒等である。
したがってこのgroupoidは同型類の集合と同値である。
affine $`T=\mathrm{Spec}\,R`$ では、$`K_s=\ker\pi_s\subseteq R^{m_s}`$ と演算によっても記述できる。
実際 $`R^{m_s}/K_s\cong E_s`$ はmarkingを保ち、逆にmarkingを保つ同型はkernelを変えない。

基底付き実現は、同型 $`b_s:\mathcal O_T^{n_s}\xrightarrow{\sim}E_s`$ を持つ実現である。
基底はmarkingの一種だが、一般のmarkingには基底以外の生成元もある。

環射に沿ってkernelを変更するときは、商加群をtensorしてからkernelを取る。
上の短完全列はaffine上で $`E_s`$ が有限射影なので分裂し、
$`K_s\otimes_RR'\to(R')^{m_s}`$ は単射で、その商は $`E_s\otimes_RR'`$ である。
したがってflatでない係数変更でも、このkernel表示とtensor表示は一致する。

**構成6.4（基底を選んだ方程式）.**
各sortの $`m_s`$ 個の名前付き生成元から、順序を保って $`n_s`$ 個を選ぶ添字 $`I_s`$ を取る。
組 $`I=(I_s)_{s\in S_0}`$ をchart添字とする。
この選択生成元を基底とし、生成元行列を
$`P_s^I=(p_{s,aj})`$ と書く。選択列は単位行列、残りの列は独立変数である。
原始演算には係数 $`c_{e,b;a_1,\ldots,a_d}`$ を置く。
各Lawの二辺をこの係数で展開する。tensor式では全入力基底・出力基底について残差を取り、
多項式Lawでは6.1節の規則により全出力成分の全単項式係数を取る。
ambient環とその商を

**式(6.2)**

```math
A_I=k[p_{s,aj}\ (j\notin I_s),\ c_{e,b;\boldsymbol a}],\qquad
J_I=(\text{必須Lawの残差成分または全単項式係数}),\qquad B_I=A_I/J_I,\qquad U_I=\mathrm{Spec}\,B_I
```

とする。sortは有限個、各階数とarityは有限だが、演算・Lawの族は任意の小さい集合でよい。
tensor式の各成分は、合成では有限和の積、tensor積では係数の積となるので多項式である。
式(6.2)から普遍自由加群、全射 $`P_s^I`$、演算を実際に作れる。

このchartは、選択生成元が全域で基底になる独立な生成元付き実現の関手を表す。
実現から基底で係数を読み、逆に係数から自由加群と演算を作る。
tensor式の帰納法と多項式Lawの普遍入力の計算により、Lawの充足は各残差の零性と同値である。
二つの操作は互いに逆である。
markingを保つ同型は一意なので、同型類でこの対応を取っても情報は失われない。
第5章の表現証明と同じく、係数射との自然性は全変数の像で検査できる。

## 6.3 chartの接着と普遍実現

**定理6.5（生成元付き実現のscheme表示）.**
定義6.1・6.3の原始入力から、scheme $`M_{\boldsymbol m,\boldsymbol n}`$ と普遍実現を構成できる。
任意の試験 $`k`$-scheme $`T`$ で自然な全単射

```math
\mathrm{Hom}_k(T,M_{\boldsymbol m,\boldsymbol n})
\ \cong\ \mathrm{Mark}_{\boldsymbol m,\boldsymbol n}(T)
```

がある。$`M_{\boldsymbol m,\boldsymbol n}`$ は構成6.4の $`U_I`$ を、
生成元の基底変更で得るopen同型に沿って接着したschemeである。

**構成と証明.**
$`I`$-chartで別の選択 $`J_s`$ の列を並べた正方行列を $`C_s=P_s^I[J_s]`$ と置く。
その列が新しい基底となる条件は各 $`\det C_s`$ が可逆であることなので、
共通部分は $`D(d_{IJ})`$、$`d_{IJ}=\prod_{s\in S_0}\det C_s`$ である。
sortが有限個であることをここで用いる。階数0では行列式を1とする。
その上で新しい係数は

**式(6.3)**

```math
P_s^J=C_s^{-1}P_s^I,\qquad
\mu_e^J=C_t^{-1}\mu_e^I(C_{s_1}\otimes\cdots\otimes C_{s_d}).
```

逆行列は余因子行列を行列式で割って作れるから、これは局所化環の射を与える。
各tensor式 $`w`$ についても、構文帰納法で
$`w^J=C_{\mathrm{out}}^{-1}w^IC_{\mathrm{in}}`$ が成り立つ。
合成の内部では隣り合う $`C C^{-1}`$ が消え、tensorと和はこの式を保つ。
したがって残差も同じ変換式に従い、各成分は元の残差成分の線形結合である。
逆の基底変更でも同じことが成り立つので、局所化した残差生成イデアルは対応する。
多項式Lawでは6.1節の変数変換の計算により全係数の生成イデアルが対応する。
よって式(6.3)は商環上のopen同型になる。
さらに $`P_s^J[K_s]=C_s^{-1}P_s^I[K_s]`$ なので、その行列式は
$`\det(C_s)^{-1}\det(P_s^I[K_s])`$ である。
したがって $`K`$-chartとの重なりのopenはこの同型で正確に対応する。

$`I\to J\to K`$ の基底変更行列は、$`I\to K`$ の行列の分解である。
式(6.3)へ代入すると行列積が結合し、直接変更と同じ係数になる。
これで三重交差のcocycleと両逆を得る。
[補題B.6](../appendix_b_coefficients_and_descent.md#b3-層chartと相対spec)でopen chartを接着し、
普遍加群と全射と演算も同じ基底変更で貼り合わせる。Lawは各chartで成り立つので大域でも成り立つ。

独立なmarking $`\pi_s`$ を与えたとき、その生成元が各残差体上で $`E_s`$ を張るため、
各点で $`n_s`$ 個の列を選んで基底にできる。
有限局所自由加群を局所的に自由化すると、同じ条件は行列式の非消滅によって開集合を定める。
全sortについて共通の近傍を取れば、これらの開集合 $`T_I`$ が $`T`$ を覆う。
$`T_I`$ 上で係数を読み、構成6.4により $`T_I\to U_I`$ を得る。
重なりでは式(6.3)で同定されるので $`T\to M_{\boldsymbol m,\boldsymbol n}`$ に貼り合う。
逆に普遍実現を引き戻せばmarking付き実現を得る。
各chartで二つの構成が逆であり、markingを保つ同型の一意性から大域でも逆である。
これらの操作は全て係数変更と可換する。□

**例6.6（二生成元のline quotientと局所基底）.**
一つのrank1の加群に二つの生成元を与え、演算は置かない。
第一生成元を基底とすると行列は $`(1,u)`$、第二を基底とすると $`(v,1)`$ である。
重なりで $`u`$ が可逆、$`v=u^{-1}`$ なので、二つのaffine直線を貼り合わせた
$`\mathbb P^1_k`$ を得る。指定した単項演算にLaw $`N=0`$ を課しても同じである。

全射 $`(2,3):\mathbb Z^2\to\mathbb Z`$ は $`-2+3=1`$ から全射である。
どちらの生成元も $`\mathbb Z`$ 上の基底ではない。
$`D(2)`$ では第一生成元が基底で行列 $`(1,3/2)`$、
$`D(3)`$ では第二が基底で行列 $`(2/3,1)`$ となる。
二つの開集合は全体を覆い、交差で $`(3/2)^{-1}=2/3`$ として貼り合う。
一つの大域markingが、一つの基底chartに全域で入る必要はない。

## 6.4 frame・自己同型・商stack

ここでは、fppf stackで対角がalgebraic spaceで表され、schemeからsmoothな全射を持つものを
algebraic stackという。algebraic spaceはschemeのétale同値関係による商のfppf層をいう。
この全射をatlasと呼ぶ。以下の対角はschemeで表されることまで示す。
schemeの射のsmooth性は、局所有限表示であり、冪零閉埋込みに対する持上げが局所的に存在する条件をいう。
smooth射がflatであること、smooth性のbase change安定性とfppf局所性をscheme論の標準事実として用いる。
本章のrepresentableな射は、任意のschemeへの引戻しがschemeとなる射を指す。
そのsmooth性も引戻したschemeの射で定める。

この節では、生成元の名前を用いない演算とLawを固定し、markingを自由な追加データとする。
全sortに基底を選び、原始演算の係数とLaw残差だけから
affine scheme $`X_{\boldsymbol n}`$ を作る。
$`G_{\boldsymbol n}=\prod_{s\in S_0}\mathrm{GL}_{n_s,k}`$ とし、右作用を

**式(6.4)**

```math
(\mu\cdot g)_e=g_t^{-1}\mu_e(g_{s_1}\otimes\cdots\otimes g_{s_d})
```

で定める。tensor式の残差は同じ式で、多項式Lawの残差は6.1節の係数変換で移るため、
作用はLawの零点を保つ。
$`(\mu\cdot g)\cdot h=\mu\cdot(gh)`$ と単位律は行列積で確認できる。

**定理6.7（実現groupoidと商stack）.**
全ての試験schemeで自然なgroupoidの同値

```math
\mathrm{Real}_{\boldsymbol n}\ \simeq\ [X_{\boldsymbol n}/G_{\boldsymbol n}]
```

がある。右辺の対象は右 $`G_{\boldsymbol n}`$-torsor $`P\to T`$ と
右同変射 $`P\to X_{\boldsymbol n}`$ で、射は両写像を保つtorsor同型である。
ここでtorsorはfppf局所で $`G_{\boldsymbol n}\times T`$ と同型になるものをいう。
このstackはalgebraic stackであり、基底付き実現 $`X_{\boldsymbol n}`$ がsmoothな全射atlasとなる。
また

```math
M_{\boldsymbol m,\boldsymbol n}\longrightarrow\mathrm{Real}_{\boldsymbol n}
```

はmarkingを忘れるrepresentable、smooth、全射の射である。

**構成と証明.**
実現 $`E`$ からframeの層

```math
P_E=\prod_s\mathrm{Isom}_{\mathcal O_T}(\mathcal O_T^{n_s},E_s)
```

を作る。$`E_s`$ を局所的に自由化すると可逆行列のschemeになり、
基底変更で貼り合う。右作用は $`b\cdot g=b\circ g`$ である。
二つのframeは一意な可逆行列で結ばれるので、これはZariski局所で自明なtorsorである。
frameごとに演算係数を読むと、式(6.4)によって同変な $`P_E\to X_{\boldsymbol n}`$ を得る。

逆にtorsorと同変射を与える。torsorを自明化するfppf被覆上で、
同変射の値から自由加群と演算を作る。
重なりのtorsorの遷移行列はcocycleを満たし、同変性は式(6.4)そのものである。
補題6.2により加群・演算を降下して実現を得る。
torsor同型は局所frame間の可逆行列として、演算を保つ加群同型を降下させる。
逆に実現同型はframeを送るtorsor同型を与える。
局所自明化で両合成は恒等であり、射のdescentの一意性から大域の自然な両逆となる。
これで対象だけでなく全ての同型も対応した。

代数性を確認する。二実現 $`E,F`$ の同型の層は、
$`\prod_s\mathrm{Isom}(E_s,F_s)`$ の中で演算保存の成分方程式を課した閉部分schemeである。
この構成は基底変更で整合するので対角はschemeで表現される。
$`T\to\mathrm{Real}_{\boldsymbol n}`$ に沿う $`X_{\boldsymbol n}`$ の引戻しはframe scheme $`P_E`$ である。
各 $`\mathrm{GL}_{n_s}`$ は $`\mathbb A^{n_s^2}`$ の行列式を可逆にしたopenなのでsmoothで有限表示である。
有限積と局所自明化から $`P_E\to T`$ はsmoothな全射である。
補題6.2のstack条件と合わせて、representableな対角とsmooth atlasという代数性の条件を満たす。

markingを忘れる射を $`E/T`$ に沿って引き戻すと、
各 $`\mathcal O_T^{m_s}\to E_s`$ の全射を選ぶschemeになる。
これは有限階数の写像のvector bundleの中で最大小行列式が生成するイデアルを単位とするopenである。
局所frame上では全射行列が存在するため全射で、vector bundleの開部分schemeだからsmoothである。
これで忘却射についての主張を得る。□

この定理の忘却射では、markingは追加の自由な生成元である。
marking自体に別のLawを課す場合には、その方程式をさらに課した射となり、
smooth性や全射性はその方程式について別に調べる。

**自己同型.**
実現 $`E`$ の自己同型は、$`\prod_s\mathrm{GL}(E_s)`$ のうち
$`a_t\mu_e=\mu_e(\bigotimes_i a_{s_i})`$ を全演算で満たす部分群schemeである。
frame上では式(6.4)のstabilizerとなり、frame変更では共役される。
markingを保持すると定義6.3の全射性によって自己同型は恒等だけになる。
自己同型を保持する実現groupoidと、その同型類の集合は別の対象である。

**例6.8（lineの自己同型と冪零演算）.**
rank1で演算がないと $`X=\mathrm{Spec}\,k`$、$`G=\mathbb G_m`$ なので、
生成元を忘れた実現は $`B\mathbb G_m`$ となる。
例6.6の $`\mathbb P^1`$ は二生成元を選ぶschemeであり、その忘却先がこのstackである。
一つのlineの自己同型は可逆スカラー全体である。

rank1の単項演算 $`N`$ にLaw $`N^2=0`$ を課すと、基底係数 $`z`$ は $`z^2=0`$ を満たす。
よって $`X=\mathrm{Spec}\,k[z]/(z^2)`$ である。
rank1の共役作用は自明なので実現stackは $`[X/\mathbb G_m]`$ となる。
体 $`k`$ の上で $`N=0`$ の実現を取ると、dual numbers上の $`N=a\varepsilon`$ は全てliftである。
これらは普遍演算の方程式から生じる微小方向である。

階数を固定しない有限局所自由実現では、各sortの階数は局所一定である。
sortが有限個なので、階数の組 $`\boldsymbol n`$ が一定の開閉部分に分解できる。
全階数の族は $`\coprod_{\boldsymbol n\in\mathbb N^{S_0}}\mathrm{Real}_{\boldsymbol n}`$ で表され、
基底chartとatlasもこの成分ごとに作る。
marking数を固定した場合は $`\boldsymbol n\le\boldsymbol m`$ の成分を使う。

## 6.5 相対Specと表示の成立条件

量を構造の族の上へ載せるには、量の**型**を保持する。
固定集合上の任意関数、加群上の線形量、多重線形量は、それぞれ異なる入力を持つ。

**定義6.9（構造の底と、量・Lawの原始型）.**
量を加える前の構造理論を $`\mathbb T_{\mathrm{str}}`$ とする。
その係数実現の同型groupoid $`\mathcal M_{\mathbb T_{\mathrm{str}},\sigma}`$ がfppf stackであり、
scheme $`X`$ からのrepresentableなfppf全射 $`p:X\to\mathcal M_{\mathbb T_{\mathrm{str}},\sigma}`$ を
持つ場合を扱い、このstackを $`\mathcal B_\sigma`$ と書く。
representableとは、任意のscheme $`T\to\mathcal B_\sigma`$ とのfiber積がschemeになることをいう。
特に $`X\times_{\mathcal B_\sigma}X`$ もschemeである。
有限局所自由実現では $`\mathcal B_\sigma=\mathrm{Real}_{\boldsymbol n}`$ と取れ、
補題6.2と定理6.7がこの条件と被覆を供給する。

原始担体は、係数変更でtensorされる準連接加群 $`E_s`$ とその多重線形演算、指定切断である。
固定集合を用いる場合には、係数変更で引き戻される集合の層 $`D_j`$ も指定する。
これは $`X`$ のfppf細分上で定数集合の層に分裂するものとし、
その操作・関係・Law入力も同じ細分上で集合の写像・部分集合として指定する。
固定集合や第4章の局所splitなcopying構造がこの場合に入る。
構造同型は全ての原始写像を保つ。以下の量は、この構造に追加するデータである。

量の型は次の規則で指定する。
基本の線形入力型は $`\mathcal O`$、$`E_s`$、および $`D_j`$ の元を生成子とする自由型である。
これらから小さい直和、有限tensor積を作ってよい。
線形関係を課すには、二つのこのような型 $`P_1,P_0`$ と
原始写像から作る線形式 $`d:P_1\to P_0`$ を指定し、$`q\circ d=0`$ を要求する。
線形式の構文子は、原始多重線形演算をtensor積からの写像としたもの、集合写像の線形化、
恒等、置換、直和の包含、tensor積、合成、有限和、$`k`$ のスカラー倍である。
直和からの射は各summand上で指定し、自由な生成子の像は有限和とする。
任意の原始線形関係写像も構造の演算として宣言できる。

この量の意味は、生成子への値、または指定された線形・多重線形写像であって、
線形関係を課した型ではその関係を消すものとする。量が複数あれば型の直和を用いる。
各affineな分裂chart上で型を生成子と関係に展開すると、固定索引 $`H_0,H_1`$ により

**式(6.5)**

```math
R^{(H_1)}\xrightarrow{d_b}R^{(H_0)}\longrightarrow Q_b\longrightarrow0
```

を得る。関係の列は有限和であり、係数変更ではこの表示をtensorする。
生成子・関係の数の有限性は要らない。新しい係数の加群の全ての元を自由生成子として追加する操作とは区別する。

| 量の型 | 構成する $`Q_b`$ | 量の値からの対応 |
| --- | --- | --- |
| 固定集合 $`D_j`$ 上の任意関数 | $`\bigoplus_{j,x\in D_j}R e_{j,x}`$ | $`e_{j,x}\mapsto q_j(x)`$ |
| $`E`$ 上の線形量 | $`E`$ | 量そのものが線形写像 |
| $`E_1,\ldots,E_d`$ 上の多重線形量 | $`E_1\otimes_R\cdots\otimes_RE_d`$ | 純tensorへそのtupleでの値を割り当てる |
| $`d:P_1\to P_0`$ の関係を消す量 | $`\mathrm{coker}\,d`$ | $`P_0`$ 上の値が $`d`$ の像を消すので商へ移る |

線形型の任意の表示、tensor型の生成子tupleと各変数の線形関係、商の追加関係によって、
この表の全てを式(6.5)にできる。
対応は任意の値加群 $`N`$ に対する $`\mathrm{Hom}_R(Q_b,N)`$ との全単射である。
量の値では $`N=R`$ を使う。

Lawは小さい族とし、各Lawには有限tupleの入力型を指定する。
集合型の入力には指定された部分集合を使い、加群型の入力は上の線形入力型の全体を使う。
二辺は $`k`$ の係数、環演算、量の適用からなるscalar式であり、
量へ渡すtermは原始演算、指定切断、線形式、集合の原始写像と変数から作る。
全termは指定入力上で定義されるものとする。同じ入力変数を反復してよい。
Lawの意味は、**任意の係数変更後の全局所入力**で二辺が等しいことである。
集合型だけなら、これは第5章の固定入力のLawと同じである。
加群型では形式的な入力を用いる次の構成がこの意味を表す。

**比較と残差の構成.**
構造同型 $`h:b\to b'`$ は、$`E_s`$ 上ではその成分 $`h_s`$、
自由な集合型では $`e_x\mapsto e_{h(x)}`$ を与える。
直和では成分ごとに、tensor型では $`\bigotimes h_s`$ として比較を作る。
原始演算の保存式から、線形式の構文帰納法で
$`h_{P_0}d_b=d_{b'}h_{P_1}`$ を得る。
したがって商にも $`h_Q:Q_b\to Q_{b'}`$ を誘導できる。
基本型で恒等・合成・逆を保ち、各構文子もそれらを保つため、全型で同じ法則が成り立つ。
これらの式は係数の有限和・積と純tensorの像で与えられるので、任意の係数変更とも可換する。
これが量の比較を作る手順である。

$`A_b=\mathrm{Sym}_RQ_b`$ とし、普遍量 $`Q_b\to A_b`$ で原式を評価する。
加群入力型 $`P_i`$ に生成族 $`(g_{ia})_{a\in H_i}`$ を選ぶ。
各 $`H_i`$ の任意の有限部分集合 $`F_i`$ と独立変数 $`z_{ia}`$ に対し

```math
v_i=\sum_{a\in F_i}z_{ia}g_{ia},\qquad
\rho_{\ell,\gamma,\boldsymbol F}(z)
 =t_\ell(q^{\mathrm{univ}},\gamma,\boldsymbol v)
  -t'_\ell(q^{\mathrm{univ}},\gamma,\boldsymbol v)\in A_b[z_{ia}]
```

を作る。$`\gamma`$ は集合型の入力である。
全 $`\ell,\gamma,\boldsymbol F`$ について、この多項式の**全単項式係数**が生成するイデアルを $`I_b`$ とする。
加群入力がなければ入力ごとの残差だけを取る。
多重線形なLawでは生成子tupleでの値で十分であり、有限自由な型では基底に関する成分に一致する。
一般の非自由型でも生成族への有限形式和なので、この定義が使える。

量候補による環射 $`A_b\to R'`$ の下で、残差の像は原式の値に一致する。
これは量の葉と環演算の帰納法による。
全係数が消えれば、任意のさらなる係数変更と入力への代入でLawが成立する。
逆に普遍的にLawが成立すれば、$`R'[z_{ia}]`$ 上の上の入力で残差が0だから全係数が消える。
入力加群の元は局所的に生成子の有限線形結合なので、これで独立なLawの意味と同値になる。

構造同型で量座標を送る代数射を $`\psi_h=\mathrm{Sym}(h_Q)`$ とする。
入力の翻訳は集合型では $`\gamma\mapsto h(\gamma)`$、加群型では $`v_i\mapsto h_{P_i}(v_i)`$ である。
原始写像の保存、量の普遍写像の等式
$`\psi_h(q_b^{\mathrm{univ}}(x))=q_{b'}^{\mathrm{univ}}(h_Qx)`$、環演算について帰納すると、

```math
\psi_h\bigl(\rho_{\ell,b}(\gamma,\boldsymbol v)\bigr)
 =\rho_{\ell,b'}\bigl(h(\gamma),(h_{P_i}v_i)_i\bigr)
```

を得る。各 $`h_{P_i}(g_{ia})`$ を相手側の生成子の有限線形結合で書くと、
右辺は相手側の普遍入力多項式への線形な変数代入である。
その各係数は相手側の残差係数の有限線形結合に入り、$`\psi_h(I_b)\subseteq I_{b'}`$ となる。
逆同型から逆の包含を得る。この議論は生成族の交換にも使えるので、イデアルはその選択によらない。
集合型の比較が分割上で与えられる場合は、Lawに現れる有限個の入力の開閉分割を共通細分する。
その冪等元を $`u_a`$、各片での入力の像を $`\gamma_a`$ とすれば、残差は
$`\sum_a u_a\rho_{\ell,b'}(\gamma_a,\boldsymbol v')`$ となる。
多項式の積でも $`u_a^2=u_a`$、$`u_au_c=0`$ により混合項は消え、同じイデアルの包含が従う。

例えば線形量 $`q:R^2\to R`$ のLaw $`q(v)^2=0`$ の普遍残差は
$`t_1^2z_1^2+2t_1t_2z_1z_2+t_2^2z_2^2`$ であり、交差項も生成元になる。
rank1の $`q(v)^2=q(v)`$ では $`t^2z^2-tz`$ の係数を取り、イデアルは $`(t)`$ となる。
これらは基礎環の基底上だけで等式を検査する条件と異なる。
またframeの第一座標を勝手に指定する $`t_1=1`$ は上の原始構文に入らない。
構造に切断 $`c`$ を宣言した $`q(c)=1`$ なら、$`h(c)=c'`$ により比較されるLawになる。

**定理6.10（構造のstack上の量・Lawの相対幾何）.**
定義6.9の構造の底、量の型、Lawから、準連接加群 $`Q`$ と
準連接代数 $`\mathcal C`$ を構成できる。
flat-fppf site、すなわち $`\mathcal B_\sigma`$ へflatかつ局所有限表示なschemeを対象とし
fppf被覆を用いるsite上では、残差は準連接イデアル
$`I\subseteq\mathrm{Sym}\,Q`$ を与え、$`\mathcal C=\mathrm{Sym}\,Q/I`$ である。
この包含を任意の試験射 $`b:T\to\mathcal B_\sigma`$ へ引き戻した加群射を $`\iota_b`$ と書くと、

```math
I_b=\mathrm{im}(\iota_b:b^*I\longrightarrow\mathrm{Sym}_{\mathcal O_T}(b^*Q)),\qquad
b^*\mathcal C=\mathrm{Sym}_{\mathcal O_T}(b^*Q)/I_b
```

である。一般の $`b`$ で $`\iota_b`$ の単射性は要求しない。
構造の上の量・Lawモデルの族は

**式(6.6)**

```math
\mathcal L=\mathrm{Spec}_{\mathcal B_\sigma}\mathcal C
 =\mathrm{Spec}_{\mathcal B_\sigma}(\mathrm{Sym}\,Q/I)
```

で表される。任意の試験scheme $`T`$ と構造 $`b:T\to\mathcal B_\sigma`$ への引戻しは
affineな $`T`$-schemeで、任意の $`T'\to T`$ 上の元の型の量と全Lawの充足を表す。
構成は被覆と生成子・関係表示の選び方によらず、量・関係・Lawの索引集合の有限性も要らない。

**構成と証明.**
分裂するaffine chartで、直和・tensor積・余核から表の $`Q_b`$ を作る。
任意の値加群への写像の普遍性により量の型と対応し、任意の表示から得る余核も同じ加群に一意に同型となる。
直和・tensor積・余核は任意の係数変更と可換するので、
$`Q_b\otimes_RR'\cong Q_{b|R'}`$ である。Hom加群とtensorの可換性は用いない。
構成した $`h_Q`$ とその合成則から、chartの重なりにdescent datumを得る。
重なりの射影はfppfであり、付録B.3の加群descentで $`Q`$ を降下できる。

任意の $`b:T\to\mathcal B_\sigma`$ に対しても、$`X_T=X\times_{\mathcal B_\sigma}T\to T`$ は
schemeのfppf被覆である。ここへchart上の $`Q`$ と比較を引き戻して降下することで $`b^*Q`$ を得る。
二段の引戻しの比較は、$`X_T`$ 上のtensorの結合同型から降下する。
これが全試験scheme上の準連接加群と係数変更の整合を与える。
独立な量もfppf層をなす。集合型では $`\mathcal O`$ の切断を生成子ごとに貼り、
線形・多重線形型では補題B.4によって写像を貼る。
関係を消す条件とLawは、任意の引戻し上で忠実平坦に検査できる。
したがってこの降下後の $`\mathrm{Hom}(b^*Q,\mathcal O_T)`$ も、元の量の型と一致する。

chart上の残差構成は、上で証明した比較式によって重なりで同じイデアルになる。
flatな射では像イデアルとイデアルのtensorが一致するため、
イデアルと包含写像を付録B.3でflat-fppf siteへ降下できる。
より具体的には、chart上の $`I_b`$ を加群として降下し、包含を加群射 $`\iota`$ として降下する。
flatな試験射ではこれは単射であり、イデアル層 $`I`$ になる。
任意の試験射上ではこの加群射の像を取る。
商代数の係数変更は補題B.3により

```math
(\mathrm{Sym}_RQ_b/I_b)\otimes_RR'
 \cong\mathrm{Sym}_{R'}(Q_b\otimes_RR')/
       \mathrm{im}(I_b\otimes_RR'\longrightarrow\mathrm{Sym}_{R'}(Q_b\otimes_RR'))
```

となる。この像は残差の全係数の像が生成するイデアルである。
式(6.5)のtensor後の生成族と同じ普遍入力を使えば、それは変更後のLaw idealそのものになる。
ゆえに商代数は任意の試験射で整合し、$`\mathcal C`$ を定める。
像の族を、任意の引戻しで単射を保つ加群の族と同一視することはしない。

付録B.7により $`\mathrm{Spec}_T(b^*\mathcal C)`$ を構成し、係数変更の同型で式(6.6)を得る。
その $`T'\to T`$ 上の切断は代数射 $`\mathcal C_{b|T'}\to\mathcal O_{T'}`$ であり、
対称代数の普遍性と残差評価の一致によって、元の型の量とLawの充足に両方向で対応する。
局所で互いに逆であり、量の層条件により大域でも逆である。
構造同型を含む射は、構造同型に加えてその比較で量が一致するものとなる。
構造を固定したfiberではその同型を恒等に固定するため、量モデルの集合を得る。

二つの被覆はfiber積による共通fppf細分で比較できる。
表示を交換した場合も、任意の値加群への普遍性が与える $`Q`$ の一意な比較と、
生成族に依存しない残差イデアルを使う。
descentの全忠実性からこれらの比較は一意に降下し、三つの選択の間でも合成に整合する。□

例えば非零環 $`k`$ に対し、$`k[a]`$ 上の $`I=(at)\subset k[a,t]`$ を $`a=0`$ へ引き戻すと、
加群の引戻しは零でないが、その包含からの写像は零になる。
この試験scheme上のLaw idealは像の0であり、商代数は $`k[t]`$ である。
これが上の定理で任意の係数変更に像イデアルを使う理由である。

固定集合を選べば、$`T=\mathrm{Spec}\,k`$ のfiberは第5章の定理5.4になる。
有限局所自由 $`E`$ 上の線形量では $`Q=E`$ であり、量の点は $`E\to\mathcal O`$ という線形汎関数である。
任意関数 $`|E(R)|\to R`$ を各係数で選び直す問題とは量の型が異なる。
後者では入力集合自体が変わるため、式(6.5)のtensor方式を持つかを別に調べる。

**問題6.11（一般の実現族の表示条件）.**
任意の小さい担体・宣言族と、定義4.1の原始実現方式 $`\sigma`$ を与える。
その係数的意味圏、同型groupoid、量の型を保持した上で、次を求める。

1. 各実現を被覆する有限frameまたは有限生成元の条件を原始担体から記述し、
   その成立部分がopenとなる場合には、重なりの実際の写像を構成せよ。
   自己同型が消えるmarkingとopen接着からschemeが得られる条件、
   自己同型を持つ場合のsmooth atlasとrepresentableな対角の条件を決定せよ。
2. 第4章のsupport profileが変わる族について、affine試験環上のcolimit、
   その被覆に関する層化、schemeまたはalgebraic stackによる表現を比較せよ。
   任意の試験schemeの局所族を表示するために、どのsupportの局所性が必要かを決定せよ。
   また局所splitなcopying対象をfppf stackへ拡張し、その対象・全射・表現条件を決定せよ。
   Zariski局所splitな対象はfppf descentで閉じない。実際、
   $`\mathrm{Spec}\,\mathbb C\to\mathrm{Spec}\,\mathbb R`$ はfppf被覆であり、
   $`\mathbb C\otimes_{\mathbb R}\mathbb C\cong\mathbb C\times\mathbb C`$ によって
   $`\mathrm{Spec}\,\mathbb C`$ は被覆上で二点の定数実現になる。
   しかし実数点を持たず、底が一点の $`\mathrm{Spec}\,\mathbb R`$ 上では定数二点と同型にならない。
3. 宣言・Lawを増やす逆系について、同じ有限frame上でのaffineな逆極限が
   独立な実現の全対象・全射を回復する条件を決定せよ。
   frame自体が変化する場合には、その逆極限またはind表示を構成せよ。
4. 各量の型について、固定索引の生成子・関係表示を作り、係数変更がそのtensorとなるか、
   構造同型とLaw入力の比較がどの原始式で与えられるかを決定せよ。
   この条件を満たす量には定理6.10を適用し、異なる型にはそのモデル関手に合う表示を求めよ。

有限個のsortの有限局所自由tensor実現については定理6.5・6.7が1を、
定義6.9の量については定理6.10が4を解く。
任意個の量とLawを同じ固定構造上へ加える場合は、第5章の無限変数多項式環がaffine表示を与える。
無限担体の全Homには定理4.6のsupportによる表示系がある。
これらの構成の対象・射・係数変更を保持して、一般の実現方式で必要な表示を調べる。

[第II部](../README.md#第ii部-実現の族とlawの幾何) · [共通記号](../notation.md) ·
[後続：意味を保つ変更の全体](../README.md#第iii部-意味を保つ変更の全体)
