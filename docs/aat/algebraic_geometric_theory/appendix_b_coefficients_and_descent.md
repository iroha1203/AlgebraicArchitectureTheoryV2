# 付録B 係数・affine構成・descent

第II部で使う代数的構成と局所からの組立てをまとめる。
環のSpecには素イデアルの位相と局所化による構造層を用いる。
準連接加群は、affine開集合 $`\mathrm{Spec}\,R`$ 上で加群 $`N`$ から作る層
$`\widetilde N`$ と同型になる加群層である。
基本開集合では $`\widetilde N(D(f))=N_f`$ とする。
これらの局所化は、分母を揃えることで層の一致と貼り合わせを満たす。

## B.1 係数とaffine構成

**補題B.1（開閉分割と冪等元）.**
可換環 $`R`$ の冪等元 $`e`$ と $`\mathrm{Spec}\,R`$ の開閉集合は
$`e\mapsto D(e)`$ で一対一に対応する。
有限な互いに素な開閉分割は、直交する冪等元の和1と対応する。

**証明.**
$`e(1-e)=0`$ なので各素イデアルは $`e,1-e`$ の一方だけを含み、
$`D(e)`$ の補集合は $`D(1-e)`$ である。
逆に開閉集合 $`W`$ に対して、$`W`$ 上の切断1と補集合上の切断0を貼り合わせる。
大域切断 $`R=\Gamma(\mathrm{Spec}\,R,\mathcal O)`$ の元 $`e`$ は局所的に冪等なので冪等で、
$`D(e)=W`$ となる。
同じ $`W`$ を与える冪等元は各局所環で同じ0または1だから等しい。
互いに素な分割では各積が局所的に0、和が局所的に1であり、大域でもそうなる。
逆方向も各素イデアルで読めばよい。□

**補題B.2（任意集合の多項式・対称代数・Spec）.**
小さい集合 $`L`$ に対し、$`k[t_l\mid l\in L]`$ は有限supportの指数
$`\nu:L\to\mathbb N`$ による単項式の自由 $`k`$-加群として構成できる。
積を指数の和で定めると、任意の $`k`$-代数 $`R`$ について

```math
\mathrm{Hom}_{k\text{-}\mathrm{Alg}}(k[t_l],R)\cong R^L
```

を得る。任意の $`k`$-加群 $`Q`$ に対しても、可換tensor代数
$`\mathrm{Sym}_kQ`$ は

```math
\mathrm{Hom}_{k\text{-}\mathrm{Alg}}(\mathrm{Sym}_kQ,R)
 \cong\mathrm{Hom}_k(Q,R)
```

を満たす。さらに任意の $`k`$-scheme $`T`$ と $`k`$-代数 $`B`$ に対し

```math
\mathrm{Hom}_k(T,\mathrm{Spec}\,B)
 \cong\mathrm{Hom}_{k\text{-}\mathrm{Alg}}(B,\Gamma(T,\mathcal O_T))
```

である。

**証明.**
各多項式の和と各単項式の積は有限なので、値の割当てを代入して環射を作れる。
任意の環射は生成元の像で決まるため、この構成は一意である。
tensor代数を $`u\otimes v-v\otimes u`$ の生成するイデアルで割ると対称代数を得る。
線形写像 $`Q\to R`$ はtensorを値の積へ送り、可換性によって商を経由する。
逆は次数1への制限である。

最後の主張では、環射 $`B\to\Gamma(T,\mathcal O_T)`$ を各affine開集合に制限する。
affine上で素イデアルの逆像と局所化の射によりscheme射を構成する。
重なりをaffine開集合で覆うと、同じ切断の制限を使っているので射が一致し、貼り合う。
逆にscheme射は関数の引戻しを与える。
affine上で互いに逆なので一般の $`T`$ でも逆となる。□

**補題B.3（係数変更と方程式）.**
任意の環射 $`R\to R'`$ に対し、直和、tensor積、余核、対称代数は、
それぞれの構成による自然な同型の下で係数変更と可換する。
$`A`$ が $`R`$-代数、$`I=(f_i)\subseteq A`$ なら

```math
(A/I)\otimes_RR'
 \cong (A\otimes_RR')/(f_i\otimes1\mid i).
```

**証明.**
直和の元は有限和なのでtensorの双線形関係と交換できる。
tensorの結合同型は純tensorの括弧を移す写像とその逆である。
余核は生成元を関係で割る構成であり、tensor後にも同じ関係の像で割る。
対称代数は補題B.2の普遍性を、$`R'`$-代数を試験対象として両側に適用するか、
tensor代数の生成元と可換性の関係を直接運ぶことで同型を得る。
最後の式も、両側の代数射が $`A\to C`$ と $`R'\to C`$ で $`f_i`$ を0へ送る対を表すことから従う。
任意の基礎環射について成立し、flatnessは用いない。□

この補題では、$`I\otimes_RR'`$ の $`A\otimes_RR'`$ への像を用いる。
その写像が単射であることは別の条件である。
原始の残差生成元を保持しておけば、任意の係数変更でその像のイデアルを作れる。

## B.2 忠実平坦な係数descent

環射 $`A\to B`$ が忠実平坦であるとは、$`B\otimes_A-`$ が完全であり、
$`B\otimes_A M=0`$ から $`M=0`$ が従うことをいう。
完全性と忠実性により、写像が単射・全射・同型であることをtensor後に検査できる。

$`B`$-加群 $`N`$ のdescent datumは、$`B\otimes_AB`$-線形同型

**式(B.1)**

```math
\theta:N\otimes_AB\xrightarrow{\sim}B\otimes_AN
```

で、三重tensor上で $`\theta_{12}\theta_{01}=\theta_{02}`$ を満たすものとする。
左辺の第一の $`B`$ は $`N`$ に、右辺の第二の $`B`$ は $`N`$ に作用する。
添字は $`N`$ を置く位置を示す。
datumの射は、この同型と可換する $`B`$-線形写像である。

**補題B.4（加群と全写像の有効descent）.**
忠実平坦な $`A\to B`$ について、$`A`$-加群の圏と $`B`$-加群のdescent datumの圏は同値である。
datum $`(N,\theta)`$ から得る加群は

**式(B.2)**

```math
M=\{n\in N\mid\theta(n\otimes1)=1\otimes n\},
\qquad B\otimes_AM\xrightarrow{\sim}N,\quad b\otimes m\longmapsto bm
```

で構成される。

**証明.**
$`\rho(n)=\theta(n\otimes1)`$ と置く。
線形性から $`\rho(bn)=(b\otimes1)\rho(n)`$ である。
cocycleを三つの係数を同じにする対角へ引き戻すと、そこでの同型 $`a:N\to N`$ は
$`a^2=a`$ を満たすので恒等である。よって

**式(B.3)**

```math
\mu\rho=\mathrm{id}_N,\qquad
(1\otimes\rho)\rho(n)=\sum_i b_i\otimes1\otimes n_i
\quad\left(\rho(n)=\sum_i b_i\otimes n_i\right),
```

ここで $`\mu(b\otimes n)=bn`$ である。第二式は $`n\otimes1\otimes1`$ でcocycleを評価した式である。

$`M`$ は $`\rho`$ と $`n\mapsto1\otimes n`$ の等化子である。
flatnessにより $`B\otimes_AM`$ は
$`B\otimes_AN\rightrightarrows B\otimes_AB\otimes_AN`$ の等化子となる。
式(B.3)の第二式から $`\rho(n)`$ はこの等化子に入り、
$`\beta:N\to B\otimes_AM`$ を定める。
第一式で $`\mu\beta=\mathrm{id}`$、$`m\in M`$ に対する
$`\rho(bm)=b\otimes m`$ で $`\beta\mu=\mathrm{id}`$ となる。
したがって式(B.2)は同型であり、同じ式でdatumとも整合する。

元の $`A`$-加群 $`M_0`$ から始めるときには、拡張加群 $`B\otimes_AM_0`$ の
二つの引戻しを係数因子の移動で同定する。
その等化子が $`M_0`$ であることを示すには

```math
0\longrightarrow M_0\longrightarrow B\otimes_AM_0
\rightrightarrows B\otimes_AB\otimes_AM_0
```

の完全性を示せばよい。
$`B`$ をもう一度tensorした列の最初の写像を
$`i'(b\otimes m)=b\otimes1\otimes m`$、次の差を
$`d'(b_0\otimes b_1\otimes m)=b_0\otimes b_1\otimes1\otimes m-b_0\otimes1\otimes b_1\otimes m`$ とする。
次数ごとの写像

```math
s_0(b_0\otimes b_1\otimes m)=b_0b_1\otimes m,\qquad
s_1(b_0\otimes b_1\otimes b_2\otimes m)=b_0b_1\otimes b_2\otimes m
```

は $`s_0i'=\mathrm{id}`$、$`s_1d'=i's_0-\mathrm{id}`$ を満たす。
したがって $`d'(z)=0`$ なら $`z=i's_0(z)`$ である。
よってtensor後の列は完全で、忠実平坦性が元の完全性を反映する。

datumの射は式(B.2)の等化子を等化子へ送るので $`M\to M'`$ を制限によって与える。
そのtensorは示した同型の下で元の射である。
逆に $`A`$-線形射のtensorはdatumと可換する。
この二構成も互いに逆で、恒等・合成を保つ。□

**補題B.5（有限局所自由性、tensorと演算）.**
補題B.4で $`N`$ が有限局所自由なら $`M`$ も有限局所自由である。
一定階数 $`n`$ も降下する。
tensor積、線形・多重線形演算、指定元、同じ型のtensor式の等号と、
それらを保つ全写像は同じdescentで降下する。

**証明.**
affine上の有限局所自由加群 $`N`$ は有限表示かつflatである。
これを分母払いで確認する。有限個の基本開 $`D(f_i)`$ 上の有限基底を取り、
分母を払った持上げを集めると $`B^r\to N`$ が得られる。
その余核は各 $`f_i`$ で局所化すると0なので0である。
実際、各元を消す $`f_i`$ の冪は単位イデアルを生成する。
kernelを $`K`$ とすると、各 $`K_{f_i}`$ は有限自由加群への分裂全射のkernelなので有限生成である。
その生成元の分母を払って集めれば同じ議論で $`K`$ も有限生成となり、有限表示を得る。
単射のtensor後のkernelも各 $`f_i`$ で0になるため、flatnessが従う。

次に忠実平坦な係数変更から有限生成性を降下する。
$`B\otimes_AM`$ の有限生成元をそれぞれ有限の純tensor和で書き、
そこに現れる $`M`$ の元の有限集合を取る。
それらが生成する部分加群を $`M'`$ とすると、$`B\otimes_A(M/M')=0`$ なので $`M=M'`$ である。
全射 $`A^r\to M`$ のkernel $`K`$ を取る。
flatnessによって $`B\otimes K`$ は $`B^r\to N`$ のkernelであり、
$`N`$ の有限表示性から有限生成である。
今の議論で $`K`$ は有限生成となり、$`M`$ は有限表示である。
任意の単射 $`L\to L'`$ を $`M`$ でtensorした写像は、さらに $`B`$ をtensorすれば
$`N`$ のflatnessによって単射となる。忠実性から元も単射で、$`M`$ はflatである。

有限表示かつflatな加群が局所自由であることも確認する。
各局所環 $`A_{\mathfrak p}`$ で、残差体上の基底を有限個の元へ持ち上げる。
Nakayamaの補題によりこれらは $`M_{\mathfrak p}`$ を生成する。
その全射のkernelは有限生成で、flatnessにより残差体でtensorしても左完全である。
残差体上では基底を選んだためkernelのtensorは0で、もう一度Nakayamaからkernelが0となる。
ここでNakayamaは、有限生成元の関係行列 $`I-C`$ の行列式が単元になることから従う。
有限表示により、この有限個の生成元と関係の等号はある $`D(f)`$、$`f\notin\mathfrak p`$ で成立する。
よって $`M`$ はその近傍で有限自由である。
忠実平坦射はSpec上で全射であり、残差体の拡大後も有限次元ベクトル空間の次元は変わらないため、
$`N`$ の一定階数が $`M`$ の階数になる。

affine上の有限局所自由加群は有限射影でもある。
実際、有限個の基本開集合上で基底と双対基底を選び、分母を払うと、
各被覆元の十分大きな冪を掛けた恒等写像が、有限個の写像
$`m\mapsto\lambda(m)v`$ の和になる。これらの冪は単位イデアルを生成するので、
係数付きで足すと恒等写像自身がその有限和になる。
この双対基底の式は有限自由加群からの全射に右逆を与え、射影性を示す。

tensor積のdatumは二つの $`\theta`$ をtensorして因子を並べ替えて作る。
補題B.3とB.4の同型により、その降下は $`M_1\otimes_AM_2`$ である。
演算はそのtensor積から出力加群へのdatumの射なので、補題B.4で一意に降下する。
指定元は $`A\to M`$ という線形写像として同様である。
tensor式の等号は、降下した二つの写像の差を $`B`$ でtensorして0になることから従う。
全ての構造保存射についても、同じ可換式を忠実性で検査できる。
写像に全射性を要求する場合は、その余核がtensor後に0になるかで判定できる。□

## B.3 層、chartと相対Spec

本部で使う係数の局所性は、Zariski開被覆とfppf位相である。
affine上のfppf被覆は、平坦で有限表示のaffine射の共同全射族で局所的に記述する。
有限部分族で覆う場合、対応する代数の有限積を $`B`$ とすれば元の環から $`B`$ への射は忠実平坦である。
ここでは「平坦かつ局所有限表示なscheme射は、任意のbase change後も開写像である」という
scheme論の標準定理を用いる。一般のfppf被覆をaffineな底へ制限し、各被覆元を
有限表示のaffine射となる開集合で覆う。その像は開集合で底を覆うので、
準コンパクト性により有限個を選べる。この細分に補題B.4を適用できる。

補題B.4を各affine開集合で使い、重なりで同じdatumから得る同型を貼り合わせると、
準連接加群のdescentを得る。
具体的には、選んだ有限細分から得る加群を元の各被覆元へ引き戻し、
さらに細分とのfiber積上で元の加群と比較する。その同型は補題B.4の全忠実性で一意に降下する。
二つの細分を選んだ場合も共通細分上の恒等から一意な同型を得る。
これらの一意性が重なりの一致と三重交差の条件を与える。
Zariski被覆については、加群層の切断を「局所切断の整合族」と定める直接の構成もできる。
この構成は各affineに制限すれば補題B.4の等化子と一致する。
補題B.5を適用すると有限局所自由加群、演算、全構造保存射のdescentを得る。
これが第6章の係数descentの根拠である。

**補題B.6（open chartの接着）.**
scheme族 $`(U_i)`$、open $`U_{ij}\subseteq U_i`$ と同型
$`\varphi_{ij}:U_{ij}\to U_{ji}`$ を与える。
恒等、両逆、三重交差のcocycleを満たし、重なりのopenもその同型で対応するとする。
このとき各 $`U_i`$ がopenとして埋め込まれるscheme $`M`$ を構成できる。
同じcocycleを持つ加群層とその写像も貼り合う。

**証明.**
$`\coprod_iU_i`$ の点を $`x\sim\varphi_{ij}(x)`$ で同一視する。
cocycleによりこれは整合する同値関係となり、同じ $`U_i`$ 内の二点を新たに同一視しない。
各 $`U_i`$ のopenをopenとする位相を入れる。
開集合 $`W`$ 上の構造層を、各 $`W\cap U_i`$ 上の関数で重なりで一致する族とする。
これは層で、$`U_i`$ への制限は元の構造層となる。
各点の局所環も元のchartの局所環なので、得られる空間はschemeである。
加群層も整合切断の族として作り、写像は成分ごとに作用させる。
局所的な可換式は大域でも成り立つ。□

**補題B.7（準連接代数の相対Spec）.**
scheme $`T`$ 上の準連接 $`\mathcal O_T`$-代数 $`\mathcal C`$ に対し、
affineな $`T`$-scheme $`\mathrm{Spec}_T\mathcal C`$ を構成できる。
任意の $`g:T'\to T`$ について

```math
\mathrm{Hom}_T(T',\mathrm{Spec}_T\mathcal C)
 \cong\mathrm{Hom}_{\mathcal O_{T'}\text{-}\mathrm{Alg}}(g^*\mathcal C,\mathcal O_{T'})
```

であり、この構成は任意のbase changeと可換する。

**証明.**
affine開集合 $`W=\mathrm{Spec}\,R\subseteq T`$ で $`\mathcal C|_W=\widetilde C`$ と書き、
$`\mathrm{Spec}\,C\to\mathrm{Spec}\,R`$ を取る。
$`D(f)\subseteq W`$ への制限は $`C_f`$ であり、そのSpecは元のSpecの対応するopenである。
二つのaffine開集合の交差を基本開集合で覆うと、この局所化の同型は合成に従う。
補題B.6で貼り合わせれば所期のschemeを得る。
局所的な環射の普遍性は補題B.2であり、その一意性から上の対応を貼り合わせられる。
base changeはaffine上で $`C\mapsto C\otimes_RR'`$ で構成され、局所化と交換するので大域でも交換する。□

fppf stack $`\mathcal B`$ 上の準連接代数の場合は、各試験scheme $`T\to\mathcal B`$ にこの構成を施す。
対象を構造 $`b/T`$ と代数射 $`b^*\mathcal C\to\mathcal O_T`$ の対、
射を代数射と可換する構造同型とすると、相対Specの族を得る。
底の構造 $`b`$ は $`\mathcal B`$ のstack性で降下する。
補題B.4による加群と写像、補題B.5による乗法・単位とその保存式のdescentから、
代数射も一意に降下する。したがってこれはstackであり、
構造 $`b`$ を固定したfiberは補題B.7のaffine $`T`$-schemeである。
第6章の相対Specはこの構成で定める。

[全体の構成](README.md) · [第II部](README.md#第ii部-実現の族とlawの幾何) · [共通記号](notation.md)
