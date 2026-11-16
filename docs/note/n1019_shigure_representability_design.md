# SHIGURE — AATの意味・量・変更から生成する代数幾何

SHIGUREの研究目的は、Atomから生じる意味と、意味を保つ変更の全体に幾何を与え、
変更の存在・組立て・障害・修復を、その同じ幾何から説明することである。
[研究の全体目標](../research_goal.md)に従い、対象を有限階数へ置き換えて
表現定理を得ることを主目標にはしない。

中心に置く構成は、**任意担体の状態と操作を複製・消去まで保持し、その上の量とLawから
相対的な座標環を生成すること**である。実装の変更は、非可逆な射も含めて扱う。
scheme、stack、ind表示、逆極限は、原始構造に応じて構成・判定する対象である。
一般のsheafに幾何の名前を与えるだけでは、この研究目的を達成したことにならない。

以下には直接計算による証明と、構成・形式化すべき主定理を区別して記す。
[G-149〜G-152](../../research/goals/README.md#draft人間の確認待ち)は主経路のdraftである。
有限局所自由加群のmoduli、診断値の合流、台帳分割の詳細は
[n1020](n1020_shigure_polynomial_specializations.md)に置く。これらは一般構成への
特殊化・比較として残す。[Issue #6359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)
は設計の発端を記録するメモであり、研究目的を決める条件には用いない。

## 1. 山頂：元の意味を回復する相対幾何

原始入力には、Atomの型と値、状態担体、実際の演算・関係、選択された量、
Lawの意味、文脈制限を置く。意味側の対象と射を先に定義し、恒等・合成を構成する。
表現scheme、atlas、表現同値、忠実性、descentの結論は入力に含めない。

目指す主定理は次の四部分からなる。

1. **意味の再構成。** 任意の小さい担体、有限arityの操作、関係、明示した部分操作を
   保ったまま、元の対象・全Hom・全有限操作語を回復する。量が同じという理由で
   異なる状態や構造を同一視しない。係数的意味がないpayloadも消さない。
2. **Lawからの幾何。** 同じ構造の上で量を動かす独立なモデルから、Lawの座標環と
   普遍量を生成し、相対affine schemeによる表現を証明する。変数、状態、Lawの個数に
   有限性を要求しない。一般のresidualがこの構成を持つかは、実際の式と評価から判定する。
3. **変更の幾何。** 構造を変える射、観測を保つ射、補助状態を導入・忘却する射を
   同じ意味圏に置き、射の空間と合成を幾何的に構成する。対象の同型類だけでは済ませない。
4. **大域的帰結。** 同じ射から局所変更、係数拡大へのlift、組立て障害、修復の自由を導く。
   全有限部分での存在と、一貫した大域変更の存在の差を特定し、有限計算が大域結論を
   与える条件も原始構造から証明する。

概念上は、原始データから構成した係数的実現ごとの構造のstackを $\mathcal B_\sigma$、量とLawの実現を
$\mathcal M$、観測を $o$ として

```math
 \mathcal M_\sigma=\operatorname{Spec}_{\mathcal B_\sigma}
       \bigl(\operatorname{Sym}_{\mathcal O}Q/I_{\rm Law}\bigr),
 \qquad
 \operatorname{Chg}_o(A,B)
   =\{h:A\to B\mid h\text{ が操作を運び }o_Bh=o_A\}
```

を構成する。最初の式は§3で構成する相対affine部分の定理であり、
任意のopaque residualを多項式とみなす記号ではない。
$\sigma$ は§3.2の係数的実現であり、有限階数を指定する記号ではない。
$\mathcal B_\sigma$ 自身の代数性は§4で別に証明する。非代数的な場合も元の対象を保持し、
必要な表示系と、通常のscheme・algebraic stackへ有効化できない理由を特定する。

## 2. 状態と操作を忠実に運ぶ

### 2.1 複製を捨てないcoalgebra

集合 $X$、可換環 $R$ に対して

```math
 C_R(X)=\bigoplus_{x\in X}Re_x,\qquad
 \Delta(e_x)=e_x\otimes e_x,\qquad \epsilon(e_x)=1
```

を置く。任意の集合写像 $f:X\to Y$ は $e_x\mapsto e_{f(x)}$ を定める。
$C_R(X\times Y)\cong C_R(X)\otimes_R C_R(Y)$ であり、
cocommutative・counital coalgebraの圏ではtensorが圏論的直積になる。
後者は[Barr, §5](https://math.mcgill.ca/barr/papers/coalgebra.pdf)の標準結果である。

この対応は、変数の反復を $\Delta$、変数の廃棄を $\epsilon$ に送る。
従って任意のmany-sorted cartesian theoryの有限式と等式を運べる。
例えばBool ANDの冪等性は $m\Delta=\mathrm{id}$ である。
自由加群上の全 $v$ に $m(v\otimes v)=v$ を要求すると失敗するが、
それは複製を忘れた別のLawである。有限性を加えることで修正する問題ではない。

回復は次の直接計算による。有限supportの $g=\sum_y a_ye_y$ がgroup-likeである条件は

```math
 a_y^2=a_y,\qquad a_ya_z=0\ (y\ne z),\qquad \sum_y a_y=1 .
```

したがって

```math
 \operatorname{Coalg}_R(C_RX,C_RY)
 \cong
 \operatorname{Hom}_{R}
   \left(\coprod_X\operatorname{Spec}R,\coprod_Y\operatorname{Spec}R\right).
```

各入力について有限clopen分割ごとに出力を選ぶ、という正確な対応である。
連結な非零環では出力は一つなので全ての集合写像を回復する。
特に $\mathbb Z$ 上で、元の全Homとの全単射がある。
全可換環でscalar extensionに自然なcoalgebra射の族も、その $\mathbb Z$ 成分で決まる。
零環では全担体が零になるため、その一点での忠実性は主張しない。

これは状態を量の値へ潰す構成ではない。predicate $P\subseteq X$ は部分coalgebra、
部分操作は実際のdomain $D\subseteq X$ と $D\to Y$ として保持する。
存在だけを要求するLawと、指定witnessを持つデータも区別する。

### 2.2 無限担体とtotality

出力が無限集合 $Y$ のとき、一行のBoolean graphのtotalityは

```math
 U=\bigcup_{y\in Y}D(e_y)\cong\coprod_Y\operatorname{Spec}k
```

で表す。冪等性・直交性だけでは「全ての出力がfalse」という余分な点が入る。
全ての有限queryを検査しても、この点は除去できない。

各入力 $x$ ごとに有限出力support $S_x$ を保持すれば、固定support profile上は
冪等元の有限和の方程式を持つaffine chartになる。全profileを含めると

```math
 \operatorname{Hom}(\Delta X,\Delta Y)(R)
 =\prod_{x\in X}\mathop{\rm colim}_{D\subset_{\rm fin}Y}\operatorname{Part}_D(R)
```

を回収する。全入力に共通する有限 $D$ を要求してはいけない。
$X=Y=\mathbb N$ の恒等写像がその反例である。
合成のsupportは $\bigcup_{y\in S_x^f}S_y^g$ であり、chart上で有限和により計算できる。
同じpointwise合成を全profile上で接続する。

この表示は、全profileを添字にするind-affineな表示系として構成する。
生のpro-schemeの射に一律に押し込めない。例えば $f(g(x))$ の評価で読む $f$ の行は
$g(x)$ に依存し、全モデルに共通する一つの有限query集合からは決まらない。

### 2.3 何を元のAATから回復するか

| 原始対象 | 回復の仕様 | 新しく証明すること |
| --- | --- | --- |
| Atom configuration | 担体、family、relation、identificationと実際のatom map | 元の述語と保存条件の回復、恒等・合成 |
| opaqueなpayloadと選択値 | 任意 $P$ と $p\in P$ を $\Delta P$ とその点で保持 | 値・射を回復し、未指定の演算意味を追加しない |
| total lens | get・putと三つのlens等式 | $v_0\in V$ の下で $K=\mathrm{get}^{-1}(v_0)$、$C\cong K\times V$、固定view上の全Homは $K\to K'$ |
| protocol | small execution category $P$、状態図式、観測 $O$ | $[P,\mathcal E]/O$ の全自然変換、path Law、非単射adapterを回復 |
| ring / module | nativeの演算と係数作用を別々に保持 | $C_R(\lvert M\rvert)$、$M\otimes_kR$、$\operatorname{Hom}_k(M,R)$ の比較 |
| G-124のgeometry・lens・protocol | 同じprimitive query・value・Hom | 係数側の表示から同じ読取りへ戻る可換図式 |

lensの同型は
$c\mapsto(\mathrm{put}(c,v_0),\mathrm{get}(c))$ と
$(k,v)\mapsto\mathrm{put}(k,v)$ で直接証明できる。有限性は不要である。
既存lens/protocolの有限担体は一般結果の特殊化とする。
viewも変える相対lens Homは、両viewに基準値があれば
$(K\to K')\times(V\to V')$ として回復する。空viewではgetのsourceも空になるため、
その対象・射を直接分類する。固定view版の定理で一般のview mapを捨てない。
Set上の分解・normal formには既存の
[GeneralRelativeLens](../../research/lean/ResearchLean/AG/RealizationReconstruction/GeneralRelativeLens.lean)
を再利用する。新しい義務はその全射を係数family・descent・幾何へ結ぶ比較である。

[ArchitectureObject](../../Formal/AG/Atom/ArchitectureObject.lean)は
StructureMaps・SelectedQuantitiesを型と値として保持するが、その内部の演算や係数作用は
指定していない。[ObjectAlgebra](../../Formal/AG/Atom/ObjectAlgebra.lean)の選択された
operationも、その全体に恒等・合成を供給する構造ではない。
従って型付きsemantic declarationの構成、既存データへの忘却、既存の各native圏に対する
全Homの再構成を新たに証明する。
opaqueな値を都合のよい有限加群へ読み替えることでは、この義務は放電されない。

## 3. 任意担体の上の量から、実際のschemeを生成する

### 3.1 独立な意味と座標環

まず構造 $S$ を固定する。quantity $q_j$ のdomain $D_j(S)$ は任意集合でよい。
意味側の入力は関数 $q_j:D_j(S)\to R$ である。
Lawは構造の操作からなるterm、quantityの評価、環演算、係数による有限式であり、
その全入力に対して等式を要求する。

```math
 Q_S=\bigoplus_j C_k(D_j(S)),\qquad A_S=\operatorname{Sym}_kQ_S
       =k[t_{j,x}\mid j,\ x\in D_j(S)] .
```

各Law $\ell$ の入力担体を $E_\ell(S)$ とする。
普遍量、operationのcoalgebra射、複製 $\Delta$ から、
residualの線形写像
$\rho_\ell:C_k(E_\ell(S))\to A_S$ を生成する。
$I_S$ はその全ての像が生成するidealである。

**相対表現の核となる命題。**

```math
 \{(q_j)\mid\text{元の全Lawを満たす}\}
 \ \cong\ \operatorname{Hom}_{k\text{-Alg}}(A_S/I_S,R)
 \ =\ \operatorname{Hom}_k(\operatorname{Spec}R,M_S),
 \quad M_S=\operatorname{Spec}(A_S/I_S).
```

証明は、各 $q_j$ を普遍変数の像にする環射を作り、termに関する帰納法で
元の評価と $\rho_\ell$ の評価の一致を示すことによる。
共有入力の複製もこの帰納法に含める。Lawfulであることとidealを零へ送ることは
この評価定理の帰結であり、左辺の定義には用いない。
状態数・quantity数・Law数・idealの生成数に有限性は不要である。
全環射と構文代入に対する自然性も同じ帰納法から証明する。

**通常のaffine代数幾何全体の回収。** 任意の可換k代数Sを構造とし、
量q:S→Rに加法・乗法・1・k作用の保存Lawを課すと、上の構成は
$A_S/I_S\cong S$、$M_S\cong\operatorname{Spec}S$ を与える。
元の環HomはSpecの反変な射として全て回復する。
有限生成性は不要であり、単なる離散点の埋込みに留まらない必須試験になる。
任意k加群Mについて線形な量q:M→Rを取れば、同じ構成はSym_k Mを回復する。

状態family $\Delta X=\coprod_X\operatorname{Spec}k$、量のparameter空間
$\operatorname{Spec}k[t_x]$、状態上の大域関数環 $k^X$ は異なる。
無限 $X$ の状態familyを $\operatorname{Spec}(k^X)$ に置換すると余分なprimeが入る。
また量は $\operatorname{Hom}(C_R X,R)$ であり、$C_R X$ 自身との同一視には
有限性が必要になる。ここで有限階数を密かに戻してはいけない。

### 3.2 構造も変動させる

まず二つの係数的実現を区別する。§2から作る $\mathcal B_{\rm copy}$ では
状態は局所定数であり、同じ離散operationの冪零方向の変形はない。
native module Mに対する $M\otimes_kR$、scalar sortのR、
その上の線形・多項式operationは別の係数的実現 $\sigma$ を作る。
これらは原始の係数作用・termから構成する。copyingの表示から自動的に出るとはしない。

両者の基本的な比較は
```math
 \iota_{M,R}:\Delta|M|(R)\longrightarrow M\otimes_kR,\qquad
 (e_i,m_i)_i\longmapsto\sum_i e_i(m_i\otimes1)
```
である。指定されたnative定数点はR=kで元のmに戻る。
非連結kではclopen分割に由来する追加の点があるため、全点での全単射とは言わない。
dual numbers上の $\iota$ は一般に同型でなく、線形familyには新しい微小方向がある。
全Rでcopying Homとlinear Homを同値とする要求は置かない。

係数的実現ごとに、native基点での対象・全Homの回復、原始操作とLawの保存、
係数自然性を証明する。これらの比較はデータのfieldとして受け取らない。
moduleの線形射、lens、protocolなどで個別の構成から一般化する。
F_p上の点ごとの $x^p=x$ はk[t]へのtensor extension後に全要素では成り立たない。
nativeのLawと全係数familyのLawを同一視せず、この不成立も検出する。

構造のstack $\mathcal B_{\rm copy}$ は§2の操作・関係・同型のchartとdescentから構成する。
各担体の局所split coalgebraをquasi-coherent moduleとして降下し、
$Q$、$\rho_\ell$、生成ideal $I$ を同じ比較射で降下する。
その後に
$\mathcal M=\operatorname{Spec}_{\mathcal B_{\rm copy}}(\operatorname{Sym}Q/I)$
を構成する。任意のscheme $T\to\mathcal B_{\rm copy}$ へのpullbackが
上の独立なquantity modelを表現するaffine $T$-schemeになることを証明する。
任意の内部sheaf担体がこの局所split表示を持つとは仮定しない。
内部モデルによる一般構成との比較は、対象と射を明示して証明する。
同じ構成は、quantity domainのcopying coalgebraを降下できる各 $\mathcal B_\sigma$ 上でも行う。
module自体を動かす幾何には、指定された係数的実現と§4の別の構成を用いる。

原始宣言にはquantity domain $D_j$ とLaw入力 $E_\ell$ のsort、
その上のtermを含める。構造保存射 $h:S\to S'$ はこの全てを運び、quantityを引き戻す。
座標環の向きは
$A_S\to A_{S'}$、$t_{j,x}\mapsto t_{j,h(x)}$ であり、
schemeの向きは $M_{S'}\to M_S$ である。
Lawの保存はこの写像がidealを運ぶこととして証明する。
意味を保つ変更には、この引戻しと $q=h^*q'$ という等式を同時に持たせる。
relationを保存するだけでは不十分である。例えばLawをPの補集合だけに課すと、
Pへ移る入力のLawが失われる。補集合を使う場合はそのdomainと保存写像も宣言する。
この条件を満たさない元のnative射hも削除しない。
quantity domainを運ぶhについては、一般に
```math
 Z_h=\{(q,q')\in M_S\times M_{S'}\mid q=h^*q'\}
```
という変更の対応空間を作る。これが全M_S'からの射のgraphになるのは、
Law入力を運ぶこと等からLawの引戻しを証明できた場合である。
例えばS={a}, P=∅からS'={b}, P'={b}へのrelation保存射では、
q(a)=0というLawはtargetにない。Z_hはq'(b)=0を切り出し、
元のhを残したまま、意味を保てる量の条件を正確に示す。

### 3.3 任意のresidualと係数的意味を接続する義務

[ArchitecturalEquationSystem](../../Formal/AG/Equation/Basic.lean)の
object-dependent residualは任意関数であり、有限式性はfieldにない。
その関数を§3.1の式と同一視するには、実際の式と全入力での評価一致を示す必要がある。

全native residualは、まずそのgraphとして§2に保持する。
Observableの $k$-代数構造があれば、固定native対象について
$\varepsilon(A)\otimes1\in\mathrm{Observable}\otimes_kR$ を構成できる。
これと、量を動かすfamily上のregular residualを混同しない。

係数的な追加構造が必要であること自体に、正確な反証がある。

- $k=\mathbb F_p$ では $t$ と $t^p$ が全native $k$-点で一致するが、
  dual numbers上では異なる。値tableだけでは微小変形が一意に決まらない。
- $\mathbb Q$ 上で0にだけ値1を返す関数は多項式ではない。
  $\mathbb A^1$ 上のregular familyとしての延長は存在しない。
- 全 $k$-代数に自然な操作 $R^n\to R$ は、普遍tupleにおける値から
  一意の多項式になる。従って多項式性はscalar familyの自然性から導ける性質であり、
  任意の集合操作に課す前提ではない。

この不足を単なる未解決事項の列挙にはしない。任意のnative担体D、任意集合X、
指定された量の読取り $q:D\to k^X$、任意residual $\varepsilon:D\to k$ に対して、
**全てのregularな係数拡張を分類する幾何**を構成する。
qをε自身へ選び直して問題を自明にすることはしない。
有限な単項式集合Fごとに係数 $b_m$ の空間を取り、
```math
 E_{\varepsilon,q,F}=
 \operatorname{Spec}
 k[b_m\mid m\in F]\big/
 \left(\sum_{m\in F}b_m m(q(d))-\varepsilon(d)\ \middle|\ d\in D\right)
```
とする。これは全native入力での一致を課したaffine schemeである。
Fの拡大では新係数を零にするclosed immersionを取り、
$E_{\varepsilon,q}=\mathop{\rm colim}_F E_{\varepsilon,q,F}$ を構成する。
Yonedaによる $\operatorname{Nat}(R^X,R)\cong k[t_x\mid x\in X]$ から、
$E_{\varepsilon,q}(k)$ は元のresidualと一致する全natural scalar extensionを正確に分類する。
式の次数・使用する座標を予め上限で切らない。
S点は、全S代数Rに自然な $R^X\to R$ で、native入力のSへの像に一致するものを分類する。
同じ量の読取りを持つ二つのnative対象でεが異なれば、その値を区別できないという
失敗をこの比較で記録する。Dそのものはcopying表示に保持する。

全入力の場合D=k^X、q=idでは、無限体kなら存在すれば一意、
有限体F_qでは同じnative関数の拡張の差は
$(t_x^q-t_x)_x$ に入る。これは各多項式が有限個の変数しか使わないことから証明する。
δ₀の不存在、有限体での非一意性は、この空間の具体的な性質として残る。
元のresidualのgraphを保持したまま、regularな拡張がないことも数学的成果にする。
一般の基礎環ではk点の不存在とschemeの空性を区別する。
例えばk=ℤ、q=id、ε(n)=n(n−1)/2には整数係数多項式の拡張がないが、
次数2の拡張chartはSpec ℤ[1/2]になる。

複数contextの拡張を独立に選ぶだけでは十分でない。
term substitution・restriction・operationとの可換性を普遍tupleで検査し、
同じsupport-profile chart上の係数等式として課す。
例えばF_p上で同じnative residualをtとt^pに延長した二contextは、
identity restrictionにもかかわらず係数familyでは可換でない。
互換な拡張のmoduli上に普遍residualを構成し、その零点familyを相対Specで作る。
これにより、拡張の非一意性も選択肢の幾何として扱う。
この全D・q・εの分類、coherence、nativeとの比較が未構成なら、G-150は未達である。

各Atom/Law familyの係数的実現には、このscalar分類、domain・witness、
ind表示・対応関係を接続する。
例えば有限supportの量は
$\mathop{\rm colim}_{F\subset_{\rm fin}X}\mathbb A^F$ であって、
全量の $\mathop{\rm lim}_F\mathbb A^F$ ではない。
「任意のsheafでよい」という結論で、この比較義務を終わらせない。

## 4. 通常のscheme・stackになる理由を導く

次の条件を、既に存在するatlasという入力で代用せず、原始宣言から導く。

| 原始構造から証明する条件 | 幾何的帰結 |
| --- | --- |
| 全自由度がquantity変数と方程式で記述される | 無限変数・無限Lawでもaffine scheme |
| 有限個のframeを持つ構造から、残りの宣言追加が相対affineになる | 構成したframe chart上の逆極限がaffineとして有効化 |
| 基底変更群が有限個のGL等のsmooth group scheme、全Lawが作用で保存される | 商の代数性を証明し、algebraic stackを得る |
| markingを保つ自己同型が自明で、overlapがopenとして生成される | schemeへの接着を証明 |
| 明示した有限supportが拡大に沿って変わる | ind表示を保ち、通常のschemeへの有効化を別に判定 |

有限frameがあることを、全AATへの適用条件として先に課してはいけない。
frameが存在する場合の正の定理と、その存在を妨げるnative構造を両方保持する。
有限個のdualizable module sortでは階数を固定せず、局所階数による成分と
全ての有限階数を含める。任意moduleをdualizableと宣言することはできない。

通常の対象に必ず収まるという主張には具体的反例がある。
独立した生成元付きline quotientを無限個持てば、対応するfamilyは
$\prod_{\mathbb N}\mathbb P^1$ になる。この積はalgebraic spaceではない
([Stacks 0CNH](https://stacks.math.columbia.edu/tag/0CNH))。
また無限階数自由加群の全自己同型を保つmoduliでは、恒等の一次変形が
$\operatorname{End}_k(k^{(\mathbb N)})$ を含む。
ここで用いるのはmoduleのtensor extensionによる係数的実現であり、
零の微小変形を持つ $\mathcal B_{\rm copy}$ ではない。
algebraic stackのstabilizerは体上で局所有限型である
([Stacks 04XQ](https://stacks.math.columbia.edu/tag/04XQ))ため、同じgroupoidの
通常のalgebraic stack表現はできない。

これらは対象を除去する理由ではなく、必要な幾何を区別する定理である。
一方、§7の無限protocolの変更空間は、通常のaffine schemeとして表現される。
「無限だからpro」「自己同型があるからalgebraic stack」という分類にはしない。

## 5. 変更・意味保存・二種類の局所性

観測 $o_A:A\to O$ と名前付き操作を固定する。
射 $h:A\to B$ が操作を運び $o_Bh=o_A$ を満たせば、全有限操作語 $w$ に対して

```math
 o_B(w_B(h(a)))=o_A(w_A(a))
```

となる。証明は語長の帰納法による。$h$ は非単射・非全射でもよい。
これは選択観測に関する意味保存であり、異なる $h$ の存在と対象同型は異なる。
観測を細かくすれば、この射の空間は縮む。

構造的な変更と、出力traceだけが一致するbehavioral equivalenceも区別する。
trace同値から構造保存射の存在を一般に推論しない。
操作語の翻訳、phaseの変更、stutteringが必要なら、それ自体をsignatureの射として
指定し、充足と合成を証明する。有限queryの一致を全語の一致と呼ばない。

全意味圏のnerveを使い、$N_n$ は $n$ 個の合成可能な変更のgroupoidとする。
比較の2-cellだけを同型とし、変更そのものを可逆にしない。
$N_n\simeq N_1\times_{N_0}\cdots\times_{N_0}N_1$ と合成のcoherenceを証明する。
純粋なmoduli groupoidだけでは、この構造は回復できない。

| 局所性 | 制限するもの | 構成する比較 |
| --- | --- | --- |
| AAT文脈 | 宣言、操作、Law、実際のwitness | 全Lawのsupportを含むcoverでの対象・射の組立て |
| 係数schemeの被覆 | coalgebra、quantity、module、同型 | 同じ実現と変更のeffective descent |
| 有限fragment | 実際のqueryへの制限、全体の一部分 | 元のモデルとの逆極限比較、totality・support条件の保持 |

この三つを同じ被覆とみなさない。両制限の可換性を構成する。
各Lawが有限fragmentに現れること、または明示したind条件として残ることが必要である。
合法な全体の有限片への像だけを集めると、有限support列から全ての列へ誤って拡大する。

## 6. 変更の障害と残る自由

平方零拡大、局所adapterの変更、有限fragmentからの延長は、別々のlift問題である。
同じchange space上の対応するfiberを定義してから比較する。
affine chart $B=k[V]/I$ では、原始Lawの残差と全syzygyから余接複体を構成する。
選んだ方程式のJacobianだけを、一般の完全な変形理論とはしない。

平方零liftの標準的な障害・torsor理論にはcotangent complexを使う
([Stacks 08S3](https://stacks.math.columbia.edu/tag/08S3))。
AAT側での仕事は、実際の操作保存・観測保存の残差が、その同じ障害類になることの証明である。
群oidでは自己同型を次数 $-1$、補正を0、defectを1に置く規約で比較する。

可算な有限fragmentの塔について、原始Lawから生成した複体を $D_n$ とする。
元の変更の複体と $R\!\lim D_n$ の比較を構成した後で、

```math
 0\longrightarrow\lim\nolimits^1 H^{q-1}(D_n)
 \longrightarrow H^q(R\!\lim D_n)
 \longrightarrow\lim H^q(D_n)\longrightarrow0
```

を適用する。これは[derived inverse limitの標準結果](https://stacks.math.columbia.edu/tag/07KV)である。
新しい義務は、その前にあるnative変更との比較と、同じ制限写像の生成にある。
可算cofinal towerを持たない場合には高次 $R^p\!\lim$ を含む比較を使う。

$q=1$ の $\lim^1H^0$ は各段の障害だけでは見えない整合の障害になる。
障害が零なら修復の全体は $H^0$ によるtorsor、自己同型は $H^{-1}$ に対応する
線形lift問題を扱う。非線形な変更全体を無条件に一つの加群へ置き換えない。
Mittag–Leffler性を原始構造から導けば、この追加障害は消える。
有限段階での決定には、さらに安定性または有限の証明規則を導く必要がある。
例えば射影塔 $\mathbb Z^n$ はMittag–Lefflerでも、その逆極限は一つの有限段では決まらない。

## 7. 通しの例：すべての局所で可能なprotocol変更が、大域では存在しない

### 7.1 Atom・操作・観測から全変更を決める

各 $n\in\mathbb N$ に状態 $S_n=\mathrm{Bool}\times\mathbb Z$ を持たせる。
観測は $o(b,z)=b$、操作は
$u_t(b,z)=(b,z+t)$ と $v(b,z)=(\neg b,z)$ である。
adapterは

```math
 h_n^a:S_{n+1}\to S_n,\qquad h_n^a(b,z)=(b,2z+a_n).
```

Lawは加法作用の等式、$v^2=1$、$u_tv=vu_t$、
$h_n^a u_t=u_{2t}h_n^a$、$h_n^av=vh_n^a$ とする。
これらは状態・操作・adapter Atomから定義でき、$a_n$ は明示したquantityである。

観測と全 $u_t$、$v$ を保つ写像は必ず
$\tau_c(b,z)=(b,z+c)$ となる。
実際、加法作用の保存から各 $b$ で $z\mapsto z+c_b$、$v$ の保存から
$c_0=c_1$ が従う。translationを変更の定義に仮定していない。
source $h^0$ からtarget $h^a$ への自然性は、正確に

```math
                    c_n-2c_{n+1}=a_n.                 \tag{*}
```

従ってこの方程式の解は、選んだ観測と全操作語を保ち、全adapterと整合する
native変更の全体そのものである。

### 7.2 同じ変更を表現するscheme

係数familyは $\mathrm{Bool}_R\times\mathbb A^1_R$ と全 $\mathbb G_a$-作用で作る。
射はBool_R上のG_a-equivariantなR-scheme射とし、flipも保存する。
上と同じ証明が全可換環で成り立つ。
$u_1$ だけを要求すると標数 $p$ で余分な写像が入るため、全作用を保持する。
これはnative hidden module ℤのtensor extension ℤ⊗R=Rと、明示した加法作用から
生成する係数的実現である。copying表示のΔℤをA¹と同一視していない。
R=ℤではnative全射も係数familyの全射も整数cによるtranslationに分類され、
基点で全Homを回復する。元の状態は $\iota_{\mathbb Z,R}$ で自然に送られる。

```math
 Y_a=\operatorname{Spec}B_a,\qquad
 B_a=\mathbb Z[c_0,c_1,\ldots]/(c_n-2c_{n+1}-a_n).
```

これは全変更を表現する通常のaffine schemeである。
有限段 $Y_{a,n}$ は最後の $c_n$ を自由に選ぶ $\mathbb A^1_{\mathbb Z}$ で、
$Y_a=\lim_nY_{a,n}$ となる。
斉次変更群は

```math
 G=\operatorname{Spec}\operatorname{Sym}_{\mathbb Z}(\mathbb Z[1/2]),
 \qquad G(R)=\lim(R\xleftarrow{\times2}R\xleftarrow{\times2}\cdots).
```

差を取ると $Y_a$ の二つの解は $G$ の元だけ異なる。
以下の被覆では局所解が存在するので、$Y_a$ は実際に $G$-torsorである。

### 7.3 有限部分でもZariski局所でも存在するが、整数上では存在しない

$a_{2j}=1,\ a_{2j+1}=0$ とする。
有限段では末尾 $c_n=0$ から後ろ向きに整数解を作れる。
全段の整数解があれば

```math
 3c_0+1=4^m(3c_{2m}+1)
```

が全 $m$ で成り立つ。従って $3c_0+1=0$ となり、整数解は存在しない。

さらに $U=D(2)$、$V=D(3)$ は $\operatorname{Spec}\mathbb Z$ の被覆である。
$U$ 上は $c_0=0$ から再帰できる。
$V$ 上は $c_{2j}=-1/3,\ c_{2j+1}=-2/3$ が全段の解になる。
重なりでの差の初項は $-1/3$ である。一方、

```math
 G(U)=\mathbb Z[1/2],\quad G(V)=0,\quad G(U\cap V)=\mathbb Z[1/6].
```

従って指定した組立て障害は

```math
 [-1/3]\in
 \check H^1(\{U,V\},G)=\mathbb Z[1/6]/\mathbb Z[1/2]
```

であり、零ではない。この被覆に対する類の位数は3である。
**全有限部分の修復可能性、係数の局所での全変更の存在、大域変更の不存在が、
同じnative protocolと同じscheme上で同時に成立する。**

### 7.4 余接複体・逆極限・実際の不整合が一致する

有限段の座標環は $\mathbb Z[c_n]$、遷移は $c_n\mapsto2c_{n+1}+a_n$ である。
[cotangentのfiltered colimit](https://stacks.math.columbia.edu/tag/08PL)から

```math
 L_{B_a/\mathbb Z}\simeq B_a[1/2][0].
```

また $\mathbb Z[1/2]$ の標準自由分解を双対化すると

```math
 C(R)=\left[\prod_{n\ge0}R
       \xrightarrow{\,d\,}\prod_{n\ge0}R\right],
 \qquad d(c)_n=c_n-2c_{n+1},
 \qquad C(R)\simeq R\operatorname{Hom}_R(R[1/2],R).
```

次数は0、1である。実際の変更は $d(c)=a$、障害は $[a]\in H^1C(R)$、
存在するときの全自由変更は $H^0C(R)$ である。
平方零liftの補正にも同じ複体をkernel係数で用いる。
これは任意の大きな変更が一般にcotangentで決まるという主張ではなく、
このaffineな操作保存問題では同じ線形写像が両方を計算するという比較である。

指定された類の来歴は、元のadapterから作る加群
```math
 E_a=(\mathbb Zz\oplus\bigoplus_n\mathbb Ze_n)/
       (e_n-2e_{n+1}-a_nz)
```
で固定する。有限段 $\mathbb Zz\oplus\mathbb Ze_n$ の単射な遷移から
$0\to\mathbb Zz\to E_a\to\mathbb Z[1/2]\to0$ を得る。
$Y_a(R)$ は $E_a\otimes R\to R$、$z\mapsto1$ というretractionの全体で、
$B_a\cong\operatorname{Sym}(E_a)/(z-1)$ となる。
この拡大類がtelescope分解で $[a]$ になる。
cotangentの同じ形だけからaffineな定数項を復元したことにはしない。

```math
 H^1C(\mathbb Z)=\lim\nolimits^1(\mathbb Z,\times2)
       \cong\mathbb Z_2/\mathbb Z,\qquad
 [a]\longmapsto\left[\sum_{n\ge0}2^na_n\right]=[-1/3].
```

最後の同型は、和が $d(c)$ を $c_0$ に送り、逆に和が整数なら
$c_n=(c_0-\sum_{i<n}2^ia_i)/2^n$ が整数になることから証明できる。
全射性は2進展開による。

Čechとの比較も同じ写像から作る。各次数でのlocalizationの完全列を積に取り、
$0\to C(\mathbb Z)\to C(\mathbb Z[1/2])\oplus C(\mathbb Z[1/3])
\to C(\mathbb Z[1/6])\to0$ を得る。局所解の差に対する接続写像は $[a]$ を返す。
$\mathbb Z[1/6]/\mathbb Z[1/2]\cong\mathbb Z[1/3]/\mathbb Z$
を経由すれば、上の $[-1/3]\in\mathbb Z_2/\mathbb Z$ と一致する。

**同じ非零類を実際の微小liftでも得る。**
普遍change map $d:\mathbb A^{\mathbb N}_c\to\mathbb A^{\mathbb N}_a$ を
$a_n=c_n-2c_{n+1}$ で作る。
$\mathbb Z[\epsilon]/(\epsilon^2)$ 上の基底 $a'_n=\epsilon a_n$ に対し、
mod εでの点c=0のliftを問う。liftは必ず $c'_n=\epsilon x_n$ なので、
その存在条件は正確に $d(x)=a$ となる。
relative cotangentを零点へ引いた複体は、次数−1、0に置く
$[\bigoplus\mathbb Z\xrightarrow{d^\vee}\bigoplus\mathbb Z]\simeq\mathbb Z[1/2][0]$、
$d^\vee(e_n)=e_n-2e_{n+1}$ である。defectを $a'-d(\widetilde c)$ と定めれば、
lift障害は上の $[-1/3]\in\operatorname{Ext}^1_{\mathbb Z}(\mathbb Z[1/2],\mathbb Z)$ である。
有限段のmapはsmoothでliftできるが、この全体のmapはformally smoothではない。
整数点のない固定fiberから架空の点へのpullbackを取らず、普遍familyの実在する零点で比較する。

係数変更は結論も変える。$\mathbb Q$ 上は $c_0$ を自由に選べ、
$\mathbb Z_2$ 上では上の周期解が唯一である。
斉次問題では $H^0C(\mathbb Z)=0$ だが $H^0C(\mathbb Q)=\mathbb Q$。
従ってflatな係数変更だけを理由に、無限積を含むコホモロジーのtensor比較を
同型としてはいけない。schemeのbase change自体は正しく存在する。

## 8. 既存AATとArchSigへ同じ写像で戻す

| 比較先 | 揃える対象・仮定・写像 | SHIGUREで追加するもの |
| --- | --- | --- |
| G-124 | 同じ担体、primitive query、全Hom、有限制限 | coalgebra/quantity表示からnative再構成への比較。totalityを保つ |
| G-126 | 操作語・観測、修復対象と許す射 | quotient repairと、指定adapter間の変更を別fiberとして比較 |
| SAGA | 実際のrepairのsheaf、cover、係数、matching/completeness | 原始変更からその入力を構成し、実際のmismatchと指定障害類を同定 |
| conormal | 元のideal、係数拡大、次数、補正の作用 | Law残差・全syzygyとcotangentの比較。§7では全計算を明示 |
| Atlas・K0/K1 | 同じLaw値label、台、比較射、C0–C6等 | 同じ診断がどの変更障害を検出するかを保存・反映定理にする |

G-126で同じsource上の商修復を組み合わせられることと、§7の指定adapter間の変更が
組み合わさらないことは矛盾しない。変更で保持する構造が違う。
この差を射のfiberの違いとして説明することが、新しい比較の一部になる。

[既存ArchSigの計算](../tool/archsig_v0_6_0_io/computations.md)には、
有限整数・有理数の解、指定されたČech類、局所組立てが既にある。
それを新機能として数えない。SHIGUREからの経路は次とする。

| 入力から理論への写像 | 有限に出せるもの | 答える問い |
| --- | --- | --- |
| 観測AtomとLaw式からprimitive declaration・評価写像を作る | 型と式、quantity座標、指定残差の来歴 | 何を同じ意味として保存するのか |
| 操作保存・観測保存からchange equationsを生成 | 候補変更、非存在の証拠、全補正のparameter | この変更が何によって可能／不能になるか |
| 有限coverの実際のadapterからmismatchを作る | 指定コホモロジー類と補正、比較射 | 局所修復を組み立てられるか |
| 原始Lawからnilpotent liftの方程式を作る | ある次数の障害と、次に必要な試験 | 一次では見えない干渉がいつ現れるか |
| fragmentの制限写像と安定性の証明を持つ | 有限段階で十分というcertificate | 有限計算からどこまで大域結論が出るか |

§7の全有限段は全て成功するので、有限実行を何回繰り返しても不存在は検出できない。
一方、周期的なLawの記述と上の $3c_0+1$ の証明を持てば、
全体の不存在に有限の数学的certificateを与えられる。
一般の無限入力に対する万能な有限判定手続きを主張するのではなく、
原始構造から有限証明へ降りる定理を研究する。
性能・実装済み機能・実務効果は、これらの数学的可能性とは別に検証する。

## 9. 研究分割と数学的な評価

| 主経路 | 責務 | 依存 |
| --- | --- | --- |
| [G-149](../../research/goals/G-149-aat-native-coalgebraic-reconstruction.md) | 任意担体・cartesian Law・全Homの回復、totality、既存native族との比較 | native source、coalgebraの標準構成 |
| [G-150](../../research/goals/G-150-aat-law-generated-relative-geometry.md) | 相対Spec、residual評価、構造変動、通常の代数性と有効化 | G-149 |
| [G-151](../../research/goals/G-151-aat-semantic-change-category.md) | 非可逆変更、観測、nerve、二つのsite、SAGA等への実写像 | G-149・G-150 |
| [G-152](../../research/goals/G-152-aat-coherent-repair-effectivity.md) | native修復とderived limit、§7のscheme・Čech・cotangent一致、有限certificate | G-150・G-151 |
| [G-139〜G-148](n1020_shigure_polynomial_specializations.md#9-goalの分割と証明経路) | 有限局所自由model、値診断、有限次数、台帳例の特殊化 | 各カードの依存に加え、主経路への比較 |

coalgebraへの集合の埋込み、Sym/Spec、quotient stack、cotangent、Milnor列は標準数学である。
それらの存在や用語の追加に新規性を置かない。
研究の核は、AATの実際の操作と全Homを失わない同じ構成から、
量のscheme、変更の空間、指定された障害類、計算可能な特殊化までを導き、
表現の変更にもその比較を自然にすることである。

数学的非自明性を問う試験は、§7の「全有限段・Zariski局所で存在、大域で不存在」を
元の全変更について示せること、およびその同じ指定類を加群拡大・実際の微小lift・Čechから
回復できることに置く。加えて、G-151の非可逆射を含む全変更と合成の比較を必須にする。
§7の変更自体は全てtranslationで可逆である。
非可逆な必須例にはV=Boolとしてlensのhidden担体の忘却 $K\times V\to V$ を使い、
get/put保存と、$|K|>1$ なら同型でないことを同じ射の幾何で示す。
既存の有限行列に任意の意味を後付けするだけでは、この試験を満たさない。

論文化では、一般再構成・相対表現・変更の比較を主定理とし、§7を一貫した証人にする。
独創性の最終判断には、coalgebraic semantics、moduli of algebraic structures、
refinement mappings、deformation of diagramsとの比較と、一般定理の証明が必要である。
この設計稿だけで証明完了・形式化完了・論文としての新規性確定とはしない。
全native residualの拡張空間と元のgraphの比較、係数的実現の比較、表示独立性は
主経路の固定義務であり、未構成のまま全カードを完了扱いにはしない。
