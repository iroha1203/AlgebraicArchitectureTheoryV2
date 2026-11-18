# G-141-aat-coherent-repair-effectivity — 変更の障害・修復・有限判定

- `id`: G-141-aat-coherent-repair-effectivity
- `status`: `draft`
- `research mode`: `target-theorem`
- 関連メモ: [#6359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。実行用tracking Issueはactive化時に定める。
- 設計: [n1019 §6–8](../../docs/note/n1019_shigure_representability_design.md)、[n1020 §13・15–16](../../docs/note/n1020_shigure_polynomial_specializations.md#semantic-lift)
- 依存: G-139・G-140。診断への比較はG-142が本カードの実修復から構成する。

意味を保つ変更について、その存在・組立ての障害・全修復と残る自由を同じ原始Lawから
導く。有限表示の微小liftと無限diagramの大域化を比較し、有限計算から結論してよい
条件を証明する。syzygy、cotangent、Čech、逆極限はこの一つの到達像を支える構成である。
G-140の条件付きfiberを使い、保存条件と評価条件から全候補・不存在の証拠・残る自由を計算する。

## 固定target

### A. 原始変更とderived inverse limit

G-140の変更を実際のfinite fragmentへ制限する射を構成する。
線形lift問題では、原始operation/Lawの全syzygyから
自己同型を−1、補正を0、defectを1とする複体$`D_F`$を作る。
元の変更の複体と$`R\!\varprojlim_F D_F`$の比較を構成し、同値となる条件を
原始support・totality・cochain制限から証明する。

可算cofinal towerではMilnor列を、一般の添字では高次$`R^p\!\varprojlim`$を用いて
有限段の障害と全体の障害を比較する。
有限段存在から全体存在へ進める条件を、この比較から導く。
非線形な変更全体はG-140のfiberとして扱い、線形lift問題から加群の複体を構成する。

任意の小さいadapter diagramを持つ加法作用protocolについて、次の一般定理を構成する。
状態はpublic担体とhidden moduleの積、保持する操作はhidden側の全平行移動と
public側の指定された非空な推移的作用、観測はpublic成分とする。
各vertexのpublic担体・hidden module・作用と、各adapterの線形部$`L_e`$をsource/targetで固定する。
category上のdiagramには$`L_{fe}=L_fL_e`$と$`a_{fe}=a_f+L_fa_e`$を課す。
全意味保存射がtranslationへ分類されることを証明し、
adapterの線形部・定数項から実際の補正複体を生成する。
source aからtarget bへの式は$`c_t-L_ec_s=b_e-a_e`$とする。
moduleやpublic担体も変える射はG-140の全変更で扱い、固定した担体上でtranslation分類を得る。
scheme表示を使うfamilyでは、元の任意moduleの表示とbase changeを明示する。
n1019 §7はhidden moduleが$`\mathbb Z`$の必須例とする。

### B. 一つのnative例の全比較

$`\mathrm{Bool}\times\mathbb Z`$、全$`u_t`$、flip v、観測Bool、$`h_n^a(b,z)=(b,2z+a_n)`$を原始入力とする。
全native変更の分類から$`c_n-2c_{n+1}=a_n`$を導く。
全係数環のfamilyでは$`\mathrm{Bool}_R\times\mathbb A^1_R`$と、$`u_{1}`$を含む全$`\mathbb G_a`$作用への等変性を使う。

次を同じ対象・写像で証明する。

- $`Y_a=\mathop{\mathrm{Spec}}\nolimits \mathbb Z [c_{0},c_{1},\ldots ]/(c_n-2c_{n+1}-a_n)`$が全変更を表現する。
- 有限$`Y_{a,N}\cong \mathbb A^{1}`$、遷移$`c_N=2c_{N+1}+a_N`$、$`Y_a=\varprojlim Y_{a,N}`$。
- 斉次変更群$`G=\mathop{\mathrm{Spec}}\nolimits \mathop{\mathrm{Sym}}\nolimits_{\mathbb Z} (\mathbb Z [1/2])`$と、解がある場合の自由推移的作用。
- $`L_{B_a/\mathbb Z }\simeq B_a[1/2][0]`$、および実Law複体
  $`C(R)=[\prod R\to \prod R]`$、$`d(c)_n=c_n-2c_{n+1}`$と$`\mathop{\mathrm{RHom}}\nolimits_R(R[1/2],R)`$との比較。
- $`C(R)\simeq R\!\varprojlim C_N(R)`$、$`H^{1}C(R)\simeq \mathop{\mathrm{lim}}\nolimits^1(R,\times 2)`$。
- 平方零liftの補正とその障害が同じ複体のkernel係数版から得られる。

原始adapterから$`E_a=(\mathbb Z z\oplus\bigoplus\mathbb Z e_n)/(e_n-2e_{n+1}-a_nz)`$を作り、
$`0\to \mathbb Z z\to E_a\to \mathbb Z [1/2]\to 0`$、全Rでのtensor後の完全性を証明する。
$`Y_a(R)`$を$`z\mapsto 1`$のR-linear retractionの全体と同定し、
$`B_a\cong \mathop{\mathrm{Sym}}\nolimits(E_a)/(z-1)`$と、拡大類$`[a]`$の同定を構成する。
Čechの符号はretractionの差を規約として固定する。

大きな変更の存在とcotangentによる微小liftを、それぞれのfiberとして定める。
この例では同じaffineな原始方程式が両方を計算することを比較定理にする。

### C. 非零障害とZariski局所修復

$`a_{\mathrm{even}}=1`$、$`a_{\mathrm{odd}}=0`$とする。全有限段の整数解を構成し、
$`3c_{0}+1=4^m(3c_{2m}+1)`$から全体の整数解不存在を証明する。

$`D(2)`$では$`c_{0}=0`$から再帰、$`D(3)`$では周期解$`(-1/3,-2/3)`$を構成する。
これらが全無限diagramの変更であることを検査する。
$`G(D(2))=\mathbb Z[1/2]`$、$`G(D(3))=0`$、$`G(D(6))=\mathbb Z[1/6]`$を計算し、
指定Čech類$`[-1/3]`$の非零性と位数3を証明する。

複体のlocalization短完全列から接続写像を構成し、この類が
$`[a]\in \mathop{\mathrm{lim}}\nolimits^1(\mathbb Z ,\times 2)\cong \mathbb Z _{2}/\mathbb Z`$の同じ$`[-1/3]`$になることを証明する。
$`\mathbb Z [1/6]/\mathbb Z [1/2]\cong \mathbb Z [1/3]/\mathbb Z`$を経由する。
$`\mathbb Z [1/6]`$から$`\mathbb Z _{2}`$への単位的環射は、2の可逆性の相違により存在しない。
$`\mathbb Q`$上の全解と$`\mathbb Z _{2}`$上の唯一の解も構成する。

さらに普遍map $`d:\mathbb A^{\mathbb N}_c\to\mathbb A^{\mathbb N}_a`$、$`a'_n=\varepsilon a_n`$を持つ$`\mathbb Z [\varepsilon ]/\varepsilon ^{2}`$上の基底と、
$`\bmod\varepsilon`$での点$`c=0`$を構成する。liftが$`c'=\varepsilon x`$、$`d(x)=a`$と同値であることを証明する。
relative cotangentの零点pullbackを次数−1,0のtelescope複体から計算し、
$`\mathrm{defect}=a'-d(\widetilde c)`$の規約で、同じ非零$`[a]`$が実際の平方零lift障害になると示す。
有限stageのsmoothnessと、全体のformal smoothnessの不成立を同じmapで比較する。

$`H^{0}C(\mathbb Z )=0`$と$`H^{0}C(\mathbb Q )=\mathbb Q`$から、$`C(\mathbb Z )\otimes \mathbb Q \to C(\mathbb Q )`$および
$`H^{0}C(\mathbb Z )\otimes \mathbb Q \to H^{0}C(\mathbb Q )`$が同型でないことを示す。
原因は$`(\prod \mathbb Z )\otimes \mathbb Q \to \prod \mathbb Q`$の非同型である。
flat tensor自体は核と交換する。schemeのbase changeとも区別する。

### D. 有限計算と解空間の探索の十分性を証明する

Mittag–Leffler性で$`\mathop{\mathrm{lim}}\nolimits^1`$が消えることと、有限段階で全結論が決まることは別に証明する。
原始presentationから安定性・有限生成性・再帰的な構造を導く具体的な十分条件を与える。
条件を満たす場合に、有限の証拠から全変更の存在・不存在・自由を結論する比較を構成する。
周期的adapter族について、有限個の遷移式から全段の不変式を導くcertificateを作る。

G-140 Eの$`F_{a,H,P}`$について、次の有限計算への特殊化を原始変換式から構成し、
出力の変更としての正しさ、指定した域での全解の回収、witnessの復元を証明する。
各算法の適用には、原始表示から有限個の候補係数と有限個の検査式を有効に生成し、
その生成の停止性と、検査式が全Law・全操作語の保存条件・評価条件に同値であることを証明する。
有限表示を直接コンパイルする場合と、無限表示から安定性・帰納法等により有限還元を導く場合を分ける。
後者でも、有限式系・比較同値・停止性を原始入力から構成し、判定結果の正しさを導く。

1. 有限体上で上記の有限還元を持つ表示について、生成した検査式を満たす全候補を列挙する。
   保存方程式は全操作語の評価定理から生成する。
2. 整数・有理数上で上記の有限還元がaffine方程式を生成する場合、全解のparameter表示と不存在のcertificateを作り、
   許す変更域・固定部分・原始操作への復元を同じ写像で証明する。
3. $`\mathbb Q`$上の有限多項式chartと有限個の等式・可逆条件では、$`ug-1=0`$による可逆条件の表示、
   ideal所属の検査証拠、代数閉包上の空性の判定を構成する。
   原始操作からchartと式を生成し、ideal包含条件が定める実際のlocusを計算する。
4. 同じ有限表示から評価parameterへの射について、消去と開条件の分岐から幾何点での
   実際の像を構成可能集合として計算し、各評価条件の全fiberと比較する。
   $`xy=1\to x`$の像$`D(x)`$と閉包$`\mathbb A^{1}`$を区別し、像の点に存在する変更witnessを保持する。

schemeの表示と指定係数域の点の探索を区別する。$`x^{2}+1=0`$の$`\mathbb Q`$点と代数閉包の点、
無限fragmentでのB・Cを必須の識別例にする。
順序付き評価条件では、比較する評価と順序を入力に保持し、その順序によって解を比較する。

候補の有限性と有限還元の有効性を区別する必須反例として、$`\mathbb F_2`$上の一係数$`c`$と
固定列$`a_n\in\mathbb F_2`$に対するLaw $`a_nc=0`$（全$`n\in\mathbb N`$）を用いる。
$`c=1`$が解である条件は全$`a_n=0`$であり、有限個の値を読む検査では、全零列と
未検査位置だけが1の列を区別できない。有効列に限っても、$`a_n`$を指定機械が$`n`$段以内に
停止した場合の指示値とすれば、全解を返して停止する一様な算法から停止問題の判定器が作れてしまう。
この反例と、生成idealの有限生成性だけではその無限表示からの有効な有限還元が従わないことを証明する。
全変更関手の定義と分類はこの反例も含めて保持し、有限算法が適用できる場合を構成的に特定する。

原始表示からの候補・方程式・証拠の生成と、有限解から操作モデルへの復元を本targetで証明する。
非線形な制約、高次lift、無限族についても同じ比較を構成し、
それぞれ有限計算が十分になる条件と、不十分になる反例を保持する。

### E. 有限表示の実現liftと合法な局所修復

可換環k、有限個の演算・Lawを持つn1020 §3の原始表示P、k代数R、独立な実現
$`x\in \mathop{\mathrm{Sem}}\nolimits_P(R)`$、平方零拡大$`R' \to R`$とkernel Mをこの順に量化する。Lawを忘れた
smooth ambient Yを原始表示から構成し、affine test上でのambient liftの存在を証明する。
基底chartでは$`B=k[z_{1},\ldots ,z_n]`$、原始Lawの全成分$`f_{1},\ldots ,f_r`$、$`J=(f)`$、$`A=B/J`$とし、
全syzygy $`S=\ker (B^r\to J)`$から$`N=J/J^{2}`$の表示と次の複体を生成する。

```math
D^0=M^n\xrightarrow{\mathop{\mathrm{Jac}}\nolimits(f)(x)}D^1=M^r
 \xrightarrow{d^1}D^2=\prod_{s\in S}M,
\qquad(d^1r)_s=\sum_i s_i(x)r_i.
```

原式の恒等式から$`d^{1}d^{0}=0`$と$`\ker  d^{1}\simeq \mathop{\mathrm{Hom}}\nolimits_R(N\otimes _A R,M)`$を証明する。
有限syzygy生成族を使うときは生成性と$`H^{0}`$・$`H^{1}`$の比較を証明する。
ambient lift $`\widetilde z`$の残差$`r=f(\widetilde z)`$から$`o_P\in H^{1}(D)`$を構成し、liftの変更則
$`r(\widetilde z+\delta )=r(\widetilde z)+d^{0}\delta`$、$`o_P=0`$と実際のlawful liftの存在の同値、非空な全liftへの
$`H^{0}(D)`$の自由推移作用を同じ加群・演算・Lawへ戻して証明する。

Yのideal sheafを$`\mathcal J`$、$`E_x=x^*\Omega_{Y/k}`$、$`N_x=x^*(\mathcal J/\mathcal J^2)`$として

```math
\bar D=[\mathop{\mathrm{Hom}}\nolimits_R(E_x,M)\to\mathop{\mathrm{Hom}}\nolimits_R(N_x,M)]
```

を構成する。単一chartに入らないxも含め、
chartのD、$`\bar D`$、$`R\mathop{\mathrm{Hom}}\nolimits_R(Lx^*L_{M_P/k},M)`$の次数0・1と指定障害を同定する。
$`N_x`$は一般の加群として扱う。Noetherian係数・有限表示の系では、有限principal
affine cover上の準連接性、Homの局所化、Čech totalizationとの比較を証明する。
G-139の表現定理は任意担体・任意Law族を対象とし、この系ではそのNoetherian係数・有限表示への特殊化を使う。

原始代入とLaw導出$`u:P\to P'`$から$`\rho :\mathop{\mathrm{Sem}}\nolimits_{P' }\to \mathop{\mathrm{Sem}}\nolimits_P`$を作り、$`x\in \mathop{\mathrm{Sem}}\nolimits_{P' }(R)`$と
指定された$`y' \in \mathop{\mathrm{Lift}}\nolimits_P(\rho x,R' )`$に対する$`\mathop{\mathrm{Lift}}\nolimits_u(x,y' )`$を独立に定義する。
ideal・conormal・微分・syzygyの比較から$`F_u=\mathop{\mathrm{Cone}}\nolimits(\bar D_{P'}\to\bar D_P)[-1]`$を構成し、
Law残差と$`\rho`$の像の差から$`o_u\in H^{1}(F_u)`$を得る。$`o_u=0`$と指定liftの存在、全解の
$`H^{0}(F_u)`$-torsor分類、恒等・合成・拡大の射・表示変更との自然性を証明する。

affine Law $`Lz-b`$、基準状態p、変更可能域Hについて、実修復集合の非空性を
$`b-Lp\in L(H)`$、全解を$`\ker(L\vert_H)`$のtorsorで特徴づける。非線形Lawの平方零修復は
原始Jacobianを使う。文脈ごとのHは変更可能な宣言から生成し、観測式の全参照が
所属する被覆と、その交差上で可換な原始代入から合法な修復係数を生成する。
制限、作用、matchingから実修復への組立てを証明する。$`T\mapsto X+Y`$を$`\{X\}/\{Y\}`$だけに
分ける不適合例では、$`\mathbb Q [\varepsilon ]/\varepsilon ^{2}`$上の合法差分$`(\varepsilon ,-\varepsilon )`$を局所係数0へ制限できず、
観測を落とすと$`(\varepsilon ,0)`$も組み立つことを示す。全参照を含む合併被覆で適合性を回復する。

全多重交差を持つ宣言被覆から自由な変数・Law残差のČech total complex $`T_{\mathrm{raw}}`$を作る。
各宣言の支持がfull simplexであることから$`H^{0}(T_{\mathrm{raw}})\simeq \ker  d^{0}`$、$`H^{1}(T_{\mathrm{raw}})\simeq \mathop{\mathrm{coker}}\nolimits  d^{0}`$を
導き、全大域syzygyから$`0\to H^{1}(D)\to H^{1}(T_{\mathrm{raw}})\to \prod _{s\in S}M`$の完全性を証明する。
実残差が右写像の核へ入り、その逆像が$`o_P`$になること、細分化との可換性も含める。
K0/K1のincidence生成とは同じ支持で比較する。微分・syzygyを持つ複体との同型には
それらの比較も構成し、G-142の同じadapter族で診断比較を証明する。

conormal比較では全表示の普遍ambient Bとprincipal-open siteを固定する。
G-139で構成する普遍equation systemのObservableとLaw idealを$`B_s`$、$`J_s`$へ同定し、
[Raw.shortComplex](../../Formal/AG/SemanticRepair/Conormal/LawGeneratedIdealPowerShortExact.lean)を
そのsiteへ制限して、$`(J^{2})_s=(J_s)^{2}`$とZariski層化から標準conormal列へ同定する。
実現xで引き戻す前の普遍ambientにおいて$`J/J^{2}`$を作る。
ambient lift $`B/J^{2}\to R'`$の制限$`\kappa :J/J^{2}\to M`$について、$`\kappa =0`$と同じliftが$`B/J`$を経由すること、
選択差を除いた$`[\kappa ]=o_P`$を証明する。section liftと実現liftはこの写像で比較する。
宣言の忘却とZariski制限の比較では、共有xを保って$`xy-1`$を零へ送る
$`\mathbb Q [x,y]\to \mathbb Q [x]`$の不存在を指定例として証明する。

### F. 全Artin試験・初回障害・有限上界

任意の可換環k上で、同じ型・階数・生成元を持つOへ有限の補助演算
$`Y_j=F_j(O,Y_{1},\ldots ,Y_{j-1})`$と追加Law $`G_\alpha =0`$を置いてPを作る。原始代入による消去から
残差$`\bar G_\alpha`$、ideal sheaf $`\mathcal J _u`$を生成し、全Rで$`\mathop{\mathrm{Sem}}\nolimits_P(R)`$をその零点へ自然に同定する。
marked実現の閉埋め込み、Realのfull faithfulな関手・essential image・自己同型群の
同定を証明する。追加Lawが空なら全Rで同値になる。

体k、有限表示O・P、$`x\in \mathop{\mathrm{Sem}}\nolimits_P(k)`$、$`a=u^*x`$について$`A=\mathcal O _{M_O,a}`$、m、$`J=(\mathcal J _u)_a`$を作る。
剰余体k、極大ideal $`n_R`$に$`n_R^{r+1}=0`$を課す全局所Artin k代数上のpointed deformationに
ついて、比較が自然同値 ⇔ $`J\subseteq m^{r+1}`$ ⇔ 普遍観測変形$`A\to A/m^{r+1}`$がliftする、を
全$`r\ge 0`$で証明する。普遍商のArtin性も有限表示から証明する。
$`J\ne 0`$なら$`\nu=\max\{n\mid J\subseteq m^n\}`$、$`J=0`$なら$`\nu =\infty`$とし、Krull交叉から最大値、初回失敗$`r=\nu`$、
全次数での同値 ⇔ $`J=0`$ ⇔ aのあるopen近傍での同型を導く。全R上の同値は$`\mathcal J _u=0`$で
判定する。曲線jetや有限サンプルによる試験とは量化を区別し、係数を動かすjet functorも
含めてn1020 §10・15の先行理論と比較する。

有限$`\nu`$の普遍拡大$`A/m^{\nu +1}\to A/m^\nu`$とkernel $`I=m^\nu /m^{\nu +1}`$から、
$`\kappa _u:J/J^{2}\to I`$、$`f\mapsto f\bmod m^{\nu+1}`$を構成し、Eの指定観測liftの非零障害へ送る。
$`\nu \ge 2`$では観測liftを変えるderivationもJを消すので、そのP実現自体のlift不存在を示す。
$`\nu =1`$では指定観測方向の不成立を結論し、基点の定値liftと区別する。
原始tensor残差と同型の共有演算$`Z_\alpha`$を持つ二文脈$`Z_\alpha =\bar G_\alpha  / Z_\alpha =0`$を作り、
任意の指定観測liftで局所liftを構成する。全syzygyから$`\mathop{\mathrm{Hom}}\nolimits_{A/J}(J/J^{2},I)\to I^q`$の
単射と像を構成し、$`\kappa _u`$を実際の共有部の差へ送り、その零性と合法修復をEへ同定する。

chart、改名、相互導出を持つ冗長Law、定義だけの補助演算の追加・消去に対して
J、$`\nu`$、$`\kappa _u`$と比較を自然にする。F冒頭の型のreading u,vの合成について、追加idealの
逆像から$`\nu(vu)=\min\{\nu(u),\nu(v)\}`$を対応する点の局所環で証明する。
pointed Realは還元同型を持つgroupoidとして定義し、Artin環上の生成元のliftから
同じ検出次数を比較する。生成元数$`m_v\ge n_v`$と選択を変えても$`\nu`$とpointed Realの判定は
一致し、指定観測liftの相対fiberは空またはcontractibleになることを証明する。

自由観測chart $`k[z_{1},\ldots ,z_d]`$では原始式の積で加算、和で最大を取り、補助定義順に
代入して消去残差の次数上界Dを生成し、$`J\ne 0\Rightarrow \nu \le D`$を証明する。
augmentation $`B_{0}\to k_{0}`$、$`m_{0}`$、$`J_{0}\subseteq m_{0}`$を持つ一般係数版では、二つの冪零商
$`B_{0}/m_{0}^{r+1}`$、$`B_{0}/(J_{0}+m_{0}^{r+1})`$の任意base changeとの交換を証明する。
両者の射のkernel $`D_r`$について変更後のkernelを$`D_r\otimes k_{1}`$の像へ同定し、flatなときの
同型とfaithfully flatなときの零性反映を証明する。これは剰余体kのArtin判定と分ける。

### G. 有限graphの実adapter・SAGA・全修復

可換環R、一辺以上を持つ有限連結単純graph $`\Gamma`$、その向き、$`\mu \in R`$、offset $`b_e\in R`$を
量化する。各頂点の台帳$`R^{2}`$・公開状態Rについて、原始加群演算とLawから
$`p=(1,1)`$、$`v=(1,-1)^{\mathsf T}`$、$`i_\lambda =(\lambda ,1-\lambda )^{\mathsf T}`$、$`j_\mu =\mu v`$、$`g_b=I+bvp`$を構成する。
固定pの族はG-140 Pの一型の係数表示とのmarked同型を使い、$`p i=\mathrm{id}`$、$`p j=0`$から
$`\mathop{\mathrm{apply}}\nolimits_u(x)=x+i(u)`$、$`\mathop{\mathrm{compact}}\nolimits_t(x)=x+j(t)`$、$`\mathop{\mathrm{read}}\nolimits=p`$の全有限語の公開意味保存を証明する。
入力$`u,t`$は比較の両側で同じ外部入力とする。

```math
\begin{aligned}
g_b^{-1}&=g_{-b}, & p g_b&=p, & g_bv&=v,\\
g_bi_\lambda&=i_{\lambda+b}, & g_bj_\mu&=j_\mu, & g_cg_b&=g_{b+c}
\end{aligned}
```

から、実操作のadapter整合が$`\lambda _j-\lambda _i=b_e`$と同値になることを示す。

$`\Gamma`$の頂点と辺を点とし、$`U_i=\{i\text{と接続辺}\}`$を最小開集合とする有限Alexandrov空間を作る。
$`U_i`$の非空連結性、二重交差が辺一点または空、相異なる三重交差が空であることを証明し、
全実交差、AAT site、topologyに属する被覆、MonomorphicOrderedCover、K1支持を生成する。
$`g_b`$のdescentから局所自由・局所定数の層$`E_b`$と$`0\to \underline Rv\to E_b\to \underline R\to 0`$を構成する。
$`\ker  p\simeq Rv`$、$`\mathop{\mathrm{Ob}}\nolimits(V)=\Gamma (V,\underline Rv)`$、$`\mathop{\mathrm{State}}\nolimits(V)=\{s\in\Gamma(V,E_b)\mid p(s)=1\}`$と層条件を導き、
$`\mathop{\mathrm{State}}\nolimits(X_\Gamma )`$と実大域操作$`i(a)=as`$を同定する。$`E_b`$のdescentとiの存在を分ける。

[SAGA EquationLift](../../Formal/AG/SemanticRepair/Saga/EquationLift.lean)のLiftFiberDataを
上のsectionと$`\mathrm{base}=1`$から生成し、`exact_at_middle`、restriction、単射性を放電する。
liftSystemからAffineCoefficientLiftSystem、局所実現からCoefficientLiftAtlasを作り、
`residualClass_isZero_iff_matching_correction`を同じ入力へ適用する。
空交差・対角・順序反転とStateの層条件から全pairの一致を実sectionへ戻す。
[PartIVBridge](../../Formal/AG/SemanticRepair/Saga/PartIVBridge.lean)の
SitePresheafData.ofObstructionSheaf、incToCoverRelativeH1を同じObへ適用し、
omitted pair/tripleの零係数を実交差から証明して指定IncH1類とCoverRelativeHn 1を同定する。
この比較のsite・被覆・制限写像は、上の有限空間と実交差から構成する。

SAGAの増加pairから指定向きへ、次数0は恒等、次数1は向きの符号を掛けるTを作り、
$`T\delta^0_{\mathrm{SAGA}}=d^0_\Gamma`$を証明する。三角形では$`T(c_{01},c_{02},c_{12})=(c_{01},c_{12},-c_{02})`$。
交差をj側で読み、$`r_e=\lambda _j-\lambda _i-b_e`$、$`o_b=[r]=[-b]=\delta (1)`$を同定する。

```math
\mathop{\mathrm{State}}\nolimits(X_\Gamma)\ne\varnothing\quad\Longleftrightarrow\quad o_b=0\quad\Longleftrightarrow\quad b\in\mathop{\mathrm{im}}\nolimits d^0
```

を証明し、非空な全解を$`\mathop{\mathrm{Ob}}\nolimits(X_\Gamma )\simeq R`$のtorsorとする。

頂点の変更可能集合から$`H_V\subseteq R^V`$を生成した場合は$`b-d^{0}\lambda \in d^{0}(H_V)`$で存在を判定し、
全解を$`\ker(d^0\vert_{H_V})`$のtorsorとする。SAGAの引く補正とは$`a=-c_{\mathrm{SAGA}}`$で比較する。
辺の変更可能集合から$`H_E\subseteq R^E`$を生成した場合は$`[b]+[\Delta b]=0`$でoffset修復を判定し、
全解を$`\ker (H_E\to H^{1}(\Gamma ;R))`$のtorsorとする。各修復後の操作の$`H^{0}`$の自由も保持する。
この同じOb、State、r、$`o_b`$をG-142の診断・Atlas比較へ渡す。

### H. 同じ構成を通す指定例

以下をE–Gの原始生成・比較へ通す。係数を記さない有限表示例ではkを任意の体とする。

1. $`\mathbb Q`$上の$`c+d=1`$を基準$`c=d=0`$から修復し、全域、$`\Delta d=0`$、全固定で解集合が順に直線、
   単点、空となることを示す。局所Law・観測を保つ部分加群も同じデータで計算する。
2. Law $`t^{2}=0`$の$`t=\varepsilon`$は$`k[\varepsilon ]/\varepsilon ^{2}`$上で成立し$`k[\varepsilon ]/\varepsilon ^{3}`$へlift不能となる。
   比較用のLaw $`t=0`$では同じ基準点の一次自由度が零であることを示す。
   残差$`(t^{2},t^{3})`$のsyzygy $`(t,-1)`$と、$`\mathbb Z`$上の$`(z^{2},2z^{2})`$のsyzygy $`(-2,1)`$から、冗長Lawを
   除いた$`H^{0}`$・$`H^{1}`$・障害との同定を証明する。後者は$`\mathbb F_2`$への特殊化も同じ比較へ通す。
3. $`k=\mathbb Q [t]`$、三文脈の$`x_{1}-x_{0}`$、$`x_{2}-x_{1}`$、$`x_{0}-x_{2}`$を、$`R=k/(t)`$、基点0で読む。
   syzygy $`(1,1,1)`$により$`H^{1}(T_{\mathrm{raw}})\simeq \mathbb Q`$、$`H^{1}(D)=0`$となる。一方、最後のLawからtを引くと
   各文脈は$`k/(t^{2})`$へliftできるが、大域では$`H^{1}(D)\simeq \mathbb Q`$の非零障害が残る。
   両入力で基点のLaw値・支持が一致することも示す。
4. 二文脈$`Y=T^{2} / Y=0`$、共有$`T,Y`$で、$`T=\varepsilon`$、$`Y=0`$を$`k[\varepsilon ]/\varepsilon ^{2}`$から$`k[\varepsilon ]/\varepsilon ^{3}`$へ比較する。
   任意の観測lift $`T=\varepsilon +a\varepsilon ^{2}`$に対して局所liftは存在し、合法修復係数$`C^{0}=0`$、$`C^{1}=(\varepsilon ^{2})`$に
   $`\kappa _u`$と同じ非零$`[\varepsilon ^{2}]`$が残ること、$`\nu =2`$を証明する。
5. 全$`N\ge 1`$で$`Y_{1}=T^{2}`$、$`Y_{j+1}=Y_j^{2}`$、$`Y_N=0`$を消去し、$`J=(t^{2^N})`$、$`\nu =2^N`$、
   構文上界の鋭さと初回lift不能を示す。観測Law $`Y=T^N`$と追加Law $`Y=0`$では$`\nu =N`$となり、
   表示上の一次式だけでは検出次数が決まらないことを示す。
6. $`\mathbb Z [t]`$、$`J=(2t^{2}+t^{3})`$、$`t\mapsto 0`$で、orderは$`\mathbb Z`$・$`\mathbb Q`$上で2、$`\mathbb F_2`$上で3となる。
   $`D_{2}=2\mathbb Z t^{2}`$のtensorは非零でも変更後のkernelは零となり、Fの像の比較と一致する。
7. 任意の体k上の無限表示$`T_i=T_{i+1}^{2}`$では$`A_\infty=\mathop{\mathrm{colim}}\nolimits k[t_i]`$を原式から作る。原点局所環で$`m=m^{2}`$、
   $`t_{0}\ne 0`$、全有限Artin変形は定値と証明する。$`T_{0}=0`$を追加しても全次数の比較は同値だが、
   $`A_\infty`$は整域、$`A_\infty /(t_{0})`$の$`t_{1}`$は非零平方零なので両schemeは同型でないことを示す。
8. Gの三角形$`0\to 1\to 2\to 0`$で、負のoriented sumにより$`o_b`$を$`\sum b_e`$へ同定し、holonomyの
   大域操作固定条件も$`\sum b_e=0`$とする。$`\mathbb Z`$・$`\mathbb Q`$で$`b=(1,2,-3)`$の全解は$`(t,t+1,t+3)`$、
   $`b=(1,0,0)`$は局所実現と$`E_b`$があっても大域操作を持たない。
   $`\mathbb Q`$上で後者のoffset修復域を全辺、一辺、空とした全解は平面、単点、空となり、
   各修復後に一自由度が残る。$`\mathbb Q`$上で$`\lambda =0`$、$`b=(1,2,-3)`$を頂点変更で修復する場合、
   固定頂点なしなら一自由度、固定頂点が一つなら一意、二つ以上なら不能となる。
   全解$`(t,t+1,t+3)`$と固定成分が零である条件から、全ての許容頂点集合についてこの分類を証明する。

さらにG-140 Pの同じsnapshot protocolと、その意味保存条件$`\mu \delta =0`$を用いる。
原始追加$`E=\mu \delta`$、$`E=0`$をFの消去へ通し、同じ意味保存係数fiberを$`V(\mu \delta )`$へ同定する。
体上の原点の特異性、$`\nu =2`$、各軸方向の全次数lift、$`\delta =\mu =\varepsilon`$の二次lift不能を証明する。
任意の候補$`\delta =\varepsilon +a\varepsilon ^{2}`$、$`\mu =\varepsilon +b\varepsilon ^{2}`$の残差$`\varepsilon ^{2}`$、実read差$`-\varepsilon ^{2}`$、Eの相対障害、
二文脈$`E=\mu \delta  / E=0`$の合法修復係数$`C^{0}=0`$、$`C^{1}=(\varepsilon ^{2})`$を同じ写像で比較する。
比較には、固定pの族と一型の係数表示のmarked同型を用いる。

G-140 Pの$`\mathop{\mathrm{finish}}\nolimits_{\mathrm{snap}}`$への修正ではこの障害が消えることを、同じ観測と状態比較で示す。
さらにbefore・p・語翻訳を固定し、評価条件$`D(\mu ),D(\delta )`$をG-140 Eの探索fiberとして構成する。
旧式の$`V(\mu \delta )`$では一方の評価条件だけなら$`\mathbb G_m`$、両方なら空であることを全R点で比較する。
許容変換式

```math
\mathop{\mathrm{finish}}\nolimits_\rho(B,C,h)=(B+\mu h,C-\mu((1-\rho)C+\rho h))
```

から
$`g_\rho =\mu (1-\rho )(h-C)`$を生成し、Busyを$`V(g_\rho )`$とする。
begin・applyの$`g_\rho`$への代入、finishのread差、begin; $`\mathop{\mathrm{apply}}\nolimits_1`$; finishから、
全語の意味保存と$`\mu \delta (1-\rho )=0`$を同値にする。
評価条件$`D(\mu \delta )`$の下で$`\rho =1`$が強制され、全解が$`\mathbb G_m^2`$、状態が全$`R^{3}`$、
選ばれる式が$`\mathop{\mathrm{finish}}\nolimits_{\mathrm{snap}}`$になることを原始変換族から導く。
旧Busy Lawを固定する許容変換域では、同じ評価条件の解が空のままであることも証明する。
体上の非零条件と全R上の単元条件を区別し、この変換族における全解の比較をDへ通す。

$`\mathbb Q`$上でGの$`g_{1}`$は$`\lambda =\mu =1`$を$`\lambda ' =2,\mu ' =1`$へ運ぶが、後者では$`\mathop{\mathrm{Idle}}\nolimits(0,0)`$から
begin; $`\mathop{\mathrm{apply}}\nolimits_1`$; finishのreadが2となることを証明する。
同じ$`\mu =1`$で$`g_1(\mathop{\mathrm{compact}}\nolimits_{\mathrm{all}}(1,0))=(2,-1)`$と$`\mathop{\mathrm{compact}}\nolimits_{\mathrm{all}}(g_1(1,0))=(1,0)`$を比較し、
原子操作のadapter保存を拡張した観測言語へそのまま移せないことを証明する。

## 前提・構成台帳

| 対象 | 役割 | 構成・証拠 | 使用先 |
| --- | --- | --- | --- |
| 観測・作用・adapterの原式 | 入力 | A–Bの全射分類 | change scheme・複体 |
| 複体・制限射・cotangent・比較 | 構成義務 | A–Bの同じ原式から生成 | 大域障害・微小lift |
| 交互列aと$`D(2)`$,$`D(3)`$ | 指定証人 | Cの全段・局所解と非零類 | Čech・Ext・$`\mathop{\mathrm{lim}}\nolimits^1`$の一致 |
| ML性・有限安定性・有限還元・停止性 | 別々の放電義務 | Dの原始構造から導出 | 有限certificateと算法の十分性 |
| 許容変換・評価条件・係数域と探索fiber | 入力と先行構成 | G-140 E、Dの生成・全解回収・復元 | 評価条件を満たす変更候補と不存在 |
| 有限表示、平方零拡大、原始reading、指定観測lift | Eの入力 | 独立Sem、全syzygy、残差、合法修復を生成 | 実lift・相対fiber・conormal比較 |
| 体、有限表示、実現点／自由観測chart | Fの各系の仮定 | Noetherian性・Artin商／構文上界を別々に導く | 全Artin検出・有限上界 |
| 有限graph、$`\mu`$、offset、許可変更集合 | Gの入力 | 実adapter・全交差・State・LiftFiberDataを生成 | SAGAの零性と実操作、G-142の診断比較 |
| Hの原始表示・phase・試験環 | 指定証人 | E–Gと同じ生成・比較へ通す | syzygy・検出次数・修復・操作輸送の検査 |

## 完了条件

A–Hの一般比較と指定例をLeanで証明し、native射・scheme・cotangent・Čech・$`\mathop{\mathrm{lim}}\nolimits^1`$の
全写像を同じprimitive入力に遡ってreportする。
native比較は原始操作から構成し、大域的存在と障害の零性の比較は、全Lawと全fragmentにわたって証明する。
B・Cでは無限Law族の全体を保持し、有限特殊化との比較と残る研究義務を明示する。
Gの実操作・Ob・State・指定障害は同じ入力から生成し、SAGAのmatchingから実sectionへ
戻す比較を完了対象に含める。Fの有限表示定理とHの無限Artin例は、それぞれの量化で証明する。
固定主張への反証は、その量化に属する原始入力と破れる比較・存在判定を示して記録する。

成果物はresearch/lean/ResearchLean/AG/のLean証拠と、
research/reports/G-141-aat-coherent-repair-effectivity.mdの宣言・前提対応に置く。
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
