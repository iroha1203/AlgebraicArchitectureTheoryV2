# 全Homの幾何、Lawful状態、descent

## 定理 B3 — 独立な変更と全係数上の表示

独立な変更は、二つの原始model、その実際のsort maps、語翻訳、観測・quantity・固定部分の保存式から定義する。幾何的表示を以下の手順で構成する。

**Copyingの場合。** 各状態mapの各入力に有限出力supportを選び、G-139 N3の全profileを使う。係数 `a_(x,y)` の冪等・直交・和1の式が、実際のcoalgebra mapを回復する。operationの二経路の係数を展開して等式を課す。合成は各行の有限和なので、各固定profile上の各成分式は有限多項式になる。relation/domainの保存は、許された部分copying coalgebraの外の係数が零という式である。選択値、観測、quantityの保存も同じmapの可換式として課す。

**有限局所自由なlinear familyの場合。** 原始sortのframe上で各 `h_v` の全matrix成分を変数にし、G-139 P4.1と同じoperation保存式を課す。sourceとtargetのrankは異なってよい。観測とquantityの式も加える。frame変更はsourceとtargetの基底変更によるmatrix変換であり、全保存式を運ぶ。したがって同じ条件の全mapをdescentできる。

**任意moduleの場合。** 原始module `M` をその全元を生成元とし、加法とscalar倍を関係とする自由moduleの商で表示する。map `M⊗R→N⊗R` は、各source生成元の像をtarget生成元の有限和で与え、全source関係を零へ送ることと同値である。targetの関係moduleへの所属は有限和の導出witnessで表せる。そのsupportを各生成元・各関係ごとに保持し、全profileを取る。targetの同じ元を表す有限和と、同じmapを証明するwitnessを同一視する。自由moduleと商の普遍性によって、この商は任意 `R` 上の全線形Homと全単射になる。指定operation・quantityの式もこの同じ商で検査する。

指定されたregular operationや状態schemeを持つ `σ` については、G-139 C2–C5の全有限多項式supportと、後述B4の商環での保存を使う。任意native関数のregular性を新たに仮定せず、G-139で指定した係数的解釈とnative比較をそのまま使う。

いずれも、表示から元のmapを組み立てる写像とmapの値・matrix・有限表示を読む写像は、自由性・商・totalityによって互いに逆である。異なるsupport表示や導出witnessは同じ実際のmapに戻るときにだけ同一視する。係数環射は全係数と原始式を送るので、全 `R` に自然な同値を得る。これは定義した変更modelの条件を、原始係数から生成した表示で証明する同値である。

### B3.1 — Native基点と三種類の射

copyingは整数上で定義でき、`Z`、またはconnectedな非零環でG-139 N2.3により全native mapを回復する。全環に自然なmap族からも `Z` 成分で回復する。非連結環には冪等分割による追加mapがあるので、それをnativeな一個のmapと同一視しない。linear familyのnative係数環 `k` では `M⊗k≅M`、固定したsignature・翻訳上で原始係数作用を保つ全HomもG-139 B1.4で戻る。指定native点の移送は `e_x`、または `m⊗1` へのmapであり、全保存式と可換である。構文選択自体の係数化についてもC3.1のnative比較を用いる。

| 対象 | 実際のmap |
| --- | --- |
| 状態比較 | `h:X₁→X₀` |
| quantityの引戻し | `q↦q∘h`。domain/Law-input条件を満たすと量の空間の射になる |
| 変更のmoduli | 両端と `h,τ`、補助選択、保存式を持つ点 |
| 両端へのspan | `M₀←C→M₁`。state mapそのものではなく両端を忘却して読む |

quantityのLawが全て引き戻せない場合も `h` を削らない。G-139 B3の `Z_h`、すなわち両端の量に `q=h^*q'` を課した対応を用いる。単に観測値が一致する `M_before×_(M_obs)M_after` だけでは `h` を回復できない。例えば二元集合の両端を固定し、操作なし・定値観測なら、このfiberには一組の端点しかないが、その間の実際のmapは四個ある。

## 定理 B4 — Ideal所属と状態射の一意因子分解

状態のambient表示を `A_i=k[z_(i,a)]`、原始Lawの生成idealを `I_i`、Lawful状態を `X_i=Spec(A_i/I_i)` とする。候補の原始式 `H_a∈A₁` をsource座標へ代入し、自由性から `H#:A₀→A₁` を生成する。すると

```math
H^\#(I_0)\subseteq I_1
\quad\Longleftrightarrow\quad
A_0\xrightarrow{H^\#}A_1\longrightarrow A_1/I_1
\text{ が一意に } A_0/I_0\text{ を経由する}.
```

**証明。** 因子分解があれば `I₀` は零へ送られる。逆に包含があれば `[f]↦[H#f]` が代表元に依存しない環射となり、商への全射性から一意である。scheme側へ反変に移すと、ambient mapの `X₁` への制限が一意に `X₀` を経由することになる。これは閉部分schemeへの因子分解の [Stacks 01HP](https://stacks.math.columbia.edu/tag/01HP) のaffine計算でもある。□

operation保存の残差は、二経路の各座標の差を同じsource状態環で評価する。観測残差も同様であり、零性はその状態idealへの所属である。partial操作には、始域として宣言された合法domainの座標環を使う。この可換式をA2へ渡せば全許可語の保存が従う。

`H₀₁#:A₀→A₁`、`H₁₂#:A₁→A₂` の合成は `H₁₂#H₀₁#`。二つのideal包含から合成の包含を得る。schemeでは `h₀₂=h₀₁h₁₂` であり、語翻訳もA3の順序になる。

### B4.1 — 開条件が現れる例

係数 `a∈R` と状態環 `R[y]/(ay)` を取る。この環で `y=0` となる条件は `a∈R^×` である。実際、`y=ay f(y)` なら `y` の係数比較で `1=a f(0)`。逆に `a` がunitなら `y=a⁻¹ay`。よって係数parameter `a` の条件は `D(a)` となる。

これはambient環 `R[y]` で `y=0` という恒等式を課すことと違う。状態Lawを法とするideal所属には開条件も現れ、全てをambientの係数零という閉条件に置き換えることはできない。零環もこの計算に含まれる。

### B4.2 — 導出witnessとambient代表の商

`I₁=(f_λ)` とする。`H#(r_ν)∈I₁` の証拠は有限集合 `F_ν` と多項式 `b_(ν,λ)` による

```math
H^\#(r_\nu)=\sum_{\lambda\in F_\nu}b_{\nu,\lambda}f_\lambda
```

で表せる。各多項式の有限supportを選んで係数比較すればwitness付きaffine chartを生成できる。全ν、全supportを保持し、次数の一様上限を置かない。

この表示を元の全Homへ戻すとき、同じ `H#` の導出witnessだけでなく、全source生成元 `z` について `H#z−H'#z∈I₁` となるambient代表も同一視する。両端・指定翻訳・保存すべき補助dataは固定しておく。商環の射は生成元の像で決まるので、商後の二点が等しいことと実際の状態射が等しいことが同値である。

逆に任意の商環射には、各生成元の像のambient liftがあり、各Lawに有限ideal所属witnessがある。従って全support表示のこの商は、実際の全Homへ全単射になる。選択は証明に使うが、出力Homには残らない。係数変更は代表とwitnessを送って同値関係を保つ。実際の候補として保持すべき `h,τ` を、評価値だけが等しいために商にすることはしない。

## 定義 C1 — 原始supportからのcontext site

原始宣言をsort、operation、relation/domain、quantity、選択値/witness、Lawの項目に分ける。各項目のsupportは、その型と参照する宣言の集合である。termのsupportは構文木から再帰的に作る。Lawは左右のsupportと量化するdomainを持つ。選択witnessを持つLawはそのwitness宣言も含める。

contextは、この依存関係について閉じた宣言項目の部分集合。包含が制限の向きであり、coverは合併が元のcontextになる族とする。交差もcontextで、coverの交差によるpullbackと反復coverの合成が再びcoverになるためsiteを得る。Lawという項目をcoverするとは、そのLawと全supportを一つの局所contextで保持することである。

AATのcontextとしても同じsupportを実現できる。G-139 P1aの宣言Atomを固定base objectに置き、各contextのSupportをそこに含まれる宣言項目、supportReadsを対応するAtomを読む関係とする。他の成分を同じ定数dataで取れば、包含はSupportの包含と各定数成分の恒等により `IsRestriction` を満たす。Law項目の依存閉包が、そのLawを読むcontextに全参照Atomを含める。ここで使うcoverはこの原始supportから生成した宣言contextのcoverであり、全context上の任意のquery族を無条件にcoverと宣言するものではない。

各sortのcarrierと、宣言に含む各operationの全関数は一つのdata blockとして保持する。totalityを有限個のgraph queryだけに置き換えない。無限担体の行表示を使う場合は、各入力の**全行**とその有限support表示を一つのblockとし、zero paddingで同じ行を表すものを同一視する。有限supportという原始条件を持つquantityも、その全quantityと条件を保持するblockを用いる。

## 定理 C2 — Contextについての対象・全Homの組立て

cover上でmodelが共有宣言について一致するとする。各sort・operation・quantity等を、それを含むcontextから読む。二つのcontextに属すれば交差のmatchingにより一致するので、選択に依存しない。各Lawは自身のsupportを持つcontextで成立し、その原始評価は大域dataを制限した評価と同じである。従って大域modelが得られ、その全fieldが決まるので一意。

実際の状態mapも各sortのmapを同じ方法で貼る。operation保存、relation/domain保存、観測保存は各式のsupportを含むcontextで検査できる。これらは大域式と同じ評価だから保存射が得られ、全Homについて一意である。合成は各sortの関数合成なので、制限・組立てと可換。

totalityは、ある入力の全行を持つcontextで定まる出力が大域でもその出力になることから保存される。finite supportはその全行の同じ有限和を使うので保存される。各入力で別のsupportを許し、その和集合が有限だとは結論しない。

同型でmatchingするunmarked実現では、その同型をcocycleとして保持して同じfieldをdescentする。組立ては指定matching dataを保つ一意な同型を除いて一意である。元のmodelの自己同型自体を自明とする主張ではない。

## 定理 C3 — 係数被覆と二つの制限の交換

係数schemeの被覆はfppfとする。保持する構文選択は次項C3.1の方法でまず降下させる。各選択の片上で、G-139 B1–B2・P2で構成した対象のdescentに変更の各実際のmapを加える。QC moduleの全mapはdescentを持ち、有限tensorの可換式はfaithfully flatに検査できる（[Stacks 023T](https://stacks.math.columbia.edu/tag/023T)）。copyingのcoalgebra mapとそのrelation/domain部分も同じ方法で降下する。regularなscheme mapは局所のmapを同じ対象間のmapとして貼る。観測・quantity・操作保存の二辺は局所で一致するので大域で一致する。

copyingの全行は降下後に直和moduleの元であるため有限supportを持つ。affine base上で直接確認するには、被覆のaffine片を有限個選んでfaithfully flatな環 `R→∏ S_i` を取り、ある入力の有限supportの和集合を取る。その外の係数は全 `S_i` で零だから `R` でも零である。supportは入力ごとに選ぶ。全域関数もcoalgebra mapのcounit、または原始totality dataから回復される。

宣言制限はfieldを選び、係数制限はそのfieldをtensor・pullbackする。二順序の出力は同じfieldと同じmapであり、tensorのcanonical同型で一致する。term帰納法がLawの二順序の一致を与える。組立てについては両順序の局所制限が同じで、descentの一意性により同じ結果になる。これにより対象・全Hom・観測保存・合成の二種類のdescentが可換になる。

ここで証明したsheaf条件は原始Lawと指定された係数的実現についてのもの。後で任意の集合値部分関手を評価条件として加えた場合、その条件の局所性は当該部分関手について別に判定する。

### C3.1 — 構文選択自体のdescent

翻訳名、規則添字、保持する離散的な補助選択の集合を `L` とする。その係数的解釈は定数**集合関手** `R↦L` ではなく、constant fppf sheaf `ΔL` とする。これは `∐_(l∈L)Spec k` へのmapであり、affine上では

```math
\Delta L(R)=
\{(e_l)_{l\in L}\mid e_l^2=e_l,\ e_le_{l'}=0\ (l\ne l'),\
\#\{l:e_l\ne0\}<\infty,\ \sum_l e_l=1\}.
```

非零な各 `e_l` がclopen片 `Spec(Re_l)` とその選択 `l` を指定する。独立な係数model側でも、各片に原始model・実際のmap・その構文選択を置き、片のdataを合わせたものを変更と定義する。従って幾何側だけに新しい候補を加えていない。表示用supportは同じ実mapに戻るものを商にするので、保持を指定された意味上の選択と混同しない。

この選択はdescentを持つ。affine fppf被覆の有限部分被覆上の冪等元族がoverlapで一致すれば、忠実平坦な環のequalizerから各 `e_l∈R` が一意に降下する。有限個の被覆片のsupportの合併は有限で、その外は零。冪等・直交・和1も忠実平坦に検査できる。よって上の条件が大域で成立する。任意の被覆はaffine片と有限部分被覆により同じ結論を持つ。

複数の独立な構文fieldを持つ場合はfieldごとにこの構成を使い、依存する型と式を共通細分上で照合する。例えば制約なしの翻訳族では各operationの翻訳が一つのblockである。一方、`H` の一要素が全signatureの編集をまとめて指定するなら、その規則名全体が一つのblockであり `ΔH` を取る。無限個の独立選択の積と、その積集合全体に一度 `Δ` を適用する構成は同一視しない。有限termの評価には有限個のfieldしか現れないので、必要な共通細分は有限である。二つの翻訳の合成も `e_lf_m` の片で構文代入して作れ、単位・結合則は各片の同じ式から従う。対象やsortの宣言自体を変える規則では、その規則片上の対応するtyped familyを用いる。context制限はそのfieldを制限するだけなのでC3の二種類の制限の交換にも従う。

connected非零環では冪等分割は一つの `l` となり、元の構文選択を回復する。任意の基礎環でも、指定された一つの構文選択上のfiberでは元の全mapを回復する。非連結環の混合選択を一個のnative termと呼ばない。零環では空の分割が唯一で、空scheme上の空被覆とも整合する。例えば二つの異なる翻訳が同じ実mapを与える場合も、非空の片ではその名を区別し続ける。

こうして全構文選択を含む変更とその全射を係数上で貼れる。rawな点ごとの直和 `∐_l F_l(R)` のままではclopen片で異なる選択を貼れないため、このdescent形への移行が必要である。

## C4 — 三つの異なるfiber

| 問題 | 入力とfiber |
| --- | --- |
| 平方零lift | `R'↠R`、kernel平方零、`c∈C_H(R)` に対する `C_H(R')→C_H(R)` のfiber。固定両端や評価も同時に引き戻す |
| 文脈の組立て | context coverとmatching dataに対する大域変更からdescent dataへの関手のfiber。C2–C3により空でなく、同定込みでcontractible |
| fragmentの延長 | 指定query/宣言fragmentに沿う制限の、与えられたfragment値上のfiber。全行totality・有限support・全Lawを保持した全modelから制限する |

有限fragmentへの全制限が互換でも、延長fiberが非空とは限らない。G-139 N3の無限all-false行、C4の全座標1の族は、それぞれtotality、finite supportを失う反例である。通常のcontext被覆の組立てでこれらの条件が保たれるのは、C1のblockとLaw supportをcoverしているためである。

matchingでない局所変更について、比較を補正してmatchingにする条件と全補正はG-141の同じ変更fiber上の問題となる。C2の証明は、補正の存在を仮定として隠してはいない。
