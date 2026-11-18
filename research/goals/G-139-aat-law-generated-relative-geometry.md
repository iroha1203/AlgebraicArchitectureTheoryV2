# G-139-aat-law-generated-relative-geometry — 量とLawから構成する相対幾何

- `id`: G-139-aat-law-generated-relative-geometry
- `status`: `draft`
- `research mode`: `target-theorem`
- 関連メモ: [#6359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。実行用tracking Issueはactive化時に定める。
- 設計: [n1019 §1–4](../../docs/note/n1019_shigure_representability_design.md)
- 先行成果: G-124のnative再構成。多項式特殊化の定義・具体例は[n1020 §3–8](../../docs/note/n1020_shigure_polynomial_specializations.md#3-原始入力と独立な実現)を参照する。

## 研究目的

原始構造の量とLawから相対Specを構成し、本物の代数幾何へ接続する。
その幾何的表現の基礎要件として、元の状態・操作・Law・全Homを忠実に回復する。
この構成をG-140の意味保存射と、保存条件・評価条件に相対的な変更の解空間の基礎にする。
有限局所自由modelはこの一般構成の特殊化として比較する。

## 固定target

### N. 元の意味を回復する幾何的表現

#### N1. 原始意味圏

任意の小さいmany-sorted signatureについて、担体、有限arityの実際のoperation、
relation、指定domain上のpartial operation、選択値をデータとするmodel圏を、幾何的表現に先立って構成する。
射は実際のsort mapsとoperation/relation保存であり、恒等と合成を証明する。
存在witnessを選んだモデルと存在だけを要求したモデルを区別する。
モデル集合と射を原始表示から生成し、その幾何的表現との比較を後段で構成する。

Atom configuration、opaque payload、lens、protocol、G-124のgeometryについて
原始宣言を構成し、既存の対象と全Homを回復する比較関手を与える。
generic ArchitectureObjectについては射のデータを新たに構成し、
元の型・値への忘却を明示する。

#### N2. 複製・消去を保つ係数化

全可換環$`R`$と全集合$`X`$に$`C_R(X)=\bigoplus_X R`$、basisの複製$`\Delta`$とcounitを構成する。
直積・終対象との同型を含め、N1の全termの評価、Law、恒等・合成を運ぶ。
任意の$`X,Y`$についてcoalgebra Homと
$`\mathop{\mathrm{Hom}}\nolimits_R(\coprod_X\mathop{\mathrm{Spec}}\nolimits R,\coprod_Y\mathop{\mathrm{Spec}}\nolimits R)`$の自然な全単射を構成する。
連結な非零環で全native Homを回復し、全可換環にscalar extensionで自然な射の族は
$`\mathbb Z`$成分から元の集合写像を回復することを示す。零環での挙動も証明する。

全$`R`$上のHomを、入力ごとの有限直交冪等元分割と出力選択によって分類する。
任意のnilpotent thickeningでこの離散Homが一意に持ち上がることも証明する。
この零の微小変形と、Aのquantityの非零微小変形を区別する。

#### N3. 無限担体のtotalityと全Homの表示

各入力ごとの有限出力supportを保持したaffine chart、その拡大、全profileの表示系を
生成し、全$`R`$でN2のHomを回収する。合成のsupportを有限和の式から生成する。
次の三つの主張を反証する。

- 全有限Boolean queryの閉条件だけからtotalityが回復する。
- 全入力に共通する有限出力集合を選べる。
- モデルごとの有限評価supportは一様な有限段階への因子分解を与える。

反例には無限出力の全false行、$`\mathbb N`$の恒等写像、$`f(g(x))`$の評価を使う。
G-124のIsTotalとcompose_finite_supportへの同じquery単位の比較を証明する。

#### N4. 既存native族の回復

total lensの三等式から$`C\cong K\times V`$を構成する。
同じview $`V`$を固定してview mapを恒等とする全Homは$`K\to K'`$に対応すると証明する。
viewも変える一般相対Homは、両viewに基準値がある場合、
$`(K\to K')\times(V\to V')`$に対応させ、既存のstate/view両mapを回復する。
空viewの場合はgetのsourceも空になることから対象・Homを直接分類して残す。
この分類は任意のfiberを対象とする。
Set上の分解・相対射のnormal formには既存の
[GeneralRelativeLens](../lean/ResearchLean/AG/RealizationReconstruction/GeneralRelativeLens.lean)
のproductEquiv・normalForm・productMapを再利用し、新規義務を係数・descentとの比較に置く。
任意small execution category $`P`$のprotocolは$`[P,E]/O`$として、
全path Lawと全自然変換を回復する。非単射射と非自明自己同型を必須例とする。

opaque payloadは任意$`P`$と選択点のまま保持する。
任意の既存residualはその実際のgraphとして保持する。
式と係数作用を指定した宣言については、その指定から係数的解釈を構成する。

#### N5. 図式・候補族・評価の原始表示

小さい圏$`J`$の各対象にN1の宣言を置き、各射または指定した生成射に実際のsort mapsと保存式を置く。
恒等・合成・指定関係の式から$`J`$型の意味図式を生成し、
図式間の自然変換を成分ごとの実際のsort mapsから構成する。
部分圏$`K\hookrightarrow J`$、その上の固定図式、許容する宣言変更・term代入・補助sortの規則を
原始入力とし、固定部分との比較を保持した全補完候補を独立に定義する。
原始宣言の解釈と生成した図式・候補の解釈が一致することを、termと図式関係に沿って証明する。
この生成を係数変更、図式形の引戻し、固定部分の制限、許容規則の包含と可換にする。
全補完を分類する2-fiberと経路の合成はG-140 Fで構成する。

同じ原始表示上のquantity・操作語・状態比較から評価を生成し、
各候補の評価と独立なmodel上の評価の一致を証明する。
共有する規則係数を指定した候補族には、その係数と実際の射・語翻訳・補助選択を保持する。
評価値だけへの忘却と候補そのものの回復を別の写像として構成し、
G-140 Eの条件付きfiberとreadingに相対的な共通候補の比較へ渡す。

### A. 任意担体・任意個の量とLawによる相対Spec

構造$`S`$、quantity domain $`D_j(S)`$、Law入力$`E_\ell(S)`$を任意の小さい集合で量化する。
quantity modelは実際の関数$`q_j:D_j(S)\to R`$と、その上の原始Lawの充足として定義する。
有限式は構造のcartesian term、quantity評価、係数、環演算から生成する。

$`Q_S=\bigoplus_j C_k(D_j(S))`$、$`A_S=\mathop{\mathrm{Sym}}\nolimits_k Q_S`$を作り、複製・操作のcoalgebra射・普遍量から
$`\rho_\ell:C_k(E_\ell(S))\to A_S`$を生成する。$`I_S`$は全像の生成idealとする。
原始評価と$`\rho_\ell`$の評価の一致をterm帰納法で証明し、

```math
\mathop{\mathrm{LawfulQuantity}}\nolimits_S(R)\simeq\mathop{\mathrm{Hom}}\nolimits_k(\mathop{\mathrm{Spec}}\nolimits R,\mathop{\mathrm{Spec}}\nolimits(A_S/I_S))
```

を全$`k`$代数$`R`$・全環射について自然に構成する。
変数・Law・担体とidealの生成族は任意の濃度を許す。
左辺は関数と原始Lawの充足によって定義し、環Homとの対応を評価定理から導く。

任意の可換$`k`$代数$`S`$について、量$`q:S\to R`$に環演算保存Lawを課すことで
$`A_S/I_S\cong S`$と$`\mathop{\mathrm{Spec}}\nolimits S`$を回収し、全環Homの反変な射との一致を証明する。
任意module $`M`$の線形quantityから$`\mathop{\mathrm{Sym}}\nolimits M`$も回収する。
一般には任意QC module $`Q`$の線形quantityが$`\mathop{\mathrm{Spec}}\nolimits\mathop{\mathrm{Sym}}\nolimits Q`$で表現される構成を使い、
任意のcopying domainとmodule domainを接続する。

### B. 構造・係数・文脈の変更と相対Spec

Nのsplit copying coalgebraとそのdescent forms、実際のoperation・relationから
構造のstack $`B_{\mathrm{copy}}`$を構成する。被覆の種類を固定し、局所split moduleの降下と全Homの降下を
証明する。このstackの担体はNのsplit copying coalgebraの局所splitな降下形とする。

nativeの係数作用・原式からはmodule $`M\otimes R`$、scalar $`R`$等の係数的実現$`\sigma`$と$`B_\sigma`$を別に構成する。
$`\Delta\lvert M\rvert\to M\otimes R`$の写像、指定native定数点の回復、native基点での全Homの回復を証明する。
非連結$`k`$の追加点と、dual numbers上の新しい線形方向を保持し、
全$`R`$で$`B_{\mathrm{copy}}`$と$`B_\sigma`$をそれぞれの原始構造から構成する。
点ごとのLawと全係数familyでのLawをそれぞれの評価によって比較する。

$`Q`$、$`\rho`$、$`I`$を同じ同型に沿って降下し、$`M=\mathop{\mathrm{Spec}}\nolimits_{B_{\mathrm{copy}}}(\mathop{\mathrm{Sym}}\nolimits Q/I)`$を構成する。
任意scheme $`T\to B_{\mathrm{copy}}`$へのpullbackが独立なquantity modelのaffine $`T`$-schemeになること、
基礎環変更、構造同型、文脈制限、term substitutionに自然であることを証明する。
同じ構成を、原始データから$`Q`$・$`\rho`$を生成できる各$`B_\sigma`$上でも証明する。
構造保存射$`h:S\to S'`$がquantity domainとLaw入力を運ぶ写像を原始sort mapsから生成し、
term評価との可換性からquantityの引戻しと$`A_S\to A_{S'}`$のideal保存を証明する。
この条件を満たさない元のnative $`h`$も保持する。
quantity domainを運ぶ$`h`$について、一般には$`M_S\times M_{S'}`$上の$`q=h^*q'`$という対応空間を構成し、
全target quantityからの射になる条件と区別する。補集合上のLawを持つ反例も証明する。
sheafificationとscalar extensionの交換には必要な仮定を実際に放電する。

### C. 係数的意味と全拡張の分類

既存ArchitecturalEquationSystemのsymbolic coordinateとobject-dependent residualを
原始データとして保持し、原式または下記拡張空間から生成したresidualとの評価一致を比較する。
有限式で与えられたresidualと任意関数として与えられたresidualを、それぞれの原始データから扱う。
各native familyで次の三つを区別する。1・2を構成し、3は以下で構成する拡張空間の点が与える選択として構成する。

1. graphとして元のresidualをそのまま保持する。
2. 固定native値を$`\mathop{\mathrm{Observable}}\nolimits\otimes_k R`$へ運ぶ。
3. 選択された拡張点から、変動するquantity上のregular residualを生成し、元の評価との一致を証明する。

$`\mathop{\mathrm{Nat}}\nolimits(R^n,R)\simeq k[t_1,\ldots,t_n]`$を普遍tupleから証明する。
$`\mathbb F_p`$上で$`t`$と$`t^p`$が同じnative値を持つが異なるfamilyになること、
$`\mathbb Q`$上の$`\delta_0`$が$`\mathbb A^1`$上のregular extensionを持たないことを証明する。
有限support Lawにはzero extensionのind表示を構成し、全有限restrictionの逆極限との
非同値を証明する。これらのLawも同じ意味圏の対象として保持する。

さらに任意native担体$`D`$、任意$`X`$、指定されたquantity reading $`q:D\to k^X`$、
任意$`\varepsilon:D\to k`$について、全regular extensionの空間を構成する。
有限単項式集合$`F`$ごとに係数$`b_m`$を持ち、
全$`d\in D`$で$`\sum b_m m(q(d))=\varepsilon(d)`$を課すaffine scheme $`E_{\varepsilon,q,F}`$を作る。
zero extensionの閉埋込みに沿うind表示$`E_{\varepsilon,q}`$を構成し、
その$`S`$点が全$`S`$代数$`R`$に自然な$`R^X\to R`$でnative値に一致するものを全て分類することを証明する。
$`q`$を固定し、$`\varepsilon`$に一致する拡張を、全次数・全有限座標supportにわたって分類する。

全入力$`D=k^X,q=\mathop{\mathrm{id}}\nolimits`$では無限体で存在すれば一意であることを証明する。
有限体$`\mathbb F_q`$では評価核$`(t_x^q-t_x)_x`$と、延長の存在と有限座標依存の同値を証明する。
一般の基礎環で$`k`$点不存在とschemeの空性を区別し、
$`\mathbb Z`$上の$`\varepsilon(n)=n(n-1)/2`$の次数2 chart$`\cong\mathop{\mathrm{Spec}}\nolimits\mathbb Z[1/2]`$を構成する。

複数context・operation・term substitutionとのcoherenceを、普遍tupleでの係数等式として
同じsupport-profile chartに課し、互換な全拡張のmoduliと普遍residualを構成する。
元のresidualのgraphと照合し、その上のLawの零点familyを構成する。
$`\mathbb F_p`$上の$`t/t^p`$を用い、native値の一致だけではcoherenceが従わないことを反例で示す。

$`M\otimes R`$、$`\mathop{\mathrm{Hom}}\nolimits(M,R)`$、$`C_R(\lvert M\rvert)`$を任意module $`M`$について区別し、
実際の比較写像と、dualizability等を使う箇所を記す。
係数familyの選択を明示し、指定された原始係数構造を保持する比較を構成する。

### D. 通常の代数性と有効化

原始的なevaluation/coevaluationとsnake等式を持つ有限個のmodule sortについて、
dualizabilityから局所有限自由性を導き、全局所階数成分のframe chartsを生成する。
残りの宣言が有限tensor・直和・dual・指定retract等から構成され、
操作・Lawの追加が相対affineになることを具体的な生成規則ごとに証明する。
構成したGL作用・torsor・同型diagramから商stackの代数性を証明する。
markingによる自己同型消滅とopen overlapが構成できる場合はschemeを接着する。

一般の意味圏では任意担体を保持する。独立なline quotientの無限積$`\mathbb P^1`$と、無限階数moduleの全自己同型を
同じ意味圏に保持して、それぞれの通常のalgebraic space・algebraic stackへの非有効化を証明する。
operation profileは各chartと全profile表示について有効化を個別に判定する。
$`\mathbb N`$の恒等写像を表すprofile $`S_n=\{n\}`$のchartは$`\mathop{\mathrm{Spec}}\nolimits k`$になることも検査する。
無限moduleの接空間はtensor extensionの$`B_\sigma`$で計算し、$`B_{\mathrm{copy}}`$では微小変形が零であることを示す。
schemeへの接着にはtrivial inertiaとopen overlapの構成を証明する。

### P. 多項式特殊化との同一入力上の比較

[n1020 §3–8](../../docs/note/n1020_shigure_polynomial_specializations.md#3-原始入力と独立な実現)
の原始表示Pについて、N・A–Dの構成を次の同じ対象・射へ同定する。
可換基礎環、有限個の型と階数・生成元数、小さい演算・Law族を量化し、
Law族とidealの生成族は任意の濃度を許す。

1. **独立な実現と原始評価。** 加群・演算・Lawから$`\mathop{\mathrm{Sem}}\nolimits_P`$、非可逆な演算保存写像の圏、
   その最大部分groupoid $`\mathop{\mathrm{Real}}\nolimits_P`$を定める。Semは$`K_v\subseteq R^{m_v}`$と商上の演算として定義し、
   全射qを保持する実現の同型類との同値を構成する。Atomの五座標・configurationと
   raw係数tupleのgraphからencode/decodeを作り、$`\mathop{\mathrm{decode}}\nolimits\circ\mathop{\mathrm{encode}}\nolimits=\mathop{\mathrm{id}}\nolimits`$を証明する。
   値を一意に読めないobjectにはdecodeを零tupleで補完する。
   decodeの係数自然性はraw tupleのencode像上で証明する。
   原始Lawを普遍ambient Bの残差と評価先Rの残差へ生成し、
   $`B_s\to R_{x(s)}`$による評価一致と、全raw点での$`\mathop{\mathrm{EquationLawful}}\nolimits\iff\text{原式の全Law成立}`$を証明する。
   全contextの係数は点支持の内部$`U_W`$上の$`\Gamma(U_W,O)`$とし、principal open外も含める。
   $`D(1)`$と空openを保持し、宣言の忘却と係数層の制限の向きを区別する。
   conormalのidealは普遍ambientで作ってから引き戻す。
2. **chart・descent・表現。** 生成元から選んだ局所基底のopen条件、成分多項式、
   determinantを可逆にするoverlap、tensor残差の変換とidealの一致、cocycleを生成する。
   個別の方程式はrequired Lawへ置き、StructuralRelationFamilyを使う場合は空とする。
   原始式の係数変更から、任意基礎環射での生成idealのextensionと商環のscalar extensionを
   変数・Law別生成元の対応まで、非flatな基礎環射も含めて同定する。
   宣言被覆とZariski被覆の制限・組立ての交換、Realのfppf descentを実加群から証明する。
   任意環射でのKの像とprojective quotientの分裂、tensorのcoherenceを同じ構成へ通す。
   独立な$`\mathop{\mathrm{Sem}}\nolimits_P(R)`$と$`\mathop{\mathrm{Hom}}\nolimits(\mathop{\mathrm{Spec}}\nolimits R,M_P)`$の同値、普遍実現、基底openの被覆を構成する。
3. **readingと基礎環の自然性。** 型を改名・追加する単射、tensor式代入、required Lawと
   標準等式からの導出でreading射を定義する。射の等号は型対応と導出可能な式の等号とし、
   導出証明の選択に依存せずに定まるものとする。Semの反変な解釈とMの射を同じ式で構成し、
   恒等・合成、任意基礎環変更、普遍実現、文脈細分化との可換性を証明する。
   逆代入から同型を、Law追加からその成立locusへの閉埋め込みを構成する。
   StandardArchitectureScheme.baseChangeへは、その装飾と仮定を別に満たす同じ入力で比較する。
4. **生成元を忘れる比較。** 基底付き方程式の$`X_P`$、GL作用、frame torsorを生成し、
   独立な$`\mathop{\mathrm{Real}}\nolimits_P`$と$`[X_P/\prod\mathop{\mathrm{GL}}\nolimits]`$の同値・代数性を証明する。全射行列のopenから
   $`M_P\to[X_P/\prod\mathop{\mathrm{GL}}\nolimits]`$のrepresentability・smoothness・surjectivityを導く。
   inertiaを実際の演算保存自己同型へ同定し、qを保つ自己同型の自明性を証明する。
5. **同じ構成を通す証人。** n1020のW1–W3・W5–W8を1–4へ通す。
   可逆操作とその非恒等改名、$`q=(2,3)`$を持つ$`\mathbb P^1`$、$`0`$と$`\varepsilon`$を区別する二重点、
   $`\mathbb P^1\to B\mathbb G_m`$と$`-1`$の自己同型、cocycleを破る平行移動、非同型なLaw追加と$`\mathbb Z\to\mathbb F_2`$、
   共有kernelが一致／不一致となる二文脈を指定する。$`m=1,2`$の違いと全零階数も比較する。
   W1の$`(2,1/2)`$と$`(1,1)`$は生成元付きSemでは異なり、qを忘れると$`\mathbb Q`$上の二型の基底変更で
   同型になることを、同じ実現と忘却写像で証明する。
   optionalな$`T=0`$を前提にした代入の失敗と、同階数二型の恒等／交換が異なる作用を持つ例を示す。
   Nのコピーを忘れたBool ANDが$`2e_{\mathrm{true}}`$で冪等性を失う例、非連結環のidempotent分割、
   $`x(t)=\varepsilon`$における普遍残差と評価後残差の違いも同じ比較に残す。
6. **図式と評価への特殊化。** N5の図式の対象・生成射・関係から、両端と固定部分を保持する
   comparison presentationとその普遍候補を生成する。有限対象・有限生成射・有限関係で表示される図式形について、
   有限係数表示と全Lawの有効な有限還元を持つchartでは有限の成分方程式を生成し、
   その解と元の全図式補完との同値を証明する。候補の$`h`$・語翻訳・補助選択と評価を同時に回復する。
   任意の小さい図式とLaw族はN5の全候補表示で保持し、有限還元と停止性の証明をG-141 Dへ接続する。

Pの各結果をN・A–Dへの比較として証明し、
元の任意担体・全Hom・全residualから生成した一般構成との対応を与える。

## 前提・構成台帳

| 対象 | 役割 | 構成・証拠 | 使用先 |
| --- | --- | --- | --- |
| 任意signature・担体・操作・関係 | 入力 | N1の独立な意味圏 | 全Hom・term・native族の回復 |
| coalgebra・全profile・native比較 | 構成義務 | N2–N4の生成と全Homの同定 | A–Dの意味保持 |
| 図式形・固定部分・許容規則・評価式 | 原始入力 | N5の宣言と実際のsort maps | 全図式・候補族・評価の独立定義 |
| 図式関係・候補解釈・評価一致 | 構成義務 | N5・P6の生成と自然性 | G-140の補完・経路・共通候補 |
| 原始quantity、Law式、nativeの$`D`$・$`q`$・$`\varepsilon`$ | 入力 | A・Cの意味を幾何と独立に与える | 評価一致・全拡張分類 |
| $`Q`$・$`\rho`$・ideal、$`E`$の表示、coherence | 構成義務 | A–Cの生成とnative比較 | 相対表現・普遍family |
| 局所split性、moduleの係数作用 | 経路ごとの入力 | Bのcopyingと$`\sigma`$を区別し、各原始解釈を構成 | descent・基点の全Hom |
| duality等式・有限frame生成規則 | Dの十分条件 | frame・作用・overlapを生成 | 通常の代数性 |
| 多項式表示・生成元・原始代入 | 特殊化の入力 | Pの同じSem・Real・Law評価から生成 | chart・stack・係数自然性 |
| 全nativeの保持・非有効化 | 構成義務 | C–Dの分類と指定反例 | 一般構成と特殊化の比較 |

## 完了条件と成果物

N・A–D・Pの定理、原始sourceとの対応、正例・反例をLeanで証明する。
完了には原始入力からのframe構成、$`\rho`$の生成、descentの証明を含める。
N5の図式・候補・評価を同じ宣言から生成し、全ての射の回復とP6の有限表示への比較を証明する。
全$`D`$・$`q`$・$`\varepsilon`$の拡張空間、context全体の互換性、原始係数構造とnativeの比較、
通常のscheme・algebraic stackへの有効化と指定された非有効化の証明を揃える。
有限module成分はこの一般構成への比較として証明する。

成果物はresearch/lean/ResearchLean/AG/のLean証拠と、
research/reports/G-139-aat-law-generated-relative-geometry.mdの宣言・前提対応に置く。
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
