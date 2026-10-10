# 核の標準構成と計算範囲

本書は、[reading の宣言](law.md)と[原始 Atom](inputs.md)から核が生成する対象、
局所構造、診断、修復、比較を定める。問合せの署名と結果の形式は
[実行仕様](execution.md)に従う。以下の行列、環、係数、cover、証拠は核の生成物である。

## 1. 対象、作用、Law instance

`build` の configuration `(F,R,E)` は次の固定規則で作る。
Fには選択root、そのrootをownerとするentity/arrowの存在事実、その全既知field Atomを入れる。
さらにfield値を型に沿って走査し、参照先の存在事実を加える。外部参照先のfieldは取り込まない。
Rは存在事実からそのfield Atomへの対と、field Atomから値に含まれる参照先存在事実への対。
owner/from/toも同じ規則に従い、推移閉包を加えない。
Eは原始identityの対角関係。同じ参照先は同じ存在事実を使い、別の原始位置を値の一致で同一視しない。
List等の位置・順序・重複は原始値に保持する。未知owner/参照で所属が確定しない場合は、
条件付きの構成と必要slotを残し、対象を確定値として構成しない。
Configuration.requirementsはFのsubjectに宣言された全fieldのslotであり、既知・未知の両方を含む。

共通の Atom carrier U は、全入力 snapshot の subject 存在事実と全既知 field Atom の有限族とする。
同じ subject ID でも snapshot が異なれば別の元であり、構成のための新しい原始 Atom を加えない。
写像の表、恒等、合成、作用の等値はこの同じ U 上で扱う。

`map` は correspondence の各 Map を原始要素とフィールド位置へ延長する。
root は from→to、owned subject は対応表、field は同名規則または align で移す。
対象外の外部参照は固定する。既知 field の像には実在する target field Atom を要求する。
参照を含む値は、参照 leaf をこの subject 写像で移して target の参照構造と照合する。
List の順序・重複、Tuple の位置、Option/data の参照に至る構造を保ち、量 leaf の一致は要求しない。
source root の全 configuration の F 上をこの表で写し、F 外の U の元はすべて target root の
存在 Atom へ送る。この全域表について family・関係・同一視を、対応表について型・参照・
owner・arrow の端点を検査し、確認済みのものだけを configuration map とする。
値・Law・操作・局所構造の保存は、それぞれ追加の検査である。

object algebra の有限対象族 Obj は、この root の全 configuration を base とし、さらに
各 owned entity p の部分 configuration を一つずつ持つ。部分 F は p の存在事実、p の全既知
field Atom、その値が参照する subject の存在事実である。R/E は上と同じ規則で生成する。
参照先の field は取り込まず、p の未観測 field は必要 slot として保持する。
同じ configuration が生成されても対象の subject identity を潰さない。
owned arrow は対象を増やさず、名前付き生成操作の候補となる。

内部 arrow e の候補作用は、from の存在事実を to へ、from の field を to の同名 field へ写す。
参照 leaf は from を指すものだけを to へ移し、それ以外は固定する。
参照構造と target field の実在を検査し、source 部分 F 外では恒等として U 上へ全域化する。
この総写像の configuration 保存を確認したものが、二つの部分対象間の生成操作である。
未確認の arrow は候補のまま残す。候補を黙って除外して完成した object algebra とせず、
必要な保存検査が未決なら構成も未決、反証されたならその構成を反証する。
`change` は §4 の候補状態への作用であり、この内部 arrow の操作族へ加えない。

Op(A,B) は A から B への型の合う生成操作の有限語である。空語は U 全体の真の恒等写像、
非空語の実作用は生成操作の総写像の合成とする。`compose` も端点の一致する実写像を合成し、
合成後に対応表から全域化し直さない。名前付きの語と実作用を別に保持する。
自己対応表が source F 上で恒等でも、F 外を root へ送る correspondence は、空語の全域恒等と
同作用とは限らない。`relation` は両辺の全域作用の一致を確認してから使い、
その成立だけで自由語を同一視しない。有限の語を調べた結果は、その有限族を量化域に保持する。

correspondence による object algebra の対象写像は base→base、p→対応表の像 μ(p) とする。
各対象成分には、source root の全 F から作った同じ U 上の対応総写像を使う。
生成操作 e の像は arrow の対応表で指定された生成操作であり、端点もこの対象写像で移す。
各生成操作について二通りの合成を U の全元で比較し、configuration 写像の自然性を確認する。
この対応を語へ順に延長することで、全有限語の操作写像と恒等・合成の保存を構成する。
source F 外では対応写像の像が target root であり、target の内部操作はその root を固定する。
source F 内の衝突や共有参照に起因する不一致は、この全域自然性の検査に残る。

宣言の対応は、同名、同じ宣言 kind、移送後の型付き署名の一致によってだけ決める。
entity/arrow は correspondence の型対応、field は同名規則または align、parameter は位置によって移し、
束縛名の違いを除く。参照を含まない値型は同じ型を要求する。
この規則を Law/view/local/change/relation に使い、別名や似た式から対応を推測しない。
外部の helper 宣言は、その式が参照する対応先の宣言として保持する。
対応名または署名が揃わなければ `condition_failed` とし、この固定規則で構成できないことを返す。
一般の object algebra の射が存在しないという結論にはしない。
対応が決まった後の保存違反は反証、必要な等値を決める算法がない場合は `unsupported_algorithm`
であり、未観測値への依存とも区別する。

Law は宣言名、role、束縛、原式、左右の項、型、出現 identity を持つ。
未指定の entity binder は、選択した対象と固定された外部参照に適合する有限族へ展開する。
存在が記録された instance は、値欄が欠けていても残す。
各 instance の operand は原始フィールド位置と式中の出現まで追跡する。
代数的簡約で同じ式になっても、この identity と読取りの支持は変えない。

`evaluate` は型付きの値を、`check` は原式の成立と反例を返す。
整数等式なら左右の値と差、積型なら成分ごとの値と差を保持する。
一般の条件は条件種別と型付きの評価を保持する。
`required` の全 instance が成立したことが、その族についての lawful 判定である。
空の有限族では成立と評価件数 0 を返す。

object algebra の Law/view の読取りは、その固定された Obj 上で次のように生成する。
base の適用域は root とその owned entity/arrow、部分対象 p の適用域は p とする。
参照先の存在事実を F に含めただけでは、その subject をこの適用域へ追加しない。
この域の参照に適用された宣言の instance を取り、当該 root の対象を量化する binder は
この域へ制限する。宣言が明示する外部参照は固定し、scalar parameter の全域は記号的に保持する。
域内の instance は必要 field が未観測でも残す。域に適用されない instance と、
存在する instance の評価が欠測に依存することを区別する。
root/owned の参照へ適用されない helper は独立の観測軸に追加せず、呼出し先の式として保持する。

各 view instance を関数不変量と signature の軸にする。全宣言 view の該当軸を selected とし、
値型 T、参照束縛、残る scalar parameter、各対象での評価を保持する。
軸が対象に適用されない場合を Option<T> の none、適用される場合を some(value) として区別し、
未観測値を none で埋めない。残る parameter を持つ軸は、その全域にわたる添字族である。
各 Law instance は role と適用条件を持つ述語不変量とし、適用されるときの原式成立を読む。
数値的な equation reading は §2 の同じ原式・共有記号・評価から生成する。
適用外の出現は要求違反を生まず、未評価の出現を成立済みの residual に置き換えない。

有限 circuit の候補は、各対象の U 上の atom membership と、全順序対についての
relation/identification query にその真偽を付けた完全な有限 pattern とする。
relation query の真偽は `a∈F and b∈F and R(a,b)`、identification も同様に E を読む。
F 外の R/E はこの reading の照合に用いない。順序は AtomUniverse の順に固定する。
各 Law 出現の scalar realization の成分について、原式、guard、operand の読取りから、
pattern に一致する構成が当該 residual の零性を反証することを検査する。
pattern で固定された原始値を原式へ代入し、当該成分の ε が非零であることを表す
型付きの when 式を生成する。parameter ごとに when=true となる
case の exact match の有限選言を detector とし、該当 case がなければ拒否 detector とする。
scalar parameter がなければ when は確定した Bool 値である。
pattern の一致と when から当該成分の反証への含意を原式について全称検査する。
等号全体の反証だけを理由に、零である成分の detector を受理させない。
未観測や非対応の評価を反証 case にしない。pattern、when、component、元の反証評価を保持し、
最小 circuit や、
選択した有限対象族の外で全ての反証を検出する完全性を主張しない。

AAT の任意 ArchitectureObject 上での読取りには、この query pattern による固定延長を使う。
選択 Obj と同じ pattern を持つ対象では、その Obj の適用条件、view 値、Law と residual の読みを
使う。複数の Obj が同じ pattern を持つ場合は、残る全 parameter 上でこれらの読みが一致することを
確認する。不一致は、この ArchSig の固定延長の構成条件を満たさない `condition_failed` とする。
入力不正や欠測として扱わず、任意の一行を選ばない。
選択 Obj のどの pattern にも一致しない対象では view を none、Law の適用条件を false、
適用条件付き述語を true、residual を零とする。Law の role は対象によらず保持する。
この延長は追加の StructureMaps/SelectedQuantities を読まない。
一致した行の必要値が未観測なら none や零で埋めず、必要な全域読取りの構成を未決として保持する。
値・一致・residual の全域性を確認してから AAT の全域関数へ接続する。
受理 circuit は必ず選択 pattern に一致し、その class の共通の読みを when が反証する。
したがってこの延長は任意 ArchitectureObject について circuit の健全性を保つ。

§2 の scalar realization を一つの AAT equation reading に入れるときは、型別に共有する
realization 環 R_i の有限 block 積を Observable とする。空族は空積の一元環とする。
各 R_i の原式、共有変数、ideal は保持し、Law 出現ごとの別々の積へ置き換えない。
添字は `(Law instance, scalar parameter の代入, component)` とする。
単一 global context の base root 存在 Atom に、その成分の ν と residual を対応する R_i の
factor へ置き、他の factor と、他の U の元では零とする。異なる環の同一視は行わず、
この座標配置を factor から積への単位的環準同型とは扱わない。制限は恒等である。
residual は、適用される対象では §2 の ε、適用外では零とする。原式の差の評価 ε 自体は
上書きしない。detector の when も適用条件と当該成分の ε 非零性の連言から作る。
detector は添字ごとに when を評価して reject/exact/any の有限 code を生成し、
when を既存 detector 型の追加構文にはしない。
これにより各添字の EquationHolds は当該 residual の零性と同値になり、適用される原式の等号は
全成分の成立に対応する。対応成分は移送後の型の同じ component path で対応させ、
その residual の零性の同値も検査する。

object algebra の保存は、対象・操作の対応に加え、対応 Law の required status、適用条件と
成立の同値、circuit の運搬、関数・述語不変量、signature の軸と selected status を検査する。
circuit は source の対象と受理 case を target の対応対象の case へ写し、
matching、when の含意、detector の受理を確認する。
関数不変量と signature は値型間の順逆写像を生成し、
型の全域で互いに逆であること、および各対象の評価との可換性を検査する。
参照値の写像は宣言の対応表と固定外部参照から、複合値の写像は型の構造から生成する。
この値写像は Atom の F 外を root へ送る全域化とは別であり、型の同値を構成できなければ
その適用条件を満たさない。有限域は全列挙、整数アフィン域は正確な正規化で検査し、
scalar parameter の全域について必要な等値を有限の評価例で代用しない。

local/change/relation の対応は、それぞれ reads の値と制限、候補域と実更新、
両辺の名前付き語と作用へ延長し、型付きの対応と可換性を検査する。
local の公開値を依存 field 全体へ広げず、change を内部 Op に加えず、
relation を確認前の等式として使わない。これらの生成規則と数学の条件は §3–9 に従う。
完全な ObjectAlgebraMap は、以上で選択された全構造の対応を確認した場合だけ生成する。
必要な構成が未決・非対応でも、既に確認した base の ConfigurationMap と Operation は保持する。

## 2. 方程式の記号表示と評価

`EquationPresentation` は、選択した対象の全支持上で共有変数を持つ方程式表示である。
同一 scalar 型の多項式等式族では、型に従う係数環 K と、原始位置・候補位置を共有する
記号集合 X から一つの環を生成する。整数式の K は Z であり、有限標数へ変更しない。

```math
R=K[X],\qquad \nu_q=\operatorname{lhs}_q-\operatorname{rhs}_q,\qquad
I_{\mathrm{required}}=(\nu_q\mid q\text{ is required}).
```

等式を積型の scalar 成分へ展開し、同じ位置を読む全出現で同じ記号を使う。
多項式の required ideal に入れるのは、選択域で guard が恒真と確認された出現である。
恒偽の guard は not_applicable とし、状態に依存する guard はその適用条件を保持する。
その条件を表す構成がない無限域では、当該条件の数値的 realization を非対応とする。
対象 A の代入による環準同型 evA を作り、`εq=evA(νq)` と
原式成立 `iff εq=0` を確認する。εq の R 内での表示は定数多項式である。
原式、記号対応、role、成分化、正規化前後の対応を保持する。
型の異なる等式族は型付きの表示と明示された型変換を保持し、単一環への同一視を補わない。
R と I_required は同時方程式の表示であり、ideal 内で νq が零になることを
対象の成立判定に用いない。例えば `x=0` と `x=1` は同じ R に `(x,x−1)` を生成する。

全 operand の値域が有限の場合は、全出現で共有する有限代入集合 D を列挙し、
`R=Z^D` に `νq(a)=1[guardq(a) and lhsq(a)≠rhsq(a)]` を生成する。
guard 省略時は true とし、対象代入での評価が εq である。
この場合も左右の型付きの値と原式を保持する。R/I_required の残る座標は、
全 required を同時に満たす代入に対応する。

この global 表示を AAT の equation system に接続するときは、全支持を持つ単一 context と
恒等制限を使う。局所の読取りを表す状態系と、その係数は §3–6 で独立に生成する。
この表示用の context を局所診断の cover へ追加しない。
未観測 operand に依存する ε は未評価のまま保持し、total residual を要する接続は
必要な値が揃った評価に限る。

局所では、読める値座標 X_W と、そこで原式を評価できる出現 Q(W) を生成する。
その状態から残差 tuple への評価写像を res_W とする。
V→W の読取り制限では、状態の実射影 ρ_X と残差座標の射影 ρ_Q を作り、
`res_V ∘ ρ_X = ρ_Q ∘ res_W` を検査する。対象の ε はこの写像の対象状態での値である。
保持した出現の全 operand が読めることを確認し、
不可視で落ちた行を成立件数へ数えない。
支持による多項式表示では変数包含 `K[X_V]→K[X_W]` を作り、その包含によって
ν_V が ν_W の保持した行に一致することを確認する。
局所式はこの包含の像から取り出し、隠れた変数へ零を代入する環準同型を仮定しない。
一般の有限／アフィン read では、実際の有限像／整数格子像上で同じ因子分解を検査する。

数値的な realization を構成する算法がない条件にも、原式・型・支持・通常の条件評価は残す。
非対応はその realization を求めた計算に記録する。方程式表示の環、修復係数、
状態集合、Čech 複体は別の型を持つ。

## 3. 読取りの圏と cover

`localize` は指定 Law 族と許す change を固定する。Law 省略時は reading の全 required、
change の選択と binder の指定は実行仕様に従う。Law の外部 binder は固定参照として保持する。
各 `local` を選択対象へ束縛し、公開参照、読める値座標、その出現を持つ context を生成する。
ref を公開しただけでは、その値欄を公開したことにならない。
view の依存支持と公開値座標を分け、積の成分は射影できるが、合計を読めても各項を
公開したことにはしない。Law 原式が公開値の関数として因子分解するかを、有限域では
fiber 上の一定性、アフィン域では整数核・像の計算で検査する。

同じ基底への読取りを、参照 identity と値座標を保つ写像として保持する。
標準の包含 context では重なりは公開情報の交差である。
一般の対応を介した比較では、実写像から有限 pullback と二つの射影を作る。
恒等、合成、因子分解、状態・値の制限との可換性を検査する。
同じ端点を持つ別の写像は、実作用を比較するまで別の射である。

reading に `local` 宣言がある場合、その全 instance を cover 候補とし、重なりと反復制限を生成する。
核は、必要な原始支持、Law 座標、選択した witness、値の軸、共有値・相互作用の読取りを
覆うかを検査する。不足があれば座標と宣言を示して `visibility_insufficient` を返す。
不足を埋めるために context の読取りを増やしたり、基底自身を patch に追加したりしない。
別の Law の大きな支持を理由に、選択族の cover を変更しない。

`local` 宣言がない場合は支持による reading とする。核は各 Law 出現の全支持 context と、
どの Law にも現れない候補変数の singleton を生成する。
変数と Law 出現を持つ依存閉包付きの有限 context とし、出現を持つ context は全 operand を持ち、
cover は変数と出現の両方を覆う。状態は当該 context の条件を満たす代入、制限は射影である。
一致する局所代入を変数ごとにまとめ、各出現を含む patch で条件成立を確認することが、
この状態系の一意な貼り合わせの構成になる。

実行する有限 context の圏、cover 候補、適格性、生成 topology を別の結果として保持する。
`localize` は常に、恒等、引戻し、合成による有限の閉包を計算して topology を生成する。
選択した cover の検査を、未検査の全 topology 上の sheaf 条件へ拡大しない。

## 4. 候補状態と許す変更

`solve` と `repair` の候補域は同一である。指定された `change` の entity binder を、
`on` の対象内で型に適合する各 entity へ独立に束縛する。値 parameter の域は宣言型に従う。
核は同じ原始位置への更新、固定する位置、作用の合成、必要な共有 parameter を保持する。
Law の外部参照と、更新対象外の値は固定する。
候補は観測対象から作用によって生成し、未観測の値を候補 parameter に変換しない。

候補 parameter 域が有限の場合は、指定された同時更新の全代入と、その像を全列挙する。
操作名と parameter を保持し、同じ状態に達したことを別に記録する。
局所の作用・状態は宣言された read で射影する。
修復の可否は、指定 Law を満たす候補状態が存在するかで決定する。
有限に生成された操作表について閉包を求める場合は、有限不動点まで計算する。

整数アフィンでは更新式を正規化して、有限 parameter t の作用 `x=x0+A t` と
選択 Law の条件 `Lx=c` を生成する。x0 は更新式の parameter 零での基準候補であり、
恒等からの平行移動では観測値に等しい。生成行列の行・列は原始位置、
Law 出現、change の束縛と parameter 成分へ対応する。係数を既知の正確な整数へ評価できることを
確認してから、次の系を作る。change の parameter に線形等式の guard がある場合は、
先にその整数 fiber を求め、非空なら特解と整数核によって自由 parameter へ再表示する。
x0 と A をこの再表示へ合成し、元の parameter への復元写像を保持する。

```math
B=LA,\qquad d=c-Lx_0,\qquad T=\{t\in\mathbb Z^m\mid Bt=d\}.
```

Smith normal form で解 t0、整数核の生成元、または整除・零行の矛盾を得る。
一般のアフィン作用や指定された有限操作列も、固定部分と自由 parameter について正規化できる
場合は同じ有限系へ展開する。任意長の操作語の到達可能性を、一回の更新と同一視しない。

`solve` は候補域と全解の有限表示を返す。`repair` はその表示から具体的 parameter と候補対象を
生成し、更新式、型、固定部分、原式の Law を再評価して返す。
不成立の場合は元の式に対応する有限反例または整数整除の証拠を返す。

## 5. 意味状態、係数、局所変更の持上げ

T が非空なら parameter fiber は `ker B` の自由推移作用を持つ。
実際の修復後状態 `x0+A(T)` の係数は、核が別に計算する次の像である。

```math
K_{\mathrm{state}}=A(\ker B)
=\operatorname{im}A\cap\ker L
\cong\ker B/\ker A.
```

これは候補 parameter の差が作用する係数である。元の change の反復・合成を
この加法作用と対応させる場合は、元の更新式から恒等・合成・逆の式も検査する。
作用の核を同効果関係として商にする。指定された `relation` を使う場合も、
作用の等値と、その関係で必要な安定化群を尽くすかを検査する。
非可逆な変更から群を作って、許す変更を増やすことはしない。
有限作用では可逆性・可換性・安定化群を全列挙する。可換群による有効作用を構成できる
場合に加法係数へ進み、他の場合も有限の作用と修復判定を保持する。

局所の意味状態は、まず許可変更による候補域を read へ射影し、その後に局所で可視な
Law だけを課して作る。全体の Law 解集合を先に射影して局所解とすることはしない。
アフィン read の線形部を P_W とし、定数部を局所の基準状態 x0_W に含める。
局所式の因子分解を `L_W x=c_W` とすると、核が次を生成する。

```math
A_W=P_WA,\qquad B_W=L_WA_W,\qquad d_W=c_W-L_Wx_{0,W},
\qquad S_{\mathrm{sem}}(W)=x_{0,W}+A_W\{t\mid B_Wt=d_W\}.
```

局所係数は `A_W(ker B_W)` であり、局所で消える作用 `ker A_W` を商にする。
制限の像と作用の可換性を確認する。整数の場合は格子像を保持し、隠れた変数を含む式を
削除して可視変数の全域へ広げない。例えば `x−2y=0` の x 射影は `2Z` である。

局所変更の族が一つの許された変更から来るかは、その read 射影の積を P として、
有限の逆像または整数系 `P A t=Δ` を解く。これを直接の持上げ判定とする。
`rebalance(s,d)=(-d,d)` に対する Stock/Held の要求 `(-2,0)` は、
`−d=−2` と `d=0` の矛盾として反証される。
共有参照だけの overlap による一致は、この持上げ判定を代替しない。

値域の追加条件は候補域の一部として保持する。parameter の線形等式は §4 の再表示、
状態の線形等式は L の行へ取り込む。
非負制約などで fiber を切った場合、元の kernel の作用で閉じるかを確認する。
完全な非空 fiber または確認済みの一剰余類にだけ torsor を構成する。
型付きの状態集合、parameter fiber、有効係数を別の型で返す。

## 6. 局所診断と Čech 計算

`diagnose` は `side=equation` を既定とし、`side=semantic` では許可変更からの意味状態系を使う。
結果に side を保持し、両側の状態・係数・類を同一視しない。
有限状態では、各 patch の解、重なりで一致する族、大域候補からの制限写像、その fiber を
全列挙する。局所解なし、一致しない局所族、一致するが大域へ持ち上がらない族を区別する。

方程式側の自由位置は、using で選択した change の各 instance の `with` 左辺にある
更新 field だけとする。Tuple 等の複合 field を更新する場合は、その field の全成分を含める。
自由状態の型は更新 field の宣言型である。アフィン表示では固定長Tupleをscalar成分へ分解する。
Listやdataではfield全体をその型の変数とし、観測した長さ・constructor形に候補域を固定しない。
他の全位置、外部参照、更新対象外の値は固定する。自由位置は更新先の宣言から決め、
未観測を理由に追加しない。更新前の未知の観測値は元の slot として残し、
固定部分の評価に必要なら、その依存による未決を保持する。
§2 の記号環は原式の全支持を保持する。fiber の生成では固定部分を評価してから、
局所で読める自由状態の全域に可視 Law を課す。この量化域を記号環の変数全体と同一視しない。

アフィンの局所方程式では、この自由状態上で context W ごとの完全な fiber `D_W z=b_W` と
`M(W)=ker D_W` を生成する。これは方程式側の状態・係数である。
意味側には §5 の許可作用からの状態・有効係数を使い、両側を比較する写像を別に作る。
意味側は同じ自由状態の中で、許された作用の実際の像を保持する。
using 省略時は自由位置を空とし、方程式側は固定観測の条件を読む零次元系、
意味側は Unit parameter と固定対象だけを持つ。
方程式側の全 fiber を、変更を許された意味側の修復候補へ追加しない。
制限が fiber を保つこと、D と b の制限の可換性、係数作用の自由性・推移性、
局所非空性を確認する。空の局所 fiber には atlas を生成しない。

核は、大域状態から matching family への制限写像を作り、その全単射性を検査する。
有限状態は列挙、アフィン状態は整数 kernel・image・fiber の計算で存在と一意性を決定する。
選択 cover 上の貼り合わせ条件と、生成 topology 全体の sheaf 条件は検査範囲を区別する。
局所方程式の解から意味上の actual repair へ進む場合にも、この検査と両側の状態対応を要する。

加法係数とその制限を得たら、順序付きの patch tuple と pullback から Čech cochain 群と
交代符号付き微分を生成する。次数 n の診断には n+2 個の patch の重なりまで生成する。
重複添字、平行射、面への複数の出現を保持し、構成した連続する微分の合成が零であることを検査する。
正規化した increasing-index 表示を使う場合は、その比較写像と適用条件も生成する。

`H^n=ker d^n / im d^(n−1)` は自由部と torsion を持つ有限表示として返す。
局所解 si を得た場合には制限差 `cij=sj|ij−si|ij` を計算し、cocycle 条件を確認して
対象の `[c]∈H¹` を作る。局所解の変更は coboundary になることを確認する。
H¹ という群、対象の類、その零性を別々に保持する。
局所非空性や値評価が未確定なら、計算済みの群を残しても対象の類は確定しない。
この局所解から生成する対象類は次数 1 である。他の次数では計算した群を返し、
対象に結び付く構成のない類を追加しない。

`[c]=0` なら補正を解いて matching family を生成する。
確認済みの貼り合わせ条件と状態対応を使って大域修復を生成し、元の Law に再代入する。
直接の持上げ判定と Čech 類の零性は、それらの比較条件を確認した場合にだけ同値とする。
cover-relative Čech 計算を sheaf cohomology へ同定する場合も、その接続条件を別に確認する。

## 7. 三辺の標準診断

[検証仕様](validation.md)の整数三辺では、各 Point の coordinate を読む `Edge` local と、
各 Point を独立に平行移動する change を `using=move` で選択する。
自由位置は三つの coordinate、Shift の端点と shift は固定値である。
初期 coordinate をすべて零とすると、核が生成する系は次となる。

```math
D=\begin{pmatrix}-1&1&0\\0&-1&1\\-1&0&1\end{pmatrix},\qquad
b=(1,1,\gamma).
```

三つの edge patch の係数は各々 Z、対ごとの overlap の係数も Z、
三重交差には coordinate が残らず、その係数は零である。
increasing-index 表示への比較を経て、核が次の微分と局所差を生成する。

```math
d^0=\begin{pmatrix}-1&1&0\\-1&0&1\\0&-1&1\end{pmatrix},\qquad
d^1:\mathbb Z^3\to0,\qquad c=(-1,0,\gamma-1).
```

商の同定 `H¹≅Z` は `(-1,1,-1)` によって生成され、対象の類は `2−γ` へ写る。
この計算には `using=move` が必要であり、using 省略時の零次元系とは区別する。
γ=3 なら非零類 −1 と大域解なし、γ=2 なら零類と候補 `(0,1,2)` を返す。
γ 未観測なら D、係数、微分、H¹ は計算できるが、b、局所解、対象の類は未確定となる。

## 8. 評価の十分性と診断の比較

`quotient` は選択した型付き view 評価の一致関係による商と実射影を生成する。
候補域と解集合を区別し、問合せで選択された域を固定する。
Law 評価は instance と値型を持つ族として扱い、成立 Bool だけの一致へ圧縮しない。

有限域では射影 q の各 fiber で対象評価族が一定かを検査し、降下写像または反例対を返す。
整数アフィンの全候補域では `q(x)=Qx+a` と評価 `Ex+b` に対する
`ker_Z Q⊆ker_Z E` を検査し、im Q 上へ降下写像を構成する。
アフィン部分域ではその parameter 表示上で同じ検査を行う。
商の終域は実際の像を用い、周囲の整数格子への延長を仮定しない。

診断比較では、指定された構造写像から context、cover、係数、状態の対応を生成する。
係数写像と制限の可換性、cochain map と微分の可換性を検査し、H^n 上の実写像、
kernel、cokernel を計算する。双方に対象類がある場合はその移送の一致も検査する。
Law 評価の十分性、係数の同型性、診断群の同型性、対象類の保存は別の結果である。
比較不能な構造や可視性の不足は、対応する写像を未生成として保持する。

## 9. v0.6.0 の必須決定範囲

| 入力から生成された問い | 核の必須手続き | 完了時に保持するもの |
| --- | --- | --- |
| 有限関係、有限型、有限木、有限閉包 | 全列挙、構造再帰、有限不動点 | 対象、値、導出、反例 |
| Z/Q 上のアフィン式の全代入等値 | 正確な係数正規化 | 同一正規形、または零・単位代入の反例 |
| 有限の整数線形系、格子像、有限表示可換群 | Smith normal form | unimodular 変換、解、整数核・像、整除違反 |
| Q/Fp 上の有限線形系 | 正確な消去 | 解、核・像、左零化子による反証 |
| 上記係数の複体、商、コホモロジー、比較 | 同じ正確な加群計算 | 実写像、自由部、torsion、対象類 |
| 有限の作用、局所状態、貼り合わせ、十分性 | 全列挙と fiber 比較 | 実作用、候補、反例対、持上げ |
| 完全な整数アフィン fiber の作用、制限、貼り合わせ | 正規化、整数核・像・fiber | 条件の成立または反証、実修復 |
| 有限 carrier の操作合同 | 合同閉包と作用検査 | 同値導出、異なる類、反例 |
| 自由な操作語の構文等値 | 恒等除去、平坦化 | 操作名と順序を持つ正規形 |

これらの数学的手続きは、計算資源を制限しなければ停止して正確な結果を返す。
有限 context 上の構成条件・自然性・貼り合わせ・比較条件の検査もこの責務に含む。
実行予算の消尽は `interrupted` とし、有限だが大きい計算を非対応へ変更しない。

一般の非線形整数可解性、無限提示の操作合同、一般アフィン作用の任意長到達可能性、
任意の無限構文族の意味保存については、対応する算法を備えない問いを
`unsupported_algorithm` とし、型、原式、量化域、必要な判定を保持する。
有限全列挙で尽くせる追加条件は列挙する。整数不等式など、上表で定めない無限域の条件は、
アフィン等式の torsor に置換しない。

宣言の解釈、equation realization、局所状態、作用、写像とその正確性は核の責務である。
上表の構成や一般数学の適用条件を、利用者からの証明・判定フラグで補う入力経路は設けない。
