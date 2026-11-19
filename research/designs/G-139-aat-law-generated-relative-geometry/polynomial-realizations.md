# 同じ原始入力による多項式特殊化

## P0 — 入力

`k` を可換環、`V` を有限sort集合、各sortに自然数 `0≤n_v≤m_v` を与える。演算族 `E` とLaw族 `L` は任意に小さくてよい。演算は有限入力列から一つの出力へのtensor-linear mapであり、0入力のtensorは `k`。Lawは同じ型を持つ二つの有限tensor式の等式である。式の構成子は演算、恒等、tensor、置換、合成、有限和、scalar倍。required・optional・derivedのroleを保持し、実現にはrequired Lawを課す。

宣言contextは、参照に関して閉じた部分宣言であり、一つのsortを含めたらその階数と全名前付き生成元を含める。宣言被覆は合併が元の宣言になる族。この入力は [n1020 §3](../../../docs/note/n1020_shigure_polynomial_specializations.md#3-原始入力と独立な実現) と同じである。

## 定理 P1 — 独立なSem・Realと係数変更

`Sem_P(R)` は、各 `K_v⊆R^(m_v)` と有限局所自由で一定rank `n_v` の商 `Q_v=R^(m_v)/K_v`、その上の型付き演算でrequired Lawを満たすものの集合とする。同じkernelと同じ商上の演算を同じ元とする。

別に、全射 `q_v:R^(m_v)↠Q_v` を持つ実現を定義する。そのkernelと第一同型定理で `Sem` に移る。逆に標準商射を付ければ戻る。二つの全射付き実現が同じkernelを持つとき、`q_v(a)↦q'_v(a)` は一意な同型であり、演算を保つ条件は商上で同じ演算であることと同値。従って両記述は同値である。

`Mod_P(R)` は全射を持たない有限局所自由module実現の圏とし、全ての線形operation保存mapを射とする。非可逆なmapを含める。0入力operationについても選択値保存を課す。最大部分groupoidを `Real_P(R)` とする。いずれもscheme点や群作用を使わず定義された。

環射 `R→R'` には `Q'_v=Q_v⊗_R R'` とtensorした演算を対応させる。`Q_v` がprojectiveなので `0→K_v→R^(m_v)→Q_v→0` は分裂する。その分裂をtensorすれば再び分裂完全列である。従って新しいkernelは `K_v⊗R'` の `R'^(m_v)` 内の像、商は `Q'_v`。この像は分裂の選び方に依存せずkernelとして決まる。flatnessは不要である。

式の値はpure tensor上でscalar extensionと可換で、pure tensorが全体を生成するので全ての式・Lawに成立する。tensorの単位・結合同型はpure tensorを同じ値へ送るため、identity・composition・pentagon・triangleが成立する。`Sem` では標準kernel記述により関手、`Real` と `Mod` ではこのcanonical同型を持つ擬関手になる。

## P1a — 五座標、raw tuple、全contextの方程式

### 構成 P1a.1 — 宣言のencodeとdecode

sort名、生成元名、演算名、Law名と構文木内の有限pathをtag付きの集合とする。payloadは、階数対、入出力型列、role、型付き有限式、それらの出現の直和である。Atom五座標を次で生成する。

| kind | axis | subject | predicate | payload |
| --- | --- | --- | --- | --- |
| sort | state | `v` | ranks | `(n_v,m_v)` |
| generator | state | `(v,a)` | type | `v` |
| operation | operation | `e` | signature | `(v₁,…,vᵣ;w)` |
| equation | law | `ℓ` | `role_ℓ` | `lhs_ℓ=rhs_ℓ` |
| occurrence | law | `(ℓ,path)` | constructor | その有限構文node |

configurationのrelationは宣言の参照edge、identificationは同じ名・同じ出現の等号として生成する。tagとpathから有限構文を根から再帰的に読み戻せるので、宣言のdecodeとencodeは互いに逆である。

基底chart `I` を固定する。後述するraw座標集合を `Z_I`、ambientを `B=k[z | z∈Z_I]` とする。全小さい `k` 代数 `R` のcarrierと元のtag付き直和 `⨿_R |R|` を一段大きいuniverseで取る。これを共通payloadに含め、以後の `E_B,E_x` は同じ `AtomCarrier U`、同じbase object、同じcontext categoryを使う。任意 `R` とraw tuple `a:Z_I→R` に、追加Atom

```text
(value, coefficient, z, equals, (R,a_z))
```

を一つずつ付ける。任意object `A` について、各 `z` に対するこの形でtagが `R` の値Atomがちょうど一つならその値を `decode_R(A)_z` とする。どれか一つでも欠落または非一意なら、tuple全体を零にする。他の環のtagはこのdecodeでは読まない。従ってdecodeは共通carrier上の全objectについて定義される。raw tupleは全関数 `Z_I→R` であり、無限個の演算係数に有限supportは要求しない。

`encode_R(a)` のconfigurationは宣言Atomとこのgraphを持つ。`StructureMaps` はraw係数型と選択値 `a`、`SelectedQuantities` は対応する選択量を持つ型と値を保持する。decodeは動的な型の同一視ではなくgraphから読むため、明らかに `decode_R(encode_R(a))=a`。環射 `R→R'` はgraphのpayloadを送るので、encode像上で `decode_(R')(encode_(R')(f(a)))=f(decode_R(encode_R(a)))`。不正なobject一般におけるdecode自然性は主張しない。

### 構成 P1a.2 — 全AAT contextの係数

ambient `Spec B` の各点 `p` を表すtag付きAtom `point(p)` も用意し、それら全てを固定base object `A₀` のfamilyに含める。各ArchitectureContext `W` に

```math
S_W=\{p\mid\exists s\in W.\mathrm{Support},\ W.\mathrm{supportReads}(s,\mathrm{point}(p))\},
\qquad U_W=\operatorname{Int}(S_W)
```

を対応させる。`contextMorphismPreorderCategory A₀` の射 `W→V` はsupportReadsを保存する実際のmapを持つから `S_W⊆S_V`、従って `U_W⊆U_V`。係数を **全** `W` で `Γ(U_W,O_(Spec B))` とし、restrictionはsheafの制限とする。恒等・合成則はsheafの関手性である。

任意open `U⊆Spec B` に対し、Supportを `U` の点、readsを対応する `point(p)`、AxisとObservableを一点型・全てreadable、Extensionを一点型とするcontext `W_U` を作れる。これで `U_(W_U)=U`。包含はSupportの包含、他のmapは一意のmapとして `IsRestriction` の四条件を満たす。従ってopenの圏から全contextへの関手があり、principal open上では係数は `B_s`。`D(1)` と空openが含まれる。標準product contextでは点supportが共通部分になり、`Int(S∩T)=Int(S)∩Int(T)` からopenの交差も保つ。

raw point `x:B→R` に対しては、同じcontext添字を使い `U_W` の逆像上の `Γ(x⁻¹U_W,O_(Spec R))` を係数とする。scheme射のsheaf mapが全contextで評価を与える。principal openでは

```math
B_s\longrightarrow R_{x(s)},\qquad b/s^n\longmapsto x(b)/x(s)^n.
```

任意openで単純に `Γ(U_W,O)⊗R` と置き換えない。B4がこの区別とsheaf化の比較を証明している。

### 定理 P1a.3 — 普遍残差と原始評価

tensor式の評価はchartのbasis上で有限成分多項式を与える。Law `ℓ` の差の全成分を `f_(ℓ,α)∈B` とする。`ArchitecturalEquationSystem` のindexは `(ℓ,α)`、roleは元のrole。各成分に対応する一個のLaw Atom `a_(ℓ,α)` を追加し、そのAtomにおけるsymbolic coordinateを `f_(ℓ,α)` の制限、他のAtomでは零とする。

評価系 `E_x` のsymbolic coordinateは、指定Law Atomで `x(f_(ℓ,α))` の逆像openへの制限、他Atomでは零とする。普遍系 `E_B` のobject-dependent residualは、指定Law Atomで `f_(ℓ,α)(decode_B(A))` の制限、評価系 `E_x` では `f_(ℓ,α)(decode_R(A))` の逆像openへの制限とし、両方とも他Atomでは零とする。どちらもまず大域元を作って制限するため、任意object・任意Atomでrestriction式が成立する。`a_univ=encode_B((z))` と `a_x=encode_R((x(z)))` では

```math
f_{\ell,\alpha}(\operatorname{decode}_B(a_{\rm univ}))=f_{\ell,\alpha},\qquad
f_{\ell,\alpha}(\operatorname{decode}_R(a_x))=x(f_{\ell,\alpha}).
```

これは式の構成子に関する帰納法であり、同じ環射 `B_s→R_(x(s))` により両残差が対応する。

原式の全required Lawが成立すれば、その全成分は零なので全context・全Atomで残差零となる。逆に `EquationLawful(E_x,a_x)` は `D(1)` のcontextと各指定Law Atomで `x(f_(ℓ,α))=0` を与える。基底成分が全て零ならtensor mapの差が零である。よって**全raw tuple**について

```math
\operatorname{EquationLawful}(E_x,a_x)
\iff\text{原式の全required Lawが成立する}.
```

全roleを要求する `FullyEquationLawful` には全roleの原式を対応させる。この二predicateを混ぜない。個別Lawはrequired側の生成ideal `J=(f_(ℓ,α))` に入れ、既存 `StructuralRelationFamily` を併用するなら空族とする。

conormalは普遍ambientで `J/J²` を作り、Lawfulな `x` に沿って `(J/J²)⊗_(B/J)R` を取る。評価後に零となったidealから作り直さない。例えば `B=k[t],J=(t²),x(t)=ε` では普遍 `t²` は非零、評価は零、`D(t)` の逆像は空である。

## 定理 P2 — Chart、overlap、scheme、普遍実現

各 `v` の `m_v` 個の生成元から `n_v` 個を順序付きに選び、元の順序を引き継いだ集合 `I_v` とする。`n_v=0` なら唯一の空集合、行列式は1とする。全sortの選択を `I` と書く。

`Sem_(P,I)` は選択列が基底である部分関手。基底で `q_v` の選択列を単位行列にし、残りの列の成分 `x_(v,ab)` と各演算のmatrix成分 `y_(e,αb)` をraw座標にする。0入力operationは出力vectorの座標を持つ。入力または出力rankが零のときも実際のtensor/Homから座標数を決める。原始式の全required成分を `J_I` とし、

```math
A_I=k[x_{v,ab},y_{e,\alpha b}],\qquad
B_I=A_I/J_I,\qquad U_I=\operatorname{Spec}B_I.
```

`U_I(R)≅Sem_(P,I)(R)` はmatrixを読むmapと、自由module・標準列・指定matrixから演算を作るmapによる。Lawの同値は P1a.3。選択列を単位にしたため全射性を追加仮定にせず、`q` のkernelもmatrixから生成する。両mapが逆であることは標準商と全射付き記述の同値から従う。

`I` chart内で `J` の列を並べた行列を `T_v`、`d_IJ=∏_v det T_v` と置く。`J` が基底であるlocusは `D(d_IJ)`。新座標は

```math
q_v^{J}=T_v^{-1}q_v^{I},\qquad
\mu_e^{J}=T_{\rm out}^{-1}\mu_e^{I}
                  (T_{v_1}\otimes\cdots\otimes T_{v_r}).
```

随伴行列の式から全成分は `d_IJ` をinvertした環内にある。任意tensor式 `τ` は構成子についての帰納法で同じ変換式を満たす。合成では内側の `T T⁻¹` が消え、tensor・和・scalar倍では式が分配される。従って残差も同じ可逆変換を受ける。その全成分の生成idealは両包含が逆変換から得られ、一致する。

この式から `B_J[d_JI⁻¹]≅B_I[d_IJ⁻¹]`。逆変換は `T_v⁻¹`、三重overlapの変換は `I→J→K` の行列積と `I→K` の列matrixが一致するのでcocycleを満たす。これは接着可能性をfieldとして入力に置いたものではない。

これらのopen同型でscheme `M_P` をglueする。各 `U_I` 上の自由moduleと全射列、operationは同じ行列式で貼り合わさり、普遍実現を与える。全required Lawは局所的に零なので大域的にも零である。

任意実現の各剰余体上で全射 `κ(p)^(m_v)↠Q_v⊗κ(p)` の列から基底を選べる。全sortは有限個なので同時に選べる。選択列mapの行列式が非零となる点の近傍で基底になるため、これらの基底openが `Spec R` を覆う。よって実現から局所 `U_I` へのmapを作れ、overlap式によって `M_P` へglueする。逆に普遍実現を引き戻せば元のkernel・演算が戻る。全scheme mapについてもchart上で同じことが言えるので

```math
\operatorname{Sem}_P(R)\cong
\operatorname{Hom}_k(\operatorname{Spec}R,M_P)
```

が得られる。これはGrassmannianの基底open構成（[Stacks 089T](https://stacks.math.columbia.edu/tag/089T)）に演算座標とLaw idealを加えた明示的構成である。

### P2.1 — 二種類のdescentと任意base change

宣言被覆上で局所 `K_v` とoperationが共有宣言上で一致すれば、各fieldをそれを含むcontextから読むことで一意な大域実現を作れる。参照に閉じたcontextなので各Lawの有限式はそれを持つcontextで評価され、大域でも成立する。

`Spec R` のZariski被覆ではQC moduleと全mapのdescentで `Q_v,q_v,μ_e` を貼る。局所自由rank、全射性、Lawの零性は局所的性質なので降下する。markingを保つ同型が一意なため `Sem` は集合値sheaf。fppf被覆では同じQC descentとfinite locally free性のfaithfully flat descentで `Real` の対象と全同型を貼れる。非可逆mapについてもB1.2の全Hom descentが適用される。

宣言の忘却はfieldを落とし、係数の制限は残ったfieldをtensorする。二順序で残るfieldとその値が一致するので制限は可換。組立ても、それぞれの局所制限が一致することとdescentの一意性から可換である。

任意 `k→k'` についてraw環は同じ座標で `A_I⊗k'≅A'_I`。各Lawの成分多項式は係数を送った同じ生成元になるので `J'_I=J_I A'_I`。tensorの右完全性で `B_I⊗k'≅B'_I`。行列式と随伴行列も係数変更と可換なのでoverlap同型は同じ式となる。よって

```math
M_{P\otimes k'}\cong M_P\times_{\operatorname{Spec}k}\operatorname{Spec}k'
```

となる。非flatな環射も含み、P1のkernelの像によるbase changeと同じ実現を与える。

## 定理 P3 — Reading射と自然性

reading `u:P→P'` は、階数・生成元数を保つsortの単射、各source operationへの同じ型のtarget tensor式、各source required Lawについてtarget required Lawとtensorの標準等式からの有限導出である。等号はsort対応と代入式の導出可能な等号であり、導出証明自体の違いは区別しない。

target実現に式を評価するとsource実現になる。Lawの導出に関する帰納法でsource required Lawが成立する。式の導出可能な等号は全実現で同じmapを与えるので、この解釈は導出証明の選び方に依存しない。恒等代入は恒等、代入合成の評価は式のsyntax木の帰納で合成に一致する。従って `Sem_(P')→Sem_P`、`Mod_(P')→Mod_P`、`Real_(P')→Real_P` を得る。noninvertibleなmodule mapの式保存も同じ帰納法である。

scheme側では `M_(P')` の普遍実現をこの式で解釈し、P2により `M_(P')→M_P` を得る。chart上ではsource変数を対応するtargetの成分多項式へ送る。同じmatrix、同じ式なので任意base change、普遍実現の引戻し、宣言contextの制限・細分化と可換。恒等・合成は全test点で、あるいは普遍実現で検査できる。

相互に逆な代入は両方向のscheme射の合成を恒等にする。演算を変えずLawだけを追加すると、追加残差の生成idealによる閉部分schemeが得られる。target required Lawにないoptional式を導出前提として使うことは許されない。

### P3.1 — 宣言忘却と係数層の向き

宣言 `V⊆W` の忘却は `Sem_W→Sem_V`、座標環では `B_V→B_W`。open `U⊆U'` の係数制限は `Γ(U',O)→Γ(U,O)`。この二つを同じ射にしない。例えば `Q[x]→Q[x,y]/(xy-1)` は宣言を増やす環射であり、共有 `x` を保つ逆方向の環射は `xφ(y)=1` を要求して存在しない。

### P3.2 — StandardArchitectureSchemeへの限定した比較

既存 `StandardArchitectureScheme.baseChange` は、schemeだけでなく指定 `raw`、reading decoration、context chart、overlap、およびflatな係数変更と `HasSheafCompose` を使うAPIである。その入力に P2 の同じschemeと同じ生成式を格納できるreadingを固定した場合に比較する。任意の既存decorationが自動的に一致するとは主張しない。

この比較の内容は具体的である。指定contextのsectionから大域sectionへの解釈が普遍実現の同じ係数を送り、指定chartが P2 のopen chart、overlapが上で生成した逆行列変換を表すことを検査する。これらの入力について `baseChangeUnderlyingIso` の右辺は実際のscheme fiber productであり、P2.1 の同型と同じ普遍実現を持つ。二つの射は各chartの全生成元で一致するので等しい。decoration・chart・overlapの比較も同じ生成元と局所化の式で可換になる。

sheafificationは小さいsite上の可換代数sheafの標準構成で存在する。`HasSheafCompose` の実際に放電できる係数変更として `k'` が有限projectiveな `k` moduleである場合を取れる。このときtensorはdualizable moduleによるtensorなので全limitを保ち、sheaf条件の等化子と任意積を保つ。従って係数extensionはsheafをsheafへ送り、flatnessも成立する。例えば `k'=k[ε]/ε²` はrank2自由で、非自明な係数変更のこの条件を満たす。一般のflat射に対してこの追加仮定を省略しない。

以上は同じ装飾付き入力でのAPI比較である。P1aの全context係数を各々affine chartと呼ぶ構成は使わない。非affine openにも係数を与えることと、それを `Spec Γ(U,O)` で元のopenへ同定できることは異なる。

## 定理 P4 — 生成元を忘れる商stack

各sortを自由module `k^(n_v)` に固定し、演算の全matrix成分だけを変数にしてrequired Lawの全成分を課したaffine schemeを `X_P` とする。`G=∏_v GL_(n_v)` の作用は P2 と同じbasis変換式。恒等・合成とLaw保存はその計算から従う。

実際の `Real_P(T)` の対象から全frameのtorsor `Fr(Q)` を作る。有限局所自由性によりZariski局所でframeがあり、右 `G` 作用は各frame間で自由推移的。frame上の成分が `X_P` へのequivariant mapを与える。逆にtorsorとequivariant mapから、自由moduleと演算をfppf descentする。Lawは忠実平坦に検出される。frameを再構成すれば元のtorsorに戻り、descended moduleの評価で元の実現へ戻る。mapについても全equivariant torsor mapと全演算保存同型が対応する。従って

```math
\operatorname{Real}_P\simeq[X_P/G].
```

有限積の `GL` はsmoothなので D2 によりalgebraic stackである。

`M_P→[X_P/G]` は全射 `q` を忘れる射。test scheme `T` 上の実現 `Q,μ` による2-pullbackは

```math
\prod_{v\in V}\operatorname{Surj}(\mathcal O_T^{m_v},Q_v)
```

である。これはvector bundle `Hom(O^(m_v),Q_v)` 内のmaximal minorが生成するidealが1となるopen。basisを局所的に選べば標準全射 `[I_n\ 0]` が存在するので、smoothかつsurjective。有限積を取っても同じである。これにより元のmapはrepresentable、smooth、surjectiveとなる。全ての `T` で大域的な全射が存在するという主張ではなく、fppf局所で存在するというsurjectivityである。

inertiaは実際の `Aut(Q,μ)`。marking付きでは `a_v q_v=q_v` と全射性から全 `a_v=id`。この計算と P2 のopen overlapの両方によって、marking付きはschemeとして表現される。

### P4.1 — 非可逆な全Homも保持する

固定された二つの実現 `(Q,μ),(Q',μ')` の間では、有限projective module `H=⊕_v Hom(Q_v,Q'_v)` の全元をまずparametrizeする。D1によりその空間は `Spec Sym H^∨`。普遍map `(h_v)` に全演算について

```math
h_{\rm out}\mu_e=\mu'_e(h_{v_1}\otimes\cdots\otimes h_{v_r})
```

を課す。その成分idealの閉部分schemeは、任意test上でまさに `Mod_P` の全Homを表す。0入力では右辺のtensorは恒等なので選択値保存の式になる。matrixの行列式をinvertしていないため、非単射・非全射も含む。

identityは単位matrix、合成はmatrix積。上の保存式を二段に代入すれば合成保存が従い、単位・結合はmatrixの等式である。有限projective Homのbase changeと式の係数変更から全環射に自然である。自己同型に限定したopen部分がP4のinertiaであり、商stackの同型だけでこの全Homを置き換えていない。

## 定理 P6 — 図式・比較・評価の成分表示

N5の各頂点に P0 の宣言、各生成射に実際の線形sort mapを置く。shapeの各関係に対応するmapの等式、自然変換に対応する正方形、固定部分の比較をrequired Lawとして追加する。語翻訳・補助sort・共有係数は、その許容規則のdataとして保持する。語翻訳が選択肢を持つときは各syntax選択を別の添字とし、勝手に係数値だけへ忘れない。

局所基底を選ぶと各射はmatrix、各relationは有限tensor式の成分等式となる。逆にこれらの解からmatrixの実際のmapを作り、語の合成を評価すれば元の図式を組み立てられる。path関係と自然性の等式がちょうど図式の公理である。基底があるので任意の線形mapに一意のmatrixがあり、term-definable mapだけへHomを狭めない。

有限対象・有限生成射・有限関係のshapeに加えて、各候補chartの係数表示が有限、全Lawを同値な有限族へ還元する**有効な導出**が与えられているとする。全変数を並べ、各構文木を下から評価し、有限個の成分残差を出力すれば有限方程式系を生成できる。小さいfamilyのLawを有限族へ置き換える正当性はその導出を原式に解釈して証明する。反対向きは有限族が元Lawの帰結である導出を使う。この条件の下で、有限系の解と元の全図式補完は同値である。

候補のmatrix `h`、選んだ語翻訳、補助選択、共有係数を同じ解から読み戻す。quantityと評価語も同じmatrix・係数に評価されるので N5.3 により評価が一致する。局所基底を変えた解の比較は P2 の逆行列式であり、全図式mapにも同じ変換を適用して普遍候補をglueできる。

この有限化の条件がない場合は N5 の全小さい表示と各support profileを保持する。有限還元の存在や停止性をG-139の出力とせず、G-141 Dで扱う入力と課題をこの比較から特定する。

## Pと一般構成の同定

moduleの加法・scalar作用・選択値・演算は N1 の原始宣言。setとしての任意状態と全mapはcopying経路で保持される。指定されたmodule係数構造を用いると B1 の `σ` 経路となる。P2のbasis上の演算係数は A1 の独立quantity、tensor残差は同じterm評価で作る `ρ`、`J_I` はその像の生成idealである。

P2のschemeとP4のstackは、D1のdualityから得たframeとD2の作用・torsorの具体例である。P1aのgraphは C1の第一の意味、係数変更は第二の意味、原始有限式の普遍評価は C3の選択されたregular extensionを与える。従って特殊化は別のmodelを外から当てはめたものではなく、同じ宣言・quantity・Law・全射を各構成に通した結果である。
