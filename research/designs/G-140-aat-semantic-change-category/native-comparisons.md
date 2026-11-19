# 既存の意味圏、全Hom、商修復との比較

## 定理 D1 — Lensの全Homと非可逆射

view `V` の一点を選んだtotal lensはG-139 N4.1により `K×V` と同型であり、

```math
\operatorname{get}(k,v)=v,\qquad
\operatorname{put}((k,v),w)=(k,w).
```

二つの積lens間の相対射はview map `u:V→V'` とstate map `h:K×V→K'×V'` でget/putを保つものとする。get保存から第二成分は `u(v)`。put保存を `((k,v),w)` に適用すると第一成分は `v` に依存しない。従って全Homは

```math
h(k,v)=(a(k),u(v)),\qquad a:K\to K'
```

で尽くされる。逆に全ての `a,u` は二式を保ち、合成は `(a',u')(a,u)=(a'a,u'u)` である。

`V=Bool`、同じview上の `u=id` を固定する。`K'=1` のlensを `V` と同定すると、唯一の `a:K→1` に対応する射は

```math
p:K\times V\to V,\qquad p(k,v)=v.
```

getは `id·p=get`、putは `p(k,w)=w=put_V(p(k,v),w)` により保存される。`K` が二つ以上の元を持つなら、同じ `v` の上の二状態が同じ像を持つので `p` は単射でなく、lens同型でもない。`K=∅` なら同じ分類の射は非全射となる。全Homの定義はこれらの両方を保持する。

G-139 N4.3のcopying解釈はget/put・射影・基準値と `h` の同じ式を運ぶ。全Homは係数化したhidden coalgebra間の全mapに対応し、B3の表示で全profileを保持する。connected非零環、特にnative比較の `Z` では元の全 `a,u` を回復し、合成も同じ関数合成になる。非連結環での冪等分割のmapはそのまま追加の係数点として残す。空viewの場合はG-139 N4.1の空担体の分類を用いる。

## 定理 D2 — Protocolの全自然変換と同じgeometry query

phaseの圏 `J` と観測protocol `O` を固定する。protocolは原始状態・操作から作るfunctor `A:J→E` と観測自然変換 `o_A:A→O` である。比較は全ての自然変換 `h:A→B` で `o_Bh=o_A` を満たすものとする。

各頂点の実際のmapを選び、各生成辺の自然性正方形と観測式を課す。pathについてはA2の帰納法により自然性が従う。逆に自然変換はまさにこの全dataを持つ。従ってB3の全Hom表示はslice functor圏 `[J,E]/O` の全Homと同値である。比較groupoidを作るときだけこれらの可逆なものを取る。元のprotocol射を自然同型だけに制限しない。phaseを変える場合はA3の頂点・path翻訳もdataに含める。

G-124との比較は同じquery `edge(S,T,x,y)` を使う。connected非零環でcopyingの係数をBoolean値0/1と読むと、activeな行の直交・和1は `∀x ∃!y` となり、非activeな行はfalseとなる。従って既存の `IsTyped`・`IsTotal` と一致する。graphを読むmapと、その唯一の `y` を返すassemblyは互いに逆である。

合成query `edge(α,γ,x,z)` を評価するとき、指定された最初のmapの中間値 `y` を読む。`edge(α,β,x,y)` と `edge(β,γ,y,z)` の二queryで合成値が決まる。これが既存 `compose_finite_support` と同じ、modelごとのsupportである。全modelに共通する有限query集合はG-139 N3.2の反例により存在しない。B3の全profileはこの区別を保つ。

geometryの対象・射についてはG-139「G-124のgeometryとの比較」の原始宣言を用いる。package map、係数環射、全context action、raw map、realization成分を同じdataとして保持し、原始式をB3で係数化する。nativeでgraphを戻して既存のassemblyを適用すれば、representative modeの `GeomReadCategory` とexplicit modeの `ExplicitExactGeomCategory` の全Homを回復する。explicit modeのraw map等を観測値だけで商にしない。恒等・合成は同じfieldの関数合成から作られる。

## 定理 D3 — G-126の商修復fiber

集合 `S`、全域操作系 `T=(step_e:S→S)_(e∈E)`、観測 `o:S→O` を固定する。G-126の `eval` はA2と同じ左からの有限語評価である。操作stableな同値関係をcongruenceと呼び、要求関係 `R⊆S×S` を含む最小congruenceを

```math
\theta_R=\bigcap\{c\mid c\text{ はcongruence},\ R\subseteq c\}
```

とする。behavior関係を

```math
x\,\beta_o\,y
\iff
\forall w,\ o(\operatorname{eval}_T(x,w))
 =o(\operatorname{eval}_T(y,w))
```

と定める。各語の観測のkernelの交差なので同値関係であり、各語の前に `e` を付ければ操作stableである。空語から `β_o⊆ker(o)`。逆にcongruence `c⊆ker(o)` は語の帰納法により `c⊆β_o`。従って `β_o` は観測を保つcongruenceの最大元である。

商修復とは、全射 `q:S↠Q`、降下した全操作・観測、可換式、要求 `R` の同一視を持つdataである。`ker(q)` はcongruenceで `θ_R≤ker(q)≤β_o`。逆に `θ_R≤c≤β_o` なら、集合商 `S/c` 上で `[x]↦[step_e(x)]` と `[x]↦o(x)` がwell-definedであり、全射 `q_c` を持つ商修復を得る。全射のfiberで分類すれば、元の `Q` と `S/ker(q)` は操作・観測を保って同型になる。

二つの修復間に `f q=q'` を満たす射がある条件は `ker(q)≤ker(q')` である。必要性は式から従い、十分性では `f(qx)=q'x` と置く。well-defined性はkernel包含、全域性と一意性は `q` の全射性、操作・観測保存はその可換式から従う。よってこの全Homを含む修復圏は区間 `[θ_R,β_o]` の順序圏と同値になる。特に

```math
\operatorname{Repair}(T,o,R)\ne\varnothing
\iff \theta_R\leq\beta_o
\iff R\subseteq\beta_o.
```

### D3.1 — 共通behavior上端の組立て

同じ `S,T,o` に対する任意の要求族 `(R_i)` について

```math
\theta_{\bigcup_iR_i}=\bigvee_i\theta_{R_i}.
```

実際、各 `θ_(R_i)` を含むcongruenceと、全 `R_i` の合併を含むcongruenceは同じである。その最小元を取れば等式を得る。従って各要求が修復可能なら各 `θ_(R_i)≤β_o` であり、同じ上端へのsupremumも `β_o` 以下となる。合併要求の修復を商構成から得る。逆は要求の包含により明らかである。有限性もmatching選択も必要としない。

これは既存の `generated_requestUnion`、`repairable_requestUnion_iff` と同じ証明内容であり、前提は**共通の操作系と観測**である。異なるadapterへの自然性を解く条件を、この上端条件に読み替えることはできない。

## 定理 D4 — 同じ入力上のadapter比較

各 `n∈N` に `S_n=Bool×Z` を置き、

```math
u_t(b,z)=(b,z+t),\quad
v(b,z)=(\neg b,z),\quad
o(b,z)=b,\quad
h_n^a(b,z)=(b,2z+a_n)
```

とする。`h_n^a:S_(n+1)→S_n` は `h_n^a u_t=u_(2t)h_n^a`、`h_n^a v=vh_n^a` を満たすので、語翻訳 `u_t↦u_(2t),v↦v` を持つ意味保存射である。

各段の全操作・観測を保つmap `f_n:S_n→S_n` を分類する。観測保存から `f_n(b,z)=(b,F_b(z))`。全 `u_t` の保存に `z=0,t=z` を用いて `F_b(z)=z+c_b` を得る。`v` の保存から `c_0=c_1`。従って全ての `f_n` は `f_n(b,z)=(b,z+c_n)` で尽くされる。

指定adapter列 `h^0` から `h^a` への比較には自然性

```math
f_nh_n^0=h_n^af_{n+1}
\quad\Longleftrightarrow\quad
c_n-2c_{n+1}=a_n
```

が必要十分である。全mapを分類してから式を課しているので、解がないときtermで表せない別の比較が残ることはない。

`a_(2j)=1,a_(2j+1)=0` とする。二式をまとめると `c_(2j)−4c_(2j+2)=1`。反復して

```math
3c_0+1=4^m(3c_{2m}+1)\qquad(m\geq1).
```

左辺は全ての `4^m` で割り切れる整数なので零でなければならず、`c₀=−1/3` は整数でない。従って全adapter比較fiberは空である。有限prefixでは終端の `c_N` を任意に決めて後ろから解けるので、全ての有限prefixが解を持つこととも両立する。これらの有限解が全体でmatchingするという主張はしていない。

一方、各段の全 `u_t,v` に対して `β_o=ker(o)` である。空語が異なるBool値を区別し、同じBool値の二状態はどの語でも同時に同じ回数だけ反転するからである。`π_n(b,z)=b` は操作を `u_t↦id,v↦neg` として降下させ、全adapterも `Bool→Bool` の恒等へ降下する。従って同じ段の `T,o` に対する、`ker(o)` 以下の任意の要求族はD3.1で同時に修復できる。

全phaseを一つの共通操作系に置く必要があれば、`S=∐_n S_n` に `u_t,v` を各段で作用させ、各adapterをその指定source段では次の段へ、他段では恒等となる全域操作として置く。観測を `(n,b)` とすれば同じkernelへの商が全操作を保つ。ただし `a` を変えれば操作系そのものが変わる。異なる `a` 同士へD3.1の共通 `T` という前提を適用しない。

### D4.1 — 同じ全Homの係数表示

`Z` の加群的解釈を `A¹_R`、Boolを二つの成分 `Bool_R` とし、全translationを `G_a` の作用として保持する。各成分のregular map `F` が作用を保つ条件は `F(x+t)=F(x)+t` という普遍多項式恒等式である。`x=0` を代入して `F(t)=t+c` を得る。反転保存が二成分の `c` を一致させるので、全係数環上でも全Homが同じ `c∈R` で尽くされる。単に `u₁` の保存だけを課してこの結論を使わない。

従って指定adapter比較を表すschemeは

```math
Y_a=\operatorname{Spec}
\mathbb Z[c_0,c_1,\ldots]/(c_n-2c_{n+1}-a_n\mid n\in\mathbb N).
```

原始式から生成したこの表示と独立な全自然変換は全 `R` に自然に同値で、native `Z` では直前の全関数分類に戻る。一般の `h^a→h^b` の式は `c_n−2c_(n+1)=b_n−a_n`。二つの比較の合成はtranslation係数の和、恒等は零であり、この式の加法が合成と一致する。

この例で商修復fiberの非空性を与えるものは `θ≤β_o`、指定adapter比較fiberの非空性を与えるものは全ての漸化式の同時解である。同じ状態・操作・観測を用いても、保持するdataと方程式が異なるため、前者の組立て原理は後者の解の存在を含意しない。
