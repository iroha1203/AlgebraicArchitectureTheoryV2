# 三操作から構成する局所・大域計算

[設計本文 §6](README.md#6-手で確かめられる一周)の原始 Atom から、座標整合性を
局所解の貼り合わせとして構成する。同じ LawModule を固定し、第三の shift が
3、2、未観測である三ケースを追う。以下はこの有限例の数学的構成と検算方法である。

## 1. 二入力と計算の読み

入力 A の全データを次とする。`α,β,γ` は記述をまとめる変数であり、数値は Atom に置く。

```text
subject(p)                   subject(q)                   subject(r)
translation_operation(a)    translation_operation(b)    translation_operation(c)
source(a,p)                  source(b,q)                  source(c,p)
target(a,q)                  target(b,r)                  target(c,r)
shift(a,α)                   shift(b,β)                   shift(c,γ)
```

| ケース | A の shift に関する事実 |
| --- | --- |
| 不成立 | `shift(a,1), shift(b,1), shift(c,3)` |
| 成立 | `shift(a,1), shift(b,1), shift(c,2)` |
| 不足値 | `shift(a,1), shift(b,1)`。c の存在と端点は残る |

L は、本文で省略していた局所化・係数の読みを、次の一般規則として展開する。
三ケースともこの L を用いる。具体的な対象名、patch 一覧、行列、障害値は L に書かない。
ここでの DSL は設計記法であり、`vertex_functions` 等の構成の意味は次節以降で定める。

```text
vocabulary subject(v), translation_operation(e)
vocabulary source(e,v), target(e,v), shift(e,k:Q)
derive vertices = atoms(subject)
derive edges = atoms(translation_operation)
derive endpoints(e) = required(source(e), target(e))
interpret term(e) = (x:Q) -> x + required(shift(e))

context subgraph = endpoint_closed_subsets(vertices, edges)
context operation_support(e) = closure({e}, endpoints)
coverage coordinate_cover(W) = operation_support(e) for each e in W
                               plus singleton vertices of W not on an edge

equation coordinate(e,z) = z[target(e)] - z[source(e)] - required(shift(e))
coefficient M(W) = kernel(vertex_functions(W,Q) -> edge_differences(W,Q))
state S(W) = solutions(z : vertex_functions(W,Q), coordinate(e,z)=0 for e in W)
restriction = restrict_vertex_values

law path_preservation required:
  forall (first,second,direct) in endpoint_generated_triangles:
    compose(term(second),term(first)) = term(direct)
query coordinate_compatibility:
  solve coordinate(e,z)=0 for all e in edges
reading coordinate_descent = local_solutions_and_differences(S,M,coordinate_cover)
```

Law の `coordinate` は座標変数 z への要求式であり、z や局所解を入力しない。
存在が記録された操作に必須値が欠けていても、その操作と方程式を落とさない。
端点の型と参照先、各原始フィールドが単一値であることを確かめ、欠落は未決、
相反する単一値の提示は入力の不整合として区別する。

## 2. Atom から Context と cover を作る

操作 Atom の参照から、有向辺 `a:p→q, b:q→r, c:p→r` を生成する。
名前付き操作を保持するので、同じ端点の別操作も別の辺になる。
context W は、辺を含めるとその端点も含む有限な部分graphである。
辺の原始フィールドはその辺に、subject の事実はその頂点に伴う。

`Supp(W)` はこの閉包に属する原始 Atom、`Ax(W)` は座標整合性の軸、
`Obs(W)` は頂点座標・辺の shift・各辺の方程式とする。
この例には18個の部分graphがあり、包含を射とする有限圏をなす。
空部分graphも含め、重なりは集合の交差として計算できる。
包含射について交差の二つの射と一意の因子分解があるため、これが pullback である。

L の `operation_support` を各辺へ適用すると、次を得る。

| 生成 context | 頂点 | 辺 | 局所方程式 |
| --- | --- | --- | --- |
| `U_a` | p,q | a | `z_q-z_p=α` |
| `U_b` | q,r | b | `z_r-z_q=β` |
| `U_c` | p,r | c | `z_r-z_p=γ` |
| `U_a∩U_b` | q | なし | なし |
| `U_a∩U_c` | p | なし | なし |
| `U_b∩U_c` | r | なし | なし |
| `U_a∩U_b∩U_c` | なし | なし | なし |

cover の生成条件は、頂点と辺の双方を union で覆うことである。
`{U_a,U_b,U_c}` は全体 W の全頂点・全辺を覆うので、L から生成された cover になる。
union による cover は恒等を含み、交差への引戻しと cover の合成で保たれる。
したがって、この包含圏上の Grothendieck topology を定める。

適用する equation family を、各辺の `coordinate` からなる `E_coord` と明示する。
各 equation の全 operand と residual は対応する U_e で読め、頂点の共有値は重なりで読める。
必要な Atom・equation・axis の支持を覆い、制限に残る支持も保つので、
この cover はこの座標整合性の読みについて adequate である。
ここで数値の equation まで確認できるのは shift が既知の二ケースである。
不足値のケースでも幾何の cover は生成できるが、数値 residual の評価に必要な
原始事実が欠けていることを保持し、その評価まで完了したとは扱わない。

同じ L の `path_preservation` は三操作全体を参照するため、全体 W で別に評価する。
この三patchがその三操作同時の支持まで一patchに含むとは主張しない。
経路の三角形を発見する join と、cover の三重交差は別の構成である。
三角形を理由に二次元セルや非空の三重交差を追加しない。
経路保存の residual と座標障害の対応は §6 で実際に求める。

## 3. 係数と局所状態を構成する

### 3.1 係数 M と制限

任意の生成 context W について、その頂点・辺をそれぞれ V_W、E_W と書く。
原始端点から次の線形写像を生成する。

```math
D_W:\mathbb Q^{V_W}\longrightarrow\mathbb Q^{E_W},\qquad
(D_Wh)_e=h_{t(e)}-h_{s(e)}.
```

係数を `M(W)=ker D_W` と定める。つまり、W の各辺の両端で等しい頂点関数である。
これは原始 incidence から作る係数であり、全体の可解性を使っていない。
`W'⊆W` の制限は頂点関数の通常の制限である。
W' の辺は W の辺でもあるので、`M(W)→M(W')` が定まり、恒等・合成を保つ。

各 U_e は一本の辺で連結しているため `M(U_e)≅Q`、各非空の重なりでも `M≅Q`。
これらの同型は定数関数の値を読む写像であり、patch から端点への制限は恒等行列 `[1]` になる。
`M(∅)=0` で、空集合への制限は零写像である。
一般の W では連結成分ごとに値が自由であり、成分自体も incidence から計算できる。

### 3.2 局所状態 S と層条件

shift が既知の場合、原始値の制限 `b_W=(shift(e))_(e∈E_W)` を作り、

```math
S(W)=\{z\in\mathbb Q^{V_W}\mid D_Wz=b_W\}
```

と定める。制限はやはり頂点値の制限であり、辺の方程式を保存する。
この有限例では `M` と `S` の層条件を次のように直接確認できる。

1. cover 上の局所値が重なりで一致すれば、各頂点の値を一意に決められる。
2. 各辺は少なくとも一patchに含まれるため、貼り合わせた値もその辺の方程式を満たす。
3. 全頂点が覆われるので、貼り合わせは一意である。

M では右辺0、Sでは原始 shift を使うだけで、同じ議論がすべての union cover に適用できる。
空contextでは S は空関数一つを持つ。
各一本辺patchの局所解は、source を0、target を shift とすれば構成できる。
孤立頂点にも値0を置けるため、局所解の存在も入力フラグでなく構成から得られる。

`M(W)` は `S(W)` に加法で作用する。二つの解の差は M に属し、差による移動は一意なので、
S が非空の context では自由かつ推移的な作用になる。
S の大域切断が空でも局所非空性は保たれ、M の torsor sheaf として扱える。
ここではこの作用と層条件を具体化したので、局所差の類が零なら補正して貼り合わせられる。

## 4. 局所解から微分と具体的障害類を作る

cover の順を `(U_a,U_b,U_c)`、重なりの順を `(ab,ac,bc)` に固定する。
これは行列表示のための順序であり、入力した所属や判定ではない。
source の値を0とする局所解を、辺ごとに原始 shift から作る。

```text
s_a = (p:0, q:α)
s_b = (q:0, r:β)
s_c = (p:0, r:γ)
```

[AAT 第X部 §2](../../aat/algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md)
の increasing-index Čech complex を用いる。係数と重なりの計算から、

```math
C^0=\mathbb Q^3,\qquad C^1=\mathbb Q^3,\qquad C^2=M(\varnothing)=0
```

を得る。制限が `[1]` なので、微分は次の行列として生成される。

```math
d^0=B=\begin{pmatrix}-1&1&0\\-1&0&1\\0&-1&1\end{pmatrix},
\qquad d^1:\mathbb Q^3\longrightarrow0.
```

従って `d¹d⁰=0`。全 ordered tuple 版では重複添字があるため C² を0とは置かない。
ここでの cover は包含による monomorphic cover であり、`M(∅)=0`、
`S(∅)` は一点なので、第X部補題2.1Aの正規化によってその H¹ とも対応する。

局所解の差を、各重なりへ制限して生成する。

```math
c_{ij}=s_j|_{U_{ij}}-s_i|_{U_{ij}},\qquad
c=(-\alpha,\ 0,\ \gamma-\beta).
```

具体的には q で `0−α`、p で `0−0`、r で `γ−β` を計算した値である。
`d¹c=0` なので `c∈Z¹`。対象に付随する障害は空間の次元でなく
`[c]∈Čech H¹(𝒰,M)=Q³/im B` である。

局所解を `s_i+t_i` に変えると、差は `c+Bt` になるため、類は変わらない。
線形汎関数 `μ=(-1,1,-1)` は `μB=0` を満たす。
B の rank は2、μは全射なので `ker μ=im B`。よって商を Q へ同定する写像が得られ、

```math
[c]\longmapsto\mu c=\alpha+\beta-\gamma
```

となる。この商の同定も計算結果であり、障害値として入力しない。

## 5. 零類と大域解の対応を構成する

`c=Bt` を解けたとき、各局所解を `s_i−t_i` へ補正する。
重なり上の差は `c−Bt=0` なので、§3の層条件によって大域的な頂点値 z が得られる。
補正は M による定数移動だから、各辺の方程式も保存する。

逆に大域解 z があれば、`s_i−z|_(U_i)` は M(U_i) に属する定数 `t_i` であり、
重なりで `c_ij=t_j−t_i` となる。従って `c=Bt` を得る。
この両方向の構成により、この例では

```math
[c]=0\quad\Longleftrightarrow\quad S(W)\ne\varnothing
```

が成立する。局所解の存在、補正の作用、層条件を先に確かめたことがこの同値を支える。
大域解を得たら、原始辺の方程式 `D_Wz=b_W` に代入して確認する。

## 6. 元の線形計算との比較

全体 W の頂点を `(p,q,r)`、辺を `(a,b,c)` と並べると、原始端点から

```math
D=\begin{pmatrix}-1&1&0\\0&-1&1\\-1&0&1\end{pmatrix},
\qquad b=(\alpha,\beta,\gamma),\qquad\lambda=(1,1,-1)
```

を得る。これが本文の `Dz=b` であり、`λD=0`。
Čech の B は patch 定数から overlap への写像なので、D と始域・終域が異なる。
次の写像を実際に構成して比較する。

```math
T(u,v,w)=(-u,0,w-v),\qquad
R(z_p,z_q,z_r)=(-z_p,-z_q,-z_p).
```

T は局所解の差の式を任意の辺値へ適用する線形写像であり、`Tb=c`。
R は各辺で source 値を引いて局所解を正規化する操作から得る。
直接計算で

```math
TD=BR,\qquad \mu T=\lambda
```

が成立する。`ker λ=im D` と `ker μ=im B`、両汎関数の全射性により、T は

```math
\operatorname{coker}D\ \xrightarrow{\ \sim\ }\ \check H^1(\mathcal U,M),
\qquad [b]\longmapsto[c]
```

を誘導する。これは商上の同型であり、T や R 自体を同型とは言わない。
実際、T は rank 2、Rも rank 2 である。

同じ L の経路保存では、端点の join から得た `(a,b,c)` に対し

```math
(x+\alpha)+\beta-(x+\gamma)
=\alpha+\beta-\gamma=\lambda b=\mu c
```

を得る。こうして経路の residual、元の線形不成立証拠、局所差の障害類が
この具体例では同じ値に対応することを、導出した比較で確かめられる。

## 7. 三ケースと次に必要な情報

| ケース | 局所差 c | 障害類の座標 μc | 出力と根拠 |
| --- | --- | --- | --- |
| `α=β=1, γ=3` | `(-1,0,2)` | `-1` | `Refuted`。`μB=0, μc=-1` なので補正なし。`λD=0, λb=-1` も同じ不成立を示す |
| `α=β=1, γ=2` | `(-1,0,1)` | `0` | `Established`。`t=(0,-1,0)` で `Bt=c`。補正後は `(p:0,q:1)`、`(q:1,r:2)`、`(p:0,r:2)` となり `z=(0,1,2)` に貼り合う |
| `shift(c)` 未観測 | 有理数値として未構成 | 未決 | c の存在と端点を保持し、`shift(c)` の追加観測を要求する |

不足値でも、context・cover・係数M・B・H¹の構成には shift を使わないため、そこまでは進める。
`γ=t` と形式的に置けば `c(t)=(-1,0,t−1)`、`μc(t)=2−t` と依存を説明できる。
これは未観測値を決めたことではなく、各補完についての式である。
`t=2` と `t=3` の補完で判定が異なるため、現在の入力では零・非零のいずれも確定しない。
未観測値を0へ補完したり、`2−t` が零多項式でないことから不成立を返したりしない。

全三ケースで `dim H¹=1` のままである。対象の障害類と、係数・coverが定める空間を
区別することが、修正後に同じ幾何上で零類を得るために必要になる。

## 8. 何を生成し、何を確かめたか

| 段階 | 生成元 | この例で確認する条件 |
| --- | --- | --- |
| 辺・context | 操作の存在と端点、Lの閉包規則 | 型、参照、端点閉包 |
| cover・overlap | 操作support、unionと交差 | 全頂点・全辺の被覆、pullback、座標の支持 |
| 係数・制限 | 端点差の核、頂点値の制限 | 線形性、恒等・合成、層条件 |
| 局所状態 | 原始shift、source値0の構成 | 各辺の式への代入、局所非空性、Mの作用 |
| 微分・cocycle | 制限写像、局所差 | `d¹d⁰=0`、`d¹c=0`、局所解の選択独立性 |
| 障害・大域解 | 商、補正、頂点値の貼り合わせ | `ker μ=im B`、零類と大域解の両方向 |
| 線形計算との比較 | 正規化と局所差の線形化 | `TD=BR`、`μT=λ`、商上の同型 |

これは[AAT 第IV部 §5](../../aat/algebraic_geometric_theory/part_4_obstruction_cohomology.md)
の torsor-normalized mismatch と、[第X部 §2](../../aat/algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md)
の cover-relative Čech complex を、この二入力から具体化した例である。
得られる大域状態は、この例で定義した座標 z である。

SAGA の意味側・方程式側を独立に生成する presentation、primary state correspondence、
実装の状態への対応は、この例の D と B の比較とは別に構成を要する。
sheaf cohomology との比較や任意の reading の保存、DSL処理系・生成算法の一般的健全性も、
ここでの有限計算とは別の証明・実装対象である。

## 9. 行列と三ケースの独立検算

次は文書に表示した写像の算術を検算する標準Pythonの短い例である。
エンジンの入力形式やDSL評価器ではなく、§§4–7の等式を第三者が再計算するためのものとする。
行列をここへ記述することは、設計上のエンジンへ完成行列を入力することとは区別する。

```python
from fractions import Fraction as F

def mv(a, x):
    return tuple(sum(F(v) * w for v, w in zip(row, x)) for row in a)

def mm(a, b):
    return tuple(tuple(sum(F(a[i][k]) * b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))

D = ((-1, 1, 0), (0, -1, 1), (-1, 0, 1))
B = ((-1, 1, 0), (-1, 0, 1), (0, -1, 1))
T = ((-1, 0, 0), (0, 0, 0), (0, -1, 1))
R = ((-1, 0, 0), (0, -1, 0), (-1, 0, 0))
mu, lam = ((-1, 1, -1),), ((1, 1, -1),)
assert mm(T, D) == mm(B, R)
assert mm(mu, T) == lam
assert mm(mu, B) == mm(lam, D) == ((0, 0, 0),)
# 上二行・左二列の小行列式は両方1。非零な左零化子と合わせてrankは2。
assert D[0][0]*D[1][1] - D[0][1]*D[1][0] == 1
assert B[0][0]*B[1][1] - B[0][1]*B[1][0] == 1

for gamma, obstruction in ((3, -1), (2, 0)):
    b = (1, 1, gamma)
    c = mv(T, b)
    assert c == (-1, 0, gamma - 1)
    assert mv(mu, c) == mv(lam, b) == (obstruction,)
    print(gamma, tuple(map(int, c)), obstruction)

t, z = (0, -1, 0), (0, 1, 2)
assert mv(B, t) == mv(T, (1, 1, 2))
assert mv(D, z) == (1, 1, 2)
# 未観測gammaの二つの補完が異なる判定を与える。
assert mv(lam, (1, 1, 2)) != mv(lam, (1, 1, 3))
print("comparison, correction, and distinct completions: OK")
```

出力は次となる。

```text
3 (-1, 0, 2) -1
2 (-1, 0, 1) 0
comparison, correction, and distinct completions: OK
```
