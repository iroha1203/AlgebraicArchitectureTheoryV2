# 原始入力による診断次元の実現

## D1 — 一つのlocally closed集合

任意可換環 `k`、有限表示 `A=k[x_1,…,x_m]/(F_1,…,F_q)`、`B=Spec A`、有限個の `g_1,…,g_r,h∈A` を取る。`n=max(3,r+1)` とし、`n` 頂点のcycleの辺にsourceを一つずつ置く。各辺sourceはその両端のchartに属し、readoutを順に `0,g_1,…,g_r`、余りを0とする。さらに全chartに属す一つのsource `s_*` を置き、その値を `h` とする。

ambient nerveは全頂点・全辺・全三角形からなるfull 2-skeleton。全支持はこのchart支持からK1の交差で生成する。したがって `s_*` は全cellに属し、辺sourceはその辺と両端だけに属す。各chartは非空である。

任意の幾何点 `bar b` で値を読み、Law値blockをC1で分解する。`h(bar b)` のblockはfull 2-skeletonとなる。これは `H¹=0` である。実際、一頂点を選ぶと、三角形のcycle条件から全edge値がその頂点からの差として書ける。

`a≠h(bar b)` のblockは、readoutが `a` であるcycle辺とその端点からなる部分graphである。cycleの真の部分graphはforestなので、各連結成分に根を取り、辺に沿って値を積分すれば `d⁰` は全射、従って `H¹=0`。cycle全部なら `H¹≅Λ` である。後者の同型は一周和で、そのkernelが `im d⁰` であることは同じ積分で示せる。

一辺の値を0としているので、全辺の値が等しい条件は全 `g_i(bar b)=0`。そのblockが `h` のblockに吸収されない条件は `h(bar b)≠0`。以上から、幾何の係数体と独立な任意の診断係数体 `Λ` について

```math
\dim_\Lambda H^1(C_{\bar b,\Lambda})
=\mathbf1_{V(g_1,\ldots,g_r)\cap D(h)}(b).
```

証明は実際には `H¹` が任意 `Λ` 上で零または `Λ` となることを示している。`r=0` でも三辺全てを0とすれば `D(h)` を実現する。`h=0` なら全点で0、`h` がunitなら `V(g_1,…,g_r)` を実現する。集合または `B` が空の場合も同じ入力と式で成立する。

## D2 — 有限値関数と原始実現scheme

有限個のregular function `a_1,…,a_N` の零・非零条件で定まる有限分割上で一定な、有限値域の `β:|B|→N` を取る。各Boolean atomは

```math
V(a_i:i\in Z)\cap D\!\left(\prod_{i\notin Z}a_i\right)
```

の形である。空のatomを含めてこの有限分割へ細分し、各atomの値 `β_Z` 個だけD1の入力を複製する。nerveとsourceを成分ごとの直和にし、支持は元の成分内に置く。各次数の複体は直和となるため、`H¹` の次元は `Σ_Z β_Z 1_Z=β`。零関数は空の直和で表せる。

実現scheme `B` 自体も原始表示から作る。一つのrank1・一生成元の型 `D` と、unary線形演算 `u_1,…,u_m` を置く。生成元は基底なので、その自己準同型は一意なscalar `x_i` を持つ。加法・scalar倍・合成を使う原始Law `F_j(u_1,…,u_m)=0` を課すと、任意 `k` 代数 `R` 上のmarked実現はちょうど `F_j(x)=0` のtupleとなる。

従ってG-139の独立な全R実現と比較して `M_P≅Spec A=B`。各 `g_i,h,a_i` の多項式代表を原始scalar式として読み、B1によりそのregular readoutが元の元に一致する。代表を変えた差は `(F_j)` に属すため、required Lawを使って全lawful実現上で零となる。同じelementを選んだreadout、root scheme、診断は同じmapで比較される。

## D3 — W2を回収するpseudo-coherent複体は存在しない

`B=A²_(Q,λ,μ)` 上で、W2の三辺sourceの値を `0,λ,0`、全chart sourceの値を `μ` とする。D1より

```math
\beta_1(b)=
\begin{cases}
1&\lambda(b)=0,\ \mu(b)\ne0,\\
0&\text{それ以外}.
\end{cases}
```

もし全点でこの値が `dim_(κ(b))H¹(E⊗^L_(O_B)κ(b))` に一致するpseudo-coherent複体 `E` があれば、その関数は[derived fiber Betti数の上半連続性](https://stacks.math.columbia.edu/tag/0BDI)を持つ。これは局所的なbounded-above有限free分解で、該当する三項のmatrix rankが特殊化時に増えないことからも分かる。

しかし直線 `V(λ)` のgeneric点では `μ≠0` で値1、原点へ特殊化すると値0となる。上半連続な整数値関数の集合 `{β_1≥1}` は閉じているべきだが、ここでは `V(λ)∩D(μ)` が原点を含まない。矛盾である。perfect複体はpseudo-coherentなので、その存在も否定される。

一方、B2の有限root schemeからの定数係数étale層の複体は、B3によりまさにこの全fiberを実現する。診断はこのétale層の幾何を持ち、上の全点の次元条件を満たす `O_B` のpseudo-coherent複体へ置き換えることはできない。
