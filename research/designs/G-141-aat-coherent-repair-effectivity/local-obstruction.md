# 同じ非零障害の整数・Čech・微小liftでの比較

## 定理 C1 — 全有限段の可解性と整数上の不存在

Bの同じadapterに `a_(2j)=1,a_(2j+1)=0` を指定する。有限段では `c_N=0` を選び `c_n=2c_(n+1)+a_n` と後ろ向きに定めれば全て整数である。

全段の整数解があれば、二式から `c_(2j)−4c_(2j+2)=1`。反復して

```math
3c_0+1=4^m(3c_{2m}+1).
```

固定整数 `3c₀+1` が全 `4^m` で割り切れるので零となるが、`c₀=−1/3` は整数ではない。従って `Y_a(Z)=∅`。finite fragmentに制限する実際のmapはB2の座標忘却であり、この反例は同じ全変更のfiberで成立する。

## 定理 C2 — Zariski局所の全解と指定Čech類

`U=D(2),V=D(3)` は `Spec Z` を覆う。`U` 上では

```math
c^{(2)}_0=0,\qquad c^{(2)}_{n+1}=(c^{(2)}_n-a_n)/2
```

により全段の解を作る。`V` 上では

```math
c^{(3)}_{2j}=-1/3,\qquad c^{(3)}_{2j+1}=-2/3
```

が全ての原始式を満たす。従ってB2の作用同型とこの被覆から `Y_a` は `G`-torsorとなる。

`G(R)=ker d` を計算する。2がunitなら初項 `c₀` により全列 `c_n=2^{-n}c₀` が決まる。`Z[1/3]` では初項が全 `2^n` で割り切れる必要があり、そのような元は零だけである。よって

```math
G(U)=\mathbb Z[1/2],\qquad G(V)=0,\qquad
G(U\cap V)=\mathbb Z[1/6].
```

Čech差を `c^(3)−c^(2)` とする。その初項は `−1/3`、第n項は `−1/(3·2^n)`。この被覆の1コホモロジーは

```math
\check H^1(\{U,V\},G)
=\mathbb Z[1/6]/\mathbb Z[1/2],
```

指定類は `[−1/3]` である。`−1/3` は分母が2の冪だけの整数分数ではないので非零、三倍は `−1` だから位数3。局所retractionの差が `z` を消して `Z[1/2]` 上のmapになることから、B5の拡大の局所splitとの差とも同じ類になる。

## 定理 C3 — `lim¹` と2進商への同じ写像

`C(Z)` に対し

```math
\Phi:\prod_{n\ge0}\mathbb Z\to\mathbb Z_2,\qquad
\Phi(a)=\sum_{n\ge0}2^na_n
```

を作る。この和は各項が `2^n` で割り切れるので収束する。`a=d(c)` なら有限和は `c₀−2^Nc_N` で、極限は `c₀∈Z`。逆に `Φ(a)=m∈Z` なら

```math
c_n=\frac{m-\sum_{i<n}2^ia_i}{2^n}
```

は整数で `d(c)=a`。全射性は任意2進整数の0/1展開から従う。したがってB3と合わせて

```math
H^1C(\mathbb Z)=\lim\nolimits^1(\mathbb Z,\times2)
\xrightarrow{\sim}\mathbb Z_2/\mathbb Z.
```

交互列では `Φ(a)=1+4+4²+⋯=−1/3`。よって実際の変更の不存在を表す `[a]` はこの同じ指定類へ写る。

### C3.1 — Čechからの接続写像と符号

各次数でlocalizationの短完全列を積に取り、

```math
0\to C(\mathbb Z)
\xrightarrow{\mathrm{diag}}
C(\mathbb Z[1/2])\oplus C(\mathbb Z[1/3])
\xrightarrow{(u,v)\mapsto v-u}
C(\mathbb Z[1/6])\to0
```

を得る。最後の全射性は各整数分数を二つのlocalizationの差で表すBézoutの式から従い、その表現を座標ごとに使う。局所解の対 `(c^(2),c^(3))` は差のliftであり、その微分は `(a,a)`。従って接続写像は指定Čech類を `+[a]` へ送る。

初項の表示との一致も明示できる。包含 `Z[1/3]→Z[1/6]` は

```math
\mathbb Z[1/3]/\mathbb Z
\xrightarrow{\sim}\mathbb Z[1/6]/\mathbb Z[1/2]
```

を誘導する。kernelは二つの部分環の交わり `Z`。全射性は `m/(2^a3^b)` の分子に対し `m−q2^a` を `3^b` で割り切れるように `q` を選べば分かる。`Z[1/3]` は `Z₂` に入り、これを通して両方の `[−1/3]` が一致する。

`Z[1/6]→Z₂` の単位的環射は存在しない。domainでは2がunit、codomainではmod 2で零となる非unitである。この比較は上記の**加法群の商**を介するものであり、そのような環射を使っていない。

## C4 — 有理数・2進整数上の全解

`Q` 上では任意 `t=c₀` に対して

```math
c_n=\frac{t-\sum_{i<n}2^ia_i}{2^n}
```

が唯一の全解である。従って `Y_a(Q)` は `Q` のtorsor。

`Z₂` 上では `c_n=Σ_(j≥0)2^ja_(n+j)` が解であり、交互列ではC2の周期解に一致する。斉次解の任意の `c_n` は全ての `2^m` 倍であるから零。従ってこの周期解が唯一である。

## 定理 C5 — 実在する基点での非零平方零障害

普遍mapを原始係数から

```math
d:\mathbb A^{\mathbb N}_c\to\mathbb A^{\mathbb N}_a,\qquad
a_n=c_n-2c_{n+1}
```

と作る。`R'=Z[ε]/(ε²)`、`R=Z`、kernel `M=εZ` とし、baseを `a'_n=εa_n`、還元上の点を `c=0` とする。liftの各座標は `c'_n=εx_n` と一意に書け、全式は `d(x)=a` となる。C1からliftは存在しない。

sourceとtargetは自由多項式環なので、零点でのrelative cotangentは、transitivityの実際の微分から

```math
\left[\bigoplus_n\mathbb Z\,da_n
\xrightarrow{\,da_n\mapsto dc_n-2dc_{n+1}\,}
\bigoplus_n\mathbb Z\,dc_n\right]
\simeq\mathbb Z[1/2][0]
```

となる。左の次数は−1、右は0。自由telescopeをHomに送るとB3の `C(Z)` である。ambient lift `tilde c=0` の不足量は `a'−d(tilde c)=εa` だから、指定障害は正確に `[a]=[−1/3]` となる。

有限stage `d_N:A^(N+1)→A^N` は `(a₀,…,a_(N−1),c_N)` への座標変換でprojectionに同型となりsmoothである。一方、全体のmapには上記の平方零lift反例があるのでformally smoothではない。存在しない `Z`-点を基点にした議論ではなく、普遍familyの実在する零点を用いている。

## C6 — Flat tensorと無限積の違い

`H⁰C(Z)=0` だが、`H⁰C(Q)=Q` である。`Q` はflatなので

```math
H^0(C(\mathbb Z)\otimes\mathbb Q)
=H^0C(\mathbb Z)\otimes\mathbb Q=0.
```

従って自然な複体map `C(Z)⊗Q→C(Q)` は擬同型でなく、指定された次数0の比較も同型でない。その項での原因は

```math
\left(\prod\mathbb Z\right)\otimes\mathbb Q
\longrightarrow\prod\mathbb Q
```

が全射でないことである。左辺の列は共通分母を持つが、`(2^{-n})_n` は持たない。flat tensorはkernelとの交換を失っておらず、比較している複体の無限積が変わる。schemeのbase change `Y_a×Spec Q` と、この複体のtensor比較は別の構成である。
