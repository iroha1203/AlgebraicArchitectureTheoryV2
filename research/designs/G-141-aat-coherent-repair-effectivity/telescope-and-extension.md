# 整数adapterの全変更、telescope、拡大類

## B1 — 同じnative操作からの全射分類

各 `n∈N` に `S_n=Bool×Z` を置き、

```math
u_t(b,z)=(b,z+t),\quad v(b,z)=(\neg b,z),\quad
o(b,z)=b,\quad h_n^a(b,z)=(b,2z+a_n)
```

とする。adapterの向きは `h_n^a:S_(n+1)→S_n`。A4またはG-140 D4の直接計算により、全 `u_t,v,o` を保つ全mapは `(b,z)↦(b,z+c_n)`。`h^0` から `h^a` への自然性は

```math
c_n-2c_{n+1}=a_n.
```

係数familyは `Bool_R×A¹_R` と全 `G_a` 作用を使う。等変性の普遍式 `F(x+t)=F(x)+t` に `x=0` を代入すれば全regular mapは `F(t)=t+c`。flipが二成分の `c` を一致させる。従って全環上で同じ分類が成立し、native `Z` でも全Homを回復する。`u₁` だけへの等変性で代用しない。

## 定理 B2 — 全変更schemeと有限段

原始係数とadapter保存式から

```math
B_a=\mathbb Z[c_0,c_1,\ldots]/(c_n-2c_{n+1}-a_n),\qquad
Y_a=\operatorname{Spec}B_a
```

を生成する。任意環への環射は全係数列と全式の成立を与えるので、`Y_a(R)` と独立な全変更は互いに逆に回復される。

最初の `N` 本の式を課す `Y_(a,N)` では、`c_N` から `c_(N−1),…,c₀` を後ろ向きに一意に決められる。よって全 `R` に自然に `Y_(a,N)≅A¹_Z`。制限の最後の座標は

```math
c_N=2c_{N+1}+a_N.
```

全式の環は有限式の環のfiltered colimitだから、affine schemeの反変性により `Y_a=lim_NY_(a,N)`。これは各段の `R`-点の逆極限とも可換である。

斉次群は

```math
G=\operatorname{Spec}\operatorname{Sym}_{\mathbb Z}(\mathbb Z[1/2]),\qquad
G(R)=\operatorname{Hom}_{\mathbb Z}(\mathbb Z[1/2],R)
=\{c_n=2c_{n+1}\}.
```

Hopf構造は生成元の加法から作る。解同士の差は斉次解、解に斉次解を加えると再び解となる。従って解がある各fiberで作用は自由かつ推移的であり、さらに自然なmap `G×Y_a→Y_a×Y_a`、`(g,y)↦(y,y+g)` は逆 `(y,y')↦(y'−y,y)` を持つ。torsorとしての局所非空性は指定例で次稿により証明する。

## 定理 B3 — Telescopeと実Law複体

任意環 `R` で、直和の基底に

```math
q:\bigoplus_{n\ge0}Re_n\longrightarrow\bigoplus_{n\ge0}Re_n,\qquad
q(e_n)=e_n-2e_{n+1}
```

を定める。`q` のkernelは零である。有限support元について最初の座標から順に係数を比べると全て零になる。cokernelは `e_n↦2^{-n}` により `R[1/2]` と同型であり、これは `colim(R→²R→²⋯)` の表示そのものである。従って全環で自由分解

```math
0\to\bigoplus R\xrightarrow q\bigoplus R\to R[1/2]\to0
```

を得る。`Hom_R(-,M)` を取れば、任意の `R`-加群 `M` に対して

```math
C(M)=\left[\prod M\xrightarrow d\prod M\right],\qquad
d(c)_n=c_n-2c_{n+1},\qquad
C(M)\simeq R\operatorname{Hom}_R(R[1/2],M).
```

次数は0、1。`M=R` が原始adapterの実補正複体であり、全変更の存在条件は `[a]=0∈H¹C(R)`、全解は `H⁰C(R)` のtorsorとなる。

有限段の複体を `C_N(M)=[M^(N+1)→M^N]` とする。微分は同じ式で、制限は座標を落とすmap。項ごとにsurjectiveで、通常の逆極限は `C(M)` なので

```math
C(M)\simeq R\!\lim_N C_N(M).
```

有限微分は末尾を0にして後ろ向きに解けるため全射。`H⁰C_N(M)≅M` は末尾座標で同定でき、その制限は `×2`。A3により

```math
H^0C(M)=\lim(M,\times2),\qquad
H^1C(M)=\lim\nolimits^1(M,\times2).
```

## 定理 B4 — Cotangentと平方零補正

有限環 `B_(a,N)≅Z[c_N]` のcotangentは `B_(a,N)dc_N` を次数0に置いたもの。遷移の微分は `dc_N↦2dc_(N+1)`。cotangentのfiltered colimitとの交換（[Stacks 08PL, Lemma 92.3.4](https://stacks.math.columbia.edu/tag/08PL)）から

```math
L_{B_a/\mathbb Z}
\simeq\operatorname{colim}(B_a\xrightarrow2B_a\xrightarrow2\cdots)[0]
=B_a[1/2][0].
```

点 `x:B_a→R` への導来pullbackは `R[1/2][0]`。localizationはflatなのでこの計算に余分なTorはない。したがってその `M` 係数の `RHom` がB3の `C(M)` となる。

平方零拡大 `R'↠R` のkernelを `M`、基準解を `c∈Y_a(R)` とする。各係数のambient lift `tilde c_n` を取り、

```math
\mathrm{defect}=a-d(\widetilde c)\in\prod M
```

と置く。補正 `δ∈∏M` によりdefectは `defect−dδ` となる。従ってlift障害は `[defect]∈H¹C(M)`、全liftは非空なら `H⁰C(M)` のtorsorである。

cotangentとの符号は、右辺を左辺から引いた残差ではなく、ここでは方程式 `d(c)=a` の不足量を採用する規約で合わせる。自由分解の関係generatorと補正式をこの向きで対応させれば、同じ指定類となる。大きな変更のfiber `d^{-1}(a)` と指定した点の平方零lift fiberは別の入力を持つが、どちらもこの同じ線形式で計算される。

## 定理 B5 — Adapterから生成する拡大とその類

原始定数 `a_n` から

```math
E_a=(\mathbb Zz\oplus\bigoplus_n\mathbb Ze_n)/
(e_n-2e_{n+1}-a_nz)
```

を作る。有限段は `Zz⊕Ze_N`、遷移は `z↦z,e_N↦2e_(N+1)+a_Nz`。整数上では単射である。`Zz` で商にした遷移は `×2` なので、filtered colimitの完全性から

```math
0\longrightarrow\mathbb Zz\longrightarrow E_a
\longrightarrow\mathbb Z[1/2]\longrightarrow0.
```

`Z[1/2]` がflatであるため、任意環 `R` でtensorした列も左端を含め完全である。遷移行列が任意の `R` 上でも単射だという推論は使わない。

`R`-線形map `E_a⊗R→R` で `z↦1` とするものは、`c_n` を `e_n` の像として `d(c)=a` を満たすものに等しい。これは `Rz↪E_a⊗R` のretractionである。Symの普遍性から

```math
B_a\cong\operatorname{Sym}_{\mathbb Z}(E_a)/(z-1).
```

telescope分解の自由生成元 `e_n` を `E_a` の同名の元へliftすると、その関係の像は `a_nz` となる。従って上の拡大のYoneda類は、B3の `Ext¹_Z(Z[1/2],Z)` の表示で `[a]` に一致する。拡大類の零性、retractionの存在、実際の全adapter変更の存在は、この同じmapを通して同値となる。
