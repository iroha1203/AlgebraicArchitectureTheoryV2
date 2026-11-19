# 固定labelの整数診断と係数変更

## A1 — 原始labelと整数微分

有限集合 `Source`、既存の `FiniteLawFamily`、全射reading `q:Source→T`、adequacy、`TargetSupportedNerve` を取る。各Law `ℓ` の値域 `V_ℓ` は任意である。adequacyは `q(x)=q(y)⇒eval_ℓ(x)=eval_ℓ(y)` であり、全射性から一意の `f_ℓ:T→V_ℓ` を生成する。

chart支持 `S_i⊆T` は入力、edge支持は両端支持の交差、face支持は三辺支持の交差とする。各cell `σ` のlabelは

```math
I_\sigma=\{(\ell,a)\mid\exists t\in S_\sigma,\ f_\ell(t)=a\}.
```

全 `Source`、Law、cellが有限なので、値域が無限でも各 `I_σ` とその次数別直和 `I^d` は有限である。出現witnessはlabelの等号の一部にしない。これが既存 `CellCoordinate` の `cell,law,value,generated` と同じ集合である。

`C^d_Z=Z^(I^d)` と置く。支持包含から同じ `(ℓ,a)` の端点・辺へのmapがあり、

```math
(d^0c)_{e,\ell,a}
=c_{r(e),\ell,a}-c_{l(e),\ell,a},\qquad
(d^1b)_{F,\ell,a}
=b_{e_0(F),\ell,a}-b_{e_1(F),\ell,a}+b_{e_2(F),\ell,a}.
```

faceの端点等式は `l(e_0)=l(e_1)`、`r(e_0)=l(e_2)`、`r(e_1)=r(e_2)`。代入すると六つの頂点値が対で消えるので `d¹d⁰=0`。整数の加法だけを用いるため、任意可換環 `Λ` 上でも同じ式で複体 `C_Λ` を作れる。

## A2 — 同じlabelを保つ係数変更

有限labelのdelta basis `e_ξ` により

```math
\Lambda\otimes_{\mathbb Z}\mathbb Z^{I^d}
\xrightarrow{\sim}\Lambda^{I^d},\qquad
a\otimes e_\xi\longmapsto a e_\xi
```

を得る。逆は `c↦Σ_ξ c_ξ⊗e_ξ`。微分matrixの係数は `0,1,−1` なので両微分と可換となる。恒等環射・環射の合成ともbasis上で可換である。有限性はここでtensorと有限積を交換するために用いた。

`Λ=Q` での同定は、[LawGeneratedComplex](../../lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean)の `lawGeneratedD0,lawGeneratedD1,lawGeneratedComplex` へ同じcoordinate関数を送る恒等mapである。別の同次元複体を選んだ比較ではない。

既存 `TargetSupportedNerveMorphism` は、chart map、edge・faceの部分map、支持の包含、合流した頂点、退化faceの三辺の退化を持つ。adequateな粗細readingの一意なfactorを用いると、同じLaw値のcoordinateを粗側へ送れる。粗cochainの引戻しを、chartではこのcoordinateでの評価、edge・faceでは部分mapが定義されるときその評価、退化時には零とする。

非退化cellでは端点・辺の整合式から微分と可換。退化edgeでは両端が同じ粗chartとなって差が零、退化faceでは三辺全てが退化して三項とも零となる。このmapは整数で定義され、tensor後も同じ式である。従って `Q` では [GeneratedComparisonMap](../../lean/ResearchLean/AG/ResolutionInvariance/GeneratedComparisonMap.lean) の `generatedPullback0/1/2`、`generatedComparisonHom`、`generatedComparisonH1Map` と一致する。部分mapの恒等・合成でも、定義されたcellの評価と零の規約を追えば比較が可換になる。

## A3 — コホモロジーと類の零性

`Λ→Λ'` をflatとする。cycle `Z^i` とcoboundary `B^i` の二つの完全列

```math
0\to Z^i\to C^i\to B^{i+1}\to0,\qquad
0\to B^i\to Z^i\to H^i(C)\to0
```

にtensorを適用すると完全性が保たれる。A2の次数別同定で両端のkernelとimageも同定されるので、`i=0,1,2` について

```math
\Lambda'\otimes_\Lambda H^i(C_\Lambda)
\xrightarrow{\sim}H^i(C_{\Lambda'})
```

を得る。指定類 `[z]` は `1⊗[z]`、すなわち同じcycleの係数変更へ写る。

faithfully flatなら `m↦1⊗m` は任意加群で単射である。実際、cyclic部分加群 `Λm↪M` のtensorも単射であり、`1⊗m=0` ならそのtensor全体が零、faithfulnessから `Λm=0`。従って指定類の零性を反映する。flatだけでこの反映は得られないことをW1で計算する。

ここではLaw値の値域とlabelを固定した。例えば値 `0,2∈Z` を `F₂` へ写して一つにする操作は、A2のtensorに加えて新しい `I_σ` を作る別の操作である。
