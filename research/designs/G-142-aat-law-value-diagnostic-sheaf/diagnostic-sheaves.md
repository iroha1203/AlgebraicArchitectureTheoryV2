# 原始scalar式から生成するétale診断層

## B1 — 独立な実現とregular readout

任意scheme `B`、有限集合 `S,L`、有限supported nerveを取り、各 `ℓ,s` に `f_(ℓ,s)∈Γ(B,O_B)` を与える。chart支持は `S` の部分集合、edge・face支持はK1の交差で生成する。有限 `Source` の全射reading `q:Source→S` を使う場合は、原始評価が `f_(ℓ,q(x))` となることを検査する。この等式と全射性からadequacyと一意なLaw descentを得る。

既存 `TargetSupportedNerve` への直接の入力では、各chart支持は `chartSupport_nonempty` を満たす。本節のroot schemeと層の構成自体は空chart支持にも拡張でき、そのchartの次数0成分は零となる。この拡張と、既存の非空chart支持を持つAPIとの同定を区別する。edge・face支持は既存APIでも空でよい。

G-139の実現scheme `M_P` では、`f` を原始scalar構文から作る。係数、有限和・積は構造層の同じ演算で評価し、有限tensor式から得た有限局所自由moduleの自己準同型にはtraceを取る。局所matrixでのtraceは対角和でregularであり、可換環上の `tr(AB)=tr(BA)` から `tr(gAg^(-1))=tr(A)`。よってchart間で貼れる。

名前付き生成元が基底の場合は演算matrixの成分も大域regularである。一般のframe変更では、多重線形演算のmatrixは `g_out μ(g_1^(-1)⊗⋯⊗g_r^(-1))` へ移る。従って成分を読む場合はそのframe chartを `B` として扱う。構文帰納法で、これらのregular functionの `R` 点での評価が独立な実現の同じ原始演算に一致する。

required Lawの残差はlawful実現上で零である。ここでの `L` は、操作係数やtrace等を指定したreadoutであり、required Lawと同じものとする必要はない。生成元を忘れる商stackへ降ろす場合は、作用groupoidの二射に沿うreadoutの一致を検査する。上のtrace・係数・有限和積はこの不変性を保つ。一般のmatrix成分は変換式を持つため、GL不変性が証明された式について降下する。

## B2 — 有限root schemeと支持制限

各cell `σ`、readout `ℓ` に対し

```math
F_{\sigma,\ell}(z)=\prod_{s\in S_\sigma}(z-f_{\ell,s}),\qquad
Z_{\sigma,\ell}=\operatorname{Spec}_B
\bigl(\mathcal O_B[z]/(F_{\sigma,\ell})\bigr)
```

を定める。monic多項式によるdivisionから、`1,z,…,z^(m−1)` が商の基底で、`m=|S_σ|`。従って `p_(σ,ℓ):Z_(σ,ℓ)→B` は有限局所自由である。空支持では積は1、商は零、schemeは空でrank0となる。

`S_τ⊆S_σ` なら `F_τ` は `F_σ` を割るため、商環の全射から閉埋込み `i_(τ,σ):Z_τ→Z_σ` を得る。このmapは `z` と基底係数を保ち、恒等・合成に整合する。

小étale siteで定数 `Λ` 加群層を取り、restriction
`underline Λ_(Z_σ)→i_* underline Λ_(Z_τ)` を作る。これは層のsectionを閉部分へ制限するmapである。`p_*` を適用し、各次数の有限直和

```math
\mathscr C^d_{B,\Lambda}
=\bigoplus_{\dim\sigma=d,\ \ell\in L}
(p_{\sigma,\ell})_*\underline\Lambda_{Z_{\sigma,\ell}}
```

に、A1と同じ右−左・三辺交代和を入れる。二通りのfaceから同じ頂点への閉埋込みが一致し、六項が消えるので `d¹d⁰=0`。非reducedなroot schemeもこの構成に残す。

## B3 — 幾何stalkと全値別複体

幾何点 `bar b:Spec Ω→B` を取る。`Ω` 上で `F_(σ,ℓ)` は線形因子の積であり、幾何fiberの点は相異なる値 `a∈{f_(ℓ,s)(bar b):s∈S_σ}` と一対一である。各点の重複度はその値を持つsource数だが、étale層のstalkの添字はこの点集合である。

有限射のstalk定理により

```math
\bigl((p_{\sigma,\ell})_*\underline\Lambda\bigr)_{\bar b}
\cong
\prod_{a\in f_\ell(S_\sigma)(\bar b)}\Lambda.
```

閉埋込みによるrestrictionは、残る同じrootの成分を読む射影になる。したがって両微分を含めて
`(mathscr C_(B,Λ))_(bar b)≅C_(bar b,Λ)`。各chart支持が非空なら、右辺は同じ値域 `Ω` でAのlabelを再生成したK0/K1そのものである。空chart支持を許す拡張では、その空の値集合に対応する零直和成分を加えた同じ式になる。さらに `(ℓ,a)` ごとの成分への分解も同じcoordinateで一致する。このstalk式と任意base changeは[有限順像の定理](https://stacks.math.columbia.edu/tag/03QN)を使っている。

## B4 — 幾何のbase changeと診断係数のtensor

任意のscheme射 `g:B'→B` を取る。式を引き戻して作るmonic多項式は `g^*F` なので、商の右完全性から

```math
Z'_{\sigma,\ell}\cong Z_{\sigma,\ell}\times_B B'.
```

この比較にflatnessは要らない。有限順像のbase changeで

```math
g^{-1}(p_{\sigma,\ell})_*\underline\Lambda
\cong(p'_{\sigma,\ell})_*\underline\Lambda
```

を得る。幾何stalkでは同じ根の同じ成分を読むmapであり、支持制限・微分とも可換。従って `g^(-1)mathscr C_(B,Λ)≅mathscr C_(B',Λ)` となる。恒等・合成、固定した `S,L` と支持を保つ原始表示の代入との整合は、商環の `z` と係数への作用から従う。Sourceを合併するreading比較はB6で別に構成する。層のinverse imageは完全なので、幾何のbase changeはコホモロジー層とも可換する。

別に、診断係数の任意の環射 `Λ→Λ'` に対する自然なmap

```math
\underline{\Lambda'}\otimes_{\underline\Lambda}
\mathscr C^d_{B,\Lambda}
\longrightarrow\mathscr C^d_{B,\Lambda'}
```

を作る。各stalkではA2の有限basisによる同型だから、層として同型である。各項のstalkは有限free `Λ` 加群なので、各項は `underline Λ` 上flatである。次数0–2のbounded flat複体なので、全複体でも導来tensorを通常tensorで計算できる。

通常のコホモロジーとのtensor交換には、A3のflat条件を各stalkで用いる。faithfully flatな場合は全stalkの指定類の零性も反映する。幾何の基底変更と診断係数の変更は、この二つの異なる演算として保持する。

## B5 — Partitionによる有限分割と普遍族

各 `ℓ` について `S` のpartition `π_ℓ` を取り、全体を `π` とする。各blockの代表を選び、同block内の全 `f_(ℓ,s)−f_(ℓ,t)` を零、異なるblock代表間の全差をunitとするlocally closed subscheme `B_π` を作る。差の有限積のprincipal openと、有限生成idealの閉部分の交差である。

各scheme点では残留体での値の等号が一意のpartitionを与える。従って `|B_π|` は互いに素で全 `|B|` を覆う有限分割となる。これは点集合の分割であり、冪零方向を異なる層別schemeへ自動的に分けるものではない。

`B_π` 上で、各cellに現れるblockの共通値を `a_B`、その重複度を `m_B` とすれば

```math
\mathcal O_{B_\pi}[z]/(F_{\sigma,\ell})
\cong
\prod_{B\cap S_\sigma\ne\varnothing}
\mathcal O_{B_\pi}[w_B]/(w_B^{m_B}).
```

異なる `a_B` の差がunitなので中国剰余定理が使える。各因子は `B_π` のnilpotent thickeningで、有限射の単一幾何点fiberにより、定数層の順像は `underline Λ_(B_π)` と同型である。支持制限はblockが残れば恒等、なければその成分を落とす。従って各 `B_π` 上で診断は有限free `Λ` 加群の**定数複体**となる。重複数はbasis数には入らない。

最後に `A^(L×S)_Z` の普遍座標 `x_(ℓ,s)` で同じ構成を行う。任意の `f` は、それらを `f_(ℓ,s)` へ送る一意のscheme射 `B→A^(L×S)_Z` を与える。B4によりroot scheme・層・微分・全stalk同定はそのpullbackで回復される。

## B6 — Source比較を係数の制限として生成する

各cellで、根のsectionの和 `a:∐_(s∈S_σ)B→Z_(σ,ℓ)` を取る。これは有限全射である。実際、各sectionは `z−f_(ℓ,s)` で定まる閉埋込みであり、任意の素idealが積 `F` を含めばその因子の一つを含む。二つのsectionのfiber積は `D_(s,t)=V(f_(ℓ,s)−f_(ℓ,t))` である。

有限全射の層に対するdescent（[03QN, Lemma 59.55.5・Remark 59.55.6](https://stacks.math.columbia.edu/tag/03QN)）から、次の自然な表示を得る。`i_(s,t):D_(s,t)→B` とする。

```math
(p_{\sigma,\ell})_*\underline\Lambda
\cong
\ker\!\left(
\underline\Lambda^{S_\sigma}
\xrightarrow{\ (c_s-c_t)|_{D_{s,t}}\ }
\bigoplus_{s,t}(i_{s,t})_*\underline\Lambda
\right).
```

この表示は幾何stalkでも確認できる。同じ値を持つsource間の係数が等しいという条件だけが残り、B3の値別basisを得る。

同じ基底上で `φ:S_f→S_c` が `f^f_(ℓ,s)=f^c_(ℓ,φ(s))` と支持の包含を満たすとする。粗側のfamilyを `(c_t)↦(c_(φ(s)))` で細側へ制限する。同じ細側値の等値部分は対応する粗側の等値部分なので、このmapは上のkernelを保つ。support mapを持つcellではこの制限、退化edge・faceでは零を用いる。A2の端点と三辺の恒等式からcochain mapとなる。幾何stalkでは既存のgenerated comparisonと同じ座標mapである。

恒等・合成はfamilyの代入則であり、B4の基底変更・係数変更とも可換する。支持を全射で写し同じ値集合を持つ一つのcellでは、このmapはstalk上の同型となる。Sourceの重複数が変わる場合もこの構成を使える。例えば `(z−a)²` と `z−a` のroot schemeを同型とする必要はない。
