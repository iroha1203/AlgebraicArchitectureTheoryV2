# 実操作から生成する指定診断類

## E1 — 同じadapterとreadout

[G-141 G1–G5](../G-141-aat-coherent-repair-effectivity/graph-repair.md)の有限連結単純graph `Γ=(V,E)`、`E≠∅`、向き、可換環 `R`、`μ,b_e∈R` を取る。原始操作を再掲すると

```math
p=(1,1),\quad v=(1,-1)^{\mathsf T},\quad
i_\lambda=(\lambda,1-\lambda)^{\mathsf T},\quad
j_\mu=\mu v,\quad g_b=I+bvp.
```

辺 `e:i→j` の実操作の可換式は `g_(b_e)i_(λ_i)=i_(λ_j)`、すなわち `λ_j−λ_i=b_e` である。全入力・全状態での可換式から入力1による必要性を得て、逆は線形性、全操作語へは長さの帰納法で拡張する。同じ有限空間 `X_Γ=V⊔E` と実open `U_i={i}∪{incident edges}` により、G-141の層の完全列と状態層を得る。

```math
0\longrightarrow Ob=\underline Rv\longrightarrow E_b
\xrightarrow p\underline R\longrightarrow0,\qquad
State(W)=\{s\in\Gamma(W,E_b):p(s)=1\}.
```

診断のSourceはinterface `E`、Lawは一つ、原始補正 `v` のreadoutは `p(v)=1−1=0` とする。chart支持はincident edge集合 `S_i`、edge支持は `S_i∩S_j={e}`、異なる三頂点の支持交差は空である。readingは恒等でadequacyを満たす。連結性と `E≠∅` から全chart支持は非空。診断nerveは非空pairだけを辺とし、faceは空とする。

この値0は補正の公開readであり、操作の残差 `r_e=λ_j−λ_i−b_e` とは異なる入力である。前者から診断複体を、後者からその中の指定類を生成する。

## E2 — 原始relationの完全性

各interfaceに補正生成元 `[e]` を置く。一つの頂点の操作補正 `av` は、その全incident interfaceへ同じ `av` を制限する。この制限則から、同じ頂点に接続する `e,e'` に対しrelation `[e]−[e']=0` を生成する。

各非空cell支持 `S_σ` の係数表示は

```math
\epsilon_\sigma:\mathbb Z^{S_\sigma}\longrightarrow\mathbb Zv,
\qquad (a_e)\longmapsto\Bigl(\sum_e a_e\Bigr)v.
```

これは補正をinterfaceごとの生成元で表したもの。`e₀∈S_σ` を選ぶと、核の任意の元は
`∑_(e≠e₀)a_e([e]−[e₀])` と書ける。従ってchartでの上のrelationが核を生成する。edgeでは支持が一点で核は零、空支持では両辺とも零である。係数 `R` でも同じ計算が成り立つ。

全Sourceのrelationも連結である。任意の二辺の端点を結ぶgraphの道を選び、その辺列を両端の辺とつなげれば、連続する辺は頂点を共有する。この列が `[e]` と `[e']` のrelationによる同一視を与える。従って

```math
M=\mathbb Z^{E}/\langle[e]-[e']:e,e'\text{ は頂点を共有}\rangle
\xrightarrow[\ \sum\ ]{\ \cong\ }\mathbb Z .
```

逆は任意の `[e]` のclassを1の像とするmapで、連結性により選択によらない。

これを既存の `GeneratorPresentation` に入れる。原始生成元 `(Law,e)`、relationは上の共有頂点、labelはすべて `(Law,0)` なので `relation_preserves_label` が成立する。等しいlabelの生成元がrelationで結ばれることは上の道の証明であり、`ReflectionCondition` を仮定として追加しない。`PresentationGroup` は自由可換群にこの加法relationを入れた商だから、まさに `M` である。

## E3 — 実層と整数Čech比較

`M≅Z` を `a↦av` で読む局所定数層は `underline Z v` に同型であり、`R` へtensorすると `Ob` となる。この同型はすべてのopenの局所定数関数を点ごとに写し、restrictionと可換である。

全AAT context上の比較はG-141 G3の同じsiteと `W↦U_W` を使う。これは `ContextOpenSupport` の連続なsupport functorを与える。点Atomから作るchart context、標準product context、射影を用いると `U_(W×Z)=U_W∩U_Z`。従ってpair contextのopen像は実際のedge一点となる。各chartは最小点を持ち非空かつ連結、edgeも一点で同じ性質を持つので、`FaceEmptyAATCechCover` の全fieldを満たす。

ここで診断のSource `E` と、実空間の点 `V⊔E` は別である。両者は同じchart添字・非空pair・空faceと、上で証明した係数制限によって比較する。空であるのは**異なる三添字**の交差であり、SAGAの全tupleには重複添字の交差も残す。

整数の各cellで、次のmapは加法同型である。

```math
\Gamma(U_\sigma,\underline{\mathbb Z}v)
\longrightarrow C^d_{\mathbb Z,\sigma},\qquad
av\longmapsto a\,e_{(\mathrm{Law},0)}.
```

非空支持にはlabelが一つ、face項は両方零である。restrictionは `av↦av` だから `d⁰` の右−左と可換、`d¹` は両側零で可換する。これで実際の正規化Čech複体、整数診断複体、graph cochain複体の同型を得る。全 `R` へ同じ式でtensorできる。

既存 `coefficientComparison_generatorClass_apply` は生成元をそのlabelの有理delta関数へ送る。E2の `[e]↦1` の下では `a↦a e_(Law,0)` に一致する。従ってこの整数比較に `Z→Q` を合成したものが `CochainComparison` の各次数のmapであり、商に誘導されるH¹のmapは `actualCechDiagnosticH1Map` そのものである。これは係数群の抽象同型だけでなく、各生成元の像と両微分による同定である。

## E4 — SAGA、実residual、指定類

G-141 G4の増加pairからgraphの指定向きへの符号map `T` を使う。次数0は恒等、逆向きの辺では次数1に−1を掛けるので、辺ごとに `Tδ⁰_SAGA=d⁰_Γ`。全tupleの空交差のsectionは零、逆pairは負、対角は零であり、SAGAの正規化比較とも可換する。

`R=Z` では、E2の整数係数群の同定により、既存 `ActualCechAffineLocalData` をこの増加pair座標で `transition=T^(-1)(−b)`、`localState=λ` として同じ実操作から作る。一般の可換環 `R` では、同じ式を `underline Rv` の実Čech複体に適用して係数 `Λ=R` のdataを作る。後者は本稿で構成する係数版である。どちらもgraph座標に移れば

```math
T(\mathrm{actualMismatch})
=-b+d^0\lambda=r,\qquad
o_b=[r]=[-b]=\delta(1).
```

最後の等式は `E_b→underline R` の局所lift `i_(λ_i)` の差で連結準同型を計算したG-141 G4の式である。係数比較は上の各cellのmapなので、一般の `R` では同じ `[-b]` を係数 `Λ=R` の指定診断類 `κ_b` へ送る。`R=Z` から `Z→Q` を合成したとき、この生成元上の比較が既存 `h1_map_actual_class_eq_diagnostic_class` の両辺に一致する。同宣言の比較先は有理係数に固定されている。SAGAの類、実層の類、指定診断類の比較図式は、各係数で同じ残差の成分を送ることにより可換となる。

## E5 — Spanning treeによる零性反映と全操作

spanning tree `T_Γ` と根を選ぶ。任意の `a∈R^E` について、根の値を0とし、treeの一意な道に沿う符号付き和で `u(a)∈R^V` を定める。すると `(d⁰u(a))_e=a_e` がすべてのtree辺で成立する。残るchord上のmap

```math
\Phi_R(a)=\bigl(a_e-(d^0u(a))_e\bigr)_{e\notin T_\Gamma}
\in R^{E\setminus T_\Gamma}
```

は全射である。実際、tree辺を零、chord辺を任意にしたcochainを取ればよい。`Φ_R(a)=0` なら全辺で `a=d⁰u(a)`。逆に `a=d⁰w` ならtree上の一意性から `u(a)=w−w_(root)` となり `Φ_R(a)=0`。よって全 `R` に自然な同型

```math
H^1(\Gamma;R)\cong R^{|E|-|V|+1}
```

を得る。構成は整数の加減算だけなので `Z→Q` に沿う比較は自由加群の通常の包含であり、零性を反映する。従って `R=Z` では

```math
State(X_\Gamma)\ne\varnothing
\ \Longleftrightarrow\ o_b=0
\ \Longleftrightarrow\ \kappa_b=0\quad\text{in }H^1(C_{\mathbb Q}).
```

最初の同値は実操作の式 `d⁰λ=b` とG-141の貼合せによる。`R=Q` でも同じ式となる。一般 `R` では `Λ=R` の診断で三者が同値であり、全解は `ker d⁰≅R` のtorsorである。他の `R→Λ` で零性を反映するにはA3のfaithfully flat条件、またはこの自由加群上の係数mapが単射である等の個別証明を使う。

三辺cycleでは各chartに値0は現れるが、三つのincident edge支持の共通部分は空である。既存 `CommonLabelChartSupport` は各labelを表す**同じtarget**が全chart支持に属することを要求するため、この例では偽。従って既存のその仮定付き反映定理をcycleへ適用せず、上のspanning treeで零性反映を得た。

## E6 — 定数の診断族と変動する指定類

原始parameter `μ,b,λ` の実現・局所操作族上で、同じreadout `p(v)=0` は恒等的に零である。Bのroot schemeは各支持で `z^|S_σ|=0`、B5の一つのpartition上の定数複体となる。従って体係数でのH¹次元は常に `|E|−|V|+1` であり、offsetに依存しない。

一方、各 `R` 点で実操作から得る指定類は `[-b]`、tree座標では `−Φ_R(b)` であり、offsetの原始式で変化する。これは点ごとの `R` 係数の類の構成である。Bの固定 `Λ` の定数étale層の大域sectionとして、任意のregularなoffsetを同一視する主張ではない。さらに許容頂点・辺が指定される場合は、G-141 G5の `H_V,H_E` と全解を保持する。無制約の `κ_b=0` から制約付き修復の存在を推論することはできない。W3で同じ零類と固定頂点の制約を比較する。
