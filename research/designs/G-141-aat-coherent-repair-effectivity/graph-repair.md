# 有限graphの台帳から実操作・SAGA・全修復へ

## G1 — 原始操作とadapter

可換環 `R`、辺を一つ以上持つ有限連結単純graph `Γ=(V,E)`、各辺の向き、`μ∈R`、offset `b_e∈R` を固定する。各頂点の台帳は `R²` であり、

```math
p=(1,1),\quad v=\binom1{-1},\quad
i_\lambda=\binom{\lambda}{1-\lambda},\quad
j_\mu=\mu v,\quad g_b=I+bvp.
```

観測は `p`、外部入力 `u,t∈R` に対する操作はそれぞれ `x↦x+u i_λ`、`x↦x+t j_μ`。入力自体も比較の間で固定する。`pv=0`、`pi_λ=1`、`pj_μ=0` から、これらの任意の有限語のreadは初期readに全 `u` の和を加えた値である。これは空語から末尾操作を加える帰納法であり、語の長さを制限しない。

固定 `p=(1,1)` の全 `i,j` は `pi=1,pj=0` から一意にこの `λ,μ` を持つ。逆は `i,j` の第一成分を読むmapであり、[G-140 P1.2](../G-140-aat-semantic-change-category/ledger-specialization.md)の一型係数表示と、markされた三コピーによる台帳fiberとの全 `R` 上の同型そのものである。

`(vp)²=0` より `g_b g_c=g_(b+c)`、`g_b^(-1)=g_(-b)`。さらに `pg_b=p`、`g_bv=v`、`g_bi_λ=i_(λ+b)`、`g_bj_μ=j_μ`。辺 `e:i→j` のadapterには、公開readの一致に加えて、実操作の可換式 `g_(b_e) apply^i_u=apply^j_u g_(b_e)` とcompactの同様の式を全状態・全入力で要求する。前者に `u=1` を代入する必要性と加法の十分性により、この条件は

```math
\lambda_j-\lambda_i=b_e.
```

と同値である。原始操作の可換式を語の長さで帰納すれば、全語の実state mapも可換となる。公開readだけの一致はこの必要条件を課さない。零環でも実操作の可換式との同値は成立する。

## G2 — 実交差、局所定数層、操作の状態層

有限集合 `X_Γ=V⊔E` に、頂点がそのincident辺以下となる順序を入れ、上方閉集合をopenとする。頂点 `i` の最小openは

```math
U_i=\{i\}\cup\{e\mid i\text{ は }e\text{ の端点}\}.
```

これらは `X_Γ` を覆う。異なる `i,j` では、交差は両者を結ぶ辺の一点または空であり、異なる三頂点の交差は空。`U_i` には最小点 `i` があるため連結である。

各 `U_i` に局所定数層 `\underline R²` を置き、`e:i→j` の交差では `j` 側座標を `g_(b_e)` で与える。逆方向には `g_(-b_e)`、同じ添字には恒等を使う。異なる三頂点の交差は空で、重複添字のcocycleはこの逆・恒等の式から成立する。したがって実際のrank2局所定数層 `E_b` が貼り合わさる。

`p` と `v` はtransitionで不変なので、同じ層の完全列

```math
0\longrightarrow\underline Rv
\xrightarrow{\ \iota\ }E_b
\xrightarrow{\ p\ }\underline R
\longrightarrow0
```

を得る。各chartで `ker p={(a,−a)}`、かつ `i_0` が局所splittingであることが完全性を証明する。

`Ob=\underline Rv` とし、`State(W)={s∈Γ(W,E_b) | p(s)=1}` と定める。差分は一意な `Ob(W)` の元であり、加法が非空fiber上で自由かつ推移的に作用する。これは層のsectionのfiberであるため `State` も層である。大域section `s` は実際の `R` 線形操作 `i:\underline R→E_b`、`a↦as` を与え、`pi=id`。逆は `i↦i(1)`。固定された `j_μ` は常に貼り合わさるので、`State(X_Γ)` は台帳の全大域操作そのものを分類する。

## G3 — 全AAT contextへの実装上の比較

係数環 `R`、AtomCarrier、sectionの係数群は一つのuniverse `u` に揃える。必要な小さい型は `ULift` とその環・加法群構造で移し、元・演算・restrictionを上下写像で運ぶ。これにより `SitePresheafData.ofObstructionSheaf` が要求する `AtomCarrier.{u}` と `ObstructionSheaf` の係数universeが一致する。

既存 `AATSite.category` は全architecture contextである。[G-139 P1a.2](../G-139-aat-law-generated-relative-geometry/polynomial-realizations.md)と同じ構成をこの有限空間に使う。台帳の原始宣言Atomに `point(x)`、`x∈X_Γ` を加えたbase objectを取り、各context `W` の点supportの内部を `U_W` とする。実context射は `U_W⊆U_Z` を与えるので、全 `W` に

```math
Q(W)=\Gamma(U_W,\underline Rv),\quad
L(W)=\Gamma(U_W,E_b),\quad
B(W)=\Gamma(U_W,\underline R)
```

を定め、restrictionを実openの制限とする。`Q` は空openでは零、非空連結openでは `R` となる層であり、全openで一定値 `R` を取るpresheafではない。

open `U` をその点だけ読むcontext `W_U` へ送る。chartは `W_(U_i)`、baseは `W_(X_Γ)` とする。pair・triple contextは既存の標準product contextで作る。そのSupport型自体は点の積だが、同じ点Atomを両方が読む条件から

```math
U_{W\times Z}=U_W\cap U_Z.
```

射とpullback liftはproduct contextの射影・対形成で与えられる。従ってこれを単にopen交差と同じcontextだと仮定する必要はない。thinなcontext categoryなので、すべての射はmonomorphismである。

coverage readingには全 `point(x)` をrequired supportとし、visibilityを `x∈U_W` とする。他のcoverage要求集合は空、overlap visibilityは真と選ぶ。原始台帳Lawを持つequation system自体は保持する。このreadingで上のchart familyはadmissibleであり、全点を覆うことと実restrictionのnon-generationが必要fieldを満たす。`AATGrothendieckTopology.generate_mem` により、そのsieveは生成topologyに属す。

具体的にこのequation systemの係数は、原始台帳の普遍残差環 `B_raw` の局所定数層を用いた `Observable(W)=Γ(U_W,underline(B_raw))` とする。Law index・role・Law Atomは原始宣言から取り、symbolic coordinateとdecode後の残差を対応する定数sectionの制限で与える。制限との可換性は定数sectionの制限則であり、連結かつ非空の `X_Γ` 上では大域定数を読む逆mapが元のLawを回復する。これでcontext preorder、equation system、signature、coverage、overlapという `AATSite` の全fieldが定まる。

一般のadmissible generatorも全点を覆い、そのbaseのopen像は `X_Γ` である。pullbackでは上の交差式、合成ではopen被覆の合成により被覆性を保つ。従ってopen上の `Q,L,B,State` を全contextで読んだものは生成topologyの層となる。matching familyはopenのmatching familyであり、実open層の一意な貼合せがそのままcontext上の貼合せを与えるからである。

`MonomorphicOrderedCover` の省略指定は**全添字**で「open像の交差が空」とする。異なる三添字の交差は空だが、`(i,i,j)` や `(i,i,i)` を一律に省略しない。省略tripleの単調条件、ならびに後述の省略pair・triple上の零係数は、実交差と空openのsectionが零であることから従う。

## G4 — 同じ入力からLiftFiberDataと指定類を作る

[EquationLift](../../../Formal/AG/SemanticRepair/Saga/EquationLift.lean)の `LiftFiberData` に、G3の `Q,L,B`、`incl=ι`、`proj=p`、base section `1` を入れる。各mapの自然性は層射の自然性である。`incl` はsection上でも単射で、`p(s)=0` のとき各chartで `s=(a,−a)` の第一成分を読むと、transitionが `v` を固定するため一意の `q∈Q(W)` が貼り合わさり `ι(q)=s`。これが `exact_at_middle` を放電する。大域section上で `proj` が全射であるという仮定は使わない。

`liftSystem` はG2の `State` と加法作用を返す。任意に選んだ各 `λ_i` から局所lift `i_(λ_i)(1)` を作り、同じ入力の `AffineCoefficientLiftSystem`、`CoefficientLiftAtlas` を得る。辺 `i→j` の交差を `j` 側座標で読むと、SAGAの右−左の残差は

```math
i_{\lambda_j}(1)-g_{b_e}i_{\lambda_i}(1)
=(\lambda_j-\lambda_i-b_e)v,\qquad
r_e=\lambda_j-\lambda_i-b_e.
```

`C⁰=R^V`、`C¹=R^E`、`C²=0`、`(d⁰λ)_e=λ_j−λ_i` とする。増加pairと指定辺向きの比較 `T` は次数0で恒等、次数1で向きが逆なら符号を変える。各辺で直接 `Tδ⁰_SAGA=d⁰_Γ`。三角形 `0→1→2→0` では `T(c_01,c_02,c_12)=(c_01,c_12,−c_02)` となる。従って同じ残差の類は

```math
o_b=[r]=[-b]\in H^1(\Gamma;R).
```

G3の層を `ObstructionSheaf` として、[PartIVBridge](../../../Formal/AG/SemanticRepair/Saga/PartIVBridge.lean)の `SitePresheafData.ofObstructionSheaf` と `incToCoverRelativeH1` に渡す。前者のrestrictionは既に使った制限そのもの。後者の `hpair,htriple` は全添字で空交差の零sectionから成立する。したがって `IncH1` と `CoverRelativeHn 1` の相互逆mapはこの指定 `o_b` を運ぶ。

このopen被覆で `U_i` 上のsectionは最小点 `i` のstalk評価であるため完全関手であり、非空な二重交差も一点なのでacyclicである。Čechから層cohomologyへの比較は同型となる。完全列G2の `1` の局所liftを取った連結準同型は、まさに右−左の差なので

```math
o_b=\delta(1)\in H^1(X_\Gamma,\underline Rv).
```

K1の `TargetSupportedNerve` にはreading target `X_Γ` とchart support `U_i` を入れ、edgeを非空な増加pair、faceを非空な増加tripleとする。`edgeSupport` は実交差の一点、face集合は空である。supportからの係数だけで比較を済ませず、ここでは同じ局所定数係数と上記の実restrictionが `d⁰` を与えることまで同定した。既存K0の有理係数・Law値座標を一般の `R` 係数と自動同一視はしない。

## G5 — 零性から実sectionと全修復を回復する

`residualClass_isZero_iff_matching_correction` をG4のatlasに適用すると、零類は局所liftから係数 `c_i` を引いて増加・非省略pair上で一致させられることと同値である。空pairの値は一意、対角は恒等、逆順は同じ差の負であるため、これは全pairのmatchingと同値。G2–G3の層条件で一意な実sectionへ貼れる。逆に実sectionから元の局所liftとの差を取れば補正を得る。従って

```math
State(X_\Gamma)\ne\varnothing
\ \Longleftrightarrow\ o_b=0
\ \Longleftrightarrow\ b\in\operatorname{im}d^0.
```

二つの解の差は `ker d⁰`。連結性により各辺に沿って成分が等しく、全頂点で一定となるから `ker d⁰≅R=Ob(X_Γ)`。これで全大域操作のtorsorを得る。

頂点の許可変更集合 `A⊆V` から `H_V={a∈R^V | i∉A⇒a_i=0}` を生成する。基準 `λ` の修復は `λ+a` なので

```math
d^0a=b-d^0\lambda,\quad a\in H_V.
```

存在条件は右辺が `d⁰(H_V)` に属すこと、全解は非空なら `ker(d⁰|_(H_V))` のtorsor。SAGAの引く補正とは `a=−c_SAGA` で一致する。

辺の許可集合から同様に `H_E⊆R^E` を生成する。offsetを `b+Δb` にする修復は

```math
\Delta b\in H_E,\qquad [b]+[\Delta b]=0.
```

非空な全offset解は `ker(H_E→H¹(Γ;R))` のtorsorである。各offset解に対する全操作はさらに `H⁰(Γ;R)≅R` のtorsorを持つ。この二つのfiberを保持したまま、同じ `Ob,State,r,o_b` をG-142の診断・Atlas比較の入力にできる。
