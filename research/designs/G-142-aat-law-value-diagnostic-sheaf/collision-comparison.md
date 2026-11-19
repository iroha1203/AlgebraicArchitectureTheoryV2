# 値の合流、特殊化、Mayer–Vietoris

## C1 — Law値別の閉じた部分複体

一つのLaw `ℓ` と、そのsourceの等値partition `π_ℓ` を固定する。block `a` に対し、`S_σ` とそのblockが交わるcellの集合を `K_a` とする。faceが `K_a` に属せば同じsourceが三辺と全頂点の支持に入り、edgeが属せば両端が属す。従って `K_a` はcellの面を取る操作で閉じている。ここでの部分複体は、固定された次数0–2のincidenceに相対的なものである。

A1のcoordinateを `(ℓ,a)` ごとに並べると

```math
C^\bullet(\pi;\Lambda)
\cong\bigoplus_{\ell,a} C^\bullet(K_a;\Lambda).
```

各mapは同じcellの係数を読むmap、逆はその有限tupleを元のcoordinateへ入れるmapである。微分はLawと値を変えないので両方向がcochain mapとなる。これが既存 `lawValueBlockComplex` と `lawGeneratedH1BlockEquiv` の値別分解と同じ構成である。

## C2 — 全粗化と幾何的特殊化

`π'` が `π` の粗化なら、そのblock `A` に対して `K_A=⋃_(a⊂A)K_a`。同じcellの係数を各 `K_a` へ制限することにより

```math
r_{\pi',\pi}:C^\bullet(\pi';\Lambda)\longrightarrow
C^\bullet(\pi;\Lambda)
```

を作る。粗blockに属すcellには少なくとも一つの細blockが現れるため、全制限が零なら元の係数も零。従って各次数で単射である。微分との可換性は同じincidence式から従う。

恒等粗化は恒等map。三段の粗化では、最後の細blockの各係数に中間blockの名前を介して同じ値を写すだけなので `r_(π'',π)=r_(π',π)r_(π'',π')`。二値合流をどの順番で分解しても、全体のmapはこの同じ `r` であり、そのkernel・cokernelも同じquotient mapを通して一致する。中間段の個々のkernelやfiltrationまで同じだという主張ではない。

Bの幾何点の特殊化 `bar η→bar s` を取る。regularな差が `η` で零なら `s` でも零なので、`π_s` は `π_η` の粗化である。étale stalkのgeneralization mapは

```math
\mathscr C_{\bar s}\longrightarrow\mathscr C_{\bar\eta}.
```

これを具体的に計算するため `s` のstrict henselization上へ引き戻す。各有限root schemeは特殊fiberの相異なるrootごとの局所成分へ分かれる。各成分の定数sectionは一つの `Λ` 値を持ち、そのgeneric fiberで分かれる全rootへ同じ値を制限する。rootは元のglobal section `f_(ℓ,s)` から生成されているため、どの成分へ属すかは特殊点での値の一致で定まる。

従ってstalk射は、特殊点のblock係数をその中のgeneric blockへ複製する `r_(π_s,π_η)` そのものである。支持を制限するmapも同じrootを読むため、この同定は両微分と可換となる。

## C3 — 二値合流の完全列

二blockについて `U=K_a∪K_b`、`I=K_a∩K_b` とする。制限 `r(c)=(c|_(K_a),c|_(K_b))` と、右−左 `ρ(x,y)=y|_I−x|_I` を作る。cellごとに、片側だけに属す場合は恒等、両側に属す場合は

```math
0\longrightarrow\Lambda
\xrightarrow{t\mapsto(t,t)}\Lambda^2
\xrightarrow{(x,y)\mapsto y-x}\Lambda
\longrightarrow0
```

となる。どちらにも属さないcellは零である。従って任意 `Λ` で短完全列

```math
0\longrightarrow C^\bullet(U)
\xrightarrow r C^\bullet(K_a)\oplus C^\bullet(K_b)
\xrightarrow\rho C^\bullet(I)\longrightarrow0
```

を得る。交差が空なら右の複体は零となる。

連結mapも明示する。`I` 上のcycle `z` を中間のcochain `(x,y)` へliftし、`d(x,y)` を `r` の一意な逆像へ戻す。その類が `∂[z]` であり、liftの違いはcoboundaryになる。こうして得る長完全列の該当部分は

```math
H^0(K_a)\oplus H^0(K_b)\xrightarrow{H^0\rho}H^0(I)
\xrightarrow{\partial}H^1(U)\xrightarrow{H^1r}
H^1(K_a)\oplus H^1(K_b)\xrightarrow{H^1\rho}H^1(I).
```

完全性から、同じmapによる自然な同型

```math
\ker H^1(r)\cong\operatorname{coker}H^0(\rho),\qquad
\operatorname{coker}H^1(r)\cong\operatorname{im}H^1(\rho)
```

を得る。従って `H¹(r)` が同型であることは、`H⁰(ρ)` が全射かつ `H¹(ρ)=0` と同値である。係数体なら

```math
\dim\ker H^1(r)=\dim H^0(I)-\operatorname{rank}H^0(\rho),\qquad
\dim\operatorname{coker}H^1(r)=\operatorname{rank}H^1(\rho).
```

前者は合流後から合流前へ送ると消える類、後者は合流後の類の像に入らない合流前の類を測る。W2では両方を原始支持から計算する。

## C4 — 任意有限block族の全交差

`K_1,…,K_m` の合併 `U` に対し、全非空添字集合の交差を保持して

```math
M^{p,q}=\bigoplus_{i_0<\cdots<i_p}
C^q(K_{i_0}\cap\cdots\cap K_{i_p};\Lambda)
```

を作る。横微分は制限の交代和、縦微分はincidence。両者は可換なのでtotal微分を `δ+(-1)^p d` とする。

一つのcell `σ` が属すblock添字集合 `I_σ` は、`σ∈U` なら非空。そのcellにおける拡大横複体は `I_σ` 上のfull simplexの拡大cochain複体である。最小の添字を挿入する符号付きhomotopyで収縮できる。cellの有限直和を取ると横の拡大列が完全となり、augmentation

```math
C^\bullet(U;\Lambda)\longrightarrow\operatorname{Tot}M
```

は擬同型である。有限二重複体を縦方向から計算すれば

```math
E_1^{p,q}=
\bigoplus_{i_0<\cdots<i_p}
H^q(K_{i_0}\cap\cdots\cap K_{i_p};\Lambda)
\Longrightarrow H^{p+q}(U;\Lambda)
```

を得る。どのblockの合流も、合併から各blockへの同じ制限をaugmentationとして持つ。従って二値合流による計算も全交差による計算もC2の同じ全体mapを計算し、その核・余核の比較に追加の選択は要らない。
