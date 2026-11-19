# 全fragmentと加法作用adapterの複体

## A1 — 実際の変更の制限と線形問題

G-140の変更は、端点model、全sort map、語翻訳、固定部分、選択された補助dataを持つ。fragmentは、これらの原始宣言とLawの一部を、その全参照を含めて選んだものである。制限は該当するfieldを読み、元の実mapをその型のまま保持する。sortの全担体・operationのtotalityは一つのblockであり、有限個の値queryへの置換ではない。

線形問題には、affine修復と、lawfulな基準実現・平方零拡大を固定したliftを用いる。前者はE6の二項複体 `[H→V]` と不足量 `b−Lp`、後者は原始Lawの微分と全syzygyによるE2の `D⁰→D¹→D²` で扱う。平方零のunmarked版にはE6の `D^(−1)` と還元が恒等の同型作用を加える。affine有限変位の同型を加法複体で扱うのは、許容同型自体が原始加法作用として指定された場合である。これらが存在・補正・自己同型の分類に必要な複体となる。cotangent全体の高次項を使う場合の自由simplicial分解はE4で別に指定し、この三項の高次コホモロジーを無条件に高次cotangentのExtと同定しない。

原始有限fragment `F` は有限個の変数・Lawとその型・参照を含む。平方零liftでは `B_F=k[z_j:j∈F]`、`J_F=(f_ℓ:ℓ∈F)` とし、**全ての** `S_F=ker(B_F^(L_F)→J_F)` を使う。従って `D_F²=∏_(s∈S_F)M` は無限積でもよい。`F⊂G` なら多項式環の包含 `B_F↪B_G` とLaw成分の零拡張により `S_F↪S_G` を得る。各大域syzygyは有限個のLawと有限supportの係数多項式を使うため、ある `S_F` に入る。よって `S=⋃_F S_F`。

各syzygy `s` の非零成分、係数多項式の変数、対応するLawの参照を集めたものが最小の有限原始support `F_s` である。`s∈S_F` と `F_s⊆F` は同値。全原始変数・Lawについても同様にsupportを作る。制限はこれら全座標の射影となり、微分は参照する座標の有限和なので可換である。有限個のsyzygyだけを残す近似複体に置き換えていない。

有限な図式fragmentは有限個の頂点・生成射・関係のこの意味での部分表示とする。自由圏の全pathを有限個しかないと仮定しない。全pathの保存はG-140 Aの語帰納法から生成する。

一般のaffine修復では、同じ宣言supportから補正・残差の二項複体を制限する。lawfulでない基準で全多項式syzygyを評価して次数2を足すことはしない。例えば `f=(x,y)`、基準 `p=(1,0)`、syzygy `(y,−x)` では、`d⁰=id` なのにsyzygy評価は `(0,−1)` なので合成が零でない。解 `(0,0)` 自体は存在する。追加の次数2を使う場合は、`d¹L=0` と `d¹(b−Lp)=0` を原始coherenceから証明する。A4のadapterでは合成則が両方を与える。

## 定理 A2 — 大域複体と導来逆極限

次の条件は、原始表示から直接確認できる比較条件である。

1. 大域cochainは各原始labelへの任意の係数割当て `D^q=∏_(ξ∈L_q)M_ξ` である。
2. 各微分成分は有限の参照のみを使う。fragmentはその参照と必要な型・domain・Law supportに閉じている。
3. 独立な変更または補正を全fieldから回復する際、totalityや有限support等の条件がこのblock上で保たれる。

1–2では `D_F^q=∏_(F_ξ⊆F)M_ξ` と射影による制限から

```math
D^\bullet\cong\varprojlim_F D_F^\bullet
\longrightarrow R\!\varprojlim_FD_F^\bullet
```

を構成でき、最後のmapは擬同型になる。

**証明。** 通常の逆極限は、各labelを含むfragmentでの同じ値を読むことにより全積と同型。微分との可換性は2による。導来比較には、各labelの逆系 `A_ξ(F)` を、`F_ξ⊆F` なら `M_ξ`、そうでなければ0とする。逆向き包含の圏でこれは `F_ξ` における評価関手の右随伴が作るcoinduced diagramである。Hom集合が一点または空なので、この右随伴は完全であり、injective resolutionを同じ形で運べる。その逆極限は `M_ξ`、高次導来逆極限は零となる。

各次数の逆系はこれらの積である。加群とそのdiagram圏では積が完全で、injectiveの積もinjectiveなので、同じvanishingが全積にも成り立つ。次数−1以上のcochain複体に導来逆極限の二重複体を適用すると、項ごとの高次部分が消えて通常の逆極限との擬同型を得る。□

3は、この擬同型を実際の補正問題へ戻すために使う。有限行queryだけなら無限all-false行が入り、全出力の直和を有限queryへ制限した場合には全座標1の互換族が入る。これらはG-139 N3・C4の反例であり、1の全積条件や3の回復条件を満たしていない。finite supportを失うfiberを全変更へ同一視しない。

より一般の小さい添字では、原始制限からRoosのcochain replacementを作る。次数pは添字圏のp-chainに沿う積、微分はfaceの交代和と制限mapである。適切なbounded-below totalizationには

```math
E_2^{p,q}=R^p\!\varprojlim_F H^q(D_F)
\ \Longrightarrow\ H^{p+q}(R\!\varprojlim_F D_F)
```

がある。A2の座標条件を持たない場合も、この複体と大域複体の比較mapを保持し、その擬同型性を別に検査する。一般添字で高次 `R^p lim` を無条件に捨てない。

## 定理 A3 — 可算塔、Milnor列、存在条件

可算cofinal towerでは、`Rlim D_n` は

```math
\operatorname{Cone}\!\left(
\prod_nD_n\xrightarrow{1-\mathrm{shift}}\prod_nD_n
\right)[-1]
```

で計算できる。積の完全性と長完全列から

```math
0\longrightarrow\lim\nolimits^1H^{q-1}(D_n)
\longrightarrow H^q(R\!\lim D_n)
\longrightarrow\lim H^q(D_n)\longrightarrow0.
```

これは[Stacks 07KV](https://stacks.math.columbia.edu/tag/07KV)の積複体をこの原始制限に適用したものである。A2の条件、または項ごとのsurjective towerと大域回復があれば `D≃Rlim D_n` となる。

大域残差 `o∈H¹(D)` が全有限段で零でも、残る類は `lim¹H⁰(D_n)` に属し得る。`H⁰(D_n)` のMittag–Leffler性が原始制限から得られる場合、この群は零となり `o=0`、従って実補正が存在する。MLによるvanishingは、各段の安定像へ移してsurjective towerにし、`x_n−f_nx_(n+1)=a_n` を逐次解く積複体の計算からも得られる。

例えば有限集合の線形係数群、または固定した段で有限長加群となる系では、制限像の降鎖が安定するのでMLである。全補正座標を落とす射影塔もsurjectiveなのでMLになる。ただし `R^n` の射影塔の逆極限は `R^N` であり、非零環では一段の有限座標で全自由度を回復できない。有限段での決定には [D1](effective-solving.md) の追加の構成が必要である。

## 定理 A4 — 任意の小さい加法作用diagram

各頂点 `v` に非空public担体 `P_v`、その指定された推移的作用、hidden加群 `M_v` を置く。状態は `P_v×M_v`、観測はpublic成分。保持する操作は全hidden translationと、hidden成分を変えない指定public作用である。

同じ担体・同じ入力作用を保つ全state mapはtranslationである。実際、観測保存から `h(p,m)=(p,F_p(m))`。全translation保存に `m=0` を代入して `F_p(m)=m+c_p`。public作用の保存と推移性から全 `c_p` が同じ `c∈M_v` になる。逆にこのtranslationは全操作と観測を保つ。非空性は `c` の回復に使う。

edge `e:s→t` のpublic mapと線形部 `L_e:M_s→M_t` を固定し、adapterを

```math
h_e^a(p,m)=(p_e(p),L_em+a_e)
```

とする。categoryのdiagramではpublic側にも `p_id=id,p_(fe)=p_fp_e` を課し、両端でその同じpublic diagramを固定する。hidden側には `L_id=id,a_id=0` と

```math
L_{fe}=L_fL_e,\qquad a_{fe}=a_f+L_fa_e
```

を課す。原始operation・adapterの全語保存はG-140 Aの同じ評価による。

`a` から `b` への全意味変更は各頂点のtranslation `c_v` であり、adapter自然性は

```math
c_t-L_ec_s=b_e-a_e.
```

従って `D⁰=∏_v M_v`、`D¹=∏_(e:s→t)M_t`、
`(d⁰c)_e=c_t−L_ec_s` を原始式から得る。category関係に対し

```math
(d^1r)_{e,f}=r_f-r_{fe}+L_fr_e
```

を課すと `d¹d⁰=0`。高次も恒等射を含む全composable chainの最終頂点の加群に値を取るcochainを用い、

```math
(d^qr)(e_1,\ldots,e_{q+1})
=r(e_2,\ldots,e_{q+1})
+\sum_{i=1}^{q}(-1)^i r(\ldots,e_{i+1}e_i,\ldots)
+(-1)^{q+1}L_{e_{q+1}}r(e_1,\ldots,e_q).
```

二回のface削除の対消去と `L_(fe)=L_fL_e` から `d²=0`。`b−a` は1-cocycleで、`[b−a]=0` が全変更の存在と同値、非空な全解は `H⁰` のtorsorとなる。free graphのdiagramでは生成edgeの式を使い、全pathへ延長することで同じ分類を得る。

各cochain labelは有限chainと有限参照を持つので、有限fragmentはその全頂点・edge・関係を保持して作れる。全加群を一つの係数blockとして読むこの表示はA2を満たす。

## A5 — 任意moduleの係数変更

native加群 `M_v` を `k^(I_v)/im Q_v` と自由加群で表示し、係数変更後を

```math
(M_v)_R=\operatorname{coker}(Q_v\otimes_kR)
\cong M_v\otimes_kR
```

とする。各adapterの線形部も生成元の有限和で表示し、関係を消すことを検査する。係数変更と合成はこの商の普遍性から可換である。各translation係数は商加群の実際の元であり、有限和の代表とその関係witnessを商にして回復する。

任意moduleの元の関手を無条件に `Spec Sym(M^∨)` としない。有限projectiveなら双対性によりこのschemeが `M⊗R` を表し、上のadapter式はそのscheme上の式となる。一般にはG-139の表示関手と商を用いる。hidden `Z` の場合は `Z⊗R=R` であり、次稿の `A¹_R` が全translationを表す。
