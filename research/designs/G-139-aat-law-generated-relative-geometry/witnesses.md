# 同じ構成を通る証人と反例

以下では [P0–P4](polynomial-realizations.md) の原始宣言、Atom生成、成分残差、chart、忘却をそのまま使う。各行の意味を別のpredicateで代用しない。Lawfulかどうかは P1a.3 の同じ `EquationLawful` との同値で検査する。

## W1 — 名前付き可逆操作

`k=Z`、sort `p,q`、各 `n=m=1`。演算 `f:p→q,g:q→p`、required Law `gf=id_p,fg=id_q`。五座標のsort Atomは `(sort,state,p,ranks,(1,1))` と `q` 版。生成元は `(generator,state,e_p,type,p)`、演算は `(operation,operation,f,signature,(p;q))` と `g` 版。二Lawとその各構文nodeを P1a の規則で追加する。

全生成元が基底なのでraw tupleは `(a,b)`。有限構文の合成と恒等を評価すると残差は `ba-1,ab-1`。従って

```math
M=\operatorname{Spec}\mathbb Z[a,b]/(ab-1),\qquad
\operatorname{Sem}(R)=\{(a,b)\in R^2\mid ab=1\}.
```

`(1,1),(-1,-1)` は `Z` 上で別のlawfulな点、`(0,0)` は残差が `-1` なので不成立。sort `p,q` とoperation `f,g` を交換するreadingは `(a,b)↦(b,a)`。`Q` 上の `(2,1/2)` で値が変わるので非恒等である。同階数でも型の恒等と交換は異なる作用を持つ。

marking付きでは `(2,1/2)` と `(1,1)` は別点である。生成元を忘れると、元の実現から後者への同型は `h_p=2,h_q=1` で与えられる。

```math
h_q\,2=1\,h_p,\qquad h_p(1/2)=1\,h_q.
```

二つの基底変更は可逆だが名前付き生成元を固定しない。従って同じ `M→[X/G]` がこの二点を同型なunmarked実現へ送る。

## W2 — 二生成元と大域実現

一sort `v`、`n=1,m=2`、演算 `T:v→v`、required Law `T=0`。第一列を基底にしたchartでは `q=(1,u)` と `T=t`、第二列では `q=(v,1)` と `T=t'`。残差は `t,t'`。overlapは `u,v` をinvertし `v=u⁻¹`、rank1の共役から `t'=t`。従って二つのaffine lineをこの逆数変換で貼り、`M=P¹_Z` を得る。

`q=(2,3):Z²→Z` は `-2+3=1` により全射。kernelは `Z(3,-2)`。実際 `2a+3b=0` なら `3|a`、`a=3r,b=-2r`。どちらの列も `Z` のunitではないため一個の基底chartに全体では入らないが、`D(2)` と `D(3)` が `Spec Z` を覆い、それぞれの座標は `3/2` と `2/3` である。overlapでは互いに逆数。これは同じkernelと `T=0` の大域 `Sem` 点を与える。

`m=1` に変えると生成元が必ず基底なので `M=Spec Z`。`m=2` の `P¹` と同型ではない。例えば体へのbase change後の次元がそれぞれ0と1である。unmarked実現はどちらもlineと零演算なので同じである。

## W3 — 二重点と普遍残差

一sort `n=m=1`、演算 `T`、required Law `T²=0`。raw tupleは `t`、残差はsyntaxの合成から `t²`。従って `M=Spec Z[t]/(t²)`。

`R=Z[ε]/ε²` の `t=0` と `t=ε` はともに残差零だが異なる点である。`ε≠0` は `R` の自由 `Z` basis `1,ε` から分かる。体値点では必ず `t=0` なので、この二点を体値点だけでは回復できない。`(t²)` をradical `(t)` に変えると第二の点を失う。

`k=Q` でambient `B=k[t]`、Law ideal `J=(t²)`、`x(t)=ε∈k[ε]/ε²` を取る。普遍残差は `t²≠0`、評価後残差は `ε²=0`。`D(t)` の逆像は `D(ε)=∅`。従ってこのcontextの評価先は零環であり、大域環 `R` へ `B_t→R` を作ることはできない。

`J/J²=(t²)/(t⁴)` は `B/J` 上のrank1自由moduleで、`[t²]` がbasisである。`x` でpullbackしてもrank1のmoduleが残る。一方、評価後のidealは零で、そのconormalも零。普遍ambientでconormalを作る順序が実質的な差を生む。

## W5 — 生成元を忘れた自己同型

W2の `T=0` を持つlineからmarkingを忘れる。任意lineのframe torsorは `G_m` torsor、逆にtorsorからlineをdescentできるので `Real≃B G_m`。W2の忘却は `P¹→B G_m`。

`Z` 上のline `Z` のmap `-1` は零演算を保つ非恒等自己同型である。`q=(2,3)` を保つなら全射性から `h=id` であり、`-1` は保たない。test line `L` 上の忘却mapのfiberは `O²↠L` の全射の空間。frame上では `A²\{(0,0)}` というopenになり、P4のrepresentable smooth surjectiveという証明の同じ例になる。

## W6 — Cocycleを満たさない遷移

三つの `A¹_Z` のpairwise overlapを各全体とし、点座標で `φ₀₁(t)=t+1,φ₁₂(t)=t+1,φ₀₂(t)=t` とする。逆方向は各逆写像を取る。各pairはscheme同型だが

```math
\phi_{12}\phi_{01}(t)=t+2\ne t=\phi_{02}(t)
```

なのでcocycleを満たさない。例えば `t=0` で2と0になる。この遷移を保持した接着は存在しない。これはP2の基底変換から生成した遷移ではなく、pairwise同型だけではその構成を置き換えられないことの反例である。

## W7 — Law追加と非flatな係数変更

一sort `n=m=1` の演算 `T` にLawを課さない表示は `M_P=A¹_Z`。`T²=0` をrequiredとして追加した `P'` は `M_(P')=Spec Z[t]/(t²)`。readingは型と演算を固定し、scheme射は同じ `t` を送る閉埋込みである。`(t²)≠0` なので同型ではなく、例えば `t=1` の点はsourceにliftしない。

`Z→F₂` に沿って両方のraw変数とLaw生成元を送ると、`F₂[t]` と `F₂[t]/(t²)` になる。この正方形は同じ生成元のimageからcartesianである。係数射は非flatだが、extended idealと商のtensorによるP2.1の証明が適用される。

`T=0` をoptionalにしただけでは全ての `t` が実現に残る。これを前提にして、required Law `S=0` を持つsourceの演算 `S` にtargetの `T` を代入することは許されない。targetの `t=1` がLawfulであるのにsource Lawの値が1になる具体的反例である。

## W8 — 共有kernelと宣言の組立て

`k=Q`、sort `p,q,r`、全rank1、生成元数 `1,2,1`。左contextに `p↔q` の二演算、右contextに `q↔r` の二演算を置き、各往復が恒等というrequired Lawを置く。交差には共有sort `q` の二生成元を両方含める。

共有の全射を `(2,3)`、左の可逆演算を `(2,1/2)`、右を `(3,1/3)` とする。全残差はそれぞれ `2·1/2-1=0`、`3·1/3-1=0`。交差のkernelは双方 `Q(3,-2)` なので、P2.1のfieldごとの組立てにより一つの実現になる。各演算のmatrixを選んだ基底へ移せば、これは同じP2のchartとoverlapにも通る。

右contextだけ共有全射を `(1,0)` に変更しても、右の往復Lawは成立する。しかしそのkernelは `Q(0,1)` であり、`Q(3,-2)` と異なる。共有markingを保つline同型があればkernelは同じになるので、そのような同型もない。従ってこれらの局所lawful点は同じ生成元を保持して組み立てられない。

## 零階数、copying、非連結係数

全 `n_v=0`、演算・Lawが空の場合、唯一のkernelは `R^(m_v)`、商は零。全生成元を選ぶ基底indexは空、raw座標も空、`GL_0=1`。従って任意の `m_v` で `M=Spec k`、unmarked stackも `Spec k` となる。非空のLaw族を付ける場合は、その原式を通常どおり評価する。tensor unit上の矛盾するscalar等式まで自動的に成立するとはしない。

Boolean ANDを `C_Z(Bool)` のbilinear map `μ(e_a⊗e_b)=e_(a∧b)` へ運ぶ。copyingを使う元の冪等Lawは `μΔ=id` なので、`2e_true` に対しても `μΔ(2e_true)=2e_true`。コピーを普通のtensor平方に取り替えると `μ((2e_true)⊗(2e_true))=4e_true` となり失敗する。N2の `Δ` がtermの重複を担っている。

非連結環 `R=Z×Z` で `e=(1,0),1-e=(0,1)`。一点から二点へのcoalgebra射

```math
e_*\longmapsto e\,e_0+(1-e)e_1
```

はcounitとcopyingを保つ。どちらのbasis元でもないので、単一のnative集合写像からは来ない。schemeでは二つのclopen成分で違う出力を選ぶ射である。これもN2の全Hom分類、N3の二出力profile、B1のnative比較の同じ例である。
