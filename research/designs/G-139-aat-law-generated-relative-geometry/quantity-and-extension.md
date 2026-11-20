# 普遍量、Law ideal、全regular extension

## 定理 A1 — 任意個のquantityとLawの表現

固定構造 `S`、小さい集合族 `D_j(S)`、`E_ℓ(S)` を与える。quantityは実際の関数 `q_j:D_j(S)→R`。Lawは `e∈E_ℓ(S)` に対する有限式の等式であり、構造のcartesian term、quantity評価、`k` の係数、加減乗算で作る。partial termを使うときの定義domainは `E_ℓ` の一部として指定する。

左辺と右辺の差を残差とする。quantity modelは全残差が零である関数族として、環Homに言及せず定義する。

```math
Q_S=\bigoplus_j C_k(D_j(S)),\qquad A_S=\operatorname{Sym}_k Q_S.
```

各basis元の像を `z_(j,d)∈A_S` とする。原始termのquantity評価を `z` に置き換えて普遍評価する。構造termは実際の演算で評価し、重複する入力はcopyingの `Δ` で複製する。この手順で残差 `r_(ℓ,e)∈A_S` が決まり、basisの自由性から一意の線形map

```math
\rho_\ell:C_k(E_\ell(S))\longrightarrow A_S,
\qquad e_e\longmapsto r_{\ell,e}
```

を得る。`I_S=(r_(ℓ,e) | ℓ,e)` と置く。

任意の `q` は直和の普遍性で線形map `Q_S→R`、Symの普遍性で環射 `ev_q:A_S→R` を一意に定める。式に関する帰納法により

```math
\operatorname{ev}_q(r_{\ell,e})=\text{原始Lawの残差}_{\ell,e}(q).
```

変数・係数で成立し、構造termでは N2.1、環演算では `ev_q` の環射性を使う。従って `q` がlawfulであることと `I_S⊆ker ev_q` は同値。商環の普遍性から

```math
\operatorname{LawfulQuantity}_S(R)
\cong\operatorname{Hom}_{k\text{-alg}}(A_S/I_S,R)
\cong\operatorname{Hom}_k(\operatorname{Spec}R,\operatorname{Spec}(A_S/I_S)).
```

逆写像は各 `z_(j,d)` の像を読む。全ての逆関係は生成元上の一致で証明される。`R→R'` はquantityの各値を送り、環射側では後合成するので自然性も同じ生成元上で成立する。各式は有限だが、`j,d,ℓ,e` には有限性を使っていない。零環でも同じ普遍性が成立する。□

## 系 A2 — 全可換代数と全moduleの回収

可換 `k` 代数 `S` について変数 `z_s (s∈S)` を置き、

```math
z_{s+t}-z_s-z_t,\quad z_{st}-z_sz_t,\quad z_{c\cdot1}-c\quad(c\in k)
```

をLaw生成元とする。`z_s↦s` は商環から `S` への射を与える。逆に `s↦[z_s]` は上のLawによって `k` 代数射であり、両合成は各 `s`、各生成元 `[z_s]` で恒等。従って `A_S/I_S≅S`。

`k` 代数射 `h:S→S'` は `z_s↦z_(h(s))` を与え、上の同型の下でまさに `h` となる。scheme側は `Spec S'→Spec S`。従って固定 `k` 上の全代数Homの反変な対応を回復する。`k=Z` とすれば全単位的可換環Homを回復する。基礎環自体を変える場合はその構造射と定数も同時に運ぶ。

`k` module `M` では変数 `z_m` に加法・scalar倍保存のLawだけを課す。商環へのmapは任意の線形map `M→R` と全単射である。より直接には、`m↦[z_m]` から `Sym M→A/I`、`z_m↦m` から逆射を作り、生成元で互いに逆と分かる。よって任意moduleで `A/I≅Sym M`。

scheme `T` 上の任意quasi-coherent module `Q` にも同じ線形quantityを用いる。局所affine上では上のSymの普遍性、重なりでは同じ線形mapの制限により、

```math
\operatorname{Hom}_T(T',\operatorname{Spec}_T\operatorname{Sym}Q)
\cong\operatorname{Hom}_{\mathcal O_{T'}}(f^*Q,\mathcal O_{T'})
```

を得る。任意rankで成立し、`Q` のdualizabilityは不要である。相対Specの標準定理は [Stacks 01LQ](https://stacks.math.columbia.edu/tag/01LQ)。その入力 `Sym Q` は上の原始線形quantityから構成されたものである。

## C1 — 残差の三つの意味

既存 `ArchitecturalEquationSystem` の `violationCoordinate` と `equationResidual` は異なるfieldである。前者の値から後者を自動的に定める規則はない。各context、index、atom、objectについて、その実際の値とrestriction式を保持する。

1. 任意残差 `ε:D→O` はgraph `{(d,ε(d))}` として保持する。graphの一意な値を読む写像は元の関数を回復する。
2. `O` に指定 `k` module構造があれば、固定値を `ε(d)⊗1∈O⊗_k R` へ送る。環射・元のrestriction・指定された線形比較と可換である。入力 `d` を新しい係数の点へ拡張する操作ではない。
3. quantity reading `q:D→k^X` に沿うregular extensionは、下の空間の点として選ぶ。その普遍多項式を変動quantityで評価する。元のgraphとの一致は空間の定義方程式から証明される。

有限式で与えた残差では A1 の評価定理が第三の選択を与える。任意関数の場合にはその選択が存在するとは限らず、一意とも限らない。

## 定理 C2 — 全自然operationは多項式

`k` 代数の圏上で `F_X(R)=R^X`、`F_1(R)=R` とする。任意の小さい `X` について

```math
\operatorname{Nat}(F_X,F_1)\cong k[t_x\mid x\in X].
```

**証明。** 自然変換 `η` を `k[t_x]` の普遍tuple `(t_x)` に適用し、`p=η((t_x))` と置く。任意のtuple `a∈R^X` は唯一の環射 `ev_a:k[t_x]→R` を定める。自然性から `η_R(a)=ev_a(p)`。逆に多項式評価は全環射と可換である。両合成は普遍tupleで恒等。多項式が有限個の変数と単項式しか使わないことも、この等式から従う。□

`k=F_p` の `t,t^p` は全native点 `a∈F_p` で一致するが、普遍環 `F_p[t]` で異なる。従って自然familyとして異なる。`k=Q` の関数 `δ₀` は、もし多項式 `p` による延長を持てば無限個の非零有理数を根に持つので `p=0`、しかし `p(0)=1` となり矛盾する。

## 定理 C3 — 全次数・全supportの拡張空間

任意の `D,X,q:D→k^X,ε:D→k` を固定する。`Mon(X)` を有限supportの指数列が定める単項式集合とする。有限集合 `F⊆Mon(X)` ごとに

```math
E_F=\operatorname{Spec}
 k[b_m\mid m\in F]/
 \left(\sum_{m\in F}b_m m(q(d))-\varepsilon(d)\mid d\in D\right).
```

`F⊆F'` のとき新係数を零に送る環全射があり、閉埋込み `E_F↪E_F'` を得る。`E=colim_F E_F` とする。任意 `k` 代数 `S` に対し、その `S` 点は全 `S` 代数 `R` で自然なoperation `R^X→R` で、各native tuple `q(d)` の像が `ε(d)` のscalar extensionに等しいものを全て分類する。

**証明。** C2 を基礎環 `S` で適用するとoperationは一意な `p∈S[t_x]`。その有限単項式supportを `F` に取る。native値一致はちょうど `E_F` の全方程式である。異なる有限support表示で同じ多項式なら、その和集合で全係数が一致するのでcolimitの同じ点となる。逆向きは普遍多項式 `Σ b_m t^m` の評価。基礎環変更について係数を送る式そのものなので自然である。□

`D=k^X,q=id` の場合、次の判定を得る。

- `k` が無限体ならnative多項式延長は存在すれば一意。差の有限変数集合に制限し、一変数多項式の根の個数を変数数について帰納すれば差は零である。任意 `k` 代数 `S` 上でも、各変数で次数を上回る個数の相異なる `k` の点を選ぶとVandermonde行列式がunitなので同じ一意性が成り立つ。
- `k=F_q` なら評価核は `(t_x^q-t_x)_x`。有限変数に絞り、各変数の次数を `q` 未満に割り算で落とす。そのremainderが全点で零なら、一変数の根の個数の帰納で全係数が零。逆包含は有限体の式から明らかである。native延長が存在する必要十分条件は `ε` が有限個の座標だけに依存すること。必要性は多項式の有限性、十分性はその有限座標上のLagrange補間、例えば各点 `a` の特性関数 `∏_x(1-(t_x-a_x)^(q-1))` による。

有限体の存在判定はnative `k` 点についての主張である。非零 `k` 代数への拡張でも必要性は保たれるが、零環は別である。schemeの空性とnative点の不存在を混同しない。

### 計算 C3.1 — 整数値だが整数係数ではない関数

`D=Z,q(n)=n,ε(n)=n(n-1)/2`、`F={1,t,t²}` とする。`n=0,1,2` の式から

```math
b_0=0,\qquad b_1=-b_2,\qquad 2b_2=1.
```

逆にこの三式なら、任意整数 `n` で `n(n-1)=2c_n` と書けるから、`b₂n(n-1)=c_n` となり全式を満たす。従って座標環は `Z[b₂]/(2b₂-1)≅Z[1/2]`。このchartは非空だが `Z` 点を持たない。これは分母を必要とする選択を、無断でnativeな延長にしない例である。

## C4 — 有限supportのLawとrestrictionの逆極限

`X` 上の有限support quantityの関手は

```math
R^{(X)}=\underset{F\subseteq X\text{ finite}}{\operatorname{colim}} R^F
```

で、遷移はzero extensionの閉埋込みである。一方、restrictionを遷移にする逆極限は

```math
\underset{F\subseteq X\text{ finite}}{\operatorname{lim}} R^F=R^X.
```

後者の等式はsingletonで値を読み、有限集合上でそれらを束ねる二方向の写像で証明される。`X` が無限、`R≠0` なら全座標1の族は逆極限に属し、有限supportのcolimitには属さない。有限restrictionの全互換性から有限supportは導けない。有限supportを要求するLawはこのcolimit関手として保持する。

## 定理 C5 — Context・operation・代入のcoherence

小さい残差族 `(D_i,X_i,q_i,ε_i)` と、原始宣言から生成される型付きのcontext restriction、operation、term substitutionを固定する。係数的に解釈する比較は、その構文または既に選んだ拡張点で与える。任意のnative関数のregular性を仮定なしに付け加えない。

各 `i` の有限単項式support `F_i` を選んだprofile上で、全係数 `b_(i,m)` を持つ多項式環を作り、C3 のnative一致式を課す。各coherence正方形の二経路を普遍tupleで評価する。差は有限多項式なので、その全係数を追加のideal生成元とする。任意個の正方形・残差を許すが、一つの式で必要な和と積は有限である。

この商環の点と互換な拡張族は全単射である。必要性は普遍tupleへの評価。十分性は、係数が零の多項式は全代数上で零であること、および C2 により普遍tuple上の等式が全自然familyの等式を含意することによる。supportの拡大は新係数を零にし、同じ式に戻るので閉埋込みを誘導する。全profileのcolimitが全互換拡張を分類する。宣言されたterm代入の合成・単位についても、有限syntax木の帰納で同じ比較が保たれる。

各chartには `r_i^univ=Σ_m b_(i,m)t^m` があり、overlapとなるsupport拡大で一致する。これが全moduli上の普遍残差である。固定 `d` に代入すれば `ε_i(d)` なので元graphと一致する。変動quantityをさらに付け加え、各必要残差の評価をidealとして零にすればLawの零点familyが得られる。この零点familyは A1 と同じ商環の構成である。

native値一致だけでは十分でない。`F_p` 上で二contextのrestrictionを恒等とし、一方の延長を `t`、他方を `t^p` とする。native値は全点で等しいが、coherenceは普遍環上で `t=t^p` を要求し、成立しない。従って追加の係数等式は実質的な条件である。

## C6 — 三つのmodule familyと実際の比較

任意 `k` module `M` について、

```math
M\otimes_kR,\qquad \operatorname{Hom}_k(M,R),\qquad C_R(|M|)
```

はそれぞれ「係数を拡張した元」「線形quantity」「native元をbasisとするcopying module」である。

`C_R(|M|)→M⊗R` は `e_m↦m⊗1` で生成される線形map。一般に単射でなく、例えば `e_(m+n)-e_m-e_n` を消す。group-likeな点に制限したmapは [B1](descent-and-algebraicity.md) の比較となる。任意の `M` に `M⊗R≅Hom(M,R)` を与えるmapはなく、そのような同型は選んだ自己双対性など追加dataを必要とする。

自然なmap `M^∨⊗R→Hom_k(M,R)` は `φ⊗r↦(m↦φ(m)r)`。`M` が有限projectiveならdual basisにより同型。一般には同型でない。例えば `n≥2`、`k=Z,M=Z/n,R=Z/n` では左辺は零、右辺は非零である。任意の `M` には評価 `M⊗Hom(M,R)→R` があり、`Sym M` は第二のfamilyを表す。第一のfamilyを `Spec Sym M^∨` で表すには `M` のdualizabilityを使う。この箇所が [D1](descent-and-algebraicity.md) の有限frameの役割である。
