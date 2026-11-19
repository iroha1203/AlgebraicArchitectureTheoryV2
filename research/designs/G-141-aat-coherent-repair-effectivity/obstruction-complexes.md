# 原始Lawからのlift、syzygy、相対障害

## E1 — 独立な実現liftとsmooth ambient

可換環 `k`、有限sort・有限演算・有限Lawの多項式表示 `P`、`k`-代数 `R`、独立なmarked実現 `x∈Sem_P(R)`、平方零全射 `R'↠R`、kernel `M` をこの順に取る。`M²=0` により `M` は `R`-加群となる。liftとは、同じsort・生成元・演算・required Lawを持ち、還元が `x` となる `Sem_P(R')` の元である。

Lawを忘れたambient `Y` は、G-139 Pの有限個の生成付き局所自由商のGrassmannianに、各演算のHom vector bundleを置いて作る。演算の入力は有限tensorなのでそのHomは有限局所自由である。Grassmannianの基底chartとvector bundleのchartから `Y` は `k` 上smoothとなる。Lawの原始成分をideal sheaf `J` として `M_P↪Y` を作る。

affine test `Spec R` 上ではambient liftが存在する。各有限projective商 `Q_v` を冪等matrixで表し、そのmatrixを `R'` へliftする。近似冪等元 `e` の誤差が平方零なら `3e²−2e³` は冪等元なので `Q'_v` を得る。生成元の像をliftして `R'^(m_v)→Q'_v` を作る。還元のcokernelは零であり、kernel idealがnilpotentだからこのmapは全射である。各演算のsourceはprojectiveなので、targetの全射 `Q'_w→Q_w` に沿って演算もliftできる。0入力演算も同じ議論に含む。

この構成は `x` が一つの基底chartに入ることを仮定しない。全射付き実現を標準商へ戻すG-139の比較により、ambientの実際の `R'`-点を得る。

## E2 — 全syzygyから生成する複体

一つの基底chartで

```math
B=k[z_1,\ldots,z_n],\quad J=(f_1,\ldots,f_r),\quad A=B/J,\quad
S=\ker(B^r\longrightarrow J)
```

とする。最後のmapは `(s_i)↦Σs_if_i`。全 `s∈S` を使い、

```math
D^0=M^n\xrightarrow{d^0=\operatorname{Jac}(f)(x)}
D^1=M^r\xrightarrow{d^1}\prod_{s\in S}M,\qquad
(d^1r)_s=\sum_i s_i(x)r_i
```

を作る。syzygyを評価後のJacobianから推定せず、原始多項式上の恒等式から生成する。

**複体条件。** `Σs_if_i=0` を微分して `x` で読むと、`f_i(x)=0` により `Σs_i(x)df_i(x)=0`。従って `d¹d⁰=0`。

**Conormalとの同定。** `B^r→J` を `A` へtensorすると右完全性から

```math
S\otimes_B A\longrightarrow A^r\longrightarrow J/J^2\longrightarrow0.
```

さらに `A→R` でtensorし、`Hom_R(-,M)` を適用すると

```math
\ker d^1
\cong \operatorname{Hom}_R((J/J^2)\otimes_A R,M).
```

対応は `r_i` を `[f_i]` の像とするmapである。元の生成元の全関係を消す条件がちょうど全syzygyの式なので、両方向が互いに逆となる。`J/J²` のprojective性や、tensorの左完全性は用いない。

有限生成族 `s¹,…,s^q` が `S` を生成すると証明できた場合、全syzygyの代わりにそれらを使ってよい。任意 `s=Σb_αs^α` の評価は `s(x)=Σb_α(x)s^α(x)` なので、有限式と全式のkernelが一致する。従って `H⁰,H¹` と下記の障害は変わらない。生成性の証明なしに有限個だけを選ぶことはできない。

## 定理 E3 — 残差、存在、全lift

ambient lift `tilde z∈(R')^n` を選ぶ。`r_i=f_i(tilde z)` は `M` に入る。恒等式 `Σs_i(tilde z)f_i(tilde z)=0` と `M²=0` から `Σs_i(x)r_i=0` なので `r∈ker d¹`。

`δ∈M^n` による変更は、有限多項式の展開で二個以上の `M` 因子を持つ項が零になるため

```math
r(\widetilde z+\delta)=r(\widetilde z)+d^0\delta.
```

よって `o_P=[r]∈H¹(D)` はambient liftの選択に依存しない。その零性は `r=−d⁰δ` を満たす `δ` の存在と同値であり、この `δ` から `tilde z+δ` という実際のlawful liftを得る。逆にlawful liftとの差を取れば同じ式を得る。

一つliftが存在すれば、二liftの差は `ker d⁰=H⁰(D)` に入り、その全ての元を加えて再びliftを得る。加法作用は自由かつ推移的である。係数matrixを原始演算へ戻すG-139の同値により、これは独立な実現liftそのものの分類となる。

## E4 — Chartに依存しない複体とcotangent

`E_x=x^*Ω_(Y/k)`、`N_x=x^*(J/J²)` とし、

```math
\bar D=
[\operatorname{Hom}_R(E_x,M)\longrightarrow
 \operatorname{Hom}_R(N_x,M)]
```

を次数0、1に置く。chart上の `df_i` によるmapから生成される。E2の同定は `D` と `bar D` の次数0・1のコホモロジーを同定する。

ambient liftの `J` 上の値は `M` に入り、`J²` を消すため、大域的な `κ:N_x→M` を与える。二つのambient liftの差は `k`-derivation、すなわち `Hom_R(E_x,M)` の元であり、`κ` の変更は上の微分の像となる。E1がambient liftを構成しているので、chartに入らない `x` でもE3と同じ存在・torsor分類が成立する。

cotangent complexは原始代数の標準simplicial自由多項式分解から、各段の微分加群を作って正規化する構成を用いる（[Stacks 08PL](https://stacks.math.columbia.edu/tag/08PL)）。閉埋込みとsmooth ambientのtransitivityから、`Lx^*L_(M_P/k)` の次数−1、0の切断は

```math
[N_x\longrightarrow E_x].
```

より低い次数は `RHom_R(-,M)` の次数0・1へ寄与しない。`E_x` は有限projectiveなので、同じ次数の `RHom` は上の `bar D` で計算できる。`N_x` 自体にprojective性は要らず、その高次Extは次数2以上に現れる。従って

```math
H^i(\bar D)\cong
\operatorname{Ext}^i_R(Lx^*L_{M_P/k},M)\qquad(i=0,1).
```

指定障害の一致は、自由多項式分解の次数1の関係をambient liftで評価するmapが `f↦κ([f])` そのものであることから従う。これは[平方零変形の標準障害](https://stacks.math.columbia.edu/tag/08S3)への、原始残差を保持した比較である。

Noetherian係数・有限表示に特殊化すると `N_x` は有限表示である。有限表示 `R^a→R^b→N_x→0` にHomを取り、局所化の完全性を使えば

```math
\operatorname{Hom}_R(N_x,M)_s
\cong\operatorname{Hom}_{R_s}((N_x)_s,M_s).
```

`E_x` にも同じことが言える。従って両Homは準連接層になり、`Spec R` の有限principal affine被覆の各交差上で制限できる。各項の拡大Čech複体が完全であるため、そのtotalizationと大域 `bar D` の比較は擬同型（quasi-isomorphism）である。残差も同じ局所化を受けるので指定類が一致する。

## E5 — 指定した観測liftを保つ相対fiber

原始代入とLaw導出 `u:P→P'` から `ρ:Sem_(P')→Sem_P` を作る。`x∈Sem_(P')(R)` と、指定した `y'∈Lift_P(ρx,R')` を固定する。独立な相対liftは、`x'` が `x` へ還元され、`ρ(x')=y'` となる `P'`-実現である。

比較するambientも構成する。`X'=M_(P')↪Y'_0` と `X=M_P↪Y` に対し、`ρ:X'→X→Y` のgraphを `Y'_0×Y` に閉埋め込みする。`Y` はGrassmannian上のvector bundleなので分離的であり、このgraphは閉である。新しいambient `Y'=Y'_0×Y` はsmoothで、射影 `Y'→Y` が `ρ` を延長する。chartでは原始代入の多項式 `H` に対する `y−H(z')` を加えた同じgraph表示になる。従ってambient全体で元の代入が生成元の全射性を保つことを仮定しない。

このcompatible ambientの微分とconormalへのmapは

```math
\phi^0:\bar D_{P'}^0\to\bar D_P^0,\qquad
\phi^1:\bar D_{P'}^1\to\bar D_P^1,\qquad
\phi^1d'=d\phi^0
```

を与える。最後の式は原始Law導出を微分した連鎖律である。導出の違いは全syzygyに消される。graphの定義だけの座標を消すと元の実現が一意に戻り、局所の微分複体では新座標とその定義Lawのcontractibleな対を消せる。異なるambient lift・chartでの比較mapはこの共通graph表示を介してchain homotopyで一致する。従って導来圏と以下の次数0・1の分類は同じ原始readingで定まり、任意chart間の厳密な等号を仮定しない。以後はこのcompatible ambientの `bar D_(P')` を使う。

`F_u=Cone(φ)[−1]` を、具体的には

```math
F_u^0=\bar D_{P'}^0,\quad
F_u^1=\bar D_{P'}^1\oplus\bar D_P^0,\quad
F_u^2=\bar D_P^1,\qquad
d_F^0\delta=(d'\delta,\phi^0\delta),\quad
d_F^1(r,e)=\phi^1r-de
```

とする。ambient lift `tilde x` の残差を `r`、`ρ(tilde x)−y'` というderivationを `e` とすると、Lawの評価一致から `φ¹r=de`。したがって `o_u=[(r,e)]∈H¹(F_u)` を得る。ambient liftを `δ` だけ動かすと `(r,e)` は `d_Fδ` だけ変わる。

よって `o_u=0` は `r+d'δ=0` かつ `e+φ⁰δ=0` の同時解と同値で、これは実際の `P'`-liftと指定された `P`-liftの一致条件である。全解は `H⁰(F_u)=ker d'∩ker φ⁰` のtorsorとなる。

恒等では `Cone(id)[−1]` がcontractibleで、指定liftをそのまま回復する。合成では三つのambientを共通の積に置き、比較をその射影として選ぶ。この選択で連鎖律とLaw導出の代入が `φ_(vu)=φ_uφ_v` を与え、相対fiberを反復して作るmapと一致する。別々のgraph表示を選んだ比較は上のchain homotopyを介して一致する。平方零拡大の射は全残差をkernelのmapで送る。改名・基底変更・同値なLaw表示では自由分解と実liftの読み戻しを運ぶ。これらは選択したambient liftの差を微分の像として送るので、障害と全解の作用にも自然である。

## E6 — Affine修復、自己同型、既存conormal列

affine Law `Lz=b`、基準 `p`、変更可能な部分加群 `H` に対し、修復は `a∈H` で `L(p+a)=b` となるもの。従って存在条件は `b−Lp∈L(H)`、全解は非空なら `ker(L|H)` のtorsorである。これは有限変位に対する厳密な式である。非線形Lawの平方零変位ではE3のJacobianへ置き換わる。

unmarked実現では、還元が恒等となる同型も保持する。局所frameでそれは `1+A_v`、`A_v` は `M` 値の行列であり、逆は `1−A_v`、合成は加法である。演算と比較mapに作用させて一次部分を展開すると `d^{-1}:D^{-1}→D^0` を生成する。例えば単項演算には `A_out·μ−μ·A_in` が現れる。全Lawの保存から `d⁰d^{-1}=0`。

残差を消す補正 `δ` を対象、`δ'−δ=d^{-1}A` を満たす `A` を射とするgroupoidは、実際の還元同型を持つlift groupoidと同値である。従って非空な同型類は `H⁰(D)` のtorsor、各自己同型群は `H^{-1}(D)`。marked全射生成元を固定すると `A_vq_v=0` と全射性から `A_v=0` となり、E3の集合版に戻る。

既存conormalとの比較には評価前の普遍ambient `B` とprincipal-open siteを固定する。G-139 P1aのObservableは `B_s`、Law idealは `J_s` であり、有限積を局所化する直接計算から `(J²)_s=(J_s)²`。従って [Raw.shortComplex](../../../Formal/AG/SemanticRepair/Conormal/LawGeneratedIdealPowerShortExact.lean) は各openで

```math
0\to(J/J^2)_s\to(B/J^2)_s\to(B/J)_s\to0
```

となる。同じ制限mapで層化すれば標準conormal列である。

ambient lift `B→R'` は `J²` を消す。得られる `B/J²→R'` の `J/J²` への制限が `κ` であり、`κ=0` は**同じmap**が `B/J` を経由することと同値。liftの選択差をderivationで商にした `[κ]` はE3の `o_P` である。評価後の零idealからconormalを作り直さない。

宣言の忘却はこの局所化とは異なる。共有 `x` を保つ `Q[x,y]→Q[x]` で `xy−1` を零へ送れれば `x·φ(y)=1` だが、多項式環で `x` はunitでないため不可能である。`D(x)` 上への局所化なら `y↦x^{-1}` がある。二種類の制限はそれぞれの原始mapが存在するときに比較する。
