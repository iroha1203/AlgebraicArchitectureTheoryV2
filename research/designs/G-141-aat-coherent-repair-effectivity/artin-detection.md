# 原始消去と全Artin試験の検出次数

## 定理 F1 — 定義的補助演算の消去

任意の可換環 `k` 上で、型・階数・生成元を固定した表示 `O` に

```math
Y_j=F_j(O,Y_1,\ldots,Y_{j-1})\quad(1\le j\le m)
```

と追加Law `G_α=0` を加えて `P` とする。依存順に `Y_j` を代入し、`O` の原始式 `bar G_α` を生成する。G-139 Pのchart上でその全成分をidealに取り、基底変更が成分を可逆に運ぶのでideal sheaf `J_u` を得る。

任意 `R`-実現の `Y₁,…,Y_m` はこの順序で一意に決まる。追加Lawはちょうど `bar G_α=0` となる。従って全 `R` で自然に

```math
\operatorname{Sem}_P(R)\cong V(\mathcal J_u)(R)
\subseteq\operatorname{Sem}_O(R).
```

表現するschemeのmapは閉埋込みである。全構造保存射はtermの評価を保つので、新しい `Y_j` も自動的に保つ。従ってunmarked `Real_P→Real_O` はfull faithfulで、essential imageは追加残差が零の実現、自己同型群は元のものと同じ。追加Lawが空なら全係数環上で同値となる。

## 定理 F2 — 全局所Artin代数による次数rの判定

ここから `k` を体、`O,P` を有限表示とする。`x∈Sem_P(k)`、観測点 `a`、局所環 `A=O_(M_O,a)`、極大ideal `m`、`J=(J_u)_a⊂m` を取る。

剰余体とその同定が `k` である局所Artin `k`-代数 `R` 上のpointed変形は、局所 `k`-代数射 `A→R` である。`P` 側はそのうち `J` を消すもの。任意 `r≥0` について次は同値である。

1. `n_R^(r+1)=0` を満たす全てのこの `R` 上で、pointed変形の比較が自然同値である。
2. `J⊂m^(r+1)`。
3. 普遍観測変形 `A→A/m^(r+1)` が `P` へliftする。

**証明。** 2なら局所射が `m` を `n_R` へ送るため全ての `J` が零となり、F1の一意性から1。1に普遍商を適用して3。3の因子分解条件は2そのものである。

普遍商が許された試験環であることも有限表示から従う。`A` はNoetherianで剰余体は `k`、`m` は有限生成だから各 `m^j/m^(j+1)` は有限次元 `k`-空間。有限個の層を持つ `A/m^(r+1)` は有限次元の局所Artin `k`-代数である。□

## 定理 F3 — 最初の失敗と局所同型

`J≠0` のとき

```math
\nu=\max\{n\mid J\subseteq m^n\},
```

`J=0` のとき `ν=∞` とする。`J⊂m` なので有限の場合 `ν≥1`。[Krull交叉](https://stacks.math.columbia.edu/tag/00IP)の `∩_nm^n=0` から、非零 `J` が全冪に入ることはない。包含する次数は下に閉じた整数の集合なので最大値が存在する。

F2により、比較は `r<ν` で全Artin試験に通り、初回 `r=ν` で失敗する。また

```math
\text{全次数で同値}\ \Longleftrightarrow\ J=0
\ \Longleftrightarrow\
a\text{ のあるopen近傍で }M_P\to M_O\text{ が同型}.
```

最後の同値では `J_u` の有限生成性を使う。stalkで各生成元が零なら、有限個の消去分母の積が零化するopen近傍を与える。全 `R` 上での同値は `J_u=0` と同値である。逆向きは各affine chartの普遍点へ適用してidealを零とすることで得る。

## 定理 F4 — 普遍初回拡大と相対障害

有限 `ν` に対し

```math
R'=A/m^{\nu+1}\longrightarrow R=A/m^\nu,\qquad
I=m^\nu/m^{\nu+1}
```

を取る。`I²=0`、`mI=0`。`J⊂m^ν` だから基準 `A/J→R` があり、普遍観測liftは `A→R'`。map

```math
\kappa_u:J/J^2\to I,\qquad f\longmapsto f\bmod m^{\nu+1}
```

はwell-definedで非零である。`J²⊂m^(2ν)⊂m^(ν+1)` と `J⊄m^(ν+1)` がそれぞれを与える。このmapはE5の指定観測liftの残差そのものであり、その相対障害は非零。閉埋込みなので、同じ観測liftを保つ候補は存在すれば一意である。

`ν≥2` なら、観測liftを変える任意のderivation `δ:A→I` も `J` を消す。実際 `mI=0` なので、`m^ν` の積を微分した各項は少なくとも一つの `m` 因子で `I` を掛けて零となる。従ってどの観測liftにも同じ非零 `κ_u` が残り、基準 `P`-実現自体が `R'` へliftしない。

`ν=1` では指定観測方向のliftだけが失敗する。基準は `R=k` の点なので、`A/J→k→A/m²` という定値liftは存在する。この二つの存在問題を区別する。

## F5 — 共有演算の差としての同じ障害

消去残差の各成分と同型の共有演算 `Z_α` を導入し、二文脈を `Z_α=0` と `Z_α=bar G_α` とする。Čechの順序は零Law側を先、定義側を後に取る。任意の指定観測liftに対して、それぞれの `Z_α` は0と実際の `bar G_α` の評価に一意に決まり、局所liftが得られる。

`J=(bar G₁,…,bar G_q)` の全syzygy表示にE2を適用すると

```math
\operatorname{Hom}_{A/J}(J/J^2,I)\hookrightarrow I^q
```

が生成元の像による単射となり、像は全syzygyの評価式を満たすtupleである。`κ_u` の像は共有部の右−左の差 `(bar G_α(\widetilde a))_α` である。

固定観測の下で両局所定義を保つ `Z` の補正は零なので、この差の零性がmatching、従って大域liftの存在と同値になる。任意の共有tupleが実残差とは限らず、像は上の全syzygy条件で検査する。これがEの合法修復との比較である。

## F6 — 表示変更、合成、pointed Real

改名、chart変更、相互導出を持つ冗長Lawは同じideal sheafを与える。定義だけの補助演算の追加・消去はF1の同型でidealを運ぶ。局所環・その極大ideal冪・生成元を評価する `κ_u` も同じmapで運ばれる。従って `J,ν,κ_u` と実lift比較は不変である。

二つのこの型のreadingを合成する。局所環を `A₀→A₁=A₀/J_u→A₂=A₁/J_v`、合成idealを `K` とする。`m₁^n=(m₀^n+J_u)/J_u` だから

```math
K\subseteq m_0^n
\ \Longleftrightarrow\
J_u\subseteq m_0^n\ \text{かつ}\ J_v\subseteq m_1^n.
```

従って `ν(vu)=min(ν(u),ν(v))`。無限値も同じ包含条件で扱える。

pointed `Real` の対象は実現と還元同型、射はその同定と可換な同型とする。局所Artin環上で各有限projective moduleはfreeであり、基点の `m_v≥n_v` 個の生成元は任意にliftすればNakayamaにより全射のままである。従って全unmarked変形へmarked liftを付けられる。追加Lawはmarkに依存せず、F1のfull faithfulnessにより、指定観測liftの相対groupoidは空またはcontractibleになる。

生成元の選択空間は全射matrixのopenであり、unmarked実現に対してsmoothなatlasを与える。二つの生成元数・選択を比較するには両方を保持するatlasを取る。体上の対応する点でsmoothな座標を加えた完備局所環は `widehat A[[w₁,…,w_s]]` の形となり、`(m,w)^n∩widehat A=m^n widehat A` は定数係数を読むことで分かる。忠実平坦な完備化を戻すとidealのorderを保つ。よって生成元数と選択を変えても `ν` とpointed Realの全Artin判定は一致する。

## F7 — 構文から得る次数上界

自由観測chart `k[z₁,…,z_d]` で、変数を次数1、定数を次数0とする。有限和の上界は最大、積・tensor成分の上界は和、補助定義は依存順の代入で計算する。この有限構文再帰により、全消去残差に共通の次数上界 `D` を生成できる。

`J≠0` なら一つの非零残差 `f` がある。点 `a` へ平行移動した `f(a+w)` も次数は `D` 以下で、非零項の最小次数は `D` 以下。従って `ν≤D`。自由な多項式環では局所化で非零多項式が消えないことを用いる。既存の関係を持つ観測環ではこの上界を表示の見かけの次数から主張せず、[H5](witnesses.md)で差を示す。

## F8 — 一般係数の冪零商とbase change

`k₀`-代数のaugmentation `B₀→k₀`、kernel `m₀`、`J₀⊂m₀` を与える。任意の `k₀→k₁` で `B₁=B₀⊗k₁`、`m₁=m₀B₁`、`J₁=J₀B₁` とする。augmentationは定数sectionを持つので、この `m₁` は新しいaugmentationのkernelである。idealの生成積と右完全性から

```math
(B_0/m_0^{r+1})\otimes k_1\cong B_1/m_1^{r+1},\qquad
(B_0/(J_0+m_0^{r+1}))\otimes k_1
\cong B_1/(J_1+m_1^{r+1}).
```

二商間のmapのkernelを `D_r` とする。tensorした右完全列により、新kernelは `D_r⊗k₁` の**像**である。flatなら左端も単射になりkernelと同型、faithfully flatなら零性も反映する。任意係数のこの冪零商がArtin環であるとは限らず、体・有限表示におけるF2とは区別する。

## F9 — Jet試験との比較

F2は、剰余体 `k` とnilpotenceの指定を持つ**全局所Artin代数**を量化し、その中の普遍商 `A/m^(r+1)` を使う。曲線jetの `k[t]/(t^(r+1))` だけを検査する主張ではない。

係数を動かすpointed jet functorは、任意 `k`-代数 `K` に対する `A→K[t]/(t^(r+1))` で、`t=0` の評価が基点 `A→k→K` となるものを取る。`m` は `(t)` に入るため、`J⊂m^(r+1)` ならこの全functorにも一意のliftがある。逆の比較はjet functorのkernelを別に調べる問題であり、F2の普遍Artin商による逆向きと同じ証明にはならない。

[de Fernex–Ein–Ishii](https://arxiv.org/abs/1704.07494)のjet closureとlocal isomorphism problemは、jet schemeの比較から局所構造を読む先行問題である。ここではその試験対象と、原始消去idealに対する全Artin試験を上の二つの関手で区別する。n1020 §10・15で挙げた比較に、この明示された量化と同じidealを用いる。
