# 台帳の同じ原始操作から得る全比較と合法経路

## P0 — 原始表示と式評価

基礎環を `k` とし、全ての可換 `k`-代数 `R` を動かす。beforeの公開状態はrank1の `D_R=R`、afterはrank1の二型の直和 `B_R⊕C_R=R²` とする。各型に一つの基底生成元をmarkする。原始単項線形演算を

```math
p_B:B\to D,\quad p_C:C\to D,\quad
i_B:D\to B,\quad i_C:D\to C,\quad
j_B:D\to B,\quad j_C:D\to C
```

とし、それぞれの係数を `a,b,c,d,r,s` とする。加法と定数から

```math
p(B,C)=aB+bC,\quad i(u)=(cu,du),\quad j(t)=(rt,st)
```

を生成する。beforeの `apply_u(x)=x+u`、afterの

```math
\operatorname{apply}_u(v)=v+i(u),\qquad
\operatorname{compact}_t(v)=v+j(t),\qquad
\operatorname{read}(v)=p(v)
```

も同じ原始演算のtermである。初期状態は `p(v₀)=x₀` として対応させる。比較は `p:after→before`、語翻訳は `apply_u↦apply_u`、`compact_t↦[]` とする。引数sort `D` のmapは恒等である。

AtomへのencodeはG-139 P1aの同じ五座標を使う。sort `v∈{D,B,C}` には `(sort,state,v,ranks,(1,1))`、その生成元には `(generator,state,(v,0),type,v)`、各単項演算には `(operation,operation,e,signature,(source;target))`、二つの保存Lawには `(equation,law,ℓ,required,lhs=rhs)` を置く。有限構文nodeと参照edgeも同じencodeで加える。係数値Atomのpayloadが `a,b,c,d,r,s` を読み戻すので、以下の多項式残差は同じAtom入力の原始評価である。phase・状態Law・比較演算を増やす場合も同じ宣言encodeを使う。

二引数加法は `D⊕D→D`、matrix `[1\ 1]` の**線形写像**である。`D⊗D→D` の双線形写像としては扱わない。直和sortを明示する場合はinjection・projectionとbiproduct等式を置く。各原始単項演算、定数、加法の型をこの宣言で固定する。

### 定理 P0.1 — 型付きaffine termの評価一致

変数、定数、単項線形演算、直和上の加法から作る任意の有限termの原始評価は、加群上で展開したaffine式と一致する。

**証明。** 変数と定数では定義どおり。単項演算では帰納的な式に指定matrixを掛ける。加法では同じ型の二式を直和へ入れて `[1\ 1]` を作用させるので、係数と定数項を加える式になる。この構文帰納法は任意の有限termを覆い、係数環射も各有限和・積と可換である。□

従ってG-139 P1–P4の原始modelと多項式実現の同値は、この同じsort・operation・Lawへ適用できる。各phaseの状態は、ambient加群への0引数演算として状態座標を選び、その不変量の実現fiberを取って作る。例えばBusyの状態は `(B,C,h)` という三つの0引数値と後述のLawである。そのfiber自体が自由加群であるとは仮定しない。

一般のrankでも、両端のmatrixと実際の比較 `H` を変数にし、原始保存残差を課せばB3–B4のcomparison presentationを得る。両端のrankを一致させる必要はない。両端へのspanはその係数を忘れる二つのmapであり、指定両端上のfiberは全 `H,τ` と指定補助dataを保持する。合成可能な二比較のfiber productから `(H₀₁,H₁₂)↦H₀₁H₁₂` と翻訳代入を作り、保存式を合成して合成comparisonへ送る。これがB1のnerveの合成である。unmarked版では中間frame・対象の同型を保持した2-fiberを使う。

## 定理 P1 — 原子操作の全語と係数空間

原始保存式は

```math
pi=\operatorname{id}_D,\qquad pj=0,
\quad\text{すなわち}\quad
ac+bd=1,\qquad ar+bs=0.
```

実際、`p(v+i(u))=p(v)+u`、`p(v+j(t))=p(v)` と同値であり、必要性は `v=0,u=1` または `t=1` で得る。この計算は零環も含む全環で成り立つ。

固定 `R` で操作名を `R⊔R` とすれば、afterはG-126の全域 `OperationSystem` である。beforeのcompact側の操作は恒等とする。同じ左からの有限語評価についてA2により

```math
p(\operatorname{eval}_{after}(v_0,w))
=x_0+\sum_{\text{applyの出現 }u\text{ in }w}u
=\operatorname{eval}_{before}(x_0,\tau w).
```

ここで引数は全 `R` を動く。係数変更では引数sortも変更し、nativeな一部の定数だけを操作名として保存しているわけではない。二状態のbehavior関係は、この同じ `eval` と `read` からD3の定義で得られる。

### P1.1 — `SL₂×A¹` との自然同型

`ac+bd=1` の下で

```math
M=\begin{pmatrix}c&-b\\d&a\end{pmatrix},
\qquad
M^{-1}=\begin{pmatrix}a&b\\-d&c\end{pmatrix}
```

は互いに逆で `det M=1`。`k=(b,−a)` は `ker p` に入り、線形汎関数 `ℓ(B,C)=dB−cC` は `ℓ(k)=1` を満たす。実際

```math
v=i(p(v))+\ell(v)k
```

なので `ker p=Rk`。`j=(r,s)` に `ar+bs=0` を課すと、`μ=dr−cs` に対し

```math
b\mu=r-c(ar+bs)=r,\qquad
-a\mu=s-d(ar+bs)=s
```

となり `j=μk`。逆に任意の `M∈SL₂(R)` と `μ∈R` から `a,b,c,d` と `r=bμ,s=−aμ` を戻せる。両構成は互いに逆の多項式式で、全係数環に自然である。従って

```math
\operatorname{Spec}k[a,b,c,d,r,s]/(ac+bd-1,ar+bs)
\cong SL_{2,k}\times\mathbb A^1_k.
```

非零環では `ℓ(k)=1` から `k≠0` であり、比較 `p:R²→R` は非単射である。全Hom構成はこのrank変更を含む。

### P1.2 — Marked fiberと状態fiber

`p=(1,1)` を固定すると、`c=λ,d=1−λ,r=μ,s=−μ` だから係数のmarked fiberは `A²_(λ,μ)` となる。一方、固定状態 `x` のfiberは

```math
p^{-1}(x)=\{i(x)+zk\mid z\in R\}\cong\mathbb A^1_R.
```

前者は操作係数のfamily、後者は指定操作係数上の状態のfamilyである。

rank1・一生成元の単一型 `D` とunary係数 `λ,μ` の表示から、markされた三つのコピー `D_B,D_C,D_public` を作る。コピー間の指定同型を使って

```math
p=id+id,\qquad i=(\lambda,id-\lambda),\qquad j=(\mu,-\mu)
```

を定義する。逆にmarked fiberの `i_B` と `j_B` が `λ,μ` を回復し、残りの成分は二つのLawで一意に決まる。従ってこのコピーを明示した表示とmarked fiberは全 `R` に自然に同型である。markを持たない三つの任意のline bundleを、一つの型に自動的に同定する主張ではない。

## P2 — 観測できる操作語を変える場合

以後 `p=B+C`、`δ=1−λ` とする。afterのapplyは

```math
(B,C)\longmapsto(B+\lambda u,C+\delta u).
```

これを `writeB` と `writeC` の二段に分け、途中にもreadを許す。`R=Q,λ=1/2,u=2` で初期readを `x` とすれば、writeB直後は `x+1`、完了後は `x+2` になる。旧側の単一atomic applyの前後に読めるのは `x` と `x+2` であり、同じ一回のapplyを空語またはそのatomic語へ翻訳する対応では途中の `x+1` を保存できない。

これはwriteB/writeCを旧側の既存の `apply_1` 等へ翻訳し直す問題とは異なる。P1で固定した比較・一回の操作の対応を保ったまま、read可能な時点を増やした場合の反例である。同じ状態と式評価でも、比較する操作言語によって保存条件が変わる。

### P2.1 — 状態に依存するcompact

固定引数の `compact_t` は `(B,C)↦(B+μt,C−μt)`。その引数へ現在値 `t=C` を代入すると

```math
\operatorname{compact}_{all}(B,C)=(B+\mu C,(1-\mu)C).
```

同じ原始termへの代入であり、read `B+C` を保つ。`μ=1` では `(B,C)↦(B+C,0)` となり、非零環上で `(0,0)` と `(1,−1)` を同一視するので非単射である。

固定した引数のcompactとその有限語はtranslationであり、加えるベクトルの和を引けば逆がある。固定引数のapplyも含めた有限語でも同じである。従って上の非単射な `compact_all` を、その固定引数語と同一視できない。

## 定理 P3 — Snapshotの合法family `V(μδ)`

phaseをIdleとBusyとし、状態・遷移を次で宣言する。

| phase / operation | 原始式 |
| --- | --- |
| Idle | `(B,C)∈R²` |
| Busy | `(B,C,h)∈R³`、Law `g=μ(h−C)=0` |
| begin : Idle→Busy | `(B,C)↦(B,C,C)` |
| apply_u : Busy→Busy | `(B,C,h)↦(B+(1−δ)u,C+δu,h)` |
| apply_u : Idle→Idle | `(B,C)↦(B+(1−δ)u,C+δu)` |
| finish : Busy→Idle | `(B,C,h)↦(B+μh,(1−μ)C)` |
| read | 両phaseで `B+C` |

各phaseのapplyは、宣言された全合法状態と全引数 `u` に対して定義する。begin、finishはそのsource phaseの全合法状態に定義する。語はphaseに合う有限pathとし、begin/finishを空語、applyを同じapplyへ翻訳する。

P0.1による原始評価で

```math
\operatorname{begin}^*g=0,\qquad
\operatorname{apply}_u^*g=g-\mu\delta u,\qquad
\operatorname{read}(\operatorname{finish}(B,C,h))-(B+C)=g
```

を得る。従って `μδ=0` なら全遷移は合法状態に閉じ、begin/finishはreadを保ち、applyはreadを `u` 増やす。A2の型付きpath帰納法から全許可有限経路の観測保存が従う。

逆に宣言どおりの全applyが合法Busy状態に閉じるなら、Idle `(0,0)` にbeginを適用し、続いて `apply_1` を評価した

```math
(B,C,h)=(1-\delta,\delta,0)
```

がBusy Lawを満たす必要がある。その `g` は `−μδ` なので `μδ=0`。同じ原始列 `begin;apply_1;finish` の最後のreadは `1−μδ`、旧側のreadは `1` であり、残差は `−μδ` である。

ここで `μδ≠0` なら中間状態で既にLawが破れ、この列は合法なprotocolの経路ではない。必要性は「指定されたapplyが全合法状態に定義される」という構成義務から得る。失敗する入力を後からdomainから除いて全経路保存を空虚に成立させることはしない。

従って**指定されたdomainを持つprotocolの成立と全許可経路の保存**は `μδ=0` と同値である。全係数環上でこの式から意味保存familyの像はscheme

```math
V(\mu\delta)=\operatorname{Spec}k[\delta,\mu]/(\mu\delta)
```

となる。零因子・nilpotentを持つ環も含むため、fieldの点だけを使って二つの軸へ場合分けする証明ではない。

### P3.1 — Ambient状態との差

Busy Lawを置かず全 `R³` 上で同じfinishのread保存を要求すると、残差 `μ(h−C)` は全点で零でなければならない。`(B,C,h)=(0,0,1)` から `μ=0` を得、逆も明らかである。

対照的に `R=Q,λ=μ=1` では `δ=0` であり、合法Busyは `h=C`。applyは `C,h` を変えず、finishは `(B+h,0)` でreadを保つ。従ってこの同じ係数で全合法経路は保存される。ambient上の条件と、状態Lawを法としたB4の条件は異なる。

## 定理 P4 — Snapshot量を差し引く修正

finishを

```math
\operatorname{finish}_{snap}(B,C,h)=(B+\mu h,C-\mu h)
```

へ変え、Busyの旧状態Lawを除いて全 `R³` を合法状態とする。beginとapplyは同じ式のままである。read差は恒等的に零で、beginとapplyも全状態に閉じる。従って全係数 `δ,μ` について、同じ `p=B+C` と翻訳が全許可有限経路を保つ。

旧合法family `μδ=0` 上では、Busyの包含 `V(g)↪R³`、Idleの恒等が二protocolの比較となる。beginは同じ、applyは旧Lawの保存により可換である。二つのfinishのC成分の差は `μ(h−C)=g` なので、旧合法状態上で一致する。この包含は全遷移と観測を保つ。

一方、旧Busy Lawを固定したままfinishだけを変えた場合、`δ=μ=1`、`R=Q` で `begin;apply_1` は `(0,0)↦(0,0,0)↦(0,1,0)` となり `g=−1`。よって閉じない。固定した意味Lawと、編集を許す表示の状態LawはE1の規則で明示する必要がある。

applyなしの `begin;finish` は `h=C` を代入して `compact_all` に等しい。`begin;finish_snap` も同じ代入で `compact_all` となる。snapshotの取り方と、その後のapplyを含む操作言語まで比較して初めて二protocolを区別できる。

## 定理 P5 — 原式から得るfamily `V(μδ(1−ρ))`

自由係数 `ρ` を加え、finishを

```math
\operatorname{finish}_\rho(B,C,h)
=\bigl(B+\mu h,\ C-\mu((1-\rho)C+\rho h)\bigr)
```

と宣言する。原始式のread差は

```math
g_\rho=\mu(1-\rho)(h-C).
```

Busy Lawを `g_ρ=0` とし、beginとapplyはP3と同じにする。直接代入で

```math
\operatorname{begin}^*g_\rho=0,\qquad
\operatorname{apply}_u^*g_\rho=g_\rho-\mu\delta(1-\rho)u
```

である。P3と同じ全domainの閉性・観測保存・語帰納法により、合法係数familyは

```math
X=V(\mu\delta(1-\rho))
=\operatorname{Spec}k[\delta,\mu,\rho]/(\mu\delta(1-\rho)).
```

必要性は零Idleから `begin;apply_1` のBusy Lawを評価することで得る。その後のraw finishのread残差も `−μδ(1−ρ)` である。`ρ=0` は旧snapshot、`ρ=1` は `g_ρ=0` が恒等式となる修正版である。

### P5.1 — 四つのflag順序

非零環で係数 `(δ,μ,ρ)` を `(0,0,0)` から `(1,1,1)` へ動かし、各成分を一度だけ0から1へ変える。Boolean係数の八点のうち `μδ(1−ρ)` が非零になるのは `(1,1,0)` だけで、その値は1である。六つの順序を列挙すると次のとおり。

| 順序 | 一回目の後 | 二回目の後 | 全ての点が `X` 上 |
| --- | --- | --- | --- |
| `ρδμ` | `(0,0,1)` | `(1,0,1)` | はい |
| `ρμδ` | `(0,0,1)` | `(0,1,1)` | はい |
| `δρμ` | `(1,0,0)` | `(1,0,1)` | はい |
| `μρδ` | `(0,1,0)` | `(0,1,1)` | はい |
| `δμρ` | `(1,0,0)` | `(1,1,0)` | いいえ |
| `μδρ` | `(0,1,0)` | `(1,1,0)` | いいえ |

従って指定された四順序だけが条件を満たす。零環では `0=1` となってこの区別がなくなるため、非零という仮定をこの箇所で使う。

### P5.2 — 係数を状態に含む一つのphase protocol

係数も状態成分に含め、`f=μδ(1−ρ)` と書く。

```math
\mathrm{Idle}=V(f)\subseteq\mathbb A^5_{(\delta,\mu,\rho,B,C)},\qquad
\mathrm{Busy}=V(f,g_\rho)\subseteq\mathbb A^6_{(\delta,\mu,\rho,B,C,h)}.
```

begin・apply・finishは現在の係数を読み、係数を固定して上の原始式で作用する。係数切替はIdle上のpartial operationとして宣言する。各flag操作は対象成分を0から1へ変え、他の係数と `B,C` を保持する。domainは現在の対象成分が0で、切替後も `f=0` となるIdle状態である。これは原始座標とLawのpullbackで生成したdomainである。Busyで係数切替を行う操作は宣言しない。

beginの `g_ρ` は零、applyの `g_ρ` の変化は `−fu` だから、両遷移は指定状態に閉じる。finishのread差は `g_ρ`、flag切替は `B,C` を保つ。比較は両phaseで `p=B+C`、翻訳はapplyを同じ旧apply、begin・finish・flagを空語へ送る。各生成辺の状態Lawと観測保存からA2によりこの一つのprotocolの全許可有限経路が保存される。

任意のIdle `(B,C)` を固定し、P5.1の四順序の係数点を通るflag操作を順に使えば、四つの実際のprotocol経路が得られる。残る二順序は二回目の切替のdomain条件に失敗する。

### P5.3 — Busy状態の移送は係数条件だけでは決まらない

`R=Q` とし、係数 `(δ,μ,ρ)=(1,0,0)`、Idle `(B,C)=(0,0)` から開始する。`begin;apply_1` により

```math
(B,C,h)=(0,1,0),\qquad p=1
```

を得る。係数を状態値を保持したまま `(0,0,0)`、さらに `(0,1,0)` へ変えると、三つの係数点は全て `X` に属する。しかし最後のBusy残差は `g_ρ=1·1·(0−1)=−1` である。そこへraw finishを適用すると `(B,C)=(0,0)`、readは0になる。

この切替はP5.2の許可遷移ではない。係数fiberだけを検査すれば見落とすが、G1の合法状態liftでは最後のBusy Lawにより除かれる。Fの変更経路を比較するときにも、どのmodelを頂点とし、どの実射・翻訳を辺とするかを保持する必要がある。

P5.2の四経路は、拡大した一つのphase protocol内の**実行経路**である。各係数で別個に取った固定protocolの間の全構造保存射を、状態の恒等mapだけで得たことにはならない。例えば `δ` を変えると固定protocolのapply式が変わるため、同じ引数翻訳の恒等状態mapは一般にapplyと可換でない。Fでその固定protocol間の変更経路を要求するなら、各辺の比較射・翻訳を別に生成し、その全保存式を課す。Idleの公開状態だけを読む構造ではflagの恒等状態mapを使えるが、そのreadingを指定して比較する。

## P6 — Eの評価fiberへの同定

before、比較 `p=B+C`、P3の語翻訳、旧snapshotの状態Lawを固定し、操作係数 `δ,μ` だけを変える規則を取る。P3の必要十分性から全候補は `V(μδ)` である。評価を `v=(δ,μ)` とし、その部分関手としてunit条件を取ると

```math
V(\mu\delta)\cap D(\mu)\cong\{\delta=0,\ \mu\in\mathbb G_m\},
\qquad
V(\mu\delta)\cap D(\delta)\cong\{\mu=0,\ \delta\in\mathbb G_m\}.
```

両方をunitにする `D(μδ)` との交わりは空schemeである。環の式としてはunitの積が零なら `1=0` となることで分かる。空schemeの零環上の一意な点を除き、非零環上に解はない。

表示のBusy Lawの変更と `finish_ρ` を許す規則では、全候補が `X=V(μδ(1−ρ))` となる。`D(μδ)` 上では `ρ=1` が必要十分だから解は `G_m²`。この解から修正版finishと全状態のBusyを回復する。

これに対して旧Busy Lawを固定と宣言した規則では、どのfinishを選んでもapplyの閉性に `μδ=0` が必要であり、`D(μδ)` 上の非零環解はない。意味Law（公開read・指定語保存）を保持しつつ表示Lawの編集を許した場合と、表示Lawも固定した場合を同じfiber構成で区別できる。

同時変形のliftは同じ候補familyの環射に沿うfiberであり、合成可能な二つの実際の比較射のfiber productとは異なる。四角形の併用を要求する場合にも、二つのbranchと追加の実射をF1に保持する。`μδ=0` 等の係数条件だけからその四角形の全射を補うことはしない。高次liftの存在・失敗は同じfamilyを入力とするG-141の問題となる。

## P7 — 型署名だけのreading

E3の `U` を同じ台帳sort・操作署名に原始式をdataとして保持するraw表示候補とし、`q_type` は型と署名だけを読む。旧finishと `finish_snap` は同じ型の演算なのでこのreadingの像は等しい。Lawの適合性と実際の残差は後段の `E_ok` で検査する。

`R=Q,δ=μ=1`、零Idleから同じ構文 `begin;apply_1;finish` をraw評価すると、旧式は `read=0`、修正式は `read=1`。旧側の一回のapply後のreadは1なので、残差はそれぞれ `−1` と `0` となる。旧式では途中のBusy Lawも破れるが、修正版ではBusy全体が合法なのでこの経路は実行できる。

したがってここで比べるのは、同じ型署名を持つraw候補のLaw適合性と原始式評価である。旧候補について、存在しない合法実行の観測を測ったことにはしない。等しい `q_type` の二候補で後段の評価が異なるので、型署名だけからこの評価へ因子分解する関数は存在しない。
