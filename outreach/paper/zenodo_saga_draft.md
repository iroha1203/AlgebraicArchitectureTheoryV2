# SAGA: A Comparison Theorem for Local-to-Global Software Architecture

*From Semantic Repair Cohomology to Algebraic-Geometric Descent*

**Hiroyuki Nakahata** — Independent Researcher
ORCID: [0009-0008-5928-0234](https://orcid.org/0009-0008-5928-0234) ·
contact: nakahata.theorem@gmail.com

著者はファインディ株式会社(Findy Inc.)に所属する。本研究は個人研究として
行われたものであり、同社の見解を代表しない。

> **draft note**: 本ファイルは Zenodo プレプリントの初稿下書きである。要件と完了条件は
> [zenodo_saga.md](zenodo_saga.md)、Related Work の原典調査は
> [zenodo_saga_related_work.md](zenodo_saga_related_work.md) を正とする。
> 本文中の `TODO:` は release identity 確定時に固定する箇所を示す。

---

## 要旨

software architecture の局所的な整合性と大域的な整合性の間には、構造的な隔たりがある。
本論文は、この隔たりを測る二つのコホモロジーを独立に構成し、両者の一致を証明する。

第一の構成は、supported semantic atom と局所 repair relation から
semantic repair coefficient `M_sem` と semantic Čech complex を生成する。
第二の構成は、Atom-indexed architectural equation system `E` から
equation-generated coefficient `Q_E` と幾何側 Čech complex を生成する。
Algebraic Architecture Theory (AAT) の monomorphic cover `𝒰` 上で、二つの affine local-state system、
selected local atlases、empty-overlap normalization、
repair-relation completeness、equation-generator completeness、
restriction-natural かつ generator-equivariant な対応 `β` の下で、
comparison map は同型

```math
H^1_{\mathrm{sem}}(\mathcal U)
\cong
\check H^1(\mathcal U,Q_E)
```

と residual class の対応 `κ_*([r_sem])=[r_E]` を誘導する。これを SAGA 比較定理と呼ぶ。
true semantic repair sheaf 条件の下では、global repair は三項同値

```math
\mathrm{Nonempty}\,P_{\mathrm{sem}}(W)
\iff
[r_{\mathrm{sem}}]=0
\iff
[r_E]=0
```

で特徴づけられる。

本論文は、この数学的成果を三層で提示する。第一層は完成した SAGA 数学である。
第二層は release 時点の Lean 形式化 status であり、定義、定理、有限 witness、
proof chain を declaration 単位で本論文の定理と対応させる。第三層は measurement system
ArchSig による実行可能な有限診断であり、実在するオープンソース microservice architecture 上で
観測から導出した residual の非零計測、gate による blocking、repair 案の事前検証、
repair 後の障害消滅の記録までを再現可能な一つの計算として示す。
数学、Lean、measurement は同じ release identity を参照し、各 claim から一次証拠へ
到達できる provenance を構成する。

---

## 1. Introduction

### 1.1 Local-to-global architecture problem

software architecture の各構成要素は、それぞれの局所的な文脈で整合的に設計される。
一つの service は自身のデータ規約を守り、モジュール間の個々の受け渡しは
それぞれの契約を満たす。それにもかかわらず、システム全体では意味の不整合が生じる。
この現象の核心は、局所的な正しさの総和が大域的な正しさを構成しないことにある。

この構造は数学の古典的な問題型と同じ形をしている。局所データの族が与えられ、
各局所は整合的で、隣接する局所同士も整合的であるとき、全体を貼り合わせる
大域データは存在するか。層の理論はこの問いを sheaf condition として定式化し、
コホモロジーは貼り合わせの障害を `H^1` の類として測る。

本論文は、software architecture のこの問題に対して比較定理を証明する。
すなわち、意味論的な修理の障害と、architecture の連立方程式系から生成される
幾何の障害が、同じコホモロジー類として一致することを示す。

### 1.2 SAGA の研究課題

architecture の意味不整合を「修理」の言葉で語る立場と、「方程式と幾何」の言葉で
語る立場は、それぞれ独立に定式化できる。

- **semantic repair の立場**: 各局所文脈での意味的修理の選択肢と、修理同士の
  同値関係から、修理の障害を測る係数と複体を作る。
- **equation geometry の立場**: architecture の制約を Atom-indexed な連立方程式系
  として組織し、その obstruction ideal による商から係数と複体を作る。

SAGA (Sémantique Architecturale, Géométrie Algébrique) の研究課題は、
この二つの構成を独立に立てた上で、両者の `H^1` と residual class を結ぶ
比較定理を証明することである。比較が成立すれば、意味論的な診断は幾何的な計算へ、
幾何的な計算は意味論的な読みへ、双方向に翻訳できる。

本論文で扱う cohomology は、一貫して、選ばれた monomorphic AAT cover `𝒰` に
相対的な additive Čech `H^1(𝒰,-)` である。cover の選択に依存しない sheaf
cohomology との同一視は本論文の主張に含まれない(§5.7)。

名称について付記する。本論文の SAGA は、分散トランザクションの補償系列として
知られる Saga パターン [Garcia-Molina–Salem 1987] とは無関係である。この名は、
二つの幾何の対応を確立した Serre の GAGA 比較定理 [Serre 1956] への
オマージュである(§9.2)。

### 1.3 成果の三層

本論文は、次の三層を一つの研究成果として提示する。

| 層 | 役割 |
| --- | --- |
| 数学 | プレプリントの主成果。SAGA 比較定理と residual class 対応の完成した証明 |
| Lean | 数学成果に対する release 時点の機械形式化 status |
| ArchSig | 固定した実コード事例に対する有限かつ実行可能な realization |

数学面は完成版である。semantic repair cohomology と equation-generated AAT Čech
cohomology の比較を構成し、`H^1` 同型、residual class 対応、true sheaf 条件下の
global repair 同値を証明する(第5章)。

Lean 面は release 時点の status である。形式化済みの定義、定理、witness、
proof chain を declaration 単位で示し、本論文の定理との対応と axiom 状況を固定する(第6章)。

ArchSig 面は有限 case study である。固定した microservice architecture を対象に、
数学的対象が有限 architecture evidence からどのように計算され、repair 前後で
どのように変化するかを再現可能な形で示す(第7章)。

本論文で **release identity** とは、Lean source の release tag、ArchSig の
version、入力 artifact の digest の組をいう。第6章の形式化 status と第7章の
再現手順は、この固定した同定子に対して記述される。

### 1.4 論文全体を貫く読み

```text
完成した SAGA 数学
  -> release 時点の Lean 形式化
  -> ArchSig による実コード事例の有限計算
  -> repair 前後の比較
```

本論文は、数学的比較定理が形式化と有限 measurement へ降り、実在 software
architecture の semantic repair を読めることを示す。第2章は AAT アプローチを、
第3章は SAGA に必要な数学的基礎を、第4章は二つの複体の独立な構成を、
第5章は比較定理を、第6章は Lean status を、第7章は ArchSig による実コード診断を、
第8章は関連研究を、第9章は研究展望を、第10章は結論を述べる。

---

## 2. The AAT Approach

Algebraic Architecture Theory (AAT) は、software architecture を代数幾何として
構成する数学理論である。本章はこのアプローチの構成法と、それが開く分析能力を
説明する。SAGA の statement と proof に必要な数学的対象の定義は第3章が担当する。

### 2.1 Atom による公理化

AAT は、primitive architectural fact を **Atom** として公理化する。Atom は
特定のプログラミング言語、framework、serialization 形式に属さない。
複数の言語、service、storage representation にまたがる architectural fact を、
同じ architecture object の上で扱える。この言語独立性が、後の章で意味を持つ。
実装型が一致していても意味規約が異なる、という不整合を語るには、
型システムより上の抽象度で architecture を構成する必要があるからである。

### 2.2 連立方程式としての architecture condition

複数の architecture condition は、**Atom-indexed architectural equation system**
として組織される。equation system からは residual、obstruction ideal、
そして required equations が同時に成立する零点 locus が構成される。
architecture の制約が満たされる場所は、方程式系の零点集合の類似物として
幾何的対象になる。設計原則の自然言語表現は equation index の読みとして
`E` から導かれる表示であり、数学上の一次対象は `E` である。

### 2.3 AAT site と local-to-global problem

局所 context、cover、restriction、overlap は **AAT site** として組織される。
これにより、local-to-global problem は sheaf と cohomology の言葉で扱える。
局所的に成立する条件の族が大域的に貼り合うかは global section の存在問題となり、
貼り合わせの障害は Čech cohomology の類として測られる。

### 2.4 failure の構造化

AAT では、architecture の failure は residual、ideal、cohomology class、
さらに Tor conflict や singularity として構造化される。本論文が使うのは
前三者である。diagnosis と repair は、
同じ幾何対象の変化として読める。修理とは類を消す操作であり、
修理の成否は類の零性として判定される。

### 2.5 ringed geometry と道具の接続

architecture 上に ringed geometry を構成することで、scheme、derived intersection、
deformation、monodromy、stack、base change といった代数幾何の道具が
architecture 上で働く。本論文の SAGA はこの一部、すなわち Čech `H^1` と
descent を使う。より深い道具の使用は第9章の研究展望で述べる。

SAGA の代数幾何性は構成の側にある: observable ring `O_E`、witness ideal と
obstruction ideal、商係数 `Q_E=O_E/I_Ob`、AAT site、そして零類を global repair
として読む descent interpretation である(第3〜5章。固有性の帰属は §5.1)。

### 2.6 相対性と provenance

AAT の幾何は、vocabulary、equation system、coverage、coefficient を固定した
**相対的な幾何**である。すべての claim は、選ばれた入力データに相対的であり、
その入力から結論までの provenance を追跡できる。この相対性は制約であると同時に、
claim と証拠を対応させる規律の源である。第7章の measurement は
この規律の実行形である。

### 2.7 SAGA によるアプローチの具体化

SAGA は、semantic repair obstruction と equation-generated Čech obstruction を
比較することで、AAT アプローチの local-to-global 能力を具体化する。
本章の中心メッセージを次に固定する。

> AAT constructs software architecture as a relative algebraic geometry generated
> from primitive architectural facts and simultaneous architectural equations,
> so that local consistency, global obstruction, and repair become geometric objects.

---

## 3. AAT Foundations for SAGA

本章は、SAGA の statement と proof を読むために必要な数学的対象を、論文内で
完結する形で定義する。以下の章の議論は、本章の定義だけを前提とする。

### 3.1 Atom と Atom family

**定義 3.1(Atom)。** Atom とは、次の形の型付き事実である。

```text
a = (kind, axis, subject, predicate, payload)
```

`kind` は Atom の種別(component、relation、state、contract、semantic など)、
`axis` はその Atom が読まれる signature / equation 軸、`subject` は statement の
主体、`predicate` は `subject` に対して立てる一つの atomic statement、
`payload` は statement の内容データである。Atom は特定の言語や framework に
属さない primitive architectural fact であり、AAT の内部では生成元として
扱われる。core family の schema には `component(c)`、`relation_r(c,d)`、
`state(c,x)`、`contract(m,p)`、`semantic(t,s)`、`runtime_interaction(u,v,h)`
などがある。たとえば `semantic(t,s)` は、表現 `t` を subject に、「`t` は意味
規約 `s` に従う」を predicate に、`s` の記述を payload に取る semantic Atom で
ある。

**定義 3.2(Atom family と support)。** Atom universe を `At` と書く。
Atom family `F` は `At` の部分集合であり、`support(F)` は `F` に現れる
subject の集合である。`F` は component、relation、state、contract、effect、
semantic Atom を混在して含みうる。この混在は排除されず、混在した
primitive fact がどの equation を満たしどの obstruction を生むかが問いになる。

### 3.2 Architecture object

**定義 3.3(architecture object)。** Atom configuration `C=(F, Rel, Pl)`
(Atom family `F`、関係づけ `Rel`、配置 `Pl`)に structure maps `S`(graph、category、
algebra、state transition などへの構造写像)と selected quantities `Q`
(invariant、measure、signature axis)を与えた組

```text
A = (C, S, Q)
```

を architecture object と呼ぶ。Atom family `F` から `A` が得られることを
`F ⇒ A` と書く。すべての architecture object は Atom family から生成される
(Atom-origin 原理)。本論文では固定した architecture object を `X` と書く。

### 3.3 Architecture context と context category

**定義 3.4(architecture context)。** architecture object に対する
architecture context `W` は、その局所的な読みである。最小モデルでは

```text
W = (Supp(W), Ax(W), Obs(W))
```

と読む。`Supp(W)` は `W` で読まれる Atom support、`Ax(W)` は選ばれる
signature / equation axis、`Obs(W)` は `W` で読める coordinate、witness、
semantic data の族である。component-local view、feature view、
semantic contract slice、runtime trace slice などが代表的な context である。

**定義 3.5(context category)。** context を対象とし、context 間の読み替え
`i:W'→W`(restriction、projection、refinement、embedding、base change)を
射とする圏を `ArchCtx(X)` と書く。射は局所 context から大域 context へ向かう。
cover の overlap は pullback

```math
U_i\times_W U_j
```

として構成される(context overlap)。

**最小 poset model。** support、axis、observable family が finite meet を持ち、
任意の二つの context の間に読み替え射が高々一つある equivalence
quotient の下で、`ArchCtx_min(X)` は finite-meet poset category になり、
overlap は meet として計算される。この model の
射はすべて monomorphism である(第3.7節がこの事実を cover 仮定へ接続する)。
第7章の有限計算はこの regime の実行形であり、一般の `ArchCtx(X)` 上での定理の
適用範囲と形式化の身分は §5.7 でまとめて述べる。

### 3.4 Atom-indexed architectural equation system

**定義 3.6(equation system)。** Atom universe `At`、architecture object の族、
局所 context の小圏を固定する。Atom-indexed architectural equation system `E` は
次のデータからなる。

```text
K_E:
  equation index の型。

role_E : K_E -> { required, optional, derived }:
  各 equation の役割。

O_E : ArchCtx(X)^op -> CommRing:
  context W に observable ring O_E(W) を割り当てる presheaf。

nu_{W,i,a} in O_E(W):
  i in K_E、a in At に対する symbolic violation coordinate。

epsilon_{W,A,i,a} in O_E(W):
  architecture object A 上で equation i を評価する
  object-dependent equation residual。
```

二つの coordinate family は restriction と可換する。`nu` は witness ideal を
生成する symbolic coordinate であり、`epsilon` は equation fulfillment を判定する
residual coordinate である。equation index `i` が `A` 上で成立するとは、
すべての context と Atom で `epsilon_{W,A,i,a}=0` となることをいう。
required equations の同時成立が、architecture の整合性の基礎条件である。

設計原則や規約の自然言語表現は、equation index とその coordinate family の
読みとして `E` から導かれ、独立した真偽述語を持たない。
数学上の一次対象は `E` である。

### 3.5 AAT site、presheaf、sheaf condition

**定義 3.7(AAT site)。** architecture object `X`、equation system `E`、
signature `Sig`(選ばれた signature axes の族。本論文では固定 package の一部として
扱い、以後展開しない)、coverage requirements `R`、context-overlap package `Ov` を
固定する。coverage family `{W_i→W}` が `(E,R,Ov)`-admissible であるとは、
`W` 上で読まれるべきと `R` が要求するデータ — 対象 Atom の support、`E` の
coordinate(`ν`、`ε`)の support、選ばれた witness と signature axis、context 間の
interaction overlap — のすべてが、`{W_i}` への restriction を通じて cover 全体で
読めることをいう。admissible family が生成する Grothendieck topology を
`J_{E,R,Ov}` と書く。AAT site は package

```text
Site_AAT(X,E,Sig,R,Ov) = (ArchCtx(X), E, Sig, R, Ov, J_{E,R,Ov})
```

である。本論文では、この package を固定した underlying site を `S_X` と略記し、
`W` をその context とする。cover は Atom を生成しない(non-generation)。
この topology から本論文の証明が消費するのは、`𝒰` が topology に属することと
sheaf condition(定理 5.2)だけであり、admissibility の内部構造はどの証明でも
使われない。有限実行の regime は第3.3節の finite-meet poset model である。

**定義 3.8(presheaf と sheaf condition)。** `S_X` 上の presheaf は
`F:ArchCtx(X)^op→Set` である。`F` が sheaf であるとは、任意の cover
`{W_i→W}` について、overlap 上で一致する compatible local sections が
一意の global section へ貼り合うことをいう。第5章の true semantic repair sheaf
条件はこの sheaf condition の instance である。

### 3.6 Witness ideal、obstruction ideal、equation-generated coefficient

**定義 3.9(witness ideal と obstruction ideal)。** equation index `i` の
local witness ideal を symbolic violation coordinates が生成する ideal

```math
I_i^E(W)=\langle \nu_{W,i,a}\mid a\in At\rangle\subset O_E(W)
```

で定義する。required equations の witness ideal の和

```math
I_{\mathrm{Ob}}^E(W)=\sum_{i\in K_E,\ \mathrm{role}_E(i)=\mathrm{required}} I_i^E(W)
```

を local obstruction ideal と呼ぶ。`nu` の restriction compatibility から
`res_j(I_Ob^E(W))⊂I_Ob^E(W')` が従い、context-wise ideals は ideal
subpresheaf をなす。

**定理 3.10(generated obstruction quotient)。**
equation system `E` と displayed equation source(有限個の local context
`W_q→W_base` に対する architecture object、required equation index `i_q`、
support Atom `a_q` の選択。cover-indexed の場合は local context を各 chart に
取る)を固定する。このとき次が成立する。

1. **generated coefficient**: 商

   ```math
   Q_E(W)=O_E(W)/I_{\mathrm{Ob}}^E(W)
   ```

   には商の普遍性により restriction が誘導され、`W↦Q_E(W)` は可換群値
   presheaf になる。
2. **generated interpretation**: displayed source `q` の interpretation は
   residual の商 class `interpret(q)=[d_q]∈Q_E(W_q)`、
   `d_q:=ε_{W_q,A_q,i_q,a_q}` として構成される。interpretation は自由な
   データではなく、構成される。
3. **residual restriction naturality**: context morphism `g:Z→W_q` に対し
   `d_{q|Z}:=ε_{Z,A_q,i_q,a_q}` と置くと、

   ```math
   \mathrm{res}_g([d_q])=[\mathrm{res}_g(d_q)]=[d_{q|Z}]
   ```

   が成り立つ。residual class の restriction は、同じ architecture reading、
   equation index、support Atom で評価した residual の class である。
4. **vanishing**: displayed equations が充足されるならば、すべての `q` で
   `[d_q]=0`。
5. **quotient zero criterion**: `[d_q]=0 ⟺ d_q∈I_Ob^E(W_q)`。
   したがって `d_q∉I_Ob^E(W_q)` ならば `[d_q]≠0`。

証明は商と ideal の一般論による。(1) は定義 3.9 の ideal subpresheaf 性と商の
普遍性、(2) は構成、(3) は `ε` の restriction 可換性(定義 3.6)と商の
代表元計算、(4) は equation fulfillment の定義(`ε=0`)、(5) は商に
おける零の定義そのものである。

条項 5 が与えるのは quotient における零判定である。displayed failure から
非零類 `[d_q]≠0` へ至るには、意味論上の failure が ideal に属さない residual
として顕在化すること(**semantic faithfulness**)が別に要る。これは商係数の
性質ではなく displayed source の選択と supply に属する条件である。実測の上での
担い手は第7章で述べる(§7.1)。

この `Q_E` が SAGA の幾何側 Čech complex の係数である。obstruction が
ideal-theoretic であること、すなわち failure が label ではなく商の class として
測られることが、第4章以降のすべての構成の土台になる。

### 3.7 Monomorphic AAT cover

有限添字集合 `I` と AAT cover

```math
\mathcal U=\{u_i:U_i\to W\}_{i\in I}
```

を固定し、各 `u_i` は monomorphism であると仮定する。このような cover を
**monomorphic AAT cover** と呼ぶ。添字には全順序を選び、`i<j<k` に対して

```math
U_{ij}=U_i\times_W U_j,\qquad
U_{ijk}=U_i\times_W U_j\times_W U_k
```

と書く。chart `U_i` とこれらの pairwise / triple intersection を合わせて
**cover intersection diagram** と呼ぶ。非空な `U_{ijk}` の三つの pairwise
intersection は、`U_{ijk}` からの射影を受けるため非空である。空の pullback は
intersection の対象から除き、その値は
empty-overlap normalization(第5章 定理 5.1 の条件 8)で固定する。
比較 core 自体に有限性は不要だが、有限 cover は中心定理、finite witness、
実行可能な realization を同じ記号で扱うために固定する。第3.3節の
finite-meet poset model ではすべての射が monomorphism なので、この仮定は
自動的に満たされる。一般の `ArchCtx(X)` では定理の明示仮定である。

### 3.8 Selected、generated、proved の区別

SAGA では、入力、構成、帰結を厳密に区別する。

| 種類 | 内容 |
| --- | --- |
| selected | 比較の舞台(monomorphic AAT cover、empty-overlap normalization)、semantic 側の一次データ(semantic atom system、local repair relation、local repair atlas)、equation 側の一次データ(equation system `E`、local equation-lift atlas)、両者の対応(Atom/equation interpretation、local-state interpretation `β`)、completeness 二条件、global gluing に用いる true sheaf 条件。定理 5.1 の入力 1–8 として固定される |
| generated | `M_sem`、`Q_E`、二つの Čech complex、`r_sem`、`r_E`、係数写像 `Φ`、cochain map `κ` |
| proved | repair-relation soundness、SAGA presentation exactness、`Φ` の同型性、微分可換性、cocycle / coboundary 保存、`H^1` 同型、residual class 対応、零類と actual global repair の同値 |

この区別は、数学的な相対性を保ちながら結論の provenance を固定する。
selected は入力契約であり、proved はその契約の下での定理である。

---

## 4. Semantic Repair and Equation-Generated Geometry

本章は、SAGA の二つの複体を独立に構成する。semantic 側は semantic atom と
repair relation から、equation 側は equation system から、それぞれの一次データのみで
係数、複体、residual を生成する。両者の比較は第5章の定理の結論であり、
二つの複体の構成には他方への参照が入らない。両者を接続する唯一の写像
`χ^E`(命題 4.1)は第5章の比較入力の構成であり、どちらの複体の構成にも
使われない。

### 4.1 Cover-relative Čech complex

`F` を `S_X` 上の可換群値 presheaf とする。`𝒰` に相対的な三項 cochain complex を

```math
C^0(\mathcal U,F)=\prod_iF(U_i),\qquad
C^1(\mathcal U,F)=\prod_{i<j}F(U_{ij}),\qquad
C^2(\mathcal U,F)=\prod_{i<j<k}F(U_{ijk})
```

(積は nonempty intersection 上を走る)と、ordered index 上の differential

```math
(\delta^0a)_{ij}=a_j|_{U_{ij}}-a_i|_{U_{ij}},
\qquad
(\delta^1c)_{ijk}=c_{jk}|_{U_{ijk}}-c_{ik}|_{U_{ijk}}+c_{ij}|_{U_{ijk}}
```

で定義する。直接計算により `δ¹δ⁰=0` が成立するので、cover-relative `H^1` を

```math
\check H^1(\mathcal U,F)=\ker\delta^1/\operatorname{im}\delta^0
```

で定義する。

### 4.2 Semantic 側の構成

**Semantic repair presentation。** `S_X` の各 context `V` に、`V` 上で区別する
semantic atom の集合 `Λ(V)`、semantic atom の台 Atom を与える projection
`π_V:Λ(V)→At`、および repair に使用できる **supported semantic atom** の
部分集合 `S(V)⊆Λ(V)` を与える。各 context morphism `V'→V` に対して
functorial な restriction 写像 `Λ(V)→Λ(V')` があり、support を保ち
(`λ∈S(V)` なら `λ|_{V'}∈S(V')`)、projection は台 Atom を保つ:

```math
\pi_{V'}(\lambda|_{V'})=\pi_V(\lambda).
```

`S(V)` 上の free abelian group を `F_sem(V)` と書き、その元(supported atom の
形式的有限和)を **repair word** と呼ぶ。各 `V` で restriction-stable な部分群

```math
R_{\mathrm{rep}}(V)\subset F_{\mathrm{sem}}(V)
```

(**局所 repair relation**)を選ぶ。ここまでが semantic 側の一次データである。
comparison core(§5.3〜§5.5)では、これらを cover intersection diagram へ
制限して使う。

**Semantic coefficient。** 商

```math
M_{\mathrm{sem}}(V)=F_{\mathrm{sem}}(V)/R_{\mathrm{rep}}(V)
```

には restriction-stability により restriction が誘導され、`V↦M_sem(V)` は
`S_X` 上の可換群値 presheaf をなす。`M_sem` を係数とする §4.1 の複体
`C^•_sem(𝒰):=C^•(𝒰,M_sem)` が semantic 側の複体である。

**Affine semantic repair system。** `P_sem` を `S_X` 上の semantic local repair
state の presheaf とする。各 `V` で `F_sem(V)` が `P_sem(V)` に作用し、
restriction は作用と可換し、cover intersection diagram 上の各 `V` で
次の三条件を満たす。

```text
action soundness:
  R_rep(V) の語は恒等に作用する。

stabilizer completeness:
  P_sem(V) が非空なら、恒等に作用する語は R_rep(V) に属する。

local transitivity:
  任意の二状態は語の作用で移り合う。
```

soundness により作用は `M_sem(V)` の作用へ降り、completeness により
この作用は free、transitivity により非空の `P_sem(V)` 上で transitive である。
したがって、cover intersection diagram 上の各 `V` で、非空な `P_sem(V)` は
`M_sem(V)`-torsor(affine space)になる。

**Semantic residual。** selected local repair atlas `{p_i}` を選ぶと、
各 nonempty overlap 上の torsor の差として一意な

```math
r_{\mathrm{sem},ij}=p_j|_{U_{ij}}-p_i|_{U_{ij}}\in M_{\mathrm{sem}}(U_{ij})
```

が定まり、**semantic residual** `r_sem∈C¹_sem(𝒰)` を与える。`r_sem` は cocycle
である: `U_ijk` 上で `p_k=r_jk+p_j=r_jk+r_ij+p_i` かつ `p_k=r_ik+p_i` であり、
作用の freeness から `r_jk-r_ik+r_ij=0` を得る。

class `[r_sem]∈H^1_sem(𝒰)` は atlas の選び方に依存しない(**choice
independence**): 別の atlas `p'_i=a_i+p_i` に対し同じ torsor 計算が
`r'_sem=r_sem+δ⁰a` を与える。したがって零類 `[r_sem]=0` は、ある correction
`a∈C⁰_sem(𝒰)` について corrected atlas `(-a_i)+p_i` が全 pairwise overlap 上で
一致すること(**matching correction** の存在)と同値である。

### 4.3 Equation 側の構成

equation 側は、定理 3.10 の `Q_E` を係数とする **geometric Čech complex**
`C^•_E(𝒰):=C^•(𝒰,Q_E)` を構成する。**equation-lift system** `P_E` は
`S_X` 上の presheaf であり、各 intersection `V` で、非空な `P_E(V)` には
`Q_E(V)` が free かつ transitive に作用し、restriction は作用と可換する。
selected local lift atlas `{e_i}` から、overlap 上の差として
幾何側 residual

```math
r_{E,ij}=e_j|_{U_{ij}}-e_i|_{U_{ij}}
```

が生成される。§4.2 と同じ torsor 論法により、`r_E` は cocycle であり、
その class は atlas の選択に依存しない。

**命題 4.1(equation semantic realization: `χ^E` の構成)。**
各 cover intersection `V` の supported semantic atom `λ∈S(V)` に、
required equation index `i_λ` と local architecture reading `A_λ` を
restriction と可換に対応させる(selected。cover intersection diagram の
face restriction `V'→V` について `i_{λ|_{V'}}=i_λ`、`A_{λ|_{V'}}=A_λ`)。
このとき

```math
\chi^E_V(\lambda):=[\epsilon_{V,A_\lambda,i_\lambda,\pi_V(\lambda)}]\in Q_E(V)
```

は face restriction について restriction-natural、すなわち

```math
\chi^E_{V'}(\lambda|_{V'})=\chi^E_V(\lambda)|_{V'}
```

を満たす。

**証明。** `i_λ`、`A_λ` は restriction と可換に選ばれ、`π` は台 Atom を保つ
(§4.2)。したがって `λ|_{V'}` での residual は同じ reading・index・support Atom
で `V'` 上評価した `ε` であり、定理 3.10 の residual restriction naturality に
より、その class は `χ^E_V(λ)` の restriction に一致する。∎

`χ^E` は、第5章 定理 5.1 の仮定 3 が要求する restriction-natural な写像を
equation system と displayed reading から構成する canonical な実例であり、
「どの equation のどの読みに対する failure か」だけを材料に比較写像の始点が
生成されることを示す。

### 4.4 二つの構成の独立性

semantic 側の `M_sem`、`C_sem`、`r_sem` は semantic presentation のみから、
equation 側の `Q_E`、`C_E`、`r_E` は equation system のみから構成された。
二つの複体は同じ AAT cover 上に置かれるが、係数、local state、residual は
それぞれの一次データに由来する。したがって、次章の比較写像の存在、同型性、
微分可換性、residual class の対応は、構成の反復ではなく定理の結論である。

---

## 5. The SAGA Comparison Theorem

本章は SAGA の中心定理を述べ、証明する。routine な検証(restriction naturality の
成分ごとの確認など)は文中で圧縮するが、比較定理を成立させる主要論証はすべて
本章内で連続して追える。

### 5.1 中心定理

**定理 5.1(SAGA 中心定理)。**
monomorphic AAT cover `𝒰` 上で次を固定する。

1. supported semantic atom と restriction-stable な局所 repair relation から
   生成される可換群値 presheaf `M_sem`(§4.2)。
2. architectural equation system `E` から生成される可換群値 presheaf `Q_E`。
3. supported semantic atom を displayed Atom/equation residual class へ送る
   restriction-natural な写像。
4. その写像についての局所 repair relation の completeness と
   equation generator completeness(cover intersection ごとに確認する)。
5. repair words の作用から additive torsor structure を導く affine semantic
   repair system `P_sem` と、その selected local repair atlas。
6. `Q_E` が作用する equation-lift system `P_E` と、その selected local lift atlas。
7. semantic local states を equation local lifts へ送る restriction-natural かつ
   generator-equivariant な写像 `β:P_sem→P_E`
   (cover intersection ごとに確認する)。
8. 積から除いた各 empty cover intersection `V` に対する
   `M_sem(V)=Q_E(V)=0` と、`P_sem(V)`、`P_E(V)` の subsingleton 性
   (empty-overlap normalization)。

このとき次の三段が成立する。

**(i) SAGA Presentation Theorem。** 仮定 3 の写像の free 延長
`χ̃_V:F_sem(V)→Q_E(V)`(§5.3)は、各 nonempty cover intersection `V` で

```math
\ker \widetilde\chi_V=R_{\mathrm{rep}}(V),
\qquad
\operatorname{im}\widetilde\chi_V=Q_E(V)
```

を満たす。kernel の等式のうち包含 `R_rep(V)⊆ker χ̃_V`(repair-relation
soundness)は仮定ではなく、local-state data(仮定 5–7)から導出される(§5.3)。
逆包含 `ker χ̃_V⊆R_rep(V)` は repair-relation completeness、image の等式は
equation-generator completeness であり、いずれも仮定 4 である。この exactness
により、この写像は cover intersection diagram 上の自然同型

```math
\Phi:M_{\mathrm{sem}}\xrightarrow{\sim}Q_E
```

を誘導する。

**(ii) Čech comparison。** `Φ` は、`M_sem` と `Q_E` から別々に作った Čech
complex の間の degreewise cochain isomorphism

```math
\kappa^\bullet:
C^\bullet_{\mathrm{sem}}(\mathcal U)
\xrightarrow{\sim}
C^\bullet_E(\mathcal U)
```

を誘導し、`κ` は微分と可換する。したがって

```math
\kappa_*:
H^1_{\mathrm{sem}}(\mathcal U)
\xrightarrow{\sim}
\check H^1(\mathcal U,Q_E)
```

が誘導される。semantic local repair atlas から生成した `r_sem` と、
equation local-lift atlas から生成した `r_E` について

```math
\kappa_*([r_{\mathrm{sem}}])=[r_E]
```

である。selected local atlases を各 nonempty intersection へ restriction する
ことで、この構成が使う各 intersection 上の local-state system は非空である。
residual の対応は、二つの local atlas を `β` で整合させて選んだ場合には
cochain 水準で `κ¹(r_sem)=r_E` として成立する。独立に選んだ場合にも、
両 cochain の差は明示的な `δ⁰`-像であり、class の等式が成立する。

**(iii) Grounded Global Gluing。** さらに、仮定 5 の `P_sem` が
true semantic repair sheaf(定義は §5.6)ならば、

```math
\mathrm{Nonempty}\,P_{\mathrm{sem}}(W)
\iff
[r_{\mathrm{sem}}]=0
\iff
[r_E]=0.
```

**三段の性格。** (ii) のうち cochain 同型と `H^1` 同型の誘導は、係数 presheaf
の自然同型から従う Čech complex の一般的機構である。(ii) 後半の residual 対応は
固有の内容に属する。
本定理の固有の内容は (i)、(iii)、および residual の対応に集中する: semantic
repair presentation と equation-generated quotient presentation を独立に構成した
こと(第4章)、generator map `χ` の構成(命題 4.1)、local-state interpretation `β` から
relation soundness を導出すること(§5.3)、completeness / generation を
architecture data に相対化した条件として置いたこと、そして residual class の
意味論的対応(§5.5)である。

### 5.2 証明の構造

証明は四つの段で構成され、§5.3〜§5.6 がこの順に論証を与える。

```text
generator map χ
  → coefficient isomorphism Φ : M_sem ≃ Q_E      (§5.3)
  → cochain isomorphism κ, κδ = δκ               (§5.4)
  → H¹ isomorphism κ_*                            (§5.4)
  → residual correspondence κ_*([r_sem]) = [r_E]  (§5.5)
  → grounded global gluing                        (§5.6)
```

soundness が仮定ではなく帰結である点は本定理の構成上の要であり、
その導出は §5.3 の冒頭で行う。

comparison core(§5.3〜§5.5)は cover intersection 上の局所データだけを使い、
global sheaf condition は §5.6 の gluing まで現れない。定理 5.1 の各仮定が
どの証明で消費されるかは、Appendix A が一覧として固定する。

### 5.3 係数同型: soundness の生成と presentation comparison

仮定 3 の写像は、各 nonempty cover intersection `V` で supported semantic
atom を equation coefficient へ送る restriction-natural な対応

```math
\chi_V:S(V)\longrightarrow Q_E(V)
```

である(命題 4.1 の `χ^E` はこの入力の構成された実例である)。
`F_sem(V)` は `S(V)` 上の free abelian group なので(§4.2)、普遍性により
`χ_V` は一意な準同型 `χ̃_V:F_sem(V)→Q_E(V)` へ延長される。構成すべき `Φ` は
`χ̃` を repair relation で割った商上の写像であり、その well-definedness、単射性、
全射性は soundness、completeness、generation という三つの異なる条件が担う。
この三条件の成立を **SAGA presentation exactness** と呼ぶ。

**Soundness の生成。** `x∈R_rep(V)` と `p∈P_sem(V)` を取る(定理 5.1 の下で、
selected local atlas の restriction により `P_sem(V)` は非空である)。§4.2 の
action soundness から、semantic 側の
作用で `x+p=p` である。`β` の generator-level equivariance は free group の有限和と
additive inverse へ延長されるので、

```math
\beta(p)=\beta(x+p)=\widetilde\chi(x)+\beta(p)
```

である。`Q_E(V)` の `P_E(V)` への作用は free なので `χ̃(x)=0`。したがって

```math
R_{\mathrm{rep}}(V)\subset\ker\widetilde\chi_V
```

である。soundness を仮定として置かず local-state data から
導出するのは、この3行の議論である。

仮定 7 の `β` の定義は `R_rep` に言及せず、要求されるのは restriction
naturality と generator-level equivariance だけなので、この導出は循環しない。
`β` を soundness と独立に構成できることは、§5.8 の有限例が具体写像で示す。

**商への降下。** `R_rep(V)⊂ker χ̃_V` により `χ̃_V` は商を通り、一意な準同型

```math
\Phi_V:
M_{\mathrm{sem}}(V)=F_{\mathrm{sem}}(V)/R_{\mathrm{rep}}(V)
\longrightarrow Q_E(V)
```

を誘導する。

**単射性。** `Φ_V([x])=0` とすると `x∈ker χ̃_V` であり、repair-relation
completeness(仮定 4)から `x∈R_rep(V)`、よって `[x]=0` である。

**全射性。** 任意の `q∈Q_E(V)` に対し、equation-generator completeness(仮定 4)
から `χ̃_V(x)=q` なる `x∈F_sem(V)` が存在し、`Φ_V([x])=q` である。

**自然性。** generator 上で

```math
\Phi_{V'}([\lambda|_{V'}])
  =\chi_{V'}(\lambda|_{V'})
  =\chi_V(\lambda)|_{V'}
  =\Phi_V([\lambda])|_{V'}
```

であり、二つ目の等号が `χ` の restriction naturality(仮定 3)である。generator が
`M_sem(V)` を生成するので、`Φ` は全要素で restriction と可換する。

以上で `Φ:M_sem≃Q_E` は cover intersection diagram 上の presheaf 自然同型である。
この同型は一方の complex を他方から transport した
ものではなく、semantic presentation と equation quotient の間の presentation
comparison である。三条件はそれぞれ写像の存在、単射性、全射性という異なる数学的
仕事を担い、どれを外しても同型は壊れる。一 generator の free group `F=ℤ` 上の
反例で確かめられる。

```text
soundness を外す:
  R = 2Z, Q = Z, chi(n) = n。
  relation 2 = 0 が Q で零にならず、写像が商へ降りない。

completeness を外す:
  R = 0, Q = Z/(2), chi(n) = [n]。
  写像は降りて全射だが、2 が kernel に残り単射でない。

generation を外す:
  R = 2Z, Q = Z/(4), chi(n) = [2n]。
  kernel は R と一致するが、image は {0,[2]} で全射でない。
```

### 5.4 Cochain 可換性と `H¹` 同型

**degreewise map の構成。** 各次数 `n=0,1,2` で

```math
\kappa^n:C^n_{\mathrm{sem}}(\mathcal U)\longrightarrow C^n_E(\mathcal U)
```

を、各 intersection 成分へ `Φ` を適用して定義する:

```math
(\kappa^0a)_i=\Phi_{U_i}(a_i),\qquad
(\kappa^1c)_{ij}=\Phi_{U_{ij}}(c_{ij}),\qquad
(\kappa^2z)_{ijk}=\Phi_{U_{ijk}}(z_{ijk}).
```

各 `Φ_V` が同型なので、`κ^n` は積上の同型である。

**微分との可換。** 示すべきは次の diagram の可換性である。

```math
\begin{array}{ccccc}
C^0_{\mathrm{sem}}(\mathcal U)
&\xrightarrow{\delta^0_{\mathrm{sem}}}&
C^1_{\mathrm{sem}}(\mathcal U)
&\xrightarrow{\delta^1_{\mathrm{sem}}}&
C^2_{\mathrm{sem}}(\mathcal U)\\
\downarrow\kappa^0&&\downarrow\kappa^1&&\downarrow\kappa^2\\
C^0_E(\mathcal U)
&\xrightarrow{\delta^0_E}&
C^1_E(\mathcal U)
&\xrightarrow{\delta^1_E}&
C^2_E(\mathcal U)
\end{array}
```

`a∈C⁰_sem(𝒰)` と `i<j` に対し

```math
\begin{aligned}
(\kappa^1\delta^0_{\mathrm{sem}}a)_{ij}
&=\Phi_{U_{ij}}(a_j|-a_i|)\\
&=\Phi_{U_j}(a_j)|-\Phi_{U_i}(a_i)|\\
&=(\delta_E^0\kappa^0a)_{ij}
\end{aligned}
```

であり、二行目は `Φ` の加法性と restriction naturality である。同じ計算を
`c∈C¹_sem(𝒰)` の `(i,j,k)` 成分(三項の交代和)に適用すると
`κ²δ¹_sem=δ¹_E κ¹` を得る。使うのは §5.3 で証明した `Φ` の
準同型性と自然性だけであり、ここで新しい仮定は入らない。

**`H¹` 同型。** `κ` は微分と可換な degreewise 同型なので、cocycle と coboundary を
保存し反映する。よって

```math
\kappa_*:
H^1_{\mathrm{sem}}(\mathcal U)
\longrightarrow
\check H^1(\mathcal U,Q_E),
\qquad
[c]\longmapsto[\kappa^1c]
```

は well-defined である: 代表元を `c+δ⁰_sem a` に替えても
`κ¹(c+δ⁰a)=κ¹c+δ⁰_E(κ⁰a)` で class は変わらない。逆写像は degreewise inverse
`(κ¹)^{-1}` が同じ形で誘導し、`κ_*` は可換群同型である。

### 5.5 Residual correspondence

semantic atlas `{p_i}` と equation atlas `{e_i}` を独立に選ぶ。各 chart で
`β(p_i)` と `e_i` は同じ `Q_E(U_i)`-torsor `P_E(U_i)` の元なので、一意な
`h_i∈Q_E(U_i)` が存在して `e_i=h_i+β(p_i)` を満たす。`U_ij` 上で `β` の
naturality と equivariance(仮定 7)を使うと

```math
\begin{aligned}
e_j
&=h_j+\beta(p_j)\\
&=h_j+\beta(r_{\mathrm{sem},ij}+p_i)\\
&=h_j+\Phi(r_{\mathrm{sem},ij})+\beta(p_i)\\
&=(\Phi(r_{\mathrm{sem},ij})+h_j-h_i)+e_i
\end{aligned}
```

である。equation torsor における差の一意性から

```math
r_{E,ij}=\Phi(r_{\mathrm{sem},ij})+h_j-h_i,
\qquad\text{すなわち}\qquad
r_E=\kappa^1(r_{\mathrm{sem}})+\delta_E^0h.
```

二つの atlas を `β` で整合させて選んだ場合、すなわち `e_i=β(p_i)` の場合は
`h=0` であり、cochain 水準の等式 `κ¹(r_sem)=r_E` が成立する。独立に選んだ場合も
両 cochain の差は明示的な coboundary `δ⁰_E h` なので、class の等式

```math
\kappa_*([r_{\mathrm{sem}}])=[r_E]
```

が成立する。`κ_*` は同型で零を保存し反映するので、
`[r_sem]=0⟺[r_E]=0` と `[r_sem]≠0⟺[r_E]≠0` も従う。

以上、§5.3〜§5.5 で定理 5.1 の (i) と (ii) が証明された。
残る (iii) の三項同値を次節で証明する。

### 5.6 Global repair: Grounded Global Gluing

**定義(true semantic repair sheaf)。** `S_X` 上の presheaf `P_sem` が次を
満たすとき **true semantic repair sheaf** と呼ぶ。(1) `P_sem` は選ばれた AAT
topology のすべての cover に対して sheaf condition を満たす。(2) `M_sem` の作用は
restriction と可換し、局所的に free かつ transitive である。(3) `𝒰` はその
topology に属する monomorphic AAT cover である。(4) 積から除いた empty
intersection 上で `P_sem` は subsingleton である。この四条件から `𝒰` に対する
sheaf condition が導かれ、per-cover の amalgamation map を別データとしては
置かない。

**補題 5.2A(ordered matching completion)。** cover の各射が monomorphism で
あり、積から除いた empty overlap 上で `P_sem` が subsingleton であるとする
(empty-overlap normalization)。family `(q_i)`、`q_i∈P_sem(U_i)` が、すべての
nonempty `i<j` overlap 上で一致するならば、`(q_i)` は全 ordered overlap 上の
matching family である。

**証明。** 残る overlap は三種である。self-overlap `U_ii` では、`u_i` が
monomorphism なので diagonal `U_i→U_i×_W U_i` は isomorphism であり、この
canonical isomorphism の下で二つの projection は同一射になる。したがって `q_i`
の二つの restriction は一致する。逆順 overlap `U_ji`(`i<j`)では、pullback
symmetry `U_j×_W U_i≅U_i×_W U_j` が canonical isomorphism であり、二つの
projection を入れ替える。restriction はこの canonical isomorphism に沿って
両立するので、`U_ji` 上の一致は `U_ij` 上の一致と同値である。積から除いた
empty overlap 上では `P_sem` が subsingleton なので一致は自動である。∎

**定理 5.2(Grounded Global Gluing)。** 定理 5.1 の設定に加え、`P_sem` が
true semantic repair sheaf ならば、三項同値

```math
\mathrm{Nonempty}\,P_{\mathrm{sem}}(W)
\iff
[r_{\mathrm{sem}}]=0
\iff
[r_E]=0
```

が成立する。さらに `[r_sem]=0` の証明から得る correction `a` に対して、
corrected family

```math
p_i^{\mathrm{corr}}=(-a_i)+p_i
```

を restriction として持つ global section が一意に存在する。

**証明(forward)。** `[r_sem]=0` とすると、零類は matching correction の存在と
同値なので(§4.2)、`r_sem=δ⁰_sem a` なる `a∈C⁰_sem(𝒰)` が取れる。
corrected family `p_i^corr=(-a_i)+p_i` の residual は choice independence
(§4.2)により `r_sem-δ⁰a=0` であり、corrected family は全 nonempty
`i<j` overlap 上で一致する。補題 5.2A により、corrected family は全 ordered
overlap 上の matching family である。`𝒰` が topology の cover で `P_sem` が
その topology 上の sheaf なので、sheaf amalgamation により一意な `p∈P_sem(W)` が
存在して `p|_{U_i}=p_i^corr` を満たす。

**証明(reverse)。** 逆に `p∈P_sem(W)` が存在するとする。各 chart 上で torsor の
transitivity と freeness により、一意な `a_i∈M_sem(U_i)` が存在して
`p_i=a_i+p|_{U_i}` と書ける。overlap 上で差を取ると

```math
r_{\mathrm{sem},ij}=a_j-a_i,
\qquad\text{すなわち}\qquad
r_{\mathrm{sem}}=\delta^0_{\mathrm{sem}}a
```

であり、`[r_sem]=0` である。三項同値の最後の同値 `[r_sem]=0⟺[r_E]=0` は
§5.5 の residual class 対応である。∎

ここで一意なのは固定した corrected matching family の amalgamation であり、
`P_sem(W)` 全体の一意性ではない。異なる global repair の差は degree-zero data が担う。

**Equation 側。** 同じ結論が equation 側にも降りる。次の三つを追加で仮定する:
SAGA presentation exactness が `S_X` の全 context 上で成立すること、仮定 7 の
`β` が site 全体の natural transformation として与えられること(比較 core が
使うのは intersection diagram 上の成分だけなので、この global 化は追加の仮定で
ある)、`P_E` も選ばれた topology 上の sheaf であること。各 chart と nonempty
overlap 上では、`Φ_V`-equivariant な `β_V:P_sem(V)→P_E(V)` が全単射である。
単射性は semantic torsor の transitivity、target torsor の freeness、`Φ_V` の
単射性から、全射性は target torsor の transitivity と `Φ_V` の全射性から出る。
この局所全単射性は次の三段で global へ持ち上がる。単射性: `β_W(p)=β_W(p')`
ならば各 chart 上で `β_{U_i}` の単射性から `p|_{U_i}=p'|_{U_i}` であり、
`P_sem` の separatedness から `p=p'` である。全射性: `q∈P_E(W)` に対し各 chart で
`p_i:=β_{U_i}^{-1}(q|_{U_i})` と置くと、`β` の naturality と overlap 上の単射性
から `(p_i)` は全 nonempty `i<j` overlap 上で一致し、補題 5.2A と `P_sem` の
amalgamation により一意な `p∈P_sem(W)` へ貼り合う。最後に `β_W(p)` と `q` は
各 chart への restriction が一致するので、`P_E` の separatedness から
`β_W(p)=q` である。こうして

```math
\mathrm{Nonempty}\,P_E(W)\iff[r_E]=0
```

が従う。

### 5.7 定理の適用範囲

本比較定理は可換群値 presheaf の additive theorem である。
nonabelian torsor の pointed-set-valued `H^1`、2-cocycle と gerbe による
higher coherence、stack の descent は、それぞれ独立の statement を要する。
additive `H^1` comparison からこれらの結論は導かない。

また、本定理が扱う `H^1` は、selected monomorphic AAT cover `𝒰` に相対的な
Čech `H^1(𝒰,-)` である。cover の選択に依存しない sheaf cohomology との同一視
には、refinement invariance または Leray 型 acyclicity の追加条件を要し、
本論文はこれを主張しない。

さらに、本定理の Lean 形式化は context category が thin な site 上で
行われている(第3.3節の finite-meet poset model はその代表例である)。
一般の `ArchCtx(X)` 上では、補題 5.2A を含む §5.6 の gluing 論証は
monomorphism と pullback の普遍性を使うが、その形式化は行っていない
(thin 性により不要になる仮説の詳細は Appendix A.4)。

### 5.8 有限 witness: independently generated circle comparison

**例 5.3。** 四つの chart と四つの nonempty overlap
`U_01, U_12, U_23, U_30` を持ち、nondegenerate triple overlap を持たない
monomorphic 4-cycle cover を取る。

**係数の比較。** 各 nonempty intersection `V` で semantic support を一 generator
`σ_V`、local repair relation を `2σ_V=0` とすると(generator `σ_V` 上の
free abelian group を `ℤ[σ_V]` と書く)、semantic 側は独立に

```math
M_{\mathrm{sem}}(V)=\mathbb Z[\sigma_V]/(2\sigma_V)\cong\mathbb F_2
```

を生成する。equation 側では `O_E(V)=ℤ`、`I_Ob^E(V)=(2)` から `Q_E(V)=ℤ/(2)` を得る。
interpretation `χ_V(σ_V)=[1]` に対して §5.3 の三条件は直接検査できる:

```text
soundness:    2σ_V ↦ [2] = 0
completeness: ker(ℤ → ℤ/(2)) = 2ℤ
generation:   [1] は ℤ/(2) を生成する
```

よって §5.3 の構成が `M_sem≃Q_E` を与える。これは一方の complex の transport
ではなく、semantic presentation `ℤ[σ]/(2σ)` と equation quotient `ℤ/(2)` の
presentation comparison である。

**Local state system と affine transition。** 各 chart と各 nonempty overlap 上で
`P_sem=𝔽₂` とし、`M_sem(V)≅𝔽₂` は加法で作用する。oriented edge `e`
(source chart → target chart)に対し、overlap への二つの restriction を

```math
\rho^{\mathrm{src}}_e(x)=x,
\qquad
\rho^{\mathrm{tgt}}_e(x)=x+t_e
```

と取る。ここで transition は

```math
(t_{01},t_{12},t_{23},t_{30})=(1,0,0,0)
```

である。最後の edge は `U_03` を `3→0` に向けたものであり、`𝔽₂` では向きの反転に
よる符号は変わらない。triple overlap がないため、これらの restriction に追加の
functoriality 条件はかからない。

**Residual の計算。** 各 chart で local state `p_i=0` を選ぶ。edge `e` の overlap
上では、source chart と target chart のそれぞれから同じ `0` が restriction されて
来るが、二つの restriction は異なる写像である。§4.2 の residual の定義(overlap
上の二つの restriction の差)により

```math
r_{\mathrm{sem},e}
=\rho^{\mathrm{tgt}}_e(0)-\rho^{\mathrm{src}}_e(0)
=t_e
```

である。local state がすべて `0` でも residual は消えない: mismatch を担うのは
state の値ではなく、同じ `0` を overlap へ運ぶ二つの restriction の差、すなわち
affine transition だからである。したがって

```math
r_{\mathrm{sem}}=(1,0,0,0)\in\mathbb F_2^4.
```

**Equation 側と `β` の独立構成。** `P_E=𝔽₂` とし、oriented edge 上の affine
transition を semantic 側と同じ数値 `(1,0,0,0)` で独立に与える。local-state
interpretation `β` は、各 chart と各 nonempty overlap 上の `𝔽₂` 座標の恒等写像
とする。この定義は `Φ` にも repair relation にも言及しない。generator 上の
equivariance は、`χ(σ)=[1]` の下で `β(σ+x)=x+1=χ(σ)+β(x)` という `𝔽₂` の
直接計算であり、restriction との可換は、両側の transition が同じ数値で与えられて
いることからの成分計算である。こうして仮定 5–7 のデータが `R_rep` と独立に揃い、
§5.3 の導出が soundness `χ̃(2σ)=[2]=0` を帰結する — 上の係数比較で直接検査した
soundness 行と一致する。各 chart で `e_i=0` を選ぶと、これは §5.5 の対応選択
`e_i=β(p_i)` にあたるので、cochain 水準で

```math
r_E=\kappa^1(r_{\mathrm{sem}})=(1,0,0,0)
```

である。

**Cocycle 性と非-coboundary 性。** nondegenerate triple overlap がないため
`C²(𝒰)=0` であり、`δ¹r_sem=0` は自動的に成立する。一方、任意の
`a∈C⁰(𝒰)` に対し `(δ⁰a)` の成分は overlap 上の `a_j|-a_i|` であり、4-cycle を
一周する edge sum を取ると各 chart の成分がちょうど 2 回ずつ現れるので、`𝔽₂` では
和が零になる。`r_sem` の edge sum は `1+0+0+0=1` なので、`r_sem` は `δ⁰`-像では
ない。したがって

```math
[r_{\mathrm{sem}}]\ne0,\qquad
[r_E]\ne0,\qquad
\kappa_*([r_{\mathrm{sem}}])=[r_E].
```

**実コードとの関係。** この例は、SAGA 比較が零類だけでなく非零類も保存することの
有限 witness である。非零類を立てているのは chart の個数ではなく、「閉ループ上の
奇パリティ + そのループを埋める面(triple overlap)の不在」という
**cycle-without-a-face 機構**である。第7章の one-cent obstruction は、
この機構が実在 architecture に現れた事例である(§7.2)。

---

## 6. Lean Formalization Status

Lean 形式化は、SAGA 数学の machine-checked definitions、theorems、witnesses、
proof chain を記録する。本章は release 時点の形式化 status を declaration 単位で
報告する。status の一次証拠は、release tag で固定される Lean source と、
登録 declaration 全件を standard mathlib axioms — `propext`、`Classical.choice`、
`Quot.sound` — の allowlist で検査する kernel axiom 監査、および release CI の
focused check である(source の構成と監査の実体は Appendix B)。本章の表に
載せる declaration はすべてこの監査に登録されている。

### 6.1 形式化の範囲

SAGA theorem chain は、第5章の定理の入力構造(定理 5.1 の入力 1–8)をそのまま
Lean structure として固定する形で形式化されている。構成部品は次のとおりである
(source file との対応は Appendix B)。

- monomorphic ordered cover、intersection diagram、three-term Čech complex と
  cover-relative `H^1`
- semantic repair presentation と `M_sem` の presheaf 構成
- affine semantic repair system、両側の selected atlas と residual
- soundness の導出、presentation exactness、係数同型 `Φ`、三条件の独立性を示す
  有限反例
- equation 側の realization / production(equation system が生成する `Q_E` への
  接続)
- cochain 比較 `κ`、`H^1` 同型、residual 対応
- true sheaf descent、grounded global gluing、中心定理の最終束ね
- 有限 witness(非零の 4-cycle circle witness、零類の descent witness)
- 第3.3節の finite-meet poset model 上の site 実現と、§4.1 の ordered Čech
  complex との比較 bridge(補題 5.2A の形式化対応物を含む)

Lean source の docstring は、本論文の定理番号とは別系列の番号(`X.定理1.1`
など)を label に用いる。declaration と label の対応も Appendix B が固定する。

### 6.2 Status table

status は次の語彙で記述する: `proved`(Lean で証明済み)、`defined only`
(定義のみ形式化)、`future proof obligation`(証明義務として明示済み・未証明)、
`empirical hypothesis`(経験的仮説であり証明対象でない)、`unported`
(紙上の証明は存在するが Lean へ未移植)。

| Paper claim | Lean declaration | Status | Assumptions |
| --- | --- | --- | --- |
| 定理 5.1 の結論束(residual 対応・零/非零同値・grounded gluing) | `SagaEquationPacket.sagaCentralTheorem` | proved | selected packet(§6.1)、completeness 二条件(入力 4)、cover 添字集合の `Fintype`。gluing 節はさらに cover の topology 所属と true sheaf 条件に条件付き |
| 定理 5.1(i): repair-relation soundness の導出 | `PrimaryStateCorrespondence.relationSound_of_stateCorrespondence` | proved | local-state correspondence(入力 5–7) |
| 定理 5.1(i): 係数同型 `Φ` | `SagaEquationPacket.phiEquiv`(generic 版: `PrimaryCoefficientCorrespondence.phiEquiv`) | proved | soundness と completeness 二条件 |
| 定理 5.1(i): 三条件それぞれを外す反例 | `ExactnessFixtures.soundness_failure` / `completeness_failure` / `generation_failure` | proved | なし(各 fixture は対象条件の failure を statement 化した有限反例であり、残り二条件の同時成立までは statement に含めない) |
| 定理 5.1(ii): cochain 可換 `κδ=δκ` | `kappa1_delta0`、`kappa2_delta1` | proved | 係数 family の restriction-natural 同型 |
| 定理 5.1(ii): `H^1` 同型 `κ_*` | `SagaEquationPacket.kappaStarAddEquiv`(packet 上の `≃+`。generic 版: `kappaH1AddEquiv`) | proved | completeness 二条件 |
| 定理 5.1(ii): residual 対応 `κ_*([r_sem])=[r_E]` | `SagaEquationPacket.residual_correspondence_class`、整合 atlas 版 `betaAligned_residual` | proved | completeness 二条件 |
| 定理 5.2 = 定理 5.1(iii): grounded global gluing | `SagaEquationPacket.globalRepair_nonempty_iff`(`P_sem` 側同値)、`sagaGroundedGluing`(equation 側同値まで統合) | proved | true sheaf 条件、cover の topology 所属。equation 側同値はさらに completeness 二条件 |
| 補題 5.2A(ordered matching completion) | `SiteStateData.matchingFamily_iff` | proved | thin な context category(§5.7、Appendix A.4)、省略 pair 上の state の subsingleton 仮定(empty-overlap normalization の形式化対応) |
| 例 5.3(4-cycle circle witness、非零類の transfer) | `CircleWitness.semanticResidualClass_ne_zero`、`circle_nonzero_class_transfer` | proved | なし(具体 4-cycle model 上の閉じた検証) |
| 零類側の witness(定理 5.2 の非空発火) | `DescentWitness.descentTrueSheaf`、`descent_sagaGroundedGluing` | proved | なし(具体 model 上の閉じた検証) |

表の全行は kernel axiom 監査に登録済みであり、kernel axiom は standard mathlib
axioms に限られる。`sorry` や追加公理を含む行はない。

本論文の数学(第3〜5章)に対して残るものは次のとおりである。

- 一般(thin でない)context category 上の §5.6 gluing 論証
  (monomorphism と pullback の普遍性を明示に消費する形): `unported`(§5.7)。
- refinement invariance / Leray 型 acyclicity による sheaf cohomology との
  同一視、nonabelian `H^1`、gerbe、stack descent: 本論文は主張しないため、
  証明義務に含めない(§5.7)。
- 第7章の measurement run を Lean へ移送すること(実測 packet からの
  定理 5.1 instantiation の生成): 行っていない。定理 5.1 の有限 instantiation は
  本表の witness 行(例 5.3)が担い、第7章の packet は §7.6 の condition matrix が
  示す有限検査を担う。両者の分業は §7.7 に明記する。

**TODO:** release tag 確定後に、対象 commit hash と release CI run の参照を
本章に固定する(付録 A で管理)。

### 6.3 形式化の到達地点の読み方

Lean claim は、statement の強さと proof-use によって記述する。
declaration が形式化しているのは、本論文の定理そのものではなく、
その定理の selected 入力を Lean の structure として固定した上での結論である。
本論文の数学に対して残る未証明、未接続、未移植は前節の一覧が示すとおりであり、
第9章の研究展望とは区別される。

---

## 7. ArchSig: Executable SAGA Diagnosis

ArchSig は、観測(ArchMap)と法・方程式(LawPolicy、law surface、
MeasurementProfile)の二系統の入力から、grounding、導出 residual、
boundary membership、run 対の比較、gate 判定を計算する measurement system
(Rust 製 CLI)である。本章はまず入力契約と計算を定義し(§7.1)、実在
microservice architecture に対する SAGA フル診断を一つの計算として示す
(§7.2〜§7.4)。観測の供給工程は §7.5、結論の条件種別は §7.6、claim の境界は
§7.7、再現手順は §7.8 が固定する。

### 7.1 入力契約と計算

ArchSig の入力は次の artifact である。

- **ArchMap**: 対象システムの Atom 観測。chart(局所文脈)、section value、
  overlap の対応を記録する。
- **LawPolicy**(artifact 名): 使用する Atom vocabulary と selected equation
  reading を固定する。
- **law surface**(artifact 名): 診断に用いる equation surface の族
  (closed-equational、SAGA-grounded、descent)。descent surface は
  mismatch 辺に束縛される witness variable の宣言を含む。
- **MeasurementProfile**: 係数(本 case study では `F2`)を含む measurement の
  条件を固定する。
- **repair plan**: 選択複体(charts、overlaps、任意の triple overlap、
  enumeration assertion)と対象 cover への参照だけを宣言する。residual、係数、
  比較データは運ばない。

repair plan の charts と overlaps は観測への参照であり、観測された cover と
restriction に解決できない宣言は受理されない。残る enumeration assertion と
triple overlap 宣言の有無は author assertion であり、結論を導出する材料として
ではなく、assumption ledger の開示行として結論に随伴する(§7.6)。したがって
repair plan が独自に加えるものは開示された assumption だけである。

residual は入力ではない。ArchSig の `analyze` は次を計算し、measurement packet
として出力する。

- chart ごとの **grounding**: 各 chart が displayed-equation check を満たすか
  どうか。check の対象は law surface が選んだ defect 座標(displayed equation の
  residual、§3.4 の `ε` の有限実現)と宣言された判定基準であり、
  「chart 上の全方程式の完全な充足」ではない。
- overlap ごとの **residual 導出**: 選択 cover の両端 chart が観測した
  section value 集合の比較から `F2` 値を導出し、law surface の witness 束縛と
  観測 atom 参照の provenance を辺ごとに記録する。witness 束縛とは、mismatch を
  法側の violation 座標(§3.4 の `ν` の有限実現)へ接続する辺ごとの宣言であり、
  instance の値は運ばない。束縛のない mismatch は、導出 residual の立つ法側の
  座標を持たないため、fail-closed に計算不能へ落ちる。
- 選択 1-骨格上の **boundary membership**: 導出 residual が `δ⁰`-像(`B^1`)に
  属するかの有限 `F2` 計算。residual class の語彙は、residual の立つ連結成分に
  triple overlap が宣言され cocycle 検査が実際に走る場合に限って解禁される。
  triple 宣言のない成分では selected `C^2` が零で cocycle 条件が自動成立する
  ため、ArchSig は class 語彙を出さず、その境界を named boundary statement
  として packet に明示する。

`compare` は二つの run の packet を突き合わせ、障害の変化と、run 対の読みを
記録する。run 対の読みとは、両 run の導出 residual の差が選択 `C^1` 上で
`im δ⁰` に属するかの有限 `F2` 判定である。`gate` は packet と gate policy から
`PASS_WITHIN_GATE_POLICY` / `BLOCKED_BY_GATE_POLICY` の判定を返す。

三本の law surface と出力の対応を固定する。closed-equational surface は
辺ごとの規約一致の等式を宣言し、mismatch の検出(cech 段)を担う。
SAGA-grounded surface は chart ごとの defect 座標と判定基準を宣言し、
grounding を担う。descent surface は mismatch 辺への witness 束縛を宣言し、
residual 導出と boundary membership(saga-descent 段)を担う。§7.6 の
condition matrix と注1が言う「段」は、この対応を指す。

この計算が実行するのは、第4章の複体語彙の有限断片である: selected 1-骨格上の
residual 導出、`B^1` 所属、run 対の residual 差が、有限 `F2` 線形代数に落ちる。
定理 5.1 の比較(`χ`、`Φ`、`κ`、presentation exactness)の有限 instantiation は
この計算の範囲に含まれず、第6章の Lean witness が担う(§7.7)。

この契約の下で、本論文の measurement claim は次の主張に立つ。
**SAGA 診断の結論 — residual、boundary membership、gate 判定 — は、Atom 観測と
選択された方程式系から決定論的に導出される。実施者が書けるのは観測の範囲、
選択複体、witness 束縛という選択であって、結論を運ぶ入力はこの契約に存在
しない。** この分離は fail-closed 検査が執行する: 選択 cover 外の chart、
観測された restriction を持たない overlap、重複した overlap 宣言、未観測の
section、witness 束縛のない mismatch は、いずれも結論を生成せずに計算を
停止させる。したがって、選択によって障害を沈黙させることはできるが
(列挙完全性は §7.6 の assumption として開示される)、観測が一致している辺の
上に非零 residual を立てることはできない。

### 7.2 実コード事例: one-cent obstruction

ここで本論文の case study を明かす。対象は、microservice benchmark として広く
使われるオープンソースの列車予約システム train-ticket
(commit `313886e99bef`、42 services)である。

このシステムの cancel–inside-payment–order の実呼び出し三角形上で、
払い戻し金額の規約が3流儀とも異なる。いずれも実ソースで確認され、
ArchMap の section value として観測された。

- **cancel**: `Double.parseDouble(order.getPrice()) * 0.8` を
  `DecimalFormat("0.00")` で丸めて文字列化(浮動小数点 + 丸め)
- **inside-payment**: `new BigDecimal(order.getPrice())` の正確算術
- **order**: `private String price` の素通し保管

三つの service の金額表現は、実装上はいずれも `string` を介して受け渡される。
型の一致は成立している。異なるのは、その `string` が表す金額の丸め、scale、
計算、保存の**意味規約**である。さらに、実施者の source 調査では、3サービスの
金額を同時に照合する箇所は見つからなかった。この調査所見は、選択複体に
triple overlap を宣言しないという形で診断へ反映される。同時照合サイトの不在
そのものは、観測 artifact が示す事実ではなく実施者の assertion として扱う
(§7.3、§7.6)。

この構図は、例 5.3 と同じ **cycle-without-a-face 機構**の 3-cycle instance と
して読める。複体そのものは同一ではない — 例 5.3 は 4-cycle、本 case は 3-cycle
である — が、非零類を立てる機構は共通する: 閉ループ上の奇パリティ(3流儀の
衝突)と、そのループを埋める面(triple overlap)の不在である。
払い戻し計算 `0.8 × 価格` の丸め剰余 — **1セント未満のドリフト** — は、
どの chart にも記帳されていない。この case study を **one-cent obstruction** と呼ぶ。

**Semantic trace。** 三辺が比較する量と実装規約を固定する。

| Edge | 比較する量 | 規約 L | 規約 R | 正規化 | 期待 equation | witness 変数 |
| --- | --- | --- | --- | --- | --- | --- |
| cancel–inside-payment | 払い戻し金額 | `0.8 × price` を `DecimalFormat("0.00")` で丸めた文字列 | `BigDecimal` の正確算術値 | 通貨値(scale-2) | 両 chart の払い戻し金額が同一の通貨値として確定 | `e_cancel_insidepay` |
| inside-payment–order | 払い戻しの基準額 | `BigDecimal(order.getPrice())` の正確値 | `String price` の素通し記載額 | 通貨値(scale-2) | 決済が用いる基準額が記載額と同一規約で確定 | `e_insidepay_order` |
| cancel–order | 払い戻し比率の適用 | 丸め済み `0.8 × price` | 記載額 `price` | 通貨値(scale-2) | 払い戻し額が記載額の 0.8 倍として一意に確定 | `e_cancel_order` |

この表が固定するのは意味論的根拠の側であり、residual の値そのものは
`analyze` が各辺の観測 section value の比較から導出する(§7.1)。
三辺はいずれも、同一の semantic quantity — この注文の払い戻し金額 — の
restriction を比較しており、mismatch の自由度は「その量を通貨値としてどの丸め・
scale 規約で確定するか」という一つの向きに乗る。witness 束縛は、その向きを
辺ごとに選ぶ law 側の宣言であり、instance の値は運ばない。

**有限 witness。** 頻度や総損失の評価(runtime 実測を要する。§7.7)とは分離し、
source expression で確認済みの各規約を同一の払い戻し量へ適用した正規化計算と
して、入力価格を一つ固定した witness を示す。

```text
original price:        12.33
cancel 規約:           0.8 × 12.33 = 9.864 → DecimalFormat("0.00") → "9.86"
inside-payment 規約:   同じ払い戻し量を正確算術で確定 → 9.864
通貨値としての正規化:  9.86(scale-2)対 9.864
nonzero remainder:     0.004(1セント未満)
```

cancel 側の乗算は二進浮動小数点で行われるが、この入力では scale-2 丸めの結果に
影響しない。remainder は、どの chart の局所方程式にも違反しない — cancel は
cancel の丸め規約に、inside-payment は正確算術に忠実である — が、二つの chart
の値の差として残る。

この数値 witness は実施者による source 水準の検算であり、ArchSig の計算には
価格、`0.8`、丸め、`0.004` のいずれも現れない。ArchSig の residual は金額規約の
観測表現である section value の集合比較から導出される(§7.1)。

### 7.3 診断階段

measurement の入力構成は次のとおりである。

- **cover**: 6 chart。診断三角形 {cancel, inside-payment, order} と、託送料金
  領域 {preserve, consign, consign-price}。後者は三角形の外側の観測領域であり、
  一致する辺や repair 後に境界内(`B^1`)へ収まる mismatch を同じ packet 内に
  持つ対照を与える。
- **law surface**: closed-equational、SAGA-grounded、descent の3本。descent
  surface は観測された 6 辺すべてに witness 変数を束縛する。
- **repair plan**: 選択複体だけを宣言する。chart は観測 cover の 6 chart
  そのもの、overlap は観測された restriction 6 辺(三角形 3 +
  consign–consign-price + preserve–consign + preserve–order)、triple overlap は
  宣言しない(§7.2 の調査所見の反映。assertion としての身分は §7.6)。
- **repaired 変種**: 三角形の 3 chart を BigDecimal scale-2 HALF_EVEN 統一規約に
  置換した仮修理 ArchMap。

導出 residual(head)は、三角形 3 辺と preserve 系 2 辺で section value が
不一致、consign–consign-price で一致となり、選択複体は単一の連結成分になる。
三角形一周の奇パリティは `δ⁰` で解けず、residual は非境界に立つ。

診断階段の結果は次である。

| 幕 | 結果 |
| --- | --- |
| head analyze | `MEASURED_NONGLUING_RESIDUAL`(`run:78c31d6a3172`) |
| └ grounding | `measured_zero` — 各 chart は自分の局所方程式を満たしている |
| └ residual 導出 | 三角形 3 辺 + preserve 2 辺で mismatch、consign–consign-price は一致(すべて観測から導出) |
| └ boundary membership | `measured_nonzero`(`inB1: false`。triple 宣言不在のため class 語彙は不解禁 — named boundary statement で明示) |
| gate head | `BLOCKED_BY_GATE_POLICY` |
| repaired analyze | `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`(`run:6685bab8db21`。残る preserve 残差は `B^1` 内) |
| compare head→repaired | `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE`。run 対の読みは「両 run の residual の差は `δ⁰` で解けない」であり、head 非境界 → repaired 境界内の変化と整合する(§7.1) |
| gate repaired | `PASS_WITHIN_GATE_POLICY` |

### 7.4 計測が示したこと

**局所整合・大域非貼合の実在。** grounding の `measured_zero` は、各 chart が
自分の局所方程式を満たしていること(§7.1 の displayed-equation check の意味で)を
計測として言う。cancel は cancel の丸め規約に、
inside-payment は正確算術に、order は素通し保管に、それぞれ忠実である。
ペアごとの受け渡しも各々は成立している。計測として観測されたのは、規約
mismatch の奇パリティが閉ループ上で `δ⁰` により解けないこと(`inB1: false`)で
ある。ループを埋める面(triple)の不在の assertion(§7.2)の下で、この計測は
「局所的には整合、大域的に貼り合わない」という SAGA の中心構造の、作為的に
仕込んだのではない実在 OSS 上の instance になる。

**診断階段の全段が導出 residual だけで機能。** 観測(ArchMap)と法・方程式
(law surface、MeasurementProfile)から導出した residual による非境界の計測、
gate による blocking、修理計画の事前検証、compare による障害消滅と run 対の
residual 差の記録、gate PASS まで、authored な residual・証書・比較データを
一切供給せずに一周した。実施者の宣言として残るのは選択複体(§7.1)と
repaired 変種だけである。

**数学的規律の実効。** ドリフトの立つ三角形自体を triple として申告すると
cocycle 条件で拒否される。これは数学的に正当な拒否である。witness 束縛のない
mismatch と典拠のない参照は fail-closed に落ちた。実データで負荷をかけて
規律が守られた。

**沈黙の実行。** runtime 実測数値を要する計測軸(axis 名 `harmonic-debt`)は、
実測が無い状態では供給されず、沈黙として扱われた。また、triple 宣言のない
複体で class 語彙を出さないことも同じ規律の実行であり、ArchSig はその境界を
named boundary statement として結論の近くに最小限の形で記録した。

### 7.5 入力の供給: 観測の authoring と再現性

ArchMap の供給は、source の使われ方を読む意味読解を含む。この読解は
確率的な過程であり、決定論的な計算では置き換えられない。本研究は、
この段を隠さずに工程として固定する。すなわち、ArchMap の作成を
AI agent が実行する固定手順書 — 以下 **authoring SKILL** — として定義し、
確率的な読解を追跡可能な artifact へ変換する。

SKILL は次の規律で観測の provenance を固定する。

- **機械層と読解層の分離**: 機械層はファイル列挙、content hash、正規化キーの
  literal 比較、参照整合の検査だけを行う。Atom の生成、意味の選択、候補の採否、
  類似度による merge は機械層に許さず、読解層の記録された判断として残す。
- **scope の承認記録**: 対象 repository の revision、include / exclude glob、
  承認された scope manifest を artifact として固定する。observation claim は
  記録された revision と選択された scope に有界であり、全 evidence の抽出は
  主張しない。
- **独立2パス読解と調停**: 標準 mode(full-dual)は同じ worklist を独立に
  2回読み、extraction-diff を取り、相違を source 再読で調停する。調停の
  採否は件数と根拠つきで記録される。
- **authoring audit**: 統合後の ArchMap は機械検査(参照整合、coverage ledger
  など)を通過して初めて measurement の入力になる。
- **run 記録とモデルの明記**: 各 authoring run は使用モデルを記録する。
  本 case study の土台となった全42サービスの ArchMap(2,118 atoms / 43
  contexts / 440 sources)は、抽出・調停の subagent を軽量モデルに固定した
  run で作成された。観測供給が高価な frontier model を要求しないことは、
  この measurement 系の実用条件として実測されている。

この工程設計の下で、再現性は二層に分かれる。ArchSig の計算は決定論的であり、
同じ入力 artifact から同じ出力を返す(digest で検証される)。ArchMap の生成は
確率的だが、scope、根拠、手順、調停、audit が artifact に固定されるため、
第三者は同じ規律で観測を再実行し、結果を突き合わせられる。確率的な意味読解と
決定論的な計測を直列に分業させることが、この供給 pipeline の設計原理である。

### 7.6 条件と入力種別: condition matrix

診断階段の各結論が、どの種別の条件の下で立っているかを一表に固定する。
`computed` は入力からの有限計算、`checked` は ArchSig が有限 artifact に対して
検査した条件、`assumed` は author または profile が宣言し packet が assumption
ledger に記録する前提、`unmeasured` は供給せず沈黙した軸を表す。head / repaired
の両 packet が同じ区別を記録している。

| Condition | 種別 | Status | 記録 |
| --- | --- | --- | --- |
| finite cover | 有限 artifact の性質 | `checked` | site cover digest を正規化した contexts・covers・導出 nerve から算出して記録 |
| residual 導出 | 観測 section の比較 | `computed` | 辺ごとの `F2` 値・witness 束縛・観測 atom 参照の provenance。head は三角形 3 辺 + preserve 2 辺が mismatch |
| witness 束縛 | law surface の宣言 | `checked` | mismatch 辺は witness 変数の束縛を要求する。未束縛の mismatch は fail-closed に計算不能へ落ちる |
| 係数(`F2`) | 法側の選択 | `checked` | 選択 MeasurementProfile の宣言。repair plan は係数を運ばない |
| 選択複体の列挙完全性 | author assertion | `assumed` | repair plan の enumeration assertion を assumption ledger 行として記録 |
| triple 不在 / class 語彙 | author assertion | `assumed`(class 語彙は不解禁) | 選択複体は triple を宣言しない(§7.2)。読みは 1-骨格の boundary membership に留まり、named boundary statement が境界を明示する |
| boundary membership | 有限 `F2` 計算 | `computed` | head は `inB1: false`、repaired は `inB1: true` |
| U-adequacy、Leray 型比較 | profile 供給の前提 | `assumed` | U-adequacy は選択 cover が対象の読みに十分という前提、Leray 型比較は cover 相対の読みを cover 非依存の sheaf cohomology と比較するための前提。いずれも ledger 行として開示し、後者の比較は主張しない(§5.7) |
| torsor 性・作用の固定性・係数 descent | profile 供給の前提 | `assumed` | 局所 section を係数の torsor として読むための3前提(局所 section の torsor 性、作用の固定性、係数の descent)。ledger の 3 行 |
| restriction surjectivity | profile 供給の前提 | `assumed` | restriction 写像が overlap 上へ全射であるという前提。ledger 行 |
| forest nerve | profile 供給の前提 | `assumed`(本 packet では不成立) | ledger は forest 前提を記録し、同じ packet の nerve 計算は閉路 1 を `computed` で示す(注1) |
| quotient sheaf condition | law surface の宣言 | `assumed` | 商係数にあたる係数系が sheaf condition を満たすという law surface 側の宣言。ledger 行として開示 |
| run 対の residual 差(head↔repaired) | run 対の導出読み | `computed` | 両 run の導出 residual の差の `δ⁰` 可解性(§7.1)。本対では差は `δ⁰` で解けない |
| repaired ArchMap | 仮修理入力 | supplied / hypothetical | 統一規約を表す仮説 variant。`PASS_WITHIN_GATE_POLICY` は実装済み修理を示さない |
| runtime の金額規模 | 経験的計測 | `unmeasured` | `harmonic-debt` を供給せず沈黙。頻度・金額を結論に含めない |

注1: forest nerve は開示された不成立前提である。head の saga-descent 段の
非零読み(`B^1` 所属判定)はこの行に依存しない。cech 段の verdict は別途この
assumption への依存を宣言している。

### 7.7 主張の境界

本 case study の claim は次の範囲に限る。規約 mismatch の検出自体は
closed-equational surface の段が担った。SAGA 段が加えたのは、同じ観測を
選択 1-骨格上の boundary membership として読む descent 読解、grounding の罠
(§7.4)の明示、修理計画の事前検証、run 対の residual 差の読み(§7.1)、gate の一貫した
診断であり、「SAGA が新しい障害を発見した」という主張は行わない。

authored なのは選択である。選択複体(repair plan)、witness 束縛(law surface)、
repaired 変種は実施者が書いた宣言であり、residual の値はどれも運ばない。
class 語彙は解禁していない: 三角形を含む成分に triple が宣言されない本 packet
で、ArchSig の読みは boundary membership に留まる(§7.6)。repaired は section を
書き換えた仮修理 ArchMap であり、`PASS_WITHIN_GATE_POLICY` が示すのは
「この修理案なら貼り合う」という事前検証の機構である。ドリフトの発生頻度と
金額規模は runtime 実測を要するため本論文では計測していない。広い benchmark
評価と一般的な検出性能は、別の実証研究として扱う。

定理 5.1 の有限 instantiation は本 case study の対象外である。その家は第6章の
Lean witness(例 5.3 の circle witness)であり、本章の packet が担うのは §7.6 の
condition matrix が示す有限検査である。measurement run を Lean へ移送する対応は
要求しない。

供給工程の SKILL 化の適用範囲も明示する。§7.5 の authoring SKILL が覆うのは
ArchMap の供給であり、選択複体(repair plan)にも同種の authoring SKILL が
整備されている。law surface と repaired 変種は、本実験時点では builder script と
authored 宣言として供給された。本実験の builder script と供給所見は、
その設計素材として記録されている。

### 7.8 再現

すべての入力 artifact、一次出力、builder script、authoring SKILL 本体は
再現 bundle に収録する。artifact の schema version(repair plan は
`archsig-repair-plan/v0.5.7`)は bundle の manifest が固定する。
一次出力の `inputDigests` は canonical digest と一致することを検証済みである。
再現は、固定した ArchSig version と入力から `analyze`(head / repaired)、
`compare`、`gate` ×2 を実行し、runId と gate 判定の一致で確認する。

**TODO:** deposit 内の相対 path、ArchSig version、実行 command 一式、
expected output を release identity 確定後に固定する(現行の再現手順は
`docs/reports/train_ticket_dogfooding/saga_diagnosis.md` が正本)。

---

## 8. Related Work

SAGA の主成果を、(1) cohomological program analysis、(2) sheaves for
architecture and systems engineering、(3) architecture conformance and formal
connection、(4) mechanized theorem chain and executable measurement の四群の
中へ位置づける。

### 8.1 Cohomological program analysis

Young は、Python program の observation site 上の semantic presheaf に対する
Čech-cohomological analysis として、type checking、bug finding、program
equivalence を統一する [Young 2026, arXiv:2603.27015]。local semantic
observation と Čech `H^1` を用い、Lean 形式化と実行可能な analyzer を報告する
点で、SAGA に最も近い同時代研究である。

両者は次の構造を共有する。

```text
local semantic observations
  -> site / cover
  -> presheaf or coefficient system
  -> Čech complex
  -> H¹ obstruction
  -> executable analysis
```

相違は数学的中心と抽象度にある。Young は Python の program-semantic presheaf 上で
直接コホモロジーを計算する。AAT は言語独立な Atom と equation system から始まり、
異なる言語、service、storage representation にまたがる fact を一つの
architecture object 上で関係づける。SAGA は semantic-repair cohomology と
equation-generated AAT Čech cohomology を**別々に構成した上で**、両者の
`H^1` の一致を証明する比較定理である。この差は one-cent case に具体化される。
問題の金額はいずれも `string` として表現され、実装型の一致は成立している。
SAGA が測るのは、型名の差ではなく、局所的に成立する意味規約が一つの global
architecture へ貼り合うかである。

| 軸 | Young 2026 | SAGA |
| --- | --- | --- |
| primary object | Python program と observation sites | 言語独立な Atom family と architecture object |
| coefficient | semantic presheaf、`F_2` realization | equation system が生成する `Q_E=O_E/I_Ob` |
| central theorem | Čech cohomology による program-analysis claims | `H^1_sem ≅ Čech H^1(𝒰,Q_E)` comparison |
| repair reading | rank = independent fixes | residual class、boundary、repair gluing |
| empirical unit | 375 program-analysis benchmarks | 実在 microservice architecture と repair 前後比較 |
| domain-specific construction | program-semantic presheaf 上の直接計算 | 独立な二 presentation(semantic repair / equation quotient)、`χ/Φ/κ` の構成、architecture 相対の exactness 条件 |
| discharged obligation | cohomology 計算の program-analysis claims への接続 | soundness の導出、`ker`/`im` 条件の検査、residual class の意味論的対応の証明 |

SAGA が比較の新規性として主張するのは、表の最終二行 — domain-specific
construction とそこで果たされた証明義務 — であり、係数同型から cochain 同型が従う
一般的機構ではない(固有性の帰属は §5.1)。

Young の Lean 形式化(1,259 lines)、375 benchmarks、evaluation 数値は、
同論文が報告する結果として引用する。同論文の analyzer の code artifact は
公開リンクが確認できないため、source-level comparison は本論文の範囲外である。

global-section obstruction の系譜として、sheaf-theoretic contextuality
[Abramsky–Brandenburger 2011] と、その Čech cohomology による非消滅障害
[Abramsky–Mansfield–Barbosa 2012] を基礎文献に置く。computable obstruction の先行例として、
CSP と structure isomorphism への Čech cohomology の応用 [Ó Conghaile 2022]、
distributed task solvability の task sheaf [Felber–Flores–Galeana 2025] を挙げる。

### 8.2 Sheaves for architecture and systems engineering

Gibson は、model-based systems engineering の multi-view consistency に対して
Lean 検証済みの sheaf model を与え、pairwise interface 上の compatible local
designs による global design の特徴づけを示す [Gibson 2026, arXiv:2605.08609]。
SAGA は相補的な obstruction-theoretic 方向を開発する。すなわち、局所データが
貼り合わないときに残る `H^1` 類を構成し、その semantic realization と
equation-generated realization の比較を証明する。

歴史的出発点として、objects と interaction の sheaf semantics [Goguen 1992] を置く。
cellular sheaf と有限計算の基礎文献として
[Curry 2014; Robinson 2017; Hansen–Ghrist 2019] を挙げる。

### 8.3 Architecture conformance and formal connection

architectural mismatch [Garlan–Allen–Ockerbloom 1995] は、components、connectors、
構築過程に埋め込まれた assumptions の不一致を分析した。SAGA はこの種の不一致を
局所 equation と global gluing の数学へ移し、残差を `H^1` 類として扱う。
reflexion models [Murphy–Notkin–Sullivan 1995] は high-level model と source model の
convergence / divergence を計算する conformance の代表的出発点である。
Wright [Allen–Garlan 1997] は connector protocol の compatibility を CSP で形式化した。
SAGA が扱うのは protocol 適合性ではなく、複数の局所 semantic repair が cover 全体で
貼り合うかという cohomology class である。ADL の表現力の整理
[Medvidovic–Taylor 2000] と architecture erosion の系統的整理
[De Silva–Balasubramaniam 2012; Li et al. 2022] に対して、SAGA は選ばれた
local data に対する global obstruction class と repair comparison を提供する。

### 8.4 Mechanized theorem chain and executable measurement

Lean 4 [de Moura–Ullrich 2021] と Mathlib [mathlib Community 2020] は形式化環境の
出典として引用する。SAGA の formalization contribution は Lean の利用自体ではなく、
semantic repair presentation、cover-relative Čech complex、係数同型と
cochain 比較、true sheaf descent、零・非零の有限 witness を、中心定理の
結論束に至る一つの machine-checked theorem chain として構成した点にある
(第6章)。Young と Gibson の形式化との比較は、theorem chain の範囲と
executable measurement への接続で行う。

### 8.5 Synthesis

先行研究は、sheaf を global consistency の言語として、cohomology を計算可能な
obstruction として、formal architecture model を conformance 分析の基盤として
確立してきた。SAGA はこれらの系譜に、software architecture のための
equation-generated AAT Čech complex を構成し、その first cohomology が独立に
定義された semantic-repair obstruction と一致することの証明を加える。
Lean が比較を検証し、ArchSig がその有限 architectural instance を評価する。

**TODO:** 投稿時点で 2026 年文献の最新版と publication status を再確認する。

---

## 9. Discussion and Research Outlook

SAGA 比較定理は、AAT の local-to-global 能力の最初の完成した定理であり、
より大きな研究 program の最初の縦断でもある。本章は、この定理が確定させたものを
議論し(§9.1)、そこから開く研究方向を示す(§9.2〜9.6)。本章の §9.2 以降は
研究展望であり、証明済みの成果と混同しない。各方向の定理開発、実装、
tooling の計画は本論文の範囲外である。

### 9.1 SAGA が確定させたもの

比較定理の第一の帰結は、**翻訳可能性**である。semantic repair の言葉で立てた
診断と、equation geometry の言葉で立てた計算は、`H^1` と residual class の水準で
一致する。以後の理論開発は、どちらの側で行っても他方へ翻訳できる。意味論の側で
発見された構造は幾何の道具で計算でき、幾何の側で証明された定理は修理の言葉で
読める。

第二の帰結は、**反実仮想の接地**である。「この修正がなければ全体は貼り合わ
なかった」という文は、テストと観測の語彙の中では接地する場所を持たない
反実仮想だった。起きなかった障害は観測できないからである。
定理 5.2 の三項同値は、この文に数学的な身分を与える。零類と global repair の
存在が同値である以上、「correction が類を消したから貼り合った」は経験則ではなく
帰結である。第7章の repair 前後比較は、この帰結が工学の工程でどう働くかを示す
最初の診断実働例である(計測の検査範囲と第6章 Lean witness との分業は §7.7)。

### 9.2 方法としての Rising Sea

本研究 program の方法は、Grothendieck が *la mer qui monte*(rising sea)と
呼んだもの [Grothendieck 2022] に倣う。難問を個別の道具でこじ開ける代わりに、
理論の抽象度の水位を上げ、問題が自然に解ける水準まで持ち上げる。

「局所は成立するが大域で壊れる」という工学の難問は、コードやモジュールを
直接扱う水準では、テスト、契約、CI という局所の道具で挑み続ける対象だった。
問題そのものが部分の重なりに住んでいるため、局所の道具は原理的に届かない。
Atom、site、sheaf、cover、cohomology の水準へ上がると、同じ問題は
座標を持った通常の対象になる。E2E failure は `H^1` の類であり、
類は計算でき、計算できるものは道具の仕事になる。

この水位上げには二つの固有性がある。第一に、**抽象化は可搬性である**。Atom は
言語や framework から独立した水準に置かれるため、理論も計測も特定の技術
stack に依存せず、多言語 system が一つの architecture geometry として扱える。
第二に、**水位は Lean が保つ**。Grothendieck の海は数千ページの散文に堆積したが、
本 program の海は機械検証された定理の塔として維持され、定理が形式検証されて
いる限り水は引かない。SAGA の名が Serre の GAGA [Serre 1956] — 二つの幾何の
対応を確立した比較定理 — へのオマージュであるのは、この構図による。

### 9.3 数学の次の峰

完成した SAGA 数学から、次の理論開発が自然に定式化できる。

- **descent 条件の特徴づけ**: 定理 5.2 の三項同値は selected true sheaf 条件の
  下で成立する。次の峰は、この条件の成立そのものを architecture data から
  特徴づけ、検査可能な仮定へ降ろすことである。これが実現すると、
  「この architecture は descent の仮定を満たすので、局所検証の合格が大域整合を
  含意する」を計測の検査項目にでき、仮定が破れる場所こそ統合検証を集中すべき
  場所だと理論が指させるようになる。
- **higher coherence**: 本論文が原則として分離した nonabelian torsor の
  pointed-set-valued `H^1`、2-cocycle と gerbe、`H^2` 以後の obstruction、
  stack descent(第5.7節)を、それぞれ独立の statement として開発する。
- **architecture schemes と morphism theory**: required equations の零点 locus を scheme として扱い、
  architecture 間の morphism、base change、fiber を定理化する。
- **repair の moduli と derived deformation**: 修理の空間そのものを幾何対象と
  して扱い、修理の変形、退化、特異点を語る。
- **first-order conormal specialization**: obstruction ideal の一次近似が与える
  conormal geometry の specialization。
- **Atom foundations の深化**: Atom 公理系の精密化と、semantic atom /
  equation Atom の対応理論の拡張。

### 9.4 静力学から動力学へ: Software Field Theory

AAT は、ある時点の architecture の整合性を扱う静力学である。Software Field
Theory (SFT) は、その geometry の上に software 進化の力学を構成する研究である。
開発トレースを site として組織し、変更、分岐、合流を幾何の言葉で扱い、
review、CI、運用 feedback を開発系に作用する力として定式化する。

SFT の中心的な見方は、architecture の役割の転換にある。architecture は現在の
コードの形であるだけでなく、**到達可能な未来の形**である。良い architecture とは、
望ましい未来が到達可能で、望ましくない未来が到達困難であるような場の配置である。
この見方の下で、SFT は次の形の中心命題を目指す。

> A software architecture is modular exactly when its future evolution
> satisfies descent.

version 管理の merge は局所変更の貼り合わせであり、SFT はこれを降下理論として
読む。SAGA が証明した静的な comparison は、この力学が各時刻で使う地盤である。
静力学の `H^1` が「いま貼り合わない」を測るのに対し、SFT は「この変更列は
貼り合う未来へ到達できるか」を測ることを目指す。

### 9.5 計測の未来: 生成の時代の不動点

研究展望として、measurement の側にも一つの構図を書き残す。

コードが人間の理解より速く生成される開発では、コードも、テストも、レビューも、
修正案も、同じ確率的な生成の地盤の上で揺れる。その中で、定理に接地した
決定論的な計測は、性質の異なる一点になる。その判定は誰かの意見ではなく、
機械検証された定理の、選ばれた contract 上での帰結だからである。

この構図では、「語れないことに沈黙する」という ArchSig の設計原則が、
安全装置として働く。agent は出力を字義通りに読んで字義通りに行動するため、
根拠なく警告を出す検査器は生成のループを発散させる。与えられた contract から
語れることだけを語る検査器だけが、生成系の gate に置ける。経済的にも、
決定論的な検証の計算費用は確率的な生成に比べて小さく、生成が速くなるほど
「実行前に間違いを落とす」計算の価値は上がる。

人間の仕事は、この構図の中で消えるのではなく移動する。どの語彙で語ることを
許し、どの equation を required とし、何を PASS と呼ぶか — LawPolicy の選択は、
何が守られるべきかの決定として人間の側に残り、むしろそこへ純化される。
第7章の診断階段(非零 residual → BLOCKED → repair 事前検証 → PASS)は、
この構図の最小の実働例である。

### 9.6 Rising Sea research program

本研究 program の全体は、次の連鎖である。

```text
architectural fact を言葉にする
  -> Atom と equation system から AAT geometry を構成する
  -> Lean で数学的主張を形式化する
  -> 選択された有限 instance を計測する
  -> SFT が geometry を evolution dynamics へ接続する
  -> trajectory、reachable future、feedback、governance を計算する
```

SAGA は、この連鎖の最初の三段 — 数学、形式化、計測 — を一つの定理で縦断した
最初の完成例である。本論文が固定した provenance の規律(claim の種類を分け、
各 claim を一次証拠へ接続する)は、後続のすべての峰で同じ形で使われる。
理論の水位が十分に上がったとき、使う側からは水面しか見えなくなる。
engineer は圏も層も cohomology も学ばずに「分析して」と言い、obstruction と
いう言葉だけを受け取り、直し、先へ進む。その静けさが、この program の
到達目標である。

---

## 10. Conclusion

本論文は三つの成果を提示した。

第一に、**完成した数学**である。semantic repair presentation から `M_sem` と
semantic Čech complex を、equation system から `Q_E` と幾何側 Čech complex を
独立に構成し、SAGA presentation exactness の下で `Φ:M_sem≃Q_E`、
cochain isomorphism `κ`、`H^1` 同型、residual class 対応
`κ_*([r_sem])=[r_E]` を証明した。true sheaf 条件の下では、零類が
actual global repair の存在と同値であり、correction から corrected matching
family、sheaf amalgamation を経て global section が構成される。

第二に、**Lean 形式化の到達状況**である。中心定理の結論束(residual 対応・
零/非零同値・grounded gluing)、係数同型と cochain 比較の各段、
零・非零の有限 witness を machine-checked theorem chain として記録し、
本論文の定理との対応、仮定、axiom 状況を declaration 単位で固定した。

第三に、**one-cent realization** である。実在の microservice システムの
払い戻し三角形上で、3つの金額規約の衝突が立てる非境界 residual を観測から
導出・計測し(選択複体上、§7.6)、gate による blocking、
修理案の事前検証、repair 後の障害消滅、gate PASS までを一つの再現可能な
計算として一周した。
各 chart は自分の局所方程式を満たしていた。障害は、どの局所にも帰属しない
1セント未満のドリフトとして、ループを一周したときにだけ現れた。

抽象的な比較定理から出発した航路が、機械検証を経て、実在コードの
1セントに到達した。この 1セントは、局所的な正しさの総和が大域的な正しさに
届かないことの、最小で具体的な証人である。SAGA にとってこの到達点は
喜望峰である。すなわち、理論が現実の海へ抜ける最初の岬であり、
そこから先の海 — architecture schemes、moduli、Software Field Theory、
Rising Sea — への航路が、この比較定理によって開かれている。

---

## Acknowledgments

本研究の理論構築、Lean 形式化、tooling 実装、および本論文の執筆は、著者の指揮の
下で LLM agent(Claude、Codex)との協働により行われた。数学的主張の正しさは
Lean による機械検証が、観測供給の確率的工程は §7.5 の規律が、それぞれ artifact
として固定する。AI agent は本論文の著者ではなく、すべての結論に対する責任は
著者が負う。

---

## References

- [Abramsky–Brandenburger 2011] Samson Abramsky and Adam Brandenburger.
  The sheaf-theoretic structure of non-locality and contextuality.
  *New Journal of Physics* 13, 113036, 2011. doi:10.1088/1367-2630/13/11/113036.
- [Abramsky–Mansfield–Barbosa 2012] Samson Abramsky, Shane Mansfield, and
  Rui Soares Barbosa. The cohomology of non-locality and contextuality.
  *Electronic Proceedings in Theoretical Computer Science* 95, 1–14, 2012.
  doi:10.4204/EPTCS.95.1.
- [Allen–Garlan 1997] Robert Allen and David Garlan. A formal basis for
  architectural connection. *ACM Transactions on Software Engineering and
  Methodology* 6(3), 213–249, 1997. doi:10.1145/258077.258078.
- [Curry 2014] Justin Curry. *Sheaves, Cosheaves and Applications.*
  PhD thesis, University of Pennsylvania, 2014. arXiv:1303.3255.
- [De Silva–Balasubramaniam 2012] Lakshitha Ramesh De Silva and Dharini
  Balasubramaniam. Controlling software architecture erosion: a survey.
  *Journal of Systems and Software* 85(1), 132–151, 2012.
  doi:10.1016/j.jss.2011.07.036.
- [de Moura–Ullrich 2021] Leonardo de Moura and Sebastian Ullrich. The Lean 4
  theorem prover and programming language. In *Automated Deduction — CADE 28*,
  LNCS 12699, 625–635, 2021. doi:10.1007/978-3-030-79876-5_37.
- [Felber–Flores–Galeana 2025] Stephan Felber, Bernardo Hummes Flores, and
  Hugo Rincon Galeana. A sheaf-theoretic characterization of tasks in
  distributed systems. arXiv:2503.02556, 2025.
- [Garcia-Molina–Salem 1987] Hector Garcia-Molina and Kenneth Salem. Sagas.
  In *Proceedings of the 1987 ACM SIGMOD International Conference on
  Management of Data*, 249–259, 1987. doi:10.1145/38713.38742.
- [Garlan–Allen–Ockerbloom 1995] David Garlan, Robert Allen, and John
  Ockerbloom. Architectural mismatch: why reuse is so hard.
  *IEEE Software* 12(6), 17–26, 1995. doi:10.1109/52.469757.
- [Gibson 2026] Josh Gibson. Sheaves as a means of maintaining consistency in
  model-based systems engineering. arXiv:2605.08609, 2026.
- [Goguen 1992] Joseph Goguen. Sheaf semantics for concurrent interacting
  objects. *Mathematical Structures in Computer Science* 2(2), 159–191, 1992.
  doi:10.1017/S0960129500001420.
- [Grothendieck 2022] Alexander Grothendieck. *Récoltes et semailles:
  Réflexions et témoignage sur un passé de mathématicien.* Gallimard, Paris,
  2022(執筆 1983–1986).
- [Hansen–Ghrist 2019] Jakob Hansen and Robert Ghrist. Toward a spectral
  theory of cellular sheaves. *Journal of Applied and Computational Topology*
  3, 315–358, 2019. doi:10.1007/s41468-019-00038-7.
- [Li et al. 2022] Ruiyin Li, Peng Liang, Mohamed Soliman, and Paris Avgeriou.
  Understanding software architecture erosion: a systematic mapping study.
  *Journal of Software: Evolution and Process* 34(3), e2423, 2022.
  doi:10.1002/smr.2423.
- [mathlib Community 2020] The mathlib Community. The Lean mathematical
  library. In *Proceedings of the 9th ACM SIGPLAN International Conference on
  Certified Programs and Proofs (CPP 2020)*, 367–381, 2020.
  doi:10.1145/3372885.3373824.
- [Medvidovic–Taylor 2000] Nenad Medvidovic and Richard N. Taylor.
  A classification and comparison framework for software architecture
  description languages. *IEEE Transactions on Software Engineering* 26(1),
  70–93, 2000. doi:10.1109/32.825767.
- [Murphy–Notkin–Sullivan 1995] Gail C. Murphy, David Notkin, and Kevin
  Sullivan. Software reflexion models: bridging the gap between design and
  implementation. In *Proceedings of the 3rd ACM SIGSOFT Symposium on
  Foundations of Software Engineering (FSE 1995)*, 1995.
  doi:10.1145/222132.222136.
- [Ó Conghaile 2022] Adam Ó Conghaile. Cohomology in constraint satisfaction
  and structure isomorphism. In *47th International Symposium on Mathematical
  Foundations of Computer Science (MFCS 2022)*, LIPIcs 241, 75:1–75:16, 2022.
  doi:10.4230/LIPIcs.MFCS.2022.75.
- [Robinson 2017] Michael Robinson. Sheaves are the canonical data structure
  for sensor integration. *Information Fusion* 36, 208–224, 2017.
  doi:10.1016/j.inffus.2016.12.002.
- [Serre 1956] Jean-Pierre Serre. Géométrie algébrique et géométrie
  analytique. *Annales de l'Institut Fourier* 6, 1–42, 1956. doi:10.5802/aif.59.
- [Young 2026] Halley Young. Sheaf-cohomological program analysis: unifying
  bug finding, equivalence, and verification via Čech cohomology.
  arXiv:2603.27015, 2026.

---

## Appendix A. 仮定の帰属(どの証明が何を消費するか)

定理 5.1 の入力 1–8 を本文の証明がどこで消費するかを一覧にする。主張の内容は
本文の各節を正とし、本付録は帰属の索引である。

### A.1 comparison core(§5.3〜§5.5)

- 消費: cover intersection diagram、二つの係数 presheaf(仮定 1–2)、
  generator map と completeness 二条件(仮定 3–4)、local-state data
  (仮定 5–7。soundness の導出に使用)。
- 不使用: global sheaf condition、cover の有限列挙、displayed equation
  fulfillment。

### A.2 actual gluing(§5.6)

- 補題 5.2A が消費するのは、cover の monomorphism 性と、仮定 8 のうち
  `P_sem(V)` の subsingleton 条項である(証明が消費するのは pairwise overlap の
  分に限られる)。補題は forward 証明の corrected family 補完と、equation 側
  global 化の貼り合わせとで用いる。
- これに加えて actual gluing は (iii) の true sheaf 条件(sheaf condition と
  topology 所属)を使う。`P_sem(V)` subsingleton は true sheaf 条件の条件(4)と
  同一の命題として供給される。

### A.3 未消費条項

仮定 8 のうち `P_E(V)` の subsingleton 条項と係数消失条項
`M_sem(V)=Q_E(V)=0` は、本論文のどの証明でも消費されない。複体は §4.1 で
nonempty intersection 上のみを走り、equation 側の global 化(§5.6 末尾)が
empty overlap の処理に使うのも `P_sem` 側の subsingleton 条項(補題 5.2A)で
ある。これらの未消費条項は、入力面(仮定 8)を §4.1 の ordered Čech complex との
完全な同一視(本論文の scope 外)まで含む形で固定するために保持する。

### A.4 Lean 形式化における消費(thin site)

Lean 形式化は context category が thin な site 上で行われている(§5.7)。
thin 性、すなわち平行射の一致から、この model ではすべての射が自動的に
monomorphism であり、補題 5.2A の self-overlap と逆順 overlap の処理も平行射の
一致で自動的に済む。したがって補題 5.2A の形式化対応物
`SiteStateData.matchingFamily_iff` は、選択された pairwise overlap とその lift
データは消費するが、monomorphism を明示仮説として消費しない(pullback の
可換性と一意性は thin 性から従う)。一般の `ArchCtx(X)` 上の gluing 論証は
`unported` である(第6章)。

## Appendix B. Lean source 対応(declaration・label・source file)

第6章の status の一次証拠である Lean source の、release tag 内での構成を固定
する。SAGA theorem chain は `Formal/AG/SemanticRepair/Saga/` 以下に配置される。
kernel axiom 監査の実体は `Formal/AG/AxiomAudit.lean` の
`#assert_standard_axioms_only`(登録 declaration 全件の allowlist 検査)であり、
release CI が `lake env lean Formal/AG/AxiomAudit.lean` として実行する。

Lean source の docstring は、開発時の内部整理に由来する、本論文とは別系列の
番号(`X.定理1.1` など)を label に用いる。本論文との定理対応は第6章 status
table が完結して与え、label は Lean source を閲覧する際の照合用である。
第6章の declaration との対応は次のとおりである(label のない declaration は
「—」、source file は `Saga/` からの相対)。

| Lean declaration | Lean 側 label | Source file |
| --- | --- | --- |
| `SagaEquationPacket.sagaCentralTheorem` | X.定理1.1 | `TrueSheafDescent.lean` |
| `PrimaryStateCorrespondence.relationSound_of_stateCorrespondence` | — | `Exactness.lean` |
| `SagaEquationPacket.phiEquiv`(generic 版: `PrimaryCoefficientCorrespondence.phiEquiv`、X.定理6.3/系6.7) | 左記 | `EquationRealization.lean`、`Exactness.lean` |
| `ExactnessFixtures.soundness_failure` / `completeness_failure` / `generation_failure` | X.例6.6 | `Exactness.lean` |
| `kappa1_delta0`、`kappa2_delta1` | X.定理7.2 | `KappaComparison.lean` |
| `SagaEquationPacket.kappaStarAddEquiv`(generic 版: `kappaH1AddEquiv`、X.定理7.4) | 左記 | `KappaComparison.lean` |
| `SagaEquationPacket.residual_correspondence_class`、`betaAligned_residual` | X.定理7.5 | `KappaComparison.lean` |
| `SagaEquationPacket.globalRepair_nonempty_iff`、`sagaGroundedGluing` | X.定理8.2 | `TrueSheafDescent.lean` |
| `SiteStateData.matchingFamily_iff` | — | `OrderedComparison.lean` |
| `CircleWitness.semanticResidualClass_ne_zero`、`circle_nonzero_class_transfer` | X.例10.2/付録B.9 | `CircleWitness.lean` |
| `DescentWitness.descentTrueSheaf`、`descent_sagaGroundedGluing` | — | `DescentWitness.lean` |

§6.1 の構成部品と source file の対応:

| 構成部品(§6.1) | Source file |
| --- | --- |
| cover、intersection diagram、three-term Čech complex | `Cover.lean`、`CechThreeTerm.lean` |
| semantic repair presentation と `M_sem` | `Presentation.lean` |
| affine repair system、selected atlas、residual | `RepairTorsor.lean`、`EquationLift.lean` |
| soundness 導出、exactness、係数同型、有限反例 | `Exactness.lean` |
| equation 側 realization / production | `EquationRealization.lean`、`EquationProduction.lean` |
| cochain 比較 `κ`、`H^1` 同型、residual 対応 | `KappaComparison.lean` |
| true sheaf descent、中心定理の最終束ね | `TrueSheafDescent.lean` |
| 零・非零の有限 witness | `CircleWitness.lean`、`DescentWitness.lean` |
| poset site 実現、ordered Čech model 比較 bridge | `OrderedComparison.lean`、`PartIVBridge.lean` |

---

## 付録(草稿管理)

### A. 執筆残作業(release identity 確定と連動)

- [x] 第3章: canonical 第I〜III部からの基礎定義の自足化
- [x] 本文からの repo 参照・canonical 番号参照の撤去(Lean status 章の source path は例外。対応表は付録C=内部監査用へ退避)
- [ ] 付録C: notation 対応表(paper 記号 ↔ canonical 記号、内部監査用)の追補
- [ ] release 時: 冒頭 draft note と本付録(草稿管理)全体を除去する
- [x] 第6章: status table 確定(2026-07-26、#3757 完了後の Part X route で対応・status・assumptions を固定。axiom 監査は `AxiomAudit.lean` の allowlist 検査)。残: release tag の commit hash と CI run 参照の固定
- [x] 第6章: 未証明・未接続・未移植一覧の正確な記録(2026-07-26、§6.2 末尾)
- [x] 第7章: 導出 residual 契約(#3820–#3822)への本文同期と condition matrix 転記(2026-07-26。現節番号では §7.1/7.3/7.6)
- [ ] 第7章: deposit 相対 path、ArchSig version、実行 command、expected output の固定
- [x] 第8章: Young artifact 確認と定理番号確定(related_work.md §2.7 に記録)
- [x] References 節と BibTeX 固定(`zenodo_saga_references.bib`、P0 11点+P1 使用分+Serre/Grothendieck/Garcia-Molina–Salem)
- [ ] 第8章: 投稿時点で 2026 年文献の最新版と publication status を再確認
- [ ] 英語版への翻訳(最終投稿言語=英語、2026-07-24 決定。References は英語で作成済み)
- [ ] 全章: claim-to-evidence matrix の構築と各 claim の一次証拠への対応
- [ ] SAGA comparison の可換図と one-cent の計算図の作成
- [x] 著者情報の固定(author block: Hiroyuki Nakahata / Independent Researcher / ORCID 0009-0008-5928-0234、所属企業は disclaimer で開示。Acknowledgments に AI 協働開示、2026-07-24)
- [ ] Zenodo metadata: license(CC BY 4.0 想定、要決定)と DOI の固定。creators は author block と一致させる

### B. Claim-to-evidence matrix(skeleton)

| Claim type | 論文の箇所 | 必要な一次証拠 | 状態 |
| --- | --- | --- | --- |
| Mathematics | 第4〜5章 | canonical math source(第X部)、theorem map(付録C) | 対応表あり、notation 表 TODO |
| Lean | 第6章 | declaration、source、focused check、axiom audit | 対応表確定、release tag / CI run 固定 TODO |
| Measurement | 第7.3節 | packet、manifest、digest | 正本 report あり、deposit path TODO |
| Empirical | 第7.2節 | repository、commit `313886e99bef`、source reference、input | 正本 report あり |
| Empirical(供給工程) | 第7.5節 | archmap-creater SKILL、scope manifest、調停記録、audit、run のモデル記録 | 正本 report あり、deposit 同梱範囲 TODO |

### C. Canonical 対応表(内部監査用。release 時に本付録ごと除去)

本文は self-contained であり、読者はこの表を必要としない。以下は執筆・監査時に
paper とリポジトリ内 canonical 数学本文(日本語)の対応を検証するための内部資料である。

基礎定義(第3章):

| paper | canonical | 内容 |
| --- | --- | --- |
| 定義 3.1 | 第I部 定義 1.1 | Atom |
| 定義 3.2 | 第I部 定義 3.1、3.2 | Atom family、support |
| 定義 3.3 | 第I部 定義 4.1、5.1、命題 5.3 | configuration、architecture object、Atom-origin |
| 定義 3.4 | 第II部 定義 3.1 | architecture context |
| 定義 3.5 | 第II部 定義 4.1、仮定 4.3、命題 4.2 | context category、overlap、finite-meet poset model |
| 定義 3.6 | 第I部 定義 7.1〜7.3 | equation system、fulfillment |
| 定義 3.7 | 第II部 定義 6.1、7.1、8.1 | coverage、AAT topology、AAT site |
| 定義 3.8 | 第II部 定義 9.1、10.1 | presheaf、sheaf condition |
| 定義 3.9 | 第III部 定義 5.2、6.1、6.2 | witness ideal、obstruction ideal |
| 定理 3.10 | 第III部 定義 11.3、定理 11.4 | displayed source、generated `Q_E` |

注: 論文 定理 3.10 条項5(旧条項4、2026-07-26 #3813 の residual restriction
naturality 条項挿入で繰り下げ)の名称は quotient zero criterion(#3781 項目8で
改名)。canonical 定理 11.4 の対応 clause は faithfulness / nondegeneracy の
ままであり、canonical 側は追随改名しない(2026-07-24 裁定)。名称の相違は
この注記が恒久的に対応づける。条項3(residual restriction naturality)は
canonical 定理 11.4 の同名条項に対応する(2026-07-26 #3813 で追補)。

構成と定理(第4〜5章):

| paper | canonical(第X部) | 内容 |
| --- | --- | --- |
| §4.1 | 定義 2.1、補題 2.2、定義 2.3、補題 2.1A | cover-relative Čech complex |
| §4.2 | 定義 3.1〜3.4、定義 4.1、4.2、補題 4.3、定理 4.4、系 4.5 | semantic 側の構成 |
| §4.3 | 定義 5.1〜5.3、補題 5.4 | equation 側の構成 |
| 命題 4.1(§4.3) | 定義 6.1、命題 6.1A | equation semantic realization(`χ^E` の構成) |
| 定理 5.1 | 定理 1.1 | SAGA 中心定理 |
| §5.3 | 補題 6.2A、定理 6.3、系 6.7、例 6.6 | 係数同型 `Φ` |
| §5.4 | 定義 7.1、定理 7.2、系 7.3、定理 7.4 | cochain 可換と `H¹` 同型 |
| §5.5 | 定理 7.5、定理 7.6 | residual 対応と統合 |
| 定理 5.2(§5.6) | 定義 8.1、系 4.5、補題 2.1A、定理 8.2、系 8.3 | Grounded Global Gluing |
| 補題 5.2A(§5.6) | 補題 2.1A(matching family clause のみ) | ordered matching completion |
| §5.7 | 原則 8.4 | additive/torsor/higher の分離 |
| 例 5.3(§5.8) | 例 10.2 | 非零類の有限 witness |

注: 論文 §5.6 の true semantic repair sheaf 定義は canonical 定義 8.1 と同一の
4条件である(2026-07-26 の記述整合対応 #3814 で、canonical に対応物のない
旧条件(5)と `P_sem^𝒰` 定義域分離を除去して統一)。Lean 側は担体
(`AffineSemanticRepairSystem.State`)が最初から site 全域である一方、torsor
三条件は `IsIntersectionCtx` ガードにより cover intersection 上でのみ仮定される。
`P_E` 側も同構造(`AffineCoefficientLiftSystem`、作用は intersection 上)。
仮定 7 の `β` の Lean 対応物は intersection diagram 上の成分と base 水準の
`betaW`(chart 整合仮説つき)に分かれる。

注: 論文 §4.2 の projection `π_V:Λ(V)→At` は、canonical 定義 3.1 の
occurrence 値 projection `π_V:Λ(V)→At(V)` を台 Atom へ圧縮した形である
(2026-07-26 #3813)。Lean は occurrence 水準を保持する
(`SemanticAtomData.projection` / `projection_natural` +
`AtomOccurrenceReading.occRestrict_atom`)。命題 4.1 の Lean
対応物は `EquationSemanticRealization.chiE` / `chiE_natural` である。
