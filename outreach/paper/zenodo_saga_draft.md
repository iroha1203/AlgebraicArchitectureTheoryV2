# SAGA: A Comparison Theorem for Local-to-Global Software Architecture

*From Semantic Repair Cohomology to Algebraic-Geometric Descent*

> **draft note**: 本ファイルは Zenodo プレプリントの初稿下書きである。要件と完了条件は
> [zenodo_saga.md](zenodo_saga.md)、Related Work の原典調査は
> [zenodo_saga_related_work.md](zenodo_saga_related_work.md) を正とする。
> 本文中の `TODO:` は release identity 確定時に固定する箇所を示す。

---

## 要旨

software architecture の局所的な整合性と大域的な整合性の間には、構造的な隔たりがある。
本論文は、この隔たりを測る二つのコホモロジーを独立に構成し、両者の一致を証明する。

第一の構成は、semantic atom、repair support、局所 repair relation から
semantic repair coefficient `M_sem` と semantic Čech complex を生成する。
第二の構成は、Atom-indexed architectural equation system `E` から
equation-generated coefficient `Q_E` と幾何側 Čech complex を生成する。
monomorphic AAT cover `𝒰` 上で、二つの affine local-state system、
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
proof chain を declaration 単位で数学本文と対応させる。第三層は measurement system
ArchSig による有限 realization であり、実在するオープンソース microservice architecture 上で
非零 residual class の計測、gate による blocking、repair 案の事前検証、
repair 後の障害消滅の記録までを再現可能な一つの計算として示す。
数学、Lean、measurement は同じ release identity を参照し、各 claim から一次証拠へ
到達できる provenance を構成する。

---

## 1. Introduction

### 1.1 Local-to-global architecture problem

software architecture の各構成要素は、それぞれの局所的な文脈で整合的に設計される。
一つの service は自身のデータ規約を守り、一つのモジュール間の受け渡しは
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
proof chain を declaration 単位で示し、数学本文との対応と axiom 状況を固定する(第6章)。

ArchSig 面は有限 case study である。固定した microservice architecture を対象に、
数学的対象が有限 architecture evidence からどのように計算され、repair 前後で
どのように変化するかを再現可能な形で示す(第7章)。

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
Tor conflict、singularity として構造化される。diagnosis と repair は、
同じ幾何対象の変化として読める。修理とは類を消す操作であり、
修理の成否は類の零性として判定される。

### 2.5 ringed geometry と道具の接続

architecture 上に ringed geometry を構成することで、scheme、derived intersection、
deformation、monodromy、stack、base change といった代数幾何の道具が
architecture 上で働く。本論文の SAGA はこの一部、すなわち Čech `H^1` と
descent を使う。より深い道具の使用は第9章の研究展望で述べる。

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
完結する形で定義する。正本は AAT 数学本文(`docs/aat/algebraic_geometric_theory/`
第I〜III部)であり、本章末の表が paper 定義と canonical 定義の対応を固定する。

### 3.1 Atom と Atom family

**定義 3.1(Atom)。** Atom とは、次の形の型付き事実である。

```text
a = (kind, axis, subject, predicate, payload)
```

`predicate` は `subject` に対して一つの atomic statement を与える。Atom は
特定の言語や framework に属さない primitive architectural fact であり、
AAT の内部では生成元として扱われる。core family の schema には
`component(c)`、`relation_r(c,d)`、`state(c,x)`、`contract(m,p)`、
`semantic(t,s)`、`runtime_interaction(u,v,h)` などがある。

**定義 3.2(Atom family と support)。** Atom universe を `At` と書く。
Atom family `F` は `At` の部分集合であり、`support(F)` は `F` に現れる
subject の集合である。`F` は component、relation、state、contract、effect、
semantic Atom を混在して含みうる。この混在は排除されず、混在した
primitive fact がどの equation を満たしどの obstruction を生むかが問いになる。

### 3.2 Architecture object

**定義 3.3(architecture object)。** Atom configuration `C=(F,R,E)`
(Atom family、関係づけ、配置)に structure maps `S`(graph、category、
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
任意の二つの context の間に高々一つの readable morphism がある equivalence
quotient の下で、`ArchCtx_min(X)` は finite-meet poset category になり、
overlap は meet として計算される(canonical 第II部 命題 4.2)。この model の
射はすべて monomorphism である(第3.7節がこの事実を cover 仮定へ接続する)。
第7章の有限計算はこの regime の実行形である。

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
signature `Sig`、coverage requirements `R`、context-overlap package `Ov` に対して、
`(E,R,Ov)`-admissible な coverage family `{W_i→W}`(required Atom support、
required equation-coordinate support、selected witness support、required axes、
interaction overlap が cover 全体で読める族)が生成する Grothendieck topology を
`J_{E,R,Ov}` と書く。AAT site は package

```text
Site_AAT(X,E,Sig,R,Ov) = (ArchCtx(X), E, Sig, R, Ov, J_{E,R,Ov})
```

である。本論文では、この package を固定した underlying site を `S_X` と略記し、
`W` をその context とする。cover は Atom を生成しない(non-generation)。

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

**定理 3.10(generated obstruction quotient; canonical 第III部 定理 11.4)。**
equation system `E` と displayed equation source(各 chart に対する local
context、architecture object、required index `i_q`、support Atom `a_q` の選択)を
固定する。このとき次が成立する。

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
3. **vanishing**: displayed equations が充足されるならば、すべての `q` で
   `[d_q]=0`。
4. **faithfulness と nondegeneracy**: `[d_q]=0 ⟺ d_q∈I_Ob^E(W_q)`。
   したがって `d_q∉I_Ob^E(W_q)` ならば `[d_q]≠0`。

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

と書く。空の pullback は intersection の対象から除き、その値は
empty-overlap normalization(第5章 定理 5.1 の条件 8)で固定する。
比較 core 自体に有限性は不要だが、有限 cover は中心定理、finite witness、
実行可能な realization を同じ記号で扱うために固定する。第3.3節の
finite-meet poset model ではすべての射が monomorphism なので、この仮定は
自動的に満たされる。一般の `ArchCtx(X)` では定理の明示仮定である。

### 3.8 基礎定義の対応表

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

### 3.9 Selected、generated、proved の区別

SAGA では、入力、構成、帰結を厳密に区別する。

| 種類 | 内容 |
| --- | --- |
| selected | monomorphic AAT cover、empty-overlap normalization、semantic atom system、repair support、local repair relation、repair-relation completeness、equation-generator completeness、local repair atlas、equation system `E`、local equation-lift atlas、Atom/equation interpretation、local-state interpretation `β`、global gluing に用いる true sheaf 条件 |
| generated | `M_sem`、`Q_E`、二つの Čech complex、`r_sem`、`r_E`、係数写像 `Φ`、cochain map `κ` |
| proved | repair-relation soundness、SAGA presentation exactness、`Φ` の同型性、微分可換性、cocycle / coboundary 保存、`H^1` 同型、residual class 対応、零類と actual global repair の同値 |

この区別は、数学的な相対性を保ちながら結論の provenance を固定する。
selected は入力契約であり、proved はその契約の下での定理である。

---

## 4. Semantic Repair and Equation-Generated Geometry

本章は、SAGA の二つの複体を独立に構成する。semantic 側は semantic atom と
repair relation から、equation 側は equation system から、それぞれの一次データのみで
係数、複体、residual を生成する。両者の比較は第5章の定理の結論であり、
本章の構成には他方への参照が入らない。

### 4.1 Cover-relative Čech complex

`F` を `S_X` 上の可換群値 presheaf とする。`𝒰` に相対的な三項 cochain complex

```math
C^0(\mathcal U,F)
\xrightarrow{\ \delta^0\ }
C^1(\mathcal U,F)
\xrightarrow{\ \delta^1\ }
C^2(\mathcal U,F)
```

を、ordered index 上の standard Čech differential で定義する(canonical text
第X部 定義 2.1)。`δ¹δ⁰=0` が成立し(第X部 補題 2.2)、cover-relative `H^1` を

```math
\check H^1(\mathcal U,F)=\ker\delta^1/\operatorname{im}\delta^0
```

で定義する(第X部 定義 2.3)。monomorphic cover に対しては、第X部 補題 2.1A の
normalization が ordered Čech model と第IV部の Čech cohomology を同一視する。

### 4.2 Semantic 側の構成

**semantic repair presentation**(第X部 定義 3.1)は、semantic atom、semantic
projection、repair support、restriction-stable な局所 repair relation からなる。
この presentation から **semantic coefficient** `M_sem`(第X部 定義 3.2)が生成され、
`M_sem` は可換群値 presheaf を構成する(第X部 命題 3.3)。`M_sem` を係数とする
**semantic repair complex** `C^•_sem(𝒰)`(第X部 定義 3.4)が semantic 側の複体である。

**affine semantic repair system** `P_sem`(第X部 定義 4.1)は、repair words の作用から
additive torsor structure を導く局所状態系である。selected local repair atlas
`{p_i}` を選ぶと、overlap 上の差

```math
r_{\mathrm{sem},ij}=p_j|_{U_{ij}}-p_i|_{U_{ij}}
```

が **semantic residual** `r_sem` を定める(第X部 定義 4.2)。`r_sem` は cocycle であり
(第X部 補題 4.3)、その class `[r_sem]∈H^1_sem(𝒰)` は atlas の選び方に依存しない
(第X部 定理 4.4 Choice independence)。零類は matching correction の存在と
同値である(第X部 系 4.5)。

### 4.3 Equation 側の構成

equation 側は、定理 3.10 の `Q_E` を係数とする **geometric Čech complex**
`C^•_E(𝒰)`(第X部 定義 5.2)を構成する。`Q_E` が作用する equation-lift system
`P_E` と selected local lift atlas `{e_i}` から、overlap 上の差として幾何側 residual

```math
r_{E,ij}=e_j|_{U_{ij}}-e_i|_{U_{ij}}
```

が生成される(第X部 定義 5.3)。`r_E` は cocycle であり、その class は atlas の
選択に依存しない(第X部 補題 5.4)。

### 4.4 二つの構成の独立性

semantic 側の `M_sem`、`C_sem`、`r_sem` は semantic presentation のみから、
equation 側の `Q_E`、`C_E`、`r_E` は equation system のみから構成された。
二つの複体は同じ AAT cover 上に置かれるが、係数、local state、residual は
それぞれの一次データに由来する。したがって、次章の比較写像の存在、同型性、
微分可換性、residual class の対応は、構成の反復ではなく定理の結論である。

---

## 5. The SAGA Comparison Theorem

本章は SAGA の中心定理を述べ、その証明の構造を示す。証明の完全な記述は
canonical text 第X部にあり、本章は論文内で追跡可能な形で主要な段を提示する。

### 5.1 中心定理

**定理 5.1(SAGA 中心定理; canonical 第X部 定理 1.1)。**
monomorphic AAT cover `𝒰` 上で次を固定する。

1. semantic atom、projection、repair support、restriction-stable な局所 repair
   relation から生成される可換群値 presheaf `M_sem`。
2. architectural equation system `E` から生成される可換群値 presheaf `Q_E`。
3. supported semantic atom を displayed Atom/equation residual class へ送る
   restriction-natural な一次写像。
4. その写像についての局所 repair relation の completeness と
   equation generator completeness(cover intersection ごとに確認する)。
5. repair words の作用から additive torsor structure を導く affine semantic
   repair system `P_sem` と、その selected local repair atlas。
6. `Q_E` が作用する equation-lift system `P_E` と、その selected local lift atlas。
7. semantic local states を equation local lifts へ送る restriction-natural かつ
   generator-equivariant な一次写像 `β:P_sem→P_E`。
8. 積から除いた各 empty cover intersection `V` に対する
   `M_sem(V)=Q_E(V)=0` と、`P_sem(V)`、`P_E(V)` の subsingleton 性
   (empty-overlap normalization)。

このとき一次写像は cover intersection diagram 上の自然同型

```math
\Phi:M_{\mathrm{sem}}\xrightarrow{\sim}Q_E
```

を誘導する。`M_sem` と `Q_E` から別々に作った Čech complex の間には
degreewise cochain isomorphism

```math
\kappa^\bullet:
C^\bullet_{\mathrm{sem}}(\mathcal U)
\xrightarrow{\sim}
C^\bullet_E(\mathcal U)
```

が構成され、`κ` は微分と可換する。したがって

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
residual の対応は、二つの local atlas を一次対応そのもので選んだ場合には
cochain 水準で `κ¹(r_sem)=r_E` として成立する。独立に選んだ場合にも、
両 cochain の差は明示的な `δ⁰`-像であり、class の等式が成立する。

さらに semantic repair object が AAT topology 上の true sheaf であり、
`𝒰` がその topology の cover ならば、

```math
\mathrm{Nonempty}\,P_{\mathrm{sem}}(W)
\iff
[r_{\mathrm{sem}}]=0
\iff
[r_E]=0.
```

### 5.2 証明の構造

証明は次の段で構成される。各段は canonical text 第X部の番号へ対応する。

| 段 | 内容 | canonical |
| --- | --- | --- |
| 係数同型 | relation soundness(第X部 補題 6.2A で導出)、SAGA presentation exactness、`Φ:M_sem≃Q_E` | 定理 6.3 |
| cochain 可換 | degreewise `κ` の構成と `κδ=δκ` | 定義 7.1、定理 7.2 |
| cocycle/coboundary 保存 | `κ` による `Z^1`、`B^1` の保存と反映 | 系 7.3 |
| `H^1` 同型 | `κ_*` の誘導 | 定理 7.4 |
| residual 対応 | `κ_*([r_sem])=[r_E]` | 定理 7.5 |
| 統合 | 上記全体の束ね | 定理 7.6 SAGA 比較定理 |
| global repair | true sheaf 条件下の三項同値と actual gluing | 定理 8.2 |

soundness が仮定ではなく第X部 補題 6.2A の帰結である点は、この定理の構成上の
要である。local-state data(仮定 5–7)から primary state interpretation が
soundness を生成し、それが presentation exactness(第X部 定理 6.3)を成立させる。

comparison core(第X部 定理 7.2–7.6)が使うのは、cover intersection、二つの係数
presheaf、generator/relation exactness、restriction naturality である。
global sheaf condition、cover の有限列挙、displayed equation fulfillment は
comparison core の仮定に含まれない。monomorphism と empty-overlap normalization は
ordered Čech model との同一視と actual gluing で使用する。

### 5.3 Global repair: Grounded Global Gluing

**定理 5.2(canonical 第X部 定理 8.2)。** 定理 5.1 の設定に加え、`P_sem` が
true semantic repair sheaf(canonical 定義 8.1)ならば、三項同値が成立する。
さらに `[r_sem]=0` の証明から得る correction `a` に対して、corrected family

```math
p_i^{\mathrm{corr}}=(-a_i)+p_i
```

を restriction として持つ global section が一意に存在する。

証明は、零類から correction を取り、corrected family が全 ordered overlap 上の
matching family であることを monomorphism と normalization で確認し、
sheaf amalgamation で一意な global section を得る。逆向きは torsor の
freeness と transitivity から `r_sem` が coboundary であることを導く。

ここで一意なのは固定した corrected matching family の amalgamation であり、
`P_sem(W)` 全体の一意性ではない。異なる global repair の差は degree-zero data が担う。

equation 側にも同じ結論が降りる。SAGA presentation exactness と primary state
correspondence が `S_X` 上で成立し、`P_E` も選ばれた topology 上の sheaf であれば、
`β_W:P_sem(W)→P_E(W)` は全単射であり、
`Nonempty P_E(W) ⟺ [r_E]=0` が従う(第X部 系 8.3)。

### 5.4 定理の適用範囲

本比較定理は可換群値 presheaf の additive theorem である(canonical 原則 8.4)。
nonabelian torsor の pointed-set-valued `H^1`、2-cocycle と gerbe による
higher coherence、stack の descent は、それぞれ独立の statement を要する。
additive `H^1` comparison からこれらの結論は導かない。

### 5.5 有限 witness: independently generated circle comparison

**例 5.3(canonical 第X部 例 10.2)。** 四つの chart と四つの nonempty overlap
`U_01, U_12, U_23, U_30` を持ち、nondegenerate triple overlap を持たない
monomorphic 4-cycle cover を取る。各 nonempty intersection `V` で
semantic support を一 generator `σ_V`、local repair relation を `2σ_V=0` とすると、
semantic 側は独立に

```math
M_{\mathrm{sem}}(V)=\mathbb Z[\sigma_V]/(2\sigma_V)\cong\mathbb F_2
```

を生成する。equation 側では `O_E(V)=ℤ`、`I_Ob^E(V)=(2)` から `Q_E(V)=ℤ/(2)` を得る。
interpretation `χ_V(σ_V)=[1]` は soundness、completeness、generation を満たし、
第X部 定理 6.3 が `M_sem≃Q_E` を構成する。これは一方の complex の transport ではなく、
semantic presentation `ℤ[σ]/(2σ)` と equation quotient `ℤ/(2)` の
presentation comparison である。

transition `(t_01,t_12,t_23,t_30)=(1,0,0,0)` を持つ local state system で
各 chart の local state を `0` に選ぶと、residual は

```math
r_{\mathrm{sem}}=(1,0,0,0)\in\mathbb F_2^4
```

である。4-cycle 上の任意の `δ⁰`-像は oriented edge sum が零だが、`r_sem` の
edge sum は `1` である。したがって

```math
[r_{\mathrm{sem}}]\ne0,\qquad
[r_E]\ne0,\qquad
\kappa_*([r_{\mathrm{sem}}])=[r_E].
```

この例は、SAGA 比較が零類だけでなく非零類も保存することの有限 witness であり、
第7章の実コード計測の数学的雛形である。「閉ループ上の奇パリティ + 面なし」という
構造が非零 `H^1` を立てる。この構造が実在 architecture に現れることを第7章で示す。

### 5.6 Paper theorem と canonical theorem の対応

| paper | canonical(第X部) | 内容 |
| --- | --- | --- |
| 定理 5.1 | 定理 1.1 | SAGA 中心定理 |
| 表 5.2 の各段 | 定理 6.3、7.2、7.4、7.5、7.6 | 証明の主要段 |
| 定理 5.2 | 定理 8.2、系 8.3 | Grounded Global Gluing |
| 例 5.3 | 例 10.2 | 非零類の有限 witness |

**TODO:** notation 対応表(paper 記号 ↔ canonical 記号)を付録に固定する。

---

## 6. Lean Formalization Status

Lean 形式化は、SAGA 数学の machine-checked definitions、theorems、witnesses、
proof chain を記録する。本章は release 時点の形式化 status を declaration 単位で
報告する。status の正本は release tag の `Formal/AG/` source、axiom 状況の正本は
`Formal/AG/AxiomAudit.lean`、検証の正本は release CI の focused check と監査結果である。

### 6.1 形式化の範囲

release 時点で、SAGA theorem chain の主要構成は `Formal/AG/SemanticRepair/` 以下に
形式化されている。

- additive `H^1`(cocycle、cohomologous、quotient、residual class): `AdditiveH1.lean`
- cover-relative Čech complex と cochain realization: `SiteCech.lean`、`GluingComplex.lean`
- quotient-level `H^1` comparison: `H1Comparison.lean`
- equation-generated realization: `LawEquationGeneratedPair.lean`
- SAGA 統合 packet(descent、`H^1` comparison、grounded gluing): `SagaComparison.lean`
- 零・非零の有限 witness: `Examples.lean`

### 6.2 Status table

status vocabulary は `docs/aat/guideline.md` に従う
(`proved` / `defined only` / `future proof obligation` / `empirical hypothesis` /
`unported (Research-proved)`)。

| Mathematical claim | Lean declaration | Status | Assumptions | Source | Evidence |
| --- | --- | --- | --- | --- | --- |
| true sheaf descent と `H^1` comparison の conclusion bundle(paper 定理 5.2 の候補対応) | `trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package` | **TODO** | **TODO** | `Formal/AG/SemanticRepair/SagaComparison.lean` | **TODO: release CI run** |
| equation-generated comparison packet(paper 定理 5.1 の候補対応) | `lawEquation_constructs_groundedComparisonPacket` | **TODO** | **TODO** | `Formal/AG/SemanticRepair/SagaComparison.lean` | **TODO** |
| displayed equation 充足からの degree-zero zero reading | `displayedRequiredLawsHoldOn_constructs_generatedSourceC0_zeroPackage` | **TODO** | **TODO** | `Formal/AG/SemanticRepair/SagaComparison.lean` | **TODO** |
| 非零 obstruction の有限 witness | `selectedVisibleLocalWitness_obstructionNonzero` | **TODO** | **TODO** | `Formal/AG/SemanticRepair/Examples.lean` | **TODO** |
| quotient-level `H^1` comparison(paper 定理 5.1 の `H^1` 同型の候補対応) | `toH1Comparison` ほか | **TODO** | **TODO** | `Formal/AG/SemanticRepair/H1Comparison.lean` | **TODO** |

Lean source の docstring は `X.定理7.3`、`X.例3.6` のような Lean 側 label を
用いており、この番号系列は本論文・canonical 第X部の定理番号と一致しない。
本表の「候補対応」は declaration の statement 実読に基づく現時点の対応仮説であり、
番号の混用は行わない。

**TODO:** release tag 確定後に、(1) 各行の対応を statement 実読で確定し
paper theorem 番号で揃える、(2) 各 declaration の status、実際に使用する仮定、
`#print axioms` の結果を固定する、(3) 例 5.3(4-cycle witness)に対応する
declaration の有無を確認する、(4) 未証明・未接続・未移植の一覧を本表の下へ
正確に記録する。

### 6.3 形式化の到達地点の読み方

Lean claim は、statement の強さと proof-use によって記述する。
declaration が形式化しているのは、数学本文の定理そのものではなく、
その定理の selected 入力を Lean の structure として固定した上での結論である。
paper claim と declaration の対応表は、読者が「何がどの強さで機械検証されているか」を
数学本文と直接照合できる状態にするためにある。

数学本文に対して残る未証明、未接続、未移植は本章の status table が一元管理する。
それらは第9章の研究展望とは区別され、形式化の現在地として記録される。

---

## 7. ArchSig: Executable SAGA Diagnosis

ArchSig は、ArchMap、LawPolicy、MeasurementProfile から residual、class、
comparison、gate を計算する measurement system である。本章は前半で ArchSig の
入力、その供給工程、計算、出力を定義し、後半で実在 microservice architecture に
対する SAGA フル診断を一つの計算として示す。

### 7.1 入力契約

ArchSig の入力は次の artifact である。

- **ArchMap**: 対象システムの Atom 観測。chart(局所文脈)、section value、
  overlap の対応を記録する。
- **LawPolicy**(artifact 名): 使用する Atom vocabulary と selected equation
  reading を固定する。
- **law surface**(artifact 名): 診断に用いる equation surface の族
  (closed-equational、SAGA-grounded、descent)。
- **MeasurementProfile**: measurement の条件を固定する。
- **repair plan**: cover、overlap、residual 変数の supply を記録する。

ArchSig は与えられた入力 contract から語れる diagnostic conclusion を計算する。
結論の相対性は入力契約に由来する帰結である。

### 7.2 入力の供給: agent SKILL による観測の再現性

ArchMap の供給は、source の使われ方を読む意味読解を含む。この読解は
確率的な過程であり、決定論的な計算では置き換えられない。本研究は、
この段を隠さずに工程として固定する。すなわち、ArchMap の作成を
AI agent が実行する **authoring SKILL**(`archmap-creater`)として定義し、
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

### 7.3 計算と出力

ArchSig の `analyze` は、chart ごとの grounding(各 chart の局所方程式の充足)、overlap 上の
residual、`B^1` membership、`H^1` class、semantic residual と equation-generated
residual の comparison(h1-transfer)を計算し、measurement packet として出力する。
`compare` は二つの run の packet を突き合わせ、障害の変化を記録する。
`gate` は packet と gate policy から `PASS_WITHIN_GATE_POLICY` /
`BLOCKED_BY_GATE_POLICY` の判定を返す。

この計算は第5章の有限 realization(canonical 定義 10.1 の presentation matrix)を
実行形にしたものである。有限 semantic vocabulary、有限 relation list、有限 cover の
下で、exactness 条件と residual class は行列計算に落ちる。

### 7.4 実コード事例: one-cent obstruction

ここで本論文の case study を明かす。対象は、microservice benchmark として広く
使われるオープンソースの列車予約システム train-ticket
(commit `313886e99bef`、42 services)である。

このシステムの cancel–inside-payment–order の実呼び出し三角形上で、
払い戻し金額の規約が3流儀とも異なる。いずれも実ソースで確認され、
ArchMap の sectionValue として観測された。

- **cancel**: `Double.parseDouble(order.getPrice()) * 0.8` を
  `DecimalFormat("0.00")` で丸めて文字列化(浮動小数点 + 丸め)
- **inside-payment**: `new BigDecimal(order.getPrice())` の正確算術
- **order**: `private String price` の素通し保管

三つの service の金額表現は、実装上はいずれも `string` を介して受け渡される。
型の一致は成立している。異なるのは、その `string` が表す金額の丸め、scale、
計算、保存の**意味規約**である。さらに、3サービスの金額を同時に照合する箇所が
コード上に存在しない。すなわち triple overlap が正直に空である。

これは例 5.3 の構造そのものである。閉ループ上の奇パリティ(3流儀の衝突)と
面なし(triple overlap の不在)が、非零 `F_2` residual class を立てる。
払い戻し計算 `0.8 × 価格` の丸め剰余 — **1セント未満のドリフト** — は、
どの chart にも記帳されていない。この case study を **one-cent obstruction** と呼ぶ。

### 7.5 診断階段

measurement の入力構成は次のとおりである。cover は 6 chart(診断三角形 {cancel,
inside-payment, order} + 託送料金領域 {preserve, consign, consign-price})、
law surface は closed-equational、SAGA-grounded、descent の3本、
repair plan は overlap 6(三角形3 + 託送3)であり、residual 変数
`drift:refund-rounding` を三角形3辺へ supply する。repaired 変種は、
三角形の 3 chart を BigDecimal scale-2 HALF_EVEN 統一規約に置換した仮修理 ArchMap である。

診断階段の結果は次である。

| 幕 | 結果 |
| --- | --- |
| head analyze | `MEASURED_NONGLUING_RESIDUAL_CLASS`(`run:7a94d68ac5d7`) |
| └ grounding | `measured_zero` — 各 chart は自分の局所方程式を満たしている |
| └ descent 残差類 | `measured_nonzero`(inB1: false、三角形3辺 support) |
| └ comparison h1-transfer | `established` |
| gate head | `BLOCKED_BY_GATE_POLICY` |
| repaired analyze | `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`(`run:1f657023d7e8`) |
| compare head→repaired | `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE` |
| gate repaired | `PASS_WITHIN_GATE_POLICY` |

### 7.6 計測が示したこと

**局所整合・大域非貼合の実在。** grounding の `measured_zero` は、各 chart が
自分の局所方程式を満たしていることを計測として言う。cancel は cancel の丸め規約に、
inside-payment は正確算術に、order は素通し保管に、それぞれ忠実である。
ペアごとの受け渡しも各々は成立している。障害はループを一周したときだけ現れ、
それを埋める面(triple)がコードに存在しないから、類として残る。
「局所的には整合、大域的に貼り合わない」という SAGA の中心構造が、
作為的に仕込んだのではない実在 OSS 上で観測された。

**診断階段の全段が実データで機能。** 非零類の計測、gate による blocking、
修理計画の事前検証、compare による障害消滅の記録、gate PASS まで、
一貫した artifact 契約の下で一周した。

**数学的規律の実効。** ドリフトの立つ三角形自体を triple として申告すると
cocycle 条件で拒否される。これは数学的に正当な拒否である。典拠のない
residual ref は fail した。実データで負荷をかけて規律が守られた。

**沈黙の実行。** runtime 実測数値を要する計測軸(harmonic-debt)は、
実測が無い状態では供給されず、沈黙として扱われた。

### 7.7 主張の境界

本 case study の claim は次の範囲に限る。SAGA residual の supply
(三角形3辺への `drift:refund-rounding`)は実施者が書いた authored model であり、
規約 mismatch の検出自体は closed-equational surface の段が担った。SAGA 段が
加えたのは、grounding の罠の明示、修理計画の事前検証、h1-transfer、gate の
一貫した診断である。repaired は section を書き換えた仮修理 ArchMap であり、
`PASS_WITHIN_GATE_POLICY` が示すのは「この修理案なら貼り合う」という
事前検証の機構である。ドリフトの発生頻度と金額規模は runtime 実測を要するため
本論文では計測していない。広い benchmark 評価と一般的な検出性能は、
別の実証研究として扱う。

供給工程の SKILL 化の適用範囲も明示する。§7.2 の authoring SKILL が覆うのは
ArchMap の供給である。SAGA 段の追加 artifact(law surface、repair plan、
repaired 変種)は、本実験時点では builder script と authored model として
供給されており、同水準の SKILL 化は供給工程の整備課題として残る。
本実験の builder script と供給所見は、その設計素材として記録されている。

### 7.8 再現

すべての入力 artifact、一次出力、builder script は再現 bundle に収録する。
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
中へ位置づける。原典調査は [zenodo_saga_related_work.md](zenodo_saga_related_work.md)
を正とする。

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

global-section obstruction の系譜として、Abramsky–Brandenburger の sheaf-theoretic
contextuality [2011] と、その Čech cohomology による非消滅障害 [Abramsky–
Mansfield–Barbosa 2012] を基礎文献に置く。computable obstruction の先行例として、
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
cellular sheaf と有限計算の基礎 [Curry 2014; Robinson 2017; Hansen–Ghrist 2019] は
一段落で参照し、software architecture 固有の比較は Young、Gibson、Felber へ集中させる。

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
semantic repair descent、additive `H^1`、cover-relative Čech complex、
cochain realization、quotient-level `H^1` comparison、零・非零の有限 witness、
equation-generated realization を一つの machine-checked theorem chain として
構成した点にある。Young と Gibson の形式化との比較は、theorem chain の範囲と
executable measurement への接続で行う。

### 8.5 Synthesis

先行研究は、sheaf を global consistency の言語として、cohomology を計算可能な
obstruction として、formal architecture model を conformance 分析の基盤として
確立してきた。SAGA はこれらの系譜に、software architecture のための
equation-generated AAT Čech complex を構成し、その first cohomology が独立に
定義された semantic-repair obstruction と一致することの証明を加える。
Lean が比較を検証し、ArchSig がその有限 architectural instance を評価する。

Young の引用は次の規律で書く(調査結果は related_work.md §2.7 が正本)。
定理番号は公開版で確認済みである(Definition 3.5 semantic presheaf、Theorem 5.1
bugs as gluing obstructions、Theorem 5.3 descent for equivalence、Theorem 6.3
Mayer–Vietoris ほか)。Lean 形式化(1,259 lines)、375 benchmarks、evaluation 数値は
論文が報告する結果として引用し、独立検証済みの事実としては書かない。
Deppy の code artifact は論文・出版社ページのいずれからもリンクされていないため、
source-level comparison は本文に含めない。

**TODO:** P0 文献 11 点の BibTeX 固定。投稿時点で 2026 年文献の最新版と
publication status を再確認する。

---

## 9. Discussion and Research Outlook

SAGA 比較定理は、AAT の local-to-global 能力の最初の完成した定理であり、
より大きな研究 program の最初の縦断でもある。本章は、この定理が確定させたものを
議論し(§9.1)、そこから開く研究方向を示す(§9.2〜9.6)。本章の §9.2 以降は
研究展望であり、証明済みの成果と混同しない。各方向の定理開発、Lean 実装計画、
tooling roadmap はそれぞれの正本で管理する。

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
帰結である。第7章の repair 前後比較は、この帰結の最初の有限実例である。
selected な入力契約(cover、equation system、witness)への相対性は、この主張の制約であると
同時に、主張の provenance を固定する規律でもある。

### 9.2 方法としての Rising Sea

本研究 program の方法は、Grothendieck が *la mer qui monte*(rising sea)と
呼んだものに倣う。難問を個別の道具でこじ開ける代わりに、理論の抽象度の水位を
上げ、問題が自然に解ける水準まで持ち上げる。

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
いる限り水は引かない。SAGA の名が Serre の GAGA — 二つの幾何の対応を確立した
比較定理 — へのオマージュであるのは、この構図による。

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
  stack descent(第5.4節)を、それぞれ独立の statement として開発する。
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
第7章の診断階段(非零類 → BLOCKED → repair 事前検証 → PASS)は、
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

第二に、**Lean 形式化の到達状況**である。additive `H^1`、cover-relative Čech
complex、quotient-level comparison、equation-generated realization、
零・非零の有限 witness を machine-checked theorem chain として記録し、
数学本文との対応、仮定、axiom 状況を declaration 単位で固定した。

第三に、**one-cent realization** である。実在の microservice システムの
払い戻し三角形上で、3つの金額規約の衝突と triple overlap の不在が立てる
非零 residual class を計測し、gate による blocking、修理案の事前検証、
repair 後の障害消滅、gate PASS までを一つの再現可能な計算として一周した。
各 chart は自分の局所方程式を完全に満たしていた。障害は、どの局所にも帰属しない
1セント未満のドリフトとして、ループを一周したときにだけ現れた。

抽象的な比較定理から出発した航路が、機械検証を経て、実在コードの
1セントに到達した。この 1セントは、局所的な正しさの総和が大域的な正しさに
届かないことの、最小で具体的な証人である。SAGA にとってこの到達点は
喜望峰である。すなわち、理論が現実の海へ抜ける最初の岬であり、
そこから先の海 — architecture schemes、moduli、Software Field Theory、
Rising Sea — への航路が、この比較定理によって開かれている。

---

## 付録(草稿管理)

### A. 執筆残作業(release identity 確定と連動)

- [x] 第3章: canonical 第I〜III部からの基礎定義の自足化(§3.8 対応表で固定)
- [ ] 第5章: notation 対応表(paper ↔ canonical)の付録固定
- [ ] 第6章: release tag での status table 確定(status / assumptions / `#print axioms` / CI evidence)
- [ ] 第6章: 未証明・未接続・未移植一覧の正確な記録
- [ ] 第7章: deposit 相対 path、ArchSig version、実行 command、expected output の固定
- [x] 第8章: Young artifact 確認と定理番号確定(related_work.md §2.7 に記録)
- [ ] 第8章: P0 文献 BibTeX 固定、投稿時の最新版再確認
- [ ] 全章: claim-to-evidence matrix の構築と各 claim の一次証拠への対応
- [ ] SAGA comparison の可換図と one-cent の計算図の作成
- [ ] Zenodo metadata(著者、affiliation、ORCID、license、DOI)の固定

### B. Claim-to-evidence matrix(skeleton)

| Claim type | 論文の箇所 | 必要な一次証拠 | 状態 |
| --- | --- | --- | --- |
| Mathematics | 第4〜5章 | canonical math source(第X部)、theorem map(§5.6) | 対応表あり、notation 表 TODO |
| Lean | 第6章 | declaration、source、focused check、axiom audit | table skeleton、release 監査 TODO |
| Measurement | 第7.5節 | packet、manifest、digest | 正本 report あり、deposit path TODO |
| Empirical | 第7.4節 | repository、commit `313886e99bef`、source reference、input | 正本 report あり |
| Empirical(供給工程) | 第7.2節 | archmap-creater SKILL、scope manifest、調停記録、audit、run のモデル記録 | 正本 report あり、deposit 同梱範囲 TODO |
