# Zenodo SAGA Paper: Related Work Research

調査日: 2026-07-24

この文書は、Zenodo 向け SAGA 論文の Related Work を構成するための調査メモである。
原典を直接確認し、SAGA の数学、Lean 形式化、ArchSig measurement と比較できる文献を選ぶ。

## 1. 結論

Related Work は、次の四群で構成する。

1. sheaf-cohomological program and system analysis
2. sheaf-based architecture and multi-view consistency
3. software architecture conformance and formal architecture description
4. mechanized mathematics and executable analysis

最初に扱う必須文献は Halley Young の 2026 年論文である。

> Halley Young, “Sheaf-Cohomological Program Analysis: Unifying Bug Finding,
> Equivalence, and Verification via Čech Cohomology,” arXiv:2603.27015, 2026.

- [arXiv](https://arxiv.org/abs/2603.27015)
- [Microsoft Research](https://www.microsoft.com/en-us/research/publication/sheaf-cohomological-program-analysis-unifying-bug-finding-equivalence-and-verification-via-cech-cohomology/)

この論文は、semantic presheaf、program site、Čech \(H^1\)、Lean 形式化、実行可能な
analysis tool を一つの研究として提示する。SAGA と共有する構成要素が最も多く、
SAGA の独自性を最も精密に説明できる直接比較対象である。

## 2. 最重要比較: Young 2026

### 2.1 Young 論文が構成するもの

Young は Python program から observation site と data-flow morphism を持つ program site を構成し、
各 site に refinement-type information を割り当てる semantic presheaf を置く。

論文の主要な読みは次である。

- \(H^0\): globally consistent typings
- \(H^1\): bugs、type errors、equivalence failures を表す gluing obstruction
- \(\operatorname{rank} H^1\) over \(\mathbb F_2\): minimum independent fixes
- \(H^1(U,\mathrm{Iso})=0\): behavioral equivalence
- Mayer–Vietoris: compositional and incremental obstruction counting

実装 `Deppy` は Python analysis tool であり、375 benchmarks に対して bug detection、
program equivalence、specification satisfaction を評価する。論文が報告する結果は次である。

| Task | Reported result |
| --- | --- |
| bug detection | recall 100%、precision 69%、F1 81% |
| equivalence | accuracy 99%、false equivalence 0 |
| specification satisfaction | accuracy 98%、false satisfaction 0 |

Microsoft Research は、この研究を 2026 年 3 月の arXiv 論文として掲載している。

### 2.2 Young と SAGA が共有する研究構造

両研究は、次の一本の構造を共有する。

```text
local semantic observations
  -> site / cover
  -> presheaf or coefficient system
  -> Čech complex
  -> H¹ obstruction
  -> executable analysis
```

さらに、両研究とも数学的主張の Lean 形式化と、具体的な program または architecture artifact
に対する実行系を持つ。このため、単に「sheaf を software に応用した研究」として一括せず、
対象、係数の由来、比較定理、repair interpretation、実証単位を個別に比較する。

### 2.3 比較表

| Axis | Young 2026 | SAGA |
| --- | --- | --- |
| primary object | Python program と observation sites | programming language から独立した Atom family と architecture object |
| local semantics | refinement-type information | semantic atom、architectural Law、repair datum |
| representational reach | Python の program representation と refinement types | language、framework、serialization representation を越える architectural meaning |
| characteristic inconsistency | bug、type error、equivalence failure | 同じ実装型を持ちながら意味が異なる local conventions の gluing failure |
| site | program observation と data-flow から構成 | Atom support と equation-coordinate coverage から構成 |
| coefficient | semantic presheaf、\(\mathbb F_2\) realization | architectural equations が生成する \(Q_E=\mathcal O_E/I_{\mathrm{Ob}}\) |
| \(H^0\) | globally consistent typings | law-generated degree-zero vanishing と local lawfulness |
| \(H^1\) | bug、type error、equivalence failure | semantic repair obstruction と AAT Čech obstruction |
| central theorem | program-analysis claims expressed through Čech cohomology | \(H^1_{\mathrm{sem}}\cong\check H^1(\mathcal U,Q_E)\) comparison |
| repair reading | rank as independent fixes | residual class、boundary、semantic closure、repair gluing |
| Lean | paper reports a 1,259-line formalization | Atom-to-comparison theorem chain、zero and nonzero witnesses |
| executable system | Deppy over Python programs | ArchSig over ArchMap、LawPolicy、MeasurementProfile |
| empirical unit | 375 program-analysis benchmarks | existing microservice architecture and repair comparison |

### 2.4 SAGA の位置づけ

Young は、program semantics を直接 Čech cohomology として組織し、bug finding、
equivalence、verification を統一する。SAGA は、software architecture の semantic repair complex と、
architectural equations から生成される AAT geometry の Čech complex の間に比較写像を構成する。

SAGA の中心貢献は次の三点として書く。

1. semantic repair \(H^1\) と AAT Čech \(H^1\) を別々に定義し、比較定理で接続する。
2. Čech coefficient \(Q_E\) を architectural Law の equation system と witness ideal から生成する。
3. comparison theorem、Lean theorem chain、ArchSig measurement、実コード上の repair comparison を
   同じ provenance に置く。

さらに、両研究は分析対象を構成する抽象度が異なる。Young の論文は Python program の
observation sites と refinement-type information から program analysis を構成する。
AAT の primitive は programming language や framework に属する syntax ではなく Atom であり、
複数の言語、service、storage representation にまたがる architectural fact と Law を
同じ architecture object の上で扱う。

この違いは one-cent obstruction に具体化される。問題となる価格が実装上はいずれも `string`
として表現されている場合、通常の型の一致は成立している。しかし、その `string` が表す価格の
丸め、scale、計算、保存に関する意味は service ごとに異なり得る。SAGA は、型名の差ではなく、
それぞれ局所的に成立する意味規約が一つの global architecture へ貼り合うかを測定する。

この書き方により、Young の成果を正面から評価しながら、SAGA が program-level analysis の反復ではなく、
architecture semantics と AAT geometry の比較定理であることを示せる。

### 2.5 本文用ドラフト

> Young organizes type checking, bug finding, and program equivalence as Čech-cohomological
> analysis of a semantic presheaf over a Python program site. The work is the closest contemporary
> point of comparison to SAGA: both use local semantic observations, Čech \(H^1\), Lean
> formalization, and an executable analyzer. The two constructions differ in their mathematical
> center and level of abstraction. Young computes cohomology directly on a Python
> program-semantic presheaf. AAT begins with language-independent Atoms and Laws, allowing one
> architecture object to relate facts expressed across different languages, services, and storage
> representations. SAGA constructs semantic-repair cohomology and equation-generated AAT Čech
> cohomology separately, then proves that their first cohomology groups agree. It can therefore
> capture semantic disagreement even when implementation-level types agree: the one-cent case,
> for example, involves values represented as `string` whose monetary conventions do not glue.
> The coefficient \(Q_E\), the cover, and the comparison maps are generated from the architectural
> equation system and its incidence data. This comparison turns an architectural repair obstruction
> into a geometric class while preserving its zero and nonzero readings.

### 2.6 引用前の精読項目

Young 論文の主張を SAGA 本文で正確に引用するため、次を TeX source、Lean source、
Deppy artifact で確認する。

1. semantic presheaf は complete lattice-valued と記述される一方、Čech differential、
   quotient \(Z^1/B^1\)、rank は additive structure を用いる。一般定義から
   \(\mathbb F_2\) cochain complex へ進む構成を確認する。
2. cover と sheaf condition の定義、および \(H^1=0\) との対応で用いる仮定を確認する。
3. \(\operatorname{rank} H^1\) と minimum independent code fixes の対応を与える repair semantics と
   witness を確認する。
4. behavioral equivalence の soundness and completeness が量化する program class と semantic relation を
   確認する。
5. Mayer–Vietoris による incremental update の exact sequence と計算手順を確認する。
6. 論文が報告する Lean 形式化の source、declaration、axiom、build procedure を確認する。
7. 375 benchmarks、Deppy source、evaluation script の公開 artifact を確認する。

2026-07-24 時点で、arXiv と Microsoft Research の公開ページから Lean / Deppy repository への
直接リンクは確認できていない。Related Work 本文では、公開ページで確認できる主張を引用し、
source-level comparison は artifact の所在を確認してから確定する。

### 2.7 確認結果(2026-07-24 調査)

§2.6 の精読項目のうち、公開版(arXiv HTML)と web 調査で確定できた事実を記録する。

**書誌事項。** arXiv:2603.27015 は v1(2026-03-27 submitted)のみ、subject は cs.PL、
単著(Halley Young)。abs ページに Comments field はなく、code / artifact URL の記載もない。
Microsoft Research の publication ページも outbound link は arXiv と BibTeX のみで、
code repository へのリンクを持たない。venue は arXiv preprint(会議未採録)。

**定義・定理番号(HTML 版で確認)。**

| 番号 | 内容 |
| --- | --- |
| Definition 3.1 | site kind(five families) |
| Definition 3.2 | program site category |
| Definition 3.3 | refinement lattice |
| Definition 3.4 | local section |
| Definition 3.5 | semantic presheaf |
| Definition 3.6 | covering family |
| Definition 3.8 | Čech cochains |
| Theorem 5.1 | bugs as gluing obstructions(`H¹≠0` iff bug) |
| Prop.(5.1 直後) | `rank H¹` over `F₂` = minimum independent fixes |
| Theorem 5.3 | descent for equivalence |
| Theorem 6.1 / 6.2 | soundness / relative completeness |
| Theorem 6.3 | Mayer–Vietoris for programs |
| Theorem 6.4 | fixed-point convergence |

**`F₂` realization(精読項目1に対応)。** lattice-valued presheaf から `F₂` への移行は
§5.1 で行われる。overlap 上の一致 / 不一致を Boolean に落とし、行を overlap、
列を site とする coboundary matrix `∂⁰:C⁰(F₂)→C¹(F₂)` の rank 計算に帰着する。

**Lean 形式化(精読項目6に対応)。** 本文は 1,259 lines of Lean 4 と報告し、
declaration 名として `DeppyProofs.Soundness.soundness`、
`DeppyProofs.Presheaf.h0_lifts_to_section`、`DeppyProofs.Descent.descent_theorem` を挙げる。
形式化対象は soundness、sheaf condition characterization、`H⁰` section lifting、
descent for equivalence、Mayer–Vietoris exactness、fixed-point convergence。
source repository へのリンクは本文にない。

**Artifact の所在(精読項目2・7に対応)。** 著者の GitHub に
[`thehalleyyoung/deppy`](https://github.com/thehalleyyoung/deppy)("Dependent Types for
Python"、MIT license、Lean 4 export 機構、tutorial book に Čech decomposition 章、
`paper/` ディレクトリあり)が存在し、同名 tool の公開実装として最有力候補である。
ただし repo README は本論文・375 benchmarks・`DeppyProofs` を明示引用していない。
375 benchmarks と evaluation script の公開は未確認である。

**引用方針への帰結。** Related Work 本文の Young への言及は「the paper reports」
(論文が報告する)の形を維持する。1,259-line Lean、375 benchmarks、evaluation 数値は
論文の報告として引用し、独立検証済みの事実としては書かない。`thehalleyyoung/deppy` は
本文では引用せず、artifact が論文と明示的に接続された時点で citation へ昇格させる。

## 3. 同時期の直接関連研究

### 3.1 Gibson 2026: architecture、sheaf condition、Lean

> Josh Gibson, “Sheaves as a Means of Maintaining Consistency in Model-based Systems
> Engineering,” arXiv:2605.08609, 2026.

- [arXiv](https://arxiv.org/abs/2605.08609)

Gibson は cyber-physical systems の multi-view architecture に対して architectural site を構成する。
points は engineering domains 間の pairwise interfaces、open sets は engineering views であり、
design presheaf の sheaf condition を global multi-view consistency として読む。

主要成果は次である。

- pairwise overlap compatibility と sheaf condition の同値
- compatible local designs の unique global gluing
- three-view example
- Lean 4 / Mathlib による machine verification

SAGA との関係は明確である。Gibson は architecture における compatible family と global section を
sheaf condition で扱う。SAGA は local lawfulness の先に残る first-cohomology class を構成し、
semantic repair と equation-generated geometry の比較を証明する。

本文用の一文は次とする。

> Gibson gives a Lean-verified sheaf model of multi-view consistency in systems engineering,
> characterizing global designs by compatible local designs on pairwise interfaces. SAGA develops
> the complementary obstruction-theoretic direction: it constructs the \(H^1\) class that remains
> when local architectural data fail to glue and compares its semantic and equation-generated
> geometric realizations.

Lean formalizationについては、定理が Mathlib の general sheaf result を architecture vocabulary へ
instantiate する部分と、独自に構成・証明する部分を declaration 単位で確認してから記述する。

### 3.2 Felber–Flores–Galeana 2025: distributed task solvability

> Stephan Felber, Bernardo Hummes Flores, and Hugo Rincon Galeana,
> “A Sheaf-Theoretic Characterization of Tasks in Distributed Systems,”
> arXiv:2503.02556, 2025.

- [arXiv](https://arxiv.org/abs/2503.02556)

この研究は task sheaf を構成し、distributed task の terminating solution を global section として扱う。
cohomology は process decision space の linear-algebraic description と solution obstruction を与え、
approximate agreement の protocol synthesis へ接続される。

SAGA との共有点は、local computation、global consistency、cohomological obstruction、
computational use の接続である。対象は distributed task solvability であり、SAGA は
architectural Law、semantic repair、AAT geometry を対象とする。

### 3.3 Young–Bjørner 2026: research software methodology

> Halley Young and Nikolaj Bjørner, “Theory Under Construction: Orchestrating Language
> Models for Research Software Where the Specification Evolves,” arXiv:2604.27209, 2026.

- [arXiv](https://arxiv.org/abs/2604.27209)
- [Microsoft Research](https://www.microsoft.com/en-us/research/publication/theory-under-construction-orchestrating-language-models-for-research-software-where-the-specification-evolves/)

この論文は、mathematical thesis、executable system、benchmark、public claims を一つの
workspace state として同期する Comet-H を提案する。SAGA の数学上の比較対象ではないが、
mathematics、Lean、ArchSig、paper claim を固定された証拠へ接続する artifact methodology と
近い問題を扱う。Discussion または reproducibility で一度参照する候補とする。

## 4. Sheaf と cohomology の computer science 応用

### 4.1 Global-section obstruction

> Samson Abramsky and Adam Brandenburger, “The Sheaf-Theoretic Structure of
> Non-Locality and Contextuality,” *New Journal of Physics* 13, 113036, 2011.

- [arXiv](https://arxiv.org/abs/1102.0264)
- [DOI](https://doi.org/10.1088/1367-2630/13/11/113036)

measurement cover 上の local data が global section を持つかという問題を sheaf theory で統一する。
local compatibility と global realizability を分離する基礎文献として引用する。

> Samson Abramsky, Shane Mansfield, and Rui Soares Barbosa, “The Cohomology of
> Non-Locality and Contextuality,” EPTCS 95, 1–14, 2012.

- [arXiv](https://arxiv.org/abs/1111.3620)
- [DOI](https://doi.org/10.4204/EPTCS.95.1)

Čech cohomology class の非消滅を global section の obstruction として用いる。
SAGA の \(H^1\) reading を、software より広い local-to-global obstruction の系譜へ置く文献である。

### 4.2 Constraint satisfaction and finite computation

> Adam Ó Conghaile, “Cohomology in Constraint Satisfaction and Structure Isomorphism,”
> MFCS 2022, LIPIcs 241, 75:1–75:16.

- [Dagstuhl](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2022.75)
- [DOI](https://doi.org/10.4230/LIPIcs.MFCS.2022.75)

CSP と structure isomorphism を presheaf の global-section problem として表し、
Čech cohomology による computable obstruction を構成する。SAGA と同じく、cohomological
obstruction を有限アルゴリズムへ接続する先行例として重要である。

### 4.3 Cellular sheaves and computable data integration

> Justin Curry, “Sheaves, Cosheaves and Applications,” arXiv:1303.3255, 2014.

- [arXiv](https://arxiv.org/abs/1303.3255)

> Michael Robinson, “Sheaves are the canonical data structure for sensor integration,”
> *Information Fusion* 36, 208–224, 2017.

- [arXiv](https://arxiv.org/abs/1603.01446)
- [DOI](https://doi.org/10.1016/j.inffus.2016.12.002)

> Jakob Hansen and Robert Ghrist, “Toward a Spectral Theory of Cellular Sheaves,”
> *Journal of Applied and Computational Topology* 3, 315–358, 2019.

- [arXiv](https://arxiv.org/abs/1808.01513)
- [DOI](https://doi.org/10.1007/s41468-019-00038-7)

これらは cellular sheaf、cochain complex、cohomology、Laplacian、data fusion を
有限計算として扱う数学的・計算的基礎を与える。SAGA 本文では一段落にまとめ、
software architecture 固有の貢献との比較を Young、Gibson、Felber へ集中させる。

### 4.4 Concurrent and interacting software

> Joseph Goguen, “Sheaf Semantics for Concurrent Interacting Objects,”
> *Mathematical Structures in Computer Science* 2(2), 159–191, 1992.

- [DOI](https://doi.org/10.1017/S0960129500001420)

objects、inheritance、interaction、system composition を sheaf semantics で扱う初期の重要文献である。
software system を local models と gluing から読む歴史的系譜として引用する。

## 5. Software architecture conformance and formal description

### 5.1 Architectural mismatch

> David Garlan, Robert Allen, and John Ockerbloom, “Architectural Mismatch:
> Why Reuse Is So Hard,” *IEEE Software* 12(6), 17–26, 1995.

- [DOI](https://doi.org/10.1109/52.469757)

components、connectors、global architectural structure、construction process に埋め込まれた
assumptions の不一致を architectural mismatch として分析する。SAGA は、この種の不一致を
local Law と global gluing の数学へ移し、残差を \(H^1\) class として扱う。

### 5.2 Reflexion models and conformance

> Gail C. Murphy, David Notkin, and Kevin Sullivan, “Software Reflexion Models:
> Bridging the Gap between Design and Implementation,” FSE 1995.

- [DOI](https://doi.org/10.1145/222132.222136)

high-level architecture model と source model の mapping から convergence、divergence、absence を
計算する。architecture conformance の代表的出発点として、ArchSig の local-to-global measurement
との違いを示す。

### 5.3 Formal architectural connection

> Robert Allen and David Garlan, “A Formal Basis for Architectural Connection,”
> *ACM Transactions on Software Engineering and Methodology* 6(3), 213–249, 1997.

- [DOI](https://doi.org/10.1145/258077.258078)

Wright と CSP を用いて connector の protocol と compatibility を形式化する。
SAGA は connector protocol の適合性ではなく、複数の local semantic repair が
cover 全体で貼り合うかを cohomology class として扱う。

### 5.4 Architecture description languages

> Nenad Medvidovic and Richard N. Taylor, “A Classification and Comparison Framework
> for Software Architecture Description Languages,” *IEEE Transactions on Software
> Engineering* 26(1), 70–93, 2000.

- [DOI](https://doi.org/10.1109/32.825767)

ADL が提供する components、connectors、configurations、analysis、evolution の表現力を整理する。
AAT は Atom と Law から architecture object と geometry を構成し、SAGA はその上の
local-to-global obstruction を比較する。

### 5.5 Architecture erosion

> Lakshitha Ramesh De Silva and Dharini Balasubramaniam, “Controlling Software
> Architecture Erosion: A Survey,” *Journal of Systems and Software* 85(1), 132–151, 2012.

- [DOI](https://doi.org/10.1016/j.jss.2011.07.036)

> Ruiyin Li, Peng Liang, Mohamed Soliman, and Paris Avgeriou, “Understanding Software
> Architecture Erosion: A Systematic Mapping Study,” *Journal of Software: Evolution
> and Process* 34(3), e2423, 2022.

- [DOI](https://doi.org/10.1002/smr.2423)

これらは conformance、evolution、enforcement、recovery、reconciliation を含む
architecture erosion 研究を整理する。SAGA は erosion の分類そのものではなく、
選ばれた local data に対する global obstruction class と repair comparison を提供する。

## 6. Mechanized mathematics

> Leonardo de Moura and Sebastian Ullrich, “The Lean 4 Theorem Prover and
> Programming Language,” CADE 2021.

- [DOI](https://doi.org/10.1007/978-3-030-79876-5_37)

> The mathlib Community, “The Lean Mathematical Library,” CPP 2020.

- [DOI](https://doi.org/10.1145/3372885.3373824)

これらは Lean 4 と Mathlib の基盤文献として引用する。Related Work の主比較には置かず、
Lean Formalization 節で formal environment の出典として使う。

SAGA の formalization contribution は、Lean を利用したこと自体ではなく、次を machine-checked
theorem chain として構成した点に置く。

- semantic repair descent
- additive \(H^1\)
- cover-relative Čech complex
- cochain realization
- quotient-level \(H^1\) comparison
- zero and nonzero finite witnesses
- law-equation-generated realization

## 7. 採用優先度

### P0: 本文に必ず入れる

1. Young 2026
2. Gibson 2026
3. Felber–Flores–Galeana 2025
4. Abramsky–Brandenburger 2011
5. Abramsky–Mansfield–Barbosa 2012
6. Ó Conghaile 2022
7. Garlan–Allen–Ockerbloom 1995
8. Murphy–Notkin–Sullivan 1995
9. Allen–Garlan 1997
10. Medvidovic–Taylor 2000
11. Lean 4 and Mathlib references

### P1: 本文または脚注に入れる

1. Goguen 1992
2. Curry 2014
3. Robinson 2017
4. Hansen–Ghrist 2019
5. De Silva–Balasubramaniam 2012
6. Li–Liang–Soliman–Avgeriou 2022
7. Young–Bjørner 2026

### P2: bibliography 拡張時に再評価する

- architecture reconstruction and dependency-constraint tools
- sheaf semantics for process calculi and computational effects
- cellular-sheaf dynamics relevant to Software Field Theory
- domain-specific multi-view consistency tools

## 8. Related Work 章の推奨構成

### 8.1 Cohomological program analysis

Young を先頭に置き、shared construction と SAGA comparison theorem の違いを一つの表で示す。
Felber、Abramsky、Ó Conghaile を続け、global-section obstruction から computable \(H^1\) への
研究系譜を示す。

### 8.2 Sheaves for architecture and systems engineering

Gibson を中心に、multi-view compatibility と global gluing を扱う研究を整理する。
Goguen を歴史的出発点として置く。

### 8.3 Architecture conformance and formal connection

architectural mismatch、reflexion models、Wright、ADL を取り上げる。
局所違反の検出、protocol compatibility、model-to-code conformance と、
SAGA の global obstruction class を比較する。

### 8.4 Mechanized theorem chain and executable measurement

Young と Gibson の Lean formalization を再度参照し、SAGA の theorem chain、
finite witnesses、ArchSig measurement への接続を比較する。

### 8.5 Synthesis

章末は次の主張へ収束させる。

> Prior work has established sheaves as a language for global consistency, cohomology as a
> computable obstruction, and formal architecture models as a basis for conformance analysis.
> SAGA joins these lines by constructing an equation-generated AAT Čech complex for software
> architecture and proving that its first cohomology agrees with the independently defined
> semantic-repair obstruction. Lean verifies the comparison, and ArchSig evaluates its finite
> architectural instances.

## 9. 原稿化前の作業

- [x] Young の definition と theorem の正確な番号を記録する(§2.7、HTML 版で確認。
      TeX source 水準の照合は投稿前の最新版再確認と併せて行う)
- [x] Young の Lean / Deppy artifact の公開先を確認する(§2.7: 論文・MSR ページに
      リンクなし、候補 repo `thehalleyyoung/deppy` を記録、引用は「論文が報告する」形)
- [ ] Gibson の Lean declarations と Mathlib theorem の対応を確認する
- [ ] Felber の task-sheaf construction と cohomology statement を精読する
- [ ] P0 文献を BibTeX に固定する
- [ ] SAGA の text theorem と Lean declaration を比較表へ結びつける
- [ ] Related Work の英語本文を 1,500–2,000 words へ圧縮する
- [ ] 投稿時点で 2026 年文献の最新版と publication status を再確認する
