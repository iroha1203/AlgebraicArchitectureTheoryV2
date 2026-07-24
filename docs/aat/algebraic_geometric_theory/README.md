# 代数幾何的アーキテクチャ論

このディレクトリは、現行 AAT 数学本文の正典である。

Algebraic Architecture Theory, AAT は、ソフトウェアアーキテクチャを
Atom から生成され、architectural equations によって切り出され、obstruction sheaf と
cohomology によって局所から大域への不整合を読む幾何対象として扱う理論である。

AAT の対象は、source と admissible core reading から生成される architecture object に、
coverage topology と coefficient ring を固定して構成する相対的なアーキテクチャ幾何である。

```text
C : Codebase
At : AtomUniverse
S : AtomAxiomSystem(At)
r : CoreRead(At), with source C
    including extraction doctrine, Atom vocabulary,
    finite composition, object / context / equation / circuit readings,
    signature / operation readings
E_r : architectural equation system produced by the equation reading of r
Sig_r : architecture signature produced by the signature reading of r
R_r : CoverageRequirements(A_r,E_r,Sig_r)
Ov_r : ContextOverlapPullback(ArchCtx(A_r)) realizing the requests in R_r
J_{E_r,R_r,Ov_r} : topology generated from the selected coverage package
k : coefficient ring

X_C^{r,J,k} : AATGeometry
```

`S` は Atom carrier の primitive existence と coordinate stability を認証し、`r` はその carrier 上の
extraction・composition・context・equation・signature・operation reading を選ぶ。`E_r` と `Sig_r` は
それぞれ `r` の equation reading と signature reading の値であり、別入力ではない。両者は core package で
統合するが、reading を使われない axiom parameter に添字付けない。

core reading のうち source、extraction doctrine、object reading、operation reading を固定し、
Atom vocabulary `V` と architectural equation system `E` を表示する場合は
`X_C^{V,E,J,k}` と略記する。自然言語の law universe `U_E` は `E` の index と role の読みであり、
別入力ではない。ここで `J` は、固定済みの `Sig`、`R`、`Ov` から生成された
`J_{E,R,Ov}` の略記である。係数環を明示しない `X_C^{V,E,J}` は `k` を固定済みとする。

この本文では、AAT を「代数幾何的アーキテクチャ論」として定式化する。
Atom は primitive architectural fact として公理化される。architectural equation system は Atom を生成せず、
Atom family 上の symbolic violation coordinates と object-dependent residuals を与える。law はその equation family の読みである。
obstruction は equation failure の
witness であり、局所的な witness が大域的に貼り合わない場合、その差は
cohomology class として現れる。

中心図式は次である。

```text
(Atom universe At, axiom system S, core reading r)
  -> Atom family F_r
  -> configuration C_r
  -> architecture object A_r
  -> Architecture context category
  -> Atom-indexed architectural equation system
  -> operation / circuit / signature families
  -> operation-closed object algebra Core_At(r)
  -> coverage requirements + context-overlap pullback package
  -> AAT site
  -> Sheaves
  -> Ringed AAT topos
  -> Law algebra
  -> Obstruction ideal sheaf
  -> Affine AAT charts
  -> Architecture scheme
  -> Lawful locus
  -> Obstruction cohomology
  -> Derived law geometry
  -> Singularity / monodromy / stack
  -> Representation / periods / analysis
  -> Measurement theory
  -> Evolution geometry
  -> Semantic repair descent / SAGA comparison
  -> Mathematical glossary / finite worked example
```

## 位置づけ

このディレクトリの本文では、AAT を純粋な数学理論として扱う。
本文の内部対象は、Atom、architecture object、architectural equation system、site、sheaf、cohomology、
representation、measurement profile、trace category、semantic repair presentation とその Čech complex である。
未選択の観測過程、外部過程、応用上の判定手続きについて、本文は主張しない。

従来の Atom / law / obstruction / flatness / signature による AAT は、
この理論史における古典的な有限・構成的基礎である。この本文は、その先行体系への
注釈書ではなく、Atom の公理から代数幾何的アーキテクチャ論を自立して構成する。

## 数学本文の自立性（hard rule）

このディレクトリの数学本文は Tier 1 の正典であり、定義、命題、定理、証明を
数学本文自身の公理、構成、仮定だけで閉じる。次を数学本文へ持ち込むことを禁止する。

1. Lean status、宣言名、source path、import、build、CI、axiom audit、形式化の進捗。
2. この正典シリーズ外にある repository 内文書への参照。research、GOAL、台帳、PRD、
   tooling、website、outreach、archive その他の文書を、定義・仮定・証明・完了根拠に用いない。
3. GitHub Issue、Pull Request、review comment、番号、URL、acceptance、merge state への参照。
4. web page、外部 repository、release artifact、外部 status、その他の外部資料への参照。

第I部から第X部および付録の間の参照は、同じ数学正典の内部参照として扱う。
歴史的説明、実装状況、形式化状況、研究運用、公開計画、外部資料との比較が必要な場合は、
数学本文の外で記述する。それらは数学 claim の仮定、証拠、完成判定にならない。

## なぜ代数幾何か

この本文が代数幾何を選ぶのは見立てではない。各階層が、ソフトウェアアーキテクチャが
実際に立てる問いに対応するからである。

```text
連立方程式系:
  現実のアーキテクチャは複数の law が同時に効き、同時に成立するか同時に破れる。
  代数幾何は連立方程式の数学である。required equations の symbolic violation coordinates は
  obstruction ideal を生成し、object-dependent residuals の同時消滅が equation lawfulness を定める。
  standard equation-scheme constructor の generator / localization producer theorems により、
  ideal-theoretic lawful locus は共通零点
  Flat_U(X) = V(I_Ob^U) であり、
  law の相互作用はイデアルの演算になる。
  open、constructible、descent、temporal、stacky law は対応する幾何条件として読む。

貼り合わせの障害:
  「各モジュールは正しいのに全体が壊れる」は descent 問題である。
  貼り合わない局所 section は sheaf theory の正確な対象になり、
  不整合は cohomology で測られる。可視の失敗は H^0、
  貼り合わせの失敗は H^1、整合性の失敗は H^2。

失敗の等級:
  失敗は二値ではなく構造を持つ。住む cohomology 次数、
  law conflict の Tor 次数、特異点の型。
  「どれくらい・どの種類に壊れているか」が数学的対象になり、
  repair の優先順位づけの出発点になる(第V部・第VI部)。

道具の継承:
  アーキテクチャを ringed geometry にした時点で、既存の道具がそのまま働く。
  derived intersection と Tor sheaf は潜在的 law conflict を、
  cotangent complex は特異性を、monodromy は操作履歴を読み、
  stack と gerbe は標準分解の存在可否を判定する。
  どれもソフトウェアのために発明し直す必要がなかった。

相対性:
  グロタンディーク以来、代数幾何は絶対的な対象ではなく base に相対的な対象を研究する。
  vocabulary、architectural equation system、coverage requirements、coverage topology、係数環を固定し、
  選ばれなかったものについて沈黙する本文の規律は、
  理論に後付けした安全条項ではなく、この数学そのものの標準的な作業姿勢である。

運動:
  対象が幾何であるから、その上に構造を積める。
  第IX部は trace category と temporal coefficient によって
  AAT geometry の時間方向を扱う。
```

この六つの答えの背後にあるのは、グロタンディークの「上昇する海」の像である。
問題は力ずくでこじ開けられない。理論の水位が上がり、問題が包囲され、
ほとんどひとりでに開く。AAT はソフトウェアアーキテクチャに対して同じ姿勢を取る。
循環依存、隠れた結合、修理が別の law を壊す現象は、
個別のパズルとして各個撃破されない。Atom、site、ideal、cohomology と水位が
上がるにつれて、それぞれは道具の備わった既知の幾何現象として現れる。

## 構成

1. [第I部 Atom・対象・法則](part_1_atoms_objects_laws.md)
2. [第II部 Architecture Geometry・Site・Sheaf](part_2_architecture_geometry_sites_sheaves.md)
3. [第III部 Law Algebra・Obstruction Ideal・Lawful Locus](part_3_law_algebra_obstruction_ideal_lawful_locus.md)
4. [第IV部 Obstruction Cohomology](part_4_obstruction_cohomology.md)
5. [第V部 Derived Law Geometry と Repair](part_5_derived_law_geometry_repair.md)
6. [第VI部 Singularity・Monodromy・Stack](part_6_singularity_monodromy_stack.md)
7. [第VII部 Representation・Periods・Analysis](part_7_representation_periods_analysis.md)
8. [第VIII部 Measurement Theory](part_8_measurement_theory.md)
9. [第IX部 Evolution Geometry](part_9_evolution_geometry.md)
10. [第X部 Semantic Repair Descent と SAGA 比較定理](part_10_semantic_repair_descent_saga.md)
11. [付録 Mathematical Ambient, Glossary, and Finite Worked Example](appendix.md)

## 主張の読み方

AAT 本文の主張は、固定された vocabulary、architectural equation system、coverage topology、
係数 sheaf、表現族に相対化される。次を混同しない。

```text
Formal theorem:
  公理・定義・仮定から証明される数学的命題。

Certified bounded inference:
  E-adequacy、standard constructor が生成した comparison producer theorem、
  witness completeness などの明示入力の下で成立する相対的推論。

Analytic reading:
  構成された幾何対象を graph、signature、period、metric などで読む表現。
```

本文のラベルは次の規律で読む。

```text
Definition / Construction:
  対象、係数、reading、predicate を導入する。

Theorem / Proposition / Lemma:
  本文で明示した定義と仮定のもとで読む数学命題。
  ただし E-adequacy、生成元水準の comparison producer theorem、witness completeness などを仮定に置くものは
  Certified bounded inference であり、無条件の絶対 claim ではない。

Theorem candidate:
  今後の定義・証明設計を示す本文内の定理候補。

Principle:
  claim boundary、読み方、非主張を固定する規律。

Analytic reading:
  表現、metric、period、mass など、構成済み幾何対象を読む方法。
```

主要な用語、追加仮定、theorem candidate は
[付録](appendix.md) の mathematical glossary にまとめる。

AAT 本文内の measurement は、固定された数学的対象と selected profile に相対化された reading である。
選ばれていない data source、観測手段、判定手続きの完全性は仮定しない。

## 強い代数幾何としての階層

この本文は、AAT を単に「幾何的に見立てる」のではなく、次の階層で代数幾何化する。

```text
AAT site:
  局所 context、cover、restriction、descent を与える。

Ringed AAT topos:
  AAT site 上に可換環の層 O_X^U を載せる。

Affine AAT chart:
  Spec_AAT(O_X^U(W), D_W^U) として局所的な affine geometry を読む。
  Spec_AAT は通常の Spec に AAT decoration を載せた対象である。

Architecture scheme:
  affine AAT chart が open immersion と cocycle condition によって貼れる場合の
  chart-compatible locally ringed architecture geometry。

Derived / stacky AAT geometry:
  lawful loci の derived intersection、Tor conflict、cotangent complex、
  monodromy representation、decomposition stack / gerbe を扱う。

Finite measurement geometry:
  finite poset site、cellular sheaf、Stanley-Reisner 複体、Tor、
  period pairing、Laplacian、transport cost を、選ばれた profile の中で測る。

Evolution geometry:
  trace category、state transition presheaf、temporal coefficient、dissipative policy、Lyapunov reading を、
  AAT geometry の時間方向の構造として扱う。

Semantic repair descent geometry:
  semantic atom と局所 repair relation から係数と residual class を構成し、
  architectural equation system が生成する係数と residual class へ
  Atom/equation presentation map を通じて比較する(SAGA)。
  true sheaf 条件の下で零類を actual global repair へ貼り合わせる。
```

したがって、`ringed AAT topos` は architecture scheme を作るための基礎階である。
scheme と呼ぶ部分は、chart compatibility を満たす場合に強い意味で使う。

標準代数幾何への埋め込み方、係数環、relative parameters、law condition の一般形は
[付録](appendix.md) にまとめる。
