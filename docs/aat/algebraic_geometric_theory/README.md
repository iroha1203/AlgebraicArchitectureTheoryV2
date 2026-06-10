# 代数幾何的アーキテクチャ論

Algebraic Architecture Theory, AAT は、ソフトウェアアーキテクチャを
Atom から生成され、law によって切り出され、obstruction sheaf と
cohomology によって局所から大域への不整合を読む幾何対象として扱う理論である。

AAT の対象は、裸のコードベースそのものではない。Atom vocabulary、law universe、
coverage topology を固定したときに構成される、相対的なアーキテクチャ幾何である。

```text
C : Codebase
V : AtomVocabulary
U : LawUniverse
J : CoverageTopology

X_C^{V,U,J} : AATGeometry
```

この本文では、AAT を「代数幾何的アーキテクチャ論」として定式化する。
Atom は primitive architectural fact として公理化される。law は Atom を生成せず、
Atom family 上の関係・制約・零点条件を与える。obstruction は law failure の
witness であり、局所的な witness が大域的に貼り合わない場合、その差は
cohomology class として現れる。

中心図式は次である。

```text
Atom
  -> Atom family
  -> Architecture context category
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
```

## 位置づけ

このディレクトリの本文では、AAT を純粋な数学理論として扱う。
SFT、ArchSig、FieldSig、実コードベース抽出、tool diagnosis、empirical validation は
本文の内部対象ではない。それらは、AAT で構成された幾何対象を読む、測る、または
進化させる後続の理論・artifact で扱う。

従来の Atom / law / obstruction / flatness / signature による AAT は、
この理論史における古典的な有限・構成的基礎である。この本文は、その旧体系への
注釈書ではなく、Atom の公理から代数幾何的アーキテクチャ論を自立して構成する。

## 構成

1. [第I部 Atom・対象・法則](part_1_atoms_objects_laws.md)
2. [第II部 Architecture Geometry・Site・Sheaf](part_2_architecture_geometry_sites_sheaves.md)
3. [第III部 Law Algebra・Obstruction Ideal・Lawful Locus](part_3_law_algebra_obstruction_ideal_lawful_locus.md)
4. [第IV部 Obstruction Cohomology](part_4_obstruction_cohomology.md)
5. [第V部 Derived Law Geometry と Repair](part_5_derived_law_geometry_repair.md)
6. [第VI部 Singularity・Monodromy・Stack](part_6_singularity_monodromy_stack.md)
7. [第VII部 Representation・Periods・Analysis](part_7_representation_periods_analysis.md)

## 主張の読み方

AAT 本文の主張は、固定された vocabulary、law universe、coverage topology、
係数 sheaf、表現族に相対化される。次を混同しない。

```text
Formal theorem:
  公理・定義・仮定から証明される数学的命題。

Certified bounded inference:
  coverage, exactness, witness completeness などの仮定の下で成立する相対的推論。

Analytic reading:
  構成された幾何対象を graph、signature、period、metric などで読む表現。
```

本文の `Theorem` は、この本文で明示した定義と仮定のもとで読む数学的命題である。
Lean 形式化との対応は、必要に応じて
[`lean_theorem_index.md`](../lean_theorem_index.md) と
[`proof_obligations.md`](../proof_obligations.md) で確認する。

実コードベースからの読み取り、測定、経験的検証は、この幾何対象を別の観点から読む
後続の営みである。AAT 本文は、それらの完全性を仮定せず、固定された数学的対象の中で
語れることを述べる。

## 強い代数幾何としての階層

この本文は、AAT を単に「幾何的に見立てる」のではなく、次の階層で代数幾何化する。

```text
AAT site:
  局所 context、cover、restriction、descent を与える。

Ringed AAT topos:
  AAT site 上に可換環の層 O_X^U を載せる。

Affine AAT chart:
  Spec_AAT(O_X^U(W)) として局所的な affine geometry を読む。

Architecture scheme:
  affine AAT chart が open immersion と cocycle condition によって貼れる場合の
  chart-compatible locally ringed architecture geometry。

Derived / stacky AAT geometry:
  lawful loci の derived intersection、Tor conflict、cotangent complex、
  monodromy representation、decomposition stack / gerbe を扱う。
```

したがって、`ringed AAT topos` は architecture scheme を作るための基礎階である。
scheme と呼ぶ部分は、chart compatibility を満たす場合に強い意味で使う。
