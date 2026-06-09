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
  -> Law algebra
  -> Obstruction ideal sheaf
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
2. 第II部 Site・Sheaf・Descent
3. 第III部 Law Algebra と Lawful Locus
4. 第IV部 Obstruction Cohomology
5. 第V部 Derived Law Geometry と Repair
6. 第VI部 Singularity・Monodromy・Stack
7. 第VII部 Representation・Periods・Analysis

## Claim Discipline

AAT 本文の主張は、固定された vocabulary、law universe、coverage topology、
係数 sheaf、表現族に相対化される。次を混同しない。

```text
Formal theorem:
  公理・定義・仮定から証明される数学的命題。

Certified bounded inference:
  coverage, exactness, witness completeness などの仮定の下で成立する相対的推論。

Tool diagnosis:
  測定済み artifact に相対化された実用的報告。
  AAT 本文の theorem ではない。
```

本文が扱うのは、最初の二つである。tool diagnosis は、AAT の外部で
`ArchMap + LawPolicy + evidence contract` に相対化して扱う。
