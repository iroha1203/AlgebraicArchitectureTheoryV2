# 代数幾何的アーキテクチャ論

このディレクトリは、現行 AAT 数学本文の正典である。

Algebraic Architecture Theory, AAT は、ソフトウェアアーキテクチャを
Atom から生成される architecture object として始め、その上に固定された law universe、
coverage topology、係数環 / 係数 sheaf に相対化された architecture geometry を構成する理論である。
Atom は primitive architectural fact として公理化され、そこから AAT site、sheaf、
law algebra、obstruction ideal sheaf、lawful locus、architecture scheme、Čech descent、
derived law geometry が立ち上がる。

AAT の対象は、裸のコードベースそのものではない。Atom vocabulary、law universe、
coverage topology、coefficient ring を固定したときに構成される、相対的なアーキテクチャ幾何である。

```text
C : Codebase
V : AtomVocabulary
U : LawUniverse
J : CoverageTopology
k : coefficient ring

X_C^{V,U,J,k} : AATGeometry
```

係数環を明示しない場合、`X_C^{V,U,J}` は `k` を固定済みとする省略記法である。

この本文では、AAT を「代数幾何的アーキテクチャ論」として定式化する。
law は Atom を生成せず、選ばれた architecture geometry 上の関係・制約・零点条件を与える。
law failure は obstruction ideal sheaf と lawful locus によって局所代数的に読まれ、
局所 lawful section が大域的に貼り合わない場合、その差は Čech cohomology class として現れる。

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
  -> Measurement theory
  -> Evolution geometry
  -> Claim status / finite worked example
```

## 位置づけ

このディレクトリの本文では、AAT を純粋な数学理論として扱う。
本文の内部対象は、Atom vocabulary、Atom family、architecture object、law universe、
AAT site、sheaf、ringed AAT topos、law algebra、obstruction ideal sheaf、
lawful locus、architecture scheme、cohomology、representation、measurement profile、
trace category である。
未選択の観測過程、外部過程、応用上の判定手続きについて、本文は主張しない。

Atom / law / obstruction / flatness / signature という語は、代数幾何版の基礎データ、
局所 presentation、または artifact-side reading として使う。この本文はそれらの語への
注釈書ではなく、Atom 公理系から代数幾何的アーキテクチャ論を自立した正典として構成する。

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
10. [付録 Mathematical Ambient, Claim Status, and Finite Worked Example](appendix.md)

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

本文のラベルは次の規律で読む。

```text
Definition / Construction:
  対象、係数、reading、predicate を導入する。

Theorem / Proposition / Lemma:
  本文で明示した定義と仮定のもとで読む数学命題。
  ただし coverage, exactness, witness completeness などを仮定に置くものは
  Certified bounded inference であり、無条件の絶対 claim ではない。

Theorem candidate:
  今後の定義・証明設計を示す本文内の定理候補。
  Lean の中央 proof obligation になるのは、
  lean_theorem_index.md または proof_obligations.md に対応行を置いた場合だけである。

Principle:
  claim boundary、読み方、非主張を固定する規律。

Analytic reading:
  表現、metric、period、mass など、構成済み幾何対象を読む方法。
```

主要な未定義語、primitive predicate、future design obligation は
[付録](appendix.md) の status ledger にまとめる。
Lean 形式化との対応は、必要に応じて
[`lean_theorem_index.md`](../lean_theorem_index.md) と
[`proof_obligations.md`](../proof_obligations.md) で確認する。
これらの台帳に対応する Lean API または proof obligation が記載されていない theorem label は、
本文内の数学命題であり、現在の Lean proved claim とは読まない。

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
```

したがって、`ringed AAT topos` は architecture scheme を作るための基礎階である。
scheme と呼ぶ部分は、chart compatibility を満たす場合に強い意味で使う。

標準代数幾何への埋め込み方、係数環、relative parameters、law condition の一般形は
[付録](appendix.md) にまとめる。
