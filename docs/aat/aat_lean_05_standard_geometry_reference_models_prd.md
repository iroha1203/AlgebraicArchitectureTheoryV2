# PRD: AAT Lean Standard Geometry Reference Models

- 作成: 2026-07-13
- 対象module:
  - `Formal/AG/Examples/StandardGeometryReferenceModels.lean`
  - `Formal/AG/StatementContractsStandardGeometryReferenceModels.lean`
  - `Formal/AG/StatementContracts.lean`
  - `Formal/AG/AxiomAudit.lean`
  - `Formal/AG.lean`
- 数学的正典:
  - `docs/aat/algebraic_geometric_theory/part_2_architecture_geometry_sites_sheaves.md`
    定義3.1、4.1、命題4.2のselected finite-meet overlap部分、仮定4.3、6.1、
    定義7.1、8.1、9.1、10.1〜11.2
  - `docs/aat/algebraic_geometric_theory/part_3_law_algebra_obstruction_ideal_lawful_locus.md`
    定義4.1〜4.3、条件4.4〜4.5、定義5.1、5.2〜5.2B、6.1〜7.2、定義8.1、8.5、
    定義9.2〜9.3、10.1〜10.3、定理11.1、定義11.3、定理11.4のideal-restriction部分
  - `docs/aat/algebraic_geometric_theory/appendix.md`
    A.2.1のclosed-equational law inclusion / flat coefficient base change部分、A.3〜A.8
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、
  `docs/aat/lean_quality_standard.md`
- statement contract正本: GitHub [tracking Issue #3587](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3587)
  本文の`Statement contract index`が列挙するcomment群
- executable contract: `Formal/AG/StatementContractsStandardGeometryReferenceModels.lean`
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

次をすべて満たすまで実装を開始しない。

1. tracking Issue本文の`Statement contract index`が`Statement contract policy`、`固定対象`、
   `SD0`〜`SD9`のcomment URLを一意に列挙し、対象main commit、SD0〜SD7の`T` / `F` / `C` inventory、
   SD8のmaterial premise表、family展開後のSD9 firing matrix、module DAG、子Issue依存、
   各子Issueのfocused checkを登録している。
2. 対象main commit上に次のmerged宣言が存在し、本PRDの参照型と一致している。
   PRDやdocs-only差分はこの条件を満たさない。
   - `AATCorePackage`、`FiniteModel.corePackage`、
     `FiniteModel.TwoPatchContextIndex`、`FiniteModel.twoPatchContext`、
     `FiniteModel.twoPatchContextIndexLe`、`FiniteModel.twoPatchContextMeet`
   - `RawAmbientRestrictionSystem`、`SheafifiedSectionRing`、
     `sheafifiedRestriction`、`architectureChartSpec`
   - `AATReadingDecoration`、`ArchitectureAffineChart`、
     `ArchitectureAffineAtlas`、`ArchitectureOverlapPresentation`
   - `StandardArchitectureScheme`、`StandardArchitectureScheme.ofPresentation`、
     `StandardArchitectureScheme.affineOpenCover`、
     `StandardArchitectureScheme.overlap_is_actual_pullback`
   - `ClosedEquationalLawReading`、`IsClosedEquationalLawReading`、
     `RequiredClosed`、`RequiredLawIdealExact`
   - `SemanticLawEquationWitnessIdealCore`、
     `SemanticLawEquationSchemeBridge`、
     `IsSemanticLawEquationSchemeBridge`、
     `semanticCoreGlobalEquation`、`semanticCoreIdealSheaf_realized`
   - `lawGeneratedIdealSheaf`、`lawfulClosedSubscheme`、
     `lawfulClosedImmersion`、`lawfulClosedImmersion_ker`、
     `lawfulClosedImmersion_range`、`lawfulClosedSubschemeCover`、
     `lawfulClosedSubschemeObjIso`、`lawfulnessIdealFactorizationCorrespondence`
   - `WitnessVanishes`、`IdealLawfulAlong`、
     `FactorsThroughLawfulClosedSubscheme`
   - `ClosedEquationalLawInclusion`、`IsClosedEquationalLawInclusion`、
     `lawfulClosedSubschemeMap`、`lawfulClosedSubschemeMap_isClosedImmersion`、
     `lawfulClosedSubschemeMap_immersion`、`lawfulClosedSubschemeMap_id`、
     `lawfulClosedSubschemeMap_comp`、
     `ClosedEquationalLawInclusion.refl`、
     `ClosedEquationalLawInclusion.refl_valid`、
     `ClosedEquationalLawInclusion.comp`、
     `ClosedEquationalLawInclusion.comp_valid`
3. coefficient changeのmerged実装が存在し、少なくとも次の宣言を直接参照できる。
   - `FlatCoefficientChange`
   - `RawAmbientRestrictionSystem.baseChange`
   - `StandardArchitectureScheme.baseChange`、
     `StandardArchitectureScheme.baseChangeMap`、
     `StandardArchitectureScheme.baseChangedAtlas`、
     `StandardArchitectureScheme.baseChangedAtlas_Index`、
     `StandardArchitectureScheme.baseChangedChartMap`、
     `StandardArchitectureScheme.baseChangedChart_isPullback`
   - `ClosedEquationalLawReading.baseChangeOfSemanticCore`と、そのvalidity /
     `RequiredClosed` constructor
   - `lawGeneratedIdealSheaf_baseChange_ofSemanticCore`
   - `lawfulClosedSubschemeBaseChangeMap`と
     `lawfulClosedSubschemeBaseChangeMap_immersion`
4. Mathlibの次のAPIを対象main commit上のscratch fileで`#check`し、
   exact name、引数順、direct importをtracking Issueへ記録している。
   - `Scheme.affineOpenCoverOfSpanRangeEqTop`
   - `AlgebraicGeometry.basicOpenIsoSpecAway`
   - `Scheme.isOpenImmersion_SpecMap_localizationAway`
   - `Scheme.Spec.map`、`Scheme.ΓSpecIso`
   - `Localization.Away`、`IsLocalization.Away`
   - `Scheme.IdealSheafData.ofIdealTop`、`subscheme`、`subschemeι`、
     `inclusion`、`inclusion_subschemeι`
   - `MvPolynomial.eval₂Hom`、`Ideal.map`、`Ideal.span`
5. `ℤ[x]`、`D(x)`、`D(1-x)`、`D(x(1-x))`、
   `I_weak = (x(x-1))`、`I_strong = (x)`、composition監査用`I_rigid = (x,2)`、
   評価`0/1/2`について、
   SD0〜SD6の型がscratch fileでelaborateする。証明完成は不要だが、
   localization map、scheme morphismの向き、global-section comparison、
   ideal sheafの型、および`HasSheafify`を`AATCommAlgCat Int`と
   `AATCommAlgCat (Polynomial Int)`について放電するnamed instance chainの型が
   未確定のまま子Issueを開始しない。
6. 実装前statement reviewで、SD0〜SD7の全signature、SD8のmaterial premise表、
   family展開後のSD9 positive / negative firingと`T` / `F` / `C`の集合契約が`Approved`になっている。

いずれかが欠ける間、このPRDは実行しない。

## Module import contract

新規moduleとdirect importを次で固定する。循環依存または未記載の横断importが必要になった場合は
実装を止め、tracking Issueでmodule DAGを再承認する。

| module | direct imports | 責務 |
| --- | --- | --- |
| `Formal.AG.Examples.StandardGeometryReferenceModels` | `Formal.AG.Examples.FiniteModel`、`Formal.AG.LawAlgebra.ClosedEquationalGeometry`、`Formal.AG.ReadingFunctoriality.Coefficient`、`Formal.AG.ReadingFunctoriality.StandardSchemeCoefficient`、`Formal.AG.ReadingFunctoriality.CoefficientGeometry`、`Mathlib.Algebra.MvPolynomial.Eval`、`Mathlib.Algebra.Polynomial.AlgebraMap`、`Mathlib.RingTheory.Localization.Away.Basic`、`Mathlib.RingTheory.ZMod`、`Mathlib.AlgebraicGeometry.Cover.Open`、`Mathlib.AlgebraicGeometry.Restrict`、`Mathlib.AlgebraicGeometry.OpenImmersion`、`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` | SD0〜SD7の固定fixture、positive / negative firing |
| `Formal.AG.StatementContractsStandardGeometryReferenceModels` | `Formal.AG.Examples.StandardGeometryReferenceModels` | `example : exact-type := exact-declaration`だけ |
| `Formal.AG.StatementContracts` | `Formal.AG.StatementContractsStandardGeometryReferenceModels` | executable contract aggregate |
| `Formal.AG` | `Formal.AG.ReadingFunctoriality`の後に`Formal.AG.Examples.StandardGeometryReferenceModels` | repository AAT aggregate。`Formal.AG.LawAlgebra`から本fixtureをimportしない |
| `Formal.AG.AxiomAudit` | `Formal.AG.Examples.StandardGeometryReferenceModels`、`Formal.AG.StatementContractsStandardGeometryReferenceModels` | 全new theoremのaudit aliasと最終標準公理検査 |

`Formal/AG`から`research/lean/ResearchLean`をimportしない。

## Statement contract

完全signatureは本PRDへ置かず、tracking Issue本文の`Statement contract index`が列挙するcomment群を唯一の正本とする。
同じsignatureをPRD、子Issue、別comment、現行docsへ正本として複製しない。tracking Issue本文は少なくとも
`Statement contract policy`、`固定対象`、`SD0`〜`SD9`のcomment URLを一意に列挙する。索引外のcommentは
statement contractに数えない。

Issue側のcontractは、実装開始前に次を完全に固定する。

- target theorem / definitionの名前、namespace、完全signature、量化対象、引数順、typeclass引数、結論
- statementが参照する新規definitionのsignatureと、body固定またはbehavior固定に使うnamed theorem
- 固定reference modelの環、principal open、ideal、evaluation、coefficient change
- SD0〜SD7のpublic target、SD8のmaterial premise分類、SD9のfamily展開済みfiring matrix
- public target集合`T`、proof-use集合`F`、support集合`C`と`T = F ∪ C`、`F ∩ C = ∅`
- executable contract、axiom audit、module DAG、focused checkへの対応

初回`Approved`は新規の未編集commentとして投稿し、次を持つ`contract revision manifest`を本文に置く。

- 索引順の各contract commentと、family展開済みSD9およびexact `T` / `F` / `C`を持つ一意な
  `expanded firing inventory` commentについて、種別、URL、database ID、`updated_at`、正規化本文SHA-256
- 対象main commit、査読者、判定

本文正規化はUTF-8、LF、末尾改行ちょうど1個とする。approval commentは`created_at = updated_at`を要求し、
編集されたapproval commentは無効とする。revision変更時は旧approval commentを編集せず、直前のapproval comment
database IDを記録した新規approval commentを追加する。approval comment自身のURL、database ID、author、
`created_at`、`updated_at`は投稿後にGitHub APIから取得し、completion snapshotで監査する。

初回`Approved`後または実装開始後にcontract変更が必要になった場合は関連実装を停止し、変更理由、旧 / 新signature、
追加・削除したpremise、`T` / `F` / `C`への影響をユーザーへ報告する。人間の明示承認前にcommentを変更しない。
承認後に該当commentを編集し、scratch elaboration、独立statement review、新しいrevision manifestを記録する。
再度`Approved`になるまで変更後contractに基づく実装を完了根拠に数えない。
Issue側の編集で数学的正典、本PRDの要求、Acceptance Criteria、Failure Contractを弱めてはならない。

`Formal/AG/StatementContractsStandardGeometryReferenceModels.lean`は、Issue contractの全public targetを
`example : <fixed type> := <implementation>`で一対一に検査する。`#check`、名前の存在、同値な弱いstatement、
aliasだけの宣言は契約達成に数えない。具体値またはconstructor provenanceを要求するdefinitionはnamed
`*_eq` theoremを持ち、同theoremもexecutable contractへ一対一に登録する。

## 数学本文との対応

| source label | fixed implementation target | 読み |
| --- | --- | --- |
| 第II部 定義3.1、4.1、6.1、7.1、8.1 | `ContextPreorderCategory`、`SelectedGeometryReading`、`AATCoverageFamily`を使う`referenceSite` / `referenceCover` | generic context / site要件をtask固有fixtureで放電 |
| 第II部 命題4.2のselected overlap部分、仮定4.3 | `referenceOverlap`、`referenceOverlap_selected` | selected finite-meet overlapとcover用pullback fieldsをtask固有fixtureで放電 |
| 第II部 定義9.1〜11.2 | `referenceRaw`、`referenceRaw_isSheaf`、restriction equations | presheaf、sheaf、restriction、descent |
| 第III部 定義4.1〜4.3、条件4.4〜4.5 | raw quotient、restriction stability、section-ring iso | typed coordinate algebraとpresentation stability |
| 第III部 定義5.1、5.2〜5.2B、6.1〜7.2 | weak / strong semantic cores、ideal sheaves、loci | violation witness、closed-equational witness idealとlawful locus |
| 第III部 定義8.1、8.5、9.2〜9.3、10.1〜10.3 | principal-open charts、overlap、cocycle、`referenceScheme` | actual decorated Scheme atlasとlocal lawful chart |
| 第III部 定理11.1 | weak / strong correspondenceと三point firing | semantic、witness、ideal、factorizationのfull correspondence |
| 第III部 定義11.3、定理11.4のideal-restriction部分 | `weak/strongLawEquationCore`、`rawCoordinate_restrict`、atom別witness equation、local ideal equation | law equation witness idealとrestriction naturalityのうち本fixtureが実装する部分 |
| Appendix A.2.1のclosed-equational law inclusion / flat coefficient base change部分 | law comparison、coefficient change | selected law readingとcoefficientのcomparison / transport |
| task固有regression | `strongIdeal_lt_rigidIdeal`、`lawComparison_comp_fires`、`coefficient_law_comparison_square` | 二つのnon-identity law inclusionと二種類のchangeを同じ固定fixtureで検査するconcrete calculation |
| Appendix A.3〜A.5 | underlying`Spec`、decoration、actual atlas | standard geometryへのdirect connection |
| Appendix A.6〜A.8 | semantic subfunctor、closed law、raw presentation | semantic predicateとideal constructionの分離 |

本PRDの`ℤ[x]` fixtureは、正典の一般構成を検査するtask固有のreference modelである。
Appendixのworked exampleを逐語的に実装したものとは記述しない。

## 問い

同じfinite Atom/context provenanceと一つの`ℤ[x]` coordinateから、次の縦断経路を
非退化に発火できるか。

~~~text
finite Atom/core
  -> selected four-context preorder and two-patch AAT site
  -> typed raw polynomial restriction system
  -> sheafified section rings
  -> actual Spec ℤ[x]
  -> proper principal-open atlas D(x), D(1-x)
  -> nonempty overlap D(x(1-x))
  -> weak/strong law-generated ideal sheaves
  -> actual nonempty proper lawful closed subschemes
  -> test morphisms x ↦ 0, 1, 2
  -> semantic / witness / ideal / factorization correspondence
  -> rigid audit ideal (x, 2)
  -> two non-isomorphic law comparisons and their non-identity composition
  -> flat coefficient change and the concrete comparison square
~~~

## 現状診断

- `FiniteModel`はfinite Atom/core由来の四context dataと二patch coverを持つが、
  canonical context preorderにはselected index order以外のreadable arrowもある。
  Part 5は同じcontext data上に`twoPatchContextIndexLe`だけを読む新しいselected preorderを作り、
  proper localization restrictionを保持する。
- `FiniteExamples.StandardArchitectureScheme.twoChartReferenceModel`はactual Scheme atlasを持つが、
  chart restrictionはisomorphismであり、`D(x)`、`D(1-x)`のproper principal opensではない。
- merged closed-equational finite exampleはstrict ideal、actual subscheme、positive / negative point、
  law comparisonを既に検証する。Part 5はそれを別名化せず、新しいprincipal-open model上で
  同じgeneric APIが一つのprovenanceから発火することを検証する。
- coefficient-change generic APIは実行開始条件3で列挙した宣言群がmerge済みであることを前提に利用する。
  本PRDはそのAPIを通じて`Int → Polynomial Int`を同じreference modelに適用し、
  law comparisonとのconcrete可換性まで固定する。
- 現行Lean treeには、tracking Issueのstatement contractが固定するprincipal-open modelをraw coordinateから
  coefficient comparisonまで一件で接続したfixture、executable contract、audit entryがまだない。
  tracking Issueのstatement contractはその未実装surfaceをSD0〜SD7のpublic target、SD8のpremise表、
  SD9のfiring matrixで固定し、本PRDは要求とModule import contractを固定する。

## アウトカム

完了時に次が成り立つ。

1. generic input certificateを持たない一件の固定reference modelがある。
2. 四context間のarrowがselected index orderと一致し、逆restrictionを生成しない。
3. three-variable / two-relation raw presentationと全restriction mapが固定され、base、left、right、
   overlap section ringが`ℤ[x]`と所定のlocalizationへactual isoで接続する。
4. `D(x)`と`D(1-x)`がproper affine openとしてjointly coverし、overlapが非空である。
5. raw restrictionとchart mapの少なくとも一つがnon-isomorphismである。
6. atom別のweak / strong law equationから`(x(x-1)) < (x)`が生成される。
7. 両idealはleft / right / overlapへ所定のlocalizationとして制限され、overlapで一致する。
8. 両idealがnonzero / properで、kernel、zero locus、affine quotient comparisonを伴う
   actual nonempty proper closed subschemeを与える。
9. 評価`0/1/2`がactual Scheme morphismとなり、semantic、witness、ideal、
   factorizationの4層で期待通りに発火する。
10. weak / strong / rigidの二段law inclusionがnon-isomorphic closed immersion、ambient triangle、
    non-identity composition firingを与える。
11. non-surjective flat coefficient changeがchart pullbackとideal transportを発火する。
12. law inclusionとcoefficient changeのconcrete comparison squareが可換である。
13. implementationとstatement contractsのpublic target集合が`T`、axiom auditが`T`中の
    全theorem、SD9のproof-use名集合が`F`と一致する。support名は`C`の要素だけであり、
    final reviewが`T = F ∪ C`、`F ∩ C = ∅`を含むSD9の全集合関係と宣言別proof-useを監査する。

## 採否規律

- `docs/aat/algebraic_geometric_theory/**`はread-onlyとし、本PRD実装で変更しない。
- 数学本文、merged Lean宣言、Mathlib actual APIをsource of truthとする。
- Scheme、atlas、localization、ideal、factorization、lawfulness、strictnessを入力fieldにしない。
- context-site coverとactual Scheme atlasを同一視しない。
- semantic predicateをideal vanishingまたはfactorizationの別名として定義しない。
- `LawfulnessIdealCorrespondenceAssumptions`、
  `LawfulnessIdealCorrespondencePackage`または同型の結論fieldを導入しない。
- existing finite exampleのalias、wrapper、repackageを新しいreference-model成果として数えない。
- `Spec`、principal open、localization、ideal sheaf、closed subscheme、pullbackには
  Mathlib actual objectを使う。
- integrated theoremだけで個別contract、negative fixture、proof-use監査を置き換えない。
- runtime状態はtracking Issueに置き、PRD本文へ進捗ログを追記しない。

## 改修要求

### R0 — dependency、API、fixed statement

- 実行開始条件を満たし、対象main commitと`T` / `F` / `C`をtracking Issueへ固定する。
- SD0〜SD7のLean blockをscratch fileで型検査する。
- module DAG、direct imports、namespace、universeを実装前に確定する。
- statement変更が必要なら実装を止め、tracking Issueの該当contract commentを改訂し、
  scratch elaborationとstatement reviewを再実行する。

### R1 — concrete raw localization model

- `ambientRing_eq`、coordinate / generator / raw variable / inverse relationのnamed `*_eq` theoremで、
  ACが参照するfixed polynomial dataをexecutable contractへ接続する。
- same finite Atom/core上に`twoPatchContextIndexLe`だけを読むselected preorder、
  overlap package、coverage requirements、two-patch coverを構成する。
- `referenceSelectedGeometryReading_eq`と`referenceSite_eq`でcontext preorder、requirements、
  overlapからselected reading / siteまでのconstructor provenanceを固定する。
- `referenceContextPreorder_le_iff`で全contextのarrowを、cover characterizationで
  exact index / patch / presieveを固定する。
- source / target coefficient categoryの`HasSheafify`をnamed instance chainで放電する。
- `referenceRawCoordinate_cases`で第四constructorがないことを直接固定し、
  `referenceRaw`をexactly三つのtyped variable、contextごとの二relation、
  piecewise variable-image restriction mapsから構成する。
- `leftIsInverted_iff` / `rightIsInverted_iff`で任意のsite object上のpredicate bodyを固定し、
  対応patchとoverlapでの成立、baseと反対patchでの不成立もpublic theoremとして固定する。
- 四`JStruct` equation、全morphismのvariable-image equation、identity、compositionを証明する。
- 同じ`rawCoordinate`が全restrictionと四localization presentationで保存されることを証明する。
- base / left / right / overlap raw algebraと所定のringのisoを構成する。
- raw presheafのsheaf conditionをconcrete matching-family calculationで証明する。
- overlap側RingHomをdivisibility、unit、`IsLocalization.Away.lift`から構成し、
  AmbientRingのcanonical mapを延長する二つの`comp_algebraMap` equationを証明する。
- sheafified restrictionと以上のcanonical localization homの四つのequationを証明する。
- arbitrary commutative ring、arbitrary localization iso、sheaf certificateを入力しない。

### R2 — actual principal-open atlas

- underlying Schemeを`Spec ℤ[x]`に固定する。
- `ambientScheme_eq`、四chart-domain iso、decoration、`referenceScheme_eq`、
  `actualOverlapIso_eq`でconstructor provenanceを固定する。
- chart mapをMathlib localization-away mapとのactual equalityで固定する。
- open immersion、joint coverage、properness、nonempty overlapを証明する。
- selected overlap contextとactual pullbackを`D(x(1-x))`へ接続する。
- decoration overlapとtriple cocycleをgeneric StandardArchitectureScheme APIで証明する。

### R3 — generated law ideal chain

- weak / strong / rigid semantic equation coreを同じ`coordinate`から構成する。
- 三coreそれぞれの`Observable`、`observableCommRing`、全morphismの`restrict`、
  `violationWitness`、`supportAtom`、`supportLawIndex`をnamed equationで固定する。
- 三scheme bridgeの`toRawPresentation`を全contextでidentity `RingEquiv`へ同定し、
  global equationが同一raw coordinate provenanceを使うことを固定する。
- bridge validity、reading validity、`RequiredClosed`、`RequiredLawIdealExact`を個別に証明する。
- atom別violation witnessとglobal equationを`x(x-1)`、追加generator`x`、constant `2`、`0`へ同定する。
- top global sections上のgenerated idealを`(x(x-1))`、`(x)`、`(x, 2)`へactual ring isoで比較する。
- ambientと六local expected idealのnamed `*_eq` theoremをexecutable contractへ登録する。
- weak / strong idealのleft / right / overlapへのrestrictionをlocalization idealへ同定し、
  pair overlap上で左右の引き戻しが一致することを証明する。
- nonzero、proper、strict inclusionをexplicit evaluation calculationから証明する。
- arbitrary `Ideal AmbientRing`をreading inputとして渡さない。
- composition監査用rigid readingのglobal idealを`(x, 2)`へ同定し、
  `(x) < (x, 2)`、properness、nonempty locusを証明する。

### R4 — actual closed geometryとpoints

- weak / strongについてgeneric `lawGeneratedIdealSheaf`、`lawfulClosedSubscheme`、
  `lawfulClosedImmersion`を直接用いる。
- weak / strong / rigidのideal sheaf、locus、immersionをnamed equationでgeneric constructorへ同定する。
- 両immersionのkernelをgenerated ideal sheafへ、rangeをzero locus supportへ同定する。
- ambient top affine open上のquotient-spectrum chartがweak / strong locus全体とのisoであることを証明する。
- weak / strong / rigid locusのnonemptyと各immersionのnon-isomorphismを証明する。
- `evaluationRingHom 0/1/2`からcontravariantなactual Scheme morphismを構成する。
- `evaluationRingHom_eq`、`evaluationPoint_eq`、`zero/one/twoPoint_eq`でring hom、
  `Scheme.Spec.map`、評価値`0/1/2`を固定する。
- weak / strong correspondence theoremをcanonical generic theoremから証明する。
- `zeroPoint_fires`、`onePoint_fires`、`twoPoint_fires`の全4層を個別に監査可能にする。

### R5 — law comparison

- `weakToStrong`、`strongToRigid`と各validityをwitness coordinate calculationから構成する。
- 二つのatom mapを全入力characterization theoremで固定する。
- generic `lawfulClosedSubschemeMap`を直接使う。
- 三comparisonをnamed equationでcanonical `lawfulClosedSubschemeMap`へ同定する。
- 両closed immersion、両ambient triangle、両non-isomorphism、identity / composition firingを証明する。
- composition firingのRHSを`ClosedEquationalLawInclusion.comp`から生成したmapとして残し、
  `lawfulClosedSubschemeMap_comp`を直接proof-useする。
- compositionの二つのlegはいずれもnon-isomorphismであることをcomponent theoremで固定する。
- point-set inclusionまたはideal orderだけでcomparison completionとしない。

### R6 — coefficient change

- `Int → Polynomial Int`のring homとflatnessをprimitive dataとする。
- `HasSheafCompose`をselected finite site上のnamed instanceとして放電する。
- generic base-change APIを直接使い、changed raw、Scheme、reading、idealを再発明しない。
- changed Scheme / weak reading / strong readingのnamed `*_eq` theoremでgeneric constructor reuseを固定する。
- left / right chart pullback、weak / strong ideal equality、changed strictnessを証明する。
- changed law comparisonをactual closed immersionとして構成し、sourceとのcomparison squareを証明する。
- changed law comparisonをnamed equationでcanonical constructorへ同定し、changed ambient triangleを証明する。
- changed law inclusionの`lawMap`と`atomMap`がsource inclusionとdefinitionally同じであることを証明する。
- non-flat`Int → ZMod 2`をnegative fixtureにする。

### R7 — negative fixturesとintegrated theorem

- duplicate chart、broken interpretation、collapsed law pair、unit ideal、
  non-flat coefficient changeをconcrete dataとして構成する。
- 各negative theoremをstatement contractとaxiom auditへ登録する。
- collapsed reading、unit ideal、non-flat mapのfixed bodyをnamed `*_eq` theoremで固定する。
- duplicate atlasはchart equationと未factorization point、broken chartはopen immersionと
  interpretation不一致まで固定する。
- integrated theoremはcomponent theoremからのみ組み立てる。
- integrated theoremはraw sheaf、local ideal、kernel / zero locus / quotient、三point全4層、
  non-identity inclusion composition、chart / ideal base change、changed inclusion map、
  changed strictness、mixed squareまで含める。
- integrated theoremを個別targetの代替にしない。

### R8 — API quality、contracts、audit、aggregate

- 新規ファイルと全new public declarationにdocstringを付ける。
- 自明でないdefinitionに`Implementation notes`を付け、採用した構成と退けた代替を記録する。
- no-unfold APIとしてring iso、restriction equation、chart equation、ideal equationを提供する。
- ACが具体値またはconstructor provenanceを要求する全defのnamed `*_eq` theoremを
  executable contractへ登録し、definitional body driftを検出する。
- SD0〜SD7から`T`、`F`、`C`をexact nameで展開し、implementationとcontractのpublic target集合、
  audit theorem集合、SD9 proof-use集合、support集合がSD9の集合契約と一致することを検査する。
- executable contractは全targetへ一対一の`example`を置き、新定理を追加しない。
- `AxiomAudit.lean`は実装moduleとcontract moduleをdirect importし、全new theoremにaudit aliasを置く。
- 最後の`#assert_standard_axioms_only AAT.AG.AxiomAudit`を維持する。
- fixtureを`Formal/AG/Examples/StandardGeometryReferenceModels.lean`へ置き、
  `StatementContracts.lean`と`Formal/AG.lean`へdirectに接続する。
- `Formal.AG.LawAlgebra` aggregateへfixtureを逆importせず、coefficient-change moduleとの循環を防ぐ。
- 既存のlive ledgerがないため、新しいMarkdown theorem ledgerを作らない。
  runtime inventoryはtracking Issue、恒久証拠はLean declaration、contract、audit、aggregateに置く。

### R9 — final premise dischargeとsource-of-truth

- completion snapshotで全premiseを再棚卸しし、SD8と突合する。
- `material_premise_ledger_delta = ∅`、`new_material_premise = ∅`を証明する。
- family表記を展開したSD9について、全`F`要素のpositive / negative proof-useを
  exact declaration、concrete input、使用箇所とともに記録する。
- 実装、contracts、audit、aggregate、CI、reviewのcommitを一致させる。
- AC1〜AC61、review、CI、merge、現行source反映を満たした後、
  現行repositoryから対象PRDへの参照を除去し、archive前条件を完成させる。

## Acceptance Criteria

- [ ] AC1: tracking Issueが対象main commit、SD0〜SD7からexact nameで展開した`T`、`F`、`C`、
  SD8のpremise表、family展開後のSD9 firing matrix、module DAG、子Issue依存を持つ。
- [ ] AC2: tracking Issue #3587本文の`Statement contract index`が列挙するcomment群だけがstatement contract正本であり、
  PRD、子Issue、別comment、現行docsに同じsignatureの正本がない。`Approved`は新規の未編集commentで、索引順commentと
  `expanded firing inventory`の種別、URL、database ID、`updated_at`、正規化本文SHA-256を持つ。completion snapshotで
  現行index URL列とmanifestのcontract URL列がexact一致し、全manifest rowが現行artifactからの再計算値と行単位で一致し、
  approval commentの`created_at = updated_at`が成立する。
- [ ] AC3: `StandardGeometryReferenceInput`または同型のgeneric certificate structureがない。
- [ ] AC4: `ambientRing_eq`、`coordinate_eq`、generator / coverのnamed equationにより、`AmbientRing = MvPolynomial Unit Int`、`coordinate = X ()`とfixed polynomial dataがexecutable contractで固定されている。
- [ ] AC5: `referenceContextPreorder_le_iff`が全contextのarrowをidentityまたはselected index orderへ同定する。
- [ ] AC6: `context_ctx`と`context_hom_iff`が四context dataをselected preorderへ正確に接続する。
- [ ] AC7: `referenceOverlap_selected`がselected overlapを`twoPatchContextMeet`へ同定する。
- [ ] AC8: `referenceSelectedGeometryReading_eq`と`referenceSite_eq`がselected reading / siteのconstructor provenanceを固定し、
  coverage requirements、cover index、patch、presieveがexisting two-patch dataと一致し、generated topologyのcoverである。
- [ ] AC9: source / target coefficient categoryの`HasSheafify`がnamed instance chainで放電される。
- [ ] AC10: `referenceRawCoordinate_cases`が三constructorを網羅し、raw variable / inverse relation /
  quotient coordinateのnamed equation、`leftIsInverted_iff` / `rightIsInverted_iff`の全入力characterization、
  positive / negative instance pair、exactly三変数 / 二relation、四`JStruct` equation、全restriction variable imageが固定され、
  四raw algebraが所定のpolynomial / localization ringへactual isoで接続し、一つの`rawCoordinate`を保つ。
- [ ] AC11: `referenceRaw_isSheaf`と全canonical component isoが証明されている。
- [ ] AC12: overlap側RingHomがgenerator divisibility、unit、Mathlib `IsLocalization.Away.lift`から構成され、二つの`comp_algebraMap` theoremと四つのsheafified restriction equationがcanonical localization homを直接同定する。
- [ ] AC13: left / right restrictionがnon-isomorphismである。
- [ ] AC14: `ambientScheme_eq`と`referenceScheme_underlying`により、underlying geometryがactual Mathlib `Spec ℤ[x]`としてexecutable contractで固定される。
- [ ] AC15: chart indexがexactly twoで、left / right contextが異なる。
- [ ] AC16: 四chart-domain isoのnamed equationとleft / right chart-map equationにより、chart mapが`D(x)`、`D(1-x)`のlocalization-away mapと一致する。
- [ ] AC17: 両chartがactual open immersionでjointly coverする。
- [ ] AC18: 両chart mapがnon-isomorphismである。
- [ ] AC19: `actualOverlapIso_eq`により、selected overlap contextがactual pullbackと`D(x(1-x))`へ指定した三段合成で接続する。
- [ ] AC20: actual overlapがnonemptyである。
- [ ] AC21: decoration overlapとtriple cocycleが証明されている。
- [ ] AC22: weak / strong / rigid atom別violation witnessとglobal equationが同じcoordinateから所定のgeneratorを与える。
- [ ] AC23: weak / strong / rigid coreの`Observable`、canonical `CommRing`、全morphismの`restrict`、
  atom別witness、support atom / law indexがnamed equationで固定される。各scheme bridgeの
  `toRawPresentation`は全contextでidentity `RingEquiv`であり、同一raw coordinate provenanceから構成されて個別にvalidである。
- [ ] AC24: weak / strong / rigid reading validity、`RequiredClosed`、`RequiredLawIdealExact`が個別theoremである。
- [ ] AC25: 四global-section isoとambient / local expected idealのnamed equationを経由し、generated top idealが`(x(x-1))`、`(x)`、`(x, 2)`へactual global-section isoで同定される。
- [ ] AC26: weak / strong idealのleft / right / overlap restrictionが所定のlocalization idealと一致し、pair overlapで左右が一致する。
- [ ] AC27: weak / strong / rigid ambient idealがnonzeroかつproperである。
- [ ] AC28: `weakIdealSheaf < strongIdealSheaf < rigidIdealSheaf`が証明されている。
- [ ] AC29: weak / strong / rigidのideal sheaf、locus、immersionのnamed equationがgeneric `lawGeneratedIdealSheaf`、`lawfulClosedSubscheme`、`lawfulClosedImmersion`へのconstructor provenanceを固定し、weak / strong locusがactual `IdealSheafData.subscheme`である。
- [ ] AC30: 両immersionのkernelがgenerated ideal sheaf、rangeがzero locus supportと一致する。
- [ ] AC31: ambient top affine open上のquotient-spectrum chartがweak / strong locus全体とのisoである。
- [ ] AC32: weak / strong / rigid locusがnonemptyで、各ambient immersionがnon-isomorphismである。
- [ ] AC33: `evaluationRingHom_eq`、`evaluationPoint_eq`、`zeroPoint_eq`、`onePoint_eq`、`twoPoint_eq`により、三pointが指定評価`0/1/2`から得るactual Scheme morphismとして固定される。
- [ ] AC34: weak / strong correspondenceがcanonical `lawfulnessIdealFactorizationCorrespondence`を直接proof-useする。
- [ ] AC35: `zeroPoint_fires`が両readingのsemantic / witness / ideal / factorizationをすべて満たす。
- [ ] AC36: `onePoint_fires`がweakの4層を満たし、strongの4層をすべて満たさない。
- [ ] AC37: `twoPoint_fires`が両readingの4層をすべて満たさない。
- [ ] AC38: semantic predicateがideal vanishingまたはfactorizationの別名ではない。
- [ ] AC39: `weakToStrongAtomMap_eq`と`strongToRigidAtomMap_eq`が全入力をcharacterizeし、`weakToStrong`と`strongToRigid`のlaw map / atom mapが既存generatorを保つ具体的inclusionとして固定される。
- [ ] AC40: 三comparisonのnamed constructor equationがgeneric law-inclusion APIへのprovenanceを固定し、`lawComparison`と`strongToRigidComparison`がactual non-isomorphic closed immersionで、各ambient triangleが可換である。
- [ ] AC41: law comparisonのidentity targetと、二つのnon-isomorphic legを持つcomposition targetがgeneric APIを直接proof-useする。
- [ ] AC42: `coefficientChange.hom = Polynomial.C`で、flatかつnon-surjectiveである。
- [ ] AC43: `coefficientChange_hasSheafCompose`がnamed instance chainで放電される。
- [ ] AC44: left / right base-changed chart squareがactual pullbackである。
- [ ] AC45: weak / strong ideal base-change equalityがgeneric theoremを直接使う。
- [ ] AC46: base-changed ideal pairがstrictである。
- [ ] AC47: changed inclusionのlaw map / atom mapがsourceと一致し、`coefficientChangedLawComparison_eq`とchanged ambient triangleがcanonical comparisonを固定し、そのmapがactual closed immersionかつnon-isomorphismである。
- [ ] AC48: `coefficient_law_comparison_square`がtask固有のconcrete compatibility calculationとして証明される。
- [ ] AC49: coefficient-change Scheme mapがnon-isomorphismである。
- [ ] AC50: SD6の各negative fixtureがfixed bodyのnamed equationまたはmap equationと、誤データのcharacterization、否定theoremを持つ。
- [ ] AC51: integrated theoremがraw sheaf、local ideal、closed geometry、三point全4層、non-identity inclusion composition、coefficient firingを同時に含む。
- [ ] AC52: integrated theoremがcomponent theoremから組み立てられ、個別contractを置き換えない。
- [ ] AC53: 全public targetにdocstring、全自明でないdefinitionに`Implementation notes`がある。
- [ ] AC54: implementationのexplicit public target name集合とexecutable contractのtarget name集合がともに`T`と一致し、
  全targetを一対一のexact-type `example`で検査して、ACが参照する全named def-body equationも覆う。
- [ ] AC55: AxiomAuditのtheorem name集合が`T`中の全theorem宣言と一致して標準公理のみを報告する。
  さらにfamily展開後のSD9で`firing_matrix_proof_names = F`、`firing_matrix_support_names ⊆ C`、
  `T = F ∪ C`、`F ∩ C = ∅`、未定義名・未割当名とも0件が検査される。
- [ ] AC56: aggregate import graphがModule import contractと一致し、`Formal.AG.LawAlgebra`からfixtureへのimportがない。
- [ ] AC57: `material_premise_ledger_delta = ∅`かつ`new_material_premise = ∅`である。
- [ ] AC58: `docs/aat/algebraic_geometric_theory/**`に差分がない。
- [ ] AC59: 統括エージェントがPR前に`lake build`を一度だけ実行し、PR後のfull buildはCIでgreenである。
- [ ] AC60: `math-lean-review`の4本がすべて合格、またはfinding全解消後に
  `review-protocol.md`に従う有資格な直接対応が記録される。
- [ ] AC61: 完了成果がmergeされ、現行source of truthへ接続している。
- [ ] AC62: `docs/guideline.md`が定めるarchive前条件として、AC1〜AC61、review、CI、merge、
  現行sourceへの成果反映、repository-wideのlive reference zeroがすべて満たされている。

AC62を満たした後、`docs/guideline.md`を正本としてcontentを変更せずPRDをarchiveする。
content-invariant move、archive文書への現行参照zero、archive文書が現行source of truthとして
参照されていないことを移動後のlifecycle checkで確認する。この移動後確認をAC62の前提にしない。

## Failure Contract

次は完了ではなく失敗である。

- fixed polynomial modelを実装中に別modelへ差し替える。
- `referenceRaw`をopaqueに残し、coordinate family、relation family、restriction variable imageを
  後段のring isoだけから推測させる。
- selected reading / siteのcontext preorder、requirements、overlapのconstructor provenanceを
  named equationで固定しない。
- `ReferenceRawCoordinate`の三constructorを個別に使うだけで、全入力cases theoremを置かない。
- `leftIsInverted` / `rightIsInverted`をselected四contextのpositive / negative例だけで固定し、
  任意のsite object上のbody characterizationを省く。
- ACが具体値またはconstructor provenanceを要求するdefをbody記載だけで固定し、
  named equationとexecutable contractへの登録を省く。
- Scheme、chart、overlap、localization iso、ideal、factorization、lawfulnessをinput fieldで受け取る。
- `referenceCover_topologyCover`だけを示し、cover index、patch、presieveを任意のadmissible familyにする。
- end-point ideal equalityだけを示し、raw coordinateとatom別law equationのcharacterizationを省く。
- semantic equation coreの`restrict`、support fields、canonical `CommRing`を固定せず、
  witnessと最終idealだけを同じにする。
- scheme bridgeの`toRawPresentation`をidentity equivalenceへ同定せず、
  validityとglobal equationだけでraw coordinate provenanceを主張する。
- overlap側restrictionを型だけのnamed RingHomへ同定し、AmbientRingのcanonical mapを
  延長するcharacterizationを省く。
- existing isomorphism chartを`D(x)`、`D(1-x)`と呼び替える。
- single chart、duplicate chart、empty overlap、all-isomorphism restrictionでatlasを発火させる。
- global idealと`IdealSheafData`を同一型のように扱い、comparison mapを省く。
- arbitrary idealをreadingへ渡し、law witnessから生成したと記述する。
- zero idealまたはunit idealだけでlaw geometryを発火させる。
- semantic lawfulnessをideal vanishing、kernel inclusion、factorizationの別名にする。
- correspondenceを結論相当certificateのfield projectionから得る。
- point-set zero locusだけでactual closed subschemeを代用する。
- global ideal equalityだけでchart restriction、overlap一致、kernel、quotient comparisonを省く。
- `evaluationPoint`だけをcharacterizeし、`zeroPoint` / `onePoint` / `twoPoint`の値固定を省く。
- law comparisonをideal orderまたはset inclusionだけで完了とする。
- law inclusionのatom mapをhelper名へ同定するだけで、helperの全入力characterizationを省く。
- composition firingをidentity mapとのcategory simplificationだけで閉じる。
- coefficient changeでchanged Scheme、reading、ideal、comparisonを自由入力する。
- coefficient-changed law inclusionの`lawMap` / `atomMap`をsource inclusionと無関係に選ぶ。
- changed law comparisonをclosed immersion / non-isomorphism / mixed squareだけでcharacterizeし、
  canonical constructor equationとambient triangleを省く。
- flatnessと`HasSheafCompose`を同一視し、一方の放電を省く。
- negative fixtureを「validity proofを与えない」だけ、または失敗原因を固定しない任意のinvalid dataで済ませる。
- integrated theorem、build成功、`#print axioms`、宣言名の存在だけで個別要求を完了扱いする。
- alias、wrapper、repackageを新しい数学的成果として数える。
- 新しいdrift-prone Markdown theorem ledgerを作る。

## 停止条件

次のいずれかが起きた時点で実装を止める。

- fixed signatureの仮定追加、結論弱化、対象変更、参照definitionのshape変更が必要になった。
- `referenceRaw`をtyped polynomial quotientとrestriction calculationから構成できない。
- raw presheafのsheaf conditionまたはsection-ring localization isoを放電できない。
- `D(x)`、`D(1-x)`のproper open coverと非空overlapをactual Scheme APIで構成できない。
- weak / strong / rigid witnessから所定のideal chainを生成できない。
- `RequiredLawIdealExact`をsemantic evaluationから放電できない。
- 三pointの4層firingに矛盾が見つかった。
- law comparisonまたはcoefficient comparison squareをactual morphism equalityとして証明できない。
- `HasSheafCompose`をselected site上で放電できず、新しい未放電仮定が必要になる。
- 数学本文に型不整合、well-definedness欠陥、独立した反例が見つかった。

停止報告には、該当SD / AC、現在のexact declaration、必要になった仮定、
最小API blocker、試したconstruction、構成できた最長のprovenance chain、
数学本文改訂の要否を記録する。

## Non-goals

- generic core-reading change、topology refinement、cover refinement、Čech / sheaf cohomology comparisonの新定理。
- generic coefficient base-change theoremまたはgeneric mixed naturality theoremの新設。
- derived scheme、Tor、stack、gerbe、higher obstructionのreference model。
- Research成果の蒸留、legacy APIの削除・rename・migration。
- ArchSig、ArchMap、tooling、websiteのfixture。
- 数学本文へのLean status、Issue、PR、declaration名の追加。
- `docs/aat/algebraic_geometric_theory/**`の編集。

## 検証

検証主体、PR前のfull build回数、diff / public-artifact / Research import scan、
PR後のCI確認は`AGENTS.md`と既存検査scriptを直接適用し、本PRDへ手順を複製しない。

実装中のfocused check:

~~~bash
lake env lean Formal/AG/Examples/StandardGeometryReferenceModels.lean
lake env lean Formal/AG/StatementContractsStandardGeometryReferenceModels.lean
~~~

## Completion evidence packet

tracking Issueの専用completion commentを次のpacketの一意な保存先とする。
最終PR commentは対象commit SHA、packetへのlink、短い判定要約だけを持ち、packet本文を複製しない。

1. **Snapshot**
   - commit SHA
   - 対象module一覧
   - SD0〜SD7からexact nameで展開したpublic target集合`T`
   - `F`、`C`のexact name展開と`T = F ∪ C`、`F ∩ C = ∅`の検査結果
   - child Issue / PR対応
2. **Statement contract**
   - 新規`Approved` commentのURL / database ID / author / `created_at` / `updated_at`、査読者、対象main commit、判定
   - 索引順contract commentと`expanded firing inventory`の種別 / URL / database ID / `updated_at` /
     正規化本文SHA-256を持つrevision manifest
   - approval commentの`created_at = updated_at`、現行index URL列とmanifestのcontract URL列のexact一致、
     completion snapshotで再計算した全manifest rowとの行単位exact一致
   - revision chainの直前approval comment database ID。初回は`none`
   - SD0〜SD7の各public declaration
   - implementation explicit public namesとcontract target namesが`T`に一致する検査
   - SD8 premise表とfamily展開後のSD9 firing matrixの位置
   - SD9の全`F`要素からlane、concrete input、positive / negative proof-use、実装箇所への対応
   - `firing_matrix_proof_names = F`、`firing_matrix_support_names ⊆ C`、未定義名・未割当名0件
   - exact-type `example`の位置
   - ACが参照する全named def-body equationと対応するexact-type `example`
   - elaboration結果
3. **Geometry provenance**
   - `AmbientRing`、coordinate、generatorのnamed equation
   - selected reading / siteのconstructor equation
   - full context-order characterizationとexact cover index / patch / presieve
   - `referenceRawCoordinate_cases`によるexactly三variable、contextごとの二relation、全restriction variable image
   - `leftIsInverted_iff` / `rightIsInverted_iff`の全入力characterizationとpositive / negative instance pair
   - raw coordinate quotient classから四section ringまでの構成
   - overlap側二RingHomのdivisibility / unit / `IsLocalization.Away.lift`構成と
     `comp_algebraMap` characterization
   - principal-open chart map equality
   - ambient Scheme、四chart-domain iso、decoration、reference Schemeのconstructor equation
   - actual overlap isoの三段合成equation
   - decoration / cocycle proof-use
4. **Law provenance**
   - 三semantic coreのObservable / canonical CommRing / restriction / support fieldsの全入力equation
   - 三scheme bridgeの全context identity `toRawPresentation` equationとvalidity
   - atom別violation witnessからglobal equationまでの構成
   - generated idealのglobal-section calculation
   - ambient / local expected idealのnamed equation
   - weak / strong idealのleft / right / overlap localizationとoverlap一致
   - kernel、zero locus、affine quotient comparison
   - weak / strong / rigid exactnessの放電
   - ideal sheaf、locus、immersionのgeneric constructor equation
   - rigid ideal `(x, 2)`のproperness、strictness
   - 二つの全入力atom-map characterization
   - 三comparisonのcanonical constructor equationとcomposed morphismまでの構成
5. **Point firing**
   - evaluation ring homとcontravariant `Scheme.Spec.map`のconstructor equation
   - `zeroPoint_eq`、`onePoint_eq`、`twoPoint_eq`による評価値`0/1/2`の固定
   - `0/1/2`それぞれのsemantic計算
   - correspondence theoremのproof-use
   - witness / ideal / factorization yes/no
6. **Coefficient firing**
   - flatnessとnon-surjectivity
   - source / target `HasSheafify` chain
   - named `HasSheafCompose` chain
   - changed Scheme / weak reading / strong readingのconstructor equation
   - chart pullback、ideal equality、strictness
   - sourceとchanged inclusionのlaw map / atom map一致
   - changed law comparisonのcanonical constructor equationとambient triangle
   - concrete comparison square
7. **Negative firing**
   - duplicate atlasのchart equationと未factorization point
   - broken chartのopen immersionとinterpretation不一致
   - collapsed law pair
   - unit ideal
   - non-flat map
   - collapsed reading、unit ideal、non-flat mapのnamed body equation
8. **Premise discharge**
   - 全premiseの三分類
   - `material_premise_ledger_delta = ∅`
   - `new_material_premise = ∅`
9. **Kernel evidence**
   - focused Lean checks
   - 統括エージェントの一回の`lake build`
   - executable contracts
   - AxiomAudit
   - changed public artifact scan
   - CI URLと結果
10. **Independent review**
    - `math-lean-review` 4査読の最終判定
    - findingがあった場合の、`review-protocol.md`に従う修正後確認または正式再査読の記録
11. **Lifecycle**
    - merged declaration / aggregateの確認
    - 現行repositoryからのPRD reference scan
    - archive予定path

archive実行後は、content-invariant moveと現行reference zeroの結果をpost-archive checkとして
tracking Issueへ追記する。これはarchive前completion evidenceと分離する。

次の組合せだけではcompletion evidenceにならない。

- build green + theorem名の存在
- `#print axioms` + docs更新
- integrated theorem一件
- aliases + inherited instances
- positive examplesだけ
- tracking Issueの自己申告だけ
