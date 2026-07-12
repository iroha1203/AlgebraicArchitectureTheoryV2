# PRD: AAT Lean Reading Functoriality

- 作成: 2026-07-13
- 対象: `Formal/AG`のreading parameter、law inclusion、coverage refinement、coefficient base change、comparison morphism、examples、aggregate、statement contracts、axiom audit、Lean台帳
- 数学的正典: `docs/aat/algebraic_geometric_theory/appendix.md` A.2〜A.2.1、第II部 §5.3 Refinement・§5.4 Base Change・定義7.1〜7.2、第III部のscheme relativity・ideal restriction
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、`docs/aat/lean_quality_standard.md`
- tracking Issue: 未作成。Issue作成と依存登録が済むまで実行不可
- executable contract: `Formal/AG/StatementContractsReadingFunctoriality.lean`。実装と同時に作成し、CIでelaborateする
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

- tracking Issueが作成され、対象main commit、target一覧、material premise表、子Issue依存が登録されている。
- 同Issueが、Atom由来ringed site、actual standard architecture scheme、law-generated `IdealSheafData`、
  lawful closed subscheme、law inclusion comparisonを提供するmerged宣言へのdependencyを持つ。

いずれかが欠ける間、このPRDは実行しない。

## Statement Design

この節を本PRDのfixed statement designとする。別のMarkdown contractは作成しない。
target名、入力、結論、参照definitionを実装中に変更しない。実装後は
`Formal/AG/StatementContractsReadingFunctoriality.lean`が各targetの実装signatureを直接検査する。

### SD1 — Readingとelementary change

`Reading`はvocabulary、law universe、coverage、coefficient ring、selected witnesses、selected axesと、
既存Atom/site/coefficient APIへのtyped接続だけを持つ。site、scheme、ideal、cohomology class、
comparison mapをfieldに持たない。

次の三つを別の型として固定する。

- `LawExtension p q`: law inclusion、selected witness preservation、他parameterの一致または明示transport。
- `CoverageRefinement p q`: actual cover refinement map、witnessとcoefficient sheafの保存。
- `FlatCoefficientChange p q`: ring hom、flatness、coordinate/witness compatibility。

各型に`refl`、`comp`、source/target projection、extensionalityを置く。ideal inclusion、cochain map、
base-change morphismをelementary changeのfieldに先取りしない。

### SD2 — law extension target

closed-equational lawに対しては既存の`ClosedEquationalLawInclusion`、
`lawGeneratedIdealSheaf_mono`、`lawfulClosedSubschemeMap`とそのclosed immersion、ambient triangle、
identity/compositionを再利用する。`LawExtension`には、このcanonical inclusionへ移す
`toClosedEquationalLawInclusion`だけを置き、同じ比較射を別名で再実装しない。
これらを`LawExtension`のfield射影だけで閉じない。

### SD3 — coverage refinement target

`CoverageRefinement.cechCochainMap`、differentialとの可換性、cover-relative Čech cohomology map、
本文由来のcomparison成立条件の下でのsheaf cohomology comparison map、
`obstructionClass_naturality`を固定targetとする。
結論はAppendix A.2.1のcomparison mapまでとし、isomorphism、coverage-independent equality、
無条件のČech/sheaf同一視を追加しない。

### SD4 — flat coefficient change target

`FlatCoefficientChange.coordinateAlgebraMap`、`obstructionIdealMap`、base-changed lawful closed geometryから
変更後のlawful closed geometryへの`lawfulLocusMap`、`lawConflictMap`、
必要な有限性・exactnessの下での`cohomologyClassMap`を固定targetとする。
追加仮定なしのisomorphism、Cartesian square、任意次数のcomparison equalityを結論にしない。

### SD5 — executable contract

`StatementContractsReadingFunctoriality.lean`には各targetを直接右辺に置く型検査だけを記述する。
新しいtheorem、wrapper、alias、proof helperを置かない。三種のchangeを混ぜたcoherenceは本PRDの
fixed targetに含めない。

## 問い

相対parameter

```text
p = (V, U, J, k, selected witnesses, selected axes)
```

の変更を、結論相当comparison dataを入力せず、標準幾何上のactual morphismとchain mapとして構成できるか。

```text
law extension
  -> ideal inclusion
  -> reverse lawful-closed-geometry morphism

coverage refinement
  -> site / cover comparison
  -> Čech cochain map
  -> cohomology comparison under stated hypotheses

flat coefficient change
  -> coordinate algebra base change
  -> ideal and closed subscheme base change
  -> Tor / cohomology comparison maps under stated hypotheses
```

完成対象は、任意の`ReadingHom`にcomparison morphismやcohomology mapをfieldとして持たせることではない。
law、coverage、coefficientの各変更から、Appendix A.2.1が述べるcomparison mapを構成する。
identity・compositionはelementary changeと生成mapのAPI整合であり、独立した数学claimとして扱わない。

## 現状診断

- 数学本文は`Reading`をvocabulary、law universe、coverage topology、coefficient ringと追加選択の組として置く。
- law inclusionに対するlocal ideal inclusionは現行APIの一部にあるが、actual lawful closed subschemeの比較へ統合されていない。
- coverageはactual Grothendieck topologyへ接続されているが、reading変更としてのsite functor、cover refinement、
  Čech cochain map、composition coherenceは中心APIになっていない。
- coefficient ring mapは各部で個別に現れるが、coordinate algebra、ideal sheaf、closed subscheme、Tor、cohomologyの
  comparisonを同じbase-change provenanceで追跡するAPIはない。
- `AATSchReadingParameter`はscheme morphism型、identity、composition、各compatibility predicateを選択済みfieldとして持ち、
  standard scheme morphismから生成されるparameter changeではない。
- 上層packageにはselected comparison dataやcompatibility certificateを格納するsurfaceがあり、
  parameter functorialityの生成定理の代用にはならない。

## アウトカム

完了時に次が成り立つ。

1. `Reading`の必須parameterと追加選択がtyped dataとして定義される。
2. law extension、coverage refinement、flat coefficient changeが別々のelementary changeとして定義される。
3. 各elementary changeにidentity、composition、extensionality、source/target APIがある。
4. law extensionからideal inclusionとlawful closed subscheme間のactual closed immersionが構成される。
5. coverage refinementからactual cover comparison、Čech cochain map、cover-relative Čech cohomology comparison、
   本文が要求する仮定の下でのsheaf cohomology comparison mapが構成される。
6. flat coefficient changeからcoordinate algebra、ideal sheaf、lawful closed subschemeのbase-change comparisonが構成される。
7. 本文が挙げるTor conflictとcohomology classのbase-change comparison mapが、明示したflatness・finiteness・exactness仮定の下で構成される。
8. strict law extension、strict coverage refinement、nontrivial flat coefficient changeの各reference exampleが発火する。

## 採否規律

- 数学本文はread-onlyとし、`docs/aat/algebraic_geometric_theory/**`を変更しない。
- law、coverage、coefficientの変更を一つの万能structureへ押し込み、comparison結果をfieldで受け取らない。
- topology orderの記号的向きに依存せず、coverを送るactual functorまたは包含定理でrefinementを固定する。
- coefficient base changeはring homだけでなく、本文が要求するflatnessと対象ごとのfiniteness/exactnessを明示する。
- Čech comparisonとsheaf cohomology comparisonを同一視しない。後者は必要なcomparison theoremがある場合だけ証明する。
- Appendix A.2.1がcomparison mapだけを述べる箇所で、isomorphism、Cartesian square、mixed-change coherenceへ強めない。
- `AATSchReadingParameter.SchemeMorphism`のようなcaller-supplied morphism型をstandard comparisonの代用にしない。
- target statementと参照definitionは、このPRDの`Statement Design`節を不変入力とする。

## 改修要求

### R0 — fixed statementと既存comparison APIの監査

- tracking Issueに対象main commitを固定する。
- Appendix A.2.1の各comparison claimを、入力、本文由来仮定、出力、現在のLean declarationへ分解する。
- law inclusion、coverage refinement、coefficient base changeに関係する現行APIとResearch受理成果を検索する。
- 全material premiseを本文由来、放電済み、未放電へ分類する。
- `docs/aat/research_evidence_index.md`とResearch sourceを検索し、同主題の受理成果と下限をtracking Issueに記録する。

### R1 — Reading parameter

- `V`、`U`、`J`、`k`とselected witness / signature-axis readingを持つparameterを定義する。
- 各fieldを既存Atom vocabulary、law universe、AAT site、coefficient ring、decoration APIへ接続する。
- site、scheme、ideal、cohomology classを`Reading`の入力fieldにしない。これらはparameterから構成されるgeometry側に置く。
- 必須parameterだけのcoreと追加selectionを分離し、下流が不要なprofile dataへ依存しないAPIにする。

### R2 — elementary reading changes

- law universe inclusionとwitness preservationを持つ`LawExtension`を定義する。
- context category上のcoverage refinementとchosen witness / coefficient preservationを持つ`CoverageRefinement`を定義する。
- coefficient ring hom、flatness、coordinate/witness compatibilityを持つ`FlatCoefficientChange`を定義する。
- identity、composition、source、target、extensionalityをdefinition qualityのAPI補題として各型で証明する。
- ideal inclusion、closed immersion、cochain map、base-change mapをelementary changeのfieldに入れない。

### R3 — law extension functoriality

- selected law witness generatorsから`I_U ≤ I_U'`を証明する。
- ideal inclusionから`Flat_U'(X) ⟶ Flat_U(X)`をactual scheme morphismとして構成する。
- comparison morphismがclosed immersionであり、ambient schemeへのtriangleが可換であることを証明する。
- identity extensionがidentity morphism、composed extensionがcomparison morphismのcompositionに一致することを証明する。
- semantic lawfulnessのrestriction theoremは、本文 定理11.1と同じpremiseを使って証明する。

### R4 — coverage refinement functoriality

- refinementがcontext category、generated topology、selected coverへ与えるactual comparisonを構成する。
- chosen witness familyとcoefficient sheafがcomparisonに沿って保存されることをtyped mapと可換性で表す。
- refined coverへのČech cochain mapをdegreewiseに構成し、differentialとの可換性を証明する。
- induced cover-relative Čech cohomology mapを証明する。
- 本文由来のacyclicity、Leray、cofinality等を明示し、cover-relative Čech comparisonから
  sheaf cohomology comparison mapへ接続する。必要仮定をproof bodyで使う。
- obstruction classのnaturalityは、class representative、cochain map、quotient mapから証明し、class equalityをfieldとして受け取らない。

### R5 — flat coefficient base change

- coordinate algebraに対する`k ⟶ k'`のscalar extensionを構成する。
- structural relation idealとlaw witness idealのextensionを生成元から構成する。
- base-changed affine schemeとscheme fiber productのcanonical comparisonを構成する。
- law-generated ideal sheafのpullbackとbase-changed witness idealの一致を証明する。
- lawful closed subschemeのbase-change comparison morphismを構成する。
- identity ring homとcomposite flat ring homに対する生成comparisonのAPI整合を証明する。

### R6 — Tor conflict and cohomology base change

- 本文が要求するflatness、finite presentation、coefficient compatibility、exactnessをtargetごとに固定する。
- Tor conflict comparisonをMathlibのtensor / Tor APIまたは既存AAT comparisonへ接続する。
- coefficient sheafとČech complexのscalar extensionを構成し、degreewise comparisonを証明する。
- 必要なexactnessの下でcohomology base-change mapを証明する。
- general base-change theoremを利用できない場合、finite selected regimeの明示的complexに対象を固定する。
- comparison mapやisoをcertificate fieldとして入力し、その存在を結論にする経路を作らない。

### R7 — nontrivial reference examples

- strict law inclusionによりidealが真に増え、lawful closed subschemeが真に小さくなるexampleを構成する。
- 複数coverと非恒等refinement mapを持ち、Čech cochain mapが非恒等に発火するfinite exampleを構成する。
- `Int ⟶ Rat`等のnontrivial flat ring homでcoordinate algebra、proper ideal、closed subscheme base changeが発火するexampleを構成する。
- Tor conflictとfinite cohomology comparisonの双方を同じcoefficient changeから発火させる。
- identity、zero ideal、zero complexだけのexampleを主証拠にしない。

### R8 — integration and audit

- 新moduleを`Formal/AG.lean`へ接続する。
- target declarationsとexamplesをstatement contractsとaxiom auditへ追加する。
- current `AATSchReadingParameter`等には、standard comparisonからsoundに構成できる場合だけcomparisonを提供する。
- Lean theorem indexとproof-obligation台帳を必要範囲で同期する。
- `Formal/AG`からResearch moduleをimportしない。

## Acceptance Criteria

- [ ] AC1: executable contractがlaw extension、coverage refinement、flat coefficient changeの実装signatureを直接参照する。
- [ ] AC2: `Reading`が本文の必須parameterを既存AAT型へ接続し、構成結果を入力fieldに持たない。
- [ ] AC3: law extension、coverage refinement、flat coefficient changeが別々のtyped dataである。
- [ ] AC4: 各elementary changeのidentity、composition、extensionalityがdefinition qualityのAPI補題として証明される。
- [ ] AC5: law extensionからideal inclusion、reverse lawful-locus morphism、closed immersion、可換triangleが構成される。
- [ ] AC6: coverage refinementからactual cover comparisonとČech cochain mapが構成され、differentialと可換である。
- [ ] AC7: coverage comparisonのcover-relative Čech cohomology map、obstruction class naturality、
  本文由来仮定の下でのsheaf cohomology comparison mapがcochain-level constructionから証明される。
- [ ] AC8: flat coefficient changeからcoordinate algebra、law ideal sheaf、lawful closed subschemeのbase-change comparisonが構成される。
- [ ] AC9: lawful closed subschemeのbase-change comparison morphismがlaw ideal comparisonから構成される。
- [ ] AC10: Tor conflictとfinite cohomologyのbase-change mapが、それぞれ本文由来のflatness・finiteness・exactnessを使って証明される。
- [ ] AC11: law comparison morphismのidentity/composition一致、semantic lawfulness restriction、
  coefficient comparisonのidentity/composition API整合が証明される。
- [ ] AC12: Research検索、material premise三分類、各premiseのproof-useがtracking Issueとレビューで確認される。
- [ ] AC13: strict law extension、nonidentity coverage refinement、nontrivial flat coefficient changeがそれぞれ非退化exampleで発火し、
  Tor conflictとfinite cohomology comparisonは同一coefficient changeから導出される。
- [ ] AC14: comparison morphism、cochain map、base-change map、class equalityを結論相当fieldから射影する主経路がない。
- [ ] AC15: target declarationsとexamplesがstandard axiomsのみを使用し、statement contractsとaxiom auditがgreenである。
- [ ] AC16: `docs/aat/algebraic_geometric_theory/**`に変更がなく、Lean台帳だけが必要範囲で同期される。
- [ ] AC17: `math-lean-review`の4本の独立査読がすべて`No major findings`である。

## Failure Contract

次は完了ではなく失敗である。

- law、coverage、coefficientの変更を区別しない万能`ReadingHom`。
- ideal inclusion、closed immersion、cochain map、cohomology map、base-change isoをinput fieldとして受け取ること。
- topology refinementを名称またはorder relationだけで済ませ、actual cover mapを構成しないこと。
- Čech comparisonを無条件にsheaf cohomology comparisonと呼ぶこと。
- flatness、finite presentation、exactnessを使わずbase-change isoを主張すること。
- Appendix A.2.1のcomparison mapを、本文に根拠のないisomorphism、Cartesian square、mixed coherenceへ強めること。
- identity、constant map、zero ideal、zero complexだけでfunctorialityを発火させること。
- current selected compatibility packageのfield projectionまたはrenameだけでtargetを閉じること。
- build成功またはdeclaration名の存在だけを完了根拠にすること。

## 停止条件

- 数学本文のparameter functorialityにLean実装と独立した反例、型不整合、well-definedness欠陥が見つかった。
- fixed statementを弱める、本文にないmaterial premiseを追加する、結論相当fieldを追加する必要が生じた。
- actual lawful closed geometryまたはsite comparisonをmerged standard APIから構成できない。
- coverage refinementからcochain mapを構成するためにclass equalityを入力する必要が生じた。
- flat coefficient changeからideal / closed subscheme comparisonを構成できず、arbitrary isoが必要になる。
- nontrivial exampleが構成できず、identityまたはzero exampleだけが残る。

停止報告には、該当AC、最小の反例またはAPI blocker、試したcomparison route、未放電仮定、
本文改訂の要否、finite selected theoremへ固定できるかを記録する。

## Non-goals

- G-07、conormal sequence、first-order connecting class、lift torsorの本体蒸留。
- arbitrary derived category、general stack、gerbe、higher obstructionのfunctoriality。
- law / coverage / coefficient change間の一般mixed coherence theorem。
- source extraction、ArchMap、ArchSig、FieldSigの変更。
- current legacy surfaceの一括削除。
- 数学本文へのLean status、Issue、PR、declaration名の追加。

## 検証

検証手順と実行主体は`AGENTS.md`の「よく使う検証」「PR前の確認」と
`docs/aat/guideline.md`を直接適用する。task固有の追加検査は、elementary changeのAPI laws、
cochain-map differential compatibility、obstruction class naturality、lawful closed subscheme comparison、
Tor / finite cohomology base-change mapをstatement contractsとaxiom auditが直接参照していることの確認である。
