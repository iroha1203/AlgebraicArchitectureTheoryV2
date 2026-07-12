# PRD: AAT Lean Legacy Consolidation

- 作成: 2026-07-13
- 対象: `Formal/AG/LawAlgebra`の旧ringed/scheme/ideal/locus surface、全下流利用者、aggregate、statement contracts、axiom audit、Lean台帳
- 数学的正典: `docs/aat/algebraic_geometric_theory/` 第III部 定義6.2・7.1・7.2・9.1〜10.3・定理11.1、Appendix A.4〜A.8
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、`docs/aat/lean_quality_standard.md`
- tracking Issue: 未作成。Issue作成、canonical宣言一覧、依存登録が済むまで実行不可
- executable contract: `Formal/AG/StatementContractsLegacyConsolidation.lean`。移行実装と同時に作成し、CIでelaborateする
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

- tracking Issueに対象main commit、旧宣言全数、全利用箇所、最終公開名、各宣言の処置が固定されている。
- actual ringed AAT site、actual standard architecture scheme、law-generated ideal sheaf、
  lawful closed subscheme、actual factorization、canonical decorated morphism categoryがmerged済みである。
- 上記canonical declarationsのstatement contracts、axiom audit、nontrivial reference modelsがgreenである。
- tracking Issueのdependencyがすべてclosedしている。

いずれかが欠ける間、このPRDは実行しない。

## Statement Design

このPRDは新しい数学定理を追加しない。固定対象はmust-not-remain inventory、canonical ownerから
導出するprojection、既存consumer statementの維持である。別のMarkdown contractは作成しない。
実装後は`Formal/AG/StatementContractsLegacyConsolidation.lean`がcanonical projectionと
移行対象consumerの完全signatureを検査する。

### SD1 — must-not-remain inventory

最終snapshotで次の宣言、そのrename、alias、re-export、constructor、専用module、同型surfaceを残さない。

- `RingedAATTopos`
- `ChartCompatibility`、現行`ArchitectureScheme` body、`ArchitectureScheme.singleAffineSpec`
- actual gluingへ接続しない`SchemeGluingData`、`AffineReturnConditions`
- `SheafImageConstruction`
- actual factor morphismを持たない`FactorsThroughLawfulLocus`
- `LawfulnessIdealCorrespondenceAssumptions`、`LawfulnessIdealCorrespondencePackage`
- canonical ownerから導出できるringed site、chart family、lawful locus、coherence equalityを格納する
  `AATSynthesisAssumptions`、`AATSynthesisPackage`、`AATSynthesisConstructionInput`の重複field
- `AATSchReadingParameter.SchemeMorphism`と、そのidentity、composition、category-law field
- 上記を保持する`Legacy*`名、deprecated alias、exported adapter、旧module re-export

上記を設計inventoryの正本とする。tracking Issueには宣言名、module、全consumer、最終処置、削除順を
実行用checklistとして転記する。inventory外の旧routeが見つかったbatchはPRD欠陥として停止し、
Issueだけを拡張して実行を続けない。

### SD2 — canonical projection

次をcanonical ownerから導出する固定targetとする。

- `StandardArchitectureScheme.underlying`と`atlas`。別名の`toScheme`や`affineOpenCover`を追加しない。
- `lawGeneratedIdealSheaf`、`lawfulClosedSubscheme`、`lawfulClosedImmersion`、
  `FactorsThroughLawfulClosedSubscheme`と`factorization_unique`。
- normalized synthesis packageから`architectureScheme.underlying`、`architectureScheme.atlas`、
  canonical law reading、`lawfulClosedSubscheme`を導出するprojection。
- ringed siteはsynthesis packageが保持するAtom-to-ringed-site生成物から読み、schemeだけから再構成しない。
- decorated scheme morphismのunderlying Mathlib morphismを返す`AATSchMorphism.toSchemeHom`。

同じ値をstructure fieldへ重複保存したり、二つのfieldをequality certificateで再結合したりしない。
上記を公開名とし、prerequisite確定後に別名へ読み替えない。

### SD3 — consumer statement preservation

移行対象consumer theoremは旧型をcanonical型へ置換したこと以外、量化対象、material premise、結論を
変更しない。Correspondence、Cohomology、Derived、Smooth/Singular、SemanticRepair、
RepresentationAnalysis、Synthesis、AATSch、stack atlas、stratum、finite examples、
statement contracts、axiom auditの全consumerを対象とする。
canonical APIで同じ結論を証明できないconsumerはstatementを弱めず停止対象とする。

### SD4 — executable contract

`StatementContractsLegacyConsolidation.lean`にはcanonical projectionと移行対象consumerを直接右辺に置く
型検査だけを置く。削除済み旧宣言のwrapper、alias、repackageを置かない。

## 問い

standard geometry coreを唯一の公開経路にし、旧wrapper、自由な`Prop` slot、
結論の再包装、重複coherence fieldを全利用者から除去できるか。

```text
old selected packages / wrappers / duplicate fields
  -> migrate every semantic consumer to canonical owners
  -> delete old declarations and imports
  -> one standard ringed / scheme / ideal / factorization route
```

最終状態では新旧二系統を維持しない。互換alias、`Legacy*` rename、期限なしdeprecation、
旧moduleからのre-exportを残さず、standard Scheme・actual ideal sheaf・actual factorizationから下流理論を読む。

## 現状診断

- `RingedAATTopos`はType-valued sheaf、`LawAlgebraSheafPackage`、`LocallyRingedSpace`を独立fieldとして保持する。
- `ChartCompatibility`はopen immersion、overlap、cocycle等を自由な`Prop`として持ち、
  旧`ArchitectureScheme`はactual `Scheme`、joint coverage、actual overlapを要求しない。
- `singleAffineSpec`はidentity caseで旧surfaceを発火させ、複数の下流example/packageに使われる。
- `SchemeGluingData`、`AffineReturnConditions`等にも自由な`Prop`と結論相当fieldが残る。
- `SheafImageConstruction`はactual sheaf imageではなくring idealとlocal-sum equalityを保持する。
- `lawfulLocus` / `localLawfulLocus`はaffine zero-set計算には使えるが、actual closed subschemeではない。
- `FactorsThroughLawfulLocus`はpulled idealがbottomであることの再包装で、actual lift morphismとtriangleを持たない。
- `Correspondence`、Cohomology、Derived、Singularity、RepresentationAnalysisが旧set/Prop surfaceを利用する。
- `AATSynthesisPackage`はringed topos、architecture scheme、chart index/family、lawful locusを重複fieldとして持ち、
  equality fieldで再結合する。
- `AATSchReadingParameter`はscheme morphism、identity、composition、category lawsをselected dataとして再定義する。
- Bootstrap aliases、stack atlas、stratum、examples、statement contracts、axiom auditまで旧routeが広がっており、
  declarationの局所削除だけでは一本化できない。

## 最終処置

- 旧`RingedAATTopos`、旧`ChartCompatibility`、旧`ArchitectureScheme` body、`singleAffineSpec`を削除する。
- canonical standard coreが最終公開名`ArchitectureScheme`を取得する場合、全source、contract、Issueを同じ変更系列で更新し、旧型aliasを残さない。
- actual gluingへ接続しない`SchemeGluingData`、`AffineReturnConditions`等を削除する。
- `SheafImageConstruction`を削除し、actual sheaf imageとlocal computation theoremを使う。
- set-level lawful locusは必要な場合だけaffine zero-set characterization helperへ正確にrenameする。
- `FactorsThroughLawfulLocus`を削除し、actual factor morphism、composition equality、existence/uniquenessを使う。
- `LawfulnessIdealCorrespondenceAssumptions` / `LawfulnessIdealCorrespondencePackage`を削除し、
  本文 定理11.1のmaterial premiseを明示してproof-useするcanonical theoremへ全利用者を移す。
- synthesis packagesからcanonical ownerで導出できるringed site、atlas、locus、coherence equalityの重複fieldを除く。
- `AATSchReadingParameter`の独自morphism/category dataをcanonical decorated scheme categoryへ置換する。

この処置表はtracking Issueの全数inventoryで宣言単位に確定する。独立した数学的内容を持つことが判明した宣言は、
名前だけ残さずcanonical moduleへ内容を移し、fixed statementを維持する。

## 採否規律

- 数学本文はread-onlyとし、`docs/aat/algebraic_geometric_theory/**`を変更しない。
- canonical APIがmergeされる前に旧宣言を削除しない。
- 最終snapshotにexported compatibility shim、deprecated alias、`Legacy*` namespace、旧module re-exportを残さない。
- renameは`docs/aat/lean_quality_standard.md`に従い、全Lean source、GOAL、Issueを同時更新する方式を採る。
- archiveされた歴史文書は現行参照scanと改稿の対象にしない。
- set-level calculation helperをactual closed geometryの完了証拠にしない。
- G-07のstatement、proof、Research sourceを変更しない。
- target statementと参照definitionは、このPRDの`Statement Design`節を不変入力とする。

## 改修要求

### R0 — full inventory and disposition

- 旧宣言、imports、namespace alias、abbrev、docstring、statement contract、axiom audit、example、
  GOAL / Issue参照をrepo-wideに抽出する。
- 各利用をsemantic consumer、type availability、proof dependency、historical archiveへ分類する。
- 各旧宣言の最終公開名と削除順をtracking Issueに固定する。
- inventoryに無い旧利用が一つでも見つかった場合は当該batchを止め、Issueを更新する。

### R1 — canonical public names and modules

- canonical declarationsを最終namespace / pathへ配置する。
- 旧名の`abbrev`、exported adapter、deprecated aliasを最終snapshotに残さない。
- 空になった旧moduleとimportを削除し、aggregateをcanonical moduleだけへ配線する。
- public docstring、statement contract、axiom audit、Lean台帳をcanonical名へ同期する。
- source renameは全consumer更新と同じPR系列で行い、silent renameにしない。

### R2 — ringed and scheme consumers

- Synthesis、stack atlas、stratum、Evolution、Measurement、SemanticRepair、RepresentationAnalysis、examplesを
  actual standard coreへ移行する。
- chart、open immersion、coverage、overlap、coherenceをcanonical APIから取得する。
- single-affine examplesをactual `Spec` constructorで再構成する。
- downstream proofが旧structure unfoldやcompatibility-slot projectionに依存しないようAPI補題を追加する。

### R3 — ideal, locus, and factorization consumers

- `ObstructionIdeal`、`LawfulLocus`、`Correspondence`、Cohomology、Derived、Smooth/Singular、
  RepresentationAnalysisの利用をcanonical ideal sheaf、closed subscheme、actual factorizationへ移す。
- local ideal sumとaffine zero setはcanonical geometryのcalculation / characterization theoremとしてのみ使う。
- `FactorsThroughLawfulLocus`を読むfield/theoremをactual lift objectとcomposition equalityへ変更する。
- `LawfulnessIdealCorrespondenceAssumptions` / `LawfulnessIdealCorrespondencePackage`と同型の
  conclusion-shaped field structureを削除し、input dataから構成するcanonical theoremへ置換する。
- semantic lawfulnessとの対応はfixed theorem strengthを維持し、ideal vanishingをsemantic lawfulnessの定義にしない。

### R4 — synthesis package normalization

- `AATSynthesisAssumptions`、`AATSynthesisPackage`、`AATSynthesisConstructionInput`から、
  canonical ownerで導出できるringed site、chart index/family、lawful locus、coherence equalityを除去する。
- constructorはarchitecture schemeとlaw geometryからprojection / APIで値を導出する。
- packageのstatement contractsは新signatureとprojection theoremを直接突合する。
- Part VII finite examplesをnontrivial canonical inputsで再構成する。

### R5 — decorated category consolidation

- `AATSchReadingParameter.SchemeMorphism`、identity、composition、category lawsをcanonical decorated scheme categoryへ置換する。
- `AATSchMorphism`はcanonical morphismとreading preservation proofだけを持つ。
- higher Partsのanalytic contextとrepresentation familyをcanonical categoryへ移行する。
- caller-supplied morphism categoryをfieldに持つ第二経路を残さない。

### R6 — temporary adapter containment

- child PRをbuild可能にする一時adapterが必要な場合、private namespace、aggregate非公開、削除Issue必須とする。
- 一時adapterをtarget theorem、statement contract、axiom audit、reference exampleの入力に使わない。
- leaf consumerから順に移行し、全consumer移行前に旧宣言を削除しない。
- 最終snapshotでは一時adapter、削除Issue、adapter専用moduleをゼロにする。

### R7 — final deletion and audit

- `docs/archive/`とgit historyを除くcurrent repositoryで、旧宣言名、旧module path、deprecated attribute、
  adapter namespace、old constructor、duplicate equality fieldをscanする。
- statement contractsとaxiom auditから旧target entryを除去し、canonical targetsを直接検査する。
- Lean theorem indexとproof-obligation台帳をcanonical宣言へ同期する。
- canonical nontrivial reference modelsが旧adapterなしで発火することを確認する。
- `Formal/AG`からResearch moduleをimportしない。

## Acceptance Criteria

- [ ] AC1: tracking Issueのinventoryが旧宣言、transitive consumer、contract、audit、exampleを全数固定している。
- [ ] AC2: canonical prerequisitesが開始前にmergeされている。
- [ ] AC3: 旧`RingedAATTopos` structureと全参照がゼロである。
- [ ] AC4: 旧`ChartCompatibility`、旧`ArchitectureScheme` body、`singleAffineSpec`、弱いgluing surfaceと全参照がゼロである。
- [ ] AC5: 全architecture scheme consumerがactual Mathlib `Scheme`を持つcanonical coreを使用する。
- [ ] AC6: `SheafImageConstruction`と全参照がゼロで、ideal geometryがactual sheaf imageを使用する。
- [ ] AC7: `FactorsThroughLawfulLocus`と全参照がゼロで、factorizationがactual morphismとcomposition equalityを持つ。
- [ ] AC8: set-level zero locusはcalculation / characterization helperに限定され、closed subscheme completionに使われない。
- [ ] AC9: Correspondenceがcanonical ideal/factorizationを読み、semantic lawfulnessのfixed strengthを維持する。
- [ ] AC10: `LawfulnessIdealCorrespondenceAssumptions` / `LawfulnessIdealCorrespondencePackage`と全参照がゼロで、同型のconclusion-shaped field structureがcanonical名で残っていない。
- [ ] AC11: synthesis packagesにcanonical ownerから導出可能なringed/atlas/locus値とcoherence equalityの重複fieldがない。
- [ ] AC12: AATSch系のunderlying morphismとcategory lawsがcanonical decorated scheme categoryを使う。
- [ ] AC13: stack atlas、stratum、bootstrap、higher Partsがcanonical typesへ移行し、既存claimのstrengthを維持する。
- [ ] AC14: finite examplesがactual `Spec`、closed immersion、factorizationを発火し、旧adapterを使わない。
- [ ] AC15: exported shim、`Legacy*`名、旧名deprecated alias、移行専用moduleが最終snapshotにない。
- [ ] AC16: `docs/archive/`とgit historyを除くcurrent repositoryで、old imports、aggregate exports、docstrings、contracts、audit entries、Lean台帳の旧参照がゼロである。
- [ ] AC17: new/changed declarationsがno-unfold API、standard axioms、statement contractsを満たす。
- [ ] AC18: `docs/aat/algebraic_geometric_theory/**`とG-07/Research sourceに変更がなく、Research reverse importがない。
- [ ] AC19: `math-lean-review`の4本の独立査読がすべて`No major findings`である。

## Failure Contract

次は完了ではなく失敗である。

- 旧名をcanonical型のaliasにして移行完了とすること。
- `LegacyRingedAATTopos`等へrenameして弱いrouteを温存すること。
- deprecated alias、旧module re-export、一時adapterを最終snapshotに残すこと。
- set-level zero locusをactual closed subschemeと呼ぶこと。
- pulled ideal equalityを別Propで包みactual factorizationと呼ぶこと。
- `LawfulnessIdealCorrespondenceAssumptions` / `LawfulnessIdealCorrespondencePackage`をrenameし、同型のfield structureを温存すること。
- synthesis packageで値を二重保持し、equality fieldを追加して整合させること。
- AATSchに独自scheme morphism / category lawsを残したままcanonical category完成とすること。
- single-affine identity、zero ideal、empty locusだけで移行後exampleを済ませること。
- contracts / auditだけを新名へ変更し、proof consumerを旧routeに残すこと。

## 停止条件

- canonical prerequisitesが未merge、または最終公開名・処置表が未固定である。
- consumerのfixed theoremをcanonical APIで表すためにstatement weakening、material premise追加、結論相当fieldが必要になる。
- actual factorizationへの移行にMathlib API blockerがあり、lift morphismまたはcomposition equalityを構成できない。
- canonical decorated categoryが既存AATSch consumerの必要dataを表せず、独立morphism carrierが不可避である。
- 旧宣言にcanonical coreへまだ移されていない独立した数学的内容が見つかる。
- nontrivial canonical exampleを維持できず、identity、zero、empty caseだけになる。

停止報告には、該当AC、旧宣言とconsumer、fixed signature、必要な追加premise、
試したcanonical route、最小blocker、残すべき数学的内容を記録する。

## Non-goals

- G-07、conormal sequence、Čech connecting class、first-order liftの本体蒸留。
- reading functorialityの新定理追加。mergedしたcanonical comparisonへの移行だけを扱う。
- stack、gerbe、derived、cotangentの数学的強化。
- legacyと無関係な既存weak surfaceのrepo-wide一括改修。
- 数学本文へのLean status、Issue、PR、declaration名の追加。

## 検証

検証手順と実行主体は`AGENTS.md`の「よく使う検証」「PR前の確認」と
`docs/aat/guideline.md`を直接適用する。task固有の追加検査は、tracking Issueで固定した旧宣言名、
module path、deprecated alias、adapter namespace、duplicate field、old contract/audit entryが
`docs/archive/`とgit historyを除くcurrent repositoryでno-hitであることと、canonical reference modelsが
旧routeなしで発火することの確認である。
