# Research→本体 昇格 statement contract

## 目的

Research Leanの受理statementを本体へ昇格するとき、本体側statementがResearch元の全結論を
覆い、material premiseを追加していないことをfail-closedに検査するための固定contractである。

この文書は昇格auditの恒久source of truthである。個別PRD、Issue、PR本文はこのcontractを
参照し、別の弱い判定規則を定義しない。

実装状態: 未実装。#3201で実装し、実装とnegative fixtureが受理されるまで
`ported`判定の新しい完了根拠には使わない。

## 適用対象

- `docs/aat/research_evidence_index.md`で`ported`と判定するResearch成果
- evidence indexが未整備の場合に、Research theorem index、reports、本体側対応記述から
  本体対応候補として抽出したResearch成果
- Research元statementを本体へ新規に昇格するPR
- 既存`ported`行を再監査するbackfill

Research package内のaudit-only moduleがResearch元と本体先をimportする。本体moduleは
Research packageまたはaudit moduleをimportしない。

適用対象は非空でなければならない。空のindex表を根拠に「対象0件、監査完了」と判定しない。

## 固定対象とmanifest

audit対象は`research-lean/audit/promotion-manifest.tsv`に次の列で固定する。

```text
research_decl	migration_record	body_decls	audit_decl	research_file	body_files	contract_ref
```

manifestの各行はResearch元1 declarationに対応する。`body_decls`と`body_files`は
comma-separated listとし、全列の空欄を許さない。`research_decl`と`audit_decl`はmanifest内で
一意とする。`research_file`、`body_files`、`contract_ref`はrepository現行面の実在fileに限り、
Research file、Formal本体file、statement contractという列の役割と一致しなければ失敗させる。
`migration_record`は旧module prefixを含まないstable record keyであり、R3/R4のmigration
manifestに同じkeyと移動前後のsource/type/value/axiom digestが存在しなければ失敗させる。
重複行、stale path、役割外path、manifest 0行をすべて失敗させる。

最初の必須行は次である。

- Research元:
`ResearchLean.AG.QualitySurface.SemanticRepairCechGrounding.SemanticRepairCoverRelativeCochainRealization.CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis.LawEquationDefectSemanticAtomLawInputBoundarySource.lawEquation_constructs_groundedComparisonPacket`
- migration record:
  `R4/QualitySurface/SemanticRepairLawEquationGroundedPacket.lean#lawEquation_constructs_groundedComparisonPacket`
- 本体先:
  `AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_groundedComparisonPacket_finiteFree`
- 本体statement contract:
  `docs/aat/statement_contracts/semantic_repair_part_x.md`と
  `Formal/AG/StatementContractsSemanticRepairPart10.lean`
- audit declaration:
  `ResearchLean.AG.Audit.SemanticRepair.lawEquationGroundedComparisonPacket`

Research元とaudit declarationの固定signatureは次のLeanコードである。移動時にはnamespaceと
module prefixだけを`ResearchLean.AG`へ機械的に置換し、残るidentifier、universe、binder、
premise、結論を変更しない。本体先の完全signatureは上記既存statement contractを正本とする。
下記固定signature、移動前後のtype digest、`#assert_promotion_signature`の3つを独立に照合し、
Research元とaudit declarationを同時に弱めても合格させない。

```lean
universe v w r

namespace ResearchLean.AG.Audit.SemanticRepair

open CategoryTheory
open ResearchLean.AG.QualitySurface
open ResearchLean.AG.QualitySurface.SemanticRepairSheafH1
open ResearchLean.AG.QualitySurface.SemanticRepairTrueSheafH1
open ResearchLean.AG.QualitySurface.SemanticRepairCechGrounding
open ResearchLean.AG.QualitySurface.SemanticRepairCechGrounding.SemanticRepairCoverRelativeCochainRealization
open ResearchLean.AG.QualitySurface.SemanticRepairCechGrounding.SemanticRepairCoverRelativeCochainRealization.CoverRelativeCechGeneratedSemanticCoefficient
open ResearchLean.AG.QualitySurface.SemanticRepairCechGrounding.SemanticRepairCoverRelativeCochainRealization.CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis
open ResearchLean.AG.QualitySurface.SemanticRepairCechGrounding.SemanticRepairCoverRelativeCochainRealization.CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis.LawEquationDefectSemanticAtomLawInputBoundarySource

variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {semanticSite : SemanticRepairSite.{r, v} U.Atom}
variable {S : AAT.AG.Site.AATSite A}
variable {coverGeometry : FinitePosetAtomLawCoverGeometry S}
variable {G : SemanticLawEquationWitnessIdealGeometry semanticSite S}
variable {skeleton :
  SourceSectionFreeSkeleton
    (semanticSite := semanticSite) (S := S)
    (regime := lawEquationRegime coverGeometry G)
    (C := lawEquationStandardComplex coverGeometry G)
    (Ob := G.lawEquationObstructionSheaf)
    (K := lawEquationCechComplex coverGeometry G)}

theorem lawEquationGroundedComparisonPacket
    (D :
      LawEquationDefectSemanticAtomLawInputBoundarySource coverGeometry G
        skeleton)
    (semanticCover : SemanticRepairCover.{r, v, w} semanticSite)
    (chartSimplex :
      semanticCover.CoverChart ->
        (AAT.AG.Cohomology.finitePosetCoverRelativeCover
          (lawEquationStandardComplex coverGeometry G)).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (AAT.AG.Cohomology.finitePosetCoverRelativeCover
            (lawEquationStandardComplex coverGeometry G)).simplex 1)
    (tripleSimplex :
      (Sigma fun triple :
        semanticCover.CoverChart × semanticCover.CoverChart ×
          semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (AAT.AG.Cohomology.finitePosetCoverRelativeCover
            (lawEquationStandardComplex coverGeometry G)).simplex 2)
    (hholds :
      D.toSupportOnlySemanticAtomLawInputBoundarySource.displayedRequiredLawsHoldOn
        D.objectOfLocalInput) :
    let surface :=
      lawEquationCurrentG06InputSurface coverGeometry G semanticCover
        chartSimplex overlapSimplex tripleSimplex
    let source := D.toCoverRelativeBaseRestrictionSource
    let restrictionSource :=
      source.toRestrictionRealizedBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
    let boundarySource :=
      restrictionSource.toBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
    let freeSource := boundarySource.toFreeSemanticAtomLawInputBoundarySource
    let geometry :=
      CoverRelativeCechSemanticAtomLawInputBoundaryGeometry.ofFreeSemanticAtomLawInputBoundarySource
        freeSource
    let boundary :=
      geometry.toBoundaryGeneratedCoefficient
        (K := surface.K) source.c0Order source.c1Order
    let generated := boundary.toGeneratedCoefficient
    let canonical :=
      CoverRelativeCechGeneratedCanonicalH1Envelope.defaultObservationEnvelope
        (site := semanticSite) generated
    let envelope := canonical.toGeneratedEnvelope
    let realization := envelope.toCochainRealization
    (forall sigma :
      (AAT.AG.Cohomology.finitePosetCoverRelativeCover
        (lawEquationStandardComplex coverGeometry G)).simplex 0,
      source.toPrimitive sigma =
        G.lawEquationObstructionSheaf.carrier.toPresheaf.map
          (homOfLE
            ((lawEquationRegime coverGeometry G).simplexOverlap_le_patch 0
              sigma 0)).op
          (D.toSupportOnlySemanticAtomLawInputBoundarySource.interpret
            ((lawEquationRegime coverGeometry G).simplexIndices 0 sigma 0)
            (D.toSupportOnlySemanticAtomLawInputBoundarySource.input
              ((lawEquationRegime coverGeometry G).simplexIndices 0 sigma 0)))) /\
      D.toSupportOnlySemanticAtomLawInputBoundarySource.displayedRequiredLawRestrictionEvaluator
        D.objectOfLocalInput /\
      atomLawOverlap_sourceSectionFreeSkeleton_sourceC0CechZero coverGeometry
        G.toSemanticAtomLawAdditiveCoefficientGeometry skeleton
        D.toSupportOnlySemanticAtomLawInputBoundarySource /\
      Nonempty
        (SelectedSemanticCoefficientDirectRealizationLayer
          (E := envelope.toEnvelope)
          (additive := envelope.toAdditiveCechH1Data) surface) /\
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
        (E := envelope.toEnvelope)
        (additive := envelope.toAdditiveCechH1Data)
        (coverBridge := surface.coverBridge)
        (K := surface.K) /\
      Nonempty
        (SemanticRepairCoverRelativeCochainRealization
          envelope.toAdditiveCechH1Data surface.K) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          realization.toH1Comparison) /\
      canonical.residualBoundary /\
      SemanticRepairH1Zero envelope.toEnvelope /\
      SemanticRepairAdditiveH1Zero envelope.toAdditiveCechH1Data

end ResearchLean.AG.Audit.SemanticRepair
```

## 昇格audit declaration

`ported`と判定する各Research成果について、Research package内のaudit-only moduleに名前付き
declarationを置く。

declaration名はmanifestの`audit_decl`、完全signatureはmanifestの`research_decl`の
environment上のdeclaration typeそのものを固定入力とする。audit実装が書いたtypeとの一致は
`#assert_promotion_signature`で判定し、placeholderや自然言語要約をsignatureとして扱わない。

固定条件:

- binders、universe、typeclass、explicit premise、結論の全conjunctはResearch元と一致する。
- proof bodyは本体側declarationと許可されたmathlib / core依存だけを使う。
- Research側の型・definitionをstatementで参照する必要がある場合は許可listへ宣言できる。
- Research側theorem・lemma・instanceのproof依存は許可しない。
- audit declaration自身を本体からimportしない。
- Research元statementがpacket / structureを返す場合、全fieldを個別に対応させる。
- certificate / structure / typeclass fieldに結論相当の情報を移した場合は不合格とする。

### 必須pairの入力bridge

最初の必須pairでは、固定signatureのaudit declaration
`ResearchLean.AG.Audit.SemanticRepair.lawEquationGroundedComparisonPacket`自身を
Research入力から本体routeへのbridgeとする。弱いsignatureのhelper bridge、選択済み入力、
追加同一視premise、入力対応を保持するcertificateを別途受け取らない。

`research-lean/audit/input-manifest.tsv`は次の列を持つ。

```text
audit_decl	research_binder	body_target	construction	preservation_obligation	discharge_decl
```

全Research binderを1回以上登録し、行欠落、未使用binder、同じbinderのdummy use、
未証明preservation obligation、audit valueのtransitive dependency closureにない
`construction` / `discharge_decl`を失敗させる。最初の必須pairは次を固定する。

| Research binder | 本体routeへの対応 | preservation obligation |
| --- | --- | --- |
| `U`, `A`, `S` | 同じcarrier / object / site | 対象、law universe、context preorderのdefinitional equality |
| `semanticSite` | `LawEquationSemanticAtomInputBody` | `Component := U.Atom`、`project := id`、`sourceTraceToken := semanticSite.sourceTraceToken`を固定 |
| `coverGeometry` | `Site.FinitePosetCoverGeometry` | cover index、patch、canonical tuple overlapを同じgeometryから構成 |
| `G` | `LawEquationWitnessIdealGeometryBody` | core、support visibility、`quotientIsSheaf`の生成元を保持 |
| `skeleton` | 結論再構成で使う同一binder | c0/c1 order、atom、law indexと各proof fieldを生成・選択で置換しない |
| `D` | `FinitePosetLawEquationDefectSourceBody` | LocalInput、input、support、object、defect、`holds_defect_mem`を保持 |
| `semanticCover` | 本体semantic cover | chart / overlap / triple overlapの型を保持 |
| `chartSimplex`, `overlapSimplex`, `tripleSimplex` | 本体のdegree 0/1/2 map | domain / codomainと選択写像を保持 |
| `hholds` | 本体のrequired-law premise | 追加lawfulnessなしで結論1–3に実使用 |

`skeleton`を固定値、order-free生成値、選択済みwitnessへ置換する実装は、最終型が同じでも
不合格とする。入力変換が新しい数学的同一視を要する場合は、その完全signatureをこのcontractへ
先に追加して再査読し、Issue内で暗黙に導入しない。

各`construction` declarationの型は、固定audit signatureのResearch binder telescopeのうち
必要なprefixだけを同じ順序・同じ型で受け、表の「本体routeへの対応」に記した型を返す。
追加のexplicit premise、typeclass、certificate引数を許さない。この機械生成expected typeとの
definitional equalityを`#assert_promotion_inputs`が検査し、自然言語表だけで一致判定しない。

`research-lean/audit/input-field-manifest.tsv`は次の列を持つ。

```text
audit_decl	construction_decl	target_field	source_expression	field_equation	discharge_decl
```

各constructed body structureの全fieldをenvironmentから列挙し、manifestと双方向一致させる。
行欠落・重複、target fieldの定数置換、source expression drift、field equationの型不一致、
closure外dischargeを失敗させる。最初の必須pairのsemantic inputは次の3行をlock値とする。

| target field | source expression | field equation |
| --- | --- | --- |
| `Component` | `U.Atom` | definitional equality |
| `project` | `fun atom : U.Atom => atom` | `rfl` |
| `sourceTraceToken` | `semanticSite.sourceTraceToken` | `rfl` |

`Component := PUnit`、constant project、atom identityを失うquotient / choiceを許さない。
他のconstructed inputもtarget structureの全fieldについて同じfield-level provenanceを要求する。

### 必須pairのconjunct proof-use

`research-lean/audit/conjunct-manifest.tsv`は次の列を持つ。

```text
audit_decl	conjunct_index	body_decl	body_field	conversion_decl
```

最初の必須pairではindex 1–10を重複なく全件登録する。`conversion_decl`のexpected typeは、
固定audit signatureとResearch元typeをfresh化し、同じbinder telescopeの後に
right-associated conjunctionのindex番目だけを結論として機械生成する。追加binderやpremiseを
許さない。各conversion proofは対応する`body_decl`の結果と`body_field`をtransitive closureで
実使用し、audit proofのindex番目はそのconversion declarationを実使用しなければならない。
本体theoremを呼んで結果を破棄する、別routeだけで結論を閉じる、fieldを入れ替える、
同じfieldを複数conjunctへ流用する実装を失敗させる。各変換の数学的意味は
`math-lean-review`が独立に査読する。

## 依存検査command

固定surfaceは次の5 commandとする。

```lean
syntax (name := assertPromotionSignatureCmd)
  "#assert_promotion_signature " ident " matches " ident : command

syntax (name := assertPromotionDependenciesCmd)
  "#assert_promotion_dependencies " ident
    " using_body [" ident,* "]"
    " allow_research_types [" ident,* "]" : command

syntax (name := assertPromotionInputsCmd)
  "#assert_promotion_inputs " ident " matches " ident
    " using_body [" ident,* "]"
    " ledger " str : command

syntax (name := assertPromotionConjunctsCmd)
  "#assert_promotion_conjuncts " ident " matches " ident
    " using_body [" ident,* "]"
    " ledger " str : command

syntax (name := assertPromotionPremisesCmd)
  "#assert_promotion_premises " ident
    " using_body [" ident,* "]"
    " ledger " str : command
```

`#assert_promotion_signature audit matches research`は両declarationのuniverseをfresh化し、
typeのdefinitional equalityを検査する。binder、typeclass、premise、conclusionの追加・削減・
対象縮小があれば失敗する。

`#assert_promotion_dependencies audit using_body [...] allow_research_types [...]`はauditの
value expressionから到達する全local / audit declarationのvalueを再帰的に展開し、
transitive proof-dependency closureを走査する。reducible / irreducible / opaque helper、
local `def`、instance synthesisを検査から除外せず、次を検出したらelaborationを失敗させる。

- Research theorem / lemma / instanceへの直接・間接proof依存
- Research proofへ到達するProp-producing `def`、opaque declaration、axiom、instance依存
- `using_body`に列挙されていない本体側theorem / lemmaの直接利用
- `using_body`が空、またはaudit valueから1件も到達しない状態
- `allow_research_types`にないResearch declarationへの依存
- `allow_research_types`へtheorem / lemma / instanceを登録する設定

command実装はLean Meta toolingであり、新しい数学claimではない。許可listは型・definitionだけを
列挙し、theorem / lemma / proof-producing instanceを登録できない。statement typeのdependencyと
value expressionのproof dependencyは別に収集し、Research typeがstatementに現れることを理由に
Research proof dependencyを許可しない。

`#assert_promotion_inputs audit matches research using_body [...] ledger "..."`は、両signatureを
fresh化したうえでResearch binderを列挙し、input manifestとaudit valueのtransitive closureを
突合し、input-field manifestの全field双方向一致も検査する。各binderが指定された
本体入力constructionまたはResearch結論の再構成に実質使用され、
preservation obligationのdischarge declarationがclosure内にあることを要求する。binderの欠落、
dummy use、固定値・選択値への置換、追加同一視premise、未登録constructionを失敗させる。
実質使用とpreservation内容の数学的妥当性は`math-lean-review`が独立に判定する。

`#assert_promotion_conjuncts audit matches research using_body [...] ledger "..."`は、Research結論を
正規化してconjunct数と各indexのexpected propositionを生成し、conjunct manifest、
conversion declarationの型、audit / conversion valueのtransitive dependency closureを突合する。
index欠落・重複、body field未使用、body結果破棄、別routeのみのproof、conversion型への追加premise、
Research proof依存を失敗させる。dependency command単独ではsemanticなconjunct対応を判定せず、
このcommand、signature command、material premise監査、field-content監査を組み合わせる。

`#assert_promotion_premises audit using_body [...] ledger "..."`は、`using_body`のbinder、
typeclass、transitive dependencyで使う入力structure / certificateの全field projectionを
Sortにかかわらず列挙し、
`research-lean/audit/premise-manifest.tsv`と突合する。ledger列は次で固定する。

```text
audit_decl	body_field	body_source	field_kind	classification	research_source	discharge_decl
```

`field_kind`は`prop-premise` / `type-data` / `type-witness`、`classification`は
`text-derived` / `discharged` / `undischarged` / `conclusion-witness-risk`とする。
行欠落、`undischarged`、`conclusion-witness-risk`、`discharged`なのに`discharge_decl`が
audit valueのdependency closureに無い場合は失敗する。Type-valued fieldが`Nonempty`、
`Exists`、packet / structure結論のconstructorへ流れる場合は`type-witness`として追跡する。
`using_body`結果のfieldはconjunct manifestで別管理するが、入力/certificateのfieldは除外しない。
Research typeを`allow_research_types`へ入れた場合も使用fieldを同じledgerへ登録する。
これによりProp fieldだけでなくType-valued witnessによるanswer encodingも未申告のまま通せない。
結論相当性と分類の妥当性は`math-lean-review`が独立に判定する。

## generated-pair必須conjunct mapping

最初のmanifest行は次の10対応をすべてaudit proofで構成する。

| Research結論 | 本体packet field |
| --- | --- |
| displayed interpretation realization | `displayedInterpretationRealization` |
| restriction-level required-law evaluator | `displayedRequiredLawRestrictionEvaluator` |
| actual source-C0 Čech zero | `sourceC0CechZero` |
| selected generated realization layer | `selectedRealizationLayer` |
| degree-wise carrier / face equations | `degreewiseCarrierFaceEquations` |
| cochain realization | `cochainRealization` |
| H1 comparison package | `h1ComparisonPackage` |
| residual boundary | `residualBoundary` |
| semantic H1 zero | `semanticH1Zero` |
| additive H1 zero | `additiveH1Zero` |

Research側`G.quotientIsSheaf`と本体側
`LawEquationWitnessIdealGeometryBody.quotientIsSheaf`は一般levelではmaterial premiseである。
auditは両者の対応と生成元をpremise ledgerへ明示し、fieldを読むだけで無条件放電済みと扱わない。

## 必須negative fixture

次の欠陥を各fixtureで発火させ、すべてfailureを確認する。

| fixture | 落とす検査 |
| --- | --- |
| Research元より結論を減らす | `#assert_promotion_signature` |
| 本体先へmaterial premiseを追加する | `#assert_promotion_signature` + audit elaboration |
| 量化対象またはuniverseを狭める | `#assert_promotion_signature` |
| 結論相当のpremiseをtypeclassへ移す | `#assert_promotion_premises` + material premise監査 |
| 結論相当のpremiseをstructure / certificate fieldへ移す | `#assert_promotion_premises` + field-content監査 |
| audit proofからResearch theoremを直接呼ぶ | `#assert_promotion_dependencies` |
| local helper経由でResearch theoremを呼ぶ | `#assert_promotion_dependencies` |
| opaque / Prop-producing `def`経由でResearch proofを読む | `#assert_promotion_dependencies` |
| instance synthesis経由でResearch proofを読む | `#assert_promotion_dependencies` |
| 任意の`skeleton`を固定値・生成値へ置換する | `#assert_promotion_inputs` |
| Research binderをdummy useだけで済ませる | `#assert_promotion_inputs` |
| input manifest / input-field manifestの必須行を落とす | `#assert_promotion_inputs` |
| input-field行を重複させる・field equationの型をずらす | `#assert_promotion_inputs` |
| preservation dischargeをdependency closure外に置く | `#assert_promotion_inputs` |
| constructionへ追加premiseを入れる・未登録constructionを使う | `#assert_promotion_inputs` |
| semantic inputを`Component := PUnit` / constant projectへ置換する | `#assert_promotion_inputs` |
| 本体theoremの結果を破棄して別routeで結論を閉じる | `#assert_promotion_conjuncts` |
| body fieldを入れ替える・未使用にする・複数indexへ流用する | `#assert_promotion_conjuncts` |
| conjunct indexを欠落・重複させる | `#assert_promotion_conjuncts` |
| conversion declarationへ追加premiseを入れる | `#assert_promotion_conjuncts` |
| 入力certificateの`witness : X`から`Nonempty X`を直接作る | `#assert_promotion_premises` |
| Type-valued input fieldから`Exists`を直接作る | `#assert_promotion_premises` |
| Type-valued input fieldからpacket / structure結論を直接作る | `#assert_promotion_premises` |

## 合格証拠

個別の`ported`判定には次をすべて要求する。

- Research元declarationとfile
- 本体先declarationとfile
- 全conjunct対応表
- material premise一覧と、本文由来 / 放電済み / 未放電の分類
- audit declaration
- `#assert_promotion_signature`の通過
- `#assert_promotion_dependencies`の通過
- `#assert_promotion_inputs`の通過とinput / input-field ledger
- `#assert_promotion_conjuncts`の通過とconjunct ledger
- `#assert_promotion_premises`の通過とpremise ledger
- 対象declarationのaxiom audit
- `math-lean-review` 4本の承認

build成功、theorem名の存在、台帳記載だけでは合格証拠にしない。
