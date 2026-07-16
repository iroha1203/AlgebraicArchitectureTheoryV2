# PRD: AAT Lean Legacy Consolidation

- 作成: 2026-07-13
- 改訂: 2026-07-16
- 対象module:
  - `Formal/AG/LawAlgebra/Scheme.lean`（削除）
  - `Formal/AG/LawAlgebra/ObstructionIdeal.lean`
  - `Formal/AG/LawAlgebra/LawfulLocus.lean`
  - `Formal/AG/LawAlgebra/Correspondence.lean`
  - `Formal/AG/LawAlgebra/FiniteExamples.lean`
  - `Formal/AG/LawAlgebra.lean`
  - `Formal/AG/Cohomology/GluingMismatch.lean`
  - `Formal/AG/Cohomology/LocalFlatnessGap.lean`
  - `Formal/AG/RepresentationAnalysis/Bootstrap.lean`
  - `Formal/AG/RepresentationAnalysis/AATSch.lean`
  - `Formal/AG/RepresentationAnalysis/SignatureCurvature.lean`
  - `Formal/AG/RepresentationAnalysis/GraphMatrix.lean`
  - `Formal/AG/RepresentationAnalysis/PreservationReflection.lean`
  - `Formal/AG/RepresentationAnalysis/RepairMarginDehn.lean`
  - `Formal/AG/RepresentationAnalysis/Synthesis.lean`
  - `Formal/AG/RepresentationAnalysis/`以下の`AATSch` / analytic representation consumer
  - `Formal/AG/RepresentationAnalysis.lean`
  - `Formal/AG/SingularityMonodromyStack/ArchitectureStack.lean`
  - `Formal/AG/SingularityMonodromyStack/Stratum.lean`
  - `Formal/AG/SingularityMonodromyStack/`以下のarchitecture scheme consumer
  - `Formal/AG/Measurement/Bootstrap.lean`
  - `Formal/AG/Evolution/Bootstrap.lean`
  - `Formal/AG/SemanticRepair/Bootstrap.lean`
  - `Formal/AG/Examples/LegacyConsolidation.lean`（新規）
  - `Formal/AG/Examples/RepresentationAnalysisPart7.lean`
  - `Formal/AG/StatementContractsLegacyConsolidation.lean`（新規）
  - `Formal/AG/StatementContracts.lean`
  - `Formal/AG/AxiomAudit.lean`
  - `Formal/AG.lean`
- 数学的正典:
  - `docs/aat/algebraic_geometric_theory/part_2_architecture_geometry_sites_sheaves.md`
    のselected site、sheafification、ringed AAT site
  - `docs/aat/algebraic_geometric_theory/part_3_law_algebra_obstruction_ideal_lawful_locus.md`
    定義6.1〜7.2、8.1〜10.3、定理11.1、定義11.3、定理11.4
  - `docs/aat/algebraic_geometric_theory/part_7_representation_periods_analysis.md`
    定義2.1、7.2、12.1、定理16.1
  - `docs/aat/algebraic_geometric_theory/appendix.md` A.4〜A.8
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、
  `docs/aat/lean_quality_standard.md`
- tracking Issue: 実装開始時に作成し、対象main commit、全数inventory、consumer signature manifest、
  dependencyを固定する。Issue番号と進捗は本PRDへ書かない
- statement contract正本:
  - SD2〜SD6のcore declaration、SD3で列挙したconsumer declaration、
    SD9のfiring declarationは本PRD
  - SD3外の既存public consumerはtracking Issueの`consumer signature manifest`。
    SD3列挙対象のmanifest行は旧signatureとSD3参照だけを持つ
  - `P`のsignature正本はtracking Issueでpinした対象main commit
  - 両者は対象宣言集合を分離し、同じsignatureを複製しない
- executable contract: `Formal/AG/StatementContractsLegacyConsolidation.lean`
- 実行単位: tracking Issue配下の`1 Issue = 1 PR`。最終削除batchは専用Issue / PRとする

## 実行開始条件

次をすべて満たすまで移行実装を開始しない。R0のinventory作成とscratchでの型確認だけを
preflightとして許可し、public Lean declarationは変更しない。

1. tracking Issueに次が登録されている。
   - 対象main commit SHA
   - SD0の`L`（must-not-remain）、`K`（保持）、`N`（新規・shape変更core）、
     `C`（変更対象consumer）、`E`（firing）、`P`（signature固定）のexact name集合
   - `C`の各宣言について、旧完全signature、新完全signatureまたは`SD3:<exact-name>`参照、
     処置、proof owner、batch、focused check
   - module DAG、子Issue依存、削除順、一時adapterのownerと削除Issue
2. 対象main commit上で次のcanonical declarationsがmerged済みであり、statement contractと
   AxiomAuditがgreenである。PRDやdocs-only差分はこの条件を満たさない。
   - `ReadingCore`、`RawAmbientRestrictionSystem`、`RawAmbientRestrictionSystem.toRingedSite`
   - `RingedAATSite`、`RingedAATSite.structureSheaf`、`RingedAATSite.canonical`
   - `AATReadingDecoration`、`AATReadingDecoration.Preserves`
   - `StandardArchitectureScheme`、`StandardArchitectureScheme.Hom`、
     `StandardArchitectureScheme.category`、`StandardArchitectureScheme.forget`
   - `StandardArchitectureScheme.affineOpenCover`、
     `StandardArchitectureScheme.overlap_is_actual_pullback`
   - `ClosedEquationalLawReading`、`IsClosedEquationalLawReading`、
     `RequiredClosed`、`RequiredLawIdealExact`
   - `lawGeneratedIdealSheaf`、`lawfulClosedSubscheme`、`lawfulClosedImmersion`
   - `FactorsThroughLawfulClosedSubscheme`、`factorizationLift`、
     `factorizationLift_fac`、`factorization_unique`
   - `lawfulnessIdealFactorizationCorrespondence`
   - `factorsThroughLawfulClosedSubscheme_iff_omegaU_zero`
   - `factorsThroughLawfulClosedSubscheme_iff_requiredSignatureAxesZero`
3. nondegenerate standard geometry reference modelがmerged済みであり、少なくとも次を直接参照できる。
   - `Examples.StandardGeometryReferenceModels.referenceRaw`
   - `Examples.StandardGeometryReferenceModels.referenceScheme`
   - `Examples.StandardGeometryReferenceModels.weakReading` / `strongReading`
   - 各readingのvalidity、`RequiredClosed`、`RequiredLawIdealExact`
   - `zeroPoint_fires`、`onePoint_fires`、`twoPoint_fires`
   - `standardGeometryReference_fires`
4. 最終public nameを次で固定している。
   - actual architecture schemeの公開名は`StandardArchitectureScheme`のまま維持する。
   - 旧`LawAlgebra.Scheme.ArchitectureScheme`へ`ArchitectureScheme`の名前を戻さない。
   - ringed objectは`RingedAATSite`、actual lawful geometryは
     `lawfulClosedSubscheme`、actual factorizationは
     `FactorsThroughLawfulClosedSubscheme`を唯一のownerとする。
5. scratch fileでSD2〜SD6、SD3の列挙consumer、SD9の完全signatureがelaborateし、
   対象main commit上のexact namespace、
   universe、implicit argument、typeclass argumentがtracking Issueに記録されている。
6. 同じscratchで`overlapToLeftMorphism`、`leftChartMorphism`、negative compatibility、
   `synthesisPackage`の全fieldにconstructor termを与え、未証明の`Nonempty`や結論相当local instanceを
   `Classical.choice`で埋めていない。
7. 実装前statement reviewで、SD2〜SD6、SD3の列挙consumer、SD7のconsumer規則、
   SD8のmaterial premise表、
   SD9のfiring matrix、
   `consumer signature manifest`が`Approved`になっている。

いずれかが欠ける間、このPRDは実行しない。

## Module import contract

direct importと削除後の責務を次で固定する。未記載の横断importまたは循環依存が必要になった場合は
実装を止め、module DAGを再承認する。

| module | direct imports / 最終処置 | 責務 |
| --- | --- | --- |
| `LawAlgebra/Scheme.lean` | file自体を削除 | 旧ringed / chart / scheme / gluing routeを残さない |
| `LawAlgebra/ObstructionIdeal.lean` | 現行Stanley–Reisner依存を維持 | selected witness idealとlocal sum。`SheafImageConstruction`は削除 |
| `LawAlgebra/LawfulLocus.lean` | `ObstructionIdeal`、Mathlib prime spectrum | affine zero-setとring-hom計算だけ。actual factorizationを名乗るsurfaceは削除 |
| `LawAlgebra/Correspondence.lean` | `LawEquation`、`LawfulLocus` | low-level witness / kernel補題だけ。定理11.1の主ownerにはしない |
| `LawAlgebra/ClosedEquationalGeometry.lean` | 既存direct importを維持 | actual ideal sheaf、closed subscheme、semantic / ideal / factorization correspondenceの唯一のowner |
| `RepresentationAnalysis/AATSch.lean` | `ReadingFunctoriality/Core`、`LawAlgebra/StandardScheme`、`Mathlib.CategoryTheory.Category.Basic` | SD4〜SD5のcanonical decorated categoryとFunctor surface |
| `RepresentationAnalysis/PreservationReflection.lean` | `AATSch`、`Mathlib.CategoryTheory.Category.Cat` | `CategoryTheory.Cat`でbundleしたrepresentation familyと既存reflection statement |
| `RepresentationAnalysis/GraphMatrix.lean` | `PreservationReflection` | graph / matrix targetのMathlib `Category` instanceとFunctor constructor |
| `RepresentationAnalysis/RepairMarginDehn.lean` | 現行import、`LawAlgebra/ClosedEquationalGeometry` | SD3のactual repair-route factorizationと既存distance / margin / Dehn consumer |
| `RepresentationAnalysis/Synthesis.lean` | `AnalyticContext`、`ClosedEquationalGeometry` | SD6のsingle synthesis packageとderived projections |
| `Cohomology/GluingMismatch.lean` | 現行`CechComplex` importを維持 | Part IVのring-level lawfulness / mismatch statementを維持し、旧factorization accessorだけを削除 |
| `Cohomology/LocalFlatnessGap.lean` | 現行`GluingMismatch` importを維持 | Part IVのglobal-section contradictionを維持し、旧factorization accessorだけを削除 |
| `SingularityMonodromyStack/ArchitectureStack.lean`、`Stratum.lean` | `LawAlgebra/StandardScheme`と各直前module | canonical standard Scheme / atlasを使うstack / stratum consumer |
| `Examples/LegacyConsolidation.lean` | `StandardGeometryReferenceModels`、`RepresentationAnalysis/GraphMatrix`、`RepresentationAnalysis/Synthesis` | SD9のnondegenerate migration firing |
| `StatementContractsLegacyConsolidation.lean` | 変更対象実装moduleとexample moduleをdirect import | `example : exact-type := declaration`だけ |
| `StatementContracts.lean` | `StatementContractsLegacyConsolidation`をdirect import | executable contract aggregate |
| `AxiomAudit.lean` | 変更対象実装moduleとexample moduleをdirect import | new / changed theoremの全数audit |
| `LawAlgebra.lean`、`RepresentationAnalysis.lean`、`Formal/AG.lean` | canonical moduleだけを順序どおりdirect import | aggregate到達性。削除moduleのre-export禁止 |

`Formal/AG`から`ResearchLean.AG`をimportしない。

## Statement Design

SD2〜SD6をcore declaration、SD3の列挙対象をfixed consumer declaration、SD9をfiring declarationの
唯一のfixed statement designとする。
target名、namespace、入力、
量化対象、結論、参照definitionのsignatureを実装中に変更しない。変更が必要になった場合は未達として
停止し、該当SD、必要な追加premise、旧signature、新signatureをtracking Issueへ報告する。

`Formal/AG/StatementContractsLegacyConsolidation.lean`は、`N ∪ C ∪ E ∪ P`の全public declarationを
`example : <fixed type> := <implementation>`で一対一に検査する。`#check`、名前の存在、wrapper、
alias、より弱い同値statementは達成に数えない。削除対象`L`はLean contractへ再定義せず、
SD10のrepository-wide no-hit検査で判定する。

### 共通namespaceとparameter

~~~lean
namespace AAT.AG

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry Classical

universe u v w x y z

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
~~~

### SD0 — exact inventoryと処置関数

対象main commit上で次の集合をexact nameでmaterializeする。

~~~text
L = must-not-remain declaration / field / module path
K = final snapshotに同じsignatureで保持するcanonical / independent declaration
N = 新設またはshapeを変更するcanonical core declaration
C = LまたはNを参照する全transitive public consumer
E = SD9で新設するnondegenerate firing declaration
P = touched module内でsignatureを完全維持するdeclaration; P ⊆ K

L, K, N, C, E are pairwise disjoint
inventory_target_names = L ∪ K ∪ N ∪ C ∪ E
implementation_changed_public_names = N ∪ C ∪ E
statement_contract_target_names = N ∪ C ∪ E ∪ P
axiom_audit_names = theorem declarations in (N ∪ C ∪ E)
~~~

`L`の初期固定集合は次である。field declarationとnamespace内accessorもexact nameへ展開する。

| owner | `L`へ入れる宣言 / field |
| --- | --- |
| `LawAlgebra.Scheme` | `affineChartMathlibSpecLocallyRingedSpace`、`RingedAATTopos`と全field / accessor、`ChartCompatibility`と全field / constructor / accessor、旧`ArchitectureScheme`と全field / constructor / accessor、`SchemeGluingData`、`AffineReturnConditions`、`affineReturnAssumptions`、module path自体 |
| `LawAlgebra.ObstructionIdeal` | `SelectedLawWitnessIdealFamily.SheafImageConstruction`、`imageIdeal_eq_localObstructionIdeal`、`localObstructionIdeal_eq_imageIdeal` |
| `LawAlgebra.LawfulLocus` | `LawfulSectionData.FactorsThroughLawfulLocus`、`factorsThroughLawfulLocus_of_lawful`、`lawful_of_factorsThroughLawfulLocus`、`lawful_iff_factorsThroughLawfulLocus` |
| `LawAlgebra.Correspondence` | `LawfulnessIdealCorrespondenceAssumptions`と全field / accessor、`LawfulnessIdealCorrespondencePackage`と全field、`factorsThroughLawfulLocus_iff_omegaU_zero`、`omegaU_zero_iff_requiredSignatureAxesZero`、`lawfulnessIdealCorrespondence`、旧factorization wrapperを結論に含む全theorem |
| `Cohomology` | `LocalFlatnessData.factorsThroughFlat_U`、`RestrictedLocalLawfulSection.factorsThroughFlat_U`、`CompatibleGlobalLawfulSection.globalFactorsThroughFlat_U` |
| `RepresentationAnalysis.AATSchReadingParameter` | `SchemeMorphism`、`id`、`comp`、`id_comp`、`comp_id`、`assoc` |
| `RepresentationAnalysis.AATSch` | `underlyingScheme`、`underlyingScheme_eq` |
| `RepresentationAnalysis.AATSchMorphism` | 旧`underlying` fieldとそれを返すaccessor |
| `RepresentationAnalysis` | `AATSchIdentityData`、`AATSchCompositionData`、`AATSchFiberProductData`と全accessor、`AnalyticTargetCategory`と`AsCategory` / category instance、旧`AnalyticRepresentation.targetCategory` projection、`toFunctor` / `map_identity` / `map_composition` / `toFunctor_obj` / `toFunctor_map` |
| `RepresentationAnalysis.GraphMatrix` | `finiteDirectedGraphTargetCategory`、`matrixRepresentationTargetCategory`、`GraphRepresentationProfile.graphOf` / `mapGraph` / `map_id` / `map_comp` / `toAnalyticRepresentation`、`MatrixRepresentationProfile.matrixOf` / `mapMatrix` / `map_id` / `map_comp` / `toAnalyticRepresentation` |
| `RepresentationAnalysis.SignatureCurvatureLawfulFactorizationContext` | 旧`obstructionClassReading` / `lawConflictReading`と両`*_holds` field、両`*_certificate` theorem、`FactorsThroughLawfulLocus`を結論に含む全theorem |
| `RepresentationAnalysis.RepairRoute` | 旧`LawCoordinateAlgebra` / `lawCoordinateCommRing` / `obstructionIdeal` / `lawfulSection` / `factorsThroughLawfulLocus` field、`factorsThroughLawfulLocus_certificate` |
| `RepresentationAnalysis.Synthesis` | `AATSynthesisAssumptions`、`AATSynthesisConstructionInput`、両`toPackage`、旧`algebraicGeometricAATSynthesis`、`algebraicGeometricAATSynthesis_constructedPackage`、旧`AATSynthesisPackage`の`Atom` / `aatSite` / `ringedAATTopos` / chart family / set-level lawful locus / coherence equalityの重複field |
| `Examples.RepresentationAnalysisPart7` | `toyTargetCategory`、`idealTargetCategory`。Mathlib categoryを持つtargetかSD9のgraph targetへ置換 |
| repository-wide | `Legacy*` rename、旧名deprecated alias、exported compatibility adapter、削除module re-export、旧statement contract / audit entry |

`K`には少なくとも次を入れる。

- `RawAmbientRestrictionSystem.toRingedSite`、`RingedAATSite`、
  `architectureChartSpec`、`architectureChartRestriction`
- `StandardArchitectureScheme`と`underlying` / `decoration` / `atlas` / `overlaps`、
  `StandardArchitectureScheme.Hom` / `category` / `forget` / `singleAffine`
- `lawGeneratedIdealSheaf`、`lawfulClosedSubscheme`、`lawfulClosedImmersion`、
  `FactorsThroughLawfulClosedSubscheme`、`factorizationLift`、`factorizationLift_fac`、
  `factorization_unique`、`lawfulnessIdealFactorizationCorrespondence`、
  `factorsThroughLawfulClosedSubscheme_iff_omegaU_zero`、
  `factorsThroughLawfulClosedSubscheme_iff_requiredSignatureAxesZero`
- `SelectedLawWitnessIdealFamily`、`localObstructionIdeal`、`RestrictionCompatible`
- `LawfulLocus.lawfulLocus`、`localLawfulLocus`。いずれもaffine prime-spectrum計算として保持する
- `LawfulSectionData`、`pulledObstructionIdeal`、`sectionPrimeMap`、`Lawful`
- `Correspondence.localObstructionIdeal_le_ker_iff_lawful`
- `Correspondence.lawful_of_selectedWitnessIdeals_le_ker`
- `Correspondence.lawful_of_generatedLawWitnessIdeals_le_ker`
- `Correspondence.displayedRequiredLawsHoldOn_defect_mem_localObstructionIdeal`
- `Cohomology.LocalFlatnessData`、`RestrictedLocalLawfulSection`、`GluingMismatchData`、
  `PseudoTorsorNormalizedMismatch`、`HiddenCouplingData`、`CompatibleGlobalLawfulSection`、
  `GlobalSectionCoboundarySoundness`、`LocalFlatnessGapHypotheses`とPart IVの既存main theorem。
  これらを`P`へも登録する

`K`はactual closed subschemeまたはactual factorizationの完了証拠として使用しない。

`N`はSD2の4 bootstrap alias、SD4のAATSch owner、SD5のFunctor / bundled family / target category
instance / normalized graph・matrix profile、SD6のsingle synthesis packageとderived projectionを
exact nameへ展開した集合とする。SD3冒頭のmerged actual factorizationとCohomology main statementは
`K`、三つのCohomology accessorは`L`、`RepairRoute` / `SignatureCurvature`宣言は`C`へ分類する。
`C`は`L ∪ K ∪ N ∪ E`を除いたうえで、`L`または`N`を参照する全transitive public consumerを
tracking Issueでrepository全体から自動抽出し、手入力の代表例一覧で代用しない。
`E`はSD9のLean blockにtop-levelで現れる全public declarationとautomatic projectionである。
inventory外の旧routeが見つかった場合はPRD欠陥として該当batchを止める。

### SD1 — canonical owner map

最終snapshotのownerを次で一意化する。

| 旧surface | canonical owner / 最終処置 |
| --- | --- |
| `RingedAATTopos` | `raw.toRingedSite : RingedAATSite S k`。site、structure sheaf、canonical unitをここから読む |
| 旧`ArchitectureScheme` | `StandardArchitectureScheme raw`。公開名は変更しない |
| `ChartCompatibility` | `ArchitectureAffineAtlas`、`IsArchitectureAffineAtlas`、`ArchitectureOverlapPresentation`、`IsArchitectureOverlapPresentation` |
| `singleAffineSpec` | `StandardArchitectureScheme.singleAffine raw W` |
| `SchemeGluingData` / `AffineReturnConditions` | 削除。actual atlas / pullback / coverage / cocycle APIを使用 |
| `SheafImageConstruction` | 削除。`lawGeneratedIdealSheaf`のactual `Scheme.IdealSheafData`を使用 |
| set-level lawful locus | `LawfulLocus.lawfulLocus`をaffine calculationに限定して保持 |
| `FactorsThroughLawfulLocus` | 削除。`FactorsThroughLawfulClosedSubscheme`のactual lift + triangleを使用 |
| assumptions / correspondence package | 削除。`lawfulnessIdealFactorizationCorrespondence`とSD3のcanonical edge theoremを直接proof-use |
| custom `SchemeMorphism` | `StandardArchitectureScheme.Hom` |
| custom target category | Mathlib `Category` |
| custom analytic representation | Mathlib `Functor` |
| synthesisの重複field | SD6のminimal packageからのprojection |

同じ値を別fieldへ保存してequality fieldで再結合しない。canonical ownerから定義的またはnamed projectionで
読める値はpackage fieldに入れない。

### SD2 — ringed site、standard Scheme、bootstrap alias

actual schemeの公開名は`StandardArchitectureScheme`に固定する。既存のfield / APIは次をそのまま使用する。

~~~lean
-- existing canonical owner
structure LawAlgebra.StandardArchitectureScheme
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] where
  underlying : AlgebraicGeometry.Scheme
  decoration : LawAlgebra.AATReadingDecoration raw underlying
  atlas : LawAlgebra.ArchitectureAffineAtlas raw underlying decoration
  atlasValid : LawAlgebra.IsArchitectureAffineAtlas raw atlas
  overlaps : LawAlgebra.ArchitectureOverlapPresentation raw atlas
  overlapsValid : LawAlgebra.IsArchitectureOverlapPresentation raw overlaps

-- Parts VII--Xのdependency aliasはrawを明示する
abbrev RepresentationAnalysis.UsesArchitectureScheme
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] :=
  LawAlgebra.StandardArchitectureScheme raw

abbrev Measurement.UsesArchitectureScheme
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] :=
  LawAlgebra.StandardArchitectureScheme raw

abbrev Evolution.UsesArchitectureScheme
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] :=
  LawAlgebra.StandardArchitectureScheme raw

abbrev SemanticRepair.UsesArchitectureScheme
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] :=
  LawAlgebra.StandardArchitectureScheme raw
~~~

`StandardArchitectureScheme.underlying`、`atlas`、`affineOpenCover`、`Hom.base`、`forget`を
最終APIとする。`toScheme`、`architectureScheme` alias、旧`LocallyRingedSpace` wrapperを追加しない。
ringed dataは`raw.toRingedSite`から読み、Schemeから逆算しない。

### SD3 — actual ideal geometry、factorization consumer、Part IV preservation

canonical actual factorizationはmerged宣言の次のshapeに固定する。

~~~lean
def LawAlgebra.FactorsThroughLawfulClosedSubscheme
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (R : LawAlgebra.ClosedEquationalLawReading raw X)
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hclosed : LawAlgebra.RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :=
  {t : T ⟶ LawAlgebra.lawfulClosedSubscheme raw X R hR hclosed //
    t ≫ LawAlgebra.lawfulClosedImmersion raw X R hR hclosed = s}
~~~

CohomologyのPart IV本体は、ring-level `Lawful`、mismatch、cocycle、global-section contradictionを
独立に扱い、旧factorization型は次の三つのderived accessorだけに現れる。したがって本体へ
`raw`、closed-equational reading、`RequiredClosed`を追加しない。

| 処置 | exact declaration |
| --- | --- |
| 削除 | `Cohomology.LocalFlatnessData.factorsThroughFlat_U` |
| 削除 | `Cohomology.RestrictedLocalLawfulSection.factorsThroughFlat_U` |
| 削除 | `Cohomology.CompatibleGlobalLawfulSection.globalFactorsThroughFlat_U` |
| signature完全維持 | `LocalFlatnessData`、`RestrictedLocalLawfulSection`、`GluingMismatchData`、`PseudoTorsorNormalizedMismatch` |
| signature完全維持 | `HiddenCouplingData`、`CompatibleGlobalLawfulSection`、`GlobalSectionCoboundarySoundness`、`LocalFlatnessGapHypotheses` |
| statement完全維持 | mismatch / cocycle theorem、global restriction coboundary theorem、4本の`localFlatnessGap_no_globalLawfulSection*` |

`pulledObstructionIdeal_eq_bot`はaffine ideal calculationとして保持する。保持対象へactual factorizationの
claimを付け足さず、actual Scheme targetへ移すための新premiseも追加しない。inventoryで上記三accessor
以外の旧factorization proof-useが見つかった場合は、そのconsumerだけをSD3のactual routeへ追加する前に
statement reviewをやり直す。

Part VIIのrepair routeは定義12.1のlawful targetをactual closed geometryで表す。operation-distance側の
fieldは完全維持し、旧ring ideal / pulled-ideal wrapperだけを次へ置換する。

~~~lean
structure RepresentationAnalysis.RepairRoute
    {Obj : ArchitectureObject U}
    (C : RepresentationAnalysis.DistanceFlatnessMassContext Obj)
    {S : Site.AATSite Obj} {k : Type v} [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (R : LawAlgebra.ClosedEquationalLawReading raw X)
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hclosed : LawAlgebra.RequiredClosed raw X R) where
  source : C.operationDistance.GeometryState
  target : C.operationDistance.GeometryState
  flatCandidate : C.distanceToFlatness.FlatCandidate source
  target_eq_flatState :
    target = C.distanceToFlatness.flatState source flatCandidate
  operationPath : C.operationDistance.operationPath source target
  routeCost : RepresentationAnalysis.DistanceValue Nat
  routeCost_eq_d_op : routeCost = C.d_op source target
  routeCost_eq_pathCost :
    routeCost = C.operationDistance.pathCost operationPath
  sectionSource : AlgebraicGeometry.Scheme
  section : sectionSource ⟶ X.underlying
  factorization :
    LawAlgebra.FactorsThroughLawfulClosedSubscheme raw X R hR hclosed section

theorem RepresentationAnalysis.RepairRoute.factorization_certificate
    {Obj : ArchitectureObject U}
    {C : RepresentationAnalysis.DistanceFlatnessMassContext Obj}
    {S : Site.AATSite Obj} {k : Type v} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {X : LawAlgebra.StandardArchitectureScheme raw}
    {R : LawAlgebra.ClosedEquationalLawReading raw X}
    {hR : LawAlgebra.IsClosedEquationalLawReading raw X R}
    {hclosed : LawAlgebra.RequiredClosed raw X R}
    (Q : RepresentationAnalysis.RepairRoute C raw X R hR hclosed) :
    LawAlgebra.FactorsThroughLawfulClosedSubscheme
      raw X R hR hclosed Q.section :=
  Q.factorization
~~~

`RepairProfileReading`、`RepairMarginDehnContext`と全route consumerは、operation-distance側の
旧完全signatureを維持し、route型の追加parameterを既存canonical provenanceから放電する。
放電できないconsumerはroute statementを弱めず停止する。

`SignatureCurvatureLawfulFactorizationContext`は旧correspondence assumptionsをfieldに持たず、
canonical theoremが要求するdataを明示する。

~~~lean
structure RepresentationAnalysis.SignatureCurvatureLawfulFactorizationContext
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (R : LawAlgebra.ClosedEquationalLawReading raw X)
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hclosed : LawAlgebra.RequiredClosed raw X R)
    (hexact : LawAlgebra.RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U)
    (Sig : SignatureAxes U)
    {Value : Type u}
    (valuation : ObstructionValuation U Value)
    (aggregation : ZeroReflectingAggregation Value valuation.domain
      S.lawUniverse.RequiredIndex) where
  signatureProfile : RepresentationAnalysis.SignatureReadingProfile Sig
  curvatureProfile :
    RepresentationAnalysis.CurvatureReadingProfile S.lawUniverse valuation aggregation
  pointComparison :
    LawAlgebra.RequiredObjectPointComparison raw X R s Obj
  obstructionSoundness : ∀ i : S.lawUniverse.RequiredIndex,
    ObstructionSound valuation (S.lawUniverse.law i.1)
  obstructionCompleteness : ∀ i : S.lawUniverse.RequiredIndex,
    ObstructionComplete valuation (S.lawUniverse.law i.1)
  axisExactness :
    Lawfulness Obj S.lawUniverse ↔ RequiredSignatureAxesZero Obj Sig
~~~

同contextのpublic theoremを次で固定する。旧`FactorsThroughLawfulLocus`を返す同名theoremは
signature変更で温存せず、actual targetを名前に含む宣言へ置換する。

~~~lean
namespace RepresentationAnalysis.SignatureCurvatureLawfulFactorizationContext

variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {X : LawAlgebra.StandardArchitectureScheme raw}
variable {R : LawAlgebra.ClosedEquationalLawReading raw X}
variable {hR : LawAlgebra.IsClosedEquationalLawReading raw X R}
variable {hclosed : LawAlgebra.RequiredClosed raw X R}
variable {hexact : LawAlgebra.RequiredLawIdealExact raw X R hR hclosed}
variable {T : AlgebraicGeometry.Scheme} {s : T ⟶ X.underlying}
variable {Obj : ArchitectureObject U} {Sig : SignatureAxes U}
variable {Value : Type u} {valuation : ObstructionValuation U Value}
variable {aggregation : ZeroReflectingAggregation Value valuation.domain
  S.lawUniverse.RequiredIndex}

theorem curvature_zero_iff_omegaU_zero
    (C : SignatureCurvatureLawfulFactorizationContext raw X R hR hclosed
      hexact s Obj Sig valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔
      omegaU valuation S.lawUniverse aggregation Obj = valuation.domain.zero

theorem curvature_zero_iff_requiredObstructionValuesZero
    (C : SignatureCurvatureLawfulFactorizationContext raw X R hR hclosed
      hexact s Obj Sig valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔
      ∀ i : S.lawUniverse.RequiredIndex,
        valuation.omega (S.lawUniverse.law i.1) Obj = valuation.domain.zero

theorem curvature_zero_iff_requiredSignatureAxesZero
    (C : SignatureCurvatureLawfulFactorizationContext raw X R hR hclosed
      hexact s Obj Sig valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔ RequiredSignatureAxesZero Obj Sig

theorem curvature_zero_iff_requiredSignatureReadingZero
    (C : SignatureCurvatureLawfulFactorizationContext raw X R hR hclosed
      hexact s Obj Sig valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔
      C.signatureProfile.RequiredSignatureReadingZero Obj

theorem factorsThroughLawfulClosedSubscheme_of_curvature_zero
    (C : SignatureCurvatureLawfulFactorizationContext raw X R hR hclosed
      hexact s Obj Sig valuation aggregation)
    (hcurvature : C.curvatureProfile.CurvatureZero Obj) :
    Nonempty
      (LawAlgebra.FactorsThroughLawfulClosedSubscheme
        raw X R hR hclosed s)

theorem curvature_zero_of_factorsThroughLawfulClosedSubscheme
    (C : SignatureCurvatureLawfulFactorizationContext raw X R hR hclosed
      hexact s Obj Sig valuation aggregation)
    (hfactor : Nonempty
      (LawAlgebra.FactorsThroughLawfulClosedSubscheme
        raw X R hR hclosed s)) :
    C.curvatureProfile.CurvatureZero Obj

theorem curvature_zero_iff_factorsThroughLawfulClosedSubscheme
    (C : SignatureCurvatureLawfulFactorizationContext raw X R hR hclosed
      hexact s Obj Sig valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔
      Nonempty
        (LawAlgebra.FactorsThroughLawfulClosedSubscheme
          raw X R hR hclosed s)

theorem factorsThroughLawfulClosedSubscheme_of_requiredSignatureReadingZero
    (C : SignatureCurvatureLawfulFactorizationContext raw X R hR hclosed
      hexact s Obj Sig valuation aggregation)
    (hsig : C.signatureProfile.RequiredSignatureReadingZero Obj) :
    Nonempty
      (LawAlgebra.FactorsThroughLawfulClosedSubscheme
        raw X R hR hclosed s)

end RepresentationAnalysis.SignatureCurvatureLawfulFactorizationContext
~~~

factorization conclusionの4 theoremは
`factorsThroughLawfulClosedSubscheme_iff_omegaU_zero`または
`factorsThroughLawfulClosedSubscheme_iff_requiredSignatureAxesZero`を直接proof-useする。
このnamespaceの全旧 / 新対応も、manifestには旧完全signatureと`SD3:<exact-name>`参照だけを置く。

### SD4 — AATSchをstandard decorated Scheme categoryへ統合

`AATSchReadingParameter`はreading valueと、それらの保存述語だけを持つ。
underlying morphism、identity、composition、category lawを選択dataとして持たない。

~~~lean
namespace RepresentationAnalysis

structure AATSchReadingParameter
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] where
  AtomLabelReading : Type u
  LawReading : Type u
  ObstructionIdealReading : Type w
  SignatureReading : Type u
  InterpretationMapReading : Type x
  atomLabelsCompatible :
    ∀ {X Y : LawAlgebra.StandardArchitectureScheme raw},
      (X ⟶ Y) → AtomLabelReading → AtomLabelReading → Prop
  lawReadingCompatible :
    ∀ {X Y : LawAlgebra.StandardArchitectureScheme raw},
      (X ⟶ Y) → LawReading → LawReading → Prop
  obstructionIdealCompatible :
    ∀ {X Y : LawAlgebra.StandardArchitectureScheme raw},
      (X ⟶ Y) → ObstructionIdealReading → ObstructionIdealReading → Prop
  signatureReadingCompatible :
    ∀ {X Y : LawAlgebra.StandardArchitectureScheme raw},
      (X ⟶ Y) → SignatureReading → SignatureReading → Prop
  interpretationMapCompatible :
    ∀ {X Y : LawAlgebra.StandardArchitectureScheme raw},
      (X ⟶ Y) → InterpretationMapReading → InterpretationMapReading → Prop
  id_atomLabelsCompatible :
    ∀ (X : LawAlgebra.StandardArchitectureScheme raw) (a : AtomLabelReading),
      atomLabelsCompatible (𝟙 X) a a
  id_lawReadingCompatible :
    ∀ (X : LawAlgebra.StandardArchitectureScheme raw) (a : LawReading),
      lawReadingCompatible (𝟙 X) a a
  id_obstructionIdealCompatible :
    ∀ (X : LawAlgebra.StandardArchitectureScheme raw) (a : ObstructionIdealReading),
      obstructionIdealCompatible (𝟙 X) a a
  id_signatureReadingCompatible :
    ∀ (X : LawAlgebra.StandardArchitectureScheme raw) (a : SignatureReading),
      signatureReadingCompatible (𝟙 X) a a
  id_interpretationMapCompatible :
    ∀ (X : LawAlgebra.StandardArchitectureScheme raw) (a : InterpretationMapReading),
      interpretationMapCompatible (𝟙 X) a a
  comp_atomLabelsCompatible :
    ∀ {X Y Z : LawAlgebra.StandardArchitectureScheme raw}
      {f : X ⟶ Y} {g : Y ⟶ Z} {aX aY aZ : AtomLabelReading},
      atomLabelsCompatible f aX aY →
      atomLabelsCompatible g aY aZ →
      atomLabelsCompatible (f ≫ g) aX aZ
  comp_lawReadingCompatible :
    ∀ {X Y Z : LawAlgebra.StandardArchitectureScheme raw}
      {f : X ⟶ Y} {g : Y ⟶ Z} {aX aY aZ : LawReading},
      lawReadingCompatible f aX aY →
      lawReadingCompatible g aY aZ →
      lawReadingCompatible (f ≫ g) aX aZ
  comp_obstructionIdealCompatible :
    ∀ {X Y Z : LawAlgebra.StandardArchitectureScheme raw}
      {f : X ⟶ Y} {g : Y ⟶ Z} {aX aY aZ : ObstructionIdealReading},
      obstructionIdealCompatible f aX aY →
      obstructionIdealCompatible g aY aZ →
      obstructionIdealCompatible (f ≫ g) aX aZ
  comp_signatureReadingCompatible :
    ∀ {X Y Z : LawAlgebra.StandardArchitectureScheme raw}
      {f : X ⟶ Y} {g : Y ⟶ Z} {aX aY aZ : SignatureReading},
      signatureReadingCompatible f aX aY →
      signatureReadingCompatible g aY aZ →
      signatureReadingCompatible (f ≫ g) aX aZ
  comp_interpretationMapCompatible :
    ∀ {X Y Z : LawAlgebra.StandardArchitectureScheme raw}
      {f : X ⟶ Y} {g : Y ⟶ Z} {aX aY aZ : InterpretationMapReading},
      interpretationMapCompatible f aX aY →
      interpretationMapCompatible g aY aZ →
      interpretationMapCompatible (f ≫ g) aX aZ

structure AATSch
    (p : AATSchReadingParameter raw) where
  scheme : LawAlgebra.StandardArchitectureScheme raw
  atomLabels : p.AtomLabelReading
  lawReading : p.LawReading
  obstructionIdealReading : p.ObstructionIdealReading
  signatureReading : p.SignatureReading
  interpretationMapReading : p.InterpretationMapReading

structure AATSchMorphism
    {p : AATSchReadingParameter raw}
    (X Y : AATSch p) where
  toSchemeHom : X.scheme ⟶ Y.scheme
  atomLabelsCompatible :
    p.atomLabelsCompatible toSchemeHom X.atomLabels Y.atomLabels
  lawReadingCompatible :
    p.lawReadingCompatible toSchemeHom X.lawReading Y.lawReading
  obstructionIdealCompatible :
    p.obstructionIdealCompatible toSchemeHom
      X.obstructionIdealReading Y.obstructionIdealReading
  signatureReadingCompatible :
    p.signatureReadingCompatible toSchemeHom X.signatureReading Y.signatureReading
  interpretationMapCompatible :
    p.interpretationMapCompatible toSchemeHom
      X.interpretationMapReading Y.interpretationMapReading

namespace AATSchMorphism

def toSchemeMap
    {p : AATSchReadingParameter raw} {X Y : AATSch p}
    (f : AATSchMorphism X Y) :
    X.scheme.underlying ⟶ Y.scheme.underlying :=
  f.toSchemeHom.base

@[ext] theorem ext
    {p : AATSchReadingParameter raw} {X Y : AATSch p}
    {f g : AATSchMorphism X Y}
    (h : f.toSchemeHom = g.toSchemeHom) : f = g

def id {p : AATSchReadingParameter raw} (X : AATSch p) :
    AATSchMorphism X X

def comp {p : AATSchReadingParameter raw} {X Y Z : AATSch p}
    (f : AATSchMorphism X Y) (g : AATSchMorphism Y Z) :
    AATSchMorphism X Z

@[simp] theorem id_toSchemeHom
    {p : AATSchReadingParameter raw} (X : AATSch p) :
    (id X).toSchemeHom = 𝟙 X.scheme

@[simp] theorem comp_toSchemeHom
    {p : AATSchReadingParameter raw} {X Y Z : AATSch p}
    (f : AATSchMorphism X Y) (g : AATSchMorphism Y Z) :
    (comp f g).toSchemeHom = f.toSchemeHom ≫ g.toSchemeHom

@[simp] theorem id_toSchemeMap
    {p : AATSchReadingParameter raw} (X : AATSch p) :
    (id X).toSchemeMap = 𝟙 X.scheme.underlying

@[simp] theorem comp_toSchemeMap
    {p : AATSchReadingParameter raw} {X Y Z : AATSch p}
    (f : AATSchMorphism X Y) (g : AATSchMorphism Y Z) :
    (comp f g).toSchemeMap = f.toSchemeMap ≫ g.toSchemeMap

end AATSchMorphism

instance AATSch.category
    (p : AATSchReadingParameter raw) : Category (AATSch p)

def AATSch.forget
    (p : AATSchReadingParameter raw) :
    AATSch p ⥤ LawAlgebra.StandardArchitectureScheme raw

instance AATSch.forget_faithful
    (p : AATSchReadingParameter raw) : (AATSch.forget p).Faithful

@[simp] theorem AATSch.forget_obj
    (p : AATSchReadingParameter raw) (X : AATSch p) :
    (AATSch.forget p).obj X = X.scheme

@[simp] theorem AATSch.forget_map
    (p : AATSchReadingParameter raw) {X Y : AATSch p} (f : X ⟶ Y) :
    (AATSch.forget p).map f = f.toSchemeHom

end RepresentationAnalysis
~~~

compatibility fieldは固定されたreading disciplineのmorphism条件である。SD9で少なくとも一つの
非恒真predicate、成立例、不成立例を発火させる。全predicateを`True`にしたfixtureを主証拠にしない。

### SD5 — analytic representationをMathlib Functorへ統合

analytic representationは定義2.1どおりFunctorそのものとする。

~~~lean
namespace RepresentationAnalysis

abbrev AnalyticRepresentation
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw)
    (Target : Type z) [Category Target] :=
  AATSch p ⥤ Target

structure RepresentationFamily
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) where
  Index : Type z
  Target : Index → CategoryTheory.Cat.{z, z}
  representation : ∀ i : Index, AnalyticRepresentation p (Target i)

instance FiniteDirectedGraphTarget.category
    (Vertex Edge RelationLabel : Type z) :
    Category (FiniteDirectedGraphTarget Vertex Edge RelationLabel) where
  Hom := FiniteDirectedGraphHom
  id := FiniteDirectedGraphHom.id
  comp := FiniteDirectedGraphHom.comp
  id_comp := FiniteDirectedGraphHom.id_comp
  comp_id := FiniteDirectedGraphHom.comp_id
  assoc := FiniteDirectedGraphHom.assoc

instance MatrixRepresentationTarget.category
    (Vertex Edge RelationLabel : Type z) :
    Category (MatrixRepresentationTarget Vertex Edge RelationLabel) where
  Hom := MatrixRepresentationHom
  id := MatrixRepresentationHom.id
  comp := MatrixRepresentationHom.comp
  id_comp := MatrixRepresentationHom.id_comp
  comp_id := MatrixRepresentationHom.comp_id
  assoc := MatrixRepresentationHom.assoc

structure GraphRepresentationProfile
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) where
  Vertex : Type z
  Edge : Type z
  RelationLabel : Type z
  representation :
    AnalyticRepresentation p
      (FiniteDirectedGraphTarget Vertex Edge RelationLabel)
  SelectedRelation : AATSch p → Type z
  relationEdge : ∀ X : AATSch p, SelectedRelation X → Edge
  selectedEdge : AATSch p → Edge → Prop
  relationEdge_selected : ∀ (X : AATSch p) (r : SelectedRelation X),
    selectedEdge X (relationEdge X r)

structure MatrixRepresentationProfile
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) where
  Vertex : Type z
  Edge : Type z
  RelationLabel : Type z
  representation :
    AnalyticRepresentation p
      (MatrixRepresentationTarget Vertex Edge RelationLabel)

end RepresentationAnalysis
~~~

この`abbrev`はdomain terminologyをMathlib `Functor`へ直接同定する唯一のsurfaceである。
`AnalyticTargetCategory`、`AsCategory`、独自`Hom` / `id` / `comp` / category-law field、
`AATSchIdentityData`、`AATSchCompositionData`、`AnalyticRepresentation.toFunctor`を残さない。

全consumerは次の置換を行う。

~~~text
R.targetCategory.Hom (R.obj X) (R.obj Y)  ->  R.obj X ⟶ R.obj Y
R.map I.morphism                           ->  R.map (𝟙 X)
R.map C.morphism                           ->  R.map (f ≫ g)
R.map_identity                             ->  R.map_id X
R.map_composition                          ->  R.map_comp f g
R.toFunctor                                ->  R
P.graphOf / P.matrixOf                     ->  P.representation.obj
P.mapGraph / P.mapMatrix                   ->  P.representation.map
P.toAnalyticRepresentation                 ->  P.representation
~~~

graph / matrix / signature等のtargetはMathlib `Category` instanceを持つ。instanceを対象ごとに重複fieldへ
格納せず、既存またはnamed instanceとして構成する。indexed familyは`CategoryTheory.Cat`へbundleし、
arbitrary target用のcustom category fieldを再導入しない。`GraphRepresentationProfile.toAnalyticRepresentation`、
`MatrixRepresentationProfile.toAnalyticRepresentation`、`RepresentationNotions.analyticMorphismEq`を含む全consumerの
完全signatureはmanifestで固定する。

### SD6 — synthesis package normalization

`AATSynthesisAssumptions`と`AATSynthesisConstructionInput`を削除し、single packageへ統合する。
site、ringed site、atlas、ideal sheaf、lawful closed geometryはparameter / fieldから導出する。

~~~lean
namespace RepresentationAnalysis

structure AATSynthesisPackage
    (P : Site.PartIPrerequisites.{u})
    (k : Type v) [CommRing k]
    (geometry : Site.ArchitectureGeometry P)
    (raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k)
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)] where
  architectureScheme : LawAlgebra.StandardArchitectureScheme raw
  lawReading :
    LawAlgebra.ClosedEquationalLawReading raw architectureScheme
  lawReadingValid :
    LawAlgebra.IsClosedEquationalLawReading raw architectureScheme lawReading
  requiredClosed :
    LawAlgebra.RequiredClosed raw architectureScheme lawReading
  requiredLawIdealExact :
    LawAlgebra.RequiredLawIdealExact raw architectureScheme lawReading
      lawReadingValid requiredClosed
  cover : Cohomology.CoverRelativeCechCover geometry.site
  obstructionSheaf : Cohomology.ObstructionSheaf geometry.site
  obstructionCohomology :
    Cohomology.CoverRelativeCechComplex cover obstructionSheaf
  derivedLawGeometry : Derived.RepairProfile.RepairComparisonProfile.{u}
  stratumParameter :
    SingularityMonodromyStack.StratumReadingParameter geometry.site
  singularityMonodromyStack :
    SingularityMonodromyStack.ArchitectureStratum.{u, v, w, x, y}
      stratumParameter k
  readingParameter : AATSchReadingParameter raw
  representationPeriodMetricAnalysis :
    AnalyticReadingContext.{u, v, w, x, y, z}
      P.architectureObject readingParameter

namespace AATSynthesisPackage

abbrev architectureObject
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (_Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) :=
  P.architectureObject

abbrev site
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (_Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) :=
  geometry.site

noncomputable abbrev ringedAATSite
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (_Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) :=
  raw.toRingedSite

abbrev affineAtlas
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) :=
  Q.architectureScheme.atlas

noncomputable def obstructionIdealSheaf
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) :
    Q.architectureScheme.underlying.IdealSheafData :=
  LawAlgebra.lawGeneratedIdealSheaf raw Q.architectureScheme Q.lawReading
    Q.lawReadingValid Q.requiredClosed

noncomputable def lawfulClosedSubscheme
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) :
    AlgebraicGeometry.Scheme :=
  LawAlgebra.lawfulClosedSubscheme raw Q.architectureScheme Q.lawReading
    Q.lawReadingValid Q.requiredClosed

noncomputable def lawfulClosedImmersion
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) :
    Q.lawfulClosedSubscheme ⟶ Q.architectureScheme.underlying :=
  LawAlgebra.lawfulClosedImmersion raw Q.architectureScheme Q.lawReading
    Q.lawReadingValid Q.requiredClosed

def analyticReadingContext
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) :
    AnalyticReadingContext.{u, v, w, x, y, z}
      P.architectureObject Q.readingParameter :=
  Q.representationPeriodMetricAnalysis

end AATSynthesisPackage
end RepresentationAnalysis
~~~

`AATSynthesisPackage`へAtom、AtomFamily、ArchitectureObject、AATSite、RingedAATSite、chart index、
chart family、ideal sheaf、lawful closed subscheme、closed immersionをfieldとして追加しない。
`algebraicGeometricAATSynthesis`という旧conjunction theoremはrepackageとして削除し、
Lean台帳ではsingle packageと上記projectionの実装状態を宣言単位で記録する。

### SD7 — consumer signature preservation contract

`C`の各public consumerはtracking Issueの`consumer signature manifest`をsignature正本とする。
manifestは対象main commitから機械抽出した旧signatureと、次の正規化規則を適用した新signatureを並べる。
SD3列挙対象だけは新signature本文の代わりに`SD3:<exact-name>`を置き、本PRDとの二重正本化を防ぐ。

| old type / expression | required replacement |
| --- | --- |
| `LawAlgebra.Scheme.ArchitectureScheme S k` | `LawAlgebra.StandardArchitectureScheme raw` |
| `LawAlgebra.Scheme.RingedAATTopos S k` | `raw.toRingedSite`を読むparameter / projection |
| `X.ChartIndex` / `X.chart` / `X.compatibility` | `X.atlas.Index` / `X.atlas.chart` / actual atlas・overlap validity API |
| `LawfulSectionData.FactorsThroughLawfulLocus` | `FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s` |
| three Cohomology `*factorsThroughFlat_U*` accessors | `delete-repackage`; Part IV main statementは変更しない |
| old `RepairRoute` ring / ideal / section fields | SD3のactual Scheme sectionとsingle factorization value |
| `LawfulnessIdealCorrespondenceAssumptions` / package field | SD3のcanonical theoremと明示premise |
| `p.SchemeMorphism X Y` | `X ⟶ Y` for `StandardArchitectureScheme raw` |
| `AATSchMorphism.underlying` | `AATSchMorphism.toSchemeHom` |
| `AATSchIdentityData` | `𝟙 X` |
| `AATSchCompositionData f g` | `f ≫ g` |
| `AnalyticTargetCategory Target` | `[Category Target]` |
| old `AnalyticRepresentation p Target` structure | `AATSch p ⥤ Target` |
| `RepresentationFamily.Target : Index → Type` | `RepresentationFamily.Target : Index → CategoryTheory.Cat` |
| graph / matrix object map、morphism map、law fields | SD5のsingle `representation : Functor` field |
| synthesis duplicate field | SD6のparameterまたはnamed projection |

manifestの各行は次のいずれか一つに分類する。

1. `preserve`: canonical型への置換以外、量化対象、material premise、結論を変えない。
2. `derive`: 旧accessorを削除し、canonical ownerの既存APIへconsumer proofを直結する。
3. `delete-repackage`: field projection、identity / composition wrapper、aliasだけで独立した数学的内容がない。
4. `stop-independent-content`: canonical ownerへまだ移されていない独立した数学的内容がある。

`stop-independent-content`が一件でもあれば、そのbatchは実装しない。`preserve`宣言でpremise追加、
結論弱化、対象縮小が必要になった場合も停止する。公開名だけを維持するwrapperは許可しない。

### SD8 — material premise分類

core targetと代表consumerのmaterial premiseを次で固定する。最終packetでは`N ∪ C ∪ E`の
全theoremについて
明示引数、typeclass、structure field、certificate fieldを独立に列挙し、この表へ展開する。
旧surfaceからcanonical geometryへ移す際のpremise置換は、旧premise、replacement、数学本文の根拠、
放電宣言、proof-useを一対一に記録した行だけをapproved replacementとする。
`material_premise_ledger_delta`は未分類または未承認の差分、`new_material_premise`は本文根拠も
放電宣言もない追加premiseを表す。approved replacement自体を隠れたzero差分として扱わない。

| material premise | 分類 | 放電宣言 / provenance | proof-use |
| --- | --- | --- | --- |
| `CommRing k` | 本文由来 | coefficient ring | raw、sheafification、scheme、ideal geometry全体 |
| `HasSheafify S.topology (AATCommAlgCat k)` | 本文由来のambient premise。concrete firingでは放電済み | merged named instance chain | `raw.toRingedSite`、`StandardArchitectureScheme`、closed geometry |
| `IsArchitectureAffineAtlas` / `IsArchitectureOverlapPresentation` | 放電済み | `StandardArchitectureScheme`のcanonical constructor、reference modelのnamed validity theorem | underlying Scheme、actual cover、overlap、cocycle |
| `IsClosedEquationalLawReading` | 本文由来。concrete firingでは放電済み | reference modelの`*_Reading_valid` | ideal sheafとcorrespondenceへ実引数として渡す |
| `RequiredClosed` | 本文由来。concrete firingでは放電済み | reference modelの`*_requiredClosed` | `lawGeneratedIdealSheaf`、lawful closed geometryへ実引数として渡す |
| `RequiredLawIdealExact` | 本文由来。concrete firingでは放電済み | reference modelの`*_requiredLawIdealExact` | semantic / ideal / factorization correspondenceへ実引数として渡す |
| old `witnessCoverage` / `uAdequateCover` / `obstructionSheafDescent` / `ringRestrictionCompatibility` fields | approved replacement | `RequiredLawIdealExact`と`RequiredObjectPointComparison`のnamed proofs | `lawfulnessIdealFactorizationCorrespondence`とsemantic / object comparisonへ渡し、旧Prop / certificate projectionは削除 |
| `RequiredObjectPointComparison` | 本文由来のsection / object comparison premise | consumerごとのnamed construction | valuation / signature comparison theoremへ実引数として渡す |
| obstruction soundness / completeness | 本文由来 | Part I valuation theoremまたはfinite witness | `factorsThroughLawfulClosedSubscheme_iff_omegaU_zero`へ実引数として渡す |
| axis exactness | 本文由来 | selected signature theorem | `factorsThroughLawfulClosedSubscheme_iff_requiredSignatureAxesZero`へ実引数として渡す |
| AATSch compatibility closure | fixed reading parameter data | SD4 parameterのidentity / composition closure field | `AATSch.category`のidentity / associativity proof |
| target `Category` | Mathlib ambient premise | concrete targetのnamed category instance | analytic representationをactual Functorとして型付けする |
| repair / signature factorization | 放電済み | `lawfulnessIdealFactorizationCorrespondence`、`factorizationLift`、reference point firing | repair / signature consumerのactual liftとtriangle |
| `RepairRoute.factorization` | 定義12.1のlawful-target data | SD3のsingle subtype value | route target membershipとcertificate accessorだけに使用し、別定理の結論生成に流用しない |
| synthesisのscheme / reading / cohomology / derived / stratum / analytic data | predecessor data | merged constructorsとreference fixture | SD6のfieldとして保持し、derived owner projectionへ接続する |

申告のないpremiseは`未放電`として扱う。`ofPresentation`へのproof入力、field accessor、
localに追加した結論相当instanceは放電証拠にしない。完了には
`material_premise_ledger_delta = ∅`かつ`new_material_premise = ∅`を要求する。

### SD9 — nondegenerate migration firing

`Formal/AG/Examples/LegacyConsolidation.lean`はmerged standard geometry reference modelを再利用し、
新しいpolynomial / atlas / ideal fixtureを複製しない。次のpublic targetを固定する。

~~~lean
namespace AAT.AG.Examples.LegacyConsolidation

noncomputable def standardPartIPrerequisites :
    Site.PartIPrerequisites where
  carrier := AAT.AG.FiniteModel.carrier
  core := AAT.AG.FiniteModel.corePackage

noncomputable def standardGeometry :
    Site.ArchitectureGeometry standardPartIPrerequisites where
  site := StandardGeometryReferenceModels.referenceSite

inductive ReferenceObstructionReading where
  | weak
  | strong
deriving DecidableEq

noncomputable def readingParameter :
    RepresentationAnalysis.AATSchReadingParameter
      StandardGeometryReferenceModels.referenceRaw where
  AtomLabelReading := PUnit
  LawReading := PUnit
  ObstructionIdealReading := ReferenceObstructionReading
  SignatureReading := PUnit
  InterpretationMapReading := PUnit
  atomLabelsCompatible _ _ _ := True
  lawReadingCompatible _ _ _ := True
  obstructionIdealCompatible _ a b := a = b
  signatureReadingCompatible _ _ _ := True
  interpretationMapCompatible _ _ _ := True
  id_atomLabelsCompatible _ _ := trivial
  id_lawReadingCompatible _ _ := trivial
  id_obstructionIdealCompatible _ _ := rfl
  id_signatureReadingCompatible _ _ := trivial
  id_interpretationMapCompatible _ _ := trivial
  comp_atomLabelsCompatible _ _ := trivial
  comp_lawReadingCompatible _ _ := trivial
  comp_obstructionIdealCompatible hab hbc := hab.trans hbc
  comp_signatureReadingCompatible _ _ := trivial
  comp_interpretationMapCompatible _ _ := trivial

noncomputable def overlapAATSch :
    RepresentationAnalysis.AATSch readingParameter where
  scheme := LawAlgebra.StandardArchitectureScheme.singleAffine
    StandardGeometryReferenceModels.referenceRaw
    (StandardGeometryReferenceModels.referenceScheme.atlas.pairContext
      StandardGeometryReferenceModels.referenceRaw
      StandardGeometryReferenceModels.leftIndex
      StandardGeometryReferenceModels.rightIndex)
  atomLabels := PUnit.unit
  lawReading := PUnit.unit
  obstructionIdealReading := .weak
  signatureReading := PUnit.unit
  interpretationMapReading := PUnit.unit

noncomputable def leftAATSch :
    RepresentationAnalysis.AATSch readingParameter where
  scheme := LawAlgebra.StandardArchitectureScheme.singleAffine
    StandardGeometryReferenceModels.referenceRaw
    (StandardGeometryReferenceModels.referenceScheme.atlas.chart
      StandardGeometryReferenceModels.leftIndex).context
  atomLabels := PUnit.unit
  lawReading := PUnit.unit
  obstructionIdealReading := .weak
  signatureReading := PUnit.unit
  interpretationMapReading := PUnit.unit

noncomputable def referenceAATSch :
    RepresentationAnalysis.AATSch readingParameter where
  scheme := StandardGeometryReferenceModels.referenceScheme
  atomLabels := PUnit.unit
  lawReading := PUnit.unit
  obstructionIdealReading := .weak
  signatureReading := PUnit.unit
  interpretationMapReading := PUnit.unit

noncomputable def strongReferenceAATSch :
    RepresentationAnalysis.AATSch readingParameter where
  scheme := StandardGeometryReferenceModels.referenceScheme
  atomLabels := PUnit.unit
  lawReading := PUnit.unit
  obstructionIdealReading := .strong
  signatureReading := PUnit.unit
  interpretationMapReading := PUnit.unit

noncomputable def overlapToLeftMorphism :
    overlapAATSch ⟶ leftAATSch

@[simp] theorem overlapToLeftMorphism_toSchemeMap :
    overlapToLeftMorphism.toSchemeMap =
      LawAlgebra.architectureChartRestriction
        StandardGeometryReferenceModels.referenceRaw
        (StandardGeometryReferenceModels.referenceScheme.atlas.pairToLeft
          StandardGeometryReferenceModels.referenceRaw
          StandardGeometryReferenceModels.leftIndex
          StandardGeometryReferenceModels.rightIndex)

noncomputable def leftChartMorphism :
    leftAATSch ⟶ referenceAATSch

@[simp] theorem leftChartMorphism_toSchemeMap :
    leftChartMorphism.toSchemeMap =
      (StandardGeometryReferenceModels.referenceScheme.atlas.chart
        StandardGeometryReferenceModels.leftIndex).map

theorem leftChartMorphism_not_isIso :
    ¬ IsIso leftChartMorphism.toSchemeMap

noncomputable def nonPreservingCandidate :
    referenceAATSch.scheme ⟶ strongReferenceAATSch.scheme

theorem nonPreservingCandidate_not_compatible :
    ¬ readingParameter.obstructionIdealCompatible nonPreservingCandidate
      referenceAATSch.obstructionIdealReading
      strongReferenceAATSch.obstructionIdealReading

inductive MigrationVertex where
  | overlap
  | leftChart
  | ambient
deriving DecidableEq, Fintype

inductive MigrationEdge where
  | overlapToLeft
  | leftToAmbient
deriving DecidableEq, Fintype

inductive MigrationLabel where
  | restricts
deriving DecidableEq, Fintype

def migrationGraph :
    RepresentationAnalysis.FiniteDirectedGraphTarget
      MigrationVertex MigrationEdge MigrationLabel where
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  source
    | .overlapToLeft => .overlap
    | .leftToAmbient => .leftChart
  target
    | .overlapToLeft => .leftChart
    | .leftToAmbient => .ambient
  relationLabel
    | .overlapToLeft => .restricts
    | .leftToAmbient => .restricts

noncomputable def graphRepresentation :
    RepresentationAnalysis.AnalyticRepresentation readingParameter
      (RepresentationAnalysis.FiniteDirectedGraphTarget
        MigrationVertex MigrationEdge MigrationLabel) where
  obj _ := migrationGraph
  map _ := 𝟙 migrationGraph
  map_id _ := by simp
  map_comp _ _ := by simp

@[simp] theorem graphRepresentation_obj_reference :
    graphRepresentation.obj referenceAATSch = migrationGraph

theorem graphRepresentation_map_id :
    graphRepresentation.map (𝟙 referenceAATSch) =
      𝟙 (graphRepresentation.obj referenceAATSch)

theorem graphRepresentation_map_comp :
    graphRepresentation.map (overlapToLeftMorphism ≫ leftChartMorphism) =
      graphRepresentation.map overlapToLeftMorphism ≫
        graphRepresentation.map leftChartMorphism

noncomputable def synthesisPackage :
    RepresentationAnalysis.AATSynthesisPackage
      standardPartIPrerequisites Int standardGeometry
      StandardGeometryReferenceModels.referenceRaw

theorem synthesisPackage_fires :
    synthesisPackage.site =
        StandardGeometryReferenceModels.referenceSite ∧
      synthesisPackage.ringedAATSite =
        StandardGeometryReferenceModels.referenceRaw.toRingedSite ∧
      synthesisPackage.architectureScheme =
        StandardGeometryReferenceModels.referenceScheme ∧
      synthesisPackage.lawReading =
        StandardGeometryReferenceModels.weakReading ∧
      synthesisPackage.readingParameter = readingParameter ∧
      synthesisPackage.obstructionIdealSheaf =
        LawAlgebra.lawGeneratedIdealSheaf
          StandardGeometryReferenceModels.referenceRaw
          StandardGeometryReferenceModels.referenceScheme
          StandardGeometryReferenceModels.weakReading
          StandardGeometryReferenceModels.weakReading_valid
          StandardGeometryReferenceModels.weakReading_requiredClosed ∧
      synthesisPackage.lawfulClosedSubscheme =
        LawAlgebra.lawfulClosedSubscheme
          StandardGeometryReferenceModels.referenceRaw
          StandardGeometryReferenceModels.referenceScheme
          StandardGeometryReferenceModels.weakReading
          StandardGeometryReferenceModels.weakReading_valid
          StandardGeometryReferenceModels.weakReading_requiredClosed ∧
      Nonempty
        (LawAlgebra.FactorsThroughLawfulClosedSubscheme
          StandardGeometryReferenceModels.referenceRaw
          StandardGeometryReferenceModels.referenceScheme
          StandardGeometryReferenceModels.weakReading
          StandardGeometryReferenceModels.weakReading_valid
          StandardGeometryReferenceModels.weakReading_requiredClosed
          StandardGeometryReferenceModels.zeroPoint)

end AAT.AG.Examples.LegacyConsolidation
~~~

`standardPartIPrerequisites`はPart Iの`FiniteModel.corePackage`を唯一のcore provenanceとし、
`standardGeometry.site`はmerged reference modelの`referenceSite`とdefinitionally一致させる。
upstream reviewで`referenceSite`またはそのobject provenanceが変更された場合は実装を始めず、
このSDとexecutable contractを同じ差分で改訂する。実装中の別名への読み替えはしない。

firing matrixは次である。

| lane | positive | negative | 非退化条件 |
| --- | --- | --- | --- |
| standard Scheme | `referenceScheme`、actual two-chart cover、nonempty overlap | 旧Scheme宣言no-hit | actual Mathlib Scheme、異なる二chart、proper chart inclusion |
| actual lawful geometry | weak / strong ideal sheaf、closed subscheme、zero point factorization | one / two pointのnamed non-factorization | nonzero proper ideal、actual lift、triangle |
| AATSch | `overlapToLeftMorphism`、`leftChartMorphism`、forgetful functor、composition | `nonPreservingCandidate_not_compatible` | proper chart inclusion、non-isomorphism、compatibility predicateが非恒真 |
| analytic representation | `graphRepresentation_map_id`、`graphRepresentation_map_comp` | custom target category / wrapper no-hit | Mathlib Functor lawを直接使用 |
| synthesis | `synthesisPackage_fires` | duplicate field / equality field no-hit | same provenanceのScheme、ideal sheaf、actual factorization |
| deletion | `L`全name / field / module path no-hit | — | archiveとgit historyだけをscan対象外にする |

### SD10 — executable contract、audit、no-hit contract

`StatementContractsLegacyConsolidation.lean`は次を満たす。

- `N ∪ C ∪ E ∪ P`の全public declarationをexact-type `example`で一対一に検査する。
- automatic projectionを含むstructure fieldは、target name集合へ展開して型を検査する。
- `AnalyticRepresentation`がdefinitionally Mathlib `Functor`であることを両方向の型代入で検査する。
- consumer signature manifestの`preserve`行すべてを直接参照する。
- 削除済み宣言をcontract内で再定義しない。

no-hit contractは`docs/archive/`、`.git/`、git historyを除くcurrent repositoryを対象にする。

~~~text
removed_declaration_hits = ∅
removed_field_hits = ∅
removed_module_path_hits = ∅
legacy_namespace_hits = ∅
deprecated_alias_hits = ∅
exported_adapter_hits = ∅
old_contract_hits = ∅
old_audit_hits = ∅
old_ledger_hits = ∅
~~~

`AxiomAudit.lean`は`N ∪ C ∪ E`中の全new / changed theoremをexact nameで登録する。
代表theoremだけの登録、aggregate経由の偶然の到達、旧audit aliasの温存を認めない。

## 数学本文との対応

| 数学本文 | canonical Lean owner | このPRDの処置 |
| --- | --- | --- |
| 第II部 selected site / sheafification | `RingedAATSite`、`raw.toRingedSite` | 旧`RingedAATTopos` packageを削除しcanonical生成物を使う |
| 第III部 定義9.2〜10.3、Appendix A.5 | `StandardArchitectureScheme`、actual atlas / overlap API | 自由なProp chart compatibilityと旧Schemeを削除 |
| 第III部 定義6.1〜7.2 | selected witness ideal、actual `IdealSheafData`、closed subscheme | set-level helperとactual geometryを用途別に分ける |
| 第III部 定理11.1 | `lawfulnessIdealFactorizationCorrespondence`とactual factorization edge | assumptions / result packageのfield projectionを削除 |
| 第VII部 定義2.1 | `AATSch` category、Mathlib `Functor` | custom morphism categoryとcustom target categoryを削除 |
| 第VII部 定義7.2 | SD3のsignature / curvature context | actual factorization、valuation、signature edgeへ直接接続 |
| 第VII部 定義12.1 | SD3の`RepairRoute` | lawful targetをactual closed-subscheme factorizationで保持 |
| 第VII部 定理16.1 | SD6のsingle synthesis packageとcanonical projections | 重複value / equality fieldによる再包装を削除 |

本PRDは数学本文を編集しない。本文の用語をLeanの旧宣言名へ合わせて改稿しない。

## 問い

Atom由来site、canonical sheafification、standard Scheme、law-generated actual closed geometry、
actual factorization、decorated scheme category、analytic Functorを唯一の実装経路とし、旧wrapper、
自由な`Prop` slot、結論再包装、重複coherence fieldを全consumerから除去できるか。

~~~text
ReadingCore / raw
  -> RingedAATSite
  -> StandardArchitectureScheme
  -> lawGeneratedIdealSheaf
  -> lawfulClosedSubscheme
  -> actual factorization
  -> AATSch category
  -> Mathlib Functor
  -> normalized synthesis package
~~~

最終snapshotでは新旧二系統を維持しない。compatibility alias、`Legacy*` rename、期限なしdeprecation、
旧module re-exportを残さない。

## 現状診断

- `LawAlgebra/Scheme.lean`はType-valued sheaf object、structure sheaf、独立した
  `LocallyRingedSpace`を同一provenanceなしに保持する`RingedAATTopos`を公開している。
- `ChartCompatibility`、`SchemeGluingData`、`AffineReturnConditions`はopen immersion、overlap、
  cocycle、affineness等を自由な`Prop`として受け取る。
- 旧`ArchitectureScheme`はactual Mathlib `Scheme`、actual affine open cover、actual pullback overlapを
  fieldに持たず、`singleAffineSpec`のidentity caseが下流packageを発火させる。
- `SheafImageConstruction`はring idealとequality fieldであり、actual sheaf imageまたは
  `Scheme.IdealSheafData`ではない。
- `FactorsThroughLawfulLocus`はpulled ideal vanishingの再包装で、actual lift morphismとtriangleを持たない。
- `LawfulnessIdealCorrespondenceAssumptions` / packageは、定理11.1の主要edgeをfieldとして受け取り、
  field projectionで五項対応を作れる。
- Part IIIのcanonical closed-equational geometryにはactual ideal sheaf、closed subscheme、lift、triangle、
  uniqueness、semantic correspondenceがすでに別ownerとして存在する。
- `AATSchReadingParameter`はunderlying scheme morphism、identity、composition、category lawを独自dataとして持つ。
- `AnalyticTargetCategory`と`AnalyticRepresentation`はMathlib category / Functorを再実装し、
  identity / composition wrapperを介して後からFunctorへ戻している。
- synthesis packageはsite、ringed object、scheme、chart family、set-level locusを重複保存し、
  equality fieldで再結合する。
- bootstrap、Cohomology、RepresentationAnalysis、stack、Measurement、Evolution、SemanticRepair、
  examples、statement contracts、axiom auditまで旧routeが伝播している。

## アウトカム

完了時に次が成り立つ。

1. `LawAlgebra/Scheme.lean`と全旧宣言がcurrent repositoryから消えている。
2. ringed dataは`raw.toRingedSite`、scheme dataは`StandardArchitectureScheme raw`だけから読まれる。
3. obstruction geometryはactual `IdealSheafData`、closed subscheme、closed immersionを使う。
4. factorization consumerはactual liftとtriangleを使う。
5. 定理11.1 consumerはcanonical theoremと明示premiseをproof-useする。
6. `AATSch`のunderlying morphismは`StandardArchitectureScheme.Hom`である。
7. analytic representationはMathlib `Functor`であり、custom category wrapperがない。
8. synthesis packageはcanonical ownerから導出できる値を重複保存しない。
9. 全public consumerのstatement strengthがmanifestで保存される。
10. nondegenerate reference modelが旧routeなしでScheme、factorization、AATSch、Functor、synthesisを発火する。
11. removed name、module、adapter、contract、audit、ledgerのrepository-wide hitがzeroである。

## 採否規律

- `docs/aat/algebraic_geometric_theory/**`を変更しない。
- canonical prerequisiteがmergeされる前に旧宣言を削除しない。
- `StandardArchitectureScheme`を最終公開名とし、旧`ArchitectureScheme`へrenameしない。
- 最終snapshotにexported compatibility shim、deprecated alias、`Legacy*` namespace、旧module re-exportを残さない。
- 一時adapterはprivate namespace、aggregate非公開、削除Issue必須とし、target theorem、contract、audit、
  reference modelの入力に使わない。
- set-level zero locusをactual closed geometryの完了証拠にしない。
- ring-level vanishingをactual factorizationと呼ばない。
- custom category / Functor wrapperをcanonical analytic representationと呼ばない。
- archived文書は現行参照scanと改稿の対象にしない。
- G-07、Research source、数学本文のstatementを変更しない。

## 改修要求

### R0 — inventory、signature manifest、batch DAG

- 対象main commitを固定し、`L`、`K`、`N`、`C`、`E`、`P`をexact nameで生成する。
- declaration、field、constructor、namespace、module import、docstring、example、contract、audit、台帳を抽出する。
- `C`の各宣言について旧完全signature、新完全signatureまたはSD3参照、処置分類、proof owner、batchを固定する。
- leaf consumerからownerへ向かう依存順と、owner導入後にleafへ戻る削除順を分離して記録する。
- inventory外の旧routeが見つかったbatchは停止する。

### R1 — legacy Scheme module deletion準備

- bootstrap aliasをSD2のraw-indexed `StandardArchitectureScheme`へ変更する。
- stack atlas、stratum、Measurement、Evolution、SemanticRepairのscheme fieldをcanonical型へ移す。
- chart index、chart map、coverage、overlap、cocycleをcanonical APIから取得する。
- single-affine exampleは`StandardArchitectureScheme.singleAffine`、nondegenerate exampleはstandard reference modelで再構成する。
- 全consumer移行後に`LawAlgebra/Scheme.lean`とaggregate importを削除する。

### R2 — obstruction ideal / lawful geometry consolidation

- `SheafImageConstruction`と全accessorを削除する。
- actual geometry consumerを`lawGeneratedIdealSheaf`、`lawfulClosedSubscheme`、
  `lawfulClosedImmersion`へ移す。
- set-level `lawfulLocus` / `localLawfulLocus`はaffine calculationに限定するdocstringへ更新する。
- actual geometry completionにset-level helperを使用していないことをproof dependencyで確認する。

### R3 — factorization / correspondence consolidation

- CohomologyのPart IV main statementはsignatureを維持し、SD3で列挙した三つの旧factorization
  accessorだけを削除する。
- repair routeとsignature / curvature consumerをactual closed subscheme factorizationへ移す。
- assumptions / result packageを削除し、canonical correspondence edgeを直接proof-useする。
- `RequiredObjectPointComparison`、soundness、completeness、axis exactnessを個別premiseとして維持する。
- actual factorizationへ移せないconsumerはstatementを弱めず停止する。

### R4 — AATSch category consolidation

- `AATSchReadingParameter`をSD4へ置換する。
- `AATSch.scheme`を`StandardArchitectureScheme raw`へ変更する。
- `AATSchMorphism.toSchemeHom`と`toSchemeMap`を実装する。
- identity、composition、category、forgetful functor、faithfulnessをcanonical categoryから構成する。
- `AATSchIdentityData`、`AATSchCompositionData`、`AATSchFiberProductData`を削除する。
- fiber productが必要なconsumerはMathlib pullback coneとdecoration compatibilityのactual theoremを使う。

### R5 — analytic representation consolidation

- `AnalyticTargetCategory`と全wrapperを削除する。
- concrete targetへnamed Mathlib `Category` instanceを与え、indexed familyのtargetは
  `CategoryTheory.Cat`へbundleする。
- `AnalyticRepresentation`をSD5のFunctor abbreviationへ変更する。
- GraphMatrix、PreservationReflection、Period、FiniteHomology、AnalyticContext等のconsumerを
  `Functor.map_id` / `map_comp`へ移す。
- graph / matrix profileはSD5のsingle `representation` fieldへ正規化し、object map、morphism map、
  Functor lawを別fieldへ重複保存しない。
- custom category law fieldをconsumer structureへ移し替えない。

### R6 — synthesis package normalization

- `AATSynthesisAssumptions`と`AATSynthesisConstructionInput`を削除する。
- `AATSynthesisPackage`をSD6のsingle packageへ変更する。
- site、ringed site、atlas、ideal sheaf、lawful closed geometry、analytic contextをnamed projectionで読む。
- 旧conjunction theoremとconstructed-package existentialを削除する。
- Lean台帳はpackage、projection、reference firingの実装状態だけを現行宣言に沿って同期する。

### R7 — transitive consumer migration

- `consumer signature manifest`の全行をbatch順に移行する。
- `preserve`行はcanonical型への置換以外のstatement diffをzeroにする。
- `derive`行はcanonical APIのproof-useをcontractとreviewで確認する。
- `delete-repackage`行は全consumer移行後に削除する。
- `stop-independent-content`行が出た場合は別Issueへ逃がさず、当該batchと本PRDの再設計を止める。

### R8 — nondegenerate examples

- SD9のoverlap / left / ambient `AATSch`、proper chart inclusion、invalid candidateをstandard reference modelから構成する。
- graph representationをactual Functorとして構成する。
- normalized synthesis packageを同じreference raw / Scheme / weak readingから構成する。
- PUnit、zero ideal、empty Scheme、identity mapだけのexampleを主証拠にしない。
- 旧`RepresentationAnalysisPart7` fixtureはcanonical inputで再構成するか、独立内容がなければ削除する。

### R9 — contracts、audit、aggregate、台帳

- `StatementContractsLegacyConsolidation.lean`を作成し、`N ∪ C ∪ E ∪ P`を全数登録する。
- `StatementContracts.lean`、`AxiomAudit.lean`、aggregate importをcanonical moduleへ同期する。
- theorem indexとproof-obligation台帳を現行宣言へ同期する。
- `Formal/AG`からResearch moduleをimportしない。
- 新しいMarkdown theorem ledgerを作らない。

### R10 — final deletionとlifecycle

- `L`、旧module path、deprecated attribute、adapter namespace、old constructor、duplicate equality fieldを
  repository-wide scanする。
- temporary adapter、adapter専用module、削除Issueをzeroにする。
- contract targetが`N ∪ C ∪ E ∪ P`、audit targetが`N ∪ C ∪ E`中のtheorem、
  material premise対象が`N ∪ C ∪ E`と一致することを検査する。
- review、CI、merge、現行source同期後にPRD参照をzeroにし、`docs/guideline.md`に従ってarchiveする。

## Acceptance Criteria

- [ ] AC1: tracking Issueが対象main commit、`L`、`K`、`N`、`C`、`E`、`P`、module DAG、batch、依存順をexact nameで固定している。
- [ ] AC2: `consumer signature manifest`が`C`の全public declarationを覆い、旧完全signature、新完全signatureまたはSD3参照、処置、proof ownerを持つ。
- [ ] AC3: SD2〜SD6のcore statement、SD3の列挙consumer、SD9のfiring statement、consumer manifestが同じsignatureを重複して正本化していない。
- [ ] AC4: executable contractのtarget name集合が`N ∪ C ∪ E ∪ P`と一致し、全targetをexact-type `example`で検査する。
- [ ] AC5: AxiomAuditのtarget name集合が`N ∪ C ∪ E`中の全new / changed theoremと一致する。
- [ ] AC6: `LawAlgebra/Scheme.lean`、旧`RingedAATTopos`、旧`ChartCompatibility`、旧`ArchitectureScheme`、`singleAffineSpec`、`SchemeGluingData`、`AffineReturnConditions`と全参照がzeroである。
- [ ] AC7: actual architecture schemeの公開名が`StandardArchitectureScheme`に一意化されている。
- [ ] AC8: Parts VII〜Xの`UsesArchitectureScheme`がraw-indexed canonical型を返す。
- [ ] AC9: 全scheme consumerがactual Mathlib `Scheme`、actual atlas、actual overlap presentationを使用する。
- [ ] AC10: `SheafImageConstruction`と全参照がzeroである。
- [ ] AC11: actual obstruction geometryが`lawGeneratedIdealSheaf : Scheme.IdealSheafData`を使用する。
- [ ] AC12: set-level lawful locusはaffine calculationに限定され、actual closed geometry completionに使われない。
- [ ] AC13: `FactorsThroughLawfulLocus`と全accessor / consumerがzeroである。
- [ ] AC14: factorization consumerがactual morphism、triangle equality、一意性を持つcanonical APIを使用する。
- [ ] AC15: SD3の三Cohomology accessorがzeroであり、Part IVのcover、local / restricted section、mismatch、cocycle、adequacy、coboundary dataと4本のno-global-section theoremが完全signatureを維持する。
- [ ] AC16: `LawfulnessIdealCorrespondenceAssumptions` / packageと同型のconclusion-shaped structureがzeroである。
- [ ] AC17: repair routeとsignature / curvature consumerがSD3で固定したactual target名を持ち、canonical factorization / valuation / signature theoremを直接proof-useする。
- [ ] AC18: `AATSchReadingParameter`に`SchemeMorphism`、custom identity、custom composition、category-law fieldがない。
- [ ] AC19: `AATSch.scheme`が`StandardArchitectureScheme raw`である。
- [ ] AC20: `AATSchMorphism.toSchemeHom`が`StandardArchitectureScheme.Hom`、`toSchemeMap`がその`.base`である。
- [ ] AC21: `AATSch` categoryのidentity / compositionがcanonical `StandardArchitectureScheme` categoryへ写る。
- [ ] AC22: `AATSch.forget`がfaithfulで、object / map projectionがcontractで固定される。
- [ ] AC23: `AATSchIdentityData`、`AATSchCompositionData`、`AATSchFiberProductData`と全参照がzeroである。
- [ ] AC24: `AnalyticTargetCategory`、`AsCategory`、`finiteDirectedGraphTargetCategory`、`matrixRepresentationTargetCategory`、custom target category fieldと全参照がzeroである。
- [ ] AC25: `AnalyticRepresentation`がdefinitionally Mathlib `Functor`であり、`RepresentationFamily.Target`が`CategoryTheory.Cat`を返す。
- [ ] AC26: analytic consumerが`Functor.map_id` / `map_comp`を直接使い、graph / matrix profileにobject map、morphism map、Functor lawの重複fieldがない。
- [ ] AC27: `AATSynthesisAssumptions`、`AATSynthesisConstructionInput`、両`toPackage`と全参照がzeroである。
- [ ] AC28: normalized `AATSynthesisPackage`がSD6のfieldだけを持つ。
- [ ] AC29: site、ringed site、atlas、ideal sheaf、lawful closed geometryがSD6のcanonical owner projectionから得られる。
- [ ] AC30: synthesis packageにAtom、AtomFamily、ArchitectureObject、AATSite、ringed site、chart family、ideal sheaf、locus、immersionの重複fieldとcoherence equalityがない。
- [ ] AC31: 旧`algebraicGeometricAATSynthesis` conjunction theoremとconstructed-package existentialがzeroである。
- [ ] AC32: manifestの全`preserve`行でcanonical型置換以外のstatement diffがzeroである。
- [ ] AC33: manifestの全`derive`行でcanonical ownerのproof-useが確認される。
- [ ] AC34: manifestに未処理`stop-independent-content`行がない。
- [ ] AC35: SD9の`leftChartMorphism.toSchemeMap`がreference modelのleft chart mapに一致し、`¬ IsIso`が証明されている。
- [ ] AC36: SD9に少なくとも一つの非恒真compatibility predicate、成立例、不成立例がある。
- [ ] AC37: graph representationがactual Mathlib Functorでidentity / compositionを発火する。
- [ ] AC38: `standardPartIPrerequisites`、`standardGeometry`、normalized synthesis packageが同じPart I core / reference site provenanceを持ち、standard reference Scheme、weak ideal sheaf、zero point actual factorizationを発火する。
- [ ] AC39: main firingがPUnit、zero ideal、empty Scheme、identity mapだけに依存しない。
- [ ] AC40: `L`のdeclaration、field、module path、namespace、constructorのcurrent repository hitがzeroである。
- [ ] AC41: deprecated alias、`Legacy*` rename、exported adapter、旧module re-exportがzeroである。
- [ ] AC42: old statement contract、old audit entry、old theorem-index entryがzeroである。
- [ ] AC43: temporary adapter、adapter専用module、削除Issueが最終snapshotでzeroである。
- [ ] AC44: 全new / changed declarationにdocstringがあり、自明でないdefinitionに`Implementation notes`がある。
- [ ] AC45: 下流proofがnew / changed core definitionのunfoldに依存しない。
- [ ] AC46: `material_premise_ledger_delta = ∅`かつ`new_material_premise = ∅`である。
- [ ] AC47: new / changed theoremがstandard axiomsのみを使用する。
- [ ] AC48: `docs/aat/algebraic_geometric_theory/**`、G-07、Research sourceに差分がない。
- [ ] AC49: aggregate import graphがModule import contractと一致し、Research reverse importがない。
- [ ] AC50: 統括エージェントがPR前に`lake build`を一度だけ実行し、PR後のfull buildはCIでgreenである。
- [ ] AC51: `math-lean-review`の4本がすべて合格、またはfinding全解消後に
  `review-protocol.md`に従う有資格な直接対応が記録される。
- [ ] AC52: 全child PRがmergeされ、tracking Issueと依存Issueのstatusが同期される。
- [ ] AC53: `docs/guideline.md`のarchive前条件として、AC1〜AC52、review、CI、merge、
  現行sourceへの成果反映、repository-wide live reference zeroがすべて満たされる。

AC53を満たした後、contentを変更せずPRDをarchiveする。移動後にcontent-invariant move、
現行repositoryからの参照zero、archive文書が現行sourceとして参照されていないことを確認する。

## Failure Contract

次は完了ではなく失敗である。

- 旧名をcanonical型のaliasにして移行完了とする。
- `LegacyRingedAATTopos`、`LegacyArchitectureScheme`等へrenameする。
- deprecated alias、旧module re-export、一時adapterを最終snapshotに残す。
- `StandardArchitectureScheme`を旧`ArchitectureScheme`へrenameして二つの履歴を混ぜる。
- `LocallyRingedSpace`だけをunderlying objectに持つpackageをactual Schemeと呼ぶ。
- open immersion、coverage、overlap、cocycleを自由な`Prop`で受け取る。
- `SheafImageConstruction`をrenameし、idealとequality fieldを温存する。
- set-level zero locusをactual closed subschemeと呼ぶ。
- pulled ideal equalityを別Propで包みactual factorizationと呼ぶ。
- actual factorizationのlift、triangle、uniquenessをinput fieldへ別々に受け取る。
- correspondence edgeをassumptions / result packageのfieldとして受け取り、projectionで閉じる。
- `AATSch`へcustom Scheme morphism carrier、identity、composition、category lawを残す。
- analytic target categoryまたはFunctor lawをcustom structureで再実装する。
- `AATSchIdentityData` / `AATSchCompositionData`をrenameして温存する。
- synthesis packageで同じvalueを二重保持し、equality fieldで整合させる。
- consumer statementを弱める、量化対象を狭める、本文にないmaterial premiseを追加する。
- PUnit、single-affine identity、zero ideal、empty locusだけでmigration firingを済ませる。
- contract / audit / 台帳だけを新名へ変更し、proof consumerを旧routeに残す。
- integrated firing theorem一件、build green、axiom scan、宣言名の存在だけで完了とする。
- 新しいdrift-prone Markdown migration ledgerを作る。

## 停止条件

次のいずれかが起きた時点で該当batchを停止する。

- canonical prerequisitesが未merge、または最終公開名・inventory・consumer signatureが未固定である。
- fixed signatureを弱める、material premiseを増やす、結論相当fieldを追加する必要が生じた。
- 旧宣言にcanonical ownerへまだ移されていない独立した数学的内容が見つかった。
- actual Scheme atlas / overlapへ移行できず、自由なcompatibility Propが必要になる。
- repair / signatureのring-level lawful section consumerをactual Scheme morphismへ接続できない。
- actual factorizationのliftまたはtriangleを構成できない。
- `SignatureCurvatureLawfulFactorizationContext`をcanonical valuation / signature theoremへ接続できない。
- `AATSch`のunderlying morphismを`StandardArchitectureScheme.Hom`で表せない。
- analytic consumerをMathlib Functorへ移すために独立morphism carrierが必要になる。
- synthesis packageのderived valueを除くと既存の独立claimを表現できない。
- standard reference site上でSD6のcover、obstruction cohomology、derived、stratum、analytic fieldの
  constructor termを構成できない。
- nondegenerate canonical exampleを維持できず、identity、zero、empty caseだけになる。

停止報告には、該当SD / AC、旧宣言とconsumer、旧 / 新fixed signature、必要な追加premise、
試したcanonical route、最小blocker、構成できた最長のprovenance chain、保持すべき独立内容を記録する。

## Non-goals

- G-07、conormal sequence、Čech connecting class、first-order liftの本体蒸留。
- reading functoriality、coverage refinement、coefficient base changeの新定理追加。
- closed-equational geometryまたはstandard reference modelの数学的強化。
- stack、gerbe、derived、cotangent、normal coneの新定理追加。
- legacy移行と無関係な既存weak surfaceのrepository-wide一括改修。
- ArchSig、ArchMap、tooling、websiteの変更。
- 数学本文へのLean status、Issue、PR、declaration名の追加。
- `docs/aat/algebraic_geometric_theory/**`の編集。

## 検証

検証主体、PR前のfull build回数、PR後のCI、diff / hidden Unicode / privacy / placeholder /
Research import scanは`AGENTS.md`と既存検査scriptを直接適用し、本PRDへ一般手順を複製しない。

実装中のfocused checkは変更batchごとの単一非aggregate fileに限定する。少なくとも次をbatch ownerが実行する。

~~~bash
lake env lean Formal/AG/RepresentationAnalysis/AATSch.lean
lake env lean Formal/AG/RepresentationAnalysis/Synthesis.lean
lake env lean Formal/AG/Examples/LegacyConsolidation.lean
lake env lean Formal/AG/StatementContractsLegacyConsolidation.lean
~~~

task固有の追加検査は次である。

- `L` / `K` / `N` / `C` / `E`と`P ⊆ K`の集合等式
- implementation public names、contract target names、audit theorem namesの一致
- consumer manifestの全行処置済み、statement diff zero、未処理分類zero
- removed declaration / field / module / adapter / contract / audit / ledgerのno-hit
- `AATSchMorphism.toSchemeHom` / `toSchemeMap`、forgetful faithfulness
- concrete compatibilityのpositive / negative firing
- analytic Functorの`map_id` / `map_comp`
- synthesis packageのfield一覧とcanonical projection一覧
- standard reference Scheme / ideal / factorizationからのsame-provenance firing
- `material_premise_ledger_delta = ∅`、`new_material_premise = ∅`
- protected math source差分zero

## Completion evidence packet

tracking Issueの専用completion commentをpacketの一意な保存先とする。最終PR commentは対象commit SHA、
packetへのlink、短い判定だけを持ち、packet本文を複製しない。

1. **Snapshot**
   - commit SHA
   - 対象module一覧
   - child Issue / PR / merge対応
   - `L`、`K`、`N`、`C`、`E`、`P`のexact name集合
2. **Inventory and disposition**
   - 旧declaration / field / module / consumerの全数表
   - 各処置分類と最終owner
   - inventory追加履歴と再承認
3. **Statement preservation**
   - consumer signature manifest
   - `P`全宣言の対象main commit signatureとのexact一致
   - 全`preserve`行の旧 / 新signatureまたはSD3参照とstatement diff zero
   - 全`derive`行のcanonical proof-use
   - `delete-repackage`の独立内容なし判定
   - 未処理`stop-independent-content = ∅`
4. **Canonical geometry**
   - `raw.toRingedSite`
   - `StandardArchitectureScheme` actual Scheme / atlas / overlap
   - `lawGeneratedIdealSheaf`
   - lawful closed subscheme / immersion
   - actual factorization lift / triangle / uniqueness
5. **AATSch and analytic representation**
   - `toSchemeHom` / `toSchemeMap`
   - category / forgetful functor / faithfulness
   - compatibility positive / negative example
   - proper chart inclusionと`¬ IsIso`
   - Mathlib Functor `map_id` / `map_comp`
6. **Synthesis normalization**
   - final field list
   - derived projection list
   - duplicate field / equality field no-hit
   - standard reference model firing
7. **Premise discharge**
   - `N ∪ C ∪ E`の全premise三分類
   - 旧premiseからcanonical premiseへのapproved replacement map
   - 放電宣言とproof-use
   - `material_premise_ledger_delta = ∅`
   - `new_material_premise = ∅`
8. **Deletion evidence**
   - removed declaration / field / module path no-hit
   - deprecated alias / `Legacy*` / adapter / re-export no-hit
   - old contract / audit / ledger no-hit
9. **Kernel evidence**
   - focused Lean checks
   - 統括エージェントによる一回の`lake build`
   - executable contract
   - AxiomAudit
   - static scans
   - CI URLと結果
10. **Independent review**
    - `math-lean-review` 4査読の判定
    - findingがあった場合の修正後確認または正式再査読
11. **Lifecycle**
    - merge済み宣言 / aggregate確認
    - current repositoryからのPRD reference zero
    - archive予定path

archive後はcontent-invariant moveと現行reference zeroをpost-archive checkとしてtracking Issueへ追記する。

次の組合せだけではcompletion evidenceにならない。

- build green + removed nameの一部no-hit
- `#print axioms` + docs更新
- integrated firing theorem一件
- alias + inherited instance
- positive exampleだけ
- tracking Issueの自己申告だけ
