# PRD: AAT Lean Legacy Consolidation

- 作成: 2026-07-13
- 改訂: 2026-07-17
- 対象module:
  - `Formal/AG/LawAlgebra/Scheme.lean`（削除）
  - `Formal/AG/LawAlgebra/ObstructionIdeal.lean`
  - `Formal/AG/LawAlgebra/LawfulLocus.lean`
  - `Formal/AG/LawAlgebra/Correspondence.lean`
  - `Formal/AG/LawAlgebra/FiniteExamples.lean`
  - `Formal/AG/LawAlgebra/StandardScheme.lean`（保持anchorのsignature参照）
  - `Formal/AG/LawAlgebra/ClosedEquationalGeometry.lean`（保持anchorのsignature参照）
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
  - `docs/aat/algebraic_geometric_theory/part_4_obstruction_cohomology.md`
    定義5.1〜5.3、6.1〜6.2、定理7.1
  - `docs/aat/algebraic_geometric_theory/part_7_representation_periods_analysis.md`
    定義2.1、7.2、12.1、定理16.1
  - `docs/aat/algebraic_geometric_theory/appendix.md` A.4〜A.8
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、
  `docs/aat/lean_quality_standard.md`
- tracking Issue: 実装開始時に作成し、対象main commit、SD0の`M_base` / `M₀` / 4 seed /
  consumer closure / `H` / `Ω₀` / `Ω` / `disposition_rows` / `T` / `L` / `K` / `N` / `C` /
  `E` / `P`、最終public inventory、
  Module import delta contractの`D` / `I₀`、
  consumer signature manifest、dependencyを
  exact nameで固定する。Issue番号と進捗は本PRDへ書かない
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
   - SD0の`M_base`、`M₀`、`L_seed` / `K_seed` / `N_seed` / `E_seed`、consumer closure、
     `H`（予定変更Lean module）、`Ω₀`、`Ω`、`disposition_rows`、
     `T`（変更module内の既存contractable public surface）、`L`（must-not-remain）、
     `K`（保持）、`N`（新規・shape変更core）、`C`（変更対象consumer）、`E`（firing）、
     `P = T ∩ K`（signature固定）のexact name集合
   - closure安定、`H ⊆ M₀`、`K_seed ⊆ K`、`unclassified_inventory_items = ∅`、
     `multiply_classified_inventory_items = ∅`、最終diffのLean module集合が`H`と一致し、
     `final_public_inventory = Ω \ L`
   - Module import delta contractの`D = M₀`と、全`M ∈ D`のordered `I₀(M)`。新規fileは`[]`
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

## Module import delta contract

import contractのdomainを`D = M₀`とする。tracking Issueでpinした対象main commitについて、
各`M ∈ D`のordered direct import listを`I₀(M)`として機械抽出し、編集開始前に全文をIssueへ
materializeする。対象main commitにfileが存在しない「新規」moduleは`I₀(M) = []`と定義する。
本PRDは`I₀`から最終list`I₁`へのdeltaを正本とする。`I₀(M)`は「当時のimport」等の文章へ
置き換えず、exact module名の列として保存する。

`keep`は`I₁(M) = I₀(M)`、`append [A, …]`は既存順を保った末尾追加、`remove [A, …]`はexact name削除、
`replace [A, …]`は`I₁(M)`全体の置換、`delete`はfileと`I₁(M)`が存在しないことを表す。
下表を`explicit_delta_domain`とし、consumer closureから追加されたものを含む
`M ∈ D \ explicit_delta_domain`には`keep`を適用する。次にないmoduleのdirect import変更、表にない追加、
並び順の変更、循環依存が必要になった場合は実装を止め、このcontractとmodule DAGを再承認する。

| module `M` | `I₁(M)` | 責務 |
| --- | --- | --- |
| `Formal.AG.LawAlgebra.Scheme` | `delete` | 旧ringed / chart / scheme / gluing routeを残さない |
| `Formal.AG.LawAlgebra.ObstructionIdeal` | `keep` | selected witness idealとlocal sum。`SheafImageConstruction`は削除 |
| `Formal.AG.LawAlgebra.LawfulLocus` | `keep` | affine zero-setとring-hom計算だけ。actual factorizationを名乗るsurfaceは削除 |
| `Formal.AG.LawAlgebra.Correspondence` | `keep` | low-level witness / kernel補題だけ。定理11.1の主ownerにはしない |
| `Formal.AG.LawAlgebra.StandardScheme` | `keep` | canonical Scheme providerのsignatureを保持 |
| `Formal.AG.LawAlgebra.ClosedEquationalGeometry` | `keep` | actual ideal sheaf、closed subscheme、semantic / ideal / factorization correspondenceの唯一のowner |
| `Formal.AG.LawAlgebra.FiniteExamples` | `keep` | 独立したfinite law-algebra exampleを保持 |
| `Formal.AG.RepresentationAnalysis.AATSch` | `replace [Formal.AG.ReadingFunctoriality.Core, Formal.AG.LawAlgebra.StandardScheme, Mathlib.CategoryTheory.Category.Basic]` | SD4〜SD5のcanonical decorated categoryとFunctor surface |
| `Formal.AG.RepresentationAnalysis.PreservationReflection` | `replace [Formal.AG.RepresentationAnalysis.AATSch, Mathlib.CategoryTheory.Category.Cat]` | `CategoryTheory.Cat`でbundleしたrepresentation familyと既存reflection statement |
| `Formal.AG.RepresentationAnalysis.GraphMatrix` | `keep` | `PreservationReflection`と二つのMathlib Matrix importをすべて維持し、Functor constructorを実装 |
| `Formal.AG.RepresentationAnalysis.SignatureCurvature` | `replace [Formal.AG.RepresentationAnalysis.PeriodSeparation, Formal.AG.LawAlgebra.ClosedEquationalGeometry, Formal.AG.Cohomology.FlatnessCriterion, Formal.AG.Derived.Intersection]` | SD3の4つの最小contextとfixed theorem |
| `Formal.AG.RepresentationAnalysis.RepairMarginDehn` | `replace [Formal.AG.RepresentationAnalysis.DistanceFlatnessMass, Formal.AG.SingularityMonodromyStack, Formal.AG.LawAlgebra.ClosedEquationalGeometry]` | SD3のactual repair-route factorizationと既存distance / margin / Dehn consumer |
| `Formal.AG.RepresentationAnalysis.Synthesis` | `replace [Formal.AG.RepresentationAnalysis.AnalyticContext, Formal.AG.LawAlgebra.ClosedEquationalGeometry]` | SD6のsingle synthesis packageとderived projections |
| `Formal.AG.Cohomology.GluingMismatch` | `keep` | Part IVのring-level lawfulness / mismatch statementを維持し、旧factorization accessorだけを削除 |
| `Formal.AG.Cohomology.LocalFlatnessGap` | `keep` | Part IVのglobal-section contradictionを維持し、旧factorization accessorだけを削除 |
| `Formal.AG.SingularityMonodromyStack.ArchitectureStack` | `replace [Formal.AG.SingularityMonodromyStack.RefactorGalois, Formal.AG.LawAlgebra.StandardScheme]` | canonical standard Scheme / atlasを使うstack consumer |
| `Formal.AG.SingularityMonodromyStack.Stratum` | `replace [Formal.AG.Derived, Formal.AG.LawAlgebra.StandardScheme, Formal.AG.Site.Topology]` | 旧Scheme module importをcanonical moduleへ置換 |
| `Formal.AG.Examples.LegacyConsolidation` | `replace [Formal.AG.Examples.StandardGeometryReferenceModels, Formal.AG.RepresentationAnalysis.GraphMatrix, Formal.AG.RepresentationAnalysis.Synthesis]` | SD9のnondegenerate migration firing |
| `Formal.AG.Examples.RepresentationAnalysisPart7` | `keep` | 独立したPart VII exampleをcanonical inputへ移行して保持 |
| `Formal.AG.StatementContractsLegacyConsolidation` | `replace [Formal.AG.LawAlgebra.ClosedEquationalGeometry, Formal.AG.Cohomology.LocalFlatnessGap, Formal.AG.RepresentationAnalysis.AATSch, Formal.AG.RepresentationAnalysis.SignatureCurvature, Formal.AG.RepresentationAnalysis.RepairMarginDehn, Formal.AG.RepresentationAnalysis.GraphMatrix, Formal.AG.RepresentationAnalysis.Synthesis, Formal.AG.Examples.LegacyConsolidation]` | exact-type contractだけを持つ |
| `Formal.AG.StatementContracts` | `append [Formal.AG.StatementContractsLegacyConsolidation]` | executable contract aggregate |
| `Formal.AG.AxiomAudit` | `append [Formal.AG.StatementContractsLegacyConsolidation, Formal.AG.Examples.LegacyConsolidation]` | new / changed theoremの全数audit |
| `Formal.AG.LawAlgebra` | `remove [Formal.AG.LawAlgebra.Scheme]` | canonical LawAlgebra aggregate。削除moduleのre-export禁止 |
| `Formal.AG.RepresentationAnalysis` | `keep` | migration後も同じmodule path集合を到達可能にする |
| `Formal.AG` | `append [Formal.AG.Examples.LegacyConsolidation]` | top-level aggregateからnondegenerate firingへ到達可能にする |
| `Formal.AG.RepresentationAnalysis.Bootstrap`、`Formal.AG.Measurement.Bootstrap`、`Formal.AG.Evolution.Bootstrap`、`Formal.AG.SemanticRepair.Bootstrap` | `keep` | canonical aggregate名を介した到達性を維持する |

AC49は全`M ∈ D`についてIssueにmaterializeした`I₀(M)`へ上表のordered deltaを適用する。
`delete`行はfile不存在とaggregate import zero、それ以外は`I₁(M)`と最終sourceのordered direct import
listを比較する。`Formal/AG`から`ResearchLean.AG`をimportしない。

## Statement Design

SD2〜SD6をcore declaration、SD3の列挙対象をfixed consumer declaration、SD9をfiring declarationの
唯一のfixed statement designとする。
target名、namespace、入力、
量化対象、結論、参照definitionのsignatureを実装中に変更しない。変更が必要になった場合は未達として
停止し、該当SD、必要な追加premise、旧signature、新signatureをtracking Issueへ報告する。

`Formal/AG/StatementContractsLegacyConsolidation.lean`は、`decl(N ∪ C ∪ E ∪ P)`を
`example : <fixed type> := <implementation>`で一対一に検査する。`#check`、名前の存在、wrapper、
alias、より弱い同値statementは達成に数えない。削除対象`L`はLean contractへ再定義せず、
SD10のpre-archive / post-archive no-hit検査で判定する。

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

対象main commitと本PRDのfixed statementから、次の集合をexact nameでmaterializeする。inventory itemは
public declaration、automatic projection、field / accessor、constructor、namespace、module pathのいずれかとし、
各itemにkind、owner file、source line、完全signatureまたはpath、抽出根拠を持たせる。

~~~text
inventory_at(snapshot, modules) = every public declaration, automatic projection,
  field / accessor, constructor, named instance, namespace, and module path
  owned by an existing module in modules at snapshot
M_base = every exact path ending in .lean in the 対象module metadata above
L_seed = exact expansion of the initial L table at the pinned main commit
K_seed = exact expansion of the required K anchors and SD3 P_IV
N_seed = every new or shape-changed public core item fixed by SD2–SD6,
  plus the new executable-contract module path fixed by SD10
E_seed = every public inventory item fixed by SD9, including constructors, fields,
  projections, named instances, namespaces, and the firing module path

consumer_step(X) = X ∪ direct public Lean consumers of names in X at the pinned main commit
consumer_closure = least fixed point of consumer_step starting from (L_seed ∪ N_seed)
C_seed = consumer_closure \ (L_seed ∪ N_seed ∪ E_seed)
ownerPaths(X) = exact .lean owner paths of every item in X
decl(X) = public declaration, automatic projection, field / accessor, constructor,
  and named instance items in X
M₀ = M_base ∪ ownerPaths(L_seed ∪ K_seed ∪ N_seed ∪ E_seed ∪ consumer_closure)

H = exact .lean module paths planned to change in the implementation PR graph
Ω₀ = inventory_at(pinned main commit, M₀)
Ω = Ω₀ ∪ N_seed ∪ E_seed
T = decl(Ω₀) whose owner path is in H

disposition_rows ⊆ Ω × {L, K, N, C, E}
L = {x ∈ Ω | (x, L) ∈ disposition_rows}
K = {x ∈ Ω | (x, K) ∈ disposition_rows}
N = {x ∈ Ω | (x, N) ∈ disposition_rows}
C = {x ∈ Ω | (x, C) ∈ disposition_rows}
E = {x ∈ Ω | (x, E) ∈ disposition_rows}
P = T ∩ K

L = L_seed
N = N_seed
C = C_seed
E = E_seed
K_seed ⊆ K
consumer_step(consumer_closure) = consumer_closure
H ⊆ M₀
unclassified_inventory_items =
  Ω \ {x | ∃ label, (x, label) ∈ disposition_rows} = ∅
multiply_classified_inventory_items =
  {x ∈ Ω | 1 < card {label | (x, label) ∈ disposition_rows}} = ∅
L, K, N, C, E are pairwise disjoint
Ω = L ∪ K ∪ N ∪ C ∪ E
changed_lean_module_paths(pinned main..final integrated snapshot) = H
final_public_inventory = inventory_at(final implementation snapshot, M₀)
final_public_inventory = Ω \ L
inventory_target_names = Ω
implementation_changed_public_names = decl(N ∪ C ∪ E)
statement_contract_target_names = decl(N ∪ C ∪ E ∪ P)
axiom_audit_names = theorem declarations in (N ∪ C ∪ E)
~~~

directoryや「consumer」という説明行を`M_base`のglobとして扱わない。consumer ownerは
`ownerPaths(consumer_closure)`を通じて`M₀`へ加え、そのmoduleの独立public surfaceも`Ω₀`へ全数収載する。
`M₀`とimport domain `D`は同じ式から生成し、closure由来moduleを別の暗黙集合へ置かない。
`L_seed` / `K_seed` / `N_seed` / `E_seed`は分類結果を
参照せず本PRDとpin済みsourceから先に展開し、qualified Lean reference graphのleast fixed pointを
安定するまで計算してから`M₀`、`Ω₀`、`Ω`をこの順で固定する。`K_seed ⊆ K`、`H ⊆ M₀`、
closure安定式のいずれかが失敗した場合は開始しない。

R0のsource inspectionで`L_seed` / `N_seed`にない削除対象またはshape変更coreが見つかった場合、
そのitemを`K`へ流さない。本PRD欠陥としてseed、consumer closure、`Ω`、module DAGを再計算し、
statement reviewを再承認する。`unclassified_inventory_items`と
`multiply_classified_inventory_items`は、default labelを持たない明示的`disposition_rows`から計算する。
seed外のitemも、完全signatureと最終処置を実読して`K` rowを明示するまで未分類のまま残す。
`P = T ∩ K`により、変更file内でsignatureを変えない全public declaration / projectionを
statement contractの対象に含める。pinned mainから全child PR merge後のintegrated snapshotまでの
`.lean` path集合が`H`と一致し、最終sourceから独立抽出した
`final_public_inventory`が`Ω \ L`とexact一致することを完了時に再計算する。unplanned public helper、
constructor、named instance、namespace、module pathはこの一致を失敗させるため、`K`へ暗黙追加せず、
seed、closure、module DAG、statement reviewを再承認する。

`L_seed`の固定specは次である。field declarationとnamespace内accessorもpin済みsourceから
exact nameへ展開し、説明上の「全field」を未展開のままIssueへ置かない。

| owner | `L_seed`へ展開する宣言 / field |
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
| `RepresentationAnalysis.SignatureCurvatureLawfulFactorizationContext` | 過剰なgeometry / valuation / signature premiseを一つに束ねる旧structureと全field / constructor / accessor、同namespace内の全旧theorem。SD3の4つの最小contextへ置換 |
| `RepresentationAnalysis.RepairRoute` | 旧`LawCoordinateAlgebra` / `lawCoordinateCommRing` / `obstructionIdeal` / `lawfulSection` / `factorsThroughLawfulLocus` field、`factorsThroughLawfulLocus_certificate` |
| `RepresentationAnalysis.Synthesis` | `AATSynthesisAssumptions`、`AATSynthesisConstructionInput`、両`toPackage`、旧`algebraicGeometricAATSynthesis`、`algebraicGeometricAATSynthesis_constructedPackage`、旧`AATSynthesisPackage`の`Atom` / `aatSite` / `ringedAATTopos` / chart family / set-level lawful locus / coherence equalityの重複field |
| `Examples.RepresentationAnalysisPart7` | `toyTargetCategory`、`idealTargetCategory`。Mathlib categoryを持つtargetかSD9のgraph targetへ置換 |
| repository-wide | `Legacy*` rename、旧名deprecated alias、exported compatibility adapter、削除module re-export、旧statement contract / audit entry |

次のanchorとSD3の`P_IV`をautomatic projectionまでexact nameへ展開した集合を`K_seed`とする。
`K_seed ⊆ K`を要求するが、このanchor一覧を完全な`K`の代用にしない。

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

`N`はSD2の4 bootstrap alias、SD3の`CurvatureReadingContext` / `CurvatureAxisComparisonContext` /
`CurvatureLawfulFactorizationContext` / `SignatureLawfulFactorizationContext`と各fixed theorem、
SD4のAATSch owner、SD5のFunctor / bundled family / target category
instance / normalized graph・matrix profile、SD6のsingle synthesis packageとderived projection、
SD10の新規executable-contract module pathを全public inventory kindへ展開した`N_seed`とする。
SD3冒頭のmerged actual factorizationとCohomology main statementは
`K`、三つのCohomology accessorと旧wide contextは`L`、`RepairRoute`と既存のtransitive consumerは
`C_seed`に入る。
`C = C_seed`は`L_seed ∪ N_seed`からqualified Lean reference graphのleast fixed pointとして
repository全体から自動抽出し、手入力の代表例一覧で代用しない。
`E = E_seed`はSD9のLean blockに現れる全public declaration、constructor、field、automatic projection、
named instance、namespace、firing module pathである。
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

~~~text
P_IV = public declarations / automatic projections at the pinned main commit in
       Formal.AG.Cohomology.GluingMismatch and Formal.AG.Cohomology.LocalFlatnessGap
       \ {
         Cohomology.LocalFlatnessData.factorsThroughFlat_U,
         Cohomology.RestrictedLocalLawfulSection.factorsThroughFlat_U,
         Cohomology.CompatibleGlobalLawfulSection.globalFactorsThroughFlat_U
       }
P_IV ⊆ P
~~~

tracking Issueは`P_IV`をexact nameと完全signatureへ展開する。次のanchorを含み、同じmoduleのhelper、
constructor、automatic projectionを省略しない。

| 処置 | exact declaration |
| --- | --- |
| 削除 | `Cohomology.LocalFlatnessData.factorsThroughFlat_U` |
| 削除 | `Cohomology.RestrictedLocalLawfulSection.factorsThroughFlat_U` |
| 削除 | `Cohomology.CompatibleGlobalLawfulSection.globalFactorsThroughFlat_U` |
| signature完全維持 | `Cohomology.LocalFlatnessData`、`Cohomology.RestrictedLocalLawfulSection`、`Cohomology.GluingMismatchData`、`Cohomology.PseudoTorsorNormalizedMismatch` |
| signature完全維持 | `Cohomology.HiddenCouplingData`、`Cohomology.CompatibleGlobalLawfulSection`、`Cohomology.GlobalSectionCoboundarySoundness`、`Cohomology.FiniteGlobalRestrictionCoboundarySurface` |
| signature完全維持 | `Cohomology.FiniteGlobalRestrictionPointwiseSoundness`、`Cohomology.GlobalLawfulRestrictionCoboundaryData`、`Cohomology.LocalFlatnessGapHypotheses` |
| statement完全維持 | `Cohomology.readMismatch_gluingMismatch`、`Cohomology.triple_mismatch_sum_zero`、`Cohomology.gluingMismatch_cocycle`、`Cohomology.hiddenCouplingClass_eq_zero` |
| statement完全維持 | `Cohomology.localFlatnessGap_no_globalLawfulSection`、`Cohomology.localFlatnessGap_no_globalLawfulSection_of_globalRestrictionCoboundaryData` |
| statement完全維持 | `Cohomology.localFlatnessGap_no_globalLawfulSection_of_finiteGlobalRestrictionCoboundarySurface`、`Cohomology.localFlatnessGap_no_globalLawfulSection_of_finiteGlobalRestrictionPointwiseSoundness` |

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

旧wide contextは、curvature reading、axis comparison、actual factorization、signature readingに分割する。
各contextはそのnamespaceのfixed theoremが実際に使うmaterial premiseだけを持つ。

~~~lean
structure RepresentationAnalysis.CurvatureReadingContext
    (LU : LawUniverse U)
    {Value : Type u}
    (valuation : ObstructionValuation U Value)
    (aggregation : ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex) where
  curvatureProfile :
    RepresentationAnalysis.CurvatureReadingProfile LU valuation aggregation

namespace RepresentationAnalysis.CurvatureReadingContext

theorem curvature_zero_iff_omegaU_zero
    {LU : LawUniverse U} {Value : Type u}
    {valuation : ObstructionValuation U Value}
    {aggregation : ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex}
    (C : CurvatureReadingContext LU valuation aggregation)
    (Obj : ArchitectureObject U) :
    C.curvatureProfile.CurvatureZero Obj ↔
      omegaU valuation LU aggregation Obj = valuation.domain.zero

theorem curvature_zero_iff_requiredObstructionValuesZero
    {LU : LawUniverse U} {Value : Type u}
    {valuation : ObstructionValuation U Value}
    {aggregation : ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex}
    (C : CurvatureReadingContext LU valuation aggregation)
    (Obj : ArchitectureObject U) :
    C.curvatureProfile.CurvatureZero Obj ↔
      ∀ i : LU.RequiredIndex,
        valuation.omega (LU.law i.1) Obj = valuation.domain.zero

end RepresentationAnalysis.CurvatureReadingContext

structure RepresentationAnalysis.CurvatureAxisComparisonContext
    (Obj : ArchitectureObject U) (LU : LawUniverse U) (Sig : SignatureAxes U)
    {Value : Type u}
    (valuation : ObstructionValuation U Value)
    (aggregation : ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex)
    extends RepresentationAnalysis.CurvatureReadingContext LU valuation aggregation where
  obstructionSoundness : ∀ i : LU.RequiredIndex,
    ObstructionSound valuation (LU.law i.1)
  obstructionCompleteness : ∀ i : LU.RequiredIndex,
    ObstructionComplete valuation (LU.law i.1)
  axisExactness : Lawfulness Obj LU ↔ RequiredSignatureAxesZero Obj Sig

namespace RepresentationAnalysis.CurvatureAxisComparisonContext

theorem curvature_zero_iff_requiredSignatureAxesZero
    {Obj : ArchitectureObject U} {LU : LawUniverse U} {Sig : SignatureAxes U}
    {Value : Type u} {valuation : ObstructionValuation U Value}
    {aggregation : ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex}
    (C : CurvatureAxisComparisonContext Obj LU Sig valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔ RequiredSignatureAxesZero Obj Sig

theorem curvature_zero_iff_requiredSignatureReadingZero
    {Obj : ArchitectureObject U} {LU : LawUniverse U} {Sig : SignatureAxes U}
    {Value : Type u} {valuation : ObstructionValuation U Value}
    {aggregation : ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex}
    (C : CurvatureAxisComparisonContext Obj LU Sig valuation aggregation)
    (signatureProfile : RepresentationAnalysis.SignatureReadingProfile Sig) :
    C.curvatureProfile.CurvatureZero Obj ↔
      signatureProfile.RequiredSignatureReadingZero Obj

end RepresentationAnalysis.CurvatureAxisComparisonContext

structure RepresentationAnalysis.CurvatureLawfulFactorizationContext
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (R : LawAlgebra.ClosedEquationalLawReading raw X)
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hclosed : LawAlgebra.RequiredClosed raw X R)
    (hexact : LawAlgebra.RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U)
    {Value : Type u}
    (valuation : ObstructionValuation U Value)
    (aggregation : ZeroReflectingAggregation Value valuation.domain
      S.lawUniverse.RequiredIndex)
    extends RepresentationAnalysis.CurvatureReadingContext
      S.lawUniverse valuation aggregation where
  pointComparison : LawAlgebra.RequiredObjectPointComparison raw X R s Obj
  obstructionSoundness : ∀ i : S.lawUniverse.RequiredIndex,
    ObstructionSound valuation (S.lawUniverse.law i.1)
  obstructionCompleteness : ∀ i : S.lawUniverse.RequiredIndex,
    ObstructionComplete valuation (S.lawUniverse.law i.1)

namespace RepresentationAnalysis.CurvatureLawfulFactorizationContext

variable {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {X : LawAlgebra.StandardArchitectureScheme raw}
variable {R : LawAlgebra.ClosedEquationalLawReading raw X}
variable {hR : LawAlgebra.IsClosedEquationalLawReading raw X R}
variable {hclosed : LawAlgebra.RequiredClosed raw X R}
variable {hexact : LawAlgebra.RequiredLawIdealExact raw X R hR hclosed}
variable {T : AlgebraicGeometry.Scheme} {s : T ⟶ X.underlying}
variable {Value : Type u}
variable {valuation : ObstructionValuation U Value}
variable {aggregation : ZeroReflectingAggregation Value valuation.domain
  S.lawUniverse.RequiredIndex}

theorem factorsThroughLawfulClosedSubscheme_of_curvature_zero
    (C : CurvatureLawfulFactorizationContext raw X R hR hclosed hexact
      s Obj valuation aggregation)
    (hcurvature : C.curvatureProfile.CurvatureZero Obj) :
    Nonempty (LawAlgebra.FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s)

theorem curvature_zero_of_factorsThroughLawfulClosedSubscheme
    (C : CurvatureLawfulFactorizationContext raw X R hR hclosed hexact
      s Obj valuation aggregation)
    (hfactor : Nonempty
      (LawAlgebra.FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s)) :
    C.curvatureProfile.CurvatureZero Obj

theorem curvature_zero_iff_factorsThroughLawfulClosedSubscheme
    (C : CurvatureLawfulFactorizationContext raw X R hR hclosed hexact
      s Obj valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔
      Nonempty (LawAlgebra.FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s)

end RepresentationAnalysis.CurvatureLawfulFactorizationContext

structure RepresentationAnalysis.SignatureLawfulFactorizationContext
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (R : LawAlgebra.ClosedEquationalLawReading raw X)
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hclosed : LawAlgebra.RequiredClosed raw X R)
    (hexact : LawAlgebra.RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) (Sig : SignatureAxes U) where
  signatureProfile : RepresentationAnalysis.SignatureReadingProfile Sig
  pointComparison : LawAlgebra.RequiredObjectPointComparison raw X R s Obj
  axisExactness : Lawfulness Obj S.lawUniverse ↔ RequiredSignatureAxesZero Obj Sig

namespace RepresentationAnalysis.SignatureLawfulFactorizationContext

variable {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {X : LawAlgebra.StandardArchitectureScheme raw}
variable {R : LawAlgebra.ClosedEquationalLawReading raw X}
variable {hR : LawAlgebra.IsClosedEquationalLawReading raw X R}
variable {hclosed : LawAlgebra.RequiredClosed raw X R}
variable {hexact : LawAlgebra.RequiredLawIdealExact raw X R hR hclosed}
variable {T : AlgebraicGeometry.Scheme} {s : T ⟶ X.underlying}
variable {Sig : SignatureAxes U}

theorem factorsThroughLawfulClosedSubscheme_of_requiredSignatureReadingZero
    (C : SignatureLawfulFactorizationContext raw X R hR hclosed hexact s Obj Sig)
    (hsig : C.signatureProfile.RequiredSignatureReadingZero Obj) :
    Nonempty (LawAlgebra.FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s)

end RepresentationAnalysis.SignatureLawfulFactorizationContext
~~~

`CurvatureReadingContext`の2 theoremは`CurvatureReadingProfile`の既存最小APIだけをproof-useする。
`CurvatureAxisComparisonContext`は`lawfulness_iff_omegaU_zero`と`axisExactness`をproof-useする。
`CurvatureLawfulFactorizationContext`の3 theoremは
`factorsThroughLawfulClosedSubscheme_iff_omegaU_zero`を直接proof-useし、
`SignatureLawfulFactorizationContext`のtheoremは
`factorsThroughLawfulClosedSubscheme_iff_requiredSignatureAxesZero`と
`requiredSignatureReadingZero_iff_requiredSignatureAxesZero`を直接proof-useする。
旧wide contextをwrapper、alias、`extends`先として残さない。manifestには旧完全signatureと
該当する`SD3:<exact-name>`参照だけを置く。

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
executable contract、AxiomAudit、tracking IssueのAC evidence mapでsingle packageと上記projectionを
宣言単位に記録する。新しいMarkdown status文書は作らない。

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
| old `SignatureCurvatureLawfulFactorizationContext` | SD3の4 contextへtheorem単位で分割。旧context / namespaceは`delete-repackage` |
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
`material_premise_ledger_delta`はtracking Issueのpremise inventoryから計算する未分類または未承認の差分、
`new_material_premise`は本文根拠も放電宣言もない追加premiseを表す。これはMarkdown台帳名ではない。
approved replacement自体を隠れたzero差分として扱わない。

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
| `CurvatureReadingContext` | profile data | `CurvatureReadingProfile` | profileの既存2 theoremだけを使い、Scheme / closed geometry / signature premiseを受け取らない |
| `CurvatureAxisComparisonContext` | Part I comparison data | soundness、completeness、axis exactnessのnamed proof | `lawfulness_iff_omegaU_zero`とaxis equivalenceへ渡し、Scheme premiseを受け取らない |
| `CurvatureLawfulFactorizationContext` | actual factorization comparison data | `hR`、`hclosed`、`hexact`、point comparison、soundness、completeness | curvatureとactual factorizationを結ぶ3 theoremですべてproof-useする |
| `SignatureLawfulFactorizationContext` | signature / actual factorization comparison data | `hR`、`hclosed`、`hexact`、point comparison、axis exactness | signature readingからactual factorizationを得るtheoremですべてproof-useする |
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
| deletion | `L`全name / field / module path no-hit | — | SD10のpre-archive / post-archive二段階scopeで検査する |

### SD10 — executable contract、audit、no-hit contract

`StatementContractsLegacyConsolidation.lean`は次を満たす。

- `decl(N ∪ C ∪ E ∪ P)`をexact-type `example`で一対一に検査する。
- automatic projectionを含むstructure fieldは、target name集合へ展開して型を検査する。
- `AnalyticRepresentation`がdefinitionally Mathlib `Functor`であることを両方向の型代入で検査する。
- consumer signature manifestの`preserve`行すべてを直接参照する。
- 削除済み宣言をcontract内で再定義しない。

`L`の各inventory rowはkindに加えて、Lean fully-qualified name、short identifier、module name、
file pathのうち該当する`search_key`を持つ。bareな数学語とLean declaration referenceを同じhitに
数えず、次の型付きscopeと判定規則を使う。

~~~text
live_contract_path = docs/aat/aat_lean_06_legacy_consolidation_prd.md
tracked_snapshot_files = paths returned by git ls-tree -r --name-only <reviewed-commit>
lean_source_scope = tracked_snapshot_files ∩ (Formal/**/*.lean ∪ {Formal.lean, Main.lean})
lean_syntax_scope = syntax nodes parsed from lean_source_scope
lean_prose_scope = comment and docstring nodes parsed from lean_source_scope
live_nonmath_reference_scope = tracked_snapshot_files
  - lean_source_scope
  - docs/archive/**
  - docs/aat/algebraic_geometric_theory/**
  - **/*_prd.md
  - .git/**

pre_archive_no_hit_scope = lean_syntax_scope ∪ lean_prose_scope ∪ live_nonmath_reference_scope
post_archive_no_hit_scope = the same typed scope after the content-invariant move

pre_archive_prd_reference_scope = tracked_snapshot_files
  - docs/archive/** - .git/** - live_contract_path
post_archive_prd_reference_scope = tracked_snapshot_files after the archive move
  - docs/archive/** - .git/**
~~~

declaration、field、accessor、constructor、namespaceは`lean_syntax_scope`の各identifier occurrenceを
parser-resolved fully-qualified nameへ戻して
`search_key`と比較する。module pathはfile不存在、exact `import` module name、aggregate re-exportを
別々に検査する。`Legacy*`はLean syntax identifierだけをpattern scanする。
`lean_prose_scope`ではfully-qualified name、module name、file path、short identifierをcandidateにし、
Lean declaration / field / source referenceを指すか実読する。public docstringは独立kindとして全candidateと
採否をpacketへ残し、通常commentと一括して省略しない。
`live_nonmath_reference_scope`ではfully-qualified Lean name、exact module name、exact file pathだけを
自動reference hitとする。各legacy short identifierはMarkdown装飾の有無に依存せずtoken単位で
全出現をcandidate抽出し、Lean declaration、Lean status、source referenceを指す場合だけhit、
数学用語として使う場合は非hitとする。backtick付きだけを抽出する実装、substring一致だけで
候補を減らす実装を認めない。
protected math sourceと他PRDはlegacy declaration scanの対象ではない。

各検査はcandidate hitのpath、line、syntax / prose kind、resolved name、採否を保存し、zero件の場合も検索keyと
scope file一覧をpacketへ添付する。AC6、AC10、AC13、AC16、AC17、AC23、AC24、AC27、AC31、
AC40〜AC43は`pre_archive_no_hit_scope`で判定する。AC43の削除Issue状態はtracking Issueでも
別に確認する。AC53の対象PRD reference zeroは
`pre_archive_prd_reference_scope`で、`docs/guideline.md`が指定する現在path、archive予定path、filename、
titleを検索し、自己fileを数えない。

AC1〜AC54、review、CI、merge、現行source同期を確認した後にcontent-invariant archive moveを行い、
legacy searchを`post_archive_no_hit_scope`、PRD reference searchを
`post_archive_prd_reference_scope`で再実行する。git historyとGitHub Issue / PR / reviewは
repository scan対象ではない。

~~~text
removed_declaration_syntax_hits = ∅
removed_field_or_accessor_syntax_hits = ∅
removed_module_file_or_import_hits = ∅
legacy_namespace_syntax_hits = ∅
removed_lean_docstring_reference_hits = ∅
removed_live_nonmath_reference_hits = ∅
deprecated_alias_hits = ∅
exported_adapter_hits = ∅
old_contract_hits = ∅
old_audit_hits = ∅
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
| 第IV部 定義5.1〜5.3、6.1〜6.2、定理7.1 | SD3の`P_IV` exact declaration set | 三つの旧factorization accessorだけを削除し、mismatch、cocycle、coboundary、4本のnonexistence theoremを完全signatureで保持 |
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
11. removed name、module、adapter、contract、auditのpre-archive scope hitがzeroである。
12. live docsとwebsiteのaccepted legacy referenceがcanonical ownerと現行pathへ同期される。

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

- 対象main commitを固定し、`M_base`、4 seed、consumer closure、`M₀`、`H`、`Ω₀`、`Ω`、
  `disposition_rows`、`T`、`L`、`K`、`N`、`C`、`E`、`P`をexact nameで生成する。
- declaration、field、constructor、namespace、module import、docstring、example、contract、auditを抽出する。
- 各`L` itemへkind別`search_key`を付け、Lean syntax scopeとnonmath exact-reference scopeを固定する。
- closure安定、`H ⊆ M₀`、`K_seed ⊆ K`、`Ω = L ∪ K ∪ N ∪ C ∪ E`、未分類zero、
  重複分類zero、`P = T ∩ K`を独立計算で確認する。
- 最終diffから`changed_lean_module_paths`と`final_public_inventory`を再抽出し、
  `changed_lean_module_paths = H`、`final_public_inventory = Ω \ L`を確認する。
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
- executable contract、AxiomAudit、tracking IssueのAC evidence mapをpackage、projection、reference firingの
  現行宣言へ同期する。

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
- `RepresentationAnalysisPart7`はmodule pathと独立したexample theoremを保持し、旧target categoryと
  synthesis inputだけをcanonical inputへ再構成する。file削除は本PRDの処置に含めない。

### R9 — contracts、audit、aggregate、tracking state

- `StatementContractsLegacyConsolidation.lean`を作成し、`decl(N ∪ C ∪ E ∪ P)`を全数登録する。
- `StatementContracts.lean`、`AxiomAudit.lean`、aggregate importをcanonical moduleへ同期する。
- tracking Issueのinventory、consumer manifest、AC evidence mapを現行宣言と検査結果へ同期する。
- `live_nonmath_reference_scope`のaccepted legacy hitをcanonical owner、現行module path、現行statusへ同期する。
  `website/**`のhitは専用child Issue / PRで更新し、`website-review`を通す。文章の数学claim、layout、
  navigation、機能は変更せず、各candidateの旧reference、置換先、採否、review URLをpacketへ残す。
- `Formal/AG`からResearch moduleをimportしない。
- theorem index、proof-obligation一覧、migration status用の新しいMarkdown文書を作らない。

### R10 — final deletionとlifecycle

- `L`、旧module path、deprecated attribute、adapter namespace、old constructor、duplicate equality fieldを
  `pre_archive_no_hit_scope`でscanする。
- temporary adapter、adapter専用module、削除Issueをzeroにする。
- contract targetが`decl(N ∪ C ∪ E ∪ P)`、audit targetが`N ∪ C ∪ E`中のtheorem、
  material premise対象が`N ∪ C ∪ E`と一致することを検査する。
- review、CI、merge、現行source同期後に`pre_archive_prd_reference_scope`の対象PRD参照をzeroにし、
  `docs/guideline.md`に従ってarchiveする。

## Acceptance Criteria

- [ ] AC1: tracking Issueが対象main commit、`M_base`、4 seed、consumer closure、`M₀`、`H`、
  `Ω₀`、`Ω`、defaultなしの`disposition_rows`、`T`、`L`、`K`、`N`、`C`、`E`、`P`、
  `D = M₀`、全`I₀(M)`、module DAG、batch、依存順をexact nameで固定し、closure安定、
  `H ⊆ M₀`、`K_seed ⊆ K`、`Ω = L ∪ K ∪ N ∪ C ∪ E`、未分類zero、重複分類zero、
  `P = T ∩ K`、`changed_lean_module_paths = H`、`final_public_inventory = Ω \ L`を独立計算で確認している。
- [ ] AC2: `consumer signature manifest`が`C`の全public declarationを覆い、旧完全signature、新完全signatureまたはSD3参照、処置、proof ownerを持つ。
- [ ] AC3: SD2〜SD6のcore statement、SD3の列挙consumer、SD9のfiring statement、consumer manifestが同じsignatureを重複して正本化していない。
- [ ] AC4: executable contractのtarget name集合が`decl(N ∪ C ∪ E ∪ P)`と一致し、全targetをexact-type `example`で検査する。
- [ ] AC5: AxiomAuditのtarget name集合が`N ∪ C ∪ E`中の全new / changed theoremと一致する。
- [ ] AC6: `LawAlgebra/Scheme.lean`、旧`RingedAATTopos`、旧`ChartCompatibility`、旧`ArchitectureScheme`、`singleAffineSpec`、`SchemeGluingData`、`AffineReturnConditions`と全参照のpre-archive scope hitがzeroである。
- [ ] AC7: actual architecture schemeの公開名が`StandardArchitectureScheme`に一意化されている。
- [ ] AC8: Parts VII〜Xの`UsesArchitectureScheme`がraw-indexed canonical型を返す。
- [ ] AC9: 全scheme consumerがactual Mathlib `Scheme`、actual atlas、actual overlap presentationを使用する。
- [ ] AC10: `SheafImageConstruction`と全参照のpre-archive scope hitがzeroである。
- [ ] AC11: actual obstruction geometryが`lawGeneratedIdealSheaf : Scheme.IdealSheafData`を使用する。
- [ ] AC12: set-level lawful locusはaffine calculationに限定され、actual closed geometry completionに使われない。
- [ ] AC13: `FactorsThroughLawfulLocus`と全accessor / consumerのpre-archive scope hitがzeroである。
- [ ] AC14: factorization consumerがactual morphism、triangle equality、一意性を持つcanonical APIを使用する。
- [ ] AC15: SD3の三Cohomology accessorのpre-archive scope hitがzeroであり、`P_IV`が同二moduleの他の全public declaration / projectionを覆い、Part IVのmismatch、cocycle、coboundary bridgeと4本のno-global-section theoremが完全signatureを維持する。
- [ ] AC16: `LawfulnessIdealCorrespondenceAssumptions` / packageと同型のconclusion-shaped structureのpre-archive scope hitがzeroである。
- [ ] AC17: repair routeがactual factorizationを使い、旧wide curvature contextのpre-archive scope hitがzeroである。SD3の4 contextは各fixed theoremが使うpremiseだけを持ち、profile / valuation / signature / actual factorizationのcanonical theoremを直接proof-useする。
- [ ] AC18: `AATSchReadingParameter`に`SchemeMorphism`、custom identity、custom composition、category-law fieldがない。
- [ ] AC19: `AATSch.scheme`が`StandardArchitectureScheme raw`である。
- [ ] AC20: `AATSchMorphism.toSchemeHom`が`StandardArchitectureScheme.Hom`、`toSchemeMap`がその`.base`である。
- [ ] AC21: `AATSch` categoryのidentity / compositionがcanonical `StandardArchitectureScheme` categoryへ写る。
- [ ] AC22: `AATSch.forget`がfaithfulで、object / map projectionがcontractで固定される。
- [ ] AC23: `AATSchIdentityData`、`AATSchCompositionData`、`AATSchFiberProductData`と全参照のpre-archive scope hitがzeroである。
- [ ] AC24: `AnalyticTargetCategory`、`AsCategory`、`finiteDirectedGraphTargetCategory`、`matrixRepresentationTargetCategory`、custom target category fieldと全参照のpre-archive scope hitがzeroである。
- [ ] AC25: `AnalyticRepresentation`がdefinitionally Mathlib `Functor`であり、`RepresentationFamily.Target`が`CategoryTheory.Cat`を返す。
- [ ] AC26: analytic consumerが`Functor.map_id` / `map_comp`を直接使い、graph / matrix profileにobject map、morphism map、Functor lawの重複fieldがない。
- [ ] AC27: `AATSynthesisAssumptions`、`AATSynthesisConstructionInput`、両`toPackage`と全参照のpre-archive scope hitがzeroである。
- [ ] AC28: normalized `AATSynthesisPackage`がSD6のfieldだけを持つ。
- [ ] AC29: site、ringed site、atlas、ideal sheaf、lawful closed geometryがSD6のcanonical owner projectionから得られる。
- [ ] AC30: synthesis packageにAtom、AtomFamily、ArchitectureObject、AATSite、ringed site、chart family、ideal sheaf、locus、immersionの重複fieldとcoherence equalityがない。
- [ ] AC31: 旧`algebraicGeometricAATSynthesis` conjunction theoremとconstructed-package existentialのpre-archive scope hitがzeroである。
- [ ] AC32: manifestの全`preserve`行でcanonical型置換以外のstatement diffがzeroである。
- [ ] AC33: manifestの全`derive`行でcanonical ownerのproof-useが確認される。
- [ ] AC34: manifestに未処理`stop-independent-content`行がない。
- [ ] AC35: SD9の`leftChartMorphism.toSchemeMap`がreference modelのleft chart mapに一致し、`¬ IsIso`が証明されている。
- [ ] AC36: SD9に少なくとも一つの非恒真compatibility predicate、成立例、不成立例がある。
- [ ] AC37: graph representationがactual Mathlib Functorでidentity / compositionを発火する。
- [ ] AC38: `standardPartIPrerequisites`、`standardGeometry`、normalized synthesis packageが同じPart I core / reference site provenanceを持ち、standard reference Scheme、weak ideal sheaf、zero point actual factorizationを発火する。
- [ ] AC39: main firingがPUnit、zero ideal、empty Scheme、identity mapだけに依存しない。
- [ ] AC40: `L`のdeclaration、field、module path、namespace、constructorのpre-archive scope hitがzeroである。
- [ ] AC41: deprecated alias、`Legacy*` rename、exported adapter、旧module re-exportのpre-archive scope hitがzeroである。
- [ ] AC42: old statement contractとold audit entryのpre-archive scope hitがzeroである。
- [ ] AC43: temporary adapterとadapter専用moduleのpre-archive scope hitがzeroであり、
  tracking Issueに未解決のadapter削除Issueがない。
- [ ] AC44: 全new / changed declarationにdocstringがあり、自明でないdefinitionに`Implementation notes`がある。
- [ ] AC45: 下流proofがnew / changed core definitionのunfoldに依存しない。
- [ ] AC46: `material_premise_ledger_delta = ∅`かつ`new_material_premise = ∅`である。
- [ ] AC47: new / changed theoremがstandard axiomsのみを使用する。
- [ ] AC48: `docs/aat/algebraic_geometric_theory/**`、G-07、Research sourceに差分がない。
- [ ] AC49: 全`M ∈ D`について、`delete`行はfile / aggregate importがzero、それ以外は最終ordered direct import listが`I₀(M)`へdeltaを適用した`I₁(M)`とexact一致し、Research reverse importがない。
- [ ] AC50: 統括エージェントがPR前に`lake build`を一度だけ実行し、PR後のfull buildはCIでgreenである。
- [ ] AC51: `math-lean-review`の4本がすべて合格、またはfinding全解消後に
  `.codex/skills/_shared/review-protocol.md`に従う有資格な直接対応が記録される。
- [ ] AC52: 全child PRがmergeされ、tracking Issueと依存Issueのstatusが同期される。
- [ ] AC53: `docs/guideline.md`のarchive前条件として、AC1〜AC52、review、CI、merge、
  現行sourceへの成果反映、`pre_archive_prd_reference_scope`での対象PRD reference zero、
  `pre_archive_no_hit_scope`の全no-hit式が満たされる。
- [ ] AC54: `live_nonmath_reference_scope`の全short identifierを装飾の有無に依存せずtoken単位で
  candidate抽出し、accepted hitがcanonical owner / path / statusへ同期されている。`website/**`の
  accepted hitは専用child PRで同期され、`website-review`が合格し、数学claim、layout、navigation、
  機能のdiffがzeroである。

AC1〜AC54を満たした後、contentを変更せずPRDをarchiveする。移動後にcontent-invariant move、
`post_archive_prd_reference_scope`の参照zero、`post_archive_no_hit_scope`の全no-hit式、archive文書が
現行sourceとして参照されていないことを確認し、tracking Issueへpost-archive resultを追記する。

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
- contract / audit / tracking Issueだけを新名へ変更し、proof consumerを旧routeに残す。
- unplanned public helper、constructor、named instance、namespace、moduleを`Ω`外へ追加する。
- legacy short identifierをbacktick付き出現だけで検査し、裸tokenを候補から落とす。
- websiteのaccepted legacy referenceを残したまま、websiteを対象外としてno-hitを宣言する。
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
- SD3のcurvature / axis / factorization contextを各canonical theoremへ接続できず、
  fixed theoremごとに未使用premiseが残る。
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
- ArchSig、ArchMap、toolingの変更。
- websiteの新機能、layout、navigation、数学claimの変更。R9のaccepted legacy reference同期だけを扱う。
- 数学本文へのLean status、Issue、PR、declaration名の追加。
- `docs/aat/algebraic_geometric_theory/**`の編集。

## 検証

検証主体、PR前のfull build回数、PR後のCIは`AGENTS.md`を適用する。repository共通の静的検査は
`git diff --check`、`.github/lean_quality/check_changed_public_artifacts.sh`、
`.github/lean_quality/check_research_import_direction.sh`、`.github/lean_quality/check_lint_formal.sh`を
exact pathで使用し、本PRDへscript本文を複製しない。

実装中のfocused checkは変更batchごとの単一非aggregate fileに限定する。少なくとも次をbatch ownerが実行する。

~~~bash
lake env lean Formal/AG/Cohomology/LocalFlatnessGap.lean
lake env lean Formal/AG/RepresentationAnalysis/SignatureCurvature.lean
lake env lean Formal/AG/RepresentationAnalysis/AATSch.lean
lake env lean Formal/AG/RepresentationAnalysis/Synthesis.lean
lake env lean Formal/AG/Examples/LegacyConsolidation.lean
lake env lean Formal/AG/StatementContractsLegacyConsolidation.lean
~~~

task固有の追加検査は次である。

- least-fixed-point closure安定、`H ⊆ M₀`、`K_seed ⊆ K`、`Ω = L ∪ K ∪ N ∪ C ∪ E`、
  未分類zero、重複分類zero、`P = T ∩ K`
- 最終diffの`changed_lean_module_paths = H`、最終sourceの`final_public_inventory = Ω \ L`
- `D = M₀`、全`M ∈ D`の`I₀`、delta、`I₁`、最終ordered direct import listのexact一致
- implementation public names、contract target names、audit theorem namesの一致
- consumer manifestの全行処置済み、statement diff zero、未処理分類zero
- `P_IV`の完全展開と三accessor以外のsignature diff zero
- inventory kindごとの`search_key`、Lean syntax / comment / public docstring / nonmath scope、
  parser-resolved candidate一覧とpre-archive no-hit
- live nonmathの装飾なしshort identifierを含むtoken candidate一覧、accepted hitの同期先、
  website child PRと`website-review`結果
- `pre_archive_prd_reference_scope`での現在path / archive予定path / filename / title zero
- `AATSchMorphism.toSchemeHom` / `toSchemeMap`、forgetful faithfulness
- concrete compatibilityのpositive / negative firing
- analytic Functorの`map_id` / `map_comp`
- synthesis packageのfield一覧とcanonical projection一覧
- standard reference Scheme / ideal / factorizationからのsame-provenance firing
- AC44のdocstring / `Implementation notes`全数表
- AC45のchanged coreからtransitive downstream proofへのunfold依存検査
- `material_premise_ledger_delta = ∅`、`new_material_premise = ∅`
- protected math source差分zero

## Completion evidence packet

tracking Issueの専用completion commentをpacketの一意な保存先とする。最終PR commentは対象commit SHA、
packetへのlink、短い判定だけを持ち、packet本文を複製しない。

1. **Snapshot**
   - commit SHA
   - 対象module一覧
   - child Issue / PR / merge対応
   - `M_base`、4 seed、consumer closure、`M₀`、`H`のexact集合と、closure安定結果
   - `Ω₀`、`Ω`、defaultなしの`disposition_rows`、`T`、`L`、`K`、`N`、`C`、`E`、`P`のexact name集合
   - `changed_lean_module_paths = H`と`final_public_inventory = Ω \ L`の再計算結果
   - `D = M₀`と、全`M ∈ D`のordered `I₀`、delta、最終`I₁`
2. **AC evidence map**
   - AC1〜AC54の各行について、対象declaration / source path、検査commandまたはreview、結果、一次証拠link
   - AC44の全new / changed declaration、docstring line、`Implementation notes` line
   - AC45の全changed core、transitive downstream consumer、unfold依存scan、proof inspection result
   - 一つのgreen jobを複数ACの根拠にする場合は、各ACを直接検査する出力位置
3. **Inventory and disposition**
   - 旧declaration / field / module / consumerの全数表
   - 各itemの明示的disposition row、完全signature / path、処置根拠、最終owner
   - consumer closure安定、`H ⊆ M₀`、`K_seed ⊆ K`
   - `Ω = L ∪ K ∪ N ∪ C ∪ E`、未分類zero、重複分類zero、`P = T ∩ K`
   - final public inventoryの全kind一覧と`Ω \ L`とのexact diff zero
   - inventory追加履歴と再承認
4. **Statement preservation**
   - consumer signature manifest
   - `P`全宣言の対象main commit signatureとのexact一致
   - `P_IV`のexact name展開と三accessor以外のsignature diff zero
   - 全`preserve`行の旧 / 新signatureまたはSD3参照とstatement diff zero
   - 全`derive`行のcanonical proof-use
   - `delete-repackage`の独立内容なし判定
   - 未処理`stop-independent-content = ∅`
5. **Canonical geometry**
   - `raw.toRingedSite`
   - `StandardArchitectureScheme` actual Scheme / atlas / overlap
   - `lawGeneratedIdealSheaf`
   - lawful closed subscheme / immersion
   - actual factorization lift / triangle / uniqueness
6. **AATSch and analytic representation**
   - `toSchemeHom` / `toSchemeMap`
   - category / forgetful functor / faithfulness
   - compatibility positive / negative example
   - proper chart inclusionと`¬ IsIso`
   - Mathlib Functor `map_id` / `map_comp`
7. **Synthesis normalization**
   - final field list
   - derived projection list
   - duplicate field / equality field no-hit
   - standard reference model firing
8. **Premise discharge**
   - `N ∪ C ∪ E`の全premise三分類
   - 旧premiseからcanonical premiseへのapproved replacement map
   - 放電宣言とproof-use
   - `material_premise_ledger_delta = ∅`
   - `new_material_premise = ∅`
9. **Deletion evidence**
   - `pre_archive_no_hit_scope`、scope file一覧、全`search_key`、candidate hitとsyntax / prose adjudication
   - public Lean docstringのshort identifier candidateとzero結果
   - live nonmathの全short identifier token candidate、装飾kind、採否、canonical同期先
   - website candidateのchild Issue / PR、`website-review` URL、非reference diff zero
   - removed declaration / field / accessor / module file / exact importのzero結果
   - deprecated alias / `Legacy*` / adapter / re-exportのzero結果
   - old contract / auditのzero結果
10. **Kernel evidence**
   - focused Lean checks
   - 統括エージェントによる一回の`lake build`
   - executable contract
   - AxiomAudit
   - static scans
   - final `I₁` import comparison
   - AC44 / AC45の専用検査結果
   - CI URLと結果
11. **Independent review**
    - `math-lean-review` 4査読の判定
    - website reference同期child PRの`website-review`判定
    - findingがあった場合の修正後確認または正式再査読
12. **Lifecycle**
    - merge済み宣言 / aggregate確認
    - `pre_archive_prd_reference_scope`と現在path / archive予定path / filename / titleのzero結果
    - archive予定path

archive後はcontent-invariant move、`post_archive_prd_reference_scope`のreference zero、
`post_archive_no_hit_scope`の全検索結果をpost-archive checkとしてtracking Issueへ追記する。

次の組合せだけではcompletion evidenceにならない。

- build green + removed nameの一部no-hit
- `#print axioms` + docs更新
- integrated firing theorem一件
- alias + inherited instance
- positive exampleだけ
- tracking Issueの自己申告だけ
