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
- statement contract正本: 本PRDの`Statement Design`
- executable contract: `Formal/AG/StatementContractsStandardGeometryReferenceModels.lean`
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

次をすべて満たすまで実装を開始しない。

1. tracking Issueに対象main commit、SD0〜SD7の`T` / `F` / `C` inventory、SD8のmaterial premise表、
   family展開後のSD9 firing matrix、module DAG、子Issue依存、各子Issueのfocused checkを登録している。
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
   - `HasSheafify`を`AATCommAlgCat Int`と
     `AATCommAlgCat (Polynomial Int)`について放電するnamed instance chain
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
   ideal sheafの型が未確定のまま子Issueを開始しない。
6. 実装前statement reviewで、SD0〜SD7の全signature、SD8のmaterial premise表、
   family展開後のSD9 positive / negative firingと`T` / `F` / `C`の集合契約が`Approved`になっている。

いずれかが欠ける間、このPRDは実行しない。

## Module import contract

新規moduleとdirect importを次で固定する。循環依存または未記載の横断importが必要になった場合は
実装を止め、tracking Issueでmodule DAGを再承認する。

| module | direct imports | 責務 |
| --- | --- | --- |
| `Formal.AG.Examples.StandardGeometryReferenceModels` | `Formal.AG.Examples.FiniteModel`、`Formal.AG.LawAlgebra.ClosedEquationalGeometry`、`Formal.AG.ReadingFunctoriality.Coefficient`、`Mathlib.Algebra.MvPolynomial.Eval`、`Mathlib.Algebra.Polynomial.AlgebraMap`、`Mathlib.RingTheory.Localization.Away.Basic`、`Mathlib.RingTheory.ZMod`、`Mathlib.AlgebraicGeometry.Cover.Open`、`Mathlib.AlgebraicGeometry.Restrict`、`Mathlib.AlgebraicGeometry.OpenImmersion`、`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` | SD0〜SD7の固定fixture、positive / negative firing |
| `Formal.AG.StatementContractsStandardGeometryReferenceModels` | `Formal.AG.Examples.StandardGeometryReferenceModels` | `example : exact-type := exact-declaration`だけ |
| `Formal.AG.StatementContracts` | `Formal.AG.StatementContractsStandardGeometryReferenceModels` | executable contract aggregate |
| `Formal.AG` | `Formal.AG.ReadingFunctoriality`の後に`Formal.AG.Examples.StandardGeometryReferenceModels` | repository AAT aggregate。`Formal.AG.LawAlgebra`から本fixtureをimportしない |
| `Formal.AG.AxiomAudit` | `Formal.AG.Examples.StandardGeometryReferenceModels`、`Formal.AG.StatementContractsStandardGeometryReferenceModels` | 全new theoremのaudit aliasと最終標準公理検査 |

`Formal/AG`から`research/lean/ResearchLean`をimportしない。

## Statement Design

この節を本PRDの唯一のstatement contract正本とする。別のMarkdown contractは作成しない。
実装開始後にtarget名、namespace、入力、量化対象、結論、参照definitionのsignatureを変更しない。
変更が必要になった場合は未達として停止し、該当SDと差分をtracking Issueへ報告する。

`Formal/AG/StatementContractsStandardGeometryReferenceModels.lean`は、下記の全public targetを
`example : <fixed type> := <implementation>`で一対一に検査する。`#check`、名前の存在、
同値な弱いstatement、aliasだけの宣言は契約達成に数えない。

exact-type検査だけでは新規defのbody変更を検出できない。したがって、ACが具体値または
constructor provenanceを要求するdefには、下記のnamed `*_eq` theoremを置き、同theoremも
executable contractへ一対一に登録する。単にdefをunfoldできること、またはcontract側で
`rfl`を直接証明することはbody固定の証拠に数えない。behaviorを要求するdefは、対応する
map、ideal、firing、validity theoremの固定statementでcharacterizeする。

以下のLean blockはすべて次のnamespaceで読む。

~~~lean
namespace AAT.AG.Examples.StandardGeometryReferenceModels

open CategoryTheory CategoryTheory.Limits Opposite
open AAT.AG.LawAlgebra
open AlgebraicGeometry
open scoped AlgebraicGeometry Classical

noncomputable section
~~~

### 固定対象

reference modelは次の一件に固定する。

~~~text
A = ℤ[x]
X = Spec A
U_left  = D(x)
U_right = D(1-x)
U_left ∩ U_right = D(x(1-x))

I_weak   = (x(x-1))
I_strong = (x)
I_rigid  = (x, 2)   [non-identity inclusion composition audit only]

p0 : x ↦ 0
p1 : x ↦ 1
p2 : x ↦ 2

coefficient change : ℤ → ℤ[t]
~~~

`StandardGeometryReferenceInput`のようなgeneric certificate structureは導入しない。
Scheme、chart、overlap、ideal、closed subscheme、factorization、strictness、nonempty、
lawfulnessをfieldとして受け取らない。上記の環、生成元、評価、既存のfinite Atom/context dataだけを
definitionとして置き、すべての性質をtheoremで証明する。

この固定値を変更する場合は、Acceptance Criteriaを保った代替への実装中の差し替えを認めない。
本PRDのstatement改訂と再承認が必要であり、それまでは停止する。

### SD0 — polynomial、site、raw restriction、localization presentation

~~~lean
abbrev AmbientRing := MvPolynomial Unit Int

theorem ambientRing_eq :
    AmbientRing = MvPolynomial Unit Int :=
  rfl

def coordinate : AmbientRing :=
  MvPolynomial.X ()

@[simp] theorem coordinate_eq :
    coordinate = MvPolynomial.X () :=
  rfl

def leftGenerator : AmbientRing :=
  coordinate

@[simp] theorem leftGenerator_eq :
    leftGenerator = coordinate :=
  rfl

def rightGenerator : AmbientRing :=
  1 - coordinate

@[simp] theorem rightGenerator_eq :
    rightGenerator = 1 - coordinate :=
  rfl

def overlapGenerator : AmbientRing :=
  leftGenerator * rightGenerator

@[simp] theorem overlapGenerator_eq :
    overlapGenerator = leftGenerator * rightGenerator :=
  rfl

def coverGenerator : Bool → AmbientRing
  | false => leftGenerator
  | true => rightGenerator

@[simp] theorem coverGenerator_false :
    coverGenerator false = leftGenerator :=
  rfl

@[simp] theorem coverGenerator_true :
    coverGenerator true = rightGenerator :=
  rfl

theorem coverGenerator_span_eq_top :
    Ideal.span (Set.range coverGenerator) = ⊤

noncomputable def referenceContextPreorder :
    Site.ContextPreorderCategory
      AAT.AG.FiniteModel.corePackage.object

theorem referenceContextPreorder_le_iff
    (W V : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object) :
    referenceContextPreorder.le W V ↔
      W = V ∨
        ∃ i j : AAT.AG.FiniteModel.TwoPatchContextIndex,
          W = AAT.AG.FiniteModel.twoPatchContext i ∧
          V = AAT.AG.FiniteModel.twoPatchContext j ∧
          AAT.AG.FiniteModel.twoPatchContextIndexLe i j

def referenceCoverageRequirements :
    Site.CoverageRequirements
      AAT.AG.FiniteModel.corePackage.object
      AAT.AG.FiniteModel.corePackage.algebra.lawReading.lawUniverse
      AAT.AG.FiniteModel.corePackage.algebra.signatureReading :=
  AAT.AG.FiniteModel.twoPatchCoverageRequirements

theorem referenceCoverageRequirements_eq :
    referenceCoverageRequirements =
      AAT.AG.FiniteModel.twoPatchCoverageRequirements :=
  rfl

noncomputable def referenceOverlap :
    Site.ContextOverlapPullback referenceContextPreorder

theorem referenceOverlap_selected
    (base left right : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    referenceOverlap.overlap
        (AAT.AG.FiniteModel.twoPatchContext base)
        (AAT.AG.FiniteModel.twoPatchContext left)
        (AAT.AG.FiniteModel.twoPatchContext right) =
      AAT.AG.FiniteModel.twoPatchContext
        (AAT.AG.FiniteModel.twoPatchContextMeet left right)

noncomputable def referenceSelectedGeometryReading :
    Site.SelectedGeometryReading AAT.AG.FiniteModel.corePackage where
  contextPreorder := referenceContextPreorder
  requirements := referenceCoverageRequirements
  overlap := referenceOverlap

@[simp] theorem referenceSelectedGeometryReading_eq :
    referenceSelectedGeometryReading =
      { contextPreorder := referenceContextPreorder
        requirements := referenceCoverageRequirements
        overlap := referenceOverlap } :=
  rfl

noncomputable def referenceSite :
    Site.AATSite AAT.AG.FiniteModel.corePackage.object :=
  referenceSelectedGeometryReading.toAATSite

@[simp] theorem referenceSite_eq :
    referenceSite = referenceSelectedGeometryReading.toAATSite :=
  rfl

noncomputable instance referenceSite_hasSheafifyInt :
    HasSheafify referenceSite.topology (AATCommAlgCat Int)

noncomputable instance referenceSite_hasSheafifyPolynomialInt :
    HasSheafify referenceSite.topology
      (AATCommAlgCat (Polynomial Int))

def context
    (i : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    referenceSite.category :=
  Site.ContextCategoryObject.of referenceContextPreorder
    (AAT.AG.FiniteModel.twoPatchContext i)

@[simp] theorem context_ctx
    (i : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    (context i).ctx = AAT.AG.FiniteModel.twoPatchContext i :=
  rfl

def overlapContext : referenceSite.category :=
  context AAT.AG.FiniteModel.TwoPatchContextIndex.overlap

def leftContext : referenceSite.category :=
  context AAT.AG.FiniteModel.TwoPatchContextIndex.left

def rightContext : referenceSite.category :=
  context AAT.AG.FiniteModel.TwoPatchContextIndex.right

def baseContext : referenceSite.category :=
  context AAT.AG.FiniteModel.TwoPatchContextIndex.base

theorem context_hom_iff
    (i j : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    Nonempty (context i ⟶ context j) ↔
      AAT.AG.FiniteModel.twoPatchContextIndexLe i j

def leftToBase : leftContext ⟶ baseContext

def rightToBase : rightContext ⟶ baseContext

def overlapToLeft : overlapContext ⟶ leftContext

def overlapToRight : overlapContext ⟶ rightContext

noncomputable def referenceCover :
    Site.AATCoverageFamily
      referenceSite.requirements referenceSite.overlap baseContext

noncomputable def referenceCoverIndexEquiv :
    referenceCover.Index ≃ AAT.AG.FiniteModel.TwoPatchCoverIndex

@[simp] theorem referenceCover_patch
    (i : AAT.AG.FiniteModel.TwoPatchCoverIndex) :
    referenceCover.patch (referenceCoverIndexEquiv.symm i) =
      AAT.AG.FiniteModel.twoPatchCoverPatch i

theorem referenceCover_presieve :
    referenceCover.presieve =
      Presieve.ofArrows
        (fun i : AAT.AG.FiniteModel.TwoPatchCoverIndex =>
          context (AAT.AG.FiniteModel.twoPatchCoverContextIndex i))
        (fun i => match i with
          | AAT.AG.FiniteModel.TwoPatchCoverIndex.left => leftToBase
          | AAT.AG.FiniteModel.TwoPatchCoverIndex.right => rightToBase)

theorem referenceCover_topologyCover :
    Sieve.generate referenceCover.presieve ∈
      referenceSite.topology baseContext

inductive ReferenceRawCoordinate where
  | coordinate
  | leftInverse
  | rightInverse
  deriving DecidableEq

theorem referenceRawCoordinate_cases (c : ReferenceRawCoordinate) :
    c = .coordinate ∨ c = .leftInverse ∨ c = .rightInverse := by
  cases c <;> simp

def referenceCoordinateFamily (W : referenceSite.category) :
    CoordinateFamily W.ctx where
  Coord := ReferenceRawCoordinate
  label _ := CoordinateLabel.semantic
  LocalData _ := PUnit

@[simp] theorem referenceCoordinateFamily_coord
    (W : referenceSite.category) :
    (referenceCoordinateFamily W).Coord = ReferenceRawCoordinate :=
  rfl

@[simp] theorem referenceCoordinateFamily_label
    (W : referenceSite.category)
    (c : ReferenceRawCoordinate) :
    (referenceCoordinateFamily W).label c = CoordinateLabel.semantic :=
  rfl

@[simp] theorem referenceCoordinateFamily_localData
    (W : referenceSite.category)
    (c : ReferenceRawCoordinate) :
    (referenceCoordinateFamily W).LocalData c = PUnit :=
  rfl

def rawVariable
    (W : referenceSite.category)
    (c : ReferenceRawCoordinate) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  MvPolynomial.X c

@[simp] theorem rawVariable_eq
    (W : referenceSite.category)
    (c : ReferenceRawCoordinate) :
    rawVariable W c = MvPolynomial.X c :=
  rfl

def rawX (W : referenceSite.category) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawVariable W .coordinate

@[simp] theorem rawX_eq (W : referenceSite.category) :
    rawX W = rawVariable W .coordinate :=
  rfl

def rawLeftInverse (W : referenceSite.category) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawVariable W .leftInverse

@[simp] theorem rawLeftInverse_eq (W : referenceSite.category) :
    rawLeftInverse W = rawVariable W .leftInverse :=
  rfl

def rawRightInverse (W : referenceSite.category) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawVariable W .rightInverse

@[simp] theorem rawRightInverse_eq (W : referenceSite.category) :
    rawRightInverse W = rawVariable W .rightInverse :=
  rfl

def leftInverseRelation (W : referenceSite.category) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawX W * rawLeftInverse W - 1

@[simp] theorem leftInverseRelation_eq (W : referenceSite.category) :
    leftInverseRelation W = rawX W * rawLeftInverse W - 1 :=
  rfl

def rightInverseRelation (W : referenceSite.category) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  (1 - rawX W) * rawRightInverse W - 1

@[simp] theorem rightInverseRelation_eq (W : referenceSite.category) :
    rightInverseRelation W = (1 - rawX W) * rawRightInverse W - 1 :=
  rfl

def leftIsInverted (W : referenceSite.category) : Prop :=
  W = leftContext ∨ W = overlapContext

def rightIsInverted (W : referenceSite.category) : Prop :=
  W = rightContext ∨ W = overlapContext

@[simp] theorem leftIsInverted_iff (W : referenceSite.category) :
    leftIsInverted W ↔ W = leftContext ∨ W = overlapContext :=
  Iff.rfl

@[simp] theorem rightIsInverted_iff (W : referenceSite.category) :
    rightIsInverted W ↔ W = rightContext ∨ W = overlapContext :=
  Iff.rfl

@[simp] theorem leftIsInverted_left :
    leftIsInverted leftContext

@[simp] theorem leftIsInverted_overlap :
    leftIsInverted overlapContext

@[simp] theorem leftIsInverted_base :
    ¬ leftIsInverted baseContext

@[simp] theorem leftIsInverted_right :
    ¬ leftIsInverted rightContext

@[simp] theorem rightIsInverted_right :
    rightIsInverted rightContext

@[simp] theorem rightIsInverted_overlap :
    rightIsInverted overlapContext

@[simp] theorem rightIsInverted_base :
    ¬ rightIsInverted baseContext

@[simp] theorem rightIsInverted_left :
    ¬ rightIsInverted leftContext

noncomputable def referenceRelationPolynomial
    (W : referenceSite.category) : Bool →
      FreeTypedCommAlg (referenceCoordinateFamily W) Int
  | false =>
      if leftIsInverted W then leftInverseRelation W else rawLeftInverse W
  | true =>
      if rightIsInverted W then rightInverseRelation W else rawRightInverse W

@[simp] theorem referenceRelationPolynomial_false
    (W : referenceSite.category) :
    referenceRelationPolynomial W false =
      if leftIsInverted W then leftInverseRelation W else rawLeftInverse W :=
  rfl

@[simp] theorem referenceRelationPolynomial_true
    (W : referenceSite.category) :
    referenceRelationPolynomial W true =
      if rightIsInverted W then rightInverseRelation W else rawRightInverse W :=
  rfl

noncomputable def referenceRelationFamily
    (W : referenceSite.category) :
    StructuralRelationFamily (referenceCoordinateFamily W) Int where
  Relation := Bool
  polynomial := referenceRelationPolynomial W

@[simp] theorem referenceRelationFamily_relation
    (W : referenceSite.category) :
    (referenceRelationFamily W).Relation = Bool :=
  rfl

@[simp] theorem referenceRelationFamily_polynomial
    (W : referenceSite.category)
    (r : Bool) :
    (referenceRelationFamily W).polynomial r =
      referenceRelationPolynomial W r :=
  rfl

theorem base_JStruct_eq :
    (referenceRelationFamily baseContext).JStruct =
      Ideal.span {rawLeftInverse baseContext, rawRightInverse baseContext}

theorem left_JStruct_eq :
    (referenceRelationFamily leftContext).JStruct =
      Ideal.span
        {leftInverseRelation leftContext, rawRightInverse leftContext}

theorem right_JStruct_eq :
    (referenceRelationFamily rightContext).JStruct =
      Ideal.span
        {rawLeftInverse rightContext, rightInverseRelation rightContext}

theorem overlap_JStruct_eq :
    (referenceRelationFamily overlapContext).JStruct =
      Ideal.span
        {leftInverseRelation overlapContext,
          rightInverseRelation overlapContext}

noncomputable def referenceTypedRestriction
    {source target : referenceSite.category}
    (f : source ⟶ target) :
    TypedCoordinateRestriction
      (referenceCoordinateFamily source)
      (referenceCoordinateFamily target) Int
      (referenceSite.contextPreorder.morphism
        (CategoryTheory.leOfHom f)) where
  variableImage
    | .coordinate => rawX source
    | .leftInverse =>
        if leftIsInverted target then rawLeftInverse source
        else if leftIsInverted source then leftInverseRelation source
        else rawLeftInverse source
    | .rightInverse =>
        if rightIsInverted target then rawRightInverse source
        else if rightIsInverted source then rightInverseRelation source
        else rawRightInverse source

@[simp] theorem referenceTypedRestriction_variableImage
    {source target : referenceSite.category}
    (f : source ⟶ target)
    (c : ReferenceRawCoordinate) :
    (referenceTypedRestriction f).variableImage c =
      match c with
      | .coordinate => rawX source
      | .leftInverse =>
          if leftIsInverted target then rawLeftInverse source
          else if leftIsInverted source then leftInverseRelation source
          else rawLeftInverse source
      | .rightInverse =>
          if rightIsInverted target then rawRightInverse source
          else if rightIsInverted source then rightInverseRelation source
          else rawRightInverse source :=
  rfl

theorem referenceTypedRestriction_maps_JStruct
    {source target : referenceSite.category}
    (f : source ⟶ target)
    (p : FreeTypedCommAlg (referenceCoordinateFamily target) Int)
    (hp : p ∈ (referenceRelationFamily target).JStruct) :
    (referenceTypedRestriction f).polynomialMap p ∈
      (referenceRelationFamily source).JStruct

noncomputable def referenceRestrictionStable
    {source target : referenceSite.category}
    (f : source ⟶ target) :
    RestrictionStableStructuralRelations
      (referenceRelationFamily source)
      (referenceRelationFamily target)
      (referenceSite.contextPreorder.morphism
        (CategoryTheory.leOfHom f)) where
  restriction := referenceTypedRestriction f
  maps_JStruct := referenceTypedRestriction_maps_JStruct f

theorem referenceRestrictionStable_identity
    (W : referenceSite.category) :
    (referenceRestrictionStable (𝟙 W)).restriction.polynomialMap =
      RingHom.id (FreeTypedCommAlg (referenceCoordinateFamily W) Int)

theorem referenceRestrictionStable_comp
    {X Y Z : referenceSite.category}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (referenceRestrictionStable (f ≫ g)).restriction.polynomialMap =
      ((referenceRestrictionStable f).restriction.polynomialMap).comp
        ((referenceRestrictionStable g).restriction.polynomialMap)

noncomputable def referenceRaw :
    RawAmbientRestrictionSystem referenceSite Int where
  coordFamily := referenceCoordinateFamily
  relationFamily := referenceRelationFamily
  restrictionStable := referenceRestrictionStable
  identity_polynomialMap := referenceRestrictionStable_identity
  composition_polynomialMap := referenceRestrictionStable_comp

@[simp] theorem referenceRaw_coordFamily
    (W : referenceSite.category) :
    referenceRaw.coordFamily W = referenceCoordinateFamily W :=
  rfl

@[simp] theorem referenceRaw_relationFamily
    (W : referenceSite.category) :
    referenceRaw.relationFamily W = referenceRelationFamily W :=
  rfl

@[simp] theorem referenceRaw_restrictionStable
    {source target : referenceSite.category}
    (f : source ⟶ target) :
    referenceRaw.restrictionStable f = referenceRestrictionStable f :=
  rfl

noncomputable def rawCoordinate (W : referenceSite.category) :
    referenceRaw.rawAlgebra W :=
  (referenceRelationFamily W).quotientMap (rawX W)

@[simp] theorem rawCoordinate_eq (W : referenceSite.category) :
    rawCoordinate W =
      (referenceRelationFamily W).quotientMap (rawX W) :=
  rfl

theorem rawCoordinate_restrict
    {source target : referenceSite.category}
    (f : source ⟶ target) :
    (referenceRaw.restrictionStable f).quotientDesc
        (rawCoordinate target) =
      rawCoordinate source

noncomputable def baseRawAlgebraIso :
    CommRingCat.of (referenceRaw.rawAlgebra baseContext) ≅
      CommRingCat.of AmbientRing

noncomputable def leftRawAlgebraIso :
    CommRingCat.of (referenceRaw.rawAlgebra leftContext) ≅
      CommRingCat.of (Localization.Away leftGenerator)

noncomputable def rightRawAlgebraIso :
    CommRingCat.of (referenceRaw.rawAlgebra rightContext) ≅
      CommRingCat.of (Localization.Away rightGenerator)

noncomputable def overlapRawAlgebraIso :
    CommRingCat.of (referenceRaw.rawAlgebra overlapContext) ≅
      CommRingCat.of (Localization.Away overlapGenerator)

@[simp] theorem baseRawAlgebraIso_coordinate :
    baseRawAlgebraIso.hom (rawCoordinate baseContext) = coordinate

@[simp] theorem leftRawAlgebraIso_coordinate :
    leftRawAlgebraIso.hom (rawCoordinate leftContext) =
      algebraMap AmbientRing (Localization.Away leftGenerator) coordinate

@[simp] theorem rightRawAlgebraIso_coordinate :
    rightRawAlgebraIso.hom (rawCoordinate rightContext) =
      algebraMap AmbientRing (Localization.Away rightGenerator) coordinate

@[simp] theorem overlapRawAlgebraIso_coordinate :
    overlapRawAlgebraIso.hom (rawCoordinate overlapContext) =
      algebraMap AmbientRing (Localization.Away overlapGenerator) coordinate

theorem referenceRaw_isSheaf :
    Presheaf.IsSheaf referenceSite.topology referenceRaw.toPresheaf

theorem canonical_component_isIso (W : referenceSite.category) :
    IsIso (referenceRaw.toRingedSite.canonical.app (op W))

noncomputable def baseSectionRingIso :
    SheafifiedSectionRing referenceRaw baseContext ≅
      CommRingCat.of AmbientRing

noncomputable def leftSectionRingIso :
    SheafifiedSectionRing referenceRaw leftContext ≅
      CommRingCat.of (Localization.Away leftGenerator)

noncomputable def rightSectionRingIso :
    SheafifiedSectionRing referenceRaw rightContext ≅
      CommRingCat.of (Localization.Away rightGenerator)

noncomputable def overlapSectionRingIso :
    SheafifiedSectionRing referenceRaw overlapContext ≅
      CommRingCat.of (Localization.Away overlapGenerator)

theorem leftGenerator_dvd_overlap :
    leftGenerator ∣ overlapGenerator :=
  ⟨rightGenerator, rfl⟩

theorem rightGenerator_dvd_overlap :
    rightGenerator ∣ overlapGenerator :=
  ⟨leftGenerator, mul_comm _ _⟩

theorem leftGenerator_isUnit_on_overlap :
    IsUnit
      (algebraMap AmbientRing (Localization.Away overlapGenerator)
        leftGenerator) :=
  IsLocalization.Away.isUnit_of_dvd
    overlapGenerator leftGenerator_dvd_overlap

theorem rightGenerator_isUnit_on_overlap :
    IsUnit
      (algebraMap AmbientRing (Localization.Away overlapGenerator)
        rightGenerator) :=
  IsLocalization.Away.isUnit_of_dvd
    overlapGenerator rightGenerator_dvd_overlap

noncomputable def leftToOverlapRingHom :
    Localization.Away leftGenerator →+*
      Localization.Away overlapGenerator :=
  IsLocalization.Away.lift
    leftGenerator leftGenerator_isUnit_on_overlap

noncomputable def rightToOverlapRingHom :
    Localization.Away rightGenerator →+*
      Localization.Away overlapGenerator :=
  IsLocalization.Away.lift
    rightGenerator rightGenerator_isUnit_on_overlap

@[simp] theorem leftToOverlapRingHom_comp_algebraMap :
    leftToOverlapRingHom.comp
        (algebraMap AmbientRing (Localization.Away leftGenerator)) =
      algebraMap AmbientRing (Localization.Away overlapGenerator)

@[simp] theorem rightToOverlapRingHom_comp_algebraMap :
    rightToOverlapRingHom.comp
        (algebraMap AmbientRing (Localization.Away rightGenerator)) =
      algebraMap AmbientRing (Localization.Away overlapGenerator)

theorem left_restriction_is_localization :
    baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw leftToBase ≫
        leftSectionRingIso.hom =
      CommRingCat.ofHom
        (algebraMap AmbientRing (Localization.Away leftGenerator))

theorem right_restriction_is_localization :
    baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw rightToBase ≫
        rightSectionRingIso.hom =
      CommRingCat.ofHom
        (algebraMap AmbientRing (Localization.Away rightGenerator))

theorem overlap_left_restriction_is_localization :
    leftSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw overlapToLeft ≫
        overlapSectionRingIso.hom =
      CommRingCat.ofHom leftToOverlapRingHom

theorem overlap_right_restriction_is_localization :
    rightSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw overlapToRight ≫
        overlapSectionRingIso.hom =
      CommRingCat.ofHom rightToOverlapRingHom

theorem left_restriction_not_isIso :
    ¬ IsIso (sheafifiedRestriction referenceRaw leftToBase)

theorem right_restriction_not_isIso :
    ¬ IsIso (sheafifiedRestriction referenceRaw rightToBase)
~~~

`referenceContextPreorder_le_iff`は全contextを量化し、selected四context間では
`twoPatchContextIndexLe`のarrowだけ、それ以外ではidentityだけであることを固定する。
したがってbaseからleftへの逆arrowはなく、localization restrictionをisomorphismへ
強制しない。`referenceOverlap_selected`はselected四context上のoverlapを
`twoPatchContextMeet`へ同定する。`referenceCoverageRequirements_eq`、
`referenceCoverIndexEquiv`、`referenceCover_patch`、`referenceCover_presieve`は、
coverがexactly left / rightの二patchとそのinclusionであることを固定する。
canonical `FiniteModel.twoPatchSite`のcontext categoryを流用しない。

`referenceRaw`のfree algebraは、全contextでexactly
`ReferenceRawCoordinate.coordinate / leftInverse / rightInverse`の三変数を持つ。
baseでは両inverse variableを`0`へ、leftでは`x·leftInverse-1`と`rightInverse`を、
rightでは`leftInverse`と`(1-x)·rightInverse-1`を、overlapでは二つのinverse relationを
structural idealへ入れる。四`*_JStruct_eq`がこのrelation inventoryを固定し、
追加変数、追加relation、別presentationを許さない。

`referenceTypedRestriction.variableImage`は、targetで未可逆なinverse variableを、
sourceで新たに可逆化する場合に対応するinverse relationへ送る。その他は同名variableへ送る。
この一つのpiecewise definitionから`maps_JStruct`、identity、compositionを証明し、
`referenceRaw`の全data-bearing fieldへ直接渡す。localization ring、restriction map、
sheaf condition、comparison isoを自由なfieldとして受け取らない。
`rawCoordinate`は`rawX`のstructural quotient classとして定義し、
`rawCoordinate_restrict`と四つの`RawAlgebraIso_coordinate` theoremにより、同じclassが
global polynomial variableと各localizationへ運ばれることを固定する。
overlap側の二RingHomは各generatorの`overlapGenerator`に対するdivisibilityとunit theoremから
`IsLocalization.Away.lift`で構成し、二つの`comp_algebraMap` theoremで
AmbientRingのcanonical mapを延長することを固定する。

### SD1 — actual two-chart StandardArchitectureScheme

~~~lean
noncomputable def ambientScheme : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of AmbientRing)

@[simp] theorem ambientScheme_eq :
    ambientScheme =
      AlgebraicGeometry.Spec (CommRingCat.of AmbientRing) :=
  rfl

noncomputable def baseChartDomainIso :
    architectureChartSpec referenceRaw baseContext ≅
      ambientScheme :=
  AlgebraicGeometry.Scheme.Spec.mapIso baseSectionRingIso.op

@[simp] theorem baseChartDomainIso_eq :
    baseChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso baseSectionRingIso.op :=
  rfl

noncomputable def leftChartDomainIso :
    architectureChartSpec referenceRaw leftContext ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away leftGenerator)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso leftSectionRingIso.op

@[simp] theorem leftChartDomainIso_eq :
    leftChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso leftSectionRingIso.op :=
  rfl

noncomputable def rightChartDomainIso :
    architectureChartSpec referenceRaw rightContext ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away rightGenerator)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso rightSectionRingIso.op

@[simp] theorem rightChartDomainIso_eq :
    rightChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso rightSectionRingIso.op :=
  rfl

noncomputable def overlapChartDomainIso :
    architectureChartSpec referenceRaw overlapContext ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso overlapSectionRingIso.op

@[simp] theorem overlapChartDomainIso_eq :
    overlapChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso overlapSectionRingIso.op :=
  rfl

noncomputable def ambientDecoration :
    AATReadingDecoration referenceRaw ambientScheme :=
  AATReadingDecoration.pullback
    referenceRaw baseChartDomainIso.inv
    (AATReadingDecoration.ofContext referenceRaw baseContext)

@[simp] theorem ambientDecoration_eq :
    ambientDecoration =
      AATReadingDecoration.pullback
        referenceRaw baseChartDomainIso.inv
        (AATReadingDecoration.ofContext referenceRaw baseContext) :=
  rfl

noncomputable def leftChart :
    ArchitectureAffineChart
      referenceRaw ambientScheme ambientDecoration where
  context := leftContext
  contextHom := leftToBase
  map :=
    leftChartDomainIso.hom ≫
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom
          (algebraMap AmbientRing
            (Localization.Away leftGenerator))).op

noncomputable def rightChart :
    ArchitectureAffineChart
      referenceRaw ambientScheme ambientDecoration where
  context := rightContext
  contextHom := rightToBase
  map :=
    rightChartDomainIso.hom ≫
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom
          (algebraMap AmbientRing
            (Localization.Away rightGenerator))).op

noncomputable def referenceAtlas :
    ArchitectureAffineAtlas
      referenceRaw ambientScheme ambientDecoration where
  Index := Bool
  chart
    | false => leftChart
    | true => rightChart

theorem referenceAtlas_valid :
    IsArchitectureAffineAtlas referenceRaw referenceAtlas

noncomputable def referenceOverlapPresentation :
    ArchitectureOverlapPresentation referenceRaw referenceAtlas

theorem referenceOverlapPresentation_valid :
    IsArchitectureOverlapPresentation
      referenceRaw referenceOverlapPresentation

noncomputable def referenceScheme :
    StandardArchitectureScheme referenceRaw :=
  StandardArchitectureScheme.ofPresentation
    referenceRaw ambientScheme ambientDecoration
    referenceAtlas referenceAtlas_valid
    referenceOverlapPresentation
    referenceOverlapPresentation_valid

@[simp] theorem referenceScheme_eq :
    referenceScheme =
      StandardArchitectureScheme.ofPresentation
        referenceRaw ambientScheme ambientDecoration
        referenceAtlas referenceAtlas_valid
        referenceOverlapPresentation
        referenceOverlapPresentation_valid :=
  rfl

def leftIndex : referenceScheme.atlas.Index :=
  false

def rightIndex : referenceScheme.atlas.Index :=
  true

theorem leftIndex_ne_rightIndex : leftIndex ≠ rightIndex

theorem index_cases (i : referenceScheme.atlas.Index) :
    i = leftIndex ∨ i = rightIndex

@[simp] theorem referenceScheme_underlying :
    referenceScheme.underlying = ambientScheme :=
  rfl

@[simp] theorem left_chart_context :
    (referenceScheme.atlas.chart leftIndex).context = leftContext

@[simp] theorem right_chart_context :
    (referenceScheme.atlas.chart rightIndex).context = rightContext

theorem chart_contexts_ne :
    (referenceScheme.atlas.chart leftIndex).context ≠
      (referenceScheme.atlas.chart rightIndex).context

@[simp] theorem left_chart_map :
    (referenceScheme.atlas.chart leftIndex).map =
      leftChartDomainIso.hom ≫
        AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom
            (algebraMap AmbientRing
              (Localization.Away leftGenerator))).op

@[simp] theorem right_chart_map :
    (referenceScheme.atlas.chart rightIndex).map =
      rightChartDomainIso.hom ≫
        AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom
            (algebraMap AmbientRing
              (Localization.Away rightGenerator))).op

theorem left_chart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart leftIndex).map

theorem right_chart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart rightIndex).map

theorem twoChart_jointlyCovers :
    ⨆ i,
        ((referenceScheme.affineOpenCover referenceRaw).f i).opensRange =
      ⊤

theorem left_chart_not_isIso :
    ¬ IsIso (referenceScheme.atlas.chart leftIndex).map

theorem right_chart_not_isIso :
    ¬ IsIso (referenceScheme.atlas.chart rightIndex).map

@[simp] theorem pair_context :
    referenceScheme.atlas.pairContext
        referenceRaw leftIndex rightIndex =
      overlapContext

noncomputable def actualOverlapIso :
    referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator)) :=
  (referenceScheme.overlap_is_actual_pullback
      referenceRaw leftIndex rightIndex).symm ≪≫
    eqToIso (by rw [pair_context]) ≪≫
    overlapChartDomainIso

@[simp] theorem actualOverlapIso_eq :
    actualOverlapIso =
      (referenceScheme.overlap_is_actual_pullback
          referenceRaw leftIndex rightIndex).symm ≪≫
        eqToIso (by rw [pair_context]) ≪≫
        overlapChartDomainIso :=
  rfl

theorem actualOverlap_nonempty :
    Nonempty
      (referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex)

theorem decoration_overlap :
    sheafifiedRestriction referenceRaw
        (referenceScheme.atlas.pairToLeft
            referenceRaw leftIndex rightIndex ≫
          (referenceScheme.atlas.chart leftIndex).contextHom) =
      sheafifiedRestriction referenceRaw
        (referenceScheme.atlas.pairToRight
            referenceRaw leftIndex rightIndex ≫
          (referenceScheme.atlas.chart rightIndex).contextHom)

theorem actual_triple_cocycle :
    ∀ i j l : referenceScheme.atlas.Index,
      referenceScheme.atlas.actualTripleToLeft
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart i).map =
        referenceScheme.atlas.actualTripleToMiddle
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart j).map ∧
      referenceScheme.atlas.actualTripleToMiddle
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart j).map =
        referenceScheme.atlas.actualTripleToRight
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart l).map
~~~

chartは`D(x)`、`D(1-x)`のactual principal-open immersionであり、
既存`twoChartReferenceModel`のisomorphism chartを別名化しない。
`ambientDecoration`はbase global sectionsと`baseSectionRingIso`から構成し、
`leftChart`、`rightChart`はSD0のlocalization comparisonから構成する。
atlas validityとoverlap validityは別theoremであり、`referenceScheme`の自由入力にしない。
`actualOverlapIso`は`overlap_is_actual_pullback`の逆、`pair_context`によるtransport、
`overlapChartDomainIso`の三段合成に固定し、任意のoverlap isoを選ばない。
`left_chart_not_isIso`、`right_chart_not_isIso`、
`left_restriction_not_isIso`、`right_restriction_not_isIso`を
proper openとnontrivial restrictionの回帰証拠とする。

### SD2 — closed-equational readingsとstrict ideal chain

~~~lean
noncomputable def weakLawEquationCore :
    SemanticLawEquationWitnessIdealCore referenceSite

noncomputable def strongLawEquationCore :
    SemanticLawEquationWitnessIdealCore referenceSite

noncomputable def rigidLawEquationCore :
    SemanticLawEquationWitnessIdealCore referenceSite

@[simp] theorem weakLawEquationCore_observable
    (W : referenceSite.category) :
    weakLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  rfl

@[simp] theorem strongLawEquationCore_observable
    (W : referenceSite.category) :
    strongLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  rfl

@[simp] theorem rigidLawEquationCore_observable
    (W : referenceSite.category) :
    rigidLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  rfl

@[simp] theorem weakLawEquationCore_observableCommRing
    (W : referenceSite.category) :
    weakLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  rfl

@[simp] theorem strongLawEquationCore_observableCommRing
    (W : referenceSite.category) :
    strongLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  rfl

@[simp] theorem rigidLawEquationCore_observableCommRing
    (W : referenceSite.category) :
    rigidLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  rfl

@[simp] theorem weakLawEquationCore_restrict
    {source target : referenceSite.category} (f : source ⟶ target) :
    weakLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  rfl

@[simp] theorem strongLawEquationCore_restrict
    {source target : referenceSite.category} (f : source ⟶ target) :
    strongLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  rfl

@[simp] theorem rigidLawEquationCore_restrict
    {source target : referenceSite.category} (f : source ⟶ target) :
    rigidLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  rfl

@[simp] theorem weakViolationWitness_eq
    (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    weakLawEquationCore.violationWitness W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else 0

@[simp] theorem strongViolationWitness_eq
    (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    strongLawEquationCore.violationWitness W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        rawCoordinate W
      else 0

@[simp] theorem rigidViolationWitness_eq
    (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    rigidLawEquationCore.violationWitness W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        rawCoordinate W
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentC then
        algebraMap Int (referenceRaw.rawAlgebra W) 2
      else 0

@[simp] theorem weakLawEquationCore_supportAtom :
    weakLawEquationCore.supportAtom =
      AAT.AG.FiniteModel.FiniteAtom.componentA :=
  rfl

@[simp] theorem strongLawEquationCore_supportAtom :
    strongLawEquationCore.supportAtom =
      AAT.AG.FiniteModel.FiniteAtom.componentA :=
  rfl

@[simp] theorem rigidLawEquationCore_supportAtom :
    rigidLawEquationCore.supportAtom =
      AAT.AG.FiniteModel.FiniteAtom.componentA :=
  rfl

@[simp] theorem weakLawEquationCore_supportLawIndex :
    weakLawEquationCore.supportLawIndex = PUnit.unit :=
  rfl

@[simp] theorem strongLawEquationCore_supportLawIndex :
    strongLawEquationCore.supportLawIndex = PUnit.unit :=
  rfl

@[simp] theorem rigidLawEquationCore_supportLawIndex :
    rigidLawEquationCore.supportLawIndex = PUnit.unit :=
  rfl

noncomputable def weakSchemeBridge :
    SemanticLawEquationSchemeBridge referenceRaw weakLawEquationCore

noncomputable def strongSchemeBridge :
    SemanticLawEquationSchemeBridge referenceRaw strongLawEquationCore

noncomputable def rigidSchemeBridge :
    SemanticLawEquationSchemeBridge referenceRaw rigidLawEquationCore

@[simp] theorem weakSchemeBridge_toRawPresentation
    (W : referenceSite.category) :
    weakSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  rfl

@[simp] theorem strongSchemeBridge_toRawPresentation
    (W : referenceSite.category) :
    strongSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  rfl

@[simp] theorem rigidSchemeBridge_toRawPresentation
    (W : referenceSite.category) :
    rigidSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  rfl

theorem weakSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge
      referenceRaw weakLawEquationCore weakSchemeBridge

theorem strongSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge
      referenceRaw strongLawEquationCore strongSchemeBridge

theorem rigidSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge
      referenceRaw rigidLawEquationCore rigidSchemeBridge

noncomputable def weakReading :
    ClosedEquationalLawReading referenceRaw referenceScheme :=
  ClosedEquationalLawReading.ofSemanticCore
    referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge

@[simp] theorem weakReading_eq :
    weakReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge :=
  rfl

noncomputable def strongReading :
    ClosedEquationalLawReading referenceRaw referenceScheme :=
  ClosedEquationalLawReading.ofSemanticCore
    referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge

@[simp] theorem strongReading_eq :
    strongReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge :=
  rfl

noncomputable def rigidReading :
    ClosedEquationalLawReading referenceRaw referenceScheme :=
  ClosedEquationalLawReading.ofSemanticCore
    referenceRaw referenceScheme rigidLawEquationCore rigidSchemeBridge

@[simp] theorem rigidReading_eq :
    rigidReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme rigidLawEquationCore rigidSchemeBridge :=
  rfl

theorem weakReading_valid :
    IsClosedEquationalLawReading referenceRaw referenceScheme weakReading

theorem strongReading_valid :
    IsClosedEquationalLawReading referenceRaw referenceScheme strongReading

theorem rigidReading_valid :
    IsClosedEquationalLawReading referenceRaw referenceScheme rigidReading

theorem weakReading_requiredClosed :
    RequiredClosed referenceRaw referenceScheme weakReading

theorem strongReading_requiredClosed :
    RequiredClosed referenceRaw referenceScheme strongReading

theorem rigidReading_requiredClosed :
    RequiredClosed referenceRaw referenceScheme rigidReading

theorem weakReading_requiredLawIdealExact :
    RequiredLawIdealExact referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed

theorem strongReading_requiredLawIdealExact :
    RequiredLawIdealExact referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed

theorem rigidReading_requiredLawIdealExact :
    RequiredLawIdealExact referenceRaw referenceScheme
      rigidReading rigidReading_valid rigidReading_requiredClosed

noncomputable abbrev weakIdealSheaf :
    referenceScheme.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed

@[simp] theorem weakIdealSheaf_eq :
    weakIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  rfl

noncomputable abbrev strongIdealSheaf :
    referenceScheme.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf referenceRaw referenceScheme
    strongReading strongReading_valid strongReading_requiredClosed

@[simp] theorem strongIdealSheaf_eq :
    strongIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  rfl

noncomputable abbrev rigidIdealSheaf :
    referenceScheme.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf referenceRaw referenceScheme
    rigidReading rigidReading_valid rigidReading_requiredClosed

@[simp] theorem rigidIdealSheaf_eq :
    rigidIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rfl

noncomputable abbrev weakLocus : AlgebraicGeometry.Scheme :=
  lawfulClosedSubscheme referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed

@[simp] theorem weakLocus_eq :
    weakLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  rfl

noncomputable abbrev strongLocus : AlgebraicGeometry.Scheme :=
  lawfulClosedSubscheme referenceRaw referenceScheme
    strongReading strongReading_valid strongReading_requiredClosed

@[simp] theorem strongLocus_eq :
    strongLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  rfl

noncomputable abbrev rigidLocus : AlgebraicGeometry.Scheme :=
  lawfulClosedSubscheme referenceRaw referenceScheme
    rigidReading rigidReading_valid rigidReading_requiredClosed

@[simp] theorem rigidLocus_eq :
    rigidLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rfl

noncomputable abbrev weakImmersion :
    weakLocus ⟶ referenceScheme.underlying :=
  lawfulClosedImmersion referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed

@[simp] theorem weakImmersion_eq :
    weakImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  rfl

noncomputable abbrev strongImmersion :
    strongLocus ⟶ referenceScheme.underlying :=
  lawfulClosedImmersion referenceRaw referenceScheme
    strongReading strongReading_valid strongReading_requiredClosed

@[simp] theorem strongImmersion_eq :
    strongImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  rfl

noncomputable abbrev rigidImmersion :
    rigidLocus ⟶ referenceScheme.underlying :=
  lawfulClosedImmersion referenceRaw referenceScheme
    rigidReading rigidReading_valid rigidReading_requiredClosed

@[simp] theorem rigidImmersion_eq :
    rigidImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rfl

noncomputable def ambientGlobalSectionsIso :
  Γ(referenceScheme.underlying, ⊤) ≅
      CommRingCat.of AmbientRing :=
  AlgebraicGeometry.Scheme.ΓSpecIso
    (CommRingCat.of AmbientRing)

@[simp] theorem ambientGlobalSectionsIso_eq :
    ambientGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of AmbientRing) :=
  rfl

@[simp] theorem weakGlobalEquation_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else 0

@[simp] theorem strongGlobalEquation_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        coordinate
      else 0

@[simp] theorem rigidGlobalEquation_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          rigidLawEquationCore rigidSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        coordinate
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentC then
        MvPolynomial.C 2
      else 0

def weakAmbientIdeal : Ideal AmbientRing :=
  Ideal.span {coordinate * (coordinate - 1)}

@[simp] theorem weakAmbientIdeal_eq :
    weakAmbientIdeal =
      Ideal.span {coordinate * (coordinate - 1)} :=
  rfl

def strongAmbientIdeal : Ideal AmbientRing :=
  Ideal.span {coordinate}

@[simp] theorem strongAmbientIdeal_eq :
    strongAmbientIdeal = Ideal.span {coordinate} :=
  rfl

def rigidAmbientIdeal : Ideal AmbientRing :=
  Ideal.span {coordinate, MvPolynomial.C 2}

@[simp] theorem rigidAmbientIdeal_eq :
    rigidAmbientIdeal =
      Ideal.span {coordinate, MvPolynomial.C 2} :=
  rfl

def weakLeftIdeal : Ideal (Localization.Away leftGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away leftGenerator)
      (coordinate * (coordinate - 1))}

@[simp] theorem weakLeftIdeal_eq :
    weakLeftIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away leftGenerator)
          (coordinate * (coordinate - 1))} :=
  rfl

def weakRightIdeal : Ideal (Localization.Away rightGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away rightGenerator)
      (coordinate * (coordinate - 1))}

@[simp] theorem weakRightIdeal_eq :
    weakRightIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away rightGenerator)
          (coordinate * (coordinate - 1))} :=
  rfl

def weakOverlapIdeal : Ideal (Localization.Away overlapGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away overlapGenerator)
      (coordinate * (coordinate - 1))}

@[simp] theorem weakOverlapIdeal_eq :
    weakOverlapIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away overlapGenerator)
          (coordinate * (coordinate - 1))} :=
  rfl

def strongLeftIdeal : Ideal (Localization.Away leftGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away leftGenerator) coordinate}

@[simp] theorem strongLeftIdeal_eq :
    strongLeftIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away leftGenerator) coordinate} :=
  rfl

def strongRightIdeal : Ideal (Localization.Away rightGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away rightGenerator) coordinate}

@[simp] theorem strongRightIdeal_eq :
    strongRightIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away rightGenerator) coordinate} :=
  rfl

def strongOverlapIdeal : Ideal (Localization.Away overlapGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away overlapGenerator) coordinate}

@[simp] theorem strongOverlapIdeal_eq :
    strongOverlapIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away overlapGenerator) coordinate} :=
  rfl

noncomputable def leftChartGlobalSectionsIso :
  Γ(leftChart.domain, ⊤) ≅
      CommRingCat.of (Localization.Away leftGenerator) :=
  AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing referenceRaw leftContext) ≪≫
    leftSectionRingIso

@[simp] theorem leftChartGlobalSectionsIso_eq :
    leftChartGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw leftContext) ≪≫
        leftSectionRingIso :=
  rfl

noncomputable def rightChartGlobalSectionsIso :
  Γ(rightChart.domain, ⊤) ≅
      CommRingCat.of (Localization.Away rightGenerator) :=
  AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing referenceRaw rightContext) ≪≫
    rightSectionRingIso

@[simp] theorem rightChartGlobalSectionsIso_eq :
    rightChartGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw rightContext) ≪≫
        rightSectionRingIso :=
  rfl

noncomputable def actualOverlapGlobalSectionsIso :
    Γ(referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex, ⊤) ≅
      CommRingCat.of (Localization.Away overlapGenerator) :=
  (asIso actualOverlapIso.inv.appTop) ≪≫
    AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (Localization.Away overlapGenerator))

@[simp] theorem actualOverlapGlobalSectionsIso_eq :
    actualOverlapGlobalSectionsIso =
      (asIso actualOverlapIso.inv.appTop) ≪≫
        AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (Localization.Away overlapGenerator)) :=
  rfl

theorem weakIdeal_top_eq :
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (weakIdealSheaf.ideal ⊤) =
      weakAmbientIdeal

theorem strongIdeal_top_eq :
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ⊤) =
      strongAmbientIdeal

theorem rigidIdeal_top_eq :
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (rigidIdealSheaf.ideal ⊤) =
      rigidAmbientIdeal

theorem weakIdeal_left_eq :
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap leftChart.map).ideal ⊤) =
      weakLeftIdeal

theorem weakIdeal_right_eq :
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap rightChart.map).ideal ⊤) =
      weakRightIdeal

theorem weakIdeal_overlap_eq :
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal ⊤) =
      weakOverlapIdeal

theorem strongIdeal_left_eq :
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap leftChart.map).ideal ⊤) =
      strongLeftIdeal

theorem strongIdeal_right_eq :
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap rightChart.map).ideal ⊤) =
      strongRightIdeal

theorem strongIdeal_overlap_eq :
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal ⊤) =
      strongOverlapIdeal

theorem weakIdeal_overlap_agrees :
    (weakIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (weakIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map)

theorem strongIdeal_overlap_agrees :
    (strongIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (strongIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map)

theorem weakAmbientIdeal_ne_bot :
    weakAmbientIdeal ≠ ⊥

theorem weakAmbientIdeal_ne_top :
    weakAmbientIdeal ≠ ⊤

theorem strongAmbientIdeal_ne_bot :
    strongAmbientIdeal ≠ ⊥

theorem strongAmbientIdeal_ne_top :
    strongAmbientIdeal ≠ ⊤

theorem rigidAmbientIdeal_ne_bot :
    rigidAmbientIdeal ≠ ⊥

theorem rigidAmbientIdeal_ne_top :
    rigidAmbientIdeal ≠ ⊤

theorem weakIdeal_lt_strongIdeal :
    weakIdealSheaf < strongIdealSheaf

theorem strongIdeal_lt_rigidIdeal :
    strongIdealSheaf < rigidIdealSheaf

theorem weakLocus_nonempty :
    Nonempty weakLocus

theorem strongLocus_nonempty :
    Nonempty strongLocus

theorem rigidLocus_nonempty :
    Nonempty rigidLocus

theorem weakImmersion_not_isIso :
    ¬ IsIso weakImmersion

theorem strongImmersion_not_isIso :
    ¬ IsIso strongImmersion

theorem rigidImmersion_not_isIso :
    ¬ IsIso rigidImmersion

@[simp] theorem weakImmersion_ker :
    weakImmersion.ker = weakIdealSheaf

@[simp] theorem strongImmersion_ker :
    strongImmersion.ker = strongIdealSheaf

@[simp] theorem weakImmersion_zeroLocus :
    Set.range weakImmersion = weakIdealSheaf.support

@[simp] theorem strongImmersion_zeroLocus :
    Set.range strongImmersion = strongIdealSheaf.support

noncomputable def ambientTopAffineOpen :
    referenceScheme.underlying.affineOpens

@[simp] theorem ambientTopAffineOpen_obj :
    ambientTopAffineOpen.1 = ⊤

noncomputable def weakAffineQuotientChart :
    AlgebraicGeometry.Spec
        (CommRingCat.of
          (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
            weakIdealSheaf.ideal ambientTopAffineOpen)) ⟶
      weakLocus :=
  (lawfulClosedSubschemeCover
    referenceRaw referenceScheme weakReading weakReading_valid
    weakReading_requiredClosed).f ambientTopAffineOpen

noncomputable def strongAffineQuotientChart :
    AlgebraicGeometry.Spec
        (CommRingCat.of
          (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
            strongIdealSheaf.ideal ambientTopAffineOpen)) ⟶
      strongLocus :=
  (lawfulClosedSubschemeCover
    referenceRaw referenceScheme strongReading strongReading_valid
    strongReading_requiredClosed).f ambientTopAffineOpen

theorem weakAffineQuotientChart_isIso :
    IsIso weakAffineQuotientChart

theorem strongAffineQuotientChart_isIso :
    IsIso strongAffineQuotientChart
~~~

weak coreは`componentA`に`x(x-1)`だけを置く。strong coreは同じatom上の旧generatorを保持し、
`componentB`に追加generator`x`を置くため、generated idealはそれぞれ`(x(x-1))`と`(x)`になる。
その他のatomは`0`であり、`weakToStrongAtomMap`が旧generatorをstrong側へ直接対応させる。
rigid coreはさらに`componentC`へconstant `2`を置き、global idealを`(x, 2)`にする。
これはSD4で二つのnon-identity inclusionのcompositionを検査するための固定readingであり、
primary weak / strong判定と三point firingを置き換えない。

`weak/strong/rigidIdealSheaf`と対応するlocusは、
既存generic constructionへのtransparent accessorであり、それ自体を新しい数学的成果として数えない。
weak / strongの完了証拠は、global / chart / overlap上のpolynomial idealとの同一視、overlap一致、
strictness、nonzero / proper、kernel、zero locus、affine quotient comparison、
nonempty、non-isomorphismの各theoremである。rigid readingはglobal equation、top ideal、
properness、strongからのstrictness、nonempty、non-isomorphismで監査する。

### SD3 — actual test morphismsとfull correspondence

~~~lean
def evaluationRingHom (n : Int) :
    AmbientRing →+* Int :=
  MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => n)

@[simp] theorem evaluationRingHom_eq (n : Int) :
    evaluationRingHom n =
      MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => n) :=
  rfl

noncomputable def evaluationPoint (n : Int) :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  AlgebraicGeometry.Scheme.Spec.map
    (CommRingCat.ofHom (evaluationRingHom n)).op

@[simp] theorem evaluationPoint_eq (n : Int) :
    evaluationPoint n =
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom (evaluationRingHom n)).op :=
  rfl

noncomputable def zeroPoint :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  evaluationPoint 0

@[simp] theorem zeroPoint_eq :
    zeroPoint = evaluationPoint 0 :=
  rfl

noncomputable def onePoint :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  evaluationPoint 1

@[simp] theorem onePoint_eq :
    onePoint = evaluationPoint 1 :=
  rfl

noncomputable def twoPoint :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  evaluationPoint 2

@[simp] theorem twoPoint_eq :
    twoPoint = evaluationPoint 2 :=
  rfl

theorem weak_correspondence
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying) :
    (SemanticLawfulAlong referenceRaw referenceScheme weakReading s ↔
      WitnessVanishes referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s) ∧
    (WitnessVanishes referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s ↔
      IdealLawfulAlong referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s) ∧
    (IdealLawfulAlong referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
          weakReading weakReading_valid weakReading_requiredClosed s))

theorem strong_correspondence
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying) :
    (SemanticLawfulAlong referenceRaw referenceScheme strongReading s ↔
      WitnessVanishes referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s) ∧
    (WitnessVanishes referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s ↔
      IdealLawfulAlong referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s) ∧
    (IdealLawfulAlong referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
          strongReading strongReading_valid strongReading_requiredClosed s))

theorem zeroPoint_fires :
    SemanticLawfulAlong referenceRaw referenceScheme weakReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme strongReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed zeroPoint)

theorem onePoint_fires :
    SemanticLawfulAlong referenceRaw referenceScheme weakReading onePoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading onePoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed onePoint)

theorem twoPoint_fires :
    ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed twoPoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed twoPoint)
~~~

local accessorや別名を置かず、全statementに既存のcanonical predicate / factorization typeを
直接記載する。`weak_correspondence`と`strong_correspondence`は
`lawfulnessIdealFactorizationCorrespondence`を直接proof-useする。
三つのpoint firing theoremは、semantic計算を先に証明し、対応定理を用いて
witness、ideal、actual factorizationへ運ぶ。semantic predicateをideal vanishingで定義しない。

### SD4 — law inclusionとcontravariant closed geometry

~~~lean
def weakToStrongAtomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    AAT.AG.FiniteModel.carrier.Atom :=
  if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
    AAT.AG.FiniteModel.FiniteAtom.componentA
  else
    AAT.AG.FiniteModel.FiniteAtom.componentC

@[simp] theorem weakToStrongAtomMap_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    weakToStrongAtomMap a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        AAT.AG.FiniteModel.FiniteAtom.componentA
      else
        AAT.AG.FiniteModel.FiniteAtom.componentC :=
  rfl

def weakToStrong :
    ClosedEquationalLawInclusion
      referenceRaw referenceScheme weakReading strongReading

@[simp] theorem weakToStrong_lawMap :
    weakToStrong.lawMap = id

@[simp] theorem weakToStrong_atomMap :
    weakToStrong.atomMap PUnit.unit = weakToStrongAtomMap

theorem weakToStrong_valid :
    IsClosedEquationalLawInclusion
      referenceRaw referenceScheme weakToStrong

noncomputable def lawComparison :
    strongLocus ⟶ weakLocus :=
  lawfulClosedSubschemeMap
    referenceRaw referenceScheme
    weakReading_valid strongReading_valid
    weakReading_requiredClosed strongReading_requiredClosed
    weakToStrong weakToStrong_valid

@[simp] theorem lawComparison_eq :
    lawComparison =
      lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        weakReading_valid strongReading_valid
        weakReading_requiredClosed strongReading_requiredClosed
        weakToStrong weakToStrong_valid :=
  rfl

theorem lawComparison_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion lawComparison

theorem lawComparison_immersion :
    lawComparison ≫ weakImmersion = strongImmersion

theorem lawComparison_not_isIso :
    ¬ IsIso lawComparison

def strongToRigidAtomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    AAT.AG.FiniteModel.carrier.Atom :=
  if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
    AAT.AG.FiniteModel.FiniteAtom.componentA
  else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
    AAT.AG.FiniteModel.FiniteAtom.componentB
  else
    AAT.AG.FiniteModel.FiniteAtom.dependsAB

@[simp] theorem strongToRigidAtomMap_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    strongToRigidAtomMap a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        AAT.AG.FiniteModel.FiniteAtom.componentA
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        AAT.AG.FiniteModel.FiniteAtom.componentB
      else
        AAT.AG.FiniteModel.FiniteAtom.dependsAB :=
  rfl

def strongToRigid :
    ClosedEquationalLawInclusion
      referenceRaw referenceScheme strongReading rigidReading

@[simp] theorem strongToRigid_lawMap :
    strongToRigid.lawMap = id

@[simp] theorem strongToRigid_atomMap :
    strongToRigid.atomMap PUnit.unit = strongToRigidAtomMap

theorem strongToRigid_valid :
    IsClosedEquationalLawInclusion
      referenceRaw referenceScheme strongToRigid

noncomputable def strongToRigidComparison :
    rigidLocus ⟶ strongLocus :=
  lawfulClosedSubschemeMap
    referenceRaw referenceScheme
    strongReading_valid rigidReading_valid
    strongReading_requiredClosed rigidReading_requiredClosed
    strongToRigid strongToRigid_valid

@[simp] theorem strongToRigidComparison_eq :
    strongToRigidComparison =
      lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        strongReading_valid rigidReading_valid
        strongReading_requiredClosed rigidReading_requiredClosed
        strongToRigid strongToRigid_valid :=
  rfl

theorem strongToRigidComparison_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion strongToRigidComparison

theorem strongToRigidComparison_immersion :
    strongToRigidComparison ≫ strongImmersion = rigidImmersion

theorem strongToRigidComparison_not_isIso :
    ¬ IsIso strongToRigidComparison

def weakToRigid :
    ClosedEquationalLawInclusion
      referenceRaw referenceScheme weakReading rigidReading :=
  weakToStrong.comp referenceRaw referenceScheme strongToRigid

@[simp] theorem weakToRigid_eq :
    weakToRigid =
      weakToStrong.comp referenceRaw referenceScheme strongToRigid :=
  rfl

theorem weakToRigid_valid :
    IsClosedEquationalLawInclusion
      referenceRaw referenceScheme weakToRigid :=
  ClosedEquationalLawInclusion.comp_valid
    referenceRaw referenceScheme weakToStrong strongToRigid
    weakToStrong_valid strongToRigid_valid

noncomputable def weakToRigidComparison :
    rigidLocus ⟶ weakLocus :=
  lawfulClosedSubschemeMap
    referenceRaw referenceScheme
    weakReading_valid rigidReading_valid
    weakReading_requiredClosed rigidReading_requiredClosed
    weakToRigid weakToRigid_valid

@[simp] theorem weakToRigidComparison_eq :
    weakToRigidComparison =
      lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        weakReading_valid rigidReading_valid
        weakReading_requiredClosed rigidReading_requiredClosed
        weakToRigid weakToRigid_valid :=
  rfl

theorem lawComparison_id_fires :
    lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        weakReading_valid weakReading_valid
        weakReading_requiredClosed weakReading_requiredClosed
        (ClosedEquationalLawInclusion.refl
          referenceRaw referenceScheme weakReading)
        (ClosedEquationalLawInclusion.refl_valid
          referenceRaw referenceScheme weakReading) =
      𝟙 weakLocus

theorem lawComparison_comp_fires :
    strongToRigidComparison ≫ lawComparison = weakToRigidComparison
~~~

strict ideal calculationと`lawComparison_not_isIso`により、law変更がlawful locusを
実際に縮めることを固定する。point-set inclusionだけを比較の完了証拠にしない。
`rigidReading`はcomposition proof-use専用の第三readingであり、global idealを`(x, 2)`へ固定する。
`strongIdeal_lt_rigidIdeal`、`strongToRigidComparison_not_isIso`により、
`lawComparison_comp_fires`の二つのlegはいずれもnon-isomorphismである。
RHSは`weakToStrong.comp strongToRigid`から構成したactual mapとして残し、
`lawfulClosedSubschemeMap_comp`を直接proof-useする。

### SD5 — flat coefficient change firing

このSDはmerged coefficient-change APIのconcrete firingであり、generic base-change定理を再定義しない。

~~~lean
noncomputable def coefficientChange :
    FlatCoefficientChange Int (Polynomial Int)

@[simp] theorem coefficientChange_hom :
    coefficientChange.hom = Polynomial.C

theorem coefficientChange_not_surjective :
    ¬ Function.Surjective coefficientChange.hom

noncomputable instance coefficientChange_hasSheafCompose :
    referenceSite.topology.HasSheafCompose
      (coefficientChange.coefficientExtension :
        AATCommAlgCat.{0, 0} Int ⥤
          AATCommAlgCat.{0, 0} (Polynomial Int))

noncomputable def coefficientChangedScheme :
    StandardArchitectureScheme
      (referenceRaw.baseChange coefficientChange.hom) :=
  referenceScheme.baseChange referenceRaw coefficientChange

@[simp] theorem coefficientChangedScheme_eq :
    coefficientChangedScheme =
      referenceScheme.baseChange referenceRaw coefficientChange :=
  rfl

noncomputable def coefficientChangedWeakReading :
    ClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore
    referenceRaw referenceScheme
    weakLawEquationCore weakSchemeBridge coefficientChange

@[simp] theorem coefficientChangedWeakReading_eq :
    coefficientChangedWeakReading =
      ClosedEquationalLawReading.baseChangeOfSemanticCore
        referenceRaw referenceScheme
        weakLawEquationCore weakSchemeBridge coefficientChange :=
  rfl

noncomputable def coefficientChangedStrongReading :
    ClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore
    referenceRaw referenceScheme
    strongLawEquationCore strongSchemeBridge coefficientChange

@[simp] theorem coefficientChangedStrongReading_eq :
    coefficientChangedStrongReading =
      ClosedEquationalLawReading.baseChangeOfSemanticCore
        referenceRaw referenceScheme
        strongLawEquationCore strongSchemeBridge coefficientChange :=
  rfl

theorem coefficientChangedWeakReading_valid :
    IsClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakReading

theorem coefficientChangedStrongReading_valid :
    IsClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading

theorem coefficientChangedWeakReading_requiredClosed :
    RequiredClosed
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakReading

theorem coefficientChangedStrongReading_requiredClosed :
    RequiredClosed
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading

theorem weakIdeal_baseChange :
    Scheme.IdealSheafData.comap weakIdealSheaf
        (referenceScheme.baseChangeMap
          referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed

theorem strongIdeal_baseChange :
    Scheme.IdealSheafData.comap strongIdealSheaf
        (referenceScheme.baseChangeMap
          referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed

theorem leftChart_baseChange_isPullback :
    IsPullback
      ((referenceScheme.baseChangedAtlas
          referenceRaw coefficientChange).chart
        (cast
          (referenceScheme.baseChangedAtlas_Index
            referenceRaw coefficientChange).symm leftIndex)).map
      (referenceScheme.baseChangedChartMap
        referenceRaw coefficientChange leftIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart leftIndex).map

theorem rightChart_baseChange_isPullback :
    IsPullback
      ((referenceScheme.baseChangedAtlas
          referenceRaw coefficientChange).chart
        (cast
          (referenceScheme.baseChangedAtlas_Index
            referenceRaw coefficientChange).symm rightIndex)).map
      (referenceScheme.baseChangedChartMap
        referenceRaw coefficientChange rightIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart rightIndex).map

theorem coefficientChanged_ideal_strict :
    lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed <
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed

def coefficientChangedWeakToStrong :
    ClosedEquationalLawInclusion
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme
      coefficientChangedWeakReading
      coefficientChangedStrongReading where
  lawMap := weakToStrong.lawMap
  atomMap := weakToStrong.atomMap

@[simp] theorem coefficientChangedWeakToStrong_lawMap :
    coefficientChangedWeakToStrong.lawMap = weakToStrong.lawMap :=
  rfl

@[simp] theorem coefficientChangedWeakToStrong_atomMap :
    coefficientChangedWeakToStrong.atomMap = weakToStrong.atomMap :=
  rfl

theorem coefficientChangedWeakToStrong_valid :
    IsClosedEquationalLawInclusion
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakToStrong

noncomputable def coefficientChangedLawComparison :
    lawfulClosedSubscheme
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed ⟶
      lawfulClosedSubscheme
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed :=
  lawfulClosedSubschemeMap
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme
    coefficientChangedWeakReading_valid
    coefficientChangedStrongReading_valid
    coefficientChangedWeakReading_requiredClosed
    coefficientChangedStrongReading_requiredClosed
    coefficientChangedWeakToStrong
    coefficientChangedWeakToStrong_valid

@[simp] theorem coefficientChangedLawComparison_eq :
    coefficientChangedLawComparison =
      lawfulClosedSubschemeMap
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading_valid
        coefficientChangedStrongReading_valid
        coefficientChangedWeakReading_requiredClosed
        coefficientChangedStrongReading_requiredClosed
        coefficientChangedWeakToStrong
        coefficientChangedWeakToStrong_valid :=
  rfl

theorem coefficientChangedLawComparison_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion
      coefficientChangedLawComparison

theorem coefficientChangedLawComparison_immersion :
    coefficientChangedLawComparison ≫
        lawfulClosedImmersion
          (referenceRaw.baseChange coefficientChange.hom)
          coefficientChangedScheme
          coefficientChangedWeakReading
          coefficientChangedWeakReading_valid
          coefficientChangedWeakReading_requiredClosed =
      lawfulClosedImmersion
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed

theorem coefficientChangedLawComparison_not_isIso :
    ¬ IsIso coefficientChangedLawComparison

theorem coefficient_law_comparison_square :
    coefficientChangedLawComparison ≫
        lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge coefficientChange =
      lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge coefficientChange ≫
        lawComparison

theorem coefficientChange_schemeMap_not_isIso :
    ¬ IsIso
      (referenceScheme.baseChangeMap
        referenceRaw coefficientChange)
~~~

`coefficient_law_comparison_square`は、このconcrete fixture上でlaw inclusionとcoefficient changeが
同じclosed-subscheme provenanceを保つことを固定する。新しいgeneral naturality theoremを
このPRDの成果へ追加しない。

### SD6 — negative fixtures

negative fixtureは単にproofを渡さない例ではなく、具体的な誤データと否定theoremを持つ。

~~~lean
noncomputable def duplicateLeftAtlas :
    ArchitectureAffineAtlas referenceRaw
      referenceScheme.underlying referenceScheme.decoration where
  Index := Bool
  chart _ := leftChart

@[simp] theorem duplicateLeftAtlas_chart (i : Bool) :
    duplicateLeftAtlas.chart i = leftChart :=
  rfl

theorem zeroPoint_not_factors_through_leftChart :
    ¬ ∃ lift : AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
        leftChart.domain,
      lift ≫ leftChart.map = zeroPoint

theorem duplicateLeftAtlas_not_valid :
    ¬ IsArchitectureAffineAtlas referenceRaw duplicateLeftAtlas

noncomputable def coordinateReflection :
    AmbientRing ≃+* AmbientRing

@[simp] theorem coordinateReflection_coordinate :
    coordinateReflection coordinate = rightGenerator

@[simp] theorem coordinateReflection_rightGenerator :
    coordinateReflection rightGenerator = coordinate

noncomputable def reflectedRightRingHom :
    AmbientRing →+* Localization.Away rightGenerator :=
  (algebraMap AmbientRing
    (Localization.Away rightGenerator)).comp
      coordinateReflection.toRingHom

@[simp] theorem reflectedRightRingHom_coordinate :
    reflectedRightRingHom coordinate =
      algebraMap AmbientRing
        (Localization.Away rightGenerator) rightGenerator

noncomputable def brokenRightChart :
    ArchitectureAffineChart referenceRaw
      referenceScheme.underlying referenceScheme.decoration where
  context := rightContext
  contextHom := rightToBase
  map :=
    rightChartDomainIso.hom ≫
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom reflectedRightRingHom).op

@[simp] theorem brokenRightChart_context :
    brokenRightChart.context = rightContext :=
  rfl

@[simp] theorem brokenRightChart_map :
    brokenRightChart.map =
      rightChartDomainIso.hom ≫
        AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom reflectedRightRingHom).op :=
  rfl

theorem brokenRightChart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion brokenRightChart.map

theorem brokenRightChart_interpretation_ne :
    sheafifiedRestriction referenceRaw brokenRightChart.contextHom ≠
      referenceScheme.decoration.interpretation ≫
        brokenRightChart.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing
            referenceRaw brokenRightChart.context)).hom

theorem brokenRightChart_not_valid :
    ¬ IsArchitectureAffineChart referenceRaw brokenRightChart

noncomputable def collapsedStrongReading :
    ClosedEquationalLawReading referenceRaw referenceScheme :=
  weakReading

@[simp] theorem collapsedStrongReading_eq :
    collapsedStrongReading = weakReading :=
  rfl

theorem collapsedIdeal_not_strict :
    ¬ lawGeneratedIdealSheaf
        referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed <
      lawGeneratedIdealSheaf
        referenceRaw referenceScheme
        collapsedStrongReading weakReading_valid weakReading_requiredClosed

noncomputable def unitIdealFixture :
    referenceScheme.underlying.IdealSheafData :=
  ⊤

@[simp] theorem unitIdealFixture_eq :
    unitIdealFixture = ⊤ :=
  rfl

theorem unitIdealFixture_subscheme_empty :
    IsEmpty unitIdealFixture.subscheme

noncomputable def nonFlatCoefficientMap :
    Int →+* ZMod 2 :=
  Int.castRingHom (ZMod 2)

@[simp] theorem nonFlatCoefficientMap_eq :
    nonFlatCoefficientMap = Int.castRingHom (ZMod 2) :=
  rfl

theorem nonFlatCoefficientMap_not_flat :
    ¬ nonFlatCoefficientMap.Flat
~~~

- `duplicateLeftAtlas`はIndexと両chartを固定して二chartを両方`D(x)`にし、
  `zeroPoint_not_factors_through_leftChart`により`D(1-x)`側で検出される点を覆わない。
- `brokenRightChart`はright contextを維持し、coordinate reflectionによりopen immersionを保ったまま
  `x`のinterpretationを`1-x`へ変える。`brokenRightChart_interpretation_ne`が唯一壊した
  chart-validity clauseを直接固定する。
- `collapsedStrongReading`はweak/strong equationを同一化し、strictnessを失う。
- `unitIdealFixture`はunit idealをnonempty lawful geometryの証拠にできないことを示す。
- `nonFlatCoefficientMap`はflatnessなしの係数変更をSD5へ流入させない。
- `twoPoint_fires`はsemantic、witness、ideal、factorizationの全層でnegativeを固定する。

### SD7 — integrated firing theorem

~~~lean
theorem standardGeometryReference_fires :
    Presheaf.IsSheaf referenceSite.topology referenceRaw.toPresheaf ∧
    (∀ W : referenceSite.category,
      IsIso (referenceRaw.toRingedSite.canonical.app (op W))) ∧
    (⨆ i,
          ((referenceScheme.affineOpenCover referenceRaw).f i).opensRange =
        ⊤) ∧
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart leftIndex).map ∧
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart rightIndex).map ∧
    ¬ IsIso (referenceScheme.atlas.chart leftIndex).map ∧
    ¬ IsIso (referenceScheme.atlas.chart rightIndex).map ∧
    Nonempty
      (referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex) ∧
    ¬ IsIso (sheafifiedRestriction referenceRaw leftToBase) ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (weakIdealSheaf.ideal ⊤) = weakAmbientIdeal ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ⊤) = strongAmbientIdeal ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (rigidIdealSheaf.ideal ⊤) = rigidAmbientIdeal ∧
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap leftChart.map).ideal ⊤) =
      weakLeftIdeal ∧
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap rightChart.map).ideal ⊤) =
      weakRightIdeal ∧
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal ⊤) =
      weakOverlapIdeal ∧
    (weakIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (weakIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) ∧
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap leftChart.map).ideal ⊤) =
      strongLeftIdeal ∧
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap rightChart.map).ideal ⊤) =
      strongRightIdeal ∧
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal ⊤) =
      strongOverlapIdeal ∧
    (strongIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (strongIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) ∧
    weakAmbientIdeal ≠ ⊥ ∧ weakAmbientIdeal ≠ ⊤ ∧
    strongAmbientIdeal ≠ ⊥ ∧ strongAmbientIdeal ≠ ⊤ ∧
    weakIdealSheaf < strongIdealSheaf ∧
    rigidAmbientIdeal ≠ ⊥ ∧ rigidAmbientIdeal ≠ ⊤ ∧
    strongIdealSheaf < rigidIdealSheaf ∧
    weakImmersion.ker = weakIdealSheaf ∧
    strongImmersion.ker = strongIdealSheaf ∧
    Set.range weakImmersion = weakIdealSheaf.support ∧
    Set.range strongImmersion = strongIdealSheaf.support ∧
    IsIso weakAffineQuotientChart ∧
    IsIso strongAffineQuotientChart ∧
    Nonempty weakLocus ∧
    Nonempty strongLocus ∧
    Nonempty rigidLocus ∧
    ¬ IsIso weakImmersion ∧
    ¬ IsIso strongImmersion ∧
    ¬ IsIso rigidImmersion ∧
    SemanticLawfulAlong referenceRaw referenceScheme weakReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme strongReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme weakReading onePoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading onePoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed twoPoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed twoPoint) ∧
    AlgebraicGeometry.IsClosedImmersion lawComparison ∧
    lawComparison ≫ weakImmersion = strongImmersion ∧
    ¬ IsIso lawComparison ∧
    AlgebraicGeometry.IsClosedImmersion strongToRigidComparison ∧
    strongToRigidComparison ≫ strongImmersion = rigidImmersion ∧
    ¬ IsIso strongToRigidComparison ∧
    strongToRigidComparison ≫ lawComparison = weakToRigidComparison ∧
    ¬ Function.Surjective coefficientChange.hom ∧
    IsPullback
      ((referenceScheme.baseChangedAtlas
          referenceRaw coefficientChange).chart
        (cast
          (referenceScheme.baseChangedAtlas_Index
            referenceRaw coefficientChange).symm leftIndex)).map
      (referenceScheme.baseChangedChartMap
        referenceRaw coefficientChange leftIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart leftIndex).map ∧
    IsPullback
      ((referenceScheme.baseChangedAtlas
          referenceRaw coefficientChange).chart
        (cast
          (referenceScheme.baseChangedAtlas_Index
            referenceRaw coefficientChange).symm rightIndex)).map
      (referenceScheme.baseChangedChartMap
        referenceRaw coefficientChange rightIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart rightIndex).map ∧
    Scheme.IdealSheafData.comap weakIdealSheaf
        (referenceScheme.baseChangeMap
          referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed ∧
    Scheme.IdealSheafData.comap strongIdealSheaf
        (referenceScheme.baseChangeMap
          referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed ∧
    lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed <
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed ∧
    AlgebraicGeometry.IsClosedImmersion
      coefficientChangedLawComparison ∧
    coefficientChangedWeakToStrong.lawMap = weakToStrong.lawMap ∧
    coefficientChangedWeakToStrong.atomMap = weakToStrong.atomMap ∧
    ¬ IsIso coefficientChangedLawComparison ∧
    coefficientChangedLawComparison ≫
        lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge coefficientChange =
      lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge coefficientChange ≫
        lawComparison ∧
    ¬ IsIso
      (referenceScheme.baseChangeMap
        referenceRaw coefficientChange)
~~~

このtheoremはcomponent theoremから組み立てる回帰packageであり、各component contract、
各correspondence、各negative theoremの代替ではない。conjunction相当のstructureやcertificateを
新設してfield projectionだけで閉じない。

### SD8 — task data provenanceとmaterial premise分類

次のdefinitionは固定fixtureを選ぶtask dataであり、theoremのmaterial premiseではない。
数学本文がこれらの具体値を指定したとは扱わない。

| task data | provenance | fixed use |
| --- | --- | --- |
| `FiniteModel.corePackage`、`TwoPatchContextIndex`、`twoPatchContext` | merged Lean fixture | `referenceContextPreorder_le_iff`、`context_ctx`、`referenceSite` |
| `twoPatchCoverageRequirements`、`TwoPatchCoverIndex` | merged Lean fixture | `referenceCoverageRequirements_eq`、`referenceCoverIndexEquiv`、`referenceCover_patch`、`referenceCover_presieve` |
| `Int`、`MvPolynomial Unit Int`、`x`、`1-x` | 本PRDの固定値 | raw presentation、chart、law equation、evaluation |
| `x(x-1)`、`x`、constant `2`、evaluation `0/1/2` | 本PRDの固定値 | weak / strong / rigid witness、ideal、point firing、non-identity inclusion composition |
| `Int → Polynomial Int`と`Int → ZMod 2` | 本PRDのpositive / negative係数変更 | SD5 / SD6 |

本reference modelのpublic targetは外部のmathematical certificateを引数に持たない。
generic APIが要求するstructure fieldとtypeclassは、次の通りすべて対象dataから放電する。
分類語はLean品質基準の三分類だけを使う。

| material premise | 分類 | 放電宣言 / construction | proof-use |
| --- | --- | --- | --- |
| context preorderのrefl / trans / readable morphism | 放電済み | `referenceContextPreorder`、`referenceContextPreorder_le_iff` | `referenceSite`、全restriction |
| selected overlapのpullback fields | 放電済み | `referenceOverlap`、`referenceOverlap_selected` | pair context、cover admissibility、actual overlap presentation |
| selected cover admissibility | 放電済み | `referenceCoverageRequirements_eq`、`referenceCover_presieve` | `referenceCover_topologyCover` |
| `HasSheafify referenceSite.topology (AATCommAlgCat Int)` | 放電済み | `referenceSite_hasSheafifyInt` | `SheafifiedSectionRing`、`sheafifiedRestriction`、`StandardArchitectureScheme` |
| raw structural relations | 放電済み | `ReferenceRawCoordinate`、`referenceCoordinateFamily`、`referenceRelationFamily`、`base_JStruct_eq`、`left_JStruct_eq`、`right_JStruct_eq`、`overlap_JStruct_eq` | 四`RawAlgebraIso`と`rawCoordinate_restrict` |
| raw restriction stability | 放電済み | `referenceTypedRestriction_variableImage`と`referenceTypedRestriction_maps_JStruct` | `referenceRestrictionStable`、`referenceRestrictionStable_identity`、`referenceRestrictionStable_comp` |
| raw presheafのsheaf condition | 放電済み | finite two-patch matching-family calculation | `referenceRaw_isSheaf`、`canonical_component_isIso` |
| localization comparison | 放電済み | `left/rightGenerator_dvd_overlap`、`left/rightGenerator_isUnit_on_overlap`、Mathlib `IsLocalization.Away.lift`、二`*comp_algebraMap` | 四section-ring iso、四restriction equation、local ideal equation |
| atlas validity | 放電済み | Mathlib principal-open APIと`x + (1-x) = 1` | `referenceAtlas_valid`、`left/right_chart_isOpenImmersion`、`twoChart_jointlyCovers` |
| overlap presentation validity | 放電済み | selected pair context、actual pullback、localization composition | `referenceOverlapPresentation_valid`、`actualOverlapIso`、ideal overlap一致、`actual_triple_cocycle` |
| source semantic equation bridge | 放電済み | 三coreのcanonical restriction equation、三identity `toRawPresentation` equation、`rawCoordinate_restrict`とglobal / local equation calculation | `weakSchemeBridge_valid`、`strongSchemeBridge_valid`、`rigidSchemeBridge_valid`、三つのglobal-equation theorem |
| source `IsClosedEquationalLawReading` | 放電済み | bridge validity、restriction自然性、selected law calculation | `weakReading_valid`、`strongReading_valid`、`rigidReading_valid` |
| source `RequiredClosed` | 放電済み | finite required-law calculation | `weakReading_requiredClosed`、`strongReading_requiredClosed`、`rigidReading_requiredClosed`をideal sheafとlocusへ実引数として渡す |
| source `RequiredLawIdealExact` | 放電済み | evaluationとprincipal ideal calculation | `weakReading_requiredLawIdealExact`、`strongReading_requiredLawIdealExact`、`rigidReading_requiredLawIdealExact`をcorrespondenceまたはstrictness証明へ実引数として渡す |
| source `IsClosedEquationalLawInclusion` | 放電済み | fixed law map、atom map、witness coordinate equality、semantic implication | `weakToStrong_valid`、`strongToRigid_valid`、`weakToRigid_valid`、identity / non-identity composition firing |
| flatness of `Int → Polynomial Int` | 放電済み | polynomial ringのfree module structure | `coefficientChange.flat` |
| `HasSheafify referenceSite.topology (AATCommAlgCat (Polynomial Int))` | 放電済み | `referenceSite_hasSheafifyPolynomialInt` | target raw / Scheme / readingのbase change |
| `HasSheafCompose` | 放電済み | `coefficientChange_hasSheafCompose`のnamed instance chain | scheme / reading / ideal base change |
| changed `IsClosedEquationalLawReading` | 放電済み | generic semantic-core base changeとsource bridge validity | `coefficientChangedWeakReading_valid`、`coefficientChangedStrongReading_valid` |
| changed `RequiredClosed` | 放電済み | generic required-closed base change | `coefficientChangedWeakReading_requiredClosed`、`coefficientChangedStrongReading_requiredClosed` |
| changed `IsClosedEquationalLawInclusion` | 放電済み | sourceの`lawMap` / `atomMap`をdefinitionally再利用し、changed witness equalityを計算 | `coefficientChangedWeakToStrong_valid`、`coefficientChangedLawComparison`、mixed square |

Scheme、ideal、factorization、strictness、nonemptyを自由入力、typeclass、opaque certificateとして
追加しない。最終レビューでは全new theoremの明示引数、typeclass、参照structure fieldを独立に棚卸しし、
この表と突合する。申告のないpremiseは`未放電`として扱う。完了には
`material_premise_ledger_delta = ∅`かつ`new_material_premise = ∅`を要求する。

### SD9 — firing matrix

完全なpublic target集合`T`は、SD0〜SD7のLean fenceにtop-levelで明示される全public
`abbrev` / `def` / named `instance` / `theorem` / `inductive`宣言の集合とする。
`ReferenceRawCoordinate`の自動生成declarationは別の`T`要素に数えず、三constructorの網羅性は
`referenceRawCoordinate_cases`で固定する。

`F`を`T`中の全`theorem`とnamed `instance`の集合、`C := T \ F`をconstructor / data support集合とする。
SD8はpremise表、SD9は`F`のpositive / negative proof-useと`C`のsupport宣言を読むfiring projectionであり、
新しいtarget集合ではない。table中の`weak/strong`、`left/right`、`*_eq`などのfamily表記は、
SD0〜SD7にある該当宣言をすべてexact nameへ展開して読む。各`F`要素は一つのlaneに属し、
一つのtheoremが同じlaneのpositiveとnegativeの両方を与えてよい。`C`要素はsupport名としてtableに現れ得るが、
そのbodyにACが具体値またはconstructor provenanceを要求する場合は、必ず`F`中のnamed theoremで固定する。

tracking Issueで`T`、`F`、`C`とfamily展開後のSD9をexact nameでmaterializeし、次を機械検査する。

~~~text
implementation_explicit_public_target_names = T
statement_contract_target_names = T
axiom_audit_theorem_names = theorem declarations in T
firing_matrix_proof_names = F
firing_matrix_support_names ⊆ C
T = F ∪ C
F ∩ C = ∅
~~~

展開後のSD9で`F`の欠落、`T`外の宣言名、lane未割当が一つでもあれば完了ではない。

| lane | positive declaration | negative declaration | 非退化条件 |
| --- | --- | --- | --- |
| site / cover | `referenceContextPreorder_le_iff`、`referenceCoverageRequirements_eq`、`referenceOverlap_selected`、`referenceSelectedGeometryReading_eq`、`referenceSite_eq`、二`referenceSite_hasSheafify*` instance、`context_ctx`、`context_hom_iff`、`referenceCoverIndexEquiv`、`referenceCover_patch`、`referenceCover_presieve`、`referenceCover_topologyCover` | — | selected reading / siteのconstructor provenance、exactly four selected contexts、exactly two patches、source / target sheafification discharge |
| raw presentation | `ambientRing_eq`、`coordinate_eq`、`left/right/overlapGenerator_eq`、二`coverGenerator_false/true`、`coverGenerator_span_eq_top`、`ReferenceRawCoordinate`、`referenceRawCoordinate_cases`、三`referenceCoordinateFamily_*`、`rawVariable_eq`、`rawX_eq`、`rawLeftInverse_eq`、`rawRightInverse_eq`、`left/rightInverseRelation_eq`、`leftIsInverted_iff`、`rightIsInverted_iff`、二`referenceRelationPolynomial_*`、二`referenceRelationFamily_*`、`leftIsInverted_left`、`leftIsInverted_overlap`、`rightIsInverted_right`、`rightIsInverted_overlap`、`referenceRaw_coordFamily`、`referenceRaw_relationFamily`、四`*_JStruct_eq`、`referenceTypedRestriction_variableImage`、`referenceTypedRestriction_maps_JStruct`、`referenceRestrictionStable_identity`、`referenceRestrictionStable_comp`、`referenceRaw_restrictionStable` | `leftIsInverted_base`、`leftIsInverted_right`、`rightIsInverted_base`、`rightIsInverted_left` | fixed polynomial body、coordinate / relation family body、inversion predicateの全入力characterizationとpositive / negative instance pair、exactly three variables、exactly two relations、全morphismのmapを固定 |
| raw / sheaf | `rawCoordinate_eq`、`rawCoordinate_restrict`、四`RawAlgebraIso_coordinate`、`referenceRaw_isSheaf`、`canonical_component_isIso`、四section-ring iso | — | 一つのquotient coordinate class、actual polynomial / localization ring |
| atlas | `ambientScheme_eq`、四`*ChartDomainIso_eq`、`ambientDecoration_eq`、`referenceScheme_eq`、`referenceScheme_underlying`、`leftIndex_ne_rightIndex`、`index_cases`、`left/right_chart_context`、`chart_contexts_ne`、`left/right_chart_map`、`referenceAtlas_valid`、`referenceOverlapPresentation_valid`、`left/right_chart_isOpenImmersion`、`twoChart_jointlyCovers`、`pair_context`、`actualOverlapIso_eq`、`actualOverlap_nonempty`、`decoration_overlap`、`actual_triple_cocycle` | `left/right_chart_not_isIso`、`duplicateLeftAtlas_chart`、`zeroPoint_not_factors_through_leftChart`、`duplicateLeftAtlas_not_valid`、`coordinateReflection_coordinate`、`coordinateReflection_rightGenerator`、`reflectedRightRingHom_coordinate`、`brokenRightChart_context`、`brokenRightChart_map`、`brokenRightChart_isOpenImmersion`、`brokenRightChart_interpretation_ne`、`brokenRightChart_not_valid` | actual constructor provenance、二つのproper principal open、非空overlap、decoration / cocycle、失敗原因を固定したnegative data |
| restriction | `leftGenerator_dvd_overlap`、`rightGenerator_dvd_overlap`、`leftGenerator_isUnit_on_overlap`、`rightGenerator_isUnit_on_overlap`、`left_restriction_is_localization`、`right_restriction_is_localization`、`leftToOverlapRingHom_comp_algebraMap`、`rightToOverlapRingHom_comp_algebraMap`、`overlap_left_restriction_is_localization`、`overlap_right_restriction_is_localization` | `left_restriction_not_isIso`、`right_restriction_not_isIso` | 四restrictionをcanonical localization mapへ同定し、properな二mapのnon-isoを固定 |
| equation provenance | 三`*LawEquationCore_observable`、三`*LawEquationCore_observableCommRing`、三`*LawEquationCore_restrict`、三`*ViolationWitness_eq`、三`*LawEquationCore_supportAtom`、三`*LawEquationCore_supportLawIndex`、三`*SchemeBridge_toRawPresentation`、三`*SchemeBridge_valid`、三`*Reading_eq`、三`*Reading_valid`、三`*Reading_requiredClosed`、三`*Reading_requiredLawIdealExact`、三`*GlobalEquation_eq` | — | semantic coreの全data-bearing fieldとidentity raw-presentation bridgeからreading、closedness、exactness、global equationまで個別放電 |
| ideal | 三`*IdealSheaf_eq`、四`*GlobalSectionsIso_eq`、`weak/strong/rigidAmbientIdeal_eq`、六local `weak/strong*Ideal_eq`、global / left / right / overlapの`weak/strongIdeal_*_eq`、`rigidIdeal_top_eq`、overlap一致、nonzero / proper、`weakIdeal_lt_strongIdeal`、`strongIdeal_lt_rigidIdeal` | `collapsedStrongReading_eq`、`collapsedIdeal_not_strict` | generic ideal-sheaf constructor、canonical global-section comparison、expected ideal body、localizes consistently、nonzero、proper、二段のstrict inclusion |
| closed geometry | 三`*Locus_eq`、三`*Immersion_eq`、kernel、zero locus、`ambientTopAffineOpen_obj`、affine quotient chart iso、`weakLocus_nonempty`、`strongLocus_nonempty`、`rigidLocus_nonempty`、`weakImmersion_not_isIso`、`strongImmersion_not_isIso`、`rigidImmersion_not_isIso` | `unitIdealFixture_eq`、`unitIdealFixture_subscheme_empty` | actual generic subscheme / immersion provenance、nonempty proper closed subschemes、quotient comparison |
| correspondence | `weak_correspondence`、`strong_correspondence` | — | canonical semantic / witness / ideal / factorization equivalenceを直接proof-use |
| point 0 | `evaluationRingHom_eq`、`evaluationPoint_eq`、`zeroPoint_eq`、`zeroPoint_fires` | — | fixed evaluation 0、weak / strongの全4層がpositive |
| point 1 | `onePoint_eq`、`onePoint_fires`のweak側 | 同theoremのstrong側 | fixed evaluation 1、law変更で判定とfactorizationが変化 |
| point 2 | `twoPoint_eq` | `twoPoint_fires` | fixed evaluation 2、weak / strongの全4層がnegative |
| law inclusion | `weakToStrongAtomMap_eq`、`weakToStrong_lawMap`、`weakToStrong_atomMap`、`strongToRigidAtomMap_eq`、`strongToRigid_lawMap`、`strongToRigid_atomMap`、`weakToStrong_valid`、`strongToRigid_valid`、`weakToRigid_eq`、`weakToRigid_valid`、三comparison `*_eq`、`lawComparison_isClosedImmersion`、`strongToRigidComparison_isClosedImmersion`、`lawComparison_immersion`、`strongToRigidComparison_immersion`、`lawComparison_id_fires`、`lawComparison_comp_fires` | `lawComparison_not_isIso`、`strongToRigidComparison_not_isIso` | 二つの全入力atom map、strict contravariant comparison、generic identity / non-identity composition proof-use |
| coefficient change | `coefficientChange_hom`、`coefficientChange_not_surjective`、`coefficientChange_hasSheafCompose`、`coefficientChangedScheme_eq`、`coefficientChangedWeak/StrongReading_eq`、二changed-reading validity、二changed `RequiredClosed`、`left/rightChart_baseChange_isPullback`、`weak/strongIdeal_baseChange`、`coefficientChanged_ideal_strict`、`coefficientChangedWeakToStrong_lawMap`、`coefficientChangedWeakToStrong_atomMap`、`coefficientChangedWeakToStrong_valid`、`coefficientChange_schemeMap_not_isIso` | `nonFlatCoefficientMap_eq`、`nonFlatCoefficientMap_not_flat` | non-surjective flat change、named sheaf-compose discharge、actual pullback、ideal transport、source inclusion mapの保存、changed strictness |
| mixed comparison | `coefficientChangedLawComparison_eq`、`coefficientChangedLawComparison_isClosedImmersion`、`coefficientChangedLawComparison_immersion`、`coefficient_law_comparison_square` | `coefficientChangedLawComparison_not_isIso` | canonical changed comparison、ambient triangle、law inclusionとcoefficient changeの可換性 |
| integrated | `standardGeometryReference_fires` | — | R7 / AC51に列挙した縦断conjunctをcomponent theoremだけから同時監査 |

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
- 現行Lean treeには、本PRDが固定するprincipal-open modelをraw coordinateから
  coefficient comparisonまで一件で接続したfixture、executable contract、audit entryがまだない。
  本PRDはその未実装surfaceをSD0〜SD7のpublic target、SD8のpremise表、
  SD9のfiring matrix、Module import contractで固定する。

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
- statement変更が必要なら実装を止め、PRD改訂へ戻す。

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
- [ ] AC2: statement contract正本が本PRDの`Statement Design`に一意化されている。
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
