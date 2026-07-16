# PRD: AAT Lean Reading Functoriality

- 作成: 2026-07-13
- 対象: `Formal/AG/ReadingFunctoriality/**`、core reading change、selected closed-law extension、
  coverage topology refinement、selected cover refinement、flat coefficient base change、
  comparison morphism、finite examples、aggregate、statement contracts、axiom audit
- 数学的正典:
  - `docs/aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md` — 原則10.6 `Change of Core Reading`
  - `docs/aat/algebraic_geometric_theory/part_2_architecture_geometry_sites_sheaves.md` — `5.3 Refinement`、`5.4 Base Change`、定義7.1〜7.2
  - `docs/aat/algebraic_geometric_theory/part_3_law_algebra_obstruction_ideal_lawful_locus.md` — 定義7.1 `Lawful Locus`、定義9.3 `Architecture Scheme`、定義10.2 `Ideal Restriction`
  - `docs/aat/algebraic_geometric_theory/part_4_obstruction_cohomology.md` — 定義2.2、原則2.3、原則2.5、定義3.1〜4.1
  - `docs/aat/algebraic_geometric_theory/part_8_measurement_theory.md` — 定義9.1、定理候補9.2 `Flat Base Change Stability for LawConflict`のaffine Tor-object formula
  - `docs/aat/algebraic_geometric_theory/appendix.md` — A.2〜A.2.1
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、
  `docs/aat/lean_quality_standard.md`
- tracking Issue: 未作成。Issue作成と依存登録が済むまで実行不可
- statement contract正本: 本PRDの`Statement Design`節
- executable contract: `Formal/AG/StatementContractsReadingFunctoriality.lean`。
  実装と同時に作成し、CIでelaborateする
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

次をすべて満たすまで、このPRDの実装を開始しない。

1. tracking Issueに対象main commit、SD0〜SD9のtarget inventory、material premise表、
   child Issue依存、各childのsource fileとfocused checkが登録されている。
2. `CoreReading`、`AATCorePackage.generate`、`AATCorePackage.algebra`、
   `SelectedGeometryReading.toAATSite`、`RawAmbientRestrictionSystem`、
   `StandardArchitectureScheme`がmerged済みで、対象main commit上のsignatureと
   SD0〜SD2の参照が一致している。
3. closed-equational geometryの実装がmerged済みで、少なくとも次の宣言が存在する。
   PRDやdocs-only PRのmergeはこの条件を満たさない。

   - `ClosedEquationalLawReading` / `IsClosedEquationalWitnessReading` /
     `IsClosedEquationalLawReading` / `RequiredClosed` / `AllLawsSelected`
   - `SemanticLawfulAlong` / `FullySemanticLawfulAlong`
   - `lawGeneratedIdealSheaf` / `allLawGeneratedIdealSheaf`
   - `lawfulClosedSubscheme` / `allLawfulClosedSubscheme`
   - `SemanticLawEquationSchemeBridge` / `IsSemanticLawEquationSchemeBridge`
   - `SemanticCoreIdealSheafRealized` / `semanticCoreIdealSheaf_realized`
   - `ClosedEquationalLawInclusion` / `IsClosedEquationalLawInclusion`
   - `ClosedEquationalLawInclusion.ext`
   - `ClosedEquationalLawInclusion.refl` / `refl_valid` / `comp` / `comp_valid`
   - `lawWitnessIdealSheaf_le`
   - `lawGeneratedIdealSheaf_mono` / `allLawGeneratedIdealSheaf_mono`
   - `semanticLawfulAlong_mono` / `fullySemanticLawfulAlong_mono`
   - `lawfulClosedSubschemeMap` / `lawfulClosedSubschemeMap_isClosedImmersion` /
     `lawfulClosedSubschemeMap_immersion` / `lawfulClosedSubschemeMap_id` /
     `lawfulClosedSubschemeMap_comp`
   - `allLawfulClosedSubschemeMap` / `allLawfulClosedSubschemeMap_isClosedImmersion` /
     `allLawfulClosedSubschemeMap_immersion` / `allLawfulClosedSubschemeMap_id` /
     `allLawfulClosedSubschemeMap_comp`
   - finite modelの`weakToStrong` / `weakToStrong_valid` /
     `weak_ideal_lt_strong` / `weakToStrongMap_not_isIso` /
     `weakToStrongAllMap_not_isIso` / `coordinateBrokenInclusion_not_valid`

4. closed-equational geometryのfinal implementation snapshotに対して、
   本PRDのlaw targetを再同期する。同じ`S : Site.AATSite A`、`k`、
   `[HasSheafify S.topology (AATCommAlgCat k)]`、`raw`、`X`を共有することを確認する。
   semantic comparisonはrequired / full all-lawの二系統、ideal / closed geometry comparisonは
   required / all-selectedの二系統として突合する。
5. Mathlibの次のactual APIを対象main commit上でfocused checkし、tracking Issueへ
   declaration名とimport pathを記録する。

   - `CategoryTheory.Sheaf.H`、`Sheaf.H'`
   - `cechComplexFunctor`の`HasFiniteProducts`要件（prior-art確認。fixed targetには直接使用しない）
   - `RingHom.Flat`とflat homのcomposition
   - `Scheme.IdealSheafData.comap`とidentity / composition
   - Scheme pullback、affine pullback、tensor product
   - `Under.pushout`、`CommRingCat.tensorProdIsoPushout`、flat homに対する
     `PreservesFiniteLimits (Under.pushout _)`
   - `GrothendieckTopology.HasSheafCompose`、`sheafifyComposeIso`、
     left-adjoint functorの`PreservesSheafification`
   - `CategoryTheory.Tor`と`Derived.Intersection.mathlibTor`
   - `ModuleCat.extendScalars`、flat extensionのfinite-limit preservation
   - `Sheaf.composeAndSheafify`、`presheafToSheaf`、
     `sheafificationAdjunction`、`sheafificationAdjunction_unit_app`
   - `CategoryTheory.GrothendieckTopology.pullback_stable`
   - `Presieve.isSheaf_of_le`、`Adjunction.leftAdjoint_preservesColimits`、
     `preservesFiniteLimits_presheafToSheaf`、
     `plusPlusSheafIsoPresheafToSheaf`、`preservesFiniteLimits_of_natIso`、
     `presheafToSheaf_additive`、`equivSmallModel`、
     `smallSheafificationAdjunction`
   - `forget₂ (ModuleCat R) AddCommGrpCat`と、そのsheaf condition保存
   - `HomologicalComplex.Hom.isoOfComponents` / `homologyMapIso`
   - `AddEquiv.ofBijective` / `AddEquiv.module`

6. topology changeとcoefficient changeのactual `Sheaf.H` comparison、
   affine Tor-object flat-base-changeのfixed signature、flat extensionが無限積と可換しない
   `CechCoefficientBaseChangeCompatible` negative modelを
   Lean scratch fileで型検査する。実装証明は不要だが、source / target、universe、
   required typeclassが曖昧な状態ではchild Issueを開始しない。
   coefficient routeでは、objectwise scalar extensionから
   raw quotientの`baseChangePresheafIso`を構成できること、finite siteで
   `HasSheafCompose`を放電して`sheafifyComposeIso`からsection-object scalar-extension isoと
   構成できること、Part 3の`semanticCoreIdealSheaf_realized`をideal comap equalityへ接続できること、
   `LinearObstructionSheaf.baseChange`、`baseChangeSectionMap`、
   module-valued sheafから`ObstructionSheaf`へのforget routeをcanonicalに構成できること、
   finite modelで`HasSheafify S.topology (ModuleCat R')`を与えるnamed instance chainまで確認する。
   topology routeでは`fineSheafificationAdjunction`のbody、加法性、有限極限保存、
   有限余極限保存の三instanceをactual proof termで確認する。
   特に有限極限保存は`LeftExact`のplus construction、
   `plusPlusSheafIsoPresheafToSheaf`、必要ならsmall-site equivalenceを用いる必須child targetとし、
   `sheafHMap`へ`PreservesFiniteLimits`を新しい引数として追加して回避しない。

## Module import contract

新規moduleと直接importを次で固定する。循環依存が必要になった場合は停止し、tracking Issueで
SDとmodule DAGを再承認する。

| module | 直接importする既存module | 責務 |
| --- | --- | --- |
| `Formal.AG.ReadingFunctoriality.Core` | `Formal.AG.Atom.AATCore`、`Formal.AG.Site.Geometry`、`Formal.AG.LawAlgebra.StructureSheaf`、`Mathlib.Logic.Equiv.Defs` | `ReadingCore`、exact / positive core change、`ObjectAlgebraHom` |
| `Formal.AG.ReadingFunctoriality.Coverage` | `Formal.AG.ReadingFunctoriality.Core`、`Formal.AG.Site.FinitePosetGeometry`、`Formal.AG.Cohomology.CechComplex`、`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`、`Mathlib.CategoryTheory.Sites.Limits`、`Mathlib.CategoryTheory.Sites.LeftExact`、`Mathlib.CategoryTheory.Sites.Abelian`、`Mathlib.CategoryTheory.Sites.Equivalence`、`Mathlib.CategoryTheory.Adjunction.Restrict`、`Mathlib.CategoryTheory.Adjunction.Limits`、`Mathlib.Algebra.Category.Grp.FilteredColimits`、`Mathlib.Algebra.Homology.DerivedCategory.Ext.Map` | topology refinement、canonical tuple cover、selected cover refinement、one-way cochain hom、actual `Sheaf.H` / `Sheaf.H'` comparison |
| `Formal.AG.ReadingFunctoriality.Coefficient` | `Formal.AG.ReadingFunctoriality.Core`、`Formal.AG.ReadingFunctoriality.Coverage`、`Formal.AG.LawAlgebra.ClosedEquationalGeometry`、`Formal.AG.Derived.Intersection`、`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`、`Mathlib.Algebra.Category.ModuleCat.Descent`、`Mathlib.Algebra.Category.ModuleCat.Sheaf`、`Mathlib.Algebra.Category.Ring.Under.Basic`、`Mathlib.Algebra.Category.Ring.Under.Limits`、`Mathlib.Algebra.Module.TransferInstance`、`Mathlib.CategoryTheory.Sites.Adjunction`、`Mathlib.CategoryTheory.Sites.PreservesSheafification`、`Mathlib.CategoryTheory.Sites.Whiskering`、`Mathlib.AlgebraicGeometry.Pullbacks`、`Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`、`Mathlib.RingTheory.RingHom.Flat` | closed-equational geometry宣言のdirect reuse、raw quotient / sheafification scalar-extension comparison、scheme / ideal / Tor / linear Čech scalar extension / actual sheaf H coefficient change |
| `Formal.AG.ReadingFunctoriality.FiniteExamples` | `Formal.AG.ReadingFunctoriality.Core`、`Formal.AG.ReadingFunctoriality.Coverage`、`Formal.AG.ReadingFunctoriality.Coefficient`、`Formal.AG.Examples.FiniteModel`、`Formal.AG.LawAlgebra.ClosedEquationalGeometryFiniteExample` | SD9のpositive / negative firing |
| `Formal.AG.ReadingFunctoriality` | `Formal.AG.ReadingFunctoriality.Core`、`Formal.AG.ReadingFunctoriality.Coverage`、`Formal.AG.ReadingFunctoriality.Coefficient`、`Formal.AG.ReadingFunctoriality.FiniteExamples` | public aggregate |
| `Formal.AG.StatementContractsReadingFunctoriality` | `Formal.AG.ReadingFunctoriality`、`Formal.AG.ReadingFunctoriality.FiniteExamples` | SD0〜SD9のexact signature突合だけ |
| `Formal.AG` | `Formal.AG.ReadingFunctoriality` | repository AAT aggregate |
| `Formal.AG.StatementContracts` | `Formal.AG.StatementContractsReadingFunctoriality` | executable contract aggregate |
| `Formal.AG.AxiomAudit` | `Formal.AG.ReadingFunctoriality`、`Formal.AG.StatementContractsReadingFunctoriality` | new public theoremとfiring declarationのaxiom audit |

`Formal/AG`から`research/lean/ResearchLean`をimportしない。

## Statement Design

この節は本PRDのstatement contract正本である。実装開始後にtarget名、仮定、結論、量化対象、
参照definitionのsignatureを変更しない。実装状態は記録しない。
`StatementContractsReadingFunctoriality.lean`は
`example : <fixed type> := <implementation>`の形で全targetを直接突合する。
別のMarkdown contractは作成しない。

以下のLean blockは、特記しない限り
`namespace AAT.AG`、
`open CategoryTheory Opposite`、
`open AlgebraicGeometry`、
`open scoped AlgebraicGeometry`、
`universe u v w x`の下で読む。
既存APIを拡張するblockは`Cohomology`、`LawAlgebra`、`Derived.Intersection`など
既存の完全namespaceをこの位置から再開する。新しい入れ子namespaceへ同名APIを複製しない。

### 固定対象

このPRDは四つのchangeを分ける。

1. exact / positive core reading change
2. 同一`raw`・同一`X`・同一`S.lawUniverse`上のselected closed-law extension
3. 同一context category上のcoverage topology refinementと、その下のselected cover refinement
4. 同一Atom/site dataを保つcoefficient ringのflat base change

一つの万能`ReadingHom`は作らない。mixed-change coherenceも作らない。
異なるlaw universeを持つ二つのstandard geometry間のclosed-subscheme comparisonは、
SD1のcore changeだけからは完了したと数えない。

### SD0 — ReadingCoreとoptional selection

`ReadingCore`はAppendix A.2の`p = (r,J,k)`を既存generated APIへ接続する。
scheme、ideal、cohomology class、comparison mapをfieldに持たない。
`raw`はcoefficient-awareなprimitive reading dataとして保持する。

~~~lean
structure ReadingCore (U : AtomCarrier.{u}) where
  core : AATCorePackage U
  geometry : Site.SelectedGeometryReading core
  Coefficient : Type v
  coefficientCommRing : CommRing Coefficient
  raw :
    let _ := coefficientCommRing
    LawAlgebra.RawAmbientRestrictionSystem
      geometry.toAATSite Coefficient

attribute [instance] ReadingCore.coefficientCommRing

namespace ReadingCore

abbrev site (p : ReadingCore.{u, v} U) : Site.AATSite p.core.object :=
  p.geometry.toAATSite

abbrev lawUniverse (p : ReadingCore.{u, v} U) : LawUniverse U :=
  p.site.lawUniverse

abbrev signature (p : ReadingCore.{u, v} U) : ArchitectureSignature U :=
  p.site.signature

@[ext] theorem ext
    {p q : ReadingCore.{u, v} U}
    (hcore : p.core = q.core)
    (hgeometry : HEq p.geometry q.geometry)
    (hCoefficient : p.Coefficient = q.Coefficient)
    (hraw : HEq p.raw q.raw) :
    p = q

end ReadingCore

structure ReadingSelection (p : ReadingCore.{u, v} U) where
  selectedWitness : p.lawUniverse.witnessFamily.Witness → Prop
  selectedCircuit : FiniteCircuitDatum U → Prop
  selectedAxis : p.signature.Axis → Prop

@[ext] theorem ReadingSelection.ext
    {p : ReadingCore.{u, v} U}
    {s t : ReadingSelection p}
    (hwitness : s.selectedWitness = t.selectedWitness)
    (hcircuit : s.selectedCircuit = t.selectedCircuit)
    (haxis : s.selectedAxis = t.selectedAxis) :
    s = t
~~~

`rho`、representation family、profile / repair orderは、それぞれ係数sheaf、representation、
measurement moduleでtypedになった時点の別packageに置く。`ReadingSelection`へ
型だけを置いた仮フィールドを追加しない。

### SD1 — exact signed core change、positive core change、ObjectAlgebraHom

`SignedExactCoreReadingHom`は同一Atom carrier上の二つのgenerated coreを比較するprimitive dataである。
completed `ObjectAlgebraHom`をfieldに持たない。`PositiveCoreReadingHom`はpositive circuitだけを運び、
negative queryのtransportを結論にしない。

~~~lean
def AtomFamily.transport
    (f : U.Atom → U.Atom)
    (F : AtomFamily U) :
    AtomFamily U where
  mem target := ∃ source, F.mem source ∧ f source = target

theorem AtomFamily.ListFinite.transport
    {F : AtomFamily U}
    (hF : F.ListFinite)
    (f : U.Atom → U.Atom) :
    (F.transport f).ListFinite

def AtomConfiguration.transport
    (f : U.Atom → U.Atom)
    (C : AtomConfiguration U) :
    AtomConfiguration U where
  family := C.family.transport f
  relation target₁ target₂ :=
    ∃ source₁ source₂,
      C.relation source₁ source₂ ∧
        f source₁ = target₁ ∧ f source₂ = target₂
  identification target₁ target₂ :=
    ∃ source₁ source₂,
      C.identification source₁ source₂ ∧
        f source₁ = target₁ ∧ f source₂ = target₂

def AtomConfiguration.transportHom
    (f : U.Atom → U.Atom)
    (C : AtomConfiguration U) :
    ConfigurationHom C (C.transport f)

@[simp] theorem AtomConfiguration.transportHom_atomMap
    (f : U.Atom → U.Atom)
    (C : AtomConfiguration U) :
    (AtomConfiguration.transportHom f C).atomMap = f

def Invariant.TransportedAlong
    (I J : Invariant U)
    {ι : Type w}
    (source target : ι → ArchitectureObject U) : Prop :=
  match I, J with
  | .function I, .function J =>
      ∃ e : I.Value ≃ J.Value,
        ∀ A, e (I.evaluate (source A)) = J.evaluate (target A)
  | .predicate I, .predicate J =>
      ∀ A, I.holds (source A) ↔ J.holds (target A)
  | _, _ => False

theorem Invariant.function_predicate_not_transportedAlong
    (I : FunctionInvariant U) (J : PredicateInvariant U)
    {ι : Type w}
    (source target : ι → ArchitectureObject U) :
    ¬ Invariant.TransportedAlong (.function I) (.predicate J) source target

theorem Invariant.transportedAlong_refl
    (I : Invariant U)
    {ι : Type w}
    (source : ι → ArchitectureObject U) :
    Invariant.TransportedAlong I I source source

structure ObjectAlgebraHom
    (K L : ObjectAlgebra U) where
  objMap : K.Obj → L.Obj
  configurationMap :
    ∀ A, ConfigurationHom (K.object A).configuration
      (L.object (objMap A)).configuration
  lawMap :
    K.lawReading.lawUniverse.Index →
      L.lawReading.lawUniverse.Index
  required_iff :
    ∀ i,
      K.lawReading.lawUniverse.Required i ↔
        L.lawReading.lawUniverse.Required (lawMap i)
  law_holds_iff :
    ∀ i A,
      (K.lawReading.lawUniverse.law i).holds (K.object A) ↔
        (L.lawReading.lawUniverse.law (lawMap i)).holds
          (L.object (objMap A))
  circuitMap :
    ∀ A i, K.Circuit A i →
      L.Circuit (objMap A) (lawMap i)
  operationMap :
    ∀ {A B}, K.Op A B → L.Op (objMap A) (objMap B)
  operation_naturality :
    ∀ {A B} (op : K.Op A B),
      ConfigurationHom.comp
          (L.configurationMap (operationMap op))
          (configurationMap A) =
        ConfigurationHom.comp
          (configurationMap B)
          (K.configurationMap op)
  invariantMap :
    K.invariantReading.Index → L.invariantReading.Index
  invariant_transport :
    ∀ i,
      Invariant.TransportedAlong
        (K.invariantReading.invariant i)
        (L.invariantReading.invariant (invariantMap i))
        K.object (fun A => L.object (objMap A))
  axisMap :
    K.signatureReading.Axis → L.signatureReading.Axis
  coordinateEquiv :
    ∀ i,
      K.signatureReading.Coordinate i ≃
        L.signatureReading.Coordinate (axisMap i)
  axis_selected_iff :
    ∀ i,
      K.signatureReading.selected i ↔
        L.signatureReading.selected (axisMap i)
  coordinate_eq :
    ∀ A i,
      coordinateEquiv i
          (K.signatureReading.coordinate (K.object A) i) =
        L.signatureReading.coordinate
          (L.object (objMap A)) (axisMap i)

namespace ObjectAlgebraHom

@[ext] theorem ext
    {K L : ObjectAlgebra U}
    {f g : ObjectAlgebraHom K L}
    (hobj : f.objMap = g.objMap)
    (hconfiguration : HEq f.configurationMap g.configurationMap)
    (hlaw : HEq f.lawMap g.lawMap)
    (hcircuit : HEq f.circuitMap g.circuitMap)
    (hoperation : HEq f.operationMap g.operationMap)
    (hinvariant : HEq f.invariantMap g.invariantMap)
    (haxis : HEq f.axisMap g.axisMap)
    (hcoordinate : HEq f.coordinateEquiv g.coordinateEquiv) :
    f = g

def id (K : ObjectAlgebra U) : ObjectAlgebraHom K K

def comp
    {K L M : ObjectAlgebra U}
    (f : ObjectAlgebraHom K L)
    (g : ObjectAlgebraHom L M) :
    ObjectAlgebraHom K M

@[simp] theorem id_objMap (K : ObjectAlgebra U) :
    (id K).objMap = id

@[simp] theorem comp_objMap
    {K L M : ObjectAlgebra U}
    (f : ObjectAlgebraHom K L)
    (g : ObjectAlgebraHom L M) :
    (f.comp g).objMap = g.objMap ∘ f.objMap

end ObjectAlgebraHom

structure SignedExactCoreReadingHom
    (P Q : AATCorePackage U) where
  atomMap : U.Atom → U.Atom
  extraction_eq :
    Q.family = P.family.transport atomMap
  composition_eq :
    ∀ (F : AtomFamily U) (hF : F.ListFinite),
      Q.reading.composition.compose
          (F.transport atomMap) (hF.transport atomMap) =
        (P.reading.composition.compose F hF).transport atomMap
  objectMap : ArchitectureObject U → ArchitectureObject U
  object_formation_eq :
    ∀ C,
      objectMap (P.reading.objectReading.object C) =
        Q.reading.objectReading.object (C.transport atomMap)
  configurationMap :
    ∀ A, ConfigurationHom A.configuration (objectMap A).configuration
  configurationMap_atomMap :
    ∀ A, (configurationMap A).atomMap = atomMap
  lawMap :
    P.algebra.lawReading.lawUniverse.Index →
      Q.algebra.lawReading.lawUniverse.Index
  required_iff :
    ∀ i,
      P.algebra.lawReading.lawUniverse.Required i ↔
        Q.algebra.lawReading.lawUniverse.Required (lawMap i)
  law_holds_iff :
    ∀ i A,
      (P.algebra.lawReading.lawUniverse.law i).holds A ↔
        (Q.algebra.lawReading.lawUniverse.law (lawMap i)).holds
          (objectMap A)
  queryMap : FiniteCircuitDatum U → FiniteCircuitDatum U
  matches_iff :
    ∀ Qry A, Qry.Matches A ↔ (queryMap Qry).Matches (objectMap A)
  accepts_iff :
    ∀ i Qry,
      P.algebra.lawReading.circuits.accepts i Qry = true ↔
        Q.algebra.lawReading.circuits.accepts
          (lawMap i) (queryMap Qry) = true
  operationMap :
    ∀ {A B},
      P.reading.operationReading.Op A B →
        Q.reading.operationReading.Op (objectMap A) (objectMap B)
  operation_naturality :
    ∀ {A B} (op : P.reading.operationReading.Op A B),
      ConfigurationHom.comp
          (Q.reading.operationReading.configurationMap (operationMap op))
          (configurationMap A) =
        ConfigurationHom.comp
          (configurationMap B)
          (P.reading.operationReading.configurationMap op)
  invariantMap :
    P.reading.invariantReading.Index →
      Q.reading.invariantReading.Index
  invariant_transport :
    ∀ i,
      Invariant.TransportedAlong
        (P.reading.invariantReading.invariant i)
        (Q.reading.invariantReading.invariant (invariantMap i))
        id objectMap
  axisMap :
    P.reading.signatureReading.Axis →
      Q.reading.signatureReading.Axis
  coordinateEquiv :
    ∀ i,
      P.reading.signatureReading.Coordinate i ≃
        Q.reading.signatureReading.Coordinate (axisMap i)
  axis_selected_iff :
    ∀ i,
      P.reading.signatureReading.selected i ↔
        Q.reading.signatureReading.selected (axisMap i)
  coordinate_eq :
    ∀ A i,
      coordinateEquiv i
          (P.reading.signatureReading.coordinate A i) =
        Q.reading.signatureReading.coordinate
          (objectMap A) (axisMap i)

namespace SignedExactCoreReadingHom

@[ext] theorem ext
    {P Q : AATCorePackage U}
    {f g : SignedExactCoreReadingHom P Q}
    (hatom : f.atomMap = g.atomMap)
    (hobject : f.objectMap = g.objectMap)
    (hlaw : HEq f.lawMap g.lawMap)
    (hquery : HEq f.queryMap g.queryMap)
    (hoperation : HEq f.operationMap g.operationMap)
    (hinvariant : HEq f.invariantMap g.invariantMap)
    (haxis : HEq f.axisMap g.axisMap)
    (hcoordinate : HEq f.coordinateEquiv g.coordinateEquiv) :
    f = g

def refl (P : AATCorePackage U) :
    SignedExactCoreReadingHom P P

def comp
    {P Q R : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    (g : SignedExactCoreReadingHom Q R) :
    SignedExactCoreReadingHom P R

theorem generatedConfiguration_eq
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    Q.configuration = P.configuration.transport f.atomMap

theorem base_eq
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    f.objectMap P.object = Q.object

noncomputable def toObjectAlgebraHom
    {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    ObjectAlgebraHom P.algebra Q.algebra

@[simp] theorem toObjectAlgebraHom_refl
    (P : AATCorePackage U) :
    (refl P).toObjectAlgebraHom = ObjectAlgebraHom.id P.algebra

@[simp] theorem toObjectAlgebraHom_comp
    {P Q R : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    (g : SignedExactCoreReadingHom Q R) :
    (f.comp g).toObjectAlgebraHom =
      f.toObjectAlgebraHom.comp g.toObjectAlgebraHom

end SignedExactCoreReadingHom

def FiniteCircuitDatum.Positive
    (Qry : FiniteCircuitDatum U) : Prop :=
  ∀ query expected,
    (query, expected) ∈ Qry.queries → expected = true

def PositiveCircuitDatum
    (P : AATCorePackage U)
    (A : P.algebra.Obj)
    (i : P.algebra.lawReading.lawUniverse.Index) : Type u :=
  {Qry : FiniteCircuitDatum U //
    Qry.Positive ∧
      Qry.Matches (P.algebra.object A) ∧
        P.algebra.lawReading.circuits.accepts i Qry = true}

structure PositiveCoreReadingHom
    (P Q : AATCorePackage U) where
  atomMap : U.Atom → U.Atom
  extraction_mono :
    (P.family.transport atomMap).Subset Q.family
  compositionMap :
    ∀ (F : AtomFamily U) (hF : F.ListFinite),
      ConfigurationHom
        (P.reading.composition.compose F hF)
        (Q.reading.composition.compose
          (F.transport atomMap) (hF.transport atomMap))
  compositionMap_atomMap :
    ∀ F hF, (compositionMap F hF).atomMap = atomMap
  objectMap : ArchitectureObject U → ArchitectureObject U
  object_formation_eq :
    ∀ C,
      objectMap (P.reading.objectReading.object C) =
        Q.reading.objectReading.object (C.transport atomMap)
  base_reachable :
    Q.reading.operationReading.Reachable Q.object (objectMap P.object)
  configurationMap :
    ∀ A, ConfigurationHom A.configuration (objectMap A).configuration
  configurationMap_atomMap :
    ∀ A, (configurationMap A).atomMap = atomMap
  operationMap :
    ∀ {A B},
      P.reading.operationReading.Op A B →
        Q.reading.operationReading.Op (objectMap A) (objectMap B)
  operation_naturality :
    ∀ {A B} (op : P.reading.operationReading.Op A B),
      ConfigurationHom.comp
          (Q.reading.operationReading.configurationMap (operationMap op))
          (configurationMap A) =
        ConfigurationHom.comp
          (configurationMap B)
          (P.reading.operationReading.configurationMap op)
  lawMap :
    P.algebra.lawReading.lawUniverse.Index →
      Q.algebra.lawReading.lawUniverse.Index
  queryMap : FiniteCircuitDatum U → FiniteCircuitDatum U
  positive_preserved :
    ∀ Qry, Qry.Positive → (queryMap Qry).Positive
  matches_of_positive :
    ∀ Qry A, Qry.Positive → Qry.Matches A →
      (queryMap Qry).Matches (objectMap A)
  accepts_mono :
    ∀ i Qry, Qry.Positive →
      P.algebra.lawReading.circuits.accepts i Qry = true →
        Q.algebra.lawReading.circuits.accepts
          (lawMap i) (queryMap Qry) = true

namespace PositiveCoreReadingHom

@[ext] theorem ext
    {P Q : AATCorePackage U}
    {f g : PositiveCoreReadingHom P Q}
    (hatom : f.atomMap = g.atomMap)
    (hobject : f.objectMap = g.objectMap)
    (hoperation : HEq f.operationMap g.operationMap)
    (hlaw : HEq f.lawMap g.lawMap)
    (hquery : f.queryMap = g.queryMap) :
    f = g

def refl (P : AATCorePackage U) :
    PositiveCoreReadingHom P P

def comp
    {P Q R : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q)
    (g : PositiveCoreReadingHom Q R) :
    PositiveCoreReadingHom P R

theorem mapReachable
    {P Q : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q)
    {A : ArchitectureObject U}
    (hA : P.reading.operationReading.Reachable P.object A) :
    Q.reading.operationReading.Reachable Q.object (f.objectMap A)

def objMap
    {P Q : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q) :
    P.algebra.Obj → Q.algebra.Obj :=
  fun A => ⟨f.objectMap A.1, f.mapReachable A.2⟩

def mapPositiveCircuit
    {P Q : AATCorePackage U}
    (f : PositiveCoreReadingHom P Q)
    {A : P.algebra.Obj}
    {i : P.algebra.lawReading.lawUniverse.Index}
    (c : PositiveCircuitDatum P A i) :
    PositiveCircuitDatum Q (f.objMap A) (f.lawMap i)

end PositiveCoreReadingHom

namespace ReadingCore

abbrev ExactCoreChange
    (p q : ReadingCore.{u, v} U) :=
  SignedExactCoreReadingHom p.core q.core

abbrev PositiveCoreChange
    (p q : ReadingCore.{u, v} U) :=
  PositiveCoreReadingHom p.core q.core

abbrev SelectedCover
    (p : ReadingCore.{u, v} U)
    (base : p.site.category) :=
  Site.AATCoverageFamily p.site.requirements p.site.overlap base

end ReadingCore
~~~

`toObjectAlgebraHom`のreachable-object proofはprimitive operation mapから帰納的に構成し、
structure fieldへ追加しない。exact base objectの一致も`extraction_eq`、`composition_eq`、
`object_formation_eq`から`base_eq`として導出し、fieldにしない。
exact changeの`matches_iff`はnegative queryのabsence反射をproof bodyで使用する。
positive changeではbase objectのtarget reachabilityだけをprimitive compatibilityとして固定し、
任意のsource reachable objectのtarget reachabilityを`operationMap`による帰納法で導出する。
したがってpositive circuitはactual `Q.algebra.Obj`へtransportされるが、law反射を持つ
`ObjectAlgebraHom`は主張しない。positive changeからnegative circuitを運ぶtargetは置かない。

### SD2 — selected closed-law extension

law laneはclosed-equational geometryのmerged APIを直接使用する。
新しい`LawExtension`、adapter、rename、duplicate mapを作らない。
対象は同一`raw`・同一`X`・同一`S.lawUniverse.Index`である。

~~~lean
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable (X : LawAlgebra.StandardArchitectureScheme raw)

example
    {R Q : LawAlgebra.ClosedEquationalLawReading raw X}
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hQ : LawAlgebra.IsClosedEquationalLawReading raw X Q)
    (hRclosed : LawAlgebra.RequiredClosed raw X R)
    (hQclosed : LawAlgebra.RequiredClosed raw X Q)
    (e : LawAlgebra.ClosedEquationalLawInclusion raw X R Q)
    (he : LawAlgebra.IsClosedEquationalLawInclusion raw X e) :
    LawAlgebra.lawfulClosedSubscheme raw X Q hQ hQclosed ⟶
      LawAlgebra.lawfulClosedSubscheme raw X R hR hRclosed :=
  LawAlgebra.lawfulClosedSubschemeMap
    raw X hR hQ hRclosed hQclosed e he

example
    {R Q : LawAlgebra.ClosedEquationalLawReading raw X}
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hQ : LawAlgebra.IsClosedEquationalLawReading raw X Q)
    (e : LawAlgebra.ClosedEquationalLawInclusion raw X R Q)
    (he : LawAlgebra.IsClosedEquationalLawInclusion raw X e) :
    LawAlgebra.allLawfulClosedSubscheme raw X Q hQ ⟶
      LawAlgebra.allLawfulClosedSubscheme raw X R hR :=
  LawAlgebra.allLawfulClosedSubschemeMap raw X hR hQ e he

example
    {R Q : LawAlgebra.ClosedEquationalLawReading raw X}
    (e : LawAlgebra.ClosedEquationalLawInclusion raw X R Q)
    (he : LawAlgebra.IsClosedEquationalLawInclusion raw X e)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) :
    LawAlgebra.SemanticLawfulAlong raw X Q s →
      LawAlgebra.SemanticLawfulAlong raw X R s :=
  LawAlgebra.semanticLawfulAlong_mono raw X e he s

example
    {R Q : LawAlgebra.ClosedEquationalLawReading raw X}
    (e : LawAlgebra.ClosedEquationalLawInclusion raw X R Q)
    (he : LawAlgebra.IsClosedEquationalLawInclusion raw X e)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) :
    LawAlgebra.FullySemanticLawfulAlong raw X Q s →
      LawAlgebra.FullySemanticLawfulAlong raw X R s :=
  LawAlgebra.fullySemanticLawfulAlong_mono raw X e he s
~~~

executable contractは、semantic comparisonのrequired / full all-law二系統と、
ideal / closed geometry comparisonのrequired / all-selected二系統を直接参照する。
`allLawGeneratedIdealSheaf`と`allLawfulClosedSubscheme`はaffine open `V`ごとの
`R.selected V`上の対象である。`AllLawsSelected R`がある場合に同じ対象を
full all-lawとして特殊化する。
stronger reading `Q`に対してidealは`I_R ≤ I_Q`、closed geometryは
`V(I_Q) ⟶ V(I_R)`である。

### SD3 — coverage topology refinementとselected cover refinement

topology refinementと個別cover refinementを別の型にする。
個別coverは`Site.AATCoverageFamily`そのものを入力し、simplex、反復overlap、faceを
そこからcanonicalに生成する。任意のsimplicial objectやoverlap familyは入力しない。

~~~lean
structure CoverageTopologyRefinement
    {C : Type u} [Category.{v} C]
    (J J' : GrothendieckTopology C) where
  refineCover :
    ∀ (X : C) (R : Sieve X), R ∈ J X →
      {R' : Sieve X // R' ∈ J' X ∧ R' ≤ R}

namespace CoverageTopologyRefinement

theorem le
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J') :
    J ≤ J'

def refl (J : GrothendieckTopology C) :
    CoverageTopologyRefinement J J

def comp
    {J₁ J₂ J₃ : GrothendieckTopology C}
    (f : CoverageTopologyRefinement J₁ J₂)
    (g : CoverageTopologyRefinement J₂ J₃) :
    CoverageTopologyRefinement J₁ J₃

end CoverageTopologyRefinement

namespace Site.AATCoverageFamily

structure Refinement
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {base : S.category}
    (coarse fine :
      Site.AATCoverageFamily S.requirements S.overlap base) where
  indexMap : fine.Index → coarse.Index
  factor :
    ∀ i,
      S.contextPreorder.le
        (fine.patch i) (coarse.patch (indexMap i))
  factor_triangle :
    ∀ i,
      S.contextPreorder.trans (factor i)
        (coarse.inclusion (indexMap i)) = fine.inclusion i

namespace Refinement

def refl (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Refinement 𝒰 𝒰

def comp
    {𝒰 𝒱 𝒲 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱)
    (s : Refinement 𝒱 𝒲) :
    Refinement 𝒰 𝒲

theorem presieve_le
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱) :
    Sieve.generate 𝒱.presieve ≤ Sieve.generate 𝒰.presieve

end Refinement

theorem mem_topology
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Sieve.generate 𝒰.presieve ∈ S.topology base

end Site.AATCoverageFamily

namespace Cohomology

noncomputable def canonicalTupleOverlap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ∀ n, Site.FinitePosetCechCanonicalTupleSimplex 𝒰.Index n → S.category

@[simp] theorem canonicalTupleOverlap_zero
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (σ : Fin 1 → 𝒰.Index) :
    canonicalTupleOverlap 𝒰 0 σ =
      Site.ContextCategoryObject.of S.contextPreorder (𝒰.patch (σ 0))

@[simp] theorem canonicalTupleOverlap_succ
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (σ : Fin (n + 2) → 𝒰.Index) :
    (canonicalTupleOverlap 𝒰 (n + 1) σ).ctx =
      S.overlap.overlap base.ctx
        (canonicalTupleOverlap 𝒰 n
          (fun i => σ i.castSucc)).ctx
        (𝒰.patch (σ (Fin.last (n + 1))))

theorem canonicalTupleOverlap_face_le
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (i : Fin (n + 2))
    (σ : Fin (n + 2) → 𝒰.Index) :
    S.contextPreorder.le
      (canonicalTupleOverlap 𝒰 (n + 1) σ).ctx
      (canonicalTupleOverlap 𝒰 n
        (Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
          (SimplexCategory.δ i) σ)).ctx

noncomputable def canonicalCoverRelative
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    CoverRelativeCechCover S where
  base := base
  Index := 𝒰.Index
  chart i := Site.ContextCategoryObject.of S.contextPreorder (𝒰.patch i)
  inclusion i := homOfLE (𝒰.inclusion i)
  simplex n := Site.FinitePosetCechCanonicalTupleSimplex 𝒰.Index n
  overlap n σ := canonicalTupleOverlap 𝒰 n σ
  face n i σ :=
    Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
      (SimplexCategory.δ i) σ
  faceRestriction n i σ := by
    apply homOfLE
    exact canonicalTupleOverlap_face_le 𝒰 n i σ

@[simp] theorem canonicalCoverRelative_base
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    (canonicalCoverRelative 𝒰).base = base

@[simp] theorem canonicalCoverRelative_simplex
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    (canonicalCoverRelative 𝒰).simplex n =
      Site.FinitePosetCechCanonicalTupleSimplex 𝒰.Index n

@[simp] theorem canonicalCoverRelative_overlap
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (σ : Fin (n + 1) → 𝒰.Index) :
    (canonicalCoverRelative 𝒰).overlap n σ =
      canonicalTupleOverlap 𝒰 n σ

@[simp] theorem canonicalCoverRelative_face
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (i : Fin (n + 2))
    (σ : Fin (n + 2) → 𝒰.Index) :
    (canonicalCoverRelative 𝒰).face n i σ =
      Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
        (SimplexCategory.δ i) σ

theorem canonicalCoverRelative_twoFace
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (σ : (canonicalCoverRelative 𝒰).simplex (n + 2))
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    (canonicalCoverRelative 𝒰).face n i
        ((canonicalCoverRelative 𝒰).face (n + 1) j.succ σ) =
      (canonicalCoverRelative 𝒰).face n j
        ((canonicalCoverRelative 𝒰).face (n + 1) i.castSucc σ)

theorem canonicalCoverRelative_faceRestriction_twoFace
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (σ : (canonicalCoverRelative 𝒰).simplex (n + 2))
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    (canonicalCoverRelative 𝒰).faceRestriction (n + 1) j.succ σ ≫
        (canonicalCoverRelative 𝒰).faceRestriction n i
          ((canonicalCoverRelative 𝒰).face (n + 1) j.succ σ) =
      (canonicalCoverRelative 𝒰).faceRestriction (n + 1) i.castSucc σ ≫
        (canonicalCoverRelative 𝒰).faceRestriction n j
          ((canonicalCoverRelative 𝒰).face (n + 1) i.castSucc σ) ≫
        eqToHom (canonicalCoverRelative_twoFace 𝒰 n σ i j hij).symm

namespace Site.AATCoverageFamily.Refinement

def simplexMap
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱)
    (n : Nat) :
    (canonicalCoverRelative 𝒱).simplex n →
      (canonicalCoverRelative 𝒰).simplex n :=
  fun σ i => r.indexMap (σ i)

noncomputable def overlapMap
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱)
    (n : Nat) (σ : (canonicalCoverRelative 𝒱).simplex n) :
    (canonicalCoverRelative 𝒱).overlap n σ ⟶
      (canonicalCoverRelative 𝒰).overlap n (r.simplexMap n σ)

theorem overlapMap_face_naturality
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱)
    (n : Nat) (i : Fin (n + 2))
    (σ : (canonicalCoverRelative 𝒱).simplex (n + 1)) :
    (canonicalCoverRelative 𝒱).faceRestriction n i σ ≫
        r.overlapMap n ((canonicalCoverRelative 𝒱).face n i σ) =
      r.overlapMap (n + 1) σ ≫
        (canonicalCoverRelative 𝒰).faceRestriction n i
          (r.simplexMap (n + 1) σ)

end Site.AATCoverageFamily.Refinement
end Cohomology
~~~

`canonicalTupleOverlap`は`S.overlap`の反復だけから生成し、
`canonicalCoverRelative`の全次数simplex、overlap、face、restrictionをcharacterization theoremで固定する。
refinementのcoarse / fine coverは同じ`base`でindexされるため、後段でbaseのcastを導入しない。

### SD4 — canonical Čech complex、one-way cochain hom、class naturality

現行`CoverRelativeCechComplex`はdifferentialをfieldで受けるため、そのfield projectionを
refinement functorialityの完了根拠にしない。`canonicalCechComplex`をrestriction mapの交代和から
構成し、refinementからone-way homを導く。

~~~lean
namespace Cohomology

def ObstructionSheaf.mapAddMonoidHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (Ob : ObstructionSheaf S)
    {X Y : S.category} (f : X ⟶ Y) :
    Ob.carrier.toPresheaf.obj (op Y) →+
      Ob.carrier.toPresheaf.obj (op X)

noncomputable def canonicalCechComplex
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    CoverRelativeCechComplex (canonicalCoverRelative 𝒰) Ob

theorem canonicalCechComplex_d_apply
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S)
    (n : Nat)
    (c : (canonicalCechComplex 𝒰 Ob).AdditiveCochain n)
    (σ : (canonicalCoverRelative 𝒰).simplex (n + 1)) :
    (canonicalCechComplex 𝒰 Ob).d n c σ =
      ∑ i : Fin (n + 2),
        ((-1 : ℤ) ^ i.1) •
          Ob.mapAddMonoidHom
            ((canonicalCoverRelative 𝒰).faceRestriction n i σ)
            (c ((canonicalCoverRelative 𝒰).face n i σ))

theorem canonicalCechComplex_d_comp_d
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S)
    (n : Nat)
    (c : (canonicalCechComplex 𝒰 Ob).AdditiveCochain n) :
    (canonicalCechComplex 𝒰 Ob).d (n + 1)
        ((canonicalCechComplex 𝒰 Ob).d n c) = 0

namespace CoverRelativeCechComplex

def AdditiveCechHn
    (K : CoverRelativeCechComplex 𝒰 Ob) :
    Nat → Type u
  | 0 => K.CechCocycleSubgroup 0
  | n + 1 =>
      K.CechCocycleSubgroup (n + 1) ⧸
        K.CechCoboundarySubgroupSucc n

instance additiveCechHnAddCommGroup
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (n : Nat) :
    AddCommGroup (K.AdditiveCechHn n)

def additiveCohomologyClass
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (n : Nat) :
    K.CechCocycle n → K.AdditiveCechHn n

structure Hom
    {𝒰 𝒱 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (L : CoverRelativeCechComplex 𝒱 Ob) where
  app : ∀ n, K.AdditiveCochain n →+ L.AdditiveCochain n
  commutes :
    ∀ n c, app (n + 1) (K.d n c) = L.d n (app n c)

namespace Hom

def mapCocycle
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) (n : Nat) :
    K.CechCocycle n → L.CechCocycle n

def id (K : CoverRelativeCechComplex 𝒰 Ob) : Hom K K

def comp
    {𝒰 𝒱 𝒲 : CoverRelativeCechCover S}
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    {M : CoverRelativeCechComplex 𝒲 Ob}
    (f : Hom K L) (g : Hom L M) :
    Hom K M

def mapAdditiveCechHn
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) (n : Nat) :
    K.AdditiveCechHn n →+ L.AdditiveCechHn n

@[simp] theorem mapAdditiveCechHn_id
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) :
    (id K).mapAdditiveCechHn n = AddMonoidHom.id _

@[simp] theorem mapAdditiveCechHn_comp
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    {M : CoverRelativeCechComplex 𝒲 Ob}
    (f : Hom K L) (g : Hom L M) (n : Nat) :
    (f.comp g).mapAdditiveCechHn n =
      (g.mapAdditiveCechHn n).comp (f.mapAdditiveCechHn n)

end Hom

end CoverRelativeCechComplex

noncomputable def Site.AATCoverageFamily.Refinement.canonicalCechHom
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) :
    CoverRelativeCechComplex.Hom
      (canonicalCechComplex 𝒰 Ob)
      (canonicalCechComplex 𝒱 Ob)

theorem Site.AATCoverageFamily.Refinement.canonicalCechHom_app_apply
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S)
    (n : Nat)
    (c : (canonicalCechComplex 𝒰 Ob).AdditiveCochain n)
    (σ : (canonicalCoverRelative 𝒱).simplex n) :
    (r.canonicalCechHom Ob).app n c σ =
      Ob.mapAddMonoidHom (r.overlapMap n σ)
        (c (r.simplexMap n σ))

@[simp] theorem Site.AATCoverageFamily.Refinement.canonicalCechHom_refl
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    (Site.AATCoverageFamily.Refinement.refl 𝒰).canonicalCechHom Ob =
      CoverRelativeCechComplex.Hom.id (canonicalCechComplex 𝒰 Ob)

@[simp] theorem Site.AATCoverageFamily.Refinement.canonicalCechHom_comp
    {𝒰 𝒱 𝒲 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (s : Site.AATCoverageFamily.Refinement 𝒱 𝒲)
    (Ob : ObstructionSheaf S) :
    (r.comp s).canonicalCechHom Ob =
      (r.canonicalCechHom Ob).comp (s.canonicalCechHom Ob)

theorem obstructionClass_naturality
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S)
    (n : Nat)
    (c : (canonicalCechComplex 𝒰 Ob).CechCocycle n) :
    (r.canonicalCechHom Ob).mapAdditiveCechHn n
        ((canonicalCechComplex 𝒰 Ob).additiveCohomologyClass n c) =
      (canonicalCechComplex 𝒱 Ob).additiveCohomologyClass n
        ((r.canonicalCechHom Ob).mapCocycle n c)

end Cohomology
~~~

`AdditiveCechHn`、`additiveCohomologyClass`、`mapCocycle`は
degree 0 / successorをactual additive quotientとして統一する。
`CochainComparison.Equivalence`やselected finite H1 comparisonのfieldを
一般refinement mapの代用にしない。

### SD5 — actual sheaf cohomology comparison

`ConditionalSpaceCohomology.HnX`は使用しない。`ObstructionSheaf`を
`AddCommGrpCat`-valued actual sheafへbundlingする。任意baseのcoverはまず
Mathlib `Sheaf.H' n base`へ比較し、global `Sheaf.H`へ進むときだけterminal baseと
`H'` / `H` comparisonを明示する。Leray条件は反復overlap上のpositive-degree
`Sheaf.H'` vanishingで固定し、comparison mapやisoをfieldに持たない。

~~~lean
namespace Cohomology

noncomputable def ObstructionSheaf.toAddCommGrpSheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (Ob : ObstructionSheaf S) :
    Sheaf S.topology AddCommGrpCat.{u}

def IsLerayFor
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})] :
    Prop :=
  ∀ q, 0 < q →
    ∀ p, ∀ σ : (canonicalCoverRelative 𝒰).simplex p,
      Subsingleton
        ((Ob.toAddCommGrpSheaf).H' q
          ((canonicalCoverRelative 𝒰).overlap p σ))

noncomputable def cechToSheafHAtBase
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (hLeray : IsLerayFor 𝒰 Ob)
    (n : Nat) :
    (canonicalCechComplex 𝒰 Ob).AdditiveCechHn n →+
      (Ob.toAddCommGrpSheaf).H' n base

theorem cechToSheafHAtBase_bijective
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (hLeray : IsLerayFor 𝒰 Ob)
    (n : Nat) :
    Function.Bijective (cechToSheafHAtBase 𝒰 Ob hLeray n)

theorem cechToSheafHAtBase_refinement_naturality
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (h𝒰 : IsLerayFor 𝒰 Ob)
    (h𝒱 : IsLerayFor 𝒱 Ob)
    (n : Nat) :
    (cechToSheafHAtBase 𝒱 Ob h𝒱 n).comp
        ((r.canonicalCechHom Ob).mapAdditiveCechHn n) =
      cechToSheafHAtBase 𝒰 Ob h𝒰 n

noncomputable def terminalHComparison
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{w})
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    (X : C) (hX : IsTerminal X) (n : Nat) :
    F.H' n X ≃+ F.H n

noncomputable def cechToSheafH
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (hbase : IsTerminal base)
    (hLeray : IsLerayFor 𝒰 Ob)
    (n : Nat) :
    (canonicalCechComplex 𝒰 Ob).AdditiveCechHn n →+
      (Ob.toAddCommGrpSheaf).H n :=
  (terminalHComparison Ob.toAddCommGrpSheaf base hbase n).toAddMonoidHom.comp
    (cechToSheafHAtBase 𝒰 Ob hLeray n)

theorem cechToSheafH_bijective
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (hbase : IsTerminal base)
    (hLeray : IsLerayFor 𝒰 Ob)
    (n : Nat) :
    Function.Bijective (cechToSheafH 𝒰 Ob hbase hLeray n)

theorem cechToSheafH_refinement_naturality
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (hbase : IsTerminal base)
    (h𝒰 : IsLerayFor 𝒰 Ob)
    (h𝒱 : IsLerayFor 𝒱 Ob)
    (n : Nat) :
    (cechToSheafH 𝒱 Ob hbase h𝒱 n).comp
        ((r.canonicalCechHom Ob).mapAdditiveCechHn n) =
      cechToSheafH 𝒰 Ob hbase h𝒰 n

end Cohomology
~~~

topology changeは同一presheafが両topologyでsheafになるdataをcoefficient compatibilityとして受ける。
cohomology map自体はfieldにせず、coarse / fine sheaf category間のactual functor、
constant sheaf comparison、Ext naturalityから構成する。Mathlibに未実装の比較があれば
必須child Issueで実装し、cover-relative mapだけで完了しない。

~~~lean
structure CommonCoefficientSheaf
    {C : Type u} [Category.{v} C]
    (J J' : GrothendieckTopology C) where
  presheaf : Cᵒᵖ ⥤ AddCommGrpCat.{w}
  isSheaf_coarse : Presheaf.IsSheaf J presheaf
  isSheaf_fine : Presheaf.IsSheaf J' presheaf

namespace CommonCoefficientSheaf

def coarse (F : CommonCoefficientSheaf J J') :
    Sheaf J AddCommGrpCat.{w}

def fine (F : CommonCoefficientSheaf J J') :
    Sheaf J' AddCommGrpCat.{w}

noncomputable def sameTopologyIso
    (F : CommonCoefficientSheaf J J) :
    F.coarse ≅ F.fine

noncomputable def sameTopologyHMap
    (F : CommonCoefficientSheaf J J)
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    (n : Nat) :
    F.coarse.H n →+ F.fine.H n :=
  (Abelian.Ext.mk₀ (F.sameTopologyIso).hom).postcomp
    ((constantSheaf J AddCommGrpCat.{w}).obj
      (AddCommGrpCat.of (ULift ℤ))) (add_zero n)

end CommonCoefficientSheaf

noncomputable def CoverageTopologyRefinement.fineSheafification
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J' AddCommGrpCat.{w}] :
    Sheaf J AddCommGrpCat.{w} ⥤ Sheaf J' AddCommGrpCat.{w} :=
  sheafToPresheaf J AddCommGrpCat.{w} ⋙
    presheafToSheaf J' AddCommGrpCat.{w}

theorem CoverageTopologyRefinement.isSheaf_coarse
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J')
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hP : Presheaf.IsSheaf J' P) :
    Presheaf.IsSheaf J P :=
  fun E =>
    Presieve.isSheaf_of_le
      (P ⋙ coyoneda.obj (op E)) r.le (hP E)

def CoverageTopologyRefinement.coarseRestriction
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J') :
    Sheaf J' AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w} where
  obj F := ⟨F.val, r.isSheaf_coarse F.val F.cond⟩
  map η := ⟨η.val⟩

noncomputable def CoverageTopologyRefinement.fineSheafificationAdjunction
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J' AddCommGrpCat.{w}] :
    r.fineSheafification ⊣ r.coarseRestriction :=
  (sheafificationAdjunction J' AddCommGrpCat.{w}).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{w})
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

noncomputable instance CoverageTopologyRefinement.fineSheafification_additive
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}] :
    (r.fineSheafification).Additive

noncomputable instance CoverageTopologyRefinement.fineSheafification_preservesFiniteLimits
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}] :
    PreservesFiniteLimits r.fineSheafification

noncomputable instance CoverageTopologyRefinement.fineSheafification_preservesFiniteColimits
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}] :
    PreservesFiniteColimits r.fineSheafification

noncomputable def CoverageTopologyRefinement.constantSheafIso
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}] :
    (r.fineSheafification.obj
      ((constantSheaf J AddCommGrpCat.{w}).obj
        (AddCommGrpCat.of (ULift ℤ)))) ≅
      (constantSheaf J' AddCommGrpCat.{w}).obj
        (AddCommGrpCat.of (ULift ℤ))

noncomputable def CoverageTopologyRefinement.commonCoefficientIso
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J')
    (F : CommonCoefficientSheaf J J')
    [HasSheafify J' AddCommGrpCat.{w}] :
    r.fineSheafification.obj F.coarse ≅ F.fine

noncomputable def CoverageTopologyRefinement.sheafHExtMap
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J')
    (F : CommonCoefficientSheaf J J')
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    [HasExt.{w} (Sheaf J' AddCommGrpCat.{w})]
    (n : Nat) :
    F.coarse.H n →+ F.fine.H n :=
  ((Abelian.Ext.mk₀ (r.commonCoefficientIso F).hom).postcomp
      ((constantSheaf J' AddCommGrpCat.{w}).obj
        (AddCommGrpCat.of (ULift ℤ))) (add_zero n)).comp
    (((Abelian.Ext.mk₀ (r.constantSheafIso).inv).precomp
        (r.fineSheafification.obj F.coarse) (zero_add n)).comp
      (r.fineSheafification.mapExtAddHom
        ((constantSheaf J AddCommGrpCat.{w}).obj
          (AddCommGrpCat.of (ULift ℤ))) F.coarse n))

noncomputable def CoverageTopologyRefinement.sheafHMap
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J')
    (F : CommonCoefficientSheaf J J')
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    [HasExt.{w} (Sheaf J' AddCommGrpCat.{w})]
    (n : Nat) :
    F.coarse.H n →+ F.fine.H n :=
  r.sheafHExtMap F n

@[simp] theorem CoverageTopologyRefinement.sheafHMap_eq_ext
    {C : Type u} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J')
    (F : CommonCoefficientSheaf J J')
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    [HasExt.{w} (Sheaf J' AddCommGrpCat.{w})]
    (n : Nat) :
    r.sheafHMap F n = r.sheafHExtMap F n := rfl

@[simp] theorem CoverageTopologyRefinement.sheafHMap_refl
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (F : CommonCoefficientSheaf J J)
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    (n : Nat) :
    (CoverageTopologyRefinement.refl J).sheafHMap F n =
      F.sameTopologyHMap n

theorem CoverageTopologyRefinement.sheafHMap_comp
    {C : Type u} [Category.{v} C]
    {J₁ J₂ J₃ : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J₁ J₂)
    (s : CoverageTopologyRefinement J₂ J₃)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (h₁ : Presheaf.IsSheaf J₁ F)
    (h₂ : Presheaf.IsSheaf J₂ F)
    (h₃ : Presheaf.IsSheaf J₃ F)
    [HasSheafify J₁ AddCommGrpCat.{w}]
    [HasSheafify J₂ AddCommGrpCat.{w}]
    [HasSheafify J₃ AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf J₁ AddCommGrpCat.{w})]
    [HasExt.{w} (Sheaf J₂ AddCommGrpCat.{w})]
    [HasExt.{w} (Sheaf J₃ AddCommGrpCat.{w})]
    (n : Nat) :
    (r.comp s).sheafHMap ⟨F, h₁, h₃⟩ n =
      (s.sheafHMap ⟨F, h₂, h₃⟩ n).comp
        (r.sheafHMap ⟨F, h₁, h₂⟩ n)
~~~

`terminalHComparison`はMathlib `Basic.lean`に残る未実装箇所を埋めるactual theoremであり、
任意isoを入力しない。`sheafHMap_refl`、`sheafHMap_comp`とSD9のnonzero firingを
zero mapやunrelated Ext mapの排除条件とする。
`fineSheafification`のexactnessは実在しない一括predicateで表さない。
`PreservesFiniteLimits`は`sheafToPresheaf`とleft-exact `presheafToSheaf`の合成から、
`PreservesFiniteColimits`は`fineSheafificationAdjunction`のleft-adjoint性から、
`Additive`はpointwise additiveな`sheafToPresheaf`と`presheafToSheaf_additive`の合成から導き、
三instanceのproof-useを分けて記録する。
`coarseRestriction`は`r.le`と`Presieve.isSheaf_of_le`からfine sheafをcoarse sheafとして
再解釈するactual right adjointであり、adjunctionや保存性を自由なfieldとして受け取らない。
`sheafHExtMap`は`mapExtAddHom`の後にconstant-sheaf isoをprecomposition、
common-coefficient isoをpostcompositionする具体的な合成であり、`sheafHMap_eq_ext`で主経路を固定する。

### SD6 — canonical raw / scheme coefficient base change

coefficient changeはring homとflatnessだけをprimitive change dataとする。
変更後raw system、standard scheme、law reading、ideal comparison、scheme morphismをfieldに持たない。
scheme-level pullbackには、係数拡大functorが選択site上のsheafをsheafへ送るという
Mathlibの`GrothendieckTopology.HasSheafCompose`を明示する。この条件は`FlatCoefficientChange`の
fieldにせず、siteと係数写像に依存するmaterial premiseとしてscheme-level APIだけに課す。
flatnessは係数拡大functorの有限極限保存を与えるが、一般coverのmatching objectに現れる
無限積の保存を自動では与えないため、両者を同一視しない。
Implementation notes: `coefficientExtension`とscheme-level APIは`k k' : Type v`を使い、
同じ`CommRingCat` universe内のMathlib `Under.pushout`へ直接接続する。
cross-universe coefficient changeには追加のcategory universe equivalenceが必要だが、
本PRDはそのrepackageを導入せず、係数環の数学的内容を変えないcommon-universe statementを固定する。

~~~lean
structure FlatCoefficientChange
    (k : Type v) [CommRing k]
    (k' : Type w) [CommRing k'] where
  hom : k →+* k'
  flat : hom.Flat

namespace FlatCoefficientChange

def refl (k : Type v) [CommRing k] :
    FlatCoefficientChange k k

def comp
    {k : Type v} {k' : Type w} {k'' : Type x}
    [CommRing k] [CommRing k'] [CommRing k'']
    (f : FlatCoefficientChange k k')
    (g : FlatCoefficientChange k' k'') :
    FlatCoefficientChange k k''

noncomputable def liftedHom
    {k k' : Type v}
    [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    ULift.{max u v, v} k →+* ULift.{max u v, v} k'

noncomputable def coefficientExtension
    {k k' : Type v}
    [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k' :=
  Under.pushout (CommRingCat.ofHom f.liftedHom)

noncomputable instance coefficientExtension_preservesFiniteLimits
    {k k' : Type v}
    [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    PreservesFiniteLimits
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')

noncomputable instance coefficientExtension_preservesSheafification
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A)
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : FlatCoefficientChange k k') :
    S.topology.PreservesSheafification
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')

noncomputable def coefficientExtensionReflIso
    (k : Type v) [CommRing k] :
    ((FlatCoefficientChange.refl k).coefficientExtension :
      AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k) ≅ 𝟙 _

noncomputable def coefficientExtensionCompIso
    {k k' k'' : Type v}
    [CommRing k] [CommRing k'] [CommRing k'']
    (f : FlatCoefficientChange k k')
    (g : FlatCoefficientChange k' k'') :
    ((f.comp g).coefficientExtension :
      AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k'') ≅
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k') ⋙
      (g.coefficientExtension :
        AATCommAlgCat.{u, v} k' ⥤ AATCommAlgCat.{u, v} k'')

noncomputable instance coefficientExtension_hasSheafCompose_refl
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k] :
    S.topology.HasSheafCompose
      ((FlatCoefficientChange.refl k).coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k)

theorem coefficientExtension_hasSheafCompose_comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {k k' k'' : Type v}
    [CommRing k] [CommRing k'] [CommRing k'']
    (f : FlatCoefficientChange k k')
    (g : FlatCoefficientChange k' k'')
    (hf : S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k'))
    (hg : S.topology.HasSheafCompose
      (g.coefficientExtension :
        AATCommAlgCat.{u, v} k' ⥤ AATCommAlgCat.{u, v} k'')) :
    S.topology.HasSheafCompose
      ((f.comp g).coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k'')

end FlatCoefficientChange

namespace LawAlgebra

noncomputable def StructuralRelationFamily.baseChange
    {W : Site.ArchitectureContext A}
    {k k' : Type v}
    [CommRing k] [CommRing k']
    {F : CoordinateFamily W}
    (R : StructuralRelationFamily F k)
    (f : k →+* k') :
    StructuralRelationFamily F k'

noncomputable def RestrictionStableStructuralRelations.baseChange
    {source target : Site.ArchitectureContext A}
    {sourceFamily : CoordinateFamily source}
    {targetFamily : CoordinateFamily target}
    {sourceRelations : StructuralRelationFamily sourceFamily k}
    {targetRelations : StructuralRelationFamily targetFamily k}
    {g : Site.ContextMorphism source target}
    (h : RestrictionStableStructuralRelations
      sourceRelations targetRelations g)
    (f : k →+* k') :
    RestrictionStableStructuralRelations
      (sourceRelations.baseChange f)
      (targetRelations.baseChange f) g

end LawAlgebra

namespace LawAlgebra.RawAmbientRestrictionSystem

noncomputable def baseChange
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k') :
    RawAmbientRestrictionSystem S k'

@[simp] theorem baseChange_coordFamily
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k') :
    (raw.baseChange f).coordFamily = raw.coordFamily

@[simp] theorem baseChange_relationFamily
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k') (W : S.category) :
    (raw.baseChange f).relationFamily W =
      (raw.relationFamily W).baseChange f

theorem baseChange_restrictionStable
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k')
    {W V : S.category} (g : W ⟶ V) :
    HEq ((raw.baseChange f).restrictionStable g)
      ((raw.restrictionStable g).baseChange f)

@[simp] theorem baseChange_id
    (raw : RawAmbientRestrictionSystem S k) :
    raw.baseChange (RingHom.id k) = raw

@[simp] theorem baseChange_comp
    (raw : RawAmbientRestrictionSystem S k)
    (f : k →+* k') (g : k' →+* k'') :
    raw.baseChange (g.comp f) =
      (raw.baseChange f).baseChange g

noncomputable def baseChangePresheafIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    (f : FlatCoefficientChange k k') :
    (raw.baseChange f.hom).toPresheaf ≅
      raw.toPresheaf ⋙ f.coefficientExtension

noncomputable def sheafifiedSectionObjectBaseChangeIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (AATCommAlgCat k)]
    [HasSheafify S.topology (AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    (f.coefficientExtension.obj
        (raw.toRingedSite.structureSheaf.val.obj (op W)) :
      AATCommAlgCat.{u, v} k') ≅
      (raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj (op W)

noncomputable def sheafifiedSectionSpecBaseChangeIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (AATCommAlgCat k)]
    [HasSheafify S.topology (AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    architectureChartSpec (raw.baseChange f.hom) W ≅
      pullback
        (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom (sheafifiedSectionAlgebraMap raw W)).op)
        (AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom f.hom).op)

noncomputable def sheafifiedSectionBaseChangeMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (AATCommAlgCat k)]
    [HasSheafify S.topology (AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    SheafifiedSectionRing raw W ⟶
      SheafifiedSectionRing (raw.baseChange f.hom) W

theorem sheafifiedSectionBaseChangeMap_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (AATCommAlgCat k)]
    [HasSheafify S.topology (AATCommAlgCat k')]
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    sheafifiedSectionBaseChangeMap raw f W =
      Limits.pushout.inl
          (raw.toRingedSite.structureSheaf.val.obj (op W)).hom
          (CommRingCat.ofHom f.liftedHom) ≫
        (sheafifiedSectionObjectBaseChangeIso raw f W).hom.right

end LawAlgebra.RawAmbientRestrictionSystem

namespace LawAlgebra.StandardArchitectureScheme

noncomputable def coefficientStructureMap
    (X : StandardArchitectureScheme raw) :
    X.underlying ⟶
      AlgebraicGeometry.Scheme.Spec.obj
        (op (CommRingCat.of k))

noncomputable def baseChange
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {k k' : Type v}
    [CommRing k] [CommRing k']
    (raw : RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (AATCommAlgCat k)]
    [HasSheafify S.topology (AATCommAlgCat k')]
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    StandardArchitectureScheme (raw.baseChange f.hom)

noncomputable def baseChangeMap
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (X.baseChange raw f).underlying ⟶ X.underlying

noncomputable def baseChangeUnderlyingIso
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (X.baseChange raw f).underlying ≅
      pullback (X.coefficientStructureMap raw)
        (AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom f.hom).op)

theorem baseChangeMap_eq_pullback_fst
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    X.baseChangeMap raw f =
      (X.baseChangeUnderlyingIso raw f).hom ≫
        pullback.fst
          (X.coefficientStructureMap raw)
          (AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom f.hom).op)

noncomputable def baseChangedDecoration
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    AATReadingDecoration (raw.baseChange f.hom)
      (X.baseChange raw f).underlying

@[simp] theorem baseChangedDecoration_context
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (X.baseChangedDecoration raw f).context = X.decoration.context

theorem baseChangedDecoration_interpretation
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f X.decoration.context ≫
        (X.baseChangedDecoration raw f).interpretation =
      X.decoration.interpretation ≫ (X.baseChangeMap raw f).appTop

@[simp] theorem baseChange_decoration
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (X.baseChange raw f).decoration = X.baseChangedDecoration raw f

noncomputable def baseChangedAtlas
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    ArchitectureAffineAtlas (raw.baseChange f.hom)
      (X.baseChange raw f).underlying
      (X.baseChange raw f).decoration

@[simp] theorem baseChangedAtlas_Index
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (X.baseChangedAtlas raw f).Index = X.atlas.Index

noncomputable def baseChangedChartMap
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    ((X.baseChangedAtlas raw f).chart
      (cast (X.baseChangedAtlas_Index raw f).symm i)).domain ⟶
      (X.atlas.chart i).domain

theorem baseChangedChart_isPullback
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    IsPullback
      ((X.baseChangedAtlas raw f).chart
        (cast (X.baseChangedAtlas_Index raw f).symm i)).map
      (X.baseChangedChartMap raw f i)
      (X.baseChangeMap raw f)
      (X.atlas.chart i).map

theorem baseChange_atlas
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (X.baseChange raw f).atlas = X.baseChangedAtlas raw f

noncomputable def baseChangedOverlaps
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    ArchitectureOverlapPresentation
      (raw.baseChange f.hom) (X.baseChangedAtlas raw f)

theorem baseChangedOverlaps_valid
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    IsArchitectureOverlapPresentation
      (raw.baseChange f.hom) (X.baseChangedOverlaps raw f)

theorem baseChange_overlaps
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    HEq (X.baseChange raw f).overlaps (X.baseChangedOverlaps raw f)

noncomputable def baseChangeIdIso
    (X : StandardArchitectureScheme raw) :
    (X.baseChange raw (FlatCoefficientChange.refl k)).underlying ≅
      X.underlying

theorem baseChangeMap_id
    (X : StandardArchitectureScheme raw) :
    X.baseChangeMap raw (FlatCoefficientChange.refl k) =
      (X.baseChangeIdIso raw).hom

noncomputable def baseChangeCompIso
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    (g : FlatCoefficientChange k' k'')
    [hf : S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    [hg : S.topology.HasSheafCompose
      (g.coefficientExtension :
        AATCommAlgCat.{u, v} k' ⥤ AATCommAlgCat.{u, v} k'')] :
    letI : S.topology.HasSheafCompose
        ((f.comp g).coefficientExtension :
          AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k'') :=
      FlatCoefficientChange.coefficientExtension_hasSheafCompose_comp
        f g hf hg
    ((X.baseChange raw f).baseChange
        (raw.baseChange f.hom) g).underlying ≅
      (X.baseChange raw (f.comp g)).underlying

@[reassoc] theorem baseChangeMap_comp
    (X : StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    (g : FlatCoefficientChange k' k'')
    [hf : S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    [hg : S.topology.HasSheafCompose
      (g.coefficientExtension :
        AATCommAlgCat.{u, v} k' ⥤ AATCommAlgCat.{u, v} k'')] :
    letI : S.topology.HasSheafCompose
        ((f.comp g).coefficientExtension :
          AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k'') :=
      FlatCoefficientChange.coefficientExtension_hasSheafCompose_comp
        f g hf hg
    (X.baseChangeCompIso raw f g).hom ≫
        X.baseChangeMap raw (f.comp g) =
      (X.baseChange raw f).baseChangeMap
          (raw.baseChange f.hom) g ≫
        X.baseChangeMap raw f

end LawAlgebra.StandardArchitectureScheme
~~~

`RawAmbientRestrictionSystem.baseChange`はcoordinate familyを保ち、structural relationの係数を
`f`で写し、restriction polynomial mapとの可換性を証明する。
`baseChangePresheafIso`はstructural quotientの係数変更から構成し、
`sheafifiedSectionObjectBaseChangeIso`はこのpresheaf iso、`sheafifyComposeIso`、
`HasSheafCompose`、`coefficientExtension_preservesSheafification`をproof-useする。
`sheafifiedSectionSpecBaseChangeIso`はこのobject isoと`pullbackSpecIso`からactual affine pullbackを構成し、
`StandardArchitectureScheme.baseChange`は得られたSpec isoからatlas、overlap、
reading decorationを構成する。caller-supplied comparison isoやScheme morphismを受け取らない。

### SD7 — ideal、lawful closed geometry、Torのflat base change

closed-equational readingにもcanonical base changeを定義する。
ideal / closed geometryはrequiredとall-selectedを別々に比較し、
full all-lawは`AllLawsSelected`によるall-selected対象の特殊化として扱う。

~~~lean
namespace LawAlgebra

noncomputable def baseChangedSemanticCoreGlobalEquation
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : S.lawUniverse.Index) (a : U.Atom) :
    Γ((X.baseChange raw f).underlying, ⊤) :=
  (X.baseChangeMap raw f).appTop
    (semanticCoreGlobalEquation raw X G B i a)

noncomputable def ClosedEquationalLawReading.baseChangeOfSemanticCore
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    ClosedEquationalLawReading
      (raw.baseChange f.hom) (X.baseChange raw f) where
  geometric := {
    HoldsOn := fun s i =>
      GlobalEquationsVanishAlong
        (raw.baseChange f.hom) (X.baseChange raw f)
        (baseChangedSemanticCoreGlobalEquation raw X G B f i) s
  }
  closed := Set.univ
  selected := fun _ => Set.univ
  witness := fun i _ =>
    ClosedEquationalLawWitness.ofGlobalSections
      (raw.baseChange f.hom) (X.baseChange raw f) i
      (baseChangedSemanticCoreGlobalEquation raw X G B f i)

theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_geometric_iff
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ (X.baseChange raw f).underlying)
    (i : S.lawUniverse.Index) :
    (ClosedEquationalLawReading.baseChangeOfSemanticCore
      raw X G B f).geometric.HoldsOn s i ↔
      (ClosedEquationalLawReading.ofSemanticCore
        raw X G B).geometric.HoldsOn
          (s ≫ X.baseChangeMap raw f) i

theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    IsClosedEquationalLawReading
      (raw.baseChange f.hom) (X.baseChange raw f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f)

theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    RequiredClosed
      (raw.baseChange f.hom) (X.baseChange raw f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f)

theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_allLawsSelected
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    AllLawsSelected
      (raw.baseChange f.hom) (X.baseChange raw f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f)

theorem semanticCoreLawWitnessIdeal_baseChangedChart
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (j : X.atlas.Index)
    (i : S.lawUniverse.Index) :
    let R' := ClosedEquationalLawReading.baseChangeOfSemanticCore
      raw X G B f
    let hR' :=
      (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
        raw X G B f).witness_compatible
    let j' := cast (X.baseChangedAtlas_Index raw f).symm j
    Scheme.IdealSheafData.comap
        (Scheme.IdealSheafData.ofIdealTop
          (X := (X.atlas.chart j).domain)
          (Ideal.map
            (AlgebraicGeometry.Scheme.ΓSpecIso
              (SheafifiedSectionRing raw
                (X.atlas.chart j).context)).inv.hom
            (Ideal.map
              (B.toSheafifiedSection (X.atlas.chart j).context)
              (G.lawWitnessIdeal (X.atlas.chart j).context i))))
        (X.baseChangedChartMap raw f j) =
      Scheme.IdealSheafData.comap
        (lawWitnessIdealSheaf
          (raw.baseChange f.hom) (X.baseChange raw f)
          R' hR' i (Set.mem_univ i))
        ((X.baseChangedAtlas raw f).chart j').map

theorem lawGeneratedIdealSheaf_baseChange_ofSemanticCore
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    Scheme.IdealSheafData.comap
        (lawGeneratedIdealSheaf raw X
          (ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid
            raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_requiredClosed
            raw X G B))
        (X.baseChangeMap raw f) =
      lawGeneratedIdealSheaf
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore
          raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
          raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
          raw X G B f)

theorem allSelectedLawGeneratedIdealSheaf_baseChange_ofSemanticCore
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    Scheme.IdealSheafData.comap
        (allLawGeneratedIdealSheaf raw X
          (ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid
            raw X G B))
        (X.baseChangeMap raw f) =
      allLawGeneratedIdealSheaf
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore
          raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
          raw X G B f)

noncomputable def lawfulClosedSubschemeBaseChangeMap
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    lawfulClosedSubscheme
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore
          raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
          raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
          raw X G B f) ⟶
      lawfulClosedSubscheme raw X
        (ClosedEquationalLawReading.ofSemanticCore raw X G B)
        (ClosedEquationalLawReading.ofSemanticCore_valid
          raw X G B)
        (ClosedEquationalLawReading.ofSemanticCore_requiredClosed
          raw X G B)

@[reassoc] theorem lawfulClosedSubschemeBaseChangeMap_immersion
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    lawfulClosedSubschemeBaseChangeMap raw X G B f ≫
        lawfulClosedImmersion raw X
          (ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid
            raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_requiredClosed
            raw X G B) =
      lawfulClosedImmersion
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore
          raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
          raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
          raw X G B f) ≫
          X.baseChangeMap raw f

noncomputable def allLawfulClosedSubschemeBaseChangeMap
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    allLawfulClosedSubscheme
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore
          raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
          raw X G B f) ⟶
      allLawfulClosedSubscheme raw X
        (ClosedEquationalLawReading.ofSemanticCore raw X G B)
        (ClosedEquationalLawReading.ofSemanticCore_valid
          raw X G B)

@[reassoc] theorem allLawfulClosedSubschemeBaseChangeMap_immersion
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    allLawfulClosedSubschemeBaseChangeMap raw X G B f ≫
        allLawfulClosedImmersion raw X
          (ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid
            raw X G B) =
      allLawfulClosedImmersion
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore
          raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
          raw X G B f) ≫
        X.baseChangeMap raw f

end LawAlgebra

`baseChangeOfSemanticCore`はsource bridgeから得たglobal equationsを
`X.baseChangeMap.appTop`でtarget global sectionsへ送ってreadingを再構成する。
`SemanticLawEquationWitnessIdealCore`のobservable ringを異なるcoefficient rawへ同一視せず、
target witness compatibilityとrequired / all selectionはglobal-section constructorから導出する。
source realizationはPart 3の`semanticCoreIdealSheaf_realized raw X G B hB`が担う。
`semanticCoreLawWitnessIdeal_baseChangedChart`はそのchart成分、
`baseChangedChart_isPullback`、`IdealSheafData.comap_comp`を同じproof chainで使い、
source semantic-core chart idealをSD6のchart mapで引き戻したidealと、target readingの
law-witness idealを対応chartへ引き戻したidealを直接等置する。
required / all-selected ideal comap equalityはglobal equationsのpullback計算から独立に証明し、
不要な`hB`を受け取らない。lawful closed geometry mapはこのaggregate equalityから構成する。
したがってsource realization、per-law existing-core transport、aggregate ideal base changeを
別の数学的事実として追跡し、単なる積をideal equalityのproof provenanceとは扱わない。

namespace Derived.Intersection

open scoped ChangeOfRings

noncomputable def moduleScalarExtension
    {R R' : Type v}
    [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (M : ModuleCat.{v} R) :
    ModuleCat.{v} R' :=
  (ModuleCat.extendScalars f.hom).obj M

noncomputable def moduleScalarExtensionUnit
    {R R' : Type v}
    [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (M : ModuleCat.{v} R) :
    M ⟶ (ModuleCat.restrictScalars f.hom).obj
      (moduleScalarExtension f M) :=
  (ModuleCat.extendRestrictScalarsAdj f.hom).unit.app M

@[simp] theorem moduleScalarExtensionUnit_apply
    {R R' : Type v}
    [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (M : ModuleCat.{v} R) (m : M) :
    moduleScalarExtensionUnit f M m =
      (1 : R') ⊗ₜ[R, f.hom] m

noncomputable def moduleScalarExtensionIdIso
    {R : Type v} [CommRing R]
    (M : ModuleCat.{v} R) :
    moduleScalarExtension (FlatCoefficientChange.refl R) M ≅ M

noncomputable def moduleScalarExtensionCompIso
    {R R' R'' : Type v}
    [CommRing R] [CommRing R'] [CommRing R'']
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    (M : ModuleCat.{v} R) :
    moduleScalarExtension g (moduleScalarExtension f M) ≅
      moduleScalarExtension (f.comp g) M

noncomputable def mathlibTorFlatBaseChangeIso
    {R R' : Type v}
    [CommRing R] [CommRing R']
    (f : FlatCoefficientChange R R')
    (I J : Ideal R) (n : Nat) :
    moduleScalarExtension f (mathlibTor R I J n) ≅
      mathlibTor R' (I.map f.hom) (J.map f.hom) n

end Derived.Intersection
~~~

affine Tor-object theoremは任意次数で固定し、finite版への差し替えを許さない。
これは第VIII部 定理候補9.2 `Flat Base Change Stability for LawConflict`のaffine表示にある
bare Tor-object formulaを、
flatnessだけで証明する独立の強化targetである。selected coefficient objects、selected
LawConflict class、`conflictSupport` / `selectedSupport`のpullbackはstatementに含まれず、
定理候補9.2のfull selected LawConflict transferの完了根拠には数えない。
`Measurement.FlatBaseChangeCandidate`はcomparison typeと結論をfieldに持つため、
このTor-object targetの証拠として使用しない。

### SD8 — linear Čech scalar extension

cohomology coefficient changeはlinear cochain complexとflat scalar extensionで固定する。
flat tensorのexactnessからhomology comparisonを構成し、generic theoremへ
finite / projective premiseを追加しない。有限性はSD9の計算可能modelだけで使う。
abstract complexのhomologyとactual `Sheaf.H` coefficient comparisonは別targetにし、
後者はcanonical base-changed coefficient sheaf、degreewise compatibility、source / target Leray comparisonから構成する。

~~~lean
namespace Cohomology

open scoped ChangeOfRings

structure LinearCoverRelativeCechComplex
    (R : Type u) [CommRing R]
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) where
  complex : CoverRelativeCechComplex (canonicalCoverRelative 𝒰) Ob
  moduleStructure : ∀ n, Module R (complex.AdditiveCochain n)
  differential_linear :
    ∀ n, complex.AdditiveCochain n →ₗ[R]
      complex.AdditiveCochain (n + 1)
  differential_linear_apply :
    ∀ n c, differential_linear n c = complex.d n c

attribute [instance] LinearCoverRelativeCechComplex.moduleStructure

noncomputable instance LinearCoverRelativeCechComplex.additiveCechHnModule
    {R : Type u} [CommRing R]
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (n : Nat) :
    Module R (K.complex.AdditiveCechHn n)

noncomputable def LinearCoverRelativeCechComplex.moduleComplex
    {R : Type u} [CommRing R]
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob) :
    CochainComplex (ModuleCat R) Nat

noncomputable def LinearCoverRelativeCechComplex.scalarExtension
    {R R' : Type u} [CommRing R] [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R') :
    CochainComplex (ModuleCat R') Nat :=
  ((ModuleCat.extendScalars f.hom).mapHomologicalComplex
    (ComplexShape.up Nat)).obj K.moduleComplex

noncomputable def LinearCoverRelativeCechComplex.scalarExtensionObjIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    (K.scalarExtension f).X n ≅
    Derived.Intersection.moduleScalarExtension f
      (ModuleCat.of R (K.complex.AdditiveCochain n))

noncomputable def LinearCoverRelativeCechComplex.scalarExtensionCochain
    {R R' : Type u} [CommRing R] [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    ModuleCat.of R (K.complex.AdditiveCochain n) ⟶
      (ModuleCat.restrictScalars f.hom).obj ((K.scalarExtension f).X n) :=
  Derived.Intersection.moduleScalarExtensionUnit f
      (ModuleCat.of R (K.complex.AdditiveCochain n)) ≫
    (ModuleCat.restrictScalars f.hom).map
      (K.scalarExtensionObjIso f n).inv

theorem LinearCoverRelativeCechComplex.scalarExtensionCochain_objIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat)
    (c : K.complex.AdditiveCochain n) :
    (K.scalarExtensionObjIso f n).hom
        (K.scalarExtensionCochain f n c) =
      Derived.Intersection.moduleScalarExtensionUnit f
        (ModuleCat.of R (K.complex.AdditiveCochain n)) c

theorem LinearCoverRelativeCechComplex.scalarExtension_d_apply
    {R R' : Type u} [CommRing R] [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat)
    (c : K.complex.AdditiveCochain n) :
    (K.scalarExtension f).d n (n + 1)
        (K.scalarExtensionCochain f n c) =
      K.scalarExtensionCochain f (n + 1)
        (K.differential_linear n c)

noncomputable def LinearCoverRelativeCechComplex.scalarExtensionCocycle
    {R R' : Type u} [CommRing R] [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    K.complex.CechCocycle n →
      (K.scalarExtension f).cycles n

noncomputable def LinearCoverRelativeCechComplex.moduleHomologyIso
    {R : Type u} [CommRing R]
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (n : Nat) :
    K.moduleComplex.homology n ≅
      ModuleCat.of R (K.complex.AdditiveCechHn n)

noncomputable def LinearCoverRelativeCechComplex.hnFlatBaseChangeIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    Derived.Intersection.moduleScalarExtension f
        (ModuleCat.of R (K.complex.AdditiveCechHn n)) ≅
      (K.scalarExtension f).homology n

noncomputable def LinearCoverRelativeCechComplex.classBaseChange
    {R R' : Type u} [CommRing R] [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat) :
    K.complex.CechCocycle n →
      (K.scalarExtension f).homology n

theorem LinearCoverRelativeCechComplex.classBaseChange_eq_homologyπ
    {R R' : Type u} [CommRing R] [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat)
    (c : K.complex.CechCocycle n) :
    K.classBaseChange f n c =
      (K.scalarExtension f).homologyπ n
        (K.scalarExtensionCocycle f n c)

theorem LinearCoverRelativeCechComplex.class_baseChange_naturality
    {R R' : Type u} [CommRing R] [CommRing R']
    (K : LinearCoverRelativeCechComplex R 𝒰 Ob)
    (f : FlatCoefficientChange R R')
    (n : Nat)
    (c : K.complex.CechCocycle n) :
    (K.hnFlatBaseChangeIso f n).hom
        (Derived.Intersection.moduleScalarExtensionUnit f
          (ModuleCat.of R (K.complex.AdditiveCechHn n))
          (K.complex.additiveCohomologyClass n c)) =
      K.classBaseChange f n c

structure LinearObstructionSheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (R : Type u) [CommRing R]
    (S : Site.AATSite A) where
  toModuleSheaf : Sheaf S.topology (ModuleCat R)

namespace LinearObstructionSheaf

noncomputable def toObstructionSheaf
    {R : Type u} [CommRing R]
    (Ob : LinearObstructionSheaf R S) :
    ObstructionSheaf S

noncomputable def baseChange
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')] :
    LinearObstructionSheaf R' S where
  toModuleSheaf :=
    (Sheaf.composeAndSheafify S.topology
      (ModuleCat.extendScalars f.hom)).obj Ob.toModuleSheaf

noncomputable def baseChangeIdIso
    {R : Type u} [CommRing R]
    (Ob : LinearObstructionSheaf R S)
    [HasSheafify S.topology (ModuleCat R)] :
    (Ob.baseChange (FlatCoefficientChange.refl R)).toModuleSheaf ≅
      Ob.toModuleSheaf

noncomputable def baseChangeCompIso
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology (ModuleCat R')]
    [HasSheafify S.topology (ModuleCat R'')] :
    ((Ob.baseChange f).baseChange g).toModuleSheaf ≅
      (Ob.baseChange (f.comp g)).toModuleSheaf

noncomputable def baseChangeSectionMap
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    (W : S.category) :
    Derived.Intersection.moduleScalarExtension f
        (Ob.toModuleSheaf.val.obj (op W)) ⟶
      (Ob.baseChange f).toModuleSheaf.val.obj (op W)

theorem baseChangeSectionMap_naturality
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    {source target : S.category} (g : source ⟶ target) :
    (ModuleCat.extendScalars f.hom).map
          (Ob.toModuleSheaf.val.map g.op) ≫
        Ob.baseChangeSectionMap f source =
      Ob.baseChangeSectionMap f target ≫
        (Ob.baseChange f).toModuleSheaf.val.map g.op

noncomputable def canonicalLinearCech
    {R : Type u} [CommRing R]
    (Ob : LinearObstructionSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    LinearCoverRelativeCechComplex R 𝒰 Ob.toObstructionSheaf

noncomputable def canonicalCechBaseChangeHom
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    (Ob.canonicalLinearCech 𝒰).scalarExtension f ⟶
      ((Ob.baseChange f).canonicalLinearCech 𝒰).moduleComplex

theorem canonicalCechBaseChangeHom_f_apply
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (c : (Ob.canonicalLinearCech 𝒰).complex.AdditiveCochain n)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    (canonicalCechBaseChangeHom Ob f 𝒰).f n
        ((Ob.canonicalLinearCech 𝒰).scalarExtensionCochain f n c) σ =
      Ob.baseChangeSectionMap f
        ((canonicalCoverRelative 𝒰).overlap n σ)
        (Derived.Intersection.moduleScalarExtensionUnit f
          (Ob.toModuleSheaf.val.obj
            (op ((canonicalCoverRelative 𝒰).overlap n σ)))
          (c σ))

def CechCoefficientBaseChangeCompatible
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) : Prop :=
  ∀ n, IsIso ((canonicalCechBaseChangeHom Ob f 𝒰).f n)

noncomputable def canonicalCechHnBaseChangeMap
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    Derived.Intersection.moduleScalarExtension f
        (ModuleCat.of R
          ((Ob.canonicalLinearCech 𝒰).complex.AdditiveCechHn n)) ⟶
      ModuleCat.of R'
        (((Ob.baseChange f).canonicalLinearCech 𝒰).complex.AdditiveCechHn n)

noncomputable def canonicalCocycleBaseChange
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    (Ob.canonicalLinearCech 𝒰).complex.CechCocycle n →
      ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.CechCocycle n

theorem canonicalCocycleBaseChange_class
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (c : (Ob.canonicalLinearCech 𝒰).complex.CechCocycle n) :
    ((Ob.baseChange f).canonicalLinearCech 𝒰).complex.additiveCohomologyClass n
        (canonicalCocycleBaseChange Ob f 𝒰 n c) =
      canonicalCechHnBaseChangeMap Ob f 𝒰 n
        (Derived.Intersection.moduleScalarExtensionUnit f
          (ModuleCat.of R
            ((Ob.canonicalLinearCech 𝒰).complex.AdditiveCechHn n))
          ((Ob.canonicalLinearCech 𝒰).complex.additiveCohomologyClass n c))

theorem canonicalCechHnBaseChangeMap_isIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hcompat : CechCoefficientBaseChangeCompatible Ob f 𝒰)
    (n : Nat) :
    IsIso (canonicalCechHnBaseChangeMap Ob f 𝒰 n)

noncomputable def canonicalCechHnFlatBaseChangeIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hcompat : CechCoefficientBaseChangeCompatible Ob f 𝒰)
    (n : Nat) :
    Derived.Intersection.moduleScalarExtension f
        (ModuleCat.of R
          ((Ob.canonicalLinearCech 𝒰).complex.AdditiveCechHn n)) ≅
      ModuleCat.of R'
        (((Ob.baseChange f).canonicalLinearCech 𝒰).complex.AdditiveCechHn n)

theorem canonicalCechHnFlatBaseChangeIso_hom
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hcompat : CechCoefficientBaseChangeCompatible Ob f 𝒰)
    (n : Nat) :
    (canonicalCechHnFlatBaseChangeIso Ob f 𝒰 hcompat n).hom =
      canonicalCechHnBaseChangeMap Ob f 𝒰 n

noncomputable def terminalLerayHModule
    {R : Type u} [CommRing R]
    (Ob : LinearObstructionSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (hbase : IsTerminal base)
    (hLeray : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (n : Nat) : ModuleCat R

@[simp] theorem terminalLerayHModule_carrier
    {R : Type u} [CommRing R]
    (Ob : LinearObstructionSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (hbase : IsTerminal base)
    (hLeray : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (n : Nat) :
    (Ob.terminalLerayHModule 𝒰 hbase hLeray n : Type u) =
      (Ob.toObstructionSheaf.toAddCommGrpSheaf).H n

noncomputable def baseChangeIdTerminalLerayHModuleIso
    {R : Type u} [CommRing R]
    (Ob : LinearObstructionSheaf R S)
    [HasSheafify S.topology (ModuleCat R)]
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (htarget : IsLerayFor 𝒰
      (Ob.baseChange (FlatCoefficientChange.refl R)).toObstructionSheaf)
    (n : Nat) :
    (Ob.baseChange (FlatCoefficientChange.refl R)).terminalLerayHModule
        𝒰 hbase htarget n ≅
      Ob.terminalLerayHModule 𝒰 hbase hsource n

noncomputable def baseChangeCompTerminalLerayHModuleIso
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology (ModuleCat R')]
    [HasSheafify S.topology (ModuleCat R'')]
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hiterated : IsLerayFor 𝒰
      ((Ob.baseChange f).baseChange g).toObstructionSheaf)
    (hcomposite : IsLerayFor 𝒰
      (Ob.baseChange (f.comp g)).toObstructionSheaf)
    (n : Nat) :
    ((Ob.baseChange f).baseChange g).terminalLerayHModule
        𝒰 hbase hiterated n ≅
      (Ob.baseChange (f.comp g)).terminalLerayHModule
        𝒰 hbase hcomposite n

noncomputable def cechToSheafHLinearIso
    {R : Type u} [CommRing R]
    (Ob : LinearObstructionSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (hbase : IsTerminal base)
    (hLeray : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (n : Nat) :
    ModuleCat.of R
        ((Ob.canonicalLinearCech 𝒰).complex.AdditiveCechHn n) ≅
      Ob.terminalLerayHModule 𝒰 hbase hLeray n

theorem cechToSheafHLinearIso_hom_apply
    {R : Type u} [CommRing R]
    (Ob : LinearObstructionSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (hbase : IsTerminal base)
    (hLeray : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (n : Nat)
    (x : (Ob.canonicalLinearCech 𝒰).complex.AdditiveCechHn n) :
    (Ob.cechToSheafHLinearIso 𝒰 hbase hLeray n).hom x =
      cechToSheafH 𝒰 Ob.toObstructionSheaf hbase hLeray n x

noncomputable def sheafHFlatBaseChangeMap
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (htarget : IsLerayFor 𝒰 (Ob.baseChange f).toObstructionSheaf)
    (n : Nat) :
    Derived.Intersection.moduleScalarExtension f
        (Ob.terminalLerayHModule 𝒰 hbase hsource n) ⟶
      (Ob.baseChange f).terminalLerayHModule 𝒰 hbase htarget n

theorem sheafHFlatBaseChangeMap_formula
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (htarget : IsLerayFor 𝒰 (Ob.baseChange f).toObstructionSheaf)
    (n : Nat) :
    sheafHFlatBaseChangeMap Ob f 𝒰 hbase hsource htarget n =
      (ModuleCat.extendScalars f.hom).map
          (Ob.cechToSheafHLinearIso 𝒰 hbase hsource n).inv ≫
        canonicalCechHnBaseChangeMap Ob f 𝒰 n ≫
        ((Ob.baseChange f).cechToSheafHLinearIso
          𝒰 hbase htarget n).hom

theorem sheafHFlatBaseChangeMap_on_class
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (htarget : IsLerayFor 𝒰 (Ob.baseChange f).toObstructionSheaf)
    (n : Nat)
    (c : (Ob.canonicalLinearCech 𝒰).complex.CechCocycle n) :
    sheafHFlatBaseChangeMap Ob f 𝒰 hbase hsource htarget n
        (Derived.Intersection.moduleScalarExtensionUnit f
          (Ob.terminalLerayHModule 𝒰 hbase hsource n)
          (cechToSheafH 𝒰 Ob.toObstructionSheaf hbase hsource n
            ((Ob.canonicalLinearCech 𝒰).complex.additiveCohomologyClass n c))) =
      cechToSheafH 𝒰 (Ob.baseChange f).toObstructionSheaf
        hbase htarget n
        (((Ob.baseChange f).canonicalLinearCech 𝒰).complex.additiveCohomologyClass n
          (canonicalCocycleBaseChange Ob f 𝒰 n c))

theorem sheafHFlatBaseChangeMap_isIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hcompat : CechCoefficientBaseChangeCompatible Ob f 𝒰)
    (hsource : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (htarget : IsLerayFor 𝒰 (Ob.baseChange f).toObstructionSheaf)
    (n : Nat) :
    IsIso (sheafHFlatBaseChangeMap Ob f 𝒰 hbase hsource htarget n)

noncomputable def sheafHFlatBaseChangeIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hcompat : CechCoefficientBaseChangeCompatible Ob f 𝒰)
    (hsource : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (htarget : IsLerayFor 𝒰 (Ob.baseChange f).toObstructionSheaf)
    (n : Nat) :
    Derived.Intersection.moduleScalarExtension f
        (Ob.terminalLerayHModule 𝒰 hbase hsource n) ≅
      (Ob.baseChange f).terminalLerayHModule 𝒰 hbase htarget n

theorem sheafHFlatBaseChangeIso_hom
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology (ModuleCat R')]
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hcompat : CechCoefficientBaseChangeCompatible Ob f 𝒰)
    (hsource : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (htarget : IsLerayFor 𝒰 (Ob.baseChange f).toObstructionSheaf)
    (n : Nat) :
    (sheafHFlatBaseChangeIso Ob f 𝒰 hbase hcompat hsource htarget n).hom =
      sheafHFlatBaseChangeMap Ob f 𝒰 hbase hsource htarget n

@[simp] theorem sheafHFlatBaseChangeMap_id
    {R : Type u} [CommRing R]
    (Ob : LinearObstructionSheaf R S)
    [HasSheafify S.topology (ModuleCat R)]
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (htarget : IsLerayFor 𝒰
      (Ob.baseChange (FlatCoefficientChange.refl R)).toObstructionSheaf)
    (n : Nat) :
    sheafHFlatBaseChangeMap Ob (FlatCoefficientChange.refl R)
          𝒰 hbase hsource htarget n ≫
        (Ob.baseChangeIdTerminalLerayHModuleIso
          𝒰 hbase hsource htarget n).hom =
      (Derived.Intersection.moduleScalarExtensionIdIso
        (Ob.terminalLerayHModule 𝒰 hbase hsource n)).hom

theorem sheafHFlatBaseChangeMap_comp
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : LinearObstructionSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology (ModuleCat R')]
    [HasSheafify S.topology (ModuleCat R'')]
    [HasSheafify S.topology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.topology AddCommGrpCat.{u})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLerayFor 𝒰 Ob.toObstructionSheaf)
    (hmiddle : IsLerayFor 𝒰 (Ob.baseChange f).toObstructionSheaf)
    (hiterated : IsLerayFor 𝒰
      ((Ob.baseChange f).baseChange g).toObstructionSheaf)
    (hcomposite : IsLerayFor 𝒰
      (Ob.baseChange (f.comp g)).toObstructionSheaf)
    (n : Nat) :
    (ModuleCat.extendScalars g.hom).map
          (sheafHFlatBaseChangeMap Ob f
            𝒰 hbase hsource hmiddle n) ≫
        sheafHFlatBaseChangeMap (Ob.baseChange f) g
          𝒰 hbase hmiddle hiterated n ≫
        (Ob.baseChangeCompTerminalLerayHModuleIso f g
          𝒰 hbase hiterated hcomposite n).hom =
      (Derived.Intersection.moduleScalarExtensionCompIso f g
          (Ob.terminalLerayHModule 𝒰 hbase hsource n)).hom ≫
        sheafHFlatBaseChangeMap Ob (f.comp g)
          𝒰 hbase hsource hcomposite n

end Cohomology
~~~

`moduleScalarExtension`はMathlibの`ModuleCat.extendScalars`を直接使い、canonical unitは
`extendRestrictScalarsAdj`のunitで固定する。`scalarExtensionCochain`はこのunitと
`scalarExtensionObjIso`の逆射から構成し、caller-supplied mapにしない。
`scalarExtensionObjIso`と`scalarExtension_d_apply`がcochain objectとdifferentialの
scalar-extension formulaを検査する。`scalarExtensionCocycle`からactual homology classを作り、
`classBaseChange`を任意関数として選ばない。
`LinearObstructionSheaf.baseChange`はobjectwise scalar extension後のsheafificationから
target coefficient sheafをcanonicalに生成する。`canonicalCechBaseChangeHom`も
sheafification unitと`baseChangeSectionMap_naturality`から構成し、complex homやHn mapを入力しない。
`CechCoefficientBaseChangeCompatible`はこのcanonical complex homのdegreewise `IsIso`だけを要求する。
一般のcomparison mapは`sheafHFlatBaseChangeMap`、compatibilityが放電された場合のisoは
そのmapを同型化した`sheafHFlatBaseChangeIso`であり、SD5のLeray comparisonを介して
Mathlib actual `Sheaf.H`へ到達する。
恒等・合成係数写像では、sheafification後のcoefficient sheafとscalar extensionは
definitionally同一視せず、`baseChangeIdIso` / `baseChangeCompIso`、
`moduleScalarExtensionIdIso` / `moduleScalarExtensionCompIso`を介して
`sheafHFlatBaseChangeMap_id` / `sheafHFlatBaseChangeMap_comp`を証明する。

### SD9 — material premise分類とnondegenerate reference models

#### Material premise分類

| premise / data | 三分類 | generic APIでの役割 | completionでの放電 |
| --- | --- | --- | --- |
| `U`、`AATCorePackage U` | 本文由来 | core readingとgenerated object algebra | merged core APIを使用し、別object algebraを入力しない |
| `SelectedGeometryReading core` | 本文由来 | context category、coverage、overlap | `toAATSite`からsiteを生成する |
| coefficient ring / `CommRing` | 本文由来 | Appendix A.2の`k` | finite modelでは`Int`と`Polynomial Int` |
| `RawAmbientRestrictionSystem` | 本文由来 | coordinate / relation / restriction reading | coefficient base changeは係数写像からcanonicalに生成 |
| `SemanticLawEquationWitnessIdealCore` / source bridge / `IsSemanticLawEquationSchemeBridge` | 本文由来 / `ClosedEquationalGeometry` dependency | source global equations、law-index provenance、restriction naturality、canonical chart presentation | source `B`からglobal equationsを生成し、`hB`を`semanticCoreIdealSheaf_realized`と`semanticCoreLawWitnessIdeal_baseChangedChart`でproof-useする。finite modelでは`coefficientBridge_valid`で放電し、target rawのbridgeへ同じ`G`を再利用しない |
| `SemanticCoreIdealSheafRealized` | 放電済み | existing semantic coreのactual chart ideal-sheaf realization | Part 3の`semanticCoreIdealSheaf_realized raw X G B hB`から独立に導出する。input fieldや追加premiseとして受け取らず、aggregate ideal base-change equalityのproof provenanceとは呼ばない |
| `SignedExactCoreReadingHom`のprimitive maps | 本文由来 | extraction、object、law、query、operation、invariant、signature transport | nonidentity finite modelで各mapとcompatibilityを構成 |
| completed `ObjectAlgebraHom` | 放電済み | exact core changeの結論 | `toObjectAlgebraHom`で生成。input field禁止 |
| positive base reachability | 本文由来 | `theta_Obj`がtarget coreのactual object familyへ入るための最小compatibility | finite modelの具体operation pathで`base_reachable`を構成し、一般objectは`mapReachable`で帰納的に生成 |
| positive matching / acceptance implication | 本文由来 | positive-only transport | positive finite queryの式から証明 |
| negative-query reflection | 本文由来 / exactだけ | signed exact transport | `matches_iff`で使用。positive homには要求しない |
| `IsClosedEquationalLawInclusion` | 本文由来 |同一`raw` / `X`上のselected law strengthening | merged primitive law/atom mapとvalidityを直接再利用 |
| ideal inclusion / closed immersion / semantic monotonicity | 放電済み | `ClosedEquationalGeometry`の結論 | merged theoremを直接参照し、new fieldにしない |
| `CoverageTopologyRefinement.refineCover` | 本文由来 | `J'`が`J`の各coverをactualに細分するdata | finite topology modelで具体sieve inclusionを構成 |
| `CommonCoefficientSheaf` | 本文由来 | chosen coefficientがcoarse / fine両topologyでsheafになるcompatibility | 同一presheafと二つのactual sheaf proofをfinite modelで構成 |
| topology-change Ext functor data | 放電済み | `Sheaf.H` comparison | `r.le`から`coarseRestriction`を構成し、`fineSheafificationAdjunction`、left-exact sheafification、pointwise additive forget / `presheafToSheaf_additive`から加法性・有限極限/余極限保存を別々に導く。二つのisoと`mapExtAddHom`から具体合成を生成 |
| cover simplex / overlap / face map | 放電済み | selected cover refinement | `AATCoverageFamily`と`S.overlap`の反復からcanonicalに生成 |
| canonical differential / `d² = 0` | 放電済み | Čech complex | restrictionの交代和とsimplicial identityから証明 |
| cochain hom / Hn map / class equality | 放電済み | refinementの結論 | `Refinement`から生成。field禁止 |
| Leray acyclicity | 本文由来 | cover-relative Čechからactual `Sheaf.H'`への接続 | named finite sheaf / coverでpositive-degree vanishingを証明 |
| Čech-to-sheaf comparison map / bijectivity | 放電済み | SD5の結論 | Leray proofから生成。field禁止 |
| terminal base / `terminalHComparison` | 本文のglobal cohomology対象 / 放電済み | `Sheaf.H'`からglobal `Sheaf.H`への特殊化 | terminal objectのuniversal propertyとExtから比較を構成。iso input禁止 |
| `HasSheafify` / `HasExt` | 本文由来のambient premise | actual `Sheaf.H`とcanonical module-valued sheafification | generic APIで明示し、finite modelでnamed instance chainを記録。`Sheaf.composeAndSheafify`とsheafification unitをproof-useする |
| `FlatCoefficientChange.hom` / `flat` | 本文由来 | Appendix A.2.1の`k → k'` | positive例は`Int → Polynomial Int`、negative例はnon-flat map |
| `S.topology.HasSheafCompose f.coefficientExtension`（coefficient categoriesのuniverseを明示） | 本文由来のcoefficient compatibility | scalar extensionが選択siteのsheafをsheafへ送る条件 | generic scheme-level APIで明示し、finite coefficient modelではnamed instance `coefficientExtension_hasSheafCompose`を有限matching計算から証明する。flatnessによる有限極限保存だけで無条件導出しない |
| raw presheaf / sheafified section-object / Spec pullback iso | 放電済み | affine chart domainとactual pullbackの比較 | structural quotientから`baseChangePresheafIso`を構成し、`HasSheafCompose`、left-adjoint由来の`PreservesSheafification`、`sheafifyComposeIso`からUnder-object isoを導く。さらにcommon-universeのcoefficient category内で`pullbackSpecIso`からSpec pullback isoを構成し、comparison isoを入力しない |
| changed raw / scheme / reading | 放電済み | coefficient changeの出力 | rawはring homから、schemeは上記sheaf compatibilityの下で`baseChange`から、readingはsource global equationsの`baseChangeMap.appTop`像から生成。field禁止 |
| existing-core per-law chart transport | 放電済み | source semantic coreとtarget law-witness idealのcoefficient comparison | `hB`から導くPart 3 chart realization、`baseChangedChart_isPullback`、`IdealSheafData.comap_comp`を`semanticCoreLawWitnessIdeal_baseChangedChart`で同じequalityへ接続する |
| required / all-selected ideal extension equality | 放電済み | aggregate ideal comparison | global equationsのpullback、generator map、restriction、`IdealSheafData.comap`から証明する。数学的に不要な`hB`を受け取らない |
| lawful-locus mapとtriangle | 放電済み | scheme comparison | aggregate ideal equalityから生成し、数学的に不要な`hB`を受け取らない。existing-core provenanceは別のper-law chart theoremで追跡する |
| affine Tor-object base-change iso | 放電済み | 第VIII部9.2のbare affine displayを強化する独立target | `CategoryTheory.Tor`とflat tensor exactnessから構成し、finite firingではsource witnessのcanonical unit像をこのisoでtargetへ送る。selected coefficient / support transferの証拠には数えない |
| linear Čech terms / flat tensor exactness | 本文由来 | scalar-extension theorem | module-valued differentialと`FlatCoefficientChange.flat`から証明 |
| `LinearObstructionSheaf` / canonical `baseChange` | 本文由来 | source coefficientとbase-changed target coefficient | module-valued sheafから生成し、target sheafをcallerから受けない |
| `CechCoefficientBaseChangeCompatible` | 本文由来 | Appendix A.2.1のcoefficient compatibility | canonical complex homのcomponentだけを検査し、map / isoをfieldとして受けない。finite modelではflat extensionのfinite-limit preservationで放電 |
| `terminalLerayHModule` / `cechToSheafHLinearIso` | 放電済み | actual `Sheaf.H`のmodule carrierとČech comparison | `cechToSheafH_bijective`と`AddEquiv.module`から生成 |
| base-change unit / compositor iso | 放電済み | coefficient sheafとactual H mapのidentity / composition | `Sheaf.composeAndSheafify`と`ModuleCat.extendScalars`のunit / compositorから生成し、definitionally同一視しない |
| finite Čech model | firing限定 | nonzero計算とcanonical coefficient compatibilityの放電 | abstract complex theoremの明示引数やtypeclassへ追加しない |
| `ConditionalSpaceCohomology`、selected H1 comparison field | 未放電 | completion routeに使用不可 | final source scanで主経路からzero |
| `Measurement.FlatBaseChangeCandidate` | 未放電 | completion evidenceに使用不可 | final source scanで依存zero |
| comparison map / iso / class equalityのinput field | 未放電 | generic / completion theoremとも禁止 | declaration inventoryに一件あればReject |

実装完了時に、全target declarationの明示引数、typeclass、structure field、certificate fieldを
この表と突合する。tracking Issueのfinal packetには各premiseのdeclaration、放電元、
proof-use、主結論への寄与、finite firingまたはMathlib sourceを記録する。
`material_premise_ledger_delta = ∅`かつ`new_material_premise = ∅`を要求する。

#### Firing matrix

| lane | positive declaration | negative declaration | 非退化条件 |
| --- | --- | --- | --- |
| exact core | `nonidentityExactCoreChange`、`nonidentityExactCoreChange_fires` | `positiveOnly_not_signedExact` | object / law / query mapの少なくとも一つがidentityでない。negative query反射の差を検出 |
| positive core | `positiveCoreChange`、`positiveQuery_mem`、`positiveCircuit_queries_nonempty`、`positiveBase_target_reachable`、`positiveCircuit_transport` | `negativeCircuit_not_transportable` | actual positive queryを一件以上持ち、actual target algebra objectへ運ぶ。negative queryを含む回路は運べない |
| law | `ClosedEquationalGeometry`の`weakToStrong`、`weakToStrong_valid`、`weak_ideal_lt_strong`、`weakToStrongMap_not_isIso`、`weakToStrongAllMap_not_isIso` | `coordinateBrokenInclusion_not_valid` | required / all-selected双方のstrict ideal comparisonとnon-iso closed immersion |
| topology / cover | `coarseFineTopologyRefinement`、`coarseFineTopologyRefinement_selects_fineCover`、`coarseToFineCover`、`coarseToFineCechHom_nonzero` | `brokenFaceMap_not_refinement` | topology refinementが返すactual sieveがselected `fineCover`の生成sieveと一致し、fine-to-coarse index mapが全単射でなく、cochain mapが非零 |
| sheaf H | `finiteLerayCover`、`finite_cechToSheafH_bijective` | `nonLerayCover_not_completionEvidence` | actual `Sheaf.H`を参照し、cover-relative aliasを使わない |
| coefficient geometry | `intPolynomialFlatChange`、`coefficientExtension_hasSheafCompose`、`coefficientSectionSpecBaseChangeIso_fires`、`coefficientSemanticCore_realized`、`coefficientSemanticCore_baseChangedChart`、`properIdeal_baseChange`、`lawfulLocus_baseChange_fires` | `intZModTwo_not_flat`、`brokenRelationChange_not_rawBaseChange` | site-dependent sheaf compatibility、source existing-core realization、per-law chart transport、proper ideal、nonidentity scheme mapを同じ係数変更で放電 |
| Tor | `modTwoTorOneBaseChangeIso`、`modTwoTorOneSourceWitness_ne_zero`、`modTwoTorOneTargetWitness_ne_zero`、`modTwoTorOne_baseChange_nonzero` | `intZModTwo_not_flat` | `Tor₁^Int(Int/2,Int/2)`のnonzero witnessをcanonical unitとgeneric base-change isoで`Int[X]`へ送り、その像が非零 |
| linear Čech | `finiteClass_baseChange_nonzero` | `zeroClass_not_firing` | finite model上のnonzero classとnonidentity scalar extension |
| invariant transport predicate | `Invariant.transportedAlong_refl`とexact core change内のfunction / predicate同種transport | `Invariant.function_predicate_not_transportedAlong` | constructor不一致のとき`TransportedAlong`が不成立 |
| actual coefficient H | `finiteCechCoefficientCompatible`、`finiteTargetLerayCover`、`finiteSheafHBaseChangeMap`、`finiteSheafHBaseChangeIso`、`finiteSheafHClass_baseChange_nonzero` | `infiniteProductCech_not_compatible`、`intZModTwo_not_flat`、`zeroClass_not_firing` | canonical source / base-changed target coefficientとsource / target Leray proofを使い、actual `Sheaf.H` classのcanonical unit像が非零。infinite duplicated coverではflat scalar extensionが無限積と可換でないことを検出 |

identity、zero ideal、zero complex、duplicated coverだけを主証拠にしない。
`Int → Rat`はtorsion classを消す例があるため、Tor laneのpositive modelには使用しない。

firing declarationの型は次で固定する。model dataを一つのcertificate structureへまとめず、
各definitionをprimitive finite dataから構成し、各nonidentity / nonzero theoremを別に証明する。

~~~lean
namespace ReadingFunctorialityFinite

noncomputable def exactSourceCore :
    AATCorePackage FiniteModel.carrier

noncomputable def exactTargetCore :
    AATCorePackage FiniteModel.carrier

noncomputable def nonidentityExactCoreChange :
    SignedExactCoreReadingHom exactSourceCore exactTargetCore

theorem nonidentityExactCoreChange_fires :
    nonidentityExactCoreChange.atomMap ≠ id

noncomputable def positiveSourceCore :
    AATCorePackage FiniteModel.carrier

noncomputable def positiveTargetCore :
    AATCorePackage FiniteModel.carrier

noncomputable def positiveCoreChange :
    PositiveCoreReadingHom positiveSourceCore positiveTargetCore

noncomputable def positiveLawIndex :
    positiveSourceCore.algebra.lawReading.lawUniverse.Index

noncomputable def positiveCircuit :
    PositiveCircuitDatum positiveSourceCore
      positiveSourceCore.baseObject positiveLawIndex

noncomputable def positiveQuery : CircuitQuery FiniteModel.carrier

theorem positiveQuery_mem :
    (positiveQuery, true) ∈ positiveCircuit.1.queries

theorem positiveCircuit_queries_nonempty :
    positiveCircuit.1.queries.Nonempty

def positiveCircuit_transport :
    PositiveCircuitDatum positiveTargetCore
      (positiveCoreChange.objMap positiveSourceCore.baseObject)
      (positiveCoreChange.lawMap positiveLawIndex) :=
  positiveCoreChange.mapPositiveCircuit positiveCircuit

theorem positiveBase_target_reachable :
    positiveTargetCore.reading.operationReading.Reachable
      positiveTargetCore.object
      (positiveCoreChange.objectMap positiveSourceCore.object) :=
  positiveCoreChange.base_reachable

theorem positiveOnly_not_signedExact :
    ¬ Nonempty
      (SignedExactCoreReadingHom positiveSourceCore positiveTargetCore)

noncomputable def negativeCircuit : FiniteCircuitDatum FiniteModel.carrier

theorem negativeCircuit_not_positive : ¬ negativeCircuit.Positive

theorem negativeCircuit_not_transportable :
    ¬ ∃ target : FiniteCircuitDatum FiniteModel.carrier,
      ∀ A,
        negativeCircuit.Matches A ↔
          target.Matches (positiveCoreChange.objectMap A)

noncomputable def finiteSite :
    Site.AATSite FiniteModel.corePackage.object

noncomputable def finiteBase : finiteSite.category

noncomputable def coarseTopology :
    GrothendieckTopology finiteSite.category :=
  finiteSite.topology

@[simp] theorem coarseTopology_eq_site :
    coarseTopology = finiteSite.topology := rfl

noncomputable def fineTopology :
    GrothendieckTopology finiteSite.category

def nonzeroDegree : Nat := 1

noncomputable def coarseCover :
    Site.AATCoverageFamily finiteSite.requirements
      finiteSite.overlap finiteBase

noncomputable def fineCover :
    Site.AATCoverageFamily finiteSite.requirements
      finiteSite.overlap finiteBase

noncomputable def coarseToFineCover :
    Site.AATCoverageFamily.Refinement coarseCover fineCover

theorem coarseToFineCover_not_bijective :
    ¬ Function.Bijective coarseToFineCover.indexMap

noncomputable def finiteLinearObstructionSheaf :
    Cohomology.LinearObstructionSheaf Int finiteSite

noncomputable def finiteObstructionSheaf :
    Cohomology.ObstructionSheaf finiteSite :=
  finiteLinearObstructionSheaf.toObstructionSheaf

theorem coarseToFineCechHom_nonzero :
    ∃ (n : Nat)
      (c : (Cohomology.canonicalCechComplex
        coarseCover finiteObstructionSheaf).AdditiveCochain n)
      (σ : (Cohomology.canonicalCoverRelative fineCover).simplex n),
      (coarseToFineCover.canonicalCechHom finiteObstructionSheaf).app n c σ ≠ 0

noncomputable def brokenFaceMap :
    ∀ n,
      (Cohomology.canonicalCoverRelative fineCover).simplex n →
        (Cohomology.canonicalCoverRelative coarseCover).simplex n

theorem brokenFaceMap_not_refinement :
    ¬ ∃ r : Site.AATCoverageFamily.Refinement coarseCover fineCover,
      r.simplexMap = brokenFaceMap

noncomputable def coarseFineTopologyRefinement :
    CoverageTopologyRefinement coarseTopology fineTopology

theorem coarseFineTopology_strict : coarseTopology ≠ fineTopology

theorem coarseCover_mem_coarseTopology :
    Sieve.generate coarseCover.presieve ∈ coarseTopology finiteBase

theorem coarseFineTopologyRefinement_selects_fineCover :
    (coarseFineTopologyRefinement.refineCover
      finiteBase (Sieve.generate coarseCover.presieve)
      coarseCover_mem_coarseTopology).1 =
        Sieve.generate fineCover.presieve

theorem fineCover_mem_fineTopology :
    Sieve.generate fineCover.presieve ∈ fineTopology finiteBase

theorem finiteLerayCover :
    Cohomology.IsLerayFor coarseCover finiteObstructionSheaf

noncomputable def finiteBaseIsTerminal : IsTerminal finiteBase

theorem finite_cechToSheafH_bijective (n : Nat) :
    Function.Bijective
      (Cohomology.cechToSheafH coarseCover finiteObstructionSheaf
        finiteBaseIsTerminal finiteLerayCover n)

noncomputable def nonLerayCover :
    Site.AATCoverageFamily finiteSite.requirements
      finiteSite.overlap finiteBase

theorem nonLerayCover_not_completionEvidence :
    ¬ Cohomology.IsLerayFor nonLerayCover finiteObstructionSheaf

noncomputable def topologyCoefficient :
    CommonCoefficientSheaf coarseTopology fineTopology

theorem coarseFineSheafHMap_nonzero :
    coarseFineTopologyRefinement.sheafHMap topologyCoefficient nonzeroDegree ≠ 0

noncomputable def intPolynomialFlatChange :
    FlatCoefficientChange Int (Polynomial Int)

@[simp] theorem intPolynomialFlatChange_hom :
    intPolynomialFlatChange.hom = Polynomial.C

theorem intPolynomialFlatChange_nonidentity :
    ¬ Function.Surjective intPolynomialFlatChange.hom

noncomputable instance finiteCoarseCoverIndexFintype :
    Fintype coarseCover.Index

noncomputable def finiteBaseChangedLinearObstructionSheaf :
    Cohomology.LinearObstructionSheaf (Polynomial Int) finiteSite :=
  finiteLinearObstructionSheaf.baseChange intPolynomialFlatChange

theorem finiteCechCoefficientCompatible :
    Cohomology.LinearObstructionSheaf.CechCoefficientBaseChangeCompatible
      finiteLinearObstructionSheaf intPolynomialFlatChange coarseCover

noncomputable def intRationalFlatChange :
    FlatCoefficientChange Int Rat

@[simp] theorem intRationalFlatChange_hom :
    intRationalFlatChange.hom = algebraMap Int Rat

noncomputable def infiniteDuplicatedCover :
    Site.AATCoverageFamily finiteSite.requirements
      finiteSite.overlap finiteBase

noncomputable def infiniteDuplicatedCoverIndexEquiv :
    infiniteDuplicatedCover.Index ≃ Nat

noncomputable def infiniteProductLinearObstructionSheaf :
    Cohomology.LinearObstructionSheaf Int finiteSite

theorem infiniteProductCech_not_compatible :
    ¬ Cohomology.LinearObstructionSheaf.CechCoefficientBaseChangeCompatible
      infiniteProductLinearObstructionSheaf intRationalFlatChange
        infiniteDuplicatedCover

theorem infiniteProductCech_degreeZero_not_isIso :
    ¬ IsIso
      ((Cohomology.LinearObstructionSheaf.canonicalCechBaseChangeHom
        infiniteProductLinearObstructionSheaf intRationalFlatChange
          infiniteDuplicatedCover).f 0)

theorem finiteTargetLerayCover :
    Cohomology.IsLerayFor coarseCover
      finiteBaseChangedLinearObstructionSheaf.toObstructionSheaf

noncomputable def properIdeal : Ideal Int

theorem properIdeal_eq : properIdeal = Ideal.span {2}

theorem properIdeal_ne_top : properIdeal ≠ ⊤

theorem properIdeal_baseChange :
    properIdeal.map intPolynomialFlatChange.hom ≠ ⊤

noncomputable def coefficientRaw :
    LawAlgebra.RawAmbientRestrictionSystem finiteSite Int

noncomputable local instance coefficientExtension_hasSheafCompose :
    finiteSite.topology.HasSheafCompose
      (intPolynomialFlatChange.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{0, 0} Int ⥤
          LawAlgebra.AATCommAlgCat.{0, 0} (Polynomial Int))

noncomputable def coefficientSectionSpecBaseChangeIso_fires :
    LawAlgebra.architectureChartSpec
        (coefficientRaw.baseChange intPolynomialFlatChange.hom) finiteBase ≅
      pullback
        (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom
            (LawAlgebra.sheafifiedSectionAlgebraMap
              coefficientRaw finiteBase)).op)
        (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom intPolynomialFlatChange.hom).op) :=
  LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso
    coefficientRaw intPolynomialFlatChange finiteBase

noncomputable def coefficientScheme :
    LawAlgebra.StandardArchitectureScheme coefficientRaw

noncomputable def coefficientSemanticCore :
    LawAlgebra.SemanticLawEquationWitnessIdealCore finiteSite

noncomputable def coefficientBridge :
    LawAlgebra.SemanticLawEquationSchemeBridge
      coefficientRaw coefficientSemanticCore

theorem coefficientBridge_valid :
    LawAlgebra.IsSemanticLawEquationSchemeBridge
      coefficientRaw coefficientSemanticCore coefficientBridge

theorem coefficientSemanticCore_realized :
    LawAlgebra.SemanticCoreIdealSheafRealized
      coefficientRaw coefficientScheme coefficientSemanticCore coefficientBridge :=
  LawAlgebra.semanticCoreIdealSheaf_realized
    coefficientRaw coefficientScheme coefficientSemanticCore
      coefficientBridge coefficientBridge_valid

theorem coefficientSemanticCore_baseChangedChart
    (j : coefficientScheme.atlas.Index)
    (i : finiteSite.lawUniverse.Index) :
    let R' :=
      LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore
        coefficientRaw coefficientScheme coefficientSemanticCore
          coefficientBridge intPolynomialFlatChange
    let hR' :=
      (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
        coefficientRaw coefficientScheme coefficientSemanticCore
          coefficientBridge intPolynomialFlatChange).witness_compatible
    let j' := cast
      (coefficientScheme.baseChangedAtlas_Index
        coefficientRaw intPolynomialFlatChange).symm j
    Scheme.IdealSheafData.comap
        (Scheme.IdealSheafData.ofIdealTop
          (X := (coefficientScheme.atlas.chart j).domain)
          (Ideal.map
            (AlgebraicGeometry.Scheme.ΓSpecIso
              (LawAlgebra.SheafifiedSectionRing coefficientRaw
                (coefficientScheme.atlas.chart j).context)).inv.hom
            (Ideal.map
              (coefficientBridge.toSheafifiedSection
                (coefficientScheme.atlas.chart j).context)
              (coefficientSemanticCore.lawWitnessIdeal
                (coefficientScheme.atlas.chart j).context i))))
        (coefficientScheme.baseChangedChartMap
          coefficientRaw intPolynomialFlatChange j) =
      Scheme.IdealSheafData.comap
        (LawAlgebra.lawWitnessIdealSheaf
          (coefficientRaw.baseChange intPolynomialFlatChange.hom)
          (coefficientScheme.baseChange
            coefficientRaw intPolynomialFlatChange)
          R' hR' i (Set.mem_univ i))
        ((coefficientScheme.baseChangedAtlas
          coefficientRaw intPolynomialFlatChange).chart j').map :=
  LawAlgebra.semanticCoreLawWitnessIdeal_baseChangedChart
    coefficientRaw coefficientScheme coefficientSemanticCore
      coefficientBridge coefficientBridge_valid intPolynomialFlatChange j i

theorem lawfulLocus_baseChange_fires :
    LawAlgebra.SemanticCoreIdealSheafRealized
        coefficientRaw coefficientScheme coefficientSemanticCore coefficientBridge ∧
    ¬ IsIso
      (LawAlgebra.lawfulClosedSubschemeBaseChangeMap
        coefficientRaw coefficientScheme coefficientSemanticCore
        coefficientBridge intPolynomialFlatChange)

noncomputable def intZModTwo : Int →+* ZMod 2 :=
  Int.castRingHom (ZMod 2)

theorem intZModTwo_not_flat : ¬ intZModTwo.Flat

noncomputable def brokenRelationChange :
    LawAlgebra.RawAmbientRestrictionSystem finiteSite (Polynomial Int)

theorem brokenRelationChange_not_rawBaseChange :
    brokenRelationChange ≠
      coefficientRaw.baseChange intPolynomialFlatChange.hom

noncomputable def modTwoTorOneBaseChangeIso :
    Derived.Intersection.moduleScalarExtension intPolynomialFlatChange
        (Derived.Intersection.mathlibTor Int properIdeal properIdeal 1) ≅
      Derived.Intersection.mathlibTor (Polynomial Int)
        (properIdeal.map intPolynomialFlatChange.hom)
        (properIdeal.map intPolynomialFlatChange.hom) 1 :=
  Derived.Intersection.mathlibTorFlatBaseChangeIso
    intPolynomialFlatChange properIdeal properIdeal 1

noncomputable def modTwoTorOneSourceWitness :
    Derived.Intersection.mathlibTor Int properIdeal properIdeal 1

theorem modTwoTorOneSourceWitness_ne_zero :
    modTwoTorOneSourceWitness ≠ 0

noncomputable def modTwoTorOneTargetWitness :
    Derived.Intersection.mathlibTor (Polynomial Int)
      (properIdeal.map intPolynomialFlatChange.hom)
      (properIdeal.map intPolynomialFlatChange.hom) 1 :=
  modTwoTorOneBaseChangeIso.hom
    (Derived.Intersection.moduleScalarExtensionUnit
      intPolynomialFlatChange
      (Derived.Intersection.mathlibTor Int properIdeal properIdeal 1)
      modTwoTorOneSourceWitness)

theorem modTwoTorOneTargetWitness_ne_zero :
    modTwoTorOneTargetWitness ≠ 0

theorem modTwoTorOne_baseChange_nonzero :
    Nontrivial
      (Derived.Intersection.mathlibTor (Polynomial Int)
        (properIdeal.map intPolynomialFlatChange.hom)
        (properIdeal.map intPolynomialFlatChange.hom) 1) :=
  nontrivial_iff.mpr
    ⟨modTwoTorOneTargetWitness, 0, modTwoTorOneTargetWitness_ne_zero⟩

noncomputable def finiteLinearCech :
    Cohomology.LinearCoverRelativeCechComplex Int
      coarseCover finiteObstructionSheaf :=
  finiteLinearObstructionSheaf.canonicalLinearCech coarseCover

def finiteDegree : Nat := 1

noncomputable def finiteCocycle :
    finiteLinearCech.complex.CechCocycle finiteDegree

noncomputable def finiteActualSourceClass :
    finiteLinearObstructionSheaf.terminalLerayHModule
      coarseCover finiteBaseIsTerminal finiteLerayCover finiteDegree :=
  Cohomology.cechToSheafH coarseCover finiteObstructionSheaf
    finiteBaseIsTerminal finiteLerayCover finiteDegree
    (finiteLinearCech.complex.additiveCohomologyClass
      finiteDegree finiteCocycle)

noncomputable def finiteSheafHBaseChangeMap :
    Derived.Intersection.moduleScalarExtension intPolynomialFlatChange
        (finiteLinearObstructionSheaf.terminalLerayHModule
          coarseCover finiteBaseIsTerminal finiteLerayCover finiteDegree) ⟶
      finiteBaseChangedLinearObstructionSheaf.terminalLerayHModule
        coarseCover finiteBaseIsTerminal finiteTargetLerayCover finiteDegree :=
  Cohomology.LinearObstructionSheaf.sheafHFlatBaseChangeMap
    finiteLinearObstructionSheaf intPolynomialFlatChange coarseCover
    finiteBaseIsTerminal finiteLerayCover finiteTargetLerayCover finiteDegree

noncomputable def finiteSheafHBaseChangeIso :
    Derived.Intersection.moduleScalarExtension intPolynomialFlatChange
        (finiteLinearObstructionSheaf.terminalLerayHModule
          coarseCover finiteBaseIsTerminal finiteLerayCover finiteDegree) ≅
      finiteBaseChangedLinearObstructionSheaf.terminalLerayHModule
        coarseCover finiteBaseIsTerminal finiteTargetLerayCover finiteDegree :=
  Cohomology.LinearObstructionSheaf.sheafHFlatBaseChangeIso
    finiteLinearObstructionSheaf intPolynomialFlatChange coarseCover
    finiteBaseIsTerminal finiteCechCoefficientCompatible
    finiteLerayCover finiteTargetLerayCover finiteDegree

theorem finiteSheafHBaseChangeIso_hom :
    finiteSheafHBaseChangeIso.hom = finiteSheafHBaseChangeMap :=
  Cohomology.LinearObstructionSheaf.sheafHFlatBaseChangeIso_hom
    finiteLinearObstructionSheaf intPolynomialFlatChange coarseCover
    finiteBaseIsTerminal finiteCechCoefficientCompatible
    finiteLerayCover finiteTargetLerayCover finiteDegree

theorem finiteClass_baseChange_nonzero :
    finiteLinearCech.classBaseChange intPolynomialFlatChange
      finiteDegree finiteCocycle ≠ 0

theorem finiteSheafHClass_baseChange_nonzero :
    finiteSheafHBaseChangeMap
        (Derived.Intersection.moduleScalarExtensionUnit
          intPolynomialFlatChange
          (finiteLinearObstructionSheaf.terminalLerayHModule
            coarseCover finiteBaseIsTerminal finiteLerayCover finiteDegree)
          finiteActualSourceClass) ≠ 0

theorem zeroClass_not_firing :
    finiteLinearCech.classBaseChange intPolynomialFlatChange
      finiteDegree 0 = 0

end ReadingFunctorialityFinite
~~~

## 数学本文との対応

| 数学本文 | fixed target | 完了時の読み方 |
| --- | --- | --- |
| 第I部 原則10.6 | SD1 | exact signed changeからactual `ObjectAlgebraHom`を構成し、positive changeはpositive circuitだけを運ぶ |
| Appendix A.2 | SD0 | generated core、selected geometry、coefficient ring、raw readingを一つのtyped provenanceで読む |
| Appendix A.2.1 law inclusion | SD2 | 同一standard geometry内のselected closed-law strengtheningについて`ClosedEquationalGeometry`のactual ideal / closed geometry mapを直接再利用 |
| 第II部 `5.3 Refinement`、定義7.1〜7.2、Appendix A.2.1 coverage | SD3〜SD5 | generated topologyのactual cover membership、topology refinement、selected adequate cover refinement、Čech map、actual `Sheaf.H'` / `Sheaf.H`を別々に構成 |
| 第II部 `5.4 Base Change` | merged `S.topology` dependency、`CategoryTheory.GrothendieckTopology.pullback_stable`（new targetなし、AC `N/A`、開始条件5のfocused check） | context morphismに沿うcover pullback stabilityは既存Grothendieck topology APIから直接使用する。new targetは同一base上のselected cover refinementであり、context-change cover pullbackを再実装しない |
| 第III部 定義7.1 `Lawful Locus`、定義9.3 `Architecture Scheme`、定義10.2 `Ideal Restriction` | SD6〜SD7 | canonical raw / standard scheme changeからideal comapとlawful geometry mapを構成 |
| 第IV部 定義2.2、原則2.3、原則2.5 | SD5、SD8 | abelian-group / module-valued coefficientを明示し、selected coefficient sheafとそのbase changeに相対化したactual cohomologyを構成 |
| 第IV部 定義3.1〜4.1 | SD3〜SD5、SD8 | actual cover、all-degree cochains、alternating differential、cover-relative quotient、actual sheaf cohomologyを区別して接続 |
| Appendix A.2.1 coefficient | SD6〜SD8 | coordinate、ideal、Tor、linear Čech classをflat scalar extensionへ送り、canonical base-changed coefficientとLeray comparisonを介してactual `Sheaf.H` class mapを構成する |
| 第VIII部 定義9.1 | SD7 | common affine ambient `R`と同じambient内の二ideal `I`、`J`を`mathlibTorFlatBaseChangeIso`の入力として固定 |
| 第VIII部 定理候補9.2 `Flat Base Change Stability for LawConflict`のaffine表示 | SD7 | bare affine Tor-object formulaをflatnessだけで証明する独立の強化target。selected coefficient objects、LawConflict class、support pullbackを含むfull candidateの完了根拠には数えない |

同一law index carrierを越えるclosed-equational geometry comparisonとgeneral ringed-site Torは、
この表の完了claimに含めない。

## 問い

reading parameterを変えたとき、結論相当comparison dataを入力せず、次をactual mapとして構成できるか。

~~~text
exact core reading change
  -> ObjectAlgebraHom

positive core reading change
  -> positive circuit transport

selected closed-law strengthening
  -> ideal inclusion
  -> reverse lawful-closed-geometry morphism

coverage topology / selected cover refinement
  -> actual sieve / overlap maps
  -> canonical Čech cochain map
  -> cover-relative Hn map
  -> actual Sheaf.H comparison under fixed Leray condition

flat coefficient change
  -> canonical raw change
  -> site-dependent sheaf-compatible standard scheme change
  -> law ideal and lawful geometry comparison
  -> affine Tor base-change iso
  -> linear Čech Hn base-change iso
  -> actual Sheaf.H coefficient base-change map
~~~

## 現状診断

- core generation、selected geometry、raw restriction systemはあるが、原則10.6の
  `SignedExactCoreReadingHom`、`PositiveCoreReadingHom`、`ObjectAlgebraHom`は未実装である。
- closed-equational law comparisonは先行implementation dependencyであり、本PRDはそのmapを再実装しない。
- current `CoverRelativeCechCover`はcover membershipとsimplicial identityを持たず、
  `CoverRelativeCechComplex`はdifferentialと`d² = 0`をfieldで受ける。
- Mathlib `cechComplexFunctor`はambient categoryの`HasFiniteProducts`を要求するが、
  AAT siteの現行primitiveはselected `ContextOverlapPullback`である。本PRDは
  `AATCoverageFamily`とselected overlapからcanonical tuple complexを生成し、
  actual `Sheaf.H'`との比較だけをMathlib cohomologyへ接続する。
- current selected H1 comparisonは入力済みcochain comparisonを読むAPIであり、
  topology refinementからmapを生成しない。
- current conditional space cohomologyはcover-relative typeのaliasであり、actual `Sheaf.H`ではない。
- raw coefficient change、base-changed standard scheme、law ideal comapの統合APIは未実装である。
- `Derived.Intersection.mathlibTor`はactual Mathlib Torへ接続されているが、
  flat base-change isoは未実装である。
- `Measurement.FlatBaseChangeCandidate`はstatement-only dataであり、proof targetの代用にならない。
- Researchのselected finite H1 comparisonはprior artとして調査するが、general refinement completionに数えない。

## アウトカム

1. `ReadingCore`がgenerated core、selected geometry、coefficient ring、raw systemをtypedに接続する。
2. exact signed core changeからactual `ObjectAlgebraHom`が生成される。
3. positive core changeがpositive circuitだけをtransportする。
4. selected closed-law strengtheningが先行implementationのactual ideal / closed geometry mapを使用する。
5. topology refinementとselected cover refinementが別々のactual dataになる。
6. canonical Čech differential、one-way cochain hom、任意次数Hn map、class naturalityが生成される。
7. fixed Leray conditionからactual `Sheaf.H'` comparisonとrefinement naturalityを証明し、terminal baseではactual `Sheaf.H`へ接続する。
8. flat coefficient changeからrawがcanonicalに生成され、選択site上の`HasSheafCompose`の下で
   section-object scalar-extension iso、Spec pullback iso、standard scheme、closed-equational readingがcanonicalに生成される。
9. valid semantic-core bridgeからsource ideal-sheaf realizationを導出し、required / all-selected idealと
   lawful closed geometryのbase-change comparisonが同じsemantic-core provenanceをproof-useして構成され、
   `AllLawsSelected`の下でfull all-lawへ特殊化される。
10. affine Tor flat-base-change isoとlinear Čech Hn scalar-extension isoが証明される。
11. canonical base-changed coefficient sheaf、canonical Čech map、source / target Leray comparisonから
    actual `Sheaf.H` coefficient base-change mapが構成される。
12. SD9のpositive / negative firingがすべて発火する。

## 採否規律

- target名、量化対象、仮定、結論、参照definitionは`Statement Design`を不変入力とする。
- exact、positive、law、topology、cover、coefficientのchangeを一つのstructureへ統合しない。
- completed map、iso、class equalityをprimitive fieldに持たない。
- `ClosedEquationalGeometry`の同一`raw` / `X` / law-index条件を一般law-universe inclusionへ読み替えない。
- topology orderだけでselected cover refinementを完了としない。
- selected cover Čech cohomologyとactual `Sheaf.H`を区別する。
- generic affine Tor theoremをfinite calculationへ差し替えない。
- finite Čech targetをactual sheaf cohomology base changeと呼ばない。
- theorem candidate interface、legacy selected comparison、wrapperをproofの代用にしない。

## 改修要求

### R0 — dependency、prior art、Mathlib route、fixed statement

- 対象main commitと先行merged declaration inventoryをtracking Issueへ固定する。
- `ClosedEquationalGeometry` final implementation signatureをSD2と再突合する。
- Research sourceを直接検索し、selected theoremとnew construction targetを分ける。
- `Sheaf.H` / Čech、flat hom、IdealSheaf、pullback、TorのMathlib routeをLean scratchで型検査する。
- SD0〜SD9の全public signatureをexecutable contractへ記述する。

### R1 — ReadingCoreとcore changes

- SD0の`ReadingCore` / `ReadingSelection`を実装する。
- SD1の`ObjectAlgebraHom`、exact / positive change、refl / compを実装する。
- reachable object mapをoperation closureの帰納法で構成する。
- negative query reflectionをexact proofで使用し、positive proofへ混入させない。

### R2 — law dependency integration

- `ClosedEquationalGeometry`のrequired / all-selected ideal geometryとrequired / full all-law semantic comparisonを
  direct importする。
- duplicate `LawExtension`やcomparison mapを作らない。
- statement contractとfinite firingでmerged宣言を直接参照する。

### R3 — topologyとcover refinement

- actual cover selectorを持つ`CoverageTopologyRefinement`を実装する。
- `AATCoverageFamily`からall-degree tuple overlap / face / actual cover membershipを生成する。
- all-degree simplex / overlap mapとface naturalityを持つselected refinementを実装する。
- refl / compと非恒等finite refinementを証明する。

### R4 — canonical Čech functoriality

- additive restriction mapとcanonical alternating differentialを構成する。
- `d² = 0`をsimplicial identityから証明する。
- one-way complex hom、任意次数Hn map、id / compを証明する。
- obstruction representative / class naturalityをquotient mapから証明する。

### R5 — actual sheaf cohomology

- `ObstructionSheaf.toAddCommGrpSheaf`を構成する。
- `IsLerayFor`から`cechToSheafHAtBase`とbijectivityを証明する。
- selected refinement naturalityを`Sheaf.H' n base`上で証明する。
- terminal baseの`terminalHComparison`を構成し、global `cechToSheafH`へ接続する。
- topology change functorの加法性・有限極限/余極限保存を証明し、`sheafHMap`を
  `mapExtAddHom`、constant-sheaf iso、common-coefficient isoの具体合成から構成する。

### R6 — raw / standard scheme coefficient change

- polynomial coefficient mapから`raw.baseChange`を構成する。
- structural quotientから`baseChangePresheafIso`を構成する。
- scheme-level APIにcoefficient categoriesのuniverseを固定した
  `S.topology.HasSheafCompose f.coefficientExtension`を明示し、
  `sheafifyComposeIso`からsection-object scalar-extension isoを導く。
- section-object iso、`pullbackSpecIso`、atlas、overlapから`StandardArchitectureScheme.baseChange`を構成する。
- decoration equation、全chartのpullback、overlap validityをcharacterization theoremで固定する。
- identity / compositionをunit / compositor isoを介したactual map equalityとして証明する。
- source semantic-core global equationsを`baseChangeMap.appTop`で送り、target closed-equational readingを
  global-section witnessとrestrictionから生成する。

### R7 — ideals、lawful geometry、Tor

- `hB : IsSemanticLawEquationSchemeBridge raw G B`からPart 3の
  `semanticCoreIdealSheaf_realized`を導出してsource realizationを固定する。
- `semanticCoreLawWitnessIdeal_baseChangedChart`で、source semantic-core chart idealの引き戻しと
  target law-witness idealのchart pullbackを直接等置する。
- required / all-selected ideal sheafのaggregate comap equalityはglobal equationsのpullbackから
  独立に証明し、不要な`hB`を受け取らない。そのequalityからlawful closed geometry mapと
  ambient triangleを構成する。
- bare Tor-object formulaとして`mathlibTorFlatBaseChangeIso`をflatnessだけから任意次数で証明する。
- selected coefficient objects / LawConflict class / support pullbackのtransferへ完了claimを拡張しない。
- `FlatBaseChangeCandidate`への依存なしをsource scanで確認する。

### R8 — linear Čech scalar extension

- module-valued obstruction sheafとlinear differentialを接続する。
- flat tensorのexactnessから任意次数Hn scalar-extension isoを証明する。
- cochain object、differential、cocycle mapをcharacterization theoremで固定する。
- module-valued coefficient sheafからcanonical base-changed coefficient sheafを生成する。
- canonical Čech complex hom、degreewise compatibility、Hn mapをsection mapとdifferential可換性から構成する。
- terminal Leray comparisonでactual `Sheaf.H`へmodule structureをtransportし、
  `sheafHFlatBaseChangeMap`とclass formulaを構成する。
- coefficient sheafificationとmodule scalar extensionのunit / compositor isoを構成し、
  actual H mapのidentity / compositionを証明する。
- linear Čech class naturalityとactual `Sheaf.H` class mapのnonzero preservationを同じ具体modelで発火させる。

### R9 — examples、integration、audit

- SD9 firing matrixの全positive / negative declarationを実装する。
- aggregate、statement contracts、axiom auditへ接続する。
- tracking Issueへpremise discharge packetとdeclaration mapを記録する。
- 数学本文の各source行をfixed target、実装宣言、ACへ対応づけたsource mapをtracking Issueへ記録する。

## Acceptance Criteria

- [ ] AC1: executable contractがSD0〜SD9の全public definition / theoremをexact signatureで直接突合する。
- [ ] AC2: module import contractどおりのDAGで、ResearchLean reverse importがない。
- [ ] AC3: `ReadingCore`が`AATCorePackage`、`SelectedGeometryReading`、coefficient ring、`raw`を同一provenanceで接続する。
- [ ] AC4: `ReadingCore` / selectionにscheme、ideal、class、comparison mapがない。
- [ ] AC5: `ObjectAlgebraHom`がactual object / configuration / law / circuit / operation mapを持つ。
- [ ] AC6: exact core changeから`ObjectAlgebraHom`が生成され、input fieldから射影されない。
- [ ] AC7: exact core changeのidentity / compositionが`ObjectAlgebraHom`のidentity / compositionに一致する。
- [ ] AC8: positive core changeはsource reachable objectをactual target algebra objectへ送り、positive circuitをtransportする。negative circuit transportは主張しない。
- [ ] AC9: nonidentity exact exampleが発火し、positive core exampleでは`positiveQuery_mem`と`positiveCircuit_queries_nonempty`がactual positive queryを固定する。positive-only negative example、`Invariant.transportedAlong_refl`、`Invariant.function_predicate_not_transportedAlong`も発火する。
- [ ] AC10: law laneが同じ`S`、`k`、`HasSheafify`、`raw`、`X`を共有する`ClosedEquationalGeometry` declarationを直接使用し、新しいwrapper / duplicate mapを作らない。
- [ ] AC11: semantic comparisonのrequired / full all-law二系統と、ideal / closed geometry comparisonのrequired / all-selected二系統がcontractで参照される。`allLawGeneratedIdealSheaf`を無条件のfull all-law idealと扱わない。
- [ ] AC12: `weakToStrong` / `weakToStrong_valid`、required / all-selected双方のnon-iso theorem、`coordinateBrokenInclusion_not_valid`が発火する。
- [ ] AC13: topology refinementがcoarse coverごとにfine coverとactual sieve inclusionを返す。
- [ ] AC14: selected cover refinementが全次数のsimplex map、overlap map、face naturalityを持つ。
- [ ] AC15: canonical coverがactual `AATCoverageFamily`から生成され、全次数のsimplex / overlap / face characterizationとtopology membershipを持つ。
- [ ] AC16: canonical differentialがrestrictionの交代和であり、`d² = 0`がderived theoremである。
- [ ] AC17: refinementからone-way cochain homが生成され、cochain-level formulaとdifferential可換性を持つ。
- [ ] AC18: arbitrary degreeのcover-relative Hn map、identity、compositionが証明される。
- [ ] AC19: obstruction class naturalityがrepresentativeとquotient mapから証明される。
- [ ] AC20: coarse/fine finite exampleでtopology refinementのactual refined sieveがselected `fineCover`の生成sieveと一致し、index mapが非全単射で、cochain mapが非零である。
- [ ] AC21: broken face mapからvalid refinementを構成できないnegative exampleがある。
- [ ] AC22: `ObstructionSheaf.toAddCommGrpSheaf`がactual AddCommGrp-valued sheafである。
- [ ] AC23: `IsLerayFor`がpositive-degree actual `Sheaf.H'` vanishingであり、comparison mapをfieldに持たない。
- [ ] AC24: arbitrary baseでは`cechToSheafHAtBase`がactual `Sheaf.H'`を参照し、terminal baseでのみ`cechToSheafH`がactual `Sheaf.H`を参照する。
- [ ] AC25: topology changeで`r.le`と`Presieve.isSheaf_of_le`から`coarseRestriction`を構成し、`fineSheafificationAdjunction`を証明する。そこから`fineSheafification`の`PreservesFiniteColimits`、left-exact sheafificationから`PreservesFiniteLimits`、pointwise additive forget / `presheafToSheaf_additive`から`Additive`を導く。`sheafHMap_eq_ext`が`mapExtAddHom`、constant-sheaf iso、common-coefficient isoの具体合成を固定し、identity / compositionが証明され、strict finite topology changeで`coarseFineSheafHMap_nonzero`が発火する。
- [ ] AC26: `ConditionalSpaceCohomology`とselected comparison fieldがAC22〜AC25の主経路にない。
- [ ] AC27: `FlatCoefficientChange`のprimitive dataがring homと`RingHom.Flat`だけであり、`coefficientExtension_preservesFiniteLimits`がflatnessをproof-useする。sheaf、section、scheme、comparison isoをfieldに追加しない。
- [ ] AC28: `raw.baseChange`がcoordinate、relation、restrictionをcoefficient mapから構成し、`baseChangePresheafIso`がstructural quotientのscalar extensionをrestriction naturality込みで証明する。
- [ ] AC29: scheme-level APIがcoefficient categoriesのuniverseを固定した`S.topology.HasSheafCompose f.coefficientExtension`を明示し、`coefficientExtension_preservesSheafification`が`Under.mapPushoutAdj`をproof-useする。`sheafifiedSectionObjectBaseChangeIso`と`sheafifiedSectionSpecBaseChangeIso`が`baseChangePresheafIso`、`sheafifyComposeIso`、`pullbackSpecIso`をproof-useし、standard scheme base changeとmapがactual affine pullback / decoration / atlas / overlapから構成され、interpretation equationと全chart pullbackが検査される。
- [ ] AC30: coefficient extensionのrefl / comp isoと`HasSheafCompose`のrefl / comp導出から、scheme base-change mapのidentity / compositionがunit / compositor isoを介したactual morphism equalityとして証明される。
- [ ] AC31: `baseChangedSemanticCoreGlobalEquation`がsource global equationsをactual `baseChangeMap.appTop`で送り、`baseChangeOfSemanticCore`がtarget geometric reading、witness coordinates、restriction compatibilityを同じpullbackから生成する。同じ`G`を異なるcoefficient rawのbridgeへ再利用しない。Part 3の`semanticCoreIdealSheaf_realized`がsource realizationを放電する。
- [ ] AC32: `semanticCoreLawWitnessIdeal_baseChangedChart`が`hB`、Part 3のchart realization、`baseChangedChart_isPullback`、`IdealSheafData.comap_comp`をproof-useし、各law・各atlas chartでsource semantic-core chart idealの引き戻しとtarget law-witness idealのchart pullbackを一つのequalityとして直接結ぶ。
- [ ] AC33: required / all-selected ideal sheafのaggregate `IdealSheafData.comap` equalityはglobal equationsのpullbackから証明し、数学的に不要な`hB`を受け取らない。両lawful closed subscheme comparisonとambient triangleはそのaggregate equalityから構成し、per-law existing-core provenanceとの役割を混同しない。
- [ ] AC34: affine `mathlibTorFlatBaseChangeIso`がflatnessだけから任意次数について証明され、finite theoremへの差し替えがない。結論はbare Tor-object isoであり、selected coefficient / LawConflict support transferの完了証拠として扱わない。
- [ ] AC35: `Measurement.FlatBaseChangeCandidate`をAC27〜AC34の証拠として使用しない。
- [ ] AC36: linear Čech Hn scalar-extension iso、cochain / differential characterization、class naturalityが証明される。
- [ ] AC37: `LinearObstructionSheaf.baseChange`がtarget coefficient sheafをcanonicalに生成し、canonical complex hom / Hn map / actual `Sheaf.H` mapがH-level comparison dataを入力せず構成される。source / target Leray proofと`CechCoefficientBaseChangeCompatible`の下で`sheafHFlatBaseChangeMap_isIso` / `sheafHFlatBaseChangeIso`が導かれ、`sheafHFlatBaseChangeMap_on_class`がcanonical unit上のclass formulaを固定する。sheafificationのunit / compositor isoを介してidentity / compositionが証明される。
- [ ] AC38: `Int → Polynomial Int` modelで`coefficientExtension_hasSheafCompose`、section-object / Spec pullback iso、`coefficientBridge_valid`、`coefficientSemanticCore_realized`、`coefficientSemanticCore_baseChangedChart`、nonidentity lawful-locus map、proper ideal、source Tor₁ witnessのgeneric base-change iso像、nonzero linear Čech class、nonzero actual `Sheaf.H` class mapが同じcoefficient changeから発火する。`finiteCechCoefficientCompatible`とsource / target Leray proofを具体modelで放電し、final actual H isoを構成する。さらに`Int → Rat`と`Nat`添字のinfinite duplicated coverでdegree-zero canonical componentがisoでないことと`infiniteProductCech_not_compatible`を証明し、Čech coefficient compatibilityの不成立を直接示す。
- [ ] AC39: non-flat `Int → ZMod 2`とbroken relation transportのnegative exampleが発火する。
- [ ] AC40: 全material premiseの放電元、proof-use、主結論への寄与が記録され、deltaがemptyである。
- [ ] AC41: new public theorem、positive / negative examplesがstandard axiomsのみを使用し、axiom auditがgreenである。
- [ ] AC42: protected数学本文のdiffがzeroである。
- [ ] AC43: final snapshotにLean品質基準で禁止された仮置き・非安全declaration、private path、hidden / bidirectional Unicodeがない。
- [ ] AC44: `math-lean-review`の4本の独立査読がすべて`No major findings`である。

## Failure Contract

次は完了ではなく失敗である。

- exact core changeにcompleted `ObjectAlgebraHom`をfieldとして持たせる。
- positive changeからnegative queryを含むcircuit transportを主張する。
- law laneを`ClosedEquationalGeometry` declarationのwrapper / alias / repackageだけで水増しする。
- `ClosedEquationalGeometry`のsame-site mapを異なるlaw universe間のcomparisonと扱う。
- topology orderだけ、またはcover名だけでrefinementを表す。
- differential、cochain map、Hn map、class equalityをinput fieldから射影する。
- current conditional cohomology aliasをactual `Sheaf.H`と扱う。
- `CechComputes`を自由なcomparison iso fieldとして定義する。
- topology-change H mapを`mapExtAddHom`、constant-sheaf iso、coefficient isoと接続しない任意のadditive mapとして置く。
- Mathlibに存在しない一括exactness predicateをfixed signatureへ置く。
- `fineSheafificationAdjunction`を構成せず、有限余極限保存を根拠なしのinstanceとして宣言する。
- left-exact sheafificationを構成せず、`PreservesFiniteLimits`を`sheafHMap`の引数へ移す。
- fine sheafからcoarse sheafへの再解釈を`r.le`とactual sheaf proofへ接続しない。
- raw / scheme / readingの変更後objectをcallerから受け取り、canonical base changeの代用にする。
- flatnessによる有限極限保存だけから、一般site上の
  `S.topology.HasSheafCompose f.coefficientExtension`を無条件に主張する。
- `baseChangePresheafIso`、`sheafifyComposeIso`、section-ring tensor comparisonを構成せず、
  scheme isoまたはchart pullback squareを入力する。
- tensor productを経由しないsource section mapだけでaffine pullbackを完了扱いする。
- source `SemanticLawEquationWitnessIdealCore`を異なるcoefficient rawのbridgeへそのまま再利用する。
- existing semantic-core routeで`hB : IsSemanticLawEquationSchemeBridge raw G B`と
  Part 3の`semanticCoreIdealSheaf_realized`をproof-useせず、任意のglobal equationsのgenerated idealだけを比較する。
- source realizationとaggregate ideal equalityを独立な積に入れただけで、
  existing-core chart idealとtarget law-witness idealの直接比較を省略する。
- aggregate ideal equalityやlawful geometry mapへ数学的に不要な`hB`を装飾的に追加する。
- `SemanticCoreIdealSheafRealized`をcaller-supplied premiseまたはcertificate fieldとして受け取る。
- arbitrary Scheme morphismを`baseChangeMap`として入力する。
- Tor comparison type / isoを`FlatBaseChangeCandidate`から読む。
- generic affine Tor targetをselected finite resolution theoremへ変更する。
- linear Čech Hn isoをactual sheaf cohomology base changeと呼ぶ。
- flatnessだけからgeneral `CechCoefficientBaseChangeCompatible`を無条件に主張する。
- arbitrary `LinearCoverRelativeCechComplex`をactual `Sheaf.H`のcanonical coefficient complexとして扱う。
- generic compatibility / Leray引数つき定理だけを示し、finite modelでcompatibility、target Leray、actual H map / isoを放電しない。
- base-changed coefficient sheaf、canonical complex hom、Hn map、actual `Sheaf.H` map / isoをcaller-supplied fieldから読む。
- sheafificationを挟む恒等・合成base changeをdefinitionally同一視し、unit / compositor isoを構成しない。
- identity、zero ideal、zero complex、duplicated coverだけでfiringを満たす。

## 停止条件

- 数学本文のparameter functorialityに、Lean実装と独立した反例、型不整合、well-definedness欠陥が見つかった。
- fixed signatureを弱める、本文にないmaterial premiseを追加する、結論相当fieldを追加する必要が生じた。
- exact core changeからreachable object mapを構成できず、completed object mapを入力する必要が生じた。
- `ClosedEquationalGeometry` merged signatureがSD2のsame-site contractと一致しない。
- current Čech surfaceからcanonical differentialを構成できず、`d² = 0`を自由なfieldに戻す必要が生じた。
- Leray vanishingからactual `Sheaf.H'` comparisonを構成できず、cover-relative typeだけが残る。
- terminal baseで`Sheaf.H'` / `Sheaf.H` comparisonを構成できない。
- topology refinementからactual sheaf functor / Ext mapを構成できない。
- `fineSheafification`の有限極限保存をfixed signatureのまま証明できず、
  `PreservesFiniteLimits`を外部入力にする必要が生じた。
- structural quotientから`baseChangePresheafIso`を構成できない。
- `HasSheafCompose`の下でもsheafified section scalar-extension isoを構成できず、
  arbitrary comparison isoまたはtarget schemeが必要になる。
- finite coefficient modelで`coefficientExtension_hasSheafCompose`を放電できない。
- source global equationsのactual scheme pullbackからtarget closed-equational readingを構成できない。
- `hB`からPart 3のsource ideal-sheaf realizationを導出できない、またはそのchart成分と
  target law-witness idealを`semanticCoreLawWitnessIdeal_baseChangedChart`の一つのequalityへ接続できない。
- flatnessだけを仮定するaffine Tor-object base-change isoをSD7のsignatureで証明できない。
- source module sheafからbase-changed target coefficient sheafをcanonicalに生成できず、arbitrary target sheafが必要になる。
- canonical complex homとsource / target Leray comparisonからactual `Sheaf.H` coefficient mapを構成できない。
- finite modelで`CechCoefficientBaseChangeCompatible`、target Leray、nonzero actual H classを同時に放電できない。
- flat scalar extensionが無限積と可換しないmodelから`infiniteProductCech_not_compatible`を構成できない。
- coefficient sheafificationのunit / compositor isoからactual H mapのidentity / compositionを構成できない。
- nontrivial exact / cover / coefficient exampleが構成できず、identityまたはzero exampleだけが残る。

停止報告には、該当SD / AC、fixed signature、最小の反例またはAPI blocker、試したMathlib route、
material premise分類、数学本文改訂の要否、独立タスクとして必要な設計を記録する。

## Non-goals

- 異なるlaw universeを持つ二つのstandard geometry間のgeneral closed-subscheme comparison。
- 第VIII部 定理候補9.2のgeneral ringed-site Tor base-change iso。
- 第VIII部 定理候補9.2のselected coefficient objects、LawConflict class、support pullbackまで含むfull transfer。
- `CechCoefficientBaseChangeCompatible`を仮定しないgeneral actual `Sheaf.H` coefficient base-change iso。
- law / topology / coefficient change間のgeneral mixed coherence。
- conormal sequence、first-order connecting class、lift torsorの本体蒸留。
- arbitrary derived stack、gerbe、higher obstruction functoriality。
- source extraction、ArchMap、ArchSig、FieldSig、websiteの変更。
- legacy selected comparison surfaceのrepo-wide削除。
- protected数学本文へのLean status、Issue、PR、declaration名の追加。
- archive文書のruntime台帳化。

## 検証

検証手順と実行主体は`AGENTS.md`と`docs/aat/guideline.md`を直接適用する。
task固有のfocused checksは次である。

- `StatementContractsReadingFunctoriality.lean`がSD0〜SD9の全targetを直接参照する。
- `AxiomAudit.lean`が全new public theoremとfiring declarationsを直接参照する。
- 数学本文との対応表の各行がfixed target、実装宣言、AC、focused checkへ一意に接続される。
- 第II部5.4のsource mappingが`CategoryTheory.GrothendieckTopology.pullback_stable`を
  exact declarationとして参照し、対象main commitとimport pathをfocused checkする。
- exact core changeのsource scanでcompleted `ObjectAlgebraHom` fieldがzeroである。
- positive core proofからnegative circuit transport declarationがzeroである。
- SD2 implementationにduplicate comparison definitionがなく、`ClosedEquationalGeometry`のdirect importとdirect theorem useがある。
- topology / cover / cochainの三層が別typeであり、actual sieve / overlap mapを参照する。
- canonical differentialのformulaと`d² = 0` proofがrestriction / simplicial identityを使用する。
- actual cohomology targetが`CategoryTheory.Sheaf.H` / `H'`を参照し、
  `ConditionalSpaceCohomology`への依存がzeroである。
- topology-change routeが`r.le`、`Presieve.isSheaf_of_le`、
  `fineSheafificationAdjunction`を直接参照し、有限余極限保存をleft-adjoint性、
  有限極限保存をleft-exact sheafification、加法性をpointwise additive forgetと
  `presheafToSheaf_additive`から導く。
  `Functor.mapExtAddHom`、constant-sheaf iso、common-coefficient isoは
  `sheafHMap_eq_ext`の具体合成として直接参照する。
- coefficient routeが`RawAmbientRestrictionSystem.baseChange`、
  `baseChangePresheafIso`、`sheafifiedSectionObjectBaseChangeIso`、
  `sheafifiedSectionSpecBaseChangeIso`、
  `StandardArchitectureScheme.baseChange`、`coefficientBridge_valid`、
  Part 3の`semanticCoreIdealSheaf_realized`、`semanticCoreLawWitnessIdeal_baseChangedChart`、
  `baseChangedSemanticCoreGlobalEquation`、`IdealSheafData.comap`、
  `lawfulClosedSubschemeBaseChangeMap`を役割別のproof chainで使用する。
- Tor routeが`Derived.Intersection.mathlibTor`を参照し、
  `Measurement.FlatBaseChangeCandidate`への依存がzeroである。
- actual coefficient H routeが`LinearObstructionSheaf.baseChange`、
  `canonicalCechBaseChangeHom`、`terminalLerayHModule`、
  `sheafHFlatBaseChangeMap_on_class`を同じprovenanceで参照し、target coefficient sheaf、
  complex hom、Hn map、H-level map / isoのinput fieldがzeroである。
- actual coefficient H routeが`finiteCechCoefficientCompatible`、source / target Leray、
  `finiteSheafHBaseChangeIso`を具体modelで放電し、identity / composition theoremが
  sheafificationとscalar extensionのunit / compositor isoをproof-useする。
- flat extensionのfinite-limit preservation、`HomologicalComplex.homologyMapIso`、
  `AddEquiv.module`へのproof-useをdeclaration単位で記録する。
- SD9 firing matrixの各entryについてpositive / negative declaration、具体map、ideal、class、
  morphism、nonidentity / nonzero proofを記録する。
- final declaration inventoryをSD9 material premise表へ突合する。
- `git diff --check`、staged diff、untracked file、hidden / bidirectional Unicode、
  仮置き・非安全declaration・private pathのscanを実行する。
- protected数学本文がdiffに含まれない。

## Completion evidence packet

完了判定には次を一つのtracking Issue commentへまとめる。

| evidence | 必須内容 |
| --- | --- |
| fixed statement diff | Approved SD0〜SD9 signatureと実装signatureの差分zero |
| declaration map | 各ACに対応するdeclaration名、source file、focused check |
| dependency evidence | 対象main commit、`AATCorePackage` / `SelectedGeometryReading.toAATSite` / `StandardArchitectureScheme`のmerged宣言、`ClosedEquationalGeometry` final merged declaration inventoryとsame-site signature、`IsSemanticLawEquationSchemeBridge` / `semanticCoreIdealSheaf_realized`、Mathlib `Under.pushout` / `HasSheafCompose` / `sheafifyComposeIso`、module-sheaf / actual-H scratch、finite modelのnamed `HasSheafify` / `HasSheafCompose` instance chain |
| source mapping evidence | 数学本文との対応表の各行に対するfixed target、実装宣言、AC、focused check。new targetを持たないmerged / Mathlib依存行だけはACを`N/A`とできるが、exact declaration名、import path、対象main commit上のfocused checkを必須とする |
| premise discharge | 全明示引数 / typeclass / field / certificate、分類、放電元、proof-use、主結論への寄与、delta empty |
| core evidence | exact / positive map、actual positive query membership / nonempty、reachable construction、id / comp、negative-query差 |
| law evidence | required / all-selected ideal geometryとrequired / full all-law semantic direct reuse、strict ideal、non-iso map |
| coverage evidence | topology selector、cover maps、canonical differential、cochain map、Hn、class naturality |
| sheaf evidence | actual AddCommGrp sheaf、Leray condition、`Sheaf.H'` comparison、terminal `Sheaf.H` comparison、topology-changeのcoarse restriction / adjunction、加法性・有限極限/余極限保存の別々のproof-use、`mapExtAddHom`と二つのisoによる具体Ext map、nonzero firing |
| coefficient evidence | `HasSheafCompose`のfinite放電、canonical raw-presheaf / sheafified-section comparison、actual pullback scheme、valid source bridge、source ideal-sheaf realization、per-law chart transport、source global equationのactual pullback、target reading、aggregate ideal comap、lawful map、unit / compositor compatibility |
| Tor / Čech evidence | flatnessだけからのarbitrary-degree affine Tor-object iso、full selected LawConflict transferへclaimを拡張していないこと、linear Hn iso、cochain / differential formula、nonzero firing |
| actual coefficient H evidence | canonical base-changed module sheaf、section map naturality、canonical complex / Hn map、`CechCoefficientBaseChangeCompatible`の具体放電、source / target Leray、terminal Leray H module、map / final iso、identity / composition、class formula、nonzero firing |
| negative evidence | function / predicate invariant mismatch、positive-only mismatch、broken face、non-Leray non-evidence、infinite-product Čech incompatibility、non-flat map、broken relation、candidate-field非依存 |
| axiom evidence | statement contracts、axiom audit、`#print axioms` |
| aggregate evidence | direct imports、`Formal/AG.lean` transitive import、ResearchLean reverse import zero |

static検査、review、CI、merge、runtime status同期、完了後の参照除去とarchiveは、
`AGENTS.md`、`docs/aat/guideline.md`、`docs/guideline.md`を直接適用する。
