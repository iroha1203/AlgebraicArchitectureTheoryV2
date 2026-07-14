# PRD: AAT Lean Atom由来readingからringed siteまでの生成基盤

- 作成: 2026-07-12
- 対象: `Formal/AG/Atom`、`Formal/AG/Site`、`Formal/AG/LawAlgebra` のsite・raw algebra・structure sheaf層、aggregate、statement contracts、axiom audit、Lean台帳
- 数学的正典: `docs/aat/algebraic_geometric_theory/` 第I部〜第III部
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、`docs/aat/lean_quality_standard.md`
- 数学statement改訂: Issue #3330
- tracking Issue: 旧tracking Issue #3308 は停止処理済み。再開時に新tracking Issueを作成する
- statement contract正本: 本PRDの`Statement Design`節
- executable contract: `Formal/AG/StatementContractsAtomToRingedSite.lean`。実装と同時に作成し、CIでelaborateする
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

- tracking Issueが作成され、対象main commit、target一覧、material premise表、子Issue依存が登録されている。

## Statement Design

この節は本PRDの設計入力であり、実装開始後にtargetの仮定・結論・量化対象を変更しない。
実装状態は記録しない。実装後は
`Formal/AG/StatementContractsAtomToRingedSite.lean`が、ここに固定したtargetと
実装宣言のLean signatureを回帰検査する。別のMarkdown contractは作成しない。

以下のLean blockは`namespace AAT.AG`、`open CategoryTheory`、`universe u v`の下で読む。
SD3〜SD5ではさらに`open LawAlgebra`を前提とする。

### SD1 — AAT Core generation

Part I 定義8.2、定義10.1、定義10.4A、定理10.5に合わせ、axiom-level data、
core reading、生成物を分離する。A8は、canonical selectorが関数であることだけで閉じず、
sourceとfamilyの間のextraction relation、そのcanonical witness、一意性を固定する。

```lean
structure ExtractionDoctrine (U : AtomCarrier.{u}) where
  Source : Type u
  Vocabulary : Type u
  SemanticReading : Type u
  Resolution : Type u
  vocabulary : Vocabulary
  semanticReading : SemanticReading
  resolution : Resolution
  vocabularyAllows : Vocabulary -> U.Atom -> Prop
  semanticAllows : SemanticReading -> Source -> U.Atom -> Prop
  resolutionAllows : Resolution -> Source -> U.Atom -> Prop
  sourceSemantics : Source -> U.Atom -> Prop
  normalize : Source -> Source

def ExtractionDoctrine.extracts {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source) (atom : U.Atom) : Prop :=
  D.vocabularyAllows D.vocabulary atom ∧
    D.semanticAllows D.semanticReading (D.normalize source) atom ∧
    D.resolutionAllows D.resolution (D.normalize source) atom ∧
    D.sourceSemantics (D.normalize source) atom

def ExtractionDoctrine.atomize {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source) : AtomFamily U where
  mem atom := D.extracts source atom

def ExtractionDoctrine.Atomizes {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source)
    (family : AtomFamily U) : Prop :=
  ∀ atom, family.mem atom ↔ D.extracts source atom

theorem ExtractionDoctrine.atomize_holds {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source) :
    D.Atomizes source (D.atomize source)

theorem ExtractionDoctrine.atomize_unique {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source)
    {F G : AtomFamily U}
    (hF : D.Atomizes source F) (hG : D.Atomizes source G) :
    F = G

theorem ExtractionDoctrine.eq_atomize {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source)
    {F : AtomFamily U} (hF : D.Atomizes source F) :
    F = D.atomize source
```

`atomize_holds`、`atomize_unique`、`eq_atomize`はstructure fieldではなく、
`AtomFamily` のmembership extensionalityと`propext`から証明する。
`Vocabulary`、`SemanticReading`、`Resolution`、`sourceSemantics`、`normalize`は
`extracts`の定義ですべてproof-useされる。

現行`AtomAxiomSystem`はactual towerを直接返さないabstract carrierを内包しているため、
tower componentを持たない次のsignatureへ移行する。

```lean
structure AtomAxiomSystem (U : AtomCarrier.{u}) where
  primitiveExistence : Nonempty U.Atom
  predicateStability : ∀ a b, SameCoordinates U a b ↔ a = b
```

A1の座標totalityとA2のsingle-fact readingは`AtomCarrier`の一つのAtomが一つの
coordinate tupleを持つ型構造で担う。`singleFact : Atom -> Prop`と全Atomに対する
`singleFact_holds`は`True`で空虚に満たせるため、fixed signatureへ残さない。
A4、A7、A8は`CoreReading`のcomposition、operation、doctrineが担い、A5/A6はlaw / observationが
Atomを返さない型付けとして扱う。

composition と object formation は、selected outputではなく全入力に作用する rule として固定する。

```lean
structure CompositionReading (U : AtomCarrier.{u}) where
  compose : (F : AtomFamily U) -> F.ListFinite -> AtomConfiguration U
  family_eq : ∀ F hfinite, (compose F hfinite).family = F
  family_supported : ∀ F hfinite, (compose F hfinite).FamilySupported

structure ObjectReading (U : AtomCarrier.{u}) where
  object : AtomConfiguration U -> ArchitectureObject U
  configuration_eq : ∀ C, (object C).configuration = C
```

finite circuit はobject-wide failureをfieldに持たず、正負の極性を持つ有限 query pattern、
そのobject上でのmatching、finite-template Boolean detector、soundnessから構成する。

```lean
def SemanticObstruction {U : AtomCarrier.{u}} (L : Law U)
    (A : ArchitectureObject U) : Prop :=
  ¬ L.holds A

inductive CircuitQuery (U : AtomCarrier.{u}) where
  | atomPresent (a : U.Atom)
  | relationPresent (a b : U.Atom)
  | identificationPresent (a b : U.Atom)

def CircuitQuery.Holds {U : AtomCarrier.{u}} (q : CircuitQuery U)
    (A : ArchitectureObject U) : Prop :=
  match q with
  | .atomPresent a => A.configuration.family.mem a
  | .relationPresent a b =>
      A.configuration.family.mem a ∧
      A.configuration.family.mem b ∧
      A.configuration.relation a b
  | .identificationPresent a b =>
      A.configuration.family.mem a ∧
      A.configuration.family.mem b ∧
      A.configuration.identification a b

structure FiniteCircuitDatum (U : AtomCarrier.{u}) where
  queries : List (CircuitQuery U × Bool)

def FiniteCircuitDatum.Matches {U : AtomCarrier.{u}}
    (Q : FiniteCircuitDatum U) (A : ArchitectureObject U) : Prop :=
  ∀ query expected, (query, expected) ∈ Q.queries ->
    (query.Holds A ↔ expected = true)

inductive CircuitDetectorCode (U : AtomCarrier.{u}) where
  | reject
  | exact (pattern : FiniteCircuitDatum U)
  | any (left right : CircuitDetectorCode U)

noncomputable def CircuitDetectorCode.eval {U : AtomCarrier.{u}}
    (code : CircuitDetectorCode U) (Q : FiniteCircuitDatum U) : Bool := by
  classical
  exact match code with
    | .reject => false
    | .exact pattern => if pattern = Q then true else false
    | .any left right => left.eval Q || right.eval Q

structure CircuitReading {U : AtomCarrier.{u}} (LU : LawUniverse U) where
  code : (i : LU.Index) -> CircuitDetectorCode U
  sound : ∀ (i : LU.Index) (A : ArchitectureObject U)
    (Q : FiniteCircuitDatum U),
      Q.Matches A -> (code i).eval Q = true ->
        ¬ (LU.law i).holds A

noncomputable def CircuitReading.accepts {U : AtomCarrier.{u}}
    {LU : LawUniverse U} (R : CircuitReading LU)
    (i : LU.Index) (Q : FiniteCircuitDatum U) : Bool :=
  (R.code i).eval Q

def CircuitReading.Circuit {U : AtomCarrier.{u}} {LU : LawUniverse U}
    (R : CircuitReading LU) (A : ArchitectureObject U)
    (i : LU.Index) : Type u :=
  {Q : FiniteCircuitDatum U // Q.Matches A ∧ R.accepts i Q = true}

def CircuitReading.RequiredComplete {U : AtomCarrier.{u}}
    {LU : LawUniverse U} (R : CircuitReading LU) : Prop :=
  ∀ (A : ArchitectureObject U) (i : LU.Index), LU.Required i ->
    ¬ (LU.law i).holds A -> Nonempty (R.Circuit A i)

structure LawReading (U : AtomCarrier.{u}) where
  lawUniverse : LawUniverse U
  circuits : CircuitReading lawUniverse
```

`CircuitDetectorCode`のgrammarはfinite datum、exact template、有限選言だけを持つ。
architecture object、`Law.holds`、law-failure proof、arbitrary `Prop`はcodeのconstructorに入れない。
finite modelは少なくとも一つのaccepted datumと一つのrejected datumを計算する。

operation は actual configuration homomorphism を持つobject-pair-indexed型族とし、
selected operationをcore fieldに置かない。

```lean
structure ConfigurationHom {U : AtomCarrier.{u}}
    (C D : AtomConfiguration U) where
  atomMap : U.Atom -> U.Atom
  maps_family : ∀ {a}, C.family.mem a -> D.family.mem (atomMap a)
  maps_relation : ∀ {a b}, C.relation a b ->
    D.relation (atomMap a) (atomMap b)
  maps_identification : ∀ {a b}, C.identification a b ->
    D.identification (atomMap a) (atomMap b)

def ConfigurationHom.id {U : AtomCarrier.{u}} (C : AtomConfiguration U) :
    ConfigurationHom C C

def ConfigurationHom.comp {U : AtomCarrier.{u}}
    {C D E : AtomConfiguration U}
    (g : ConfigurationHom D E) (f : ConfigurationHom C D) :
    ConfigurationHom C E

structure Operation (U : AtomCarrier.{u}) where
  source : ArchitectureObject U
  target : ArchitectureObject U
  configurationMap :
    ConfigurationHom source.configuration target.configuration

structure OperationReading (U : AtomCarrier.{u}) where
  Op : ArchitectureObject U -> ArchitectureObject U -> Type u
  configurationMap : ∀ {A B}, Op A B ->
    ConfigurationHom A.configuration B.configuration

def OperationReading.operation {U : AtomCarrier.{u}}
    (R : OperationReading U) {A B : ArchitectureObject U}
    (op : R.Op A B) : Operation U where
  source := A
  target := B
  configurationMap := R.configurationMap op

inductive OperationReading.Reachable {U : AtomCarrier.{u}}
    (R : OperationReading U) (base : ArchitectureObject U) :
    ArchitectureObject U -> Prop
  | base : Reachable R base base
  | step {A B} : Reachable R base A -> R.Op A B -> Reachable R base B
```

admissible core reading とobject algebraを次で固定する。

```lean
structure CoreReading (U : AtomCarrier.{u}) where
  doctrine : ExtractionDoctrine U
  source : doctrine.Source
  family_listFinite : (doctrine.atomize source).ListFinite
  composition : CompositionReading U
  objectReading : ObjectReading U
  lawReading : LawReading U
  invariantReading : InvariantFamily U
  signatureReading : ArchitectureSignature U
  operationReading : OperationReading U

structure ObjectAlgebra (U : AtomCarrier.{u}) where
  Obj : Type (u + 1)
  object : Obj -> ArchitectureObject U
  Op : Obj -> Obj -> Type u
  configurationMap : ∀ {A B}, Op A B ->
    ConfigurationHom (object A).configuration (object B).configuration
  invariantReading : InvariantFamily U
  lawReading : LawReading U
  signatureReading : ArchitectureSignature U

def ObjectAlgebra.Circuit {U : AtomCarrier.{u}}
    (K : ObjectAlgebra U) (A : K.Obj)
    (i : K.lawReading.lawUniverse.Index) : Type u :=
  K.lawReading.circuits.Circuit (K.object A) i

def ObjectAlgebra.operation {U : AtomCarrier.{u}}
    (K : ObjectAlgebra U) {A B : K.Obj} (op : K.Op A B) : Operation U where
  source := K.object A
  target := K.object B
  configurationMap := K.configurationMap op
```

`AATCorePackage`はaxiomsとadmissible readingだけを保持し、family以降はdefinitionで生成する。

```lean
structure AATCorePackage (U : AtomCarrier.{u}) where
  axioms : AtomAxiomSystem U
  reading : CoreReading U

def AATCorePackage.generate {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) : AATCorePackage U

def AATCorePackage.family {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : AtomFamily U
def AATCorePackage.configuration {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : AtomConfiguration U
def AATCorePackage.object {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : ArchitectureObject U
def AATCorePackage.algebra {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : ObjectAlgebra U
def AATCorePackage.baseObject {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : core.algebra.Obj
```

characterization targetを次で固定する。

```lean
theorem AATCorePackage.generate_axioms {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).axioms = S

theorem AATCorePackage.generate_reading {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).reading = r

theorem AATCorePackage.generate_family_eq_atomize {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).family = r.doctrine.atomize r.source

theorem AATCorePackage.generate_family_atomizes {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    r.doctrine.Atomizes r.source (AATCorePackage.generate S r).family

theorem AATCorePackage.generate_family_listFinite {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).family.ListFinite

theorem AATCorePackage.generate_family_unique {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {F : AtomFamily U} (hF : r.doctrine.Atomizes r.source F) :
    F = (AATCorePackage.generate S r).family

theorem AATCorePackage.generate_configuration_family_eq
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).configuration.family =
      (AATCorePackage.generate S r).family

theorem AATCorePackage.generate_configuration_familySupported
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).configuration.FamilySupported

theorem AATCorePackage.generate_object_configuration_eq
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).object.configuration =
      (AATCorePackage.generate S r).configuration

theorem AATCorePackage.generate_lawReading_eq {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).algebra.lawReading = r.lawReading

theorem AATCorePackage.generate_algebra_base_object
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).algebra.object
      (AATCorePackage.generate S r).baseObject =
        (AATCorePackage.generate S r).object

theorem AATCorePackage.generate_algebra_operation_source
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B) :
    ((AATCorePackage.generate S r).algebra.operation op).source =
      (AATCorePackage.generate S r).algebra.object A

theorem AATCorePackage.generate_algebra_operation_target
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B) :
    ((AATCorePackage.generate S r).algebra.operation op).target =
      (AATCorePackage.generate S r).algebra.object B

theorem AATCorePackage.generate_circuit_sound
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    (A : (AATCorePackage.generate S r).algebra.Obj)
    (i : (AATCorePackage.generate S r).algebra.lawReading.lawUniverse.Index)
    (c : (AATCorePackage.generate S r).algebra.Circuit A i) :
    ¬ ((AATCorePackage.generate S r).algebra.lawReading.lawUniverse.law i).holds
      ((AATCorePackage.generate S r).algebra.object A)

theorem AATCorePackage.generate_algebra_operation_maps_family
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a : U.Atom}
    (ha : ((AATCorePackage.generate S r).algebra.object A).configuration.family.mem a) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.family.mem
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a)

theorem AATCorePackage.generate_algebra_operation_maps_relation
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a b : U.Atom}
    (hab : ((AATCorePackage.generate S r).algebra.object A).configuration.relation a b) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.relation
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a)
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap b)

theorem AATCorePackage.generate_algebra_operation_maps_identification
    {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a b : U.Atom}
    (hab : ((AATCorePackage.generate S r).algebra.object A).configuration.identification a b) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.identification
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a)
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap b)
```

`CoreReading`に許されるのはdoctrine、source、finite evidence、全familyに作用するcomposition rule、
全configurationに作用するobject rule、law/circuit semantics、invariant/signature/operation ruleである。
生成済み`AtomFamily`、`AtomConfiguration`、`ArchitectureObject`、selected circuit、selected operation、
完成済み`ObjectAlgebra`またはそれらとの一致証明をfieldとして追加しない。

`CircuitReading.RequiredComplete`はlawfulnessとrequired circuit fiberの空性を同値に読むための
追加条件であり、core generationの必須fieldにしない。この条件はrequired failureが有限個の
presence / absence queryで検出可能であることを述べる。非恒等operationとnonempty circuit fiberは
concrete modelの性質として別々に証明する。

### SD2 — selected geometry reading

```lean
structure Site.CoverageRequirements {U : AtomCarrier.{u}}
    (A : ArchitectureObject U) (LU : LawUniverse U)
    (Sig : ArchitectureSignature U) where
  requiredSupport : U.Atom -> Prop
  requiredWitness : LU.witnessFamily.Witness -> Prop
  requiredAxis : Sig.Axis -> Prop
  supportVisibleOn : Site.ArchCtx A -> U.Atom -> Prop
  witnessVisibleOn : Site.ArchCtx A -> LU.witnessFamily.Witness -> Prop
  axisReadableOn : Site.ArchCtx A -> Sig.Axis -> Prop
  boundaryVisibleOn : Site.ArchCtx A -> Site.ArchCtx A -> Prop

structure Site.SelectedGeometryReading {U : AtomCarrier.{u}}
    (core : AATCorePackage U) where
  contextPreorder : Site.ContextPreorderCategory core.object
  requirements : Site.CoverageRequirements core.object
    core.algebra.lawReading.lawUniverse core.algebra.signatureReading
  overlap : Site.ContextOverlapPullback contextPreorder

def Site.SelectedGeometryReading.toAATSite {U : AtomCarrier.{u}}
    {core : AATCorePackage U} (reading : Site.SelectedGeometryReading core) :
    Site.AATSite core.object

theorem Site.SelectedGeometryReading.topology_eq_generated
    {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (reading : Site.SelectedGeometryReading core) :
    reading.toAATSite.topology =
      Site.AATGrothendieckTopology reading.requirements reading.overlap
```

`Site.SelectedGeometryReading`は、
`core.algebra.lawReading.lawUniverse`に型付けされたcoverage requirements、context preorder、
overlap dataだけを保持する。
selected readingは`LawUniverse.selectedReading`に一本化し、coverage packageの中で
別の値を再選択しない。
このsignature変更では、`CoverageRequirements`だけでなく、これを引数に取る
`AdmissibleCover`、`AATCoverageFamily`、`admissiblePrecoverage`、
`AATGrothendieckTopology`、`AATSite`、`UAdequacyRequirements`、`UAdequateCover`を
同じPRで一括移行する。旧`selectedReading` fieldやreading引数付きpredicateを保持するadapterを
新しい主経路には置かない。
`toAATSite`は`AATSite core.object`を返し、`topology_eq_generated`はそのtopologyが
admissible coverageから生成されたMathlib `GrothendieckTopology`であることを述べる。
architecture object、law reading、signature readingは`core`から読み、coefficient ringは
raw algebra層の独立parameterとする。異なるlaw universeを使うgeometryは、law readingを変更した
別のcore readingとして表す。

### SD3 — typed raw algebra presheaf

```lean
structure RawAmbientRestrictionSystem
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k] where
  coordFamily : (W : S.category) -> CoordinateFamily W.ctx
  relationFamily : (W : S.category) ->
    StructuralRelationFamily (coordFamily W) k
  restrictionStable : ∀ {X Y : S.category} (f : X ⟶ Y),
    RestrictionStableStructuralRelations
      (relationFamily X) (relationFamily Y)
      (S.contextPreorder.morphism (CategoryTheory.leOfHom f))
  identity_polynomialMap : ∀ X : S.category,
    (restrictionStable (𝟙 X)).restriction.polynomialMap =
      RingHom.id (FreeTypedCommAlg (coordFamily X) k)
  composition_polynomialMap :
    ∀ {X Y Z : S.category} (f : X ⟶ Y) (g : Y ⟶ Z),
      (restrictionStable (f ≫ g)).restriction.polynomialMap =
        ((restrictionStable f).restriction.polynomialMap).comp
          ((restrictionStable g).restriction.polynomialMap)

abbrev RawAmbientRestrictionSystem.rawAlgebra
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientRestrictionSystem S k) (W : S.category) :
    Type (max u v) :=
  (B.relationFamily W).RawAmbientLawAlgebra

theorem TypedCoordinateRestriction.polynomialMap_C
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : CoordinateFamily source}
    {targetFamily : CoordinateFamily target}
    {k : Type v} [CommRing k]
    {f : Site.ContextMorphism source target}
    (rho : TypedCoordinateRestriction sourceFamily targetFamily k f)
    (x : k) :
    rho.polynomialMap (MvPolynomial.C x) = MvPolynomial.C x

theorem RestrictionStableStructuralRelations.quotientDesc_C
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : CoordinateFamily source}
    {targetFamily : CoordinateFamily target}
    {k : Type v} [CommRing k]
    {sourceRelations : StructuralRelationFamily sourceFamily k}
    {targetRelations : StructuralRelationFamily targetFamily k}
    {f : Site.ContextMorphism source target}
    (h : RestrictionStableStructuralRelations
      sourceRelations targetRelations f) (x : k) :
    h.quotientDesc (targetRelations.quotientMap (MvPolynomial.C x)) =
      sourceRelations.quotientMap (MvPolynomial.C x)

theorem RawAmbientRestrictionSystem.quotientDesc_id
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientRestrictionSystem S k) (X : S.category) :
    (B.restrictionStable (𝟙 X)).quotientDesc =
      RingHom.id (B.rawAlgebra X)

theorem RawAmbientRestrictionSystem.quotientDesc_comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientRestrictionSystem S k)
    {X Y Z : S.category} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (B.restrictionStable (f ≫ g)).quotientDesc =
      ((B.restrictionStable f).quotientDesc).comp
        ((B.restrictionStable g).quotientDesc)

noncomputable def RawAmbientRestrictionSystem.toPresheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientRestrictionSystem S k) :
    AlgebraValuedAATPresheaf S k

noncomputable def RawAmbientRestrictionSystem.toPresheafObjectIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientRestrictionSystem S k) (W : S.category) :
    B.rawAlgebra W ≃+* (B.toPresheaf.obj (Opposite.op W)).right

theorem RawAmbientRestrictionSystem.toPresheaf_map
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientRestrictionSystem S k)
    {X Y : S.category} (f : X ⟶ Y) (x : B.rawAlgebra Y) :
    B.toPresheafObjectIso X ((B.restrictionStable f).quotientDesc x) =
      (B.toPresheaf.map f.op).right (B.toPresheafObjectIso Y x)
```

`identity_polynomialMap`と`composition_polynomialMap`はquotient前のtyped polynomial restrictionの
coherenceである。`quotientDesc_id`と`quotientDesc_comp`は、それらと
`restrictionStable.maps_JStruct`をproof bodyで使って証明する。
`toPresheaf`はこの二定理からactual functor lawを構成し、`polynomialMap_C`と
`quotientDesc_C`によって`AATCommAlgCat k`のUnder-structureを保存する。
arbitrary presheaf、object equivalence、naturalityは入力しない。

### SD4 — ringed AAT site

```lean
structure RingedAATSite
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k] where
  raw : AlgebraValuedAATPresheaf S k

def RingedAATSite.site
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k) : Site.AATSite A := S

def RingedAATSite.architectureObject
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k) : ArchitectureObject U :=
  S.architectureObject

noncomputable def RingedAATSite.ofMathlibSheafification
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (raw : AlgebraValuedAATPresheaf S k) : RingedAATSite S k

noncomputable def RingedAATSite.structureSheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    LawAlgebraSheaf S k

noncomputable def RingedAATSite.canonical
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    R.raw ⟶ R.structureSheaf.val

@[simp] theorem RingedAATSite.structureSheaf_eq_sheafify
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    R.structureSheaf =
      (CategoryTheory.presheafToSheaf
        S.topology (AATCommAlgCat k)).obj R.raw

@[simp] theorem RingedAATSite.canonical_eq_toSheafify
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    R.canonical = CategoryTheory.toSheafify S.topology R.raw

theorem RingedAATSite.lift_unique
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (F : LawAlgebraSheaf S k) (η : R.raw ⟶ F.val) :
    ∃! lift : R.structureSheaf.val ⟶ F.val,
      R.canonical ≫ lift = η

def AATCommAlgToType (k : Type v) [CommRing k] :
    AATCommAlgCat.{u, v} k ⥤ Type (max u v) :=
  CategoryTheory.Under.forget
      (CommRingCat.of (ULift.{max u v, v} k)) ⋙
    CategoryTheory.forget CommRingCat

noncomputable def RingedAATSite.underlyingTypeSheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    [S.topology.HasSheafCompose (AATCommAlgToType k)] :
    CategoryTheory.Sheaf S.topology (Type (max u v))

@[simp] theorem RingedAATSite.underlyingTypeSheaf_val
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    [S.topology.HasSheafCompose (AATCommAlgToType k)] :
    R.underlyingTypeSheaf.val =
      R.structureSheaf.val ⋙ AATCommAlgToType k
```

`structureSheaf`と`canonical`は`raw`のMathlib sheafificationとそのunitから定義し、
structure fieldとして選択させない。`underlyingTypeSheaf`はstructure sheafに
`AATCommAlgToType`をwhiskerして構成する。係数環のuniverseによりtargetは
`Type (max u v)`であり、現行の`Type u`固定`Site.AATSh`とは区別する。
Mathlibのwhiskeringに必要な`HasSheafCompose (AATCommAlgToType k)`はinstance parameterとして明示し、
別のType-valued sheafを入力するpremiseにはしない。
sheafificationの普遍性は自由なfieldにせずMathlib `HasSheafify`から証明する。
無関係なType-valued sheaf、`LocallyRingedSpace`、presentation certificateを入力しない。

### SD5 — end-to-end constructor

```lean
noncomputable def generateRingedAATSite
    {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U)
    (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (AATCommAlgCat k)] :
    RingedAATSite reading.toAATSite k

@[simp] theorem generateRingedAATSite_site
    {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (AATCommAlgCat k)] :
    (generateRingedAATSite S coreReading reading k raw).site =
      reading.toAATSite

@[simp] theorem generateRingedAATSite_raw
    {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (AATCommAlgCat k)] :
    (generateRingedAATSite S coreReading reading k raw).raw =
      raw.toPresheaf

@[simp] theorem generateRingedAATSite_structureSheaf
    {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (AATCommAlgCat k)] :
    (generateRingedAATSite S coreReading reading k raw).structureSheaf =
      (CategoryTheory.presheafToSheaf
        reading.toAATSite.topology (AATCommAlgCat k)).obj raw.toPresheaf

@[simp] theorem generateRingedAATSite_canonical
    {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (AATCommAlgCat k)] :
    (generateRingedAATSite S coreReading reading k raw).canonical =
      CategoryTheory.toSheafify
        reading.toAATSite.topology raw.toPresheaf

@[simp] theorem generateRingedAATSite_architectureObject
    {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (coreReading : CoreReading U)
    (reading : Site.SelectedGeometryReading
      (AATCorePackage.generate S coreReading))
    (k : Type v) [CommRing k]
    (raw : RawAmbientRestrictionSystem reading.toAATSite k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (AATCommAlgCat k)] :
    (generateRingedAATSite S coreReading reading k raw).architectureObject =
      (AATCorePackage.generate S coreReading).object
```

五本のcharacterization theoremは、site、raw presheaf、structure sheaf、canonical map、
architecture objectがそれぞれ`reading.toAATSite`、`raw.toPresheaf`、Mathlib sheafification、
`toSheafify`、`AATCorePackage.generate S coreReading`に由来することを固定する。
任意のcommutative-ring-valued sheafificationからstalkのlocal-ring性は従わないため、
`LocallyRingedSpace`や`CanonicalLocallyRingedAATSite`はSD5のconstructor targetに含めない。

## 問い

固定されたAtom公理系、admissible core reading、coverage requirements、coefficient ringから、
次の対象を同じ入力provenanceの下でLean上に生成できるか。

```text
Atom axiom system
  + admissible core reading
  -> Atom family / configuration / architecture object
  -> core law reading / circuit type family / signature / operation family / AAT core
  + coverage requirements / coefficient ring
  -> architecture context category
  -> admissible coverage and generated Grothendieck topology
  -> AAT site
  -> typed raw coordinate algebra presheaf
  -> commutative-ring-valued sheafification
  -> ringed AAT site presentation
```

完了対象は、無関係に選択されたsite、presheaf、sheaf、ringed spaceをpackageへ並べることではない。
各矢印をdefinition、constructor、universal property、comparison theoremで構成し、
後続のscheme・ideal・cohomology形式化が同じsiteとstructure sheafを再利用できる基盤を作る。

## 現状診断

- `AATCorePackage`、`PartIPrerequisites`、`ArchitectureGeometry`、`AATSite`、
  `AATGrothendieckTopology`は存在する。
- 現行`AtomAxiomSystem`はabstract `Family` / `Configuration` carrierと`compose`を保持するが、
  `ExtractionDoctrine`の`atomize`はactual `AtomFamily U`を返さない。Part I 定義10.4Aの
  actual core readingとしては未接続である。また現行A8は`atomize`を関数として置いた上で
  同じ関数値への等式から一意性を返すため、extraction semanticsを特徴付ける`atomizes` relationを持たない。
- `AATCorePackage.ofComponents`はfamily、configuration、architecture object、law universe、
  obstruction circuit、signatureをすべて受け取り、`ofAxiomRealization`も後段componentを受け取る。
  現行主経路はAtom公理系からのgeneration theoremではなくselected componentのassemblyである。
- 現行`ObstructionCircuit`は`law_failure`をfieldとして持ち、現行`AATCorePackage`はその
  selected elementを必須fieldとして持つ。これはPart I 定義8.2のfinite datum + finite-template
  Boolean detector + matching + soundness、および定理10.5のcircuit type familyと一致しない。
- 現行`ObjectAlgebra`の`Op`と`Ob`はobject pair / lawに添字付けられておらず、
  `AATCorePackage.objectAlgebraOfComponents`は`PUnit`上のsingleton object/operationを使う。
  Part I 定義10.1のindexed familyとoperation closureには未接続である。
- `RawAmbientPresheafBridge`と`RawAmbientAlgebraPresheafBridge`は、context-indexed raw algebraと
  site-indexed presheafの対応を記録する。
- `LawAlgebraSheafificationBridge`はsheafified objectと普遍性を記録し、
  `ofMathlibSheafification`はMathlibの`HasSheafify`から構成できる。
- `LawAlgebraSheafPackage`はraw presheaf、sheafification、presentation stabilityをまとめるが、
  `SelectedLawAlgebraPresentation`の`presentsRaw`と`presentsSheafified`は自由な`Prop`である。
- `RingedAATTopos`はType-valued sheaf object、law algebra sheaf package、
  `LocallyRingedSpace`を独立に格納でき、それらが同じringed geometryを表すことを型が保証しない。
- 現在の`ArchitectureGeometry`は`PartIPrerequisites`のobjectとsiteを結ぶが、
  raw coordinate dataからstructure sheafまでの一本の公開constructorを持たない。

既存の各部品は再利用する。課題は新しい包括wrapperを加えることではなく、
既存部品の入力provenanceと標準Mathlib対象への接続をload-bearingなAPIにすることである。

## アウトカム

完了時に次が成り立つ。

1. Atom公理系とadmissible core readingからfamily、configuration、architecture object、
   core law/circuit reading、signature reading、operation-closed object algebraを生成する公開経路がある。
2. 生成済みcoreから、そのlaw universeに型付けされたcoverageを持つAAT siteまでの公開constructorがある。
3. typed coordinate family、structural relations、restriction dataからraw ambient algebra presheafが構成される。
4. structural relation idealのrestriction stabilityが、quotient restriction mapとpresheaf functorialityの証明に実際に使われる。
5. Mathlib sheafificationからcommutative-ring-valued structure sheafとcanonical mapが構成される。
6. siteとstructure sheafを同じ対象として保持するringed AAT site presentationがある。
7. underlying Type-valued sheafはstructure sheafのforgetful imageとして得られ、無関係な入力として受け取らない。
8. 少なくとも一つの非退化有限モデルが同じ`(AtomAxiomSystem, CoreReading)`からcore、site、
   raw algebra、structure sheafまで発火し、非恒等operationと実在するfinite circuitを別々に示す。
9. 後続のscheme・ideal形式化が新基盤をdefinition unfoldなしで利用できるAPIを持つ。

## 採否規律

- 実装ループ中は、本PRDが参照するPart I 定義8.2、定義10.1、定義10.4A、定理10.5と
  Part II 定義2.1を固定入力として扱い、変更が必要なら停止する。
- `AATCorePackage.ofComponents`または`ofAxiomRealization`によるassemblyだけを
  Atom-to-ringed-site generationの完了証拠にしない。
- 本文の定理10.5をLean都合でcomponent assembly theoremまたはbare axiomsからの
  無条件existence theoremへ変形しない。
- `AATSite`、Mathlib `GrothendieckTopology`、`Sheaf`、`Under CommRingCat`を再発明しない。
- conclusion-shaped propertyをstructure field、typeclass、certificateへ追加しない。
- sheafificationの普遍性、presheaf functoriality、restriction compatibilityを
  supplied proof packageから射影するだけの主定理を完了根拠にしない。
- legacy declarationは直ちに削除しない。新基盤へsoundに変換できる場合だけadapterを置く。
- core law universeとcircuit semanticsは`CoreReading.lawReading`から生成し、実在する
  circuitはindexed type familyのelementとして扱う。selected circuitをcore generationへ入力しない。
- geometryのcoverageはgenerated core law universeに型付けし、coefficientはgeometry parameterとして入力する。
- target statementと参照definitionは、このPRDの`Statement Design`節を不変入力とする。

## 改修要求

### R0 — 現行宣言と固定statementの確定

- tracking Issueに対象main commitを固定する。
- `AATCorePackage`、`PartIPrerequisites`、`ArchitectureGeometry`、`AATSite`、
  raw algebra bridge、sheafification bridge、`LawAlgebraSheafPackage`の完全なsignatureと依存を棚卸しする。
- 各material premiseを本文由来、放電済み、未放電へ分類し、tracking Issueに記録する。

### R1 — Atom towerとAAT coreのgeneration

- 現行`AtomAxiomSystem`をSD1のaxiom-level signatureへ移行し、空虚な`singleFact` markerと、
  旧abstract `Family` / `Configuration` / `Law` / `Observation` / `Operation` / `Doctrine` fieldを
  主生成経路から除く。
- `ExtractionDoctrine U`がvocabulary、semantic reading、resolution、source semantics、normalizationから
  atom-level `extracts source atom`を定義し、`atomize source` をそのmembership extensionとして構成する。
  `Atomizes`はこのmembership characterizationとし、`atomize_holds`と`atomize_unique`は定理として証明する。
  選択sourceに対する`ListFinite` evidenceを
  `CoreReading`が保持する形へ移行する。finite evidenceはA4のcomposition domainであり、
  生成済みfamilyとの一致を受け取るcertificateではない。
- `CompositionReading.compose`がactual finite familyからactual configurationを構成し、
  family equalityとrelation / identification supportを証明する。
- `ObjectReading.object`がactual configurationからarchitecture objectを構成し、
  configuration equalityを証明する。
- `CircuitQuery`、`CircuitQuery.Holds`、`FiniteCircuitDatum`、`FiniteCircuitDatum.Matches`、
  `CircuitDetectorCode`、`CircuitDetectorCode.eval`、`CircuitReading.accepts`、`CircuitReading.sound`、
  indexed `Circuit`を実装する。detector codeはfinite exact templateと有限選言だけから構成し、
  object、law predicate、law-failure proofを格納しない。
- semantic obstructionは`SemanticObstruction L A := ¬ L.holds A`として公開し、
  legacy `Obstruction` structureを新主経路のcertificateに使わない。
- 現行`ObstructionCircuit.law_failure`を主経路から除き、旧APIが必要なら
  `CircuitReading.sound`からfailureを導く一方向adapterだけを置く。
- `ObjectAlgebra.Op`をobject pairに添字付け、circuitをobject / law indexに添字付けた
  derived type familyとして公開する。selected operationとselected circuitを必須fieldにしない。
- `ConfigurationHom`にactual atom map、family membership、relation、identificationのtransportを実装し、
  `Operation`と`OperationReading`の主経路をこのhomomorphismで定義する。endpoint上の任意の`Prop`で
  A7を閉じない。
- `OperationReading.Reachable`によりbase objectを含む最小のoperation-closed object familyを構成し、
  `AATCorePackage.algebra`の`Obj`とする。
- `AATCorePackage.generate S r`からfamily、configuration、object、law/circuit reading、
  invariant/signature reading、object algebraをdefinitionで生成し、SD1のcharacterization theoremを証明する。
- `CoreReading`に生成済みcomponentまたは完成済みalgebraを追加してconstructorを閉じない。
- object algebraはsingleton identity exampleだけでなく、少なくとも二つのreachable object間の
  非恒等operationを持つfinite modelで発火させる。
- circuit exampleはconcrete finite query pattern、matching、finite-template detector codeのBool acceptanceを与え、
  soundnessからlaw failureを導く。accepted / rejected datumを別々計算する。
  非恒等operationのexistenceとcircuitのexistenceを同じfieldで要求しない。
- geometryのcoverage requirementsとoverlap dataが、同じgenerated architecture objectと
  `core.algebra.lawReading.lawUniverse`に型付けされるようにする。
- source、Atom vocabulary、law、coverage、coefficientの相対性を、巨大な万能structureではなく
  既存型のparameterと小さいcomparison definitionで表す。
- `CoreReading`は`AtomCarrier U`に直接添字付け、`AtomAxiomSystem U`は
  `AATCorePackage.generate S r`で認証データとして統合する。使われない`S`をreadingのindexに残さない。
- `ArchitectureGeometry`またはadditiveな後継型からAAT siteへのconstructorを作る。
- coreと無関係なarchitecture objectまたはlaw universeを差し替えられないことを型とcharacterization theoremで保証する。

### R2 — coverageからGrothendieck topologyまでの生成経路

- admissible coverageから`AATGrothendieckTopology`を生成する現行経路を新APIへ接続する。
- `CoverageRequirements`のselected reading一本化に伴い、`Coverage.lean`、`Topology.lean`、
  `Geometry.lean`、`Adequate.lean`のcoverage / topology / site / adequacy APIを新signatureへ一括移行する。
  旧signatureを要求するadapterは主経路に残さない。
- identity、base change、transitivityはMathlibの生成位相APIまたは現行証明へ接続する。
- topologyがselected coverage requirementsから生成されたことをcharacterization theoremで公開する。
- finite-poset regimeを一般APIの実例として接続し、別理論として複製しない。

### R3 — typed raw coordinate algebra presheafの実構成

- contextごとのtyped coordinate familyとstructural relation familyから
  `FreeTypedCommAlg`およびstructural quotient algebraを構成する。
- context morphismに沿うcoordinate restrictionがstructural relation idealを保存することから、
  quotient ring homを構成する。
- `RawAmbientRestrictionSystem`のprequotient `identity_polynomialMap`と
  `composition_polynomialMap`、およびstructural-ideal stabilityからquotient restrictionのidentityとcompositionを
  証明し、actual `AlgebraValuedAATPresheaf`を構成する。
- `polynomialMap_C`と`quotientDesc_C`を証明し、restriction mapがcoefficient structure mapと可換する
  `AATCommAlgCat k`のmorphismになることを示す。
- arbitrary presheaf、objectwise equivalence、naturalityを受け取るbridgeは主経路に使わず、
  `RawAmbientRestrictionSystem.toPresheaf`のcharacterization theoremとしてobject/map provenanceを得る。
- raw presheafのobjectwise algebraがselected contextのraw ambient quotientと一致することを公開APIにする。

### R4 — Mathlib sheafificationによるstructure sheaf

- R3のraw presheafに対し、利用可能な`HasSheafify`からMathlib sheafificationを構成する。
- canonical map、sheaf condition、universal propertyをMathlib APIから証明する。
- `LawAlgebraSheafificationBridge.ofMathlibSheafification`を主経路へ接続する。
- `SelectedLawAlgebraPresentation`の自由な`presentsRaw` / `presentsSheafified`は、
  新しい主経路の完成根拠に使わない。
- selected presentationが必要な場合は、generator map、quotient comparison、surjectivity、kernel equality、
  algebra isomorphismのいずれか本文の要求に対応する具体述語へ分解する。

### R5 — ringed AAT site presentation

- AAT siteとその上のcommutative-ring-valued structure sheafを同じ対象として保持する新coreを導入する。
- underlying Type-valued sheafはstructure sheafに対する`AATCommAlgToType`から構成し、
  target universeを`Type (max u v)`とする。Mathlib whiskeringの`HasSheafCompose`は明示instanceとする。
- restriction ring hom、global/local section、canonical raw-to-sheafified mapへアクセスするAPIを持つ。
- extensionality、constructor/destructor、forgetful comparison、legacy comparisonを用意する。
- `RingedAATTopos`から新coreへの変換は、stored componentsの一致を証明できる場合だけ提供する。
- 新coreからlegacy surfaceへの一方向adapterは、既存利用者の段階的移行に必要な場合だけ提供する。

### R6 — 非退化finite vertical slice

- 非自明なcoefficient ring、複数context、非恒等restrictionを持つfinite modelを固定する。
- 同一`(AtomAxiomSystem, CoreReading)`入力からAAT site、raw algebra presheaf、canonical sheafification、
  ringed site presentationを構成する。
- 同じfinite modelで、少なくとも一つのfinite-template detector code、accepted datum、
  rejected datum、accepted datumのsoundness、および別のnonempty law/circuit fiberを具体化する。
- 非恒等operationはactual `ConfigurationHom`のatom mapが少なくとも一のAtomを別のAtomへ送り、
  family membershipと少なくとも一のrelationまたはidentificationを実際にtransportすることを証明する。
- 少なくとも一つのstructural relationがquotientとrestrictionに実際に影響することをLean theoremで示す。
- singleton site、`PUnit`だけのcarrier、all-`True` property、定数零restrictionだけのexampleを主発火証拠にしない。

### R7 — API統合・監査・台帳同期

- 新moduleを`Formal/AG.lean`へ接続する。
- target declarationsとfinite exampleを`Formal/AG/AxiomAudit.lean`へ追加する。
- statement contractsを通常aggregateとCIでelaborateさせる。
- 変更した本文対応宣言をLean theorem indexとproof-obligation台帳へ同期する。
- `Formal/AG`からResearch moduleをimportしない。

## Acceptance Criteria

- [ ] AC1: executable contractが主constructor、ringed site presentation、非退化exampleの実装signatureを直接参照する。
- [ ] AC2: `ExtractionDoctrine.extracts`がvocabulary、semantic reading、resolution、normalized source semanticsを
  proof-useし、`atomize`のactual `AtomFamily U` membershipを定義する。`Atomizes`はこのmembershipとの同値であり、
  canonicalityとfixed doctrine/sourceに対するA8 uniquenessがfieldではなく定理として証明される。
  concrete `ListFinite` evidence、compositionのfamily equality、
  relation / identification support、objectのconfiguration equalityが
  証明され、生成済みcomponentの再包装ではない。
- [ ] AC3: generated objectを含む`OperationReading.Reachable` closureとobject-pair-indexed `Op`が
  構成され、少なくとも二つのreachable object間の非恒等operationがactual `ConfigurationHom`を持ち、
  family membershipとrelation / identificationのtransportがproof-usedされるmodelで発火する。
- [ ] AC4: finite circuitがsigned query datum、matching、finite-template `CircuitDetectorCode`のBool acceptanceから
  構成され、law failureは`CircuitReading.sound`から導かれる。detector grammarはobject、law predicate、
  law-failure proofを持たず、finite modelはaccepted / rejected datumを別々計算する。
- [ ] AC5: generated coreのobject / law readingに型付けされたcoverageからAAT siteと
  actual Mathlib `GrothendieckTopology`が生成され、signature / coverage provenanceを失わない。
- [ ] AC6: typed coordinateとstructural relation、prequotient polynomial restriction coherenceからactual
  algebra-valued presheafが構成され、quotient restriction identity/compositionとcoefficient-map compatibilityが証明される。
- [ ] AC7: structural relation idealのrestriction stabilityがquotient restriction mapのproof bodyで使われ、非自明relationがquotientと少なくとも一つのrestriction mapを実際に変える。
- [ ] AC8: raw presheafのMathlib sheafificationからactual commutative-ring-valued sheaf、canonical map、universal propertyが得られる。
- [ ] AC9: ringed AAT site presentationがsiteとstructure sheafを同じ対象として保持し、無関係なType-valued sheafやlocally ringed spaceを入力しない。
- [ ] AC10: underlying `Type (max u v)`-valued sheafがstructure sheafの`AATCommAlgToType`による
  forgetful imageとして構成され、`underlyingTypeSheaf_val`がその合成を特徴付ける。
- [ ] AC11: 新主経路は`law_failure : ¬ L.holds A`、`presentsRaw : Prop`、
  `presentsSheafified : Prop`その他の結論相当certificateの射影だけで閉じない。
- [ ] AC12: 非退化finite vertical sliceが同一`(AtomAxiomSystem, CoreReading)`からcore、site、
  raw presheaf、structure sheafまで発火する。
- [ ] AC13: `generate`、indexed object algebra、circuit family、site、ringed siteの新definitionに
  constructor/destructor/ext/characterization APIがあり、主要利用者がdefinition unfoldに依存しない。
- [ ] AC14: target declarationsとexampleがstandard axiomsのみを使用し、statement contractsとaxiom auditがgreenである。
- [ ] AC15: Part I 定義8.2 / 10.1 / 10.4A / 定理10.5、Part II 定義2.1とLean declarationの
  対応が台帳へ同期され、実装ループ内で固定数学statementを変更していない。
- [ ] AC16: `math-lean-review`の4本の独立査読がすべて`No major findings`である。

## Failure Contract

次は完了ではなく失敗である。

- unrelated componentsを並べたpackageの追加。
- `AATCorePackage.ofComponents`またはsingleton object algebraだけでAtom generationを主張すること。
- `CoreReading`に生成済みfamily / configuration / object / algebraと一致証明を格納し、provenanceと呼ぶこと。
- `ExtractionDoctrine.Atomizes`を`family = chosenFamily`のようなopaque relationとして再定義し、
  atom-level `extracts`を経由せずにA8を閉じること。
- `CircuitDetectorCode`またはその代替grammarにarchitecture object、`Law.holds`、
  `¬ law.holds A`のproof、arbitrary `Prop`を格納し、failureをfinite patternとして再包装すること。
- `Operation`をendpoint上の`True`または任意の`Prop`だけで構成し、actual atom mapと
  family / relation / identification transportを持たせないこと。
- selected circuitまたはselected operationをcoreの必須fieldに戻すこと。
- arbitrary presheaf、objectwise equivalence、naturalityを入力して生成と呼ぶこと。
- presheaf functoriality、sheaf condition、sheafification普遍性を結論相当fieldから射影すること。
- `True`、未使用material premise、singletonだけで主経路を発火させること。
- Mathlib対象と接続しないAAT専用presheaf・sheaf・ringed objectの再発明。
- current codeが難しいことを理由に数学本文の主張を弱めること。

## 停止条件

- 数学本文の主張にLean実装と独立した反例、型不整合、well-definedness欠陥が見つかった。
- fixed statementを弱める、material premiseを追加する、参照definitionのsignatureを結論相当に変更する必要が生じた。
- Mathlib sheafificationを利用できず、同じ普遍性を持つ構成も対象範囲内で実装できない。
- Atom公理系とSD1の`CoreReading`からactual family/configuration/objectを生成するために、
  本文にないmaterial premiseがさらに必要と判明した。
- 現行`ObstructionCircuit.law_failure`をfinite query datum + matching + finite-template Bool detector + soundnessへ
  移行できず、結論相当fieldを主経路に残す必要が生じた。
- actual `ConfigurationHom`からoperation closureを構成できず、endpoint上の命題だけを
  operation evidenceとして残す必要が生じた。
- 非退化finite modelが構成できず、退化例だけが残る。

停止報告には、該当AC、最小の反例またはAPI blocker、試した構成、未放電仮定、
本文改訂の要否、独立タスクとして切り出す候補を記録する。

## Non-goals

- standard `Scheme`、affine atlas、closed subschemeの構成。
- law-generated ideal sheaf、lawful locus、conormal sheaf、Čech obstructionの構成。
- Part IIIのrestriction-stable local circuit family `Circ_U^loc`、ideal-to-coefficient morphism `rho`、
  circuit coefficient `kappa`の構成。SD1のglobal circuit familyに無条件なrestrictionを追加しない。
- coverage refinement、coefficient base changeを含む一般reading functoriality。
- `SignedExactCoreReadingHom`と`PositiveCoreReadingHom`のLean実装。数学statementはPart Iで分離済みとし、
  vocabulary refinementからsigned circuit全体のtransportを仮定しない。
- G-07または他のResearch成果の本体蒸留。
- 数学本文へのLean status、Issue、PR、declaration名の追加。

## 検証

検証手順と実行主体は`AGENTS.md`の「よく使う検証」「PR前の確認」と
`docs/aat/guideline.md`を直接適用する。task固有の追加検査は、actual atomization、
doctrine / composition / object provenance、finite-template Bool detector soundness、actual configuration-map transport、
indexed operation closure、
raw presheaf functoriality、sheafification universal propertyを
statement contractsとaxiom auditが直接参照していることの確認である。
