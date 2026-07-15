# PRD: AAT Lean Closed-Equational Law Geometry

- 作成: 2026-07-12
- 改訂: 2026-07-15
- 対象module:
  - `Formal/AG/LawAlgebra/ClosedEquationalGeometry.lean`
  - `Formal/AG/LawAlgebra/ClosedEquationalGeometryFiniteExample.lean`
  - `Formal/AG/StatementContractsClosedEquationalGeometry.lean`
  - `Formal/AG/AxiomAudit.lean`
  - `Formal/AG/LawAlgebra.lean`
  - `Formal/AG/StatementContracts.lean`
  - `Formal/AG.lean`
- 数学的正典:
  - `docs/aat/algebraic_geometric_theory/part_3_law_algebra_obstruction_ideal_lawful_locus.md`
    定義5.1、5.2、5.2A、5.2B、6.1、6.2、7.1、7.2、定理11.1、
    定義11.3、定理11.4
  - `docs/aat/algebraic_geometric_theory/appendix.md` A.6〜A.8
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、
  `docs/aat/lean_quality_standard.md`
- tracking Issue: 未作成。Issue作成と依存登録が済むまで実行不可
- statement contract正本: 本PRDの`Statement Design`
- executable contract: `Formal/AG/StatementContractsClosedEquationalGeometry.lean`
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

次をすべて満たした時点で実装を開始する。

1. tracking Issueに対象main commit、担当module、SD0〜SD9のtarget一覧、SD8のmaterial premise表、
   親子Issue依存が登録されている。
2. 次のmerged宣言が対象main commit上に存在し、signatureが本PRDのSD0と一致している。
   - `RawAmbientRestrictionSystem`
   - `SemanticLawEquationWitnessIdealCore`
   - `AATReadingDecoration`
   - `AATReadingDecoration.pullback`
   - `StandardArchitectureScheme`
   - `StandardArchitectureScheme.affineOpenCover`
   - `FiniteExamples.StandardArchitectureScheme.twoChartReferenceModel`
3. Mathlibの次のAPIをscratch fileで`#check`し、採用するexact nameと引数順をIssueに固定している。
   - `Scheme.IdealSheafData`
   - `Scheme.IdealSheafData.ofIdealTop`
   - `Scheme.IdealSheafData.subscheme`
   - `Scheme.IdealSheafData.subschemeι`
   - `Scheme.IdealSheafData.subschemeCover`
   - `Scheme.IdealSheafData.subschemeObjIso`
   - `Scheme.IdealSheafData.ker_subschemeι`
   - `Scheme.IdealSheafData.range_subschemeι`
   - `Scheme.IdealSheafData.comap`
   - `Scheme.IdealSheafData.map_gc`
   - `Scheme.IdealSheafData.map_bot`
   - `Scheme.IdealSheafData.ideal_iSup`
   - `Scheme.IdealSheafData.inclusion`
   - `Scheme.IdealSheafData.inclusion_subschemeι`
   - `Scheme.IdealSheafData.inclusion_id`
   - `Scheme.IdealSheafData.inclusion_comp`
   - `IsClosedImmersion.lift`
   - `IsClosedImmersion.lift_fac`
   - `AffineChart.AffineAATChart.SheafifiedChartPresentation`
   - `sheafificationUnitAlgHom`
   また、`Formal/AG/LawAlgebra/ClosedEquationalGeometry.lean`は
   `Formal.AG.LawAlgebra.AffineChart`、
   `Formal.AG.LawAlgebra.StandardScheme`、
   `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`、
   `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`、
   `Mathlib.AlgebraicGeometry.Morphisms.Separated`を直接importする。
   最後のimportは`Scheme.IdealSheafData.inclusion`の`IsClosedImmersion` instanceに必要である。
4. 実装前statement reviewで、SD0〜SD7の全signatureとSD9のexample signatureが
   `Approved`になっている。

いずれかが欠ける間、このPRDは実行しない。

### Module import contract

transitive importへの偶然の依存を避けるため、担当moduleのdirect importを次で固定する。

| module | direct imports |
| --- | --- |
| `ClosedEquationalGeometry.lean` | `Formal.AG.Atom.LawfulnessZero`、`Formal.AG.LawAlgebra.LawEquation`、`Formal.AG.LawAlgebra.AffineChart`、`Formal.AG.LawAlgebra.StandardScheme`、`Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`、`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`、`Mathlib.AlgebraicGeometry.Morphisms.Separated` |
| `ClosedEquationalGeometryFiniteExample.lean` | `Formal.AG.LawAlgebra.ClosedEquationalGeometry`、`Formal.AG.LawAlgebra.StandardSchemeFiniteExample`、`Formal.AG.LawAlgebra.FiniteExamples` |
| `StatementContractsClosedEquationalGeometry.lean` | `Formal.AG.LawAlgebra.ClosedEquationalGeometry`、`Formal.AG.LawAlgebra.ClosedEquationalGeometryFiniteExample` |

`AxiomAudit.lean`は`Formal.AG`から到達するだけで済ませず、上記二実装moduleを直接importしてから
全new public theoremを監査namespaceへ登録する。aggregate側のdirect / transitive接続はR8とAC38で検査する。

## Statement Design

この節を本PRDの唯一のfixed statement designとする。別のMarkdown statement contractは作らない。
実装者はtarget名、namespace、共通parameter、入力、量化対象、主要definitionのshapeを変更しない。
変更が必要になった場合は実装を止め、該当SD、追加または削除した仮定、数学本文との対応を
tracking Issueへ報告して再承認を受ける。

`Formal/AG/StatementContractsClosedEquationalGeometry.lean`は、下記signatureを
`example : fixed type := implementation`の形で直接検査する。単なる`#check`、名前の存在、
別名、wrapper、同値な弱いstatementはcontract達成に数えない。

### 共通namespaceとparameter

```lean
namespace AAT.AG.LawAlgebra

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable (raw : RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (AATCommAlgCat k)]
variable (X : StandardArchitectureScheme raw)
```

全targetは同じ`raw`、`S`、`k`、`HasSheafify`、`X`を使う。
law indexは新しい独立型を保存せず、`S.lawUniverse.Index`を使う。
coordinate、signature、law universeは`X.decoration`から同じsite provenanceを読む。

### 固定対象 — atom-indexed exact restriction-stable regime

本PRDは、merged `SemanticLawEquationWitnessIdealCore`が与えるlaw/atom-indexed witness familyを、
同じraw quotient presentationとのobjectwise equivalence、canonical sheafification unit、
`X.decoration.interpretation`の順に送るregimeを実装する。
各witnessは同じatom indexでrestrictionされるため、coordinate equalityからbasic-open ideal equalityを導き、
actual `IdealSheafData`を直接構成する。

このcoreは数学本文の定義11.3・定理11.4をLeanへ蒸留した既存宣言である。本PRDは、
coreの`lawWitnessIdeal`をbridgeの環準同型で移したidealが、移されたatom-indexed coordinatesのspanと
一致することを固定し、そのspanをactual Scheme上のideal sheafへ接続する。

contextごとに任意のwitness type `Viol_i(V)`が変化する一般形、restriction inclusionだけからの
categorical sheaf-image constructionは本PRDのtargetに含めない。本PRDでは本文のcontext `W`を
actual Schemeのaffine open `V`として実体化し、lawのclosed-equationalityと`selected on V`を分離する。
selectionがbasic open restrictionで不変なexact caseでは、各`V`でselected lawを添字とするsupremumが
actual `IdealSheafData`をなす。selectionがrestrictionで増減する一般sheaf-image case全体の実装完了は
主張しない。この対象の制限はcore bridge、selection firing、Acceptance Criteriaで検査する。

### SD0 — geometric law readingとclosed-equational witness

section-level semantic predicateとequation witness dataを分ける。
semantic predicateはideal vanishingの別名にせず、witness dataはidealそのものをfieldに持たない。

```lean
/-- Test Scheme上のsectionに対する、site由来law indexごとのsemantic reading。 -/
structure GeometricLawReading where
  HoldsOn : ∀ {T : AlgebraicGeometry.Scheme},
    (T ⟶ X.underlying) → S.lawUniverse.Index → Prop

@[ext] theorem GeometricLawReading.ext
    (R Q : GeometricLawReading raw X)
    (h : @R.HoldsOn = @Q.HoldsOn) : R = Q

/-- `HoldsOn`がtest Schemeのbase changeで保存されること。 -/
def IsGeometricLawReading (R : GeometricLawReading raw X) : Prop :=
  ∀ {T T' : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) (f : T' ⟶ T) (i : S.lawUniverse.Index),
    R.HoldsOn s i → R.HoldsOn (f ≫ s) i

/-- law `i`のatom-indexed violation coordinatesを各affine open上に置くdata。 -/
structure ClosedEquationalLawWitness (i : S.lawUniverse.Index) where
  coordinate : ∀ V : X.underlying.affineOpens,
    U.Atom → Γ(X.underlying, V)

@[ext] theorem ClosedEquationalLawWitness.ext
    {i : S.lawUniverse.Index}
    (W Z : ClosedEquationalLawWitness raw X i)
    (h : W.coordinate = Z.coordinate) : W = Z

/-- witness coordinatesがbasic open restrictionと一致すること。 -/
def IsClosedEquationalLawWitness
    {i : S.lawUniverse.Index}
    (W : ClosedEquationalLawWitness raw X i) : Prop :=
  ∀ (V : X.underlying.affineOpens) (f : Γ(X.underlying, V)) (a : U.Atom),
    X.underlying.presheaf.map
        (homOfLE (X.underlying.basicOpen_le f)).op (W.coordinate V a) =
      W.coordinate (X.underlying.affineBasicOpen f) a

/-- 一つのlawのlocal witness idealはcoordinate rangeのspanである。 -/
def localLawWitnessIdeal
    {i : S.lawUniverse.Index}
    (W : ClosedEquationalLawWitness raw X i)
    (V : X.underlying.affineOpens) : Ideal Γ(X.underlying, V) :=
  Ideal.span (Set.range (W.coordinate V))

/-- coordinate compatibilityから、IdealSheafDataが要求するexact ideal equalityを導く。 -/
theorem localLawWitnessIdeal_map_basicOpen
    {i : S.lawUniverse.Index}
    (W : ClosedEquationalLawWitness raw X i)
    (hW : IsClosedEquationalLawWitness raw X W)
    (V : X.underlying.affineOpens) (f : Γ(X.underlying, V)) :
    Ideal.map
        (X.underlying.presheaf.map
          (homOfLE (X.underlying.basicOpen_le f)).op).hom
        (localLawWitnessIdeal raw X W V) =
      localLawWitnessIdeal raw X W (X.underlying.affineBasicOpen f)

/-- global equationsを各affine openへ制限するcanonical constructor。 -/
noncomputable def ClosedEquationalLawWitness.ofGlobalSections
    (i : S.lawUniverse.Index)
    (equation : U.Atom → Γ(X.underlying, ⊤)) :
    ClosedEquationalLawWitness raw X i

theorem ClosedEquationalLawWitness.ofGlobalSections_valid
    (i : S.lawUniverse.Index)
    (equation : U.Atom → Γ(X.underlying, ⊤)) :
    IsClosedEquationalLawWitness raw X
      (ClosedEquationalLawWitness.ofGlobalSections raw X i equation)

@[simp] theorem ClosedEquationalLawWitness.ofGlobalSections_coordinate
    (i : S.lawUniverse.Index)
    (equation : U.Atom → Γ(X.underlying, ⊤))
    (V : X.underlying.affineOpens) (a : U.Atom) :
    (ClosedEquationalLawWitness.ofGlobalSections raw X i equation).coordinate V a =
      X.underlying.presheaf.map (homOfLE le_top).op (equation a)

/-- existing core observableを同じraw quotient presentationへ同一視するprimitive data。 -/
structure SemanticLawEquationSchemeBridge
    (G : SemanticLawEquationWitnessIdealCore S) where
  toRawPresentation : ∀ W : S.category,
    G.Observable W ≃+* raw.rawAlgebra W

/-- bridge mapはraw presentation equivalenceとcanonical sheafification unitの合成である。 -/
noncomputable def SemanticLawEquationSchemeBridge.toSheafifiedSection
    {raw : RawAmbientRestrictionSystem S k}
    {G : SemanticLawEquationWitnessIdealCore S}
    (B : SemanticLawEquationSchemeBridge raw G)
    (W : S.category) : G.Observable W →+* SheafifiedSectionRing raw W :=
  (sheafificationUnitAlgHom raw W).toRingHom.comp
    (B.toRawPresentation W).toRingHom

@[ext] theorem SemanticLawEquationSchemeBridge.ext
    (G : SemanticLawEquationWitnessIdealCore S)
    (B C : SemanticLawEquationSchemeBridge raw G)
    (h : B.toRawPresentation = C.toRawPresentation) : B = C

/-- bridge validityはrestriction naturalityとcanonical presentation-stabilityを要求する。 -/
structure IsSemanticLawEquationSchemeBridge
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) : Prop where
  restriction_natural :
    ∀ {source target : S.category} (f : source ⟶ target)
      (x : G.Observable target),
      B.toSheafifiedSection source (G.restrict f x) =
        sheafifiedRestriction raw f (B.toSheafifiedSection target x)
  presentation_stable :
    ∀ W : S.category,
      AffineChart.AffineAATChart.SheafifiedChartPresentation raw W

/-- valid bridge mapはcore observableとcanonical section ringのbijectionである。 -/
theorem SemanticLawEquationSchemeBridge.toSheafifiedSection_bijective
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    (W : S.category) :
    Function.Bijective (B.toSheafifiedSection W)

/-- core witnessをselected decorationからactual global sectionへ送る。 -/
noncomputable def semanticCoreGlobalEquation
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (i : S.lawUniverse.Index) (a : U.Atom) : Γ(X.underlying, ⊤) :=
  X.decoration.interpretation
    (B.toSheafifiedSection X.decoration.context
      (G.violationWitness X.decoration.context i a))

/-- global equationsをsectionに沿ってgeneratorごとに評価するpredicate。 -/
def GlobalEquationsVanishAlong
    (equation : U.Atom → Γ(X.underlying, ⊤))
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  ∀ a, s.appTop (equation a) = 0

/-- core equation evaluationから作るcanonical geometric reading。 -/
noncomputable def GeometricLawReading.ofSemanticCore
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    GeometricLawReading raw X where
  HoldsOn s i :=
    GlobalEquationsVanishAlong raw X
      (semanticCoreGlobalEquation raw X G B i) s

theorem GeometricLawReading.ofSemanticCore_valid
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    IsGeometricLawReading raw X
      (GeometricLawReading.ofSemanticCore raw X G B)

@[simp] theorem GeometricLawReading.ofSemanticCore_holdsOn
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (i : S.lawUniverse.Index) :
    (GeometricLawReading.ofSemanticCore raw X G B).HoldsOn s i ↔
      ∀ a, s.appTop (semanticCoreGlobalEquation raw X G B i a) = 0

/-- presentation-stable bridgeはcore witness restrictionをcanonical section restrictionへ送る。 -/
theorem semanticCoreWitness_restrict
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    {source target : S.category} (f : source ⟶ target)
    (i : S.lawUniverse.Index) (a : U.Atom) :
    B.toSheafifiedSection source (G.violationWitness source i a) =
      sheafifiedRestriction raw f
        (B.toSheafifiedSection target (G.violationWitness target i a))

/-- core witness idealのbridge像は、移されたatom-indexed coordinatesのspanと一致する。 -/
theorem semanticCoreLawWitnessIdeal_map
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (W : S.category) (i : S.lawUniverse.Index) :
    Ideal.map (B.toSheafifiedSection W) (G.lawWitnessIdeal W i) =
      Ideal.span (Set.range (fun a =>
        B.toSheafifiedSection W (G.violationWitness W i a)))

/-- valid bridgeはcore witness idealをmap/comapで忠実に反映する。 -/
theorem semanticCoreLawWitnessIdeal_comap_map
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    (W : S.category) (i : S.lawUniverse.Index) :
    Ideal.comap (B.toSheafifiedSection W)
        (Ideal.map (B.toSheafifiedSection W) (G.lawWitnessIdeal W i)) =
      G.lawWitnessIdeal W i

/-- actual atlas chartで、global equationのpullbackはcoreのlocal witnessに戻る。 -/
theorem semanticCoreGlobalEquation_on_chart
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    (j : X.atlas.Index) (i : S.lawUniverse.Index) (a : U.Atom) :
    ((X.atlas.chart j).map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw (X.atlas.chart j).context)).hom)
        (semanticCoreGlobalEquation raw X G B i a) =
      B.toSheafifiedSection (X.atlas.chart j).context
        (G.violationWitness (X.atlas.chart j).context i a)

/-- existing coreからglobal-section constructorを経由するcanonical witness。 -/
noncomputable def ClosedEquationalLawWitness.ofSemanticCore
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (i : S.lawUniverse.Index) : ClosedEquationalLawWitness raw X i :=
  ClosedEquationalLawWitness.ofGlobalSections raw X i
    (semanticCoreGlobalEquation raw X G B i)

theorem ClosedEquationalLawWitness.ofSemanticCore_valid
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (i : S.lawUniverse.Index) :
    IsClosedEquationalLawWitness raw X
      (ClosedEquationalLawWitness.ofSemanticCore raw X G B i)
```

`IsClosedEquationalLawWitness`はcoordinate-level restriction equalityであり、
任意のideal familyのcompatibility proofではない。`localLawWitnessIdeal_map_basicOpen`は
`Ideal.map_span`と同じatom indexから導く。新主経路は`ofSemanticCore`を使い、
`semanticCoreWitness_restrict`がexisting core、raw restriction、canonical sheafificationの
provenanceを固定する。`ofGlobalSections`だけから作るreadingは補助constructorであり、
既存core接続の完了証拠には数えない。

### SD1 — closed-equationality、context selection、validity、required/allの分離

```lean
/-- semantic reading、closed-equationality、context selection、law witnessesを束ねるdata。 -/
structure ClosedEquationalLawReading where
  geometric : GeometricLawReading raw X
  closed : Set S.lawUniverse.Index
  selected : X.underlying.affineOpens → Set S.lawUniverse.Index
  witness : ∀ i, closed i → ClosedEquationalLawWitness raw X i

@[ext] theorem ClosedEquationalLawReading.ext
    (R Q : ClosedEquationalLawReading raw X)
    (hgeometric : R.geometric = Q.geometric)
    (hclosed : R.closed = Q.closed)
    (hselected : R.selected = Q.selected)
    (hwitness : HEq R.witness Q.witness) : R = Q

/-- ideal-sheaf constructionに必要なwitness compatibilityだけを表すpredicate。 -/
def IsClosedEquationalWitnessReading
    (R : ClosedEquationalLawReading raw X) : Prop :=
  ∀ i (hi : R.closed i),
    IsClosedEquationalLawWitness raw X (R.witness i hi)

/-- semantic base-change stabilityも含むfull recognition predicate。 -/
structure IsClosedEquationalLawReading
    (R : ClosedEquationalLawReading raw X) : Prop where
  geometric_stable : IsGeometricLawReading raw X R.geometric
  witness_compatible : IsClosedEquationalWitnessReading raw X R
  selected_closed :
    ∀ V i, R.selected V i → R.closed i
  selected_basicOpen :
    ∀ (V : X.underlying.affineOpens)
      (f : Γ(X.underlying, V)) (i : S.lawUniverse.Index),
      R.selected V i ↔
        R.selected (X.underlying.affineBasicOpen f) i

/-- required lawのclosed-equationalityと全affine contextでのselection。 -/
structure RequiredClosed (R : ClosedEquationalLawReading raw X) : Prop where
  closed : ∀ i, S.lawUniverse.Required i → R.closed i
  selected :
    ∀ V i, S.lawUniverse.Required i → R.selected V i

/-- required lawsだけを読むsection-level semantic lawfulness。 -/
def SemanticLawfulAlong
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  ∀ i, S.lawUniverse.Required i → R.geometric.HoldsOn s i

/-- law universeの全indexを読む本文どおりのfull semantic lawfulness。 -/
def FullySemanticLawfulAlong
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  ∀ i, R.geometric.HoldsOn s i

/-- full theoremで要求する、全lawのclosed-equationalityと全affine contextでのselection。 -/
structure AllLawsSelected
    (R : ClosedEquationalLawReading raw X) : Prop where
  closed : ∀ i, R.closed i
  selected : ∀ V i, R.selected V i

/-- existing coreとscheme bridgeから作る新主経路のreading。 -/
noncomputable def ClosedEquationalLawReading.ofSemanticCore
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    ClosedEquationalLawReading raw X where
  geometric := GeometricLawReading.ofSemanticCore raw X G B
  closed := Set.univ
  selected := fun _ => Set.univ
  witness i _ := ClosedEquationalLawWitness.ofSemanticCore raw X G B i

@[simp] theorem ClosedEquationalLawReading.ofSemanticCore_witness
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (i : S.lawUniverse.Index)
    (hi : (ClosedEquationalLawReading.ofSemanticCore raw X G B).closed i) :
    (ClosedEquationalLawReading.ofSemanticCore raw X G B).witness i hi =
      ClosedEquationalLawWitness.ofSemanticCore raw X G B i

theorem ClosedEquationalLawReading.ofSemanticCore_witnessCompatible
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    IsClosedEquationalWitnessReading raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B)

theorem ClosedEquationalLawReading.ofSemanticCore_valid
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    IsClosedEquationalLawReading raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B)

theorem ClosedEquationalLawReading.ofSemanticCore_requiredClosed
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    RequiredClosed raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B)

theorem ClosedEquationalLawReading.ofSemanticCore_selected
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (V : X.underlying.affineOpens) (i : S.lawUniverse.Index) :
    (ClosedEquationalLawReading.ofSemanticCore raw X G B).selected V i

theorem ClosedEquationalLawReading.ofSemanticCore_allLawsSelected
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    AllLawsSelected raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B)
```

`RequiredClosed R`は`R.closed = Set.univ`を要求しない。`R.closed i`はlaw `i`がclosed-equational
witnessを持つこと、`R.selected V i`は本文の「law `i` is selected on `V`」を表す。
`selected_closed`はselectionからclosed-equationalityを回収し、`RequiredClosed.selected`はrequired lawが
全affine contextのobstruction idealに現れることを保証する。`selected_basicOpen`はselectionの
exact restriction compatibilityであり、SD2のobjectwise supremumの`map_ideal_basicOpen`でproof-useする。
selectionがrestrictionで増減する一般形は本PRDの一般sheaf-image対象へは数えない。

本文のfull semantic theoremには`AllLawsSelected R`を明示し、context-selected aggregate idealに対する
factorization APIと区別する。`ofSemanticCore`はglobal-equation constructorとして全indexをclosedかつselectedにし、
existing-core経路はvalid bridge、canonical `ofSemanticCore_requiredClosed`、
`SemanticCoreIdealSheafRealized`を必須とする。required/allの差はlaw universeのroleで決まり、SD9の
2-law fixtureでrequired indexがselected index全体の真部分であることを固定する。

### SD2 — actual IdealSheafDataとrequired/all obstruction ideals

```lean
/-- local witness idealsから直接作るactual Mathlib ideal sheaf。 -/
noncomputable def lawWitnessIdealSheaf
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i) :
    X.underlying.IdealSheafData where
  ideal := localLawWitnessIdeal raw X (R.witness i hi)
  map_ideal_basicOpen :=
    localLawWitnessIdeal_map_basicOpen raw X (R.witness i hi)
      (hR i hi)

@[simp] theorem lawWitnessIdealSheaf_ideal
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i)
    (V : X.underlying.affineOpens) :
    (lawWitnessIdealSheaf raw X R hR i hi).ideal V =
      localLawWitnessIdeal raw X (R.witness i hi) V

/-- global equation constructorはMathlib `ofIdealTop`と一致する。 -/
theorem lawWitnessIdealSheaf_ofGlobalSections
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i)
    (equation : U.Atom → Γ(X.underlying, ⊤))
    (hw : R.witness i hi =
      ClosedEquationalLawWitness.ofGlobalSections raw X i equation) :
    lawWitnessIdealSheaf raw X R hR i hi =
      Scheme.IdealSheafData.ofIdealTop (X := X.underlying)
        (Ideal.span (Set.range equation))

/-- existing core由来のideal sheafを各atlas chartへ引き戻したときの実現条件。 -/
def SemanticCoreIdealSheafRealized
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) : Prop :=
  (∀ W : S.category,
    AffineChart.AffineAATChart.SheafifiedChartPresentation raw W) ∧
  ∀ (j : X.atlas.Index) (i : S.lawUniverse.Index),
    let R := ClosedEquationalLawReading.ofSemanticCore raw X G B
    let hR := ClosedEquationalLawReading.ofSemanticCore_witnessCompatible raw X G B
    ((lawWitnessIdealSheaf raw X R hR i (Set.mem_univ i)).comap
        (X.atlas.chart j).map) =
      Scheme.IdealSheafData.ofIdealTop
        (X := (X.atlas.chart j).domain)
        (Ideal.map
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing raw (X.atlas.chart j).context)).inv.hom
          (Ideal.map
            (B.toSheafifiedSection (X.atlas.chart j).context)
            (G.lawWitnessIdeal (X.atlas.chart j).context i)))

/-- valid bridgeはpresentation provenanceと全atlas-chart pullback equalityを同時に実現する。 -/
theorem semanticCoreIdealSheaf_realized
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B) :
    SemanticCoreIdealSheafRealized raw X G B

/-- required selected supremumはbasic open restrictionとexactに可換である。 -/
theorem requiredLocalLawIdeal_map_basicOpen
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) (f : Γ(X.underlying, V)) :
    Ideal.map
        (X.underlying.presheaf.map
          (homOfLE (X.underlying.basicOpen_le f)).op).hom
        (⨆ i : {i : S.lawUniverse.Index //
            S.lawUniverse.Required i ∧ R.selected V i},
          localLawWitnessIdeal raw X
            (R.witness i.1 (hclosed.closed i.1 i.2.1)) V) =
      ⨆ i : {i : S.lawUniverse.Index //
          S.lawUniverse.Required i ∧
            R.selected (X.underlying.affineBasicOpen f) i},
        localLawWitnessIdeal raw X
            (R.witness i.1 (hclosed.closed i.1 i.2.1))
            (X.underlying.affineBasicOpen f)

/-- all selected supremumはbasic open restrictionとexactに可換である。 -/
theorem allSelectedLocalLawIdeal_map_basicOpen
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (V : X.underlying.affineOpens) (f : Γ(X.underlying, V)) :
    Ideal.map
        (X.underlying.presheaf.map
          (homOfLE (X.underlying.basicOpen_le f)).op).hom
        (⨆ i : {i : S.lawUniverse.Index // R.selected V i},
          localLawWitnessIdeal raw X
            (R.witness i.1 (hR.selected_closed V i.1 i.2)) V) =
      ⨆ i : {i : S.lawUniverse.Index //
          R.selected (X.underlying.affineBasicOpen f) i},
          localLawWitnessIdeal raw X
            (R.witness i.1
              (hR.selected_closed
                (X.underlying.affineBasicOpen f) i.1 i.2))
            (X.underlying.affineBasicOpen f)

/-- `I_Ob^U(V)`: `V`でselectedなrequired closed-equational law idealsのsupremum。 -/
noncomputable def lawGeneratedIdealSheaf
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    X.underlying.IdealSheafData where
  ideal V :=
    ⨆ i : {i : S.lawUniverse.Index //
        S.lawUniverse.Required i ∧ R.selected V i},
      localLawWitnessIdeal raw X
        (R.witness i.1 (hclosed.closed i.1 i.2.1)) V
  map_ideal_basicOpen := requiredLocalLawIdeal_map_basicOpen raw X R hR hclosed

/-- `I_Ob^{U,all}(V)`: `V`でselectedなclosed-equational law idealsのsupremum。 -/
noncomputable def allLawGeneratedIdealSheaf
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) :
    X.underlying.IdealSheafData where
  ideal V :=
    ⨆ i : {i : S.lawUniverse.Index // R.selected V i},
      localLawWitnessIdeal raw X
        (R.witness i.1 (hR.selected_closed V i.1 i.2)) V
  map_ideal_basicOpen := allSelectedLocalLawIdeal_map_basicOpen raw X R hR

@[simp] theorem lawGeneratedIdealSheaf_ideal
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) :
    (lawGeneratedIdealSheaf raw X R hR hclosed).ideal V =
      ⨆ i : {i : S.lawUniverse.Index //
          S.lawUniverse.Required i ∧ R.selected V i},
        localLawWitnessIdeal raw X
          (R.witness i.1 (hclosed.closed i.1 i.2.1)) V

@[simp] theorem allLawGeneratedIdealSheaf_ideal
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (V : X.underlying.affineOpens) :
    (allLawGeneratedIdealSheaf raw X R hR).ideal V =
      ⨆ i : {i : S.lawUniverse.Index // R.selected V i},
        localLawWitnessIdeal raw X
          (R.witness i.1 (hR.selected_closed V i.1 i.2)) V

theorem lawGeneratedIdealSheaf_le_all
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    lawGeneratedIdealSheaf raw X R hR hclosed ≤
      allLawGeneratedIdealSheaf raw X R hR
```

一般constructorは`IdealSheafData`を各affine openのselected indexed supremumと
`map_ideal_basicOpen`から直接構成する。required側の`hclosed.selected`とall側の
`hR.selected_closed`、両方の`hR.selected_basicOpen`をproof-useする。
`IdealSheafData.ofIdeals`は任意family以下の最大ideal sheafを返すため、
objectwise equalityが別途証明されない限り主経路に使わない。

### SD3 — actual closed geometry、quotient cover、pulled decoration

```lean
noncomputable def lawfulClosedSubscheme
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) : AlgebraicGeometry.Scheme :=
  (lawGeneratedIdealSheaf raw X R hR hclosed).subscheme

noncomputable def lawfulClosedImmersion
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    lawfulClosedSubscheme raw X R hR hclosed ⟶ X.underlying :=
  (lawGeneratedIdealSheaf raw X R hR hclosed).subschemeι

noncomputable def allLawfulClosedSubscheme
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) : AlgebraicGeometry.Scheme :=
  (allLawGeneratedIdealSheaf raw X R hR).subscheme

noncomputable def allLawfulClosedImmersion
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) :
    allLawfulClosedSubscheme raw X R hR ⟶ X.underlying :=
  (allLawGeneratedIdealSheaf raw X R hR).subschemeι

theorem lawfulClosedImmersion_isClosedImmersion
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    IsClosedImmersion (lawfulClosedImmersion raw X R hR hclosed)

@[simp] theorem lawfulClosedImmersion_ker
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedImmersion raw X R hR hclosed).ker =
      lawGeneratedIdealSheaf raw X R hR hclosed

@[simp] theorem lawfulClosedImmersion_range
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    Set.range (lawfulClosedImmersion raw X R hR hclosed) =
      (lawGeneratedIdealSheaf raw X R hR hclosed).support

noncomputable def lawfulClosedSubschemeCover
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedSubscheme raw X R hR hclosed).AffineOpenCover :=
  (lawGeneratedIdealSheaf raw X R hR hclosed).subschemeCover

@[simp] theorem lawfulClosedSubschemeCover_X
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) :
    (lawfulClosedSubschemeCover raw X R hR hclosed).X V =
      CommRingCat.of
        (Γ(X.underlying, V) ⧸
          (lawGeneratedIdealSheaf raw X R hR hclosed).ideal V)

noncomputable def lawfulClosedSubschemeObjIso
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) :
    Γ(lawfulClosedSubscheme raw X R hR hclosed,
        lawfulClosedImmersion raw X R hR hclosed ⁻¹ᵁ V) ≅
      CommRingCat.of
        (Γ(X.underlying, V) ⧸
          (lawGeneratedIdealSheaf raw X R hR hclosed).ideal V) :=
  (lawGeneratedIdealSheaf raw X R hR hclosed).subschemeObjIso V

noncomputable def lawfulClosedDecoration
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    AATReadingDecoration raw (lawfulClosedSubscheme raw X R hR hclosed) :=
  AATReadingDecoration.pullback raw
    (lawfulClosedImmersion raw X R hR hclosed) X.decoration

@[simp] theorem lawfulClosedDecoration_context
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedDecoration raw X R hR hclosed).context = X.decoration.context

@[simp] theorem lawfulClosedDecoration_lawUniverse
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedDecoration raw X R hR hclosed).lawUniverse raw =
      X.decoration.lawUniverse raw

@[simp] theorem lawfulClosedDecoration_signature
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedDecoration raw X R hR hclosed).signature raw =
      X.decoration.signature raw

@[simp] theorem lawfulClosedDecoration_coordinateSection
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (c : (X.decoration.coordinateFamily raw).CoordX) :
    (lawfulClosedDecoration raw X R hR hclosed).coordinateSection raw c =
      (lawfulClosedImmersion raw X R hR hclosed).appTop
        (X.decoration.coordinateSection raw c)

noncomputable def fullToRequiredLawfulMap
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    allLawfulClosedSubscheme raw X R hR ⟶
      lawfulClosedSubscheme raw X R hR hclosed :=
  Scheme.IdealSheafData.inclusion
    (lawGeneratedIdealSheaf_le_all raw X R hR hclosed)

theorem fullToRequiredLawfulMap_isClosedImmersion
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    IsClosedImmersion (fullToRequiredLawfulMap raw X R hR hclosed)

@[reassoc] theorem fullToRequiredLawfulMap_immersion
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    fullToRequiredLawfulMap raw X R hR hclosed ≫
        lawfulClosedImmersion raw X R hR hclosed =
      allLawfulClosedImmersion raw X R hR
```

一般の`X.underlying`を単一の`Spec A`と仮定しない。
affine open `V`ごとのquotient chartはMathlibの`subschemeCover`と`subschemeObjIso`で与える。
global equation constructorをaffine Schemeへ適用した場合に限り、`ofIdealTop`と
`equivOfIsAffine`を通して単一quotient spectrumの追加定理を証明してよい。

### SD4 — law-by-law exactness、ideal lawfulness、actual factorization

```lean
/-- 一つのclosed lawについてsemantic truthがideal vanishingを含意する。 -/
def LawIdealSound
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i) : Prop :=
  ∀ {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying),
    R.geometric.HoldsOn s i →
      (lawWitnessIdealSheaf raw X R hR i hi).comap s = ⊥

/-- 一つのclosed lawについてideal vanishingがsemantic truthを含意する。 -/
def LawIdealComplete
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i) : Prop :=
  ∀ {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying),
    (lawWitnessIdealSheaf raw X R hR i hi).comap s = ⊥ →
      R.geometric.HoldsOn s i

/-- 数学本文のlaw-by-law `LawIdealExact_U(i)`。 -/
def LawIdealExact
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i) : Prop :=
  ∀ {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying),
    R.geometric.HoldsOn s i ↔
      (lawWitnessIdealSheaf raw X R hR i hi).comap s = ⊥

theorem lawIdealExact_iff_sound_and_complete
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i) :
    LawIdealExact raw X R hR i hi ↔
      LawIdealSound raw X R hR i hi ∧
        LawIdealComplete raw X R hR i hi

def RequiredLawIdealExact
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) : Prop :=
  ∀ i (hi : S.lawUniverse.Required i),
    LawIdealExact raw X R hR.witness_compatible i (hclosed.closed i hi)

def AllLawIdealExact
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hall : AllLawsSelected raw X R) : Prop :=
  ∀ i, LawIdealExact raw X R hR.witness_compatible i
    (hall.closed i)

def WitnessVanishes
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  ∀ i (hi : S.lawUniverse.Required i),
    (lawWitnessIdealSheaf raw X R hR.witness_compatible i
      (hclosed.closed i hi)).comap s = ⊥

def IdealLawfulAlong
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  (lawGeneratedIdealSheaf raw X R hR hclosed).comap s = ⊥

def FullIdealLawfulAlong
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  (allLawGeneratedIdealSheaf raw X R hR).comap s = ⊥

def FactorsThroughLawfulClosedSubscheme
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :=
  {t : T ⟶ lawfulClosedSubscheme raw X R hR hclosed //
    t ≫ lawfulClosedImmersion raw X R hR hclosed = s}

def FactorsThroughAllLawfulClosedSubscheme
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :=
  {t : T ⟶ allLawfulClosedSubscheme raw X R hR //
    t ≫ allLawfulClosedImmersion raw X R hR = s}

theorem idealLawfulAlong_iff_le_ker
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    IdealLawfulAlong raw X R hR hclosed s ↔
      lawGeneratedIdealSheaf raw X R hR hclosed ≤ s.ker

noncomputable def factorizationLift
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : IdealLawfulAlong raw X R hR hclosed s) :
    T ⟶ lawfulClosedSubscheme raw X R hR hclosed

@[reassoc] theorem factorizationLift_fac
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : IdealLawfulAlong raw X R hR hclosed s) :
    factorizationLift raw X R hR hclosed s hs ≫
        lawfulClosedImmersion raw X R hR hclosed = s

theorem factorization_unique
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (a b : FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s) :
    a.1 = b.1

theorem idealLawfulAlong_iff_nonempty_factorsThrough
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    IdealLawfulAlong raw X R hR hclosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s)

noncomputable def allLawFactorizationLift
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : FullIdealLawfulAlong raw X R hR s) :
    T ⟶ allLawfulClosedSubscheme raw X R hR

@[reassoc] theorem allLawFactorizationLift_fac
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : FullIdealLawfulAlong raw X R hR s) :
    allLawFactorizationLift raw X R hR s hs ≫
        allLawfulClosedImmersion raw X R hR = s

theorem allLawFactorization_unique
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (a b : FactorsThroughAllLawfulClosedSubscheme raw X R hR s) :
    a.1 = b.1

theorem fullIdealLawfulAlong_iff_nonempty_factorsThrough
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    FullIdealLawfulAlong raw X R hR s ↔
      Nonempty (FactorsThroughAllLawfulClosedSubscheme raw X R hR s)
```

`idealLawfulAlong_iff_le_ker`は`IdealSheafData.map_gc`と`map_bot`から導き、
liftは`IsClosedImmersion.lift`、triangleは`lift_fac`、一意性はclosed immersionの`Mono`から導く。
factorization proof、triangle、一意性をfieldとして外部入力しない。

### SD5 — 定理11.1のrequired coreとfull all-law版

```lean
theorem semanticLawfulAlong_iff_witnessVanishes
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (hexact : RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    SemanticLawfulAlong raw X R s ↔
      WitnessVanishes raw X R hR hclosed s

theorem witnessVanishes_iff_idealLawfulAlong
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    WitnessVanishes raw X R hR hclosed s ↔
      IdealLawfulAlong raw X R hR hclosed s

/-- 定理11.1のrequired closed-equational core。 -/
theorem lawfulnessIdealFactorizationCorrespondence
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (hexact : RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    (SemanticLawfulAlong raw X R s ↔
      WitnessVanishes raw X R hR hclosed s) ∧
    (WitnessVanishes raw X R hR hclosed s ↔
      IdealLawfulAlong raw X R hR hclosed s) ∧
    (IdealLawfulAlong raw X R hR hclosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s))

/-- existing coreからactual ideal sheafを経由する定理11.1の完了経路。 -/
theorem semanticCoreLawfulnessIdealFactorizationCorrespondence
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    (hexact : RequiredLawIdealExact raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B))
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    let R := ClosedEquationalLawReading.ofSemanticCore raw X G B
    let hR := ClosedEquationalLawReading.ofSemanticCore_valid raw X G B
    let hclosed := ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B
    SemanticCoreIdealSheafRealized raw X G B ∧
    (SemanticLawfulAlong raw X R s ↔
      WitnessVanishes raw X R hR hclosed s) ∧
    (WitnessVanishes raw X R hR hclosed s ↔
      IdealLawfulAlong raw X R hR hclosed s) ∧
    (IdealLawfulAlong raw X R hR hclosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s))

theorem fullySemanticLawfulAlong_iff_fullIdealLawfulAlong
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hall : AllLawsSelected raw X R)
    (hexact : AllLawIdealExact raw X R hR hall)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    FullySemanticLawfulAlong raw X R s ↔
      FullIdealLawfulAlong raw X R hR s

theorem fullLawfulnessIdealFactorizationCorrespondence
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hall : AllLawsSelected raw X R)
    (hexact : AllLawIdealExact raw X R hR hall)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    (FullySemanticLawfulAlong raw X R s ↔
      FullIdealLawfulAlong raw X R hR s) ∧
    (FullIdealLawfulAlong raw X R hR s ↔
      Nonempty (FactorsThroughAllLawfulClosedSubscheme raw X R hR s))
```

ambient inputとideal-sheaf construction validityを除き、generic core theoremが新たに要求する
theorem-specific semantic premisesは`RequiredClosed`とlaw-by-law`RequiredLawIdealExact`である。
existing-core版は`RequiredClosed`を引数へ戻さず、`ofSemanticCore_requiredClosed`を内部使用する。
`IsClosedEquationalLawReading`はwitness compatibilityに加えてcontext selectionのclosed性と
basic-open不変性を担い、`RequiredClosed.selected`はrequired selectionを担う。両方を
objectwise selected supremumの構成にproof-useする。
required indexed supremumとのextension-ideal compatibilityは`IdealSheafData.map_gc`が与える
supremum preservationから証明し、追加入力にしない。factorization criterionもSD4から証明する。

cover上のlocal vanishingからglobal vanishingを計算する定理は本PRDに含めない。
その定理を後続で追加する場合にのみ、`U`-adequate cover、witness coverage、
ideal-sheaf descentを具体的なcover dataへ型付けして固定する。

### SD6 — architecture object、valuation、signature axisへの別定理

object-level law、valuation、signature axisはcore theoremへ混ぜない。
section-level readingとのcomparisonとPart Iのexactnessを明示した別定理として接続する。

```lean
def RequiredObjectPointComparison
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) : Prop :=
  ∀ i, S.lawUniverse.Required i →
    (R.geometric.HoldsOn s i ↔ (S.lawUniverse.law i).holds Obj)

theorem semanticLawfulAlong_iff_lawfulness
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U)
    (hpoint : RequiredObjectPointComparison raw X R s Obj) :
    SemanticLawfulAlong raw X R s ↔ Lawfulness Obj S.lawUniverse

theorem semanticLawfulAlong_iff_omegaU_zero
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U)
    {Value : Type u}
    (valuation : ObstructionValuation U Value)
    (aggregation : ZeroReflectingAggregation Value valuation.domain
      S.lawUniverse.RequiredIndex)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (hsound : ∀ i : S.lawUniverse.RequiredIndex,
      ObstructionSound valuation (S.lawUniverse.law i.1))
    (hcomplete : ∀ i : S.lawUniverse.RequiredIndex,
      ObstructionComplete valuation (S.lawUniverse.law i.1)) :
    SemanticLawfulAlong raw X R s ↔
      omegaU valuation S.lawUniverse aggregation Obj = valuation.domain.zero

theorem semanticLawfulAlong_iff_requiredSignatureAxesZero
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) (Sig : SignatureAxes U)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (haxis : Lawfulness Obj S.lawUniverse ↔
      RequiredSignatureAxesZero Obj Sig) :
    SemanticLawfulAlong raw X R s ↔ RequiredSignatureAxesZero Obj Sig

theorem factorsThroughLawfulClosedSubscheme_iff_omegaU_zero
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (hexact : RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U)
    {Value : Type u}
    (valuation : ObstructionValuation U Value)
    (aggregation : ZeroReflectingAggregation Value valuation.domain
      S.lawUniverse.RequiredIndex)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (hsound : ∀ i : S.lawUniverse.RequiredIndex,
      ObstructionSound valuation (S.lawUniverse.law i.1))
    (hcomplete : ∀ i : S.lawUniverse.RequiredIndex,
      ObstructionComplete valuation (S.lawUniverse.law i.1)) :
    Nonempty (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s) ↔
      omegaU valuation S.lawUniverse aggregation Obj = valuation.domain.zero

theorem factorsThroughLawfulClosedSubscheme_iff_requiredSignatureAxesZero
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (hexact : RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) (Sig : SignatureAxes U)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (haxis : Lawfulness Obj S.lawUniverse ↔
      RequiredSignatureAxesZero Obj Sig) :
    Nonempty (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s) ↔
      RequiredSignatureAxesZero Obj Sig
```

`RequiredObjectPointComparison`、obstruction soundness/completeness、axis exactnessは
それぞれ独立したmaterial premiseである。`LawIdealExact`から自動生成しない。

### SD7 — law inclusionとcontravariant closed geometry

inclusion dataはlaw index mapとatom witness mapだけを持つ。
required/closed/context selection preservation、coordinate equality、semantic implicationは
別のvalidity predicateで証明する。

```lean
structure ClosedEquationalLawInclusion
    (R Q : ClosedEquationalLawReading raw X) where
  lawMap : S.lawUniverse.Index → S.lawUniverse.Index
  atomMap : ∀ i : S.lawUniverse.Index, U.Atom → U.Atom

@[ext] theorem ClosedEquationalLawInclusion.ext
    {R Q : ClosedEquationalLawReading raw X}
    (e f : ClosedEquationalLawInclusion raw X R Q)
    (hlawMap : e.lawMap = f.lawMap)
    (hatomMap : e.atomMap = f.atomMap) : e = f

structure IsClosedEquationalLawInclusion
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q) : Prop where
  required_map : ∀ i, S.lawUniverse.Required i →
    S.lawUniverse.Required (e.lawMap i)
  closed_map : ∀ i, R.closed i → Q.closed (e.lawMap i)
  selected_map :
    ∀ V i, R.selected V i → Q.selected V (e.lawMap i)
  coordinate_eq :
    ∀ i (hi : R.closed i) (V : X.underlying.affineOpens) (a : U.Atom),
      (R.witness i hi).coordinate V a =
        (Q.witness (e.lawMap i) (closed_map i hi)).coordinate V (e.atomMap i a)
  semantic_monotone :
    ∀ {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) i,
      Q.geometric.HoldsOn s (e.lawMap i) → R.geometric.HoldsOn s i

def ClosedEquationalLawInclusion.refl
    (R : ClosedEquationalLawReading raw X) :
    ClosedEquationalLawInclusion raw X R R

theorem ClosedEquationalLawInclusion.refl_valid
    (R : ClosedEquationalLawReading raw X) :
    IsClosedEquationalLawInclusion raw X
      (ClosedEquationalLawInclusion.refl raw X R)

def ClosedEquationalLawInclusion.comp
    {R Q P : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (f : ClosedEquationalLawInclusion raw X Q P) :
    ClosedEquationalLawInclusion raw X R P

theorem ClosedEquationalLawInclusion.comp_valid
    {R Q P : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (f : ClosedEquationalLawInclusion raw X Q P)
    (he : IsClosedEquationalLawInclusion raw X e)
    (hf : IsClosedEquationalLawInclusion raw X f) :
    IsClosedEquationalLawInclusion raw X (e.comp raw X f)

theorem lawWitnessIdealSheaf_le
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e)
    (i : S.lawUniverse.Index) (hi : R.closed i) :
    lawWitnessIdealSheaf raw X R hR.witness_compatible i hi ≤
      lawWitnessIdealSheaf raw X Q hQ.witness_compatible
        (e.lawMap i) (he.closed_map i hi)

theorem lawGeneratedIdealSheaf_mono
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    lawGeneratedIdealSheaf raw X R hR hRclosed ≤
      lawGeneratedIdealSheaf raw X Q hQ hQclosed

theorem allLawGeneratedIdealSheaf_mono
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    allLawGeneratedIdealSheaf raw X R hR ≤
      allLawGeneratedIdealSheaf raw X Q hQ

theorem semanticLawfulAlong_mono
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    SemanticLawfulAlong raw X Q s → SemanticLawfulAlong raw X R s

theorem fullySemanticLawfulAlong_mono
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    FullySemanticLawfulAlong raw X Q s →
      FullySemanticLawfulAlong raw X R s

noncomputable def lawfulClosedSubschemeMap
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    lawfulClosedSubscheme raw X Q hQ hQclosed ⟶
      lawfulClosedSubscheme raw X R hR hRclosed :=
  Scheme.IdealSheafData.inclusion
    (lawGeneratedIdealSheaf_mono raw X hR hQ hRclosed hQclosed e he)

theorem lawfulClosedSubschemeMap_isClosedImmersion
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    IsClosedImmersion
      (lawfulClosedSubschemeMap raw X hR hQ hRclosed hQclosed e he)

@[reassoc] theorem lawfulClosedSubschemeMap_immersion
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    lawfulClosedSubschemeMap raw X hR hQ hRclosed hQclosed e he ≫
        lawfulClosedImmersion raw X R hR hRclosed =
      lawfulClosedImmersion raw X Q hQ hQclosed

@[simp] theorem lawfulClosedSubschemeMap_id
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    lawfulClosedSubschemeMap raw X hR hR hclosed hclosed
        (ClosedEquationalLawInclusion.refl raw X R)
        (ClosedEquationalLawInclusion.refl_valid raw X R) = 𝟙 _

@[reassoc] theorem lawfulClosedSubschemeMap_comp
    {R Q P : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hP : IsClosedEquationalLawReading raw X P)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (hPclosed : RequiredClosed raw X P)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (f : ClosedEquationalLawInclusion raw X Q P)
    (he : IsClosedEquationalLawInclusion raw X e)
    (hf : IsClosedEquationalLawInclusion raw X f) :
    lawfulClosedSubschemeMap raw X hQ hP hQclosed hPclosed f hf ≫
        lawfulClosedSubschemeMap raw X hR hQ hRclosed hQclosed e he =
      lawfulClosedSubschemeMap raw X hR hP hRclosed hPclosed
        (e.comp raw X f) (ClosedEquationalLawInclusion.comp_valid raw X e f he hf)

noncomputable def allLawfulClosedSubschemeMap
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    allLawfulClosedSubscheme raw X Q hQ ⟶
      allLawfulClosedSubscheme raw X R hR :=
  Scheme.IdealSheafData.inclusion
    (allLawGeneratedIdealSheaf_mono raw X hR hQ e he)

theorem allLawfulClosedSubschemeMap_isClosedImmersion
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    IsClosedImmersion (allLawfulClosedSubschemeMap raw X hR hQ e he)

@[reassoc] theorem allLawfulClosedSubschemeMap_immersion
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    allLawfulClosedSubschemeMap raw X hR hQ e he ≫
        allLawfulClosedImmersion raw X R hR =
      allLawfulClosedImmersion raw X Q hQ

@[simp] theorem allLawfulClosedSubschemeMap_id
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) :
    allLawfulClosedSubschemeMap raw X hR hR
        (ClosedEquationalLawInclusion.refl raw X R)
        (ClosedEquationalLawInclusion.refl_valid raw X R) = 𝟙 _

@[reassoc] theorem allLawfulClosedSubschemeMap_comp
    {R Q P : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hP : IsClosedEquationalLawReading raw X P)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (f : ClosedEquationalLawInclusion raw X Q P)
    (he : IsClosedEquationalLawInclusion raw X e)
    (hf : IsClosedEquationalLawInclusion raw X f) :
    allLawfulClosedSubschemeMap raw X hQ hP f hf ≫
        allLawfulClosedSubschemeMap raw X hR hQ e he =
      allLawfulClosedSubschemeMap raw X hR hP
        (e.comp raw X f) (ClosedEquationalLawInclusion.comp_valid raw X e f he hf)
```

`Q`が`R`より強いlaw dataであるとき、idealは`I_R ≤ I_Q`、closed geometryは
`V(I_Q) ⟶ V(I_R)`の向きになる。`coordinate_eq`はvalidity proofとしてprimitive mapから証明し、
inclusion dataのfieldにderived ideal equalityを保存しない。

### SD8 — material premise分類

三分類は次で固定する。`本文由来`はgeneric APIで許可する数学的input、`放電済み`は既存APIまたは
primitive finite dataから内部導出する事実、`未放電`はfinal targetの引数、typeclass、field、certificateに
残してはならない項目である。API上の役割名をこの三分類の代用にしない。

| premise / data | 三分類 | generic APIでの役割 | completionでの放電方法 |
| --- | --- | --- | --- |
| `U : AtomCarrier` / `A : ArchitectureObject U` / `S : Site.AATSite A` | 本文由来 | 全targetのAtom carrier、architecture object、selected AAT site。 | merged dependencyの同一`U` / `A` / `S`を使い、別siteへのtransportをtarget内で追加しない。 |
| `k : Type v` / `[CommRing k]` | 本文由来 | 第III部のcoefficient ring。 | field、reduced、Noetherian等の追加typeclassを要求せず、finiteでは`k = Int`で放電する。 |
| `raw : RawAmbientRestrictionSystem S k` | 本文由来 | coordinate、structural relation、canonical sheafification input。 | merged `raw`のrestriction、structure sheaf、interpretation APIを使い、別のcoefficient systemを選択しない。 |
| `HasSheafify S.topology (AATCommAlgCat k)` | 本文由来 | ambient typeclass parameter。 | merged `raw`と同じsheafificationを使い、finiteでは名前付きinstance chainを記録する。新しい局所instanceを追加しない。 |
| `X : StandardArchitectureScheme raw` | 本文由来 | actual ambient Scheme、decoration、atlasのmerged input。 | merged `StandardArchitectureScheme` constructorを使い、finiteでは`twoChartReferenceModel`と、同じunderlying Schemeを2-law siteへretargetした`requiredAllReferenceModel`へ放電する。 |
| `{T : Scheme}` / `s : T ⟶ X.underlying` | 本文由来 | semantic predicate、ideal comap、factorizationを検査する任意test section。 | 主定理では全`T` / `s`を量化し、finite firingでは`integerPoint` / `modTwoPoint`を具体化する。 |
| `G : SemanticLawEquationWitnessIdealCore S` | 本文由来 | 定義11.3・定理11.4のmerged atom-indexed law-equation core。 | existing `violationWitness`、`lawWitnessIdeal`、restriction theoremを直接proof-useし、free witness idealを追加しない。 |
| `SemanticLawEquationSchemeBridge` / `IsSemanticLawEquationSchemeBridge` | 本文由来 | existing coreを同じraw quotient presentationとcanonical section ringへ移すdata / validity。 | `Observable W ≃+* raw.rawAlgebra W`をprimitive dataとし、bridge mapをそのequivalenceと`sheafificationUnitAlgHom`の合成で定義する。validityはrestriction naturalityと各`W`の`SheafifiedChartPresentation`を要求し、mapのbijectionを内部導出する。 |
| core witness idealのbridge像とspanの一致 | 放電済み | 新しい明示premiseを取らないderived theorem。A.8の完了証拠には単独で数えない。 | `SemanticLawEquationWitnessIdealCore.lawWitnessIdeal`、`Ideal.map_span`、`Set.range`の像計算から`semanticCoreLawWitnessIdeal_map`を証明する。valid bridgeではbijectionから`semanticCoreLawWitnessIdeal_comap_map`も証明し、generator collapseを拒否する。 |
| core idealのactual chart ideal-sheaf realization | 放電済み | valid bridgeから導くexisting-core completion property。 | `hB.presentation_stable`と`semanticCoreGlobalEquation_on_chart`、`lawWitnessIdealSheaf_ofGlobalSections`、`IdealSheafData.comap`、affine `ext_of_isAffine`から、canonical presentation provenanceとchart equalityのpairを証明する。 |
| `equation : U.Atom → Γ(X.underlying, ⊤)` | 本文由来 | global-equation constructorのselected equation family。 | new main routeでは`semanticCoreGlobalEquation G B i`から生成し、finiteでは`x - 1` / `x + 1`のformulaを証明する。任意idealに置き換えない。 |
| `GeometricLawReading.HoldsOn` | 本文由来 | section-level semantic predicateのprimitive data。 | concrete generator evaluationとして定義し、ideal vanishingの別名にしない。base change proofを別に構成する。 |
| `IsGeometricLawReading` | 本文由来 | semantic readingのrecognition premise。 | concrete readingのformulaからbase change保存を証明する。`HoldsOn := ideal vanishing`では放電しない。 |
| `ClosedEquationalLawWitness.coordinate` | 本文由来 | law / affine-open / atom indexed local equationのprimitive data。 | core global equationのrestrictionから生成し、local idealはcoordinate rangeのspanとして導出する。idealをfieldに持たない。 |
| `V : X.underlying.affineOpens` / `f : Γ(X.underlying, V)` / `a : U.Atom` | 本文由来 | local ideal、basic-open restriction、generator equalityを検査する量化data。 | `map_ideal_basicOpen`では全`V` / `f` / `a`を量化し、finite chart theoremで具体indexとcoordinateへ発火させる。 |
| `IsClosedEquationalLawWitness` | 本文由来 | closed equation witnessのrecognition premise。 | atom-indexed coordinate restriction equalityから証明する。global equation constructorではpresheaf functorialityから導く。 |
| `ClosedEquationalLawReading.geometric` / `closed` / `selected` / `witness` | 本文由来 | semantic reading、closed-equationality、affine contextごとのselection、各closed indexのwitnessというprimitive data。 | finiteではcore constructorから生成する。ideal、subscheme、lawfulness、factorizationをfieldに追加しない。 |
| `i : S.lawUniverse.Index` / `Required i` / `R.closed i` / `R.selected V i`のproof | 本文由来 | law role、witness typing、本文の`selected on V`に必要なmembership data。 | required proof、closed proof、context selection proofをnamed theoremから供給し、proof irrelevance以外の数学を隠さない。 |
| `IsClosedEquationalWitnessReading` | 本文由来 | ideal-sheaf constructorが受け取るrecognition premise。 | 各closed indexのwitness compatibilityをprimitive coordinatesから証明し、ideal、subscheme、factorization APIでproof-useする。 |
| `IsClosedEquationalLawReading` | 本文由来 | semantic APIとexact context selectionのrecognition premise。 | base-change stability、witness compatibility、`selected_closed`、`selected_basicOpen`を別々に証明する。restriction-broken selectionでnegative firingする。 |
| `RequiredClosed R` | 本文由来 | 定理11.1 required coreのmaterial premise。 | 各required indexのclosed proofと、全affine contextでのselected proofを与える。existing-core版では`ofSemanticCore_requiredClosed`で内部放電し引数へ戻さない。 |
| `LawIdealSound` / `LawIdealComplete` / `LawIdealExact` | 本文由来 | 定理11.1のlaw-by-law material premise。 | soundness / completenessの両方向をlawごと、全test Schemeと全sectionについてgenerator計算から証明する。 |
| `RequiredLawIdealExact` | 本文由来 | required core theoremのaggregate semantic premise。 | required indexごとの`LawIdealExact`から束ね、finiteでは`weakReading_requiredLawIdealExact` / `strongReading_requiredLawIdealExact`で放電する。 |
| `AllLawsSelected R` | 本文由来 | full theoremだけのmaterial premise。 | 全law indexのclosed proofと、全affine contextでのselected proofを与え、required coreには要求しない。 |
| `AllLawIdealExact` | 本文由来 | full theoremのaggregate material premise。 | `AllLawsSelected.closed`で全indexのlaw-by-law exactnessをfinite generator計算から証明する。context-selected aggregate ideal単独にはglobal semantic equivalenceを主張しない。 |
| context-selected indexed supremumとのextension-ideal compatibility | 放電済み | 新しい明示premiseを取らないderived theorem。 | `selected_basicOpen`、`localLawWitnessIdeal_map_basicOpen`、`IdealSheafData.map_gc`、complete latticeから導く。 |
| factorization through `V(I)` iff ideal comap is zero | 放電済み | 新しい明示premiseを取らないderived theorem。 | `map_gc`、`map_bot`、`ker_subschemeι`、`IsClosedImmersion.lift`、`lift_fac`、`Mono`から導く。 |
| `U`-adequate cover / witness coverage / ideal-sheaf descent | 未放電 | 本PRDのtarget signatureには置かない。 | cover上のlocal vanishingからglobal vanishingを計算する別statementでのみ具体化する。final ledgerに現れた場合はReject。 |
| `RequiredObjectPointComparison` | 本文由来 | SD6だけのmaterial premise。 | selected architecture pointとPart I lawの具体comparisonから証明する。 |
| `Obj : ArchitectureObject U` | 本文由来 | SD6 object comparisonのselected architecture point。 | finiteではcycle exampleの`acyclicObject`をpositive、`cyclicObject`をnegative firingに使う。 |
| `Value : Type u` / `valuation : ObstructionValuation U Value` / `ZeroReflectingAggregation` | 本文由来 | SD6 valuation theoremのprimitive value type / valuation / aggregation data。 | finiteでは`Nat`、`noCycleValuation`、`singletonRequiredAggregation`を使い、zero-reflectionを名前付きproofで放電する。 |
| obstruction soundness / completeness | 本文由来 | SD6だけのvaluation material premise。 | existing `ObstructionSound` / `ObstructionComplete`をlaw indexごとに具体valuationから証明する。 |
| `Sig : SignatureAxes U` | 本文由来 | SD6 axis theoremのselected signature data。 | finiteでは`CycleCorrespondenceExample.signatureAxes`を使い、axis equalityを具体計算する。 |
| axis exactness | 本文由来 | SD6だけのaxis material premise。 | `Lawfulness Obj LU ↔ RequiredSignatureAxesZero Obj Sig`の具体theoremを与える。 |
| `ClosedEquationalLawInclusion.lawMap` / `atomMap` | 本文由来 | law strengtheningのprimitive index / atom maps。 | finiteのweak-to-strong mapから具体化し、coordinate equalityやideal inclusionをfieldとして保存しない。 |
| `IsClosedEquationalLawInclusion` | 本文由来 | inclusion recognition premise。 | index map、atom map、context selection preservation、coordinate formula、semantic implicationから証明する。 |
| finite exampleのstrictness / nonemptiness / nonfactorization | 放電済み | generic APIへのpremiseとして追加しないfinite result。 | `x = 1`評価、`x = -1`評価、mod 2評価、quotient ring homで証明する。命題fieldとして入力しない。 |
| free `Prop` slot / conclusion-equivalent structure field / certificate field | 未放電 | generic APIにもcompletion theoremにも置かない。 | final declaration inventoryに一件でも現れた場合は`certificate escape`または`structure-field escape`としてRejectする。 |

実装完了時に、final snapshotの全target declarationについて明示引数、typeclass、structure field、
certificate fieldを独立に列挙し、この表の各行と突合する。各premiseについて「declaration」
「放電元」「proof bodyで使う箇所」「主結論への寄与」「finite firingまたはMathlib source」を
tracking Issueのfinal premise discharge packetへ記録する。完了条件は
`material_premise_ledger_delta = ∅`かつ`new_material_premise = ∅`である。

### SD9 — nondegenerate finite reference model

finite exampleは二つの相補的なfixtureを持つ。第一fixtureは既存の
`AAT.AG.LawAlgebra.FiniteExamples.StandardArchitectureScheme.twoChartReferenceModel`
上でglobal equations `x - 1`と`x + 1`からweak / strong readingsを構成し、reading間のstrictnessを示す。
第二fixtureは同じcontext geometry、raw relation `x^2 - 1`、underlying Schemeを保ちながら、
`base`をrequired、`strengthening`をoptionalとする2-law siteへretargetする。一つのreadingの中で
required ideal `(x - 1)`とall ideal `(x - 1, x + 1)`を比較し、required/all comparisonが
identityへ縮退しないことをactual factorizationで示す。

```lean
namespace AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry
open AAT.AG.FiniteModel
open AAT.AG.LawAlgebra.FiniteExamples.RingedSite.FiniteModel
open AAT.AG.LawAlgebra.FiniteExamples.StandardArchitectureScheme

noncomputable def weakLawEquationCore :
    SemanticLawEquationWitnessIdealCore
      AAT.AG.LawAlgebra.FiniteExamples.RingedSite.FiniteModel.site

noncomputable def strongLawEquationCore :
    SemanticLawEquationWitnessIdealCore
      AAT.AG.LawAlgebra.FiniteExamples.RingedSite.FiniteModel.site

noncomputable def weakSchemeBridge :
    SemanticLawEquationSchemeBridge rawSystem weakLawEquationCore

noncomputable def strongSchemeBridge :
    SemanticLawEquationSchemeBridge rawSystem strongLawEquationCore

theorem weakSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge rawSystem
      weakLawEquationCore weakSchemeBridge

theorem strongSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge rawSystem
      strongLawEquationCore strongSchemeBridge

theorem weakSchemeBridge_presentationStable
    (W : site.category) :
    AffineChart.AffineAATChart.SheafifiedChartPresentation rawSystem W

theorem weakSchemeBridge_toSheafifiedSection_bijective
    (W : site.category) :
    Function.Bijective (weakSchemeBridge.toSheafifiedSection W)

theorem weakCore_witnessIdeal_reflected
    (W : site.category) (i : lawUniverse.Index) :
    Ideal.comap (weakSchemeBridge.toSheafifiedSection W)
        (Ideal.map (weakSchemeBridge.toSheafifiedSection W)
          (weakLawEquationCore.lawWitnessIdeal W i)) =
      weakLawEquationCore.lawWitnessIdeal W i

noncomputable def baseGlobalCoordinate :
    Γ(twoChartReferenceModel.underlying, ⊤) :=
  twoChartReferenceModel.decoration.coordinateSection rawSystem ()

theorem weakCore_componentA_equation :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge PUnit.unit FiniteAtom.componentA =
      baseGlobalCoordinate - 1

theorem weakCore_other_equation
    (a : carrier.Atom) (ha : a ≠ FiniteAtom.componentA) :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge PUnit.unit a = 0

theorem strongCore_componentA_equation :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit FiniteAtom.componentA =
      baseGlobalCoordinate - 1

theorem strongCore_componentB_equation :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit FiniteAtom.componentB =
      baseGlobalCoordinate + 1

theorem strongCore_other_equation
    (a : carrier.Atom)
    (ha : a ≠ FiniteAtom.componentA) (hb : a ≠ FiniteAtom.componentB) :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit a = 0

theorem weakCore_leftChart_provenance_fires
    (a : carrier.Atom) :
    ((twoChartReferenceModel.atlas.chart leftIndex).map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem
            (twoChartReferenceModel.atlas.chart leftIndex).context)).hom)
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          weakLawEquationCore weakSchemeBridge PUnit.unit a) =
      weakSchemeBridge.toSheafifiedSection
        (twoChartReferenceModel.atlas.chart leftIndex).context
        (weakLawEquationCore.violationWitness
          (twoChartReferenceModel.atlas.chart leftIndex).context PUnit.unit a)

theorem weakCore_leftChart_witnessIdeal_realization_fires :
    Ideal.map
        (weakSchemeBridge.toSheafifiedSection
          (twoChartReferenceModel.atlas.chart leftIndex).context)
        (weakLawEquationCore.lawWitnessIdeal
          (twoChartReferenceModel.atlas.chart leftIndex).context PUnit.unit) =
      Ideal.span (Set.range (fun a =>
        weakSchemeBridge.toSheafifiedSection
          (twoChartReferenceModel.atlas.chart leftIndex).context
          (weakLawEquationCore.violationWitness
            (twoChartReferenceModel.atlas.chart leftIndex).context
            PUnit.unit a)))

noncomputable def weakReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  ClosedEquationalLawReading.ofSemanticCore rawSystem twoChartReferenceModel
    weakLawEquationCore weakSchemeBridge

noncomputable def strongReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  ClosedEquationalLawReading.ofSemanticCore rawSystem twoChartReferenceModel
    strongLawEquationCore strongSchemeBridge

@[simp] theorem weakReading_holdsOn_iff
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) (i : lawUniverse.Index) :
    weakReading.geometric.HoldsOn s i ↔
      ∀ a, s.appTop
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          weakLawEquationCore weakSchemeBridge i a) = 0

@[simp] theorem strongReading_holdsOn_iff
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) (i : lawUniverse.Index) :
    strongReading.geometric.HoldsOn s i ↔
      ∀ a, s.appTop
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          strongLawEquationCore strongSchemeBridge i a) = 0

@[simp] theorem weakReading_witness_eq_ofSemanticCore
    (i : lawUniverse.Index) (hi : weakReading.closed i) :
    weakReading.witness i hi =
      ClosedEquationalLawWitness.ofSemanticCore rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge i

@[simp] theorem strongReading_witness_eq_ofSemanticCore
    (i : lawUniverse.Index) (hi : strongReading.closed i) :
    strongReading.witness i hi =
      ClosedEquationalLawWitness.ofSemanticCore rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge i

theorem weakGeometricReading_valid :
    IsGeometricLawReading rawSystem twoChartReferenceModel weakReading.geometric

theorem strongGeometricReading_valid :
    IsGeometricLawReading rawSystem twoChartReferenceModel strongReading.geometric

theorem weakReading_witnessCompatible :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel weakReading

theorem strongReading_witnessCompatible :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel strongReading

theorem weakReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel weakReading

theorem strongReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel strongReading

theorem weakReading_closed_unit :
    weakReading.closed PUnit.unit

theorem weakReading_selected
    (V : twoChartReferenceModel.underlying.affineOpens)
    (i : lawUniverse.Index) :
    weakReading.selected V i

theorem strongReading_selected
    (V : twoChartReferenceModel.underlying.affineOpens)
    (i : lawUniverse.Index) :
    strongReading.selected V i

theorem weakCore_leftChart_idealSheaf_realization_fires :
    ((lawWitnessIdealSheaf rawSystem twoChartReferenceModel weakReading
        weakReading_witnessCompatible PUnit.unit weakReading_closed_unit).comap
        (twoChartReferenceModel.atlas.chart leftIndex).map) =
      Scheme.IdealSheafData.ofIdealTop
        (X := (twoChartReferenceModel.atlas.chart leftIndex).domain)
        (Ideal.map
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing rawSystem
              (twoChartReferenceModel.atlas.chart leftIndex).context)).inv.hom
          (Ideal.map
            (weakSchemeBridge.toSheafifiedSection
              (twoChartReferenceModel.atlas.chart leftIndex).context)
            (weakLawEquationCore.lawWitnessIdeal
              (twoChartReferenceModel.atlas.chart leftIndex).context PUnit.unit)))

theorem weakWitness_valid :
    IsClosedEquationalLawWitness rawSystem twoChartReferenceModel
      (weakReading.witness PUnit.unit weakReading_closed_unit)

theorem weakReading_requiredClosed :
    RequiredClosed rawSystem twoChartReferenceModel weakReading

theorem strongReading_requiredClosed :
    RequiredClosed rawSystem twoChartReferenceModel strongReading

theorem weakReading_allLawsSelected :
    AllLawsSelected rawSystem twoChartReferenceModel weakReading

theorem strongReading_allLawsSelected :
    AllLawsSelected rawSystem twoChartReferenceModel strongReading

theorem weakReading_requiredLawIdealExact :
    RequiredLawIdealExact rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed

theorem strongReading_requiredLawIdealExact :
    RequiredLawIdealExact rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed

theorem weakReading_lawIdealSound :
    LawIdealSound rawSystem twoChartReferenceModel weakReading
      weakReading_witnessCompatible PUnit.unit
      (weakReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit))

theorem weakReading_lawIdealComplete :
    LawIdealComplete rawSystem twoChartReferenceModel weakReading
      weakReading_witnessCompatible PUnit.unit
      (weakReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit))

theorem weakReading_lawIdealExact :
    LawIdealExact rawSystem twoChartReferenceModel weakReading
      weakReading_witnessCompatible PUnit.unit
      (weakReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit))

theorem weakReading_allLawIdealExact :
    AllLawIdealExact rawSystem twoChartReferenceModel weakReading
      weakReading_valid weakReading_allLawsSelected

theorem strongReading_allLawIdealExact :
    AllLawIdealExact rawSystem twoChartReferenceModel strongReading
      strongReading_valid strongReading_allLawsSelected

def weakToStrong :
    ClosedEquationalLawInclusion rawSystem twoChartReferenceModel
      weakReading strongReading

theorem weakToStrong_valid :
    IsClosedEquationalLawInclusion rawSystem twoChartReferenceModel weakToStrong

theorem weak_ideal_lt_strong :
    lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
        weakReading weakReading_valid weakReading_requiredClosed <
      lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
        strongReading strongReading_valid strongReading_requiredClosed

theorem weakSubscheme_nonempty :
    Nonempty (lawfulClosedSubscheme rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed)

theorem strongSubscheme_nonempty :
    Nonempty (lawfulClosedSubscheme rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed)

theorem weakImmersion_not_isIso :
    ¬ IsIso (lawfulClosedImmersion rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed)

theorem strongImmersion_not_isIso :
    ¬ IsIso (lawfulClosedImmersion rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed)

theorem weakToStrongMap_not_isIso :
    ¬ IsIso (lawfulClosedSubschemeMap rawSystem twoChartReferenceModel
      weakReading_valid strongReading_valid
      weakReading_requiredClosed strongReading_requiredClosed
      weakToStrong weakToStrong_valid)

theorem weakToStrongAllMap_not_isIso :
    ¬ IsIso (allLawfulClosedSubschemeMap rawSystem twoChartReferenceModel
      weakReading_valid strongReading_valid
      weakToStrong weakToStrong_valid)

/-- required idealとall idealを一つのreading内で区別する2-law index。 -/
inductive RequiredAllLawIndex
  | base
  | strengthening
  deriving DecidableEq

/-- `base`だけをrequired、`strengthening`をoptionalとするfinite law universe。 -/
def requiredAllLawUniverse : LawUniverse carrier where
  Index := RequiredAllLawIndex
  law
    | .base => noCycleLaw
    | .strengthening => substitutionLaw
  role
    | .base => LawRole.required
    | .strengthening => LawRole.optional
  witnessFamily := concreteNoCycleWitnessFamily
  SelectedReading := PUnit
  selectedReading := PUnit.unit
  coverageAssumptions := True
  exactnessAssumptions := True

theorem requiredAllLawUniverse_required_iff (i : RequiredAllLawIndex) :
    requiredAllLawUniverse.Required i ↔ i = .base

theorem requiredAllLawUniverse_optional_strengthening :
    requiredAllLawUniverse.Optional .strengthening

/-- 既存finite context geometryを2-law universeへretargetしたsite。 -/
noncomputable def requiredAllSite : Site.AATSite corePackage.object

@[simp] theorem requiredAllSite_lawUniverse :
    requiredAllSite.lawUniverse = requiredAllLawUniverse

/-- 既存のcoordinate、relation、restrictionを保つ2-law raw system。 -/
def requiredAllRawSystem : RawAmbientRestrictionSystem requiredAllSite Int

/-- retarget後のtopologyに対するfinite sheafification instance。 -/
noncomputable instance requiredAllHasSheafify :
    HasSheafify requiredAllSite.topology (AATCommAlgCat Int)

/-- 既存two-chart Schemeを同じunderlying Schemeのまま2-law siteへretargetしたmodel。 -/
noncomputable def requiredAllReferenceModel :
    StandardArchitectureScheme requiredAllRawSystem

theorem requiredAllReferenceModel_underlying :
    requiredAllReferenceModel.underlying = twoChartReferenceModel.underlying

noncomputable def requiredAllLawEquationCore :
    SemanticLawEquationWitnessIdealCore requiredAllSite

noncomputable def requiredAllSchemeBridge :
    SemanticLawEquationSchemeBridge requiredAllRawSystem requiredAllLawEquationCore

theorem requiredAllSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge requiredAllRawSystem
      requiredAllLawEquationCore requiredAllSchemeBridge

noncomputable def requiredAllBaseGlobalCoordinate :
    Γ(requiredAllReferenceModel.underlying, ⊤) :=
  requiredAllReferenceModel.decoration.coordinateSection requiredAllRawSystem ()

theorem requiredLaw_componentA_equation :
    semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
        requiredAllLawEquationCore requiredAllSchemeBridge
        .base FiniteAtom.componentA =
      requiredAllBaseGlobalCoordinate - 1

theorem strengtheningLaw_componentB_equation :
    semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
        requiredAllLawEquationCore requiredAllSchemeBridge
        .strengthening FiniteAtom.componentB =
      requiredAllBaseGlobalCoordinate + 1

noncomputable def requiredAllReading :
    ClosedEquationalLawReading requiredAllRawSystem requiredAllReferenceModel :=
  ClosedEquationalLawReading.ofSemanticCore requiredAllRawSystem
    requiredAllReferenceModel requiredAllLawEquationCore requiredAllSchemeBridge

theorem requiredAllReading_witnessCompatible :
    IsClosedEquationalWitnessReading requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading

theorem requiredAllReading_valid :
    IsClosedEquationalLawReading requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading

theorem requiredAllReading_requiredClosed :
    RequiredClosed requiredAllRawSystem requiredAllReferenceModel requiredAllReading

theorem requiredAllReading_allLawsSelected :
    AllLawsSelected requiredAllRawSystem requiredAllReferenceModel
      requiredAllReading

theorem required_indices_ssubset_closed :
    {i | requiredAllSite.lawUniverse.Required i} ⊂ requiredAllReading.closed

theorem requiredAllReading_selected
    (V : requiredAllReferenceModel.underlying.affineOpens)
    (i : RequiredAllLawIndex) :
    requiredAllReading.selected V i

theorem required_indices_ssubset_selected
    (V : requiredAllReferenceModel.underlying.affineOpens) :
    {i | requiredAllSite.lawUniverse.Required i} ⊂
      {i | requiredAllReading.selected V i}

/-- optional strengthening lawがall idealを真に強める。 -/
theorem required_ideal_lt_all_ideal :
    lawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid
        requiredAllReading_requiredClosed <
      allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid

/-- 同じreading内のall locusからrequired locusへのmapは同型ではない。 -/
theorem fullToRequiredLawfulMap_not_isIso :
    ¬ IsIso (fullToRequiredLawfulMap requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid requiredAllReading_requiredClosed)

noncomputable def selectedRequiredPoint :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of Int)) ⟶
      requiredAllReferenceModel.underlying

noncomputable def selectedModTwoPoint :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of (ZMod 2))) ⟶
      requiredAllReferenceModel.underlying

/-- `x = 1`のpointはrequired equationを満たす。 -/
theorem selected_point_factors_required :
    Nonempty (FactorsThroughLawfulClosedSubscheme requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid requiredAllReading_requiredClosed
      selectedRequiredPoint)

/-- 同じpointではoptional equationの値が`2`となり、all locusへはfactorしない。 -/
theorem selected_point_not_factors_all :
    ¬ Nonempty (FactorsThroughAllLawfulClosedSubscheme requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid selectedRequiredPoint)

/-- characteristic twoのpointはrequired / optional双方を満たす。 -/
theorem selected_modTwo_point_factors_all :
    Nonempty (FactorsThroughAllLawfulClosedSubscheme requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid selectedModTwoPoint)

noncomputable def integerPoint :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of Int)) ⟶
      twoChartReferenceModel.underlying

noncomputable def modTwoPoint :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of (ZMod 2))) ⟶
      twoChartReferenceModel.underlying

theorem integerPoint_objectComparison :
    RequiredObjectPointComparison rawSystem twoChartReferenceModel
      weakReading integerPoint
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject

theorem integerPoint_objectComparison_fails_for_cyclic :
    ¬ RequiredObjectPointComparison rawSystem twoChartReferenceModel
      weakReading integerPoint
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cyclicObject

theorem integerPoint_omega_fires :
    SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading integerPoint ↔
      omegaU noCycleValuation lawUniverse singletonRequiredAggregation
          AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject =
        noCycleValuation.domain.zero

theorem integerPoint_axis_fires :
    SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading integerPoint ↔
      RequiredSignatureAxesZero
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.signatureAxes

theorem integerPoint_globalEquationsVanish_weak :
    GlobalEquationsVanishAlong rawSystem twoChartReferenceModel
      (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge PUnit.unit) integerPoint

theorem integerPoint_not_globalEquationsVanish_strong :
    ¬ GlobalEquationsVanishAlong rawSystem twoChartReferenceModel
      (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit) integerPoint

theorem integerPoint_semanticLawful_weak :
    SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading integerPoint

theorem integerPoint_not_semanticLawful_strong :
    ¬ SemanticLawfulAlong rawSystem twoChartReferenceModel
      strongReading integerPoint

theorem integerPoint_fullySemanticLawful_weak :
    FullySemanticLawfulAlong rawSystem twoChartReferenceModel
      weakReading integerPoint

theorem integerPoint_not_fullySemanticLawful_strong :
    ¬ FullySemanticLawfulAlong rawSystem twoChartReferenceModel
      strongReading integerPoint

theorem integerPoint_witnessVanishes_weak :
    WitnessVanishes rawSystem twoChartReferenceModel weakReading
      weakReading_valid weakReading_requiredClosed integerPoint

theorem integerPoint_not_witnessVanishes_strong :
    ¬ WitnessVanishes rawSystem twoChartReferenceModel strongReading
      strongReading_valid strongReading_requiredClosed integerPoint

theorem integerPoint_idealLawful_weak :
    IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
      weakReading_valid weakReading_requiredClosed integerPoint

theorem integerPoint_not_idealLawful_strong :
    ¬ IdealLawfulAlong rawSystem twoChartReferenceModel strongReading
      strongReading_valid strongReading_requiredClosed integerPoint

theorem integerPoint_fullIdealLawful_weak :
    FullIdealLawfulAlong rawSystem twoChartReferenceModel weakReading
      weakReading_valid integerPoint

theorem integerPoint_not_fullIdealLawful_strong :
    ¬ FullIdealLawfulAlong rawSystem twoChartReferenceModel strongReading
      strongReading_valid integerPoint

theorem integerPoint_factors_weak :
    Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel weakReading weakReading_valid
      weakReading_requiredClosed integerPoint)

theorem integerPoint_not_factors_strong :
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel strongReading strongReading_valid
      strongReading_requiredClosed integerPoint)

theorem modTwoPoint_factors_weak :
    Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel weakReading weakReading_valid
      weakReading_requiredClosed modTwoPoint)

theorem modTwoPoint_factors_strong :
    Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel strongReading strongReading_valid
      strongReading_requiredClosed modTwoPoint)

theorem integerPoint_factorsAll_weak :
    Nonempty (FactorsThroughAllLawfulClosedSubscheme rawSystem
      twoChartReferenceModel weakReading weakReading_valid integerPoint)

theorem integerPoint_not_factorsAll_strong :
    ¬ Nonempty (FactorsThroughAllLawfulClosedSubscheme rawSystem
      twoChartReferenceModel strongReading strongReading_valid integerPoint)

theorem weak_correspondence_fires
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) :
    (SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading s ↔
      WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
        twoChartReferenceModel weakReading weakReading_valid
        weakReading_requiredClosed s))

theorem weak_semanticCore_correspondence_fires
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) :
    SemanticCoreIdealSheafRealized rawSystem twoChartReferenceModel
      weakLawEquationCore weakSchemeBridge ∧
    (SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading s ↔
      WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
        twoChartReferenceModel weakReading weakReading_valid
        weakReading_requiredClosed s))

theorem weak_full_correspondence_fires
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) :
    (FullySemanticLawfulAlong rawSystem twoChartReferenceModel weakReading s ↔
      FullIdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid s) ∧
    (FullIdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid s ↔
      Nonempty (FactorsThroughAllLawfulClosedSubscheme rawSystem
        twoChartReferenceModel weakReading weakReading_valid s))

noncomputable def restrictionBrokenSchemeBridge :
    SemanticLawEquationSchemeBridge rawSystem weakLawEquationCore

theorem restrictionBrokenSchemeBridge_not_valid :
    ¬ IsSemanticLawEquationSchemeBridge rawSystem
      weakLawEquationCore restrictionBrokenSchemeBridge

theorem restrictionBrokenSchemeBridge_not_realized :
    ¬ SemanticCoreIdealSheafRealized rawSystem twoChartReferenceModel
      weakLawEquationCore restrictionBrokenSchemeBridge

noncomputable def baseChangeBrokenGeometricReading :
    GeometricLawReading rawSystem twoChartReferenceModel

theorem baseChangeBrokenGeometricReading_not_valid :
    ¬ IsGeometricLawReading rawSystem twoChartReferenceModel
      baseChangeBrokenGeometricReading

noncomputable def baseChangeBrokenReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel

theorem baseChangeBrokenReading_witnessCompatible :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      baseChangeBrokenReading

theorem baseChangeBrokenReading_not_valid :
    ¬ IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      baseChangeBrokenReading

noncomputable def missingRequiredReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel

theorem missingRequiredReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      missingRequiredReading

theorem missingRequiredReading_not_requiredClosed :
    ¬ RequiredClosed rawSystem twoChartReferenceModel missingRequiredReading

theorem missingRequiredReading_not_allLawsSelected :
    ¬ AllLawsSelected rawSystem twoChartReferenceModel
      missingRequiredReading

/-- closed lawのselectionがbasic open restrictionで変化するnegative fixture。 -/
noncomputable def restrictionBrokenSelectionReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel

theorem restrictionBrokenSelectionReading_not_valid :
    ¬ IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      restrictionBrokenSelectionReading

/-- required lawをclosedに保つが、一つのaffine contextでselectionから外すnegative fixture。 -/
noncomputable def missingRequiredSelectionReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel

theorem missingRequiredSelectionReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      missingRequiredSelectionReading

theorem missingRequiredSelectionReading_not_requiredClosed :
    ¬ RequiredClosed rawSystem twoChartReferenceModel
      missingRequiredSelectionReading

noncomputable def semanticMismatchReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel

theorem semanticMismatchReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      semanticMismatchReading

theorem semanticMismatchReading_witnessCompatible :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      semanticMismatchReading

theorem semanticMismatchReading_requiredClosed :
    RequiredClosed rawSystem twoChartReferenceModel semanticMismatchReading

theorem semanticMismatchReading_allLawsSelected :
    AllLawsSelected rawSystem twoChartReferenceModel
      semanticMismatchReading

theorem semanticMismatchReading_not_exact :
    ¬ RequiredLawIdealExact rawSystem twoChartReferenceModel
      semanticMismatchReading semanticMismatchReading_valid
      semanticMismatchReading_requiredClosed

theorem semanticMismatchReading_not_lawIdealExact :
    ¬ LawIdealExact rawSystem twoChartReferenceModel
      semanticMismatchReading semanticMismatchReading_witnessCompatible
      PUnit.unit
      (semanticMismatchReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit))

theorem semanticMismatchReading_not_complete :
    ¬ LawIdealComplete rawSystem twoChartReferenceModel
      semanticMismatchReading semanticMismatchReading_witnessCompatible
      PUnit.unit
      (semanticMismatchReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit))

theorem semanticMismatchReading_not_allLawIdealExact :
    ¬ AllLawIdealExact rawSystem twoChartReferenceModel semanticMismatchReading
      semanticMismatchReading_valid
      semanticMismatchReading_allLawsSelected

theorem semanticMismatch_full_correspondence_fails :
    ¬ (FullySemanticLawfulAlong rawSystem twoChartReferenceModel
          semanticMismatchReading integerPoint ↔
        FullIdealLawfulAlong rawSystem twoChartReferenceModel
          semanticMismatchReading semanticMismatchReading_valid
          integerPoint)

noncomputable def semanticOverclaimReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel

theorem semanticOverclaimReading_valid :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      semanticOverclaimReading

theorem semanticOverclaimReading_witnessCompatible :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      semanticOverclaimReading

theorem semanticOverclaimReading_requiredClosed :
    RequiredClosed rawSystem twoChartReferenceModel semanticOverclaimReading

theorem semanticOverclaimReading_not_sound :
    ¬ LawIdealSound rawSystem twoChartReferenceModel semanticOverclaimReading
      semanticOverclaimReading_witnessCompatible PUnit.unit
      (semanticOverclaimReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit))

noncomputable def restrictionBrokenWitness :
    ClosedEquationalLawWitness rawSystem twoChartReferenceModel PUnit.unit

theorem restrictionBrokenWitness_not_valid :
    ¬ IsClosedEquationalLawWitness rawSystem twoChartReferenceModel
      restrictionBrokenWitness

noncomputable def restrictionBrokenReading :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel

theorem restrictionBrokenReading_not_witnessCompatible :
    ¬ IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      restrictionBrokenReading

theorem restrictionBrokenReading_not_valid :
    ¬ IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      restrictionBrokenReading

def coordinateBrokenInclusion :
    ClosedEquationalLawInclusion rawSystem twoChartReferenceModel
      weakReading strongReading

theorem coordinateBrokenInclusion_not_valid :
    ¬ IsClosedEquationalLawInclusion rawSystem twoChartReferenceModel
      coordinateBrokenInclusion

end AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry
```

finite moduleは次のfiring matrixを満たす。positive列とnegative列は、それぞれ独立した
named declarationを持つ。projection、definition unfold、`by trivial`だけの代用は不可とする。

| new predicate / factorization type | positive firing | negative firing |
| --- | --- | --- |
| `IsSemanticLawEquationSchemeBridge` | `weakSchemeBridge_valid` | `restrictionBrokenSchemeBridge_not_valid` |
| `SemanticCoreIdealSheafRealized` | `weak_semanticCore_correspondence_fires` | `restrictionBrokenSchemeBridge_not_realized` |
| `IsGeometricLawReading` | `weakGeometricReading_valid` | `baseChangeBrokenGeometricReading_not_valid` |
| `GlobalEquationsVanishAlong` | `integerPoint_globalEquationsVanish_weak` | `integerPoint_not_globalEquationsVanish_strong` |
| `IsClosedEquationalLawWitness` | `weakWitness_valid` | `restrictionBrokenWitness_not_valid` |
| `IsClosedEquationalWitnessReading` | `weakReading_witnessCompatible` | `restrictionBrokenReading_not_witnessCompatible` |
| `IsClosedEquationalLawReading` | `weakReading_valid` | `baseChangeBrokenReading_not_valid`、`restrictionBrokenReading_not_valid`、`restrictionBrokenSelectionReading_not_valid` |
| `RequiredClosed` | `weakReading_requiredClosed` | `missingRequiredReading_not_requiredClosed`、`missingRequiredSelectionReading_not_requiredClosed` |
| `AllLawsSelected` | `weakReading_allLawsSelected` | `missingRequiredReading_not_allLawsSelected` |
| `SemanticLawfulAlong` | `integerPoint_semanticLawful_weak` | `integerPoint_not_semanticLawful_strong` |
| `FullySemanticLawfulAlong` | `integerPoint_fullySemanticLawful_weak` | `integerPoint_not_fullySemanticLawful_strong` |
| `LawIdealSound` | `weakReading_lawIdealSound` | `semanticOverclaimReading_not_sound` |
| `LawIdealComplete` | `weakReading_lawIdealComplete` | `semanticMismatchReading_not_complete` |
| `LawIdealExact` | `weakReading_lawIdealExact` | `semanticMismatchReading_not_lawIdealExact` |
| `RequiredLawIdealExact` | `weakReading_requiredLawIdealExact` | `semanticMismatchReading_not_exact` |
| `AllLawIdealExact` | `weakReading_allLawIdealExact` | `semanticMismatchReading_not_allLawIdealExact` |
| `WitnessVanishes` | `integerPoint_witnessVanishes_weak` | `integerPoint_not_witnessVanishes_strong` |
| `IdealLawfulAlong` | `integerPoint_idealLawful_weak` | `integerPoint_not_idealLawful_strong` |
| `FullIdealLawfulAlong` | `integerPoint_fullIdealLawful_weak` | `integerPoint_not_fullIdealLawful_strong` |
| `FactorsThroughLawfulClosedSubscheme`の`Nonempty` | `integerPoint_factors_weak` | `integerPoint_not_factors_strong` |
| `FactorsThroughAllLawfulClosedSubscheme`の`Nonempty` | `integerPoint_factorsAll_weak` | `integerPoint_not_factorsAll_strong` |
| `RequiredObjectPointComparison` | `integerPoint_objectComparison` | `integerPoint_objectComparison_fails_for_cyclic` |
| `IsClosedEquationalLawInclusion` | `weakToStrong_valid` | `coordinateBrokenInclusion_not_valid` |
| 一つのreading内のrequired/all factorization | `selected_point_factors_required`、`selected_modTwo_point_factors_all` | `selected_point_not_factors_all` |

matrixの全entryをstatement contractと`AxiomAudit.lean`の双方へ登録する。negative firingは単に必要なpremiseを省略するのではなく、
具体的な式、section、index、atom、morphismのいずれが破れるかをproof bodyで示す。
`restrictionBrokenSchemeBridge_not_realized`は`restrictionBrokenSchemeBridge_not_valid`の否定だけから導かない。
broken bridgeを、`leftIndex`と`PUnit.unit`でcore idealのbridge像がactual chart pullback idealと異なるように構成し、
そのideal-level mismatchをwitnessとして`SemanticCoreIdealSheafRealized`を反証する。
`weakGeometricReading_valid` / `strongGeometricReading_valid`と各`witnessCompatible`は具体formulaから
独立に証明し、`weakReading_valid` / `strongReading_valid`はそのpairから組み立てる。full validityのfield射影を
component firingの代用にしない。
`weakSchemeBridge_valid`はrestriction naturalityとcanonical `SheafifiedChartPresentation`の双方を
構成し、`weakSchemeBridge_toSheafifiedSection_bijective`と`weakCore_witnessIdeal_reflected`で
core witnessがbridge kernelへ失われないことを発火させる。bridge mapはraw presentation equivalenceと
canonical unitの合成として定義されるため、任意のcollapse RingHomをbridge dataとして入力できない。
`restrictionBrokenSelectionReading_not_valid`はnamed basic openでselection equivalenceが破れること、
`missingRequiredSelectionReading_not_requiredClosed`はnamed affine contextでrequired lawが未選択であることを示す。

weak idealは`(x - 1)`、strong idealは`(x - 1, x + 1)`として発火させる。
両readingの`HoldsOn`は、各global equationを`s.appTop`で評価した値がzeroであるという
generator-level predicateから定義し、ideal comap zeroをdefinitionに使わない。
`RequiredLawIdealExact`はspanとring-hom imageの計算から証明する。
`integerPoint`は`x = 1`でweakにfactorし、`2 ≠ 0`によりstrongにはfactorしない。
`modTwoPoint`は両方にfactorする。strictness、properness、nonemptinessは同じevaluation mapsから証明し、
`⊥`、`⊤`、empty Scheme、identity morphismだけを主証拠にしない。
2-law fixtureでは`requiredAllLawUniverse_required_iff`によりrequired indexが`.base`だけであることを固定し、
`.strengthening`がclosedかつoptionalであることを別定理で示す。`selectedRequiredPoint`はrequired locusへfactorする一方、
optional generatorの評価値`2`によりall locusへfactorしない。これにより`required_ideal_lt_all_ideal`と
`fullToRequiredLawfulMap_not_isIso`を同じreading上で証明する。
base-change stability、required closedness、law ideal exactness、witness compatibility、inclusion validityの
各`Prop`にpositive firingとconcrete negative firingを置く。

### 数学本文との対応

| 数学本文 | Lean target | 対応 |
| --- | --- | --- |
| 定義5.1 Violation Witness Familyのatom-indexed specialization | `SemanticLawEquationWitnessIdealCore`、`SemanticLawEquationSchemeBridge`、`ClosedEquationalLawWitness.coordinate` | contextごとに型が変わる一般`Viol_L(W)`全体ではなく、existing coreが固定するatom-indexed witnessをraw quotient equivalenceとcanonical unitを通してactual local sectionへ送る。 |
| 定義5.2 Law Witness Idealのatom-indexed specialization | `semanticCoreLawWitnessIdeal_map`、`semanticCoreLawWitnessIdeal_comap_map`、`localLawWitnessIdeal` | core idealのbridge像をcoordinate spanと一致させ、valid bridgeのbijectionで元のcore idealを反映する。像計算だけをpresentation保存の証拠にしない。 |
| 定義5.2A Geometric Law Reading | `GeometricLawReading`、`IsGeometricLawReading` | section predicateとbase change保存を分離する。 |
| 定義5.2B ClosedEquational / LawIdealExact | `IsClosedEquationalLawWitness`、`LawIdealSound`、`LawIdealComplete`、`LawIdealExact` | closed equation dataとsemantic exactnessを別条件にする。 |
| 定義6.1 `I_Ob^U` / `I_Ob^{U,all}` | `ClosedEquationalLawReading.selected`、`lawGeneratedIdealSheaf` / `allLawGeneratedIdealSheaf` | 本文の`selected on W`をaffine open `V`ごとの`selected V`として持ち、各`V`のrequired / all selected supremumを別々に構成する。exact caseでは`selected_basicOpen`を要求する。 |
| 定義6.2 Obstruction Ideal Sheafのexact restriction-compatible case | `lawWitnessIdealSheaf`、`SemanticCoreIdealSheafRealized`、そのsupremum | actual `Scheme.IdealSheafData`を直接構成し、existing core idealとの一致をatlas chartへのpullbackで示す。一般sheaf-image caseは対象外。 |
| 定義7.1 `Flat_U(X)` / `FullFlat_U(X)` | `lawfulClosedSubscheme` / `allLawfulClosedSubscheme` | Mathlib subschemeとactual closed immersion。 |
| 定義7.2 Ideal-Lawful Section | `IdealLawfulAlong`、`FactorsThroughLawfulClosedSubscheme` | ideal comap zeroとactual morphism lift。 |
| 定理11.1 core | `lawfulnessIdealFactorizationCorrespondence`、`semanticCoreLawfulnessIdealFactorizationCorrespondence` | genericな三つの同値に加え、existing core経路ではvalid bridgeからactual chart ideal-sheaf realizationも返す。 |
| 定理11.1 valuation / axis extension | SD6の別定理 | object comparisonと各exactnessを明示した場合だけ追加する。 |
| 定義11.3・定理11.4のexisting Lean core | `SemanticLawEquationWitnessIdealCore`、`semanticCoreWitness_restrict`、`semanticCoreLawWitnessIdeal_map`、`semanticCoreIdealSheaf_realized` | merged coreのrestriction-compatible atom coordinatesとgenerated idealをactual Scheme ideal sheafのchart pullbackへ移す。displayed reading全体の再実装は主張しない。 |
| A.6〜A.7 | SD0〜SD7 | law subfunctorとclosed equationsをactual scheme APIへ接続する。 |
| A.8のatom-indexed presentation-stable case | `SemanticLawEquationSchemeBridge.toRawPresentation`、`IsSemanticLawEquationSchemeBridge.presentation_stable`、`toSheafifiedSection_bijective`、`semanticCoreIdealSheaf_realized` | core observableを同じraw quotient algebraへ同一視し、Part 2のcanonical-unit presentation、actual atlas chart、actual ideal sheaf componentを一つのcomparison chainで証明する。 |

## 問い

context-selected closed-equational law witnessesから、actual `Scheme.IdealSheafData`、required/allの
closed subschemes、actual factorization universal propertyを同じprovenanceの下で構成できるか。

```text
geometric law reading + selected-on-V atom-indexed local equations
  -> witness ideals I_i(V)
  -> actual ideal sheaves I_i
  -> required supremum I_Ob^U / all-law supremum I_Ob^{U,all}
  -> V(I_Ob^U) / V(I_Ob^{U,all})
  -> actual closed immersions and quotient affine cover
  -> semantic lawfulness iff ideal vanishing iff actual factorization
```

完了対象はset-level zero locus、任意ideal family、pulled ideal zeroのwrapperではない。
law witnessからMathlib closed geometryとactual liftまでを構成し、後続のconormal、cohomology、
deformationが`I_Ob^U`と`V(I_Ob^U)`を直接入力できるAPIを作る。

## 現状診断

- `SemanticLawEquationWitnessIdealCore`にはlaw/atom-indexed witness coordinates、local span、
  restrictionによるideal inclusion、generated quotient presheafがある。
- `SelectedLawWitnessIdealFamily`は`witnessIdeal : LawIndex → Ideal A`を任意入力として受けるため、
  standard Scheme上のactual sheafを単独では構成しない。
- `SheafImageConstruction`は`imageIdeal`と`agreesWithLocalSum`を保存するlegacy wrapperであり、
  actual sheaf imageまたは`IdealSheafData`ではない。
- `LawfulLocus.lawfulLocus`は`PrimeSpectrum.zeroLocus`の`Set`であり、
  Mathlib `Scheme`のclosed subschemeを構成しない。
- `FactorsThroughLawfulLocus`はpulled ideal zeroの再包装であり、
  actual morphism、triangle、一意性を持たない。
- `Correspondence.LawfulnessIdealCorrespondenceAssumptions`と`Package`は結論形のfieldを含み、
  本PRDのcore theoremの完了根拠には使えない。
- Mathlib `IdealSheafData.ofIdeals`は任意family以下の最大ideal sheafを返す。
  `ideal V`が入力familyと一致するとは無条件に言えない。
- Mathlibにはdirect constructor、complete lattice、`ofIdealTop`、`subschemeCover`、
  `subschemeObjIso`、`ker_subschemeι`、`range_subschemeι`、`map_gc`、`inclusion`、
  `IsClosedImmersion.lift`がある。

課題は既存local law-equation計算を置き換えることではない。
そのprovenanceをactual ideal sheaf、closed subscheme、factorizationへ接続し、
semantic exactnessをmaterial premiseとして正確に管理することである。

## アウトカム

完了時に次が成り立つ。

1. section-level semantic law readingとclosed-equational witness dataが分離される。
2. existing coreのlaw witness idealのbridge像が、移されたatom-indexed coordinatesのspanと一致する。
3. 各witness idealがlaw index、atom、affine open、ambient standard Schemeを保持し、
   coordinate restriction equalityからactual `IdealSheafData`が構成される。
4. global equations constructorが`IdealSheafData.ofIdealTop`と一致する。
5. closed-equationalityとaffine contextごとのselectionが分離される。
6. required ideal `I_Ob^U`とall selected closed-law ideal `I_Ob^{U,all}`が別々に構成され、objectwise idealが各contextのselected indexed supremumに一致する。
7. `I_Ob^U ≤ I_Ob^{U,all}`がactual ideal-sheaf inclusionとして証明される。
8. required/allのactual closed subschemesとclosed immersionsが構成される。
9. required/all comparisonがactual closed immersionとambient triangleを持つ。
10. 一般Scheme上のclosed geometryがquotient affine coverとsection-ring isoを持つ。
11. closed immersionのkernelとrangeがMathlib APIへ接続される。
12. AAT reading decorationがactual closed immersionに沿ってpullbackされる。
13. semantic lawfulness、law-wise witness vanishing、required sum vanishing、actual factorizationが
    定理11.1のpremiseの下で同値になる。
14. factorization lift、triangle、一意性がMathlib universal propertyから導かれる。
15. 全lawがclosed-equationalである場合のfull semantic/full ideal/actual factorization theoremが別にある。
16. valuationとaxisはobject comparisonと各exactnessを明示した別定理で接続される。
17. stronger law dataからrequired/all ideal inclusion、required/full semantic monotonicity、反変向きの
    required/all actual closed-geometry mapが構成される。
18. nondegenerate finite pairがstrict ideal inclusion、proper nonempty geometry、factorization yes/noを示す。
19. downstream moduleがdefinition unfoldなしでideal、subscheme、immersion、cover、liftを利用できる。

## 採否規律

- `docs/aat/algebraic_geometric_theory/**`はread-onlyとし、本PRDの実装で変更しない。
- 対象はclosed-equational lawsである。open、constructible、temporal、stacky lawをideal sumへ入れない。
- witness idealはatom-indexed equationsのspanから生成する。任意idealをprimary inputにしない。
- ideal sheafはactual `Scheme.IdealSheafData`を使う。
- `ofIdeals`を使う場合は、入力familyとのobjectwise equalityを先に証明する。
- required idealとall selected closed-law idealを同一視しない。
- general Schemeを単一`Spec(A/I)`へ弱めない。quotient affine coverを使う。
- semantic lawfulnessをideal vanishingとして定義しない。
- law-by-law exactnessをfree `Prop`、certificate、typeclass、structure fieldの結論射影で代替しない。
- factorizationはactual Scheme morphism、triangle、一意性で表す。
- law inclusionはprimitive mapsからideal monotonicityを導く。derived ideal equalityを入力しない。
- valuation/axisのexactnessをcore exactnessから自動導出しない。
- target statementと参照definitionはStatement Designを不変入力とする。

## 改修要求

### R0 — dependency、Mathlib API、fixed statementの確定

- 実行開始条件を満たし、対象main commitをtracking Issueに固定する。
- current declarationsとMathlib APIのexact signatureをscratch fileで確認する。
- Module import contractの全direct importを固定し、特に
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`から`IdealSheafData.inclusion`の
  closed-immersion instanceを利用可能にする。
- legacy wrappersの全利用箇所を棚卸しし、新主経路の証明依存に入れない。
- SD0〜SD9の全targetとmaterial premiseをIssueへ転記する。
- target signature変更が発生した場合は実装を止める。

### R1 — semantic readingとwitness provenance

- `GeometricLawReading`と`IsGeometricLawReading`をdata/validityに分離する。
- `ClosedEquationalLawWitness`をlaw/atom/affine-open indexed section familyとして定義する。
- local idealを`Ideal.span (Set.range coordinate)`から定義する。
- coordinate restriction equalityからbasic-open ideal equalityを証明する。
- global equations constructorとvalidity theoremを提供する。
- `SemanticLawEquationSchemeBridge`をraw presentation equivalenceから構成し、bridge mapをcanonical
  sheafification unitとの合成として定義する。restriction naturalityと`SheafifiedChartPresentation`を証明する。
- existing coreのwitness idealのbridge像が移されたatom-indexed coordinatesのspanと一致し、
  valid bridgeのmap/comapで元のidealが反映されることを証明する。
- actual atlas chart上でglobal equationがcore witnessへ戻るcomparison theoremを証明する。
- existing core由来の`lawWitnessIdealSheaf`をchartへcomapしたactual ideal sheafが、core idealのbridge像を
  `ΓSpecIso.inv`で移した`ofIdealTop`と一致することを証明する。
- constructor、extensionality、projection、characterization theoremを揃える。

### R2 — actual ideal sheavesとrequired/all ideals

- local ideal familyから`IdealSheafData`を直接構成する。
- global equations routeと`ofIdealTop`の一致を証明する。
- `closed`とaffine contextごとの`selected`を分離し、selectionのclosed性とbasic-open不変性を証明する。
- required/allを各affine contextのselected indexed supremumとして別々に定義する。
- objectwise idealとcontext-selected indexed supremumのexact equalityを証明する。
- required idealからall idealへのinclusionを証明する。
- arbitrary familyを`ofIdeals`へ渡しただけでobjectwise equalityを主張しない。

### R3 — actual closed geometry

- required/allのsubschemeとimmersionをMathlib constructorから定義する。
- closed immersion、kernel、range/supportをMathlib theoremへ接続する。
- `subschemeCover`と`subschemeObjIso`を公開APIとして包む。
- pulled decorationのcontext、law universe、signature、coordinate sectionの保存を証明する。
- all locusからrequired locusへのclosed immersionとambient triangleを証明する。
- affine-specific single quotient spectrum theoremは`IsAffine`を明示した別lemmaに限る。

### R4 — law exactnessとactual factorization

- soundness、completeness、exactnessをlaw-by-lawに定義する。
- exactnessがsoundnessとcompletenessのconjunctionであることを証明する。
- required/all用のaggregate exactness predicateを定義する。
- witness-wise vanishingとrequired supremum vanishingをcomplete latticeから同値にする。
- ideal comap zeroをkernel inclusionへ接続する。
- actual lift、triangle、一意性をMathlib universal propertyから構成する。
- legacy `FactorsThroughLawfulLocus`をactual factorizationの証拠に使わない。

### R5 — 定理11.1 coreと別exactness

- SD5の三つのiff edgeを個別theoremとして証明する。
- `lawfulnessIdealFactorizationCorrespondence`をその三edgeから証明する。
- existing-core版`semanticCoreLawfulnessIdealFactorizationCorrespondence`はvalid bridgeをproof-useし、
  canonical `ofSemanticCore_requiredClosed`を内部使用してactual chart ideal-sheaf realizationと三edgeを同時に返す。
- required indexed sum compatibilityとfactorization criterionを追加入力にしない。
- 本文のfull版は`AllLawsSelected`と`AllLawIdealExact`の下で別に証明する。
- context-selected aggregate idealにはactual factorization APIを与えるが、局所化していない
  `HoldsOn`とのglobal semantic equivalenceを追加しない。
- cover premiseをcore theoremへ持ち込まない。
- SD6のobject、valuation、axis theoremをcoreと別に実装する。
- 各material premiseがproof bodyで使われることをstatement contractとreviewで確認する。

### R6 — law inclusion

- inclusion dataをlaw index mapとatom mapだけで定義する。
- required/closed/context selection preservation、coordinate equality、semantic implicationをvalidity predicateに置く。
- refl、compとそのvalidityを証明する。
- per-law ideal inclusionとrequired/all supremum inclusionを証明する。
- stronger required / full semantic lawfulnessから各weaker lawfulnessを証明する。
- required/all双方のactual subscheme map、closed immersion、ambient triangle、identity、compositionを証明する。

### R7 — nondegenerate finite examples

- existing `twoChartReferenceModel`をambient Schemeとしてweak/strong fixtureに再利用する。
- `x - 1`と`x + 1`からweak/strong readingsを構成する。
- 同じcontext geometry、raw relation、underlying Schemeを保つ2-law site / raw system / standard schemeを構成し、
  `.base`だけをrequired、`.strengthening`をoptionalかつclosedにする。
- global equations constructorでwitness compatibilityを放電する。
- generator-level semantic predicateからrequired law exactnessを証明し、core correspondenceを発火させる。
- evaluation mapsでstrict ideal inclusionとpropernessを証明する。
- 2-law reading上で`required_ideal_lt_all_ideal`と`fullToRequiredLawfulMap_not_isIso`を具体evaluationから証明する。
- integer pointとmod-2 pointをactual Scheme morphismとして構成する。
- weak-only / both factorizationに加え、同じ2-law reading上のrequired factorization / all non-factorizationをactual liftsで示す。
- `restrictionBrokenSchemeBridge`でactual chart pullback idealとの具体的不一致を示し、
  `restrictionBrokenSchemeBridge_not_realized`をbridge validityの否定へ還元せず証明する。
- bridge mapのbijectionとwitness ideal reflectionを発火させ、collapse RingHomをdata constructorから排除する。
- restriction-broken selectionとmissing-required selectionを別fixtureで発火させる。
- SD9 firing matrixに列挙した全new predicate / factorization typeについて、positiveとnegativeの
  named theoremを具体式から証明する。

### R8 — API quality、contracts、audit、aggregate

- 全public declarationへ数学的役割、入力provenance、仮定を説明するdocstringを付ける。
- constructor/destructor/ext/characterization/comparison APIを揃え、downstreamでのunfoldを不要にする。
- `StatementContractsClosedEquationalGeometry.lean`へSD0〜SD7とSD9のexact signature exampleを置く。
- `AxiomAudit.lean`へimplementation moduleとfinite example moduleで追加した全public theoremを登録する。
- `Formal/AG/LawAlgebra.lean`がmain implementation moduleとfinite example moduleを直接importし、
  `Formal/AG/StatementContracts.lean`がstatement contract moduleを直接importする。
- `Formal/AG.lean`から両aggregateへのtransitive import pathを確認し、
  `research/lean/ResearchLean`からreverse importしない。
- `sorry`、`admit`、新規`axiom`、結論相当certificateを残さない。

### R9 — final premise discharge、review、source-of-truth

- final snapshotの全target declarationについて、明示引数、typeclass、structure field、certificate fieldを
  独立に列挙し、SD8の各行と突合する。
- 各material premiseについて放電元、proof bodyで使う箇所、主結論への寄与を記録し、
  `material_premise_ledger_delta = ∅`かつ`new_material_premise = ∅`を確認する。
- statement diffを取り、Approved signatureとの差分がzeroであることを記録する。
- protected math sourceの差分がzeroであることを確認する。
- `math-lean-review`の4本の独立査読を最終snapshotに対して実行する。
- findingを修正した場合はreview protocolに従って直接対応または正式再実行を行う。
- CI green、review完了、Issue/PR status同期後にのみ完了と判定する。
- runtime stateはGitHub Issue / PRに保持し、新しい進捗Markdownを作らない。

## Acceptance Criteria

- [ ] AC1: tracking Issueが対象main commit、SD0〜SD9 target、material premise、依存順を固定している。
- [ ] AC2: statement contractがimplementationとfinite exampleの全public definition/theoremの完全signatureを`example`で直接参照する。
- [ ] AC3: `ClosedEquationalLawReading`がsemantic reading、closed-equationality、affine contextごとのselection、witness dataだけを持ち、ideal、subscheme、lawfulness、factorizationをfieldに持たない。
- [ ] AC4: `IsClosedEquationalLawReading`が別の`Prop` recognition predicateであり、`selected_closed`と`selected_basicOpen`を具体proofとして持つ。
- [ ] AC5: semantic `HoldsOn`がideal vanishingの別名ではなく、base change保存が具体proofを持つ。
- [ ] AC6: bridgeは`Observable W ≃+* raw.rawAlgebra W`とcanonical `sheafificationUnitAlgHom`から構成され、validityが全`W`の`SheafifiedChartPresentation`を要求する。bridge mapのbijectionとcore witness idealのmap/comap reflectionを証明し、さらに`semanticCoreIdealSheaf_realized`がpresentation provenanceと全atlas-chart pullback equalityを同時に返す。
- [ ] AC7: local witness idealがlaw/atom-indexed sectionsのspanから生成され、coordinate restriction equalityから`map_ideal_basicOpen`のexact equalityが導かれる。
- [ ] AC8: `lawWitnessIdealSheaf`がactual `Scheme.IdealSheafData`であり、任意ideal familyをprimary inputにしない。
- [ ] AC9: global equations constructorのideal sheafが`IdealSheafData.ofIdealTop`と一致する。
- [ ] AC10: required `lawGeneratedIdealSheaf`とall `allLawGeneratedIdealSheaf`が別definitionであり、両方が`R.selected V`をobjectwiseにproof-useする。
- [ ] AC11: 両ideal sheafのobjectwise idealが各affine contextのselected indexed supremumと一致し、`selected_basicOpen`からexact restriction equalityが導かれる。
- [ ] AC12: `lawGeneratedIdealSheaf_le_all`がactual ideal-sheaf inclusionを与える。
- [ ] AC13: required/all closed geometryがactual Mathlib subschemeと`subschemeι`である。
- [ ] AC14: required/all comparisonがactual closed immersionとambient triangleを持つ。
- [ ] AC15: `lawfulClosedImmersion_ker`と`lawfulClosedImmersion_range`がMathlib APIから証明される。
- [ ] AC16: general Scheme上のlocal quotient geometryが`subschemeCover`と`subschemeObjIso`で公開される。
- [ ] AC17: general Schemeを単一global `Spec(A/I)`とする未証明claimがない。
- [ ] AC18: lawful closed decorationがactual immersionに沿う`AATReadingDecoration.pullback`である。
- [ ] AC19: `LawIdealExact`が全test Schemeと全sectionを量化し、soundness/completenessの両方向を持つ。
- [ ] AC20: required exactnessと全law exactnessが区別され、finite readingがrequired/full exactnessをgenerator計算から放電する。context-selected aggregate ideal単独にはglobal semantic equivalenceを主張しない。
- [ ] AC21: witness-wise vanishingとrequired supremum vanishingの同値に追加入力premiseがない。
- [ ] AC22: ideal comap zeroとkernel inclusionが`map_gc`と`map_bot`から接続される。
- [ ] AC23: factorizationがactual morphism、triangle equality、一意性を持つ。
- [ ] AC24: generic `lawfulnessIdealFactorizationCorrespondence`がsemantic、witness、ideal、actual factorizationの三edgeを返す。existing-core版は`IsSemanticLawEquationSchemeBridge`をproof-useし、`ofSemanticCore_requiredClosed`を内部使用してpresentation-stable chart realizationと三edgeを同時に返す。finite readingで両経路が直接発火する。
- [ ] AC25: ambient inputとconstruction validityを除き、generic core theoremが新たに要求するtheorem-specific semantic premisesは`RequiredClosed`と`RequiredLawIdealExact`に限られ、両方がproof-usedである。existing-core版は`RequiredClosed`を再要求せずcanonical theoremで放電し、bridge validityのrestriction componentとpresentation componentの双方をproof-useする。全target inventoryをSD8と突合する。
- [ ] AC26: cover由来のpremiseがcore theoremのunused argumentとして残らない。
- [ ] AC27: object comparison、valuation exactness、axis exactnessがSD6の別theoremに分離される。
- [ ] AC28: `ClosedEquationalLawInclusion`がprimitive mapsだけを持ち、validity predicateのclosed/context selection preservationからideal inclusionを導く。
- [ ] AC29: law inclusionがrequired / full semantic monotonicityと、required/all双方のactual subscheme map、closed immersion、ambient triangle、identity、compositionを持つ。
- [ ] AC30: finite weak/strong pairが同一ambient Scheme上でstrict ideal inclusionを示し、2-law fixtureが同じunderlying Schemeを保持する。
- [ ] AC31: weak/strong closed subschemesがnonemptyかつambientと同一でなく、2-law fixtureではrequired indicesが各named affine contextのselected indicesの真部分である。
- [ ] AC32: 2-law reading上で`required_ideal_lt_all_ideal`と`fullToRequiredLawfulMap_not_isIso`を具体evaluationから証明する。
- [ ] AC33: `integerPoint`がweakだけにfactorし、`modTwoPoint`がweak/strong双方にfactorする。加えて`selectedRequiredPoint`が同じ2-law readingのrequired locusへfactorし、all locusへfactorしない。
- [ ] AC34: SD9 firing matrixに列挙した全new predicate / factorization typeに、独立したpositive/negative named declarationがある。bridgeのbijection / ideal reflection、selection restriction failure、required selection failure、`SemanticCoreIdealSheafRealized`のpositive/negativeをstatement contractと`AxiomAudit.lean`の双方へ登録する。
- [ ] AC35: 主証拠が`⊥`、`⊤`、empty Scheme、identity morphismだけに依存しない。
- [ ] AC36: legacy `SheafImageConstruction`、`FactorsThroughLawfulLocus`、`LawfulnessIdealCorrespondencePackage`が新主定理の証明依存に入らない。
- [ ] AC37: public APIにdocstring、extensionality、characterization、comparison theoremがあり、downstream testがdefinition unfoldに依存しない。
- [ ] AC38: `Formal/AG/LawAlgebra.lean`と`Formal/AG/StatementContracts.lean`が担当moduleを直接importし、`Formal/AG.lean`からtransitiveに到達でき、ResearchLeanへのreverse importがない。
- [ ] AC39: target declarationsとexamplesに`sorry`、`admit`、新規`axiom`がなく、`AxiomAudit.lean`が両moduleの全new public theoremを参照し、standard axiomsのみを報告する。
- [ ] AC40: protected math sourceのdiffがzeroである。
- [ ] AC41: final snapshotの全target declarationについて明示引数/typeclass/structure field/certificate fieldを独立監査し、放電元とproof-useを記録したうえで、`material_premise_ledger_delta = ∅`、`new_material_premise = ∅`、statement diff zeroをtracking Issueに記録する。
- [ ] AC42: `math-lean-review`の4本がすべて合格、またはfinding全解消後の有資格な直接対応が記録される。
- [ ] AC43: required CIがgreenで、PR merge後にtracking Issueと依存Issueのstatusが同期される。
- [ ] AC44: diff、staged diff、untracked file、hidden Unicode、`unsafe`、placeholder、internal pathのstatic checksがcleanである。
- [ ] AC45: 完了後のPRD処理が`docs/guideline.md`のcontent-invariant archive手順を満たす。

## Failure Contract

次は完了ではなく失敗である。

- `ClosedEquationalLawReading`へarbitrary `Ideal`、`IdealSheafData`、subscheme、factorization proofを保存する。
- arbitrary ideal familyを`ofIdeals`へ渡し、objectwise equalityなしに入力familyと同一視する。
- `imageIdeal`とequality fieldをactual sheaf imageと呼ぶ。
- required lawsとall selected closed lawsを同じidealへ畳み込む、またはfinite fixtureでrequired indexとall closed indexを同一集合にしたままcomparison達成を主張する。
- existing coreのbridge像とcoordinate spanだけを示し、actual `lawWitnessIdealSheaf`のchart pullbackとの一致を未接続のまま完了とする。
- arbitraryまたは自然なRingHomだけをbridgeとして受け、raw presentation equivalenceとcanonical sheafification unitへ接続せずA.8のpresentation-stabilityを主張する。
- core witness generatorをkernelへ落とせるmapについて、image ideal equalityだけでpresentation保存またはrealization達成を主張する。
- context-independentな`closed : Set Index`を本文の`selected on W`の代用にし、`selected V`と`selected_basicOpen`をfixed statementへ持たない。
- required lawが未選択のaffine contextでrequired semantic/ideal correspondenceを主張する。
- 一部のaffine contextだけでselectedなlawのobjectwise aggregate idealと、context引数を持たないglobal `HoldsOn`を無条件に同値とする。
- local witness restrictionがinclusionしか与えないのに、`map_ideal_basicOpen`のequalityを仮定する。
- atom-indexed specializationだけを実装して、contextごとに変わる一般`Viol_L(W)`または
  定義6.2の一般sheaf-image construction全体の完了を主張する。
- general Schemeを単一の`Spec(A/I)`として扱う。
- `PrimeSpectrum.zeroLocus`の`Set`だけでclosed geometry完成とする。
- semantic lawfulnessをwitness vanishingまたはideal comap zeroとして定義する。
- `LawIdealExact`をfree `Prop`、opaque adequacy field、結論相当certificateから射影する。
- factorizationをideal comap zeroのrepackageにし、actual liftとtriangleを構成しない。
- lift、triangle、一意性をstructure fieldとして入力する。
- cover premiseをcore theoremへ追加し、proof bodyで使わない。
- valuation/axis conclusionをlaw-ideal exactnessだけから導く。
- law inclusionへ`witness_eq`またはideal equalityをdata fieldとして直接保存する。
- point-set inclusionだけでlaw inclusionのfunctoriality完成とする。
- zero ideal、unit ideal、empty Scheme、all-identity morphismだけでfinite firingを済ませる。
- wrapper、alias、renaming、既存packageのfield射影だけでtarget名を満たす。
- theorem名の存在、`lake build`、axiom scan、docs整備だけで数学的達成と判定する。
- `AxiomAudit.lean`へ代表theoremだけを登録し、new public theoremの一部を監査対象から外す。
- aggregate importまたはfinal premise ledgerの差分を未確認のまま完了とする。
- implementation convenienceを理由にfixed statementの対象、仮定、結論を変更する。

## 停止条件

次のいずれかが発生したら実装を止める。

- fixed signatureを弱める、material premiseを増やす、結論相当fieldを追加する必要が生じた。
- law witness coordinatesからbasic-open ideal equalityを証明できない。
- Mathlib `IdealSheafData`からSD3またはSD4のactual geometryを構成できない。
- required/allの分離を保ったまま定理11.1 coreを証明できない。
- nondegenerate weak/strong pairのstrictness、properness、factorization差を証明できない。
- 数学本文に独立した型不整合、well-definedness欠陥、反例が見つかった。

停止報告には、該当SD / AC、fixed signature、最小のcounterexampleまたはAPI blocker、
試したMathlib route、未放電仮定、必要な補題または未移植theorem、数学本文改訂の要否を記録する。
停止中のwrapperや弱いtheoremを完了根拠として残さない。

## Non-goals

- cover上のlocal vanishingからglobal vanishingを計算する一般定理。
- open、constructible、temporal、stacky lawのideal-sheaf encoding。
- conormal sheaf`I/I^2`、short exact sequence、Čech connecting class、first-order lift。
- derived zero locus、cotangent complex、`Ext^1`、higher obstruction。
- general coefficient base changeを含むreading functoriality。
- full two-chart law-variation reference modelの追加。
- legacy wrapper自体の削除。
- Research成果の本体蒸留。
- protected math sourceへの編集。

## 検証

実装時は`AGENTS.md`、`docs/aat/guideline.md`、`docs/aat/lean_quality_standard.md`を直接適用する。
通常の実装確認では、統括エージェントが単一の非aggregate fileを対象に次を実行する。

```bash
lake env lean Formal/AG/LawAlgebra/ClosedEquationalGeometry.lean
lake env lean Formal/AG/LawAlgebra/ClosedEquationalGeometryFiniteExample.lean
lake env lean Formal/AG/StatementContractsClosedEquationalGeometry.lean
```

Lean変更を含むPR前に、統括エージェントが`lake build`を1回だけ実行する。
サブエージェントは`lake build`、aggregate rootのelaboration、全file loopを実行しない。
PR作成後のfull buildはCIへ任せる。

task固有のfocused checksは次である。

1. scratch fileでSD0〜SD7のMathlib API exact namesと
   `Mathlib.AlgebraicGeometry.Morphisms.Separated`由来のinstanceを`#check`する。
2. statement contractがimplementation moduleとfinite example moduleの全public definition/theoremの
   fixed signatureを`example`で直接検査する。
3. `AxiomAudit.lean`が両moduleで追加した全public theoremを一件ずつ参照する。
4. `#print axioms`がstandard axioms以外を報告しない。
5. finite exampleでSD9 firing matrixの全positive/negative pair、`weak_ideal_lt_strong`、
   `required_ideal_lt_all_ideal`、`fullToRequiredLawfulMap_not_isIso`、nonempty、factorization yes/noを同時に確認する。
6. final snapshotの全target declarationについて明示引数、typeclass、structure field、certificate field、
   放電元、proof-use、主結論への寄与を独立監査し、SD8にないmaterial premiseがないことを確認する。
7. `Formal/AG/LawAlgebra.lean`と`Formal/AG/StatementContracts.lean`の直接import、
   `Formal/AG.lean`からのtransitive importを確認する。
8. protected math sourceのdiffがzeroであることを確認する。

PR前のtextual checksは次である。

```bash
git diff --check
git diff --cached --check
git ls-files --others --exclude-standard
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" \
  Formal/AG/LawAlgebra/ClosedEquationalGeometry.lean \
  Formal/AG/LawAlgebra/ClosedEquationalGeometryFiniteExample.lean \
  Formal/AG/StatementContractsClosedEquationalGeometry.lean \
  Formal/AG/AxiomAudit.lean \
  Formal/AG/LawAlgebra.lean \
  Formal/AG/StatementContracts.lean \
  Formal/AG.lean \
  docs/aat/aat_lean_03_closed_equational_geometry_prd.md
rg -n "s[o]rry|a[d]mit|^a[x]iom |T[O]DO|F[I]XME|u[n]safe" \
  Formal/AG/LawAlgebra/ClosedEquationalGeometry.lean \
  Formal/AG/LawAlgebra/ClosedEquationalGeometryFiniteExample.lean \
  Formal/AG/StatementContractsClosedEquationalGeometry.lean
rg -n '^import (Formal.AG.Atom.LawfulnessZero|Formal.AG.LawAlgebra.LawEquation|Formal.AG.LawAlgebra.StandardScheme|Mathlib.AlgebraicGeometry.IdealSheaf.Functorial|Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme|Mathlib.AlgebraicGeometry.Morphisms.Separated)$' \
  Formal/AG/LawAlgebra/ClosedEquationalGeometry.lean
rg -n '^import (Formal.AG.LawAlgebra.ClosedEquationalGeometry|Formal.AG.LawAlgebra.StandardSchemeFiniteExample|Formal.AG.LawAlgebra.FiniteExamples)$' \
  Formal/AG/LawAlgebra/ClosedEquationalGeometryFiniteExample.lean
rg -n '^import Formal.AG.LawAlgebra.ClosedEquationalGeometry(FiniteExample)?$' \
  Formal/AG/StatementContractsClosedEquationalGeometry.lean \
  Formal/AG/AxiomAudit.lean
rg -n '^import Formal.AG.LawAlgebra.ClosedEquationalGeometry(FiniteExample)?$' \
  Formal/AG/LawAlgebra.lean
rg -n '^import Formal.AG.StatementContractsClosedEquationalGeometry$' \
  Formal/AG/StatementContracts.lean
rg -n '^import Formal.AG.(LawAlgebra|StatementContracts)$' Formal/AG.lean
rg -n "research/lean/ResearchLean|ResearchLean" \
  Formal/AG/LawAlgebra/ClosedEquationalGeometry.lean \
  Formal/AG/LawAlgebra/ClosedEquationalGeometryFiniteExample.lean \
  Formal/AG/StatementContractsClosedEquationalGeometry.lean
rg -n '/U[s]ers/|D[o]cuments/LEAN|\.c[o]dex/worktrees|\.l[a]ke/packages' \
  Formal/AG/LawAlgebra/ClosedEquationalGeometry.lean \
  Formal/AG/LawAlgebra/ClosedEquationalGeometryFiniteExample.lean \
  Formal/AG/StatementContractsClosedEquationalGeometry.lean \
  Formal/AG/AxiomAudit.lean \
  Formal/AG/LawAlgebra.lean \
  Formal/AG/StatementContracts.lean \
  Formal/AG.lean \
  docs/aat/aat_lean_03_closed_equational_geometry_prd.md
```

`git ls-files --others --exclude-standard`はPR前snapshotでzero、`rg`のnegative scansはmatch zeroを要求する。
aggregate import checksは各required importが一件以上matchすることを要求する。

## Completion evidence packet

完了判定には次を一つのGitHub tracking Issue commentへまとめる。

| evidence | 必須内容 |
| --- | --- |
| fixed statement diff | Approved SD0〜SD9 signatureと実装signatureの差分zero。 |
| declaration map | 各ACに対応するdeclaration名、source file、focused check。 |
| premise discharge | 全target declarationの明示引数/typeclass/structure field/certificate field、SD8分類、放電元、proof-use、主結論への寄与。`material_premise_ledger_delta = ∅`かつ`new_material_premise = ∅`。 |
| geometry evidence | ideal sheaf、kernel、range、quotient cover、actual lift、triangle、一意性。 |
| finite evidence | weak/strong strictness、proper nonempty、required/all comparison non-iso、integer/mod-2 factorization。 |
| firing evidence | SD9 firing matrixの全entryについてpositive/negative declaration、使用した具体式、section、index、atom、morphism。 |
| negative evidence | semantic mismatch、semantic overclaim、invalid bridge、base-change failure、missing required/all selection、invalid witness、invalid reading、invalid inclusion、legacy wrapper非依存。 |
| axiom evidence | 全new public theoremを含むstatement contracts、axiom audit、`#print axioms`結果。 |
| aggregate evidence | 二つの直接import、`Formal/AG.lean`からのtransitive import、ResearchLean reverse import zero。 |
| static evidence | diff/staged/untracked、hidden Unicode、placeholder、`unsafe`、privacy/internal-path scans。 |
| review evidence | 4本の独立査読結果とfinding対応。 |
| CI evidence | required checksのgreen結果とmerge commit。 |
| source evidence | protected math source diff zero、runtime status同期。 |

PRDの完了、参照除去、archiveは`docs/guideline.md`を正本とする。
全AC、review、CI、merge、runtime status同期が完了し、repository-wideのlive referenceがzeroになった後、
contentを変更せず`git mv`でarchiveする。archive後の文書を現行source of truthとして参照しない。
