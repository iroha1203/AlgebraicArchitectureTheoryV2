# PRD: AAT Lean Standard Architecture Scheme Core

- 作成: 2026-07-12
- 対象: `Formal/AG/LawAlgebra/StandardScheme.lean`、`AffineChart.lean`のsheafified
  representability、finite examples、aggregate、statement contracts、axiom audit、Lean台帳
- 数学的正典: `docs/aat/algebraic_geometric_theory/` 第III部 定義8.1〜8.2、定理8.3、
  仮定8.4、定義9.2〜9.3、定義10.1、定義10.3のうち既存Scheme上で
  open immersion・joint coverage・overlap coherenceを認識する部分、
  Appendix A.3〜A.5
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、`docs/aat/lean_quality_standard.md`
- tracking Issue: 未作成。Issue作成と依存登録が済むまで実行不可
- statement contract正本: 本PRDの`Statement Design`節
- executable contract: `Formal/AG/StatementContractsStandardArchitectureScheme.lean`。実装と同時に作成し、CIでelaborateする
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

- tracking Issueが作成され、対象main commit、target一覧、material premise表、子Issue依存が登録されている。
- `RawAmbientRestrictionSystem.toPresheaf`、`RingedAATSite.ofMathlibSheafification`、
  `RingedAATSite.structureSheaf`、`RingedAATSite.canonical`、
  `generateRingedAATSite`とそのcharacterization theoremがmerged済みである。
- 同Issueが、上記宣言を提供するmerged commitへのdependencyを持つ。
- `Formal/AG/LawAlgebra/StructureSheaf.lean`のsection objectとrestriction morphismを
  `CommRingCat`として利用できることが、対象main commit上のfocused Lean checkで確認されている。

いずれかが欠ける間、このPRDは実行しない。

## Statement Design

この節は本PRDのstatement contract正本である。実装開始後にtarget名、仮定、結論、量化対象、
参照definitionのsignatureを変更しない。実装状態は記録しない。実装後は
`Formal/AG/StatementContractsStandardArchitectureScheme.lean`が、ここに固定したsignatureと
実装宣言を`example : <fixed type> := <implementation>`の形で直接突合する。
別のMarkdown contractは作成しない。

以下のLean blockは`namespace AAT.AG.LawAlgebra`、
`open CategoryTheory CategoryTheory.Limits Opposite`、
`open AlgebraicGeometry`、`open scoped AlgebraicGeometry`、
`universe u v w x`の下で読む。
各blockでは次を共通parameterとする。

```lean
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable (raw : RawAmbientRestrictionSystem S k)
variable [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
```

### SD0 — 同一ringed siteからのsection ringとaffine Spec

standard architecture schemeの全chartは、同一の`raw`、同一の`S`、同一のMathlib sheafificationから
得る。独立に選んだcoordinate ring、structure sheaf、restriction mapを再結合しない。

```lean
noncomputable def RawAmbientRestrictionSystem.toRingedSite
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    RingedAATSite S k :=
  RingedAATSite.ofMathlibSheafification raw.toPresheaf

noncomputable abbrev SheafifiedSectionRing
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) : CommRingCat :=
  (raw.toRingedSite.structureSheaf.val.obj (op W)).right

noncomputable def sheafifiedSectionAlgebraMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    k →+* SheafifiedSectionRing raw W :=
  (raw.toRingedSite.structureSheaf.val.obj (op W)).hom.hom.comp
    ULift.ringEquiv.symm.toRingHom

noncomputable instance SheafifiedSectionRing.instAlgebra
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    Algebra k (SheafifiedSectionRing raw W) :=
  (sheafifiedSectionAlgebraMap raw W).toAlgebra

noncomputable def sheafifiedRestriction
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    SheafifiedSectionRing raw V ⟶ SheafifiedSectionRing raw W :=
  (raw.toRingedSite.structureSheaf.val.map f.op).right

noncomputable def sheafifiedRestrictionAlgHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    SheafifiedSectionRing raw V →ₐ[k] SheafifiedSectionRing raw W

noncomputable def sheafificationUnitAlgHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    raw.rawAlgebra W →ₐ[k] SheafifiedSectionRing raw W

noncomputable abbrev architectureChartSpec
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Scheme.Spec.obj
    (op (SheafifiedSectionRing raw W))

noncomputable def architectureChartRestriction
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    architectureChartSpec raw W ⟶ architectureChartSpec raw V :=
  AlgebraicGeometry.Scheme.Spec.map (sheafifiedRestriction raw f).op
```

次をfixed theoremとする。

```lean
@[simp] theorem RawAmbientRestrictionSystem.toRingedSite_raw :
    (raw.toRingedSite).raw = raw.toPresheaf

theorem SheafifiedSectionRing_eq_structureSheaf
    (W : S.category) :
    SheafifiedSectionRing raw W =
      (raw.toRingedSite.structureSheaf.val.obj (op W)).right

@[simp] theorem SheafifiedSectionRing_algebraMap
    (W : S.category) :
    algebraMap k (SheafifiedSectionRing raw W) =
      sheafifiedSectionAlgebraMap raw W

theorem sheafifiedRestriction_eq_structureSheafMap
    {W V : S.category} (f : W ⟶ V) :
    sheafifiedRestriction raw f =
      (raw.toRingedSite.structureSheaf.val.map f.op).right

theorem sheafifiedRestrictionAlgHom_toRingHom
    {W V : S.category} (f : W ⟶ V) :
    (sheafifiedRestrictionAlgHom raw f).toRingHom =
      (sheafifiedRestriction raw f).hom

theorem sheafificationUnitAlgHom_toRingHom
    (W : S.category) :
    (sheafificationUnitAlgHom raw W).toRingHom =
      (raw.toRingedSite.canonical.app (op W)).right.hom

theorem architectureChartSpec_eq_Spec
    (W : S.category) :
    architectureChartSpec raw W =
      AlgebraicGeometry.Scheme.Spec.obj
        (op (SheafifiedSectionRing raw W))

theorem architectureChartRestriction_eq_SpecMap
    {W V : S.category} (f : W ⟶ V) :
    architectureChartRestriction raw f =
      AlgebraicGeometry.Scheme.Spec.map
        (sheafifiedRestriction raw f).op

@[simp] theorem sheafifiedRestriction_id
    (W : S.category) :
    sheafifiedRestriction raw (𝟙 W) = 𝟙 (SheafifiedSectionRing raw W)

@[simp] theorem sheafifiedRestriction_comp
    {W V Z : S.category} (f : W ⟶ V) (g : V ⟶ Z) :
    sheafifiedRestriction raw (f ≫ g) =
      sheafifiedRestriction raw g ≫ sheafifiedRestriction raw f

@[simp] theorem architectureChartRestriction_id
    (W : S.category) :
    architectureChartRestriction raw (𝟙 W) = 𝟙 (architectureChartSpec raw W)

@[simp] theorem architectureChartRestriction_comp
    {W V Z : S.category} (f : W ⟶ V) (g : V ⟶ Z) :
    architectureChartRestriction raw (f ≫ g) =
      architectureChartRestriction raw f ≫ architectureChartRestriction raw g

noncomputable def architectureChartFunctor :
    S.category ⥤ AlgebraicGeometry.Scheme

@[simp] theorem architectureChartFunctor_obj
    (W : S.category) :
    (architectureChartFunctor raw).obj W = architectureChartSpec raw W

@[simp] theorem architectureChartFunctor_map
    {W V : S.category} (f : W ⟶ V) :
    (architectureChartFunctor raw).map f =
      architectureChartRestriction raw f

noncomputable def architectureChartIso
    {W V : S.category} (e : W ≅ V) :
    architectureChartSpec raw W ≅ architectureChartSpec raw V :=
  (architectureChartFunctor raw).mapIso e

@[simp] theorem architectureChartIso_hom
    {W V : S.category} (e : W ≅ V) :
    (architectureChartIso raw e).hom =
      architectureChartRestriction raw e.hom

@[simp] theorem architectureChartIso_inv
    {W V : S.category} (e : W ≅ V) :
    (architectureChartIso raw e).inv =
      architectureChartRestriction raw e.inv

theorem architectureChartRestriction_appTop
    {W V : S.category} (f : W ⟶ V) :
    (architectureChartRestriction raw f).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw W)).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw V)).hom ≫
        sheafifiedRestriction raw f
```

`sheafifiedRestriction_id`と`sheafifiedRestriction_comp`はstructure sheaf functorの
`map_id` / `map_comp`から証明する。`architectureChartRestriction_appTop`は
Mathlib `Scheme.ΓSpecIso_naturality`から証明し、ring restrictionとSpec transitionを
別のcompatibility fieldで再入力しない。
`architectureChartFunctor`はobject / mapの別保存を防ぎ、context isoがactual Scheme isoへ
送られることを`architectureChartIso`として公開する。
`sheafifiedSectionAlgebraMap`は`AATCommAlgCat k = Under (CommRingCat.of (ULift k))`の
structure mapを`ULift.ringEquiv.symm`に沿って`k`-algebra mapとして読む。
`sheafifiedRestrictionAlgHom`と`sheafificationUnitAlgHom`は、それぞれactual Under-morphismの
underlying ring homに固定し、SD7で任意のalgebra structureを再選択しない。

### SD1 — global reading decoration

このPRDで構成するのは、数学本文の`D_X`のうち、context、typed coordinate family、selected law-universe provenance、
signature reading、interpretationに対応するreading componentである。law-generated idealは保持しない。
full decorationは後続のclosed-equational law geometryが、このreading componentと同じ`raw` / `S`上に
actual ideal sheafを構成して完成させる。
ここで`global`は、選択したbase contextのsection ringから`Γ(X, ⊤)`へのinterpretationを指す。
各affine chartのlocal readingは`ofContext`で構成し、chart mapに沿うpreservation equationでglobal
readingへ接続する。任意のopen setで独立にreading dataを再入力する構造は作らない。

```lean
structure AATReadingDecoration
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : AlgebraicGeometry.Scheme) where
  context : S.category
  interpretation :
    SheafifiedSectionRing raw context ⟶ Γ(X, ⊤)

def AATReadingDecoration.coordinateFamily
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    CoordinateFamily D.context.ctx :=
  raw.coordFamily D.context

def AATReadingDecoration.lawUniverse
    {X : AlgebraicGeometry.Scheme}
    (_D : AATReadingDecoration raw X) : LawUniverse U :=
  S.lawUniverse

def AATReadingDecoration.signature
    {X : AlgebraicGeometry.Scheme}
    (_D : AATReadingDecoration raw X) : ArchitectureSignature U :=
  S.signature

noncomputable def AATReadingDecoration.coefficientMap
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    k →+* Γ(X, ⊤) :=
  D.interpretation.hom.comp
    (sheafifiedSectionAlgebraMap raw D.context)

noncomputable def AATReadingDecoration.coordinateSection
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X)
    (c : D.coordinateFamily.CoordX) : Γ(X, ⊤) :=
  D.interpretation
    ((raw.toRingedSite.canonical.app (op D.context)).right
      ((raw.relationFamily D.context).quotientMap (MvPolynomial.X c)))

noncomputable def AATReadingDecoration.pullback
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    AATReadingDecoration raw X where
  context := D.context
  interpretation := D.interpretation ≫ f.appTop

def AATReadingDecoration.Preserves
    {X Y : AlgebraicGeometry.Scheme}
    (D_X : AATReadingDecoration raw X) (f : X ⟶ Y)
    (D_Y : AATReadingDecoration raw Y) : Prop :=
  ∃ h : D_X.context ⟶ D_Y.context,
    sheafifiedRestriction raw h ≫ D_X.interpretation =
      D_Y.interpretation ≫ f.appTop
```

次をfixed theoremとする。

```lean
@[ext] theorem AATReadingDecoration.ext
    {X : AlgebraicGeometry.Scheme}
    (D E : AATReadingDecoration raw X)
    (hcontext : D.context = E.context)
    (hinterpretation : HEq D.interpretation E.interpretation) : D = E

@[simp] theorem AATReadingDecoration.coordinateFamily_eq
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.coordinateFamily = raw.coordFamily D.context

@[simp] theorem AATReadingDecoration.lawUniverse_eq
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.lawUniverse = S.lawUniverse

@[simp] theorem AATReadingDecoration.signature_eq
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.signature = S.signature

@[simp] theorem AATReadingDecoration.coefficientMap_eq
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.coefficientMap raw =
      D.interpretation.hom.comp
        (sheafifiedSectionAlgebraMap raw D.context)

@[simp] theorem AATReadingDecoration.coordinateSection_apply
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X)
    (c : D.coordinateFamily.CoordX) :
    D.coordinateSection raw c =
      D.interpretation
        ((raw.toRingedSite.canonical.app (op D.context)).right
          ((raw.relationFamily D.context).quotientMap (MvPolynomial.X c)))

@[simp] theorem AATReadingDecoration.pullback_context
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    (D.pullback raw f).context = D.context

@[simp] theorem AATReadingDecoration.pullback_interpretation
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    (D.pullback raw f).interpretation = D.interpretation ≫ f.appTop

@[simp] theorem AATReadingDecoration.pullback_coefficientMap
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    (D.pullback raw f).coefficientMap raw =
      f.appTop.hom.comp (D.coefficientMap raw)

@[simp] theorem AATReadingDecoration.pullback_id
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.pullback raw (𝟙 X) = D

@[simp] theorem AATReadingDecoration.pullback_comp
    {X Y Z : AlgebraicGeometry.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (D : AATReadingDecoration raw Z) :
    D.pullback raw (f ≫ g) =
      (D.pullback raw g).pullback raw f

@[simp] theorem AATReadingDecoration.coordinateSection_pullback
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y)
    (c : D.coordinateFamily.CoordX) :
    (D.pullback raw f).coordinateSection raw c =
      f.appTop (D.coordinateSection raw c)

theorem AATReadingDecoration.preserves_id
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.Preserves raw (𝟙 X) D

theorem AATReadingDecoration.preserves_comp
    {X Y Z : AlgebraicGeometry.Scheme}
    {D_X : AATReadingDecoration raw X}
    {D_Y : AATReadingDecoration raw Y}
    {D_Z : AATReadingDecoration raw Z}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : D_X.Preserves raw f D_Y)
    (hg : D_Y.Preserves raw g D_Z) :
    D_X.Preserves raw (f ≫ g) D_Z

theorem AATReadingDecoration.Preserves.coefficientMap
    {X Y : AlgebraicGeometry.Scheme}
    {D_X : AATReadingDecoration raw X}
    {D_Y : AATReadingDecoration raw Y}
    {f : X ⟶ Y}
    (hf : D_X.Preserves raw f D_Y) :
    D_X.coefficientMap raw =
      f.appTop.hom.comp (D_Y.coefficientMap raw)

noncomputable def AATReadingDecoration.ofContext
    (W : S.category) :
    AATReadingDecoration raw (architectureChartSpec raw W) where
  context := W
  interpretation :=
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing raw W)).inv

@[simp] theorem AATReadingDecoration.ofContext_context
    (W : S.category) :
    (AATReadingDecoration.ofContext raw W).context = W

@[simp] theorem AATReadingDecoration.ofContext_interpretation
    (W : S.category) :
    (AATReadingDecoration.ofContext raw W).interpretation =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing raw W)).inv
```

`Preserves`は自由なcompatibility propositionではない。context morphismが誘導するactual
sheafified restrictionと、scheme morphismの`appTop`が作る可換式である。
identityとcompositionはsite category、structure sheaf functor、Mathlib scheme morphismの
functorialityから証明する。`coordinateSection_apply`により、typed variable、structural quotient、
sheafification unit、interpretationの四段を実装が省略できないようにする。
`coefficientMap`はcanonical section-algebra mapとinterpretationの合成であり、
`Preserves.coefficientMap`によりdecorated morphismが同じcoefficient readingに沿うことも導出する。

### SD2 — actual affine chart

chart domainはdefinitionally`Spec(O_X^U(W_i))`であり、別のaffine carrierや`specIso`を格納しない。

```lean
structure ArchitectureAffineChart
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X) where
  context : S.category
  contextHom : context ⟶ D.context
  map : architectureChartSpec raw context ⟶ X

structure IsArchitectureAffineChart
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) : Prop where
  isOpenImmersion : AlgebraicGeometry.IsOpenImmersion C.map
  interpretation_compatible :
    sheafifiedRestriction raw C.contextHom =
      D.interpretation ≫ C.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw C.context)).hom
```

次をfixed APIとする。

```lean
def ArchitectureAffineChart.domain
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) : AlgebraicGeometry.Scheme :=
  architectureChartSpec raw C.context

def ArchitectureAffineChart.domainLocallyRingedSpace
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) :
    LocallyRingedSpace :=
  C.domain.toLocallyRingedSpace

theorem ArchitectureAffineChart.domain_isAffine
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) :
    AlgebraicGeometry.IsAffine C.domain := by
  infer_instance

@[simp] theorem ArchitectureAffineChart.domain_eq
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) :
    C.domain = architectureChartSpec raw C.context

def ArchitectureAffineChart.image
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D)
    (hC : IsArchitectureAffineChart raw C) : X.Opens := by
  letI : AlgebraicGeometry.IsOpenImmersion C.map := hC.isOpenImmersion
  exact C.map.opensRange

noncomputable def ArchitectureAffineChart.identity
    (W : S.category) :
    ArchitectureAffineChart raw
      (architectureChartSpec raw W)
      (AATReadingDecoration.ofContext raw W) where
  context := W
  contextHom := 𝟙 W
  map := 𝟙 (architectureChartSpec raw W)

@[simp] theorem ArchitectureAffineChart.identity_context
    (W : S.category) :
    (ArchitectureAffineChart.identity raw W).context = W

@[simp] theorem ArchitectureAffineChart.identity_contextHom
    (W : S.category) :
    (ArchitectureAffineChart.identity raw W).contextHom = 𝟙 W

@[simp] theorem ArchitectureAffineChart.identity_map
    (W : S.category) :
    (ArchitectureAffineChart.identity raw W).map =
      𝟙 (architectureChartSpec raw W)

theorem ArchitectureAffineChart.identity_isArchitectureAffineChart
    (W : S.category) :
    IsArchitectureAffineChart raw
      (ArchitectureAffineChart.identity raw W)

theorem ArchitectureAffineChart.localDecoration_preserves
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D)
    (hC : IsArchitectureAffineChart raw C) :
    (AATReadingDecoration.ofContext raw C.context).Preserves raw C.map D
```

`identity_isArchitectureAffineChart`はMathlib identity open immersion、
`sheafifiedRestriction_id`、`Scheme.Hom.id_appTop`、`ΓSpecIso.inv_hom_id`から証明する。
`localDecoration_preserves`は`C.contextHom`をwitnessとし、
`interpretation_compatible`を`ΓSpecIso`の逆射で移して証明する。
chart成立条件をconstructor fieldへ埋めず、`IsArchitectureAffineChart`として分離する。

### SD3 — actual affine atlas、pair overlap、triple coherence

atlas data、atlas成立proof、overlap comparison data、comparison成立proofを四つに分ける。
actual overlapはchart mapsのMathlib pullbackであり、別のoverlap schemeを選択しない。

```lean
structure ArchitectureAffineAtlas
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X) where
  Index : Type u
  chart : Index → ArchitectureAffineChart raw X D

structure IsArchitectureAffineAtlas
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D) : Prop where
  chart_valid : ∀ i, IsArchitectureAffineChart raw (atlas.chart i)
  covers : ∀ x : X, ∃ i y, (atlas.chart i).map y = x
```

pair contextは`S.overlap`からdefinitionで生成する。

```lean
noncomputable def ArchitectureAffineAtlas.pairContext
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) : S.category :=
  Site.ContextCategoryObject.of S.contextPreorder
    (S.overlap.overlap D.context.ctx
      (atlas.chart i).context.ctx (atlas.chart j).context.ctx)

noncomputable def ArchitectureAffineAtlas.pairToLeft
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairContext raw i j ⟶ (atlas.chart i).context

noncomputable def ArchitectureAffineAtlas.pairToRight
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairContext raw i j ⟶ (atlas.chart j).context

noncomputable def ArchitectureAffineAtlas.pairToBase
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairContext raw i j ⟶ D.context

noncomputable def ArchitectureAffineAtlas.selfToPair
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    (atlas.chart i).context ⟶ atlas.pairContext raw i i

noncomputable def ArchitectureAffineAtlas.selfPairContextIso
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    atlas.pairContext raw i i ≅ (atlas.chart i).context

noncomputable def ArchitectureAffineAtlas.tripleContext
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) : S.category :=
  Site.ContextCategoryObject.of S.contextPreorder
    (S.overlap.overlap D.context.ctx
      (atlas.pairContext raw i j).ctx
      (atlas.pairContext raw j l).ctx)

noncomputable def ArchitectureAffineAtlas.tripleToFirstPair
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ atlas.pairContext raw i j

noncomputable def ArchitectureAffineAtlas.tripleToSecondPair
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ atlas.pairContext raw j l

noncomputable def ArchitectureAffineAtlas.tripleToLeft
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ (atlas.chart i).context

noncomputable def ArchitectureAffineAtlas.tripleToMiddle
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ (atlas.chart j).context

noncomputable def ArchitectureAffineAtlas.tripleToRight
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ (atlas.chart l).context

@[simp] theorem ArchitectureAffineAtlas.pairContext_ctx
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    (atlas.pairContext raw i j).ctx =
      S.overlap.overlap D.context.ctx
        (atlas.chart i).context.ctx (atlas.chart j).context.ctx

@[simp] theorem ArchitectureAffineAtlas.tripleContext_ctx
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    (atlas.tripleContext raw i j l).ctx =
      S.overlap.overlap D.context.ctx
        (atlas.pairContext raw i j).ctx
        (atlas.pairContext raw j l).ctx

@[simp] theorem ArchitectureAffineAtlas.pairToBase_eq_left
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairToBase raw i j =
      atlas.pairToLeft raw i j ≫ (atlas.chart i).contextHom

theorem ArchitectureAffineAtlas.pairToBase_eq_right
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairToBase raw i j =
      atlas.pairToRight raw i j ≫ (atlas.chart j).contextHom

@[simp] theorem ArchitectureAffineAtlas.selfPairContextIso_hom
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    (atlas.selfPairContextIso raw i).hom = atlas.pairToLeft raw i i

@[simp] theorem ArchitectureAffineAtlas.selfPairContextIso_inv
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    (atlas.selfPairContextIso raw i).inv = atlas.selfToPair raw i

@[simp] theorem ArchitectureAffineAtlas.tripleToLeft_eq
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToLeft raw i j l =
      atlas.tripleToFirstPair raw i j l ≫ atlas.pairToLeft raw i j

@[simp] theorem ArchitectureAffineAtlas.tripleToMiddle_eq_first
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToMiddle raw i j l =
      atlas.tripleToFirstPair raw i j l ≫ atlas.pairToRight raw i j

theorem ArchitectureAffineAtlas.tripleToMiddle_eq_second
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToMiddle raw i j l =
      atlas.tripleToSecondPair raw i j l ≫ atlas.pairToLeft raw j l

@[simp] theorem ArchitectureAffineAtlas.tripleToRight_eq
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToRight raw i j l =
      atlas.tripleToSecondPair raw i j l ≫ atlas.pairToRight raw j l

noncomputable abbrev ArchitectureAffineAtlas.actualOverlap
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) : AlgebraicGeometry.Scheme :=
  pullback (atlas.chart i).map (atlas.chart j).map

noncomputable def ArchitectureAffineAtlas.actualOverlapToUnderlying
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.actualOverlap raw i j ⟶ X :=
  pullback.fst (atlas.chart i).map (atlas.chart j).map ≫
    (atlas.chart i).map

noncomputable abbrev ArchitectureAffineAtlas.actualTripleOverlap
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) : AlgebraicGeometry.Scheme :=
  pullback (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map

noncomputable def ArchitectureAffineAtlas.actualTripleToLeft
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l ⟶
      architectureChartSpec raw (atlas.chart i).context :=
  pullback.fst (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map ≫
    pullback.fst (atlas.chart i).map (atlas.chart j).map

noncomputable def ArchitectureAffineAtlas.actualTripleToMiddle
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l ⟶
      architectureChartSpec raw (atlas.chart j).context :=
  pullback.fst (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map ≫
    pullback.snd (atlas.chart i).map (atlas.chart j).map

noncomputable def ArchitectureAffineAtlas.actualTripleToRight
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l ⟶
      architectureChartSpec raw (atlas.chart l).context :=
  pullback.snd (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map

theorem ArchitectureAffineAtlas.actualOverlap_eq_pullback
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.actualOverlap raw i j =
      pullback (atlas.chart i).map (atlas.chart j).map

theorem ArchitectureAffineAtlas.actualTripleOverlap_eq_pullback
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l =
      pullback (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map

theorem ArchitectureAffineAtlas.actualOverlapToUnderlying_eq_left
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.actualOverlapToUnderlying raw i j =
      pullback.fst (atlas.chart i).map (atlas.chart j).map ≫
        (atlas.chart i).map

theorem ArchitectureAffineAtlas.actualTripleToLeft_eq
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToLeft raw i j l =
      pullback.fst (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map ≫
        pullback.fst (atlas.chart i).map (atlas.chart j).map

theorem ArchitectureAffineAtlas.actualTripleToMiddle_eq
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToMiddle raw i j l =
      pullback.fst (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map ≫
        pullback.snd (atlas.chart i).map (atlas.chart j).map

theorem ArchitectureAffineAtlas.actualTripleToRight_eq
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToRight raw i j l =
      pullback.snd (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map

structure ArchitectureOverlapPresentation
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D) where
  comparison : ∀ i j,
    architectureChartSpec raw (atlas.pairContext raw i j) ≅
      atlas.actualOverlap raw i j

structure IsArchitectureOverlapPresentation
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (P : ArchitectureOverlapPresentation raw atlas) : Prop where
  comparison_fst : ∀ i j,
    (P.comparison i j).hom ≫
        pullback.fst (atlas.chart i).map (atlas.chart j).map =
      architectureChartRestriction raw (atlas.pairToLeft raw i j)
  comparison_snd : ∀ i j,
    (P.comparison i j).hom ≫
        pullback.snd (atlas.chart i).map (atlas.chart j).map =
      architectureChartRestriction raw (atlas.pairToRight raw i j)
```

`pairToLeft`、`pairToRight`、`pairToBase`は`S.overlap.left` / `right` / `base`、
triple helperは二つのpair contextに対する`S.overlap`から構成する。
`selfToPair`は同じ`contextHom`を両辺に使う`S.overlap.lift`から構成し、
context categoryのhom subsingleton性で`selfPairContextIso`を得る。
`pairToBase_eq_left`と`tripleToMiddle_eq_first`だけをcanonicalな`@[simp]`正規形とする。
`pairToBase_eq_right`と`tripleToMiddle_eq_second`はcontext categoryのhom subsingleton性から得る
二経路のcoherence theoremとして公開し、`@[simp]`を付けない。同じ左辺を異なる右辺へ簡約する
複数のsimp lemmaを作らない。
したがってtriple coherenceは`IsArchitectureOverlapPresentation`の追加入力ではなく、二つのpair
comparisonとfunctorialityから導出する。arbitrary context、arbitrary scheme map、arbitrary equalityを
入力するhelperは置かない。

次をfixed theoremとする。

```lean
noncomputable def ArchitectureAffineAtlas.toAffineOpenCover
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas) :
    X.AffineOpenCover

@[simp] theorem ArchitectureAffineAtlas.toAffineOpenCover_X
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas)
    (i : atlas.Index) :
    (atlas.toAffineOpenCover raw h).X i =
      SheafifiedSectionRing raw (atlas.chart i).context

@[simp] theorem ArchitectureAffineAtlas.toAffineOpenCover_f
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas)
    (i : atlas.Index) :
    (atlas.toAffineOpenCover raw h).f i = (atlas.chart i).map

theorem ArchitectureAffineAtlas.jointlyCovers
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas) :
    ⨆ i, ((atlas.toAffineOpenCover raw h).f i).opensRange = ⊤

theorem ArchitectureAffineAtlas.overlap_left_isOpenImmersion
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (h : IsArchitectureAffineAtlas raw atlas)
    (i j : atlas.Index) :
    AlgebraicGeometry.IsOpenImmersion
      (pullback.fst (atlas.chart i).map (atlas.chart j).map)

theorem ArchitectureAffineAtlas.overlap_right_isOpenImmersion
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (h : IsArchitectureAffineAtlas raw atlas)
    (i j : atlas.Index) :
    AlgebraicGeometry.IsOpenImmersion
      (pullback.snd (atlas.chart i).map (atlas.chart j).map)

theorem ArchitectureAffineAtlas.actualOverlapToUnderlying_eq_right
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.actualOverlapToUnderlying raw i j =
      pullback.snd (atlas.chart i).map (atlas.chart j).map ≫
        (atlas.chart j).map

theorem ArchitectureAffineAtlas.overlap_commutes
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (P : ArchitectureOverlapPresentation raw atlas)
    (hP : IsArchitectureOverlapPresentation raw P)
    (i j : atlas.Index) :
    architectureChartRestriction raw (atlas.pairToLeft raw i j) ≫
        (atlas.chart i).map =
      architectureChartRestriction raw (atlas.pairToRight raw i j) ≫
        (atlas.chart j).map

theorem ArchitectureAffineAtlas.overlap_toLeft_preserves
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    (AATReadingDecoration.ofContext raw (atlas.pairContext raw i j)).Preserves raw
      (architectureChartRestriction raw (atlas.pairToLeft raw i j))
      (AATReadingDecoration.ofContext raw (atlas.chart i).context)

theorem ArchitectureAffineAtlas.overlap_toRight_preserves
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    (AATReadingDecoration.ofContext raw (atlas.pairContext raw i j)).Preserves raw
      (architectureChartRestriction raw (atlas.pairToRight raw i j))
      (AATReadingDecoration.ofContext raw (atlas.chart j).context)

theorem ArchitectureAffineAtlas.decoration_overlap
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    sheafifiedRestriction raw
        (atlas.pairToLeft raw i j ≫ (atlas.chart i).contextHom) =
      sheafifiedRestriction raw
        (atlas.pairToRight raw i j ≫ (atlas.chart j).contextHom)

theorem ArchitectureAffineAtlas.actualTriple_cocycle
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToLeft raw i j l ≫ (atlas.chart i).map =
      atlas.actualTripleToMiddle raw i j l ≫ (atlas.chart j).map ∧
    atlas.actualTripleToMiddle raw i j l ≫ (atlas.chart j).map =
      atlas.actualTripleToRight raw i j l ≫ (atlas.chart l).map

theorem ArchitectureAffineAtlas.contextTriple_cocycle
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (P : ArchitectureOverlapPresentation raw atlas)
    (hP : IsArchitectureOverlapPresentation raw P)
    (i j l : atlas.Index) :
    architectureChartRestriction raw
          (atlas.tripleToLeft raw i j l) ≫ (atlas.chart i).map =
      architectureChartRestriction raw
          (atlas.tripleToMiddle raw i j l) ≫ (atlas.chart j).map ∧
    architectureChartRestriction raw
          (atlas.tripleToMiddle raw i j l) ≫ (atlas.chart j).map =
      architectureChartRestriction raw
          (atlas.tripleToRight raw i j l) ≫ (atlas.chart l).map
```

`jointlyCovers`は`AffineOpenCover.openCover`と`OpenCover.iSup_opensRange`へ接続する。
`actualOverlapToUnderlying_eq_right`はinner pullbackの`pullback.condition`そのものである。
`overlap_commutes`は`pullback.condition`と`comparison_fst` / `comparison_snd`から証明する。
`overlap_toLeft_preserves` / `overlap_toRight_preserves`は
`ΓSpecIso_inv_naturality`から証明する。
`decoration_overlap`はcontext categoryのsubsingleton homとstructure sheaf functorialityから証明する。
`actualTriple_cocycle`はiterated Mathlib pullbackのconditionから証明する。
`contextTriple_cocycle`は二つの`overlap_commutes`をselected triple contextからprecomposeして証明する。
両statementともactual Scheme mapsの等式であり、`cocycle : Prop`を自由に選んで代用しない。

### SD4 — standard architecture scheme core

```lean
structure StandardArchitectureScheme
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] where
  underlying : AlgebraicGeometry.Scheme
  decoration : AATReadingDecoration raw underlying
  atlas : ArchitectureAffineAtlas raw underlying decoration
  atlasValid : IsArchitectureAffineAtlas raw atlas
  overlaps : ArchitectureOverlapPresentation raw atlas
  overlapsValid : IsArchitectureOverlapPresentation raw overlaps
```

次をfixed APIとする。

```lean
noncomputable def StandardArchitectureScheme.affineOpenCover
    (X : StandardArchitectureScheme raw) : X.underlying.AffineOpenCover :=
  X.atlas.toAffineOpenCover raw X.atlasValid

theorem StandardArchitectureScheme.chart_isOpenImmersion
    (X : StandardArchitectureScheme raw) (i : X.atlas.Index) :
    AlgebraicGeometry.IsOpenImmersion (X.atlas.chart i).map

theorem StandardArchitectureScheme.chart_jointlyCovers
    (X : StandardArchitectureScheme raw) :
    ⨆ i, ((X.affineOpenCover raw).f i).opensRange = ⊤

theorem StandardArchitectureScheme.chart_sectionRing
    (X : StandardArchitectureScheme raw) (i : X.atlas.Index) :
    (X.affineOpenCover raw).X i =
      SheafifiedSectionRing raw (X.atlas.chart i).context

theorem StandardArchitectureScheme.overlap_is_actual_pullback
    (X : StandardArchitectureScheme raw) (i j : X.atlas.Index) :
    architectureChartSpec raw (X.atlas.pairContext raw i j) ≅
      pullback (X.atlas.chart i).map (X.atlas.chart j).map :=
  X.overlaps.comparison i j

@[ext] theorem StandardArchitectureScheme.ext
    (X Y : StandardArchitectureScheme raw)
    (hunderlying : X.underlying = Y.underlying)
    (hdecoration : HEq X.decoration Y.decoration)
    (hatlas : HEq X.atlas Y.atlas)
    (hoverlaps : HEq X.overlaps Y.overlaps) : X = Y
```

`StandardArchitectureScheme`は本文 定義9.3 / Appendix A.5のstandard geometry coreである。
full law-equational decorationはこのcoreと同じ`underlying`、`raw`、`S`上に
law-generated ideal sheafを追加した後続対象として扱う。このPRDのcompletion labelは
`reading-decorated standard architecture scheme core`とする。

### SD5 — decorated morphismとfaithful forgetful functor

atlasはpresentation dataであり、morphismにchart index mapを要求しない。
morphismはunderlying scheme morphismと、SD1のactual preservation equationだけを持つ。

```lean
structure StandardArchitectureScheme.Hom
    (X Y : StandardArchitectureScheme raw) where
  base : X.underlying ⟶ Y.underlying
  preserves : X.decoration.Preserves raw base Y.decoration

namespace StandardArchitectureScheme.Hom

def id (X : StandardArchitectureScheme raw) : Hom X X

def comp {X Y Z : StandardArchitectureScheme raw}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z

@[simp] theorem id_base (X : StandardArchitectureScheme raw) :
    (id X).base = 𝟙 X.underlying

@[simp] theorem comp_base {X Y Z : StandardArchitectureScheme raw}
    (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).base = f.base ≫ g.base

@[ext] theorem ext {X Y : StandardArchitectureScheme raw}
    (f g : Hom X Y) (hbase : f.base = g.base) : f = g

end StandardArchitectureScheme.Hom

instance StandardArchitectureScheme.category :
    Category (StandardArchitectureScheme raw)

def StandardArchitectureScheme.forget :
    StandardArchitectureScheme raw ⥤ AlgebraicGeometry.Scheme where
  obj X := X.underlying
  map f := f.base

instance StandardArchitectureScheme.forget_faithful :
    Faithful (StandardArchitectureScheme.forget raw)

@[simp] theorem StandardArchitectureScheme.forget_obj
    (X : StandardArchitectureScheme raw) :
    (StandardArchitectureScheme.forget raw).obj X = X.underlying

@[simp] theorem StandardArchitectureScheme.forget_map
    {X Y : StandardArchitectureScheme raw}
    (f : X ⟶ Y) :
    (StandardArchitectureScheme.forget raw).map f = f.base
```

`Hom.ext`はunderlying morphism equalityとproof irrelevanceから証明する。
sourceとtargetは同じ`raw` / `S`上にあるため、law universeとsignatureはdefinitionally共通であり、
typed coordinate restrictionは`Preserves`のcontext morphismから`sheafifiedRestriction`として決まる。
coefficient mapの保存は`Preserves.coefficientMap`の帰結であり、Hom fieldへ重複保存しない。
追加のcomparison map、chart-index action、category-law fieldをHomへ入れない。

### SD6 — constructors

```lean
noncomputable def StandardArchitectureScheme.ofPresentation
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X)
    (atlas : ArchitectureAffineAtlas raw X D)
    (hatlas : IsArchitectureAffineAtlas raw atlas)
    (overlaps : ArchitectureOverlapPresentation raw atlas)
    (hoverlaps : IsArchitectureOverlapPresentation raw overlaps) :
    StandardArchitectureScheme raw

@[simp] theorem StandardArchitectureScheme.ofPresentation_underlying
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X)
    (atlas : ArchitectureAffineAtlas raw X D)
    (hatlas : IsArchitectureAffineAtlas raw atlas)
    (overlaps : ArchitectureOverlapPresentation raw atlas)
    (hoverlaps : IsArchitectureOverlapPresentation raw overlaps) :
    (StandardArchitectureScheme.ofPresentation raw X D atlas hatlas
      overlaps hoverlaps).underlying = X

@[simp] theorem StandardArchitectureScheme.ofPresentation_decoration
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X)
    (atlas : ArchitectureAffineAtlas raw X D)
    (hatlas : IsArchitectureAffineAtlas raw atlas)
    (overlaps : ArchitectureOverlapPresentation raw atlas)
    (hoverlaps : IsArchitectureOverlapPresentation raw overlaps) :
    (StandardArchitectureScheme.ofPresentation raw X D atlas hatlas
      overlaps hoverlaps).decoration = D

@[simp] theorem StandardArchitectureScheme.ofPresentation_atlas
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X)
    (atlas : ArchitectureAffineAtlas raw X D)
    (hatlas : IsArchitectureAffineAtlas raw atlas)
    (overlaps : ArchitectureOverlapPresentation raw atlas)
    (hoverlaps : IsArchitectureOverlapPresentation raw overlaps) :
    (StandardArchitectureScheme.ofPresentation raw X D atlas hatlas
      overlaps hoverlaps).atlas = atlas

@[simp] theorem StandardArchitectureScheme.ofPresentation_overlaps
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X)
    (atlas : ArchitectureAffineAtlas raw X D)
    (hatlas : IsArchitectureAffineAtlas raw atlas)
    (overlaps : ArchitectureOverlapPresentation raw atlas)
    (hoverlaps : IsArchitectureOverlapPresentation raw overlaps) :
    (StandardArchitectureScheme.ofPresentation raw X D atlas hatlas
      overlaps hoverlaps).overlaps = overlaps

noncomputable def StandardArchitectureScheme.singleAffine
    (W : S.category) : StandardArchitectureScheme raw

@[simp] theorem StandardArchitectureScheme.singleAffine_underlying
    (W : S.category) :
    (StandardArchitectureScheme.singleAffine raw W).underlying =
      architectureChartSpec raw W

@[simp] theorem StandardArchitectureScheme.singleAffine_decoration
    (W : S.category) :
    (StandardArchitectureScheme.singleAffine raw W).decoration =
      AATReadingDecoration.ofContext raw W

theorem StandardArchitectureScheme.singleAffine_index_subsingleton
    (W : S.category) :
    Subsingleton (StandardArchitectureScheme.singleAffine raw W).atlas.Index

def StandardArchitectureScheme.singleAffineIndex
    (W : S.category) :
    (StandardArchitectureScheme.singleAffine raw W).atlas.Index

@[simp] theorem StandardArchitectureScheme.singleAffine_index_eq
    (W : S.category)
    (i : (StandardArchitectureScheme.singleAffine raw W).atlas.Index) :
    i = StandardArchitectureScheme.singleAffineIndex raw W

theorem StandardArchitectureScheme.singleAffine_chart_map
    (W : S.category)
    (i : (StandardArchitectureScheme.singleAffine raw W).atlas.Index) :
    ((StandardArchitectureScheme.singleAffine raw W).atlas.chart i).map =
      𝟙 (architectureChartSpec raw W)
```

`singleAffine`は`ArchitectureAffineChart.identity`、identity cover、
`selfPairContextIso`を`architectureChartIso`でScheme isoへ送った射、およびMathlibの
identity-pullback limit uniquenessからatlas validityとoverlap validityを放電する。
callerにopen immersion、coverage、overlap、cocycleのproofを要求しない。
`singleAffineIndex`と`singleAffine_index_eq`により、index typeが実際にsingle chartを持つことも固定する。

### SD7 — canonical sheafification-unit representability

現行`SheafifiedChartPresentation`の自由な`preservesDecoration : Prop`と
`preservesObstructionIdeal : Prop`を除く。また、任意の二つの`AffineAATChart`の
algebra同値を「sheafified presentation」と呼ばない。仮定8.4のうちこのPRDで
採用するのは、同一`raw`、同一context `W`においてMathlib sheafification unit自身が
algebra isomorphismである強いcaseである。

raw configuration functorの普遍性は、siteやrestriction systemを要求しない
`StructuralRelationFamily`単位のgeneric coreとして抽出する。同一coreを
`RawAmbientRestrictionSystem`のobjectwise APIと現行`RawAffinePresentation` APIの
双方から使用し、一方から他方を復元しない。

```lean
namespace StructuralRelationFamily

def Configuration
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {k : Type v} [CommRing k]
    {F : CoordinateFamily W}
    (relations : StructuralRelationFamily F k)
    (R : Type w) [CommRing R] [Algebra k R] :=
  { a : F.CoordX → R //
    ∀ r : relations.Relation,
      MvPolynomial.aeval a (relations.polynomial r) = 0 }

def Configuration.map
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {k : Type v} [CommRing k]
    {F : CoordinateFamily W} {relations : StructuralRelationFamily F k}
    {R : Type w} {T : Type x} [CommRing R] [Algebra k R]
    [CommRing T] [Algebra k T]
    (a : relations.Configuration R) (g : R →ₐ[k] T) :
    relations.Configuration T

def configurationRepresentability
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {k : Type v} [CommRing k]
    {F : CoordinateFamily W}
    (relations : StructuralRelationFamily F k)
    (R : Type w) [CommRing R] [Algebra k R] :
    relations.Configuration R ≃
      (relations.RawAmbientLawAlgebra →ₐ[k] R)

@[simp] theorem Configuration.map_id
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {k : Type v} [CommRing k]
    {F : CoordinateFamily W} {relations : StructuralRelationFamily F k}
    {R : Type w} [CommRing R] [Algebra k R]
    (a : relations.Configuration R) :
    a.map (AlgHom.id k R) = a

@[simp] theorem Configuration.map_comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {k : Type v} [CommRing k]
    {F : CoordinateFamily W} {relations : StructuralRelationFamily F k}
    {R : Type w} {T : Type x} {Q : Type*}
    [CommRing R] [Algebra k R] [CommRing T] [Algebra k T]
    [CommRing Q] [Algebra k Q]
    (a : relations.Configuration R)
    (g : R →ₐ[k] T) (h : T →ₐ[k] Q) :
    (a.map g).map h = a.map (h.comp g)

theorem configurationRepresentability_natural
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {k : Type v} [CommRing k]
    {F : CoordinateFamily W}
    (relations : StructuralRelationFamily F k)
    {R : Type w} {T : Type x} [CommRing R] [Algebra k R]
    [CommRing T] [Algebra k T]
    (g : R →ₐ[k] T) (a : relations.Configuration R) :
    relations.configurationRepresentability T (a.map g) =
      g.comp (relations.configurationRepresentability R a)

end StructuralRelationFamily

namespace RawAmbientRestrictionSystem

def LocalConfiguration
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    (W : S.category)
    (R : Type w) [CommRing R] [Algebra k R] :=
  (raw.relationFamily W).Configuration R

def LocalConfiguration.map
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k} {W : S.category}
    {R : Type w} {T : Type x} [CommRing R] [Algebra k R]
    [CommRing T] [Algebra k T]
    (a : raw.LocalConfiguration W R) (g : R →ₐ[k] T) :
    raw.LocalConfiguration W T :=
  StructuralRelationFamily.Configuration.map a g

def localConfigurationRepresentability
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    (W : S.category)
    (R : Type w) [CommRing R] [Algebra k R] :
    raw.LocalConfiguration W R ≃
      (raw.rawAlgebra W →ₐ[k] R) :=
  (raw.relationFamily W).configurationRepresentability R

@[simp] theorem LocalConfiguration.map_id
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k} {W : S.category}
    {R : Type w} [CommRing R] [Algebra k R]
    (a : raw.LocalConfiguration W R) :
    a.map (AlgHom.id k R) = a

@[simp] theorem LocalConfiguration.map_comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k} {W : S.category}
    {R : Type w} {T : Type x} {Q : Type*}
    [CommRing R] [Algebra k R] [CommRing T] [Algebra k T]
    [CommRing Q] [Algebra k Q]
    (a : raw.LocalConfiguration W R)
    (g : R →ₐ[k] T) (h : T →ₐ[k] Q) :
    (a.map g).map h = a.map (h.comp g)

theorem localConfigurationRepresentability_natural
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k) (W : S.category)
    {R : Type w} {T : Type x} [CommRing R] [Algebra k R]
    [CommRing T] [Algebra k T]
    (g : R →ₐ[k] T) (a : raw.LocalConfiguration W R) :
    raw.localConfigurationRepresentability W T (a.map g) =
      g.comp (raw.localConfigurationRepresentability W R a)

end RawAmbientRestrictionSystem

namespace AffineChart.AffineAATChart.RawAffinePresentation

-- The existing public signatures are retained; their implementations use the
-- same relation-family core as RawAmbientRestrictionSystem.
def hWUConfiguration
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {k : Type v} [CommRing k]
    {F : CoordinateFamily W} {C : AffineAATChart k}
    (P : RawAffinePresentation k F C)
    (R : Type w) [CommRing R] [Algebra k R] :=
  P.relations.Configuration R

def rawQuotientRepresentability
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {k : Type v} [CommRing k]
    {F : CoordinateFamily W} {C : AffineAATChart k}
    (P : RawAffinePresentation k F C)
    (R : Type w) [CommRing R] [Algebra k R] :
    P.hWUConfiguration R ≃
      (P.relations.RawAmbientLawAlgebra →ₐ[k] R) :=
  P.relations.configurationRepresentability R

theorem rawQuotientRepresentability_eq_generic
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {k : Type v} [CommRing k]
    {F : CoordinateFamily W} {C : AffineAATChart k}
    (P : RawAffinePresentation k F C)
    (R : Type w) [CommRing R] [Algebra k R] :
    P.rawQuotientRepresentability R =
      P.relations.configurationRepresentability R :=
  rfl

end AffineChart.AffineAATChart.RawAffinePresentation

namespace AffineChart.AffineAATChart

structure SheafifiedChartPresentation
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) : Prop where
  canonical_isIso :
    CategoryTheory.IsIso
      (raw.toRingedSite.canonical.app (op W))

noncomputable def SheafifiedChartPresentation.comparison
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category}
    (P : SheafifiedChartPresentation raw W) :
    SheafifiedSectionRing raw W ≃ₐ[k] raw.rawAlgebra W

@[simp] theorem SheafifiedChartPresentation.comparison_symm_toAlgHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category}
    (P : SheafifiedChartPresentation raw W) :
    P.comparison.symm.toAlgHom = sheafificationUnitAlgHom raw W

noncomputable def sheafifiedChartRepresentability
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category}
    (P : SheafifiedChartPresentation raw W)
    (R : Type w) [CommRing R] [Algebra k R] :
    raw.LocalConfiguration W R ≃
      (SheafifiedSectionRing raw W →ₐ[k] R)

@[simp] theorem sheafifiedChartRepresentability_apply
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category}
    (P : SheafifiedChartPresentation raw W)
    (R : Type w) [CommRing R] [Algebra k R]
    (a : raw.LocalConfiguration W R) :
    P.sheafifiedChartRepresentability R a =
      (raw.localConfigurationRepresentability W R a).comp
        P.comparison.toAlgHom

@[simp] theorem sheafifiedChartRepresentability_symm_apply
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category}
    (P : SheafifiedChartPresentation raw W)
    (R : Type w) [CommRing R] [Algebra k R]
    (f : SheafifiedSectionRing raw W →ₐ[k] R) :
    (P.sheafifiedChartRepresentability R).symm f =
      (raw.localConfigurationRepresentability W R).symm
        (f.comp P.comparison.symm.toAlgHom)

theorem sheafifiedChartRepresentability_natural
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category}
    (P : SheafifiedChartPresentation raw W)
    {R : Type w} {T : Type x} [CommRing R] [Algebra k R]
    [CommRing T] [Algebra k T]
    (g : R →ₐ[k] T) (a : raw.LocalConfiguration W R) :
    P.sheafifiedChartRepresentability T (a.map g) =
      g.comp (P.sheafifiedChartRepresentability R a)

end AffineChart.AffineAATChart
```

`StructuralRelationFamily.configurationRepresentability`が唯一のuniversal-property proofである。
`localConfigurationRepresentability`は`raw.relationFamily W`へ適用し、既存の
`RawAffinePresentation.rawQuotientRepresentability`は`P.relations`へ適用する。
`RawAffinePresentation`から`S` / `raw` / `W : S.category`を復元する経路は要求しない。
既存public APIは同じsignatureを維持し、`rawQuotientRepresentability_eq_generic`が
generic core由来であることを固定する。
`SheafifiedChartPresentation` はcanonical unitの`IsIso`だけを仮定8.4のmaterial conditionとし、
`comparison`はその逆射から導出する。したがって、無関係なalgebra equivalence、
`Equiv.refl`、自由なdecoration / obstruction propositionで閉じられない。

### SD8 — nontrivial reference models

reference modelは既存finite ringed-site exampleの`Int`係数、left/right/base context、
nonidentity quotient restrictionを再利用する。structure sheaf側で同じrestrictionが読めることを証明してから、
そのSpec mapsをchart mapsとして使う。

```lean
namespace FiniteExamples.StandardArchitectureScheme

open FiniteExamples.RingedSite.FiniteModel

def rightContext : site.category :=
  Site.ContextCategoryObject.of site.contextPreorder
    (AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.right)

def rightToBase : rightContext ⟶ base

theorem leftContext_ne_rightContext :
    RawPresheaf.left ≠ rightContext

theorem canonical_component_isIso (W : site.category) :
    CategoryTheory.IsIso
      (rawSystem.toRingedSite.canonical.app (op W))

noncomputable def baseSheafifiedPresentation :
    AffineChart.AffineAATChart.SheafifiedChartPresentation
      rawSystem base where
  canonical_isIso := canonical_component_isIso base

@[simp] theorem basePresentation_comparison_symm_toAlgHom :
    baseSheafifiedPresentation.comparison.symm.toAlgHom =
      sheafificationUnitAlgHom rawSystem base

noncomputable def baseSheafifiedRepresentability
    (R : Type w) [CommRing R] [Algebra Int R] :
    rawSystem.LocalConfiguration base R ≃
      (SheafifiedSectionRing rawSystem base →ₐ[Int] R) :=
  baseSheafifiedPresentation.sheafifiedChartRepresentability R

@[simp] theorem baseSheafifiedRepresentability_apply
    (R : Type w) [CommRing R] [Algebra Int R]
    (a : rawSystem.LocalConfiguration base R) :
    baseSheafifiedRepresentability R a =
      (rawSystem.localConfigurationRepresentability base R a).comp
        baseSheafifiedPresentation.comparison.toAlgHom

theorem baseSheafifiedRepresentability_natural
    {R : Type w} {T : Type x}
    [CommRing R] [Algebra Int R] [CommRing T] [Algebra Int T]
    (g : R →ₐ[Int] T) (a : rawSystem.LocalConfiguration base R) :
    baseSheafifiedRepresentability T (a.map g) =
      g.comp (baseSheafifiedRepresentability R a)

theorem baseSpec_nonempty :
    Nonempty (architectureChartSpec rawSystem base)

noncomputable def uncoveredAtlas :
    ArchitectureAffineAtlas rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base) where
  Index := Empty
  chart := Empty.elim

theorem uncoveredAtlas_not_valid :
    ¬ IsArchitectureAffineAtlas rawSystem uncoveredAtlas

noncomputable def twoChartReferenceModel :
    StandardArchitectureScheme rawSystem

def leftIndex : twoChartReferenceModel.atlas.Index
def rightIndex : twoChartReferenceModel.atlas.Index

theorem leftIndex_ne_rightIndex : leftIndex ≠ rightIndex

theorem index_cases (i : twoChartReferenceModel.atlas.Index) :
    i = leftIndex ∨ i = rightIndex

@[simp] theorem twoChart_underlying :
    twoChartReferenceModel.underlying =
      architectureChartSpec rawSystem base

@[simp] theorem left_chart_context :
    (twoChartReferenceModel.atlas.chart leftIndex).context =
      RawPresheaf.left

@[simp] theorem right_chart_context :
    (twoChartReferenceModel.atlas.chart rightIndex).context =
      rightContext

@[simp] theorem left_chart_map :
    (twoChartReferenceModel.atlas.chart leftIndex).map =
      architectureChartRestriction rawSystem RawPresheaf.leftToBase

@[simp] theorem right_chart_map :
    (twoChartReferenceModel.atlas.chart rightIndex).map =
      architectureChartRestriction rawSystem rightToBase

theorem chart_contexts_ne :
    (twoChartReferenceModel.atlas.chart leftIndex).context ≠
      (twoChartReferenceModel.atlas.chart rightIndex).context

theorem coefficient_nontrivial : Nontrivial Int

theorem twoChart_jointlyCovers :
    ⨆ i, ((twoChartReferenceModel.affineOpenCover rawSystem).f i).opensRange = ⊤

theorem left_chart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      (twoChartReferenceModel.atlas.chart leftIndex).map

theorem right_chart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      (twoChartReferenceModel.atlas.chart rightIndex).map

theorem twoChart_overlap_nonempty :
    Nonempty
      (twoChartReferenceModel.atlas.actualOverlap rawSystem leftIndex rightIndex)

noncomputable def baseCoordinateSection :
    SheafifiedSectionRing rawSystem base :=
  (rawSystem.toRingedSite.canonical.app (op base)).right
    ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ()))

noncomputable def leftCoordinateSection :
    SheafifiedSectionRing rawSystem RawPresheaf.left :=
  (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
    ((rawSystem.relationFamily RawPresheaf.left).quotientMap
      (MvPolynomial.X ()))

theorem canonical_left_injective :
    Function.Injective
      (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right

theorem sheafified_leftToBase_coordinate :
    sheafifiedRestriction rawSystem RawPresheaf.leftToBase
        baseCoordinateSection =
      -leftCoordinateSection

theorem sheafified_leftToBase_changes_coordinate :
    sheafifiedRestriction rawSystem RawPresheaf.leftToBase
        baseCoordinateSection ≠
      leftCoordinateSection

theorem left_transition_changes_coordinate :
    ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem base)).inv ≫
        (architectureChartRestriction rawSystem
          RawPresheaf.leftToBase).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem RawPresheaf.left)).hom)
        baseCoordinateSection ≠
      leftCoordinateSection

theorem overlap_comparison_fst :
    (twoChartReferenceModel.overlaps.comparison leftIndex rightIndex).hom ≫
        pullback.fst
          (twoChartReferenceModel.atlas.chart leftIndex).map
          (twoChartReferenceModel.atlas.chart rightIndex).map =
      architectureChartRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToLeft rawSystem leftIndex rightIndex)

theorem overlap_comparison_snd :
    (twoChartReferenceModel.overlaps.comparison leftIndex rightIndex).hom ≫
        pullback.snd
          (twoChartReferenceModel.atlas.chart leftIndex).map
          (twoChartReferenceModel.atlas.chart rightIndex).map =
      architectureChartRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToRight rawSystem leftIndex rightIndex)

theorem decoration_overlap_fires :
    sheafifiedRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToLeft rawSystem leftIndex rightIndex ≫
          (twoChartReferenceModel.atlas.chart leftIndex).contextHom) =
      sheafifiedRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToRight rawSystem leftIndex rightIndex ≫
          (twoChartReferenceModel.atlas.chart rightIndex).contextHom)

theorem actual_triple_cocycle_fires :
    ∀ i j l : twoChartReferenceModel.atlas.Index,
      twoChartReferenceModel.atlas.actualTripleToLeft rawSystem i j l ≫
          (twoChartReferenceModel.atlas.chart i).map =
        twoChartReferenceModel.atlas.actualTripleToMiddle rawSystem i j l ≫
          (twoChartReferenceModel.atlas.chart j).map ∧
      twoChartReferenceModel.atlas.actualTripleToMiddle rawSystem i j l ≫
          (twoChartReferenceModel.atlas.chart j).map =
        twoChartReferenceModel.atlas.actualTripleToRight rawSystem i j l ≫
          (twoChartReferenceModel.atlas.chart l).map

theorem context_triple_cocycle_fires :
    ∀ i j l : twoChartReferenceModel.atlas.Index,
      architectureChartRestriction rawSystem
            (twoChartReferenceModel.atlas.tripleToLeft rawSystem i j l) ≫
          (twoChartReferenceModel.atlas.chart i).map =
        architectureChartRestriction rawSystem
            (twoChartReferenceModel.atlas.tripleToMiddle rawSystem i j l) ≫
          (twoChartReferenceModel.atlas.chart j).map ∧
      architectureChartRestriction rawSystem
            (twoChartReferenceModel.atlas.tripleToMiddle rawSystem i j l) ≫
          (twoChartReferenceModel.atlas.chart j).map =
        architectureChartRestriction rawSystem
            (twoChartReferenceModel.atlas.tripleToRight rawSystem i j l) ≫
          (twoChartReferenceModel.atlas.chart l).map

noncomputable def interpretationBrokenChart :
    ArchitectureAffineChart rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base)

theorem interpretationBrokenChart_equation_ne :
    sheafifiedRestriction rawSystem interpretationBrokenChart.contextHom ≠
      (AATReadingDecoration.ofContext rawSystem base).interpretation ≫
        interpretationBrokenChart.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem
            interpretationBrokenChart.context)).hom

theorem interpretationBrokenChart_not_valid :
    ¬ IsArchitectureAffineChart rawSystem interpretationBrokenChart

noncomputable def fstBrokenOverlapPresentation :
    ArchitectureOverlapPresentation rawSystem twoChartReferenceModel.atlas

theorem fstBrokenOverlapPresentation_equation_ne :
    (fstBrokenOverlapPresentation.comparison leftIndex rightIndex).hom ≫
        pullback.fst
          (twoChartReferenceModel.atlas.chart leftIndex).map
          (twoChartReferenceModel.atlas.chart rightIndex).map ≠
      architectureChartRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToLeft rawSystem leftIndex rightIndex)

theorem fstBrokenOverlapPresentation_not_valid :
    ¬ IsArchitectureOverlapPresentation rawSystem
      fstBrokenOverlapPresentation

noncomputable def sndBrokenOverlapPresentation :
    ArchitectureOverlapPresentation rawSystem twoChartReferenceModel.atlas

theorem sndBrokenOverlapPresentation_equation_ne :
    (sndBrokenOverlapPresentation.comparison leftIndex rightIndex).hom ≫
        pullback.snd
          (twoChartReferenceModel.atlas.chart leftIndex).map
          (twoChartReferenceModel.atlas.chart rightIndex).map ≠
      architectureChartRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToRight rawSystem leftIndex rightIndex)

theorem sndBrokenOverlapPresentation_not_valid :
    ¬ IsArchitectureOverlapPresentation rawSystem
      sndBrokenOverlapPresentation

noncomputable def nonPreservingSourceDecoration :
    AATReadingDecoration rawSystem
      (architectureChartSpec rawSystem RawPresheaf.left)

@[simp] theorem nonPreservingSourceDecoration_context :
    nonPreservingSourceDecoration.context = base

theorem nonPreservingSourceDecoration_coordinate_ne :
    nonPreservingSourceDecoration.interpretation baseCoordinateSection ≠
      ((AATReadingDecoration.ofContext rawSystem base).interpretation ≫
        (architectureChartRestriction rawSystem
          RawPresheaf.leftToBase).appTop) baseCoordinateSection

theorem nonPreservingDecoration_example :
    ¬ nonPreservingSourceDecoration.Preserves rawSystem
      (architectureChartRestriction rawSystem RawPresheaf.leftToBase)
      (AATReadingDecoration.ofContext rawSystem base)

end FiniteExamples.StandardArchitectureScheme
```

`canonical_component_isIso`はbottom topology上のsheafification unitがobjectwise isoであることを固定し、
`baseSheafifiedPresentation`はそのcanonical unitを仮定8.4のstrong presentationとして使う。
`canonical_left_injective`はそのunderlying ring homから証明する。
`uncoveredAtlas_not_valid`は`baseSpec_nonempty`の点にcoverage witnessが存在しないことから証明し、
atlas validityが恒真でないことを固定する。
`sheafified_leftToBase_changes_coordinate`は既存の
`raw_leftToBase_quotientDesc_X_ne_X`をcanonical mapのnaturalityとinjectivityでtransportして証明する。
`left_transition_changes_coordinate`は`architectureChartRestriction_appTop`から証明する。
二つの同じchartをindexだけ変えて並べるmodelを主証拠にしない。

`interpretationBrokenChart`と`nonPreservingSourceDecoration`は
`sheafified_leftToBase_changes_coordinate` / `left_transition_changes_coordinate`が検出する
同じ非恒等座標作用から構成し、任意の不一致proofを入力しない。
`nonPreservingSourceDecoration_context`でwitness候補をbaseの自己射に固定し、
`nonPreservingSourceDecoration_coordinate_ne`を`baseCoordinateSection`上の具体的不一致として証明してから
`nonPreservingDecoration_example`を導く。
`fstBrokenOverlapPresentation` / `sndBrokenOverlapPresentation`はtwo-chart modelのactual comparisonを
同じ非恒等transitionで変形し、各projection equationが成立しないことを先に証明してから
validityの否定を導く。これにより`IsArchitectureAffineChart`、
`IsArchitectureOverlapPresentation`、`AATReadingDecoration.Preserves`の各Prop surfaceに
具体的な不成立例を持たせる。

`SheafifiedChartPresentation`について、このfinite modelはbottom topologyであり、
`canonical_component_isIso (W)`が全context `W`に対してcanonical unitの`IsIso`を与える。
したがって同じmodel内にcanonical unitがisoでないpresentationは構成できない。
これは不成立例を省略する具体的理由であり、単なる未実装理由として扱わない。

representabilityの非自由性は、domainが`rawSystem.LocalConfiguration base R`、codomainがactual
`SheafifiedSectionRing rawSystem base →ₐ[Int] R`であること、および
`basePresentation_comparison_symm_toAlgHom`によりcanonical unitとの一致を固定する。
nonidentityの数学的挙動は、別の任意automorphismで作らず、同じfinite modelの
`sheafified_leftToBase_changes_coordinate`と`left_transition_changes_coordinate`が負う。

### SD9 — material premise分類

| premise / data | 分類 | 根拠・放電宣言 |
| --- | --- | --- |
| `U` / `A` / `S : Site.AATSite A` | 本文由来 / dependencyで放電済み | 第I〜II部から得るAtom carrier、architecture object、selected AAT site。このPRDは実行開始条件のmerged generation APIを使用する。 |
| `k : Type v` / `[CommRing k]` | 本文由来 | 第III部のcoefficient ring。field、reduced、Noetherian等の追加typeclassは要求しない。 |
| `[HasSheafify S.topology (AATCommAlgCat k)]` | 本文由来のambient premise / finite completion evidenceでは放電必須 | 第III部 第1節 / 定義2.1 / 定義9.1。generic APIでは許可されたtypeclass parameterとし、`singleAffine`とfinite modelをcompletion evidenceに使う場合は名前付きinstance chainを要求する。finite modelでは`FiniteExamples.RingedSite.FiniteModel.hasSheafify`が放電する。target実装内で結論相当の局所instanceを追加しない。 |
| `raw : RawAmbientRestrictionSystem S k` | 本文由来 | 第III部 定義3.1〜条件4.4のselected coordinate、structural relation、restriction input。`toPresheaf`、`canonical`、`structureSheaf`が生成経路を固定する。 |
| `SheafifiedSectionRing`の`Algebra k`、`sheafificationUnitAlgHom`、`sheafifiedRestrictionAlgHom` | 新premiseなし / 放電済み | `AATCommAlgCat k`のUnder-objectのstructure map、canonical unit、structure sheaf functorから導出する。別のalgebra structureやlinearity proofを入力しない。 |
| `AATReadingDecoration.context` | 本文由来 | 第III部 定義8.1 / 定義10.1のselected base context。typed coordinate、law、signatureはこのcontextと同じ`S`から読む。 |
| `AATReadingDecoration.interpretation` | 本文由来 | Appendix A.3〜A.5のselected interpretation map。actual ring homとして入力し、chart validityでrestrictionと突合する。coefficient mapはこれとcanonical section-algebra mapから導出する。 |
| `ArchitectureAffineChart.context` / `contextHom` | 本文由来 | 第III部 定義8.1 / 定義10.1のlocal contextとbase contextへのactual morphism。自由なcompatibility labelではない。 |
| `ArchitectureAffineChart.map` | 本文由来のselected chart data | 第III部 定義9.2 / 定義9.3。domainは同じ`raw`のsection ringのSpecに固定される。 |
| `IsArchitectureAffineChart.isOpenImmersion` | 本文由来 / constructorsでは放電済み | 第III部 定義9.2。`singleAffine`とfinite modelではidentityまたはring-isomorphism由来のMathlib instanceから証明する。 |
| `IsArchitectureAffineChart.interpretation_compatible` | 本文由来 / constructorsでは放電済み | 第III部 定義9.2 / Appendix A.5のdecoration preservation。ring restriction、global interpretation、`appTop`、`ΓSpecIso`のactual equalityである。 |
| `ArchitectureAffineAtlas.Index` / `chart` | 本文由来のselected atlas data | 第III部 定義9.3 / Appendix A.5。generic recognition inputであり、finite modelでは`leftIndex` / `rightIndex`と全index分類を構成する。 |
| `IsArchitectureAffineAtlas.chart_valid` | 本文由来 / constructorsでは放電済み | 各chartの前二条件を要求する。field射影だけをcompletion evidenceにせず、`singleAffine`とfinite modelが各proofを構成する。 |
| `IsArchitectureAffineAtlas.covers` | 本文由来 / constructorsでは放電済み | 第III部 定義9.3 / Appendix A.5。pointwise witnessからMathlib `AffineOpenCover`を構成し、`iSup_opensRange = ⊤`を導く。`uncoveredAtlas_not_valid`が非恒真性を示す。 |
| `ArchitectureOverlapPresentation.comparison` | 本文由来 / constructorsでは放電済み | 第III部 定義9.2のoverlap representability。actual AAT context Specとactual pullbackのisoとして構成する。 |
| `comparison_fst` / `comparison_snd` | 本文由来 / constructorsでは放電済み | comparison isoとMathlib pullback projectionのactual equality。`singleAffine`とfinite model constructorが証明する。 |
| self-overlap comparison | 新premiseなし / 放電済み | `S.overlap.left` / `lift`、context hom subsingleton性、`architectureChartFunctor.mapIso`、identity-pullback limit uniquenessから`singleAffine`内で構成する。 |
| `StandardArchitectureScheme.atlasValid` / `overlapsValid` | recognition constructorでは本文由来の入力 / completion constructorsでは放電必須 | `ofPresentation`では明示入力を許すが、それ自体をcompletion evidenceにしない。`singleAffine`と`twoChartReferenceModel`ではprimitive dataから生成し、新しい結論相当fieldを追加しない。 |
| `StandardArchitectureScheme.Hom.preserves` | 本文由来のmorphism条件 | Appendix A.4〜A.5。actual context morphismとring-map equalityであり、identity/compositionはSD1から放電する。 |
| triple coherence | 追加premiseなし / 放電済み | iterated Mathlib pullbackのconditionからactual triple equalityを、pair equations、`S.overlap`由来のtriple maps、`architectureChartRestriction_comp`からselected-context triple equalityを導出する。 |
| `RawAmbientRestrictionSystem.LocalConfiguration` / `localConfigurationRepresentability` | 本文由来 / 新premiseなし | 第III部 定義8.2〜定理8.3。`StructuralRelationFamily.configurationRepresentability`を唯一のgeneric universal-property coreとして構成し、`raw.relationFamily W`への適用として導出する。既存`RawAffinePresentation.rawQuotientRepresentability`も同じcoreの別の系とする。 |
| `SheafifiedChartPresentation.canonical_isIso` | 本文由来のmaterial condition / sheafified representabilityでは放電必須 | 第III部 仮定8.4の強いcanonical-unit-isomorphism case。任意のcomparisonは受け取らず、`comparison`はcanonical unitの逆射から導出する。generic presentationでは明示条件だがcompletion evidenceでは生成元を要求し、finite modelは`canonical_component_isIso`で放電する。 |
| law-generated obstruction ideal | 後続構成 | full law-equational completion時にselected law witnessから生成する。arbitrary idealをこのcoreへ入力しない。 |

未放電仮定を持つcompletion theoremは置かない。`ofPresentation`はproof-carrying constructorであり、
completion evidenceは`singleAffine`と`twoChartReferenceModel`がprimitive dataから各proofを放電することとする。
同じpremiseでもgeneric recognition APIの許可入力とcompletion evidenceでの放電必須条件を区別し、
最終判定では後者について生成元、instance chain、主結論でのproof-useを要求する。

## 数学本文との対応

| 数学本文 | このPRDのfixed target | 完了時の読み方 |
| --- | --- | --- |
| 第III部 定義8.1 / Appendix A.4 | `architectureChartSpec`、`AATReadingDecoration.ofContext` | ordinary `Spec`にcontext由来readingを載せるcore。law-generated idealは後続構成。 |
| 第III部 定義8.2〜定理8.3 | `StructuralRelationFamily.configurationRepresentability`と既存`rawQuotientRepresentability` | universal-property proofをrelation-family単位へ抽出し、raw-specific APIと既存APIを同じcoreの系として維持する。 |
| 第III部 仮定8.4 | `SheafifiedChartPresentation`、`sheafifiedChartRepresentability` | 同一`raw` / contextのcanonical sheafification unitがisoである強いcaseから導くfunctor equivalence。 |
| 第III部 定義9.2 | `IsArchitectureAffineChart`、actual pair / triple pullback、overlap comparison、二種のtriple equality | open immersion、overlap representability、restriction、coherenceをactual mapsで表す。 |
| 第III部 定義9.3 / Appendix A.5 | `StandardArchitectureScheme` | actual Mathlib `Scheme`とactual affine atlasを持つreading-decorated core。 |
| 第III部 定義10.1 | `sheafifiedRestriction`、`architectureChartRestriction` | structure sheaf restrictionとSpec transitionを同じmapから構成する。 |
| 第III部 定義10.3 | 既存Scheme上のatlas recognitionとactual overlap | arbitrary affine chart dataからunderlying Schemeを構成する一般gluing constructorはこのPRDの対象外。 |

この対応表のcompletion objectはreading-decorated coreである。full law-equational
`ArchitectureScheme`のcompletionには、後続fixed targetのlaw-generated ideal、lawful closed geometry、
ideal restrictionが必要である。

## 問い

同一のAtom由来ringed AAT siteから得たsheafified section ringsをcoordinate ringsとし、
通常のMathlib `Scheme`上にactual affine open cover、actual pair pullback、triple coherence、
reading decorationを構成できるか。

```text
RawAmbientRestrictionSystem on S
  -> Mathlib sheafification O_X^U
  -> section ring O_X^U(W)
  -> ordinary Spec(O_X^U(W))
  -> open immersion into an ordinary Scheme X
  -> jointly covering affine atlas
  -> actual pullback overlaps and triple coherence
  -> reading-decorated standard architecture scheme core
```

underlying geometry、chart domain、overlapはMathlib objectsそのものを使う。
Atom/context、law universe、signature、typed coordinates、interpretationは同じ`S` / `raw`から読む。

## 現状診断

- `RawAmbientRestrictionSystem.toPresheaf`はtyped structural quotientとrestrictionからactual functorを構成する。
- `RingedAATSite.structureSheaf`は同じraw presheafのMathlib sheafificationであり、
  `RingedAATSite.canonical`はそのunitである。
- `FiniteExamples.RingedSite.FiniteModel`は`Int`係数、複数context、非恒等raw restriction、
  Mathlib `HasSheafify` instanceを持つ。
- `SpecAAT`は`PrimeSpectrum`、opaque decoration、obstruction idealを保持するが、
  Mathlib `Scheme`をunderlying objectとして持たない。
- `AffineAATChart`はselected algebraを持つが、ringed AAT siteのsheafified section ringとの
  provenanceを型で固定しない。
- `SheafifiedChartPresentation`はalgebra comparisonに加えて自由なPropを持ち、
  `sheafifiedChartRepresentability`はpresentationを使わない`Equiv.refl`である。
- `ChartCompatibility`はopen immersion、overlap、restriction、decoration、cocycle等を
  自由な`Prop` slotとして保持する。
- 旧`ArchitectureScheme`はunderlying objectを`LocallyRingedSpace`として持ち、
  actual Mathlib `Scheme`、joint coverage、actual pair pullbackを要求しない。
- `singleAffineSpec`は旧surfaceのidentity例であり、standard coreのactual atlas constructorではない。
- Mathlibには`Scheme.AffineOpenCover`、`OpenCover.iSup_opensRange`、`IsOpenImmersion`、
  Scheme pullback、`Scheme.ΓSpecIso`、`Scheme.Hom.appTop`が存在する。

既存raw quotient theoremとringed-site generationを再利用する。新しい包括wrapperを増やすのではなく、
同一section ringからSpec、restriction、chart、overlap、atlasを生成するAPIをload-bearingにする。

## アウトカム

完了時に次が成り立つ。

1. sheafified section ring、canonical `k`-algebra structure、sheafification unit、ring restriction、affine Spec、Spec transitionが同一`raw` / `S`から構成される。
2. global reading decorationがcontext、typed coordinate family、selected law-universe / signature provenance、actual interpretation ring homを持つ。
3. chart domainがdefinitionally`Spec(O_X^U(W_i))`であり、chart mapがactual Mathlib Scheme morphismである。
4. chart mapがactual `IsOpenImmersion`を満たし、ring restrictionとscheme restrictionの式が証明される。
5. chart familyがMathlib `AffineOpenCover`へ変換され、underlying Schemeをjointly coverする。
6. pair overlapがchart mapsのactual pullbackであり、selected overlap contextのSpecとactual isoで接続される。
7. overlap comparisonがpullback projectionsとcontext restriction-induced Spec mapsを一致させる。
8. actual triple overlapがiterated Mathlib pullbackとして構成され、そのcoherenceがpullback conditionから導出される。
9. selected triple context上のcoherenceもpair overlap equationsからactual Scheme map equalityとして導出される。
10. standard architecture scheme coreがactual Mathlib `Scheme`、reading decoration、atlas、overlap presentationを持つ。
11. decorated morphismがunderlying scheme morphismとactual preservation equationだけを持ち、faithful forgetful functorを成す。
12. single-affine constructorがcontext section ringのSpecからproof入力なしで発火する。
13. two-chart modelが異なるcontexts、nonempty actual overlap、選択座標を変えるactual sheafified restrictionを示す。
14. sheafified representabilityが同一`raw` / contextのcanonical sheafification unitのisoを使用し、target algebraに自然である。
15. full law-equational architecture schemeのcompletion conditionに、actual law-generated idealの構成を要求する。

## 採否規律

- 数学本文はread-onlyとし、`docs/aat/algebraic_geometric_theory/**`を変更しない。
- section ringは`raw.toRingedSite.structureSheaf`から読む。独立に選んだringをchart algebraとして再入力しない。
- chart domainにはMathlib `AlgebraicGeometry.Scheme.Spec.obj (op R)`を使う。
- underlying geometryにはMathlib `AlgebraicGeometry.Scheme`を使う。
- joint coverageはMathlib `AffineOpenCover` / `OpenCover` APIへ接続する。
- pair overlapはactual pullbackとして定義し、選択したoverlap objectで置換しない。
- selected overlap contextは`S.overlap`から生成し、actual pullbackとのcomparison isoだけをdataとして持つ。
- restriction compatibilityとtriple coherenceはactual morphism equalityで表す。
- sheafified presentationは同じ`raw` / contextのcanonical sheafification unitの`IsIso`で表し、
  任意のchart algebra comparisonで代用しない。
- reading decorationにlaw-generated idealを仮置きfieldとして追加しない。
- morphismにchart-index mapや追加comparison mapを持たせない。
- 一般gluing constructorをoptional ACにしない。このPRDは既存standard Scheme上のrecognition coreを完了対象とする。
- target statementと参照definitionは、このPRDの`Statement Design`節を不変入力とする。

## 改修要求

### R0 — 現行surface・Mathlib API・fixed statementの確定

- tracking Issueに対象main commitを固定する。
- `RawAmbientRestrictionSystem`、`RingedAATSite`、`SpecAAT`、`AffineAATChart`、
  `SheafifiedChartPresentation`、`ChartCompatibility`、旧`ArchitectureScheme`、
  `singleAffineSpec`の完全signatureと全利用箇所を棚卸しする。
- Mathlib `AffineOpenCover`、`OpenCover.iSup_opensRange`、`IsOpenImmersion`、pullback、
  `ΓSpecIso`、`Hom.appTop`、`Under`のstructure map、`CommRingCat.toAlgHom`のimportと
  利用signatureをfocused Lean fileで確認する。
- SD0〜SD8のtargetをIssueに列挙し、material premiseをSD9と突合する。

### R1 — section ringからSpecまでのcanonical route

- `RawAmbientRestrictionSystem.toRingedSite`、`SheafifiedSectionRing`、
  `sheafifiedSectionAlgebraMap`、`sheafificationUnitAlgHom`、`sheafifiedRestriction`、
  `sheafifiedRestrictionAlgHom`、`architectureChartSpec`、`architectureChartRestriction`を実装する。
- identity/compositionをstructure sheaf functorから証明する。
- `architectureChartRestriction_appTop`を`ΓSpecIso_naturality`から証明する。
- section ringまたはrestrictionを別fieldで重複保存しない。

### R2 — reading decoration

- `AATReadingDecoration`をcontextとactual ring homだけを持つ小さいdataとして実装する。
- typed coordinate family、law universe、signatureは`raw` / `S`からprojectionで読む。
- raw coordinate variableからglobal scheme sectionへの`coordinateSection`をcanonical map経由で構成する。
- coefficient mapをcanonical section-algebra mapとinterpretationの合成で導く。
- pullbackをscheme morphismの`appTop`から構成する。
- preservationをcontext restrictionと`appTop`のactual equationとして定義し、identity/compositionと
  coefficient-map preservationを証明する。
- obstruction ideal、open immersion、coverage、overlap、cocycleをdecoration fieldへ入れない。

### R3 — actual affine chart

- chart dataをcontext、context morphism、`Spec(section ring) ⟶ X`だけで定義する。
- `IsArchitectureAffineChart`をMathlib open immersionとinterpretation compatibilityのconjunctionとして分離する。
- chart domainの`IsAffine`、image open、locally ringed spaceへのforgetful APIをMathlibから得る。
- identity chart constructorが全propertyをprimitive APIから放電することを証明する。

### R4 — atlasとMathlib open cover

- atlas dataをindexとchart familyだけにする。
- atlas validityを全chart validityとpointwise coverageとして別predicateにする。
- atlas validityからactual Mathlib `AffineOpenCover`を構成する。
- `AffineOpenCover.openCover`と`OpenCover.iSup_opensRange`へ接続し、joint coverage theoremを公開する。
- `jointlyCovers : Prop` fieldやcoverage equality fieldを追加しない。

### R5 — actual pair overlapとtriple coherence

- pair contextを`S.overlap`から生成する。
- self-overlapには`S.overlap.lift`から逆向きのcontext morphismを構成し、
  `selfPairContextIso`として公開する。
- actual overlapをchart mapsのMathlib pullbackとして定義する。
- actual triple overlapをpair overlapとthird chartのiterated Mathlib pullbackとして定義する。
- overlap context Specとactual pullbackのcomparison isoを構成するdata structureを導入する。
- comparisonがpullback fst/sndとcontext-induced Spec restrictionsを一致させることを別predicateで証明する。
- pullback projectionsのopen immersionをMathlib base-change stabilityから証明する。
- overlap commutationを`pullback.condition`から証明する。
- actual triple mapsのcoherenceをpullback conditionから証明する。
- triple context mapsを二つのpair contextに対する`S.overlap`から生成し、pair equationsからselected-context Scheme map equalityを証明する。
- sheafified restrictionsがpair/triple routesで一致することをfunctorialityから証明する。
- triple equalityをoverlap validityの追加入力fieldにしない。

### R6 — standard coreとdecorated category

- SD4の`StandardArchitectureScheme`を導入する。
- constructor/destructor/ext/characterization APIを揃える。
- chart、actual cover、actual overlap、decoration、structure sheaf sectionへのprojectionを公開する。
- SD5のHom、identity、composition、ext、category instance、forgetful functor、faithfulnessを実装する。
- atlas presentationはHomの追加dataにしない。

### R7 — constructors

- `ofPresentation`を構造constructorとして実装する。
- `singleAffine`はcontext section ringのSpec、canonical reading decoration、identity chart、
  `selfPairContextIso`のScheme image、identity pullbackから構成する。
- `singleAffine`のopen immersion、coverage、overlapをcaller-supplied proofなしで放電し、triple coherenceをpair equationsから導く。
- 旧`singleAffineSpec`をnew core completionの証拠に使わない。

### R8 — sheafified representability

- `StructuralRelationFamily.Configuration`と`configurationRepresentability`を、
  `CoordinateFamily` / `StructuralRelationFamily`だけに依存するgeneric coreとして実装する。
- configurationのmap、identity、composition、target algebra morphismに対するnaturalityを
  generic coreで証明する。
- `RawAmbientRestrictionSystem.LocalConfiguration`を同じ`raw.coordFamily W` /
  `raw.relationFamily W`のgeneric configurationとして定義する。
- `localConfigurationRepresentability`を`raw.relationFamily W`へのgeneric theorem適用として実装する。
- 現行`RawAffinePresentation.hWUConfiguration`と`rawQuotientRepresentability`のpublic signatureを維持し、
  `P.relations`への同じgeneric theorem適用として実装する。
- `RawAffinePresentation`から`S` / `raw` / `W : S.category`を復元しない。
- `rawQuotientRepresentability_eq_generic`をstatement contractへ追加し、
  二つ目のuniversal-property proofを禁止する。
- `SheafifiedChartPresentation raw W`はcanonical sheafification unitの`IsIso`だけを持つ
  propositionへ変更する。
- sheafified section ringからraw quotientへのcomparisonはcanonical unitの逆射から導出する。
- configurationからactual `SheafifiedSectionRing raw W`出発の`k`-algebra homへの
  forward / inverse equivalenceを構成する。
- apply、symm_apply、target algebra morphismに対するnaturalityを証明する。
- 任意の二chart algebra comparison、二つ目のraw universal-property proof、`Equiv.refl`は使わない。

### R9 — nontrivial examples

- finite ringed-site exampleのbottom topology sheafification comparisonをsection-ring APIとして公開する。
- nonempty base Spec上のempty atlasが`IsArchitectureAffineAtlas`を満たさないことを証明する。
- left/right/base contextからtwo-chart atlasを構成する。
- 二つのchart contextが異なること、actual overlapがnonemptyであること、joint coverageを証明する。
- raw restrictionが選択座標を変えることをcanonical mapのnaturalityとinjectivityでsheafified restrictionへtransportする。
- `architectureChartRestriction_appTop`により、対応するSpec transitionも同じ選択座標を変えることを証明する。
- overlap comparison fst/snd、actual / selected-context triple coherence、decoration restriction equalityをexample上で発火させる。
- `canonical_component_isIso base`から`baseSheafifiedPresentation`を構成し、
  comparisonのcanonical provenance、apply、naturalityをexample上で発火させる。
- finite modelの非恒等座標作用から`interpretationBrokenChart`を構成し、
  interpretation equationの不成立と`IsArchitectureAffineChart`の否定を証明する。
- two-chart actual comparisonを同じ非恒等transitionで変形した
  `fstBrokenOverlapPresentation` / `sndBrokenOverlapPresentation`を構成し、
  各projection equationの不成立と`IsArchitectureOverlapPresentation`の否定を証明する。
- `nonPreservingSourceDecoration`と既存Spec transitionから、
  `AATReadingDecoration.Preserves`が成立しない具体例を証明する。
- `SheafifiedChartPresentation`の不成立例を同じfinite modelで作れない理由を、
  全contextに対する`canonical_component_isIso`として明記する。

### R10 — legacy comparison・統合・監査

- 旧`SpecAAT` / `AffineAATChart`からnew chartへのadapterは、同一`raw`、context、
  sheafified section ring comparison、actual chart mapを証明できる場合だけ提供する。
- 旧`ChartCompatibility`の自由なPropからnew overlap validityを自動生成しない。
- 旧`ArchitectureScheme`をnew coreへ自動変換しない。
- 新moduleを`Formal/AG/LawAlgebra.lean`と`Formal/AG.lean`へ接続する。
- target declarationsとreference modelsをstatement contractsとaxiom auditへ追加する。
- Lean theorem indexとproof-obligation台帳を必要範囲で同期する。
- `Formal/AG`からResearch moduleをimportしない。

## Acceptance Criteria

- [ ] AC1: executable contractがSD0〜SD8の全fixed definition / theorem signatureを実装宣言へ直接突合する。
- [ ] AC2: `SheafifiedSectionRing`が`raw.toRingedSite.structureSheaf`のobjectであり、そのcanonical `k`-algebra structureがUnder-objectのstructure mapから導かれ、独立ring / algebra inputを持たない。
- [ ] AC3: `sheafificationUnitAlgHom`がcanonical unitのunderlying map、`sheafifiedRestriction` / `sheafifiedRestrictionAlgHom`がstructure sheaf mapのunderlying mapであり、restrictionのidentity/compositionが証明される。
- [ ] AC4: `architectureChartSpec`がactual Mathlib `Spec`、`architectureChartRestriction`が同じrestrictionのSpec mapである。
- [ ] AC5: `architectureChartRestriction_appTop`が`ΓSpecIso_naturality`へ接続される。
- [ ] AC6: `AATReadingDecoration`がcontextとactual interpretation ring homを持ち、coordinate family、law universe、signatureを`raw` / `S`から読み、`coefficientMap`をcanonical section-algebra mapとinterpretationの合成で導く。
- [ ] AC7: `coordinateSection`がraw variable、structural quotient、canonical sheafification map、interpretationを同じproof bodyで使用する。
- [ ] AC8: decoration preservationがactual context restrictionとscheme `appTop`の式であり、identity/compositionとcoefficient-map preservationが導かれる。
- [ ] AC9: chart domainがdefinitionally`Spec(SheafifiedSectionRing raw W)`であり、Mathlib `IsAffine`へ接続される。
- [ ] AC10: chart validityがactual `IsOpenImmersion`とactual interpretation compatibilityを持つ。
- [ ] AC11: atlas validityからactual `Scheme.AffineOpenCover`が構成され、`iSup opensRange = ⊤`がMathlib APIで証明される。
- [ ] AC12: pair overlapがactual Mathlib pullbackであり、別のselected scheme objectで置換されていない。
- [ ] AC13: selected overlap contextが`S.overlap`から生成され、そのSpecがactual pullbackとisoで接続される。
- [ ] AC14: overlap comparison fst/sndがactual pullback projectionsとcontext-induced Spec mapsを一致させる。
- [ ] AC15: pair overlap projectionのopen immersion、overlap commutation、decoration restriction equalityが証明される。
- [ ] AC16: actual triple overlapがiterated Mathlib pullbackであり、そのcoherenceがpullback conditionから導出される。selected-context coherenceもpair comparison equations、fixed context maps、restriction functorialityから導出され、追加入力fieldも自由な`cocycle : Prop` slotもない。
- [ ] AC17: `StandardArchitectureScheme.underlying`がactual Mathlib `Scheme`であり、atlasとoverlap presentationがSD3から構成される。
- [ ] AC18: Homがunderlying scheme morphismとpreservation proofだけを持ち、category instanceとfaithful forgetful functorが構成される。
- [ ] AC19: `singleAffine`が実在するunique indexを持ち、`selfPairContextIso`とidentity pullbackからoverlap comparisonを構成し、caller-supplied open immersion、coverage、overlap proofなしで発火し、coherenceがderived theoremとして発火する。
- [ ] AC20: two-chart reference modelがちょうど二つの異なるchart contexts、各chartのactual open immersion、nonempty actual overlap、joint coverage、選択座標を変えるsheafified restrictionとSpec transitionを証明する。
- [ ] AC21: two-chart modelのoverlap comparison fst/snd、actual triple coherence、selected-context triple coherence、decoration overlapがdeclarationとして発火する。
- [ ] AC22: `StructuralRelationFamily.configurationRepresentability`が`CoordinateFamily` / `StructuralRelationFamily`だけに依存する唯一のuniversal-property proofであり、`localConfigurationRepresentability`は`raw.relationFamily W`への適用、既存`RawAffinePresentation.rawQuotientRepresentability`は`P.relations`への適用として同じpublic signatureで維持される。`RawAffinePresentation`から`S` / `raw` / `W : S.category`を復元せず、`rawQuotientRepresentability_eq_generic`が両者の共通coreを固定する。
- [ ] AC23: `SheafifiedChartPresentation raw W`はcanonical sheafification unitの`IsIso`だけをmaterial conditionとし、derived comparisonの逆射がcanonical unitと一致する。`sheafifiedChartRepresentability`はapply / symm_apply / naturalityを満たし、finite base exampleで発火する。
- [ ] AC24: `interpretationBrokenChart_not_valid`、`fstBrokenOverlapPresentation_not_valid`、`sndBrokenOverlapPresentation_not_valid`、`nonPreservingDecoration_example`がfinite modelの非恒等座標作用から発火する。`SheafifiedChartPresentation`の不成立例を同じbottom-topology modelで構成できない理由は、全contextに対する`canonical_component_isIso`で証明される。
- [ ] AC25: 新主経路に自由な`Prop` slot、`Prop + holds`、結論相当certificate、未使用material premise、definitionally unrelated componentの再包装がなく、`uncoveredAtlas_not_valid`がatlas validityの非恒真性を発火させる。
- [ ] AC26: 新definitionにconstructor/destructor/ext/characterization/comparison APIがあり、主要利用者がdefinition unfoldに依存しない。
- [ ] AC27: target declarationsとreference modelsがstandard axiomsのみを使用し、statement contractsとaxiom auditがgreenである。
- [ ] AC28: Lean theorem indexとproof-obligation台帳が、reading-decorated coreとfull law-equational geometryを区別して同期される。
- [ ] AC29: `docs/aat/algebraic_geometric_theory/**`に変更がなく、Research reverse importがない。
- [ ] AC30: 最終snapshotで全target declarationの明示引数、typeclass、structure field、certificate fieldを独立に列挙してSD9と突合し、tracking Issueのfinal discharge packetへ記録する。`material_premise_ledger_delta`と`new_material_premise`は空でなければならない。放電済みとする各premiseには、入力dataから生成するtheorem、construction、finite witnessまたは名前付きinstance chainと、主結論でのproof-useを示す。`ofPresentation`へのproof入力、field射影、accessor theorem、局所的に追加した結論相当instanceはcompletion evidenceとして認めない。generic APIの`HasSheafify`は本文由来のambient premiseとして許可するが、`singleAffine`とfinite modelでは名前付きinstance chainを放電証拠とする。
- [ ] AC31: `math-lean-review`の4本の独立査読がすべて`No major findings`である。

## Failure Contract

次は完了ではなく失敗である。

- independent section rings、scheme、structure sheafを一つのpackageへ並べること。
- `SpecAAT`の`PrimeSpectrum`だけをactual Mathlib `Scheme`の代用にすること。
- `LocallyRingedSpace`だけをunderlying objectに持つpackageをstandard coreと呼ぶこと。
- chart domain ringを`raw` / structure sheafと無関係に選ぶこと。
- `openImmersion : Prop`、`jointlyCovers : Prop`、`cocycle : Prop`をactual mapsとproofの代用にすること。
- pair overlapをselected typeまたはselected schemeとして格納し、actual pullbackを構成しないこと。
- overlap comparison isoを持つだけでfst/snd equationsを証明しないこと。
- triple equalityを証明せず、pairwise labelsだけでcoherence完成とすること。
- morphismにchart-index actionや追加comparison map dataを持たせたままfaithfulnessを主張すること。
- sheafified representabilityを任意の二chart algebraの同値で構成し、同じ`raw` /
  contextのcanonical sheafification unitと結ばないこと。
- `SheafifiedChartPresentation`がcanonical unitの`IsIso`以外の自由なcomparisonや
  decoration / obstruction propositionを持つこと。
- canonical unitの`IsIso`を放電しないまま、sheafified section ringが
  `LocalConfiguration`を表現すると無条件に主張すること。
- material premiseをtheorem argument、typeclass、structure field、certificate fieldへ移し、
  生成元と主結論でのproof-useを示さず放電済みとすること。
- `ofPresentation`へのproof入力、field accessor、またはtarget実装内で追加した
  結論相当instanceをcompletion evidenceにすること。
- raw-specific representabilityと既存`RawAffinePresentation` representabilityに
  独立なuniversal-property proofを書くこと、または既存presentationからsite-indexed
  `raw`を復元しようとすること。
- two-chart indexを持つだけで、同じidentity chartを複製したmodelを主証拠にすること。
- nonempty overlap、選択座標を変えるrestriction、actual comparisonを示さないreference model。
- law-generated idealをarbitrary fieldで追加し、full decorationと呼ぶこと。
- optional gluing targetの未実装を曖昧な状態のままAC完了と数えること。
- legacy wrapperのrename、alias、repackageだけでnew core完成とすること。
- implementation convenienceを理由にfixed statementを弱めること。

## 停止条件

- 数学本文の対象定義にLean実装と独立した反例、型不整合、well-definedness欠陥が見つかった。
- fixed statementを弱める、material premiseを増やす、参照definitionを結論相当に変更する必要が生じた。
- `RingedAATSite.structureSheaf`からcontext section ringまたはrestriction morphismを取り出せない。
- Mathlib APIでactual `Scheme`、`AffineOpenCover`、open immersion、pullbackをSD0〜SD4どおり表現できない。
- selected overlap context Specをactual pullbackへ接続するため、本文にないmaterial premiseがさらに必要になる。
- triple coherenceをactual Scheme map equalityとして証明できず、自由なPropが必要になる。
- finite ringed-site modelでcanonical sheafification unitの`IsIso`を放電できず、
  仮定8.4のstrong caseのreferenceが構成できない。
- finite ringed-site modelのraw coordinate-changing restrictionをsheafified restrictionへtransportできない。
- two-chart modelが構成できず、single chart、duplicated identity chart、empty overlapだけが残る。
- reading decoration coreとlaw-generated idealを分離すると、後続closed-equational geometryのfixed targetを表せないことが判明した。

停止報告には、該当SD / AC、fixed signature、最小の反例またはAPI blocker、試したMathlib route、
material premise分類、本文改訂の要否、独立タスクとして必要な設計を記録する。

## Non-goals

- law-generated ideal sheaf、lawful closed subscheme、factorization theoremの構成。
- full law-equational decorationを持つ最終`ArchitectureScheme`公開名へのrename。
- arbitrary affine chart gluing dataからunderlying Schemeを構成する一般gluing theory。
- 仮定8.4のうち、canonical sheafification unitはalgebra isoではないが、
  represented local functorのisoだけを別に与えるより一般のcase。
- conormal sequence、Čech connecting class、first-order lift、G-07蒸留。
- general reading functoriality、coverage refinement、coefficient base change。
- algebraic stack、gerbe、derived scheme、cotangent complexの構成。
- 旧`ArchitectureScheme`、`ChartCompatibility`、`SchemeGluingData`のrepo-wide削除。
- 数学本文へのLean status、Issue、PR、declaration名の追加。

## 検証

検証手順と実行主体は`AGENTS.md`の「よく使う検証」「PR前の確認」と
`docs/aat/guideline.md`を直接適用する。

task固有のfocused checksは次である。

- `StatementContractsStandardArchitectureScheme.lean`がSD0〜SD8の全targetを直接参照する。
- `AxiomAudit.lean`がnew theorem、two-chart declarations、base sheafified-representability
  declarationsを直接参照する。
- tracking Issueのfinal discharge packetが全target declarationの明示引数、typeclass、
  structure field、certificate fieldをSD9と突合し、`material_premise_ledger_delta`、
  `new_material_premise`、premiseごとの生成元とproof-useを記録する。
- `StructuralRelationFamily.configurationRepresentability`が唯一のgeneric coreであり、
  `localConfigurationRepresentability`と`RawAffinePresentation.rawQuotientRepresentability`が
  それぞれ同coreを直接使用する。
- `AffineOpenCover.openCover`、`OpenCover.iSup_opensRange`、pullback fst/snd、
  `ΓSpecIso_naturality`への接続がsource上に存在する。
- new core moduleに`openImmersion : Prop`、`jointlyCovers : Prop`、`cocycle : Prop`、
  `preservesDecoration : Prop`、`preservesObstructionIdeal : Prop`の自由なslotがない。
- two-chart reference modelが`leftIndex_ne_rightIndex`、`chart_contexts_ne`、
  `baseSpec_nonempty`、`uncoveredAtlas_not_valid`、`index_cases`、`twoChart_overlap_nonempty`、
  `sheafified_leftToBase_changes_coordinate`、
  `left_transition_changes_coordinate`を発火させる。
- negative examplesが`interpretationBrokenChart_equation_ne`、
  `interpretationBrokenChart_not_valid`、`fstBrokenOverlapPresentation_equation_ne`、
  `fstBrokenOverlapPresentation_not_valid`、`sndBrokenOverlapPresentation_equation_ne`、
  `sndBrokenOverlapPresentation_not_valid`、`nonPreservingDecoration_example`を発火させる。
- representability exampleが`canonical_component_isIso`、`baseSheafifiedPresentation`、
  `basePresentation_comparison_symm_toAlgHom`、`baseSheafifiedRepresentability_apply`、
  `baseSheafifiedRepresentability_natural`を発火させる。
- `docs/aat/algebraic_geometric_theory/**`がdiffに含まれない。
- changed filesにhidden / bidirectional Unicodeがない。
- public diffにprivate path、workspace名、個人識別子がない。
