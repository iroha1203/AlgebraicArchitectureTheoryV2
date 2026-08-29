import ResearchLean.AG.DoctrineFiberProduct.RefinementCategory
import ResearchLean.AG.GeometryTransport.Categories
import ResearchLean.AG.GeometryTransport.FiniteWitnesses

/-!
# Geometry transport over lax refinement morphisms

This module supplies the G-115 geometry-over-refinement category.  Its lower
projection is the actual lax `RefinementPackageHom`; geometry indices are read
directly from the complete upper morphism stored in that refinement.

## Implementation notes

The G-108 `GeomReadHom` cannot be reused directly because its base is an exact
`PackageTotalHom`.  Introducing an unrelated exact lower morphism would erase
the G-114 route.  The definitions below therefore reproduce the G-108 contract
over `RefinementPackageHom.upper`, while retaining the lax lower morphism as an
ordinary data field.  The exact G-108 category enters through a separate
faithful comparison functor.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport

/-- A complete geometry index map carried by an actual lax refinement. -/
abbrev RefinementGeometryBaseHom {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) :=
  RefinementPackageHom (⟨G.core⟩ : RefinementPackageObject U) ⟨H.core⟩

/-- Forward context functor determined by the complete upper refinement map. -/
abbrev refinementGeometryContextFunctor {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : RefinementGeometryBaseHom G H) :=
  f.upper.equationTransport.contextEquivalence.functor

/-- Inverse context functor determined by the complete upper refinement map. -/
abbrev refinementGeometryContextInverse {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : RefinementGeometryBaseHom G H) :=
  f.upper.equationTransport.contextEquivalence.inverse

/-- Forward image of a geometry context along a lax refinement. -/
abbrev refinementGeometryContextForward {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : RefinementGeometryBaseHom G H) (W : G.site.category) : H.site.category :=
  (refinementGeometryContextFunctor f).obj W

/-- Backward image of a geometry context along a lax refinement. -/
abbrev refinementGeometryContextBackward {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : RefinementGeometryBaseHom G H) (W : H.site.category) : G.site.category :=
  (refinementGeometryContextInverse f).obj W

/-- Raw forward context map carried by a lax refinement's complete upper map. -/
def refinementGeometryContextMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : RefinementGeometryBaseHom G H)
    (W : Site.ArchCtx G.core.object) : Site.ArchCtx H.core.object :=
  (refinementGeometryContextForward f ⟨W⟩).ctx

/-- Raw backward context map carried by a lax refinement's complete upper map. -/
def refinementGeometryContextBackwardMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : RefinementGeometryBaseHom G H)
    (W : Site.ArchCtx H.core.object) : Site.ArchCtx G.core.object :=
  (refinementGeometryContextBackward f ⟨W⟩).ctx

/-- Required-coordinate transport carried by the complete upper refinement map. -/
def refinementRequiredCoordinateMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : RefinementGeometryBaseHom G H) :
    G.site.equationSystem.RequiredCoordinate →
      H.site.equationSystem.RequiredCoordinate :=
  fun coordinate =>
    (⟨f.upper.equationMap coordinate.1.1,
        (f.upper.required_iff coordinate.1.1).mp coordinate.1.2⟩,
      f.upper.atomEquiv coordinate.2)

/-- Full equation-coordinate transport carried by the complete upper refinement map. -/
def refinementEquationCoordinateMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : RefinementGeometryBaseHom G H) :
    G.site.equationSystem.Coordinate → H.site.equationSystem.Coordinate :=
  fun coordinate =>
    (f.upper.equationEquiv coordinate.1, f.upper.atomEquiv coordinate.2)

/-- Coverage preservation over a lax refinement and its complete upper reading. -/
structure RefinementCoverageTransport {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (f : RefinementGeometryBaseHom G H) : Prop where
  /-- Required support is preserved by the upper Atom equivalence. -/
  requiredSupport : ∀ atom,
    G.geometry.requirements.requiredSupport atom →
      H.geometry.requirements.requiredSupport (f.upper.atomEquiv atom)
  /-- Required equation coordinates are preserved by upper reindexing. -/
  requiredEquationCoordinate : ∀ coordinate,
    G.geometry.requirements.requiredEquationCoordinate coordinate →
      H.geometry.requirements.requiredEquationCoordinate
        (refinementRequiredCoordinateMap f coordinate)
  /-- Selected violation witnesses are preserved by upper reindexing. -/
  selectedViolationWitness : ∀ coordinate,
    G.geometry.requirements.selectedViolationWitness coordinate →
      H.geometry.requirements.selectedViolationWitness
        (refinementEquationCoordinateMap f coordinate)
  /-- Required axes are preserved by the upper axis map. -/
  requiredAxis : ∀ axis,
    G.geometry.requirements.requiredAxis axis →
      H.geometry.requirements.requiredAxis (f.upper.axisMap axis)
  /-- Visible support remains visible on the forward context. -/
  supportVisibleOn : ∀ W atom,
    G.geometry.requirements.supportVisibleOn W atom →
      H.geometry.requirements.supportVisibleOn
        (refinementGeometryContextMap f W) (f.upper.atomEquiv atom)
  /-- Visible required coordinates remain visible on the forward context. -/
  equationCoordinateVisibleOn : ∀ W coordinate,
    G.geometry.requirements.equationCoordinateVisibleOn W coordinate →
      H.geometry.requirements.equationCoordinateVisibleOn
        (refinementGeometryContextMap f W)
        (refinementRequiredCoordinateMap f coordinate)
  /-- Visible violation witnesses remain visible on the forward context. -/
  violationWitnessVisibleOn : ∀ W coordinate,
    G.geometry.requirements.violationWitnessVisibleOn W coordinate →
      H.geometry.requirements.violationWitnessVisibleOn
        (refinementGeometryContextMap f W)
        (refinementEquationCoordinateMap f coordinate)
  /-- Readable axes remain readable on the forward context. -/
  axisReadableOn : ∀ W axis,
    G.geometry.requirements.axisReadableOn W axis →
      H.geometry.requirements.axisReadableOn
        (refinementGeometryContextMap f W) (f.upper.axisMap axis)
  /-- Visible context incidences remain visible after upper transport. -/
  boundaryVisibleOn : ∀ W V,
    G.geometry.requirements.boundaryVisibleOn W V →
      H.geometry.requirements.boundaryVisibleOn
        (refinementGeometryContextMap f W) (refinementGeometryContextMap f V)

namespace RefinementCoverageTransport

/-- Identity coverage preservation over the identity refinement. -/
def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    RefinementCoverageTransport G G (RefinementPackageHom.id ⟨G.core⟩) where
  requiredSupport _ := _root_.id
  requiredEquationCoordinate _ := _root_.id
  selectedViolationWitness _ := _root_.id
  requiredAxis _ := _root_.id
  supportVisibleOn _ _ := _root_.id
  equationCoordinateVisibleOn _ _ := _root_.id
  violationWitnessVisibleOn _ _ := _root_.id
  axisReadableOn _ _ := _root_.id
  boundaryVisibleOn _ _ := _root_.id

/-- Coverage preservation composes through complete upper refinement maps. -/
def comp {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    {f : RefinementGeometryBaseHom G H} {g : RefinementGeometryBaseHom H K}
    (F : RefinementCoverageTransport G H f)
    (T : RefinementCoverageTransport H K g) :
    RefinementCoverageTransport G K (f.comp g) where
  requiredSupport atom h := T.requiredSupport _ (F.requiredSupport atom h)
  requiredEquationCoordinate coordinate h := by
    simpa [refinementRequiredCoordinateMap] using
      T.requiredEquationCoordinate (refinementRequiredCoordinateMap f coordinate)
        (F.requiredEquationCoordinate coordinate h)
  selectedViolationWitness coordinate h := by
    simpa [refinementEquationCoordinateMap] using
      T.selectedViolationWitness (refinementEquationCoordinateMap f coordinate)
        (F.selectedViolationWitness coordinate h)
  requiredAxis axis h := T.requiredAxis _ (F.requiredAxis axis h)
  supportVisibleOn W atom h :=
    T.supportVisibleOn (refinementGeometryContextMap f W) _
      (F.supportVisibleOn W atom h)
  equationCoordinateVisibleOn W coordinate h := by
    simpa [refinementRequiredCoordinateMap] using
      T.equationCoordinateVisibleOn (refinementGeometryContextMap f W)
        (refinementRequiredCoordinateMap f coordinate)
        (F.equationCoordinateVisibleOn W coordinate h)
  violationWitnessVisibleOn W coordinate h := by
    simpa [refinementEquationCoordinateMap] using
      T.violationWitnessVisibleOn (refinementGeometryContextMap f W)
        (refinementEquationCoordinateMap f coordinate)
        (F.violationWitnessVisibleOn W coordinate h)
  axisReadableOn W axis h :=
    T.axisReadableOn (refinementGeometryContextMap f W) _
      (F.axisReadableOn W axis h)
  boundaryVisibleOn W V h :=
    T.boundaryVisibleOn (refinementGeometryContextMap f W)
      (refinementGeometryContextMap f V) (F.boundaryVisibleOn W V h)

/-- The lax coverage certificate has a concrete negative instance inherited
from the reviewed G-108 finite coverage fixture. -/
theorem no_transport_to_emptyTarget :
    ¬ RefinementCoverageTransport
      GeometryTransport.NegativeGeometryWitness.package
      GeometryTransport.NegativeGeometryWitness.emptyCoverageTarget
      ((exactPackageToRefinement FiniteModel.carrier).map
        GeometryTransport.NegativeGeometryWitness.coreHom) := by
  intro T
  have htarget := T.requiredSupport FiniteModel.FiniteAtom.componentA rfl
  exact htarget

end RefinementCoverageTransport

/-- Selected-overlap comparison over a lax refinement. -/
structure RefinementOverlapTransport {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (f : RefinementGeometryBaseHom G H) where
  /-- The selected overlap comparison on every target context triple. -/
  overlapIso : ∀ base left right,
    refinementGeometryContextForward f
        ⟨G.geometry.overlap.overlap
          (refinementGeometryContextBackwardMap f base)
          (refinementGeometryContextBackwardMap f left)
          (refinementGeometryContextBackwardMap f right)⟩ ≅
      ⟨H.geometry.overlap.overlap base left right⟩

namespace RefinementOverlapTransport

/-- Identity overlap comparison. -/
def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    RefinementOverlapTransport G G (RefinementPackageHom.id ⟨G.core⟩) where
  overlapIso _ _ _ := Iso.refl _

/-- Overlap comparisons compose through the complete upper context functors. -/
def comp {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    {f : RefinementGeometryBaseHom G H} {g : RefinementGeometryBaseHom H K}
    (F : RefinementOverlapTransport G H f)
    (T : RefinementOverlapTransport H K g) :
    RefinementOverlapTransport G K (f.comp g) where
  overlapIso base left right :=
    ((refinementGeometryContextFunctor g).mapIso
      (F.overlapIso
        (refinementGeometryContextBackwardMap g base)
        (refinementGeometryContextBackwardMap g left)
        (refinementGeometryContextBackwardMap g right))).trans
      (T.overlapIso base left right)

end RefinementOverlapTransport

/-- Coverage preservation proofs over a fixed refinement are unique. -/
instance refinementCoverageTransportSubsingleton {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) (f : RefinementGeometryBaseHom G H) :
    Subsingleton (RefinementCoverageTransport G H f) := ⟨fun _ _ => by rfl⟩

/-- Overlap comparisons over a fixed refinement are unique in the context preorder. -/
instance refinementOverlapTransportSubsingleton {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) (f : RefinementGeometryBaseHom G H) :
    Subsingleton (RefinementOverlapTransport G H f) := by
  constructor
  intro F T
  cases F with
  | mk Fiso =>
      cases T with
      | mk Tiso =>
          congr
          funext base left right
          exact Subsingleton.elim _ _

/-- Source context morphism used by refinement-geometry naturality. -/
abbrev refinementSourceContextMorphism {U : AtomCarrier.{u}}
    {G : GeometryPackage.{u, v} U} {W V : G.site.category} (w : W ⟶ V) :=
  G.core.contextPreorder.morphism (leOfHom w)

/-- Target context morphism induced by the complete upper refinement map. -/
abbrev refinementTargetContextMorphism {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {f : RefinementGeometryBaseHom G H}
    {W V : G.site.category} (w : W ⟶ V) :=
  H.core.contextPreorder.morphism
    (leOfHom ((refinementGeometryContextFunctor f).map w))

/-- Reindex a raw system along the inverse context functor of a lax refinement. -/
noncomputable def refinementRawReindex {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {k : Type v} [CommRing k]
    (f : RefinementGeometryBaseHom G H)
    (raw : LawAlgebra.RawAmbientRestrictionSystem G.site k) :
    LawAlgebra.RawAmbientRestrictionSystem H.site k where
  coordFamily W :=
    copyCoordinateFamily (V := W.ctx)
      (raw.coordFamily ((refinementGeometryContextInverse f).obj W))
  relationFamily W :=
    copyRelationFamily (V := W.ctx)
      (raw.relationFamily ((refinementGeometryContextInverse f).obj W))
  restrictionStable {X Y} h := by
    let source := raw.restrictionStable ((refinementGeometryContextInverse f).map h)
    exact {
      restriction := { variableImage := source.restriction.variableImage }
      maps_JStruct := source.maps_JStruct
    }
  identity_polynomialMap X := by
    have hmap : (refinementGeometryContextInverse f).map (𝟙 X) =
        𝟙 ((refinementGeometryContextInverse f).obj X) := by simp
    cases hmap
    exact raw.identity_polynomialMap ((refinementGeometryContextInverse f).obj X)
  composition_polynomialMap h k := by
    have hmap : (refinementGeometryContextInverse f).map (h ≫ k) =
        (refinementGeometryContextInverse f).map h ≫
          (refinementGeometryContextInverse f).map k := by simp
    cases hmap
    exact raw.composition_polynomialMap
      ((refinementGeometryContextInverse f).map h)
      ((refinementGeometryContextInverse f).map k)

/-- Coefficient base change followed by refinement-indexed raw reindexing. -/
noncomputable def refinementRawTransport {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : RefinementGeometryBaseHom G H)
    (coeff : G.Coefficient →+* H.Coefficient) :
    LawAlgebra.RawAmbientRestrictionSystem H.site H.Coefficient :=
  refinementRawReindex f (G.raw.baseChange coeff)

@[simp] theorem refinementRawReindex_id {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {k : Type v} [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem G.site k) :
    refinementRawReindex (G := G) (H := G) (RefinementPackageHom.id ⟨G.core⟩) raw =
      raw := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

theorem refinementRawReindex_comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U} {k : Type v} [CommRing k]
    (f : RefinementGeometryBaseHom G H)
    (g : RefinementGeometryBaseHom H K)
    (raw : LawAlgebra.RawAmbientRestrictionSystem G.site k) :
    refinementRawReindex (f.comp g) raw =
      refinementRawReindex g (refinementRawReindex f raw) := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

theorem refinementRawReindex_baseChange {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : RefinementGeometryBaseHom G H)
    (raw : LawAlgebra.RawAmbientRestrictionSystem G.site k)
    (coeff : k →+* k') :
    (refinementRawReindex f raw).baseChange coeff =
      refinementRawReindex f (raw.baseChange coeff) := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

@[simp] theorem refinementRawTransport_id {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    refinementRawTransport (G := G) (H := G) (RefinementPackageHom.id ⟨G.core⟩)
      (RingHom.id G.Coefficient) = G.raw := by
  simp [refinementRawTransport]

theorem refinementRawTransport_comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (f : RefinementGeometryBaseHom G H)
    (g : RefinementGeometryBaseHom H K)
    (coeff₁ : G.Coefficient →+* H.Coefficient)
    (coeff₂ : H.Coefficient →+* K.Coefficient) :
    refinementRawTransport (f.comp g) (coeff₂.comp coeff₁) =
      refinementRawReindex g ((refinementRawTransport f coeff₁).baseChange coeff₂) := by
  rw [refinementRawTransport, refinementRawTransport,
    LawAlgebra.RawAmbientRestrictionSystem.baseChange_comp]
  rw [refinementRawReindex_comp, refinementRawReindex_baseChange]

/-- The G-108 geometry contract indexed by a lax refinement's complete upper map. -/
structure RefinementGeomReadHom {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (baseHom : RefinementGeometryBaseHom G H) where
  /-- Coverage preservation indexed by the complete upper reading. -/
  coverage : RefinementCoverageTransport G H baseHom
  /-- Selected-overlap preservation indexed by the complete upper reading. -/
  overlap : RefinementOverlapTransport G H baseHom
  /-- Coefficient-ring transport. -/
  coefficientHom : G.Coefficient →+* H.Coefficient
  /-- Compatibility of the target raw system with upper reindexing and coefficients. -/
  raw_eq : H.raw = refinementRawTransport baseHom coefficientHom
  /-- Support comparison on every source context. -/
  supportComp : ∀ W : G.site.category,
    W.ctx.Support → (refinementGeometryContextForward baseHom W).ctx.Support
  /-- Axis comparison on every source context. -/
  axisComp : ∀ W : G.site.category,
    W.ctx.Axis → (refinementGeometryContextForward baseHom W).ctx.Axis
  /-- Observable comparison on every source context. -/
  observableComp : ∀ W : G.site.category,
    W.ctx.Observable → (refinementGeometryContextForward baseHom W).ctx.Observable
  /-- The support comparison preserves the selected support reading. -/
  supportReads : ∀ (W : G.site.category) support atom,
    W.ctx.minimal.supportReads support atom →
      (refinementGeometryContextForward baseHom W).ctx.minimal.supportReads
        (supportComp W support) (baseHom.upper.atomEquiv atom)
  /-- The axis comparison preserves the selected axis reading. -/
  axisReads : ∀ (W : G.site.category) axis,
    W.ctx.minimal.axisReads axis →
      (refinementGeometryContextForward baseHom W).ctx.minimal.axisReads
        (axisComp W axis)
  /-- The observable comparison preserves the selected observable reading. -/
  observableReads : ∀ (W : G.site.category) observable,
    W.ctx.minimal.observableReads observable →
      (refinementGeometryContextForward baseHom W).ctx.minimal.observableReads
        (observableComp W observable)
  /-- Support comparison is natural in context restriction. -/
  support_naturality : ∀ {W V : G.site.category} (w : W ⟶ V) support,
    (refinementTargetContextMorphism (f := baseHom) w).supportMap
        (supportComp W support) =
      supportComp V ((refinementSourceContextMorphism w).supportMap support)
  /-- Axis comparison is natural in context restriction. -/
  axis_naturality : ∀ {W V : G.site.category} (w : W ⟶ V) axis,
    (refinementTargetContextMorphism (f := baseHom) w).axisMap
        (axisComp W axis) =
      axisComp V ((refinementSourceContextMorphism w).axisMap axis)
  /-- Observable comparison is natural in context restriction. -/
  observable_naturality : ∀ {W V : G.site.category} (w : W ⟶ V) observable,
    (refinementTargetContextMorphism (f := baseHom) w).observableRestrict
        (observableComp V observable) =
      observableComp W
        ((refinementSourceContextMorphism w).observableRestrict observable)

namespace RefinementGeomReadHom

/-- Identity refinement-geometry contract. -/
noncomputable def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    RefinementGeomReadHom G G (RefinementPackageHom.id ⟨G.core⟩) where
  coverage := RefinementCoverageTransport.id G
  overlap := RefinementOverlapTransport.id G
  coefficientHom := RingHom.id G.Coefficient
  raw_eq := (refinementRawTransport_id G).symm
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- Composition of refinement-geometry contracts. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {f : RefinementGeometryBaseHom G H}
    {g : RefinementGeometryBaseHom H K}
    (F : RefinementGeomReadHom G H f) (T : RefinementGeomReadHom H K g) :
    RefinementGeomReadHom G K (f.comp g) where
  coverage := F.coverage.comp T.coverage
  overlap := F.overlap.comp T.overlap
  coefficientHom := T.coefficientHom.comp F.coefficientHom
  raw_eq := by
    calc
      K.raw = refinementRawTransport g T.coefficientHom := T.raw_eq
      _ = refinementRawReindex g (H.raw.baseChange T.coefficientHom) := rfl
      _ = refinementRawReindex g
          ((refinementRawTransport f F.coefficientHom).baseChange
            T.coefficientHom) := by rw [F.raw_eq]
      _ = refinementRawTransport (f.comp g)
          (T.coefficientHom.comp F.coefficientHom) :=
            (refinementRawTransport_comp f g F.coefficientHom T.coefficientHom).symm
  supportComp W support :=
    T.supportComp (refinementGeometryContextForward f W) (F.supportComp W support)
  axisComp W axis :=
    T.axisComp (refinementGeometryContextForward f W) (F.axisComp W axis)
  observableComp W observable :=
    T.observableComp (refinementGeometryContextForward f W)
      (F.observableComp W observable)
  supportReads W support atom h :=
    T.supportReads (refinementGeometryContextForward f W) _ _
      (F.supportReads W support atom h)
  axisReads W axis h :=
    T.axisReads (refinementGeometryContextForward f W) _ (F.axisReads W axis h)
  observableReads W observable h :=
    T.observableReads (refinementGeometryContextForward f W) _
      (F.observableReads W observable h)
  support_naturality {W V} w support := by
    rw [T.support_naturality ((refinementGeometryContextFunctor f).map w),
      F.support_naturality w]
  axis_naturality {W V} w axis := by
    rw [T.axis_naturality ((refinementGeometryContextFunctor f).map w),
      F.axis_naturality w]
  observable_naturality {W V} w observable := by
    rw [T.observable_naturality ((refinementGeometryContextFunctor f).map w),
      F.observable_naturality w]

/-- Refinement geometry contracts are determined by their computational data. -/
@[ext (iff := false)] theorem ext {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {f : RefinementGeometryBaseHom G H}
    {F T : RefinementGeomReadHom G H f}
    (hcoefficient : F.coefficientHom = T.coefficientHom)
    (hsupport : HEq F.supportComp T.supportComp)
    (haxis : HEq F.axisComp T.axisComp)
    (hobservable : HEq F.observableComp T.observableComp) : F = T := by
  have hcoverage : F.coverage = T.coverage := Subsingleton.elim _ _
  have hoverlap : F.overlap = T.overlap := Subsingleton.elim _ _
  cases F
  cases T
  cases hcoverage
  cases hoverlap
  cases hcoefficient
  cases hsupport
  cases haxis
  cases hobservable
  rfl

end RefinementGeomReadHom

/-- A geometry morphism whose lower projection is an actual lax refinement. -/
structure RefinementGeometryHom {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  /-- The actual lax lower refinement together with its complete upper reading. -/
  base : RefinementGeometryBaseHom G H
  /-- Geometry transport indexed by the complete upper reading of `base`. -/
  geometry : RefinementGeomReadHom G H base

namespace RefinementGeometryHom

/-- Identity refinement-geometry morphism. -/
noncomputable def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    RefinementGeometryHom G G where
  base := RefinementPackageHom.id ⟨G.core⟩
  geometry := RefinementGeomReadHom.id G

/-- Composition retains the lax lower route and composes the full geometry data. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (F : RefinementGeometryHom G H) (T : RefinementGeometryHom H K) :
    RefinementGeometryHom G K where
  base := F.base.comp T.base
  geometry := F.geometry.comp T.geometry

/-- Total refinement-geometry homs are determined by base and geometry data. -/
@[ext (iff := false)] theorem ext {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {F T : RefinementGeometryHom G H}
    (hbase : F.base = T.base)
    (hgeometry : HEq F.geometry T.geometry) : F = T := by
  cases F
  cases T
  cases hbase
  cases hgeometry
  rfl

/-- Equality of total refinement-geometry homs identifies their dependent geometry data. -/
theorem geometry_heq {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {F T : RefinementGeometryHom G H} (h : F = T) :
    HEq F.geometry T.geometry := by
  cases h
  rfl

end RefinementGeometryHom

/-- A geometry package regarded as an object of the lax-refinement geometry category.

The wrapper separates this category instance from the exact G-108 category
instance while retaining exactly the same mathematical object data. -/
structure RefinementGeometryObject (U : AtomCarrier.{u}) where
  /-- The unchanged G-108 geometry package data. -/
  geometry : GeometryPackage.{u, v} U

/-- Geometry packages with lax refinement-geometry morphisms. -/
abbrev RefinementGeometryCategory (U : AtomCarrier.{u}) :=
  RefinementGeometryObject.{u, v} U

/-- The category structure generated by identity and composition of lax geometry homs. -/
noncomputable instance refinementGeometryCategory (U : AtomCarrier.{u}) :
    Category (RefinementGeometryCategory.{u, v} U) where
  Hom G H := RefinementGeometryHom G.geometry H.geometry
  id G := RefinementGeometryHom.id G.geometry
  comp F T := RefinementGeometryHom.comp F T
  id_comp := by
    intro G H F
    apply RefinementGeometryHom.ext
    · apply RefinementPackageHom.ext
      · apply PointedRefinementHom.ext
        apply RefinementDoctrineHom.ext <;> rfl
      · exact PackageTotalHom.upper_id_comp F.base.upper
    · apply heq_of_eq
      apply RefinementGeomReadHom.ext <;> rfl
  comp_id := by
    intro G H F
    apply RefinementGeometryHom.ext
    · apply RefinementPackageHom.ext
      · apply PointedRefinementHom.ext
        apply RefinementDoctrineHom.ext <;> rfl
      · exact PackageTotalHom.upper_comp_id F.base.upper
    · apply heq_of_eq
      apply RefinementGeomReadHom.ext <;> rfl
  assoc := by
    intro G H K L F T S
    apply RefinementGeometryHom.ext
    · apply RefinementPackageHom.ext
      · rfl
      · exact PackageTotalHom.upper_comp_assoc
          F.base.upper T.base.upper S.base.upper
    · apply heq_of_eq
      apply RefinementGeomReadHom.ext <;> rfl

/-- Forget geometry data while preserving the actual lax refinement morphism. -/
noncomputable def refinementGeometryProjection (U : AtomCarrier.{u}) :
    RefinementGeometryCategory.{u, v} U ⥤ RefinementPackageTotalCategory U where
  obj G := ⟨G.geometry.core⟩
  map F := F.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The projection exposes the actual lax lower refinement package morphism. -/
@[simp] theorem refinementGeometryProjection_map {U : AtomCarrier.{u}}
    {G H : RefinementGeometryCategory.{u, v} U} (F : G ⟶ H) :
    (refinementGeometryProjection U).map F =
      (show RefinementGeometryHom G.geometry H.geometry from F).base := rfl

/-- Exact raw reindexing agrees with refinement reindexing after exact embedding. -/
theorem refinementRawReindex_ofExact {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {k : Type v} [CommRing k]
    (f : PackageTotalHom G.core H.core)
    (raw : LawAlgebra.RawAmbientRestrictionSystem G.site k) :
    refinementRawReindex
        ((exactPackageToRefinement U).map f) raw =
      rawReindex f raw := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

/-- Exact G-108 geometry data induce the lax-refinement geometry contract. -/
noncomputable def RefinementGeomReadHom.ofExact {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (F : GeometryTotalHom G H) :
    RefinementGeomReadHom G H ((exactPackageToRefinement U).map F.base) where
  coverage := {
    requiredSupport := F.geometry.coverage.requiredSupport
    requiredEquationCoordinate := F.geometry.coverage.requiredEquationCoordinate
    selectedViolationWitness := F.geometry.coverage.selectedViolationWitness
    requiredAxis := F.geometry.coverage.requiredAxis
    supportVisibleOn := F.geometry.coverage.supportVisibleOn
    equationCoordinateVisibleOn := F.geometry.coverage.equationCoordinateVisibleOn
    violationWitnessVisibleOn := F.geometry.coverage.violationWitnessVisibleOn
    axisReadableOn := F.geometry.coverage.axisReadableOn
    boundaryVisibleOn := F.geometry.coverage.boundaryVisibleOn
  }
  overlap := { overlapIso := F.geometry.overlap.overlapIso }
  coefficientHom := F.geometry.coefficientHom
  raw_eq := by
    rw [F.geometry.raw_eq]
    unfold refinementRawTransport rawTransport
    rw [refinementRawReindex_ofExact]
  supportComp := F.geometry.supportComp
  axisComp := F.geometry.axisComp
  observableComp := F.geometry.observableComp
  supportReads := F.geometry.supportReads
  axisReads := F.geometry.axisReads
  observableReads := F.geometry.observableReads
  support_naturality := F.geometry.support_naturality
  axis_naturality := F.geometry.axis_naturality
  observable_naturality := F.geometry.observable_naturality

/-- Exact G-108 geometry morphisms embed into refinement geometry morphisms. -/
noncomputable def exactGeometryToRefinementGeometry (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ⥤ RefinementGeometryCategory.{u, v} U where
  obj G := ⟨G⟩
  map F := {
    base := (exactPackageToRefinement U).map F.base
    geometry := RefinementGeomReadHom.ofExact F
  }
  map_id G := by
    apply RefinementGeometryHom.ext
    · rfl
    · apply heq_of_eq
      apply RefinementGeomReadHom.ext <;> rfl
  map_comp F T := by
    apply RefinementGeometryHom.ext
    · rfl
    · apply heq_of_eq
      apply RefinementGeomReadHom.ext <;> rfl

/-- The exact embedding commutes strictly with the two package projections. -/
theorem exact_refinementGeometry_projection_square (U : AtomCarrier.{u}) :
    exactGeometryToRefinementGeometry.{u, v} U ⋙ refinementGeometryProjection U =
      geometryProjection U ⋙ exactPackageToRefinement U := by
  rfl

/-- Exact package morphisms remain distinguishable after refinement embedding. -/
theorem exactPackageToRefinement_map_injective {U : AtomCarrier.{u}}
    {P Q : PackageTotalCategory U} {f g : P ⟶ Q}
    (h : (exactPackageToRefinement U).map f =
      (exactPackageToRefinement U).map g) : f = g := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · exact congrArg
        (fun x => x.base.doctrineHom.sourceMap) h
    · apply Equiv.ext
      intro atom
      exact congrFun (congrArg (fun x => x.base.doctrineHom.atomMap) h) atom
  · exact congrArg RefinementPackageHom.upper h

/-- The exact geometry embedding is faithful. -/
noncomputable instance exactGeometryToRefinementGeometry_faithful
    (U : AtomCarrier.{u}) :
    (exactGeometryToRefinementGeometry.{u, v} U).Faithful where
  map_injective {G H} F T h := by
    rcases F with ⟨Fbase, Fgeometry⟩
    rcases T with ⟨Tbase, Tgeometry⟩
    have hbase : Fbase = Tbase :=
      exactPackageToRefinement_map_injective
        (congrArg RefinementGeometryHom.base h)
    subst Tbase
    have hrefinementGeometry :
        RefinementGeomReadHom.ofExact
            (F := ⟨Fbase, Fgeometry⟩) =
          RefinementGeomReadHom.ofExact
            (F := ⟨Fbase, Tgeometry⟩) := by
      exact eq_of_heq (RefinementGeometryHom.geometry_heq h)
    apply GeometryTotalHom.ext
    · rfl
    · apply heq_of_eq
      apply GeomReadHom.ext
      · exact congrArg
          RefinementGeomReadHom.coefficientHom hrefinementGeometry
      · exact heq_of_eq (congrArg
          RefinementGeomReadHom.supportComp hrefinementGeometry)
      · exact heq_of_eq (congrArg
          RefinementGeomReadHom.axisComp hrefinementGeometry)
      · exact heq_of_eq (congrArg
          RefinementGeomReadHom.observableComp hrefinementGeometry)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
