import ResearchLean.AG.GeometryTransport.Transport

/-!
# Geometry component and realization supply

Every geometry component other than the three context-local realization
comparisons is transported freely along an arbitrary G-101 core-package hom.
The remaining low-level data are isolated in `RealizationTransportSupply`.
This file proves both directions: such a supply constructs a geometry lift,
and every geometry lift yields such a supply.
-/

namespace AAT.AG.GeometryTransport

universe u v

open CategoryTheory
open AtomFoundation

/-- The image of every selected context arrow is non-generating.  This is
derived from the target core's readable-context structure, independently of
any geometry lift. -/
theorem coreContextFunctor_mappedNonGeneration {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : PackageTotalHom P Q)
    {W V : Site.ContextCategoryObject P.contextPreorder} (w : W ⟶ V) :
    Site.SupportMapNonGenerating
      ((coreContextFunctor f).obj W).ctx ((coreContextFunctor f).obj V).ctx
      (Q.contextPreorder.morphism
        (leOfHom ((coreContextFunctor f).map w))).supportMap :=
  Site.ContextMorphism.nonGenerating_of_restriction
    (Q.contextPreorder.morphism_isRestriction
      (leOfHom ((coreContextFunctor f).map w)))

/-- Transport geometry components while allowing an arbitrary forward
coefficient hom.  The target coverage and overlap are still generated freely
from the core hom; the raw system is coefficient base change followed by
inverse-context reindexing. -/
noncomputable def pushGeometryPackageWithCoefficient {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q)
    (k : Type v) [CommRing k] (coeff : G.Coefficient →+* k) :
    GeometryPackage.{u, v} U where
  core := Q
  geometry := pushSelectedGeometry G f
  Coefficient := k
  coefficientCommRing := inferInstance
  raw := rawReindexCore G.geometry (pushSelectedGeometry G f) f
    (G.raw.baseChange coeff)

/-- Arbitrary-coefficient push retains exactly the supplied target core. -/
@[simp] theorem pushGeometryPackageWithCoefficient_core {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q)
    (k : Type v) [CommRing k] (coeff : G.Coefficient →+* k) :
    (pushGeometryPackageWithCoefficient G f k coeff).core = Q :=
  rfl

/-- The pushed raw system is coefficient base change followed by core reindexing. -/
@[simp] theorem pushGeometryPackageWithCoefficient_raw {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q)
    (k : Type v) [CommRing k] (coeff : G.Coefficient →+* k) :
    (pushGeometryPackageWithCoefficient G f k coeff).raw =
      rawReindexCore G.geometry (pushSelectedGeometry G f) f
        (G.raw.baseChange coeff) :=
  rfl

/-- Forward witnesses for the freely pushed coverage with arbitrary
coefficient change. -/
def pushCoverageTransportWithCoefficient {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q)
    (k : Type v) [CommRing k] (coeff : G.Coefficient →+* k) :
    CoverageTransport G (pushGeometryPackageWithCoefficient G f k coeff) f where
  requiredSupport atom h := ⟨atom, h, rfl⟩
  requiredEquationCoordinate coordinate h := ⟨coordinate, h, rfl⟩
  selectedViolationWitness coordinate h := ⟨coordinate, h, rfl⟩
  requiredAxis axis h := ⟨axis, h, rfl⟩
  supportVisibleOn W atom h := ⟨W, atom, h, rfl, rfl⟩
  equationCoordinateVisibleOn W coordinate h :=
    ⟨W, coordinate, h, rfl, rfl⟩
  violationWitnessVisibleOn W coordinate h :=
    ⟨W, coordinate, h, rfl, rfl⟩
  axisReadableOn W axis h := ⟨W, axis, h, rfl, rfl⟩
  boundaryVisibleOn W V h := ⟨W, V, h, rfl, rfl⟩

/-- The freely pushed overlap is still definitionally the selected forward
image when coefficients change. -/
noncomputable def pushOverlapTransportWithCoefficient {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q)
    (k : Type v) [CommRing k] (coeff : G.Coefficient →+* k) :
    OverlapTransport G (pushGeometryPackageWithCoefficient G f k coeff) f where
  overlapIso _ _ _ := Iso.refl _

/-- Arbitrary coefficient change also supplies every non-realization field. -/
theorem geomReadHomComponentsWithCoefficient {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q)
    (k : Type v) [CommRing k] (coeff : G.Coefficient →+* k) :
    CoverageTransport G (pushGeometryPackageWithCoefficient G f k coeff) f ∧
      Nonempty
        (OverlapTransport G (pushGeometryPackageWithCoefficient G f k coeff) f) :=
  by
    constructor
    · exact pushCoverageTransportWithCoefficient G f k coeff
    · exact ⟨pushOverlapTransportWithCoefficient G f k coeff⟩

/-- All non-realization components transported along a core-package hom. -/
structure NonRealizationComponentTransport {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) where
  coverage : CoverageTransport G (pushGeometryPackage G f) f
  overlap : OverlapTransport G (pushGeometryPackage G f) f
  coefficientHom : G.Coefficient →+* (pushGeometryPackage G f).Coefficient
  raw_eq : (pushGeometryPackage G f).raw =
    rawTransport f coefficientHom

/-- Site requirements, overlap, coefficients, and the raw system are always
transportable; realization compatibility is not an input to this construction. -/
noncomputable def transportNonRealizationComponents {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) :
    NonRealizationComponentTransport G f where
  coverage := pushCoverageTransport G f
  overlap := pushOverlapTransport G f
  coefficientHom := RingHom.id G.Coefficient
  raw_eq := rfl

/-- Standalone existence form of component transportability. -/
theorem nonRealizationComponents_transportable {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) :
    Nonempty (NonRealizationComponentTransport G f) :=
  ⟨transportNonRealizationComponents G f⟩

/-- A low-level realization supply completes the freely transported
non-realization components to a geometry hom. -/
noncomputable def geomReadHomOfHGeom {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) (H : HGeom G f) :
    GeomReadHom G (pushGeometryPackage G f) f where
  coverage := pushCoverageTransport G f
  overlap := pushOverlapTransport G f
  coefficientHom := RingHom.id G.Coefficient
  raw_eq := rfl
  supportComp := H.supportComp
  axisComp := H.axisComp
  observableComp := H.observableComp
  supportReads := H.supportReads
  axisReads := H.axisReads
  observableReads := H.observableReads
  support_naturality := H.support_naturality
  axis_naturality := H.axis_naturality
  observable_naturality := H.observable_naturality

/-- Sufficiency of `HGeom`: it constructs a target package and a total lift
over the original core-package hom. -/
noncomputable def geometryLiftOfHGeom {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) (H : HGeom G f) :
    GeometryTotalHom G (pushGeometryPackage G f) where
  base := f
  geometry := geomReadHomOfHGeom G f H

/-- The lift constructed from `HGeom` lies over the original core hom. -/
@[simp] theorem geometryLiftOfHGeom_base {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) (H : HGeom G f) :
    (geometryLiftOfHGeom G f H).base = f :=
  rfl

/-- Every geometry hom exposes the low-level realization supply required by
`HGeom`; no nondegeneracy premise is needed for this extraction. -/
def hGeomOfGeomReadHom {U : AtomCarrier.{u}}
    {G K : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core K.core} (F : GeomReadHom G K f) :
    HGeom G f where
  supportComp := F.supportComp
  axisComp := F.axisComp
  observableComp := F.observableComp
  supportReads := F.supportReads
  axisReads := F.axisReads
  observableReads := F.observableReads
  support_naturality := F.support_naturality
  axis_naturality := F.axis_naturality
  observable_naturality := F.observable_naturality
  mappedNonGeneration := coreContextFunctor_mappedNonGeneration f

/-- Necessity of `HGeom` for any geometry lift over `f`. -/
theorem hGeom_necessary {U : AtomCarrier.{u}}
    {G K : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core K.core}
    (lift : GeometryTotalHom G K) (hbase : lift.base = f) :
    Nonempty (HGeom G f) := by
  cases hbase
  exact ⟨hGeomOfGeomReadHom lift.geometry⟩

/-- For the canonical pushed target, realization supply is exactly the
remaining existence condition for a geometry hom. -/
theorem hGeom_iff_nonempty_geomReadHom {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) :
    Nonempty (HGeom G f) ↔
      Nonempty (GeomReadHom G (pushGeometryPackage G f) f) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨geomReadHomOfHGeom G f H⟩
  · rintro ⟨F⟩
    exact ⟨hGeomOfGeomReadHom F⟩

/-- Canonical G-101 transport supplies all three realization comparisons from
the underlying context transport, without referring to a geometry lift. -/
noncomputable def canonicalHGeom {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    HGeom G (transportAlongHom G.core sigma) where
  supportComp := geomTransportSupportComp G sigma
  axisComp := geomTransportAxisComp G sigma
  observableComp := geomTransportObservableComp G sigma
  supportReads W support atom h := by
    simpa [geomTransportSupportComp, coreContextFunctor,
      transportAlongHom, transportAlongUpper] using
      (transportCoreSupportEquiv_reads_iff
        G.core.reading sigma W support atom).2 h
  axisReads W axis h := by
    simpa [geomTransportAxisComp, coreContextFunctor,
      transportAlongHom, transportAlongUpper] using
      (transportCoreAxisEquiv_reads_iff G.core.reading sigma W axis).2 h
  observableReads W observable h := by
    simpa [geomTransportObservableComp, coreContextFunctor,
      transportAlongHom, transportAlongUpper] using
      (transportCoreObservableEquiv_reads_iff
        G.core.reading sigma W observable).2 h
  support_naturality w support := by
    simpa [geomTransportSupportComp, coreContextFunctor,
      transportAlongHom, transportAlongUpper] using
      transportCoreSupportEquiv_naturality G.core.reading sigma w support
  axis_naturality w axis := by
    simpa [geomTransportAxisComp, coreContextFunctor,
      transportAlongHom, transportAlongUpper] using
      transportCoreAxisEquiv_naturality G.core.reading sigma w axis
  observable_naturality w observable := by
    simpa [geomTransportObservableComp, coreContextFunctor,
      transportAlongHom, transportAlongUpper] using
      transportCoreObservableEquiv_naturality G.core.reading sigma w observable
  mappedNonGeneration :=
    coreContextFunctor_mappedNonGeneration (transportAlongHom G.core sigma)

/-- The canonical realization condition is inhabited for every source
geometry package and exact doctrine hom. -/
theorem canonicalHGeom_nonempty {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    Nonempty (HGeom G (transportAlongHom G.core sigma)) :=
  ⟨canonicalHGeom G sigma⟩

end AAT.AG.GeometryTransport

#assert_standard_axioms_only AAT.AG.GeometryTransport
