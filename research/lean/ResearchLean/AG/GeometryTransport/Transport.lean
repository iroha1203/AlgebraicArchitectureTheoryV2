import ResearchLean.AG.AtomFoundation.Transport
import ResearchLean.AG.GeometryTransport.Categories

/-!
# Canonical geometry-package transport

This module constructs every non-realization component of a target geometry
package from a source package and a G-101 core morphism.  It then specializes
the construction to the canonical core lift of an exact doctrine morphism and
builds the tautological geometry morphism.

## Implementation notes

Coverage predicates use existential direct image along the exact index maps.
This is the free forward-preserving choice and is intentionally not reflection.
Overlap data are reindexed along the inverse context functor and then sent
forward; the unit/counit of the context equivalence prove the pullback laws.
The coefficient ring is retained and the raw system is obtained by identity
base change followed by inverse-context reindexing.
-/

namespace AAT.AG.GeometryTransport

universe u v

open CategoryTheory
open AtomFoundation

/-- Free forward transport of all selected coverage predicates. -/
def pushCoverage {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) :
    Site.CoverageRequirements Q.object Q.equationSystem
      Q.algebra.signatureReading where
  requiredSupport target :=
    ∃ source, G.geometry.requirements.requiredSupport source ∧
      f.upper.atomEquiv source = target
  requiredEquationCoordinate target :=
    ∃ source, G.geometry.requirements.requiredEquationCoordinate source ∧
      (⟨f.upper.equationMap source.1.1,
          (f.upper.required_iff source.1.1).mp source.1.2⟩,
        f.upper.atomEquiv source.2) = target
  selectedViolationWitness target :=
    ∃ source, G.geometry.requirements.selectedViolationWitness source ∧
      (f.upper.equationEquiv source.1, f.upper.atomEquiv source.2) = target
  requiredAxis target :=
    ∃ source, G.geometry.requirements.requiredAxis source ∧
      f.upper.axisMap source = target
  supportVisibleOn W target :=
    ∃ sourceW source,
      G.geometry.requirements.supportVisibleOn sourceW source ∧
        coreContextMap f sourceW = W ∧ f.upper.atomEquiv source = target
  equationCoordinateVisibleOn W target :=
    ∃ sourceW source,
      G.geometry.requirements.equationCoordinateVisibleOn sourceW source ∧
        coreContextMap f sourceW = W ∧
        (⟨f.upper.equationMap source.1.1,
            (f.upper.required_iff source.1.1).mp source.1.2⟩,
          f.upper.atomEquiv source.2) = target
  violationWitnessVisibleOn W target :=
    ∃ sourceW source,
      G.geometry.requirements.violationWitnessVisibleOn sourceW source ∧
        coreContextMap f sourceW = W ∧
        (f.upper.equationEquiv source.1, f.upper.atomEquiv source.2) = target
  axisReadableOn W target :=
    ∃ sourceW source,
      G.geometry.requirements.axisReadableOn sourceW source ∧
        coreContextMap f sourceW = W ∧ f.upper.axisMap source = target
  boundaryVisibleOn W V :=
    ∃ sourceW sourceV,
      G.geometry.requirements.boundaryVisibleOn sourceW sourceV ∧
        coreContextMap f sourceW = W ∧ coreContextMap f sourceV = V

/-- Reindex the selected overlap package along a core context equivalence. -/
noncomputable def pushOverlap {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) :
    Site.ContextOverlapPullback Q.contextPreorder where
  overlap base left right :=
    coreContextMap f
      (G.geometry.overlap.overlap
        (coreContextBackwardMap f base)
        (coreContextBackwardMap f left)
        (coreContextBackwardMap f right))
  overlap_le_left {base left right} hl hr := by
    apply Q.contextPreorder.trans
    · exact ((coreContextFunctor f).map
        (homOfLE (G.geometry.overlap.overlap_le_left
          ((coreContextInverse f).map (homOfLE hl)).le
          ((coreContextInverse f).map (homOfLE hr)).le))).le
    · exact
        (f.upper.equationTransport.contextEquivalence.counitIso.hom.app
          ⟨left⟩).le
  overlap_le_right {base left right} hl hr := by
    apply Q.contextPreorder.trans
    · exact ((coreContextFunctor f).map
        (homOfLE (G.geometry.overlap.overlap_le_right
          ((coreContextInverse f).map (homOfLE hl)).le
          ((coreContextInverse f).map (homOfLE hr)).le))).le
    · exact
        (f.upper.equationTransport.contextEquivalence.counitIso.hom.app
          ⟨right⟩).le
  overlap_le_base {base left right} hl hr := by
    apply Q.contextPreorder.trans
    · exact ((coreContextFunctor f).map
        (homOfLE (G.geometry.overlap.overlap_le_base
          ((coreContextInverse f).map (homOfLE hl)).le
          ((coreContextInverse f).map (homOfLE hr)).le))).le
    · exact
        (f.upper.equationTransport.contextEquivalence.counitIso.hom.app
          ⟨base⟩).le
  overlap_lift {base left right X} hl hr hXl hXr := by
    apply Q.contextPreorder.trans
    · exact
        (f.upper.equationTransport.contextEquivalence.counitIso.inv.app
          ⟨X⟩).le
    · exact ((coreContextFunctor f).map
        (homOfLE (G.geometry.overlap.overlap_lift
          ((coreContextInverse f).map (homOfLE hl)).le
          ((coreContextInverse f).map (homOfLE hr)).le
          ((coreContextInverse f).map (homOfLE hXl)).le
          ((coreContextInverse f).map (homOfLE hXr)).le))).le

/-- Selected geometry transported freely along a core-package morphism. -/
noncomputable def pushSelectedGeometry {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) : Site.SelectedGeometryReading Q where
  requirements := pushCoverage G f
  overlap := pushOverlap G f

/--
The componentwise transported geometry package.  This construction exists for
every core-package morphism; realization comparison is supplied separately.
-/
noncomputable def pushGeometryPackage {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) : GeometryPackage.{u, v} U where
  core := Q
  geometry := pushSelectedGeometry G f
  Coefficient := G.Coefficient
  coefficientCommRing := G.coefficientCommRing
  raw := rawReindexCore G.geometry (pushSelectedGeometry G f) f
    (G.raw.baseChange (RingHom.id G.Coefficient))

/-- The pushed package has exactly the supplied target core. -/
@[simp] theorem pushGeometryPackage_core {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) :
    (pushGeometryPackage G f).core = Q :=
  rfl

/-- The pushed package retains the source coefficient type. -/
@[simp] theorem pushGeometryPackage_coefficient {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) :
    (pushGeometryPackage G f).Coefficient = G.Coefficient :=
  rfl

/-- The pushed raw system is coefficient base change followed by context reindexing. -/
@[simp] theorem pushGeometryPackage_raw {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) :
    (pushGeometryPackage G f).raw =
      rawReindexCore G.geometry (pushSelectedGeometry G f) f
        (G.raw.baseChange (RingHom.id G.Coefficient)) :=
  rfl

/-- Canonical geometry transport above an exact doctrine morphism. -/
noncomputable def geomTransportAlong {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    GeometryPackage.{u, v} U :=
  pushGeometryPackage G (transportAlongHom G.core sigma)

/-- Canonical geometry transport projects to G-101's canonical core transport. -/
@[simp] theorem geomTransportAlong_core {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    (geomTransportAlong G sigma).core = transportAlong G.core sigma :=
  rfl

/-- Canonical context transport retains each support carrier. -/
def geomTransportSupportComp {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : G.site.category) : W.ctx.Support →
      (contextForward (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma) W).ctx.Support := by
  exact (transportCoreSupportEquiv G.core.reading sigma W).toFun

/-- Canonical context transport retains each axis carrier. -/
def geomTransportAxisComp {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : G.site.category) : W.ctx.Axis →
      (contextForward (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma) W).ctx.Axis := by
  exact (transportCoreAxisEquiv G.core.reading sigma W).toFun

/-- Canonical context transport retains each observable carrier. -/
def geomTransportObservableComp {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : G.site.category) : W.ctx.Observable →
      (contextForward (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma) W).ctx.Observable := by
  exact (transportCoreObservableEquiv G.core.reading sigma W).toFun

/-- The free coverage predicates receive the canonical forward witnesses. -/
def pushCoverageTransport {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) :
    CoverageTransport G (pushGeometryPackage G f) f where
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

/-- The pushed overlap object is definitionally the forward image used by the hom. -/
noncomputable def pushOverlapTransport {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {Q : AATCorePackage U}
    (f : PackageTotalHom G.core Q) :
    OverlapTransport G (pushGeometryPackage G f) f where
  overlapIso _base _left _right := Iso.refl _

/-- The canonical geometry-stage morphism over G-101's tautological core lift. -/
noncomputable def geomTransportAlongGeometryHom {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    GeomReadHom G (geomTransportAlong G sigma)
      (transportAlongHom G.core sigma) where
  coverage := pushCoverageTransport G (transportAlongHom G.core sigma)
  overlap := pushOverlapTransport G (transportAlongHom G.core sigma)
  coefficientHom := RingHom.id G.Coefficient
  raw_eq := rfl
  supportComp := geomTransportSupportComp G sigma
  axisComp := geomTransportAxisComp G sigma
  observableComp := geomTransportObservableComp G sigma
  supportReads W support atom h := by
    simpa [geomTransportSupportComp, contextForward, contextFunctor,
      transportAlongHom, transportAlongUpper] using
      (transportCoreSupportEquiv_reads_iff
        G.core.reading sigma W support atom).2 h
  axisReads W axis h := by
    simpa [geomTransportAxisComp, contextForward, contextFunctor,
      transportAlongHom, transportAlongUpper] using
      (transportCoreAxisEquiv_reads_iff G.core.reading sigma W axis).2 h
  observableReads W observable h := by
    simpa [geomTransportObservableComp, contextForward, contextFunctor,
      transportAlongHom, transportAlongUpper] using
      (transportCoreObservableEquiv_reads_iff
        G.core.reading sigma W observable).2 h
  support_naturality w support := by
    simpa [geomTransportSupportComp, contextForward, contextFunctor,
      transportAlongHom, transportAlongUpper, targetContextMorphism,
      sourceContextMorphism] using
      transportCoreSupportEquiv_naturality G.core.reading sigma w support
  axis_naturality w axis := by
    simpa [geomTransportAxisComp, contextForward, contextFunctor,
      transportAlongHom, transportAlongUpper, targetContextMorphism,
      sourceContextMorphism] using
      transportCoreAxisEquiv_naturality G.core.reading sigma w axis
  observable_naturality w observable := by
    simpa [geomTransportObservableComp, contextForward, contextFunctor,
      transportAlongHom, transportAlongUpper, targetContextMorphism,
      sourceContextMorphism] using
      transportCoreObservableEquiv_naturality
        G.core.reading sigma w observable

/-- The tautological total geometry morphism. -/
noncomputable def geomTransportAlongHom {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    GeometryTotalHom G (geomTransportAlong G sigma) where
  base := transportAlongHom G.core sigma
  geometry := geomTransportAlongGeometryHom G sigma

/-- The tautological geometry hom lies over exactly the G-101 lift. -/
@[simp] theorem geomTransportAlongHom_base {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    (geomTransportAlongHom G sigma).base = transportAlongHom G.core sigma :=
  rfl

end AAT.AG.GeometryTransport

#assert_standard_axioms_only AAT.AG.GeometryTransport
