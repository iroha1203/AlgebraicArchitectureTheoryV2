import ResearchLean.AG.GeometryTransport.Transport

/-!
# Opcartesian geometry transport

This module deconjugates an arbitrary geometry hom along the canonical G-101
context transport.  The resulting factor is over an arbitrary core-package
tail, so the final universal property is the strong cocartesian property.
-/

namespace AAT.AG.GeometryTransport

universe u v

open CategoryTheory
open AtomFoundation

set_option maxHeartbeats 2000000

namespace GeomReadHom

/-- Reindex a geometry hom along equality of its fixed core morphism. -/
def castBase {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {f g : PackageTotalHom G.core H.core} (hfg : f = g)
    (F : GeomReadHom G H f) : GeomReadHom G H g := by
  cases hfg
  exact F

end GeomReadHom

/-- Every canonical target context is the image of its inverse context. -/
theorem canonicalContextSection_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : (geomTransportAlong G sigma).site.category) :
    contextForward (transportAlongHom G.core sigma)
        (contextBackward (transportAlongHom G.core sigma) W) = W := by
  simpa [contextForward, contextBackward, contextFunctor, contextInverse,
    transportAlongHom, transportAlongUpper] using
    transportCoreContextFunctorInverse_obj_eq G.core.reading sigma W

/-- Forward canonical context transport followed by its inverse fixes the
source context. -/
theorem canonicalContextRetraction_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : G.site.category) :
    contextBackward (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma)
        (contextForward (G := G) (H := geomTransportAlong G sigma)
          (transportAlongHom G.core sigma) W) = W := by
  simpa [contextForward, contextBackward, contextFunctor, contextInverse,
    transportAlongHom, transportAlongUpper] using
    transportCoreContextInverseFunctor_obj_eq G.core.reading sigma W

/-- A tail functor carries canonical context cancellation to its target. -/
theorem canonicalTailContextSection_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (W : (geomTransportAlong G sigma).site.category) :
    (contextFunctor tail).obj
        (contextForward (transportAlongHom G.core sigma)
          (contextBackward (transportAlongHom G.core sigma) W)) =
      (contextFunctor tail).obj W :=
  congrArg (contextFunctor tail).obj (canonicalContextSection_eq G sigma W)

/-- Composite context transport cancels the canonical inverse before the tail. -/
theorem compositeTailContextSection_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (W : (geomTransportAlong G sigma).site.category) :
    contextForward
        (PackageTotalHom.comp (transportAlongHom G.core sigma) tail)
        (contextBackward (transportAlongHom G.core sigma) W) =
      contextForward tail W := by
  calc
    contextForward
        (PackageTotalHom.comp (transportAlongHom G.core sigma) tail)
        (contextBackward (transportAlongHom G.core sigma) W) =
      contextForward tail
        (contextForward (transportAlongHom G.core sigma)
          (contextBackward (transportAlongHom G.core sigma) W)) :=
        contextForward_comp (transportAlongHom G.core sigma) tail _
    _ = contextForward tail W := canonicalTailContextSection_eq G sigma tail W

/-- Canonical inverse context transport identifies the support carrier. -/
noncomputable def canonicalSectionSupportEquiv {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : (geomTransportAlong G sigma).site.category) :
    (contextBackward (transportAlongHom G.core sigma) W).ctx.Support ≃
      W.ctx.Support := by
  simpa [contextBackward, contextInverse, transportAlongHom,
    transportAlongUpper] using
    transportCoreSectionSupportEquiv G.core.reading sigma W

/-- Canonical inverse context transport identifies the axis carrier. -/
noncomputable def canonicalSectionAxisEquiv {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : (geomTransportAlong G sigma).site.category) :
    (contextBackward (transportAlongHom G.core sigma) W).ctx.Axis ≃
      W.ctx.Axis := by
  simpa [contextBackward, contextInverse, transportAlongHom,
    transportAlongUpper] using
    transportCoreSectionAxisEquiv G.core.reading sigma W

/-- Canonical inverse context transport identifies the observable carrier. -/
noncomputable def canonicalSectionObservableEquiv {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : (geomTransportAlong G sigma).site.category) :
    (contextBackward (transportAlongHom G.core sigma) W).ctx.Observable ≃
      W.ctx.Observable := by
  simpa [contextBackward, contextInverse, transportAlongHom,
    transportAlongUpper] using
    transportCoreSectionObservableEquiv G.core.reading sigma W

/-- The support comparison and inverse section satisfy the source triangle. -/
theorem canonicalSectionSupportEquiv_triangle {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : G.site.category) (support : W.ctx.Support) :
    supportEquivOfContextEq (canonicalContextRetraction_eq G sigma W)
        ((canonicalSectionSupportEquiv G sigma
          (contextForward (transportAlongHom G.core sigma) W)).symm
          (geomTransportSupportComp G sigma W support)) = support := by
  simpa [supportEquivOfContextEq, canonicalSectionSupportEquiv,
    geomTransportSupportComp, contextForward, contextBackward, contextFunctor,
    contextInverse, transportAlongHom, transportAlongUpper] using
    transportCoreSectionSupportEquiv_triangle G.core.reading sigma W support

/-- The axis comparison and inverse section satisfy the source triangle. -/
theorem canonicalSectionAxisEquiv_triangle {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : G.site.category) (axis : W.ctx.Axis) :
    axisEquivOfContextEq (canonicalContextRetraction_eq G sigma W)
        ((canonicalSectionAxisEquiv G sigma
          (contextForward (transportAlongHom G.core sigma) W)).symm
          (geomTransportAxisComp G sigma W axis)) = axis := by
  simpa [axisEquivOfContextEq, canonicalSectionAxisEquiv,
    geomTransportAxisComp, contextForward, contextBackward, contextFunctor,
    contextInverse, transportAlongHom, transportAlongUpper] using
    transportCoreSectionAxisEquiv_triangle G.core.reading sigma W axis

/-- The observable comparison and inverse section satisfy the source triangle. -/
theorem canonicalSectionObservableEquiv_triangle {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : G.site.category) (observable : W.ctx.Observable) :
    observableEquivOfContextEq (canonicalContextRetraction_eq G sigma W)
        ((canonicalSectionObservableEquiv G sigma
          (contextForward (transportAlongHom G.core sigma) W)).symm
          (geomTransportObservableComp G sigma W observable)) = observable := by
  simpa [observableEquivOfContextEq, canonicalSectionObservableEquiv,
    geomTransportObservableComp, contextForward, contextBackward, contextFunctor,
    contextInverse, transportAlongHom, transportAlongUpper] using
    transportCoreSectionObservableEquiv_triangle G.core.reading sigma W observable

/-- The canonical section support equivalence preserves and reflects reads. -/
theorem canonicalSectionSupportEquiv_reads_iff {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : (geomTransportAlong G sigma).site.category)
    (support : (contextBackward (transportAlongHom G.core sigma) W).ctx.Support)
    (atom : U.Atom) :
    W.ctx.minimal.supportReads
        (canonicalSectionSupportEquiv G sigma W support)
        (sigma.atomEquiv atom) ↔
      (contextBackward (transportAlongHom G.core sigma) W).ctx.minimal.supportReads
        support atom := by
  simpa [canonicalSectionSupportEquiv, contextBackward, contextInverse,
    transportAlongHom, transportAlongUpper] using
    transportCoreSectionSupportEquiv_reads_iff
      G.core.reading sigma W support atom

/-- The canonical section axis equivalence preserves and reflects reads. -/
theorem canonicalSectionAxisEquiv_reads_iff {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : (geomTransportAlong G sigma).site.category)
    (axis : (contextBackward (transportAlongHom G.core sigma) W).ctx.Axis) :
    W.ctx.minimal.axisReads
        (canonicalSectionAxisEquiv G sigma W axis) ↔
      (contextBackward (transportAlongHom G.core sigma) W).ctx.minimal.axisReads
        axis := by
  simpa [canonicalSectionAxisEquiv, contextBackward, contextInverse,
    transportAlongHom, transportAlongUpper] using
    transportCoreSectionAxisEquiv_reads_iff G.core.reading sigma W axis

/-- The canonical section observable equivalence preserves and reflects reads. -/
theorem canonicalSectionObservableEquiv_reads_iff {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : (geomTransportAlong G sigma).site.category)
    (observable :
      (contextBackward (transportAlongHom G.core sigma) W).ctx.Observable) :
    W.ctx.minimal.observableReads
        (canonicalSectionObservableEquiv G sigma W observable) ↔
      (contextBackward (transportAlongHom G.core sigma) W).ctx.minimal.observableReads
        observable := by
  simpa [canonicalSectionObservableEquiv, contextBackward, contextInverse,
    transportAlongHom, transportAlongUpper] using
    transportCoreSectionObservableEquiv_reads_iff
      G.core.reading sigma W observable

/-- The canonical support section is natural on target contexts. -/
theorem canonicalSectionSupportEquiv_naturality {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {W V : (geomTransportAlong G sigma).site.category} (w : W ⟶ V)
    (support :
      (contextBackward (transportAlongHom G.core sigma) W).ctx.Support) :
    ((geomTransportAlong G sigma).core.contextPreorder.morphism
      (leOfHom w)).supportMap
        (canonicalSectionSupportEquiv G sigma W support) =
      canonicalSectionSupportEquiv G sigma V
        ((G.core.contextPreorder.morphism
          (leOfHom ((contextInverse
            (transportAlongHom G.core sigma)).map w))).supportMap support) := by
  simpa [canonicalSectionSupportEquiv, contextBackward, contextInverse,
    transportAlongHom, transportAlongUpper] using
    transportCoreSectionSupportEquiv_naturality
      G.core.reading sigma w support

/-- The canonical axis section is natural on target contexts. -/
theorem canonicalSectionAxisEquiv_naturality {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {W V : (geomTransportAlong G sigma).site.category} (w : W ⟶ V)
    (axis : (contextBackward (transportAlongHom G.core sigma) W).ctx.Axis) :
    ((geomTransportAlong G sigma).core.contextPreorder.morphism
      (leOfHom w)).axisMap
        (canonicalSectionAxisEquiv G sigma W axis) =
      canonicalSectionAxisEquiv G sigma V
        ((G.core.contextPreorder.morphism
          (leOfHom ((contextInverse
            (transportAlongHom G.core sigma)).map w))).axisMap axis) := by
  simpa [canonicalSectionAxisEquiv, contextBackward, contextInverse,
    transportAlongHom, transportAlongUpper] using
    transportCoreSectionAxisEquiv_naturality G.core.reading sigma w axis

/-- The canonical observable section is natural on target contexts. -/
theorem canonicalSectionObservableEquiv_naturality {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {W V : (geomTransportAlong G sigma).site.category} (w : W ⟶ V)
    (observable :
      (contextBackward (transportAlongHom G.core sigma) V).ctx.Observable) :
    ((geomTransportAlong G sigma).core.contextPreorder.morphism
      (leOfHom w)).observableRestrict
        (canonicalSectionObservableEquiv G sigma V observable) =
      canonicalSectionObservableEquiv G sigma W
        ((G.core.contextPreorder.morphism
          (leOfHom ((contextInverse
            (transportAlongHom G.core sigma)).map w))).observableRestrict
          observable) := by
  simpa [canonicalSectionObservableEquiv, contextBackward, contextInverse,
    transportAlongHom, transportAlongUpper] using
    transportCoreSectionObservableEquiv_naturality
      G.core.reading sigma w observable

/-- Inverse support sections commute with selected readable maps. -/
theorem canonicalSectionSupportEquiv_symm_naturality {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {W V : (geomTransportAlong G sigma).site.category} (w : W ⟶ V)
    (support : W.ctx.Support) :
    (G.core.contextPreorder.morphism
      (leOfHom ((contextInverse
        (transportAlongHom G.core sigma)).map w))).supportMap
        ((canonicalSectionSupportEquiv G sigma W).symm support) =
      (canonicalSectionSupportEquiv G sigma V).symm
        (((geomTransportAlong G sigma).core.contextPreorder.morphism
          (leOfHom w)).supportMap support) := by
  apply (canonicalSectionSupportEquiv G sigma V).injective
  simpa using (canonicalSectionSupportEquiv_naturality G sigma w
    ((canonicalSectionSupportEquiv G sigma W).symm support)).symm

/-- Inverse axis sections commute with selected readable maps. -/
theorem canonicalSectionAxisEquiv_symm_naturality {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {W V : (geomTransportAlong G sigma).site.category} (w : W ⟶ V)
    (axis : W.ctx.Axis) :
    (G.core.contextPreorder.morphism
      (leOfHom ((contextInverse
        (transportAlongHom G.core sigma)).map w))).axisMap
        ((canonicalSectionAxisEquiv G sigma W).symm axis) =
      (canonicalSectionAxisEquiv G sigma V).symm
        (((geomTransportAlong G sigma).core.contextPreorder.morphism
          (leOfHom w)).axisMap axis) := by
  apply (canonicalSectionAxisEquiv G sigma V).injective
  simpa using (canonicalSectionAxisEquiv_naturality G sigma w
    ((canonicalSectionAxisEquiv G sigma W).symm axis)).symm

/-- Inverse observable sections commute with selected restrictions. -/
theorem canonicalSectionObservableEquiv_symm_naturality {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {W V : (geomTransportAlong G sigma).site.category} (w : W ⟶ V)
    (observable : V.ctx.Observable) :
    (G.core.contextPreorder.morphism
      (leOfHom ((contextInverse
        (transportAlongHom G.core sigma)).map w))).observableRestrict
        ((canonicalSectionObservableEquiv G sigma V).symm observable) =
      (canonicalSectionObservableEquiv G sigma W).symm
        (((geomTransportAlong G sigma).core.contextPreorder.morphism
          (leOfHom w)).observableRestrict observable) := by
  apply (canonicalSectionObservableEquiv G sigma W).injective
  simpa using (canonicalSectionObservableEquiv_naturality G sigma w
    ((canonicalSectionObservableEquiv G sigma V).symm observable)).symm

/-- The support comparison of the deconjugated geometry factor. -/
noncomputable def geometryFactorSupportComp {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail))
    (W : (geomTransportAlong G sigma).site.category) :
    W.ctx.Support → (contextForward tail W).ctx.Support := fun support =>
  supportEquivOfContextEq (compositeTailContextSection_eq G sigma tail W)
    (H.supportComp
      (contextBackward (transportAlongHom G.core sigma) W)
      ((canonicalSectionSupportEquiv G sigma W).symm support))

/-- The axis comparison of the deconjugated geometry factor. -/
noncomputable def geometryFactorAxisComp {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail))
    (W : (geomTransportAlong G sigma).site.category) :
    W.ctx.Axis → (contextForward tail W).ctx.Axis := fun axis =>
  axisEquivOfContextEq (compositeTailContextSection_eq G sigma tail W)
    (H.axisComp
      (contextBackward (transportAlongHom G.core sigma) W)
      ((canonicalSectionAxisEquiv G sigma W).symm axis))

/-- The observable comparison of the deconjugated geometry factor. -/
noncomputable def geometryFactorObservableComp {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail))
    (W : (geomTransportAlong G sigma).site.category) :
    W.ctx.Observable → (contextForward tail W).ctx.Observable := fun observable =>
  observableEquivOfContextEq (compositeTailContextSection_eq G sigma tail W)
    (H.observableComp
      (contextBackward (transportAlongHom G.core sigma) W)
      ((canonicalSectionObservableEquiv G sigma W).symm observable))

/-- Free direct-image coverage makes every composite coverage hom factor. -/
def geometryFactorCoverage {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail)) :
    CoverageTransport (geomTransportAlong G sigma) K tail where
  requiredSupport atom := by
    rintro ⟨source, hsource, rfl⟩
    exact H.coverage.requiredSupport source hsource
  requiredEquationCoordinate coordinate := by
    rintro ⟨source, hsource, rfl⟩
    simpa [requiredCoordinateMap] using
      H.coverage.requiredEquationCoordinate source hsource
  selectedViolationWitness coordinate := by
    rintro ⟨source, hsource, rfl⟩
    simpa [equationCoordinateMap] using
      H.coverage.selectedViolationWitness source hsource
  requiredAxis axis := by
    rintro ⟨source, hsource, rfl⟩
    exact H.coverage.requiredAxis source hsource
  supportVisibleOn W atom := by
    rintro ⟨sourceW, source, hsource, rfl, rfl⟩
    simpa [contextMap] using
      H.coverage.supportVisibleOn sourceW source hsource
  equationCoordinateVisibleOn W coordinate := by
    rintro ⟨sourceW, source, hsource, rfl, rfl⟩
    simpa [contextMap, requiredCoordinateMap] using
      H.coverage.equationCoordinateVisibleOn sourceW source hsource
  violationWitnessVisibleOn W coordinate := by
    rintro ⟨sourceW, source, hsource, rfl, rfl⟩
    simpa [contextMap, equationCoordinateMap] using
      H.coverage.violationWitnessVisibleOn sourceW source hsource
  axisReadableOn W axis := by
    rintro ⟨sourceW, source, hsource, rfl, rfl⟩
    simpa [contextMap] using
      H.coverage.axisReadableOn sourceW source hsource
  boundaryVisibleOn W V := by
    rintro ⟨sourceW, sourceV, hsource, rfl, rfl⟩
    simpa [contextMap] using
      H.coverage.boundaryVisibleOn sourceW sourceV hsource

/-- Reindexed overlap objects make every composite overlap comparison factor. -/
noncomputable def geometryFactorOverlap {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail)) :
    OverlapTransport (geomTransportAlong G sigma) K tail where
  overlapIso base left right := by
    simpa [geomTransportAlong, pushGeometryPackage, pushSelectedGeometry,
      pushOverlap, contextForward, contextBackward, contextFunctor,
      contextInverse] using
      H.overlap.overlapIso base left right

/-- Raw base change and inverse-context reindexing give the factor raw equality. -/
theorem geometryFactor_raw_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail)) :
    K.raw = rawTransport tail H.coefficientHom := by
  calc
    K.raw = rawTransport
        (PackageTotalHom.comp (transportAlongHom G.core sigma) tail)
        H.coefficientHom := H.raw_eq
    _ = rawTransport tail H.coefficientHom := by
      simpa [geomTransportAlong, pushGeometryPackage, rawTransport] using
        rawTransport_comp (transportAlongHom G.core sigma) tail
          (RingHom.id G.Coefficient) H.coefficientHom

/-- The factor support comparison preserves cross-context readability. -/
theorem geometryFactor_supportReads {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail))
    (W : (geomTransportAlong G sigma).site.category)
    (support : W.ctx.Support) (atom : U.Atom)
    (hread : W.ctx.minimal.supportReads support atom) :
    (contextForward tail W).ctx.minimal.supportReads
      (geometryFactorSupportComp G sigma tail H W support)
      (tail.upper.atomEquiv atom) := by
  let sourceSupport := (canonicalSectionSupportEquiv G sigma W).symm support
  let sourceAtom := sigma.atomEquiv.symm atom
  have hsource :
      (contextBackward (transportAlongHom G.core sigma) W).ctx.minimal.supportReads
        sourceSupport sourceAtom := by
    apply (canonicalSectionSupportEquiv_reads_iff
      G sigma W sourceSupport sourceAtom).mp
    simpa [sourceSupport, sourceAtom] using hread
  have hmapped := H.supportReads
    (contextBackward (transportAlongHom G.core sigma) W)
    sourceSupport sourceAtom hsource
  apply (supportEquivOfContextEq_reads_iff
    (compositeTailContextSection_eq G sigma tail W)
    (H.supportComp (contextBackward (transportAlongHom G.core sigma) W)
      sourceSupport)
    (tail.upper.atomEquiv atom)).2
  simpa [sourceAtom, PackageTotalHom.comp,
    SignedExactCoreReadingHom.comp, transportAlongHom,
    transportAlongUpper] using hmapped

/-- The factor axis comparison preserves readability. -/
theorem geometryFactor_axisReads {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail))
    (W : (geomTransportAlong G sigma).site.category)
    (axis : W.ctx.Axis) (hread : W.ctx.minimal.axisReads axis) :
    (contextForward tail W).ctx.minimal.axisReads
      (geometryFactorAxisComp G sigma tail H W axis) := by
  let sourceAxis := (canonicalSectionAxisEquiv G sigma W).symm axis
  have hsource :
      (contextBackward (transportAlongHom G.core sigma) W).ctx.minimal.axisReads
        sourceAxis := by
    apply (canonicalSectionAxisEquiv_reads_iff G sigma W sourceAxis).mp
    simpa [sourceAxis] using hread
  have hmapped := H.axisReads
    (contextBackward (transportAlongHom G.core sigma) W) sourceAxis hsource
  apply (axisEquivOfContextEq_reads_iff
    (compositeTailContextSection_eq G sigma tail W)
    (H.axisComp (contextBackward (transportAlongHom G.core sigma) W)
      sourceAxis)).2
  exact hmapped

/-- The factor observable comparison preserves readability. -/
theorem geometryFactor_observableReads {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail))
    (W : (geomTransportAlong G sigma).site.category)
    (observable : W.ctx.Observable)
    (hread : W.ctx.minimal.observableReads observable) :
    (contextForward tail W).ctx.minimal.observableReads
      (geometryFactorObservableComp G sigma tail H W observable) := by
  let sourceObservable :=
    (canonicalSectionObservableEquiv G sigma W).symm observable
  have hsource :
      (contextBackward (transportAlongHom G.core sigma) W).ctx.minimal.observableReads
        sourceObservable := by
    apply (canonicalSectionObservableEquiv_reads_iff
      G sigma W sourceObservable).mp
    simpa [sourceObservable] using hread
  have hmapped := H.observableReads
    (contextBackward (transportAlongHom G.core sigma) W)
    sourceObservable hsource
  apply (observableEquivOfContextEq_reads_iff
    (compositeTailContextSection_eq G sigma tail W)
    (H.observableComp (contextBackward (transportAlongHom G.core sigma) W)
      sourceObservable)).2
  exact hmapped

/-- The factor support comparison is natural in the intermediate context. -/
theorem geometryFactor_support_naturality {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail))
    {W V : (geomTransportAlong G sigma).site.category} (w : W ⟶ V)
    (support : W.ctx.Support) :
    (targetContextMorphism (f := tail) w).supportMap
        (geometryFactorSupportComp G sigma tail H W support) =
      geometryFactorSupportComp G sigma tail H V
        ((sourceContextMorphism w).supportMap support) := by
  let canonical := transportAlongHom G.core sigma
  let inverseArrow := (contextInverse canonical).map w
  let sourceSupport := (canonicalSectionSupportEquiv G sigma W).symm support
  calc
    _ = supportEquivOfContextEq
        (compositeTailContextSection_eq G sigma tail V)
        ((K.core.contextPreorder.morphism
          (leOfHom ((contextFunctor (PackageTotalHom.comp canonical tail)).map
            inverseArrow))).supportMap
          (H.supportComp (contextBackward canonical W) sourceSupport)) :=
      supportEquivOfContextEq_naturality
        (compositeTailContextSection_eq G sigma tail W)
        (compositeTailContextSection_eq G sigma tail V)
        ((contextFunctor (PackageTotalHom.comp canonical tail)).map inverseArrow)
        ((contextFunctor tail).map w)
        (H.supportComp (contextBackward canonical W) sourceSupport)
    _ = supportEquivOfContextEq
        (compositeTailContextSection_eq G sigma tail V)
        (H.supportComp (contextBackward canonical V)
          ((G.core.contextPreorder.morphism
            (leOfHom inverseArrow)).supportMap sourceSupport)) := by
      exact congrArg
        (supportEquivOfContextEq
          (compositeTailContextSection_eq G sigma tail V))
        (H.support_naturality inverseArrow sourceSupport)
    _ = _ := by
      simp only [geometryFactorSupportComp, sourceSupport, canonical,
        sourceContextMorphism]
      rw [canonicalSectionSupportEquiv_symm_naturality G sigma w support]

end AAT.AG.GeometryTransport

#assert_standard_axioms_only AAT.AG.GeometryTransport
