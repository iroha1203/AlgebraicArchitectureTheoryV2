import ResearchLean.AG.FullGeometryNormalization.ExactNormalizationNaturality

/-!
# Canonical normalization along semantic exact geometry transport

The canonical complete-geometry transport along any exact pointed arrow
preserves normalization admissibility and maps canonical normalization to the
normalization generated at its target.  The lift equation is proved from the
actual transport morphism and is then used with its cocartesian universal
property to identify the transported vertical endomorphism.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- Semantic exact transport preserves canonical normalization admissibility.
The target proof is generated from the source through the transported core. -/
theorem canonicalGeometryNormalizationAdmissible_semanticExactTransport
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (source : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible source.1.core) :
    CanonicalObjectNormalizationAdmissible
      ((geomFiberTransportFunctor input).obj source).1.core := by
  change CanonicalObjectNormalizationAdmissible
    (transportAlong source.1.core
      (geomFiberBaseHom input source).doctrineHom)
  exact canonicalObjectNormalizationAdmissible_transportAlong
    source.1.core admissible
      (geomFiberBaseHom input source).doctrineHom

/-- The generated semantic exact transport lift commutes with canonical
complete-geometry normalization at its source and target. -/
theorem semanticGeomFiberLift_normalization_natural
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (source : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible source.1.core) :
    canonicalGeometryNormalization source.1 admissible ≫
        geomFiberLift input source =
      geomFiberLift input source ≫
        canonicalGeometryNormalization
          ((geomFiberTransportFunctor input).obj source).1
          (canonicalGeometryNormalizationAdmissible_semanticExactTransport
            input source admissible) := by
  simpa [geomFiberLift, geomFiberTransportFunctor, geomFiberTransportObj,
    geomFiberTransportObject] using
      geomTransportAlongHom_normalization_natural source.1 admissible
        (geomFiberBaseHom input source).doctrineHom

/-- Semantic exact geometry transport maps canonical normalization to the
normalization generated at its target. -/
theorem semanticGeomFiberTransportFunctor_map_normalization
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (source : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible source.1.core) :
    (geomFiberTransportFunctor input).map
        (canonicalGeometryFiberNormalization source admissible) =
      canonicalGeometryFiberNormalization
        ((geomFiberTransportFunctor input).obj source)
        (canonicalGeometryNormalizationAdmissible_semanticExactTransport
          input source admissible) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      input (geomFiberLift input source) :=
    geomFiberLift_isStronglyCocartesian input source
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (crossStageProjection.{u, v} U) input
    (geomFiberLift input source) (𝟙 Y)
  calc
    geomFiberLift input source ≫
          ((geomFiberTransportFunctor input).map
            (canonicalGeometryFiberNormalization source admissible)).1 =
        (canonicalGeometryFiberNormalization source admissible).1 ≫
          geomFiberLift input source := by
      simpa only [geomFiberTransportFunctor] using
        geomFiberTransportMap_fac input
          (canonicalGeometryFiberNormalization source admissible)
    _ = geomFiberLift input source ≫
        (canonicalGeometryFiberNormalization
          ((geomFiberTransportFunctor input).obj source)
          (canonicalGeometryNormalizationAdmissible_semanticExactTransport
            input source admissible)).1 := by
      simpa [canonicalGeometryFiberNormalization] using
        semanticGeomFiberLift_normalization_natural input source admissible

/-- On a realized arrow, semantic admissibility is the same proposition and
proof as the existing exact-transport API. -/
theorem canonicalGeometryNormalizationAdmissible_semanticExactTransport_realizable
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (source : GeomFiber.{u, v} input.semantic.source)
    (admissible : CanonicalObjectNormalizationAdmissible source.1.core) :
    canonicalGeometryNormalizationAdmissible_semanticExactTransport
        input.semantic.hom source admissible =
      canonicalGeometryNormalizationAdmissible_exactTransport
        input source admissible := by
  rfl

/-- The previous realized-arrow normalization law is the restriction of the
semantic exact-transport law to the arrow represented by the presentation. -/
theorem geomFiberTransportFunctor_map_normalization_of_semantic
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (source : GeomFiber.{u, v} input.semantic.source)
    (admissible : CanonicalObjectNormalizationAdmissible source.1.core) :
    (geomFiberTransportFunctor input.semantic.hom).map
        (canonicalGeometryFiberNormalization source admissible) =
      canonicalGeometryFiberNormalization
        ((geomFiberTransportFunctor input.semantic.hom).obj source)
        (canonicalGeometryNormalizationAdmissible_exactTransport
          input source admissible) := by
  simpa only [canonicalGeometryNormalizationAdmissible_semanticExactTransport_realizable]
    using semanticGeomFiberTransportFunctor_map_normalization
      input.semantic.hom source admissible

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
